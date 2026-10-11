/-
Census: the finite enumeration of admissible pairs `(g, δ)` (set partitions of `{0, …, k-1}` given
by their minimal-representative maps, with a direction per block).

`cd_gen k` lists every pair with `cd_valid k g δ` (`cd_mem_gen`), so a statement about all admissible
pairs follows from a kernel evaluation over the list (`cd_forall_valid`).  For `k = 2, 3, 4, 5` the
list has `9, 54, 306, 1863` entries.
-/
import IIT.Census.CertDataBase

namespace IIT
namespace Census

/-- All lists `l` of length `n` with `l[i] ∈ ch i`, the last entry varying fastest. -/
def cd_enum (ch : ℕ → List ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (cd_enum ch n).flatMap fun l => (ch n).map fun a => l ++ [a]

lemma cd_getD_append_lt (l : List ℕ) (a : ℕ) {i : ℕ} (hi : i < l.length) :
    (l ++ [a]).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma cd_getD_append_eq (l : List ℕ) (a : ℕ) : (l ++ [a]).getD l.length 0 = a := by
  simp [List.getD_eq_getElem?_getD]

lemma cd_mem_enum (ch : ℕ → List ℕ) (n : ℕ) (l : List ℕ) :
    l ∈ cd_enum ch n ↔ l.length = n ∧ ∀ i < n, l.getD i 0 ∈ ch i := by
  induction n generalizing l with
  | zero =>
    simp only [cd_enum, List.mem_singleton, Nat.not_lt_zero, false_imp_iff, imp_true_iff,
      and_true]
    exact ⟨fun h => h ▸ rfl, fun h => List.eq_nil_of_length_eq_zero h⟩
  | succ n ih =>
    simp only [cd_enum, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨l', hl', a, ha, rfl⟩
      rw [ih] at hl'
      refine ⟨by simp [hl'.1], fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · rw [cd_getD_append_lt _ _ (by omega)]; exact hl'.2 i h
      · subst h; rw [← hl'.1, cd_getD_append_eq, hl'.1]; exact ha
    · rintro ⟨hlen, hch⟩
      have hl : l = l.take n ++ [l.getD n 0] := by
        apply List.ext_getElem
        · simp [hlen]
        · intro i h1 h2
          by_cases hi : i < n
          · rw [List.getElem_append_left (by simp [hlen]; omega)]
            simp
          · have : i = n := by omega
            subst this
            rw [List.getElem_append_right (by simp [hlen])]
            simp [List.getD_eq_getElem?_getD, hlen]
      refine ⟨l.take n, (ih _).2 ⟨by simp [hlen], fun i hi => ?_⟩, l.getD n 0, hch n (by omega), hl.symm⟩
      have := hch i (by omega)
      simpa [List.getD_eq_getElem?_getD, List.getElem?_take, hi] using this

/-- Choices for the representative of unit `i`. -/
def cd_chG (i : ℕ) : List ℕ := List.range (i + 1)

/-- Choices for the direction code at position `i`. -/
def cd_chD (g : List ℕ) (i : ℕ) : List ℕ := if g.getD i 0 = i then [0, 1, 2] else [0]

/-- The admissible pairs of a `k`-set. -/
def cd_gen (k : ℕ) : List (List ℕ × List ℕ) :=
  ((cd_enum cd_chG k).flatMap fun g => (cd_enum (cd_chD g) k).map fun δ => (g, δ)).filter
    fun x => cd_valid k x.1 x.2

lemma cd_valid_iff (k : ℕ) (g δ : List ℕ) :
    cd_valid k g δ = true ↔ g.length = k ∧ δ.length = k ∧
      (∀ i < k, g.getD i 0 ≤ i ∧ g.getD (g.getD i 0) 0 = g.getD i 0 ∧
        (if g.getD i 0 = i then δ.getD i 0 ≤ 2 else δ.getD i 0 = 0)) ∧
      (∃ i < k, g.getD i 0 ≠ 0) := by
  unfold cd_valid
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    List.any_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, h2, fun i hi => ?_, h4⟩
    obtain ⟨⟨a, b⟩, c⟩ := h3 i hi
    refine ⟨a, b, ?_⟩
    split_ifs at c ⊢ with h
    · simpa using c
    · simpa using c
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨⟨h1, h2⟩, fun i hi => ?_⟩, h4⟩
    obtain ⟨a, b, c⟩ := h3 i hi
    refine ⟨⟨a, b⟩, ?_⟩
    split_ifs at c ⊢ with h
    · simpa using c
    · simpa using c

/-- Every admissible pair is listed. -/
theorem cd_mem_gen {k : ℕ} {g δ : List ℕ} (h : cd_valid k g δ = true) : (g, δ) ∈ cd_gen k := by
  unfold cd_gen
  rw [List.mem_filter]
  refine ⟨?_, h⟩
  obtain ⟨hg, hd, hi, _⟩ := (cd_valid_iff k g δ).1 h
  simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  refine ⟨g, (cd_mem_enum _ _ _).2 ⟨hg, fun i hi' => ?_⟩, δ, (cd_mem_enum _ _ _).2 ⟨hd, fun i hi' => ?_⟩,
    rfl, rfl⟩
  · simp only [cd_chG, List.mem_range]
    have := (hi i hi').1
    omega
  · have := (hi i hi').2.2
    simp only [cd_chD]
    split_ifs at this ⊢ with hh
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    · exact List.mem_singleton.2 this

/-- A statement about all admissible pairs follows from its evaluation on `cd_gen k`. -/
theorem cd_forall_valid (k : ℕ) (P : List ℕ → List ℕ → Bool)
    (h : (cd_gen k).all (fun x => P x.1 x.2) = true) :
    ∀ g δ, cd_valid k g δ = true → P g δ = true := by
  intro g δ hv
  rw [List.all_eq_true] at h
  exact h _ (cd_mem_gen hv)

end Census
end IIT
