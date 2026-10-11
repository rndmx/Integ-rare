/-
Census, B1 LTBetaHi, module T2 tool: **the window** (W8 §3).

Values `v q ∈ [0,1]^d` on a class `Q`; cutting `[0,1]` into `n` bins gives a sub-class `Q' ⊆ Q` with
`|Q| ≤ n^d |Q'|` on which every coordinate varies by at most `1/n`.
-/
import Mathlib

namespace IIT
namespace Census

open Finset

/-- The bin of `x ∈ [0,1]` among `n` bins. -/
noncomputable def winBin (n : ℕ) (hn : 0 < n) (x : ℝ) : Fin n :=
  ⟨min (⌊x * n⌋₊) (n - 1), lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hn one_pos)⟩

lemma winBin_bounds (n : ℕ) (hn : 0 < n) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ((winBin n hn x : ℕ) : ℝ) / n ≤ x ∧ x ≤ (((winBin n hn x : ℕ) : ℝ) + 1) / n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [winBin]
  constructor
  · rw [div_le_iff₀ hnr]
    calc ((min ⌊x * n⌋₊ (n - 1) : ℕ) : ℝ) ≤ (⌊x * n⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
      _ ≤ x * n := Nat.floor_le (by positivity)
  · rw [le_div_iff₀ hnr]
    rcases le_total ⌊x * n⌋₊ (n - 1) with h | h
    · rw [min_eq_left h]; exact (Nat.lt_floor_add_one _).le
    · rw [min_eq_right h]
      have : ((n - 1 : ℕ) : ℝ) + 1 = n := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]; nlinarith

lemma winBin_close (n : ℕ) (hn : 0 < n) {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (h : winBin n hn x = winBin n hn y) : |x - y| ≤ 1 / n := by
  have a := winBin_bounds n hn hx0 hx1
  have b := winBin_bounds n hn hy0 hy1
  rw [h] at a
  rw [abs_le]
  have e : (((winBin n hn y : ℕ) : ℝ) + 1) / n = ((winBin n hn y : ℕ) : ℝ) / n + 1 / n := by ring
  constructor <;> linarith [a.1, a.2, b.1, b.2]

/-- **Window lemma.** -/
theorem window_pigeon {ι : Type*} [DecidableEq ι] (Q : Finset ι) (d n : ℕ) (hn : 0 < n) (v : ι → Fin d → ℝ)
    (hv : ∀ q ∈ Q, ∀ k, 0 ≤ v q k ∧ v q k ≤ 1) :
    ∃ Q' ⊆ Q, Q.card ≤ n ^ d * Q'.card ∧ ∀ q ∈ Q', ∀ q' ∈ Q', ∀ k, |v q k - v q' k| ≤ 1 / n := by
  classical
  let f : ι → (Fin d → Fin n) := fun q k => winBin n hn (v q k)
  -- some fibre is large
  have hbig : ∃ y : Fin d → Fin n, Q.card ≤ n ^ d * (Q.filter fun q => f q = y).card := by
    by_contra hno
    push Not at hno
    have : Nonempty (Fin d → Fin n) := ⟨fun _ => ⟨0, hn⟩⟩
    rcases Q.eq_empty_or_nonempty with he | hne
    · have := hno (fun _ => ⟨0, hn⟩); rw [he] at this; simp at this
    · have hsum : Q.card = ∑ y : Fin d → Fin n, (Q.filter fun q => f q = y).card :=
        card_eq_sum_card_fiberwise (fun q _ => mem_univ (f q))
      have hlt : ∑ y : Fin d → Fin n, n ^ d * (Q.filter fun q => f q = y).card <
          ∑ _y : Fin d → Fin n, Q.card :=
        Finset.sum_lt_sum_of_nonempty univ_nonempty fun y _ => hno y
      rw [← Finset.mul_sum, ← hsum, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin, smul_eq_mul] at hlt
      exact lt_irrefl _ hlt
  obtain ⟨y, hy⟩ := hbig
  refine ⟨Q.filter fun q => f q = y, filter_subset _ _, hy, fun q hq q' hq' k => ?_⟩
  obtain ⟨hqQ, hfq⟩ := mem_filter.1 hq
  obtain ⟨hqQ', hfq'⟩ := mem_filter.1 hq'
  have hk : winBin n hn (v q k) = winBin n hn (v q' k) := by
    have := congrFun (hfq.trans hfq'.symm) k; exact this
  exact winBin_close n hn (hv q hqQ k).1 (hv q hqQ k).2 (hv q' hqQ' k).1 (hv q' hqQ' k).2 hk

/-- Pigeonhole: some fibre of `f : ι → β` over `Q` has at least `|Q|/|β|` elements. -/
lemma exists_big_fiber {ι β : Type*} [Fintype β] [Nonempty β] [DecidableEq β] (Q : Finset ι) (f : ι → β) :
    ∃ y, Q.card ≤ Fintype.card β * (Q.filter fun q => f q = y).card := by
  classical
  by_contra hno
  push Not at hno
  rcases Q.eq_empty_or_nonempty with he | hne
  · obtain ⟨y⟩ := ‹Nonempty β›
    have := hno y; rw [he] at this; simp at this
  · have hsum : Q.card = ∑ y : β, (Q.filter fun q => f q = y).card :=
      card_eq_sum_card_fiberwise (fun q _ => mem_univ (f q))
    have hlt : ∑ y : β, Fintype.card β * (Q.filter fun q => f q = y).card < ∑ _y : β, Q.card :=
      Finset.sum_lt_sum_of_nonempty univ_nonempty fun y _ => hno y
    rw [← Finset.mul_sum, ← hsum, sum_const, card_univ, smul_eq_mul] at hlt
    exact lt_irrefl _ hlt

/-- **Agreement class** (W2 6.1(d)): a sub-class `Q ⊆ U` with `|U| ≤ 2^{|𝒮|} |Q|` on which every row of `𝒮`
agrees with `tc` everywhere or nowhere. -/
theorem agree_class {N : ℕ} (𝒮 : Finset (Fin N → Bool)) (U : Finset (Fin N)) (tc : Fin N → Bool) :
    ∃ Q ⊆ U, U.card ≤ 2 ^ 𝒮.card * Q.card ∧
      ∀ r ∈ 𝒮, (∀ j ∈ Q, r j = tc j) ∨ (∀ j ∈ Q, r j ≠ tc j) := by
  classical
  let f : Fin N → (𝒮 → Bool) := fun j r => decide (r.1 j = tc j)
  obtain ⟨y, hy⟩ := exists_big_fiber U f
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at hy
  refine ⟨U.filter fun j => f j = y, filter_subset _ _, hy, fun r hr => ?_⟩
  have hfib : ∀ j ∈ U.filter (fun j => f j = y), decide (r j = tc j) = y ⟨r, hr⟩ := fun j hj =>
    congrFun (mem_filter.1 hj).2 ⟨r, hr⟩
  cases hyr : y ⟨r, hr⟩
  · exact Or.inr fun j hj => by have := hfib j hj; rw [hyr] at this; simpa using this
  · exact Or.inl fun j hj => by have := hfib j hj; rw [hyr] at this; simpa using this

/-- Two rows each agreeing-or-differing with `tc` on `Q` agree-or-differ with each other on `Q`. -/
lemma agree_pair_tc {N : ℕ} {Q : Finset (Fin N)} {r r' tc : Fin N → Bool}
    (h : (∀ j ∈ Q, r j = tc j) ∨ (∀ j ∈ Q, r j ≠ tc j)) (h' : (∀ j ∈ Q, r' j = tc j) ∨ (∀ j ∈ Q, r' j ≠ tc j)) :
    (∀ j ∈ Q, r j = r' j) ∨ (∀ j ∈ Q, r j ≠ r' j) := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact Or.inl fun j hj => by rw [h j hj, h' j hj]
  · exact Or.inr fun j hj => by rw [h j hj]; exact fun e => h' j hj e.symm
  · exact Or.inr fun j hj => by rw [h' j hj]; exact h j hj
  · exact Or.inl fun j hj => by
      have a := h j hj; have b := h' j hj
      cases hr : r j <;> cases hr' : r' j <;> cases ht : tc j <;> simp_all

end Census
end IIT
