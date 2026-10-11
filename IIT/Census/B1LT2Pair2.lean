/-
Census, B1 lemma LT2, module M6b-4: the success events of a pair and their product lower bound.

Index `κ = (eff, c, u, v) : Bool⁴`: `c` picks the column (`a` or `b`), `(u,v)` the pattern on `{a,b}`.
* `eff = false`: the private-sum small ball (`≥ x sd` for the target pattern `(false,false)`, `≤ -x sd` otherwise);
  entries `{(merge {a,b} (u,v) r, col) : r ∈ H, r_oth ≠ pattern_oth}`.
* `eff = true`: the effect entry `(merge {a,b} (u,v) s, col)` in its oriented box (when it is one of M1's four
  private effect positions), else `univ`.
Disjointness: every entry of block `κ` decodes to `κ` (`lt2code`).
-/
import IIT.Census.B1LT2Pair

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

section PairEvents

variable (s : State N) (w : Param N) (a b : Fin N) (x ρ : ℝ)

/-- Column and other column. -/
def lt2col (c : Bool) : Fin N := if c then b else a
def lt2oth (c : Bool) : Fin N := if c then a else b

open Classical in
/-- The rows of the private sum for `(c, u, v)`. -/
noncomputable def lt2Hf (c u v : Bool) : Finset (State N) :=
  (lt2H s w).filter fun r => r (lt2oth a b c) ≠ lt2pat a b u v (lt2oth a b c)

/-- The private sum with resampled entries `η`. -/
noncomputable def lt2Sres (c u v : Bool) (η : Param N) : ℝ :=
  ∑ r ∈ lt2Hf s w a b c u v, lt2gNs (w r) *
    (clamp01 (η (merge {a, b} (lt2pat a b u v) r) (lt2col a b c)) - 1 / 2)

/-- Its standard deviation. -/
noncomputable def lt2sd (c u v : Bool) : ℝ :=
  Real.sqrt (∑ r ∈ lt2Hf s w a b c u v, lt2gNs (w r) ^ 2 / 12)

/-- The effect row of a pattern. -/
def lt2rowE (u v : Bool) : State N := merge {a, b} (lt2pat a b u v) s

/-- Whether `(c, u, v)` is one of M1's four private effect positions. -/
def lt2isEff (c u v : Bool) : Prop := if c then u ≠ s a else v ≠ s b

open Classical in
/-- The events. -/
noncomputable def lt2X (κ : Bool × Bool × Bool × Bool) : Set (Param N) :=
  if κ.1 then
    (if lt2isEff s a b κ.2.1 κ.2.2.1 κ.2.2.2 then
      (if 1 / 2 ≤ clamp01 (w s (lt2col a b κ.2.1)) then
        {η | clamp01 (η (lt2rowE s a b κ.2.2.1 κ.2.2.2) (lt2col a b κ.2.1)) ≤ ρ}
      else {η | 1 - ρ ≤ clamp01 (η (lt2rowE s a b κ.2.2.1 κ.2.2.2) (lt2col a b κ.2.1))})
    else Set.univ)
  else
    (if κ.2.2.1 = false ∧ κ.2.2.2 = false then
      {η | x * lt2sd s w a b κ.2.1 κ.2.2.1 κ.2.2.2 ≤ lt2Sres s w a b κ.2.1 κ.2.2.1 κ.2.2.2 η}
    else {η | lt2Sres s w a b κ.2.1 κ.2.2.1 κ.2.2.2 η ≤ -(x * lt2sd s w a b κ.2.1 κ.2.2.1 κ.2.2.2)})

open Classical in
/-- The entry blocks. -/
noncomputable def lt2C (κ : Bool × Bool × Bool × Bool) : Finset (State N × Fin N) :=
  if κ.1 then
    (if lt2isEff s a b κ.2.1 κ.2.2.1 κ.2.2.2 then {(lt2rowE s a b κ.2.2.1 κ.2.2.2, lt2col a b κ.2.1)} else ∅)
  else (lt2Hf s w a b κ.2.1 κ.2.2.1 κ.2.2.2).image
    fun r => (merge {a, b} (lt2pat a b κ.2.2.1 κ.2.2.2) r, lt2col a b κ.2.1)

end PairEvents

open Classical in
/-- The decoding of an entry. -/
noncomputable def lt2code (s : State N) (a b : Fin N) (q : State N × Fin N) : Bool × Bool × Bool × Bool :=
  (decide (ham q.1 s ≤ 2), decide (q.2 = b), q.1 a, q.1 b)

lemma lt2_merge_pat_a {a b : Fin N} (u v : Bool) (r : State N) : merge {a, b} (lt2pat a b u v) r a = u := by
  rw [merge_mem (by simp)]; simp [lt2pat]

lemma lt2_merge_pat_b {a b : Fin N} (hab : a ≠ b) (u v : Bool) (r : State N) :
    merge {a, b} (lt2pat a b u v) r b = v := by
  rw [merge_mem (by simp)]; simp [lt2pat, Ne.symm hab]

lemma lt2_ham_merge_self (S : Finset (Fin N)) (t r : State N) : ham (merge S t r) r ≤ S.card := by
  rw [b1_ham_comm]; exact lt2_ham_merge_le S t r

/-- **Every entry of a block decodes to its index.** -/
lemma lt2_code_C {s : State N} {w : Param N} {a b : Fin N} (hab : a ≠ b) (κ : Bool × Bool × Bool × Bool)
    {q : State N × Fin N} (hq : q ∈ lt2C s w a b κ) : lt2code s a b q = κ := by
  classical
  obtain ⟨e, c, u, v⟩ := κ
  have hcol : ∀ c' : Bool, decide (lt2col a b c' = b) = c' := fun c' => by
    cases c' <;> simp [lt2col, hab]
  have hcard : ({a, b} : Finset (Fin N)).card ≤ 2 := Finset.card_insert_le _ _
  cases e
  · simp only [lt2C, Bool.false_eq_true, ↓reduceIte, mem_image] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    have hrH := (mem_filter.1 hr).1
    have hfar := ((mem_filter.1 hrH).2).2.2
    have h1 : ham r (merge {a, b} (lt2pat a b u v) r) ≤ 2 := by
      rw [b1_ham_comm]; exact (lt2_ham_merge_self {a, b} (lt2pat a b u v) r).trans hcard
    have h2 := ham_triangle r (merge {a, b} (lt2pat a b u v) r) s
    have h3 : ¬ ham (merge {a, b} (lt2pat a b u v) r) s ≤ 2 := by omega
    unfold lt2code
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · exact decide_eq_false h3
    · exact hcol c
    · exact lt2_merge_pat_a u v r
    · exact lt2_merge_pat_b hab u v r
  · simp only [lt2C, ↓reduceIte] at hq
    split_ifs at hq with hE
    · rw [mem_singleton] at hq; subst hq
      have h1 : ham (lt2rowE s a b u v) s ≤ 2 := (lt2_ham_merge_self _ _ s).trans hcard
      unfold lt2code
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · exact decide_eq_true h1
      · exact hcol c
      · exact lt2_merge_pat_a u v s
      · exact lt2_merge_pat_b hab u v s
    · simp at hq

lemma lt2_C_disj {s : State N} {w : Param N} {a b : Fin N} (hab : a ≠ b) (j k : Bool × Bool × Bool × Bool)
    (hjk : j ≠ k) : Disjoint (lt2C s w a b j) (lt2C s w a b k) := by
  rw [Finset.disjoint_left]
  intro q hj hk
  exact hjk ((lt2_code_C hab j hj).symm.trans (lt2_code_C hab k hk))

end Census
end IIT
