/-
Census, B1 lemma LT2, module M6b: the private sums of a pair, explicitly.

For `{i, o}` with one of `i, o` in `D₁` and the other in `D₂`:
`(merge {i,o} t r, i) ∈ PB(r) ↔ r_o ≠ t_o` (`lt2_mem_PB_merge`), hence
`Π_i(t) = Σ_{r ∈ H, r_o ≠ t_o} P_ns(r) (y_{merge {i,o} t r, i} - 1/2)` (`lt2Pi_eq_PiE`).
-/
import IIT.Census.B1LT2Cond

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

open Classical in
/-- The explicit private sum. -/
noncomputable def lt2PiE (s : State N) (w : Param N) (i o : Fin N) (t : State N) : ℝ :=
  ∑ r ∈ (lt2H s w).filter (fun r => r o ≠ t o), lt2gNs (w r) * (clamp01 (w (merge {i, o} t r) i) - 1 / 2)

lemma lt2_flip_apply_ne {r : State N} {j k : Fin N} (h : k ≠ j) : flip r j k = r k := by
  unfold flip; rw [Function.update_of_ne h]

lemma lt2_flip_apply_self (r : State N) (j : Fin N) : flip r j j = !r j := by
  unfold flip; simp

/-- The four private positions of a block as a membership criterion. -/
lemma lt2_mem_PB_iff {r : State N} {q : State N × Fin N} :
    q ∈ lt2PB r ↔ ∃ a ∈ lt2D1 N, ∃ b ∈ lt2D2 N, q = (flip r b, a) ∨ q = (flip (flip r a) b, a) ∨
      q = (flip r a, b) ∨ q = (flip (flip r a) b, b) := by
  classical
  unfold lt2PB
  simp only [mem_biUnion, mem_product, mem_insert, mem_singleton, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, h⟩; exact ⟨a, ha, b, hb, h⟩
  · rintro ⟨a, ha, b, hb, h⟩; exact ⟨a, b, ⟨ha, hb⟩, h⟩

lemma lt2_D_disj {i : Fin N} (h1 : i ∈ lt2D1 N) (h2 : i ∈ lt2D2 N) : False := lt2_D1_ne_D2 h1 h2 rfl

/-- **The private-position criterion for a pair.** -/
theorem lt2_mem_PB_merge {r t : State N} {i o : Fin N}
    (hio : (i ∈ lt2D1 N ∧ o ∈ lt2D2 N) ∨ (i ∈ lt2D2 N ∧ o ∈ lt2D1 N)) :
    (merge {i, o} t r, i) ∈ lt2PB r ↔ r o ≠ t o := by
  have hne : i ≠ o := by
    rcases hio with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact lt2_D1_ne_D2 h1 h2
    · exact (lt2_D1_ne_D2 h2 h1).symm
  set m := merge {i, o} t r
  have hmi : m i = t i := merge_mem (by simp)
  have hmo : m o = t o := merge_mem (by simp)
  have hmj : ∀ j, j ≠ i → j ≠ o → m j = r j := fun j h1 h2 => merge_not_mem (by simp [h1, h2])
  constructor
  · intro hP hro
    -- `m` differs from `r` only at `i`
    have hmr : ∀ j, j ≠ i → m j = r j := fun j hj => by
      by_cases hjo : j = o
      · subst hjo; rw [hmo, hro]
      · exact hmj j hj hjo
    obtain ⟨a, ha, b, hb, hq⟩ := lt2_mem_PB_iff.1 hP
    have hab := lt2_D1_ne_D2 ha hb
    rcases hq with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨hm, hi⟩ := h
    · -- `m = r^b`, column `a = i`: then `b = i`
      have := hmr b (by rw [hi]; exact Ne.symm hab)
      rw [hm, lt2_flip_apply_self] at this; cases r b <;> simp at this
    · have := hmr b (by rw [hi]; exact Ne.symm hab)
      rw [hm, lt2_flip_apply_self, lt2_flip_apply_ne (Ne.symm hab)] at this; cases r b <;> simp at this
    · have := hmr a (by rw [hi]; exact hab)
      rw [hm, lt2_flip_apply_self] at this; cases r a <;> simp at this
    · have := hmr a (by rw [hi]; exact hab)
      rw [hm, lt2_flip_apply_ne hab, lt2_flip_apply_self] at this; cases r a <;> simp at this
  · intro hro
    have hto : t o = !r o := by cases h1 : t o <;> cases h2 : r o <;> simp_all
    rw [lt2_mem_PB_iff]
    by_cases hti : t i = r i
    · -- `m = r^o`
      have hm : m = flip r o := by
        funext j
        by_cases hji : j = i
        · subst hji; rw [hmi, lt2_flip_apply_ne hne, hti]
        · by_cases hjo : j = o
          · subst hjo; rw [hmo, lt2_flip_apply_self, hto]
          · rw [hmj j hji hjo, lt2_flip_apply_ne hjo]
      rcases hio with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨i, h1, o, h2, Or.inl (by rw [hm])⟩
      · exact ⟨o, h2, i, h1, Or.inr (Or.inr (Or.inl (by rw [hm])))⟩
    · have hti' : t i = !r i := by cases h1 : t i <;> cases h2 : r i <;> simp_all
      rcases hio with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hm : m = flip (flip r i) o := by
          funext j
          by_cases hji : j = i
          · subst hji; rw [hmi, lt2_flip_apply_ne hne, lt2_flip_apply_self, hti']
          · by_cases hjo : j = o
            · subst hjo; rw [hmo, lt2_flip_apply_self, lt2_flip_apply_ne (Ne.symm hne), hto]
            · rw [hmj j hji hjo, lt2_flip_apply_ne hjo, lt2_flip_apply_ne hji]
        exact ⟨i, h1, o, h2, Or.inr (Or.inl (by rw [hm]))⟩
      · have hm : m = flip (flip r o) i := by
          funext j
          by_cases hji : j = i
          · subst hji; rw [hmi, lt2_flip_apply_self, lt2_flip_apply_ne hne, hti']
          · by_cases hjo : j = o
            · subst hjo; rw [hmo, lt2_flip_apply_ne (Ne.symm hne), lt2_flip_apply_self, hto]
            · rw [hmj j hji hjo, lt2_flip_apply_ne hji, lt2_flip_apply_ne hjo]
        exact ⟨o, h2, i, h1, Or.inr (Or.inr (Or.inr (by rw [hm])))⟩

/-- **The private sum, explicitly.** -/
theorem lt2Pi_eq_PiE (s : State N) (w : Param N) {i o : Fin N} (t : State N)
    (hio : (i ∈ lt2D1 N ∧ o ∈ lt2D2 N) ∨ (i ∈ lt2D2 N ∧ o ∈ lt2D1 N)) :
    lt2Pi s w {i, o} t i = lt2PiE s w i o t := by
  classical
  unfold lt2Pi lt2PiE
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : r o ≠ t o
  · rw [if_pos ((lt2_mem_PB_merge hio).2 h), if_pos h]
  · rw [if_neg (fun hh => h ((lt2_mem_PB_merge hio).1 hh)), if_neg h]

end Census
end IIT
