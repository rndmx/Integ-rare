/-
Census, B1 lemma LT2, module M6c-2: reflection of the private entries.

`reflE A η` reflects the entries on `A` (`y ↦ 1 - y`); it preserves `cubeM`, and the private sums change sign.
`lt2_reflect_half`: if the shared part `F(t) = NumNs(w½)` of a pair-column difference is `≥ M` in absolute value,
then after resampling the private entries the true difference is `≥ M - 2ε` in absolute value with probability
`≥ 1/2`.
-/
import IIT.Census.B1LT2Count

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- Reflection of the entries on `A`. -/
noncomputable def reflE (A : Finset (State N × Fin N)) (η : Param N) : Param N := by
  classical exact fun r j => if (r, j) ∈ A then 1 - η r j else η r j

lemma lt2_mp_reflE (A : Finset (State N × Fin N)) : MeasurePreserving (reflE A) (cubeM N) (cubeM N) := by
  classical
  unfold cubeM
  have hrow : ∀ r : State N, MeasurePreserving (fun x : Fin N → ℝ => fun j => if (r, j) ∈ A then 1 - x j else x j)
      (rowM N) (rowM N) := fun r => by
    unfold rowM
    refine measurePreserving_pi (fun _ : Fin N => unif) (fun _ : Fin N => unif)
      (f := fun j u => if (r, j) ∈ A then 1 - u else u) fun j => ?_
    split_ifs
    · exact lt2_unif_reflect
    · exact MeasurePreserving.id unif
  have := measurePreserving_pi (fun _ : State N => rowM N) (fun _ : State N => rowM N) hrow
  convert this using 1
  funext η r j
  simp only [reflE]

lemma lt2_replE_reflE_mem {A : Finset (State N × Fin N)} {w η : Param N} {q : State N × Fin N} (hq : q ∈ A) :
    replE A w (reflE A η) q.1 q.2 = 1 - replE A w η q.1 q.2 := by
  classical
  simp only [replE, reflE, if_pos (show (q.1, q.2) ∈ A from hq)]

lemma lt2_replE_reflE_out (A : Finset (State N × Fin N)) (w η : Param N) :
    ∀ q ∉ A, replE A w (reflE A η) q.1 q.2 = replE A w η q.1 q.2 := by
  classical
  intro q hq; simp only [replE, if_neg (show (q.1, q.2) ∉ A from hq)]

/-- The private sum changes sign under reflection. -/
lemma lt2PiE_reflE (s : State N) (w η : Param N) {i o : Fin N} (t : State N)
    (hio : (i ∈ lt2D1 N ∧ o ∈ lt2D2 N) ∨ (i ∈ lt2D2 N ∧ o ∈ lt2D1 N)) :
    lt2PiE s (replE (lt2Priv s w) w (reflE (lt2Priv s w) η)) i o t =
      -lt2PiE s (replE (lt2Priv s w) w η) i o t := by
  classical
  rw [lt2PiE_replE s w _ t hio, lt2PiE_replE s w _ t hio, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨hrH, hro⟩ := mem_filter.1 hr
  have hpriv : (merge {i, o} t r, i) ∈ lt2Priv s w := by
    unfold lt2Priv; exact mem_union_left _ (mem_biUnion.2 ⟨r, hrH, (lt2_mem_PB_merge hio).2 hro⟩)
  have : reflE (lt2Priv s w) η (merge {i, o} t r) i = 1 - η (merge {i, o} t r) i := by
    simp only [reflE, if_pos hpriv]
  rw [this, clamp01_one_sub]; ring

/-- The shared data are unchanged by resampling the private entries. -/
lemma lt2_replE_agree (s : State N) (w η : Param N) :
    ∀ q ∉ lt2Priv s w, w q.1 q.2 = replE (lt2Priv s w) w η q.1 q.2 := by
  classical
  intro q hq; simp only [replE, if_neg (show (q.1, q.2) ∉ lt2Priv s w from hq)]

lemma lt2Half_replE (s : State N) (w η : Param N) :
    lt2Half s (replE (lt2Priv s w) w η) = lt2Half s w := by
  classical
  have hag := lt2_replE_agree s w η
  have hP : lt2Priv s (replE (lt2Priv s w) w η) = lt2Priv s w := lt2Priv_stop hag
  funext r j
  unfold lt2Half
  rw [hP]
  split_ifs with h
  · rfl
  · exact (hag (r, j) h).symm

lemma lt2Eps_replE (s : State N) (w η : Param N) : lt2Eps s (replE (lt2Priv s w) w η) = lt2Eps s w := by
  unfold lt2Eps; rw [lt2H_stop (lt2_replE_agree s w η)]

lemma lt2_meas_NumNs (S : Finset (Fin N)) (t : State N) (i : Fin N) :
    Measurable fun w : Param N => lt2NumNs w S t i := by
  unfold lt2NumNs
  exact Finset.measurable_sum _ fun v _ =>
    (measurable_clamp01.comp ((measurable_pi_apply i).comp (measurable_pi_apply _))).mul
      (lt2gNs_measurable.comp (measurable_pi_apply v))

/-- **Reflection: half of the resamplings keep a large shared difference visible.** -/
theorem lt2_reflect_half (s : State N) (w : Param N) {a b : Fin N} (ha : a ∈ lt2D1 N) (hb : b ∈ lt2D2 N)
    (c : Bool) (t0 t : State N) {M : ℝ}
    (hF : M ≤ |lt2NumNs (lt2Half s w) {a, b} t0 (lt2col a b c) - lt2NumNs (lt2Half s w) {a, b} t (lt2col a b c)|) :
    ENNReal.ofReal (1 / 2) ≤ cubeM N {η | M - 2 * lt2Eps s w ≤
      |lt2NumNs (replE (lt2Priv s w) w η) {a, b} t0 (lt2col a b c) -
        lt2NumNs (replE (lt2Priv s w) w η) {a, b} t (lt2col a b c)|} := by
  classical
  haveI : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  set A := lt2Priv s w
  set i := lt2col a b c
  set o := lt2oth a b c
  have hio := lt2_orient ha hb c
  have hS : ({a, b} : Finset (Fin N)) = {i, o} := (lt2_pair_set a b c).symm
  have hcard : ({a, b} : Finset (Fin N)).card ≤ 2 := Finset.card_insert_le _ _
  set ε := lt2Eps s w
  set F : State N → ℝ := fun t => lt2NumNs (lt2Half s w) {a, b} t i
  set D : Param N → ℝ := fun η => lt2NumNs (replE A w η) {a, b} t0 i - lt2NumNs (replE A w η) {a, b} t i
  set P : Param N → ℝ := fun η => lt2PiE s (replE A w η) i o t0 - lt2PiE s (replE A w η) i o t
  -- the decomposition
  have hdec : ∀ η, |D η - (F t0 - F t) - P η| ≤ 2 * ε := by
    intro η
    have h1 := lt2_pert s (replE A w η) hcard t0 i
    have h2 := lt2_pert s (replE A w η) hcard t i
    rw [lt2Half_replE, lt2Eps_replE, hS, lt2Pi_eq_PiE _ _ _ hio, ← hS] at h1 h2
    simp only [D, F, P]
    rw [abs_le] at h1 h2 ⊢; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hrefl : ∀ η, P (reflE A η) = -P η := fun η => by
    simp only [P]; rw [lt2PiE_reflE s w η t0 hio, lt2PiE_reflE s w η t hio]; ring
  set G := {η : Param N | M - 2 * ε ≤ |D η|}
  have hGm : MeasurableSet G := by
    refine measurableSet_le measurable_const ?_
    exact (((lt2_meas_NumNs _ _ _).comp (lt2_meas_replE A w)).sub
      ((lt2_meas_NumNs _ _ _).comp (lt2_meas_replE A w))).abs
  have hcover : ∀ η, η ∈ G ∨ reflE A η ∈ G := by
    intro η
    have hd1 := hdec η
    have hd2 := hdec (reflE A η)
    rw [hrefl] at hd2
    rw [abs_le] at hd1 hd2
    simp only [G, Set.mem_setOf_eq]
    rcases le_abs'.1 hF with hneg | hpos
    · -- `F t0 - F t ≤ -M`
      by_cases hP : P η ≤ 0
      · left; rw [le_abs']; left; linarith [hd1.2]
      · right; rw [le_abs']; left; linarith [hd2.2]
    · by_cases hP : 0 ≤ P η
      · left; rw [le_abs']; right; linarith [hd1.1]
      · right; rw [le_abs']; right; linarith [hd2.1]
  have mp := lt2_mp_reflE (N := N) A
  have hpre : cubeM N (reflE A ⁻¹' G) = cubeM N G := mp.measure_preimage hGm.nullMeasurableSet
  have h1 : (1 : ENNReal) ≤ cubeM N G + cubeM N (reflE A ⁻¹' G) := by
    calc (1 : ENNReal) = cubeM N Set.univ := measure_univ.symm
      _ ≤ cubeM N (G ∪ reflE A ⁻¹' G) := measure_mono fun η _ => hcover η
      _ ≤ _ := measure_union_le _ _
  rw [hpre] at h1
  have h3 : (1 : ENNReal) ≤ cubeM N G * 2 := by rw [mul_two]; exact h1
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  exact ENNReal.div_le_of_le_mul h3

end Census
end IIT
