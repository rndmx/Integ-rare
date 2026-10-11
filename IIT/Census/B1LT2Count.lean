/-
Census, B1 lemma LT2, module M6c-1: transferring a count through the private resampling.

`lt2_count_transfer`: let `Z(w) ⊆ U` be a set of indices read on the shared data, and `Y_p` events such that
for every `w` and `p ∈ Z(w)`, resampling the private entries lands in `Y_p` with probability `≥ 1/2`. Then
`P(#Z ≥ m) · m/(4|U|) ≤ P(#{p ∈ U : w ∈ Y_p} ≥ m/4)`.
-/
import IIT.Census.B1LT2Pair5

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

lemma lt2_meas_replE (C : Finset (State N × Fin N)) (w : Param N) : Measurable fun η : Param N => replE C w η := by
  refine measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun i => ?_
  unfold replE
  split_ifs
  · exact (measurable_pi_apply i).comp (measurable_pi_apply r)
  · exact measurable_const

open Classical in
/-- Reverse Markov for a bounded count: `E X ≥ m/2`, `X ≤ n` give `P(X ≥ m/4) ≥ m/(4n)`. -/
lemma lt2_reverse_markov {ι : Type*} (U : Finset ι) (S : ι → Set (Param N)) (hS : ∀ p, MeasurableSet (S p))
    {m : ℝ} (hm : 0 ≤ m) (hE : ENNReal.ofReal (m / 2) ≤ ∑ p ∈ U, cubeM N (S p)) (hU : 0 < U.card) :
    ENNReal.ofReal (m / (4 * U.card)) ≤
      cubeM N {η | m / 4 ≤ ((U.filter fun p => η ∈ S p).card : ℝ)} := by
  classical
  haveI : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  set n : ℝ := (U.card : ℝ)
  have hn : 0 < n := Nat.cast_pos.2 hU
  set X : Param N → ℝ := fun η => ((U.filter fun p => η ∈ S p).card : ℝ)
  have hXeq : ∀ η, X η = ∑ p ∈ U, (S p).indicator (fun _ => (1 : ℝ)) η := fun η => by
    simp only [X, Set.indicator_apply]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hXm : Measurable X := by
    have : X = fun η => ∑ p ∈ U, (S p).indicator (fun _ => (1 : ℝ)) η := funext hXeq
    rw [this]; exact Finset.measurable_sum _ fun p _ => measurable_const.indicator (hS p)
  set T := {η : Param N | m / 4 ≤ X η}
  have hT : MeasurableSet T := measurableSet_le measurable_const hXm
  have hXle : ∀ η, X η ≤ n := fun η => by simp only [X, n]; exact_mod_cast Finset.card_filter_le _ _
  have hX0 : ∀ η, 0 ≤ X η := fun η => Nat.cast_nonneg _
  -- `X ≤ m/4 + n 1_T`
  have hpt : ∀ η, X η ≤ m / 4 + n * T.indicator (fun _ => (1 : ℝ)) η := fun η => by
    by_cases h : η ∈ T
    · rw [Set.indicator_of_mem h]; linarith [hXle η]
    · rw [Set.indicator_of_notMem h]; simp only [T, Set.mem_setOf_eq, not_le] at h; linarith
  have hint : Integrable X (cubeM N) := Integrable.of_bound hXm.aestronglyMeasurable n
    (ae_of_all _ fun η => by rw [Real.norm_eq_abs, abs_of_nonneg (hX0 η)]; exact hXle η)
  have hEX : ∫ η, X η ∂cubeM N = ∑ p ∈ U, (cubeM N).real (S p) := by
    simp_rw [hXeq]
    rw [integral_finset_sum _ fun p _ => (integrable_const _).indicator (hS p)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show (S p).indicator (fun _ => (1 : ℝ)) = (S p).indicator 1 from rfl, integral_indicator_one (hS p)]
  have hEX' : m / 2 ≤ ∫ η, X η ∂cubeM N := by
    rw [hEX]
    have h1 : ∑ p ∈ U, (cubeM N).real (S p) = (∑ p ∈ U, cubeM N (S p)).toReal := by
      rw [ENNReal.toReal_sum fun p _ => measure_ne_top _ _]; rfl
    rw [h1]
    exact (ENNReal.ofReal_le_iff_le_toReal (ENNReal.sum_ne_top.2 fun p _ => measure_ne_top _ _)).1 hE
  have hup : ∫ η, X η ∂cubeM N ≤ m / 4 + n * (cubeM N).real T := by
    calc ∫ η, X η ∂cubeM N ≤ ∫ η, (m / 4 + n * T.indicator (fun _ => (1 : ℝ)) η) ∂cubeM N :=
          integral_mono hint ((integrable_const _).add (((integrable_const _).indicator hT).const_mul n)) hpt
      _ = m / 4 + n * (cubeM N).real T := by
          rw [integral_add (integrable_const _) (((integrable_const _).indicator hT).const_mul n),
            integral_const, integral_const_mul,
            show T.indicator (fun _ => (1 : ℝ)) = T.indicator 1 from rfl, integral_indicator_one hT]
          simp [measureReal_def]
  have hfin : m / (4 * n) ≤ (cubeM N).real T := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hfin

open Classical in
/-- **Count transfer.** -/
theorem lt2_count_transfer (s : State N) {ι : Type*} [DecidableEq ι] (U : Finset ι) (hU : 0 < U.card)
    (Z : Param N → Finset ι) (hZU : ∀ w, Z w ⊆ U)
    (hZ : ∀ w w', (∀ q ∉ lt2Priv s w, w q.1 q.2 = w' q.1 q.2) → Z w' = Z w)
    {m : ℕ} (hZm : MeasurableSet {w : Param N | m ≤ (Z w).card})
    (Y : ι → Set (Param N)) (hYm : ∀ p, MeasurableSet (Y p))
    (hhalf : ∀ w, ∀ p ∈ Z w, ENNReal.ofReal (1 / 2) ≤ cubeM N {η | replE (lt2Priv s w) w η ∈ Y p}) :
    cubeM N {w | m ≤ (Z w).card} * ENNReal.ofReal ((m : ℝ) / (4 * U.card)) ≤
      cubeM N {w | (m : ℝ) / 4 ≤ ((U.filter fun p => w ∈ Y p).card : ℝ)} := by
  classical
  haveI : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  set W := {w : Param N | (m : ℝ) / 4 ≤ ((U.filter fun p => w ∈ Y p).card : ℝ)}
  have hWm : MeasurableSet W := by
    have : W = {w | (m : ℝ) / 4 ≤ ∑ p ∈ U, (Y p).indicator (fun _ => (1 : ℝ)) w} := by
      ext w; simp only [W, Set.mem_setOf_eq, Set.indicator_apply]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [this]
    exact measurableSet_le measurable_const (Finset.measurable_sum _ fun p _ =>
      measurable_const.indicator (hYm p))
  have hPm := lt2_mset_Priv (N := N) s
  -- partition over the value of `Priv`
  calc cubeM N {w | m ≤ (Z w).card} * ENNReal.ofReal ((m : ℝ) / (4 * U.card))
      = (∑ A, cubeM N ({w | m ≤ (Z w).card} ∩ {w | lt2Priv s w = A})) *
          ENNReal.ofReal ((m : ℝ) / (4 * U.card)) := by rw [← measure_eq_sum_partition _ hPm]
    _ = ∑ A, ENNReal.ofReal ((m : ℝ) / (4 * U.card)) *
          cubeM N ({w | lt2Priv s w = A} ∩ {w | m ≤ (Z w).card}) := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun A _ => by rw [mul_comm, Set.inter_comm]
    _ ≤ ∑ A, cubeM N (({w | lt2Priv s w = A} ∩ {w | m ≤ (Z w).card}) ∩ W) := by
        refine Finset.sum_le_sum fun A _ => ?_
        set X := {w | lt2Priv s w = A} ∩ {w : Param N | m ≤ (Z w).card}
        have hXm : MeasurableSet X := (hPm A).inter hZm
        have hXd : DetOnE Aᶜ X := by
          intro w w' h
          simp only [X, Set.mem_inter_iff, Set.mem_setOf_eq]
          constructor
          · rintro ⟨hA, hk⟩
            have hag : ∀ q ∉ lt2Priv s w, w q.1 q.2 = w' q.1 q.2 := fun q hq => h q (mem_compl.2 (hA ▸ hq))
            exact ⟨(lt2Priv_stop hag).trans hA, by rw [hZ w w' hag]; exact hk⟩
          · rintro ⟨hA, hk⟩
            have hag : ∀ q ∉ lt2Priv s w', w' q.1 q.2 = w q.1 q.2 := fun q hq =>
              (h q (mem_compl.2 (hA ▸ hq))).symm
            exact ⟨(lt2Priv_stop hag).trans hA, by rw [hZ w' w hag]; exact hk⟩
        rw [cubeM_inter_eq_setLIntegralE A hXm hWm hXd]
        calc ENNReal.ofReal ((m : ℝ) / (4 * U.card)) * cubeM N X
            = ∫⁻ _w in X, ENNReal.ofReal ((m : ℝ) / (4 * U.card)) ∂cubeM N := by
              rw [setLIntegral_const, mul_comm]
          _ ≤ ∫⁻ w in X, cubeM N {η | replE A w η ∈ W} ∂cubeM N := by
              refine setLIntegral_mono' hXm fun w hw => ?_
              obtain ⟨hA, hk⟩ := hw
              simp only [Set.mem_setOf_eq] at hA hk
              subst hA
              have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
              refine lt2_reverse_markov U (fun p => {η | replE (lt2Priv s w) w η ∈ Y p})
                (fun p => (lt2_meas_replE (lt2Priv s w) w) (hYm p)) hm0 ?_ hU
              calc ENNReal.ofReal ((m : ℝ) / 2) ≤ ∑ _p ∈ Z w, ENNReal.ofReal (1 / 2) := by
                    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
                    refine ENNReal.ofReal_le_ofReal ?_
                    have : (m : ℝ) ≤ (Z w).card := by exact_mod_cast hk
                    linarith
                _ ≤ ∑ p ∈ Z w, cubeM N {η | replE (lt2Priv s w) w η ∈ Y p} := Finset.sum_le_sum fun p hp => hhalf w p hp
                _ ≤ ∑ p ∈ U, cubeM N {η | replE (lt2Priv s w) w η ∈ Y p} :=
                    Finset.sum_le_sum_of_subset (hZU w)
    _ ≤ ∑ A, cubeM N (W ∩ {w | lt2Priv s w = A}) := by
        refine Finset.sum_le_sum fun A _ => measure_mono fun w hw => ⟨hw.2, hw.1.1⟩
    _ = cubeM N W := (measure_eq_sum_partition _ hPm W).symm

end Census
end IIT
