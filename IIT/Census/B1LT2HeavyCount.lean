/-
Census, B1 lemma LT2, module M4 part 3: the number of heavy rows.

`#{r : X(r) ≤ (38/100)N} ≤ 2·2^N p̄` with `p̄ = e^{-N I(0.38)}`, off probability `exp(-2^N p̄ / 8)` (row-local
Bernstein on the indicators). Hence `|H| ≤ 2·2^N p̄` and `ε ≤ 2·2^N p̄ (N+1)⁴ e^{-7N/10} + (N+1)⁴ θ`.
-/
import IIT.Census.B1LT2Pert
import IIT.Census.CertRatesCore

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- The Cramér bound for one row: `p̄ = e^{-N I(0.38)}`. -/
noncomputable def lt2pH (N : ℕ) : ℝ := Real.exp (-(N * (38 / 100 - 1 - Real.log (38 / 100))))

/-- The set of rows with `X ≤ 0.38N`. -/
def lt2HvSet (N : ℕ) : Set (Fin N → ℝ) := {x | ∑ i, -Real.log (clamp01 (x i)) ≤ 38 / 100 * (N : ℝ)}

lemma lt2_measurable_negLog : Measurable fun x : Fin N → ℝ => ∑ i, -Real.log (clamp01 (x i)) :=
  Finset.measurable_sum _ fun i _ => (Real.measurable_log.comp (measurable_clamp01.comp (measurable_pi_apply i))).neg

lemma lt2_mset_HvSet : MeasurableSet (lt2HvSet N) := measurableSet_le lt2_measurable_negLog measurable_const

lemma lt2_HvSet_le (hN : 0 < N) : (rowM N).real (lt2HvSet N) ≤ lt2pH N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := rowM_negLog_sum_le (N := N) univ (x := 38 / 100 * N) (by positivity) (by
    simp only [card_univ, Fintype.card_fin]; nlinarith)
  simp only [card_univ, Fintype.card_fin] at h
  rw [show 38 / 100 * (N : ℝ) / N = 38 / 100 by field_simp] at h
  unfold lt2HvSet lt2pH
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le h

open Classical in
/-- **The count of rows with `X ≤ 0.38N`.** -/
theorem lt2_heavy_count (hN : 0 < N) :
    (cubeM N).real {w | 2 * (2 ^ N * lt2pH N) < ((univ.filter fun r : State N => w r ∈ lt2HvSet N).card : ℝ)} ≤
      Real.exp (-(2 ^ N * lt2pH N / 8)) := by
  classical
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  set p := (rowM N).real (lt2HvSet N)
  set pb := lt2pH N
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := measureReal_le_one
  have hppb : p ≤ pb := lt2_HvSet_le hN
  have hpb : 0 < pb := Real.exp_pos _
  set G : State N → (Fin N → ℝ) → ℝ := fun _ x => (lt2HvSet N).indicator (fun _ => (1 : ℝ)) x - p
  have hG : ∀ v, Measurable (G v) := fun v =>
    (measurable_const.indicator lt2_mset_HvSet).sub measurable_const
  have hM : ∀ v x, |G v x| ≤ 1 := by
    intro v x; simp only [G]
    by_cases hx : x ∈ lt2HvSet N
    · rw [Set.indicator_of_mem hx, abs_le]; constructor <;> linarith
    · rw [Set.indicator_of_notMem hx, abs_le]; constructor <;> linarith
  have hint1 : ∫ x, (lt2HvSet N).indicator (fun _ => (1 : ℝ)) x ∂rowM N = p := by
    show ∫ x, (lt2HvSet N).indicator 1 x ∂rowM N = p
    rw [integral_indicator_one lt2_mset_HvSet]
  have hI : Integrable (fun x => (lt2HvSet N).indicator (fun _ => (1 : ℝ)) x) (rowM N) :=
    (integrable_const (1 : ℝ)).indicator lt2_mset_HvSet
  have h0 : ∑ v, ∫ x, G v x ∂rowM N = 0 := by
    refine Finset.sum_eq_zero fun v _ => ?_
    simp only [G]
    rw [integral_sub hI (integrable_const _), hint1, integral_const]
    simp [measureReal_def]
  have hV : ∑ v, ∫ x, G v x ^ 2 ∂rowM N ≤ 2 * (2 ^ N * pb) := by
    have hpt : ∀ v x, G v x ^ 2 ≤ (lt2HvSet N).indicator (fun _ => (1 : ℝ)) x + p ^ 2 := by
      intro v x; simp only [G]
      by_cases hx : x ∈ lt2HvSet N
      · rw [Set.indicator_of_mem hx]; nlinarith
      · rw [Set.indicator_of_notMem hx]; nlinarith
    have hone : ∀ v, ∫ x, G v x ^ 2 ∂rowM N ≤ 2 * pb := by
      intro v
      calc ∫ x, G v x ^ 2 ∂rowM N ≤ ∫ x, ((lt2HvSet N).indicator (fun _ => (1 : ℝ)) x + p ^ 2) ∂rowM N :=
            integral_mono (Integrable.of_bound ((hG v).pow_const 2).aestronglyMeasurable 1 (ae_of_all _ fun x => by
              rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
              have := hM v x
              nlinarith [abs_nonneg (G v x), sq_abs (G v x)])) (hI.add (integrable_const _)) (hpt v)
        _ ≤ 2 * pb := by
            rw [integral_add hI (integrable_const _), hint1, integral_const]
            simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
            nlinarith
    calc ∑ v, ∫ x, G v x ^ 2 ∂rowM N ≤ ∑ _v : State N, 2 * pb := Finset.sum_le_sum fun v _ => hone v
      _ = 2 * (2 ^ N * pb) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; simp; ring
  have hε : 0 ≤ 2 ^ N * pb := by positivity
  have htail := lt2_rowloc_tail G hG hM h0 hε hV
  refine le_trans (measureReal_mono ?_) (htail.trans (Real.exp_le_exp.2 ?_))
  · intro w hw
    simp only [Set.mem_setOf_eq] at hw ⊢
    have hcount : ((univ.filter fun r : State N => w r ∈ lt2HvSet N).card : ℝ) =
        ∑ v, G v (w v) + 2 ^ N * p := by
      simp only [G]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Finset.card_filter, Nat.cast_sum]
      simp only [Set.indicator_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      simp
    have : 2 ^ N * p ≤ 2 ^ N * pb := mul_le_mul_of_nonneg_left hppb (by positivity)
    linarith
  · have e1 : (2 ^ N * pb) ^ 2 / (4 * (2 * (2 ^ N * pb))) = 2 ^ N * pb / 8 := by
      field_simp; ring
    have e2 : 2 ^ N * pb / (2 * (2 * 1)) = 2 ^ N * pb / 4 := by ring
    rw [e1, e2, neg_le_neg_iff]
    exact le_min le_rfl (by linarith)

open Classical in
lemma lt2H_card_le (s : State N) (w : Param N) :
    ((lt2H s w).card : ℝ) ≤ ((univ.filter fun r : State N => w r ∈ lt2HvSet N).card : ℝ) := by
  classical
  refine Nat.cast_le.2 (Finset.card_le_card fun r hr => ?_)
  have hH := ((mem_filter.1 hr).2).1
  simp only [mem_filter, mem_univ, true_and]
  exact hH.2

/-- `log 0.38 ≤ -0.9675`. -/
lemma lt2_log38 : Real.log (38 / 100 : ℝ) ≤ -9675 / 10000 := by
  have hq : Real.log (((38 / 100 : ℚ)) : ℝ) ≤ (((-9675 / 10000 : ℚ)) : ℝ) := crLog_le (-1) 40 (by decide +kernel)
  push_cast at hq; exact hq

/-- **The perturbation bound is `≤ σ e^{-N/1000}`** on the heavy-count event. -/
theorem lt2_eps_small : ∀ᶠ N : ℕ in atTop, ∀ (s : State N) (w : Param N),
    ((lt2H s w).card : ℝ) ≤ 2 * (2 ^ N * lt2pH N) → lt2Eps s w ≤ sigN N * Real.exp (-(N : ℝ) / 1000) := by
  filter_upwards [cr_ev_poly_exp 4 (Real.log 4) (δ := 99 / 1000) (by norm_num),
    cr_ev_poly_exp 4 (Real.log 2) (δ := 3 / 2000) (by norm_num)] with N h1 h2 s w hH
  have hx0 := cr_x0_bounds
  have hhi : ((crX0hi : ℚ) : ℝ) ≤ 2028 / 10000 := by unfold crX0hi; push_cast; norm_num
  have hlo : ((crX0lo : ℚ) : ℝ) ≥ 2027 / 10000 := by unfold crX0lo; push_cast; norm_num
  have hl38 := lt2_log38
  have hl2 := Real.log_two_lt_d9
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hP : (0 : ℝ) ≤ ((N : ℝ) + 1) ^ 4 := by positivity
  have hσ : sigN N = Real.exp (-(x0 * N)) := sigN_eq_exp N
  rw [Real.exp_log (by norm_num)] at h1 h2
  unfold lt2Eps
  -- term 1
  have t1 : (lt2H s w).card * ((N : ℝ) + 1) ^ 4 * Real.exp (-(7 / 10 * (N : ℝ))) ≤
      sigN N * Real.exp (-(N : ℝ) / 1000) / 2 := by
    have e2N : (2 : ℝ) ^ N = Real.exp (Real.log 2 * N) := by
      rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_nat_mul, Real.exp_log (by norm_num)]; ring_nf
    calc (lt2H s w).card * ((N : ℝ) + 1) ^ 4 * Real.exp (-(7 / 10 * (N : ℝ)))
        ≤ 2 * (2 ^ N * lt2pH N) * ((N : ℝ) + 1) ^ 4 * Real.exp (-(7 / 10 * (N : ℝ))) := by gcongr
      _ = (((N : ℝ) + 1) ^ 4 * 4) * Real.exp ((Real.log 2 - (38 / 100 - 1 - Real.log (38 / 100)) - 7 / 10) * N) / 2 := by
          unfold lt2pH; rw [e2N]
          rw [show (2 : ℝ) * (Real.exp (Real.log 2 * N) * Real.exp (-(N * (38 / 100 - 1 - Real.log (38 / 100))))) *
            ((N : ℝ) + 1) ^ 4 * Real.exp (-(7 / 10 * (N : ℝ))) = ((N : ℝ) + 1) ^ 4 * 4 *
            (Real.exp (Real.log 2 * N) * Real.exp (-(N * (38 / 100 - 1 - Real.log (38 / 100)))) *
              Real.exp (-(7 / 10 * (N : ℝ)))) / 2 by ring]
          rw [← Real.exp_add, ← Real.exp_add]; congr 3; ring
      _ ≤ Real.exp (99 / 1000 * N) * Real.exp (-(x0 * N) - (N : ℝ) / 10) / 2 := by
          gcongr
          nlinarith
      _ = sigN N * Real.exp (-(N : ℝ) / 1000) / 2 := by
          rw [hσ, ← Real.exp_add, ← Real.exp_add]; congr 2; ring
  -- term 2
  have t2 : ((N : ℝ) + 1) ^ 4 * lt2θ N ≤ sigN N * Real.exp (-(N : ℝ) / 1000) / 2 := by
    unfold lt2θ lt2x1
    calc ((N : ℝ) + 1) ^ 4 * Real.exp (-((x0 + 1 / 400) * N))
        = (((N : ℝ) + 1) ^ 4 * 2) * Real.exp (-((x0 + 1 / 400) * N)) / 2 := by ring
      _ ≤ Real.exp (3 / 2000 * N) * Real.exp (-((x0 + 1 / 400) * N)) / 2 := by gcongr
      _ = sigN N * Real.exp (-(N : ℝ) / 1000) / 2 := by
          rw [hσ, ← Real.exp_add, ← Real.exp_add]; congr 2; ring
  linarith

end Census
end IIT
