/-
Census, B1 lemma LT2, module M3 part 3c: the Gram events with `D = ∅` (row-local).

* `lt2_Gm_diag`: `P(Σ_{v ∈ Ω_b} P_ns(v)² ≥ 2σ_N²) ≤ exp(-min((10/9)^N/4, e^{N/200}/4))`.
* `lt2_Gm_off0`: for `U ∉ {∅, Λ}`, `P(|Σ_{v ∈ Ω_b} P_ns(v)² χ_U(v)| ≥ t) ≤ 2 exp(-min(t²/(4(2/5)^N), t/(2θ²)))`.
-/
import IIT.Census.B1LT2Gram

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ} {b : Bool}

lemma lt2gNs_pow_int (p : ℕ) : ∫ x, lt2gNs x ^ p ∂rowM N ≤ (1 / ((p : ℝ) + 1)) ^ N := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  have hle : ∀ x : Fin N → ℝ, lt2gNs x ^ p ≤ (∏ j, clamp01 (x j)) ^ p := by
    intro x
    have h1 : lt2gNs x ≤ ∏ j, clamp01 (x j) := by
      unfold lt2gNs; split_ifs
      · exact le_rfl
      · exact Finset.prod_nonneg fun j _ => clamp01_nonneg _
    exact pow_le_pow_left₀ (lt2gNs_nonneg x) h1 p
  have hi : Integrable (fun x : Fin N → ℝ => (∏ j, clamp01 (x j)) ^ p) (rowM N) :=
    Integrable.of_bound (measurable_rowPw.pow_const p).aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Finset.prod_nonneg fun j _ => clamp01_nonneg _) _)]
      exact pow_le_one₀ (Finset.prod_nonneg fun j _ => clamp01_nonneg _)
        (Finset.prod_le_one (fun j _ => clamp01_nonneg _) fun j _ => clamp01_le_one _))
  calc ∫ x, lt2gNs x ^ p ∂rowM N ≤ ∫ x, (∏ j, clamp01 (x j)) ^ p ∂rowM N :=
        integral_mono_of_nonneg (ae_of_all _ fun x => pow_nonneg (lt2gNs_nonneg x) p) hi (ae_of_all _ hle)
    _ = _ := integral_rowP_pow' p

lemma lt2θ_sq (N : ℕ) : lt2θ N ^ 2 = sigN N ^ 2 * Real.exp (-(N : ℝ) / 200) := by
  unfold lt2θ lt2x1
  rw [lt2_sigN_sq, ← Real.exp_nat_mul, show (2 / 3 : ℝ) = Real.exp (-(2 * x0)) by
    unfold x0; rw [show -(2 * (Real.log (3 / 2) / 2)) = Real.log (2 / 3) by
      rw [show (2 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, Real.log_inv]; ring, Real.exp_log (by norm_num)],
    ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1; ring

lemma lt2θ_le_one : lt2θ N ≤ 1 := by
  unfold lt2θ
  rw [Real.exp_le_one_iff]
  have h := lt2x1_bounds
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith [h.1]

/-- A centred row-local sum with weights `a_v` and the function `gNs²`. -/
lemma lt2_sq_weighted_tail (a : State N → ℝ) (ha : ∀ v, |a v| ≤ 1) {ε : ℝ} (hε : 0 ≤ ε) :
    (cubeM N).real {w | ε ≤ ∑ v, (lt2gNs (w v) ^ 2 - ∫ x, lt2gNs x ^ 2 ∂rowM N) * a v} ≤
      Real.exp (-min (ε ^ 2 / (4 * (2 / 5 : ℝ) ^ N)) (ε / (2 * (2 * lt2θ N ^ 2)))) := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  set m2 := ∫ x, lt2gNs x ^ 2 ∂rowM N
  have hm2 : 0 ≤ m2 := integral_nonneg fun x => sq_nonneg _
  have hm2θ : m2 ≤ lt2θ N ^ 2 := by
    calc m2 ≤ ∫ _x, lt2θ N ^ 2 ∂rowM N := integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
          (integrable_const _) (ae_of_all _ fun x => pow_le_pow_left₀ (lt2gNs_nonneg x) (lt2gNs_le x) 2)
      _ = lt2θ N ^ 2 := by simp
  have hgm : Measurable fun x : Fin N → ℝ => lt2gNs x ^ 2 := lt2gNs_measurable.pow_const 2
  have hint2 : Integrable (fun x : Fin N → ℝ => lt2gNs x ^ 2) (rowM N) :=
    Integrable.of_bound hgm.aestronglyMeasurable (lt2θ N ^ 2) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (lt2gNs_nonneg x) (lt2gNs_le x) 2)
  refine lt2_rowloc_tail (fun v x => (lt2gNs x ^ 2 - m2) * a v) (fun v => (hgm.sub measurable_const).mul_const _)
    (M := lt2θ N ^ 2) (fun v x => ?_) ?_ hε ?_
  · rw [abs_mul]
    have h1 : |lt2gNs x ^ 2 - m2| ≤ lt2θ N ^ 2 := abs_sub_le_iff.2 ⟨by
      linarith [pow_le_pow_left₀ (lt2gNs_nonneg x) (lt2gNs_le x) 2], by linarith [sq_nonneg (lt2gNs x)]⟩
    calc |lt2gNs x ^ 2 - m2| * |a v| ≤ lt2θ N ^ 2 * 1 :=
          mul_le_mul h1 (ha v) (abs_nonneg _) (sq_nonneg _)
      _ = lt2θ N ^ 2 := mul_one _
  · refine Finset.sum_eq_zero fun v _ => ?_
    rw [integral_mul_const, integral_sub hint2 (integrable_const _), integral_const]; simp [m2]
  · have hint4 : Integrable (fun x : Fin N → ℝ => lt2gNs x ^ 4) (rowM N) :=
      Integrable.of_bound (lt2gNs_measurable.pow_const 4).aestronglyMeasurable 1 (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (lt2gNs_nonneg x) 4)]
        exact pow_le_one₀ (lt2gNs_nonneg x) ((lt2gNs_le x).trans lt2θ_le_one))
    have hvar : ∀ v, ∫ x, ((lt2gNs x ^ 2 - m2) * a v) ^ 2 ∂rowM N ≤ (1 / 5 : ℝ) ^ N := by
      intro v
      have e : (fun x : Fin N → ℝ => ((lt2gNs x ^ 2 - m2) * a v) ^ 2) =
          fun x => a v ^ 2 * (lt2gNs x ^ 4 - 2 * m2 * lt2gNs x ^ 2 + m2 ^ 2) := by funext x; ring
      rw [e, integral_const_mul, integral_add (f := fun x => lt2gNs x ^ 4 - 2 * m2 * lt2gNs x ^ 2)
        (g := fun _ => m2 ^ 2) (hint4.sub (hint2.const_mul _)) (integrable_const _),
        integral_sub (f := fun x => lt2gNs x ^ 4) (g := fun x => 2 * m2 * lt2gNs x ^ 2) hint4 (hint2.const_mul _),
        integral_const_mul, integral_const]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
      have h4 := lt2gNs_pow_int (N := N) 4
      have ha2 : a v ^ 2 ≤ 1 := by nlinarith [ha v, abs_nonneg (a v), sq_abs (a v)]
      have hpos : 0 ≤ ∫ x, lt2gNs x ^ 4 ∂rowM N - 2 * m2 * m2 + m2 ^ 2 := by
        have := lt2gNs_pow_int (N := N) 4
        -- E g⁴ ≥ (E g²)² (Jensen via variance ≥ 0)
        have hj : m2 ^ 2 ≤ ∫ x, lt2gNs x ^ 4 ∂rowM N := by
          have hv : 0 ≤ ∫ x, (lt2gNs x ^ 2 - m2) ^ 2 ∂rowM N := integral_nonneg fun x => sq_nonneg _
          have e2 : (fun x : Fin N → ℝ => (lt2gNs x ^ 2 - m2) ^ 2) =
              fun x => lt2gNs x ^ 4 - 2 * m2 * lt2gNs x ^ 2 + m2 ^ 2 := by funext x; ring
          rw [e2, integral_add (f := fun x => lt2gNs x ^ 4 - 2 * m2 * lt2gNs x ^ 2) (g := fun _ => m2 ^ 2)
            (hint4.sub (hint2.const_mul _)) (integrable_const _),
            integral_sub (f := fun x => lt2gNs x ^ 4) (g := fun x => 2 * m2 * lt2gNs x ^ 2) hint4
              (hint2.const_mul _), integral_const_mul, integral_const] at hv
          simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hv
          nlinarith
        nlinarith
      norm_num at h4 ⊢
      nlinarith [mul_le_mul_of_nonneg_right ha2 hpos]
    calc ∑ v, ∫ x, ((lt2gNs x ^ 2 - m2) * a v) ^ 2 ∂rowM N ≤ ∑ _v : State N, (1 / 5 : ℝ) ^ N :=
          Finset.sum_le_sum fun v _ => hvar v
      _ = (2 / 5 : ℝ) ^ N := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          simp [div_pow]; ring

end Census
end IIT
