/-
Census, B1 lemma LT2, module M3 part 3e: row-local tails of the auxiliary sums and the `D = ∅` Gram events.

* `lt2_S1_tail`: `P(2 < Σ_{v ∈ F} P_ns(v)) ≤ exp(-min(1/(4σ²), 1/(2θ)))`.
* `lt2_S2_tail`: `P(2σ² < Σ_{v ∈ F} P_ns(v)²) ≤ exp(-min((10/9)^N/4, …))`.
* `lt2_Gm_zero`: `P(t ≤ |Gm(∅, U)|) ≤ 2 exp(…)` for `U ∉ {∅, Λ}`.
-/
import IIT.Census.B1LT2Gram3

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ} {b : Bool}

lemma lt2_card_states_le (F : Finset (State N)) : (F.card : ℝ) ≤ 2 ^ N := by
  have := Finset.card_le_univ F
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
  exact_mod_cast this

/-- **Tail of `Σ_F P_ns`.** -/
theorem lt2_S1_tail (F : Finset (State N)) :
    cubeM N {w | 2 < ∑ v ∈ F, lt2gNs (w v)} ≤
      ENNReal.ofReal (Real.exp (-min (1 / (4 * sigN N ^ 2)) (1 / (4 * lt2θ N)))) := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  haveI : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  set m1 := ∫ x, lt2gNs x ∂rowM N
  have hm1 : 0 ≤ m1 := integral_nonneg fun x => lt2gNs_nonneg x
  have hm1u : m1 ≤ (1 / 2 : ℝ) ^ N := by
    have h := lt2gNs_pow_int (N := N) 1
    simp only [pow_one] at h
    exact h.trans (le_of_eq (by norm_num))
  have hm1θ : m1 ≤ lt2θ N := by
    calc m1 ≤ ∫ _x, lt2θ N ∂rowM N := integral_mono_of_nonneg (ae_of_all _ fun x => lt2gNs_nonneg x)
          (integrable_const _) (ae_of_all _ lt2gNs_le)
      _ = lt2θ N := by simp
  have hint1 : Integrable (lt2gNs (N := N)) (rowM N) :=
    Integrable.of_bound lt2gNs_measurable.aestronglyMeasurable (lt2θ N) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (lt2gNs_nonneg x)]; exact lt2gNs_le x)
  set a : State N → ℝ := fun v => if v ∈ F then 1 else 0
  have hmean : m1 * ∑ v, a v ≤ 1 := by
    have : ∑ v, a v = F.card := by simp [a, Finset.sum_ite_mem]
    rw [this]
    calc m1 * F.card ≤ (1 / 2 : ℝ) ^ N * 2 ^ N :=
          mul_le_mul hm1u (lt2_card_states_le F) (Nat.cast_nonneg _) (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  have hint2 : Integrable (fun x => lt2gNs (N := N) x ^ 2) (rowM N) :=
    Integrable.of_bound (lt2gNs_measurable.pow_const 2).aestronglyMeasurable (lt2θ N ^ 2)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (lt2gNs_nonneg x) (lt2gNs_le x) 2)
  have hvar1 : ∫ x, (lt2gNs x - m1) ^ 2 ∂rowM N ≤ (1 / 3 : ℝ) ^ N := by
    have e : (fun x : Fin N → ℝ => (lt2gNs x - m1) ^ 2) = fun x => lt2gNs x ^ 2 - 2 * m1 * lt2gNs x + m1 ^ 2 := by
      funext x; ring
    rw [e, integral_add (f := fun x => lt2gNs x ^ 2 - 2 * m1 * lt2gNs x) (g := fun _ => m1 ^ 2)
      (hint2.sub (hint1.const_mul _)) (integrable_const _),
      integral_sub (f := fun x => lt2gNs x ^ 2) (g := fun x => 2 * m1 * lt2gNs x) hint2 (hint1.const_mul _),
      integral_const_mul, integral_const]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    have := lt2gNs_pow_int (N := N) 2
    norm_num at this ⊢
    nlinarith
  have ha2 : ∀ v, a v ^ 2 ≤ 1 := fun v => by simp only [a]; split_ifs <;> norm_num
  have h := lt2_rowloc_tail (fun v x => (lt2gNs x - m1) * a v) (fun v => (lt2gNs_measurable.sub
    measurable_const).mul_const _) (M := lt2θ N) (fun v x => by
      rw [abs_mul]
      have h1 : |lt2gNs x - m1| ≤ lt2θ N := abs_sub_le_iff.2 ⟨by linarith [lt2gNs_le x], by linarith [lt2gNs_nonneg x]⟩
      have h2 : |a v| ≤ 1 := by simp only [a]; split_ifs <;> norm_num
      calc |lt2gNs x - m1| * |a v| ≤ lt2θ N * 1 := mul_le_mul h1 h2 (abs_nonneg _) (Real.exp_pos _).le
        _ = lt2θ N := mul_one _)
    (Finset.sum_eq_zero fun v _ => by
      rw [integral_mul_const, integral_sub hint1 (integrable_const _), integral_const]; simp [m1])
    (V := sigN N ^ 2) (ε := 1) zero_le_one (by
      calc ∑ v, ∫ x, ((lt2gNs x - m1) * a v) ^ 2 ∂rowM N
          = ∑ v, (∫ x, (lt2gNs x - m1) ^ 2 ∂rowM N) * a v ^ 2 := Finset.sum_congr rfl fun v _ => by
            rw [← integral_mul_const]; exact integral_congr_ae (ae_of_all _ fun x => by ring)
        _ ≤ ∑ _v : State N, (1 / 3 : ℝ) ^ N * 1 := Finset.sum_le_sum fun v _ =>
            mul_le_mul hvar1 (ha2 v) (sq_nonneg _) (by positivity)
        _ = sigN N ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, lt2_sigN_sq]; simp [div_pow]; ring)
  have hsub : {w : Param N | 2 < ∑ v ∈ F, lt2gNs (w v)} ⊆
      {w | 1 ≤ ∑ v, (lt2gNs (w v) - m1) * a v} := by
    intro w hw
    simp only [Set.mem_setOf_eq] at hw ⊢
    have e : ∑ v ∈ F, lt2gNs (w v) = ∑ v, (lt2gNs (w v) - m1) * a v + m1 * ∑ v, a v := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      simp only [a, mul_ite, mul_one, mul_zero]
      have hx : ∀ x : State N, ((if x ∈ F then lt2gNs (w x) - m1 else 0) + if x ∈ F then m1 else 0) =
          if x ∈ F then lt2gNs (w x) else 0 := fun x => by split_ifs <;> ring
      rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_ite_mem, Finset.univ_inter]
    linarith
  refine (measure_mono hsub).trans ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal (h.trans (le_of_eq (by congr 2; ring_nf)))

/-- **Tail of `Σ_F P_ns²`.** -/
theorem lt2_S2_tail (F : Finset (State N)) :
    cubeM N {w | 2 * sigN N ^ 2 < ∑ v ∈ F, lt2gNs (w v) ^ 2} ≤
      ENNReal.ofReal (Real.exp (-min ((sigN N ^ 2) ^ 2 / (4 * (2 / 5 : ℝ) ^ N))
        (sigN N ^ 2 / (2 * (2 * lt2θ N ^ 2))))) := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  set m2 := ∫ x, lt2gNs x ^ 2 ∂rowM N
  have hm2 : m2 ≤ (1 / 3 : ℝ) ^ N := by
    have := lt2gNs_pow_int (N := N) 2; norm_num at this ⊢; exact this
  set a : State N → ℝ := fun v => if v ∈ F then 1 else 0
  have h := lt2_sq_weighted_tail a (fun v => by simp only [a]; split_ifs <;> norm_num)
    (ε := sigN N ^ 2) (sq_nonneg _)
  have hsub : {w : Param N | 2 * sigN N ^ 2 < ∑ v ∈ F, lt2gNs (w v) ^ 2} ⊆
      {w | sigN N ^ 2 ≤ ∑ v, (lt2gNs (w v) ^ 2 - m2) * a v} := by
    intro w hw
    simp only [Set.mem_setOf_eq] at hw ⊢
    have e : ∑ v ∈ F, lt2gNs (w v) ^ 2 = ∑ v, (lt2gNs (w v) ^ 2 - m2) * a v + m2 * F.card := by
      have hx : ∀ x : State N, (lt2gNs (w x) ^ 2 - m2) * a x + (if x ∈ F then m2 else 0) =
          if x ∈ F then lt2gNs (w x) ^ 2 else 0 := fun x => by simp only [a]; split_ifs <;> ring
      rw [show m2 * F.card = ∑ x, (if x ∈ F then m2 else 0) by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm],
        ← Finset.sum_add_distrib, Finset.sum_congr rfl fun x _ => hx x, Finset.sum_ite_mem, Finset.univ_inter]
    have hcard : m2 * F.card ≤ sigN N ^ 2 := by
      have hm20 : 0 ≤ m2 := integral_nonneg fun x => sq_nonneg _
      calc m2 * F.card ≤ (1 / 3 : ℝ) ^ N * 2 ^ N :=
            mul_le_mul hm2 (lt2_card_states_le F) (Nat.cast_nonneg _) (by positivity)
        _ = sigN N ^ 2 := by rw [lt2_sigN_sq, ← mul_pow]; norm_num
    linarith
  refine (measure_mono hsub).trans ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal h

lemma lt2Xor_empty (v : State N) : lt2Xor v ∅ = v := by funext j; simp [lt2Xor]

/-- **The `D = ∅` Gram event** (`U ∉ {∅, Λ}`). -/
theorem lt2_Gm_zero (Λ U : Finset (Fin N)) (hU : U.Nonempty) (hUΛ : U ≠ Λ) {t : ℝ} (ht : 0 ≤ t) :
    cubeM N {w | t ≤ |lt2Gm Λ b ∅ U w|} ≤
      ENNReal.ofReal (2 * Real.exp (-min (t ^ 2 / (4 * (2 / 5 : ℝ) ^ N)) (t / (2 * (2 * lt2θ N ^ 2))))) := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  haveI : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  set m2 := ∫ x, lt2gNs x ^ 2 ∂rowM N
  set a : State N → ℝ := fun v => if v ∈ lt2Om0 Λ b then lt2Chi U v else 0
  have ha : ∀ v, |a v| ≤ 1 := fun v => by simp only [a]; split_ifs <;> simp [lt2Chi_abs]
  have hna : ∀ v, |-a v| ≤ 1 := fun v => by rw [abs_neg]; exact ha v
  have e : ∀ w : Param N, lt2Gm Λ b ∅ U w = ∑ v, (lt2gNs (w v) ^ 2 - m2) * a v := by
    intro w
    unfold lt2Gm
    simp only [lt2Xor_empty]
    have hsum0 : ∑ v, m2 * a v = 0 := by
      rw [← Finset.mul_sum]
      simp only [a]
      rw [Finset.sum_ite_mem, Finset.univ_inter, lt2_sum_Om0_chi Λ U hU hUΛ, mul_zero]
    have : ∑ v, (lt2gNs (w v) ^ 2 - m2) * a v = ∑ v, lt2gNs (w v) ^ 2 * a v - ∑ v, m2 * a v := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun v _ => by ring
    rw [this, hsum0, sub_zero]
    simp only [a, mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    exact Finset.sum_congr rfl fun v _ => by ring
  have h1 := lt2_sq_weighted_tail a ha ht
  have h2 := lt2_sq_weighted_tail (fun v => -a v) hna ht
  have hsub : {w : Param N | t ≤ |lt2Gm Λ b ∅ U w|} ⊆
      {w | t ≤ ∑ v, (lt2gNs (w v) ^ 2 - m2) * a v} ∪ {w | t ≤ ∑ v, (lt2gNs (w v) ^ 2 - m2) * -a v} := by
    intro w hw
    simp only [Set.mem_setOf_eq, Set.mem_union] at hw ⊢
    rw [e] at hw
    rcases le_abs'.1 hw with h | h
    · right
      have : ∑ v, (lt2gNs (w v) ^ 2 - m2) * -a v = -∑ v, (lt2gNs (w v) ^ 2 - m2) * a v := by
        rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun v _ => by ring
      rw [this]; linarith
    · left; exact h
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [← ENNReal.ofReal_toReal (measure_ne_top (cubeM N) {w | t ≤ ∑ v, (lt2gNs (w v) ^ 2 - m2) * a v}),
    ← ENNReal.ofReal_toReal (measure_ne_top (cubeM N) {w | t ≤ ∑ v, (lt2gNs (w v) ^ 2 - m2) * -a v}),
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  apply ENNReal.ofReal_le_ofReal
  have h1' : (cubeM N).real {w | t ≤ ∑ v, (lt2gNs (w v) ^ 2 - m2) * a v} ≤ _ := h1
  have h2' : (cubeM N).real {w | t ≤ ∑ v, (lt2gNs (w v) ^ 2 - m2) * -a v} ≤ _ := h2
  simp only [measureReal_def] at h1' h2'
  linarith

end Census
end IIT
