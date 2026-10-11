/-
Census, B1 lemma LT2, module M3 part 2: the own-entry statistics (W2 Lemma P1b, AC).

`Õ_i(T) = Σ_v P_ns(v) (y_{v,i} - 3/4) χ_T(v)`.  A signed sum over a set `A` of pairs `(i, T)` is a row-local sum
`Σ_v G_v(w v)` with `Σ_v E G_v = 0`; since `P_ns ≤ P` pointwise, `E[G_v²] ≤ E[P² (Σ_i a_{v,i}(y_i - 3/4))²]
= 3^{-N} (3/80) Σ_i a_{v,i}²` (under the `P²`-weight the factors `y_i - 3/4` are uncorrelated), and
`Σ_v Σ_i a_{v,i}² = 2^N |A|`.  Bernstein and the count union give `lt2_Ot_count`.
-/
import IIT.Census.B1LT2Stats
import IIT.Census.B1SmallBall

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-! ### A general row-local Bernstein bound -/

theorem lt2_rowloc_tail (G : State N → (Fin N → ℝ) → ℝ) (hG : ∀ v, Measurable (G v)) {M : ℝ}
    (hM : ∀ v x, |G v x| ≤ M) (h0 : ∑ v, ∫ x, G v x ∂rowM N = 0) {V ε : ℝ} (hε : 0 ≤ ε)
    (hV : ∑ v, ∫ x, G v x ^ 2 ∂rowM N ≤ V) :
    (cubeM N).real {w | ε ≤ ∑ v, G v (w v)} ≤ Real.exp (-min (ε ^ 2 / (4 * V)) (ε / (2 * (2 * M)))) := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  haveI : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (Classical.arbitrary _) 0)
  have hGi : ∀ v, Integrable (G v) (rowM N) := fun v =>
    Integrable.of_bound (hG v).aestronglyMeasurable M (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hM v x)
  set E : State N → ℝ := fun v => ∫ x, G v x ∂rowM N
  have hE : ∀ v, |E v| ≤ M := fun v => by
    calc |E v| ≤ ∫ x, |G v x| ∂rowM N := abs_integral_le_integral_abs
      _ ≤ ∫ _x, M ∂rowM N := integral_mono (hGi v).abs (integrable_const M) (hM v)
      _ = M := by simp
  set X : State N → Param N → ℝ := fun v w => G v (w v) - E v with hX
  have hind : iIndepFun X (cubeM N) :=
    iIndepFun_rows (N := N) (fun v x => G v x - E v) (fun v => (hG v).sub measurable_const)
  have hsum : ∀ w, ∑ v, G v (w v) = ∑ v, X v w := by
    intro w; simp only [hX, Finset.sum_sub_distrib]; rw [show ∑ v, E v = 0 from h0, sub_zero]
  simp_rw [hsum]
  refine bernstein_upper univ hind (fun v => (((hG v).comp (measurable_pi_apply v)).sub
    measurable_const).aemeasurable) (by positivity) hε (fun v _ => ae_of_all _ fun w => ?_) (fun v _ => ?_) ?_
  · simp only [hX]; exact (abs_sub _ _).trans (by linarith [hM v (w v), hE v])
  · simp only [hX]
    rw [lt2_int_row (fun x => G v x - E v) ((hG v).sub measurable_const) v,
      integral_sub (hGi v) (integrable_const _), integral_const]
    simp [E]
  · refine le_trans (Finset.sum_le_sum fun v _ => ?_) hV
    simp only [hX]
    rw [lt2_int_row (fun x => (G v x - E v) ^ 2) (((hG v).sub measurable_const).pow_const 2) v]
    have hGi2 : Integrable (fun x => G v x ^ 2) (rowM N) :=
      Integrable.of_bound ((hG v).pow_const 2).aestronglyMeasurable (M ^ 2) (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have := hM v x; nlinarith [abs_nonneg (G v x), sq_abs (G v x)])
    have e : ∫ x, (G v x - E v) ^ 2 ∂rowM N = ∫ x, G v x ^ 2 ∂rowM N - E v ^ 2 := by
      have : (fun x => (G v x - E v) ^ 2) = fun x => G v x ^ 2 - 2 * E v * G v x + E v ^ 2 := by
        funext x; ring
      rw [this, integral_add (f := fun x => G v x ^ 2 - 2 * E v * G v x) (g := fun _ => E v ^ 2)
        (hGi2.sub ((hGi v).const_mul _)) (integrable_const _),
        integral_sub (f := fun x => G v x ^ 2) (g := fun x => 2 * E v * G v x) hGi2 ((hGi v).const_mul _),
        integral_const_mul, integral_const]
      simp [E]; ring
    rw [e]; nlinarith [sq_nonneg (E v)]

/-! ### Signed character sums -/

lemma lt2_signed_chi_sq (B B' : Finset (Finset (Fin N))) :
    ∑ v : State N, (∑ T ∈ B, (if T ∈ B' then (1 : ℝ) else -1) * lt2Chi T v) ^ 2 = (2 : ℝ) ^ N * B.card := by
  have hsign : ∀ T, (if T ∈ B' then (1 : ℝ) else -1) ^ 2 = 1 := fun T => by split_ifs <;> norm_num
  simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ T ∈ B, ∑ v, ∑ T' ∈ B, (if T ∈ B' then (1 : ℝ) else -1) * lt2Chi T v *
      ((if T' ∈ B' then (1 : ℝ) else -1) * lt2Chi T' v) = (2 : ℝ) ^ N := by
    intro T hT
    rw [Finset.sum_comm, Finset.sum_eq_single T]
    · have h := lt2_sum_chi_mul T T
      rw [if_pos rfl] at h
      rw [← h]
      refine Finset.sum_congr rfl fun v _ => ?_
      calc (if T ∈ B' then (1 : ℝ) else -1) * lt2Chi T v * ((if T ∈ B' then (1 : ℝ) else -1) * lt2Chi T v)
          = (if T ∈ B' then (1 : ℝ) else -1) ^ 2 * (lt2Chi T v * lt2Chi T v) := by ring
        _ = _ := by rw [hsign, one_mul]
    · intro T' _ hne
      have h := lt2_sum_chi_mul T T'
      rw [if_neg (Ne.symm hne)] at h
      calc ∑ v, (if T ∈ B' then (1 : ℝ) else -1) * lt2Chi T v * ((if T' ∈ B' then (1 : ℝ) else -1) * lt2Chi T' v)
          = (if T ∈ B' then (1 : ℝ) else -1) * (if T' ∈ B' then (1 : ℝ) else -1) *
              ∑ v, lt2Chi T v * lt2Chi T' v := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
        _ = 0 := by rw [h, mul_zero]
    · intro h; exact absurd hT h
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-! ### The `P²`-weighted moments -/

lemma lt2_int_unif_poly (f : ℝ → ℝ) (hf : Continuous f) : ∫ u, f (clamp01 u) ∂unif = ∫ u in (0 : ℝ)..1, f u :=
  sb_unif_eq_interval f

/-- `E[P² (y_i - 3/4)(y_k - 3/4)] = 1{i = k} 3^{-N} (3/80)`. -/
lemma lt2_P2_cross (i k : Fin N) :
    ∫ x, (∏ j, clamp01 (x j)) ^ 2 * ((clamp01 (x i) - 3 / 4) * (clamp01 (x k) - 3 / 4)) ∂rowM N =
      if i = k then (1 / 3 : ℝ) ^ N * (3 / 80) else 0 := by
  set f : Fin N → ℝ → ℝ := fun j u => clamp01 u ^ 2 * (if j = i then clamp01 u - 3 / 4 else 1) *
    (if j = k then clamp01 u - 3 / 4 else 1) with hf
  have e : ∀ x : Fin N → ℝ, (∏ j, clamp01 (x j)) ^ 2 * ((clamp01 (x i) - 3 / 4) * (clamp01 (x k) - 3 / 4)) =
      ∏ j, f j (x j) := by
    intro x
    simp only [hf, Finset.prod_mul_distrib, ← Finset.prod_pow]
    rw [Finset.prod_ite_eq' univ i, Finset.prod_ite_eq' univ k]
    simp; ring
  simp_rw [e]
  unfold rowM
  rw [integral_fintype_prod_eq_prod (f := f)]
  have hsq : ∫ u, clamp01 u ^ 2 ∂unif = 1 / 3 := by
    rw [lt2_int_unif_poly (fun u => u ^ 2) (by fun_prop), integral_pow]; norm_num
  have h1 : ∫ u, clamp01 u ^ 2 * (clamp01 u - 3 / 4) ∂unif = 0 := by
    rw [lt2_int_unif_poly (fun u => u ^ 2 * (u - 3 / 4)) (by fun_prop)]
    have : (fun u : ℝ => u ^ 2 * (u - 3 / 4)) = fun u => u ^ 3 - 3 / 4 * u ^ 2 := by funext u; ring
    rw [this, intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul, integral_pow, integral_pow]
    norm_num
  have h2 : ∫ u, clamp01 u ^ 2 * (clamp01 u - 3 / 4) * (clamp01 u - 3 / 4) ∂unif = 1 / 80 := by
    rw [lt2_int_unif_poly (fun u => u ^ 2 * (u - 3 / 4) * (u - 3 / 4)) (by fun_prop)]
    have : (fun u : ℝ => u ^ 2 * (u - 3 / 4) * (u - 3 / 4)) = fun u => u ^ 4 - 3 / 2 * u ^ 3 + 9 / 16 * u ^ 2 := by
      funext u; ring
    rw [this, intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow, integral_pow,
      integral_pow]
    norm_num
  split_ifs with hik
  · subst hik
    rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
    have hrest : ∏ j ∈ univ.erase i, ∫ u, f j u ∂unif = (1 / 3 : ℝ) ^ (N - 1) := by
      rw [Finset.prod_congr rfl fun j hj => show ∫ u, f j u ∂unif = 1 / 3 by
        simp only [hf, if_neg (Finset.ne_of_mem_erase hj), mul_one]; exact hsq]
      rw [Finset.prod_const, Finset.card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
    have hi : ∫ u, f i u ∂unif = 1 / 80 := by simp only [hf, if_pos rfl]; exact h2
    rw [hrest, hi]
    have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 fun h => by subst h; exact i.elim0
    rw [show (1 / 3 : ℝ) ^ N = (1 / 3) ^ (N - 1) * (1 / 3) by
      rw [← pow_succ, Nat.sub_add_cancel hN]]
    ring
  · refine Finset.prod_eq_zero (mem_univ i) ?_
    simp only [hf, if_true, if_neg hik, mul_one]; exact h1

/-- `E[P² (Σ_i a_i (y_i - 3/4))²] = 3^{-N} (3/80) Σ_i a_i²`. -/
lemma lt2_P2_quad (a : Fin N → ℝ) :
    ∫ x, (∏ j, clamp01 (x j)) ^ 2 * (∑ i, a i * (clamp01 (x i) - 3 / 4)) ^ 2 ∂rowM N =
      (1 / 3 : ℝ) ^ N * (3 / 80) * ∑ i, a i ^ 2 := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  have hP : Measurable fun x : Fin N → ℝ => (∏ j, clamp01 (x j)) ^ 2 := measurable_rowPw.pow_const 2
  have hc : ∀ i, Measurable fun x : Fin N → ℝ => clamp01 (x i) - 3 / 4 := fun i =>
    (clamp01_measurable.comp (measurable_pi_apply i)).sub measurable_const
  have hint : ∀ i k, Integrable (fun x : Fin N → ℝ => (∏ j, clamp01 (x j)) ^ 2 *
      ((clamp01 (x i) - 3 / 4) * (clamp01 (x k) - 3 / 4))) (rowM N) := by
    intro i k
    refine Integrable.of_bound (hP.mul ((hc i).mul (hc k))).aestronglyMeasurable 1 (ae_of_all _ fun x => ?_)
    have h0 : 0 ≤ (∏ j, clamp01 (x j)) ^ 2 := sq_nonneg _
    have h1 : (∏ j, clamp01 (x j)) ^ 2 ≤ 1 := pow_le_one₀ (Finset.prod_nonneg fun j _ => clamp01_nonneg _)
      (Finset.prod_le_one (fun j _ => clamp01_nonneg _) fun j _ => clamp01_le_one _)
    have hi : |clamp01 (x i) - 3 / 4| ≤ 1 := abs_le.2 ⟨by linarith [clamp01_nonneg (x i)],
      by linarith [clamp01_le_one (x i)]⟩
    have hk : |clamp01 (x k) - 3 / 4| ≤ 1 := abs_le.2 ⟨by linarith [clamp01_nonneg (x k)],
      by linarith [clamp01_le_one (x k)]⟩
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h0]
    calc (∏ j, clamp01 (x j)) ^ 2 * (|clamp01 (x i) - 3 / 4| * |clamp01 (x k) - 3 / 4|)
        ≤ 1 * (1 * 1) := mul_le_mul h1 (mul_le_mul hi hk (abs_nonneg _) zero_le_one) (by positivity) zero_le_one
      _ = 1 := by norm_num
  have e : ∀ x : Fin N → ℝ, (∏ j, clamp01 (x j)) ^ 2 * (∑ i, a i * (clamp01 (x i) - 3 / 4)) ^ 2 =
      ∑ i, ∑ k, a i * a k * ((∏ j, clamp01 (x j)) ^ 2 * ((clamp01 (x i) - 3 / 4) * (clamp01 (x k) - 3 / 4))) := by
    intro x
    rw [sq (∑ i, _), Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e]
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun k _ => (hint i k).const_mul _]
  simp_rw [integral_finset_sum _ fun k _ => (hint _ k).const_mul _, integral_const_mul, lt2_P2_cross]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The own-entry statistic `Õ_i(T) = Σ_v P_ns(v) (y_{v,i} - 3/4) χ_T(v)`. -/
noncomputable def lt2Ot (w : Param N) (p : Fin N × Finset (Fin N)) : ℝ :=
  ∑ v, lt2gNs (w v) * (clamp01 (w v p.1) - 3 / 4) * lt2Chi p.2 v

/-- **Tail of a signed sum of own-entry statistics.** -/
theorem lt2_Ot_signed_tail (A A' : Finset (Fin N × Finset (Fin N))) (hA : ∀ p ∈ A, p.2.Nonempty) {ε : ℝ}
    (hε : 0 ≤ ε) :
    (cubeM N).real {w | ε ≤ ∑ p ∈ A, (if p ∈ A' then lt2Ot w p else -lt2Ot w p)} ≤
      Real.exp (-min (ε ^ 2 / (4 * ((2 / 3 : ℝ) ^ N * (3 / 80) * A.card)))
        (ε / (2 * (2 * (lt2θ N * (3 / 4 * A.card)))))) := by
  set sg : Fin N × Finset (Fin N) → ℝ := fun p => if p ∈ A' then 1 else -1 with hsg
  set G : State N → (Fin N → ℝ) → ℝ := fun v x =>
    lt2gNs x * ∑ p ∈ A, sg p * ((clamp01 (x p.1) - 3 / 4) * lt2Chi p.2 v) with hG
  have hrew : ∀ w : Param N, ∑ p ∈ A, (if p ∈ A' then lt2Ot w p else -lt2Ot w p) = ∑ v, G v (w v) := by
    intro w
    simp only [hG, lt2Ot, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hsg]
    split_ifs
    · exact Finset.sum_congr rfl fun v _ => by ring
    · rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun v _ => by ring
  simp_rw [hrew]
  have hsg1 : ∀ p, |sg p| = 1 := fun p => by simp only [hsg]; split_ifs <;> norm_num
  have hGm : ∀ v, Measurable (G v) := fun v => lt2gNs_measurable.mul (Finset.measurable_sum _ fun p _ =>
    measurable_const.mul (((clamp01_measurable.comp (measurable_pi_apply p.1)).sub measurable_const).mul_const _))
  refine lt2_rowloc_tail G hGm (M := lt2θ N * (3 / 4 * A.card)) (fun v x => ?_) ?_ hε ?_
  · simp only [hG]
    rw [abs_mul, abs_of_nonneg (lt2gNs_nonneg x)]
    refine mul_le_mul (lt2gNs_le x) ?_ (abs_nonneg _) (Real.exp_pos _).le
    calc |∑ p ∈ A, sg p * ((clamp01 (x p.1) - 3 / 4) * lt2Chi p.2 v)|
        ≤ ∑ p ∈ A, |sg p * ((clamp01 (x p.1) - 3 / 4) * lt2Chi p.2 v)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ A, (3 / 4 : ℝ) := Finset.sum_le_sum fun p _ => by
          rw [abs_mul, abs_mul, hsg1, lt2Chi_abs, one_mul, mul_one]
          exact abs_le.2 ⟨by linarith [clamp01_nonneg (x p.1)], by linarith [clamp01_le_one (x p.1)]⟩
      _ = 3 / 4 * A.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  · -- the mean
    haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
    have hint : ∀ v (p : Fin N × Finset (Fin N)), Integrable (fun x : Fin N → ℝ =>
        lt2gNs x * (sg p * ((clamp01 (x p.1) - 3 / 4) * lt2Chi p.2 v))) (rowM N) := by
      intro v p
      refine Integrable.of_bound ((lt2gNs_measurable).mul (measurable_const.mul
        (((clamp01_measurable.comp (measurable_pi_apply p.1)).sub measurable_const).mul_const _))).aestronglyMeasurable
        (lt2θ N) (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, hsg1, lt2Chi_abs, abs_of_nonneg (lt2gNs_nonneg x)]
      have h1 : |clamp01 (x p.1) - 3 / 4| ≤ 1 := abs_le.2 ⟨by linarith [clamp01_nonneg (x p.1)],
        by linarith [clamp01_le_one (x p.1)]⟩
      calc lt2gNs x * (1 * (|clamp01 (x p.1) - 3 / 4| * 1)) ≤ lt2θ N * (1 * (1 * 1)) :=
            mul_le_mul (lt2gNs_le x) (by linarith) (by positivity) (Real.exp_pos _).le
        _ = lt2θ N := by ring
    simp only [hG, Finset.mul_sum]
    simp_rw [integral_finset_sum _ fun p _ => hint _ p]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun p hp => ?_
    have e : ∀ v, ∫ x, lt2gNs x * (sg p * ((clamp01 (x p.1) - 3 / 4) * lt2Chi p.2 v)) ∂rowM N =
        sg p * (∫ x, lt2gNs x * (clamp01 (x p.1) - 3 / 4) ∂rowM N) * lt2Chi p.2 v := by
      intro v
      rw [← integral_const_mul, ← integral_mul_const]
      exact integral_congr_ae (ae_of_all _ fun x => by ring)
    simp_rw [e, ← Finset.mul_sum, lt2_sum_chi (hA p hp), mul_zero]
  · -- the variance
    haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
    set a : State N → Fin N → ℝ := fun v i => ∑ p ∈ A.filter (fun p => p.1 = i), sg p * lt2Chi p.2 v with ha
    have hGa : ∀ v x, G v x = lt2gNs x * ∑ i, a v i * (clamp01 (x i) - 3 / 4) := by
      intro v x
      simp only [hG, ha, Finset.sum_mul]
      congr 1
      rw [← Finset.sum_fiberwise A (fun p => p.1)]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p hp => ?_
      rw [(mem_filter.1 hp).2]; ring
    have hle : ∀ v, ∫ x, G v x ^ 2 ∂rowM N ≤ (1 / 3 : ℝ) ^ N * (3 / 80) * ∑ i, a v i ^ 2 := by
      intro v
      rw [← lt2_P2_quad (a v)]
      have hbd : ∀ x : Fin N → ℝ, G v x ^ 2 ≤ (∏ j, clamp01 (x j)) ^ 2 * (∑ i, a v i * (clamp01 (x i) - 3 / 4)) ^ 2 := by
        intro x
        rw [hGa, mul_pow]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have h0 := lt2gNs_nonneg x
        have h1 : lt2gNs x ≤ ∏ j, clamp01 (x j) := by
          unfold lt2gNs; split_ifs
          · exact le_rfl
          · exact Finset.prod_nonneg fun j _ => clamp01_nonneg _
        exact pow_le_pow_left₀ h0 h1 2
      have hm : Measurable fun x : Fin N → ℝ => (∏ j, clamp01 (x j)) ^ 2 * (∑ i, a v i * (clamp01 (x i) - 3 / 4)) ^ 2 :=
        (measurable_rowPw.pow_const 2).mul ((Finset.measurable_sum _ fun i _ => measurable_const.mul
          ((clamp01_measurable.comp (measurable_pi_apply i)).sub measurable_const)).pow_const 2)
      have hB : ∀ x : Fin N → ℝ, |∑ i, a v i * (clamp01 (x i) - 3 / 4)| ≤ ∑ i, |a v i| := fun x =>
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          have : |clamp01 (x i) - 3 / 4| ≤ 1 := abs_le.2 ⟨by linarith [clamp01_nonneg (x i)],
            by linarith [clamp01_le_one (x i)]⟩
          nlinarith [abs_nonneg (a v i)])
      refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) (Integrable.of_bound hm.aestronglyMeasurable
        ((∑ i, |a v i|) ^ 2) (ae_of_all _ fun x => ?_)) (ae_of_all _ hbd)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 : (∏ j, clamp01 (x j)) ^ 2 ≤ 1 := pow_le_one₀ (Finset.prod_nonneg fun j _ => clamp01_nonneg _)
        (Finset.prod_le_one (fun j _ => clamp01_nonneg _) fun j _ => clamp01_le_one _)
      have h2 : (∑ i, a v i * (clamp01 (x i) - 3 / 4)) ^ 2 ≤ (∑ i, |a v i|) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
      nlinarith [sq_nonneg (∑ i, a v i * (clamp01 (x i) - 3 / 4))]
    have hsumsq : ∑ v, ∑ i, a v i ^ 2 = (2 : ℝ) ^ N * A.card := by
      rw [Finset.sum_comm]
      have hfib : ∀ i, ∑ v, a v i ^ 2 = (2 : ℝ) ^ N * (A.filter (fun p => p.1 = i)).card := by
        intro i
        set B := (A.filter (fun p => p.1 = i)).image Prod.snd
        set B' := ((A.filter (fun p => p.1 = i)).filter (fun p => p ∈ A')).image Prod.snd
        have hinj : Set.InjOn Prod.snd ((A.filter (fun p => p.1 = i)) : Set (Fin N × Finset (Fin N))) := by
          intro p hp q hq hpq
          have h1 := (mem_filter.1 hp).2; have h2 := (mem_filter.1 hq).2
          exact Prod.ext (h1.trans h2.symm) hpq
        have hcard : B.card = (A.filter (fun p => p.1 = i)).card := Finset.card_image_of_injOn hinj
        have ha' : ∀ v, a v i = ∑ T ∈ B, (if T ∈ B' then (1 : ℝ) else -1) * lt2Chi T v := by
          intro v
          simp only [ha]
          rw [Finset.sum_image (fun p hp q hq h => hinj hp hq h)]
          refine Finset.sum_congr rfl fun p hp => ?_
          congr 1
          simp only [hsg, B', mem_image, mem_filter]
          have hpi := (mem_filter.1 hp)
          split_ifs with h1 h2 h2
          · rfl
          · exact absurd ⟨p, ⟨⟨hpi.1, hpi.2⟩, h1⟩, rfl⟩ h2
          · obtain ⟨q, ⟨⟨hqA, hqi⟩, hq'⟩, hqp⟩ := h2
            have : q = p := Prod.ext (hqi.trans hpi.2.symm) hqp
            exact absurd (this ▸ hq') h1
          · rfl
        simp_rw [ha']
        rw [lt2_signed_chi_sq, hcard]
      simp_rw [hfib, ← Finset.mul_sum]
      congr 1
      have hcf := Finset.card_eq_sum_card_fiberwise (f := fun p : Fin N × Finset (Fin N) => p.1) (s := A)
        (t := univ) (fun p _ => mem_univ _)
      exact_mod_cast hcf.symm
    calc ∑ v, ∫ x, G v x ^ 2 ∂rowM N ≤ ∑ v, (1 / 3 : ℝ) ^ N * (3 / 80) * ∑ i, a v i ^ 2 :=
          Finset.sum_le_sum fun v _ => hle v
      _ = (1 / 3 : ℝ) ^ N * (3 / 80) * ((2 : ℝ) ^ N * A.card) := by rw [← Finset.mul_sum, hsumsq]
      _ = (2 / 3 : ℝ) ^ N * (3 / 80) * A.card := by
          rw [show (2 / 3 : ℝ) ^ N = (1 / 3) ^ N * 2 ^ N by rw [← mul_pow]; norm_num]; ring

/-- **Adverse count for the own-entry statistics.** -/
theorem lt2_Ot_count (Fam : Finset (Fin N × Finset (Fin N))) (hFam : ∀ p ∈ Fam, p.2.Nonempty) {κ : ℝ}
    (hκ : 0 < κ) (m : ℕ) (hm : 1 ≤ m) :
    cubeM N {w | m ≤ (Fam.filter fun p => κ * sigN N ≤ |lt2Ot w p|).card} ≤
      ENNReal.ofReal ((Fam.card.choose m) * 2 ^ m *
        Real.exp (-min (20 * m * κ ^ 2 / 3) (κ * sigN N / (3 * lt2θ N)))) := by
  haveI : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  have hσ : 0 < sigN N := by unfold sigN; positivity
  have hθ : 0 < lt2θ N := Real.exp_pos _
  refine lt2_count_union Fam (fun p w => lt2Ot w p) m (fun A hA hAc A' _ => ?_) (by positivity)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := lt2_Ot_signed_tail A A' (fun p hp => hFam p (hA hp)) (ε := m * (κ * sigN N)) (by positivity)
  rw [← ENNReal.ofReal_toReal (measure_ne_top (cubeM N) _)]
  refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
  congr 2
  rw [hAc]
  congr 1
  · rw [mul_pow, mul_pow, lt2_sigN_sq]; field_simp; ring
  · field_simp; ring

end Census
end IIT

#print axioms IIT.Census.lt2_Ot_count
