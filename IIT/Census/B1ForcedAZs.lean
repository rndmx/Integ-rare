/-
Census, B1 forced leaves, part A0: the `Zs` regularity leaf (`bZs`), unconditional.

`Zs w = ∑_r P(r)` is a sum of `2^N` independent row products with `E P = 2^{-N}`, `E P² = 3^{-N}`.
* lower tail: `P(Zs ≤ 1/2) ≤ exp(-t/2 + t²(2/3)^N/2)`, `t = 3N` (via `e^{-y} ≤ 1 - y + y²/2`);
* upper tail: `P(Zs ≥ 13) ≤ exp(-12 t + t² e^t (2/3)^N / 2)`, `t = N/4` (via `e^u ≤ 1 + u + u² e^u/2`).
Both are `≤ e^{-3N/2}` eventually, so `P(Zs ∉ [1/2, 13]) ≤ e^{-(10105/10000) N}` eventually.
-/
import IIT.Census.B1Chernoff

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

noncomputable section

variable {N : ℕ}

lemma fa_exp_neg_le (y : ℝ) (hy : 0 ≤ y) : Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
  have h := Real.quadratic_le_exp_of_nonneg hy
  have hp : 0 < 1 + y + y ^ 2 / 2 := by positivity
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos y)]
  have : 1 ≤ (1 - y + y ^ 2 / 2) * (1 + y + y ^ 2 / 2) := by nlinarith [sq_nonneg (y ^ 2)]
  have h2 : 0 ≤ 1 - y + y ^ 2 / 2 := by nlinarith [sq_nonneg (y - 1)]
  nlinarith

lemma fa_exp_le_quad (u : ℝ) (hu : 0 ≤ u) : Real.exp u ≤ 1 + u + u ^ 2 * Real.exp u / 2 := by
  let f : ℝ → ℝ := fun x => 1 + x + x ^ 2 * Real.exp x / 2 - Real.exp x
  have hd : ∀ x, HasDerivAt f (1 + (2 * x * Real.exp x + x ^ 2 * Real.exp x) / 2 - Real.exp x) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2 * Real.exp x) (2 * x * Real.exp x + x ^ 2 * Real.exp x) x := by
      exact ((hasDerivAt_pow 2 x).mul (Real.hasDerivAt_exp x)).congr_deriv (by push_cast; ring)
    exact (((hasDerivAt_id x).const_add 1).add (h1.div_const 2)).sub (Real.hasDerivAt_exp x)
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (fun x _ => (hd x).continuousAt.continuousWithinAt)
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x _
      rw [(hd x).deriv]
      have h1 := Real.one_sub_le_exp_neg x
      have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
      have he := Real.exp_pos x
      have : Real.exp x - x * Real.exp x ≤ 1 := by nlinarith
      nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) he.le]
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hu) hu
  simp only [f] at this
  simp at this
  linarith

/-- the row product -/
def faG (v : Fin N → ℝ) : ℝ := ∏ j, clamp01 (v j)

lemma faG_nonneg (v : Fin N → ℝ) : 0 ≤ faG v := prod_nonneg fun _ _ => clamp01_nonneg _

lemma faG_le_one (v : Fin N → ℝ) : faG v ≤ 1 :=
  prod_le_one (fun _ _ => clamp01_nonneg _) fun _ _ => clamp01_le_one _

lemma faG_meas : Measurable (faG (N := N)) := measurable_rowPw

lemma faG_int (p : ℕ) : Integrable (fun v : Fin N → ℝ => faG v ^ p) (rowM N) :=
  Integrable.of_bound (faG_meas.pow_const p).aestronglyMeasurable 1 (ae_of_all _ fun v => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (faG_nonneg v) p)]
    exact pow_le_one₀ (faG_nonneg v) (faG_le_one v))

lemma faG_mom (p : ℕ) : ∫ v, faG v ^ p ∂rowM N = (1 / ((p : ℝ) + 1)) ^ N := integral_rowP_pow' p

lemma fa_int_lin (a b c : ℝ) :
    ∫ v, (a + b * faG v + c * faG v ^ 2) ∂rowM N = a + b * (1 / 2) ^ N + c * (1 / 3) ^ N := by
  have i1 : Integrable (fun v : Fin N → ℝ => faG v) (rowM N) := by simpa using faG_int (N := N) 1
  have i2 := faG_int (N := N) 2
  rw [integral_add (by exact (integrable_const a).add (i1.const_mul b)) (i2.const_mul c),
    integral_add (integrable_const a) (i1.const_mul b), integral_const, integral_const_mul,
    integral_const_mul]
  have m1 := faG_mom (N := N) 1
  have m2 := faG_mom (N := N) 2
  simp only [pow_one] at m1
  rw [m1, m2]
  simp
  norm_num

/-- one-row factor, lower tail -/
lemma fa_factor_lo {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ v, ENNReal.ofReal (Real.exp (-t * faG v)) ∂rowM N ≤
      ENNReal.ofReal (Real.exp (-t * (1 / 2) ^ N + t ^ 2 / 2 * (1 / 3) ^ N)) := by
  have hnn : ∀ v : Fin N → ℝ, 0 ≤ 1 + (-t) * faG v + t ^ 2 / 2 * faG v ^ 2 := fun v => by
    nlinarith [sq_nonneg (t * faG v - 1)]
  calc ∫⁻ v, ENNReal.ofReal (Real.exp (-t * faG v)) ∂rowM N
      ≤ ∫⁻ v, ENNReal.ofReal (1 + (-t) * faG v + t ^ 2 / 2 * faG v ^ 2) ∂rowM N := by
        refine lintegral_mono fun v => ENNReal.ofReal_le_ofReal ?_
        have := fa_exp_neg_le (t * faG v) (mul_nonneg ht (faG_nonneg v))
        rw [show -t * faG v = -(t * faG v) by ring]
        nlinarith
    _ = ENNReal.ofReal (∫ v, (1 + (-t) * faG v + t ^ 2 / 2 * faG v ^ 2) ∂rowM N) := by
        rw [ofReal_integral_eq_lintegral_ofReal]
        · have i1 : Integrable (fun v : Fin N → ℝ => faG v) (rowM N) := by simpa using faG_int (N := N) 1
          exact ((integrable_const 1).add (i1.const_mul _)).add ((faG_int 2).const_mul _)
        · exact ae_of_all _ hnn
    _ ≤ _ := by
        rw [fa_int_lin]
        apply ENNReal.ofReal_le_ofReal
        have := Real.add_one_le_exp (-t * (1 / 2) ^ N + t ^ 2 / 2 * (1 / 3) ^ N)
        linarith

/-- one-row factor, upper tail -/
lemma fa_factor_hi {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ v, ENNReal.ofReal (Real.exp (-t * -faG v)) ∂rowM N ≤
      ENNReal.ofReal (Real.exp (t * (1 / 2) ^ N + t ^ 2 * Real.exp t / 2 * (1 / 3) ^ N)) := by
  have hnn : ∀ v : Fin N → ℝ, 0 ≤ 1 + t * faG v + t ^ 2 * Real.exp t / 2 * faG v ^ 2 := fun v => by
    have := faG_nonneg v; have := Real.exp_pos t; positivity
  calc ∫⁻ v, ENNReal.ofReal (Real.exp (-t * -faG v)) ∂rowM N
      ≤ ∫⁻ v, ENNReal.ofReal (1 + t * faG v + t ^ 2 * Real.exp t / 2 * faG v ^ 2) ∂rowM N := by
        refine lintegral_mono fun v => ENNReal.ofReal_le_ofReal ?_
        have hu := mul_nonneg ht (faG_nonneg v)
        have h := fa_exp_le_quad (t * faG v) hu
        have h1 : Real.exp (t * faG v) ≤ Real.exp t := by
          apply Real.exp_le_exp.2
          nlinarith [faG_le_one v]
        rw [show -t * -faG v = t * faG v by ring]
        have : (t * faG v) ^ 2 * Real.exp (t * faG v) ≤ t ^ 2 * Real.exp t * faG v ^ 2 := by
          calc (t * faG v) ^ 2 * Real.exp (t * faG v) ≤ (t * faG v) ^ 2 * Real.exp t :=
                mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
            _ = _ := by ring
        nlinarith
    _ = ENNReal.ofReal (∫ v, (1 + t * faG v + t ^ 2 * Real.exp t / 2 * faG v ^ 2) ∂rowM N) := by
        rw [ofReal_integral_eq_lintegral_ofReal]
        · have i1 : Integrable (fun v : Fin N → ℝ => faG v) (rowM N) := by simpa using faG_int (N := N) 1
          exact ((integrable_const 1).add (i1.const_mul _)).add ((faG_int 2).const_mul _)
        · exact ae_of_all _ hnn
    _ ≤ _ := by
        rw [fa_int_lin]
        apply ENNReal.ofReal_le_ofReal
        have := Real.add_one_le_exp (t * (1 / 2) ^ N + t ^ 2 * Real.exp t / 2 * (1 / 3) ^ N)
        linarith

lemma fa_prod_const (a : ℝ) :
    ∏ _r : State N, ENNReal.ofReal (Real.exp a) = ENNReal.ofReal (Real.exp (2 ^ N * a)) := by
  rw [prod_const, card_univ, show Fintype.card (State N) = 2 ^ N by simp,
    ← ENNReal.ofReal_pow (Real.exp_pos a).le, ← Real.exp_nat_mul]
  norm_num

lemma fa_two_pow_mul (t : ℝ) : (2 : ℝ) ^ N * (t * (1 / 2) ^ N) = t := by
  rw [mul_left_comm, ← mul_pow]; norm_num

lemma fa_two_pow_mul3 (t : ℝ) : (2 : ℝ) ^ N * (t * (1 / 3) ^ N) = t * (2 / 3) ^ N := by
  rw [mul_left_comm, ← mul_pow]; norm_num

theorem cubeM_Zs_le_half {t : ℝ} (ht : 0 ≤ t) :
    cubeM N {w | Zs w ≤ 1 / 2} ≤
      ENNReal.ofReal (Real.exp (-(t / 2) + t ^ 2 / 2 * (2 / 3) ^ N)) := by
  have h := chernoff_pi (fun _ : State N => rowM N) (fun _ v => faG v) (fun _ => faG_meas)
    (a := 1 / 2) ht
  have e : cubeM N {w | Zs w ≤ 1 / 2} =
      Measure.pi (fun _ : State N => rowM N) {x | ∑ i, (fun _ v => faG v) i (x i) ≤ 1 / 2} := rfl
  rw [e]
  refine h.trans ?_
  calc ENNReal.ofReal (Real.exp (t * (1 / 2))) *
        ∏ i : State N, ∫⁻ v, ENNReal.ofReal (Real.exp (-t * faG v)) ∂rowM N
      ≤ ENNReal.ofReal (Real.exp (t * (1 / 2))) *
        ∏ _i : State N, ENNReal.ofReal (Real.exp (-t * (1 / 2) ^ N + t ^ 2 / 2 * (1 / 3) ^ N)) := by
        gcongr with i
        exact fa_factor_lo ht
    _ = _ := by
        rw [fa_prod_const, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        have h1 := fa_two_pow_mul (N := N) t
        have h2 := fa_two_pow_mul3 (N := N) (t ^ 2 / 2)
        have : (2 : ℝ) ^ N * (-t * (1 / 2) ^ N + t ^ 2 / 2 * (1 / 3) ^ N) =
            -((2 : ℝ) ^ N * (t * (1 / 2) ^ N)) + (2 : ℝ) ^ N * (t ^ 2 / 2 * (1 / 3) ^ N) := by ring
        rw [this, h1, h2]; ring

theorem cubeM_Zs_ge_13 {t : ℝ} (ht : 0 ≤ t) :
    cubeM N {w | 13 ≤ Zs w} ≤
      ENNReal.ofReal (Real.exp (-(12 * t) + t ^ 2 * Real.exp t / 2 * (2 / 3) ^ N)) := by
  have h := chernoff_pi (fun _ : State N => rowM N) (fun _ v => -faG v) (fun _ => faG_meas.neg)
    (a := -13) ht
  have e : cubeM N {w | 13 ≤ Zs w} =
      Measure.pi (fun _ : State N => rowM N) {x | ∑ i, (fun _ v => -faG v) i (x i) ≤ -13} := by
    congr 1
    ext w
    simp only [Set.mem_setOf_eq, sum_neg_distrib, neg_le_neg_iff]
    rfl
  rw [e]
  refine h.trans ?_
  calc ENNReal.ofReal (Real.exp (t * -13)) *
        ∏ i : State N, ∫⁻ v, ENNReal.ofReal (Real.exp (-t * -faG v)) ∂rowM N
      ≤ ENNReal.ofReal (Real.exp (t * -13)) *
        ∏ _i : State N, ENNReal.ofReal
          (Real.exp (t * (1 / 2) ^ N + t ^ 2 * Real.exp t / 2 * (1 / 3) ^ N)) := by
        gcongr with i
        exact fa_factor_hi ht
    _ = _ := by
        rw [fa_prod_const, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        have h1 := fa_two_pow_mul (N := N) t
        have h2 := fa_two_pow_mul3 (N := N) (t ^ 2 * Real.exp t / 2)
        have : (2 : ℝ) ^ N * (t * (1 / 2) ^ N + t ^ 2 * Real.exp t / 2 * (1 / 3) ^ N) =
            (2 : ℝ) ^ N * (t * (1 / 2) ^ N) + (2 : ℝ) ^ N * (t ^ 2 * Real.exp t / 2 * (1 / 3) ^ N) := by
          ring
        rw [this, h1, h2]; ring

lemma fa_small_lo : ∀ᶠ N : ℕ in atTop, (3 * (N : ℝ)) ^ 2 / 2 * (2 / 3) ^ N ≤ 1 := by
  have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2
    (r := (2 / 3 : ℝ)) (by rw [abs_of_pos (by norm_num)]; norm_num))
  filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 2 / 9))] with N hN
  have : (3 * (N : ℝ)) ^ 2 / 2 * (2 / 3) ^ N = 9 / 2 * ((N : ℝ) ^ 2 * (2 / 3) ^ N) := by ring
  rw [this]; linarith

lemma fa_small_hi : ∀ᶠ N : ℕ in atTop,
    ((N : ℝ) / 4) ^ 2 * Real.exp ((N : ℝ) / 4) / 2 * (2 / 3) ^ N ≤ 1 := by
  have he : Real.exp (1 / 4) < 3 / 2 := by
    have := Real.exp_bound' (x := 1 / 4) (by norm_num) (by norm_num) (n := 2) (by norm_num)
    have h2 : Real.exp (1 / 4) ≤ 1 + 1 / 4 + (1 / 4) ^ 2 * Real.exp (1 / 4) / 2 :=
      fa_exp_le_quad _ (by norm_num)
    nlinarith
  set r : ℝ := Real.exp (1 / 4) * (2 / 3)
  have hr0 : 0 < r := by positivity
  have hr : |r| < 1 := by rw [abs_of_pos hr0]; simp only [r]; nlinarith
  have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hr
  filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 32))] with N hN
  have e1 : Real.exp ((N : ℝ) / 4) * (2 / 3) ^ N = r ^ N := by
    simp only [r]
    rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
  have : ((N : ℝ) / 4) ^ 2 * Real.exp ((N : ℝ) / 4) / 2 * (2 / 3) ^ N =
      ((N : ℝ) ^ 2 * (Real.exp ((N : ℝ) / 4) * (2 / 3) ^ N)) / 32 := by ring
  rw [this, e1]
  rw [div_le_one (by norm_num)]; linarith

/-- **Leaf `bZs`, unconditional form.** -/
theorem cubeM_Zs_out_le : ∀ᶠ N : ℕ in atTop,
    cubeM N {w | ¬ (1 / 2 ≤ Zs w ∧ Zs w ≤ 13)} ≤
      ENNReal.ofReal (Real.exp (-((10105 / 10000 : ℝ) * N))) := by
  have hlim : Tendsto (fun N : ℕ => 2 * Real.exp (1 - 48 / 100 * (N : ℝ))) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => (1 : ℝ) - 48 / 100 * N) atTop atBot := by
      have h := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num : (0 : ℝ) < 48 / 100)
      exact tendsto_atBot_add_const_left _ 1 (tendsto_neg_atTop_atBot.comp h) |>.congr
        (fun N => by simp; ring)
    simpa using (Real.tendsto_exp_atBot.comp this).const_mul 2
  filter_upwards [fa_small_lo, fa_small_hi,
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N h1 h2 h3
  have hsub : {w : Param N | ¬ (1 / 2 ≤ Zs w ∧ Zs w ≤ 13)} ⊆ {w | Zs w ≤ 1 / 2} ∪ {w | 13 ≤ Zs w} := by
    intro w hw
    simp only [Set.mem_setOf_eq, not_and_or, not_le] at hw
    rcases hw with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have b1 := cubeM_Zs_le_half (N := N) (t := 3 * N) (by positivity)
  have b2 := cubeM_Zs_ge_13 (N := N) (t := N / 4) (by positivity)
  calc cubeM N {w | ¬ (1 / 2 ≤ Zs w ∧ Zs w ≤ 13)}
      ≤ cubeM N {w | Zs w ≤ 1 / 2} + cubeM N {w | 13 ≤ Zs w} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (Real.exp (1 - 3 * N / 2)) + ENNReal.ofReal (Real.exp (1 - 3 * N / 2)) := by
        gcongr
        · refine b1.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
          linarith
        · refine b2.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
          linarith
    _ = ENNReal.ofReal (2 * Real.exp (1 - 3 * N / 2)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]; ring_nf
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have e : Real.exp (1 - 3 * N / 2) = Real.exp (1 - 48 / 100 * (N : ℝ)) *
            Real.exp (-((10105 / 10000 : ℝ) * N)) * Real.exp (-(95 / 10000 * (N : ℝ))) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        rw [e]
        have hx := Real.exp_pos (-((10105 / 10000 : ℝ) * N))
        have hy : Real.exp (-(95 / 10000 * (N : ℝ))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        have hz := Real.exp_pos (1 - 48 / 100 * (N : ℝ))
        have hy0 := Real.exp_pos (-(95 / 10000 * (N : ℝ)))
        nlinarith [mul_le_mul_of_nonneg_left hy (mul_nonneg hz.le hx.le)]

end

end Census
end IIT
