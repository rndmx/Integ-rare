/-
Census, B1 LTBetaHi, case `s ∈ Sp \ {tc}`: **Case A at threshold `N/20`** (variant of `B1LTHiCaseA`; multipliers `(5, 5, 2)`).

For two distinct rows `r0` (the future `tc`) and `s`, with per-unit values `a_j = y_{r0,j}`, `b_j = y_{s,j}`:
the event "`P(r0) ≥ e^{-x_t N}`, `P(s) ≥ e^{-x₁ N}`, every `a_j ≥ 49/100`, and fewer than `N/100` units with
`a_j ≥ 17/20 ∧ b_j ≥ 7/8`" (fewer than `N/20`) has probability `≤ e^{(5 x_t + 5 x₁ + 2/20) N} K^N`, where
`K = E[1{a ≥ 49/100} a⁵ b⁵ e^{-2·1{a ≥ 17/20, b ≥ 7/8}}]`.
-/
import IIT.Census.B1LTHiCaseA

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- The per-unit Chernoff factor. -/
noncomputable def c2F (a b : ℝ) : ℝ :=
  (if 49 / 100 ≤ clamp01 a then clamp01 a ^ 5 else 0) * clamp01 b ^ 5 *
    (if 17 / 20 ≤ clamp01 a ∧ 7 / 8 ≤ clamp01 b then Real.exp (-2) else 1)

lemma c2F_nonneg (a b : ℝ) : 0 ≤ c2F a b := by
  unfold c2F
  have := clamp01_nonneg a; have := clamp01_nonneg b
  split_ifs <;> positivity

lemma c2F_le_one (a b : ℝ) : c2F a b ≤ 1 := by
  unfold c2F
  have ha0 := clamp01_nonneg a; have ha1 := clamp01_le_one a
  have hb0 := clamp01_nonneg b; have hb1 := clamp01_le_one b
  have h5 : clamp01 a ^ 5 ≤ 1 := pow_le_one₀ ha0 ha1
  have h6 : clamp01 b ^ 5 ≤ 1 := pow_le_one₀ hb0 hb1
  have h6' : 0 ≤ clamp01 b ^ 5 := by positivity
  have he : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have he' : 0 ≤ Real.exp (-2) := (Real.exp_pos _).le
  split_ifs <;> refine mul_le_one₀ (mul_le_one₀ ?_ h6' h6) (by positivity) ?_ <;>
    first | exact h5 | exact he | norm_num

lemma c2F_meas : Measurable fun p : ℝ × ℝ => c2F p.1 p.2 := by
  have hc : Measurable clamp01 := by
    unfold clamp01; exact measurable_const.max (measurable_const.min measurable_id)
  unfold c2F
  refine Measurable.mul (Measurable.mul ?_ ((hc.comp measurable_snd).pow_const 5)) ?_
  · exact Measurable.ite (measurableSet_le measurable_const (hc.comp measurable_fst))
      ((hc.comp measurable_fst).pow_const 5) measurable_const
  · exact Measurable.ite ((measurableSet_le measurable_const (hc.comp measurable_fst)).inter
      (measurableSet_le measurable_const (hc.comp measurable_snd))) measurable_const measurable_const

/-! ### The per-unit integral -/

noncomputable def c2F1 (a : ℝ) : ℝ := if 49 / 100 ≤ clamp01 a then clamp01 a ^ 5 else 0
noncomputable def c2F2 (a : ℝ) : ℝ := if 17 / 20 ≤ clamp01 a then clamp01 a ^ 5 else 0
noncomputable def c2H2 (b : ℝ) : ℝ := if 7 / 8 ≤ clamp01 b then clamp01 b ^ 5 else 0

lemma c2F_split (a b : ℝ) :
    c2F a b = c2F1 a * clamp01 b ^ 5 - (1 - Real.exp (-2)) * (c2F2 a * c2H2 b) := by
  unfold c2F c2F1 c2F2 c2H2
  by_cases ha : 17 / 20 ≤ clamp01 a
  · have ha' : 49 / 100 ≤ clamp01 a := le_trans (by norm_num) ha
    by_cases hb : 7 / 8 ≤ clamp01 b
    · rw [if_pos ha', if_pos ⟨ha, hb⟩, if_pos ha, if_pos hb]; ring
    · rw [if_pos ha', if_neg (fun h => hb h.2), if_pos ha, if_neg hb]; ring
  · rw [if_neg (show ¬(17 / 20 ≤ clamp01 a ∧ 7 / 8 ≤ clamp01 b) from fun h => ha h.1), if_neg ha]; ring

lemma c2_hc : Measurable clamp01 := by
  unfold clamp01; exact measurable_const.max (measurable_const.min measurable_id)

/-- `∫ 1{c ≤ y} y^k ∂unif = (1 - c^{k+1})/(k+1)` for `c ∈ [0,1]`. -/
lemma c2_int_tail (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (k : ℕ) :
    ∫ y, (if c ≤ clamp01 y then clamp01 y ^ k else 0) ∂unif = (1 - c ^ (k + 1)) / (k + 1) := by
  have hae : (fun y => if c ≤ clamp01 y then clamp01 y ^ k else 0) =ᵐ[unif]
      fun y => (Set.Icc c 1).indicator (fun y => y ^ k) y := by
    filter_upwards [unif_ae] with y hy
    rw [clamp01_of_mem hy]
    by_cases h : c ≤ y
    · rw [if_pos h, Set.indicator_of_mem (show y ∈ Set.Icc c 1 from ⟨h, hy.2⟩)]
    · rw [if_neg h, Set.indicator_of_notMem (fun hm => h hm.1)]
  rw [integral_congr_ae hae, integral_indicator measurableSet_Icc]
  unfold unif
  rw [Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_left.2 (Set.Icc_subset_Icc hc0 le_rfl), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hc1, integral_pow, one_pow]

lemma c2_int_pow (k : ℕ) : ∫ y, clamp01 y ^ k ∂unif = 1 / (k + 1) := by
  have := c2_int_tail 0 le_rfl zero_le_one k
  have hae : (fun y => if (0 : ℝ) ≤ clamp01 y then clamp01 y ^ k else 0) = fun y => clamp01 y ^ k := by
    funext y; rw [if_pos (clamp01_nonneg y)]
  rw [hae] at this; rw [this, zero_pow (Nat.succ_ne_zero k)]; ring

/-- The per-unit constant. -/
noncomputable def c2K : ℝ :=
  (1 - (49 / 100 : ℝ) ^ 6) / 6 * (1 / 6) - (1 - Real.exp (-2)) * ((1 - (17 / 20 : ℝ) ^ 6) / 6 * ((1 - (7 / 8 : ℝ) ^ 6) / 6))

lemma c2_bdd {f : ℝ → ℝ} (hf : Measurable f) (h : ∀ y, |f y| ≤ 1) : Integrable f unif :=
  Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact h y)

/-- **The per-unit integral equals `c2K`.** -/
theorem c2_int_unit : ∫ p, c2F p.1 p.2 ∂(unif.prod unif) = c2K := by
  have hc := c2_hc
  have m1 : Measurable c2F1 := Measurable.ite (measurableSet_le measurable_const hc) (hc.pow_const 5) measurable_const
  have m2 : Measurable c2F2 := Measurable.ite (measurableSet_le measurable_const hc) (hc.pow_const 5) measurable_const
  have mh2 : Measurable c2H2 := Measurable.ite (measurableSet_le measurable_const hc) (hc.pow_const 5) measurable_const
  have b01 : ∀ y, 0 ≤ clamp01 y ∧ clamp01 y ≤ 1 := fun y => ⟨clamp01_nonneg y, clamp01_le_one y⟩
  have bnd : ∀ (k : ℕ) (c : ℝ) y, |(if c ≤ clamp01 y then clamp01 y ^ k else 0)| ≤ 1 := by
    intro k c y; split_ifs
    · rw [abs_of_nonneg (pow_nonneg (b01 y).1 k)]; exact pow_le_one₀ (b01 y).1 (b01 y).2
    · simp
  have i1 : Integrable c2F1 unif := c2_bdd m1 (bnd 5 _)
  have i2 : Integrable c2F2 unif := c2_bdd m2 (bnd 5 _)
  have ih2 : Integrable c2H2 unif := c2_bdd mh2 (bnd 5 _)
  have ip : Integrable (fun y => clamp01 y ^ 5) unif := c2_bdd (hc.pow_const 5) fun y => by
    rw [abs_of_nonneg (pow_nonneg (b01 y).1 5)]; exact pow_le_one₀ (b01 y).1 (b01 y).2
  have e : (fun p : ℝ × ℝ => c2F p.1 p.2) = fun p => c2F1 p.1 * clamp01 p.2 ^ 5 -
      (1 - Real.exp (-2)) * (c2F2 p.1 * c2H2 p.2) := funext fun p => c2F_split p.1 p.2
  rw [e, integral_sub (i1.mul_prod ip) ((i2.mul_prod ih2).const_mul _), integral_const_mul,
    integral_prod_mul (f := c2F1) (g := fun y => clamp01 y ^ 5), integral_prod_mul]
  have a1 : ∫ y, c2F1 y ∂unif = (1 - (49 / 100 : ℝ) ^ 6) / 6 := by
    have := c2_int_tail (49 / 100) (by norm_num) (by norm_num) 5; unfold c2F1; rw [this]; norm_num
  have a2 : ∫ y, c2F2 y ∂unif = (1 - (17 / 20 : ℝ) ^ 6) / 6 := by
    have := c2_int_tail (17 / 20) (by norm_num) (by norm_num) 5; unfold c2F2; rw [this]; norm_num
  have a3 : ∫ y, c2H2 y ∂unif = (1 - (7 / 8 : ℝ) ^ 6) / 6 := by
    have := c2_int_tail (7 / 8) (by norm_num) (by norm_num) 5; unfold c2H2; rw [this]; norm_num
  have a4 : ∫ y, clamp01 y ^ 5 ∂unif = 1 / 6 := by rw [c2_int_pow 5]; norm_num
  rw [a1, a2, a3, a4]; rfl

/-! ### The two-row product -/

/-- The pair map of two rows. -/
def c2Pair (r0 s : State N) (w : Param N) : Fin N → ℝ × ℝ := fun j => (w r0 j, w s j)

lemma c2_mp_pair {r0 s : State N} (h : r0 ≠ s) :
    MeasurePreserving (c2Pair r0 s) (cubeM N) (Measure.pi fun _ : Fin N => unif.prod unif) := by
  have : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  have : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  have hmp : ∀ r, MeasurePreserving (fun w : Param N => w r) (cubeM N) (rowM N) := fun r =>
    measurePreserving_eval (fun _ : State N => rowM N) r
  have hind : IndepFun (fun w : Param N => w r0) (fun w => w s) (cubeM N) :=
    (iIndepFun_rows (fun _ v => v) fun _ => measurable_id).indepFun h
  have hprod : MeasurePreserving (fun w : Param N => (w r0, w s)) (cubeM N) ((rowM N).prod (rowM N)) := by
    refine ⟨(measurable_pi_apply r0).prodMk (measurable_pi_apply s), ?_⟩
    rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply r0).aemeasurable
      (measurable_pi_apply s).aemeasurable).1 hind, (hmp r0).map_eq, (hmp s).map_eq]
  have heq := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin N) (fun _ => unif) (fun _ => unif)).symm
  have e : c2Pair r0 s = (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin N)).symm ∘
      fun w : Param N => (w r0, w s) := by
    funext w j; rfl
  rw [e]
  exact heq.comp hprod

/-- `∫ ∏_j c2F(y_{r0,j}, y_{s,j}) = c2K^N`. -/
theorem c2_int_prod {r0 s : State N} (h : r0 ≠ s) :
    ∫ w, ∏ j, c2F (w r0 j) (w s j) ∂cubeM N = c2K ^ N := by
  have hm := c2_mp_pair h
  have hg : Measurable fun z : Fin N → ℝ × ℝ => ∏ j, c2F (z j).1 (z j).2 :=
    Finset.measurable_prod _ fun j _ => c2F_meas.comp (measurable_pi_apply j)
  have hi := integral_map (μ := cubeM N) hm.measurable.aemeasurable
    (f := fun z : Fin N → ℝ × ℝ => ∏ j, c2F (z j).1 (z j).2) hg.aestronglyMeasurable
  rw [hm.map_eq] at hi
  rw [show (∫ w, ∏ j, c2F (w r0 j) (w s j) ∂cubeM N) =
      ∫ w, (fun z : Fin N → ℝ × ℝ => ∏ j, c2F (z j).1 (z j).2) (c2Pair r0 s w) ∂cubeM N from rfl, ← hi]
  have h2 := integral_fintype_prod_eq_prod (μ := fun _ : Fin N => unif.prod unif)
    (fun (_ : Fin N) (p : ℝ × ℝ) => c2F p.1 p.2)
  refine h2.trans ?_
  rw [Finset.prod_const, card_univ, Fintype.card_fin, c2_int_unit]

/-! ### Markov -/

/-- The tilt for `tc`. -/
noncomputable def c2Xt : ℝ := lt2x1 - 1 / 800

/-- The Case A event for fixed rows. -/
def c2Ev (r0 s : State N) (w : Param N) : Prop :=
  Real.exp (-(c2Xt * N)) ≤ Pw w r0 ∧ Real.exp (-(lt2x1 * N)) ≤ Pw w s ∧
    (∀ j, 49 / 100 ≤ clamp01 (w r0 j)) ∧
    (((univ.filter fun j : Fin N => 17 / 20 ≤ clamp01 (w r0 j) ∧ 7 / 8 ≤ clamp01 (w s j)).card : ℕ) : ℝ) <
      (N : ℝ) / 20

open Classical in
lemma c2_prod_eq (r0 s : State N) (w : Param N) (hfl : ∀ j, 49 / 100 ≤ clamp01 (w r0 j)) :
    ∏ j, c2F (w r0 j) (w s j) = Pw w r0 ^ 5 * Pw w s ^ 5 *
      Real.exp (-2) ^ (univ.filter fun j : Fin N => 17 / 20 ≤ clamp01 (w r0 j) ∧ 7 / 8 ≤ clamp01 (w s j)).card := by
  unfold c2F Pw
  simp only [if_pos (hfl _)]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow, Finset.prod_ite,
    Finset.prod_const, Finset.prod_const_one, mul_one]

/-- **Case A for fixed rows**: `P(c2Ev) ≤ e^{(5x_t + 6x₁ + 6/100)N} c2K^N`. -/
theorem c2_one {r0 s : State N} (h : r0 ≠ s) :
    cubeM N {w | c2Ev r0 s w} ≤
      ENNReal.ofReal (Real.exp ((5 * c2Xt + 5 * lt2x1 + 2 / 20) * N) * c2K ^ N) := by
  classical
  have : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  set c := (5 * c2Xt + 5 * lt2x1 + 2 / 20) * N
  set F : Param N → ℝ := fun w => Real.exp c * ∏ j, c2F (w r0 j) (w s j)
  have hF0 : ∀ w, 0 ≤ F w := fun w => mul_nonneg (Real.exp_pos _).le
    (Finset.prod_nonneg fun j _ => c2F_nonneg _ _)
  have hj : ∀ j, Measurable fun w : Param N => c2F (w r0 j) (w s j) := fun j => by
    have ha : Measurable fun w : Param N => w r0 j := (measurable_pi_apply j).comp (measurable_pi_apply r0)
    have hb : Measurable fun w : Param N => w s j := (measurable_pi_apply j).comp (measurable_pi_apply s)
    exact c2F_meas.comp (ha.prodMk hb)
  have hFm : Measurable F := measurable_const.mul (Finset.measurable_prod _ fun j _ => hj j)
  have hFi : Integrable F (cubeM N) := by
    refine Integrable.of_bound hFm.aestronglyMeasurable (Real.exp c) (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 w)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le
      (Finset.prod_le_one (fun j _ => c2F_nonneg _ _) fun j _ => c2F_le_one _ _)
  have hsub : {w | c2Ev r0 s w} ⊆ {w | 1 ≤ F w} := by
    rintro w ⟨h1, h2, hfl, hG⟩
    simp only [Set.mem_setOf_eq, F]
    rw [c2_prod_eq r0 s w hfl]
    set G := (univ.filter fun j : Fin N => 17 / 20 ≤ clamp01 (w r0 j) ∧ 7 / 8 ≤ clamp01 (w s j)).card
    have hp : ∀ (x : ℝ) (n : ℕ), Real.exp x ^ n = Real.exp (n * x) := fun x n => (Real.exp_nat_mul x n).symm
    have e1 : Real.exp (5 * (-(c2Xt * N))) ≤ Pw w r0 ^ 5 := by
      have := pow_le_pow_left₀ (Real.exp_pos _).le h1 5; rw [hp] at this; exact_mod_cast this
    have e2 : Real.exp (5 * (-(lt2x1 * N))) ≤ Pw w s ^ 5 := by
      have := pow_le_pow_left₀ (Real.exp_pos _).le h2 5; rw [hp] at this; exact_mod_cast this
    have e3 : Real.exp (-(2 / 20 * (N : ℝ))) ≤ Real.exp (-2) ^ G := by
      rw [hp]; exact Real.exp_le_exp.2 (by linarith)
    have hprod : Real.exp (-c) ≤ Pw w r0 ^ 5 * Pw w s ^ 5 * Real.exp (-2) ^ G := by
      have : Real.exp (-c) = Real.exp (5 * (-(c2Xt * N))) * Real.exp (5 * (-(lt2x1 * N))) *
          Real.exp (-(2 / 20 * (N : ℝ))) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; simp only [c]; ring
      rw [this]
      exact mul_le_mul (mul_le_mul e1 e2 (Real.exp_pos _).le (pow_nonneg (le_trans (Real.exp_pos _).le h1) 5)) e3
        (Real.exp_pos _).le (mul_nonneg (pow_nonneg (le_trans (Real.exp_pos _).le h1) 5)
          (pow_nonneg (le_trans (Real.exp_pos _).le h2) 5))
    calc (1 : ℝ) = Real.exp c * Real.exp (-c) := by rw [← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
  have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hF0) hFi 1
  rw [one_mul] at hmk
  have hint : ∫ w, F w ∂cubeM N = Real.exp c * c2K ^ N := by
    simp only [F]; rw [integral_const_mul, c2_int_prod h]
  rw [hint] at hmk
  calc cubeM N {w | c2Ev r0 s w} ≤ cubeM N {w | 1 ≤ F w} := measure_mono hsub
    _ = ENNReal.ofReal ((cubeM N).real {w | 1 ≤ F w}) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hmk

/-! ### Numerics and the union over `tc` -/

lemma c2_exp2 : Real.exp (-2) ≤ 1354 / 10000 := by
  have he := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have : (10000 / 1354 : ℝ) ≤ Real.exp 2 := by
    rw [h2]
    calc (10000 / 1354 : ℝ) ≤ 2.7182818283 ^ 2 := by norm_num
      _ ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) he.le 2
  rw [Real.exp_neg, inv_eq_one_div]
  calc 1 / Real.exp 2 ≤ 1 / (10000 / 1354) := one_div_le_one_div_of_le (by norm_num) this
    _ = 1354 / 10000 := by norm_num

lemma c2K_le : c2K ≤ 193 / 10000 := by
  unfold c2K
  have := c2_exp2
  nlinarith [Real.exp_pos (-2)]

lemma c2_log : Real.log ((193 / 10000 : ℚ) : ℝ) ≤ ((-3947 / 1000 : ℚ) : ℝ) :=
  log_le_rat (by norm_num) 12 8 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

/-- **Case A at `N/20` for fixed rows, rate `≥ 1.1 + log 2`.** -/
theorem c2_one_rate {r0 s : State N} (h : r0 ≠ s) :
    cubeM N {w | c2Ev r0 s w} ≤ ENNReal.ofReal (Real.exp (-((11 / 10 + Real.log 2) * N))) := by
  refine (c2_one h).trans (ENNReal.ofReal_le_ofReal ?_)
  have hK0 : 0 ≤ c2K := by
    have := c2_int_unit
    rw [← this]; exact integral_nonneg fun p => c2F_nonneg _ _
  have hK : c2K ≤ Real.exp (-3947 / 1000) := by
    refine c2K_le.trans ?_
    have hl := c2_log; push_cast at hl
    have := Real.exp_le_exp.2 hl
    rwa [Real.exp_log (by norm_num)] at this
  have hKN : c2K ^ N ≤ Real.exp (-3947 / 1000 * N) := by
    rw [mul_comm, Real.exp_nat_mul]; exact pow_le_pow_left₀ hK0 hK N
  obtain ⟨-, hx2⟩ := lt2x1_bounds
  have hl2 := Real.log_two_lt_d9
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc Real.exp ((5 * c2Xt + 5 * lt2x1 + 2 / 20) * N) * c2K ^ N
      ≤ Real.exp ((5 * c2Xt + 5 * lt2x1 + 2 / 20) * N) * Real.exp (-3947 / 1000 * N) :=
        mul_le_mul_of_nonneg_left hKN (Real.exp_pos _).le
    _ = Real.exp ((5 * c2Xt + 5 * lt2x1 + 2 / 20 - 3947 / 1000) * N) := by rw [← Real.exp_add]; ring_nf
    _ ≤ _ := Real.exp_le_exp.2 (by unfold c2Xt; nlinarith)

/-- **Case A** (union over `tc`): some row `r0 ≠ s` with `c2Ev r0 s` has probability `≤ e^{-1.1N}`. -/
theorem c2_ev (s : State N) :
    cubeM N {w | ∃ r0, r0 ≠ s ∧ c2Ev r0 s w} ≤ ENNReal.ofReal (Real.exp (-((11 / 10 : ℝ) * N))) := by
  have e : {w : Param N | ∃ r0, r0 ≠ s ∧ c2Ev r0 s w} ⊆ ⋃ r0 ∈ (univ : Finset (State N)).erase s,
      {w | c2Ev r0 s w} := by
    rintro w ⟨r0, hr, hc⟩
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨r0, mem_erase.2 ⟨hr, mem_univ _⟩, hc⟩
  refine (measure_mono e).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ r0 ∈ (univ : Finset (State N)).erase s, cubeM N {w | c2Ev r0 s w}
      ≤ ∑ _r0 ∈ (univ : Finset (State N)).erase s, ENNReal.ofReal (Real.exp (-((11 / 10 + Real.log 2) * N))) :=
        Finset.sum_le_sum fun r0 hr => c2_one_rate (mem_erase.1 hr).1
    _ ≤ (2 ^ N : ℕ) * ENNReal.ofReal (Real.exp (-((11 / 10 + Real.log 2) * N))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        have : ((univ : Finset (State N)).erase s).card ≤ 2 ^ N := (card_erase_le).trans (by simp)
        exact_mod_cast this
    _ = _ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show ((2 ^ N : ℕ) : ℝ) = Real.exp (N * Real.log 2) by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]; push_cast; ring, ← Real.exp_add]
        congr 1; ring

end Census
end IIT
