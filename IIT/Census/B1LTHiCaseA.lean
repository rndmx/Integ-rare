/-
Census, B1 LTBetaHi, case `s ∈ Sp \ {tc}`: **Case A** of W11 §3 (few good units for `Top'`).

For two distinct rows `r0` (the future `tc`) and `s`, with per-unit values `a_j = y_{r0,j}`, `b_j = y_{s,j}`:
the event "`P(r0) ≥ e^{-x_t N}`, `P(s) ≥ e^{-x₁ N}`, every `a_j ≥ 49/100`, and fewer than `N/100` units with
`a_j ≥ 17/20 ∧ b_j ≥ 7/8`" has probability `≤ e^{(5 x_t + 6 x₁ + 6/100) N} K^N`, where
`K = E[1{a ≥ 49/100} a⁵ b⁶ e^{-6·1{a ≥ 17/20, b ≥ 7/8}}]` (Chernoff with multipliers `(p, ν, μ) = (5, 6, 6)`).
-/
import IIT.Census.B1LTHiSpRed

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- The per-unit Chernoff factor. -/
noncomputable def caF (a b : ℝ) : ℝ :=
  (if 49 / 100 ≤ clamp01 a then clamp01 a ^ 5 else 0) * clamp01 b ^ 6 *
    (if 17 / 20 ≤ clamp01 a ∧ 7 / 8 ≤ clamp01 b then Real.exp (-6) else 1)

lemma caF_nonneg (a b : ℝ) : 0 ≤ caF a b := by
  unfold caF
  have := clamp01_nonneg a; have := clamp01_nonneg b
  split_ifs <;> positivity

lemma caF_le_one (a b : ℝ) : caF a b ≤ 1 := by
  unfold caF
  have ha0 := clamp01_nonneg a; have ha1 := clamp01_le_one a
  have hb0 := clamp01_nonneg b; have hb1 := clamp01_le_one b
  have h5 : clamp01 a ^ 5 ≤ 1 := pow_le_one₀ ha0 ha1
  have h6 : clamp01 b ^ 6 ≤ 1 := pow_le_one₀ hb0 hb1
  have h6' : 0 ≤ clamp01 b ^ 6 := by positivity
  have he : Real.exp (-6) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have he' : 0 ≤ Real.exp (-6) := (Real.exp_pos _).le
  split_ifs <;> refine mul_le_one₀ (mul_le_one₀ ?_ h6' h6) (by positivity) ?_ <;>
    first | exact h5 | exact he | norm_num

lemma caF_meas : Measurable fun p : ℝ × ℝ => caF p.1 p.2 := by
  have hc : Measurable clamp01 := by
    unfold clamp01; exact measurable_const.max (measurable_const.min measurable_id)
  unfold caF
  refine Measurable.mul (Measurable.mul ?_ ((hc.comp measurable_snd).pow_const 6)) ?_
  · exact Measurable.ite (measurableSet_le measurable_const (hc.comp measurable_fst))
      ((hc.comp measurable_fst).pow_const 5) measurable_const
  · exact Measurable.ite ((measurableSet_le measurable_const (hc.comp measurable_fst)).inter
      (measurableSet_le measurable_const (hc.comp measurable_snd))) measurable_const measurable_const

/-! ### The per-unit integral -/

noncomputable def caF1 (a : ℝ) : ℝ := if 49 / 100 ≤ clamp01 a then clamp01 a ^ 5 else 0
noncomputable def caF2 (a : ℝ) : ℝ := if 17 / 20 ≤ clamp01 a then clamp01 a ^ 5 else 0
noncomputable def caH2 (b : ℝ) : ℝ := if 7 / 8 ≤ clamp01 b then clamp01 b ^ 6 else 0

lemma caF_split (a b : ℝ) :
    caF a b = caF1 a * clamp01 b ^ 6 - (1 - Real.exp (-6)) * (caF2 a * caH2 b) := by
  unfold caF caF1 caF2 caH2
  by_cases ha : 17 / 20 ≤ clamp01 a
  · have ha' : 49 / 100 ≤ clamp01 a := le_trans (by norm_num) ha
    by_cases hb : 7 / 8 ≤ clamp01 b
    · rw [if_pos ha', if_pos ⟨ha, hb⟩, if_pos ha, if_pos hb]; ring
    · rw [if_pos ha', if_neg (fun h => hb h.2), if_pos ha, if_neg hb]; ring
  · rw [if_neg (show ¬(17 / 20 ≤ clamp01 a ∧ 7 / 8 ≤ clamp01 b) from fun h => ha h.1), if_neg ha]; ring

lemma ca_hc : Measurable clamp01 := by
  unfold clamp01; exact measurable_const.max (measurable_const.min measurable_id)

/-- `∫ 1{c ≤ y} y^k ∂unif = (1 - c^{k+1})/(k+1)` for `c ∈ [0,1]`. -/
lemma ca_int_tail (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (k : ℕ) :
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

lemma ca_int_pow (k : ℕ) : ∫ y, clamp01 y ^ k ∂unif = 1 / (k + 1) := by
  have := ca_int_tail 0 le_rfl zero_le_one k
  have hae : (fun y => if (0 : ℝ) ≤ clamp01 y then clamp01 y ^ k else 0) = fun y => clamp01 y ^ k := by
    funext y; rw [if_pos (clamp01_nonneg y)]
  rw [hae] at this; rw [this, zero_pow (Nat.succ_ne_zero k)]; ring

/-- The per-unit constant. -/
noncomputable def caK : ℝ :=
  (1 - (49 / 100 : ℝ) ^ 6) / 6 * (1 / 7) - (1 - Real.exp (-6)) * ((1 - (17 / 20 : ℝ) ^ 6) / 6 * ((1 - (7 / 8 : ℝ) ^ 7) / 7))

lemma ca_bdd {f : ℝ → ℝ} (hf : Measurable f) (h : ∀ y, |f y| ≤ 1) : Integrable f unif :=
  Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact h y)

/-- **The per-unit integral equals `caK`.** -/
theorem ca_int_unit : ∫ p, caF p.1 p.2 ∂(unif.prod unif) = caK := by
  have hc := ca_hc
  have m1 : Measurable caF1 := Measurable.ite (measurableSet_le measurable_const hc) (hc.pow_const 5) measurable_const
  have m2 : Measurable caF2 := Measurable.ite (measurableSet_le measurable_const hc) (hc.pow_const 5) measurable_const
  have mh2 : Measurable caH2 := Measurable.ite (measurableSet_le measurable_const hc) (hc.pow_const 6) measurable_const
  have b01 : ∀ y, 0 ≤ clamp01 y ∧ clamp01 y ≤ 1 := fun y => ⟨clamp01_nonneg y, clamp01_le_one y⟩
  have bnd : ∀ (k : ℕ) (c : ℝ) y, |(if c ≤ clamp01 y then clamp01 y ^ k else 0)| ≤ 1 := by
    intro k c y; split_ifs
    · rw [abs_of_nonneg (pow_nonneg (b01 y).1 k)]; exact pow_le_one₀ (b01 y).1 (b01 y).2
    · simp
  have i1 : Integrable caF1 unif := ca_bdd m1 (bnd 5 _)
  have i2 : Integrable caF2 unif := ca_bdd m2 (bnd 5 _)
  have ih2 : Integrable caH2 unif := ca_bdd mh2 (bnd 6 _)
  have ip : Integrable (fun y => clamp01 y ^ 6) unif := ca_bdd (hc.pow_const 6) fun y => by
    rw [abs_of_nonneg (pow_nonneg (b01 y).1 6)]; exact pow_le_one₀ (b01 y).1 (b01 y).2
  have e : (fun p : ℝ × ℝ => caF p.1 p.2) = fun p => caF1 p.1 * clamp01 p.2 ^ 6 -
      (1 - Real.exp (-6)) * (caF2 p.1 * caH2 p.2) := funext fun p => caF_split p.1 p.2
  rw [e, integral_sub (i1.mul_prod ip) ((i2.mul_prod ih2).const_mul _), integral_const_mul,
    integral_prod_mul (f := caF1) (g := fun y => clamp01 y ^ 6), integral_prod_mul]
  have a1 : ∫ y, caF1 y ∂unif = (1 - (49 / 100 : ℝ) ^ 6) / 6 := by
    have := ca_int_tail (49 / 100) (by norm_num) (by norm_num) 5; unfold caF1; rw [this]; norm_num
  have a2 : ∫ y, caF2 y ∂unif = (1 - (17 / 20 : ℝ) ^ 6) / 6 := by
    have := ca_int_tail (17 / 20) (by norm_num) (by norm_num) 5; unfold caF2; rw [this]; norm_num
  have a3 : ∫ y, caH2 y ∂unif = (1 - (7 / 8 : ℝ) ^ 7) / 7 := by
    have := ca_int_tail (7 / 8) (by norm_num) (by norm_num) 6; unfold caH2; rw [this]; norm_num
  have a4 : ∫ y, clamp01 y ^ 6 ∂unif = 1 / 7 := by rw [ca_int_pow 6]; norm_num
  rw [a1, a2, a3, a4]; rfl

/-! ### The two-row product -/

/-- The pair map of two rows. -/
def caPair (r0 s : State N) (w : Param N) : Fin N → ℝ × ℝ := fun j => (w r0 j, w s j)

lemma ca_mp_pair {r0 s : State N} (h : r0 ≠ s) :
    MeasurePreserving (caPair r0 s) (cubeM N) (Measure.pi fun _ : Fin N => unif.prod unif) := by
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
  have e : caPair r0 s = (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin N)).symm ∘
      fun w : Param N => (w r0, w s) := by
    funext w j; rfl
  rw [e]
  exact heq.comp hprod

/-- `∫ ∏_j caF(y_{r0,j}, y_{s,j}) = caK^N`. -/
theorem ca_int_prod {r0 s : State N} (h : r0 ≠ s) :
    ∫ w, ∏ j, caF (w r0 j) (w s j) ∂cubeM N = caK ^ N := by
  have hm := ca_mp_pair h
  have hg : Measurable fun z : Fin N → ℝ × ℝ => ∏ j, caF (z j).1 (z j).2 :=
    Finset.measurable_prod _ fun j _ => caF_meas.comp (measurable_pi_apply j)
  have hi := integral_map (μ := cubeM N) hm.measurable.aemeasurable
    (f := fun z : Fin N → ℝ × ℝ => ∏ j, caF (z j).1 (z j).2) hg.aestronglyMeasurable
  rw [hm.map_eq] at hi
  rw [show (∫ w, ∏ j, caF (w r0 j) (w s j) ∂cubeM N) =
      ∫ w, (fun z : Fin N → ℝ × ℝ => ∏ j, caF (z j).1 (z j).2) (caPair r0 s w) ∂cubeM N from rfl, ← hi]
  have h2 := integral_fintype_prod_eq_prod (μ := fun _ : Fin N => unif.prod unif)
    (fun (_ : Fin N) (p : ℝ × ℝ) => caF p.1 p.2)
  refine h2.trans ?_
  rw [Finset.prod_const, card_univ, Fintype.card_fin, ca_int_unit]

/-! ### Markov -/

/-- The tilt for `tc`. -/
noncomputable def caXt : ℝ := lt2x1 - 1 / 800

/-- The Case A event for fixed rows. -/
def caEv (r0 s : State N) (w : Param N) : Prop :=
  Real.exp (-(caXt * N)) ≤ Pw w r0 ∧ Real.exp (-(lt2x1 * N)) ≤ Pw w s ∧
    (∀ j, 49 / 100 ≤ clamp01 (w r0 j)) ∧
    (((univ.filter fun j : Fin N => 17 / 20 ≤ clamp01 (w r0 j) ∧ 7 / 8 ≤ clamp01 (w s j)).card : ℕ) : ℝ) <
      (N : ℝ) / 100

open Classical in
lemma ca_prod_eq (r0 s : State N) (w : Param N) (hfl : ∀ j, 49 / 100 ≤ clamp01 (w r0 j)) :
    ∏ j, caF (w r0 j) (w s j) = Pw w r0 ^ 5 * Pw w s ^ 6 *
      Real.exp (-6) ^ (univ.filter fun j : Fin N => 17 / 20 ≤ clamp01 (w r0 j) ∧ 7 / 8 ≤ clamp01 (w s j)).card := by
  unfold caF Pw
  simp only [if_pos (hfl _)]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow, Finset.prod_ite,
    Finset.prod_const, Finset.prod_const_one, mul_one]

/-- **Case A for fixed rows**: `P(caEv) ≤ e^{(5x_t + 6x₁ + 6/100)N} caK^N`. -/
theorem ca_one {r0 s : State N} (h : r0 ≠ s) :
    cubeM N {w | caEv r0 s w} ≤
      ENNReal.ofReal (Real.exp ((5 * caXt + 6 * lt2x1 + 6 / 100) * N) * caK ^ N) := by
  classical
  have : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  set c := (5 * caXt + 6 * lt2x1 + 6 / 100) * N
  set F : Param N → ℝ := fun w => Real.exp c * ∏ j, caF (w r0 j) (w s j)
  have hF0 : ∀ w, 0 ≤ F w := fun w => mul_nonneg (Real.exp_pos _).le
    (Finset.prod_nonneg fun j _ => caF_nonneg _ _)
  have hj : ∀ j, Measurable fun w : Param N => caF (w r0 j) (w s j) := fun j => by
    have ha : Measurable fun w : Param N => w r0 j := (measurable_pi_apply j).comp (measurable_pi_apply r0)
    have hb : Measurable fun w : Param N => w s j := (measurable_pi_apply j).comp (measurable_pi_apply s)
    exact caF_meas.comp (ha.prodMk hb)
  have hFm : Measurable F := measurable_const.mul (Finset.measurable_prod _ fun j _ => hj j)
  have hFi : Integrable F (cubeM N) := by
    refine Integrable.of_bound hFm.aestronglyMeasurable (Real.exp c) (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 w)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le
      (Finset.prod_le_one (fun j _ => caF_nonneg _ _) fun j _ => caF_le_one _ _)
  have hsub : {w | caEv r0 s w} ⊆ {w | 1 ≤ F w} := by
    rintro w ⟨h1, h2, hfl, hG⟩
    simp only [Set.mem_setOf_eq, F]
    rw [ca_prod_eq r0 s w hfl]
    set G := (univ.filter fun j : Fin N => 17 / 20 ≤ clamp01 (w r0 j) ∧ 7 / 8 ≤ clamp01 (w s j)).card
    have hp : ∀ (x : ℝ) (n : ℕ), Real.exp x ^ n = Real.exp (n * x) := fun x n => (Real.exp_nat_mul x n).symm
    have e1 : Real.exp (5 * (-(caXt * N))) ≤ Pw w r0 ^ 5 := by
      have := pow_le_pow_left₀ (Real.exp_pos _).le h1 5; rw [hp] at this; exact_mod_cast this
    have e2 : Real.exp (6 * (-(lt2x1 * N))) ≤ Pw w s ^ 6 := by
      have := pow_le_pow_left₀ (Real.exp_pos _).le h2 6; rw [hp] at this; exact_mod_cast this
    have e3 : Real.exp (-(6 / 100 * (N : ℝ))) ≤ Real.exp (-6) ^ G := by
      rw [hp]; exact Real.exp_le_exp.2 (by linarith)
    have hprod : Real.exp (-c) ≤ Pw w r0 ^ 5 * Pw w s ^ 6 * Real.exp (-6) ^ G := by
      have : Real.exp (-c) = Real.exp (5 * (-(caXt * N))) * Real.exp (6 * (-(lt2x1 * N))) *
          Real.exp (-(6 / 100 * (N : ℝ))) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; simp only [c]; ring
      rw [this]
      exact mul_le_mul (mul_le_mul e1 e2 (Real.exp_pos _).le (pow_nonneg (le_trans (Real.exp_pos _).le h1) 5)) e3
        (Real.exp_pos _).le (mul_nonneg (pow_nonneg (le_trans (Real.exp_pos _).le h1) 5)
          (pow_nonneg (le_trans (Real.exp_pos _).le h2) 6))
    calc (1 : ℝ) = Real.exp c * Real.exp (-c) := by rw [← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
  have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hF0) hFi 1
  rw [one_mul] at hmk
  have hint : ∫ w, F w ∂cubeM N = Real.exp c * caK ^ N := by
    simp only [F]; rw [integral_const_mul, ca_int_prod h]
  rw [hint] at hmk
  calc cubeM N {w | caEv r0 s w} ≤ cubeM N {w | 1 ≤ F w} := measure_mono hsub
    _ = ENNReal.ofReal ((cubeM N).real {w | 1 ≤ F w}) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hmk

/-! ### Numerics and the union over `tc` -/

lemma ca_exp6 : Real.exp (-6) ≤ 1 / 400 := by
  have he := Real.exp_one_gt_d9
  have h6 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
  have : (400 : ℝ) ≤ Real.exp 6 := by
    rw [h6]
    calc (400 : ℝ) ≤ 2.7182818283 ^ 6 := by norm_num
      _ ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) he.le 6
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) this

lemma caK_le : caK ≤ 145 / 10000 := by
  unfold caK
  have := ca_exp6
  nlinarith [Real.exp_pos (-6)]

lemma ca_log : Real.log ((145 / 10000 : ℚ) : ℝ) ≤ ((-423 / 100 : ℚ) : ℝ) :=
  log_le_rat (by norm_num) 12 8 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

/-- **Case A for fixed rows, rate `≥ 1.2 + log 2`.** -/
theorem ca_one_rate {r0 s : State N} (h : r0 ≠ s) :
    cubeM N {w | caEv r0 s w} ≤ ENNReal.ofReal (Real.exp (-((12 / 10 + Real.log 2) * N))) := by
  refine (ca_one h).trans (ENNReal.ofReal_le_ofReal ?_)
  have hK0 : 0 ≤ caK := by
    have := ca_int_unit
    rw [← this]; exact integral_nonneg fun p => caF_nonneg _ _
  have hK : caK ≤ Real.exp (-423 / 100) := by
    refine caK_le.trans ?_
    have hl := ca_log; push_cast at hl
    have := Real.exp_le_exp.2 hl
    rwa [Real.exp_log (by norm_num)] at this
  have hKN : caK ^ N ≤ Real.exp (-423 / 100 * N) := by
    rw [mul_comm, Real.exp_nat_mul]; exact pow_le_pow_left₀ hK0 hK N
  obtain ⟨-, hx2⟩ := lt2x1_bounds
  have hl2 := Real.log_two_lt_d9
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc Real.exp ((5 * caXt + 6 * lt2x1 + 6 / 100) * N) * caK ^ N
      ≤ Real.exp ((5 * caXt + 6 * lt2x1 + 6 / 100) * N) * Real.exp (-423 / 100 * N) :=
        mul_le_mul_of_nonneg_left hKN (Real.exp_pos _).le
    _ = Real.exp ((5 * caXt + 6 * lt2x1 + 6 / 100 - 423 / 100) * N) := by rw [← Real.exp_add]; ring_nf
    _ ≤ _ := Real.exp_le_exp.2 (by unfold caXt; nlinarith)

/-- **Case A** (union over `tc`): some row `r0 ≠ s` with `caEv r0 s` has probability `≤ e^{-1.2N}`. -/
theorem ca_ev (s : State N) :
    cubeM N {w | ∃ r0, r0 ≠ s ∧ caEv r0 s w} ≤ ENNReal.ofReal (Real.exp (-((12 / 10 : ℝ) * N))) := by
  have e : {w : Param N | ∃ r0, r0 ≠ s ∧ caEv r0 s w} ⊆ ⋃ r0 ∈ (univ : Finset (State N)).erase s,
      {w | caEv r0 s w} := by
    rintro w ⟨r0, hr, hc⟩
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨r0, mem_erase.2 ⟨hr, mem_univ _⟩, hc⟩
  refine (measure_mono e).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ r0 ∈ (univ : Finset (State N)).erase s, cubeM N {w | caEv r0 s w}
      ≤ ∑ _r0 ∈ (univ : Finset (State N)).erase s, ENNReal.ofReal (Real.exp (-((12 / 10 + Real.log 2) * N))) :=
        Finset.sum_le_sum fun r0 hr => ca_one_rate (mem_erase.1 hr).1
    _ ≤ (2 ^ N : ℕ) * ENNReal.ofReal (Real.exp (-((12 / 10 + Real.log 2) * N))) := by
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
