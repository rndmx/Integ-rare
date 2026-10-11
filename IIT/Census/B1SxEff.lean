/-
Census, B1 forced leaf `SxEffStmt`: on the effect regime, the competitor product `∏_k pTe(s, s^x, k)` stays below
`σ_N / 2` (rate `≥ 1.0112`, certified `1.0315`).

The constraint `Σ_k -log c_k ≤ x0 N + log 2` (`c_k = pTe(s, s^x, k)`, the oriented competitor) enters the effect
Chernoff template as a fifth term with multiplier `1`, i.e. a weight `c` in the competitor integral.  With
`a(u) = (X+u)/(2X)`, `m = min(1, c_m/X)`: `u = 2X a - X ≤ 2X max(a,m) - X`, so
`∫ max(a,m)^λ u du ≤ 2X gX(λ+1) - X gX(λ)` (`integral_maxpow` twice), and the outer integral is
`2 cellIq(λ+1, LU+4) - cellIq(λ, LU+4)`: no new closed form.  Certificate `CertSx` (61 cells, kernel-checked).
-/
import IIT.Census.CertRSXESound
import IIT.Census.CertSx
import IIT.Census.B1SRowR
import IIT.Census.B1NuSx

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-! ### 1. The effect template with a fifth term -/

theorem joint_template_eff_floor_h (ra rb rc : Fin N → State N)
    (hab : ∀ i, ra i ≠ rb i) (hac : ∀ i, ra i ≠ rc i) (hbc : ∀ i, rb i ≠ rc i)
    (ellT ellS : ℝ → ℝ) (g h : ℝ → ℝ → ℝ) (hellT : Measurable ellT) (hellS : Measurable ellS)
    (hg : Measurable fun p : ℝ × ℝ => g p.1 p.2) (hh : Measurable fun p : ℝ × ℝ => h p.1 p.2)
    (W : Set ℝ) (hW : MeasurableSet W)
    (B t lamU lam : ℝ) (ht : 0 ≤ t) (hlamU : 0 ≤ lamU) (hlam : 0 ≤ lam) (a : ℝ) (mu : ℝ) (hmu : 0 ≤ mu)
    (L : ℝ) :
    cubeM N {w | (∀ i, w (ra i) i ∈ W) ∧ ∑ i, ellT (w (rc i) i) ≤ B ∧
        ∑ i, ellS (w (ra i) i) ≤ ∑ i, ellT (w (rc i) i) ∧ ∑ i, g (w (ra i) i) (w (rb i) i) ≤ 0 ∧
        (∀ i, a ≤ w (rc i) i) ∧ ∑ i, h (w (ra i) i) (w (rb i) i) ≤ L} ≤
      ENNReal.ofReal (Real.exp (t * B + L)) *
        ((∫⁻ x in W, ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
            ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g x u - h x u)) ∂unif ∂unif) *
          ∫⁻ y, ENNReal.ofReal (Real.exp ((lamU - t) * ellT y - mu * Set.indicator (Set.Iio a) 1 y))
            ∂unif) ^ N := by
  set f : Fin 5 → Fin N → ℝ × ℝ × ℝ → ℝ :=
    ![fun _ p => ellT p.2.2, fun _ p => ellS p.1 - ellT p.2.2, fun _ p => g p.1 p.2.1,
      fun _ p => Set.indicator (Set.Iio a) 1 p.2.2, fun _ p => h p.1 p.2.1] with hf
  have hfm : ∀ k i, Measurable (f k i) := by
    intro k i
    fin_cases k
    · exact hellT.comp (measurable_snd.comp measurable_snd)
    · exact (hellS.comp measurable_fst).sub (hellT.comp (measurable_snd.comp measurable_snd))
    · exact hg.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    · exact (measurable_one.indicator measurableSet_Iio).comp (measurable_snd.comp measurable_snd)
    · exact hh.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  set aa : Fin 5 → ℝ := ![B, 0, 0, 0, L] with ha
  set tt : Fin 5 → ℝ := ![t, lamU, lam, mu, 1] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 5)), 0 ≤ tt k := by
    intro k _; fin_cases k <;> simp [htt, ht, hlamU, hlam, hmu]
  have hmain := cubeM_chernoff_three ra rb rc hab hac hbc univ f hfm aa tt htt0 (fun _ => W)
    (fun _ => hW)
  refine (measure_mono ?_).trans (hmain.trans_eq ?_)
  · rintro w ⟨hW', hB, hU, hG, hF, hL⟩
    refine ⟨hW', fun k _ => ?_⟩
    fin_cases k
    · simpa [hf, ha] using hB
    · simp only [hf, ha, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [Finset.sum_sub_distrib]; linarith
    · simpa [hf, ha] using hG
    · simp only [hf, ha]
      refine le_of_eq (Finset.sum_eq_zero fun i _ => ?_)
      simp [Set.indicator_of_notMem (show w (rc i) i ∉ Set.Iio a from not_lt.2 (hF i))]
    · show ∑ i, h (w (ra i) i) (w (rb i) i) ≤ L
      exact hL
  · have hsum : ∑ k ∈ (univ : Finset (Fin 5)), tt k * aa k = t * B + L := by
      simp [htt, ha, Fin.sum_univ_five]
    rw [hsum]
    congr 1
    have hexp : ∀ i x u y, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 5)),
        tt k * f k i (x, u, y))) = ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
          ENNReal.ofReal (Real.exp (-lam * g x u - h x u)) *
            ENNReal.ofReal (Real.exp ((lamU - t) * ellT y - mu * Set.indicator (Set.Iio a) 1 y)) := by
      intro i x u y
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
        ← Real.exp_add, ← Real.exp_add]
      congr 2
      simp only [Fin.sum_univ_five, hf, htt, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
        Matrix.head_cons]
      ring
    have hA : Measurable fun x => ENNReal.ofReal (Real.exp (-lamU * ellS x)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hellS.const_mul _))
    have hBm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-lam * g p.1 p.2 - h p.1 p.2)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hg.const_mul _).sub hh))
    have hC : Measurable fun y => ENNReal.ofReal (Real.exp ((lamU - t) * ellT y -
        mu * Set.indicator (Set.Iio a) 1 y)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hellT.const_mul _).sub
        ((measurable_one.indicator measurableSet_Iio).const_mul _)))
    have hIB : Measurable fun x => ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g x u - h x u)) ∂unif :=
      hBm.lintegral_prod_right'
    have hfac : ∀ i : Fin N, ∫⁻ x in W, ∫⁻ u, ∫⁻ y, ENNReal.ofReal (Real.exp
        (-∑ k ∈ (univ : Finset (Fin 5)), tt k * f k i (x, u, y))) ∂unif ∂unif ∂unif =
        (∫⁻ x in W, ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
            ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g x u - h x u)) ∂unif ∂unif) *
          ∫⁻ y, ENNReal.ofReal (Real.exp ((lamU - t) * ellT y - mu * Set.indicator (Set.Iio a) 1 y))
            ∂unif := by
      intro i
      have hAB : Measurable fun x => ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g x u - h x u)) ∂unif := hA.mul hIB
      simp_rw [hexp i]
      rw [← lintegral_mul_const _ hAB]
      refine lintegral_congr fun x => ?_
      have hBx : Measurable fun u => ENNReal.ofReal (Real.exp (-lam * g x u - h x u)) :=
        Measurable.of_uncurry_left (f := fun x u => ENNReal.ofReal (Real.exp (-lam * g x u - h x u))) hBm
      have hABx : Measurable fun u => ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
          ENNReal.ofReal (Real.exp (-lam * g x u - h x u)) := hBx.const_mul _
      simp_rw [lintegral_const_mul _ hC]
      rw [lintegral_mul_const _ hABx, lintegral_const_mul _ hBx]
    rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]

/-! ### 2. The `u`-weighted inner integral -/

/-- The oriented competitor entry. -/
noncomputable def sxCor (y u : ℝ) : ℝ := if 1 / 2 < clamp01 y then clamp01 u else 1 - clamp01 u

/-- The weighted kernel `2X gX(λ+1) - X gX(λ)`. -/
noncomputable def gXw (lam : ℕ) (c X : ℝ) : ℝ := 2 * X * gX (lam + 1) c X - X * gX lam c X

lemma gXw_eq_integral (lam : ℕ) {c X : ℝ} (hX : 0 < X) (hX1 : X ≤ 1) (hc : 0 < c) (hcX : X ≤ 2 * c) :
    gXw lam c X = ∫ u in (0 : ℝ)..1,
      (2 * X * (max ((X + u) / (2 * X)) (min 1 (c / X))) ^ (lam + 1) -
        X * (max ((X + u) / (2 * X)) (min 1 (c / X))) ^ lam) := by
  have hint : ∀ n : ℕ, IntervalIntegrable (fun u => (max ((X + u) / (2 * X)) (min 1 (c / X))) ^ n)
      MeasureTheory.volume 0 1 := fun n => Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_sub ((hint _).const_mul _) ((hint _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_maxpow (lam + 1) hX hX1 hc hcX, integral_maxpow lam hX hX1 hc hcX]
  rfl

lemma gXw_nonneg (lam : ℕ) {c X : ℝ} (hX : 0 < X) (hX1 : X ≤ 1) (hc : 0 < c) (hcX : X ≤ 2 * c) :
    0 ≤ gXw lam c X := by
  rw [gXw_eq_integral lam hX hX1 hc hcX]
  refine intervalIntegral.integral_nonneg zero_le_one fun u hu => ?_
  set M := max ((X + u) / (2 * X)) (min 1 (c / X))
  have hM : 1 / 2 ≤ M := by
    refine le_trans ?_ (le_max_left _ _)
    rw [le_div_iff₀ (by positivity)]; linarith [hu.1]
  have hM0 : 0 ≤ M := by linarith
  have : 2 * X * M ^ (lam + 1) - X * M ^ lam = X * M ^ lam * (2 * M - 1) := by ring
  rw [this]
  exact mul_nonneg (mul_nonneg hX.le (pow_nonneg hM0 _)) (by linarith)

lemma gXw_continuousOn (lam : ℕ) (c : ℝ) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun X => gXw lam c X) (Set.Icc a 1) := by
  unfold gXw
  exact ((continuousOn_const.mul continuousOn_id).mul (gX_continuousOn (lam + 1) c ha)).sub
    (continuousOn_id.mul (gX_continuousOn lam c ha))

/-- **The core weighted inner bound** at a base value `Y ∈ [1/2, 1]` (`u ↦ u` weight). -/
theorem sx_inner_core (lam : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) {Y : ℝ} (hY : 1 / 2 ≤ Y) (hY1 : Y ≤ 1) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c Y u - -Real.log (clamp01 u))) ∂unif ≤
      ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
        gXw lam (c.2 : ℝ) Y) := by
  have hY0 : 0 < Y := by linarith
  have hcY : clamp01 Y = Y := by unfold clamp01; rw [min_eq_right hY1, max_eq_right hY0.le]
  have hc0 : (0 : ℝ) < c.2 := by linarith
  have hYc : Y ≤ 2 * (c.2 : ℝ) := by linarith
  set K := 7 * deltaU N + (slV N + Real.log 2) / N
  set m := min 1 ((c.2 : ℝ) / Y)
  have hl : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
  -- pointwise on `(0, 1]`
  have hpt : ∀ u ∈ Set.Ioc (0 : ℝ) 1, Real.exp (-(lam : ℝ) * gXev N c Y u - -Real.log (clamp01 u)) ≤
      Real.exp ((lam : ℝ) * K) *
        (2 * Y * (max ((Y + u) / (2 * Y)) m) ^ (lam + 1) - Y * (max ((Y + u) / (2 * Y)) m) ^ lam) := by
    intro u hu
    have hcu : clamp01 u = u := by unfold clamp01; rw [min_eq_right hu.2, max_eq_right hu.1.le]
    have hg : Real.exp (-(lam : ℝ) * gXev N c Y u) ≤ Real.exp ((lam : ℝ) * K) *
        (max ((Y + u) / (2 * Y)) m) ^ lam := by
      have hmin : min (Real.log (2 * Y / (Y + u))) (max 0 (Real.log (Y / c.2))) - 7 * deltaU N ≤
          min (Real.log (2 * Y / (Y + u))) (max 0 (Real.log (Y / c.2)) - 7 * deltaU N) := by
        have hδ : 0 ≤ deltaU N := by unfold deltaU; positivity
        rcases le_total (Real.log (2 * Y / (Y + u))) (max 0 (Real.log (Y / c.2))) with h | h
        · rw [min_eq_left h]; exact le_min (by linarith) (by linarith)
        · rw [min_eq_right h]; exact le_min (by linarith) le_rfl
      rw [← mgfX_pointwise lam hY0 hc0 hu.1.le, ← Real.exp_add, Real.exp_le_exp]
      unfold gXev
      rw [hcY, hcu]
      simp only [K]
      nlinarith [mul_le_mul_of_nonneg_left hmin hl]
    set M := max ((Y + u) / (2 * Y)) m
    have hM0 : 0 ≤ M := le_trans (div_nonneg (by linarith [hu.1]) (by positivity)) (le_max_left _ _)
    have huM : u ≤ 2 * Y * M - Y := by
      have : (Y + u) / (2 * Y) ≤ M := le_max_left _ _
      rw [div_le_iff₀ (by positivity)] at this; linarith
    rw [hcu, sub_neg_eq_add, Real.exp_add, Real.exp_log hu.1]
    calc Real.exp (-(lam : ℝ) * gXev N c Y u) * u ≤ Real.exp ((lam : ℝ) * K) * M ^ lam * u :=
          mul_le_mul_of_nonneg_right hg hu.1.le
      _ ≤ Real.exp ((lam : ℝ) * K) * M ^ lam * (2 * Y * M - Y) := by gcongr
      _ = _ := by ring
  have hcont : ContinuousOn (fun u => Real.exp ((lam : ℝ) * K) *
      (2 * Y * (max ((Y + u) / (2 * Y)) m) ^ (lam + 1) - Y * (max ((Y + u) / (2 * Y)) m) ^ lam))
      (Set.Icc 0 1) := (Continuous.continuousOn (by fun_prop))
  have hnn : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Real.exp ((lam : ℝ) * K) *
      (2 * Y * (max ((Y + u) / (2 * Y)) m) ^ (lam + 1) - Y * (max ((Y + u) / (2 * Y)) m) ^ lam) := by
    intro u hu
    set M := max ((Y + u) / (2 * Y)) m
    have hM : 1 / 2 ≤ M := le_trans (by rw [le_div_iff₀ (by positivity)]; linarith [hu.1]) (le_max_left _ _)
    have : 2 * Y * M ^ (lam + 1) - Y * M ^ lam = Y * M ^ lam * (2 * M - 1) := by ring
    rw [this]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg hY0.le (pow_nonneg (by linarith) _))
      (by linarith))
  unfold unif
  rw [setLIntegral_congr (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 1)).symm]
  calc ∫⁻ u in Set.Ioc 0 1, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c Y u - -Real.log (clamp01 u)))
      ≤ ∫⁻ u in Set.Ioc 0 1, ENNReal.ofReal (Real.exp ((lam : ℝ) * K) *
          (2 * Y * (max ((Y + u) / (2 * Y)) m) ^ (lam + 1) - Y * (max ((Y + u) / (2 * Y)) m) ^ lam)) :=
        setLIntegral_mono' measurableSet_Ioc fun u hu => ENNReal.ofReal_le_ofReal (hpt u hu)
    _ = ∫⁻ u in Set.Icc 0 1, ENNReal.ofReal (Real.exp ((lam : ℝ) * K) *
          (2 * Y * (max ((Y + u) / (2 * Y)) m) ^ (lam + 1) - Y * (max ((Y + u) / (2 * Y)) m) ^ lam)) :=
        setLIntegral_congr Ioc_ae_eq_Icc
    _ = ENNReal.ofReal (∫ u in Set.Icc 0 1, Real.exp ((lam : ℝ) * K) *
          (2 * Y * (max ((Y + u) / (2 * Y)) m) ^ (lam + 1) - Y * (max ((Y + u) / (2 * Y)) m) ^ lam)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc]
        exact Filter.eventually_of_mem (ae_restrict_mem measurableSet_Icc) hnn
    _ = _ := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
          intervalIntegral.integral_const_mul, ← gXw_eq_integral lam hY0 hY1 hc0 hYc]

/-- **The weighted inner bound** for a row-`s` entry `y` (both orientations). -/
theorem sx_inner (lam : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) (y : ℝ) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u - -Real.log (sxCor y u))) ∂unif ≤
      ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
        gXw lam (c.2 : ℝ) (max (clamp01 y) (1 - clamp01 y))) := by
  set X := max (clamp01 y) (1 - clamp01 y) with hX
  have hX12 : 1 / 2 ≤ X := by
    have := le_max_left (clamp01 y) (1 - clamp01 y); have := le_max_right (clamp01 y) (1 - clamp01 y)
    rw [hX]; linarith
  have hX1 : X ≤ 1 := max_le (clamp01_le_one y) (by linarith [clamp01_nonneg y])
  have hcX : clamp01 X = X := by unfold clamp01; rw [min_eq_right hX1, max_eq_right (by linarith)]
  have hmain := sx_inner_core (N := N) lam c hcm hX12 hX1
  by_cases ho : 1 / 2 < clamp01 y
  · have : ∀ u, gXevE N c y u = gXev N c X u := fun u => by
      unfold gXevE gXev; rw [if_pos ho, hcX]
    have hc : ∀ u, sxCor y u = clamp01 u := fun u => by unfold sxCor; rw [if_pos ho]
    simp only [this, hc]; exact hmain
  · have hfm : Measurable fun u : ℝ =>
        ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c X u - -Real.log (clamp01 u))) := by
      unfold gXev
      refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.sub ?_ ?_))
      · refine Measurable.const_mul ((Measurable.min ?_ measurable_const).sub_const _) _
        exact Real.measurable_log.comp (measurable_const.div (measurable_const.add clamp01_measurable))
      · exact (Real.measurable_log.comp clamp01_measurable).neg
    have hrefl : ∀ u ∈ Set.Icc (0 : ℝ) 1, Real.exp (-(lam : ℝ) * gXevE N c y u - -Real.log (sxCor y u)) =
        Real.exp (-(lam : ℝ) * gXev N c X (1 - u) - -Real.log (clamp01 (1 - u))) := fun u hu => by
      have hcu : clamp01 u = u := by unfold clamp01; rw [min_eq_right hu.2, max_eq_right hu.1]
      have hcu' : clamp01 (1 - u) = 1 - u := by
        unfold clamp01; rw [min_eq_right (by linarith [hu.1]), max_eq_right (by linarith [hu.2])]
      unfold gXevE gXev sxCor; rw [if_neg ho, hcX, hcu, hcu']
    calc ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u - -Real.log (sxCor y u))) ∂unif
        = ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c X (1 - u) - -Real.log (clamp01 (1 - u))))
            ∂unif := by
          unfold unif
          exact setLIntegral_congr_fun measurableSet_Icc fun u hu => by rw [hrefl u hu]
      _ = ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c X u - -Real.log (clamp01 u))) ∂unif :=
          lintegral_unif_reflect _ hfm
      _ ≤ _ := hmain

/-! ### 3. The weighted row-`s` factor -/

lemma gXw_measurable (lam : ℕ) (c : ℝ) : Measurable fun X => gXw lam c X := by
  unfold gXw
  exact ((measurable_const.mul measurable_id).mul (gX_measurable (lam + 1) c)).sub
    (measurable_id.mul (gX_measurable lam c))

/-- **The weighted row-`s` factor**: `≤ e^{l_u slT/N} e^{λK} · 2 ∫_b^1 X^{l_u} gXw(X) dX`. -/
theorem sx_s_factor (lam : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) {lu : ℝ} (hlu : 0 ≤ lu)
    {b : ℝ} (hb0 : 0 < b) (hb : b ≤ max (1 / 2) (c.1 : ℝ)) (hb1 : b ≤ 1) :
    ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)},
        ENNReal.ofReal (Real.exp (-lu * ellSX N y)) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u - -Real.log (sxCor y u))) ∂unif ∂unif ≤
      ENNReal.ofReal (Real.exp (lu * (slT N / N)) *
        Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
          (2 * ∫ X in b..1, X ^ lu * gXw lam (c.2 : ℝ) X)) := by
  set C := Real.exp (lu * (slT N / N)) * Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N))
  have hC : 0 < C := by positivity
  have hc0 : (0 : ℝ) < c.2 := by linarith
  set G : ℝ → ENNReal := Set.indicator (Set.Ici b) fun X => ENNReal.ofReal (C * (X ^ lu * gXw lam (c.2 : ℝ) X))
  have hGm : Measurable G := by
    refine Measurable.indicator ?_ measurableSet_Ici
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((measurable_id.pow_const lu).mul (gXw_measurable lam _)))
  set Xf : ℝ → ℝ := fun y => max (clamp01 y) (1 - clamp01 y)
  have hW : MeasurableSet {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} :=
    measurableSet_le measurable_const (clamp01_measurable.max (measurable_const.sub clamp01_measurable))
  have hpt : ∀ y ∈ {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} ∩ Set.Icc 0 1,
      ENNReal.ofReal (Real.exp (-lu * ellSX N y)) *
        ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u - -Real.log (sxCor y u))) ∂unif ≤
          G (Xf y) := by
    rintro y ⟨hyW, hy⟩
    have hX0 : 0 < Xf y := by
      have := le_max_left (clamp01 y) (1 - clamp01 y); have := le_max_right (clamp01 y) (1 - clamp01 y)
      simp only [Xf]; linarith
    have hXb : b ≤ Xf y := by
      have h12 : 1 / 2 ≤ Xf y := by
        have := le_max_left (clamp01 y) (1 - clamp01 y); have := le_max_right (clamp01 y) (1 - clamp01 y)
        simp only [Xf]; linarith
      exact hb.trans (max_le h12 hyW)
    simp only [G, Set.indicator_of_mem (show Xf y ∈ Set.Ici b from hXb)]
    have he : Real.exp (-lu * ellSX N y) = Real.exp (lu * (slT N / N)) * Xf y ^ lu := by
      unfold ellSX; rw [Real.rpow_def_of_pos hX0, ← Real.exp_add]; congr 1; simp only [Xf]; ring
    rw [he]
    calc ENNReal.ofReal (Real.exp (lu * (slT N / N)) * Xf y ^ lu) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u - -Real.log (sxCor y u))) ∂unif
        ≤ ENNReal.ofReal (Real.exp (lu * (slT N / N)) * Xf y ^ lu) *
          ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
            gXw lam (c.2 : ℝ) (Xf y)) := by gcongr; exact sx_inner lam c hcm y
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; simp only [C]; ring
  unfold unif
  rw [Measure.restrict_restrict hW]
  have hsplit : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc 0 (1 / 2) ∪ Set.Icc (1 / 2) 1 := by
    intro y hy; by_cases h : y ≤ 1 / 2
    · exact Or.inl ⟨hy.1, h⟩
    · exact Or.inr ⟨(not_le.1 h).le, hy.2⟩
  have hlo : ∀ y ∈ Set.Icc (0 : ℝ) (1 / 2), Xf y = 1 - y := fun y hy => by
    have hcy : clamp01 y = y := by
      unfold clamp01; rw [min_eq_right (show y ≤ 1 by linarith [hy.2]), max_eq_right hy.1]
    simp only [Xf, hcy]; exact max_eq_right (by linarith [hy.2])
  have hhi : ∀ y ∈ Set.Icc (1 / 2 : ℝ) 1, Xf y = y := fun y hy => by
    have hcy : clamp01 y = y := by
      unfold clamp01; rw [min_eq_right hy.2, max_eq_right (show (0:ℝ) ≤ y by linarith [hy.1])]
    simp only [Xf, hcy]; exact max_eq_left (by linarith [hy.1])
  calc ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} ∩ Set.Icc 0 1,
        ENNReal.ofReal (Real.exp (-lu * ellSX N y)) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u - -Real.log (sxCor y u))) ∂unif
      ≤ ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} ∩ Set.Icc 0 1, G (Xf y) :=
        setLIntegral_mono' (hW.inter measurableSet_Icc) hpt
    _ ≤ ∫⁻ y in Set.Icc 0 (1 / 2) ∪ Set.Icc (1 / 2) 1, G (Xf y) :=
        MeasureTheory.lintegral_mono_set (Set.inter_subset_right.trans hsplit)
    _ ≤ (∫⁻ y in Set.Icc 0 (1 / 2), G (Xf y)) + (∫⁻ y in Set.Icc (1 / 2) 1, G (Xf y)) :=
        MeasureTheory.lintegral_union_le _ _ _
    _ = (∫⁻ y in Set.Icc 0 (1 / 2), G (1 - y)) + (∫⁻ y in Set.Icc (1 / 2) 1, G y) := by
        congr 1
        · exact setLIntegral_congr_fun measurableSet_Icc fun y hy => by rw [hlo y hy]
        · exact setLIntegral_congr_fun measurableSet_Icc fun y hy => by rw [hhi y hy]
    _ = 2 * ∫⁻ y in Set.Icc (1 / 2 : ℝ) 1, G y := by rw [setLIntegral_reflect_half G hGm, two_mul]
    _ ≤ 2 * ∫⁻ y in Set.Icc (0 : ℝ) 1, G y := by
        exact mul_le_mul_right (MeasureTheory.lintegral_mono_set
          (Set.Icc_subset_Icc_left (by norm_num : (0 : ℝ) ≤ 1 / 2))) 2
    _ = 2 * ∫⁻ y in Set.Ioc b 1, ENNReal.ofReal (C * (y ^ lu * gXw lam (c.2 : ℝ) y)) := by
        congr 1
        simp only [G]
        rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
        have : Set.Ici b ∩ Set.Icc 0 1 = Set.Icc b 1 := by
          ext y; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
          constructor
          · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
          · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith, h3⟩
        rw [this]; exact setLIntegral_congr Ioc_ae_eq_Icc.symm
    _ = _ := by
        have hint : IntegrableOn (fun y => C * (y ^ lu * gXw lam (c.2 : ℝ) y)) (Set.Ioc b 1) :=
          (((continuousOn_const.mul ((Real.continuous_rpow_const hlu).continuousOn.mul
            (gXw_continuousOn lam _ hb0)))).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
        rw [← ofReal_integral_eq_lintegral_ofReal hint, ← intervalIntegral.integral_of_le hb1,
          intervalIntegral.integral_const_mul, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        · congr 1; ring
        · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy => ?_)
          have hy0 : 0 < y := hb0.trans hy.1
          have := gXw_nonneg lam (c := (c.2 : ℝ)) hy0 hy.2 hc0 (by linarith [hy.2])
          exact mul_nonneg hC.le (mul_nonneg (Real.rpow_nonneg hy0.le _) this)

/-! ### 4. The exact identity -/

lemma cellExpOK_spec {lam P : ℕ} (h : cellExpOK lam P = true) :
    (∀ k ∈ range (lam + 2), (P : ℤ) + 4 * k - 4 * lam + 4 ≠ 0) ∧ (P : ℤ) + 8 ≠ 0 ∧
      (P : ℤ) - 4 * lam + 4 ≠ 0 ∧ (P : ℤ) - 4 * lam + 8 ≠ 0 := by
  simp only [cellExpOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hk, hp⟩, h0⟩, h1⟩ := h
  exact ⟨fun k hkm => hk k (Finset.mem_range.1 hkm), hp, h0, h1⟩

theorem sx_exact (v w : ℚ) (hv : 0 < v) (hvw : v ≤ w) (hw1 : w ≤ 1) (lam LU : ℕ)
    (he1 : cellExpOK (lam + 1) (LU + 4) = true) (he0 : cellExpOK lam (LU + 4) = true) :
    ∫ X in ((v : ℝ) ^ 4)..1, X ^ ((LU : ℝ) / 4) * gXw lam ((w : ℝ) ^ 4) X =
      ((2 * cellIq v w (lam + 1) (LU + 4) - cellIq v w lam (LU + 4) : ℚ) : ℝ) := by
  obtain ⟨hk1, hp1, h01, h11⟩ := cellExpOK_spec he1
  obtain ⟨hk0, hp0, h00, h10⟩ := cellExpOK_spec he0
  have e1 := cellIq_eq v w hv hvw hw1 (lam + 1) (LU + 4) hk1 hp1 h01 h11
  have e0 := cellIq_eq v w hv hvw hw1 lam (LU + 4) hk0 hp0 h00 h10
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hv4 : (0 : ℝ) < (v : ℝ) ^ 4 := by positivity
  have hv41 : (v : ℝ) ^ 4 ≤ 1 := pow_le_one₀ hv'.le (by exact_mod_cast hvw.trans hw1)
  have hq : ((LU + 4 : ℕ) : ℝ) / 4 = (LU : ℝ) / 4 + 1 := by push_cast; ring
  rw [hq] at e1 e0
  have hcongr : Set.EqOn (fun X : ℝ => X ^ ((LU : ℝ) / 4) * gXw lam ((w : ℝ) ^ 4) X)
      (fun X => 2 * (X ^ ((LU : ℝ) / 4 + 1) * gX (lam + 1) ((w : ℝ) ^ 4) X) -
        X ^ ((LU : ℝ) / 4 + 1) * gX lam ((w : ℝ) ^ 4) X) (Set.uIcc ((v : ℝ) ^ 4) 1) := by
    intro X hX
    rw [Set.uIcc_of_le hv41] at hX
    have hX0 : 0 < X := lt_of_lt_of_le hv4 hX.1
    simp only [gXw]
    rw [Real.rpow_add_one hX0.ne']
    ring
  have hint : ∀ l : ℕ, IntervalIntegrable (fun X : ℝ => X ^ ((LU : ℝ) / 4 + 1) * gX l ((w : ℝ) ^ 4) X)
      MeasureTheory.volume ((v : ℝ) ^ 4) 1 := by
    intro l
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hv41]
    exact (ContinuousOn.rpow_const continuousOn_id fun _ _ => Or.inr (by positivity)).mul
      (gX_continuousOn l _ hv4)
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_sub ((hint _).const_mul _) (hint _),
    intervalIntegral.integral_const_mul, ← e1, ← e0]
  push_cast; ring

/-! ### 5. The certified cells -/

/-- **One effect cell with the `s^x` product constraint** (rows `s`, `s^x`, `r0` distinct). -/
theorem cellEvX_sx_prob (hN : 0 < N) (s r0 : State N) (x : Fin N) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2)
    (hδ : deltaU N < 1 / 2) (hsr : s ≠ r0) (hfr : flipAt x s ≠ r0) (t lamU : ℝ) (lam : ℕ) (mu : ℝ)
    (ht : 0 ≤ t) (hlamU : 0 ≤ lamU) (hmu : 0 ≤ mu) {Js Jt : ℝ} (hJs0 : 0 ≤ Js) (hJt0 : 0 ≤ Jt)
    (hJs : ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)},
        ENNReal.ofReal (Real.exp (-lamU * ellSX N y)) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u - -Real.log (sxCor y u))) ∂unif ∂unif ≤
            ENNReal.ofReal Js)
    (hJt : ∫⁻ y, ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y) -
        mu * Set.indicator (Set.Iio (1 / 2 - deltaU N)) 1 y)) ∂unif ≤ ENNReal.ofReal Jt) (L : ℝ) :
    cubeM N {w : Param N | CellEvX N s r0 x .effect c w ∧
        ∑ i, -Real.log (sxCor (w s i) (w (flipAt x s) i)) ≤ L} ≤
      ENNReal.ofReal (Real.exp (t * (x0 * N + slT N) + L) * (Js * Jt) ^ N) := by
  have hellT : Measurable fun y : ℝ => -Real.log (clamp01 y) :=
    (Real.measurable_log.comp clamp01_measurable).neg
  have hellS : Measurable (ellSX N) := by
    unfold ellSX
    exact ((Real.measurable_log.comp (clamp01_measurable.max
      (measurable_const.sub clamp01_measurable))).neg).sub_const _
  have hg : Measurable fun p : ℝ × ℝ => gXevE N c p.1 p.2 := nsx_measurable_gXevE c
  have hh : Measurable fun p : ℝ × ℝ => -Real.log (sxCor p.1 p.2) := by
    unfold sxCor
    have hy : Measurable fun p : ℝ × ℝ => clamp01 p.1 := clamp01_measurable.comp measurable_fst
    have hu : Measurable fun p : ℝ × ℝ => clamp01 p.2 := clamp01_measurable.comp measurable_snd
    exact (Real.measurable_log.comp (Measurable.ite (measurableSet_lt measurable_const hy) hu
      (measurable_const.sub hu))).neg
  have hW : MeasurableSet {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} :=
    measurableSet_le measurable_const (clamp01_measurable.max (measurable_const.sub clamp01_measurable))
  have hsub : {w : Param N | CellEvX N s r0 x .effect c w ∧
      ∑ i, -Real.log (sxCor (w s i) (w (flipAt x s) i)) ≤ L} ⊆
      {w | (∀ i, w ((fun _ : Fin N => s) i) i ∈ {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)}) ∧
        ∑ i, (fun y => -Real.log (clamp01 y)) (w ((fun _ : Fin N => r0) i) i) ≤ x0 * N + slT N ∧
        ∑ i, ellSX N (w ((fun _ : Fin N => s) i) i) ≤
          ∑ i, (fun y => -Real.log (clamp01 y)) (w ((fun _ : Fin N => r0) i) i) ∧
        ∑ i, gXevE N c (w ((fun _ : Fin N => s) i) i) (w ((fun _ : Fin N => flipAt x s) i) i) ≤ 0 ∧
        (∀ i, 1 / 2 - deltaU N ≤ w ((fun _ : Fin N => r0) i) i) ∧
        ∑ i, (fun y u => -Real.log (sxCor y u)) (w ((fun _ : Fin N => s) i) i)
          (w ((fun _ : Fin N => flipAt x s) i) i) ≤ L} := by
    rintro w ⟨hc, hL⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := cellEvX_eff_sub_template hN s r0 x c hcm hδ hc
    exact ⟨h1, h2, h3, h4, h5, hL⟩
  refine (measure_mono hsub).trans ?_
  refine (joint_template_eff_floor_h (fun _ => s) (fun _ => flipAt x s) (fun _ => r0)
    (fun _ => (flipAt_ne x s).symm) (fun _ => hsr) (fun _ => hfr)
    (fun y => -Real.log (clamp01 y)) (ellSX N) (gXevE N c) (fun y u => -Real.log (sxCor y u))
    hellT hellS hg hh _ hW (x0 * N + slT N) t lamU (lam : ℝ) ht hlamU (Nat.cast_nonneg _)
    (1 / 2 - deltaU N) mu hmu L).trans ?_
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow (mul_nonneg hJs0 hJt0),
    ENNReal.ofReal_mul hJs0]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zero_le (mul_le_mul' hJs hJt) N) zero_le

/-- `H = (1 - 2^{-(p+1)})/(p+1) ≥ 1/16` for `p ≤ 7`. -/
lemma sx_H_ge (p : ℕ) (hp : p ≤ 7) : (1 : ℝ) / 16 ≤ (1 - (1 / 2 : ℝ) ^ (p + 1)) / (p + 1) := by
  interval_cases p <;> norm_num

set_option maxHeartbeats 1000000 in
/-- **One original effect cell with the `s^x` constraint, explicit.** -/
theorem sxCell_prob (hN : 0 < N) (s r0 : State N) (x : Fin N) {c : ℚ × ℚ}
    (hc : c ∈ cellsXEffectData) (hδ : deltaU N < 1 / 2) (hsr : s ≠ r0) (hfr : flipAt x s ≠ r0) :
    cubeM N {w : Param N | CellEvX N s r0 x .effect c w ∧
        ∑ i, -Real.log (sxCor (w s i) (w (flipAt x s) i)) ≤ x0 * N + Real.log 2} ≤
      ENNReal.ofReal (Real.exp (-((sxR1 : ℝ) * N)) *
        Real.exp (38 * slT N + 34 * (8 + slV N) + 34) / 2 ^ N) := by
  have hall := sxLink_all
  rw [List.all_eq_true] at hall
  obtain ⟨C, hC, hlink⟩ := List.any_eq_true.1 (hall c hc)
  have hok : sxOK C = true := (List.all_eq_true.1 sxCells_ok) C hC
  have hb := (List.all_eq_true.1 sxBounds) C hC
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨hlam, hp⟩, hLU⟩ := hb
  simp only [sxLink, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hlink
  obtain ⟨⟨hv4, hcap⟩, hc2⟩ := hlink
  simp only [sxOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hvw⟩, hw1⟩, hv1⟩, hw2⟩, he1⟩, he0⟩, hub⟩, hq0⟩, hq⟩, hlnhi⟩, hrate⟩ := hok
  set c' : ℚ × ℚ := (c.1, C.w ^ 4) with hc'
  have hc2R : (1 : ℝ) / 2 ≤ c.2 := by
    have := (Rat.cast_le (K := ℝ)).2 hc2; push_cast at this ⊢; exact this
  have hw4 : (1 : ℝ) / 2 ≤ (C.w : ℝ) ^ 4 := by
    have := (Rat.cast_le (K := ℝ)).2 hw2; push_cast at this ⊢; exact this
  have hmono := cellEvX_mono_eff s r0 x (c := c) (c' := c') (by simp only [hc'])
    (by
      simp only [hc']
      rcases hcap with h | h
      · left; exact_mod_cast h
      · right; rw [h]; norm_num)
    (by linarith) (by simp only [hc']; push_cast; linarith)
  have hmono' : {w : Param N | CellEvX N s r0 x .effect c w ∧
      ∑ i, -Real.log (sxCor (w s i) (w (flipAt x s) i)) ≤ x0 * N + Real.log 2} ⊆
      {w | CellEvX N s r0 x .effect c' w ∧
        ∑ i, -Real.log (sxCor (w s i) (w (flipAt x s) i)) ≤ x0 * N + Real.log 2} :=
    fun w hw => ⟨hmono hw.1, hw.2⟩
  refine (measure_mono hmono').trans ?_
  have hδ0 : 0 < deltaU N := by unfold deltaU; positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcm' : (1 : ℝ) / 2 ≤ (c'.2 : ℝ) := by simp only [hc']; push_cast; exact hw4
  set lu : ℝ := (C.LU : ℝ) / 4 with hludef
  set t : ℝ := lu + C.p with htdef
  set K : ℝ := 7 * deltaU N + (slV N + Real.log 2) / N with hK
  set I := ∫ X in ((C.v : ℝ) ^ 4)..1, X ^ ((C.LU : ℝ) / 4) * gXw C.lam ((C.w : ℝ) ^ 4) X with hIdef
  set H : ℝ := (1 - (1 / 2 : ℝ) ^ (C.p + 1)) / (C.p + 1) with hH
  have hv' : (0 : ℝ) < C.v := by exact_mod_cast hv
  have hv0 : (0 : ℝ) < (C.v : ℝ) ^ 4 := by positivity
  have hb : (C.v : ℝ) ^ 4 ≤ max (1 / 2) (c'.1 : ℝ) := by
    simp only [hc']; have := (Rat.cast_le (K := ℝ)).2 hv4; push_cast at this; exact this
  have hb1 : (C.v : ℝ) ^ 4 ≤ 1 := pow_le_one₀ hv'.le (by exact_mod_cast hv1.le)
  have hIq : I = ((sxItot C : ℚ) : ℝ) := by
    rw [hIdef, sx_exact C.v C.w hv hvw hw1 C.lam C.LU he1 he0]; rfl
  have hIub : I ≤ (C.ub : ℝ) := by rw [hIq]; exact_mod_cast hub
  have hH16 : (1 : ℝ) / 16 ≤ H := sx_H_ge C.p hp
  have hH0 : 0 < H := lt_of_lt_of_le (by norm_num) hH16
  have hlu0 : 0 ≤ lu := by positivity
  have hI0 : 0 ≤ I := by
    refine intervalIntegral.integral_nonneg hb1 fun X hX => ?_
    have hX0 : 0 < X := lt_of_lt_of_le hv0 hX.1
    exact mul_nonneg (Real.rpow_nonneg hX0.le _) (gXw_nonneg _ hX0 hX.2 (by linarith) (by linarith [hX.2]))
  have hJs := sx_s_factor (N := N) C.lam c' hcm' hlu0 hv0 hb hb1
  have hI' : (∫ X in ((C.v : ℝ) ^ 4)..1, X ^ lu * gXw C.lam (c'.2 : ℝ) X) = I := by
    simp only [hc', hludef]; push_cast; rfl
  rw [hI'] at hJs
  have hJt := tcJ_le (N := N) C.p (t := t) (lu := lu) (by simp only [htdef]; ring) hδ
  set C1 : ℝ := Real.exp (lu * (slT N / N)) * Real.exp ((C.lam : ℝ) * K) with hC1
  have hlog1 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  refine (cellEvX_sx_prob hN s r0 x c' hcm' hδ hsr hfr t lu C.lam (Real.log (N + 1))
    (by positivity) hlu0 hlog1 (Js := C1 * (2 * I)) (Jt := H + 2 * deltaU N)
    (by positivity) (by positivity) hJs hJt (x0 * N + Real.log 2)).trans ?_
  -- the rate, through `ub`
  have hub0 : (0 : ℝ) < C.ub := by
    have : (0 : ℚ) < C.ub := by
      by_contra hneg; push Not at hneg
      have : 2 * C.ub * rsEx C.p ≤ 0 := by
        have hE : (0 : ℚ) ≤ rsEx C.p := by
          unfold rsEx
          have : ((1 : ℚ) / 2) ^ (C.p + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          apply div_nonneg (by linarith) (by positivity)
        nlinarith
      linarith
    exact_mod_cast this
  have hEx : (rsEx C.p : ℝ) = 2 * H := by unfold rsEx; push_cast; simp only [hH]; ring
  have hEx0 : (0 : ℝ) < rsEx C.p := by rw [hEx]; positivity
  have hcr := crLog_le (q := 2 * C.ub * rsEx C.p) (r := C.r) C.k C.n (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hq0, hq⟩, hlnhi⟩)
  have hsplitL : Real.log (((2 * C.ub * rsEx C.p : ℚ)) : ℝ) =
      Real.log 2 + Real.log (C.ub : ℝ) + Real.log (rsEx C.p : ℝ) := by
    push_cast
    rw [Real.log_mul (by positivity) hEx0.ne', Real.log_mul (by norm_num) hub0.ne']
  have hx0 := cr_x0_bounds.2
  have hrR : ((C.r : ℚ) : ℝ) + ((C.LU : ℝ) / 4 + C.p + 1) * (crX0hi : ℝ) ≤ -(sxR1 : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 hrate; push_cast at this ⊢; linarith
  have hlog : Real.log 2 + Real.log (C.ub : ℝ) + Real.log (rsEx C.p : ℝ) + (t + 1) * x0 ≤ -(sxR1 : ℝ) := by
    have ht0 : (0 : ℝ) ≤ t + 1 := by positivity
    have := mul_le_mul_of_nonneg_left hx0 ht0
    simp only [htdef, hludef] at this ⊢
    linarith
  have hrate' := rate_of_log_le hub0 hEx0 hlog N
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  -- the correction `(1 + 2δ/H)^N ≤ e^{32}`
  have hδN : deltaU N * N ≤ 1 := by
    unfold deltaU; rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  have hcorr : (1 + 2 * deltaU N / H) ^ N ≤ Real.exp 32 := by
    calc (1 + 2 * deltaU N / H) ^ N ≤ (Real.exp (2 * deltaU N / H)) ^ N := by
          gcongr
          linarith [Real.add_one_le_exp (2 * deltaU N / H)]
      _ = Real.exp (2 * (deltaU N * N) / H) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ Real.exp 32 := by
          apply Real.exp_le_exp.2
          rw [div_le_iff₀ hH0]; nlinarith
  have e1 : C1 ^ N = Real.exp (lu * slT N + (C.lam : ℝ) * (K * N)) := by
    simp only [hC1]
    rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; field_simp
  -- the lower-order exponent
  have hslT : 0 ≤ slT N := by
    unfold slT
    have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    linarith
  have hslV : 0 ≤ slV N := by unfold slV; positivity
  have hKNe : K * N = 7 * (deltaU N * N) + (slV N + Real.log 2) := by
    simp only [hK]; field_simp
  have hKN : K * N ≤ 7 + slV N + 1 := by
    rw [hKNe]; linarith [Real.log_two_lt_d9]
  have hKN0 : 0 ≤ K * N := by
    rw [hKNe]; have := Real.log_pos one_lt_two; positivity
  have hlamR : (C.lam : ℝ) ≤ 29 := by exact_mod_cast hlam
  have hluR : lu ≤ 15 := by
    have : (C.LU : ℝ) ≤ 60 := by exact_mod_cast hLU
    simp only [hludef]; linarith
  have hpR : (C.p : ℝ) ≤ 7 := by exact_mod_cast hp
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hE : t * slT N + (lu * slT N + (C.lam : ℝ) * (K * N)) + Real.log 2 + 32 ≤
      38 * slT N + 34 * (8 + slV N) + 34 := by
    have hl0 : (0 : ℝ) ≤ C.lam := Nat.cast_nonneg _
    have a1 : t * slT N ≤ 22 * slT N := mul_le_mul_of_nonneg_right (by simp only [htdef]; linarith) hslT
    have a2 := mul_le_mul_of_nonneg_right hluR hslT
    have a3 := mul_le_mul hlamR hKN hKN0 (by norm_num : (0 : ℝ) ≤ 29)
    nlinarith
  apply ENNReal.ofReal_le_ofReal
  -- `exp(t(x0 N + slT) + x0 N + log 2) (C1 · 2I · (H + 2δ))^N`
  have hJ : C1 * (2 * I) * (H + 2 * deltaU N) ≤ C1 * ((C.ub : ℝ) * (rsEx C.p : ℝ)) * (1 + 2 * deltaU N / H) := by
    rw [hEx]
    have : C1 * (2 * I) * (H + 2 * deltaU N) = C1 * (I * (2 * H)) * (1 + 2 * deltaU N / H) := by
      field_simp
    rw [this]
    gcongr
  have hJ0 : 0 ≤ C1 * (2 * I) * (H + 2 * deltaU N) := by positivity
  calc Real.exp (t * (x0 * N + slT N) + (x0 * N + Real.log 2)) * (C1 * (2 * I) * (H + 2 * deltaU N)) ^ N
      ≤ Real.exp (t * (x0 * N + slT N) + (x0 * N + Real.log 2)) *
          (C1 * ((C.ub : ℝ) * (rsEx C.p : ℝ)) * (1 + 2 * deltaU N / H)) ^ N := by gcongr
    _ = (2 ^ N * (Real.exp ((t + 1) * (x0 * N)) * ((C.ub : ℝ) * (rsEx C.p : ℝ)) ^ N)) *
          (Real.exp (t * slT N + Real.log 2) * C1 ^ N * (1 + 2 * deltaU N / H) ^ N) / 2 ^ N := by
        rw [mul_pow, mul_pow]
        rw [show Real.exp (t * (x0 * N + slT N) + (x0 * N + Real.log 2)) =
            Real.exp ((t + 1) * (x0 * N)) * Real.exp (t * slT N + Real.log 2) by
          rw [← Real.exp_add]; ring_nf]
        field_simp
    _ ≤ Real.exp (-((sxR1 : ℝ) * N)) *
          (Real.exp (t * slT N + Real.log 2) * C1 ^ N * Real.exp 32) / 2 ^ N := by
        rw [div_le_div_iff_of_pos_right h2N]
        exact mul_le_mul hrate' (mul_le_mul_of_nonneg_left hcorr (by positivity)) (by positivity)
          (Real.exp_pos _).le
    _ ≤ _ := by
        rw [div_le_div_iff_of_pos_right h2N, e1, ← Real.exp_add, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
        linarith

/-- **The effect regime with the `s^x` constraint**: at most 61 cells. -/
theorem regEvX_sx_prob (hN : 0 < N) (s r0 : State N) (x : Fin N) (hδ : deltaU N < 1 / 2)
    (hsr : s ≠ r0) (hfr : flipAt x s ≠ r0) :
    cubeM N {w : Param N | RegEvX N s r0 x .effect w ∧
        ∑ i, -Real.log (sxCor (w s i) (w (flipAt x s) i)) ≤ x0 * N + Real.log 2} ≤
      ENNReal.ofReal (61 * (Real.exp (-((sxR1 : ℝ) * N)) *
        Real.exp (38 * slT N + 34 * (8 + slV N) + 34) / 2 ^ N)) := by
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = Real.exp (-((sxR1 : ℝ) * N)) *
      Real.exp (38 * slT N + 34 * (8 + slV N) + 34) / 2 ^ N := ⟨_, rfl⟩
  rw [← hBdef]
  have hset : {w : Param N | RegEvX N s r0 x .effect w ∧
      ∑ i, -Real.log (sxCor (w s i) (w (flipAt x s) i)) ≤ x0 * N + Real.log 2} =
      ⋃ c ∈ cellsXEffectData.toFinset, {w : Param N | CellEvX N s r0 x .effect c w ∧
        ∑ i, -Real.log (sxCor (w s i) (w (flipAt x s) i)) ≤ x0 * N + Real.log 2} := by
    ext w
    simp only [RegEvX, cellsX, Set.mem_setOf_eq, Set.mem_iUnion, List.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨⟨c, hc, h⟩, hL⟩; exact ⟨c, hc, h, hL⟩
    · rintro ⟨c, hc, h, hL⟩; exact ⟨⟨c, hc, h⟩, hL⟩
  rw [hset]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ c ∈ cellsXEffectData.toFinset, cubeM N {w : Param N | CellEvX N s r0 x .effect c w ∧
        ∑ i, -Real.log (sxCor (w s i) (w (flipAt x s) i)) ≤ x0 * N + Real.log 2}
      ≤ ∑ _c ∈ cellsXEffectData.toFinset, ENNReal.ofReal B :=
        Finset.sum_le_sum fun c hc => by
          rw [hBdef]; exact sxCell_prob hN s r0 x (List.mem_toFinset.1 hc) hδ hsr hfr
    _ = (cellsXEffectData.toFinset.card : ENNReal) * ENNReal.ofReal B := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (61 : ENNReal) * ENNReal.ofReal B := by
        gcongr
        have : cellsXEffectData.toFinset.card ≤ cellsXEffectData.length := List.toFinset_card_le _
        have hlen : cellsXEffectData.length = 61 := by decide
        exact_mod_cast hlen ▸ this
    _ = ENNReal.ofReal (61 * B) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 61)]; norm_num

/-! ### 6. `SxEffStmt` -/

lemma sx_absorb : ∀ᶠ N : ℕ in atTop, 61 * (Real.exp (-((sxR1 : ℝ) * N)) *
    Real.exp (38 * slT N + 34 * (8 + slV N) + 34) / 2 ^ N) ≤
      Real.exp (-((10109 / 10000 : ℝ) * N)) / 2 ^ N := by
  set δ : ℝ := (sxR1 : ℝ) - 10109 / 10000 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; unfold sxR1; norm_num
  have hab1 := poly_absorb (61 * Real.exp 16) 0 (δ := δ / 2) (by positivity)
  have hab2 := poly_absorb 1 0 (δ := δ / 2) (by positivity)
  filter_upwards [hab1, hab2] with N hab1 hab2
  have hsl := rs_slack_le N
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  simp only [pow_zero, mul_one, one_mul] at hab1 hab2
  rw [mul_div_assoc', div_le_div_iff_of_pos_right h2N]
  have hE : Real.exp (38 * slT N + 34 * (8 + slV N) + 34) ≤
      Real.exp 16 * Real.exp (4000 + 1400 * Real.log N) * Real.exp (4000 + 1400 * Real.log N) := by
    rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.2; linarith
  have hsplit : Real.exp (-((10109 / 10000 : ℝ) * N)) =
      Real.exp (-((sxR1 : ℝ) * N)) * (Real.exp (δ / 2 * N) * Real.exp (δ / 2 * N)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [hδ]; ring
  rw [hsplit]
  calc 61 * (Real.exp (-((sxR1 : ℝ) * N)) * Real.exp (38 * slT N + 34 * (8 + slV N) + 34))
      ≤ 61 * (Real.exp (-((sxR1 : ℝ) * N)) *
          (Real.exp 16 * Real.exp (4000 + 1400 * Real.log N) * Real.exp (4000 + 1400 * Real.log N))) := by
        gcongr
    _ = Real.exp (-((sxR1 : ℝ) * N)) *
          ((61 * Real.exp 16 * Real.exp (4000 + 1400 * Real.log N)) * Real.exp (4000 + 1400 * Real.log N)) := by
        ring
    _ ≤ Real.exp (-((sxR1 : ℝ) * N)) * (Real.exp (δ / 2 * N) * Real.exp (δ / 2 * N)) := by
        gcongr

/-- `log (σ_N / 2) = -x0 N - log 2`. -/
lemma sx_log_sig (N : ℕ) : Real.log (sigN N / 2) = -(x0 * N) - Real.log 2 := by
  unfold sigN x0
  rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by positivity), Real.log_pow,
    show (2 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, Real.log_inv]
  ring

/-- **`SxEffStmt`, PROVED.** -/
theorem sxEff_proved : SxEffStmt := by
  filter_upwards [sx_absorb, eventually_ge_atTop 7] with N hab hN7 s r0 x hfar
  have hN : 0 < N := by omega
  have hδ : deltaU N < 1 / 2 := by
    unfold deltaU; rw [div_lt_iff₀ (by positivity)]; have : (7 : ℝ) ≤ N := by exact_mod_cast hN7
    linarith
  obtain ⟨h0s, h0sx, -, -⟩ := dr_far_ne hN7 x hfar
  have hsub : {w : Param N | RegEvX N s r0 x .effect w ∧ sigN N / 2 < ∏ k, pTe w s (flipAt x s) k} ⊆
      {w | RegEvX N s r0 x .effect w ∧
        ∑ i, -Real.log (sxCor (w s i) (w (flipAt x s) i)) ≤ x0 * N + Real.log 2} := by
    rintro w ⟨hreg, hlt⟩
    refine ⟨hreg, ?_⟩
    have hσ : 0 < sigN N / 2 := by unfold sigN; positivity
    have hpos : ∀ k ∈ (univ : Finset (Fin N)), pTe w s (flipAt x s) k ≠ 0 := by
      intro k _ h0
      have : ∏ k, pTe w s (flipAt x s) k = 0 := Finset.prod_eq_zero (mem_univ k) h0
      linarith
    have hlog := Real.log_lt_log hσ hlt
    rw [Real.log_prod hpos, sx_log_sig] at hlog
    have e : ∀ i, sxCor (w s i) (w (flipAt x s) i) = pTe w s (flipAt x s) i := fun i => rfl
    simp only [e, Finset.sum_neg_distrib]
    linarith
  refine (measure_mono hsub).trans ((regEvX_sx_prob hN s r0 x hδ (Ne.symm h0s) (Ne.symm h0sx)).trans ?_)
  exact ENNReal.ofReal_le_ofReal hab

end Census
end IIT

#print axioms IIT.Census.sxEff_proved
