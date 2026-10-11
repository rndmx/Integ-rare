/-
Census, Lemma RS, effect side: the mirror template.  Rows: `ra = s` (base entries, V-sum with `rb = s^x`, the
window `W`), `rc = r0` (tilt).  Constraints: `Σ ellT(y_{r0}) ≤ B` (tilt), `Σ ellS(y_s) ≤ Σ ellT(y_{r0})` (link),
`Σ g(y_s, y_{s^x}) ≤ 0` (V-sum).  Per unit the Chernoff factor splits as
`(∫_{x∈W} e^{-λ_u ellS x} ∫_u e^{-λ g x u}) · ∫_y e^{(λ_u - t) ellT y}`.
-/
import IIT.Census.B1Chernoff
import IIT.Census.B1RegRS

namespace IIT
namespace Census

open MeasureTheory Finset

variable {N : ℕ}

theorem joint_template_eff (ra rb rc : Fin N → State N)
    (hab : ∀ i, ra i ≠ rb i) (hac : ∀ i, ra i ≠ rc i) (hbc : ∀ i, rb i ≠ rc i)
    (ellT ellS : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (hellT : Measurable ellT) (hellS : Measurable ellS)
    (hg : Measurable fun p : ℝ × ℝ => g p.1 p.2) (W : Set ℝ) (hW : MeasurableSet W)
    (B t lamU lam : ℝ) (ht : 0 ≤ t) (hlamU : 0 ≤ lamU) (hlam : 0 ≤ lam) :
    cubeM N {w | (∀ i, w (ra i) i ∈ W) ∧ ∑ i, ellT (w (rc i) i) ≤ B ∧
        ∑ i, ellS (w (ra i) i) ≤ ∑ i, ellT (w (rc i) i) ∧ ∑ i, g (w (ra i) i) (w (rb i) i) ≤ 0} ≤
      ENNReal.ofReal (Real.exp (t * B)) *
        ((∫⁻ x in W, ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
            ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g x u)) ∂unif ∂unif) *
          ∫⁻ y, ENNReal.ofReal (Real.exp ((lamU - t) * ellT y)) ∂unif) ^ N := by
  set f : Fin 3 → Fin N → ℝ × ℝ × ℝ → ℝ :=
    ![fun _ p => ellT p.2.2, fun _ p => ellS p.1 - ellT p.2.2, fun _ p => g p.1 p.2.1] with hf
  have hfm : ∀ k i, Measurable (f k i) := by
    intro k i
    fin_cases k
    · exact hellT.comp (measurable_snd.comp measurable_snd)
    · exact (hellS.comp measurable_fst).sub (hellT.comp (measurable_snd.comp measurable_snd))
    · exact hg.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  set a : Fin 3 → ℝ := ![B, 0, 0] with ha
  set tt : Fin 3 → ℝ := ![t, lamU, lam] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 3)), 0 ≤ tt k := by
    intro k _; fin_cases k <;> simpa [htt]
  have hmain := cubeM_chernoff_three ra rb rc hab hac hbc univ f hfm a tt htt0 (fun _ => W)
    (fun _ => hW)
  refine (measure_mono ?_).trans (hmain.trans_eq ?_)
  · rintro w ⟨hW', hB, hU, hG⟩
    refine ⟨hW', fun k _ => ?_⟩
    fin_cases k
    · simpa [hf, ha] using hB
    · simp only [hf, ha, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [Finset.sum_sub_distrib]; linarith
    · simpa [hf, ha] using hG
  · have hsum : ∑ k ∈ (univ : Finset (Fin 3)), tt k * a k = t * B := by
      simp [htt, ha, Fin.sum_univ_three]
    rw [hsum]
    congr 1
    have hexp : ∀ i x u y, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 3)),
        tt k * f k i (x, u, y))) = ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
          ENNReal.ofReal (Real.exp (-lam * g x u)) *
            ENNReal.ofReal (Real.exp ((lamU - t) * ellT y)) := by
      intro i x u y
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
        ← Real.exp_add, ← Real.exp_add]
      congr 2
      simp only [Fin.sum_univ_three, hf, htt, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      ring
    have hA : Measurable fun x => ENNReal.ofReal (Real.exp (-lamU * ellS x)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hellS.const_mul _))
    have hBm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-lam * g p.1 p.2)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hg.const_mul _))
    have hC : Measurable fun y => ENNReal.ofReal (Real.exp ((lamU - t) * ellT y)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hellT.const_mul _))
    have hIB : Measurable fun x => ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g x u)) ∂unif :=
      hBm.lintegral_prod_right'
    have hfac : ∀ i : Fin N, ∫⁻ x in W, ∫⁻ u, ∫⁻ y, ENNReal.ofReal (Real.exp
        (-∑ k ∈ (univ : Finset (Fin 3)), tt k * f k i (x, u, y))) ∂unif ∂unif ∂unif =
        (∫⁻ x in W, ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
            ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g x u)) ∂unif ∂unif) *
          ∫⁻ y, ENNReal.ofReal (Real.exp ((lamU - t) * ellT y)) ∂unif := by
      intro i
      have hAB : Measurable fun x => ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g x u)) ∂unif := hA.mul hIB
      simp_rw [hexp i]
      rw [← lintegral_mul_const _ hAB]
      refine lintegral_congr fun x => ?_
      have hBx : Measurable fun u => ENNReal.ofReal (Real.exp (-lam * g x u)) :=
        hBm.comp (measurable_const.prodMk measurable_id)
      have hABx : Measurable fun u => ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
          ENNReal.ofReal (Real.exp (-lam * g x u)) := hBx.const_mul _
      simp_rw [lintegral_const_mul _ hC]
      rw [lintegral_mul_const _ hABx, lintegral_const_mul _ hBx]
    rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]

theorem joint_template_eff_floor (ra rb rc : Fin N → State N)
    (hab : ∀ i, ra i ≠ rb i) (hac : ∀ i, ra i ≠ rc i) (hbc : ∀ i, rb i ≠ rc i)
    (ellT ellS : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (hellT : Measurable ellT) (hellS : Measurable ellS)
    (hg : Measurable fun p : ℝ × ℝ => g p.1 p.2) (W : Set ℝ) (hW : MeasurableSet W)
    (B t lamU lam : ℝ) (ht : 0 ≤ t) (hlamU : 0 ≤ lamU) (hlam : 0 ≤ lam) (a : ℝ) (mu : ℝ) (hmu : 0 ≤ mu) :
    cubeM N {w | (∀ i, w (ra i) i ∈ W) ∧ ∑ i, ellT (w (rc i) i) ≤ B ∧
        ∑ i, ellS (w (ra i) i) ≤ ∑ i, ellT (w (rc i) i) ∧ ∑ i, g (w (ra i) i) (w (rb i) i) ≤ 0 ∧
        ∀ i, a ≤ w (rc i) i} ≤
      ENNReal.ofReal (Real.exp (t * B)) *
        ((∫⁻ x in W, ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
            ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g x u)) ∂unif ∂unif) *
          ∫⁻ y, ENNReal.ofReal (Real.exp ((lamU - t) * ellT y - mu * Set.indicator (Set.Iio a) 1 y))
            ∂unif) ^ N := by
  set f : Fin 4 → Fin N → ℝ × ℝ × ℝ → ℝ :=
    ![fun _ p => ellT p.2.2, fun _ p => ellS p.1 - ellT p.2.2, fun _ p => g p.1 p.2.1,
      fun _ p => Set.indicator (Set.Iio a) 1 p.2.2] with hf
  have hfm : ∀ k i, Measurable (f k i) := by
    intro k i
    fin_cases k
    · exact hellT.comp (measurable_snd.comp measurable_snd)
    · exact (hellS.comp measurable_fst).sub (hellT.comp (measurable_snd.comp measurable_snd))
    · exact hg.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    · exact (measurable_one.indicator measurableSet_Iio).comp (measurable_snd.comp measurable_snd)
  set aa : Fin 4 → ℝ := ![B, 0, 0, 0] with ha
  set tt : Fin 4 → ℝ := ![t, lamU, lam, mu] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 4)), 0 ≤ tt k := by
    intro k _; fin_cases k <;> simpa [htt]
  have hmain := cubeM_chernoff_three ra rb rc hab hac hbc univ f hfm aa tt htt0 (fun _ => W)
    (fun _ => hW)
  refine (measure_mono ?_).trans (hmain.trans_eq ?_)
  · rintro w ⟨hW', hB, hU, hG, hF⟩
    refine ⟨hW', fun k _ => ?_⟩
    fin_cases k
    · simpa [hf, ha] using hB
    · simp only [hf, ha, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [Finset.sum_sub_distrib]; linarith
    · simpa [hf, ha] using hG
    · simp only [hf, ha]
      refine le_of_eq (Finset.sum_eq_zero fun i _ => ?_)
      simp [Set.indicator_of_notMem (show w (rc i) i ∉ Set.Iio a from not_lt.2 (hF i))]
  · have hsum : ∑ k ∈ (univ : Finset (Fin 4)), tt k * aa k = t * B := by
      simp [htt, ha, Fin.sum_univ_four]
    rw [hsum]
    congr 1
    have hexp : ∀ i x u y, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)),
        tt k * f k i (x, u, y))) = ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
          ENNReal.ofReal (Real.exp (-lam * g x u)) *
            ENNReal.ofReal (Real.exp ((lamU - t) * ellT y - mu * Set.indicator (Set.Iio a) 1 y)) := by
      intro i x u y
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
        ← Real.exp_add, ← Real.exp_add]
      congr 2
      simp only [Fin.sum_univ_four, hf, htt, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
      ring
    have hA : Measurable fun x => ENNReal.ofReal (Real.exp (-lamU * ellS x)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hellS.const_mul _))
    have hBm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-lam * g p.1 p.2)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hg.const_mul _))
    have hC : Measurable fun y => ENNReal.ofReal (Real.exp ((lamU - t) * ellT y -
        mu * Set.indicator (Set.Iio a) 1 y)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hellT.const_mul _).sub
        ((measurable_one.indicator measurableSet_Iio).const_mul _)))
    have hIB : Measurable fun x => ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g x u)) ∂unif :=
      hBm.lintegral_prod_right'
    have hfac : ∀ i : Fin N, ∫⁻ x in W, ∫⁻ u, ∫⁻ y, ENNReal.ofReal (Real.exp
        (-∑ k ∈ (univ : Finset (Fin 4)), tt k * f k i (x, u, y))) ∂unif ∂unif ∂unif =
        (∫⁻ x in W, ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
            ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g x u)) ∂unif ∂unif) *
          ∫⁻ y, ENNReal.ofReal (Real.exp ((lamU - t) * ellT y - mu * Set.indicator (Set.Iio a) 1 y))
            ∂unif := by
      intro i
      have hAB : Measurable fun x => ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g x u)) ∂unif := hA.mul hIB
      simp_rw [hexp i]
      rw [← lintegral_mul_const _ hAB]
      refine lintegral_congr fun x => ?_
      have hBx : Measurable fun u => ENNReal.ofReal (Real.exp (-lam * g x u)) :=
        hBm.comp (measurable_const.prodMk measurable_id)
      have hABx : Measurable fun u => ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
          ENNReal.ofReal (Real.exp (-lam * g x u)) := hBx.const_mul _
      simp_rw [lintegral_const_mul _ hC]
      rw [lintegral_mul_const _ hABx, lintegral_const_mul _ hBx]
    rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]

/-- `unif` is invariant under `u ↦ 1 - u`. -/
lemma lintegral_unif_reflect (f : ℝ → ENNReal) (hf : Measurable f) :
    ∫⁻ u, f (1 - u) ∂unif = ∫⁻ u, f u ∂unif := by
  unfold unif
  have hmp : MeasurePreserving (fun u : ℝ => 1 - u) volume volume := Measure.measurePreserving_sub_left volume 1
  rw [← hmp.setLIntegral_comp_preimage measurableSet_Icc hf]
  congr 2
  ext u; simp only [Set.mem_preimage, Set.mem_Icc]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- The effect-side V-term: base `X = max(y, 1-y)` of row `s`, competitor the oriented entry of `s^x`. -/
noncomputable def gXevE (N : ℕ) (c : ℚ × ℚ) (y u : ℝ) : ℝ :=
  min (Real.log (2 * max (clamp01 y) (1 - clamp01 y) /
      (max (clamp01 y) (1 - clamp01 y) + (if 1 / 2 < clamp01 y then clamp01 u else 1 - clamp01 u))))
    (max 0 (Real.log (max (clamp01 y) (1 - clamp01 y) / (c.2 : ℝ))) - 7 * deltaU N) -
    (slV N + Real.log 2) / N

/-- **The effect inner factor**: `E_u exp(-λ gXevE) ≤ exp(λK) gX λ c_m X`, `X = max(y, 1-y)`. -/
theorem inner_mgf_le_eff (lam : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) (y : ℝ) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u)) ∂unif ≤
      ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
        gX lam (c.2 : ℝ) (max (clamp01 y) (1 - clamp01 y))) := by
  set X := max (clamp01 y) (1 - clamp01 y) with hX
  have hX0 : 0 < X := by
    have := le_max_left (clamp01 y) (1 - clamp01 y); have := le_max_right (clamp01 y) (1 - clamp01 y)
    rw [hX]; linarith
  have hX1 : X ≤ 1 := max_le (clamp01_le_one y) (by linarith [clamp01_nonneg y])
  have hcX : clamp01 X = X := by unfold clamp01; rw [min_eq_right hX1, max_eq_right hX0.le]
  -- reduce to the cause-side bound at the base value `X`
  have hmain := inner_mgf_le (N := N) lam c hcm (y := X) (by rw [hcX]; exact hX0)
  rw [hcX] at hmain
  by_cases ho : 1 / 2 < clamp01 y
  · have : ∀ u, gXevE N c y u = gXev N c X u := fun u => by
      unfold gXevE gXev; rw [if_pos ho, hcX]
    simp only [this]; exact hmain
  · have hfm : Measurable fun u : ℝ => ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c X u)) := by
      unfold gXev
      refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.const_mul ?_ _))
      refine (Measurable.min ?_ measurable_const).sub_const _
      exact Real.measurable_log.comp (measurable_const.div (measurable_const.add clamp01_measurable))
    have hrefl : ∀ u ∈ Set.Icc (0 : ℝ) 1, gXevE N c y u = gXev N c X (1 - u) := fun u hu => by
      have hcu : clamp01 u = u := by unfold clamp01; rw [min_eq_right hu.2, max_eq_right hu.1]
      have hcu' : clamp01 (1 - u) = 1 - u := by
        unfold clamp01; rw [min_eq_right (by linarith [hu.1]), max_eq_right (by linarith [hu.2])]
      unfold gXevE gXev; rw [if_neg ho, hcX, hcu, hcu']
    calc ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u)) ∂unif
        = ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c X (1 - u))) ∂unif := by
          unfold unif
          exact setLIntegral_congr_fun measurableSet_Icc fun u hu => by rw [hrefl u hu]
      _ = ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c X u)) ∂unif :=
          lintegral_unif_reflect _ hfm
      _ ≤ _ := hmain

/-- The link term of the effect template (row `s`). -/
noncomputable def ellSX (N : ℕ) (y : ℝ) : ℝ := -Real.log (max (clamp01 y) (1 - clamp01 y)) - slT N / N

/-- **An effect cell inside the floored effect template.** -/
lemma cellEvX_eff_sub_template (hN : 0 < N) (s r0 : State N) (x : Fin N) (c : ℚ × ℚ)
    (hcm : (1 : ℝ) / 2 ≤ c.2) (hδ : deltaU N < 1 / 2) :
    {w : Param N | CellEvX N s r0 x .effect c w} ⊆
      {w | (∀ i, w ((fun _ : Fin N => s) i) i ∈ {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)}) ∧
        ∑ i, (fun y => -Real.log (clamp01 y)) (w ((fun _ : Fin N => r0) i) i) ≤ x0 * N + slT N ∧
        ∑ i, ellSX N (w ((fun _ : Fin N => s) i) i) ≤
          ∑ i, (fun y => -Real.log (clamp01 y)) (w ((fun _ : Fin N => r0) i) i) ∧
        ∑ i, gXevE N c (w ((fun _ : Fin N => s) i) i) (w ((fun _ : Fin N => flipAt x s) i) i) ≤ 0 ∧
        ∀ i, 1 / 2 - deltaU N ≤ w ((fun _ : Fin N => r0) i) i} := by
  rintro w ⟨h1, -, h3, h4, h5, h6⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨fun i => h1 i, h3, ?_, ?_, fun i => ?_⟩
  · have : ∑ i, ellSX N (w s i) = ∑ k, -Real.log (xE w s k) - slT N := by
      simp only [ellSX, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ hNr.ne']
      rfl
    show ∑ i, ellSX N (w s i) ≤ ∑ i, -Real.log (clamp01 (w r0 i))
    rw [this]
    have hX : XW w r0 = ∑ i, -Real.log (clamp01 (w r0 i)) := rfl
    linarith
  · set V : Fin N → ℝ := fun i => min (lamX w s r0 x .effect i)
        (max 0 (Real.log (baseE w s r0 x .effect i / (c.2 : ℝ))) - 7 * deltaU N) with hVdef
    have hterm : ∀ i, gXevE N c (w s i) (w (flipAt x s) i) = V i - (slV N + Real.log 2) / N := by
      intro i; rfl
    have hsum : ∑ i, gXevE N c (w s i) (w (flipAt x s) i) = ∑ i, V i - (slV N + Real.log 2) := by
      simp only [hterm, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ hNr.ne']
    have hVx : V x ≤ Real.log 2 := by
      have hc0 : (0 : ℝ) < c.2 := by linarith
      have hX1 : xE w s x ≤ 1 := max_le (clamp01_le_one _) (by linarith [clamp01_nonneg (w s x)])
      have hX0 : 0 < xE w s x := by
        have := le_max_left (clamp01 (w s x)) (1 - clamp01 (w s x))
        have := le_max_right (clamp01 (w s x)) (1 - clamp01 (w s x))
        unfold xE; linarith
      have hlog : Real.log (xE w s x / (c.2 : ℝ)) ≤ Real.log 2 :=
        Real.log_le_log (div_pos hX0 hc0) (by rw [div_le_iff₀ hc0]; linarith)
      have hδ0 : 0 ≤ deltaU N := by unfold deltaU; positivity
      have := min_le_right (lamX w s r0 x .effect x)
        (max 0 (Real.log (baseE w s r0 x .effect x / (c.2 : ℝ))) - 7 * deltaU N)
      have h2 : max 0 (Real.log (xE w s x / (c.2 : ℝ))) ≤ Real.log 2 :=
        max_le (Real.log_pos one_lt_two).le hlog
      simp only [baseE] at this; simp only [hVdef, baseE]; linarith
    have hrest : ∑ i ∈ univ.erase x, V i ≤ slV N := h5
    show ∑ i, gXevE N c (w s i) (w (flipAt x s) i) ≤ 0
    rw [hsum, ← add_sum_erase _ _ (mem_univ x)]
    linarith
  · -- the floor, from the clamped to the raw entry
    have hf := h6 rfl i
    have hδ0 : 0 ≤ deltaU N := by unfold deltaU; positivity
    by_contra hlt
    push Not at hlt
    have : clamp01 (w r0 i) < 1 / 2 - deltaU N := by
      unfold clamp01
      rw [min_eq_right (by linarith : w r0 i ≤ 1)]
      exact max_lt (by linarith) hlt
    linarith

/-- **One effect cell, Chernoff bound** (rows `s`, `s^x`, `r0` distinct). -/
theorem cellEvX_eff_prob (hN : 0 < N) (s r0 : State N) (x : Fin N) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2)
    (hδ : deltaU N < 1 / 2) (hsr : s ≠ r0) (hfr : flipAt x s ≠ r0) (t lamU lam mu : ℝ) (ht : 0 ≤ t)
    (hlamU : 0 ≤ lamU) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) {Js Jt : ℝ} (hJs0 : 0 ≤ Js) (hJt0 : 0 ≤ Jt)
    (hJs : ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)},
        ENNReal.ofReal (Real.exp (-lamU * ellSX N y)) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * gXevE N c y u)) ∂unif ∂unif ≤ ENNReal.ofReal Js)
    (hJt : ∫⁻ y, ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y) -
        mu * Set.indicator (Set.Iio (1 / 2 - deltaU N)) 1 y)) ∂unif ≤ ENNReal.ofReal Jt) :
    cubeM N {w : Param N | CellEvX N s r0 x .effect c w} ≤
      ENNReal.ofReal (Real.exp (t * (x0 * N + slT N)) * (Js * Jt) ^ N) := by
  have hellT : Measurable fun y : ℝ => -Real.log (clamp01 y) :=
    (Real.measurable_log.comp clamp01_measurable).neg
  have hellS : Measurable (ellSX N) := by
    unfold ellSX
    exact ((Real.measurable_log.comp (clamp01_measurable.max
      (measurable_const.sub clamp01_measurable))).neg).sub_const _
  have hg : Measurable fun p : ℝ × ℝ => gXevE N c p.1 p.2 := by
    unfold gXevE
    have hy : Measurable fun p : ℝ × ℝ => clamp01 p.1 := clamp01_measurable.comp measurable_fst
    have hu : Measurable fun p : ℝ × ℝ => clamp01 p.2 := clamp01_measurable.comp measurable_snd
    have hX : Measurable fun p : ℝ × ℝ => max (clamp01 p.1) (1 - clamp01 p.1) :=
      hy.max (measurable_const.sub hy)
    have hU : Measurable fun p : ℝ × ℝ => if 1 / 2 < clamp01 p.1 then clamp01 p.2 else 1 - clamp01 p.2 :=
      Measurable.ite (measurableSet_lt measurable_const hy) hu (measurable_const.sub hu)
    refine (Measurable.min ?_ ?_).sub_const _
    · exact Real.measurable_log.comp ((measurable_const.mul hX).div (hX.add hU))
    · exact (measurable_const.max (Real.measurable_log.comp (hX.div_const _))).sub_const _
  have hW : MeasurableSet {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} :=
    measurableSet_le measurable_const (clamp01_measurable.max (measurable_const.sub clamp01_measurable))
  refine (measure_mono (cellEvX_eff_sub_template hN s r0 x c hcm hδ)).trans ?_
  refine (joint_template_eff_floor (fun _ => s) (fun _ => flipAt x s) (fun _ => r0)
    (fun _ => (flipAt_ne x s).symm) (fun _ => hsr) (fun _ => hfr)
    (fun y => -Real.log (clamp01 y)) (ellSX N) (gXevE N c) hellT hellS hg _ hW
    (x0 * N + slT N) t lamU lam ht hlamU hlam (1 / 2 - deltaU N) mu hmu).trans ?_
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow (mul_nonneg hJs0 hJt0),
    ENNReal.ofReal_mul hJs0]
  gcongr

/-- `∫⁻_{(u,v]} y^p = ∫_u^v y^p` (real `p ≥ 0`, `0 ≤ u ≤ v`). -/
lemma lintegral_Ioc_rpow {u v p : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hp : 0 ≤ p) :
    ∫⁻ y in Set.Ioc u v, ENNReal.ofReal (y ^ p) = ENNReal.ofReal (∫ y in u..v, y ^ p) := by
  rw [intervalIntegral.integral_of_le huv, ofReal_integral_eq_lintegral_ofReal]
  · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).1
  · exact Filter.eventually_of_mem (MeasureTheory.ae_restrict_mem measurableSet_Ioc) fun y hy =>
      Real.rpow_nonneg (le_trans hu hy.1.le) p

/-- **The `r0` factor of an effect cell**, explicit: `∫_a^1 y^p dy + e^{-μ} ∫_0^a y^p dy`. -/
theorem tc_factor_le {t lu : ℝ} (hp : lu ≤ t) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (mu : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 y) -
        mu * Set.indicator (Set.Iio a) 1 y)) ∂unif ≤
      ENNReal.ofReal (Real.exp (-mu) * ∫ y in (0 : ℝ)..a, y ^ (t - lu)) +
        ENNReal.ofReal (∫ y in a..1, y ^ (t - lu)) := by
  set p := t - lu with hpdef
  have hp0 : 0 ≤ p := by simp only [hpdef]; linarith
  have hyp : ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      Real.exp ((lu - t) * -Real.log (clamp01 y)) = y ^ p := fun y hy => by
    have hcy : clamp01 y = y := by unfold clamp01; rw [min_eq_right hy.2, max_eq_right hy.1.le]
    rw [hcy, Real.rpow_def_of_pos hy.1]; simp only [hpdef]; ring_nf
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ ({0} ∪ Set.Ioo 0 a) ∪ Set.Icc a 1 := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with h | h
    · exact Or.inl (Or.inl h.symm)
    · by_cases hya : y < a
      · exact Or.inl (Or.inr ⟨h, hya⟩)
      · exact Or.inr ⟨not_lt.1 hya, hy.2⟩
  set F : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 y) -
    mu * Set.indicator (Set.Iio a) 1 y)) with hF
  have hlow : ∫⁻ y in Set.Ioo 0 a, F y ≤ ENNReal.ofReal (Real.exp (-mu) * ∫ y in (0 : ℝ)..a, y ^ p) := by
    calc ∫⁻ y in Set.Ioo 0 a, F y
        = ∫⁻ y in Set.Ioo 0 a, ENNReal.ofReal (Real.exp (-mu)) * ENNReal.ofReal (y ^ p) := by
          refine setLIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
          simp only [hF]
          rw [Set.indicator_of_mem (show y ∈ Set.Iio a from hy.2), sub_eq_add_neg, Real.exp_add,
            hyp y ⟨hy.1, hy.2.le.trans ha1⟩, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
          congr 1; simp only [Pi.one_apply, mul_one]; ring
      _ ≤ ∫⁻ y in Set.Ioc 0 a, ENNReal.ofReal (Real.exp (-mu)) * ENNReal.ofReal (y ^ p) :=
          MeasureTheory.lintegral_mono_set Set.Ioo_subset_Ioc_self
      _ = _ := by
          rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_Ioc_rpow le_rfl ha0.le hp0, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hhigh : ∫⁻ y in Set.Icc a 1, F y = ENNReal.ofReal (∫ y in a..1, y ^ p) := by
    rw [setLIntegral_congr_fun measurableSet_Icc (g := fun y => ENNReal.ofReal (y ^ p)) fun y hy => by
      simp only [hF]
      rw [Set.indicator_of_notMem (show y ∉ Set.Iio a from not_lt.2 hy.1), mul_zero, sub_zero,
        hyp y ⟨lt_of_lt_of_le ha0 hy.1, hy.2⟩]]
    rw [← MeasureTheory.Measure.restrict_congr_set (μ := MeasureTheory.volume)
      (MeasureTheory.Ioc_ae_eq_Icc (a := a) (b := (1 : ℝ)))]
    exact lintegral_Ioc_rpow ha0.le ha1 hp0
  have hzero : ∫⁻ y in ({0} : Set ℝ), F y = 0 :=
    MeasureTheory.setLIntegral_measure_zero _ _ (Real.volume_singleton)
  unfold unif
  calc ∫⁻ y in Set.Icc 0 1, F y
      ≤ ∫⁻ y in ({0} ∪ Set.Ioo 0 a) ∪ Set.Icc a 1, F y := MeasureTheory.lintegral_mono_set hsub
    _ ≤ (∫⁻ y in {0} ∪ Set.Ioo 0 a, F y) + (∫⁻ y in Set.Icc a 1, F y) :=
        MeasureTheory.lintegral_union_le F ({0} ∪ Set.Ioo 0 a) (Set.Icc a 1)
    _ ≤ ((∫⁻ y in ({0} : Set ℝ), F y) + (∫⁻ y in Set.Ioo 0 a, F y)) + (∫⁻ y in Set.Icc a 1, F y) :=
        add_le_add (MeasureTheory.lintegral_union_le F {0} (Set.Ioo 0 a)) le_rfl
    _ ≤ (0 + ENNReal.ofReal (Real.exp (-mu) * ∫ y in (0 : ℝ)..a, y ^ p)) +
          ENNReal.ofReal (∫ y in a..1, y ^ p) :=
        add_le_add (add_le_add (le_of_eq hzero) hlow) (le_of_eq hhigh)
    _ = _ := by rw [zero_add]

/-- Reflection on sets: `∫⁻_{[0,1/2]} f(1-y) = ∫⁻_{[1/2,1]} f`. -/
lemma setLIntegral_reflect_half (f : ℝ → ENNReal) (hf : Measurable f) :
    ∫⁻ y in Set.Icc (0 : ℝ) (1 / 2), f (1 - y) = ∫⁻ y in Set.Icc (1 / 2 : ℝ) 1, f y := by
  have hmp : MeasurePreserving (fun u : ℝ => 1 - u) volume volume :=
    Measure.measurePreserving_sub_left volume 1
  rw [← hmp.setLIntegral_comp_preimage measurableSet_Icc hf]
  congr 2
  ext u; simp only [Set.mem_preimage, Set.mem_Icc]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

lemma gX_measurable (lam : ℕ) (c : ℝ) : Measurable fun y => gX lam c y := by
  unfold gX
  have hmin : Measurable fun y : ℝ => min y c := measurable_id.min measurable_const
  refine Measurable.add (Measurable.mul ((measurable_const.mul hmin).sub measurable_id)
    ((measurable_const.min (measurable_const.div measurable_id)).pow_const lam))
    (Measurable.div ?_ ?_)
  · exact ((measurable_const.add measurable_id).pow_const _).sub ((measurable_const.mul hmin).pow_const _)
  · exact measurable_const.mul ((measurable_const.mul measurable_id).pow_const _)

/-- **The row-`s` factor of an effect cell**: `≤ e^{l_u slT/N} e^{λK} · 2 ∫_b^1 X^{l_u} gX(X) dX`. -/
theorem s_factor_le (lam : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) {lu : ℝ} (hlu : 0 ≤ lu)
    {b : ℝ} (hb0 : 0 < b) (hb : b ≤ max (1 / 2) (c.1 : ℝ)) (hb1 : b ≤ 1) :
    ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)},
        ENNReal.ofReal (Real.exp (-lu * ellSX N y)) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u)) ∂unif ∂unif ≤
      ENNReal.ofReal (Real.exp (lu * (slT N / N)) *
        Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
          (2 * ∫ X in b..1, X ^ lu * gX lam (c.2 : ℝ) X)) := by
  set C := Real.exp (lu * (slT N / N)) * Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N))
  have hC : 0 < C := by positivity
  set G : ℝ → ENNReal := Set.indicator (Set.Ici b) fun X => ENNReal.ofReal (C * (X ^ lu * gX lam (c.2 : ℝ) X))
  have hGm : Measurable G := by
    refine Measurable.indicator ?_ measurableSet_Ici
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((measurable_id.pow_const lu).mul (gX_measurable lam _)))
  set Xf : ℝ → ℝ := fun y => max (clamp01 y) (1 - clamp01 y)
  have hW : MeasurableSet {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} :=
    measurableSet_le measurable_const (clamp01_measurable.max (measurable_const.sub clamp01_measurable))
  -- pointwise bound by `G (X y)` on `W ∩ [0,1]`
  have hpt : ∀ y ∈ {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} ∩ Set.Icc 0 1,
      ENNReal.ofReal (Real.exp (-lu * ellSX N y)) *
        ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u)) ∂unif ≤ G (Xf y) := by
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
          ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u)) ∂unif
        ≤ ENNReal.ofReal (Real.exp (lu * (slT N / N)) * Xf y ^ lu) *
          ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
            gX lam (c.2 : ℝ) (Xf y)) := by gcongr; exact inner_mgf_le_eff lam c hcm y
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; simp only [C]; ring
  unfold unif
  rw [Measure.restrict_restrict hW]
  have hsplit : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc 0 (1 / 2) ∪ Set.Icc (1 / 2) 1 := by
    intro y hy; by_cases h : y ≤ 1 / 2
    · exact Or.inl ⟨hy.1, h⟩
    · exact Or.inr ⟨(not_le.1 h).le, hy.2⟩
  have hlo : ∀ y ∈ Set.Icc (0 : ℝ) (1 / 2), Xf y = 1 - y := fun y hy => by
    have hcy : clamp01 y = y := by unfold clamp01; rw [min_eq_right (show y ≤ 1 by linarith [hy.2]), max_eq_right hy.1]
    simp only [Xf, hcy]; exact max_eq_right (by linarith [hy.2])
  have hhi : ∀ y ∈ Set.Icc (1 / 2 : ℝ) 1, Xf y = y := fun y hy => by
    have hcy : clamp01 y = y := by unfold clamp01; rw [min_eq_right hy.2, max_eq_right (show (0:ℝ) ≤ y by linarith [hy.1])]
    simp only [Xf, hcy]; exact max_eq_left (by linarith [hy.1])
  calc ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} ∩ Set.Icc 0 1,
        ENNReal.ofReal (Real.exp (-lu * ellSX N y)) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u)) ∂unif
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
    _ = 2 * ∫⁻ y in Set.Ioc b 1, ENNReal.ofReal (C * (y ^ lu * gX lam (c.2 : ℝ) y)) := by
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
        have hint : IntegrableOn (fun y => C * (y ^ lu * gX lam (c.2 : ℝ) y)) (Set.Ioc b 1) :=
          (((continuousOn_const.mul ((Real.continuous_rpow_const hlu).continuousOn.mul (gX_continuousOn lam _ hb0)))).integrableOn_Icc).mono_set
            Set.Ioc_subset_Icc_self
        rw [← ofReal_integral_eq_lintegral_ofReal hint, ← intervalIntegral.integral_of_le hb1,
          intervalIntegral.integral_const_mul, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        · congr 1; ring
        · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy => ?_)
          have hy0 : 0 < y := hb0.trans hy.1
          have := gX_nonneg lam (c := (c.2 : ℝ)) hy0 hy.2 (by linarith) (by linarith [hy.2])
          exact mul_nonneg hC.le (mul_nonneg (Real.rpow_nonneg hy0.le _) this)

end Census
end IIT
