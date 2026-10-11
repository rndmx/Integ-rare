/-
Census, B1 GoodX3 leaf `lowFew`, effect side: `le_eff_cell`.

On the effect side `r0` is the tilt row, floored at `1/2 - δ` (`δ = deltaU N = 1/(N+1)`) by `CellEvX`.  The low window
`[1/2 - δ, 1/2 + e^{-N/200})` has length `≤ 2δ`, so the Chernoff weight `e^{5·1[low]}` on the `r0` entries costs
`(e⁵ - 1)·2δ ≤ 296 δ` per unit (a bounded factor over `N` units) and gains `e^{-5N/1000}`: rate `rsR0 + 1/200`.
-/
import IIT.Census.B1NewLeaf3LowC

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- The floored `r0` factor with the low weight `e^{5·1[low]}`. -/
lemma le_floor_factor (p : ℕ) {t lu : ℝ} (htp : t - lu = p) (hδ : deltaU N < 1 / 2) {bb : ℝ}
    (hbb : bb ≤ 1 / 2 + deltaU N) :
    ∫⁻ z in {z : ℝ | 1 / 2 - deltaU N ≤ z}, ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 z)) *
        Real.exp (5 * ({z : ℝ | clamp01 z < bb}.indicator (fun _ => (1 : ℝ)) z))) ∂unif ≤
      ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ (p + 1)) / (p + 1) + 297 * deltaU N) := by
  have hδ0 : 0 < deltaU N := by unfold deltaU; positivity
  set Ar : ℝ → ℝ := fun z => Real.exp ((lu - t) * -Real.log (clamp01 z)) with hAr
  set low : Set ℝ := {z : ℝ | clamp01 z < bb} with hlow
  have hL : MeasurableSet low := measurableSet_lt clamp01_measurable measurable_const
  have hWc : MeasurableSet {z : ℝ | 1 / 2 - deltaU N ≤ z} := measurableSet_le measurable_const measurable_id
  have hArm : Measurable Ar := Real.measurable_exp.comp
    ((Real.measurable_log.comp clamp01_measurable).neg.const_mul _)
  have he5 : Real.exp 5 - 1 ≤ 148 := by
    have h := Real.exp_one_lt_d9
    have e : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    have : Real.exp 1 ^ 5 ≤ (2.7182818286 : ℝ) ^ 5 := pow_le_pow_left₀ (Real.exp_pos _).le h.le 5
    norm_num at this ⊢; linarith
  have he1 : 0 ≤ Real.exp 5 - 1 := by have := Real.add_one_le_exp (5 : ℝ); linarith
  have hA1 : ∀ z, Ar z ≤ 1 := by
    intro z
    simp only [hAr]
    rw [Real.exp_le_one_iff]
    have hl : Real.log (clamp01 z) ≤ 0 := Real.log_nonpos (clamp01_nonneg z) (clamp01_le_one z)
    have : lu - t ≤ 0 := by rw [show lu - t = -(p : ℝ) by linarith]; simp
    nlinarith
  have hpt : ∀ z, ENNReal.ofReal (Ar z * Real.exp (5 * (low.indicator (fun _ => (1 : ℝ)) z))) ≤
      ENNReal.ofReal (Ar z) + low.indicator (fun _ => ENNReal.ofReal (Real.exp 5 - 1)) z := by
    intro z
    have hA0 : 0 ≤ Ar z := (Real.exp_pos _).le
    by_cases hz : z ∈ low
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, mul_one,
        ← ENNReal.ofReal_add hA0 he1]
      apply ENNReal.ofReal_le_ofReal
      have := hA1 z
      nlinarith
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero, Real.exp_zero, mul_one, add_zero]
  calc _ ≤ ∫⁻ z in {z : ℝ | 1 / 2 - deltaU N ≤ z},
          (ENNReal.ofReal (Ar z) + low.indicator (fun _ => ENNReal.ofReal (Real.exp 5 - 1)) z) ∂unif :=
        lintegral_mono fun z => hpt z
    _ = (∫⁻ z in {z : ℝ | 1 / 2 - deltaU N ≤ z}, ENNReal.ofReal (Ar z) ∂unif) +
          ∫⁻ z in {z : ℝ | 1 / 2 - deltaU N ≤ z}, low.indicator (fun _ => ENNReal.ofReal (Real.exp 5 - 1)) z ∂unif :=
        lintegral_add_left (ENNReal.measurable_ofReal.comp hArm) _
    _ ≤ ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ (p + 1)) / (p + 1) + deltaU N) +
          ENNReal.ofReal (Real.exp 5 - 1) * ENNReal.ofReal (2 * deltaU N) := by
        refine add_le_add (tf_floor_factor p htp hδ) ?_
        rw [lintegral_indicator_const hL]
        gcongr
        rw [Measure.restrict_apply hL]
        unfold unif
        rw [Measure.restrict_apply (hL.inter hWc)]
        calc volume (low ∩ {z : ℝ | 1 / 2 - deltaU N ≤ z} ∩ Set.Icc 0 1)
            ≤ volume (Set.Icc (1 / 2 - deltaU N) bb) := by
              refine measure_mono fun z hz => ?_
              obtain ⟨⟨h1, h2⟩, h3⟩ := hz
              have hc : clamp01 z = z := by unfold clamp01; rw [min_eq_right h3.2, max_eq_right h3.1]
              simp only [hlow, Set.mem_setOf_eq, hc] at h1 h2
              exact ⟨h2, h1.le⟩
          _ = ENNReal.ofReal (bb - (1 / 2 - deltaU N)) := Real.volume_Icc
          _ ≤ ENNReal.ofReal (2 * deltaU N) := ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ (p + 1)) / (p + 1) + 297 * deltaU N) := by
        have hH0 : 0 ≤ (1 - (1 / 2 : ℝ) ^ (p + 1)) / (p + 1) := by
          have : (1 / 2 : ℝ) ^ (p + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          apply div_nonneg (by linarith) (by positivity)
        rw [← ENNReal.ofReal_mul he1, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        nlinarith

set_option maxHeartbeats 2000000 in
/-- **An effect cell jointly with the `lowFew` failure.** -/
theorem le_eff_cell (hN : 2 ≤ N) (hδ : deltaU N < 1 / 2) (s r0 : State N) (x x' : Fin N) (hxx : x' ≠ x)
    {c : ℚ × ℚ} (hc : c ∈ cellsXEffectData) (h1 : r0 ≠ s) (h2 : r0 ≠ flipAt x s)
    (hd : r0 ≠ flipAt x' s) (hε : Real.exp (-((N : ℝ) / 200)) ≤ deltaU N) :
    cubeM N ({w | CellEvX N s r0 x .effect c w} ∩ lowFail N r0) ≤
      ENNReal.ofReal (Real.exp (-(((rsR0 : ℝ) + 5 / 1000) * N)) *
        Real.exp (19 * slT N + 17 * (8 + slV N) + 1300) / 2 ^ N) := by
  have hN0 : 0 < N := by omega
  have hδ0 : 0 < deltaU N := by unfold deltaU; positivity
  obtain ⟨C, hC, hok, hlam, hlu, hP, hv, hv1, hw4, hb, hcap, hc2⟩ := fs_eff_partner hc
  set c1 : ℚ × ℚ := (c.1, C.w ^ 4) with hc1
  have hc12 : (c1.2 : ℝ) = (C.w : ℝ) ^ 4 := by simp only [hc1]; push_cast; rfl
  have hcm1 : (1 : ℝ) / 2 ≤ (c1.2 : ℝ) := by rw [hc12]; exact hw4
  have hmono := cellEvX_mono_eff s r0 x (c := c) (c' := c1) (by simp only [hc1])
    (by rw [hc12]; exact hcap) (by linarith) (by linarith)
  have hsubE := cellEvX_eff_sub_template hN0 s r0 x c1 hcm1 hδ
  set lu : ℝ := (C.P : ℝ) / 4 with hludef
  set t : ℝ := lu + C.lu with ht
  have hlu0 : 0 ≤ lu := by positivity
  set bb : ℝ := 1 / 2 + Real.exp (-((N : ℝ) / 200)) with hbb
  set ind : ℝ → ℝ := fun z => {z : ℝ | clamp01 z < bb}.indicator (fun _ => (1 : ℝ)) z with hind
  have hindm : Measurable ind := measurable_const.indicator (measurableSet_lt clamp01_measurable measurable_const)
  set Wx : Set ℝ := {y : ℝ | (c1.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} with hWx
  have hWxm : MeasurableSet Wx :=
    measurableSet_le measurable_const (clamp01_measurable.max (measurable_const.sub clamp01_measurable))
  set Wc : Set ℝ := {y : ℝ | 1 / 2 - deltaU N ≤ y} with hWc
  have hWcm : MeasurableSet Wc := measurableSet_le measurable_const measurable_id
  set f : Fin 4 → Fin N → (ℝ × ℝ) × (ℝ × ℝ) → ℝ :=
    ![fun _ p => -Real.log (clamp01 p.2.1), fun _ p => ellSX N p.1.1 - -Real.log (clamp01 p.2.1),
      fun _ p => gXevE N c1 p.1.1 p.1.2, fun _ p => -ind p.2.1] with hf
  have hell : Measurable fun y : ℝ => -Real.log (clamp01 y) :=
    (Real.measurable_log.comp clamp01_measurable).neg
  have hfm : ∀ k i, Measurable (f k i) := by
    intro k i
    fin_cases k
    · exact hell.comp (measurable_fst.comp measurable_snd)
    · exact (fs_ellSX_meas.comp (measurable_fst.comp measurable_fst)).sub (hell.comp (measurable_fst.comp measurable_snd))
    · exact (fs_gE_meas c1).comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst))
    · exact (hindm.comp (measurable_fst.comp measurable_snd)).neg
  set a : Fin 4 → ℝ := ![x0 * N + slT N, 0, 0, -((N : ℝ) / 1000)] with ha
  set tt : Fin 4 → ℝ := ![t, lu, (C.lam : ℝ), 5] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 4)), 0 ≤ tt k := by
    intro k _; fin_cases k
    · simp only [htt]; simp; positivity
    · simpa [htt] using hlu0
    · simp [htt]
    · simp [htt]
  have hmain := cubeM_chernoff_four (fun _ => s) (fun _ => flipAt x s) (fun _ => r0) (fun _ => flipAt x' s)
    (fun _ => (flipAt_ne x s).symm) (fun _ => Ne.symm h1) (fun _ => (flipAt_ne x' s).symm) (fun _ => Ne.symm h2)
    (fun _ => fs_flip_ne hxx s) (fun _ => hd) univ f hfm a tt htt0 (fun _ => Wx) (fun _ => Wc)
    (fun _ => hWxm) (fun _ => hWcm)
  have hsub : ({w | CellEvX N s r0 x .effect c w} ∩ lowFail N r0 : Set (Param N)) ⊆
      {w | (∀ i, w ((fun _ : Fin N => s) i) i ∈ (fun _ : Fin N => Wx) i ∧
          w ((fun _ : Fin N => r0) i) i ∈ (fun _ : Fin N => Wc) i) ∧
        ∀ j ∈ (univ : Finset (Fin 4)), ∑ i, f j i ((w ((fun _ : Fin N => s) i) i,
          w ((fun _ : Fin N => flipAt x s) i) i), (w ((fun _ : Fin N => r0) i) i,
            w ((fun _ : Fin N => flipAt x' s) i) i)) ≤ a j} := by
    rintro w ⟨hw1, hw2⟩
    obtain ⟨hW1, hT, hL, hV, hF⟩ := hsubE (hmono hw1)
    refine ⟨fun i => ⟨hW1 i, hF i⟩, fun j _ => ?_⟩
    fin_cases j
    · simpa [hf, ha] using hT
    · simp only [hf, ha]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [sum_sub_distrib]; linarith
    · simpa [hf, ha] using hV
    · have hc := lowU_card_eq w r0
      have hlt : (N : ℝ) < 1000 * ((lowU N w r0).card : ℝ) := by exact_mod_cast hw2
      show ∑ i, -ind (w r0 i) ≤ -((N : ℝ) / 1000)
      rw [sum_neg_distrib]
      have : ∑ i, ind (w r0 i) = ((lowU N w r0).card : ℝ) := hc
      rw [this]; linarith
  -- the column factors
  set I1 := fsI C with hI1
  have hI10 := fs_cell_pos C hok
  set H : ℝ := (1 - (1 / 2 : ℝ) ^ (C.lu + 1)) / (C.lu + 1) with hH
  have hH15 : (15 : ℝ) / 64 ≤ H := by
    have key : ∀ n : ℕ, n ≤ 3 → (15 : ℝ) / 64 ≤ (1 - (1 / 2 : ℝ) ^ (n + 1)) / (n + 1) := by
      intro n hn; interval_cases n <;> norm_num
    exact key C.lu hlu
  set E : ℝ := Real.exp (lu * (slT N / N)) * Real.exp ((C.lam : ℝ) * fsK N) with hE
  set J : ℝ := E * (2 * I1) * (H + 297 * deltaU N) with hJ
  have hJ0 : 0 ≤ J := by positivity
  have hbb2 : bb ≤ 1 / 2 + deltaU N := by rw [hbb]; linarith
  have hcol : ∀ i : Fin N, ∫⁻ y in (fun _ : Fin N => Wx) i, ∫⁻ u, ∫⁻ z in (fun _ : Fin N => Wc) i, ∫⁻ v,
      ENNReal.ofReal (Real.exp (-∑ j ∈ (univ : Finset (Fin 4)), tt j * f j i ((y, u), (z, v))))
        ∂unif ∂unif ∂unif ∂unif ≤ ENNReal.ofReal J := by
    intro i
    have hpt : ∀ y u z v, ENNReal.ofReal (Real.exp (-∑ j ∈ (univ : Finset (Fin 4)), tt j * f j i ((y, u), (z, v)))) =
        ENNReal.ofReal (Real.exp (-lu * ellSX N y)) *
          ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXevE N c1 y u)) *
          (ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 z)) * Real.exp (5 * ind z)) *
            ENNReal.ofReal (Real.exp 0)) := by
      intro y u z v
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 2
      simp [Fin.sum_univ_four, hf, htt]
      ring
    simp_rw [hpt]
    have m1 : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (-lu * ellSX N y)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (fs_ellSX_meas.const_mul _))
    have m2 : Measurable fun z : ℝ => ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 z)) *
        Real.exp (5 * ind z)) :=
      ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp (hell.const_mul _)).mul
        (Real.measurable_exp.comp (hindm.const_mul _)))
    have m3 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXevE N c1 p.1 p.2)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((fs_gE_meas c1).const_mul _))
    rw [lint4_split Wx Wc (fun y => ENNReal.ofReal (Real.exp (-lu * ellSX N y)))
      (fun z => ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 z)) * Real.exp (5 * ind z)))
      (fun y u => ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXevE N c1 y u)))
      (fun _ _ => ENNReal.ofReal (Real.exp 0)) m1 m2 m3 measurable_const]
    have hone : ∫⁻ _v : ℝ, ENNReal.ofReal (Real.exp 0) ∂unif = 1 := by
      rw [Real.exp_zero, ENNReal.ofReal_one, lintegral_const, unif_univ, mul_one]
    simp_rw [hone, mul_one]
    have hF := le_floor_factor (N := N) C.lu (t := t) (lu := lu) (by rw [ht]; ring) hδ hbb2
    have hS : ∫⁻ y in Wx, ENNReal.ofReal (Real.exp (-lu * ellSX N y)) *
        ∫⁻ u, ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXevE N c1 y u)) ∂unif ∂unif ≤
        ENNReal.ofReal (E * (2 * I1)) := by
      have hb0 : (0 : ℝ) < (C.v : ℝ) ^ 4 := by positivity
      have hb1 : (C.v : ℝ) ^ 4 ≤ 1 := pow_le_one₀ hv.le hv1.le
      have := s_factor_le (N := N) C.lam c1 hcm1 hlu0 hb0 (by simpa [hc1] using hb) hb1
      have e2 : (∫ X in (C.v : ℝ) ^ 4..1, X ^ lu * gX C.lam (c1.2 : ℝ) X) = I1 := by
        rw [hc12]; simp only [hI1, fsI, hludef]
      rw [e2] at this
      refine this.trans (le_of_eq ?_)
      congr 1
    calc _ ≤ ENNReal.ofReal (E * (2 * I1)) *
          ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ (C.lu + 1)) / (C.lu + 1) + 297 * deltaU N) := mul_le_mul' hS hF
      _ = ENNReal.ofReal J := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  refine (measure_mono hsub).trans (hmain.trans ?_)
  have hsum : ∑ j ∈ (univ : Finset (Fin 4)), tt j * a j = t * (x0 * N + slT N) - 5 * ((N : ℝ) / 1000) := by
    simp [Fin.sum_univ_four, htt, ha]; ring
  rw [hsum]
  calc ENNReal.ofReal (Real.exp (t * (x0 * N + slT N) - 5 * ((N : ℝ) / 1000))) *
        ∏ i : Fin N, ∫⁻ y in (fun _ : Fin N => Wx) i, ∫⁻ u, ∫⁻ z in (fun _ : Fin N => Wc) i, ∫⁻ v,
          ENNReal.ofReal (Real.exp (-∑ j ∈ (univ : Finset (Fin 4)), tt j * f j i ((y, u), (z, v))))
            ∂unif ∂unif ∂unif ∂unif
      ≤ ENNReal.ofReal (Real.exp (t * (x0 * N + slT N) - 5 * ((N : ℝ) / 1000))) *
          ∏ _i : Fin N, ENNReal.ofReal J := by
        gcongr with i; exact hcol i
    _ = ENNReal.ofReal (Real.exp (t * (x0 * N + slT N) - 5 * ((N : ℝ) / 1000)) * J ^ N) := by
        rw [prod_const, card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow hJ0,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hsound := rsCell_sound C hok
        have hEx2 : (rsEx C.lu : ℝ) = 2 * H := by rw [rsEx_cast, hH]; ring
        have hEx0 : (0 : ℝ) < rsEx C.lu := by rw [hEx2]; linarith
        have hs' : Real.log 2 + Real.log I1 + Real.log (rsEx C.lu : ℝ) + ((C.P : ℝ) / 4 + C.lu) * x0 ≤
            -(rsR0 : ℝ) := hsound
        have hunit : Real.exp (t * x0) * (2 * I1 * H) ≤ Real.exp (-(rsR0 : ℝ)) / 2 := by
          have hl : Real.exp (t * x0) * (2 * I1 * H) * 2 =
              Real.exp (Real.log 2 + Real.log I1 + Real.log (rsEx C.lu : ℝ) + t * x0) := by
            rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), Real.exp_log hI10,
              Real.exp_log hEx0, hEx2]; ring
          rw [le_div_iff₀ (by norm_num), hl]
          apply Real.exp_le_exp.2
          rw [ht, hludef]; linarith
        have hHpos : 0 < H := by linarith
        have hJe : J = E * (1 + 297 * deltaU N / H) * (2 * I1 * H) := by rw [hJ]; field_simp
        have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN0
        have hδN : deltaU N * N ≤ 1 := by
          unfold deltaU; rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
        have hslT : 0 ≤ slT N := by
          unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
          linarith
        have hslV : 0 ≤ slV N := by unfold slV; positivity
        have hKN := fsK_mul_le (N := N) (by omega)
        have hKN0 := fsK_mul_nonneg (N := N)
        have hlamR : (C.lam : ℝ) ≤ 17 := by exact_mod_cast hlam
        have hluR : lu ≤ 15 / 2 := by
          have : (C.P : ℝ) ≤ 30 := by exact_mod_cast hP
          rw [hludef]; linarith
        have hpR : (C.lu : ℝ) ≤ 3 := by exact_mod_cast hlu
        have htR : t ≤ 21 / 2 := by rw [ht]; linarith
        have hEN : E ^ N = Real.exp (lu * slT N) * Real.exp ((C.lam : ℝ) * (fsK N * N)) := by
          rw [hE, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
          congr 1 <;> congr 1
          · field_simp
          · ring
        have hcorr : (1 + 297 * deltaU N / H) ^ N ≤ Real.exp 1268 := by
          calc (1 + 297 * deltaU N / H) ^ N ≤ Real.exp (297 * deltaU N / H) ^ N := by
                gcongr; linarith [Real.add_one_le_exp (297 * deltaU N / H)]
            _ = Real.exp (297 * (deltaU N * N) / H) := by rw [← Real.exp_nat_mul]; congr 1; ring
            _ ≤ Real.exp 1268 := Real.exp_le_exp.2 (by
                rw [div_le_iff₀ hHpos]; nlinarith)
        have hpowN : (Real.exp (t * x0) * J) ^ N ≤ (E * (1 + 297 * deltaU N / H)) ^ N *
            (Real.exp (-(rsR0 : ℝ)) / 2) ^ N := by
          rw [← mul_pow]
          apply pow_le_pow_left₀ (by positivity)
          rw [hJe]
          calc Real.exp (t * x0) * (E * (1 + 297 * deltaU N / H) * (2 * I1 * H))
              = E * (1 + 297 * deltaU N / H) * (Real.exp (t * x0) * (2 * I1 * H)) := by ring
            _ ≤ E * (1 + 297 * deltaU N / H) * (Real.exp (-(rsR0 : ℝ)) / 2) :=
                mul_le_mul_of_nonneg_left hunit (by positivity)
        have hsplit : Real.exp (t * (x0 * N + slT N) - 5 * ((N : ℝ) / 1000)) * J ^ N =
            Real.exp (t * slT N) * (Real.exp (t * x0) * J) ^ N * Real.exp (-(5 / 1000 * (N : ℝ))) := by
          have : Real.exp (t * (x0 * N)) = Real.exp (t * x0) ^ N := by rw [← Real.exp_nat_mul]; ring_nf
          rw [sub_eq_add_neg, mul_add, Real.exp_add, Real.exp_add, this, mul_pow (Real.exp (t * x0)) J N,
            show -(5 * ((N : ℝ) / 1000)) = -(5 / 1000 * (N : ℝ)) by ring]
          ring
        rw [hsplit]
        have hR : (Real.exp (-(rsR0 : ℝ)) / 2) ^ N = Real.exp (-((rsR0 : ℝ) * N)) / 2 ^ N := by
          rw [div_pow, ← Real.exp_nat_mul]; ring_nf
        have hEc : (E * (1 + 297 * deltaU N / H)) ^ N ≤
            Real.exp (lu * slT N) * Real.exp ((C.lam : ℝ) * (fsK N * N)) * Real.exp 1268 := by
          rw [mul_pow, hEN]
          exact mul_le_mul_of_nonneg_left hcorr (by positivity)
        have hexpo : Real.exp (t * slT N) * (Real.exp (lu * slT N) * Real.exp ((C.lam : ℝ) * (fsK N * N)) *
            Real.exp 1268) ≤ Real.exp (19 * slT N + 17 * (8 + slV N) + 1300) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.2
          have a1 := mul_le_mul_of_nonneg_right htR hslT
          have a2 := mul_le_mul_of_nonneg_right hluR hslT
          have a3 := mul_le_mul hlamR hKN hKN0 (by norm_num : (0 : ℝ) ≤ 17)
          linarith
        have hRR : Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (-(5 / 1000 * (N : ℝ))) =
            Real.exp (-(((rsR0 : ℝ) + 5 / 1000) * N)) := by rw [← Real.exp_add]; ring_nf
        calc Real.exp (t * slT N) * (Real.exp (t * x0) * J) ^ N * Real.exp (-(5 / 1000 * (N : ℝ)))
            ≤ Real.exp (t * slT N) * ((E * (1 + 297 * deltaU N / H)) ^ N * (Real.exp (-((rsR0 : ℝ) * N)) / 2 ^ N)) *
                Real.exp (-(5 / 1000 * (N : ℝ))) := by
              rw [← hR]; gcongr
          _ ≤ Real.exp (t * slT N) * ((Real.exp (lu * slT N) * Real.exp ((C.lam : ℝ) * (fsK N * N)) *
                Real.exp 1268) * (Real.exp (-((rsR0 : ℝ) * N)) / 2 ^ N)) * Real.exp (-(5 / 1000 * (N : ℝ))) := by
              gcongr
          _ = (Real.exp (t * slT N) * (Real.exp (lu * slT N) * Real.exp ((C.lam : ℝ) * (fsK N * N)) *
                Real.exp 1268)) * (Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (-(5 / 1000 * (N : ℝ)))) / 2 ^ N := by
              ring
          _ ≤ Real.exp (19 * slT N + 17 * (8 + slV N) + 1300) *
                (Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (-(5 / 1000 * (N : ℝ)))) / 2 ^ N := by
              gcongr
          _ = _ := by rw [hRR]; ring

end Census
end IIT

#print axioms IIT.Census.le_eff_cell
