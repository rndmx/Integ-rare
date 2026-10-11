/-
Census, B1 GoodX3 leaf `pairLow` with a non-low witness (B1GoodX3): **`joint_pairLow3 : JointBound P0PairLow3`**.

Failure: `∀ j ≠ x, y_{r0,j} + y_{r1,j} > 1 - 1/N ∨ y_{r0,j} < b` (`b = 1/2 + e^{-N/200}`).  Per column `j ≠ x` the
window is `{y + u > 1 - 1/N} ∪ {y < b}`: the inner MGF is `≤ e^{λK}(plG(y) + 1[y < b])` (`pl3_inner_le`), and the
extra mass `∫_{[v⁴, b)} y^p ≤ b - v⁴ ≤ 4·10⁻⁶` (`pl3Cells_ok`, all partner cells have `v⁴ ≥ 1/2 + 10⁻⁷ - 4·10⁻⁶`).
Rate `plR - 1/1000 = 1.0192 > RJ`.
-/
import IIT.Census.B1NewLeaf
import IIT.Census.B1GoodX3

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- Every certified cause cell has `v⁴ ≥ 1/2 + 10⁻⁷ - 4·10⁻⁶`. -/
theorem pl3Cells_ok :
    rsCellsC.all (fun C => decide ((1 : ℚ) / 2 + 1 / 10 ^ 7 - C.v ^ 4 ≤ 4 / 10 ^ 6)) = true := by
  decide +kernel

/-- The `pairLow3` failure set (cause side). -/
def plFail3 (N : ℕ) (r0 : State N) (x : Fin N) : Set (Param N) :=
  {w | ∀ j, j ≠ x → (1 - 1 / (N : ℝ) < clamp01 (w r0 j) + clamp01 (w (flipAt x r0) j) ∨
    clamp01 (w r0 j) < 1 / 2 + Real.exp (-((N : ℝ) / 200)))}

/-- **The inner MGF with the non-low window.** -/
theorem pl3_inner_le (hN : 0 < N) (lam : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) {y : ℝ}
    (hy0 : 0 < clamp01 y) (b : ℝ) :
    ∫⁻ u, {u : ℝ | 1 - 1 / (N : ℝ) < clamp01 y + clamp01 u ∨ clamp01 y < b}.indicator
        (fun u => ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c y u))) u ∂unif ≤
      ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
        plG N lam (c.2 : ℝ) (clamp01 y)) +
      {y : ℝ | clamp01 y < b}.indicator
        (fun _ => ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)))) y := by
  have hY1 := clamp01_le_one y
  have hc0 : (0 : ℝ) < c.2 := by linarith
  have hG0 := plG_nonneg N lam hy0 hY1 hc0 (by linarith)
  by_cases hb : clamp01 y < b
  · have hset : {u : ℝ | 1 - 1 / (N : ℝ) < clamp01 y + clamp01 u ∨ clamp01 y < b} = Set.univ := by
      ext u; simp [hb]
    rw [hset, Set.indicator_univ, Set.indicator_of_mem (show y ∈ {y : ℝ | clamp01 y < b} from hb)]
    refine (inner_mgf_le lam c hcm hy0).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hm0 : 0 ≤ (min 1 ((c.2 : ℝ) / clamp01 y)) ^ lam :=
      pow_nonneg (le_min zero_le_one (div_nonneg hc0.le hy0.le)) _
    have hm1 : (min 1 ((c.2 : ℝ) / clamp01 y)) ^ lam ≤ 1 :=
      pow_le_one₀ (le_min zero_le_one (div_nonneg hc0.le hy0.le)) (min_le_left _ _)
    have hgx : gX lam (c.2 : ℝ) (clamp01 y) ≤ plG N lam (c.2 : ℝ) (clamp01 y) + 1 := by
      unfold plG
      have : (0 : ℝ) ≤ 1 / N := by positivity
      nlinarith [clamp01_nonneg y]
    have he := Real.exp_pos ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N))
    nlinarith
  · have hset : {u : ℝ | 1 - 1 / (N : ℝ) < clamp01 y + clamp01 u ∨ clamp01 y < b} =
        {u : ℝ | 1 - 1 / (N : ℝ) < clamp01 y + clamp01 u} := by
      ext u; simp [hb]
    rw [hset, Set.indicator_of_notMem (show y ∉ {y : ℝ | clamp01 y < b} from hb), add_zero]
    exact pl_inner_le hN lam c hcm hy0

/-- The outer integral of the restricted unit factor. -/
theorem pl_outer (lam : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) (hm0 : (0 : ℝ) < c.1)
    (hm1 : (c.1 : ℝ) ≤ 1) {t lamU : ℝ} (hp : lamU ≤ t) :
    ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ clamp01 y},
        ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
          ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
            plG N lam (c.2 : ℝ) (clamp01 y)) ∂unif ≤
      ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
        ∫ y in (c.1 : ℝ)..1, y ^ (t - lamU) * plG N lam (c.2 : ℝ) y) := by
  set K := 7 * deltaU N + (slV N + Real.log 2) / N
  set a : ℝ := (c.1 : ℝ)
  have hc0 : (0 : ℝ) < c.2 := by linarith
  have hset : {y : ℝ | a ≤ clamp01 y} ∩ Set.Icc 0 1 = Set.Icc a 1 := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have : clamp01 y = y := by unfold clamp01; rw [min_eq_right h3, max_eq_right h2]
      exact ⟨this ▸ h1, h3⟩
    · rintro ⟨h1, h3⟩
      have h2 : 0 ≤ y := le_trans hm0.le h1
      have : clamp01 y = y := by unfold clamp01; rw [min_eq_right h3, max_eq_right h2]
      refine ⟨?_, h2, h3⟩
      rw [this]; exact h1
  have hW : MeasurableSet {y : ℝ | a ≤ clamp01 y} := measurableSet_le measurable_const clamp01_measurable
  unfold unif
  rw [Measure.restrict_restrict hW, hset]
  have hcont : ContinuousOn (fun y => Real.exp ((lam : ℝ) * K) * (y ^ (t - lamU) * plG N lam (c.2 : ℝ) y))
      (Set.Icc a 1) :=
    continuousOn_const.mul ((ContinuousOn.rpow_const continuousOn_id fun y _ =>
      Or.inr (sub_nonneg.2 hp)).mul (plG_continuousOn N lam _ hm0))
  calc ∫⁻ y in Set.Icc a 1, ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
          ENNReal.ofReal (Real.exp ((lam : ℝ) * K) * plG N lam (c.2 : ℝ) (clamp01 y))
      = ∫⁻ y in Set.Icc a 1, ENNReal.ofReal (Real.exp ((lam : ℝ) * K) *
          (y ^ (t - lamU) * plG N lam (c.2 : ℝ) y)) := by
        refine setLIntegral_congr_fun measurableSet_Icc fun y hy => ?_
        have hy0 : 0 < y := lt_of_lt_of_le hm0 hy.1
        have hcy : clamp01 y = y := by
          unfold clamp01; rw [min_eq_right hy.2, max_eq_right hy0.le]
        rw [hcy]
        have hexp : Real.exp ((lamU - t) * -Real.log y) = y ^ (t - lamU) := by
          rw [Real.rpow_def_of_pos hy0]; ring_nf
        rw [hexp, ← ENNReal.ofReal_mul (Real.rpow_nonneg hy0.le _)]; congr 1; ring
    _ = ENNReal.ofReal (∫ y in Set.Icc a 1, Real.exp ((lam : ℝ) * K) *
          (y ^ (t - lamU) * plG N lam (c.2 : ℝ) y)) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)]
        refine Filter.eventually_of_mem (ae_restrict_mem measurableSet_Icc) fun y hy => ?_
        have hy0 : 0 < y := lt_of_lt_of_le hm0 hy.1
        exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.rpow_nonneg hy0.le _)
          (plG_nonneg N lam hy0 hy.2 hc0 (by have := hy.2; linarith)))
    _ ≤ _ := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hm1,
          intervalIntegral.integral_const_mul]

/-- The low-window part of the outer integral. -/
lemma pl3_low (a b d E0 : ℝ) (ha : 0 < a) (hd : b - a ≤ d) (hE0 : 0 ≤ E0) {t lamU : ℝ} (hp : lamU ≤ t) :
    ∫⁻ y in {y : ℝ | a ≤ clamp01 y}, ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
      {y : ℝ | clamp01 y < b}.indicator (fun _ => ENNReal.ofReal E0) y ∂unif ≤ ENNReal.ofReal (E0 * d) := by
  have hWa : MeasurableSet {y : ℝ | a ≤ clamp01 y} := measurableSet_le measurable_const clamp01_measurable
  have hL : MeasurableSet {y : ℝ | clamp01 y < b} := measurableSet_lt clamp01_measurable measurable_const
  calc _ ≤ ∫⁻ y in {y : ℝ | a ≤ clamp01 y}, {y : ℝ | clamp01 y < b}.indicator
          (fun _ => ENNReal.ofReal E0) y ∂unif := by
        refine setLIntegral_mono' hWa fun y hy => ?_
        have hy0 : 0 < clamp01 y := lt_of_lt_of_le ha hy
        have hA : Real.exp ((lamU - t) * -Real.log (clamp01 y)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have := Real.log_nonpos hy0.le (clamp01_le_one y)
          nlinarith
        calc ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
              {y : ℝ | clamp01 y < b}.indicator (fun _ => ENNReal.ofReal E0) y
            ≤ 1 * {y : ℝ | clamp01 y < b}.indicator (fun _ => ENNReal.ofReal E0) y := by
              gcongr; exact ENNReal.ofReal_le_one.2 hA
          _ = _ := one_mul _
    _ = ENNReal.ofReal E0 * (unif.restrict {y : ℝ | a ≤ clamp01 y}) {y : ℝ | clamp01 y < b} :=
        lintegral_indicator_const hL _
    _ ≤ ENNReal.ofReal E0 * ENNReal.ofReal d := by
        gcongr
        rw [Measure.restrict_apply hL]
        unfold unif
        rw [Measure.restrict_apply (hL.inter hWa)]
        calc volume ({y : ℝ | clamp01 y < b} ∩ {y : ℝ | a ≤ clamp01 y} ∩ Set.Icc 0 1)
            ≤ volume (Set.Icc a b) := by
              refine measure_mono fun y hy => ?_
              obtain ⟨⟨h1, h2⟩, h3⟩ := hy
              have hc : clamp01 y = y := by unfold clamp01; rw [min_eq_right h3.2, max_eq_right h3.1]
              simp only [Set.mem_setOf_eq, hc] at h1 h2
              exact ⟨h2, h1.le⟩
          _ = ENNReal.ofReal (b - a) := Real.volume_Icc
          _ ≤ ENNReal.ofReal d := ENNReal.ofReal_le_ofReal hd
    _ = _ := (ENNReal.ofReal_mul hE0).symm

/-- **The restricted `J` factor with the non-low window.** -/
theorem pl3_J_le (hN : 0 < N) (lam : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) (hm0 : (0 : ℝ) < c.1)
    (hm1 : (c.1 : ℝ) ≤ 1) {t lamU : ℝ} (hp : lamU ≤ t) (b : ℝ) {d : ℝ} (hd : b - c.1 ≤ d) (hd0 : 0 ≤ d) :
    ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ clamp01 y},
        ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
          ∫⁻ u, {u : ℝ | 1 - 1 / (N : ℝ) < clamp01 y + clamp01 u ∨ clamp01 y < b}.indicator
            (fun u => ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c y u))) u ∂unif ∂unif ≤
      ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
        ∫ y in (c.1 : ℝ)..1, y ^ (t - lamU) * plG N lam (c.2 : ℝ) y) +
      ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) * d) := by
  set K := 7 * deltaU N + (slV N + Real.log 2) / N
  have hWa : MeasurableSet {y : ℝ | (c.1 : ℝ) ≤ clamp01 y} := measurableSet_le measurable_const clamp01_measurable
  have hL : MeasurableSet {y : ℝ | clamp01 y < b} := measurableSet_lt clamp01_measurable measurable_const
  have hAm : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((Real.measurable_log.comp clamp01_measurable).neg.const_mul _))
  calc _ ≤ ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ clamp01 y},
          (ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
            ENNReal.ofReal (Real.exp ((lam : ℝ) * K) * plG N lam (c.2 : ℝ) (clamp01 y)) +
          ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
            {y : ℝ | clamp01 y < b}.indicator (fun _ => ENNReal.ofReal (Real.exp ((lam : ℝ) * K))) y) ∂unif := by
        refine setLIntegral_mono' hWa fun y hy => ?_
        rw [← mul_add]
        exact mul_le_mul' le_rfl (pl3_inner_le hN lam c hcm (lt_of_lt_of_le hm0 hy) b)
    _ = _ := lintegral_add_right _ (hAm.mul (measurable_const.indicator hL))
    _ ≤ _ := add_le_add (pl_outer lam c hcm hm0 hm1 hp) (pl3_low _ b d _ hm0 hd (Real.exp_pos _).le hp)

set_option maxHeartbeats 2000000 in
/-- **One cause cell jointly with the `pairLow` failure.** -/
theorem pl3_cause_cell (hN : 1 ≤ N) (s r0 : State N) (x : Fin N) {c : ℚ × ℚ}
    (hc : c ∈ cellsXCauseData) (h1 : r0 ≠ s) (h3 : flipAt x r0 ≠ s)
    (hε : Real.exp (-((N : ℝ) / 200)) ≤ 1 / 10 ^ 7) :
    cubeM N ({w | CellEvX N s r0 x .cause c w} ∩ plFail3 N r0 x) ≤
      ENNReal.ofReal (Real.exp (-(((plR : ℝ) - 1 / 1000) * N)) *
        Real.exp (14 * slT N + 17 * (8 + slV N) + 210) / 2 ^ N) := by
  have hN0 : 0 < N := by omega
  obtain ⟨C, hC, hok, hlam, hlu, hP, hmono1, hcm1, hm0, hm1⟩ := fs_cause_partner hN0 hc
  have hpl : plOK C = true := (List.all_eq_true.1 plCells_ok) C hC
  obtain ⟨hBcorr, hB2, hB203, hBrate⟩ := pl_unit C hok hpl
  have hIle := pl_int_le hN0 C hok
  have hdC : (1 : ℝ) / 2 + 1 / 10 ^ 7 - (C.v : ℝ) ^ 4 ≤ 4 / 10 ^ 6 := by
    have := (List.all_eq_true.1 pl3Cells_ok) C hC
    simp only [decide_eq_true_eq] at this
    have := (Rat.cast_le (K := ℝ)).2 this; push_cast at this; exact this
  set bb : ℝ := 1 / 2 + Real.exp (-((N : ℝ) / 200)) with hbb
  set c1 : ℚ × ℚ := (C.v ^ 4, C.w ^ 4) with hc1
  have hsubC := cellEvX_sub_template hN0 s r0 x c1 hcm1
  set lu : ℝ := (C.lu : ℝ) with hludef
  set t : ℝ := (C.P : ℝ) / 4 + lu with ht
  have hlu0 : 0 ≤ lu := Nat.cast_nonneg _
  have htlu : lu ≤ t := by rw [ht]; have : (0 : ℝ) ≤ (C.P : ℝ) / 4 := by positivity
                           linarith
  set Wa : Set ℝ := {y : ℝ | (c1.1 : ℝ) ≤ clamp01 y} with hWa
  have hWam : MeasurableSet Wa := measurableSet_le measurable_const clamp01_measurable
  set W : Fin N → Set (ℝ × ℝ × ℝ) := fun i =>
    {p | (c1.1 : ℝ) ≤ clamp01 p.1 ∧ (i ≠ x → (1 - 1 / (N : ℝ) < clamp01 p.1 + clamp01 p.2.1 ∨
      clamp01 p.1 < bb))} with hW
  have hWm : ∀ i, MeasurableSet (W i) := fun i =>
    b1_mset_and (measurableSet_le measurable_const (clamp01_measurable.comp measurable_fst))
      (b1_mset_imp (MeasurableSet.const _) (b1_mset_or (measurableSet_lt measurable_const
        ((clamp01_measurable.comp measurable_fst).add
          (clamp01_measurable.comp (measurable_fst.comp measurable_snd))))
        (measurableSet_lt (clamp01_measurable.comp measurable_fst) measurable_const)))
  have hell : Measurable fun y : ℝ => -Real.log (clamp01 y) :=
    (Real.measurable_log.comp clamp01_measurable).neg
  have hellU : Measurable (ellUX N) := by
    unfold ellUX
    exact ((Real.measurable_log.comp (clamp01_measurable.max
      (measurable_const.sub clamp01_measurable))).neg).sub_const _
  set f : Fin 3 → Fin N → ℝ × ℝ × ℝ → ℝ :=
    ![fun _ p => -Real.log (clamp01 p.1), fun _ p => ellUX N p.2.2 - -Real.log (clamp01 p.1),
      fun _ p => gXev N c1 p.1 p.2.1] with hf
  have hfm : ∀ k i, Measurable (f k i) := by
    intro k i
    fin_cases k
    · exact hell.comp measurable_fst
    · exact (hellU.comp (measurable_snd.comp measurable_snd)).sub (hell.comp measurable_fst)
    · exact (fs_gXev_meas c1).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  set a : Fin 3 → ℝ := ![x0 * N + slT N, 0, 0] with ha
  set tt : Fin 3 → ℝ := ![t, lu, (C.lam : ℝ)] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 3)), 0 ≤ tt k := by
    intro k _; fin_cases k
    · simp only [htt]; simp; positivity
    · simpa [htt] using hlu0
    · simp [htt]
  have hmain := cubeM_chernoff_three_win (fun _ => r0) (fun _ => flipAt x r0) (fun _ => s)
    (fun _ => (flipAt_ne x r0).symm) (fun _ => h1) (fun _ => h3) univ f hfm a tt htt0 W hWm
  have hsub : ({w | CellEvX N s r0 x .cause c w} ∩ plFail3 N r0 x : Set (Param N)) ⊆
      {w | (∀ i, (w ((fun _ : Fin N => r0) i) i, w ((fun _ : Fin N => flipAt x r0) i) i,
          w ((fun _ : Fin N => s) i) i) ∈ W i) ∧
        ∀ k ∈ (univ : Finset (Fin 3)), ∑ i, f k i (w ((fun _ : Fin N => r0) i) i,
          w ((fun _ : Fin N => flipAt x r0) i) i, w ((fun _ : Fin N => s) i) i) ≤ a k} := by
    rintro w ⟨hw1, hw2⟩
    obtain ⟨hW1, hT, hL, hV⟩ := hsubC (hmono1 s r0 x hw1)
    refine ⟨fun i => ⟨hW1 i, fun hi => hw2 i hi⟩, fun k _ => ?_⟩
    fin_cases k
    · simpa [hf, ha] using hT
    · simp only [hf, ha, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [sum_sub_distrib]; linarith
    · simpa [hf, ha] using hV
  -- the column constants
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = fsK N := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (lu * (slT N / N)) := ⟨_, rfl⟩
  obtain ⟨Ex, hExd⟩ : ∃ Ex : ℝ, Ex = 2 * (1 - (1 / 2 : ℝ) ^ (C.lu + 1)) / (C.lu + 1) := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, B = plB C := ⟨_, rfl⟩
  rw [← hBd] at hBcorr hB2 hB203 hBrate
  have hEx2 : (rsEx C.lu : ℝ) = Ex := by rw [hExd, rsEx_cast]
  rw [hEx2] at hBrate
  have hEx0 : 0 < Ex := by
    rw [hExd]
    have : (1 / 2 : ℝ) ^ (C.lu + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    apply div_pos (by linarith) (by positivity)
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB203
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = Real.exp ((C.lam : ℝ) * K) * (E * Ex) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ, hE]; positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hJ1 : 0 ≤ Q * (2 * B) := by positivity
  have hJ2 : 0 ≤ Q * (B + 1 / N + 4 / 10 ^ 6) := by positivity
  -- the column bound
  have hcol : ∀ i : Fin N, ∫⁻ y, ∫⁻ u, ∫⁻ z, (W i).indicator
      (fun p => ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 3)), tt k * f k i p))) (y, u, z)
        ∂unif ∂unif ∂unif ≤ ENNReal.ofReal (if i = x then Q * (2 * B) else Q * (B + 1 / N + 4 / 10 ^ 6)) := by
    intro i
    set A : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 y))) with hA
    set G0 : ℝ → ℝ → ENNReal := fun y u => ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXev N c1 y u)) with hG0
    set F2 : ℝ → ℝ → ENNReal := fun y u => if i = x then G0 y u else
      ({u : ℝ | 1 - 1 / (N : ℝ) < clamp01 y + clamp01 u ∨ clamp01 y < bb}).indicator (fun u => G0 y u) u with hF2
    set F3 : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp (-lu * ellUX N z)) with hF3
    have hAm : Measurable A := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hell.const_mul _))
    have hG0m : Measurable fun p : ℝ × ℝ => G0 p.1 p.2 :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((fs_gXev_meas c1).const_mul _))
    have hF2m : Measurable fun p : ℝ × ℝ => F2 p.1 p.2 := by
      by_cases hix : i = x
      · simp only [hF2, hix, if_true]; exact hG0m
      · have e : (fun p : ℝ × ℝ => F2 p.1 p.2) =
            ({q : ℝ × ℝ | 1 - 1 / (N : ℝ) < clamp01 q.1 + clamp01 q.2 ∨ clamp01 q.1 < bb}).indicator
              (fun q => G0 q.1 q.2) := by
          funext q; simp only [hF2, hix, if_false, Set.indicator, Set.mem_setOf_eq]
        rw [e]
        exact hG0m.indicator ((measurableSet_lt measurable_const
          ((clamp01_measurable.comp measurable_fst).add (clamp01_measurable.comp measurable_snd))).union
          (measurableSet_lt (clamp01_measurable.comp measurable_fst) measurable_const))
    have hF3m : Measurable F3 := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hellU.const_mul _))
    have hpt : ∀ y u z, (W i).indicator
        (fun p => ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 3)), tt k * f k i p))) (y, u, z) ≤
        Wa.indicator A y * F2 y u * F3 z := by
      intro y u z
      by_cases hp : (y, u, z) ∈ W i
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show y ∈ Wa from hp.1)]
        have hF2e : F2 y u = G0 y u := by
          by_cases hix : i = x
          · simp only [hF2, hix, if_true]
          · simp only [hF2, hix, if_false]
            exact Set.indicator_of_mem (show u ∈ {u : ℝ | 1 - 1 / (N : ℝ) < clamp01 y + clamp01 u ∨
              clamp01 y < bb} from hp.2 hix) _
        rw [hF2e]
        simp only [hA, hG0, hF3]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
          ← Real.exp_add, ← Real.exp_add]
        apply le_of_eq
        congr 2
        simp only [Fin.sum_univ_three, hf, htt, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        ring
      · rw [Set.indicator_of_notMem hp]; exact bot_le
    have hstep : ∫⁻ y, ∫⁻ u, ∫⁻ z, (W i).indicator
        (fun p => ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 3)), tt k * f k i p))) (y, u, z)
          ∂unif ∂unif ∂unif ≤ (∫⁻ y in Wa, A y * ∫⁻ u, F2 y u ∂unif ∂unif) * ∫⁻ z, F3 z ∂unif := by
      calc _ ≤ ∫⁻ y, ∫⁻ u, ∫⁻ z, Wa.indicator A y * F2 y u * F3 z ∂unif ∂unif ∂unif :=
            lintegral_mono fun y => lintegral_mono fun u => lintegral_mono fun z => hpt y u z
        _ = (∫⁻ y, Wa.indicator A y * ∫⁻ u, F2 y u ∂unif ∂unif) * ∫⁻ z, F3 z ∂unif :=
            pl_lint3 _ F2 F3 (hAm.indicator hWam) hF2m hF3m
        _ = _ := by
            congr 1
            rw [← lintegral_indicator hWam]
            refine lintegral_congr fun y => ?_
            by_cases hy : y ∈ Wa
            · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
            · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
    have hF3v : ∫⁻ z, F3 z ∂unif = ENNReal.ofReal (E * Ex) := by
      have := lintegral_ellUX (N := N) C.lu
      rw [show -(C.lu : ℝ) = -lu from rfl] at this
      rw [hE, hExd]; exact this
    refine hstep.trans ?_
    rw [hF3v]
    have hpow : t - lu = (C.P : ℝ) / 4 := by rw [ht]; ring
    by_cases hix : i = x
    · rw [if_pos hix]
      have hF2x : ∀ y u, F2 y u = G0 y u := fun y u => by simp only [hF2, hix, if_true]
      simp_rw [hF2x]
      have hJ := cell_J_le (N := N) C.lam c1 hcm1 hm0 hm1 (t := t) (lamU := lu) htlu
      have e1 : (∫ y in (c1.1 : ℝ)..1, y ^ (t - lu) * gX C.lam (c1.2 : ℝ) y) = fsI C := by
        rw [hpow]; simp only [hc1, fsI]; push_cast; rfl
      rw [e1] at hJ
      calc (∫⁻ y in Wa, A y * ∫⁻ u, G0 y u ∂unif ∂unif) * ENNReal.ofReal (E * Ex)
          ≤ ENNReal.ofReal (Real.exp ((C.lam : ℝ) * K) * (2 * B)) * ENNReal.ofReal (E * Ex) := by
            gcongr
            refine hJ.trans (ENNReal.ofReal_le_ofReal ?_)
            rw [hK]
            exact mul_le_mul_of_nonneg_left hB2 (Real.exp_pos _).le
        _ = ENNReal.ofReal (Q * (2 * B)) := by
            rw [← ENNReal.ofReal_mul (by positivity), hQ]; ring_nf
    · rw [if_neg hix]
      have hF2x : ∀ y u, F2 y u = ({u : ℝ | 1 - 1 / (N : ℝ) < clamp01 y + clamp01 u ∨ clamp01 y < bb}).indicator
          (fun u => G0 y u) u := fun y u => by simp only [hF2, hix, if_false]
      simp_rw [hF2x]
      have hd : bb - (c1.1 : ℝ) ≤ 4 / 10 ^ 6 := by
        have : ((c1.1 : ℚ) : ℝ) = (C.v : ℝ) ^ 4 := by simp only [hc1]; push_cast; rfl
        rw [this, hbb]; linarith
      have hJ := pl3_J_le hN0 C.lam c1 hcm1 hm0 hm1 (t := t) (lamU := lu) htlu bb hd (by norm_num)
      have e1 : (∫ y in (c1.1 : ℝ)..1, y ^ (t - lu) * plG N C.lam (c1.2 : ℝ) y) =
          ∫ y in ((C.v : ℝ) ^ 4)..1, y ^ ((C.P : ℝ) / 4) * plG N C.lam ((C.w : ℝ) ^ 4) y := by
        rw [hpow]; simp only [hc1]; push_cast; rfl
      rw [e1] at hJ
      calc (∫⁻ y in Wa, A y * ∫⁻ u, ({u : ℝ | 1 - 1 / (N : ℝ) < clamp01 y + clamp01 u ∨ clamp01 y < bb}).indicator
              (fun u => G0 y u) u ∂unif ∂unif) * ENNReal.ofReal (E * Ex)
          ≤ ENNReal.ofReal (Real.exp ((C.lam : ℝ) * K) * (B + 1 / N + 4 / 10 ^ 6)) *
              ENNReal.ofReal (E * Ex) := by
            gcongr
            refine hJ.trans ((add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
              (show _ ≤ B + 1 / N by linarith) (Real.exp_pos _).le)) le_rfl).trans ?_)
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            apply le_of_eq
            rw [hK]; unfold fsK; ring_nf
        _ = ENNReal.ofReal (Q * (B + 1 / N + 4 / 10 ^ 6)) := by
            rw [← ENNReal.ofReal_mul (by positivity), hQ]; ring_nf
  refine (measure_mono hsub).trans (hmain.trans ?_)
  have hsum : ∑ k ∈ (univ : Finset (Fin 3)), tt k * a k = t * (x0 * N + slT N) := by
    simp [Fin.sum_univ_three, htt, ha]
  rw [hsum]
  calc ENNReal.ofReal (Real.exp (t * (x0 * N + slT N))) * ∏ i : Fin N, ∫⁻ y, ∫⁻ u, ∫⁻ z, (W i).indicator
        (fun p => ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 3)), tt k * f k i p))) (y, u, z)
          ∂unif ∂unif ∂unif
      ≤ ENNReal.ofReal (Real.exp (t * (x0 * N + slT N))) *
          ∏ i : Fin N, ENNReal.ofReal (if i = x then Q * (2 * B) else Q * (B + 1 / N + 4 / 10 ^ 6)) := by
        gcongr with i; exact hcol i
    _ = ENNReal.ofReal (Real.exp (t * (x0 * N + slT N)) * (Q * (2 * B) * (Q * (B + 1 / N + 4 / 10 ^ 6)) ^ (N - 1))) := by
        rw [show (fun i : Fin N => ENNReal.ofReal (if i = x then Q * (2 * B) else Q * (B + 1 / N + 4 / 10 ^ 6))) =
          fun i => if i = x then ENNReal.ofReal (Q * (2 * B)) else ENNReal.ofReal (Q * (B + 1 / N + 4 / 10 ^ 6)) from
            funext fun i => by split_ifs <;> rfl, prod_ite_one, ← ENNReal.ofReal_pow hJ2,
          ← ENNReal.ofReal_mul hJ1, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        -- (1) J1 J2^{N-1} ≤ 2 (Q (B + 1/N + d))^N
        have hstep1 : Q * (2 * B) * (Q * (B + 1 / N + 4 / 10 ^ 6)) ^ (N - 1) ≤
            2 * (Q * (B + 1 / N + 4 / 10 ^ 6)) ^ N := by
          have hpow : (Q * (B + 1 / N + 4 / 10 ^ 6)) ^ N =
              Q * (B + 1 / N + 4 / 10 ^ 6) * (Q * (B + 1 / N + 4 / 10 ^ 6)) ^ (N - 1) := by
            rw [← pow_succ']; congr 1; omega
          rw [hpow]
          have : Q * (2 * B) ≤ 2 * (Q * (B + 1 / N + 4 / 10 ^ 6)) := by
            have : (0 : ℝ) ≤ 1 / N := by positivity
            nlinarith
          nlinarith [pow_nonneg hJ2 (N - 1)]
        -- (2) (B + 1/N + d)^N ≤ B^N e^{203} e^{N/1000}
        have hstep2 : (B + 1 / N + 4 / 10 ^ 6) ^ N ≤ B ^ N * (Real.exp 203 * Real.exp (N / 1000)) := by
          have h1 : B + 1 / N + 4 / 10 ^ 6 ≤ B * Real.exp (1 / (N * B) + 4 / 10 ^ 6 / B) := by
            have := Real.add_one_le_exp (1 / (N * B) + 4 / 10 ^ 6 / B)
            have e : B + 1 / N + 4 / 10 ^ 6 = B * (1 / (N * B) + 4 / 10 ^ 6 / B + 1) := by field_simp; ring
            rw [e]; exact mul_le_mul_of_nonneg_left this hB0.le
          have h2 := pow_le_pow_left₀ (by positivity) h1 N
          rw [mul_pow, ← Real.exp_nat_mul] at h2
          have e2 : (N : ℝ) * (1 / (N * B) + 4 / 10 ^ 6 / B) = 1 / B + N * (4 / 10 ^ 6 / B) := by
            field_simp
          rw [e2, Real.exp_add] at h2
          have h3 : 1 / B ≤ 203 := by rw [div_le_iff₀ hB0]; linarith
          have h4 : (N : ℝ) * (4 / 10 ^ 6 / B) ≤ N / 1000 := by
            have : 4 / 10 ^ 6 / B ≤ 1 / 1000 := by rw [div_le_iff₀ hB0]; linarith
            have hN' : (0 : ℝ) ≤ N := Nat.cast_nonneg N
            nlinarith
          exact h2.trans (mul_le_mul_of_nonneg_left (mul_le_mul (Real.exp_le_exp.2 h3) (Real.exp_le_exp.2 h4)
            (Real.exp_pos _).le (Real.exp_pos _).le) (by positivity))
        -- (3) the rate
        have hrate := rate_of_log_le hB0 hEx0 hBrate N
        have h2N : (0 : ℝ) < 2 ^ N := by positivity
        have hslT : 0 ≤ slT N := by
          unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
          linarith
        have hslV : 0 ≤ slV N := by unfold slV; positivity
        have hKN := fsK_mul_le (N := N) hN
        have hKN0 := fsK_mul_nonneg (N := N)
        have hlamR : (C.lam : ℝ) ≤ 17 := by exact_mod_cast hlam
        have hluR : lu ≤ 3 := by rw [hludef]; exact_mod_cast hlu
        have htR : t ≤ 11 := by
          have : (C.P : ℝ) ≤ 30 := by exact_mod_cast hP
          rw [ht]; linarith
        have hQN : (Q * (B + 1 / N + 4 / 10 ^ 6)) ^ N =
            Real.exp ((C.lam : ℝ) * (K * N)) * Real.exp (lu * slT N) * (Ex * (B + 1 / N + 4 / 10 ^ 6)) ^ N := by
          rw [hQ, hE, mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
          rw [show (N : ℝ) * ((C.lam : ℝ) * K) = (C.lam : ℝ) * (K * N) by ring,
            show (N : ℝ) * (lu * (slT N / N)) = lu * slT N by field_simp]
          rw [mul_pow]; ring
        have hE1 : Real.exp (t * slT N) * (Real.exp ((C.lam : ℝ) * (K * N)) * Real.exp (lu * slT N)) ≤
            Real.exp (14 * slT N + 17 * (8 + slV N)) := by
          rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.2
          rw [hK]
          have a1 := mul_le_mul_of_nonneg_right htR hslT
          have a2 := mul_le_mul_of_nonneg_right hluR hslT
          have a3 := mul_le_mul hlamR hKN hKN0 (by norm_num : (0 : ℝ) ≤ 17)
          linarith
        have hrate' : Real.exp (t * (x0 * N)) * (B * Ex) ^ N ≤ Real.exp (-((plR : ℝ) * N)) / 2 ^ N := by
          rw [le_div_iff₀ h2N]; linarith [hrate]
        have hEB : (Ex * (B + 1 / N + 4 / 10 ^ 6)) ^ N ≤ (B * Ex) ^ N * (Real.exp 203 * Real.exp (N / 1000)) := by
          rw [mul_pow, mul_pow, mul_comm (B ^ N) (Ex ^ N), mul_assoc]
          exact mul_le_mul_of_nonneg_left hstep2 (by positivity)
        have h207 : 2 * Real.exp 203 ≤ Real.exp 210 := by
          have : (2 : ℝ) ≤ Real.exp 7 := by
            have := Real.add_one_le_exp (7 : ℝ); linarith
          calc 2 * Real.exp 203 ≤ Real.exp 7 * Real.exp 203 := by gcongr
            _ = Real.exp 210 := by rw [← Real.exp_add]; norm_num
        have hR : Real.exp (-((plR : ℝ) * N)) * Real.exp (N / 1000) = Real.exp (-(((plR : ℝ) - 1 / 1000) * N)) := by
          rw [← Real.exp_add]; ring_nf
        calc Real.exp (t * (x0 * N + slT N)) * (Q * (2 * B) * (Q * (B + 1 / N + 4 / 10 ^ 6)) ^ (N - 1))
            ≤ Real.exp (t * (x0 * N + slT N)) * (2 * (Q * (B + 1 / N + 4 / 10 ^ 6)) ^ N) :=
              mul_le_mul_of_nonneg_left hstep1 (Real.exp_pos _).le
          _ = 2 * (Real.exp (t * slT N) * (Real.exp ((C.lam : ℝ) * (K * N)) * Real.exp (lu * slT N))) *
                (Real.exp (t * (x0 * N)) * (Ex * (B + 1 / N + 4 / 10 ^ 6)) ^ N) := by
              rw [hQN, mul_add, Real.exp_add]; ring
          _ ≤ 2 * Real.exp (14 * slT N + 17 * (8 + slV N)) *
                (Real.exp (t * (x0 * N)) * ((B * Ex) ^ N * (Real.exp 203 * Real.exp (N / 1000)))) := by
              gcongr
          _ = (2 * Real.exp 203) * Real.exp (14 * slT N + 17 * (8 + slV N)) *
                ((Real.exp (t * (x0 * N)) * (B * Ex) ^ N) * Real.exp (N / 1000)) := by ring
          _ ≤ Real.exp 210 * Real.exp (14 * slT N + 17 * (8 + slV N)) *
                ((Real.exp (-((plR : ℝ) * N)) / 2 ^ N) * Real.exp (N / 1000)) := by
              gcongr
          _ = _ := by
              rw [show Real.exp (14 * slT N + 17 * (8 + slV N) + 210) =
                Real.exp 210 * Real.exp (14 * slT N + 17 * (8 + slV N)) by rw [← Real.exp_add]; ring_nf, ← hR]
              ring

/-! ### The joint bound -/

/-- The `pairLow` field of `NewX3` with an explicit anchor row (cause side only). -/
def P0PairLow3 (N : ℕ) (_s : State N) : State N → Param N → Fin N → XSide → Prop := fun r0 w x σ =>
  σ = .cause → ∃ j, j ≠ x ∧ 1 / 2 + Real.exp (-((N : ℝ) / 200)) ≤ clamp01 (w r0 j) ∧
    clamp01 (w r0 j) + clamp01 (w (flipAt x r0) j) ≤ 1 - 1 / (N : ℝ)

lemma nl3_eps : ∀ᶠ N : ℕ in atTop, Real.exp (-((N : ℝ) / 200)) ≤ 1 / 10 ^ 7 := by
  filter_upwards [eventually_ge_atTop 4000] with N hN
  have hN' : (4000 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : Real.exp (-((N : ℝ) / 200)) ≤ Real.exp (-20) := Real.exp_le_exp.2 (by linarith)
  have h2 : (10 : ℝ) ^ 7 ≤ Real.exp 20 := by
    have he := Real.exp_one_gt_d9
    have e : Real.exp 20 = Real.exp 1 ^ 20 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc (10 : ℝ) ^ 7 ≤ (27 / 10) ^ 20 := by norm_num
      _ ≤ Real.exp 1 ^ 20 := pow_le_pow_left₀ (by norm_num) (by linarith) 20
  refine h1.trans ?_
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by positivity) h2

/-- **Joint bound for `pairLow3`, PROVED** (rate `plR - 1/1000 = 1.0192 > RJ`). -/
theorem joint_pairLow3 : JointBound P0PairLow3 := by
  have hab := poly_absorb (61 * Real.exp 210) 0 (δ := ((plR : ℝ) - 1 / 1000) - RJ)
    (by unfold plR RJ rsR0; norm_num)
  filter_upwards [hab, nl3_eps, eventually_ge_atTop 15] with N hab hε hN s r0 x σ hfar
  cases σ with
  | effect =>
    have : {w : Param N | RegEvX N s r0 x .effect w ∧ ¬ P0PairLow3 N s r0 w x .effect} = ∅ := by
      ext w; simp [P0PairLow3]
    rw [this, measure_empty]; exact bot_le
  | cause =>
    set SB := Real.exp (-(((plR : ℝ) - 1 / 1000) * N)) *
      Real.exp (14 * slT N + 17 * (8 + slV N) + 210) / 2 ^ N with hSB
    have hSB0 : 0 ≤ SB := by positivity
    have hsub : {w : Param N | RegEvX N s r0 x .cause w ∧ ¬ P0PairLow3 N s r0 w x .cause} ⊆
        ⋃ c ∈ cellsX .cause, ({w | CellEvX N s r0 x .cause c w} ∩ plFail3 N r0 x) := by
      rintro w ⟨⟨c, hc, hcw⟩, hn⟩
      simp only [P0PairLow3, forall_const, not_exists, not_and, not_le] at hn
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
      refine ⟨c, hc, hcw, fun j hj => ?_⟩
      by_cases hb : clamp01 (w r0 j) < 1 / 2 + Real.exp (-((N : ℝ) / 200))
      · exact Or.inr hb
      · exact Or.inl (hn j hj (not_lt.1 hb))
    refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
    calc ∑ c ∈ cellsX .cause, cubeM N ({w | CellEvX N s r0 x .cause c w} ∩ plFail3 N r0 x)
        ≤ ∑ _c ∈ cellsX .cause, ENNReal.ofReal SB := sum_le_sum fun c hc =>
          pl3_cause_cell (by omega) s r0 x (List.mem_toFinset.1 hc) (tf_far_ne2 (by omega) hfar)
            (tf_far_ne1 (by omega) hfar x) hε
      _ ≤ (61 : ENNReal) * ENNReal.ofReal SB := by
          rw [sum_const, nsmul_eq_mul]; gcongr; exact_mod_cast tf_cells_card .cause
      _ = ENNReal.ofReal (61 * SB) := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hsl := rs_slack_le N
          have hslT : 0 ≤ slT N := by
            unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
            linarith
          have h2N : (0 : ℝ) < 2 ^ N := by positivity
          set δ : ℝ := ((plR : ℝ) - 1 / 1000) - RJ with hδ
          have hk : 61 * Real.exp 210 * Real.exp (14 * slT N + 17 * (8 + slV N)) ≤ Real.exp (δ * N) := by
            refine le_trans ?_ hab
            simp only [pow_zero, mul_one]
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)
          have e : 61 * SB = (61 * Real.exp 210 * Real.exp (14 * slT N + 17 * (8 + slV N))) *
              (Real.exp (-(δ * N)) * Real.exp (-(RJ * N))) / 2 ^ N := by
            rw [hSB, show Real.exp (14 * slT N + 17 * (8 + slV N) + 210) =
              Real.exp 210 * Real.exp (14 * slT N + 17 * (8 + slV N)) by rw [← Real.exp_add]; ring_nf,
              show Real.exp (-(((plR : ℝ) - 1 / 1000) * N)) = Real.exp (-(δ * N)) * Real.exp (-(RJ * N)) by
                rw [← Real.exp_add, hδ]; ring_nf]
            ring
          rw [e, div_le_div_iff_of_pos_right h2N]
          have hy : Real.exp (δ * N) * Real.exp (-(δ * N)) = 1 := by
            rw [← Real.exp_add]; simp
          calc (61 * Real.exp 210 * Real.exp (14 * slT N + 17 * (8 + slV N))) *
                (Real.exp (-(δ * N)) * Real.exp (-(RJ * N)))
              ≤ Real.exp (δ * N) * (Real.exp (-(δ * N)) * Real.exp (-(RJ * N))) := by gcongr
            _ = Real.exp (-(RJ * N)) := by rw [← mul_assoc, hy, one_mul]

end Census
end IIT

#print axioms IIT.Census.pl3_cause_cell
#print axioms IIT.Census.joint_pairLow3
