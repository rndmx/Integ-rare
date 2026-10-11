/-
Census, B1 forced leaf 18 (agent "forcedF"): per-pair bounds for two failing units.

`TFB N = e^{-1.03 N} e^{30 slT + 40 (8 + slV) + 10} / 2^N` bounds `P(CellEvX(x, σ, c) ∩ CellEvX(x', σ', c'))`:
* `tf_mixed` (`σ ≠ σ'`): from the Lemma RS certificates of both cells (rate `2 R0 + log(9/8) - log 2 ≥ 1.43`);
* `tf_cc`, `tf_ee` (`σ = σ'`): from the two-failure records (`tfRT = 1.03`).
-/
import IIT.Census.B1ForcedFTwo
import IIT.Census.B1ForcedFTwoSound
import IIT.Census.B1ForcedFTwoCertC
import IIT.Census.B1ForcedFTwoCertE

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- The common per-pair bound. -/
noncomputable def TFB (N : ℕ) : ℝ :=
  Real.exp (-((103 / 100 : ℝ) * N)) * Real.exp (30 * slT N + 40 * (8 + slV N) + 10) / 2 ^ N

lemma TFB_nonneg (N : ℕ) : 0 ≤ TFB N := by unfold TFB; positivity

/-- **The common final arithmetic.** -/
lemma tf_final (hN : 1 ≤ N) {t a b I Rr κ : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 16) (ha0 : 0 ≤ a) (ha : a ≤ 40)
    (hb0 : 0 ≤ b) (hb : b ≤ 10) (hI : 0 ≤ I) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 10)
    (hrate : Real.exp (t * x0) * I ≤ Real.exp (-Rr)) (hRr : 103 / 100 + Real.log 2 ≤ Rr) :
    Real.exp (t * (x0 * N + slT N)) *
      (Real.exp (a * fsK N) * Real.exp (b * (slT N / N)) * I * (1 + κ * deltaU N)) ^ N ≤ TFB N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ0 : 0 ≤ deltaU N := by unfold deltaU; positivity
  have hδN : deltaU N * N ≤ 1 := by
    unfold deltaU; rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  have hslT : 0 ≤ slT N := by
    unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    linarith
  have hKN := fsK_mul_le hN
  have hKN0 := fsK_mul_nonneg (N := N)
  have e1 : (Real.exp (a * fsK N) * Real.exp (b * (slT N / N)) * I * (1 + κ * deltaU N)) ^ N =
      Real.exp (a * (fsK N * N)) * Real.exp (b * slT N) * I ^ N * (1 + κ * deltaU N) ^ N := by
    rw [mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 3
    · ring
    · field_simp
  have h2 : (1 + κ * deltaU N) ^ N ≤ Real.exp 10 := by
    calc (1 + κ * deltaU N) ^ N ≤ Real.exp (κ * deltaU N) ^ N := by
          gcongr; linarith [Real.add_one_le_exp (κ * deltaU N)]
      _ = Real.exp (κ * (deltaU N * N)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp 10 := Real.exp_le_exp.2 (by nlinarith)
  have h3 : Real.exp (t * (x0 * N)) * I ^ N ≤ Real.exp (-(Rr * N)) := by
    have := pow_le_pow_left₀ (by positivity) hrate N
    calc Real.exp (t * (x0 * N)) * I ^ N = (Real.exp (t * x0) * I) ^ N := by
          rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-Rr) ^ N := this
      _ = Real.exp (-(Rr * N)) := by rw [← Real.exp_nat_mul]; ring_nf
  have h4 : Real.exp (-(Rr * N)) ≤ Real.exp (-((103 / 100 : ℝ) * N)) / 2 ^ N := by
    rw [le_div_iff₀ (by positivity)]
    have : (2 : ℝ) ^ N = Real.exp (Real.log 2 * N) := by
      rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_nat_mul]; ring_nf
      rw [Real.exp_log (by norm_num)]
    rw [this, ← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
  have h5 : Real.exp (t * slT N) * (Real.exp (a * (fsK N * N)) * Real.exp (b * slT N)) ≤
      Real.exp (30 * slT N + 40 * (8 + slV N)) := by
    rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
  rw [e1]
  have hIN : 0 ≤ I ^ N := pow_nonneg hI N
  calc Real.exp (t * (x0 * N + slT N)) *
        (Real.exp (a * (fsK N * N)) * Real.exp (b * slT N) * I ^ N * (1 + κ * deltaU N) ^ N)
      = (Real.exp (t * (x0 * N)) * I ^ N) *
          (Real.exp (t * slT N) * (Real.exp (a * (fsK N * N)) * Real.exp (b * slT N))) *
            (1 + κ * deltaU N) ^ N := by rw [mul_add, Real.exp_add]; ring
    _ ≤ (Real.exp (-((103 / 100 : ℝ) * N)) / 2 ^ N) * Real.exp (30 * slT N + 40 * (8 + slV N)) *
          Real.exp 10 := by
        gcongr
        · exact h3.trans h4
    _ = TFB N := by unfold TFB; rw [Real.exp_add (30 * slT N + 40 * (8 + slV N)) 10]; ring

/-- Splitting the four-fold column integral of a product. -/
lemma lint4_split (Wa Wc : Set ℝ) (F1 F2 : ℝ → ENNReal) (G1 G2 : ℝ → ℝ → ENNReal)
    (hF1 : Measurable F1) (hF2 : Measurable F2) (hG1 : Measurable fun p : ℝ × ℝ => G1 p.1 p.2)
    (hG2 : Measurable fun p : ℝ × ℝ => G2 p.1 p.2) :
    ∫⁻ y in Wa, ∫⁻ u, ∫⁻ z in Wc, ∫⁻ v, F1 y * G1 y u * (F2 z * G2 z v) ∂unif ∂unif ∂unif ∂unif =
      (∫⁻ y in Wa, F1 y * ∫⁻ u, G1 y u ∂unif ∂unif) * (∫⁻ z in Wc, F2 z * ∫⁻ v, G2 z v ∂unif ∂unif) := by
  have hG2v : ∀ z, Measurable fun v => G2 z v := fun z => hG2.comp (measurable_const.prodMk measurable_id)
  have hG1u : ∀ y, Measurable fun u => G1 y u := fun y => hG1.comp (measurable_const.prodMk measurable_id)
  have hQ : Measurable fun z => F2 z * ∫⁻ v, G2 z v ∂unif := hF2.mul hG2.lintegral_prod_right'
  have hP : Measurable fun y => F1 y * ∫⁻ u, G1 y u ∂unif := hF1.mul hG1.lintegral_prod_right'
  set Q := ∫⁻ z in Wc, F2 z * ∫⁻ v, G2 z v ∂unif ∂unif with hQdef
  have step1 : ∀ y u, ∫⁻ z in Wc, ∫⁻ v, F1 y * G1 y u * (F2 z * G2 z v) ∂unif ∂unif = F1 y * G1 y u * Q := by
    intro y u
    have : ∀ z, ∫⁻ v, F1 y * G1 y u * (F2 z * G2 z v) ∂unif = F1 y * G1 y u * (F2 z * ∫⁻ v, G2 z v ∂unif) := by
      intro z
      rw [lintegral_const_mul _ ((hG2v z).const_mul _), lintegral_const_mul _ (hG2v z)]
    simp_rw [this]
    rw [lintegral_const_mul _ hQ]
  simp_rw [step1]
  have step2 : ∀ y, ∫⁻ u, F1 y * G1 y u * Q ∂unif = F1 y * (∫⁻ u, G1 y u ∂unif) * Q := by
    intro y
    rw [lintegral_mul_const _ ((hG1u y).const_mul _), lintegral_const_mul _ (hG1u y)]
  simp_rw [step2]
  rw [lintegral_mul_const _ hP]

/-- The certified partner of a cause cell, unpacked (with the monotone covering cell). -/
lemma fs_cause_partner (hN0 : 0 < N) {c : ℚ × ℚ} (hc : c ∈ cellsXCauseData) :
    ∃ C ∈ rsCellsC, rsCellOK C = true ∧ C.lam ≤ 17 ∧ C.lu ≤ 3 ∧ C.P ≤ 30 ∧
      (∀ (s r0 : State N) (x : Fin N), {w : Param N | CellEvX N s r0 x .cause c w} ⊆
        {w | CellEvX N s r0 x .cause (C.v ^ 4, C.w ^ 4) w}) ∧
      (1 : ℝ) / 2 ≤ (((C.v ^ 4, C.w ^ 4) : ℚ × ℚ).2 : ℝ) ∧ (0 : ℝ) < (((C.v ^ 4, C.w ^ 4) : ℚ × ℚ).1 : ℝ) ∧
      (((C.v ^ 4, C.w ^ 4) : ℚ × ℚ).1 : ℝ) ≤ 1 := by
  have hall := rsLink_all
  rw [List.all_eq_true] at hall
  obtain ⟨C, hC, hlink⟩ := List.any_eq_true.1 (hall c hc)
  have hok : rsCellOK C = true := (List.all_eq_true.1 rsCellsC_ok) C hC
  have hb := (List.all_eq_true.1 rsBounds) C hC
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨hlam, hlu⟩, hP⟩ := hb
  simp only [rsLink, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hlink
  obtain ⟨⟨hv4, hcap⟩, hc2⟩ := hlink
  have hok' := hok
  simp only [rsCellOK, Bool.and_eq_true, decide_eq_true_eq] at hok'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hvw⟩, hw1⟩, hv1⟩, hw2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok'
  refine ⟨C, hC, hok, hlam, hlu, hP, fun s r0 x => ?_, ?_, ?_, ?_⟩
  · exact cellEvX_mono hN0 s r0 x (by exact_mod_cast hv4)
      (by
        rcases hcap with h | h
        · left; exact_mod_cast h
        · right; simp only [h]; norm_num)
      (by exact_mod_cast hc2) (by push_cast; exact pow_pos (by exact_mod_cast (lt_of_lt_of_le hv hvw)) 4)
  · have := (Rat.cast_le (K := ℝ)).2 hw2; push_cast at this ⊢; exact this
  · push_cast; exact pow_pos (by exact_mod_cast hv) 4
  · push_cast; exact pow_le_one₀ (by exact_mod_cast hv.le) (by exact_mod_cast hv1.le)

lemma fs_gXev_meas (c : ℚ × ℚ) : Measurable fun p : ℝ × ℝ => gXev N c p.1 p.2 := by
  unfold gXev
  have hy : Measurable fun p : ℝ × ℝ => clamp01 p.1 := clamp01_measurable.comp measurable_fst
  have hu : Measurable fun p : ℝ × ℝ => clamp01 p.2 := clamp01_measurable.comp measurable_snd
  refine (Measurable.min ?_ ?_).sub_const _
  · exact Real.measurable_log.comp ((measurable_const.mul hy).div (hy.add hu))
  · exact (measurable_const.max (Real.measurable_log.comp (hy.div_const _))).sub_const _

lemma fs_ellUX_eq_ellSX (y : ℝ) : ellUX N y = ellSX N y := rfl

/-- **Two failing units on opposite sides** (`cause` at `xc`, `effect` at `xe`). -/
theorem tf_mixed (hN : 2 ≤ N) (hδ : deltaU N < 1 / 2) (s r0 : State N) (xc xe : Fin N) {cc ce : ℚ × ℚ}
    (hcc : cc ∈ cellsXCauseData) (hce : ce ∈ cellsXEffectData)
    (h1 : r0 ≠ s) (h2 : r0 ≠ flipAt xe s) (h3 : flipAt xc r0 ≠ s) (h4 : flipAt xc r0 ≠ flipAt xe s) :
    cubeM N ({w | CellEvX N s r0 xc .cause cc w} ∩ {w | CellEvX N s r0 xe .effect ce w}) ≤
      ENNReal.ofReal (TFB N) := by
  have hN0 : 0 < N := by omega
  obtain ⟨C, hC, hok, hlam, hlu, hP, hmono1, hcm1, hm0, hm1⟩ := fs_cause_partner hN0 hcc
  obtain ⟨C', hC', hok', hlam', hlu', hP', hv', hv1', hw4', hb', hcap', hc2'⟩ := fs_eff_partner hce
  set c1 : ℚ × ℚ := (C.v ^ 4, C.w ^ 4) with hc1
  set c2 : ℚ × ℚ := (ce.1, C'.w ^ 4) with hc2
  have hc22 : (c2.2 : ℝ) = (C'.w : ℝ) ^ 4 := by simp only [hc2]; push_cast; rfl
  have hcm2 : (1 : ℝ) / 2 ≤ (c2.2 : ℝ) := by rw [hc22]; exact hw4'
  have hmono2 := cellEvX_mono_eff s r0 xe (c := ce) (c' := c2) (by simp only [hc2])
    (by rw [hc22]; exact hcap') (by linarith) (by linarith)
  have hsubC := cellEvX_sub_template hN0 s r0 xc c1 hcm1
  have hsubE := cellEvX_eff_sub_template hN0 s r0 xe c2 hcm2 hδ
  set P1 : ℝ := (C.P : ℝ) / 4 with hP1
  set P2 : ℝ := (C'.P : ℝ) / 4 with hP2
  have hP10 : 0 ≤ P1 := by positivity
  have hP20 : 0 ≤ P2 := by positivity
  set t : ℝ := P1 + P2 with ht
  set Wa : Set ℝ := {y : ℝ | (c1.1 : ℝ) ≤ clamp01 y} with hWa
  set Wc : Set ℝ := {y : ℝ | (c2.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} with hWc
  have hWam : MeasurableSet Wa := measurableSet_le measurable_const clamp01_measurable
  have hWcm : MeasurableSet Wc :=
    measurableSet_le measurable_const (clamp01_measurable.max (measurable_const.sub clamp01_measurable))
  set f : Fin 4 → Fin N → (ℝ × ℝ) × (ℝ × ℝ) → ℝ :=
    ![fun _ p => -Real.log (clamp01 p.1.1), fun _ p => ellSX N p.2.1 - -Real.log (clamp01 p.1.1),
      fun _ p => gXev N c1 p.1.1 p.1.2, fun _ p => gXevE N c2 p.2.1 p.2.2] with hf
  have hell : Measurable fun y : ℝ => -Real.log (clamp01 y) :=
    (Real.measurable_log.comp clamp01_measurable).neg
  have hfm : ∀ k i, Measurable (f k i) := by
    intro k i
    fin_cases k
    · exact hell.comp (measurable_fst.comp measurable_fst)
    · exact (fs_ellSX_meas.comp (measurable_fst.comp measurable_snd)).sub (hell.comp (measurable_fst.comp measurable_fst))
    · exact (fs_gXev_meas c1).comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst))
    · exact (fs_gE_meas c2).comp ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))
  set a : Fin 4 → ℝ := ![x0 * N + slT N, 0, 0, 0] with ha
  set tt : Fin 4 → ℝ := ![t, P2, (C.lam : ℝ), (C'.lam : ℝ)] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 4)), 0 ≤ tt k := by
    intro k _; fin_cases k
    · simp only [htt]; simp; positivity
    · simpa [htt] using hP20
    · simp [htt]
    · simp [htt]
  have hmain := cubeM_chernoff_four (fun _ => r0) (fun _ => flipAt xc r0) (fun _ => s) (fun _ => flipAt xe s)
    (fun _ => (flipAt_ne xc r0).symm) (fun _ => h1) (fun _ => h2) (fun _ => h3) (fun _ => h4)
    (fun _ => (flipAt_ne xe s).symm) univ f hfm a tt htt0 (fun _ => Wa) (fun _ => Wc) (fun _ => hWam) (fun _ => hWcm)
  have hsub : ({w | CellEvX N s r0 xc .cause cc w} ∩ {w | CellEvX N s r0 xe .effect ce w} : Set (Param N)) ⊆
      {w | (∀ i, w ((fun _ : Fin N => r0) i) i ∈ (fun _ : Fin N => Wa) i ∧
          w ((fun _ : Fin N => s) i) i ∈ (fun _ : Fin N => Wc) i) ∧
        ∀ k ∈ (univ : Finset (Fin 4)), ∑ i, f k i ((w ((fun _ : Fin N => r0) i) i,
          w ((fun _ : Fin N => flipAt xc r0) i) i), (w ((fun _ : Fin N => s) i) i,
            w ((fun _ : Fin N => flipAt xe s) i) i)) ≤ a k} := by
    rintro w ⟨hw1, hw2⟩
    obtain ⟨hW1, hT, hL, hV⟩ := hsubC (hmono1 s r0 xc hw1)
    obtain ⟨hW2, -, -, hV', -⟩ := hsubE (hmono2 hw2)
    refine ⟨fun i => ⟨hW1 i, hW2 i⟩, fun k _ => ?_⟩
    fin_cases k
    · simpa [hf, ha] using hT
    · simp only [hf, ha]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [sum_sub_distrib]
      have : ∑ i, ellSX N (w s i) = ∑ i, ellUX N (w s i) := rfl
      rw [this]; linarith
    · simpa [hf, ha] using hV
    · simpa [hf, ha] using hV'
  -- the column factor
  set K := fsK N with hK
  set I1 := fsI C with hI1
  set I2 := fsI C' with hI2
  set J : ℝ := (Real.exp ((C.lam : ℝ) * K) * I1) *
    (Real.exp (P2 * (slT N / N)) * Real.exp ((C'.lam : ℝ) * K) * (2 * I2)) with hJ
  have hI10 := fs_cell_pos C hok
  have hI20 := fs_cell_pos C' hok'
  have hJ0 : 0 ≤ J := by positivity
  have hcol : ∀ i : Fin N, ∫⁻ y in (fun _ : Fin N => Wa) i, ∫⁻ u, ∫⁻ z in (fun _ : Fin N => Wc) i, ∫⁻ v,
      ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)), tt k * f k i ((y, u), (z, v))))
        ∂unif ∂unif ∂unif ∂unif ≤ ENNReal.ofReal J := by
    intro i
    have hpt : ∀ y u z v, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)), tt k * f k i ((y, u), (z, v)))) =
        ENNReal.ofReal (Real.exp ((P2 - t) * -Real.log (clamp01 y))) *
          ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXev N c1 y u)) *
          (ENNReal.ofReal (Real.exp (-P2 * ellSX N z)) *
            ENNReal.ofReal (Real.exp (-(C'.lam : ℝ) * gXevE N c2 z v))) := by
      intro y u z v
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 2
      simp [Fin.sum_univ_four, hf, htt]
      ring
    simp_rw [hpt]
    have m1 : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp ((P2 - t) * -Real.log (clamp01 y))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hell.const_mul _))
    have m2 : Measurable fun z : ℝ => ENNReal.ofReal (Real.exp (-P2 * ellSX N z)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (fs_ellSX_meas.const_mul _))
    have m3 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXev N c1 p.1 p.2)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((fs_gXev_meas c1).const_mul _))
    have m4 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(C'.lam : ℝ) * gXevE N c2 p.1 p.2)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((fs_gE_meas c2).const_mul _))
    rw [lint4_split Wa Wc (fun y => ENNReal.ofReal (Real.exp ((P2 - t) * -Real.log (clamp01 y))))
      (fun z => ENNReal.ofReal (Real.exp (-P2 * ellSX N z)))
      (fun y u => ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXev N c1 y u)))
      (fun z v => ENNReal.ofReal (Real.exp (-(C'.lam : ℝ) * gXevE N c2 z v))) m1 m2 m3 m4]
    have hJ1 := cell_J_le (N := N) C.lam c1 hcm1 hm0 hm1 (t := t) (lamU := P2) (by rw [ht]; linarith)
    have hb0 : (0 : ℝ) < (C'.v : ℝ) ^ 4 := by positivity
    have hb1 : (C'.v : ℝ) ^ 4 ≤ 1 := pow_le_one₀ hv'.le hv1'.le
    have hJ2 := s_factor_le (N := N) C'.lam c2 hcm2 hP20 hb0 (by simpa [hc2] using hb') hb1
    have e1 : (∫ y in (c1.1 : ℝ)..1, y ^ (t - P2) * gX C.lam (c1.2 : ℝ) y) = I1 := by
      simp only [hc1, ht, add_sub_cancel_right, hI1, fsI, hP1]; push_cast; rfl
    have e2 : (∫ X in (C'.v : ℝ) ^ 4..1, X ^ P2 * gX C'.lam (c2.2 : ℝ) X) = I2 := by
      rw [hc22]; simp only [hI2, fsI, hP2]
    rw [e1] at hJ1; rw [e2] at hJ2
    calc _ ≤ ENNReal.ofReal (Real.exp ((C.lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) * I1) *
          ENNReal.ofReal (Real.exp (P2 * (slT N / N)) *
            Real.exp ((C'.lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) * (2 * I2)) :=
          mul_le_mul' hJ1 hJ2
      _ = ENNReal.ofReal J := by
          rw [← ENNReal.ofReal_mul (by positivity)]; rfl
  refine (measure_mono hsub).trans (hmain.trans ?_)
  have hsum : ∑ k ∈ (univ : Finset (Fin 4)), tt k * a k = t * (x0 * N + slT N) := by
    simp [Fin.sum_univ_four, htt, ha]
  rw [hsum]
  calc ENNReal.ofReal (Real.exp (t * (x0 * N + slT N))) * ∏ i : Fin N, ∫⁻ y in (fun _ : Fin N => Wa) i,
        ∫⁻ u, ∫⁻ z in (fun _ : Fin N => Wc) i, ∫⁻ v,
          ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)), tt k * f k i ((y, u), (z, v))))
            ∂unif ∂unif ∂unif ∂unif
      ≤ ENNReal.ofReal (Real.exp (t * (x0 * N + slT N))) * ∏ _i : Fin N, ENNReal.ofReal J := by
        gcongr with i; exact hcol i
    _ = ENNReal.ofReal (Real.exp (t * (x0 * N + slT N)) * J ^ N) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow hJ0,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ ENNReal.ofReal (TFB N) := by
        apply ENNReal.ofReal_le_ofReal
        have hJe : J = Real.exp (((C.lam : ℝ) + C'.lam) * fsK N) * Real.exp (P2 * (slT N / N)) *
            (2 * I1 * I2) * (1 + 0 * deltaU N) := by
          rw [hJ, hK, add_mul, Real.exp_add]; ring
        rw [hJe]
        have hr1 := fs_cell_rate C hok hlu
        have hs2 := rsCell_sound C' hok'
        have ht2 := rsEx_tilt_ge C'.lu hlu'
        have hl2 := Real.log_two_lt_d9
        have hx := x0_gt
        have hl32 := log_three_halves_eq
        refine tf_final (by omega) (by positivity) (by
            have : (C.P : ℝ) ≤ 30 := by exact_mod_cast hP
            have : (C'.P : ℝ) ≤ 30 := by exact_mod_cast hP'
            rw [ht, hP1, hP2]; linarith) (by positivity) (by
            have : (C.lam : ℝ) ≤ 17 := by exact_mod_cast hlam
            have : (C'.lam : ℝ) ≤ 17 := by exact_mod_cast hlam'
            linarith) hP20 (by
            have : (C'.P : ℝ) ≤ 30 := by exact_mod_cast hP'
            rw [hP2]; linarith) (by positivity) le_rfl (by norm_num)
          (Rr := 2 * (rsR0 : ℝ) + Real.log (3 / 2) + Real.log (3 / 4)) ?_ ?_
        · -- the rate
          rw [← Real.exp_log (show 0 < 2 * I1 * I2 by positivity), ← Real.exp_add]
          apply Real.exp_le_exp.2
          rw [Real.log_mul (by positivity) hI20.ne', Real.log_mul (by norm_num) hI10.ne']
          have hfsI : fsI C' = ∫ y in ((C'.v : ℝ) ^ 4)..1, y ^ ((C'.P : ℝ) / 4) * gX C'.lam ((C'.w : ℝ) ^ 4) y := rfl
          rw [← hfsI] at hs2
          simp only [ht, hP1, hP2]
          nlinarith
        · have : Real.log (3 / 4) = Real.log (3 / 2) - Real.log 2 := by
            rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
          rw [this, hl32]; unfold rsR0; push_cast; nlinarith

/-! ### Same side: helpers -/

/-- Splitting the four-fold column integral when the fourth entry pairs with the first. -/
lemma lint4_split2 (Wa Wc : Set ℝ) (A B : ℝ → ENNReal) (G H : ℝ → ℝ → ENNReal)
    (hA : Measurable A) (hB : Measurable B) (hG : Measurable fun p : ℝ × ℝ => G p.1 p.2)
    (hH : Measurable fun p : ℝ × ℝ => H p.1 p.2) :
    ∫⁻ a in Wa, ∫⁻ u, ∫⁻ b in Wc, ∫⁻ v, A a * G a u * (B b * H a v) ∂unif ∂unif ∂unif ∂unif =
      (∫⁻ b in Wc, B b ∂unif) * ∫⁻ a in Wa, A a * (∫⁻ u, G a u ∂unif) * (∫⁻ v, H a v ∂unif) ∂unif := by
  have hHv : ∀ a, Measurable fun v => H a v := fun a => hH.comp (measurable_const.prodMk measurable_id)
  have hGu : ∀ a, Measurable fun u => G a u := fun a => hG.comp (measurable_const.prodMk measurable_id)
  have step1 : ∀ a u, ∫⁻ b in Wc, ∫⁻ v, A a * G a u * (B b * H a v) ∂unif ∂unif =
      A a * G a u * (∫⁻ v, H a v ∂unif) * ∫⁻ b in Wc, B b ∂unif := by
    intro a u
    have : ∀ b, ∫⁻ v, A a * G a u * (B b * H a v) ∂unif = A a * G a u * (∫⁻ v, H a v ∂unif) * B b := by
      intro b
      rw [lintegral_const_mul _ ((hHv a).const_mul _), lintegral_const_mul _ (hHv a)]; ring
    simp_rw [this]
    rw [lintegral_const_mul _ hB]
  simp_rw [step1]
  have step2 : ∀ a, ∫⁻ u, A a * G a u * (∫⁻ v, H a v ∂unif) * ∫⁻ b in Wc, B b ∂unif ∂unif =
      (∫⁻ b in Wc, B b ∂unif) * (A a * (∫⁻ u, G a u ∂unif) * (∫⁻ v, H a v ∂unif)) := by
    intro a
    rw [lintegral_mul_const _ (((hGu a).const_mul _).mul_const _), lintegral_mul_const _ ((hGu a).const_mul _),
      lintegral_const_mul _ (hGu a)]; ring
  simp_rw [step2]
  have hm : Measurable fun a => A a * (∫⁻ u, G a u ∂unif) * (∫⁻ v, H a v ∂unif) :=
    (hA.mul hG.lintegral_prod_right').mul hH.lintegral_prod_right'
  rw [lintegral_const_mul _ hm]

/-- **Cause side, the row-`r0` factor with two V-functionals.** -/
lemma tf_J_cc (lam lam2 : ℕ) (c1 c2 : ℚ × ℚ) (hcm1 : (1 : ℝ) / 2 ≤ c1.2) (hcm2 : (1 : ℝ) / 2 ≤ c2.2)
    (hm0 : (0 : ℝ) < c1.1) (hm1 : (c1.1 : ℝ) ≤ 1) {t lamU : ℝ} (hp : lamU ≤ t) :
    ∫⁻ y in {y : ℝ | (c1.1 : ℝ) ≤ clamp01 y},
        ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
          (∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c1 y u)) ∂unif) *
          (∫⁻ v, ENNReal.ofReal (Real.exp (-(lam2 : ℝ) * gXev N c2 y v)) ∂unif) ∂unif ≤
      ENNReal.ofReal (Real.exp ((lam : ℝ) * fsK N) * Real.exp ((lam2 : ℝ) * fsK N) *
        ∫ y in (c1.1 : ℝ)..1, y ^ (t - lamU) * gX lam (c1.2 : ℝ) y * GhR lam2 (c2.2 : ℝ) y) := by
  set a : ℝ := (c1.1 : ℝ)
  set E := Real.exp ((lam : ℝ) * fsK N) * Real.exp ((lam2 : ℝ) * fsK N) with hE
  have hset : {y : ℝ | a ≤ clamp01 y} ∩ Set.Icc 0 1 = Set.Icc a 1 := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc]
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
  have hcont : ContinuousOn (fun y => E * (y ^ (t - lamU) * gX lam (c1.2 : ℝ) y * GhR lam2 (c2.2 : ℝ) y))
      (Set.Icc a 1) :=
    continuousOn_const.mul (((ContinuousOn.rpow_const continuousOn_id fun y _ =>
      Or.inr (sub_nonneg.2 hp)).mul (gX_continuousOn lam _ hm0)).mul (GhR_continuousOn lam2 _ hm0))
  unfold unif
  rw [Measure.restrict_restrict hW, hset]
  calc ∫⁻ y in Set.Icc a 1, ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y))) *
          (∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c1 y u)) ∂volume.restrict (Set.Icc 0 1)) *
          (∫⁻ v, ENNReal.ofReal (Real.exp (-(lam2 : ℝ) * gXev N c2 y v)) ∂volume.restrict (Set.Icc 0 1))
      ≤ ∫⁻ y in Set.Icc a 1, ENNReal.ofReal (E * (y ^ (t - lamU) * gX lam (c1.2 : ℝ) y * GhR lam2 (c2.2 : ℝ) y)) := by
        refine setLIntegral_mono' measurableSet_Icc fun y hy => ?_
        have hy0 : 0 < y := lt_of_lt_of_le hm0 hy.1
        have hcy : clamp01 y = y := by
          unfold clamp01; rw [min_eq_right hy.2, max_eq_right hy0.le]
        have hin1 := inner_mgf_le (N := N) lam c1 hcm1 (y := y) (by rw [hcy]; exact hy0)
        have hin2 := inner_mgf_le (N := N) lam2 c2 hcm2 (y := y) (by rw [hcy]; exact hy0)
        unfold unif at hin1 hin2
        rw [hcy] at hin1 hin2 ⊢
        have hexp : Real.exp ((lamU - t) * -Real.log y) = y ^ (t - lamU) := by
          rw [Real.rpow_def_of_pos hy0]; ring_nf
        rw [hexp]
        have hg1 := gX_nonneg lam hy0 hy.2 (show (0 : ℝ) < c1.2 by linarith) (by linarith [hy.2])
        have hg2 := gX_nonneg lam2 hy0 hy.2 (show (0 : ℝ) < c2.2 by linarith) (by linarith [hy.2])
        have hG := gX_le_GhR lam2 hy0 hcm2
        calc ENNReal.ofReal (y ^ (t - lamU)) *
              (∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXev N c1 y u)) ∂volume.restrict (Set.Icc 0 1)) *
              (∫⁻ v, ENNReal.ofReal (Real.exp (-(lam2 : ℝ) * gXev N c2 y v)) ∂volume.restrict (Set.Icc 0 1))
            ≤ ENNReal.ofReal (y ^ (t - lamU)) *
                ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
                  gX lam (c1.2 : ℝ) y) *
                ENNReal.ofReal (Real.exp ((lam2 : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
                  GhR lam2 (c2.2 : ℝ) y) := by
              gcongr
              exact hin2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hG (Real.exp_pos _).le))
          _ = _ := by
              rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy0.le _), ← ENNReal.ofReal_mul (by positivity)]
              congr 1; simp only [hE, fsK]; ring
    _ = ENNReal.ofReal (∫ y in Set.Icc a 1, E * (y ^ (t - lamU) * gX lam (c1.2 : ℝ) y * GhR lam2 (c2.2 : ℝ) y)) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)]
        refine Filter.eventually_of_mem (ae_restrict_mem measurableSet_Icc) fun y hy => ?_
        have hy0 : 0 < y := lt_of_lt_of_le hm0 hy.1
        have hg1 := gX_nonneg lam hy0 hy.2 (show (0 : ℝ) < c1.2 by linarith) (by linarith [hy.2])
        have hg2 := gX_nonneg lam2 hy0 hy.2 (show (0 : ℝ) < c2.2 by linarith) (by linarith [hy.2])
        have hG := gX_le_GhR lam2 hy0 hcm2
        exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (Real.rpow_nonneg hy0.le _) hg1) (hg2.trans hG))
    _ = _ := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hm1,
          intervalIntegral.integral_const_mul]

/-- **Effect side, the row-`s` factor with two V-functionals** (reflection at `1/2`). -/
lemma tf_s_factor2 (lam lam2 : ℕ) (c1 c2 : ℚ × ℚ) (hcm1 : (1 : ℝ) / 2 ≤ c1.2) (hcm2 : (1 : ℝ) / 2 ≤ c2.2)
    {lu : ℝ} (hlu : 0 ≤ lu) {b : ℝ} (hb0 : 0 < b) (hb : b ≤ max (1 / 2) (c1.1 : ℝ)) (hb1 : b ≤ 1) :
    ∫⁻ y in {y : ℝ | (c1.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)},
        ENNReal.ofReal (Real.exp (-lu * ellSX N y)) *
          (∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c1 y u)) ∂unif) *
          (∫⁻ v, ENNReal.ofReal (Real.exp (-(lam2 : ℝ) * gXevE N c2 y v)) ∂unif) ∂unif ≤
      ENNReal.ofReal (Real.exp (lu * (slT N / N)) * Real.exp ((lam : ℝ) * fsK N) * Real.exp ((lam2 : ℝ) * fsK N) *
        (2 * ∫ X in b..1, X ^ lu * gX lam (c1.2 : ℝ) X * GhR lam2 (c2.2 : ℝ) X)) := by
  set C := Real.exp (lu * (slT N / N)) * Real.exp ((lam : ℝ) * fsK N) * Real.exp ((lam2 : ℝ) * fsK N) with hCdef
  have hC : 0 < C := by positivity
  set G : ℝ → ENNReal := Set.indicator (Set.Ici b)
    fun X => ENNReal.ofReal (C * (X ^ lu * gX lam (c1.2 : ℝ) X * GhR lam2 (c2.2 : ℝ) X)) with hGdef
  have hGm : Measurable G := by
    refine Measurable.indicator ?_ measurableSet_Ici
    refine ENNReal.measurable_ofReal.comp (measurable_const.mul
      (((measurable_id.pow_const lu).mul (gX_measurable lam _)).mul ?_))
    unfold GhR binS
    refine Measurable.sub (Measurable.add ?_ ?_) ?_
    · exact (Finset.measurable_sum _ fun k _ => measurable_const.mul (measurable_id.pow_const k)).div
        (measurable_const.mul (measurable_id.pow_const _))
    · exact measurable_const.div (measurable_id.pow_const _)
    · exact (measurable_const.mul measurable_id).div (measurable_id.pow_const _)
  set Xf : ℝ → ℝ := fun y => max (clamp01 y) (1 - clamp01 y)
  have hW : MeasurableSet {y : ℝ | (c1.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} :=
    measurableSet_le measurable_const (clamp01_measurable.max (measurable_const.sub clamp01_measurable))
  have hpt : ∀ y ∈ {y : ℝ | (c1.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} ∩ Set.Icc 0 1,
      ENNReal.ofReal (Real.exp (-lu * ellSX N y)) *
        (∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c1 y u)) ∂unif) *
        (∫⁻ v, ENNReal.ofReal (Real.exp (-(lam2 : ℝ) * gXevE N c2 y v)) ∂unif) ≤ G (Xf y) := by
    rintro y ⟨hyW, hy⟩
    obtain ⟨hX12, hX1⟩ := fs_X_bounds y
    have hX0 : 0 < Xf y := lt_of_lt_of_le (by norm_num) hX12
    have hXb : b ≤ Xf y := hb.trans (max_le hX12 hyW)
    simp only [G, Set.indicator_of_mem (show Xf y ∈ Set.Ici b from hXb)]
    have he : Real.exp (-lu * ellSX N y) = Real.exp (lu * (slT N / N)) * Xf y ^ lu := by
      unfold ellSX; rw [Real.rpow_def_of_pos hX0, ← Real.exp_add]; congr 1; simp only [Xf]; ring
    rw [he]
    have hin1 := inner_mgf_le_eff (N := N) lam c1 hcm1 y
    have hin2 := inner_mgf_le_eff (N := N) lam2 c2 hcm2 y
    have hG := gX_le_GhR lam2 hX0 hcm2
    have hg1 := gX_nonneg lam hX0 hX1 (show (0 : ℝ) < c1.2 by linarith) (by linarith)
    calc ENNReal.ofReal (Real.exp (lu * (slT N / N)) * Xf y ^ lu) *
          (∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c1 y u)) ∂unif) *
          (∫⁻ v, ENNReal.ofReal (Real.exp (-(lam2 : ℝ) * gXevE N c2 y v)) ∂unif)
        ≤ ENNReal.ofReal (Real.exp (lu * (slT N / N)) * Xf y ^ lu) *
          ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
            gX lam (c1.2 : ℝ) (Xf y)) *
          ENNReal.ofReal (Real.exp ((lam2 : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) *
            GhR lam2 (c2.2 : ℝ) (Xf y)) := by
          gcongr
          exact hin2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hG (Real.exp_pos _).le))
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1; simp only [C, fsK]; ring
  unfold unif
  rw [Measure.restrict_restrict hW]
  have hsplit : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc 0 (1 / 2) ∪ Set.Icc (1 / 2) 1 := by
    intro y hy; by_cases h : y ≤ 1 / 2
    · exact Or.inl ⟨hy.1, h⟩
    · exact Or.inr ⟨(not_le.1 h).le, hy.2⟩
  have hlo : ∀ y ∈ Set.Icc (0 : ℝ) (1 / 2), Xf y = 1 - y := fun y hy => by
    have hcy : clamp01 y = y := fs_clamp_of_mem ⟨hy.1, by linarith [hy.2]⟩
    simp only [Xf, hcy]; exact max_eq_right (by linarith [hy.2])
  have hhi : ∀ y ∈ Set.Icc (1 / 2 : ℝ) 1, Xf y = y := fun y hy => by
    have hcy : clamp01 y = y := fs_clamp_of_mem ⟨by linarith [hy.1], hy.2⟩
    simp only [Xf, hcy]; exact max_eq_left (by linarith [hy.1])
  have hgh : ∀ y ∈ Set.Ioc b 1, 0 ≤ C * (y ^ lu * gX lam (c1.2 : ℝ) y * GhR lam2 (c2.2 : ℝ) y) := by
    intro y hy
    have hy0 : 0 < y := hb0.trans hy.1
    have h1 := gX_nonneg lam (c := (c1.2 : ℝ)) hy0 hy.2 (by linarith) (by linarith [hy.2])
    have h2 := gX_nonneg lam2 (c := (c2.2 : ℝ)) hy0 hy.2 (by linarith) (by linarith [hy.2])
    have h3 := gX_le_GhR lam2 hy0 hcm2
    exact mul_nonneg hC.le (mul_nonneg (mul_nonneg (Real.rpow_nonneg hy0.le _) h1) (h2.trans h3))
  calc ∫⁻ y in {y : ℝ | (c1.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} ∩ Set.Icc 0 1,
        ENNReal.ofReal (Real.exp (-lu * ellSX N y)) *
          (∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c1 y u)) ∂unif) *
          (∫⁻ v, ENNReal.ofReal (Real.exp (-(lam2 : ℝ) * gXevE N c2 y v)) ∂unif)
      ≤ ∫⁻ y in {y : ℝ | (c1.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} ∩ Set.Icc 0 1, G (Xf y) :=
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
    _ = 2 * ∫⁻ y in Set.Ioc b 1, ENNReal.ofReal (C * (y ^ lu * gX lam (c1.2 : ℝ) y * GhR lam2 (c2.2 : ℝ) y)) := by
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
        have hint : IntegrableOn (fun y => C * (y ^ lu * gX lam (c1.2 : ℝ) y * GhR lam2 (c2.2 : ℝ) y))
            (Set.Ioc b 1) :=
          ((continuousOn_const.mul (((Real.continuous_rpow_const hlu).continuousOn.mul
            (gX_continuousOn lam _ hb0)).mul (GhR_continuousOn lam2 _ hb0))).integrableOn_Icc).mono_set
            Set.Ioc_subset_Icc_self
        rw [← ofReal_integral_eq_lintegral_ofReal hint, ← intervalIntegral.integral_of_le hb1,
          intervalIntegral.integral_const_mul, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        · congr 1; ring
        · exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hgh)

/-- **The floored row factor**: `∫_{y ≥ 1/2 - δ} y^p ≤ (1 - 2^{-(p+1)})/(p+1) + δ`. -/
lemma tf_floor_factor (p : ℕ) {t lu : ℝ} (htp : t - lu = p) (hδ : deltaU N < 1 / 2) :
    ∫⁻ y in {y : ℝ | 1 / 2 - deltaU N ≤ y}, ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 y))) ∂unif ≤
      ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ (p + 1)) / (p + 1) + deltaU N) := by
  have hδ0 : 0 < deltaU N := by unfold deltaU; positivity
  set a := 1 / 2 - deltaU N with ha
  have ha0 : 0 < a := by linarith
  have hWm : MeasurableSet {y : ℝ | a ≤ y} := measurableSet_le measurable_const measurable_id
  unfold unif
  rw [Measure.restrict_restrict hWm]
  have hset : {y : ℝ | a ≤ y} ∩ Set.Icc 0 1 = Set.Icc a 1 := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith, h3⟩
  rw [hset]
  have hpt : ∀ y ∈ Set.Icc a 1, Real.exp ((lu - t) * -Real.log (clamp01 y)) = y ^ p := fun y hy => by
    have hy0 : 0 < y := lt_of_lt_of_le ha0 hy.1
    rw [fs_clamp_of_mem ⟨hy0.le, hy.2⟩, show (lu - t) = -(p : ℝ) by linarith, ← Real.rpow_natCast,
      Real.rpow_def_of_pos hy0]
    ring_nf
  rw [setLIntegral_congr_fun measurableSet_Icc (g := fun y => ENNReal.ofReal (y ^ p)) fun y hy => by rw [hpt y hy]]
  rw [← ofReal_integral_eq_lintegral_ofReal ((continuous_pow p).integrableOn_Icc)
    (Filter.eventually_of_mem (ae_restrict_mem measurableSet_Icc) fun y hy =>
      pow_nonneg (by linarith [hy.1]) _)]
  apply ENNReal.ofReal_le_ofReal
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun y : ℝ => y ^ p) volume u v :=
    fun u v => (continuous_pow p).intervalIntegrable u v
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint a (1 / 2)) (hint (1 / 2) 1)]
  have h2 : ∫ y in a..1 / 2, y ^ p ≤ deltaU N := by
    calc ∫ y in a..1 / 2, y ^ p ≤ ∫ _y in a..1 / 2, (1 : ℝ) :=
          intervalIntegral.integral_mono_on (by linarith) (hint _ _) intervalIntegrable_const fun y hy =>
            pow_le_one₀ (by linarith [hy.1]) (by linarith [hy.2])
      _ = deltaU N := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have h3 : ∫ y in (1 / 2 : ℝ)..1, y ^ p = (1 - (1 / 2 : ℝ) ^ (p + 1)) / (p + 1) := by
    rw [integral_pow]; push_cast; ring
  linarith

/-! ### Same side: the per-pair bounds -/

lemma cellsXCause_half : cellsXCauseData.all (fun c => decide ((1 : ℚ) / 2 ≤ c.2)) = true := by decide +kernel
lemma cellsXEffect_half : cellsXEffectData.all (fun c => decide ((1 : ℚ) / 2 ≤ c.2)) = true := by decide +kernel

lemma cellX_half {c : ℚ × ℚ} (σ : XSide) (hc : c ∈ (match σ with
    | .cause => cellsXCauseData | .effect => cellsXEffectData)) : (1 : ℝ) / 2 ≤ (c.2 : ℝ) := by
  have h : (1 : ℚ) / 2 ≤ c.2 := by
    cases σ
    · simpa using List.all_eq_true.1 cellsXCause_half c hc
    · simpa using List.all_eq_true.1 cellsXEffect_half c hc
  have := (Rat.cast_le (K := ℝ)).2 h; push_cast at this; exact this

/-- The record of an overlapping pair. -/
lemma tf_recC {c c' : ℚ × ℚ} (hc : c ∈ cellsXCauseData) (hc' : c' ∈ cellsXCauseData)
    (hov : ¬ c.2 < c'.1) (hov' : ¬ c'.2 < c.1) : ∃ R ∈ tfRecsC, R.c1 = c ∧ R.c2 = c' := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 tfRecsC_cover c hc) c' hc'
  simp only [Bool.or_eq_true, decide_eq_true_eq, hov, hov', false_or] at h
  obtain ⟨R, hR, hR'⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hR'
  exact ⟨R, hR, hR'⟩

lemma tf_recE {c c' : ℚ × ℚ} (hc : c ∈ cellsXEffectData) (hc' : c' ∈ cellsXEffectData)
    (hov : ¬ c.2 < c'.1) (hov' : ¬ c'.2 < c.1) : ∃ R ∈ tfRecsE, R.c1 = c ∧ R.c2 = c' := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 tfRecsE_cover c hc) c' hc'
  simp only [Bool.or_eq_true, decide_eq_true_eq, hov, hov', false_or] at h
  obtain ⟨R, hR, hR'⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hR'
  exact ⟨R, hR, hR'⟩

/-- The unpacked facts of a checked record. -/
lemma tf_rec_facts (R : TFRec) (h : tfOK R = true) :
    (0 : ℝ) < R.v ∧ (R.v : ℝ) < 1 ∧ (1 : ℝ) / 2 ≤ (R.w : ℝ) ^ 4 ∧ (1 : ℝ) / 2 ≤ (R.cap2 : ℝ) := by
  simp only [tfOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, -⟩, -⟩, hv1⟩, hw2⟩, hc2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  refine ⟨by exact_mod_cast hv, by exact_mod_cast hv1, ?_, ?_⟩
  · have := (Rat.cast_le (K := ℝ)).2 hw2; push_cast at this; exact this
  · have := (Rat.cast_le (K := ℝ)).2 hc2; push_cast at this; exact this

/-- The rate of a checked record in the `tf_final` form. -/
lemma tf_rec_rate (R : TFRec) (h : tfOK R = true) :
    let TI := ∫ y in ((R.v : ℝ) ^ 4)..1, y ^ ((R.P : ℝ) / 4) * gX R.lam ((R.w : ℝ) ^ 4) y *
        GhR R.lam2 (R.cap2 : ℝ) y
    0 < TI ∧ Real.exp (((R.P : ℝ) / 4 + R.l2) * x0) * (TI * (rsEx R.l2 : ℝ)) ≤
      Real.exp (-((tfRT : ℝ) + Real.log 2)) := by
  intro TI
  obtain ⟨hpos, hs⟩ := tfRec_sound R h
  have hEx0 : (0 : ℝ) < rsEx R.l2 := by
    have : (0 : ℚ) < rsEx R.l2 := by
      unfold rsEx
      have : ((1 : ℚ) / 2) ^ (R.l2 + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      apply div_pos (by linarith) (by positivity)
    exact_mod_cast this
  refine ⟨hpos, ?_⟩
  rw [← Real.exp_log (show 0 < TI * (rsEx R.l2 : ℝ) from mul_pos hpos hEx0), ← Real.exp_add]
  apply Real.exp_le_exp.2
  rw [Real.log_mul hpos.ne' hEx0.ne']
  linarith

/-- **Two failing units, both cause.** -/
theorem tf_cc (hN : 2 ≤ N) (s r0 : State N) (x x' : Fin N) (hxx : x ≠ x') {c c' : ℚ × ℚ}
    (hc : c ∈ cellsXCauseData) (hc' : c' ∈ cellsXCauseData) (hov : ¬ c.2 < c'.1) (hov' : ¬ c'.2 < c.1)
    (h1 : r0 ≠ s) (h3 : flipAt x r0 ≠ s) (h5 : flipAt x' r0 ≠ s) :
    cubeM N ({w | CellEvX N s r0 x .cause c w} ∩ {w | CellEvX N s r0 x' .cause c' w}) ≤
      ENNReal.ofReal (TFB N) := by
  have hN0 : 0 < N := by omega
  obtain ⟨R, hR, hRc, hRc'⟩ := tf_recC hc hc' hov hov'
  have hok := List.all_eq_true.1 tfRecsC_ok R hR
  have hlk := List.all_eq_true.1 tfRecsC_link R hR
  obtain ⟨hv, hv1, hw4, hcap2⟩ := tf_rec_facts R hok
  simp only [tfLinkC, tfBounds, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hlk
  obtain ⟨⟨⟨hv4, hcap1⟩, hcapc⟩, ⟨⟨⟨hlam, hlam2⟩, hP⟩, hl2⟩⟩ := hlk
  rw [hRc] at hv4 hcap1; rw [hRc'] at hcapc
  have hch : (1 : ℝ) / 2 ≤ (c.2 : ℝ) := cellX_half .cause hc
  have hch' : (1 : ℝ) / 2 ≤ (c'.2 : ℝ) := cellX_half .cause hc'
  set c1 : ℚ × ℚ := (R.v ^ 4, R.w ^ 4) with hc1
  set c2 : ℚ × ℚ := (c'.1, R.cap2) with hc2
  have hcm1 : (1 : ℝ) / 2 ≤ (c1.2 : ℝ) := by simp only [hc1]; push_cast; exact hw4
  have hcm2 : (1 : ℝ) / 2 ≤ (c2.2 : ℝ) := hcap2
  have hm0 : (0 : ℝ) < (c1.1 : ℝ) := by simp only [hc1]; push_cast; positivity
  have hm1 : (c1.1 : ℝ) ≤ 1 := by simp only [hc1]; push_cast; exact pow_le_one₀ hv.le hv1.le
  have hmono1 := cellEvX_mono hN0 s r0 x (c := c) (c' := c1) (by simp only [hc1]; exact_mod_cast hv4)
    (by
      rcases hcap1 with h | h
      · left; simp only [hc1]; exact_mod_cast h
      · right; simp only [hc1, h]; norm_num)
    (by linarith) (by linarith)
  have hmono2 := cellEvX_mono hN0 s r0 x' (c := c') (c' := c2) (by simp only [hc2]; exact le_rfl)
    (by
      rcases hcapc with h | h
      · left; simp only [hc2]; exact_mod_cast h
      · right; simp only [hc2, h]; norm_num)
    (by linarith) (by linarith)
  have hsubA := cellEvX_sub_template hN0 s r0 x c1 hcm1
  have hsubB := cellEvX_sub_template hN0 s r0 x' c2 hcm2
  set lu : ℝ := (R.l2 : ℝ) with hlu
  set t : ℝ := (R.P : ℝ) / 4 + lu with ht
  have hlu0 : 0 ≤ lu := Nat.cast_nonneg _
  set Wa : Set ℝ := {y : ℝ | (c1.1 : ℝ) ≤ clamp01 y} with hWa
  have hWam : MeasurableSet Wa := measurableSet_le measurable_const clamp01_measurable
  set f : Fin 4 → Fin N → (ℝ × ℝ) × (ℝ × ℝ) → ℝ :=
    ![fun _ p => -Real.log (clamp01 p.1.1), fun _ p => ellSX N p.2.1 - -Real.log (clamp01 p.1.1),
      fun _ p => gXev N c1 p.1.1 p.1.2, fun _ p => gXev N c2 p.1.1 p.2.2] with hf
  have hell : Measurable fun y : ℝ => -Real.log (clamp01 y) :=
    (Real.measurable_log.comp clamp01_measurable).neg
  have hfm : ∀ k i, Measurable (f k i) := by
    intro k i
    fin_cases k
    · exact hell.comp (measurable_fst.comp measurable_fst)
    · exact (fs_ellSX_meas.comp (measurable_fst.comp measurable_snd)).sub (hell.comp (measurable_fst.comp measurable_fst))
    · exact (fs_gXev_meas c1).comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst))
    · exact (fs_gXev_meas c2).comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
  set a : Fin 4 → ℝ := ![x0 * N + slT N, 0, 0, 0] with ha
  set tt : Fin 4 → ℝ := ![t, lu, (R.lam : ℝ), (R.lam2 : ℝ)] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 4)), 0 ≤ tt k := by
    intro k _; fin_cases k
    · simp only [htt]; simp; positivity
    · simpa [htt] using hlu0
    · simp [htt]
    · simp [htt]
  have hmain := cubeM_chernoff_four (fun _ => r0) (fun _ => flipAt x r0) (fun _ => s) (fun _ => flipAt x' r0)
    (fun _ => (flipAt_ne x r0).symm) (fun _ => h1) (fun _ => (flipAt_ne x' r0).symm) (fun _ => h3)
    (fun _ => fs_flip_ne (Ne.symm hxx) r0) (fun _ => Ne.symm h5) univ f hfm a tt htt0 (fun _ => Wa)
    (fun _ => Set.univ) (fun _ => hWam) (fun _ => MeasurableSet.univ)
  have hsub : ({w | CellEvX N s r0 x .cause c w} ∩ {w | CellEvX N s r0 x' .cause c' w} : Set (Param N)) ⊆
      {w | (∀ i, w ((fun _ : Fin N => r0) i) i ∈ (fun _ : Fin N => Wa) i ∧
          w ((fun _ : Fin N => s) i) i ∈ (fun _ : Fin N => (Set.univ : Set ℝ)) i) ∧
        ∀ k ∈ (univ : Finset (Fin 4)), ∑ i, f k i ((w ((fun _ : Fin N => r0) i) i,
          w ((fun _ : Fin N => flipAt x r0) i) i), (w ((fun _ : Fin N => s) i) i,
            w ((fun _ : Fin N => flipAt x' r0) i) i)) ≤ a k} := by
    rintro w ⟨hw1, hw2⟩
    obtain ⟨hW1, hT, hL, hV⟩ := hsubA (hmono1 hw1)
    obtain ⟨-, -, -, hV'⟩ := hsubB (hmono2 hw2)
    refine ⟨fun i => ⟨hW1 i, Set.mem_univ _⟩, fun k _ => ?_⟩
    fin_cases k
    · simpa [hf, ha] using hT
    · simp only [hf, ha]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [sum_sub_distrib]
      have : ∑ i, ellSX N (w s i) = ∑ i, ellUX N (w s i) := rfl
      rw [this]; linarith
    · simpa [hf, ha] using hV
    · simpa [hf, ha] using hV'
  -- the column factor
  set TI := ∫ y in ((R.v : ℝ) ^ 4)..1, y ^ ((R.P : ℝ) / 4) * gX R.lam ((R.w : ℝ) ^ 4) y *
      GhR R.lam2 (R.cap2 : ℝ) y with hTI
  obtain ⟨hTI0, hrate⟩ := tf_rec_rate R hok
  set Ex : ℝ := (rsEx R.l2 : ℝ) with hEx
  have hEx' : Ex = 2 * (1 - (1 / 2 : ℝ) ^ (R.l2 + 1)) / (R.l2 + 1) := by rw [hEx, rsEx_cast]
  have hEx0 : 0 ≤ Ex := by
    rw [hEx']; have : (1 / 2 : ℝ) ^ (R.l2 + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    apply div_nonneg (by linarith) (by positivity)
  set J : ℝ := Real.exp (((R.lam : ℝ) + R.lam2) * fsK N) * Real.exp (lu * (slT N / N)) * (TI * Ex) *
    (1 + 0 * deltaU N) with hJ
  have hJ0 : 0 ≤ J := by
    rw [hJ]
    have hδ0 : 0 ≤ deltaU N := by unfold deltaU; positivity
    exact mul_nonneg (mul_nonneg (by positivity) (mul_nonneg hTI0.le hEx0)) (by positivity)
  have hcol : ∀ i : Fin N, ∫⁻ y in (fun _ : Fin N => Wa) i, ∫⁻ u, ∫⁻ z in (fun _ : Fin N => (Set.univ : Set ℝ)) i,
      ∫⁻ v, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)), tt k * f k i ((y, u), (z, v))))
        ∂unif ∂unif ∂unif ∂unif ≤ ENNReal.ofReal J := by
    intro i
    have hpt : ∀ y u z v, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)), tt k * f k i ((y, u), (z, v)))) =
        ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 y))) *
          ENNReal.ofReal (Real.exp (-(R.lam : ℝ) * gXev N c1 y u)) *
          (ENNReal.ofReal (Real.exp (-(R.l2 : ℝ) * ellSX N z)) *
            ENNReal.ofReal (Real.exp (-(R.lam2 : ℝ) * gXev N c2 y v))) := by
      intro y u z v
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 2
      simp [Fin.sum_univ_four, hf, htt]
      ring
    simp_rw [hpt]
    have m1 : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 y))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hell.const_mul _))
    have m2 : Measurable fun z : ℝ => ENNReal.ofReal (Real.exp (-(R.l2 : ℝ) * ellSX N z)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (fs_ellSX_meas.const_mul _))
    have m3 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(R.lam : ℝ) * gXev N c1 p.1 p.2)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((fs_gXev_meas c1).const_mul _))
    have m4 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(R.lam2 : ℝ) * gXev N c2 p.1 p.2)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((fs_gXev_meas c2).const_mul _))
    rw [lint4_split2 Wa Set.univ (fun y => ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 y))))
      (fun z => ENNReal.ofReal (Real.exp (-(R.l2 : ℝ) * ellSX N z)))
      (fun y u => ENNReal.ofReal (Real.exp (-(R.lam : ℝ) * gXev N c1 y u)))
      (fun y v => ENNReal.ofReal (Real.exp (-(R.lam2 : ℝ) * gXev N c2 y v))) m1 m2 m3 m4]
    have hE : ∫⁻ z in Set.univ, ENNReal.ofReal (Real.exp (-(R.l2 : ℝ) * ellSX N z)) ∂unif =
        ENNReal.ofReal (Real.exp (lu * (slT N / N)) * Ex) := by
      rw [Measure.restrict_univ, hEx']; exact lintegral_ellUX R.l2
    have hJ1 := tf_J_cc (N := N) R.lam R.lam2 c1 c2 hcm1 hcm2 hm0 hm1 (t := t) (lamU := lu) (by
      rw [ht]; have : (0 : ℝ) ≤ (R.P : ℝ) / 4 := by positivity
      linarith)
    have e1 : (∫ y in (c1.1 : ℝ)..1, y ^ (t - lu) * gX R.lam (c1.2 : ℝ) y * GhR R.lam2 (c2.2 : ℝ) y) = TI := by
      simp only [hc1, hc2, ht, add_sub_cancel_right, hTI]; push_cast; rfl
    rw [e1] at hJ1
    rw [hE]
    calc ENNReal.ofReal (Real.exp (lu * (slT N / N)) * Ex) *
          ∫⁻ y in Wa, ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 y))) *
            (∫⁻ u, ENNReal.ofReal (Real.exp (-(R.lam : ℝ) * gXev N c1 y u)) ∂unif) *
            (∫⁻ v, ENNReal.ofReal (Real.exp (-(R.lam2 : ℝ) * gXev N c2 y v)) ∂unif) ∂unif
        ≤ ENNReal.ofReal (Real.exp (lu * (slT N / N)) * Ex) *
          ENNReal.ofReal (Real.exp ((R.lam : ℝ) * fsK N) * Real.exp ((R.lam2 : ℝ) * fsK N) * TI) :=
          mul_le_mul_right hJ1 _
      _ = ENNReal.ofReal J := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; rw [hJ, add_mul, Real.exp_add]; ring
  refine (measure_mono hsub).trans (hmain.trans ?_)
  have hsum : ∑ k ∈ (univ : Finset (Fin 4)), tt k * a k = t * (x0 * N + slT N) := by
    simp [Fin.sum_univ_four, htt, ha]
  rw [hsum]
  calc ENNReal.ofReal (Real.exp (t * (x0 * N + slT N))) * ∏ i : Fin N, ∫⁻ y in (fun _ : Fin N => Wa) i,
        ∫⁻ u, ∫⁻ z in (fun _ : Fin N => (Set.univ : Set ℝ)) i, ∫⁻ v,
          ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)), tt k * f k i ((y, u), (z, v))))
            ∂unif ∂unif ∂unif ∂unif
      ≤ ENNReal.ofReal (Real.exp (t * (x0 * N + slT N))) * ∏ _i : Fin N, ENNReal.ofReal J := by
        gcongr with i; exact hcol i
    _ = ENNReal.ofReal (Real.exp (t * (x0 * N + slT N)) * J ^ N) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow hJ0,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ ENNReal.ofReal (TFB N) := by
        apply ENNReal.ofReal_le_ofReal
        have hlamR : (R.lam : ℝ) ≤ 17 := by exact_mod_cast hlam
        have hlam2R : (R.lam2 : ℝ) ≤ 6 := by exact_mod_cast hlam2
        have hPR : (R.P : ℝ) ≤ 40 := by exact_mod_cast hP
        have hl2R : (R.l2 : ℝ) ≤ 5 := by exact_mod_cast hl2
        exact tf_final (by omega) (by rw [ht]; positivity) (by rw [ht, hlu]; linarith) (by positivity)
          (by linarith) hlu0 (by rw [hlu]; linarith) (mul_nonneg hTI0.le hEx0) le_rfl (by norm_num)
          (by rw [ht, hlu]; exact hrate) (by unfold tfRT; push_cast; linarith)

lemma tf_Hp_ge (p : ℕ) (hp : p ≤ 5) : (1 : ℝ) / 10 ≤ (1 - (1 / 2 : ℝ) ^ (p + 1)) / (p + 1) := by
  interval_cases p <;> norm_num

/-- **Two failing units, both effect.** -/
theorem tf_ee (hN : 2 ≤ N) (hδ : deltaU N < 1 / 2) (s r0 : State N) (x x' : Fin N) (hxx : x ≠ x')
    {c c' : ℚ × ℚ} (hc : c ∈ cellsXEffectData) (hc' : c' ∈ cellsXEffectData) (hov : ¬ c.2 < c'.1)
    (hov' : ¬ c'.2 < c.1) (h1 : r0 ≠ s) (h2 : r0 ≠ flipAt x s) (h4 : r0 ≠ flipAt x' s) :
    cubeM N ({w | CellEvX N s r0 x .effect c w} ∩ {w | CellEvX N s r0 x' .effect c' w}) ≤
      ENNReal.ofReal (TFB N) := by
  have hN0 : 0 < N := by omega
  have hδ0 : 0 < deltaU N := by unfold deltaU; positivity
  obtain ⟨R, hR, hRc, hRc'⟩ := tf_recE hc hc' hov hov'
  have hok := List.all_eq_true.1 tfRecsE_ok R hR
  have hlk := List.all_eq_true.1 tfRecsE_link R hR
  obtain ⟨hv, hv1, hw4, hcap2⟩ := tf_rec_facts R hok
  simp only [tfLinkE, tfBounds, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hlk
  obtain ⟨⟨⟨hv4, hcap1⟩, hcapc⟩, ⟨⟨⟨hlam, hlam2⟩, hP⟩, hl2⟩⟩ := hlk
  rw [hRc] at hv4 hcap1; rw [hRc'] at hcapc
  have hch : (1 : ℝ) / 2 ≤ (c.2 : ℝ) := cellX_half .effect hc
  have hch' : (1 : ℝ) / 2 ≤ (c'.2 : ℝ) := cellX_half .effect hc'
  set c1 : ℚ × ℚ := (c.1, R.w ^ 4) with hc1
  set c2 : ℚ × ℚ := (c'.1, R.cap2) with hc2
  have hcm1 : (1 : ℝ) / 2 ≤ (c1.2 : ℝ) := by simp only [hc1]; push_cast; exact hw4
  have hcm2 : (1 : ℝ) / 2 ≤ (c2.2 : ℝ) := hcap2
  have hmono1 := cellEvX_mono_eff s r0 x (c := c) (c' := c1) (by simp only [hc1])
    (by
      rcases hcap1 with h | h
      · left; simp only [hc1]; exact_mod_cast h
      · right; simp only [hc1, h]; norm_num)
    (by linarith) (by linarith)
  have hmono2 := cellEvX_mono_eff s r0 x' (c := c') (c' := c2) (by simp only [hc2])
    (by
      rcases hcapc with h | h
      · left; simp only [hc2]; exact_mod_cast h
      · right; simp only [hc2, h]; norm_num)
    (by linarith) (by linarith)
  have hsubA := cellEvX_eff_sub_template hN0 s r0 x c1 hcm1 hδ
  have hsubB := cellEvX_eff_sub_template hN0 s r0 x' c2 hcm2 hδ
  set lu : ℝ := (R.P : ℝ) / 4 with hlu
  set t : ℝ := lu + R.l2 with ht
  have hlu0 : 0 ≤ lu := by positivity
  set Wa : Set ℝ := {y : ℝ | (c1.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} with hWa
  set Wc : Set ℝ := {y : ℝ | 1 / 2 - deltaU N ≤ y} with hWc
  have hWam : MeasurableSet Wa :=
    measurableSet_le measurable_const (clamp01_measurable.max (measurable_const.sub clamp01_measurable))
  have hWcm : MeasurableSet Wc := measurableSet_le measurable_const measurable_id
  set f : Fin 4 → Fin N → (ℝ × ℝ) × (ℝ × ℝ) → ℝ :=
    ![fun _ p => -Real.log (clamp01 p.2.1), fun _ p => ellSX N p.1.1 - -Real.log (clamp01 p.2.1),
      fun _ p => gXevE N c1 p.1.1 p.1.2, fun _ p => gXevE N c2 p.1.1 p.2.2] with hf
  have hell : Measurable fun y : ℝ => -Real.log (clamp01 y) :=
    (Real.measurable_log.comp clamp01_measurable).neg
  have hfm : ∀ k i, Measurable (f k i) := by
    intro k i
    fin_cases k
    · exact hell.comp (measurable_fst.comp measurable_snd)
    · exact (fs_ellSX_meas.comp (measurable_fst.comp measurable_fst)).sub (hell.comp (measurable_fst.comp measurable_snd))
    · exact (fs_gE_meas c1).comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst))
    · exact (fs_gE_meas c2).comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
  set a : Fin 4 → ℝ := ![x0 * N + slT N, 0, 0, 0] with ha
  set tt : Fin 4 → ℝ := ![t, lu, (R.lam : ℝ), (R.lam2 : ℝ)] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 4)), 0 ≤ tt k := by
    intro k _; fin_cases k
    · simp only [htt]; simp; positivity
    · simpa [htt] using hlu0
    · simp [htt]
    · simp [htt]
  have hmain := cubeM_chernoff_four (fun _ => s) (fun _ => flipAt x s) (fun _ => r0) (fun _ => flipAt x' s)
    (fun _ => (flipAt_ne x s).symm) (fun _ => Ne.symm h1) (fun _ => (flipAt_ne x' s).symm) (fun _ => Ne.symm h2)
    (fun _ => fs_flip_ne (Ne.symm hxx) s) (fun _ => h4) univ f hfm a tt htt0 (fun _ => Wa)
    (fun _ => Wc) (fun _ => hWam) (fun _ => hWcm)
  have hsub : ({w | CellEvX N s r0 x .effect c w} ∩ {w | CellEvX N s r0 x' .effect c' w} : Set (Param N)) ⊆
      {w | (∀ i, w ((fun _ : Fin N => s) i) i ∈ (fun _ : Fin N => Wa) i ∧
          w ((fun _ : Fin N => r0) i) i ∈ (fun _ : Fin N => Wc) i) ∧
        ∀ k ∈ (univ : Finset (Fin 4)), ∑ i, f k i ((w ((fun _ : Fin N => s) i) i,
          w ((fun _ : Fin N => flipAt x s) i) i), (w ((fun _ : Fin N => r0) i) i,
            w ((fun _ : Fin N => flipAt x' s) i) i)) ≤ a k} := by
    rintro w ⟨hw1, hw2⟩
    obtain ⟨hW1, hT, hL, hV, hF⟩ := hsubA (hmono1 hw1)
    obtain ⟨-, -, -, hV', -⟩ := hsubB (hmono2 hw2)
    refine ⟨fun i => ⟨hW1 i, hF i⟩, fun k _ => ?_⟩
    fin_cases k
    · simpa [hf, ha] using hT
    · simp only [hf, ha]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [sum_sub_distrib]; linarith
    · simpa [hf, ha] using hV
    · simpa [hf, ha] using hV'
  -- the column factor
  set TI := ∫ y in ((R.v : ℝ) ^ 4)..1, y ^ ((R.P : ℝ) / 4) * gX R.lam ((R.w : ℝ) ^ 4) y *
      GhR R.lam2 (R.cap2 : ℝ) y with hTI
  obtain ⟨hTI0, hrate⟩ := tf_rec_rate R hok
  set Hp : ℝ := (1 - (1 / 2 : ℝ) ^ (R.l2 + 1)) / (R.l2 + 1) with hHpdef
  have hHp10 : (1 : ℝ) / 10 ≤ Hp := tf_Hp_ge R.l2 hl2
  set Ex : ℝ := (rsEx R.l2 : ℝ) with hEx
  have hEx' : Ex = 2 * Hp := by rw [hEx, rsEx_cast, hHpdef]; ring
  set E := Real.exp (lu * (slT N / N)) with hE
  set J : ℝ := Real.exp (((R.lam : ℝ) + R.lam2) * fsK N) * E * (TI * Ex) * (1 + (1 / Hp) * deltaU N) with hJ
  have hJ0 : 0 ≤ J := by
    rw [hJ, hEx']
    have : 0 < Hp := by linarith
    exact mul_nonneg (mul_nonneg (by positivity) (mul_nonneg hTI0.le (by positivity))) (by positivity)
  have hcol : ∀ i : Fin N, ∫⁻ y in (fun _ : Fin N => Wa) i, ∫⁻ u, ∫⁻ z in (fun _ : Fin N => Wc) i,
      ∫⁻ v, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)), tt k * f k i ((y, u), (z, v))))
        ∂unif ∂unif ∂unif ∂unif ≤ ENNReal.ofReal J := by
    intro i
    have hpt : ∀ y u z v, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)), tt k * f k i ((y, u), (z, v)))) =
        ENNReal.ofReal (Real.exp (-lu * ellSX N y)) *
          ENNReal.ofReal (Real.exp (-(R.lam : ℝ) * gXevE N c1 y u)) *
          (ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 z))) *
            ENNReal.ofReal (Real.exp (-(R.lam2 : ℝ) * gXevE N c2 y v))) := by
      intro y u z v
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 2
      simp [Fin.sum_univ_four, hf, htt]
      ring
    simp_rw [hpt]
    have m1 : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (-lu * ellSX N y)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (fs_ellSX_meas.const_mul _))
    have m2 : Measurable fun z : ℝ => ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 z))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hell.const_mul _))
    have m3 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(R.lam : ℝ) * gXevE N c1 p.1 p.2)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((fs_gE_meas c1).const_mul _))
    have m4 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(R.lam2 : ℝ) * gXevE N c2 p.1 p.2)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((fs_gE_meas c2).const_mul _))
    rw [lint4_split2 Wa Wc (fun y => ENNReal.ofReal (Real.exp (-lu * ellSX N y)))
      (fun z => ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 z))))
      (fun y u => ENNReal.ofReal (Real.exp (-(R.lam : ℝ) * gXevE N c1 y u)))
      (fun y v => ENNReal.ofReal (Real.exp (-(R.lam2 : ℝ) * gXevE N c2 y v))) m1 m2 m3 m4]
    have hF := tf_floor_factor (N := N) R.l2 (t := t) (lu := lu) (by rw [ht]; ring) hδ
    have hb0 : (0 : ℝ) < (R.v : ℝ) ^ 4 := by positivity
    have hb1 : (R.v : ℝ) ^ 4 ≤ 1 := pow_le_one₀ hv.le hv1.le
    have hbm : (R.v : ℝ) ^ 4 ≤ max (1 / 2) (c1.1 : ℝ) := by
      simp only [hc1]; have := (Rat.cast_le (K := ℝ)).2 hv4; push_cast at this; exact this
    have hS := tf_s_factor2 (N := N) R.lam R.lam2 c1 c2 hcm1 hcm2 hlu0 hb0 hbm hb1
    have e1 : (∫ X in (R.v : ℝ) ^ 4..1, X ^ lu * gX R.lam (c1.2 : ℝ) X * GhR R.lam2 (c2.2 : ℝ) X) = TI := by
      simp only [hc1, hc2, hTI, hlu]; push_cast; rfl
    rw [e1] at hS
    calc (∫⁻ z in Wc, ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 z))) ∂unif) *
          ∫⁻ y in Wa, ENNReal.ofReal (Real.exp (-lu * ellSX N y)) *
            (∫⁻ u, ENNReal.ofReal (Real.exp (-(R.lam : ℝ) * gXevE N c1 y u)) ∂unif) *
            (∫⁻ v, ENNReal.ofReal (Real.exp (-(R.lam2 : ℝ) * gXevE N c2 y v)) ∂unif) ∂unif
        ≤ ENNReal.ofReal (Hp + deltaU N) *
          ENNReal.ofReal (E * Real.exp ((R.lam : ℝ) * fsK N) * Real.exp ((R.lam2 : ℝ) * fsK N) * (2 * TI)) :=
          mul_le_mul' hF hS
      _ = ENNReal.ofReal J := by
          rw [← ENNReal.ofReal_mul (by have : 0 < Hp := by linarith
                                       positivity)]
          congr 1
          rw [hJ, hEx', show ((R.lam : ℝ) + R.lam2) * fsK N = R.lam * fsK N + R.lam2 * fsK N by ring,
            Real.exp_add]
          have : Hp ≠ 0 := by linarith
          field_simp
  refine (measure_mono hsub).trans (hmain.trans ?_)
  have hsum : ∑ k ∈ (univ : Finset (Fin 4)), tt k * a k = t * (x0 * N + slT N) := by
    simp [Fin.sum_univ_four, htt, ha]
  rw [hsum]
  calc ENNReal.ofReal (Real.exp (t * (x0 * N + slT N))) * ∏ i : Fin N, ∫⁻ y in (fun _ : Fin N => Wa) i,
        ∫⁻ u, ∫⁻ z in (fun _ : Fin N => Wc) i, ∫⁻ v,
          ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)), tt k * f k i ((y, u), (z, v))))
            ∂unif ∂unif ∂unif ∂unif
      ≤ ENNReal.ofReal (Real.exp (t * (x0 * N + slT N))) * ∏ _i : Fin N, ENNReal.ofReal J := by
        gcongr with i; exact hcol i
    _ = ENNReal.ofReal (Real.exp (t * (x0 * N + slT N)) * J ^ N) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow hJ0,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ ENNReal.ofReal (TFB N) := by
        apply ENNReal.ofReal_le_ofReal
        have hlamR : (R.lam : ℝ) ≤ 17 := by exact_mod_cast hlam
        have hlam2R : (R.lam2 : ℝ) ≤ 6 := by exact_mod_cast hlam2
        have hPR : (R.P : ℝ) ≤ 40 := by exact_mod_cast hP
        have hl2R : (R.l2 : ℝ) ≤ 5 := by exact_mod_cast hl2
        have hEx0 : 0 ≤ Ex := by rw [hEx']; linarith
        have hHp0 : 0 < Hp := by linarith
        exact tf_final (by omega) (by rw [ht]; positivity) (by rw [ht, hlu]; linarith) (by positivity)
          (by linarith) hlu0 (by rw [hlu]; linarith) (mul_nonneg hTI0.le hEx0)
          (by positivity) (by rw [div_le_iff₀ hHp0]; linarith)
          (by rw [ht, hlu]; exact hrate) (by unfold tfRT; push_cast; linarith)

end Census
end IIT
