/-
Census, B1 forced leaf 8 (`far`) at rate `RfF2`: the row-coincidence sub-leaf (agent "forcedF").

`r0 = s` or `r0^x = s`: the union over `r0` is lost, but the coinciding rows drop out of the template and the
certified cells of Lemma RS (`rsCellsC`, `rsCellsE`) already give the rate `R0 + log(3/2) ≥ 1.4127`:
* cause side: the link row is dropped (template with a dummy third row and `ellU = 0`); per unit the factor is
  the certified `I = ∫_{v⁴}^1 y^{P/4} gX` and `log I + (P/4) x0 ≤ -(R0 + log 2 + log rsEx(l) + l x0)`, with
  `rsEx(l) e^{l x0} ≥ 3/4` (`l ≤ 3`);
* effect side, `r0 = s`: tilt and floor sit on row `s` itself; per unit `≤ e^{λK}(I + δ (3/2)^λ)`;
* effect side, `r0 = s^x`: tilt + link chain to `Σ -log X_s ≤ x0 N + 2 slT`, the floor on the `s^x` entry kills
  the orientation doubling; pairing `y` with `1-y` gives `≤ e^{λK}(I + 4δ(3/2)^λ)` per unit.
-/
import IIT.Census.B1ForcedAF
import IIT.Census.B1ForcedB1

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-! ### Constants and the certified rate -/

/-- The per-unit V-slack `K`. -/
noncomputable def fsK (N : ℕ) : ℝ := 7 * deltaU N + (slV N + Real.log 2) / N

/-- The certified integral of a cell. -/
noncomputable def fsI (C : RSCell) : ℝ :=
  ∫ y in ((C.v : ℝ) ^ 4)..1, y ^ ((C.P : ℝ) / 4) * gX C.lam ((C.w : ℝ) ^ 4) y

/-- The δ-coefficient. -/
noncomputable def fsc1 : ℝ := 4 * (3 / 2 : ℝ) ^ 17

lemma fsc1_nonneg : 0 ≤ fsc1 := by unfold fsc1; positivity

lemma log_three_halves_eq : Real.log (3 / 2) = 2 * x0 := by unfold x0; ring

lemma rsEx_cast (l : ℕ) : ((rsEx l : ℚ) : ℝ) = 2 * (1 - (1 / 2 : ℝ) ^ (l + 1)) / (l + 1) := by
  unfold rsEx; push_cast; ring

/-- `log rsEx(l) + l x0 ≥ log (3/4)` for `l ≤ 3`. -/
lemma rsEx_tilt_ge (l : ℕ) (hl : l ≤ 3) :
    Real.log (3 / 4) ≤ Real.log (rsEx l : ℝ) + l * x0 := by
  have hpos : (0 : ℝ) < rsEx l := by
    rw [rsEx_cast]
    have : (1 / 2 : ℝ) ^ (l + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    apply div_pos (by linarith) (by positivity)
  have key : (9 / 16 : ℝ) ≤ (rsEx l : ℝ) ^ 2 * (3 / 2) ^ l := by
    rw [rsEx_cast]; interval_cases l <;> norm_num
  have e1 : Real.log (rsEx l : ℝ) + l * x0 = Real.log ((rsEx l : ℝ) ^ 2 * (3 / 2) ^ l) / 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, log_three_halves_eq]
    push_cast; ring
  have e2 : Real.log (3 / 4) = Real.log (9 / 16) / 2 := by
    rw [show (9 / 16 : ℝ) = (3 / 4) ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [e1, e2]
  have := Real.log_le_log (by norm_num) key
  linarith

/-- **The self rate of a certified cell**: `log I + (P/4) x0 ≤ -(R0 + log (3/2))`. -/
lemma fs_cell_rate (C : RSCell) (h : rsCellOK C = true) (hlu : C.lu ≤ 3) :
    Real.log (fsI C) + (C.P : ℝ) / 4 * x0 ≤ -((rsR0 : ℝ) + Real.log (3 / 2)) := by
  have hs := rsCell_sound C h
  have ht := rsEx_tilt_ge C.lu hlu
  have e : Real.log (3 / 2) = Real.log 2 + Real.log (3 / 4) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  unfold fsI
  nlinarith

lemma fs_cell_pos (C : RSCell) (h : rsCellOK C = true) : 0 < fsI C := by
  have h' := h
  simp only [rsCellOK, Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hvw⟩, hw1⟩, hv1⟩, hw2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h'
  exact cellI_pos C hv hvw hv1 hw2

/-- The rate gap: `R0 + log(3/2) - 2/5 ≥ RfF2`. -/
lemma fs_rate_gap : RfF2 + 2 / 5 ≤ (rsR0 : ℝ) + Real.log (3 / 2) := by
  rw [log_three_halves_eq]; have := x0_gt; unfold RfF2 rsR0; push_cast; linarith

lemma fs_slack (N : ℕ) (hN : 1 ≤ N) :
    16 * slT N + 17 * (8 + slV N) ≤ 4000 + 1400 * Real.log N := by
  have h := rs_slack_le N
  have : 0 ≤ slT N := by
    unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    linarith
  linarith

/-- **Absorption for the self cells** (uniform over certified cells). -/
theorem fs_absorb : ∀ᶠ N : ℕ in atTop, ∀ C : RSCell, rsCellOK C = true → C.lu ≤ 3 → C.P ≤ 32 →
    Real.exp ((C.P : ℝ) / 4 * x0 * N) * Real.exp (16 * slT N + 17 * (8 + slV N)) *
      (fsI C + fsc1 * deltaU N) ^ N ≤ Real.exp (-(RfF2 * N)) / (488 * N) := by
  set c2 : ℝ := Real.exp 4 * fsc1 with hc2
  filter_upwards [poly_absorb (488 * Real.exp c2) 1 (δ := 2 / 5) (by norm_num), eventually_ge_atTop 1]
    with N hab hN1 C hok hlu hP
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set R1 : ℝ := (rsR0 : ℝ) + Real.log (3 / 2) with hR1
  set l : ℝ := (C.P : ℝ) / 4 with hl
  have hl0 : 0 ≤ l := by positivity
  have hl8 : l ≤ 8 := by
    have : (C.P : ℝ) ≤ 32 := by exact_mod_cast hP
    simp only [hl]; linarith
  have hI := fs_cell_pos C hok
  have hrate := fs_cell_rate C hok hlu
  have hδ0 : 0 ≤ deltaU N := by unfold deltaU; positivity
  have hδN : deltaU N * N ≤ 1 := by
    unfold deltaU; rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  -- per unit: e^{l x0} (I + c1 δ) ≤ e^{-R1} (1 + c2 δ)
  have hx := x0_lt
  have hxp := x0_pos
  have hR1le : R1 + 8 * x0 ≤ 4 := by
    simp only [hR1]; rw [log_three_halves_eq]; unfold rsR0; push_cast; linarith
  have hu1 : Real.exp (l * x0) * fsI C ≤ Real.exp (-R1) := by
    rw [← Real.exp_log hI, ← Real.exp_add]; apply Real.exp_le_exp.2; simp only [hR1, hl] at *; linarith
  have hu2 : Real.exp (l * x0) * (fsc1 * deltaU N) ≤ Real.exp (-R1) * (c2 * deltaU N) := by
    have h1 : Real.exp (l * x0) ≤ Real.exp (-R1) * Real.exp 4 := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
    have := fsc1_nonneg
    calc Real.exp (l * x0) * (fsc1 * deltaU N) ≤ Real.exp (-R1) * Real.exp 4 * (fsc1 * deltaU N) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by rw [hc2]; ring
  have hunit : Real.exp (l * x0) * (fsI C + fsc1 * deltaU N) ≤ Real.exp (-R1) * (1 + c2 * deltaU N) := by
    rw [mul_add, mul_add, mul_one]; linarith
  have hc20 : 0 ≤ c2 := by rw [hc2]; have := fsc1_nonneg; positivity
  have hpowN : (Real.exp (l * x0) * (fsI C + fsc1 * deltaU N)) ^ N ≤
      Real.exp (-(R1 * N)) * Real.exp c2 := by
    calc (Real.exp (l * x0) * (fsI C + fsc1 * deltaU N)) ^ N
        ≤ (Real.exp (-R1) * (1 + c2 * deltaU N)) ^ N :=
          pow_le_pow_left₀ (by have := fsc1_nonneg; positivity) hunit N
      _ = Real.exp (-R1) ^ N * (1 + c2 * deltaU N) ^ N := mul_pow _ _ _
      _ ≤ Real.exp (-R1) ^ N * Real.exp (c2 * deltaU N) ^ N := by
          gcongr; linarith [Real.add_one_le_exp (c2 * deltaU N)]
      _ = Real.exp (-(R1 * N)) * Real.exp (c2 * (deltaU N * N)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1 <;> congr 1 <;> ring
      _ ≤ Real.exp (-(R1 * N)) * Real.exp c2 := by
          gcongr; nlinarith
  have hsl := fs_slack N hN1
  have hlhs : Real.exp (l * x0 * N) * Real.exp (16 * slT N + 17 * (8 + slV N)) *
      (fsI C + fsc1 * deltaU N) ^ N =
      Real.exp (16 * slT N + 17 * (8 + slV N)) * (Real.exp (l * x0) * (fsI C + fsc1 * deltaU N)) ^ N := by
    rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
  rw [hlhs]
  -- poly_absorb: 488 e^{c2} (N+1) e^{4000 + 1400 log N} ≤ e^{2N/5}
  simp only [pow_one] at hab
  have hgap := fs_rate_gap
  have hNpos : (0 : ℝ) < N := by linarith
  rw [le_div_iff₀ (by positivity)]
  calc Real.exp (16 * slT N + 17 * (8 + slV N)) * (Real.exp (l * x0) * (fsI C + fsc1 * deltaU N)) ^ N *
        (488 * N)
      ≤ Real.exp (4000 + 1400 * Real.log N) * (Real.exp (-(R1 * N)) * Real.exp c2) * (488 * ((N : ℝ) + 1)) := by
        have hP0 : 0 ≤ (Real.exp (l * x0) * (fsI C + fsc1 * deltaU N)) ^ N :=
          pow_nonneg (mul_nonneg (Real.exp_pos _).le (add_nonneg hI.le (mul_nonneg fsc1_nonneg hδ0))) N
        exact mul_le_mul (mul_le_mul (Real.exp_le_exp.2 hsl) hpowN hP0 (Real.exp_pos _).le)
          (by linarith) (by positivity) (by positivity)
    _ = (488 * Real.exp c2 * ((N : ℝ) + 1) * Real.exp (4000 + 1400 * Real.log N)) * Real.exp (-(R1 * N)) := by
        ring
    _ ≤ Real.exp (2 / 5 * N) * Real.exp (-(R1 * N)) := by gcongr
    _ ≤ Real.exp (-(RfF2 * N)) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith

/-! ### Per-cell arithmetic -/

lemma fsK_mul_le (hN : 1 ≤ N) : fsK N * N ≤ 8 + slV N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hδN : deltaU N * N ≤ 1 := by
    unfold deltaU; rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  unfold fsK
  rw [add_mul, div_mul_cancel₀ _ hNr.ne']
  have := Real.log_two_lt_d9
  nlinarith

lemma fsK_mul_nonneg : 0 ≤ fsK N * N := by
  unfold fsK deltaU slV; have := Real.log_pos one_lt_two; positivity

lemma unif_univ : unif Set.univ = 1 := by
  unfold unif; rw [Measure.restrict_apply_univ, Real.volume_Icc]; norm_num

/-- The common final form. -/
lemma fs_final (hN : 1 ≤ N) {l lam I J B : ℝ} (hl0 : 0 ≤ l) (hl : l ≤ 8) (hlam0 : 0 ≤ lam)
    (hlam : lam ≤ 17) (hI : 0 ≤ I) (hJ0 : 0 ≤ J)
    (hJ : J ≤ Real.exp (lam * fsK N) * (I + fsc1 * deltaU N)) (hB : B ≤ x0 * N + 2 * slT N) :
    Real.exp (l * B) * J ^ N ≤
      Real.exp (l * x0 * N) * Real.exp (16 * slT N + 17 * (8 + slV N)) * (I + fsc1 * deltaU N) ^ N := by
  have hδ0 : 0 ≤ deltaU N := by unfold deltaU; positivity
  have hA : 0 ≤ I + fsc1 * deltaU N := add_nonneg hI (mul_nonneg fsc1_nonneg hδ0)
  have hslT : 0 ≤ slT N := by
    unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    linarith
  have hKN := fsK_mul_le hN
  have hKN0 := fsK_mul_nonneg (N := N)
  have h1 : J ^ N ≤ Real.exp (lam * (fsK N * N)) * (I + fsc1 * deltaU N) ^ N := by
    calc J ^ N ≤ (Real.exp (lam * fsK N) * (I + fsc1 * deltaU N)) ^ N := pow_le_pow_left₀ hJ0 hJ N
      _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
  have h2 : Real.exp (l * B) ≤ Real.exp (l * x0 * N) * Real.exp (16 * slT N) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hB hl0
    nlinarith
  have h3 : Real.exp (lam * (fsK N * N)) ≤ Real.exp (17 * (8 + slV N)) := by
    apply Real.exp_le_exp.2; nlinarith
  calc Real.exp (l * B) * J ^ N
      ≤ (Real.exp (l * x0 * N) * Real.exp (16 * slT N)) *
          (Real.exp (17 * (8 + slV N)) * (I + fsc1 * deltaU N) ^ N) :=
        mul_le_mul h2 (h1.trans (mul_le_mul_of_nonneg_right h3 (pow_nonneg hA N))) (pow_nonneg hJ0 N)
          (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

/-! ### Cause side: `r0 = s` or `r0^x = s` -/

lemma fs_dummy (hN : 2 ≤ N) (x : Fin N) : ∃ x' : Fin N, x' ≠ x := by
  by_cases h : x = ⟨0, by omega⟩
  · exact ⟨⟨1, by omega⟩, by rw [h]; simp⟩
  · exact ⟨⟨0, by omega⟩, Ne.symm h⟩

lemma fs_flip_ne {x x' : Fin N} (hx : x' ≠ x) (r : State N) : flipAt x r ≠ flipAt x' r := by
  intro he
  have := congrFun he x
  simp [flipAt, Function.update, hx.symm, Ne.symm hx] at this

/-- **One cause cell with a row coincidence** (no distinctness of `s` needed). -/
theorem fs_cause_cell (hN : 2 ≤ N) (s r0 : State N) (x : Fin N) {c : ℚ × ℚ}
    (hc : c ∈ cellsXCauseData) :
    ∃ C ∈ rsCellsC, cubeM N {w : Param N | CellEvX N s r0 x .cause c w} ≤
      ENNReal.ofReal (Real.exp ((C.P : ℝ) / 4 * x0 * N) * Real.exp (16 * slT N + 17 * (8 + slV N)) *
        (fsI C + fsc1 * deltaU N) ^ N) := by
  have hN0 : 0 < N := by omega
  have hall := rsLink_all
  rw [List.all_eq_true] at hall
  obtain ⟨C, hC, hlink⟩ := List.any_eq_true.1 (hall c hc)
  refine ⟨C, hC, ?_⟩
  have hok : rsCellOK C = true := (List.all_eq_true.1 rsCellsC_ok) C hC
  have hb := (List.all_eq_true.1 rsBounds) C hC
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨hlam, hlu⟩, hP⟩ := hb
  simp only [rsLink, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hlink
  obtain ⟨⟨hv4, hcap⟩, hc2⟩ := hlink
  have hok' := hok
  simp only [rsCellOK, Bool.and_eq_true, decide_eq_true_eq] at hok'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hvw⟩, hw1⟩, hv1⟩, hw2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok'
  set c' : ℚ × ℚ := (C.v ^ 4, C.w ^ 4) with hc'
  have hmono := cellEvX_mono hN0 s r0 x (c := c) (c' := c') (by simp only [hc']; exact_mod_cast hv4)
    (by
      rcases hcap with h | h
      · left; simp only [hc']; exact_mod_cast h
      · right; simp only [hc', h]; norm_num)
    (by exact_mod_cast hc2) (by
      simp only [hc']; push_cast
      exact pow_pos (by exact_mod_cast (lt_of_lt_of_le hv hvw)) 4)
  refine (measure_mono hmono).trans ?_
  have hcm' : (1 : ℝ) / 2 ≤ (c'.2 : ℝ) := by
    simp only [hc']; have := (Rat.cast_le (K := ℝ)).2 hw2; push_cast at this ⊢; exact this
  have hm0' : (0 : ℝ) < (c'.1 : ℝ) := by
    simp only [hc']; push_cast; exact pow_pos (by exact_mod_cast hv) 4
  have hm1' : (c'.1 : ℝ) ≤ 1 := by
    simp only [hc']; push_cast
    exact pow_le_one₀ (by exact_mod_cast hv.le) (by exact_mod_cast hv1.le)
  -- the dummy third row
  obtain ⟨x', hx'⟩ := fs_dummy hN x
  set d := flipAt x' r0 with hd
  have hsub := cellEvX_sub_template hN0 s r0 x c' hcm'
  have hW : MeasurableSet {y : ℝ | (c'.1 : ℝ) ≤ clamp01 y} :=
    measurableSet_le measurable_const clamp01_measurable
  have hsub2 : {w : Param N | CellEvX N s r0 x .cause c' w} ⊆
      {w | (∀ i, w ((fun _ : Fin N => r0) i) i ∈ {y : ℝ | (c'.1 : ℝ) ≤ clamp01 y}) ∧
        ∑ i, (fun y => -Real.log (clamp01 y)) (w ((fun _ : Fin N => r0) i) i) ≤ x0 * N + slT N ∧
        ∑ i, (fun _ : ℝ => (0 : ℝ)) (w ((fun _ : Fin N => d) i) i) ≤
          ∑ i, (fun y => -Real.log (clamp01 y)) (w ((fun _ : Fin N => r0) i) i) ∧
        ∑ i, gXev N c' (w ((fun _ : Fin N => r0) i) i) (w ((fun _ : Fin N => flipAt x r0) i) i) ≤ 0} := by
    intro w hw
    obtain ⟨h1, h2, -, h4⟩ := hsub hw
    refine ⟨h1, h2, ?_, h4⟩
    simp only [sum_const_zero]
    exact sum_nonneg fun i _ => neg_nonneg.2 (Real.log_nonpos (clamp01_nonneg _) (clamp01_le_one _))
  have hell : Measurable fun y : ℝ => -Real.log (clamp01 y) :=
    (Real.measurable_log.comp clamp01_measurable).neg
  have hg : Measurable fun p : ℝ × ℝ => gXev N c' p.1 p.2 := by
    unfold gXev
    have hy : Measurable fun p : ℝ × ℝ => clamp01 p.1 := clamp01_measurable.comp measurable_fst
    have hu : Measurable fun p : ℝ × ℝ => clamp01 p.2 := clamp01_measurable.comp measurable_snd
    refine (Measurable.min ?_ ?_).sub_const _
    · exact Real.measurable_log.comp ((measurable_const.mul hy).div (hy.add hu))
    · exact (measurable_const.max (Real.measurable_log.comp (hy.div_const _))).sub_const _
  set I := fsI C with hIdef
  have hIpos : 0 < I := fs_cell_pos C hok
  have hI' : (∫ y in (c'.1 : ℝ)..1, y ^ ((C.P : ℝ) / 4 - 0) * gX C.lam (c'.2 : ℝ) y) = I := by
    simp only [hc', sub_zero, hIdef, fsI]; push_cast; rfl
  have hJ := cell_J_le (N := N) C.lam c' hcm' hm0' hm1' (t := (C.P : ℝ) / 4) (lamU := 0) (by positivity)
  rw [hI'] at hJ
  have hE : ∫⁻ x, ENNReal.ofReal (Real.exp (-(0 : ℝ) * (fun _ : ℝ => (0 : ℝ)) x)) ∂unif ≤
      ENNReal.ofReal 1 := by
    simp only [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, lintegral_const, unif_univ, mul_one]
    exact le_rfl
  have hT := joint_template_real (fun _ => r0) (fun _ => flipAt x r0) (fun _ => d)
    (fun _ => (flipAt_ne x r0).symm) (fun _ => (flipAt_ne x' r0).symm) (fun _ => fs_flip_ne hx' r0)
    (fun y => -Real.log (clamp01 y)) (fun _ => 0) (gXev N c') hell measurable_const hg _ hW
    (x0 * N + slT N) ((C.P : ℝ) / 4) 0 C.lam (by positivity) le_rfl (Nat.cast_nonneg _)
    (J := Real.exp ((C.lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) * I) (Ex := 1)
    (by positivity) zero_le_one hJ hE
  refine (measure_mono hsub2).trans (hT.trans (ENNReal.ofReal_le_ofReal ?_))
  rw [mul_one]
  have hl8 : (C.P : ℝ) / 4 ≤ 8 := by
    have : (C.P : ℝ) ≤ 30 := by exact_mod_cast hP
    linarith
  have hslT : 0 ≤ slT N := by
    unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    linarith
  refine fs_final (by omega) (by positivity) hl8 (Nat.cast_nonneg _) (by exact_mod_cast hlam) hIpos.le
    (by positivity) ?_ (by linarith)
  have hδ0 : 0 ≤ deltaU N := by unfold deltaU; positivity
  unfold fsK
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg fsc1_nonneg hδ0)) (Real.exp_pos _).le

/-! ### Effect side: common pointwise bounds -/

lemma fs_X_bounds (y : ℝ) : 1 / 2 ≤ max (clamp01 y) (1 - clamp01 y) ∧ max (clamp01 y) (1 - clamp01 y) ≤ 1 := by
  have h0 := clamp01_nonneg y; have h1 := clamp01_le_one y
  refine ⟨?_, max_le h1 (by linarith)⟩
  by_cases h : clamp01 y ≤ 1 / 2
  · exact le_trans (by linarith) (le_max_right _ _)
  · exact le_trans (by linarith) (le_max_left _ _)

lemma fs_gE_lower (c : ℚ × ℚ) (y u : ℝ) : -Real.log (3 / 2) - fsK N ≤ gXevE N c y u := by
  obtain ⟨hX1, hX2⟩ := fs_X_bounds y
  set X := max (clamp01 y) (1 - clamp01 y) with hX
  set p := (if 1 / 2 < clamp01 y then clamp01 u else 1 - clamp01 u) with hp
  have hp0 : 0 ≤ p := by
    simp only [hp]; split_ifs
    · exact clamp01_nonneg u
    · linarith [clamp01_le_one u]
  have hp1 : p ≤ 1 := by
    simp only [hp]; split_ifs
    · exact clamp01_le_one u
    · linarith [clamp01_nonneg u]
  have hA : -Real.log (3 / 2) ≤ Real.log (2 * X / (X + p)) := by
    rw [← Real.log_inv, show ((3 / 2 : ℝ))⁻¹ = 2 / 3 by norm_num]
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have hδ0 : 0 ≤ deltaU N := by unfold deltaU; positivity
  have hl0 : 0 ≤ Real.log (3 / 2) := Real.log_nonneg (by norm_num)
  have hB : -Real.log (3 / 2) - 7 * deltaU N ≤ max 0 (Real.log (X / (c.2 : ℝ))) - 7 * deltaU N := by
    have := le_max_left 0 (Real.log (X / (c.2 : ℝ))); linarith
  have hmin : -Real.log (3 / 2) - 7 * deltaU N ≤
      min (Real.log (2 * X / (X + p))) (max 0 (Real.log (X / (c.2 : ℝ))) - 7 * deltaU N) :=
    le_min (by linarith) hB
  show -Real.log (3 / 2) - fsK N ≤
    min (Real.log (2 * X / (X + p))) (max 0 (Real.log (X / (c.2 : ℝ))) - 7 * deltaU N) -
      (slV N + Real.log 2) / N
  unfold fsK; linarith

lemma fs_gE_exp_le (lam : ℕ) (c : ℚ × ℚ) (y u : ℝ) :
    Real.exp (-(lam : ℝ) * gXevE N c y u) ≤ (3 / 2 : ℝ) ^ lam * Real.exp (lam * fsK N) := by
  have h := fs_gE_lower (N := N) c y u
  have hl : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
  rw [← Real.exp_log (show (0 : ℝ) < (3 / 2) ^ lam by positivity), ← Real.exp_add, Real.log_pow]
  apply Real.exp_le_exp.2
  nlinarith

lemma fs_gE_meas (c : ℚ × ℚ) : Measurable fun p : ℝ × ℝ => gXevE N c p.1 p.2 := by
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

lemma fs_inner_le_H (lam : ℕ) (c : ℚ × ℚ) (y : ℝ) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u)) ∂unif ≤
      ENNReal.ofReal ((3 / 2 : ℝ) ^ lam * Real.exp (lam * fsK N)) := by
  calc ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u)) ∂unif
      ≤ ∫⁻ _u, ENNReal.ofReal ((3 / 2 : ℝ) ^ lam * Real.exp (lam * fsK N)) ∂unif :=
        lintegral_mono fun u => ENNReal.ofReal_le_ofReal (fs_gE_exp_le lam c y u)
    _ = _ := by rw [lintegral_const, unif_univ, mul_one]

/-- `∫⁻_{[b,1]} A y^t gX = ofReal(A ∫_b^1 y^t gX)`. -/
lemma fs_lint_gX (lam : ℕ) {cm : ℝ} (hcm : 1 / 2 ≤ cm) {t : ℝ} (ht : 0 ≤ t) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b ≤ 1) (A : ℝ) (hA : 0 ≤ A) :
    ∫⁻ y in Set.Icc b 1, ENNReal.ofReal (A * (y ^ t * gX lam cm y)) =
      ENNReal.ofReal (A * ∫ y in b..1, y ^ t * gX lam cm y) := by
  have hcont : ContinuousOn (fun y => A * (y ^ t * gX lam cm y)) (Set.Icc b 1) :=
    continuousOn_const.mul ((ContinuousOn.rpow_const continuousOn_id fun y _ => Or.inr ht).mul
      (gX_continuousOn lam _ hb0))
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)]
  · rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb1,
      intervalIntegral.integral_const_mul]
  · refine Filter.eventually_of_mem (ae_restrict_mem measurableSet_Icc) fun y hy => ?_
    have hy0 : 0 < y := lt_of_lt_of_le hb0 hy.1
    exact mul_nonneg hA (mul_nonneg (Real.rpow_nonneg hy0.le _)
      (gX_nonneg lam hy0 hy.2 (by linarith) (by have := hy.2; linarith)))

lemma fs_I_nonneg (lam : ℕ) {cm : ℝ} (hcm : 1 / 2 ≤ cm) {t : ℝ} {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) :
    0 ≤ ∫ y in b..1, y ^ t * gX lam cm y :=
  intervalIntegral.integral_nonneg hb1 fun y hy =>
    mul_nonneg (Real.rpow_nonneg (by linarith [hy.1]) _)
      (gX_nonneg lam (by linarith [hy.1]) hy.2 (by linarith) (by linarith [hy.2]))

/-! ### Effect side, `r0 = s`: the column factor -/

lemma fs_colE1 (lam : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) {t : ℝ} (ht : 0 ≤ t) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b ≤ 1) (hb : b ≤ max (1 / 2) (c.1 : ℝ)) :
    ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y) ∧ 1 / 2 - deltaU N ≤ y},
        ENNReal.ofReal (Real.exp (-(t * -Real.log (clamp01 y)))) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u)) ∂unif ∂unif ≤
      ENNReal.ofReal (Real.exp (lam * fsK N) * (∫ y in b..1, y ^ t * gX lam (c.2 : ℝ) y) +
        deltaU N * ((3 / 2 : ℝ) ^ lam * Real.exp (lam * fsK N))) := by
  have hδ0 : 0 < deltaU N := by unfold deltaU; positivity
  set W := {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y) ∧ 1 / 2 - deltaU N ≤ y} with hWdef
  have hW : MeasurableSet W :=
    (measurableSet_le measurable_const (clamp01_measurable.max (measurable_const.sub clamp01_measurable))).inter
      (measurableSet_le measurable_const measurable_id)
  set H := (3 / 2 : ℝ) ^ lam * Real.exp (lam * fsK N) with hH
  have hH0 : 0 ≤ H := by positivity
  set F : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp (-(t * -Real.log (clamp01 y)))) *
      ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u)) ∂unif with hF
  have hcover : W ∩ Set.Icc 0 1 ⊆ (Set.Icc b 1 ∩ Set.Ioi (1 / 2)) ∪ Set.Icc (1 / 2 - deltaU N) (1 / 2) := by
    rintro y ⟨⟨hy1, hy2⟩, hy3⟩
    by_cases h : 1 / 2 < y
    · left
      have hcy : clamp01 y = y := by unfold clamp01; rw [min_eq_right hy3.2, max_eq_right hy3.1]
      have hX : max (clamp01 y) (1 - clamp01 y) = y := by rw [hcy]; exact max_eq_left (by linarith)
      rw [hX] at hy1
      exact ⟨⟨hb.trans (max_le h.le hy1), hy3.2⟩, h⟩
    · right; exact ⟨hy2, not_lt.1 h⟩
  have hhi : ∀ y ∈ Set.Icc b 1 ∩ Set.Ioi (1 / 2),
      F y ≤ ENNReal.ofReal (Real.exp (lam * fsK N) * (y ^ t * gX lam (c.2 : ℝ) y)) := by
    rintro y ⟨hy, hy2⟩
    have hy2' : (1 : ℝ) / 2 < y := hy2
    have hy0 : 0 < y := lt_trans (by norm_num) hy2'
    have hcy : clamp01 y = y := by unfold clamp01; rw [min_eq_right hy.2, max_eq_right hy0.le]
    have hX : max (clamp01 y) (1 - clamp01 y) = y := by
      rw [hcy]; exact max_eq_left (by linarith)
    have hin := inner_mgf_le_eff (N := N) lam c hcm y
    rw [hX] at hin
    have he : Real.exp (-(t * -Real.log (clamp01 y))) = y ^ t := by
      rw [hcy, Real.rpow_def_of_pos hy0]; ring_nf
    simp only [hF, he]
    calc ENNReal.ofReal (y ^ t) * ∫⁻ u, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u)) ∂unif
        ≤ ENNReal.ofReal (y ^ t) * ENNReal.ofReal (Real.exp ((lam : ℝ) * (7 * deltaU N +
            (slV N + Real.log 2) / N)) * gX lam (c.2 : ℝ) y) := by gcongr
      _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy0.le _)]; congr 1; unfold fsK; ring
  have hlo : ∀ y ∈ Set.Icc (1 / 2 - deltaU N) (1 / 2), F y ≤ ENNReal.ofReal H := by
    intro y _
    have h1 : Real.exp (-(t * -Real.log (clamp01 y))) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have := Real.log_nonpos (clamp01_nonneg y) (clamp01_le_one y)
      nlinarith
    calc F y ≤ ENNReal.ofReal 1 * ENNReal.ofReal H := by
          simp only [hF]; gcongr; exact fs_inner_le_H lam c y
      _ = ENNReal.ofReal H := by rw [ENNReal.ofReal_one, one_mul]
  unfold unif
  rw [Measure.restrict_restrict hW]
  calc ∫⁻ y in W ∩ Set.Icc 0 1, F y
      ≤ ∫⁻ y in (Set.Icc b 1 ∩ Set.Ioi (1 / 2)) ∪ Set.Icc (1 / 2 - deltaU N) (1 / 2), F y :=
        lintegral_mono_set hcover
    _ ≤ (∫⁻ y in Set.Icc b 1 ∩ Set.Ioi (1 / 2), F y) + ∫⁻ y in Set.Icc (1 / 2 - deltaU N) (1 / 2), F y :=
        lintegral_union_le _ _ _
    _ ≤ (∫⁻ y in Set.Icc b 1, ENNReal.ofReal (Real.exp (lam * fsK N) * (y ^ t * gX lam (c.2 : ℝ) y))) +
          ∫⁻ _y in Set.Icc (1 / 2 - deltaU N) (1 / 2), ENNReal.ofReal H :=
        add_le_add ((setLIntegral_mono' (measurableSet_Icc.inter measurableSet_Ioi) hhi).trans
            (lintegral_mono_set Set.inter_subset_left)) (setLIntegral_mono' measurableSet_Icc hlo)
    _ = ENNReal.ofReal (Real.exp (lam * fsK N) * ∫ y in b..1, y ^ t * gX lam (c.2 : ℝ) y) +
          ENNReal.ofReal (deltaU N * H) := by
        rw [fs_lint_gX lam hcm ht hb0 hb1 _ (Real.exp_pos _).le, setLIntegral_const, Real.volume_Icc,
          ← ENNReal.ofReal_mul hH0, mul_comm H]
        congr 3; ring
    _ = _ := by
        rw [← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le (fs_I_nonneg lam hcm hb0 hb1))
          (by positivity)]

/-- The certified partner of an effect cell, unpacked. -/
lemma fs_eff_partner {c : ℚ × ℚ} (hc : c ∈ cellsXEffectData) :
    ∃ C ∈ rsCellsE, rsCellOK C = true ∧ C.lam ≤ 17 ∧ C.lu ≤ 3 ∧ C.P ≤ 30 ∧
      (0 : ℝ) < C.v ∧ (C.v : ℝ) < 1 ∧ (1 : ℝ) / 2 ≤ (C.w : ℝ) ^ 4 ∧
      (C.v : ℝ) ^ 4 ≤ max (1 / 2) (c.1 : ℝ) ∧
      ((c.2 : ℝ) ≤ (C.w : ℝ) ^ 4 ∨ (C.w : ℝ) ^ 4 = 1) ∧ (1 : ℝ) / 2 ≤ c.2 := by
  have hall := rsLinkE_all
  rw [List.all_eq_true] at hall
  obtain ⟨C, hC, hlink⟩ := List.any_eq_true.1 (hall c hc)
  have hok : rsCellOK C = true := (List.all_eq_true.1 rsCellsE_ok) C hC
  have hb := (List.all_eq_true.1 rsBoundsE) C hC
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨hlam, hlu⟩, hP⟩ := hb
  simp only [rsLinkE, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hlink
  obtain ⟨⟨hv4, hcap⟩, hc2⟩ := hlink
  have hok' := hok
  simp only [rsCellOK, Bool.and_eq_true, decide_eq_true_eq] at hok'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hvw⟩, hw1⟩, hv1⟩, hw2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok'
  refine ⟨C, hC, hok, hlam, hlu, hP, by exact_mod_cast hv, by exact_mod_cast hv1, ?_, ?_, ?_, ?_⟩
  · have := (Rat.cast_le (K := ℝ)).2 hw2; push_cast at this; exact this
  · have := (Rat.cast_le (K := ℝ)).2 hv4; push_cast at this; exact this
  · rcases hcap with h | h
    · left; have := (Rat.cast_le (K := ℝ)).2 h; push_cast at this; exact this
    · right; rw [h]; norm_num
  · have := (Rat.cast_le (K := ℝ)).2 hc2; push_cast at this; exact this

lemma fs_I_eq (C : RSCell) :
    (∫ y in ((C.v : ℝ) ^ 4)..1, y ^ ((C.P : ℝ) / 4) * gX C.lam ((C.w : ℝ) ^ 4) y) = fsI C := rfl

/-- The `fs_final` hypothesis from a column bound with the `δ (3/2)^λ` term. -/
lemma fs_J_le (lam : ℕ) (hlam : lam ≤ 17) (I : ℝ) (k : ℝ) (hk0 : 0 ≤ k) (hk : k ≤ 4) :
    Real.exp (lam * fsK N) * I + k * deltaU N * ((3 / 2 : ℝ) ^ lam * Real.exp (lam * fsK N)) ≤
      Real.exp (lam * fsK N) * (I + fsc1 * deltaU N) := by
  have hδ0 : 0 ≤ deltaU N := by unfold deltaU; positivity
  have h1 : (3 / 2 : ℝ) ^ lam ≤ (3 / 2) ^ 17 := pow_le_pow_right₀ (by norm_num) hlam
  have h2 : k * (3 / 2 : ℝ) ^ lam ≤ fsc1 := by
    unfold fsc1; exact mul_le_mul hk h1 (by positivity) (by norm_num)
  have he := Real.exp_pos (lam * fsK N)
  have : k * deltaU N * ((3 / 2 : ℝ) ^ lam * Real.exp (lam * fsK N)) =
      Real.exp (lam * fsK N) * ((k * (3 / 2 : ℝ) ^ lam) * deltaU N) := by ring
  rw [this, mul_add]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hδ0) he.le)

/-- **One effect cell with `r0 = s`.** -/
theorem fs_effS_cell (hN : 2 ≤ N) (hδ : deltaU N < 1 / 2) (s : State N) (x : Fin N) {c : ℚ × ℚ}
    (hc : c ∈ cellsXEffectData) :
    ∃ C ∈ rsCellsE, cubeM N {w : Param N | CellEvX N s s x .effect c w} ≤
      ENNReal.ofReal (Real.exp ((C.P : ℝ) / 4 * x0 * N) * Real.exp (16 * slT N + 17 * (8 + slV N)) *
        (fsI C + fsc1 * deltaU N) ^ N) := by
  have hN0 : 0 < N := by omega
  obtain ⟨C, hC, hok, hlam, hlu, hP, hv, hv1, hw4, hb, hcap, hc2⟩ := fs_eff_partner hc
  refine ⟨C, hC, ?_⟩
  set c' : ℚ × ℚ := (c.1, C.w ^ 4) with hc'
  have hc'2 : (c'.2 : ℝ) = (C.w : ℝ) ^ 4 := by simp only [hc']; push_cast; rfl
  have hcm' : (1 : ℝ) / 2 ≤ (c'.2 : ℝ) := by rw [hc'2]; exact hw4
  have hmono := cellEvX_mono_eff s s x (c := c) (c' := c') (by simp only [hc'])
    (by rw [hc'2]; exact hcap) (by linarith) (by linarith)
  refine (measure_mono hmono).trans ?_
  have hsub := cellEvX_eff_sub_template hN0 s s x c' hcm' hδ
  obtain ⟨x', hx'⟩ := fs_dummy hN x
  set d := flipAt x' s with hd
  set t : ℝ := (C.P : ℝ) / 4 with htdef
  have ht0 : 0 ≤ t := by positivity
  set W' : Set ℝ := {y : ℝ | (c'.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y) ∧ 1 / 2 - deltaU N ≤ y} with hW'def
  have hW' : MeasurableSet W' :=
    (measurableSet_le measurable_const (clamp01_measurable.max (measurable_const.sub clamp01_measurable))).inter
      (measurableSet_le measurable_const measurable_id)
  set f : Fin 2 → Fin N → ℝ × ℝ × ℝ → ℝ :=
    ![fun _ p => -Real.log (clamp01 p.1), fun _ p => gXevE N c' p.1 p.2.1] with hf
  have hfm : ∀ k i, Measurable (f k i) := by
    intro k i
    fin_cases k
    · exact (Real.measurable_log.comp (clamp01_measurable.comp measurable_fst)).neg
    · exact (fs_gE_meas c').comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  set a : Fin 2 → ℝ := ![x0 * N + slT N, 0] with ha
  set tt : Fin 2 → ℝ := ![t, (C.lam : ℝ)] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 2)), 0 ≤ tt k := by
    intro k _; fin_cases k
    · simpa [htt] using ht0
    · simp [htt]
  have hmain := cubeM_chernoff_three (fun _ => s) (fun _ => flipAt x s) (fun _ => d)
    (fun _ => (flipAt_ne x s).symm) (fun _ => (flipAt_ne x' s).symm) (fun _ => fs_flip_ne hx' s)
    univ f hfm a tt htt0 (fun _ => W') (fun _ => hW')
  -- the event inside the Chernoff event
  have hsub2 : {w : Param N | CellEvX N s s x .effect c' w} ⊆
      {w | (∀ i, w ((fun _ : Fin N => s) i) i ∈ (fun _ : Fin N => W') i) ∧
        ∀ k ∈ (univ : Finset (Fin 2)), ∑ i, f k i (w ((fun _ : Fin N => s) i) i,
          w ((fun _ : Fin N => flipAt x s) i) i, w ((fun _ : Fin N => d) i) i) ≤ a k} := by
    intro w hw
    obtain ⟨h1, h2, -, h4, h5⟩ := hsub hw
    refine ⟨fun i => ⟨h1 i, h5 i⟩, fun k _ => ?_⟩
    fin_cases k
    · simpa [hf, ha] using h2
    · simpa [hf, ha] using h4
  -- the column factor
  set J : ℝ := Real.exp (C.lam * fsK N) * fsI C + 1 * deltaU N * ((3 / 2 : ℝ) ^ C.lam * Real.exp (C.lam * fsK N))
    with hJdef
  have hcol : ∀ i : Fin N, ∫⁻ y in (fun _ : Fin N => W') i, ∫⁻ u, ∫⁻ z,
      ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 2)), tt k * f k i (y, u, z))) ∂unif ∂unif ∂unif ≤
        ENNReal.ofReal J := by
    intro i
    have hcong : ∀ y, ∫⁻ u, ∫⁻ z, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 2)),
        tt k * f k i (y, u, z))) ∂unif ∂unif =
        ENNReal.ofReal (Real.exp (-(t * -Real.log (clamp01 y)))) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXevE N c' y u)) ∂unif := by
      intro y
      have hgm : Measurable fun u => ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXevE N c' y u)) :=
        ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          (((fs_gE_meas c').comp (measurable_const.prodMk measurable_id)).const_mul _))
      rw [← lintegral_const_mul _ hgm]
      refine lintegral_congr fun u => ?_
      have hz : ∀ z, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 2)), tt k * f k i (y, u, z))) =
          ENNReal.ofReal (Real.exp (-(t * -Real.log (clamp01 y)))) *
            ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXevE N c' y u)) := by
        intro z
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        simp [Fin.sum_univ_two, hf, htt]
        ring
      rw [lintegral_congr hz, lintegral_const, unif_univ, mul_one]
    simp only [hcong]
    have hb0 : (0 : ℝ) < (C.v : ℝ) ^ 4 := by positivity
    have hb1 : (C.v : ℝ) ^ 4 ≤ 1 := pow_le_one₀ hv.le hv1.le
    have := fs_colE1 (N := N) C.lam c' hcm' ht0 hb0 hb1 (by simpa [hc'] using hb)
    rw [hc'2] at this
    refine this.trans (le_of_eq ?_)
    simp only [hJdef, one_mul]
    rfl
  refine (measure_mono hsub2).trans (hmain.trans ?_)
  have hsum : ∑ k ∈ (univ : Finset (Fin 2)), tt k * a k = t * (x0 * N + slT N) := by
    simp [Fin.sum_univ_two, htt, ha]
  rw [hsum]
  have hJ0 : 0 ≤ J := by
    have := fs_cell_pos C hok
    have hδ0 : 0 ≤ deltaU N := by unfold deltaU; positivity
    simp only [hJdef]
    exact add_nonneg (mul_nonneg (Real.exp_pos _).le this.le) (by positivity)
  calc ENNReal.ofReal (Real.exp (t * (x0 * N + slT N))) * ∏ i : Fin N, ∫⁻ y in (fun _ : Fin N => W') i,
        ∫⁻ u, ∫⁻ z, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 2)), tt k * f k i (y, u, z)))
          ∂unif ∂unif ∂unif
      ≤ ENNReal.ofReal (Real.exp (t * (x0 * N + slT N))) * ∏ _i : Fin N, ENNReal.ofReal J :=
        by gcongr with i; exact hcol i
    _ = ENNReal.ofReal (Real.exp (t * (x0 * N + slT N)) * J ^ N) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow hJ0,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hl8 : t ≤ 8 := by
          have : (C.P : ℝ) ≤ 30 := by exact_mod_cast hP
          simp only [htdef]; linarith
        have hslT : 0 ≤ slT N := by
          unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
          linarith
        exact fs_final (by omega) ht0 hl8 (Nat.cast_nonneg _) (by exact_mod_cast hlam)
          (fs_cell_pos C hok).le hJ0 (fs_J_le C.lam hlam _ 1 zero_le_one (by norm_num)) (by linarith)

/-! ### Effect side, `r0 = s^x`: the column factor (pairing `y` with `1 - y`) -/

lemma fs_clamp_of_mem {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) : clamp01 y = y := by
  unfold clamp01; rw [min_eq_right hy.2, max_eq_right hy.1]

lemma fs_X_reflect {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    max (clamp01 (1 - y)) (1 - clamp01 (1 - y)) = max (clamp01 y) (1 - clamp01 y) := by
  rw [fs_clamp_of_mem hy, fs_clamp_of_mem ⟨by linarith [hy.2], by linarith [hy.1]⟩, sub_sub_cancel,
    max_comm]

/-- `g(1-y, u) = g(y, 1-u)` for `y ∈ (1/2, 1]`, `u ∈ [0,1]`. -/
lemma fs_gE_reflect (c : ℚ × ℚ) {y u : ℝ} (hy : y ∈ Set.Ioc (1 / 2 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    gXevE N c (1 - y) u = gXevE N c y (1 - u) := by
  have hy' : y ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hX := fs_X_reflect hy'
  have hcy := fs_clamp_of_mem hy'
  have hc1y : clamp01 (1 - y) = 1 - y := fs_clamp_of_mem ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hcu := fs_clamp_of_mem hu
  have hc1u : clamp01 (1 - u) = 1 - u := fs_clamp_of_mem ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have h1 : ¬ (1 / 2 < clamp01 (1 - y)) := by rw [hc1y]; linarith [hy.1]
  have h2 : 1 / 2 < clamp01 y := by rw [hcy]; exact hy.1
  unfold gXevE
  rw [hX, if_neg h1, if_pos h2, hcu, hc1u]

/-- **Pairing**: `Ψ(y) + Ψ(1-y) ≤ e^{λK} gX(y)` for `y ∈ (1/2, 1]`. -/
lemma fs_pair (lam : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) {y : ℝ} (hy : y ∈ Set.Ioc (1 / 2 : ℝ) 1) :
    (∫⁻ u in Set.Icc (1 / 2 : ℝ) 1, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u))) +
      (∫⁻ u in Set.Icc (1 / 2 : ℝ) 1, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c (1 - y) u))) ≤
      ENNReal.ofReal (Real.exp (lam * fsK N) * gX lam (c.2 : ℝ) y) := by
  set F : ℝ → ENNReal := fun u => ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u)) with hF
  have hFm : Measurable F :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((fs_gE_meas c).comp (measurable_const.prodMk measurable_id)).const_mul _))
  have h1 : (∫⁻ u in Set.Icc (1 / 2 : ℝ) 1, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c (1 - y) u))) =
      ∫⁻ u in Set.Icc (0 : ℝ) (1 / 2), F u := by
    rw [setLIntegral_congr_fun measurableSet_Icc (g := fun u => F (1 - u)) fun u hu => by
      simp only [hF]; rw [fs_gE_reflect c hy ⟨by linarith [hu.1], hu.2⟩]]
    have := setLIntegral_reflect_half (fun v => F (1 - v)) (hFm.comp (measurable_const.sub measurable_id))
    simp only [sub_sub_cancel] at this
    exact this.symm
  rw [h1, add_comm, ← setLIntegral_congr (Ico_ae_eq_Icc (a := (0 : ℝ)) (b := 1 / 2)),
    ← lintegral_union measurableSet_Icc (Set.disjoint_left.2 fun u hu hu' => by
      have := hu.2; have := hu'.1; linarith),
    Set.Ico_union_Icc_eq_Icc (by norm_num) (by norm_num)]
  have hin := inner_mgf_le_eff (N := N) lam c hcm y
  have hy' : y ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hX : max (clamp01 y) (1 - clamp01 y) = y := by
    rw [fs_clamp_of_mem hy']; exact max_eq_left (by linarith [hy.1])
  rw [hX] at hin
  unfold unif at hin
  refine hin.trans (le_of_eq ?_)
  unfold fsK; rfl

/-- `Φ ≤ Ψ + 2δH`: the floor indicator with weight `e^{-μ} = δ`. -/
lemma fs_floor_le (lam : ℕ) (c : ℚ × ℚ) (hδ : deltaU N < 1 / 2) (y : ℝ) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (-(Real.log ((N : ℝ) + 1) * Set.indicator (Set.Iio (1 / 2 - deltaU N)) 1 u))) *
        ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u)) ∂unif ≤
      (∫⁻ u in Set.Icc (1 / 2 : ℝ) 1, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u))) +
        ENNReal.ofReal (2 * deltaU N * ((3 / 2 : ℝ) ^ lam * Real.exp (lam * fsK N))) := by
  have hδ0 : 0 < deltaU N := by unfold deltaU; positivity
  set a := 1 / 2 - deltaU N with ha
  set H := (3 / 2 : ℝ) ^ lam * Real.exp (lam * fsK N) with hH
  have hH0 : 0 ≤ H := by positivity
  set F : ℝ → ENNReal := fun u => ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u)) with hF
  have hFm : Measurable F :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((fs_gE_meas c).comp (measurable_const.prodMk measurable_id)).const_mul _))
  have hFH : ∀ u, F u ≤ ENNReal.ofReal H := fun u => ENNReal.ofReal_le_ofReal (fs_gE_exp_le lam c y u)
  have hmu : Real.exp (-Real.log ((N : ℝ) + 1)) = deltaU N := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]; unfold deltaU; rw [one_div]
  set G : ℝ → ENNReal := fun u =>
    ENNReal.ofReal (Real.exp (-(Real.log ((N : ℝ) + 1) * Set.indicator (Set.Iio a) 1 u))) * F u with hG
  have hpt : ∀ u ∈ Set.Icc (0 : ℝ) 1, G u ≤ (Set.Icc (1 / 2 : ℝ) 1).indicator F u +
      (Set.Ico a (1 / 2)).indicator (fun _ => ENNReal.ofReal H) u + ENNReal.ofReal (deltaU N * H) := by
    intro u hu
    by_cases hua : u < a
    · have : G u ≤ ENNReal.ofReal (deltaU N) * ENNReal.ofReal H := by
        simp only [hG]
        rw [Set.indicator_of_mem (show u ∈ Set.Iio a from hua), Pi.one_apply, mul_one, hmu]
        exact mul_le_mul_right (hFH u) _
      rw [← ENNReal.ofReal_mul hδ0.le] at this
      exact this.trans le_add_self
    · have hind : Set.indicator (Set.Iio a) (1 : ℝ → ℝ) u = 0 :=
        Set.indicator_of_notMem (show u ∉ Set.Iio a from hua) _
      have hGF : G u = F u := by
        simp only [hG]; rw [hind, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul]
      rw [hGF]
      by_cases hu2 : u < 1 / 2
      · have : (Set.Ico a (1 / 2)).indicator (fun _ => ENNReal.ofReal H) u = ENNReal.ofReal H :=
          Set.indicator_of_mem (show u ∈ Set.Ico a (1 / 2) from ⟨not_lt.1 hua, hu2⟩) _
        rw [this]
        exact (hFH u).trans (le_trans le_add_self le_self_add)
      · have : (Set.Icc (1 / 2 : ℝ) 1).indicator F u = F u := Set.indicator_of_mem (show u ∈ Set.Icc (1 / 2 : ℝ) 1 from ⟨not_lt.1 hu2, hu.2⟩) _
        rw [this, add_assoc]; exact le_self_add
  have hm1 : Measurable ((Set.Icc (1 / 2 : ℝ) 1).indicator F) := hFm.indicator measurableSet_Icc
  have hm2 : Measurable ((Set.Ico a (1 / 2)).indicator (fun _ : ℝ => ENNReal.ofReal H)) :=
    measurable_const.indicator measurableSet_Ico
  unfold unif
  calc ∫⁻ u in Set.Icc (0 : ℝ) 1, G u
      ≤ ∫⁻ u in Set.Icc (0 : ℝ) 1, ((Set.Icc (1 / 2 : ℝ) 1).indicator F u +
          (Set.Ico a (1 / 2)).indicator (fun _ => ENNReal.ofReal H) u + ENNReal.ofReal (deltaU N * H)) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = (∫⁻ u in Set.Icc (0 : ℝ) 1, (Set.Icc (1 / 2 : ℝ) 1).indicator F u) +
          (∫⁻ u in Set.Icc (0 : ℝ) 1, (Set.Ico a (1 / 2)).indicator (fun _ => ENNReal.ofReal H) u) +
          ∫⁻ _u in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (deltaU N * H) := by
        have hm12 : Measurable fun u => (Set.Icc (1 / 2 : ℝ) 1).indicator F u +
            (Set.Ico a (1 / 2)).indicator (fun _ => ENNReal.ofReal H) u := hm1.add hm2
        rw [lintegral_add_left hm12, lintegral_add_left hm1]
    _ ≤ (∫⁻ u in Set.Icc (1 / 2 : ℝ) 1, F u) + ENNReal.ofReal (deltaU N * H) +
          ENNReal.ofReal (deltaU N * H) := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · rw [lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
          exact lintegral_mono_set Set.inter_subset_left
        · rw [lintegral_indicator measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico]
          refine (lintegral_mono_set Set.inter_subset_left).trans (le_of_eq ?_)
          rw [setLIntegral_const, Real.volume_Ico, ← ENNReal.ofReal_mul hH0, mul_comm]
          congr 2; rw [ha]; ring
        · rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
    _ = _ := by
        rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2; ring

lemma fs_ellSX_meas : Measurable (ellSX N) := by
  unfold ellSX
  exact ((Real.measurable_log.comp (clamp01_measurable.max
    (measurable_const.sub clamp01_measurable))).neg).sub_const _

/-- **The column factor for `r0 = s^x`.** -/
lemma fs_colE2 (lam : ℕ) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2) {l : ℝ} (hl : 0 ≤ l) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b ≤ 1) (hb : b ≤ max (1 / 2) (c.1 : ℝ)) (hδ : deltaU N < 1 / 2) :
    ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)},
        ENNReal.ofReal (Real.exp (-(l * ellSX N y))) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-(Real.log ((N : ℝ) + 1) *
              Set.indicator (Set.Iio (1 / 2 - deltaU N)) 1 u))) *
            ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u)) ∂unif ∂unif ≤
      ENNReal.ofReal (Real.exp (l * (slT N / N)) * (Real.exp (lam * fsK N) *
        (∫ y in b..1, y ^ l * gX lam (c.2 : ℝ) y) + 4 * deltaU N * ((3 / 2 : ℝ) ^ lam * Real.exp (lam * fsK N)))) := by
  have hδ0 : 0 < deltaU N := by unfold deltaU; positivity
  set W := {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} with hWdef
  have hW : MeasurableSet W :=
    measurableSet_le measurable_const (clamp01_measurable.max (measurable_const.sub clamp01_measurable))
  set H := (3 / 2 : ℝ) ^ lam * Real.exp (lam * fsK N) with hH
  have hH0 : 0 ≤ H := by positivity
  set E := Real.exp (l * (slT N / N)) with hE
  set K := Real.exp (lam * fsK N) with hK
  set A : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp (-(l * ellSX N y))) with hA
  set k2 : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (Real.exp (-(Real.log ((N : ℝ) + 1) *
      Set.indicator (Set.Iio (1 / 2 - deltaU N)) 1 p.2))) *
        ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c p.1 p.2)) with hk2
  have hk2m : Measurable k2 := by
    have h1 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(Real.log ((N : ℝ) + 1) *
        Set.indicator (Set.Iio (1 / 2 - deltaU N)) 1 p.2))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        ((((measurable_one.indicator measurableSet_Iio).comp measurable_snd).const_mul _).neg))
    have h2 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c p.1 p.2)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((fs_gE_meas c).const_mul _))
    exact h1.mul h2
  set Φ : ℝ → ENNReal := fun y => ∫⁻ u, k2 (y, u) ∂unif with hΦ
  have hΦm : Measurable Φ := hk2m.lintegral_prod_right'
  have hAm : Measurable A :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((fs_ellSX_meas.const_mul _).neg))
  set Q : ℝ → ENNReal := W.indicator fun y => A y * Φ y with hQ
  have hQm : Measurable Q := (hAm.mul hΦm).indicator hW
  set Ψ : ℝ → ENNReal := fun y =>
    ∫⁻ u in Set.Icc (1 / 2 : ℝ) 1, ENNReal.ofReal (Real.exp (-(lam : ℝ) * gXevE N c y u)) with hΨ
  set Bnd : ℝ → ENNReal := fun y => ENNReal.ofReal (E * K * (y ^ l * gX lam (c.2 : ℝ) y)) +
    ENNReal.ofReal (E * (4 * deltaU N * H)) with hBnd
  have hBm : Measurable Bnd := by
    refine Measurable.add (ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((measurable_id.pow_const l).mul (gX_measurable lam _)))) measurable_const
  -- the pointwise pairing bound
  have hpt : ∀ y ∈ Set.Ioc (1 / 2 : ℝ) 1, Q (1 - y) + Q y ≤ (Set.Icc b 1).indicator Bnd y := by
    intro y hy
    have hy01 : y ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
    have hy0 : 0 < y := by linarith [hy.1]
    have hXy : max (clamp01 y) (1 - clamp01 y) = y := by
      rw [fs_clamp_of_mem hy01]; exact max_eq_left (by linarith [hy.1])
    have hX1 : max (clamp01 (1 - y)) (1 - clamp01 (1 - y)) = y := by rw [fs_X_reflect hy01, hXy]
    by_cases hyW : y ∈ W
    · have hyW' : (c.1 : ℝ) ≤ y := by have := hyW; simp only [hWdef, Set.mem_ofPred_eq, hXy] at this; exact this
      have h1W : 1 - y ∈ W := by simp only [hWdef, Set.mem_ofPred_eq, hX1]; exact hyW'
      have hyb : y ∈ Set.Icc b 1 := ⟨hb.trans (max_le hy.1.le hyW'), hy.2⟩
      rw [Set.indicator_of_mem hyb]
      have hAy : A y = ENNReal.ofReal (E * y ^ l) := by
        simp only [hA]; congr 1
        unfold ellSX; rw [hXy, hE, Real.rpow_def_of_pos hy0, ← Real.exp_add]; congr 1; ring
      have hA1 : A (1 - y) = A y := by
        simp only [hA]; unfold ellSX; rw [hX1, hXy]
      simp only [hQ, Set.indicator_of_mem hyW, Set.indicator_of_mem h1W]
      rw [hA1, ← mul_add]
      have hΦle : ∀ z, Φ z ≤ Ψ z + ENNReal.ofReal (2 * deltaU N * H) := fun z => fs_floor_le lam c hδ z
      have hpair := fs_pair (N := N) lam c hcm hy
      have hsum : Φ (1 - y) + Φ y ≤ ENNReal.ofReal (K * gX lam (c.2 : ℝ) y) +
          ENNReal.ofReal (4 * deltaU N * H) := by
        calc Φ (1 - y) + Φ y ≤ (Ψ (1 - y) + ENNReal.ofReal (2 * deltaU N * H)) +
              (Ψ y + ENNReal.ofReal (2 * deltaU N * H)) := add_le_add (hΦle _) (hΦle _)
          _ = (Ψ y + Ψ (1 - y)) + (ENNReal.ofReal (2 * deltaU N * H) + ENNReal.ofReal (2 * deltaU N * H)) := by
              ring
          _ ≤ ENNReal.ofReal (K * gX lam (c.2 : ℝ) y) + ENNReal.ofReal (4 * deltaU N * H) := by
              refine add_le_add hpair (le_of_eq ?_)
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
      have hyl : y ^ l ≤ 1 := Real.rpow_le_one hy0.le hy.2 hl
      have hgX : 0 ≤ gX lam (c.2 : ℝ) y := gX_nonneg lam hy0 hy.2 (by linarith) (by linarith [hy.2])
      calc A y * (Φ (1 - y) + Φ y)
          ≤ ENNReal.ofReal (E * y ^ l) * (ENNReal.ofReal (K * gX lam (c.2 : ℝ) y) +
              ENNReal.ofReal (4 * deltaU N * H)) := by rw [hAy]; exact mul_le_mul_right hsum _
        _ = ENNReal.ofReal (E * K * (y ^ l * gX lam (c.2 : ℝ) y)) +
              ENNReal.ofReal (E * y ^ l * (4 * deltaU N * H)) := by
            rw [mul_add, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 2; ring
        _ ≤ Bnd y := by
            simp only [hBnd]
            refine add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_)
            have : E * y ^ l ≤ E := by
              have := Real.exp_pos (l * (slT N / N)); nlinarith
            exact mul_le_mul_of_nonneg_right this (by positivity)
    · have h1W : 1 - y ∉ W := by
        simp only [hWdef, Set.mem_ofPred_eq, hX1]
        simpa only [hWdef, Set.mem_ofPred_eq, hXy] using hyW
      simp only [hQ, Set.indicator_of_notMem hyW, Set.indicator_of_notMem h1W, add_zero]
      exact bot_le
  unfold unif
  rw [← lintegral_indicator hW]
  calc ∫⁻ y, Q y ∂volume.restrict (Set.Icc 0 1)
      ≤ ∫⁻ y in Set.Icc (0 : ℝ) (1 / 2) ∪ Set.Icc (1 / 2) 1, Q y :=
        lintegral_mono_set (fun y hy => by
          by_cases h : y ≤ 1 / 2
          · exact Or.inl ⟨hy.1, h⟩
          · exact Or.inr ⟨(not_le.1 h).le, hy.2⟩)
    _ ≤ (∫⁻ y in Set.Icc (0 : ℝ) (1 / 2), Q y) + ∫⁻ y in Set.Icc (1 / 2 : ℝ) 1, Q y :=
        lintegral_union_le _ _ _
    _ = (∫⁻ y in Set.Icc (1 / 2 : ℝ) 1, Q (1 - y)) + ∫⁻ y in Set.Icc (1 / 2 : ℝ) 1, Q y := by
        congr 1
        have := setLIntegral_reflect_half (fun v => Q (1 - v)) (hQm.comp (measurable_const.sub measurable_id))
        simp only [sub_sub_cancel] at this
        exact this
    _ = ∫⁻ y in Set.Ioc (1 / 2 : ℝ) 1, (Q (1 - y) + Q y) := by
        have hQ1 : Measurable fun y => Q (1 - y) := hQm.comp (measurable_const.sub measurable_id)
        rw [← lintegral_add_left hQ1,
          setLIntegral_congr (Ioc_ae_eq_Icc (a := (1 / 2 : ℝ)) (b := 1))]
    _ ≤ ∫⁻ y in Set.Ioc (1 / 2 : ℝ) 1, (Set.Icc b 1).indicator Bnd y := setLIntegral_mono' measurableSet_Ioc hpt
    _ ≤ ∫⁻ y, (Set.Icc b 1).indicator Bnd y := setLIntegral_le_lintegral _ _
    _ = ∫⁻ y in Set.Icc b 1, Bnd y := lintegral_indicator measurableSet_Icc _
    _ = ENNReal.ofReal (E * K * ∫ y in b..1, y ^ l * gX lam (c.2 : ℝ) y) +
          ENNReal.ofReal (E * (4 * deltaU N * H)) * ENNReal.ofReal (1 - b) := by
        have hB1 : Measurable fun y : ℝ => ENNReal.ofReal (E * K * (y ^ l * gX lam (c.2 : ℝ) y)) :=
          ENNReal.measurable_ofReal.comp (measurable_const.mul
            ((measurable_id.pow_const l).mul (gX_measurable lam _)))
        rw [lintegral_add_left hB1,
          fs_lint_gX lam hcm hl hb0 hb1 _ (by positivity), setLIntegral_const, Real.volume_Icc]
    _ ≤ ENNReal.ofReal (E * K * ∫ y in b..1, y ^ l * gX lam (c.2 : ℝ) y) +
          ENNReal.ofReal (E * (4 * deltaU N * H)) := by
        refine add_le_add le_rfl ?_
        calc ENNReal.ofReal (E * (4 * deltaU N * H)) * ENNReal.ofReal (1 - b)
            ≤ ENNReal.ofReal (E * (4 * deltaU N * H)) * 1 :=
              mul_le_mul_right (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)) _
          _ = _ := mul_one _
    _ = _ := by
        rw [← ENNReal.ofReal_add (mul_nonneg (by positivity) (fs_I_nonneg lam hcm hb0 hb1)) (by positivity)]
        congr 1; ring

/-- **One effect cell with `r0 = s^x`.** -/
theorem fs_effSx_cell (hN : 2 ≤ N) (hδ : deltaU N < 1 / 2) (s : State N) (x : Fin N) {c : ℚ × ℚ}
    (hc : c ∈ cellsXEffectData) :
    ∃ C ∈ rsCellsE, cubeM N {w : Param N | CellEvX N s (flipAt x s) x .effect c w} ≤
      ENNReal.ofReal (Real.exp ((C.P : ℝ) / 4 * x0 * N) * Real.exp (16 * slT N + 17 * (8 + slV N)) *
        (fsI C + fsc1 * deltaU N) ^ N) := by
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  obtain ⟨C, hC, hok, hlam, hlu, hP, hv, hv1, hw4, hb, hcap, hc2⟩ := fs_eff_partner hc
  refine ⟨C, hC, ?_⟩
  set c' : ℚ × ℚ := (c.1, C.w ^ 4) with hc'
  have hc'2 : (c'.2 : ℝ) = (C.w : ℝ) ^ 4 := by simp only [hc']; push_cast; rfl
  have hcm' : (1 : ℝ) / 2 ≤ (c'.2 : ℝ) := by rw [hc'2]; exact hw4
  have hmono := cellEvX_mono_eff s (flipAt x s) x (c := c) (c' := c') (by simp only [hc'])
    (by rw [hc'2]; exact hcap) (by linarith) (by linarith)
  refine (measure_mono hmono).trans ?_
  have hsub := cellEvX_eff_sub_template hN0 s (flipAt x s) x c' hcm' hδ
  obtain ⟨x', hx'⟩ := fs_dummy hN x
  set d := flipAt x' s with hd
  set l : ℝ := (C.P : ℝ) / 4 with hldef
  have hl0 : 0 ≤ l := by positivity
  set mu : ℝ := Real.log ((N : ℝ) + 1) with hmudef
  have hmu0 : 0 ≤ mu := Real.log_nonneg (by linarith)
  set a0 : ℝ := 1 / 2 - deltaU N with ha0
  set Wx : Set ℝ := {y : ℝ | (c'.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} with hWxdef
  have hWx : MeasurableSet Wx :=
    measurableSet_le measurable_const (clamp01_measurable.max (measurable_const.sub clamp01_measurable))
  set f : Fin 3 → Fin N → ℝ × ℝ × ℝ → ℝ :=
    ![fun _ p => ellSX N p.1, fun _ p => Set.indicator (Set.Iio a0) 1 p.2.1,
      fun _ p => gXevE N c' p.1 p.2.1] with hf
  have hfm : ∀ k i, Measurable (f k i) := by
    intro k i
    fin_cases k
    · exact fs_ellSX_meas.comp measurable_fst
    · exact (measurable_one.indicator measurableSet_Iio).comp (measurable_fst.comp measurable_snd)
    · exact (fs_gE_meas c').comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  set a : Fin 3 → ℝ := ![x0 * N + slT N, 0, 0] with ha
  set tt : Fin 3 → ℝ := ![l, mu, (C.lam : ℝ)] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 3)), 0 ≤ tt k := by
    intro k _; fin_cases k
    · simpa [htt] using hl0
    · simpa [htt] using hmu0
    · simp [htt]
  have hmain := cubeM_chernoff_three (fun _ => s) (fun _ => flipAt x s) (fun _ => d)
    (fun _ => (flipAt_ne x s).symm) (fun _ => (flipAt_ne x' s).symm) (fun _ => fs_flip_ne hx' s)
    univ f hfm a tt htt0 (fun _ => Wx) (fun _ => hWx)
  have hsub2 : {w : Param N | CellEvX N s (flipAt x s) x .effect c' w} ⊆
      {w | (∀ i, w ((fun _ : Fin N => s) i) i ∈ (fun _ : Fin N => Wx) i) ∧
        ∀ k ∈ (univ : Finset (Fin 3)), ∑ i, f k i (w ((fun _ : Fin N => s) i) i,
          w ((fun _ : Fin N => flipAt x s) i) i, w ((fun _ : Fin N => d) i) i) ≤ a k} := by
    intro w hw
    obtain ⟨h1, h2, h3, h4, h5⟩ := hsub hw
    refine ⟨fun i => h1 i, fun k _ => ?_⟩
    fin_cases k
    · simp only [hf, ha]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact h3.trans h2
    · simp only [hf, ha]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      refine le_of_eq (sum_eq_zero fun i _ => ?_)
      exact Set.indicator_of_notMem (show w (flipAt x s) i ∉ Set.Iio a0 from not_lt.2 (h5 i)) _
    · simpa [hf, ha] using h4
  set E := Real.exp (l * (slT N / N)) with hE
  set K := Real.exp (C.lam * fsK N) with hK
  set J : ℝ := K * fsI C + 4 * deltaU N * ((3 / 2 : ℝ) ^ C.lam * K) with hJdef
  have hJ0 : 0 ≤ J := by
    have := fs_cell_pos C hok
    have hδ0 : 0 ≤ deltaU N := by unfold deltaU; positivity
    simp only [hJdef]
    exact add_nonneg (mul_nonneg (Real.exp_pos _).le this.le) (by positivity)
  have hcol : ∀ i : Fin N, ∫⁻ y in (fun _ : Fin N => Wx) i, ∫⁻ u, ∫⁻ z,
      ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 3)), tt k * f k i (y, u, z))) ∂unif ∂unif ∂unif ≤
        ENNReal.ofReal (E * J) := by
    intro i
    have hcong : ∀ y, ∫⁻ u, ∫⁻ z, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 3)),
        tt k * f k i (y, u, z))) ∂unif ∂unif =
        ENNReal.ofReal (Real.exp (-(l * ellSX N y))) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-(mu * Set.indicator (Set.Iio a0) 1 u))) *
            ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXevE N c' y u)) ∂unif := by
      intro y
      have hgm : Measurable fun u => ENNReal.ofReal (Real.exp (-(mu * Set.indicator (Set.Iio a0) 1 u))) *
          ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXevE N c' y u)) := by
        have h1 : Measurable fun u : ℝ => ENNReal.ofReal (Real.exp (-(mu * Set.indicator (Set.Iio a0) 1 u))) :=
          ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
            (((measurable_one.indicator measurableSet_Iio).const_mul _).neg))
        have h2 : Measurable fun u => ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXevE N c' y u)) :=
          ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
            (((fs_gE_meas c').comp (measurable_const.prodMk measurable_id)).const_mul _))
        exact h1.mul h2
      rw [← lintegral_const_mul _ hgm]
      refine lintegral_congr fun u => ?_
      have hz : ∀ z, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 3)), tt k * f k i (y, u, z))) =
          ENNReal.ofReal (Real.exp (-(l * ellSX N y))) *
            (ENNReal.ofReal (Real.exp (-(mu * Set.indicator (Set.Iio a0) 1 u))) *
              ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXevE N c' y u))) := by
        intro z
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← Real.exp_add, ← Real.exp_add]
        congr 2
        simp [Fin.sum_univ_three, hf, htt]
        ring
      rw [lintegral_congr hz, lintegral_const, unif_univ, mul_one]
    simp only [hcong]
    have hb0 : (0 : ℝ) < (C.v : ℝ) ^ 4 := by positivity
    have hb1 : (C.v : ℝ) ^ 4 ≤ 1 := pow_le_one₀ hv.le hv1.le
    have := fs_colE2 (N := N) C.lam c' hcm' hl0 hb0 hb1 (by simpa [hc'] using hb) hδ
    rw [hc'2] at this
    refine this.trans (le_of_eq ?_)
    congr 1
  refine (measure_mono hsub2).trans (hmain.trans ?_)
  have hsum : ∑ k ∈ (univ : Finset (Fin 3)), tt k * a k = l * (x0 * N + slT N) := by
    simp [Fin.sum_univ_three, htt, ha]
  rw [hsum]
  have hEJ0 : 0 ≤ E * J := mul_nonneg (Real.exp_pos _).le hJ0
  calc ENNReal.ofReal (Real.exp (l * (x0 * N + slT N))) * ∏ i : Fin N, ∫⁻ y in (fun _ : Fin N => Wx) i,
        ∫⁻ u, ∫⁻ z, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 3)), tt k * f k i (y, u, z)))
          ∂unif ∂unif ∂unif
      ≤ ENNReal.ofReal (Real.exp (l * (x0 * N + slT N))) * ∏ _i : Fin N, ENNReal.ofReal (E * J) := by
        gcongr with i; exact hcol i
    _ = ENNReal.ofReal (Real.exp (l * (x0 * N + 2 * slT N)) * J ^ N) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow hEJ0,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_pow, hE, ← Real.exp_nat_mul, ← mul_assoc,
          ← Real.exp_add]
        congr 3
        field_simp
        ring
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hl8 : l ≤ 8 := by
          have : (C.P : ℝ) ≤ 30 := by exact_mod_cast hP
          simp only [hldef]; linarith
        exact fs_final (by omega) hl0 hl8 (Nat.cast_nonneg _) (by exact_mod_cast hlam)
          (fs_cell_pos C hok).le hJ0 (fs_J_le C.lam hlam _ 4 (by norm_num) le_rfl) le_rfl

/-! ### The row-coincidence sub-leaf and leaf 8 at `RfF2` -/

/-- The row-coincidence sub-leaf at rate `RfF2` (the `B1ForcedAF.FarSelfLeaf` statement with `RfF2`). -/
def FarSelfLeaf2 : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide), (r0 = s ∨ flipAt x r0 = s) →
    cubeM N {w | RegEvX N s r0 x σ w} ≤ ENNReal.ofReal (Real.exp (-(RfF2 * N)) / (8 * N))

/-- A union of the 61 cells, each bounded by `B`. -/
lemma fs_union61 (s r0 : State N) (x : Fin N) (σ : XSide) {B : ℝ} (hB0 : 0 ≤ B)
    (h : ∀ c ∈ (cellsX σ), cubeM N {w : Param N | CellEvX N s r0 x σ c w} ≤ ENNReal.ofReal B) :
    cubeM N {w | RegEvX N s r0 x σ w} ≤ ENNReal.ofReal (61 * B) := by
  have hset : {w : Param N | RegEvX N s r0 x σ w} =
      ⋃ c ∈ cellsX σ, {w : Param N | CellEvX N s r0 x σ c w} := by
    ext w; simp [RegEvX]
  rw [hset]
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hcard : (cellsX σ).card ≤ 61 := by
    cases σ
    · have : cellsXCauseData.toFinset.card ≤ cellsXCauseData.length := List.toFinset_card_le _
      have hlen : cellsXCauseData.length = 61 := by decide
      simp only [cellsX]; omega
    · have : cellsXEffectData.toFinset.card ≤ cellsXEffectData.length := List.toFinset_card_le _
      have hlen : cellsXEffectData.length = 61 := by decide
      simp only [cellsX]; omega
  calc ∑ c ∈ cellsX σ, cubeM N {w : Param N | CellEvX N s r0 x σ c w}
      ≤ ∑ _c ∈ cellsX σ, ENNReal.ofReal B := sum_le_sum h
    _ = ((cellsX σ).card : ENNReal) * ENNReal.ofReal B := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (61 : ENNReal) * ENNReal.ofReal B := by gcongr; exact_mod_cast hcard
    _ = ENNReal.ofReal (61 * B) := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num

/-- **The row-coincidence sub-leaf, PROVED** (rate `R0 + log(3/2) ≥ 1.4127` per `(s, r0, x, σ)`). -/
theorem farSelfLeaf2 : FarSelfLeaf2 := by
  filter_upwards [fs_absorb, eventually_ge_atTop 2] with N hab hN s r0 x σ hco
  have hδ : deltaU N < 1 / 2 := by
    unfold deltaU; rw [div_lt_iff₀ (by positivity)]; have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hNr : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set B := Real.exp (-(RfF2 * N)) / (488 * N) with hB
  have hB0 : 0 ≤ B := by positivity
  have hfin : Real.exp (-(RfF2 * N)) / (8 * N) = 61 * B := by rw [hB]; field_simp; ring
  rw [hfin]
  refine fs_union61 s r0 x σ hB0 fun c hc => ?_
  cases σ with
  | cause =>
    have hc' : c ∈ cellsXCauseData := List.mem_toFinset.1 hc
    obtain ⟨C, hC, hbd⟩ := fs_cause_cell hN s r0 x hc'
    have hok := (List.all_eq_true.1 rsCellsC_ok) C hC
    have hb := (List.all_eq_true.1 rsBounds) C hC
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    exact hbd.trans (ENNReal.ofReal_le_ofReal (hab C hok hb.1.2 (by omega)))
  | effect =>
    have hc' : c ∈ cellsXEffectData := List.mem_toFinset.1 hc
    rcases hco with h | h
    · subst h
      obtain ⟨C, hC, hbd⟩ := fs_effS_cell hN hδ r0 x hc'
      have hok := (List.all_eq_true.1 rsCellsE_ok) C hC
      have hb := (List.all_eq_true.1 rsBoundsE) C hC
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      exact hbd.trans (ENNReal.ofReal_le_ofReal (hab C hok hb.1.2 (by omega)))
    · have hr : r0 = flipAt x s := by rw [← h, flipAt_flipAt]
      subst hr
      obtain ⟨C, hC, hbd⟩ := fs_effSx_cell hN hδ s x hc'
      have hok := (List.all_eq_true.1 rsCellsE_ok) C hC
      have hb := (List.all_eq_true.1 rsBoundsE) C hC
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      exact hbd.trans (ENNReal.ofReal_le_ofReal (hab C hok hb.1.2 (by omega)))

/-- The Hamming count at rate `RfF2`. -/
lemma fs_far_count : ∀ᶠ N : ℕ in atTop,
    Real.exp (-(RXf * N)) * (2 ^ (N / 3) * (3 / 4) ^ N) ≤ Real.exp (-(RfF2 * N)) / 2 := by
  have hq : (27 / 32 : ℝ) / (98 / 100 + 89 / 10000) < 1 := by norm_num
  filter_upwards [fa_absorb (q := (27 / 32 : ℝ) / (98 / 100 + 89 / 10000)) (by positivity) hq 16 0]
    with N hN
  simp only [pow_zero, mul_one] at hN
  set a := 2 * (2 ^ (N / 3) * (3 / 4 : ℝ) ^ N) with ha
  set b := Real.exp (-((37 / 10000 : ℝ) * N)) with hb
  have hb0 : 0 ≤ b := (Real.exp_pos _).le
  have hcube : a ^ 3 ≤ b ^ 3 := by
    have e1 : a ^ 3 = 8 * (((2 : ℝ) ^ (N / 3)) ^ 3) * ((3 / 4 : ℝ) ^ 3) ^ N := by
      rw [ha, show ((3 / 4 : ℝ) ^ 3) ^ N = ((3 / 4 : ℝ) ^ N) ^ 3 by
        rw [← pow_mul, ← pow_mul, mul_comm]]
      ring
    have e2 : b ^ 3 = Real.exp (-((111 / 10000 : ℝ) * N)) := by
      rw [hb, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h8 : ((2 : ℝ) ^ (N / 3)) ^ 3 ≤ 2 ^ N := by
      rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h34 : (3 / 4 : ℝ) ^ 3 = 27 / 64 := by norm_num
    have hlow : (1 - 111 / 10000 : ℝ) ^ N ≤ Real.exp (-((111 / 10000 : ℝ) * N)) := by
      rw [show -((111 / 10000 : ℝ) * N) = (N : ℝ) * (-(111 / 10000)) by ring, fa_exp_mul_nat]
      exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (-(111 / 10000 : ℝ))]) N
    have hm : 8 * (2 : ℝ) ^ N * (27 / 64) ^ N ≤ (1 - 111 / 10000 : ℝ) ^ N := by
      have e3 : (27 / 32 : ℝ) / (98 / 100 + 89 / 10000) = (27 / 32) / (1 - 111 / 10000) := by norm_num
      rw [e3, div_pow] at hN
      have hp : (0 : ℝ) < (1 - 111 / 10000) ^ N := by positivity
      rw [mul_div_assoc', div_le_iff₀ hp] at hN
      have : (2 : ℝ) ^ N * (27 / 64) ^ N = (27 / 32) ^ N := by rw [← mul_pow]; norm_num
      nlinarith
    rw [e1, e2, h34]
    have := pow_nonneg (show (0 : ℝ) ≤ 27 / 64 by norm_num) N
    nlinarith
  have hab : a ≤ b := le_of_pow_le_pow_left₀ (by norm_num) hb0 hcube
  have e : Real.exp (-(RXf * N)) * b = Real.exp (-(RfF2 * N)) := by
    rw [hb, ← Real.exp_add]; unfold RXf RfF2; congr 1; ring
  have hE := Real.exp_pos (-(RXf * N))
  rw [← e]
  nlinarith

/-- **Leaf 8 (`far`) at rate `RfF2`, from the sub-leaf.** -/
theorem leafF8_of_self (hself : FarSelfLeaf2) : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bField N s (fFar N s)) ≤ ENNReal.ofReal (Real.exp (-(RfF2 * N))) := by
  filter_upwards [hself, rs_absorb 122, fs_far_count, eventually_ge_atTop 7] with N hS hab hc hN7 s
  have hN : 0 < N := by omega
  have hδ : deltaU N < 1 / 2 := by
    unfold deltaU; rw [div_lt_iff₀ (by positivity)]; have : (7 : ℝ) ≤ N := by exact_mod_cast hN7
    linarith
  set B := Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N with hB
  have hslT : 0 ≤ slT N := by
    unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    linarith
  have hB0 : 0 ≤ B := by positivity
  set F := Real.exp (-(RfF2 * N)) / (8 * N) with hF
  have hF0 : 0 ≤ F := by positivity
  set P : State N → Fin N → Prop := fun r0 x => r0 = s ∨ flipAt x r0 = s with hP
  have hterm : ∀ r0 x σ, cubeM N {w | RegEvX N s r0 x σ w} ≤
      ENNReal.ofReal ((if P r0 x then F else 0) + 61 * B) := by
    intro r0 x σ
    by_cases hp : P r0 x
    · rw [if_pos hp]; exact (hS s r0 x σ hp).trans (ENNReal.ofReal_le_ofReal (by linarith))
    · rw [if_neg hp, zero_add]
      simp only [hP, not_or] at hp
      cases σ with
      | cause =>
        refine (regEvX_cause_prob hN s r0 x hp.1 hp.2).trans (ENNReal.ofReal_le_ofReal ?_)
        have := Real.exp_le_exp.2
          (show 14 * slT N + 17 * (8 + slV N) ≤ 19 * slT N + 17 * (8 + slV N) + 9 by linarith)
        rw [hB]; gcongr
      | effect =>
        refine regEvX_effect_prob hN s r0 x hδ (Ne.symm hp.1) ?_
        intro h; apply hp.2; rw [← h, flipAt_flipAt]
  set R := (univ : Finset (State N)).filter fun r0 => ham r0 s ≤ N / 3 with hR
  have hsub : bField N s (fFar N s) ⊆ ⋃ r0 ∈ R, ⋃ x : Fin N, ⋃ σ : XSide, {w | RegEvX N s r0 x σ w} := by
    intro w hw
    obtain ⟨_, x, σ, hreg, hn⟩ := hw
    simp only [fFar, not_le] at hn
    simp only [Set.mem_iUnion, hR, mem_filter, mem_univ, true_and]
    exact ⟨tcRow w, by omega, x, σ, hreg⟩
  refine (measure_mono hsub).trans ?_
  have hsum : cubeM N (⋃ r0 ∈ R, ⋃ x : Fin N, ⋃ σ : XSide, {w | RegEvX N s r0 x σ w}) ≤
      ∑ r0 ∈ R, ∑ x : Fin N, ∑ σ : XSide,
        ENNReal.ofReal ((if P r0 x then F else 0) + 61 * B) := by
    refine (measure_biUnion_finset_le _ _).trans (sum_le_sum fun r0 _ => ?_)
    refine (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun x _ => ?_)
    exact (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun σ _ => hterm r0 x σ)
  refine hsum.trans ?_
  have hnn : ∀ r0 x, 0 ≤ (if P r0 x then F else 0) + 61 * B := fun r0 x => by
    split_ifs <;> positivity
  have e1 : ∀ r0 x, ∑ _σ : XSide, ENNReal.ofReal (((if P r0 x then F else 0) + 61 * B)) =
      ENNReal.ofReal (2 * ((if P r0 x then F else 0) + 61 * B)) := by
    intro r0 x
    rw [sum_const, card_univ, show Fintype.card XSide = 2 from rfl, nsmul_eq_mul,
      ENNReal.ofReal_mul (by norm_num)]
    simp
  simp_rw [e1]
  have hnn2 : ∀ r0 x, 0 ≤ 2 * ((if P r0 x then F else 0) + 61 * B) := fun r0 x => by
    have := hnn r0 x; linarith
  rw [show (∑ r0 ∈ R, ∑ x : Fin N, ENNReal.ofReal (2 * ((if P r0 x then F else 0) + 61 * B))) =
      ∑ r0 ∈ R, ENNReal.ofReal (∑ x : Fin N, 2 * ((if P r0 x then F else 0) + 61 * B)) from
      sum_congr rfl fun r0 _ => (ENNReal.ofReal_sum_of_nonneg fun x _ => hnn2 r0 x).symm,
    ← ENNReal.ofReal_sum_of_nonneg fun r0 _ => sum_nonneg fun x _ => hnn2 r0 x]
  apply ENNReal.ofReal_le_ofReal
  have hsplit : ∑ r0 ∈ R, ∑ x : Fin N, 2 * ((if P r0 x then F else 0) + 61 * B) =
      2 * ∑ r0 ∈ R, ∑ x : Fin N, (if P r0 x then F else 0) + 122 * B * N * R.card := by
    simp only [mul_add, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_sum]
    ring
  rw [hsplit]
  have hself : ∑ r0 ∈ R, ∑ x : Fin N, (if P r0 x then F else 0) ≤ 2 * N * F := by
    calc ∑ r0 ∈ R, ∑ x : Fin N, (if P r0 x then F else 0)
        ≤ ∑ r0 : State N, ∑ x : Fin N, (if P r0 x then F else 0) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r0 _ _ =>
            sum_nonneg fun x _ => by split_ifs <;> linarith
      _ = ∑ x : Fin N, ∑ r0 : State N, (if P r0 x then F else 0) := sum_comm
      _ ≤ ∑ _x : Fin N, 2 * F := by
          refine sum_le_sum fun x _ => ?_
          rw [← sum_filter, sum_const, nsmul_eq_mul]
          have := fa_self_card s x
          simp only [hP]
          nlinarith
      _ = 2 * N * F := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hRc := fa_card_near s (N / 3)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h4 : 2 * (2 * N * F) = Real.exp (-(RfF2 * N)) / 2 := by rw [hF]; field_simp; ring
  have hgen : 122 * B * N * (R.card : ℝ) ≤ Real.exp (-(RfF2 * N)) / 2 := by
    have hB' : 122 * B * N = 122 * N * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) *
        Real.exp (-((10072 / 10000 : ℝ) * N)) / 2 ^ N := by
      rw [hB]; simp only [rsR0]; push_cast; ring
    calc 122 * B * N * (R.card : ℝ) ≤ 122 * B * N * (2 ^ (N / 3) * (3 / 2) ^ N) :=
          mul_le_mul_of_nonneg_left hRc (by positivity)
      _ = (122 * N * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) *
            Real.exp (-((10072 / 10000 : ℝ) * N))) * (2 ^ (N / 3) * (3 / 4) ^ N) := by
          rw [hB']
          have : (3 / 4 : ℝ) ^ N = (3 / 2) ^ N / 2 ^ N := by rw [← div_pow]; norm_num
          rw [this]; field_simp
      _ ≤ Real.exp (-(RXf * N)) * (2 ^ (N / 3) * (3 / 4) ^ N) :=
          mul_le_mul_of_nonneg_right hab (by positivity)
      _ ≤ _ := hc
  linarith

/-- **`h8` of `B1_forcedX_partial`, PROVED.** -/
theorem leafF8 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bField N s (fFar N s)) ≤ ENNReal.ofReal (Real.exp (-(RfF2 * N))) :=
  leafF8_of_self farSelfLeaf2

end Census
end IIT

#print axioms IIT.Census.leafF8
#print axioms IIT.Census.farSelfLeaf2
