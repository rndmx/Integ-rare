/-
Census, B1 lower bound part (b): checks S, V, M0, D of `EXFacts` hold on `E_X` w.h.p.
-/
import IIT.Census.B1EXAvg2
import IIT.Census.CertEX2DGlue

set_option maxRecDepth 100000

namespace IIT
namespace Census

open MeasureTheory Filter Finset intervalIntegral

/-- Soundness of a table entry. -/
lemma ctab_sound {e : ℚ × Bool × ℚ × ℚ} (h : ctabOK e = true) :
    (e.2.2.1 : ℝ) ≤ Real.log e.1 ∧ Real.log e.1 ≤ e.2.2.2 := by
  unfold ctabOK at h
  split_ifs at h with hinv
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
    have glo : ((crLnLo e.1⁻¹ 0 60 : ℚ) : ℝ) ≤ Real.log (e.1⁻¹ : ℚ) := crLog_ge 0 60 (by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨h0, h1⟩, le_rfl⟩)
    have ghi : Real.log (e.1⁻¹ : ℚ) ≤ ((crLnHi e.1⁻¹ 0 60 : ℚ) : ℝ) := crLog_le 0 60 (by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨h0, h1⟩, le_rfl⟩)
    rw [Rat.cast_inv, Real.log_inv] at glo ghi
    have a := (Rat.cast_le (K := ℝ)).2 h2
    have b := (Rat.cast_le (K := ℝ)).2 h3
    push_cast at a b
    constructor <;> linarith
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
    have glo : ((crLnLo e.1 0 60 : ℚ) : ℝ) ≤ Real.log e.1 := crLog_ge 0 60 (by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨h0, h1⟩, le_rfl⟩)
    have ghi : Real.log e.1 ≤ ((crLnHi e.1 0 60 : ℚ) : ℝ) := crLog_le 0 60 (by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨h0, h1⟩, le_rfl⟩)
    have a := (Rat.cast_le (K := ℝ)).2 h2
    have b := (Rat.cast_le (K := ℝ)).2 h3
    constructor <;> linarith

lemma exCt_ok {j : ℕ} (hj : j - 32 < exCtab.length) : ctabOK (exCt j) = true := by
  unfold exCt; rw [List.getD_eq_getElem _ _ hj]
  exact (List.all_eq_true.1 exCtab_ok) _ (List.getElem_mem hj)

/-- Soundness of a log record. -/
lemma lrec_sound {q : ℚ} {r : LRec} (h : lrecOK q r = true) :
    (r.2.2.1 : ℝ) ≤ Real.log q ∧ Real.log q ≤ r.2.2.2 := by
  simp only [lrecOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hj, hc⟩, hq⟩, hx⟩, hlo⟩, hhi⟩ := h
  set c := (exCt r.2.1).1
  have ht := ctab_sound (exCt_ok hj)
  have glo : ((crLnLo (q / c) r.1 10 : ℚ) : ℝ) ≤ Real.log ((q / c : ℚ) : ℝ) := crLog_ge r.1 10 (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hq, hx⟩, le_rfl⟩)
  have ghi : Real.log ((q / c : ℚ) : ℝ) ≤ ((crLnHi (q / c) r.1 10 : ℚ) : ℝ) := crLog_le r.1 10 (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hq, hx⟩, le_rfl⟩)
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hq' : (0 : ℝ) < q := by
    have : (0 : ℝ) < ((q / c : ℚ) : ℝ) := by exact_mod_cast hq
    push_cast at this; exact (div_pos_iff_of_pos_right hc').1 this
  have hsplit : Real.log ((q / c : ℚ) : ℝ) = Real.log q - Real.log c := by
    push_cast; exact Real.log_div hq'.ne' hc'.ne'
  rw [hsplit] at glo ghi
  have a := (Rat.cast_le (K := ℝ)).2 hlo
  have b := (Rat.cast_le (K := ℝ)).2 hhi
  push_cast at a b
  constructor <;> linarith [ht.1, ht.2]

/-- The parts of the per-cell check. -/
lemma ex2DOK_parts {C : EXPCell} {R : EX2DRec} (h : ex2DOK C R = true) :
    lrecOK (exYl C + C.u0) R.r00 = true ∧ lrecOK (exYl C + C.u1) R.r01 = true ∧
    lrecOK (exYhi C + C.u0) R.r10 = true ∧ lrecOK (exYhi C + C.u1) R.r11 = true ∧
    lrecOK (max C.u0 exDEL) R.rm = true ∧ lrecOK C.u1 R.ru = true ∧ exDEL ≤ C.u1 ∧
    R.sl ≤ exLamLo C R ∧ exVup C R ≤ R.vu ∧ R.ml ≤ exMlo C R ∧ R.dl ≤ exDlo C R := by
  simp only [ex2DOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, i⟩, j⟩, k⟩, l⟩ := h
  exact ⟨a, b, c, d, e, f, g, i, j, k, l⟩

/-- Cell coordinates as reals. -/
lemma exYlo_pos (C : EXPCell) : (0 : ℝ) < exYlo C := exF_pos.trans_le (exYlo_ge C)

/-- **Fubini on a pair cell**. -/
lemma cell_integral (C : EXPCell) (hC : C ∈ exPCells) (h : ℝ × ℝ → ℝ)
    (hint : IntegrableOn h (exIP C) (unif.prod unif)) :
    ∫ p in exIP C, h p ∂(unif.prod unif) =
      ∫ y in (exYlo C : ℝ)..((exYlo C + exHy : ℚ) : ℝ), ∫ u in (C.u0 : ℝ)..C.u1, h (y, u) := by
  obtain ⟨-, -, hu0, hu01, hu1, -⟩ := exP_facts hC
  have hy0 : (0 : ℝ) ≤ exYlo C := (exYlo_pos C).le
  have hyy : (exYlo C : ℝ) ≤ ((exYlo C + exHy : ℚ) : ℝ) := by
    have := exHy_pos; exact_mod_cast (by linarith : exYlo C ≤ exYlo C + exHy)
  have hy1 := exYhi_le C hC
  rw [exIP, setIntegral_prod _ hint, unif_setIntegral_Ico hy0 hyy hy1]
  refine intervalIntegral.integral_congr fun y _ => ?_
  exact unif_setIntegral_Ico (by exact_mod_cast hu0) (by exact_mod_cast hu01.le) (by exact_mod_cast hu1) _

/-- `|log t| ≤ 1` on `[1/2, 2]`. -/
lemma abs_log_le_one {t : ℝ} (h1 : 1 / 2 ≤ t) (h2 : t ≤ 2) : |Real.log t| ≤ 1 := by
  have ht : 0 < t := by linarith
  rw [abs_le]; constructor
  · have := Real.one_sub_inv_le_log_of_pos ht
    have : t⁻¹ ≤ 2 := by rw [inv_le_comm₀ ht (by norm_num)]; linarith
    linarith
  · have := Real.log_le_sub_one_of_pos ht; linarith

/-- On a pair cell: `y ∈ [1/2, 1]`, `u ∈ [0, 1]`. -/
lemma cell_mem {C : EXPCell} (hC : C ∈ exPCells) {p : ℝ × ℝ} (hp : p ∈ exIP C) :
    (exYlo C : ℝ) ≤ p.1 ∧ p.1 ≤ 1 ∧ (1 / 2 : ℝ) ≤ p.1 ∧ (C.u0 : ℝ) ≤ p.2 ∧ p.2 < C.u1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 ∧
      clamp01 p.1 = p.1 ∧ clamp01 p.2 = p.2 := by
  obtain ⟨-, -, hu0, -, hu1, -⟩ := exP_facts hC
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
  have hy1 := exYhi_le C hC
  have hyf := exYlo_ge C
  have hf : ((exF : ℚ) : ℝ) = 1001 / 2000 := by unfold exF; norm_num
  have hu0' : (0 : ℝ) ≤ C.u0 := by exact_mod_cast hu0
  have hu1' : (C.u1 : ℝ) ≤ 1 := by exact_mod_cast hu1
  have a1 : p.1 ≤ 1 := h2.le.trans hy1
  have a2 : (1 / 2 : ℝ) ≤ p.1 := by linarith
  have a3 : 0 ≤ p.2 := hu0'.trans h3
  have a4 : p.2 ≤ 1 := h4.le.trans hu1'
  refine ⟨h1, a1, a2, h3, h4, a3, a4, ?_, ?_⟩
  · unfold clamp01; rw [min_eq_right a1, max_eq_right (by linarith)]
  · unfold clamp01; rw [min_eq_right a4, max_eq_right a3]

/-- The `S`-function `λ = ln(2y/(y+U))`. -/
noncomputable def gS (p : ℝ × ℝ) : ℝ := Real.log (2 * clamp01 p.1 / (clamp01 p.1 + clamp01 p.2))

lemma measurable_gS : Measurable gS := by
  unfold gS
  exact Real.measurable_log.comp ((measurable_const.mul (clamp01_measurable.comp measurable_fst)).div
    ((clamp01_measurable.comp measurable_fst).add (clamp01_measurable.comp measurable_snd)))

lemma gS_eq {C : EXPCell} (hC : C ∈ exPCells) {p : ℝ × ℝ} (hp : p ∈ exIP C) :
    gS p = Real.log 2 + Real.log p.1 - Real.log (p.1 + p.2) := by
  obtain ⟨-, -, a2, -, -, a3, -, c1, c2⟩ := cell_mem hC hp
  unfold gS; rw [c1, c2, Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)]

lemma gS_range {C : EXPCell} (hC : C ∈ exPCells) {p : ℝ × ℝ} (hp : p ∈ exIP C) : gS p ∈ Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨-, a1, a2, -, -, a3, a4, -, -⟩ := cell_mem hC hp
  rw [gS_eq hC hp]
  have l2 := Real.log_two_lt_d9; have l2' := Real.log_two_gt_d9
  have ly : Real.log p.1 ≤ 0 := Real.log_nonpos (by linarith) a1
  have ly' := abs_le.1 (abs_log_le_one a2 (by linarith))
  -- log(y+u) ≥ log y and ≤ log (2y) ... use 2y/(y+u) ∈ [2y/(y+1), 2]
  have hyu : Real.log p.1 ≤ Real.log (p.1 + p.2) := Real.log_le_log (by linarith) (by linarith)
  have hyu2 : Real.log (p.1 + p.2) ≤ Real.log (2 * p.1) + Real.log 2 := by
    rw [← Real.log_mul (by positivity) (by norm_num)]; exact Real.log_le_log (by linarith) (by nlinarith)
  rw [Real.log_mul (by norm_num) (by linarith)] at hyu2
  constructor <;> nlinarith

lemma exIP_meas (C : EXPCell) : MeasurableSet (exIP C) := measurableSet_Ico.prod measurableSet_Ico

/-- A function bounded by `M` on a pair cell is integrable there. -/
lemma cell_integrableOn {C : EXPCell} (h : ℝ × ℝ → ℝ) (hm : Measurable h) (M : ℝ)
    (hb : ∀ p ∈ exIP C, |h p| ≤ M) : IntegrableOn h (exIP C) (unif.prod unif) := by
  refine Measure.integrableOn_of_bounded (M := M) (measure_ne_top _ _) hm.aestronglyMeasurable ?_
  exact (ae_restrict_iff' (exIP_meas C)).2 (Filter.Eventually.of_forall fun p hp => by
    rw [Real.norm_eq_abs]; exact hb p hp)

/-- The `λ` cell integrand. -/
noncomputable def lamH (p : ℝ × ℝ) : ℝ := Real.log 2 + Real.log p.1 - Real.log (p.1 + p.2)

lemma measurable_lamH : Measurable lamH := by
  unfold lamH
  exact (measurable_const.add (Real.measurable_log.comp measurable_fst)).sub
    (Real.measurable_log.comp (measurable_fst.add measurable_snd))

lemma lamH_bound {C : EXPCell} (hC : C ∈ exPCells) : ∀ p ∈ exIP C, |lamH p| ≤ 3 := by
  intro p hp
  obtain ⟨-, a1, a2, -, -, a3, a4, -, -⟩ := cell_mem hC hp
  have l2 := abs_log_le_one (t := 2) (by norm_num) le_rfl
  have ly := abs_log_le_one a2 (by linarith)
  have lyu := abs_log_le_one (t := p.1 + p.2) (by linarith) (by linarith)
  unfold lamH
  calc |Real.log 2 + Real.log p.1 - Real.log (p.1 + p.2)|
      ≤ |Real.log 2 + Real.log p.1| + |Real.log (p.1 + p.2)| := abs_sub _ _
    _ ≤ |Real.log 2| + |Real.log p.1| + |Real.log (p.1 + p.2)| := by gcongr; exact abs_add_le _ _
    _ ≤ 3 := by linarith

/-- **The cell average of `λ`.** -/
lemma avg_gS (C : EXPCell) (hC : C ∈ exPCells) :
    (∫ p in exIP C, gS p ∂(unif.prod unif)) / ((exHy : ℝ) * (C.u1 - C.u0)) =
      Real.log 2 + (((exYlo C + exHy : ℚ) : ℝ) * Real.log ((exYlo C + exHy : ℚ) : ℝ) -
          (exYlo C : ℝ) * Real.log (exYlo C : ℝ) - ((exYlo C + exHy : ℚ) : ℝ) + exYlo C) / exHy -
        (lnG (((exYlo C + exHy : ℚ) : ℝ) + C.u1) - lnG ((exYlo C : ℝ) + C.u1) -
          (lnG (((exYlo C + exHy : ℚ) : ℝ) + C.u0) - lnG ((exYlo C : ℝ) + C.u0))) / ((exHy : ℝ) * (C.u1 - C.u0)) := by
  obtain ⟨-, -, hu0, hu01, hu1, -⟩ := exP_facts hC
  set Y0 : ℝ := ((exYlo C : ℚ) : ℝ)
  set Y1 : ℝ := ((exYlo C + exHy : ℚ) : ℝ)
  set u0 : ℝ := ((C.u0 : ℚ) : ℝ)
  set u1 : ℝ := ((C.u1 : ℚ) : ℝ)
  have hY0 : 0 < Y0 := exYlo_pos C
  have hhy : (0 : ℝ) < exHy := by exact_mod_cast exHy_pos
  have hY1 : Y1 = Y0 + exHy := by simp only [Y1, Y0]; push_cast; ring
  have hYY : Y0 ≤ Y1 := by rw [hY1]; linarith
  have hu0' : 0 ≤ u0 := by show (0 : ℝ) ≤ ((C.u0 : ℚ) : ℝ); exact_mod_cast hu0
  have huu : u0 < u1 := by show ((C.u0 : ℚ) : ℝ) < ((C.u1 : ℚ) : ℝ); exact_mod_cast hu01
  rw [setIntegral_congr_fun (exIP_meas C) (fun p hp => gS_eq hC hp : ∀ p ∈ exIP C, gS p = lamH p)]
  show (∫ p in exIP C, lamH p ∂(unif.prod unif)) / _ = _
  rw [cell_integral C hC _ (cell_integrableOn lamH measurable_lamH 3 (lamH_bound hC))]
  -- inner integral
  have hinner : ∀ y ∈ Set.uIcc Y0 Y1, ∫ u in u0..u1, lamH (y, u) =
      (u1 - u0) * (Real.log 2 + Real.log y) - ∫ u in u0..u1, Real.log (y + u) := by
    intro y hy
    rw [Set.uIcc_of_le hYY] at hy
    have hypos : 0 < y := hY0.trans_le hy.1
    simp only [lamH]
    rw [intervalIntegral.integral_sub intervalIntegrable_const ?_, intervalIntegral.integral_const, smul_eq_mul]
    refine ContinuousOn.intervalIntegrable ?_
    exact Real.continuousOn_log.comp (continuousOn_const.add continuousOn_id) fun u hu => by
      rw [Set.uIcc_of_le huu.le] at hu; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have := hu.1; intro h; linarith
  rw [intervalIntegral.integral_congr hinner]
  have hcont1 : ContinuousOn (fun y => (u1 - u0) * (Real.log 2 + Real.log y)) (Set.uIcc Y0 Y1) :=
    continuousOn_const.mul (continuousOn_const.add (Real.continuousOn_log.mono fun y hy => by
      rw [Set.uIcc_of_le hYY] at hy; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have := hy.1; intro h; linarith))
  have hcont2 : ContinuousOn (fun y => ∫ u in u0..u1, Real.log (y + u)) (Set.uIcc Y0 Y1) := by
    simp_rw [integral_log_add]
    unfold lnF
    have hpos : ∀ c, 0 ≤ c → ∀ y ∈ Set.uIcc Y0 Y1, y + c ≠ 0 := fun c hc y hy => by
      rw [Set.uIcc_of_le hYY] at hy; have := hy.1; intro h; linarith
    refine ContinuousOn.sub (ContinuousOn.sub (ContinuousOn.mul (continuousOn_id.add continuousOn_const)
      (Real.continuousOn_log.comp (continuousOn_id.add continuousOn_const) fun y hy => hpos u1 (by linarith) y hy))
      (continuousOn_id.add continuousOn_const)) (ContinuousOn.sub (ContinuousOn.mul
      (continuousOn_id.add continuousOn_const)
      (Real.continuousOn_log.comp (continuousOn_id.add continuousOn_const) fun y hy => hpos u0 hu0' y hy))
      (continuousOn_id.add continuousOn_const))
  rw [intervalIntegral.integral_sub hcont1.intervalIntegrable hcont2.intervalIntegrable,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const
      ((Real.continuousOn_log.mono fun y hy => by
        rw [Set.uIcc_of_le hYY] at hy; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have := hy.1; intro h; linarith).intervalIntegrable),
    intervalIntegral.integral_const, smul_eq_mul, integral_log,
    integral_rect_log_add hYY huu.le (by linarith)]
  have hw : (0 : ℝ) < u1 - u0 := by linarith
  rw [hY1]
  field_simp
  ring

/-- `lnG` bounds from a log bound (`t² ≥ 0`). -/
lemma lnG_bounds {t : ℚ} {r : LRec} (h : lrecOK t r = true) :
    ((gLo t r : ℚ) : ℝ) ≤ lnG t ∧ lnG t ≤ ((gHi t r : ℚ) : ℝ) := by
  have hl := lrec_sound h
  have ht : (0 : ℝ) ≤ (t : ℝ) * t := mul_self_nonneg _
  unfold gLo gHi lnG; push_cast
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hl.1 ht, mul_le_mul_of_nonneg_left hl.2 ht]

/-- The strip average of `ln y` lies in `[-BTup, -BTlo]`. -/
lemma ly_bounds (C : EXPCell) (hC : C ∈ exPCells) :
    -((exBTup C.sa : ℚ) : ℝ) ≤ (((exYlo C + exHy : ℚ) : ℝ) * Real.log ((exYlo C + exHy : ℚ) : ℝ) -
        (exYlo C : ℝ) * Real.log (exYlo C : ℝ) - ((exYlo C + exHy : ℚ) : ℝ) + exYlo C) / exHy ∧
      (((exYlo C + exHy : ℚ) : ℝ) * Real.log ((exYlo C + exHy : ℚ) : ℝ) -
        (exYlo C : ℝ) * Real.log (exYlo C : ℝ) - ((exYlo C + exHy : ℚ) : ℝ) + exYlo C) / exHy ≤
        -((exBTlo C.sa : ℚ) : ℝ) := by
  obtain ⟨i, hi⟩ := List.getElem_of_mem hC
  have hb := avg_gT_bounds ⟨i, hi.1⟩
  have hci : cP ⟨i, hi.1⟩ = C := hi.2
  rw [hci, show ellP ⟨i, hi.1⟩ = (exHy : ℝ) * (C.u1 - C.u0) by simp [ellP, hci], avg_gT C hC] at hb
  rw [neg_div] at hb
  constructor <;> linarith [hb.1, hb.2]

/-- **Bounds of the `λ` average of a pair cell from its records.** -/
lemma avg_gS_bounds (C : EXPCell) (hC : C ∈ exPCells) (R : EX2DRec)
    (hR : ex2DOK C R = true) :
    ((exLamLo C R : ℚ) : ℝ) ≤ (∫ p in exIP C, gS p ∂(unif.prod unif)) / ((exHy : ℝ) * (C.u1 - C.u0)) ∧
      (∫ p in exIP C, gS p ∂(unif.prod unif)) / ((exHy : ℝ) * (C.u1 - C.u0)) ≤ ((exLamHi C R : ℚ) : ℝ) := by
  obtain ⟨-, -, -, hu01, -, -⟩ := exP_facts hC
  obtain ⟨r00, r01, r10, r11, -⟩ := ex2DOK_parts hR
  have eYl : exYl C = exYlo C := rfl
  simp only [exYhi, eYl] at r00 r01 r10 r11
  have g00 := lnG_bounds r00; have g01 := lnG_bounds r01
  have g10 := lnG_bounds r10; have g11 := lnG_bounds r11
  have hly := ly_bounds C hC
  have l2 := crL2lo_lt; have l2' := log_two_lt_crL2hi
  rw [avg_gS C hC]
  have hA : (0 : ℝ) < (exHy : ℝ) * (C.u1 - C.u0) := by
    have : (0 : ℚ) < exHy * (C.u1 - C.u0) := mul_pos exHy_pos (by linarith)
    exact_mod_cast this
  have cast00 : ((exYlo C + C.u0 : ℚ) : ℝ) = (exYlo C : ℝ) + C.u0 := by push_cast; ring
  have cast01 : ((exYlo C + C.u1 : ℚ) : ℝ) = (exYlo C : ℝ) + C.u1 := by push_cast; ring
  have cast10 : ((exYlo C + exHy + C.u0 : ℚ) : ℝ) = ((exYlo C + exHy : ℚ) : ℝ) + C.u0 := by
    push_cast; ring
  have cast11 : ((exYlo C + exHy + C.u1 : ℚ) : ℝ) = ((exYlo C + exHy : ℚ) : ℝ) + C.u1 := by
    push_cast; ring
  rw [cast00] at g00; rw [cast01] at g01; rw [cast10] at g10; rw [cast11] at g11
  set Rr := lnG (((exYlo C + exHy : ℚ) : ℝ) + C.u1) - lnG ((exYlo C : ℝ) + C.u1) -
    (lnG (((exYlo C + exHy : ℚ) : ℝ) + C.u0) - lnG ((exYlo C : ℝ) + C.u0)) with hRr
  have eRhi : ((exRhi C R : ℚ) : ℝ) = ((gHi (exYlo C + exHy + C.u1) R.r11 : ℚ) : ℝ) -
      ((gLo (exYlo C + C.u1) R.r01 : ℚ) : ℝ) - ((gLo (exYlo C + exHy + C.u0) R.r10 : ℚ) : ℝ) +
      ((gHi (exYlo C + C.u0) R.r00 : ℚ) : ℝ) := by
    unfold exRhi; simp only [exYhi, eYl]; push_cast; ring
  have eRlo : ((exRlo C R : ℚ) : ℝ) = ((gLo (exYlo C + exHy + C.u1) R.r11 : ℚ) : ℝ) -
      ((gHi (exYlo C + C.u1) R.r01 : ℚ) : ℝ) - ((gHi (exYlo C + exHy + C.u0) R.r10 : ℚ) : ℝ) +
      ((gLo (exYlo C + C.u0) R.r00 : ℚ) : ℝ) := by
    unfold exRlo; simp only [exYhi, eYl]; push_cast; ring
  have hRhi : Rr ≤ ((exRhi C R : ℚ) : ℝ) := by
    rw [eRhi, hRr]; linarith [g00.2, g01.1, g10.1, g11.2]
  have hRlo : ((exRlo C R : ℚ) : ℝ) ≤ Rr := by
    rw [eRlo, hRr]; linarith [g00.1, g01.2, g10.2, g11.1]
  have d1 : Rr / ((exHy : ℝ) * (C.u1 - C.u0)) ≤ ((exRhi C R : ℚ) : ℝ) / ((exHy : ℝ) * (C.u1 - C.u0)) :=
    div_le_div_of_nonneg_right hRhi hA.le
  have d2 : ((exRlo C R : ℚ) : ℝ) / ((exHy : ℝ) * (C.u1 - C.u0)) ≤ Rr / ((exHy : ℝ) * (C.u1 - C.u0)) :=
    div_le_div_of_nonneg_right hRlo hA.le
  have eL : ((exLamLo C R : ℚ) : ℝ) = (crL2lo : ℝ) - (exBTup C.sa : ℝ) -
      (exRhi C R : ℝ) / ((exHy : ℝ) * ((C.u1 : ℝ) - C.u0)) := by unfold exLamLo; push_cast; ring
  have eH : ((exLamHi C R : ℚ) : ℝ) = (crL2hi : ℝ) - (exBTlo C.sa : ℝ) -
      (exRlo C R : ℝ) / ((exHy : ℝ) * ((C.u1 : ℝ) - C.u0)) := by unfold exLamHi; push_cast; ring
  rw [eL, eH]
  constructor <;> linarith [hly.1, hly.2]

/-! ### Records per cell index and weighted sums -/

lemma exZ2_len : (exPCells.zip ex2DRecs).length = KP := by
  rw [List.length_zip, ex2DRecs_len]; simp [KP, exPCells_len]

lemma ex2DRecs_len' (i : Fin KP) : i.1 < ex2DRecs.length := by
  rw [ex2DRecs_len]; have := i.2; simp only [KP, exPCells_len] at this; exact this

/-- The records of pair cell `i`. -/
def rec2 (i : Fin KP) : EX2DRec := ex2DRecs[i.1]'(ex2DRecs_len' i)

lemma rec2_ok (i : Fin KP) : ex2DOK (cP i) (rec2 i) = true := by
  have hi : i.1 < (exPCells.zip ex2DRecs).length := by rw [exZ2_len]; exact i.2
  have hm := (List.all_eq_true.1 ex2D_ok) _ (List.getElem_mem hi)
  rw [List.getElem_zip] at hm
  exact hm

/-- Weighted sums over the cells equal the kernel-checked list sums. -/
lemma sum2_eq (F : EXPCell → EX2DRec → ℚ) :
    ∑ i : Fin KP, ((cP i).a : ℝ) * ((F (cP i) (rec2 i) : ℚ) : ℝ) =
      ((((exPCells.zip ex2DRecs).map fun p => p.1.a * F p.1 p.2).sum : ℚ) : ℝ) := by
  set Z := exPCells.zip ex2DRecs
  set G := fun p : EXPCell × EX2DRec => (p.1.a : ℝ) * ((F p.1 p.2 : ℚ) : ℝ)
  have hrec : ∀ i : Fin KP, ((cP i).a : ℝ) * ((F (cP i) (rec2 i) : ℚ) : ℝ) =
      G (Z[i.1]'(by rw [exZ2_len]; exact i.2)) := by
    intro i; simp only [G, Z, List.getElem_zip, cP, rec2]
  rw [Finset.sum_congr rfl fun i _ => hrec i]
  refine (Fintype.sum_equiv (finCongr exZ2_len.symm) _ (fun j : Fin Z.length => G Z[j.1]) (fun i => rfl)).trans ?_
  rw [Fin.sum_univ_fun_getElem Z G, Rat.cast_list_sum, List.map_map]
  congr 1
  exact List.map_congr_left fun p _ => (Rat.cast_mul _ _).symm

lemma ellP_eq (i : Fin KP) : ellP i = (exHy : ℝ) * ((cP i).u1 - (cP i).u0) := rfl

/-- **Check S fails rarely on `E_X`.** -/
theorem EX_S_fail : ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N), r0 ≠ s → flipAt x r0 ≠ s →
    cubeM N (EX N s r0 x ∩ {w | ¬ (N : ℝ) / 400 ≤ ∑ j, gS (w r0 j, w (flipAt x r0) j)}) ≤
      cubeM N (EX N s r0 x) * ENNReal.ofReal (Real.exp (-(2 * N * (1 / (2 * 10 ^ 6)) ^ 2 / (1 - -1) ^ 2))) := by
  have hdev := EX_pair_dev_lo gS measurable_gS (a := -1) (b := 1) (by norm_num)
    (fun i p hp => gS_range (cP_mem i) hp) (fun i => (((rec2 i).sl : ℚ) : ℝ))
    (fun i => by
      rw [ellP_eq]
      exact ((Rat.cast_le (K := ℝ)).2 (ex2DOK_parts (rec2_ok i)).2.2.2.2.2.2.2.1).trans
        (avg_gS_bounds (cP i) (cP_mem i) (rec2 i) (rec2_ok i)).1)
    (E := exESlo) (by rw [sum2_eq (fun _ R => R.sl)]; exact (Rat.cast_le (K := ℝ)).2 exS_lo)
    (η := 1 / 10 ^ 6) (by norm_num)
  have hm := (Rat.cast_lt (K := ℝ)).2 ex2D_margins.1
  push_cast at hm
  filter_upwards [hdev] with N hN s r0 x h0 h1
  have he : (1 / 10 ^ 6 / 2 : ℝ) = 1 / (2 * 10 ^ 6) := by norm_num
  rw [he] at hN
  refine le_trans (measure_mono (s := EX N s r0 x ∩ {w | ¬ (N : ℝ) / 400 ≤ ∑ j, gS (w r0 j, w (flipAt x r0) j)})
    (t := EX N s r0 x ∩ {w | ∑ j, gS (w r0 j, w (flipAt x r0) j) ≤ N * (exESlo - 1 / 10 ^ 6)}) ?_)
    (hN s r0 x h0 h1)
  rintro w ⟨hw, hS⟩
  refine ⟨hw, ?_⟩
  simp only [Set.mem_setOf_eq, not_le] at hS ⊢
  have hX : ∑ j, gS (w r0 j, w (flipAt x r0) j) = ∑ j, gS (w r0 j, w (flipAt x r0) j) := rfl
  rw [← hX]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-! ### Check V -/

/-- `ln (y / f)`. -/
noncomputable def gC (p : ℝ × ℝ) : ℝ := Real.log (clamp01 p.1 / (1001 / 2000))
/-- The `V`-function `min(λ, ln(y/f))`. -/
noncomputable def gV (p : ℝ × ℝ) : ℝ := min (gS p) (gC p)

lemma measurable_gC : Measurable gC :=
  Real.measurable_log.comp ((clamp01_measurable.comp measurable_fst).div_const _)
lemma measurable_gV : Measurable gV := measurable_gS.min measurable_gC

lemma gC_eq {C : EXPCell} (hC : C ∈ exPCells) {p : ℝ × ℝ} (hp : p ∈ exIP C) :
    gC p = -gT p - Real.log (1001 / 2000) := by
  obtain ⟨-, -, a2, -, -, -, -, c1, -⟩ := cell_mem hC hp
  unfold gC gT; rw [c1, Real.log_div (by linarith) (by norm_num)]; ring

lemma gC_range {C : EXPCell} (hC : C ∈ exPCells) {p : ℝ × ℝ} (hp : p ∈ exIP C) : gC p ∈ Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨i, hi, hiC⟩ := List.getElem_of_mem hC
  have hT := gT_range ⟨i, hi⟩ p (by rw [show cP ⟨i, hi⟩ = C from hiC]; exact hp)
  rw [gC_eq hC hp]
  have hf := abs_le.1 (abs_log_le_one (t := 1001 / 2000) (by norm_num) (by norm_num))
  have hf' : Real.log (1001 / 2000) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  constructor <;> nlinarith [hT.1, hT.2]

lemma gV_range {C : EXPCell} (hC : C ∈ exPCells) {p : ℝ × ℝ} (hp : p ∈ exIP C) : gV p ∈ Set.Icc (-1 : ℝ) 1 := by
  have a := gS_range hC hp; have b := gC_range hC hp
  exact ⟨le_min a.1 b.1, (min_le_left _ _).trans a.2⟩

lemma intOn_of_range {C : EXPCell} {h : ℝ × ℝ → ℝ} (hm : Measurable h) {a b : ℝ}
    (hr : ∀ p ∈ exIP C, h p ∈ Set.Icc a b) : IntegrableOn h (exIP C) (unif.prod unif) :=
  cell_integrableOn h hm (|a| + |b|) fun p hp => by
    have := hr p hp
    rw [abs_le]; constructor
    · have := neg_abs_le a; have := abs_nonneg b; linarith [this, (hr p hp).1]
    · have := le_abs_self b; have := abs_nonneg a; linarith [(hr p hp).2]

lemma exArea (C : EXPCell) (hC : C ∈ exPCells) :
    (unif.prod unif).real (exIP C) = (exHy : ℝ) * (C.u1 - C.u0) := by
  have := exP_measure hC
  have hpos : (0 : ℝ) ≤ (exHy : ℝ) * (C.u1 - C.u0) := by
    obtain ⟨-, -, -, h, -⟩ := exP_facts hC
    have : (0 : ℚ) ≤ exHy * (C.u1 - C.u0) := mul_nonneg exHy_pos.le (by linarith)
    exact_mod_cast this
  rw [Measure.real, this, ENNReal.toReal_ofReal hpos]

lemma avg_gC (C : EXPCell) (hC : C ∈ exPCells) :
    (∫ p in exIP C, gC p ∂(unif.prod unif)) / ((exHy : ℝ) * (C.u1 - C.u0)) =
      -((∫ p in exIP C, gT p ∂(unif.prod unif)) / ((exHy : ℝ) * (C.u1 - C.u0))) - Real.log (1001 / 2000) := by
  obtain ⟨-, -, -, h, -⟩ := exP_facts hC
  have hA : (0 : ℝ) < (exHy : ℝ) * (C.u1 - C.u0) := by
    have : (0 : ℚ) < exHy * (C.u1 - C.u0) := mul_pos exHy_pos (by linarith)
    exact_mod_cast this
  have hT : IntegrableOn gT (exIP C) (unif.prod unif) := by
    obtain ⟨i, hi⟩ := List.getElem_of_mem hC
    have := gT_range ⟨i, hi.1⟩
    rw [show cP ⟨i, hi.1⟩ = C from hi.2] at this
    exact intOn_of_range measurable_gT this
  rw [setIntegral_congr_fun (exIP_meas C) (fun p hp => gC_eq hC hp),
    integral_sub (f := fun p => -gT p) (g := fun _ => Real.log (1001 / 2000)) hT.neg (integrable_const _),
    MeasureTheory.integral_neg, setIntegral_const, smul_eq_mul, exArea C hC]
  have hA0 : (exHy : ℝ) * ((C.u1 : ℝ) - C.u0) ≠ 0 := hA.ne'
  rw [sub_div, neg_div, mul_div_assoc, show (exHy : ℝ) * ((C.u1 : ℝ) - C.u0) *
    (Real.log (1001 / 2000) / ((exHy : ℝ) * ((C.u1 : ℝ) - C.u0))) = Real.log (1001 / 2000) by
      rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hA0, mul_one]]

lemma log_f_ge : ((exLnFlo : ℚ) : ℝ) ≤ Real.log (1001 / 2000) := by
  have := (lrec_sound exLnF_ok).1
  push_cast at this; exact this

/-- **The `V`-average of a pair cell is below `exVup`.** -/
lemma avg_gV_le (i : Fin KP) :
    (∫ p in exIP (cP i), gV p ∂(unif.prod unif)) / ellP i ≤ ((exVup (cP i) (rec2 i) : ℚ) : ℝ) := by
  rw [ellP_eq]
  set C := cP i
  have hC : C ∈ exPCells := cP_mem i
  obtain ⟨-, -, -, h, -⟩ := exP_facts hC
  have hA : (0 : ℝ) < (exHy : ℝ) * (C.u1 - C.u0) := by
    have : (0 : ℚ) < exHy * (C.u1 - C.u0) := mul_pos exHy_pos (by linarith)
    exact_mod_cast this
  have iS := intOn_of_range measurable_gS fun p hp => gS_range hC hp
  have iC := intOn_of_range measurable_gC fun p hp => gC_range hC hp
  have iV := intOn_of_range measurable_gV fun p hp => gV_range hC hp
  have m1 : ∫ p in exIP C, gV p ∂(unif.prod unif) ≤ ∫ p in exIP C, gS p ∂(unif.prod unif) :=
    setIntegral_mono_on iV iS (exIP_meas C) fun p _ => min_le_left _ _
  have m2 : ∫ p in exIP C, gV p ∂(unif.prod unif) ≤ ∫ p in exIP C, gC p ∂(unif.prod unif) :=
    setIntegral_mono_on iV iC (exIP_meas C) fun p _ => min_le_right _ _
  have bS := (avg_gS_bounds C hC (rec2 i) (rec2_ok i)).2
  have hT := (avg_gT_bounds i).1
  rw [ellP_eq] at hT
  have bC := avg_gC C hC
  have lf := log_f_ge
  unfold exVup
  rw [Rat.cast_min, le_min_iff]
  constructor
  · exact (div_le_div_of_nonneg_right m1 hA.le).trans bS
  · refine (div_le_div_of_nonneg_right m2 hA.le).trans ?_
    rw [bC]; push_cast; linarith

/-- **Check V fails rarely on `E_X`.** -/
theorem EX_V_fail : ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N), r0 ≠ s → flipAt x r0 ≠ s →
    cubeM N (EX N s r0 x ∩ {w | ¬ ∑ j, min (gS (w r0 j, w (flipAt x r0) j)) (Real.log (clamp01 (w r0 j) / (1001 / 2000))) ≤
        -((N : ℝ) / (2 * 10 ^ 6))}) ≤
      cubeM N (EX N s r0 x) * ENNReal.ofReal (Real.exp (-(2 * N * (1 / (10 ^ 7)) ^ 2 / (1 - -1) ^ 2))) := by
  have hdev := EX_pair_dev gV measurable_gV (a := -1) (b := 1) (by norm_num)
    (fun i p hp => gV_range (cP_mem i) hp) (fun i => (((rec2 i).vu : ℚ) : ℝ))
    (fun i => (avg_gV_le i).trans ((Rat.cast_le (K := ℝ)).2 (ex2DOK_parts (rec2_ok i)).2.2.2.2.2.2.2.2.1))
    (E := exEVup) (by rw [sum2_eq (fun _ R => R.vu)]; exact (Rat.cast_le (K := ℝ)).2 exV_up)
    (η := 2 / 10 ^ 7) (by norm_num)
  have hm := (Rat.cast_lt (K := ℝ)).2 ex2D_margins.2.1
  push_cast at hm
  filter_upwards [hdev] with N hN s r0 x h0 h1
  have he : (2 / 10 ^ 7 / 2 : ℝ) = 1 / 10 ^ 7 := by norm_num
  rw [he] at hN
  refine le_trans (measure_mono (s := EX N s r0 x ∩ {w | ¬ ∑ j, min (gS (w r0 j, w (flipAt x r0) j))
      (Real.log (clamp01 (w r0 j) / (1001 / 2000))) ≤ -((N : ℝ) / (2 * 10 ^ 6))})
    (t := EX N s r0 x ∩ {w | N * (exEVup + 2 / 10 ^ 7) ≤ ∑ j, gV (w r0 j, w (flipAt x r0) j)}) ?_)
    (hN s r0 x h0 h1)
  rintro w ⟨hw, hV⟩
  refine ⟨hw, ?_⟩
  simp only [Set.mem_setOf_eq, not_le] at hV ⊢
  have hX : ∑ j, min (gS (w r0 j, w (flipAt x r0) j)) (Real.log (clamp01 (w r0 j) / (1001 / 2000))) =
      ∑ j, gV (w r0 j, w (flipAt x r0) j) := rfl
  rw [← hX]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-! ### Check M0 -/

/-- The `M0`-function `min(λ, ln 2y)`. -/
noncomputable def gM (p : ℝ × ℝ) : ℝ := min (gS p) (Real.log (2 * clamp01 p.1))

lemma measurable_gM : Measurable gM :=
  measurable_gS.min (Real.measurable_log.comp (measurable_const.mul (clamp01_measurable.comp measurable_fst)))

lemma log2y_eq {C : EXPCell} (hC : C ∈ exPCells) {p : ℝ × ℝ} (hp : p ∈ exIP C) :
    Real.log (2 * clamp01 p.1) = Real.log 2 - gT p := by
  obtain ⟨-, -, a2, -, -, -, -, c1, -⟩ := cell_mem hC hp
  unfold gT; rw [c1, Real.log_mul (by norm_num) (by linarith)]; ring

lemma gM_range {C : EXPCell} (hC : C ∈ exPCells) {p : ℝ × ℝ} (hp : p ∈ exIP C) : gM p ∈ Set.Icc (-1 : ℝ) 1 := by
  have a := gS_range hC hp
  obtain ⟨-, a1, a2, -, -, -, -, c1, -⟩ := cell_mem hC hp
  have b := abs_le.1 (abs_log_le_one (t := 2 * clamp01 p.1) (by rw [c1]; linarith) (by rw [c1]; linarith))
  exact ⟨le_min a.1 b.1, (min_le_left _ _).trans a.2⟩

/-- Pointwise lower bound `min(λ, ln 2y) ≥ ln 2 + ln y - (y + u - 1)⁺` on a cell. -/
lemma gM_ge {C : EXPCell} (hC : C ∈ exPCells) {p : ℝ × ℝ} (hp : p ∈ exIP C) :
    Real.log 2 - gT p - max (p.1 + p.2 - 1) 0 ≤ gM p := by
  obtain ⟨-, a1, a2, -, -, a3, a4, c1, c2⟩ := cell_mem hC hp
  unfold gM
  rw [gS_eq hC hp, log2y_eq hC hp]
  have hT : gT p = -Real.log p.1 := by unfold gT; rw [c1]
  rw [hT]
  refine le_min ?_ ?_
  · have := Real.log_le_sub_one_of_pos (show 0 < p.1 + p.2 by linarith)
    have := le_max_left (p.1 + p.2 - 1) 0
    linarith
  · have := le_max_right (p.1 + p.2 - 1) 0; linarith

lemma gM_cap {C : EXPCell} (hC : C ∈ exPCells) (hcap : (C.u1 : ℝ) ≤ 1 - ((exYlo C + exHy : ℚ) : ℝ))
    {p : ℝ × ℝ} (hp : p ∈ exIP C) : gM p = Real.log 2 - gT p := by
  obtain ⟨h1, -, a2, -, a5, a3, -, c1, -⟩ := cell_mem hC hp
  have hy1 : p.1 < ((exYlo C + exHy : ℚ) : ℝ) := hp.1.2
  unfold gM; rw [gS_eq hC hp, log2y_eq hC hp]
  have hT : gT p = -Real.log p.1 := by unfold gT; rw [c1]
  rw [hT, min_eq_right]
  have : Real.log (p.1 + p.2) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  linarith

lemma gM_lam {C : EXPCell} (hC : C ∈ exPCells) (hlam : 1 - (exYlo C : ℝ) ≤ C.u0)
    {p : ℝ × ℝ} (hp : p ∈ exIP C) : gM p = gS p := by
  obtain ⟨h1, -, a2, h4, -, a3, -, c1, -⟩ := cell_mem hC hp
  unfold gM; rw [min_eq_left]
  rw [gS_eq hC hp, log2y_eq hC hp]
  have hT : gT p = -Real.log p.1 := by unfold gT; rw [c1]
  rw [hT]
  have : 0 ≤ Real.log (p.1 + p.2) := Real.log_nonneg (by linarith)
  linarith

lemma hP_eq (t : ℚ) : ((hP t : ℚ) : ℝ) = max (t : ℝ) 0 ^ 3 / 6 := by
  unfold hP; split_ifs with h
  · rw [max_eq_left (by exact_mod_cast h.le)]; push_cast; ring
  · push_neg at h; rw [max_eq_right (by exact_mod_cast h)]; push_cast; ring

/-- **The `M0`-average of a pair cell is above `exMlo`.** -/
lemma avg_gM_ge (i : Fin KP) :
    ((exMlo (cP i) (rec2 i) : ℚ) : ℝ) ≤ (∫ p in exIP (cP i), gM p ∂(unif.prod unif)) / ellP i := by
  rw [ellP_eq]
  set C := cP i
  have hC : C ∈ exPCells := cP_mem i
  obtain ⟨-, -, hu0, hu01, -, -⟩ := exP_facts hC
  have hA : (0 : ℝ) < (exHy : ℝ) * (C.u1 - C.u0) := by
    have : (0 : ℚ) < exHy * (C.u1 - C.u0) := mul_pos exHy_pos (by linarith)
    exact_mod_cast this
  have iT : IntegrableOn gT (exIP C) (unif.prod unif) := intOn_of_range measurable_gT (gT_range i)
  have hT := avg_gT_bounds i
  rw [ellP_eq] at hT
  have l2 := crL2lo_lt
  unfold exMlo
  simp only [exYhi, show exYl C = exYlo C from rfl]
  split_ifs with hcap hlam
  · -- cap cells
    have hcap' : (C.u1 : ℝ) ≤ 1 - ((exYlo C + exHy : ℚ) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).2 hcap; push_cast at this ⊢; linarith
    rw [setIntegral_congr_fun (exIP_meas C) (fun p hp => gM_cap hC hcap' hp),
      integral_sub (f := fun _ => Real.log 2) (g := gT) (integrable_const _) iT, setIntegral_const, smul_eq_mul,
      exArea C hC]
    have hI : (∫ p in exIP C, gT p ∂(unif.prod unif)) ≤ (exBTup C.sa : ℝ) * ((exHy : ℝ) * (C.u1 - C.u0)) := by
      have := hT.2; rwa [div_le_iff₀ hA] at this
    rw [le_div_iff₀ hA]; push_cast; nlinarith [l2]
  · -- lambda cells
    have hlam' : 1 - (exYlo C : ℝ) ≤ C.u0 := by
      have := (Rat.cast_le (K := ℝ)).2 hlam; push_cast at this; exact this
    rw [setIntegral_congr_fun (exIP_meas C) (fun p hp => gM_lam hC hlam' hp)]
    exact (avg_gS_bounds C hC (rec2 i) (rec2_ok i)).1
  · -- mixed cells
    set mF : ℝ × ℝ → ℝ := fun p => max (p.1 + p.2 - 1) 0
    have hmc : Continuous mF := ((continuous_fst.add continuous_snd).sub continuous_const).max continuous_const
    have iM : IntegrableOn mF (exIP C) (unif.prod unif) :=
      cell_integrableOn mF hmc.measurable 1 fun p hp => by
        obtain ⟨-, a1, -, -, -, a3, a4, -, -⟩ := cell_mem hC hp
        rw [abs_le]; constructor
        · have := le_max_right (p.1 + p.2 - 1) 0; simp only [mF]; linarith
        · simp only [mF]; exact max_le (by linarith) (by norm_num)
    have iV := intOn_of_range measurable_gM fun p hp => gM_range hC hp
    have hmono : ∫ p in exIP C, (Real.log 2 - gT p - mF p) ∂(unif.prod unif) ≤
        ∫ p in exIP C, gM p ∂(unif.prod unif) :=
      setIntegral_mono_on (((integrable_const _).sub iT).sub iM) iV (exIP_meas C) fun p hp => gM_ge hC hp
    rw [integral_sub (f := fun p => Real.log 2 - gT p) (g := mF) ((integrable_const _).sub iT) iM,
      integral_sub (f := fun _ => Real.log 2) (g := gT) (integrable_const _) iT, setIntegral_const,
      smul_eq_mul, exArea C hC] at hmono
    have hPint : ∫ p in exIP C, mF p ∂(unif.prod unif) =
        (max (((exYlo C + exHy : ℚ) : ℝ) + C.u1 - 1) 0 ^ 3 - max ((exYlo C : ℝ) + C.u1 - 1) 0 ^ 3 -
          (max (((exYlo C + exHy : ℚ) : ℝ) + C.u0 - 1) 0 ^ 3 - max ((exYlo C : ℝ) + C.u0 - 1) 0 ^ 3)) / 6 := by
      rw [cell_integral C hC mF iM]
      have hYY : (exYlo C : ℝ) ≤ ((exYlo C + exHy : ℚ) : ℝ) := by
        have := exHy_pos; exact_mod_cast (by linarith : exYlo C ≤ exYlo C + exHy)
      exact integral_rect_posPart hYY (by exact_mod_cast hu01.le)
    rw [hPint] at hmono
    refine le_trans ?_ (div_le_div_of_nonneg_right hmono hA.le)
    have hI : (∫ p in exIP C, gT p ∂(unif.prod unif)) ≤ (exBTup C.sa : ℝ) * ((exHy : ℝ) * (C.u1 - C.u0)) := by
      have := hT.2; rwa [div_le_iff₀ hA] at this
    rw [le_div_iff₀ hA]
    push_cast at hI ⊢; simp only [hP_eq]; push_cast
    rw [sub_mul, div_mul_cancel₀ _ hA.ne']
    nlinarith [mul_le_mul_of_nonneg_right l2.le hA.le, hI]

/-! ### Check D -/

/-- The `D`-function `ln y - ln max(U, δ)` (`≤ ln(y/U)` for `U > 0`). -/
noncomputable def gD (p : ℝ × ℝ) : ℝ := Real.log (clamp01 p.1) - Real.log (max (clamp01 p.2) (exDEL : ℝ))

lemma exDEL_val : ((exDEL : ℚ) : ℝ) = 1 / 10 ^ 5 := by unfold exDEL; push_cast; ring

lemma measurable_gD : Measurable gD :=
  (Real.measurable_log.comp (clamp01_measurable.comp measurable_fst)).sub
    (Real.measurable_log.comp ((clamp01_measurable.comp measurable_snd).max measurable_const))

lemma gD_range {C : EXPCell} (hC : C ∈ exPCells) {p : ℝ × ℝ} (hp : p ∈ exIP C) : gD p ∈ Set.Icc (-1 : ℝ) 12 := by
  obtain ⟨-, a1, a2, -, -, a3, a4, c1, c2⟩ := cell_mem hC hp
  unfold gD; rw [c1, c2, exDEL_val]
  have hm1 : max p.2 (1 / 10 ^ 5 : ℝ) ≤ 1 := max_le a4 (by norm_num)
  have hm0 : (1 / 10 ^ 5 : ℝ) ≤ max p.2 (1 / 10 ^ 5) := le_max_right _ _
  have ly := abs_le.1 (abs_log_le_one a2 (by linarith))
  have ly0 : Real.log p.1 ≤ 0 := Real.log_nonpos (by linarith) a1
  have lm0 : Real.log (max p.2 (1 / 10 ^ 5)) ≤ 0 := Real.log_nonpos (by linarith) hm1
  have lm1 : Real.log (1 / 10 ^ 5 : ℝ) ≤ Real.log (max p.2 (1 / 10 ^ 5)) := Real.log_le_log (by norm_num) hm0
  have hd : -12 ≤ Real.log (1 / 10 ^ 5 : ℝ) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_gt_d9
    have h12 : Real.exp (-12) = (Real.exp 1)⁻¹ ^ 12 := by
      rw [← Real.exp_neg, ← Real.exp_nat_mul]; norm_num
    rw [h12]
    have : (Real.exp 1)⁻¹ ≤ 1 / 2.7 := by
      rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; norm_num; linarith
    calc (Real.exp 1)⁻¹ ^ 12 ≤ (1 / 2.7 : ℝ) ^ 12 := pow_le_pow_left₀ (by positivity) this 12
      _ ≤ 1 / 10 ^ 5 := by norm_num
  constructor <;> linarith

/-- `∫_{u0}^{u1} ln max(u, δ) = (m - u0) ln δ + (u1 ln u1 - m ln m - u1 + m)`, `m = max(u0, δ) ≤ u1`. -/
lemma integral_log_max {u0 u1 δ : ℝ} (hδ : 0 < δ) (hu0 : 0 ≤ u0) (hδu : δ ≤ u1) (hu : u0 ≤ u1) :
    ∫ u in u0..u1, Real.log (max u δ) =
      (max u0 δ - u0) * Real.log δ + (u1 * Real.log u1 - max u0 δ * Real.log (max u0 δ) - u1 + max u0 δ) := by
  rcases le_total δ u0 with h | h
  · rw [max_eq_left h, sub_self, zero_mul, zero_add,
      intervalIntegral.integral_congr (g := Real.log) fun u hu' => by
        rw [Set.uIcc_of_le hu] at hu'; simp only [max_eq_left (h.trans hu'.1)], integral_log]
  · rw [max_eq_right h]
    have hc : ContinuousOn (fun u => Real.log (max u δ)) (Set.uIcc u0 u1) :=
      Real.continuousOn_log.comp (continuous_id.max continuous_const).continuousOn fun u _ => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; have := le_max_right u δ; intro h'; linarith
    have i1 : IntervalIntegrable (fun u => Real.log (max u δ)) MeasureTheory.volume u0 δ :=
      (hc.mono (by intro u hu'; rw [Set.uIcc_of_le h] at hu'; rw [Set.uIcc_of_le hu]
                   exact ⟨hu'.1, hu'.2.trans hδu⟩)).intervalIntegrable
    have i2 : IntervalIntegrable (fun u => Real.log (max u δ)) MeasureTheory.volume δ u1 :=
      (hc.mono (by intro u hu'; rw [Set.uIcc_of_le hδu] at hu'; rw [Set.uIcc_of_le hu]
                   exact ⟨h.trans hu'.1, hu'.2⟩)).intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
    rw [intervalIntegral.integral_congr (g := fun _ => Real.log δ) (a := u0) (b := δ) fun u hu' => by
        rw [Set.uIcc_of_le h] at hu'; simp only [max_eq_right hu'.2],
      intervalIntegral.integral_congr (g := Real.log) (a := δ) (b := u1) fun u hu' => by
        rw [Set.uIcc_of_le hδu] at hu'; simp only [max_eq_left hu'.1],
      intervalIntegral.integral_const, integral_log, smul_eq_mul]

/-- **The `D`-average of a pair cell is above `exDlo`.** -/
lemma avg_gD_ge (i : Fin KP) :
    ((exDlo (cP i) (rec2 i) : ℚ) : ℝ) ≤ (∫ p in exIP (cP i), gD p ∂(unif.prod unif)) / ellP i := by
  rw [ellP_eq]
  set C := cP i
  have hC : C ∈ exPCells := cP_mem i
  obtain ⟨-, -, hu0, hu01, hu1, -⟩ := exP_facts hC
  obtain ⟨-, -, -, -, rm, ru, hdu, -⟩ := ex2DOK_parts (rec2_ok i)
  have lm := lrec_sound rm; have lu := lrec_sound ru
  have hA : (0 : ℝ) < (exHy : ℝ) * (C.u1 - C.u0) := by
    have : (0 : ℚ) < exHy * (C.u1 - C.u0) := mul_pos exHy_pos (by linarith)
    exact_mod_cast this
  have hw : (0 : ℝ) < (C.u1 : ℝ) - C.u0 := by
    have : (C.u0 : ℝ) < C.u1 := by exact_mod_cast hu01
    linarith
  have hhy : (0 : ℝ) < exHy := by exact_mod_cast exHy_pos
  have hδ : (0 : ℝ) < (exDEL : ℝ) := by rw [exDEL_val]; norm_num
  have hu0' : (0 : ℝ) ≤ C.u0 := by exact_mod_cast hu0
  have hdu' : (exDEL : ℝ) ≤ C.u1 := by exact_mod_cast hdu
  -- the integrand
  set L : ℝ → ℝ := fun u => Real.log (max u (exDEL : ℝ))
  have hLm : Measurable L := Real.measurable_log.comp (measurable_id.max measurable_const)
  have hcong : ∀ p ∈ exIP C, gD p = -gT p - L p.2 := fun p hp => by
    obtain ⟨-, -, -, -, -, -, -, c1, c2⟩ := cell_mem hC hp
    simp only [gD, gT, L, c1, c2]; ring
  have iT : IntegrableOn gT (exIP C) (unif.prod unif) := intOn_of_range measurable_gT (gT_range i)
  have iL : IntegrableOn (fun p : ℝ × ℝ => L p.2) (exIP C) (unif.prod unif) :=
    cell_integrableOn _ (hLm.comp measurable_snd) 12 fun p hp => by
      obtain ⟨-, -, -, -, -, a3, a4, -, -⟩ := cell_mem hC hp
      have hm1 : max p.2 (exDEL : ℝ) ≤ 1 := max_le a4 (by rw [exDEL_val]; norm_num)
      have hm0 : (exDEL : ℝ) ≤ max p.2 (exDEL : ℝ) := le_max_right _ _
      have h1 : Real.log (max p.2 (exDEL : ℝ)) ≤ 0 := Real.log_nonpos (by linarith) hm1
      have h2 : Real.log (exDEL : ℝ) ≤ Real.log (max p.2 (exDEL : ℝ)) := Real.log_le_log hδ hm0
      have h3 : -12 ≤ Real.log (exDEL : ℝ) := by
        have := (gD_range hC hp).2
        rw [exDEL_val]
        rw [Real.le_log_iff_exp_le (by norm_num)]
        have := Real.exp_one_gt_d9
        have h12 : Real.exp (-12) = (Real.exp 1)⁻¹ ^ 12 := by rw [← Real.exp_neg, ← Real.exp_nat_mul]; norm_num
        rw [h12]
        have : (Real.exp 1)⁻¹ ≤ 1 / 2.7 := by
          rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; norm_num; linarith
        calc (Real.exp 1)⁻¹ ^ 12 ≤ (1 / 2.7 : ℝ) ^ 12 := pow_le_pow_left₀ (by positivity) this 12
          _ ≤ 1 / 10 ^ 5 := by norm_num
      simp only [L]; rw [abs_le]; constructor <;> linarith
  rw [setIntegral_congr_fun (exIP_meas C) hcong,
    integral_sub (f := fun p => -gT p) (g := fun p : ℝ × ℝ => L p.2) iT.neg iL, MeasureTheory.integral_neg]
  -- the `u`-integral
  have hLint : ∫ p in exIP C, L p.2 ∂(unif.prod unif) = (exHy : ℝ) * ∫ u in (C.u0 : ℝ)..C.u1, L u := by
    have hYY : (exYlo C : ℝ) ≤ ((exYlo C + exHy : ℚ) : ℝ) := by
      have := exHy_pos; exact_mod_cast (by linarith : exYlo C ≤ exYlo C + exHy)
    have := setIntegral_prod_mul (μ := unif) (ν := unif) (fun _ : ℝ => (1 : ℝ)) L
      (Set.Ico (exYlo C : ℝ) ((exYlo C + exHy : ℚ) : ℝ)) (Set.Ico (C.u0 : ℝ) C.u1)
    simp only [one_mul] at this
    rw [exIP, this, setIntegral_const, smul_eq_mul, mul_one, Measure.real,
      unif_Ico (exYlo_pos C).le hYY (exYhi_le C hC), ENNReal.toReal_ofReal (by linarith),
      unif_setIntegral_Ico (a := (C.u0 : ℝ)) (b := (C.u1 : ℝ)) hu0' (by exact_mod_cast hu01.le)
        (by exact_mod_cast hu1) L]
    push_cast; ring
  rw [hLint, integral_log_max hδ hu0' hdu' (by exact_mod_cast hu01.le)]
  have hT := (avg_gT_bounds i).2
  rw [ellP_eq] at hT
  -- bounds from the records
  set m : ℝ := max (C.u0 : ℝ) (exDEL : ℝ)
  have hmq : ((max C.u0 exDEL : ℚ) : ℝ) = m := by push_cast; rfl
  rw [hmq] at lm
  have hm0 : 0 < m := lt_of_lt_of_le hδ (le_max_right _ _)
  have b1 : m * ((rec2 i).lom : ℝ) ≤ m * Real.log m := mul_le_mul_of_nonneg_left lm.1 hm0.le
  have b2 : (C.u1 : ℝ) * Real.log C.u1 ≤ C.u1 * ((rec2 i).hiu : ℝ) :=
    mul_le_mul_of_nonneg_left lu.2 (by linarith)
  have b3 : (m - C.u0) * Real.log (exDEL : ℝ) ≤ max ((exDEL : ℝ) - C.u0) 0 * ((rec2 i).him : ℝ) := by
    rcases le_total (exDEL : ℝ) C.u0 with h | h
    · have : m = C.u0 := max_eq_left h
      rw [this, sub_self, zero_mul, max_eq_right (by linarith), zero_mul]
    · have : m = exDEL := max_eq_right h
      rw [this] at lm ⊢
      rw [max_eq_left (by linarith)]
      exact mul_le_mul_of_nonneg_left lm.2 (by linarith)
  have hIU : (m - C.u0) * Real.log (exDEL : ℝ) + ((C.u1 : ℝ) * Real.log C.u1 - m * Real.log m - C.u1 + m) ≤
      C.u1 * ((rec2 i).hiu : ℝ) - C.u1 - (m * ((rec2 i).lom : ℝ) - m) +
        max ((exDEL : ℝ) - C.u0) 0 * ((rec2 i).him : ℝ) := by linarith
  unfold exDlo
  have hcast : (((C.u1 * (rec2 i).hiu - C.u1 - (max C.u0 exDEL * (rec2 i).lom - max C.u0 exDEL) +
      max (exDEL - C.u0) 0 * (rec2 i).him) / (C.u1 - C.u0) : ℚ) : ℝ) =
      ((C.u1 : ℝ) * ((rec2 i).hiu : ℝ) - C.u1 - (m * ((rec2 i).lom : ℝ) - m) +
        max ((exDEL : ℝ) - C.u0) 0 * ((rec2 i).him : ℝ)) / ((C.u1 : ℝ) - C.u0) := by
    push_cast; simp only [m]
  push_cast at hcast ⊢
  have key : -(∫ p in exIP C, gT p ∂(unif.prod unif)) / ((exHy : ℝ) * (C.u1 - C.u0)) ≥ -((exBTup C.sa : ℚ) : ℝ) := by
    rw [neg_div]; linarith
  rw [sub_div]
  have hsplit : (exHy : ℝ) * ((m - C.u0) * Real.log (exDEL : ℝ) +
      ((C.u1 : ℝ) * Real.log C.u1 - m * Real.log m - C.u1 + m)) / ((exHy : ℝ) * (C.u1 - C.u0)) =
      ((m - C.u0) * Real.log (exDEL : ℝ) + ((C.u1 : ℝ) * Real.log C.u1 - m * Real.log m - C.u1 + m)) /
        ((C.u1 : ℝ) - C.u0) := by
    rw [mul_div_mul_left _ _ hhy.ne']
  rw [hsplit]
  have hdiv := div_le_div_of_nonneg_right hIU hw.le
  linarith

/-- **Check M0 fails rarely on `E_X`.** -/
theorem EX_M_fail : ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N), r0 ≠ s → flipAt x r0 ≠ s →
    cubeM N (EX N s r0 x ∩ {w | ¬ (N : ℝ) / 10 ^ 5 ≤ ∑ j, min (gS (w r0 j, w (flipAt x r0) j)) (Real.log (2 * clamp01 (w r0 j)))}) ≤
      cubeM N (EX N s r0 x) * ENNReal.ofReal (Real.exp (-(2 * N * (1 / (10 ^ 7)) ^ 2 / (1 - -1) ^ 2))) := by
  have hdev := EX_pair_dev_lo gM measurable_gM (a := -1) (b := 1) (by norm_num)
    (fun i p hp => gM_range (cP_mem i) hp) (fun i => (((rec2 i).ml : ℚ) : ℝ))
    (fun i => ((Rat.cast_le (K := ℝ)).2 (ex2DOK_parts (rec2_ok i)).2.2.2.2.2.2.2.2.2.1).trans (avg_gM_ge i))
    (E := exEMlo) (by rw [sum2_eq (fun _ R => R.ml)]; exact (Rat.cast_le (K := ℝ)).2 exM_lo)
    (η := 2 / 10 ^ 7) (by norm_num)
  have hm := (Rat.cast_lt (K := ℝ)).2 ex2D_margins.2.2.1
  push_cast at hm
  filter_upwards [hdev] with N hN s r0 x h0 h1
  have he : (2 / 10 ^ 7 / 2 : ℝ) = 1 / 10 ^ 7 := by norm_num
  rw [he] at hN
  refine le_trans (measure_mono (s := EX N s r0 x ∩ {w | ¬ (N : ℝ) / 10 ^ 5 ≤
      ∑ j, min (gS (w r0 j, w (flipAt x r0) j)) (Real.log (2 * clamp01 (w r0 j)))})
    (t := EX N s r0 x ∩ {w | ∑ j, gM (w r0 j, w (flipAt x r0) j) ≤ N * (exEMlo - 2 / 10 ^ 7)}) ?_)
    (hN s r0 x h0 h1)
  rintro w ⟨hw, hM⟩
  refine ⟨hw, ?_⟩
  simp only [Set.mem_setOf_eq, not_le] at hM ⊢
  have hX : ∑ j, min (gS (w r0 j, w (flipAt x r0) j)) (Real.log (2 * clamp01 (w r0 j))) =
      ∑ j, gM (w r0 j, w (flipAt x r0) j) := rfl
  rw [← hX]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-- **Check D fails rarely on `E_X`** (on the open cube). -/
theorem EX_D_fail : ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N), r0 ≠ s → flipAt x r0 ≠ s →
    cubeM N (EX N s r0 x ∩ openCube N ∩
        {w | ¬ (N : ℝ) / 30 ≤ ∑ j, Real.log (clamp01 (w r0 j) / clamp01 (w (flipAt x r0) j))}) ≤
      cubeM N (EX N s r0 x) * ENNReal.ofReal (Real.exp (-(2 * N * (1 / (2 * 10 ^ 3)) ^ 2 / (12 - -1) ^ 2))) := by
  have hdev := EX_pair_dev_lo gD measurable_gD (a := -1) (b := 12) (by norm_num)
    (fun i p hp => gD_range (cP_mem i) hp) (fun i => (((rec2 i).dl : ℚ) : ℝ))
    (fun i => ((Rat.cast_le (K := ℝ)).2 (ex2DOK_parts (rec2_ok i)).2.2.2.2.2.2.2.2.2.2).trans (avg_gD_ge i))
    (E := exEDlo) (by rw [sum2_eq (fun _ R => R.dl)]; exact (Rat.cast_le (K := ℝ)).2 exD_lo)
    (η := 1 / 10 ^ 3) (by norm_num)
  have hm := (Rat.cast_lt (K := ℝ)).2 ex2D_margins.2.2.2
  push_cast at hm
  filter_upwards [hdev] with N hN s r0 x h0 h1
  have he : (1 / 10 ^ 3 / 2 : ℝ) = 1 / (2 * 10 ^ 3) := by norm_num
  rw [he] at hN
  refine le_trans (measure_mono (s := EX N s r0 x ∩ openCube N ∩
      {w | ¬ (N : ℝ) / 30 ≤ ∑ j, Real.log (clamp01 (w r0 j) / clamp01 (w (flipAt x r0) j))})
    (t := EX N s r0 x ∩ {w | ∑ j, gD (w r0 j, w (flipAt x r0) j) ≤ N * (exEDlo - 1 / 10 ^ 3)}) ?_)
    (hN s r0 x h0 h1)
  rintro w ⟨⟨hw, ho⟩, hD⟩
  refine ⟨hw, ?_⟩
  simp only [Set.mem_setOf_eq, not_le] at hD ⊢
  have hle : ∀ j, gD (w r0 j, w (flipAt x r0) j) ≤ Real.log (clamp01 (w r0 j) / clamp01 (w (flipAt x r0) j)) := by
    intro j
    have hy := ho r0 j; have hu := ho (flipAt x r0) j
    have cy : clamp01 (w r0 j) = w r0 j := by
      unfold clamp01; rw [min_eq_right hy.2.le, max_eq_right hy.1.le]
    have cu : clamp01 (w (flipAt x r0) j) = w (flipAt x r0) j := by
      unfold clamp01; rw [min_eq_right hu.2.le, max_eq_right hu.1.le]
    simp only [gD, cy, cu]
    rw [Real.log_div hy.1.ne' hu.1.ne']
    have : Real.log (w (flipAt x r0) j) ≤ Real.log (max (w (flipAt x r0) j) (exDEL : ℝ)) :=
      Real.log_le_log hu.1 (le_max_left _ _)
    linarith
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ univ) => hle j
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

end Census
end IIT
