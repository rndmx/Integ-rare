/-
Census, Lemma RS: soundness of the cause-cell certificate.  From `rsCellOK C = true`:
`log 2 + log I + log Ex + t · x0 ≤ -R0` with `I = ∫_{v⁴}^1 y^{P/4} gX λ (w⁴) y dy`, `t = P/4 + l_u`.
-/
import IIT.Census.CertRSX
import IIT.Census.B1RegRS

namespace IIT
namespace Census

open Finset MeasureTheory

lemma gX_pos (lam : ℕ) {c y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hc : 0 < c) (hcy : y ≤ 2 * c) :
    0 < gX lam c y := by
  rw [← integral_maxpow lam hy hy1 hc hcy]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (Continuous.intervalIntegrable (by fun_prop) _ _)
    (fun u _ => pow_pos ?_ _) zero_lt_one
  exact lt_of_lt_of_le (lt_min one_pos (div_pos hc hy)) (le_max_right _ _)

/-- The real integral of a certified cell is positive. -/
lemma cellI_pos (C : RSCell) (hv : 0 < C.v) (hvw : C.v ≤ C.w) (hv1 : C.v < 1)
    (hw2 : (1 : ℚ) / 2 ≤ C.w ^ 4) :
    0 < ∫ y in ((C.v : ℝ) ^ 4)..1, y ^ ((C.P : ℝ) / 4) * gX C.lam ((C.w : ℝ) ^ 4) y := by
  have hv' : (0 : ℝ) < C.v := by exact_mod_cast hv
  have hw' : (0 : ℝ) < C.w := by exact_mod_cast (lt_of_lt_of_le hv hvw)
  have hvw' : (C.v : ℝ) ^ 4 ≤ (C.w : ℝ) ^ 4 := pow_le_pow_left₀ hv'.le (by exact_mod_cast hvw) 4
  have hv1' : (C.v : ℝ) ^ 4 < 1 := pow_lt_one₀ hv'.le (by exact_mod_cast hv1) (by norm_num)
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun y hy => ?_) hv1'
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hv1'.le]
    have hpos : (0 : ℝ) < (C.v : ℝ) ^ 4 := by positivity
    exact (ContinuousOn.rpow_const continuousOn_id fun y hy =>
      Or.inl (lt_of_lt_of_le hpos hy.1).ne').mul (gX_continuousOn C.lam _ hpos)
  · have hy0 : 0 < y := lt_trans (by positivity) hy.1
    refine mul_pos (Real.rpow_pos_of_pos hy0 _) (gX_pos C.lam hy0 hy.2.le (by positivity) ?_)
    have : (1 : ℝ) / 2 ≤ (C.w : ℝ) ^ 4 := by
      have h := (Rat.cast_le (K := ℝ)).2 hw2; push_cast at h; exact h
    linarith [hy.2]

/-- **Soundness of one certified cause cell.** -/
theorem rsCell_sound (C : RSCell) (h : rsCellOK C = true) :
    Real.log 2 + Real.log (∫ y in ((C.v : ℝ) ^ 4)..1, y ^ ((C.P : ℝ) / 4) * gX C.lam ((C.w : ℝ) ^ 4) y) +
      Real.log (rsEx C.lu : ℝ) + ((C.P : ℝ) / 4 + C.lu) * x0 ≤ -(rsR0 : ℝ) := by
  simp only [rsCellOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hvw⟩, hw1⟩, hv1⟩, hw2⟩, hk⟩, hp⟩, h0⟩, h1⟩, hub⟩, hq⟩, hx⟩, hhi⟩, hrate⟩ := h
  have hI := cellIq_eq C.v C.w hv hvw hw1 C.lam C.P
    (fun k hkm => hk k (Finset.mem_range.1 hkm)) hp h0 h1
  rw [← hI]
  have hIpos : (0 : ℝ) < cellIq C.v C.w C.lam C.P := by rw [hI]; exact cellI_pos C hv hvw hv1 hw2
  have hlogI : Real.log (cellIq C.v C.w C.lam C.P : ℝ) ≤ Real.log (C.ub : ℝ) :=
    Real.log_le_log hIpos (by exact_mod_cast hub)
  have hub0 : (0 : ℝ) < C.ub := lt_of_lt_of_le hIpos (by exact_mod_cast hub)
  have hEx0 : (0 : ℝ) < rsEx C.lu := by
    have : (0 : ℚ) < rsEx C.lu := by
      unfold rsEx
      have : ((1 : ℚ) / 2) ^ (C.lu + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      apply div_pos (by linarith) (by positivity)
    exact_mod_cast this
  have hcr := crLog_le (q := 2 * C.ub * rsEx C.lu) (r := C.r) C.k C.n (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hq, hx⟩, hhi⟩)
  have hsplit : Real.log (((2 * C.ub * rsEx C.lu : ℚ)) : ℝ) =
      Real.log 2 + Real.log (C.ub : ℝ) + Real.log (rsEx C.lu : ℝ) := by
    push_cast
    rw [Real.log_mul (by positivity) hEx0.ne', Real.log_mul (by norm_num) hub0.ne']
  have ht : (0 : ℝ) ≤ (C.P : ℝ) / 4 + C.lu := by positivity
  have hx0 := cr_x0_bounds.2
  have hr : ((C.r : ℚ) : ℝ) + ((C.P : ℝ) / 4 + C.lu) * (crX0hi : ℝ) ≤ -(rsR0 : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 hrate; push_cast at this; exact this
  nlinarith [mul_le_mul_of_nonneg_left hx0 ht]

/-- **Monotonicity of a cause cell event** in the cell: a smaller `m_lo` and a larger (or inactive) cap. -/
lemma cellEvX_mono (hN : 0 < N) (s r0 : State N) (x : Fin N) {c c' : ℚ × ℚ} (h1 : (c'.1 : ℝ) ≤ c.1)
    (h2 : (c.2 : ℝ) ≤ c'.2 ∨ (c'.2 : ℝ) = 1) (hc : (0 : ℝ) < c.2) (hc' : (0 : ℝ) < c'.2) :
    {w : Param N | CellEvX N s r0 x .cause c w} ⊆ {w | CellEvX N s r0 x .cause c' w} := by
  rintro w ⟨hm, ⟨j, hj⟩, hT, hL, hV, hF⟩
  refine ⟨fun i => h1.trans (hm i), ?_, hT, hL, le_trans (sum_le_sum fun i _ => ?_) hV, hF⟩
  · rcases h2 with h | h
    · exact ⟨j, hj.trans h⟩
    · exact ⟨j, by rw [h]; exact clamp01_le_one _⟩
  · refine min_le_min le_rfl (sub_le_sub_right ?_ _)
    show max 0 (Real.log (clamp01 (w r0 i) / (c'.2 : ℝ))) ≤ max 0 (Real.log (clamp01 (w r0 i) / (c.2 : ℝ)))
    rcases (clamp01_nonneg (w r0 i)).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    rcases h2 with h | h
    · exact max_le_max le_rfl
        (Real.log_le_log (div_pos hpos hc') (div_le_div_of_nonneg_left hpos.le hc h))
    · rw [h, div_one, max_eq_left (Real.log_nonpos hpos.le (clamp01_le_one _))]
      exact le_max_left _ _

/-- **One original cause cell, explicit exponential bound.** -/
theorem causeCell_prob (hN : 0 < N) (s r0 : State N) (x : Fin N) {c : ℚ × ℚ}
    (hc : c ∈ cellsXCauseData) (hr0s : r0 ≠ s) (hr1s : flipAt x r0 ≠ s) :
    cubeM N {w : Param N | CellEvX N s r0 x .cause c w} ≤
      ENNReal.ofReal (Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (14 * slT N + 17 * (8 + slV N)) / 2 ^ N) := by
  -- the certified partner cell
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
  set c' : ℚ × ℚ := (C.v ^ 4, C.w ^ 4) with hc'
  have hw0 : (0 : ℚ) < C.w := lt_of_lt_of_le hv hvw
  -- monotonicity: c's event inside c''s
  have hmono := cellEvX_mono hN s r0 x (c := c) (c' := c') (by simp only [hc']; exact_mod_cast hv4)
    (by
      rcases hcap with h | h
      · left; simp only [hc']; exact_mod_cast h
      · right; simp only [hc', h]; norm_num)
    (by exact_mod_cast hc2) (by simp only [hc']; push_cast; positivity)
  refine (measure_mono hmono).trans ?_
  -- the explicit template bound for c'
  have ht : (C.lu : ℝ) ≤ (C.P : ℝ) / 4 + C.lu := by
    have : (0 : ℝ) ≤ (C.P : ℝ) / 4 := by positivity
    linarith
  have hcm' : (1 : ℝ) / 2 ≤ (c'.2 : ℝ) := by
    simp only [hc']; have := (Rat.cast_le (K := ℝ)).2 hw2; push_cast at this ⊢; exact this
  have hm0' : (0 : ℝ) < (c'.1 : ℝ) := by simp only [hc']; push_cast; positivity
  have hm1' : (c'.1 : ℝ) ≤ 1 := by
    simp only [hc']; push_cast
    exact pow_le_one₀ (by exact_mod_cast hv.le) (by exact_mod_cast hv1.le)
  refine (cellEvX_prob_explicit hN s r0 x c' hcm' hm0' hm1' hr0s hr1s C.lam C.lu ht).trans ?_
  -- the rate: the certified log-inequality via `rate_of_log_le`
  have hsound := rsCell_sound C hok
  set I := ∫ y in ((C.v : ℝ) ^ 4)..1, y ^ ((C.P : ℝ) / 4) * gX C.lam ((C.w : ℝ) ^ 4) y with hIdef
  have hI' : (∫ y in (c'.1 : ℝ)..1, y ^ ((C.P : ℝ) / 4 + C.lu - C.lu) * gX C.lam (c'.2 : ℝ) y) = I := by
    simp only [hc', add_sub_cancel_right]; push_cast; rfl
  rw [hI']
  have hIpos : 0 < I := cellI_pos C hv hvw hv1 hw2
  have hEx : (2 * (1 - (1 / 2 : ℝ) ^ (C.lu + 1)) / (C.lu + 1)) = (rsEx C.lu : ℝ) := by
    unfold rsEx; push_cast; ring
  rw [hEx]
  have hEx0 : (0 : ℝ) < rsEx C.lu := by
    have : (0 : ℚ) < rsEx C.lu := by
      unfold rsEx
      have : ((1 : ℚ) / 2) ^ (C.lu + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      apply div_pos (by linarith) (by positivity)
    exact_mod_cast this
  have hrate := rate_of_log_le hIpos hEx0 hsound N
  set t : ℝ := (C.P : ℝ) / 4 + C.lu with htdef
  set K : ℝ := 7 * deltaU N + (slV N + Real.log 2) / N with hK
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  -- split the bound
  have hsplitB : Real.exp (t * (x0 * N + slT N)) *
      ((Real.exp ((C.lam : ℝ) * K) * I) * (Real.exp ((C.lu : ℝ) * (slT N / N)) * (rsEx C.lu : ℝ))) ^ N =
      ((2 : ℝ) ^ N * (Real.exp (t * (x0 * N)) * (I * (rsEx C.lu : ℝ)) ^ N)) *
        Real.exp (t * slT N + (C.lam : ℝ) * (K * N) + (C.lu : ℝ) * slT N) / 2 ^ N := by
    have e1 : (Real.exp ((C.lam : ℝ) * K)) ^ N = Real.exp ((C.lam : ℝ) * (K * N)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have e2 : (Real.exp ((C.lu : ℝ) * (slT N / N))) ^ N = Real.exp ((C.lu : ℝ) * slT N) := by
      rw [← Real.exp_nat_mul]; congr 1; field_simp
    rw [mul_pow, mul_pow, mul_pow, e1, e2, mul_add t, Real.exp_add, Real.exp_add, Real.exp_add]
    field_simp
    ring
  rw [hsplitB]
  -- the lower-order exponent
  have hslT : 0 ≤ slT N := by
    unfold slT
    have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    linarith
  have hslV : 0 ≤ slV N := by unfold slV; positivity
  have hδN : deltaU N * N ≤ 1 := by
    unfold deltaU; rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  have hKN : K * N ≤ 7 + slV N + 1 := by
    simp only [hK, add_mul, div_mul_cancel₀ _ hNr.ne']
    have := Real.log_two_lt_d9
    nlinarith
  have hlamR : (C.lam : ℝ) ≤ 17 := by exact_mod_cast hlam
  have hluR : (C.lu : ℝ) ≤ 3 := by exact_mod_cast hlu
  have htR : t ≤ 11 := by
    have : (C.P : ℝ) ≤ 30 := by exact_mod_cast hP
    simp only [htdef]; linarith
  have hKN0 : 0 ≤ K * N := by
    simp only [hK]; unfold deltaU; have := Real.log_pos one_lt_two; positivity
  have hE : t * slT N + (C.lam : ℝ) * (K * N) + (C.lu : ℝ) * slT N ≤ 14 * slT N + 17 * (8 + slV N) := by
    have ht0 : 0 ≤ t := by simp only [htdef]; positivity
    have hl0 : (0 : ℝ) ≤ C.lam := Nat.cast_nonneg _
    have hu0 : (0 : ℝ) ≤ C.lu := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right htR hslT, mul_le_mul_of_nonneg_right hluR hslT,
      mul_le_mul hlamR hKN hKN0 (by norm_num : (0 : ℝ) ≤ 17)]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff_of_pos_right h2N]
  exact mul_le_mul hrate (Real.exp_le_exp.2 hE) (Real.exp_pos _).le (Real.exp_pos _).le

/-- **The cause regime event at `(r0, x)`**: a union of at most 61 certified cells. -/
theorem regEvX_cause_prob (hN : 0 < N) (s r0 : State N) (x : Fin N) (hr0s : r0 ≠ s)
    (hr1s : flipAt x r0 ≠ s) :
    cubeM N {w : Param N | RegEvX N s r0 x .cause w} ≤
      ENNReal.ofReal (61 * (Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (14 * slT N + 17 * (8 + slV N)) /
        2 ^ N)) := by
  set B := Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (14 * slT N + 17 * (8 + slV N)) / 2 ^ N
  have hB : 0 ≤ B := by positivity
  have hset : {w : Param N | RegEvX N s r0 x .cause w} =
      ⋃ c ∈ cellsXCauseData.toFinset, {w : Param N | CellEvX N s r0 x .cause c w} := by
    ext w; simp [RegEvX, cellsX]
  rw [hset]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ c ∈ cellsXCauseData.toFinset, cubeM N {w : Param N | CellEvX N s r0 x .cause c w}
      ≤ ∑ _c ∈ cellsXCauseData.toFinset, ENNReal.ofReal B :=
        sum_le_sum fun c hc => causeCell_prob hN s r0 x (List.mem_toFinset.1 hc) hr0s hr1s
    _ = (cellsXCauseData.toFinset.card : ENNReal) * ENNReal.ofReal B := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (61 : ENNReal) * ENNReal.ofReal B := by
        gcongr
        have : cellsXCauseData.toFinset.card ≤ cellsXCauseData.length := List.toFinset_card_le _
        have hlen : cellsXCauseData.length = 61 := by decide
        exact_mod_cast hlen ▸ this
    _ = ENNReal.ofReal (61 * B) := by
        rw [ENNReal.ofReal_mul (by norm_num)]; norm_num

end Census
end IIT
