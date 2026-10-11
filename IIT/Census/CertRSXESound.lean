/-
Census, Lemma RS effect side: the explicit row-`tc` factor and the per-cell bound.

With the floor `a = 1/2 - δ` (`δ = deltaU N`) and the multiplier `μ = log (N+1)` (so `e^{-μ} = δ`), the row-`tc`
factor is `≤ ∫_{1/2}^1 y^p + 2δ`; over `N` units the `2δ` costs only a constant factor.
-/
import IIT.Census.B1RegRSEff
import IIT.Census.CertRSXSound
import IIT.Census.CertRSXE

namespace IIT
namespace Census

open MeasureTheory

variable {N : ℕ}

/-- **The row-`tc` factor, explicit**: `≤ (1 - 2^{-(p+1)})/(p+1) + 2δ`. -/
theorem tcJ_le (p : ℕ) {t lu : ℝ} (htp : t - lu = p) (hδ : deltaU N < 1 / 2) :
    ∫⁻ y, ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 y) -
        Real.log (N + 1) * Set.indicator (Set.Iio (1 / 2 - deltaU N)) 1 y)) ∂unif ≤
      ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ (p + 1)) / (p + 1) + 2 * deltaU N) := by
  have hδ0 : 0 < deltaU N := by unfold deltaU; positivity
  have ha0 : 0 < 1 / 2 - deltaU N := by linarith
  refine (tc_factor_le (by linarith [show (0 : ℝ) ≤ p from Nat.cast_nonneg p]) ha0 (by linarith)
    (Real.log (N + 1))).trans ?_
  rw [htp]
  simp only [Real.rpow_natCast]
  have hmu : Real.exp (-Real.log (N + 1)) = deltaU N := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]; unfold deltaU; rw [one_div]
  rw [hmu, ← ENNReal.ofReal_add (by
      have : 0 ≤ ∫ y in (0 : ℝ)..1 / 2 - deltaU N, y ^ p :=
        intervalIntegral.integral_nonneg ha0.le fun y hy => pow_nonneg hy.1 _
      positivity) (intervalIntegral.integral_nonneg (by linarith) fun y hy => pow_nonneg (by linarith [hy.1]) _)]
  apply ENNReal.ofReal_le_ofReal
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun y : ℝ => y ^ p) volume u v :=
    fun u v => (continuous_pow p).intervalIntegrable u v
  -- e^{-μ} ∫_0^a y^p ≤ δ
  have h1 : ∫ y in (0 : ℝ)..1 / 2 - deltaU N, y ^ p ≤ 1 := by
    calc ∫ y in (0 : ℝ)..1 / 2 - deltaU N, y ^ p ≤ ∫ _y in (0 : ℝ)..1 / 2 - deltaU N, (1 : ℝ) :=
          intervalIntegral.integral_mono_on ha0.le (hint _ _) intervalIntegrable_const fun y hy =>
            pow_le_one₀ hy.1 (by linarith [hy.2])
      _ ≤ 1 := by rw [intervalIntegral.integral_const, smul_eq_mul]; linarith
  -- ∫_a^1 = ∫_a^{1/2} + ∫_{1/2}^1, the first ≤ δ
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint _ (1 / 2)) (hint (1 / 2) 1)]
  have h2 : ∫ y in (1 / 2 - deltaU N)..1 / 2, y ^ p ≤ deltaU N := by
    calc ∫ y in (1 / 2 - deltaU N)..1 / 2, y ^ p ≤ ∫ _y in (1 / 2 - deltaU N)..1 / 2, (1 : ℝ) :=
          intervalIntegral.integral_mono_on (by linarith) (hint _ _) intervalIntegrable_const fun y hy =>
            pow_le_one₀ (by linarith [hy.1]) (by linarith [hy.2])
      _ = deltaU N := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have h3 : ∫ y in (1 / 2 : ℝ)..1, y ^ p = (1 - (1 / 2 : ℝ) ^ (p + 1)) / (p + 1) := by
    rw [integral_pow]; push_cast; ring
  rw [h3]
  nlinarith [mul_le_mul_of_nonneg_left h1 hδ0.le]

/-- Effect cells are monotone in the cap (or the cap becomes inactive, `c'.2 = 1`). -/
lemma cellEvX_mono_eff (s r0 : State N) (x : Fin N) {c c' : ℚ × ℚ} (h1 : (c'.1 : ℝ) = c.1)
    (h2 : (c.2 : ℝ) ≤ c'.2 ∨ (c'.2 : ℝ) = 1) (hc : (0 : ℝ) < c.2) (hc' : (0 : ℝ) < c'.2) :
    {w : Param N | CellEvX N s r0 x .effect c w} ⊆ {w | CellEvX N s r0 x .effect c' w} := by
  rintro w ⟨hm, ⟨j, hj⟩, hT, hL, hV, hF⟩
  refine ⟨fun i => h1 ▸ hm i, ?_, hT, hL, le_trans (Finset.sum_le_sum fun i _ => ?_) hV, hF⟩
  · rcases h2 with h | h
    · exact ⟨j, hj.trans h⟩
    · exact ⟨j, by rw [h]; exact xE_le_one w s j⟩
  refine min_le_min le_rfl (sub_le_sub_right ?_ _)
  show max 0 (Real.log (xE w s i / (c'.2 : ℝ))) ≤ max 0 (Real.log (xE w s i / (c.2 : ℝ)))
  have hpos := xE_pos w s i
  rcases h2 with h | h
  · exact max_le_max le_rfl (Real.log_le_log (div_pos hpos hc') (div_le_div_of_nonneg_left hpos.le hc h))
  · rw [h, div_one, max_eq_left (Real.log_nonpos hpos.le (xE_le_one w s i))]
    exact le_max_left _ _

/-- **One original effect cell, explicit exponential bound.** -/
theorem effectCell_prob (hN : 0 < N) (s r0 : State N) (x : Fin N) {c : ℚ × ℚ}
    (hc : c ∈ cellsXEffectData) (hδ : deltaU N < 1 / 2) (hsr : s ≠ r0) (hfr : flipAt x s ≠ r0) :
    cubeM N {w : Param N | CellEvX N s r0 x .effect c w} ≤
      ENNReal.ofReal (Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N) := by
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
  refine (measure_mono hmono).trans ?_
  have hδ0 : 0 < deltaU N := by unfold deltaU; positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcm' : (1 : ℝ) / 2 ≤ (c'.2 : ℝ) := by simp only [hc']; push_cast; exact hw4
  set lu : ℝ := (C.P : ℝ) / 4 with hludef
  set t : ℝ := lu + C.lu with htdef
  set K : ℝ := 7 * deltaU N + (slV N + Real.log 2) / N with hK
  set I := ∫ y in ((C.v : ℝ) ^ 4)..1, y ^ ((C.P : ℝ) / 4) * gX C.lam ((C.w : ℝ) ^ 4) y with hIdef
  set H : ℝ := (1 - (1 / 2 : ℝ) ^ (C.lu + 1)) / (C.lu + 1) with hH
  have hv' : (0 : ℝ) < C.v := by exact_mod_cast hv
  have hv0 : (0 : ℝ) < (C.v : ℝ) ^ 4 := by positivity
  have hb : (C.v : ℝ) ^ 4 ≤ max (1 / 2) (c'.1 : ℝ) := by
    simp only [hc']; have := (Rat.cast_le (K := ℝ)).2 hv4; push_cast at this; exact this
  have hb1 : (C.v : ℝ) ^ 4 ≤ 1 := pow_le_one₀ hv'.le (by exact_mod_cast hv1.le)
  have hIpos : 0 < I := cellI_pos C hv hvw hv1 hw2
  have hH15 : (15 : ℝ) / 64 ≤ H := by
    have key : ∀ n : ℕ, n ≤ 3 → (15 : ℝ) / 64 ≤ (1 - (1 / 2 : ℝ) ^ (n + 1)) / (n + 1) := by
      intro n hn; interval_cases n <;> norm_num
    exact key C.lu hlu
  have hH0 : 0 < H := lt_of_lt_of_le (by norm_num) hH15
  have hlu0 : 0 ≤ lu := by positivity
  have hJs := s_factor_le (N := N) C.lam c' hcm' hlu0 hv0 hb hb1
  have hI' : (∫ X in ((C.v : ℝ) ^ 4)..1, X ^ lu * gX C.lam (c'.2 : ℝ) X) = I := by
    simp only [hc', hludef]; push_cast; rfl
  rw [hI'] at hJs
  have hJt := tcJ_le (N := N) C.lu (t := t) (lu := lu) (by simp only [htdef]; ring) hδ
  set C1 : ℝ := Real.exp (lu * (slT N / N)) * Real.exp ((C.lam : ℝ) * K) with hC1
  have hlog1 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  refine (cellEvX_eff_prob hN s r0 x c' hcm' hδ hsr hfr t lu C.lam (Real.log (N + 1))
    (by positivity) hlu0 (Nat.cast_nonneg _) hlog1 (Js := C1 * (2 * I)) (Jt := H + 2 * deltaU N)
    (by positivity) (by positivity) hJs hJt).trans ?_
  -- the rate
  have hEx : (rsEx C.lu : ℝ) = 2 * H := by unfold rsEx; push_cast; simp only [hH]; ring
  have hsound := rsCell_sound C hok
  have hEx0 : (0 : ℝ) < rsEx C.lu := by rw [hEx]; positivity
  have hrate := rate_of_log_le hIpos hEx0 hsound N
  have hfac : C1 * (2 * I) * (H + 2 * deltaU N) = C1 * (I * (rsEx C.lu : ℝ)) * (1 + 2 * deltaU N / H) := by
    rw [hEx]; field_simp
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have e1 : C1 ^ N = Real.exp (lu * slT N + (C.lam : ℝ) * (K * N)) := by
    simp only [hC1]
    rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; field_simp
  have hsplitB : Real.exp (t * (x0 * N + slT N)) * (C1 * (2 * I) * (H + 2 * deltaU N)) ^ N =
      ((2 : ℝ) ^ N * (Real.exp (t * (x0 * N)) * (I * (rsEx C.lu : ℝ)) ^ N)) *
        (Real.exp (t * slT N + (lu * slT N + (C.lam : ℝ) * (K * N))) * (1 + 2 * deltaU N / H) ^ N) / 2 ^ N := by
    rw [hfac, mul_pow, mul_pow, e1, mul_add t, Real.exp_add, Real.exp_add]
    field_simp
    rw [Real.exp_add, Real.exp_add]
    ring
  rw [hsplitB]
  -- the correction factor `(1 + 2δ/H)^N ≤ e^9`
  have hδN : deltaU N * N ≤ 1 := by
    unfold deltaU; rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  have hcorr : (1 + 2 * deltaU N / H) ^ N ≤ Real.exp 9 := by
    calc (1 + 2 * deltaU N / H) ^ N ≤ (Real.exp (2 * deltaU N / H)) ^ N := by
          gcongr
          linarith [Real.add_one_le_exp (2 * deltaU N / H)]
      _ = Real.exp (2 * (deltaU N * N) / H) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ Real.exp 9 := by
          apply Real.exp_le_exp.2
          rw [div_le_iff₀ hH0]; nlinarith
  -- the lower-order exponent
  have hslT : 0 ≤ slT N := by
    unfold slT
    have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    linarith
  have hslV : 0 ≤ slV N := by unfold slV; positivity
  have hKN : K * N ≤ 7 + slV N + 1 := by
    simp only [hK, add_mul, div_mul_cancel₀ _ hNr.ne']
    have := Real.log_two_lt_d9
    nlinarith
  have hKN0 : 0 ≤ K * N := by
    simp only [hK]; unfold deltaU; have := Real.log_pos one_lt_two; positivity
  have hlamR : (C.lam : ℝ) ≤ 17 := by exact_mod_cast hlam
  have hluR : lu ≤ 8 := by
    have : (C.P : ℝ) ≤ 30 := by exact_mod_cast hP
    simp only [hludef]; linarith
  have htR : t ≤ 11 := by
    have : (C.lu : ℝ) ≤ 3 := by exact_mod_cast hlu
    simp only [htdef]; linarith
  have hE : t * slT N + (lu * slT N + (C.lam : ℝ) * (K * N)) ≤ 19 * slT N + 17 * (8 + slV N) := by
    have hl0 : (0 : ℝ) ≤ C.lam := Nat.cast_nonneg _
    have a1 := mul_le_mul_of_nonneg_right htR hslT
    have a2 := mul_le_mul_of_nonneg_right hluR hslT
    have a3 := mul_le_mul hlamR hKN hKN0 (by norm_num : (0 : ℝ) ≤ 17)
    linarith
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff_of_pos_right h2N, Real.exp_add (19 * slT N + 17 * (8 + slV N)) 9]
  refine mul_le_mul hrate (mul_le_mul (Real.exp_le_exp.2 hE) hcorr (by positivity) (Real.exp_pos _).le)
    (by positivity) (Real.exp_pos _).le

/-- **The effect regime event at `(s, r0, x)`**: a union of at most 61 certified cells. -/
theorem regEvX_effect_prob (hN : 0 < N) (s r0 : State N) (x : Fin N) (hδ : deltaU N < 1 / 2)
    (hsr : s ≠ r0) (hfr : flipAt x s ≠ r0) :
    cubeM N {w : Param N | RegEvX N s r0 x .effect w} ≤
      ENNReal.ofReal (61 * (Real.exp (-((rsR0 : ℝ) * N)) *
        Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N)) := by
  set B := Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N
  have hB : 0 ≤ B := by positivity
  have hset : {w : Param N | RegEvX N s r0 x .effect w} =
      ⋃ c ∈ cellsXEffectData.toFinset, {w : Param N | CellEvX N s r0 x .effect c w} := by
    ext w; simp [RegEvX, cellsX]
  rw [hset]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ c ∈ cellsXEffectData.toFinset, cubeM N {w : Param N | CellEvX N s r0 x .effect c w}
      ≤ ∑ _c ∈ cellsXEffectData.toFinset, ENNReal.ofReal B :=
        Finset.sum_le_sum fun c hc => effectCell_prob hN s r0 x (List.mem_toFinset.1 hc) hδ hsr hfr
    _ = (cellsXEffectData.toFinset.card : ENNReal) * ENNReal.ofReal B := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (61 : ENNReal) * ENNReal.ofReal B := by
        gcongr
        have : cellsXEffectData.toFinset.card ≤ cellsXEffectData.length := List.toFinset_card_le _
        have hlen : cellsXEffectData.length = 61 := by decide
        exact_mod_cast hlen ▸ this
    _ = ENNReal.ofReal (61 * B) := by
        rw [ENNReal.ofReal_mul (by norm_num)]; norm_num

end Census
end IIT
