/-
Census, B1 forced joint bound `sRowR` (`JointBound P0SRowR`), all rows but the effect-side `s^x`.

Orientation averaging (no certificate): reflecting `y ↦ 1 - y` the rows `Q ∋ s` on a column set `F` preserves
`cubeM` and the regime event (`dr_regEvX_refl`; on the cause side `Q = {s}` suffices), and for a row `r ∉ Q` it
maps `pTe(s, r, k)` to `1 - pTe(s, r, k)` exactly on `F`.  Summing over the `2^N` sets `F`,
`Σ_F ∏_k pTe(refl_F w) = ∏_k (pTe + (1 - pTe)) = 1`, so `∫_E ∏_k pTe(s, r, ·) = cubeM E / 2^N` (`sr_avg`), and Markov
gives a gain `2^{-N} / σ_N = (3/8)^{N/2} ≤ e^{-N/4}` over the regime rate.

The one row left is `s^x` on the effect side (there `∏_k pTe(s, s^x, k)` is the competitor product, invariant
under the joint reflection): the hypothesis `SxEffStmt`.
-/
import IIT.Census.B1ForcedDRet
import IIT.Census.B1ForcedFJoint

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-! ### 1. Reflection of `pTe` -/

lemma sr_pTe_refl {Q : Finset (State N)} {s r : State N} (hs : s ∈ Q) (hr : r ∉ Q) (F : Finset (Fin N))
    {w : Param N} (hw : w ∈ drH Q) (k : Fin N) :
    pTe (drRefl Q F w) s r k = if k ∈ F then 1 - pTe w s r k else pTe w s r k := by
  have er : drRefl Q F w r = w r := dr_row_refl hr F w
  unfold pTe
  rw [er]
  by_cases hk : k ∈ F
  · have es : drRefl Q F w s k = 1 - w s k := by unfold drRefl; rw [if_pos ⟨hs, hk⟩]
    rw [es, dr_clamp_refl, if_pos hk]
    have h := hw s hs k
    rcases lt_or_gt_of_ne h with h2 | h2
    · rw [if_pos (by linarith), if_neg (by linarith)]; ring
    · rw [if_neg (by linarith), if_pos h2]
  · have es : drRefl Q F w s k = w s k := by unfold drRefl; rw [if_neg (fun h => hk h.2)]
    rw [es, if_neg hk]

lemma sr_sum_refl {Q : Finset (State N)} {s r : State N} (hs : s ∈ Q) (hr : r ∉ Q) {w : Param N}
    (hw : w ∈ drH Q) : ∑ F : Finset (Fin N), ∏ k, pTe (drRefl Q F w) s r k = 1 := by
  have e : ∀ F : Finset (Fin N), ∏ k, pTe (drRefl Q F w) s r k =
      (∏ k ∈ F, (1 - pTe w s r k)) * ∏ k ∈ univ \ F, pTe w s r k := by
    intro F
    rw [Finset.prod_congr rfl fun k _ => sr_pTe_refl hs hr F hw k, Finset.prod_ite]
    congr 2
    · ext k; simp
    · ext k; simp
  simp_rw [e]
  have h := Finset.prod_add (fun k => 1 - pTe w s r k) (fun k => pTe w s r k) (univ : Finset (Fin N))
  rw [Finset.powerset_univ] at h
  rw [← h]
  simp

lemma sr_pTe_nonneg (w : Param N) (s r : State N) (k : Fin N) : 0 ≤ pTe w s r k := by
  unfold pTe
  split_ifs
  · exact clamp01_nonneg _
  · linarith [clamp01_le_one (w r k)]

/-! ### 2. The averaging identity -/

theorem sr_avg (Q : Finset (State N)) (E : Set (Param N)) (hE : MeasurableSet E)
    (hEinv : ∀ F w, w ∈ drH Q → (drRefl Q F w ∈ E ↔ w ∈ E))
    (G : Param N → ENNReal) (hG : Measurable G)
    (hsum : ∀ w ∈ drH Q, ∑ F : Finset (Fin N), G (drRefl Q F w) = 1) :
    (2 : ENNReal) ^ N * ∫⁻ w in E, G w ∂cubeM N = cubeM N E := by
  have hae : ∀ᵐ w ∂cubeM N, w ∈ drH Q := by
    rw [ae_iff]
    exact dr_H_null Q
  have hF : ∀ F : Finset (Fin N), ∫⁻ w in E, G w ∂cubeM N = ∫⁻ w in E, G (drRefl Q F w) ∂cubeM N := by
    intro F
    have hmp := dr_refl_mp (N := N) Q F
    rw [← lintegral_indicator hE, ← lintegral_indicator hE, ← hmp.lintegral_comp (hG.indicator hE)]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with w hw
    by_cases h : w ∈ E
    · rw [Set.indicator_of_mem ((hEinv F w hw).2 h), Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem (fun h' => h ((hEinv F w hw).1 h')), Set.indicator_of_notMem h]
  have hsumint : ∑ F : Finset (Fin N), ∫⁻ w in E, G (drRefl Q F w) ∂cubeM N = cubeM N E := by
    rw [← lintegral_finset_sum (f := fun F w => G (drRefl Q F w)) _
      (fun F _ => hG.comp (dr_refl_mp Q F).measurable)]
    rw [← setLIntegral_one]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hae] with w hw
    exact hsum w hw
  rw [Finset.sum_congr rfl (fun F _ => (hF F).symm), Finset.sum_const, Finset.card_univ,
    Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul] at hsumint
  rw [← hsumint]
  push_cast
  rfl

/-! ### 3. Markov -/

theorem sr_markov (E : Set (Param N)) (hE : MeasurableSet E) (R : Finset (State N))
    (G : State N → Param N → ℝ) (hG0 : ∀ r w, 0 ≤ G r w) (hGm : ∀ r, Measurable (G r)) {a : ℝ} (ha : 0 < a) :
    cubeM N (E ∩ {w | a < ∑ r ∈ R, G r w}) ≤
      ENNReal.ofReal (1 / a) * ∑ r ∈ R, ∫⁻ w in E, ENNReal.ofReal (G r w) ∂cubeM N := by
  set f : Param N → ENNReal := fun w => ∑ r ∈ R, ENNReal.ofReal (G r w) with hf
  have hfm : Measurable f := Finset.measurable_sum _ fun r _ => ENNReal.measurable_ofReal.comp (hGm r)
  have hsub : E ∩ {w | a < ∑ r ∈ R, G r w} ⊆ {w | ENNReal.ofReal a ≤ f w} ∩ E := by
    rintro w ⟨hw, hlt⟩
    refine ⟨?_, hw⟩
    simp only [Set.mem_setOf_eq, hf]
    rw [← ENNReal.ofReal_sum_of_nonneg fun r _ => hG0 r w]
    exact ENNReal.ofReal_le_ofReal hlt.le
  have hmk := mul_meas_ge_le_lintegral₀ (μ := (cubeM N).restrict E) hfm.aemeasurable (ENNReal.ofReal a)
  rw [Measure.restrict_apply' hE] at hmk
  have hint : ∫⁻ w in E, f w ∂cubeM N = ∑ r ∈ R, ∫⁻ w in E, ENNReal.ofReal (G r w) ∂cubeM N :=
    lintegral_finset_sum _ fun r _ => ENNReal.measurable_ofReal.comp (hGm r)
  rw [hint] at hmk
  have h1 : ENNReal.ofReal (1 / a) * ENNReal.ofReal a = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ ha.ne', ENNReal.ofReal_one]
  calc cubeM N (E ∩ {w | a < ∑ r ∈ R, G r w}) ≤ cubeM N ({w | ENNReal.ofReal a ≤ f w} ∩ E) := measure_mono hsub
    _ = ENNReal.ofReal (1 / a) * (ENNReal.ofReal a * cubeM N ({w | ENNReal.ofReal a ≤ f w} ∩ E)) := by
        rw [← mul_assoc, h1, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmk zero_le

/-! ### 4. One row against the regime event -/

lemma sr_cause_refl {s r0 : State N} {x : Fin N} (h0 : r0 ≠ s) (h1 : flipAt x r0 ≠ s) (F : Finset (Fin N))
    (w : Param N) : RegEvX N s r0 x .cause (drRefl {s} F w) ↔ RegEvX N s r0 x .cause w := by
  have e0 := dr_row_refl (Q := {s}) (by simpa using h0) F w
  have e1 := dr_row_refl (Q := {s}) (by simpa using h1) F w
  have hx : ∀ k, xE (drRefl {s} F w) s k = xE w s k := dr_xE_refl F w
  have hX : XW (drRefl {s} F w) r0 = XW w r0 := by unfold XW; rw [e0]
  simp only [RegEvX, CellEvX, lamX, baseE, compE, e0, e1, hX, hx]

/-- **The averaged row product**: for `Q ∋ s` keeping the regime event and `r ∉ Q`. -/
theorem sr_row_int {s r0 : State N} {x : Fin N} {σ : XSide} {Q : Finset (State N)} (hs : s ∈ Q)
    (hinv : ∀ F w, w ∈ drH Q → (RegEvX N s r0 x σ (drRefl Q F w) ↔ RegEvX N s r0 x σ w))
    {r : State N} (hr : r ∉ Q) :
    ∫⁻ w in {w | RegEvX N s r0 x σ w}, ENNReal.ofReal (∏ k, pTe w s r k) ∂cubeM N =
      cubeM N {w | RegEvX N s r0 x σ w} / 2 ^ N := by
  have hm : Measurable fun w : Param N => ENNReal.ofReal (∏ k, pTe w s r k) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun k _ => b1mx_pTe s r k)
  have h := sr_avg Q _ (b1mx_RegEvX N s r0 x σ) (fun F w hw => hinv F w hw) _ hm (fun w hw => by
    have hnn : ∀ F : Finset (Fin N), 0 ≤ ∏ k, pTe (drRefl Q F w) s r k := fun F =>
      Finset.prod_nonneg fun k _ => sr_pTe_nonneg _ s r k
    rw [← ENNReal.ofReal_sum_of_nonneg fun F _ => hnn F, sr_sum_refl hs hr hw, ENNReal.ofReal_one])
  exact (ENNReal.eq_div_iff (by simp) (by simp)).2 h

/-! ### 5. Numbers -/

/-- `2^{-N} / σ_N = (3/8)^{N/2} ≤ e^{-N/4}`. -/
lemma sr_gain (N : ℕ) : (1 / 2 : ℝ) ^ N ≤ Real.exp (-(N : ℝ) / 4) * sigN N := by
  have he : Real.exp (1 / 2) ≤ 8 / 3 := by
    have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 := Real.exp_one_lt_d9
    nlinarith [Real.exp_pos (1 / 2)]
  have hq : (3 / 8 : ℝ) ≤ Real.exp (-(1 / 2)) := by
    rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]; linarith
  unfold sigN
  have hL : (1 / 2 : ℝ) ^ N = Real.sqrt ((1 / 4 : ℝ) ^ N) := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul, Real.sqrt_sq (by positivity)]
  have hR : Real.exp (-(N : ℝ) / 4) * Real.sqrt ((2 / 3 : ℝ) ^ N) =
      Real.sqrt (Real.exp (-(1 / 2)) ^ N * (2 / 3 : ℝ) ^ N) := by
    rw [Real.sqrt_mul (by positivity), ← Real.exp_nat_mul]
    congr 1
    rw [← Real.sqrt_sq (Real.exp_pos (-(N : ℝ) / 4)).le, ← Real.exp_nat_mul]
    congr 2; ring
  rw [hL, hR]
  apply Real.sqrt_le_sqrt
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by norm_num)
  nlinarith

lemma sr_absorb : ∀ᶠ N : ℕ in atTop, 2 * (3 * ((N : ℝ) + 1) ^ 4) * (61 * (Real.exp (-((rsR0 : ℝ) * N)) *
    Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N)) * Real.exp (-(N : ℝ) / 4) ≤
      Real.exp (-((10109 / 10000 : ℝ) * N)) / 2 ^ N := by
  set R : ℝ := 10109 / 10000 with hR
  have hab := poly_absorb (2 * 3 * 61) 4 (δ := (rsR0 : ℝ) + 1 / 4 - R) (by rw [hR]; unfold rsR0; norm_num)
  filter_upwards [hab] with N hab
  have hsl := rs_slack_le N
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hexp : Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (-(N : ℝ) / 4) =
      Real.exp (-((((rsR0 : ℝ) + 1 / 4 - R)) * N)) * Real.exp (-(R * N)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have e : 2 * (3 * ((N : ℝ) + 1) ^ 4) * (61 * (Real.exp (-((rsR0 : ℝ) * N)) *
      Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N)) * Real.exp (-(N : ℝ) / 4) =
      (2 * 3 * 61 * ((N : ℝ) + 1) ^ 4 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9)) *
        (Real.exp (-((((rsR0 : ℝ) + 1 / 4 - R)) * N)) * Real.exp (-(R * N))) / 2 ^ N := by
    rw [← hexp]; ring
  rw [e, div_le_div_iff_of_pos_right h2N]
  have hk : 2 * 3 * 61 * ((N : ℝ) + 1) ^ 4 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) ≤
      Real.exp ((((rsR0 : ℝ) + 1 / 4 - R)) * N) :=
    le_trans (by gcongr) hab
  have hy : Real.exp ((((rsR0 : ℝ) + 1 / 4 - R)) * N) *
      Real.exp (-((((rsR0 : ℝ) + 1 / 4 - R)) * N)) = 1 := by rw [← Real.exp_add]; simp
  calc (2 * 3 * 61 * ((N : ℝ) + 1) ^ 4 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9)) *
        (Real.exp (-((((rsR0 : ℝ) + 1 / 4 - R)) * N)) * Real.exp (-(R * N)))
      ≤ Real.exp ((((rsR0 : ℝ) + 1 / 4 - R)) * N) *
          (Real.exp (-((((rsR0 : ℝ) + 1 / 4 - R)) * N)) * Real.exp (-(R * N))) := by gcongr
    _ = Real.exp (-(R * N)) := by rw [← mul_assoc, hy, one_mul]

/-- `cubeM E / 2^N` from a real bound. -/
lemma sr_div_le {m : ENNReal} {B : ℝ} (hm : m ≤ ENNReal.ofReal B) (hB : 0 ≤ B) :
    m / 2 ^ N ≤ ENNReal.ofReal (B / 2 ^ N) := by
  rw [ENNReal.div_le_iff (by simp) (by simp)]
  have e : (2 : ENNReal) ^ N = ENNReal.ofReal (2 ^ N) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  rw [e, ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ (by positivity)]
  exact hm

/-! ### 6. The joint bound -/

/-- **The one remaining row**: `s^x` on the effect side. -/
def SxEffStmt : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    cubeM N {w | RegEvX N s r0 x .effect w ∧ sigN N / 2 < ∏ k, pTe w s (flipAt x s) k} ≤
      ENNReal.ofReal (Real.exp (-((10109 / 10000 : ℝ) * N)) / 2 ^ N)

/-- One Markov step against the regime event, for a set of rows outside a reflection set `Q ∋ s`. -/
lemma sr_rows_le {s r0 : State N} {x : Fin N} {σ : XSide} {Q : Finset (State N)} (hs : s ∈ Q)
    (hinv : ∀ F w, w ∈ drH Q → (RegEvX N s r0 x σ (drRefl Q F w) ↔ RegEvX N s r0 x σ w))
    (R : Finset (State N)) (hR : ∀ r ∈ R, r ∉ Q) {B : ℝ} (hB0 : 0 ≤ B)
    (hE : cubeM N {w | RegEvX N s r0 x σ w} ≤ ENNReal.ofReal B) :
    cubeM N ({w | RegEvX N s r0 x σ w} ∩ {w | sigN N / 2 < ∑ r ∈ R, ∏ k, pTe w s r k}) ≤
      ENNReal.ofReal (2 / sigN N * (R.card * (B / 2 ^ N))) := by
  have hσ : 0 < sigN N := by unfold sigN; positivity
  refine (sr_markov _ (b1mx_RegEvX N s r0 x σ) R (fun r w => ∏ k, pTe w s r k)
    (fun r w => Finset.prod_nonneg fun k _ => sr_pTe_nonneg w s r k)
    (fun r => Finset.measurable_prod _ fun k _ => b1mx_pTe s r k) (by positivity)).trans ?_
  rw [Finset.sum_congr rfl fun r hr => sr_row_int hs hinv (hR r hr), Finset.sum_const, nsmul_eq_mul]
  have hd := sr_div_le (N := N) hE hB0
  calc ENNReal.ofReal (1 / (sigN N / 2)) * (R.card * (cubeM N {w | RegEvX N s r0 x σ w} / 2 ^ N))
      ≤ ENNReal.ofReal (1 / (sigN N / 2)) * (R.card * ENNReal.ofReal (B / 2 ^ N)) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp

/-- **`JointBound P0SRowR` from the effect `s^x` row.** -/
theorem joint_sRowR_of (hSx : SxEffStmt) : JointBound P0SRowR := by
  filter_upwards [hSx, sr_absorb, exp_RJ2_le, eventually_ge_atTop 7] with N hSx hab h3 hN7 s r0 x σ hfar
  obtain ⟨h0s, h0sx, h1s, h1sx⟩ := dr_far_ne hN7 x hfar
  set sx := flipAt x s with hsx
  set F' := (sensRows s r0).erase s with hF'
  set R1 := F'.erase sx with hR1
  set E := {w : Param N | RegEvX N s r0 x σ w} with hEdef
  set B : ℝ := 61 * (Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N)
    with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hEB : cubeM N E ≤ ENNReal.ofReal B := regEvX_far_le hN7 s r0 x σ hfar
  have hσ : 0 < sigN N := by unfold sigN; positivity
  have hG0 : ∀ r w, 0 ≤ ∏ k, pTe w s r k := fun r w => Finset.prod_nonneg fun k _ => sr_pTe_nonneg w s r k
  -- split the sum
  have hsplit : ∀ w, ∑ r ∈ F', ∏ k, pTe w s r k ≤ ∑ r ∈ R1, ∏ k, pTe w s r k + ∏ k, pTe w s sx k := by
    intro w
    by_cases h : sx ∈ F'
    · rw [← add_sum_erase _ _ h]; linarith
    · rw [hR1, Finset.erase_eq_of_notMem h]; linarith [hG0 sx w]
  have hsub : {w | RegEvX N s r0 x σ w ∧ ¬ P0SRowR N s r0 w x σ} ⊆
      (E ∩ {w | sigN N / 2 < ∑ r ∈ R1, ∏ k, pTe w s r k}) ∪
        (E ∩ {w | sigN N / 2 < ∑ r ∈ ({sx} : Finset (State N)), ∏ k, pTe w s r k}) := by
    rintro w ⟨hw, hn⟩
    simp only [P0SRowR, not_le] at hn
    have := hsplit w
    by_cases h : sigN N / 2 < ∑ r ∈ R1, ∏ k, pTe w s r k
    · exact Or.inl ⟨hw, h⟩
    · refine Or.inr ⟨hw, ?_⟩
      simp only [Set.mem_setOf_eq, Finset.sum_singleton]
      linarith
  -- part A: all rows but `s^x`, reflection of `{s, s^x}`
  have hQ : ∀ r ∈ R1, r ∉ ({s, sx} : Finset (State N)) := by
    intro r hr
    simp only [hR1, hF', mem_erase] at hr
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hr.2.1, hr.1⟩
  have hA := sr_rows_le (σ := σ) (Q := {s, sx}) (by simp)
    (fun F w hw => dr_regEvX_refl (by simp) (by simp [hsx]) (by simp [h0s, h0sx]) (by simp [h1s, h1sx]) F hw)
    R1 hQ hB0 hEB
  have hR1c : (R1.card : ℝ) ≤ 2 * ((N : ℝ) + 1) ^ 4 := by
    have h1 : R1.card ≤ (sensRows s r0).card :=
      (card_erase_le).trans card_erase_le
    have h2 := card_sensRows_le s r0
    exact_mod_cast h1.trans h2
  -- the gain: every part is at most `E1`
  set E1 : ℝ := Real.exp (-((10109 / 10000 : ℝ) * N)) / 2 ^ N with hE1
  have hK : ∀ c : ℝ, 0 ≤ c → c ≤ 3 * ((N : ℝ) + 1) ^ 4 → 2 / sigN N * (c * (B / 2 ^ N)) ≤ E1 := by
    intro c hc0 hc
    have hq : (1 / 2 : ℝ) ^ N / sigN N ≤ Real.exp (-(N : ℝ) / 4) := by
      rw [div_le_iff₀ hσ]; exact sr_gain N
    have e : 2 / sigN N * (c * (B / 2 ^ N)) = 2 * c * B * ((1 / 2 : ℝ) ^ N / sigN N) := by
      rw [one_div_pow]; field_simp
    rw [e]
    calc 2 * c * B * ((1 / 2 : ℝ) ^ N / sigN N) ≤ 2 * c * B * Real.exp (-(N : ℝ) / 4) := by gcongr
      _ ≤ 2 * (3 * ((N : ℝ) + 1) ^ 4) * B * Real.exp (-(N : ℝ) / 4) := by gcongr
      _ ≤ E1 := hab
  have hPA : cubeM N (E ∩ {w | sigN N / 2 < ∑ r ∈ R1, ∏ k, pTe w s r k}) ≤ ENNReal.ofReal E1 :=
    hA.trans (ENNReal.ofReal_le_ofReal (hK _ (by positivity) (by linarith)))
  have hPB : cubeM N (E ∩ {w | sigN N / 2 < ∑ r ∈ ({sx} : Finset (State N)), ∏ k, pTe w s r k}) ≤
      ENNReal.ofReal E1 := by
    cases σ with
    | cause =>
      have hB' := sr_rows_le (σ := .cause) (Q := {s}) (by simp) (fun F w _ => sr_cause_refl h0s h1s F w)
        {sx} (by simpa [hsx] using flipAt_ne x s) hB0 hEB
      refine hB'.trans (ENNReal.ofReal_le_ofReal (hK _ (by positivity) ?_))
      simp only [card_singleton, Nat.cast_one]
      have : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) N])
      linarith
    | effect =>
      have e : E ∩ {w | sigN N / 2 < ∑ r ∈ ({sx} : Finset (State N)), ∏ k, pTe w s r k} =
          {w | RegEvX N s r0 x .effect w ∧ sigN N / 2 < ∏ k, pTe w s (flipAt x s) k} := by
        ext w; simp [hEdef, hsx]
      rw [e]; exact hSx s r0 x hfar
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add hPA hPB).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hpos := Real.exp_pos (-((10109 / 10000 : ℝ) * N))
  rw [hE1, ← add_div, div_le_div_iff_of_pos_right h2N]
  linarith

end Census
end IIT

#print axioms IIT.Census.joint_sRowR_of
