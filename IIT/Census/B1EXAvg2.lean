/-
Census, B1 lower bound part (b): exact rectangle integrals for the 2-D checks (S, V, M0, D).

`∫_{[y0,y1]×[u0,u1]} ln(y + u) = G(y1+u1) - G(y1+u0) - G(y0+u1) + G(y0+u0)`, `G(t) = t² ln t / 2 - 3t²/4`.
-/
import IIT.Census.B1EXFactsTL

set_option maxRecDepth 100000

namespace IIT
namespace Census

open MeasureTheory Filter Finset intervalIntegral

/-- `F(t) = t ln t - t` (antiderivative of `ln`). -/
noncomputable def lnF (t : ℝ) : ℝ := t * Real.log t - t
/-- `G(t) = t² ln t / 2 - 3 t² / 4` (antiderivative of `F`). -/
noncomputable def lnG (t : ℝ) : ℝ := t ^ 2 * Real.log t / 2 - 3 * t ^ 2 / 4

lemma hasDerivAt_lnG {t : ℝ} (ht : 0 < t) : HasDerivAt lnG (lnF t) t := by
  have h := (((hasDerivAt_pow 2 t).mul (Real.hasDerivAt_log ht.ne')).div_const 2).sub
    (((hasDerivAt_pow 2 t).const_mul 3).div_const 4)
  have h' : HasDerivAt lnG ((↑2 * t ^ (2 - 1) * Real.log t + t ^ 2 * t⁻¹) / 2 - 3 * (↑2 * t ^ (2 - 1)) / 4) t := by
    unfold lnG; exact h
  refine h'.congr_deriv ?_
  unfold lnF; field_simp; ring

/-- Inner integral: `∫_{u0}^{u1} ln(y + u) du = F(y+u1) - F(y+u0)`. -/
lemma integral_log_add (y u0 u1 : ℝ) :
    ∫ u in u0..u1, Real.log (y + u) = lnF (y + u1) - lnF (y + u0) := by
  rw [intervalIntegral.integral_comp_add_left (fun t => Real.log t) y, integral_log]
  unfold lnF; ring

/-- Outer integral: `∫_{y0}^{y1} F(y + c) dy = G(y1+c) - G(y0+c)` for `y0 + c > 0`, `y0 ≤ y1`. -/
lemma integral_lnF_add {y0 y1 c : ℝ} (hy : y0 ≤ y1) (hc : 0 < y0 + c) :
    ∫ y in y0..y1, lnF (y + c) = lnG (y1 + c) - lnG (y0 + c) := by
  have hpos : ∀ y ∈ Set.uIcc y0 y1, 0 < y + c := fun y hy' => by
    rw [Set.uIcc_of_le hy] at hy'; linarith [hy'.1]
  have hderiv : ∀ y ∈ Set.uIcc y0 y1, HasDerivAt (fun y => lnG (y + c)) (lnF (y + c)) y := fun y hy' =>
    (hasDerivAt_lnG (hpos y hy')).comp_add_const y c
  have hcont : ContinuousOn (fun y => lnF (y + c)) (Set.uIcc y0 y1) := by
    unfold lnF
    refine ContinuousOn.sub (ContinuousOn.mul (continuousOn_id.add continuousOn_const) ?_)
      (continuousOn_id.add continuousOn_const)
    exact (Real.continuousOn_log.comp (continuousOn_id.add continuousOn_const)
      fun y hy' => (hpos y hy').ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]

/-- The rectangle integral of `ln(y + u)`. -/
lemma integral_rect_log_add {y0 y1 u0 u1 : ℝ} (hy : y0 ≤ y1) (hu : u0 ≤ u1) (hpos : 0 < y0 + u0) :
    ∫ y in y0..y1, ∫ u in u0..u1, Real.log (y + u) =
      lnG (y1 + u1) - lnG (y0 + u1) - (lnG (y1 + u0) - lnG (y0 + u0)) := by
  simp_rw [integral_log_add]
  rw [intervalIntegral.integral_sub, integral_lnF_add hy (by linarith), integral_lnF_add hy hpos]
  · exact (by
      unfold lnF
      refine ContinuousOn.intervalIntegrable (ContinuousOn.sub (ContinuousOn.mul (continuousOn_id.add
        continuousOn_const) ?_) (continuousOn_id.add continuousOn_const))
      exact Real.continuousOn_log.comp (continuousOn_id.add continuousOn_const) fun y hy' => by
        rw [Set.uIcc_of_le hy] at hy'; have := hy'.1; intro h; simp at h; linarith)
  · exact (by
      unfold lnF
      refine ContinuousOn.intervalIntegrable (ContinuousOn.sub (ContinuousOn.mul (continuousOn_id.add
        continuousOn_const) ?_) (continuousOn_id.add continuousOn_const))
      exact Real.continuousOn_log.comp (continuousOn_id.add continuousOn_const) fun y hy' => by
        rw [Set.uIcc_of_le hy] at hy'; have := hy'.1; intro h; simp at h; linarith)

/-- `∫_a^b t⁺ = ((b⁺)² - (a⁺)²) / 2`. -/
lemma integral_posPart {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, max t 0 = (max b 0 ^ 2 - max a 0 ^ 2) / 2 := by
  rcases le_total b 0 with hb | hb
  · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => by
      rw [Set.uIcc_of_le hab] at ht; exact max_eq_right (ht.2.trans hb)]
    rw [intervalIntegral.integral_zero, max_eq_right hb, max_eq_right (hab.trans hb)]; ring
  rcases le_total 0 a with ha | ha
  · rw [intervalIntegral.integral_congr (g := fun t => t) fun t ht => by
      rw [Set.uIcc_of_le hab] at ht; exact max_eq_left (ha.trans ht.1)]
    rw [integral_id, max_eq_left hb, max_eq_left ha]
  · have hc : Continuous fun t : ℝ => max t 0 := continuous_id.max continuous_const
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (a := a) (b := 0) fun t ht => by
      rw [Set.uIcc_of_le ha] at ht; exact max_eq_right ht.2]
    rw [intervalIntegral.integral_congr (g := fun t => t) (a := 0) (b := b) fun t ht => by
      rw [Set.uIcc_of_le hb] at ht; exact max_eq_left ht.1]
    rw [intervalIntegral.integral_zero, integral_id, max_eq_left hb, max_eq_right ha]; ring

/-- `∫_a^b (t⁺)² = ((b⁺)³ - (a⁺)³) / 3`. -/
lemma integral_posPart_sq {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, max t 0 ^ 2 = (max b 0 ^ 3 - max a 0 ^ 3) / 3 := by
  rcases le_total b 0 with hb | hb
  · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => by
      rw [Set.uIcc_of_le hab] at ht; simp [max_eq_right (ht.2.trans hb)]]
    rw [intervalIntegral.integral_zero, max_eq_right hb, max_eq_right (hab.trans hb)]; ring
  rcases le_total 0 a with ha | ha
  · rw [intervalIntegral.integral_congr (g := fun t => t ^ 2) fun t ht => by
      rw [Set.uIcc_of_le hab] at ht; simp only [max_eq_left (ha.trans ht.1)]]
    rw [integral_pow, max_eq_left hb, max_eq_left ha]; ring
  · have hc : Continuous fun t : ℝ => max t 0 ^ 2 := (continuous_id.max continuous_const).pow 2
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (a := a) (b := 0) fun t ht => by
      rw [Set.uIcc_of_le ha] at ht; simp [max_eq_right ht.2]]
    rw [intervalIntegral.integral_congr (g := fun t => t ^ 2) (a := 0) (b := b) fun t ht => by
      rw [Set.uIcc_of_le hb] at ht; simp only [max_eq_left ht.1]]
    rw [intervalIntegral.integral_zero, integral_pow, max_eq_left hb, max_eq_right ha]; ring

/-- **The rectangle integral of `(y + u - 1)⁺`.** -/
lemma integral_rect_posPart {y0 y1 u0 u1 : ℝ} (hy : y0 ≤ y1) (hu : u0 ≤ u1) :
    ∫ y in y0..y1, ∫ u in u0..u1, max (y + u - 1) 0 =
      (max (y1 + u1 - 1) 0 ^ 3 - max (y0 + u1 - 1) 0 ^ 3 - (max (y1 + u0 - 1) 0 ^ 3 - max (y0 + u0 - 1) 0 ^ 3)) / 6 := by
  have hin : ∀ y : ℝ, ∫ u in u0..u1, max (y + u - 1) 0 = (max (y + u1 - 1) 0 ^ 2 - max (y + u0 - 1) 0 ^ 2) / 2 := by
    intro y
    have := intervalIntegral.integral_comp_add_left (fun t => max t 0) (y - 1) (a := u0) (b := u1)
    rw [show (fun u => max (y + u - 1) 0) = fun u => max (y - 1 + u) 0 from funext fun u => by ring_nf,
      this, integral_posPart (by linarith)]
    ring_nf
  simp_rw [hin]
  have hc : ∀ c : ℝ, Continuous fun y : ℝ => max (y + c) 0 ^ 2 := fun c =>
    ((continuous_id.add continuous_const).max continuous_const).pow 2
  have hout : ∀ c : ℝ, ∫ y in y0..y1, max (y + c) 0 ^ 2 = (max (y1 + c) 0 ^ 3 - max (y0 + c) 0 ^ 3) / 3 := by
    intro c
    rw [intervalIntegral.integral_comp_add_right (fun t => max t 0 ^ 2) c, integral_posPart_sq (by linarith)]
  have hsub : ∫ y in y0..y1, (max (y + u1 - 1) 0 ^ 2 - max (y + u0 - 1) 0 ^ 2) =
      (max (y1 + u1 - 1) 0 ^ 3 - max (y0 + u1 - 1) 0 ^ 3) / 3 -
        (max (y1 + u0 - 1) 0 ^ 3 - max (y0 + u0 - 1) 0 ^ 3) / 3 := by
    have e : ∀ c : ℝ, ∀ y : ℝ, max (y + c - 1) 0 ^ 2 = max (y + (c - 1)) 0 ^ 2 := fun c y => by ring_nf
    simp_rw [e]
    rw [intervalIntegral.integral_sub ((hc _).intervalIntegrable _ _) ((hc _).intervalIntegrable _ _), hout, hout]
    ring_nf
  first
  | (rw [intervalIntegral.integral_div, hsub]; ring)
  | (rw [hsub]; ring)

end Census
end IIT
