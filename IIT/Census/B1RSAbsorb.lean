/-
Census, Lemma RS: absorbing the polynomial factors into the rate (`1.0072 → RXf = 1.007`).
-/
import IIT.Census.B1DefsX

namespace IIT
namespace Census

open Filter

/-- The lower-order exponent is `O(log N)`. -/
lemma rs_slack_le (N : ℕ) : 19 * slT N + 17 * (8 + slV N) + 9 ≤ 4000 + 1400 * Real.log N := by
  have hl : (Nat.log 2 N : ℝ) ≤ 2 * Real.log N := by
    have h1 := Real.natLog_le_logb N 2
    push_cast at h1
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have h2 : Real.logb 2 N ≤ 2 * Real.log N := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
      have := Real.log_two_gt_d9
      nlinarith
    linarith
  unfold slT slV D0U; push_cast
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  nlinarith

/-- **Absorption**: `C · N · e^{19 slT + 17(8+slV) + 9} · e^{-1.0072 N} ≤ e^{-RXf N}` eventually. -/
theorem rs_absorb (C : ℝ) : ∀ᶠ N : ℕ in atTop,
    C * N * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) * Real.exp (-((10072 / 10000 : ℝ) * N)) ≤
      Real.exp (-(RXf * N)) := by
  -- log-linear comparison: log C + log N + 4000 + 1400 log N ≤ (1/5000) N eventually
  have hlo := Real.isLittleO_log_id_atTop
  have hev : ∀ᶠ x : ℝ in atTop, |C| + 4000 + 1401 * Real.log x ≤ x / 5000 := by
    have h1 := hlo.def (c := 1 / 14010000) (by norm_num)
    filter_upwards [h1, eventually_ge_atTop (10000 * (|C| + 4000)), eventually_ge_atTop 1]
      with x hx hx1 hx2
    simp only [Real.norm_eq_abs, id] at hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx2
    rw [abs_of_nonneg hlog, abs_of_nonneg (by linarith)] at hx
    have := abs_nonneg C
    linarith
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hev, eventually_ge_atTop 1] with N hN hN1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hsl := rs_slack_le N
  have hCN : C * N ≤ Real.exp (|C| + Real.log N) := by
    rw [Real.exp_add, Real.exp_log (by linarith)]
    have : C ≤ Real.exp |C| := (le_abs_self C).trans (by linarith [Real.add_one_le_exp |C|])
    exact mul_le_mul_of_nonneg_right this (by linarith)
  calc C * N * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) * Real.exp (-((10072 / 10000 : ℝ) * N))
      ≤ Real.exp (|C| + Real.log N) * Real.exp (4000 + 1400 * Real.log N) *
          Real.exp (-((10072 / 10000 : ℝ) * N)) := by
        gcongr
    _ = Real.exp (|C| + 4000 + 1401 * Real.log N - (10072 / 10000 : ℝ) * N) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(RXf * N)) := by
        apply Real.exp_le_exp.2; unfold RXf; linarith

open MeasureTheory

/-- **The bridge**: the F-projection of `GoodFX` is the `cubeM` measure of `B1FGoodX`. -/
theorem rowsIn_goodFX_eq {N : ℕ} (s r0 : State N) (x : Fin N) (σ : XSide) :
    rowsInM (sensRows s r0) (GoodFX N s r0 x σ) = cubeM N {w | B1FGoodX N s r0 x σ w} := by
  rw [← cubeM_restrIn_preimage]
  congr 1
  ext w
  simp only [GoodFX, Set.mem_setOf_eq]
  exact (B1FGoodX.congr fun r hr => by simp [b1Ext, restrIn, hr]).symm

/-- `GoodFX`'s projection is bounded by the regime event, and it is empty unless `r0` is far from `s`. -/
theorem rowsIn_goodFX_le {N : ℕ} (s r0 : State N) (x : Fin N) (σ : XSide) :
    rowsInM (sensRows s r0) (GoodFX N s r0 x σ) ≤
      if N ≤ 3 * ham r0 s then cubeM N {w | RegEvX N s r0 x σ w} else 0 := by
  rw [rowsIn_goodFX_eq]
  split_ifs with h
  · exact measure_mono fun w hw => hw.regEv
  · have : {w | B1FGoodX N s r0 x σ w} = ∅ := Set.eq_empty_of_forall_notMem fun w hw => h hw.far
    rw [this, measure_empty]

end Census
end IIT
