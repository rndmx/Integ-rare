/-
Census of complexes, B1 development, module A6 (part 0): the numerical core of the rate
certificates (`B1-W6-certificates.md`, Section 1.2).

* Rational enclosures of `Real.log` at rational points, computable and checkable by
  `decide +kernel`: `crLnLo q k n ≤ log q ≤ crLnHi q k n` (`crLnLo_le`, `log_le_crLnHi`).  The
  point is first reduced to `q / 2^k` (`k : ℤ` is part of the data), then the series of
  `-log (1 - x)` is summed to `n` terms (`Real.abs_log_sub_add_sum_range_le`), and `k log 2` is
  enclosed by `Real.log_two_gt_d9`, `Real.log_two_lt_d9`.  The checker forms `crLog_ge`,
  `crLog_le` take a single Boolean hypothesis (`decide +kernel`).
* The constants: `x0 ∈ [x0lo, x0hi]` (`cr_x0_bounds`), `log 2 ∈ (crL2lo, crL2hi)`.
* Asymptotic helpers for the "eventually" forms of the certificates: `cr_ev_log_le`
  (`a log N + b ≤ c N` eventually) and `cr_ev_poly_exp` (`(N+1)^m e^E ≤ e^{δ N}` eventually).
-/
import IIT.Census.B1Chernoff
import IIT.Census.B1Defs
import Mathlib.Analysis.Complex.ExponentialBounds

namespace IIT
namespace Census

open Finset Filter Topology

/-! ### Rational enclosures of `log` -/

/-- `∑_{i<n} x^{i+1}/(i+1)`, the partial sums of `-log (1 - x)`. -/
def crLogSer (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => crLogSer x n + x ^ (n + 1) / (n + 1)

lemma crLogSer_cast (x : ℚ) (n : ℕ) :
    ((crLogSer x n : ℚ) : ℝ) = ∑ i ∈ range n, (x : ℝ) ^ (i + 1) / (i + 1) := by
  induction n with
  | zero => simp [crLogSer]
  | succ n ih =>
    rw [crLogSer, Finset.sum_range_succ, ← ih]
    push_cast
    ring

/-- `q / 2^k` (`k : ℤ`). -/
def crRed (q : ℚ) (k : ℤ) : ℚ := if 0 ≤ k then q / 2 ^ k.toNat else q * 2 ^ (-k).toNat

lemma crRed_cast (q : ℚ) (k : ℤ) : ((crRed q k : ℚ) : ℝ) = q / (2 : ℝ) ^ k := by
  unfold crRed
  split_ifs with h
  · push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg h]
  · push_cast
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨(-k).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
    subst hn
    rw [zpow_neg, zpow_natCast, div_inv_eq_mul]
    simp

/-- The lower rational bound of `log 2` (`Real.log_two_gt_d9`). -/
def crL2lo : ℚ := 6931471803 / 10000000000

/-- The upper rational bound of `log 2` (`Real.log_two_lt_d9`). -/
def crL2hi : ℚ := 6931471808 / 10000000000

lemma crL2lo_lt : ((crL2lo : ℚ) : ℝ) < Real.log 2 := by
  have h := Real.log_two_gt_d9
  unfold crL2lo
  push_cast
  norm_num at h ⊢
  linarith

lemma log_two_lt_crL2hi : Real.log 2 < ((crL2hi : ℚ) : ℝ) := by
  have h := Real.log_two_lt_d9
  unfold crL2hi
  push_cast
  norm_num at h ⊢
  linarith

/-- Lower bound of `k log 2`. -/
def crKL2lo (k : ℤ) : ℚ := if 0 ≤ k then k * crL2lo else k * crL2hi

/-- Upper bound of `k log 2`. -/
def crKL2hi (k : ℤ) : ℚ := if 0 ≤ k then k * crL2hi else k * crL2lo

lemma crKL2lo_le (k : ℤ) : ((crKL2lo k : ℚ) : ℝ) ≤ k * Real.log 2 := by
  have h1 := crL2lo_lt
  have h2 := log_two_lt_crL2hi
  unfold crKL2lo
  split_ifs with h
  · push_cast
    have : (0 : ℝ) ≤ k := by exact_mod_cast h
    nlinarith
  · push_cast
    have : (k : ℝ) < 0 := by exact_mod_cast (not_le.1 h)
    nlinarith

lemma le_crKL2hi (k : ℤ) : (k : ℝ) * Real.log 2 ≤ ((crKL2hi k : ℚ) : ℝ) := by
  have h1 := crL2lo_lt
  have h2 := log_two_lt_crL2hi
  unfold crKL2hi
  split_ifs with h
  · push_cast
    have : (0 : ℝ) ≤ k := by exact_mod_cast h
    nlinarith
  · push_cast
    have : (k : ℝ) < 0 := by exact_mod_cast (not_le.1 h)
    nlinarith

/-- The remainder `|x|^{n+1}/(1-|x|)` of the log series. -/
def crLnErr (x : ℚ) (n : ℕ) : ℚ := |x| ^ (n + 1) / (1 - |x|)

/-- Rational lower bound of `log q` (reduction by `2^k`, `n` terms). -/
def crLnLo (q : ℚ) (k : ℤ) (n : ℕ) : ℚ :=
  -crLogSer (1 - crRed q k) n - crLnErr (1 - crRed q k) n + crKL2lo k

/-- Rational upper bound of `log q` (reduction by `2^k`, `n` terms). -/
def crLnHi (q : ℚ) (k : ℤ) (n : ℕ) : ℚ :=
  -crLogSer (1 - crRed q k) n + crLnErr (1 - crRed q k) n + crKL2hi k

/-- The series estimate at the reduced point, in the form used by both bounds. -/
lemma cr_log_series {q : ℚ} {k : ℤ} (n : ℕ) (hq : 0 < q) (hx : |1 - crRed q k| < 1) :
    |((crLogSer (1 - crRed q k) n : ℚ) : ℝ) + (Real.log q - k * Real.log 2)| ≤
      ((crLnErr (1 - crRed q k) n : ℚ) : ℝ) := by
  set x : ℚ := 1 - crRed q k with hxdef
  have hxR : |(x : ℝ)| < 1 := by exact_mod_cast hx
  have hS := Real.abs_log_sub_add_sum_range_le hxR n
  have h1x : (1 : ℝ) - x = q / (2 : ℝ) ^ k := by
    rw [hxdef]; push_cast; rw [crRed_cast]; ring
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog : Real.log ((q : ℝ) / 2 ^ k) = Real.log q - k * Real.log 2 := by
    rw [Real.log_div hqR.ne' (zpow_pos (by norm_num) k).ne', Real.log_zpow]
  rw [h1x, hlog] at hS
  rw [crLogSer_cast, crLnErr]
  push_cast
  exact hS

theorem crLnLo_le {q : ℚ} {k : ℤ} (n : ℕ) (hq : 0 < q) (hx : |1 - crRed q k| < 1) :
    ((crLnLo q k n : ℚ) : ℝ) ≤ Real.log q := by
  have hS := (abs_le.1 (cr_log_series n hq hx)).1
  have hk := crKL2lo_le k
  have e : ((crLnLo q k n : ℚ) : ℝ) = -((crLogSer (1 - crRed q k) n : ℚ) : ℝ) -
      ((crLnErr (1 - crRed q k) n : ℚ) : ℝ) + ((crKL2lo k : ℚ) : ℝ) := by
    unfold crLnLo; push_cast; ring
  rw [e]
  linarith

theorem log_le_crLnHi {q : ℚ} {k : ℤ} (n : ℕ) (hq : 0 < q) (hx : |1 - crRed q k| < 1) :
    Real.log q ≤ ((crLnHi q k n : ℚ) : ℝ) := by
  have hS := (abs_le.1 (cr_log_series n hq hx)).2
  have hk := le_crKL2hi k
  have e : ((crLnHi q k n : ℚ) : ℝ) = -((crLogSer (1 - crRed q k) n : ℚ) : ℝ) +
      ((crLnErr (1 - crRed q k) n : ℚ) : ℝ) + ((crKL2hi k : ℚ) : ℝ) := by
    unfold crLnHi; push_cast; ring
  rw [e]
  linarith

/-- **Checker form, lower bound**: `r ≤ log q` from one Boolean check. -/
theorem crLog_ge {q r : ℚ} (k : ℤ) (n : ℕ)
    (h : (decide (0 < q) && decide (|1 - crRed q k| < 1) && decide (r ≤ crLnLo q k n)) = true) :
    (r : ℝ) ≤ Real.log q := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hq, hx⟩, hr⟩ := h
  exact (by exact_mod_cast hr : (r : ℝ) ≤ crLnLo q k n).trans (crLnLo_le n hq hx)

/-- **Checker form, upper bound**: `log q ≤ r` from one Boolean check. -/
theorem crLog_le {q r : ℚ} (k : ℤ) (n : ℕ)
    (h : (decide (0 < q) && decide (|1 - crRed q k| < 1) && decide (crLnHi q k n ≤ r)) = true) :
    Real.log q ≤ r := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hq, hx⟩, hr⟩ := h
  exact (log_le_crLnHi n hq hx).trans (by exact_mod_cast hr)

/-! ### The constants `x0`, `log 2` -/

/-- `x0 ≥ x0lo`. -/
def crX0lo : ℚ := 2027325540 / 10000000000

/-- `x0 ≤ x0hi`. -/
def crX0hi : ℚ := 2027325541 / 10000000000

theorem cr_x0_bounds : ((crX0lo : ℚ) : ℝ) ≤ x0 ∧ x0 ≤ ((crX0hi : ℚ) : ℝ) := by
  have h1 : (((2 * crX0lo : ℚ)) : ℝ) ≤ Real.log (((3 / 2 : ℚ)) : ℝ) :=
    crLog_ge 0 45 (by decide +kernel)
  have h2 : Real.log (((3 / 2 : ℚ)) : ℝ) ≤ (((2 * crX0hi : ℚ)) : ℝ) :=
    crLog_le 0 45 (by decide +kernel)
  have e : (((3 / 2 : ℚ)) : ℝ) = 3 / 2 := by norm_num
  rw [e] at h1 h2
  push_cast at h1 h2
  unfold x0
  constructor <;> linarith

lemma cr_log2_bounds : ((crL2lo : ℚ) : ℝ) < Real.log 2 ∧ Real.log 2 < ((crL2hi : ℚ) : ℝ) :=
  ⟨crL2lo_lt, log_two_lt_crL2hi⟩

/-! ### Asymptotic helpers -/

/-- `a log N + b ≤ c N` eventually (`c > 0`). -/
theorem cr_ev_log_le (a b : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, a * Real.log N + b ≤ c * N := by
  have hlo := Real.isLittleO_log_id_atTop
  have hb := hlo.bound (c := c / (2 * (|a| + 1))) (by positivity)
  have hT : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h1 := hT.eventually hb
  have h2 := hT.eventually (eventually_ge_atTop (2 * (|b| + 1) / c))
  have h3 := hT.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [h1, h2, h3] with N hN1 hN2 hN3
  simp only [id, Real.norm_eq_abs] at hN1
  have hN0 : (0 : ℝ) ≤ N := by linarith
  rw [abs_of_nonneg hN0] at hN1
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN3
  rw [abs_of_nonneg hlog0] at hN1
  have hA : a * Real.log N ≤ |a| * Real.log N := mul_le_mul_of_nonneg_right (le_abs_self a) hlog0
  have hB : (|a| + 1) * Real.log N ≤ c / 2 * N := by
    have := mul_le_mul_of_nonneg_left hN1 (show (0 : ℝ) ≤ |a| + 1 by positivity)
    calc (|a| + 1) * Real.log N ≤ (|a| + 1) * (c / (2 * (|a| + 1)) * N) := this
      _ = c / 2 * N := by field_simp
  have hC : b ≤ c / 2 * N := by
    have h' : 2 * (|b| + 1) ≤ c * N := by
      have := (div_le_iff₀ hc).1 hN2
      linarith
    have := le_abs_self b
    linarith
  nlinarith [abs_nonneg a]

/-- `(N+1)^m e^E ≤ e^{δ N}` eventually (`δ > 0`). -/
theorem cr_ev_poly_exp (m : ℕ) (E : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ((N : ℝ) + 1) ^ m * Real.exp E ≤ Real.exp (δ * N) := by
  filter_upwards [cr_ev_log_le (m : ℝ) (m * Real.log 2 + E) hδ, eventually_ge_atTop 1] with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hlog : Real.log ((N : ℝ) + 1) ≤ Real.log 2 + Real.log N := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log hpos (by linarith)
  rw [← Real.exp_log (pow_pos hpos m), ← Real.exp_add, Real.exp_le_exp, Real.log_pow]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

end Census
end IIT
