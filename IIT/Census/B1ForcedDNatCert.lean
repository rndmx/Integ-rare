/-
Census, B1 forced leaf 7 (natural regime): the kernel-checked certificate of the 118 natural cells
(data `B1ForcedDNatData`).

Per cell `C` (y_top cell `[tlo, thi]`, floor `v⁴`, cap `w⁴`, exponent `p = P/4`, link `l_u = L/4`, count `2^{-a}`):
* `v⁴ ≤ (1/2 - 10⁻⁶) · Σ_{i<12} x^i/i!` with `x = (2/5)(1 - 10⁻⁵) tlo` (the forced floor, W7 §8.2);
* `thi ≤ w⁴`, `P + L ≥ 0`, `P ≠ -4`;
* `I = (w^{P+4} - v^{P+4})/((P+4)/4) + 2^{-a} (1 - w^{P+4})/((P+4)/4) ≤ ub`;
* `e2⁴ 2^{L+4} ≤ 1` (so `e2 ≤ 2^{-(L/4+1)}` and `Ex := 2(1 - e2)/((L+4)/4) ≥ E[x^{L/4}]`);
* `log (2 · ub · Ex) ≤ r` and `r + ((P+L)/4) x0hi + 10⁻⁵ a ln2hi ≤ -1.0106`;
* the self case (`tc = s`, one row): `log Iₛ ≤ rₛ`, `rₛ + (Pₛ/4) x0hi + 10⁻⁵ aₛ ln2hi ≤ -1.0106`.
The cells chain from `0` to `1` (`dnChain`).
-/
import IIT.Census.CertRatesCore
import IIT.Census.B1ForcedDNatData

namespace IIT
namespace Census

open Finset

/-- `Σ_{i<n} x^i/i!` (a lower bound of `exp x` for `x ≥ 0`). -/
def dnExpLo (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => dnExpLo x n + x ^ n / (n.factorial : ℚ)

/-- The exact cell integral `∫_{v⁴}^{w⁴} y^{P/4} dy + 2^{-a} ∫_{w⁴}^1 y^{P/4} dy`. -/
def dnIq (v w : ℚ) (P : ℤ) (a : ℕ) : ℚ :=
  (w ^ (P + 4) - v ^ (P + 4)) / (((P : ℚ) + 4) / 4) + (1 / 2 : ℚ) ^ a * (1 - w ^ (P + 4)) / (((P : ℚ) + 4) / 4)

/-- Upper bound of `E[x^{L/4}]`, `x ~ U[1/2, 1]`. -/
def dnEx (C : DNCell) : ℚ := 2 * (1 - C.e2) / (((C.L : ℚ) + 4) / 4)

/-- The certified rate. -/
def dnR : ℚ := 10106 / 10000

/-- The per-cell Boolean check. -/
def dnCellOK (C : DNCell) : Bool :=
  decide (0 < C.v) && decide (C.v ≤ C.w) && decide (C.w ≤ 1) && decide (0 ≤ C.tlo) &&
    decide (C.v ^ 4 ≤ (1 / 2 - 1 / 10 ^ 6) * dnExpLo (2 / 5 * (1 - 1 / 10 ^ 5) * C.tlo) 12) &&
    decide (C.thi ≤ C.w ^ 4) && decide (0 ≤ C.P + C.L) && decide (C.P + 4 ≠ 0) &&
    decide (dnIq C.v C.w C.P C.a ≤ C.ub) && decide (0 ≤ C.e2) && decide (C.e2 ^ 4 * 2 ^ (C.L + 4) ≤ 1) &&
    decide (0 < 2 * C.ub * dnEx C) && decide (|1 - crRed (2 * C.ub * dnEx C) C.k| < 1) &&
    decide (crLnHi (2 * C.ub * dnEx C) C.k C.n ≤ C.r) &&
    decide (C.r + ((C.P : ℚ) + C.L) / 4 * crX0hi + 1 / 10 ^ 5 * C.a * crL2hi ≤ -dnR) &&
    decide (dnIq C.v C.w C.Ps C.As ≤ C.ubs) && decide (0 < C.ubs) &&
    decide (|1 - crRed C.ubs C.ks| < 1) && decide (crLnHi C.ubs C.ks C.n ≤ C.rs) &&
    decide (C.rs + (C.Ps : ℚ) / 4 * crX0hi + 1 / 10 ^ 5 * C.As * crL2hi ≤ -dnR)

/-- The chain condition: the cells cover `[a, 1]` in order. -/
def dnChain : ℚ → List DNCell → Bool
  | _, [] => false
  | a, [C] => decide (C.tlo ≤ a) && decide (1 ≤ C.thi)
  | a, C :: D :: l => decide (C.tlo ≤ a) && dnChain C.thi (D :: l)

/-- **The certificate**: every cell passes. -/
theorem dnCells_ok : dnCells.all dnCellOK = true := by decide +kernel

/-- **Coverage**: the cells chain from `0` to `1`. -/
theorem dnCells_chain : dnChain 0 dnCells = true := by decide +kernel

/-- Coverage, real form: every `y ∈ [0, 1]` lies in some cell. -/
theorem dnChain_cover : ∀ (l : List DNCell) (a : ℚ), dnChain a l = true → ∀ y : ℝ, (a : ℝ) ≤ y → y ≤ 1 →
    ∃ C ∈ l, (C.tlo : ℝ) ≤ y ∧ y ≤ C.thi
  | [], _, h, _, _, _ => by simp [dnChain] at h
  | [C], a, h, y, hay, hy1 => by
      simp only [dnChain, Bool.and_eq_true, decide_eq_true_eq] at h
      refine ⟨C, List.mem_singleton_self _, le_trans (by exact_mod_cast h.1) hay, hy1.trans ?_⟩
      exact_mod_cast h.2
  | C :: D :: l, a, h, y, hay, hy1 => by
      simp only [dnChain, Bool.and_eq_true, decide_eq_true_eq] at h
      by_cases hc : y ≤ C.thi
      · exact ⟨C, List.mem_cons_self, le_trans (by exact_mod_cast h.1) hay, hc⟩
      · obtain ⟨C', hC', h'⟩ := dnChain_cover (D :: l) C.thi h.2 y (le_of_lt (not_le.1 hc)) hy1
        exact ⟨C', List.mem_cons_of_mem _ hC', h'⟩

end Census
end IIT
