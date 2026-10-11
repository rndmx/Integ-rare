/-
Census, Lemma RS: the kernel-checked certificate of the 61 regime-X cause cells (data `CertRSDataX`).

Per cell `C`: `0 < v ≤ w ≤ 1`, all exponents of `cellIq` nonzero, `cellIq v w λ P ≤ ub`,
`log (2 · ub · Ex) ≤ r` (A6's `crLnHi`), and `r + (P/4 + l_u) · x0hi ≤ -1.0072`.
-/
import IIT.Census.B1RegInt
import IIT.Census.CertRatesCore
import IIT.Census.CertRSDataX
import IIT.Census.CertRatesDataX

namespace IIT
namespace Census

open Finset

/-- `Ex = 2 (1 - 2^{-(l+1)}) / (l + 1)` as a rational. -/
def rsEx (l : ℕ) : ℚ := 2 * (1 - (1 / 2 : ℚ) ^ (l + 1)) / (l + 1)

/-- The rate constant of the cause cells. -/
def rsR0 : ℚ := 10072 / 10000

/-- The per-cell Boolean check. -/
def rsCellOK (C : RSCell) : Bool :=
  decide (0 < C.v) && decide (C.v ≤ C.w) && decide (C.w ≤ 1) && decide (C.v < 1) &&
    decide ((1 : ℚ) / 2 ≤ C.w ^ 4) &&
    (List.range (C.lam + 2)).all (fun k => decide ((C.P : ℤ) + 4 * k - 4 * C.lam + 4 ≠ 0)) &&
    decide ((C.P : ℤ) + 8 ≠ 0) && decide ((C.P : ℤ) - 4 * C.lam + 4 ≠ 0) &&
    decide ((C.P : ℤ) - 4 * C.lam + 8 ≠ 0) &&
    decide (cellIq C.v C.w C.lam C.P ≤ C.ub) &&
    decide (0 < 2 * C.ub * rsEx C.lu) && decide (|1 - crRed (2 * C.ub * rsEx C.lu) C.k| < 1) &&
    decide (crLnHi (2 * C.ub * rsEx C.lu) C.k C.n ≤ C.r) &&
    decide (C.r + ((C.P : ℚ) / 4 + C.lu) * crX0hi ≤ -rsR0)

/-- **The certificate**: every cause cell passes. -/
theorem rsCellsC_ok : rsCellsC.all rsCellOK = true := by decide +kernel

/-- A certified cell covers an original cell: smaller `m_lo`, larger or inactive cap. -/
def rsLink (C : RSCell) (c : ℚ × ℚ) : Bool :=
  decide (C.v ^ 4 ≤ c.1) && (decide (c.2 ≤ C.w ^ 4) || decide (C.w = 1)) && decide (0 < c.2)

/-- **Every original cause cell is covered by a certified cell.** -/
theorem rsLink_all : cellsXCauseData.all (fun c => rsCellsC.any (fun C => rsLink C c)) = true := by
  decide +kernel

/-- Multiplier ranges of the certified cells. -/
theorem rsBounds : rsCellsC.all (fun C => decide (C.lam ≤ 17) && decide (C.lu ≤ 3) && decide (C.P ≤ 30)) = true := by
  decide +kernel

end Census
end IIT
