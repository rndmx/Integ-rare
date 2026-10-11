/-
Census, `SxEffStmt`: the kernel-checked certificate of the 61 `s^x`-weighted effect cells (data `CertSxData`).

Per cell `C`: `0 < v ≤ w ≤ 1`, `v < 1`, `1/2 ≤ w⁴`, all exponents of the two cell integrals nonzero,
`Itot = 2 I(λ+1, LU+4) - I(λ, LU+4) ≤ ub` (`I = cellIq v w`), `log (2 · ub · Ex(p)) ≤ r` (`crLnHi`), and
`r + (LU/4 + p + 1) · x0hi ≤ -R1`, `R1 = 1.0112`.
-/
import IIT.Census.CertRSX
import IIT.Census.CertSxData

namespace IIT
namespace Census

/-- The rate constant of the weighted effect cells. -/
def sxR1 : ℚ := 10112 / 10000

/-- Exponent conditions of `cellIq_eq` at `(λ, P)`. -/
def cellExpOK (lam P : ℕ) : Bool :=
  (List.range (lam + 2)).all (fun k => decide ((P : ℤ) + 4 * k - 4 * lam + 4 ≠ 0)) &&
    decide ((P : ℤ) + 8 ≠ 0) && decide ((P : ℤ) - 4 * lam + 4 ≠ 0) && decide ((P : ℤ) - 4 * lam + 8 ≠ 0)

/-- The weighted row-`s` integral (rational). -/
def sxItot (C : SxCell) : ℚ := 2 * cellIq C.v C.w (C.lam + 1) (C.LU + 4) - cellIq C.v C.w C.lam (C.LU + 4)

/-- The per-cell Boolean check. -/
def sxOK (C : SxCell) : Bool :=
  decide (0 < C.v) && decide (C.v ≤ C.w) && decide (C.w ≤ 1) && decide (C.v < 1) &&
    decide ((1 : ℚ) / 2 ≤ C.w ^ 4) && cellExpOK (C.lam + 1) (C.LU + 4) && cellExpOK C.lam (C.LU + 4) &&
    decide (sxItot C ≤ C.ub) && decide (0 < 2 * C.ub * rsEx C.p) &&
    decide (|1 - crRed (2 * C.ub * rsEx C.p) C.k| < 1) &&
    decide (crLnHi (2 * C.ub * rsEx C.p) C.k C.n ≤ C.r) &&
    decide (C.r + ((C.LU : ℚ) / 4 + C.p + 1) * crX0hi ≤ -sxR1)

/-- **The certificate**: every weighted effect cell passes. -/
theorem sxCells_ok : sxCells.all sxOK = true := by decide +kernel

/-- A certified cell covers an original effect cell (as `rsLinkE`). -/
def sxLink (C : SxCell) (c : ℚ × ℚ) : Bool :=
  decide (C.v ^ 4 ≤ max (1 / 2) c.1) && (decide (c.2 ≤ C.w ^ 4) || decide (C.w = 1)) &&
    decide ((1 : ℚ) / 2 ≤ c.2)

theorem sxLink_all : cellsXEffectData.all (fun c => sxCells.any (fun C => sxLink C c)) = true := by
  decide +kernel

/-- Multiplier ranges. -/
theorem sxBounds : sxCells.all (fun C => decide (C.lam ≤ 29) && decide (C.p ≤ 7) && decide (C.LU ≤ 60)) = true := by
  decide +kernel

end Census
end IIT
