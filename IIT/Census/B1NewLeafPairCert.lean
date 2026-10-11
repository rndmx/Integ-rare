/-
Census, B1 new leaf `pairLow` (B1GoodX2): the kernel-checked certificate.

Restricting, in the regime-X cause template, every unit `j ≠ x` to `y_{r0,j} + y_{r1,j} > 1 - 1/N` replaces the
per-unit inner MGF `gX λ c y` by at most `gX λ c y - (1 - y) min(1, c/y)^λ + 1/N` (the integrand is `≥ min(1,c/y)^λ`).
The removed mass `corr = ∫_{v⁴}^1 y^{P/4} (1-y) min(1, c/y)^λ dy` is the rational `plCorrQ`.  Per cell either
`corr ≥ (13/1000) ub` (the cell gains `log(1000/987) ≥ 13/1000` on top of `rsR0`), or the cell's own certified rate is
already `≥ plR = rsR0 + 13/1000`.
-/
import IIT.Census.CertRSX

namespace IIT
namespace Census

/-- `∫_{v⁴}^1 y^{P/4} (1-y) min(1, w⁴/y)^λ dy` as a rational (`v ≤ w ≤ 1`). -/
def plCorrQ (v w : ℚ) (lam P : ℕ) : ℚ :=
  powIntQ v w ((P : ℤ) + 4) - powIntQ v w ((P : ℤ) + 8) +
    (w ^ 4) ^ lam * (powIntQ w 1 ((P : ℤ) - 4 * lam + 4) - powIntQ w 1 ((P : ℤ) - 4 * lam + 8))

/-- The certified rate of the restricted cells. -/
def plR : ℚ := rsR0 + 13 / 1000

/-- The per-cell check of the restricted template. -/
def plOK (C : RSCell) : Bool :=
  decide ((1 : ℚ) / 200 ≤ C.ub) && decide (0 ≤ plCorrQ C.v C.w C.lam C.P) &&
    (decide (13 / 1000 * C.ub ≤ plCorrQ C.v C.w C.lam C.P) ||
      decide (C.r + ((C.P : ℚ) / 4 + C.lu) * crX0hi ≤ -plR))

/-- **The certificate**: every cause cell passes. -/
theorem plCells_ok : rsCellsC.all plOK = true := by decide +kernel

end Census
end IIT

#print axioms IIT.Census.plCells_ok
