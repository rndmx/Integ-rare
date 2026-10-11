/-
Census, B1 forced leaf 15 (`posNear`, agent "forcedF"): the kernel-checked posNear joint records.

Per record `C` (same `(v, w)` as the RS cell of the same index): the `cellIq` validity conditions,
`cellIq v w λ P ≤ ub`, `log(2 ub Ex' M) ≤ r` and `r + tilt · x0hi + 1/25 ≤ -1.013`, where on the cause side
`Ex' = rsEx(l_u)`, `tilt = (P+4)/4 + l_u`, and on the effect side `Ex' = rsExm1(p) = 2∫_{1/2}^1 y^{p-1}`,
`tilt = P/4 + p` (`p ≥ 1`); `M = 19/25` bounds `E max(m̃, b1Cap)`.
-/
import IIT.Census.CertRSX
import IIT.Census.CertRSXE
import IIT.Census.B1ForcedFPosDataC
import IIT.Census.B1ForcedFPosDataE

namespace IIT
namespace Census

/-- The subcube constant. -/
def pnM : ℚ := 19 / 25
/-- The rate constant. -/
def pnRT : ℚ := 1013 / 1000
/-- `2 ∫_{1/2}^1 y^{p-1} dy` for `p ≥ 1`. -/
def rsExm1 (l : ℕ) : ℚ := 2 * (1 - (1 / 2 : ℚ) ^ l) / l

/-- The `cellIq` validity part. -/
def pnValid (C : RSCell) : Bool :=
  decide (0 < C.v) && decide (C.v ≤ C.w) && decide (C.w ≤ 1) && decide (C.v < 1) &&
    decide ((1 : ℚ) / 2 ≤ C.w ^ 4) &&
    (List.range (C.lam + 2)).all (fun k => decide ((C.P : ℤ) + 4 * k - 4 * C.lam + 4 ≠ 0)) &&
    decide ((C.P : ℤ) + 8 ≠ 0) && decide ((C.P : ℤ) - 4 * C.lam + 4 ≠ 0) &&
    decide ((C.P : ℤ) - 4 * C.lam + 8 ≠ 0) && decide (cellIq C.v C.w C.lam C.P ≤ C.ub)

def pnOKC (C : RSCell) : Bool :=
  pnValid C && decide (0 < 2 * C.ub * rsEx C.lu * pnM) &&
    decide (|1 - crRed (2 * C.ub * rsEx C.lu * pnM) C.k| < 1) &&
    decide (crLnHi (2 * C.ub * rsEx C.lu * pnM) C.k C.n ≤ C.r) &&
    decide (C.r + (((C.P : ℚ) + 4) / 4 + C.lu) * crX0hi + 1 / 25 ≤ -pnRT)

def pnOKE (C : RSCell) : Bool :=
  pnValid C && decide (1 ≤ C.lu) && decide (0 < 2 * C.ub * rsExm1 C.lu * pnM) &&
    decide (|1 - crRed (2 * C.ub * rsExm1 C.lu * pnM) C.k| < 1) &&
    decide (crLnHi (2 * C.ub * rsExm1 C.lu * pnM) C.k C.n ≤ C.r) &&
    decide (C.r + ((C.P : ℚ) / 4 + C.lu) * crX0hi + 1 / 25 ≤ -pnRT)

theorem pnCellsC_ok : pnCellsC.all pnOKC = true := by decide +kernel
theorem pnCellsE_ok : pnCellsE.all pnOKE = true := by decide +kernel

theorem pnLinkC_all : cellsXCauseData.all (fun c => pnCellsC.any (fun C => rsLink C c)) = true := by
  decide +kernel
theorem pnLinkE_all : cellsXEffectData.all (fun c => pnCellsE.any (fun C => rsLinkE C c)) = true := by
  decide +kernel

theorem pnBoundsC : pnCellsC.all (fun C => decide (C.lam ≤ 17) && decide (C.lu ≤ 5) && decide (C.P ≤ 40)) = true := by
  decide +kernel
theorem pnBoundsE : pnCellsE.all (fun C => decide (C.lam ≤ 17) && decide (C.lu ≤ 5) && decide (C.P ≤ 40)) = true := by
  decide +kernel

end Census
end IIT
