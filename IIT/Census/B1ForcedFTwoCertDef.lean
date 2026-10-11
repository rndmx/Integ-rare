/-
Census, B1 forced leaf 18 (agent "forcedF"): the checks of the two-failure same-side certificate.

Per record `R` (an overlapping pair of original cells of one side): `0 < v ≤ w ≤ 1`, `v < 1`, `1/2 ≤ w⁴`,
`1/2 ≤ cap2 ≤ 1`, `4 lam2 ≤ P`, the exponent conditions of `cellIq` at every shifted exponent,
`tfTIq R = Σ_k coef_k · cellIq v w lam (P - 4 lam2 + 4k) ≤ ub` (the exact value of
`∫_{v⁴}^1 y^{P/4} gX(lam, w⁴, y) Gh(lam2, cap2, y) dy`), `log(2 ub rsEx(l2)) ≤ r`, `r + (P/4 + l2) x0hi ≤ -1.03`.
-/
import IIT.Census.CertRSX
import IIT.Census.B1ForcedFTwoDataDef

namespace IIT
namespace Census

open Finset

/-- The rate constant of the two-failure records. -/
def tfRT : ℚ := 103 / 100

/-- The coefficient of `y^{k - lam2}` in the Laurent form `Gh` of `gX lam2 c2` above the cap. -/
def tfCoef (lam2 : ℕ) (c2 : ℚ) (k : ℕ) : ℚ :=
  ((lam2 + 1).choose k : ℚ) / ((lam2 + 1) * 2 ^ lam2) +
    (if k = 0 then 2 * c2 ^ (lam2 + 1) - (2 * c2) ^ (lam2 + 1) / ((lam2 + 1) * 2 ^ lam2) else 0) +
    (if k = 1 then -c2 ^ lam2 else 0)

/-- The exact value of the record's integral. -/
def tfTIq (R : TFRec) : ℚ :=
  ∑ k ∈ range (R.lam2 + 2), tfCoef R.lam2 R.cap2 k * cellIq R.v R.w R.lam (R.P - 4 * R.lam2 + 4 * k)

/-- The exponent conditions of `cellIq_eq`. -/
def tfExpOK (lam P : ℕ) : Bool :=
  (List.range (lam + 2)).all (fun k => decide ((P : ℤ) + 4 * k - 4 * lam + 4 ≠ 0)) &&
    decide ((P : ℤ) + 8 ≠ 0) && decide ((P : ℤ) - 4 * lam + 4 ≠ 0) && decide ((P : ℤ) - 4 * lam + 8 ≠ 0)

/-- The per-record check. -/
def tfOK (R : TFRec) : Bool :=
  decide (0 < R.v) && decide (R.v ≤ R.w) && decide (R.w ≤ 1) && decide (R.v < 1) &&
    decide ((1 : ℚ) / 2 ≤ R.w ^ 4) && decide ((1 : ℚ) / 2 ≤ R.cap2) && decide (R.cap2 ≤ 1) &&
    decide (4 * R.lam2 ≤ R.P) &&
    (List.range (R.lam2 + 2)).all (fun k => tfExpOK R.lam (R.P - 4 * R.lam2 + 4 * k)) &&
    decide (tfTIq R ≤ R.ub) && decide (0 < 2 * R.ub * rsEx R.l2) &&
    decide (|1 - crRed (2 * R.ub * rsEx R.l2) R.k| < 1) &&
    decide (crLnHi (2 * R.ub * rsEx R.l2) R.k R.n ≤ R.r) &&
    decide (R.r + ((R.P : ℚ) / 4 + R.l2) * crX0hi ≤ -tfRT)

/-- Bounds on the multipliers. -/
def tfBounds (R : TFRec) : Bool :=
  decide (R.lam ≤ 17) && decide (R.lam2 ≤ 6) && decide (R.P ≤ 40) && decide (R.l2 ≤ 5)

/-- Cause-side link: the record covers its first cell (window, cap) and its second cell (cap). -/
def tfLinkC (R : TFRec) : Bool :=
  decide (R.v ^ 4 ≤ R.c1.1) && (decide (R.c1.2 ≤ R.w ^ 4) || decide (R.w = 1)) &&
    (decide (R.c2.2 ≤ R.cap2) || decide (R.cap2 = 1)) && tfBounds R

/-- Effect-side link (window `≤ max(1/2, m_lo)`). -/
def tfLinkE (R : TFRec) : Bool :=
  decide (R.v ^ 4 ≤ max (1 / 2) R.c1.1) && (decide (R.c1.2 ≤ R.w ^ 4) || decide (R.w = 1)) &&
    (decide (R.c2.2 ≤ R.cap2) || decide (R.cap2 = 1)) && tfBounds R

end Census
end IIT
