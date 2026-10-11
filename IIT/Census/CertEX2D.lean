/-
Census, B1 lower bound: kernel checks of the per-cell bounds of checks S, V, M0, D (data `CertEX2DData`).

Per pair cell: log bounds at the corners `y + u` (series of `q` or of `1/q`, 60 terms, no reduction by `ln 2`) and at
`max(u0, 1e-5)`, `u1`; the per-cell bounds below; their mass-weighted sums against the targets.
-/
import IIT.Census.CertEXAvg
import IIT.Census.CertEX2DData

set_option maxRecDepth 100000

namespace IIT
namespace Census

/-- A table entry `(c, inv, lo, hi)`: `lo ≤ log c ≤ hi` through the series of `c` or of `1/c` (60 terms). -/
def ctabOK (e : ℚ × Bool × ℚ × ℚ) : Bool :=
  if e.2.1 then
    decide (0 < e.1⁻¹) && decide (|1 - crRed e.1⁻¹ 0| < 1) &&
      decide (e.2.2.1 ≤ -crLnHi e.1⁻¹ 0 60) && decide (-crLnLo e.1⁻¹ 0 60 ≤ e.2.2.2)
  else
    decide (0 < e.1) && decide (|1 - crRed e.1 0| < 1) &&
      decide (e.2.2.1 ≤ crLnLo e.1 0 60) && decide (crLnHi e.1 0 60 ≤ e.2.2.2)

theorem exCtab_ok : exCtab.all ctabOK = true := by decide +kernel

def exCt (j : ℕ) : ℚ × Bool × ℚ × ℚ := exCtab.getD (j - 32) (1, false, 0, 0)

/-- A log record `(k, j, lo, hi)`. -/
abbrev LRec := ℤ × ℕ × ℚ × ℚ

/-- `lo ≤ log q ≤ hi` through `log q = log (q / c_j) + log c_j` (10-term series of `q / c_j`, reduced by `2^k`). -/
def lrecOK (q : ℚ) (r : LRec) : Bool :=
  decide (r.2.1 - 32 < exCtab.length) && decide (0 < (exCt r.2.1).1) && decide (0 < q / (exCt r.2.1).1) &&
    decide (|1 - crRed (q / (exCt r.2.1).1) r.1| < 1) &&
    decide (r.2.2.1 ≤ crLnLo (q / (exCt r.2.1).1) r.1 10 + (exCt r.2.1).2.2.1) &&
    decide (crLnHi (q / (exCt r.2.1).1) r.1 10 + (exCt r.2.1).2.2.2 ≤ r.2.2.2)

def exDEL : ℚ := 1 / 10 ^ 5

def EX2DRec.r00 (R : EX2DRec) : LRec := (R.k00, R.j00, R.lo00, R.hi00)
def EX2DRec.r01 (R : EX2DRec) : LRec := (R.k01, R.j01, R.lo01, R.hi01)
def EX2DRec.r10 (R : EX2DRec) : LRec := (R.k10, R.j10, R.lo10, R.hi10)
def EX2DRec.r11 (R : EX2DRec) : LRec := (R.k11, R.j11, R.lo11, R.hi11)
def EX2DRec.rm (R : EX2DRec) : LRec := (R.km, R.jm, R.lom, R.him)
def EX2DRec.ru (R : EX2DRec) : LRec := (R.ku, R.ju, R.lou, R.hiu)

/-- Lower `y` end of a pair cell (`= exYlo C`). -/
def exYl (C : EXPCell) : ℚ := exF + C.sa * exHy

def exYhi (C : EXPCell) : ℚ := exYl C + exHy

/-- `G` bounds from a log bound. -/
def gHi (t : ℚ) (r : LRec) : ℚ := t * t * r.2.2.2 / 2 - 3 * t * t / 4
def gLo (t : ℚ) (r : LRec) : ℚ := t * t * r.2.2.1 / 2 - 3 * t * t / 4

def exRhi (C : EXPCell) (R : EX2DRec) : ℚ :=
  gHi (exYhi C + C.u1) R.r11 - gLo (exYl C + C.u1) R.r01 - gLo (exYhi C + C.u0) R.r10 +
    gHi (exYl C + C.u0) R.r00
def exRlo (C : EXPCell) (R : EX2DRec) : ℚ :=
  gLo (exYhi C + C.u1) R.r11 - gHi (exYl C + C.u1) R.r01 - gHi (exYhi C + C.u0) R.r10 +
    gLo (exYl C + C.u0) R.r00

def exLamLo (C : EXPCell) (R : EX2DRec) : ℚ :=
  crL2lo - exBTup C.sa - exRhi C R / (exHy * (C.u1 - C.u0))
def exLamHi (C : EXPCell) (R : EX2DRec) : ℚ :=
  crL2hi - exBTlo C.sa - exRlo C R / (exHy * (C.u1 - C.u0))

def hP (t : ℚ) : ℚ := if 0 < t then t ^ 3 / 6 else 0

def exVup (C : EXPCell) (R : EX2DRec) : ℚ :=
  min (exLamHi C R) (-exBTlo C.sa - exLnFlo)

def exMlo (C : EXPCell) (R : EX2DRec) : ℚ :=
  if C.u1 ≤ 1 - exYhi C then crL2lo - exBTup C.sa
  else if 1 - exYl C ≤ C.u0 then exLamLo C R
  else crL2lo - exBTup C.sa -
    (hP (exYhi C + C.u1 - 1) - hP (exYhi C + C.u0 - 1) - hP (exYl C + C.u1 - 1) + hP (exYl C + C.u0 - 1)) /
      (exHy * (C.u1 - C.u0))

def exDlo (C : EXPCell) (R : EX2DRec) : ℚ :=
  -exBTup C.sa - (C.u1 * R.hiu - C.u1 - (max C.u0 exDEL * R.lom - max C.u0 exDEL) +
    max (exDEL - C.u0) 0 * R.him) / (C.u1 - C.u0)

def ex2DOK (C : EXPCell) (R : EX2DRec) : Bool :=
  lrecOK (exYl C + C.u0) R.r00 && lrecOK (exYl C + C.u1) R.r01 && lrecOK (exYhi C + C.u0) R.r10 &&
    lrecOK (exYhi C + C.u1) R.r11 && lrecOK (max C.u0 exDEL) R.rm && lrecOK C.u1 R.ru &&
    decide (exDEL ≤ C.u1) &&
    decide (R.sl ≤ exLamLo C R) && decide (exVup C R ≤ R.vu) && decide (R.ml ≤ exMlo C R) &&
    decide (R.dl ≤ exDlo C R)

theorem ex2D_margins : 1 / 400 + 2 / 10 ^ 6 < exESlo ∧ exEVup < -(5 / 10 ^ 7) - 2 / 10 ^ 7 ∧
    1 / 10 ^ 5 + 2 / 10 ^ 7 < exEMlo ∧ 1 / 30 + 1 / 1000 < exEDlo := by decide +kernel

theorem exLnF_ok : lrecOK (1001 / 2000) (exLnFk, exLnFj, exLnFlo, exLnFhi) = true := by decide +kernel

end Census
end IIT
