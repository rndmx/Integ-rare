/-
Census, B1 lower bound: kernel checks of the E_X data (`CertEXData`).

Pair cells: `[f + sa·hy, f + (sa+1)·hy) × [u0, u1)`, `f = 1001/2000`, `hy = (1 - f)/40`; row-`s` cells `[x0, x1)`.
Checked: positivity, ranges, masses summing to 1, `a ≤ Q · area`, `log Q ≤ r` (A6's `crLnHi`, 30 terms),
`Σ a r ≤ KL_hi`, and disjointness (same strip ⇒ ordered `u`-intervals; row-`s` intervals sorted).
-/
import IIT.Census.CertRatesCore
import IIT.Census.CertEXData

set_option maxRecDepth 100000

namespace IIT
namespace Census

def exF : ℚ := 1001 / 2000

def exPOK (C : EXPCell) : Bool :=
  decide (0 < C.a) && decide (C.sa < 40) && decide (0 ≤ C.u0) && decide (C.u0 < C.u1) && decide (C.u1 ≤ 1) &&
    decide (C.a ≤ C.Q * (exHy * (C.u1 - C.u0))) &&
    (decide (0 < C.Q) && decide (|1 - crRed C.Q C.k| < 1) && decide (crLnHi C.Q C.k 30 ≤ C.r))

def exSOK (C : EXSCell) : Bool :=
  decide (0 < C.a) && decide (0 ≤ C.x0) && decide (C.x0 < C.x1) && decide (C.x1 ≤ 1) &&
    decide (C.a ≤ C.Q * (C.x1 - C.x0)) &&
    (decide (0 < C.Q) && decide (|1 - crRed C.Q C.k| < 1) && decide (crLnHi C.Q C.k 30 ≤ C.r))

set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
theorem exPCells_ok : exPCells.all exPOK = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem exSCells_ok : exSCells.all exSOK = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem exPCells_len : exPCells.length = 4159 := by decide +kernel
set_option maxHeartbeats 0 in
theorem exSCells_len : exSCells.length = 400 := by decide +kernel
set_option maxHeartbeats 0 in
theorem exPCells_sum : (exPCells.map EXPCell.a).sum = 1 := by decide +kernel
set_option maxHeartbeats 0 in
theorem exSCells_sum : (exSCells.map EXSCell.a).sum = 1 := by decide +kernel
set_option maxHeartbeats 0 in
theorem exPCells_KL : (exPCells.map fun C => C.a * C.r).sum ≤ exKLPhi := by decide +kernel
set_option maxHeartbeats 0 in
theorem exSCells_KL : (exSCells.map fun C => C.a * C.r).sum ≤ exKLShi := by decide +kernel
set_option maxHeartbeats 0 in
theorem exRate : exKLPhi + exKLShi - 6931471803 / 10000000000 ≤ 10083 / 10000 := by decide +kernel

/-- Order of pair cells: an earlier strip, or the same strip with an earlier `u`-interval. -/
def exPRel (C D : EXPCell) : Bool := decide (C.sa < D.sa) || (decide (C.sa = D.sa) && decide (C.u1 ≤ D.u0))

/-- Order of row-`s` cells. -/
def exSRel (C D : EXSCell) : Bool := decide (C.x1 ≤ D.x0)

/-- A structurally recursive chain check. -/
def chainB {α : Type} (R : α → α → Bool) : List α → Bool
  | a :: b :: l => R a b && chainB R (b :: l)
  | _ => true

theorem chainB_isChain {α : Type} (R : α → α → Bool) : ∀ l : List α, chainB R l = true →
    l.IsChain (fun a b => R a b = true)
  | [], _ => List.isChain_nil
  | [_], _ => List.isChain_singleton _
  | a :: b :: l, h => by
      simp only [chainB, Bool.and_eq_true] at h
      exact List.isChain_cons_cons.2 ⟨h.1, chainB_isChain R (b :: l) h.2⟩

set_option maxHeartbeats 0 in
theorem exPCells_chainB : chainB exPRel exPCells = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem exSCells_chainB : chainB exSRel exSCells = true := by decide +kernel

end Census
end IIT
