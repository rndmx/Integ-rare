/-
Census, B1 lower bound, leaf `phi_univ_ge_EX`: the kernel-checked margin certificate of the small-cut sums
(W7 §3 item 2), on the cells of `EX`.

Cause side (pair cells, strip `sa`, `y ∈ [f + sa·hy, f + (sa+1)·hy)`, `U < u1`), in nats:
`Σ_C a_C (L_sa - num_v(y_hi, u1)/f) ≥ marg_v` for the four loss variants
`v = 0 (k = 1)`, `1 (k = 2, x ∈ K)`, `2 (k = 2, x ∉ K)`, `3 (k ≥ 3)`.
Effect side (row-`s` cells, `x ∈ [xlo, xhi]`): `Σ_C a_C (Lx_C - numE_v(xhi)/fe) ≥ marg_v`,
`v = 0 (k = 1)`, `1 (k = 2)`, `2 (k ≥ 3)`.
-/
import IIT.Census.B1UnivCertData

set_option maxRecDepth 100000

namespace IIT
namespace Census

/-! ### Constants -/

def ucF : ℚ := 1001 / 2000
def ucYm : ℚ := ucF + exHy
def ucSig : ℚ := 1021 / 10000
def ucY (sa : ℕ) : ℚ := ucF + sa * exHy
def ueFe : ℚ := 1 / 2 + 1 / 100000

def qmax (a b : ℚ) : ℚ := if a ≤ b then b else a

/-- The cause loss numerators (`f ln 2 ×` the loss bound). -/
def ucNum : ℕ → ℚ → ℚ → ℚ
  | 0, y, _ => (y + 1 - 2 * ucF) ^ 2 / 4
  | 1, y, u => qmax ((y + u - 1) / 4 + 1 / 2 - ucF) 0 + ucSig / 2
  | 2, y, _ => qmax ((y - 1 / 2) / 4 + 1 / 2 - ucF) 0 + 1 / 16
  | _, y, u => qmax (qmax (qmax (y + u - 1) (y - 1 / 2)) 0 / 8 + 1 / 2 - ucF) 0 + ucSig / 2

/-- The effect loss numerators. -/
def ueNum : ℕ → ℚ → ℚ
  | 0, x => (x + 1 - 2 * ueFe) ^ 2 / 4
  | 1, x => qmax ((x - 1 / 2) / 4 + 1 / 2 - ueFe) 0 + 1 / 16
  | _, x => qmax ((x - 1 / 2) / 8 + 1 / 2 - ueFe) 0 + ucSig / 2

def ucMarg : ℕ → ℚ
  | 0 => ucMarg_k1
  | 1 => ucMarg_k2in
  | 2 => ucMarg_k2out
  | _ => ucMarg_k3

def ueMarg : ℕ → ℚ
  | 0 => ucMarg_e1
  | 1 => ucMarg_e2
  | _ => ucMarg_e3

/-- Per-cell lower bound (cause). -/
def ucB (v : ℕ) (C : EXPCell) : ℚ := ucStripL.getD C.sa 0 - ucNum v (ucY (C.sa + 1)) C.u1 / ucF

def ucSum (v : ℕ) : ℚ := (exPCells.map fun C => C.a * ucB v C).sum

/-- The row-`s` cell ends in `x = max(w, 1-w)` coordinates. -/
def ueXlo (C : EXSCell) : ℚ := if 1 / 2 ≤ C.x0 then C.x0 else 1 - C.x1
def ueXhi (C : EXSCell) : ℚ := if 1 / 2 ≤ C.x0 then C.x1 else 1 - C.x0

def ueSum (v : ℕ) : ℚ := ((exSCells.zip ueCellL).map fun p => p.1.a * (p.2 - ueNum v (ueXhi p.1) / ueFe)).sum

/-! ### Kernel checks -/

def ucStripOK : Bool := (List.range 40).all fun sa =>
  decide (0 < ucY sa / ucYm) && decide (|1 - crRed (ucY sa / ucYm) (ucStripK.getD sa 0)| < 1) &&
    decide (ucStripL.getD sa 0 ≤ crLnLo (ucY sa / ucYm) (ucStripK.getD sa 0) 25)

set_option maxHeartbeats 0 in
theorem ucStrip_ok : ucStripOK = true := by decide +kernel

def ueCellOK : Bool := ((exSCells.zip (ueCellL.zip ueCellK)).all fun p =>
  decide (0 < ueXlo p.1 / ueXmBD) && decide (|1 - crRed (ueXlo p.1 / ueXmBD) p.2.2| < 1) &&
    decide (p.2.1 ≤ crLnLo (ueXlo p.1 / ueXmBD) p.2.2 25))

set_option maxHeartbeats 0 in
theorem ueCell_ok : ueCellOK = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ueCellL_len : ueCellL.length = 400 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ucSum_ok0 : ucMarg 0 ≤ ucSum 0 := by decide +kernel
set_option maxHeartbeats 0 in
theorem ucSum_ok1 : ucMarg 1 ≤ ucSum 1 := by decide +kernel
set_option maxHeartbeats 0 in
theorem ucSum_ok2 : ucMarg 2 ≤ ucSum 2 := by decide +kernel
set_option maxHeartbeats 0 in
theorem ucSum_ok3 : ucMarg 3 ≤ ucSum 3 := by decide +kernel
set_option maxHeartbeats 0 in
theorem ueSum_ok0 : ueMarg 0 ≤ ueSum 0 := by decide +kernel
set_option maxHeartbeats 0 in
theorem ueSum_ok1 : ueMarg 1 ≤ ueSum 1 := by decide +kernel
set_option maxHeartbeats 0 in
theorem ueSum_ok2 : ueMarg 2 ≤ ueSum 2 := by decide +kernel

end Census
end IIT
