/-
Census, B1 forced leaf 17 (`joint_x2`), part 2: the kernel-checked certificate of the 61 joint-X2 cause cells
(data `B1ForcedECertX2Data`).

Per cell `C`: `0 < v ≤ w ≤ 1`, `v < 1`, `1/2 ≤ w⁴`, all exponents nonzero, `e ≤ 2`, (`e = 0` or `v ≤ q = 49/50`),
`cellIq v w λ P - (1 - 2^{-e}) bIq v q λ P ≤ ub`, `log (2 · ub · Ex) ≤ r` and
`r + (P/4 + l_u) · x0hi + e · log2hi / 4 ≤ -1.07`.
-/
import IIT.Census.B1ForcedEInt
import IIT.Census.CertRSX
import IIT.Census.B1ForcedECertX2Data

namespace IIT
namespace Census

open Finset

/-- The rate constant of the joint-X2 cells. -/
def x2R : ℚ := 107 / 100

/-- The truncation point `q` of the `Neg` integral (`q⁴ ≤ 25/27`). -/
def x2q : ℚ := 49 / 50

/-- The certified value of a cell's outer integral. -/
def x2Iq (C : X2Cell) : ℚ := cellIq C.v C.w C.lam C.P - (1 - 1 / 2 ^ C.e) * bIq C.v x2q C.lam C.P

/-- The per-cell Boolean check. -/
def x2CellOK (C : X2Cell) : Bool :=
  decide (0 < C.v) && decide (C.v ≤ C.w) && decide (C.w ≤ 1) && decide (C.v < 1) &&
    decide ((1 : ℚ) / 2 ≤ C.w ^ 4) &&
    (List.range (C.lam + 2)).all (fun k => decide ((C.P : ℤ) + 4 * k - 4 * C.lam + 4 ≠ 0)) &&
    decide ((C.P : ℤ) + 8 ≠ 0) && decide ((C.P : ℤ) - 4 * C.lam + 4 ≠ 0) &&
    decide ((C.P : ℤ) - 4 * C.lam + 8 ≠ 0) &&
    decide (C.e ≤ 2) && (decide (C.e = 0) || decide (C.v ≤ x2q)) &&
    decide (x2Iq C ≤ C.ub) &&
    decide (0 < 2 * C.ub * rsEx C.lu) && decide (|1 - crRed (2 * C.ub * rsEx C.lu) C.k| < 1) &&
    decide (crLnHi (2 * C.ub * rsEx C.lu) C.k C.n ≤ C.r) &&
    decide (C.r + ((C.P : ℚ) / 4 + C.lu) * crX0hi + C.e * crL2hi / 4 ≤ -x2R)

theorem x2Cells_ok_a : (x2Cells.take 20).all x2CellOK = true := by decide +kernel
theorem x2Cells_ok_b : ((x2Cells.drop 20).take 20).all x2CellOK = true := by decide +kernel
theorem x2Cells_ok_c : (x2Cells.drop 40).all x2CellOK = true := by decide +kernel

/-- **The certificate**: every cell passes. -/
theorem x2Cells_ok : x2Cells.all x2CellOK = true := by
  have h := x2Cells_ok_a
  have h2 := x2Cells_ok_b
  have h3 := x2Cells_ok_c
  rw [List.all_eq_true] at h h2 h3 ⊢
  intro C hC
  rw [← List.take_append_drop 20 x2Cells, List.mem_append] at hC
  rcases hC with hC | hC
  · exact h C hC
  · rw [← List.take_append_drop 20 (x2Cells.drop 20), List.mem_append] at hC
    rcases hC with hC | hC
    · exact h2 C hC
    · rw [List.drop_drop] at hC; exact h3 C hC

/-- A certified cell covers an original cell: smaller `m_lo`, larger or inactive cap. -/
def x2Link (C : X2Cell) (c : ℚ × ℚ) : Bool :=
  decide (C.v ^ 4 ≤ c.1) && (decide (c.2 ≤ C.w ^ 4) || decide (C.w = 1)) && decide (0 < c.2)

/-- **Every original cause cell is covered by a certified cell.** -/
theorem x2Link_all : cellsXCauseData.all (fun c => x2Cells.any (fun C => x2Link C c)) = true := by
  decide +kernel

/-- Multiplier ranges of the certified cells. -/
theorem x2Bounds : x2Cells.all (fun C => decide (C.lam ≤ 17) && decide (C.lu ≤ 3) && decide (C.P ≤ 30)) = true := by
  decide +kernel

end Census
end IIT
