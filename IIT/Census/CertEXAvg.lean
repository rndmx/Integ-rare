/-
Census, B1 lower bound: kernel checks of the averages of checks T and L (data `CertEXAvgData`).
-/
import IIT.Census.CertEX
import IIT.Census.CertEXAvgData

set_option maxRecDepth 100000

namespace IIT
namespace Census

def exPtOK (p : ℚ × ℤ × ℚ × ℚ) : Bool :=
  (decide (0 < p.1) && decide (|1 - crRed p.1 p.2.1| < 1) && decide (p.2.2.1 ≤ crLnLo p.1 p.2.1 40)) &&
    (decide (0 < p.1) && decide (|1 - crRed p.1 p.2.1| < 1) && decide (crLnHi p.1 p.2.1 40 ≤ p.2.2.2))

def exYp (sa : ℕ) : ℚ × ℤ × ℚ × ℚ := exYpts.getD sa (1, 0, 0, 0)
def exXp (j : ℕ) : ℚ × ℤ × ℚ × ℚ := exXpts.getD j (1, 0, 0, 0)

/-- Upper / lower bounds of the strip average of `-log y`. -/
def exBTup (sa : ℕ) : ℚ :=
  -((exYp (sa + 1)).1 * (exYp (sa + 1)).2.2.1 - (exYp sa).1 * (exYp sa).2.2.2 - (exYp (sa + 1)).1 + (exYp sa).1) / exHy
def exBTlo (sa : ℕ) : ℚ :=
  -((exYp (sa + 1)).1 * (exYp (sa + 1)).2.2.2 - (exYp sa).1 * (exYp sa).2.2.1 - (exYp (sa + 1)).1 + (exYp sa).1) / exHy
/-- Upper bound of the interval average of `-log x` on `[x_j, x_{j+1}]`. -/
def exBLup (j : ℕ) : ℚ :=
  -((exXp (j + 1)).1 * (exXp (j + 1)).2.2.1 - (exXp j).1 * (exXp j).2.2.2 - (exXp (j + 1)).1 + (exXp j).1) /
    ((exXp (j + 1)).1 - (exXp j).1)

theorem exYpts_ok : exYpts.all exPtOK = true := by decide +kernel
theorem exXpts_ok : exXpts.all exPtOK = true := by decide +kernel
theorem exYpts_len : exYpts.length = 41 := by decide +kernel
theorem exXpts_len : exXpts.length = 201 := by decide +kernel
theorem exYpts_val : (List.range 41).all (fun sa => decide ((exYp sa).1 = exF + sa * exHy)) = true := by
  decide +kernel
theorem exXpts_inc : (List.range 200).all (fun j => decide ((exXp j).1 < (exXp (j + 1)).1)) = true := by
  decide +kernel

theorem exXpts_range : (List.range 201).all (fun j => decide (1 / 2 < (exXp j).1) && decide ((exXp j).1 ≤ 1)) = true := by
  decide +kernel

theorem exSIdx_len : exSIdx.length = 400 := by decide +kernel

/-- Each row-`s` cell is its upper interval or the mirror of it. -/
def exSIdxOK (C : EXSCell) (j : ℕ) : Bool :=
  decide (j < 200) && ((decide (C.x0 = (exXp j).1) && decide (C.x1 = (exXp (j + 1)).1)) ||
    (decide (C.x0 = 1 - (exXp (j + 1)).1) && decide (C.x1 = 1 - (exXp j).1)))

theorem exSIdx_ok : (exSCells.zip exSIdx).all (fun p => exSIdxOK p.1 p.2) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem exT_up : (exPCells.map fun C => C.a * exBTup C.sa).sum ≤ exETup := by decide +kernel
set_option maxHeartbeats 0 in
theorem exT_lo : exETlo ≤ (exPCells.map fun C => C.a * exBTlo C.sa).sum := by decide +kernel
set_option maxHeartbeats 0 in
theorem exL_up : ((exSCells.zip exSIdx).map fun p => p.1.a * exBLup p.2).sum ≤ exELup := by decide +kernel

/-- The lower row-`s` cells (`x1 ≤ 1/2`) carry mass exactly `1/2`. -/
theorem exS_lower_mass : (exSCells.map fun C => if C.x1 ≤ 1 / 2 then C.a else 0).sum = 1 / 2 := by
  decide +kernel

/-- The margins: `E_T + 10⁻⁶·(1/2) < x0` and `E_L + 4·10⁻⁷ < E_T,lo`. -/
theorem exT_margin : exETup + 1 / (2 * 10 ^ 6) < crX0lo := by decide +kernel
theorem exL_margin : exELup + 4 / 10 ^ 7 < exETlo := by decide +kernel

end Census
end IIT
