/-
Census, B1 leaf `B1_forcedX`: assembly after the 2026-10-07 round.

Discharged since `B1ForcedFFinal`: leaf 9 (`leaf9_of_far leafF8`), `NuSxStmt` (`nuSx_proved`, B1NuSx),
`JointBound P0X5` (field corrected to `x ∉ K'`, `joint_x5 = joint_x5F`), `JointBound P0X1` (`joint_x1_proved`, B1X1).
Still hypotheses: leaves 4, 5, 7 and `JointBound P0SRowR`.
-/
import IIT.Census.B1ForcedFFinal
import IIT.Census.B1ForcedDRet
import IIT.Census.B1NuSx
import IIT.Census.B1X1
import IIT.Census.B1SRowR
import IIT.Census.B1SxEff

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

theorem B1_forcedX_H
    (h4 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 4) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))))
    (h5 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 5) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))))
    (h7 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 7) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))))
    (jSRowR : JointBound P0SRowR) :
    ∀ᶠ N in atTop, ∀ s : State N,
      cubeM N (B1w N s \ {w | ForcedX N s w}) ≤ ENNReal.ofReal (3 * Real.exp (-(RbadX * N))) :=
  B1_forcedX_F h4 h5 h7 (leaf9_of_far leafF8) nuSx_proved joint_x5 joint_x1_proved jSRowR

/-- **`B1_forcedX` with `sRowR` reduced to the effect `s^x` row** (`joint_sRowR_of`, B1SRowR). -/
theorem B1_forcedX_I
    (h4 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 4) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))))
    (h5 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 5) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))))
    (h7 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 7) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))))
    (hSx : SxEffStmt) :
    ∀ᶠ N in atTop, ∀ s : State N,
      cubeM N (B1w N s \ {w | ForcedX N s w}) ≤ ENNReal.ofReal (3 * Real.exp (-(RbadX * N))) :=
  B1_forcedX_H h4 h5 h7 (joint_sRowR_of hSx)

/-- **`B1_forcedX` from leaves 4, 5, 7 only** (`sRowR` fully proved: `joint_sRowR_of sxEff_proved`). -/
theorem B1_forcedX_J
    (h4 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 4) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))))
    (h5 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 5) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))))
    (h7 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 7) ≤ ENNReal.ofReal (Real.exp (-(RfF * N)))) :
    ∀ᶠ N in atTop, ∀ s : State N,
      cubeM N (B1w N s \ {w | ForcedX N s w}) ≤ ENNReal.ofReal (3 * Real.exp (-(RbadX * N))) :=
  B1_forcedX_I h4 h5 h7 sxEff_proved

end Census
end IIT

#print axioms IIT.Census.B1_forcedX_H
#print axioms IIT.Census.B1_forcedX_I
#print axioms IIT.Census.B1_forcedX_J
