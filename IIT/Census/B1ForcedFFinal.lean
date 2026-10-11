/-
Census, B1 leaf `B1_forcedX` (agent "forcedF"): glue of the round-4 results into `B1_forcedX_partial`.

Discharged here: `h8` (`leafF8`), `h18` (`leafF18`), `jNuTc` (`joint_nuTcF`), `jPosNear` (`joint_posNearF`),
`jSRowMu` (`joint_sRowMuF`), `jX2` (`joint_x2E`, round 3), and `jNuS` from the sub-leaf `NuSxStmt`
(`joint_nuS_of`).  Still hypotheses: leaves 4, 5, 7, 9 (other agents), `NuSxStmt`, `JointBound P0X5`
(FALSE as stated, see `x5_fails_on_regime`; the corrected `P0X5F` is proved by `joint_x5F`), `JointBound P0X1`,
`JointBound P0SRowR`.
-/
import IIT.Census.B1ForcedC

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

theorem B1_forcedX_F
    (h4 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 4) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))))
    (h5 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 5) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))))
    (h7 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 7) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))))
    (h9 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 9) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))))
    (hNuSx : NuSxStmt) (jX5 : JointBound P0X5) (jX1 : JointBound P0X1) (jSRowR : JointBound P0SRowR) :
    ∀ᶠ N in atTop, ∀ s : State N,
      cubeM N (B1w N s \ {w | ForcedX N s w}) ≤ ENNReal.ofReal (3 * Real.exp (-(RbadX * N))) :=
  B1_forcedX_partial leafF8 h4 h5 h7 h9 leafF18 (joint_nuS_of hNuSx) joint_nuTcF jX5 joint_posNearF jX1
    joint_x2E joint_sRowMuF jSRowR

end Census
end IIT

#print axioms IIT.Census.B1_forcedX_F
