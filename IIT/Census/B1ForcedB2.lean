/-
Census, B1 forced leaves 12..19, 21 (agent "forcedB"): STATEMENTS ONLY for the per-`(r0, x, σ)` joint bounds
(clearly marked `sorry`), and the PROVED reduction of each leaf to its joint bound plus leaf 8 (`far`) at rate
`RfF2 = 1.0107` (via `leaf_of_farSplit` and `farPart_of_joint` of `B1ForcedB1`).

Interface of every joint statement (W7 §4.4 / §7 rates are per `(r0, x, σ)` and include the `2^{-N}` of the
regime event): for far `r0`,
  `cubeM {RegEvX s r0 x σ ∧ ¬ field(r0)} ≤ e^{-RJ N} / 2^N`,  `RJ = 1.0108`.
-/
import IIT.Census.B1ForcedEX2
import IIT.Census.B1ForcedFJoint
import IIT.Census.B1ForcedFSRow
import IIT.Census.B1ForcedFPos

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- [W7 X_e nuS through s^x ≈ 1.068 float; effect side only]. PROVED (`B1ForcedFJoint.joint_nuTcF`). -/
theorem joint_nuTc : JointBound P0NuTc := joint_nuTcF
/-- [W7 X5 ≈ 1.41 float; cause side only].  **FALSE AS STATED** (`B1ForcedFJoint.x5_fails_on_regime`): at
`K' = {x}` the plus mean through `r0^x` is `(1 + y_{r0})/2` and the cause tilt forces
`Σ log(1 + y_{r0,i}) ≥ (log 2 - x0/2) N - slT/2 > 0.46 N`, so the field fails on (a.e.) every cause-regime
configuration.  The corrected field `P0X5F` (`x ∉ K'`, W7's "non-tc patterns") is PROVED (`joint_x5F`). -/
theorem joint_x5 : JointBound P0X5 := joint_x5F
/-- [W7 posNear_X ≈ 1.33 float]. PROVED (`B1ForcedFPos.joint_posNearF`, certified rate `≥ 1.039`). -/
theorem joint_posNear : JointBound P0PosNear := joint_posNearF
/-- [W7 X2 1.075556 cert, 60 cells]. -/
theorem joint_x2 : JointBound P0X2 := joint_x2E
/-- [W7 sRow(i), ≥ 1.21; window of width `e^{N/100} σ_N` for one entry of row `s`]. PROVED
(`B1ForcedFSRow.joint_sRowMuF`, rate `R0 + x0 - 1/100`). -/
theorem joint_sRowMu : JointBound P0SRowMu := joint_sRowMuF

/-! ### The leaves from the joint bounds (proved modulo the `sorry`s above and leaf 8 at `RfF2`) -/

theorem leaf_of_joint (P0 : ∀ N, State N → State N → Param N → Fin N → XSide → Prop) (hj : JointBound P0)
    (h8 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (bField N s (fFar N s)) ≤ ENNReal.ofReal (Real.exp (-(RfF2 * N)))) :
    ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (bField N s (fun w x σ => P0 N s (tcRow w) w x σ)) ≤
        ENNReal.ofReal (Real.exp (-(RfF * N))) :=
  leaf_of_farSplit P0 h8 (farPart_of_joint P0 hj)

section
variable (h8 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (bField N s (fFar N s)) ≤ ENNReal.ofReal (Real.exp (-(RfF2 * N))))
include h8

theorem leaf13 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (forcedBad N s 13) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [leaf_of_joint P0NuTc joint_nuTc h8] with N h s; exact h s
theorem leaf14 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (forcedBad N s 14) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [leaf_of_joint P0X5 joint_x5 h8] with N h s; exact h s
theorem leaf15 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (forcedBad N s 15) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [leaf_of_joint P0PosNear joint_posNear h8] with N h s; exact h s
theorem leaf17 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (forcedBad N s 17) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [leaf_of_joint P0X2 joint_x2 h8] with N h s; exact h s
theorem leaf19 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (forcedBad N s 19) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [leaf_of_joint P0SRowMu joint_sRowMu h8] with N h s; exact h s

end

end Census
end IIT
