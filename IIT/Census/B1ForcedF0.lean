/-
Census, B1 forced joint bounds: the per-`(r0, x, σ)` field predicates and the `JointBound` interface
(moved from `B1ForcedB2` so that the proofs in `B1ForcedF*` can be imported back into `B1ForcedB2`).
-/
import IIT.Census.B1ForcedB1

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-! ### Fields with an explicit anchor row `r0` (definitionally the `B1ForcedSkel` fields at `r0 = tcRow w`) -/

def P0NuS (N : ℕ) (s : State N) : State N → Param N → Fin N → XSide → Prop := fun r0 w _ _ =>
  ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 2 →
    ∑ i, Real.log (max (2 * b1CutMeanS w s r0 K' i) 1) ≤ 23 / 50 * (N : ℝ)
def P0NuTc (N : ℕ) (_s : State N) : State N → Param N → Fin N → XSide → Prop := fun r0 w _ σ =>
  σ = .effect → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 3 →
    ∑ i, Real.log (max (2 * b1CutMeanPlus w r0 K' i) 1) ≤ 23 / 50 * (N : ℝ)
def P0X5 (N : ℕ) (_s : State N) : State N → Param N → Fin N → XSide → Prop := fun r0 w x σ =>
  σ = .cause → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 3 → x ∉ K' →
    ∑ i, Real.log (max (2 * b1CutMeanPlus w (flipAt x r0) K' i) 1) ≤ 23 / 50 * (N : ℝ)
def P0PosNear (N : ℕ) (_s : State N) : State N → Param N → Fin N → XSide → Prop := fun r0 w x σ =>
  ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 4 → (σ = .cause → K' ≠ {x}) →
    (N : ℝ) / 25 ≤ ∑ i, b1CutGX w r0 K' i
def P0X1 (N : ℕ) (s : State N) : State N → Param N → Fin N → XSide → Prop := fun r0 w x σ =>
  σ = .cause → -((N : ℝ) / 2000) ≤
    ∑ j ∈ univ.erase x, min (lamX w s r0 x .cause j) (Real.log (clamp01 (w r0 j) / cX))
def P0X2 (N : ℕ) (_s : State N) : State N → Param N → Fin N → XSide → Prop := fun r0 w x σ =>
  σ = .cause → N ≤ 4 * (NegX w r0 x).card
def P0SRowMu (N : ℕ) (s : State N) : State N → Param N → Fin N → XSide → Prop := fun _ w _ _ =>
  ∀ h : (univ : Finset (Fin N)).Nonempty,
    Real.exp ((N : ℝ) / 100) * sigN N ≤ univ.inf' h (fun k => xE w s k - 1 / 2)
def P0SRowR (N : ℕ) (s : State N) : State N → Param N → Fin N → XSide → Prop := fun r0 w _ _ =>
  ∑ r ∈ (sensRows s r0).erase s, ∏ k, pTe w s r k ≤ sigN N

/-! ### The joint bounds (STATEMENTS, `sorry`): W7 §4.4/§7 certified or float rates in brackets -/

/-- `JointBound P0`: the per-`(r0, x, σ)` interface of `farPart_of_joint`. -/
def JointBound (P0 : ∀ N, State N → State N → Param N → Fin N → XSide → Prop) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide), N ≤ 3 * ham r0 s →
    cubeM N {w | RegEvX N s r0 x σ w ∧ ¬ P0 N s r0 w x σ} ≤ ENNReal.ofReal (Real.exp (-(RJ * N)) / 2 ^ N)

end Census
end IIT
