/-
Census, B1: **final assembly of `NatLT3HuStmt` and `B1PhiGoal`**.

The case split (s = tc via `natTc_rareX`; s ∈ Sp \ {tc} via `natSp_rareX`; light s with
β < L σ_N via LT2(L) + Tier 3 + B1 (`hlb_no_pair`); light s with β ≥ L σ_N via `lt3HuL_final`)
is carried out in `IIT.Census.natLT3Hu_proved` (B1HuLFin). This file records the λ_u = 1
instance and the reduction of `B1PhiGoal` to the count `count_exp_famX`, in the namespace
`IIT.Census.HuFinal` (to avoid clashing with the B1HuLFin name).
-/
import IIT.Census.B1HuLMain

namespace IIT
namespace Census
namespace HuFinal

open MeasureTheory Filter Topology Finset

/-- **`NatLT3HuStmt 1 (103/100)`, proved.** -/
theorem natLT3Hu_proved : NatLT3HuStmt 1 (103 / 100) :=
  IIT.Census.natLT3Hu_proved 1

/-- **`B1PhiGoal` from the count `count_exp_famX`** (stated exactly as `b1PhiGoal_of_two` expects). -/
theorem b1PhiGoal_of_famX
    (hfam : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide),
      ∀ f ∈ GoodFX N s r0 x σ,
        rowsOutM (sensRows s r0) {g | glueRows (sensRows s r0) f g ∈ BadFam N s r0 x σ}
          ≤ ENNReal.ofReal (Real.exp (-(cCnt * N)))) : B1PhiGoal :=
  b1PhiGoal_of_two one_pos natLT3Hu_proved hfam

end HuFinal
end Census
end IIT
