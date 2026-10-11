/-
Census, B1: **`b1PhiGoal` from the two remaining statements**: `NatLT3HuStmt λ_u (103/100)` and the count
(`count_exp_famX` as a hypothesis). `NatTier3Rest6Stmt` is now proved (`natTier3Rest6_proved`).
-/
import IIT.Census.B1MainFinal
import IIT.Census.B1Rest6Final

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

theorem b1PhiGoal_of_two {lamU : ℝ} (hl : 0 < lamU) (hHu : NatLT3HuStmt lamU (103 / 100))
    (hfam : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide),
      ∀ f ∈ GoodFX N s r0 x σ,
        rowsOutM (sensRows s r0) {g | glueRows (sensRows s r0) f g ∈ BadFam N s r0 x σ}
          ≤ ENNReal.ofReal (Real.exp (-(cCnt * N)))) : B1PhiGoal :=
  b1PhiGoal_of_leaves hl natTier3Rest6_proved hHu hfam

end Census
end IIT
