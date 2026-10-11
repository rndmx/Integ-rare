/-
Census, B1: **`b1PhiGoal` from the count alone**. `NatLT3HuStmt λ_u (103/100)` is proved for every `λ_u`
(`natLT3Hu_proved`, B1HuLFin), so `b1PhiGoal_of_two` leaves only `count_exp_famX` (as a hypothesis).
-/
import IIT.Census.B1HuLFin
import IIT.Census.B1MainFinal2

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

/-- **`B1PhiGoal` from the count `count_exp_famX`** (the only remaining hypothesis). -/
theorem b1PhiGoal_of_count
    (hfam : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide),
      ∀ f ∈ GoodFX N s r0 x σ,
        rowsOutM (sensRows s r0) {g | glueRows (sensRows s r0) f g ∈ BadFam N s r0 x σ}
          ≤ ENNReal.ofReal (Real.exp (-(cCnt * N)))) : B1PhiGoal :=
  b1PhiGoal_of_two one_pos (natLT3Hu_proved 1) hfam

end Census
end IIT
