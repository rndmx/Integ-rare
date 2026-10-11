/-
Census, B1, W14 work package WP4 (fresh K-free events): assembly.

The ten per-field bounds `FreshFieldProb FE·X (1/180)` are proved in
* `B1CntFreshA` (`freshFE0`; generic tools `lowerTail_nonneg`, `multChernoff_lower`, `iIndepFun_pi_blocks`),
* `B1CntFreshB` (`freshFE1`, `freshFE2`, `freshFE6`),
* `B1CntFreshC` (`freshFE4a`, `freshFE4b`, `freshFE7b`),
* `B1CntFreshD` (`freshFE7a`, `freshFE3`),
* `B1CntFreshE` (`freshFE5`);
`B1CntGlue3.freshProb_of_fields` combines them into **`FreshProbStmt`**.  No `sorry`.
-/
import IIT.Census.B1CntFreshE

namespace IIT
namespace Census

/-- **WP4 main**: the fresh event fails with probability `≤ e^{-N/200}`. -/
theorem freshProb_proved : FreshProbStmt :=
  freshProb_of_fields freshFE0 freshFE1 freshFE2 freshFE3 freshFE4a freshFE4b freshFE5 freshFE6
    freshFE7a freshFE7b

end Census
end IIT

#print axioms IIT.Census.freshProb_proved
#print axioms IIT.Census.freshFE0
#print axioms IIT.Census.freshFE1
#print axioms IIT.Census.freshFE2
#print axioms IIT.Census.freshFE3
#print axioms IIT.Census.freshFE4a
#print axioms IIT.Census.freshFE4b
#print axioms IIT.Census.freshFE5
#print axioms IIT.Census.freshFE6
#print axioms IIT.Census.freshFE7a
#print axioms IIT.Census.freshFE7b
#print axioms IIT.Census.lowerTail_nonneg
#print axioms IIT.Census.multChernoff_lower
