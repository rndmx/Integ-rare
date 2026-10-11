/-
Census, B1: **`B1PhiGoal`, proved** (no hypotheses), and the corrected count `CountX3Stmt`.
-/
import IIT.Census.B1CountFinalPre
import IIT.Census.B1CntRet
import IIT.Census.B1CntCoinMean

namespace IIT
namespace Census

/-- **The count** (Proposition "count" of the paper): given good F-data, the fresh rows yield fewer
than `2^(N/8) + 2N` certified distinctions with probability at most `e^{-N/500}`. -/
theorem countX3_proved : CountX3Stmt :=
  countX3_of_wps causeDet_proved sysCause_proved effDet_proved sysEff_proved famBig_proved
    freshProb_proved retMarkov_proved
    (meanY_of_tools gc_proved mills_proved subGauss_proved entrySumLaw_proved)
    (cheb_of_meanY gc_proved entrySumLaw_proved)

/-- **Forcing** (Proposition "forcing" of the paper), with its two natural-regime inputs discharged. -/
theorem B1_forcedX_proved : ∀ᶠ N in Filter.atTop, ∀ s : State N,
    cubeM N (B1w N s \ {w | ForcedX N s w}) ≤ ENNReal.ofReal (3 * Real.exp (-(RbadX * N))) :=
  B1_forcedX_of_nat one_pos natTier3Rest6_proved HuFinal.natLT3Hu_proved

theorem b1PhiGoal_proved : B1PhiGoal :=
  b1PhiGoal_of_wp5 retMarkov_proved meanY_of_tools

end Census
end IIT
