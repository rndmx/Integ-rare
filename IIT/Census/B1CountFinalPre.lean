/-
Census, B1: the final assembly of `B1PhiGoal`, with WP5 (retention Markov, coin) as the only hypotheses.
-/
import IIT.Census.B1NewLeaf3
import IIT.Census.B1CntGlue3
import IIT.Census.B1CntCauseFin
import IIT.Census.B1CntEffOthers
import IIT.Census.B1CntFresh
import IIT.Census.B1CntCovMain
import IIT.Census.B1CntCovFam
import IIT.Census.B1CntTool4
import IIT.Census.B1CntTool5

namespace IIT
namespace Census

theorem b1PhiGoal_of_wp5 (hR : RetMarkovStmt)
    (hMT : GCStmt → MillsStmt → SubGaussStmt → EntrySumLawStmt → MeanYStmt) : B1PhiGoal :=
  b1PhiGoal_of_countX3 (countX3_of_wps causeDet_proved sysCause_proved effDet_proved sysEff_proved
    famBig_proved freshProb_proved hR (hMT gc_proved mills_proved subGauss_proved entrySumLaw_proved)
    (cheb_of_meanY gc_proved entrySumLaw_proved))

end Census
end IIT
