/-
Census, B1 forced leaf 18 (agent "forcedF"): kernel check of the two-failure records of side C.
-/
import IIT.Census.B1ForcedFTwoCertDef
import IIT.Census.B1ForcedFTwoDataC
import IIT.Census.CertRatesDataX

namespace IIT
namespace Census

theorem tfRecsC_ok_a : (tfRecsC.take 90).all tfOK = true := by decide +kernel
theorem tfRecsC_ok_b : (tfRecsC.drop 90).all tfOK = true := by decide +kernel

theorem tfRecsC_ok : tfRecsC.all tfOK = true := by
  rw [← List.take_append_drop 90 tfRecsC, List.all_append, tfRecsC_ok_a, tfRecsC_ok_b]
  rfl

/-- Every record is linked to its cells. -/
theorem tfRecsC_link : tfRecsC.all tfLinkC = true := by decide +kernel

/-- Every overlapping pair of original cells has a record. -/
theorem tfRecsC_cover : cellsXCauseData.all (fun c => cellsXCauseData.all (fun c' => decide (c.2 < c'.1) ||
    decide (c'.2 < c.1) || tfRecsC.any (fun R => decide (R.c1 = c) && decide (R.c2 = c')))) = true := by
  decide +kernel

end Census
end IIT
