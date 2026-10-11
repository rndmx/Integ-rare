/-
Census, B1 forced leaf 18 (agent "forcedF"): kernel check of the two-failure records of side E.
-/
import IIT.Census.B1ForcedFTwoCertDef
import IIT.Census.B1ForcedFTwoDataE
import IIT.Census.CertRatesDataX

namespace IIT
namespace Census

theorem tfRecsE_ok_a : (tfRecsE.take 90).all tfOK = true := by decide +kernel
theorem tfRecsE_ok_b : (tfRecsE.drop 90).all tfOK = true := by decide +kernel

theorem tfRecsE_ok : tfRecsE.all tfOK = true := by
  rw [← List.take_append_drop 90 tfRecsE, List.all_append, tfRecsE_ok_a, tfRecsE_ok_b]
  rfl

/-- Every record is linked to its cells. -/
theorem tfRecsE_link : tfRecsE.all tfLinkE = true := by decide +kernel

/-- Every overlapping pair of original cells has a record. -/
theorem tfRecsE_cover : cellsXEffectData.all (fun c => cellsXEffectData.all (fun c' => decide (c.2 < c'.1) ||
    decide (c'.2 < c.1) || tfRecsE.any (fun R => decide (R.c1 = c) && decide (R.c2 = c')))) = true := by
  decide +kernel

end Census
end IIT
