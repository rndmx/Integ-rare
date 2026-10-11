/-
Census, B1 leaf `B1_forcedX` from the two remaining natural-regime statements (W12):
`NatTier3Rest6Stmt (1039/1000)` (Tier 3 residual without `lowE`) and `NatLT3HuStmt λ_u (103/100)`.
Everything else is proved: LT2 (`lt2_proved`), LTβ-high (`ltBetaHi_final`), `natTier3_of_rest6`, `natNotHu_of`,
and the forcing assembly `B1_forcedX_J` (leaves 4, 5, 7).
-/
import IIT.Census.B1NotHu
import IIT.Census.B1LTHiFin
import IIT.Census.B1LT2Final
import IIT.Census.B1ForcedHFinal

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

/-- LT2 at any rate `≤ 1.04`. -/
lemma lt2_at {C : ℝ} (hC : C ≤ 104 / 100) : LT2Stmt 1 C := LT2Stmt_mono hC lt2_proved

/-- LTβ at any rate `< 1.04`. -/
lemma ltBeta_at {C : ℝ} (hC : C < 104 / 100) : LTBetaStmt (1 / 4) C :=
  ltBeta_of_LT2_hi hC hC lt2_proved ltBetaHi_final

/-- **`B1_forcedX` from the two remaining Nat statements.** -/
theorem B1_forcedX_of_nat {lamU : ℝ} (hl : 0 < lamU) (hRest6 : NatTier3Rest6Stmt (1039 / 1000))
    (hHu : NatLT3HuStmt lamU (103 / 100)) :
    ∀ᶠ N in atTop, ∀ s : State N,
      cubeM N (B1w N s \ {w | ForcedX N s w}) ≤ ENNReal.ofReal (3 * Real.exp (-(RbadX * N))) := by
  have hR : RfD = 102 / 100 := rfl
  -- Tier 3 at 1.035 and at RfD
  have hT3a : NatTier3Stmt (1035 / 1000) :=
    natTier3_of_rest6 (by norm_num) (by norm_num) hRest6 (lt2_at (by norm_num)) (ltBeta_at (by norm_num))
  have hT3 : NatTier3Stmt RfD :=
    natTier3_of_rest6 (by rw [hR]; norm_num) (by norm_num) hRest6 (lt2_at (by norm_num)) (ltBeta_at (by norm_num))
  -- NatNotHu at 1.03, NatLT3 at RfD
  have hNot : NatNotHuStmt lamU (103 / 100) :=
    natNotHu_of hl (by norm_num) (by norm_num) hT3a (ltBeta_at (by norm_num)) (lt2_at (by norm_num))
  have hL3 : NatLT3Stmt RfD := natLT3_of_split (by rw [hR]; norm_num) (by rw [hR]; norm_num) hHu hNot
  have hLT2 : LT2Stmt 1 RfD := lt2_at (by rw [hR]; norm_num)
  have hLTb : LTBetaStmt (1 / 4) RfD := ltBeta_at (by rw [hR]; norm_num)
  exact B1_forcedX_J (leaf4_of_LT2 hLT2) (leaf5_of_LTBeta hLTb) (leaf7_of hT3 hL3 hLT2 hLTb)

end Census
end IIT
