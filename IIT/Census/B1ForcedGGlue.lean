/-
Census, B1 forced leaves 4, 5, 7: glue for the orchestrator, agent "forcedG".

`leaves457_of_G`: the three leaves at rate `RfF` (the form `B1_forcedX_partial` takes) from FIVE statements at rate
`104/100`:
* `LT2Stmt 1 R`             (W2 §9, Theorem LT2 at `L' = 1`);
* `LTBetaHiStmt (1/4) R`    (on B1 with `β ≥ σ_N`, some pair/triple reaches `β/4`);
* `NatTier3Rest4Stmt R`     (residual Tier-3 event: SpreadGood (5D), SmallCutGood (7D, 1 ≤ |K| < D), SpreadLarge,
                             all at `tcRow` and at every maximal effect state, plus `λᵉ_min ≥ 1/N²`);
* `NatLT3HuStmt λu R`       (LT3 under `H_u` in the natural regime);
* `NatNotHuStmt λu R`       (`bNat ∩ ¬H_u` rare, W11).
-/
import IIT.Census.B1ForcedGTie

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

lemma g_rate_le {C C' : ℝ} (h : C ≤ C') (N : ℕ) :
    ENNReal.ofReal (Real.exp (-(C' * N))) ≤ ENNReal.ofReal (Real.exp (-(C * N))) := by
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith))

lemma LT2Stmt_mono {L C C' : ℝ} (h : C ≤ C') (hs : LT2Stmt L C') : LT2Stmt L C := by
  filter_upwards [hs] with N hN s using (hN s).trans (g_rate_le h N)

lemma LTBetaStmt_mono {c C C' : ℝ} (h : C ≤ C') (hs : LTBetaStmt c C') : LTBetaStmt c C := by
  filter_upwards [hs] with N hN s using (hN s).trans (g_rate_le h N)

lemma NatTier3Rest4Stmt_mono {C C' : ℝ} (h : C ≤ C') (hs : NatTier3Rest4Stmt C') : NatTier3Rest4Stmt C := by
  filter_upwards [hs] with N hN s using (hN s).trans (g_rate_le h N)

/-- **Leaves 4, 5, 7 from the five G-statements.** -/
theorem leaves457_of_G {lamU : ℝ}
    (hLT2 : LT2Stmt 1 (104 / 100)) (hHi : LTBetaHiStmt (1 / 4) (104 / 100))
    (hRest : NatTier3Rest4Stmt (104 / 100)) (hHu : NatLT3HuStmt lamU (104 / 100))
    (hNot : NatNotHuStmt lamU (104 / 100)) :
    (∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 4) ≤ ENNReal.ofReal (Real.exp (-(RfF * N)))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 5) ≤ ENNReal.ofReal (Real.exp (-(RfF * N)))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 7) ≤ ENNReal.ofReal (Real.exp (-(RfF * N)))) := by
  have hR1 : RfD < 103 / 100 := by unfold RfD; norm_num
  have hLTb : LTBetaStmt (1 / 4) (103 / 100) :=
    ltBeta_of_LT2_hi (by norm_num) (by norm_num) hLT2 hHi
  have hT3 : NatTier3Stmt RfD :=
    natTier3_of_rest4 hR1 (NatTier3Rest4Stmt_mono (by norm_num) hRest) hLTb
  have hL3 : NatLT3Stmt RfD := natLT3_of_split (by unfold RfD; norm_num) (by unfold RfD; norm_num) hHu hNot
  have hLT2' : LT2Stmt 1 RfD := LT2Stmt_mono (by unfold RfD; norm_num) hLT2
  have hLTb' : LTBetaStmt (1 / 4) RfD := LTBetaStmt_mono hR1.le hLTb
  exact ⟨leaf4_of_LT2 hLT2', leaf5_of_LTBeta hLTb', leaf7_of hT3 hL3 hLT2' hLTb'⟩

end Census
end IIT
