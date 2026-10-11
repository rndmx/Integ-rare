/-
Census, B1 LTBetaHi: the split at `β = Lσ_N`.

`LT3HiStmt L C`: on B1 with `β ≥ L σ_N` some pair or triple reaches `β/4` (the LT3 band, W2 §8 + W8).
`ltBetaHi_of_LT2L_LT3`: `LTBetaHiStmt (1/4) C` from `LT2Stmt L C₁` (now proved for every `L ≥ 1`, `lt2_provedL`)
and `LT3HiStmt L C₂`. On `σ ≤ β < Lσ` the LT2 pair has `φ ≥ 3Lσ > β/4`.
-/
import IIT.Census.B1LT2LFinal
import IIT.Census.B1ForcedGSplit
import IIT.Census.B1ForcedGGlue

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- **The LT3 band** (`β ≥ L σ_N`). -/
def LT3HiStmt (L C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (B1w N s ∩ openCube N ∩ {w | L * sigN N ≤ betaW w ∧ ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 →
      phi (flipP s w) s S < 1 / 4 * betaW w}) ≤ ENNReal.ofReal (Real.exp (-(C * N)))

/-- **LTBetaHi from LT2 at level `L` and the LT3 band.** -/
theorem ltBetaHi_of_LT2L_LT3 {L C C₁ C₂ : ℝ} (hL : 0 < L) (h1 : C < C₁) (h2 : C < C₂) (hLT : LT2Stmt L C₁)
    (hHi : LT3HiStmt L C₂) : LTBetaHiStmt (1 / 4) C := by
  filter_upwards [hLT, hHi, g_union_rate h1 h2] with N hA hB hU s
  refine (measure_mono ?_).trans (hU _ _ (hA s) (hB s))
  rintro w ⟨⟨hw, hcube⟩, hlo, hall⟩
  by_cases hb : L * sigN N ≤ betaW w
  · exact Or.inr ⟨⟨hw, hcube⟩, hb, hall⟩
  · refine Or.inl ⟨not_le.1 hb, fun S hS => ?_⟩
    have := hall S (by omega) (by omega)
    have hσ : 0 < sigN N := by unfold sigN; positivity
    nlinarith [not_le.1 hb]

/-- **LTBetaHi from the LT3 band alone** (LT2 at level `L` is proved). -/
theorem ltBetaHi_of_LT3 {L C₂ : ℝ} (hL : 1 ≤ L) (h2 : 104 / 100 < C₂) (hHi : LT3HiStmt L C₂) :
    LTBetaHiStmt (1 / 4) (104 / 100) :=
  ltBetaHi_of_LT2L_LT3 (by linarith) (by norm_num) h2 (lt2_provedL L hL) hHi

/-- **Leaves 4, 5, 7 with LT2 discharged**: what remains is the LT3 band, `NatTier3Rest4`, and the `H_u` split. -/
theorem leaves457_of_LT3 {L C₂ lamU : ℝ} (hL : 1 ≤ L) (h2 : 104 / 100 < C₂) (hHi : LT3HiStmt L C₂)
    (hRest : NatTier3Rest4Stmt (104 / 100)) (hHu : NatLT3HuStmt lamU (104 / 100))
    (hNot : NatNotHuStmt lamU (104 / 100)) :
    (∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 4) ≤ ENNReal.ofReal (Real.exp (-(RfF * N)))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 5) ≤ ENNReal.ofReal (Real.exp (-(RfF * N)))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 7) ≤ ENNReal.ofReal (Real.exp (-(RfF * N)))) :=
  leaves457_of_G lt2_proved (ltBetaHi_of_LT3 hL h2 hHi) hRest hHu hNot

end Census
end IIT
