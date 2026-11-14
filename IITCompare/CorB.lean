/-
Corollary B: `P(C₂ | C₄) → 1` for every sequence of states, from the rate
`P(not C₂) ≤ e^{-2N}` (IIT2, `volumeReal_not_wholeIsMainComplex_le`) and
`P(C₄) = P(B1) ≥ e^{-1.0085 N}` (Integ-rare, `B1_lowerX_final` + `cubeM_B1w`).
-/
import IITCompare.CorA
import IIT.Census.B1Final
import IIT.Census.B1Defs

namespace IITCompare

open MeasureTheory Filter Topology

variable {N : ℕ}

lemma vol_ne_top_of_sub_cube {X : Set (IIT.Census.Param N)} (h : X ⊆ IIT.Census.cube N) :
    volume X ≠ ⊤ :=
  ne_top_of_le_ne_top (b := volume (IIT.Census.cube N)) (by simp [volume_cube_IIT])
    (measure_mono h)

/-- **Corollary B**: `P(C₂ ∩ C₄) / P(C₄) → 1`. -/
theorem tendsto_prob_C2_given_C4 (s : ∀ N, IIT2.State N) :
    Tendsto (fun N => (volume (C2 N (s N) ∩ IIT.Census.caseB1 N (s N))).toReal /
      (volume (IIT.Census.caseB1 N (s N))).toReal) atTop (𝓝 1) := by
  set c : ℝ := 2 - IIT.Census.RLBX
  have hc : 0 < c := by simp only [c, IIT.Census.RLBX]; norm_num
  have hlim : Tendsto (fun N : ℕ => 1 - Real.exp (-c * N)) atTop (𝓝 1) := by
    have := Real.tendsto_exp_atBot.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg
      (show -c < 0 by linarith))
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub this
    rw [sub_zero] at h2
    exact h2
  have hB1 : ∀ᶠ N : ℕ in atTop,
      Real.exp (-(IIT.Census.RLBX * N)) ≤ (volume (IIT.Census.caseB1 N (s N))).toReal := by
    filter_upwards [IIT.Census.B1_lowerX_final] with N h
    have := h (s N)
    rwa [IIT.Census.cubeM_B1w] at this
  have hlow : ∀ᶠ N : ℕ in atTop, 1 - Real.exp (-c * N) ≤
      (volume (C2 N (s N) ∩ IIT.Census.caseB1 N (s N))).toReal /
        (volume (IIT.Census.caseB1 N (s N))).toReal := by
    filter_upwards [hB1, IIT2.volumeReal_not_wholeIsMainComplex_le s] with N hA hD
    set A := IIT.Census.caseB1 N (s N)
    set D := {z | z ∈ IIT.Census.cube N ∧
      ¬ IIT2.WholeIsMainComplex (IIT2.tpmOf (swapE N z)) (s N)}
    have hAc : A ⊆ IIT.Census.cube N := fun z hz => hz.1
    have hDc : D ⊆ IIT.Census.cube N := fun z hz => hz.1
    have hcov : A ⊆ (C2 N (s N) ∩ A) ∪ D := by
      intro z hz
      by_cases h : IIT2.WholeIsMainComplex (IIT2.tpmOf (swapE N z)) (s N)
      · exact Or.inl ⟨⟨hz.1, h⟩, hz⟩
      · exact Or.inr ⟨hz.1, h⟩
    have h1 : (volume A).toReal ≤ (volume (C2 N (s N) ∩ A)).toReal + (volume D).toReal := by
      have := (measure_mono hcov).trans (measure_union_le (μ := volume) (C2 N (s N) ∩ A) D)
      have h' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
        ⟨vol_ne_top_of_sub_cube (Set.inter_subset_right.trans hAc), vol_ne_top_of_sub_cube hDc⟩) this
      rwa [ENNReal.toReal_add (vol_ne_top_of_sub_cube (Set.inter_subset_right.trans hAc))
        (vol_ne_top_of_sub_cube hDc)] at h'
    have hDr : (volume D).toReal ≤ Real.exp (-(2 * N)) := by
      simp only [D]; rw [volume_cube_not_C2]; exact hD
    have hApos : 0 < (volume A).toReal := lt_of_lt_of_le (Real.exp_pos _) hA
    have hq : (volume D).toReal / (volume A).toReal ≤ Real.exp (-c * N) := by
      rw [div_le_iff₀ hApos]
      have : Real.exp (-c * N) * Real.exp (-(IIT.Census.RLBX * N)) = Real.exp (-(2 * N)) := by
        rw [← Real.exp_add]; congr 1; simp only [c]; ring
      have h2 := mul_le_mul_of_nonneg_left hA (Real.exp_pos (-c * N)).le
      linarith
    rw [le_div_iff₀ hApos]
    rw [div_le_iff₀ hApos] at hq
    nlinarith
  have hup : ∀ᶠ N in atTop, (volume (C2 N (s N) ∩ IIT.Census.caseB1 N (s N))).toReal /
      (volume (IIT.Census.caseB1 N (s N))).toReal ≤ 1 := by
    refine Eventually.of_forall fun N => div_le_one_of_le₀ ?_ ENNReal.toReal_nonneg
    exact ENNReal.toReal_mono (vol_ne_top_of_sub_cube fun z hz => hz.1)
      (measure_mono Set.inter_subset_right)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds hlow hup

end IITCompare

#print axioms IITCompare.tendsto_prob_C2_given_C4
