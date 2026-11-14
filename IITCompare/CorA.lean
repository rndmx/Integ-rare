/-
Corollary A: `P(C₄ | C₂) → 0` for every sequence of states, where `C₄ = caseB1 N s` (the whole
system is an IIT 4.0 complex) and `C₂` = the whole system is the IIT 2.0 main complex.
-/
import IITCompare.Bridge
import IIT.Census.UnivZero
import IIT.Census.B1Target

namespace IITCompare

open MeasureTheory Filter Topology

variable {N : ℕ}

lemma volume_cube_IIT (N : ℕ) : volume (IIT.Census.cube N) = 1 := by
  have := IIT.Census.volume_cube_inter (N := N) Set.univ
  rw [Set.inter_univ] at this
  rw [this]; exact measure_univ

/-- `C₄ ⊆ {φ_s(univ) > 0}`, from Integ's definitions (`IsComplex` at the universe and
`sysPhi_eq_zero_of_card_le_one` for a singleton competitor). -/
lemma caseB1_subset_univPos (hN : 2 ≤ N) (s : IIT.State N) :
    IIT.Census.caseB1 N s ⊆ IIT.Census.univPos N s := by
  rintro z ⟨hz, hC⟩
  refine ⟨hz, ?_⟩
  have h0 : 0 < N := by omega
  set S' : Finset (Fin N) := {⟨0, h0⟩}
  have hne : S' ≠ Finset.univ := by
    intro h
    have := congrArg Finset.card h
    simp [S'] at this
    omega
  have hlt := hC.2 S' (Finset.subset_univ _) hne (by simp [S'])
  rw [IIT.sysPhi_eq_zero_of_card_le_one _ _ _ (by simp [S'])] at hlt
  exact hlt

/-- **Corollary A**: `P(C₄ ∩ C₂) / P(C₂) → 0`. -/
theorem tendsto_prob_C4_given_C2 (s : ∀ N, IIT2.State N) :
    Tendsto (fun N => (volume (IIT.Census.caseB1 N (s N) ∩ C2 N (s N))).toReal /
      (volume (C2 N (s N))).toReal) atTop (𝓝 0) := by
  have hC2 : Tendsto (fun N => (volume (C2 N (s N))).toReal) atTop (𝓝 1) := by
    simp_rw [volume_C2]
    have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp
      (IIT2.tendsto_volume_wholeIsMainComplex s)
    rw [ENNReal.toReal_one] at this
    exact this
  have hU : Tendsto (fun N => (volume (IIT.Census.univPos N (s N))).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (IIT.Census.tendsto_volume_univPos s)
    rw [ENNReal.toReal_zero] at this
    exact this
  have hnum : Tendsto (fun N => (volume (IIT.Census.caseB1 N (s N) ∩ C2 N (s N))).toReal)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
      (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    refine ENNReal.toReal_mono ?_ (measure_mono (Set.inter_subset_left.trans
      (caseB1_subset_univPos hN (s N))))
    refine ne_top_of_le_ne_top (b := volume (IIT.Census.cube N)) (by simp [volume_cube_IIT]) ?_
    exact measure_mono fun z hz => hz.1
  have := hnum.div hC2 one_ne_zero
  rw [zero_div] at this
  exact this

end IITCompare

#print axioms IITCompare.tendsto_prob_C4_given_C2
