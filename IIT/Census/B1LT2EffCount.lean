/-
Census, B1 lemma LT2, module M6f-1: few units with a weak effect entry.

`lt2_eff_count`: for a set `D` of columns and `k ≥ 1`,
`P(#{a ∈ D : |y_{s,a} - 1/2| < γ} ≥ k) ≤ C(|D|, k) (2γ)^k` (the entries `(s, a)` are independent uniforms).
-/
import IIT.Census.B1LT2PhiPair

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

lemma lt2_unif_mid {γ : ℝ} (hγ : 0 ≤ γ) : unif {u | |clamp01 u - 1 / 2| < γ} ≤ ENNReal.ofReal (2 * γ) := by
  unfold unif
  rw [Measure.restrict_apply' measurableSet_Icc]
  calc volume ({u | |clamp01 u - 1 / 2| < γ} ∩ Set.Icc (0 : ℝ) 1) ≤ volume (Set.Icc (1 / 2 - γ) (1 / 2 + γ)) :=
        measure_mono fun u hu => by
          obtain ⟨h1, h2⟩ := hu
          simp only [Set.mem_setOf_eq] at h1
          rw [clamp01_of_mem h2, abs_lt] at h1
          exact ⟨by linarith, by linarith⟩
    _ = ENNReal.ofReal (2 * γ) := by rw [Real.volume_Icc]; congr 1; ring

/-- **Few weak effect units.** -/
theorem lt2_eff_count (s : State N) (D : Finset (Fin N)) {γ : ℝ} (hγ : 0 ≤ γ) (k : ℕ) :
    cubeM N {w | k ≤ (D.filter fun a => |clamp01 (w s a) - 1 / 2| < γ).card} ≤
      ENNReal.ofReal ((D.card.choose k : ℕ) * (2 * γ) ^ k) := by
  classical
  have hsub : {w : Param N | k ≤ (D.filter fun a => |clamp01 (w s a) - 1 / 2| < γ).card} ⊆
      ⋃ K ∈ D.powersetCard k, ⋂ a ∈ K, {w : Param N | |clamp01 (w s a) - 1 / 2| < γ} := by
    intro w hw
    simp only [Set.mem_setOf_eq] at hw
    obtain ⟨K, hK, hKc⟩ := Finset.exists_subset_card_eq hw
    simp only [Set.mem_iUnion, Set.mem_iInter, exists_prop, mem_powersetCard]
    exact ⟨K, ⟨hK.trans (filter_subset _ _), hKc⟩, fun a ha => (mem_filter.1 (hK ha)).2⟩
  have hone : ∀ a, cubeM N {w : Param N | |clamp01 (w s a) - 1 / 2| < γ} ≤ ENNReal.ofReal (2 * γ) := by
    intro a
    have mp := lt2_mp_entry (N := N) (s, a)
    rw [show {w : Param N | |clamp01 (w s a) - 1 / 2| < γ} =
        (fun w : Param N => w (s, a).1 (s, a).2) ⁻¹' {u | |clamp01 u - 1 / 2| < γ} from rfl,
      mp.measure_preimage (show MeasurableSet {u : ℝ | |clamp01 u - 1 / 2| < γ} from
        measurableSet_lt ((measurable_clamp01.sub measurable_const).abs) measurable_const).nullMeasurableSet]
    exact lt2_unif_mid hγ
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ K ∈ D.powersetCard k, cubeM N (⋂ a ∈ K, {w : Param N | |clamp01 (w s a) - 1 / 2| < γ})
      ≤ ∑ _K ∈ D.powersetCard k, ENNReal.ofReal (2 * γ) ^ k := by
        refine Finset.sum_le_sum fun K hK => ?_
        rw [cubeM_iInter_eq_prod_of_detOnE K (fun a => {(s, a)})
          (X := fun a => {w : Param N | |clamp01 (w s a) - 1 / 2| < γ})
          (fun a _ b _ hab => by simp [hab])
          (fun a _ => measurableSet_lt ((measurable_clamp01.comp ((measurable_pi_apply a).comp
            (measurable_pi_apply s))).sub measurable_const).abs measurable_const)
          (fun a _ w w' h => by
            simp only [Set.mem_setOf_eq]
            rw [show w s a = w' s a from h (s, a) (mem_singleton_self _)])]
        rw [← (mem_powersetCard.1 hK).2, ← Finset.prod_const]
        exact Finset.prod_le_prod' fun a _ => hone a
    _ = ENNReal.ofReal ((D.card.choose k : ℕ) * (2 * γ) ^ k) := by
        rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul,
          ENNReal.ofReal_mul (p := ((D.card.choose k : ℕ) : ℝ)) (q := (2 * γ) ^ k) (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by positivity)]

end Census
end IIT
