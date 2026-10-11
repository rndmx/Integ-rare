/-
Census, B1: measurability of the `GoodX3` fields (`NewX3MeasStmt`, B1GoodX3).
-/
import IIT.Census.B1GoodX3

namespace IIT
namespace Census

open MeasureTheory Finset

variable {N : ℕ}

lemma measurableSet_lowU_eq (r0 : State N) (A : Finset (Fin N)) :
    MeasurableSet {w : Param N | lowU N w r0 = A} := by
  have h : {w : Param N | lowU N w r0 = A} = ⋂ j, {w | (j ∈ lowU N w r0 ↔ j ∈ A)} := by
    ext w; simp [Finset.ext_iff]
  rw [h]
  refine MeasurableSet.iInter fun j => ?_
  by_cases hj : j ∈ A
  · convert measurableSet_mem_lowU r0 j using 1; ext w; simp [hj]
  · convert (measurableSet_mem_lowU r0 j).compl using 1; ext w; simp [hj]

/-- **`NewX3MeasStmt`, proved.** -/
theorem newX3Meas_proved : NewX3MeasStmt := by
  intro N s r0 x σ
  have h : {w : Param N | NewX3 N s r0 x σ w} =
      {w | 1000 * (lowU N w r0).card ≤ N ∧
        (σ = .cause → ∃ j, j ≠ x ∧ 1 / 2 + Real.exp (-((N : ℝ) / 200)) ≤ clamp01 (w r0 j) ∧
          clamp01 (w r0 j) + clamp01 (w (flipAt x r0) j) ≤ 1 - 1 / (N : ℝ)) ∧
        (σ = .effect → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 2 → x ∉ K' →
          ∑ i, Real.log (max (2 * b1CutMeanPlus w (flipAt x s) K' i) 1) ≤ 23 / 50 * (N : ℝ))} := by
    ext w
    exact ⟨fun h => ⟨h.1, h.2, h.3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩
  rw [h]
  refine b1_mset_and ?_ (b1_mset_and (b1_mset_imp (MeasurableSet.const _) (b1_mset_exists fun j =>
      b1_mset_and (MeasurableSet.const _) (b1_mset_and (measurableSet_le measurable_const (b1m_clamp r0 j))
        (measurableSet_le ((b1m_clamp r0 j).add (b1m_clamp _ j)) measurable_const))))
    (b1_mset_imp (MeasurableSet.const _) (b1_mset_forall fun K' => b1_mset_imp (MeasurableSet.const _)
      (b1_mset_imp (MeasurableSet.const _) (b1_mset_imp (MeasurableSet.const _)
        (measurableSet_le (Finset.measurable_sum _ fun i _ =>
          (((b1mx_CutMeanPlus _ K' i).const_mul 2).max measurable_const).log) measurable_const))))))
  exact b1_mset_at (φ := fun w => lowU N w r0) (measurableSet_lowU_eq r0)
    (P := fun _ A => 1000 * A.card ≤ N) fun A => MeasurableSet.const _

end Census
end IIT

#print axioms IIT.Census.newX3Meas_proved
