/-
Census, B1: measurability of the new `GoodX2` fields (`NewXMeasStmt`, B1GoodX2).
-/
import IIT.Census.B1GoodX2

namespace IIT
namespace Census

open MeasureTheory Finset

/-- **`NewXMeasStmt`, proved.** -/
theorem newXMeas_proved : NewXMeasStmt := by
  intro N s r0 x σ
  have h : {w : Param N | NewX N s r0 x σ w} =
      {w | (∀ j, 1 / 2 + Real.exp (-((N : ℝ) / 200)) ≤ clamp01 (w r0 j)) ∧
        (σ = .cause → ∃ j, j ≠ x ∧ clamp01 (w r0 j) + clamp01 (w (flipAt x r0) j) ≤ 1 - 1 / (N : ℝ)) ∧
        (σ = .effect → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 3 → x ∉ K' →
          ∑ i, Real.log (max (2 * b1CutMeanPlus w (flipAt x s) K' i) 1) ≤ 23 / 50 * (N : ℝ))} := by
    ext w
    exact ⟨fun h => ⟨h.1, h.2, h.3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩
  rw [h]
  refine b1_mset_and (b1_mset_forall fun j => measurableSet_le measurable_const (b1m_clamp r0 j))
    (b1_mset_and (b1_mset_imp (MeasurableSet.const _) (b1_mset_exists fun j =>
      b1_mset_and (MeasurableSet.const _)
        (measurableSet_le ((b1m_clamp r0 j).add (b1m_clamp _ j)) measurable_const)))
    (b1_mset_imp (MeasurableSet.const _) (b1_mset_forall fun K' => b1_mset_imp (MeasurableSet.const _)
      (b1_mset_imp (MeasurableSet.const _) (b1_mset_imp (MeasurableSet.const _)
        (measurableSet_le (Finset.measurable_sum _ fun i _ =>
          (((b1mx_CutMeanPlus _ K' i).const_mul 2).max measurable_const).log) measurable_const))))))

end Census
end IIT

#print axioms IIT.Census.newXMeas_proved
