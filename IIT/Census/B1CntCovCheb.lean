/-
Census, B1, W14 work package WP6 (part 3): Chebyshev's inequality for a count of events
(`count_cheb`), generic.  Blueprint: `iit-census/lean/B1-W14-count-lean.md` §11.
Model: `ThmP3Cheb.tp_cheb`.  No `sorry`.
-/
import IIT.Census.B1CntBasics

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

/-- **Chebyshev for a count**: `W = #{i ∈ I : ω ∈ A i}`, `e0 ≤ E W`, `Var W ≤ V` ⇒
`P(W < e0/2) ≤ 4V/e0²`. -/
theorem count_cheb {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : Finset ι) (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) {e0 V : ℝ} (he0 : 0 < e0)
    (he : e0 ≤ ∑ i ∈ I, (μ (A i)).toReal)
    (hV : ∑ i ∈ I, ∑ j ∈ I, ((μ (A i ∩ A j)).toReal - (μ (A i)).toReal * (μ (A j)).toReal) ≤ V) :
    μ {ω | ((I.filter fun i => ω ∈ A i).card : ℝ) < e0 / 2} ≤ ENNReal.ofReal (4 * V / e0 ^ 2) := by
  simp only [← measureReal_def] at he hV
  set e := ∑ i ∈ I, μ.real (A i) with he_def
  have hepos : 0 < e := he0.trans_le he
  set f : ι → Ω → ℝ := fun i => (A i).indicator 1 with hf
  have hfi : ∀ i, Integrable (f i) μ := fun i => (integrable_const (1 : ℝ)).indicator (hA i)
  have hfm : ∀ i, Measurable (f i) := fun i => measurable_const.indicator (hA i)
  have hff : ∀ i j, (fun ω => f i ω * f j ω) = (A i ∩ A j).indicator 1 := fun i j => by
    funext ω
    simp only [hf, Set.inter_indicator_one, Pi.mul_apply]
  have hgi : ∀ i j, Integrable (fun ω => f i ω * f j ω) μ := fun i j => by
    rw [hff]
    exact (integrable_const (1 : ℝ)).indicator ((hA i).inter (hA j))
  set X : Ω → ℝ := fun ω => ∑ i ∈ I, f i ω with hX
  have hXc : ∀ ω, X ω = ((I.filter fun i => ω ∈ A i).card : ℝ) := fun ω => by
    simp only [hX, hf, Set.indicator_apply, Pi.one_apply]
    rw [Finset.sum_boole]
  have hXm : Measurable X := Finset.measurable_sum _ fun i _ => hfm i
  have hXi : Integrable X μ := integrable_finsetSum _ fun i _ => hfi i
  have hX2 : ∀ ω, X ω ^ 2 = ∑ i ∈ I, ∑ j ∈ I, f i ω * f j ω := fun ω => by
    simp only [hX, sq, Finset.sum_mul_sum]
  have hX2i : Integrable (fun ω => X ω ^ 2) μ := by
    simp_rw [hX2]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hgi i j
  have hIX : ∫ ω, X ω ∂μ = e := by
    simp only [hX]
    rw [integral_finsetSum _ fun i _ => hfi i]
    exact Finset.sum_congr rfl fun i _ => integral_indicator_one (hA i)
  have hIX2 : ∫ ω, X ω ^ 2 ∂μ = ∑ i ∈ I, ∑ j ∈ I, μ.real (A i ∩ A j) := by
    simp_rw [hX2]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hgi i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hgi i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hff, integral_indicator_one ((hA i).inter (hA j))]
  have he2 : e ^ 2 = ∑ i ∈ I, ∑ j ∈ I, μ.real (A i) * μ.real (A j) := by
    rw [he_def, sq, Finset.sum_mul_sum]
  set Z := {ω | ((I.filter fun i => ω ∈ A i).card : ℝ) < e0 / 2} with hZdef
  have hZ : MeasurableSet Z := by
    have : Z = X ⁻¹' Set.Iio (e0 / 2) := by
      ext ω; simp only [hZdef, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iio, hXc]
    rw [this]; exact hXm measurableSet_Iio
  have hpt : ∀ ω, Z.indicator (1 : Ω → ℝ) ω ≤ 4 * (X ω - e) ^ 2 / e0 ^ 2 := fun ω => by
    by_cases hω : ω ∈ Z
    · rw [Set.indicator_of_mem hω, Pi.one_apply]
      have hlt : X ω < e0 / 2 := by rw [hXc]; exact hω
      have h1 : e0 / 2 ≤ e - X ω := by linarith
      have h2 : (e0 / 2) ^ 2 ≤ (X ω - e) ^ 2 := by
        rw [show (X ω - e) ^ 2 = (e - X ω) ^ 2 by ring]
        exact pow_le_pow_left₀ (by positivity) h1 2
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    · rw [Set.indicator_of_notMem hω]
      positivity
  have hexp : (fun ω => 4 * (X ω - e) ^ 2 / e0 ^ 2) =
      fun ω => (4 / e0 ^ 2) * (X ω ^ 2 - 2 * e * X ω + e ^ 2) := by
    funext ω; ring
  have hint : Integrable (fun ω => 4 * (X ω - e) ^ 2 / e0 ^ 2) μ := by
    rw [hexp]
    exact ((hX2i.sub (hXi.const_mul _)).add (integrable_const _)).const_mul _
  have hbound : μ.real Z ≤ ∫ ω, 4 * (X ω - e) ^ 2 / e0 ^ 2 ∂μ := by
    rw [← integral_indicator_one hZ]
    exact integral_mono ((integrable_const 1).indicator hZ) hint hpt
  have hi1 : Integrable (fun ω => X ω ^ 2 - 2 * e * X ω) μ := hX2i.sub (hXi.const_mul _)
  have hi2 : Integrable (fun ω => 2 * e * X ω) μ := hXi.const_mul _
  have hcalc : ∫ ω, 4 * (X ω - e) ^ 2 / e0 ^ 2 ∂μ =
      4 / e0 ^ 2 * (∫ ω, X ω ^ 2 ∂μ - e ^ 2) := by
    rw [hexp, integral_const_mul, integral_add hi1 (integrable_const _),
      integral_sub hX2i hi2, integral_const_mul, hIX, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    ring
  have hvar : ∫ ω, X ω ^ 2 ∂μ - e ^ 2 ≤ V := by
    rw [hIX2, he2, ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    exact hV
  have hreal : μ.real Z ≤ 4 * V / e0 ^ 2 := by
    calc μ.real Z ≤ 4 / e0 ^ 2 * (∫ ω, X ω ^ 2 ∂μ - e ^ 2) := hbound.trans hcalc.le
      _ ≤ 4 / e0 ^ 2 * V := by gcongr
      _ = 4 * V / e0 ^ 2 := by ring
  rw [← ofReal_measureReal (measure_ne_top μ Z)]
  exact ENNReal.ofReal_le_ofReal hreal

end Census
end IIT

#print axioms IIT.Census.count_cheb
