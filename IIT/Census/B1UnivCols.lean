/-
Census, B1 lower bound, leaf `phi_univ_ge_EX`: columns of the generic rows.

Under `rowsOutM A` (independent uniform entries on the rows outside `A`) the columns
`j ↦ (g r j)_{r ∉ A}` are independent with law `colLawG A = ⊗_{r ∉ A} unif`
(`mp_colsG`, `iIndepFun_colsG`), and
* `cols_hoeffding` : Hoeffding for a sum of bounded functions of distinct columns;
* `colLawG_pos_part_le` : `E ((a + Σ_{r ∈ RG} φ_r(c r))/2^k - F)⁺ ≤ ((a + |RG|/2)/2^k - F)⁺ + σ/2`
  whenever `|RG|/(12·4^k) ≤ σ²` (each `φ_r` is `clamp01` or `1 - clamp01`);
* `unif_pos_part_eq` : `∫ (φ v - c)⁺ = (1 - c)²/2` for `c ∈ [0,1]`.
-/
import IIT.Census.B1UnivCond

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

variable {N : ℕ}

/-! ### Transposition -/

/-- The law of one generic column. -/
noncomputable def colLawG (A : Finset (State N)) : Measure ({r // r ∉ A} → ℝ) := Measure.pi fun _ => unif

instance (A : Finset (State N)) : IsProbabilityMeasure (colLawG A) := by
  unfold colLawG; infer_instance

/-- The generic columns. -/
def colsG (A : Finset (State N)) (g : {r // r ∉ A} → Fin N → ℝ) : Fin N → {r // r ∉ A} → ℝ :=
  fun j r => g r j

lemma measurable_colsG (A : Finset (State N)) : Measurable (colsG A) :=
  Measurable.of_eval fun j => Measurable.of_eval fun r =>
    (measurable_pi_apply j).comp (measurable_pi_apply r)

theorem mp_colsG (A : Finset (State N)) :
    MeasurePreserving (colsG A) (rowsOutM A) (Measure.pi fun _ : Fin N => colLawG A) := by
  have h4 : MeasurePreserving (MeasurableEquiv.curry {r // r ∉ A} (Fin N) ℝ)
      (Measure.pi fun _ => unif) (rowsOutM A) := by
    refine ⟨MeasurableEquiv.measurable _, ?_⟩
    have := Measure.infinitePi_map_curry (X := ℝ) (fun (_ : {r // r ∉ A}) (_ : Fin N) => unif)
    simp only [Measure.infinitePi_eq_pi] at this
    exact this
  have h5 : MeasurePreserving (MeasurableEquiv.curry (Fin N) {r // r ∉ A} ℝ)
      (Measure.pi fun _ => unif) (Measure.pi fun _ : Fin N => colLawG A) := by
    refine ⟨MeasurableEquiv.measurable _, ?_⟩
    have := Measure.infinitePi_map_curry (X := ℝ) (fun (_ : Fin N) (_ : {r // r ∉ A}) => unif)
    simp only [Measure.infinitePi_eq_pi] at this
    exact this
  have hsw : MeasurePreserving (fun (x : {r // r ∉ A} × Fin N → ℝ) (q : Fin N × {r // r ∉ A}) => x q.swap)
      (Measure.pi fun _ => unif) (Measure.pi fun _ => unif) :=
    ⟨Measurable.of_eval fun q => measurable_pi_apply _,
      map_comp_inj Prod.swap Prod.swap_injective unif⟩
  have h := (h5.comp hsw).comp (MeasurePreserving.symm _ h4)
  convert h using 1
  funext g j r
  rfl

lemma mp_colG (A : Finset (State N)) (j : Fin N) :
    MeasurePreserving (fun g => colsG A g j) (rowsOutM A) (colLawG A) :=
  (measurePreserving_eval (fun _ : Fin N => colLawG A) j).comp (mp_colsG A)

theorem iIndepFun_colsG (A : Finset (State N)) :
    iIndepFun (fun (j : Fin N) g => colsG A g j) (rowsOutM A) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map fun j => (mp_colG A j).measurable.aemeasurable]
  have h1 : (rowsOutM A).map (fun g j => colsG A g j) = Measure.pi fun _ : Fin N => colLawG A :=
    (mp_colsG A).map_eq
  rw [h1]
  congr 1
  funext j
  exact (mp_colG A j).map_eq.symm

/-- **Hoeffding over the columns.** -/
lemma cols_hoeffding (A : Finset (State N)) (J : Finset (Fin N))
    (Ψ : Fin N → ({r // r ∉ A} → ℝ) → ℝ) (hΨm : ∀ j, Measurable (Ψ j)) {R : ℝ}
    (hΨ : ∀ j c, Ψ j c ∈ Set.Icc 0 R) {ε : ℝ} (hε : 0 ≤ ε) :
    rowsOutM A {g | ε ≤ |∑ j ∈ J, (Ψ j (colsG A g j) - ∫ c, Ψ j c ∂colLawG A)|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * ε ^ 2 / ∑ j ∈ J, R ^ 2)) := by
  have hind : iIndepFun (fun j g => Ψ j (colsG A g j)) (rowsOutM A) :=
    (iIndepFun_colsG A).comp (fun j => Ψ j) hΨm
  have hmeas : ∀ j, AEMeasurable (fun g => Ψ j (colsG A g j)) (rowsOutM A) :=
    fun j => ((hΨm j).comp (mp_colG A j).measurable).aemeasurable
  have hb : ∀ j ∈ J, ∀ᵐ g ∂(rowsOutM A), Ψ j (colsG A g j) ∈ Set.Icc 0 ((fun _ => R) j) :=
    fun j _ => ae_of_all _ fun g => hΨ j _
  have h := hoeffding_abs (μ := rowsOutM A) (X := fun j g => Ψ j (colsG A g j)) J hind hmeas hb hε
  have hint : ∀ j, ∫ g, Ψ j (colsG A g j) ∂rowsOutM A = ∫ c, Ψ j c ∂colLawG A := fun j => by
    rw [← (mp_colG A j).map_eq, integral_map (mp_colG A j).measurable.aemeasurable
      (hΨm j).aestronglyMeasurable]
  simp only [hint] at h
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal h

end Census
end IIT
