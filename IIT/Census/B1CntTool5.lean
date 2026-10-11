/-
Census, B1 count, WP1 (generic toolkit, no IIT), part 5: the law of a signed entry sum
(blueprint `B1-W14-count-lean.md` §6, `EntrySumLawStmt`).

Under `cubeM`, the entries in a finite set `E` are iid uniform (`B1Prod.mp_restrictE`); the per-entry
map `x ↦ clamp01 x` (sign `+`) or `x ↦ 1 - clamp01 x` (sign `-`) preserves `unif` (`clamp01 = id`
a.e., reflection); reindexing `E ≃ Fin E.card` (`measurePreserving_piCongrLeft`).
-/
import IIT.Census.B1CntDefs3

namespace IIT
namespace Census

open MeasureTheory Finset

noncomputable section

lemma esl_unif_reflect : MeasurePreserving (fun u : ℝ => 1 - u) unif unif := by
  unfold unif
  have h := (volume : Measure ℝ).measurePreserving_sub_left 1
  have hpre : (fun u : ℝ => 1 - u) ⁻¹' Set.Icc (0 : ℝ) 1 = Set.Icc 0 1 := by
    ext u; simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have := h.restrict_preimage (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc
  rw [hpre] at this
  exact this

lemma esl_unif_clamp : unif.map clamp01 = unif := by
  have h : clamp01 =ᵐ[unif] id := by
    unfold unif
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    simp [clamp01, min_eq_right hu.2, max_eq_right hu.1]
  rw [Measure.map_congr h, Measure.map_id]

/-- The per-entry map: `clamp01` for sign `true`, `1 - clamp01` for sign `false`. -/
def eslPhi (b : Bool) (x : ℝ) : ℝ := if b then clamp01 x else 1 - clamp01 x

lemma measurable_eslPhi (b : Bool) : Measurable (eslPhi b) := by
  cases b
  · have : eslPhi false = fun x => 1 - clamp01 x := by funext x; simp [eslPhi]
    rw [this]; exact measurable_const.sub clamp01_measurable
  · have : eslPhi true = clamp01 := by funext x; simp [eslPhi]
    rw [this]; exact clamp01_measurable

lemma eslPhi_map (b : Bool) : unif.map (eslPhi b) = unif := by
  cases b
  · have : eslPhi false = (fun u => 1 - u) ∘ clamp01 := by funext x; simp [eslPhi]
    rw [this, ← Measure.map_map (g := fun u : ℝ => 1 - u) (measurable_const.sub measurable_id)
      clamp01_measurable,
      esl_unif_clamp, esl_unif_reflect.map_eq]
  · have : eslPhi true = clamp01 := by funext x; simp [eslPhi]
    rw [this, esl_unif_clamp]

/-- **WP1d: law of a signed entry sum.** -/
theorem entrySumLaw_proved : EntrySumLawStmt := by
  intro N E ε S hS
  -- step 1: restriction to the entries of `E`
  have hsum : ∀ w : Param N,
      ∑ e ∈ E, (if ε e then clamp01 (w e.1 e.2) - 1 / 2 else 1 / 2 - clamp01 (w e.1 e.2)) =
        ∑ q : {q // q ∈ E}, (eslPhi (ε q.1) (w q.1.1 q.1.2) - 1 / 2) := by
    intro w
    rw [← Finset.sum_coe_sort E]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold eslPhi
    split_ifs <;> ring
  have hT : MeasurableSet {v : {q // q ∈ E} → ℝ |
      ∑ q : {q // q ∈ E}, (eslPhi (ε q.1) (v q) - 1 / 2) ∈ S} :=
    hS.preimage (Finset.measurable_sum _ fun q _ =>
      ((measurable_eslPhi _).comp (measurable_pi_apply q)).sub measurable_const)
  have h1 : {w : Param N | ∑ e ∈ E, (if ε e then clamp01 (w e.1 e.2) - 1 / 2
        else 1 / 2 - clamp01 (w e.1 e.2)) ∈ S} =
      (fun (w : Param N) (q : {q // q ∈ E}) => w q.1.1 q.1.2) ⁻¹'
        {v | ∑ q : {q // q ∈ E}, (eslPhi (ε q.1) (v q) - 1 / 2) ∈ S} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [hsum]
  rw [h1, (mp_restrictE E).measure_preimage hT.nullMeasurableSet]
  -- step 2: the per-entry maps preserve `unif`
  have hΦ : MeasurePreserving (fun (v : {q // q ∈ E} → ℝ) q => eslPhi (ε q.1) (v q))
      (Measure.pi fun _ : {q // q ∈ E} => unif) (Measure.pi fun _ : {q // q ∈ E} => unif) := by
    refine ⟨Measurable.of_eval fun q => (measurable_eslPhi _).comp (measurable_pi_apply q), ?_⟩
    rw [Measure.pi_map_pi (μ := fun _ : {q // q ∈ E} => unif) (f := fun q => eslPhi (ε q.1))
      (fun q => (measurable_eslPhi _).aemeasurable)]
    congr 1
    funext q
    exact eslPhi_map _
  have hT' : MeasurableSet {v : {q // q ∈ E} → ℝ | ∑ q : {q // q ∈ E}, (v q - 1 / 2) ∈ S} :=
    hS.preimage (Finset.measurable_sum _ fun q _ => (measurable_pi_apply q).sub measurable_const)
  have h2 : {v : {q // q ∈ E} → ℝ | ∑ q : {q // q ∈ E}, (eslPhi (ε q.1) (v q) - 1 / 2) ∈ S} =
      (fun (v : {q // q ∈ E} → ℝ) q => eslPhi (ε q.1) (v q)) ⁻¹'
        {v | ∑ q : {q // q ∈ E}, (v q - 1 / 2) ∈ S} := rfl
  rw [h2, hΦ.measure_preimage hT'.nullMeasurableSet]
  -- step 3: reindexing by `Fin E.card`
  have hmp := measurePreserving_piCongrLeft (fun _ : {q // q ∈ E} => unif) E.equivFin.symm
  rw [← hmp.measure_preimage hT'.nullMeasurableSet]
  congr 1
  ext u
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, MeasurableEquiv.coe_piCongrLeft]
  rw [← (E.equivFin.symm).sum_comp]
  simp only [Equiv.piCongrLeft_apply_apply]

end

end Census
end IIT
