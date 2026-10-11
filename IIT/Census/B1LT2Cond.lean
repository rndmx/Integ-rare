/-
Census, B1 lemma LT2, module M6a: conditioning on the private positions.

* `lt2_cond_priv`: if, for every value `A` of `Priv` and every `w` with `Priv w = A`, resampling the entries on `A`
  lands in `Y` with probability `≤ p`, then `P(Y) ≤ p`.
* `lt2_mp_inj`: for an injective family of entries `e : B → State N × Fin N`, `η ↦ (η (e b))_b` is measure preserving
  `cubeM → ∏ unif`.
-/
import IIT.Census.B1LT2Floor4

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- **Conditioning on the private positions.** -/
theorem lt2_cond_priv (s : State N) {Y : Set (Param N)} (hY : MeasurableSet Y) {p : ENNReal}
    (h : ∀ A w, lt2Priv s w = A → cubeM N {η | replE A w η ∈ Y} ≤ p) : cubeM N Y ≤ p := by
  haveI : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  rw [measure_eq_sum_partition (cubeM N) (lt2_mset_Priv s) Y]
  calc ∑ A, cubeM N (Y ∩ {w | lt2Priv s w = A}) ≤ ∑ A, p * cubeM N {w | lt2Priv s w = A} :=
        Finset.sum_le_sum fun A _ => by
          rw [Set.inter_comm]
          exact cubeM_inter_le_of_sectionE A (lt2_mset_Priv s A) hY (lt2Priv_detOn s A) fun w hw => h A w hw
    _ = p * ∑ A, cubeM N (Set.univ ∩ {w | lt2Priv s w = A}) := by
        rw [Finset.mul_sum]; simp only [Set.univ_inter]
    _ = p := by rw [← measure_eq_sum_partition (cubeM N) (lt2_mset_Priv s) Set.univ, measure_univ, mul_one]

/-- **An injective family of entries is iid uniform.** -/
theorem lt2_mp_inj {B : Type*} [Fintype B] [DecidableEq B] (e : B → State N × Fin N) (he : Function.Injective e) :
    MeasurePreserving (fun (η : Param N) (b : B) => η (e b).1 (e b).2) (cubeM N) (Measure.pi fun _ : B => unif) := by
  classical
  set A : Finset (State N × Fin N) := univ.image e
  have hA : ∀ b, e b ∈ A := fun b => mem_image_of_mem e (mem_univ b)
  set σ : B ≃ {q // q ∈ A} := Equiv.ofBijective (fun b => ⟨e b, hA b⟩) ⟨fun b b' h => he (congrArg Subtype.val h),
    fun q => by obtain ⟨b, -, hb⟩ := mem_image.1 q.2; exact ⟨b, Subtype.ext hb⟩⟩
  have mp1 := mp_restrictE (N := N) A
  have mp2 := (measurePreserving_piCongrLeft (fun _ : {q // q ∈ A} => unif) σ).symm
  have := mp2.comp mp1
  convert this using 1
  funext η b
  simp only [Function.comp_apply, MeasurableEquiv.piCongrLeft, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
    Equiv.piCongrLeft_symm_apply]
  rfl

/-- The coordinate map of `lt2_mp_inj`, evaluated. -/
lemma lt2_mp_inj_apply {B : Type*} [Fintype B] [DecidableEq B] (e : B → State N × Fin N) (η : Param N) (b : B) :
    (fun (η : Param N) (b : B) => η (e b).1 (e b).2) η b = η (e b).1 (e b).2 := rfl

end Census
end IIT
