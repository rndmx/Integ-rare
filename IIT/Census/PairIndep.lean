/-
Census pair step, part 1: product-measure tools.

* grouping the coordinates of an iid product measure along the fibres of a labelling gives
  independent blocks, each again an iid product (`iIndepFun_fib`, `map_fib`);
* reindexing along an injection preserves iid products (`map_comp_inj`);
* monomials in clamped coordinates integrate to `∏ 1/(e+1)` (`integral_mono`).
-/
import IIT.Census.PairReduce
import IIT.Census.UnivProb

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

noncomputable section

/-! ### Grouping coordinates -/

section Group

variable {I β E : Type*} [Fintype I] [Fintype β] [DecidableEq β] [MeasurableSpace E]

/-- Restriction of `x : I → E` to the fibre `lab ⁻¹ {w}`. -/
def fib (lab : I → β) (w : β) (x : I → E) : {i // lab i = w} → E := fun i => x i

omit [Fintype I] [Fintype β] [DecidableEq β] in
@[fun_prop]
lemma measurable_fib (lab : I → β) (w : β) : Measurable (fib (E := E) lab w) :=
  Measurable.of_eval fun i => measurable_pi_apply i.1

lemma map_fib_pi (lab : I → β) (ν : Measure E) [IsProbabilityMeasure ν] :
    (Measure.pi fun _ : I => ν).map (fun x w => fib lab w x) =
      Measure.pi fun w : β => Measure.pi fun _ : {i // lab i = w} => ν := by
  have h1 := (measurePreserving_piCongrLeft (fun _ : I => ν) (Equiv.sigmaFiberEquiv lab)).symm
  have h2 := Measure.infinitePi_map_piCurry (X := fun (w : β) (_ : {i // lab i = w}) => E)
    (fun w _ => ν)
  simp only [Measure.infinitePi_eq_pi] at h2
  have hG : (fun x w => fib lab w x) = (MeasurableEquiv.piCurry
      (fun (w : β) (_ : {i // lab i = w}) => E)) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : I => E) (Equiv.sigmaFiberEquiv lab)).symm := by
    funext x w i
    rfl
  rw [hG, ← Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _),
    h1.map_eq, h2]

lemma map_fib (lab : I → β) (ν : Measure E) [IsProbabilityMeasure ν] (w : β) :
    (Measure.pi fun _ : I => ν).map (fib lab w) = Measure.pi fun _ : {i // lab i = w} => ν := by
  have : fib (E := E) lab w = (fun y => y w) ∘ (fun x w => fib lab w x) := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply w) (Measurable.of_eval fun w =>
    measurable_fib lab w), map_fib_pi, (measurePreserving_eval _ w).map_eq]

lemma iIndepFun_fib (lab : I → β) (ν : Measure E) [IsProbabilityMeasure ν] :
    iIndepFun (fun w x => fib lab w x) (Measure.pi fun _ : I => ν) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun w => (measurable_fib lab w).aemeasurable),
    map_fib_pi]
  congr 1
  funext w
  rw [map_fib]

/-- Events depending on disjoint fibres are independent. -/
lemma measure_iInter_fib (lab : I → β) (ν : Measure E) [IsProbabilityMeasure ν]
    (S : ∀ w, Set ({i // lab i = w} → E)) (hS : ∀ w, MeasurableSet (S w)) :
    (Measure.pi fun _ : I => ν) (⋂ w, fib lab w ⁻¹' S w) =
      ∏ w, (Measure.pi fun _ : I => ν) (fib lab w ⁻¹' S w) :=
  (iIndepFun_fib lab ν).meas_iInter fun w => ⟨S w, hS w, rfl⟩

end Group

/-! ### Reindexing along an injection -/

lemma map_comp_inj {I J E : Type*} [Fintype I] [Fintype J] [MeasurableSpace E]
    (g : J → I) (hg : Function.Injective g) (ν : Measure E) [IsProbabilityMeasure ν] :
    (Measure.pi fun _ : I => ν).map (fun x j => x (g j)) = Measure.pi fun _ : J => ν := by
  classical
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (Measurable.of_eval fun j => measurable_pi_apply (g j))
    (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : I → E => fun j => x (g j)) ⁻¹' Set.univ.pi s =
      Set.univ.pi (Function.extend g s fun _ => Set.univ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h i
      by_cases hi : ∃ j, g j = i
      · obtain ⟨j, rfl⟩ := hi
        rw [hg.extend_apply]; exact h j
      · rw [Function.extend_apply' _ _ _ (by simpa using hi)]; trivial
    · intro h j
      have := h (g j)
      rwa [hg.extend_apply] at this
  rw [hpre, Measure.pi_pi]
  symm
  refine Fintype.prod_of_injective g hg _ _ (fun i hi => ?_) (fun j => by rw [hg.extend_apply])
  rw [Function.extend_apply' _ _ _ (by simpa using hi)]
  exact measure_univ

/-! ### Monomials in clamped uniform coordinates -/

lemma integral_cl_pow (e : ℕ) : ∫ x, clamp01 x ^ e ∂unif = 1 / ((e : ℝ) + 1) := by
  unfold unif
  rw [setIntegral_congr_fun measurableSet_Icc (g := fun x => x ^ e)
    (fun x hx => by simp only [clamp01_of_mem hx])]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
  simp

lemma integral_monomial {I : Type*} [Fintype I] (E : I → ℕ) :
    ∫ z, ∏ i, clamp01 (z i) ^ E i ∂(Measure.pi fun _ : I => unif) =
      ∏ i, 1 / ((E i : ℝ) + 1) := by
  rw [integral_fintype_prod_eq_prod (fun i x => clamp01 x ^ E i)]
  simp only [integral_cl_pow]

/-! ### The superblock coordinates -/

/-- States of one pair of units. -/
abbrev PS := Fin 2 → Bool
/-- The pair bits of a row: one pair state per pair. -/
abbrev Pb (L : ℕ) := Fin L → PS
/-- The outer bits of a row (superblock label). -/
abbrev Outer (n : ℕ) := Fin n → Bool
/-- Columns: the pair units `(k, e)` and the outer units. -/
abbrev Col (L n : ℕ) := (Fin L × Fin 2) ⊕ Fin n
/-- Coordinates of one superblock: a row (pair bits) and a column. -/
abbrev LI (L n : ℕ) := Pb L × Col L n
/-- Parameters of one superblock. -/
abbrev Loc (L n : ℕ) := LI L n → ℝ
/-- Parameters, arranged by superblocks. -/
abbrev Om (L n : ℕ) := Outer n → Loc L n

/-- Uniform measure on a superblock. -/
def locM (L n : ℕ) : Measure (Loc L n) := Measure.pi fun _ => unif
/-- Uniform measure on all superblocks. -/
def omM (L n : ℕ) : Measure (Om L n) := Measure.pi fun _ => locM L n

instance (L n : ℕ) : IsProbabilityMeasure (locM L n) := by unfold locM; infer_instance
instance (L n : ℕ) : IsProbabilityMeasure (omM L n) := by unfold omM; infer_instance

/-- Column `(k, e)` is unit `2k + e`; outer column `j` is unit `2L + j`. -/
def eCol (L n : ℕ) : Col L n ≃ Fin (2 * L + n) :=
  ((Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv).trans
    (finCongr (by ring))

@[simp] lemma eCol_inl_val (L n : ℕ) (k : Fin L) (e : Fin 2) :
    ((eCol L n) (Sum.inl (k, e))).val = 2 * k + e := by
  simp [eCol, finProdFinEquiv]; ring

@[simp] lemma eCol_inr_val (L n : ℕ) (j : Fin n) :
    ((eCol L n) (Sum.inr j)).val = 2 * L + j := by
  simp [eCol]

/-- The bits of the row with pair bits `π` and outer bits `w`, by column. -/
def rowFun {L n : ℕ} (π : Pb L) (w : Outer n) : Col L n → Bool
  | Sum.inl (k, e) => π k e
  | Sum.inr j => w j

/-- Rows are pairs (pair bits, outer bits). -/
def eRow (L n : ℕ) : Pb L × Outer n ≃ State (2 * L + n) where
  toFun p := fun j => rowFun p.1 p.2 ((eCol L n).symm j)
  invFun v := (fun k e => v (eCol L n (Sum.inl (k, e))), fun j => v (eCol L n (Sum.inr j)))
  left_inv := by
    rintro ⟨π, w⟩
    simp [rowFun]
  right_inv := by
    intro v
    funext j
    obtain ⟨c, rfl⟩ := (eCol L n).surjective j
    rcases c with ⟨k, e⟩ | j <;> simp [rowFun]

@[simp] lemma eRow_eCol {L n : ℕ} (π : Pb L) (w : Outer n) (c : Col L n) :
    eRow L n (π, w) (eCol L n c) = rowFun π w c := by
  simp [eRow]

/-- Flat coordinates: `(w, (π, c)) ↦ (row (π, w), column c)`. -/
def eFlat (L n : ℕ) : Outer n × LI L n ≃ State (2 * L + n) × Fin (2 * L + n) :=
  ((Equiv.prodAssoc _ _ _).symm.trans
    (Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.refl _))).trans
    (Equiv.prodCongr (eRow L n) (eCol L n))

@[simp] lemma eFlat_apply {L n : ℕ} (w : Outer n) (π : Pb L) (c : Col L n) :
    eFlat L n (w, (π, c)) = (eRow L n (π, w), eCol L n c) := rfl

/-- Parameters rearranged by superblocks. -/
def Ψ (L n : ℕ) : Param (2 * L + n) ≃ᵐ Om L n :=
  ((MeasurableEquiv.curry (State (2 * L + n)) (Fin (2 * L + n)) ℝ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (eFlat L n)).symm).trans
    (MeasurableEquiv.curry (Outer n) (LI L n) ℝ)

lemma Ψ_apply {L n : ℕ} (x : Param (2 * L + n)) (w : Outer n) (i : LI L n) :
    Ψ L n x w i = x (eRow L n (i.1, w)) (eCol L n i.2) := by
  obtain ⟨π, c⟩ := i
  simp [Ψ, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]

lemma mp_Ψ (L n : ℕ) : MeasurePreserving (Ψ L n) (cubeM (2 * L + n)) (omM L n) := by
  have h1 : MeasurePreserving (MeasurableEquiv.curry (State (2 * L + n)) (Fin (2 * L + n)) ℝ).symm
      (cubeM (2 * L + n)) (Measure.pi fun _ => unif) := by
    refine ⟨MeasurableEquiv.measurable _, ?_⟩
    have := Measure.infinitePi_map_curry_symm (X := ℝ) (fun (_ : State (2 * L + n))
      (_ : Fin (2 * L + n)) => unif)
    simp only [Measure.infinitePi_eq_pi] at this
    exact this
  have h2 := (measurePreserving_piCongrLeft (fun _ : State (2 * L + n) × Fin (2 * L + n) => unif)
    (eFlat L n)).symm
  have h3 : MeasurePreserving (MeasurableEquiv.curry (Outer n) (LI L n) ℝ)
      (Measure.pi fun _ => unif) (omM L n) := by
    refine ⟨MeasurableEquiv.measurable _, ?_⟩
    have := Measure.infinitePi_map_curry (X := ℝ) (fun (_ : Outer n) (_ : LI L n) => unif)
    simp only [Measure.infinitePi_eq_pi] at this
    exact this
  exact (h3.comp h2).comp h1

end

end Census
end IIT
