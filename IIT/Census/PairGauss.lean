/-
Census pair step, part 4: the limiting Gaussian.

The limiting covariance is diagonal (`Cmat`), so the multivariate Gaussian is the product of
one-dimensional Gaussians (`mvg_eq`); the margin boxes of different pairs are therefore
independent under it, and each has positive mass `gBox` (`gauss_FA`, `gBox_pos`).
-/
import IIT.Census.PairBridge

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Complex

noncomputable section

variable {L : ℕ}

/-- The limiting covariance matrix. -/
def Cmat (L : ℕ) : Matrix (Ix L) (Ix L) ℝ := Matrix.diagonal fun a => ddv a.2.1

lemma Cmat_posSemidef : (Cmat L).PosSemidef := by
  unfold Cmat
  rw [Matrix.posSemidef_diagonal_iff]
  exact fun a => (ddv_pos _).le

/-- Product of the one-dimensional limiting Gaussians. -/
def gaussPi (L : ℕ) : Measure (Ix L → ℝ) :=
  Measure.pi fun a => gaussianReal 0 (ddv a.2.1).toNNReal

instance : IsProbabilityMeasure (gaussPi L) := by unfold gaussPi; infer_instance

lemma mvg_eq : multivariateGaussian (0 : EuclideanSpace ℝ (Ix L)) (Cmat L) =
    (gaussPi L).map (WithLp.toLp 2) := by
  apply Measure.ext_of_charFun (E := EuclideanSpace ℝ (Ix L))
  funext t
  rw [charFun_multivariateGaussian Cmat_posSemidef, gaussPi, charFun_pi]
  simp_rw [charFun_gaussianReal]
  rw [← Complex.exp_sum]
  congr 1
  simp only [inner_zero_right, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub, Cmat,
    Matrix.mulVec_diagonal, dotProduct, Real.coe_toNNReal _ (ddv_pos _).le]
  push_cast
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => by ring

/-- One-pair margin box, in coordinates `(ε, c)`. -/
def box6 : Set (Fin 2 × Fin 3 → ℝ) := {y | ∀ c, 1 < y (0, c) ∧ |y (1, c)| < 1 / 2}

/-- One-pair product Gaussian. -/
def mu6 : Measure (Fin 2 × Fin 3 → ℝ) := Measure.pi fun p => gaussianReal 0 (ddv p.1).toNNReal

instance : IsProbabilityMeasure mu6 := by unfold mu6; infer_instance

/-- The Gaussian mass of the margin box. -/
def gBox : ENNReal := mu6 box6

/-- Interval of coordinate `p` in the box. -/
def Ibox (p : Fin 2 × Fin 3) : Set ℝ := if p.1 = 0 then Set.Ioi 1 else Set.Ioo (-(1 / 2)) (1 / 2)

lemma box6_eq : box6 = Set.univ.pi Ibox := by
  ext y
  simp only [box6, Set.mem_setOf_eq, Set.mem_univ_pi, Ibox]
  constructor
  · rintro h ⟨ε, c⟩
    fin_cases ε
    · simpa using (h c).1
    · simpa [abs_lt] using (h c).2
  · intro h c
    have h0 := h (0, c)
    have h1 := h (1, c)
    simp at h0 h1
    exact ⟨h0, abs_lt.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩⟩

lemma measurableSet_box6 : MeasurableSet box6 := by
  rw [box6_eq]
  exact MeasurableSet.univ_pi fun p => by unfold Ibox; split_ifs <;> measurability

lemma gBox_pos : 0 < gBox := by
  rw [gBox, box6_eq, mu6, Measure.pi_pi]
  refine CanonicallyOrderedAdd.prod_pos.mpr fun p _ => ?_
  rw [pos_iff_ne_zero]
  intro h
  have hv : (ddv p.1).toNNReal ≠ 0 := by simp [ddv_pos]
  have := gaussianReal_absolutelyContinuous' 0 hv h
  unfold Ibox at this
  split_ifs at this <;> simp at this <;> norm_num at this

/-- Pair `k` of a rescaled statistic vector sits in the margin box. -/
def goodV (v : EuclideanSpace ℝ (Ix L)) (k : Fin L) : Prop :=
  ∀ c, 1 < v (k, 0, c) ∧ |v (k, 1, c)| < 1 / 2

/-- No pair of `A` sits in the margin box. -/
def FA (A : Finset (Fin L)) : Set (EuclideanSpace ℝ (Ix L)) := {v | ∀ k ∈ A, ¬ goodV v k}

lemma isOpen_goodV (k : Fin L) : IsOpen {v : EuclideanSpace ℝ (Ix L) | goodV v k} := by
  have : {v : EuclideanSpace ℝ (Ix L) | goodV v k} =
      ⋂ c, ({v | 1 < v (k, 0, c)} ∩ {v | |v (k, 1, c)| < 1 / 2}) := by
    ext v; simp [goodV]
  rw [this]
  exact isOpen_iInter_of_finite fun c =>
    (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt (by fun_prop) continuous_const)

lemma isClosed_FA (A : Finset (Fin L)) : IsClosed (FA A) := by
  have : FA A = ⋂ k ∈ A, {v : EuclideanSpace ℝ (Ix L) | goodV v k}ᶜ := by
    ext v; simp [FA]
  rw [this]
  exact isClosed_biInter fun k _ => (isOpen_goodV k).isClosed_compl

lemma gaussPi_eq : gaussPi L =
    (Measure.pi fun _ : Fin L => mu6).map (MeasurableEquiv.curry (Fin L) (Fin 2 × Fin 3) ℝ).symm := by
  have := Measure.infinitePi_map_curry_symm (X := ℝ)
    (fun (_ : Fin L) (p : Fin 2 × Fin 3) => gaussianReal 0 (ddv p.1).toNNReal)
  simp only [Measure.infinitePi_eq_pi] at this
  rw [gaussPi, mu6, this]

lemma gauss_FA (A : Finset (Fin L)) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Ix L)) (Cmat L) (FA A) = (1 - gBox) ^ A.card := by
  rw [mvg_eq, Measure.map_apply (by fun_prop) (isClosed_FA A).measurableSet, gaussPi_eq,
    Measure.map_apply (MeasurableEquiv.measurable _)
      ((isClosed_FA A).measurableSet.preimage (by fun_prop))]
  have hpre : (MeasurableEquiv.curry (Fin L) (Fin 2 × Fin 3) ℝ).symm ⁻¹'
      (WithLp.toLp 2 ⁻¹' FA A) = Set.univ.pi fun k => if k ∈ A then box6ᶜ else Set.univ := by
    ext Y
    simp only [Set.mem_preimage, FA, goodV, Set.mem_setOf_eq, Set.mem_univ_pi]
    constructor
    · intro h k
      split_ifs with hk
      · intro hb; exact h k hk fun c => hb c
      · trivial
    · intro h k hk hg
      have := h k
      rw [if_pos hk] at this
      exact this fun c => hg c
  rw [hpre, Measure.pi_pi]
  simp only [apply_ite (mu6 ·), measure_univ]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const,
    prob_compl_eq_one_sub measurableSet_box6]
  rfl

end

end Census
end IIT
