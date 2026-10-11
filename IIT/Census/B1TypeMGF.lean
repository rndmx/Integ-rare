/-
Census, B1 lower bound part (b), foundation: integrals over a type event (general coordinate space).

For disjoint measurable cells `I j ⊆ E`, counts `n` with `∑ n = N`, a finite measure `μ` on `E` and `F : E → ℝ`
integrable on every cell, the type event `T = {v | ∀ j, #{i | v i ∈ I j} = n j}` satisfies

  `∫_{T} ∏_i F (v i) dμ^N = #T(n) · ∏_j (∫_{I j} F dμ)^{n j}`.

With `F = 1` this is `μ^N(T) = #T(n) ∏_j μ(I j)^{n j}`, so for `F > 0` the ratio is `∏_j (cell average of F)^{n j}`:
the coordinates are, given the type, independent with the within-cell laws (the conditional Chernoff method).
-/
import IIT.Census.B1TypeGen
import Mathlib.Probability.Moments.SubGaussian

namespace IIT
namespace Census

open MeasureTheory Finset

section TypeMGF

variable {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ] {N k : ℕ}
variable (I : Fin k → Set E) [∀ j, DecidablePred (· ∈ I j)]

/-- Every coordinate of a point of a type event lies in some cell (general `E`). -/
lemma gen_type_cell (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) {n : Fin k → ℕ}
    (hn : ∑ j, n j = N) {v : Fin N → E} (hv : ∀ j, (univ.filter fun i => v i ∈ I j).card = n j) :
    ∃ σ : Fin N → Fin k, (∀ i, v i ∈ I (σ i)) ∧ fibType σ = n := by
  classical
  have hcov : ∀ i, ∃ j, v i ∈ I j := by
    intro i
    by_contra h
    push Not at h
    have hsub : (univ : Finset (Fin k)).biUnion (fun j => univ.filter fun i' => v i' ∈ I j) ⊆
        univ.erase i := by
      intro i' hi'
      rw [Finset.mem_biUnion] at hi'
      obtain ⟨j, _, hj⟩ := hi'
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_erase]
      refine ⟨?_, mem_univ _⟩
      rintro rfl
      exact h j hj.2
    have hpd : ((univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
        (fun j => univ.filter fun i' => v i' ∈ I j) :=
      fun j _ j' _ hjj' => Finset.disjoint_filter.2 fun _ _ h1 h2 =>
        Set.disjoint_left.1 (hdisj hjj') h1 h2
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_biUnion hpd, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
      Fintype.card_fin] at hcard
    simp only [hv, hn] at hcard
    have := i.2
    omega
  choose σ hσ using hcov
  refine ⟨σ, hσ, funext fun j => ?_⟩
  unfold fibType
  rw [← hv j]
  congr 1
  ext i
  simp only [Finset.mem_filter, mem_univ, true_and]
  constructor
  · rintro rfl; exact hσ i
  · intro h
    by_contra hne
    exact Set.disjoint_left.1 (hdisj hne) (hσ i) h

/-- The type event is the disjoint union of its boxes. -/
lemma gen_type_event_eq (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) {n : Fin k → ℕ}
    (hn : ∑ j, n j = N) :
    {v : Fin N → E | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} =
      ⋃ σ ∈ univ.filter (fun σ : Fin N → Fin k => fibType σ = n), genTypeBox I σ := by
  refine subset_antisymm (fun v hv => ?_) (Set.iUnion₂_subset fun _ hσ =>
    genTypeBox_sub_event I hdisj (Finset.mem_filter.1 hσ).2)
  obtain ⟨σ, hσ, hfib⟩ := gen_type_cell I hdisj hn hv
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨σ, Finset.mem_filter.2 ⟨mem_univ _, hfib⟩, fun i _ => hσ i⟩

/-- **The integral over a type event of a product function.** -/
theorem type_event_integral_prod (hI : ∀ j, MeasurableSet (I j))
    (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) {n : Fin k → ℕ} (hn : ∑ j, n j = N)
    (F : E → ℝ) (hF : ∀ j, IntegrableOn F (I j) μ) :
    ∫ v in {v : Fin N → E | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j}, ∏ i, F (v i)
        ∂(Measure.pi fun _ => μ) =
      fibTypeCount N k n * ∏ j, (∫ x in I j, F x ∂μ) ^ n j := by
  rw [gen_type_event_eq I hdisj hn]
  have hbox : ∀ σ : Fin N → Fin k, ∫ v in genTypeBox I σ, ∏ i, F (v i) ∂(Measure.pi fun _ => μ) =
      ∏ i, ∫ x in I (σ i), F x ∂μ := by
    intro σ
    rw [genTypeBox, Measure.restrict_pi_pi]
    exact integral_fintype_prod_eq_prod (fun i => F)
  have hmeas : ∀ σ ∈ univ.filter (fun σ : Fin N → Fin k => fibType σ = n), MeasurableSet (genTypeBox I σ) :=
    fun σ _ => MeasurableSet.univ_pi fun i => hI (σ i)
  rw [integral_biUnion_finset (s := genTypeBox I) _ hmeas
    (fun σ _ σ' _ h => genTypeBox_disjoint hdisj h)]
  · rw [Finset.sum_congr rfl fun σ hσ => by
      rw [hbox σ, prod_comp_eq_prod_pow_fibType (fun j => ∫ x in I j, F x ∂μ) σ,
        (Finset.mem_filter.1 hσ).2]]
    rw [Finset.sum_const, nsmul_eq_mul]
    rfl
  · intro σ _
    rw [IntegrableOn, genTypeBox, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod (f := fun _ => F) fun i => hF (σ i)

/-- The measure of a type event, real form. -/
theorem type_event_real (hI : ∀ j, MeasurableSet (I j))
    (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) {n : Fin k → ℕ} (hn : ∑ j, n j = N) :
    (Measure.pi fun _ => μ).real {v : Fin N → E | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} =
      fibTypeCount N k n * ∏ j, (μ.real (I j)) ^ n j := by
  have h := type_event_integral_prod μ I hI hdisj hn (fun _ => (1 : ℝ)) fun j => integrableOn_const
  simp only [prod_const_one, integral_const, smul_eq_mul, mul_one, Measure.real,
    Measure.restrict_apply_univ] at h
  simpa [Measure.real] using h

/-- **Conditional Chernoff on a type event**: for `t ≥ 0`,
`μ^N(T ∩ {Σ g(v_i) ≥ θ}) ≤ e^{-tθ} #T(n) ∏_j (∫_{I j} e^{t g})^{n j}`. -/
theorem type_event_dev (hI : ∀ j, MeasurableSet (I j))
    (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) {n : Fin k → ℕ} (hn : ∑ j, n j = N)
    (g : E → ℝ) (hgm : Measurable g) {t : ℝ} (ht : 0 ≤ t)
    (hg : ∀ j, IntegrableOn (fun x => Real.exp (t * g x)) (I j) μ) (θ : ℝ) :
    (Measure.pi fun _ => μ).real
        ({v : Fin N → E | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} ∩ {v | θ ≤ ∑ i, g (v i)}) ≤
      Real.exp (-(t * θ)) * (fibTypeCount N k n * ∏ j, (∫ x in I j, Real.exp (t * g x) ∂μ) ^ n j) := by
  set T := {v : Fin N → E | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j}
  set P := Measure.pi fun _ : Fin N => μ
  have hT : MeasurableSet T := by
    rw [show T = _ from gen_type_event_eq I hdisj hn]
    exact Finset.measurableSet_biUnion _ fun σ _ => MeasurableSet.univ_pi fun i => hI (σ i)
  have hsum : Measurable fun v : Fin N → E => ∑ i, g (v i) :=
    Finset.measurable_sum _ fun i _ => hgm.comp (measurable_pi_apply i)
  have hD : MeasurableSet {v : Fin N → E | θ ≤ ∑ i, g (v i)} := measurableSet_le measurable_const hsum
  have hint := type_event_integral_prod μ I hI hdisj hn (fun x => Real.exp (t * g x)) hg
  -- integrability of the product on T
  have hIT : IntegrableOn (fun v : Fin N → E => ∏ i, Real.exp (t * g (v i))) T P := by
    rw [show T = _ from gen_type_event_eq I hdisj hn]
    refine integrableOn_finset_iUnion.2 fun σ _ => ?_
    rw [IntegrableOn, genTypeBox, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod (f := fun _ x => Real.exp (t * g x)) fun i => hg (σ i)
  have hexp : ∀ v : Fin N → E, Real.exp (t * ∑ i, g (v i)) = ∏ i, Real.exp (t * g (v i)) := by
    intro v; rw [Finset.mul_sum, Real.exp_sum]
  calc P.real (T ∩ {v | θ ≤ ∑ i, g (v i)})
      = ∫ v in T, Set.indicator {v | θ ≤ ∑ i, g (v i)} (fun _ => (1 : ℝ)) v ∂P := by
        rw [integral_indicator hD, setIntegral_const, smul_eq_mul, mul_one, Measure.real,
          Measure.real, Measure.restrict_apply hD, Set.inter_comm]
    _ ≤ ∫ v in T, Real.exp (-(t * θ)) * ∏ i, Real.exp (t * g (v i)) ∂P := by
        refine setIntegral_mono_on ((integrable_const (1 : ℝ)).indicator hD |>.integrableOn
          |> fun h => h) (hIT.const_mul _) hT fun v _ => ?_
        by_cases hv : θ ≤ ∑ i, g (v i)
        · rw [Set.indicator_of_mem (show v ∈ {v | θ ≤ ∑ i, g (v i)} from hv), ← hexp, ← Real.exp_add]
          exact Real.one_le_exp (by nlinarith)
        · rw [Set.indicator_of_notMem (show v ∉ {v | θ ≤ ∑ i, g (v i)} from hv)]; positivity
    _ = _ := by rw [integral_const_mul, hint]

/-- **Hoeffding's lemma on a finite measure** (normalised): if `a ≤ g ≤ b` `ν`-a.e. and `t > 0`, then
`∫ e^{t g} dν ≤ ν(E) · exp(t · avg_ν g + t² (b - a)² / 8)`. -/
lemma lintegral_exp_hoeffding {E : Type*} [MeasurableSpace E] (ν : Measure E) [IsFiniteMeasure ν]
    (hν : 0 < ν.real Set.univ) (g : E → ℝ) (hgm : Measurable g) {a b : ℝ}
    (hg : ∀ᵐ x ∂ν, g x ∈ Set.Icc a b) {t : ℝ} (ht : 0 < t) :
    ∫ x, Real.exp (t * g x) ∂ν ≤
      ν.real Set.univ * Real.exp (t * ((∫ x, g x ∂ν) / ν.real Set.univ) + t ^ 2 * (b - a) ^ 2 / 8) := by
  set Z := ν.real Set.univ with hZ
  have hZ0 : ν Set.univ ≠ 0 := by
    intro h; rw [hZ, Measure.real, h] at hν; simp at hν
  set c : Measure E := (ν Set.univ)⁻¹ • ν with hc
  haveI : IsProbabilityMeasure c := by
    constructor; rw [hc, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hZ0 (measure_ne_top _ _)]
  have hint : ∀ f : E → ℝ, ∫ x, f x ∂c = (∫ x, f x ∂ν) / Z := by
    intro f
    rw [hc, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul, hZ, Measure.real]
    ring
  set m := ∫ x, g x ∂c with hm
  have hgc : ∀ᵐ x ∂c, g x - m ∈ Set.Icc (a - m) (b - m) := by
    have : c ≪ ν := Measure.smul_absolutelyContinuous
    filter_upwards [this.ae_le hg] with x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hbd : ∀ᵐ x ∂c, g x ∈ Set.Icc a b := Measure.smul_absolutelyContinuous.ae_le hg
  have hgint : Integrable g c := by
    refine Integrable.of_bound hgm.aestronglyMeasurable (max |a| |b|) ?_
    filter_upwards [hbd] with x hx
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := le_max_left |a| |b|; have := neg_abs_le a; linarith [hx.1]
    · have := le_max_right |a| |b|; have := le_abs_self b; linarith [hx.2]
  have hc0 : ∫ x, (g x - m) ∂c = 0 := by
    rw [integral_sub hgint (integrable_const m), integral_const]; simp [hm]
  have hH := ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero (X := fun x => g x - m)
    ((hgm.sub measurable_const).aemeasurable) hgc hc0 ht
  have hnn : ((‖(b - m) - (a - m)‖₊ : ℝ) / 2) ^ 2 * t ^ 2 / 2 = t ^ 2 * (b - a) ^ 2 / 8 := by
    rw [coe_nnnorm, Real.norm_eq_abs, show (b - m) - (a - m) = b - a by ring, div_pow, sq_abs]; ring
  rw [hnn] at hH
  unfold ProbabilityTheory.mgf at hH
  have heq : ∫ x, Real.exp (t * g x) ∂ν = Z * Real.exp (t * m) * ∫ x, Real.exp (t * (g x - m)) ∂c := by
    rw [hint (fun x => Real.exp (t * (g x - m)))]
    have hx : ∀ x, Real.exp (t * (g x - m)) = Real.exp (t * g x) * Real.exp (-(t * m)) := fun x => by
      rw [← Real.exp_add]; ring_nf
    simp_rw [hx, integral_mul_const]
    have hZ' : Z ≠ 0 := hν.ne'
    field_simp
    rw [mul_assoc, ← Real.exp_add]; simp
  rw [heq, show (∫ x, g x ∂ν) / Z = m from (hint g).symm, Real.exp_add, ← mul_assoc]
  have hZpos : 0 < Z * Real.exp (t * m) := by positivity
  exact mul_le_mul_of_nonneg_left hH hZpos.le

/-- **Hoeffding given the type**: with `a ≤ g ≤ b` on every cell and cell averages `avg_j`,
`μ^N(T ∩ {Σ g(v_i) ≥ Σ_j n_j avg_j + N η}) ≤ μ^N(T) · e^{-2 N η² / (b-a)²}`. -/
theorem type_event_hoeffding (hI : ∀ j, MeasurableSet (I j))
    (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) {n : Fin k → ℕ} (hn : ∑ j, n j = N)
    (hpos : ∀ j, 0 < μ.real (I j)) (g : E → ℝ) (hgm : Measurable g) {a b : ℝ} (hab : a < b)
    (hg : ∀ j, ∀ x ∈ I j, g x ∈ Set.Icc a b) {η : ℝ} (hη : 0 < η) :
    (Measure.pi fun _ => μ).real
        ({v : Fin N → E | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} ∩
          {v | ∑ j, (n j : ℝ) * ((∫ x in I j, g x ∂μ) / μ.real (I j)) + N * η ≤ ∑ i, g (v i)}) ≤
      (Measure.pi fun _ => μ).real {v : Fin N → E | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} *
        Real.exp (-(2 * N * η ^ 2 / (b - a) ^ 2)) := by
  set R := b - a with hR
  have hR0 : 0 < R := by simp only [hR]; linarith
  set t := 4 * η / R ^ 2 with ht
  have ht0 : 0 < t := by positivity
  set avg : Fin k → ℝ := fun j => (∫ x in I j, g x ∂μ) / μ.real (I j) with havg
  set θ := ∑ j, (n j : ℝ) * avg j + N * η with hθ
  have hgi : ∀ j, IntegrableOn (fun x => Real.exp (t * g x)) (I j) μ := by
    intro j
    refine Measure.integrableOn_of_bounded (M := Real.exp (t * b)) (measure_ne_top _ _)
      ((hgm.const_mul t).exp.aestronglyMeasurable) ?_
    refine (ae_restrict_iff' (hI j)).2 (Filter.Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hg j x hx).2 ht0.le)
  have hdev := type_event_dev μ I hI hdisj hn g hgm ht0.le hgi θ
  have hcell : ∀ j, ∫ x in I j, Real.exp (t * g x) ∂μ ≤
      μ.real (I j) * Real.exp (t * avg j + t ^ 2 * R ^ 2 / 8) := by
    intro j
    have hν : 0 < (μ.restrict (I j)).real Set.univ := by
      rw [Measure.real, Measure.restrict_apply_univ]; exact hpos j
    have h := lintegral_exp_hoeffding (μ.restrict (I j)) hν g hgm
      ((ae_restrict_iff' (hI j)).2 (Filter.Eventually.of_forall fun x hx => hg j x hx)) ht0
    have hr : (μ.restrict (I j)).real Set.univ = μ.real (I j) := by
      rw [Measure.real, Measure.restrict_apply_univ]; rfl
    rw [hr] at h
    exact h
  have hprod : ∏ j, (∫ x in I j, Real.exp (t * g x) ∂μ) ^ n j ≤
      (∏ j, μ.real (I j) ^ n j) * Real.exp (t * ∑ j, (n j : ℝ) * avg j + t ^ 2 * R ^ 2 / 8 * N) := by
    calc ∏ j, (∫ x in I j, Real.exp (t * g x) ∂μ) ^ n j
        ≤ ∏ j, (μ.real (I j) * Real.exp (t * avg j + t ^ 2 * R ^ 2 / 8)) ^ n j :=
          Finset.prod_le_prod (fun j _ => pow_nonneg (setIntegral_nonneg (hI j)
            fun x _ => (Real.exp_pos _).le) _) fun j _ => pow_le_pow_left₀
            (setIntegral_nonneg (hI j) fun x _ => (Real.exp_pos _).le) (hcell j) _
      _ = (∏ j, μ.real (I j) ^ n j) * ∏ j, Real.exp ((n j : ℝ) * (t * avg j + t ^ 2 * R ^ 2 / 8)) := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [mul_pow, ← Real.exp_nat_mul]
      _ = _ := by
          rw [← Real.exp_sum]
          congr 2
          have hN : (∑ j, (n j : ℝ)) = N := by exact_mod_cast hn
          rw [Finset.mul_sum, ← hN, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  rw [type_event_real μ I hI hdisj hn]
  refine hdev.trans ?_
  have hfib : (0 : ℝ) ≤ fibTypeCount N k n := Nat.cast_nonneg _
  calc Real.exp (-(t * θ)) * (fibTypeCount N k n * ∏ j, (∫ x in I j, Real.exp (t * g x) ∂μ) ^ n j)
      ≤ Real.exp (-(t * θ)) * (fibTypeCount N k n * ((∏ j, μ.real (I j) ^ n j) *
          Real.exp (t * ∑ j, (n j : ℝ) * avg j + t ^ 2 * R ^ 2 / 8 * N))) := by gcongr
    _ = fibTypeCount N k n * (∏ j, μ.real (I j) ^ n j) *
          Real.exp (-(t * θ) + (t * ∑ j, (n j : ℝ) * avg j + t ^ 2 * R ^ 2 / 8 * N)) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring
    _ = _ := by
        congr 2
        simp only [hθ, ht]
        field_simp
        ring

end TypeMGF

end Census
end IIT
