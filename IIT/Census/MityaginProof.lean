import Mathlib

/-!
# Mityagin's theorem: zero sets of real-analytic functions are null

`volume_zero_set_analytic_thm`: if `f` is real analytic on an open preconnected set `U` of a
finite-dimensional real normed space and does not vanish identically on `U`, then its zero set in
`U` is null for every additive Haar measure.  (B. Mityagin, arXiv:1512.07276.)

Proof: induction on the dimension, through `F × ℝ`.
* dimension 1: every zero is isolated (principle of isolated zeros), so the zero set is discrete,
  hence countable, hence null;
* `F × ℝ`: cover `U` by countably many balls `ball x r ×ˢ ball t r`; on each, pick `(x₁, t₁)` with
  `f (x₁, t₁) ≠ 0`.  By induction, for a.e. `x`, `f (x, t₁) ≠ 0`, and then the slice
  `t ↦ f (x, t)` has a null zero set by the one-dimensional case; conclude by Fubini
  (`measure_prod_null`);
* transport along continuous linear equivalences, and uniqueness of Haar measure up to scalars.

Self-contained: imports only Mathlib.
-/

open MeasureTheory Set Filter Topology Metric

namespace IIT.Census

/-- The statement of Mityagin's theorem for a given space. -/
def MityaginProp (G : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G] :
    Prop :=
  ∀ (μ : Measure G) [μ.IsAddHaarMeasure] {U : Set G}, IsOpen U → IsPreconnected U →
    ∀ {f : G → ℝ}, AnalyticOnNhd ℝ f U → (∃ x ∈ U, f x ≠ 0) → μ {x ∈ U | f x = 0} = 0

lemma measurableSet_zero_of_continuousOn {G : Type*} [TopologicalSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] {U : Set G} (hU : IsOpen U) {f : G → ℝ} (hf : ContinuousOn f U) :
    MeasurableSet {x ∈ U | f x = 0} := by
  have : {x ∈ U | f x = 0} = U \ (U ∩ f ⁻¹' {0}ᶜ) := by
    ext x; simp only [mem_ofPred_eq, Set.mem_sdiff, mem_inter_iff, mem_preimage, mem_compl_iff,
      mem_singleton_iff]; tauto
  rw [this]
  exact hU.measurableSet.diff (hf.isOpen_inter_preimage hU isOpen_compl_singleton).measurableSet

/-- One-dimensional case: the zero set is countable. -/
lemma one_dim {U : Set ℝ} (hc : IsPreconnected U) {g : ℝ → ℝ} (hg : AnalyticOnNhd ℝ g U)
    (hne : ∃ x ∈ U, g x ≠ 0) : volume {x ∈ U | g x = 0} = 0 := by
  apply Set.Countable.measure_zero _ volume
  have hd : IsDiscrete {x ∈ U | g x = 0} := by
    rw [isDiscrete_iff_nhdsNE]
    intro z hz
    rcases (hg z hz.1).eventually_eq_zero_or_eventually_ne_zero with h | h
    · obtain ⟨x, hx, hgx⟩ := hne
      exact absurd (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hz.1 h hx) hgx
    · rw [inf_principal_eq_bot]
      exact mem_of_superset h fun w hw hwZ => hw hwZ.2
  exact (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hd

section Step

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

omit [FiniteDimensional ℝ F] in
/-- The local piece: on a product `V ×ˢ I ⊆ U` of preconnected open sets on which `f` is not
identically zero, the zero set is null (Fubini + induction + one-dimensional case). -/
lemma local_piece (hF : MityaginProp F) (μ : Measure F) [μ.IsAddHaarMeasure]
    {U : Set (F × ℝ)} (hU : IsOpen U) {f : F × ℝ → ℝ} (hf : AnalyticOnNhd ℝ f U)
    {V : Set F} {I : Set ℝ} (hV : IsOpen V) (hVc : IsPreconnected V) (hI : IsOpen I)
    (hIc : IsPreconnected I) (hVI : V ×ˢ I ⊆ U) {x₀ : F} {t₀ : ℝ} (hx₀ : x₀ ∈ V) (ht₀ : t₀ ∈ I)
    (hne : f (x₀, t₀) ≠ 0) :
    (μ.prod volume) ({p ∈ U | f p = 0} ∩ V ×ˢ I) = 0 := by
  have hmeas : MeasurableSet ({p ∈ U | f p = 0} ∩ V ×ˢ I) :=
    (measurableSet_zero_of_continuousOn hU hf.continuousOn).inter (hV.prod hI).measurableSet
  rw [Measure.measure_prod_null hmeas]
  have hN : μ {x ∈ V | f (x, t₀) = 0} = 0 :=
    hF μ hV hVc (f := fun x => f (x, t₀))
      (fun x hx => (hf _ (hVI ⟨hx, ht₀⟩)).comp (analyticAt_id.prod analyticAt_const))
      ⟨x₀, hx₀, hne⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with x hx
  simp only [Pi.zero_apply]
  by_cases hxV : x ∈ V
  · have hne' : f (x, t₀) ≠ 0 := fun h => hx ⟨hxV, h⟩
    refine measure_mono_null ?_ (one_dim hIc (g := fun t => f (x, t))
      (fun t ht => (hf _ (hVI ⟨hxV, ht⟩)).comp (analyticAt_const.prod analyticAt_id))
      ⟨t₀, ht₀, hne'⟩)
    intro t ht
    exact ⟨ht.2.2, ht.1.2⟩
  · convert measure_empty (μ := (volume : Measure ℝ))
    ext t
    simp [hxV]

/-- The inductive step: Mityagin for `F` implies Mityagin for `F × ℝ`. -/
lemma prod_step (hF : MityaginProp F) : MityaginProp (F × ℝ) := by
  intro ν _ U hU hc f hf hne
  set ρ : Measure (F × ℝ) := (Measure.addHaar : Measure F).prod volume
  rw [Measure.isAddLeftInvariant_eq_smul ν ρ, Measure.smul_apply]
  suffices h : ρ {x ∈ U | f x = 0} = 0 by rw [h, smul_zero]
  have hnl : ∀ p ∈ U, ¬ (f =ᶠ[𝓝 p] 0) := fun p hp h => by
    obtain ⟨x, hx, hfx⟩ := hne
    exact hfx (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hp h hx)
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i : {q : (F × ℝ) × ℝ // 0 < q.2 ∧ ball q.1 q.2 ⊆ U} => ball i.1.1 i.1.2)
    (fun _ => isOpen_ball)
  have hcov : {x ∈ U | f x = 0} ⊆
      ⋃ i ∈ T, ({x ∈ U | f x = 0} ∩ ball (i : (F × ℝ) × ℝ).1 (i : (F × ℝ) × ℝ).2) := by
    intro p hp
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU p hp.1
    have : p ∈ ⋃ i ∈ T, ball (i : (F × ℝ) × ℝ).1 (i : (F × ℝ) × ℝ).2 := by
      rw [hTU]; exact mem_iUnion.2 ⟨⟨(p, r), hr, hrU⟩, mem_ball_self hr⟩
    simp only [mem_iUnion] at this ⊢
    obtain ⟨i, hi, hpi⟩ := this
    exact ⟨i, hi, hp, hpi⟩
  refine measure_mono_null hcov ((measure_biUnion_null_iff hT).2 fun i _ => ?_)
  rcases i with ⟨⟨⟨x₀, t₀⟩, r⟩, hr, hsub⟩
  simp only at hr hsub ⊢
  rw [← ball_prod_same] at hsub ⊢
  have : ∃ q ∈ ball x₀ r ×ˢ ball t₀ r, f q ≠ 0 := by
    by_contra h
    push Not at h
    exact hnl (x₀, t₀) (hsub ⟨mem_ball_self hr, mem_ball_self hr⟩)
      (Filter.eventually_of_mem (prod_mem_nhds (ball_mem_nhds x₀ hr) (ball_mem_nhds t₀ hr)) h)
  obtain ⟨⟨x₁, t₁⟩, ⟨hx₁, ht₁⟩, hq⟩ := this
  exact local_piece hF _ hU hf isOpen_ball (convex_ball _ _).isPreconnected isOpen_ball
    (convex_ball _ _).isPreconnected hsub hx₁ ht₁ hq

end Step

/-- Transport along a continuous linear equivalence. -/
lemma MityaginProp.transport {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
    (e : E ≃L[ℝ] G) (hG : MityaginProp G) : MityaginProp E := by
  intro μ _ U hU hc f hf hne
  have key := hG (μ.map e) (U := e.symm ⁻¹' U) (hU.preimage e.symm.continuous)
    (e.symm.toHomeomorph.isPreconnected_preimage.2 hc) (f := f ∘ e.symm)
    (fun y hy => (hf _ hy).comp ((e.symm : G →L[ℝ] E).analyticAt y))
    (by obtain ⟨x, hx, h⟩ := hne; exact ⟨e x, by simpa using hx, by simpa using h⟩)
  have h2 := MeasurableEquiv.map_apply (e.toHomeomorph.toMeasurableEquiv) (μ := μ)
    (e.symm ⁻¹' {x ∈ U | f x = 0})
  have h3 : ⇑e.toHomeomorph.toMeasurableEquiv ⁻¹' (e.symm ⁻¹' {x ∈ U | f x = 0}) =
      {x ∈ U | f x = 0} := by
    ext x; simp
  rw [h3] at h2
  rw [← h2]
  exact key

theorem mityagin_fin : ∀ n : ℕ, MityaginProp (Fin n → ℝ)
  | 0 => by
    intro μ _ U _ _ f _ hne
    obtain ⟨x, _, hfx⟩ := hne
    have : {y ∈ U | f y = 0} = ∅ :=
      eq_empty_iff_forall_notMem.2 fun y hy => hfx (Subsingleton.elim y x ▸ hy.2)
    rw [this, measure_empty]
  | n + 1 =>
    MityaginProp.transport (ContinuousLinearEquiv.ofFinrankEq (by simp))
      (prod_step (mityagin_fin n))

/-- **Mityagin's theorem.** -/
theorem volume_zero_set_analytic_thm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E)
    [μ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U) {f : E → ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hne : ∃ x ∈ U, f x ≠ 0) : μ {x ∈ U | f x = 0} = 0 :=
  MityaginProp.transport (ContinuousLinearEquiv.ofFinrankEq (by simp) :
    E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ)) (mityagin_fin _) μ hU hc hf hne

end IIT.Census
