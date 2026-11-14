/-
Census of IIT 2.0: the product probability space `[0,1]^(Fin N × State N)`, independence of
functions of disjoint sets of coordinates, single- and two-coordinate integrals.
-/
import IIT2.Census.GoodEvent
import IIT2.Census.Constants

namespace IIT2

open MeasureTheory ProbabilityTheory Finset Real

/-- The flat parameter space. -/
abbrev Ωf (N : ℕ) := Fin N × State N → ℝ

/-- The uniform distribution on `[0,1]`. -/
noncomputable def unif : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unif := ⟨by simp [unif]⟩

/-- The product measure on the flat parameter space. -/
noncomputable def μP (N : ℕ) : Measure (Ωf N) := Measure.pi (fun _ => unif)

instance (N : ℕ) : IsProbabilityMeasure (μP N) := by unfold μP; infer_instance

/-- Clamp to `[0,1]`. -/
noncomputable def clamp (u : ℝ) : ℝ := max 0 (min 1 u)

lemma clamp_nonneg (u : ℝ) : 0 ≤ clamp u := le_max_left _ _
lemma clamp_le_one (u : ℝ) : clamp u ≤ 1 := max_le zero_le_one (min_le_left _ _)
lemma clamp_of_mem {u : ℝ} (h : u ∈ Set.Icc (0 : ℝ) 1) : clamp u = u := by
  unfold clamp; rw [min_eq_right h.2, max_eq_right h.1]
lemma continuous_clamp : Continuous clamp :=
  continuous_const.max (continuous_const.min continuous_id)
lemma measurable_clamp : Measurable clamp := continuous_clamp.measurable

variable {N : ℕ}

/-- Aligned probabilities read off a parameter. -/
noncomputable def qω (ω : Ωf N) : Fin N → State N → ℝ := fun l c => clamp (ω (l, c))

/-- `f` depends only on the coordinates in `A`. -/
def DepC (A : Finset (Fin N × State N)) (f : Ωf N → ℝ) : Prop :=
  ∀ ω ω' : Ωf N, (∀ p ∈ A, ω p = ω' p) → f ω = f ω'

lemma DepC.mono {A B : Finset (Fin N × State N)} (h : A ⊆ B) {f : Ωf N → ℝ} (hf : DepC A f) :
    DepC B f := fun ω ω' hw => hf ω ω' fun p hp => hw p (h hp)

lemma iIndep_coords : iIndepFun (fun (p : Fin N × State N) (ω : Ωf N) => ω p) (μP N) := by
  have := iIndepFun_pi (μ := fun _ : Fin N × State N => unif) (X := fun _ x => x)
    (fun _ => measurable_id.aemeasurable)
  exact this

/-- Extension by zero of a family indexed by `A`. -/
noncomputable def extA (A : Finset (Fin N × State N)) (v : A → ℝ) : Ωf N :=
  fun p => if h : p ∈ A then v ⟨p, h⟩ else 0

lemma measurable_extA (A : Finset (Fin N × State N)) : Measurable (extA A) := by
  refine measurable_pi_iff.mpr fun p => ?_
  unfold extA
  by_cases h : p ∈ A
  · simp only [h, dite_true]; exact measurable_pi_apply _
  · simp only [h, dite_false]; exact measurable_const

lemma DepC.factor {A : Finset (Fin N × State N)} {f : Ωf N → ℝ} (hf : DepC A f) :
    f = (f ∘ extA A) ∘ (fun ω (i : A) => ω i) := by
  funext ω
  refine hf _ _ fun p hp => ?_
  simp [extA, hp]

/-- Functions of disjoint sets of coordinates are independent. -/
theorem indepFun_of_depC {A B : Finset (Fin N × State N)} (hAB : Disjoint A B)
    {f g : Ωf N → ℝ} (hfm : Measurable f) (hgm : Measurable g) (hf : DepC A f) (hg : DepC B g) :
    IndepFun f g (μP N) := by
  have h2 := iIndep_coords.indepFun_finset A B hAB (fun p => measurable_pi_apply p)
  have h3 := h2.comp (hfm.comp (measurable_extA A)) (hgm.comp (measurable_extA B))
  rw [hf.factor, hg.factor]
  exact h3

lemma integral_mul_of_depC {A B : Finset (Fin N × State N)} (hAB : Disjoint A B)
    {f g : Ωf N → ℝ} (hfm : Measurable f) (hgm : Measurable g) (hf : DepC A f) (hg : DepC B g) :
    ∫ ω, f ω * g ω ∂(μP N) = (∫ ω, f ω ∂(μP N)) * ∫ ω, g ω ∂(μP N) :=
  (indepFun_of_depC hAB hfm hgm hf hg).integral_mul_eq_mul_integral
    hfm.aestronglyMeasurable hgm.aestronglyMeasurable

/-- Coordinates of unit `l`. -/
def unitSet (l : Fin N) : Finset (Fin N × State N) := Finset.univ.filter (fun p => p.1 = l)

lemma unitSet_disjoint_biUnion {a : Fin N} {s : Finset (Fin N)} (ha : a ∉ s) :
    Disjoint (unitSet a) (s.biUnion unitSet) := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  obtain ⟨l, hl, hpl⟩ := Finset.mem_biUnion.mp hp'
  simp only [unitSet, Finset.mem_filter] at hp hpl
  exact ha (hp.2 ▸ hpl.2 ▸ hl)

/-- Product over units of functions each depending only on its unit: expectations factorize. -/
theorem integral_prod_units (s : Finset (Fin N)) (F : Fin N → Ωf N → ℝ)
    (hm : ∀ l, Measurable (F l)) (hd : ∀ l, DepC (unitSet l) (F l)) :
    ∫ ω, (∏ l ∈ s, F l ω) ∂(μP N) = ∏ l ∈ s, ∫ ω, F l ω ∂(μP N) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    have hdep : DepC (s.biUnion unitSet) (fun ω => ∏ l ∈ s, F l ω) := fun ω ω' hw =>
      Finset.prod_congr rfl fun l hl => hd l ω ω' fun p hp =>
        hw p (Finset.mem_biUnion.mpr ⟨l, hl, hp⟩)
    rw [integral_mul_of_depC (unitSet_disjoint_biUnion ha) (hm a)
      (Finset.measurable_prod _ fun l _ => hm l) (hd a) hdep, ih]

lemma integrable_of_bdd {f : Ωf N → ℝ} (hf : Measurable f) (C : ℝ) (h : ∀ ω, |f ω| ≤ C) :
    Integrable f (μP N) :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]; exact h ω)

/-- Integral of a function of one clamped coordinate. -/
lemma integral_unif_clamp (g : ℝ → ℝ) : ∫ u, g (clamp u) ∂unif = ∫ u in (0 : ℝ)..1, g u := by
  unfold unif
  rw [setIntegral_congr_fun measurableSet_Icc (g := g) (fun u hu => by rw [clamp_of_mem hu])]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]

lemma integral_coord (p : Fin N × State N) (g : ℝ → ℝ) (hg : Measurable g) :
    ∫ ω, g (ω p) ∂(μP N) = ∫ u, g u ∂unif := by
  have hmp := measurePreserving_eval (fun _ : Fin N × State N => unif) p
  rw [← hmp.map_eq, integral_map (measurable_pi_apply p).aemeasurable hg.aestronglyMeasurable]
  rfl

lemma integral_coord_clamp (p : Fin N × State N) (g : ℝ → ℝ) (hg : Measurable g) :
    ∫ ω, g (clamp (ω p)) ∂(μP N) = ∫ u in (0 : ℝ)..1, g u := by
  rw [integral_coord p (fun u => g (clamp u)) (hg.comp measurable_clamp), integral_unif_clamp]

/-- Integral of a bounded function of two distinct clamped coordinates. -/
lemma integral_two_coords {p₁ p₂ : Fin N × State N} (hne : p₁ ≠ p₂) (g : ℝ → ℝ → ℝ)
    (hg : Measurable (Function.uncurry g)) (C : ℝ) (hC : ∀ u v, |g (clamp u) (clamp v)| ≤ C) :
    ∫ ω, g (clamp (ω p₁)) (clamp (ω p₂)) ∂(μP N) =
      ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, g u v := by
  have hind : IndepFun (fun ω : Ωf N => ω p₁) (fun ω => ω p₂) (μP N) :=
    indepFun_of_depC (A := {p₁}) (B := {p₂}) (Finset.disjoint_singleton.mpr hne)
      (measurable_pi_apply p₁) (measurable_pi_apply p₂)
      (fun ω ω' h => h p₁ (Finset.mem_singleton_self _))
      (fun ω ω' h => h p₂ (Finset.mem_singleton_self _))
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply p₁).aemeasurable
    (measurable_pi_apply p₂).aemeasurable).mp hind
  have e1 : Measure.map (fun f : Ωf N => f p₁) (μP N) = unif :=
    (measurePreserving_eval (fun _ : Fin N × State N => unif) p₁).map_eq
  have e2 : Measure.map (fun f : Ωf N => f p₂) (μP N) = unif :=
    (measurePreserving_eval (fun _ : Fin N × State N => unif) p₂).map_eq
  rw [e1, e2] at hmap
  set G : ℝ × ℝ → ℝ := fun z => g (clamp z.1) (clamp z.2)
  have hGm : Measurable G :=
    hg.comp ((measurable_clamp.comp measurable_fst).prodMk (measurable_clamp.comp measurable_snd))
  have : ∫ ω, g (clamp (ω p₁)) (clamp (ω p₂)) ∂(μP N) = ∫ z, G z ∂(unif.prod unif) := by
    rw [← hmap, integral_map ((measurable_pi_apply p₁).prodMk
      (measurable_pi_apply p₂)).aemeasurable hGm.aestronglyMeasurable]
  rw [this]
  have hint : Integrable G (unif.prod unif) :=
    Integrable.of_bound hGm.aestronglyMeasurable C (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]; exact hC _ _)
  rw [integral_prod G hint]
  simp only [G]
  have : ∀ u, ∫ v, g (clamp u) (clamp v) ∂unif = ∫ v in (0 : ℝ)..1, g (clamp u) v := fun u =>
    integral_unif_clamp (g (clamp u))
  simp_rw [this]
  exact integral_unif_clamp (fun a => ∫ v in (0 : ℝ)..1, g a v)

end IIT2
