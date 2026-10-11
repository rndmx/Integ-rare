/-
Census of complexes, B1 development, module A3 (`B1-BLUEPRINT.md`, Sections 2-3 and module A3):
the measure infrastructure of the B1 argument.

Contents.
1. Two-factor tools on `α × β` (`μ ⊗ ν`, with `ν` the law of the resampled block):
   `prod_resample_eq` (the resampling identity `P(A(f,r) ∩ B(f,r')) = ∫ ν(A_f) ν(B_f)`),
   `prod_resample_eq_mul` (`= ν(A') P(B)` when `A` only reads the resampled block), the marginals
   `prod_marginal_one/two`, **`resample_le`**, **`fubini_window`** (+ `fubini_window_div`), and the
   partition identity `measure_eq_sum_partition`.
2. Abstract replacement maps `repl : Ω → Ω → Ω` pushing `μ ⊗ μ` to `μ` (conditioning on the
   complement of a block, independence, finite products, product bound given the rest).
3. Coordinate blocks of a finite product `Measure.pi ν` (`replS`, `DetOn`): independence of
   events determined by disjoint coordinate sets (`pi_inter_eq_mul_of_detOn`,
   `pi_iInter_eq_prod_of_detOn`), **the product bound for events on disjoint private coordinate
   sets given the rest** (`pi_prod_bound_private`), and **the stopping-set lemmas**
   (`stopping_set_indep`, `stopping_set_iid`, `stopping_sum`, `stopping_le`).
4. Rows of `cubeM`: **`cubeM_split_rows`** (`MeasurableEquiv.piEquivPiSubtypeProd`), gluing
   (`glueRows`), Fubini/conditioning over the rows outside a row set (`cubeM_eq_lintegral_rows`,
   `cubeM_inter_restrIn_eq/le`), the cube-level resampling (`cubeM_resample_le`,
   `cubeM_resample_bound`), and the specialisation to the sensitive rows (`sensM`, `freshM`,
   `b1Glue`, `b1Glue_mem_GoodF_iff`, ...).
5. Entries of `cubeM` (`entM`, `replE`, `DetOnE`): the same statements for sets of entries
   (`cubeM_inter_eq_mul_of_detOnE`, `cubeM_prod_bound_private`, `cubeM_stopping_set_iid`, ...)
   and the one-entry Fubini window `cubeM_fubini_window`.
6. `sum_over_argmax`.

Deviations from the blueprint (A3), all minimal:
* NAME: `glue` already exists in `IIT.Census` (`ColSplit.lean`, the COLUMN gluing
  `glue i c ρ`).  The row gluing is therefore `glueRows F f g` (any row set `F`), with
  `b1Glue f g := glueRows (sensRows s r0) f g`; the laws are `rowsInM F`, `rowsOutM F`, with
  `sensM N s r0 := rowsInM (sensRows s r0)` and `freshM N s r0 := rowsOutM (sensRows s r0)`
  (the `freshM` of module D3).  So D3's `glue f g` must be read as `b1Glue f g`.
* `resample_le` needs `A`, `B`, `Stab` measurable (for non-measurable `A` the inequality
  `(μ ⊗ ν)(S) ≤ ∫ ν(S_f)` is not available).  `SmallW` is NOT known to be measurable
  (B1Defs header), so E1 must apply it to a measurable superset of `SmallW ∩ B` whose sections
  are still bounded (e.g. the complement of the count event of D3).  `μ` only needs to be
  s-finite, `ν` a probability measure.
* `stopping_set_iid` is stated for any finite index type, any coordinate type `E` and any
  probability measures `ν i` (the uniform case is `ν i = unif`).  "`{P = A}` measurable w.r.t. the
  coordinates outside `A`" is formalised as `P ω = A ↔ ω|_{Aᶜ} ∈ G` for a set `G` of
  `Aᶜ`-configurations (then NO measurability is needed at all).  Also given: the version with
  "determined by" hypotheses (`DetOn`, `stopping_set_indep`) and the random-set sums
  (`stopping_sum`, `stopping_le`: given the stopping set, the entries on it are iid).
* `fubini_window`: the hypothesis "section of `B` has measure `≥ c · 1[section ≠ ∅]`" is used in
  the (weaker, hence more general) form "section measure `≠ 0 → ≥ c`"; the conclusion is
  `c · μ(B ∩ W) ≤ δ · μ(B)` (and `≤ (δ/c) μ(B)` for `c ≠ 0, ∞`).  The cube version measures the
  section of one entry with `unif` (Lebesgue measure on `[0,1]`, `unif_apply`).
* `sum_over_argmax` holds for EVERY set `B` (no measurability), as an equality of the sum.
-/
import IIT.Census.B1Defs
import IIT.Census.ColSplit
import IIT.Census.PairIndep
import IIT.Census.UnivProb

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

noncomputable section

/-- `Measure.pi` does not depend on the `Fintype` instance of the index type (two instances on
`↥A` occur: `Finset.Subtype.fintype` and `Subtype.fintype`). -/
lemma b1p_pi_fintype_irrel {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) (h1 h2 : Fintype ι) :
    @Measure.pi ι α h1 _ μ = @Measure.pi ι α h2 _ μ := by
  cases Subsingleton.elim h1 h2; rfl

/-! ## 1. Two-factor tools on `α × β` -/

section TwoFactor

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma b1p_meas_fst_snd1 {B : Set (α × β)} (hB : MeasurableSet B) :
    MeasurableSet {x : α × β × β | (x.1, x.2.1) ∈ B} :=
  hB.preimage (measurable_fst.prodMk (measurable_fst.comp measurable_snd))

lemma b1p_meas_fst_snd2 {B : Set (α × β)} (hB : MeasurableSet B) :
    MeasurableSet {x : α × β × β | (x.1, x.2.2) ∈ B} :=
  hB.preimage (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

/-- **Resampling identity.** With `(f, r, r')` distributed as `μ ⊗ ν ⊗ ν`, the probability that
`(f, r) ∈ A` and `(f, r') ∈ B` is the average over `f` of the product of the section measures. -/
theorem prod_resample_eq (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {A B : Set (α × β)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (μ.prod (ν.prod ν)) {x | (x.1, x.2.1) ∈ A ∧ (x.1, x.2.2) ∈ B} =
      ∫⁻ f, ν {r | (f, r) ∈ A} * ν {r | (f, r) ∈ B} ∂μ := by
  have hm : MeasurableSet {x : α × β × β | (x.1, x.2.1) ∈ A ∧ (x.1, x.2.2) ∈ B} :=
    (b1p_meas_fst_snd1 hA).inter (b1p_meas_fst_snd2 hB)
  rw [Measure.prod_apply hm]
  refine lintegral_congr fun f => ?_
  have : Prod.mk f ⁻¹' {x : α × β × β | (x.1, x.2.1) ∈ A ∧ (x.1, x.2.2) ∈ B} =
      {r | (f, r) ∈ A} ×ˢ {r | (f, r) ∈ B} := by
    ext p; simp
  rw [this, Measure.prod_prod]

/-- The law of `(f, r)` under `μ ⊗ ν ⊗ ν` is `μ ⊗ ν`. -/
theorem prod_marginal_one (μ : Measure α) (ν : Measure β) [SFinite μ] [IsProbabilityMeasure ν]
    {B : Set (α × β)} (hB : MeasurableSet B) :
    (μ.prod (ν.prod ν)) {x | (x.1, x.2.1) ∈ B} = μ.prod ν B := by
  rw [Measure.prod_apply (b1p_meas_fst_snd1 hB), Measure.prod_apply hB]
  refine lintegral_congr fun f => ?_
  have : Prod.mk f ⁻¹' {x : α × β × β | (x.1, x.2.1) ∈ B} = {r | (f, r) ∈ B} ×ˢ Set.univ := by
    ext p; simp
  rw [this, Measure.prod_prod, measure_univ, mul_one]
  rfl

/-- The law of `(f, r')` under `μ ⊗ ν ⊗ ν` is `μ ⊗ ν`. -/
theorem prod_marginal_two (μ : Measure α) (ν : Measure β) [SFinite μ] [IsProbabilityMeasure ν]
    {B : Set (α × β)} (hB : MeasurableSet B) :
    (μ.prod (ν.prod ν)) {x | (x.1, x.2.2) ∈ B} = μ.prod ν B := by
  rw [Measure.prod_apply (b1p_meas_fst_snd2 hB), Measure.prod_apply hB]
  refine lintegral_congr fun f => ?_
  have : Prod.mk f ⁻¹' {x : α × β × β | (x.1, x.2.2) ∈ B} = Set.univ ×ˢ {r | (f, r) ∈ B} := by
    ext p; simp
  rw [this, Measure.prod_prod, measure_univ, one_mul]
  rfl

/-- **Resampling identity, product form.** If `A` only reads the first copy `r` of the resampled
block, then `P(r ∈ A' ∧ (f, r') ∈ B) = ν(A') · P(B)`. -/
theorem prod_resample_eq_mul (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {A' : Set β} {B : Set (α × β)} (hA' : MeasurableSet A') (hB : MeasurableSet B) :
    (μ.prod (ν.prod ν)) {x | x.2.1 ∈ A' ∧ (x.1, x.2.2) ∈ B} = ν A' * μ.prod ν B := by
  have hm : MeasurableSet {x : α × β × β | x.2.1 ∈ A' ∧ (x.1, x.2.2) ∈ B} :=
    (hA'.preimage (measurable_fst.comp measurable_snd)).inter (b1p_meas_fst_snd2 hB)
  rw [Measure.prod_apply hm, Measure.prod_apply hB,
    ← lintegral_const_mul _ (measurable_measure_prodMk_left hB)]
  refine lintegral_congr fun f => ?_
  have : Prod.mk f ⁻¹' {x : α × β × β | x.2.1 ∈ A' ∧ (x.1, x.2.2) ∈ B} =
      A' ×ˢ {r | (f, r) ∈ B} := by
    ext p; simp
  rw [this, Measure.prod_prod]
  rfl

/-- **Resampling identity, product form (second copy).** If `B` only reads the second copy `r'`,
then `P((f, r) ∈ A ∧ r' ∈ B') = P(A) · ν(B')`. -/
theorem prod_resample_eq_mul' (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {A : Set (α × β)} {B' : Set β} (hA : MeasurableSet A) (hB' : MeasurableSet B') :
    (μ.prod (ν.prod ν)) {x | (x.1, x.2.1) ∈ A ∧ x.2.2 ∈ B'} = μ.prod ν A * ν B' := by
  have hm : MeasurableSet {x : α × β × β | (x.1, x.2.1) ∈ A ∧ x.2.2 ∈ B'} :=
    (b1p_meas_fst_snd1 hA).inter (hB'.preimage (measurable_snd.comp measurable_snd))
  rw [Measure.prod_apply hm, Measure.prod_apply hA,
    ← lintegral_mul_const _ (measurable_measure_prodMk_left hA)]
  refine lintegral_congr fun f => ?_
  have : Prod.mk f ⁻¹' {x : α × β × β | (x.1, x.2.1) ∈ A ∧ x.2.2 ∈ B'} =
      {r | (f, r) ∈ A} ×ˢ B' := by
    ext p; simp
  rw [this, Measure.prod_prod]
  rfl

/-- The pointwise inequality behind `resample_le`: if `ν(B) ≤ ν(B)² + E` then
`ν(A ∩ B) ≤ ν(A) ν(B) + E` (for a probability measure `ν`). -/
lemma b1p_pointwise {ν : Measure β} [IsProbabilityMeasure ν] {A B : Set β} {E : ENNReal}
    (h : ν B ≤ ν B * ν B + E) : ν (A ∩ B) ≤ ν A * ν B + E := by
  by_cases hE : E = ⊤
  · rw [hE, add_top]; exact le_top
  have hAB : ν (A ∩ B) ≠ ⊤ := measure_ne_top _ _
  have hA : ν A ≠ ⊤ := measure_ne_top _ _
  have hB : ν B ≠ ⊤ := measure_ne_top _ _
  have hR : (ν B).toReal ≤ (ν B).toReal * (ν B).toReal + E.toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hB hB, hE⟩) h
    rwa [ENNReal.toReal_add (ENNReal.mul_ne_top hB hB) hE, ENNReal.toReal_mul] at this
  have hc1 : (ν (A ∩ B)).toReal ≤ (ν A).toReal :=
    ENNReal.toReal_mono hA (measure_mono Set.inter_subset_left)
  have hc2 : (ν (A ∩ B)).toReal ≤ (ν B).toReal :=
    ENNReal.toReal_mono hB (measure_mono Set.inter_subset_right)
  have hb1 : (ν B).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ν) (s := B))
    simpa using this
  have hb0 : 0 ≤ (ν B).toReal := ENNReal.toReal_nonneg
  have key : (ν (A ∩ B)).toReal ≤ (ν A).toReal * (ν B).toReal + E.toReal := by
    nlinarith [mul_le_mul_of_nonneg_right hc1 hb0,
      mul_le_mul_of_nonneg_right hc2 (sub_nonneg.2 hb1)]
  rw [← ENNReal.toReal_le_toReal hAB (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hA hB, hE⟩),
    ENNReal.toReal_add (ENNReal.mul_ne_top hA hB) hE, ENNReal.toReal_mul]
  exact key

/-- **`resample_le` (blueprint A3).** `μ, ν` with `ν` a probability measure; `A, B ⊆ α × β`;
`Stab ⊆ α × β × β` such that `(f, r) ∈ B` and `(f, r, r') ∈ Stab` imply `(f, r') ∈ B`. Then
`(μ ⊗ ν)(A ∩ B) ≤ ∫ ν(A_f) ν(B_f) dμ + (μ ⊗ ν ⊗ ν){(f, r, r') | (f, r) ∈ B, ∉ Stab}`. -/
theorem resample_le (μ : Measure α) (ν : Measure β) [SFinite μ] [IsProbabilityMeasure ν]
    {A B : Set (α × β)} {Stab : Set (α × β × β)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hS : MeasurableSet Stab)
    (hstab : ∀ f r r', (f, r) ∈ B → (f, r, r') ∈ Stab → (f, r') ∈ B) :
    (μ.prod ν) (A ∩ B) ≤ ∫⁻ f, ν {r | (f, r) ∈ A} * ν {r | (f, r) ∈ B} ∂μ +
      (μ.prod (ν.prod ν)) {x | (x.1, x.2.1) ∈ B ∧ x ∉ Stab} := by
  have hm : MeasurableSet {x : α × β × β | (x.1, x.2.1) ∈ B ∧ x ∉ Stab} :=
    (b1p_meas_fst_snd1 hB).inter hS.compl
  have hmeas : Measurable fun f => ν {r | (f, r) ∈ A} * ν {r | (f, r) ∈ B} :=
    (measurable_measure_prodMk_left hA).mul (measurable_measure_prodMk_left hB)
  have hpt : ∀ f, ν {r | (f, r) ∈ A ∩ B} ≤ ν {r | (f, r) ∈ A} * ν {r | (f, r) ∈ B} +
      (ν.prod ν) {p : β × β | (f, p.1) ∈ B ∧ (f, p) ∉ Stab} := by
    intro f
    refine b1p_pointwise (A := {r | (f, r) ∈ A}) (B := {r | (f, r) ∈ B}) ?_
    have hsub : {r | (f, r) ∈ B} ×ˢ (Set.univ : Set β) ⊆
        ({r | (f, r) ∈ B} ×ˢ {r | (f, r) ∈ B}) ∪ {p : β × β | (f, p.1) ∈ B ∧ (f, p) ∉ Stab} := by
      rintro ⟨r, r'⟩ ⟨hr, -⟩
      by_cases hst : (f, r, r') ∈ Stab
      · exact Or.inl ⟨hr, hstab f r r' hr hst⟩
      · exact Or.inr ⟨hr, hst⟩
    calc ν {r | (f, r) ∈ B} = (ν.prod ν) ({r | (f, r) ∈ B} ×ˢ (Set.univ : Set β)) := by
          rw [Measure.prod_prod, measure_univ, mul_one]
      _ ≤ (ν.prod ν) ({r | (f, r) ∈ B} ×ˢ {r | (f, r) ∈ B}) +
            (ν.prod ν) {p : β × β | (f, p.1) ∈ B ∧ (f, p) ∉ Stab} :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ = _ := by rw [Measure.prod_prod]
  calc (μ.prod ν) (A ∩ B) = ∫⁻ f, ν {r | (f, r) ∈ A ∩ B} ∂μ := Measure.prod_apply (hA.inter hB)
    _ ≤ ∫⁻ f, (ν {r | (f, r) ∈ A} * ν {r | (f, r) ∈ B} +
          (ν.prod ν) {p : β × β | (f, p.1) ∈ B ∧ (f, p) ∉ Stab}) ∂μ := lintegral_mono hpt
    _ = ∫⁻ f, ν {r | (f, r) ∈ A} * ν {r | (f, r) ∈ B} ∂μ +
          ∫⁻ f, (ν.prod ν) {p : β × β | (f, p.1) ∈ B ∧ (f, p) ∉ Stab} ∂μ :=
        lintegral_add_left hmeas _
    _ = _ := by rw [Measure.prod_apply hm]; rfl

/-- The pointwise step of the Fubini window. -/
lemma b1p_window_pt {x y c δ : ENNReal} (hxy : x ≤ y) (h1 : y ≠ 0 → c ≤ y) (h2 : x ≤ δ) :
    c * x ≤ δ * y := by
  by_cases hy : y = 0
  · have : x = 0 := nonpos_iff_eq_zero.1 (hxy.trans hy.le)
    simp [this]
  · calc c * x ≤ y * δ := mul_le_mul' (h1 hy) h2
      _ = δ * y := mul_comm _ _

/-- **`fubini_window` (blueprint A3).** If for a.e. `f` the section `B_f` has `ν`-measure
`≥ c` as soon as it is not null, and the section of `B ∩ W` has measure `≤ δ`, then
`c · (μ ⊗ ν)(B ∩ W) ≤ δ · (μ ⊗ ν)(B)`. -/
theorem fubini_window (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {B W : Set (α × β)} (hB : MeasurableSet B) (hW : MeasurableSet W) {c δ : ENNReal}
    (h : ∀ᵐ f ∂μ, (ν {r | (f, r) ∈ B} ≠ 0 → c ≤ ν {r | (f, r) ∈ B}) ∧
      ν {r | (f, r) ∈ B ∩ W} ≤ δ) :
    c * (μ.prod ν) (B ∩ W) ≤ δ * (μ.prod ν) B := by
  rw [Measure.prod_apply (hB.inter hW), Measure.prod_apply hB,
    ← lintegral_const_mul _ (measurable_measure_prodMk_left (hB.inter hW)),
    ← lintegral_const_mul _ (measurable_measure_prodMk_left hB)]
  refine lintegral_mono_ae (h.mono fun f hf => ?_)
  exact b1p_window_pt (measure_mono (Set.preimage_mono Set.inter_subset_left)) hf.1 hf.2

lemma b1p_div_of_mul_le {x y c δ : ENNReal} (hc0 : c ≠ 0) (hct : c ≠ ⊤) (h : c * x ≤ δ * y) :
    x ≤ δ / c * y := by
  calc x = c⁻¹ * (c * x) := (ENNReal.inv_mul_cancel_left hc0 hct).symm
    _ ≤ c⁻¹ * (δ * y) := by gcongr
    _ = δ / c * y := by rw [div_eq_mul_inv]; ring

/-- `fubini_window` in the form `(μ ⊗ ν)(B ∩ W) ≤ (δ / c) (μ ⊗ ν)(B)`. -/
theorem fubini_window_div (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {B W : Set (α × β)} (hB : MeasurableSet B) (hW : MeasurableSet W) {c δ : ENNReal}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (h : ∀ᵐ f ∂μ, (ν {r | (f, r) ∈ B} ≠ 0 → c ≤ ν {r | (f, r) ∈ B}) ∧
      ν {r | (f, r) ∈ B ∩ W} ≤ δ) :
    (μ.prod ν) (B ∩ W) ≤ δ / c * (μ.prod ν) B :=
  b1p_div_of_mul_le hc0 hct (fubini_window μ ν hB hW h)

end TwoFactor

/-! ### Partitions by a finite-valued measurable map -/

/-- `μ S = ∑_a μ (S ∩ {P = a})` for a measurable finite-valued `P` and ANY set `S`. -/
theorem measure_eq_sum_partition {Ω ι' : Type*} [MeasurableSpace Ω] [Fintype ι'] (μ : Measure Ω)
    {P : Ω → ι'} (hP : ∀ a, MeasurableSet {ω | P ω = a}) (S : Set Ω) :
    μ S = ∑ a, μ (S ∩ {ω | P ω = a}) := by
  have hU : (⋃ a, {ω | P ω = a}) = Set.univ := by
    ext ω; simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact ⟨P ω, rfl⟩
  have hd : Pairwise (Function.onFun Disjoint fun a => {ω | P ω = a}) := by
    intro a b hab
    exact Set.disjoint_left.2 fun ω h1 h2 => hab (h1.symm.trans h2)
  calc μ S = μ.restrict (⋃ a, {ω | P ω = a}) S := by rw [hU, Measure.restrict_univ]
    _ = (Measure.sum fun a => μ.restrict {ω | P ω = a}) S := by
        rw [Measure.restrict_iUnion hd hP]
    _ = ∑' a, μ.restrict {ω | P ω = a} S := Measure.sum_apply_of_countable _ _
    _ = ∑ a, μ (S ∩ {ω | P ω = a}) := by
        rw [tsum_fintype]
        exact Finset.sum_congr rfl fun a _ => Measure.restrict_apply' (hP a)

/-! ## 2. Abstract replacement maps -/

section Repl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ] {repl : Ω → Ω → Ω}

/-- If `(ω, η) ↦ repl ω η` pushes `μ ⊗ μ` to `μ`, then `μ S = ∫ μ{η | repl ω η ∈ S} dμ(ω)`. -/
theorem measure_eq_lintegral_repl
    (hrepl : MeasurePreserving (fun p : Ω × Ω => repl p.1 p.2) (μ.prod μ) μ)
    {S : Set Ω} (hS : MeasurableSet S) : μ S = ∫⁻ ω, μ {η | repl ω η ∈ S} ∂μ := by
  rw [← hrepl.measure_preimage hS.nullMeasurableSet, Measure.prod_apply (hrepl.measurable hS)]
  rfl

/-- **Conditioning on the complement of a block.** If `X` only reads what `repl` keeps from
`ω`, then `μ(X ∩ Y) = ∫_X μ{η | repl ω η ∈ Y} dμ(ω)`. -/
theorem measure_inter_eq_repl
    (hrepl : MeasurePreserving (fun p : Ω × Ω => repl p.1 p.2) (μ.prod μ) μ)
    {X Y : Set Ω} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXr : ∀ ω η, repl ω η ∈ X ↔ ω ∈ X) :
    μ (X ∩ Y) = ∫⁻ ω in X, μ {η | repl ω η ∈ Y} ∂μ := by
  rw [measure_eq_lintegral_repl hrepl (hX.inter hY), ← lintegral_indicator hX]
  refine lintegral_congr fun ω => ?_
  by_cases hω : ω ∈ X
  · rw [Set.indicator_of_mem hω]
    have : {η | repl ω η ∈ X ∩ Y} = {η | repl ω η ∈ Y} := by
      ext η; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, hXr, hω, true_and]
    rw [this]
  · rw [Set.indicator_of_notMem hω]
    have : {η | repl ω η ∈ X ∩ Y} = ∅ := by
      ext η
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, hXr, hω, false_and,
        Set.mem_empty_iff_false]
    rw [this, measure_empty]

/-- Conditional bound: `μ(X ∩ Y) ≤ p μ(X)` if every section of `Y` over `ω ∈ X` is `≤ p`. -/
theorem measure_inter_le_repl
    (hrepl : MeasurePreserving (fun p : Ω × Ω => repl p.1 p.2) (μ.prod μ) μ)
    {X Y : Set Ω} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXr : ∀ ω η, repl ω η ∈ X ↔ ω ∈ X) {p : ENNReal}
    (hp : ∀ ω ∈ X, μ {η | repl ω η ∈ Y} ≤ p) : μ (X ∩ Y) ≤ p * μ X := by
  rw [measure_inter_eq_repl hrepl hX hY hXr, ← setLIntegral_const X p]
  exact setLIntegral_mono measurable_const hp

/-- Independence: `X` reads only what is kept from `ω`, `Y` only what is taken from `η`. -/
theorem measure_inter_eq_mul_repl
    (hrepl : MeasurePreserving (fun p : Ω × Ω => repl p.1 p.2) (μ.prod μ) μ)
    {X Y : Set Ω} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXr : ∀ ω η, repl ω η ∈ X ↔ ω ∈ X) (hYr : ∀ ω η, repl ω η ∈ Y ↔ η ∈ Y) :
    μ (X ∩ Y) = μ X * μ Y := by
  rw [measure_inter_eq_repl hrepl hX hY hXr]
  have : ∀ ω, {η | repl ω η ∈ Y} = Y := fun ω => by ext η; simp only [Set.mem_ofPred_eq, hYr]
  simp_rw [this]
  rw [setLIntegral_const, mul_comm]

/-- Finite products of events, each reading its own block. -/
theorem measure_iInter_eq_prod_repl [IsProbabilityMeasure μ] {κ : Type*} [DecidableEq κ]
    (J : Finset κ) {rp : κ → Ω → Ω → Ω} {X : κ → Set Ω}
    (hrp : ∀ j ∈ J, MeasurePreserving (fun p : Ω × Ω => rp j p.1 p.2) (μ.prod μ) μ)
    (hX : ∀ j ∈ J, MeasurableSet (X j))
    (hin : ∀ j ∈ J, ∀ ω η, rp j ω η ∈ X j ↔ η ∈ X j)
    (hout : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → ∀ ω η, rp k ω η ∈ X j ↔ ω ∈ X j) :
    μ (⋂ j ∈ J, X j) = ∏ j ∈ J, μ (X j) := by
  induction J using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biInter_insert, Finset.prod_insert ha, Set.inter_comm]
    have hms : MeasurableSet (⋂ j ∈ s, X j) :=
      Finset.measurableSet_biInter s fun j hj => hX j (mem_insert_of_mem hj)
    have hr : ∀ ω η, rp a ω η ∈ ⋂ j ∈ s, X j ↔ ω ∈ ⋂ j ∈ s, X j := by
      intro ω η
      simp only [Set.mem_iInter]
      refine forall₂_congr fun j hj => ?_
      exact hout j (mem_insert_of_mem hj) a (mem_insert_self a s)
        (fun h => ha (h ▸ hj)) ω η
    rw [measure_inter_eq_mul_repl (hrp a (mem_insert_self a s)) hms (hX a (mem_insert_self a s))
      hr (hin a (mem_insert_self a s)), mul_comm,
      ih (fun j hj => hrp j (mem_insert_of_mem hj)) (fun j hj => hX j (mem_insert_of_mem hj))
        (fun j hj => hin j (mem_insert_of_mem hj))
        (fun j hj k hk => hout j (mem_insert_of_mem hj) k (mem_insert_of_mem hk))]

/-- **Product bound given the rest (abstract form).** Events `X j` each resampled through its own
block map `rp j`; `G` and every other `X k` only read what `rp j` keeps; every section of `X j`
over `G` has measure `≤ p j`.  Then `μ(G ∩ ⋂ X j) ≤ (∏ p j) μ(G)`. -/
theorem measure_inter_iInter_le_prod_repl {κ : Type*} [DecidableEq κ]
    (J : Finset κ) {rp : κ → Ω → Ω → Ω} {G : Set Ω} {X : κ → Set Ω}
    (hrp : ∀ j ∈ J, MeasurePreserving (fun p : Ω × Ω => rp j p.1 p.2) (μ.prod μ) μ)
    (hG : MeasurableSet G) (hX : ∀ j ∈ J, MeasurableSet (X j))
    (hGr : ∀ j ∈ J, ∀ ω η, rp j ω η ∈ G ↔ ω ∈ G)
    (hout : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → ∀ ω η, rp k ω η ∈ X j ↔ ω ∈ X j)
    {p : κ → ENNReal} (hp : ∀ j ∈ J, ∀ ω ∈ G, μ {η | rp j ω η ∈ X j} ≤ p j) :
    μ (G ∩ ⋂ j ∈ J, X j) ≤ (∏ j ∈ J, p j) * μ G := by
  induction J using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biInter_insert, Finset.prod_insert ha]
    have hms : MeasurableSet (G ∩ ⋂ j ∈ s, X j) :=
      hG.inter (Finset.measurableSet_biInter s fun j hj => hX j (mem_insert_of_mem hj))
    have hr : ∀ ω η, rp a ω η ∈ G ∩ ⋂ j ∈ s, X j ↔ ω ∈ G ∩ ⋂ j ∈ s, X j := by
      intro ω η
      simp only [Set.mem_inter_iff, Set.mem_iInter]
      refine and_congr (hGr a (mem_insert_self a s) ω η) (forall₂_congr fun j hj => ?_)
      exact hout j (mem_insert_of_mem hj) a (mem_insert_self a s)
        (fun h => ha (h ▸ hj)) ω η
    have hset : G ∩ (X a ∩ ⋂ j ∈ s, X j) = (G ∩ ⋂ j ∈ s, X j) ∩ X a := by
      ext ω; simp only [Set.mem_inter_iff]; tauto
    rw [hset]
    calc μ ((G ∩ ⋂ j ∈ s, X j) ∩ X a) ≤ p a * μ (G ∩ ⋂ j ∈ s, X j) :=
          measure_inter_le_repl (hrp a (mem_insert_self a s)) hms (hX a (mem_insert_self a s)) hr
            fun ω hω => hp a (mem_insert_self a s) ω hω.1
      _ ≤ p a * ((∏ j ∈ s, p j) * μ G) := by
          gcongr
          exact ih (fun j hj => hrp j (mem_insert_of_mem hj)) (fun j hj => hX j (mem_insert_of_mem hj))
            (fun j hj => hGr j (mem_insert_of_mem hj))
            (fun j hj k hk => hout j (mem_insert_of_mem hj) k (mem_insert_of_mem hk))
            (fun j hj => hp j (mem_insert_of_mem hj))
      _ = p a * (∏ j ∈ s, p j) * μ G := by rw [mul_assoc]

end Repl

/-! ## 3. Coordinate blocks of a finite product measure -/

section PiCoord

variable {ι E : Type*}

/-- `X` is determined by the coordinates in `C`. -/
def DetOn (C : Finset ι) (X : Set (ι → E)) : Prop :=
  ∀ ω ω' : ι → E, (∀ i ∈ C, ω i = ω' i) → (ω ∈ X ↔ ω' ∈ X)

lemma DetOn.mono {C D : Finset ι} {X : Set (ι → E)} (h : DetOn C X) (hCD : C ⊆ D) : DetOn D X :=
  fun ω ω' hω => h ω ω' fun i hi => hω i (hCD hi)

lemma DetOn.inter {C : Finset ι} {X Y : Set (ι → E)} (hX : DetOn C X) (hY : DetOn C Y) :
    DetOn C (X ∩ Y) :=
  fun ω ω' hω => and_congr (hX ω ω' hω) (hY ω ω' hω)

lemma DetOn.compl {C : Finset ι} {X : Set (ι → E)} (hX : DetOn C X) : DetOn C Xᶜ :=
  fun ω ω' hω => not_congr (hX ω ω' hω)

lemma detOn_univ (C : Finset ι) : DetOn C (Set.univ : Set (ι → E)) := fun _ _ _ => Iff.rfl

lemma DetOn.biInter {κ : Type*} {C : Finset ι} (J : Finset κ) {X : κ → Set (ι → E)}
    (h : ∀ j ∈ J, DetOn C (X j)) : DetOn C (⋂ j ∈ J, X j) := by
  intro ω ω' hω
  simp only [Set.mem_iInter]
  exact forall₂_congr fun j hj => h j hj ω ω' hω

variable [DecidableEq ι]

/-- Replace the coordinates in `C` of `ω` by those of `η`. -/
def replS (C : Finset ι) (ω η : ι → E) : ι → E := fun i => if i ∈ C then η i else ω i

lemma replS_of_mem {C : Finset ι} {ω η : ι → E} {i : ι} (h : i ∈ C) : replS C ω η i = η i := by
  simp only [replS, h, ↓reduceIte]

lemma replS_of_not_mem {C : Finset ι} {ω η : ι → E} {i : ι} (h : i ∉ C) :
    replS C ω η i = ω i := by
  simp only [replS, h, ↓reduceIte]

/-- A set determined by `C` only sees the replaced block. -/
lemma DetOn.replS_in {C : Finset ι} {X : Set (ι → E)} (h : DetOn C X) (ω η : ι → E) :
    replS C ω η ∈ X ↔ η ∈ X :=
  h _ _ fun _ hi => replS_of_mem hi

/-- A set determined outside `C` does not see the replaced block. -/
lemma DetOn.replS_out [Fintype ι] {C : Finset ι} {X : Set (ι → E)} (h : DetOn Cᶜ X)
    (ω η : ι → E) : replS C ω η ∈ X ↔ ω ∈ X :=
  h _ _ fun _ hi => replS_of_not_mem (Finset.mem_compl.1 hi)

lemma measurable_replS [MeasurableSpace E] (C : Finset ι) :
    Measurable fun p : (ι → E) × (ι → E) => replS C p.1 p.2 := by
  refine Measurable.of_eval fun i => ?_
  by_cases hi : i ∈ C
  · simp only [replS, hi, ↓reduceIte]; exact (measurable_pi_apply i).comp measurable_snd
  · simp only [replS, hi, ↓reduceIte]; exact (measurable_pi_apply i).comp measurable_fst

variable [Fintype ι] [MeasurableSpace E]

/-- Replacing a block by an independent copy preserves the product law. -/
theorem mp_replS (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] (C : Finset ι) :
    MeasurePreserving (fun p : (ι → E) × (ι → E) => replS C p.1 p.2)
      ((Measure.pi ν).prod (Measure.pi ν)) (Measure.pi ν) := by
  refine ⟨measurable_replS C, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply (measurable_replS C) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → E) × (ι → E) => replS C p.1 p.2) ⁻¹' Set.univ.pi s =
      (Set.univ.pi fun i => if i ∈ C then Set.univ else s i) ×ˢ
        (Set.univ.pi fun i => if i ∈ C then s i else Set.univ) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i ∈ C
        · simp only [hi, ↓reduceIte, Set.mem_univ]
        · simp only [hi, ↓reduceIte]; simpa [replS, hi] using h i
      · by_cases hi : i ∈ C
        · simp only [hi, ↓reduceIte]; simpa [replS, hi] using h i
        · simp only [hi, ↓reduceIte, Set.mem_univ]
    · rintro ⟨h1, h2⟩ i
      have h1 := h1 i
      have h2 := h2 i
      by_cases hi : i ∈ C
      · simp only [hi, ↓reduceIte] at h2; simpa [replS, hi] using h2
      · simp only [hi, ↓reduceIte] at h1; simpa [replS, hi] using h1
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ C <;> simp [hi]

variable (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]

/-- **Conditioning on the coordinates outside a block `C`** (Fubini form). -/
theorem pi_inter_eq_setLIntegral (C : Finset ι) {X Y : Set (ι → E)} (hX : MeasurableSet X)
    (hY : MeasurableSet Y) (hXd : DetOn Cᶜ X) :
    Measure.pi ν (X ∩ Y) = ∫⁻ ω in X, Measure.pi ν {η | replS C ω η ∈ Y} ∂Measure.pi ν :=
  measure_inter_eq_repl (mp_replS ν C) hX hY hXd.replS_out

/-- Conditional bound over a block `C`. -/
theorem pi_inter_le_of_section (C : Finset ι) {X Y : Set (ι → E)} (hX : MeasurableSet X)
    (hY : MeasurableSet Y) (hXd : DetOn Cᶜ X) {p : ENNReal}
    (hp : ∀ ω ∈ X, Measure.pi ν {η | replS C ω η ∈ Y} ≤ p) :
    Measure.pi ν (X ∩ Y) ≤ p * Measure.pi ν X :=
  measure_inter_le_repl (mp_replS ν C) hX hY hXd.replS_out hp

/-- **Independence of events determined by disjoint coordinate sets.** -/
theorem pi_inter_eq_mul_of_detOn {C D : Finset ι} (hCD : Disjoint C D) {X Y : Set (ι → E)}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (hXd : DetOn C X) (hYd : DetOn D Y) :
    Measure.pi ν (X ∩ Y) = Measure.pi ν X * Measure.pi ν Y :=
  measure_inter_eq_mul_repl (mp_replS ν D) hX hY
    (hXd.mono (Finset.subset_compl_iff_disjoint_right.2 hCD)).replS_out hYd.replS_in

/-- Finitely many events determined by pairwise disjoint coordinate sets are independent. -/
theorem pi_iInter_eq_prod_of_detOn {κ : Type*} [DecidableEq κ] (J : Finset κ)
    (C : κ → Finset ι) (hC : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → Disjoint (C j) (C k))
    {X : κ → Set (ι → E)} (hX : ∀ j ∈ J, MeasurableSet (X j))
    (hXd : ∀ j ∈ J, DetOn (C j) (X j)) :
    Measure.pi ν (⋂ j ∈ J, X j) = ∏ j ∈ J, Measure.pi ν (X j) :=
  measure_iInter_eq_prod_repl (rp := fun j => replS (C j)) J (fun j _ => mp_replS ν (C j)) hX
    (fun j hj => (hXd j hj).replS_in)
    (fun j hj k hk hjk =>
      ((hXd j hj).mono (Finset.subset_compl_iff_disjoint_right.2 (hC j hj k hk hjk))).replS_out)

/-- **Product bound for events on disjoint private coordinate sets given the rest.**
The private blocks `C j` (`j ∈ J`) are pairwise disjoint and disjoint from the shared block `R`;
`G` is determined by `R` and `X j` by `C j ∪ R`.  If, for every configuration `ω ∈ G`, the
conditional probability of `X j` given the coordinates outside `C j` (the measure of the section
`{η | replS (C j) ω η ∈ X j}`) is `≤ p j`, then `P(G ∩ ⋂ X j) ≤ (∏ p j) P(G)`. -/
theorem pi_prod_bound_private {κ : Type*} [DecidableEq κ] (J : Finset κ) (C : κ → Finset ι)
    (R : Finset ι) (hC : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → Disjoint (C j) (C k))
    (hR : ∀ j ∈ J, Disjoint R (C j)) {G : Set (ι → E)} {X : κ → Set (ι → E)}
    (hG : MeasurableSet G) (hX : ∀ j ∈ J, MeasurableSet (X j)) (hGd : DetOn R G)
    (hXd : ∀ j ∈ J, DetOn (C j ∪ R) (X j)) {p : κ → ENNReal}
    (hp : ∀ j ∈ J, ∀ ω ∈ G, Measure.pi ν {η | replS (C j) ω η ∈ X j} ≤ p j) :
    Measure.pi ν (G ∩ ⋂ j ∈ J, X j) ≤ (∏ j ∈ J, p j) * Measure.pi ν G :=
  measure_inter_iInter_le_prod_repl (rp := fun j => replS (C j)) J (fun j _ => mp_replS ν (C j))
    hG hX
    (fun j hj => (hGd.mono (Finset.subset_compl_iff_disjoint_right.2 (hR j hj))).replS_out)
    (fun j hj k hk hjk => ((hXd j hj).mono (Finset.union_subset
      (Finset.subset_compl_iff_disjoint_right.2 (hC j hj k hk hjk))
      (Finset.subset_compl_iff_disjoint_right.2 (hR k hk)))).replS_out)
    hp

/-- **Stopping set, "determined by" form.** If `{P = A}` is determined by the coordinates
outside `A` (the stopping property), then given `{P = A}` and any event `X` of the outside
coordinates, the coordinates on `A` keep their product law. -/
theorem stopping_set_indep (P : (ι → E) → Finset ι) (A : Finset ι)
    (hP : MeasurableSet {ω | P ω = A}) (hPd : DetOn Aᶜ {ω | P ω = A})
    {X Y : Set (ι → E)} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXd : DetOn Aᶜ X) (hYd : DetOn A Y) :
    Measure.pi ν ({ω | P ω = A} ∩ X ∩ Y) = Measure.pi ν ({ω | P ω = A} ∩ X) * Measure.pi ν Y :=
  pi_inter_eq_mul_of_detOn ν disjoint_compl_left (hP.inter hX) hY (hPd.inter hXd) hYd

/-- **`stopping_set_iid` (blueprint A3).** `{P = A} = {ω | ω|_{Aᶜ} ∈ G}` (measurable w.r.t. the
coordinates outside `A`); then
`μ{P = A ∧ ω|_{Aᶜ} ∈ Eo ∧ ω|_A ∈ Ei} = μ_{Aᶜ}(G ∩ Eo) · μ_A(Ei)`. No measurability is needed. -/
theorem stopping_set_iid (P : (ι → E) → Finset ι) (A : Finset ι)
    (G : Set ({i // i ∉ A} → E)) (hPG : ∀ ω, P ω = A ↔ (fun i : {i // i ∉ A} => ω i) ∈ G)
    (Eo : Set ({i // i ∉ A} → E)) (Ei : Set ({i // i ∈ A} → E)) :
    Measure.pi ν {ω | P ω = A ∧ (fun i : {i // i ∉ A} => ω i) ∈ Eo ∧
        (fun i : {i // i ∈ A} => ω i) ∈ Ei} =
      (Measure.pi fun i : {i // i ∉ A} => ν i) (G ∩ Eo) *
        (Measure.pi fun i : {i // i ∈ A} => ν i) Ei := by
  have hmp := measurePreserving_piEquivPiSubtypeProd ν (fun i => i ∈ A)
  have hset : {ω : ι → E | P ω = A ∧ (fun i : {i // i ∉ A} => ω i) ∈ Eo ∧
      (fun i : {i // i ∈ A} => ω i) ∈ Ei} =
      MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => E) (fun i => i ∈ A) ⁻¹'
        (Ei ×ˢ (G ∩ Eo)) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff,
      MeasurableEquiv.piEquivPiSubtypeProd_apply, hPG]
    tauto
  rw [hset, hmp.measure_preimage_equiv, Measure.prod_prod, mul_comm]
  congr 2
  exact b1p_pi_fintype_irrel _ _ _

/-- **Stopping set with a random block.** For a random set `P` with the stopping property, events
`X A` of the outside coordinates and `Y A` of the block: the sum over the values of `P`. -/
theorem stopping_sum (P : (ι → E) → Finset ι) (hP : ∀ A, MeasurableSet {ω | P ω = A})
    (hPd : ∀ A, DetOn Aᶜ {ω | P ω = A}) {X Y : Finset ι → Set (ι → E)}
    (hX : ∀ A, MeasurableSet (X A)) (hY : ∀ A, MeasurableSet (Y A))
    (hXd : ∀ A, DetOn Aᶜ (X A)) (hYd : ∀ A, DetOn A (Y A)) :
    Measure.pi ν {ω | ω ∈ X (P ω) ∧ ω ∈ Y (P ω)} =
      ∑ A, Measure.pi ν ({ω | P ω = A} ∩ X A) * Measure.pi ν (Y A) := by
  rw [measure_eq_sum_partition _ hP]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [← stopping_set_indep ν P A (hP A) (hPd A) (hX A) (hY A) (hXd A) (hYd A)]
  congr 1
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; rw [h3] at h1 h2; exact ⟨⟨h3, h1⟩, h2⟩
  · rintro ⟨⟨h3, h1⟩, h2⟩; rw [h3]; exact ⟨⟨h1, h2⟩, rfl⟩

/-- **Given the stopping set, the entries on it are iid**: if every block event has probability
`≤ q`, the event "`Y` holds on the random block" has probability `≤ q · P(X)`. -/
theorem stopping_le (P : (ι → E) → Finset ι) (hP : ∀ A, MeasurableSet {ω | P ω = A})
    (hPd : ∀ A, DetOn Aᶜ {ω | P ω = A}) {X Y : Finset ι → Set (ι → E)}
    (hX : ∀ A, MeasurableSet (X A)) (hY : ∀ A, MeasurableSet (Y A))
    (hXd : ∀ A, DetOn Aᶜ (X A)) (hYd : ∀ A, DetOn A (Y A)) {q : ENNReal}
    (hq : ∀ A, Measure.pi ν (Y A) ≤ q) :
    Measure.pi ν {ω | ω ∈ X (P ω) ∧ ω ∈ Y (P ω)} ≤ q * Measure.pi ν {ω | ω ∈ X (P ω)} := by
  rw [stopping_sum ν P hP hPd hX hY hXd hYd, measure_eq_sum_partition (Measure.pi ν) hP
    {ω | ω ∈ X (P ω)}, Finset.mul_sum]
  refine Finset.sum_le_sum fun A _ => ?_
  have hs : {ω : ι → E | ω ∈ X (P ω)} ∩ {ω | P ω = A} = {ω | P ω = A} ∩ X A := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; rw [h2] at h1; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; rw [h2]; exact ⟨h1, rfl⟩
  rw [hs, mul_comm]
  gcongr
  exact hq A

end PiCoord

/-! ## 4. Rows of the parameter cube -/

section Rows

variable {N : ℕ}

/-- The law of the rows of a row set `F`. -/
def rowsInM (F : Finset (State N)) : Measure (F → Fin N → ℝ) := Measure.pi fun _ => rowM N

/-- The law of the rows outside a row set `F`. -/
def rowsOutM (F : Finset (State N)) : Measure ({r // r ∉ F} → Fin N → ℝ) :=
  Measure.pi fun _ => rowM N

instance (F : Finset (State N)) : IsProbabilityMeasure (rowsInM F) := by
  unfold rowsInM; infer_instance

instance (F : Finset (State N)) : IsProbabilityMeasure (rowsOutM F) := by
  unfold rowsOutM; infer_instance

/-- The parameter with the rows of `F` given by `f` and the other rows given by `g`. -/
def glueRows (F : Finset (State N)) (f : F → Fin N → ℝ) (g : {r // r ∉ F} → Fin N → ℝ) :
    Param N :=
  fun r => if h : r ∈ F then f ⟨r, h⟩ else g ⟨r, h⟩

/-- The rows of `w` in `F`. -/
def restrIn (F : Finset (State N)) (w : Param N) : F → Fin N → ℝ := fun r => w r.1

/-- The rows of `w` outside `F`. -/
def restrOut (F : Finset (State N)) (w : Param N) : {r // r ∉ F} → Fin N → ℝ := fun r => w r.1

variable (F : Finset (State N))

lemma glueRows_of_mem (f : F → Fin N → ℝ) (g : {r // r ∉ F} → Fin N → ℝ) {r : State N}
    (hr : r ∈ F) : glueRows F f g r = f ⟨r, hr⟩ := by
  simp [glueRows, hr]

lemma glueRows_of_not_mem (f : F → Fin N → ℝ) (g : {r // r ∉ F} → Fin N → ℝ) {r : State N}
    (hr : r ∉ F) : glueRows F f g r = g ⟨r, hr⟩ := by
  simp [glueRows, hr]

@[simp] lemma restrIn_glueRows (f : F → Fin N → ℝ) (g : {r // r ∉ F} → Fin N → ℝ) :
    restrIn F (glueRows F f g) = f := by
  funext r; exact glueRows_of_mem F f g r.2

@[simp] lemma restrOut_glueRows (f : F → Fin N → ℝ) (g : {r // r ∉ F} → Fin N → ℝ) :
    restrOut F (glueRows F f g) = g := by
  funext r; exact glueRows_of_not_mem F f g r.2

@[simp] lemma glueRows_restr (w : Param N) : glueRows F (restrIn F w) (restrOut F w) = w := by
  funext r
  by_cases hr : r ∈ F
  · rw [glueRows_of_mem F _ _ hr]; rfl
  · rw [glueRows_of_not_mem F _ _ hr]; rfl

/-- Two gluings with the same `F`-part agree on the rows of `F`. -/
lemma glueRows_agree (f : F → Fin N → ℝ) (g g' : {r // r ∉ F} → Fin N → ℝ) :
    ∀ r ∈ F, glueRows F f g' r = glueRows F f g r := fun r hr => by
  rw [glueRows_of_mem F _ _ hr, glueRows_of_mem F _ _ hr]

lemma measurable_restrIn : Measurable (restrIn F) :=
  Measurable.of_eval fun r => measurable_pi_apply r.1

lemma measurable_restrOut : Measurable (restrOut F) :=
  Measurable.of_eval fun r => measurable_pi_apply r.1

/-- The row split as a measurable equivalence (`MeasurableEquiv.piEquivPiSubtypeProd`). -/
def splitRowsE : Param N ≃ᵐ (F → Fin N → ℝ) × ({r // r ∉ F} → Fin N → ℝ) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : State N => Fin N → ℝ) (· ∈ F)

lemma splitRowsE_apply (w : Param N) : splitRowsE F w = (restrIn F w, restrOut F w) := rfl

lemma splitRowsE_symm_apply (p : (F → Fin N → ℝ) × ({r // r ∉ F} → Fin N → ℝ)) :
    (splitRowsE F).symm p = glueRows F p.1 p.2 := rfl

/-- **`cubeM_split_rows`, measure-preserving form.** -/
theorem mp_splitRows :
    MeasurePreserving (splitRowsE F) (cubeM N) ((rowsInM F).prod (rowsOutM F)) := by
  have h := measurePreserving_piEquivPiSubtypeProd (fun _ : State N => rowM N) (· ∈ F)
  have hin : rowsInM F = @Measure.pi {r // r ∈ F} (fun _ => Fin N → ℝ) (Subtype.fintype _) _
      (fun _ => rowM N) := b1p_pi_fintype_irrel _ _ _
  rw [hin]
  exact h

/-- Gluing independent rows gives the uniform cube. -/
theorem mp_glueRows :
    MeasurePreserving (fun p : (F → Fin N → ℝ) × ({r // r ∉ F} → Fin N → ℝ) => glueRows F p.1 p.2)
      ((rowsInM F).prod (rowsOutM F)) (cubeM N) :=
  (mp_splitRows F).symm (splitRowsE F)

/-- **`cubeM_split_rows` (blueprint A3).** `cubeM N` is the pushforward of
`(pi over F) ⊗ (pi over Fᶜ)` under the inverse of `piEquivPiSubtypeProd`. -/
theorem cubeM_split_rows :
    cubeM N = ((rowsInM F).prod (rowsOutM F)).map (splitRowsE F).symm :=
  (mp_glueRows F).map_eq.symm

lemma measurable_glueRows :
    Measurable fun p : (F → Fin N → ℝ) × ({r // r ∉ F} → Fin N → ℝ) => glueRows F p.1 p.2 :=
  (mp_glueRows F).measurable

/-- **Fubini over the rows outside `F`.** -/
theorem cubeM_eq_lintegral_rows {X : Set (Param N)} (hX : MeasurableSet X) :
    cubeM N X = ∫⁻ f, rowsOutM F {g | glueRows F f g ∈ X} ∂rowsInM F := by
  rw [← (mp_glueRows F).measure_preimage hX.nullMeasurableSet,
    Measure.prod_apply ((mp_glueRows F).measurable hX)]
  rfl

/-- The law of the `F`-rows under `cubeM`. -/
theorem cubeM_restrIn_preimage (G : Set (F → Fin N → ℝ)) :
    cubeM N {w | restrIn F w ∈ G} = rowsInM F G := by
  have : {w : Param N | restrIn F w ∈ G} = splitRowsE F ⁻¹' (G ×ˢ Set.univ) := by
    ext w; simp [splitRowsE_apply]
  rw [this, (mp_splitRows F).measure_preimage_equiv, Measure.prod_prod, measure_univ, mul_one]

/-- The law of the rows outside `F` under `cubeM`. -/
theorem cubeM_restrOut_preimage (G : Set ({r // r ∉ F} → Fin N → ℝ)) :
    cubeM N {w | restrOut F w ∈ G} = rowsOutM F G := by
  have : {w : Param N | restrOut F w ∈ G} = splitRowsE F ⁻¹' (Set.univ ×ˢ G) := by
    ext w; simp [splitRowsE_apply]
  rw [this, (mp_splitRows F).measure_preimage_equiv, Measure.prod_prod, measure_univ, one_mul]

/-- **Conditioning on the `F`-rows** (Fubini form). -/
theorem cubeM_inter_restrIn_eq {X : Set (Param N)} (hX : MeasurableSet X)
    {G : Set (F → Fin N → ℝ)} (hG : MeasurableSet G) :
    cubeM N (X ∩ {w | restrIn F w ∈ G}) = ∫⁻ f in G, rowsOutM F {g | glueRows F f g ∈ X} ∂rowsInM F := by
  have hm : MeasurableSet (X ∩ {w | restrIn F w ∈ G}) := hX.inter (measurable_restrIn F hG)
  rw [cubeM_eq_lintegral_rows F hm, ← lintegral_indicator hG]
  refine lintegral_congr fun f => ?_
  by_cases hf : f ∈ G
  · rw [Set.indicator_of_mem hf]
    have : {g | glueRows F f g ∈ X ∩ {w | restrIn F w ∈ G}} = {g | glueRows F f g ∈ X} := by
      ext g; simp [hf]
    rw [this]
  · rw [Set.indicator_of_notMem hf]
    have : {g | glueRows F f g ∈ X ∩ {w | restrIn F w ∈ G}} = ∅ := by
      ext g; simp [hf]
    rw [this, measure_empty]

/-- **Conditional bound given the `F`-rows.** If for every `f ∈ G` the conditional probability of
`X` given the `F`-rows `f` is `≤ δ`, then `P(X ∩ {rows of F ∈ G}) ≤ δ · P(rows of F ∈ G)`. -/
theorem cubeM_inter_restrIn_le {X : Set (Param N)} (hX : MeasurableSet X)
    {G : Set (F → Fin N → ℝ)} (hG : MeasurableSet G) {δ : ENNReal}
    (h : ∀ f ∈ G, rowsOutM F {g | glueRows F f g ∈ X} ≤ δ) :
    cubeM N (X ∩ {w | restrIn F w ∈ G}) ≤ δ * rowsInM F G := by
  rw [cubeM_inter_restrIn_eq F hX hG, ← setLIntegral_const G δ]
  exact setLIntegral_mono measurable_const h

/-- A uniform bound on the conditional probabilities bounds the probability. -/
theorem cubeM_le_of_rows {X : Set (Param N)} (hX : MeasurableSet X) {δ : ENNReal}
    (h : ∀ f, rowsOutM F {g | glueRows F f g ∈ X} ≤ δ) : cubeM N X ≤ δ := by
  rw [cubeM_eq_lintegral_rows F hX]
  calc ∫⁻ f, rowsOutM F {g | glueRows F f g ∈ X} ∂rowsInM F ≤ ∫⁻ _, δ ∂rowsInM F :=
        lintegral_mono h
    _ = δ := by simp

/-- **Independence of events determined by disjoint row sets.** -/
theorem cubeM_inter_eq_mul_of_rows {F' : Finset (State N)} (hFF : Disjoint F F')
    {X Y : Set (Param N)} (hX : MeasurableSet X) (hY : MeasurableSet Y) (hXd : DetOn F X)
    (hYd : DetOn F' Y) : cubeM N (X ∩ Y) = cubeM N X * cubeM N Y :=
  pi_inter_eq_mul_of_detOn (fun _ : State N => rowM N) hFF hX hY hXd hYd

/-- The law of `(f, g, g')`: the `F`-rows and two independent copies of the other rows. -/
abbrev rows3M : Measure ((F → Fin N → ℝ) × ({r // r ∉ F} → Fin N → ℝ) × ({r // r ∉ F} → Fin N → ℝ)) :=
  (rowsInM F).prod ((rowsOutM F).prod (rowsOutM F))

lemma measurable_glue1 :
    Measurable fun x : (F → Fin N → ℝ) × ({r // r ∉ F} → Fin N → ℝ) × ({r // r ∉ F} → Fin N → ℝ) =>
      glueRows F x.1 x.2.1 :=
  (measurable_glueRows F).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))

lemma measurable_glue2 :
    Measurable fun x : (F → Fin N → ℝ) × ({r // r ∉ F} → Fin N → ℝ) × ({r // r ∉ F} → Fin N → ℝ) =>
      glueRows F x.1 x.2.2 :=
  (measurable_glueRows F).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

/-- The resampled parameter `glue f g'` has the law `cubeM`, and so has `glue f g`. -/
theorem rows3M_marginal_one {X : Set (Param N)} (hX : MeasurableSet X) :
    rows3M F {x | glueRows F x.1 x.2.1 ∈ X} = cubeM N X := by
  have h := prod_marginal_one (rowsInM F) (rowsOutM F) ((mp_glueRows F).measurable hX)
  rw [(mp_glueRows F).measure_preimage hX.nullMeasurableSet] at h
  exact h

theorem rows3M_marginal_two {X : Set (Param N)} (hX : MeasurableSet X) :
    rows3M F {x | glueRows F x.1 x.2.2 ∈ X} = cubeM N X := by
  have h := prod_marginal_two (rowsInM F) (rowsOutM F) ((mp_glueRows F).measurable hX)
  rw [(mp_glueRows F).measure_preimage hX.nullMeasurableSet] at h
  exact h

/-- **Resampling identity on the cube.** `P(A(ω) ∩ B(ω'))`, with `ω'` = `ω` with the rows outside
`F` replaced by an independent copy, is `∫ P(A | f) P(B | f) df`. -/
theorem rows3M_resample_eq {X Y : Set (Param N)} (hX : MeasurableSet X) (hY : MeasurableSet Y) :
    rows3M F {x | glueRows F x.1 x.2.1 ∈ X ∧ glueRows F x.1 x.2.2 ∈ Y} =
      ∫⁻ f, rowsOutM F {g | glueRows F f g ∈ X} * rowsOutM F {g | glueRows F f g ∈ Y} ∂rowsInM F :=
  prod_resample_eq (rowsInM F) (rowsOutM F) ((mp_glueRows F).measurable hX)
    ((mp_glueRows F).measurable hY)

/-- The resampled events factor when the first one only reads the first fresh copy:
`P(g ∈ X' ∧ glue f g' ∈ Y) = P(X') P(Y)`. -/
theorem rows3M_resample_eq_mul {X' : Set ({r // r ∉ F} → Fin N → ℝ)} {Y : Set (Param N)}
    (hX' : MeasurableSet X') (hY : MeasurableSet Y) :
    rows3M F {x | x.2.1 ∈ X' ∧ glueRows F x.1 x.2.2 ∈ Y} = rowsOutM F X' * cubeM N Y := by
  have h := prod_resample_eq_mul (rowsInM F) (rowsOutM F) hX' ((mp_glueRows F).measurable hY)
  rw [(mp_glueRows F).measure_preimage hY.nullMeasurableSet] at h
  exact h

/-- **Resampling identity with independence (cube form).** `ω = glue f g`, `ω' = glue f g'`
(the rows outside `F` replaced by an independent copy).  If `X` is determined by the rows
outside `F`, then `P(ω ∈ X ∧ ω' ∈ Y) = P(X) P(Y)`. -/
theorem rows3M_resample_indep {X Y : Set (Param N)} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXd : DetOn Fᶜ X) :
    rows3M F {x | glueRows F x.1 x.2.1 ∈ X ∧ glueRows F x.1 x.2.2 ∈ Y} = cubeM N X * cubeM N Y := by
  let f0 : F → Fin N → ℝ := fun _ _ => 0
  let X' : Set ({r // r ∉ F} → Fin N → ℝ) := {g | glueRows F f0 g ∈ X}
  have hX' : MeasurableSet X' :=
    ((measurable_glueRows F).comp ((measurable_const (a := f0)).prodMk measurable_id)) hX
  have key : ∀ f g, glueRows F f g ∈ X ↔ g ∈ X' := fun f g => hXd _ _ fun r hr => by
    have : r ∉ F := Finset.mem_compl.1 hr
    rw [glueRows_of_not_mem F _ _ this, glueRows_of_not_mem F _ _ this]
  have hset : {x : (F → Fin N → ℝ) × ({r // r ∉ F} → Fin N → ℝ) × ({r // r ∉ F} → Fin N → ℝ) |
      glueRows F x.1 x.2.1 ∈ X ∧ glueRows F x.1 x.2.2 ∈ Y} =
      {x | x.2.1 ∈ X' ∧ glueRows F x.1 x.2.2 ∈ Y} := by
    ext x; simp only [Set.mem_ofPred_eq, key]
  have hXX : cubeM N X = rowsOutM F X' := by
    rw [← cubeM_restrOut_preimage F X']
    congr 1; ext w
    simp only [Set.mem_ofPred_eq]
    rw [← key (restrIn F w) (restrOut F w), glueRows_restr]
  rw [hset, rows3M_resample_eq_mul F hX' hY, hXX]

/-- The same when `Y` is determined by the rows outside `F`: `P(ω ∈ X ∧ ω' ∈ Y) = P(X) P(Y)`. -/
theorem rows3M_resample_indep' {X Y : Set (Param N)} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hYd : DetOn Fᶜ Y) :
    rows3M F {x | glueRows F x.1 x.2.1 ∈ X ∧ glueRows F x.1 x.2.2 ∈ Y} = cubeM N X * cubeM N Y := by
  let f0 : F → Fin N → ℝ := fun _ _ => 0
  let Y' : Set ({r // r ∉ F} → Fin N → ℝ) := {g | glueRows F f0 g ∈ Y}
  have hY' : MeasurableSet Y' :=
    ((measurable_glueRows F).comp ((measurable_const (a := f0)).prodMk measurable_id)) hY
  have key : ∀ f g, glueRows F f g ∈ Y ↔ g ∈ Y' := fun f g => hYd _ _ fun r hr => by
    have : r ∉ F := Finset.mem_compl.1 hr
    rw [glueRows_of_not_mem F _ _ this, glueRows_of_not_mem F _ _ this]
  have hset : {x : (F → Fin N → ℝ) × ({r // r ∉ F} → Fin N → ℝ) × ({r // r ∉ F} → Fin N → ℝ) |
      glueRows F x.1 x.2.1 ∈ X ∧ glueRows F x.1 x.2.2 ∈ Y} =
      {x | (x.1, x.2.1) ∈ (fun p : (F → Fin N → ℝ) × ({r // r ∉ F} → Fin N → ℝ) =>
        glueRows F p.1 p.2) ⁻¹' X ∧ x.2.2 ∈ Y'} := by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_preimage, key]
  have hYY : cubeM N Y = rowsOutM F Y' := by
    rw [← cubeM_restrOut_preimage F Y']
    congr 1; ext w
    simp only [Set.mem_ofPred_eq]
    rw [← key (restrIn F w) (restrOut F w), glueRows_restr]
  rw [hset, prod_resample_eq_mul' (rowsInM F) (rowsOutM F) ((mp_glueRows F).measurable hX) hY',
    (mp_glueRows F).measure_preimage hX.nullMeasurableSet, hYY]

/-- **`resample_le` on the cube.** `Stab w w'` is a stability relation between `w = glue f g` and
the resampled `w' = glue f g'`: if `w ∈ B`, `w'` agrees with `w` on the rows of `F`, and
`Stab w w'`, then `w' ∈ B`. -/
theorem cubeM_resample_le {A B : Set (Param N)} (Stab : Param N → Param N → Prop)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hS : MeasurableSet {p : Param N × Param N | Stab p.1 p.2})
    (hstab : ∀ w w', (∀ r ∈ F, w' r = w r) → w ∈ B → Stab w w' → w' ∈ B) :
    cubeM N (A ∩ B) ≤
      ∫⁻ f, rowsOutM F {g | glueRows F f g ∈ A} * rowsOutM F {g | glueRows F f g ∈ B} ∂rowsInM F +
        rows3M F {x | glueRows F x.1 x.2.1 ∈ B ∧
          ¬ Stab (glueRows F x.1 x.2.1) (glueRows F x.1 x.2.2)} := by
  have hSt : MeasurableSet {x : (F → Fin N → ℝ) × ({r // r ∉ F} → Fin N → ℝ) ×
      ({r // r ∉ F} → Fin N → ℝ) | Stab (glueRows F x.1 x.2.1) (glueRows F x.1 x.2.2)} :=
    hS.preimage ((measurable_glue1 F).prodMk (measurable_glue2 F))
  rw [← (mp_glueRows F).measure_preimage (hA.inter hB).nullMeasurableSet]
  exact resample_le (rowsInM F) (rowsOutM F) ((mp_glueRows F).measurable hA)
    ((mp_glueRows F).measurable hB) hSt
    (fun f r r' hr hst => hstab _ _ (glueRows_agree F f r r') hr hst)

/-- The error term of the resampling, split into a bad set of `w` and a bad set of `w'`. -/
theorem rows3M_err_le {B Bad Q : Set (Param N)} (hB : MeasurableSet B) (hBad : MeasurableSet Bad)
    (hQ : MeasurableSet Q) :
    rows3M F {x | glueRows F x.1 x.2.1 ∈ B ∧
        (glueRows F x.1 x.2.1 ∈ Bad ∨ glueRows F x.1 x.2.2 ∈ Q)} ≤
      cubeM N (B ∩ Bad) +
        ∫⁻ f, rowsOutM F {g | glueRows F f g ∈ B} * rowsOutM F {g | glueRows F f g ∈ Q} ∂rowsInM F := by
  have hsub : {x : (F → Fin N → ℝ) × ({r // r ∉ F} → Fin N → ℝ) × ({r // r ∉ F} → Fin N → ℝ) |
      glueRows F x.1 x.2.1 ∈ B ∧ (glueRows F x.1 x.2.1 ∈ Bad ∨ glueRows F x.1 x.2.2 ∈ Q)} ⊆
      {x | glueRows F x.1 x.2.1 ∈ B ∩ Bad} ∪
        {x | glueRows F x.1 x.2.1 ∈ B ∧ glueRows F x.1 x.2.2 ∈ Q} := by
    rintro x ⟨h1, h2 | h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [rows3M_marginal_one F (hB.inter hBad), rows3M_resample_eq F hB hQ]

/-- `∫ P(X | f) P(Y | f) df ≤ ε P(Y) + P(Y ∩ {f ∉ G})` if `P(X | f) ≤ ε` on `G`. -/
theorem rows_lintegral_mul_le {X Y : Set (Param N)} (hY : MeasurableSet Y)
    {G : Set (F → Fin N → ℝ)} (hG : MeasurableSet G) {ε : ENNReal}
    (hε : ∀ f ∈ G, rowsOutM F {g | glueRows F f g ∈ X} ≤ ε) :
    ∫⁻ f, rowsOutM F {g | glueRows F f g ∈ X} * rowsOutM F {g | glueRows F f g ∈ Y} ∂rowsInM F ≤
      ε * cubeM N Y + cubeM N (Y ∩ {w | restrIn F w ∉ G}) := by
  have hmY : Measurable fun f => rowsOutM F {g | glueRows F f g ∈ Y} :=
    measurable_measure_prodMk_left ((mp_glueRows F).measurable hY)
  have hpt : ∀ f, rowsOutM F {g | glueRows F f g ∈ X} * rowsOutM F {g | glueRows F f g ∈ Y} ≤
      ε * rowsOutM F {g | glueRows F f g ∈ Y} +
        Gᶜ.indicator (fun f => rowsOutM F {g | glueRows F f g ∈ Y}) f := by
    intro f
    by_cases hf : f ∈ G
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.2 hf), add_zero]
      exact mul_le_mul_left (hε f hf) _
    · rw [Set.indicator_of_mem (Set.mem_compl hf)]
      calc rowsOutM F {g | glueRows F f g ∈ X} * rowsOutM F {g | glueRows F f g ∈ Y}
          ≤ 1 * rowsOutM F {g | glueRows F f g ∈ Y} := mul_le_mul_left prob_le_one _
        _ ≤ _ := by rw [one_mul]; exact le_add_self
  calc _ ≤ ∫⁻ f, (ε * rowsOutM F {g | glueRows F f g ∈ Y} +
          Gᶜ.indicator (fun f => rowsOutM F {g | glueRows F f g ∈ Y}) f) ∂rowsInM F :=
        lintegral_mono hpt
    _ = ε * ∫⁻ f, rowsOutM F {g | glueRows F f g ∈ Y} ∂rowsInM F +
          ∫⁻ f in Gᶜ, rowsOutM F {g | glueRows F f g ∈ Y} ∂rowsInM F := by
        rw [lintegral_add_left (hmY.const_mul ε), lintegral_const_mul ε hmY,
          lintegral_indicator hG.compl]
    _ = _ := by
        rw [← cubeM_eq_lintegral_rows F hY, ← cubeM_inter_restrIn_eq F hY hG.compl]
        rfl

/-- **Combined resampling bound (for E1).** With `A` the small event, `B` the event to be
preserved, `Bad` the unstable part of `B` and `Q` the irregular fresh rows:
`P(A ∩ B) ≤ (ε + δ) P(B) + 2 P(B ∩ {f ∉ G}) + P(B ∩ Bad)`. -/
theorem cubeM_resample_bound {A B Bad Q : Set (Param N)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hBad : MeasurableSet Bad) (hQ : MeasurableSet Q)
    {G : Set (F → Fin N → ℝ)} (hG : MeasurableSet G) {ε δ : ENNReal}
    (hstab : ∀ w w', (∀ r ∈ F, w' r = w r) → w ∈ B → w ∉ Bad → w' ∉ Q → w' ∈ B)
    (hε : ∀ f ∈ G, rowsOutM F {g | glueRows F f g ∈ A} ≤ ε)
    (hδ : ∀ f ∈ G, rowsOutM F {g | glueRows F f g ∈ Q} ≤ δ) :
    cubeM N (A ∩ B) ≤
      (ε + δ) * cubeM N B + 2 * cubeM N (B ∩ {w | restrIn F w ∉ G}) + cubeM N (B ∩ Bad) := by
  have hS : MeasurableSet {p : Param N × Param N | p.1 ∉ Bad ∧ p.2 ∉ Q} :=
    (hBad.compl.preimage measurable_fst).inter (hQ.compl.preimage measurable_snd)
  have h1 := cubeM_resample_le F (fun w w' => w ∉ Bad ∧ w' ∉ Q) hA hB hS
    (fun w w' h hw hst => hstab w w' h hw hst.1 hst.2)
  have h2 : rows3M F {x | glueRows F x.1 x.2.1 ∈ B ∧
      ¬ (glueRows F x.1 x.2.1 ∉ Bad ∧ glueRows F x.1 x.2.2 ∉ Q)} ≤
      cubeM N (B ∩ Bad) +
        ∫⁻ f, rowsOutM F {g | glueRows F f g ∈ B} * rowsOutM F {g | glueRows F f g ∈ Q} ∂rowsInM F := by
    refine (measure_mono ?_).trans (rows3M_err_le F hB hBad hQ)
    rintro x ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra h
    push Not at h
    exact h2 h
  have h3 := rows_lintegral_mul_le F hB hG hε
  have h4 : ∫⁻ f, rowsOutM F {g | glueRows F f g ∈ B} * rowsOutM F {g | glueRows F f g ∈ Q}
      ∂rowsInM F ≤ δ * cubeM N B + cubeM N (B ∩ {w | restrIn F w ∉ G}) := by
    simp_rw [mul_comm (rowsOutM F {g | glueRows F _ g ∈ B})]
    exact rows_lintegral_mul_le F hB hG hδ
  calc cubeM N (A ∩ B) ≤ (ε * cubeM N B + cubeM N (B ∩ {w | restrIn F w ∉ G})) +
        (cubeM N (B ∩ Bad) + (δ * cubeM N B + cubeM N (B ∩ {w | restrIn F w ∉ G}))) :=
        h1.trans (add_le_add h3 (h2.trans (add_le_add le_rfl h4)))
    _ = _ := by ring

end Rows

/-! ### The sensitive rows `sensRows s r0` and the fresh rows -/

section Sens

variable {N : ℕ}

/-- The law of the sensitive-row data `f` (the rows of `sensRows s r0`). -/
abbrev sensM (N : ℕ) (s r0 : State N) : Measure (sensRows s r0 → Fin N → ℝ) :=
  rowsInM (sensRows s r0)

/-- The law of the fresh rows (the rows outside `sensRows s r0`), `freshM` of module D3. -/
abbrev freshM (N : ℕ) (s r0 : State N) : Measure ({r // r ∉ sensRows s r0} → Fin N → ℝ) :=
  rowsOutM (sensRows s r0)

/-- The parameter with sensitive rows `f` and fresh rows `g` (the `glue f g` of module D3). -/
abbrev b1Glue {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ)
    (g : {r // r ∉ sensRows s r0} → Fin N → ℝ) : Param N :=
  glueRows (sensRows s r0) f g

lemma b1Restr_eq_restrIn (s r0 : State N) (w : Param N) :
    b1Restr s r0 w = restrIn (sensRows s r0) w := rfl

@[simp] lemma b1Restr_b1Glue {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ)
    (g : {r // r ∉ sensRows s r0} → Fin N → ℝ) : b1Restr s r0 (b1Glue f g) = f :=
  restrIn_glueRows _ f g

/-- `f ∈ GoodF` iff the glued parameter satisfies the `F`-part of `Forced`. -/
theorem b1Glue_mem_GoodF_iff {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ)
    (g : {r // r ∉ sensRows s r0} → Fin N → ℝ) :
    f ∈ GoodF N s r0 ↔ B1FGood N s r0 (b1Glue f g) :=
  b1_mem_GoodF_iff_of_agree fun _ hr => glueRows_of_mem _ f g hr

theorem mp_b1Glue (s r0 : State N) :
    MeasurePreserving (fun p : (sensRows s r0 → Fin N → ℝ) ×
        ({r // r ∉ sensRows s r0} → Fin N → ℝ) => b1Glue p.1 p.2)
      ((sensM N s r0).prod (freshM N s r0)) (cubeM N) :=
  mp_glueRows _

theorem cubeM_eq_lintegral_fresh (s r0 : State N) {X : Set (Param N)} (hX : MeasurableSet X) :
    cubeM N X = ∫⁻ f, freshM N s r0 {g | b1Glue f g ∈ X} ∂sensM N s r0 :=
  cubeM_eq_lintegral_rows _ hX

theorem cubeM_goodF (s r0 : State N) :
    cubeM N {w | b1Restr s r0 w ∈ GoodF N s r0} = sensM N s r0 (GoodF N s r0) :=
  cubeM_restrIn_preimage _ _

/-- The count step: if `P(X | f) ≤ δ` for every `f ∈ GoodF`, then
`P(X ∩ {f ∈ GoodF}) ≤ δ P(f ∈ GoodF)`. -/
theorem cubeM_inter_goodF_le (s r0 : State N) {X : Set (Param N)} (hX : MeasurableSet X)
    {δ : ENNReal} (h : ∀ f ∈ GoodF N s r0, freshM N s r0 {g | b1Glue f g ∈ X} ≤ δ) :
    cubeM N (X ∩ {w | b1Restr s r0 w ∈ GoodF N s r0}) ≤ δ * sensM N s r0 (GoodF N s r0) :=
  cubeM_inter_restrIn_le _ hX (measurableSet_GoodF s r0) h

end Sens

/-! ## 5. Entries of the parameter cube -/

section Entries

variable {N : ℕ}

/-- The law of the entries of the cube, indexed by (row, column). -/
def entM (N : ℕ) : Measure (State N × Fin N → ℝ) := Measure.pi fun _ => unif

instance : IsProbabilityMeasure (entM N) := by unfold entM; infer_instance

/-- Uncurrying the parameters. -/
def uncurryE (N : ℕ) : Param N ≃ᵐ (State N × Fin N → ℝ) :=
  (MeasurableEquiv.curry (State N) (Fin N) ℝ).symm

lemma uncurryE_apply (w : Param N) (q : State N × Fin N) : uncurryE N w q = w q.1 q.2 := rfl

lemma uncurryE_symm_apply (x : State N × Fin N → ℝ) (r : State N) (i : Fin N) :
    (uncurryE N).symm x r i = x (r, i) := rfl

theorem mp_uncurryE : MeasurePreserving (uncurryE N) (cubeM N) (entM N) := by
  refine ⟨(uncurryE N).measurable, ?_⟩
  have := Measure.infinitePi_map_curry_symm (X := ℝ) (fun (_ : State N) (_ : Fin N) => unif)
  simp only [Measure.infinitePi_eq_pi] at this
  exact this

/-- Replace the entries in `C` of `w` by those of `η`. -/
def replE (C : Finset (State N × Fin N)) (w η : Param N) : Param N :=
  fun r i => if (r, i) ∈ C then η r i else w r i

lemma replE_eq (C : Finset (State N × Fin N)) (w η : Param N) :
    replE C w η = (uncurryE N).symm (replS C (uncurryE N w) (uncurryE N η)) := rfl

/-- Replacing a block of entries by an independent copy preserves `cubeM`. -/
theorem mp_replE (C : Finset (State N × Fin N)) :
    MeasurePreserving (fun p : Param N × Param N => replE C p.1 p.2)
      ((cubeM N).prod (cubeM N)) (cubeM N) := by
  have h1 := (mp_uncurryE (N := N)).prod (mp_uncurryE (N := N))
  have h2 := mp_replS (fun _ : State N × Fin N => unif) C
  have h3 := (mp_uncurryE (N := N)).symm (uncurryE N)
  exact h3.comp (h2.comp h1)

/-- `X ⊆ Param N` is determined by the entries in `C`. -/
def DetOnE (C : Finset (State N × Fin N)) (X : Set (Param N)) : Prop :=
  ∀ w w' : Param N, (∀ q ∈ C, w q.1 q.2 = w' q.1 q.2) → (w ∈ X ↔ w' ∈ X)

lemma DetOnE.mono {C D : Finset (State N × Fin N)} {X : Set (Param N)} (h : DetOnE C X)
    (hCD : C ⊆ D) : DetOnE D X :=
  fun w w' hw => h w w' fun q hq => hw q (hCD hq)

lemma DetOnE.inter {C : Finset (State N × Fin N)} {X Y : Set (Param N)} (hX : DetOnE C X)
    (hY : DetOnE C Y) : DetOnE C (X ∩ Y) :=
  fun w w' hw => and_congr (hX w w' hw) (hY w w' hw)

lemma DetOnE.compl {C : Finset (State N × Fin N)} {X : Set (Param N)} (hX : DetOnE C X) :
    DetOnE C Xᶜ :=
  fun w w' hw => not_congr (hX w w' hw)

/-- Rows determine entries: a set determined by the rows `F` is determined by `F × univ`. -/
lemma detOnE_of_rows {F : Finset (State N)} {X : Set (Param N)}
    (h : ∀ w w' : Param N, (∀ r ∈ F, w r = w' r) → (w ∈ X ↔ w' ∈ X)) :
    DetOnE (F ×ˢ univ) X :=
  fun w w' hw => h w w' fun r hr => funext fun i => hw (r, i) (Finset.mem_product.2 ⟨hr, mem_univ i⟩)

lemma DetOnE.replE_out {C : Finset (State N × Fin N)} {X : Set (Param N)} (h : DetOnE Cᶜ X)
    (w η : Param N) : replE C w η ∈ X ↔ w ∈ X := by
  refine h _ _ fun q hq => ?_
  have : q ∉ C := Finset.mem_compl.1 hq
  simp [replE, this]

lemma DetOnE.replE_in {C : Finset (State N × Fin N)} {X : Set (Param N)} (h : DetOnE C X)
    (w η : Param N) : replE C w η ∈ X ↔ η ∈ X := by
  refine h _ _ fun q hq => ?_
  simp [replE, hq]

/-- **Conditioning on the entries outside a block `C`** (Fubini form). -/
theorem cubeM_inter_eq_setLIntegralE (C : Finset (State N × Fin N)) {X Y : Set (Param N)}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (hXd : DetOnE Cᶜ X) :
    cubeM N (X ∩ Y) = ∫⁻ w in X, cubeM N {η | replE C w η ∈ Y} ∂cubeM N :=
  measure_inter_eq_repl (mp_replE C) hX hY hXd.replE_out

/-- Conditional bound over a block `C` of entries. -/
theorem cubeM_inter_le_of_sectionE (C : Finset (State N × Fin N)) {X Y : Set (Param N)}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (hXd : DetOnE Cᶜ X) {p : ENNReal}
    (hp : ∀ w ∈ X, cubeM N {η | replE C w η ∈ Y} ≤ p) : cubeM N (X ∩ Y) ≤ p * cubeM N X :=
  measure_inter_le_repl (mp_replE C) hX hY hXd.replE_out hp

/-- **Independence of events determined by disjoint sets of entries.** -/
theorem cubeM_inter_eq_mul_of_detOnE {C D : Finset (State N × Fin N)} (hCD : Disjoint C D)
    {X Y : Set (Param N)} (hX : MeasurableSet X) (hY : MeasurableSet Y) (hXd : DetOnE C X)
    (hYd : DetOnE D Y) : cubeM N (X ∩ Y) = cubeM N X * cubeM N Y :=
  measure_inter_eq_mul_repl (mp_replE D) hX hY
    (hXd.mono (Finset.subset_compl_iff_disjoint_right.2 hCD)).replE_out hYd.replE_in

/-- Finitely many events determined by pairwise disjoint sets of entries are independent. -/
theorem cubeM_iInter_eq_prod_of_detOnE {κ : Type*} [DecidableEq κ] (J : Finset κ)
    (C : κ → Finset (State N × Fin N)) (hC : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → Disjoint (C j) (C k))
    {X : κ → Set (Param N)} (hX : ∀ j ∈ J, MeasurableSet (X j))
    (hXd : ∀ j ∈ J, DetOnE (C j) (X j)) :
    cubeM N (⋂ j ∈ J, X j) = ∏ j ∈ J, cubeM N (X j) :=
  measure_iInter_eq_prod_repl (rp := fun j => replE (C j)) J (fun j _ => mp_replE (C j)) hX
    (fun j hj => (hXd j hj).replE_in)
    (fun j hj k hk hjk =>
      ((hXd j hj).mono (Finset.subset_compl_iff_disjoint_right.2 (hC j hj k hk hjk))).replE_out)

/-- **Product bound for events on disjoint private sets of entries given the rest.**
Private blocks `C j` pairwise disjoint and disjoint from the shared block `R`; `G` determined by
`R`, `X j` by `C j ∪ R`; for `w ∈ G` the conditional probability of `X j` given the entries
outside `C j` is `≤ p j`.  Then `P(G ∩ ⋂ X j) ≤ (∏ p j) P(G)`. -/
theorem cubeM_prod_bound_private {κ : Type*} [DecidableEq κ] (J : Finset κ)
    (C : κ → Finset (State N × Fin N)) (R : Finset (State N × Fin N))
    (hC : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → Disjoint (C j) (C k)) (hR : ∀ j ∈ J, Disjoint R (C j))
    {G : Set (Param N)} {X : κ → Set (Param N)} (hG : MeasurableSet G)
    (hX : ∀ j ∈ J, MeasurableSet (X j)) (hGd : DetOnE R G) (hXd : ∀ j ∈ J, DetOnE (C j ∪ R) (X j))
    {p : κ → ENNReal} (hp : ∀ j ∈ J, ∀ w ∈ G, cubeM N {η | replE (C j) w η ∈ X j} ≤ p j) :
    cubeM N (G ∩ ⋂ j ∈ J, X j) ≤ (∏ j ∈ J, p j) * cubeM N G :=
  measure_inter_iInter_le_prod_repl (rp := fun j => replE (C j)) J (fun j _ => mp_replE (C j))
    hG hX
    (fun j hj => (hGd.mono (Finset.subset_compl_iff_disjoint_right.2 (hR j hj))).replE_out)
    (fun j hj k hk hjk => ((hXd j hj).mono (Finset.union_subset
      (Finset.subset_compl_iff_disjoint_right.2 (hC j hj k hk hjk))
      (Finset.subset_compl_iff_disjoint_right.2 (hR k hk)))).replE_out)
    hp

/-- **Stopping set of entries** ("determined by" form). -/
theorem cubeM_stopping_set_indep (Priv : Param N → Finset (State N × Fin N))
    (A : Finset (State N × Fin N)) (hP : MeasurableSet {w | Priv w = A})
    (hPd : DetOnE Aᶜ {w | Priv w = A}) {X Y : Set (Param N)} (hX : MeasurableSet X)
    (hY : MeasurableSet Y) (hXd : DetOnE Aᶜ X) (hYd : DetOnE A Y) :
    cubeM N ({w | Priv w = A} ∩ X ∩ Y) = cubeM N ({w | Priv w = A} ∩ X) * cubeM N Y :=
  cubeM_inter_eq_mul_of_detOnE disjoint_compl_left (hP.inter hX) hY (hPd.inter hXd) hYd

/-- **`stopping_set_iid` for entries (blueprint A3, G6(e)).** If `{Priv = A}` is the event
`{w|_{Aᶜ} ∈ G}` of the entries outside `A`, then given it (and any event `Eo` of the outside
entries) the entries on `A` are iid uniform:
`P(Priv = A ∧ w|_{Aᶜ} ∈ Eo ∧ w|_A ∈ Ei) = unif^{Aᶜ}(G ∩ Eo) · unif^A(Ei)`. -/
theorem cubeM_stopping_set_iid (Priv : Param N → Finset (State N × Fin N))
    (A : Finset (State N × Fin N)) (G : Set ({q // q ∉ A} → ℝ))
    (hPG : ∀ w, Priv w = A ↔ (fun q : {q // q ∉ A} => w q.1.1 q.1.2) ∈ G)
    (Eo : Set ({q // q ∉ A} → ℝ)) (Ei : Set ({q // q ∈ A} → ℝ)) :
    cubeM N {w | Priv w = A ∧ (fun q : {q // q ∉ A} => w q.1.1 q.1.2) ∈ Eo ∧
        (fun q : {q // q ∈ A} => w q.1.1 q.1.2) ∈ Ei} =
      (Measure.pi fun _ : {q // q ∉ A} => unif) (G ∩ Eo) *
        (Measure.pi fun _ : {q // q ∈ A} => unif) Ei := by
  have h := stopping_set_iid (fun _ : State N × Fin N => unif) (fun x => Priv ((uncurryE N).symm x))
    A G (fun x => hPG ((uncurryE N).symm x)) Eo Ei
  have hset : {w : Param N | Priv w = A ∧ (fun q : {q // q ∉ A} => w q.1.1 q.1.2) ∈ Eo ∧
      (fun q : {q // q ∈ A} => w q.1.1 q.1.2) ∈ Ei} =
      uncurryE N ⁻¹' {x | Priv ((uncurryE N).symm x) = A ∧ (fun i : {q // q ∉ A} => x i) ∈ Eo ∧
        (fun i : {q // q ∈ A} => x i) ∈ Ei} := rfl
  rw [hset, mp_uncurryE.measure_preimage_equiv]
  exact h

/-- **Random stopping set of entries**: given the stopping set, the entries on it are iid. -/
theorem cubeM_stopping_le (Priv : Param N → Finset (State N × Fin N))
    (hP : ∀ A, MeasurableSet {w | Priv w = A}) (hPd : ∀ A, DetOnE Aᶜ {w | Priv w = A})
    {X Y : Finset (State N × Fin N) → Set (Param N)}
    (hX : ∀ A, MeasurableSet (X A)) (hY : ∀ A, MeasurableSet (Y A))
    (hXd : ∀ A, DetOnE Aᶜ (X A)) (hYd : ∀ A, DetOnE A (Y A)) {q : ENNReal}
    (hq : ∀ A, cubeM N (Y A) ≤ q) :
    cubeM N {w | w ∈ X (Priv w) ∧ w ∈ Y (Priv w)} ≤ q * cubeM N {w | w ∈ X (Priv w)} := by
  rw [measure_eq_sum_partition (cubeM N) hP, measure_eq_sum_partition (cubeM N) hP
    {w | w ∈ X (Priv w)}, Finset.mul_sum]
  refine Finset.sum_le_sum fun A _ => ?_
  have hs1 : {w : Param N | w ∈ X (Priv w) ∧ w ∈ Y (Priv w)} ∩ {w | Priv w = A} =
      {w | Priv w = A} ∩ X A ∩ Y A := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; rw [h3] at h1 h2; exact ⟨⟨h3, h1⟩, h2⟩
    · rintro ⟨⟨h3, h1⟩, h2⟩; rw [h3]; exact ⟨⟨h1, h2⟩, rfl⟩
  have hs2 : {w : Param N | w ∈ X (Priv w)} ∩ {w | Priv w = A} = {w | Priv w = A} ∩ X A := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; rw [h2] at h1; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; rw [h2]; exact ⟨h1, rfl⟩
  rw [hs1, hs2, cubeM_stopping_set_indep Priv A (hP A) (hPd A) (hX A) (hY A) (hXd A) (hYd A),
    mul_comm]
  gcongr
  exact hq A

/-- The entries of a fixed set `A` are iid uniform under `cubeM`. -/
theorem mp_restrictE (A : Finset (State N × Fin N)) :
    MeasurePreserving (fun (w : Param N) (q : {q // q ∈ A}) => w q.1.1 q.1.2) (cubeM N)
      (Measure.pi fun _ : {q // q ∈ A} => unif) := by
  have h1 := measurePreserving_piEquivPiSubtypeProd (fun _ : State N × Fin N => unif)
    (fun q => q ∈ A)
  have h2 := measurePreserving_fst.comp (h1.comp (mp_uncurryE (N := N)))
  rw [b1p_pi_fintype_irrel (fun _ : {q // q ∈ A} => unif) (Finset.Subtype.fintype A)
    (Subtype.fintype _)]
  exact h2

/-- **The product structure of `cubeM` over a set of entries `A` and its complement.** -/
theorem mp_splitEntries (A : Finset (State N × Fin N)) :
    MeasurePreserving (fun w : Param N => ((fun q : {q // q ∈ A} => w q.1.1 q.1.2),
        (fun q : {q // q ∉ A} => w q.1.1 q.1.2))) (cubeM N)
      ((Measure.pi fun _ : {q // q ∈ A} => unif).prod
        (Measure.pi fun _ : {q // q ∉ A} => unif)) := by
  have h1 := measurePreserving_piEquivPiSubtypeProd (fun _ : State N × Fin N => unif)
    (fun q => q ∈ A)
  have h2 := h1.comp (mp_uncurryE (N := N))
  rw [b1p_pi_fintype_irrel (fun _ : {q // q ∈ A} => unif) (Finset.Subtype.fintype A)
    (Subtype.fintype _)]
  exact h2

/-! ### One entry: the Fubini window -/

/-- `w` with the entry `a` set to `x`. -/
def setE (w : Param N) (a : State N × Fin N) (x : ℝ) : Param N :=
  fun r i => if (r, i) = a then x else w r i

lemma measurable_setE (w : Param N) (a : State N × Fin N) : Measurable (setE w a) := by
  refine Measurable.of_eval fun r => Measurable.of_eval fun i => ?_
  by_cases h : (r, i) = a
  · simp only [setE, h, ↓reduceIte]; exact measurable_id
  · simp only [setE, h, ↓reduceIte]; exact measurable_const

lemma replE_singleton (w η : Param N) (a : State N × Fin N) :
    replE {a} w η = setE w a (η a.1 a.2) := by
  funext r i
  by_cases h : (r, i) = a
  · subst h; simp [replE, setE]
  · simp [replE, setE, h]

/-- `unif` is the Lebesgue measure on `[0, 1]`. -/
lemma unif_apply {S : Set ℝ} (hS : MeasurableSet S) : unif S = volume (S ∩ Set.Icc 0 1) :=
  Measure.restrict_apply hS

/-- The section of `S` in one entry, under `cubeM`, is the `unif`-measure of the entry section. -/
lemma cubeM_section_entry (w : Param N) (a : State N × Fin N) {S : Set (Param N)}
    (hS : MeasurableSet S) :
    cubeM N {η | replE {a} w η ∈ S} = unif {x | setE w a x ∈ S} := by
  have : {η : Param N | replE {a} w η ∈ S} =
      (fun η : Param N => η a.1 a.2) ⁻¹' {x | setE w a x ∈ S} := by
    ext η; simp [replE_singleton]
  rw [this]
  exact (mp_coord a.1 a.2).measure_preimage (measurable_setE w a hS).nullMeasurableSet

/-- **`fubini_window` on the cube, over one entry `a`** (e.g. the pair-private entry of D2).
If for a.e. `w` the section `{x ∈ [0,1] | setE w a x ∈ B}` has Lebesgue measure `≥ c` whenever it
is not null, and the section of `B ∩ W` has measure `≤ δ`, then `c P(B ∩ W) ≤ δ P(B)`. -/
theorem cubeM_fubini_window (a : State N × Fin N) {B W : Set (Param N)} (hB : MeasurableSet B)
    (hW : MeasurableSet W) {c δ : ENNReal}
    (h : ∀ᵐ w ∂cubeM N, (unif {x | setE w a x ∈ B} ≠ 0 → c ≤ unif {x | setE w a x ∈ B}) ∧
      unif {x | setE w a x ∈ B ∩ W} ≤ δ) :
    c * cubeM N (B ∩ W) ≤ δ * cubeM N B := by
  have hr := mp_replE (N := N) {a}
  have hm1 : Measurable fun w => cubeM N {η | replE {a} w η ∈ B ∩ W} :=
    measurable_measure_prodMk_left (hr.measurable (hB.inter hW))
  have hm2 : Measurable fun w => cubeM N {η | replE {a} w η ∈ B} :=
    measurable_measure_prodMk_left (hr.measurable hB)
  rw [measure_eq_lintegral_repl hr (hB.inter hW), measure_eq_lintegral_repl hr hB,
    ← lintegral_const_mul _ hm1, ← lintegral_const_mul _ hm2]
  refine lintegral_mono_ae (h.mono fun w hw => ?_)
  rw [cubeM_section_entry w a (hB.inter hW), cubeM_section_entry w a hB]
  exact b1p_window_pt (measure_mono fun x hx => hx.1) hw.1 hw.2

/-- `cubeM_fubini_window` in the form `P(B ∩ W) ≤ (δ / c) P(B)`. -/
theorem cubeM_fubini_window_div (a : State N × Fin N) {B W : Set (Param N)}
    (hB : MeasurableSet B) (hW : MeasurableSet W) {c δ : ENNReal} (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (h : ∀ᵐ w ∂cubeM N, (unif {x | setE w a x ∈ B} ≠ 0 → c ≤ unif {x | setE w a x ∈ B}) ∧
      unif {x | setE w a x ∈ B ∩ W} ≤ δ) :
    cubeM N (B ∩ W) ≤ δ / c * cubeM N B :=
  b1p_div_of_mul_le hc0 hct (cubeM_fubini_window a hB hW h)

end Entries

/-! ## 6. Summing over the maximal row -/

section Argmax

variable {N : ℕ}

lemma iUnion_inter_tcRow (B : Set (Param N)) : (⋃ r0, B ∩ {w | tcRow w = r0}) = B := by
  ext w
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨tcRow w, h, rfl⟩⟩

lemma pairwise_disjoint_tcRow (B : Set (Param N)) :
    Pairwise (Function.onFun Disjoint fun r0 : State N => B ∩ {w | tcRow w = r0}) := by
  intro a b hab
  exact Set.disjoint_left.2 fun w h1 h2 => hab (h1.2.symm.trans h2.2)

/-- **`sum_over_argmax` (blueprint A3).** `B = ⋃_{r0} (B ∩ {tcRow = r0})` is a disjoint union of
pieces cut out by measurable sets, so `P(B) = ∑_{r0} P(B ∩ {tcRow = r0})` for EVERY `B`. -/
theorem sum_over_argmax (B : Set (Param N)) :
    cubeM N B = ∑ r0, cubeM N (B ∩ {w | tcRow w = r0}) :=
  measure_eq_sum_partition (cubeM N) measurableSet_tcRow_eq B

end Argmax

end

end Census
end IIT
