/-
Census of complexes: isolating one column of the parameter cube.

* `cubeM N` is the image of `colLaw N ⊗ restLaw N i` under `glue i` (`mp_glue`): column `i` is an
  iid uniform family indexed by the rows, independent of all other entries;
* a bound on every fibre `{c | glue i c ρ ∈ X}` bounds `cubeM N X` (`cubeM_le_of_fiber`);
* the row statistics without column `i` (`Qw`, `ZQ`, `SQ2`, `subSum`, `blockQ`, `Vp`) do not depend
  on the column (`Qw_glue` and its consequences);
* rows are independent under `cubeM N`, column entries are independent under `colLaw N`, and
  monomials in clamped entries have explicit moments.
-/
import IIT.Census.UnivProb
import IIT.Census.PairIndep
import IIT.Census.BigPhiStats

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

noncomputable section

variable {N : ℕ}

lemma clamp01_measurable : Measurable clamp01 := by
  unfold clamp01
  exact measurable_const.max (measurable_const.min measurable_id)

lemma Qw_le_one (w : Param N) (i : Fin N) (r : State N) : Qw w i r ≤ 1 :=
  prod_le_one (fun _ _ => clamp01_nonneg _) fun _ _ => clamp01_le_one _

lemma Pw_le_one (w : Param N) (r : State N) : Pw w r ≤ 1 :=
  prod_le_one (fun _ _ => clamp01_nonneg _) fun _ _ => clamp01_le_one _

/-! ### Generic facts on iid products -/

section Generic

variable {I E : Type*} [Fintype I] [MeasurableSpace E]

lemma integral_pi_eval (μ0 : Measure E) [IsProbabilityMeasure μ0] {g : E → ℝ}
    (hg : AEStronglyMeasurable g μ0) (a : I) :
    ∫ x, g (x a) ∂(Measure.pi fun _ : I => μ0) = ∫ y, g y ∂μ0 := by
  have hmp := measurePreserving_eval (fun _ : I => μ0) a
  have hg' : AEStronglyMeasurable g ((Measure.pi fun _ : I => μ0).map (Function.eval a)) := by
    rw [hmp.map_eq]; exact hg
  rw [← integral_map hmp.measurable.aemeasurable hg', hmp.map_eq]

lemma integral_pi_mul_of_ne (μ0 : Measure E) [IsProbabilityMeasure μ0] {a b : I} (hab : a ≠ b)
    {g h : E → ℝ} (hg : Measurable g) (hh : Measurable h) :
    ∫ x, g (x a) * h (x b) ∂(Measure.pi fun _ : I => μ0) =
      (∫ y, g y ∂μ0) * ∫ y, h y ∂μ0 := by
  have hind : iIndepFun (fun (c : I) (x : I → E) => x c) (Measure.pi fun _ : I => μ0) :=
    iIndepFun_pi (X := fun (_ : I) (y : E) => y) fun _ => measurable_id.aemeasurable
  have h2 := (hind.indepFun hab).comp hg hh
  have := h2.integral_fun_mul_eq_mul_integral
    (hg.comp (measurable_pi_apply a)).aestronglyMeasurable
    (hh.comp (measurable_pi_apply b)).aestronglyMeasurable
  simp only [Function.comp_def] at this
  rw [this, integral_pi_eval μ0 hg.aestronglyMeasurable, integral_pi_eval μ0 hh.aestronglyMeasurable]

end Generic

lemma prod_pow_ite_erase {M : Type*} [CommMonoid M] (f : Fin N → M) (i : Fin N) (p : ℕ) :
    ∏ j, f j ^ (if j = i then 0 else p) = (∏ j ∈ univ.erase i, f j) ^ p := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i), ← prod_pow]
  simp only [↓reduceIte, pow_zero, one_mul]
  refine prod_congr rfl fun j hj => ?_
  simp [ne_of_mem_erase hj]

lemma card_erase_univ (i : Fin N) : (univ.erase i).card = N - 1 := by
  rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]

/-! ### Rows -/

/-- Monomials in the clamped entries of a row. -/
lemma integral_rowM_monomial (E : Fin N → ℕ) :
    ∫ v, ∏ j, clamp01 (v j) ^ E j ∂rowM N = ∏ j, 1 / ((E j : ℝ) + 1) :=
  integral_monomial E

lemma integral_rowQ_pow (i : Fin N) (p : ℕ) :
    ∫ v, (∏ j ∈ univ.erase i, clamp01 (v j)) ^ p ∂rowM N = (1 / ((p : ℝ) + 1)) ^ (N - 1) := by
  simp_rw [← prod_pow_ite_erase]
  rw [integral_rowM_monomial]
  have := prod_pow_ite_erase (fun _ : Fin N => 1 / ((p : ℝ) + 1)) i 1
  simp only [pow_one, prod_const, card_erase_univ] at this
  rw [← this]
  refine prod_congr rfl fun j _ => ?_
  split_ifs <;> simp

lemma integral_rowP_pow' (p : ℕ) :
    ∫ v, (∏ j, clamp01 (v j)) ^ p ∂rowM N = (1 / ((p : ℝ) + 1)) ^ N := by
  simp_rw [← prod_pow]
  rw [integral_rowM_monomial (fun _ => p), prod_const, card_univ, Fintype.card_fin]

lemma measurable_rowQ (i : Fin N) : Measurable fun v : Fin N → ℝ => ∏ j ∈ univ.erase i, clamp01 (v j) :=
  Finset.measurable_prod _ fun j _ => clamp01_measurable.comp (measurable_pi_apply j)

lemma measurable_rowPw : Measurable fun v : Fin N → ℝ => ∏ j, clamp01 (v j) :=
  Finset.measurable_prod _ fun j _ => clamp01_measurable.comp (measurable_pi_apply j)

/-! ### Moments and independence under `cubeM` -/

lemma measurable_Qw (i : Fin N) (r : State N) : Measurable fun w : Param N => Qw w i r :=
  (measurable_rowQ i).comp (measurable_pi_apply r)

lemma measurable_Pw (r : State N) : Measurable fun w : Param N => Pw w r :=
  measurable_rowPw.comp (measurable_pi_apply r)

lemma measurable_Zs : Measurable fun w : Param N => Zs w :=
  Finset.measurable_sum _ fun r _ => measurable_Pw r

lemma measurable_ZQ (i : Fin N) : Measurable fun w : Param N => ZQ w i :=
  Finset.measurable_sum _ fun r _ => measurable_Qw i r

lemma measurable_SQ2 (i : Fin N) : Measurable fun w : Param N => SQ2 w i :=
  Finset.measurable_sum _ fun r _ => (measurable_Qw i r).pow_const 2

lemma measurable_subSum (i : Fin N) (M : Finset (Fin N)) (m : State N) :
    Measurable fun w : Param N => subSum w i M m :=
  Finset.measurable_sum _ fun r _ => measurable_Qw i r

/-- Functions of distinct rows are independent under `cubeM N`. -/
lemma iIndepFun_rows {β : Type*} [MeasurableSpace β] (f : State N → (Fin N → ℝ) → β)
    (hf : ∀ r, Measurable (f r)) :
    iIndepFun (fun r (w : Param N) => f r (w r)) (cubeM N) := by
  unfold cubeM
  exact iIndepFun_pi (X := f) fun r => (hf r).aemeasurable

/-- The integral of a function of one row. -/
lemma integral_row_eval {g : (Fin N → ℝ) → ℝ} (hg : AEStronglyMeasurable g (rowM N)) (r : State N) :
    ∫ w, g (w r) ∂cubeM N = ∫ v, g v ∂rowM N :=
  integral_pi_eval (rowM N) hg r

/-- Functions of two distinct rows factor. -/
lemma integral_row_mul {r r' : State N} (hrr : r ≠ r') {g h : (Fin N → ℝ) → ℝ}
    (hg : Measurable g) (hh : Measurable h) :
    ∫ w, g (w r) * h (w r') ∂cubeM N = (∫ v, g v ∂rowM N) * ∫ v, h v ∂rowM N :=
  integral_pi_mul_of_ne (rowM N) hrr hg hh

/-- Monomials in all the clamped entries. -/
lemma integral_cubeM_monomial (E : State N → Fin N → ℕ) :
    ∫ w, ∏ r, ∏ j, clamp01 (w r j) ^ E r j ∂cubeM N = ∏ r, ∏ j, 1 / ((E r j : ℝ) + 1) := by
  unfold cubeM
  rw [integral_fintype_prod_eq_prod (fun r (v : Fin N → ℝ) => ∏ j, clamp01 (v j) ^ E r j)]
  exact prod_congr rfl fun r _ => integral_rowM_monomial (E r)

theorem integral_Qw_pow (i : Fin N) (r : State N) (p : ℕ) :
    ∫ w, Qw w i r ^ p ∂cubeM N = (1 / ((p : ℝ) + 1)) ^ (N - 1) := by
  rw [← integral_rowQ_pow i p]
  exact integral_row_eval (g := fun v => (∏ j ∈ univ.erase i, clamp01 (v j)) ^ p)
    ((measurable_rowQ i).pow_const p).aestronglyMeasurable r

theorem integral_Pw_pow (r : State N) (p : ℕ) :
    ∫ w, Pw w r ^ p ∂cubeM N = (1 / ((p : ℝ) + 1)) ^ N := by
  rw [← integral_rowP_pow' p]
  exact integral_row_eval (g := fun v => (∏ j, clamp01 (v j)) ^ p)
    (measurable_rowPw.pow_const p).aestronglyMeasurable r

theorem integral_Qw_pow_mul_pow (i : Fin N) {r r' : State N} (hrr : r ≠ r') (p q : ℕ) :
    ∫ w, Qw w i r ^ p * Qw w i r' ^ q ∂cubeM N =
      (1 / ((p : ℝ) + 1)) ^ (N - 1) * (1 / ((q : ℝ) + 1)) ^ (N - 1) := by
  rw [← integral_rowQ_pow i p, ← integral_rowQ_pow i q]
  exact integral_row_mul (g := fun v => (∏ j ∈ univ.erase i, clamp01 (v j)) ^ p)
    (h := fun v => (∏ j ∈ univ.erase i, clamp01 (v j)) ^ q) hrr
    ((measurable_rowQ i).pow_const p) ((measurable_rowQ i).pow_const q)

theorem integral_Pw_pow_mul_pow {r r' : State N} (hrr : r ≠ r') (p q : ℕ) :
    ∫ w, Pw w r ^ p * Pw w r' ^ q ∂cubeM N =
      (1 / ((p : ℝ) + 1)) ^ N * (1 / ((q : ℝ) + 1)) ^ N := by
  rw [← integral_rowP_pow' p, ← integral_rowP_pow' q]
  exact integral_row_mul (g := fun v => (∏ j, clamp01 (v j)) ^ p)
    (h := fun v => (∏ j, clamp01 (v j)) ^ q) hrr
    (measurable_rowPw.pow_const p) (measurable_rowPw.pow_const q)

/-- `E[Qw(r) Qw(r')] = 4^{-(N-1)}` for distinct rows. -/
theorem integral_Qw_mul (i : Fin N) {r r' : State N} (hrr : r ≠ r') :
    ∫ w, Qw w i r * Qw w i r' ∂cubeM N = (1 / 4 : ℝ) ^ (N - 1) := by
  have := integral_Qw_pow_mul_pow i hrr 1 1
  simp only [pow_one] at this
  rw [this, ← mul_pow]
  norm_num

lemma integrable_of_bdd_cubeM {f : Param N → ℝ} (hf : Measurable f) (C : ℝ)
    (h : ∀ w, |f w| ≤ C) : Integrable f (cubeM N) :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun w => by
    rw [Real.norm_eq_abs]; exact h w)

lemma integrable_Qw_pow (i : Fin N) (r : State N) (p : ℕ) :
    Integrable (fun w => Qw w i r ^ p) (cubeM N) :=
  integrable_of_bdd_cubeM ((measurable_Qw i r).pow_const p) 1 fun w => by
    rw [abs_of_nonneg (pow_nonneg (Qw_nonneg w i r) p)]
    exact pow_le_one₀ (Qw_nonneg w i r) (Qw_le_one w i r)

lemma integrable_Pw_pow (r : State N) (p : ℕ) :
    Integrable (fun w => Pw w r ^ p) (cubeM N) :=
  integrable_of_bdd_cubeM ((measurable_Pw r).pow_const p) 1 fun w => by
    rw [abs_of_nonneg (pow_nonneg (Pw_nonneg w r) p)]
    exact pow_le_one₀ (Pw_nonneg w r) (Pw_le_one w r)

/-! ### The column law -/

/-- The law of one column: iid uniform entries indexed by the rows. -/
def colLaw (N : ℕ) : Measure (State N → ℝ) := Measure.pi fun _ : State N => unif

/-- The entries outside column `i`, indexed by (row, column) pairs with column `≠ i`. -/
abbrev Rest (N : ℕ) (i : Fin N) := {q : State N × Fin N // ¬ q.2 = i} → ℝ

/-- The law of the entries outside column `i`. -/
def restLaw (N : ℕ) (i : Fin N) : Measure (Rest N i) := Measure.pi fun _ => unif

instance : IsProbabilityMeasure (colLaw N) := by unfold colLaw; infer_instance
instance (i : Fin N) : IsProbabilityMeasure (restLaw N i) := by unfold restLaw; infer_instance

/-- The parameter with column `i` equal to `c` and the other entries given by `ρ`. -/
def glue (i : Fin N) (c : State N → ℝ) (ρ : Rest N i) : Param N :=
  fun r j => if h : j = i then c r else ρ ⟨(r, j), h⟩

@[simp] lemma glue_self (i : Fin N) (c : State N → ℝ) (ρ : Rest N i) (r : State N) :
    glue i c ρ r i = c r := by
  simp [glue]

lemma glue_of_ne {i j : Fin N} (h : j ≠ i) (c : State N → ℝ) (ρ : Rest N i) (r : State N) :
    glue i c ρ r j = ρ ⟨(r, j), h⟩ := by
  simp [glue, h]

lemma glue_eq_of_ne {i j : Fin N} (h : j ≠ i) (c c' : State N → ℝ) (ρ : Rest N i) (r : State N) :
    glue i c ρ r j = glue i c' ρ r j := by
  rw [glue_of_ne h, glue_of_ne h]

lemma measurable_glue_col (i : Fin N) (ρ : Rest N i) : Measurable fun c => glue i c ρ := by
  refine Measurable.of_eval fun r => Measurable.of_eval fun j => ?_
  by_cases h : j = i
  · subst h; simp only [glue_self]; exact measurable_pi_apply r
  · simp only [glue_of_ne h]; exact measurable_const

/-- `glue i` carries `colLaw N ⊗ restLaw N i` to `cubeM N`. -/
theorem mp_glue (i : Fin N) :
    MeasurePreserving (fun p : (State N → ℝ) × Rest N i => glue i p.1 p.2)
      ((colLaw N).prod (restLaw N i)) (cubeM N) := by
  -- column: reindex rows as the pairs `(r, i)`
  have hinj : Function.Injective fun q : {q : State N × Fin N // q.2 = i} => q.1.1 := by
    rintro ⟨⟨r, j⟩, hj⟩ ⟨⟨r', j'⟩, hj'⟩ h
    simp only at hj hj' h
    subst hj hj' h; rfl
  have h1 : MeasurePreserving (fun (c : State N → ℝ) (q : {q : State N × Fin N // q.2 = i}) => c q.1.1)
      (colLaw N) (Measure.pi fun _ => unif) :=
    ⟨Measurable.of_eval fun q => measurable_pi_apply _,
      map_comp_inj (fun q : {q : State N × Fin N // q.2 = i} => q.1.1) hinj unif⟩
  have h2 := h1.prod (MeasurePreserving.id (restLaw N i))
  have h3 := (measurePreserving_piEquivPiSubtypeProd (fun _ : State N × Fin N => unif)
    (fun q : State N × Fin N => q.2 = i)).symm
  have h4 : MeasurePreserving (MeasurableEquiv.curry (State N) (Fin N) ℝ)
      (Measure.pi fun _ => unif) (cubeM N) := by
    refine ⟨MeasurableEquiv.measurable _, ?_⟩
    have := Measure.infinitePi_map_curry (X := ℝ) (fun (_ : State N) (_ : Fin N) => unif)
    simp only [Measure.infinitePi_eq_pi] at this
    exact this
  have h := (h4.comp h3).comp h2
  convert h using 1
  funext p
  funext r j
  by_cases hj : j = i
  · subst hj
    simp [glue, MeasurableEquiv.curry, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd]
  · simp [glue, hj, MeasurableEquiv.curry, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd]

lemma measurable_glue (i : Fin N) :
    Measurable fun p : (State N → ℝ) × Rest N i => glue i p.1 p.2 :=
  (mp_glue i).measurable

/-- `cubeM N X` as an average over the rest of the fibre measures. -/
lemma cubeM_eq_lintegral_fiber (i : Fin N) {X : Set (Param N)} (hX : MeasurableSet X) :
    cubeM N X = ∫⁻ ρ, colLaw N {c | glue i c ρ ∈ X} ∂restLaw N i := by
  rw [← (mp_glue i).measure_preimage hX.nullMeasurableSet,
    Measure.prod_apply_symm (measurable_glue i hX)]
  rfl

/-- **Fibre bound.** If every fibre of `X` over the entries outside column `i` has
`colLaw`-measure at most `δ`, then `cubeM N X ≤ δ`. -/
theorem cubeM_le_of_fiber (i : Fin N) {X : Set (Param N)} (hX : MeasurableSet X) {δ : ENNReal}
    (h : ∀ ρ, colLaw N {c | glue i c ρ ∈ X} ≤ δ) : cubeM N X ≤ δ := by
  rw [cubeM_eq_lintegral_fiber i hX]
  calc ∫⁻ ρ, colLaw N {c | glue i c ρ ∈ X} ∂restLaw N i ≤ ∫⁻ _, δ ∂restLaw N i :=
        lintegral_mono fun ρ => h ρ
    _ = δ := by simp

/-- Fibre bound on a good set: it suffices to bound the fibres of `X` over the rests `ρ` for
which some parameter of the fibre lies in `G`. -/
theorem cubeM_inter_le_of_fiber (i : Fin N) {X G : Set (Param N)} (hX : MeasurableSet X)
    (hG : MeasurableSet G) {δ : ENNReal}
    (h : ∀ ρ c, glue i c ρ ∈ G → colLaw N {c | glue i c ρ ∈ X} ≤ δ) :
    cubeM N (X ∩ G) ≤ δ := by
  refine cubeM_le_of_fiber i (hX.inter hG) fun ρ => ?_
  by_cases hρ : ∃ c, glue i c ρ ∈ G
  · obtain ⟨c, hc⟩ := hρ
    exact (measure_mono fun c' hc' => hc'.1).trans (h ρ c hc)
  · push Not at hρ
    have : {c | glue i c ρ ∈ X ∩ G} = ∅ := by
      ext c; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      exact fun hc => hρ c hc.2
    rw [this, measure_empty]
    exact zero_le

/-- The law of column `i` under `cubeM N` is `colLaw N`. -/
lemma mp_col (i : Fin N) : MeasurePreserving (fun (w : Param N) (r : State N) => w r i)
    (cubeM N) (colLaw N) := by
  have hm : Measurable fun (w : Param N) (r : State N) => w r i :=
    Measurable.of_eval fun r => (measurable_pi_apply i).comp (measurable_pi_apply r)
  refine ⟨hm, ?_⟩
  rw [← (mp_glue i).map_eq, Measure.map_map hm (measurable_glue i)]
  have : ((fun (w : Param N) (r : State N) => w r i) ∘
      fun p : (State N → ℝ) × Rest N i => glue i p.1 p.2) = Prod.fst := by
    funext p r; simp
  rw [this, Measure.map_fst_prod, measure_univ, one_smul]

/-! ### Statistics without column `i` do not depend on the column -/

section Glue

variable (i : Fin N) (c c' : State N → ℝ) (ρ : Rest N i)

lemma Qw_glue (r : State N) : Qw (glue i c ρ) i r = Qw (glue i c' ρ) i r :=
  prod_congr rfl fun j hj => by rw [glue_eq_of_ne (ne_of_mem_erase hj)]

lemma Pw_glue (r : State N) : Pw (glue i c ρ) r = clamp01 (c r) * Qw (glue i c' ρ) i r := by
  rw [Pw_eq_mul_Qw, glue_self, Qw_glue i c c']

lemma Zs_glue : Zs (glue i c ρ) = ∑ r, clamp01 (c r) * Qw (glue i c' ρ) i r :=
  sum_congr rfl fun r _ => Pw_glue i c c' ρ r

lemma ZQ_glue : ZQ (glue i c ρ) i = ZQ (glue i c' ρ) i :=
  sum_congr rfl fun r _ => Qw_glue i c c' ρ r

lemma SQ2_glue : SQ2 (glue i c ρ) i = SQ2 (glue i c' ρ) i :=
  sum_congr rfl fun r _ => by rw [Qw_glue i c c']

lemma subSum_glue (M : Finset (Fin N)) (m : State N) :
    subSum (glue i c ρ) i M m = subSum (glue i c' ρ) i M m :=
  sum_congr rfl fun r _ => Qw_glue i c c' ρ r

lemma blockQ_glue (S : Finset (Fin N)) (r : State N) :
    blockQ (glue i c ρ) i S r = blockQ (glue i c' ρ) i S r :=
  subSum_glue i c c' ρ _ r

lemma Vp_glue (S : Finset (Fin N)) : Vp (glue i c ρ) i S = Vp (glue i c' ρ) i S :=
  sum_congr rfl fun r _ => by rw [Qw_glue i c c', blockQ_glue i c c']

lemma cNum_glue (S Y : Finset (Fin N)) (t : State N) :
    cNum (glue i c ρ) S Y t i = cNum (glue i c' ρ) S Y t i := by
  rw [cNum, cNum, ZQ_glue i c c', subSum_glue i c c']

lemma DQ_glue (S Y Y' : Finset (Fin N)) (t : State N) :
    DQ (glue i c ρ) S Y Y' t i = DQ (glue i c' ρ) S Y Y' t i := by
  rw [DQ, DQ, subSum_glue i c c', subSum_glue i c c']

lemma Xk_glue (k : ℕ) : Xk (glue i c ρ) k i = Xk (glue i c' ρ) k i :=
  sum_congr rfl fun r _ => sum_congr rfl fun r' _ => by rw [Qw_glue i c c', Qw_glue i c c']

end Glue

/-! ### Moments and independence under `colLaw` -/

/-- Functions of distinct column entries are independent under `colLaw N`. -/
lemma iIndepFun_col {β : Type*} [MeasurableSpace β] (f : State N → ℝ → β)
    (hf : ∀ r, Measurable (f r)) :
    iIndepFun (fun r (c : State N → ℝ) => f r (c r)) (colLaw N) := by
  unfold colLaw
  exact iIndepFun_pi (X := f) fun r => (hf r).aemeasurable

/-- Monomials in the clamped column entries. -/
lemma integral_col_monomial (E : State N → ℕ) :
    ∫ c, ∏ r, clamp01 (c r) ^ E r ∂colLaw N = ∏ r, 1 / ((E r : ℝ) + 1) :=
  integral_monomial E

lemma integral_col_eval {g : ℝ → ℝ} (hg : AEStronglyMeasurable g unif) (r : State N) :
    ∫ c, g (c r) ∂colLaw N = ∫ x, g x ∂unif :=
  integral_pi_eval unif hg r

lemma integral_col_pow (r : State N) (p : ℕ) :
    ∫ c, clamp01 (c r) ^ p ∂colLaw N = 1 / ((p : ℝ) + 1) := by
  rw [integral_col_eval (g := fun x => clamp01 x ^ p)
    (clamp01_measurable.pow_const p).aestronglyMeasurable r, integral_cl_pow]

lemma integral_col (r : State N) : ∫ c, clamp01 (c r) ∂colLaw N = 1 / 2 := by
  have := integral_col_pow (N := N) r 1
  simp only [pow_one] at this
  rw [this]; norm_num

/-- Second moments of the column entries. -/
theorem integral_col_mul (r r' : State N) :
    ∫ c, clamp01 (c r) * clamp01 (c r') ∂colLaw N = if r = r' then 1 / 3 else 1 / 4 := by
  split_ifs with h
  · subst h
    have := integral_col_pow (N := N) r 2
    simp only [sq] at this
    rw [this]; norm_num
  · rw [colLaw, integral_pi_mul_of_ne unif h clamp01_measurable clamp01_measurable]
    have := integral_cl_pow 1
    simp only [pow_one] at this
    rw [this]; norm_num

lemma integrable_of_bdd_col {f : (State N → ℝ) → ℝ} (hf : Measurable f) (C : ℝ)
    (h : ∀ c, |f c| ≤ C) : Integrable f (colLaw N) :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun c => by
    rw [Real.norm_eq_abs]; exact h c)

lemma integrable_col_cl (r : State N) : Integrable (fun c => clamp01 (c r)) (colLaw N) :=
  integrable_of_bdd_col (clamp01_measurable.comp (measurable_pi_apply r)) 1 fun c => by
    rw [abs_of_nonneg (clamp01_nonneg _)]; exact clamp01_le_one _

/-- The mean of a linear form in the clamped column entries. -/
theorem integral_col_linear (s : Finset (State N)) (a : State N → ℝ) :
    ∫ c, ∑ r ∈ s, a r * clamp01 (c r) ∂colLaw N = (∑ r ∈ s, a r) / 2 := by
  rw [integral_finsetSum s fun r _ => (integrable_col_cl r).const_mul (a r), sum_div]
  refine sum_congr rfl fun r _ => ?_
  rw [integral_const_mul, integral_col]; ring

end

end Census
end IIT
