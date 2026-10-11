/-
Census of complexes: generalised block summands.

The rows of a block (or of a superblock) are indexed by a finite type `K` and read as a family
`y : K → Fin N → ℝ` of iid rows.  A generalised block summand is the vector with coordinates
`bg_F ρ j c y p = (∑_u P_u(y) · clamp01 (y (ρ p u) (j p)) - c p) / σ_N`, where `P_u` is the product
of row `u`, `ρ p u` is the row of the block of `u` that carries the pattern of the coordinate `p`,
and `j p` is the unit of `p`.  For a single `k`-set, `ρ p` is constant and the summand is
`(W · clamp01 (y t j) - c) / σ_N`; for two `k`-sets, `ρ p` replaces the bits of one set.

This file proves, for an arbitrary finite `K`,
* the exact first moment `bg_integral_G` and the diagonal second moments `bg_integral_diag`;
* the zero means (`bg_nu_mean`), the second moments
  `|B ∫ x p x q dν - |K|⁻¹ ∑_u bg_corr| ≤ |K| (3/4)^N` (`bg_nu_second`), where `B |K| = 2^N`,
  and the third absolute moments `B ∫ (∑ |x p|)^3 dν ≤ 8 d^3 |K|^2 (23/25)^N` (`bg_nu_third`);
  the same with `B - 1` summands (`bg_nu_second_pred`, error `3 |K|^2 (3/4)^N`);
* for a parametrisation `g : Γ × K ≃ State N` of the rows by (superblock, row): the regrouping of
  the cause numerators (`bg_sum_X`), the iid law of the summands (`bg_map_X`, `bg_map_Xs`), the
  removal of the superblock of a state (`bg_map_Xr`, `bg_sum_eq_rest`, `bg_abs_sub_rest_le`) and
  the independence of the remaining summands from the rows of that superblock (`bg_indep_rest`);
* the parametrisation `bg_eqv` of the rows by the bits off and on the image of an injection
  `E : Fin n → Fin N`, and the merge rule `bg_merge_row`.
-/
import IIT.Census.PairBlocks

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

set_option linter.unusedSectionVars false

noncomputable section

variable {N : ℕ}

/-! ### Products with finitely many modified factors -/

lemma bg_prod_ratio {α : Type*} [Fintype α] (f g : α → ℝ) (s : Finset α)
    (hg : ∀ x, g x ≠ 0) (hfg : ∀ x ∉ s, f x = g x) :
    ∏ x, f x = (∏ x, g x) * ∏ x ∈ s, f x / g x := by
  have h : ∀ x, f x = g x * (f x / g x) := fun x => by field_simp [hg x]
  rw [Finset.prod_congr rfl fun x _ => h x, prod_mul_distrib]
  congr 1
  refine (Finset.prod_subset (subset_univ s) fun x _ hx => ?_).symm
  rw [hfg x hx, div_self (hg x)]

lemma bg_prod_base {K : Type*} [Fintype K] (u : K) (h : K → ℝ) (hh : ∀ t, t ≠ u → h t = 0) :
    ∏ t : K, ∏ _j : Fin N, 1 / (h t + 1) = (1 / (h u + 1)) ^ N := by
  rw [Fintype.prod_eq_single u fun t ht => by simp [hh t ht]]
  simp

section Generic

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The law of the rows of a block indexed by `K`. -/
def bg_blkM (N : ℕ) (K : Type*) [Fintype K] : Measure (K → Fin N → ℝ) :=
  Measure.pi fun _ => rowM N

instance (K : Type*) [Fintype K] : IsProbabilityMeasure (bg_blkM N K) := by
  unfold bg_blkM; infer_instance

/-- The uncentred part `∑_u P_u · clamp01 (y (ρ u) j)` of a coordinate. -/
def bg_G (ρ : K → K) (j : Fin N) (y : K → Fin N → ℝ) : ℝ :=
  ∑ u, pb_P y u * clamp01 (y (ρ u) j)

/-- For a constant `ρ` the uncentred part is `W · clamp01 (y t j)`. -/
lemma bg_G_const (t : K) (j : Fin N) (y : K → Fin N → ℝ) :
    bg_G (fun _ => t) j y = pb_W y * clamp01 (y t j) := by
  rw [bg_G, pb_W, sum_mul]

lemma bg_measurable_G (ρ : K → K) (j : Fin N) : Measurable (bg_G (N := N) ρ j) :=
  Finset.measurable_sum _ fun u _ => (pb_measurable_P u).mul (pb_measurable_cl _ _)

lemma bg_G_nonneg (ρ : K → K) (j : Fin N) (y : K → Fin N → ℝ) : 0 ≤ bg_G ρ j y :=
  sum_nonneg fun u _ => mul_nonneg (pb_P_nonneg y u) (clamp01_nonneg _)

lemma bg_G_le_W (ρ : K → K) (j : Fin N) (y : K → Fin N → ℝ) : bg_G ρ j y ≤ pb_W y := by
  unfold bg_G pb_W
  refine sum_le_sum fun u _ => ?_
  have := pb_P_nonneg y u
  have := clamp01_le_one (y (ρ u) j)
  nlinarith

variable {ι : Type*} [Fintype ι]

/-- The generalised block summand. -/
def bg_F (ρ : ι → K → K) (j : ι → Fin N) (c : ι → ℝ) (y : K → Fin N → ℝ) : ι → ℝ :=
  fun p => (bg_G (ρ p) (j p) y - c p) / sigN N

lemma bg_measurable_F (ρ : ι → K → K) (j : ι → Fin N) (c : ι → ℝ) :
    Measurable (bg_F ρ j c) :=
  Measurable.of_eval fun p => ((bg_measurable_G (ρ p) (j p)).sub_const _).div_const _

/-- The common law of the generalised block summands. -/
def bg_nu (ρ : ι → K → K) (j : ι → Fin N) (c : ι → ℝ) : Measure (ι → ℝ) :=
  (bg_blkM N K).map (bg_F ρ j c)

instance (ρ : ι → K → K) (j : ι → Fin N) (c : ι → ℝ) : IsProbabilityMeasure (bg_nu ρ j c) := by
  unfold bg_nu; exact (Measure.isProbabilityMeasure_map_iff (bg_measurable_F ρ j c).aemeasurable).2 inferInstance

lemma bg_integral_nu {ρ : ι → K → K} {j : ι → Fin N} {c : ι → ℝ} {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) :
    ∫ x, f x ∂bg_nu ρ j c = ∫ y, f (bg_F ρ j c y) ∂bg_blkM N K :=
  integral_map (bg_measurable_F ρ j c).aemeasurable hf.aestronglyMeasurable

/-! ### First moments -/

/-- The mean of the uncentred part. -/
def bg_mean (N : ℕ) (ρ : K → K) : ℝ := (1 / 2 : ℝ) ^ N * ∑ u, (if ρ u = u then 2 / 3 else 1 / 2)

lemma bg_mean_nonneg (ρ : K → K) : 0 ≤ bg_mean N ρ := by
  unfold bg_mean
  refine mul_nonneg (by positivity) (sum_nonneg fun u _ => ?_)
  split_ifs <;> norm_num

lemma bg_mean_le (ρ : K → K) : bg_mean N ρ ≤ Fintype.card K * (1 / 2 : ℝ) ^ N := by
  unfold bg_mean
  have h : ∑ u, (if ρ u = u then (2 / 3 : ℝ) else 1 / 2) ≤ ∑ _u : K, (1 : ℝ) :=
    sum_le_sum fun u _ => by split_ifs <;> norm_num
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right h (by positivity)

lemma bg_mono_Pcl (y : K → Fin N → ℝ) (u r : K) (j : Fin N) :
    pb_P y u * clamp01 (y r j) =
      pb_mono (fun t j' => (if t = u then 1 else 0) + (if t = r ∧ j' = j then 1 else 0)) y := by
  simp only [pb_mono, pow_add, prod_mul_distrib]
  rw [pb_prod_row_ind, pb_prod_single_ind]

/-- `E[P_u · clamp01 (y r j)] = 2^{-N} (2/3 if r = u, 1/2 otherwise)`. -/
lemma bg_integral_Pcl (u r : K) (j : Fin N) :
    ∫ y, pb_P y u * clamp01 (y r j) ∂bg_blkM N K =
      (1 / 2 : ℝ) ^ N * (if r = u then 2 / 3 else 1 / 2) := by
  simp_rw [bg_mono_Pcl]
  rw [bg_blkM, pb_integral_mono, ← Fintype.prod_prod_type']
  rw [bg_prod_ratio _ (fun x : K × Fin N => 1 / (((if x.1 = u then 1 else 0 : ℕ) : ℝ) + 1))
    {(r, j)} (fun x => by positivity) (fun x hx => by
      obtain ⟨t, j'⟩ := x
      have : ¬ (t = r ∧ j' = j) := fun h => hx (by simp [h.1, h.2])
      simp [this])]
  rw [Fintype.prod_prod_type' (f := fun t (_ : Fin N) =>
      1 / (((if t = u then 1 else 0 : ℕ) : ℝ) + 1)),
    bg_prod_base u (fun t => ((if t = u then 1 else 0 : ℕ) : ℝ)) (fun t ht => by simp [ht]),
    prod_singleton]
  by_cases h : r = u
  · subst h; norm_num
  · simp [h]; norm_num

lemma bg_integrable_of_bound {f : (K → Fin N → ℝ) → ℝ} (hf : Measurable f) (C : ℝ)
    (h : ∀ y, |f y| ≤ C) : Integrable f (bg_blkM N K) :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun y => by
    rw [Real.norm_eq_abs]; exact h y)

lemma bg_abs_Pcl_le (y : K → Fin N → ℝ) (u r : K) (j : Fin N) :
    |pb_P y u * clamp01 (y r j)| ≤ 1 := by
  rw [abs_of_nonneg (mul_nonneg (pb_P_nonneg y u) (clamp01_nonneg _))]
  have := pb_P_le_one y u
  have := clamp01_le_one (y r j)
  have := clamp01_nonneg (y r j)
  nlinarith [pb_P_nonneg y u]

lemma bg_integrable_Pcl (u r : K) (j : Fin N) :
    Integrable (fun y => pb_P y u * clamp01 (y r j)) (bg_blkM N K) :=
  bg_integrable_of_bound ((pb_measurable_P u).mul (pb_measurable_cl r j)) 1
    fun y => bg_abs_Pcl_le y u r j

/-- The exact mean of the uncentred part. -/
theorem bg_integral_G (ρ : K → K) (j : Fin N) :
    ∫ y, bg_G ρ j y ∂bg_blkM N K = bg_mean N ρ := by
  unfold bg_G
  rw [integral_finsetSum _ fun u _ => bg_integrable_Pcl u (ρ u) j, bg_mean, mul_sum]
  exact sum_congr rfl fun u _ => bg_integral_Pcl u (ρ u) j

lemma bg_abs_G_le (ρ : K → K) (j : Fin N) (y : K → Fin N → ℝ) :
    |bg_G ρ j y| ≤ Fintype.card K := by
  rw [abs_of_nonneg (bg_G_nonneg ρ j y)]
  exact (bg_G_le_W ρ j y).trans (pb_W_le y)

lemma bg_integrable_G (ρ : K → K) (j : Fin N) :
    Integrable (bg_G ρ j) (bg_blkM N K) :=
  bg_integrable_of_bound (bg_measurable_G ρ j) _ (bg_abs_G_le ρ j)

/-- **Zero means** of the generalised block law, when each `c p` is the exact mean. -/
theorem bg_nu_mean {ρ : ι → K → K} {j : ι → Fin N} {c : ι → ℝ}
    (hc : ∀ p, c p = bg_mean N (ρ p)) (p : ι) : ∫ x, x p ∂bg_nu ρ j c = 0 := by
  rw [bg_integral_nu (measurable_pi_apply p)]
  simp only [bg_F]
  rw [integral_div, integral_sub (bg_integrable_G _ _) (integrable_const _), bg_integral_G,
    integral_const, hc p]
  simp

/-! ### Second moments -/

/-- The diagonal correlation factor of the entries `(r, j)` and `(r', j')` against row `u`. -/
def bg_corr0 (u r r' : K) (j j' : Fin N) : ℝ :=
  if r = r' ∧ j = j' then (if r = u then 3 / 5 else 1 / 3)
  else (if r = u then 3 / 4 else 1 / 2) * (if r' = u then 3 / 4 else 1 / 2)

/-- The correlation factor of two coordinates at row `u`. -/
def bg_corr (ρp ρq : K → K) (jp jq : Fin N) (u : K) : ℝ := bg_corr0 u (ρp u) (ρq u) jp jq

lemma bg_mono_P2clcl (y : K → Fin N → ℝ) (u r r' : K) (j j' : Fin N) :
    pb_P y u * pb_P y u * clamp01 (y r j) * clamp01 (y r' j') =
      pb_mono (fun t j'' => (if t = u then 1 else 0) + (if t = u then 1 else 0) +
        (if t = r ∧ j'' = j then 1 else 0) + (if t = r' ∧ j'' = j' then 1 else 0)) y := by
  simp only [pb_mono, pow_add, prod_mul_distrib]
  rw [pb_prod_row_ind, pb_prod_single_ind, pb_prod_single_ind]

/-- `E[P_u^2 · clamp01 (y r j) · clamp01 (y r' j')] = 3^{-N} · bg_corr0`. -/
theorem bg_integral_diag (u r r' : K) (j j' : Fin N) :
    ∫ y, pb_P y u * pb_P y u * clamp01 (y r j) * clamp01 (y r' j') ∂bg_blkM N K =
      (1 / 3 : ℝ) ^ N * bg_corr0 u r r' j j' := by
  simp_rw [bg_mono_P2clcl]
  rw [bg_blkM, pb_integral_mono, ← Fintype.prod_prod_type']
  rw [bg_prod_ratio _ (fun x : K × Fin N =>
      1 / ((((if x.1 = u then 1 else 0) + (if x.1 = u then 1 else 0) : ℕ) : ℝ) + 1))
    {(r, j), (r', j')} (fun x => by positivity) (fun x hx => by
      obtain ⟨t, j''⟩ := x
      have h1 : ¬ (t = r ∧ j'' = j) := fun h => hx (by simp [h.1, h.2])
      have h2 : ¬ (t = r' ∧ j'' = j') := fun h => hx (by simp [h.1, h.2])
      simp only [h1, h2, ite_false, add_zero])]
  rw [Fintype.prod_prod_type' (f := fun t (_ : Fin N) =>
      1 / ((((if t = u then 1 else 0) + (if t = u then 1 else 0) : ℕ) : ℝ) + 1)),
    bg_prod_base u (fun t => (((if t = u then 1 else 0) + (if t = u then 1 else 0) : ℕ) : ℝ))
      (fun t ht => by simp [ht])]
  unfold bg_corr0
  by_cases hs : r = r' ∧ j = j'
  · obtain ⟨rfl, rfl⟩ := hs
    rw [Finset.insert_eq_of_mem (mem_singleton_self _), prod_singleton]
    by_cases h : r = u
    · subst h; norm_num
    · simp [h]; norm_num
  · have hne : (r, j) ≠ (r', j') := fun h => hs ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
    rw [prod_pair hne]
    have h1 : ¬ (r' = r ∧ j' = j) := fun h => hs ⟨h.1.symm, h.2.symm⟩
    simp only [hs, h1, ite_false, add_zero, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, and_self, ite_true]
    split_ifs <;> norm_num

/-- `E[P_u P_u'] = 4^{-N}` for distinct rows. -/
lemma bg_integral_PP {u u' : K} (h : u ≠ u') :
    ∫ y, pb_P y u * pb_P y u' ∂bg_blkM N K = (1 / 4 : ℝ) ^ N := by
  have := integral_pi_mul_of_ne (I := K) (rowM N) h measurable_rowPw measurable_rowPw
  simp only [pb_P, bg_blkM]
  rw [this]
  have h1 := integral_rowP_pow' (N := N) 1
  simp only [pow_one] at h1
  rw [h1, ← mul_pow]
  norm_num

lemma bg_measurable_T (u u' r r' : K) (j j' : Fin N) :
    Measurable fun y : K → Fin N → ℝ =>
      pb_P y u * clamp01 (y r j) * (pb_P y u' * clamp01 (y r' j')) :=
  ((pb_measurable_P u).mul (pb_measurable_cl r j)).mul
    ((pb_measurable_P u').mul (pb_measurable_cl r' j'))

lemma bg_integrable_T (u u' r r' : K) (j j' : Fin N) :
    Integrable (fun y : K → Fin N → ℝ =>
      pb_P y u * clamp01 (y r j) * (pb_P y u' * clamp01 (y r' j'))) (bg_blkM N K) :=
  bg_integrable_of_bound (bg_measurable_T u u' r r' j j') 1 fun y => by
    rw [abs_mul]
    have h1 := bg_abs_Pcl_le y u r j
    have h2 := bg_abs_Pcl_le y u' r' j'
    nlinarith [abs_nonneg (pb_P y u * clamp01 (y r j)), abs_nonneg (pb_P y u' * clamp01 (y r' j'))]

lemma bg_integral_T_nonneg (u u' r r' : K) (j j' : Fin N) :
    0 ≤ ∫ y, pb_P y u * clamp01 (y r j) * (pb_P y u' * clamp01 (y r' j')) ∂bg_blkM N K :=
  integral_nonneg fun y => mul_nonneg (mul_nonneg (pb_P_nonneg y u) (clamp01_nonneg _))
    (mul_nonneg (pb_P_nonneg y u') (clamp01_nonneg _))

lemma bg_integral_T_le {u u' : K} (h : u ≠ u') (r r' : K) (j j' : Fin N) :
    ∫ y, pb_P y u * clamp01 (y r j) * (pb_P y u' * clamp01 (y r' j')) ∂bg_blkM N K ≤
      (1 / 4 : ℝ) ^ N := by
  rw [← bg_integral_PP (N := N) h]
  refine integral_mono (bg_integrable_T u u' r r' j j')
    (bg_integrable_of_bound ((pb_measurable_P u).mul (pb_measurable_P u')) 1 fun y => by
      rw [abs_of_nonneg (mul_nonneg (pb_P_nonneg y u) (pb_P_nonneg y u'))]
      have := pb_P_le_one y u; have := pb_P_le_one y u'
      nlinarith [pb_P_nonneg y u, pb_P_nonneg y u']) fun y => ?_
  have a1 := pb_P_nonneg y u; have a2 := pb_P_nonneg y u'
  have b1 := clamp01_le_one (y r j); have b2 := clamp01_le_one (y r' j')
  have c1 := clamp01_nonneg (y r j); have c2 := clamp01_nonneg (y r' j')
  have : clamp01 (y r j) * clamp01 (y r' j') ≤ 1 := by nlinarith
  calc pb_P y u * clamp01 (y r j) * (pb_P y u' * clamp01 (y r' j'))
      = (pb_P y u * pb_P y u') * (clamp01 (y r j) * clamp01 (y r' j')) := by ring
    _ ≤ (pb_P y u * pb_P y u') * 1 := by gcongr
    _ = pb_P y u * pb_P y u' := mul_one _

/-- **Second moments of the uncentred parts**: the diagonal rows give `3^{-N} ∑_u bg_corr`, the
off-diagonal pairs of rows at most `|K|^2 4^{-N}`. -/
theorem bg_integral_GG (ρp ρq : K → K) (jp jq : Fin N) :
    (1 / 3 : ℝ) ^ N * ∑ u, bg_corr ρp ρq jp jq u ≤
        ∫ y, bg_G ρp jp y * bg_G ρq jq y ∂bg_blkM N K ∧
      ∫ y, bg_G ρp jp y * bg_G ρq jq y ∂bg_blkM N K ≤
        (1 / 3 : ℝ) ^ N * ∑ u, bg_corr ρp ρq jp jq u +
          (Fintype.card K : ℝ) ^ 2 * (1 / 4 : ℝ) ^ N := by
  set T : K → K → ℝ := fun u u' => ∫ y, pb_P y u * clamp01 (y (ρp u) jp) *
    (pb_P y u' * clamp01 (y (ρq u') jq)) ∂bg_blkM N K
  have hGG : ∫ y, bg_G ρp jp y * bg_G ρq jq y ∂bg_blkM N K = ∑ u, ∑ u', T u u' := by
    simp only [bg_G, sum_mul_sum]
    rw [integral_finsetSum _ fun u _ => integrable_finsetSum _ fun u' _ =>
      bg_integrable_T u u' _ _ jp jq]
    exact sum_congr rfl fun u _ => integral_finsetSum _ fun u' _ => bg_integrable_T u u' _ _ jp jq
  have hdiag : ∀ u, T u u = (1 / 3 : ℝ) ^ N * bg_corr ρp ρq jp jq u := by
    intro u
    simp only [T, bg_corr]
    rw [← bg_integral_diag]
    congr 1; funext y; ring
  have hsplit : ∀ u, ∑ u', T u u' = T u u + ∑ u' ∈ univ.erase u, T u u' := fun u =>
    (add_sum_erase _ _ (mem_univ u)).symm
  have hoff : ∀ u, 0 ≤ ∑ u' ∈ univ.erase u, T u u' ∧
      ∑ u' ∈ univ.erase u, T u u' ≤ Fintype.card K * (1 / 4 : ℝ) ^ N := by
    intro u
    refine ⟨sum_nonneg fun u' _ => bg_integral_T_nonneg _ _ _ _ _ _, ?_⟩
    calc ∑ u' ∈ univ.erase u, T u u' ≤ ∑ _u' ∈ univ.erase u, (1 / 4 : ℝ) ^ N :=
          sum_le_sum fun u' hu' => bg_integral_T_le (Ne.symm (ne_of_mem_erase hu')) _ _ _ _
      _ ≤ ∑ _u' : K, (1 / 4 : ℝ) ^ N :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ => by positivity
      _ = Fintype.card K * (1 / 4 : ℝ) ^ N := by simp
  rw [hGG, mul_sum]
  simp_rw [hsplit, sum_add_distrib, hdiag]
  constructor
  · linarith [sum_nonneg fun u (_ : u ∈ univ) => (hoff u).1]
  · have : ∑ u, ∑ u' ∈ univ.erase u, T u u' ≤ ∑ _u : K, Fintype.card K * (1 / 4 : ℝ) ^ N :=
      sum_le_sum fun u _ => (hoff u).2
    simp only [sum_const, card_univ, nsmul_eq_mul] at this
    nlinarith

lemma bg_sigN_sq (N : ℕ) : sigN N ^ 2 = (2 / 3 : ℝ) ^ N := Real.sq_sqrt (by positivity)

/-- **Second moments** of the generalised block law: if `B |K| = 2^N` and each `c p` is the exact
mean, then `|B ∫ x p x q dν - |K|⁻¹ ∑_u bg_corr| ≤ |K| (3/4)^N`. -/
theorem bg_nu_second {ρ : ι → K → K} {j : ι → Fin N} {c : ι → ℝ}
    (hc : ∀ p, c p = bg_mean N (ρ p)) {B : ℕ} (hB : (B : ℝ) * Fintype.card K = 2 ^ N)
    (p q : ι) :
    |(B : ℝ) * ∫ x, x p * x q ∂bg_nu ρ j c -
        (Fintype.card K : ℝ)⁻¹ * ∑ u, bg_corr (ρ p) (ρ q) (j p) (j q) u| ≤
      Fintype.card K * (3 / 4 : ℝ) ^ N := by
  rw [bg_integral_nu (f := fun x => x p * x q) ((measurable_pi_apply p).mul (measurable_pi_apply q))]
  have hK : (0 : ℝ) < Fintype.card K := by
    rcases Nat.eq_zero_or_pos (Fintype.card K) with h | h
    · rw [h, Nat.cast_zero, mul_zero] at hB; exact absurd hB.symm (by positivity)
    · exact_mod_cast h
  set κ := (Fintype.card K : ℝ)
  have hs := sigN_pos N
  have hs2 := bg_sigN_sq N
  have hIp := bg_integrable_G (ρ p) (j p) (N := N)
  have hIq := bg_integrable_G (ρ q) (j q) (N := N)
  have hIGG : Integrable (fun y => bg_G (ρ p) (j p) y * bg_G (ρ q) (j q) y) (bg_blkM N K) :=
    bg_integrable_of_bound ((bg_measurable_G _ _).mul (bg_measurable_G _ _)) (κ * κ) fun y => by
      rw [abs_mul]
      exact mul_le_mul (bg_abs_G_le _ _ y) (bg_abs_G_le _ _ y) (abs_nonneg _) hK.le
  have hexp : ∫ y, bg_F ρ j c y p * bg_F ρ j c y q ∂bg_blkM N K =
      ((∫ y, bg_G (ρ p) (j p) y * bg_G (ρ q) (j q) y ∂bg_blkM N K) - c p * c q) / sigN N ^ 2 := by
    have e : ∀ y, bg_F ρ j c y p * bg_F ρ j c y q =
        (bg_G (ρ p) (j p) y * bg_G (ρ q) (j q) y - c q * bg_G (ρ p) (j p) y -
          c p * bg_G (ρ q) (j q) y + c p * c q) / sigN N ^ 2 := by
      intro y; simp only [bg_F]; field_simp; ring
    simp_rw [e]
    have h1 : Integrable (fun y => bg_G (ρ p) (j p) y * bg_G (ρ q) (j q) y -
        c q * bg_G (ρ p) (j p) y) (bg_blkM N K) := hIGG.sub (hIp.const_mul _)
    have h2 : Integrable (fun y => bg_G (ρ p) (j p) y * bg_G (ρ q) (j q) y -
        c q * bg_G (ρ p) (j p) y - c p * bg_G (ρ q) (j q) y) (bg_blkM N K) :=
      h1.sub (hIq.const_mul _)
    rw [integral_div, integral_add h2 (integrable_const _), integral_sub h1 (hIq.const_mul _),
      integral_sub hIGG (hIp.const_mul _), integral_const_mul, integral_const_mul,
      bg_integral_G, bg_integral_G, integral_const, ← hc p, ← hc q]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    congr 1; ring
  rw [hexp]
  obtain ⟨hlo, hhi⟩ := bg_integral_GG (N := N) (ρ p) (ρ q) (j p) (j q)
  set I := ∫ y, bg_G (ρ p) (j p) y * bg_G (ρ q) (j q) y ∂bg_blkM N K
  set Sc := ∑ u, bg_corr (ρ p) (ρ q) (j p) (j q) u
  have hcp0 : 0 ≤ c p := hc p ▸ bg_mean_nonneg _
  have hcq0 : 0 ≤ c q := hc q ▸ bg_mean_nonneg _
  have hcp1 : c p ≤ κ * (1 / 2 : ℝ) ^ N := hc p ▸ bg_mean_le _
  have hcq1 : c q ≤ κ * (1 / 2 : ℝ) ^ N := hc q ▸ bg_mean_le _
  have hcc : c p * c q ≤ κ ^ 2 * (1 / 4 : ℝ) ^ N := by
    calc c p * c q ≤ (κ * (1 / 2 : ℝ) ^ N) * (κ * (1 / 2 : ℝ) ^ N) :=
          mul_le_mul hcp1 hcq1 hcq0 (by positivity)
      _ = κ ^ 2 * (1 / 4 : ℝ) ^ N := by
          rw [show (1 / 4 : ℝ) = 1 / 2 * (1 / 2) by norm_num, mul_pow]; ring
  have hB' : (B : ℝ) = 2 ^ N / κ := by rw [eq_div_iff hK.ne']; exact hB
  have h3 : (B : ℝ) * (1 / 3 : ℝ) ^ N / sigN N ^ 2 = κ⁻¹ := by
    rw [hB', hs2]
    have e : (2 : ℝ) ^ N * (1 / 3) ^ N = (2 / 3) ^ N := by rw [← mul_pow]; norm_num
    calc (2 : ℝ) ^ N / κ * (1 / 3) ^ N / (2 / 3) ^ N = (2 ^ N * (1 / 3) ^ N) / (2 / 3) ^ N / κ := by
          ring
      _ = κ⁻¹ := by rw [e, div_self (by positivity), one_div]
  have h4 : (B : ℝ) * (κ ^ 2 * (1 / 4 : ℝ) ^ N) / sigN N ^ 2 = κ * (3 / 4 : ℝ) ^ N := by
    rw [hB', hs2]
    have e : (2 : ℝ) ^ N * (1 / 4) ^ N = (3 / 4) ^ N * (2 / 3) ^ N := by
      rw [← mul_pow, ← mul_pow]; norm_num
    have hκ : κ ≠ 0 := hK.ne'
    calc (2 : ℝ) ^ N / κ * (κ ^ 2 * (1 / 4) ^ N) / (2 / 3) ^ N
        = κ * ((2 : ℝ) ^ N * (1 / 4) ^ N / (2 / 3) ^ N) := by field_simp
      _ = κ * (3 / 4 : ℝ) ^ N := by rw [e, mul_div_assoc, div_self (by positivity), mul_one]
  have key : (B : ℝ) * ((I - c p * c q) / sigN N ^ 2) - κ⁻¹ * Sc =
      (B : ℝ) * (I - (1 / 3 : ℝ) ^ N * Sc - c p * c q) / sigN N ^ 2 := by
    rw [← h3]; ring
  have hBn : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hcc0 : 0 ≤ c p * c q := mul_nonneg hcp0 hcq0
  rw [key, abs_le, ← h4]
  constructor
  · rw [neg_le, ← neg_div, div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  · rw [div_le_div_iff_of_pos_right (by positivity)]
    nlinarith

lemma bg_corr0_nonneg (u r r' : K) (j j' : Fin N) : 0 ≤ bg_corr0 u r r' j j' := by
  unfold bg_corr0; split_ifs <;> norm_num

lemma bg_corr0_le_one (u r r' : K) (j j' : Fin N) : bg_corr0 u r r' j j' ≤ 1 := by
  unfold bg_corr0; split_ifs <;> norm_num

/-- The second moments with `B - 1` summands. -/
theorem bg_nu_second_pred {ρ : ι → K → K} {j : ι → Fin N} {c : ι → ℝ}
    (hc : ∀ p, c p = bg_mean N (ρ p)) {B : ℕ} (hB : (B : ℝ) * Fintype.card K = 2 ^ N)
    (p q : ι) :
    |((B - 1 : ℕ) : ℝ) * ∫ x, x p * x q ∂bg_nu ρ j c -
        (Fintype.card K : ℝ)⁻¹ * ∑ u, bg_corr (ρ p) (ρ q) (j p) (j q) u| ≤
      3 * (Fintype.card K : ℝ) ^ 2 * (3 / 4 : ℝ) ^ N := by
  have h := bg_nu_second (j := j) hc hB p q
  set κ := (Fintype.card K : ℝ)
  have hK : 0 < κ := by
    rcases Nat.eq_zero_or_pos (Fintype.card K) with h0 | h0
    · simp only [κ, h0, Nat.cast_zero, mul_zero] at hB; exact absurd hB.symm (by positivity)
    · simp only [κ]; exact_mod_cast h0
  have hκ1 : 1 ≤ κ := by
    have h0 : 0 < Fintype.card K := by
      have := hK; simp only [κ] at this; exact_mod_cast this
    simp only [κ]; exact_mod_cast h0
  have hB0 : 1 ≤ B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · rw [h0, Nat.cast_zero, zero_mul] at hB; exact absurd hB.symm (by positivity)
    · exact h0
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB0
  set I := ∫ x, x p * x q ∂bg_nu ρ j c
  set G := κ⁻¹ * ∑ u, bg_corr (ρ p) (ρ q) (j p) (j q) u
  have hG0 : 0 ≤ G := mul_nonneg (inv_nonneg.2 hK.le) (sum_nonneg fun u _ => bg_corr0_nonneg _ _ _ _ _)
  have hG1 : G ≤ 1 := by
    have : ∑ u, bg_corr (ρ p) (ρ q) (j p) (j q) u ≤ κ := by
      calc ∑ u, bg_corr (ρ p) (ρ q) (j p) (j q) u ≤ ∑ _u : K, (1 : ℝ) :=
            sum_le_sum fun u _ => bg_corr0_le_one _ _ _ _ _
        _ = κ := by simp [κ]
    calc G ≤ κ⁻¹ * κ := mul_le_mul_of_nonneg_left this (inv_nonneg.2 hK.le)
      _ = 1 := inv_mul_cancel₀ hK.ne'
  have h34 : (3 / 4 : ℝ) ^ N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h12 : (1 / 2 : ℝ) ^ N ≤ (3 / 4) ^ N := pow_le_pow_left₀ (by norm_num) (by norm_num) N
  have hBI : |(B : ℝ) * I| ≤ 2 * κ := by
    rw [abs_le] at h ⊢; constructor <;> nlinarith
  have hI : |I| ≤ 2 * κ ^ 2 * (3 / 4 : ℝ) ^ N := by
    have h1 : |I| ≤ 2 * κ / B := by
      rw [le_div_iff₀ hBpos]
      calc |I| * B = |(B : ℝ) * I| := by rw [abs_mul, abs_of_pos hBpos]; ring
        _ ≤ 2 * κ := hBI
    have hBr : (B : ℝ) = 2 ^ N / κ := by rw [eq_div_iff hK.ne']; exact hB
    have h2 : 2 * κ / B = 2 * κ ^ 2 * (1 / 2 : ℝ) ^ N := by
      rw [hBr, one_div_pow]; field_simp
    rw [h2] at h1
    exact h1.trans (by gcongr)
  rw [Nat.cast_sub hB0, Nat.cast_one]
  calc |((B : ℝ) - 1) * I - G| = |((B : ℝ) * I - G) - I| := by ring_nf
    _ ≤ |(B : ℝ) * I - G| + |I| := abs_sub _ _
    _ ≤ κ * (3 / 4 : ℝ) ^ N + 2 * κ ^ 2 * (3 / 4 : ℝ) ^ N := add_le_add h hI
    _ ≤ 3 * κ ^ 2 * (3 / 4 : ℝ) ^ N := by
        nlinarith [mul_le_mul_of_nonneg_right (show κ ≤ κ ^ 2 by nlinarith)
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) N)]

/-! ### Third moments -/

lemma bg_measurable_abs3 : Measurable fun x : ι → ℝ => (∑ p, |x p|) ^ 3 :=
  (Finset.measurable_sum _ fun p _ => (measurable_pi_apply p).abs).pow_const 3

lemma bg_abs_F_le {ρ : ι → K → K} {j : ι → Fin N} {c : ι → ℝ}
    (hc : ∀ p, c p = bg_mean N (ρ p)) (y : K → Fin N → ℝ) (p : ι) :
    |bg_F ρ j c y p| ≤ (pb_W y + Fintype.card K * (1 / 2 : ℝ) ^ N) / sigN N := by
  have hs := sigN_pos N
  rw [bg_F, abs_div, abs_of_pos hs, div_le_div_iff_of_pos_right hs]
  have h0 := bg_G_nonneg (ρ p) (j p) y
  have h1 := bg_G_le_W (ρ p) (j p) y
  have h2 : 0 ≤ c p := hc p ▸ bg_mean_nonneg _
  have h3 : c p ≤ Fintype.card K * (1 / 2 : ℝ) ^ N := hc p ▸ bg_mean_le _
  rw [abs_le]; constructor <;> linarith

lemma bg_cube_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (a - b))]

/-- Integrability of the third absolute moment of the generalised block law. -/
theorem bg_nu_integrable3 {ρ : ι → K → K} {j : ι → Fin N} {c : ι → ℝ}
    (hc : ∀ p, c p = bg_mean N (ρ p)) :
    Integrable (fun x => (∑ p, |x p|) ^ 3) (bg_nu ρ j c) := by
  rw [bg_nu, integrable_map_measure bg_measurable_abs3.aestronglyMeasurable
    (bg_measurable_F ρ j c).aemeasurable]
  have hs := sigN_pos N
  refine Integrable.of_bound (bg_measurable_abs3.comp (bg_measurable_F ρ j c)).aestronglyMeasurable
    ((Fintype.card ι * ((Fintype.card K + Fintype.card K * (1 / 2 : ℝ) ^ N) / sigN N)) ^ 3)
    (ae_of_all _ fun y => ?_)
  have h0 : 0 ≤ ∑ p, |bg_F ρ j c y p| := sum_nonneg fun p _ => abs_nonneg _
  simp only [Function.comp, Real.norm_eq_abs]
  rw [abs_of_nonneg (pow_nonneg h0 3)]
  refine pow_le_pow_left₀ h0 ?_ 3
  calc ∑ p, |bg_F ρ j c y p| ≤ ∑ _p : ι, (Fintype.card K + Fintype.card K * (1 / 2 : ℝ) ^ N) /
        sigN N := sum_le_sum fun p _ => (bg_abs_F_le hc y p).trans (by
          gcongr; exact pb_W_le y)
    _ = _ := by simp

/-- **Third moments** of the generalised block law: `B ∫ (∑ |x p|)^3 dν ≤ 8 d^3 |K|^2 (23/25)^N`. -/
theorem bg_nu_third {ρ : ι → K → K} {j : ι → Fin N} {c : ι → ℝ}
    (hc : ∀ p, c p = bg_mean N (ρ p)) {B : ℕ} (hB : (B : ℝ) * Fintype.card K = 2 ^ N) :
    (B : ℝ) * ∫ x, (∑ p, |x p|) ^ 3 ∂bg_nu ρ j c ≤
      8 * (Fintype.card ι : ℝ) ^ 3 * (Fintype.card K : ℝ) ^ 2 * (23 / 25 : ℝ) ^ N := by
  rw [bg_integral_nu bg_measurable_abs3]
  have hs := sigN_pos N
  set κ := (Fintype.card K : ℝ)
  set d := (Fintype.card ι : ℝ)
  set a := κ * (1 / 2 : ℝ) ^ N
  have ha : 0 ≤ a := by positivity
  have hW3 := pb_integral_W3 (N := N) (K := K)
  have hIW : Integrable (fun y : K → Fin N → ℝ => pb_W y ^ 3) (bg_blkM N K) :=
    bg_integrable_of_bound (pb_measurable_W.pow_const 3) (κ ^ 3) fun y => by
      rw [abs_of_nonneg (pow_nonneg (pb_W_nonneg y) 3)]
      exact pow_le_pow_left₀ (pb_W_nonneg y) (pb_W_le y) 3
  have hpt : ∀ y, (∑ p, |bg_F ρ j c y p|) ^ 3 ≤
      4 * d ^ 3 / sigN N ^ 3 * (pb_W y ^ 3 + a ^ 3) := by
    intro y
    have h0 : 0 ≤ ∑ p, |bg_F ρ j c y p| := sum_nonneg fun p _ => abs_nonneg _
    have h1 : ∑ p, |bg_F ρ j c y p| ≤ d * ((pb_W y + a) / sigN N) := by
      calc ∑ p, |bg_F ρ j c y p| ≤ ∑ _p : ι, (pb_W y + a) / sigN N :=
            sum_le_sum fun p _ => bg_abs_F_le hc y p
        _ = _ := by simp [d]
    calc (∑ p, |bg_F ρ j c y p|) ^ 3 ≤ (d * ((pb_W y + a) / sigN N)) ^ 3 :=
          pow_le_pow_left₀ h0 h1 3
      _ = d ^ 3 / sigN N ^ 3 * (pb_W y + a) ^ 3 := by field_simp
      _ ≤ d ^ 3 / sigN N ^ 3 * (4 * (pb_W y ^ 3 + a ^ 3)) := by
          gcongr; exact bg_cube_le _ _ (pb_W_nonneg y) ha
      _ = _ := by ring
  have hbd : ∫ y, (∑ p, |bg_F ρ j c y p|) ^ 3 ∂bg_blkM N K ≤
      4 * d ^ 3 / sigN N ^ 3 * (κ ^ 3 * (1 / 4 : ℝ) ^ N + a ^ 3) := by
    calc ∫ y, (∑ p, |bg_F ρ j c y p|) ^ 3 ∂bg_blkM N K
        ≤ ∫ y, 4 * d ^ 3 / sigN N ^ 3 * (pb_W y ^ 3 + a ^ 3) ∂bg_blkM N K :=
          integral_mono_of_nonneg (ae_of_all _ fun y =>
            pow_nonneg (sum_nonneg fun p _ => abs_nonneg _) 3)
            ((hIW.add (integrable_const _)).const_mul _) (ae_of_all _ hpt)
      _ = 4 * d ^ 3 / sigN N ^ 3 * (∫ y, pb_W y ^ 3 ∂bg_blkM N K + a ^ 3) := by
          rw [integral_const_mul, integral_add hIW (integrable_const _), integral_const]
          simp
      _ ≤ _ := by gcongr; exact hW3
  have ha3 : a ^ 3 ≤ κ ^ 3 * (1 / 4 : ℝ) ^ N := by
    have e : a ^ 3 = κ ^ 3 * ((1 / 2 : ℝ) ^ N) ^ 3 := by simp only [a]; ring
    rw [e]
    gcongr
    rw [← pow_mul, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, ← pow_mul]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hK : 0 < κ := by
    rcases Nat.eq_zero_or_pos (Fintype.card K) with h | h
    · simp only [κ, h, Nat.cast_zero, mul_zero] at hB; exact absurd hB.symm (by positivity)
    · simp only [κ]; exact_mod_cast h
  have hh := pb_half_div_sig3 N
  have hBn : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  calc (B : ℝ) * ∫ y, (∑ p, |bg_F ρ j c y p|) ^ 3 ∂bg_blkM N K
      ≤ (B : ℝ) * (4 * d ^ 3 / sigN N ^ 3 * (κ ^ 3 * (1 / 4 : ℝ) ^ N + κ ^ 3 * (1 / 4 : ℝ) ^ N)) := by
        gcongr; exact hbd.trans (by gcongr)
    _ = 8 * d ^ 3 * κ ^ 2 * ((1 / 2 : ℝ) ^ N / sigN N ^ 3) := by
        have e : (2 : ℝ) ^ N * (1 / 4) ^ N = (1 / 2) ^ N := by rw [← mul_pow]; norm_num
        have hB2 : (B : ℝ) = 2 ^ N / κ := by rw [eq_div_iff hK.ne']; exact hB
        rw [hB2, ← e]
        field_simp
        ring
    _ ≤ 8 * d ^ 3 * κ ^ 2 * (23 / 25 : ℝ) ^ N := by gcongr

end Generic

/-! ### Summands along a parametrisation of the rows -/

section Param

variable {Γ K ι : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype K] [DecidableEq K] [Fintype ι]

/-- The summand of the superblock `γ` along the parametrisation `g`. -/
def bg_X (g : Γ × K ≃ State N) (ρ : ι → K → K) (j : ι → Fin N) (c : ι → ℝ) (γ : Γ)
    (w : Param N) : ι → ℝ :=
  bg_F ρ j c fun u => w (g (γ, u))

lemma bg_measurable_X (g : Γ × K ≃ State N) (ρ : ι → K → K) (j : ι → Fin N) (c : ι → ℝ)
    (γ : Γ) : Measurable (bg_X g ρ j c γ) :=
  (bg_measurable_F ρ j c).comp (Measurable.of_eval fun _ => measurable_pi_apply _)

/-- **Regrouping**: if merging the pattern `t` on `S` moves row `u` of every superblock to row
`ρ p u` of the same superblock, the cause numerator of `S` at `t` and unit `j p` is the sum of the
uncentred parts of coordinate `p`. -/
theorem bg_Num_regroup (g : Γ × K ≃ State N) (S : Finset (Fin N)) (t : State N) (ρ0 : K → K)
    (hm : ∀ γ u, merge S t (g (γ, u)) = g (γ, ρ0 u)) (w : Param N) (i : Fin N) :
    Num w S S t i = ∑ γ, bg_G ρ0 i fun u => w (g (γ, u)) := by
  rw [Num, ← g.sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun γ _ => sum_congr rfl fun u _ => ?_
  rw [pb_meanW_self, hm, mul_comm]
  rfl

/-- **Block decomposition** of one coordinate of the centred field. -/
theorem bg_sum_X (g : Γ × K ≃ State N) (ρ : ι → K → K) (j : ι → Fin N) (c : ι → ℝ)
    (S : Finset (Fin N)) (t : State N) (p : ι)
    (hm : ∀ γ u, merge S t (g (γ, u)) = g (γ, ρ p u)) (w : Param N) :
    (∑ γ, bg_X g ρ j c γ w) p = (Num w S S t (j p) - Fintype.card Γ * c p) / sigN N := by
  rw [Finset.sum_apply, bg_Num_regroup g S t (ρ p) hm w (j p)]
  simp only [bg_X, bg_F]
  rw [← sum_div, sum_sub_distrib]
  simp

/-- **Law of the summands**: under `cubeM N` the summands are iid with law `bg_nu ρ j c`. -/
theorem bg_map_X (g : Γ × K ≃ State N) (ρ : ι → K → K) (j : ι → Fin N) (c : ι → ℝ) :
    (cubeM N).map (fun w (γ : Γ) => bg_X g ρ j c γ w) = Measure.pi fun _ : Γ => bg_nu ρ j c :=
  pb_map_blocks g g.injective (bg_F ρ j c) (bg_measurable_F ρ j c)

/-- Enumeration of the superblocks. -/
def bg_e (Γ : Type*) [Fintype Γ] : Fin (Fintype.card Γ) ≃ Γ := (Fintype.equivFin _).symm

/-- The family of summands, indexed by `Fin (card Γ)`. -/
def bg_Xs (g : Γ × K ≃ State N) (ρ : ι → K → K) (j : ι → Fin N) (c : ι → ℝ) (w : Param N) :
    Fin (Fintype.card Γ) → ι → ℝ :=
  fun k => bg_X g ρ j c (bg_e Γ k) w

lemma bg_measurable_Xs (g : Γ × K ≃ State N) (ρ : ι → K → K) (j : ι → Fin N) (c : ι → ℝ) :
    Measurable (bg_Xs g ρ j c) :=
  Measurable.of_eval fun _ => bg_measurable_X g ρ j c _

lemma bg_sum_Xs (g : Γ × K ≃ State N) (ρ : ι → K → K) (j : ι → Fin N) (c : ι → ℝ)
    (w : Param N) : ∑ k, bg_Xs g ρ j c w k = ∑ γ, bg_X g ρ j c γ w :=
  (bg_e Γ).sum_comp fun γ => bg_X g ρ j c γ w

/-- **Law of the summands**, enumerated form. -/
theorem bg_map_Xs (g : Γ × K ≃ State N) (ρ : ι → K → K) (j : ι → Fin N) (c : ι → ℝ) :
    (cubeM N).map (bg_Xs g ρ j c) =
      Measure.pi fun _ : Fin (Fintype.card Γ) => bg_nu ρ j c := by
  have hc : bg_Xs g ρ j c = (fun (x : Γ → ι → ℝ) k => x (bg_e Γ k)) ∘
      fun w (γ : Γ) => bg_X g ρ j c γ w := rfl
  rw [hc, ← Measure.map_map (Measurable.of_eval fun k => measurable_pi_apply _)
    (Measurable.of_eval fun γ => bg_measurable_X g ρ j c γ), bg_map_X g ρ j c]
  exact map_comp_inj _ (bg_e Γ).injective _

/-! ### Removing the superblock of a state -/

/-- Enumeration of the superblocks other than `γs`. -/
def bg_er (γs : Γ) : Fin (Fintype.card Γ - 1) ≃ {γ : Γ // γ ≠ γs} :=
  (Fintype.equivFinOfCardEq (pb_card_ne γs)).symm

/-- The summands of the superblocks other than the superblock of `s`. -/
def bg_Xr (g : Γ × K ≃ State N) (ρ : ι → K → K) (j : ι → Fin N) (c : ι → ℝ) (s : State N)
    (w : Param N) : Fin (Fintype.card Γ - 1) → ι → ℝ :=
  fun k => bg_X g ρ j c (bg_er (g.symm s).1 k).1 w

lemma bg_measurable_Xr (g : Γ × K ≃ State N) (ρ : ι → K → K) (j : ι → Fin N) (c : ι → ℝ)
    (s : State N) : Measurable (bg_Xr g ρ j c s) :=
  Measurable.of_eval fun _ => bg_measurable_X g ρ j c _

/-- **Law of the remaining summands**: iid with law `bg_nu ρ j c`. -/
theorem bg_map_Xr (g : Γ × K ≃ State N) (ρ : ι → K → K) (j : ι → Fin N) (c : ι → ℝ)
    (s : State N) :
    (cubeM N).map (bg_Xr g ρ j c s) =
      Measure.pi fun _ : Fin (Fintype.card Γ - 1) => bg_nu ρ j c := by
  have hc : bg_Xr g ρ j c s = (fun (x : Γ → ι → ℝ) k => x (bg_er (g.symm s).1 k).1) ∘
      fun w (γ : Γ) => bg_X g ρ j c γ w := rfl
  rw [hc, ← Measure.map_map (Measurable.of_eval fun k => measurable_pi_apply _)
    (Measurable.of_eval fun γ => bg_measurable_X g ρ j c γ), bg_map_X g ρ j c]
  exact map_comp_inj _ (Subtype.val_injective.comp (bg_er (g.symm s).1).injective) _

/-- The sum of all summands is the sum of the remaining ones plus the summand of the superblock
of `s`. -/
theorem bg_sum_eq_rest (g : Γ × K ≃ State N) (ρ : ι → K → K) (j : ι → Fin N) (c : ι → ℝ)
    (s : State N) (w : Param N) :
    ∑ γ, bg_X g ρ j c γ w = ∑ k, bg_Xr g ρ j c s w k + bg_X g ρ j c (g.symm s).1 w := by
  rw [Fintype.sum_eq_add_sum_compl (g.symm s).1, add_comm]
  congr 1
  rw [Finset.sum_subtype ({(g.symm s).1}ᶜ : Finset Γ) (p := fun γ => γ ≠ (g.symm s).1)
    (by simp), ← (bg_er (g.symm s).1).sum_comp]
  rfl

/-- `2^{-N} ≤ τ_N`. -/
lemma bg_half_pow_le_tauN (N : ℕ) : (1 / 2 : ℝ) ^ N ≤ tauN N := by
  rw [tauN, one_div, inv_pow, ← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ N), ← Real.exp_neg,
    Real.exp_le_exp, Real.log_pow]
  have := Real.log_two_gt_d9
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-- On `g2` every summand is at most `|K| τ_N / σ_N` in every coordinate. -/
theorem bg_abs_X_le (g : Γ × K ≃ State N) {ρ : ι → K → K} {j : ι → Fin N} {c : ι → ℝ}
    (hc : ∀ p, c p = bg_mean N (ρ p)) {w : Param N} (h2 : ∀ i r, Qw w i r ≤ tauN N) (γ : Γ)
    (p : ι) : |bg_X g ρ j c γ w p| ≤ Fintype.card K * tauN N / sigN N := by
  have hs := sigN_pos N
  rw [bg_X, bg_F, abs_div, abs_of_pos hs, div_le_div_iff_of_pos_right hs]
  set y : K → Fin N → ℝ := fun u => w (g (γ, u))
  have hW : pb_W y ≤ Fintype.card K * tauN N := by
    calc pb_W y ≤ ∑ _u : K, tauN N := sum_le_sum fun u _ => pb_Pw_le_tau (j p) h2 _
      _ = _ := by simp
  have h0 := bg_G_nonneg (ρ p) (j p) y
  have h1 := bg_G_le_W (ρ p) (j p) y
  have h2' : 0 ≤ c p := hc p ▸ bg_mean_nonneg _
  have h3 : c p ≤ Fintype.card K * tauN N := by
    rw [hc p]
    exact (bg_mean_le _).trans (by gcongr; exact bg_half_pow_le_tauN N)
  exact abs_sub_le_of_nonneg_of_le h0 (h1.trans hW) h2' h3

/-- **Removing the superblock of `s`** changes every coordinate by at most `|K| τ_N / σ_N` on
`g2`. -/
theorem bg_abs_sub_rest_le (g : Γ × K ≃ State N) {ρ : ι → K → K} {j : ι → Fin N} {c : ι → ℝ}
    (hc : ∀ p, c p = bg_mean N (ρ p)) (s : State N) {w : Param N}
    (h2 : ∀ i r, Qw w i r ≤ tauN N) (p : ι) :
    |(∑ γ, bg_X g ρ j c γ w) p - (∑ k, bg_Xr g ρ j c s w k) p| ≤
      Fintype.card K * tauN N / sigN N := by
  rw [bg_sum_eq_rest g ρ j c s w, Pi.add_apply, add_sub_cancel_left]
  exact bg_abs_X_le g hc h2 _ p

/-- The rows of the superblock of `s`, as a random element. -/
def bg_blockRows (g : Γ × K ≃ State N) (s : State N) (w : Param N) : K → Fin N → ℝ :=
  fun u => w (g ((g.symm s).1, u))

lemma bg_measurable_blockRows (g : Γ × K ≃ State N) (s : State N) :
    Measurable (bg_blockRows g s) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- **Independence**: the remaining summands are independent of the rows of the superblock of
`s`. -/
theorem bg_indep_rest (g : Γ × K ≃ State N) (ρ : ι → K → K) (j : ι → Fin N) (c : ι → ℝ)
    (s : State N) : IndepFun (bg_blockRows g s) (bg_Xr g ρ j c s) (cubeM N) := by
  have hI : iIndepFun (fun r (w : Param N) => w r) (cubeM N) :=
    iIndepFun_rows (fun _ v => v) fun _ => measurable_id
  set γs := (g.symm s).1
  set Sr := univ.filter fun r : State N => (g.symm r).1 = γs
  set Tr := univ.filter fun r : State N => (g.symm r).1 ≠ γs
  have hST : Disjoint Sr Tr := by
    rw [Finset.disjoint_filter]; intro r _ h h'; exact h' h
  have h := hI.indepFun_finset Sr Tr hST fun r => measurable_pi_apply r
  have hS : ∀ u, g (γs, u) ∈ Sr := fun u => by simp [Sr]
  have hT : ∀ k u, g ((bg_er γs k).1, u) ∈ Tr := fun k u => by
    simp only [Tr, mem_filter, mem_univ, true_and, Equiv.symm_apply_apply]
    exact (bg_er γs k).2
  let φ : (Sr → Fin N → ℝ) → K → Fin N → ℝ := fun x u => x ⟨_, hS u⟩
  let ψ : (Tr → Fin N → ℝ) → Fin (Fintype.card Γ - 1) → ι → ℝ :=
    fun x k => bg_F ρ j c fun u => x ⟨_, hT k u⟩
  have hφ : Measurable φ := Measurable.of_eval fun _ => measurable_pi_apply _
  have hψ : Measurable ψ := Measurable.of_eval fun _ =>
    (bg_measurable_F ρ j c).comp (Measurable.of_eval fun _ => measurable_pi_apply _)
  exact h.comp hφ hψ

end Param

/-! ### Rows parametrised by the bits on and off the image of an injection -/

section Rows

variable {n : ℕ} (E : Fin n → Fin N) {K : Type*} [Fintype K] (bits : K → Fin n → Bool)

/-- The units of the image of `E`. -/
def bg_U : Finset (Fin N) := univ.image E

/-- Backgrounds: the bits off the image of `E`. -/
abbrev bg_Bg := {j : Fin N // j ∉ bg_U E} → Bool

lemma bg_mem_U {j : Fin N} (h : j ∈ bg_U E) : ∃ g, E g = j := by
  simpa [bg_U] using h

/-- The index of a unit of the image. -/
def bg_idx {j : Fin N} (h : j ∈ bg_U E) : Fin n := (bg_mem_U E h).choose

lemma bg_idx_spec {j : Fin N} (h : j ∈ bg_U E) : E (bg_idx E h) = j := (bg_mem_U E h).choose_spec

lemma bg_E_mem (g : Fin n) : E g ∈ bg_U E := mem_image_of_mem E (mem_univ g)

/-- The row with background `γ` and bits `bits u` on the image of `E`. -/
def bg_row (γ : bg_Bg E) (u : K) : State N :=
  fun j => if h : j ∈ bg_U E then bits u (bg_idx E h) else γ ⟨j, h⟩

variable {E}

lemma bg_row_E (hE : Function.Injective E) (γ : bg_Bg E) (u : K) (g : Fin n) :
    bg_row E bits γ u (E g) = bits u g := by
  simp only [bg_row, bg_E_mem, ↓reduceDIte]
  rw [hE (bg_idx_spec E (bg_E_mem E g))]

lemma bg_row_out (γ : bg_Bg E) (u : K) {j : Fin N} (hj : j ∉ bg_U E) :
    bg_row E bits γ u j = γ ⟨j, hj⟩ := by
  simp [bg_row, hj]

lemma bg_row_inj (hE : Function.Injective E) (hb : Function.Injective bits) :
    Function.Injective fun q : bg_Bg E × K => bg_row E bits q.1 q.2 := by
  rintro ⟨γ, u⟩ ⟨γ', u'⟩ h
  have h' := congrFun h
  simp only at h'
  refine Prod.ext (funext fun ⟨j, hj⟩ => ?_) (hb (funext fun g => ?_))
  · have := h' j
    rwa [bg_row_out bits γ u hj, bg_row_out bits γ' u' hj] at this
  · have := h' (E g)
    rwa [bg_row_E bits hE, bg_row_E bits hE] at this

lemma bg_card_U (hE : Function.Injective E) : (bg_U E).card = n := by
  rw [bg_U, card_image_of_injective _ hE, card_univ, Fintype.card_fin]

lemma bg_le_of_inj (hE : Function.Injective E) : n ≤ N := by
  have := Fintype.card_le_of_injective E hE
  simpa using this

lemma bg_card_Bg (hE : Function.Injective E) : Fintype.card (bg_Bg E) = 2 ^ (N - n) := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl, Fintype.card_coe,
    bg_card_U hE, Fintype.card_fin]

/-- The parametrisation of the rows by (background, bits on the image of `E`). -/
def bg_eqv (hE : Function.Injective E) (hb : Function.Injective bits)
    (hK : Fintype.card K = 2 ^ n) : bg_Bg E × K ≃ State N :=
  Equiv.ofBijective (fun q => bg_row E bits q.1 q.2)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨bg_row_inj bits hE hb, by
      rw [Fintype.card_prod, bg_card_Bg hE, hK, ← pow_add, Nat.sub_add_cancel (bg_le_of_inj hE)]
      simp⟩)

@[simp] lemma bg_eqv_apply (hE : Function.Injective E) (hb : Function.Injective bits)
    (hK : Fintype.card K = 2 ^ n) (q : bg_Bg E × K) :
    bg_eqv bits hE hb hK q = bg_row E bits q.1 q.2 := rfl

/-- **Merge rule**: merging a state `t` on `S ⊆ image E` moves row `u` to row `ρ0 u` of the same
superblock, as soon as the bits of `ρ0 u` are those of `t` on `S` and those of `u` elsewhere. -/
lemma bg_merge_row (hE : Function.Injective E) {S : Finset (Fin N)} (hS : S ⊆ bg_U E)
    (t : State N) (ρ0 : K → K)
    (h : ∀ u g, bits (ρ0 u) g = if E g ∈ S then t (E g) else bits u g)
    (γ : bg_Bg E) (u : K) : merge S t (bg_row E bits γ u) = bg_row E bits γ (ρ0 u) := by
  funext j
  by_cases hj : j ∈ bg_U E
  · obtain ⟨g, rfl⟩ := bg_mem_U E hj
    simp only [merge]
    rw [bg_row_E bits hE, bg_row_E bits hE, h]
  · have hjS : j ∉ S := fun h' => hj (hS h')
    rw [merge_not_mem hjS, bg_row_out bits γ u hj, bg_row_out bits γ (ρ0 u) hj]

end Rows

/-! ### Bits of patterns -/

/-- Bit `g` of the pattern `u`. -/
def bg_bits (n : ℕ) (u : Fin (2 ^ n)) (g : Fin n) : Bool := (u : ℕ).testBit g

lemma bg_bits_inj (n : ℕ) : Function.Injective (bg_bits n) := by
  intro u u' h
  refine Fin.ext (Nat.eq_of_testBit_eq fun i => ?_)
  by_cases hi : i < n
  · exact congrFun h ⟨i, hi⟩
  · have h1 : (u : ℕ) < 2 ^ i := lt_of_lt_of_le u.2 (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : (u' : ℕ) < 2 ^ i := lt_of_lt_of_le u'.2 (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

/-- The state carrying the pattern `u` on the image of `E` and `false` elsewhere. -/
def bg_pst {n : ℕ} (E : Fin n → Fin N) (u : Fin (2 ^ n)) : State N :=
  bg_row E (bg_bits n) (fun _ => false) u

lemma bg_pst_E {n : ℕ} {E : Fin n → Fin N} (hE : Function.Injective E) (u : Fin (2 ^ n))
    (g : Fin n) : bg_pst E u (E g) = bg_bits n u g :=
  bg_row_E _ hE _ u g

end

end Census
end IIT
