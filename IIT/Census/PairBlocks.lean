/-
Census of complexes: the block decomposition of the cause-side differences of a pair.

For a pair `{a, b}` of distinct units the rows of the parameter cube split into `2^(N-2)` blocks of
four rows agreeing off `{a, b}`.  The six differences `etaP w a b i ta tb` (`i ∈ {a, b}`,
`(ta, tb) ≠ (false, false)`), collected in the vector `pb_eta w a b : Fin 6 → ℝ`, are sums over the
blocks of summands which, under `cubeM N`, are independent with a common law `pb_nu a b`.

Coordinates: `p : Fin 6` stands for the unit `a` if `p < 3` and `b` otherwise, and for the pattern
`(true,false)`, `(false,true)`, `(true,true)` according to `p mod 3 = 0, 1, 2`.

This file proves
* the decomposition `pb_eta_eq_sum` and the law `pb_map_Xs` of the family of summands;
* the moments of `pb_nu`: zero means (`pb_nu_mean`), second moments
  `|2^(N-2) ∫ x p * x q - pb_Gam p q| ≤ (3/4)^N / 2` (`pb_nu_second`), where `pb_Gam` is the
  limit covariance `(1/64 + 23/320 [i = j]) ([t = u] + 1)`, and third absolute moments
  `2^(N-2) ∫ (∑ |x p|)^3 ≤ 3456 (23/25)^N` (`pb_nu_third`);
* the removal of the block of a state `s`: the remaining `2^(N-2) - 1` summands keep the law
  (`pb_map_Xr`), are independent of the rows of that block (`pb_indep_rest`), and on `g2` the
  removed summand is at most `4 tauN N / sigN N` in every coordinate (`pb_abs_eta_sub_le`).
-/
import IIT.Census.TightStats
import IIT.Census.ColSplit

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

noncomputable section

variable {N : ℕ}

/-! ### Coordinates and the limit covariance -/

/-- Patterns of a pair of units. -/
abbrev PbPat := Bool × Bool

/-- The pattern of coordinate `p`. -/
def pb_pt (p : Fin 6) : PbPat :=
  if p.val % 3 = 0 then (true, false) else if p.val % 3 = 1 then (false, true) else (true, true)

/-- Coordinate `p` refers to the first unit of the pair iff `p < 3`. -/
def pb_pu (p : Fin 6) : Bool := decide (p.val < 3)

/-- The unit selected by a Boolean. -/
def pb_sel (a b : Fin N) (c : Bool) : Fin N := if c then a else b

/-- The unit of coordinate `p`. -/
def pb_unit (a b : Fin N) (p : Fin 6) : Fin N := pb_sel a b (pb_pu p)

/-- The limit covariance `Γ∞[(i,t),(j,u)] = (1/64 + 23/320 [i = j]) ([t = u] + 1)`. -/
def pb_Gam (p q : Fin 6) : ℝ :=
  (1 / 64 + if pb_pu p = pb_pu q then 23 / 320 else 0) * ((if pb_pt p = pb_pt q then 1 else 0) + 1)

/-- The vector of the six cause-side differences of the pair `{a, b}`. -/
def pb_eta (w : Param N) (a b : Fin N) : Fin 6 → ℝ :=
  fun p => etaP w a b (pb_unit a b p) (pb_pt p).1 (pb_pt p).2

lemma pb_pt_ne (p : Fin 6) : pb_pt p ≠ (false, false) := by
  unfold pb_pt; split_ifs <;> simp

lemma pb_Gam_nonneg (p q : Fin 6) : 0 ≤ pb_Gam p q := by
  unfold pb_Gam; split_ifs <;> norm_num

lemma pb_Gam_le (p q : Fin 6) : pb_Gam p q ≤ 7 / 40 := by
  unfold pb_Gam; split_ifs <;> norm_num

/-! ### Block summands -/

/-- Row product of row `u` of a family of rows. -/
def pb_P {K : Type*} (y : K → Fin N → ℝ) (u : K) : ℝ := ∏ j, clamp01 (y u j)

/-- Total row product of a family of rows. -/
def pb_W {K : Type*} [Fintype K] (y : K → Fin N → ℝ) : ℝ := ∑ u, pb_P y u

/-- The summand of a block, as a function of its four rows. -/
def pb_F (a b : Fin N) (y : PbPat → Fin N → ℝ) : Fin 6 → ℝ :=
  fun p => pb_W y * (clamp01 (y (pb_pt p) (pb_unit a b p)) -
    clamp01 (y (false, false) (pb_unit a b p))) / sigN N

/-- The law of the four rows of a block. -/
def pb_blkM (N : ℕ) : Measure (PbPat → Fin N → ℝ) := Measure.pi fun _ => rowM N

instance : IsProbabilityMeasure (pb_blkM N) := by unfold pb_blkM; infer_instance

lemma pb_measurable_cl {K : Type*} (t : K) (j : Fin N) :
    Measurable fun y : K → Fin N → ℝ => clamp01 (y t j) :=
  clamp01_measurable.comp ((measurable_pi_apply j).comp (measurable_pi_apply t))

lemma pb_measurable_P {K : Type*} (u : K) : Measurable fun y : K → Fin N → ℝ => pb_P y u :=
  Finset.measurable_prod _ fun j _ => pb_measurable_cl u j

lemma pb_measurable_W {K : Type*} [Fintype K] : Measurable fun y : K → Fin N → ℝ => pb_W y :=
  Finset.measurable_sum _ fun u _ => pb_measurable_P u

lemma pb_measurable_F (a b : Fin N) : Measurable (pb_F a b) :=
  Measurable.of_eval fun _ =>
    (pb_measurable_W.mul ((pb_measurable_cl _ _).sub (pb_measurable_cl _ _))).div_const _

/-- The common law of the block summands. -/
def pb_nu (a b : Fin N) : Measure (Fin 6 → ℝ) := (pb_blkM N).map (pb_F a b)

instance (a b : Fin N) : IsProbabilityMeasure (pb_nu a b) := by
  unfold pb_nu; infer_instance

lemma pb_P_nonneg {K : Type*} (y : K → Fin N → ℝ) (u : K) : 0 ≤ pb_P y u :=
  prod_nonneg fun _ _ => clamp01_nonneg _

lemma pb_P_le_one {K : Type*} (y : K → Fin N → ℝ) (u : K) : pb_P y u ≤ 1 :=
  prod_le_one (fun _ _ => clamp01_nonneg _) fun _ _ => clamp01_le_one _

lemma pb_W_nonneg {K : Type*} [Fintype K] (y : K → Fin N → ℝ) : 0 ≤ pb_W y :=
  sum_nonneg fun u _ => pb_P_nonneg y u

lemma pb_W_le {K : Type*} [Fintype K] (y : K → Fin N → ℝ) : pb_W y ≤ Fintype.card K := by
  unfold pb_W
  calc ∑ u, pb_P y u ≤ ∑ _u : K, (1 : ℝ) := sum_le_sum fun u _ => pb_P_le_one y u
    _ = Fintype.card K := by simp

lemma pb_abs_cl_sub (x y : ℝ) : |clamp01 x - clamp01 y| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [clamp01_nonneg x, clamp01_le_one x, clamp01_nonneg y, clamp01_le_one y]

lemma pb_abs_F_le (a b : Fin N) (y : PbPat → Fin N → ℝ) (p : Fin 6) :
    |pb_F a b y p| ≤ pb_W y / sigN N := by
  have hs := sigN_pos N
  rw [pb_F, abs_div, abs_mul, abs_of_nonneg (pb_W_nonneg y), abs_of_pos hs]
  gcongr
  calc pb_W y * |clamp01 (y (pb_pt p) (pb_unit a b p)) - clamp01 (y (false, false) (pb_unit a b p))|
      ≤ pb_W y * 1 := by gcongr; · exact pb_W_nonneg y
                         exact pb_abs_cl_sub _ _
    _ = pb_W y := mul_one _

/-! ### Regrouping the cause numerators by blocks -/

lemma pb_meanW_self (w : Param N) (S : Finset (Fin N)) (t : State N) (i : Fin N) (v : State N) :
    meanW w S S t i v = clamp01 (w (merge S t v) i) := by
  have h : agree (S ∪ Sᶜ) (merge S t v) = {merge S t v} := by
    ext r
    simp only [mem_agree, Finset.union_compl, Finset.mem_univ, true_implies, mem_singleton]
    exact ⟨fun h => funext h, fun h j => by rw [h]⟩
  rw [meanW, h, sum_singleton, Nat.sub_self, pow_zero, div_one]

/-- The conditioned cause numerator of a pair, regrouped along a block parametrisation `e` of the
rows (`e (k, u)` is row `u` of block `k`). -/
lemma pb_Num_regroup {ι : Type*} [Fintype ι] (a b : Fin N) (e : ι × PbPat ≃ State N)
    (he : ∀ k u (t : State N), merge {a, b} t (e (k, u)) = e (k, (t a, t b)))
    (w : Param N) (t : State N) (i : Fin N) :
    Num w {a, b} {a, b} t i =
      ∑ k, clamp01 (w (e (k, (t a, t b))) i) * pb_W (fun u => w (e (k, u))) := by
  rw [Num, ← e.sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun k _ => ?_
  rw [pb_W, mul_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [pb_meanW_self, he]
  rfl

lemma pb_pat_a (a b : Fin N) (ta tb : Bool) : pat a b ta tb a = ta := by simp [pat]

lemma pb_pat_b {a b : Fin N} (hab : a ≠ b) (ta tb : Bool) : pat a b ta tb b = tb := by
  simp [pat, hab.symm]

/-- **Block decomposition** of the cause-side differences along a block parametrisation. -/
theorem pb_eta_regroup {ι : Type*} [Fintype ι] {a b : Fin N} (hab : a ≠ b)
    (e : ι × PbPat ≃ State N)
    (he : ∀ k u (t : State N), merge {a, b} t (e (k, u)) = e (k, (t a, t b))) (w : Param N) :
    pb_eta w a b = ∑ k, pb_F a b (fun u => w (e (k, u))) := by
  funext p
  rw [Finset.sum_apply, pb_eta, etaP, pb_Num_regroup a b e he, pb_Num_regroup a b e he,
    ← sum_sub_distrib, sum_div]
  simp only [pb_pat_a, pb_pat_b hab, Prod.mk.eta]
  refine sum_congr rfl fun k _ => ?_
  simp only [pb_F]
  ring

/-! ### The blocks of a pair -/

/-- Backgrounds of the blocks of `{a, b}`: the bits off `{a, b}`. -/
abbrev PbBlk (a b : Fin N) := {j : Fin N // j ∉ ({a, b} : Finset (Fin N))} → Bool

/-- Row `t` of block `β`. -/
def pb_row (a b : Fin N) (β : PbBlk a b) (t : PbPat) : State N :=
  fun j => if ha : j = a then t.1 else if hb : j = b then t.2 else β ⟨j, by simp [ha, hb]⟩

/-- The block of a row. -/
def pb_blk (a b : Fin N) (r : State N) : PbBlk a b := fun j => r j.1

section Rows

variable {a b : Fin N}

lemma pb_row_a (β : PbBlk a b) (t : PbPat) : pb_row a b β t a = t.1 := by simp [pb_row]

lemma pb_row_b (hab : a ≠ b) (β : PbBlk a b) (t : PbPat) : pb_row a b β t b = t.2 := by
  simp [pb_row, hab.symm]

lemma pb_row_out (β : PbBlk a b) (t : PbPat) {j : Fin N} (hj : j ∉ ({a, b} : Finset (Fin N))) :
    pb_row a b β t j = β ⟨j, hj⟩ := by
  have ha : j ≠ a := by rintro rfl; simp at hj
  have hb : j ≠ b := by rintro rfl; simp at hj
  simp [pb_row, ha, hb]

lemma pb_row_blk (r : State N) : pb_row a b (pb_blk a b r) (r a, r b) = r := by
  funext j
  by_cases ha : j = a
  · subst ha; simp [pb_row]
  by_cases hb : j = b
  · subst hb; simp [pb_row, ha]
  simp [pb_row, ha, hb, pb_blk]

lemma pb_blk_row (β : PbBlk a b) (t : PbPat) : pb_blk a b (pb_row a b β t) = β := by
  funext ⟨j, hj⟩
  exact pb_row_out β t hj

/-- A row agreeing with `s` off `{a, b}` is a row of the block of `s`. -/
lemma pb_row_of_agree {r s : State N} (h : ∀ j ∉ ({a, b} : Finset (Fin N)), r j = s j) :
    r = pb_row a b (pb_blk a b s) (r a, r b) := by
  have hb : pb_blk a b r = pb_blk a b s := by
    funext ⟨j, hj⟩; exact h j hj
  rw [← hb, pb_row_blk]

/-- Rows are parametrised by (block, pattern). -/
def pb_eqv (hab : a ≠ b) : PbBlk a b × PbPat ≃ State N where
  toFun k := pb_row a b k.1 k.2
  invFun r := (pb_blk a b r, (r a, r b))
  left_inv := by
    rintro ⟨β, t⟩
    simp [pb_blk_row, pb_row_a, pb_row_b hab]
  right_inv r := pb_row_blk r

@[simp] lemma pb_eqv_apply (hab : a ≠ b) (k : PbBlk a b × PbPat) :
    pb_eqv hab k = pb_row a b k.1 k.2 := rfl

lemma pb_merge_row (hab : a ≠ b) (β : PbBlk a b) (u : PbPat) (t : State N) :
    merge {a, b} t (pb_row a b β u) = pb_row a b β (t a, t b) := by
  funext j
  by_cases ha : j = a
  · subst ha; simp [merge, pb_row]
  by_cases hb : j = b
  · subst hb; simp [merge, pb_row, ha]
  have hj : j ∉ ({a, b} : Finset (Fin N)) := by simp [ha, hb]
  rw [merge_not_mem hj, pb_row_out β _ hj, pb_row_out β _ hj]

end Rows

/-- The summand of block `β`. -/
def pb_X (a b : Fin N) (β : PbBlk a b) (w : Param N) : Fin 6 → ℝ :=
  pb_F a b (fun t => w (pb_row a b β t))

/-- The number of blocks. -/
def pb_B (a b : Fin N) : ℕ := Fintype.card (PbBlk a b)

lemma pb_B_eq {a b : Fin N} (hab : a ≠ b) : pb_B a b = 2 ^ (N - 2) := by
  rw [pb_B, Fintype.card_fun, Fintype.card_bool]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_coe, card_pair hab, Fintype.card_fin]

lemma pb_two_le {a b : Fin N} (hab : a ≠ b) : 2 ≤ N := by
  have := card_pair hab
  have h2 := Finset.card_le_univ ({a, b} : Finset (Fin N))
  rw [Fintype.card_fin] at h2
  omega

lemma pb_B_pos (a b : Fin N) : 0 < pb_B a b := Fintype.card_pos

/-- Enumeration of the blocks. -/
def pb_e (a b : Fin N) : Fin (pb_B a b) ≃ PbBlk a b := (Fintype.equivFin _).symm

/-- The family of block summands, indexed by `Fin (pb_B a b)`. -/
def pb_Xs (a b : Fin N) (w : Param N) : Fin (pb_B a b) → Fin 6 → ℝ :=
  fun k => pb_X a b (pb_e a b k) w

/-- **Block decomposition**: `η = ∑_β X_β`. -/
theorem pb_eta_eq_sum_blk {a b : Fin N} (hab : a ≠ b) (w : Param N) :
    pb_eta w a b = ∑ β, pb_X a b β w := by
  rw [pb_eta_regroup hab (pb_eqv hab) (fun β u t => pb_merge_row hab β u t) w,
    Fintype.sum_congr _ _ fun β => rfl]
  rfl

/-- **Block decomposition**, enumerated form. -/
theorem pb_eta_eq_sum {a b : Fin N} (hab : a ≠ b) (w : Param N) :
    pb_eta w a b = ∑ k, pb_Xs a b w k := by
  rw [pb_eta_eq_sum_blk hab, ← (pb_e a b).sum_comp]
  rfl

/-! ### The law of the block summands -/

/-- Reading the rows through an injective parametrisation `g : ι × κ → State N` turns `cubeM N`
into an iid product over `ι` of iid products over `κ` of rows. -/
lemma pb_map_rows {ι κ : Type*} [Fintype ι] [Fintype κ] (g : ι × κ → State N)
    (hg : Function.Injective g) :
    (cubeM N).map (fun w (k : ι) (t : κ) => w (g (k, t))) =
      Measure.pi fun _ : ι => Measure.pi fun _ : κ => rowM N := by
  have h1 := map_comp_inj g hg (rowM N)
  have h2 := Measure.infinitePi_map_curry (X := Fin N → ℝ) (fun (_ : ι) (_ : κ) => rowM N)
  simp only [Measure.infinitePi_eq_pi] at h2
  unfold cubeM
  have hψ : Measurable fun (x : State N → Fin N → ℝ) (j : ι × κ) => x (g j) :=
    Measurable.of_eval fun j => measurable_pi_apply (g j)
  rw [← h2, ← h1, Measure.map_map (MeasurableEquiv.measurable _) hψ]
  rfl

/-- Summands `F (rows of block k)` over the blocks of an injective parametrisation are iid. -/
lemma pb_map_blocks {ι κ E : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace E]
    (g : ι × κ → State N) (hg : Function.Injective g) (F : (κ → Fin N → ℝ) → E)
    (hF : Measurable F) :
    (cubeM N).map (fun w (k : ι) => F (fun t => w (g (k, t)))) =
      Measure.pi fun _ : ι => (Measure.pi fun _ : κ => rowM N).map F := by
  have hm : Measurable fun (w : Param N) (k : ι) (t : κ) => w (g (k, t)) :=
    Measurable.of_eval fun k => Measurable.of_eval fun t => measurable_pi_apply _
  have hc : (fun w (k : ι) => F (fun t => w (g (k, t)))) =
      (fun y (k : ι) => F (y k)) ∘ fun (w : Param N) (k : ι) (t : κ) => w (g (k, t)) := rfl
  have h1 : Measurable fun (y : ι → κ → Fin N → ℝ) (k : ι) => F (y k) :=
    Measurable.of_eval fun k => hF.comp (measurable_pi_apply k)
  rw [hc, ← Measure.map_map h1 hm, pb_map_rows g hg]
  exact Measure.pi_map_pi fun _ => hF.aemeasurable

lemma pb_measurable_X (a b : Fin N) (β : PbBlk a b) : Measurable (pb_X a b β) :=
  (pb_measurable_F a b).comp (Measurable.of_eval fun _ => measurable_pi_apply _)

lemma pb_measurable_Xs (a b : Fin N) : Measurable (pb_Xs a b (N := N)) :=
  Measurable.of_eval fun _ => pb_measurable_X a b _

/-- **Law of the block summands**: under `cubeM N` the summands are iid with law `pb_nu a b`. -/
theorem pb_map_X {a b : Fin N} (hab : a ≠ b) :
    (cubeM N).map (fun w (β : PbBlk a b) => pb_X a b β w) =
      Measure.pi fun _ : PbBlk a b => pb_nu a b :=
  pb_map_blocks (fun k => pb_row a b k.1 k.2) (pb_eqv hab).injective (pb_F a b)
    (pb_measurable_F a b)

/-- **Law of the block summands**, enumerated form (the input of Lindeberg's bound). -/
theorem pb_map_Xs {a b : Fin N} (hab : a ≠ b) :
    (cubeM N).map (pb_Xs a b) = Measure.pi fun _ : Fin (pb_B a b) => pb_nu a b := by
  have hc : pb_Xs a b = (fun (x : PbBlk a b → Fin 6 → ℝ) k => x (pb_e a b k)) ∘
      fun w (β : PbBlk a b) => pb_X a b β w := rfl
  rw [hc, ← Measure.map_map (Measurable.of_eval fun k => measurable_pi_apply _)
    (Measurable.of_eval fun β => pb_measurable_X a b β), pb_map_X hab]
  exact map_comp_inj _ (pb_e a b).injective _

/-! ### Zero means -/

/-- Integrals over iid rows are invariant under an injective relabelling of the rows. -/
lemma pb_integral_comp_inj {K : Type*} [Fintype K] (g : K → K) (hg : Function.Injective g)
    {f : (K → Fin N → ℝ) → ℝ} (hf : Measurable f) :
    ∫ y, f (fun k => y (g k)) ∂(Measure.pi fun _ : K => rowM N) =
      ∫ y, f y ∂(Measure.pi fun _ : K => rowM N) := by
  have h := map_comp_inj g hg (rowM N)
  have hφ : Measurable fun (x : K → Fin N → ℝ) k => x (g k) :=
    Measurable.of_eval fun k => measurable_pi_apply _
  rw [← integral_map hφ.aemeasurable (by rw [h]; exact hf.aestronglyMeasurable), h]

lemma pb_W_comp_equiv {K : Type*} [Fintype K] (σ : K ≃ K) (y : K → Fin N → ℝ) :
    pb_W (fun u => y (σ u)) = pb_W y :=
  σ.sum_comp fun u => pb_P y u

/-- Exchanging the rows `pb_pt p` and `(false, false)` of a block negates coordinate `p`. -/
lemma pb_F_swap (a b : Fin N) (y : PbPat → Fin N → ℝ) (p : Fin 6) :
    pb_F a b (fun u => y (Equiv.swap (pb_pt p) (false, false) u)) p = -pb_F a b y p := by
  have hW := pb_W_comp_equiv (Equiv.swap (pb_pt p) (false, false)) y
  simp only [pb_F, hW, Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

lemma pb_integral_nu {a b : Fin N} {g : (Fin 6 → ℝ) → ℝ} (hg : Measurable g) :
    ∫ x, g x ∂pb_nu a b = ∫ y, g (pb_F a b y) ∂pb_blkM N :=
  integral_map (pb_measurable_F a b).aemeasurable hg.aestronglyMeasurable

/-- **Zero means** of `pb_nu`. -/
theorem pb_nu_mean (a b : Fin N) (p : Fin 6) : ∫ x, x p ∂pb_nu a b = 0 := by
  rw [pb_integral_nu (measurable_pi_apply p)]
  have h := pb_integral_comp_inj (Equiv.swap (pb_pt p) (false, false)) (Equiv.injective _)
    (f := fun y => pb_F a b y p) ((measurable_pi_apply p).comp (pb_measurable_F a b))
  simp only [pb_F_swap, integral_neg] at h
  unfold pb_blkM
  linarith

/-! ### Monomials in the rows of a block -/

/-- A monomial in the clamped entries of a family of rows. -/
def pb_mono {K : Type*} [Fintype K] (E : K → Fin N → ℕ) (y : K → Fin N → ℝ) : ℝ :=
  ∏ t, ∏ j, clamp01 (y t j) ^ E t j

lemma pb_integral_mono {K : Type*} [Fintype K] (E : K → Fin N → ℕ) :
    ∫ y, pb_mono E y ∂(Measure.pi fun _ : K => rowM N) = ∏ t, ∏ j, 1 / ((E t j : ℝ) + 1) := by
  unfold pb_mono
  rw [integral_fintype_prod_eq_prod (fun t (v : Fin N → ℝ) => ∏ j, clamp01 (v j) ^ E t j)]
  exact prod_congr rfl fun t _ => integral_rowM_monomial (E t)

lemma pb_prod_row_ind {K : Type*} [Fintype K] [DecidableEq K] (y : K → Fin N → ℝ) (u : K) :
    ∏ t, ∏ j, clamp01 (y t j) ^ (if t = u then 1 else 0) = pb_P y u := by
  rw [Fintype.prod_eq_single u fun t ht => by simp [ht]]
  simp [pb_P]

lemma pb_prod_single_ind {K : Type*} [Fintype K] [DecidableEq K] (y : K → Fin N → ℝ) (s : K)
    (i : Fin N) :
    ∏ t, ∏ j, clamp01 (y t j) ^ (if t = s ∧ j = i then 1 else 0) = clamp01 (y s i) := by
  rw [Fintype.prod_eq_single s fun t ht => by simp [ht]]
  rw [Fintype.prod_eq_single i fun j hj => by simp [hj]]
  simp

/-- The product `P u1 P u2 cl(y s i) cl(y s' i')`. -/
def pb_M (y : PbPat → Fin N → ℝ) (u1 u2 s s' : PbPat) (i i' : Fin N) : ℝ :=
  pb_P y u1 * pb_P y u2 * clamp01 (y s i) * clamp01 (y s' i')

lemma pb_M_eq_mono (y : PbPat → Fin N → ℝ) (u1 u2 s s' : PbPat) (i i' : Fin N) :
    pb_M y u1 u2 s s' i i' = pb_mono (fun t j => (if t = u1 then 1 else 0) +
      (if t = u2 then 1 else 0) + (if t = s ∧ j = i then 1 else 0) +
      (if t = s' ∧ j = i' then 1 else 0)) y := by
  simp only [pb_mono, pow_add, prod_mul_distrib]
  rw [pb_prod_row_ind, pb_prod_row_ind, pb_prod_single_ind, pb_prod_single_ind]
  rfl

lemma pb_measurable_M (u1 u2 s s' : PbPat) (i i' : Fin N) :
    Measurable fun y : PbPat → Fin N → ℝ => pb_M y u1 u2 s s' i i' :=
  (((pb_measurable_P u1).mul (pb_measurable_P u2)).mul (pb_measurable_cl s i)).mul
    (pb_measurable_cl s' i')

lemma pb_integrable_M (u1 u2 s s' : PbPat) (i i' : Fin N) :
    Integrable (fun y => pb_M y u1 u2 s s' i i') (pb_blkM N) := by
  refine Integrable.of_bound (pb_measurable_M u1 u2 s s' i i').aestronglyMeasurable 1
    (ae_of_all _ fun y => ?_)
  have h1 := pb_P_nonneg y u1; have h2 := pb_P_nonneg y u2
  have h3 := pb_P_le_one y u1; have h4 := pb_P_le_one y u2
  have h5 := clamp01_nonneg (y s i); have h6 := clamp01_le_one (y s i)
  have h7 := clamp01_nonneg (y s' i'); have h8 := clamp01_le_one (y s' i')
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold pb_M; positivity)]
  unfold pb_M
  calc pb_P y u1 * pb_P y u2 * clamp01 (y s i) * clamp01 (y s' i') ≤ 1 * 1 * 1 * 1 := by gcongr
    _ = 1 := by norm_num

/-- Exponent of column `a` in row `t`. -/
def pb_ea (u1 u2 s s' : PbPat) (ia ia' : Bool) (t : PbPat) : ℕ :=
  (if t = u1 then 1 else 0) + (if t = u2 then 1 else 0) + (if t = s ∧ ia = true then 1 else 0) +
    (if t = s' ∧ ia' = true then 1 else 0)

/-- Exponent of column `b` in row `t`. -/
def pb_eb (u1 u2 s s' : PbPat) (ia ia' : Bool) (t : PbPat) : ℕ :=
  (if t = u1 then 1 else 0) + (if t = u2 then 1 else 0) + (if t = s ∧ ia = false then 1 else 0) +
    (if t = s' ∧ ia' = false then 1 else 0)

/-- Splitting a product over the units at two distinct units. -/
lemma pb_prod_split {a b : Fin N} (hab : a ≠ b) (f : Fin N → ℝ) (c : ℝ)
    (hf : ∀ j, j ≠ a → j ≠ b → f j = c) : ∏ j, f j = f a * f b * c ^ (N - 2) := by
  rw [← Finset.mul_prod_erase univ f (mem_univ a),
    ← Finset.mul_prod_erase (univ.erase a) f (mem_erase.2 ⟨hab.symm, mem_univ b⟩), mul_assoc]
  congr 2
  rw [prod_congr rfl fun j hj => hf j (ne_of_mem_erase (mem_of_mem_erase hj))
    (ne_of_mem_erase hj), prod_const]
  congr 1
  rw [card_erase_of_mem (mem_erase.2 ⟨hab.symm, mem_univ b⟩), card_erase_of_mem (mem_univ a),
    card_univ, Fintype.card_fin]
  omega

lemma pb_sel_a {a b : Fin N} (hab : a ≠ b) (c : Bool) : (a = pb_sel a b c) ↔ c = true := by
  cases c <;> simp [pb_sel, hab]

lemma pb_sel_b {a b : Fin N} (hab : a ≠ b) (c : Bool) : (b = pb_sel a b c) ↔ c = false := by
  cases c <;> simp [pb_sel, hab.symm]

lemma pb_sel_out {a b j : Fin N} (hja : j ≠ a) (hjb : j ≠ b) (c : Bool) : ¬ (j = pb_sel a b c) := by
  cases c <;> simp [pb_sel, hja, hjb]

lemma pb_prod_kappa (u1 u2 : PbPat) :
    ∏ t : PbPat, 1 / ((((if t = u1 then 1 else 0) + (if t = u2 then 1 else 0) : ℕ) : ℝ) + 1) =
      if u1 = u2 then 1 / 3 else 1 / 4 := by
  rcases u1 with ⟨_ | _, _ | _⟩ <;> rcases u2 with ⟨_ | _, _ | _⟩ <;>
    simp [Fintype.prod_prod_type] <;> norm_num

/-- **Moments of block monomials**. -/
lemma pb_integral_M {a b : Fin N} (hab : a ≠ b) (u1 u2 s s' : PbPat) (ia ia' : Bool) :
    ∫ y, pb_M y u1 u2 s s' (pb_sel a b ia) (pb_sel a b ia') ∂pb_blkM N =
      (if u1 = u2 then 1 / 3 else 1 / 4 : ℝ) ^ (N - 2) *
        ∏ t, (1 / ((pb_ea u1 u2 s s' ia ia' t : ℝ) + 1) *
          (1 / ((pb_eb u1 u2 s s' ia ia' t : ℝ) + 1))) := by
  simp_rw [pb_M_eq_mono]
  rw [pb_blkM, pb_integral_mono, ← pb_prod_kappa, ← prod_pow, ← prod_mul_distrib]
  refine prod_congr rfl fun t _ => ?_
  rw [pb_prod_split hab _ (1 / ((((if t = u1 then 1 else 0) + (if t = u2 then 1 else 0) : ℕ) : ℝ)
    + 1)) fun j hja hjb => by simp [pb_sel_out hja hjb]]
  simp only [pb_sel_a hab, pb_sel_b hab, pb_ea, pb_eb]
  ring

/-! ### Second moments -/

/-- The rational constant of a block monomial. -/
def pb_qq (u1 u2 s s' : PbPat) (ia ia' : Bool) : ℚ :=
  ∏ t : PbPat, (1 / ((pb_ea u1 u2 s s' ia ia' t : ℚ) + 1) * (1 / ((pb_eb u1 u2 s s' ia ia' t : ℚ) + 1)))

/-- The constant of `E[P u1 P u2 D_p D_q]`, with `D_p` the difference in coordinate `p`. -/
def pb_C (u1 u2 : PbPat) (p q : Fin 6) : ℚ :=
  pb_qq u1 u2 (pb_pt p) (pb_pt q) (pb_pu p) (pb_pu q) -
    pb_qq u1 u2 (pb_pt p) (false, false) (pb_pu p) (pb_pu q) -
    pb_qq u1 u2 (false, false) (pb_pt q) (pb_pu p) (pb_pu q) +
    pb_qq u1 u2 (false, false) (false, false) (pb_pu p) (pb_pu q)

/-- The diagonal (`u1 = u2`) part. -/
def pb_A (p q : Fin 6) : ℚ := ∑ u : PbPat, pb_C u u p q

/-- The off-diagonal (`u1 ≠ u2`) part. -/
def pb_A2 (p q : Fin 6) : ℚ := ∑ u1 : PbPat, ∑ u2 : PbPat, if u1 = u2 then 0 else pb_C u1 u2 p q

/-- `pb_Gam` over `ℚ`. -/
def pb_GamQ (p q : Fin 6) : ℚ :=
  (1 / 64 + if pb_pu p = pb_pu q then 23 / 320 else 0) * ((if pb_pt p = pb_pt q then 1 else 0) + 1)

set_option maxRecDepth 100000 in
/-- The leading constants give exactly the limit covariance. -/
theorem pb_A_eq : ∀ p q : Fin 6, 9 / 4 * pb_A p q = pb_GamQ p q := by decide +kernel

set_option maxRecDepth 100000 in
theorem pb_A2_bound : ∀ p q : Fin 6, pb_A2 p q ≤ 1 / 8 ∧ -(1 / 8) ≤ pb_A2 p q := by decide +kernel

lemma pb_Gam_eq_cast (p q : Fin 6) : pb_Gam p q = (pb_GamQ p q : ℝ) := by
  unfold pb_Gam pb_GamQ
  split_ifs <;> push_cast <;> norm_num

lemma pb_qq_cast (u1 u2 s s' : PbPat) (ia ia' : Bool) :
    (pb_qq u1 u2 s s' ia ia' : ℝ) = ∏ t, (1 / ((pb_ea u1 u2 s s' ia ia' t : ℝ) + 1) *
      (1 / ((pb_eb u1 u2 s s' ia ia' t : ℝ) + 1))) := by
  unfold pb_qq
  push_cast
  rfl

lemma pb_FF_expand (a b : Fin N) (y : PbPat → Fin N → ℝ) (p q : Fin 6) :
    pb_F a b y p * pb_F a b y q =
      (∑ u1, ∑ u2, (pb_M y u1 u2 (pb_pt p) (pb_pt q) (pb_unit a b p) (pb_unit a b q) -
        pb_M y u1 u2 (pb_pt p) (false, false) (pb_unit a b p) (pb_unit a b q) -
        pb_M y u1 u2 (false, false) (pb_pt q) (pb_unit a b p) (pb_unit a b q) +
        pb_M y u1 u2 (false, false) (false, false) (pb_unit a b p) (pb_unit a b q))) /
        sigN N ^ 2 := by
  have hW : pb_W y * pb_W y = ∑ u1, ∑ u2, pb_P y u1 * pb_P y u2 := by
    rw [pb_W, sum_mul_sum]
  set cp := clamp01 (y (pb_pt p) (pb_unit a b p))
  set cp0 := clamp01 (y (false, false) (pb_unit a b p))
  set cq := clamp01 (y (pb_pt q) (pb_unit a b q))
  set cq0 := clamp01 (y (false, false) (pb_unit a b q))
  calc pb_F a b y p * pb_F a b y q = (pb_W y * pb_W y) * ((cp - cp0) * (cq - cq0)) / sigN N ^ 2 := by
        simp only [pb_F, cp, cp0, cq, cq0]; ring
    _ = _ := by
        rw [hW, sum_mul, sum_div, sum_div]
        refine sum_congr rfl fun u1 _ => ?_
        rw [sum_mul, sum_div, sum_div]
        refine sum_congr rfl fun u2 _ => ?_
        simp only [pb_M, cp, cp0, cq, cq0]
        ring

lemma pb_integral_C {a b : Fin N} (hab : a ≠ b) (u1 u2 : PbPat) (p q : Fin 6) :
    ∫ y, (pb_M y u1 u2 (pb_pt p) (pb_pt q) (pb_unit a b p) (pb_unit a b q) -
        pb_M y u1 u2 (pb_pt p) (false, false) (pb_unit a b p) (pb_unit a b q) -
        pb_M y u1 u2 (false, false) (pb_pt q) (pb_unit a b p) (pb_unit a b q) +
        pb_M y u1 u2 (false, false) (false, false) (pb_unit a b p) (pb_unit a b q)) ∂pb_blkM N =
      (if u1 = u2 then 1 / 3 else 1 / 4 : ℝ) ^ (N - 2) * (pb_C u1 u2 p q : ℝ) := by
  set i := pb_unit a b p
  set i' := pb_unit a b q
  have hI := fun s s' => pb_integrable_M (N := N) u1 u2 s s' i i'
  have h1 : Integrable (fun y => pb_M y u1 u2 (pb_pt p) (pb_pt q) i i' -
      pb_M y u1 u2 (pb_pt p) (false, false) i i') (pb_blkM N) := (hI _ _).sub (hI _ _)
  have h2 : Integrable (fun y => pb_M y u1 u2 (pb_pt p) (pb_pt q) i i' -
      pb_M y u1 u2 (pb_pt p) (false, false) i i' - pb_M y u1 u2 (false, false) (pb_pt q) i i')
      (pb_blkM N) := h1.sub (hI _ _)
  have hM : ∀ s s', ∫ y, pb_M y u1 u2 s s' i i' ∂pb_blkM N =
      (if u1 = u2 then 1 / 3 else 1 / 4 : ℝ) ^ (N - 2) * (pb_qq u1 u2 s s' (pb_pu p) (pb_pu q) : ℝ) :=
    fun s s' => by rw [pb_qq_cast]; exact pb_integral_M hab u1 u2 s s' _ _
  rw [integral_add h2 (hI _ _), integral_sub h1 (hI _ _), integral_sub (hI _ _) (hI _ _),
    hM, hM, hM, hM, pb_C]
  push_cast
  ring

lemma pb_integral_FF {a b : Fin N} (hab : a ≠ b) (p q : Fin 6) :
    ∫ y, pb_F a b y p * pb_F a b y q ∂pb_blkM N =
      ((1 / 3 : ℝ) ^ (N - 2) * (pb_A p q : ℝ) + (1 / 4 : ℝ) ^ (N - 2) * (pb_A2 p q : ℝ)) /
        sigN N ^ 2 := by
  have hI := fun s s' u1 u2 => pb_integrable_M (N := N) u1 u2 s s' (pb_unit a b p) (pb_unit a b q)
  have hJ : ∀ u1 u2, Integrable (fun y =>
      pb_M y u1 u2 (pb_pt p) (pb_pt q) (pb_unit a b p) (pb_unit a b q) -
        pb_M y u1 u2 (pb_pt p) (false, false) (pb_unit a b p) (pb_unit a b q) -
        pb_M y u1 u2 (false, false) (pb_pt q) (pb_unit a b p) (pb_unit a b q) +
        pb_M y u1 u2 (false, false) (false, false) (pb_unit a b p) (pb_unit a b q)) (pb_blkM N) :=
    fun u1 u2 => (((hI _ _ _ _).sub (hI _ _ _ _)).sub (hI _ _ _ _)).add (hI _ _ _ _)
  simp_rw [pb_FF_expand]
  rw [integral_div, integral_finsetSum _ fun u1 _ => integrable_finsetSum _ fun u2 _ => hJ u1 u2]
  simp_rw [integral_finsetSum _ fun u2 _ => hJ _ u2, pb_integral_C hab]
  congr 1
  simp only [pb_A, pb_A2, Rat.cast_sum]
  simp [Fintype.sum_prod_type]
  ring

lemma pb_sigN_sq (N : ℕ) : sigN N ^ 2 = (2 / 3 : ℝ) ^ N :=
  Real.sq_sqrt (by positivity)

/-- **Second moments** of the block law: `2^(N-2) ∫ x p x q dν = Γ∞ p q + O((3/4)^N)`. -/
theorem pb_nu_second {a b : Fin N} (hab : a ≠ b) (p q : Fin 6) :
    |(pb_B a b : ℝ) * ∫ x, x p * x q ∂pb_nu a b - pb_Gam p q| ≤ (3 / 4 : ℝ) ^ N / 2 := by
  rw [pb_integral_nu (g := fun x => x p * x q) ((measurable_pi_apply p).mul (measurable_pi_apply q)),
    pb_integral_FF hab,
    pb_B_eq hab, pb_sigN_sq, pb_Gam_eq_cast, ← pb_A_eq p q]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by have := pb_two_le hab; omega⟩
  simp only [Nat.add_sub_cancel]
  have hb := pb_A2_bound p q
  have hb1 : (pb_A2 p q : ℝ) ≤ 1 / 8 := by
    rw [show (1 / 8 : ℝ) = ((1 / 8 : ℚ) : ℝ) by norm_num, Rat.cast_le]; exact hb.1
  have hb2 : -(1 / 8 : ℝ) ≤ pb_A2 p q := by
    rw [show -(1 / 8 : ℝ) = ((-(1 / 8) : ℚ) : ℝ) by norm_num, Rat.cast_le]; exact hb.2
  set A := (pb_A p q : ℝ)
  set A2 := (pb_A2 p q : ℝ)
  have h1 : (2 : ℝ) ^ n * (1 / 3) ^ n = (2 / 3) ^ n := by rw [← mul_pow]; norm_num
  have h2 : (2 : ℝ) ^ n * (1 / 4) ^ n = (3 / 4) ^ n * (2 / 3) ^ n := by
    rw [← mul_pow, ← mul_pow]; norm_num
  have key : ((2 : ℝ) ^ n * (((1 / 3) ^ n * A + (1 / 4) ^ n * A2) / (2 / 3) ^ (n + 2))) =
      9 / 4 * A + 4 * (3 / 4) ^ (n + 2) * A2 := by
    rw [mul_div_assoc', div_eq_iff (by positivity)]
    linear_combination A * h1 + A2 * h2
  push_cast
  rw [key]
  have hp : (0 : ℝ) ≤ (3 / 4) ^ (n + 2) := by positivity
  rw [abs_le]
  constructor <;> nlinarith

/-- Each second moment of `pb_nu` is at most `4 (3/4)^N` in absolute value. -/
lemma pb_abs_nu_second_le {a b : Fin N} (hab : a ≠ b) (p q : Fin 6) :
    |∫ x, x p * x q ∂pb_nu a b| ≤ 4 * (3 / 4 : ℝ) ^ N := by
  have h := pb_nu_second hab p q
  have hB := pb_B_pos a b
  have hBr : (0 : ℝ) < pb_B a b := by exact_mod_cast hB
  set I := ∫ x, x p * x q ∂pb_nu a b
  have hG0 := pb_Gam_nonneg p q
  have hG1 := pb_Gam_le p q
  have h34 : (3 / 4 : ℝ) ^ N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hBI : |(pb_B a b : ℝ) * I| ≤ 1 := by
    rw [abs_le] at h ⊢; constructor <;> linarith
  rw [pb_B_eq hab] at hBI hBr
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by have := pb_two_le hab; omega⟩
  simp only [Nat.add_sub_cancel, Nat.cast_pow, Nat.cast_ofNat] at hBI hBr
  rw [abs_mul, abs_of_pos hBr] at hBI
  have h1 : (1 / 2 : ℝ) ^ n ≤ (3 / 4) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h2 : (2 : ℝ) ^ n * (1 / 2) ^ n = 1 := by rw [← mul_pow]; norm_num
  have h3 : |I| ≤ (1 / 2 : ℝ) ^ n := by
    rw [← h2] at hBI
    exact le_of_mul_le_mul_left hBI hBr
  calc |I| ≤ (3 / 4 : ℝ) ^ n := h3.trans h1
    _ ≤ 4 * (3 / 4 : ℝ) ^ (n + 2) := by
        rw [pow_add]; nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 3 / 4) n]

/-- The second moments with `2^(N-2) - 1` summands. -/
theorem pb_nu_second_pred {a b : Fin N} (hab : a ≠ b) (p q : Fin 6) :
    |((pb_B a b - 1 : ℕ) : ℝ) * ∫ x, x p * x q ∂pb_nu a b - pb_Gam p q| ≤ 5 * (3 / 4 : ℝ) ^ N := by
  have h := pb_nu_second hab p q
  have hI := pb_abs_nu_second_le hab p q
  rw [Nat.cast_sub (pb_B_pos a b), Nat.cast_one]
  set I := ∫ x, x p * x q ∂pb_nu a b
  calc |((pb_B a b : ℝ) - 1) * I - pb_Gam p q| = |((pb_B a b : ℝ) * I - pb_Gam p q) - I| := by
        ring_nf
    _ ≤ |(pb_B a b : ℝ) * I - pb_Gam p q| + |I| := abs_sub _ _
    _ ≤ (3 / 4 : ℝ) ^ N / 2 + 4 * (3 / 4 : ℝ) ^ N := add_le_add h hI
    _ ≤ 5 * (3 / 4 : ℝ) ^ N := by nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 3 / 4) N]

/-! ### Third moments -/

lemma pb_sum_abs_F_le (a b : Fin N) (y : PbPat → Fin N → ℝ) :
    ∑ p, |pb_F a b y p| ≤ 6 * (pb_W y / sigN N) := by
  calc ∑ p, |pb_F a b y p| ≤ ∑ _p : Fin 6, pb_W y / sigN N :=
        sum_le_sum fun p _ => pb_abs_F_le a b y p
    _ = 6 * (pb_W y / sigN N) := by simp

/-- The third moment of the total row product of `K` iid rows. -/
lemma pb_integral_W3 {K : Type*} [Fintype K] :
    ∫ y, pb_W y ^ 3 ∂(Measure.pi fun _ : K => rowM N) ≤
      (Fintype.card K : ℝ) ^ 3 * (1 / 4 : ℝ) ^ N := by
  set μ := Measure.pi fun _ : K => rowM N
  have hP3 : ∀ u : K, ∫ y, pb_P y u ^ 3 ∂μ = (1 / 4 : ℝ) ^ N := by
    intro u
    have h := integral_pi_eval (I := K) (rowM N)
      (g := fun v : Fin N → ℝ => (∏ j, clamp01 (v j)) ^ 3)
      (measurable_rowPw.pow_const 3).aestronglyMeasurable u
    simp only [μ, pb_P]
    rw [h, integral_rowP_pow' 3]
    norm_num
  have hIP : ∀ u : K, Integrable (fun y => pb_P y u ^ 3) μ := fun u =>
    Integrable.of_bound ((pb_measurable_P u).pow_const 3).aestronglyMeasurable 1
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (pb_P_nonneg y u) 3)]
        exact pow_le_one₀ (pb_P_nonneg y u) (pb_P_le_one y u))
  have hpt : ∀ y : K → Fin N → ℝ, pb_W y ^ 3 ≤ (Fintype.card K : ℝ) ^ 2 * ∑ u, pb_P y u ^ 3 := by
    intro y
    rcases Nat.eq_zero_or_pos (Fintype.card K) with h0 | h0
    · have : IsEmpty K := Fintype.card_eq_zero_iff.1 h0
      simp [pb_W]
    have hc : (0 : ℝ) < (Fintype.card K : ℝ) ^ 2 := by positivity
    have := pow_sum_div_card_le_sum_pow (s := (univ : Finset K)) (f := fun u => pb_P y u)
      (fun u _ => pb_P_nonneg y u) 2
    rw [card_univ, div_le_iff₀ hc] at this
    unfold pb_W; norm_num at this; linarith
  calc ∫ y, pb_W y ^ 3 ∂μ ≤ ∫ y, (Fintype.card K : ℝ) ^ 2 * ∑ u, pb_P y u ^ 3 ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun y => pow_nonneg (pb_W_nonneg y) 3)
          ((integrable_finsetSum _ fun u _ => hIP u).const_mul _) (ae_of_all _ hpt)
    _ = (Fintype.card K : ℝ) ^ 3 * (1 / 4 : ℝ) ^ N := by
        rw [integral_const_mul, integral_finsetSum _ fun u _ => hIP u]
        simp only [hP3, sum_const, card_univ, nsmul_eq_mul]
        ring

/-- `(1/2)^N / σ_N^3 ≤ (23/25)^N`. -/
lemma pb_half_div_sig3 (N : ℕ) : (1 / 2 : ℝ) ^ N / sigN N ^ 3 ≤ (23 / 25 : ℝ) ^ N := by
  have hs := sigN_pos N
  have hs2 := pb_sigN_sq N
  rw [div_le_iff₀ (by positivity)]
  have hY : 0 ≤ (23 / 25 : ℝ) ^ N * sigN N ^ 3 := by positivity
  refine (pow_le_pow_iff_left₀ (by positivity) hY two_ne_zero).1 ?_
  have e1 : ((1 / 2 : ℝ) ^ N) ^ 2 = (1 / 4 : ℝ) ^ N := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e2 : ((23 / 25 : ℝ) ^ N * sigN N ^ 3) ^ 2 =
      (23 / 25 * (23 / 25) * ((2 / 3) * (2 / 3) * (2 / 3)) : ℝ) ^ N := by
    have : (sigN N ^ 3) ^ 2 = (sigN N ^ 2) ^ 3 := by ring
    rw [mul_pow, this, hs2, ← pow_mul, ← pow_mul, mul_pow, mul_pow, mul_pow, mul_pow]
    ring
  rw [e1, e2]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) N

lemma pb_measurable_abs3 : Measurable fun x : Fin 6 → ℝ => (∑ p, |x p|) ^ 3 :=
  (Finset.measurable_sum _ fun p _ => (measurable_pi_apply p).abs).pow_const 3

lemma pb_integral_nu3 (a b : Fin N) :
    ∫ x, (∑ p, |x p|) ^ 3 ∂pb_nu a b = ∫ y, (∑ p, |pb_F a b y p|) ^ 3 ∂pb_blkM N :=
  pb_integral_nu (g := fun x => (∑ p, |x p|) ^ 3) pb_measurable_abs3

lemma pb_W_le_four (y : PbPat → Fin N → ℝ) : pb_W y ≤ 4 := by
  have := pb_W_le y
  simp only [Fintype.card_prod, Fintype.card_bool] at this
  norm_num at this
  exact this

/-- Integrability of the third absolute moment of `pb_nu`. -/
theorem pb_nu_integrable3 (a b : Fin N) :
    Integrable (fun x => (∑ p, |x p|) ^ 3) (pb_nu a b) := by
  rw [pb_nu, integrable_map_measure pb_measurable_abs3.aestronglyMeasurable
    (pb_measurable_F a b).aemeasurable]
  refine Integrable.of_bound (pb_measurable_abs3.comp (pb_measurable_F a b)).aestronglyMeasurable
    ((6 * (4 / sigN N)) ^ 3) (ae_of_all _ fun y => ?_)
  have hs := sigN_pos N
  have h1 := pb_sum_abs_F_le a b y
  have h2 := pb_W_le_four y
  have h0 : 0 ≤ ∑ p, |pb_F a b y p| := sum_nonneg fun p _ => abs_nonneg _
  simp only [Function.comp, Real.norm_eq_abs]
  rw [abs_of_nonneg (pow_nonneg h0 3)]
  refine pow_le_pow_left₀ h0 (h1.trans ?_) 3
  gcongr

/-- **Third moments** of the block law: `2^(N-2) ∫ (∑ |x p|)^3 dν ≤ 3456 (23/25)^N`. -/
theorem pb_nu_third {a b : Fin N} (hab : a ≠ b) :
    (pb_B a b : ℝ) * ∫ x, (∑ p, |x p|) ^ 3 ∂pb_nu a b ≤ 3456 * (23 / 25 : ℝ) ^ N := by
  have hs := sigN_pos N
  have hW3 := pb_integral_W3 (N := N) (K := PbPat)
  simp only [Fintype.card_prod, Fintype.card_bool] at hW3
  have hIW : Integrable (fun y : PbPat → Fin N → ℝ => pb_W y ^ 3) (pb_blkM N) :=
    Integrable.of_bound (pb_measurable_W.pow_const 3).aestronglyMeasurable (4 ^ 3)
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (pb_W_nonneg y) 3)]
        exact pow_le_pow_left₀ (pb_W_nonneg y) (pb_W_le_four y) 3)
  have hbd : ∫ y, (∑ p, |pb_F a b y p|) ^ 3 ∂pb_blkM N ≤
      216 / sigN N ^ 3 * (64 * (1 / 4 : ℝ) ^ N) := by
    calc ∫ y, (∑ p, |pb_F a b y p|) ^ 3 ∂pb_blkM N
        ≤ ∫ y, 216 / sigN N ^ 3 * pb_W y ^ 3 ∂pb_blkM N := by
          refine integral_mono_of_nonneg (ae_of_all _ fun y =>
            pow_nonneg (sum_nonneg fun p _ => abs_nonneg _) 3) (hIW.const_mul _)
            (ae_of_all _ fun y => ?_)
          have h1 := pb_sum_abs_F_le a b y
          calc (∑ p, |pb_F a b y p|) ^ 3 ≤ (6 * (pb_W y / sigN N)) ^ 3 :=
                pow_le_pow_left₀ (sum_nonneg fun p _ => abs_nonneg _) h1 3
            _ = 216 / sigN N ^ 3 * pb_W y ^ 3 := by field_simp; ring
      _ = 216 / sigN N ^ 3 * ∫ y, pb_W y ^ 3 ∂pb_blkM N := integral_const_mul _ _
      _ ≤ 216 / sigN N ^ 3 * (64 * (1 / 4 : ℝ) ^ N) := by
          gcongr
          unfold pb_blkM; norm_num at hW3 ⊢; linarith
  rw [pb_integral_nu3]
  have hB4 : (pb_B a b : ℝ) * 4 = 2 ^ N := by
    rw [pb_B_eq hab]
    have := pb_two_le hab
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  have hh := pb_half_div_sig3 N
  have hBp : (0 : ℝ) ≤ pb_B a b := Nat.cast_nonneg _
  calc (pb_B a b : ℝ) * ∫ y, (∑ p, |pb_F a b y p|) ^ 3 ∂pb_blkM N
      ≤ (pb_B a b : ℝ) * (216 / sigN N ^ 3 * (64 * (1 / 4 : ℝ) ^ N)) := by gcongr
    _ = 3456 * ((1 / 2 : ℝ) ^ N / sigN N ^ 3) := by
        have e : (2 : ℝ) ^ N * (1 / 4) ^ N = (1 / 2) ^ N := by rw [← mul_pow]; norm_num
        rw [← e, ← hB4]
        field_simp
        ring
    _ ≤ 3456 * (23 / 25 : ℝ) ^ N := by gcongr

/-! ### Removing the block of a state -/

lemma pb_card_ne {α : Type*} [Fintype α] [DecidableEq α] (x : α) :
    Fintype.card {y : α // y ≠ x} = Fintype.card α - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- Enumeration of the blocks other than the block of `s`. -/
def pb_er (a b : Fin N) (s : State N) :
    Fin (pb_B a b - 1) ≃ {β : PbBlk a b // β ≠ pb_blk a b s} :=
  (Fintype.equivFinOfCardEq (pb_card_ne (pb_blk a b s))).symm

/-- The summands of the blocks other than the block of `s`. -/
def pb_Xr (a b : Fin N) (s : State N) (w : Param N) : Fin (pb_B a b - 1) → Fin 6 → ℝ :=
  fun k => pb_X a b (pb_er a b s k).1 w

lemma pb_measurable_Xr (a b : Fin N) (s : State N) : Measurable (pb_Xr a b s) :=
  Measurable.of_eval fun _ => pb_measurable_X a b _

/-- **Law of the remaining summands**: iid with law `pb_nu a b`. -/
theorem pb_map_Xr {a b : Fin N} (hab : a ≠ b) (s : State N) :
    (cubeM N).map (pb_Xr a b s) = Measure.pi fun _ : Fin (pb_B a b - 1) => pb_nu a b := by
  have hc : pb_Xr a b s = (fun (x : PbBlk a b → Fin 6 → ℝ) k => x (pb_er a b s k).1) ∘
      fun w (β : PbBlk a b) => pb_X a b β w := rfl
  rw [hc, ← Measure.map_map (Measurable.of_eval fun k => measurable_pi_apply _)
    (Measurable.of_eval fun β => pb_measurable_X a b β), pb_map_X hab]
  exact map_comp_inj _ (Subtype.val_injective.comp (pb_er a b s).injective) _

/-- `η` is the sum of the remaining summands plus the summand of the block of `s`. -/
theorem pb_eta_eq_rest {a b : Fin N} (hab : a ≠ b) (s : State N) (w : Param N) :
    pb_eta w a b = ∑ k, pb_Xr a b s w k + pb_X a b (pb_blk a b s) w := by
  rw [pb_eta_eq_sum_blk hab, Fintype.sum_eq_add_sum_compl (pb_blk a b s), add_comm]
  congr 1
  rw [Finset.sum_subtype ({pb_blk a b s}ᶜ : Finset (PbBlk a b))
    (p := fun β => β ≠ pb_blk a b s) (by simp), ← (pb_er a b s).sum_comp]
  rfl

/-- On `g2` every row product is at most `tauN N`. -/
lemma pb_Pw_le_tau {w : Param N} (i : Fin N) (h2 : ∀ i r, Qw w i r ≤ tauN N) (r : State N) :
    Pw w r ≤ tauN N := by
  have h := h2 i r
  have hq := Qw_nonneg w i r
  have hc := clamp01_le_one (w r i)
  have hc0 := clamp01_nonneg (w r i)
  rw [Pw_eq_mul_Qw w i r]; nlinarith

/-- A block summand whose four row products are at most `τ` is at most `4 τ / σ_N`. -/
lemma pb_abs_F_le_tau (a b : Fin N) {y : PbPat → Fin N → ℝ} {τ : ℝ} (hy : ∀ u, pb_P y u ≤ τ)
    (p : Fin 6) : |pb_F a b y p| ≤ 4 * τ / sigN N := by
  have hs := sigN_pos N
  refine (pb_abs_F_le a b _ p).trans ?_
  rw [div_le_div_iff_of_pos_right hs]
  calc pb_W y ≤ ∑ _u : PbPat, τ := sum_le_sum fun u _ => hy u
    _ = 4 * τ := by simp

/-- On `g2` each block summand is at most `4 tauN N / sigN N` in every coordinate. -/
lemma pb_abs_X_le {a b : Fin N} {w : Param N} (h2 : ∀ i r, Qw w i r ≤ tauN N)
    (β : PbBlk a b) (p : Fin 6) : |pb_X a b β w p| ≤ 4 * tauN N / sigN N :=
  pb_abs_F_le_tau a b (fun _ => pb_Pw_le_tau a h2 _) p

/-- **Removing the block of `s`** changes every coordinate of `η` by at most `4 τ_N / σ_N` on `g2`. -/
theorem pb_abs_eta_sub_le {a b : Fin N} (hab : a ≠ b) (s : State N) {w : Param N}
    (h2 : ∀ i r, Qw w i r ≤ tauN N) (p : Fin 6) :
    |pb_eta w a b p - (∑ k, pb_Xr a b s w k) p| ≤ 4 * tauN N / sigN N := by
  rw [pb_eta_eq_rest hab s w, Pi.add_apply, add_sub_cancel_left]
  exact pb_abs_X_le h2 _ p

/-- The rows of the block of `s`, as a random element. -/
def pb_blockRows (a b : Fin N) (s : State N) (w : Param N) : PbPat → Fin N → ℝ :=
  fun t => w (pb_row a b (pb_blk a b s) t)

lemma pb_measurable_blockRows (a b : Fin N) (s : State N) : Measurable (pb_blockRows a b s) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- **Independence**: the remaining summands are independent of the rows of the block of `s`. -/
theorem pb_indep_rest (a b : Fin N) (s : State N) :
    IndepFun (pb_blockRows a b s) (pb_Xr a b s) (cubeM N) := by
  have hI : iIndepFun (fun r (w : Param N) => w r) (cubeM N) :=
    iIndepFun_rows (fun _ v => v) fun _ => measurable_id
  set Sr := univ.filter fun r : State N => pb_blk a b r = pb_blk a b s
  set Tr := univ.filter fun r : State N => pb_blk a b r ≠ pb_blk a b s
  have hST : Disjoint Sr Tr := by
    rw [Finset.disjoint_filter]; intro r _ h h'; exact h' h
  have h := hI.indepFun_finset Sr Tr hST fun r => measurable_pi_apply r
  have hS : ∀ t, pb_row a b (pb_blk a b s) t ∈ Sr := fun t => by
    simp [Sr, pb_blk_row]
  have hT : ∀ k u, pb_row a b (pb_er a b s k).1 u ∈ Tr := fun k u => by
    simp only [Tr, mem_filter, mem_univ, true_and, pb_blk_row]
    exact (pb_er a b s k).2
  let φ : (Sr → Fin N → ℝ) → PbPat → Fin N → ℝ := fun x t => x ⟨_, hS t⟩
  let ψ : (Tr → Fin N → ℝ) → Fin (pb_B a b - 1) → Fin 6 → ℝ :=
    fun x k => pb_F a b fun u => x ⟨_, hT k u⟩
  have hφ : Measurable φ := Measurable.of_eval fun _ => measurable_pi_apply _
  have hψ : Measurable ψ := Measurable.of_eval fun _ =>
    (pb_measurable_F a b).comp (Measurable.of_eval fun _ => measurable_pi_apply _)
  exact h.comp hφ hψ

end

end Census
end IIT
