/-
Census of complexes, B1 development, module A10 (`B1-W4-B5.md`, Sections 2-3, and the W4 entry of
`B1-BLUEPRINT-AMEND.md`): the two-row replacement coupling and the deterministic transfer bounds.

Notation (flipped coordinates, as in `BigPhiStats`): `w = flipP s z`, `y_{r,i} = clamp01 (w r i)`.
`A` is a set of fixed rows (in W4, `A = {tc, s}`), `AgreeOff A w w̃` says that `w` and `w̃` agree off
`A`; `H = Σ_{a ∈ A} Pw w a` (for `A = {tc, s}`: `≤ Pw w tc + Pw w s`), `τ = tauN N`.

Contents.
0. New definitions of W4 Section 2: `AgreeOff`, `colMean`, `colMeanPlus`, `blockP`, and `blockPo`
   (`blockP°` of TR5: the block mass without the rows of `A`).
1. **Lemma CPL** (measure level).  With `νA = rowsInM A`, `νB = rowsOutM A` and the row gluing
   `glueRows A` of `B1Prod`:
   (a) `cpl_split`: `cubeM N = (νA ⊗ νB).map (glue ∘ uncurry)`;
   (b) `gFail A E v = νA {ξ | glueRows A ξ v ∉ E}` is measurable (`measurable_gFail`),
       `∫⁻ gFail dνB = cubeM N Eᶜ` (`lintegral_gFail`), hence `νB {gFail = 1} ≤ cubeM N Eᶜ`
       (`rowsOutM_gFail_eq_one_le`);
   (c) `gFail A E v < 1 → ∃ ξ, glueRows A ξ v ∈ E` (`exists_glueRows_mem`);
   and the form used downstream, `cpl_transfer`: if `Φ w` follows from `∃ w̃ ∈ E, AgreeOff A w w̃`,
   then `νB {v | ¬ Φ (glueRows A f v)} ≤ cubeM N Eᶜ` for every value `f` of the fixed rows
   (no measurability of `Φ` is needed).
2. **Lemma TR** (deterministic).  General `A` first, then the W4 forms for `A = {tc, s}` with the W4
   constants:
   (TR0) `tr0_split`; (TR1) `Zs_sub_eq`, `Zs_le_add`, `sub_le_Zs`, `tr1`;
   (TR2) `tr2_exact` (the exact form "for A8"), `tr2_abs`, `tr2`, `tr2_goodW`;
   (TR3) `tr3_core`, `tr3`, `tr3_goodW`; (TR4) `tr4`, `tr4_eq`, `tr4_pair`, plus the heavy-pattern
   facts `colMean_le_colMeanPlus`, `colMeanPlus_congr`, `colMean_congr_agree`;
   (TR5) `blockPo_congr`, `blockPo_le_blockP`, `blockP_sub_le_blockPo`, `tr5`.
   The elementary identities (I1) `meanW_eq_colMean`, (I2) `Num_S_eq_sum_blockP` (re-indexing
   `sum_merge_mul_eq`) and the B5-a decomposition `Num_S_eq_blockPo`.
3. (I3) `sysBackCause_eq_Num`: on the open cube,
   `sysBackCause = 2^(N-k) Π_{i∈S} Num w S S t i / Σ_{t'} Π_{i∈S} Num w S S t' i`.
4. (I4) the positive-part log lemmas `pos_logb_div_le_pos` and `pos_logb_div_le_logb`.
5. `measurableSet_goodW` (`MeasurableSet {w | GoodW N s w}`), with measurability of `Xk`, `DQ`,
   `qW`, `Mrow`, `colMean`, `colMeanPlus`, `blockP`.
6. `eventually_N_dlev`: the bound `N · dlev N k ≤ 1/100` of `eventually_levels`, exported; and
   `eventually_N_tau_Mk`: `N · (2τ + 2 Mk N k) ≤ 1/200` (the rest of W4's EV1).

Deviations from W4 (all minimal; no W4 statement was found false):
* TR2/TR3 are proved in a sharper form: the fixed-row block term is `Σ_{a∈A} blockQ w̃ i S a`
  (not `|A| · max_a`), and in TR3 its coefficient is `1 + 2^{1-k}` (W4: `2 (1 + 2^{2-k}) max_a`).
  The W4 constants are recovered in `tr2`, `tr2_goodW`, `tr3`, `tr3_goodW`; `2^{1-k}`, `2^{2-k}` are
  written `2 / 2^k`, `4 / 2^k`.  In `tr2` the term `2^{1-(k-|Y|)} max_a blockQ` is written
  `(blockQ w̃ i S tc + blockQ w̃ i S s) / 2^(k-|Y|)` (smaller or equal).
* W4 writes `H := Pw tc + Pw s` assuming `tc ≠ s`; the pair statements hold for all `tc, s`
  (for `tc = s` the set `{tc, s}` is `{tc}`).
* "g2 for w̃ gives `P̃_a ≤ τ`" holds for every `N` (`Pw_le_tauN_of_g2`; for `N = 0`, `Pw = 1 ≤ e^{2/9}`).
* (I3) is stated on the open cube (it needs `Zs > 0` and a positive normaliser).
* `eventually_N_dlev` asks `1 ≤ k` (as `eventually_levels`, which asks `2 ≤ k`): for `k = 0` the
  hypothesis `k ≤ K2N N` does not give `k + 4 log₂ N + 16 ≤ N`.
* CPL's `g_E` is `ENNReal`-valued (`gFail`), the natural type of `νA`-probabilities.
-/
import IIT.Census.B1Prod
import IIT.Census.BigPhiDet
import IIT.Census.BigPhiProbCond

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

noncomputable section

variable {N : ℕ}

/-! ## 0. Definitions (W4, Section 2) -/

/-- `w` and `w'` agree off the row set `A`. -/
def AgreeOff (A : Finset (State N)) (w w' : Param N) : Prop := ∀ r, r ∉ A → w r = w' r

/-- Mean of column `i` over the subcube `agree M m` (dimension `N - |M|`). -/
def colMean (w : Param N) (M : Finset (Fin N)) (m : State N) (i : Fin N) : ℝ :=
  (∑ r ∈ agree M m, clamp01 (w r i)) / (2 : ℝ) ^ (N - M.card)

/-- The same mean with the entry of row `a` replaced by `1`. -/
def colMeanPlus (w : Param N) (M : Finset (Fin N)) (a : State N) (i : Fin N) : ℝ :=
  (1 + ∑ r ∈ (agree M a).erase a, clamp01 (w r i)) / (2 : ℝ) ^ (N - M.card)

/-- `Pw`-mass of the `S`-block of `r` (the `2^|S|` rows agreeing with `r` off `S`). -/
def blockP (w : Param N) (S : Finset (Fin N)) (r : State N) : ℝ := ∑ r' ∈ agree Sᶜ r, Pw w r'

/-- `blockP°` of TR5: the `Pw`-mass of the `S`-block of `r` without the rows of `A`. -/
def blockPo (A : Finset (State N)) (w : Param N) (S : Finset (Fin N)) (r : State N) : ℝ :=
  ∑ v ∈ (agree Sᶜ r).filter (fun v => v ∉ A), Pw w v

/-! ## 1. Lemma CPL: the replacement coupling -/

section CPL

variable (A : Finset (State N))

/-- Two gluings with the same rows off `A` agree off `A`. -/
lemma agreeOff_glueRows (f f' : A → Fin N → ℝ) (v : {r // r ∉ A} → Fin N → ℝ) :
    AgreeOff A (glueRows A f v) (glueRows A f' v) := fun r hr => by
  rw [glueRows_of_not_mem A f v hr, glueRows_of_not_mem A f' v hr]

/-- **CPL (a).** `cubeM N` is the image of `νA ⊗ νB` under the row gluing. -/
theorem cpl_split :
    cubeM N = ((rowsInM A).prod (rowsOutM A)).map (fun p => glueRows A p.1 p.2) :=
  (mp_glueRows A).map_eq.symm

/-- The averaged failure function `g_E(v) = νA {ξ | glue ξ v ∉ E}`. -/
def gFail (E : Set (Param N)) (v : {r // r ∉ A} → Fin N → ℝ) : ENNReal :=
  rowsInM A {ξ | glueRows A ξ v ∉ E}

lemma gFail_le_one (E : Set (Param N)) (v : {r // r ∉ A} → Fin N → ℝ) : gFail A E v ≤ 1 :=
  prob_le_one

/-- **CPL (b), measurability.** -/
lemma measurable_gFail {E : Set (Param N)} (hE : MeasurableSet E) : Measurable (gFail A E) :=
  measurable_measure_prodMk_right ((measurable_glueRows A) hE.compl)

/-- **CPL (b).** `∫⁻ g_E dνB = cubeM N Eᶜ`. -/
theorem lintegral_gFail {E : Set (Param N)} (hE : MeasurableSet E) :
    ∫⁻ v, gFail A E v ∂rowsOutM A = cubeM N Eᶜ := by
  rw [← (mp_glueRows A).measure_preimage hE.compl.nullMeasurableSet,
    Measure.prod_apply_symm ((measurable_glueRows A) hE.compl)]
  rfl

/-- **CPL (b), Markov.** `νB {g_E = 1} ≤ cubeM N Eᶜ`. -/
theorem rowsOutM_gFail_eq_one_le {E : Set (Param N)} (hE : MeasurableSet E) :
    rowsOutM A {v | gFail A E v = 1} ≤ cubeM N Eᶜ := by
  rw [← lintegral_gFail A hE]
  calc rowsOutM A {v | gFail A E v = 1} ≤ rowsOutM A {v | 1 ≤ gFail A E v} :=
        measure_mono fun v hv => le_of_eq (Eq.symm hv)
    _ = 1 * rowsOutM A {v | 1 ≤ gFail A E v} := (one_mul _).symm
    _ ≤ ∫⁻ v, gFail A E v ∂rowsOutM A := mul_meas_ge_le_lintegral (measurable_gFail A hE) 1

/-- **CPL (c).** If `g_E v < 1`, some gluing with the rows `v` off `A` lies in `E`. -/
theorem exists_glueRows_mem {E : Set (Param N)} {v : {r // r ∉ A} → Fin N → ℝ}
    (h : gFail A E v < 1) : ∃ ξ, glueRows A ξ v ∈ E := by
  by_contra hne
  push Not at hne
  have hu : {ξ | glueRows A ξ v ∉ E} = Set.univ := Set.eq_univ_of_forall hne
  rw [gFail, hu, measure_univ] at h
  exact lt_irrefl _ h

/-- **CPL, the transfer form.**  Fix the rows `f` of `A`.  If a property `Φ` of `w` follows from
the existence of `w̃ ∈ E` agreeing with `w` off `A`, then the rows off `A` for which `Φ` fails have
`νB`-(outer) measure at most `cubeM N Eᶜ`. -/
theorem cpl_transfer (f : A → Fin N → ℝ) {E : Set (Param N)} (hE : MeasurableSet E)
    {Φ : Param N → Prop} (hΦ : ∀ w w', AgreeOff A w w' → w' ∈ E → Φ w) :
    rowsOutM A {v | ¬ Φ (glueRows A f v)} ≤ cubeM N Eᶜ := by
  refine le_trans (measure_mono fun v hv => ?_) (rowsOutM_gFail_eq_one_le A hE)
  by_contra hne
  obtain ⟨ξ, hξ⟩ := exists_glueRows_mem A (lt_of_le_of_ne (gFail_le_one A E v) hne)
  exact hv (hΦ _ _ (agreeOff_glueRows A f ξ v) hξ)

end CPL

/-! ## 2. Lemma TR: deterministic transfers from `w̃` to `w` -/

section Basic

lemma Pw_le_Qw (w : Param N) (i : Fin N) (r : State N) : Pw w r ≤ Qw w i r := by
  rw [Pw_eq_mul_Qw w i r]
  exact mul_le_of_le_one_left (Qw_nonneg w i r) (clamp01_le_one _)

/-- g2 gives `Pw ≤ τ` (for every `N`; for `N = 0`, `Pw = 1 ≤ e^{2/9} = τ`). -/
lemma Pw_le_tauN_of_g2 {w : Param N} (h : ∀ i r, Qw w i r ≤ tauN N) (r : State N) :
    Pw w r ≤ tauN N := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h1 : Pw w r = 1 := by simp [Pw]
    rw [h1, tauN]
    exact Real.one_le_exp (by norm_num)
  · exact (Pw_le_Qw w ⟨0, hN⟩ r).trans (h _ r)

lemma blockP_nonneg (w : Param N) (S : Finset (Fin N)) (r : State N) : 0 ≤ blockP w S r :=
  sum_nonneg fun v _ => Pw_nonneg w v

lemma blockP_le_blockQ (w : Param N) (i : Fin N) (S : Finset (Fin N)) (r : State N) :
    blockP w S r ≤ blockQ w i S r :=
  sum_le_sum fun v _ => Pw_le_Qw w i v

lemma blockPo_nonneg (A : Finset (State N)) (w : Param N) (S : Finset (Fin N)) (r : State N) :
    0 ≤ blockPo A w S r :=
  sum_nonneg fun v _ => Pw_nonneg w v

lemma colMean_nonneg (w : Param N) (M : Finset (Fin N)) (m : State N) (i : Fin N) :
    0 ≤ colMean w M m i :=
  div_nonneg (sum_nonneg fun _ _ => clamp01_nonneg _) (by positivity)

lemma colMean_le_one (w : Param N) (M : Finset (Fin N)) (m : State N) (i : Fin N) :
    colMean w M m i ≤ 1 := by
  unfold colMean
  rw [div_le_one (by positivity)]
  calc ∑ r ∈ agree M m, clamp01 (w r i) ≤ ∑ r ∈ agree M m, (1 : ℝ) :=
        sum_le_sum fun r _ => clamp01_le_one _
    _ = (2 : ℝ) ^ (N - M.card) := by
        rw [sum_const, card_agree, nsmul_eq_mul, mul_one]; push_cast; rfl

lemma card_union_compl {S Y : Finset (Fin N)} (hY : Y ⊆ S) :
    (Y ∪ Sᶜ).card = Y.card + (N - S.card) := by
  rw [card_union_of_disjoint (disjoint_compl_of_subset hY), card_compl, Fintype.card_fin]

/-- **(I1)** `meanW` is a column mean over the subcube `agree (Y ∪ Sᶜ) (merge S t v)`. -/
theorem meanW_eq_colMean (w : Param N) {S Y : Finset (Fin N)} (hY : Y ⊆ S) (t : State N)
    (i : Fin N) (v : State N) :
    meanW w S Y t i v = colMean w (Y ∪ Sᶜ) (merge S t v) i := by
  unfold meanW colMean
  have h1 : Y.card ≤ S.card := card_le_card hY
  have h2 : S.card ≤ N := card_le_N S
  rw [card_union_compl hY]
  congr 2
  omega

lemma meanW_le_one (w : Param N) {S Y : Finset (Fin N)} (hY : Y ⊆ S) (t : State N) (i : Fin N)
    (v : State N) : meanW w S Y t i v ≤ 1 := by
  rw [meanW_eq_colMean w hY]; exact colMean_le_one _ _ _ _

lemma agree_univ_eq (m : State N) : agree univ m = {m} := by
  ext r
  simp [mem_agree, funext_iff]

/-- For `Y = S` the mean is the single entry of the row `merge S t v`. -/
lemma meanW_S_eq (w : Param N) (S : Finset (Fin N)) (t : State N) (i : Fin N) (v : State N) :
    meanW w S S t i v = clamp01 (w (merge S t v) i) := by
  unfold meanW
  rw [union_compl, agree_univ_eq, sum_singleton, Nat.sub_self, pow_zero, div_one]

/-- **Re-indexing** (I2): `Σ_v F(merge S t v) p(v) = Σ_{r ∈ agree S t} F(r) Σ_{v ∈ agree Sᶜ r} p(v)`. -/
lemma sum_merge_mul_eq (S : Finset (Fin N)) (t : State N) (F P : State N → ℝ) :
    ∑ v, F (merge S t v) * P v = ∑ r ∈ agree S t, F r * ∑ v ∈ agree Sᶜ r, P v := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := agree S t) (g := merge S t)
    (fun v _ => mem_agree.2 fun j hj => merge_mem hj)]
  refine sum_congr rfl fun r hr => ?_
  have hset : univ.filter (fun v => merge S t v = r) = agree Sᶜ r := by
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_agree, mem_compl]
    constructor
    · rintro rfl j hj; exact (merge_not_mem hj).symm
    · intro H
      funext j
      by_cases hj : j ∈ S
      · rw [merge_mem hj]; exact ((mem_agree.1 hr) j hj).symm
      · rw [merge_not_mem hj]; exact H j hj
  have e : ∀ v ∈ univ.filter (fun v => merge S t v = r), F (merge S t v) * P v = F r * P v :=
    fun v hv => by rw [(mem_filter.1 hv).2]
  rw [sum_congr rfl e, ← mul_sum, hset]

/-- **(I2)** `Num w S S t i = Σ_{r ∈ agree S t} y_{r,i} blockP w S r`. -/
theorem Num_S_eq_sum_blockP (w : Param N) (S : Finset (Fin N)) (t : State N) (i : Fin N) :
    Num w S S t i = ∑ r ∈ agree S t, clamp01 (w r i) * blockP w S r := by
  unfold Num
  simp_rw [meanW_S_eq]
  exact sum_merge_mul_eq S t (fun r => clamp01 (w r i)) (Pw w)

/-- Splitting a sum over all rows into the rows off `A` and the rows of `A`. -/
lemma sum_eq_sum_off_add (A : Finset (State N)) (g : State N → ℝ) :
    ∑ v, g v = ∑ v ∈ univ.filter (fun v => v ∉ A), g v + ∑ a ∈ A, g a := by
  rw [← sum_filter_add_sum_filter_not univ (fun v => v ∉ A) g]
  congr 1
  refine sum_congr ?_ fun _ _ => rfl
  ext v; simp

/-- A sum over all rows of a function vanishing off `A` is a sum over `A`. -/
lemma sum_eq_sum_A_of_vanish (A : Finset (State N)) {g : State N → ℝ}
    (hg : ∀ v, v ∉ A → g v = 0) : ∑ v, g v = ∑ a ∈ A, g a :=
  (sum_subset (subset_univ A) fun v _ hv => hg v hv).symm

lemma sum_pair_le {g : State N → ℝ} (hg : ∀ r, 0 ≤ g r) (a b : State N) :
    ∑ r ∈ ({a, b} : Finset (State N)), g r ≤ g a + g b := by
  by_cases hab : a = b
  · subst hab
    rw [insert_eq_of_mem (mem_singleton_self a), sum_singleton]
    linarith [hg a]
  · rw [sum_pair hab]

lemma sum_pair_Pw_le_tau {w : Param N} (h2 : ∀ i r, Qw w i r ≤ tauN N) (a b : State N) :
    ∑ r ∈ ({a, b} : Finset (State N)), Pw w r ≤ 2 * tauN N := by
  have := sum_pair_le (Pw_nonneg w) a b
  linarith [Pw_le_tauN_of_g2 h2 a, Pw_le_tauN_of_g2 h2 b]

end Basic

section Transfer

variable {A : Finset (State N)} {w w' : Param N}

lemma AgreeOff.symm (h : AgreeOff A w w') : AgreeOff A w' w := fun r hr => (h r hr).symm

lemma AgreeOff.Pw_eq (h : AgreeOff A w w') {v : State N} (hv : v ∉ A) : Pw w v = Pw w' v := by
  unfold Pw; rw [h v hv]

/-! ### TR0, TR1 -/

/-- **(TR0) Split.** `Σ_v F(v) Pw w v = Σ_{v∉A} F(v) Pw w̃ v + Σ_{a∈A} F(a) P_a`. -/
theorem tr0_split (h : AgreeOff A w w') (F : State N → ℝ) :
    ∑ v, F v * Pw w v =
      ∑ v ∈ univ.filter (fun v => v ∉ A), F v * Pw w' v + ∑ a ∈ A, F a * Pw w a := by
  rw [sum_eq_sum_off_add A]
  congr 1
  exact sum_congr rfl fun v hv => by rw [h.Pw_eq (mem_filter.1 hv).2]

/-- **(TR1)** `Zs w - Zs w̃ = Σ_{a∈A} (P_a - P̃_a)`. -/
theorem Zs_sub_eq (h : AgreeOff A w w') : Zs w - Zs w' = ∑ a ∈ A, (Pw w a - Pw w' a) := by
  unfold Zs
  rw [← sum_sub_distrib]
  exact sum_eq_sum_A_of_vanish A fun v hv => by rw [h.Pw_eq hv, sub_self]

theorem Zs_le_add (h : AgreeOff A w w') : Zs w ≤ Zs w' + ∑ a ∈ A, Pw w a := by
  have e := Zs_sub_eq h
  have : ∑ a ∈ A, (Pw w a - Pw w' a) ≤ ∑ a ∈ A, Pw w a :=
    sum_le_sum fun a _ => by linarith [Pw_nonneg w' a]
  linarith

theorem sub_le_Zs (h : AgreeOff A w w') : Zs w' - ∑ a ∈ A, Pw w' a ≤ Zs w := by
  have e := Zs_sub_eq h
  have : -∑ a ∈ A, Pw w' a ≤ ∑ a ∈ A, (Pw w a - Pw w' a) := by
    rw [← sum_neg_distrib]; exact sum_le_sum fun a _ => by linarith [Pw_nonneg w a]
  linarith

/-- **(TR1), W4 form.** `Zs w̃ - 2τ ≤ Zs w ≤ Zs w̃ + H`. -/
theorem tr1 {tc s : State N} (h : AgreeOff {tc, s} w w') (h2 : ∀ i r, Qw w' i r ≤ tauN N) :
    Zs w' - 2 * tauN N ≤ Zs w ∧ Zs w ≤ Zs w' + (Pw w tc + Pw w s) := by
  have h1 := sub_le_Zs h
  have h3 := Zs_le_add h
  have h4 := sum_pair_Pw_le_tau h2 tc s
  have h5 := sum_pair_le (Pw_nonneg w) tc s
  constructor <;> linarith

/-! ### Column sums over a set of rows -/

lemma sum_clamp_sub_eq (h : AgreeOff A w w') (R : Finset (State N)) (i : Fin N) :
    ∑ r ∈ R, clamp01 (w r i) - ∑ r ∈ R, clamp01 (w' r i)
      = ∑ r ∈ R.filter (· ∈ A), (clamp01 (w r i) - clamp01 (w' r i)) := by
  rw [← sum_sub_distrib, sum_filter]
  refine sum_congr rfl fun r _ => ?_
  split_ifs with hr
  · rfl
  · rw [h r hr, sub_self]

lemma abs_clamp_sub_le (x y : ℝ) : |clamp01 x - clamp01 y| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [clamp01_nonneg x, clamp01_le_one x, clamp01_nonneg y, clamp01_le_one y]

lemma abs_sum_clamp_sub_le (h : AgreeOff A w w') (R : Finset (State N)) (i : Fin N) :
    |∑ r ∈ R, clamp01 (w r i) - ∑ r ∈ R, clamp01 (w' r i)| ≤ ((R.filter (· ∈ A)).card : ℝ) := by
  rw [sum_clamp_sub_eq h]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ r ∈ R.filter (· ∈ A), |clamp01 (w r i) - clamp01 (w' r i)|
      ≤ ∑ r ∈ R.filter (· ∈ A), (1 : ℝ) := sum_le_sum fun r _ => abs_clamp_sub_le _ _
    _ = _ := by rw [sum_const, nsmul_eq_mul, mul_one]

/-! ### TR4 and the heavy-pattern means -/

/-- **(TR4)** `|colMean w M m i - colMean w̃ M m i| ≤ |A ∩ agree M m| / 2^{N-|M|}`. -/
theorem tr4 (h : AgreeOff A w w') (M : Finset (Fin N)) (m : State N) (i : Fin N) :
    |colMean w M m i - colMean w' M m i| ≤
      (((agree M m).filter (· ∈ A)).card : ℝ) / (2 : ℝ) ^ (N - M.card) := by
  unfold colMean
  rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (N - M.card))]
  gcongr
  exact abs_sum_clamp_sub_le h _ i

/-- **(TR4)** The column mean does not change if the subcube avoids `A`. -/
theorem tr4_eq (h : AgreeOff A w w') {M : Finset (Fin N)} {m : State N}
    (hd : ∀ a ∈ A, a ∉ agree M m) (i : Fin N) : colMean w M m i = colMean w' M m i := by
  have h0 : ((agree M m).filter (· ∈ A)) = ∅ :=
    filter_eq_empty_iff.2 fun r hr hrA => hd r hrA hr
  have := tr4 h M m i
  rw [h0, card_empty, Nat.cast_zero, zero_div] at this
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-- **(TR4), W4 form** (at most two changed rows). -/
theorem tr4_pair {tc s : State N} (h : AgreeOff {tc, s} w w') (M : Finset (Fin N)) (m : State N)
    (i : Fin N) : |colMean w M m i - colMean w' M m i| ≤ 2 / (2 : ℝ) ^ (N - M.card) := by
  refine (tr4 h M m i).trans ?_
  gcongr
  have : ((agree M m).filter (· ∈ ({tc, s} : Finset (State N)))).card ≤ 2 :=
    (card_le_card fun r hr => (mem_filter.1 hr).2).trans (card_insert_le _ _)
  exact_mod_cast this

/-- The mean over a subcube depends only on the subcube: `agree M m = agree M a` when `m` and `a`
agree on `M`. -/
lemma colMean_congr_agree (w : Param N) {M : Finset (Fin N)} {m a : State N}
    (hma : ∀ j ∈ M, m j = a j) (i : Fin N) : colMean w M m i = colMean w M a i := by
  have : agree M m = agree M a := by
    ext r; simp only [mem_agree]
    exact ⟨fun H j hj => (H j hj).trans (hma j hj), fun H j hj => (H j hj).trans (hma j hj).symm⟩
  unfold colMean; rw [this]

/-- The heavy row's entry is at most `1`: `colMean ≤ colMeanPlus` (B5-b). -/
lemma colMean_le_colMeanPlus (w : Param N) (M : Finset (Fin N)) (a : State N) (i : Fin N) :
    colMean w M a i ≤ colMeanPlus w M a i := by
  unfold colMean colMeanPlus
  rw [← add_sum_erase _ _ (self_mem_agree M a)]
  gcongr
  exact clamp01_le_one _

/-- `colMeanPlus` does not read row `a`; it is unchanged when the other rows of the subcube avoid
`A` (geometry (G) of B5). -/
lemma colMeanPlus_congr (h : AgreeOff A w w') {M : Finset (Fin N)} {a : State N}
    (hG : ∀ r ∈ (agree M a).erase a, r ∉ A) (i : Fin N) :
    colMeanPlus w M a i = colMeanPlus w' M a i := by
  unfold colMeanPlus
  congr 2
  exact sum_congr rfl fun r hr => by rw [h r (hG r hr)]

/-! ### TR5 -/

/-- **(TR5)** `blockP°` is the same for `w` and `w̃`. -/
theorem blockPo_congr (h : AgreeOff A w w') (S : Finset (Fin N)) (r : State N) :
    blockPo A w S r = blockPo A w' S r :=
  sum_congr rfl fun _ hv => h.Pw_eq (mem_filter.1 hv).2

theorem blockPo_le_blockP (A : Finset (State N)) (w : Param N) (S : Finset (Fin N))
    (r : State N) : blockPo A w S r ≤ blockP w S r :=
  sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun v _ _ => Pw_nonneg w v

theorem blockP_sub_le_blockPo (A : Finset (State N)) (w : Param N) (S : Finset (Fin N))
    (r : State N) : blockP w S r - ∑ a ∈ A, Pw w a ≤ blockPo A w S r := by
  have e := sum_filter_add_sum_filter_not (agree Sᶜ r) (fun v => v ∉ A) (Pw w)
  have h1 : ∑ v ∈ (agree Sᶜ r).filter (fun v => ¬ v ∉ A), Pw w v ≤ ∑ a ∈ A, Pw w a :=
    sum_le_sum_of_subset_of_nonneg (fun v hv => not_not.1 (mem_filter.1 hv).2)
      fun v _ _ => Pw_nonneg w v
  unfold blockP blockPo
  linarith

/-- **(TR5), W4 form.** `blockP w̃ S r - 2τ ≤ blockP° S r ≤ blockP w̃ S r`, and `blockP°` is the
same for `w` and `w̃`. -/
theorem tr5 {tc s : State N} (h : AgreeOff {tc, s} w w') (h2 : ∀ i r, Qw w' i r ≤ tauN N)
    (S : Finset (Fin N)) (r : State N) :
    blockP w' S r - 2 * tauN N ≤ blockPo {tc, s} w' S r ∧
      blockPo {tc, s} w' S r ≤ blockP w' S r ∧ blockPo {tc, s} w S r = blockPo {tc, s} w' S r := by
  refine ⟨?_, blockPo_le_blockP _ _ _ _, blockPo_congr h S r⟩
  have := blockP_sub_le_blockPo {tc, s} w' S r
  have := sum_pair_Pw_le_tau h2 tc s
  linarith

/-- **B5-a decomposition.** `Num w S S t i = Σ_{r ∈ agree S t} y^w_{r,i} blockP°(r)
+ Σ_{a∈A} y^w_{merge S t a, i} P_a`, with `blockP°` read on `w̃`. -/
theorem Num_S_eq_blockPo (h : AgreeOff A w w') (S : Finset (Fin N)) (t : State N) (i : Fin N) :
    Num w S S t i = ∑ r ∈ agree S t, clamp01 (w r i) * blockPo A w' S r
      + ∑ a ∈ A, clamp01 (w (merge S t a) i) * Pw w a := by
  unfold Num
  simp_rw [meanW_S_eq]
  rw [tr0_split h]
  congr 1
  have e : ∑ v ∈ univ.filter (fun v => v ∉ A), clamp01 (w (merge S t v) i) * Pw w' v
      = ∑ v, clamp01 (w (merge S t v) i) * (if v ∉ A then Pw w' v else 0) := by
    rw [sum_filter]
    refine sum_congr rfl fun v _ => ?_
    split_ifs <;> simp
  rw [e, sum_merge_mul_eq S t (fun r => clamp01 (w r i))]
  refine sum_congr rfl fun r _ => ?_
  rw [blockPo, sum_filter]

/-! ### TR2 -/

lemma mem_agree_merge_iff {S Y : Finset (Fin N)} (hY : Y ⊆ S) (t v a : State N) :
    a ∈ agree (Y ∪ Sᶜ) (merge S t v) ↔ (∀ j ∈ Y, a j = t j) ∧ v ∈ agree Sᶜ a := by
  simp only [mem_agree, mem_union]
  constructor
  · intro H
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have := H j (Or.inl hj); rwa [merge_mem (hY hj)] at this
    · have := H j (Or.inr hj); rw [merge_not_mem (mem_compl.1 hj)] at this; exact this.symm
  · rintro ⟨H1, H2⟩ j hj
    rcases hj with hj | hj
    · rw [merge_mem (hY hj)]; exact H1 j hj
    · rw [merge_not_mem (mem_compl.1 hj)]; exact (H2 j hj).symm

/-- Changing the rows of `A` changes a `meanW` by at most the number of rows of `A` whose `S`-block
contains `v`, over `2^{k-|Y|}`. -/
lemma abs_meanW_sub_le (h : AgreeOff A w w') (S Y : Finset (Fin N)) (t : State N) (i : Fin N)
    (v : State N) :
    |meanW w S Y t i v - meanW w' S Y t i v| ≤
      ((A.filter fun a => v ∈ agree Sᶜ a).card : ℝ) / (2 : ℝ) ^ (S.card - Y.card) := by
  unfold meanW
  rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (S.card - Y.card))]
  gcongr
  refine (abs_sum_clamp_sub_le h _ i).trans ?_
  have hsub : (agree (Y ∪ Sᶜ) (merge S t v)).filter (· ∈ A) ⊆ A.filter fun a => v ∈ agree Sᶜ a := by
    intro r hr
    rw [mem_filter] at hr ⊢
    refine ⟨hr.2, mem_agree.2 fun j hj => ?_⟩
    have := mem_agree.1 hr.1 j (mem_union_right _ hj)
    rw [merge_not_mem (mem_compl.1 hj)] at this
    exact this.symm
  exact_mod_cast card_le_card hsub

lemma sum_card_filter_mul (A : Finset (State N)) (S : Finset (Fin N)) (P : State N → ℝ) :
    ∑ v, ((A.filter fun a => v ∈ agree Sᶜ a).card : ℝ) * P v =
      ∑ a ∈ A, ∑ v ∈ agree Sᶜ a, P v := by
  simp_rw [natCast_card_filter, sum_mul, ite_mul, one_mul, zero_mul]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_ite_mem, univ_inter]

/-- **(TR2), general `A`.**
`|Num w S Y t i - Num w̃ S Y t i| ≤ H + H̃ + Σ_{a∈A} blockQ w̃ i S a / 2^{k-|Y|}`. -/
theorem tr2_abs (h : AgreeOff A w w') {S Y : Finset (Fin N)} (hY : Y ⊆ S) (t : State N)
    (i : Fin N) :
    |Num w S Y t i - Num w' S Y t i| ≤ ∑ a ∈ A, Pw w a + ∑ a ∈ A, Pw w' a
      + (∑ a ∈ A, blockQ w' i S a) / (2 : ℝ) ^ (S.card - Y.card) := by
  have hdec : Num w S Y t i - Num w' S Y t i =
      ∑ v, (meanW w S Y t i v - meanW w' S Y t i v) * Pw w' v
        + ∑ a ∈ A, meanW w S Y t i a * (Pw w a - Pw w' a) := by
    have e2 : ∑ v, meanW w S Y t i v * (Pw w v - Pw w' v) =
        ∑ a ∈ A, meanW w S Y t i a * (Pw w a - Pw w' a) :=
      sum_eq_sum_A_of_vanish A fun v hv => by rw [h.Pw_eq hv, sub_self, mul_zero]
    rw [← e2, ← sum_add_distrib]
    unfold Num
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun v _ => by ring
  have h1 : |∑ v, (meanW w S Y t i v - meanW w' S Y t i v) * Pw w' v| ≤
      (∑ a ∈ A, blockQ w' i S a) / (2 : ℝ) ^ (S.card - Y.card) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ v, |(meanW w S Y t i v - meanW w' S Y t i v) * Pw w' v|
        ≤ ∑ v, ((A.filter fun a => v ∈ agree Sᶜ a).card : ℝ) / (2 : ℝ) ^ (S.card - Y.card)
            * Pw w' v := by
          refine sum_le_sum fun v _ => ?_
          rw [abs_mul, abs_of_nonneg (Pw_nonneg w' v)]
          exact mul_le_mul_of_nonneg_right (abs_meanW_sub_le h S Y t i v) (Pw_nonneg w' v)
      _ = (∑ a ∈ A, blockP w' S a) / (2 : ℝ) ^ (S.card - Y.card) := by
          simp_rw [div_mul_eq_mul_div]
          rw [← sum_div, sum_card_filter_mul]
          rfl
      _ ≤ _ := by
          gcongr with a
          exact blockP_le_blockQ w' i S a
  have h2 : |∑ a ∈ A, meanW w S Y t i a * (Pw w a - Pw w' a)| ≤
      ∑ a ∈ A, Pw w a + ∑ a ∈ A, Pw w' a := by
    have hP : 0 ≤ ∑ a ∈ A, Pw w a := sum_nonneg fun a _ => Pw_nonneg w a
    have hP' : 0 ≤ ∑ a ∈ A, Pw w' a := sum_nonneg fun a _ => Pw_nonneg w' a
    rw [abs_le]
    constructor
    · have : -(∑ a ∈ A, Pw w' a) ≤ ∑ a ∈ A, meanW w S Y t i a * (Pw w a - Pw w' a) := by
        rw [← sum_neg_distrib]
        refine sum_le_sum fun a _ => ?_
        have m0 := meanW_nonneg w S Y t i a
        have m1 := meanW_le_one w hY t i a
        have p0 := Pw_nonneg w a
        have p0' := Pw_nonneg w' a
        nlinarith
      linarith
    · have : ∑ a ∈ A, meanW w S Y t i a * (Pw w a - Pw w' a) ≤ ∑ a ∈ A, Pw w a := by
        refine sum_le_sum fun a _ => ?_
        have m0 := meanW_nonneg w S Y t i a
        have m1 := meanW_le_one w hY t i a
        have p0 := Pw_nonneg w a
        have p0' := Pw_nonneg w' a
        nlinarith
      linarith
  rw [hdec]
  refine (abs_add_le _ _).trans ?_
  linarith

/-- **(TR2), W4 form.** `|Num w S Y t i - Num w̃ S Y t i| ≤ H + 2τ
+ (blockQ w̃ i S tc + blockQ w̃ i S s) / 2^{k-|Y|}` (`≤ H + 2τ + 2^{1-(k-|Y|)} max_a blockQ`). -/
theorem tr2 {tc s : State N} (h : AgreeOff {tc, s} w w') (h2 : ∀ i r, Qw w' i r ≤ tauN N)
    {S Y : Finset (Fin N)} (hY : Y ⊆ S) (t : State N) (i : Fin N) :
    |Num w S Y t i - Num w' S Y t i| ≤ (Pw w tc + Pw w s) + 2 * tauN N
      + (blockQ w' i S tc + blockQ w' i S s) / (2 : ℝ) ^ (S.card - Y.card) := by
  refine (tr2_abs h hY t i).trans ?_
  have h3 := sum_pair_le (Pw_nonneg w) tc s
  have h4 := sum_pair_Pw_le_tau h2 tc s
  have h5 : (∑ a ∈ ({tc, s} : Finset (State N)), blockQ w' i S a) / (2 : ℝ) ^ (S.card - Y.card)
      ≤ (blockQ w' i S tc + blockQ w' i S s) / (2 : ℝ) ^ (S.card - Y.card) := by
    gcongr
    exact sum_pair_le (blockQ_nonneg w' i S) tc s
  linarith

/-- **(TR2) on `GoodW w̃`.** `|Num w S Y t i - Num w̃ S Y t i| ≤ ε_k := H + 2τ + 2 Mk N k`. -/
theorem tr2_goodW {s0 tc s : State N} (h : AgreeOff {tc, s} w w') (hG : GoodW N s0 w')
    {S Y : Finset (Fin N)} (hY : Y ⊆ S) (t : State N) (i : Fin N) :
    |Num w S Y t i - Num w' S Y t i| ≤ (Pw w tc + Pw w s) + 2 * tauN N + 2 * Mk N S.card := by
  refine (tr2 h hG.g2 hY t i).trans ?_
  have hb1 := blockQ_le_Mk hG i S tc
  have hb2 := blockQ_le_Mk hG i S s
  have h0 : 0 ≤ blockQ w' i S tc + blockQ w' i S s :=
    add_nonneg (blockQ_nonneg w' i S tc) (blockQ_nonneg w' i S s)
  have hdiv : (blockQ w' i S tc + blockQ w' i S s) / (2 : ℝ) ^ (S.card - Y.card)
      ≤ blockQ w' i S tc + blockQ w' i S s :=
    div_le_self h0 (one_le_pow₀ (by norm_num))
  linarith

/-- **(TR2), exact form (for A8).** For `Y ⊆ S`,
`Num w S Y t i - Num w̃ S Y t i = Σ_{a∈A} ([a_Y = t_Y] (y^w_{a,i} - y^{w̃}_{a,i}) blockP w S a
/ 2^{k-|Y|} + meanW w̃ S Y t i a (P_a - P̃_a))`. -/
theorem tr2_exact (h : AgreeOff A w w') {S Y : Finset (Fin N)} (hY : Y ⊆ S) (t : State N)
    (i : Fin N) :
    Num w S Y t i - Num w' S Y t i =
      ∑ a ∈ A, ((if ∀ j ∈ Y, a j = t j then
          (clamp01 (w a i) - clamp01 (w' a i)) * blockP w S a else 0) / (2 : ℝ) ^ (S.card - Y.card)
        + meanW w' S Y t i a * (Pw w a - Pw w' a)) := by
  have hdec : Num w S Y t i - Num w' S Y t i =
      ∑ v, (meanW w S Y t i v - meanW w' S Y t i v) * Pw w v
        + ∑ a ∈ A, meanW w' S Y t i a * (Pw w a - Pw w' a) := by
    have e2 : ∑ v, meanW w' S Y t i v * (Pw w v - Pw w' v) =
        ∑ a ∈ A, meanW w' S Y t i a * (Pw w a - Pw w' a) :=
      sum_eq_sum_A_of_vanish A fun v hv => by rw [h.Pw_eq hv, sub_self, mul_zero]
    rw [← e2, ← sum_add_distrib]
    unfold Num
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun v _ => by ring
  -- the difference of the means, as a sum over `A`
  have hmean : ∀ v, meanW w S Y t i v - meanW w' S Y t i v =
      (∑ a ∈ A, if a ∈ agree (Y ∪ Sᶜ) (merge S t v) then
        clamp01 (w a i) - clamp01 (w' a i) else 0) / (2 : ℝ) ^ (S.card - Y.card) := by
    intro v
    unfold meanW
    rw [← sub_div, sum_clamp_sub_eq h, ← sum_filter]
    congr 2
    ext a
    simp only [mem_filter]
    exact and_comm
  have hfirst : ∑ v, (meanW w S Y t i v - meanW w' S Y t i v) * Pw w v =
      ∑ a ∈ A, (if ∀ j ∈ Y, a j = t j then
          (clamp01 (w a i) - clamp01 (w' a i)) * blockP w S a else 0) /
        (2 : ℝ) ^ (S.card - Y.card) := by
    simp_rw [hmean, div_mul_eq_mul_div, sum_mul]
    rw [← sum_div, ← sum_div, sum_comm]
    congr 1
    refine sum_congr rfl fun a _ => ?_
    split_ifs with hC
    · rw [blockP, mul_sum]
      have e : ∀ v : State N, (if a ∈ agree (Y ∪ Sᶜ) (merge S t v) then
          clamp01 (w a i) - clamp01 (w' a i) else 0) * Pw w v =
          if v ∈ agree Sᶜ a then (clamp01 (w a i) - clamp01 (w' a i)) * Pw w v else 0 := by
        intro v
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd ((mem_agree_merge_iff hY t v a).1 h1).2 h2
        · exact absurd ((mem_agree_merge_iff hY t v a).2 ⟨hC, h2⟩) h1
        · rw [zero_mul]
      rw [sum_congr rfl fun v _ => e v, sum_ite_mem, univ_inter]
    · refine sum_eq_zero fun v _ => ?_
      split_ifs with h1
      · exact absurd ((mem_agree_merge_iff hY t v a).1 h1).1 hC
      · rw [zero_mul]
  rw [hdec, hfirst, ← sum_add_distrib]

/-! ### TR3 -/

/-- **(TR3), general `A`.** For `j ∈ S`, with `k = |S|`:
`Num w S S t j - Num w S {j} t j ≤ [Num w̃ S S t j - Num w̃ S {j} t j] + (1 - 2^{1-k}) H + H̃
+ (1 + 2^{1-k}) Σ_{a∈A} blockQ w̃ j S a`. -/
theorem tr3_core (h : AgreeOff A w w') {S : Finset (Fin N)} {j : Fin N} (hj : j ∈ S)
    (t : State N) :
    Num w S S t j - Num w S {j} t j ≤ (Num w' S S t j - Num w' S {j} t j)
      + (1 - 2 / (2 : ℝ) ^ S.card) * ∑ a ∈ A, Pw w a + ∑ a ∈ A, Pw w' a
      + (1 + 2 / (2 : ℝ) ^ S.card) * ∑ a ∈ A, blockQ w' j S a := by
  have hk1 : 1 ≤ S.card := card_pos.2 ⟨j, hj⟩
  have hjS : ({j} : Finset (Fin N)) ⊆ S := singleton_subset_iff.2 hj
  have hpow : (2 : ℝ) ^ S.card = 2 * 2 ^ (S.card - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hq : 2 / (2 : ℝ) ^ S.card = 1 / 2 ^ (S.card - 1) := by
    rw [hpow]; field_simp
  have hq0 : 0 ≤ 1 / (2 : ℝ) ^ (S.card - 1) := by positivity
  have hq1 : 1 / (2 : ℝ) ^ (S.card - 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  set D : Param N → State N → ℝ := fun x v => meanW x S S t j v - meanW x S {j} t j v with hD
  have hNum : ∀ x : Param N, Num x S S t j - Num x S {j} t j = ∑ v, D x v * Pw x v := by
    intro x
    unfold Num
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun v _ => by simp only [hD]; ring
  -- the three pieces
  have hsplit : ∑ v, D w v * Pw w v = ∑ v, D w' v * Pw w' v + ∑ v, (D w v - D w' v) * Pw w' v
      + ∑ a ∈ A, D w a * Pw w a - ∑ a ∈ A, D w a * Pw w' a := by
    have e : ∑ v, D w v * (Pw w v - Pw w' v) = ∑ a ∈ A, D w a * (Pw w a - Pw w' a) :=
      sum_eq_sum_A_of_vanish A fun v hv => by rw [h.Pw_eq hv, sub_self, mul_zero]
    have e' : ∑ v, D w v * Pw w v = ∑ v, D w' v * Pw w' v + ∑ v, (D w v - D w' v) * Pw w' v
        + ∑ v, D w v * (Pw w v - Pw w' v) := by
      rw [← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun v _ => by ring
    rw [e', e, sum_congr rfl fun a _ => mul_sub (D w a) (Pw w a) (Pw w' a), sum_sub_distrib]
    ring
  -- coefficient of `P_a`
  have hDa : ∀ a, D w a ≤ 1 - 2 / (2 : ℝ) ^ S.card := by
    intro a
    simp only [hD]
    rw [meanW_S_eq]
    have hlow : clamp01 (w (merge S t a) j) / 2 ^ (S.card - 1) ≤ meanW w S {j} t j a := by
      unfold meanW
      rw [card_singleton]
      gcongr
      exact single_le_sum (fun r _ => clamp01_nonneg (w r j)) (self_mem_agree _ _)
    have hy0 := clamp01_nonneg (w (merge S t a) j)
    have hy1 := clamp01_le_one (w (merge S t a) j)
    rw [hq]
    have : clamp01 (w (merge S t a) j) / 2 ^ (S.card - 1)
        = clamp01 (w (merge S t a) j) * (1 / 2 ^ (S.card - 1)) := by ring
    rw [this] at hlow
    nlinarith
  have hDlow : ∀ x a, -1 ≤ D x a := by
    intro x a
    simp only [hD]
    linarith [meanW_nonneg x S S t j a, meanW_le_one x hjS t j a]
  have hA1 : ∑ a ∈ A, D w a * Pw w a ≤ (1 - 2 / (2 : ℝ) ^ S.card) * ∑ a ∈ A, Pw w a := by
    rw [mul_sum]
    exact sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hDa a) (Pw_nonneg w a)
  have hA2 : -∑ a ∈ A, D w a * Pw w' a ≤ ∑ a ∈ A, Pw w' a := by
    rw [← sum_neg_distrib]
    exact sum_le_sum fun a _ => by nlinarith [hDlow w a, Pw_nonneg w' a]
  -- the rows off `A`
  have hB : ∑ v, (D w v - D w' v) * Pw w' v ≤
      (1 + 2 / (2 : ℝ) ^ S.card) * ∑ a ∈ A, blockQ w' j S a := by
    have hpt : ∀ v, (D w v - D w' v) * Pw w' v ≤
        ((A.filter fun a => v ∈ agree Sᶜ a).card : ℝ) * (1 + 1 / 2 ^ (S.card - 1)) * Pw w' v := by
      intro v
      have e1 := abs_meanW_sub_le h S S t j v
      have e2 := abs_meanW_sub_le h S {j} t j v
      rw [Nat.sub_self, pow_zero, div_one] at e1
      rw [card_singleton] at e2
      have hdiff : D w v - D w' v ≤
          |meanW w S S t j v - meanW w' S S t j v| + |meanW w S {j} t j v - meanW w' S {j} t j v| := by
        simp only [hD]
        have := le_abs_self (meanW w S S t j v - meanW w' S S t j v)
        have := neg_abs_le (meanW w S {j} t j v - meanW w' S {j} t j v)
        linarith
      have hc0 : (0 : ℝ) ≤ ((A.filter fun a => v ∈ agree Sᶜ a).card : ℝ) := Nat.cast_nonneg _
      have : D w v - D w' v ≤ ((A.filter fun a => v ∈ agree Sᶜ a).card : ℝ) * (1 + 1 / 2 ^ (S.card - 1)) := by
        have : ((A.filter fun a => v ∈ agree Sᶜ a).card : ℝ) / 2 ^ (S.card - 1)
            = ((A.filter fun a => v ∈ agree Sᶜ a).card : ℝ) * (1 / 2 ^ (S.card - 1)) := by ring
        rw [this] at e2
        nlinarith
      exact mul_le_mul_of_nonneg_right this (Pw_nonneg w' v)
    calc ∑ v, (D w v - D w' v) * Pw w' v
        ≤ ∑ v, ((A.filter fun a => v ∈ agree Sᶜ a).card : ℝ) * (1 + 1 / 2 ^ (S.card - 1))
            * Pw w' v := sum_le_sum fun v _ => hpt v
      _ = (1 + 1 / 2 ^ (S.card - 1)) * ∑ a ∈ A, blockP w' S a := by
          have : ∀ v, ((A.filter fun a => v ∈ agree Sᶜ a).card : ℝ) * (1 + 1 / 2 ^ (S.card - 1))
              * Pw w' v = (1 + 1 / 2 ^ (S.card - 1))
                * (((A.filter fun a => v ∈ agree Sᶜ a).card : ℝ) * Pw w' v) := fun v => by ring
          rw [sum_congr rfl fun v _ => this v, ← mul_sum, sum_card_filter_mul]
          rfl
      _ ≤ (1 + 2 / (2 : ℝ) ^ S.card) * ∑ a ∈ A, blockQ w' j S a := by
          rw [hq]
          gcongr with a
          exact blockP_le_blockQ w' j S a
  rw [hNum w, hNum w', hsplit]
  linarith

/-- **(TR3), W4 form.** `Num w S S t j - Num w S {j} t j ≤ [Num w̃ S S t j - Num w̃ S {j} t j]
+ (1 - 2^{1-k}) H + 2τ + (1 + 2^{1-k}) (blockQ w̃ j S tc + blockQ w̃ j S s)`. -/
theorem tr3 {tc s : State N} (h : AgreeOff {tc, s} w w') (h2 : ∀ i r, Qw w' i r ≤ tauN N)
    {S : Finset (Fin N)} {j : Fin N} (hj : j ∈ S) (t : State N) :
    Num w S S t j - Num w S {j} t j ≤ (Num w' S S t j - Num w' S {j} t j)
      + (1 - 2 / (2 : ℝ) ^ S.card) * (Pw w tc + Pw w s) + 2 * tauN N
      + (1 + 2 / (2 : ℝ) ^ S.card) * (blockQ w' j S tc + blockQ w' j S s) := by
  have hk1 : 1 ≤ S.card := card_pos.2 ⟨j, hj⟩
  have hc : 0 ≤ 1 - 2 / (2 : ℝ) ^ S.card := by
    have : (2 : ℝ) ≤ 2 ^ S.card := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ S.card := pow_le_pow_right₀ (by norm_num) hk1
    rw [sub_nonneg, div_le_one (by positivity)]; exact this
  have hc' : 0 ≤ 1 + 2 / (2 : ℝ) ^ S.card := by positivity
  refine (tr3_core h hj t).trans ?_
  have h3 := mul_le_mul_of_nonneg_left (sum_pair_le (Pw_nonneg w) tc s) hc
  have h4 := sum_pair_Pw_le_tau h2 tc s
  have h5 := mul_le_mul_of_nonneg_left (sum_pair_le (blockQ_nonneg w' j S) tc s) hc'
  linarith

/-- **(TR3) on `GoodW w̃`, with the W4 constants.** `Num w S S t j - Num w S {j} t j ≤
[Num w̃ S S t j - Num w̃ S {j} t j] + (1 - 2^{1-k}) H + 2τ + 2 (1 + 2^{2-k}) Mk N k`. -/
theorem tr3_goodW {s0 tc s : State N} (h : AgreeOff {tc, s} w w') (hG : GoodW N s0 w')
    {S : Finset (Fin N)} {j : Fin N} (hj : j ∈ S) (t : State N) :
    Num w S S t j - Num w S {j} t j ≤ (Num w' S S t j - Num w' S {j} t j)
      + (1 - 2 / (2 : ℝ) ^ S.card) * (Pw w tc + Pw w s) + 2 * tauN N
      + 2 * (1 + 4 / (2 : ℝ) ^ S.card) * Mk N S.card := by
  refine (tr3 h hG.g2 hj t).trans ?_
  have hb1 := blockQ_le_Mk hG j S tc
  have hb2 := blockQ_le_Mk hG j S s
  have hM := Mk_nonneg N S.card
  have hp : (0 : ℝ) < 2 ^ S.card := by positivity
  have hc' : 0 ≤ 1 + 2 / (2 : ℝ) ^ S.card := by positivity
  have h1 : (1 + 2 / (2 : ℝ) ^ S.card) * (blockQ w' j S tc + blockQ w' j S s)
      ≤ (1 + 2 / (2 : ℝ) ^ S.card) * (2 * Mk N S.card) :=
    mul_le_mul_of_nonneg_left (by linarith) hc'
  have h2 : (1 + 2 / (2 : ℝ) ^ S.card) * (2 * Mk N S.card)
      ≤ 2 * (1 + 4 / (2 : ℝ) ^ S.card) * Mk N S.card := by
    have : 2 / (2 : ℝ) ^ S.card ≤ 4 / 2 ^ S.card := by gcongr; norm_num
    nlinarith
  linarith

end Transfer

/-! ## 3. (I3): the backward cause probability in the statistics -/

/-- **(I3)** On the open cube, `sysBackCause (tpmOf z) S s s t =
2^{N-k} Π_{i∈S} Num w S S t i / Σ_{t'} Π_{i∈S} Num w S S t' i` (the factors `Zs^{-k}` cancel). -/
theorem sysBackCause_eq_Num {z : Param N} (hz : z ∈ openCube N) (s t : State N)
    (S : Finset (Fin N)) :
    sysBackCause (tpmOf z) S s s t =
      (2 : ℝ) ^ (N - S.card) * (∏ i ∈ S, Num (flipP s z) S S t i) /
        ∑ t' : State N, ∏ i ∈ S, Num (flipP s z) S S t' i := by
  have hZ := Zs_pos hz s
  have hpos : ∀ t', 0 < ∏ i ∈ S, Num (flipP s z) S S t' i :=
    fun t' => prod_pos fun i _ => Num_pos hz s S S t' i
  have hsum : 0 < ∑ t' : State N, ∏ i ∈ S, Num (flipP s z) S S t' i :=
    sum_pos (fun t' _ => hpos t') univ_nonempty
  have hk : S.card ≤ N := card_le_N S
  have hcp : ∀ t', sysCauseProb (tpmOf z) S s s t' =
      (∏ i ∈ S, Num (flipP s z) S S t' i) / Zs (flipP s z) ^ S.card := by
    intro t'; rw [sysCauseProb_eq_Num, prod_div_distrib, prod_const]
  rw [sysBackCause, sysUncCause, avgOverStates]
  simp_rw [hcp]
  rw [← sum_div]
  have h2 : (2 : ℝ) ^ N = 2 ^ (N - S.card) * 2 ^ S.card := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [h2]
  have hZk : 0 < Zs (flipP s z) ^ S.card := pow_pos hZ _
  field_simp

/-! ## 4. (I4): positive parts of logarithms of ratios -/

/-- **(I4a)** For `a, b > 0`: `|log₂ (a/b)|₊ ≤ max (a - b) 0 / (b ln 2)`. -/
theorem pos_logb_div_le_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    pos (Real.logb 2 (a / b)) ≤ max (a - b) 0 / (b * Real.log 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hden : 0 < b * Real.log 2 := mul_pos hb hl2
  refine max_le (div_nonneg (le_max_right _ _) hden.le) ?_
  have hlog : Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
  have heq : a / b - 1 = (a - b) / b := by field_simp
  rw [Real.logb, div_le_div_iff₀ hl2 hden]
  have h1 : Real.log (a / b) * b ≤ a - b := by
    have := mul_le_mul_of_nonneg_right hlog hb.le
    rw [heq, div_mul_cancel₀ _ hb.ne'] at this
    exact this
  have h2 : a - b ≤ max (a - b) 0 := le_max_left _ _
  nlinarith

/-- **(I4b)** For `a, b > 0`, `c ≥ 1` and `a ≤ c b`: `|log₂ (a/b)|₊ ≤ log₂ c`. -/
theorem pos_logb_div_le_logb {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 1 ≤ c)
    (hab : a ≤ c * b) : pos (Real.logb 2 (a / b)) ≤ Real.logb 2 c := by
  refine pos_le (Real.logb_nonneg one_lt_two hc) ?_
  refine Real.logb_le_logb_of_le one_lt_two (div_pos ha hb) ?_
  rw [div_le_iff₀ hb]; exact hab

/-! ## 5. Measurability -/

section Meas

lemma b1c_measurable_le {f g : Param N → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun w => f w ≤ g w :=
  measurableSet_setOfPred.1 (measurableSet_le hf hg)

lemma measurable_clampEntry (r : State N) (i : Fin N) :
    Measurable fun w : Param N => clamp01 (w r i) :=
  clamp01_measurable.comp ((measurable_pi_apply i).comp (measurable_pi_apply r))

lemma measurable_Xk (k : ℕ) (i : Fin N) : Measurable fun w : Param N => Xk w k i :=
  Finset.measurable_sum _ fun r _ => Finset.measurable_sum _ fun r' _ =>
    (measurable_Qw i r).mul (measurable_Qw i r')

lemma measurable_DQ (S Y Y' : Finset (Fin N)) (t : State N) (i : Fin N) :
    Measurable fun w : Param N => DQ w S Y Y' t i :=
  ((measurable_subSum i Y t).div_const _).sub ((measurable_subSum i Y' t).div_const _)

lemma measurable_qW (s : State N) (S : Finset (Fin N)) (j : Fin N) (b : Bool) :
    Measurable fun w : Param N => qW w s S j b := by
  refine (Finset.measurable_sum _ fun r _ => ?_).div_const _
  split_ifs
  · exact measurable_clampEntry r j
  · exact measurable_const.sub (measurable_clampEntry r j)

lemma measurable_Mrow (s : State N) : Measurable fun w : Param N => Mrow w s :=
  Finset.measurable_prod _ fun i _ =>
    (measurable_clampEntry s i).max (measurable_const.sub (measurable_clampEntry s i))

lemma measurable_colMean (M : Finset (Fin N)) (m : State N) (i : Fin N) :
    Measurable fun w : Param N => colMean w M m i :=
  (Finset.measurable_sum _ fun r _ => measurable_clampEntry r i).div_const _

lemma measurable_colMeanPlus (M : Finset (Fin N)) (a : State N) (i : Fin N) :
    Measurable fun w : Param N => colMeanPlus w M a i :=
  (measurable_const.add (Finset.measurable_sum _ fun r _ => measurable_clampEntry r i)).div_const _

lemma measurable_blockP (S : Finset (Fin N)) (r : State N) :
    Measurable fun w : Param N => blockP w S r :=
  Finset.measurable_sum _ fun v _ => measurable_Pw v

/-- **`MeasurableSet {GoodW}`**: a countable conjunction of inequalities between measurable
statistics. -/
theorem measurableSet_goodW (s : State N) : MeasurableSet {w : Param N | GoodW N s w} := by
  have e : {w : Param N | GoodW N s w} = {w | (∀ i r, Qw w i r ≤ tauN N)
      ∧ (1 / 2 ≤ Zs w ∧ Zs w ≤ 2 ∧ ∀ i, ZQ w i ≤ 3)
      ∧ (∀ i, SQ2 w i ≤ 6 * (2 / 3 : ℝ) ^ N)
      ∧ (∀ i (M : Finset (Fin N)) (m : State N), subSum w i M m ≤
          (2 : ℝ) ^ (N - M.card) * (1 / 2 : ℝ) ^ (N - 1)
            + 16 * N * (Real.sqrt ((2 : ℝ) ^ (N - M.card) * (1 / 3 : ℝ) ^ (N - 1)) + tauN N))
      ∧ (∀ i, |Zs w - ZQ w i / 2| ≤ 16 * N * sigN N)
      ∧ (∀ k i, Xk w k i ≤ 4 * (N : ℝ) ^ 3 * vk N k * (1 / 2 : ℝ) ^ N)
      ∧ (∀ (S : Finset (Fin N)) i (Y : Finset (Fin N)) t, i ∈ S → Y ⊆ S →
          |Num w S Y t i - cNum w S Y t i| ≤ 2 * Real.sqrt (LkN N S.card * Vp w i S))
      ∧ (∀ (S : Finset (Fin N)) i (Y Y' : Finset (Fin N)) t, i ∈ S → Y ⊆ S → Y' ⊆ S →
          |DQ w S Y Y' t i| ≤ 16 * LkN N S.card * (Real.sqrt 3 * sigN N + tauN N))
      ∧ (∀ (S : Finset (Fin N)) j b, j ∈ S → K2N N < S.card → 1 / 4 ≤ qW w s S j b)
      ∧ Mrow w s ≤ (4 / 5 : ℝ) ^ N} := by
    ext w
    constructor
    · intro h
      exact ⟨h.g2, h.g3, h.g4, h.g6, h.g11, h.g12, h.g13a, h.g13b, h.g16, h.gU⟩
    · rintro ⟨h2, h3, h4, h6, h11, h12, h13a, h13b, h16, hU⟩
      exact ⟨h2, h3, h4, h6, h11, h12, h13a, h13b, h16, hU⟩
  rw [e, measurableSet_setOfPred]
  refine Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_
    (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_
    (Measurable.and ?_ ?_))))))))
  · exact Measurable.forall fun i => Measurable.forall fun r =>
      b1c_measurable_le (measurable_Qw i r) measurable_const
  · exact (b1c_measurable_le measurable_const measurable_Zs).and
      ((b1c_measurable_le measurable_Zs measurable_const).and
        (Measurable.forall fun i => b1c_measurable_le (measurable_ZQ i) measurable_const))
  · exact Measurable.forall fun i => b1c_measurable_le (measurable_SQ2 i) measurable_const
  · exact Measurable.forall fun i => Measurable.forall fun M => Measurable.forall fun m =>
      b1c_measurable_le (measurable_subSum i M m) measurable_const
  · exact Measurable.forall fun i => b1c_measurable_le
      (measurable_abs_comp (measurable_Zs.sub ((measurable_ZQ i).div_const 2))) measurable_const
  · exact Measurable.forall fun k => Measurable.forall fun i =>
      b1c_measurable_le (measurable_Xk k i) measurable_const
  · exact Measurable.forall fun S => Measurable.forall fun i => Measurable.forall fun Y =>
      Measurable.forall fun t => measurable_const.imp (measurable_const.imp (b1c_measurable_le
        (measurable_abs_comp ((measurable_Num S Y t i).sub (measurable_cNum S Y t i)))
        ((measurable_const.mul (measurable_Vp S i)).sqrt.const_mul 2)))
  · exact Measurable.forall fun S => Measurable.forall fun i => Measurable.forall fun Y =>
      Measurable.forall fun Y' => Measurable.forall fun t => measurable_const.imp
        (measurable_const.imp (measurable_const.imp (b1c_measurable_le
          (measurable_abs_comp (measurable_DQ S Y Y' t i)) measurable_const)))
  · exact Measurable.forall fun S => Measurable.forall fun j => Measurable.forall fun b =>
      measurable_const.imp (measurable_const.imp
        (b1c_measurable_le measurable_const (measurable_qW s S j b)))
  · exact b1c_measurable_le (measurable_Mrow s) measurable_const

end Meas

/-! ## 6. The bound `N · dlev N k ≤ 1/100` of `eventually_levels`, exported -/

/-- **EV1 input.** Eventually, `N · dlev N k ≤ 1/100` for all `1 ≤ k ≤ K2N N` (the local `hNd` of
`eventually_levels`). -/
theorem eventually_N_dlev : ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ K2N N →
    (N : ℝ) * dlev N k ≤ 1 / 100 := by
  filter_upwards [eventually_ge_atTop 1,
    ev_quad_half_comp tendsto_natLog2 0 1 6 (by norm_num : (0 : ℝ) < 1e-3),
    ev_pow_mul_sigN 5 (C := 5376) (by norm_num) (by norm_num : (0 : ℝ) < 5e-5)]
    with N hN hℓ h5
  intro k hk1 hkK
  set ℓ := Nat.log 2 N with hℓdef
  have hℓ' : ((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ ℓ < 1e-3 := by
    have : ((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ ℓ = (0 * (ℓ : ℝ) ^ 2 + 1 * ℓ + 6) * (1 / 2 : ℝ) ^ ℓ := by
      ring
    rw [this]; exact hℓ
  have hkN : k + (4 * ℓ + 16) ≤ N := by unfold K2N at hkK; omega
  have hkN' : k ≤ N := by omega
  have hσ := sigN_pos N
  have e : (N : ℝ) * dlev N k = (2 * N) * Real.sqrt (LkN N k * (3 * Mk N k)) := by
    rw [dlev]; ring
  rw [e]
  apply mul_sqrt_le_of_sq (by positivity) (by norm_num)
  have hL := LkN_le_levels hN hkN'
  have hL0 := LkN_nonneg' k hN
  have hM := Mk_le hN hkN
  set Mb : ℝ := (1 / 2 : ℝ) ^ (4 * ℓ + 15) + 64 * N * sigN N with hMb
  have hMb0 : 0 ≤ Mb := by positivity
  have s1 : (2 * (N : ℝ)) ^ 2 * (LkN N k * (3 * Mk N k)) ≤
      (2 * (N : ℝ)) ^ 2 * ((N * ((ℓ : ℝ) + 6)) * (3 * Mb)) := by
    have : LkN N k * (3 * Mk N k) ≤ (N * ((ℓ : ℝ) + 6)) * (3 * Mb) := by
      calc LkN N k * (3 * Mk N k) ≤ LkN N k * (3 * Mb) := by gcongr
        _ ≤ _ := by gcongr
    exact mul_le_mul_of_nonneg_left this (by positivity)
  set u : ℝ := (N : ℝ) * (1 / 2 : ℝ) ^ ℓ with hu
  have hu0 : 0 ≤ u := by positivity
  have hu2 : u ≤ 2 := by
    have hlt : (N : ℝ) < 2 * 2 ^ ℓ := by exact_mod_cast lt_two_mul_two_pow_natLog N
    have hh : (2 : ℝ) ^ ℓ * (1 / 2 : ℝ) ^ ℓ = 1 := by rw [← mul_pow]; norm_num
    have : 0 < (1 / 2 : ℝ) ^ ℓ := by positivity
    rw [hu]; nlinarith
  have hu3 : u ^ 3 ≤ 8 := by
    have := pow_le_pow_left₀ hu0 hu2 3; norm_num at this; linarith
  have hpow : (1 / 2 : ℝ) ^ (4 * ℓ + 15) =
      ((1 / 2 : ℝ) ^ ℓ) ^ 3 * (1 / 2 : ℝ) ^ ℓ * (1 / 2) ^ 15 := by
    rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
  have p1 : 12 * (N : ℝ) ^ 3 * ((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ (4 * ℓ + 15) ≤ 1e-5 := by
    have e1 : 12 * (N : ℝ) ^ 3 * ((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ (4 * ℓ + 15) =
        12 * u ^ 3 * (1 / 2) ^ 15 * (((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ ℓ) := by
      rw [hpow, hu]; ring
    rw [e1]
    have : 0 ≤ ((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ ℓ := by positivity
    have : 12 * u ^ 3 * (1 / 2 : ℝ) ^ 15 ≤ 12 * 8 * (1 / 2) ^ 15 := by gcongr
    nlinarith
  have p2 : 768 * (N : ℝ) ^ 4 * ((ℓ : ℝ) + 6) * sigN N ≤ 5e-5 := by
    have hℓN : ((ℓ : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast natLog_succ_le_self hN
    have : 768 * (N : ℝ) ^ 4 * ((ℓ : ℝ) + 6) * sigN N ≤ 768 * (N : ℝ) ^ 4 * (7 * N) * sigN N := by
      gcongr; linarith
    have e : 768 * (N : ℝ) ^ 4 * (7 * N) * sigN N = 5376 * (N : ℝ) ^ 5 * sigN N := by ring
    linarith
  have e2 : (2 * (N : ℝ)) ^ 2 * ((N * ((ℓ : ℝ) + 6)) * (3 * Mb)) =
      12 * (N : ℝ) ^ 3 * ((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ (4 * ℓ + 15)
        + 768 * (N : ℝ) ^ 4 * ((ℓ : ℝ) + 6) * sigN N := by
    rw [hMb]; ring
  rw [e2] at s1
  nlinarith

/-- **EV1, second part.** Eventually, `N · (2τ + 2 Mk N k) ≤ 1/200` for all `1 ≤ k ≤ K2N N`
(from `Mk_le` and `tauN_le_two_sigN`). -/
theorem eventually_N_tau_Mk : ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ K2N N →
    (N : ℝ) * (2 * tauN N + 2 * Mk N k) ≤ 1 / 200 := by
  filter_upwards [eventually_ge_atTop 1,
    ev_pow_mul_sigN 2 (C := 132) (by norm_num) (by norm_num : (0 : ℝ) < 1e-3)]
    with N hN h2
  intro k hk1 hkK
  set ℓ := Nat.log 2 N with hℓdef
  have hkN : k + (4 * ℓ + 16) ≤ N := by unfold K2N at hkK; omega
  have hσ := sigN_pos N
  have hM := Mk_le hN hkN
  rw [← hℓdef] at hM
  have hτ := tauN_le_two_sigN N
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set u : ℝ := (N : ℝ) * (1 / 2 : ℝ) ^ ℓ with hu
  have hu2 : u ≤ 2 := by
    have hlt : (N : ℝ) < 2 * 2 ^ ℓ := by exact_mod_cast lt_two_mul_two_pow_natLog N
    have hh : (2 : ℝ) ^ ℓ * (1 / 2 : ℝ) ^ ℓ = 1 := by rw [← mul_pow]; norm_num
    have : 0 < (1 / 2 : ℝ) ^ ℓ := by positivity
    rw [hu]; nlinarith
  have hp : (N : ℝ) * (1 / 2 : ℝ) ^ (4 * ℓ + 15) ≤ 2 * (1 / 2 : ℝ) ^ 15 := by
    have e : (N : ℝ) * (1 / 2 : ℝ) ^ (4 * ℓ + 15) = u * ((1 / 2 : ℝ) ^ (3 * ℓ) * (1 / 2) ^ 15) := by
      rw [hu, show 4 * ℓ + 15 = ℓ + 3 * ℓ + 15 by ring, pow_add, pow_add]; ring
    rw [e]
    have h3 : (1 / 2 : ℝ) ^ (3 * ℓ) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h0 : 0 ≤ (1 / 2 : ℝ) ^ (3 * ℓ) := by positivity
    have hu0 : 0 ≤ u := by positivity
    have : (1 / 2 : ℝ) ^ (3 * ℓ) * (1 / 2) ^ 15 ≤ (1 / 2) ^ 15 := by
      have : (0 : ℝ) ≤ (1 / 2) ^ 15 := by positivity
      nlinarith
    exact mul_le_mul hu2 this (by positivity) (by norm_num)
  have hNM : (N : ℝ) * Mk N k ≤ 2 * (1 / 2 : ℝ) ^ 15 + 64 * (N : ℝ) ^ 2 * sigN N := by
    have := mul_le_mul_of_nonneg_left hM (by positivity : (0 : ℝ) ≤ N)
    nlinarith
  have hNτ : (N : ℝ) * tauN N ≤ 2 * (N : ℝ) ^ 2 * sigN N := by
    have := mul_le_mul_of_nonneg_left hτ (by positivity : (0 : ℝ) ≤ N)
    have : (N : ℝ) * sigN N ≤ (N : ℝ) ^ 2 * sigN N := by
      have : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this hσ.le
    nlinarith
  have e : (N : ℝ) * (2 * tauN N + 2 * Mk N k) = 2 * ((N : ℝ) * tauN N) + 2 * ((N : ℝ) * Mk N k) := by
    ring
  rw [e]
  have : 132 * (N : ℝ) ^ 2 * sigN N ≤ 1e-3 := h2
  norm_num at this ⊢
  nlinarith

end

end Census
end IIT
