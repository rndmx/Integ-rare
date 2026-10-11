/-
Census of complexes, B1 development, module A1 (`B1-BLUEPRINT.md`, Sections 2, 3 and module A1):
the definitions every other B1 module codes against.

Notation (flipped coordinates, as in `BigPhiStats`): `w = flipP s z`, `y_{r,i} = clamp01 (w r i)`,
`tc = tcRow w` (argmax of the row products `Pw`), `β = betaW w`, `ℓ_i = -log y_{tc,i}`,
`x_k = xE w s k`, `e = eE w s`, `te = teW w s`, `ph_j = phU w s j`.

Deviations from the blueprint signatures (all minimal; nothing else is changed):
* `RLB`, `Rbad` and `teW` are `noncomputable def` (division and `<` on `ℝ` are noncomputable).
* `yTopW w ε` is the `⌈ε N⌉₊`-th largest entry of row `tc` (with multiplicity, `b1Kth`); it is
  the maximum for `⌈ε N⌉₊ = 0` and `0` for `⌈ε N⌉₊ > N`.  For `N = 0` (empty rows) the conventions
  are `yMinW = 1`, `yMaxW = yTopW = 0`.  `yMaxW` (the largest entry of `tc`) is added.
* `tcRow` breaks ties by the least binary index `b1Idx` (the "least index" of the blueprint).
* `phU w s j` is the EXACT value of the single-unit cut `θ_j` of `univ` (unit `j` cut from all
  others, `cc = N - 1`) at the state pair `(tcRow w, teW w s)`, i.e. it carries the positive parts:
  `min (β · pos (log₂ (y_{tc,j} / q_j))) (e · pos (log₂ (x_j / q'_j)))` with
  `q_j = b1HalfW w j (tc j)` (the flipped column half-mean, `= halfMean` by `b1_halfMean_eq`) and
  `q'_j = qW w s univ j (te j)`.  Since `β, e ≥ 0` this is `pos` of the blueprint's `ph_j`.
* `univ.inf' _ (phU w s)` is packaged as `phUMin w s` (no nonemptiness proof needed; equal to the
  `inf'` for `N ≥ 1`, see `b1_phUMin_eq_inf'`).
* `Forced`, `GoodF`, `bdry` had no body in the blueprint.  They are fixed here (Section 2, Layer II
  and III, with explicit constants `b1Eps = 1/1000`, `b1TopRatio = 984/1000`, `b1Eta = 1/400`,
  `b1ZMax = 13`, `b1YLo = 3/5`, `b1Cap = 63/125 = 0.504`, `b1PosC = 1/25`).  NOTE on G13: with the
  exact constants the 4-set level `11·(7/8)/(48 lvK 4 ln 2) = 0.566775` over `levTrip = 0.577078`
  is `0.982147`, so the blueprint's `y_top ≥ 0.982 y_max` is NOT sufficient; `b1TopRatio = 0.984`
  together with the factor `1 - b1Eps` is (lemma `b1_fourSet_margin`).  Certificate C10 must
  therefore exclude `y_top < 0.984 y_max`.
* `GoodF N s r0` is the set of sensitive-row data `f` whose extension `b1Ext f` (other rows set
  to `1`) satisfies `B1FGood N s r0`, the conjunction of the conditions of `Forced` that only read
  the rows of `sensRows s r0` (tilt of `r0`, far, profile of `r0`, positivity near `r0` for
  `|K'| ≤ 4`, retention against the ball rows).  `Forced` contains `B1FGood N s (tcRow w) w`, so
  `Forced ∧ tcRow w = r0` implies `b1Restr s r0 w ∈ GoodF N s r0` (`Forced.restr_mem_goodF`).
* The positivity condition near `tc` is Fable's Lemma G5 small-cut sum
  `∑_i g_i(K')`, `g_i(K') = min (log (y_{tc,i} / Ā_i(K'))) (log (y_{tc,i} / 0.504))`, taken over
  ALL units with margin `b1PosC · N`; for `M = univ \ K`, `|K| = dFam N`, it gives
  `∑_{i∈M} g_i ≥ (1/25 - 0.0172) N - 0.69 > 0` (each `g_i ≤ log (1/0.504) < 0.69`), which covers
  positivity and the tc-pattern uniqueness of the near-full purviews for `|K'| ≤ 4` (C6, C7).
* `Forced` also carries three fields that the blueprint's list leaves implicit and that later
  modules need: `mem_open` (all entries in `(0,1)`; the complement is null), `zs` (`1/2 ≤ Z ≤ 13`,
  G16) and `states` (the maximal cause/effect states of `U` are `tc` and `te`, A7's hypotheses).
* Helper definitions added (all prefixed `b1`/`B1` to avoid clashes): `b1Idx`, `b1Kth`,
  `b1YMinR`, `b1YMaxR`, `b1YTopR` (row-level versions of `yMinW`, `yMaxW`, `yTopW`), `b1HalfW`,
  `b1CutMean`, `b1CutG`, `B1FGood`, `b1Ext`, `b1Restr`; also `yMaxW` and `phUMin`.
* `caseB1 ⊆ univPos` needs `2 ≤ N` (for `N = 1` every one-unit system is vacuously a complex).
* Measurability: proved for `B1w`, `{tcRow = r0}`, `GoodF`, `Forced` and `bdry` (`phi` is
  measurable in `z`: `b1_measurable_phi`).  Not proved for `SmallW` (it quantifies over the
  `z`-dependent type of selectors); downstream bounds on it go through measurable supersets.
-/
import IIT.Census.B1Target
import IIT.Census.Profile

namespace IIT
namespace Census

open MeasureTheory Finset

variable {N : ℕ}

/-! ## 1. Constants (Section 2 notation and Section 3) -/

/-- The size-biased cause level `a_k = 1/2 + 2^{-k}/6` of a candidate of size `k`. -/
noncomputable def lvK (k : ℕ) : ℝ := 1 / 2 + (1 / 2 : ℝ) ^ k / 6

/-- The triple level `levTrip = (5/3)/(8 a_3 ln 2) = 0.5771`. -/
noncomputable def levTrip : ℝ := 5 / 24 / (lvK 3 * Real.log 2)

/-- `x0 = ln(3/2)/2 = 0.2027`, so that `σ_N = (2/3)^{N/2} = e^{-x0 N}`. -/
noncomputable def x0 : ℝ := Real.log (3 / 2) / 2

/-- The rate of the lower bound on `P(B1)`. -/
noncomputable def RLB : ℝ := 103 / 100

/-- The rate every excluded event is certified at. -/
noncomputable def Rbad : ℝ := 104 / 100

/-- The size `d = ⌈N/40⌉` of the deleted sets `K` of the counting family. -/
def dFam (N : ℕ) : ℕ := (N + 39) / 40

/-- The `ε` of `y_top` (the `⌈εN⌉`-th largest entry of `tc`) in `Forced`. -/
noncomputable def b1Eps : ℝ := 1 / 1000

/-- G13: `y_top ≥ b1TopRatio · y_max` in `Forced`. -/
noncomputable def b1TopRatio : ℝ := 984 / 1000

/-- The near-tie margin `η` of heavy rows (C8, C11) and of retention against the ball rows. -/
noncomputable def b1Eta : ℝ := 1 / 400

/-- The upper bound on `Zs` (at most ten special rows, G16). -/
noncomputable def b1ZMax : ℝ := 13

/-- The lower bound on the entries of `tc` in `Forced` (implied by the stage-2 profile). -/
noncomputable def b1YLo : ℝ := 3 / 5

/-- The big-cut cap `0.504` of the positivity sums (Fable's Lemma G5, `b_i = log (e_i/0.504)`). -/
noncomputable def b1Cap : ℝ := 63 / 125

/-- The margin of the positivity sums near `tc` (C6, C7). -/
noncomputable def b1PosC : ℝ := 1 / 25

lemma lvK_gt_half (k : ℕ) : 1 / 2 < lvK k := by
  unfold lvK; have : 0 < (1 / 2 : ℝ) ^ k := by positivity
  linarith

lemma lvK_pos (k : ℕ) : 0 < lvK k := lt_trans (by norm_num) (lvK_gt_half k)

lemma lvK_le (k : ℕ) : lvK k ≤ 2 / 3 := by
  unfold lvK
  have : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

lemma lvK_two : lvK 2 = 13 / 24 := by norm_num [lvK]
lemma lvK_three : lvK 3 = 25 / 48 := by norm_num [lvK]
lemma lvK_four : lvK 4 = 49 / 96 := by norm_num [lvK]

lemma b1_log_two_pos : 0 < Real.log 2 := Real.log_pos one_lt_two

lemma levTrip_eq : levTrip = 2 / (5 * Real.log 2) := by
  have h := b1_log_two_pos
  rw [levTrip, lvK_three]; field_simp; ring

lemma levTrip_pos : 0 < levTrip := by rw [levTrip_eq]; have := b1_log_two_pos; positivity

lemma levTrip_gt : (577 / 1000 : ℝ) < levTrip := by
  rw [levTrip_eq, lt_div_iff₀ (by have := b1_log_two_pos; positivity)]
  have := Real.log_two_lt_d9; norm_num at this ⊢; linarith

lemma levTrip_lt : levTrip < 5771 / 10000 := by
  rw [levTrip_eq, div_lt_iff₀ (by have := b1_log_two_pos; positivity)]
  have := Real.log_two_gt_d9; norm_num at this ⊢; linarith

lemma b1_log_three_halves_gt : 31 / 53 * Real.log 2 < Real.log (3 / 2) := by
  have h1 : (2 : ℝ) ^ 31 < (3 / 2) ^ 53 := by norm_num
  have h2 := Real.log_lt_log (by positivity) h1
  rw [Real.log_pow, Real.log_pow] at h2
  push_cast at h2
  linarith

lemma b1_log_three_halves_lt : Real.log (3 / 2) < 24 / 41 * Real.log 2 := by
  have h1 : ((3 : ℝ) / 2) ^ 41 < 2 ^ 24 := by norm_num
  have h2 := Real.log_lt_log (by positivity) h1
  rw [Real.log_pow, Real.log_pow] at h2
  push_cast at h2
  linarith

lemma x0_gt : (2027 / 10000 : ℝ) < x0 := by
  have := b1_log_three_halves_gt; have := Real.log_two_gt_d9
  unfold x0; norm_num at *; linarith

lemma x0_lt : x0 < 2029 / 10000 := by
  have := b1_log_three_halves_lt; have := Real.log_two_lt_d9
  unfold x0; norm_num at *; linarith

lemma x0_pos : 0 < x0 := lt_trans (by norm_num) x0_gt

/-- `σ_N = e^{-x0 N}`. -/
lemma sigN_eq_exp (N : ℕ) : sigN N = Real.exp (-(x0 * N)) := by
  unfold sigN x0
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (Real.exp_pos _).le, ← Real.exp_add,
    ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  congr 1
  rw [show (2 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, Real.log_inv]
  ring

lemma RLB_lt_Rbad : RLB < Rbad := by norm_num [RLB, Rbad]

lemma RLB_pos : 0 < RLB := by norm_num [RLB]

lemma le_forty_mul_dFam (N : ℕ) : N ≤ 40 * dFam N := by unfold dFam; omega

lemma forty_mul_dFam_le (N : ℕ) : 40 * dFam N ≤ N + 39 := by unfold dFam; omega

lemma dFam_le (hN : 1 ≤ N) : dFam N ≤ N := by unfold dFam; omega

lemma dFam_pos (hN : 1 ≤ N) : 0 < dFam N := by unfold dFam; omega

/-- **C2, the 4-set margin (G13).** The 4-set level `11·(7/8)/(48 a_4 ln 2) = 0.566775` is below
`(1 - b1Eps) · b1TopRatio · levTrip = 0.567285`. -/
lemma b1_fourSet_margin :
    11 * (7 / 8) / (48 * lvK 4 * Real.log 2) < (1 - b1Eps) * b1TopRatio * levTrip := by
  have h := b1_log_two_pos
  rw [levTrip_eq, lvK_four, b1Eps, b1TopRatio]
  rw [div_lt_iff₀ (by positivity)]
  field_simp
  norm_num

/-- **C2, the pair level** `1/(8 a_2 ln 2) = 0.3329` is below `levTrip`. -/
lemma b1_pair_level_lt : 1 / (8 * lvK 2 * Real.log 2) < levTrip := by
  have h := b1_log_two_pos
  rw [levTrip_eq, lvK_two, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ## 2. The maximal cause row `tcRow` -/

/-- The binary index of a state (unit `i` has weight `2^i`); used to break ties. -/
def b1Idx (r : State N) : ℕ :=
  (finFunctionFinEquiv (fun i => if r i then (1 : Fin 2) else 0) : ℕ)

lemma b1Idx_injective : Function.Injective (b1Idx (N := N)) := by
  intro r r' h
  have h2 := finFunctionFinEquiv.injective (Fin.ext h)
  funext i
  have := congrFun h2 i
  by_cases hr : r i <;> by_cases hr' : r' i <;> simp_all

lemma b1_exists_tcRow (w : Param N) :
    ∃ r ∈ argmaxSet (Pw w), ∀ r' ∈ argmaxSet (Pw w), b1Idx r ≤ b1Idx r' :=
  Finset.exists_min_image _ b1Idx (argmaxSet_nonempty _)

/-- `tc`: the row with the largest row product `Pw`, the least index `b1Idx` on ties. -/
noncomputable def tcRow (w : Param N) : State N := (b1_exists_tcRow w).choose

lemma tcRow_spec (w : Param N) :
    tcRow w ∈ argmaxSet (Pw w) ∧ ∀ r' ∈ argmaxSet (Pw w), b1Idx (tcRow w) ≤ b1Idx r' :=
  (b1_exists_tcRow w).choose_spec

lemma Pw_le_tcRow (w : Param N) (r : State N) : Pw w r ≤ Pw w (tcRow w) :=
  mem_argmaxSet.1 (tcRow_spec w).1 r

/-- **Characterisation of `tcRow`** (used for the decomposition `B1 = ⋃ r0, B1 ∩ {tcRow = r0}`). -/
theorem tcRow_eq_iff (w : Param N) (r0 : State N) :
    tcRow w = r0 ↔ (∀ r, Pw w r ≤ Pw w r0) ∧ ∀ r, b1Idx r < b1Idx r0 → Pw w r < Pw w r0 := by
  constructor
  · rintro rfl
    refine ⟨Pw_le_tcRow w, fun r hr => lt_of_le_of_ne (Pw_le_tcRow w r) fun heq => ?_⟩
    have hmem : r ∈ argmaxSet (Pw w) :=
      mem_argmaxSet.2 fun b => by rw [heq]; exact Pw_le_tcRow w b
    exact absurd ((tcRow_spec w).2 r hmem) (not_le.2 hr)
  · rintro ⟨hmax, hlt⟩
    have h1 := (tcRow_spec w).2 r0 (mem_argmaxSet.2 hmax)
    have heq : Pw w (tcRow w) = Pw w r0 := le_antisymm (hmax _) (Pw_le_tcRow w r0)
    rcases h1.lt_or_eq with h | h
    · exact absurd heq (ne_of_lt (hlt _ h))
    · exact b1Idx_injective h

lemma tcRow_eq_of_strict {w : Param N} {r0 : State N} (h : ∀ r, r ≠ r0 → Pw w r < Pw w r0) :
    tcRow w = r0 := by
  refine (tcRow_eq_iff w r0).2 ⟨fun r => ?_, fun r hr => h r fun e => ?_⟩
  · by_cases hr : r = r0
    · rw [hr]
    · exact (h r hr).le
  · rw [e] at hr; exact lt_irrefl _ hr

/-! ## 3. Statistics of Section 2 -/

/-- `β = Pw(tc)/Zs`. -/
noncomputable def betaW (w : Param N) : ℝ := Pw w (tcRow w) / Zs w

/-- `X(r) = ∑_i -log y_{r,i}`. -/
noncomputable def XW (w : Param N) (r : State N) : ℝ := ∑ i, -Real.log (clamp01 (w r i))

/-- `X_M(r) = ∑_{i ∈ M} -log y_{r,i}`. -/
noncomputable def XMW (w : Param N) (M : Finset (Fin N)) (r : State N) : ℝ :=
  ∑ i ∈ M, -Real.log (clamp01 (w r i))

/-- The `k`-th largest value of `f` counted with multiplicity (`1 ≤ k ≤ N`); the maximum for
`k = 0`, and `0` when `k > N`. -/
noncomputable def b1Kth (f : Fin N → ℝ) (k : ℕ) : ℝ :=
  sup'OrZero (univ.filter fun i => k ≤ (univ.filter fun j => f i ≤ f j).card) f

/-- Smallest entry of row `r` (`1` for `N = 0`). -/
noncomputable def b1YMinR (w : Param N) (r : State N) : ℝ :=
  if h : (univ : Finset (Fin N)).Nonempty then univ.inf' h fun i => clamp01 (w r i) else 1

/-- Largest entry of row `r` (`0` for `N = 0`). -/
noncomputable def b1YMaxR (w : Param N) (r : State N) : ℝ :=
  sup'OrZero univ fun i => clamp01 (w r i)

/-- The `⌈εN⌉₊`-th largest entry of row `r`. -/
noncomputable def b1YTopR (w : Param N) (r : State N) (ε : ℝ) : ℝ :=
  b1Kth (fun i => clamp01 (w r i)) ⌈ε * N⌉₊

/-- `y_min`: the smallest entry of `tc`. -/
noncomputable def yMinW (w : Param N) : ℝ := b1YMinR w (tcRow w)

/-- `y_max`: the largest entry of `tc`. -/
noncomputable def yMaxW (w : Param N) : ℝ := b1YMaxR w (tcRow w)

/-- `y_top`: the `⌈εN⌉₊`-th largest entry of `tc`. -/
noncomputable def yTopW (w : Param N) (ε : ℝ) : ℝ := b1YTopR w (tcRow w) ε

/-- `x_k = max(y_{s,k}, 1 - y_{s,k})`: the largest probability of unit `k` from the current row. -/
noncomputable def xE (w : Param N) (s : State N) (k : Fin N) : ℝ :=
  max (clamp01 (w s k)) (1 - clamp01 (w s k))

/-- `e = ∏_k x_k` (`= Mrow w s`). -/
noncomputable def eE (w : Param N) (s : State N) : ℝ := ∏ k, xE w s k

/-- `te`: the componentwise argmax of the current row. -/
noncomputable def teW (w : Param N) (s : State N) : State N :=
  fun k => if 1 / 2 < clamp01 (w s k) then s k else !s k

/-- Column half-mean in flipped coordinates (`= halfMean`, `b1_halfMean_eq`). -/
noncomputable def b1HalfW (w : Param N) (j : Fin N) (b : Bool) : ℝ :=
  (∑ r ∈ univ.filter (fun r : State N => r j = b), clamp01 (w r j)) / (2 : ℝ) ^ (N - 1)

/-- **The single-unit cut value of `univ`** at `(tc, te)`: unit `j` cut from all the others
(`cc = N - 1`), the minimum of the cause side `β · (log₂ (y_{tc,j}/q_j))⁺` and the effect side
`e · (log₂ (x_j/q'_j))⁺`. -/
noncomputable def phU (w : Param N) (s : State N) (j : Fin N) : ℝ :=
  min (betaW w * pos (Real.logb 2 (clamp01 (w (tcRow w) j) / b1HalfW w j (tcRow w j))))
    (eE w s * pos (Real.logb 2 (xE w s j / qW w s univ j (teW w s j))))

/-- `min_j ph_j` (`0` for `N = 0`). -/
noncomputable def phUMin (w : Param N) (s : State N) : ℝ :=
  if h : (univ : Finset (Fin N)).Nonempty then univ.inf' h (phU w s) else 0

/-- The mean of column `i` over the `K'`-subcube through `t` (the `2^{|K'|}` rows agreeing with `t`
off `K'`): Fable's `Ā_i(C_{K'}(t))`. -/
noncomputable def b1CutMean (w : Param N) (t : State N) (K' : Finset (Fin N)) (i : Fin N) : ℝ :=
  (∑ r ∈ agree K'ᶜ t, clamp01 (w r i)) / (2 : ℝ) ^ K'.card

/-- The truncated small-cut term `g_i(K') = min (log (y_{t,i}/Ā_i(K'))) (log (y_{t,i}/0.504))`. -/
noncomputable def b1CutG (w : Param N) (t : State N) (K' : Finset (Fin N)) (i : Fin N) : ℝ :=
  min (Real.log (clamp01 (w t i) / b1CutMean w t K' i)) (Real.log (clamp01 (w t i) / b1Cap))

/-! ### Basic facts -/

lemma b1_clamp01_of_mem_Ioo {x : ℝ} (h : x ∈ Set.Ioo (0 : ℝ) 1) : clamp01 x = x :=
  clamp01_of_mem ⟨h.1.le, h.2.le⟩

lemma betaW_nonneg (w : Param N) : 0 ≤ betaW w := div_nonneg (Pw_nonneg _ _) (Zs_nonneg _)

lemma betaW_le_one (w : Param N) : betaW w ≤ 1 := by
  unfold betaW
  rcases (Zs_nonneg w).lt_or_eq with h | h
  · rw [div_le_one h]
    exact single_le_sum (fun r _ => Pw_nonneg w r) (mem_univ _)
  · rw [← h, div_zero]; exact zero_le_one

lemma b1_Pw_pos {w : Param N} (hw : w ∈ openCube N) (r : State N) : 0 < Pw w r :=
  prod_pos fun i _ => by rw [b1_clamp01_of_mem_Ioo (hw r i)]; exact (hw r i).1

lemma b1_Zs_pos {w : Param N} (hw : w ∈ openCube N) : 0 < Zs w :=
  sum_pos (fun r _ => b1_Pw_pos hw r) univ_nonempty

lemma betaW_pos {w : Param N} (hw : w ∈ openCube N) : 0 < betaW w :=
  div_pos (b1_Pw_pos hw _) (b1_Zs_pos hw)

lemma b1_neg_log_clamp_nonneg (x : ℝ) : 0 ≤ -Real.log (clamp01 x) :=
  neg_nonneg.2 (Real.log_nonpos (clamp01_nonneg x) (clamp01_le_one x))

lemma XW_nonneg (w : Param N) (r : State N) : 0 ≤ XW w r :=
  sum_nonneg fun _ _ => b1_neg_log_clamp_nonneg _

lemma XMW_nonneg (w : Param N) (M : Finset (Fin N)) (r : State N) : 0 ≤ XMW w M r :=
  sum_nonneg fun _ _ => b1_neg_log_clamp_nonneg _

lemma XMW_univ (w : Param N) (r : State N) : XMW w univ r = XW w r := rfl

lemma XMW_le_XW (w : Param N) (M : Finset (Fin N)) (r : State N) : XMW w M r ≤ XW w r :=
  sum_le_sum_of_subset_of_nonneg (subset_univ M) fun _ _ _ => b1_neg_log_clamp_nonneg _

lemma XW_eq_XMW_add (w : Param N) (M : Finset (Fin N)) (r : State N) :
    XW w r = XMW w M r + XMW w Mᶜ r :=
  (sum_add_sum_compl M _).symm

/-- `Pw = e^{-X}` when the entries of the row are positive. -/
lemma Pw_eq_exp_neg_XW {w : Param N} {r : State N} (h : ∀ i, 0 < clamp01 (w r i)) :
    Pw w r = Real.exp (-XW w r) := by
  unfold Pw XW
  rw [← sum_neg_distrib, Real.exp_sum]
  exact prod_congr rfl fun i _ => by rw [neg_neg, Real.exp_log (h i)]

lemma xE_ge_half (w : Param N) (s : State N) (k : Fin N) : 1 / 2 ≤ xE w s k := by
  unfold xE
  rcases le_total (clamp01 (w s k)) (1 / 2) with h | h
  · exact le_max_of_le_right (by linarith)
  · exact le_max_of_le_left h

lemma xE_le_one (w : Param N) (s : State N) (k : Fin N) : xE w s k ≤ 1 :=
  max_le (clamp01_le_one _) (by linarith [clamp01_nonneg (w s k)])

lemma xE_pos (w : Param N) (s : State N) (k : Fin N) : 0 < xE w s k :=
  lt_of_lt_of_le (by norm_num) (xE_ge_half w s k)

lemma eE_eq_Mrow (w : Param N) (s : State N) : eE w s = Mrow w s := rfl

lemma eE_pos (w : Param N) (s : State N) : 0 < eE w s := prod_pos fun k _ => xE_pos w s k

lemma eE_le_one (w : Param N) (s : State N) : eE w s ≤ 1 :=
  prod_le_one (fun k _ => (xE_pos w s k).le) fun k _ => xE_le_one w s k

/-- The effect probability of `te_k` from the current state is `x_k`. -/
lemma prob_teW (z : Param N) (s : State N) (k : Fin N) :
    (tpmOf z).prob k s (teW (flipP s z) s k) = xE (flipP s z) s k := by
  have hc := prob_eq_clamp z s s k
  have hnot : (tpmOf z).prob k s (!s k) = 1 - (tpmOf z).prob k s (s k) := by
    cases s k <;> simp [tpmOf]
  unfold teW xE
  split_ifs with h
  · rw [hc, max_eq_left (by linarith)]
  · rw [hnot, hc, max_eq_right (by linarith)]

lemma b1_halfMean_eq (z : Param N) (s : State N) (j : Fin N) (b : Bool) :
    halfMean z s j b = b1HalfW (flipP s z) j b := by
  unfold halfMean b1HalfW
  simp only [y_eq_clamp]

lemma phU_nonneg (w : Param N) (s : State N) (j : Fin N) : 0 ≤ phU w s j :=
  le_min (mul_nonneg (betaW_nonneg w) (pos_nonneg _)) (mul_nonneg (eE_pos w s).le (pos_nonneg _))

lemma b1_phUMin_eq_inf' (w : Param N) (s : State N) (h : (univ : Finset (Fin N)).Nonempty) :
    phUMin w s = univ.inf' h (phU w s) := by
  rw [phUMin, dite_eq_left h]

lemma phUMin_le (w : Param N) (s : State N) (j : Fin N) : phUMin w s ≤ phU w s j := by
  rw [b1_phUMin_eq_inf' w s ⟨j, mem_univ j⟩]; exact inf'_le _ (mem_univ j)

lemma le_phUMin {w : Param N} {s : State N} {a : ℝ} (h : ∀ j, a ≤ phU w s j) (ha : a ≤ 0 ∨ 0 < N) :
    a ≤ phUMin w s := by
  unfold phUMin
  split_ifs with hne
  · exact le_inf' _ _ fun j _ => h j
  · rcases ha with ha | ha
    · exact ha
    · exact absurd ⟨⟨0, ha⟩, mem_univ _⟩ hne

/-! ### Order statistics of a row -/

lemma b1Kth_filter_nonempty {f : Fin N → ℝ} {k : ℕ} (hk : k ≤ N) (hN : 0 < N) :
    (univ.filter fun i => k ≤ (univ.filter fun j => f i ≤ f j).card).Nonempty := by
  obtain ⟨i0, -, hi0⟩ := exists_min_image (univ : Finset (Fin N)) f ⟨⟨0, hN⟩, mem_univ _⟩
  refine ⟨i0, mem_filter.2 ⟨mem_univ _, ?_⟩⟩
  rw [filter_true_of_mem fun j _ => hi0 j (mem_univ j), card_univ, Fintype.card_fin]
  exact hk

/-- For `k ≤ N` (and `N ≥ 1`) the `k`-th largest value is attained, at an index with at least `k`
values above it. -/
lemma b1Kth_mem {f : Fin N → ℝ} {k : ℕ} (hk : k ≤ N) (hN : 0 < N) :
    ∃ i, k ≤ (univ.filter fun j => f i ≤ f j).card ∧ b1Kth f k = f i := by
  obtain ⟨i1, hi1A, hi1⟩ := exists_mem_eq_sup' (b1Kth_filter_nonempty (f := f) hk hN) f
  refine ⟨i1, (mem_filter.1 hi1A).2, ?_⟩
  rw [b1Kth, sup'OrZero, dite_eq_left (b1Kth_filter_nonempty hk hN), hi1]

lemma b1Kth_count {f : Fin N → ℝ} {k : ℕ} (hk : k ≤ N) :
    k ≤ (univ.filter fun j => b1Kth f k ≤ f j).card := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · have : k = 0 := by omega
    rw [this]; exact Nat.zero_le _
  obtain ⟨i, hi, he⟩ := b1Kth_mem (f := f) hk hN
  rw [he]; exact hi

lemma b1Kth_lt_count {f : Fin N → ℝ} {k : ℕ} (hk : 1 ≤ k) :
    (univ.filter fun j => b1Kth f k < f j).card < k := by
  by_contra hcon
  push Not at hcon
  set J := univ.filter fun j => b1Kth f k < f j with hJ
  have hJne : J.Nonempty := card_pos.1 (lt_of_lt_of_le hk hcon)
  obtain ⟨j0, hj0J, hj0⟩ := exists_min_image J f hJne
  have hmem : j0 ∈ univ.filter fun i => k ≤ (univ.filter fun j => f i ≤ f j).card := by
    refine mem_filter.2 ⟨mem_univ _, le_trans hcon (card_le_card fun j hj => ?_)⟩
    exact mem_filter.2 ⟨mem_univ _, hj0 j hj⟩
  have hle : f j0 ≤ b1Kth f k := le_sup'OrZero hmem
  exact absurd (mem_filter.1 hj0J).2 (not_lt.2 hle)

lemma b1Kth_le_max {f : Fin N → ℝ} {k : ℕ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, f i ≤ M) :
    b1Kth f k ≤ M :=
  sup'OrZero_le hM0 fun i _ => hM i

lemma b1_YMinR_le (w : Param N) (r : State N) (i : Fin N) : b1YMinR w r ≤ clamp01 (w r i) := by
  rw [b1YMinR, dite_eq_left ⟨i, mem_univ i⟩]; exact inf'_le _ (mem_univ i)

lemma b1_le_YMaxR (w : Param N) (r : State N) (i : Fin N) : clamp01 (w r i) ≤ b1YMaxR w r :=
  le_sup'OrZero (f := fun i => clamp01 (w r i)) (mem_univ i)

lemma b1_YMaxR_le_one (w : Param N) (r : State N) : b1YMaxR w r ≤ 1 :=
  sup'OrZero_le zero_le_one fun _ _ => clamp01_le_one _

lemma b1_YMinR_nonneg (w : Param N) (r : State N) : 0 ≤ b1YMinR w r := by
  unfold b1YMinR
  split_ifs with h
  · exact le_inf' _ _ fun i _ => clamp01_nonneg _
  · exact zero_le_one

lemma b1_YTopR_le_YMaxR (w : Param N) (r : State N) (ε : ℝ) : b1YTopR w r ε ≤ b1YMaxR w r := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    unfold b1YTopR b1Kth b1YMaxR
    simp [sup'OrZero]
  · exact b1Kth_le_max (le_trans (clamp01_nonneg _) (b1_le_YMaxR w r ⟨0, hN⟩))
      fun i => b1_le_YMaxR w r i

/-- `y_top ≥ y_min` as soon as `⌈εN⌉₊ ≤ N`. -/
lemma b1_YMinR_le_YTopR (w : Param N) (r : State N) {ε : ℝ} (hN : 0 < N)
    (hk : ⌈ε * N⌉₊ ≤ N) : b1YMinR w r ≤ b1YTopR w r ε := by
  obtain ⟨i, -, he⟩ := b1Kth_mem (f := fun i => clamp01 (w r i)) hk hN
  unfold b1YTopR
  rw [he]
  exact b1_YMinR_le w r i

/-! ## 4. Balls and the sensitive rows -/

/-- The Hamming ball of radius `ρ` around `r`. -/
def ballR (r : State N) (ρ : ℕ) : Finset (State N) := univ.filter fun r' => ham r r' ≤ ρ

/-- The sensitive rows `Sens(r0) = Ball(r0, 4) ∪ Ball(s, 2)` (the data `F`, never resampled). -/
def sensRows (s r0 : State N) : Finset (State N) := ballR r0 4 ∪ ballR s 2

lemma mem_ballR {r r' : State N} {ρ : ℕ} : r' ∈ ballR r ρ ↔ ham r r' ≤ ρ := by
  simp [ballR]

lemma b1_ham_self (r : State N) : ham r r = 0 := by simp [ham]

lemma b1_ham_comm (r r' : State N) : ham r r' = ham r' r := by
  unfold ham; congr 1; ext j; simp [ne_comm]

lemma self_mem_ballR (r : State N) (ρ : ℕ) : r ∈ ballR r ρ := by
  rw [mem_ballR, b1_ham_self]; exact Nat.zero_le _

lemma tc_mem_sensRows (s r0 : State N) : r0 ∈ sensRows s r0 :=
  mem_union_left _ (self_mem_ballR r0 4)

lemma s_mem_sensRows (s r0 : State N) : s ∈ sensRows s r0 :=
  mem_union_right _ (self_mem_ballR s 2)

/-- The `K'`-subcube through `t` lies in the ball of radius `|K'|` around `t`. -/
lemma b1_agree_compl_subset_ballR (t : State N) (K' : Finset (Fin N)) :
    agree K'ᶜ t ⊆ ballR t K'.card := by
  intro r hr
  rw [mem_ballR]
  refine card_le_card fun j hj => ?_
  by_contra hjK
  exact (mem_filter.1 hj).2 ((mem_agree.1 hr j (mem_compl.2 hjK))).symm

lemma b1_agree_compl_subset_sensRows (s t : State N) {K' : Finset (Fin N)} (hK : K'.card ≤ 4) :
    agree K'ᶜ t ⊆ sensRows s t := fun _ hr =>
  mem_union_left _ (mem_ballR.2 (le_trans (mem_ballR.1 (b1_agree_compl_subset_ballR t K' hr)) hK))

/-! ## 5. The events `B1w` and `SmallW` in flipped coordinates -/

/-- B1 in flipped coordinates. -/
def B1w (N : ℕ) (s : State N) : Set (Param N) := {w | flipP s w ∈ caseB1 N s}

/-- The bad event inside B1 in flipped coordinates. -/
def SmallW (N : ℕ) (s : State N) : Set (Param N) := {w | flipP s w ∈ smallPhiB1 N s}

lemma B1w_eq_preimage (s : State N) : B1w N s = flipE s ⁻¹' caseB1 N s := rfl

lemma SmallW_eq_preimage (s : State N) : SmallW N s = flipE s ⁻¹' smallPhiB1 N s := rfl

lemma SmallW_subset_B1w (s : State N) : SmallW N s ⊆ B1w N s := fun _ h => h.1

lemma b1_mem_cube_of_flipP {s : State N} {w : Param N} (h : flipP s w ∈ cube N) : w ∈ cube N := by
  have := flipP_cube h s
  rwa [flipP_invol s w] at this

lemma B1w_subset_cube (s : State N) : B1w N s ⊆ cube N := fun _ h => b1_mem_cube_of_flipP h.1

/-- `cubeM N (B1w N s) = volume (caseB1 N s)` (flip invariance). -/
theorem cubeM_B1w (s : State N) : cubeM N (B1w N s) = volume (caseB1 N s) := by
  rw [← volume_cube_inter, Set.inter_eq_right.2 (B1w_subset_cube s), B1w_eq_preimage,
    (mp_flipE s).measure_preimage_equiv]

theorem cubeM_SmallW (s : State N) : cubeM N (SmallW N s) = volume (smallPhiB1 N s) := by
  rw [← volume_cube_inter,
    Set.inter_eq_right.2 ((SmallW_subset_B1w s).trans (B1w_subset_cube s)), SmallW_eq_preimage,
    (mp_flipE s).measure_preimage_equiv]

theorem cubeM_SmallW_inter (s : State N) :
    cubeM N (SmallW N s ∩ B1w N s) = volume (smallPhiB1 N s) := by
  rw [Set.inter_eq_left.2 (SmallW_subset_B1w s), cubeM_SmallW]

/-- `isComplex_univ_iff` restated for `caseB1`. -/
theorem mem_caseB1_iff {s : State N} {z : Param N} :
    z ∈ caseB1 N s ↔ z ∈ cube N ∧
      ∀ S : Finset (Fin N), S ≠ univ → S.Nonempty → phi z s S < phi z s univ := by
  unfold caseB1
  rw [Set.mem_ofPred_eq, isComplex_univ_iff]
  rfl

theorem mem_B1w_iff {s : State N} {w : Param N} :
    w ∈ B1w N s ↔ flipP s w ∈ cube N ∧
      ∀ S : Finset (Fin N), S ≠ univ → S.Nonempty →
        phi (flipP s w) s S < phi (flipP s w) s univ :=
  mem_caseB1_iff

/-- On B1 the whole substrate has positive `φ_s` (`N ≥ 2`, a singleton is a proper candidate). -/
theorem caseB1_subset_univPos (hN : 2 ≤ N) (s : State N) : caseB1 N s ⊆ univPos N s := by
  intro z hz
  obtain ⟨hcube, h⟩ := mem_caseB1_iff.1 hz
  refine ⟨hcube, ?_⟩
  have h0 : (0 : ℕ) < N := by omega
  have hne : ({⟨0, h0⟩} : Finset (Fin N)) ≠ univ := by
    intro he
    have : (⟨1, by omega⟩ : Fin N) ∈ ({⟨0, h0⟩} : Finset (Fin N)) := he ▸ mem_univ _
    simp [Fin.ext_iff] at this
  exact lt_of_le_of_lt (sysPhi_nonneg _ _ _ _) (h _ hne (singleton_nonempty _))

/-! ## 6. Measurability -/

section Meas

open scoped Classical

variable {X : Type*} [MeasurableSpace X]

lemma b1_measurable_inf' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → X → ℝ}
    (hf : ∀ i ∈ s, Measurable (f i)) : Measurable fun x => s.inf' hs fun i => f i x := by
  have heq : (fun x => s.inf' hs fun i => f i x) = fun x => -(s.sup' hs fun i => -f i x) := by
    funext x
    refine le_antisymm ?_ (le_inf' _ _ fun i hi => ?_)
    · rw [le_neg]
      exact sup'_le _ _ fun i hi => neg_le_neg (inf'_le _ hi)
    · rw [neg_le]
      exact le_sup' (fun i => -f i x) hi
  have h2 : (fun x => s.sup' hs fun i => -f i x) = s.sup' hs (fun i x => -f i x) := by
    funext x; rw [Finset.sup'_apply]
  rw [heq]
  refine Measurable.neg ?_
  rw [h2]
  exact Finset.measurable_sup' hs fun i hi => (hf i hi).neg

/-- The set where a `Finset.filter` over a finite type takes a given value is measurable. -/
lemma b1_measurableSet_filter_eq {α : Type*} [Fintype α] {P : X → α → Prop}
    [∀ x, DecidablePred (P x)] (hP : ∀ a, MeasurableSet {x | P x a}) (A : Finset α) :
    MeasurableSet {x | univ.filter (P x) = A} := by
  have h : {x | univ.filter (P x) = A} = ⋂ a, {x | P x a ↔ a ∈ A} := by
    ext x
    simp [Finset.ext_iff]
  rw [h]
  refine MeasurableSet.iInter fun a => ?_
  by_cases ha : a ∈ A
  · convert hP a using 1
    ext x; simp [ha]
  · convert (hP a).compl using 1
    ext x; simp [ha]

lemma b1_measurableSet_card_filter_ge {α : Type*} [Fintype α] {P : X → α → Prop}
    [∀ x, DecidablePred (P x)] (hP : ∀ a, MeasurableSet {x | P x a}) (k : ℕ) :
    MeasurableSet {x | k ≤ (univ.filter (P x)).card} := by
  have h : {x | k ≤ (univ.filter (P x)).card} =
      ⋃ A : Finset α, (if k ≤ A.card then {x | univ.filter (P x) = A} else ∅) := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      have hx' : k ≤ (univ.filter (P x)).card := hx
      refine ⟨univ.filter (P x), ?_⟩
      rw [ite_eq_left hx']
      rfl
    · rintro ⟨A, hA⟩
      split_ifs at hA with hk
      · have hA' : univ.filter (P x) = A := hA
        show k ≤ (univ.filter (P x)).card
        rw [hA']; exact hk
      · exact absurd hA (Set.notMem_empty x)
  rw [h]
  refine MeasurableSet.iUnion fun A => ?_
  split_ifs
  · exact b1_measurableSet_filter_eq hP A
  · exact MeasurableSet.empty

lemma b1_measurableSet_argmax_eq {α : Type*} [Fintype α] {f : X → α → ℝ}
    (hf : ∀ a, Measurable fun x => f x a) (A : Finset α) :
    MeasurableSet {x | argmaxSet (f x) = A} := by
  unfold argmaxSet
  refine b1_measurableSet_filter_eq (fun a => ?_) A
  have : {x | ∀ b, f x b ≤ f x a} = ⋂ b, {x | f x b ≤ f x a} := by ext x; simp
  rw [this]
  exact MeasurableSet.iInter fun b => measurableSet_le (hf b) (hf a)

lemma b1_measurableSet_argmin_eq {α : Type*} [Fintype α] {f : X → α → ℝ}
    (hf : ∀ a, Measurable fun x => f x a) (A : Finset α) :
    MeasurableSet {x | argminSet (f x) = A} := by
  unfold argminSet
  refine b1_measurableSet_filter_eq (fun a => ?_) A
  have : {x | ∀ b, f x a ≤ f x b} = ⋂ b, {x | f x a ≤ f x b} := by ext x; simp
  rw [this]
  exact MeasurableSet.iInter fun b => measurableSet_le (hf a) (hf b)

lemma b1_measurableSet_mem_argmax {α : Type*} [Fintype α] {f : X → α → ℝ}
    (hf : ∀ a, Measurable fun x => f x a) (a : α) :
    MeasurableSet {x | a ∈ argmaxSet (f x)} := by
  have : {x | a ∈ argmaxSet (f x)} = ⋂ b, {x | f x b ≤ f x a} := by
    ext x; simp [mem_argmaxSet]
  rw [this]
  exact MeasurableSet.iInter fun b => measurableSet_le (hf b) (hf a)

lemma b1_measurableSet_mem_argmin {α : Type*} [Fintype α] {f : X → α → ℝ}
    (hf : ∀ a, Measurable fun x => f x a) (a : α) :
    MeasurableSet {x | a ∈ argminSet (f x)} := by
  have : {x | a ∈ argminSet (f x)} = ⋂ b, {x | f x a ≤ f x b} := by
    ext x; simp [mem_argminSet]
  rw [this]
  exact MeasurableSet.iInter fun b => measurableSet_le (hf a) (hf b)

lemma b1_measurable_sup'OrZero_const {α : Type*} (A : Finset α) {g : X → α → ℝ}
    (hg : ∀ a, Measurable fun x => g x a) : Measurable fun x => sup'OrZero A (g x) := by
  by_cases hne : A.Nonempty
  · have h2 : (fun x => sup'OrZero A (g x)) = A.sup' hne (fun a x => g x a) := by
      funext x; rw [sup'OrZero, dite_eq_left hne, Finset.sup'_apply]
    rw [h2]; exact Finset.measurable_sup' hne fun a _ => hg a
  · have h2 : (fun x => sup'OrZero A (g x)) = fun _ => 0 := by
      funext x; simp [sup'OrZero, hne]
    rw [h2]; exact measurable_const

lemma b1_measurable_sup'OrZero {α : Type*} [Fintype α] {F : X → Finset α}
    (hF : ∀ A, MeasurableSet {x | F x = A}) {g : X → α → ℝ} (hg : ∀ a, Measurable fun x => g x a) :
    Measurable fun x => sup'OrZero (F x) (g x) := by
  have h2 : (fun x => sup'OrZero (F x) (g x)) =
      fun x => ∑ A : Finset α, if F x = A then sup'OrZero A (g x) else 0 := by
    funext x; simp
  rw [h2]
  exact Finset.measurable_sum _ fun A _ =>
    Measurable.ite (hF A) (b1_measurable_sup'OrZero_const A hg) measurable_const

lemma b1_measurableSet_product_eq {α β : Type*} [Fintype α] [Fintype β] {F : X → Finset α}
    {G : X → Finset β} (hF : ∀ A, MeasurableSet {x | F x = A})
    (hG : ∀ B, MeasurableSet {x | G x = B}) (C : Finset (α × β)) :
    MeasurableSet {x | F x ×ˢ G x = C} := by
  have h : {x | F x ×ˢ G x = C} = ⋃ p : Finset α × Finset β,
      (if p.1 ×ˢ p.2 = C then {x | F x = p.1} ∩ {x | G x = p.2} else ∅) := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      have hx' : F x ×ˢ G x = C := hx
      refine ⟨(F x, G x), ?_⟩
      dsimp only
      rw [ite_eq_left hx']
      exact ⟨rfl, rfl⟩
    · rintro ⟨p, hp⟩
      split_ifs at hp with hpC
      · obtain ⟨h1, h2⟩ := hp
        have h1' : F x = p.1 := h1
        have h2' : G x = p.2 := h2
        show F x ×ˢ G x = C
        rw [h1', h2']; exact hpC
      · exact absurd hp (Set.notMem_empty x)
  rw [h]
  refine MeasurableSet.iUnion fun p => ?_
  split_ifs
  · exact (hF _).inter (hG _)
  · exact MeasurableSet.empty

lemma b1_measurable_logb {f : X → ℝ} (hf : Measurable f) :
    Measurable fun x => Real.logb 2 (f x) := by
  unfold Real.logb; exact hf.log.div_const _

lemma b1_measurable_pos {f : X → ℝ} (hf : Measurable f) : Measurable fun x => pos (f x) := by
  unfold pos; exact measurable_const.max hf

/-! ### The system level is measurable in the parameters -/

lemma b1m_coord (r : State N) (i : Fin N) : Measurable fun z : Param N => z r i :=
  (measurable_pi_apply i).comp (measurable_pi_apply r)

lemma b1m_clamp (r : State N) (i : Fin N) : Measurable fun z : Param N => clamp01 (z r i) := by
  unfold clamp01; exact measurable_const.max (measurable_const.min (b1m_coord r i))

lemma b1m_prob (i : Fin N) (r : State N) (b : Bool) :
    Measurable fun z : Param N => (tpmOf z).prob i r b := by
  cases b
  · show Measurable fun z : Param N =>
      if false = true then clamp01 (z r i) else 1 - clamp01 (z r i)
    simpa using (b1m_clamp r i).const_sub 1
  · show Measurable fun z : Param N =>
      if true = true then clamp01 (z r i) else 1 - clamp01 (z r i)
    simpa using b1m_clamp r i

lemma b1m_fullProb (v t : State N) : Measurable fun z : Param N => fullProb (tpmOf z) v t := by
  unfold fullProb; exact Finset.measurable_prod _ fun i _ => b1m_prob i v (t i)

lemma b1m_effUnit (M : Finset (Fin N)) (m : State N) (i : Fin N) (b : Bool) :
    Measurable fun z : Param N => effUnit (tpmOf z) M m i b := by
  unfold effUnit
  exact (Finset.measurable_sum _ fun r _ => b1m_prob i r b).div_const _

lemma b1m_sysEffProb (S : Finset (Fin N)) (u s t : State N) :
    Measurable fun z : Param N => sysEffProb (tpmOf z) S u s t := by
  unfold sysEffProb; exact Finset.measurable_prod _ fun i _ => b1m_prob _ _ _

lemma b1m_sysUncEff (S : Finset (Fin N)) (u t : State N) :
    Measurable fun z : Param N => sysUncEff (tpmOf z) S u t := by
  unfold sysUncEff avgOverStates
  exact (Finset.measurable_sum _ fun s _ => b1m_sysEffProb S u s t).div_const _

lemma b1m_sysIiE (S : Finset (Fin N)) (u s t : State N) :
    Measurable fun z : Param N => sysIiE (tpmOf z) S u s t := by
  unfold sysIiE
  exact (b1m_sysEffProb S u s t).mul
    (b1_measurable_logb ((b1m_sysEffProb S u s t).div (b1m_sysUncEff S u t)))

lemma b1m_bgWeight (S : Finset (Fin N)) (u w : State N) :
    Measurable fun z : Param N => bgWeight (tpmOf z) S u w := by
  unfold bgWeight
  exact ((Finset.measurable_sum _ fun s _ => b1m_fullProb _ _).div_const _).div
    (Finset.measurable_sum _ fun v _ => b1m_fullProb _ _)

lemma b1m_sysCauseProb (S : Finset (Fin N)) (u s t : State N) :
    Measurable fun z : Param N => sysCauseProb (tpmOf z) S u s t := by
  unfold sysCauseProb
  exact Finset.measurable_prod _ fun i _ =>
    (Finset.measurable_sum _ fun w _ => (b1m_prob _ _ _).mul (b1m_bgWeight S u w)).div_const _

lemma b1m_sysUncCause (S : Finset (Fin N)) (u s : State N) :
    Measurable fun z : Param N => sysUncCause (tpmOf z) S u s := by
  unfold sysUncCause avgOverStates
  exact (Finset.measurable_sum _ fun t _ => b1m_sysCauseProb S u s t).div_const _

lemma b1m_sysBackCause (S : Finset (Fin N)) (u s t : State N) :
    Measurable fun z : Param N => sysBackCause (tpmOf z) S u s t := by
  unfold sysBackCause
  exact (b1m_sysCauseProb S u s t).div (measurable_const.mul (b1m_sysUncCause S u s))

lemma b1m_sysIiC (S : Finset (Fin N)) (u s t : State N) :
    Measurable fun z : Param N => sysIiC (tpmOf z) S u s t := by
  unfold sysIiC
  exact (b1m_sysBackCause S u s t).mul
    (b1_measurable_logb ((b1m_sysCauseProb S u s t).div (b1m_sysUncCause S u s)))

lemma b1m_sysPartEffProb (S : Finset (Fin N)) (u : State N) (θ : SysPartition N S)
    (s t : State N) : Measurable fun z : Param N => sysPartEffProb (tpmOf z) S u θ s t := by
  unfold sysPartEffProb; exact Finset.measurable_prod _ fun j _ => b1m_effUnit _ _ _ _

lemma b1m_sysPartCauseProb (S : Finset (Fin N)) (u : State N) (θ : SysPartition N S)
    (s t : State N) : Measurable fun z : Param N => sysPartCauseProb (tpmOf z) S u θ s t := by
  unfold sysPartCauseProb
  exact Finset.measurable_prod _ fun j _ =>
    (Finset.measurable_sum _ fun w _ =>
      (b1m_effUnit _ _ _ _).mul (b1m_bgWeight S u w)).div_const _

lemma b1m_sysPhiE (S : Finset (Fin N)) (u : State N) (θ : SysPartition N S) (s t : State N) :
    Measurable fun z : Param N => sysPhiE (tpmOf z) S u θ s t := by
  unfold sysPhiE
  exact (b1m_sysEffProb S u s t).mul (b1_measurable_pos (b1_measurable_logb
    ((b1m_sysEffProb S u s t).div (b1m_sysPartEffProb S u θ s t))))

lemma b1m_sysPhiC (S : Finset (Fin N)) (u : State N) (θ : SysPartition N S) (s t : State N) :
    Measurable fun z : Param N => sysPhiC (tpmOf z) S u θ s t := by
  unfold sysPhiC
  exact (b1m_sysBackCause S u s t).mul (b1_measurable_pos (b1_measurable_logb
    ((b1m_sysCauseProb S u s t).div (b1m_sysPartCauseProb S u θ s t))))

lemma b1m_sysPhiAt (S : Finset (Fin N)) (u : State N) (θ : SysPartition N S)
    (s tc te : State N) : Measurable fun z : Param N => sysPhiAt (tpmOf z) S u θ s tc te := by
  unfold sysPhiAt; exact (b1m_sysPhiC S u θ s tc).min (b1m_sysPhiE S u θ s te)

lemma b1m_normalizedSysPhiAt (S : Finset (Fin N)) (u : State N) (θ : SysPartition N S)
    (s tc te : State N) :
    Measurable fun z : Param N => normalizedSysPhiAt (tpmOf z) S u θ s tc te := by
  unfold normalizedSysPhiAt; exact (b1m_sysPhiAt S u θ s tc te).div_const _

lemma b1m_sysMipSetAt_eq (S : Finset (Fin N)) (u s tc te : State N)
    (A : Finset (SysPartition N S)) :
    MeasurableSet {z : Param N | sysMipSetAt (tpmOf z) S u s tc te = A} := by
  unfold sysMipSetAt
  exact b1_measurableSet_argmin_eq (fun θ => b1m_normalizedSysPhiAt S u θ s tc te) A

lemma b1m_sysPhiOfState (S : Finset (Fin N)) (u s tc te : State N) :
    Measurable fun z : Param N => sysPhiOfState (tpmOf z) S u s tc te := by
  unfold sysPhiOfState
  exact b1_measurable_sup'OrZero (b1m_sysMipSetAt_eq S u s tc te)
    fun θ => b1m_sysPhiAt S u θ s tc te

lemma b1m_sysMaxCauseStates_eq (S : Finset (Fin N)) (u s : State N) (A : Finset (State N)) :
    MeasurableSet {z : Param N | sysMaxCauseStates (tpmOf z) S u s = A} :=
  b1_measurableSet_argmax_eq (fun t => b1m_sysIiC S u s t) A

lemma b1m_sysMaxEffStates_eq (S : Finset (Fin N)) (u s : State N) (A : Finset (State N)) :
    MeasurableSet {z : Param N | sysMaxEffStates (tpmOf z) S u s = A} :=
  b1_measurableSet_argmax_eq (fun t => b1m_sysIiE S u s t) A

lemma b1m_mem_sysMaxCauseStates (S : Finset (Fin N)) (u s t : State N) :
    MeasurableSet {z : Param N | t ∈ sysMaxCauseStates (tpmOf z) S u s} :=
  b1_measurableSet_mem_argmax (fun t => b1m_sysIiC S u s t) t

lemma b1m_mem_sysMaxEffStates (S : Finset (Fin N)) (u s t : State N) :
    MeasurableSet {z : Param N | t ∈ sysMaxEffStates (tpmOf z) S u s} :=
  b1_measurableSet_mem_argmax (fun t => b1m_sysIiE S u s t) t

lemma b1m_mem_sysMipSetAt (S : Finset (Fin N)) (u s tc te : State N) (θ : SysPartition N S) :
    MeasurableSet {z : Param N | θ ∈ sysMipSetAt (tpmOf z) S u s tc te} :=
  b1_measurableSet_mem_argmin (fun θ => b1m_normalizedSysPhiAt S u θ s tc te) θ

lemma b1m_sysPhi (S : Finset (Fin N)) (u s : State N) :
    Measurable fun z : Param N => sysPhi (tpmOf z) S u s := by
  unfold sysPhi
  exact b1_measurable_sup'OrZero
    (b1_measurableSet_product_eq (b1m_sysMaxCauseStates_eq S u s)
      (b1m_sysMaxEffStates_eq S u s))
    fun p => b1m_sysPhiOfState S u s p.1 p.2

/-- **`φ_s` is a measurable function of the parameters.** -/
theorem b1_measurable_phi (s : State N) (S : Finset (Fin N)) :
    Measurable fun z : Param N => phi z s S :=
  b1m_sysPhi S s s

theorem measurableSet_caseB1 (s : State N) : MeasurableSet (caseB1 N s) := by
  have h : caseB1 N s = cube N ∩ ⋂ S : Finset (Fin N),
      (if S ≠ univ ∧ S.Nonempty then {z | phi z s S < phi z s univ} else Set.univ) := by
    ext z
    rw [mem_caseB1_iff]
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    refine and_congr_right fun _ => forall_congr' fun S => ?_
    split_ifs with hS
    · exact ⟨fun h => h hS.1 hS.2, fun h _ _ => h⟩
    · simp only [Set.mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ hS
  rw [h]
  refine measurableSet_cube.inter (MeasurableSet.iInter fun S => ?_)
  split_ifs
  · exact measurableSet_lt (b1_measurable_phi s S) (b1_measurable_phi s univ)
  · exact MeasurableSet.univ

/-- **`B1w` is measurable.** -/
theorem measurableSet_B1w (s : State N) : MeasurableSet (B1w N s) :=
  (mp_flipP s).measurable (measurableSet_caseB1 s)

/-! ### Statistics of the rows -/

lemma b1m_Pw (r : State N) : Measurable fun w : Param N => Pw w r :=
  Finset.measurable_prod _ fun i _ => b1m_clamp r i

lemma b1m_Zs : Measurable fun w : Param N => Zs w :=
  Finset.measurable_sum _ fun r _ => b1m_Pw r

lemma b1m_XMW (M : Finset (Fin N)) (r : State N) : Measurable fun w : Param N => XMW w M r :=
  Finset.measurable_sum _ fun i _ => (b1m_clamp r i).log.neg

lemma b1m_XW (r : State N) : Measurable fun w : Param N => XW w r := b1m_XMW univ r

theorem measurableSet_tcRow_eq (r0 : State N) :
    MeasurableSet {w : Param N | tcRow w = r0} := by
  have h : {w : Param N | tcRow w = r0} = (⋂ r, {w | Pw w r ≤ Pw w r0}) ∩
      ⋂ r, (if b1Idx r < b1Idx r0 then {w | Pw w r < Pw w r0} else Set.univ) := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    rw [Set.mem_ofPred_eq, tcRow_eq_iff]
    refine and_congr Iff.rfl (forall_congr' fun r => ?_)
    split_ifs with hr
    · exact ⟨fun h => h hr, fun h _ => h⟩
    · simp only [Set.mem_univ, iff_true]; intro h; exact absurd h hr
  rw [h]
  refine (MeasurableSet.iInter fun r => measurableSet_le (b1m_Pw r) (b1m_Pw r0)).inter
    (MeasurableSet.iInter fun r => ?_)
  split_ifs
  · exact measurableSet_lt (b1m_Pw r) (b1m_Pw r0)
  · exact MeasurableSet.univ

/-- A function evaluated at `tcRow w` is measurable if it is for every fixed row. -/
lemma b1_measurable_at_tcRow {g : Param N → State N → ℝ} (hg : ∀ r, Measurable fun w => g w r) :
    Measurable fun w => g w (tcRow w) := by
  have h2 : (fun w => g w (tcRow w)) = fun w => ∑ r0, if tcRow w = r0 then g w r0 else 0 := by
    funext w; simp
  rw [h2]
  exact Finset.measurable_sum _ fun r0 _ =>
    Measurable.ite (measurableSet_tcRow_eq r0) (hg r0) measurable_const

/-- A predicate evaluated at `tcRow w` defines a measurable set if it does for every fixed row. -/
lemma b1_measurableSet_at_tcRow {P : Param N → State N → Prop}
    (hP : ∀ r, MeasurableSet {w | P w r}) : MeasurableSet {w | P w (tcRow w)} := by
  have h : {w | P w (tcRow w)} = ⋃ r0, {w | tcRow w = r0} ∩ {w | P w r0} := by
    ext w
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨tcRow w, rfl, h⟩, fun ⟨r0, h1, h2⟩ => by
      have h1' : tcRow w = r0 := h1
      show P w (tcRow w)
      rw [h1']; exact h2⟩
  rw [h]
  exact MeasurableSet.iUnion fun r0 => (measurableSet_tcRow_eq r0).inter (hP r0)

lemma b1m_betaW : Measurable fun w : Param N => betaW w :=
  b1_measurable_at_tcRow (g := fun w r => Pw w r / Zs w) fun r => (b1m_Pw r).div b1m_Zs

lemma b1m_YMinR (r : State N) : Measurable fun w : Param N => b1YMinR w r := by
  unfold b1YMinR
  by_cases h : (univ : Finset (Fin N)).Nonempty
  · simp only [h, dite_true]
    exact b1_measurable_inf' h (f := fun (i : Fin N) (w : Param N) => clamp01 (w r i))
      fun i _ => b1m_clamp r i
  · simp only [h, dite_false]; exact measurable_const

lemma b1m_YMaxR (r : State N) : Measurable fun w : Param N => b1YMaxR w r :=
  b1_measurable_sup'OrZero_const univ fun i => b1m_clamp r i

lemma b1m_Kth {f : X → Fin N → ℝ} (hf : ∀ i, Measurable fun x => f x i) (k : ℕ) :
    Measurable fun x => b1Kth (f x) k := by
  unfold b1Kth
  refine b1_measurable_sup'OrZero (fun A => b1_measurableSet_filter_eq (fun i => ?_) A) hf
  exact b1_measurableSet_card_filter_ge (fun j => measurableSet_le (hf i) (hf j)) k

lemma b1m_YTopR (r : State N) (ε : ℝ) : Measurable fun w : Param N => b1YTopR w r ε := by
  unfold b1YTopR
  exact b1m_Kth (f := fun (w : Param N) (i : Fin N) => clamp01 (w r i)) (fun i => b1m_clamp r i) _

lemma b1m_xE (s : State N) (k : Fin N) : Measurable fun w : Param N => xE w s k :=
  (b1m_clamp s k).max ((b1m_clamp s k).const_sub 1)

lemma b1m_eE (s : State N) : Measurable fun w : Param N => eE w s :=
  Finset.measurable_prod _ fun k _ => b1m_xE s k

lemma b1m_HalfW (j : Fin N) (b : Bool) : Measurable fun w : Param N => b1HalfW w j b :=
  (Finset.measurable_sum _ fun r _ => b1m_clamp r j).div_const _

lemma b1m_qW (s : State N) (S : Finset (Fin N)) (j : Fin N) (b : Bool) :
    Measurable fun w : Param N => qW w s S j b := by
  unfold qW
  refine (Finset.measurable_sum _ fun r _ => ?_).div_const _
  split_ifs
  · exact b1m_clamp r j
  · exact (b1m_clamp r j).const_sub 1

lemma b1_measurableSet_teW_eq (s t : State N) : MeasurableSet {w : Param N | teW w s = t} := by
  have h : {w : Param N | teW w s = t} = ⋂ k, {w | teW w s k = t k} := by
    ext w; simp [funext_iff]
  rw [h]
  refine MeasurableSet.iInter fun k => ?_
  have hlt : MeasurableSet {w : Param N | 1 / 2 < clamp01 (w s k)} :=
    measurableSet_lt measurable_const (b1m_clamp s k)
  have hte : ∀ w : Param N, teW w s k = if 1 / 2 < clamp01 (w s k) then s k else !s k :=
    fun _ => rfl
  by_cases h1 : s k = t k <;> by_cases h2 : (!s k) = t k
  · rw [h1] at h2; simp at h2
  · convert hlt using 1; ext w
    simp only [Set.mem_ofPred_eq, hte]; split_ifs with hc <;> simp_all
  · convert hlt.compl using 1; ext w
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, hte]; split_ifs with hc <;> simp_all
  · exfalso; cases hs : s k <;> cases ht : t k <;> simp_all

lemma b1m_phU (s : State N) (j : Fin N) : Measurable fun w : Param N => phU w s j := by
  unfold phU
  refine Measurable.min ?_ ?_
  · refine b1_measurable_at_tcRow (g := fun w r => betaW w * pos (Real.logb 2
      (clamp01 (w r j) / b1HalfW w j (r j)))) fun r => ?_
    exact b1m_betaW.mul (b1_measurable_pos (b1_measurable_logb
      ((b1m_clamp r j).div (b1m_HalfW j (r j)))))
  · have h2 : (fun w : Param N => qW w s univ j (teW w s j)) = fun w =>
        if 1 / 2 < clamp01 (w s j) then qW w s univ j (s j) else qW w s univ j (!s j) := by
      funext w; unfold teW; split_ifs <;> rfl
    refine (b1m_eE s).mul (b1_measurable_pos (b1_measurable_logb ((b1m_xE s j).div ?_)))
    rw [h2]
    exact Measurable.ite (measurableSet_lt measurable_const (b1m_clamp s j)) (b1m_qW s univ j _)
      (b1m_qW s univ j _)

lemma b1m_phUMin (s : State N) : Measurable fun w : Param N => phUMin w s := by
  unfold phUMin
  by_cases h : (univ : Finset (Fin N)).Nonempty
  · simp only [h, dite_true]
    exact b1_measurable_inf' h (f := fun (j : Fin N) (w : Param N) => phU w s j)
      fun j _ => b1m_phU s j
  · simp only [h, dite_false]; exact measurable_const

lemma b1m_CutMean (t : State N) (K' : Finset (Fin N)) (i : Fin N) :
    Measurable fun w : Param N => b1CutMean w t K' i :=
  (Finset.measurable_sum _ fun r _ => b1m_clamp r i).div_const _

lemma b1m_CutG (t : State N) (K' : Finset (Fin N)) (i : Fin N) :
    Measurable fun w : Param N => b1CutG w t K' i :=
  (((b1m_clamp t i).div (b1m_CutMean t K' i)).log).min (((b1m_clamp t i).div_const _).log)

lemma b1_measurableSet_openCube : MeasurableSet (openCube N) := by
  have h : openCube N =
      ⋂ r : State N, ⋂ i : Fin N, (fun z : Param N => z r i) ⁻¹' Set.Ioo 0 1 := by
    ext z; simp [openCube]
  rw [h]
  exact MeasurableSet.iInter fun r => MeasurableSet.iInter fun i =>
    b1m_coord r i measurableSet_Ioo

lemma b1m_phi_flip (s : State N) (S : Finset (Fin N)) :
    Measurable fun w : Param N => phi (flipP s w) s S :=
  (b1_measurable_phi s S).comp (mp_flipP s).measurable

end Meas

/-! ## 7. The forced event, its `F`-projection, and the triple boundary -/

/-- **The `F`-part of `Forced`**: the conditions that read only the rows of `sensRows s r0`
(`r0` plays the role of `tc`). -/
structure B1FGood (N : ℕ) (s r0 : State N) (w : Param N) : Prop where
  /-- the sensitive entries lie in `(0, 1)` -/
  openRows : ∀ r ∈ sensRows s r0, ∀ i, w r i ∈ Set.Ioo (0 : ℝ) 1
  /-- tilt typicality (G12, C9): `X(tc) ≤ x0 N - 9 ln N` -/
  tilt : XW w r0 ≤ x0 * N - 9 * Real.log N
  /-- `d(tc, u) ≥ N/3` (C12) -/
  far : N ≤ 3 * ham r0 s
  /-- every entry of `tc` is at least `3/5` (a consequence of the stage-2 profile) -/
  yMin : b1YLo ≤ b1YMinR w r0
  /-- G13 (C10): `y_top ≥ 0.984 y_max` -/
  top : b1TopRatio * b1YMaxR w r0 ≤ b1YTopR w r0 b1Eps
  /-- positivity and tc-pattern uniqueness near `tc` for `1 ≤ |K'| ≤ 4` (C6, C7; Fable G5) -/
  posNear : ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 4 →
    b1PosC * N ≤ ∑ i, b1CutG w r0 K' i
  /-- retention of `tc` against every other sensitive row, for every deleted set of size `≤ d` -/
  ret : ∀ r ∈ sensRows s r0, r ≠ r0 → ∀ K : Finset (Fin N), K.card ≤ dFam N →
    XW w r0 + b1Eta * N < XMW w (univ \ K) r

/-- Sensitive-row data extended by `1` on the other rows. -/
noncomputable def b1Ext {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) : Param N :=
  fun r => if h : r ∈ sensRows s r0 then f ⟨r, h⟩ else fun _ => 1

/-- The sensitive-row data of `w`. -/
def b1Restr (s r0 : State N) (w : Param N) : sensRows s r0 → Fin N → ℝ := fun r => w r.1

/-- **`GoodF`**: the `F`-projection of `Forced ∩ {tcRow = r0}` (the data `f` of the rows of
`sensRows s r0` satisfying the `F`-part `B1FGood` of `Forced`). -/
def GoodF (N : ℕ) (s r0 : State N) : Set (sensRows s r0 → Fin N → ℝ) :=
  {f | B1FGood N s r0 (b1Ext f)}

/-- **`Forced`**: the conditions of Section 2, Layer II, that B1 forces except on an event of
probability `≤ 3 e^{-Rbad N}` (`B1_forced`). -/
structure Forced (N : ℕ) (s : State N) (w : Param N) : Prop where
  /-- all entries in `(0, 1)` (the complement is null) -/
  mem_open : w ∈ openCube N
  /-- the conditions on the sensitive rows around `tc` and `u` -/
  fgood : B1FGood N s (tcRow w) w
  /-- `1/2 ≤ Z ≤ 13` (G16) -/
  zs : 1 / 2 ≤ Zs w ∧ Zs w ≤ b1ZMax
  /-- tilt (G12): `β ≥ N^8 σ_N` -/
  beta : (N : ℝ) ^ 8 * sigN N ≤ betaW w
  /-- no near-tie heavy row (G9, C8, C11) -/
  noHeavy : ∀ r, r ≠ tcRow w → XW w (tcRow w) + b1Eta * N < XW w r
  /-- the stage-2 profile, cause and effect sides (steps 2-4): every single cut of `U` is above
  the triple level -/
  level : ∀ j, (1 - b1Eps) * levTrip * yTopW w b1Eps * betaW w ≤ phU w s j
  /-- the MIP of `U` (Tier 3): `φ_s(U) = min_j ph_j` -/
  mip : phi (flipP s w) s univ = phUMin w s
  /-- the maximal cause and effect states of `U` are `tc` and `te` -/
  states : sysMaxCauseStates (tpmOf (flipP s w)) univ s s = {tcRow w} ∧
    sysMaxEffStates (tpmOf (flipP s w)) univ s s = {teW w s}
  /-- no effect window (G2): for candidates with `|S| ≤ 4`, every effect-side partition value at a
  maximal effect state is `0` or at least `β` -/
  noEffWin : ∀ S : Finset (Fin N), S.card ≤ 4 →
    ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) S s s, ∀ θ : SysPartition N S,
      sysPhiE (tpmOf (flipP s w)) S s θ s te = 0 ∨
        betaW w ≤ sysPhiE (tpmOf (flipP s w)) S s θ s te

/-- **The triple boundary `∂`** (width `δ` in units of `β`): some triple has its `φ_s` within `δβ`
of `φ_s(U)`, or, at one of its maximal state pairs, a partition with a different cut count
whose normalised value is within `δβ` of the MIP ratio. -/
def bdry (N : ℕ) (s : State N) (δ : ℝ) : Set (Param N) :=
  {w | ∃ S : Finset (Fin N), S.card = 3 ∧
    (|phi (flipP s w) s S - phi (flipP s w) s univ| ≤ δ * betaW w ∨
      ∃ tc ∈ sysMaxCauseStates (tpmOf (flipP s w)) S s s,
      ∃ te ∈ sysMaxEffStates (tpmOf (flipP s w)) S s s,
      ∃ θ ∈ sysMipSetAt (tpmOf (flipP s w)) S s s tc te, ∃ θ' : SysPartition N S,
        sysCutCount θ' ≠ sysCutCount θ ∧
        normalizedSysPhiAt (tpmOf (flipP s w)) S s θ' s tc te ≤
          normalizedSysPhiAt (tpmOf (flipP s w)) S s θ s tc te + δ * betaW w)}

lemma bdry_mono {s : State N} {δ δ' : ℝ} (h : δ ≤ δ') : bdry N s δ ⊆ bdry N s δ' := by
  rintro w ⟨S, hS, h1 | ⟨tc, htc, te, hte, θ, hθ, θ', hcc, hle⟩⟩
  · exact ⟨S, hS, Or.inl (h1.trans (mul_le_mul_of_nonneg_right h (betaW_nonneg w)))⟩
  · refine ⟨S, hS, Or.inr ⟨tc, htc, te, hte, θ, hθ, θ', hcc, hle.trans ?_⟩⟩
    have := mul_le_mul_of_nonneg_right h (betaW_nonneg w)
    linarith

/-! ### Locality of the `F`-part -/

lemma b1_XMW_congr {w w' : Param N} {r : State N} (h : w' r = w r) (M : Finset (Fin N)) :
    XMW w' M r = XMW w M r := by
  unfold XMW; rw [h]

lemma b1_XW_congr {w w' : Param N} {r : State N} (h : w' r = w r) : XW w' r = XW w r :=
  b1_XMW_congr h univ

lemma b1_YMinR_congr {w w' : Param N} {r : State N} (h : w' r = w r) :
    b1YMinR w' r = b1YMinR w r := by
  unfold b1YMinR; rw [h]

lemma b1_YMaxR_congr {w w' : Param N} {r : State N} (h : w' r = w r) :
    b1YMaxR w' r = b1YMaxR w r := by
  unfold b1YMaxR; rw [h]

lemma b1_YTopR_congr {w w' : Param N} {r : State N} (h : w' r = w r) (ε : ℝ) :
    b1YTopR w' r ε = b1YTopR w r ε := by
  unfold b1YTopR; rw [h]

lemma b1_CutG_congr {w w' : Param N} {t : State N} {K' : Finset (Fin N)}
    (h : ∀ r ∈ agree K'ᶜ t, w' r = w r) (i : Fin N) : b1CutG w' t K' i = b1CutG w t K' i := by
  have ht : w' t = w t := h t (mem_agree.2 fun _ _ => rfl)
  have hm : b1CutMean w' t K' i = b1CutMean w t K' i := by
    unfold b1CutMean
    congr 1
    exact sum_congr rfl fun r hr => by rw [h r hr]
  unfold b1CutG
  rw [hm, ht]

/-- `B1FGood` only reads the sensitive rows. -/
theorem B1FGood.congr {s r0 : State N} {w w' : Param N} (h : ∀ r ∈ sensRows s r0, w' r = w r)
    (hw : B1FGood N s r0 w) : B1FGood N s r0 w' := by
  have h0 : w' r0 = w r0 := h r0 (tc_mem_sensRows s r0)
  refine ⟨fun r hr i => by rw [h r hr]; exact hw.openRows r hr i, ?_, hw.far, ?_, ?_, ?_, ?_⟩
  · rw [b1_XW_congr h0]; exact hw.tilt
  · rw [b1_YMinR_congr h0]; exact hw.yMin
  · rw [b1_YMaxR_congr h0, b1_YTopR_congr h0]; exact hw.top
  · intro K' hK' hK4
    rw [sum_congr rfl fun i _ =>
      b1_CutG_congr (fun r hr => h r (b1_agree_compl_subset_sensRows s r0 hK4 hr)) i]
    exact hw.posNear K' hK' hK4
  · intro r hr hne K hK
    rw [b1_XW_congr h0, b1_XMW_congr (h r hr)]
    exact hw.ret r hr hne K hK

lemma b1_Ext_Restr (s r0 : State N) (w : Param N) :
    ∀ r ∈ sensRows s r0, b1Ext (b1Restr s r0 w) r = w r := by
  intro r hr; simp [b1Ext, b1Restr, hr]

lemma b1_Ext_apply {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) {r : State N}
    (hr : r ∈ sensRows s r0) : b1Ext f r = f ⟨r, hr⟩ := by
  simp [b1Ext, hr]

theorem mem_GoodF_iff {s r0 : State N} {f : sensRows s r0 → Fin N → ℝ} :
    f ∈ GoodF N s r0 ↔ B1FGood N s r0 (b1Ext f) := Iff.rfl

/-- The sensitive data of `w` is in `GoodF` iff `w` satisfies the `F`-part. -/
theorem b1_restr_mem_GoodF_iff {s r0 : State N} {w : Param N} :
    b1Restr s r0 w ∈ GoodF N s r0 ↔ B1FGood N s r0 w :=
  ⟨fun h => B1FGood.congr (fun r hr => (b1_Ext_Restr s r0 w r hr).symm) h,
    fun h => B1FGood.congr (b1_Ext_Restr s r0 w) h⟩

/-- If `w'` agrees with the data `f` on the sensitive rows, then `f ∈ GoodF` iff `B1FGood w'`
(e.g. `w' = glue f g`). -/
theorem b1_mem_GoodF_iff_of_agree {s r0 : State N} {f : sensRows s r0 → Fin N → ℝ} {w' : Param N}
    (h : ∀ r (hr : r ∈ sensRows s r0), w' r = f ⟨r, hr⟩) :
    f ∈ GoodF N s r0 ↔ B1FGood N s r0 w' :=
  ⟨fun hf => B1FGood.congr (fun r hr => by rw [h r hr, b1_Ext_apply f hr]) hf,
    fun hw => B1FGood.congr (fun r hr => by rw [h r hr, b1_Ext_apply f hr]) hw⟩

/-! ### Consequences of `Forced` -/

namespace Forced

variable {s : State N} {w : Param N}

/-- `Forced ∩ {tcRow = r0}` projects into `GoodF`. -/
theorem restr_mem_goodF (h : Forced N s w) {r0 : State N} (hr : tcRow w = r0) :
    b1Restr s r0 w ∈ GoodF N s r0 := by
  subst hr; exact b1_restr_mem_GoodF_iff.2 h.fgood

lemma clamp_pos (h : Forced N s w) (r : State N) (i : Fin N) : 0 < clamp01 (w r i) := by
  rw [b1_clamp01_of_mem_Ioo (h.mem_open r i)]; exact (h.mem_open r i).1

/-- `tc` is the strict argmax of the row products. -/
lemma Pw_lt (h : Forced N s w) {r : State N} (hr : r ≠ tcRow w) :
    Pw w r < Pw w (tcRow w) := by
  rw [Pw_eq_exp_neg_XW (h.clamp_pos r), Pw_eq_exp_neg_XW (h.clamp_pos _)]
  refine Real.exp_lt_exp.2 (neg_lt_neg ?_)
  have h1 := h.noHeavy r hr
  have h2 : 0 ≤ b1Eta * N := by unfold b1Eta; positivity
  linarith

lemma tcRow_ne (h : Forced N s w) (hN : 1 ≤ N) : tcRow w ≠ s := by
  intro he
  have := h.fgood.far
  rw [he, b1_ham_self] at this
  omega

lemma beta_pos (h : Forced N s w) : 0 < betaW w := betaW_pos h.mem_open

/-- The value of `U` is above the triple level. -/
lemma level_le_phi (h : Forced N s w) (hN : 0 < N) :
    (1 - b1Eps) * levTrip * yTopW w b1Eps * betaW w ≤ phi (flipP s w) s univ := by
  rw [h.mip]; exact le_phUMin h.level (Or.inr hN)

end Forced

/-! ### Measurability of the events -/

section MeasEvents

open scoped Classical

variable {X : Type*} [MeasurableSpace X]

lemma b1_mset_forall {ι : Type*} [Countable ι] {Q : X → ι → Prop}
    (hQ : ∀ i, MeasurableSet {x | Q x i}) : MeasurableSet {x | ∀ i, Q x i} := by
  have : {x | ∀ i, Q x i} = ⋂ i, {x | Q x i} := by ext x; simp
  rw [this]; exact MeasurableSet.iInter hQ

lemma b1_mset_exists {ι : Type*} [Countable ι] {Q : X → ι → Prop}
    (hQ : ∀ i, MeasurableSet {x | Q x i}) : MeasurableSet {x | ∃ i, Q x i} := by
  have : {x | ∃ i, Q x i} = ⋃ i, {x | Q x i} := by ext x; simp
  rw [this]; exact MeasurableSet.iUnion hQ

lemma b1_mset_imp {P Q : X → Prop} (hP : MeasurableSet {x | P x}) (hQ : MeasurableSet {x | Q x}) :
    MeasurableSet {x | P x → Q x} := by
  have : {x | P x → Q x} = {x | P x}ᶜ ∪ {x | Q x} := by ext x; simp [imp_iff_not_or]
  rw [this]; exact hP.compl.union hQ

lemma b1_mset_and {P Q : X → Prop} (hP : MeasurableSet {x | P x}) (hQ : MeasurableSet {x | Q x}) :
    MeasurableSet {x | P x ∧ Q x} := hP.inter hQ

lemma b1_mset_or {P Q : X → Prop} (hP : MeasurableSet {x | P x}) (hQ : MeasurableSet {x | Q x}) :
    MeasurableSet {x | P x ∨ Q x} := hP.union hQ

/-- A predicate evaluated along a function with measurable fibres and countable range. -/
lemma b1_mset_at {Y : Type*} [Countable Y] {φ : X → Y} (hφ : ∀ y, MeasurableSet {x | φ x = y})
    {P : X → Y → Prop} (hP : ∀ y, MeasurableSet {x | P x y}) :
    MeasurableSet {x | P x (φ x)} := by
  have h : {x | P x (φ x)} = ⋃ y, {x | φ x = y} ∩ {x | P x y} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨φ x, rfl, h⟩, fun ⟨y, h1, h2⟩ => h1 ▸ h2⟩
  rw [h]; exact MeasurableSet.iUnion fun y => (hφ y).inter (hP y)

theorem measurableSet_B1FGood (s r0 : State N) :
    MeasurableSet {w : Param N | B1FGood N s r0 w} := by
  have h : {w : Param N | B1FGood N s r0 w} = {w | (∀ r, r ∈ sensRows s r0 → ∀ i,
      w r i ∈ Set.Ioo (0 : ℝ) 1) ∧ XW w r0 ≤ x0 * N - 9 * Real.log N ∧ N ≤ 3 * ham r0 s ∧
      b1YLo ≤ b1YMinR w r0 ∧ b1TopRatio * b1YMaxR w r0 ≤ b1YTopR w r0 b1Eps ∧
      (∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 4 → b1PosC * N ≤ ∑ i, b1CutG w r0 K' i) ∧
      ∀ r, r ∈ sensRows s r0 → r ≠ r0 → ∀ K : Finset (Fin N), K.card ≤ dFam N →
        XW w r0 + b1Eta * N < XMW w (univ \ K) r} := by
    ext w
    exact ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7⟩,
      fun ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩
  rw [h]
  refine b1_mset_and ?_ (b1_mset_and ?_ (b1_mset_and (MeasurableSet.const _) (b1_mset_and ?_
    (b1_mset_and ?_ (b1_mset_and ?_ ?_)))))
  · exact b1_mset_forall fun r => b1_mset_imp (MeasurableSet.const _) (b1_mset_forall fun i =>
      b1m_coord r i measurableSet_Ioo)
  · exact measurableSet_le (b1m_XW r0) measurable_const
  · exact measurableSet_le measurable_const (b1m_YMinR r0)
  · exact measurableSet_le (measurable_const.mul (b1m_YMaxR r0)) (b1m_YTopR r0 _)
  · exact b1_mset_forall fun K' => b1_mset_imp (MeasurableSet.const _) (b1_mset_imp
      (MeasurableSet.const _) (measurableSet_le measurable_const
        (Finset.measurable_sum _ fun i _ => b1m_CutG r0 K' i)))
  · exact b1_mset_forall fun r => b1_mset_imp (MeasurableSet.const _) (b1_mset_imp
      (MeasurableSet.const _) (b1_mset_forall fun K => b1_mset_imp (MeasurableSet.const _)
        (measurableSet_lt ((b1m_XW r0).add_const _) (b1m_XMW _ r))))

lemma b1_measurable_Ext (s r0 : State N) :
    Measurable (b1Ext : (sensRows s r0 → Fin N → ℝ) → Param N) := by
  refine measurable_pi_iff.2 fun r => ?_
  by_cases h : r ∈ sensRows s r0
  · simp only [b1Ext, h, dite_true]; exact measurable_pi_apply _
  · simp only [b1Ext, h, dite_false]; exact measurable_const

/-- **`GoodF` is measurable.** -/
theorem measurableSet_GoodF (s r0 : State N) : MeasurableSet (GoodF N s r0) :=
  b1_measurable_Ext s r0 (measurableSet_B1FGood s r0)

lemma b1m_yTopW (ε : ℝ) : Measurable fun w : Param N => yTopW w ε :=
  b1_measurable_at_tcRow (g := fun w r => b1YTopR w r ε) fun r => b1m_YTopR r ε

/-- **`Forced` is measurable.** -/
theorem measurableSet_Forced (s : State N) : MeasurableSet {w : Param N | Forced N s w} := by
  have hflip : Measurable (flipP s : Param N → Param N) := (mp_flipP s).measurable
  have h : {w : Param N | Forced N s w} = {w | w ∈ openCube N ∧ B1FGood N s (tcRow w) w ∧
      (1 / 2 ≤ Zs w ∧ Zs w ≤ b1ZMax) ∧ (N : ℝ) ^ 8 * sigN N ≤ betaW w ∧
      (∀ r, r ≠ tcRow w → XW w (tcRow w) + b1Eta * N < XW w r) ∧
      (∀ j, (1 - b1Eps) * levTrip * yTopW w b1Eps * betaW w ≤ phU w s j) ∧
      phi (flipP s w) s univ = phUMin w s ∧
      (sysMaxCauseStates (tpmOf (flipP s w)) univ s s = {tcRow w} ∧
        sysMaxEffStates (tpmOf (flipP s w)) univ s s = {teW w s}) ∧
      ∀ S : Finset (Fin N), S.card ≤ 4 →
        ∀ te, te ∈ sysMaxEffStates (tpmOf (flipP s w)) S s s → ∀ θ : SysPartition N S,
          sysPhiE (tpmOf (flipP s w)) S s θ s te = 0 ∨
            betaW w ≤ sysPhiE (tpmOf (flipP s w)) S s θ s te} := by
    ext w
    exact ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9⟩,
      fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩
  rw [h]
  refine b1_mset_and b1_measurableSet_openCube (b1_mset_and ?_ (b1_mset_and ?_ (b1_mset_and ?_
    (b1_mset_and ?_ (b1_mset_and ?_ (b1_mset_and ?_ (b1_mset_and ?_ ?_)))))))
  · exact b1_measurableSet_at_tcRow (P := fun w r => B1FGood N s r w) (measurableSet_B1FGood s)
  · exact b1_mset_and (measurableSet_le measurable_const b1m_Zs)
      (measurableSet_le b1m_Zs measurable_const)
  · exact measurableSet_le measurable_const b1m_betaW
  · exact b1_measurableSet_at_tcRow (P := fun w r0 => ∀ r, r ≠ r0 → XW w r0 + b1Eta * N < XW w r)
      fun r0 => b1_mset_forall fun r => b1_mset_imp (MeasurableSet.const _)
        (measurableSet_lt ((b1m_XW r0).add_const _) (b1m_XW r))
  · exact b1_mset_forall fun j => measurableSet_le
      ((measurable_const.mul (b1m_yTopW b1Eps)).mul b1m_betaW) (b1m_phU s j)
  · exact measurableSet_eq_fun (b1m_phi_flip s univ) (b1m_phUMin s)
  · refine b1_mset_and ?_ ?_
    · exact b1_measurableSet_at_tcRow
        (P := fun w r0 => sysMaxCauseStates (tpmOf (flipP s w)) univ s s = {r0})
        fun r0 => hflip (b1m_sysMaxCauseStates_eq univ s s {r0})
    · exact b1_mset_at (φ := fun w : Param N => teW w s) (b1_measurableSet_teW_eq s)
        (P := fun w t => sysMaxEffStates (tpmOf (flipP s w)) univ s s = {t})
        fun t => hflip (b1m_sysMaxEffStates_eq univ s s {t})
  · refine b1_mset_forall fun S => b1_mset_imp (MeasurableSet.const _) (b1_mset_forall fun te =>
      b1_mset_imp (hflip (b1m_mem_sysMaxEffStates S s s te)) (b1_mset_forall fun θ => ?_))
    have hE : Measurable fun w : Param N => sysPhiE (tpmOf (flipP s w)) S s θ s te :=
      (b1m_sysPhiE S s θ s te).comp hflip
    exact b1_mset_or (measurableSet_eq_fun hE measurable_const) (measurableSet_le b1m_betaW hE)

/-- **`bdry` is measurable.** -/
theorem measurableSet_bdry (s : State N) (δ : ℝ) : MeasurableSet (bdry N s δ) := by
  have hflip : Measurable (flipP s : Param N → Param N) := (mp_flipP s).measurable
  refine b1_mset_exists fun S => b1_mset_and (MeasurableSet.const _) (b1_mset_or ?_ ?_)
  · exact measurableSet_le (continuous_abs.measurable.comp
      ((b1m_phi_flip s S).sub (b1m_phi_flip s univ))) (measurable_const.mul b1m_betaW)
  · refine b1_mset_exists fun tc => b1_mset_and (hflip (b1m_mem_sysMaxCauseStates S s s tc))
      (b1_mset_exists fun te => b1_mset_and (hflip (b1m_mem_sysMaxEffStates S s s te))
        (b1_mset_exists fun θ => b1_mset_and (hflip (b1m_mem_sysMipSetAt S s s tc te θ))
          (b1_mset_exists fun θ' => b1_mset_and (MeasurableSet.const _) ?_)))
    exact measurableSet_le ((b1m_normalizedSysPhiAt S s θ' s tc te).comp hflip)
      (((b1m_normalizedSysPhiAt S s θ s tc te).comp hflip).add (measurable_const.mul b1m_betaW))

end MeasEvents

/-! ## 8. Further elementary facts -/

lemma b1_sum_pow_le (N ρ : ℕ) : ∑ k ∈ range (ρ + 1), N ^ k ≤ (N + 1) ^ ρ := by
  induction ρ with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h1 : N ^ (n + 1) ≤ N * (N + 1) ^ n := by
      rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ N) n)
    calc ∑ k ∈ range (n + 1), N ^ k + N ^ (n + 1) ≤ (N + 1) ^ n + N * (N + 1) ^ n :=
          Nat.add_le_add ih h1
      _ = (N + 1) ^ (n + 1) := by ring

/-- A Hamming ball of radius `ρ` has at most `(N + 1)^ρ` rows. -/
lemma card_ballR_le (r : State N) (ρ : ℕ) : (ballR r ρ).card ≤ (N + 1) ^ ρ := by
  classical
  set D : State N → Finset (Fin N) := fun r' => univ.filter fun j => r j ≠ r' j with hD
  set T : Finset (Finset (Fin N)) := (range (ρ + 1)).biUnion fun k => powersetCard k univ with hT
  have hmaps : Set.MapsTo D (ballR r ρ) T := by
    intro r' hr'
    have hc : (D r').card ≤ ρ := mem_ballR.1 (mem_coe.1 hr')
    refine mem_coe.2 (mem_biUnion.2 ⟨(D r').card, mem_range.2 (Nat.lt_succ_of_le hc), ?_⟩)
    exact mem_powersetCard.2 ⟨subset_univ _, rfl⟩
  have hinj : Set.InjOn D (ballR r ρ) := by
    intro a _ b _ hab
    funext j
    have h := congrArg (fun E => j ∈ E) hab
    simp only [hD, mem_filter, mem_univ, true_and, eq_iff_iff] at h
    cases ha : a j <;> cases hb : b j <;> cases hr : r j <;> simp_all
  calc (ballR r ρ).card ≤ T.card := card_le_card_of_injOn D hmaps hinj
    _ ≤ ∑ k ∈ range (ρ + 1), (powersetCard k (univ : Finset (Fin N))).card := card_biUnion_le
    _ = ∑ k ∈ range (ρ + 1), N.choose k := by simp [card_powersetCard]
    _ ≤ ∑ k ∈ range (ρ + 1), N ^ k := sum_le_sum fun k _ => Nat.choose_le_pow N k
    _ ≤ (N + 1) ^ ρ := b1_sum_pow_le N ρ

/-- The sensitive rows are at most `2 (N + 1)^4`. -/
lemma card_sensRows_le (s r0 : State N) : (sensRows s r0).card ≤ 2 * (N + 1) ^ 4 := by
  have h1 := card_ballR_le r0 4
  have h2 := card_ballR_le s 2
  have h3 : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (Nat.succ_pos N) (by norm_num)
  calc (sensRows s r0).card ≤ (ballR r0 4).card + (ballR s 2).card := card_union_le _ _
    _ ≤ 2 * (N + 1) ^ 4 := by omega

lemma b1_ceil_eps_le (N : ℕ) : ⌈b1Eps * N⌉₊ ≤ N := by
  rw [Nat.ceil_le]; unfold b1Eps
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

lemma b1_one_le_ceil_eps (hN : 1 ≤ N) : 1 ≤ ⌈b1Eps * N⌉₊ := by
  rw [Nat.one_le_ceil_iff]; unfold b1Eps
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  positivity

lemma yMinW_le (w : Param N) (i : Fin N) : yMinW w ≤ clamp01 (w (tcRow w) i) :=
  b1_YMinR_le w _ i

lemma le_yMaxW (w : Param N) (i : Fin N) : clamp01 (w (tcRow w) i) ≤ yMaxW w :=
  b1_le_YMaxR w _ i

lemma yMinW_nonneg (w : Param N) : 0 ≤ yMinW w := b1_YMinR_nonneg w _

lemma yMaxW_le_one (w : Param N) : yMaxW w ≤ 1 := b1_YMaxR_le_one w _

lemma yTopW_le_yMaxW (w : Param N) (ε : ℝ) : yTopW w ε ≤ yMaxW w := b1_YTopR_le_YMaxR w _ ε

lemma yMinW_le_yTopW (w : Param N) (hN : 0 < N) : yMinW w ≤ yTopW w b1Eps :=
  b1_YMinR_le_YTopR w _ hN (b1_ceil_eps_le N)

/-- At least `⌈εN⌉₊` entries of `tc` are `≥ y_top`. -/
lemma card_ge_yTopW (w : Param N) {ε : ℝ} (hk : ⌈ε * N⌉₊ ≤ N) :
    ⌈ε * N⌉₊ ≤ (univ.filter fun i => yTopW w ε ≤ clamp01 (w (tcRow w) i)).card :=
  b1Kth_count (f := fun i => clamp01 (w (tcRow w) i)) hk

/-- Fewer than `⌈εN⌉₊` entries of `tc` are `> y_top`. -/
lemma card_gt_yTopW_lt (w : Param N) {ε : ℝ} (hk : 1 ≤ ⌈ε * N⌉₊) :
    (univ.filter fun i => yTopW w ε < clamp01 (w (tcRow w) i)).card < ⌈ε * N⌉₊ :=
  b1Kth_lt_count (f := fun i => clamp01 (w (tcRow w) i)) hk

namespace Forced

variable {s : State N} {w : Param N}

lemma tilt (h : Forced N s w) : XW w (tcRow w) ≤ x0 * N - 9 * Real.log N := h.fgood.tilt

lemma far (h : Forced N s w) : N ≤ 3 * ham (tcRow w) s := h.fgood.far

lemma yMin (h : Forced N s w) : b1YLo ≤ yMinW w := h.fgood.yMin

lemma top (h : Forced N s w) : b1TopRatio * yMaxW w ≤ yTopW w b1Eps := h.fgood.top

lemma posNear (h : Forced N s w) (K' : Finset (Fin N)) (hK' : K'.Nonempty) (hK4 : K'.card ≤ 4) :
    b1PosC * N ≤ ∑ i, b1CutG w (tcRow w) K' i :=
  h.fgood.posNear K' hK' hK4

end Forced

end Census
end IIT
