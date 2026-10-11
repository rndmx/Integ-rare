/-
Census of complexes: probability bounds for the subcube parts of the good event.

Under `cubeM N`, each of the following fails with probability at most an explicit function of `N`
tending to `0`:
* `g6`: every subcube sum `subSum w i M m` is at most its mean plus `16 N (√V + τ)` (Bernstein over
  the rows of the subcube, level `N`, union over `i`, `M`, `m`);
* `g13b`: every difference `DQ w S Y Y' t i` of normalised subcube sums is at most
  `16 L (√3 σ + τ)` with `L = LkN N |S|` (Bernstein over all rows, union over `S`, `i`, `Y`, `Y'`
  and the patterns `t` on `S`).

In both cases the summands are the row products without column `i`, truncated at `tauN N`; on the
event `g2` the truncation changes nothing.
-/
import IIT.Census.Bernstein
import IIT.Census.ColSplit
import IIT.Census.BigPhiProbBasic

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

noncomputable section

variable {N : ℕ}

/-! ### The truncated row product -/

/-- The row product without column `i`, truncated at `tauN N`. -/
def rowT (i : Fin N) (v : Fin N → ℝ) : ℝ := min (∏ j ∈ univ.erase i, clamp01 (v j)) (tauN N)

/-- The mean of the truncated row product. -/
def muT (N : ℕ) (i : Fin N) : ℝ := ∫ v, rowT i v ∂rowM N

lemma measurable_rowT (i : Fin N) : Measurable (rowT i) :=
  (measurable_rowQ i).min measurable_const

lemma rowT_nonneg (i : Fin N) (v : Fin N → ℝ) : 0 ≤ rowT i v :=
  le_min (prod_nonneg fun _ _ => clamp01_nonneg _) (tauN_pos N).le

lemma rowT_le_tau (i : Fin N) (v : Fin N → ℝ) : rowT i v ≤ tauN N := min_le_right _ _

lemma rowT_le_Q (i : Fin N) (v : Fin N → ℝ) : rowT i v ≤ ∏ j ∈ univ.erase i, clamp01 (v j) :=
  min_le_left _ _

lemma integrable_rowM {g : (Fin N → ℝ) → ℝ} (hg : Measurable g) (C : ℝ) (h : ∀ v, |g v| ≤ C) :
    Integrable g (rowM N) :=
  Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ fun v => by
    rw [Real.norm_eq_abs]; exact h v)

lemma integrable_rowT (i : Fin N) : Integrable (rowT i) (rowM N) :=
  integrable_rowM (measurable_rowT i) (tauN N) fun v => by
    rw [abs_of_nonneg (rowT_nonneg i v)]; exact rowT_le_tau i v

lemma integrable_rowQ (i : Fin N) (p : ℕ) :
    Integrable (fun v : Fin N → ℝ => (∏ j ∈ univ.erase i, clamp01 (v j)) ^ p) (rowM N) :=
  integrable_rowM ((measurable_rowQ i).pow_const p) 1 fun v => abs_rowQ_pow_le i p v

lemma muT_nonneg (i : Fin N) : 0 ≤ muT N i := integral_nonneg fun v => rowT_nonneg i v

lemma muT_le_tau (i : Fin N) : muT N i ≤ tauN N := by
  have h := integral_mono (integrable_rowT i) (integrable_const (tauN N)) fun v => rowT_le_tau i v
  unfold muT
  simpa using h

lemma muT_le_half (i : Fin N) : muT N i ≤ (1 / 2 : ℝ) ^ (N - 1) := by
  have h := integral_mono (integrable_rowT i) (integrable_rowQ i 1) fun v => by
    simp only [pow_one]; exact rowT_le_Q i v
  rw [integral_rowQ_pow] at h
  norm_num at h
  unfold muT
  norm_num
  exact h

/-- The second central moment of the truncated row product is at most `3^{-(N-1)}`. -/
lemma integral_sq_rowT_sub (i : Fin N) :
    ∫ v, (rowT i v - muT N i) ^ 2 ∂rowM N ≤ (1 / 3 : ℝ) ^ (N - 1) := by
  have h1 := variance_eq_integral (μ := rowM N) (measurable_rowT i).aemeasurable
  have h2 := variance_le_expectation_sq (μ := rowM N) (measurable_rowT i).aestronglyMeasurable
  rw [h1] at h2
  refine h2.trans ?_
  have h3 : ∫ v, (rowT i ^ 2) v ∂rowM N ≤
      ∫ v, (∏ j ∈ univ.erase i, clamp01 (v j)) ^ 2 ∂rowM N :=
    integral_mono (integrable_rowM ((measurable_rowT i).pow_const 2) (tauN N ^ 2) fun v => by
        simp only [Pi.pow_apply]
        rw [abs_of_nonneg (pow_nonneg (rowT_nonneg i v) 2)]
        exact pow_le_pow_left₀ (rowT_nonneg i v) (rowT_le_tau i v) 2)
      (integrable_rowQ i 2) (fun v => by
        simp only [Pi.pow_apply]
        exact pow_le_pow_left₀ (rowT_nonneg i v) (rowT_le_Q i v) 2)
  rw [integral_rowQ_pow] at h3
  norm_num at h3 ⊢
  exact h3

lemma abs_rowT_sub_le (i : Fin N) (v : Fin N → ℝ) : |rowT i v - muT N i| ≤ tauN N :=
  abs_sub_le_iff.2 ⟨by linarith [rowT_le_tau i v, muT_nonneg i],
    by linarith [rowT_nonneg i v, muT_le_tau i]⟩

/-- **Bernstein over the rows** for a weighted sum of centred truncated row products, with
weights of absolute value at most one: at level `L ≥ 1` the deviation `16 L max (√V) τ` has
probability at most `2 e^{-6L}`. -/
theorem cubeM_trunc_dev (i : Fin N) (s : Finset (State N)) (ε : State N → ℝ)
    (hε : ∀ r, |ε r| ≤ 1) {L V : ℝ} (hL : 1 ≤ L)
    (hV : (s.card : ℝ) * (1 / 3 : ℝ) ^ (N - 1) ≤ V) :
    cubeM N {w | 16 * L * max (Real.sqrt V) (tauN N) ≤
      |∑ r ∈ s, ε r * (rowT i (w r) - muT N i)|} ≤ ENNReal.ofReal (2 * Real.exp (-6 * L)) := by
  have hmf : ∀ r, Measurable fun v : Fin N → ℝ => ε r * (rowT i v - muT N i) :=
    fun r => measurable_const.mul ((measurable_rowT i).sub_const _)
  have hind := iIndepFun_rows (fun r v => ε r * (rowT i v - muT N i)) hmf
  have hmeas : ∀ r, AEMeasurable (fun w : Param N => ε r * (rowT i (w r) - muT N i)) (cubeM N) :=
    fun r => ((hmf r).comp (measurable_pi_apply r)).aemeasurable
  have hb : ∀ r ∈ s, ∀ᵐ w ∂cubeM N, |ε r * (rowT i (w r) - muT N i)| ≤ tauN N := by
    intro r _
    refine ae_of_all _ fun w => ?_
    rw [abs_mul]
    calc |ε r| * |rowT i (w r) - muT N i| ≤ 1 * tauN N :=
          mul_le_mul (hε r) (abs_rowT_sub_le i _) (abs_nonneg _) zero_le_one
      _ = tauN N := one_mul _
  have h0 : ∀ r ∈ s, ∫ w, ε r * (rowT i (w r) - muT N i) ∂cubeM N = 0 := by
    intro r _
    rw [integral_row_eval (g := fun v => ε r * (rowT i v - muT N i)) (hmf r).aestronglyMeasurable r,
      integral_const_mul, integral_sub (integrable_rowT i) (integrable_const _), integral_const]
    simp [muT]
  have hV' : ∑ r ∈ s, ∫ w, (ε r * (rowT i (w r) - muT N i)) ^ 2 ∂cubeM N ≤ V := by
    calc ∑ r ∈ s, ∫ w, (ε r * (rowT i (w r) - muT N i)) ^ 2 ∂cubeM N
        ≤ ∑ _r ∈ s, (1 / 3 : ℝ) ^ (N - 1) := by
          refine sum_le_sum fun r _ => ?_
          rw [integral_row_eval (g := fun v => (ε r * (rowT i v - muT N i)) ^ 2)
            ((hmf r).pow_const 2).aestronglyMeasurable r]
          simp_rw [mul_pow]
          rw [integral_const_mul]
          have hε2 : ε r ^ 2 ≤ 1 := by
            rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (hε r)
          calc ε r ^ 2 * ∫ v, (rowT i v - muT N i) ^ 2 ∂rowM N
              ≤ 1 * ∫ v, (rowT i v - muT N i) ^ 2 ∂rowM N :=
                mul_le_mul_of_nonneg_right hε2 (integral_nonneg fun v => sq_nonneg _)
            _ ≤ _ := by rw [one_mul]; exact integral_sq_rowT_sub i
      _ = s.card * (1 / 3 : ℝ) ^ (N - 1) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ V := hV
  have hpos : 0 < max (Real.sqrt V) (tauN N) := lt_max_of_lt_right (tauN_pos N)
  have h := bernstein_L (X := fun r (w : Param N) => ε r * (rowT i (w r) - muT N i))
    s hind hmeas hL hpos hb h0 hV'
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal h

/-! ### `g6`: subcube sums -/

lemma rowT_eq_Qw {w : Param N} {i : Fin N} (h : ∀ r, Qw w i r ≤ tauN N) (r : State N) :
    rowT i (w r) = Qw w i r :=
  min_eq_left (h r)

lemma cubeM_subSum_bad (i : Fin N) (M : Finset (Fin N)) (m : State N) :
    cubeM N {w | (∀ i r, Qw w i r ≤ tauN N) ∧ ¬ subSum w i M m ≤
      (2 : ℝ) ^ (N - M.card) * (1 / 2 : ℝ) ^ (N - 1)
        + 16 * N * (Real.sqrt ((2 : ℝ) ^ (N - M.card) * (1 / 3 : ℝ) ^ (N - 1)) + tauN N)} ≤
      ENNReal.ofReal (2 * Real.exp (-6 * N)) := by
  set V := (2 : ℝ) ^ (N - M.card) * (1 / 3 : ℝ) ^ (N - 1) with hVdef
  have hN : (1 : ℝ) ≤ N := by
    obtain ⟨n, rfl⟩ := exists_succ_of_fin i
    push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hcard : ((agree M m).card : ℝ) = (2 : ℝ) ^ (N - M.card) := by
    rw [card_agree]; push_cast; rfl
  refine (measure_mono ?_).trans (cubeM_trunc_dev i (agree M m) (fun _ => 1)
    (fun _ => by norm_num) hN (V := V) (by rw [hcard]))
  rintro w ⟨hg2, hbad⟩
  simp only [Set.mem_ofPred_eq, one_mul]
  have hsum : ∑ r ∈ agree M m, (rowT i (w r) - muT N i) =
      subSum w i M m - (2 : ℝ) ^ (N - M.card) * muT N i := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcard, subSum]
    congr 1
    exact sum_congr rfl fun r _ => rowT_eq_Qw (hg2 i) r
  rw [hsum]
  have hmu := muT_le_half i
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (N - M.card) := by positivity
  have hmax : max (Real.sqrt V) (tauN N) ≤ Real.sqrt V + tauN N :=
    max_le (le_add_of_nonneg_right (tauN_pos N).le) (le_add_of_nonneg_left (Real.sqrt_nonneg _))
  have h16 : 16 * (N : ℝ) * max (Real.sqrt V) (tauN N) ≤ 16 * N * (Real.sqrt V + tauN N) :=
    mul_le_mul_of_nonneg_left hmax (by positivity)
  refine le_trans ?_ (le_abs_self _)
  push Not at hbad
  nlinarith [mul_le_mul_of_nonneg_left hmu h2]

/-- The failure probability of `g6`. -/
def fg6 (N : ℕ) : ℝ := fg2 N + 2 * N * (4 * Real.exp (-6)) ^ N

/-- **`g6` fails with probability at most `fg6 N`.** -/
theorem cubeM_not_g6 :
    cubeM N {w | ¬ ∀ i (M : Finset (Fin N)) (m : State N), subSum w i M m ≤
      (2 : ℝ) ^ (N - M.card) * (1 / 2 : ℝ) ^ (N - 1)
        + 16 * N * (Real.sqrt ((2 : ℝ) ^ (N - M.card) * (1 / 3 : ℝ) ^ (N - 1)) + tauN N)} ≤
      ENNReal.ofReal (fg6 N) := by
  have hsub : {w : Param N | ¬ ∀ i (M : Finset (Fin N)) (m : State N), subSum w i M m ≤
      (2 : ℝ) ^ (N - M.card) * (1 / 2 : ℝ) ^ (N - 1)
        + 16 * N * (Real.sqrt ((2 : ℝ) ^ (N - M.card) * (1 / 3 : ℝ) ^ (N - 1)) + tauN N)} ⊆
      {w | ¬ ∀ i r, Qw w i r ≤ tauN N} ∪ ⋃ i, ⋃ M : Finset (Fin N), ⋃ m : State N,
        {w | (∀ i r, Qw w i r ≤ tauN N) ∧ ¬ subSum w i M m ≤
          (2 : ℝ) ^ (N - M.card) * (1 / 2 : ℝ) ^ (N - 1)
            + 16 * N * (Real.sqrt ((2 : ℝ) ^ (N - M.card) * (1 / 3 : ℝ) ^ (N - 1)) + tauN N)} := by
    intro w hw
    by_cases hg2 : ∀ i r, Qw w i r ≤ tauN N
    · right
      simp only [Set.mem_ofPred_eq, not_forall] at hw
      obtain ⟨i, M, m, h⟩ := hw
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ⟨i, M, m, hg2, h⟩
    · exact Or.inl hg2
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hU := cubeM_iUnion_le _ fun i => cubeM_iUnion_le _ fun M =>
    cubeM_iUnion_le _ fun m => cubeM_subSum_bad (N := N) i M m
  refine (add_le_add cubeM_not_g2 hU).trans ?_
  rw [← ENNReal.ofReal_add (by unfold fg2; positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  apply le_of_eq
  simp only [Fintype.card_fin, Fintype.card_finset, Fintype.card_fun, Fintype.card_bool,
    Nat.cast_pow, Nat.cast_ofNat]
  unfold fg6
  rw [mul_pow, show -6 * (N : ℝ) = N * (-6) by ring, Real.exp_nat_mul,
    show (4 : ℝ) ^ N = 2 ^ N * 2 ^ N by rw [← mul_pow]; norm_num]
  ring

lemma four_exp_neg_six_lt_one : 4 * Real.exp (-6) < 1 := by
  have h := Real.add_one_le_exp 6
  rw [Real.exp_neg]
  have hp := Real.exp_pos 6
  rw [← div_eq_mul_inv, div_lt_one hp]
  linarith

theorem tendsto_fg6 : Tendsto fg6 atTop (𝓝 0) := by
  have h := (tendsto_self_mul_const_pow_of_lt_one (r := 4 * Real.exp (-6)) (by positivity)
    four_exp_neg_six_lt_one).const_mul 2
  rw [mul_zero] at h
  have h2 := tendsto_fg2.add h
  rw [add_zero] at h2
  refine h2.congr fun N => ?_
  unfold fg6; ring

/-! ### `g13b`: differences of normalised subcube sums -/

/-- The row weights of `DQ`: indicator of the `Y`-subcube over `2^{|S|-|Y|}` minus the same for
`Y'`. -/
def epsW (S Y Y' : Finset (Fin N)) (t : State N) (r : State N) : ℝ :=
  (if r ∈ agree Y t then 1 else 0) / (2 : ℝ) ^ (S.card - Y.card)
    - (if r ∈ agree Y' t then 1 else 0) / (2 : ℝ) ^ (S.card - Y'.card)

lemma ind_div_mem_Icc (A : Finset (State N)) (r : State N) (n : ℕ) :
    0 ≤ (if r ∈ A then (1 : ℝ) else 0) / (2 : ℝ) ^ n ∧
      (if r ∈ A then (1 : ℝ) else 0) / (2 : ℝ) ^ n ≤ 1 := by
  have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  constructor
  · split_ifs <;> positivity
  · rw [div_le_one (by positivity)]
    split_ifs <;> linarith

lemma abs_epsW_le (S Y Y' : Finset (Fin N)) (t r : State N) : |epsW S Y Y' t r| ≤ 1 := by
  have h1 := ind_div_mem_Icc (agree Y t) r (S.card - Y.card)
  have h2 := ind_div_mem_Icc (agree Y' t) r (S.card - Y'.card)
  unfold epsW
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

lemma DQ_eq_sum (w : Param N) (S Y Y' : Finset (Fin N)) (t : State N) (i : Fin N) :
    DQ w S Y Y' t i = ∑ r, epsW S Y Y' t r * Qw w i r := by
  unfold DQ subSum epsW
  simp_rw [sub_mul, div_mul_eq_mul_div, ite_mul, one_mul, zero_mul, sum_sub_distrib, ← sum_div,
    Fintype.sum_ite_mem]

lemma sum_ind_div {S Y : Finset (Fin N)} (hY : Y ⊆ S) (t : State N) :
    ∑ r, (if r ∈ agree Y t then (1 : ℝ) else 0) / (2 : ℝ) ^ (S.card - Y.card) =
      (2 : ℝ) ^ (N - S.card) := by
  have h1 := card_le_card hY
  have h2 := card_le_univ S
  rw [Fintype.card_fin] at h2
  rw [← sum_div, Fintype.sum_ite_mem (agree Y t) (fun _ => (1 : ℝ)), sum_const, card_agree,
    nsmul_one]
  push_cast
  rw [show N - Y.card = (N - S.card) + (S.card - Y.card) by omega, pow_add,
    mul_div_cancel_right₀ _ (by positivity)]

lemma sum_epsW {S Y Y' : Finset (Fin N)} (hY : Y ⊆ S) (hY' : Y' ⊆ S) (t : State N) :
    ∑ r, epsW S Y Y' t r = 0 := by
  unfold epsW
  rw [sum_sub_distrib, sum_ind_div hY, sum_ind_div hY', sub_self]

/-- The state that is `true` exactly on `T`. -/
def indS (T : Finset (Fin N)) : State N := fun j => decide (j ∈ T)

lemma agree_indS {S Y : Finset (Fin N)} (hY : Y ⊆ S) (t : State N) :
    agree Y t = agree Y (indS (S.filter fun j => t j = true)) := by
  ext r
  simp only [mem_agree, indS, mem_filter]
  refine forall₂_congr fun j hj => ?_
  simp [hY hj]

lemma DQ_indS (w : Param N) {S Y Y' : Finset (Fin N)} (hY : Y ⊆ S) (hY' : Y' ⊆ S) (t : State N)
    (i : Fin N) :
    DQ w S Y Y' t i = DQ w S Y Y' (indS (S.filter fun j => t j = true)) i := by
  unfold DQ subSum
  rw [agree_indS hY t, agree_indS hY' t]

lemma V13_eq (hN : 1 ≤ N) : (2 : ℝ) ^ N * (1 / 3 : ℝ) ^ (N - 1) = 3 * (2 / 3 : ℝ) ^ N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel, div_pow, div_pow, one_pow, pow_succ (3 : ℝ) n]
  field_simp
  try ring

lemma one_le_LkN {k : ℕ} (hk : 1 ≤ k) : 1 ≤ LkN N k := by
  unfold LkN
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 := Real.log_natCast_nonneg N
  nlinarith

/-- The bad event of `g13b` for one pattern, on the event `g2`. -/
def badDQ (S : Finset (Fin N)) (i : Fin N) (Y Y' : Finset (Fin N)) (t : State N) : Set (Param N) :=
  {w | (∀ i r, Qw w i r ≤ tauN N) ∧
    ¬ |DQ w S Y Y' t i| ≤ 16 * LkN N S.card * (Real.sqrt 3 * sigN N + tauN N)}

lemma cubeM_badDQ {S : Finset (Fin N)} {i : Fin N} {Y Y' : Finset (Fin N)} (t : State N)
    (hi : i ∈ S) (hY : Y ⊆ S) (hY' : Y' ⊆ S) :
    cubeM N (badDQ S i Y Y' t) ≤ ENNReal.ofReal (2 * Real.exp (-6 * LkN N S.card)) := by
  have hN : 1 ≤ N := by have := i.pos; omega
  have hL : 1 ≤ LkN N S.card := one_le_LkN (card_pos.2 ⟨i, hi⟩)
  set V := (2 : ℝ) ^ N * (1 / 3 : ℝ) ^ (N - 1) with hVdef
  refine (measure_mono ?_).trans (cubeM_trunc_dev i univ (epsW S Y Y' t)
    (abs_epsW_le S Y Y' t) hL (V := V) (by rw [card_state]; push_cast; exact le_refl _))
  rintro w ⟨hg2, hbad⟩
  simp only [Set.mem_ofPred_eq]
  have hsum : ∑ r, epsW S Y Y' t r * (rowT i (w r) - muT N i) = DQ w S Y Y' t i := by
    simp_rw [mul_sub, sum_sub_distrib, ← sum_mul, sum_epsW hY hY', zero_mul, sub_zero,
      DQ_eq_sum, rowT_eq_Qw (hg2 i)]
  rw [hsum]
  have hsV : Real.sqrt V = Real.sqrt 3 * sigN N := by
    rw [hVdef, V13_eq hN, Real.sqrt_mul (by norm_num), sigN]
  have hmax : max (Real.sqrt V) (tauN N) ≤ Real.sqrt 3 * sigN N + tauN N := by
    rw [hsV]
    exact max_le (le_add_of_nonneg_right (tauN_pos N).le)
      (le_add_of_nonneg_left (by have := sigN_pos N; positivity))
  push Not at hbad
  refine le_trans ?_ hbad.le
  exact mul_le_mul_of_nonneg_left hmax (by linarith)

/-- A union bound over a finset, with real bounds. -/
lemma cubeM_biUnion_le {ι : Type*} (s : Finset ι) (X : ι → Set (Param N)) {b : ℝ}
    (h : ∀ a ∈ s, cubeM N (X a) ≤ ENNReal.ofReal b) :
    cubeM N (⋃ a ∈ s, X a) ≤ ENNReal.ofReal (s.card * b) := by
  calc cubeM N (⋃ a ∈ s, X a) ≤ ∑ a ∈ s, cubeM N (X a) := measure_biUnion_finset_le s X
    _ ≤ ∑ _a ∈ s, ENNReal.ofReal b := sum_le_sum h
    _ = _ := by
        rw [sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-- All bad patterns of one candidate `S`. -/
def badDQS (S : Finset (Fin N)) : Set (Param N) :=
  ⋃ i ∈ S, ⋃ Y ∈ S.powerset, ⋃ Y' ∈ S.powerset, ⋃ T ∈ S.powerset, badDQ S i Y Y' (indS T)

/-- The per-candidate union bound: `|S| 2^{3|S|}` patterns. -/
def bS (N k : ℕ) : ℝ := k * (2 ^ k * (2 ^ k * (2 ^ k * (2 * Real.exp (-6 * LkN N k)))))

lemma cubeM_badDQS (S : Finset (Fin N)) : cubeM N (badDQS S) ≤ ENNReal.ofReal (bS N S.card) := by
  have h : cubeM N (badDQS S) ≤ ENNReal.ofReal (S.card * (S.powerset.card *
      (S.powerset.card * (S.powerset.card * (2 * Real.exp (-6 * LkN N S.card)))))) := by
    unfold badDQS
    refine cubeM_biUnion_le _ _ fun i hi => ?_
    refine cubeM_biUnion_le _ _ fun Y hY => ?_
    refine cubeM_biUnion_le _ _ fun Y2 hY2 => ?_
    refine cubeM_biUnion_le _ _ fun T _ => ?_
    exact cubeM_badDQ (indS T) hi (mem_powerset.1 hY) (mem_powerset.1 hY2)
  rw [card_powerset] at h
  refine h.trans_eq ?_
  unfold bS
  push_cast
  rfl

lemma bS_le (hN : 1 ≤ N) {k : ℕ} (hk : k ≤ N) :
    bS N k ≤ 2 * (1 / (N : ℝ)) ^ 11 * (1 / (N : ℝ)) ^ k := by
  have hx : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNx : (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log hNpos).symm
  have h1N : 1 / (N : ℝ) = Real.exp (-Real.log N) := by
    rw [Real.exp_neg, ← hNx, one_div]
  have h8 : (2 : ℝ) ^ k * (2 ^ k * 2 ^ k) ≤ Real.exp (k * 18) := by
    calc (2 : ℝ) ^ k * (2 ^ k * 2 ^ k) = (8 : ℝ) ^ k := by
          rw [← mul_pow, ← mul_pow]; norm_num
      _ ≤ Real.exp 18 ^ k :=
          pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp 18]) k
      _ = Real.exp (k * 18) := (Real.exp_nat_mul 18 k).symm
  have hk' : (k : ℝ) ≤ Real.exp (Real.log N) := by rw [← hNx]; exact_mod_cast hk
  have hkx : 0 ≤ (k : ℝ) * Real.log N := mul_nonneg (Nat.cast_nonneg k) hx
  rw [h1N, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  unfold bS
  calc (k : ℝ) * (2 ^ k * (2 ^ k * (2 ^ k * (2 * Real.exp (-6 * LkN N k)))))
      = (k : ℝ) * (2 ^ k * (2 ^ k * 2 ^ k)) * (2 * Real.exp (-6 * LkN N k)) := by ring
    _ ≤ Real.exp (Real.log N) * Real.exp (k * 18) * (2 * Real.exp (-6 * LkN N k)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hk' h8 (by positivity) (Real.exp_pos _).le)
          (by positivity)
    _ = 2 * Real.exp (Real.log N + k * 18 + -6 * LkN N k) := by
        rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ 2 * Real.exp (((11 : ℕ) : ℝ) * -Real.log N + (k : ℝ) * -Real.log N) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
        unfold LkN
        push_cast
        nlinarith
    _ = 2 * Real.exp (((11 : ℕ) : ℝ) * -Real.log N) * Real.exp ((k : ℝ) * -Real.log N) := by
        rw [Real.exp_add]; ring

/-- The failure probability of `g13b`. -/
def fg13b (N : ℕ) : ℝ := fg2 N + 2 * Real.exp 1 * (1 / (N : ℝ)) ^ 11

lemma sum_bS_le (hN : 1 ≤ N) :
    ∑ S : Finset (Fin N), bS N S.card ≤ 2 * Real.exp 1 * (1 / (N : ℝ)) ^ 11 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hbin := Fin.sum_pow_mul_eq_add_pow (n := N) (1 / (N : ℝ)) 1
  simp only [one_pow, mul_one] at hbin
  have he : (1 / (N : ℝ) + 1) ^ N ≤ Real.exp 1 := by
    calc (1 / (N : ℝ) + 1) ^ N ≤ Real.exp (1 / N) ^ N :=
          pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) N
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul, mul_one_div_cancel hNpos.ne']
  calc ∑ S : Finset (Fin N), bS N S.card
      ≤ ∑ S : Finset (Fin N), 2 * (1 / (N : ℝ)) ^ 11 * (1 / (N : ℝ)) ^ S.card := by
        refine sum_le_sum fun S _ => bS_le hN ?_
        simpa using card_le_univ S
    _ = 2 * (1 / (N : ℝ)) ^ 11 * (1 / (N : ℝ) + 1) ^ N := by rw [← mul_sum, hbin]
    _ ≤ 2 * (1 / (N : ℝ)) ^ 11 * Real.exp 1 :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

lemma bS_nonneg (N k : ℕ) : 0 ≤ bS N k := by unfold bS; positivity

/-- **`g13b` fails with probability at most `fg13b N`.** -/
theorem cubeM_not_g13b :
    cubeM N {w | ¬ ∀ (S : Finset (Fin N)) i (Y Y' : Finset (Fin N)) t, i ∈ S → Y ⊆ S → Y' ⊆ S →
      |DQ w S Y Y' t i| ≤ 16 * LkN N S.card * (Real.sqrt 3 * sigN N + tauN N)} ≤
      ENNReal.ofReal (fg13b N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hE : {w : Param 0 | ¬ ∀ (S : Finset (Fin 0)) i (Y Y' : Finset (Fin 0)) t, i ∈ S →
        Y ⊆ S → Y' ⊆ S →
        |DQ w S Y Y' t i| ≤ 16 * LkN 0 S.card * (Real.sqrt 3 * sigN 0 + tauN 0)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun w hw => hw fun S i => i.elim0
    rw [hE, measure_empty]
    exact bot_le
  have hsub : {w : Param N | ¬ ∀ (S : Finset (Fin N)) i (Y Y' : Finset (Fin N)) t, i ∈ S →
      Y ⊆ S → Y' ⊆ S →
      |DQ w S Y Y' t i| ≤ 16 * LkN N S.card * (Real.sqrt 3 * sigN N + tauN N)} ⊆
      {w | ¬ ∀ i r, Qw w i r ≤ tauN N} ∪ ⋃ S : Finset (Fin N), badDQS S := by
    intro w hw
    by_cases hg2 : ∀ i r, Qw w i r ≤ tauN N
    · right
      simp only [Set.mem_ofPred_eq, not_forall] at hw
      obtain ⟨S, i, Y, Y', t, hi, hY, hY', h⟩ := hw
      simp only [Set.mem_iUnion, badDQS, mem_powerset, exists_prop]
      refine ⟨S, i, hi, Y, hY, Y', hY', S.filter fun j => t j = true, filter_subset _ _, hg2, ?_⟩
      rwa [← DQ_indS w hY hY' t i]
    · exact Or.inl hg2
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hU : cubeM N (⋃ S : Finset (Fin N), badDQS S) ≤
      ENNReal.ofReal (∑ S : Finset (Fin N), bS N S.card) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun S _ => bS_nonneg N S.card]
    exact (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun S _ => cubeM_badDQS S)
  refine (add_le_add cubeM_not_g2 hU).trans ?_
  rw [← ENNReal.ofReal_add (by unfold fg2; positivity)
    (sum_nonneg fun S _ => bS_nonneg N S.card)]
  apply ENNReal.ofReal_le_ofReal
  unfold fg13b
  linarith [sum_bS_le hN]

theorem tendsto_fg13b : Tendsto fg13b atTop (𝓝 0) := by
  have h := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 11).const_mul (2 * Real.exp 1)
  rw [zero_pow (by norm_num), mul_zero] at h
  have h2 := tendsto_fg2.add h
  rw [add_zero] at h2
  exact h2

end

end Census
end IIT
