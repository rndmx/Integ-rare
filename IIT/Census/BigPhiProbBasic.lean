/-
Census of complexes: explicit probability bounds for the basic parts of the good event.

Under `cubeM N`, each of the following fails with probability at most an explicit function of `N`
tending to `0`:
* `g2`: every `Qw w i r ≤ tauN N` (Markov on `Qw^3`, union over `i` and `r`);
* `g3`: `1/2 ≤ Zs ≤ 2` and every `ZQ w i ≤ 3` (Chebyshev over the independent rows);
* `g4`: every `SQ2 w i ≤ 6 (2/3)^N` (Chebyshev over the rows);
* `g12`: every `Xk w k i ≤ 4 N^3 vk N k 2^{-N}` (Markov, union over `k ≤ N` and `i`);
* `gU`: `Mrow w s ≤ (4/5)^N` (Markov on a polynomial majorant of the row maximum).
-/
import IIT.Census.ColSplit

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

noncomputable section

variable {N : ℕ}

/-! ### Markov and Chebyshev under `cubeM` -/

/-- Markov's inequality under `cubeM N`, with a real bound. -/
lemma markov_cubeM {f : Param N → ℝ} (h0 : ∀ w, 0 ≤ f w) (hint : Integrable f (cubeM N))
    {ε : ℝ} (hε : 0 < ε) :
    cubeM N {w | ε ≤ f w} ≤ ENNReal.ofReal ((∫ w, f w ∂cubeM N) / ε) := by
  have h := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ h0) hint ε
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  rw [le_div_iff₀ hε, mul_comm]
  exact h

lemma memLp_row {g : (Fin N → ℝ) → ℝ} (hg : Measurable g) (hb : ∀ v, |g v| ≤ 1) (r : State N) :
    MemLp (fun w : Param N => g (w r)) 2 (cubeM N) :=
  MemLp.of_bound (hg.comp (measurable_pi_apply r)).aestronglyMeasurable 1
    (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hb (w r))

lemma variance_sum_rows {g : (Fin N → ℝ) → ℝ} (hg : Measurable g) (hb : ∀ v, |g v| ≤ 1) :
    variance (fun w : Param N => ∑ r, g (w r)) (cubeM N) ≤ 2 ^ N * ∫ v, g v ^ 2 ∂rowM N := by
  have hind := iIndepFun_rows (fun _ => g) (fun _ => hg)
  have hsum : (fun w : Param N => ∑ r, g (w r)) = ∑ r, fun w : Param N => g (w r) := by
    funext w; simp [Finset.sum_apply]
  rw [hsum, IndepFun.variance_sum (fun r _ => memLp_row hg hb r)
    (fun r _ r' _ hrr => hind.indepFun hrr)]
  calc ∑ r, variance (fun w : Param N => g (w r)) (cubeM N)
      ≤ ∑ _r : State N, ∫ v, g v ^ 2 ∂rowM N := by
        refine sum_le_sum fun r _ => ?_
        refine (variance_le_expectation_sq (memLp_row hg hb r).aestronglyMeasurable).trans_eq ?_
        exact integral_row_eval (g := fun v => g v ^ 2) (hg.pow_const 2).aestronglyMeasurable r
    _ = _ := by rw [sum_const, card_state, nsmul_eq_mul]; push_cast; ring

lemma integral_sum_rows {g : (Fin N → ℝ) → ℝ} (hg : Measurable g) (hb : ∀ v, |g v| ≤ 1) :
    ∫ w, ∑ r, g (w r) ∂cubeM N = 2 ^ N * ∫ v, g v ∂rowM N := by
  rw [integral_finsetSum _ fun r _ => (memLp_row hg hb r).integrable one_le_two,
    sum_congr rfl fun r _ => integral_row_eval hg.aestronglyMeasurable r, sum_const, card_state,
    nsmul_eq_mul]
  push_cast; ring

/-- Chebyshev's inequality for a sum of iid functions of the rows. -/
lemma cheb_rows {g : (Fin N → ℝ) → ℝ} (hg : Measurable g) (hb : ∀ v, |g v| ≤ 1) {c : ℝ}
    (hc : 0 < c) :
    cubeM N {w | c ≤ |∑ r, g (w r) - 2 ^ N * ∫ v, g v ∂rowM N|} ≤
      ENNReal.ofReal (2 ^ N * (∫ v, g v ^ 2 ∂rowM N) / c ^ 2) := by
  have hmem : MemLp (fun w : Param N => ∑ r, g (w r)) 2 (cubeM N) :=
    memLp_finsetSum _ fun r _ => memLp_row hg hb r
  have h := meas_ge_le_variance_div_sq hmem hc
  have hE : (∫ w, (fun w : Param N => ∑ r, g (w r)) w ∂cubeM N) = 2 ^ N * ∫ v, g v ∂rowM N :=
    integral_sum_rows hg hb
  rw [hE] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  gcongr
  exact variance_sum_rows hg hb

/-- A union bound over a finite index type, with real bounds. -/
lemma cubeM_iUnion_le {ι : Type*} [Fintype ι] (X : ι → Set (Param N)) {b : ℝ}
    (h : ∀ i, cubeM N (X i) ≤ ENNReal.ofReal b) :
    cubeM N (⋃ i, X i) ≤ ENNReal.ofReal (Fintype.card ι * b) := by
  calc cubeM N (⋃ i, X i) ≤ ∑ i, cubeM N (X i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : ι, ENNReal.ofReal b := sum_le_sum fun i _ => h i
    _ = _ := by
        rw [sum_const, card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

lemma exists_succ_of_fin (i : Fin N) : ∃ n, N = n + 1 := ⟨N - 1, by have := i.pos; omega⟩

lemma abs_rowPw_le (v : Fin N → ℝ) : |∏ j, clamp01 (v j)| ≤ 1 := by
  rw [abs_of_nonneg (prod_nonneg fun _ _ => clamp01_nonneg _)]
  exact prod_le_one (fun _ _ => clamp01_nonneg _) fun _ _ => clamp01_le_one _

lemma abs_rowQ_pow_le (i : Fin N) (p : ℕ) (v : Fin N → ℝ) :
    |(∏ j ∈ univ.erase i, clamp01 (v j)) ^ p| ≤ 1 := by
  have h0 : 0 ≤ ∏ j ∈ univ.erase i, clamp01 (v j) := prod_nonneg fun _ _ => clamp01_nonneg _
  rw [abs_of_nonneg (pow_nonneg h0 p)]
  exact pow_le_one₀ h0 (prod_le_one (fun _ _ => clamp01_nonneg _) fun _ _ => clamp01_le_one _)

/-! ### `g2`: no large row product without one column -/

/-- The failure probability of `g2`. -/
def fg2 (N : ℕ) : ℝ := 4 * N * (Real.exp (2 / 3) / 2) ^ N

lemma cubeM_Qw_gt (i : Fin N) (r : State N) :
    cubeM N {w | ¬ Qw w i r ≤ tauN N} ≤ ENNReal.ofReal (4 * (Real.exp (2 / 3) / 4) ^ N) := by
  obtain ⟨n, rfl⟩ := exists_succ_of_fin i
  have hτ := tauN_pos (n + 1)
  have hsub : {w : Param (n + 1) | ¬ Qw w i r ≤ tauN (n + 1)} ⊆
      {w | tauN (n + 1) ^ 3 ≤ Qw w i r ^ 3} := by
    intro w hw
    simp only [Set.mem_ofPred_eq, not_le] at hw ⊢
    exact pow_le_pow_left₀ hτ.le hw.le 3
  refine (measure_mono hsub).trans ((markov_cubeM (fun w => pow_nonneg (Qw_nonneg w i r) 3)
    (integrable_Qw_pow i r 3) (pow_pos hτ 3)).trans (ENNReal.ofReal_le_ofReal ?_))
  rw [integral_Qw_pow, tauN, ← Real.exp_nat_mul, div_eq_mul_inv, ← Real.exp_neg]
  have e1 : (1 / (((3 : ℕ) : ℝ) + 1)) ^ (n + 1 - 1) = (1 / 4 : ℝ) ^ n := by norm_num
  have e2 : -(((3 : ℕ) : ℝ) * (-(2 / 9) * (((n + 1 : ℕ) : ℝ) - 1))) = n * (2 / 3) := by
    push_cast; ring
  rw [e1, e2, Real.exp_nat_mul, pow_succ]
  have h1 : 1 ≤ Real.exp (2 / 3) := Real.one_le_exp (by norm_num)
  have key : (Real.exp (2 / 3) / 4) ^ n = (1 / 4 : ℝ) ^ n * Real.exp (2 / 3) ^ n := by ring
  have hp : 0 ≤ (1 / 4 : ℝ) ^ n * Real.exp (2 / 3) ^ n := by positivity
  rw [key]
  nlinarith [mul_le_mul_of_nonneg_left h1 hp]

/-- **`g2` fails with probability at most `fg2 N`.** -/
theorem cubeM_not_g2 : cubeM N {w | ¬ ∀ i r, Qw w i r ≤ tauN N} ≤ ENNReal.ofReal (fg2 N) := by
  have hset : {w : Param N | ¬ ∀ i r, Qw w i r ≤ tauN N} =
      ⋃ i, ⋃ r, {w | ¬ Qw w i r ≤ tauN N} := by
    ext w; simp
  rw [hset]
  refine (cubeM_iUnion_le _ fun i =>
    cubeM_iUnion_le _ fun r => cubeM_Qw_gt i r).trans (ENNReal.ofReal_le_ofReal ?_)
  simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  apply le_of_eq
  unfold fg2
  rw [div_pow, div_pow, show (4 : ℝ) ^ N = 2 ^ N * 2 ^ N by rw [← mul_pow]; norm_num]
  have : (0 : ℝ) < 2 ^ N := by positivity
  field_simp

lemma exp_two_thirds_lt_two : Real.exp (2 / 3) < 2 := by
  have h := Real.log_two_gt_d9
  calc Real.exp (2 / 3) < Real.exp (Real.log 2) := Real.exp_lt_exp.2 (by linarith)
    _ = 2 := Real.exp_log (by norm_num)

theorem tendsto_fg2 : Tendsto fg2 atTop (𝓝 0) := by
  have h := (tendsto_self_mul_const_pow_of_lt_one (r := Real.exp (2 / 3) / 2) (by positivity)
    (by linarith [exp_two_thirds_lt_two])).const_mul 4
  rw [mul_zero] at h
  refine h.congr fun N => ?_
  unfold fg2; ring

/-! ### `g3`: the normalisations -/

/-- The failure probability of `g3`. -/
def fg3 (N : ℕ) : ℝ := 4 * (2 / 3 : ℝ) ^ N + 3 * N * (2 / 3 : ℝ) ^ N

lemma cubeM_Zs_bad :
    cubeM N {w | ¬ (1 / 2 ≤ Zs w ∧ Zs w ≤ 2)} ≤ ENNReal.ofReal (4 * (2 / 3 : ℝ) ^ N) := by
  have hmean : (2 : ℝ) ^ N * ∫ v, ∏ j, clamp01 (v j) ∂rowM N = 1 := by
    have := integral_rowP_pow' (N := N) 1
    simp only [pow_one] at this
    rw [this, ← mul_pow]; norm_num
  have hsq : ∫ v, (∏ j, clamp01 (v j)) ^ 2 ∂rowM N = (1 / 3 : ℝ) ^ N := by
    rw [integral_rowP_pow']; norm_num
  have hsub : {w : Param N | ¬ (1 / 2 ≤ Zs w ∧ Zs w ≤ 2)} ⊆
      {w | 1 / 2 ≤ |∑ r, (fun v : Fin N → ℝ => ∏ j, clamp01 (v j)) (w r) -
        2 ^ N * ∫ v, ∏ j, clamp01 (v j) ∂rowM N|} := by
    intro w hw
    rw [Set.mem_ofPred_eq, hmean]
    change 1 / 2 ≤ |Zs w - 1|
    simp only [Set.mem_ofPred_eq, not_and_or, not_le] at hw
    rcases hw with h | h
    · rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  refine (measure_mono hsub).trans ((cheb_rows measurable_rowPw abs_rowPw_le
    (by norm_num)).trans (ENNReal.ofReal_le_ofReal ?_))
  rw [hsq, ← mul_pow]
  apply le_of_eq
  norm_num
  ring

lemma cubeM_ZQ_bad (i : Fin N) :
    cubeM N {w | ¬ ZQ w i ≤ 3} ≤ ENNReal.ofReal (3 * (2 / 3 : ℝ) ^ N) := by
  obtain ⟨n, rfl⟩ := exists_succ_of_fin i
  have hmean : (2 : ℝ) ^ (n + 1) * ∫ v, (∏ j ∈ univ.erase i, clamp01 (v j)) ∂rowM (n + 1) = 2 := by
    have := integral_rowQ_pow i 1
    simp only [pow_one] at this
    rw [this, Nat.add_sub_cancel, pow_succ, mul_comm, ← mul_assoc, ← mul_pow]; norm_num
  have hsq : ∫ v, (∏ j ∈ univ.erase i, clamp01 (v j)) ^ 2 ∂rowM (n + 1) = (1 / 3 : ℝ) ^ n := by
    rw [integral_rowQ_pow, Nat.add_sub_cancel]; norm_num
  have hsub : {w : Param (n + 1) | ¬ ZQ w i ≤ 3} ⊆
      {w | 1 ≤ |∑ r, (fun v : Fin (n + 1) → ℝ => ∏ j ∈ univ.erase i, clamp01 (v j)) (w r) -
        2 ^ (n + 1) * ∫ v, (∏ j ∈ univ.erase i, clamp01 (v j)) ∂rowM (n + 1)|} := by
    intro w hw
    rw [Set.mem_ofPred_eq, hmean]
    change 1 ≤ |ZQ w i - 2|
    simp only [Set.mem_ofPred_eq, not_le] at hw
    rw [abs_of_pos (by linarith)]; linarith
  have hg := abs_rowQ_pow_le i 1
  simp only [pow_one] at hg
  refine (measure_mono hsub).trans ((cheb_rows (measurable_rowQ i) hg
    (by norm_num)).trans (ENNReal.ofReal_le_ofReal ?_))
  have e : (2 / 3 : ℝ) ^ n = 2 ^ n * (1 / 3) ^ n := by rw [← mul_pow]; norm_num
  rw [hsq, pow_succ (2 / 3 : ℝ) n, e]
  apply le_of_eq
  ring

/-- **`g3` fails with probability at most `fg3 N`.** -/
theorem cubeM_not_g3 :
    cubeM N {w | ¬ (1 / 2 ≤ Zs w ∧ Zs w ≤ 2 ∧ ∀ i, ZQ w i ≤ 3)} ≤ ENNReal.ofReal (fg3 N) := by
  have hsub : {w : Param N | ¬ (1 / 2 ≤ Zs w ∧ Zs w ≤ 2 ∧ ∀ i, ZQ w i ≤ 3)} ⊆
      {w | ¬ (1 / 2 ≤ Zs w ∧ Zs w ≤ 2)} ∪ ⋃ i, {w | ¬ ZQ w i ≤ 3} := by
    intro w hw
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_exists,
      not_not] at h
    exact hw ⟨h.1.1, h.1.2, h.2⟩
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have h2 := cubeM_iUnion_le _ fun i => cubeM_ZQ_bad (N := N) i
  rw [Fintype.card_fin] at h2
  refine (add_le_add cubeM_Zs_bad h2).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  unfold fg3; ring_nf; rfl

theorem tendsto_fg3 : Tendsto fg3 atTop (𝓝 0) := by
  have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 / 3 : ℝ)) (by norm_num)
    (by norm_num)).const_mul 4
  have h2 := (tendsto_self_mul_const_pow_of_lt_one (r := (2 / 3 : ℝ)) (by norm_num)
    (by norm_num)).const_mul 3
  have := h1.add h2
  rw [mul_zero, mul_zero, add_zero] at this
  refine this.congr fun N => ?_
  unfold fg3; ring

/-! ### `g4`: the squared row products -/

/-- The failure probability of `g4`. -/
def fg4 (N : ℕ) : ℝ := N * (9 / 10 : ℝ) ^ N

lemma cubeM_SQ2_bad (i : Fin N) :
    cubeM N {w | ¬ SQ2 w i ≤ 6 * (2 / 3 : ℝ) ^ N} ≤ ENNReal.ofReal ((9 / 10 : ℝ) ^ N) := by
  obtain ⟨n, rfl⟩ := exists_succ_of_fin i
  set g : (Fin (n + 1) → ℝ) → ℝ := fun v => (∏ j ∈ univ.erase i, clamp01 (v j)) ^ 2 with hgdef
  have hmean : (2 : ℝ) ^ (n + 1) * ∫ v, g v ∂rowM (n + 1) = 2 * (2 / 3 : ℝ) ^ n := by
    rw [hgdef, integral_rowQ_pow, Nat.add_sub_cancel, pow_succ, mul_comm, ← mul_assoc,
      mul_comm _ ((2 : ℝ) ^ n), ← mul_pow]
    norm_num; ring
  have hsq : ∫ v, g v ^ 2 ∂rowM (n + 1) = (1 / 5 : ℝ) ^ n := by
    simp_rw [hgdef, ← pow_mul]
    rw [integral_rowQ_pow, Nat.add_sub_cancel]; norm_num
  have hsub : {w : Param (n + 1) | ¬ SQ2 w i ≤ 6 * (2 / 3 : ℝ) ^ (n + 1)} ⊆
      {w | 2 * (2 / 3 : ℝ) ^ n ≤ |∑ r, g (w r) - 2 ^ (n + 1) * ∫ v, g v ∂rowM (n + 1)|} := by
    intro w hw
    rw [Set.mem_ofPred_eq, hmean]
    change 2 * (2 / 3 : ℝ) ^ n ≤ |SQ2 w i - 2 * (2 / 3 : ℝ) ^ n|
    have ha : (0 : ℝ) < (2 / 3 : ℝ) ^ n := by positivity
    simp only [Set.mem_ofPred_eq, not_le, pow_succ] at hw
    rw [abs_of_pos (by linarith)]; linarith
  have hgm : Measurable g := (measurable_rowQ i).pow_const 2
  refine (measure_mono hsub).trans ((cheb_rows hgm (abs_rowQ_pow_le i 2)
    (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_))
  rw [hsq]
  have ha : (0 : ℝ) < (2 / 3 : ℝ) ^ n := by positivity
  have e1 : (2 : ℝ) ^ (n + 1) * (1 / 5 : ℝ) ^ n = 2 * ((9 / 10 : ℝ) ^ n * ((2 / 3 : ℝ) ^ n) ^ 2) := by
    rw [← pow_mul, mul_comm n 2, pow_mul, ← mul_pow, pow_succ, mul_comm _ (2 : ℝ), mul_assoc,
      ← mul_pow]
    norm_num
  have hb : (0 : ℝ) ≤ (9 / 10 : ℝ) ^ n := by positivity
  rw [e1, div_le_iff₀ (by positivity), pow_succ (9 / 10 : ℝ) n]
  nlinarith [mul_nonneg hb (sq_nonneg ((2 / 3 : ℝ) ^ n))]

/-- **`g4` fails with probability at most `fg4 N`.** -/
theorem cubeM_not_g4 :
    cubeM N {w | ¬ ∀ i, SQ2 w i ≤ 6 * (2 / 3 : ℝ) ^ N} ≤ ENNReal.ofReal (fg4 N) := by
  have hset : {w : Param N | ¬ ∀ i, SQ2 w i ≤ 6 * (2 / 3 : ℝ) ^ N} =
      ⋃ i, {w | ¬ SQ2 w i ≤ 6 * (2 / 3 : ℝ) ^ N} := by
    ext w; simp
  rw [hset]
  have h := cubeM_iUnion_le _ fun i => cubeM_SQ2_bad (N := N) i
  rw [Fintype.card_fin] at h
  exact h

theorem tendsto_fg4 : Tendsto fg4 atTop (𝓝 0) :=
  tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)

/-! ### `g12`: pairs of nearby rows -/

lemma ham_self (r : State N) : ham r r = 0 := by simp [ham]

lemma ham_le (r r' : State N) : ham r r' ≤ N := by
  unfold ham
  exact (card_le_univ _).trans (by rw [Fintype.card_fin])

lemma card_ham_filter_le (r : State N) (k : ℕ) :
    (univ.filter (fun r' : State N => 1 ≤ ham r r' ∧ ham r r' ≤ k)).card ≤ vk N k := by
  classical
  let φ : Finset (Fin N) → State N := fun A j => if j ∈ A then !r j else r j
  have hsub : univ.filter (fun r' : State N => 1 ≤ ham r r' ∧ ham r r' ≤ k) ⊆
      ((Icc 1 k).biUnion fun m => powersetCard m (univ : Finset (Fin N))).image φ := by
    intro r' hr'
    simp only [mem_filter, mem_univ, true_and] at hr'
    refine mem_image.2 ⟨univ.filter fun j => r j ≠ r' j, ?_, ?_⟩
    · simp only [mem_biUnion, mem_Icc, mem_powersetCard]
      exact ⟨ham r r', hr', subset_univ _, rfl⟩
    · funext j
      simp only [φ, mem_filter, mem_univ, true_and]
      split_ifs with h
      · cases hj : r j <;> cases hj' : r' j <;> simp_all
      · simpa using h
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ((Icc 1 k).biUnion fun m => powersetCard m (univ : Finset (Fin N))).card := card_image_le
    _ ≤ ∑ m ∈ Icc 1 k, (powersetCard m (univ : Finset (Fin N))).card := card_biUnion_le
    _ = vk N k := by simp [vk, card_powersetCard]

lemma vk_mono {k k' : ℕ} (h : k ≤ k') : vk N k ≤ vk N k' :=
  sum_le_sum_of_subset (Icc_subset_Icc_right h)

lemma Xk_nonneg (w : Param N) (k : ℕ) (i : Fin N) : 0 ≤ Xk w k i :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_nonneg (Qw_nonneg _ _ _) (Qw_nonneg _ _ _)

lemma Xk_of_le {k : ℕ} (hk : N ≤ k) (w : Param N) (i : Fin N) : Xk w k i = Xk w N i := by
  unfold Xk
  refine sum_congr rfl fun r _ => ?_
  congr 1
  ext r'
  simp only [mem_filter, mem_univ, true_and]
  have := ham_le r r'
  constructor
  · rintro ⟨h1, _⟩; exact ⟨h1, this⟩
  · rintro ⟨h1, _⟩; exact ⟨h1, this.trans hk⟩

lemma integrable_Qw_mul (i : Fin N) (r r' : State N) :
    Integrable (fun w => Qw w i r * Qw w i r') (cubeM N) :=
  integrable_of_bdd_cubeM ((measurable_Qw i r).mul (measurable_Qw i r')) 1 fun w => by
    rw [abs_of_nonneg (mul_nonneg (Qw_nonneg w i r) (Qw_nonneg w i r'))]
    exact (mul_le_mul (Qw_le_one w i r) (Qw_le_one w i r') (Qw_nonneg w i r')
      zero_le_one).trans (by norm_num)

lemma integrable_Xk (k : ℕ) (i : Fin N) : Integrable (fun w => Xk w k i) (cubeM N) :=
  integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun r' _ => integrable_Qw_mul i r r'

lemma integral_Xk_le (k : ℕ) (i : Fin N) :
    ∫ w, Xk w k i ∂cubeM N ≤ 2 ^ N * vk N k * (1 / 4 : ℝ) ^ (N - 1) := by
  unfold Xk
  rw [integral_finsetSum _ fun r _ => integrable_finsetSum _ fun r' _ => integrable_Qw_mul i r r']
  calc ∑ r, ∫ w, ∑ r' ∈ univ.filter (fun r' => 1 ≤ ham r r' ∧ ham r r' ≤ k),
          Qw w i r * Qw w i r' ∂cubeM N
      = ∑ r, ((univ.filter (fun r' => 1 ≤ ham r r' ∧ ham r r' ≤ k)).card : ℝ) *
          (1 / 4 : ℝ) ^ (N - 1) := by
        refine sum_congr rfl fun r _ => ?_
        rw [integral_finsetSum _ fun r' _ => integrable_Qw_mul i r r']
        rw [sum_congr rfl fun r' hr' => integral_Qw_mul i (r := r) (r' := r') ?_, sum_const,
          nsmul_eq_mul]
        rintro rfl
        simp only [mem_filter, mem_univ, true_and, ham_self] at hr'
        omega
    _ ≤ ∑ _r : State N, (vk N k : ℝ) * (1 / 4 : ℝ) ^ (N - 1) := by
        refine sum_le_sum fun r _ => ?_
        gcongr
        exact_mod_cast card_ham_filter_le r k
    _ = _ := by rw [sum_const, card_state, nsmul_eq_mul]; push_cast; ring

lemma cubeM_Xk_bad (k : ℕ) (i : Fin N) :
    cubeM N {w | ¬ Xk w k i ≤ 4 * (N : ℝ) ^ 3 * vk N k * (1 / 2 : ℝ) ^ N} ≤
      ENNReal.ofReal (1 / (N : ℝ) ^ 3) := by
  obtain ⟨n, rfl⟩ := exists_succ_of_fin i
  rcases Nat.eq_zero_or_pos (vk (n + 1) k) with hv | hv
  · have hempty : {w : Param (n + 1) |
        ¬ Xk w k i ≤ 4 * ((n + 1 : ℕ) : ℝ) ^ 3 * vk (n + 1) k * (1 / 2 : ℝ) ^ (n + 1)} = ∅ := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not, hv,
        Nat.cast_zero, mul_zero, zero_mul]
      unfold Xk
      refine le_of_eq (sum_eq_zero fun r _ => ?_)
      have := card_ham_filter_le r k
      rw [hv, Nat.le_zero, card_eq_zero] at this
      rw [this, sum_empty]
    rw [hempty, measure_empty]
    exact zero_le
  · set ε : ℝ := 4 * ((n + 1 : ℕ) : ℝ) ^ 3 * vk (n + 1) k * (1 / 2 : ℝ) ^ (n + 1) with hε
    have hvpos : (0 : ℝ) < vk (n + 1) k := by exact_mod_cast hv
    have hεpos : 0 < ε := by positivity
    have hsub : {w : Param (n + 1) | ¬ Xk w k i ≤ ε} ⊆ {w | ε ≤ Xk w k i} := by
      intro w hw
      simp only [Set.mem_ofPred_eq, not_le] at hw ⊢
      exact hw.le
    refine (measure_mono hsub).trans ((markov_cubeM (fun w => Xk_nonneg w k i)
      (integrable_Xk k i) hεpos).trans (ENNReal.ofReal_le_ofReal ?_))
    refine (div_le_div_of_nonneg_right (integral_Xk_le k i) hεpos.le).trans (le_of_eq ?_)
    rw [Nat.add_sub_cancel, hε]
    have h : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
    have h4 : (1 / 4 : ℝ) ^ n = (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n := by rw [← mul_pow]; norm_num
    have hM : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 3 := by positivity
    have ha : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    rw [h4, pow_succ (2 : ℝ) n, pow_succ (1 / 2 : ℝ) n, div_eq_div_iff (by positivity) hM.ne']
    linear_combination (2 * (vk (n + 1) k : ℝ) * (1 / 2 : ℝ) ^ n * ((n + 1 : ℕ) : ℝ) ^ 3) * h

/-- The failure probability of `g12`. -/
def fg12 (N : ℕ) : ℝ := 2 / N

/-- **`g12` fails with probability at most `fg12 N`.** Only `k ≤ N` matters, since `Xk w k i`
is constant and `vk N k` is monotone for `k ≥ N`. -/
theorem cubeM_not_g12 :
    cubeM N {w | ¬ ∀ k i, Xk w k i ≤ 4 * (N : ℝ) ^ 3 * vk N k * (1 / 2 : ℝ) ^ N} ≤
      ENNReal.ofReal (fg12 N) := by
  have hsub : {w : Param N | ¬ ∀ k i, Xk w k i ≤ 4 * (N : ℝ) ^ 3 * vk N k * (1 / 2 : ℝ) ^ N} ⊆
      ⋃ k : Fin (N + 1), ⋃ i : Fin N,
        {w | ¬ Xk w k i ≤ 4 * (N : ℝ) ^ 3 * vk N k * (1 / 2 : ℝ) ^ N} := by
    intro w hw
    simp only [Set.mem_ofPred_eq, not_forall, not_le] at hw
    obtain ⟨k, i, h⟩ := hw
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_le]
    by_cases hk : k ≤ N
    · exact ⟨⟨k, Nat.lt_succ_of_le hk⟩, i, h⟩
    · push Not at hk
      refine ⟨⟨N, Nat.lt_succ_self N⟩, i, ?_⟩
      simp only
      rw [← Xk_of_le hk.le w i]
      refine lt_of_le_of_lt ?_ h
      gcongr
      exact vk_mono hk.le
  refine (measure_mono hsub).trans ((cubeM_iUnion_le _ fun (k : Fin (N + 1)) =>
    cubeM_iUnion_le _ fun i => cubeM_Xk_bad (N := N) (k : ℕ) i).trans
    (ENNReal.ofReal_le_ofReal ?_))
  simp only [Fintype.card_fin]
  unfold fg12
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp
  · have hN : (1 : ℝ) ≤ N := by exact_mod_cast hpos
    rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
    push_cast
    have e : ((N : ℝ) ^ 3)⁻¹ = (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * (N : ℝ)⁻¹ := by
      rw [pow_succ, pow_succ, pow_one, mul_inv, mul_inv]
    have hi : (N : ℝ) * (N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    have hi' : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
    rw [e]
    have hx1 : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN
    have heq : ((N : ℝ) + 1) * ((N : ℝ) * ((N : ℝ)⁻¹ * (N : ℝ)⁻¹ * (N : ℝ)⁻¹)) =
        (N : ℝ)⁻¹ + (N : ℝ)⁻¹ * (N : ℝ)⁻¹ := by
      linear_combination ((N : ℝ)⁻¹ * ((N : ℝ) * (N : ℝ)⁻¹ + 1) + (N : ℝ)⁻¹ * (N : ℝ)⁻¹) * hi
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hx1 hi']

theorem tendsto_fg12 : Tendsto fg12 atTop (𝓝 0) :=
  tendsto_const_div_atTop_nhds_zero_nat 2

/-! ### `gU`: the largest next-state probability from the current state -/

/-- A polynomial majorant of `max c (1 - c)`, tangent at `c = 1/5` and `c = 4/5`. -/
def pU (x : ℝ) : ℝ := 16 / 15 - 5 / 3 * clamp01 x + 5 / 3 * clamp01 x ^ 2

lemma measurable_pU : Measurable pU :=
  (measurable_const.sub (measurable_const.mul clamp01_measurable)).add
    (measurable_const.mul (clamp01_measurable.pow_const 2))

lemma max_le_pU (x : ℝ) : max (clamp01 x) (1 - clamp01 x) ≤ pU x := by
  unfold pU
  apply max_le
  · nlinarith [sq_nonneg (clamp01 x - 4 / 5)]
  · nlinarith [sq_nonneg (clamp01 x - 1 / 5)]

lemma pU_nonneg (x : ℝ) : 0 ≤ pU x :=
  (le_max_of_le_left (clamp01_nonneg x)).trans (max_le_pU x)

lemma pU_le_two (x : ℝ) : pU x ≤ 2 := by
  unfold pU
  have h0 := clamp01_nonneg x
  have h1 := clamp01_le_one x
  nlinarith

lemma integral_pU : ∫ x, pU x ∂unif = 71 / 90 := by
  have hc : ∀ e : ℕ, Integrable (fun x => clamp01 x ^ e) unif := fun e =>
    Integrable.of_bound (clamp01_measurable.pow_const e).aestronglyMeasurable 1
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (clamp01_nonneg x) e)]
        exact pow_le_one₀ (clamp01_nonneg x) (clamp01_le_one x))
  have hc1 : Integrable (fun x => clamp01 x) unif := by simpa using hc 1
  have h1 := integral_cl_pow 1
  have h2 := integral_cl_pow 2
  simp only [pow_one] at h1
  have hA : Integrable (fun x => 16 / 15 - 5 / 3 * clamp01 x) unif :=
    (integrable_const _).sub (hc1.const_mul _)
  have e1 : ∫ x, pU x ∂unif =
      ∫ x, (16 / 15 - 5 / 3 * clamp01 x) ∂unif + ∫ x, 5 / 3 * clamp01 x ^ 2 ∂unif :=
    integral_add hA ((hc 2).const_mul _)
  have e2 : ∫ x, (16 / 15 - 5 / 3 * clamp01 x) ∂unif =
      ∫ _x, (16 / 15 : ℝ) ∂unif - ∫ x, 5 / 3 * clamp01 x ∂unif :=
    integral_sub (integrable_const _) (hc1.const_mul _)
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_const, h1, h2]
  simp
  norm_num

/-- **`gU` fails with probability at most `(71/72)^N`.** -/
theorem cubeM_not_gU (s : State N) :
    cubeM N {w | ¬ Mrow w s ≤ (4 / 5 : ℝ) ^ N} ≤ ENNReal.ofReal ((71 / 72 : ℝ) ^ N) := by
  set F : Param N → ℝ := fun w => ∏ j, pU (w s j) with hF
  have hMF : ∀ w, Mrow w s ≤ F w := fun w =>
    prod_le_prod (fun j _ => (le_max_of_le_left (clamp01_nonneg _))) fun j _ => max_le_pU _
  have hsub : {w : Param N | ¬ Mrow w s ≤ (4 / 5 : ℝ) ^ N} ⊆ {w | (4 / 5 : ℝ) ^ N ≤ F w} := by
    intro w hw
    simp only [Set.mem_ofPred_eq, not_le] at hw ⊢
    exact hw.le.trans (hMF w)
  have hFm : Measurable fun v : Fin N → ℝ => ∏ j, pU (v j) :=
    Finset.measurable_prod _ fun j _ => measurable_pU.comp (measurable_pi_apply j)
  have hFint : Integrable F (cubeM N) :=
    integrable_of_bdd_cubeM (hFm.comp (measurable_pi_apply s)) (2 ^ N) fun w => by
      rw [hF, abs_of_nonneg (prod_nonneg fun j _ => pU_nonneg _)]
      calc ∏ j, pU (w s j) ≤ ∏ _j : Fin N, (2 : ℝ) :=
            prod_le_prod (fun j _ => pU_nonneg _) fun j _ => pU_le_two _
        _ = 2 ^ N := by rw [prod_const, card_univ, Fintype.card_fin]
  have hEF : ∫ w, F w ∂cubeM N = (71 / 90 : ℝ) ^ N := by
    rw [hF, integral_row_eval (g := fun v => ∏ j, pU (v j)) hFm.aestronglyMeasurable s]
    unfold rowM
    rw [integral_fintype_prod_eq_prod (fun (_ : Fin N) x => pU x)]
    simp only [integral_pU, prod_const, card_univ, Fintype.card_fin]
  refine (measure_mono hsub).trans ((markov_cubeM (fun w => prod_nonneg fun j _ => pU_nonneg _)
    hFint (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_))
  rw [hEF, ← div_pow]
  norm_num

theorem tendsto_fgU : Tendsto (fun N : ℕ => (71 / 72 : ℝ) ^ N) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

end

end Census
end IIT
