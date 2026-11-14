/-
Census of IIT 2.0: with `L = log₂ N + 25`, the bound of `bad_bound` tends to `0`.
-/
import IIT2.Census.Union

namespace IIT2

open Filter Topology Real

/-- The threshold separating small and large `m`. -/
def Lsel (N : ℕ) : ℕ := Nat.log 2 N + 25

noncomputable def badB (N : ℕ) : ℝ :=
  2 ^ N * N * 2 ^ N * (2 * Real.exp (-(1 / 2000) ^ 2 * 2 ^ Lsel N / 2)) +
    Lsel N * (N : ℝ) ^ Lsel N * (7 * 10 ^ 6 * (8 ^ Lsel N * (2 / 3) ^ N))

lemma two_pow_Lsel (N : ℕ) : (2 : ℝ) ^ 24 * N ≤ 2 ^ Lsel N := by
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
  have h' : (N : ℝ) ≤ 2 ^ (Nat.log 2 N + 1) := by exact_mod_cast h.le
  unfold Lsel
  rw [show Nat.log 2 N + 25 = (Nat.log 2 N + 1) + 24 by ring, pow_add]
  nlinarith [show (0 : ℝ) < 2 ^ 24 by positivity]

lemma exp_two_gt : (4 : ℝ) < Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]; nlinarith

lemma term1_tendsto : Tendsto (fun N : ℕ =>
    2 ^ N * N * 2 ^ N * (2 * Real.exp (-(1 / 2000) ^ 2 * 2 ^ Lsel N / 2))) atTop (𝓝 0) := by
  set r : ℝ := 4 * Real.exp (-2)
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by
    have h := exp_two_gt
    have : Real.exp (-2) = (Real.exp 2)⁻¹ := Real.exp_neg 2
    simp only [r, this]
    rw [← div_eq_mul_inv, div_lt_one (by positivity)]; exact h
  have hlim := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 1
    (show |r| < 1 by rw [abs_of_pos hr0]; exact hr1)).const_mul 2
  rw [mul_zero] at hlim
  refine squeeze_zero (fun N => by positivity) (fun N => ?_) hlim
  have hL := two_pow_Lsel N
  have hexp : Real.exp (-(1 / 2000) ^ 2 * 2 ^ Lsel N / 2) ≤ Real.exp (-2) ^ N := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have : (2 : ℝ) ^ N * N * 2 ^ N * (2 * Real.exp (-(1 / 2000) ^ 2 * 2 ^ Lsel N / 2)) ≤
      2 ^ N * N * 2 ^ N * (2 * Real.exp (-2) ^ N) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  refine this.trans (le_of_eq ?_)
  simp only [r, mul_pow, pow_one]
  rw [show (4 : ℝ) ^ N = 2 ^ N * 2 ^ N by rw [← mul_pow]; norm_num]
  ring

lemma log_two_pos' : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

lemma natLog_le (N : ℕ) (hN : 1 ≤ N) : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
  have h := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
  have h' : (2 : ℝ) ^ Nat.log 2 N ≤ N := by exact_mod_cast h
  rw [← Real.log_pow]
  exact Real.log_le_log (by positivity) h'

lemma term2_tendsto : Tendsto (fun N : ℕ =>
    Lsel N * (N : ℝ) ^ Lsel N * (7 * 10 ^ 6 * (8 ^ Lsel N * (2 / 3) ^ N))) atTop (𝓝 0) := by
  -- eventual bounds on log
  have hA : ∀ᶠ N : ℕ in atTop, Real.log N ^ 2 ≤ (1 / 20) * N := by
    have := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (show (0 : ℝ) < 1 / 20 by norm_num)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually this,
      eventually_ge_atTop 1] with N hN h1
    simp only [Real.norm_eq_abs, id] at hN
    rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (Nat.cast_nonneg N)] at hN
    exact hN
  have hB : ∀ᶠ N : ℕ in atTop, Real.log N ≤ (1 / 1000) * N := by
    have := (Real.isLittleO_log_id_atTop).bound (show (0 : ℝ) < 1 / 1000 by norm_num)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually this,
      eventually_ge_atTop 1] with N hN h1
    simp only [Real.norm_eq_abs, id] at hN
    have hN' : |(N : ℝ)| = N := abs_of_nonneg (Nat.cast_nonneg N)
    rw [hN'] at hN
    exact (le_abs_self _).trans hN
  set C : ℝ := 26 * 8 ^ 25 * (7 * 10 ^ 6)
  have hlim : Tendsto (fun N : ℕ => C * Real.exp (-(1 / 5) * N)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg
      (show -(1 / 5 : ℝ) < 0 by norm_num))).const_mul C
    rw [mul_zero] at this
    exact this
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hlim
  filter_upwards [hA, hB, eventually_ge_atTop 1] with N hA hB h1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast h1
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hl2 := log_two_gt
  -- the pieces
  have hLle : (Lsel N : ℝ) ≤ 26 * N := by
    have hlog : (Nat.log 2 N : ℝ) ≤ N := by exact_mod_cast (Nat.log_lt_self 2 (by omega)).le
    have : (Lsel N : ℝ) = Nat.log 2 N + 25 := by unfold Lsel; push_cast; ring
    linarith
  have h8 : (8 : ℝ) ^ Lsel N ≤ 8 ^ 25 * N ^ 3 := by
    unfold Lsel
    rw [pow_add, mul_comm]
    have h := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
    have h' : (2 : ℝ) ^ Nat.log 2 N ≤ N := by exact_mod_cast h
    have : (8 : ℝ) ^ Nat.log 2 N = (2 ^ Nat.log 2 N) ^ 3 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h' 3) (by positivity)
  have hpow : (N : ℝ) ^ (Lsel N + 4) * (2 / 3) ^ N ≤ Real.exp (-(1 / 5) * N) := by
    have e1 : (N : ℝ) ^ (Lsel N + 4) = Real.exp ((Lsel N + 4 : ℕ) * Real.log N) := by
      rw [Real.exp_nat_mul, Real.exp_log hNpos]
    have e2 : ((2 : ℝ) / 3) ^ N = Real.exp (N * Real.log (2 / 3)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [e1, e2, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hl23 : Real.log (2 / 3) ≤ -(1 / 3) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 / 3 by norm_num); linarith
    have hnl := natLog_le N h1
    have hLr : ((Lsel N + 4 : ℕ) : ℝ) * Real.log 2 ≤ Real.log N + 29 * Real.log 2 := by
      unfold Lsel; push_cast; nlinarith
    have : ((Lsel N + 4 : ℕ) : ℝ) * Real.log N ≤
        (Real.log N + 29 * Real.log 2) / Real.log 2 * Real.log N := by
      apply mul_le_mul_of_nonneg_right _ hlogN
      rw [le_div_iff₀ (by linarith)]; exact hLr
    have h3 : (Real.log N + 29 * Real.log 2) / Real.log 2 * Real.log N =
        Real.log N ^ 2 / Real.log 2 + 29 * Real.log N := by field_simp
    have h4 : Real.log N ^ 2 / Real.log 2 ≤ (1 / 20) * N / (69 / 100) := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    have h5 : (N : ℝ) * Real.log (2 / 3) ≤ -(1 / 3) * N := by nlinarith
    rw [h3] at this
    linarith
  calc (Lsel N : ℝ) * (N : ℝ) ^ Lsel N * (7 * 10 ^ 6 * (8 ^ Lsel N * (2 / 3) ^ N))
      ≤ (26 * N) * (N : ℝ) ^ Lsel N * (7 * 10 ^ 6 * ((8 ^ 25 * N ^ 3) * (2 / 3) ^ N)) := by
        gcongr
    _ = C * ((N : ℝ) ^ (Lsel N + 4) * (2 / 3) ^ N) := by simp only [C]; ring
    _ ≤ C * Real.exp (-(1 / 5) * N) := mul_le_mul_of_nonneg_left hpow (by positivity)

theorem badB_tendsto : Tendsto badB atTop (𝓝 0) := by
  have := term1_tendsto.add term2_tendsto
  rw [add_zero] at this
  exact this

end IIT2
