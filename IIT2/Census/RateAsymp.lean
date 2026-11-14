/-
Census of IIT 2.0, rate: with `L = log₂ N + 27`, eventually `rateB N L ≤ exp(-2N)`.
-/
import IIT2.Census.RateBound

namespace IIT2

open Filter Topology Real

/-- The threshold for the rate. -/
def Lr (N : ℕ) : ℕ := Nat.log 2 N + 27

lemma pow_eq_exp {b : ℝ} (hb : 0 < b) (n : ℕ) : b ^ n = Real.exp (n * Real.log b) := by
  rw [Real.exp_nat_mul, Real.exp_log hb]

lemma two_pow_Lr_ge (N : ℕ) : (2 : ℝ) ^ 26 * N ≤ 2 ^ Lr N := by
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
  have h' : (N : ℝ) ≤ 2 ^ (Nat.log 2 N + 1) := by exact_mod_cast h.le
  unfold Lr
  rw [show Nat.log 2 N + 27 = (Nat.log 2 N + 1) + 26 by ring, pow_add]
  nlinarith [show (0 : ℝ) < 2 ^ 26 by positivity]

lemma two_pow_Lr_le (N : ℕ) (hN : 1 ≤ N) : (2 : ℝ) ^ Lr N ≤ 2 ^ 27 * N := by
  have h := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
  have h' : (2 : ℝ) ^ Nat.log 2 N ≤ N := by exact_mod_cast h
  unfold Lr
  rw [pow_add]
  nlinarith [show (0 : ℝ) < 2 ^ 27 by positivity]

lemma Lr_le_log (N : ℕ) (hN : 1 ≤ N) : (Lr N : ℝ) ≤ 145 / 100 * Real.log N + 28 := by
  have h := natLog_le N hN
  have hl := log_two_gt
  have hl' := Real.log_two_lt_d9
  have : (Lr N : ℝ) = Nat.log 2 N + 27 := by unfold Lr; push_cast; ring
  rw [this]
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have : (Nat.log 2 N : ℝ) ≤ Real.log N / Real.log 2 := by
    rw [le_div_iff₀ (by linarith)]; exact h
  have : Real.log N / Real.log 2 ≤ Real.log N / (69 / 100) :=
    div_le_div_of_nonneg_left hlog0 (by norm_num) (by linarith)
  have : Real.log N / (69 / 100) ≤ 145 / 100 * Real.log N := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  linarith

lemma ev_log_le (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ N : ℕ in atTop, Real.log N ≤ δ * N := by
  have := (Real.isLittleO_log_id_atTop).bound hδ
  filter_upwards [tendsto_natCast_atTop_atTop.eventually this, eventually_ge_atTop 1] with N hN h1
  simp only [Real.norm_eq_abs, id] at hN
  have hN' : |(N : ℝ)| = N := abs_of_nonneg (Nat.cast_nonneg N)
  rw [hN'] at hN
  exact (le_abs_self _).trans hN

lemma ev_log_sq_le (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ N : ℕ in atTop, Real.log N ^ 2 ≤ δ * N := by
  have := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound hδ
  filter_upwards [tendsto_natCast_atTop_atTop.eventually this, eventually_ge_atTop 1] with N hN h1
  simp only [Real.norm_eq_abs, id] at hN
  rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (Nat.cast_nonneg N)] at hN
  exact hN

lemma ev_poly_geom (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ k * r ^ N ≤ ε := by
  have := tendsto_pow_const_mul_const_pow_of_abs_lt_one k (show |r| < 1 by rwa [abs_of_nonneg hr0])
  exact (this.eventually (ge_mem_nhds hε))

lemma exp_two_ge_three : (3 : ℝ) ≤ Real.exp 2 := by linarith [exp_two_gt]

lemma exp_three_ge_ten : (10 : ℝ) ≤ Real.exp 3 := by
  have h1 := Real.exp_one_gt_d9
  have h2 := exp_two_gt
  have : Real.exp 3 = Real.exp 2 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]; nlinarith

/-- The three pieces, each at most `exp(-2N-2)`. -/
lemma piece1 : ∀ᶠ N : ℕ in atTop,
    2 ^ N * (N : ℝ) * 2 ^ N * (2 * Real.exp (-(1 / 2000) ^ 2 * 2 ^ Lr N / 2)) ≤
      Real.exp (-2 * N - 2) := by
  filter_upwards [ev_log_le (1 / 10000) (by norm_num), eventually_ge_atTop 1] with N hl h1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast h1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast h1
  have hL := two_pow_Lr_ge N
  have hl2 := Real.log_two_lt_d9
  have e1 : (2 : ℝ) ^ N * N * 2 ^ N * (2 * Real.exp (-(1 / 2000) ^ 2 * 2 ^ Lr N / 2)) =
      2 * (Real.exp (Real.log N) * Real.exp (N * Real.log 2) * Real.exp (N * Real.log 2) *
        Real.exp (-(1 / 2000) ^ 2 * 2 ^ Lr N / 2)) := by
    rw [Real.exp_log hN0, ← pow_eq_exp (by norm_num)]; ring
  rw [e1, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  calc 2 * Real.exp (Real.log N + N * Real.log 2 + N * Real.log 2 +
        -(1 / 2000) ^ 2 * 2 ^ Lr N / 2)
      ≤ Real.exp 1 * Real.exp (Real.log N + N * Real.log 2 + N * Real.log 2 +
        -(1 / 2000) ^ 2 * 2 ^ Lr N / 2) := by gcongr
    _ = Real.exp (1 + (Real.log N + N * Real.log 2 + N * Real.log 2 +
        -(1 / 2000) ^ 2 * 2 ^ Lr N / 2)) := by rw [← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith

lemma piece2 : ∀ᶠ N : ℕ in atTop,
    Lr N * (N : ℝ) ^ Lr N * (3 * (Lr N * (N : ℝ) ^ Lr N * 2 ^ N *
      ((N : ℝ) ^ 252 / 64 ^ (N - Lr N)))) ≤ Real.exp (-2 * N - 2) := by
  filter_upwards [ev_log_le (1 / 10000) (by norm_num), ev_log_sq_le (1 / 10000) (by norm_num),
    eventually_ge_atTop 1000] with N hl hl2 h1
  have hNr : (1000 : ℝ) ≤ N := by exact_mod_cast h1
  have hN0 : (0 : ℝ) < N := by linarith
  set l := Real.log N
  have hl0 : 0 ≤ l := Real.log_nonneg (by linarith)
  have hLl := Lr_le_log N (by omega)
  have hLN : Lr N ≤ N := by
    have : (Lr N : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have hLN' : (Lr N : ℝ) ≤ N := by exact_mod_cast hLN
  have hl2' := Real.log_two_lt_d9
  have hl2'' := log_two_gt
  have hsub : ((N - Lr N : ℕ) : ℝ) = N - Lr N := by push_cast [hLN]; ring
  have e : (Lr N : ℝ) * (N : ℝ) ^ Lr N * (3 * (Lr N * (N : ℝ) ^ Lr N * 2 ^ N *
      ((N : ℝ) ^ 252 / 64 ^ (N - Lr N)))) =
      3 * ((Lr N : ℝ) * Lr N) * Real.exp (Lr N * l + Lr N * l + N * Real.log 2 + 252 * l +
        -(((N - Lr N : ℕ) : ℝ) * Real.log 64)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_neg,
      ← pow_eq_exp hN0, ← pow_eq_exp (show (0 : ℝ) < 2 by norm_num),
      ← pow_eq_exp (show (0 : ℝ) < 64 by norm_num)]
    have : (Real.exp (252 * l)) = (N : ℝ) ^ 252 := by
      rw [show (252 : ℝ) = ((252 : ℕ) : ℝ) by norm_num, ← pow_eq_exp hN0]
    rw [this]
    field_simp
  rw [e]
  have hlog64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  rw [hsub, hlog64]
  have hL2 : (Lr N : ℝ) * Lr N ≤ Real.exp (2 * l) := by
    rw [show (2 : ℝ) * l = l + l by ring, Real.exp_add, Real.exp_log hN0]
    exact mul_le_mul hLN' hLN' (Nat.cast_nonneg _) hN0.le
  have hLlog : (Lr N : ℝ) * l ≤ 145 / 100 * l ^ 2 + 28 * l := by nlinarith
  calc 3 * ((Lr N : ℝ) * Lr N) * Real.exp (Lr N * l + Lr N * l + N * Real.log 2 + 252 * l +
        -((N - Lr N) * (6 * Real.log 2)))
      ≤ Real.exp 2 * Real.exp (2 * l) * Real.exp (Lr N * l + Lr N * l + N * Real.log 2 + 252 * l +
        -((N - Lr N) * (6 * Real.log 2))) := by
        gcongr
        · exact exp_two_ge_three
    _ = Real.exp (2 + 2 * l + (Lr N * l + Lr N * l + N * Real.log 2 + 252 * l +
        -((N - Lr N) * (6 * Real.log 2)))) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith

lemma piece3 : ∀ᶠ N : ℕ in atTop, Lr N * (N : ℝ) ^ Lr N * (10 * eB N (Lr N)) ≤
    Real.exp (-2 * N - 2) := by
  filter_upwards [ev_log_le (1 / 10000) (by norm_num), ev_log_sq_le (1 / 10000) (by norm_num),
    eventually_ge_atTop (2000 * 2 ^ 27 * 20),
    ev_poly_geom 9 (r := 2 / 3) (by norm_num) (by norm_num) (1 / (3 * 2 ^ 27)) (by positivity)]
    with N hl hl2 h1 hgeom
  have hNr : (2000 * 2 ^ 27 * 20 : ℝ) ≤ N := by exact_mod_cast h1
  have hN0 : (0 : ℝ) < N := by linarith
  set l := Real.log N
  have hl0 : 0 ≤ l := Real.log_nonneg (by linarith)
  have hLl := Lr_le_log N (by omega)
  have hLN' : (Lr N : ℝ) ≤ N := by nlinarith
  have hLle := two_pow_Lr_le N (by omega)
  have hLpos : (0 : ℝ) < 2 ^ Lr N := by positivity
  -- the error term
  have herr : 3 * (N : ℝ) ^ 8 * 2 ^ Lr N * (2 / 3) ^ N ≤ 1 := by
    have : 3 * (N : ℝ) ^ 8 * 2 ^ Lr N * (2 / 3) ^ N ≤ 3 * 2 ^ 27 * ((N : ℝ) ^ 9 * (2 / 3) ^ N) := by
      have h0 : (0 : ℝ) ≤ 3 * (N : ℝ) ^ 8 * (2 / 3) ^ N := by positivity
      calc 3 * (N : ℝ) ^ 8 * 2 ^ Lr N * (2 / 3) ^ N = (3 * (N : ℝ) ^ 8 * (2 / 3) ^ N) * 2 ^ Lr N := by
            ring
        _ ≤ (3 * (N : ℝ) ^ 8 * (2 / 3) ^ N) * (2 ^ 27 * N) := mul_le_mul_of_nonneg_left hLle h0
        _ = _ := by ring
    have h3 : 3 * 2 ^ 27 * ((N : ℝ) ^ 9 * (2 / 3) ^ N) ≤ 3 * 2 ^ 27 * (1 / (3 * 2 ^ 27)) :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    have : (3 : ℝ) * 2 ^ 27 * (1 / (3 * 2 ^ 27)) = 1 := by norm_num
    linarith
  -- the main term
  have hmain : 10 * (N : ℝ) ≤ (N : ℝ) ^ 3 / (2000 * 2 ^ Lr N) := by
    rw [le_div_iff₀ (by positivity)]
    have : (2000 : ℝ) * 2 ^ Lr N ≤ 2000 * (2 ^ 27 * N) := by linarith
    have h2 : 10 * (N : ℝ) * (2000 * (2 ^ 27 * N)) ≤ N ^ 3 := by
      have : (10 : ℝ) * (2000 * 2 ^ 27) ≤ N := by linarith
      have := mul_le_mul_of_nonneg_right this (sq_nonneg (N : ℝ))
      nlinarith
    nlinarith
  unfold eB
  have e : (Lr N : ℝ) * (N : ℝ) ^ Lr N = Lr N * Real.exp (Lr N * l) := by
    rw [← pow_eq_exp hN0]
  rw [e]
  have hLe : (Lr N : ℝ) ≤ Real.exp l := by rw [Real.exp_log hN0]; exact hLN'
  have hLlog : (Lr N : ℝ) * l ≤ 145 / 100 * l ^ 2 + 28 * l := by nlinarith
  calc (Lr N : ℝ) * Real.exp (Lr N * l) * (10 * Real.exp (-((N : ℝ) ^ 3 / (2000 * 2 ^ Lr N)) +
        3 * (N : ℝ) ^ 8 * 2 ^ Lr N * (2 / 3) ^ N))
      ≤ Real.exp l * Real.exp (Lr N * l) * (Real.exp 3 * Real.exp (-((N : ℝ) ^ 3 / (2000 * 2 ^ Lr N)) +
        3 * (N : ℝ) ^ 8 * 2 ^ Lr N * (2 / 3) ^ N)) := by
        gcongr
        exact exp_three_ge_ten
    _ = Real.exp (l + Lr N * l + (3 + (-((N : ℝ) ^ 3 / (2000 * 2 ^ Lr N)) +
        3 * (N : ℝ) ^ 8 * 2 ^ Lr N * (2 / 3) ^ N))) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith

theorem rateB_le : ∀ᶠ N : ℕ in atTop, rateB N (Lr N) ≤ Real.exp (-(2 * N)) := by
  filter_upwards [piece1, piece2, piece3] with N h1 h2 h3
  unfold rateB
  have hE : 3 * Real.exp (-2 * N - 2) ≤ Real.exp (-(2 * N)) := by
    have : Real.exp (-2 * N - 2) = Real.exp (-(2 * N)) * Real.exp (-2) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    have h := exp_two_gt
    have : Real.exp (-2) = (Real.exp 2)⁻¹ := Real.exp_neg 2
    rw [this]
    have hp : 0 < Real.exp (-(2 * (N : ℝ))) := Real.exp_pos _
    have h3 : 3 * (Real.exp 2)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by positivity)]; linarith
    nlinarith
  have : (Lr N : ℝ) * (N : ℝ) ^ Lr N * (3 * (Lr N * (N : ℝ) ^ Lr N * 2 ^ N *
      ((N : ℝ) ^ 252 / 64 ^ (N - Lr N))) + 10 * eB N (Lr N)) =
      Lr N * (N : ℝ) ^ Lr N * (3 * (Lr N * (N : ℝ) ^ Lr N * 2 ^ N *
      ((N : ℝ) ^ 252 / 64 ^ (N - Lr N)))) + Lr N * (N : ℝ) ^ Lr N * (10 * eB N (Lr N)) := by ring
  rw [this]
  linarith

lemma ev_side : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ 2 * (N : ℝ) ^ 3 ≤ 2 ^ N ∧ 2 * Lr N < N := by
  filter_upwards [ev_log_le (1 / 10000) (by norm_num), eventually_ge_atTop 1000,
    ev_poly_geom 3 (r := 1 / 2) (by norm_num) (by norm_num) (1 / 2) (by norm_num)]
    with N hl h1 hg
  refine ⟨by omega, ?_, ?_⟩
  · have : (N : ℝ) ^ 3 * (1 / 2) ^ N * 2 ^ N = N ^ 3 := by
      rw [mul_assoc, ← mul_pow]; norm_num
    have hp : (0 : ℝ) < 2 ^ N := by positivity
    nlinarith
  · have hLl := Lr_le_log N (by omega)
    have hNr : (1000 : ℝ) ≤ N := by exact_mod_cast h1
    have : (2 * Lr N : ℝ) < N := by nlinarith
    exact_mod_cast this

end IIT2
