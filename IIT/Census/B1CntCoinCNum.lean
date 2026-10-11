/-
Census, B1, W14 work package WP5 (part 7): the numbers of the coin (W5 Lemma E2', G-W14-4).

Thresholds (on fresh sums, scaled by `a = 2^d`): `λ1 = A0 + 2κN + 3κ0`, `λ2 = A0 + κN - 5κ0/2`,
`λ3 = x2 - 3κ0`, `θ = (1 - 2/m) A0`, with `a A0 = q zA`, `q = √(a/12)`, `zA = √(2 ln N)`.
Gaussian levels: `zA + 1/N` (lower, Mills), `2√(ln N)`, `zA`, `(1 - 3/m) zA` (upper, Mills).
GC error `w5err C N = C (a/2)^{-1/8}` (`N² w5err ≤ 10^{-6}` eventually).
Final: `2 d (G1 - G3)(1 - 2N G2 - N G4) ≥ 1/(100 √(ln N))` (true value of the left side `≈ 0.0188/√(ln N)`).

No `sorry`.
-/
import IIT.Census.B1CntCoinTail

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

noncomputable def w5lam1 (N : ℕ) : ℝ := A0C N + 2 * kapN N + 3 * kap0 N
noncomputable def w5lam2 (N : ℕ) : ℝ := A0C N + kapN N - 5 / 2 * kap0 N
noncomputable def w5lam3 (N : ℕ) : ℝ := x2C N - 3 * kap0 N
noncomputable def w5th (N : ℕ) : ℝ := (1 - 2 / mX N) * A0C N
noncomputable def w5zA (N : ℕ) : ℝ := Real.sqrt (2 * Real.log N)
noncomputable def w5q (N : ℕ) : ℝ := Real.sqrt ((2 : ℝ) ^ dX N / 12)
noncomputable def w5err (C : ℝ) (N : ℕ) : ℝ := C * ((2 : ℝ) ^ dX N / 2) ^ (-(1 / 8 : ℝ))

/-- Mills lower and upper forms. -/
noncomputable def w5mlo (z : ℝ) : ℝ :=
  Real.exp (-(z ^ 2 / 2)) / Real.sqrt (2 * Real.pi) * (z / (1 + z ^ 2))
noncomputable def w5mup (z : ℝ) : ℝ := Real.exp (-(z ^ 2 / 2)) / Real.sqrt (2 * Real.pi) / z

/-! ### Identities -/

lemma w5_a_sigC (N : ℕ) : 2 ^ dX N * sigC N = w5q N := by
  unfold sigC w5q
  have ha : (0 : ℝ) < 2 ^ dX N := by positivity
  rw [show (2 : ℝ) ^ dX N / 12 = (2 ^ dX N) ^ 2 * (1 / (12 * 2 ^ dX N)) by field_simp,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha.le]

lemma w5_aA0_q (N : ℕ) : 2 ^ dX N * A0C N = w5q N * w5zA N := by
  unfold A0C w5zA; rw [← mul_assoc, w5_a_sigC]

lemma w5_ax2_q (N : ℕ) : 2 ^ dX N * x2C N = w5q N * Real.sqrt (6 * Real.log N) := by
  unfold x2C; rw [← mul_assoc, w5_a_sigC]

lemma w5_zA_sq (N : ℕ) : w5zA N ^ 2 = 2 * Real.log N := by
  unfold w5zA; rw [Real.sq_sqrt (by have := Real.log_natCast_nonneg N; positivity)]

lemma w5_q_sq (N : ℕ) : w5q N ^ 2 = (2 : ℝ) ^ dX N / 12 := by
  unfold w5q; rw [Real.sq_sqrt (by positivity)]

lemma w5_q_ge (N : ℕ) : Real.sqrt ((2 : ℝ) ^ dX N) / 4 ≤ w5q N := by
  unfold w5q
  rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 12)]
  have h12 : Real.sqrt 12 ≤ 4 := by
    rw [show (4 : ℝ) = Real.sqrt (4 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h12p : 0 < Real.sqrt 12 := Real.sqrt_pos.2 (by norm_num)
  rw [div_le_div_iff₀ (by norm_num) h12p]
  exact mul_le_mul_of_nonneg_left h12 (Real.sqrt_nonneg _)

lemma w5_sqrt_two_pi : 5 / 2 ≤ Real.sqrt (2 * Real.pi) ∧ Real.sqrt (2 * Real.pi) ≤ 13 / 5 := by
  have h1 := Real.pi_gt_d2
  have h2 := Real.pi_lt_d2
  constructor
  · rw [show (5 : ℝ) / 2 = Real.sqrt ((5 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  · rw [show (13 : ℝ) / 5 = Real.sqrt ((13 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)

/-! ### Eventual facts -/

lemma w5_ev_log100 : ∀ᶠ N : ℕ in atTop, (100 : ℝ) ≤ Real.log N :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 100

lemma w5_ev_err (C : ℝ) (hC : 0 ≤ C) : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ 2 * w5err C N ≤ 1 / 10 ^ 6 := by
  have hc : (0 : ℝ) < Real.log 2 / 240 := by positivity
  filter_upwards [ev_poly_exp 2 (10 ^ 6 * C * Real.exp (Real.log 2 / 8)) hc one_pos,
    eventually_ge_atTop 1] with N hN hN1
  have hd : (N : ℝ) / 30 ≤ dX N := by
    have : N ≤ 30 * dX N := by unfold dX; omega
    have : (N : ℝ) ≤ 30 * dX N := by exact_mod_cast this
    linarith
  have hd1 : 1 ≤ dX N := by unfold dX; omega
  have hpos : (0 : ℝ) < 2 ^ dX N / 2 := by positivity
  have hlog : Real.log ((2 : ℝ) ^ dX N / 2) = (dX N - 1 : ℝ) * Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow]; ring
  have hE : w5err C N ≤ C * Real.exp (Real.log 2 / 8) * Real.exp (-(Real.log 2 / 240 * N)) := by
    unfold w5err
    rw [Real.rpow_def_of_pos hpos, hlog]
    have e : C * Real.exp (Real.log 2 / 8) * Real.exp (-(Real.log 2 / 240 * N)) =
        C * Real.exp (Real.log 2 / 8 + -(Real.log 2 / 240 * N)) := by
      rw [mul_assoc, ← Real.exp_add]
    rw [e]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC
    have hl2 : 0 < Real.log 2 := by positivity
    have : Real.log 2 * ((N : ℝ) / 30) ≤ Real.log 2 * (dX N : ℝ) := mul_le_mul_of_nonneg_left hd hl2.le
    nlinarith
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  calc (N : ℝ) ^ 2 * w5err C N
      ≤ (N : ℝ) ^ 2 * (C * Real.exp (Real.log 2 / 8) * Real.exp (-(Real.log 2 / 240 * N))) :=
        mul_le_mul_of_nonneg_left hE hN0
    _ = (10 ^ 6 * C * Real.exp (Real.log 2 / 8) * (N : ℝ) ^ 2 *
          Real.exp (-(Real.log 2 / 240 * N))) / 10 ^ 6 := by ring
    _ ≤ 1 / 10 ^ 6 := by rw [div_le_div_iff_of_pos_right (by norm_num)]; exact hN.le

lemma w5_err_le (C : ℝ) (hC : 0 ≤ C) {N n : ℕ} (hn : (2 : ℝ) ^ dX N / 2 ≤ n) :
    C * (n : ℝ) ^ (-(1 / 8 : ℝ)) ≤ w5err C N := by
  unfold w5err
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (by positivity) hn (by norm_num)) hC

/-! ### The Gaussian-level requirements -/

lemma w5_req1 {N n : ℕ} (hN1 : 1 ≤ N) (h2d : 2 * dX N ≤ N) (hP : 20000 * (N : ℝ) ^ 5 ≤ Real.sqrt (2 ^ dX N))
    (hzA : w5zA N ≤ N) (hd2 : (dX N : ℝ) ^ 2 ≤ 2 ^ dX N / 2)
    (hn : (2 : ℝ) ^ dX N - (dX N : ℝ) ^ 2 ≤ n) :
    2 ^ dX N * w5lam1 N ≤ (w5zA N + 1 / N) * Real.sqrt ((n : ℝ) / 12) := by
  set a : ℝ := 2 ^ dX N with ha_def
  have ha : 0 < a := by positivity
  set q := w5q N with hq_def
  set q' := Real.sqrt ((a - (dX N : ℝ) ^ 2) / 12) with hq'_def
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hN5 : (0 : ℝ) < (N : ℝ) ^ 5 := by positivity
  have hd0 : (0 : ℝ) ≤ (dX N : ℝ) ^ 2 := by positivity
  have hq2 : q ^ 2 = a / 12 := w5_q_sq N
  have hq'2 : q' ^ 2 = (a - (dX N : ℝ) ^ 2) / 12 := Real.sq_sqrt (by linarith)
  have hqge := w5_q_ge N
  rw [← ha_def, ← hq_def] at hqge
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq'0 : 0 ≤ q' := Real.sqrt_nonneg _
  have hq'q : q' ≤ q := by
    rw [hq_def]; unfold w5q; rw [← ha_def]
    exact Real.sqrt_le_sqrt (by linarith)
  have hq'half : q / 2 ≤ q' := by
    have : (q / 2) ^ 2 ≤ q' ^ 2 := by rw [div_pow, hq2, hq'2]; linarith
    exact (sq_le_sq₀ (by linarith) hq'0).1 this
  have hq'big : 89 * (N : ℝ) ^ 5 ≤ q' := by linarith
  have hq'pos : 0 < q' := by linarith
  have hzA0 : 0 ≤ w5zA N := Real.sqrt_nonneg _
  have hκ := w5_a_kapN_le hN1 h2d
  rw [← ha_def] at hκ
  have hk0 : a * kap0 N = (dX N : ℝ) ^ 2 := by unfold kap0; rw [← ha_def]; field_simp
  have hdN : (dX N : ℝ) ≤ N := by
    have : dX N ≤ N := by omega
    exact_mod_cast this
  have hd4 : (dX N : ℝ) ^ 2 ≤ (N : ℝ) ^ 4 := by
    calc (dX N : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hdN 2
      _ ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ hNr (by norm_num)
  have hD1 : a * (2 * kapN N + 3 * kap0 N) ≤ 88 * (N : ℝ) ^ 4 := by
    have e : a * (2 * kapN N + 3 * kap0 N) = 2 * (a * kapN N) + 3 * (a * kap0 N) := by ring
    rw [e, hk0]; linarith
  have hdiff : (q - q') * q' ≤ (dX N : ℝ) ^ 2 / 12 := by
    have e : (q - q') * (q + q') = q ^ 2 - q' ^ 2 := by ring
    rw [hq2, hq'2] at e
    have e2 : (q - q') * (q + q') = (q - q') * q' + (q - q') * q := by ring
    have : 0 ≤ (q - q') * q := mul_nonneg (by linarith) hq0
    linarith
  have hsq : q' ≤ Real.sqrt ((n : ℝ) / 12) := Real.sqrt_le_sqrt (by linarith)
  have hA : a * w5lam1 N = q * w5zA N + a * (2 * kapN N + 3 * kap0 N) := by
    unfold w5lam1
    have := w5_aA0_q N
    rw [← ha_def, ← hq_def] at this
    linear_combination this
  rw [hA]
  have hzd : w5zA N * ((q - q') * q') ≤ (N : ℝ) * ((N : ℝ) ^ 4 / 12) := by
    have : (q - q') * q' ≤ (N : ℝ) ^ 4 / 12 := by linarith
    have h0 : 0 ≤ (q - q') * q' := mul_nonneg (by linarith) hq'0
    calc w5zA N * ((q - q') * q') ≤ w5zA N * ((N : ℝ) ^ 4 / 12) :=
          mul_le_mul_of_nonneg_left this hzA0
      _ ≤ (N : ℝ) * ((N : ℝ) ^ 4 / 12) := mul_le_mul_of_nonneg_right hzA (by positivity)
  have h5 : a * (2 * kapN N + 3 * kap0 N) * q' ≤ 88 * (N : ℝ) ^ 4 * q' :=
    mul_le_mul_of_nonneg_right hD1 hq'pos.le
  have h6 : 89 * (N : ℝ) ^ 4 * q' ≤ q' * q' / N := by
    rw [le_div_iff₀ hN0]
    have h1 : 89 * (N : ℝ) ^ 5 * q' ≤ q' * q' := mul_le_mul_of_nonneg_right hq'big hq'pos.le
    have e : 89 * (N : ℝ) ^ 4 * q' * N = 89 * (N : ℝ) ^ 5 * q' := by ring
    linarith
  have h7 : (N : ℝ) * ((N : ℝ) ^ 4 / 12) ≤ (N : ℝ) ^ 4 * q' := by
    have hNq : (N : ℝ) ≤ q' := by
      have : (N : ℝ) ≤ (N : ℝ) ^ 5 := by
        calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (N : ℝ) ^ 5 := pow_le_pow_right₀ hNr (by norm_num)
      linarith
    have h1 : (N : ℝ) ^ 4 * N ≤ (N : ℝ) ^ 4 * q' := mul_le_mul_of_nonneg_left hNq (by positivity)
    have e : (N : ℝ) * ((N : ℝ) ^ 4 / 12) = (N : ℝ) ^ 4 * N / 12 := by ring
    have : (0 : ℝ) ≤ (N : ℝ) ^ 4 * N := by positivity
    linarith
  have key : (q * w5zA N + a * (2 * kapN N + 3 * kap0 N)) * q' ≤ ((w5zA N + 1 / N) * q') * q' := by
    have e1 : (q * w5zA N + a * (2 * kapN N + 3 * kap0 N)) * q' =
        w5zA N * q' * q' + w5zA N * ((q - q') * q') + a * (2 * kapN N + 3 * kap0 N) * q' := by ring
    have e2 : ((w5zA N + 1 / N) * q') * q' = w5zA N * q' * q' + q' * q' / N := by
      field_simp
    rw [e1, e2]
    linarith
  have h3 : q * w5zA N + a * (2 * kapN N + 3 * kap0 N) ≤ (w5zA N + 1 / N) * q' :=
    le_of_mul_le_mul_right key hq'pos
  calc q * w5zA N + a * (2 * kapN N + 3 * kap0 N) ≤ (w5zA N + 1 / N) * q' := h3
    _ ≤ (w5zA N + 1 / N) * Real.sqrt ((n : ℝ) / 12) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)

lemma w5_req3 {N n : ℕ} (hN1 : 1 ≤ N) (hL : 1 ≤ Real.log N) (hP : 20000 * (N : ℝ) ^ 5 ≤ Real.sqrt (2 ^ dX N))
    (hdN : dX N ≤ N) (hn : (n : ℝ) ≤ 2 ^ dX N) :
    2 * Real.sqrt (Real.log N) * Real.sqrt ((n : ℝ) / 12) < 2 ^ dX N * w5lam3 N := by
  set a : ℝ := 2 ^ dX N with ha_def
  have ha : 0 < a := by positivity
  set q := w5q N with hq_def
  set ℓ := Real.sqrt (Real.log N) with hℓ
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hL
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hqge := w5_q_ge N
  rw [← ha_def, ← hq_def] at hqge
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hsq : Real.sqrt ((n : ℝ) / 12) ≤ q := Real.sqrt_le_sqrt (by linarith)
  have h6 : Real.sqrt (6 * Real.log N) = Real.sqrt 6 * ℓ := Real.sqrt_mul (by norm_num) _
  have hs6 : 61 / 25 ≤ Real.sqrt 6 := (Real.le_sqrt' (by norm_num)).2 (by norm_num)
  have hk0 : a * kap0 N = (dX N : ℝ) ^ 2 := by unfold kap0; rw [← ha_def]; field_simp
  have hA : a * w5lam3 N = q * (Real.sqrt 6 * ℓ) - 3 * (dX N : ℝ) ^ 2 := by
    unfold w5lam3
    have := w5_ax2_q N
    rw [← ha_def, ← hq_def, h6] at this
    rw [mul_sub, this, show a * (3 * kap0 N) = 3 * (a * kap0 N) by ring, hk0]
  rw [hA]
  have hdN' : (dX N : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hdN) 2
  have hqN : 20 * (N : ℝ) ^ 2 ≤ q := by
    have : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 5 := pow_le_pow_right₀ hNr (by norm_num)
    linarith
  have h1 : 2 * ℓ * Real.sqrt ((n : ℝ) / 12) ≤ 2 * ℓ * q :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have hA1 : q * (61 / 25 * ℓ) ≤ q * (Real.sqrt 6 * ℓ) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs6 hℓ0) hq0
  have hqℓ : q * 1 ≤ q * ℓ := mul_le_mul_of_nonneg_left hℓ1 hq0
  have e1 : q * (61 / 25 * ℓ) = 61 / 25 * (q * ℓ) := by ring
  have e2 : 2 * ℓ * q = 2 * (q * ℓ) := by ring
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  linarith

lemma w5_req2 {N n : ℕ} (hL : 0 < Real.log N) (hn : (n : ℝ) ≤ 2 ^ dX N) :
    w5zA N * Real.sqrt ((n : ℝ) / 12) < 2 ^ dX N * w5lam2 N := by
  set a : ℝ := 2 ^ dX N with ha_def
  have ha : 0 < a := by positivity
  have hsq : Real.sqrt ((n : ℝ) / 12) ≤ w5q N := by
    unfold w5q; exact Real.sqrt_le_sqrt (by linarith)
  have hA : a * w5lam2 N = w5q N * w5zA N + a * (kapN N - 5 / 2 * kap0 N) := by
    unfold w5lam2; rw [← w5_aA0_q]; ring
  rw [hA]
  have hκ : 5 / 2 * kap0 N < kapN N := by
    unfold kapN
    have := w5_kap0_nonneg N
    have := w5_epsN_nonneg N
    have : 0 < 6 * Real.log N / 2 ^ dX N := by positivity
    linarith
  have h1 : 0 < a * (kapN N - 5 / 2 * kap0 N) := mul_pos ha (by linarith)
  have h2 : w5zA N * Real.sqrt ((n : ℝ) / 12) ≤ w5zA N * w5q N :=
    mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
  linarith

lemma w5_req4 {N n : ℕ} (hL : 0 < Real.log N) (hm : 3 ≤ mX N) (hn : (n : ℝ) ≤ 2 ^ dX N) :
    (1 - 3 / mX N) * w5zA N * Real.sqrt ((n : ℝ) / 12) < 2 ^ dX N * w5th N := by
  have hsq : Real.sqrt ((n : ℝ) / 12) ≤ w5q N := by
    unfold w5q; exact Real.sqrt_le_sqrt (by linarith)
  have hA : (2 : ℝ) ^ dX N * w5th N = (1 - 2 / mX N) * (w5q N * w5zA N) := by
    unfold w5th; rw [← w5_aA0_q]; ring
  rw [hA]
  have hm0 : 0 < mX N := by linarith
  have hc : 0 ≤ 1 - 3 / mX N := by rw [sub_nonneg, div_le_one hm0]; exact hm
  have hzA : 0 < w5zA N := Real.sqrt_pos.2 (by positivity)
  have hq : 0 < w5q N := Real.sqrt_pos.2 (by positivity)
  have h1 : (1 - 3 / mX N) * w5zA N * Real.sqrt ((n : ℝ) / 12) ≤ (1 - 3 / mX N) * w5zA N * w5q N :=
    mul_le_mul_of_nonneg_left hsq (mul_nonneg hc hzA.le)
  have h2 : 3 / mX N > 2 / mX N := div_lt_div_of_pos_right (by norm_num) hm0
  have h3 : 0 < w5zA N * w5q N := mul_pos hzA hq
  nlinarith

end Census
end IIT
