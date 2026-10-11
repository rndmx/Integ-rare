/-
Census, B1, W14 work package WP5 (part 8): the final inequality of the coin (W5 Lemma E2', G-W14-4):
`2 d (G1 - G3)(1 - 2N G2 - N G4) ≥ 1/(100 √(ln N))` with the Mills forms at the explicit levels
`zA + 1/N`, `2√(ln N)`, `zA`, `(1 - 3/m) zA` and the GC error `w5err`.

No `sorry`.
-/
import IIT.Census.B1CntCoinCNum

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-- The algebra of the final inequality. -/
lemma w5_cfinal_alg {n ℓ zA e d G1 G2 G3 G4 : ℝ} (hn : 1 ≤ n) (hℓ : 10 ≤ ℓ) (hℓn : 3000 * ℓ ≤ n)
    (hzA1 : 1414 / 1000 * ℓ ≤ zA) (hzA2 : zA ≤ 14143 / 10000 * ℓ) (he0 : 0 ≤ e)
    (he : n ^ 2 * e ≤ 1 / 10 ^ 6) (hd : n / 30 ≤ d)
    (hG1 : 99 / 100 ≤ 26 / 10 * n * (zA + 2) * G1) (hG3 : n ^ 2 * G3 ≤ 1)
    (hG2 : n * zA * G2 ≤ 4 / 10) (hG4 : n * zA * G4 ≤ 9 / 10) (hG2' : 0 ≤ G2) (hG4' : 0 ≤ G4) :
    0 ≤ 1 - (2 * n * (G2 + e) + n * (G4 + e)) ∧
      1 / (100 * ℓ) ≤ 2 * d * ((G1 - e) - (G3 + e)) * (1 - (2 * n * (G2 + e) + n * (G4 + e))) := by
  have hn0 : 0 < n := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hzA0 : 0 < zA := by linarith
  -- `n e ≤ 10⁻⁶ / n`
  have hne : n * e ≤ 1 / 10 ^ 6 := by
    have : n * e ≤ n ^ 2 * e := by
      have : n ≤ n ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this he0
    linarith
  -- `X ≤ 0.1203`
  have hnG2 : n * G2 ≤ 4 / 10 / zA := by
    rw [le_div_iff₀ hzA0]; linarith [show n * G2 * zA = n * zA * G2 by ring]
  have hnG4 : n * G4 ≤ 9 / 10 / zA := by
    rw [le_div_iff₀ hzA0]; linarith [show n * G4 * zA = n * zA * G4 by ring]
  have hzA14 : 14 ≤ zA := by linarith
  have h1z : 1 / zA ≤ 1 / 14 := one_div_le_one_div_of_le (by norm_num) hzA14
  have hX : 2 * n * (G2 + e) + n * (G4 + e) ≤ 1203 / 10000 := by
    have e1 : 2 * n * (G2 + e) + n * (G4 + e) = 2 * (n * G2) + n * G4 + 3 * (n * e) := by ring
    rw [e1]
    have : 4 / 10 / zA = 4 / 10 * (1 / zA) := by ring
    have : 9 / 10 / zA = 9 / 10 * (1 / zA) := by ring
    nlinarith
  refine ⟨by linarith, ?_⟩
  -- `n ℓ Y ≥ 0.2355`
  have hG1' : 99 / 100 ≤ 26 / 10 * n * (16143 / 10000 * ℓ) * G1 := by
    have hG10 : 0 ≤ G1 := by
      by_contra h
      push_neg at h
      have : 26 / 10 * n * (zA + 2) * G1 < 0 :=
        mul_neg_of_pos_of_neg (by positivity) h
      linarith
    have : 26 / 10 * n * (zA + 2) * G1 ≤ 26 / 10 * n * (16143 / 10000 * ℓ) * G1 := by
      have hz : zA + 2 ≤ 16143 / 10000 * ℓ := by linarith
      have := mul_le_mul_of_nonneg_left hz (show (0 : ℝ) ≤ 26 / 10 * n by positivity)
      exact mul_le_mul_of_nonneg_right this hG10
    linarith
  have hnℓG1 : 99 / 100 / (26 / 10 * (16143 / 10000)) ≤ n * ℓ * G1 := by
    rw [div_le_iff₀ (by norm_num)]
    linarith [show 26 / 10 * n * (16143 / 10000 * ℓ) * G1 = n * ℓ * G1 * (26 / 10 * (16143 / 10000)) by ring]
  have hnℓG3 : n * ℓ * G3 ≤ 1 / 3000 := by
    have h1 : n * ℓ * G3 * n = ℓ * (n ^ 2 * G3) := by ring
    have h2 : ℓ * (n ^ 2 * G3) ≤ ℓ * 1 := mul_le_mul_of_nonneg_left hG3 hℓ0.le
    have h3 : n * ℓ * G3 * n ≤ 1 / 3000 * n := by nlinarith
    exact le_of_mul_le_mul_right h3 hn0
  have hnℓe : n * ℓ * e ≤ 1 / 10 ^ 6 := by
    have h1 : n * ℓ * e * n = ℓ * (n ^ 2 * e) := by ring
    have h2 : ℓ * (n ^ 2 * e) ≤ ℓ * (1 / 10 ^ 6) := mul_le_mul_of_nonneg_left he hℓ0.le
    have h3 : n * ℓ * e * n ≤ 1 / 10 ^ 6 * n := by nlinarith
    exact le_of_mul_le_mul_right h3 hn0
  set Y := (G1 - e) - (G3 + e) with hY
  have hnℓY : 2355 / 10000 ≤ n * ℓ * Y := by
    have : n * ℓ * Y = n * ℓ * G1 - n * ℓ * G3 - 2 * (n * ℓ * e) := by rw [hY]; ring
    rw [this]
    have : (2355 : ℝ) / 10000 ≤ 99 / 100 / (26 / 10 * (16143 / 10000)) - 1 / 3000 - 2 / 10 ^ 6 := by
      norm_num
    linarith
  have hY0 : 0 ≤ Y := by
    by_contra h
    push_neg at h
    have : n * ℓ * Y < 0 := mul_neg_of_pos_of_neg (by positivity) h
    linarith
  -- assemble
  set X := 2 * n * (G2 + e) + n * (G4 + e) with hXdef
  have h2d : n * ℓ * Y / 15 ≤ 2 * d * ℓ * Y := by
    have : n / 15 ≤ 2 * d := by linarith
    have hℓY : 0 ≤ ℓ * Y := mul_nonneg hℓ0.le hY0
    calc n * ℓ * Y / 15 = n / 15 * (ℓ * Y) := by ring
      _ ≤ 2 * d * (ℓ * Y) := mul_le_mul_of_nonneg_right this hℓY
      _ = 2 * d * ℓ * Y := by ring
  have hmain : 1 / 100 ≤ 2 * d * ℓ * Y * (1 - X) := by
    have h1 : 2355 / 10000 / 15 ≤ 2 * d * ℓ * Y := by linarith
    have h2 : 8797 / 10000 ≤ 1 - X := by linarith
    have h3 : 2355 / 10000 / 15 * (8797 / 10000) ≤ 2 * d * ℓ * Y * (1 - X) :=
      mul_le_mul h1 h2 (by norm_num) (by linarith)
    have : (1 : ℝ) / 100 ≤ 2355 / 10000 / 15 * (8797 / 10000) := by norm_num
    linarith
  rw [div_le_iff₀ (by positivity)]
  calc (1 : ℝ) = 100 * (1 / 100) := by norm_num
    _ ≤ 100 * (2 * d * ℓ * Y * (1 - X)) := mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = 2 * d * Y * (1 - X) * (100 * ℓ) := by ring

/-! ### The Mills forms at the explicit levels -/

lemma w5_exp_neg_log (hN : 0 < (N : ℝ)) : Real.exp (-Real.log N) = 1 / N := by
  rw [Real.exp_neg, Real.exp_log hN, one_div]

lemma w5_G1 {n L zA : ℝ} (hn : 100 ≤ n) (hexpL : Real.exp (-L) = 1 / n) (hzAsq : zA ^ 2 = 2 * L)
    (hzA1 : 1 ≤ zA) (hzAn : 200 * zA ≤ n) :
    99 / 100 ≤ 26 / 10 * n * (zA + 2) * w5mlo (zA + 1 / n) := by
  have hN0 : 0 < n := by linarith
  obtain ⟨_, hpi2⟩ := w5_sqrt_two_pi
  set sπ := Real.sqrt (2 * Real.pi) with hsπ
  set x := zA + 1 / n with hx
  have hinv : 0 < 1 / n := by positivity
  have hx1 : 1 ≤ x := by linarith
  have hxsq : x ^ 2 / 2 = L + (zA / n + 1 / (2 * n ^ 2)) := by
    rw [hx]; field_simp; linear_combination (n ^ 2) * hzAsq
  have hsmall : zA / n + 1 / (2 * n ^ 2) ≤ 1 / 100 := by
    have h1 : zA / n ≤ 1 / 200 := by rw [div_le_iff₀ hN0]; linarith
    have h2 : 1 / (2 * n ^ 2) ≤ 1 / 200 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hE : 99 / 100 ≤ n * Real.exp (-(x ^ 2 / 2)) := by
    rw [hxsq, neg_add, Real.exp_add, hexpL]
    have := Real.add_one_le_exp (-(zA / n + 1 / (2 * n ^ 2)))
    have e : n * (1 / n * Real.exp (-(zA / n + 1 / (2 * n ^ 2)))) =
        Real.exp (-(zA / n + 1 / (2 * n ^ 2))) := by field_simp
    rw [e]; linarith
  have hR : 1 ≤ (zA + 2) * (x / (1 + x ^ 2)) := by
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    have : 1 / n ≤ 1 := by rw [div_le_one hN0]; linarith
    nlinarith
  have hkey : 99 / 100 ≤ sπ * (n * (zA + 2) * w5mlo x) := by
    have e : sπ * (n * (zA + 2) * w5mlo x) =
        (n * Real.exp (-(x ^ 2 / 2))) * ((zA + 2) * (x / (1 + x ^ 2))) := by
      unfold w5mlo; rw [← hsπ]; field_simp
    rw [e]
    have h0 : 0 ≤ n * Real.exp (-(x ^ 2 / 2)) := by positivity
    calc (99 / 100 : ℝ) = 99 / 100 * 1 := by ring
      _ ≤ (n * Real.exp (-(x ^ 2 / 2))) * ((zA + 2) * (x / (1 + x ^ 2))) :=
          mul_le_mul hE hR (by norm_num) h0
  have hm0' : 0 ≤ n * (zA + 2) * w5mlo x := by
    unfold w5mlo; have : 0 < x := by linarith
    positivity
  have h2 : sπ * (n * (zA + 2) * w5mlo x) ≤ 26 / 10 * (n * (zA + 2) * w5mlo x) :=
    mul_le_mul_of_nonneg_right (by linarith) hm0'
  have e : 26 / 10 * n * (zA + 2) * w5mlo x = 26 / 10 * (n * (zA + 2) * w5mlo x) := by ring
  rw [e]; linarith

lemma w5_G3 {n L ℓ : ℝ} (hn : 0 < n) (hexpL : Real.exp (-L) = 1 / n) (hℓsq : ℓ ^ 2 = L)
    (hℓ : 1 ≤ ℓ) : n ^ 2 * w5mup (2 * ℓ) ≤ 1 := by
  obtain ⟨hpi1, _⟩ := w5_sqrt_two_pi
  have hE : Real.exp (-((2 * ℓ) ^ 2 / 2)) = (1 / n) ^ 2 := by
    rw [show -((2 * ℓ) ^ 2 / 2) = ((2 : ℕ) : ℝ) * (-L) by rw [mul_pow, hℓsq]; push_cast; ring,
      Real.exp_nat_mul, hexpL]
  unfold w5mup
  rw [hE]
  have e : n ^ 2 * ((1 / n) ^ 2 / Real.sqrt (2 * Real.pi) / (2 * ℓ)) =
      1 / (Real.sqrt (2 * Real.pi) * (2 * ℓ)) := by field_simp
  rw [e, div_le_one (by positivity)]
  nlinarith

lemma w5_G2 {n L zA : ℝ} (hn : 0 < n) (hexpL : Real.exp (-L) = 1 / n) (hzAsq : zA ^ 2 = 2 * L)
    (hzA0 : 0 < zA) : n * zA * w5mup zA ≤ 4 / 10 := by
  obtain ⟨hpi1, _⟩ := w5_sqrt_two_pi
  unfold w5mup
  rw [show zA ^ 2 / 2 = L by rw [hzAsq]; ring, hexpL]
  have e : n * zA * (1 / n / Real.sqrt (2 * Real.pi) / zA) = 1 / Real.sqrt (2 * Real.pi) := by
    field_simp
  rw [e, div_le_iff₀ (by linarith)]
  linarith

lemma w5_G4 {n L zA m : ℝ} (hn : 0 < n) (hexpL : Real.exp (-L) = 1 / n) (hzAsq : zA ^ 2 = 2 * L)
    (hzA0 : 0 < zA) (hm0 : 0 < m) (h3m : 3 / m ≤ 1 / 100) (h6L : 6 * L / m ≤ 1 / 100) (hL : 0 ≤ L) :
    n * zA * w5mup ((1 - 3 / m) * zA) ≤ 9 / 10 := by
  obtain ⟨hpi1, _⟩ := w5_sqrt_two_pi
  set sπ := Real.sqrt (2 * Real.pi) with hsπ
  have hsπ0 : 0 < sπ := by linarith
  set y4 := (1 - 3 / m) * zA with hy4
  have h3m0 : 0 ≤ 3 / m := by positivity
  have hy4a : 9 / 10 * zA ≤ y4 := by
    rw [hy4]
    have := mul_le_mul_of_nonneg_right (show (9 : ℝ) / 10 ≤ 1 - 3 / m by linarith) hzA0.le
    linarith
  have hy4p : 0 < y4 := by linarith
  have hy4sq : L - 1 / 100 ≤ y4 ^ 2 / 2 := by
    have h1 : y4 ^ 2 = (1 - 3 / m) ^ 2 * (2 * L) := by rw [hy4, mul_pow, hzAsq]
    have h2 : 1 - 2 * (3 / m) ≤ (1 - 3 / m) ^ 2 := by nlinarith [sq_nonneg (3 / m)]
    have h4 : (1 - 2 * (3 / m)) * (2 * L) ≤ (1 - 3 / m) ^ 2 * (2 * L) :=
      mul_le_mul_of_nonneg_right h2 (by linarith)
    have h5 : (1 - 2 * (3 / m)) * (2 * L) = 2 * L - 2 * (6 * L / m) := by ring
    rw [h1]; linarith
  have hE : Real.exp (-(y4 ^ 2 / 2)) ≤ 2 / n := by
    calc Real.exp (-(y4 ^ 2 / 2)) ≤ Real.exp (-L + 1 / 100) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp (-L) * Real.exp (1 / 100) := Real.exp_add _ _
      _ ≤ 1 / n * 2 := by
          rw [hexpL]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num)]
          exact Real.exp_le_exp.2 (by have := Real.log_two_gt_d9; linarith)
      _ = 2 / n := by ring
  unfold w5mup
  rw [← hsπ]
  have e : n * zA * (Real.exp (-(y4 ^ 2 / 2)) / sπ / y4) =
      (n * Real.exp (-(y4 ^ 2 / 2))) * zA / (sπ * y4) := by field_simp
  rw [e, div_le_iff₀ (by positivity)]
  have h1 : n * Real.exp (-(y4 ^ 2 / 2)) ≤ 2 := by
    have := mul_le_mul_of_nonneg_left hE hn.le
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hn.ne'] at this
    linarith
  have h2 : (5 / 2) * (9 / 10 * zA) ≤ sπ * y4 := mul_le_mul hpi1 hy4a (by positivity) hsπ0.le
  have h3 : n * Real.exp (-(y4 ^ 2 / 2)) * zA ≤ 2 * zA := mul_le_mul_of_nonneg_right h1 hzA0.le
  linarith

/-- **The final coin inequality.** -/
theorem w5_cfinal (C : ℝ) (hC : 0 ≤ C) : ∀ᶠ N : ℕ in atTop,
    0 ≤ 1 - (2 * N * (w5mup (w5zA N) + w5err C N) +
      N * (w5mup ((1 - 3 / mX N) * w5zA N) + w5err C N)) ∧
    1 / (100 * Real.sqrt (Real.log N)) ≤
      2 * (dX N : ℝ) * ((w5mlo (w5zA N + 1 / N) - w5err C N) -
        (w5mup (2 * Real.sqrt (Real.log N)) + w5err C N)) *
      (1 - (2 * N * (w5mup (w5zA N) + w5err C N) +
        N * (w5mup ((1 - 3 / mX N) * w5zA N) + w5err C N))) := by
  filter_upwards [w5_ev_log100, w5_ev_log_sq, w5_ev_err C hC, eventually_ge_atTop 100]
    with N hL100 hLs herr hN
  set L := Real.log N with hLdef
  have hNr : (100 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set ℓ := Real.sqrt L with hℓdef
  have hℓsq : ℓ ^ 2 = L := Real.sq_sqrt (by linarith)
  have hℓ10 : 10 ≤ ℓ := (Real.le_sqrt' (by norm_num)).2 (by linarith)
  have hℓL : ℓ ≤ L := by nlinarith
  have hLN : 3000 * L ≤ N := by nlinarith
  have hℓN : 3000 * ℓ ≤ N := by linarith
  set zA := w5zA N with hzAdef
  have hzA : zA = Real.sqrt 2 * ℓ := by rw [hzAdef]; unfold w5zA; exact Real.sqrt_mul (by norm_num) _
  have hs2a : 1414 / 1000 ≤ Real.sqrt 2 := (Real.le_sqrt' (by norm_num)).2 (by norm_num)
  have hs2b : Real.sqrt 2 ≤ 14143 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hzA1 : 1414 / 1000 * ℓ ≤ zA := by rw [hzA]; exact mul_le_mul_of_nonneg_right hs2a (by linarith)
  have hzA2 : zA ≤ 14143 / 10000 * ℓ := by rw [hzA]; exact mul_le_mul_of_nonneg_right hs2b (by linarith)
  have hzA0 : 0 < zA := by linarith
  have hzAsq : zA ^ 2 = 2 * L := w5_zA_sq N
  have he0 : 0 ≤ w5err C N := by unfold w5err; positivity
  have hexpL : Real.exp (-L) = 1 / N := w5_exp_neg_log hN0
  have hd30 : (N : ℝ) / 30 ≤ dX N := by
    have : N ≤ 30 * dX N := by unfold dX; omega
    have : (N : ℝ) ≤ 30 * dX N := by exact_mod_cast this
    linarith
  have hdN : dX N ≤ N := by unfold dX; omega
  have hm : (N : ℝ) / 2 ≤ mX N := by
    unfold mX; rw [Nat.cast_sub hdN]
    have : (30 : ℝ) * dX N ≤ N + 29 := by
      have : 30 * dX N ≤ N + 29 := by unfold dX; omega
      exact_mod_cast this
    linarith
  have hm0 : 0 < mX N := by linarith
  have hG1 := w5_G1 hNr hexpL hzAsq (by linarith) (by linarith)
  have hG3 := w5_G3 hN0 hexpL hℓsq (by linarith)
  have hG2 := w5_G2 hN0 hexpL hzAsq hzA0
  have hG4 := w5_G4 hN0 hexpL hzAsq hzA0 hm0 (by rw [div_le_iff₀ hm0]; linarith)
    (by rw [div_le_iff₀ hm0]; nlinarith) (by linarith)
  have hG2' : 0 ≤ w5mup zA := by unfold w5mup; positivity
  have hG4' : 0 ≤ w5mup ((1 - 3 / mX N) * zA) := by
    unfold w5mup
    have : 0 < 1 - 3 / mX N := by
      have : 3 / mX N ≤ 1 / 100 := by rw [div_le_iff₀ hm0]; linarith
      linarith
    positivity
  exact w5_cfinal_alg (n := N) (by linarith) hℓ10 hℓN hzA1 hzA2 he0 herr hd30 hG1 hG3 hG2 hG4
    hG2' hG4'

end Census
end IIT
