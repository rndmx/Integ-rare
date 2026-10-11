/-
Census, B1, W14 work package WP5 (part 4): the numbers of Lemma D' (W5 6.6, W13-effect G1).

With `a = 2^d`, `A0 = σ √(2 ln N)` (so `6 a A0² = ln N`), the deficit threshold of `(D_A)` at `r = |M \ A|`
is `w5tr N r = a A0 (2^r (1 - r/m) - 1) - a 2^r κN/2 - (d+r+1)²/2 ≥ a A0 (2^r - 1)(1 - γ)` with
`γ = w5gam N = 2 rD/m + κN/A0 + (d+rD+1)²/(a A0) → 0` (`γ ≤ 1/(40 ln N) + 1/(40 N)`), so that the sharp
sub-Gaussian tail `exp(-6t²/n)` at `n ≤ a(2^r - 1)` is `≤ N^{-(2^r-1)(1-2γ)}`; and
`2 d Σ_{2 ≤ r ≤ rD} C(m, r) N^{-(2^r-1)(1-2γ)} ≤ 1` (the `r = 2` term is `≤ 2/N`, the others `≤ N^{-3}`).

No `sorry`.
-/
import IIT.Census.B1CntCoinFlip

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-- The fresh-part threshold of a failing `(D_A)`, `r = |M \ A|`. -/
noncomputable def w5tr (N r : ℕ) : ℝ :=
  2 ^ dX N * A0C N * (2 ^ r * (1 - (r : ℝ) / mX N) - 1) - 2 ^ dX N * 2 ^ r * kapN N / 2 -
    ((dX N + r + 1 : ℕ) : ℝ) ^ 2 / 2

/-- The relative loss `γ` of the threshold. -/
noncomputable def w5gam (N : ℕ) : ℝ :=
  2 * (rD N : ℝ) / mX N + kapN N / A0C N + ((dX N + rD N + 1 : ℕ) : ℝ) ^ 2 / (2 ^ dX N * A0C N)

/-! ### The constants -/

lemma w5_A0C_eq (N : ℕ) : A0C N = Real.sqrt (Real.log N / 6) / Real.sqrt (2 ^ dX N) := by
  unfold A0C sigC
  have ha : (0 : ℝ) < 2 ^ dX N := by positivity
  have hL := Real.log_natCast_nonneg N
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_div' _ ha.le]
  congr 1
  field_simp
  ring

lemma w5_A0C_sq (N : ℕ) : 6 * 2 ^ dX N * A0C N ^ 2 = Real.log N := by
  have hL := Real.log_natCast_nonneg N
  rw [w5_A0C_eq, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp

lemma w5_aA0_eq (N : ℕ) :
    2 ^ dX N * A0C N = Real.sqrt (2 ^ dX N) * Real.sqrt (Real.log N / 6) := by
  rw [w5_A0C_eq]
  have hs : 0 < Real.sqrt ((2 : ℝ) ^ dX N) := Real.sqrt_pos.2 (by positivity)
  have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 ^ dX N by positivity)
  calc (2 : ℝ) ^ dX N * (Real.sqrt (Real.log N / 6) / Real.sqrt (2 ^ dX N))
      = (Real.sqrt (2 ^ dX N) * Real.sqrt (2 ^ dX N)) * Real.sqrt (Real.log N / 6) /
          Real.sqrt (2 ^ dX N) := by rw [h]; ring
    _ = _ := by field_simp

lemma w5_aA0_ge (N : ℕ) (hL : 1 ≤ Real.log N) :
    Real.sqrt (2 ^ dX N) / 3 ≤ 2 ^ dX N * A0C N := by
  rw [w5_aA0_eq]
  have h1 : (1 : ℝ) / 3 ≤ Real.sqrt (Real.log N / 6) := by
    rw [show (1 : ℝ) / 3 = Real.sqrt (1 / 9) by
      rw [show (1 : ℝ) / 9 = (1 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hs := Real.sqrt_nonneg ((2 : ℝ) ^ dX N)
  nlinarith

lemma w5_A0C_pos (hL : 0 < Real.log N) : 0 < A0C N := by
  rw [w5_A0C_eq]
  exact div_pos (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_pos.2 (by positivity))

lemma w5_sqrt_le_self {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  calc Real.sqrt x ≤ Real.sqrt (x ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = x := Real.sqrt_sq (by linarith)

lemma w5_a_kapN_le (hN : 1 ≤ N) (h2d : 2 * dX N ≤ N) :
    2 ^ dX N * kapN N ≤ 42 * (N : ℝ) ^ 4 := by
  set a : ℝ := 2 ^ dX N with ha_def
  have ha : 0 < a := by positivity
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : Real.log N ≤ N := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hd : (dX N : ℝ) ≤ N := by
    have : dX N ≤ N := by omega
    exact_mod_cast this
  have ha2 : a ^ 2 ≤ 2 ^ N := by
    rw [ha_def, ← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have haN : a ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have he1 : a * Real.sqrt ((N : ℝ) / 2 ^ N) ≤ Real.sqrt N := by
    have e : a * Real.sqrt ((N : ℝ) / 2 ^ N) = Real.sqrt (a ^ 2 * ((N : ℝ) / 2 ^ N)) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ha.le]
    rw [e]
    apply Real.sqrt_le_sqrt
    rw [mul_div_assoc', div_le_iff₀ h2N]
    nlinarith
  have he2 : a * ((N : ℝ) ^ 4 / 2 ^ N) ≤ (N : ℝ) ^ 4 := by
    rw [mul_div_assoc', div_le_iff₀ h2N]
    nlinarith [pow_nonneg hN0 4]
  have hsq := w5_sqrt_le_self hNr
  have hexp : a * kapN N = 6 * Real.log N + 4 * (dX N : ℝ) ^ 2 +
      8 * (2 * (a * Real.sqrt ((N : ℝ) / 2 ^ N)) + 2 * (a * ((N : ℝ) ^ 4 / 2 ^ N))) := by
    unfold kapN kap0 epsN
    rw [← ha_def]
    field_simp
  rw [hexp]
  have h1 : (N : ℝ) ≤ (N : ℝ) ^ 4 := by
    calc (N : ℝ) = N ^ 1 := (pow_one _).symm
      _ ≤ N ^ 4 := pow_le_pow_right₀ hNr (by norm_num)
  have h2 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ hNr (by norm_num)
  have h3 : (dX N : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hd 2
  nlinarith

lemma w5_rD_le (hN : 1 ≤ N) : (rD N : ℝ) ≤ 5 * Real.log N + 13 := by
  have h1 : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have h2 : (2 : ℝ) ^ Nat.log 2 N ≤ N := by exact_mod_cast h1
  have h3 : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h2
  have hl2 := Real.log_two_gt_d9
  have hL := Real.log_natCast_nonneg N
  have h0 : (0 : ℝ) ≤ Nat.log 2 N := Nat.cast_nonneg _
  have h4 : (Nat.log 2 N : ℝ) ≤ 3 / 2 * Real.log N := by nlinarith
  unfold rD; push_cast; linarith

/-! ### Eventual facts -/

lemma w5_sqrt_two_pow (n : ℕ) : Real.sqrt ((2 : ℝ) ^ n) = Real.exp (n * Real.log 2 / 2) := by
  have e : (2 : ℝ) ^ n = Real.exp (n * Real.log 2 / 2) ^ 2 := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (n * Real.log 2 / 2) = n * Real.log 2 by
      push_cast; ring, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [e, Real.sqrt_sq (Real.exp_pos _).le]

lemma w5_ev_exp_poly : ∀ᶠ N : ℕ in atTop, 20000 * (N : ℝ) ^ 5 ≤ Real.sqrt (2 ^ dX N) := by
  have hc : (0 : ℝ) < Real.log 2 / 60 := by positivity
  filter_upwards [ev_poly_exp 5 20000 hc one_pos] with N hN
  have hd : (N : ℝ) / 30 ≤ dX N := by
    have : N ≤ 30 * dX N := by unfold dX; omega
    have : (N : ℝ) ≤ 30 * dX N := by exact_mod_cast this
    linarith
  rw [w5_sqrt_two_pow]
  have hl2 : 0 < Real.log 2 := by positivity
  have hle : Real.log 2 / 60 * N ≤ dX N * Real.log 2 / 2 := by nlinarith
  have hE := Real.exp_le_exp.2 hle
  have hpos := Real.exp_pos (Real.log 2 / 60 * N)
  have : 20000 * (N : ℝ) ^ 5 = 20000 * (N : ℝ) ^ 5 * Real.exp (-(Real.log 2 / 60 * N)) *
      Real.exp (Real.log 2 / 60 * N) := by
    rw [mul_assoc, ← Real.exp_add]; simp
  rw [this]
  calc 20000 * (N : ℝ) ^ 5 * Real.exp (-(Real.log 2 / 60 * N)) * Real.exp (Real.log 2 / 60 * N)
      ≤ 1 * Real.exp (Real.log 2 / 60 * N) := mul_le_mul_of_nonneg_right hN.le hpos.le
    _ ≤ _ := by rw [one_mul]; exact hE

lemma w5_ev_log_sq : ∀ᶠ N : ℕ in atTop, 3000 * Real.log N ^ 2 ≤ N := by
  filter_upwards [eventually_ge_atTop (48000 ^ 2)] with N hN
  have hNr : (48000 : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 := Real.log_le_rpow_div (x := (N : ℝ)) (ε := 1 / 4) hN0 (by norm_num)
  have hL := Real.log_natCast_nonneg N
  have hq : ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num
  have hs : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0
  have hs48 : 48000 ≤ Real.sqrt N := by
    rw [show (48000 : ℝ) = Real.sqrt (48000 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hNr
  have h1' : Real.log N ≤ 4 * (N : ℝ) ^ (1 / 4 : ℝ) := by
    have e : (N : ℝ) ^ (1 / 4 : ℝ) / (1 / 4) = 4 * (N : ℝ) ^ (1 / 4 : ℝ) := by ring
    rw [← e]; exact h1
  have hL2 : Real.log N ^ 2 ≤ 16 * Real.sqrt N := by
    calc Real.log N ^ 2 ≤ (4 * (N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ hL h1' 2
      _ = 16 * Real.sqrt N := by rw [mul_pow, hq]; norm_num
  nlinarith

lemma w5_nat_pow_ge (r : ℕ) (hr : 3 ≤ r) : 10 * (r + 3) + 9 ≤ 9 * 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    have : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega

/-- **The thresholds of D'** (deterministic). -/
lemma w5_thr (N r : ℕ) (hA0 : 0 < A0C N) (hmpos : 0 < mX N) (hγ0 : 0 ≤ w5gam N)
    (hγ20 : w5gam N ≤ 1 / 20) : 2 ≤ r → r ≤ rD N → 0 < w5tr N r ∧
      Real.log N * (2 ^ r - 1) * (1 - 2 * w5gam N) ≤
        6 * w5tr N r ^ 2 / (2 ^ dX N * (2 ^ r - 1)) := by
  set L := Real.log N with hLdef
  set a : ℝ := 2 ^ dX N with ha_def
  have ha : 0 < a := by positivity
  have hκN := w5_kapN_nonneg N
  have hA0sq := w5_A0C_sq N
  rw [← ha_def, ← hLdef] at hA0sq
  intro hr2 hrr
  set ρ : ℝ := 2 ^ r with hρ
  have hρ4 : 4 ≤ ρ := by
    rw [hρ]; calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr2
  have hrr' : (r : ℝ) ≤ rD N := by exact_mod_cast hrr
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  set P := a * A0C N with hPdef
  have hPpos : 0 < P := mul_pos ha hA0
  set Q := a * kapN N with hQdef
  have hQ0 : 0 ≤ Q := mul_nonneg ha.le hκN
  set R := ((dX N + rD N + 1 : ℕ) : ℝ) ^ 2 with hRdef
  set R' := ((dX N + r + 1 : ℕ) : ℝ) ^ 2 with hR'def
  have hRR : R' ≤ R := by
    rw [hRdef, hR'def]
    exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) 2
  have hγP : w5gam N * P = 2 * rD N / mX N * P + Q + R := by
    unfold w5gam; rw [← ha_def, hPdef, hQdef, ← hRdef]
    field_simp
  have htr : w5tr N r = P * (ρ * (1 - r / mX N) - 1) - ρ * Q / 2 - R' / 2 := by
    unfold w5tr; rw [← ha_def, ← hρ, hPdef, hQdef, hR'def]; ring
  have hX : P * (ρ - 1) * (1 - w5gam N) ≤ w5tr N r := by
    rw [htr]
    have e1 : P * ρ * (r / mX N) ≤ (ρ - 1) * (2 * rD N / mX N * P) := by
      have h1 : ρ * r ≤ (2 * (ρ - 1)) * r := mul_le_mul_of_nonneg_right (by linarith) hr0
      have h2 : (2 * (ρ - 1)) * r ≤ (2 * (ρ - 1)) * rD N :=
        mul_le_mul_of_nonneg_left hrr' (by linarith)
      have : ρ * r ≤ (ρ - 1) * (2 * rD N) := by linarith
      have hPm : 0 ≤ P / mX N := div_nonneg hPpos.le hmpos.le
      calc P * ρ * (r / mX N) = (ρ * r) * (P / mX N) := by ring
        _ ≤ ((ρ - 1) * (2 * rD N)) * (P / mX N) := mul_le_mul_of_nonneg_right this hPm
        _ = _ := by ring
    have e2 : ρ * Q / 2 ≤ (ρ - 1) * Q := by
      have := mul_nonneg (show (0 : ℝ) ≤ ρ / 2 - 1 by linarith) hQ0
      linarith
    have hR0 : 0 ≤ R := by rw [hRdef]; positivity
    have e3 : R' / 2 ≤ (ρ - 1) * R := by
      have := mul_nonneg (show (0 : ℝ) ≤ ρ - 1 - 1 / 2 by linarith) hR0
      linarith
    have e4 : (ρ - 1) * (w5gam N * P) = (ρ - 1) * (2 * rD N / mX N * P) + (ρ - 1) * Q +
        (ρ - 1) * R := by rw [hγP]; ring
    have k1 : P * (ρ - 1) * (1 - w5gam N) = P * (ρ - 1) - (ρ - 1) * (w5gam N * P) := by ring
    have k2 : P * (ρ * (1 - r / mX N) - 1) = P * ρ - P * ρ * (r / mX N) - P := by ring
    rw [k1, k2]
    linarith
  have hXpos : 0 < P * (ρ - 1) * (1 - w5gam N) := by
    have : 0 < 1 - w5gam N := by linarith
    have : 0 < ρ - 1 := by linarith
    positivity
  refine ⟨hXpos.trans_le hX, ?_⟩
  rw [le_div_iff₀ (by have : 0 < ρ - 1 := by linarith
                      positivity)]
  have hsq : (P * (ρ - 1) * (1 - w5gam N)) ^ 2 ≤ w5tr N r ^ 2 :=
    pow_le_pow_left₀ hXpos.le hX 2
  have hid : 6 * (P * (ρ - 1) * (1 - w5gam N)) ^ 2 =
      a * L * (ρ - 1) ^ 2 * (1 - w5gam N) ^ 2 := by
    rw [hPdef, ← hA0sq]; ring
  have hρ1 : 0 ≤ (ρ - 1) ^ 2 := sq_nonneg _
  have hL0 : 0 ≤ L := Real.log_natCast_nonneg N
  have hmono : a * L * (ρ - 1) ^ 2 * (1 - 2 * w5gam N) ≤
      a * L * (ρ - 1) ^ 2 * (1 - w5gam N) ^ 2 := by
    have haL : 0 ≤ a * L * (ρ - 1) ^ 2 := by positivity
    have : 1 - 2 * w5gam N ≤ (1 - w5gam N) ^ 2 := by nlinarith [sq_nonneg (w5gam N)]
    exact mul_le_mul_of_nonneg_left this haL
  calc L * (ρ - 1) * (1 - 2 * w5gam N) * (a * (ρ - 1))
      = a * L * (ρ - 1) ^ 2 * (1 - 2 * w5gam N) := by ring
    _ ≤ a * L * (ρ - 1) ^ 2 * (1 - w5gam N) ^ 2 := hmono
    _ = 6 * (P * (ρ - 1) * (1 - w5gam N)) ^ 2 := hid.symm
    _ ≤ 6 * w5tr N r ^ 2 := by linarith

/-- **The sum over `r` in D'** (deterministic). -/
lemma w5_rsum (N : ℕ) (hN1 : 1 ≤ N) (hγ0 : 0 ≤ w5gam N) (hγ20 : w5gam N ≤ 1 / 20)
    (hγL : w5gam N * Real.log N ≤ 1 / 20) (hd20 : (dX N : ℝ) ≤ N / 20) (hrDN : (rD N : ℝ) ≤ N) :
    2 * (dX N : ℝ) * ∑ r ∈ Icc 2 (rD N), ((N - dX N).choose r : ℝ) *
      Real.exp (-(Real.log N * (2 ^ r - 1) * (1 - 2 * w5gam N))) ≤ 1 := by
  set L := Real.log N with hLdef
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hrD2 : 2 ≤ rD N := by unfold rD; omega
  have hNinv : Real.exp (-L) = 1 / N := by
    rw [Real.exp_neg, hLdef, Real.exp_log hN0, one_div]
  have hterm : ∀ r ∈ Icc 2 (rD N), ((N - dX N).choose r : ℝ) *
      Real.exp (-(L * (2 ^ r - 1) * (1 - 2 * w5gam N))) ≤
        (if r = 2 then (2 : ℝ) / N else 0) + 1 / (N : ℝ) ^ 3 := by
    intro r hr
    rw [mem_Icc] at hr
    have hC : ((N - dX N).choose r : ℝ) ≤ Real.exp (r * L) := by
      have h1 : (N - dX N).choose r ≤ N ^ r :=
        (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) r)
      have h2 : ((N - dX N).choose r : ℝ) ≤ (N : ℝ) ^ r := by exact_mod_cast h1
      rw [Real.exp_nat_mul, hLdef, Real.exp_log hN0]; exact h2
    have hE0 := Real.exp_pos (-(L * (2 ^ r - 1) * (1 - 2 * w5gam N)))
    have hb : ((N - dX N).choose r : ℝ) * Real.exp (-(L * (2 ^ r - 1) * (1 - 2 * w5gam N))) ≤
        Real.exp (r * L - L * (2 ^ r - 1) * (1 - 2 * w5gam N)) := by
      rw [show (r : ℝ) * L - L * (2 ^ r - 1) * (1 - 2 * w5gam N) =
        r * L + -(L * (2 ^ r - 1) * (1 - 2 * w5gam N)) by ring, Real.exp_add]
      exact mul_le_mul_of_nonneg_right hC hE0.le
    have hN3 : (0 : ℝ) < 1 / (N : ℝ) ^ 3 := by positivity
    by_cases h2 : r = 2
    · subst h2
      rw [if_pos rfl]
      refine hb.trans ?_
      have hexp : ((2 : ℕ) : ℝ) * L - L * (2 ^ 2 - 1) * (1 - 2 * w5gam N) ≤ -L + 3 / 10 := by
        push_cast; nlinarith
      have h03 : Real.exp (3 / 10) ≤ 2 := by
        rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num)]
        exact Real.exp_le_exp.2 (by have := Real.log_two_gt_d9; linarith)
      calc Real.exp (((2 : ℕ) : ℝ) * L - L * (2 ^ 2 - 1) * (1 - 2 * w5gam N))
          ≤ Real.exp (-L + 3 / 10) := Real.exp_le_exp.2 hexp
        _ = Real.exp (-L) * Real.exp (3 / 10) := Real.exp_add _ _
        _ ≤ 1 / N * 2 := by
            rw [hNinv]; exact mul_le_mul_of_nonneg_left h03 (by positivity)
        _ ≤ 2 / N + 1 / (N : ℝ) ^ 3 := by rw [div_mul_eq_mul_div, one_mul]; linarith
    · rw [if_neg h2, zero_add]
      refine hb.trans ?_
      have hr3 : 3 ≤ r := by omega
      have hnat := w5_nat_pow_ge r hr3
      have hreal : (10 : ℝ) * (r + 3) + 9 ≤ 9 * 2 ^ r := by exact_mod_cast hnat
      have hk : (r : ℝ) + 3 ≤ (2 ^ r - 1) * (1 - 2 * w5gam N) := by nlinarith
      have hL0 : 0 ≤ L := Real.log_natCast_nonneg N
      have hm := mul_le_mul_of_nonneg_left hk hL0
      have hexp : (r : ℝ) * L - L * (2 ^ r - 1) * (1 - 2 * w5gam N) ≤ -(3 * L) := by
        have e : L * ((2 ^ r - 1) * (1 - 2 * w5gam N)) = L * (2 ^ r - 1) * (1 - 2 * w5gam N) := by
          ring
        rw [e] at hm
        linarith
      calc Real.exp ((r : ℝ) * L - L * (2 ^ r - 1) * (1 - 2 * w5gam N))
          ≤ Real.exp (-(3 * L)) := Real.exp_le_exp.2 hexp
        _ = 1 / (N : ℝ) ^ 3 := by
            rw [show -(3 * L) = ((3 : ℕ) : ℝ) * (-L) by push_cast; ring, Real.exp_nat_mul, hNinv]
            ring
  have hsum := sum_le_sum hterm
  rw [sum_add_distrib, sum_ite_eq' (Icc 2 (rD N)) 2 (fun _ => 2 / (N : ℝ)), sum_const,
    nsmul_eq_mul, Nat.card_Icc] at hsum
  have h2mem : 2 ∈ Icc 2 (rD N) := mem_Icc.2 ⟨le_rfl, hrD2⟩
  rw [if_pos h2mem] at hsum
  have hcard : ((rD N + 1 - 2 : ℕ) : ℝ) ≤ N := by
    have : rD N + 1 - 2 ≤ rD N := by omega
    have : ((rD N + 1 - 2 : ℕ) : ℝ) ≤ rD N := by exact_mod_cast this
    linarith
  have hd20 : (dX N : ℝ) ≤ N / 20 := by linarith
  have hd0 : (0 : ℝ) ≤ dX N := Nat.cast_nonneg _
  have hfin : 2 * (dX N : ℝ) * (2 / N + ((rD N + 1 - 2 : ℕ) : ℝ) * (1 / (N : ℝ) ^ 3)) ≤ 1 := by
    have e1 : 2 * (dX N : ℝ) * (2 / N) ≤ 1 / 5 := by
      rw [mul_div_assoc', div_le_iff₀ hN0]; nlinarith
    have e2 : ((rD N + 1 - 2 : ℕ) : ℝ) * (1 / (N : ℝ) ^ 3) ≤ 1 / (N : ℝ) ^ 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      nlinarith [pow_pos hN0 2]
    have e3 : 2 * (dX N : ℝ) * (1 / (N : ℝ) ^ 2) ≤ 1 / 5 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
    have e4 : 2 * (dX N : ℝ) * (((rD N + 1 - 2 : ℕ) : ℝ) * (1 / (N : ℝ) ^ 3)) ≤
        2 * (dX N : ℝ) * (1 / (N : ℝ) ^ 2) := mul_le_mul_of_nonneg_left e2 (by positivity)
    nlinarith
  calc 2 * (dX N : ℝ) * ∑ r ∈ Icc 2 (rD N), ((N - dX N).choose r : ℝ) *
        Real.exp (-(L * (2 ^ r - 1) * (1 - 2 * w5gam N)))
      ≤ 2 * (dX N : ℝ) * (2 / N + ((rD N + 1 - 2 : ℕ) : ℝ) * (1 / (N : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 1 := hfin


/-- **The numbers of D'.** -/
theorem w5_dnum : ∀ᶠ N : ℕ in atTop,
    0 < A0C N ∧ 1 ≤ Real.log N ∧ 4 * (rD N : ℝ) ≤ mX N ∧ 3 * (dX N + rD N) + 19 ≤ N ∧
    2 ≤ dX N ∧ dX N ≤ N ∧ 0 ≤ w5gam N ∧ w5gam N ≤ 1 / 20 ∧
    (∀ r : ℕ, 2 ≤ r → r ≤ rD N → 0 < w5tr N r ∧
      Real.log N * (2 ^ r - 1) * (1 - 2 * w5gam N) ≤
        6 * w5tr N r ^ 2 / (2 ^ dX N * (2 ^ r - 1))) ∧
    2 * (dX N : ℝ) * ∑ r ∈ Icc 2 (rD N), ((N - dX N).choose r : ℝ) *
      Real.exp (-(Real.log N * (2 ^ r - 1) * (1 - 2 * w5gam N))) ≤ 1 := by
  filter_upwards [w5_ev_exp_poly, w5_ev_log_sq, w5_ev_sizes, eventually_ge_atTop (10 ^ 10)]
    with N hP hLs hsz hN
  obtain ⟨hd2, hD19, hdN, hm8⟩ := hsz
  have hNr : (10 : ℝ) ^ 10 ≤ N := by exact_mod_cast hN
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by linarith
  set L := Real.log N with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hN0]
    have := Real.exp_one_lt_d9
    linarith
  have hLN : L ≤ N := (Real.log_le_sub_one_of_pos hN0).trans (by linarith)
  have hL3000 : L ≤ (N : ℝ) / 3000 := by nlinarith
  have hrD := w5_rD_le hN1
  rw [← hLdef] at hrD
  have hrDN : (rD N : ℝ) ≤ (N : ℝ) / 500 := by linarith
  -- sizes
  have hdR : (30 : ℝ) * dX N ≤ N + 29 := by
    have : 30 * dX N ≤ N + 29 := by unfold dX; omega
    exact_mod_cast this
  have hm : mX N = (N : ℝ) - dX N := by unfold mX; rw [Nat.cast_sub hdN]
  have hmN : (N : ℝ) / 2 ≤ mX N := by rw [hm]; linarith
  have hmpos : 0 < mX N := by linarith
  have h2d : 2 * dX N ≤ N := by unfold dX; omega
  have h319 : 3 * (dX N + rD N) + 19 ≤ N := by
    have : (3 * (dX N + rD N) + 19 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have h4rD : 4 * (rD N : ℝ) ≤ mX N := by linarith
  -- the scale
  set a : ℝ := 2 ^ dX N with ha_def
  have ha : 0 < a := by positivity
  set sa := Real.sqrt a with hsa_def
  have hsapos : 0 < sa := Real.sqrt_pos.2 ha
  have hA0 := w5_A0C_pos (N := N) (by linarith)
  have haA0 := w5_aA0_ge N hL1
  rw [← ha_def, ← hsa_def] at haA0
  have haκ := w5_a_kapN_le hN1 h2d
  rw [← ha_def] at haκ
  have hκN := w5_kapN_nonneg N
  have hA0sq := w5_A0C_sq N
  rw [← ha_def, ← hLdef] at hA0sq
  -- γ is small
  have hP' : 83 * (N : ℝ) ^ 4 ≤ sa / (240 * N) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [pow_nonneg hN0.le 4]
  have hκA : kapN N / A0C N ≤ 1 / (80 * N) := by
    rw [div_le_iff₀ hA0]
    have h1 : a * kapN N ≤ a * (1 / (80 * N) * A0C N) := by
      have : a * (1 / (80 * N) * A0C N) = a * A0C N / (80 * N) := by ring
      rw [this, le_div_iff₀ (by positivity)]
      have h4 : (N : ℝ) ^ 4 ≥ 0 := by positivity
      have : 42 * (N : ℝ) ^ 4 * (80 * N) ≤ sa / 3 := by
        have := hP'
        rw [le_div_iff₀ (by positivity)] at this
        nlinarith
      nlinarith
    exact le_of_mul_le_mul_left h1 ha
  have hdr : ((dX N + rD N + 1 : ℕ) : ℝ) ≤ N := by push_cast; linarith
  have hRA : ((dX N + rD N + 1 : ℕ) : ℝ) ^ 2 / (a * A0C N) ≤ 1 / (80 * N) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have h1 : ((dX N + rD N + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 4 := by
      have : ((dX N + rD N + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hdr 2
      exact this.trans (pow_le_pow_right₀ (by linarith) (by norm_num))
    have : 83 * (N : ℝ) ^ 4 * (240 * N) ≤ sa := by
      have := hP'; rw [le_div_iff₀ (by positivity)] at this; exact this
    nlinarith [pow_nonneg hN0.le 4]
  have hrm : 2 * (rD N : ℝ) / mX N ≤ 1 / (40 * L) := by
    rw [div_le_div_iff₀ hmpos (by positivity)]
    nlinarith
  have hγ0 : 0 ≤ w5gam N := by unfold w5gam; positivity
  have hγ : w5gam N ≤ 1 / (40 * L) + 1 / (40 * N) := by
    unfold w5gam; rw [← ha_def]
    have : 1 / (80 * (N : ℝ)) + 1 / (80 * N) = 1 / (40 * N) := by field_simp; ring
    linarith
  have hγL : w5gam N * L ≤ 1 / 20 := by
    have h1 : 1 / (40 * L) * L = 1 / 40 := by field_simp
    have h2 : 1 / (40 * (N : ℝ)) * L ≤ 1 / 40 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith
    have h3 := mul_le_mul_of_nonneg_right hγ (by linarith : (0 : ℝ) ≤ L)
    rw [add_mul] at h3
    linarith
  have hγ20 : w5gam N ≤ 1 / 20 :=
    (le_mul_of_one_le_right hγ0 hL1).trans hγL
  refine ⟨hA0, hL1, h4rD, h319, hd2, hdN, hγ0, hγ20, fun r => w5_thr N r hA0 hmpos hγ0 hγ20, ?_⟩
  exact w5_rsum N hN1 hγ0 hγ20 hγL (by linarith) (by linarith)
end Census
end IIT
