/-
Census, B1, W14 work package WP3 (effect side), part 3: the numerical facts about the constants
`σ = sigC`, `ε_N = epsN`, `κ_N = kapN`, `A_0 = A0C`, `x_2 = x2C`, `d = dX`, `r_D = rD` used by the
deterministic effect-side lemmas, collected in the structure `EffC N` (eventually true).
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §8.  No `sorry`.
-/
import IIT.Census.B1CntBasics

namespace IIT
namespace Census

/-! Helpers live in `IIT.Census.WP3` (avoids name clashes with the other work packages);
the blueprint names are re-exported to `IIT.Census` by `alias` at the end of the file. -/
namespace WP3

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### Identities -/

lemma sigC_sq (N : ℕ) : sigC N ^ 2 = 1 / (12 * 2 ^ dX N) := by
  unfold sigC; rw [Real.sq_sqrt (by positivity)]

lemma sigC_pos (N : ℕ) : 0 < sigC N := Real.sqrt_pos.2 (by positivity)

lemma inv_two_pow_dX (N : ℕ) : 1 / (2 : ℝ) ^ dX N = 12 * sigC N ^ 2 := by
  rw [sigC_sq]; field_simp

lemma epsN_nonneg (N : ℕ) : 0 ≤ epsN N := by unfold epsN; positivity

lemma kap0_eq (N : ℕ) : kap0 N = 12 * (dX N : ℝ) ^ 2 * sigC N ^ 2 := by
  unfold kap0; rw [div_eq_mul_one_div, inv_two_pow_dX]; ring

lemma kapN_eq (N : ℕ) : kapN N =
    72 * Real.log N * sigC N ^ 2 + 48 * (dX N : ℝ) ^ 2 * sigC N ^ 2 + 8 * epsN N := by
  unfold kapN; rw [kap0_eq, div_eq_mul_one_div, inv_two_pow_dX]; ring

lemma x2C_sq {N : ℕ} (hL : 0 ≤ Real.log N) : x2C N ^ 2 = 6 * Real.log N * sigC N ^ 2 := by
  unfold x2C; rw [mul_pow, Real.sq_sqrt (by positivity)]; ring

lemma x2C_nonneg (N : ℕ) : 0 ≤ x2C N := by unfold x2C; exact mul_nonneg (sigC_pos N).le (Real.sqrt_nonneg _)

lemma A0C_ge {N : ℕ} (hL : 1 ≤ Real.log N) : sigC N ≤ A0C N := by
  unfold A0C
  have h1 : 1 ≤ Real.sqrt (2 * Real.log N) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  nlinarith [sigC_pos N]

lemma kapN_nonneg {N : ℕ} (_hL : 0 ≤ Real.log N) : 0 ≤ kapN N := by
  rw [kapN_eq]; have := epsN_nonneg N; positivity

lemma rD_pow (N : ℕ) (hN : 1 ≤ N) : 1024 * (N + 1) ^ 3 ≤ 2 ^ rD N := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  have h' : N + 1 ≤ 2 * 2 ^ Nat.log 2 N := by rw [pow_succ] at h; omega
  unfold rD
  rw [pow_add, pow_mul]
  have h3 : (N + 1) ^ 3 ≤ (2 * 2 ^ Nat.log 2 N) ^ 3 := Nat.pow_le_pow_left h' 3
  rw [mul_pow] at h3
  have e1 : (2 ^ Nat.log 2 N) ^ 3 = 2 ^ (3 * Nat.log 2 N) := by rw [← pow_mul, mul_comm]
  have e2 : ((2 : ℕ) ^ 3) ^ Nat.log 2 N = 2 ^ (3 * Nat.log 2 N) := by rw [← pow_mul]
  calc 1024 * (N + 1) ^ 3 ≤ 1024 * (2 ^ 3 * (2 ^ Nat.log 2 N) ^ 3) := Nat.mul_le_mul_left _ h3
    _ = (2 ^ 3) ^ Nat.log 2 N * 2 ^ 13 := by rw [e1, e2]; ring

/-! ### Asymptotics in `d` -/

lemma tendsto_dX : Tendsto dX atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨30 * b, fun a ha => by unfold dX; omega⟩

lemma dX_le (N : ℕ) : N ≤ 30 * dX N := by unfold dX; omega

lemma dX_ge (N : ℕ) : 30 * dX N ≤ N + 29 := by unfold dX; omega

lemma ev_d_lt {p : ℕ} {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (C : ℝ) :
    ∀ᶠ N in atTop, C * ((dX N : ℕ) : ℝ) ^ p * r ^ dX N < 1 :=
  tendsto_dX.eventually (ev_poly_geom p h0 h1 C one_pos)

lemma half_pow_mul_two_pow (a d e : ℕ) :
    (((1 : ℝ) / 2) ^ a) ^ d * 2 ^ (a * d + e) = 2 ^ e := by
  rw [← pow_mul, one_div_pow, pow_add]; field_simp

lemma two_pow_N_ge (N : ℕ) : (2 : ℝ) ^ (30 * dX N) ≤ 2 ^ 29 * 2 ^ N := by
  rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by have := dX_ge N; omega)

/-- `log 3 > 1`. -/
lemma one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9; linarith

lemma log_two_le_add (L : ℕ) (hL : 10 ≤ L) : 60 * L + 420 ≤ 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    have : 60 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
    omega

/-! ### The bundle -/

/-- The numerical facts used by the deterministic effect side. -/
structure EffC (N : ℕ) : Prop where
  hN : 90000 ≤ N
  hD0 : D0C N ≤ dX N
  hL1 : 1 ≤ Real.log N
  hLd : 100 * Real.log N ≤ (dX N : ℝ) ^ 2
  hεσ : epsN N ≤ sigC N ^ 2
  hσ : (N : ℝ) ^ 3 * sigC N ≤ 1 / 100

theorem ev_effC : ∀ᶠ N in atTop, EffC N := by
  filter_upwards [eventually_ge_atTop 90000,
    ev_d_lt (p := 6) (r := 1 / 2) (by norm_num) (by norm_num) (30 ^ 6 * 10 ^ 4 / 12),
    ev_d_lt (p := 4) (r := (1 / 2) ^ 29) (by positivity) (by norm_num) (48 * 30 ^ 4 * 2 ^ 29 * 24),
    ev_d_lt (p := 1) (r := (1 / 2) ^ 28) (by positivity) (by norm_num) (2304 * 30 * 2 ^ 29 * 24)]
    with N hN h6 h4 h1
  have hd := dX_le N
  have hd' := dX_ge N
  set d := dX N with hddef
  have hdR : (N : ℝ) ≤ 30 * d := by exact_mod_cast hd
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hσ2 := sigC_sq N
  rw [← hddef] at hσ2
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  have hpow : ∀ k : ℕ, ((1 : ℝ) / 2) ^ k = 1 / 2 ^ k := fun k => by rw [one_div_pow]
  refine ⟨hN, ?_, ?_, ?_, ?_, ?_⟩
  · -- `D0C ≤ d`
    unfold D0C
    have hL10 : 10 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by omega)
    have h2L : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
    have := log_two_le_add _ hL10
    omega
  · have h3 : Real.log 3 ≤ Real.log N :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (show 3 ≤ N by omega))
    linarith [one_lt_log_three]
  · have hlog : Real.log N ≤ N := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    have hd3000 : (3000 : ℝ) ≤ d := by
      have : 3000 ≤ d := by omega
      exact_mod_cast this
    nlinarith
  · -- `ε ≤ σ²`
    rw [hσ2]
    unfold epsN
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    have hpN := two_pow_N_ge N
    rw [← hddef] at hpN
    have hd1 : 1 ≤ d := by omega
    -- second term
    have ht2 : 2 * (N : ℝ) ^ 4 / 2 ^ N ≤ 1 / (24 * 2 ^ d) := by
      rw [div_le_div_iff₀ h2N (by positivity)]
      have hN4 : (N : ℝ) ^ 4 ≤ (30 * d) ^ 4 := pow_le_pow_left₀ hN0 hdR 4
      have e : (((1 : ℝ) / 2) ^ 29) ^ d * 2 ^ (30 * d) = 2 ^ d := by
        rw [show 30 * d = 29 * d + d by ring]; exact half_pow_mul_two_pow 29 d d
      have hpos : (0 : ℝ) < 2 ^ (30 * d) := by positivity
      have hP : 48 * 30 ^ 4 * 2 ^ 29 * 24 * (d : ℝ) ^ 4 * 2 ^ d < 2 ^ (30 * d) := by
        have := mul_lt_mul_of_pos_right h4 hpos
        rwa [mul_assoc (48 * 30 ^ 4 * 2 ^ 29 * 24 * (d : ℝ) ^ 4), e, one_mul] at this
      calc 2 * (N : ℝ) ^ 4 * (24 * 2 ^ d) = 48 * ((N : ℝ) ^ 4 * 2 ^ d) := by ring
        _ ≤ 48 * ((30 * (d : ℝ)) ^ 4 * 2 ^ d) := by gcongr
        _ = (48 * 30 ^ 4 * 2 ^ 29 * 24 * (d : ℝ) ^ 4 * 2 ^ d) / (2 ^ 29 * 24) := by ring
        _ ≤ 2 ^ (30 * d) / (2 ^ 29 * 24) := by gcongr
        _ ≤ (2 ^ 29 * 2 ^ N) / (2 ^ 29 * 24) := by gcongr
        _ = 2 ^ N / 24 := by rw [mul_div_mul_left _ _ (by positivity)]
        _ ≤ 1 * 2 ^ N := by rw [one_mul]; exact div_le_self h2N.le (by norm_num)
    -- first term
    have ht1 : 2 * Real.sqrt ((N : ℝ) / 2 ^ N) ≤ 1 / (24 * 2 ^ d) := by
      have hy : (0 : ℝ) ≤ 1 / (48 * 2 ^ d) := by positivity
      have hs : Real.sqrt ((N : ℝ) / 2 ^ N) ≤ 1 / (48 * 2 ^ d) := by
        refine Real.sqrt_le_iff.2 ⟨hy, ?_⟩
        rw [div_pow, one_pow, mul_pow, div_le_div_iff₀ h2N (by positivity)]
        have e : (((1 : ℝ) / 2) ^ 28) ^ d * 2 ^ (30 * d) = 2 ^ (2 * d) := by
          rw [show 30 * d = 28 * d + 2 * d by ring]; exact half_pow_mul_two_pow 28 d (2 * d)
        have hpos : (0 : ℝ) < 2 ^ (30 * d) := by positivity
        have hP : 2304 * 30 * 2 ^ 29 * 24 * (d : ℝ) ^ 1 * 2 ^ (2 * d) < 2 ^ (30 * d) := by
          have := mul_lt_mul_of_pos_right h1 hpos
          rwa [mul_assoc (2304 * 30 * 2 ^ 29 * 24 * (d : ℝ) ^ 1), e, one_mul] at this
        have e2 : ((2 : ℝ) ^ d) ^ 2 = 2 ^ (2 * d) := by rw [← pow_mul, mul_comm]
        calc (N : ℝ) * (48 ^ 2 * ((2 : ℝ) ^ d) ^ 2) = 2304 * ((N : ℝ) * 2 ^ (2 * d)) := by
              rw [e2]; ring
          _ ≤ 2304 * ((30 * (d : ℝ)) * 2 ^ (2 * d)) := by gcongr
          _ = (2304 * 30 * 2 ^ 29 * 24 * (d : ℝ) ^ 1 * 2 ^ (2 * d)) / (2 ^ 29 * 24) := by ring
          _ ≤ 2 ^ (30 * d) / (2 ^ 29 * 24) := by gcongr
          _ ≤ (2 ^ 29 * 2 ^ N) / (2 ^ 29 * 24) := by gcongr
          _ = 2 ^ N / 24 := by rw [mul_div_mul_left _ _ (by positivity)]
          _ ≤ 1 * 2 ^ N := by rw [one_mul]; exact div_le_self h2N.le (by norm_num)
      have e3 : 2 * (1 / (48 * (2 : ℝ) ^ d)) = 1 / (24 * 2 ^ d) := by field_simp; ring
      linarith
    have : (1 : ℝ) / (24 * 2 ^ d) + 1 / (24 * 2 ^ d) = 1 / (12 * 2 ^ d) := by
      field_simp; ring
    linarith
  · -- `N³ σ ≤ 1/100`
    have hσ0 := (sigC_pos N).le
    have hsq : ((N : ℝ) ^ 3 * sigC N) ^ 2 ≤ (1 / 100) ^ 2 := by
      rw [mul_pow, hσ2, ← pow_mul]
      have hN6 : (N : ℝ) ^ (3 * 2) ≤ (30 * d) ^ 6 := pow_le_pow_left₀ hN0 hdR 6
      calc (N : ℝ) ^ (3 * 2) * (1 / (12 * 2 ^ d)) ≤ (30 * (d : ℝ)) ^ 6 * (1 / (12 * 2 ^ d)) := by
            gcongr
        _ = (30 ^ 6 * 10 ^ 4 / 12 * (d : ℝ) ^ 6 * (1 / 2) ^ d) / 10 ^ 4 := by
            rw [one_div_pow]; field_simp
        _ ≤ 1 / 10 ^ 4 := by gcongr
        _ = (1 / 100) ^ 2 := by norm_num
    have hx0 : 0 ≤ (N : ℝ) ^ 3 * sigC N := by positivity
    nlinarith

end WP3


end Census
end IIT

#print axioms IIT.Census.WP3.ev_effC
#print axioms IIT.Census.WP3.rD_pow
