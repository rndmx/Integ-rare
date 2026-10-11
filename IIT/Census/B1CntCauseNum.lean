/-
Census, B1, W14 work package WP2 (cause side), part 6: the eventual numeric facts used by the
deterministic cause-side lemmas (all `∀ᶠ N in atTop`).  Method: every quantity is an exponential
`exp(α N)` up to a polynomial factor, and polynomials are absorbed by `log N ≤ c N`.
No `sorry`.
-/
import IIT.Census.B1CntCauseGen

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

/-! ### Tools -/

lemma cs_two_pow (n : ℕ) : (2 : ℝ) ^ n = Real.exp (n * Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- Polynomials are eventually below every exponential. -/
lemma cs_ev_poly_lt_exp (C : ℝ) (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, C * ((N : ℝ) + 1) ^ k < Real.exp (c * N) := by
  have hc' : 0 < c / (4 * (k + 1)) := by positivity
  have hC : ∀ᶠ N : ℕ in atTop, C < Real.exp (c / 2 * N) := by
    have h := (Real.tendsto_exp_atTop.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by positivity : 0 < c / 2)))
    exact h.eventually (eventually_gt_atTop C)
  have hL2 : ∀ᶠ N : ℕ in atTop, Real.log 2 ≤ (c / (4 * (k + 1))) * N :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc').eventually
      (eventually_ge_atTop (Real.log 2))
  filter_upwards [cs_ev_log_le hc', hC, eventually_ge_atTop 1, hL2] with N hlog hCN hN1 hl2
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog1 : Real.log ((N : ℝ) + 1) ≤ Real.log N + Real.log 2 := by
    rw [← Real.log_mul hN0.ne' (by norm_num)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hpow : ((N : ℝ) + 1) ^ k ≤ Real.exp (c / 2 * N) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < ((N : ℝ) + 1) ^ k), Real.log_pow]
    refine Real.exp_le_exp.2 ?_
    have hk : (k : ℝ) * Real.log ((N : ℝ) + 1) ≤ k * (2 * (c / (4 * (k + 1))) * N) := by
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg k)
      linarith
    have : (k : ℝ) * (2 * (c / (4 * (k + 1))) * N) ≤ c / 2 * N := by
      rw [show (k : ℝ) * (2 * (c / (4 * (k + 1))) * N) = (k / (k + 1)) * (c / 2 * N) by
        field_simp; ring]
      have hkk : (k : ℝ) / (k + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have : 0 ≤ c / 2 * N := by positivity
      nlinarith
    linarith
  rcases le_or_gt C 0 with hC0 | hC0
  · calc C * ((N : ℝ) + 1) ^ k ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC0 (by positivity)
      _ < Real.exp (c * N) := Real.exp_pos _
  · calc C * ((N : ℝ) + 1) ^ k ≤ C * Real.exp (c / 2 * N) := mul_le_mul_of_nonneg_left hpow hC0.le
      _ < Real.exp (c / 2 * N) * Real.exp (c / 2 * N) :=
          mul_lt_mul_of_pos_right hCN (Real.exp_pos _)
      _ = Real.exp (c * N) := by rw [← Real.exp_add]; ring_nf

variable {N : ℕ}

/-! ### Elementary eventual facts -/

lemma cs_exp_neg_le_inv {x B : ℝ} (hB : 0 < B) (h : B ≤ x + 1) : Real.exp (-x) ≤ 1 / B := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le hB (h.trans (Real.add_one_le_exp x))

lemma cs_ev_slT : ∀ᶠ N : ℕ in atTop, slT N ≤ N / 1000 := by
  filter_upwards [cs_ev_log_le (c := 1 / 4000) (by norm_num), eventually_ge_atTop 40000] with N hl hN
  have : (40000 : ℝ) ≤ N := by exact_mod_cast hN
  unfold slT; linarith

lemma cs_ev_a : ∀ᶠ N : ℕ in atTop, Real.exp (-((N : ℝ) / 200)) ≤ 1 / 2000 := by
  filter_upwards [eventually_ge_atTop 400000] with N hN
  have : (400000 : ℝ) ≤ N := by exact_mod_cast hN
  exact cs_exp_neg_le_inv (by norm_num) (by linarith)

lemma cs_two_pow_natLog_le (hN : 1 ≤ N) : (2 : ℝ) ^ Nat.log 2 N ≤ N := by
  exact_mod_cast Nat.pow_log_le_self 2 (by omega)

lemma cs_two_pow_JC_le (hN : 1 ≤ N) : (2 : ℝ) ^ JC N ≤ 2 ^ 16 * (N : ℝ) ^ 6 := by
  have e : (2 : ℝ) ^ JC N = 2 ^ 16 * (2 ^ Nat.log 2 N) ^ 6 := by
    unfold JC; rw [← pow_mul, ← pow_add]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (cs_two_pow_natLog_le hN) 6)
    (by positivity)

lemma cs_ev_natLog : ∀ᶠ N : ℕ in atTop, (Nat.log 2 N : ℝ) ≤ N / 69 := by
  filter_upwards [cs_ev_log_le (c := 1 / 100) (by norm_num), eventually_ge_atTop 1] with N hl hN
  have h := cs_natLog_le hN
  have := Real.log_two_gt_d9
  have hL : (0 : ℝ) ≤ Nat.log 2 N := Nat.cast_nonneg _
  nlinarith

lemma cs_ev_JC : ∀ᶠ N : ℕ in atTop, 3 * JC N + 3 < N ∧ 2 * D0C N ≤ N := by
  filter_upwards [cs_ev_natLog, eventually_ge_atTop 1000] with N hL hN
  have hNr : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (18 * Nat.log 2 N + 51 : ℝ) < N := by linarith
  have h2 : (4 * Nat.log 2 N + 28 : ℝ) ≤ N := by linarith
  have h1' : 18 * Nat.log 2 N + 51 < N := by exact_mod_cast h1
  have h2' : 4 * Nat.log 2 N + 28 ≤ N := by exact_mod_cast h2
  unfold JC D0C; constructor <;> omega

/-- `√(N/2^N) ≤ e^{-3N/10}` and `(N+1)^4/2^N ≤ e^{-3N/10}`. -/
lemma cs_ev_tail : ∀ᶠ N : ℕ in atTop, Real.sqrt ((N : ℝ) / 2 ^ N) ≤ Real.exp (-(3 / 10 * N)) ∧
    ((N : ℝ) + 1) ^ 4 / 2 ^ N ≤ Real.exp (-(3 / 10 * N)) := by
  filter_upwards [cs_ev_poly_lt_exp 1 1 (c := 9 / 100) (by norm_num),
    cs_ev_poly_lt_exp 1 4 (c := 39 / 100) (by norm_num)] with N h1 h4
  have hl2 := Real.log_two_gt_d9
  have h2N : (2 : ℝ) ^ N = Real.exp (N * Real.log 2) := cs_two_pow N
  have h2pos : (0 : ℝ) < 2 ^ N := by positivity
  constructor
  · have hx : (N : ℝ) / 2 ^ N ≤ Real.exp (-(3 / 10 * N)) ^ 2 := by
      rw [div_le_iff₀ h2pos, ← Real.exp_nat_mul, h2N, ← Real.exp_add]
      have : (N : ℝ) ≤ Real.exp (9 / 100 * N) := by linarith
      refine this.trans (Real.exp_le_exp.2 ?_)
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      push_cast; nlinarith
    calc Real.sqrt ((N : ℝ) / 2 ^ N) ≤ Real.sqrt (Real.exp (-(3 / 10 * N)) ^ 2) :=
          Real.sqrt_le_sqrt hx
      _ = Real.exp (-(3 / 10 * N)) := Real.sqrt_sq (Real.exp_pos _).le
  · rw [div_le_iff₀ h2pos, h2N, ← Real.exp_add]
    refine (by linarith : ((N : ℝ) + 1) ^ 4 ≤ Real.exp (39 / 100 * N)).trans (Real.exp_le_exp.2 ?_)
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith

lemma cs_ev_eps4 : ∀ᶠ N : ℕ in atTop, epsN N ≤ 4 * Real.exp (-(3 / 10 * N)) := by
  filter_upwards [cs_ev_tail] with N h
  unfold epsN
  have h4 : (N : ℝ) ^ 4 / 2 ^ N ≤ ((N : ℝ) + 1) ^ 4 / 2 ^ N :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 4) (by positivity)
  have : 2 * (N : ℝ) ^ 4 / 2 ^ N = 2 * ((N : ℝ) ^ 4 / 2 ^ N) := by ring
  rw [this]; linarith [h.1, h.2]

lemma cs_ev_eps : ∀ᶠ N : ℕ in atTop, epsN N ≤ Real.exp (-((N : ℝ) / 200)) / 100 ∧
    epsN N < 1 / (2 * N) := by
  filter_upwards [cs_ev_eps4, cs_ev_poly_lt_exp 400 0 (c := 295 / 1000) (by norm_num),
    cs_ev_poly_lt_exp 8 1 (c := 3 / 10) (by norm_num), eventually_ge_atTop 1] with N he h1 h2 hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  simp only [pow_zero, mul_one, pow_one] at h1 h2
  constructor
  · refine he.trans ?_
    rw [le_div_iff₀ (by norm_num)]
    have : Real.exp (-((N : ℝ) / 200)) = Real.exp (295 / 1000 * N) * Real.exp (-(3 / 10 * N)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    nlinarith [Real.exp_pos (-(3 / 10 * (N : ℝ)))]
  · refine lt_of_le_of_lt he ?_
    rw [lt_div_iff₀ (by positivity)]
    have : Real.exp (3 / 10 * N) * Real.exp (-(3 / 10 * N)) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-(3 / 10 * (N : ℝ)))]

lemma cs_ev_sens : ∀ᶠ N : ℕ in atTop, 2 * ((N : ℝ) + 1) ^ 4 ≤ 2 ^ (dX N + 1) := by
  filter_upwards [cs_ev_poly_lt_exp 2 4 (c := 23 / 1000) (by norm_num)] with N h
  rw [cs_two_pow]
  refine h.le.trans (Real.exp_le_exp.2 ?_)
  have := cs_dX_ge N
  have := Real.log_two_gt_d9
  push_cast
  nlinarith

/-- FE1' at dimensions `D ≥ D0`: deviation `≤ 1/500`. -/
lemma cs_ev_dev : ∀ᶠ N : ℕ in atTop, ∀ D : ℕ, D0C N ≤ D → D ≤ N →
    2 * Real.sqrt ((N : ℝ) / 2 ^ D) + 2 * ((D + 1 : ℕ) : ℝ) ^ 4 / 2 ^ D ≤ 1 / 500 := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 4 (r := (2 : ℝ)) (by norm_num)
  obtain ⟨D1, hD1⟩ := eventually_atTop.1 (ht.eventually (eventually_le_nhds
    (by norm_num : (0 : ℝ) < 1 / 8000)))
  filter_upwards [eventually_ge_atTop (2 ^ D1), eventually_ge_atTop 1000] with N hN1 hN
  intro D hD hDN
  have hNr : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : D1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) hN1
  have hDD1 : D1 ≤ D + 1 := by unfold D0C at hD; omega
  have hpoly := hD1 (D + 1) hDD1
  have h2D : (0 : ℝ) < 2 ^ D := by positivity
  have hp : 2 * ((D + 1 : ℕ) : ℝ) ^ 4 / 2 ^ D ≤ 1 / 2000 := by
    have e : 2 * ((D + 1 : ℕ) : ℝ) ^ 4 / 2 ^ D = 4 * (((D + 1 : ℕ) : ℝ) ^ 4 / 2 ^ (D + 1)) := by
      rw [pow_succ]; field_simp; ring
    rw [e]; linarith
  have hs : Real.sqrt ((N : ℝ) / 2 ^ D) ≤ 1 / 2000 := by
    have hD0 : (2 : ℝ) ^ D0C N ≤ 2 ^ D := pow_le_pow_right₀ (by norm_num) hD
    have hD0' : 4096 * (N : ℝ) ^ 2 < 2 ^ D0C N := by
      have h := cs_lt_two_pow_natLog N
      have e : (2 : ℝ) ^ D0C N = 2 ^ 14 * (2 ^ Nat.log 2 N) ^ 2 := by
        unfold D0C; rw [← pow_mul, ← pow_add]; ring_nf
      rw [e]; nlinarith
    rw [show (1 / 2000 : ℝ) = Real.sqrt ((1 / 2000) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ h2D]
    nlinarith
  linarith

/-- The common lower bound for `causeRep(univ, r0) · e^{-N/200}`. -/
lemma cs_rhs_ge (hslT : slT N ≤ N / 1000) :
    Real.exp (-((2089 / 10000 + Real.log 2 / 30) * N)) / 8 ≤
      Real.exp (-(x0 * N + slT N)) / 2 ^ (dX N + 2) * Real.exp (-((N : ℝ) / 200)) := by
  have hx0 := x0_lt
  have hd := cs_dX_le N
  have hl2 := Real.log_two_gt_d9
  have hl0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have h2 : (2 : ℝ) ^ (dX N + 2) ≤ 8 * Real.exp (N / 30 * Real.log 2) := by
    have hd2 : (2 : ℝ) ^ dX N ≤ 2 * Real.exp (N / 30 * Real.log 2) := by
      rw [cs_two_pow]
      calc Real.exp (dX N * Real.log 2) ≤ Real.exp ((N / 30 + 1) * Real.log 2) :=
            Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hd hl0)
        _ = Real.exp (Real.log 2) * Real.exp (N / 30 * Real.log 2) := by
            rw [← Real.exp_add]; ring_nf
        _ = 2 * Real.exp (N / 30 * Real.log 2) := by rw [Real.exp_log (by norm_num)]
    rw [pow_add]; nlinarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hnum : Real.exp (-((2089 / 10000 + Real.log 2 / 30) * N)) ≤
      Real.exp (-(x0 * N + slT N)) * Real.exp (-((N : ℝ) / 200)) /
        Real.exp (N / 30 * Real.log 2) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  calc Real.exp (-((2089 / 10000 + Real.log 2 / 30) * N)) / 8
      ≤ Real.exp (-(x0 * N + slT N)) * Real.exp (-((N : ℝ) / 200)) /
          (8 * Real.exp (N / 30 * Real.log 2)) := by
        rw [div_mul_eq_div_div_swap]
        exact div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ Real.exp (-(x0 * N + slT N)) * Real.exp (-((N : ℝ) / 200)) / 2 ^ (dX N + 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h2
    _ = _ := by ring

/-! ### The final comparisons (against `exp(-aN)/8`, `a = 0.2089 + ln2/30`) -/

/-- The exponent of the common lower bound `cs_rhs_ge`. -/
noncomputable def csA : ℝ := 2089 / 10000 + Real.log 2 / 30

lemma cs_log2_sub_csA : 4611 / 10000 ≤ Real.log 2 - csA := by
  unfold csA; have := Real.log_two_gt_d9; linarith

lemma cs_csA_le : csA ≤ 24 / 100 := by
  unfold csA; have := Real.log_two_lt_d9; linarith

lemma cs_ev_H3 : ∀ᶠ N : ℕ in atTop,
    (N : ℝ) ^ 2 * 2 ^ (JC N + 4) * Real.exp (-((N : ℝ) / 100)) < Real.exp (-((N : ℝ) / 200)) := by
  filter_upwards [cs_ev_poly_lt_exp (2 ^ 20) 8 (c := 1 / 200) (by norm_num),
    eventually_ge_atTop 1] with N h hN
  have hJ := cs_two_pow_JC_le hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h8 : (N : ℝ) ^ 8 ≤ ((N : ℝ) + 1) ^ 8 := pow_le_pow_left₀ hN0 (by linarith) 8
  have hL : (N : ℝ) ^ 2 * 2 ^ (JC N + 4) ≤ 2 ^ 20 * ((N : ℝ) + 1) ^ 8 := by
    rw [pow_add]
    calc (N : ℝ) ^ 2 * (2 ^ JC N * 2 ^ 4) ≤ (N : ℝ) ^ 2 * (2 ^ 16 * (N : ℝ) ^ 6 * 2 ^ 4) := by gcongr
      _ = 2 ^ 20 * (N : ℝ) ^ 8 := by ring
      _ ≤ 2 ^ 20 * ((N : ℝ) + 1) ^ 8 := by gcongr
  have e : Real.exp (-((N : ℝ) / 200)) = Real.exp (1 / 200 * N) * Real.exp (-((N : ℝ) / 100)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hpos := Real.exp_pos (-((N : ℝ) / 100))
  calc (N : ℝ) ^ 2 * 2 ^ (JC N + 4) * Real.exp (-((N : ℝ) / 100))
      ≤ 2 ^ 20 * ((N : ℝ) + 1) ^ 8 * Real.exp (-((N : ℝ) / 100)) :=
        mul_le_mul_of_nonneg_right hL hpos.le
    _ < Real.exp (1 / 200 * N) * Real.exp (-((N : ℝ) / 100)) := mul_lt_mul_of_pos_right h hpos

lemma cs_ev_H4 : ∀ᶠ N : ℕ in atTop,
    4 * (N : ℝ) ^ 2 * Real.exp (23 / 50 * N) * 2 ^ JC N / 2 ^ N < Real.exp (-(csA * N)) / 8 := by
  filter_upwards [cs_ev_poly_lt_exp (2 ^ 21) 8 (c := 11 / 10000) (by norm_num),
    eventually_ge_atTop 1] with N h hN
  have hJ := cs_two_pow_JC_le hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h8 : (N : ℝ) ^ 8 ≤ ((N : ℝ) + 1) ^ 8 := pow_le_pow_left₀ hN0 (by linarith) 8
  have hc := cs_log2_sub_csA
  have hE := Real.exp_pos (23 / 50 * (N : ℝ))
  rw [div_lt_div_iff₀ (by positivity) (by norm_num), cs_two_pow N]
  have hL : 4 * (N : ℝ) ^ 2 * Real.exp (23 / 50 * N) * 2 ^ JC N * 8 ≤
      2 ^ 21 * ((N : ℝ) + 1) ^ 8 * Real.exp (23 / 50 * N) := by
    calc 4 * (N : ℝ) ^ 2 * Real.exp (23 / 50 * N) * 2 ^ JC N * 8
        ≤ 4 * (N : ℝ) ^ 2 * Real.exp (23 / 50 * N) * (2 ^ 16 * (N : ℝ) ^ 6) * 8 := by gcongr
      _ = 2 ^ 21 * (N : ℝ) ^ 8 * Real.exp (23 / 50 * N) := by ring
      _ ≤ 2 ^ 21 * ((N : ℝ) + 1) ^ 8 * Real.exp (23 / 50 * N) := by gcongr
  have hR : Real.exp (11 / 10000 * N) * Real.exp (23 / 50 * N) ≤
      Real.exp (-(csA * N)) * Real.exp (N * Real.log 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  calc 4 * (N : ℝ) ^ 2 * Real.exp (23 / 50 * N) * 2 ^ JC N * 8
      ≤ 2 ^ 21 * ((N : ℝ) + 1) ^ 8 * Real.exp (23 / 50 * N) := hL
    _ < Real.exp (11 / 10000 * N) * Real.exp (23 / 50 * N) := mul_lt_mul_of_pos_right h hE
    _ ≤ Real.exp (-(csA * N)) * Real.exp (N * Real.log 2) := hR

lemma cs_ev_H2 : ∀ᶠ N : ℕ in atTop,
    12 * N * ((2 * Real.sqrt ((N : ℝ) / 2 ^ N) + 2 * ((N : ℝ) + 1) ^ 4 / 2 ^ N) + epsN N) <
      Real.exp (-(csA * N)) / 8 := by
  filter_upwards [cs_ev_tail, cs_ev_eps4, cs_ev_poly_lt_exp 768 1 (c := 6 / 100) (by norm_num)]
    with N ht he h
  simp only [pow_one] at h
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set e3 := Real.exp (-(3 / 10 * N)) with he3
  have he3pos : 0 < e3 := Real.exp_pos _
  have hsum : (2 * Real.sqrt ((N : ℝ) / 2 ^ N) + 2 * ((N : ℝ) + 1) ^ 4 / 2 ^ N) + epsN N ≤ 8 * e3 := by
    have : 2 * ((N : ℝ) + 1) ^ 4 / 2 ^ N = 2 * (((N : ℝ) + 1) ^ 4 / 2 ^ N) := by ring
    rw [this]; linarith [ht.1, ht.2]
  have hc := cs_csA_le
  have hR : Real.exp (6 / 100 * N) * e3 ≤ Real.exp (-(csA * N)) := by
    rw [he3, ← Real.exp_add]; refine Real.exp_le_exp.2 ?_; nlinarith
  calc 12 * N * ((2 * Real.sqrt ((N : ℝ) / 2 ^ N) + 2 * ((N : ℝ) + 1) ^ 4 / 2 ^ N) + epsN N)
      ≤ 12 * N * (8 * e3) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (768 * N) * e3 / 8 := by ring
    _ < Real.exp (6 / 100 * N) * e3 / 8 := by
        refine div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (by linarith) he3pos) (by norm_num)
    _ ≤ Real.exp (-(csA * N)) / 8 := div_le_div_of_nonneg_right hR (by norm_num)

lemma cs_ev_floor : ∀ᶠ N : ℕ in atTop, phiFloor N ≤ Real.exp (-(csA * N)) / 8 ∧
    1 / (2 : ℝ) ^ N < Real.exp (-(csA * N)) / 8 := by
  filter_upwards [cs_ev_poly_lt_exp 16 1 (c := 4611 / 10000) (by norm_num)] with N h
  simp only [pow_one] at h
  have hc := cs_log2_sub_csA
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hkey : Real.exp (4611 / 10000 * N) ≤ Real.exp (-(csA * N)) * 2 ^ N := by
    rw [cs_two_pow, ← Real.exp_add]; refine Real.exp_le_exp.2 ?_; nlinarith
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  constructor
  · unfold phiFloor
    rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, div_le_div_iff₀ h2N (by norm_num)]
    linarith
  · rw [div_lt_div_iff₀ h2N (by norm_num)]
    linarith

end Census
end IIT
