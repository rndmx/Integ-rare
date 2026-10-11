/-
B1 lower bound, leaf `phi_S_le_EX` (W7 §3 item 4), the candidates `5 ≤ |S| ≤ K2N`:
W4's Proposition M / Proposition KT re-proved for ANY set `A` of at most three fixed rows
(constants `2τ, 2 Mk` of the two-row version become `3τ, 3 Mk`), via the general-`A` transfers
`tr2_abs`, `tr3_core` of B1Couple.
-/
import IIT.Census.B1SubCoX

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace IIT
namespace Census

open MeasureTheory Filter Finset

noncomputable section

variable {N : ℕ} {A : Finset (State N)} {s0 : State N} {w' : Param N}

/-- **(TR2) on `GoodW w̃`, at most three fixed rows.** -/
theorem tr2_goodW3 {w : Param N} (h : AgreeOff A w w') (hA3 : A.card ≤ 3) (hG : GoodW N s0 w')
    {S Y : Finset (Fin N)} (hY : Y ⊆ S) (t : State N) (i : Fin N) :
    |Num w S Y t i - Num w' S Y t i| ≤ ∑ a ∈ A, Pw w a + 3 * tauN N + 3 * Mk N S.card := by
  refine (tr2_abs h hY t i).trans ?_
  have hc : (A.card : ℝ) ≤ 3 := by exact_mod_cast hA3
  have h4 : ∑ a ∈ A, Pw w' a ≤ 3 * tauN N := by
    calc ∑ a ∈ A, Pw w' a ≤ ∑ _a ∈ A, tauN N := sum_le_sum fun a _ => Pw_le_tauN_of_g2 hG.g2 a
      _ = A.card * tauN N := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 3 * tauN N := by have := tauN_pos N; nlinarith
  have hQ : ∑ a ∈ A, blockQ w' i S a ≤ 3 * Mk N S.card := by
    calc ∑ a ∈ A, blockQ w' i S a ≤ ∑ _a ∈ A, Mk N S.card := sum_le_sum fun a _ => blockQ_le_Mk hG i S a
      _ = A.card * Mk N S.card := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 3 * Mk N S.card := by have := Mk_nonneg N S.card; nlinarith
  have h0 : 0 ≤ ∑ a ∈ A, blockQ w' i S a := sum_nonneg fun a _ => blockQ_nonneg w' i S a
  have hdiv : (∑ a ∈ A, blockQ w' i S a) / (2 : ℝ) ^ (S.card - Y.card) ≤ ∑ a ∈ A, blockQ w' i S a :=
    div_le_self h0 (one_le_pow₀ (by norm_num))
  linarith

/-- **(TR3) on `GoodW w̃`, at most three fixed rows.** -/
theorem tr3_goodW3 {w : Param N} (h : AgreeOff A w w') (hA3 : A.card ≤ 3) (hG : GoodW N s0 w')
    {S : Finset (Fin N)} {j : Fin N} (hj : j ∈ S) (t : State N) :
    Num w S S t j - Num w S {j} t j ≤ (Num w' S S t j - Num w' S {j} t j)
      + (1 - 2 / (2 : ℝ) ^ S.card) * ∑ a ∈ A, Pw w a + 3 * tauN N
      + 3 * (1 + 4 / (2 : ℝ) ^ S.card) * Mk N S.card := by
  refine (tr3_core h hj t).trans ?_
  have hc : (A.card : ℝ) ≤ 3 := by exact_mod_cast hA3
  have h4 : ∑ a ∈ A, Pw w' a ≤ 3 * tauN N := by
    calc ∑ a ∈ A, Pw w' a ≤ ∑ _a ∈ A, tauN N := sum_le_sum fun a _ => Pw_le_tauN_of_g2 hG.g2 a
      _ = A.card * tauN N := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 3 * tauN N := by have := tauN_pos N; nlinarith
  have hQ : ∑ a ∈ A, blockQ w' j S a ≤ 3 * Mk N S.card := by
    calc ∑ a ∈ A, blockQ w' j S a ≤ ∑ _a ∈ A, Mk N S.card := sum_le_sum fun a _ => blockQ_le_Mk hG j S a
      _ = A.card * Mk N S.card := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 3 * Mk N S.card := by have := Mk_nonneg N S.card; nlinarith
  have hM := Mk_nonneg N S.card
  have hc' : 0 ≤ 1 + 2 / (2 : ℝ) ^ S.card := by positivity
  have h1 : (1 + 2 / (2 : ℝ) ^ S.card) * ∑ a ∈ A, blockQ w' j S a
      ≤ (1 + 2 / (2 : ℝ) ^ S.card) * (3 * Mk N S.card) := mul_le_mul_of_nonneg_left hQ hc'
  have h2 : (1 + 2 / (2 : ℝ) ^ S.card) * (3 * Mk N S.card)
      ≤ 3 * (1 + 4 / (2 : ℝ) ^ S.card) * Mk N S.card := by
    have : 2 / (2 : ℝ) ^ S.card ≤ 4 / 2 ^ S.card := by gcongr; norm_num
    nlinarith
  linarith

/-- `ε_k := H + 2τ + 2 Mk N k`. -/
def epsK3 (N k : ℕ) (H : ℝ) : ℝ := H + 3 * tauN N + 3 * Mk N k

/-- `L_k := Zs w̃ / 2 - 8 N σ_N - dlev N k - ε_k`. -/
def LK3 (N k : ℕ) (Z H : ℝ) : ℝ := Z / 2 - 8 * N * sigN N - dlev N k - epsK3 N k H

/-- `ρ_k := k (δ_k + 2 ε_k) / L_k`. -/
def rhoK3 (N k : ℕ) (Z H : ℝ) : ℝ := k * (deltaK N k + 2 * epsK3 N k H) / LK3 N k Z H

/-- `fl_k := Dev N k + 2τ + 2 (1 + 2^{2-k}) Mk N k`. -/
def flK3 (N k : ℕ) : ℝ := Dev N k + 3 * tauN N + 3 * (1 + 4 / (2 : ℝ) ^ k) * Mk N k

lemma epsK3_nonneg (N k : ℕ) {H : ℝ} (hH : 0 ≤ H) : 0 ≤ epsK3 N k H := by
  unfold epsK3; have := tauN_pos N; have := Mk_nonneg N k; positivity

lemma flK3_nonneg {N : ℕ} (hN : 1 ≤ N) (k : ℕ) : 0 ≤ flK3 N k := by
  unfold flK3; have := tauN_pos N; have := Mk_nonneg N k; have := Dev_nonneg (N := N) k hN
  positivity

/-- **Proposition M (M1).** `Num w S Y t i ≥ L_k`. -/
theorem propM1_3 {w : Param N} (hN : 1 ≤ N) (hA : AgreeOff A w w') (hA3 : A.card ≤ 3) (hG : GoodW N s0 w')
    {S Y : Finset (Fin N)} {i : Fin N} (hi : i ∈ S) (hY : Y ⊆ S) (t : State N) :
    LK3 N S.card (Zs w') (∑ a ∈ A, Pw w a) ≤ Num w S Y t i := by
  have h1 := tr2_goodW3 hA hA3 hG hY t i
  have h2 := dev_le_dlev hG hN hi hY t
  have h3 := hG.g11 i
  have hsub : 0 ≤ subSum w' i Y t / (12 * (2 : ℝ) ^ (S.card - Y.card)) :=
    div_nonneg (subSum_nonneg _ _ _ _) (by positivity)
  unfold LK3 epsK3
  unfold cNum at h2
  rw [abs_le] at h1 h2 h3
  linarith [h1.1, h2.1, h3.2]

/-- **Proposition M (M2).** `|Num w S S t i - Num w S S t' i| ≤ δ_k + 2 ε_k`. -/
theorem propM2_3 {w : Param N} (hN : 1 ≤ N) (hA : AgreeOff A w w') (hA3 : A.card ≤ 3) (hG : GoodW N s0 w')
    {S : Finset (Fin N)} (hS : 1 ≤ S.card) {i : Fin N} (hi : i ∈ S) (t t' : State N) :
    |Num w S S t i - Num w S S t' i| ≤
      deltaK N S.card + 2 * epsK3 N S.card (∑ a ∈ A, Pw w a) := by
  have hdiff : |Num w' S S t i - Num w' S S t' i| ≤ deltaK N S.card := by
    rw [Num_S_sub t t']
    have h1 := dev_le_dlev hG hN hi (subset_refl S) t
    have h2 := dev_le_dlev hG hN hi (subset_refl S) t'
    have hs1 := subSum_S_le hG i hS t
    have hs2 := subSum_S_le hG i hS t'
    have hn1 := subSum_nonneg w' i S t
    have hn2 := subSum_nonneg w' i S t'
    unfold deltaK
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith
  have e1 := tr2_goodW3 hA hA3 hG (subset_refl S) t i
  have e2 := tr2_goodW3 hA hA3 hG (subset_refl S) t' i
  unfold epsK3
  rw [abs_le] at e1 e2 hdiff ⊢
  constructor <;> linarith

/-- **Proposition M (M3).** `sysBackCause (tpmOf z) S s s t ≤ e^{ρ_k} / 2^k`. -/
theorem propM3_3 (hN : 1 ≤ N) {z : Param N} (hz : z ∈ openCube N) {s : State N}
    (hA : AgreeOff A (flipP s z) w') (hA3 : A.card ≤ 3) (hG : GoodW N s0 w') {S : Finset (Fin N)}
    (hS : 1 ≤ S.card)
    (hL : 0 < LK3 N S.card (Zs w') (∑ a ∈ A, Pw (flipP s z) a)) (t : State N) :
    sysBackCause (tpmOf z) S s s t ≤
      Real.exp (rhoK3 N S.card (Zs w') (∑ a ∈ A, Pw (flipP s z) a)) / 2 ^ S.card := by
  set w := flipP s z with hw
  have hZpos : 0 < Zs w := Zs_pos hz s
  have hratio : ∀ t t', sysCauseProb (tpmOf z) S s s t ≤
      Real.exp (rhoK3 N S.card (Zs w') (∑ a ∈ A, Pw w a)) * sysCauseProb (tpmOf z) S s s t' := by
    intro t t'
    rw [sysCauseProb_eq_Num, sysCauseProb_eq_Num, ← hw, prod_div_distrib, prod_div_distrib,
      ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ (prod_nonneg fun _ _ => hZpos.le)
    have hδ : 0 ≤ deltaK N S.card + 2 * epsK3 N S.card (∑ a ∈ A, Pw w a) := by
      have := epsK3_nonneg N S.card (H := ∑ a ∈ A, Pw w a) (sum_nonneg fun a _ => Pw_nonneg w a)
      have := dlev_nonneg N S.card
      have := E6_nonneg N S.card
      unfold deltaK; positivity
    exact prod_le_exp_mul_prod_L S (fun i => Num w S S t i) (fun i => Num w S S t' i) hL hδ
      (fun i hi => propM1_3 hN hA hA3 hG hi subset_rfl t')
      (fun i hi => (abs_le.1 (propM2_3 hN hA hA3 hG hS hi t t')).2)
      (fun i _ => Num_nonneg _ _ _ _ _)
  have hpos : ∀ t, 0 < sysCauseProb (tpmOf z) S s s t := by
    intro t
    rw [sysCauseProb_eq_Num]
    exact prod_pos fun i _ => div_pos (Num_pos hz s S S t i) (Zs_pos hz s)
  exact sysBackCause_le_of_ratio (tpmOf z) S s s (Real.exp_pos _) hpos hratio t

/-- **Proposition KT** (tilted `k`-sets, the corrected A8 `k_upper_tilt`). -/
theorem propKT3 (hN : 1 ≤ N) {z : Param N} (hz : z ∈ openCube N) {s : State N}
    (hA : AgreeOff A (flipP s z) w') (hA3 : A.card ≤ 3) (hG : GoodW N s0 w') {S : Finset (Fin N)}
    (hk2 : 2 ≤ S.card)
    (hL : 0 < LK3 N S.card (Zs w') (∑ a ∈ A, Pw (flipP s z) a)) :
    phi z s S ≤ S.card *
      (Real.exp (rhoK3 N S.card (Zs w') (∑ a ∈ A, Pw (flipP s z) a)) / 2 ^ S.card *
        (((1 - 2 / (2 : ℝ) ^ S.card) * (∑ a ∈ A, Pw (flipP s z) a) + flK3 N S.card) /
          (LK3 N S.card (Zs w') (∑ a ∈ A, Pw (flipP s z) a) * Real.log 2))) := by
  set w := flipP s z with hw
  set H := ∑ a ∈ A, Pw w a with hH
  set L := LK3 N S.card (Zs w') H with hLdef
  obtain ⟨j, hj⟩ : S.Nonempty := card_pos.1 (by omega)
  have hjS : ({j} : Finset (Fin N)) ⊆ S := singleton_subset_iff.2 hj
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hH0 : 0 ≤ H := sum_nonneg fun a _ => Pw_nonneg _ _
  have hc : 0 ≤ 1 - 2 / (2 : ℝ) ^ S.card := by
    have : (2 : ℝ) ≤ 2 ^ S.card := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ S.card := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [sub_nonneg, div_le_one (by positivity)]; exact this
  have hnum0 : 0 ≤ (1 - 2 / (2 : ℝ) ^ S.card) * H + flK3 N S.card :=
    add_nonneg (mul_nonneg hc hH0) (flK3_nonneg hN _)
  have hB0 : (0 : ℝ) ≤ Real.exp (rhoK3 N S.card (Zs w') H) / 2 ^ S.card *
      (((1 - 2 / (2 : ℝ) ^ S.card) * H + flK3 N S.card) / (L * Real.log 2)) := by
    have := hL; positivity
  refine phi_le_cause hz hk2 hj hB0 fun t => ?_
  have hback := propM3_3 hN hz hA hA3 hG (by omega) hL t
  have hb := propM1_3 hN hA hA3 hG hj hjS t
  have hbpos : 0 < Num w S {j} t j := Num_pos hz s S {j} t j
  have hlog : pos (Real.logb 2 (Num w S S t j / Num w S {j} t j)) ≤
      ((1 - 2 / (2 : ℝ) ^ S.card) * H + flK3 N S.card) / (L * Real.log 2) := by
    refine (pos_logb_div_le_pos (Num_pos hz s S S t j) hbpos).trans ?_
    have h3 := tr3_goodW3 hA hA3 hG hj t
    have h4 := Num_diff_le hG hN hj (subset_refl S) hjS t
    have hdiff : Num w S S t j - Num w S {j} t j ≤
        (1 - 2 / (2 : ℝ) ^ S.card) * H + flK3 N S.card := by
      unfold flK3
      rw [abs_le] at h4
      linarith [h4.2]
    have hmax : max (Num w S S t j - Num w S {j} t j) 0 ≤
        (1 - 2 / (2 : ℝ) ^ S.card) * H + flK3 N S.card := max_le hdiff hnum0
    exact div_le_div₀ hnum0 hmax (mul_pos hL hl2) (mul_le_mul_of_nonneg_right hb hl2.le)
  exact mul_le_mul hback hlog (pos_nonneg _) (by positivity)


lemma two_mul_le_two_pow' {k : ℕ} (hk : 1 ≤ k) : 2 * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [pow_succ]; omega

lemma kdiv_le_half {k : ℕ} (hk : 1 ≤ k) : (k : ℝ) / 2 ^ k ≤ 1 / 2 := by
  rw [div_le_iff₀ (by positivity)]
  have : ((2 * k : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast two_mul_le_two_pow' hk
  push_cast at this
  linarith

/-- **Sizes `2 ≤ |S| ≤ K2N`, three fixed rows** (deterministic): `φ_s(S) ≤ 8 P` when `P ≥ N^9 σ_N` dominates the fixed
rows (`Σ_A P_a ≤ 3P`) and `Σ_A P_a ≤ 2/N³`: `φ_s(S) ≤ 32 P`. -/
theorem phi_mid3_det (hnum : W4Num N) (hA3 : A.card ≤ 3) {z : Param N} (hz : z ∈ openCube N)
    {s : State N} (hA : AgreeOff A (flipP s z) w') (hG : GoodW N s0 w') {S : Finset (Fin N)}
    (hk2 : 2 ≤ S.card) (hkK : S.card ≤ K2N N) {P : ℝ} (hP : (N : ℝ) ^ 9 * sigN N ≤ P)
    (hHP : ∑ a ∈ A, Pw (flipP s z) a ≤ 3 * P) (hH : ∑ a ∈ A, Pw (flipP s z) a ≤ 2 / (N : ℝ) ^ 3) :
    phi z s S ≤ 32 * P := by
  have hN := hnum.one_le
  set w := flipP s z with hw
  set k := S.card with hkdef
  set H := ∑ a ∈ A, Pw w a with hHdef
  set L := LK3 N k (Zs w') H with hLdef
  set ρ := rhoK3 N k (Zs w') H with hρdef
  set x : ℝ := (k : ℝ) / 2 ^ k with hx
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hσ := sigN_pos N
  have hτ := tauN_pos N
  have hH0 : 0 ≤ H := sum_nonneg fun a _ => Pw_nonneg _ _
  have hdl0 := dlev_nonneg N k
  have hMk0 := Mk_nonneg N k
  have hE60 := E6_nonneg N k
  have hZ'1 := hG.g3.1
  have n1 := hnum.sig8
  have n2 := hnum.dl k (by omega) hkK
  have n3 := hnum.tm k (by omega) hkK
  have n4 := hnum.sig64
  have n5 := hnum.fl k (by omega) (card_le_N S)
  have nN2 := hnum.n2
  have hNH : (N : ℝ) * H ≤ 2 / 10000 := by
    have h1 : (N : ℝ) * H ≤ N * (2 / (N : ℝ) ^ 3) := mul_le_mul_of_nonneg_left hH (by positivity)
    have e : (N : ℝ) * (2 / (N : ℝ) ^ 3) = 2 * (1 / (N : ℝ) ^ 2) := by field_simp
    linarith
  have hHle : H ≤ 2 / 10000 := (le_mul_of_one_le_left hH0 hN').trans hNH
  have hdl : dlev N k ≤ 1 / 10000 := (le_mul_of_one_le_left hdl0 hN').trans n2
  have htm3 : (N : ℝ) * (3 * tauN N + 3 * Mk N k) ≤ 15 / 100000 := by
    have : (N : ℝ) * (3 * tauN N + 3 * Mk N k) = 3 / 2 * ((N : ℝ) * (2 * tauN N + 2 * Mk N k)) := by ring
    linarith
  have htm3' : 3 * tauN N + 3 * Mk N k ≤ 15 / 100000 :=
    (le_mul_of_one_le_left (by positivity) hN').trans htm3
  have hσ8 : 8 * N * sigN N ≤ 1 / 10000 := n1
  have hL1 : 1 / 5 ≤ L := by
    simp only [hLdef, LK3, epsK3]; linarith
  have hLpos : 0 < L := by linarith
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast card_le_N S
  have hk1 : 1 ≤ k := by omega
  have hxle := kdiv_le_half hk1
  have hnum' : (k : ℝ) * (deltaK N k + 2 * epsK3 N k H) ≤ 1 / 10 := by
    have e1 : (k : ℝ) * (deltaK N k + 2 * epsK3 N k H) =
        ((k : ℝ) * (1 / 2 : ℝ) ^ (k - 1)) / 12 + (k : ℝ) * E6 N k / 12 + 2 * ((k : ℝ) * dlev N k)
          + 2 * ((k : ℝ) * H) + 2 * ((k : ℝ) * (3 * tauN N + 3 * Mk N k)) := by
      unfold deltaK epsK3; ring
    rw [e1, one_div_two_pow_pred hk1]
    have a1 : (k : ℝ) * E6 N k ≤ 1 / 10000 := by
      calc (k : ℝ) * E6 N k ≤ N * (64 * N * sigN N) :=
            mul_le_mul hkN (E6_le k hN) hE60 (by positivity)
        _ = 64 * (N : ℝ) ^ 2 * sigN N := by ring
        _ ≤ 1 / 10000 := n4
    have a2 : (k : ℝ) * dlev N k ≤ 1 / 10000 := (mul_le_mul_of_nonneg_right hkN hdl0).trans n2
    have a3 : (k : ℝ) * H ≤ 2 / 10000 := (mul_le_mul_of_nonneg_right hkN hH0).trans hNH
    have a4 : (k : ℝ) * (3 * tauN N + 3 * Mk N k) ≤ 15 / 100000 :=
      (mul_le_mul_of_nonneg_right hkN (by positivity)).trans htm3
    have : (2 * ((k : ℝ) / 2 ^ k)) / 12 ≤ 2 * (1 / 2) / 12 := by gcongr
    linarith
  have hρle : ρ ≤ 1 / 2 := by
    simp only [hρdef, rhoK3]
    rw [div_le_iff₀ hLpos]
    nlinarith
  have hexp : Real.exp ρ ≤ 2 := (Real.exp_le_exp.2 hρle).trans exp_half_le_two
  have hKT : phi z s S ≤ (k : ℝ) * (Real.exp ρ / 2 ^ k *
      (((1 - 2 / (2 : ℝ) ^ k) * H + flK3 N k) / (L * Real.log 2))) :=
    propKT3 hN hz hA hA3 hG (by omega) hLpos
  have hX : x * (1 - 2 / (2 : ℝ) ^ k) ≤ 1 / 2 := by
    have : 0 ≤ 2 / (2 : ℝ) ^ k := by positivity
    have : 0 ≤ x := by positivity
    nlinarith
  have hc0 : 0 ≤ 1 - 2 / (2 : ℝ) ^ k := by
    have : (2 : ℝ) ≤ 2 ^ k := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [sub_nonneg, div_le_one (by positivity)]; exact this
  have hx0 : 0 ≤ x := by positivity
  have hfl3 : flK3 N k ≤ 3 / 2 * flK N k := by
    have := Dev_nonneg (N := N) k hN
    unfold flK3 flK; nlinarith
  have hflP : x * flK3 N k ≤ 2 / 10000 * P := by
    have : x * flK3 N k ≤ x * (3 / 2 * flK N k) := mul_le_mul_of_nonneg_left hfl3 hx0
    nlinarith
  have hcP : x * ((1 - 2 / (2 : ℝ) ^ k) * H + flK3 N k) ≤ 151 / 100 * P := by
    have e : x * ((1 - 2 / (2 : ℝ) ^ k) * H + flK3 N k) =
        (x * (1 - 2 / (2 : ℝ) ^ k)) * H + x * flK3 N k := by ring
    rw [e]
    have hX0 : 0 ≤ x * (1 - 2 / (2 : ℝ) ^ k) := mul_nonneg hx0 hc0
    have : x * (1 - 2 / (2 : ℝ) ^ k) * H ≤ 1 / 2 * (3 * P) :=
      mul_le_mul hX hHP hH0 (by norm_num)
    nlinarith
  have hl2 := Real.log_two_gt_d9
  have hl2pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hRHS : (k : ℝ) * (Real.exp ρ / 2 ^ k *
      (((1 - 2 / (2 : ℝ) ^ k) * H + flK3 N k) / (L * Real.log 2))) =
      Real.exp ρ * (x * ((1 - 2 / (2 : ℝ) ^ k) * H + flK3 N k)) / (L * Real.log 2) := by
    simp only [hx]; field_simp
  rw [hRHS] at hKT
  have hX0' : 0 ≤ x * ((1 - 2 / (2 : ℝ) ^ k) * H + flK3 N k) := by
    have := flK3_nonneg hN k
    exact mul_nonneg hx0 (add_nonneg (mul_nonneg hc0 hH0) this)
  have hP0 : 0 ≤ P := le_trans (by positivity) hP
  refine hKT.trans ?_
  rw [div_le_iff₀ (mul_pos hLpos hl2pos)]
  have h1 : Real.exp ρ * (x * ((1 - 2 / (2 : ℝ) ^ k) * H + flK3 N k)) ≤ 2 * (151 / 100 * P) :=
    mul_le_mul hexp hcP hX0' (by norm_num)
  have h2 : 32 * P * (1 / 5 * (6931471803 / 10000000000)) ≤ 32 * P * (L * Real.log 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul hL1 (by norm_num at hl2 ⊢; linarith) (by norm_num) hLpos.le
  nlinarith

/-- **Leaf `phi_S_le_EX`, case `2 ≤ |S| ≤ K2N`** (three-row Prop KT; covers pairs, triples, 4-sets and mid
sizes at once, since the target `β N / 10⁶` is generous). -/
theorem phi_S_le_EX_le_K2N : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    ∀ w ∈ openCube N, w ∈ EX N s r0 x → EXFacts N s r0 x w → RestGood N s r0 x w →
      SubGood N s r0 x w → ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ K2N N →
        phi (flipP s w) s S < betaW w * N / 10 ^ 6 := by
  filter_upwards [ev_W4Num, tc_of_EX, sumA_le, eventually_ge_atTop (10 ^ 8)] with N hnum htc hsum hNbig
  intro s r0 x hham w ho hw hF hR hSG S hk2 hkK
  obtain ⟨w', hA, -, hG, -⟩ := hSG.cmp
  have hN : 1 ≤ N := hnum.one_le
  have hN' : (10 ^ 8 : ℝ) ≤ N := by exact_mod_cast hNbig
  set z := flipP s w with hz
  have hzo : z ∈ openCube N := flipP_mem_openCube ho
  have hzw : flipP s z = w := flipP_invol s w
  have hH := hsum s r0 x hham w ho hw hF
  have htc := htc s r0 x hham w ho hw hF hR
  have hA3 : (rowsA s r0 x).card ≤ 3 := by
    simp only [rowsA]
    exact (card_insert_le _ _).trans (Nat.succ_le_succ (card_insert_le _ _))
  have hHP : ∑ a ∈ rowsA s r0 x, Pw w a ≤ 3 * Pw w r0 := by
    calc ∑ a ∈ rowsA s r0 x, Pw w a ≤ ∑ _a ∈ rowsA s r0 x, Pw w r0 :=
          sum_le_sum fun a _ => by rw [← htc]; exact Pw_le_tcRow w a
      _ = (rowsA s r0 x).card * Pw w r0 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 3 * Pw w r0 := by
          have : ((rowsA s r0 x).card : ℝ) ≤ 3 := by exact_mod_cast hA3
          have := Pw_nonneg w r0; nlinarith
  -- `P(r0) ≥ N^9 σ_N`
  have hP9 : (N : ℝ) ^ 9 * sigN N ≤ Pw w r0 := by
    have hsig : sigN N = Real.exp (-(x0 * N)) := by
      unfold sigN x0
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (Real.exp_pos _).le, ← Real.exp_add,
        show (2 / 3 : ℝ) ^ N = Real.exp (Real.log (2 / 3) * N) by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]]
      congr 1
      rw [show Real.log (2 / 3) = -Real.log (3 / 2) by
        rw [← Real.log_inv]; norm_num]
      ring
    have hNpos : (0 : ℝ) < N := by linarith
    have hN9 : (N : ℝ) ^ 9 = Real.exp (9 * Real.log N) := by
      rw [show 9 * Real.log N = Real.log ((N : ℝ) ^ 9) by rw [Real.log_pow]; norm_num,
        Real.exp_log (by positivity)]
    rw [hsig, hN9, ← Real.exp_add, Pw_eq_exp ho]
    apply Real.exp_le_exp.2
    have := hF.T
    linarith
  have hphi := phi_mid3_det hnum hA3 hzo (by rw [hzw]; exact hA) hG hk2 hkK hP9
    (by rw [hzw]; exact hHP) (by rw [hzw]; exact hH)
  have hZ : Zs w ≤ 3 := by
    have h1 := Zs_le_add hA
    have h2 := hG.g3.2.1
    have h3 : 2 / (N : ℝ) ^ 3 ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (2 : ℝ) ≤ N := by linarith
      have : (2 : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) this 3
      linarith
    linarith
  have hZpos : 0 < Zs w := b1_Zs_pos ho
  have hPpos : 0 < Pw w r0 := b1_Pw_pos ho r0
  unfold betaW; rw [htc]
  calc phi z s S ≤ 32 * Pw w r0 := hphi
    _ < Pw w r0 * N / (3 * 10 ^ 6) := by
        rw [lt_div_iff₀ (by norm_num)]; nlinarith
    _ ≤ Pw w r0 / Zs w * N / 10 ^ 6 := by
        rw [div_mul_eq_mul_div, div_div]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith

end

end Census
end IIT
