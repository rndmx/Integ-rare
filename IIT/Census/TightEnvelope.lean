/-
Census of complexes: the envelope bound for candidates of moderate size.

On the good event `GoodW` together with the sharp deviation bound `gSharp` (for the flipped
parameters `flipP s z`), eventually in `N`, every candidate `S` with `22 ≤ |S| ≤ KN N` has
`φ_s < cstar · sqrt (log N) · σ_N`.  The argument is the cause-side bound of `BigPhiDet`
(`φ_s ≤ |S| e² / 2^|S| · (8 / ln 2) · D` for any bound `D` on the numerator differences at a
single-unit split), used with the sharp deviation `Dev'`, of order `sqrt (|S| log N) σ_N`.
-/
import IIT.Census.BigPhiDet
import IIT.Census.TightStats

namespace IIT
namespace Census

open Finset Filter Topology

variable {N : ℕ}

/-- The sharp deviation between the conditioned numerators of a candidate of size `k`. -/
noncomputable def Dev' (N k : ℕ) : ℝ :=
  4 * Real.sqrt (LkN N k * Vbd N k)
    + (2 * Real.sqrt (6 * sigN N ^ 2 * LkN N k) + 2 * tauN N * LkN N k) / 12

lemma Dev'_nonneg {N : ℕ} (k : ℕ) (hN : 1 ≤ N) : 0 ≤ Dev' N k := by
  have := LkN_nonneg' k hN
  have := tauN_pos N
  unfold Dev'; positivity

/-- Two numerators of the same unit with purviews inside `S` differ by at most `Dev' N |S|`. -/
lemma Num_diff_le' {s : State N} {w : Param N} (hG : GoodW N s w) (hS : gSharp N w) (hN : 1 ≤ N)
    {S Y Y' : Finset (Fin N)} {i : Fin N} (hi : i ∈ S) (hY : Y ⊆ S) (hY' : Y' ⊆ S) (t : State N) :
    |Num w S Y t i - Num w S Y' t i| ≤ Dev' N S.card := by
  rw [Num_sub_Num hY hY']
  have h1 := dev_le_dsmall hG hN hi hY t
  have h2 := dev_le_dsmall hG hN hi hY' t
  have h3 := hS S i Y Y' t hi hY hY'
  have habs : |(Num w S Y t i - cNum w S Y t i) - (Num w S Y' t i - cNum w S Y' t i)
      + DQ w S Y Y' t i / 12| ≤ |Num w S Y t i - cNum w S Y t i|
        + |Num w S Y' t i - cNum w S Y' t i| + |DQ w S Y Y' t i| / 12 := by
    have := abs_add_le ((Num w S Y t i - cNum w S Y t i) - (Num w S Y' t i - cNum w S Y' t i))
      (DQ w S Y Y' t i / 12)
    have h4 := abs_sub (Num w S Y t i - cNum w S Y t i) (Num w S Y' t i - cNum w S Y' t i)
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 12)] at this
    linarith
  unfold Dev'
  unfold dsmall at h1 h2
  linarith

/-- Cause side for intermediate sizes, with a general bound `D` on the numerator differences at
the single-unit splits: `φ_s ≤ |S| e² / 2^|S| · (8 / ln 2) · D`. -/
lemma phi_le_rangeI' {s : State N} {z : Param N} (hz : z ∈ openCube N)
    (hG : GoodW N s (flipP s z)) (hN : 1 ≤ N) {S : Finset (Fin N)} (hk2 : 2 ≤ S.card)
    (hlev : 16 * N * sigN N / 2 + dlev N S.card ≤ 1 / 8 ∧
      (S.card : ℝ) * 8 * (((1 / 2 : ℝ) ^ (S.card - 1) + E6 N S.card) / 12
        + 2 * dlev N S.card) ≤ 2)
    {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ j ∈ S, ∀ t, |Num (flipP s z) S S t j - Num (flipP s z) S {j} t j| ≤ D) :
    phi z s S ≤ (S.card : ℝ) * Real.exp 2 / 2 ^ S.card * (8 / Real.log 2) * D := by
  set w := flipP s z with hw
  set k := S.card with hkdef
  obtain ⟨j, hj⟩ : S.Nonempty := card_pos.1 (by omega)
  have hZ := hG.g3.1
  have hZpos : 0 < Zs w := Zs_pos hz s
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlow : ∀ i ∈ S, ∀ Y ⊆ S, ∀ t, 1 / 8 ≤ Num w S Y t i := by
    intro i hi Y hY t
    have := Num_lower hZ (hG.g11 i) (dev_le_dlev hG hN hi hY t) hlev.1 (subSum_nonneg w i Y t)
    linarith
  set δ : ℝ := ((1 / 2 : ℝ) ^ (k - 1) + E6 N k) / 12 + 2 * dlev N k with hδ
  have hdiff : ∀ i ∈ S, ∀ t t', |Num w S S t i - Num w S S t' i| ≤ δ := by
    intro i hi t t'
    rw [Num_S_sub t t']
    have h1 := dev_le_dlev hG hN hi (subset_refl S) t
    have h2 := dev_le_dlev hG hN hi (subset_refl S) t'
    have hs1 := subSum_S_le hG i (by omega : 1 ≤ S.card) t
    have hs2 := subSum_S_le hG i (by omega : 1 ≤ S.card) t'
    have hn1 := subSum_nonneg w i S t
    have hn2 := subSum_nonneg w i S t'
    have hsub : |subSum w i S t - subSum w i S t'| ≤ (1 / 2 : ℝ) ^ (k - 1) + E6 N k :=
      abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    have habs := abs_add_le ((Num w S S t i - cNum w S S t i) - (Num w S S t' i - cNum w S S t' i))
      ((subSum w i S t - subSum w i S t') / 12)
    have h4 := abs_sub (Num w S S t i - cNum w S S t i) (Num w S S t' i - cNum w S S t' i)
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 12)] at habs
    rw [hδ]
    have : |subSum w i S t - subSum w i S t'| / 12 ≤ ((1 / 2 : ℝ) ^ (k - 1) + E6 N k) / 12 := by
      linarith
    linarith
  have hsum : ∑ i ∈ S, 8 * δ ≤ 2 := by
    rw [sum_const, nsmul_eq_mul, ← hkdef]
    rw [← mul_assoc]
    exact hlev.2
  have hratio : ∀ t t', sysCauseProb (tpmOf z) S s s t ≤
      Real.exp 2 * sysCauseProb (tpmOf z) S s s t' := by
    intro t t'
    rw [sysCauseProb_eq_Num, sysCauseProb_eq_Num, ← hw, prod_div_distrib, prod_div_distrib,
      ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ (prod_nonneg fun _ _ => hZpos.le)
    exact prod_le_exp_mul_prod S _ _ (fun _ => δ) (fun i hi => hlow i hi S subset_rfl t)
      (fun i hi => hlow i hi S subset_rfl t') (fun i hi => hdiff i hi t t') hsum
  have hpos : ∀ t, 0 < sysCauseProb (tpmOf z) S s s t := by
    intro t
    rw [sysCauseProb_eq_Num]
    exact prod_pos fun i _ => div_pos (Num_pos hz s S S t i) (Zs_pos hz s)
  have hback := sysBackCause_le_of_ratio (tpmOf z) S s s (Real.exp_pos 2) hpos hratio
  set B : ℝ := Real.exp 2 / 2 ^ k * (8 / Real.log 2 * D) with hB
  have hB0 : 0 ≤ B := by positivity
  have hphi := phi_le_cause hz hk2 hj hB0 (B := B) (fun tc => by
    have hlog : pos (Real.logb 2 (Num w S S tc j / Num w S {j} tc j)) ≤ 8 / Real.log 2 * D := by
      have hj1 := hlow j hj {j} (singleton_subset_iff.2 hj) tc
      refine (pos_logb_div_le (Num_pos hz s S S tc j) (by linarith)).trans ?_
      have hd := hD j hj tc
      calc |Num w S S tc j - Num w S {j} tc j| / (Num w S {j} tc j * Real.log 2)
          ≤ D / (1 / 8 * Real.log 2) :=
            div_le_div₀ hD0 hd (by positivity) (mul_le_mul_of_nonneg_right hj1 hl2.le)
        _ = 8 / Real.log 2 * D := by field_simp
    exact mul_le_mul (hback tc) hlog (pos_nonneg _) (by positivity))
  calc phi z s S ≤ k * B := hphi
    _ = _ := by rw [hB]; ring

/-! ## Arithmetic -/

/-- `k^3 / 4^k` is decreasing from `k = 22` on. -/
lemma cube_mul_four_pow_le {k : ℕ} (hk : 22 ≤ k) : k ^ 3 * 4 ^ 22 ≤ 22 ^ 3 * 4 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    have h2 : 22 * n ^ 2 ≤ n ^ 3 := by
      calc 22 * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right _ hn
        _ = n ^ 3 := by ring
    have h3 : n ≤ n ^ 2 := by nlinarith
    have h1 : (n + 1) ^ 3 ≤ 4 * n ^ 3 := by nlinarith
    calc (n + 1) ^ 3 * 4 ^ 22 ≤ 4 * n ^ 3 * 4 ^ 22 := Nat.mul_le_mul_right _ h1
      _ = 4 * (n ^ 3 * 4 ^ 22) := by ring
      _ ≤ 4 * (22 ^ 3 * 4 ^ n) := Nat.mul_le_mul_left _ ih
      _ = 22 ^ 3 * 4 ^ (n + 1) := by ring

lemma exp_neg_four_ninths_lt : Real.exp (-(4 / 9)) < 2 / 3 := by
  rw [Real.exp_neg]
  have h := Real.quadratic_le_exp_of_nonneg (x := 4 / 9) (by norm_num)
  have hpos : (0 : ℝ) < Real.exp (4 / 9) := Real.exp_pos _
  rw [inv_lt_comm₀ hpos (by norm_num)]
  linarith

/-- `τ_N` is exponentially smaller than `σ_N`: eventually `18 N² τ_N ≤ σ_N / 1000`. -/
lemma ev_tauN_small : ∀ᶠ N : ℕ in atTop, 18 * (N : ℝ) ^ 2 * tauN N ≤ 1e-3 * sigN N := by
  have hr0 : 0 ≤ Real.exp (-(4 / 9)) * (3 / 2) := by positivity
  have hr1 : Real.exp (-(4 / 9)) * (3 / 2) < 1 := by linarith [exp_neg_four_ninths_lt]
  filter_upwards [ev_poly_geom 4 hr0 hr1 1296 (by norm_num : (0 : ℝ) < 1e-6)] with N hN
  have hsq : tauN N ^ 2 = Real.exp (4 / 9) * Real.exp (-(4 / 9)) ^ N := by
    rw [tauN, sq, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; ring
  have h49 : Real.exp (4 / 9) ≤ 4 := by
    have := Real.exp_one_lt_d9
    have : Real.exp (4 / 9) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
    linarith
  have hsplit : Real.exp (-(4 / 9)) ^ N = (Real.exp (-(4 / 9)) * (3 / 2)) ^ N * (2 / 3 : ℝ) ^ N := by
    rw [← mul_pow]; congr 1; ring
  have hq0 : 0 ≤ (Real.exp (-(4 / 9)) * (3 / 2)) ^ N := by positivity
  have h23 : 0 ≤ (2 / 3 : ℝ) ^ N := by positivity
  have hsq' : (18 * (N : ℝ) ^ 2 * tauN N) ^ 2 ≤ (1e-3 * sigN N) ^ 2 := by
    rw [show (18 * (N : ℝ) ^ 2 * tauN N) ^ 2 = 324 * (N : ℝ) ^ 4 * tauN N ^ 2 by ring, hsq, hsplit,
      show (1e-3 * sigN N) ^ 2 = 1e-6 * sigN N ^ 2 by ring, sigN_sq]
    have e : 324 * (N : ℝ) ^ 4 * (Real.exp (4 / 9) *
        ((Real.exp (-(4 / 9)) * (3 / 2)) ^ N * (2 / 3 : ℝ) ^ N))
        = 324 * Real.exp (4 / 9) * ((N : ℝ) ^ 4 * (Real.exp (-(4 / 9)) * (3 / 2)) ^ N)
          * (2 / 3 : ℝ) ^ N := by ring
    rw [e]
    have hA : 324 * Real.exp (4 / 9) * ((N : ℝ) ^ 4 * (Real.exp (-(4 / 9)) * (3 / 2)) ^ N)
        ≤ 1e-6 := by
      have hm : 0 ≤ (N : ℝ) ^ 4 * (Real.exp (-(4 / 9)) * (3 / 2)) ^ N := by positivity
      have : 1296 * (N : ℝ) ^ 4 * (Real.exp (-(4 / 9)) * (3 / 2)) ^ N
          = 1296 * ((N : ℝ) ^ 4 * (Real.exp (-(4 / 9)) * (3 / 2)) ^ N) := by ring
      rw [this] at hN
      nlinarith
    exact mul_le_mul_of_nonneg_right hA h23
  exact le_of_pow_le_pow_left₀ two_ne_zero (by have := sigN_pos N; positivity) hsq'

/-- The envelope arithmetic: eventually, uniformly in `22 ≤ k ≤ KN N`, the cause-side bound with
the sharp deviation is below `cstar · sqrt (log N) · σ_N`. -/
theorem eventually_envelope_arith : ∀ᶠ N in atTop, ∀ k, 22 ≤ k → k ≤ KN N →
    (k : ℝ) * Real.exp 2 / 2 ^ k * (8 / Real.log 2) * Dev' N k
      < cstar * Real.sqrt (Real.log N) * sigN N := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, hlog.eventually_ge_atTop 3,
    ev_poly_geom 7 vkRate_pos.le vkRate_lt_one 1024 one_pos, ev_tauN_small]
    with N hN hx3 hρ hτ
  intro k hk22 hkK
  set x := Real.log N with hx
  have hσ := sigN_pos N
  have hτ0 := tauN_pos N
  have hx0 : 0 ≤ x := by linarith
  have hsx : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hsx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  have hk0 : (22 : ℝ) ≤ k := by exact_mod_cast hk22
  have hL0 := LkN_nonneg' k hN
  have hL : LkN N k ≤ 3 * k * x := by
    unfold LkN; rw [← hx]; nlinarith
  have hV := Vbd_le_seven hN hkK hρ
  have hV0 := Vbd_nonneg N k
  have hLN : LkN N k ≤ 18 * (N : ℝ) ^ 2 := by
    have hK := KN_le_six_mul hN
    have hk' : (k : ℝ) ≤ 6 * N := by exact_mod_cast hkK.trans hK
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hl1 : x ≤ N := Real.log_le_self (by positivity)
    have : 3 * (k : ℝ) * x ≤ 3 * (6 * N) * N := by gcongr
    nlinarith
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  set a : ℝ := (k : ℝ) / 2 ^ k with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one h2k]; exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  -- `a² k = k³ / 4^k ≤ 22³ / 4^22`
  have hak : a ^ 2 * k ≤ 22 ^ 3 / 4 ^ 22 := by
    have hc : (k : ℝ) ^ 3 * 4 ^ 22 ≤ 22 ^ 3 * 4 ^ k := by exact_mod_cast cube_mul_four_pow_le hk22
    have h4k : (0 : ℝ) < 4 ^ k := by positivity
    have e : a ^ 2 * k = (k : ℝ) ^ 3 / 4 ^ k := by
      rw [ha, div_pow, show (4 : ℝ) ^ k = (2 ^ k) ^ 2 by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      field_simp
    rw [e, div_le_div_iff₀ h4k (by positivity)]
    linarith
  have hs2 : 0 ≤ sigN N ^ 2 := by positivity
  -- the square-root parts
  have hA : a * Real.sqrt (LkN N k * Vbd N k) ≤ 1.2e-4 * Real.sqrt x * sigN N := by
    apply mul_sqrt_le_of_sq ha0 (by positivity)
    calc a ^ 2 * (LkN N k * Vbd N k) ≤ a ^ 2 * ((3 * k * x) * (7 * sigN N ^ 2)) := by gcongr
      _ = 21 * (a ^ 2 * k) * x * sigN N ^ 2 := by ring
      _ ≤ 21 * (22 ^ 3 / 4 ^ 22) * x * sigN N ^ 2 := by gcongr
      _ ≤ 1.44e-8 * x * sigN N ^ 2 := by gcongr; norm_num
      _ = (1.2e-4 * Real.sqrt x * sigN N) ^ 2 := by rw [mul_pow, mul_pow, hsx2]; norm_num
  have hB : a * Real.sqrt (6 * sigN N ^ 2 * LkN N k) ≤ 1.1e-4 * Real.sqrt x * sigN N := by
    apply mul_sqrt_le_of_sq ha0 (by positivity)
    calc a ^ 2 * (6 * sigN N ^ 2 * LkN N k) ≤ a ^ 2 * (6 * sigN N ^ 2 * (3 * k * x)) := by gcongr
      _ = 18 * (a ^ 2 * k) * x * sigN N ^ 2 := by ring
      _ ≤ 18 * (22 ^ 3 / 4 ^ 22) * x * sigN N ^ 2 := by gcongr
      _ ≤ 1.21e-8 * x * sigN N ^ 2 := by gcongr; norm_num
      _ = (1.1e-4 * Real.sqrt x * sigN N) ^ 2 := by rw [mul_pow, mul_pow, hsx2]; norm_num
  -- the linear part
  have hC : a * (tauN N * LkN N k) ≤ 1e-3 * Real.sqrt x * sigN N := by
    calc a * (tauN N * LkN N k) ≤ 1 * (tauN N * (18 * (N : ℝ) ^ 2)) := by gcongr
      _ = 18 * (N : ℝ) ^ 2 * tauN N := by ring
      _ ≤ 1e-3 * sigN N := hτ
      _ ≤ 1e-3 * Real.sqrt x * sigN N := by
          rw [mul_assoc]; gcongr; nlinarith
  have hDev : a * Dev' N k ≤ 6.65e-4 * Real.sqrt x * sigN N := by
    have e : a * Dev' N k = 4 * (a * Real.sqrt (LkN N k * Vbd N k))
        + (2 * (a * Real.sqrt (6 * sigN N ^ 2 * LkN N k)) + 2 * (a * (tauN N * LkN N k))) / 12 := by
      unfold Dev'; ring
    rw [e]
    have hsxσ : 0 ≤ Real.sqrt x * sigN N := by positivity
    nlinarith
  have hC0 : 0 ≤ Real.exp 2 * (8 / Real.log 2) := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have hrw : (k : ℝ) * Real.exp 2 / 2 ^ k * (8 / Real.log 2) * Dev' N k
      = (Real.exp 2 * (8 / Real.log 2)) * (a * Dev' N k) := by rw [ha]; ring
  rw [hrw]
  have hpos : 0 < Real.sqrt x * sigN N := by positivity
  have hy0 : 0 ≤ 6.65e-4 * Real.sqrt x * sigN N := by positivity
  calc (Real.exp 2 * (8 / Real.log 2)) * (a * Dev' N k)
      ≤ (Real.exp 2 * (8 / Real.log 2)) * (6.65e-4 * Real.sqrt x * sigN N) :=
        mul_le_mul_of_nonneg_left hDev hC0
    _ ≤ 100 * (6.65e-4 * Real.sqrt x * sigN N) := mul_le_mul_of_nonneg_right exp_two_mul_le hy0
    _ < cstar * Real.sqrt x * sigN N := by
        rw [cstar, mul_assoc, mul_assoc (9 / 100 : ℝ)]; nlinarith

/-! ## The envelope -/

/-- **Envelope.** Eventually in `N`, on the good event with the sharp deviation bound, every
candidate `S` with `22 ≤ |S| ≤ KN N` has `φ_s < cstar · sqrt (log N) · σ_N`. -/
theorem eventually_envelope : ∀ᶠ N in atTop, ∀ (s : State N) (z : Param N), z ∈ openCube N →
    GoodW N s (flipP s z) → gSharp N (flipP s z) → ∀ S : Finset (Fin N), 22 ≤ S.card →
    S.card ≤ KN N → phi z s S < cstar * Real.sqrt (Real.log N) * sigN N := by
  filter_upwards [eventually_ge_atTop 1, eventually_envelope_arith, eventually_levels,
    eventually_KN_le_K2N] with N hN hA hlev hK s z hz hG hSh S hS22 hSK
  refine (phi_le_rangeI' hz hG hN (by omega) (hlev _ (by omega) (hSK.trans hK.2))
    (Dev'_nonneg _ hN) fun j hj t => ?_).trans_lt (hA _ hS22 hSK)
  exact Num_diff_le' hG hSh hN hj (subset_refl S) (singleton_subset_iff.2 hj) t

end Census
end IIT
