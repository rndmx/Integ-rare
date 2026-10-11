/-
Census of complexes: the deterministic bounds on `φ_s` and `Φ` on the good event.

On the good event `GoodW` (for the flipped parameters `flipP s z`), eventually in `N`:
* `detA`: every candidate larger than the threshold `KN N` has `φ_s < σ_N / 128`.  Intermediate
  sizes use the cause side (the cause numerators are all close to each other, so the backward cause
  distribution is nearly uniform and the cause ratio at a single-unit split is close to one); sizes
  near the whole substrate use the effect side.
* `detB`: every candidate of size at most `KN N` has `Φ ≤ rateN N` for every selector.
-/
import IIT.Census.BigPhiMech
import IIT.Census.BigPhiSys
import IIT.Census.BigPhiLevels
import IIT.Census.BigPhiArith

namespace IIT
namespace Census

open Finset Filter Topology

variable {N : ℕ}

/-! ## Deviation bounds on the good event -/

lemma card_le_N (S : Finset (Fin N)) : S.card ≤ N := by
  simpa using Finset.card_le_univ S

/-- The variance proxy is at most `Vbd N |S|`. -/
lemma Vp_le_Vbd {s : State N} {w : Param N} (hG : GoodW N s w) (i : Fin N) (S : Finset (Fin N)) :
    Vp w i S ≤ Vbd N S.card :=
  (Vp_le_SQ2_add_Xk le_rfl).trans (add_le_add (hG.g4 i) (hG.g12 S.card i))

/-- The centred part of a numerator is at most `dsmall N |S|`. -/
lemma dev_le_dsmall {s : State N} {w : Param N} (hG : GoodW N s w) (hN : 1 ≤ N)
    {S Y : Finset (Fin N)} {i : Fin N} (hi : i ∈ S) (hY : Y ⊆ S) (t : State N) :
    |Num w S Y t i - cNum w S Y t i| ≤ dsmall N S.card := by
  refine (hG.g13a S i Y t hi hY).trans ?_
  unfold dsmall
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left (Vp_le_Vbd hG i S) (LkN_nonneg' _ hN))) (by norm_num)

/-- Two numerators of the same unit with purviews inside `S` differ by at most `Dev N |S|`. -/
lemma Num_diff_le {s : State N} {w : Param N} (hG : GoodW N s w) (hN : 1 ≤ N)
    {S Y Y' : Finset (Fin N)} {i : Fin N} (hi : i ∈ S) (hY : Y ⊆ S) (hY' : Y' ⊆ S) (t : State N) :
    |Num w S Y t i - Num w S Y' t i| ≤ Dev N S.card := by
  rw [Num_sub_Num hY hY']
  have h1 := dev_le_dsmall hG hN hi hY t
  have h2 := dev_le_dsmall hG hN hi hY' t
  have h3 := hG.g13b S i Y Y' t hi hY hY'
  have habs : |(Num w S Y t i - cNum w S Y t i) - (Num w S Y' t i - cNum w S Y' t i)
      + DQ w S Y Y' t i / 12| ≤ |Num w S Y t i - cNum w S Y t i|
        + |Num w S Y' t i - cNum w S Y' t i| + |DQ w S Y Y' t i| / 12 := by
    have := abs_add_le ((Num w S Y t i - cNum w S Y t i) - (Num w S Y' t i - cNum w S Y' t i))
      (DQ w S Y Y' t i / 12)
    have h4 := abs_sub (Num w S Y t i - cNum w S Y t i) (Num w S Y' t i - cNum w S Y' t i)
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 12)] at this
    linarith
  unfold Dev
  unfold dsmall at h1 h2
  linarith

/-- The mass of a `k`-dimensional block of rows is at most `Mk N k`. -/
lemma blockQ_le_Mk {s : State N} {w : Param N} (hG : GoodW N s w) (i : Fin N)
    (S : Finset (Fin N)) (r : State N) : blockQ w i S r ≤ Mk N S.card := by
  have h := hG.g6 i Sᶜ r
  have hc : N - Sᶜ.card = S.card := by
    rw [card_compl, Fintype.card_fin]; exact Nat.sub_sub_self (card_le_N S)
  rw [hc] at h
  exact h

lemma Mk_nonneg (N k : ℕ) : 0 ≤ Mk N k := by
  have := tauN_pos N
  unfold Mk; positivity

/-- For intermediate sizes the centred part of a numerator is at most `dlev N |S|`. -/
lemma dev_le_dlev {s : State N} {w : Param N} (hG : GoodW N s w) (hN : 1 ≤ N)
    {S Y : Finset (Fin N)} {i : Fin N} (hi : i ∈ S) (hY : Y ⊆ S) (t : State N) :
    |Num w S Y t i - cNum w S Y t i| ≤ dlev N S.card := by
  refine (hG.g13a S i Y t hi hY).trans ?_
  have hV : Vp w i S ≤ 3 * Mk N S.card := by
    refine (Vp_le_mul (blockQ_le_Mk hG i S)).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hG.g3.2.2 i) (Mk_nonneg _ _)
  unfold dlev
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left hV (LkN_nonneg' _ hN))) (by norm_num)

/-- The `Qw`-mass of an `(N - k)`-dimensional subcube is at most `(1/2)^(k-1) + E6 N k`. -/
lemma subSum_S_le {s : State N} {w : Param N} (hG : GoodW N s w) (i : Fin N)
    {S : Finset (Fin N)} (hS : 1 ≤ S.card) (t : State N) :
    subSum w i S t ≤ (1 / 2 : ℝ) ^ (S.card - 1) + E6 N S.card := by
  have h := hG.g6 i S t
  have hk := card_le_N S
  have hsplit : (1 / 2 : ℝ) ^ (N - 1) = (1 / 2 : ℝ) ^ (N - S.card) * (1 / 2 : ℝ) ^ (S.card - 1) := by
    rw [← pow_add]; congr 1; omega
  have heq : (2 : ℝ) ^ (N - S.card) * (1 / 2 : ℝ) ^ (N - 1) = (1 / 2 : ℝ) ^ (S.card - 1) := by
    rw [hsplit, ← mul_assoc, ← mul_pow]; norm_num
  rw [heq] at h
  unfold E6
  linarith

/-! ## Large candidates -/

/-- Cause side for intermediate sizes: `φ_s` is at most `|S| e² / 2^|S| · (8 / ln 2) · Dev`. -/
lemma phi_le_rangeI {s : State N} {z : Param N} (hz : z ∈ openCube N)
    (hG : GoodW N s (flipP s z)) (hN : 1 ≤ N) {S : Finset (Fin N)} (hk2 : 2 ≤ S.card)
    (hlev : 16 * N * sigN N / 2 + dlev N S.card ≤ 1 / 8 ∧
      (S.card : ℝ) * 8 * (((1 / 2 : ℝ) ^ (S.card - 1) + E6 N S.card) / 12
        + 2 * dlev N S.card) ≤ 2) :
    phi z s S ≤ (S.card : ℝ) * Real.exp 2 / 2 ^ S.card * (8 / Real.log 2) * Dev N S.card := by
  set w := flipP s z with hw
  set k := S.card with hkdef
  obtain ⟨j, hj⟩ : S.Nonempty := card_pos.1 (by omega)
  have hZ := hG.g3.1
  have hZpos : 0 < Zs w := Zs_pos hz s
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- lower bound on every numerator
  have hlow : ∀ i ∈ S, ∀ Y ⊆ S, ∀ t, 1 / 8 ≤ Num w S Y t i := by
    intro i hi Y hY t
    have := Num_lower hZ (hG.g11 i) (dev_le_dlev hG hN hi hY t) hlev.1 (subSum_nonneg w i Y t)
    linarith
  -- the backward cause distribution is nearly uniform
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
  -- the cause ratio at the split `{j} | S \ {j}`
  have hDev0 : 0 ≤ Dev N k := Dev_nonneg k hN
  set B : ℝ := Real.exp 2 / 2 ^ k * (8 / Real.log 2 * Dev N k) with hB
  have hB0 : 0 ≤ B := by positivity
  have hphi := phi_le_cause hz hk2 hj hB0 (B := B) (fun tc => by
    have hlog : pos (Real.logb 2 (Num w S S tc j / Num w S {j} tc j)) ≤ 8 / Real.log 2 * Dev N k := by
      have hj1 := hlow j hj {j} (singleton_subset_iff.2 hj) tc
      refine (pos_logb_div_le (Num_pos hz s S S tc j) (by linarith)).trans ?_
      have hd := Num_diff_le hG hN hj (subset_refl S) (singleton_subset_iff.2 hj) tc
      calc |Num w S S tc j - Num w S {j} tc j| / (Num w S {j} tc j * Real.log 2)
          ≤ Dev N k / (1 / 8 * Real.log 2) :=
            div_le_div₀ hDev0 hd (by positivity) (mul_le_mul_of_nonneg_right hj1 hl2.le)
        _ = 8 / Real.log 2 * Dev N k := by field_simp
    exact mul_le_mul (hback tc) hlog (pos_nonneg _) (by positivity))
  calc phi z s S ≤ k * B := hphi
    _ = _ := by rw [hB]; ring

/-- **Large candidates.** Eventually in `N`, on the good event every candidate larger than the
threshold `KN N` has `φ_s < σ_N / 128`. -/
theorem detA : ∀ᶠ N in atTop, ∀ (s : State N) (z : Param N), z ∈ openCube N →
    GoodW N s (flipP s z) → ∀ S : Finset (Fin N), KN N < S.card → phi z s S < sigN N / 128 := by
  filter_upwards [eventually_ge_atTop 1, eventually_rangeI, eventually_levels, eventually_rangeII,
    eventually_KN_le_K2N] with N hN hI hlev hII hK s z hz hG S hS
  have hkN := card_le_N S
  obtain ⟨j, hj⟩ : S.Nonempty := card_pos.1 (by omega)
  by_cases h2 : S.card ≤ K2N N
  · exact (phi_le_rangeI hz hG hN (by omega) (hlev _ (by omega) h2)).trans_lt (hI _ hS hkN)
  · rw [not_le] at h2
    refine lt_of_le_of_lt (phi_le_eff hz (by omega) hj fun b => hG.g16 S j b hj h2) ?_
    refine lt_of_le_of_lt ?_ (hII _ h2 hkN)
    gcongr
    exact hG.gU

/-! ## Small candidates -/

/-- **Small candidates.** Eventually in `N`, on the good event every candidate of size at most
`KN N` has `Φ ≤ rateN N`, for every selector. -/
theorem detB : ∀ᶠ N in atTop, ∀ (s : State N) (z : Param N), z ∈ openCube N →
    GoodW N s (flipP s z) → ∀ S : Finset (Fin N), S.card ≤ KN N →
      ∀ σ' : SelectorAt (tpmOf z) S s s, PhiOfAt (tpmOf z) S s s σ' ≤ rateN N := by
  filter_upwards [eventually_ge_atTop 1, eventually_small, eventually_rateB]
    with N hN hsmall hrate s z hz hG S hS σ'
  set w := flipP s z with hw
  set k := S.card with hkdef
  have hZ := hG.g3.1
  have hZpos : 0 < Zs w := Zs_pos hz s
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hDev0 : 0 ≤ Dev N k := Dev_nonneg k hN
  have hlow : ∀ i ∈ S, ∀ Y ⊆ S, ∀ t, 1 / 8 ≤ Num w S Y t i := by
    intro i hi Y hY t
    have := Num_lower hZ (hG.g11 i) (dev_le_dsmall hG hN hi hY t) (hsmall k hS)
      (subSum_nonneg w i Y t)
    linarith
  have hB0 : 0 ≤ (k : ℝ) * (8 / Real.log 2) * Dev N k := by positivity
  refine (PhiOfAt_le_of_ratio (tpmOf z) S s s σ' hB0 fun M hM Z hZS zz θ => ?_).trans
    (hrate k hS)
  rw [causeFwdAt_eq z s hZS zz M, partCauseFwdAt_eq z s zz θ hZS, ← hw]
  have hY : ∀ i, θ.causePart i ⊆ S := fun i => (θ.causePart_subset i).trans hZS
  refine (pos_logb_prod_div_le M _ _ (fun i _ => div_pos (Num_pos hz s S Z zz i) hZpos)
    (fun i _ => div_pos (Num_pos hz s S _ zz i) hZpos)).trans ?_
  have hterm : ∀ i ∈ M, |Num w S Z zz i / Zs w - Num w S (θ.causePart i) zz i / Zs w|
      / (Num w S (θ.causePart i) zz i / Zs w * Real.log 2) ≤ 8 / Real.log 2 * Dev N k := by
    intro i hi
    have hiS := hM hi
    have hY1 := hlow i hiS _ (hY i) zz
    have hd := Num_diff_le hG hN hiS hZS (hY i) zz
    have heq : |Num w S Z zz i / Zs w - Num w S (θ.causePart i) zz i / Zs w|
        / (Num w S (θ.causePart i) zz i / Zs w * Real.log 2)
        = |Num w S Z zz i - Num w S (θ.causePart i) zz i|
          / (Num w S (θ.causePart i) zz i * Real.log 2) := by
      rw [← sub_div, abs_div, abs_of_pos hZpos, div_mul_eq_mul_div, div_div_div_cancel_right₀
        hZpos.ne']
    rw [heq]
    calc |Num w S Z zz i - Num w S (θ.causePart i) zz i|
          / (Num w S (θ.causePart i) zz i * Real.log 2)
        ≤ Dev N k / (1 / 8 * Real.log 2) :=
          div_le_div₀ hDev0 hd (by positivity) (mul_le_mul_of_nonneg_right hY1 hl2.le)
      _ = 8 / Real.log 2 * Dev N k := by field_simp
  calc ∑ i ∈ M, |Num w S Z zz i / Zs w - Num w S (θ.causePart i) zz i / Zs w|
        / (Num w S (θ.causePart i) zz i / Zs w * Real.log 2)
      ≤ ∑ _i ∈ M, 8 / Real.log 2 * Dev N k := sum_le_sum hterm
    _ = (M.card : ℝ) * (8 / Real.log 2 * Dev N k) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (k : ℝ) * (8 / Real.log 2 * Dev N k) := by
        gcongr
        exact card_le_card hM
    _ = (k : ℝ) * (8 / Real.log 2) * Dev N k := by ring

end Census
end IIT
