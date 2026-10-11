/-
Census, module B1UnivMIP part 4: W3 Lemma 4.3 without the gap (W10 §1, (A) and (B_mid)).

At `S = univ` the cause numerator is a subcube mean times `Zs`, so
`λᶜⱼ(C) = log₂ (y_{t,j} / A_j(C))` with `A_j(C)` the mean of column `j` over the rows that agree
with `t` off `C`.  Subcube concentration `|A - 1/2| ≤ δ` then gives `λᶜⱼ(C) ≥ Fⱼ - 3(δ_{|C|} + δ_{N-1})`.
-/
import IIT.Census.B1UnivSys
import IIT.Census.B1KeyLemma

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- Mean of column `i` over the rows that agree with `t` on `Y` (a subcube of dimension `N - |Y|`). -/
noncomputable def cmean (w : Param N) (Y : Finset (Fin N)) (t : State N) (i : Fin N) : ℝ :=
  (∑ r ∈ agree Y t, clamp01 (w r i)) / (2 : ℝ) ^ (N - Y.card)

lemma Num_univ_eq (w : Param N) (Y : Finset (Fin N)) (t : State N) (i : Fin N) :
    Num w univ Y t i = cmean w Y t i * Zs w := by
  unfold Num meanW cmean Zs
  rw [mul_sum]
  refine sum_congr rfl fun v _ => ?_
  rw [compl_univ, union_empty, merge_univ, card_univ, Fintype.card_fin]

lemma cmean_univ (w : Param N) (t : State N) (i : Fin N) :
    cmean w univ t i = clamp01 (w t i) := by
  unfold cmean
  rw [prof_agree_univ, sum_singleton, card_univ, Fintype.card_fin, Nat.sub_self, pow_zero, div_one]

lemma cmean_pos {z : Param N} (hz : z ∈ openCube N) (s : State N) (Y : Finset (Fin N))
    (t : State N) (i : Fin N) : 0 < cmean (flipP s z) Y t i := by
  unfold cmean
  refine div_pos (sum_pos (fun r _ => ?_) (agree_nonempty _ _)) (by positivity)
  rw [← y_eq_clamp]; exact y_pos hz s r i

lemma cmean_le_one (w : Param N) (Y : Finset (Fin N)) (t : State N) (i : Fin N) :
    cmean w Y t i ≤ 1 := by
  unfold cmean
  rw [div_le_one (by positivity)]
  calc ∑ r ∈ agree Y t, clamp01 (w r i) ≤ ∑ _r ∈ agree Y t, (1 : ℝ) :=
        sum_le_sum fun r _ => clamp01_le_one _
    _ = (2 : ℝ) ^ (N - Y.card) := by
        rw [sum_const, nsmul_eq_mul, mul_one, card_agree]; push_cast; ring

/-- The cause-side term of Lemma V as a ratio of subcube means. -/
lemma lamCU_eq {z : Param N} (hz : z ∈ openCube N) (s t : State N) (C : Finset (Fin N))
    (j : Fin N) :
    lamCU (flipP s z) t C j =
      Real.logb 2 (clamp01 (flipP s z t j) / cmean (flipP s z) (univ \ C) t j) := by
  unfold lamCU
  rw [Num_univ_eq, Num_univ_eq, cmean_univ, mul_div_mul_right _ _ (Zs_pos hz s).ne']

/-- **The elementary bound behind (B_mid).** -/
lemma logb_ratio_ge {q A δq δA : ℝ} (hq : |q - 1 / 2| ≤ δq) (hA : |A - 1 / 2| ≤ δA)
    (hδq : δq ≤ 1 / 100) (hA0 : 0 < A) :
    -(3 * (δq + δA)) ≤ Real.logb 2 (q / A) := by
  have hq' := abs_le.1 hq
  have hA' := abs_le.1 hA
  have hq0 : 49 / 100 ≤ q := by linarith
  have hlog : (q - A) / q ≤ Real.log (q / A) := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos (by linarith) hA0)
    rw [inv_div] at this
    calc (q - A) / q = 1 - A / q := by field_simp
      _ ≤ _ := this
  have h1 : -((δq + δA) / (49 / 100)) ≤ (q - A) / q := by
    rw [neg_le, ← neg_div, neg_sub]
    calc (A - q) / q ≤ (δq + δA) / q := div_le_div_of_nonneg_right (by linarith) (by linarith)
      _ ≤ (δq + δA) / (49 / 100) := div_le_div_of_nonneg_left (by linarith) (by norm_num) hq0
  have hl2 : (69 / 100 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  unfold Real.logb
  rw [le_div_iff₀ (by linarith)]
  nlinarith [abs_nonneg (q - 1 / 2), abs_nonneg (A - 1 / 2)]

/-- Shifting the denominator from `q` to `A`. -/
lemma logb_shift {x q A δq δA : ℝ} (hx : 0 < x) (hq0 : 0 < q) (hA0 : 0 < A)
    (hq : |q - 1 / 2| ≤ δq) (hA : |A - 1 / 2| ≤ δA) (hδq : δq ≤ 1 / 100) :
    Real.logb 2 (x / q) - 3 * (δq + δA) ≤ Real.logb 2 (x / A) := by
  have h := logb_ratio_ge hq hA hδq hA0
  have : x / A = (x / q) * (q / A) := by field_simp
  rw [this, Real.logb_mul (div_pos hx hq0).ne' (div_pos hq0 hA0).ne']
  linarith

/-- `log₂(1/2 - δ) ≥ -1 - 3δ` for `0 ≤ δ ≤ 1/100`. -/
lemma logb_half_sub_ge {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 100) :
    -(1 + 3 * δ) ≤ Real.logb 2 (1 / 2 - δ) := by
  have hpos : 0 < 1 / 2 - δ := by linarith
  have hlog : 1 - (1 / 2 - δ)⁻¹ ≤ Real.log (1 / 2 - δ) := Real.one_sub_inv_le_log_of_pos hpos
  -- write `log(1/2 - δ) = -log 2 + log(1 - 2δ)` and bound the second term
  have hsplit : Real.log (1 / 2 - δ) = -Real.log 2 + Real.log (1 - 2 * δ) := by
    rw [show (1 / 2 - δ : ℝ) = (1 - 2 * δ) / 2 by ring, Real.log_div (by linarith) (by norm_num)]
    ring
  have h2 : 1 - (1 - 2 * δ)⁻¹ ≤ Real.log (1 - 2 * δ) :=
    Real.one_sub_inv_le_log_of_pos (by linarith)
  have h3 : -(2 * δ * (100 / 98)) ≤ 1 - (1 - 2 * δ)⁻¹ := by
    rw [show 1 - (1 - 2 * δ)⁻¹ = -(2 * δ) / (1 - 2 * δ) by
      have hne : (1 : ℝ) - 2 * δ ≠ 0 := by linarith
      rw [eq_div_iff hne, sub_mul, inv_mul_cancel₀ hne]; ring]
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ (by linarith)]
    nlinarith
  have hl2 : (69 / 100 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  unfold Real.logb
  rw [hsplit, le_div_iff₀ (by linarith)]
  nlinarith

/-- **Lemma 4.3 without the gap (W10).** A side whose terms are `λⱼ(C) = log₂(xⱼ / Aⱼ(C))`, with
`Aⱼ(∅) = xⱼ`, `0 < Aⱼ(C) ≤ 1` and the subcube concentration `|Aⱼ(C) - 1/2| ≤ δ_{|C|}` for big
cuts, satisfies the W10 hypotheses with `a = 1 + 3δ_{N-1}` and `ε_d = 3(δ_d + δ_{N-1})`, given the
threshold events. -/
theorem keyHyp_of_means {lam : Fin N → Finset (Fin N) → ℝ} {x : Fin N → ℝ}
    {A : Fin N → Finset (Fin N) → ℝ} {δ : ℕ → ℝ} {lmin : ℝ} {D dstar : ℕ}
    (hlam : ∀ j C, lam j C = Real.logb 2 (x j / A j C)) (hA_empty : ∀ j, A j ∅ = x j)
    (hx0 : ∀ j, 0 < x j) (hA0 : ∀ j C, 0 < A j C) (hA1 : ∀ j C, A j C ≤ 1)
    (hconc : ∀ j C, j ∉ C → D ≤ C.card → |A j C - 1 / 2| ≤ δ C.card)
    (hδ0 : ∀ d, 0 ≤ δ d) (hδs : δ (N - 1) ≤ 1 / 100)
    (hδanti : ∀ d d', D ≤ d → d ≤ d' → δ d' ≤ δ d)
    (hD : 1 ≤ D) (hDN : D ≤ N - 1) (hDd : 2 * D ≤ dstar)
    (hP : 0 < lmin) (hmin : ∀ j, lmin ≤ kF lam j)
    (hBfar : ∀ d, dstar ≤ d → d + 2 ≤ N →
      ((N : ℝ) - 1) * (3 * (δ d + δ (N - 1))) < lmin)
    (hS : ∀ A' : Finset (Fin N), A'.card < 2 * D →
      2 * D * ((1 + 3 * δ (N - 1)) + lmin) + N * (3 * (δ D + δ (N - 1))) <
        ∑ j ∈ A'ᶜ, (kF lam j - lmin))
    (hH : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < D →
      D * ((1 + 3 * δ (N - 1)) + 2 * lmin) + N * (3 * (δ D + δ (N - 1))) < kM lam lmin K)
    (hLS : ∀ Q : Finset (Fin N), N - dstar < Q.card →
      Q.card * (3 * (δ (2 * D) + δ (N - 1))) < ∑ j ∈ Q, (kF lam j - lmin)) :
    KeyHyp lam lmin (1 + 3 * δ (N - 1)) (fun d => 3 * (δ d + δ (N - 1))) D dstar := by
  have hfullcard : ∀ j : Fin N, (univ.erase j).card = N - 1 := fun j => by
    rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
  have hq : ∀ j, |A j (univ.erase j) - 1 / 2| ≤ δ (N - 1) := fun j => by
    have := hconc j (univ.erase j) (notMem_erase j univ) (by rw [hfullcard]; exact hDN)
    rwa [hfullcard] at this
  -- `x_j > q_j ≥ 1/2 - δ_{N-1}` from `F_j ≥ λ_min > 0`
  have hxq : ∀ j, 1 / 2 - δ (N - 1) ≤ x j := by
    intro j
    have hF : 0 < kF lam j := lt_of_lt_of_le hP (hmin j)
    unfold kF at hF
    rw [hlam] at hF
    have h1 : 1 < x j / A j (univ.erase j) := by
      by_contra h; push Not at h
      exact absurd hF (not_lt.2 (Real.logb_nonpos one_lt_two
        (div_pos (hx0 j) (hA0 j _)).le h))
    rw [one_lt_div (hA0 j _)] at h1
    have := (abs_le.1 (hq j)).1
    linarith
  refine
    { lam_empty := fun j => by rw [hlam, hA_empty, div_self (hx0 j).ne', Real.logb_one]
      hP := hP
      hmin := hmin
      ha := by have := hδ0 (N - 1); linarith
      hA := fun j C _ _ => by
        rw [hlam]
        have h1 : Real.logb 2 (x j) ≤ Real.logb 2 (x j / A j C) :=
          Real.logb_le_logb_of_le one_lt_two (hx0 j)
            ((le_div_iff₀ (hA0 j C)).2 (by nlinarith [hA1 j C, hx0 j]))
        have h2 : Real.logb 2 (1 / 2 - δ (N - 1)) ≤ Real.logb 2 (x j) :=
          Real.logb_le_logb_of_le one_lt_two (by linarith) (hxq j)
        have h3 := logb_half_sub_ge (hδ0 (N - 1)) hδs
        linarith
      hD := hD
      hDd := hDd
      hBmid := fun j C hjC hDC => by
        unfold kF
        rw [hlam, hlam]
        have := logb_shift (hx0 j) (hA0 j _) (hA0 j C) (hq j) (hconc j C hjC hDC) hδs
        linarith
      eps_nonneg := fun d => by have := hδ0 d; have := hδ0 (N - 1); positivity
      eps_anti := fun d d' hd hdd' => by have := hδanti d d' hd hdd'; linarith
      hBfar := hBfar
      hS := hS
      hH := hH
      hLS := hLS }

end Census
end IIT
