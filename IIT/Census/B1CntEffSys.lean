/-
Census, B1, W14 work package WP3 (effect side, deterministic), part 1: the system effect state
(W9 Lemma TE', `SysEffStmt`), the split of `effRest` into fresh and sensitive rows, and the
deviation bounds `eff_subDev`, `eff_colDev` (W5 FE1' and (C) for the te-oriented columns).
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

/-! ### Small facts on `pTe`, `rowTX` -/

lemma pTe_nonneg' (w : Param N) (s r : State N) (k : Fin N) : 0 ≤ pTe w s r k := by
  unfold pTe; split_ifs
  · exact clamp01_nonneg _
  · linarith [clamp01_le_one (w r k)]

lemma pTe_le_one' (w : Param N) (s r : State N) (k : Fin N) : pTe w s r k ≤ 1 := by
  unfold pTe; split_ifs
  · exact clamp01_le_one _
  · linarith [clamp01_nonneg (w r k)]

lemma rowTX_nonneg (w : Param N) (s r t : State N) : 0 ≤ rowTX w s r t := by
  unfold rowTX
  refine prod_nonneg fun k _ => ?_
  split_ifs
  · exact clamp01_nonneg _
  · linarith [clamp01_le_one (w r k)]

/-! ### The split of `effRest` -/

theorem effRest_split (w : Param N) (s r0 t : State N) :
    effRest (tpmOf (flipP s w)) s t =
      ∑ r ∈ freshRows s r0, rowTX w s r t + ∑ r ∈ (sensRows s r0).erase s, rowTX w s r t := by
  have hU : univ.erase s = freshRows s r0 ∪ (sensRows s r0).erase s := by
    ext r
    simp only [mem_erase, mem_univ, and_true, mem_union, freshRows, mem_filter, true_and]
    constructor
    · intro h
      by_cases hr : r ∈ sensRows s r0
      · exact Or.inr ⟨h, hr⟩
      · exact Or.inl hr
    · rintro (h | ⟨h, _⟩)
      · intro hrs; rw [hrs] at h; exact h (mem_sensRows_s s r0)
      · exact h
  have hD : Disjoint (freshRows s r0) ((sensRows s r0).erase s) := by
    rw [disjoint_left]
    intro r h1 h2
    simp only [freshRows, mem_filter] at h1
    exact h1.2 (mem_of_mem_erase h2)
  unfold effRest
  rw [hU, sum_union hD]
  simp only [fullProb_flipP]

/-! ### Asymptotic facts for Lemma TE' -/

lemma sigN_sq' (N : ℕ) : sigN N ^ 2 = (2 / 3 : ℝ) ^ N := by
  unfold sigN; rw [Real.sq_sqrt (by positivity)]

lemma sigN_le_one'' (N : ℕ) : sigN N ≤ 1 :=
  Real.sqrt_le_one.mpr (pow_le_one₀ (by norm_num) (by norm_num))

lemma ev_te_consts : ∀ᶠ N : ℕ in atTop,
    100 ≤ N ∧ 2 * (N : ℝ) ^ 4 / 2 ^ N ≤ sigN N ∧ sigN N ≤ 1 / 4 ∧
      2 * Real.sqrt N * sigN N ≤ 1 / 4 ∧ Real.exp ((N : ℝ) / 100) * sigN N ≤ 1 / 2 := by
  filter_upwards [eventually_ge_atTop 100,
    ev_poly_geom 4 (r := 3 / 4) (by norm_num) (by norm_num) 2 (ε := 1) one_pos,
    ev_pow_mul_sigN 0 (C := 1) zero_le_one (ε := 1 / 4) (by norm_num),
    ev_pow_mul_sigN 1 (C := 2) zero_le_two (ε := 1 / 4) (by norm_num)] with N hN h4 h0 h1
  have hσ0 : 0 ≤ sigN N := (sigN_pos N).le
  have hσ1 := sigN_le_one'' N
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  refine ⟨hN, ?_, by simpa using h0, ?_, ?_⟩
  · have e1 : (2 : ℝ) * (N : ℝ) ^ 4 / 2 ^ N = 2 * (N : ℝ) ^ 4 * (3 / 4 : ℝ) ^ N * (2 / 3 : ℝ) ^ N := by
      rw [mul_assoc (2 * (N : ℝ) ^ 4), ← mul_pow,
        show (3 / 4 : ℝ) * (2 / 3) = (2 : ℝ)⁻¹ by norm_num, inv_pow, div_eq_mul_inv]
    rw [e1, ← sigN_sq']
    have hp : 0 ≤ 2 * (N : ℝ) ^ 4 * (3 / 4 : ℝ) ^ N := by positivity
    calc 2 * (N : ℝ) ^ 4 * (3 / 4 : ℝ) ^ N * sigN N ^ 2 ≤ 1 * sigN N ^ 2 :=
          mul_le_mul_of_nonneg_right h4.le (by positivity)
      _ ≤ sigN N := by nlinarith
  · have hs : Real.sqrt N ≤ N := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
    have : 2 * Real.sqrt N * sigN N ≤ 2 * (N : ℝ) ^ 1 * sigN N := by
      rw [pow_one]; gcongr
    linarith
  · rw [sigN_eq_exp, ← Real.exp_add]
    have hx := x0_gt
    have hle : (N : ℝ) / 100 + -(x0 * N) ≤ -((N : ℝ) / 10) := by nlinarith
    have h10 : (2 : ℝ) ≤ Real.exp ((N : ℝ) / 10) := by
      have := Real.add_one_le_exp ((N : ℝ) / 10)
      have : (100 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    calc Real.exp ((N : ℝ) / 100 + -(x0 * N)) ≤ Real.exp (-((N : ℝ) / 10)) := Real.exp_le_exp.2 hle
      _ = 1 / Real.exp ((N : ℝ) / 10) := by rw [Real.exp_neg, one_div]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le two_pos h10

/-! ### Lemma TE' -/

theorem sysEff_proved : SysEffStmt := by
  filter_upwards [ev_te_consts] with N hc s r0 x σ w hg hfr
  obtain ⟨hN, hA, hσq, hσs, hE⟩ := hc
  have hz := cnt_flipP_open hg hfr
  set T := tpmOf (flipP s w) with hT
  have hpos : ∀ i r b, 0 < T.prob i r b := prob_pos hz
  have hne : (univ : Finset (Fin N)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  set σN := sigN N with hσN
  have hσ0 : 0 < σN := sigN_pos N
  set E := Real.exp ((N : ℝ) / 100) * σN with hEdef
  have hE1 : σN ≤ E := le_mul_of_one_le_left hσ0.le (Real.one_le_exp (by positivity))
  set μ := univ.inf' hne (fun k => xE w s k - 1 / 2) with hμdef
  have hμ0 : E ≤ μ := hg.1.sRowMu' hne
  have hμ : 0 < μ := lt_of_lt_of_le (lt_of_lt_of_le hσ0 hE1) hμ0
  have hx : ∀ k, 1 / 2 + μ ≤ T.prob k s (teW w s k) := by
    intro k
    rw [hT, prob_flipP_teW, ← xE_eq_pTe]
    have := inf'_le (fun k => xE w s k - 1 / 2) (mem_univ k)
    rw [← hμdef] at this
    linarith
  have he : (2 : ℝ) ^ (-((N : ℝ) / 2)) ≤ fullProb T s (teW w s) := by
    rw [hT, fullProb_flipP, rowTX_teW]
    have h := hg.1.sRowE
    unfold eE at h
    simp only [xE_eq_pTe] at h
    rwa [neg_div] at h
  -- the two parts of `effRest`
  have hsens_nn : ∀ t, 0 ≤ ∑ r ∈ (sensRows s r0).erase s, rowTX w s r t :=
    fun t => sum_nonneg fun r _ => rowTX_nonneg w s r t
  have hsens_te : ∑ r ∈ (sensRows s r0).erase s, rowTX w s r (teW w s) ≤ σN := by
    simp only [rowTX_teW]; exact hg.1.sRowR
  have hlow : ∀ t, 1 - 2 * (N : ℝ) ^ 4 / 2 ^ N - 2 * Real.sqrt N * σN ≤ effRest T s t := by
    intro t
    rw [hT, effRest_split w s r0 t]
    have h7 := hfr.fe7a
    unfold FE7aX at h7
    linarith [h7 t, hsens_nn t]
  have hup : effRest T s (teW w s) ≤ 1 + E + σN := by
    rw [hT, effRest_split w s r0 (teW w s)]
    have h7 := hfr.fe7b
    unfold FE7bX at h7
    linarith
  set ν := E + σN + 2 * (N : ℝ) ^ 4 / 2 ^ N + 2 * Real.sqrt N * σN with hν
  have hAnn : 0 ≤ 2 * (N : ℝ) ^ 4 / 2 ^ N := by positivity
  have hsq0 : 0 ≤ 2 * Real.sqrt N * σN := by positivity
  refine sysMaxEffStates_univ_eq_of T s hpos (teW w s) (ν := ν) hμ hx he ?_ ?_ ?_ ?_ ?_
  · intro t; linarith [hlow t]
  · linarith
  · intro t; linarith [hlow t]
  · positivity
  · -- `3 ν < μ (N - 10)`
    have hN' : (100 : ℝ) ≤ N := by exact_mod_cast hN
    have hs : Real.sqrt N ≤ (N : ℝ) / 10 := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
    have h1 : 2 * Real.sqrt N * σN ≤ 2 * Real.sqrt N * E :=
      mul_le_mul_of_nonneg_left hE1 (by positivity)
    have h2 : 2 * Real.sqrt N * E ≤ 2 * ((N : ℝ) / 10) * E :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h3 : E * ((N : ℝ) - 10) ≤ μ * ((N : ℝ) - 10) :=
      mul_le_mul_of_nonneg_right hμ0 (by linarith)
    have hEp : 0 < E := lt_of_lt_of_le hσ0 hE1
    nlinarith

/-! ### Deviations of the te-oriented columns (W5 FE1', (C)) -/

lemma effDevA_abs (w : Param N) (s : State N) (A : Finset (Fin N)) (t : State N) (k : Fin N) :
    |effDevA w s A t k| = |subMean w A t k - 1 / 2| := by
  have hc : ((agree A t).card : ℝ) ≠ 0 := (Nat.cast_pos.2 (card_agree_pos A t)).ne'
  have hm : subMean w A t k - 1 / 2 =
      (∑ r ∈ agree A t, (clamp01 (w r k) - 1 / 2)) / (agree A t).card := by
    unfold subMean
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
    field_simp
  rw [hm]
  unfold effDevA pTe
  by_cases h : 1 / 2 < clamp01 (w s k)
  · simp only [h, if_true]
  · simp only [h, if_false]
    rw [show (∑ r ∈ agree A t, (1 - clamp01 (w r k) - 1 / 2)) =
        -∑ r ∈ agree A t, (clamp01 (w r k) - 1 / 2) by
      rw [← sum_neg_distrib]; exact sum_congr rfl fun r _ => by ring,
      neg_div, abs_neg]

theorem eff_subDev : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N),
    GoodW3 N s r0 x σ w → CountFreshX N s r0 w →
      ∀ (A : Finset (Fin N)) (t : State N) (k : Fin N), A.card + D0C N ≤ N →
        |effDevA w s A t k| ≤ 2 * Real.sqrt ((N : ℝ) / 2 ^ (N - A.card)) +
          2 * ((N - A.card + 1 : ℕ) : ℝ) ^ 4 / 2 ^ (N - A.card) := by
  filter_upwards [cnt_subDev] with N h s r0 x σ w hg hfr A t k hA
  rw [effDevA_abs]
  exact h s r0 x σ w hg hfr A t k hA

theorem eff_colDev : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N),
    GoodW3 N s r0 x σ w → CountFreshX N s r0 w → ∀ (t : State N) (k : Fin N),
      |effDevA w s ∅ t k| ≤ epsN N := by
  filter_upwards [cnt_colDev] with N h s r0 x σ w hg hfr t k
  rw [effDevA_abs]
  exact h s r0 x σ w hg hfr t k

end WP3

alias effRest_split := WP3.effRest_split
alias sysEff_proved := WP3.sysEff_proved
alias eff_subDev := WP3.eff_subDev
alias eff_colDev := WP3.eff_colDev

end Census
end IIT

#print axioms IIT.Census.sysEff_proved
#print axioms IIT.Census.eff_subDev
#print axioms IIT.Census.eff_colDev
