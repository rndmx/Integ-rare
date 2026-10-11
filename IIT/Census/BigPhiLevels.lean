/-
Census of complexes: algebra on the statistics behind the bound on `Φ` of the maximal complex.

Bounds on the variance proxy `Vp` (by `SQ2 + Xk` and by a block bound times `ZQ`), the identities
expressing differences of cause numerators through their centred parts and the differences of
their conditional means, a lower bound on `Num`, a multiplicative comparison of products with close
factors, and the elementary bound on `|log₂ (a / b)|₊`.
-/
import IIT.Census.BigPhiStats

namespace IIT
namespace Census

open Finset

variable {N : ℕ} {w : Param N} {i : Fin N} {S Y Y' : Finset (Fin N)} {t : State N} {k : ℕ}

/-! ## The variance proxy -/

lemma ham_self (r : State N) : ham r r = 0 := by
  simp [ham]

lemma agree_compl_subset_insert (r : State N) (hk : S.card ≤ k) :
    agree Sᶜ r ⊆ insert r (univ.filter fun r' => 1 ≤ ham r r' ∧ ham r r' ≤ k) := by
  intro r' hr'
  rw [mem_agree] at hr'
  by_cases h : r' = r
  · simp [h]
  · refine mem_insert_of_mem (mem_filter.2 ⟨mem_univ _, ?_, ?_⟩)
    · obtain ⟨j, hj⟩ := Function.ne_iff.1 (Ne.symm h)
      show 1 ≤ (univ.filter fun j => r j ≠ r' j).card
      exact Finset.card_pos.2 ⟨j, mem_filter.2 ⟨mem_univ _, hj⟩⟩
    · refine le_trans (card_le_card ?_) hk
      intro j hj
      rw [mem_filter] at hj
      by_contra hjS
      exact hj.2 (hr' j (mem_compl.2 hjS)).symm

/-- The variance proxy is at most the sum of squares plus the pair sum over Hamming distances
`1, …, k`, whenever `|S| ≤ k`. -/
theorem Vp_le_SQ2_add_Xk (hk : S.card ≤ k) : Vp w i S ≤ SQ2 w i + Xk w k i := by
  unfold Vp SQ2 Xk
  rw [← sum_add_distrib]
  refine sum_le_sum fun r _ => ?_
  have hnot : r ∉ univ.filter (fun r' => 1 ≤ ham r r' ∧ ham r r' ≤ k) := by
    simp [ham_self]
  calc Qw w i r * blockQ w i S r = ∑ r' ∈ agree Sᶜ r, Qw w i r * Qw w i r' := by
        rw [blockQ, subSum, mul_sum]
    _ ≤ ∑ r' ∈ insert r (univ.filter fun r' => 1 ≤ ham r r' ∧ ham r r' ≤ k),
          Qw w i r * Qw w i r' :=
        sum_le_sum_of_subset_of_nonneg (agree_compl_subset_insert r hk)
          fun _ _ _ => mul_nonneg (Qw_nonneg _ _ _) (Qw_nonneg _ _ _)
    _ = Qw w i r ^ 2 + ∑ r' ∈ univ.filter (fun r' => 1 ≤ ham r r' ∧ ham r r' ≤ k),
          Qw w i r * Qw w i r' := by
        rw [sum_insert hnot, sq]

/-- A uniform bound on the block masses bounds the variance proxy by that bound times `ZQ`. -/
theorem Vp_le_mul {B : ℝ} (hB : ∀ r, blockQ w i S r ≤ B) : Vp w i S ≤ B * ZQ w i := by
  unfold Vp ZQ
  rw [mul_sum]
  refine sum_le_sum fun r _ => ?_
  rw [mul_comm B]
  exact mul_le_mul_of_nonneg_left (hB r) (Qw_nonneg w i r)

/-! ## Differences of cause numerators -/

lemma cNum_sub_cNum : cNum w S Y t i - cNum w S Y' t i = DQ w S Y Y' t i / 12 := by
  unfold cNum DQ
  ring

/-- The difference of two cause numerators with purviews `Y, Y' ⊆ S`: the two centred parts plus
the difference of the conditional means. -/
theorem Num_sub_Num (_hY : Y ⊆ S) (_hY' : Y' ⊆ S) : Num w S Y t i - Num w S Y' t i =
    (Num w S Y t i - cNum w S Y t i) - (Num w S Y' t i - cNum w S Y' t i)
      + DQ w S Y Y' t i / 12 := by
  have := cNum_sub_cNum (w := w) (S := S) (Y := Y) (Y' := Y') (t := t) (i := i)
  linarith

/-- The difference of the full-purview cause numerators at two purview states. -/
theorem Num_S_sub (t t' : State N) : Num w S S t i - Num w S S t' i =
    (Num w S S t i - cNum w S S t i) - (Num w S S t' i - cNum w S S t' i)
      + (subSum w i S t - subSum w i S t') / 12 := by
  unfold cNum
  simp only [Nat.sub_self, pow_zero, mul_one]
  ring

/-- A lower bound on a cause numerator from the bounds on `Zs`, on `Zs - ZQ/2`, and on the centred
part. -/
theorem Num_lower {d e : ℝ} (hZ : 1 / 2 ≤ Zs w) (h11 : |Zs w - ZQ w i / 2| ≤ e)
    (hdev : |Num w S Y t i - cNum w S Y t i| ≤ d) (hsmall : e / 2 + d ≤ 1 / 8)
    (hsub : 0 ≤ subSum w i Y t) : Zs w / 4 ≤ Num w S Y t i := by
  have hterm : 0 ≤ subSum w i Y t / (12 * (2 : ℝ) ^ (S.card - Y.card)) :=
    div_nonneg hsub (by positivity)
  have h1 := (abs_le.1 h11).2
  have h2 := (abs_le.1 hdev).1
  unfold cNum at h2
  linarith

/-! ## Products with close factors -/

/-- Products of factors bounded below by `1/8` and close in total deviation differ by at most the
factor `e²`. -/
theorem prod_le_exp_mul_prod {ι : Type*} (S : Finset ι) (a b : ι → ℝ) (δ : ι → ℝ)
    (ha : ∀ i ∈ S, 1 / 8 ≤ a i) (hb : ∀ i ∈ S, 1 / 8 ≤ b i)
    (hd : ∀ i ∈ S, |a i - b i| ≤ δ i) (hsum : ∑ i ∈ S, 8 * δ i ≤ 2) :
    ∏ i ∈ S, a i ≤ Real.exp 2 * ∏ i ∈ S, b i := by
  have hstep : ∀ i ∈ S, a i ≤ b i * Real.exp (8 * δ i) := by
    intro i hi
    have hδ : 0 ≤ δ i := le_trans (abs_nonneg _) (hd i hi)
    have hab := (abs_le.1 (hd i hi)).2
    have hexp := Real.add_one_le_exp (8 * δ i)
    have hbi := hb i hi
    nlinarith [mul_le_mul_of_nonneg_left hexp (by linarith : (0 : ℝ) ≤ b i)]
  calc ∏ i ∈ S, a i ≤ ∏ i ∈ S, (b i * Real.exp (8 * δ i)) :=
        prod_le_prod (fun i hi => by linarith [ha i hi]) hstep
    _ = (∏ i ∈ S, b i) * Real.exp (∑ i ∈ S, 8 * δ i) := by
        rw [prod_mul_distrib, Real.exp_sum]
    _ ≤ (∏ i ∈ S, b i) * Real.exp 2 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hsum)
          (prod_nonneg fun i hi => by linarith [hb i hi])
    _ = Real.exp 2 * ∏ i ∈ S, b i := mul_comm _ _

/-! ## Logarithms of ratios -/

/-- `|log₂ (a / b)|₊ ≤ |a - b| / (b ln 2)` for positive `a, b`. -/
theorem pos_logb_div_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    pos (Real.logb 2 (a / b)) ≤ |a - b| / (b * Real.log 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hden : 0 < b * Real.log 2 := mul_pos hb hl2
  refine max_le (div_nonneg (abs_nonneg _) hden.le) ?_
  have hlog : Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
  have heq : a / b - 1 = (a - b) / b := by field_simp
  rw [Real.logb, div_le_div_iff₀ hl2 hden]
  have h1 : Real.log (a / b) * b ≤ a - b := by
    have := mul_le_mul_of_nonneg_right hlog hb.le
    rw [heq, div_mul_cancel₀ _ hb.ne'] at this
    exact this
  have h2 : a - b ≤ |a - b| := le_abs_self _
  nlinarith
