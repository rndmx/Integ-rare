/-
Census, B1 lemma LT2, module M6d-3b: one adverse-count bound per statistic type, eventually `≤ 2 e^{-3N}`.

Hypotheses on the index set `P` (pairs or units) and the threshold `m'`: `|P| ≤ 12288 m'`, `N/491520 ≤ m' ≤ N²`,
`|P| ≤ N²`; the level is `κσ` with `κ = 2500`.
-/
import IIT.Census.B1LT2Asym

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- The level constant. -/
def lt2κ : ℝ := 2500

lemma lt2_logc : Real.log (2 * Real.exp 1 * 12288) ≤ 12 := by
  have h1 : Real.log (2 * Real.exp 1 * 12288) = Real.log 2 + 1 + Real.log 12288 := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_mul (by norm_num) (by positivity), Real.log_exp]
  rw [h1]
  have h2 : Real.log 12288 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have h27 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have := pow_le_pow_left₀ (by norm_num) h27 10
    rw [he]; norm_num at this ⊢; linarith
  linarith [Real.log_two_lt_d9]

lemma lt2_sig_div_theta (N : ℕ) : sigN N / lt2θ N = Real.exp ((N : ℝ) / 400) := by
  rw [sigN_eq_exp, lt2θ, lt2x1, ← Real.exp_sub]; congr 1; ring

/-- The eventual facts used for every kind. -/
lemma lt2_ev_kind : ∀ᶠ N : ℕ in atTop,
    (3 * (N : ℝ) + (N : ℝ) ^ 2 * 12 ≤ lt2κ * sigN N / (4 * lt2θ N)) ∧ 8 * (1 / 2 : ℝ) ^ N ≤ lt2tG N ∧
    (1 : ℝ) ≤ N := by
  filter_upwards [eventually_ge_atTop 1, cr_ev_poly_exp 2 (Real.log 15) (δ := 1 / 400) (by norm_num),
    cr_ev_poly_exp 4 (Real.log 8) (δ := 1 / 10) (by norm_num)] with N hN e1 e2
  rw [Real.exp_log (by norm_num)] at e1 e2
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hθ : 0 < lt2θ N := Real.exp_pos _
  refine ⟨?_, ?_, hNr⟩
  · have h : lt2κ * sigN N / (4 * lt2θ N) = 625 * Real.exp ((N : ℝ) / 400) := by
      rw [← lt2_sig_div_theta]; unfold lt2κ; field_simp; ring
    rw [h, show (1 / 400 : ℝ) * N = (N : ℝ) / 400 by ring] at *
    have := Real.exp_pos ((N : ℝ) / 400)
    nlinarith
  · -- `8 N⁴ ≤ (4/3)^N`
    have hlog : (1 / 10 : ℝ) ≤ Real.log (4 / 3) := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 10) (by norm_num) (by norm_num)
      norm_num at this ⊢; linarith
    have h43 : Real.exp (1 / 10 * N) ≤ (4 / 3 : ℝ) ^ N := by
      rw [← Real.exp_log (show (0 : ℝ) < 4 / 3 by norm_num), ← Real.exp_nat_mul, Real.exp_le_exp]; nlinarith
    have hN4 : (N : ℝ) ^ 4 ≤ ((N : ℝ) + 1) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    have h8 : 8 * (N : ℝ) ^ 4 ≤ (4 / 3 : ℝ) ^ N := by linarith
    unfold lt2tG
    rw [lt2_sigN_sq, le_div_iff₀ (by positivity)]
    have : (2 / 3 : ℝ) ^ N = (1 / 2) ^ N * (4 / 3) ^ N := by rw [← mul_pow]; norm_num
    rw [this]
    have h2 : (0 : ℝ) < (1 / 2) ^ N := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h8 h2.le]

/-- The common exponent check. -/
lemma lt2_kind_exp {m' : ℕ} {c : ℝ} (hc : 1 / 4 ≤ c) (hmN : (N : ℝ) / 491520 ≤ m') :
    3 * (N : ℝ) + m' * Real.log (2 * Real.exp 1 * 12288) ≤ c * m' * lt2κ ^ 2 := by
  have hl := lt2_logc
  have hm0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  unfold lt2κ
  have h1 : m' * Real.log (2 * Real.exp 1 * 12288) ≤ 12 * m' := by nlinarith
  have h2 : (1 / 4 : ℝ) * m' * 2500 ^ 2 ≤ c * m' * 2500 ^ 2 := by
    have := mul_le_mul_of_nonneg_right hc (show (0 : ℝ) ≤ m' * 2500 ^ 2 by positivity); nlinarith
  nlinarith

theorem lt2_kind_mT (hev : 3 * (N : ℝ) + (N : ℝ) ^ 2 * 12 ≤ lt2κ * sigN N / (4 * lt2θ N))
    {α : Type*} (P : Finset α) (g : α → Finset (Fin N)) (hg : Set.InjOn g P) (hne : ∀ p ∈ P, (g p).Nonempty)
    {m' : ℕ} (hm1 : 1 ≤ m') (hPm : (P.card : ℝ) ≤ 12288 * m') (hmN : (N : ℝ) / 491520 ≤ m')
    (hmN2 : (m' : ℝ) ≤ (N : ℝ) ^ 2) :
    cubeM N {w | m' ≤ (P.filter fun p => lt2κ * sigN N ≤ |lt2mT w (g p)|).card} ≤
      ENNReal.ofReal (Real.exp (-(3 * (N : ℝ)))) := by
  refine (lt2_mT_count_img P g hg hne (by unfold lt2κ; norm_num) m' hm1).trans (ENNReal.ofReal_le_ofReal ?_)
  refine lt2_binom_le (D := 12288) (by norm_num) hPm (le_min ?_ ?_)
  · have := lt2_kind_exp (c := 1 / 4) le_rfl hmN; nlinarith
  · have hl := lt2_logc; have hm0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg _; nlinarith

theorem lt2_kind_Ot (hev : 3 * (N : ℝ) + (N : ℝ) ^ 2 * 12 ≤ lt2κ * sigN N / (4 * lt2θ N))
    {α : Type*} (P : Finset α) (g : α → Fin N × Finset (Fin N)) (hg : Set.InjOn g P)
    (hne : ∀ p ∈ P, (g p).2.Nonempty)
    {m' : ℕ} (hm1 : 1 ≤ m') (hPm : (P.card : ℝ) ≤ 12288 * m') (hmN : (N : ℝ) / 491520 ≤ m')
    (hmN2 : (m' : ℝ) ≤ (N : ℝ) ^ 2) :
    cubeM N {w | m' ≤ (P.filter fun p => lt2κ * sigN N ≤ |lt2Ot w (g p)|).card} ≤
      ENNReal.ofReal (Real.exp (-(3 * (N : ℝ)))) := by
  refine (lt2_Ot_count_img P g hg hne (by unfold lt2κ; norm_num) m' hm1).trans (ENNReal.ofReal_le_ofReal ?_)
  refine lt2_binom_le (D := 12288) (by norm_num) hPm (le_min ?_ ?_)
  · have := lt2_kind_exp (c := 20 / 3) (by norm_num) hmN; nlinarith
  · have hl := lt2_logc; have hm0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg _
    have hσ : 0 < sigN N := by unfold sigN; positivity
    have hθ : 0 < lt2θ N := Real.exp_pos _
    have h34 : lt2κ * sigN N / (4 * lt2θ N) ≤ lt2κ * sigN N / (3 * lt2θ N) :=
      div_le_div_of_nonneg_left (by unfold lt2κ; positivity) (by positivity) (by linarith)
    nlinarith

theorem lt2_kind_N0 (hev : 3 * (N : ℝ) + (N : ℝ) ^ 2 * 12 ≤ lt2κ * sigN N / (4 * lt2θ N))
    (hN : 8 * (1 / 2 : ℝ) ^ N ≤ lt2tG N) (hN1 : (1 : ℝ) ≤ N)
    (hextra : ∀ d m : ℕ, d ≤ N ^ 2 →
      ((d.choose m : ℕ) : ℝ) * 2 ^ m * (lt2B2 N + (d : ℝ) ^ 2 * lt2Bpair N) ≤ Real.exp (-(3 * (N : ℝ))))
    {α : Type*} {b : Bool} (Λ : Finset (Fin N)) (P : Finset α) (g : α → LT2Idx N) (hg : Set.InjOn g P)
    (hodd : ∀ p ∈ P, ((g p).2.1 ∩ Λ).card % 2 = 1)
    (hT : ∀ p ∈ P, ∀ p' ∈ P, (g p).2.1 = (g p').2.1 → symmDiff (g p).2.2 (g p').2.2 ≠ Λ)
    {m' : ℕ} (hm1 : 1 ≤ m') (hPm : (P.card : ℝ) ≤ 12288 * m') (hmN : (N : ℝ) / 491520 ≤ m')
    (hmN2 : (m' : ℝ) ≤ (N : ℝ) ^ 2) (hPN : P.card ≤ N ^ 2) :
    cubeM N {w | m' ≤ (P.filter fun p => lt2κ * sigN N ≤ |lt2N0 Λ b w (g p)|).card} ≤
      ENNReal.ofReal (2 * Real.exp (-(3 * (N : ℝ)))) := by
  have hN0 : N ≠ 0 := by intro h; subst h; norm_num at hN1
  refine (lt2_N0_count_img Λ P g hg hodd hT hN hN0 (by unfold lt2κ; norm_num) m' hm1).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [mul_add, two_mul]
  refine add_le_add ?_ (hextra _ _ hPN)
  refine lt2_binom_le (D := 12288) (by norm_num) hPm (le_min ?_ ?_)
  · have hm0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg _
    have hN4 : (m' : ℝ) / (N : ℝ) ^ 4 ≤ 1 := by
      rw [div_le_one (by positivity)]
      calc (m' : ℝ) ≤ (N : ℝ) ^ 2 := hmN2
        _ ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
    have hden : 0 < 2 + (m' : ℝ) / (N : ℝ) ^ 4 := by positivity
    have : m' * lt2κ ^ 2 ≤ 3 * m' * lt2κ ^ 2 / (2 + (m' : ℝ) / (N : ℝ) ^ 4) := by
      rw [le_div_iff₀ hden]
      have h3 : 2 + (m' : ℝ) / (N : ℝ) ^ 4 ≤ 3 := by linarith
      have := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ m' * lt2κ ^ 2 by positivity)
      linarith
    have := lt2_kind_exp (c := 1) (by norm_num) hmN
    nlinarith
  · have hl := lt2_logc; have hm0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg _
    have hσ : 0 < sigN N := by unfold sigN; positivity
    have hθ : 0 < lt2θ N := Real.exp_pos _
    have h34 : lt2κ * sigN N / (4 * lt2θ N) ≤ lt2κ * sigN N / lt2θ N :=
      div_le_div_of_nonneg_left (by unfold lt2κ; positivity) hθ (by linarith)
    nlinarith

end Census
end IIT
