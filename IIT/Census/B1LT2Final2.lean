/-
Census, B1 lemma LT2, module M6f-4: the eventual numerical facts of the final assembly.
-/
import IIT.Census.B1LT2Final1

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

lemma lt2_log38_ge : (-9677 / 10000 : ℝ) ≤ Real.log (38 / 100 : ℝ) := by
  have hq : (((-9677 / 10000 : ℚ)) : ℝ) ≤ Real.log (((38 / 100 : ℚ)) : ℝ) := crLog_ge (-1) 40 (by decide +kernel)
  push_cast at hq; exact hq

/-- `2^N p̄ ≥ e^{3N/10}`. -/
lemma lt2_pH_ge (N : ℕ) : Real.exp (3 / 10 * (N : ℝ)) ≤ 2 ^ N * lt2pH N := by
  have h2 : (2 : ℝ) ^ N = Real.exp (Real.log 2 * N) := by
    rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_nat_mul, Real.exp_log (by norm_num)]; ring_nf
  rw [h2, lt2pH, ← Real.exp_add, Real.exp_le_exp]
  have := lt2_log38_ge; have := Real.log_two_gt_d9
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-- **The numerical facts.** -/
theorem lt2_final_ev : ∀ᶠ N : ℕ in atTop,
    sigN N ≤ 1 / 15 ∧ lt2θ N ≤ sigN N / (14 * 16 * lt2x) ∧
    Real.exp (-(2 ^ N * lt2pH N / 8)) ≤ Real.exp (-(11 / 10 * (N : ℝ))) ∧
    (((lt2m N).choose (lt2m N / 8) : ℕ) : ℝ) * (2 * lt2γ) ^ (lt2m N / 8) ≤ Real.exp (-(11 / 10 * (N : ℝ))) ∧
    Real.exp (-(lt2p2 * (((lt2m N : ℝ)) ^ 2 / 4))) ≤ Real.exp (-(11 / 10 * (N : ℝ))) ∧
    Real.exp (-(3 * (N : ℝ)) + 1) ≤ Real.exp (-(11 / 10 * (N : ℝ))) ∧
    16 * Real.exp (-(2 * (N : ℝ))) ≤ Real.exp (-(11 / 10 * (N : ℝ))) ∧
    Real.exp (-(105 / 100 * (N : ℝ))) + 7 * Real.exp (-(11 / 10 * (N : ℝ))) ≤ Real.exp (-(104 / 100 * (N : ℝ))) ∧
    1 ≤ N ∧ 16 ≤ lt2m N := by
  have hp2 := lt2p2_pos
  filter_upwards [eventually_ge_atTop (⌈7040 / lt2p2⌉₊ + 3000000000000),
    cr_ev_poly_exp 1 (Real.log 9) (δ := 3 / 10) (by norm_num)] with N hN e1
  rw [Real.exp_log (by norm_num), pow_one] at e1
  have hNr : (3000000000000 : ℝ) ≤ N := by
    have : 3000000000000 ≤ N := le_trans (Nat.le_add_left _ _) hN
    exact_mod_cast this
  have hNp : 7040 / lt2p2 ≤ N := by
    have h1 : (⌈7040 / lt2p2⌉₊ : ℝ) ≤ N := by exact_mod_cast le_trans (Nat.le_add_right _ _) hN
    exact (Nat.le_ceil _).trans h1
  have hN0 : (0 : ℝ) ≤ N := by linarith
  set m := lt2m N with hmdef
  have hmn : 20 * m ≤ N ∧ N < 20 * m + 20 := by rw [hmdef]; unfold lt2m; omega
  have hmr : (N : ℝ) / 20 - 1 ≤ m := by
    have : N < 20 * m + 20 := hmn.2
    have : (N : ℝ) < 20 * m + 20 := by exact_mod_cast this
    linarith
  have hx0 := cr_x0_bounds
  have hlo : ((crX0lo : ℚ) : ℝ) ≥ 2027 / 10000 := by unfold crX0lo; push_cast; norm_num
  have hσ : sigN N = Real.exp (-(x0 * N)) := sigN_eq_exp N
  have hexp_big : ∀ y : ℝ, 0 ≤ y → 1 + y ≤ Real.exp y := fun y _ => by linarith [Real.add_one_le_exp y]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, by omega⟩
  · -- `σ ≤ 1/15`
    rw [hσ, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have := hexp_big (x0 * N) (by nlinarith); nlinarith
  · -- `θ ≤ σ/(224x)`
    have h1 : lt2θ N = sigN N * Real.exp (-(N : ℝ) / 400) := by
      rw [hσ, lt2θ, lt2x1, ← Real.exp_add]; congr 1; ring
    rw [h1, le_div_iff₀ (by unfold lt2x; norm_num)]
    have h2 : 14 * 16 * lt2x * Real.exp (-(N : ℝ) / 400) ≤ 1 := by
      have := hexp_big ((N : ℝ) / 400) (by positivity)
      have h3 : Real.exp (-(N : ℝ) / 400) = (Real.exp ((N : ℝ) / 400))⁻¹ := by rw [← Real.exp_neg]; ring_nf
      rw [h3, mul_inv_le_iff₀ (Real.exp_pos _)]; unfold lt2x; nlinarith
    have hσp : 0 < sigN N := by rw [hσ]; exact Real.exp_pos _
    nlinarith
  · -- the heavy count
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have := lt2_pH_ge N
    rw [show (3 / 10 : ℝ) * N = 3 / 10 * N from rfl] at e1
    nlinarith
  · -- the weak units
    set k := m / 8
    have hk : m ≤ 8 * k + 7 := by omega
    have hkr : (N : ℝ) / 160 - 1 ≤ k := by
      have : (m : ℝ) ≤ 8 * k + 7 := by exact_mod_cast hk
      linarith
    have hc : (((m.choose k : ℕ) : ℝ)) ≤ Real.exp m := by
      have h1 : ((m.choose k : ℕ) : ℝ) ≤ 2 ^ m := by exact_mod_cast Nat.choose_le_two_pow m k
      have h2 : (2 : ℝ) ^ m ≤ Real.exp m := by
        rw [← Real.exp_one_pow]; exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) m
      linarith
    have hg : 2 * lt2γ ≤ Real.exp (-199) := by
      unfold lt2γ
      have : Real.exp (-199) = Real.exp 1 * Real.exp (-200) := by rw [← Real.exp_add]; norm_num
      rw [this]; nlinarith [Real.exp_pos (-200), Real.exp_one_gt_d9]
    have hgk : (2 * lt2γ) ^ k ≤ Real.exp (-199 * k) := by
      calc (2 * lt2γ) ^ k ≤ Real.exp (-199) ^ k := pow_le_pow_left₀ (by unfold lt2γ; positivity) hg k
        _ = Real.exp (-199 * k) := by rw [← Real.exp_nat_mul]; ring_nf
    calc (((m.choose k : ℕ) : ℝ)) * (2 * lt2γ) ^ k ≤ Real.exp m * Real.exp (-199 * k) :=
          mul_le_mul hc hgk (by unfold lt2γ; positivity) (Real.exp_pos _).le
      _ = Real.exp (m - 199 * k) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(11 / 10 * (N : ℝ))) := by
          refine Real.exp_le_exp.2 ?_
          have : (m : ℝ) ≤ 8 * k + 7 := by exact_mod_cast hk
          nlinarith
  · -- the conditional product
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have hm40 : (N : ℝ) / 40 ≤ m := by linarith
    have hm2 : ((N : ℝ) / 40) ^ 2 ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hm40 2
    have : 7040 ≤ lt2p2 * N := by rwa [div_le_iff₀ hp2, mul_comm] at hNp
    nlinarith
  · exact Real.exp_le_exp.2 (by linarith)
  · have h : Real.exp (-(11 / 10 * (N : ℝ))) = Real.exp (-(2 * (N : ℝ))) * Real.exp (9 / 10 * N) := by
      rw [← Real.exp_add]; ring_nf
    rw [h]
    have := hexp_big (9 / 10 * N) (by positivity)
    have := Real.exp_pos (-(2 * (N : ℝ)))
    nlinarith
  · have h1 : Real.exp (-(11 / 10 * (N : ℝ))) = Real.exp (-(105 / 100 * (N : ℝ))) * Real.exp (-(5 / 100 * N)) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-(104 / 100 * (N : ℝ))) = Real.exp (-(105 / 100 * (N : ℝ))) * Real.exp (1 / 100 * N) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-(5 / 100 * (N : ℝ))) ≤ 1 / 7 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have := hexp_big (5 / 100 * N) (by positivity); linarith
    have h4 : (2 : ℝ) ≤ Real.exp (1 / 100 * N) := by have := hexp_big (1 / 100 * N) (by positivity); linarith
    rw [h1, h2]
    have := Real.exp_pos (-(105 / 100 * (N : ℝ)))
    nlinarith

end Census
end IIT
