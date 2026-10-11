/-
Census, B1 lemma LT2, module M6d-3a: asymptotics.

* `lt2_card_D1`, `lt2_card_D2`: `|D₁| = |D₂| = m = N/20`.
* `lt2_B_small`: eventually `B₂ ≤ e^{-N³}` and `B_pair ≤ 6 e^{-N³}` (every exponent is `≥ e^{N/200}/(128 N⁸) ≥ N³`).
* `lt2_extra_small`: eventually, for `d ≤ N²`, `C(d,m) 2^m (B₂ + d² B_pair) ≤ e^{-3N}`.
-/
import IIT.Census.B1LT2Adv

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

lemma lt2_card_window (lo hi : ℕ) (hhi : hi ≤ N) :
    (univ.filter fun j : Fin N => lo ≤ j.val ∧ j.val < hi).card = hi - lo := by
  have h : (univ.filter fun j : Fin N => lo ≤ j.val ∧ j.val < hi).map Fin.valEmbedding = Finset.Ico lo hi := by
    ext n
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hn; exact ⟨⟨n, by omega⟩, hn, rfl⟩
  rw [← Finset.card_map, h, Nat.card_Ico]

lemma lt2_card_D1 : (lt2D1 N).card = lt2m N := by
  unfold lt2D1
  rw [lt2_card_window _ _ (Nat.sub_le _ _)]
  unfold lt2m; omega

lemma lt2_card_D2 : (lt2D2 N).card = lt2m N := by
  have h : lt2D2 N = univ.filter fun j : Fin N => N - lt2m N ≤ j.val ∧ j.val < N := by
    unfold lt2D2; ext j; simp [j.isLt]
  rw [h, lt2_card_window _ _ le_rfl]
  unfold lt2m; omega

/-- The common lower bound of the failure exponents. -/
lemma lt2_exps_ge (hN : 1 ≤ N) :
    let E := Real.exp ((N : ℝ) / 200) / (128 * (N : ℝ) ^ 8)
    E ≤ (sigN N ^ 2) ^ 2 / (4 * (2 / 5 : ℝ) ^ N) ∧
    E ≤ sigN N ^ 2 / (2 * (2 * lt2θ N ^ 2)) ∧
    E ≤ lt2tG N ^ 2 / (4 * (2 / 5 : ℝ) ^ N) ∧
    E ≤ lt2tG N / (2 * (2 * lt2θ N ^ 2)) ∧
    E ≤ (lt2tG N / 2) ^ 2 / (4 * (8 * (1 / 3 : ℝ) ^ N * sigN N ^ 2)) ∧
    E ≤ (lt2tG N / 2) / (2 * (2 * lt2θ N ^ 2)) ∧
    E ≤ 1 / (4 * sigN N ^ 2) ∧
    E ≤ 1 / (4 * lt2θ N) := by
  intro E
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN8 : (1 : ℝ) ≤ (N : ℝ) ^ 8 := one_le_pow₀ hNr
  have hN4 : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ hNr
  have hN84 : (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 8 := pow_le_pow_right₀ hNr (by norm_num)
  have hσ : 0 < sigN N ^ 2 := by unfold sigN; positivity
  have hθ : 0 < lt2θ N := Real.exp_pos _
  have he : 0 < Real.exp ((N : ℝ) / 200) := Real.exp_pos _
  have h109 : Real.exp ((N : ℝ) / 200) ≤ (10 / 9 : ℝ) ^ N := by
    refine le_trans (Real.exp_le_exp.2 ?_) (lt2_exp_le_109 N); nlinarith
  have h2 : Real.exp ((N : ℝ) / 200) ≤ (2 : ℝ) ^ N := by
    rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_nat_mul, Real.exp_le_exp]
    have := Real.log_two_gt_d9; nlinarith
  have h32 : Real.exp ((N : ℝ) / 200) ≤ (3 / 2 : ℝ) ^ N := by
    rw [← Real.exp_log (show (0 : ℝ) < 3 / 2 by norm_num), ← Real.exp_nat_mul, Real.exp_le_exp]
    have : (1 / 200 : ℝ) ≤ Real.log (3 / 2) := by
      have := Real.add_one_le_exp (-(1 / 3 : ℝ))
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have h := Real.exp_le_exp.2 (show (1 / 200 : ℝ) ≤ 1 / 3 by norm_num)
      have h' : Real.exp (1 / 3) ≤ 3 / 2 := by
        have := Real.exp_bound' (x := 1 / 3) (by norm_num) (by norm_num) (n := 3) (by norm_num)
        norm_num [Finset.sum_range_succ, Nat.factorial] at this; linarith
      linarith
    nlinarith
  have hsig4 := lt2_sig4_ratio N
  have hsigθ := lt2_sig_theta N
  have hθ2 : lt2θ N ^ 2 = sigN N ^ 2 * Real.exp (-(N : ℝ) / 200) := lt2θ_sq N
  have hE1 : Real.exp ((N : ℝ) / 200) * Real.exp (-(N : ℝ) / 200) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hE : E ≤ Real.exp ((N : ℝ) / 200) / 128 := by
    simp only [E]; exact div_le_div_of_nonneg_left he.le (by norm_num) (by nlinarith)
  have hE4 : E ≤ Real.exp ((N : ℝ) / 200) / (128 * (N : ℝ) ^ 4) := by
    simp only [E]; exact div_le_div_of_nonneg_left he.le (by positivity) (by nlinarith)
  have htG : lt2tG N = sigN N ^ 2 / (N : ℝ) ^ 4 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (sigN N ^ 2) ^ 2 / (4 * (2 / 5 : ℝ) ^ N) = ((sigN N ^ 2) ^ 2 / (2 / 5 : ℝ) ^ N) / 4 by ring, hsig4]
    linarith
  · rw [show sigN N ^ 2 / (2 * (2 * lt2θ N ^ 2)) = (sigN N ^ 2 / lt2θ N ^ 2) / 4 by field_simp <;> ring, hsigθ]
    linarith
  · rw [htG, show (sigN N ^ 2 / (N : ℝ) ^ 4) ^ 2 / (4 * (2 / 5 : ℝ) ^ N) =
      ((sigN N ^ 2) ^ 2 / (2 / 5 : ℝ) ^ N) / (4 * (N : ℝ) ^ 8) by field_simp <;> ring, hsig4]
    simp only [E]; exact div_le_div₀ (by positivity) h109 (by positivity) (by nlinarith)
  · rw [htG, show sigN N ^ 2 / (N : ℝ) ^ 4 / (2 * (2 * lt2θ N ^ 2)) =
      (sigN N ^ 2 / lt2θ N ^ 2) / (4 * (N : ℝ) ^ 4) by field_simp <;> ring, hsigθ]
    refine hE4.trans (div_le_div_of_nonneg_left he.le (by positivity) (by nlinarith))
  · have hs3 : sigN N ^ 2 / (1 / 3 : ℝ) ^ N = 2 ^ N := by
      rw [lt2_sigN_sq, ← div_pow]; norm_num
    rw [htG, show (sigN N ^ 2 / (N : ℝ) ^ 4 / 2) ^ 2 / (4 * (8 * (1 / 3 : ℝ) ^ N * sigN N ^ 2)) =
      (sigN N ^ 2 / (1 / 3 : ℝ) ^ N) / (128 * (N : ℝ) ^ 8) by field_simp <;> ring, hs3]
    simp only [E]; exact div_le_div_of_nonneg_right h2 (by positivity)
  · rw [htG, show sigN N ^ 2 / (N : ℝ) ^ 4 / 2 / (2 * (2 * lt2θ N ^ 2)) =
      (sigN N ^ 2 / lt2θ N ^ 2) / (8 * (N : ℝ) ^ 4) by field_simp <;> ring, hsigθ]
    refine hE4.trans (div_le_div_of_nonneg_left he.le (by positivity) (by nlinarith))
  · rw [lt2_sigN_sq, show (1 : ℝ) / (4 * (2 / 3 : ℝ) ^ N) = (3 / 2 : ℝ) ^ N / 4 by
      rw [show (3 / 2 : ℝ) = (2 / 3)⁻¹ by norm_num, inv_pow]; field_simp]
    linarith
  · have hx1 := lt2x1_bounds
    have hθe : 1 / (4 * lt2θ N) = Real.exp (lt2x1 * N) / 4 := by
      unfold lt2θ; rw [Real.exp_neg]; field_simp
    rw [hθe]
    have : Real.exp ((N : ℝ) / 200) ≤ Real.exp (lt2x1 * N) := Real.exp_le_exp.2 (by nlinarith)
    linarith

/-- **The failure terms are doubly-exponentially small.** -/
theorem lt2_B_small : ∀ᶠ N : ℕ in atTop,
    lt2B2 N ≤ Real.exp (-((N : ℝ) ^ 3)) ∧ lt2Bpair N ≤ 6 * Real.exp (-((N : ℝ) ^ 3)) := by
  filter_upwards [eventually_ge_atTop 1, cr_ev_poly_exp 11 (Real.log 128) (δ := 1 / 200) (by norm_num)]
    with N hN e1
  rw [Real.exp_log (by norm_num)] at e1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := lt2_exps_ge hN
  set E := Real.exp ((N : ℝ) / 200) / (128 * (N : ℝ) ^ 8)
  have hEN : (N : ℝ) ^ 3 ≤ E := by
    have h11 : (N : ℝ) ^ 11 ≤ ((N : ℝ) + 1) ^ 11 := pow_le_pow_left₀ (by positivity) (by linarith) 11
    have : (N : ℝ) ^ 3 * (128 * (N : ℝ) ^ 8) ≤ Real.exp ((N : ℝ) / 200) := by
      rw [show (1 / 200 : ℝ) * N = (N : ℝ) / 200 by ring] at e1
      nlinarith [pow_pos (show (0 : ℝ) < N by linarith) 8]
    simp only [E]; rw [le_div_iff₀ (by positivity)]; exact this
  have hX : ∀ X Y : ℝ, E ≤ X → E ≤ Y → Real.exp (-min X Y) ≤ Real.exp (-((N : ℝ) ^ 3)) := fun X Y hX hY =>
    Real.exp_le_exp.2 (neg_le_neg (le_min (hEN.trans hX) (hEN.trans hY)))
  have hB2 : lt2B2 N ≤ Real.exp (-((N : ℝ) ^ 3)) := hX _ _ i1 i2
  refine ⟨hB2, ?_⟩
  unfold lt2Bpair
  have t1 := hX _ _ i3 i4
  have t2 := hX _ _ i5 i6
  have t3 := hX _ _ i7 i8
  linarith

/-- **The extra term of the shifted-entry counts.** -/
theorem lt2_extra_small : ∀ᶠ N : ℕ in atTop, ∀ d m : ℕ, d ≤ N ^ 2 →
    ((d.choose m : ℕ) : ℝ) * 2 ^ m * (lt2B2 N + (d : ℝ) ^ 2 * lt2Bpair N) ≤ Real.exp (-(3 * (N : ℝ))) := by
  filter_upwards [lt2_B_small, eventually_ge_atTop 10,
    cr_ev_poly_exp 4 (Real.log 7) (δ := 1) (by norm_num)] with N hB hN e1 d m hd
  rw [Real.exp_log (by norm_num), one_mul] at e1
  obtain ⟨hB2, hBp⟩ := hB
  have hNr : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hdr : (d : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hd
  have hE := Real.exp_pos (-((N : ℝ) ^ 3))
  rcases Nat.lt_or_ge d m with hdm | hdm
  · rw [Nat.choose_eq_zero_of_lt hdm]; simp; positivity
  have hc : ((d.choose m : ℕ) : ℝ) * 2 ^ m ≤ (4 : ℝ) ^ (N ^ 2) := by
    have h1 : ((d.choose m : ℕ) : ℝ) ≤ 2 ^ d := by exact_mod_cast Nat.choose_le_two_pow d m
    have h2 : (2 : ℝ) ^ m ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hdm
    have h3 : (2 : ℝ) ^ d ≤ 2 ^ (N ^ 2) := pow_le_pow_right₀ (by norm_num) hd
    calc ((d.choose m : ℕ) : ℝ) * 2 ^ m ≤ 2 ^ (N ^ 2) * 2 ^ (N ^ 2) := by gcongr <;> linarith
      _ = (4 : ℝ) ^ (N ^ 2) := by rw [← mul_pow]; norm_num
  have hbr : lt2B2 N + (d : ℝ) ^ 2 * lt2Bpair N ≤ 7 * (N : ℝ) ^ 4 * Real.exp (-((N : ℝ) ^ 3)) := by
    have hd2 : (d : ℝ) ^ 2 ≤ (N : ℝ) ^ 4 := by nlinarith [sq_nonneg (d : ℝ)]
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ (by linarith)
    have hbp0 := lt2Bpair_nonneg (N := N)
    nlinarith [mul_le_mul hd2 hBp hbp0 (by positivity)]
  have h4 : (4 : ℝ) ^ (N ^ 2) = Real.exp (Real.log 4 * (N : ℝ) ^ 2) := by
    rw [← Real.exp_log (show (0 : ℝ) < 4 by norm_num), ← Real.exp_nat_mul, Real.exp_log (by norm_num)]
    push_cast; ring_nf
  have hl4 : Real.log 4 < 14 / 10 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith [Real.log_two_lt_d9]
  have h7 : 7 * (N : ℝ) ^ 4 ≤ Real.exp N := by
    have : (N : ℝ) ^ 4 ≤ ((N : ℝ) + 1) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    linarith
  calc ((d.choose m : ℕ) : ℝ) * 2 ^ m * (lt2B2 N + (d : ℝ) ^ 2 * lt2Bpair N)
      ≤ (4 : ℝ) ^ (N ^ 2) * (7 * (N : ℝ) ^ 4 * Real.exp (-((N : ℝ) ^ 3))) :=
        mul_le_mul hc hbr (add_nonneg (Real.exp_pos _).le (mul_nonneg (sq_nonneg _) lt2Bpair_nonneg))
          (by positivity)
    _ ≤ Real.exp (Real.log 4 * (N : ℝ) ^ 2) * (Real.exp N * Real.exp (-((N : ℝ) ^ 3))) := by
        rw [h4]; gcongr
    _ = Real.exp (Real.log 4 * (N : ℝ) ^ 2 + N - (N : ℝ) ^ 3) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(3 * (N : ℝ))) := by
        refine Real.exp_le_exp.2 ?_
        nlinarith [mul_le_mul_of_nonneg_right hl4.le (sq_nonneg (N : ℝ))]

end Census
end IIT
