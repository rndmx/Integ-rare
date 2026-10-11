/-
Census, B1 LTBetaHi, module T3 (part 4): (R6) perturbation of an admissible table.

If `|M u i - M0 u i| ≤ ω` for all entries, the three conditions move by at most explicit multiples of `ω`:
`|8 v_C(M) - 8 v_C(M0)| ≤ rlAbs C · ω` (`rlAbs C = Σ |cd_fz 3 C 0 _|`, kernel-computed: `≤ 36` for every profile) and
`|PS(M) - PS(M0)| ≤ 3ω` per pattern; the gap condition weakens by `6ω`.
-/
import IIT.Census.B1LTHiCertRL3

namespace IIT
namespace Census

/-- The absolute coefficient sum of `8 v_C`. -/
def rlAbs (C : List (List Bool)) : ℚ :=
  rlS3 fun i => rlS8 fun u => |(cd_fz 3 C 0 (u + 8 * i) : ℚ)|

theorem rlAbs_le : lp3Profiles.all (fun C => decide (rlAbs C ≤ 36)) = true := by decide +kernel

lemma rlAbs_le' {C : List (List Bool)} (hC : C ∈ lp3Profiles) : rlAbs C ≤ 36 := by
  have h := rlAbs_le
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h C hC

lemma rlAbs_star : rlAbs lp3CStar ≤ 36 := rlAbs_le' (by decide +kernel)

lemma rl_abs_term (a x y ω : ℚ) (h : |x - y| ≤ ω) : |a * x - a * y| ≤ |a| * ω := by
  rw [← mul_sub, abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg a)

lemma rlS8_abs_le {f g : ℕ → ℚ} (h : ∀ u, |f u| ≤ g u) : |rlS8 f| ≤ rlS8 g := by
  unfold rlS8
  have := fun u => abs_le.1 (h u)
  rw [abs_le]; constructor <;>
    linarith [(this 0).1, (this 1).1, (this 2).1, (this 3).1, (this 4).1, (this 5).1, (this 6).1, (this 7).1,
      (this 0).2, (this 1).2, (this 2).2, (this 3).2, (this 4).2, (this 5).2, (this 6).2, (this 7).2]

lemma rlS3_abs_le {f g : ℕ → ℚ} (h : ∀ u, |f u| ≤ g u) : |rlS3 f| ≤ rlS3 g := by
  unfold rlS3
  have := fun u => abs_le.1 (h u)
  rw [abs_le]; constructor <;> linarith [(this 0).1, (this 1).1, (this 2).1, (this 0).2, (this 1).2, (this 2).2]

/-- **Perturbation of the value form.** -/
theorem rlV8_pert (C : List (List Bool)) (Ts : ℕ) {M M0 : Fin 8 → Fin 3 → ℚ} {ω : ℚ}
    (h : ∀ u i, |rlM M u i - rlM M0 u i| ≤ ω) :
    |rlV8 C Ts M - rlV8 C Ts M0| ≤ rlAbs C * ω := by
  have e : rlV8 C Ts M - rlV8 C Ts M0 = rlS3 fun i => rlS8 fun u =>
      ((cd_fz 3 C 0 (u + 8 * i) : ℚ) * rlM M (Ts ^^^ u) i - (cd_fz 3 C 0 (u + 8 * i) : ℚ) * rlM M0 (Ts ^^^ u) i) := by
    unfold rlV8 rlS3 rlS8; ring
  have e2 : rlAbs C * ω = rlS3 fun i => rlS8 fun u => |(cd_fz 3 C 0 (u + 8 * i) : ℚ)| * ω := by
    unfold rlAbs rlS3 rlS8; ring
  rw [e, e2]
  exact rlS3_abs_le fun i => rlS8_abs_le fun u => rl_abs_term _ _ _ _ (h _ _)

theorem rlPS_pert {M M0 : Fin 8 → Fin 3 → ℚ} {ω : ℚ} (h : ∀ u i, |rlM M u i - rlM M0 u i| ≤ ω) (u : ℕ) :
    |rlPS M u - rlPS M0 u| ≤ 3 * ω := by
  unfold rlPS rlS3
  have h0 := abs_le.1 (h u 0); have h1 := abs_le.1 (h u 1); have h2 := abs_le.1 (h u 2)
  rw [abs_le]; constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

/-- **(R6) Weakened admissibility of a perturbed table.** -/
theorem rlAdm_pert {d : RLD} {t : ℚ} {Ts : ℕ} {M0 M : Fin 8 → Fin 3 → ℚ} (h : rlAdm d t Ts M0) {ω : ℚ}
    (hM : ∀ u i, |rlM M u i - rlM M0 u i| ≤ ω) :
    8 * d.G1 * (5 / 3 - t) - 36 * ω ≤ rlV8 lp3CStar Ts M ∧
    (∀ C ∈ lp3Profiles, C ≠ lp3CStar →
      1 / 20 * d.G1 * t - 6 * ω ≤ rlV8 C Ts M / (8 * (cd_cc 3 C : ℚ)) - rlV8 lp3CStar Ts M / 40) ∧
    (∀ u < 8, u ≠ Ts → 1 / 20 - 6 * ω ≤ rlPS M Ts - rlPS M u) := by
  obtain ⟨-, v1, g1, p1⟩ := h
  have hω : 0 ≤ ω := (abs_nonneg _).trans (hM 0 0)
  have hs := abs_le.1 (rlV8_pert lp3CStar Ts hM)
  have hsb := rlAbs_star
  have hsa : 0 ≤ rlAbs lp3CStar := by
    unfold rlAbs rlS3 rlS8; positivity
  have hmul := mul_le_mul_of_nonneg_right hsb hω
  refine ⟨by linarith [hs.1], fun C hC hne => ?_, fun u hu hne => ?_⟩
  · have hc := abs_le.1 (rlV8_pert C Ts hM)
    have hcb := rlAbs_le' hC
    have hca : 0 ≤ rlAbs C := by unfold rlAbs rlS3 rlS8; positivity
    have hcc : (1 : ℚ) ≤ cd_cc 3 C := by
      have := profiles3_cc_pos C (by simpa [profiles3] using hC); exact_mod_cast this
    have := g1 C hC hne
    -- |Δ(v_C/(8cc))| ≤ 36ω/8, |Δ(v*/40)| ≤ 36ω/40
    have e1 : |rlV8 C Ts M / (8 * (cd_cc 3 C : ℚ)) - rlV8 C Ts M0 / (8 * (cd_cc 3 C : ℚ))| ≤ 36 * ω / 8 := by
      have hc8 : (0 : ℚ) < 8 * (cd_cc 3 C : ℚ) := by linarith
      rw [← sub_div, abs_div, abs_of_pos hc8, div_le_iff₀ hc8]
      have : |rlV8 C Ts M - rlV8 C Ts M0| ≤ 36 * ω :=
        (rlV8_pert C Ts hM).trans (mul_le_mul_of_nonneg_right hcb hω)
      nlinarith
    have e1' := abs_le.1 e1
    have e2 : |rlV8 lp3CStar Ts M / 40 - rlV8 lp3CStar Ts M0 / 40| ≤ 36 * ω / 40 := by
      rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℚ) < 40)]
      have : |rlV8 lp3CStar Ts M - rlV8 lp3CStar Ts M0| ≤ 36 * ω :=
        (rlV8_pert lp3CStar Ts hM).trans (mul_le_mul_of_nonneg_right hsb hω)
      linarith
    have e2' := abs_le.1 e2
    linarith [e1'.1, e2'.2]
  · have a1 := abs_le.1 (rlPS_pert hM Ts)
    have a2 := abs_le.1 (rlPS_pert hM u)
    have := p1 u hu hne
    linarith [a1.1, a2.2]

end Census
end IIT
