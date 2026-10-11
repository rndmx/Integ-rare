/-
Census, Lemma RS (D1'): `goodFX_rate`, assembled from the cause and effect cell bounds.
-/
import IIT.Census.B1RSAbsorb
import IIT.Census.CertRSXESound

namespace IIT
namespace Census

open MeasureTheory Filter Finset

/-- **Lemma RS** (D1'), proved. -/
theorem goodFX_rate' : ∀ᶠ N in atTop, ∀ s : State N,
    ∑ r0 : State N, ∑ x : Fin N, ∑ σ : XSide, rowsInM (sensRows s r0) (GoodFX N s r0 x σ)
      ≤ ENNReal.ofReal (Real.exp (-(RXf * N))) := by
  filter_upwards [rs_absorb 122, eventually_ge_atTop 7] with N hab hN7 s
  have hN : 0 < N := by omega
  have hδ : deltaU N < 1 / 2 := by
    unfold deltaU; rw [div_lt_iff₀ (by positivity)]; have : (7 : ℝ) ≤ N := by exact_mod_cast hN7
    linarith
  set B := Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N with hB
  have hslT : 0 ≤ slT N := by
    unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    linarith
  have hB0 : 0 ≤ B := by positivity
  -- every term is ≤ 61 B
  have hterm : ∀ r0 x σ, rowsInM (sensRows s r0) (GoodFX N s r0 x σ) ≤ ENNReal.ofReal (61 * B) := by
    intro r0 x σ
    refine (rowsIn_goodFX_le s r0 x σ).trans ?_
    split_ifs with hfar
    swap; · exact bot_le
    have hh0 := ham_flipAt_le_one x r0
    have hh1 := ham_flipAt_le_one x s
    have hne : ∀ a b : State N, 3 ≤ ham a b → a ≠ b := fun a b h hab => by
      subst hab; rw [ham_self] at h; omega
    have hfar3 : 3 ≤ ham r0 s := by omega
    have t1 := ham_triangle (flipAt x r0) r0 s
    have t2 := ham_triangle r0 s (flipAt x s)
    have hc1 : ham s (flipAt x s) ≤ 1 := by rw [ham_comm]; exact hh1
    cases σ with
    | cause =>
      refine (regEvX_cause_prob hN s r0 x (hne _ _ hfar3) ?_).trans (ENNReal.ofReal_le_ofReal ?_)
      · intro h
        rw [← h] at hfar3
        have : ham r0 (flipAt x r0) ≤ 1 := by rw [ham_comm]; exact hh0
        omega
      · have := Real.exp_le_exp.2
          (show 14 * slT N + 17 * (8 + slV N) ≤ 19 * slT N + 17 * (8 + slV N) + 9 by linarith)
        rw [hB]
        gcongr
    | effect =>
      refine regEvX_effect_prob hN s r0 x hδ (fun h => hne _ _ hfar3 h.symm) ?_
      intro h
      rw [← h] at hfar3
      have := ham_triangle (flipAt x s) s (flipAt x s)
      rw [ham_self] at this
      have t4 := ham_triangle s (flipAt x s) s
      have : ham (flipAt x s) s ≤ 1 := hh1
      omega
  calc ∑ r0 : State N, ∑ x : Fin N, ∑ σ : XSide, rowsInM (sensRows s r0) (GoodFX N s r0 x σ)
      ≤ ∑ _r0 : State N, ∑ _x : Fin N, ∑ _σ : XSide, ENNReal.ofReal (61 * B) :=
        sum_le_sum fun r0 _ => sum_le_sum fun x _ => sum_le_sum fun σ _ => hterm r0 x σ
    _ = ENNReal.ofReal (2 ^ N * N * 2 * (61 * B)) := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show Fintype.card XSide = 2 from rfl, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        rw [ENNReal.ofReal_mul (p := (2 : ℝ) ^ N * N * 2) (by positivity),
          ENNReal.ofReal_mul (p := (2 : ℝ) ^ N * N) (by positivity),
          ENNReal.ofReal_mul (p := (2 : ℝ) ^ N) (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_natCast]
        simp; ring
    _ ≤ ENNReal.ofReal (Real.exp (-(RXf * N))) := by
        apply ENNReal.ofReal_le_ofReal
        have h2N : (0 : ℝ) < 2 ^ N := by positivity
        have : 2 ^ N * N * 2 * (61 * B) =
            122 * N * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) * Real.exp (-((10072 / 10000 : ℝ) * N)) := by
          simp only [hB, rsR0]; push_cast; field_simp; ring
        rw [this]; exact hab

end Census
end IIT
