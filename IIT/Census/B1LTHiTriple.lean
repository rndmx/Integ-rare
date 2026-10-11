/-
Census, B1 LTBetaHi, module T5: the triple lower bound with a separate pattern margin `m` (W2-2).

`tl_triple_lower_gen'` is `tl_triple_lower_gen` with the margin hypothesis `Σ Num(pat) + m ≤ Σ Num(t0)` and
`24 A η² < (A - η)² m` in place of the value level `y σ` (the margin is only used by `tl_tc_false`, which already takes
an arbitrary `m`).
-/
import IIT.Census.TripleLower
import IIT.Census.B1LTHiTrans

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

theorem tl_triple_lower_gen' {z : Param N} (hz : z ∈ openCube N) (s : State N) {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {A η δ y σ E0 m : ℝ}
    (hη : 0 ≤ η) (hηA : 3 * η ≤ A) (hA : 0 < A) (hδ : 0 ≤ δ) (hy : 0 < y) (hσ : 0 < σ)
    (hlev : ∀ Y ⊆ ({a, b, c} : Finset (Fin N)), ∀ t, ∀ i ∈ ({a, b, c} : Finset (Fin N)),
      |Num (flipP s z) {a, b, c} Y t i - A| ≤ η)
    (hreg : ∀ θ : SysPartition N {a, b, c},
      (∃ j ∈ ({a, b, c} : Finset (Fin N)), profile θ j ≠
        profile (tl_thetaStar a b c hab hac hbc) j) →
      (1 + δ) * tl_F (flipP s z) (tl_thetaStar a b c hab hac hbc) tl_t0 σ / 5 ≤
        tl_F (flipP s z) θ tl_t0 σ / (sysCutCount θ : ℝ))
    (hFy : y ≤ tl_F (flipP s z) (tl_thetaStar a b c hab hac hbc) tl_t0 σ)
    (hmarg : ∀ ta tb tc : Bool, (ta || tb || tc) = true →
      ∑ i ∈ ({a, b, c} : Finset (Fin N)), Num (flipP s z) {a, b, c} {a, b, c}
          (tl_pat3 a b c ta tb tc) i + m ≤
        ∑ i ∈ ({a, b, c} : Finset (Fin N)), Num (flipP s z) {a, b, c} {a, b, c} tl_t0 i)
    (hsmall : 36 * η ^ 2 < δ * y * σ * (A - η))
    (hmsmall : 24 * A * η ^ 2 < (A - η) ^ 2 * m)
    (hE0 : 6 * η / ((A - η) * Real.log 2) ≤ E0)
    (heff : ∃ te ∈ sysMaxEffStates (tpmOf z) {a, b, c} s s,
      ∀ θ : SysPartition N {a, b, c}, E0 ≤ sysPhiE (tpmOf z) {a, b, c} s θ s te) :
    σ * (y - 6 * η ^ 2 / ((A - η) * σ)) / (8 * A * Real.log 2) ≤ phi z s {a, b, c} := by
  set S : Finset (Fin N) := {a, b, c} with hSdef
  set w := flipP s z
  set θs := tl_thetaStar a b c hab hac hbc
  have hηA' : η < A := by
    rcases hη.lt_or_eq with h | h
    · linarith
    · rw [← h]; exact hA
  have hAη : 0 < A - η := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcard : S.card = 3 := tl_card3 hab hac hbc
  obtain ⟨te, hte, hE⟩ := heff
  obtain ⟨tc, htc⟩ := sysMaxCauseStates_nonempty (tpmOf z) S s s
  have htc0 := tl_tc_false hz s hab hac hbc hη hηA' (fun t i hi => hlev S (subset_refl _) t i hi)
    hmarg hmsmall htc
  set R := 3 * (2 * η ^ 2 / (A * (A - η))) with hR
  have hR0 : 0 ≤ R := by positivity
  set P : SysPartition N S → ℝ := fun θ => ∑ i ∈ S, tl_D w θ tl_t0 i with hP
  have hnear : ∀ θ : SysPartition N S, |tl_G w θ - P θ / A| ≤ R := by
    intro θ
    have := tl_G_near hη hηA' w (fun Y hY i hi => hlev Y hY tl_t0 i hi) θ
    rw [hcard] at this
    push_cast at this
    exact this
  have hback := sysBackCause_ge_of_mem hz s tc htc
  rw [hcard] at hback
  have hb0 : 0 < sysBackCause (tpmOf z) S s s tc := lt_of_lt_of_le (by norm_num) hback
  have hb1 := tl_backCause_le_one s hz hη hηA (fun t i hi => hlev S (subset_refl _) t i hi) tc
  have hC : ∀ θ : SysPartition N S, sysPhiC (tpmOf z) S s θ s tc =
      sysBackCause (tpmOf z) S s s tc * pos (tl_G w θ / Real.log 2) := by
    intro θ
    unfold sysPhiC
    rw [tl_logb_eq s hz htc0 θ]
  -- every cause side is at most `E0`
  have hDle : ∀ θ : SysPartition N S, tl_G w θ ≤ 6 * η / (A - η) := by
    intro θ
    have h1 := (abs_le.1 (hnear θ)).2
    have h2 : P θ ≤ 3 * (2 * η) := by
      have hs := sum_le_card_nsmul S (fun i => tl_D w θ tl_t0 i) (2 * η) fun i hi => by
        have hx := hlev S (subset_refl _) tl_t0 i hi
        have hy' := hlev _ (sdiff_subset : S \ profile θ i ⊆ S) tl_t0 i hi
        rw [abs_le] at hx hy'
        unfold tl_D; linarith
      rw [hcard, nsmul_eq_mul] at hs
      simp only [hP]
      push_cast at hs
      linarith
    have h3 : P θ / A ≤ 6 * η / A := by
      rw [div_le_div_iff_of_pos_right hA]; linarith
    have h4 : 6 * η / A + R = 6 * η / (A - η) := by
      rw [hR]; field_simp; ring
    linarith
  have hCle : ∀ θ : SysPartition N S, sysPhiC (tpmOf z) S s θ s tc ≤ E0 := by
    intro θ
    rw [hC θ]
    have hp : pos (tl_G w θ / Real.log 2) ≤ 6 * η / ((A - η) * Real.log 2) := by
      unfold pos
      refine max_le (by positivity) ?_
      rw [← div_div]
      exact div_le_div_of_nonneg_right (hDle θ) hlog2.le
    have h0 : 0 ≤ pos (tl_G w θ / Real.log 2) := pos_nonneg _
    calc _ ≤ 1 * pos (tl_G w θ / Real.log 2) := mul_le_mul_of_nonneg_right hb1 h0
      _ ≤ _ := by rw [one_mul]; exact hp.trans hE0
  have hAt : ∀ θ : SysPartition N S, sysPhiAt (tpmOf z) S s θ s tc te =
      sysPhiC (tpmOf z) S s θ s tc := fun θ =>
    min_eq_left ((hCle θ).trans (hE θ))
  -- the region in terms of `P`
  have hFs : tl_F w θs tl_t0 σ = P θs / σ := rfl
  have hPs : y * σ ≤ P θs := by
    rw [hFs, le_div_iff₀ hσ] at hFy; exact hFy
  have hLs : y * σ / A ≤ P θs / A := div_le_div_of_nonneg_right hPs hA.le
  have hsm' : 6 * R < δ * (y * σ / A) := by
    rw [hR]
    have : 36 * η ^ 2 / (A * (A - η)) < δ * y * σ * (A - η) / (A * (A - η)) :=
      div_lt_div_of_pos_right hsmall (mul_pos hA hAη)
    have e1 : δ * y * σ * (A - η) / (A * (A - η)) = δ * (y * σ / A) := by
      field_simp
    have e2 : 6 * (3 * (2 * η ^ 2 / (A * (A - η)))) = 36 * η ^ 2 / (A * (A - η)) := by ring
    linarith
  have hδL : δ * (y * σ / A) ≤ δ * (P θs / A) := mul_le_mul_of_nonneg_left hLs hδ
  have hLs0 : 0 ≤ P θs / A := le_trans (by positivity) hLs
  have hcc5 : (sysCutCount θs : ℝ) = 5 := by
    rw [tl_cc_star hab hac hbc]; norm_num
  -- the minimiser is `θ*`
  have hstrict : ∀ θ : SysPartition N S, (∃ j ∈ S, profile θ j ≠ profile θs j) →
      sysPhiAt (tpmOf z) S s θs s tc te / (sysCutCount θs : ℝ) <
        sysPhiAt (tpmOf z) S s θ s tc te / (sysCutCount θ : ℝ) := by
    intro θ hθ
    have hk1 : (1 : ℝ) ≤ sysCutCount θ := by exact_mod_cast sysCutCount_pos θ
    set k : ℝ := (sysCutCount θ : ℝ) with hk
    have hk0 : 0 < k := by linarith
    have hr := hreg θ hθ
    have hFθ : tl_F w θ tl_t0 σ = P θ / σ := rfl
    rw [hFs, hFθ, div_div, le_div_iff₀ (mul_pos hσ hk0)] at hr
    -- `k (1 + δ) P* ≤ 5 P_θ`
    have hr' : k * (1 + δ) * (P θs / A) ≤ 5 * (P θ / A) := by
      have : (1 + δ) * (P θs / σ) / 5 * (σ * k) = k * (1 + δ) * P θs / 5 := by
        field_simp
      rw [this] at hr
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 5)] at hr
      have : k * (1 + δ) * (P θs / A) = (k * (1 + δ) * P θs) / A := by ring
      rw [this, show 5 * (P θ / A) = (P θ * 5) / A by ring]
      exact div_le_div_of_nonneg_right hr hA.le
    have hGθ := abs_le.1 (hnear θ)
    have hGs := abs_le.1 (hnear θs)
    -- `5 G_θ > k max(G*, 0)`
    obtain ⟨hkey1, hkey0⟩ := tl_arith (Gs := tl_G w θs) (Gθ := tl_G w θ) hk1 hR0 hLs0 hr'
      (lt_of_lt_of_le hsm' hδL)
      (by linarith [hGθ.1]) (by linarith [hGs.2])
    rw [hAt, hAt, hC, hC, hcc5]
    have hpθ : pos (tl_G w θ / Real.log 2) = tl_G w θ / Real.log 2 :=
      max_eq_right (div_pos hkey0 hlog2).le
    rw [hpθ]
    set bb := sysBackCause (tpmOf z) S s s tc
    rcases le_or_gt (tl_G w θs) 0 with hneg | hposs
    · have : pos (tl_G w θs / Real.log 2) = 0 :=
        max_eq_left (div_nonpos_of_nonpos_of_nonneg hneg hlog2.le)
      rw [this, mul_zero, zero_div]
      exact div_pos (mul_pos hb0 (div_pos hkey0 hlog2)) hk0
    · have : pos (tl_G w θs / Real.log 2) = tl_G w θs / Real.log 2 :=
        max_eq_right (div_pos hposs hlog2).le
      rw [this, div_lt_div_iff₀ (by norm_num) hk0]
      have : bb * (tl_G w θs / Real.log 2) * k = bb / Real.log 2 * (k * tl_G w θs) := by ring
      rw [this]
      have : bb * (tl_G w θ / Real.log 2) * 5 = bb / Real.log 2 * (5 * tl_G w θ) := by ring
      rw [this]
      exact mul_lt_mul_of_pos_left hkey1 (div_pos hb0 hlog2)
  have hval := sysPhiOfState_eq_of_strict (tpmOf z) S s θs s tc te hstrict
  have hle := sysPhiOfState_le_sysPhi (tpmOf z) S s s htc hte
  unfold phi
  refine le_trans ?_ hle
  rw [hval, hAt, hC]
  have hGlow : y * σ / A - R ≤ tl_G w θs := by linarith [(abs_le.1 (hnear θs)).1]
  have hp1 : (y * σ / A - R) / Real.log 2 ≤ pos (tl_G w θs / Real.log 2) :=
    le_max_of_le_right (div_le_div_of_nonneg_right hGlow hlog2.le)
  have hp0 : 0 ≤ pos (tl_G w θs / Real.log 2) := pos_nonneg _
  have htarget : σ * (y - 6 * η ^ 2 / ((A - η) * σ)) / (8 * A * Real.log 2) =
      1 / 8 * ((y * σ / A - R) / Real.log 2) := by
    rw [hR]; field_simp; ring
  rw [htarget]
  calc 1 / 8 * ((y * σ / A - R) / Real.log 2) ≤ 1 / 8 * pos (tl_G w θs / Real.log 2) :=
        mul_le_mul_of_nonneg_left hp1 (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by rw [show (1 : ℝ) / 8 = 1 / 2 ^ 3 by norm_num]; exact hback) hp0


end Census
end IIT
