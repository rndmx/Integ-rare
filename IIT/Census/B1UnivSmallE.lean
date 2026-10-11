/-
Census, B1 lower bound, leaf `phi_univ_ge_EX`: the effect-side small-cut sums (`smallE_cond'`).

For `1 ≤ |K| < D` with `|K| + 1 < ham(r0, s)`, the subcube of `s` free on `K` contains the fixed row `s`
(reading `x_j`) and `2^|K| - 1` generic rows `RGE K`, read through `φ_j` (`clamp01` or `1 - clamp01`).
-/
import IIT.Census.B1UnivSmallC2

set_option maxRecDepth 100000

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

variable {N : ℕ}

section Effect

variable (s r0 : State N) (x : Fin N)

/-- The generic rows of the subcube of `s` free on `K`. -/
noncomputable def RGE (K : Finset (Fin N)) : Finset {r // r ∉ rowsA s r0 x} :=
  (agree Kᶜ s).subtype fun r => r ∉ rowsA s r0 x

variable {s r0 x}

lemma not_mem_agree_s {K : Finset (Fin N)} {r : State N} (hr : K.card < ham r s) : r ∉ agree Kᶜ s := by
  intro h
  have := ham_le_card_of_mem_agree h
  omega

lemma agree_s_filter_rowsA {K : Finset (Fin N)} (hK : K.card + 1 < ham r0 s) :
    (agree Kᶜ s).filter (fun r => r ∈ rowsA s r0 x) = {s} := by
  have h0 : r0 ∉ agree Kᶜ s := not_mem_agree_s (by omega)
  have h1 : flipAt x r0 ∉ agree Kᶜ s := by
    apply not_mem_agree_s
    have h := ham_triangle r0 (flipAt x r0) s
    have h' := ham_flipAt_le_one x r0
    rw [ham_comm] at h'
    omega
  ext r
  simp only [mem_filter, rowsA, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hr, h | h | h⟩
    · subst h; exact absurd hr h0
    · subst h; exact absurd hr h1
    · exact h
  · rintro rfl
    exact ⟨self_mem_agree _ _, Or.inr (Or.inr rfl)⟩

lemma card_RGE {K : Finset (Fin N)} (hK : K.card + 1 < ham r0 s) :
    ((RGE s r0 x K).card : ℝ) = 2 ^ K.card - 1 := by
  have h1 : (RGE s r0 x K).card = ((agree Kᶜ s).filter fun r => r ∉ rowsA s r0 x).card :=
    card_subtype _ _
  have h2 := card_filter_add_card_filter_not (s := agree Kᶜ s) (fun r => r ∈ rowsA s r0 x)
  rw [agree_s_filter_rowsA hK, card_agree, card_compl_sub, card_singleton] at h2
  rw [h1]
  have h2' : (1 : ℝ) + ((((agree Kᶜ s).filter fun r => r ∉ rowsA s r0 x).card : ℕ) : ℝ) = 2 ^ K.card := by
    exact_mod_cast h2
  linarith

/-- The reading function of unit `j` for generic rows. -/
noncomputable def phiE (f : rowsA s r0 x → Fin N → ℝ) (j : Fin N) (v : ℝ) : ℝ :=
  if (1 / 2 : ℝ) < clamp01 (f ⟨s, rowsA_mem_s⟩ j) then clamp01 v else 1 - clamp01 v

lemma phiE_half (f : rowsA s r0 x → Fin N → ℝ) (j : Fin N) : IsHalf (phiE f j) := by
  unfold phiE
  split_ifs
  · exact Or.inl fun _ => rfl
  · exact Or.inr fun _ => rfl

/-- The fixed reading of the current row. -/
noncomputable def xvE (f : rowsA s r0 x → Fin N → ℝ) (j : Fin N) : ℝ :=
  max (clamp01 (f ⟨s, rowsA_mem_s⟩ j)) (1 - clamp01 (f ⟨s, rowsA_mem_s⟩ j))

lemma xE_glue (f : rowsA s r0 x → Fin N → ℝ) (g : {r // r ∉ rowsA s r0 x} → Fin N → ℝ) (j : Fin N) :
    xE (glueRows (rowsA s r0 x) f g) s j = xvE f j := by
  unfold xE xvE; rw [glueRows_of_mem _ f g rowsA_mem_s]

/-- **The effect subcube average.** -/
lemma effUnit_glue_s (f : rowsA s r0 x → Fin N → ℝ) (g : {r // r ∉ rowsA s r0 x} → Fin N → ℝ)
    {K : Finset (Fin N)} (hK : K.card + 1 < ham r0 s) (j : Fin N) :
    effUnit (tpmOf (flipP s (glueRows (rowsA s r0 x) f g))) Kᶜ s j (teW (glueRows (rowsA s r0 x) f g) s j) =
      (xvE f j + ∑ r ∈ RGE s r0 x K, phiE f j (g r j)) / 2 ^ K.card := by
  classical
  rw [effUnit_teW_eq, card_agree, card_compl_sub]
  push_cast
  congr 1
  rw [← sum_filter_add_sum_filter_not (agree Kᶜ s) (fun r => r ∈ rowsA s r0 x),
    agree_s_filter_rowsA hK, sum_singleton, ← xE_eq_pTe, xE_glue]
  congr 1
  unfold RGE
  rw [← sum_subtype_eq_sum_filter (fun r => pTe (glueRows (rowsA s r0 x) f g) s r j)]
  refine sum_congr rfl fun r _ => ?_
  unfold pTe phiE
  rw [glueRows_of_mem _ f g rowsA_mem_s, glueRows_of_not_mem _ f g r.2]

/-- The effect loss of unit `j`. -/
noncomputable def PsiE (f : rowsA s r0 x → Fin N → ℝ) (K : Finset (Fin N)) (j : Fin N)
    (c : {r // r ∉ rowsA s r0 x} → ℝ) : ℝ :=
  max ((xvE f j + ∑ r ∈ RGE s r0 x K, phiE f j (c r)) / 2 ^ K.card - (1 / 2 + 1 / 100000)) 0

def vE (K : Finset (Fin N)) : ℕ := if K.card = 1 then 0 else if K.card = 2 then 1 else 2

lemma PsiE_meas (f : rowsA s r0 x → Fin N → ℝ) (K : Finset (Fin N)) (j : Fin N) :
    Measurable (PsiE f K j) := by
  unfold PsiE
  exact (((measurable_const.add (Finset.measurable_sum _ fun r _ =>
    (phiE_half f j).meas.comp (measurable_pi_apply r))).div_const _).sub_const _).max measurable_const

lemma xvE_le (f : rowsA s r0 x → Fin N → ℝ) (j : Fin N) : xvE f j ≤ 1 :=
  max_le (clamp01_le_one _) (by linarith [clamp01_nonneg (f ⟨s, rowsA_mem_s⟩ j)])

lemma PsiE_mem (f : rowsA s r0 x → Fin N → ℝ) {K : Finset (Fin N)} (hK : K.card + 1 < ham r0 s)
    (j : Fin N) (c : {r // r ∉ rowsA s r0 x} → ℝ) : PsiE f K j c ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  refine ⟨le_max_right _ _, max_le ?_ (by norm_num)⟩
  have hc := card_RGE (x := x) hK
  have hx := xvE_le f j
  have hsum : ∑ r ∈ RGE s r0 x K, phiE f j (c r) ≤ (RGE s r0 x K).card := by
    calc _ ≤ ∑ _r ∈ RGE s r0 x K, (1 : ℝ) := sum_le_sum fun r _ => ((phiE_half f j).mem _).2
      _ = _ := by simp
  have h2k : (0 : ℝ) < 2 ^ K.card := by positivity
  have : (xvE f j + ∑ r ∈ RGE s r0 x K, phiE f j (c r)) / 2 ^ K.card ≤ 1 := by
    rw [div_le_one h2k]; linarith
  linarith

theorem PsiE_int_le (f : rowsA s r0 x → Fin N → ℝ) {K : Finset (Fin N)} (hK : K.card + 1 < ham r0 s)
    (hK1 : 1 ≤ K.card) (j : Fin N) (hx : 1 / 2 + 1 / 100000 ≤ xvE f j) :
    ∫ c, PsiE f K j c ∂colLawG (rowsA s r0 x) ≤ numRE (vE K) (xvE f j) := by
  classical
  have hc := card_RGE (x := x) hK
  have hx1 := xvE_le f j
  have hhalf : ∀ r : {r // r ∉ rowsA s r0 x}, IsHalf (phiE f j) := fun _ => phiE_half f j
  by_cases h1 : K.card = 1
  · rw [h1] at hc
    have hc1 : (RGE s r0 x K).card = 1 := by exact_mod_cast (by linarith : ((RGE s r0 x K).card : ℝ) = 1)
    obtain ⟨r1, hr1⟩ := card_eq_one.1 hc1
    have e : ∀ c : {r // r ∉ rowsA s r0 x} → ℝ, PsiE f K j c =
        max (phiE f j (c r1) - (2 * (1 / 2 + 1 / 100000) - xvE f j)) 0 / 2 := fun c => by
      unfold PsiE
      rw [hr1, sum_singleton, h1, pow_one]
      rw [← max_div_div_right (by norm_num : (0 : ℝ) ≤ 2), zero_div]
      congr 1; ring
    simp_rw [e]
    rw [integral_div]
    unfold colLawG
    rw [integral_pi_eval unif (g := fun v => max (phiE f j v - (2 * (1 / 2 + 1 / 100000) - xvE f j)) 0)
      (((phiE_half f j).meas.sub_const _).max measurable_const).aestronglyMeasurable r1]
    rw [unif_pos_part_half (phiE_half f j) (by linarith) (by linarith)]
    simp only [vE, if_pos h1, numRE]
    ring_nf; exact le_refl _
  · by_cases h2 : K.card = 2
    · rw [h2] at hc
      have hb := colLawG_pos_part_le (rowsA s r0 x) (RGE s r0 x K) (fun _ => phiE f j) hhalf
        (xvE f j) (1 / 2 + 1 / 100000) (1 / 8) K.card (by norm_num) (by rw [hc, h2]; norm_num)
      refine hb.trans (le_of_eq ?_)
      simp only [vE, if_neg h1, if_pos h2, numRE]
      rw [hc, h2]; ring_nf
    · have h3 : 3 ≤ K.card := by omega
      have h8 : (8 : ℝ) ≤ 2 ^ K.card := by
        have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h3; norm_num at this; linarith
      have hvar : ((RGE s r0 x K).card : ℝ) / (12 * 4 ^ K.card) ≤ (1021 / 10000) ^ 2 := by
        have h4 : (4 : ℝ) ^ K.card = 2 ^ K.card * 2 ^ K.card := by rw [← mul_pow]; norm_num
        rw [div_le_iff₀ (by positivity), h4, hc]
        nlinarith
      have hb := colLawG_pos_part_le (rowsA s r0 x) (RGE s r0 x K) (fun _ => phiE f j) hhalf
        (xvE f j) (1 / 2 + 1 / 100000) (1021 / 10000) K.card (by norm_num) hvar
      refine hb.trans ?_
      simp only [vE, if_neg h1, if_neg h2, numRE]
      gcongr
      have hM : (xvE f j + ((RGE s r0 x K).card : ℝ) / 2) / 2 ^ K.card =
          1 / 2 + (xvE f j - 1 / 2) / 2 ^ K.card := by
        rw [hc]; field_simp; ring
      rw [hM]
      have : (xvE f j - 1 / 2) / 2 ^ K.card ≤ (xvE f j - 1 / 2) / 8 :=
        div_le_div_of_nonneg_left (by linarith) (by norm_num) h8
      linarith

/-! ### One unit and one `K` -/

lemma unit_min_ge' {F y A ym ymB δ1 : ℝ} (hF : 0 < F) (hf : F ≤ ym) (hym : ym ≤ y) (hymB : ym ≤ ymB)
    (hA : 0 < A) (hδ : 0 ≤ δ1) :
    (Real.log (y / ymB) - 7 * δ1) / Real.log 2 - max (A - F) 0 / (F * Real.log 2) ≤
      min (Real.logb 2 (y / A)) ((max 0 (Real.log (y / ym)) - 7 * δ1) / Real.log 2) := by
  have hl2 := Real.log_pos one_lt_two
  have hy0 : 0 < y := by linarith
  have hym0 : 0 < ym := by linarith
  have hyB : 0 < ymB := by linarith
  set Ψ := max (A - F) 0 with hΨdef
  have hΨ0 : 0 ≤ Ψ := le_max_right _ _
  have e : (Real.log (y / ymB) - 7 * δ1) / Real.log 2 - Ψ / (F * Real.log 2) =
      ((Real.log (y / ymB) - 7 * δ1) - Ψ / F) / Real.log 2 := by
    field_simp
  rw [e]
  have hlog1 : Real.log (y / ymB) ≤ Real.log (y / ym) :=
    Real.log_le_log (div_pos hy0 hyB) (div_le_div_of_nonneg_left hy0.le hym0 hymB)
  refine le_min ?_ ?_
  · rw [Real.logb]
    apply div_le_div_of_nonneg_right _ hl2.le
    have h1 : Real.log A - Real.log ymB ≤ Real.log A - Real.log F := by
      have := Real.log_le_log hF (hf.trans hymB); linarith
    have h2 : Real.log A - Real.log F ≤ A / F - 1 := by
      rw [← Real.log_div hA.ne' hF.ne']; exact Real.log_le_sub_one_of_pos (by positivity)
    have h3 : A / F - 1 ≤ Ψ / F := by
      rw [div_sub_one hF.ne']; exact div_le_div_of_nonneg_right (le_max_left _ _) hF.le
    rw [Real.log_div hy0.ne' hyB.ne', Real.log_div hy0.ne' hA.ne']
    linarith
  · apply div_le_div_of_nonneg_right _ hl2.le
    have : 0 ≤ Ψ / F := by positivity
    linarith [le_max_right 0 (Real.log (y / ym))]

theorem K_bound_E (f : rowsA s r0 x → Fin N → ℝ) (g : {r // r ∉ rowsA s r0 x} → Fin N → ℝ)
    {K : Finset (Fin N)} (hK : K.card + 1 < ham r0 s) (hEX : glueRows (rowsA s r0 x) f g ∈ EX N s r0 x)
    {xmB δ1 ε : ℝ} (hxmB : rowMinU (xvE f) ≤ xmB) (hδ : 0 ≤ δ1)
    (hgood : ∑ j ∈ Kᶜ, (PsiE f K j (colsG (rowsA s r0 x) g j) -
      ∫ c, PsiE f K j c ∂colLawG (rowsA s r0 x)) < ε) :
    (∑ j ∈ Kᶜ, (Real.log (xvE f j / xmB) -
        (∫ c, PsiE f K j c ∂colLawG (rowsA s r0 x)) / (1 / 2 + 1 / 100000)) -
        ε / (1 / 2 + 1 / 100000) - 7 * δ1 * N) / Real.log 2 ≤
      ∑ j ∈ Kᶜ, min (Real.logb 2 (xE (glueRows (rowsA s r0 x) f g) s j /
          effUnit (tpmOf (flipP s (glueRows (rowsA s r0 x) f g))) Kᶜ s j
            (teW (glueRows (rowsA s r0 x) f g) s j)))
        (cpx (xE (glueRows (rowsA s r0 x) f g) s) (rowMinU (xE (glueRows (rowsA s r0 x) f g) s)) δ1 j) := by
  have hl2 := Real.log_pos one_lt_two
  have hg0 : xE (glueRows (rowsA s r0 x) f g) s = xvE f := funext fun j => xE_glue f g j
  rw [hg0]
  have hxge : ∀ j, (1 / 2 + 1 / 100000 : ℝ) ≤ xvE f j := fun j => by
    have := EX_xE_ge hEX j; rwa [xE_glue] at this
  have hN : 0 < N := by
    have : ham r0 s ≤ N := by
      unfold ham; exact (card_filter_le _ _).trans (by simp)
    omega
  have hmin_ge : (1 / 2 + 1 / 100000 : ℝ) ≤ rowMinU (xvE f) := le_rowMinU hxge hN
  have hunit : ∀ j, (Real.log (xvE f j / xmB) - 7 * δ1) / Real.log 2 -
      PsiE f K j (colsG (rowsA s r0 x) g j) / ((1 / 2 + 1 / 100000) * Real.log 2) ≤
      min (Real.logb 2 (xvE f j / effUnit (tpmOf (flipP s (glueRows (rowsA s r0 x) f g))) Kᶜ s j
            (teW (glueRows (rowsA s r0 x) f g) s j)))
        (cpx (xvE f) (rowMinU (xvE f)) δ1 j) := by
    intro j
    have hA : 0 < effUnit (tpmOf (flipP s (glueRows (rowsA s r0 x) f g))) Kᶜ s j
        (teW (glueRows (rowsA s r0 x) f g) s j) := by
      rw [effUnit_glue_s f g hK j]
      apply div_pos _ (by positivity)
      have : 0 ≤ ∑ r ∈ RGE s r0 x K, phiE f j (g r j) := sum_nonneg fun r _ => ((phiE_half f j).mem _).1
      linarith [hxge j]
    have h := unit_min_ge' (by norm_num) hmin_ge (rowMinU_le _ j) hxmB hA hδ
    have e : max (effUnit (tpmOf (flipP s (glueRows (rowsA s r0 x) f g))) Kᶜ s j
        (teW (glueRows (rowsA s r0 x) f g) s j) - (1 / 2 + 1 / 100000)) 0 =
        PsiE f K j (colsG (rowsA s r0 x) g j) := by
      rw [effUnit_glue_s f g hK j]; rfl
    rw [e] at h
    unfold cpx
    exact h
  have hsum := sum_le_sum fun j (_ : j ∈ Kᶜ) => hunit j
  refine le_trans ?_ hsum
  have hcard : ((Kᶜ).card : ℝ) ≤ N := by
    have := card_le_univ Kᶜ; simp only [Fintype.card_fin] at this; exact_mod_cast this
  have hP : ∑ j ∈ Kᶜ, PsiE f K j (colsG (rowsA s r0 x) g j) ≤
      ∑ j ∈ Kᶜ, ∫ c, PsiE f K j c ∂colLawG (rowsA s r0 x) + ε := by
    rw [sum_sub_distrib] at hgood; linarith
  have eR : ∑ j ∈ Kᶜ, ((Real.log (xvE f j / xmB) - 7 * δ1) / Real.log 2 -
      PsiE f K j (colsG (rowsA s r0 x) g j) / ((1 / 2 + 1 / 100000) * Real.log 2)) =
      (∑ j ∈ Kᶜ, Real.log (xvE f j / xmB) - 7 * δ1 * (Kᶜ).card -
        (∑ j ∈ Kᶜ, PsiE f K j (colsG (rowsA s r0 x) g j)) / (1 / 2 + 1 / 100000)) / Real.log 2 := by
    rw [sum_sub_distrib, ← sum_div, ← sum_div, sum_sub_distrib, sum_const, nsmul_eq_mul]
    field_simp
  rw [eR]
  apply div_le_div_of_nonneg_right _ hl2.le
  have hd : (∑ j ∈ Kᶜ, PsiE f K j (colsG (rowsA s r0 x) g j)) / (1 / 2 + 1 / 100000) ≤
      (∑ j ∈ Kᶜ, ∫ c, PsiE f K j c ∂colLawG (rowsA s r0 x) + ε) / (1 / 2 + 1 / 100000) :=
    div_le_div_of_nonneg_right hP (by norm_num)
  have h7 : 7 * δ1 * (Kᶜ).card ≤ 7 * δ1 * N := by
    have := mul_le_mul_of_nonneg_left hcard (by positivity : (0 : ℝ) ≤ 7 * δ1); linarith
  rw [sum_sub_distrib, ← sum_div]
  rw [add_div] at hd
  linarith

end Effect


/-! ### The lowest row-`s` cell is occupied -/

set_option maxHeartbeats 0 in
lemma exS200_facts : ueXhi (exSCells[200]'(by simp only [exSCells_len]; norm_num)) = ueXmBD ∧
    (1 / 2000 : ℚ) ≤ (exSCells[200]'(by simp only [exSCells_len]; norm_num)).a := by
  constructor <;> decide +kernel

lemma bottom_E {s r0 : State N} {x : Fin N} {w : Param N} (hw : w ∈ EX N s r0 x)
    (hN : 2000 * 400 < N) : rowMinU (xE w s) ≤ ((ueXmBD : ℚ) : ℝ) := by
  classical
  set i0 : Fin KS := ⟨200, by rw [KS_eq]; norm_num⟩
  obtain ⟨hhi, ha⟩ := exS200_facts
  have hpos : 0 < nS N i0 := by
    have h := nS_err N i0
    have ha' : (1 / 2000 : ℝ) ≤ ((cS i0).a : ℝ) := by
      have : (cS i0) = exSCells[200]'(by simp only [exSCells_len]; norm_num) := rfl
      rw [this]; have := (Rat.cast_le (K := ℝ)).2 ha; push_cast at this; exact this
    have hNr : (2000 * 400 : ℝ) < N := by exact_mod_cast hN
    have hKS : (KS : ℝ) = 400 := by rw [KS_eq]; norm_num
    have : (0 : ℝ) < nS N i0 := by
      have := (abs_le.1 h).1
      nlinarith
    exact_mod_cast this
  rw [← hw.2 i0] at hpos
  obtain ⟨k, hk⟩ := card_pos.1 hpos
  have hk' := (mem_filter.1 hk).2
  refine (rowMinU_le _ k).trans ?_
  have := (xE_cell hk').2
  have e : ueXhi (cS i0) = ueXmBD := hhi
  rw [e] at this
  exact this

/-! ### The effect-side leaf -/

lemma ueMarg_ge (v : ℕ) : (11 / 400 : ℚ) ≤ ueMarg v := by
  rcases v with _ | _ | v <;> simp only [ueMarg, ucMarg_e1, ucMarg_e2, ucMarg_e3] <;> norm_num

lemma ev_lin_E : ∀ᶠ N : ℕ in atTop,
    3 * (400 : ℝ) ^ 2 + 10 * DU N + 2 ≤ (N : ℝ) * (11 / 400 - 1 / 100 - 1 / 1000) := by
  have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 10000 by norm_num))
  filter_upwards [hev, eventually_ge_atTop (10 ^ 10)] with N h1 hN
  simp only [Function.comp, one_mul, add_zero, pow_one] at h1
  have hNr : (10 : ℝ) ^ 10 ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hl : Real.log N ≤ N / 10000 := by rw [div_lt_iff₀ hN0] at h1; linarith
  have hD := DU_le_log N
  nlinarith

lemma ev_DU3' : ∀ᶠ N : ℕ in atTop, 3 * (DU N + 2) ≤ N := by
  filter_upwards [ev_lin_C, eventually_ge_atTop 1] with N h hN
  have hD : (0 : ℝ) ≤ DU N := Nat.cast_nonneg _
  have : (3 * (DU N + 2) : ℝ) ≤ N := by nlinarith
  exact_mod_cast this

/-- **Leaf `smallE_cond`, proved.** -/
theorem smallE_cond' : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    ∀ f : rowsA s r0 x → Fin N → ℝ, ∀ g0 : {r // r ∉ rowsA s r0 x} → Fin N → ℝ,
      (glueRows (rowsA s r0 x) f g0 ∈ EX N s r0 x ∧ EXFacts N s r0 x (glueRows (rowsA s r0 x) f g0)) →
      rowsOutM (rowsA s r0 x) {g | ¬ ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N →
        8 * (DU N : ℝ) < ∑ j ∈ Kᶜ,
          min (Real.logb 2 (xE (glueRows (rowsA s r0 x) f g) s j /
              effUnit (tpmOf (flipP s (glueRows (rowsA s r0 x) f g))) Kᶜ s j
                (teW (glueRows (rowsA s r0 x) f g) s j)))
            (cpx (xE (glueRows (rowsA s r0 x) f g) s) (rowMinU (xE (glueRows (rowsA s r0 x) f g) s))
              (dU N (N - 1)) j)} ≤ 1 / 48 := by
  filter_upwards [ev_small_union, ev_N_dU_top, eventually_ge_atTop (2000 * 4159 + 1),
    ev_DU3', ev_lin_E, eventually_ge_atTop (10 ^ 7)] with N hU htop hNb h3 hlin hN7
  intro s r0 x hham f g0 hfix
  classical
  obtain ⟨δ1, hδ1⟩ : ∃ δ1 : ℝ, δ1 = dU N (N - 1) := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = N / 200 := ⟨_, rfl⟩
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hδ0 : 0 ≤ δ1 := hδ1 ▸ dU_nonneg _ _
  have hδN : (N : ℝ) * δ1 ≤ 1 / (2 * 10 ^ 6) := hδ1 ▸ htop
  obtain ⟨𝒦, h𝒦⟩ : ∃ 𝒦 : Finset (Finset (Fin N)), 𝒦 = (univ : Finset (Finset (Fin N))).filter
      (fun K => 1 ≤ K.card ∧ K.card < DU N) := ⟨_, rfl⟩
  have hK𝒦 : ∀ K ∈ 𝒦, K.card + 1 < ham r0 s := fun K hK => by
    rw [h𝒦] at hK; have := (mem_filter.1 hK).2.2; omega
  have hEXg : ∀ g, glueRows (rowsA s r0 x) f g ∈ EX N s r0 x := fun g =>
    ((EX_local s r0 x (w := glueRows (rowsA s r0 x) f g0) (w' := glueRows (rowsA s r0 x) f g) fun r hr => by
      rw [glueRows_of_mem (rowsA s r0 x) f g hr, glueRows_of_mem (rowsA s r0 x) f g0 hr]).1 hfix).1
  have hxm : rowMinU (xvE f) ≤ ((ueXmBD : ℚ) : ℝ) := by
    have h := bottom_E (hEXg g0) (by omega)
    have e : xE (glueRows (rowsA s r0 x) f g0) s = xvE f := funext fun j => xE_glue f g0 j
    rwa [e] at h
  obtain ⟨B, hB⟩ : ∃ B : Finset (Fin N) → Set ({r // r ∉ (rowsA s r0 x)} → Fin N → ℝ), B = fun K =>
    {g | ε ≤ |∑ j ∈ Kᶜ, (PsiE f K j (colsG (rowsA s r0 x) g j) - ∫ c, PsiE f K j c ∂colLawG (rowsA s r0 x))|} :=
    ⟨_, rfl⟩
  have hsub : {g | ¬ ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N →
      8 * (DU N : ℝ) < ∑ j ∈ Kᶜ,
        min (Real.logb 2 (xE (glueRows (rowsA s r0 x) f g) s j /
            effUnit (tpmOf (flipP s (glueRows (rowsA s r0 x) f g))) Kᶜ s j
              (teW (glueRows (rowsA s r0 x) f g) s j)))
          (cpx (xE (glueRows (rowsA s r0 x) f g) s) (rowMinU (xE (glueRows (rowsA s r0 x) f g) s)) δ1 j)} ⊆
      ⋃ K ∈ 𝒦, B K := by
    intro g hg
    by_contra hno
    simp only [Set.mem_iUnion, not_exists, hB, Set.mem_setOf_eq, not_le] at hno
    apply hg
    intro K hK1 hKD
    have hK : K ∈ 𝒦 := by rw [h𝒦]; exact mem_filter.2 ⟨mem_univ _, hK1, hKD⟩
    have hgood := (abs_lt.1 (hno K hK)).2
    have hKh := hK𝒦 K hK
    have hmain := K_bound_E f g hKh (hEXg g) hxm hδ0 hgood
    refine lt_of_lt_of_le ?_ hmain
    have hcells := effect_cells_sum (hEXg g) (vE K)
    have e0 : xE (glueRows (rowsA s r0 x) f g) s = xvE f := funext fun j => xE_glue f g j
    rw [e0] at hcells
    set T : Fin N → ℝ := fun j => Real.log (xvE f j / ((ueXmBD : ℚ) : ℝ)) -
      numRE (vE K) (xvE f j) / (1 / 2 + 1 / 100000) with hT
    have hT1 : ∀ j, T j ≤ 1 := fun j => by
      have hX : (1 / 2 : ℝ) ≤ ((ueXmBD : ℚ) : ℝ) := by unfold ueXmBD; norm_num
      have hx := EX_xE_ge (hEXg g) j
      rw [e0] at hx
      have h1 : Real.log (xvE f j / ((ueXmBD : ℚ) : ℝ)) ≤ xvE f j / ((ueXmBD : ℚ) : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
      have h2 : xvE f j / ((ueXmBD : ℚ) : ℝ) ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; have := xvE_le f j; linarith
      have h3 : 0 ≤ numRE (vE K) (xvE f j) := by
        rcases vE K with _ | _ | v <;> simp only [numRE] <;> positivity
      simp only [hT]
      have : 0 ≤ numRE (vE K) (xvE f j) / (1 / 2 + 1 / 100000) := by positivity
      linarith
    have hint : ∀ j ∈ Kᶜ, T j ≤ Real.log (xvE f j / ((ueXmBD : ℚ) : ℝ)) -
        (∫ c, PsiE f K j c ∂colLawG (rowsA s r0 x)) / (1 / 2 + 1 / 100000) := fun j _ => by
      have hx := EX_xE_ge (hEXg g) j
      rw [e0] at hx
      have := PsiE_int_le f hKh hK1 j hx
      simp only [hT]
      have := div_le_div_of_nonneg_right this (by norm_num : (0 : ℝ) ≤ 1 / 2 + 1 / 100000)
      linarith
    have hsplit := sum_compl_add_sum K T
    have hKsum : ∑ j ∈ K, T j ≤ K.card := by
      calc ∑ j ∈ K, T j ≤ ∑ _j ∈ K, (1 : ℝ) := sum_le_sum fun j _ => hT1 j
        _ = K.card := by simp
    have hKD' : (K.card : ℝ) ≤ DU N := by exact_mod_cast hKD.le
    have hmarg : ((11 / 400 : ℚ) : ℝ) ≤ (ueMarg (vE K) : ℝ) := by exact_mod_cast ueMarg_ge _
    have hsumC := sum_le_sum hint
    have hl2 := Real.log_pos one_lt_two
    have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have hKS : (KS : ℝ) = 400 := by rw [KS_eq]; norm_num
    rw [hKS] at hcells
    have hmargN := mul_le_mul_of_nonneg_left hmarg hN0.le
    push_cast at hmargN
    rw [lt_div_iff₀ hl2]
    have hδ7 : 7 * δ1 * N ≤ 1 := by nlinarith
    have hεf : ε / (1 / 2 + 1 / 100000) ≤ (N : ℝ) * (1 / 100) := by
      rw [hε, div_le_iff₀ (by norm_num)]; nlinarith
    have hD0 : (0 : ℝ) ≤ DU N := Nat.cast_nonneg _
    nlinarith
  rw [← hδ1]
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le 𝒦 B).trans ?_)
  have hpiece : ∀ K ∈ 𝒦, rowsOutM (rowsA s r0 x) (B K) ≤ ENNReal.ofReal (2 * Real.exp (-((N : ℝ) / 5000))) := by
    intro K hK
    have hKh := hK𝒦 K hK
    have hb := cols_hoeffding (rowsA s r0 x) Kᶜ (PsiE f K) (fun j => PsiE_meas f K j) (R := 1 / 2)
      (fun j c => PsiE_mem f hKh j c) (by rw [hε]; positivity : (0 : ℝ) ≤ ε)
    rw [hB]
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.2
    rw [sum_const, nsmul_eq_mul]
    have hc1 : (1 : ℝ) ≤ (Kᶜ).card := by
      have : 0 < (Kᶜ).card := by
        rw [card_compl, Fintype.card_fin]
        rw [h𝒦] at hK; have := (mem_filter.1 hK).2.2; omega
      exact_mod_cast this
    have hc2 : ((Kᶜ).card : ℝ) ≤ N := by
      have := card_le_univ Kᶜ; simp only [Fintype.card_fin] at this; exact_mod_cast this
    set cK : ℝ := ((Kᶜ).card : ℝ)
    have e : -2 * ε ^ 2 / (cK * (1 / 2) ^ 2) = -((N : ℝ) * ((N : ℝ) / cK)) / 5000 := by
      rw [hε]; field_simp; ring
    rw [e]
    have h1 : (1 : ℝ) ≤ (N : ℝ) / cK := by rw [le_div_iff₀ (by linarith)]; linarith
    have : (N : ℝ) ≤ (N : ℝ) * ((N : ℝ) / cK) := by nlinarith
    linarith
  have hcard : (𝒦.card : ℝ) ≤ DU N * (N : ℝ) ^ DU N := by
    have hsub𝒦 : 𝒦 ⊆ (univ : Finset (Finset (Fin N))).filter (fun K => K.card < DU N) := by
      intro K hK
      rw [h𝒦] at hK
      simp only [mem_filter, mem_univ, true_and] at hK ⊢
      exact hK.2
    have := (card_le_card hsub𝒦).trans (card_small_sets (DU N) (by omega))
    exact_mod_cast this
  calc ∑ K ∈ 𝒦, rowsOutM (rowsA s r0 x) (B K) ≤ ∑ _K ∈ 𝒦, ENNReal.ofReal (2 * Real.exp (-((N : ℝ) / 5000))) :=
        sum_le_sum hpiece
    _ = ENNReal.ofReal (𝒦.card * (2 * Real.exp (-((N : ℝ) / 5000)))) := by
        rw [sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg (α := ℝ) 𝒦.card), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (1 / 48) := by
        apply ENNReal.ofReal_le_ofReal
        refine le_trans ?_ hU
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 1 / 48 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp

end Census
end IIT
