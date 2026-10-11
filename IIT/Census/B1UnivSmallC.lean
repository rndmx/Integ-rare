/-
Census, B1 lower bound, leaf `phi_univ_ge_EX`: the cause-side small-cut sums (`smallC_cond`).

For a small set `K` (`1 ≤ |K| < D`, `K ≠ {x}`, `|K| < ham(r0, s)`), the subcube of `r0` free on `K`
contains the fixed rows `r0` (and `r0^x` iff `x ∈ K`) and `2^|K| - 1 - [x ∈ K]` generic rows `RGC K`.
`ΨC K j` is the loss `max(A_j(K) - f, 0)` as a function of the generic column `j`.
-/
import IIT.Census.B1UnivSmallA

set_option maxRecDepth 100000

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

variable {N : ℕ}

section Cause

variable (s r0 : State N) (x : Fin N)

/-- The generic rows of the subcube of `r0` free on `K`. -/
noncomputable def RGC (K : Finset (Fin N)) : Finset {r // r ∉ rowsA s r0 x} :=
  (agree (univ \ K) r0).subtype fun r => r ∉ rowsA s r0 x

variable {s r0 x}

lemma flip_mem_agree_iff (K : Finset (Fin N)) : flipAt x r0 ∈ agree (univ \ K) r0 ↔ x ∈ K := by
  rw [mem_agree]
  constructor
  · intro h
    by_contra hx
    have := h x (mem_sdiff.2 ⟨mem_univ x, hx⟩)
    simp [flipAt] at this
  · intro hx j hj
    have hjx : j ≠ x := fun e => (mem_sdiff.1 hj).2 (e ▸ hx)
    simp [flipAt, Function.update_of_ne hjx]

lemma s_not_mem_agree {K : Finset (Fin N)} (hK : K.card < ham r0 s) : s ∉ agree (univ \ K) r0 := by
  intro h
  have h' : s ∈ agree Kᶜ r0 := by rwa [compl_eq_univ_sdiff]
  have := ham_le_card_of_mem_agree h'
  rw [ham_comm] at this
  omega

lemma agree_filter_rowsA {K : Finset (Fin N)} (hK : K.card < ham r0 s) :
    (agree (univ \ K) r0).filter (fun r => r ∈ rowsA s r0 x) =
      if x ∈ K then {r0, flipAt x r0} else {r0} := by
  ext r
  simp only [mem_filter, rowsA, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hr, h | h | h⟩
    · split_ifs <;> simp [h]
    · subst h
      have hx := (flip_mem_agree_iff K).1 hr
      simp [hx]
    · subst h; exact absurd hr (s_not_mem_agree hK)
  · intro h
    split_ifs at h with hx
    · simp only [mem_insert, mem_singleton] at h
      rcases h with h | h
      · subst h; exact ⟨self_mem_agree _ _, Or.inl rfl⟩
      · subst h; exact ⟨(flip_mem_agree_iff K).2 hx, Or.inr (Or.inl rfl)⟩
    · simp only [mem_singleton] at h
      subst h; exact ⟨self_mem_agree _ _, Or.inl rfl⟩

lemma card_RGC {K : Finset (Fin N)} (hK : K.card < ham r0 s) :
    ((RGC s r0 x K).card : ℝ) = 2 ^ K.card - 1 - (if x ∈ K then 1 else 0) := by
  have h1 : (RGC s r0 x K).card = ((agree (univ \ K) r0).filter fun r => r ∉ rowsA s r0 x).card :=
    card_subtype _ _
  have h2 := card_filter_add_card_filter_not (s := agree (univ \ K) r0) (fun r => r ∈ rowsA s r0 x)
  rw [agree_filter_rowsA hK, card_agree, card_univ_sdiff_sub] at h2
  have hne : r0 ≠ flipAt x r0 := (flipAt_ne x r0).symm
  have h3 : ((if x ∈ K then ({r0, flipAt x r0} : Finset (State N)) else {r0}).card : ℝ) =
      1 + (if x ∈ K then 1 else 0) := by
    split_ifs
    · rw [card_pair hne]; norm_num
    · rw [card_singleton]; norm_num
  rw [h1]
  have h2' : (((if x ∈ K then ({r0, flipAt x r0} : Finset (State N)) else {r0}).card : ℕ) : ℝ) +
      ((((agree (univ \ K) r0).filter fun r => r ∉ rowsA s r0 x).card : ℕ) : ℝ) = 2 ^ K.card := by
    exact_mod_cast h2
  rw [h3] at h2'
  linarith

/-- The fixed values of the cause side. -/
noncomputable def yvC (f : rowsA s r0 x → Fin N → ℝ) (j : Fin N) : ℝ :=
  clamp01 (f ⟨r0, rowsA_mem_r0⟩ j)

noncomputable def UvC (f : rowsA s r0 x → Fin N → ℝ) (j : Fin N) : ℝ :=
  clamp01 (f ⟨flipAt x r0, rowsA_mem_flip⟩ j)

/-- **The subcube sum, split into fixed and generic rows.** -/
lemma sum_agree_glue (f : rowsA s r0 x → Fin N → ℝ) (g : {r // r ∉ rowsA s r0 x} → Fin N → ℝ)
    {K : Finset (Fin N)} (hK : K.card < ham r0 s) (j : Fin N) :
    ∑ r ∈ agree (univ \ K) r0, clamp01 (glueRows (rowsA s r0 x) f g r j) =
      yvC f j + (if x ∈ K then UvC f j else 0) + ∑ r ∈ RGC s r0 x K, clamp01 (g r j) := by
  classical
  rw [← sum_filter_add_sum_filter_not (agree (univ \ K) r0) (fun r => r ∈ rowsA s r0 x),
    agree_filter_rowsA hK]
  have e3 : ∑ r ∈ (agree (univ \ K) r0).filter (fun r => r ∉ rowsA s r0 x),
      clamp01 (glueRows (rowsA s r0 x) f g r j) = ∑ r ∈ RGC s r0 x K, clamp01 (g r j) := by
    unfold RGC
    rw [← sum_subtype_eq_sum_filter (fun r => clamp01 (glueRows (rowsA s r0 x) f g r j))]
    refine sum_congr rfl fun r _ => ?_
    rw [glueRows_of_not_mem _ f g r.2]
  rw [e3]
  have hne : r0 ≠ flipAt x r0 := (flipAt_ne x r0).symm
  have g0 : glueRows (rowsA s r0 x) f g r0 = f ⟨r0, rowsA_mem_r0⟩ := glueRows_of_mem _ f g _
  have g1 : glueRows (rowsA s r0 x) f g (flipAt x r0) = f ⟨flipAt x r0, rowsA_mem_flip⟩ :=
    glueRows_of_mem _ f g _
  split_ifs
  · rw [sum_pair hne, g0, g1]; rfl
  · rw [sum_singleton, g0, add_zero]; rfl

lemma cmean_glue (f : rowsA s r0 x → Fin N → ℝ) (g : {r // r ∉ rowsA s r0 x} → Fin N → ℝ)
    {K : Finset (Fin N)} (hK : K.card < ham r0 s) (j : Fin N) :
    cmean (glueRows (rowsA s r0 x) f g) (univ \ K) r0 j =
      (yvC f j + (if x ∈ K then UvC f j else 0) + ∑ r ∈ RGC s r0 x K, clamp01 (g r j)) / 2 ^ K.card := by
  unfold cmean
  rw [card_univ_sdiff_sub, sum_agree_glue f g hK j]

/-- The loss of unit `j` as a function of the generic column. -/
noncomputable def PsiC (f : rowsA s r0 x → Fin N → ℝ) (K : Finset (Fin N)) (j : Fin N)
    (c : {r // r ∉ rowsA s r0 x} → ℝ) : ℝ :=
  max ((yvC f j + (if x ∈ K then UvC f j else 0) + ∑ r ∈ RGC s r0 x K, clamp01 (c r)) / 2 ^ K.card -
    1001 / 2000) 0

/-- The loss variant of `K`. -/
def vC (x : Fin N) (K : Finset (Fin N)) : ℕ :=
  if K.card = 1 then 0 else if K.card = 2 then (if x ∈ K then 1 else 2) else 3

lemma PsiC_meas (f : rowsA s r0 x → Fin N → ℝ) (K : Finset (Fin N)) (j : Fin N) :
    Measurable (PsiC f K j) := by
  unfold PsiC
  exact (((measurable_const.add (Finset.measurable_sum _ fun r _ =>
    clamp01_measurable.comp (measurable_pi_apply r))).div_const _).sub_const _).max measurable_const

lemma PsiC_mem (f : rowsA s r0 x → Fin N → ℝ) {K : Finset (Fin N)} (hK : K.card < ham r0 s)
    (j : Fin N) (c : {r // r ∉ rowsA s r0 x} → ℝ) : PsiC f K j c ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  refine ⟨le_max_right _ _, max_le ?_ (by norm_num)⟩
  have hc := card_RGC (x := x) hK
  have hy : yvC f j ≤ 1 := clamp01_le_one _
  have hU : (if x ∈ K then UvC f j else 0) ≤ if x ∈ K then 1 else 0 := by
    split_ifs
    · exact clamp01_le_one _
    · exact le_rfl
  have hsum : ∑ r ∈ RGC s r0 x K, clamp01 (c r) ≤ (RGC s r0 x K).card := by
    calc _ ≤ ∑ _r ∈ RGC s r0 x K, (1 : ℝ) := sum_le_sum fun r _ => clamp01_le_one _
      _ = _ := by simp
  have h2k : (0 : ℝ) < 2 ^ K.card := by positivity
  have : (yvC f j + (if x ∈ K then UvC f j else 0) + ∑ r ∈ RGC s r0 x K, clamp01 (c r)) / 2 ^ K.card ≤ 1 := by
    rw [div_le_one h2k]; linarith
  linarith

/-- **The expected loss.** -/
theorem PsiC_int_le (f : rowsA s r0 x → Fin N → ℝ) {K : Finset (Fin N)} (hK : K.card < ham r0 s)
    (hK1 : 1 ≤ K.card) (hKx : K ≠ {x}) (j : Fin N) (hy : 1001 / 2000 ≤ yvC f j) :
    ∫ c, PsiC f K j c ∂colLawG (rowsA s r0 x) ≤ numRC (vC x K) (yvC f j) (UvC f j) := by
  classical
  have hc := card_RGC (x := x) hK
  have hy1 : yvC f j ≤ 1 := clamp01_le_one _
  have hU0 : 0 ≤ UvC f j := clamp01_nonneg _
  have hU1 : UvC f j ≤ 1 := clamp01_le_one _
  have hhalf : ∀ r : {r // r ∉ rowsA s r0 x}, IsHalf (fun v => clamp01 v) := fun _ => Or.inl fun _ => rfl
  by_cases h1 : K.card = 1
  · -- one generic row
    have hxK : x ∉ K := by
      intro hx
      obtain ⟨a, ha⟩ := card_eq_one.1 h1
      rw [ha, mem_singleton] at hx
      exact hKx (by rw [ha, hx])
    rw [if_neg hxK, h1] at hc
    have hc1 : (RGC s r0 x K).card = 1 := by exact_mod_cast (by linarith : ((RGC s r0 x K).card : ℝ) = 1)
    obtain ⟨r1, hr1⟩ := card_eq_one.1 hc1
    have e : ∀ c : {r // r ∉ rowsA s r0 x} → ℝ, PsiC f K j c =
        max (clamp01 (c r1) - (2 * (1001 / 2000) - yvC f j)) 0 / 2 := fun c => by
      unfold PsiC
      rw [if_neg hxK, hr1, sum_singleton, h1, pow_one]
      rw [← max_div_div_right (by norm_num : (0 : ℝ) ≤ 2), zero_div]
      congr 1; ring
    simp_rw [e]
    rw [integral_div]
    unfold colLawG
    rw [integral_pi_eval unif (g := fun v => max (clamp01 v - (2 * (1001 / 2000) - yvC f j)) 0)
      ((clamp01_measurable.sub_const _).max measurable_const).aestronglyMeasurable r1]
    rw [unif_pos_part_half (φ := clamp01) (Or.inl fun _ => rfl) (by linarith) (by linarith)]
    simp only [vC, if_pos h1, numRC]
    ring_nf; exact le_refl _
  · by_cases h2 : K.card = 2
    · by_cases hxK : x ∈ K
      · -- two generic rows
        rw [if_pos hxK, h2] at hc
        have hb := colLawG_pos_part_le (rowsA s r0 x) (RGC s r0 x K) (fun _ v => clamp01 v) hhalf
          (yvC f j + UvC f j) (1001 / 2000) (1021 / 10000) K.card (by norm_num)
          (by rw [hc, h2]; norm_num)
        have e : ∀ c, PsiC f K j c = max ((yvC f j + UvC f j + ∑ r ∈ RGC s r0 x K, clamp01 (c r)) / 2 ^ K.card -
            1001 / 2000) 0 := fun c => by unfold PsiC; rw [if_pos hxK]
        simp_rw [e]
        refine hb.trans (le_of_eq ?_)
        simp only [vC, if_neg h1, if_pos h2, if_pos hxK, numRC]
        rw [hc, h2]; ring_nf
      · rw [if_neg hxK, h2] at hc
        have hb := colLawG_pos_part_le (rowsA s r0 x) (RGC s r0 x K) (fun _ v => clamp01 v) hhalf
          (yvC f j) (1001 / 2000) (1 / 8) K.card (by norm_num)
          (by rw [hc, h2]; norm_num)
        have e : ∀ c, PsiC f K j c = max ((yvC f j + ∑ r ∈ RGC s r0 x K, clamp01 (c r)) / 2 ^ K.card -
            1001 / 2000) 0 := fun c => by unfold PsiC; rw [if_neg hxK, add_zero]
        simp_rw [e]
        refine hb.trans (le_of_eq ?_)
        simp only [vC, if_neg h1, if_pos h2, if_neg hxK, numRC]
        rw [hc, h2]; ring_nf
    · -- three or more
      have h3 : 3 ≤ K.card := by omega
      have h8 : (8 : ℝ) ≤ 2 ^ K.card := by
        have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h3; norm_num at this; linarith
      set b : ℝ := if x ∈ K then 1 else 0 with hbdef
      have hb01 : 0 ≤ b ∧ b ≤ 1 := by rw [hbdef]; split_ifs <;> norm_num
      have hcard : ((RGC s r0 x K).card : ℝ) ≤ 2 ^ K.card := by rw [hc]; linarith
      have hvar : ((RGC s r0 x K).card : ℝ) / (12 * 4 ^ K.card) ≤ (1021 / 10000) ^ 2 := by
        have h4 : (4 : ℝ) ^ K.card = 2 ^ K.card * 2 ^ K.card := by
          rw [← mul_pow]; norm_num
        rw [div_le_iff₀ (by positivity), h4]
        nlinarith
      have hbU : (if x ∈ K then UvC f j else 0) = b * UvC f j := by
        rw [hbdef]; split_ifs <;> ring
      have hb := colLawG_pos_part_le (rowsA s r0 x) (RGC s r0 x K) (fun _ v => clamp01 v) hhalf
        (yvC f j + b * UvC f j) (1001 / 2000) (1021 / 10000) K.card (by norm_num) hvar
      have e : ∀ c, PsiC f K j c = max ((yvC f j + b * UvC f j + ∑ r ∈ RGC s r0 x K, clamp01 (c r)) /
          2 ^ K.card - 1001 / 2000) 0 := fun c => by unfold PsiC; rw [hbU]
      simp_rw [e]
      refine hb.trans ?_
      simp only [vC, if_neg h1, if_neg h2, numRC]
      gcongr
      -- the mean term
      have hM : (yvC f j + b * UvC f j + ((RGC s r0 x K).card : ℝ) / 2) / 2 ^ K.card =
          1 / 2 + (yvC f j + b * UvC f j - 1 / 2 - b / 2) / 2 ^ K.card := by
        rw [hc]; field_simp; ring
      rw [hM]
      set M := max (max (yvC f j + UvC f j - 1) (yvC f j - 1 / 2)) 0
      have hM1 : yvC f j + b * UvC f j - 1 / 2 - b / 2 ≤ M := by
        rcases hb01 with ⟨hb0, hb1⟩
        rw [hbdef] at hb0 hb1 ⊢
        split_ifs
        · exact le_trans (by linarith) (le_trans (le_max_left _ _) (le_max_left _ _))
        · exact le_trans (by linarith) (le_trans (le_max_right _ _) (le_max_left _ _))
      have hM0 : 0 ≤ M := le_max_right _ _
      have : (yvC f j + b * UvC f j - 1 / 2 - b / 2) / 2 ^ K.card ≤ M / 8 := by
        calc (yvC f j + b * UvC f j - 1 / 2 - b / 2) / 2 ^ K.card ≤ M / 2 ^ K.card :=
              div_le_div_of_nonneg_right hM1 (by positivity)
          _ ≤ M / 8 := div_le_div_of_nonneg_left hM0 (by norm_num) h8
      linarith


/-! ### One unit: `min(λ, c') ≥ c'' - Ψ/(f ln 2)` -/

lemma unit_min_ge {y A ym ymB δ1 : ℝ} (hf : 1001 / 2000 ≤ ym) (hym : ym ≤ y) (hymB : ym ≤ ymB)
    (hA : 0 < A) (hδ : 0 ≤ δ1) :
    (Real.log (y / ymB) - 7 * δ1) / Real.log 2 - max (A - 1001 / 2000) 0 / (1001 / 2000 * Real.log 2) ≤
      min (Real.logb 2 (y / A)) ((max 0 (Real.log (y / ym)) - 7 * δ1) / Real.log 2) := by
  have hl2 := Real.log_pos one_lt_two
  have hy0 : 0 < y := by linarith
  have hym0 : 0 < ym := by linarith
  have hyB : 0 < ymB := by linarith
  set Ψ := max (A - 1001 / 2000) 0 with hΨdef
  have hΨ0 : 0 ≤ Ψ := le_max_right _ _
  have e : (Real.log (y / ymB) - 7 * δ1) / Real.log 2 - Ψ / (1001 / 2000 * Real.log 2) =
      ((Real.log (y / ymB) - 7 * δ1) - Ψ / (1001 / 2000)) / Real.log 2 := by
    field_simp
  rw [e]
  have hlog1 : Real.log (y / ymB) ≤ Real.log (y / ym) :=
    Real.log_le_log (div_pos hy0 hyB) (div_le_div_of_nonneg_left hy0.le hym0 hymB)
  refine le_min ?_ ?_
  · rw [Real.logb]
    apply div_le_div_of_nonneg_right _ hl2.le
    have h1 : Real.log A - Real.log ymB ≤ Real.log A - Real.log (1001 / 2000) := by
      have := Real.log_le_log (by norm_num) (hf.trans hymB); linarith
    have h2 : Real.log A - Real.log (1001 / 2000) ≤ A / (1001 / 2000) - 1 := by
      rw [← Real.log_div hA.ne' (by norm_num)]; exact Real.log_le_sub_one_of_pos (by positivity)
    have h3 : A / (1001 / 2000) - 1 ≤ Ψ / (1001 / 2000) := by
      rw [div_sub_one (by norm_num)]; exact div_le_div_of_nonneg_right (le_max_left _ _) (by norm_num)
    rw [Real.log_div hy0.ne' hyB.ne', Real.log_div hy0.ne' hA.ne']
    linarith
  · apply div_le_div_of_nonneg_right _ hl2.le
    have : 0 ≤ Ψ / (1001 / 2000) := by positivity
    linarith [le_max_right 0 (Real.log (y / ym))]

lemma numRC_nonneg (v : ℕ) (y u : ℝ) : 0 ≤ numRC v y u := by
  rcases v with _ | _ | _ | v <;> simp only [numRC] <;> positivity

/-! ### One set `K` -/

/-- **The small-cut sum of one `K` on the good event.** -/
theorem K_bound_C (f : rowsA s r0 x → Fin N → ℝ) (g : {r // r ∉ rowsA s r0 x} → Fin N → ℝ)
    {K : Finset (Fin N)} (hK : K.card < ham r0 s) (hEX : glueRows (rowsA s r0 x) f g ∈ EX N s r0 x)
    {ymB δ1 ε : ℝ} (hymB : rowMinU (yvC f) ≤ ymB) (hδ : 0 ≤ δ1)
    (hgood : ∑ j ∈ Kᶜ, (PsiC f K j (colsG (rowsA s r0 x) g j) -
      ∫ c, PsiC f K j c ∂colLawG (rowsA s r0 x)) < ε) :
    (∑ j ∈ Kᶜ, (Real.log (yvC f j / ymB) - (∫ c, PsiC f K j c ∂colLawG (rowsA s r0 x)) / (1001 / 2000)) -
        ε / (1001 / 2000) - 7 * δ1 * N) / Real.log 2 ≤
      ∑ j ∈ Kᶜ, min (Real.logb 2 (clamp01 (glueRows (rowsA s r0 x) f g r0 j) /
          cmean (glueRows (rowsA s r0 x) f g) (univ \ K) r0 j))
        (cpx (fun j => clamp01 (glueRows (rowsA s r0 x) f g r0 j))
          (rowMinU fun j => clamp01 (glueRows (rowsA s r0 x) f g r0 j)) δ1 j) := by
  have hl2 := Real.log_pos one_lt_two
  have hg0 : ∀ j, clamp01 (glueRows (rowsA s r0 x) f g r0 j) = yvC f j := fun j => by
    rw [glueRows_of_mem _ f g rowsA_mem_r0]; rfl
  simp_rw [hg0]
  have hyge : ∀ j, (1001 / 2000 : ℝ) ≤ yvC f j := fun j => by
    have := EX_y_ge hEX j; rwa [hg0] at this
  have hN : 0 < N := by
    have : ham r0 s ≤ N := by
      unfold ham; exact (card_filter_le _ _).trans (by simp)
    omega
  have hmin_ge : (1001 / 2000 : ℝ) ≤ rowMinU (yvC f) := le_rowMinU hyge hN
  -- per unit
  have hunit : ∀ j, (Real.log (yvC f j / ymB) - 7 * δ1) / Real.log 2 -
      PsiC f K j (colsG (rowsA s r0 x) g j) / (1001 / 2000 * Real.log 2) ≤
      min (Real.logb 2 (yvC f j / cmean (glueRows (rowsA s r0 x) f g) (univ \ K) r0 j))
        (cpx (yvC f) (rowMinU (yvC f)) δ1 j) := by
    intro j
    have hA : 0 < cmean (glueRows (rowsA s r0 x) f g) (univ \ K) r0 j := by
      rw [cmean_glue f g hK j]
      apply div_pos _ (by positivity)
      have : 0 ≤ ∑ r ∈ RGC s r0 x K, clamp01 (g r j) := sum_nonneg fun r _ => clamp01_nonneg _
      have : 0 ≤ (if x ∈ K then UvC f j else 0) := by split_ifs <;> [exact clamp01_nonneg _; exact le_rfl]
      linarith [hyge j]
    have h := unit_min_ge hmin_ge (rowMinU_le _ j) hymB hA hδ
    have e : max (cmean (glueRows (rowsA s r0 x) f g) (univ \ K) r0 j - 1001 / 2000) 0 =
        PsiC f K j (colsG (rowsA s r0 x) g j) := by
      rw [cmean_glue f g hK j]; rfl
    rw [e] at h
    unfold cpx
    exact h
  have hsum := sum_le_sum fun j (_ : j ∈ Kᶜ) => hunit j
  refine le_trans ?_ hsum
  have hcard : ((Kᶜ).card : ℝ) ≤ N := by
    have := card_le_univ Kᶜ; simp only [Fintype.card_fin] at this; exact_mod_cast this
  have hP : ∑ j ∈ Kᶜ, PsiC f K j (colsG (rowsA s r0 x) g j) ≤
      ∑ j ∈ Kᶜ, ∫ c, PsiC f K j c ∂colLawG (rowsA s r0 x) + ε := by
    rw [sum_sub_distrib] at hgood; linarith
  have eR : ∑ j ∈ Kᶜ, ((Real.log (yvC f j / ymB) - 7 * δ1) / Real.log 2 -
      PsiC f K j (colsG (rowsA s r0 x) g j) / (1001 / 2000 * Real.log 2)) =
      (∑ j ∈ Kᶜ, Real.log (yvC f j / ymB) - 7 * δ1 * (Kᶜ).card -
        (∑ j ∈ Kᶜ, PsiC f K j (colsG (rowsA s r0 x) g j)) / (1001 / 2000)) / Real.log 2 := by
    rw [sum_sub_distrib, ← sum_div, ← sum_div, sum_sub_distrib, sum_const, nsmul_eq_mul]
    field_simp
  rw [eR]
  apply div_le_div_of_nonneg_right _ hl2.le
  have hd : (∑ j ∈ Kᶜ, PsiC f K j (colsG (rowsA s r0 x) g j)) / (1001 / 2000) ≤
      (∑ j ∈ Kᶜ, ∫ c, PsiC f K j c ∂colLawG (rowsA s r0 x) + ε) / (1001 / 2000) :=
    div_le_div_of_nonneg_right hP (by norm_num)
  have h7 : 7 * δ1 * (Kᶜ).card ≤ 7 * δ1 * N := by
    have := mul_le_mul_of_nonneg_left hcard (by positivity : (0 : ℝ) ≤ 7 * δ1); linarith
  rw [sum_sub_distrib, ← sum_div]
  rw [add_div] at hd
  linarith

end Cause

end Census
end IIT
