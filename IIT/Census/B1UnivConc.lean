/-
Census, B1 lower bound, leaf `phi_univ_ge_EX`: the subcube concentration fields `concC`, `concE` of
`UnivGood` hold with conditional probability `1 - O(N 2^N e^{-N²/2})` given the fixed rows.

* `rows_hoeffding` : Hoeffding for one column over a set of generic rows (law `rowsOutM`).
* `subcube_dev`    : a subcube average of `2^d` rows, at most `|A| ≤ 3` of them fixed, deviates from `1/2`
                     by more than `δ` (with `2^d δ ≥ 3`) with probability `≤ 2 e^{-2^d δ²/2}`.
* `conc_union`     : the union over `(j, C)`.
-/
import IIT.Census.B1UnivMain

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

variable {N : ℕ}

/-- **Hoeffding for one column over generic rows.** -/
lemma rows_hoeffding (A : Finset (State N)) (RG : Finset {r // r ∉ A}) (j : Fin N) {φ : ℝ → ℝ}
    (hφm : Measurable φ) (hφ : ∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) (hφi : ∫ v, φ v ∂unif = 1 / 2)
    {ε : ℝ} (hε : 0 ≤ ε) :
    rowsOutM A {g | ε ≤ |∑ r ∈ RG, (φ (g r j) - 1 / 2)|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * ε ^ 2 / RG.card)) := by
  have hφj : Measurable fun v : Fin N → ℝ => φ (v j) := hφm.comp (measurable_pi_apply j)
  have hind : iIndepFun (fun (r : {r // r ∉ A}) (g : {r // r ∉ A} → Fin N → ℝ) => φ (g r j))
      (rowsOutM A) := by
    unfold rowsOutM
    exact iIndepFun_pi (X := fun (_ : {r // r ∉ A}) (v : Fin N → ℝ) => φ (v j))
      fun _ => hφj.aemeasurable
  have hmeas : ∀ r, AEMeasurable (fun g : {r // r ∉ A} → Fin N → ℝ => φ (g r j)) (rowsOutM A) :=
    fun r => (hφj.comp (measurable_pi_apply r)).aemeasurable
  have hb : ∀ r ∈ RG, ∀ᵐ g ∂(rowsOutM A), φ (g r j) ∈ Set.Icc 0 ((fun _ => (1 : ℝ)) r) :=
    fun r _ => ae_of_all _ fun g => hφ _
  have h := hoeffding_abs (μ := rowsOutM A) (X := fun r g => φ (g r j)) RG hind hmeas hb hε
  have hint : ∀ r, ∫ g, φ (g r j) ∂(rowsOutM A) = 1 / 2 := by
    intro r
    unfold rowsOutM
    rw [integral_pi_eval (rowM N) (g := fun v : Fin N → ℝ => φ (v j)) hφj.aestronglyMeasurable r]
    unfold rowM
    rw [integral_pi_eval unif hφm.aestronglyMeasurable j, hφi]
  simp only [hint, one_pow, sum_const, nsmul_eq_mul, mul_one] at h
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal h

/-- **A subcube average with at most three fixed rows.** -/
lemma subcube_dev (A : Finset (State N)) (hA : A.card ≤ 3) (R : Finset (State N)) {d : ℕ}
    (hR : R.card = 2 ^ d) (j : Fin N) {φ : ℝ → ℝ} (hφm : Measurable φ)
    (hφ : ∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) (hφi : ∫ v, φ v ∂unif = 1 / 2)
    (F : A → ℝ) (hF : ∀ r, F r ∈ Set.Icc (0 : ℝ) 1) {δ : ℝ} (hδ : 3 ≤ 2 ^ d * δ) :
    rowsOutM A {g | δ < |(∑ r ∈ R, (if h : r ∈ A then F ⟨r, h⟩ else φ (g ⟨r, h⟩ j))) / 2 ^ d - 1 / 2|} ≤
      ENNReal.ofReal (2 * Real.exp (-(2 ^ d * δ ^ 2) / 2)) := by
  classical
  set RG : Finset {r // r ∉ A} := R.subtype fun r => r ∉ A with hRG
  set RA := R.filter fun r => r ∈ A with hRA
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  have hRAc : (RA.card : ℝ) ≤ 3 := by
    have : RA.card ≤ A.card := card_le_card fun r hr => (mem_filter.1 hr).2
    exact_mod_cast this.trans hA
  have hcard : (RA.card : ℝ) + RG.card = 2 ^ d := by
    have h1 : RG.card = (R.filter fun r => r ∉ A).card := card_subtype _ _
    have h2 := card_filter_add_card_filter_not (s := R) (fun r => r ∈ A)
    rw [hR] at h2
    have : RA.card + RG.card = 2 ^ d := by rw [h1]; exact h2
    exact_mod_cast this
  -- the split of the sum
  have hsplit : ∀ g : {r // r ∉ A} → Fin N → ℝ,
      ∑ r ∈ R, (if h : r ∈ A then F ⟨r, h⟩ else φ (g ⟨r, h⟩ j)) - 2 ^ d / 2 =
        ∑ r ∈ RA, ((if h : r ∈ A then F ⟨r, h⟩ else 0) - 1 / 2) + ∑ r ∈ RG, (φ (g r j) - 1 / 2) := by
    intro g
    have e1 := sum_filter_add_sum_filter_not R (fun r => r ∈ A)
      (fun r => if h : r ∈ A then F ⟨r, h⟩ else φ (g ⟨r, h⟩ j))
    have e2 : ∑ r ∈ R.filter (fun r => r ∈ A), (if h : r ∈ A then F ⟨r, h⟩ else φ (g ⟨r, h⟩ j)) =
        ∑ r ∈ RA, (if h : r ∈ A then F ⟨r, h⟩ else 0) :=
      sum_congr rfl fun r hr => by rw [dif_pos (mem_filter.1 hr).2, dif_pos (mem_filter.1 hr).2]
    have e3 : ∑ r ∈ R.filter (fun r => r ∉ A), (if h : r ∈ A then F ⟨r, h⟩ else φ (g ⟨r, h⟩ j)) =
        ∑ r ∈ RG, φ (g r j) := by
      rw [← sum_subtype_eq_sum_filter (fun r => if h : r ∈ A then F ⟨r, h⟩ else φ (g ⟨r, h⟩ j))]
      refine sum_congr rfl fun r _ => ?_
      rw [dif_neg r.2]
    rw [← e1, e2, e3, sum_sub_distrib, sum_sub_distrib, sum_const, sum_const, nsmul_eq_mul,
      nsmul_eq_mul, ← hcard]
    ring
  have hfix : ∀ g : {r // r ∉ A} → Fin N → ℝ,
      |∑ r ∈ RA, ((if h : r ∈ A then F ⟨r, h⟩ else 0) - 1 / 2)| ≤ 3 / 2 := by
    intro g
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ r ∈ RA, |(if h : r ∈ A then F ⟨r, h⟩ else 0) - 1 / 2| ≤ ∑ _r ∈ RA, (1 / 2 : ℝ) :=
          sum_le_sum fun r hr => by
            rw [dif_pos (mem_filter.1 hr).2]
            have := hF ⟨r, (mem_filter.1 hr).2⟩
            rw [abs_le]; constructor <;> linarith [this.1, this.2]
      _ = RA.card / 2 := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ 3 / 2 := by linarith
  set ε := 2 ^ d * δ / 2 with hε
  have hε0 : 0 ≤ ε := by rw [hε]; linarith
  have hsub : {g : {r // r ∉ A} → Fin N → ℝ |
      δ < |(∑ r ∈ R, (if h : r ∈ A then F ⟨r, h⟩ else φ (g ⟨r, h⟩ j))) / 2 ^ d - 1 / 2|} ⊆
      {g | ε ≤ |∑ r ∈ RG, (φ (g r j) - 1 / 2)|} := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    have e : (∑ r ∈ R, (if h : r ∈ A then F ⟨r, h⟩ else φ (g ⟨r, h⟩ j))) / 2 ^ d - 1 / 2 =
        (∑ r ∈ R, (if h : r ∈ A then F ⟨r, h⟩ else φ (g ⟨r, h⟩ j)) - 2 ^ d / 2) / 2 ^ d := by
      field_simp
    rw [e, abs_div, abs_of_pos h2d, lt_div_iff₀ h2d, hsplit g] at hg
    have h1 := abs_add_le (∑ r ∈ RA, ((if h : r ∈ A then F ⟨r, h⟩ else 0) - 1 / 2))
      (∑ r ∈ RG, (φ (g r j) - 1 / 2))
    have h2 := hfix g
    rw [hε]
    nlinarith
  refine (measure_mono hsub).trans ?_
  rcases Nat.eq_zero_or_pos RG.card with h0 | hpos
  · -- no generic row: the event is empty unless `ε = 0`, impossible
    have hempty : {g : {r // r ∉ A} → Fin N → ℝ | ε ≤ |∑ r ∈ RG, (φ (g r j) - 1 / 2)|} = ∅ := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      rw [card_eq_zero.1 h0, sum_empty, abs_zero]
      rw [hε]; linarith
    rw [hempty, measure_empty]; exact zero_le
  · refine (rows_hoeffding A RG j hφm hφ hφi hε0).trans (ENNReal.ofReal_le_ofReal ?_)
    have hRG : (RG.card : ℝ) ≤ 2 ^ d := by linarith [Nat.cast_nonneg (α := ℝ) RA.card]
    have hRGp : (0 : ℝ) < RG.card := by exact_mod_cast hpos
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.2
    rw [hε, div_le_div_iff₀ hRGp (by norm_num : (0 : ℝ) < 2)]
    have : (0 : ℝ) ≤ (2 ^ d * δ) ^ 2 := sq_nonneg _
    nlinarith


/-! ### The union over `(j, C)` -/

lemma dU_props {d : ℕ} (hN : 3 ≤ N) : 3 ≤ 2 ^ d * dU N d ∧ (N : ℝ) ^ 2 ≤ 2 ^ d * dU N d ^ 2 := by
  unfold dU
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have h4 : (4 : ℝ) ^ (d / 2) ≤ 2 ^ d := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_div_le d 2)
  have h2 : (2 : ℝ) ^ (d / 2) ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) (Nat.div_le_self d 2)
  have hp : (0 : ℝ) < 2 ^ (d / 2) := by positivity
  have hq : (0 : ℝ) < 4 ^ (d / 2) := by positivity
  constructor
  · rw [one_div_pow, mul_one_div, ← mul_div_assoc, le_div_iff₀ hp]
    nlinarith
  · have e : ((1 : ℝ) / 2 ^ (d / 2)) ^ 2 = 1 / 4 ^ (d / 2) := by
      rw [div_pow, one_pow, ← pow_mul, mul_comm, pow_mul]; norm_num
    rw [mul_pow, one_div_pow, e, mul_one_div, ← mul_div_assoc, le_div_iff₀ hq]
    nlinarith [sq_nonneg (N : ℝ)]

/-- **Union bound for a family of subcube averages.** -/
lemma conc_union (A : Finset (State N)) (hA : A.card ≤ 3) (hN : 3 ≤ N) {D : ℕ}
    (Q : ({r // r ∉ A} → Fin N → ℝ) → Fin N → Finset (Fin N) → ℝ)
    (hQ : ∀ j C, j ∉ C → D ≤ C.card → ∃ (R : Finset (State N)) (φ : ℝ → ℝ) (F : A → ℝ),
      R.card = 2 ^ C.card ∧ Measurable φ ∧ (∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) ∧
      ∫ v, φ v ∂unif = 1 / 2 ∧ (∀ r, F r ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ g, Q g j C = (∑ r ∈ R, (if h : r ∈ A then F ⟨r, h⟩ else φ (g ⟨r, h⟩ j))) / 2 ^ C.card) :
    rowsOutM A {g | ¬ ∀ j C, j ∉ C → D ≤ C.card → |Q g j C - 1 / 2| ≤ dU N C.card} ≤
      ENNReal.ofReal (N * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2))) := by
  classical
  set c := 2 * Real.exp (-((N : ℝ) ^ 2) / 2) with hc
  have hc0 : 0 ≤ c := by positivity
  set S : Fin N → Finset (Fin N) → Set ({r // r ∉ A} → Fin N → ℝ) := fun j C =>
    if j ∉ C ∧ D ≤ C.card then {g | dU N C.card < |Q g j C - 1 / 2|} else ∅ with hS
  have hsub : {g | ¬ ∀ j C, j ∉ C → D ≤ C.card → |Q g j C - 1 / 2| ≤ dU N C.card} ⊆
      ⋃ j, ⋃ C, S j C := by
    intro g hg
    simp only [Set.mem_setOf_eq, not_forall, not_le] at hg
    obtain ⟨j, C, hj, hD, hlt⟩ := hg
    refine Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨C, ?_⟩⟩
    simp only [hS, if_pos (And.intro hj hD)]
    exact hlt
  have hpiece : ∀ j C, rowsOutM A (S j C) ≤ ENNReal.ofReal c := by
    intro j C
    by_cases h : j ∉ C ∧ D ≤ C.card
    · simp only [hS, if_pos h]
      obtain ⟨R, φ, F, hR, hφm, hφ, hφi, hF, hQe⟩ := hQ j C h.1 h.2
      have hd := dU_props (d := C.card) hN
      have e : {g : {r // r ∉ A} → Fin N → ℝ | dU N C.card < |Q g j C - 1 / 2|} =
          {g | dU N C.card < |(∑ r ∈ R, (if h : r ∈ A then F ⟨r, h⟩ else φ (g ⟨r, h⟩ j))) /
            2 ^ C.card - 1 / 2|} := by
        ext g; simp only [Set.mem_setOf_eq, hQe g]
      rw [e]
      refine (subcube_dev A hA R hR j hφm hφ hφi F hF hd.1).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hc]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.2
      linarith [hd.2]
    · simp only [hS, if_neg h, measure_empty]; exact zero_le
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
  calc ∑ j, rowsOutM A (⋃ C, S j C) ≤ ∑ _j : Fin N, ∑ _C : Finset (Fin N), ENNReal.ofReal c :=
        sum_le_sum fun j _ => (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun C _ => hpiece j C)
    _ = ENNReal.ofReal (N * 2 ^ N * c) := by
        rw [sum_const, sum_const, card_univ, card_univ, Fintype.card_fin, Fintype.card_finset,
          Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        rw [hc]; simp [ENNReal.ofReal_pow, ENNReal.ofReal_mul]

/-! ### The two concentration fields -/

lemma integral_clamp : ∫ v, clamp01 v ∂unif = 1 / 2 := by
  have h1 := integral_cl_pow 1
  simp only [pow_one, Nat.cast_one] at h1
  rw [h1]; norm_num

lemma integral_one_sub_clamp : ∫ v, (1 - clamp01 v) ∂unif = 1 / 2 := by
  have hi : Integrable clamp01 unif :=
    Integrable.of_bound clamp01_measurable.aestronglyMeasurable 1
      (ae_of_all _ fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (clamp01_nonneg v)]; exact clamp01_le_one v)
  rw [integral_sub (integrable_const 1) hi, integral_clamp, integral_const]
  simp; norm_num

lemma card_rowsA_le (s r0 : State N) (x : Fin N) : (rowsA s r0 x).card ≤ 3 := by
  unfold rowsA
  refine (card_insert_le _ _).trans ?_
  have := card_insert_le (flipAt x r0) ({s} : Finset (State N))
  rw [card_singleton] at this
  omega

lemma card_compl_sub (C : Finset (Fin N)) : N - Cᶜ.card = C.card := by
  rw [card_compl, Fintype.card_fin]
  have := card_le_univ C; simp only [Fintype.card_fin] at this; omega

lemma card_univ_sdiff_sub (C : Finset (Fin N)) : N - (univ \ C).card = C.card := by
  rw [← compl_eq_univ_sdiff]; exact card_compl_sub C

/-- **`concC` given the fixed rows.** -/
theorem concC_cond (hN : 3 ≤ N) (s r0 : State N) (x : Fin N) (f : rowsA s r0 x → Fin N → ℝ) :
    rowsOutM (rowsA s r0 x) {g | ¬ ∀ j C, j ∉ C → DU N ≤ C.card →
      |cmean (glueRows (rowsA s r0 x) f g) (univ \ C) r0 j - 1 / 2| ≤ dU N C.card} ≤
      ENNReal.ofReal (N * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2))) := by
  classical
  refine conc_union (rowsA s r0 x) (card_rowsA_le s r0 x) hN
    (fun g j C => cmean (glueRows (rowsA s r0 x) f g) (univ \ C) r0 j) fun j C _ _ => ?_
  refine ⟨agree (univ \ C) r0, clamp01, fun r => clamp01 (f r j), ?_, clamp01_measurable,
    fun v => ⟨clamp01_nonneg v, clamp01_le_one v⟩, integral_clamp,
    fun r => ⟨clamp01_nonneg _, clamp01_le_one _⟩, fun g => ?_⟩
  · rw [card_agree, card_univ_sdiff_sub]
  · unfold cmean
    rw [card_univ_sdiff_sub]
    congr 1
    refine sum_congr rfl fun r _ => ?_
    unfold glueRows
    split_ifs <;> rfl

/-- The effect subcube average as an average of row readings. -/
lemma effUnit_glue (A : Finset (State N)) {s : State N} (hsA : s ∈ A) (f : A → Fin N → ℝ)
    (g : {r // r ∉ A} → Fin N → ℝ) (C : Finset (Fin N)) (j : Fin N) :
    effUnit (tpmOf (flipP s (glueRows A f g))) Cᶜ s j (teW (glueRows A f g) s j) =
      (∑ r ∈ agree Cᶜ s, (if h : r ∈ A then
          (if (1 / 2 : ℝ) < clamp01 (f ⟨s, hsA⟩ j) then clamp01 (f ⟨r, h⟩ j) else 1 - clamp01 (f ⟨r, h⟩ j))
        else (if (1 / 2 : ℝ) < clamp01 (f ⟨s, hsA⟩ j) then clamp01 (g ⟨r, h⟩ j)
          else 1 - clamp01 (g ⟨r, h⟩ j)))) / 2 ^ C.card := by
  rw [effUnit, card_agree, card_compl_sub]
  push_cast
  congr 1
  refine sum_congr rfl fun r _ => ?_
  have h1 := prob_teW_row (flipP s (glueRows A f g)) s r j
  rw [flipP_invol s (glueRows A f g)] at h1
  rw [h1]
  unfold pTe
  rw [glueRows_of_mem A f g hsA]
  by_cases hr : r ∈ A
  · rw [dif_pos hr, glueRows_of_mem A f g hr]
  · rw [dif_neg hr, glueRows_of_not_mem A f g hr]

/-- **`concE` given the fixed rows.** -/
theorem concE_cond (hN : 3 ≤ N) (s r0 : State N) (x : Fin N) (f : rowsA s r0 x → Fin N → ℝ) :
    rowsOutM (rowsA s r0 x) {g | ¬ ∀ j C, j ∉ C → DU N ≤ C.card →
      |effUnit (tpmOf (flipP s (glueRows (rowsA s r0 x) f g))) Cᶜ s j
        (teW (glueRows (rowsA s r0 x) f g) s j) - 1 / 2| ≤ dU N C.card} ≤
      ENNReal.ofReal (N * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2))) := by
  classical
  have hsA : s ∈ rowsA s r0 x := rowsA_mem_s
  refine conc_union (rowsA s r0 x) (card_rowsA_le s r0 x) hN _ fun j C _ _ => ?_
  refine ⟨agree Cᶜ s,
    fun v => if (1 / 2 : ℝ) < clamp01 (f ⟨s, hsA⟩ j) then clamp01 v else 1 - clamp01 v,
    fun r => if (1 / 2 : ℝ) < clamp01 (f ⟨s, hsA⟩ j) then clamp01 (f r j) else 1 - clamp01 (f r j),
    by rw [card_agree, card_compl_sub], ?_, ?_, ?_, ?_, fun g => effUnit_glue _ hsA f g C j⟩
  · split_ifs
    · exact clamp01_measurable
    · exact measurable_const.sub clamp01_measurable
  · intro v; split_ifs
    · exact ⟨clamp01_nonneg v, clamp01_le_one v⟩
    · exact ⟨by linarith [clamp01_le_one v], by linarith [clamp01_nonneg v]⟩
  · split_ifs
    · exact integral_clamp
    · exact integral_one_sub_clamp
  · intro r; split_ifs
    · exact ⟨clamp01_nonneg _, clamp01_le_one _⟩
    · exact ⟨by linarith [clamp01_le_one (f r j)], by linarith [clamp01_nonneg (f r j)]⟩

end Census
end IIT
