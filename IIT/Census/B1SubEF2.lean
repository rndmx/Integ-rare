/-
The `EF` event of W4 (heavy pattern through a fixed row, level `43/100`) with SEVERAL fixed entries replaced
by `1`: needed for near-universe candidates `S ∌ x` of regime X, whose `r0`-pattern contains both fixed rows
`r0` and `r0^x` (W7 §3 item 4: "EF with the two fixed entries of r0, r1 bounded by 1: E max(1 + (V+W)/2, 1)
= 3/2, same Markov bound as EF").  The Jensen pairing needs a flip coordinate `j0 ∉ M` that never pairs two
fixed rows; for `F = {r0, r0^x}` and `x ∉ M`, `|M| ≤ N - 2`, any `j0 ∉ M ∪ {x}` works.
-/
import IIT.Census.B1LowerB

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Finset

noncomputable section

variable {N : ℕ}

/-- Subcube column mean with the entries of the rows of `F` replaced by `1`. -/
def cmSetCol (M : Finset (Fin N)) (a : State N) (F : Finset (State N)) (c : State N → ℝ) : ℝ :=
  (∑ r ∈ agree M a, (if r ∈ F then 1 else clamp01 (c r))) / (2 : ℝ) ^ (N - M.card)

/-- `colMeanSet w M a F i = cmSetCol M a F (colsOf w i)`. -/
def colMeanSet (w : Param N) (M : Finset (Fin N)) (a : State N) (F : Finset (State N)) (i : Fin N) : ℝ :=
  cmSetCol M a F (colsOf w i)

lemma measurable_cmSetCol (M : Finset (Fin N)) (a : State N) (F : Finset (State N)) :
    Measurable (cmSetCol M a F) := by
  unfold cmSetCol
  refine (Finset.measurable_sum _ fun r _ => ?_).div_const _
  by_cases h : r ∈ F
  · simp only [h, ite_true]; exact measurable_const
  · simp only [h, ite_false]; exact clamp01_measurable.comp (measurable_pi_apply r)

/-- **Lemma JP with a set of fixed rows.** -/
lemma jp_set {M : Finset (Fin N)} {j0 : Fin N} (hj0 : j0 ∉ M) (a : State N) (F : Finset (State N))
    (hF : ∀ r ∈ F, flipAt j0 r ∉ F) (c : State N → ℝ) :
    max (2 * cmSetCol M a F c) 1 ≤
      (∑ r ∈ agree M a, (1 + clamp01 (c (if flipAt j0 r ∈ F then r else flipAt j0 r)))) /
        (2 : ℝ) ^ (N - M.card) := by
  classical
  set C := agree M a with hC
  set n : ℝ := (2 : ℝ) ^ (N - M.card) with hn
  have hcard : (C.card : ℝ) = n := by rw [hC, card_agree]; push_cast; rfl
  have hnpos : 0 < n := by positivity
  set xp : State N → ℝ := fun r => if r ∈ F then 1 else clamp01 (c r) with hxp
  have hxp0 : ∀ r, 0 ≤ xp r := fun r => by
    simp only [hxp]; split_ifs
    · norm_num
    · exact clamp01_nonneg _
  have hxp1 : ∀ r, xp r ≤ 1 := fun r => by
    simp only [hxp]; split_ifs
    · norm_num
    · exact clamp01_le_one _
  set b : State N → ℝ := fun r => xp r + xp (flipAt j0 r) with hb
  have hsumb : ∑ r ∈ C, b r = 2 * ∑ r ∈ C, xp r := by
    simp only [hb, sum_add_distrib]
    rw [hC, sum_agree_flipAt hj0 a xp]; ring
  have h2 : 2 * cmSetCol M a F c = (∑ r ∈ C, b r) / n := by
    rw [hsumb, cmSetCol, ← hC, ← hn]; ring
  have hpt : ∀ r ∈ C, max (b r) 1 ≤
      1 + clamp01 (c (if flipAt j0 r ∈ F then r else flipAt j0 r)) := by
    intro r _
    have hu0 := hxp0 r
    have hu1 := hxp1 r
    have hv0 := hxp0 (flipAt j0 r)
    have hv1 := hxp1 (flipAt j0 r)
    have hmax : max (b r) 1 ≤ 1 + xp r * xp (flipAt j0 r) := by
      refine max_le ?_ (by nlinarith)
      simp only [hb]; nlinarith
    refine hmax.trans ?_
    have hz : xp r * xp (flipAt j0 r) ≤
        clamp01 (c (if flipAt j0 r ∈ F then r else flipAt j0 r)) := by
      by_cases hfa : flipAt j0 r ∈ F
      · have hra : r ∉ F := by
          intro hra; exact hF r hra hfa
        simp only [hxp, hra, hfa, ite_true, ite_false, mul_one, le_refl]
      · simp only [hfa, ite_false]
        have : xp (flipAt j0 r) = clamp01 (c (flipAt j0 r)) := by simp [hxp, hfa]
        rw [this]
        have := clamp01_nonneg (c (flipAt j0 r))
        nlinarith
    linarith
  rw [h2]
  have hsum_le : ∑ r ∈ C, max (b r) 1 ≤
      ∑ r ∈ C, (1 + clamp01 (c (if flipAt j0 r ∈ F then r else flipAt j0 r))) := sum_le_sum hpt
  refine max_le ?_ ?_
  · rw [div_le_div_iff_of_pos_right hnpos]
    exact (sum_le_sum fun r _ => le_max_left _ _).trans hsum_le
  · rw [le_div_iff₀ hnpos, one_mul, ← hcard]
    calc (C.card : ℝ) = ∑ _r ∈ C, (1 : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ r ∈ C, max (b r) 1 := sum_le_sum fun r _ => le_max_right _ _
      _ ≤ _ := hsum_le

/-- **One moment.** `E max(2 cmSetCol, 1) ≤ 3/2`. -/
lemma lintegral_max_set_le {M : Finset (Fin N)} {j0 : Fin N} (hj0 : j0 ∉ M) (a : State N)
    (F : Finset (State N)) (hF : ∀ r ∈ F, flipAt j0 r ∉ F) :
    ∫⁻ c, ENNReal.ofReal (max (2 * cmSetCol M a F c) 1) ∂colLaw N ≤ ENNReal.ofReal (3 / 2) := by
  classical
  set n : ℝ := (2 : ℝ) ^ (N - M.card) with hn
  have hnpos : 0 < n := by positivity
  set q : State N → State N := fun r => if flipAt j0 r ∈ F then r else flipAt j0 r with hq
  set g : (State N → ℝ) → ℝ := fun c => (∑ r ∈ agree M a, (1 + clamp01 (c (q r)))) / n with hg
  have hint1 : ∀ r : State N, Integrable (fun c : State N → ℝ => 1 + clamp01 (c (q r)))
      (colLaw N) := fun r => (integrable_const 1).add (integrable_col_cl (q r))
  have hint : Integrable g (colLaw N) :=
    (integrable_finsetSum _ fun r _ => hint1 r).div_const n
  have hg0 : ∀ c, 0 ≤ g c := fun c =>
    div_nonneg (sum_nonneg fun r _ => add_nonneg zero_le_one (clamp01_nonneg _)) hnpos.le
  have hval : ∫ c, g c ∂colLaw N = 3 / 2 := by
    simp only [hg]
    rw [integral_div, integral_finsetSum _ fun r _ => hint1 r]
    have : ∀ r ∈ agree M a, ∫ c, (1 + clamp01 (c (q r))) ∂colLaw N = 3 / 2 := by
      intro r _
      rw [integral_add (integrable_const 1) (integrable_col_cl (q r)), integral_col,
        integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      norm_num
    rw [sum_congr rfl this, sum_const, card_agree, nsmul_eq_mul]
    have e : ((2 ^ (N - M.card) : ℕ) : ℝ) = n := by rw [hn]; push_cast; rfl
    rw [e]
    field_simp
  calc ∫⁻ c, ENNReal.ofReal (max (2 * cmSetCol M a F c) 1) ∂colLaw N
      ≤ ∫⁻ c, ENNReal.ofReal (g c) ∂colLaw N :=
        lintegral_mono fun c => ENNReal.ofReal_le_ofReal (jp_set hj0 a F hF c)
    _ = ENNReal.ofReal (∫ c, g c ∂colLaw N) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hg0)).symm
    _ = ENNReal.ofReal (3 / 2) := by rw [hval]

/-- **One set.** -/
lemma cubeM_EFset_bad {M : Finset (Fin N)} {j0 : Fin N} (hj0 : j0 ∉ M) (a : State N)
    (F : Finset (State N)) (hF : ∀ r ∈ F, flipAt j0 r ∉ F) :
    cubeM N {w | ¬ ∑ i ∈ M, Real.log (max (2 * colMeanSet w M a F i) 1) ≤ 43 / 100 * M.card} ≤
      ENNReal.ofReal ((3 / 2 * Real.exp (-(43 / 100))) ^ M.card) := by
  set G : (State N → ℝ) → ℝ := fun c => Real.log (max (2 * cmSetCol M a F c) 1) with hG
  have hGm : Measurable G := Real.measurable_log.comp
    (((measurable_cmSetCol M a F).const_mul 2).max measurable_const)
  set X : Fin N → Param N → ℝ := fun i w => G (colsOf w i) with hX
  have hind : iIndepFun X (cubeM N) := iIndepFun_cols.comp (fun _ => G) (fun _ => hGm)
  have hmeas : ∀ i, Measurable (X i) := fun i => hGm.comp (measurable_colOf i)
  have h := chernoff_indep_ge (μ := cubeM N) M hind hmeas (a := 43 / 100 * M.card) (t := 1)
    (by norm_num)
  have hsub : {w : Param N | ¬ ∑ i ∈ M, Real.log (max (2 * colMeanSet w M a F i) 1) ≤
      43 / 100 * M.card} ⊆ {w | 43 / 100 * M.card ≤ ∑ i ∈ M, X i w} := fun w hw =>
    le_of_lt (not_le.1 hw)
  refine (measure_mono hsub).trans (h.trans ?_)
  have hI : ∀ i, ∫⁻ w, ENNReal.ofReal (Real.exp (1 * X i w)) ∂cubeM N ≤
      ENNReal.ofReal (3 / 2) := by
    intro i
    have hg : Measurable fun c : State N → ℝ => ENNReal.ofReal (Real.exp (1 * G c)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hGm.const_mul 1))
    refine le_trans (le_of_eq ((mp_colOf i).lintegral_comp hg)) ?_
    refine le_trans (le_of_eq (lintegral_congr fun c => ?_)) (lintegral_max_set_le hj0 a F hF)
    congr 1
    simp only [hG, one_mul]
    exact Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))
  calc ENNReal.ofReal (Real.exp (-1 * (43 / 100 * M.card))) *
        ∏ i ∈ M, ∫⁻ w, ENNReal.ofReal (Real.exp (1 * X i w)) ∂cubeM N
      ≤ ENNReal.ofReal (Real.exp (-1 * (43 / 100 * M.card))) *
          ∏ _i ∈ M, ENNReal.ofReal (3 / 2) := by
        gcongr with i hi
        exact hI i
    _ = ENNReal.ofReal ((3 / 2 * Real.exp (-(43 / 100))) ^ M.card) := by
        rw [prod_const, ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity),
          mul_pow, ← Real.exp_nat_mul]
        congr 1
        rw [mul_comm]
        congr 1
        ring_nf

/-- **EF2**: the `r0`-pattern of every large `M ∌ x` with `|M| ≤ N - 2`, both fixed rows `r0, r0^x` at `1`. -/
def EF2 (N : ℕ) (r0 : State N) (x : Fin N) : Set (Param N) :=
  {w | ∀ M : Finset (Fin N), K2N N < M.card → M.card + 2 ≤ N → x ∉ M →
    ∑ i ∈ M, Real.log (max (2 * colMeanSet w M r0 {r0, flipAt x r0} i) 1) ≤ 43 / 100 * M.card}

lemma measurableSet_EF2 (r0 : State N) (x : Fin N) : MeasurableSet (EF2 N r0 x) := by
  have : EF2 N r0 x = ⋂ M : Finset (Fin N), ⋂ (_ : K2N N < M.card ∧ M.card + 2 ≤ N ∧ x ∉ M),
      {w : Param N | ∑ i ∈ M, Real.log (max (2 * colMeanSet w M r0 {r0, flipAt x r0} i) 1) ≤
        43 / 100 * M.card} := by
    ext w; simp only [EF2, Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun h M hM => h M hM.1 hM.2.1 hM.2.2, fun h M h1 h2 h3 => h M ⟨h1, h2, h3⟩⟩
  rw [this]
  refine MeasurableSet.iInter fun M => MeasurableSet.iInter fun _ => measurableSet_le ?_ measurable_const
  exact Finset.measurable_sum _ fun i _ => Real.measurable_log.comp
    ((((measurable_cmSetCol M r0 _).comp (measurable_colOf i)).const_mul 2).max measurable_const)

/-- A flip coordinate that never pairs `r0` with `r0^x`. -/
lemma exists_j0_EF2 {M : Finset (Fin N)} (hM : M.card + 2 ≤ N) (x : Fin N) (r0 : State N) :
    ∃ j0, j0 ∉ M ∧ ∀ r ∈ ({r0, flipAt x r0} : Finset (State N)), flipAt j0 r ∉ ({r0, flipAt x r0} : Finset (State N)) := by
  classical
  have hc : (insert x M).card < N := by
    have := card_insert_le x M; omega
  obtain ⟨j0, hj0⟩ := exists_not_mem_of_card_lt hc
  rw [mem_insert, not_or] at hj0
  obtain ⟨hjx, hjM⟩ := hj0
  refine ⟨j0, hjM, fun r hr => ?_⟩
  simp only [mem_insert, mem_singleton] at hr ⊢
  rcases hr with rfl | rfl
  · rintro (h | h)
    · exact flipAt_ne j0 r h
    · have := congrFun h j0
      simp [flipAt, Function.update_of_ne hjx] at this
  · rintro (h | h)
    · have := congrFun h x
      simp [flipAt, Function.update_of_ne (Ne.symm hjx)] at this
    · exact flipAt_ne j0 _ h

theorem cubeM_not_EF2 (hN : 1 ≤ N) (r0 : State N) (x : Fin N) :
    cubeM N (EF2 N r0 x)ᶜ ≤ ENNReal.ofReal (Real.exp 1 * ((1 / bEF) * N) ^ D1 N * bEF ^ N) := by
  set X : Finset (Fin N) → Set (Param N) := fun M =>
    {w | K2N N < M.card ∧ M.card + 2 ≤ N ∧ x ∉ M ∧
      ¬ ∑ i ∈ M, Real.log (max (2 * colMeanSet w M r0 {r0, flipAt x r0} i) 1) ≤ 43 / 100 * M.card}
    with hX
  have hsub : (EF2 N r0 x)ᶜ ⊆ ⋃ M, X M := by
    intro w hw
    simp only [EF2, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hw
    obtain ⟨M, hk, hk', hx, h⟩ := hw
    exact Set.mem_iUnion.2 ⟨M, hk, hk', hx, h⟩
  have hb0 : 0 ≤ (1 / bEF) ^ D1 N * bEF ^ N := by have := bEF_pos; positivity
  refine (measure_mono hsub).trans ((cubeM_iUnion_bigM_le hN X hb0 (fun M hM => ?_)
    (fun M hM => ?_)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  · by_cases hMN : M.card + 2 ≤ N
    · obtain ⟨j0, hj0, hF⟩ := exists_j0_EF2 hMN x r0
      refine le_trans (measure_mono fun w hw => hw.2.2.2) ((cubeM_EFset_bad hj0 r0 _ hF).trans
        (ENNReal.ofReal_le_ofReal ?_))
      exact pow_le_of_big bEF_pos bEF_lt_one.le hM (by omega)
    · have : X M = ∅ := by
        ext w; simp only [hX, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hMN h.2.1
      rw [this, measure_empty]; exact zero_le
  · ext w
    simp only [hX, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => hM h.1
  · rw [mul_pow]; ring

end

end Census
end IIT
