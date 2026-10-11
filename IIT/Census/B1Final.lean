/-
Final assembly of the lower bound `B1_lowerX` (W7 §3), combining
* `RestGood` (fe6) and `UnivGood` (`RestUniv_cond`, conditional failure ≤ 1/4),
* `SubGood` (`SubGood_cond`, conditional outer-measure failure ≤ ε, here ε = 1/4), handled through
  a measurable superset `toMeasurable` of its failure set on the outside rows,
* `EXFacts_whp` (≤ 1/4).
Total failure ≤ 3/4, so `B1 ∩ {tc = r0}` keeps a quarter of `EX`; `B1_lowerX_final` then follows as
`B1_lowerX_univ`, with `log 8` in place of `log 4`.
-/
import IIT.Census.B1UnivGlue
import IIT.Census.B1SubMain

namespace IIT
namespace Census

open MeasureTheory Filter Finset

variable {N : ℕ}

/-- The constant fixed rows used to describe the `SubGood` failure set on the outside rows. -/
noncomputable def finFix (s r0 : State N) (x : Fin N) : rowsA s r0 x → Fin N → ℝ := fun _ _ => 1 / 2

/-- The `SubGood` failure set, as a set of outside rows (it does not depend on the fixed rows). -/
def subBadOut (N : ℕ) (s r0 : State N) (x : Fin N) : Set ({r // r ∉ rowsA s r0 x} → Fin N → ℝ) :=
  {g | ¬ SubGood N s r0 x (glueRows (rowsA s r0 x) (finFix s r0 x) g)}

/-- A measurable superset of the same `rowsOutM`-measure. -/
noncomputable def subBadM (N : ℕ) (s r0 : State N) (x : Fin N) :
    Set ({r // r ∉ rowsA s r0 x} → Fin N → ℝ) :=
  toMeasurable (rowsOutM (rowsA s r0 x)) (subBadOut N s r0 x)

lemma subGood_of_not_mem {s r0 : State N} {x : Fin N} {w : Param N}
    (h : restrOut (rowsA s r0 x) w ∉ subBadM N s r0 x) : SubGood N s r0 x w := by
  have h1 : restrOut (rowsA s r0 x) w ∉ subBadOut N s r0 x := fun hm => h (subset_toMeasurable _ _ hm)
  simp only [subBadOut, Set.mem_setOf_eq, not_not] at h1
  obtain ⟨w', hA, hE, hG, ho⟩ := h1.cmp
  refine ⟨⟨w', fun r hr => ?_, hE, hG, ho⟩⟩
  rw [← hA r hr, glueRows_of_not_mem _ _ _ hr]; rfl

/-- **`B1 ∩ {tc = r0}` keeps a quarter of `EX`** (all three good-row conditions). -/
theorem EX_B1_quarter : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    cubeM N (EX N s r0 x) / 4 ≤ cubeM N (EX N s r0 x ∩ {w | tcRow w = r0} ∩ B1w N s) := by
  filter_upwards [EXFacts_whp, RestUniv_cond, tc_of_EX, phi_univ_ge_EX_univ, phi_S_le_EX_sub,
    SubGood_cond (ε := 1 / 4) (by norm_num)] with N h1 h2 h3 h4 h5 h6 s r0 x hham
  set A := rowsA s r0 x
  set Y := {w : Param N | w ∈ EX N s r0 x ∧ EXFacts N s r0 x w} with hY
  set R := {w : Param N | (RestGood N s r0 x w ∧ UnivGood N s r0 x w) ∧
    restrOut A w ∉ subBadM N s r0 x} with hR
  set Tg := EX N s r0 x ∩ {w | tcRow w = r0} ∩ B1w N s with hTg
  have hYm : MeasurableSet Y := measurableSet_EXFacts s r0 x
  have hRm : MeasurableSet R :=
    ((measurableSet_RestGood s r0 x).inter (measurableSet_UnivGood s r0 x)).inter
      ((measurable_restrOut A) (measurableSet_toMeasurable _ _)).compl
  have hsub : Y ∩ R ∩ openCube N ⊆ Tg := by
    rintro w ⟨⟨⟨hEX, hF⟩, hRg, hSb⟩, ho⟩
    have hSG := subGood_of_not_mem hSb
    refine ⟨⟨hEX, h3 s r0 x hham w ho hEX hF hRg.1⟩, ?_⟩
    rw [mem_B1w_iff]
    refine ⟨flipP_cube (fun r i => Set.Ioo_subset_Icc_self (ho r i)) s, fun S hS hne => ?_⟩
    exact (h5 s r0 x hham w ho hEX hF ⟨hRg.1, hSG⟩ S hS hne).trans_le (h4 s r0 x hham w ho hEX hF hRg)
  set g0 : {r // r ∉ A} → Fin N → ℝ := fun _ _ => 1 / 2
  set G : Set (A → Fin N → ℝ) := {f | glueRows A f g0 ∈ Y} with hG
  have hgm : Measurable fun f : A → Fin N → ℝ => glueRows A f g0 :=
    (measurable_glueRows A).comp (measurable_id.prodMk
      (measurable_const : Measurable fun _ : A → Fin N → ℝ => g0))
  have hGm : MeasurableSet G := hYm.preimage hgm
  have hYG : Y = {w | restrIn A w ∈ G} := by
    ext w
    simp only [hY, hG, Set.mem_setOf_eq]
    refine (EX_local s r0 x fun r hr => ?_)
    show glueRows A (restrIn A w) g0 r = w r
    rw [glueRows_of_mem A _ _ hr]; rfl
  have hcond : ∀ f ∈ G, rowsOutM A {g | glueRows A f g ∈ Rᶜ} ≤ 1 / 2 := by
    intro f hf
    have hsplit : {g | glueRows A f g ∈ Rᶜ} ⊆
        {g | ¬ (RestGood N s r0 x (glueRows A f g) ∧ UnivGood N s r0 x (glueRows A f g))} ∪
          subBadM N s r0 x := by
      intro g hg
      have hg' : ¬ ((RestGood N s r0 x (glueRows A f g) ∧ UnivGood N s r0 x (glueRows A f g)) ∧
          restrOut A (glueRows A f g) ∉ subBadM N s r0 x) := hg
      rw [restrOut_glueRows] at hg'
      by_cases hc : RestGood N s r0 x (glueRows A f g) ∧ UnivGood N s r0 x (glueRows A f g)
      · right; by_contra hn; exact hg' ⟨hc, hn⟩
      · exact Or.inl hc
    have hb : rowsOutM A (subBadM N s r0 x) ≤ ENNReal.ofReal (1 / 4) := by
      rw [subBadM, measure_toMeasurable]
      exact h6 s r0 x (finFix s r0 x)
    refine (measure_mono hsplit).trans ((measure_union_le _ _).trans ?_)
    calc _ ≤ (1 / 4 : ENNReal) + ENNReal.ofReal (1 / 4) := add_le_add (h2 s r0 x hham f g0 hf) hb
      _ = 1 / 2 := by
          have e4 : (1 / 4 : ENNReal) = ENNReal.ofReal (1 / 4) := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
          have e2 : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
          rw [e4, e2, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
  have hfail : cubeM N (Rᶜ ∩ Y) ≤ 1 / 2 * cubeM N Y := by
    rw [hYG]
    refine (cubeM_inter_restrIn_le A hRm.compl hGm (δ := 1 / 2) hcond).trans_eq ?_
    rw [cubeM_restrIn_preimage]
  have hfacts : cubeM N (EX N s r0 x \ Y) ≤ cubeM N (EX N s r0 x) / 4 := by
    refine le_trans (measure_mono (s := EX N s r0 x \ Y) (t := EX N s r0 x \ {w | EXFacts N s r0 x w}) ?_)
      (h1 s r0 x hham)
    intro w hw
    exact ⟨hw.1, fun hF => hw.2 ⟨hw.1, hF⟩⟩
  have hcov : EX N s r0 x ⊆ (EX N s r0 x \ Y) ∪ (Rᶜ ∩ Y) ∪ (Y ∩ R ∩ openCube N) ∪ (openCube N)ᶜ := by
    intro w hw
    by_cases hy : w ∈ Y
    · by_cases hr : w ∈ R
      · by_cases ho : w ∈ openCube N
        · exact Or.inl (Or.inr ⟨⟨hy, hr⟩, ho⟩)
        · exact Or.inr ho
      · exact Or.inl (Or.inl (Or.inr ⟨hr, hy⟩))
    · exact Or.inl (Or.inl (Or.inl ⟨hw, hy⟩))
  set a := cubeM N (EX N s r0 x)
  have ha : a ≠ ⊤ := measure_ne_top _ _
  have hYle : cubeM N Y ≤ a := measure_mono fun w hw => hw.1
  have hmain : a ≤ a / 4 + 1 / 2 * a + cubeM N Tg := by
    calc a ≤ cubeM N ((EX N s r0 x \ Y) ∪ (Rᶜ ∩ Y) ∪ (Y ∩ R ∩ openCube N) ∪ (openCube N)ᶜ) :=
          measure_mono hcov
      _ ≤ cubeM N (EX N s r0 x \ Y) + cubeM N (Rᶜ ∩ Y) + cubeM N (Y ∩ R ∩ openCube N) +
            cubeM N (openCube N)ᶜ := by
          refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
            (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
      _ ≤ a / 4 + 1 / 2 * a + cubeM N Tg + 0 := by
          rw [cubeM_compl_openCube]
          exact add_le_add (add_le_add (add_le_add hfacts (hfail.trans (by gcongr))) (measure_mono hsub))
            le_rfl
      _ = a / 4 + 1 / 2 * a + cubeM N Tg := by rw [add_zero]
  have hsplit : a = (a / 4 + 1 / 2 * a) + a / 4 := by
    rw [ENNReal.div_eq_inv_mul, ← add_mul, ← add_mul]
    have : ((4 : ENNReal)⁻¹ + 1 / 2 + 4⁻¹) = 1 := by
      rw [show (4 : ENNReal)⁻¹ = ENNReal.ofReal (1 / 4) by
            rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp,
        show (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) by
            rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp,
        ← ENNReal.ofReal_add (by norm_num) (by norm_num),
        ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    rw [this, one_mul]
  have hfin : a / 4 + 1 / 2 * a ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top ha (by norm_num), ENNReal.mul_ne_top (by simp) ha⟩
  have : (a / 4 + 1 / 2 * a) + a / 4 ≤ (a / 4 + 1 / 2 * a) + cubeM N Tg := by
    rw [← hsplit]; exact hmain
  exact (ENNReal.add_le_add_iff_left hfin).1 this

/-- **`B1_lowerX`**: `P(B1) ≥ e^{-RLBX N}` eventually. -/
theorem B1_lowerX_final : ∀ᶠ N in atTop, ∀ s : State N,
    Real.exp (-(RLBX * N)) ≤ (cubeM N (B1w N s)).toReal := by
  set K : ℝ := (exKLPhi : ℝ) + exKLShi + 1 / 10 ^ 5 with hK
  have hgap : 0 < RLBX - (K - Real.log 2) := by have := EX_rate_lt; linarith
  have hlin : ∀ᶠ N : ℕ in atTop, Real.log 8 ≤ (RLBX - (K - Real.log 2)) * N := by
    have := tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.log 8 / (RLBX - (K - Real.log 2)))
    filter_upwards [this] with N hN
    rwa [div_le_iff₀ hgap, mul_comm] at hN
  filter_upwards [EX_B1_quarter, EX_prob_ev, card_far_rows, hlin, eventually_ge_atTop 6] with
    N hhalf hprob hcard hl hN6 s
  have hN0 : 0 < N := by omega
  set x : Fin N := ⟨0, hN0⟩
  set Far := univ.filter fun r0 : State N => N ≤ 3 * ham r0 s
  set Tg : State N → Set (Param N) := fun r0 => EX N s r0 x ∩ {w | tcRow w = r0} ∩ B1w N s
  have hTm : ∀ r0, MeasurableSet (Tg r0) := fun r0 =>
    ((measurableSet_EX s r0 x).inter (measurableSet_tcRow_eq r0)).inter (measurableSet_B1w s)
  have hdisj : Set.PairwiseDisjoint (↑Far) Tg := by
    intro r0 _ r1 _ hne
    refine Set.disjoint_left.2 fun w h0 h1 => hne ?_
    exact h0.1.2.symm.trans h1.1.2
  have hrows : ∀ r0 ∈ Far, r0 ≠ s ∧ flipAt x r0 ≠ s := by
    intro r0 hr0
    have hh : N ≤ 3 * ham r0 s := (Finset.mem_filter.1 hr0).2
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, ham_self] at hh; omega
    · have := ham_flipAt_le_one x r0
      rw [h, ham_comm] at this
      omega
  have hpiece : ∀ r0 ∈ Far, ENNReal.ofReal (Real.exp (-(K * N))) / 4 ≤ cubeM N (Tg r0) := by
    intro r0 hr0
    obtain ⟨h0, h1⟩ := hrows r0 hr0
    have hp := hprob s r0 x h0 h1
    have hp' : ENNReal.ofReal (Real.exp (-(K * N))) ≤ cubeM N (EX N s r0 x) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top (cubeM N) (EX N s r0 x))]
      exact ENNReal.ofReal_le_ofReal hp
    exact (ENNReal.div_le_div_right hp' 4).trans (hhalf s r0 x (Finset.mem_filter.1 hr0).2)
  have hsum : (Far.card : ENNReal) * (ENNReal.ofReal (Real.exp (-(K * N))) / 4) ≤ cubeM N (B1w N s) := by
    calc (Far.card : ENNReal) * (ENNReal.ofReal (Real.exp (-(K * N))) / 4)
        = ∑ _r0 ∈ Far, ENNReal.ofReal (Real.exp (-(K * N))) / 4 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ r0 ∈ Far, cubeM N (Tg r0) := sum_le_sum hpiece
      _ = cubeM N (⋃ r0 ∈ Far, Tg r0) := (measure_biUnion_finset hdisj fun r0 _ => hTm r0).symm
      _ ≤ cubeM N (B1w N s) := measure_mono (Set.iUnion₂_subset fun r0 _ => Set.inter_subset_right)
  have hfin : cubeM N (B1w N s) ≠ ⊤ := measure_ne_top _ _
  have hreal : (Far.card : ℝ) * (Real.exp (-(K * N)) / 4) ≤ (cubeM N (B1w N s)).toReal := by
    have := ENNReal.toReal_mono hfin hsum
    rwa [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_natCast, ENNReal.toReal_ofNat] at this
  refine le_trans ?_ hreal
  have hc := hcard s
  calc Real.exp (-(RLBX * N)) ≤ (2 : ℝ) ^ N / 2 * (Real.exp (-(K * N)) / 4) := by
        have h2N : (2 : ℝ) ^ N = Real.exp (Real.log 2 * N) := by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
        have h8 : (8 : ℝ) = Real.exp (Real.log 8) := (Real.exp_log (by norm_num)).symm
        rw [h2N, show ∀ a b : ℝ, a / 2 * (b / 4) = a * b / 8 from fun a b => by ring, ← Real.exp_add, h8,
          ← Real.exp_sub]
        apply Real.exp_le_exp.2
        nlinarith
    _ ≤ (Far.card : ℝ) * (Real.exp (-(K * N)) / 4) := by gcongr

end Census
end IIT
