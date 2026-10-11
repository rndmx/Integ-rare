/-
Census, B1 lower bound, leaf `phi_univ_ge_EX`: GLUE for the orchestrator.

* `RestGood_cond8`  : `RestGood_cond` with the bound `1/8` (same proof, `log 8` for `log 4`).
* `RestUniv_cond`   : the rows outside `rowsA` satisfy `RestGood ∧ UnivGood` with conditional probability
                      `≥ 3/4` (all fields proved; `smallC_cond'`, `smallE_cond'` in B1UnivSmallC2/E).
* `EX_B1_half_univ` : the statement of `B1LowerB.EX_B1_half`, proved with `R := RestGood ∧ UnivGood`,
                      `phi_univ_ge_EX_univ` in place of the leaf `phi_univ_ge_EX` (and `phi_S_le_EX`,
                      `tc_of_EX` applied to the `RestGood` component).
-/
import IIT.Census.B1UnivSmallE

set_option maxRecDepth 100000

namespace IIT
namespace Census

open MeasureTheory Filter Finset

variable {N : ℕ}

/-! ### Assembly -/

lemma two_pow_eq_exp (N : ℕ) : (2 : ℝ) ^ N = Real.exp (N * Real.log 2) := by
  rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ N), Real.log_pow]

lemma ev_low_small : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ N * Real.exp (-((3 / 2 : ℝ) ^ N / 32)) ≤ 1 / 48 := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 1 (show (1 : ℝ) < 3 / 2 by norm_num)
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 64 by norm_num))
  filter_upwards [hev, eventually_ge_atTop 20] with N hN hN20
  have hN' : (N : ℝ) ^ 1 < 1 / 64 * (3 / 2) ^ N := by
    have := hN; rwa [div_lt_iff₀ (by positivity)] at this
  have hNr : (20 : ℝ) ≤ N := by exact_mod_cast hN20
  have h1 : 2 * (N : ℝ) ≤ (3 / 2 : ℝ) ^ N / 32 := by rw [pow_one] at hN'; linarith
  have hl2 : Real.log 2 < 7 / 10 := by have := Real.log_two_lt_d9; linarith
  rw [two_pow_eq_exp, ← Real.exp_add]
  calc Real.exp (N * Real.log 2 + -((3 / 2 : ℝ) ^ N / 32)) ≤ Real.exp (-(13 / 10 * (N : ℝ))) := by
        apply Real.exp_le_exp.2; nlinarith
    _ ≤ Real.exp (-26) := Real.exp_le_exp.2 (by linarith)
    _ ≤ 1 / 48 := by
        rw [Real.exp_neg, inv_eq_one_div, one_div_le_one_div (Real.exp_pos _) (by norm_num)]
        have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 26); linarith

lemma ev_up_small : ∀ᶠ N : ℕ in atTop, 4 * (2 / 3 : ℝ) ^ N ≤ 1 / 48 := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 2 / 3 by norm_num)
    (show (2 / 3 : ℝ) < 1 by norm_num)
  filter_upwards [ht.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 192 by norm_num))] with N hN
  linarith

lemma ev_conc_small : ∀ᶠ N : ℕ in atTop, (N : ℝ) * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2)) ≤ 1 / 48 := by
  filter_upwards [eventually_ge_atTop 20] with N hN20
  have hNr : (20 : ℝ) ≤ N := by exact_mod_cast hN20
  have hN2 : (N : ℝ) ≤ 2 ^ N := by
    have := Nat.lt_two_pow_self (n := N); exact_mod_cast this.le
  have hl2 : Real.log 2 < 7 / 10 := by have := Real.log_two_lt_d9; linarith
  have h4 : (N : ℝ) * 2 ^ N ≤ Real.exp (N * (2 * Real.log 2)) := by
    calc (N : ℝ) * 2 ^ N ≤ 2 ^ N * 2 ^ N := mul_le_mul_of_nonneg_right hN2 (by positivity)
      _ = Real.exp (N * (2 * Real.log 2)) := by
          rw [two_pow_eq_exp, ← Real.exp_add]; ring_nf
  calc (N : ℝ) * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2))
      ≤ Real.exp (N * (2 * Real.log 2)) * (2 * Real.exp (-((N : ℝ) ^ 2) / 2)) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = 2 * Real.exp (N * (2 * Real.log 2) + -((N : ℝ) ^ 2) / 2) := by rw [Real.exp_add]; ring
    _ ≤ 2 * Real.exp (-26) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.2; nlinarith
    _ ≤ 1 / 48 := by
        have : Real.exp (-26) ≤ 1 / 96 := by
          rw [Real.exp_neg, inv_eq_one_div, one_div_le_one_div (Real.exp_pos _) (by norm_num)]
          have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 26); linarith
        linarith

/-- **The conditional bound for `UnivGood`** (the analogue of `RestGood_cond`), from the
small-cut bounds `smallC_cond'`, `smallE_cond'` (all proved). -/
theorem UnivGood_cond : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    ∀ f : rowsA s r0 x → Fin N → ℝ, ∀ g0 : {r // r ∉ rowsA s r0 x} → Fin N → ℝ,
      (glueRows (rowsA s r0 x) f g0 ∈ EX N s r0 x ∧ EXFacts N s r0 x (glueRows (rowsA s r0 x) f g0)) →
      rowsOutM (rowsA s r0 x) {g | ¬ UnivGood N s r0 x (glueRows (rowsA s r0 x) f g)} ≤ 1 / 8 := by
  filter_upwards [smallC_cond', smallE_cond', eventually_ge_atTop 4, ev_low_small, ev_up_small,
    ev_conc_small] with N hC hE hN4 e1 e2 e3
  intro s r0 x hham f g0 hfix
  have hsA : s ∈ (rowsA s r0 x) := rowsA_mem_s
  have hL := low_cond_gen (rowsA s r0 x) (card_rowsA_le s r0 x) hN4 s f
  have hU := upTe_cond_gen (rowsA s r0 x) hsA f
  have hcC := concC_cond (by omega) s r0 x f
  have hcE := concE_cond (by omega) s r0 x f
  have hsC := hC s r0 x hham f g0 hfix
  have hsE := hE s r0 x hham f g0 hfix
  have hsub : {g | ¬ UnivGood N s r0 x (glueRows (rowsA s r0 x) f g)} ⊆
      {g | ¬ ∀ t : State N, 1 / 2 ≤ ∑ r ∈ (rowsA s r0 x)ᶜ, fullProb (tpmOf (flipP s (glueRows (rowsA s r0 x) f g))) r t} ∪
      {g | ¬ ∑ r ∈ (rowsA s r0 x)ᶜ, fullProb (tpmOf (flipP s (glueRows (rowsA s r0 x) f g))) r (teW (glueRows (rowsA s r0 x) f g) s) ≤ 3 / 2} ∪
      {g | ¬ ∀ j C, j ∉ C → DU N ≤ C.card →
        |cmean (glueRows (rowsA s r0 x) f g) (univ \ C) r0 j - 1 / 2| ≤ dU N C.card} ∪
      {g | ¬ ∀ j C, j ∉ C → DU N ≤ C.card →
        |effUnit (tpmOf (flipP s (glueRows (rowsA s r0 x) f g))) Cᶜ s j (teW (glueRows (rowsA s r0 x) f g) s j) - 1 / 2| ≤
          dU N C.card} ∪
      {g | ¬ ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N → K ≠ {x} →
        8 * (DU N : ℝ) < ∑ j ∈ Kᶜ,
          min (Real.logb 2 (clamp01 (glueRows (rowsA s r0 x) f g r0 j) / cmean (glueRows (rowsA s r0 x) f g) (univ \ K) r0 j))
            (cpx (fun j => clamp01 (glueRows (rowsA s r0 x) f g r0 j))
              (rowMinU fun j => clamp01 (glueRows (rowsA s r0 x) f g r0 j)) (dU N (N - 1)) j)} ∪
      {g | ¬ ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N →
        8 * (DU N : ℝ) < ∑ j ∈ Kᶜ,
          min (Real.logb 2 (xE (glueRows (rowsA s r0 x) f g) s j /
              effUnit (tpmOf (flipP s (glueRows (rowsA s r0 x) f g))) Kᶜ s j (teW (glueRows (rowsA s r0 x) f g) s j)))
            (cpx (xE (glueRows (rowsA s r0 x) f g) s) (rowMinU (xE (glueRows (rowsA s r0 x) f g) s)) (dU N (N - 1)) j)} := by
    intro g hg
    by_contra hno
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hno
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hno
    exact hg ⟨h1, h2, h3, h4, h5, h6⟩
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
      (add_le_add hL hU)) hcC)) hcE)) hsC)) hsE).trans ?_
  have q48 : (1 / 48 : ENNReal) = ENNReal.ofReal (1 / 48) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  have c1 : ENNReal.ofReal (2 ^ N * Real.exp (-((3 / 2 : ℝ) ^ N / 32))) ≤ ENNReal.ofReal (1 / 48) :=
    ENNReal.ofReal_le_ofReal e1
  have c2 : ENNReal.ofReal (4 * (2 / 3 : ℝ) ^ N) ≤ ENNReal.ofReal (1 / 48) := ENNReal.ofReal_le_ofReal e2
  have c3 : ENNReal.ofReal ((N : ℝ) * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2))) ≤ ENNReal.ofReal (1 / 48) :=
    ENNReal.ofReal_le_ofReal e3
  rw [q48] at hsC hsE ⊢
  calc _ ≤ ENNReal.ofReal (1 / 48) + ENNReal.ofReal (1 / 48) + ENNReal.ofReal (1 / 48) +
        ENNReal.ofReal (1 / 48) + ENNReal.ofReal (1 / 48) + ENNReal.ofReal (1 / 48) := by gcongr
    _ = ENNReal.ofReal (1 / 8) := by
        simp only [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 48) (by norm_num : (0 : ℝ) ≤ 1 / 48)]
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num),
          ← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
    _ = 1 / 8 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp


theorem RestGood_cond8 : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    ∀ f : rowsA s r0 x → Fin N → ℝ, ∀ g0 : {r // r ∉ rowsA s r0 x} → Fin N → ℝ,
      (glueRows (rowsA s r0 x) f g0 ∈ EX N s r0 x ∧ EXFacts N s r0 x (glueRows (rowsA s r0 x) f g0)) →
      rowsOutM (rowsA s r0 x) {g | ¬ RestGood N s r0 x (glueRows (rowsA s r0 x) f g)} ≤ 1 / 8 := by
  -- the rate: 2^N e^{-N(x0 - 1 - ln x0)} → 0 since x0 - 1 - ln x0 > ln 2 + 1/10
  have hx0 := cr_x0_bounds
  have hlx : Real.log x0 ≤ -(3 / 2) := by
    have h1 : x0 ≤ 2027325541 / 10000000000 := by have := hx0.2; unfold crX0hi at this; push_cast at this; exact this
    have h2 : (0 : ℝ) < x0 := by have := hx0.1; unfold crX0lo at this; push_cast at this; linarith
    rw [Real.log_le_iff_le_exp h2]
    have he := Real.exp_one_lt_d9
    have hq : Real.exp (1 / 4) < 1 / (1 - 1 / 4) := Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
    have e32 : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 4) ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have hb : Real.exp (3 / 2) ≤ 2.7182818286 * (4 / 3) ^ 2 := by
      rw [e32]
      have h0 : 0 ≤ Real.exp (1 / 4) := (Real.exp_pos _).le
      have : Real.exp (1 / 4) ^ 2 ≤ (4 / 3) ^ 2 := pow_le_pow_left₀ h0 (by norm_num at hq ⊢; linarith) 2
      nlinarith [Real.exp_pos 1, Real.exp_pos (1 / 4)]
    have hm : Real.exp (-(3 / 2)) = (Real.exp (3 / 2))⁻¹ := Real.exp_neg _
    rw [hm]
    calc x0 ≤ 2027325541 / 10000000000 := h1
      _ ≤ (2.7182818286 * (4 / 3) ^ 2)⁻¹ := by norm_num
      _ ≤ (Real.exp (3 / 2))⁻¹ := inv_anti₀ (Real.exp_pos _) hb
  have hrate : Real.log 2 + 1 / 200 ≤ x0 - 1 - Real.log x0 := by
    have := Real.log_two_lt_d9; have := hx0.1; unfold crX0lo at this; push_cast at this; linarith
  have hev : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ N * Real.exp (-(N * (x0 - 1 - Real.log x0))) ≤ 1 / 8 := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.log 8 / (1 / 200))] with N hN
    rw [div_le_iff₀ (by norm_num)] at hN
    have h2N : (2 : ℝ) ^ N = Real.exp (Real.log 2 * N) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    rw [h2N, ← Real.exp_add, show (1 / 8 : ℝ) = Real.exp (-Real.log 8) by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num]
    apply Real.exp_le_exp.2
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [mul_le_mul_of_nonneg_left hrate hN0]
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  intro s r0 x _ f g0 _
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hx0p : 0 < x0 := by have := hx0.1; unfold crX0lo at this; push_cast at this; linarith
  have hx01 : x0 ≤ 1 := by have := hx0.2; unfold crX0hi at this; push_cast at this; linarith
  have hsub : {g | ¬ RestGood N s r0 x (glueRows (rowsA s r0 x) f g)} ⊆
      {V : {r // r ∉ (rowsA s r0 x)} → Fin N → ℝ | ∃ r, ∑ i ∈ (univ : Finset (Fin N)), -Real.log (clamp01 (V r i)) ≤ x0 * N} := by
    intro g hg
    by_contra hno
    simp only [Set.mem_setOf_eq, not_exists, not_le] at hno
    exact hg ⟨fun r hr => by
      have := (hno ⟨r, hr⟩).le
      rw [show XW (glueRows (rowsA s r0 x) f g) r = ∑ i, -Real.log (clamp01 (g ⟨r, hr⟩ i)) by
        unfold XW; rw [glueRows_of_not_mem (rowsA s r0 x) f g hr]]
      exact this⟩
  have hcard : (Finset.univ : Finset (Fin N)).card = N := by simp
  refine (measure_mono (μ := rowsOutM (rowsA s r0 x)) hsub).trans ?_
  have ht := pi_rows_negLog_tail (R := {r // r ∉ (rowsA s r0 x)}) (N := N) (univ : Finset (Fin N)) (x := x0 * N)
    (by positivity) (by rw [hcard]; nlinarith)
  unfold rowsOutM
  refine ht.trans ?_
  rw [hcard, show x0 * (N : ℝ) / N = x0 by field_simp]
  have hR : (Fintype.card {r // r ∉ (rowsA s r0 x)} : ℝ) ≤ 2 ^ N := by
    have := Fintype.card_subtype_le (fun r : State N => r ∉ (rowsA s r0 x))
    have h2 : Fintype.card (State N) = 2 ^ N := by simp
    exact_mod_cast h2 ▸ this
  calc ENNReal.ofReal (Fintype.card {r // r ∉ (rowsA s r0 x)} * Real.exp (-(N * (x0 - 1 - Real.log x0))))
      ≤ ENNReal.ofReal ((2 : ℝ) ^ N * Real.exp (-(N * (x0 - 1 - Real.log x0)))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hR (Real.exp_pos _).le)
    _ ≤ ENNReal.ofReal (1 / 8) := ENNReal.ofReal_le_ofReal hN
    _ = 1 / 8 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp


/-- **The combined conditional bound**: `RestGood ∧ UnivGood` fails with conditional probability `≤ 1/4`. -/
theorem RestUniv_cond : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    ∀ f : rowsA s r0 x → Fin N → ℝ, ∀ g0 : {r // r ∉ rowsA s r0 x} → Fin N → ℝ,
      (glueRows (rowsA s r0 x) f g0 ∈ EX N s r0 x ∧ EXFacts N s r0 x (glueRows (rowsA s r0 x) f g0)) →
      rowsOutM (rowsA s r0 x) {g | ¬ (RestGood N s r0 x (glueRows (rowsA s r0 x) f g) ∧
        UnivGood N s r0 x (glueRows (rowsA s r0 x) f g))} ≤ 1 / 4 := by
  filter_upwards [RestGood_cond8, UnivGood_cond] with N h1 h2
  intro s r0 x hham f g0 hfix
  have hsub : {g | ¬ (RestGood N s r0 x (glueRows (rowsA s r0 x) f g) ∧
      UnivGood N s r0 x (glueRows (rowsA s r0 x) f g))} ⊆
      {g | ¬ RestGood N s r0 x (glueRows (rowsA s r0 x) f g)} ∪
        {g | ¬ UnivGood N s r0 x (glueRows (rowsA s r0 x) f g)} := by
    intro g hg
    by_cases h : RestGood N s r0 x (glueRows (rowsA s r0 x) f g)
    · exact Or.inr fun hu => hg ⟨h, hu⟩
    · exact Or.inl h
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  calc _ ≤ (1 / 8 : ENNReal) + 1 / 8 := add_le_add (h1 s r0 x hham f g0 hfix) (h2 s r0 x hham f g0 hfix)
    _ = 1 / 4 := by
        have e8 : (1 / 8 : ENNReal) = ENNReal.ofReal (1 / 8) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
        have e4 : (1 / 4 : ENNReal) = ENNReal.ofReal (1 / 4) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
        rw [e8, e4, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num

/-! ### Drop-in replacement for `EX_B1_half` -/


end Census
end IIT
