/-
Census, B1 lower bound, leaf `phi_univ_ge_EX`: `smallC_cond'` — the cause-side small-cut sums hold with
conditional probability `≥ 1 - 1/48` (union over `K` of the column Hoeffding bound, the per-`K` chain
`K_bound_C`, the expected losses `PsiC_int_le`, the cell margin `cause_cells_sum`).
-/
import IIT.Census.B1UnivSmallC

set_option maxRecDepth 100000

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

variable {N : ℕ}

/-! ### The bottom strip is occupied -/

set_option maxHeartbeats 0 in
lemma exP0_facts : (exPCells[0]'(by simp only [exPCells_len]; norm_num)).sa = 0 ∧
    (1 / 2000 : ℚ) ≤ (exPCells[0]'(by simp only [exPCells_len]; norm_num)).a := by
  constructor <;> decide +kernel

lemma KP_eq : KP = 4159 := by simp only [KP, exPCells_len]

/-- **Some entry of row `r0` lies in the bottom strip.** -/
lemma bottom_C {s r0 : State N} {x : Fin N} {w : Param N} (hw : w ∈ EX N s r0 x)
    (hN : 2000 * 4159 < N) : rowMinU (fun j => clamp01 (w r0 j)) ≤ ((ucYm : ℚ) : ℝ) := by
  classical
  set i0 : Fin KP := ⟨0, by rw [KP_eq]; norm_num⟩
  obtain ⟨hsa, ha⟩ := exP0_facts
  have hpos : 0 < nP N i0 := by
    have h := nP_err N i0
    have ha' : (1 / 2000 : ℝ) ≤ ((cP i0).a : ℝ) := by
      have : (cP i0) = exPCells[0]'(by simp only [exPCells_len]; norm_num) := rfl
      rw [this]; have := (Rat.cast_le (K := ℝ)).2 ha; push_cast at this; exact this
    have hNr : (2000 * 4159 : ℝ) < N := by exact_mod_cast hN
    have hKP : (KP : ℝ) = 4159 := by rw [KP_eq]; norm_num
    have : (0 : ℝ) < nP N i0 := by
      have := (abs_le.1 h).1
      nlinarith
    exact_mod_cast this
  rw [← hw.1 i0] at hpos
  obtain ⟨j, hj⟩ := card_pos.1 hpos
  have hj' := (mem_filter.1 hj).2
  have hm := cell_mem (cP_mem i0) hj'
  refine (rowMinU_le _ j).trans ?_
  rw [hm.2.2.2.2.2.2.2.1]
  have h1 := hj'.1.2
  have e : ((exYlo (cP i0) + exHy : ℚ) : ℝ) = ((ucYm : ℚ) : ℝ) := by
    have : (cP i0).sa = 0 := hsa
    unfold exYlo ucYm ucF exF; rw [this]; push_cast; ring
  rw [e] at h1
  exact h1.le

/-! ### Counting the small sets -/

lemma card_small_sets (D : ℕ) (hN : 1 ≤ N) :
    ((univ : Finset (Finset (Fin N))).filter (fun K => K.card < D)).card ≤ D * N ^ D := by
  classical
  have hsub : (univ : Finset (Finset (Fin N))).filter (fun K => K.card < D) ⊆
      (range D).biUnion fun k => powersetCard k univ := by
    intro K hK
    simp only [mem_filter, mem_univ, true_and] at hK
    simp only [mem_biUnion, mem_range, mem_powersetCard]
    exact ⟨K.card, hK, subset_univ K, rfl⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ k ∈ range D, (powersetCard k (univ : Finset (Fin N))).card
      ≤ ∑ _k ∈ range D, N ^ D := sum_le_sum fun k hk => by
        rw [card_powersetCard, card_univ, Fintype.card_fin]
        exact (Nat.choose_le_pow N k).trans (Nat.pow_le_pow_right hN (mem_range.1 hk).le)
    _ = D * N ^ D := by rw [sum_const, card_range, smul_eq_mul]

/-! ### Asymptotics -/

lemma DU_le_log (N : ℕ) : (DU N : ℝ) ≤ 6 * Real.log N + 20 := by
  unfold DU
  push_cast
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · have h1 := Real.natLog_le_logb N 2
    simp only [Nat.cast_ofNat] at h1
    have h2 : Real.logb 2 N = Real.log N / Real.log 2 := rfl
    have hl2 : (69 / 100 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have h3 : Real.log N / Real.log 2 ≤ 3 / 2 * Real.log N := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    rw [h2] at h1
    linarith

lemma ev_small_union : ∀ᶠ N : ℕ in atTop,
    (DU N : ℝ) * N ^ DU N * (2 * Real.exp (-((N : ℝ) / 5000))) ≤ 1 / 48 := by
  -- `log` of the left side is `≤ O(log² N) - N/5000`
  have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 100000 by norm_num))
  have ht1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have hev1 := ht1.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 100000 by norm_num))
  filter_upwards [hev, hev1, eventually_ge_atTop (10 ^ 7)] with N h2 h1 hN
  simp only [Function.comp, one_mul, add_zero] at h2 h1
  have hNr : (10 : ℝ) ^ 7 ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hl2 : Real.log N ^ 2 ≤ N / 100000 := by
    rw [div_lt_iff₀ hN0] at h2; linarith
  have hl1 : Real.log N ≤ N / 100000 := by
    rw [pow_one, div_lt_iff₀ hN0] at h1; linarith
  have hD := DU_le_log N
  have hD0 : (0 : ℝ) < DU N := by unfold DU; positivity
  -- write everything as one exponential
  have e1 : (N : ℝ) ^ DU N = Real.exp (DU N * Real.log N) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < (N : ℝ) ^ DU N), Real.log_pow]
  have e2 : (DU N : ℝ) = Real.exp (Real.log (DU N)) := (Real.exp_log hD0).symm
  have hlD : Real.log (DU N) ≤ DU N := by
    have := Real.log_le_sub_one_of_pos hD0; linarith
  rw [e1]
  calc (DU N : ℝ) * Real.exp (DU N * Real.log N) * (2 * Real.exp (-((N : ℝ) / 5000)))
      = 2 * Real.exp (Real.log (DU N) + DU N * Real.log N + -((N : ℝ) / 5000)) := by
        rw [Real.exp_add, Real.exp_add, ← e2]; ring
    _ ≤ 2 * Real.exp (-26) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.2
        have : (DU N : ℝ) * Real.log N ≤ (6 * Real.log N + 20) * Real.log N :=
          mul_le_mul_of_nonneg_right hD hl
        nlinarith
    _ ≤ 1 / 48 := by
        have : Real.exp (-26) ≤ 1 / 96 := by
          rw [Real.exp_neg, inv_eq_one_div, one_div_le_one_div (Real.exp_pos _) (by norm_num)]
          have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 26); linarith
        linarith


/-! ### The cause-side leaf -/

lemma ucMarg_ge (v : ℕ) : (11 / 400 : ℚ) ≤ ucMarg v := by
  rcases v with _ | _ | _ | v <;>
    simp only [ucMarg, ucMarg_k1, ucMarg_k2in, ucMarg_k2out, ucMarg_k3] <;> norm_num

lemma ev_lin_C : ∀ᶠ N : ℕ in atTop,
    3 * (4159 : ℝ) ^ 2 + 10 * DU N + 2 ≤ (N : ℝ) * (11 / 400 - 10 / 1001 - 1 / 1000) := by
  have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 10000 by norm_num))
  filter_upwards [hev, eventually_ge_atTop (10 ^ 10)] with N h1 hN
  simp only [Function.comp, one_mul, add_zero, pow_one] at h1
  have hNr : (10 : ℝ) ^ 10 ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hl : Real.log N ≤ N / 10000 := by rw [div_lt_iff₀ hN0] at h1; linarith
  have hD := DU_le_log N
  nlinarith

lemma ev_DU3 : ∀ᶠ N : ℕ in atTop, 3 * (DU N + 1) ≤ N := by
  filter_upwards [ev_lin_C, eventually_ge_atTop 1] with N h hN
  have hD : (0 : ℝ) ≤ DU N := Nat.cast_nonneg _
  have : (3 * (DU N + 1) : ℝ) ≤ N := by nlinarith
  exact_mod_cast this

/-- **Leaf `smallC_cond`, proved.** -/
theorem smallC_cond' : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    ∀ f : rowsA s r0 x → Fin N → ℝ, ∀ g0 : {r // r ∉ rowsA s r0 x} → Fin N → ℝ,
      (glueRows (rowsA s r0 x) f g0 ∈ EX N s r0 x ∧ EXFacts N s r0 x (glueRows (rowsA s r0 x) f g0)) →
      rowsOutM (rowsA s r0 x) {g | ¬ ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N → K ≠ {x} →
        8 * (DU N : ℝ) < ∑ j ∈ Kᶜ,
          min (Real.logb 2 (clamp01 (glueRows (rowsA s r0 x) f g r0 j) /
              cmean (glueRows (rowsA s r0 x) f g) (univ \ K) r0 j))
            (cpx (fun j => clamp01 (glueRows (rowsA s r0 x) f g r0 j))
              (rowMinU fun j => clamp01 (glueRows (rowsA s r0 x) f g r0 j)) (dU N (N - 1)) j)} ≤ 1 / 48 := by
  filter_upwards [ev_small_union, ev_N_dU_top, eventually_ge_atTop (2000 * 4159 + 1),
    ev_DU3, ev_lin_C, eventually_ge_atTop (10 ^ 7)] with N hU htop hNb h3 hlin hN7
  intro s r0 x hham f g0 hfix
  classical
  obtain ⟨δ1, hδ1⟩ : ∃ δ1 : ℝ, δ1 = dU N (N - 1) := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = N / 200 := ⟨_, rfl⟩
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hδ0 : 0 ≤ δ1 := hδ1 ▸ dU_nonneg _ _
  have hδN : (N : ℝ) * δ1 ≤ 1 / (2 * 10 ^ 6) := hδ1 ▸ htop
  -- the family of sets
  obtain ⟨𝒦, h𝒦⟩ : ∃ 𝒦 : Finset (Finset (Fin N)), 𝒦 = (univ : Finset (Finset (Fin N))).filter
      (fun K => 1 ≤ K.card ∧ K.card < DU N ∧ K ≠ {x}) := ⟨_, rfl⟩
  have hK𝒦 : ∀ K ∈ 𝒦, K.card < ham r0 s := fun K hK => by
    rw [h𝒦] at hK; have := (mem_filter.1 hK).2.2.1; omega
  -- the fixed rows are on `EX` for every `g`
  have hEXg : ∀ g, glueRows (rowsA s r0 x) f g ∈ EX N s r0 x := fun g =>
    ((EX_local s r0 x (w := glueRows (rowsA s r0 x) f g0) (w' := glueRows (rowsA s r0 x) f g) fun r hr => by
      rw [glueRows_of_mem (rowsA s r0 x) f g hr, glueRows_of_mem (rowsA s r0 x) f g0 hr]).1 hfix).1
  have hym : rowMinU (yvC f) ≤ ((ucYm : ℚ) : ℝ) := by
    have h := bottom_C (hEXg g0) (by omega)
    have e : (fun j => clamp01 (glueRows (rowsA s r0 x) f g0 r0 j)) = yvC f := by
      funext j; rw [glueRows_of_mem (rowsA s r0 x) f g0 rowsA_mem_r0]; rfl
    rwa [e] at h
  -- the bad set is covered
  obtain ⟨B, hB⟩ : ∃ B : Finset (Fin N) → Set ({r // r ∉ (rowsA s r0 x)} → Fin N → ℝ), B = fun K =>
    {g | ε ≤ |∑ j ∈ Kᶜ, (PsiC f K j (colsG (rowsA s r0 x) g j) - ∫ c, PsiC f K j c ∂colLawG (rowsA s r0 x))|} :=
    ⟨_, rfl⟩
  have hsub : {g | ¬ ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N → K ≠ {x} →
      8 * (DU N : ℝ) < ∑ j ∈ Kᶜ,
        min (Real.logb 2 (clamp01 (glueRows (rowsA s r0 x) f g r0 j) / cmean (glueRows (rowsA s r0 x) f g) (univ \ K) r0 j))
          (cpx (fun j => clamp01 (glueRows (rowsA s r0 x) f g r0 j))
            (rowMinU fun j => clamp01 (glueRows (rowsA s r0 x) f g r0 j)) δ1 j)} ⊆ ⋃ K ∈ 𝒦, B K := by
    intro g hg
    by_contra hno
    simp only [Set.mem_iUnion, not_exists, hB, Set.mem_setOf_eq, not_le] at hno
    apply hg
    intro K hK1 hKD hKx
    have hK : K ∈ 𝒦 := by rw [h𝒦]; exact mem_filter.2 ⟨mem_univ _, hK1, hKD, hKx⟩
    have hgood := (abs_lt.1 (hno K hK)).2
    have hKh := hK𝒦 K hK
    have hmain := K_bound_C f g hKh (hEXg g) hym hδ0 hgood
    refine lt_of_lt_of_le ?_ hmain
    -- the numerator
    have hcells := cause_cells_sum (hEXg g) (vC x K)
    have e0 : ∀ j, clamp01 (glueRows (rowsA s r0 x) f g r0 j) = yvC f j := fun j => by
      rw [glueRows_of_mem (rowsA s r0 x) f g rowsA_mem_r0]; rfl
    have e1 : ∀ j, clamp01 (glueRows (rowsA s r0 x) f g (flipAt x r0) j) = UvC f j := fun j => by
      rw [glueRows_of_mem (rowsA s r0 x) f g rowsA_mem_flip]; rfl
    simp_rw [e0, e1] at hcells
    set T : Fin N → ℝ := fun j => Real.log (yvC f j / ((ucYm : ℚ) : ℝ)) -
      numRC (vC x K) (yvC f j) (UvC f j) / (1001 / 2000) with hT
    have hT1 : ∀ j, T j ≤ 1 := fun j => by
      have hy := EX_y_ge (hEXg g) j
      rw [e0] at hy
      have hY : (1 / 2 : ℝ) ≤ ((ucYm : ℚ) : ℝ) := by unfold ucYm ucF; rw [exHy_val]; norm_num
      have h1 : Real.log (yvC f j / ((ucYm : ℚ) : ℝ)) ≤ yvC f j / ((ucYm : ℚ) : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
      have h2 : yvC f j / ((ucYm : ℚ) : ℝ) ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; have := clamp01_le_one (f ⟨r0, rowsA_mem_r0⟩ j)
        unfold yvC at *; linarith
      have h3 := numRC_nonneg (vC x K) (yvC f j) (UvC f j)
      simp only [hT]
      have : 0 ≤ numRC (vC x K) (yvC f j) (UvC f j) / (1001 / 2000) := by positivity
      linarith
    have hint : ∀ j ∈ Kᶜ, T j ≤ Real.log (yvC f j / ((ucYm : ℚ) : ℝ)) -
        (∫ c, PsiC f K j c ∂colLawG (rowsA s r0 x)) / (1001 / 2000) := fun j _ => by
      have hy := EX_y_ge (hEXg g) j
      rw [e0] at hy
      have := PsiC_int_le f hKh hK1 hKx j hy
      simp only [hT]
      have := div_le_div_of_nonneg_right this (by norm_num : (0 : ℝ) ≤ 1001 / 2000)
      linarith
    have hsplit := sum_compl_add_sum K T
    have hKsum : ∑ j ∈ K, T j ≤ K.card := by
      calc ∑ j ∈ K, T j ≤ ∑ _j ∈ K, (1 : ℝ) := sum_le_sum fun j _ => hT1 j
        _ = K.card := by simp
    have hKD' : (K.card : ℝ) ≤ DU N := by exact_mod_cast hKD.le
    have hmarg : ((11 / 400 : ℚ) : ℝ) ≤ (ucMarg (vC x K) : ℝ) := by exact_mod_cast ucMarg_ge _
    have hsumC := sum_le_sum hint
    have hl2 := Real.log_pos one_lt_two
    have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have hKP : (KP : ℝ) = 4159 := by rw [KP_eq]; norm_num
    rw [hKP] at hcells
    have hmargN := mul_le_mul_of_nonneg_left hmarg hN0.le
    push_cast at hmargN
    rw [lt_div_iff₀ hl2]
    have hδ7 : 7 * δ1 * N ≤ 1 := by nlinarith
    have hεf : ε / (1001 / 2000) = (N : ℝ) * (10 / 1001) := by rw [hε]; field_simp; ring
    have hD0 : (0 : ℝ) ≤ DU N := Nat.cast_nonneg _
    nlinarith
  -- the union bound
  rw [← hδ1]
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le 𝒦 B).trans ?_)
  have hpiece : ∀ K ∈ 𝒦, rowsOutM (rowsA s r0 x) (B K) ≤ ENNReal.ofReal (2 * Real.exp (-((N : ℝ) / 5000))) := by
    intro K hK
    have hKh := hK𝒦 K hK
    have hb := cols_hoeffding (rowsA s r0 x) Kᶜ (PsiC f K) (fun j => PsiC_meas f K j) (R := 1 / 2)
      (fun j c => PsiC_mem f hKh j c) (by rw [hε]; positivity : (0 : ℝ) ≤ ε)
    rw [hB]
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.2
    rw [sum_const, nsmul_eq_mul]
    have hc1 : (1 : ℝ) ≤ (Kᶜ).card := by
      have : 0 < (Kᶜ).card := by
        rw [card_compl, Fintype.card_fin]
        rw [h𝒦] at hK; have := (mem_filter.1 hK).2.2.1; omega
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
      exact hK.2.1
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
