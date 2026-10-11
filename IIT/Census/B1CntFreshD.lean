/-
Census, B1, W14 WP4, part D: FE7(a) (fresh effect mass at every target, `lowerTail_nonneg_V` with
`a = (3/2) √N σ_N` and a union over the `2^N` targets) and FE3 (Cramér level `23/50` on fresh subcubes of
dimension `1 … J`: `lintegral_max_pow5_le`, column independence, union over `(N+1)^J 2^N` subcubes).
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §9; math W5 §4.  No `sorry`.
-/
import IIT.Census.B1CntFreshC

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### FE7(a) -/

/-- The fresh-row function of a target `t`. -/
noncomputable def frG7 (s : State N) (F : Finset (State N)) (t : State N) (r : State N)
    (v : Fin N → ℝ) : ℝ :=
  if r ∉ F then frRowPhi (fun k => decide (t k = s k)) v else 0

lemma frG7_mem (s : State N) (F : Finset (State N)) (t r : State N) (v : Fin N → ℝ) :
    frG7 s F t r v ∈ Set.Icc (0 : ℝ) 1 := by
  unfold frG7; by_cases h : r ∈ F
  · simp [h]
  · simp only [h, not_false_eq_true, ite_true]; exact frRowPhi_mem _ _

lemma measurable_frG7 (s : State N) (F : Finset (State N)) (t r : State N) :
    Measurable (frG7 s F t r) := by
  unfold frG7; by_cases h : r ∈ F
  · simp only [h, not_true_eq_false, ite_false]; exact measurable_const
  · simp only [h, not_false_eq_true, ite_true]; exact measurable_frRowPhi _

lemma integral_frG7 (s : State N) (F : Finset (State N)) (t r : State N) :
    ∫ w, frG7 s F t r (w r) ∂cubeM N = if r ∉ F then (1 / 2 : ℝ) ^ N else 0 := by
  rw [integral_row_eval (g := frG7 s F t r) (measurable_frG7 s F t r).aestronglyMeasurable r]
  unfold frG7; by_cases h : r ∈ F
  · simp [h]
  · simp only [h, not_false_eq_true, ite_true]; exact integral_frRowPhi _

lemma integral_frG7_sq (s : State N) (F : Finset (State N)) (t r : State N) :
    ∫ w, frG7 s F t r (w r) ^ 2 ∂cubeM N = if r ∉ F then (1 / 3 : ℝ) ^ N else 0 := by
  rw [integral_row_eval (g := fun v => frG7 s F t r v ^ 2)
    ((measurable_frG7 s F t r).pow_const 2).aestronglyMeasurable r]
  unfold frG7; by_cases h : r ∈ F
  · simp [h]
  · simp only [h, not_false_eq_true, ite_true]; exact integral_frRowPhi_sq _

lemma frD_card_fresh (F : Finset (State N)) :
    (2 : ℝ) ^ N - F.card ≤ ((univ.filter fun r : State N => r ∉ F).card : ℝ) := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (State N))) (fun r => r ∈ F)
  rw [card_state] at h
  have h2 : (univ.filter fun r : State N => r ∈ F).card ≤ F.card :=
    card_le_card fun r hr => (mem_filter.1 hr).2
  have h3 : ((univ.filter fun r : State N => r ∈ F).card : ℝ) +
      ((univ.filter fun r : State N => r ∉ F).card : ℝ) = 2 ^ N := by exact_mod_cast h
  have h4 : ((univ.filter fun r : State N => r ∈ F).card : ℝ) ≤ F.card := by exact_mod_cast h2
  linarith

lemma frD_sum_ite (F : Finset (State N)) (q : ℝ) :
    ∑ r : State N, (if r ∉ F then q else 0) = ((univ.filter fun r : State N => r ∉ F).card : ℝ) * q := by
  rw [← sum_filter, sum_const, nsmul_eq_mul]

/-- `4 (N+1)^4 ≤ σ_N 2^N` once `16 (N+1)^8 ≤ 2^N`. -/
lemma frD_poly_le_sig (hN : 1 ≤ N) (hev : 3 + 8 * (Real.log N + 1) ^ 2 ≤ 1 / 2 * N) :
    4 * ((N : ℝ) + 1) ^ 4 ≤ sigN N * 2 ^ N := by
  have hL := frA_log_nonneg N
  have hpow := frA_pow_le_exp hN 8
  have he3 : (16 : ℝ) ≤ Real.exp 3 := by
    have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 := Real.exp_one_gt_d9
    rw [h2]
    calc (16 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
      _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h3.le 3
  have h2N : Real.exp (1 / 2 * N) ≤ (2 : ℝ) ^ N := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ N), Real.log_pow]
    apply Real.exp_le_exp.2
    have := Real.log_two_gt_d9
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hA : 16 * ((N : ℝ) + 1) ^ 8 ≤ (2 : ℝ) ^ N := by
    calc 16 * ((N : ℝ) + 1) ^ 8 ≤ Real.exp 3 * Real.exp (8 * (Real.log N + 1)) := by
          gcongr; push_cast at hpow; exact hpow
      _ = Real.exp (3 + 8 * (Real.log N + 1)) := by rw [← Real.exp_add]
      _ ≤ Real.exp (1 / 2 * N) := Real.exp_le_exp.2 (by nlinarith)
      _ ≤ 2 ^ N := h2N
  have hB : (2 : ℝ) ^ N ≤ (sigN N * 2 ^ N) ^ 2 := by
    have e1 : ((2 : ℝ) ^ N) ^ 2 = 4 ^ N := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [mul_pow, frC_sigN_sq, e1, ← mul_pow]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) N
  have hpos : 0 ≤ sigN N * 2 ^ N := by have := sigN_pos N; positivity
  have hsq : (4 * ((N : ℝ) + 1) ^ 4) ^ 2 ≤ (sigN N * 2 ^ N) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (4 * ((N : ℝ) + 1) ^ 4 - sigN N * 2 ^ N),
    sq_nonneg (4 * ((N : ℝ) + 1) ^ 4 + sigN N * 2 ^ N)]

/-- **FE7(a)**: failure `≤ 2^N e^{-9N/8}`. -/
theorem freshFE7a : FreshFieldProb FE7aX (1 / 180) := by
  filter_upwards [eventually_ge_atTop 1, frA_ev_logsq 3 8 (δ := 1 / 2) (by norm_num)] with
    N hN hev s r0 f
  set σ := sigN N with hσ
  have hσ0 : 0 < σ := sigN_pos N
  set a : ℝ := 3 / 2 * Real.sqrt N * σ with ha
  have ha0 : 0 ≤ a := by positivity
  set E : State N → Set (Param N) := fun t =>
    {w | ∑ r, frG7 s (sensRows s r0) t r (w r) ≤ ∑ r, ∫ w', frG7 s (sensRows s r0) t r (w' r) ∂cubeM N - a} with hE
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsq : (1 : ℝ) ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hN'
  refine (frA_transfer (sensRows s r0) f (FE7aX N s r0) (B := ⋃ t, E t) fun w hw => ?_).trans ?_
  · simp only [FE7aX, not_forall, not_le] at hw
    obtain ⟨t, ht⟩ := hw
    refine Set.mem_iUnion.2 ⟨t, ?_⟩
    simp only [hE, Set.mem_ofPred_eq]
    have e : ∑ r ∈ freshRows s r0, rowTX (glueRows (sensRows s r0) f (restrOut (sensRows s r0) w)) s r t =
        ∑ r, frG7 s (sensRows s r0) t r (w r) := by
      unfold freshRows frG7
      rw [sum_filter]
      refine sum_congr rfl fun r _ => ?_
      split_ifs with h
      · rfl
      · rw [rowTX_eq_frRowPhi, frA_glue_fresh _ f w h]
    rw [e] at ht
    have hmean : ∑ r, ∫ w', frG7 s (sensRows s r0) t r (w' r) ∂cubeM N =
        ((univ.filter fun r : State N => r ∉ (sensRows s r0)).card : ℝ) * (1 / 2) ^ N := by
      simp only [integral_frG7]; exact frD_sum_ite (sensRows s r0) _
    rw [hmean]
    have hcard := frD_card_fresh (sensRows s r0)
    have hF4 : ((sensRows s r0).card : ℝ) ≤ 2 * ((N : ℝ) + 1) ^ 4 := by
      have := card_sensRows_le s r0; exact_mod_cast this
    have hkey := frD_poly_le_sig hN hev
    have h2 : (0 : ℝ) < 2 ^ N := by positivity
    have hhalf : (2 : ℝ) ^ N * (1 / 2) ^ N = 1 := by rw [← mul_pow]; norm_num
    have hlow : 1 - 2 * ((N : ℝ) + 1) ^ 4 * (1 / 2) ^ N ≤
        ((univ.filter fun r : State N => r ∉ (sensRows s r0)).card : ℝ) * (1 / 2) ^ N := by
      have hp : (0 : ℝ) ≤ (1 / 2) ^ N := by positivity
      nlinarith
    have hpoly : 2 * ((N : ℝ) + 1) ^ 4 * (1 / 2) ^ N ≤ 1 / 2 * Real.sqrt N * σ := by
      have h1 : 2 * ((N : ℝ) + 1) ^ 4 ≤ 1 / 2 * σ * 2 ^ N := by linarith
      have h3 : 2 * ((N : ℝ) + 1) ^ 4 * (1 / 2) ^ N ≤ 1 / 2 * σ := by
        calc 2 * ((N : ℝ) + 1) ^ 4 * (1 / 2) ^ N ≤ 1 / 2 * σ * 2 ^ N * (1 / 2) ^ N := by gcongr
          _ = 1 / 2 * σ := by rw [mul_assoc, hhalf, mul_one]
      nlinarith
    have hN4 : 0 ≤ 2 * (N : ℝ) ^ 4 / 2 ^ N := by positivity
    linarith
  · refine (cubeM_iUnion_le E (b := Real.exp (-(9 / 8 * N))) fun t => ?_).trans ?_
    · have hind : iIndepFun (fun r (w : Param N) => frG7 s (sensRows s r0) t r (w r)) (cubeM N) :=
        iIndepFun_rows (frG7 s (sensRows s r0) t) (measurable_frG7 s (sensRows s r0) t)
      have hV : (0 : ℝ) < (2 / 3) ^ N := by positivity
      have hVs : ∑ r, ∫ w', frG7 s (sensRows s r0) t r (w' r) ^ 2 ∂cubeM N ≤ (2 / 3 : ℝ) ^ N := by
        simp only [integral_frG7_sq]
        rw [frD_sum_ite]
        have : ((univ.filter fun r : State N => r ∉ (sensRows s r0)).card : ℝ) ≤ 2 ^ N := by
          have := card_filter_le (univ : Finset (State N)) (fun r => r ∉ (sensRows s r0))
          rw [card_state] at this; exact_mod_cast this
        calc ((univ.filter fun r : State N => r ∉ (sensRows s r0)).card : ℝ) * (1 / 3) ^ N
            ≤ 2 ^ N * (1 / 3) ^ N := by gcongr
          _ = (2 / 3) ^ N := by rw [← mul_pow]; norm_num
      refine (lowerTail_nonneg_V (μ := cubeM N) univ hind
        (fun r => (measurable_frG7 s (sensRows s r0) t r).comp (measurable_pi_apply r))
        (fun r w => frG7_mem s (sensRows s r0) t r (w r)) ha0 hV hVs).trans ?_
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      have e : a ^ 2 / (2 * (2 / 3 : ℝ) ^ N) = 9 / 8 * N := by
        rw [ha, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), hσ, frC_sigN_sq]
        field_simp; ring
      rw [e]
    · apply ENNReal.ofReal_le_ofReal
      rw [frB_card_state]
      push_cast
      calc (2 : ℝ) ^ N * Real.exp (-(9 / 8 * N)) ≤ Real.exp (7 / 10 * N) * Real.exp (-(9 / 8 * N)) := by
            gcongr; exact frB_two_pow_le N
        _ = Real.exp (-(17 / 40 * N)) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ Real.exp (-(1 / 180 * N)) := Real.exp_le_exp.2 (by nlinarith)

/-! ### FE3 -/

/-- One fresh subcube: `P(Σ_i log max(2Ā_i, 1) ≥ 23N/50) ≤ 4^N e^{-23N/10}`. -/
lemma frD_fe3_one {A : Finset (Fin N)} (hA : A.card < N) (t : State N) :
    cubeM N {w | 23 / 50 * (N : ℝ) ≤ ∑ i, Real.log (max (2 * cmCol A t (colsOf w i)) 1)} ≤
      ENNReal.ofReal ((4 * Real.exp (-(23 / 10))) ^ N) := by
  set Fn : (State N → ℝ) → ℝ := fun c => Real.log (max (2 * cmCol A t c) 1) with hFn
  have hFm : Measurable Fn := Real.measurable_log.comp
    (((measurable_cmCol A t).const_mul 2).max measurable_const)
  set X : Fin N → Param N → ℝ := fun i w => Fn (colsOf w i) with hX
  have hind : iIndepFun X (cubeM N) := iIndepFun_cols.comp (fun _ => Fn) (fun _ => hFm)
  have hmeas : ∀ i, Measurable (X i) := fun i => hFm.comp (measurable_colOf i)
  have h := chernoff_indep_ge (μ := cubeM N) univ hind hmeas (a := 23 / 50 * (N : ℝ)) (t := 5)
    (by norm_num)
  refine h.trans ?_
  have hI : ∀ i, ∫⁻ w, ENNReal.ofReal (Real.exp (5 * X i w)) ∂cubeM N ≤ ENNReal.ofReal 4 := by
    intro i
    have hg : Measurable fun c : State N → ℝ => ENNReal.ofReal (Real.exp (5 * Fn c)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hFm.const_mul 5))
    refine le_trans (le_of_eq ((mp_colOf i).lintegral_comp hg)) ?_
    refine le_trans (le_of_eq (lintegral_congr fun c => ?_)) (lintegral_max_pow5_le hA t)
    congr 1
    simp only [hFn]
    have hpos : 0 < max (2 * cmCol A t c) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hpos]
  calc ENNReal.ofReal (Real.exp (-5 * (23 / 50 * (N : ℝ)))) *
        ∏ i, ∫⁻ w, ENNReal.ofReal (Real.exp (5 * X i w)) ∂cubeM N
      ≤ ENNReal.ofReal (Real.exp (-5 * (23 / 50 * (N : ℝ)))) * ∏ _i : Fin N, ENNReal.ofReal 4 := by
        gcongr with i hi
        exact hI i
    _ = ENNReal.ofReal ((4 * Real.exp (-(23 / 10))) ^ N) := by
        rw [prod_const, card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow (by norm_num),
          ← ENNReal.ofReal_mul (by positivity), mul_pow, ← Real.exp_nat_mul]
        congr 1
        rw [mul_comm]
        congr 1
        ring_nf

lemma frD_card_big (J : ℕ) :
    ((univ : Finset (Finset (Fin N))).filter fun A => N ≤ A.card + J).card ≤ (N + 1) ^ J := by
  set S := (univ : Finset (Finset (Fin N))).filter fun A => N ≤ A.card + J
  have h1 : S.card = (S.image compl).card := (card_image_of_injective _ compl_injective).symm
  have h2 : S.image compl ⊆ (range (J + 1)).biUnion fun k => (univ : Finset (Fin N)).powersetCard k := by
    intro B hB
    rw [mem_image] at hB
    obtain ⟨A, hA, rfl⟩ := hB
    rw [mem_filter] at hA
    rw [mem_biUnion]
    refine ⟨Aᶜ.card, mem_range.2 ?_, mem_powersetCard.2 ⟨subset_univ _, rfl⟩⟩
    rw [card_compl, Fintype.card_fin]; omega
  rw [h1]
  refine (card_le_card h2).trans (card_biUnion_le.trans ?_)
  simp only [card_powersetCard, card_univ, Fintype.card_fin]
  exact sum_choose_le_succ_pow N J

/-- **FE3**: failure `≤ (N+1)^J 2^N 4^N e^{-2.3N}`. -/
theorem freshFE3 : FreshFieldProb FE3X (1 / 180) := by
  filter_upwards [eventually_ge_atTop 1, frA_ev_logsq 0 16 (δ := 19 / 100) (by norm_num)] with
    N hN hev s r0 f
  set 𝒜 := (univ : Finset (Finset (Fin N))).filter fun A => N ≤ A.card + JC N ∧ A.card < N with h𝒜
  set E : Finset (Fin N) × State N → Set (Param N) := fun p =>
    {w | 23 / 50 * (N : ℝ) ≤ ∑ i, Real.log (max (2 * cmCol p.1 p.2 (colsOf w i)) 1)} with hE
  refine (frA_transfer (sensRows s r0) f (FE3X N s r0)
    (B := ⋃ p ∈ 𝒜 ×ˢ (univ : Finset (State N)), E p) fun w hw => ?_).trans ?_
  · simp only [FE3X, not_forall, not_le, exists_prop] at hw
    obtain ⟨t, A, hJ, hAN, hfr, hlt⟩ := hw
    refine Set.mem_biUnion (x := (A, t)) (Finset.mem_coe.2 (mem_product.2
      ⟨mem_filter.2 ⟨mem_univ _, hJ, hAN⟩, mem_univ _⟩)) ?_
    simp only [hE, Set.mem_ofPred_eq]
    have e : ∀ i, subMean (glueRows (sensRows s r0) f (restrOut (sensRows s r0) w)) A t i =
        cmCol A t (colsOf w i) := by
      intro i
      rw [subMean_eq_colMean, colMean_eq_cmCol]
      unfold cmCol colsOf
      congr 1
      exact sum_congr rfl fun r hr => by rw [frA_glue_fresh _ f w (hfr r hr)]
    simp only [e] at hlt
    exact hlt.le
  · refine (measure_biUnion_finset_le _ _).trans ?_
    have hone : ∀ p ∈ 𝒜 ×ˢ (univ : Finset (State N)),
        cubeM N (E p) ≤ ENNReal.ofReal ((4 * Real.exp (-(23 / 10))) ^ N) := by
      intro p hp
      have hA : p.1.card < N := (mem_filter.1 (mem_product.1 hp).1).2.2
      exact frD_fe3_one hA p.2
    refine (sum_le_sum hone).trans ?_
    rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hc𝒜 : ((𝒜 ×ˢ (univ : Finset (State N))).card : ℝ) ≤ ((N : ℝ) + 1) ^ JC N * 2 ^ N := by
      rw [card_product, card_univ, frB_card_state]
      have h1 : 𝒜.card ≤ (N + 1) ^ JC N :=
        (card_le_card fun A hA => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hA).2.1⟩).trans
          (frD_card_big (JC N))
      exact_mod_cast Nat.mul_le_mul_right (2 ^ N) h1
    have hpow := frA_pow_le_exp hN (JC N)
    have hJ := frA_JC_le hN
    have hL := frA_log_nonneg N
    have hJL : (JC N : ℝ) * (Real.log N + 1) ≤ 16 * (Real.log N + 1) ^ 2 := by nlinarith
    have h4 : (4 * Real.exp (-(23 / 10))) ^ N ≤ Real.exp (14 / 10 * N) * Real.exp (-(23 / 10 * N)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      gcongr
      · have := frB_two_pow_le N
        calc (4 : ℝ) ^ N = (2 ^ N) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          _ ≤ Real.exp (7 / 10 * N) ^ 2 := by gcongr
          _ = Real.exp (14 / 10 * N) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      · exact le_of_eq (by ring_nf)
    have h40 : 0 ≤ (4 * Real.exp (-(23 / 10))) ^ N := by positivity
    calc ((𝒜 ×ˢ (univ : Finset (State N))).card : ℝ) * (4 * Real.exp (-(23 / 10))) ^ N
        ≤ ((N : ℝ) + 1) ^ JC N * 2 ^ N * (Real.exp (14 / 10 * N) * Real.exp (-(23 / 10 * N))) :=
          mul_le_mul hc𝒜 h4 h40 (by positivity)
      _ ≤ Real.exp (16 * (Real.log N + 1) ^ 2) * Real.exp (7 / 10 * N) *
            (Real.exp (14 / 10 * N) * Real.exp (-(23 / 10 * N))) := by
          gcongr
          · exact hpow.trans (Real.exp_le_exp.2 hJL)
          · exact frB_two_pow_le N
      _ = Real.exp (16 * (Real.log N + 1) ^ 2 - 2 / 10 * N) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-(1 / 180 * N)) := Real.exp_le_exp.2 (by linarith)

end Census
end IIT

#print axioms IIT.Census.freshFE7a
#print axioms IIT.Census.freshFE3
