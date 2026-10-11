/-
Census, B1, W14 WP4, part B: the fresh fields FE1 (Hoeffding per subcube and column), FE2 (row excess
near `Sens`, `rowM_excBad_le`) and FE6 (no heavy fresh row, `cubeM_rows_negLog_tail`).
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §9; math W5 §4, W9 §5.1.  No `sorry`.
-/
import IIT.Census.B1CntFreshA

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### Small numerics -/

lemma frB_two_pow_le (N : ℕ) : (2 : ℝ) ^ N ≤ Real.exp (7 / 10 * N) := by
  rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ N), Real.log_pow]
  apply Real.exp_le_exp.2
  have := Real.log_two_lt_d9
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

lemma frB_nat_le_exp (N : ℕ) : (N : ℝ) ≤ Real.exp N := by
  have := Real.add_one_le_exp (N : ℝ); linarith

lemma frB_card_state : Fintype.card (State N) = 2 ^ N := by
  simp [State, Fintype.card_bool, Fintype.card_fin]

lemma frB_cubeM_row (r : State N) {S : Set (Fin N → ℝ)} (hS : MeasurableSet S) :
    cubeM N {w | w r ∈ S} = rowM N S := by
  unfold cubeM
  exact (measurePreserving_eval (fun _ : State N => rowM N) r).measure_preimage hS.nullMeasurableSet

/-! ### FE1 -/

lemma frB_integral_clamp_row (r : State N) (i : Fin N) :
    ∫ w, clamp01 (w r i) ∂cubeM N = 1 / 2 := by
  have h1 : ∫ w, clamp01 (w r i) ∂cubeM N = ∫ v, clamp01 (v i) ∂rowM N :=
    integral_row_eval (g := fun v => clamp01 (v i))
      (clamp01_measurable.comp (measurable_pi_apply i)).aestronglyMeasurable r
  have h2 : ∫ v, clamp01 (v i) ∂rowM N = ∫ x, clamp01 x ∂unif :=
    integral_pi_eval unif clamp01_measurable.aestronglyMeasurable i
  rw [h1, h2]
  have := integral_cl_pow 1
  simp only [pow_one] at this
  rw [this]; norm_num

/-- Hoeffding for the fresh part of one column of one subcube. -/
lemma frB_hoeff (S : Finset (State N)) (i : Fin N) {ε : ℝ} (hε : 0 ≤ ε) :
    cubeM N {w | ε ≤ |∑ r ∈ S, (clamp01 (w r i) - 1 / 2)|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * ε ^ 2 / S.card)) := by
  set X : State N → Param N → ℝ := fun r w => clamp01 (w r i) with hX
  have hind : iIndepFun X (cubeM N) :=
    iIndepFun_rows (fun _ v => clamp01 (v i)) fun _ => clamp01_measurable.comp (measurable_pi_apply i)
  have hmeas : ∀ r, AEMeasurable (X r) (cubeM N) := fun r =>
    (clamp01_measurable.comp ((measurable_pi_apply i).comp (measurable_pi_apply r))).aemeasurable
  have hb : ∀ r ∈ S, ∀ᵐ w ∂(cubeM N), X r w ∈ Set.Icc 0 ((fun _ => (1 : ℝ)) r) := fun r _ =>
    ae_of_all _ fun w => ⟨clamp01_nonneg _, clamp01_le_one _⟩
  have h := hoeffding_abs S hind hmeas hb hε
  have hmean : ∀ r, (cubeM N)[X r] = 1 / 2 := fun r => frB_integral_clamp_row r i
  simp only [hmean] at h
  have hc : ∑ r ∈ S, ((fun _ => (1 : ℝ)) r) ^ 2 = S.card := by simp
  rw [hc] at h
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal h

lemma frB_fe1_one (t : State N) (A : Finset (Fin N)) (i : Fin N) (F : Finset (State N))
    (hN : 1 ≤ N) :
    cubeM N {w | 2 * Real.sqrt ((N : ℝ) * 2 ^ (N - A.card)) <
        |∑ r ∈ (agree A t).filter (fun r => r ∉ F), (clamp01 (w r i) - 1 / 2)|} ≤
      ENNReal.ofReal (2 * Real.exp (-(8 * (N : ℝ)))) := by
  set S := (agree A t).filter (fun r => r ∉ F) with hS
  set ε := 2 * Real.sqrt ((N : ℝ) * 2 ^ (N - A.card)) with hε
  have hε0 : 0 ≤ ε := by positivity
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · have he : {w : Param N | ε < |∑ r ∈ S, (clamp01 (w r i) - 1 / 2)|} = ∅ := by
      ext w; simp only [card_eq_zero.1 h0, sum_empty, abs_zero, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false, not_lt]; exact hε0
    rw [he, measure_empty]; exact bot_le
  · have hsub : {w : Param N | ε < |∑ r ∈ S, (clamp01 (w r i) - 1 / 2)|} ⊆
        {w | ε ≤ |∑ r ∈ S, (clamp01 (w r i) - 1 / 2)|} := fun w hw =>
      show ε ≤ |∑ r ∈ S, (clamp01 (w r i) - 1 / 2)| from le_of_lt hw
    refine (measure_mono hsub).trans ((frB_hoeff S i hε0).trans ?_)
    apply ENNReal.ofReal_le_ofReal
    gcongr
    have hSc : (S.card : ℝ) ≤ 2 ^ (N - A.card) := by
      have : S.card ≤ (agree A t).card := card_filter_le _ _
      rw [card_agree] at this; exact_mod_cast this
    have hSp : (0 : ℝ) < S.card := by exact_mod_cast hpos
    have hε2 : ε ^ 2 = 4 * ((N : ℝ) * 2 ^ (N - A.card)) := by
      rw [hε, mul_pow, Real.sq_sqrt (by positivity)]; norm_num
    rw [hε2, div_le_iff₀ hSp]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith

/-- **FE1**: failure `≤ N 4^N · 2 e^{-8N}`. -/
theorem freshFE1 : FreshFieldProb FE1X (1 / 180) := by
  filter_upwards [eventually_ge_atTop 1] with N hN s r0 f
  set E : State N × Finset (Fin N) × Fin N → Set (Param N) := fun p =>
    {w | 2 * Real.sqrt ((N : ℝ) * 2 ^ (N - p.2.1.card)) <
      |∑ r ∈ (agree p.2.1 p.1).filter (fun r => r ∉ sensRows s r0), (clamp01 (w r p.2.2) - 1 / 2)|}
    with hE
  refine (frA_transfer (sensRows s r0) f (FE1X N s r0) (B := ⋃ p, E p) fun w hw => ?_).trans ?_
  · simp only [FE1X, not_forall, not_le, exists_prop] at hw
    obtain ⟨t, A, _, i, hi⟩ := hw
    refine Set.mem_iUnion.2 ⟨(t, A, i), ?_⟩
    simp only [hE, Set.mem_ofPred_eq]
    have : ∑ r ∈ (agree A t).filter (fun r => r ∉ sensRows s r0),
        (clamp01 (glueRows (sensRows s r0) f (restrOut (sensRows s r0) w) r i) - 1 / 2) =
        ∑ r ∈ (agree A t).filter (fun r => r ∉ sensRows s r0), (clamp01 (w r i) - 1 / 2) :=
      sum_congr rfl fun r hr => by rw [frA_glue_fresh _ f w (mem_filter.1 hr).2]
    rwa [this] at hi
  · refine (cubeM_iUnion_le E fun p => frB_fe1_one p.1 p.2.1 p.2.2 _ hN).trans ?_
    apply ENNReal.ofReal_le_ofReal
    simp only [Fintype.card_prod, frB_card_state, Fintype.card_finset, Fintype.card_fin]
    push_cast
    have h1 := frB_two_pow_le N
    have h2 := frB_nat_le_exp N
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have he2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    calc (2 : ℝ) ^ N * (2 ^ N * N) * (2 * Real.exp (-(8 * N)))
        ≤ Real.exp (7 / 10 * N) * (Real.exp (7 / 10 * N) * Real.exp N) *
            (Real.exp 1 * Real.exp (-(8 * N))) := by gcongr
      _ = Real.exp (1 - 56 / 10 * N) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-(1 / 180 * N)) := Real.exp_le_exp.2 (by linarith)

/-! ### FE2 -/

lemma frB_card_ball (c : State N) (ρ : ℕ) : (ballR c ρ).card ≤ (N + 1) ^ ρ := by
  have h := card_agree_ball_le (∅ : Finset (Fin N)) c c ρ
  have e : (agree (∅ : Finset (Fin N)) c).filter (fun r => ham c r ≤ ρ) = ballR c ρ := by
    ext r; simp [ballR, mem_agree]
  rw [e] at h; simpa using h

/-- **FE2**: failure `≤ 2(N+1)^4 (N+1)^J e^{-N/165}`. -/
theorem freshFE2 : FreshFieldProb FE2X (1 / 180) := by
  filter_upwards [eventually_ge_atTop 1, frA_ev_logsq 1 20 (δ := 1 / 1980) (by norm_num)] with
    N hN hev s r0 f
  set R : Finset (State N) := (sensRows s r0).biUnion fun r' => ballR r' (JC N) with hR
  refine (frA_transfer (sensRows s r0) f (FE2X N s r0)
    (B := ⋃ r ∈ R, {w | w r ∈ excBad N}) fun w hw => ?_).trans ?_
  · simp only [FE2X, not_forall, not_le, exists_prop] at hw
    obtain ⟨r, hr, ⟨r', hr', hham⟩, hexc⟩ := hw
    refine Set.mem_biUnion (x := r) (Finset.mem_coe.2 ?_) ?_
    · rw [hR, mem_biUnion]
      exact ⟨r', hr', by simp only [ballR, mem_filter, mem_univ, true_and]; rw [ham_comm]; exact hham⟩
    · simp only [Set.mem_ofPred_eq, excBad]
      have : ∀ i, glueRows (sensRows s r0) f (restrOut (sensRows s r0) w) r i = w r i := fun i => by
        rw [frA_glue_fresh _ f w hr]
      simp only [this] at hexc
      exact hexc
  · refine (measure_biUnion_finset_le R _).trans ?_
    have hrow : ∀ r ∈ R, cubeM N {w | w r ∈ excBad N} ≤
        ENNReal.ofReal (Real.exp (-((N : ℝ) / 165))) := fun r _ =>
      (frB_cubeM_row r (measurableSet_excBad N)).le.trans (rowM_excBad_le N)
    refine (sum_le_sum hrow).trans ?_
    rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hRc : (R.card : ℝ) ≤ 2 * ((N : ℝ) + 1) ^ (JC N + 4) := by
      have h1 : R.card ≤ ∑ r' ∈ sensRows s r0, (ballR r' (JC N)).card := card_biUnion_le
      have h2 : ∑ r' ∈ sensRows s r0, (ballR r' (JC N)).card ≤
          (sensRows s r0).card * (N + 1) ^ JC N := by
        rw [← smul_eq_mul, ← sum_const]; exact sum_le_sum fun r' _ => frB_card_ball r' _
      have h3 := card_sensRows_le s r0
      have h4 : R.card ≤ 2 * (N + 1) ^ 4 * (N + 1) ^ JC N :=
        h1.trans (h2.trans (Nat.mul_le_mul_right _ h3))
      have h5 : (R.card : ℝ) ≤ 2 * ((N : ℝ) + 1) ^ 4 * ((N : ℝ) + 1) ^ JC N := by exact_mod_cast h4
      rw [pow_add]; linarith
    have hpow := frA_pow_le_exp hN (JC N + 4)
    have hJ := frA_JC_le hN
    have hL := frA_log_nonneg N
    have hJ4 : ((JC N + 4 : ℕ) : ℝ) * (Real.log N + 1) ≤ 20 * (Real.log N + 1) ^ 2 := by
      push_cast; nlinarith
    have he2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    calc (R.card : ℝ) * Real.exp (-((N : ℝ) / 165))
        ≤ 2 * ((N : ℝ) + 1) ^ (JC N + 4) * Real.exp (-((N : ℝ) / 165)) := by gcongr
      _ ≤ Real.exp 1 * Real.exp (20 * (Real.log N + 1) ^ 2) * Real.exp (-((N : ℝ) / 165)) := by
          gcongr; exact hpow.trans (Real.exp_le_exp.2 hJ4)
      _ = Real.exp (1 + 20 * (Real.log N + 1) ^ 2 - (N : ℝ) / 165) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1 <;> ring
      _ ≤ Real.exp (-(1 / 180 * N)) := Real.exp_le_exp.2 (by linarith)

/-! ### FE6 -/

lemma frB_exp_three_halves : Real.exp (3 / 2) ≤ 9 / 2 := by
  have he := Real.exp_one_lt_d9
  have h3 : Real.exp 3 ≤ 81 / 4 := by
    have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    calc Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := pow_le_pow_left₀ h0 he.le 3
      _ ≤ 81 / 4 := by norm_num
  have hsq : Real.exp (3 / 2) ^ 2 = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (3 / 2)]

/-- `b - 1 - log b ≥ 18/25` for `0 < b ≤ 0.22`. -/
lemma frB_rate_ge {b : ℝ} (hb : 0 < b) (hb2 : b ≤ 11 / 50) : 18 / 25 ≤ b - 1 - Real.log b := by
  have hc : Real.log (11 / 50 : ℝ) ≤ -(3 / 2) := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := frB_exp_three_halves
    rw [Real.exp_neg]
    rw [le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    linarith
  have hmono : Real.log b ≤ Real.log (11 / 50) - (11 / 50 - b) := by
    have h1 : Real.log (11 / 50 / b) ≥ 1 - b / (11 / 50) := by
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 11 / 50 / b by positivity)
      rwa [inv_div] at this
    rw [Real.log_div (by norm_num) hb.ne'] at h1
    have h2 : 11 / 50 - b ≤ 1 - b / (11 / 50) := by
      have e : b / (11 / 50) = 50 * b / 11 := by ring
      rw [e]; linarith
    linarith
  linarith

/-- **FE6**: failure `≤ 2^N e^{-N(I_1(b) )}`, `b ≤ 0.22`. -/
theorem freshFE6 : FreshFieldProb FE6X (1 / 180) := by
  filter_upwards [eventually_ge_atTop 1, frA_ev_logsq 20 2 (δ := 1 / 100) (by norm_num)] with
    N hN hev s r0 f
  set x : ℝ := x0 * N + slT N + b1Eta * N with hx
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL := frA_log_nonneg N
  have hslT : slT N ≤ 1 / 100 * N := by
    unfold slT; nlinarith
  have hx0 := x0_lt
  have hx0p := x0_pos
  have hxpos : 0 < x := by
    rw [hx]; unfold slT b1Eta; positivity
  have hxN : x ≤ 11 / 50 * N := by
    rw [hx]; unfold b1Eta
    nlinarith [mul_le_mul_of_nonneg_right hx0.le (Nat.cast_nonneg N)]
  have hcard : ((univ : Finset (Fin N)).card : ℝ) = N := by simp
  refine (frA_transfer (sensRows s r0) f (FE6X N s r0)
    (B := {w | ∃ r ∈ freshRows s r0, ∑ i ∈ (univ : Finset (Fin N)),
      -Real.log (clamp01 (w r i)) ≤ x}) fun w hw => ?_).trans ?_
  · simp only [FE6X, not_forall, not_lt, exists_prop] at hw
    obtain ⟨r, hr, hle⟩ := hw
    refine ⟨r, by simp [freshRows, hr], ?_⟩
    have : XW (glueRows (sensRows s r0) f (restrOut (sensRows s r0) w)) r = XW w r := by
      unfold XW; rw [frA_glue_fresh _ f w hr]
    rw [this] at hle; exact hle
  · refine (cubeM_rows_negLog_tail (freshRows s r0) univ hxpos (by rw [hcard]; linarith)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    rw [hcard]
    have hb : 0 < x / N := div_pos hxpos (by linarith)
    have hb2 : x / N ≤ 11 / 50 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hrate := frB_rate_ge hb hb2
    have hfc : ((freshRows s r0).card : ℝ) ≤ 2 ^ N := by
      have : (freshRows s r0).card ≤ 2 ^ N := (card_filter_le _ _).trans (by simp)
      exact_mod_cast this
    have h2 := frB_two_pow_le N
    have hl2 : Real.log 2 < 6932 / 10000 := by have := Real.log_two_lt_d9; linarith
    have h2' : (2 : ℝ) ^ N ≤ Real.exp (6932 / 10000 * N) := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ N), Real.log_pow]
      exact Real.exp_le_exp.2 (by nlinarith)
    calc ((freshRows s r0).card : ℝ) * Real.exp (-((N : ℝ) * (x / N - 1 - Real.log (x / N))))
        ≤ Real.exp (6932 / 10000 * N) * Real.exp (-((N : ℝ) * (18 / 25))) := by
          gcongr
          all_goals first | exact hfc.trans h2' | nlinarith
      _ = Real.exp (-(268 / 10000 * N)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-(1 / 180 * N)) := Real.exp_le_exp.2 (by nlinarith)

end Census
end IIT

#print axioms IIT.Census.freshFE1
#print axioms IIT.Census.freshFE2
#print axioms IIT.Census.freshFE6
