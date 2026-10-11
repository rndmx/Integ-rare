/-
Census, B1: **`NewLeaf3Stmt` and `NewX3MeasStmt`, PROVED** (the new rate leaf of `GoodX3`, B1GoodX3).

`GoodX3Fail` lies in the union of three per-field failure events jointly with the regime event (for far `r0`):
* `lowFew` (`joint_lowFew`): cause side, only cell 0 meets the low window (`lc_cause_joint`, rate 1.012);
  effect side, weight `e^5` on the `r0` low window of length `≤ 2 deltaU` (`le_eff_cell`, rate `rsR0 + 0.005`);
* `pairLow` with a non-low witness (`joint_pairLow3`, rate 1.0192);
* `x5e` at `|K'| ≤ 2` (`joint_x5e2`, rate `rsR0 + 1/32`).
Each is `≤ e^{-RJ N}/2^N` per `(r0, x, σ)`; the sum over `(r0, x, σ)` is `≤ 6 N e^{-RJ N} ≤ e^{-RbadX N}`.
-/
import IIT.Census.B1NewLeaf3LowE
import IIT.Census.B1NewLeaf3Meas
import IIT.Census.B1NewLeafX5e

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- The `lowFew` field with an explicit anchor row. -/
def P0LowFew (N : ℕ) (_s : State N) : State N → Param N → Fin N → XSide → Prop := fun r0 w _ _ =>
  1000 * (lowU N w r0).card ≤ N

/-- `e^{-N/200} ≤ deltaU N` eventually. -/
lemma nl3_eps_delta : ∀ᶠ N : ℕ in atTop, Real.exp (-((N : ℝ) / 200)) ≤ deltaU N := by
  filter_upwards [eventually_ge_atTop 160000] with N hN
  have hN' : (160000 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (N : ℝ) + 1 ≤ Real.exp ((N : ℝ) / 200) := by
    have h2 := Real.add_one_le_exp ((N : ℝ) / 400)
    have e : Real.exp ((N : ℝ) / 200) = Real.exp ((N : ℝ) / 400) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [e]
    have h3 : 0 ≤ (N : ℝ) / 400 + 1 := by positivity
    calc (N : ℝ) + 1 ≤ ((N : ℝ) / 400 + 1) ^ 2 := by nlinarith
      _ ≤ Real.exp ((N : ℝ) / 400) ^ 2 := pow_le_pow_left₀ h3 (by linarith) 2
  unfold deltaU
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) h1

/-- **Joint bound for `lowFew`, PROVED** (both sides). -/
theorem joint_lowFew : JointBound P0LowFew := by
  have habC := poly_absorb 1 0 (δ := (1012 / 1000 : ℝ) - RJ) (by unfold RJ; norm_num)
  have habE := poly_absorb (61 * Real.exp 1291) 0 (δ := ((rsR0 : ℝ) + 5 / 1000) - RJ)
    (by unfold RJ rsR0; norm_num)
  filter_upwards [habC, habE, nl3_eps, nl3_eps_delta, eventually_ge_atTop 15] with N habC habE hε hεδ hN
    s r0 x σ hfar
  have hsl := rs_slack_le N
  have hslT : 0 ≤ slT N := by
    unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    linarith
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  cases σ with
  | cause =>
    have hsub : {w : Param N | RegEvX N s r0 x .cause w ∧ ¬ P0LowFew N s r0 w x .cause} ⊆
        {w | RegEvX N s r0 x .cause w ∧ N < 1000 * (lowU N w r0).card} := by
      rintro w ⟨h1, h2⟩; exact ⟨h1, by simp only [P0LowFew, not_le] at h2; exact h2⟩
    refine (measure_mono hsub).trans ((lc_cause_joint hN hε s r0 x hfar).trans (ENNReal.ofReal_le_ofReal ?_))
    set δ : ℝ := (1012 / 1000 : ℝ) - RJ with hδ
    have hk : Real.exp (14 * slT N + 17 * (8 + slV N)) ≤ Real.exp (δ * N) := by
      refine le_trans ?_ habC
      simp only [pow_zero, mul_one, one_mul]
      exact Real.exp_le_exp.2 (by linarith)
    have e : Real.exp (-((1012 / 1000 : ℝ) * N)) = Real.exp (-(δ * N)) * Real.exp (-(RJ * N)) := by
      rw [← Real.exp_add, hδ]; ring_nf
    rw [e, div_le_div_iff_of_pos_right h2N]
    have hy : Real.exp (δ * N) * Real.exp (-(δ * N)) = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp (-(δ * N)) * Real.exp (-(RJ * N)) * Real.exp (14 * slT N + 17 * (8 + slV N))
        ≤ Real.exp (-(δ * N)) * Real.exp (-(RJ * N)) * Real.exp (δ * N) := by gcongr
      _ = Real.exp (-(RJ * N)) := by rw [mul_comm, ← mul_assoc, hy, one_mul]
  | effect =>
    have hN2 : 2 ≤ N := by omega
    have hδ : deltaU N < 1 / 2 := by
      unfold deltaU; rw [div_lt_iff₀ (by positivity)]; have : (15 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    obtain ⟨x', hx'⟩ := fs_dummy hN2 x
    set SB := Real.exp (-(((rsR0 : ℝ) + 5 / 1000) * N)) *
      Real.exp (19 * slT N + 17 * (8 + slV N) + 1300) / 2 ^ N with hSB
    have hSB0 : 0 ≤ SB := by positivity
    have hsub : {w : Param N | RegEvX N s r0 x .effect w ∧ ¬ P0LowFew N s r0 w x .effect} ⊆
        ⋃ c ∈ cellsX .effect, ({w | CellEvX N s r0 x .effect c w} ∩ lowFail N r0) := by
      rintro w ⟨⟨c, hc, hcw⟩, hn⟩
      simp only [P0LowFew, not_le] at hn
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
      exact ⟨c, hc, hcw, hn⟩
    refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
    have h0 := tf_far_ne2 (by omega) hfar
    calc ∑ c ∈ cellsX .effect, cubeM N ({w | CellEvX N s r0 x .effect c w} ∩ lowFail N r0)
        ≤ ∑ _c ∈ cellsX .effect, ENNReal.ofReal SB := sum_le_sum fun c hc =>
          le_eff_cell hN2 hδ s r0 x x' hx' (List.mem_toFinset.1 hc) h0 (tf_far_ne0 (by omega) hfar x)
            (tf_far_ne0 (by omega) hfar x') hεδ
      _ ≤ (61 : ENNReal) * ENNReal.ofReal SB := by
          rw [sum_const, nsmul_eq_mul]; gcongr; exact_mod_cast tf_cells_card .effect
      _ = ENNReal.ofReal (61 * SB) := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          set δ : ℝ := ((rsR0 : ℝ) + 5 / 1000) - RJ with hδd
          have hk : 61 * Real.exp 1291 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) ≤ Real.exp (δ * N) := by
            refine le_trans ?_ habE
            simp only [pow_zero, mul_one]
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hsl) (by positivity)
          have e : 61 * SB = (61 * Real.exp 1291 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9)) *
              (Real.exp (-(δ * N)) * Real.exp (-(RJ * N))) / 2 ^ N := by
            rw [hSB, show Real.exp (19 * slT N + 17 * (8 + slV N) + 1300) =
              Real.exp 1291 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) by rw [← Real.exp_add]; ring_nf,
              show Real.exp (-(((rsR0 : ℝ) + 5 / 1000) * N)) = Real.exp (-(δ * N)) * Real.exp (-(RJ * N)) by
                rw [← Real.exp_add, hδd]; ring_nf]
            ring
          rw [e, div_le_div_iff_of_pos_right h2N]
          have hy : Real.exp (δ * N) * Real.exp (-(δ * N)) = 1 := by rw [← Real.exp_add]; simp
          calc (61 * Real.exp 1291 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9)) *
                (Real.exp (-(δ * N)) * Real.exp (-(RJ * N)))
              ≤ Real.exp (δ * N) * (Real.exp (-(δ * N)) * Real.exp (-(RJ * N))) := by gcongr
            _ = Real.exp (-(RJ * N)) := by rw [← mul_assoc, hy, one_mul]

/-- **`GoodX3Fail` lies in the three per-field failure events** (for far `r0`). -/
theorem goodX3Fail_sub (s r0 : State N) (x : Fin N) (σ : XSide) :
    {w : Param N | restrIn (sensRows s r0) w ∈ GoodX3Fail N s r0 x σ} ⊆
      {w | N ≤ 3 * ham r0 s ∧ RegEvX N s r0 x σ w ∧ ¬ P0LowFew N s r0 w x σ} ∪
        {w | N ≤ 3 * ham r0 s ∧ RegEvX N s r0 x σ w ∧ ¬ P0PairLow3 N s r0 w x σ} ∪
          {w | N ≤ 3 * ham r0 s ∧ RegEvX N s r0 x σ w ∧ ¬ P0X5eExt2 N s r0 w x σ} := by
  intro w hw
  obtain ⟨hg, hn⟩ := hw
  have hE : ∀ r ∈ sensRows s r0, b1Ext (restrIn (sensRows s r0) w) r = w r := by
    intro r hr; rw [← b1Restr_eq_restrIn]; exact b1_Ext_Restr s r0 w r hr
  have hg' : B1FGoodX N s r0 x σ w := (B1FGoodX.congr hE).2 hg
  have h0 := hE r0 (nl_r0_mem s r0)
  have h1 := hE _ (nl_r1_mem s r0 x)
  have hlow : lowU N (b1Ext (restrIn (sensRows s r0) w)) r0 = lowU N w r0 := by
    unfold lowU; rw [h0]
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_and, not_not] at hcon
  obtain ⟨⟨hA, hB⟩, hC⟩ := hcon
  have fA := hA hg'.far hg'.regEv
  have fB := hB hg'.far hg'.regEv
  have fC := hC hg'.far hg'.regEv
  apply hn
  refine ⟨?_, fun hσ => ?_, fun hσ => fC hσ⟩
  · rw [hlow]; exact fA
  · obtain ⟨j, hj, hb, hle⟩ := fB hσ
    exact ⟨j, hj, by rw [h0]; exact hb, by rw [h0, h1]; exact hle⟩

/-- **`NewLeaf3Stmt`, PROVED.** -/
theorem newLeaf3_proved : NewLeaf3Stmt := by
  filter_upwards [joint_lowFew, joint_pairLow3, joint_x5e2, nl_absorb] with N h1 h2 h3 hab s
  set E : ℝ := Real.exp (-(RJ * N)) / 2 ^ N with hE
  have hE0 : 0 ≤ E := by positivity
  have hpiece : ∀ (r0 : State N) (x : Fin N) (σ : XSide)
      (P : ∀ N, State N → State N → Param N → Fin N → XSide → Prop),
      (∀ (s r0 : State N) (x : Fin N) (σ : XSide), N ≤ 3 * ham r0 s →
        cubeM N {w | RegEvX N s r0 x σ w ∧ ¬ P N s r0 w x σ} ≤ ENNReal.ofReal (Real.exp (-(RJ * N)) / 2 ^ N)) →
      cubeM N {w | N ≤ 3 * ham r0 s ∧ RegEvX N s r0 x σ w ∧ ¬ P N s r0 w x σ} ≤ ENNReal.ofReal E := by
    intro r0 x σ P hP
    by_cases hf : N ≤ 3 * ham r0 s
    · exact le_trans (measure_mono fun w hw => hw.2) (hP s r0 x σ hf)
    · have : {w | N ≤ 3 * ham r0 s ∧ RegEvX N s r0 x σ w ∧ ¬ P N s r0 w x σ} = ∅ :=
        Set.eq_empty_of_forall_notMem fun w hw => hf hw.1
      rw [this, measure_empty]; exact bot_le
  have hterm : ∀ r0 x σ, rowsInM (sensRows s r0) (GoodX3Fail N s r0 x σ) ≤ ENNReal.ofReal (3 * E) := by
    intro r0 x σ
    rw [← cubeM_restrIn_preimage (sensRows s r0)]
    refine (measure_mono (goodX3Fail_sub s r0 x σ)).trans ?_
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add (measure_union_le _ _) le_rfl).trans ?_
    calc _ ≤ ENNReal.ofReal E + ENNReal.ofReal E + ENNReal.ofReal E :=
          add_le_add (add_le_add (hpiece r0 x σ P0LowFew h1) (hpiece r0 x σ P0PairLow3 h2))
            (hpiece r0 x σ P0X5eExt2 h3)
      _ = ENNReal.ofReal (3 * E) := by
          rw [← ENNReal.ofReal_add hE0 hE0, ← ENNReal.ofReal_add (by positivity) hE0]; ring_nf
  calc ∑ r0 : State N, ∑ x : Fin N, ∑ σ : XSide, rowsInM (sensRows s r0) (GoodX3Fail N s r0 x σ)
      ≤ ∑ _r0 : State N, ∑ _x : Fin N, ∑ _σ : XSide, ENNReal.ofReal (3 * E) :=
        sum_le_sum fun r0 _ => sum_le_sum fun x _ => sum_le_sum fun σ _ => hterm r0 x σ
    _ = ENNReal.ofReal (2 ^ N * N * 2 * (3 * E)) := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show Fintype.card XSide = 2 from rfl, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        rw [ENNReal.ofReal_mul (p := (2 : ℝ) ^ N * N * 2) (by positivity),
          ENNReal.ofReal_mul (p := (2 : ℝ) ^ N * N) (by positivity),
          ENNReal.ofReal_mul (p := (2 : ℝ) ^ N) (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_natCast]
        simp; ring
    _ ≤ ENNReal.ofReal (Real.exp (-(RbadX * N))) := by
        apply ENNReal.ofReal_le_ofReal
        have e1 : 2 ^ N * N * 2 * (3 * E) = 6 * N * Real.exp (-(RJ * N)) := by
          rw [hE]; field_simp; ring
        rw [e1]; exact hab

/-- **`B1PhiGoal` modulo the count over `GoodX3`.** -/
theorem b1PhiGoal_of_countX3 (hcnt : CountX3Stmt) : B1PhiGoal :=
  b1PhiGoal_of_X3 newX3Meas_proved newLeaf3_proved hcnt

end Census
end IIT

#print axioms IIT.Census.newX3Meas_proved
#print axioms IIT.Census.joint_lowFew
#print axioms IIT.Census.joint_pairLow3
#print axioms IIT.Census.joint_x5e2
#print axioms IIT.Census.newLeaf3_proved
#print axioms IIT.Census.b1PhiGoal_of_countX3
