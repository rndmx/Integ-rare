/-
Census, B1, W14 work package WP5 (part 1): retention (W5 Lemma C3a, W9 5.3) and the Markov bound over the
family (W5 Lemma C3b), at the constants of `B1CntDefs3.lean`.

* `ret_perK`: for every `f` and every `|K| = dX N`, the fresh rows fail `RetK` with probability `≤ e^{-N/20}`
  (`B1Chernoff.pi_rows_negLog_tail`, threshold `x = x0 N + slT N + 1`, `m = N - dX N`; tangent-line bound
  `log(x/m) ≤ log c + x/(m c) - 1` at `c = 21/100`, exponent `-0.0515 N + O(log N)`);
* `retMarkov_proved : RetMarkovStmt` (`famX3` is fixed by `f`; Markov at `|famX3| pY/4`).

Blueprint: `iit-census/lean/B1-W14-count-lean.md` §10.  No `sorry`.
-/
import IIT.Census.B1CntBasics

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### Real-analysis helpers -/

lemma w5_ev_log_le (c ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, c * Real.log N ≤ ε * N := by
  have hlo := Real.isLittleO_log_id_atTop
  have h1 := hlo.def (c := ε / (|c| + 1)) (by positivity)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h1, eventually_ge_atTop 1] with N hN hN1
  simp only [Real.norm_eq_abs, id] at hN
  have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [abs_of_nonneg hl, abs_of_nonneg hN0] at hN
  have hc : c * Real.log N ≤ |c| * Real.log N := mul_le_mul_of_nonneg_right (le_abs_self c) hl
  have : |c| * Real.log N ≤ |c| * (ε / (|c| + 1) * N) := mul_le_mul_of_nonneg_left hN (abs_nonneg c)
  have h2 : |c| * (ε / (|c| + 1) * N) ≤ ε * N := by
    rw [← mul_assoc, mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg c, mul_nonneg hε.le hN0]
  linarith

/-- `dX N ≤ N` and `30 · dX N ≤ N + 29`. -/
lemma w5_dX_le (hN : 1 ≤ N) : dX N ≤ N ∧ 30 * dX N ≤ N + 29 := by
  unfold dX; constructor <;> omega

/-- `m = N - dX N ≥ (29 N - 29)/30` as reals. -/
lemma w5_m_ge (hN : 1 ≤ N) : (29 * (N : ℝ) - 29) / 30 ≤ ((N - dX N : ℕ) : ℝ) := by
  obtain ⟨h1, h2⟩ := w5_dX_le hN
  rw [Nat.cast_sub h1]
  have : (30 : ℝ) * dX N ≤ N + 29 := by exact_mod_cast h2
  linarith

lemma w5_log_21_le : Real.log ((21 / 100 : ℚ) : ℝ) ≤ ((-156 / 100 : ℚ) : ℝ) :=
  log_le_rat (by norm_num) 12 2 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

/-- **The retention rate** (W5 C13'): `2^N F_m(x) ≤ e^{-N/20}` with `x = x0 N + slT N + 1`. -/
lemma w5_ret_rate : ∀ᶠ N : ℕ in atTop,
    0 < x0 * N + slT N + 1 ∧ x0 * N + slT N + 1 ≤ ((N - dX N : ℕ) : ℝ) ∧
    (2 : ℝ) ^ N * Real.exp (-(((N - dX N : ℕ) : ℝ) *
      ((x0 * N + slT N + 1) / ((N - dX N : ℕ) : ℝ) - 1 -
        Real.log ((x0 * N + slT N + 1) / ((N - dX N : ℕ) : ℝ))))) ≤
      Real.exp (-((N : ℝ) / 20)) := by
  filter_upwards [w5_ev_log_le 8 (1 / 2000) (by norm_num), eventually_ge_atTop 200000]
    with N hlog hN
  have hN1 : 1 ≤ N := by omega
  have hNr : (200000 : ℝ) ≤ N := by exact_mod_cast hN
  set m : ℝ := ((N - dX N : ℕ) : ℝ) with hm
  set x : ℝ := x0 * N + slT N + 1 with hx
  have hmge := w5_m_ge hN1
  rw [← hm] at hmge
  have hx0 := x0_lt
  have hx0p := x0_pos
  have hl0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hxdef : x = x0 * N + 2 * Real.log N + 21 := by rw [hx]; unfold slT; ring
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have hxle : x ≤ 2029 / 10000 * N + 2 * Real.log N + 21 := by
    rw [hxdef]; nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hmpos : 0 < m := by linarith
  have hxm : x ≤ m := by linarith
  refine ⟨hxpos, hxm, ?_⟩
  -- the tangent-line bound for the logarithm at `c = 21/100`
  have hc : Real.log (21 / 100 : ℝ) ≤ -156 / 100 := by
    have := w5_log_21_le; push_cast at this; linarith
  have htan : Real.log (x / m) ≤ Real.log (21 / 100) + x / (m * (21 / 100)) - 1 := by
    have hq : x / m = (21 / 100) * (x / (m * (21 / 100))) := by field_simp
    rw [hq, Real.log_mul (by norm_num) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show 0 < x / (m * (21 / 100)) by positivity)
    linarith
  have hE : -(m * (x / m - 1 - Real.log (x / m))) ≤ -156 / 100 * m + 79 / 21 * x := by
    have h1 : m * Real.log (x / m) ≤ m * (-156 / 100 + x / (m * (21 / 100)) - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hmpos.le
    have h2 : m * (x / (m * (21 / 100))) = 100 / 21 * x := by field_simp
    have h3 : m * (x / m) = x := by field_simp
    nlinarith
  have h2N : (2 : ℝ) ^ N = Real.exp (N * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [h2N, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hl2 := Real.log_two_lt_d9
  have : (N : ℝ) * Real.log 2 ≤ N * 0.6931471808 :=
    mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg N)
  nlinarith

/-! ### Retention per `K` (W5 Lemma C3a) -/

theorem ret_perK : ∀ᶠ N in atTop, ∀ (s r0 : State N) (f : sensRows s r0 → Fin N → ℝ)
    (K : Finset (Fin N)), K.card = dX N →
      rowsOutM (sensRows s r0) {g | ¬ RetK N s r0 K (glueRows (sensRows s r0) f g)} ≤
        ENNReal.ofReal (Real.exp (-((N : ℝ) / 20))) := by
  filter_upwards [w5_ret_rate, eventually_ge_atTop 1] with N hN hN1 s r0 f K hK
  obtain ⟨hxpos, hxm, hrate⟩ := hN
  set M : Finset (Fin N) := univ \ K with hMdef
  have hMc : M.card = N - dX N := by
    rw [hMdef, card_univ_sdiff, Fintype.card_fin, hK]
  set x : ℝ := x0 * N + slT N + 1 with hx
  have hsub : {g : {r // r ∉ sensRows s r0} → Fin N → ℝ | ¬ RetK N s r0 K (glueRows (sensRows s r0) f g)} ⊆
      {V | ∃ r, ∑ i ∈ M, -Real.log (clamp01 (V r i)) ≤ x} := by
    intro g hg
    simp only [Set.mem_ofPred_eq, RetK, not_forall, not_lt] at hg
    obtain ⟨r, hr, hle⟩ := hg
    refine ⟨⟨r, hr⟩, ?_⟩
    unfold XMW at hle
    rw [glueRows_of_not_mem (sensRows s r0) f g hr] at hle
    exact hle
  have hxM : x ≤ (M.card : ℝ) := by rw [hMc]; exact hxm
  have ht := pi_rows_negLog_tail (R := {r // r ∉ sensRows s r0}) M hxpos hxM
  refine (measure_mono (μ := rowsOutM (sensRows s r0)) hsub).trans ?_
  unfold rowsOutM
  refine ht.trans (ENNReal.ofReal_le_ofReal ?_)
  have hcard : (Fintype.card {r // r ∉ sensRows s r0} : ℝ) ≤ 2 ^ N := by
    have h1 : Fintype.card {r // r ∉ sensRows s r0} ≤ Fintype.card (State N) := Fintype.card_subtype_le _
    have h2 : Fintype.card (State N) = 2 ^ N := by simp
    exact_mod_cast h1.trans h2.le
  rw [hMc]
  exact (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le).trans hrate

/-! ### Markov over the family (W5 Lemma C3b) -/

lemma w5_markov_rate : ∀ᶠ N : ℕ in atTop,
    0 < pY N ∧ 4 * Real.exp (-((N : ℝ) / 20)) / pY N ≤ Real.exp (-((N : ℝ) / 40)) := by
  filter_upwards [eventually_ge_atTop 3, w5_ev_log_le 1 1 one_pos,
    w5_ev_log_le 1 (1 / 80) (by norm_num), eventually_ge_atTop 2000000] with N hN3 hlog1 hlog hN
  have hNr : (2000000 : ℝ) ≤ N := by exact_mod_cast hN
  have hlpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hpY : 0 < pY N := by unfold pY; positivity
  refine ⟨hpY, ?_⟩
  unfold pY
  rw [div_div_eq_mul_div, div_one]
  -- `4000 log N e^{-N/20} ≤ e^{-N/40}` ⟸ `log(4000 log N) ≤ N/40`
  have hlogle : Real.log (4 * (1000 * Real.log N)) ≤ (N : ℝ) / 40 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) hlpos.ne']
    have h1 : Real.log (Real.log N) ≤ Real.log N :=
      (Real.log_le_sub_one_of_pos hlpos).trans (by linarith)
    have h4 : Real.log (4 : ℝ) ≤ 4 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    have h1000 : Real.log (1000 : ℝ) ≤ 1000 :=
      (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    linarith
  have hpos : 0 < 4 * (1000 * Real.log N) := by positivity
  calc 4 * Real.exp (-((N : ℝ) / 20)) * (1000 * Real.log N)
      = Real.exp (Real.log (4 * (1000 * Real.log N))) * Real.exp (-((N : ℝ) / 20)) := by
        rw [Real.exp_log hpos]; ring
    _ = Real.exp (Real.log (4 * (1000 * Real.log N)) - (N : ℝ) / 20) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-((N : ℝ) / 40)) := Real.exp_le_exp.2 (by linarith)

theorem retMarkov_proved : RetMarkovStmt := by
  filter_upwards [ret_perK, w5_markov_rate] with N hR hrate s r0 x σ f _hf
  obtain ⟨hpY, hrate⟩ := hrate
  set 𝒦 := famX3 N s r0 x σ (b1Ext f) with h𝒦
  set S : Finset (Fin N) → Set ({r // r ∉ sensRows s r0} → Fin N → ℝ) :=
    fun K => {g | ¬ RetK N s r0 K (glueRows (sensRows s r0) f g)} with hS
  have hSm : ∀ K, MeasurableSet (S K) := fun K =>
    (measurable_glueRows_right (sensRows s r0) f) (measurableSet_RetK s r0 K).compl
  set c : ℝ := (𝒦.card : ℝ) * pY N / 4 with hc
  -- the count as a sum of indicators
  set Φ : ({r // r ∉ sensRows s r0} → Fin N → ℝ) → ENNReal :=
    fun g => ∑ K ∈ 𝒦, (S K).indicator (fun _ => (1 : ENNReal)) g with hΦ
  have hΦeq : ∀ g, Φ g = ((RFCnt N s r0 x σ (glueRows (sensRows s r0) f g) : ℕ) : ENNReal) := by
    intro g
    unfold RFCnt
    rw [famX3_glue f g, ← h𝒦, Finset.card_filter]
    push_cast
    refine sum_congr rfl fun K _ => ?_
    by_cases h : ¬ RetK N s r0 K (glueRows (sensRows s r0) f g)
    · rw [Set.indicator_of_mem (show g ∈ S K from h), if_pos h]
    · rw [Set.indicator_of_notMem (show g ∉ S K from h), if_neg h]
  have hsub : {g | glueRows (sensRows s r0) f g ∈ RetBad N s r0 x σ} ⊆ {g | ENNReal.ofReal c ≤ Φ g} := by
    intro g hg
    simp only [Set.mem_ofPred_eq, RetBad] at hg ⊢
    rw [famX3_glue f g, ← h𝒦] at hg
    rw [hΦeq g, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hg.le
  have hint : ∫⁻ g, Φ g ∂rowsOutM (sensRows s r0) ≤ (𝒦.card : ENNReal) * ENNReal.ofReal (Real.exp (-((N : ℝ) / 20))) := by
    rw [lintegral_finsetSum _ fun K _ => (measurable_const.indicator (hSm K))]
    calc ∑ K ∈ 𝒦, ∫⁻ g, (S K).indicator (fun _ => (1 : ENNReal)) g ∂rowsOutM (sensRows s r0)
        = ∑ K ∈ 𝒦, rowsOutM (sensRows s r0) (S K) := by
          refine sum_congr rfl fun K _ => ?_
          rw [lintegral_indicator_const (hSm K), one_mul]
      _ ≤ ∑ _K ∈ 𝒦, ENNReal.ofReal (Real.exp (-((N : ℝ) / 20))) :=
          sum_le_sum fun K hK => hR s r0 f K (famX3_card hK)
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  by_cases h0 : 𝒦.card = 0
  · -- empty family: `RetBad` is empty
    have : {g | glueRows (sensRows s r0) f g ∈ RetBad N s r0 x σ} = ∅ := by
      ext g
      simp only [Set.mem_ofPred_eq, RetBad, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [famX3_glue f g, ← h𝒦, h0]
      have : RFCnt N s r0 x σ (glueRows (sensRows s r0) f g) = 0 := by
        unfold RFCnt; rw [famX3_glue f g, ← h𝒦, card_eq_zero.1 h0]; simp
      rw [this]; simp
    rw [this, measure_empty]; exact bot_le
  have hcpos : 0 < c := by
    rw [hc]; have : (0 : ℝ) < 𝒦.card := by exact_mod_cast Nat.pos_of_ne_zero h0
    positivity
  have hΦm : Measurable Φ := by
    rw [hΦ]; exact Finset.measurable_sum _ fun K _ => measurable_const.indicator (hSm K)
  have hmk := mul_meas_ge_le_lintegral₀ (μ := rowsOutM (sensRows s r0)) hΦm.aemeasurable
    (ENNReal.ofReal c)
  have hc0 : ENNReal.ofReal c ≠ 0 := by rw [ENNReal.ofReal_ne_zero_iff]; exact hcpos
  refine (measure_mono (μ := rowsOutM (sensRows s r0)) hsub).trans ?_
  rw [← ENNReal.mul_le_mul_iff_right hc0 ENNReal.ofReal_ne_top]
  refine (hmk.trans hint).trans ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul hcpos.le]
  refine ENNReal.ofReal_le_ofReal ?_
  have hK0 : (0 : ℝ) < 𝒦.card := by exact_mod_cast Nat.pos_of_ne_zero h0
  have h4 : (𝒦.card : ℝ) * Real.exp (-((N : ℝ) / 20)) =
      c * (4 * Real.exp (-((N : ℝ) / 20)) / pY N) := by
    rw [hc]; field_simp
  rw [h4]
  exact mul_le_mul_of_nonneg_left hrate hcpos.le

end Census
end IIT

#print axioms IIT.Census.ret_perK
#print axioms IIT.Census.retMarkov_proved
