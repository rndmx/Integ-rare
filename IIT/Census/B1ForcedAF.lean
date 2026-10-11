/-
Census, B1 forced leaves, part AF: field leaves `far` (leaf 8) and `retR1` (leaf 10).

* leaf 10 (`retR1`, W7 X3): PROVED (`leafA10`). The F-data in `RegEvX(cause)` satisfy T and L; together
  with `D_total < N/400` the three-row Chernoff `fa_r1_core` (multipliers 11, 3, 4) gives rate
  `ln(80/3) - 11 x0 - 1/100 ≥ 1.041 > RfF`; the row coincidences `s ∈ {r0, r0^x}` use `fa_r1_core_self`
  (rate `ln 40 - 11 x0 - 1/100 ≥ 1.44`, no union over `r0`).
* leaf 8 (`far`): PROVED modulo the row-coincidence sub-leaf `FarSelfLeaf` (`leafA8_of_self`).
  Generic part: certified `RegEvX` bounds (`regEvX_cause_prob`, `regEvX_effect_prob`) times the Hamming
  count `#{ham(r0,s) ≤ N/3} ≤ 2^{N/3}(3/2)^N`: rate `≥ 1.0072 + ln 2 - ln(3/2) - (ln 2)/3 ≥ 1.063`.
-/
import IIT.Census.B1ForcedA
import IIT.Census.B1ForcedARet1
import IIT.Census.B1ForcedAHam
import IIT.Census.B1GoodFXRate

namespace IIT
namespace Census

open MeasureTheory Filter Finset Topology

variable {N : ℕ}

/-! ### Asymptotic helpers -/

lemma fa_absorb {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) (C : ℝ) (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ k * q ^ N ≤ 1 / 2 := by
  have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one k (by rwa [abs_of_nonneg hq0])
  have hC : (0 : ℝ) < 1 / (2 * (|C| + 1)) := by positivity
  filter_upwards [h.eventually (gt_mem_nhds hC)] with N hN
  have h0 : 0 ≤ (N : ℝ) ^ k * q ^ N := by positivity
  have h1 : C * (N : ℝ) ^ k * q ^ N ≤ (|C| + 1) * ((N : ℝ) ^ k * q ^ N) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right ((le_abs_self C).trans (by linarith)) h0
  have h2 : (|C| + 1) * ((N : ℝ) ^ k * q ^ N) ≤ (|C| + 1) * (1 / (2 * (|C| + 1))) :=
    mul_le_mul_of_nonneg_left hN.le (by positivity)
  have h3 : (|C| + 1) * (1 / (2 * (|C| + 1))) = 1 / 2 := by field_simp
  linarith

lemma fa_exp_slT (c : ℝ) (hN : 1 ≤ N) :
    Real.exp (c * slT N) = Real.exp (20 * c) * Real.exp ((2 * c) * Real.log N) := by
  rw [← Real.exp_add]; unfold slT; congr 1; ring

lemma fa_exp_nat_log (k : ℕ) (hN : 1 ≤ N) : Real.exp ((k : ℝ) * Real.log N) = (N : ℝ) ^ k := by
  rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hN)]

lemma fa_exp_mul_nat (c : ℝ) (N : ℕ) : Real.exp ((N : ℝ) * c) = Real.exp c ^ N := by
  rw [← Real.exp_nat_mul]

/-- `e^{11 x0 + 1/100 + RfF} ≤ 26`. -/
lemma fa_exp_key : Real.exp (11 * x0 + 1 / 100 + RfF) ≤ 26 := by
  have hx := x0_lt
  have h1 : Real.exp (11 * x0 + 1 / 100 + RfF) ≤ Real.exp ((32524 / 10000 : ℚ) : ℝ) := by
    apply Real.exp_le_exp.2; unfold RfF; push_cast; linarith
  have h2 : Real.exp ((32524 / 10000 : ℚ) : ℝ) ≤ ((26 : ℚ) : ℝ) :=
    exp_le_rat 12 4 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have : ((26 : ℚ) : ℝ) = 26 := by norm_num
  linarith

/-! ### leaf 10 -/

/-- the generic and self bounds -/
noncomputable def faG10 (N : ℕ) : ℝ :=
  Real.exp (11 * (x0 * N + slT N) + 3 * slT N + 4 * ((N : ℝ) / 400)) * (3 / 160) ^ (N - 1)
noncomputable def faS10 (N : ℕ) : ℝ :=
  Real.exp (11 * (x0 * N + slT N) + 4 * ((N : ℝ) / 400)) * (1 / 40) ^ (N - 1)

lemma fa_G10_nonneg (N : ℕ) : 0 ≤ faG10 N := by unfold faG10; positivity
lemma fa_S10_nonneg (N : ℕ) : 0 ≤ faS10 N := by unfold faS10; positivity

lemma fa_arith10 : ∀ᶠ N : ℕ in atTop,
    (N : ℝ) * 2 ^ N * faG10 N + 2 * N * faS10 N ≤ Real.exp (-(RfF * N)) := by
  have hk := fa_exp_key
  set K := Real.exp (11 * x0 + 1 / 100 + RfF) with hK
  have hK0 : 0 < K := Real.exp_pos _
  filter_upwards [fa_absorb (q := 3 / 80 * K) (by positivity) (by linarith)
      (160 / 3 * Real.exp 280) 29,
    fa_absorb (q := K / 40) (by positivity) (by linarith) (80 * Real.exp 220) 23,
    eventually_ge_atTop 1] with N h1 h2 hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set E := Real.exp (-(RfF * N)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- e^{N(11 x0 + 1/100)} = K^N E
  have hKN : Real.exp ((N : ℝ) * (11 * x0 + 1 / 100)) = K ^ N * E := by
    rw [hK, ← fa_exp_mul_nat, hE, ← Real.exp_add]; congr 1; ring
  have hp1 : ∀ a : ℝ, a ^ N = a ^ (N - 1) * a := fun a => by
    rw [← pow_succ]; congr 1; omega
  -- generic part
  have hG : (N : ℝ) * 2 ^ N * faG10 N = 160 / 3 * Real.exp 280 * (N : ℝ) ^ 29 * (3 / 80 * K) ^ N * E := by
    unfold faG10
    have e1 : 11 * (x0 * N + slT N) + 3 * slT N + 4 * ((N : ℝ) / 400) =
        280 + ((28 : ℕ) : ℝ) * Real.log N + (N : ℝ) * (11 * x0 + 1 / 100) := by
      unfold slT; push_cast; ring
    rw [e1, Real.exp_add, Real.exp_add, fa_exp_nat_log 28 hN, hKN, mul_pow]
    have h3 : (3 / 80 : ℝ) ^ N = 2 ^ N * (3 / 160) ^ N := by rw [← mul_pow]; norm_num
    rw [h3, hp1 (3 / 160)]
    ring
  have hS : 2 * (N : ℝ) * faS10 N = 80 * Real.exp 220 * (N : ℝ) ^ 23 * (K / 40) ^ N * E := by
    unfold faS10
    have e1 : 11 * (x0 * N + slT N) + 4 * ((N : ℝ) / 400) =
        220 + ((22 : ℕ) : ℝ) * Real.log N + (N : ℝ) * (11 * x0 + 1 / 100) := by
      unfold slT; push_cast; ring
    rw [e1, Real.exp_add, Real.exp_add, fa_exp_nat_log 22 hN, hKN, div_pow, div_pow, one_pow, hp1 40]
    field_simp
    ring
  rw [hG, hS]
  nlinarith

/-- the per-`(r0, x)` event -/
def faE10 (N : ℕ) (s r0 : State N) (x : Fin N) : Set (Param N) :=
  {w | w ∈ openCube N ∧ XW w r0 ≤ x0 * N + slT N ∧ ∑ k, -Real.log (xE w s k) ≤ XW w r0 + slT N ∧
      ∑ j ∈ univ.erase x, Real.log (clamp01 (w r0 j) / clamp01 (w (flipAt x r0) j)) < (N : ℝ) / 400}

lemma fa_E10_bound (hN : 2 ≤ N) (s r0 : State N) (x : Fin N) :
    cubeM N (faE10 N s r0 x) ≤
      ENNReal.ofReal (faG10 N + if (r0 = s ∨ flipAt x r0 = s) then faS10 N else 0) := by
  split_ifs with hc
  · -- self case: a third row distinct from r0 and r0^x
    obtain ⟨x', hx'⟩ : ∃ x' : Fin N, x' ≠ x := by
      by_cases h : x = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by rw [h]; simp⟩
      · exact ⟨⟨0, by omega⟩, Ne.symm h⟩
    have h0 : r0 ≠ flipAt x' r0 := (flipAt_ne x' r0).symm
    have h1 : flipAt x r0 ≠ flipAt x' r0 := by
      intro he
      have := congrFun he x
      simp [flipAt, Function.update, hx'.symm, Ne.symm hx'] at this
    refine (measure_mono ?_).trans ((fa_r1_core_self r0 (flipAt x' r0) x h0 h1 (x0 * N + slT N)).trans
      (ENNReal.ofReal_le_ofReal ?_))
    · rintro w ⟨ho, hT, -, hD⟩; exact ⟨ho, hT, hD⟩
    · have := fa_G10_nonneg N; unfold faS10; linarith
  · push Not at hc
    refine (measure_mono ?_).trans ((fa_r1_core s r0 x hc.1 hc.2 (x0 * N + slT N) (slT N)).trans
      (ENNReal.ofReal_le_ofReal ?_))
    · exact fun w hw => hw
    · unfold faG10; simp

lemma fa_self_card (s : State N) (x : Fin N) :
    ((univ.filter fun r0 : State N => r0 = s ∨ flipAt x r0 = s).card : ℝ) ≤ 2 := by
  have : (univ.filter fun r0 : State N => r0 = s ∨ flipAt x r0 = s) ⊆ {s, flipAt x s} := by
    intro r0 hr
    rcases (mem_filter.1 hr).2 with h | h
    · simp [h]
    · have : r0 = flipAt x s := by rw [← h, flipAt_flipAt]
      simp [this]
  have h2 := (card_le_card this).trans (card_insert_le _ _)
  simp only [card_singleton] at h2
  exact_mod_cast h2

theorem leafA10 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (forcedBad N s 10) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [fa_arith10, eventually_ge_atTop 2] with N hA hN s
  have hsub : forcedBad N s 10 ⊆ ⋃ r0 : State N, ⋃ x : Fin N, faE10 N s r0 x := by
    intro w hw
    have hw' : w ∈ bField N s (fRetR1 N s) := hw
    obtain ⟨⟨_, ho⟩, x, σ, hreg, hn⟩ := hw'
    simp only [fRetR1, Classical.not_imp, not_le] at hn
    obtain ⟨rfl, hD⟩ := hn
    obtain ⟨c, _, hcell⟩ := hreg
    simp only [Set.mem_iUnion]
    exact ⟨tcRow w, x, ho, hcell.2.2.1, hcell.2.2.2.1, hD⟩
  refine (measure_mono hsub).trans ?_
  calc cubeM N (⋃ r0 : State N, ⋃ x : Fin N, faE10 N s r0 x)
      ≤ ∑ r0 : State N, ∑ x : Fin N, cubeM N (faE10 N s r0 x) :=
        (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun r0 _ => measure_iUnion_fintype_le _ _)
    _ ≤ ∑ r0 : State N, ∑ x : Fin N,
          ENNReal.ofReal (faG10 N + if (r0 = s ∨ flipAt x r0 = s) then faS10 N else 0) :=
        sum_le_sum fun r0 _ => sum_le_sum fun x _ => fa_E10_bound hN s r0 x
    _ = ENNReal.ofReal (∑ r0 : State N, ∑ x : Fin N,
          (faG10 N + if (r0 = s ∨ flipAt x r0 = s) then faS10 N else 0)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        · refine sum_congr rfl fun r0 _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro x _; have := fa_G10_nonneg N; have := fa_S10_nonneg N; split_ifs <;> linarith
        · intro r0 _; refine sum_nonneg fun x _ => ?_
          have := fa_G10_nonneg N; have := fa_S10_nonneg N; split_ifs <;> linarith
    _ ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [sum_comm]
        have hS0 := fa_S10_nonneg N
        have hx : ∀ x : Fin N, ∑ r0 : State N,
            (faG10 N + if (r0 = s ∨ flipAt x r0 = s) then faS10 N else 0) ≤
              2 ^ N * faG10 N + 2 * faS10 N := by
          intro x
          rw [sum_add_distrib, sum_const, card_univ, show Fintype.card (State N) = 2 ^ N by simp,
            nsmul_eq_mul, ← sum_filter, sum_const, nsmul_eq_mul]
          push_cast
          have := fa_self_card s x
          nlinarith
        calc ∑ x : Fin N, ∑ r0 : State N,
              (faG10 N + if (r0 = s ∨ flipAt x r0 = s) then faS10 N else 0)
            ≤ ∑ _x : Fin N, (2 ^ N * faG10 N + 2 * faS10 N) := sum_le_sum fun x _ => hx x
          _ = (N : ℝ) * 2 ^ N * faG10 N + 2 * N * faS10 N := by
              rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
          _ ≤ _ := hA

/-! ### leaf 8 -/

/-- **Sub-leaf (row coincidences of `far`)**, NOT proved here: W7 §2.2 "tc = s or s = r0^x"
(cert 1.550870, cause) and "tc = s^x" (float 1.46, effect); no union over `r0`. -/
def FarSelfLeaf : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide), (r0 = s ∨ flipAt x r0 = s) →
    cubeM N {w | RegEvX N s r0 x σ w} ≤ ENNReal.ofReal (Real.exp (-(RfF * N)) / (8 * N))

lemma fa_far_count : ∀ᶠ N : ℕ in atTop,
    Real.exp (-(RXf * N)) * (2 ^ (N / 3) * (3 / 4) ^ N) ≤ Real.exp (-(RfF * N)) / 2 := by
  have hq : (27 / 32 : ℝ) / (98 / 100 + 95 / 10000) < 1 := by norm_num
  filter_upwards [fa_absorb (q := (27 / 32 : ℝ) / (98 / 100 + 95 / 10000)) (by positivity) hq 16 0]
    with N hN
  simp only [pow_zero, mul_one] at hN
  set a := 2 * (2 ^ (N / 3) * (3 / 4 : ℝ) ^ N) with ha
  set b := Real.exp (-((35 / 10000 : ℝ) * N)) with hb
  have hb0 : 0 ≤ b := (Real.exp_pos _).le
  have hcube : a ^ 3 ≤ b ^ 3 := by
    have e1 : a ^ 3 = 8 * (((2 : ℝ) ^ (N / 3)) ^ 3) * ((3 / 4 : ℝ) ^ 3) ^ N := by
      rw [ha, show ((3 / 4 : ℝ) ^ 3) ^ N = ((3 / 4 : ℝ) ^ N) ^ 3 by
        rw [← pow_mul, ← pow_mul, mul_comm]]
      ring
    have e2 : b ^ 3 = Real.exp (-((105 / 10000 : ℝ) * N)) := by
      rw [hb, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h8 : ((2 : ℝ) ^ (N / 3)) ^ 3 ≤ 2 ^ N := by
      rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h34 : (3 / 4 : ℝ) ^ 3 = 27 / 64 := by norm_num
    have hlow : (1 - 105 / 10000 : ℝ) ^ N ≤ Real.exp (-((105 / 10000 : ℝ) * N)) := by
      rw [show -((105 / 10000 : ℝ) * N) = (N : ℝ) * (-(105 / 10000)) by ring, fa_exp_mul_nat]
      exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (-(105 / 10000 : ℝ))]) N
    have hm : 8 * (2 : ℝ) ^ N * (27 / 64) ^ N ≤ (1 - 105 / 10000 : ℝ) ^ N := by
      have e3 : (27 / 32 : ℝ) / (98 / 100 + 95 / 10000) = (27 / 32) / (1 - 105 / 10000) := by norm_num
      rw [e3, div_pow] at hN
      have hp : (0 : ℝ) < (1 - 105 / 10000) ^ N := by positivity
      rw [mul_div_assoc', div_le_iff₀ hp] at hN
      have : (2 : ℝ) ^ N * (27 / 64) ^ N = (27 / 32) ^ N := by rw [← mul_pow]; norm_num
      nlinarith
    rw [e1, e2, h34]
    have := pow_nonneg (show (0 : ℝ) ≤ 27 / 64 by norm_num) N
    nlinarith
  have hab : a ≤ b := le_of_pow_le_pow_left₀ (by norm_num) hb0 hcube
  have e : Real.exp (-(RXf * N)) * b = Real.exp (-(RfF * N)) := by
    rw [hb, ← Real.exp_add]; unfold RXf RfF; congr 1; ring
  have hE := Real.exp_pos (-(RXf * N))
  rw [← e]
  nlinarith

theorem leafA8_of_self (hself : FarSelfLeaf) : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (forcedBad N s 8) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [hself, rs_absorb 122, fa_far_count, eventually_ge_atTop 7] with N hS hab hc hN7 s
  have hN : 0 < N := by omega
  have hδ : deltaU N < 1 / 2 := by
    unfold deltaU; rw [div_lt_iff₀ (by positivity)]; have : (7 : ℝ) ≤ N := by exact_mod_cast hN7
    linarith
  set B := Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N with hB
  have hslT : 0 ≤ slT N := by
    unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    linarith
  have hB0 : 0 ≤ B := by positivity
  set F := Real.exp (-(RfF * N)) / (8 * N) with hF
  have hF0 : 0 ≤ F := by positivity
  -- the per-triple bound
  set P : State N → Fin N → Prop := fun r0 x => r0 = s ∨ flipAt x r0 = s with hP
  have hterm : ∀ r0 x σ, cubeM N {w | RegEvX N s r0 x σ w} ≤
      ENNReal.ofReal ((if P r0 x then F else 0) + 61 * B) := by
    intro r0 x σ
    by_cases hp : P r0 x
    · rw [if_pos hp]; exact (hS s r0 x σ hp).trans (ENNReal.ofReal_le_ofReal (by linarith))
    · rw [if_neg hp, zero_add]
      simp only [hP, not_or] at hp
      cases σ with
      | cause =>
        refine (regEvX_cause_prob hN s r0 x hp.1 hp.2).trans (ENNReal.ofReal_le_ofReal ?_)
        have := Real.exp_le_exp.2
          (show 14 * slT N + 17 * (8 + slV N) ≤ 19 * slT N + 17 * (8 + slV N) + 9 by linarith)
        rw [hB]; gcongr
      | effect =>
        refine regEvX_effect_prob hN s r0 x hδ (Ne.symm hp.1) ?_
        intro h; apply hp.2; rw [← h, flipAt_flipAt]
  set R := (univ : Finset (State N)).filter fun r0 => ham r0 s ≤ N / 3 with hR
  have hsub : forcedBad N s 8 ⊆ ⋃ r0 ∈ R, ⋃ x : Fin N, ⋃ σ : XSide, {w | RegEvX N s r0 x σ w} := by
    intro w hw
    have hw' : w ∈ bField N s (fFar N s) := hw
    obtain ⟨_, x, σ, hreg, hn⟩ := hw'
    simp only [fFar, not_le] at hn
    simp only [Set.mem_iUnion, hR, mem_filter, mem_univ, true_and]
    exact ⟨tcRow w, by omega, x, σ, hreg⟩
  refine (measure_mono hsub).trans ?_
  have hsum : cubeM N (⋃ r0 ∈ R, ⋃ x : Fin N, ⋃ σ : XSide, {w | RegEvX N s r0 x σ w}) ≤
      ∑ r0 ∈ R, ∑ x : Fin N, ∑ σ : XSide,
        ENNReal.ofReal ((if P r0 x then F else 0) + 61 * B) := by
    refine (measure_biUnion_finset_le _ _).trans (sum_le_sum fun r0 _ => ?_)
    refine (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun x _ => ?_)
    exact (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun σ _ => hterm r0 x σ)
  refine hsum.trans ?_
  have hnn : ∀ r0 x, 0 ≤ (if P r0 x then F else 0) + 61 * B := fun r0 x => by
    split_ifs <;> positivity
  have e1 : ∀ r0 x, ∑ _σ : XSide, ENNReal.ofReal (((if P r0 x then F else 0) + 61 * B)) = ENNReal.ofReal (2 * ((if P r0 x then F else 0) + 61 * B)) := by
    intro r0 x
    rw [sum_const, card_univ, show Fintype.card XSide = 2 from rfl, nsmul_eq_mul,
      ENNReal.ofReal_mul (by norm_num)]
    simp
  simp_rw [e1]
  have hnn2 : ∀ r0 x, 0 ≤ 2 * ((if P r0 x then F else 0) + 61 * B) := fun r0 x => by have := hnn r0 x; linarith
  rw [show (∑ r0 ∈ R, ∑ x : Fin N, ENNReal.ofReal (2 * ((if P r0 x then F else 0) + 61 * B))) =
      ∑ r0 ∈ R, ENNReal.ofReal (∑ x : Fin N, 2 * ((if P r0 x then F else 0) + 61 * B)) from
      sum_congr rfl fun r0 _ => (ENNReal.ofReal_sum_of_nonneg fun x _ => hnn2 r0 x).symm,
    ← ENNReal.ofReal_sum_of_nonneg fun r0 _ => sum_nonneg fun x _ => hnn2 r0 x]
  apply ENNReal.ofReal_le_ofReal
  -- split the two parts
  have hsplit : ∑ r0 ∈ R, ∑ x : Fin N, 2 * ((if P r0 x then F else 0) + 61 * B) =
      2 * ∑ r0 ∈ R, ∑ x : Fin N, (if P r0 x then F else 0) + 122 * B * N * R.card := by
    simp only [mul_add, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_sum]
    ring
  rw [hsplit]
  have hself : ∑ r0 ∈ R, ∑ x : Fin N, (if P r0 x then F else 0) ≤ 2 * N * F := by
    calc ∑ r0 ∈ R, ∑ x : Fin N, (if P r0 x then F else 0)
        ≤ ∑ r0 : State N, ∑ x : Fin N, (if P r0 x then F else 0) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r0 _ _ =>
            sum_nonneg fun x _ => by split_ifs <;> linarith
      _ = ∑ x : Fin N, ∑ r0 : State N, (if P r0 x then F else 0) := sum_comm
      _ ≤ ∑ _x : Fin N, 2 * F := by
          refine sum_le_sum fun x _ => ?_
          rw [← sum_filter, sum_const, nsmul_eq_mul]
          have := fa_self_card s x
          simp only [hP]
          nlinarith
      _ = 2 * N * F := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hRc := fa_card_near s (N / 3)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h4 : 2 * (2 * N * F) = Real.exp (-(RfF * N)) / 2 := by rw [hF]; field_simp; ring
  have hgen : 122 * B * N * (R.card : ℝ) ≤ Real.exp (-(RfF * N)) / 2 := by
    have hB' : 122 * B * N = 122 * N * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) *
        Real.exp (-((10072 / 10000 : ℝ) * N)) / 2 ^ N := by
      rw [hB]; simp only [rsR0]; push_cast; ring
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    calc 122 * B * N * (R.card : ℝ) ≤ 122 * B * N * (2 ^ (N / 3) * (3 / 2) ^ N) :=
          mul_le_mul_of_nonneg_left hRc (by positivity)
      _ = (122 * N * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) *
            Real.exp (-((10072 / 10000 : ℝ) * N))) * (2 ^ (N / 3) * (3 / 4) ^ N) := by
          rw [hB']
          have : (3 / 4 : ℝ) ^ N = (3 / 2) ^ N / 2 ^ N := by rw [← div_pow]; norm_num
          rw [this]; field_simp
      _ ≤ Real.exp (-(RXf * N)) * (2 ^ (N / 3) * (3 / 4) ^ N) :=
          mul_le_mul_of_nonneg_right hab (by positivity)
      _ ≤ _ := hc
  linarith

end Census
end IIT
