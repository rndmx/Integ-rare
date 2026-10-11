/-
Census, B1 forced leaf 7: `NatTier3Stmt` reduced to concrete events, agent "forcedG".

PROVED here (sorry-free):
* `concTc_rare`, `concEAll_rare` : the subcube concentration events at `tcRow w` (union over the `2^N` rows) and
                                around `s` at every effect state `te` (union over `2^N`) fail with probability `≤ 2^N · N 2^N · 2 e^{-N²/2}` (`concC_cond`, `concE_cond`,
                                Fubini over the rows outside `rowsA`).
* `g_superexp`                : that bound is `≤ e^{-C N}` eventually, for every `C`.
* `tier3Good_of_rest`         : eventually in `N`, `Tier3Rest ∧ concC(tc) ∧ concE ⇒ Tier3Good` (all W10 numerics with
                                `D = DU N`, `d* = dsU N`, `δ = dU N`, `η = 1/N`, through `keyHyp_of_events`).
* `natTier3_of_rest`          : `NatTier3Stmt C` from `NatTier3RestStmt C'` (`C < C'`).

The residual `Tier3Rest` (stated exactly below) collects: unique maximal cause state; at every maximal effect state
(`EffRest`) no exact tie; `λ_min ≥ 1/N²` on both sides, `SpreadGood` (5D) and `SmallCutGood` (7D, all `1 ≤ |K| < D`) on both sides, and `SpreadLarge` in count form.
-/
import IIT.Census.B1ForcedGSplit
import IIT.Census.B1UnivGlue

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-! ### Concentration: unconditional, with the union over `tc` -/

/-- Subcube concentration of the cause side around the row `r0`. -/
def concCAt (N : ℕ) (w : Param N) (r0 : State N) : Prop :=
  ∀ j C, j ∉ C → DU N ≤ C.card → |cmean w (univ \ C) r0 j - 1 / 2| ≤ dU N C.card

/-- Subcube concentration of the effect side around `s`, at EVERY effect state `te`. -/
def concEAll (N : ℕ) (s : State N) (w : Param N) : Prop :=
  ∀ te : State N, ∀ j C, j ∉ C → DU N ≤ C.card →
    |effUnit (tpmOf (flipP s w)) Cᶜ s j (te j) - 1 / 2| ≤ dU N C.card

/-- Concentration at one effect state. -/
def concETe (N : ℕ) (s te : State N) (w : Param N) : Prop :=
  ∀ j C, j ∉ C → DU N ≤ C.card →
    |effUnit (tpmOf (flipP s w)) Cᶜ s j (te j) - 1 / 2| ≤ dU N C.card

lemma measurableSet_concCAt (r0 : State N) : MeasurableSet {w : Param N | concCAt N w r0} := by
  unfold concCAt
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun C =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le ((m_cmean _ r0 j).sub_const _).abs measurable_const

/-- The transition probability in flipped coordinates. -/
lemma g_prob_te (w : Param N) (s r : State N) (j : Fin N) (b : Bool) :
    (tpmOf (flipP s w)).prob j r b = if b = s j then clamp01 (w r j) else 1 - clamp01 (w r j) := by
  have h1 := prob_eq_clamp (flipP s w) s r j
  rw [flipP_invol s w] at h1
  have hn := (tpmOf (flipP s w)).normalized j r
  split_ifs with hb
  · rw [hb]; exact h1
  · have hb' : b = !(s j) := by cases b <;> cases h : s j <;> simp_all
    subst hb'
    cases hs : s j <;> rw [hs] at h1 <;> simp only [Bool.not_false, Bool.not_true] <;> linarith

lemma m_effUnitTe (s te : State N) (C : Finset (Fin N)) (j : Fin N) :
    Measurable fun w : Param N => effUnit (tpmOf (flipP s w)) Cᶜ s j (te j) := by
  unfold effUnit
  simp_rw [g_prob_te]
  refine (Finset.measurable_sum _ fun r _ => ?_).div_const _
  split_ifs
  · exact b1m_clamp r j
  · exact measurable_const.sub (b1m_clamp r j)

lemma measurableSet_concETe (s te : State N) : MeasurableSet {w : Param N | concETe N s te w} := by
  unfold concETe
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun C =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le ((m_effUnitTe s te C j).sub_const _).abs measurable_const

/-- The conditional-to-unconditional step: a uniform conditional bound integrates. -/
lemma g_cube_le_of_cond (F : Finset (State N)) {X : Set (Param N)} (hX : MeasurableSet X) {c : ENNReal}
    (h : ∀ f, rowsOutM F {g | glueRows F f g ∈ X} ≤ c) : cubeM N X ≤ c := by
  rw [cubeM_eq_lintegral_rows F hX]
  calc ∫⁻ f, rowsOutM F {g | glueRows F f g ∈ X} ∂rowsInM F ≤ ∫⁻ _f, c ∂rowsInM F := lintegral_mono h
    _ = c := by rw [lintegral_const, measure_univ, mul_one]

theorem concC_rare (hN : 3 ≤ N) (s r0 : State N) :
    cubeM N {w | ¬ concCAt N w r0} ≤
      ENNReal.ofReal (N * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2))) := by
  have x : Fin N := ⟨0, by omega⟩
  refine g_cube_le_of_cond (rowsA s r0 x) (measurableSet_concCAt r0).compl fun f => ?_
  have e : {g | glueRows (rowsA s r0 x) f g ∈ {w : Param N | concCAt N w r0}ᶜ} =
      {g | ¬ ∀ j C, j ∉ C → DU N ≤ C.card →
        |cmean (glueRows (rowsA s r0 x) f g) (univ \ C) r0 j - 1 / 2| ≤ dU N C.card} := by
    ext g; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, concCAt]
  rw [e]
  exact concC_cond hN s r0 x f

/-- The effect subcube average at a fixed effect state, as an average of row readings. -/
lemma effUnit_te_glue (A : Finset (State N)) (s te : State N) (f : A → Fin N → ℝ)
    (g : {r // r ∉ A} → Fin N → ℝ) (C : Finset (Fin N)) (j : Fin N) :
    effUnit (tpmOf (flipP s (glueRows A f g))) Cᶜ s j (te j) =
      (∑ r ∈ agree Cᶜ s, (if h : r ∈ A then
          (if te j = s j then clamp01 (f ⟨r, h⟩ j) else 1 - clamp01 (f ⟨r, h⟩ j))
        else (if te j = s j then clamp01 (g ⟨r, h⟩ j) else 1 - clamp01 (g ⟨r, h⟩ j)))) / 2 ^ C.card := by
  rw [effUnit, card_agree, card_compl_sub]
  push_cast
  congr 1
  refine sum_congr rfl fun r _ => ?_
  rw [g_prob_te]
  by_cases hr : r ∈ A
  · rw [dif_pos hr, glueRows_of_mem A f g hr]
  · rw [dif_neg hr, glueRows_of_not_mem A f g hr]

theorem concETe_rare (hN : 3 ≤ N) (s te : State N) :
    cubeM N {w | ¬ concETe N s te w} ≤
      ENNReal.ofReal (N * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2))) := by
  classical
  have x : Fin N := ⟨0, by omega⟩
  set A := rowsA s s x
  refine g_cube_le_of_cond A (measurableSet_concETe s te).compl fun f => ?_
  have e : {g | glueRows A f g ∈ {w : Param N | concETe N s te w}ᶜ} =
      {g | ¬ ∀ j C, j ∉ C → DU N ≤ C.card →
        |effUnit (tpmOf (flipP s (glueRows A f g))) Cᶜ s j (te j) - 1 / 2| ≤ dU N C.card} := by
    ext g; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, concETe]
  rw [e]
  refine conc_union A (card_rowsA_le s s x) hN _ fun j C _ _ => ?_
  refine ⟨agree Cᶜ s,
    fun v => if te j = s j then clamp01 v else 1 - clamp01 v,
    fun r => if te j = s j then clamp01 (f r j) else 1 - clamp01 (f r j),
    by rw [card_agree, card_compl_sub], ?_, ?_, ?_, ?_, fun g => effUnit_te_glue A s te f g C j⟩
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

theorem concEAll_rare (hN : 3 ≤ N) (s : State N) :
    cubeM N {w | ¬ concEAll N s w} ≤
      ENNReal.ofReal (2 ^ N * (N * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2)))) := by
  have hsub : {w : Param N | ¬ concEAll N s w} ⊆ ⋃ te : State N, {w | ¬ concETe N s te w} := by
    intro w hw
    rw [Set.mem_ofPred_eq] at hw
    unfold concEAll at hw
    push Not at hw
    obtain ⟨te, h⟩ := hw
    refine Set.mem_iUnion.2 ⟨te, ?_⟩
    rw [Set.mem_ofPred_eq]
    unfold concETe
    push Not
    exact h
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
  refine (Finset.sum_le_sum fun te _ => concETe_rare hN s te).trans (le_of_eq ?_)
  have h2 : ENNReal.ofReal ((2 : ℝ) ^ N) = ((2 ^ N : ℕ) : ENNReal) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  rw [sum_const, card_state, nsmul_eq_mul, ← h2, ← ENNReal.ofReal_mul (by positivity)]

theorem concTc_rare (hN : 3 ≤ N) (s : State N) :
    cubeM N {w | ¬ concCAt N w (tcRow w)} ≤
      ENNReal.ofReal (2 ^ N * (N * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2)))) := by
  have hsub : {w : Param N | ¬ concCAt N w (tcRow w)} ⊆ ⋃ r0 : State N, {w | ¬ concCAt N w r0} :=
    fun w hw => by
      rw [Set.mem_ofPred_eq] at hw
      exact Set.mem_iUnion.2 ⟨tcRow w, by rw [Set.mem_ofPred_eq]; exact hw⟩
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
  refine (Finset.sum_le_sum fun r0 _ => concC_rare hN s r0).trans (le_of_eq ?_)
  have h2 : ENNReal.ofReal ((2 : ℝ) ^ N) = ((2 ^ N : ℕ) : ENNReal) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  rw [sum_const, card_state, nsmul_eq_mul, ← h2, ← ENNReal.ofReal_mul (by positivity)]

/-- The concentration bounds are superexponentially small. -/
lemma g_superexp (C : ℝ) : ∀ᶠ N : ℕ in atTop,
    2 * (2 ^ N * (N * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2)))) ≤ Real.exp (-(C * N)) := by
  filter_upwards [eventually_ge_atTop (⌈|C|⌉₊ * 2 + 40)] with N hN
  have hC : |C| ≤ ⌈|C|⌉₊ := Nat.le_ceil _
  have hNr : ((⌈|C|⌉₊ * 2 + 40 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
  push_cast at hNr
  have hN2 : (N : ℝ) ≤ 2 ^ N := by
    have := Nat.lt_two_pow_self (n := N); exact_mod_cast this.le
  have hl2 : Real.log 2 < 7 / 10 := by have := Real.log_two_lt_d9; linarith
  have h4 : (N : ℝ) * 2 ^ N ≤ Real.exp (N * (2 * Real.log 2)) := by
    calc (N : ℝ) * 2 ^ N ≤ 2 ^ N * 2 ^ N := mul_le_mul_of_nonneg_right hN2 (by positivity)
      _ = Real.exp (N * (2 * Real.log 2)) := by
          rw [two_pow_eq_exp, ← Real.exp_add]; ring_nf
  have h2 : (2 : ℝ) ^ N = Real.exp (N * Real.log 2) := two_pow_eq_exp N
  have h4e : (4 : ℝ) ≤ Real.exp 2 := by
    have h1 := Real.exp_one_gt_d9
    have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hlog0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq : (N : ℝ) * (N / 2) ≥ N * (|C| + 20) := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg N)
  have hl : (N : ℝ) * Real.log 2 ≤ N * (7 / 10) := mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg N)
  have hcN : -(|C| * N) ≤ -(C * N) := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C) (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
  rw [h2] at h4
  calc 2 * (2 ^ N * (N * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2))))
      ≤ 2 * (Real.exp (N * Real.log 2) * (Real.exp (N * (2 * Real.log 2)) *
          (2 * Real.exp (-((N : ℝ) ^ 2) / 2)))) := by
        rw [h2]; gcongr
    _ = 4 * Real.exp (N * Real.log 2 + N * (2 * Real.log 2) + -((N : ℝ) ^ 2) / 2) := by
        rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ Real.exp 2 * Real.exp (-(C * N) - 2) := by
        gcongr
        nlinarith
    _ = Real.exp (-(C * N)) := by rw [← Real.exp_add]; ring_nf

/-! ### The residual event and the W10 numerics -/

/-- **The residual effect-side event at one maximal effect state `te`.** -/
structure EffRest (N : ℕ) (s : State N) (w : Param N) (te : State N) : Prop where
  noTie : ∀ j j', j ≠ j' → phTAt s w te j ≠ phTAt s w te j'
  lowE : 1 / (N : ℝ) ^ 2 ≤ leMinAt s w te
  spreadE : ∀ A' : Finset (Fin N), A'.card < 2 * DU N →
    5 * (DU N : ℝ) < ∑ j ∈ A'ᶜ, (kF (lamEz (flipP s w) s te) j - leMinAt s w te)
  smallE : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N →
    7 * (DU N : ℝ) < kM (lamEz (flipP s w) s te) (leMinAt s w te) K
  countE : 5 * (univ.filter fun j => kF (lamEz (flipP s w) s te) j - leMinAt s w te ≤ 1 / (N : ℝ)).card < N

/-- **The residual Tier 3 event** (everything except the concentration fields). -/
structure Tier3Rest (N : ℕ) (s : State N) (w : Param N) : Prop where
  mem_open : w ∈ openCube N
  stateC : sysMaxCauseStates (tpmOf (flipP s w)) univ s s = {tcRow w}
  lowC : 1 / (N : ℝ) ^ 2 ≤ lcMin s w
  spreadC : ∀ A' : Finset (Fin N), A'.card < 2 * DU N →
    5 * (DU N : ℝ) < ∑ j ∈ A'ᶜ, (kF (lamCz (flipP s w) s (tcRow w)) j - lcMin s w)
  smallC : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N →
    7 * (DU N : ℝ) < kM (lamCz (flipP s w) s (tcRow w)) (lcMin s w) K
  countC : 5 * (univ.filter fun j => kF (lamCz (flipP s w) s (tcRow w)) j - lcMin s w ≤ 1 / (N : ℝ)).card < N
  eff : ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) univ s s, EffRest N s w te

/-- `N · δ_d ≤ 16 / (2^20 N²)` for `d ≥ 2 D`. -/
lemma g_N_dU_2DU (hN : 1 ≤ N) {d : ℕ} (hd : 2 * DU N ≤ d) : (N : ℝ) * dU N d ≤ 1 / (N : ℝ) ^ 2 / 1000 := by
  refine (mul_le_mul_of_nonneg_left (dU_anti N hd) (Nat.cast_nonneg _)).trans ?_
  unfold dU DU
  have hdiv : (2 * (4 * Nat.log 2 N + 20)) / 2 = 4 * Nat.log 2 N + 20 := by omega
  rw [hdiv]
  set L := Nat.log 2 N
  have h1 := two_pow_log_gt N
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (1 / 2 : ℝ) ^ (4 * L + 20) = 1 / (2 ^ 20 * ((2 ^ L) ^ 2) ^ 2) := by
    rw [one_div_pow, ← pow_mul, ← pow_mul, ← pow_add]; congr 2; ring
  rw [hp]
  have hL0 : (0 : ℝ) < 2 ^ L := by positivity
  have hsq : (N : ℝ) ^ 2 < 4 * (2 ^ L) ^ 2 := by nlinarith
  have hq : (N : ℝ) ^ 4 < 16 * ((2 ^ L) ^ 2) ^ 2 := by nlinarith [sq_nonneg ((N : ℝ) ^ 2)]
  rw [← mul_assoc, ← sq, mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The W10 numerics, eventually. -/
lemma g_numerics : ∀ᶠ N : ℕ in atTop, 64 ≤ N ∧ 5 * dsU N ≤ 3 * N ∧ dsU N ≤ N - 1 := by
  filter_upwards [ev_lin_C, eventually_ge_atTop 64] with N h hN
  have hD : (0 : ℝ) ≤ DU N := Nat.cast_nonneg _
  have h1 : (10 * DU N + 400 : ℝ) ≤ N := by nlinarith
  have h2 : 10 * DU N + 400 ≤ N := by exact_mod_cast h1
  refine ⟨hN, ?_, ?_⟩ <;> unfold dsU <;> omega

/-- **From the residual event and the concentration fields to `Tier3Good`.** -/
theorem tier3Good_of_rest : ∀ᶠ N : ℕ in atTop, ∀ (s : State N) (w : Param N),
    Tier3Rest N s w → concCAt N w (tcRow w) → concEAll N s w → Tier3Good N s w := by
  filter_upwards [g_numerics, ev_N_dU_top] with N ⟨hN64, hd5, hdN⟩ htop
  intro s w hr hcC hcE
  have hN1 : 1 ≤ N := by omega
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hN0 : (0 : ℝ) < N := by linarith
  have hz : flipP s w ∈ openCube N := flipP_mem_openCube hr.mem_open
  have hinv : flipP s (flipP s w) = w := flipP_invol s w
  have hDN : DU N ≤ N - 1 := DU_le hN64
  have hDd : 2 * DU N ≤ dsU N := by unfold dsU; omega
  have hD1 : 1 ≤ DU N := by unfold DU; omega
  have hDr : (1 : ℝ) ≤ DU N := by exact_mod_cast hD1
  have hDN' : DU N ≤ N := by omega
  have hDNr : (DU N : ℝ) ≤ N := by exact_mod_cast hDN'
  -- the δ facts
  have hδ0 : ∀ d, 0 ≤ dU N d := dU_nonneg N
  have hδtop0 := hδ0 (N - 1)
  have hδs : dU N (N - 1) ≤ 1 / 100 := by
    have : dU N (N - 1) ≤ N * dU N (N - 1) := le_mul_of_one_le_left hδtop0 (by linarith)
    linarith
  have hfar : ∀ d, 2 * DU N ≤ d → (N : ℝ) * dU N d ≤ 1 / (N : ℝ) ^ 2 / 1000 :=
    fun d hd => g_N_dU_2DU hN1 hd
  have htopf : (N : ℝ) * dU N (N - 1) ≤ 1 / (N : ℝ) ^ 2 / 1000 := hfar _ (hDd.trans hdN)
  have hDU := N_dU_DU hN1
  have hN2 : (0 : ℝ) < 1 / (N : ℝ) ^ 2 := by positivity
  have hN2' : 1 / (N : ℝ) ^ 2 ≤ 1 / 64 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hδc : 12 * DU N * dU N (N - 1) + 3 * N * (dU N (DU N) + dU N (N - 1)) < DU N := by
    have : (DU N : ℝ) * dU N (N - 1) ≤ N * dU N (N - 1) := mul_le_mul_of_nonneg_right hDNr hδtop0
    nlinarith
  have hBfar : ∀ lmin : ℝ, 1 / (N : ℝ) ^ 2 ≤ lmin → ∀ d, dsU N ≤ d → d + 2 ≤ N →
      ((N : ℝ) - 1) * (3 * (dU N d + dU N (N - 1))) < lmin := by
    intro lmin hl d hd _
    have h1 := hfar d (hDd.trans hd)
    have h0 := hδ0 d
    have : ((N : ℝ) - 1) * (3 * (dU N d + dU N (N - 1))) ≤ 3 * (N * dU N d + N * dU N (N - 1)) := by
      nlinarith
    linarith
  have hη : 6 * (dU N (2 * DU N) + dU N (N - 1)) < 1 / (N : ℝ) := by
    have h1 := hfar (2 * DU N) le_rfl
    have h2 : (N : ℝ) * (6 * (dU N (2 * DU N) + dU N (N - 1))) < 1 := by nlinarith
    rw [lt_div_iff₀ hN0]; linarith
  have hj0 : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hbdd : ∀ f : Fin N → ℝ, BddBelow (Set.range f) := fun f => (Set.finite_range f).bddBelow
  -- cause side
  obtain ⟨mc1, mc2, mc3, mc4, mc5⟩ := lamCz_means hz s (tcRow w)
  rw [hinv] at mc1 mc2 mc3 mc4 mc5
  have kc := keyHyp_of_events (lam := lamCz (flipP s w) s (tcRow w)) (x := fun j => clamp01 (w (tcRow w) j))
    (A := fun j C => cmean w (univ \ C) (tcRow w) j) (δ := dU N) (lmin := lcMin s w) (η := 1 / (N : ℝ))
    (D := DU N) (dstar := dsU N) mc1 mc2 mc3 (fun j => clamp01_le_one _) mc4 mc5
    (fun j C hj hC => hcC j C hj hC) hδ0 hδs (fun d d' _ h => dU_anti N h) hD1 hDN hDd hd5
    (hN2.trans_le hr.lowC) (fun j => ciInf_le (hbdd _) j) hj0 hδc (hBfar _ hr.lowC) hr.spreadC
    hr.smallC hr.countC hη
  -- effect side, at every maximal effect state
  refine ⟨hr.mem_open, hr.stateC, fun te hte => ?_, fun te hte => (hr.eff te hte).noTie⟩
  have he := hr.eff te hte
  obtain ⟨me1, me2, me3, me4, me5⟩ := lamEz_means hz s te
  have ke := keyHyp_of_events (lam := lamEz (flipP s w) s te)
    (x := fun j => (tpmOf (flipP s w)).prob j s (te j))
    (A := fun j C => effUnit (tpmOf (flipP s w)) Cᶜ s j (te j)) (δ := dU N) (lmin := leMinAt s w te)
    (η := 1 / (N : ℝ)) (D := DU N) (dstar := dsU N) me1 me2 me3
    (fun j => (tpmOf (flipP s w)).le_one j s _) me4 me5
    (fun j C hj hC => hcE te j C hj hC) hδ0 hδs (fun d d' _ h => dU_anti N h) hD1 hDN hDd hd5
    (hN2.trans_le he.lowE) (fun j => ciInf_le (hbdd _) j) hj0 hδc (hBfar _ he.lowE) he.spreadE
    he.smallE he.countE hη
  exact ⟨_, _, _, _, _, _, kc, ke⟩

/-- **The residual statement for Tier 3**: `bNat ∖ Tier3Rest` is rare. -/
def NatTier3RestStmt (C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bNat N s ∩ {w | ¬ Tier3Rest N s w}) ≤ ENNReal.ofReal (Real.exp (-(C * N)))

/-- **NatTier3 from the residual statement** (the concentration part is proved). -/
theorem natTier3_of_rest {C C' : ℝ} (hC : C < C') (h : NatTier3RestStmt C') : NatTier3Stmt C := by
  have hm : C < (C + C') / 2 := by linarith
  have hm' : (C + C') / 2 < C' := by linarith
  refine natTier3_of_good ?_
  filter_upwards [h, tier3Good_of_rest, g_superexp ((C + C') / 2), g_absorb 2 hm,
    eventually_ge_atTop 3] with N hR hG hS hA hN3 s
  set c := 2 ^ N * (N * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2)))
  have hsub : bNat N s ∩ {w | ¬ Tier3Good N s w} ⊆
      (bNat N s ∩ {w | ¬ Tier3Rest N s w}) ∪ ({w | ¬ concCAt N w (tcRow w)} ∪ {w | ¬ concEAll N s w}) := by
    rintro w ⟨hw, hng⟩
    by_cases h1 : Tier3Rest N s w
    · by_cases h2 : concCAt N w (tcRow w)
      · by_cases h3 : concEAll N s w
        · exact absurd (hG s w h1 h2 h3) hng
        · exact Or.inr (Or.inr h3)
      · exact Or.inr (Or.inl h2)
    · exact Or.inl ⟨hw, h1⟩
  have hc0 : 0 ≤ c := by positivity
  have hE : cubeM N {w | ¬ concEAll N s w} ≤ ENNReal.ofReal c := concEAll_rare hN3 s
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hR' : Real.exp (-(C' * N)) ≤ Real.exp (-((C + C') / 2 * N)) :=
    Real.exp_le_exp.2 (by nlinarith)
  calc cubeM N (bNat N s ∩ {w | ¬ Tier3Good N s w})
      ≤ cubeM N (bNat N s ∩ {w | ¬ Tier3Rest N s w}) +
          (cubeM N {w | ¬ concCAt N w (tcRow w)} + cubeM N {w | ¬ concEAll N s w}) :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _)))
    _ ≤ ENNReal.ofReal (Real.exp (-((C + C') / 2 * N))) + (ENNReal.ofReal c + ENNReal.ofReal c) :=
        add_le_add ((hR s).trans (ENNReal.ofReal_le_ofReal hR')) (add_le_add (concTc_rare hN3 s) hE)
    _ = ENNReal.ofReal (Real.exp (-((C + C') / 2 * N)) + 2 * c) := by
        rw [← ENNReal.ofReal_add hc0 hc0, ← ENNReal.ofReal_add (Real.exp_pos _).le (by positivity)]
        ring_nf
    _ ≤ ENNReal.ofReal (2 * Real.exp (-((C + C') / 2 * N))) := ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (Real.exp (-(C * N))) := ENNReal.ofReal_le_ofReal hA

end Census
end IIT
