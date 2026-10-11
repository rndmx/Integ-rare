/-
Census, B1 leaf `B1_forcedX`: the field leaves 11..21 of `B1ForcedSkel` (agent "forcedB").

Contents (all sorry-free):
* `bField_subset_far`, `leaf_of_farSplit`: every field event splits into the `far` field event (leaf 8) and its
  far part `bFieldF`; a leaf at rate `RfF = 1.0105` follows from both parts at rate `RfF2 = 1.0107`.
* `farPart_of_joint`: the far part of a field event is bounded at rate `RfF2` as soon as, for every far `r0`, every
  `x`, `σ`, the joint event `RegEvX(s,r0,x,σ) ∧ ¬field(r0)` has probability `≤ e^{-RJ N} / 2^N`, `RJ = 1.0108`
  (this is the per-cell interface of W7 §4.4/§7: `RegEvX` alone is `e^{-1.0072 N}/2^N`, `rsR0`).
* Leaf 20 (`sRowE`): PROVED outright: on the regime event, tilt + link give `e ≥ e^{-x0 N - 2 slT} ≥ 2^{-N/2}`.
* Leaf 11 (`rowExc`): PROVED modulo leaf 8 at rate `RfF2` (`leaf11_of_far`): the excess rows are independent of
  the three rows `RegEvX` reads, and one row's excess `Σ (y - 63/125)^+ > N/5` costs `e^{-N/165}`.
-/
import IIT.Census.B1ForcedSkel
import IIT.Census.B1GoodFXRate

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- Rate of the two halves of a split field leaf. -/
noncomputable def RfF2 : ℝ := 10107 / 10000

/-- Per-`(r0, x, σ)` joint rate (times `2^{-N}`) required of a field failure on the regime event. -/
noncomputable def RJ : ℝ := 10108 / 10000

/-! ### 1. Splitting off the `far` field -/

/-- The far part of a field event (field written with an explicit anchor row). -/
def bFieldF (N : ℕ) (s : State N) (P0 : State N → Param N → Fin N → XSide → Prop) : Set (Param N) :=
  B1w N s ∩ openCube N ∩
    {w | ∃ x σ, RegEvX N s (tcRow w) x σ w ∧ N ≤ 3 * ham (tcRow w) s ∧ ¬ P0 (tcRow w) w x σ}

theorem bField_subset_far (s : State N) (P0 : State N → Param N → Fin N → XSide → Prop) :
    bField N s (fun w x σ => P0 (tcRow w) w x σ) ⊆ bField N s (fFar N s) ∪ bFieldF N s P0 := by
  rintro w ⟨hBo, x, σ, hreg, hP⟩
  by_cases hf : N ≤ 3 * ham (tcRow w) s
  · exact Or.inr ⟨hBo, x, σ, hreg, hf, hP⟩
  · exact Or.inl ⟨hBo, x, σ, hreg, hf⟩

lemma two_exp_RfF2_le : ∀ᶠ N : ℕ in atTop,
    2 * Real.exp (-(RfF2 * N)) ≤ Real.exp (-(RfF * N)) := by
  filter_upwards [eventually_ge_atTop 10000] with N hN
  have hN' : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have h2 : (2 : ℝ) ≤ Real.exp ((RfF2 - RfF) * N) := by
    have := Real.add_one_le_exp ((RfF2 - RfF) * N)
    unfold RfF2 RfF at *; nlinarith
  have e : Real.exp (-(RfF * N)) = Real.exp ((RfF2 - RfF) * N) * Real.exp (-(RfF2 * N)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  have := Real.exp_pos (-(RfF2 * N))
  nlinarith

/-- **Split leaf**: the far field leaf and the far part, both at rate `RfF2`, give the leaf at rate `RfF`. -/
theorem leaf_of_farSplit (P0 : ∀ N, State N → State N → Param N → Fin N → XSide → Prop)
    (h8 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (bField N s (fFar N s)) ≤ ENNReal.ofReal (Real.exp (-(RfF2 * N))))
    (hF : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (bFieldF N s (P0 N s)) ≤ ENNReal.ofReal (Real.exp (-(RfF2 * N)))) :
    ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (bField N s (fun w x σ => P0 N s (tcRow w) w x σ)) ≤
        ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [h8, hF, two_exp_RfF2_le] with N h8 hF h2 s
  calc cubeM N (bField N s (fun w x σ => P0 N s (tcRow w) w x σ))
      ≤ cubeM N (bField N s (fFar N s) ∪ bFieldF N s (P0 N s)) := measure_mono (bField_subset_far s _)
    _ ≤ cubeM N (bField N s (fFar N s)) + cubeM N (bFieldF N s (P0 N s)) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(RfF2 * N))) + ENNReal.ofReal (Real.exp (-(RfF2 * N))) :=
        add_le_add (h8 s) (hF s)
    _ = ENNReal.ofReal (2 * Real.exp (-(RfF2 * N))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]; ring_nf
    _ ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := ENNReal.ofReal_le_ofReal h2

/-! ### 2. Absorption -/

/-- Polynomial and `exp(O(log N))` factors are absorbed by any exponential margin. -/
theorem poly_absorb (C : ℝ) (k : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ N : ℕ in atTop,
    C * ((N : ℝ) + 1) ^ k * Real.exp (4000 + 1400 * Real.log N) ≤ Real.exp (δ * N) := by
  have hlo := Real.isLittleO_log_id_atTop
  set K : ℝ := (k : ℝ) + 1400 with hK
  have hK0 : 0 < K := by positivity
  have hev : ∀ᶠ x : ℝ in atTop, |C| + k * Real.log 2 + 4000 + K * Real.log x ≤ δ * x := by
    have h1 := hlo.def (c := δ / (2 * K)) (by positivity)
    filter_upwards [h1, eventually_ge_atTop (2 * (|C| + k * Real.log 2 + 4000) / δ),
      eventually_ge_atTop 1] with x hx hx1 hx2
    simp only [Real.norm_eq_abs, id] at hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx2
    rw [abs_of_nonneg hlog, abs_of_nonneg (by linarith)] at hx
    have h3 : K * Real.log x ≤ δ * x / 2 := by
      have := mul_le_mul_of_nonneg_left hx hK0.le
      calc K * Real.log x ≤ K * (δ / (2 * K) * x) := this
        _ = δ * x / 2 := by field_simp
    have h4 : 2 * (|C| + k * Real.log 2 + 4000) ≤ δ * x := by
      rw [div_le_iff₀ hδ] at hx1; linarith
    linarith
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hev, eventually_ge_atTop 1] with N hN hN1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hC : C ≤ Real.exp |C| := (le_abs_self C).trans (by linarith [Real.add_one_le_exp |C|])
  have hpow : ((N : ℝ) + 1) ^ k ≤ Real.exp (k * (Real.log 2 + Real.log N)) := by
    rw [← Real.log_mul (by norm_num) (by linarith), ← Real.log_pow, Real.exp_log (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (by linarith) k
  calc C * ((N : ℝ) + 1) ^ k * Real.exp (4000 + 1400 * Real.log N)
      ≤ Real.exp |C| * Real.exp (k * (Real.log 2 + Real.log N)) *
          Real.exp (4000 + 1400 * Real.log N) := by
        gcongr
    _ = Real.exp (|C| + k * Real.log 2 + 4000 + K * Real.log N) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [hK]; ring
    _ ≤ Real.exp (δ * N) := Real.exp_le_exp.2 hN

/-! ### 3. The regime event: the uniform per-`(r0, x, σ)` bound for far `r0` -/

/-- The `RS` bound in one form for both sides (far `r0`). -/
theorem regEvX_far_le (hN7 : 7 ≤ N) (s r0 : State N) (x : Fin N) (σ : XSide) (hfar : N ≤ 3 * ham r0 s) :
    cubeM N {w | RegEvX N s r0 x σ w} ≤
      ENNReal.ofReal (61 * (Real.exp (-((rsR0 : ℝ) * N)) *
        Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N)) := by
  have hN : 0 < N := by omega
  have hδ : deltaU N < 1 / 2 := by
    unfold deltaU; rw [div_lt_iff₀ (by positivity)]; have : (7 : ℝ) ≤ N := by exact_mod_cast hN7
    linarith
  have hslT : 0 ≤ slT N := by
    unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    linarith
  have hh0 := ham_flipAt_le_one x r0
  have hh1 := ham_flipAt_le_one x s
  have hne : ∀ a b : State N, 3 ≤ ham a b → a ≠ b := fun a b h hab => by
    subst hab; rw [ham_self] at h; omega
  have hfar3 : 3 ≤ ham r0 s := by omega
  have t1 := ham_triangle (flipAt x r0) r0 s
  cases σ with
  | cause =>
    refine (regEvX_cause_prob hN s r0 x (hne _ _ hfar3) ?_).trans (ENNReal.ofReal_le_ofReal ?_)
    · intro h
      rw [← h] at hfar3
      have : ham r0 (flipAt x r0) ≤ 1 := by rw [ham_comm]; exact hh0
      omega
    · have := Real.exp_le_exp.2
        (show 14 * slT N + 17 * (8 + slV N) ≤ 19 * slT N + 17 * (8 + slV N) + 9 by linarith)
      gcongr
  | effect =>
    refine regEvX_effect_prob hN s r0 x hδ (fun h => hne _ _ hfar3 h.symm) ?_
    intro h
    rw [← h] at hfar3
    have t4 := ham_triangle s (flipAt x s) s
    have : ham (flipAt x s) s ≤ 1 := hh1
    rw [ham_self] at t4
    have t5 := ham_triangle (flipAt x s) s (flipAt x s)
    have : ham s (flipAt x s) ≤ 1 := by rw [ham_comm]; exact hh1
    omega

/-! ### 4. From per-`(r0, x, σ)` joint bounds to the far part -/

/-- **Far part from joint bounds.** -/
theorem farPart_of_joint (P0 : ∀ N, State N → State N → Param N → Fin N → XSide → Prop)
    (hj : ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide), N ≤ 3 * ham r0 s →
      cubeM N {w | RegEvX N s r0 x σ w ∧ ¬ P0 N s r0 w x σ} ≤
        ENNReal.ofReal (Real.exp (-(RJ * N)) / 2 ^ N)) :
    ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (bFieldF N s (P0 N s)) ≤ ENNReal.ofReal (Real.exp (-(RfF2 * N))) := by
  have hab := poly_absorb 2 1 (δ := RJ - RfF2) (by unfold RJ RfF2; norm_num)
  filter_upwards [hj, hab, eventually_ge_atTop 1] with N hj hab hN1 s
  set E : ℝ := Real.exp (-(RJ * N)) / 2 ^ N with hE
  have hE0 : 0 ≤ E := by positivity
  have hsub : bFieldF N s (P0 N s) ⊆ ⋃ r0 : State N, ⋃ x : Fin N, ⋃ σ : XSide,
      {w | N ≤ 3 * ham r0 s ∧ RegEvX N s r0 x σ w ∧ ¬ P0 N s r0 w x σ} := by
    rintro w ⟨_, x, σ, hreg, hf, hP⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨tcRow w, x, σ, hf, hreg, hP⟩
  have hterm : ∀ r0 x σ, cubeM N {w | N ≤ 3 * ham r0 s ∧ RegEvX N s r0 x σ w ∧ ¬ P0 N s r0 w x σ}
      ≤ ENNReal.ofReal E := by
    intro r0 x σ
    by_cases hf : N ≤ 3 * ham r0 s
    · refine le_trans (measure_mono fun w hw => ?_) (hj s r0 x σ hf)
      exact hw.2
    · have : {w | N ≤ 3 * ham r0 s ∧ RegEvX N s r0 x σ w ∧ ¬ P0 N s r0 w x σ} = ∅ :=
        Set.eq_empty_of_forall_notMem fun w hw => hf hw.1
      rw [this, measure_empty]; exact bot_le
  calc cubeM N (bFieldF N s (P0 N s))
      ≤ cubeM N (⋃ r0 : State N, ⋃ x : Fin N, ⋃ σ : XSide,
          {w | N ≤ 3 * ham r0 s ∧ RegEvX N s r0 x σ w ∧ ¬ P0 N s r0 w x σ}) := measure_mono hsub
    _ ≤ ∑ r0 : State N, ∑ x : Fin N, ∑ σ : XSide,
          cubeM N {w | N ≤ 3 * ham r0 s ∧ RegEvX N s r0 x σ w ∧ ¬ P0 N s r0 w x σ} := by
        refine (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun r0 _ => ?_)
        refine (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun x _ => ?_)
        exact measure_iUnion_fintype_le _ _
    _ ≤ ∑ _r0 : State N, ∑ _x : Fin N, ∑ _σ : XSide, ENNReal.ofReal E :=
        sum_le_sum fun r0 _ => sum_le_sum fun x _ => sum_le_sum fun σ _ => hterm r0 x σ
    _ = ENNReal.ofReal (2 ^ N * N * 2 * E) := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show Fintype.card XSide = 2 from rfl, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        rw [ENNReal.ofReal_mul (p := (2 : ℝ) ^ N * N * 2) (by positivity),
          ENNReal.ofReal_mul (p := (2 : ℝ) ^ N * N) (by positivity),
          ENNReal.ofReal_mul (p := (2 : ℝ) ^ N) (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_natCast]
        simp; ring
    _ ≤ ENNReal.ofReal (Real.exp (-(RfF2 * N))) := by
        apply ENNReal.ofReal_le_ofReal
        have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
        have hlog : 0 ≤ Real.log N := Real.log_nonneg hNr
        have h1 : (1 : ℝ) ≤ Real.exp (4000 + 1400 * Real.log N) := Real.one_le_exp (by positivity)
        have e1 : 2 ^ N * N * 2 * E = 2 * N * Real.exp (-(RJ * N)) := by
          rw [hE]; field_simp
        have e2 : Real.exp (-(RfF2 * N)) = Real.exp ((RJ - RfF2) * N) * Real.exp (-(RJ * N)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [e1, e2]
        have hx := Real.exp_pos (-(RJ * N))
        have : 2 * (N : ℝ) ≤ Real.exp ((RJ - RfF2) * N) := by
          refine le_trans ?_ hab
          rw [pow_one]
          nlinarith
        nlinarith

/-! ### 5. Leaf 20 (`sRowE`): deterministic on the regime event -/

lemma sRowE_slack : ∀ᶠ N : ℕ in atTop, x0 * N + 2 * slT N ≤ Real.log 2 * N / 2 := by
  have hq : Real.log 2 = Real.log (4 / 3) + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hpos : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have hab := poly_absorb 1 0 (δ := Real.log (4 / 3) / 8) (by positivity)
  filter_upwards [hab, eventually_ge_atTop 1] with N hab hN1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hNr
  simp only [pow_zero, mul_one, one_mul] at hab
  -- `4000 + 1400 log N ≤ exp(..) ≤ ...`, then take logs
  have h1 : 4000 + 1400 * Real.log N ≤ Real.log (4 / 3) / 8 * N := by
    have := Real.exp_le_exp.1 hab
    exact this
  unfold x0 slT
  rw [hq]
  nlinarith

theorem bField_sRowE_empty : ∀ᶠ N : ℕ in atTop, ∀ s : State N, bField N s (fSRowE N s) = ∅ := by
  filter_upwards [sRowE_slack] with N hsl s
  refine Set.eq_empty_of_forall_notMem ?_
  rintro w ⟨_, x, σ, ⟨c, _, hcell⟩, hfail⟩
  apply hfail
  obtain ⟨_, _, hT, hL, _, _⟩ := hcell
  have hx : ∀ k, 0 < xE w s k := fun k => by
    unfold xE
    have : (1 / 2 : ℝ) ≤ max (clamp01 (w s k)) (1 - clamp01 (w s k)) := by
      rcases le_total (clamp01 (w s k)) (1 / 2) with h | h
      · exact le_max_of_le_right (by linarith)
      · exact le_max_of_le_left h
    linarith
  have heE : eE w s = Real.exp (-∑ k, -Real.log (xE w s k)) := by
    unfold eE
    rw [Real.exp_neg, Real.exp_sum]
    simp only [Real.exp_neg, Real.exp_log (hx _)]
    rw [Finset.prod_inv_distrib, inv_inv]
  show (2 : ℝ) ^ (-(N : ℝ) / 2) ≤ eE w s
  rw [heE, Real.rpow_def_of_pos two_pos]
  apply Real.exp_le_exp.2
  have : Real.log 2 * (-(N : ℝ) / 2) = -(Real.log 2 * N / 2) := by ring
  rw [this]
  linarith

/-- **Leaf 20 (`sRowE`), proved.** -/
theorem leaf20 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (forcedBad N s 20) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [bField_sRowE_empty] with N h s
  show cubeM N (bField N s (fSRowE N s)) ≤ _
  rw [h s, measure_empty]; exact bot_le

/-! ### 6. Independence of one row from an event that does not read it -/

theorem cubeM_inter_row (r : State N) (X : Set (Param N))
    (hX : ∀ w w' : Param N, (∀ q, q ≠ r → w q = w' q) → w ∈ X → w' ∈ X)
    {Y : Set (Fin N → ℝ)} (hY : MeasurableSet Y) :
    cubeM N (X ∩ {w | w r ∈ Y}) = cubeM N X * rowM N Y := by
  classical
  set F : Finset (State N) := {r}
  have hrF : r ∈ F := Finset.mem_singleton_self r
  set H := restrOut F '' X
  set G : Set (F → Fin N → ℝ) := {f | f ⟨r, hrF⟩ ∈ Y}
  have hXH : X = {w | restrOut F w ∈ H} := by
    ext w
    refine ⟨fun hw => ⟨w, hw, rfl⟩, ?_⟩
    rintro ⟨w', hw', he⟩
    refine hX w' w (fun q hq => ?_) hw'
    have hqF : q ∉ F := by simpa [F] using hq
    have := congrFun he ⟨q, hqF⟩
    exact this
  have hYG : {w : Param N | w r ∈ Y} = {w | restrIn F w ∈ G} := rfl
  have hsplit : X ∩ {w | w r ∈ Y} = splitRowsE F ⁻¹' (G ×ˢ H) := by
    rw [hYG]
    conv_lhs => rw [hXH]
    ext w; simp [splitRowsE_apply, and_comm]
  have hrow : cubeM N {w : Param N | w r ∈ Y} = rowM N Y :=
    (measurePreserving_eval (fun _ : State N => rowM N) r).measure_preimage hY.nullMeasurableSet
  rw [hsplit, (mp_splitRows F).measure_preimage_equiv, Measure.prod_prod,
    ← cubeM_restrIn_preimage, ← cubeM_restrOut_preimage, ← hYG, ← hXH, hrow, mul_comm]

/-! ### 7. Leaf 11 (`rowExc`) -/

/-- The excess event of one row. -/
def excBad (N : ℕ) : Set (Fin N → ℝ) := {v | (N : ℝ) / 5 < ∑ i, pos (clamp01 (v i) - b1Cap)}

lemma clamp01_mem (u : ℝ) : 0 ≤ clamp01 u ∧ clamp01 u ≤ 1 := by
  unfold clamp01
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- `(c - 63/125)^+ ≤ (62/125) c²` on `[0, 1]`. -/
lemma pos_sub_cap_le {c : ℝ} (_h0 : 0 ≤ c) (h1 : c ≤ 1) : pos (c - b1Cap) ≤ 62 / 125 * c ^ 2 := by
  unfold pos b1Cap
  refine max_le (by positivity) ?_
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (show (0 : ℝ) ≤ 63 / 125 - 62 / 125 * c by linarith)]

/-- MGF bound for `g(u) = (62/125) clamp(u)²` at `t = 1/3`. -/
lemma lintegral_exp_g_le :
    ∫⁻ u, ENNReal.ofReal (Real.exp (-(1 / 3 : ℝ) * -(62 / 125 * clamp01 u ^ 2))) ∂unif ≤
      ENNReal.ofReal (1 + 62 / 1125 + 3844 / 703125) := by
  have hpt : ∀ u, ENNReal.ofReal (Real.exp (-(1 / 3 : ℝ) * -(62 / 125 * clamp01 u ^ 2))) ≤
      ENNReal.ofReal 1 + ENNReal.ofReal (62 / 375 * clamp01 u ^ 2) +
        ENNReal.ofReal (3844 / 140625 * clamp01 u ^ 4) := by
    intro u
    obtain ⟨_, h1⟩ := clamp01_mem u
    set y := 62 / 375 * clamp01 u ^ 2 with hy
    have hy0 : 0 ≤ y := by positivity
    have hy1 : y ≤ 1 := by rw [hy]; nlinarith
    have e : -(1 / 3 : ℝ) * -(62 / 125 * clamp01 u ^ 2) = y := by rw [hy]; ring
    rw [e, ← ENNReal.ofReal_add (by norm_num) hy0,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hb := Real.abs_exp_sub_one_sub_id_le (x := y) (by rw [abs_of_nonneg hy0]; exact hy1)
    have := (abs_le.1 hb).2
    have hy2 : y ^ 2 = 3844 / 140625 * clamp01 u ^ 4 := by rw [hy]; ring
    linarith
  have hm2 : Measurable fun u : ℝ => ENNReal.ofReal (62 / 375 * clamp01 u ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_clamp01.pow_const 2).const_mul _)
  have hm4 : Measurable fun u : ℝ => ENNReal.ofReal (3844 / 140625 * clamp01 u ^ 4) :=
    ENNReal.measurable_ofReal.comp ((measurable_clamp01.pow_const 4).const_mul _)
  calc ∫⁻ u, ENNReal.ofReal (Real.exp (-(1 / 3 : ℝ) * -(62 / 125 * clamp01 u ^ 2))) ∂unif
      ≤ ∫⁻ u, (ENNReal.ofReal 1 + ENNReal.ofReal (62 / 375 * clamp01 u ^ 2) +
          ENNReal.ofReal (3844 / 140625 * clamp01 u ^ 4)) ∂unif := lintegral_mono hpt
    _ = ENNReal.ofReal 1 + ENNReal.ofReal (62 / 375) * ENNReal.ofReal (1 / ((2 : ℕ) + 1)) +
          ENNReal.ofReal (3844 / 140625) * ENNReal.ofReal (1 / ((4 : ℕ) + 1)) := by
        rw [lintegral_add_right _ hm4, lintegral_add_left measurable_const, lintegral_const,
          measure_univ, mul_one]
        simp_rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 62 / 375 by norm_num),
          ENNReal.ofReal_mul (show (0 : ℝ) ≤ 3844 / 140625 by norm_num)]
        rw [lintegral_const_mul (ENNReal.ofReal (62 / 375)) (f := fun a => ENNReal.ofReal (clamp01 a ^ 2))
            (ENNReal.measurable_ofReal.comp (measurable_clamp01.pow_const 2)),
          lintegral_const_mul (ENNReal.ofReal (3844 / 140625)) (f := fun a => ENNReal.ofReal (clamp01 a ^ 4))
            (ENNReal.measurable_ofReal.comp (measurable_clamp01.pow_const 4)),
          lintegral_unif_pow 2, lintegral_unif_pow 4]
    _ = ENNReal.ofReal (1 + 62 / 1125 + 3844 / 703125) := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by norm_num) (by norm_num),
          ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num

/-- **One row's excess**: `P(Σ (y_i - 63/125)^+ > N/5) ≤ e^{-N/165}`. -/
theorem rowM_excBad_le (N : ℕ) : rowM N (excBad N) ≤ ENNReal.ofReal (Real.exp (-((N : ℝ) / 165))) := by
  set g : Fin N → ℝ → ℝ := fun _ u => -(62 / 125 * clamp01 u ^ 2)
  have hg : ∀ i, Measurable (g i) := fun _ =>
    ((measurable_clamp01.pow_const 2).const_mul _).neg
  have hsub : excBad N ⊆ {v | ∑ i, g i (v i) ≤ -((N : ℝ) / 5)} := by
    intro v hv
    simp only [excBad, Set.mem_setOf_eq] at hv
    simp only [Set.mem_setOf_eq, g, sum_neg_distrib, neg_le_neg_iff]
    refine hv.le.trans (sum_le_sum fun i _ => ?_)
    exact pos_sub_cap_le (clamp01_mem _).1 (clamp01_mem _).2
  have hch := chernoff_pi (fun _ : Fin N => unif) g hg (a := -((N : ℝ) / 5)) (t := 1 / 3) (by norm_num)
  have hrow : rowM N = Measure.pi fun _ : Fin N => unif := rfl
  set m : ℝ := 1 + 62 / 1125 + 3844 / 703125 with hm
  calc rowM N (excBad N) ≤ rowM N {v | ∑ i, g i (v i) ≤ -((N : ℝ) / 5)} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (1 / 3 * -((N : ℝ) / 5))) * ∏ _i : Fin N, ENNReal.ofReal m := by
        rw [hrow]
        refine hch.trans ?_
        gcongr with i
        exact lintegral_exp_g_le
    _ = ENNReal.ofReal (Real.exp (-((N : ℝ) / 15)) * m ^ N) := by
        rw [prod_const, card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow (by norm_num),
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 2; ring_nf
    _ ≤ ENNReal.ofReal (Real.exp (-((N : ℝ) / 165))) := by
        apply ENNReal.ofReal_le_ofReal
        have hmexp : m ^ N ≤ Real.exp ((m - 1) * N) := by
          have h := Real.add_one_le_exp (m - 1)
          calc m ^ N ≤ Real.exp (m - 1) ^ N :=
                pow_le_pow_left₀ (by rw [hm]; norm_num) (by linarith) N
            _ = Real.exp ((m - 1) * N) := by rw [← Real.exp_nat_mul]; ring_nf
        calc Real.exp (-((N : ℝ) / 15)) * m ^ N ≤ Real.exp (-((N : ℝ) / 15)) * Real.exp ((m - 1) * N) :=
              mul_le_mul_of_nonneg_left hmexp (Real.exp_pos _).le
          _ = Real.exp (-((N : ℝ) / 15) + (m - 1) * N) := by rw [Real.exp_add]
          _ ≤ Real.exp (-((N : ℝ) / 165)) := by
              apply Real.exp_le_exp.2
              have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
              rw [hm]; nlinarith

lemma measurableSet_excBad (N : ℕ) : MeasurableSet (excBad N) := by
  unfold excBad
  refine measurableSet_lt measurable_const ?_
  refine Finset.measurable_sum _ fun i _ => ?_
  unfold pos
  exact measurable_const.max ((measurable_clamp01.comp (measurable_pi_apply i)).sub measurable_const)

/-- `RegEvX` reads only the rows `r0`, `s` and `spRow σ`. -/
theorem regEvX_congr {s r0 : State N} {x : Fin N} {σ : XSide} {w w' : Param N}
    (h0 : w r0 = w' r0) (h1 : w s = w' s) (h2 : w (spRow s r0 x σ) = w' (spRow s r0 x σ)) :
    RegEvX N s r0 x σ w ↔ RegEvX N s r0 x σ w' := by
  cases σ <;> simp only [spRow] at h2 <;>
    simp only [RegEvX, CellEvX, baseE, compE, lamX, XW, xE, pTe, h0, h1, h2]

/-- The rows-excess field written with an explicit anchor row. -/
def P0RowExc (N : ℕ) (s : State N) : State N → Param N → Fin N → XSide → Prop := fun r0 w x σ =>
  ∀ r ∈ sensRows s r0, r ≠ r0 → r ≠ s → r ≠ spRow s r0 x σ →
    ∑ i, pos (clamp01 (w r i) - b1Cap) ≤ (N : ℝ) / 5

/-- **Joint bound for `rowExc`** (per far `(r0, x, σ)`, rate `1.0072 + 1/165 > RJ`). -/
theorem joint_rowExc : ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide),
    N ≤ 3 * ham r0 s →
      cubeM N {w | RegEvX N s r0 x σ w ∧ ¬ P0RowExc N s r0 w x σ} ≤
        ENNReal.ofReal (Real.exp (-(RJ * N)) / 2 ^ N) := by
  have hab := poly_absorb (2 * 61) 4 (δ := (rsR0 : ℝ) + 1 / 165 - RJ)
    (by unfold RJ rsR0; norm_num)
  filter_upwards [hab, eventually_ge_atTop 7] with N hab hN7 s r0 x σ hfar
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  set B := Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N with hB
  set T := Real.exp (-((N : ℝ) / 165)) with hT
  have hB0 : 0 ≤ B := by positivity
  set R := (sensRows s r0).filter fun r => r ≠ r0 ∧ r ≠ s ∧ r ≠ spRow s r0 x σ
  have hsub : {w | RegEvX N s r0 x σ w ∧ ¬ P0RowExc N s r0 w x σ} ⊆
      ⋃ r ∈ R, {w | RegEvX N s r0 x σ w} ∩ {w | w r ∈ excBad N} := by
    rintro w ⟨hreg, hP⟩
    simp only [P0RowExc, not_forall, not_le, exists_prop] at hP
    obtain ⟨r, hr, h1, h2, h3, hex⟩ := hP
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
    exact ⟨r, mem_filter.2 ⟨hr, h1, h2, h3⟩, hreg, hex⟩
  have hterm : ∀ r ∈ R, cubeM N ({w | RegEvX N s r0 x σ w} ∩ {w | w r ∈ excBad N}) ≤
      ENNReal.ofReal (61 * B * T) := by
    intro r hr
    obtain ⟨_, h1, h2, h3⟩ := mem_filter.1 hr
    rw [cubeM_inter_row r _ ?_ (measurableSet_excBad N)]
    · rw [ENNReal.ofReal_mul (by positivity)]
      exact mul_le_mul' (regEvX_far_le hN7 s r0 x σ hfar) (rowM_excBad_le N)
    · intro w w' hq hw
      exact (regEvX_congr (hq _ (Ne.symm h1)) (hq _ (Ne.symm h2)) (hq _ (Ne.symm h3))).1 hw
  have hcard : (R.card : ℝ) ≤ 2 * ((N : ℝ) + 1) ^ 4 := by
    have := (Finset.card_filter_le (sensRows s r0)
      (fun r => r ≠ r0 ∧ r ≠ s ∧ r ≠ spRow s r0 x σ)).trans (card_sensRows_le s r0)
    exact_mod_cast this
  calc cubeM N {w | RegEvX N s r0 x σ w ∧ ¬ P0RowExc N s r0 w x σ}
      ≤ cubeM N (⋃ r ∈ R, {w | RegEvX N s r0 x σ w} ∩ {w | w r ∈ excBad N}) := measure_mono hsub
    _ ≤ ∑ r ∈ R, cubeM N ({w | RegEvX N s r0 x σ w} ∩ {w | w r ∈ excBad N}) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _r ∈ R, ENNReal.ofReal (61 * B * T) := sum_le_sum hterm
    _ = ENNReal.ofReal (R.card * (61 * B * T)) := by
        rw [sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (p := (R.card : ℝ)) (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (Real.exp (-(RJ * N)) / 2 ^ N) := by
        apply ENNReal.ofReal_le_ofReal
        have hsl := rs_slack_le N
        have hS : Real.exp (19 * slT N + 17 * (8 + slV N) + 9) ≤ Real.exp (4000 + 1400 * Real.log N) :=
          Real.exp_le_exp.2 hsl
        have h2N : (0 : ℝ) < 2 ^ N := by positivity
        have e1 : (R.card : ℝ) * (61 * B * T) =
            (R.card : ℝ) * 61 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) *
              (Real.exp (-((rsR0 : ℝ) * N)) * T) / 2 ^ N := by
          rw [hB]; ring
        rw [e1, div_le_div_iff_of_pos_right h2N]
        have e2 : Real.exp (-((rsR0 : ℝ) * N)) * T =
            Real.exp (-(((rsR0 : ℝ) + 1 / 165 - RJ) * N)) * Real.exp (-(RJ * N)) := by
          rw [hT, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
        rw [e2]
        have hx := Real.exp_pos (-(RJ * N))
        have hy : Real.exp ((((rsR0 : ℝ) + 1 / 165 - RJ) * N)) *
            Real.exp (-(((rsR0 : ℝ) + 1 / 165 - RJ) * N)) = 1 := by
          rw [← Real.exp_add]; simp
        have hz := Real.exp_pos (-(((rsR0 : ℝ) + 1 / 165 - RJ) * N))
        have hS0 := Real.exp_pos (19 * slT N + 17 * (8 + slV N) + 9)
        have hc0 : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
        -- `card · 61 · e^{slack} ≤ 122 (N+1)^4 e^{4000 + 1400 log N} ≤ e^{δ N}`
        have hk : (R.card : ℝ) * 61 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) ≤
            Real.exp ((((rsR0 : ℝ) + 1 / 165 - RJ) * N)) := by
          refine le_trans ?_ hab
          calc (R.card : ℝ) * 61 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9)
              ≤ (2 * ((N : ℝ) + 1) ^ 4) * 61 * Real.exp (4000 + 1400 * Real.log N) := by gcongr
            _ = 2 * 61 * ((N : ℝ) + 1) ^ 4 * Real.exp (4000 + 1400 * Real.log N) := by ring
        calc (R.card : ℝ) * 61 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) *
              (Real.exp (-(((rsR0 : ℝ) + 1 / 165 - RJ) * N)) * Real.exp (-(RJ * N)))
            ≤ Real.exp ((((rsR0 : ℝ) + 1 / 165 - RJ) * N)) *
              (Real.exp (-(((rsR0 : ℝ) + 1 / 165 - RJ) * N)) * Real.exp (-(RJ * N))) := by
              gcongr
          _ = Real.exp (-(RJ * N)) := by rw [← mul_assoc, hy, one_mul]

/-- **Leaf 11 (`rowExc`)**, proved from leaf 8 (`far`) at rate `RfF2 = 1.0107` (W7: `far` costs 1.063964). -/
theorem leaf11_of_far
    (h8 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (bField N s (fFar N s)) ≤ ENNReal.ofReal (Real.exp (-(RfF2 * N)))) :
    ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 11) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) :=
  leaf_of_farSplit P0RowExc h8 (farPart_of_joint P0RowExc joint_rowExc)

end Census
end IIT
