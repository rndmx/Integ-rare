/-
Census, B1 lower bound (C1') part (b): `B1` holds with conditional probability → 1 on `E_X` (W7 §3 items 1-5),
and the assembly of `B1_lowerX` from (a) and (b).

TOP-DOWN SKELETON. Leaves (`sorry`), each with its intended proof:
* `EX_local`         — `EX` and `EXFacts` read only the rows `A = {r0, r0^x, s}` (congruence; routine).
* `EXFacts_whp`      — the per-unit sums of W7's check table hold on `EX` w.h.p.:
                       `type_event_hoeffding` (B1TypeMGF) + kernel-certified type expectations
                       (exact cell averages; g5c2_lbX_cert_40_100_200.json).
* `RestGood_cond`    — given the rows `A` (with `EXFacts`), the other rows are good w.h.p.:
                       W4's `thmW4`/`thmB5` events (B1NearUniv), to be RE-STATED FOR THREE FIXED ROWS
                       `{r0, r0^x, s}` (W7 §3 item 4); `RestGood` may gain fields (FE6 generic bound, no ties).
* `tc_of_EX`         — item 1: `tcRow w = r0` (FE6-type bound; `r0^x` lighter by `N/30`; `P(s) ≤ 2^{-N/3}`).
* `phi_univ_ge_EX`   — items 2, 3, 5: `φ_s(U) ≥ β N / 10⁶` (W3 Thm 6.1 via `phi_lower_fail`, `univ_tier3`;
                       check V puts the MIP in `𝓕_x`; check M0 gives the value; `te` = argmax).
* `phi_S_le_EX`      — item 4: every proper `S` has `φ_s(S) < β N / 10⁶` (pairs `pair_upper_tilt`, triples /
                       4-sets C15/C15b, `5 ≤ |S| ≤ K2N` Prop KT, `|S| > K2N` B5, `S ∌ x` EF, `S = U \ {x}` check S).
* `card_far_rows`    — `#{r0 : N ≤ 3 ham r0 s} ≥ 2^N / 2` eventually (Hamming ball count).
* `measurableSet_EXFacts`, `measurableSet_RestGood` — routine.
Assembly (PROVED here from the leaves): `EX_B1_half` and `B1_lowerX'`.
-/
import IIT.Census.B1LowerEX
import IIT.Census.B1NearUniv
import IIT.Census.B1EXFacts2D

set_option maxRecDepth 100000

namespace IIT
namespace Census

open MeasureTheory Filter Finset

variable {N : ℕ}

/-! ### Per-unit quantities of the regime-X event (W7 §3 check table) -/

/-- The fixed rows of the event. -/
def rowsA (s r0 : State N) (x : Fin N) : Finset (State N) := {r0, flipAt x r0, s}

/-- `λ_j = ln (2y / (y + U))`, `y = y_{r0,j}`, `U = y_{r0^x,j}`. -/
noncomputable def lamEX (w : Param N) (r0 : State N) (x j : Fin N) : ℝ :=
  Real.log (2 * clamp01 (w r0 j) / (clamp01 (w r0 j) + clamp01 (w (flipAt x r0) j)))

/-- **The per-unit facts on `E_X`** (W7 §3 checks T, L, V, M0, S, D_total; thresholds below the certified
type expectations of the corrected 40 × 100 design by fixed margins). -/
structure EXFacts (N : ℕ) (s r0 : State N) (x : Fin N) (w : Param N) : Prop where
  T : XW w r0 ≤ x0 * N - 9 * Real.log N
  L : ∑ k, -Real.log (xE w s k) ≤ XW w r0 - 3 * Real.log N
  V : ∑ j, min (lamEX w r0 x j) (Real.log (clamp01 (w r0 j) / (1001 / 2000))) ≤ -((N : ℝ) / (2 * 10 ^ 6))
  M0 : (N : ℝ) / 10 ^ 5 ≤ ∑ j, min (lamEX w r0 x j) (Real.log (2 * clamp01 (w r0 j)))
  S : (N : ℝ) / 400 ≤ ∑ j, lamEX w r0 x j
  D : (N : ℝ) / 30 ≤ ∑ j, Real.log (clamp01 (w r0 j) / clamp01 (w (flipAt x r0) j))

/-- **The other rows are good.** Conditions on the rows outside `rowsA` only (so that they are independent of the
fixed rows). `fe6`: no other row is as heavy as the current cause row can be (`X(r) ≥ x0 N`). FIELDS TO ADD for
items 2-5 (three-fixed-row versions of W4's `GoodW`/`E5`); `GoodW ∧ E5` itself is false on `E_X` (`GoodW.gU`). -/
structure RestGood (N : ℕ) (s r0 : State N) (x : Fin N) (w : Param N) : Prop where
  fe6 : ∀ r ∉ rowsA s r0 x, x0 * N ≤ XW w r

/-! ### Leaves -/

/-- `EX` and `EXFacts` read only the rows of `rowsA`. -/
theorem EX_local (s r0 : State N) (x : Fin N) {w w' : Param N} (h : ∀ r ∈ rowsA s r0 x, w' r = w r) :
    (w ∈ EX N s r0 x ∧ EXFacts N s r0 x w) ↔ (w' ∈ EX N s r0 x ∧ EXFacts N s r0 x w') := by
  have h0 : w' r0 = w r0 := h r0 (by simp [rowsA])
  have h1 : w' (flipAt x r0) = w (flipAt x r0) := h _ (by simp [rowsA])
  have h2 : w' s = w s := h s (by simp [rowsA])
  have hXW : XW w' r0 = XW w r0 := by unfold XW; rw [h0]
  have hxE : ∀ k, xE w' s k = xE w s k := fun k => by unfold xE; rw [h2]
  have hlam : ∀ j, lamEX w' r0 x j = lamEX w r0 x j := fun j => by unfold lamEX; rw [h0, h1]
  have hEX : w' ∈ EX N s r0 x ↔ w ∈ EX N s r0 x := by
    classical
    have e1 : ∀ i : Fin KP, (univ.filter fun j => (w' r0 j, w' (flipAt x r0) j) ∈ exIP (cP i)) =
        univ.filter fun j => (w r0 j, w (flipAt x r0) j) ∈ exIP (cP i) := fun i =>
      Finset.filter_congr fun j _ => by rw [congrFun h0 j, congrFun h1 j]
    have e2 : ∀ i : Fin KS, (univ.filter fun k => w' s k ∈ exIS (cS i)) =
        univ.filter fun k => w s k ∈ exIS (cS i) := fun i =>
      Finset.filter_congr fun k _ => by rw [congrFun h2 k]
    simp only [EX, Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨fun i => by rw [← a i]; exact congrArg _ (e1 i).symm,
        fun i => by rw [← b i]; exact congrArg _ (e2 i).symm⟩
    · rintro ⟨a, b⟩
      exact ⟨fun i => by rw [← a i]; exact congrArg _ (e1 i), fun i => by rw [← b i]; exact congrArg _ (e2 i)⟩
  have hF : EXFacts N s r0 x w' ↔ EXFacts N s r0 x w := by
    constructor
    · rintro ⟨hT, hL, hV, hM, hS, hD⟩
      simp only [hXW, hxE, hlam, h0, h1] at hT hL hV hM hS hD
      exact ⟨hT, hL, hV, hM, hS, hD⟩
    · rintro ⟨hT, hL, hV, hM, hS, hD⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hXW, hxE, hlam, h0, h1] <;> assumption
  rw [hEX, hF]

theorem measurableSet_RestGood (s r0 : State N) (x : Fin N) :
    MeasurableSet {w : Param N | RestGood N s r0 x w} := by
  have : {w : Param N | RestGood N s r0 x w} = ⋂ r ∈ (rowsA s r0 x)ᶜ, {w : Param N | x0 * N ≤ XW w r} := by
    ext w; simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_coe, Finset.mem_compl]
    exact ⟨fun h => h.fe6, fun h => ⟨h⟩⟩
  rw [this]
  refine Finset.measurableSet_biInter _ fun r _ => measurableSet_le measurable_const ?_
  unfold XW
  exact Finset.measurable_sum _ fun i _ => (Real.measurable_log.comp
    (clamp01_measurable.comp ((measurable_pi_apply i).comp (measurable_pi_apply r)))).neg

/-- `e^{-2N k²/d} ≤ 1/32` eventually. -/
lemma ev_exp_small (k d : ℝ) (hk : 0 < k) (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (Real.exp (-(2 * N * k ^ 2 / d))) ≤ 1 / 32 := by
  have hc : 0 < 2 * k ^ 2 / d := by positivity
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.log 32 / (2 * k ^ 2 / d))] with N hN
  rw [div_le_iff₀ hc] at hN
  have : Real.exp (-(2 * N * k ^ 2 / d)) ≤ 1 / 32 := by
    rw [show (1 / 32 : ℝ) = Real.exp (-Real.log 32) by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num]
    apply Real.exp_le_exp.2
    have : 2 * (N : ℝ) * k ^ 2 / d = N * (2 * k ^ 2 / d) := by ring
    linarith
  calc ENNReal.ofReal (Real.exp (-(2 * N * k ^ 2 / d))) ≤ ENNReal.ofReal (1 / 32) := ENNReal.ofReal_le_ofReal this
    _ = 1 / 32 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp

/-- **(b2) The per-unit facts hold on `EX` with conditional probability `≥ 3/4`.** -/
theorem EXFacts_whp : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    cubeM N (EX N s r0 x \ {w | EXFacts N s r0 x w}) ≤ cubeM N (EX N s r0 x) / 4 := by
  filter_upwards [EX_T_fail, EX_L_fail, EX_S_fail, EX_V_fail, EX_M_fail, EX_D_fail,
    ev_exp_small (1 / (8 * 10 ^ 6)) ((1 - 0) ^ 2) (by norm_num) (by norm_num),
    ev_exp_small (1 / (2 * 10 ^ 7)) ((1 - 0) ^ 2) (by norm_num) (by norm_num),
    ev_exp_small (1 / (2 * 10 ^ 6)) ((1 - -1) ^ 2) (by norm_num) (by norm_num),
    ev_exp_small (1 / 10 ^ 7) ((1 - -1) ^ 2) (by norm_num) (by norm_num),
    ev_exp_small (1 / (2 * 10 ^ 3)) ((12 - -1) ^ 2) (by norm_num) (by norm_num),
    eventually_ge_atTop 6] with N hT hL hS hV hM hD e1 e2 e3 e4 e5 hN6 s r0 x hham
  have h0 : r0 ≠ s := fun h => by rw [h, ham_self] at hham; omega
  have h1 : flipAt x r0 ≠ s := fun h => by
    have := ham_flipAt_le_one x r0; rw [h, ham_comm] at this; omega
  set E := EX N s r0 x
  set a := cubeM N E
  have hcov : E \ {w | EXFacts N s r0 x w} ⊆
      (E ∩ {w | ¬ XW w r0 ≤ x0 * N - 9 * Real.log N}) ∪
      (E ∩ {w | ¬ ∑ k, -Real.log (xE w s k) ≤ XW w r0 - 3 * Real.log N}) ∪
      (E ∩ {w | ¬ ∑ j, min (gS (w r0 j, w (flipAt x r0) j)) (Real.log (clamp01 (w r0 j) / (1001 / 2000))) ≤
        -((N : ℝ) / (2 * 10 ^ 6))}) ∪
      (E ∩ {w | ¬ (N : ℝ) / 10 ^ 5 ≤ ∑ j, min (gS (w r0 j, w (flipAt x r0) j)) (Real.log (2 * clamp01 (w r0 j)))}) ∪
      (E ∩ {w | ¬ (N : ℝ) / 400 ≤ ∑ j, gS (w r0 j, w (flipAt x r0) j)}) ∪
      (E ∩ openCube N ∩ {w | ¬ (N : ℝ) / 30 ≤ ∑ j, Real.log (clamp01 (w r0 j) / clamp01 (w (flipAt x r0) j))}) ∪
      (openCube N)ᶜ := by
    rintro w ⟨hw, hF⟩
    by_contra hno
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, not_or, not_and,
      not_not] at hno
    obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := hno
    exact hF ⟨a1 hw, a2 hw, a3 hw, a4 hw, a5 hw, a6 ⟨hw, a7⟩⟩
  have hu := (measure_mono (μ := cubeM N) hcov).trans
    ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add
      ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add
        ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add le_rfl le_rfl))
          le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl))
  rw [cubeM_compl_openCube, add_zero] at hu
  refine hu.trans ?_
  have t1 : _ ≤ a * (1 / 32) := (hT s r0 x h0 h1).trans (by gcongr)
  have t2 : _ ≤ a * (1 / 32) + a * (1 / 32) := (hL s r0 x h0 h1).trans (by gcongr <;> exact e2)
  have t3 : _ ≤ a * (1 / 32) := (hV s r0 x h0 h1).trans (by gcongr)
  have t4 : _ ≤ a * (1 / 32) := (hM s r0 x h0 h1).trans (by gcongr)
  have t5 : _ ≤ a * (1 / 32) := (hS s r0 x h0 h1).trans (by gcongr)
  have t6 : _ ≤ a * (1 / 32) := (hD s r0 x h0 h1).trans (by gcongr)
  calc _ ≤ a * (1 / 32) + (a * (1 / 32) + a * (1 / 32)) + a * (1 / 32) + a * (1 / 32) + a * (1 / 32) +
        a * (1 / 32) := by gcongr
    _ = a * (7 * (1 / 32)) := by ring
    _ ≤ a * (1 / 4) := by
        gcongr
        rw [mul_one_div, ENNReal.div_le_iff (by norm_num) (by norm_num), one_div,
          show (32 : ENNReal) = 4 * 8 by norm_num, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
          one_mul]
        norm_num
    _ = a / 4 := by rw [mul_one_div]

/-- **Leaf**: given the fixed rows (satisfying `EX` and `EXFacts`), the other rows are good with probability
`≥ 3/4`. -/
theorem RestGood_cond : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    ∀ f : rowsA s r0 x → Fin N → ℝ, ∀ g0 : {r // r ∉ rowsA s r0 x} → Fin N → ℝ,
      (glueRows (rowsA s r0 x) f g0 ∈ EX N s r0 x ∧ EXFacts N s r0 x (glueRows (rowsA s r0 x) f g0)) →
      rowsOutM (rowsA s r0 x) {g | ¬ RestGood N s r0 x (glueRows (rowsA s r0 x) f g)} ≤ 1 / 4 := by
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
  have hev : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ N * Real.exp (-(N * (x0 - 1 - Real.log x0))) ≤ 1 / 4 := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.log 4 / (1 / 200))] with N hN
    rw [div_le_iff₀ (by norm_num)] at hN
    have h2N : (2 : ℝ) ^ N = Real.exp (Real.log 2 * N) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    rw [h2N, ← Real.exp_add, show (1 / 4 : ℝ) = Real.exp (-Real.log 4) by
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
    _ ≤ ENNReal.ofReal (1 / 4) := ENNReal.ofReal_le_ofReal hN
    _ = 1 / 4 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp

/-- On the open cube, `P(r) = e^{-X(r)}`. -/
lemma Pw_eq_exp {w : Param N} (ho : w ∈ openCube N) (r : State N) : Pw w r = Real.exp (-XW w r) := by
  unfold Pw XW
  rw [Finset.sum_neg_distrib, neg_neg, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := ho r i
  have hc : clamp01 (w r i) = w r i := by unfold clamp01; rw [min_eq_right h.2.le, max_eq_right h.1.le]
  rw [hc, Real.exp_log h.1]

/-- `X(r0^x) - X(r0) = Σ ln(y/U)` on the open cube. -/
lemma XW_flip_sub {w : Param N} (ho : w ∈ openCube N) (r0 : State N) (x : Fin N) :
    XW w (flipAt x r0) - XW w r0 = ∑ j, Real.log (clamp01 (w r0 j) / clamp01 (w (flipAt x r0) j)) := by
  unfold XW
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 := ho r0 j; have h1 := ho (flipAt x r0) j
  have c0 : clamp01 (w r0 j) = w r0 j := by unfold clamp01; rw [min_eq_right h0.2.le, max_eq_right h0.1.le]
  have c1 : clamp01 (w (flipAt x r0) j) = w (flipAt x r0) j := by
    unfold clamp01; rw [min_eq_right h1.2.le, max_eq_right h1.1.le]
  rw [c0, c1, Real.log_div h0.1.ne' h1.1.ne']; ring

/-- Mass of the lower row-`s` cells. -/
lemma aS_lower : ∑ i : Fin KS, (((if (cS i).x1 ≤ 1 / 2 then (cS i).a else 0 : ℚ)) : ℝ) = 1 / 2 := by
  have h := Fin.sum_univ_fun_getElem exSCells (fun C : EXSCell => (((if C.x1 ≤ 1 / 2 then C.a else 0 : ℚ)) : ℝ))
  refine Eq.trans h ?_
  have e : (exSCells.map fun C : EXSCell => (((if C.x1 ≤ 1 / 2 then C.a else 0 : ℚ)) : ℝ)).sum =
      (((exSCells.map fun C : EXSCell => if C.x1 ≤ 1 / 2 then C.a else 0).sum : ℚ) : ℝ) := by
    rw [Rat.cast_list_sum, List.map_map]; rfl
  rw [e, exS_lower_mass]; norm_num

/-- On `EX`, at least `N/2 - KS²` entries of row `s` lie below `1/2`. -/
lemma EX_s_lower {w : Param N} (hw : w ∈ EX N s r0 x) :
    (N : ℝ) / 2 - (KS : ℝ) ^ 2 ≤ ((univ.filter fun k => w s k ∈ Set.Iio (1 / 2 : ℝ)).card : ℝ) := by
  classical
  have hv : ∀ j, (univ.filter fun i => w s i ∈ (exIS ∘ cS) j).card = nS N j := fun j =>
    (congrArg Finset.card (Finset.filter_congr fun _ _ => Iff.rfl)).trans (hw.2 j)
  set J := univ.filter fun i : Fin KS => (cS i).x1 ≤ 1 / 2
  have hJ : ∀ j ∈ J, (exIS ∘ cS) j ⊆ Set.Iio (1 / 2 : ℝ) := fun j hj y hy => by
    have h1 : ((cS j).x1 : ℝ) ≤ 1 / 2 := by
      have := (Finset.mem_filter.1 hj).2
      have := (Rat.cast_le (K := ℝ)).2 this; push_cast at this; exact this
    exact lt_of_lt_of_le hy.2 h1
  have hc := cr_type_count_ge (exIS ∘ cS) exIS_disjoint (nS_sum N) hv (Set.Iio (1 / 2 : ℝ)) J hJ
  have hc' : (∑ j ∈ J, (nS N j : ℝ)) ≤ ((univ.filter fun k => w s k ∈ Set.Iio (1 / 2 : ℝ)).card : ℝ) := by
    exact_mod_cast hc
  have hlow : ∀ j ∈ J, ((cS j).a : ℝ) * N - KS ≤ (nS N j : ℝ) := fun j _ => by
    have := abs_le.1 (nS_err N j); linarith [this.1]
  have hsum : ∑ j ∈ J, (((cS j).a : ℝ) * N - KS) ≤ ∑ j ∈ J, (nS N j : ℝ) := Finset.sum_le_sum hlow
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul] at hsum
  have hJa : ∑ j ∈ J, ((cS j).a : ℝ) = 1 / 2 := by
    rw [Finset.sum_filter, ← aS_lower]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have hJc : (J.card : ℝ) ≤ KS := by
    have := Finset.card_le_univ J; simp only [Fintype.card_fin] at this; exact_mod_cast this
  rw [hJa] at hsum
  have hKS : (0 : ℝ) ≤ KS := Nat.cast_nonneg _
  nlinarith

/-- `P(s) ≤ (1/2)^{#lower}`. -/
lemma Pw_s_le {w : Param N} (ho : w ∈ openCube N) (s : State N) :
    Pw w s ≤ (1 / 2 : ℝ) ^ (univ.filter fun k => w s k ∈ Set.Iio (1 / 2 : ℝ)).card := by
  classical
  set L := univ.filter fun k => w s k ∈ Set.Iio (1 / 2 : ℝ)
  have hc : ∀ k, clamp01 (w s k) = w s k := fun k => by
    have h := ho s k; unfold clamp01; rw [min_eq_right h.2.le, max_eq_right h.1.le]
  unfold Pw
  calc ∏ k, clamp01 (w s k) ≤ ∏ k ∈ L, clamp01 (w s k) := by
        rw [← Finset.prod_filter_mul_prod_filter_not univ (fun k => w s k ∈ Set.Iio (1 / 2 : ℝ))]
        refine mul_le_of_le_one_right (Finset.prod_nonneg fun k _ => clamp01_nonneg _) ?_
        exact Finset.prod_le_one (fun k _ => clamp01_nonneg _) fun k _ => clamp01_le_one _
    _ ≤ ∏ _k ∈ L, (1 / 2 : ℝ) := Finset.prod_le_prod (fun k _ => clamp01_nonneg _) fun k hk => by
        rw [hc]; exact (Finset.mem_filter.1 hk).2.le
    _ = _ := by rw [Finset.prod_const]

/-- **Item 1: on the good event the current-cause row is `r0`.** -/
theorem tc_of_EX : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    ∀ w ∈ openCube N, w ∈ EX N s r0 x → EXFacts N s r0 x w → RestGood N s r0 x w → tcRow w = r0 := by
  have hx0 := cr_x0_bounds
  have hx0hi : x0 ≤ 2027325541 / 10000000000 := by have := hx0.2; unfold crX0hi at this; push_cast at this; exact this
  have hev : ∀ᶠ N : ℕ in atTop, ((KS : ℝ) ^ 2 + 1) * Real.log 2 ≤ N * (Real.log 2 / 2 - 2027325541 / 10000000000) := by
    have hl : (0 : ℝ) < Real.log 2 / 2 - 2027325541 / 10000000000 := by
      have := Real.log_two_gt_d9; linarith
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop
      (((KS : ℝ) ^ 2 + 1) * Real.log 2 / (Real.log 2 / 2 - 2027325541 / 10000000000))] with N hN
    rwa [div_le_iff₀ hl] at hN
  filter_upwards [hev, eventually_ge_atTop 6] with N hN hN6
  intro s r0 x hham w ho hw hF hR
  have h0 : r0 ≠ s := fun h => by rw [h, ham_self] at hham; omega
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hT : XW w r0 ≤ x0 * N := by have := hF.T; linarith
  refine tcRow_eq_of_strict fun r hr => ?_
  rw [Pw_eq_exp ho, Pw_eq_exp ho]
  by_cases hA : r ∈ rowsA s r0 x
  · simp only [rowsA, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with h | h | h
    · exact absurd h hr
    · -- the flipped row
      rw [h]
      apply Real.exp_lt_exp.2
      have hD := hF.D
      rw [← XW_flip_sub ho] at hD
      have : (0 : ℝ) < N / 30 := by
        have : (6 : ℝ) ≤ N := by exact_mod_cast hN6
        linarith
      linarith
    · -- the current row `s`
      rw [h, ← Pw_eq_exp ho]
      refine lt_of_le_of_lt (Pw_s_le ho s) ?_
      have hL := EX_s_lower (s := s) (r0 := r0) (x := x) hw
      set c := (univ.filter fun k => w s k ∈ Set.Iio (1 / 2 : ℝ)).card
      have hpow : (1 / 2 : ℝ) ^ c = Real.exp (-(c * Real.log 2)) := by
        rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num), one_div, inv_pow]
      rw [hpow]
      apply Real.exp_lt_exp.2
      have hl2 := Real.log_two_gt_d9
      have hX : XW w r0 ≤ 2027325541 / 10000000000 * N := by
        have := mul_le_mul_of_nonneg_right hx0hi (Nat.cast_nonneg N); linarith
      nlinarith
  · -- generic rows
    apply Real.exp_lt_exp.2
    have h1 := hR.fe6 r hA
    have : (0 : ℝ) < 9 * Real.log N := by
      have : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
      have := Real.log_pos this; linarith
    have := hF.T
    linarith


/-- Flipping every bit: `ham (!r) s = N - ham r s`. -/
lemma ham_flipAll (r s : State N) : ham (fun i => !r i) s + ham r s = N := by
  unfold ham
  have : (univ.filter fun j => (!r j) ≠ s j) = univ.filter fun j => ¬ (r j ≠ s j) := by
    ext j; simp only [mem_filter, mem_univ, true_and]; cases r j <;> cases s j <;> simp
  rw [this, add_comm, Finset.card_filter_add_card_filter_not, card_univ, Fintype.card_fin]

/-- At least half of the rows are far from `s` (for every `N`). -/
theorem card_far_rows : ∀ᶠ N in atTop, ∀ s : State N,
    (2 : ℝ) ^ N / 2 ≤ ((univ.filter fun r0 : State N => N ≤ 3 * ham r0 s).card : ℝ) := by
  refine Filter.Eventually.of_forall fun N s => ?_
  set P := univ.filter fun r0 : State N => N ≤ 3 * ham r0 s
  set Q := univ.filter fun r0 : State N => ¬ N ≤ 3 * ham r0 s
  have hQP : Q.card ≤ P.card := by
    refine Finset.card_le_card_of_injOn (fun r i => !r i) (fun r hr => ?_) (fun r _ r' _ h => ?_)
    · simp only [Q, P, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hr ⊢
      have := ham_flipAll r s
      omega
    · funext i; have := congrFun h i; simpa using this
  have hsum : P.card + Q.card = 2 ^ N := by
    rw [Finset.card_filter_add_card_filter_not, card_univ]; simp
  have : (2 : ℝ) ^ N = P.card + Q.card := by exact_mod_cast hsum.symm
  have hQP' : (Q.card : ℝ) ≤ P.card := by exact_mod_cast hQP
  linarith

open Classical in
theorem measurableSet_EX (s r0 : State N) (x : Fin N) : MeasurableSet (EX N s r0 x) := by
  have h1 : ∀ i : Fin KP, MeasurableSet {w : Param N |
      (univ.filter fun j => (w r0 j, w (flipAt x r0) j) ∈ exIP (cP i)).card = nP N i} := fun i =>
    measurableSet_card_filter (fun (j : Fin N) (w : Param N) => (w r0 j, w (flipAt x r0) j) ∈ exIP (cP i))
      (fun j => (((measurable_pi_apply j).comp (measurable_pi_apply r0)).prodMk
        ((measurable_pi_apply j).comp (measurable_pi_apply (flipAt x r0))))
        (measurableSet_Ico.prod measurableSet_Ico)) _
  have h2 : ∀ i : Fin KS, MeasurableSet {w : Param N |
      (univ.filter fun k => w s k ∈ exIS (cS i)).card = nS N i} := fun i =>
    measurableSet_card_filter (fun (k : Fin N) (w : Param N) => w s k ∈ exIS (cS i))
      (fun k => ((measurable_pi_apply k).comp (measurable_pi_apply s)) measurableSet_Ico) _
  have : EX N s r0 x = (⋂ i, {w : Param N |
      (univ.filter fun j => (w r0 j, w (flipAt x r0) j) ∈ exIP (cP i)).card = nP N i}) ∩
      ⋂ i, {w : Param N | (univ.filter fun k => w s k ∈ exIS (cS i)).card = nS N i} := by
    ext w; simp [EX]
  rw [this]
  exact (MeasurableSet.iInter h1).inter (MeasurableSet.iInter h2)

theorem measurableSet_EXFacts (s r0 : State N) (x : Fin N) :
    MeasurableSet {w : Param N | w ∈ EX N s r0 x ∧ EXFacts N s r0 x w} := by
  have hy : ∀ (r : State N) (j : Fin N), Measurable fun w : Param N => clamp01 (w r j) := fun r j =>
    clamp01_measurable.comp ((measurable_pi_apply j).comp (measurable_pi_apply r))
  have hXW : Measurable fun w : Param N => XW w r0 := by
    unfold XW; exact Finset.measurable_sum _ fun j _ => (Real.measurable_log.comp (hy r0 j)).neg
  have hxE : Measurable fun w : Param N => ∑ k, -Real.log (xE w s k) := by
    unfold xE
    exact Finset.measurable_sum _ fun k _ =>
      (Real.measurable_log.comp ((hy s k).max (measurable_const.sub (hy s k)))).neg
  have hlam : ∀ j, Measurable fun w : Param N => lamEX w r0 x j := fun j => by
    unfold lamEX
    exact Real.measurable_log.comp ((measurable_const.mul (hy r0 j)).div ((hy r0 j).add (hy _ j)))
  have hV : Measurable fun w : Param N =>
      ∑ j, min (lamEX w r0 x j) (Real.log (clamp01 (w r0 j) / (1001 / 2000))) :=
    Finset.measurable_sum _ fun j _ => (hlam j).min (Real.measurable_log.comp ((hy r0 j).div_const _))
  have hM : Measurable fun w : Param N => ∑ j, min (lamEX w r0 x j) (Real.log (2 * clamp01 (w r0 j))) :=
    Finset.measurable_sum _ fun j _ => (hlam j).min (Real.measurable_log.comp (measurable_const.mul (hy r0 j)))
  have hS : Measurable fun w : Param N => ∑ j, lamEX w r0 x j := Finset.measurable_sum _ fun j _ => hlam j
  have hD : Measurable fun w : Param N => ∑ j, Real.log (clamp01 (w r0 j) / clamp01 (w (flipAt x r0) j)) :=
    Finset.measurable_sum _ fun j _ => Real.measurable_log.comp ((hy r0 j).div (hy _ j))
  have : {w : Param N | w ∈ EX N s r0 x ∧ EXFacts N s r0 x w} = EX N s r0 x ∩
      ({w | XW w r0 ≤ x0 * N - 9 * Real.log N} ∩
        {w | ∑ k, -Real.log (xE w s k) ≤ XW w r0 - 3 * Real.log N} ∩
        {w | ∑ j, min (lamEX w r0 x j) (Real.log (clamp01 (w r0 j) / (1001 / 2000))) ≤
          -((N : ℝ) / (2 * 10 ^ 6))} ∩
        {w | (N : ℝ) / 10 ^ 5 ≤ ∑ j, min (lamEX w r0 x j) (Real.log (2 * clamp01 (w r0 j)))} ∩
        {w | (N : ℝ) / 400 ≤ ∑ j, lamEX w r0 x j} ∩
        {w | (N : ℝ) / 30 ≤ ∑ j, Real.log (clamp01 (w r0 j) / clamp01 (w (flipAt x r0) j))}) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hE, ⟨a, b, c, d, e, f⟩⟩; exact ⟨hE, ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩⟩
    · rintro ⟨hE, ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩⟩; exact ⟨hE, ⟨a, b, c, d, e, f⟩⟩
  rw [this]
  exact (measurableSet_EX s r0 x).inter
    ((((((measurableSet_le hXW measurable_const).inter (measurableSet_le hxE (hXW.sub_const _))).inter
      (measurableSet_le hV measurable_const)).inter (measurableSet_le measurable_const hM)).inter
      (measurableSet_le measurable_const hS)).inter (measurableSet_le measurable_const hD))

/-! ### Assembly -/


end Census
end IIT
