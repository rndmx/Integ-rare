/-
Census, B1, W14 work package WP5 (part 3): the column flip with fixed rows (W5 Lemma E4') and the sign
(W5 Corollary E4'').

* `coin_flip`: reflecting column `k` maps `Core^{(k)}_K(2κ0) ∩ {f_k < 0}` into `Core^{(k)}_K(0) ∩ {f_k > 0}`
  (the fixed rows of `C_0`, `C_j` lie in `Ball(s, 2)` and number `≤ d²`, so they move `f_k`, `h_j(k)` by `≤ κ0`);
* `w5_sign_ge_half`: `P(Core_K(2κ0)) ≤ 2 P(Sign_K)` (the `Core^{(k)}_K(0)` are disjoint in `k`).

Blueprint: `iit-census/lean/B1-W14-count-lean.md` §10.  No `sorry`.
-/
import IIT.Census.B1CntCoinBase

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### Eventual sizes and signs of the constants -/

lemma w5_ev_sizes : ∀ᶠ N : ℕ in atTop,
    2 ≤ dX N ∧ 3 * dX N + 19 ≤ N ∧ dX N ≤ N ∧ (8 : ℝ) ≤ mX N := by
  filter_upwards [eventually_ge_atTop 1000] with N hN
  have h1 : 2 ≤ dX N := by unfold dX; omega
  have h2 : 3 * dX N + 19 ≤ N := by unfold dX; omega
  have h3 : dX N ≤ N := by unfold dX; omega
  refine ⟨h1, h2, h3, ?_⟩
  unfold mX
  have : 8 ≤ N - dX N := by omega
  exact_mod_cast this

lemma w5_kap0_nonneg (N : ℕ) : 0 ≤ kap0 N := by unfold kap0; positivity

lemma w5_epsN_nonneg (N : ℕ) : 0 ≤ epsN N := by unfold epsN; positivity

lemma w5_kapN_nonneg (N : ℕ) : 0 ≤ kapN N := by
  unfold kapN
  have := Real.log_natCast_nonneg N
  have := w5_kap0_nonneg N
  have := w5_epsN_nonneg N
  positivity

lemma w5_sigC_nonneg (N : ℕ) : 0 ≤ sigC N := Real.sqrt_nonneg _

lemma w5_A0C_nonneg (N : ℕ) : 0 ≤ A0C N := by
  unfold A0C; exact mul_nonneg (w5_sigC_nonneg N) (Real.sqrt_nonneg _)

/-- `CoreAt` decreases in `κ`. -/
lemma w5_coreAt_mono {s : State N} {K : Finset (Fin N)} {k : Fin N} {κ : ℝ} (hκ : 0 ≤ κ)
    {w : Param N} (h : CoreAt N s K k κ w) : CoreAt N s K k 0 w := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by linarith, by linarith, fun k' hk' => by linarith [h3 k' hk'],
    fun j hj => by linarith [h4 j hj]⟩

/-- The `Core^{(k)}_K(0)` are disjoint in `k`. -/
lemma w5_coreAt_disj {s : State N} {K : Finset (Fin N)} {k k' : Fin N} (hkk : k ≠ k')
    {w : Param N} (h : CoreAt N s K k 0 w) (h' : CoreAt N s K k' 0 w) : False := by
  have h1 := h.1
  have h2 := h'.2.2.1 k hkk
  have := w5_kapN_nonneg N
  linarith

/-! ### The split of `f_k`, `h_j(k)` into fixed and fresh parts -/

section Split

variable {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ)

lemma w5_card_M {K : Finset (Fin N)} (hK : K.card = dX N) (hdN : dX N ≤ N) :
    N - (univ \ K).card = dX N := by
  rw [card_univ_sdiff, Fintype.card_fin, hK]; omega

lemma w5_fK_w5G (K : Finset (Fin N)) (c : Fin N) (w : Param N) {d : ℕ}
    (hd : N - (univ \ K).card = d) :
    fK (w5G f w) s K c * 2 ^ d =
      w5fix f (agree (univ \ K) s) c +
        w5S (sensRows s r0) (agree (univ \ K) s) c (w5or f c) w := by
  unfold fK; rw [← hd]; exact effDevA_w5G f w _ s c

lemma w5_hK_w5G (K : Finset (Fin N)) (j c : Fin N) (w : Param N) {d : ℕ}
    (hd : N - (univ \ K).card = d) :
    hK (w5G f w) s K j c * 2 ^ d =
      w5fix f (agree (univ \ K) (flipAt j s)) c +
        w5S (sensRows s r0) (agree (univ \ K) (flipAt j s)) c (w5or f c) w := by
  unfold hK; rw [← hd]; exact effDevA_w5G f w _ _ c

/-- The fixed part of a subcube through `Ball(s,1)` of dimension `d` is `≤ κ0/2` after scaling. -/
lemma w5fix_scaled_le (hfar : N ≤ 3 * ham r0 s) (K : Finset (Fin N)) (t : State N)
    (ht : ham s t ≤ 2) {d : ℕ} (hd : N - (univ \ K).card = d) (hd2 : 2 ≤ d)
    (hD : 3 * d + 19 ≤ N) (c : Fin N) :
    |w5fix f (agree (univ \ K) t) c| / 2 ^ d ≤ (d : ℝ) ^ 2 / 2 ^ d / 2 := by
  have h1 := abs_w5fix_le f (agree (univ \ K) t) c
  have h2 := w5_sens_card_le (r0 := r0) hfar (univ \ K) t ht hd hd2 hD
  have h3 : (((agree (univ \ K) t).filter fun r => r ∈ sensRows s r0).card : ℝ) ≤ (d : ℝ) ^ 2 := by
    exact_mod_cast h2
  have h4 : |w5fix f (agree (univ \ K) t) c| ≤ (d : ℝ) ^ 2 / 2 := by linarith
  calc |w5fix f (agree (univ \ K) t) c| / 2 ^ d ≤ ((d : ℝ) ^ 2 / 2) / 2 ^ d :=
        div_le_div_of_nonneg_right h4 (by positivity)
    _ = _ := by ring

end Split

/-! ### The flip (W5 Lemma E4') -/

/-- **Lemma E4'(c)** in `cubeM` form. -/
theorem w5_flip_cube : ∀ᶠ N in atTop, ∀ (s r0 : State N) (f : sensRows s r0 → Fin N → ℝ)
    (K : Finset (Fin N)) (k : Fin N), K.card = dX N → k ∈ K → N ≤ 3 * ham r0 s →
      cubeM N {w | CoreAt N s K k (2 * kap0 N) (w5G f w) ∧ fK (w5G f w) s K k < 0} ≤
        cubeM N {w | CoreAt N s K k 0 (w5G f w) ∧ 0 < fK (w5G f w) s K k} := by
  filter_upwards [w5_ev_sizes] with N hN s r0 f K k hKc hk hfar
  obtain ⟨hd2, hD, hdN, hm8⟩ := hN
  have hdM := w5_card_M hKc hdN
  set d := dX N with hd
  set a : ℝ := 2 ^ d with ha
  have hapos : 0 < a := by positivity
  have hκ0 : kap0 N = (d : ℝ) ^ 2 / a := by unfold kap0; rw [← hd]
  have hκ0n := w5_kap0_nonneg N
  have hκNn := w5_kapN_nonneg N
  have hA0 := w5_A0C_nonneg N
  -- the target set is measurable
  have hR : MeasurableSet {w : Param N | CoreAt N s K k 0 (w5G f w) ∧ 0 < fK (w5G f w) s K k} :=
    (measurable_w5G f) ((measurableSet_CoreAt s K k 0).inter
      (measurableSet_lt measurable_const (measurable_effDevA s _ s k)))
  rw [← (mp_w5refl k).measure_preimage hR.nullMeasurableSet]
  refine measure_mono fun w hw => ?_
  obtain ⟨hcore, hneg⟩ := hw
  set u := w5G f w
  set u' := w5G f (w5refl k w)
  -- the moves of the coin variables
  have hfk : |fK u' s K k + fK u s K k| ≤ kap0 N := by
    have e1 := w5_fK_w5G f K k w hdM
    have e2 := w5_fK_w5G f K k (w5refl k w) hdM
    rw [w5S_refl_self] at e2
    have hsum : fK u' s K k + fK u s K k = 2 * w5fix f (agree (univ \ K) s) k / a := by
      rw [eq_div_iff hapos.ne']; linarith
    rw [hsum, abs_div, abs_mul, abs_of_pos hapos, abs_two, mul_div_assoc]
    have := w5fix_scaled_le f hfar K s (by simp [ham_self]) hdM hd2 hD k
    rw [hκ0]; linarith
  have hhk : ∀ j ∈ univ \ K, |hK u' s K j k + hK u s K j k| ≤ kap0 N := by
    intro j _
    have e1 := w5_hK_w5G f K j k w hdM
    have e2 := w5_hK_w5G f K j k (w5refl k w) hdM
    rw [w5S_refl_self] at e2
    have hsum : hK u' s K j k + hK u s K j k = 2 * w5fix f (agree (univ \ K) (flipAt j s)) k / a := by
      rw [eq_div_iff hapos.ne']; linarith
    rw [hsum, abs_div, abs_mul, abs_of_pos hapos, abs_two, mul_div_assoc]
    have hj : ham s (flipAt j s) ≤ 2 := by
      have := ham_flipAt_le_one j s; rw [ham_comm] at this; omega
    have := w5fix_scaled_le f hfar K _ hj hdM hd2 hD k
    rw [hκ0]; linarith
  have hc : ∀ c, c ≠ k → fK u' s K c = fK u s K c := by
    intro c hck
    have e1 := w5_fK_w5G f K c w hdM
    have e2 := w5_fK_w5G f K c (w5refl k w) hdM
    rw [w5S_refl_ne _ _ hck] at e2
    have : fK u' s K c * a = fK u s K c * a := by rw [e1, e2]
    exact mul_right_cancel₀ hapos.ne' this
  -- the algebra
  have hm' : 0 ≤ 1 - 2 / mX N ∧ 1 - 2 / mX N ≤ 1 := by
    have : 0 < mX N := by linarith
    constructor
    · rw [sub_nonneg, div_le_one this]; linarith
    · have : 0 ≤ 2 / mX N := by positivity
      linarith
  obtain ⟨hL, hU, hS, hN⟩ := hcore
  have habs : |fK u s K k| = -fK u s K k := abs_of_neg hneg
  rw [habs] at hL hU
  have hf' := (abs_le.1 hfk)
  have hpos : 0 < fK u' s K k := by linarith
  have habs' : |fK u' s K k| = fK u' s K k := abs_of_pos hpos
  show CoreAt N s K k 0 u' ∧ 0 < fK u' s K k
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hpos⟩
  · rw [habs']; linarith
  · rw [habs']; linarith
  · intro k' hk'
    rw [hc k' hk']
    linarith [hS k' hk']
  · intro j hj
    have hNj := hN j hj
    rw [habs] at hNj
    unfold sgnMul at hNj ⊢
    rw [if_neg (not_lt.2 hneg.le)] at hNj
    rw [if_pos hpos, habs']
    have hh := (abs_le.1 (hhk j hj))
    have hmul : (1 - 2 / mX N) * (-fK u s K k) ≤ (1 - 2 / mX N) * fK u' s K k + kap0 N := by
      have : (1 - 2 / mX N) * (-fK u s K k) ≤ (1 - 2 / mX N) * (fK u' s K k + kap0 N) :=
        mul_le_mul_of_nonneg_left (by linarith) hm'.1
      nlinarith [hm'.2]
    linarith

theorem coin_flip : ∀ᶠ N in atTop, ∀ (s r0 : State N) (f : sensRows s r0 → Fin N → ℝ)
    (K : Finset (Fin N)) (k : Fin N), K.card = dX N → k ∈ K → N ≤ 3 * ham r0 s →
      rowsOutM (sensRows s r0) {g | CoreAt N s K k (2 * kap0 N) (glueRows (sensRows s r0) f g) ∧
          fK (glueRows (sensRows s r0) f g) s K k < 0} ≤
        rowsOutM (sensRows s r0) {g | CoreAt N s K k 0 (glueRows (sensRows s r0) f g) ∧
          0 < fK (glueRows (sensRows s r0) f g) s K k} := by
  filter_upwards [w5_flip_cube] with N h s r0 f K k hK hk hfar
  rw [rowsOut_eq_w5G f (fun w => CoreAt N s K k (2 * kap0 N) w ∧ fK w s K k < 0),
    rowsOut_eq_w5G f (fun w => CoreAt N s K k 0 w ∧ 0 < fK w s K k)]
  exact h s r0 f K k hK hk hfar

/-! ### The sign (W5 Corollary E4'') -/

/-- **`P(Core_K(2κ0)) ≤ 2 P(Sign_K)`** in `cubeM` form. -/
theorem w5_sign_ge_half_cube : ∀ᶠ N in atTop, ∀ (s r0 : State N)
    (f : sensRows s r0 → Fin N → ℝ) (K : Finset (Fin N)), K.card = dX N → N ≤ 3 * ham r0 s →
      cubeM N {w | CoreK N s K (2 * kap0 N) (w5G f w)} ≤
        2 * cubeM N {w | SignK N s K (w5G f w)} := by
  filter_upwards [w5_flip_cube] with N hflip s r0 f K hK hfar
  have hκ := w5_kap0_nonneg N
  set P : Fin N → Set (Param N) := fun k => {w | CoreAt N s K k 0 (w5G f w) ∧ 0 < fK (w5G f w) s K k}
    with hP
  have hPm : ∀ k, MeasurableSet (P k) := fun k =>
    (measurable_w5G f) ((measurableSet_CoreAt s K k 0).inter
      (measurableSet_lt measurable_const (measurable_effDevA s _ s k)))
  have h1 : {w | CoreK N s K (2 * kap0 N) (w5G f w)} =
      ⋃ k ∈ K, {w | CoreAt N s K k (2 * kap0 N) (w5G f w)} := by
    ext w; simp [CoreK]
  have h2 : {w | SignK N s K (w5G f w)} = ⋃ k ∈ K, P k := by
    ext w; simp only [SignK, hP, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  have hdisj : (↑K : Set (Fin N)).PairwiseDisjoint P := by
    intro k _ k' _ hkk
    rw [Function.onFun, Set.disjoint_left]
    intro w hw hw'
    exact w5_coreAt_disj hkk hw.1 hw'.1
  rw [h1, h2, measure_biUnion_finset hdisj fun k _ => hPm k, mul_sum]
  refine (measure_biUnion_finset_le K _).trans (sum_le_sum fun k hk => ?_)
  have hsub : {w | CoreAt N s K k (2 * kap0 N) (w5G f w)} ⊆
      {w | CoreAt N s K k (2 * kap0 N) (w5G f w) ∧ fK (w5G f w) s K k < 0} ∪ P k := by
    intro w hw
    rcases lt_or_ge (fK (w5G f w) s K k) 0 with h | h
    · exact Or.inl ⟨hw, h⟩
    · refine Or.inr ⟨w5_coreAt_mono (by linarith) hw, ?_⟩
      have hL := hw.1
      have := w5_kapN_nonneg N
      have := w5_A0C_nonneg N
      rcases h.lt_or_eq with h' | h'
      · exact h'
      · rw [← h', abs_zero] at hL; linarith
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  exact (add_le_add (hflip s r0 f K k hK hk hfar) le_rfl).trans_eq (two_mul _).symm

theorem w5_sign_ge_half : ∀ᶠ N in atTop, ∀ (s r0 : State N)
    (f : sensRows s r0 → Fin N → ℝ) (K : Finset (Fin N)), K.card = dX N → N ≤ 3 * ham r0 s →
      rowsOutM (sensRows s r0) {g | CoreK N s K (2 * kap0 N) (glueRows (sensRows s r0) f g)} ≤
        2 * rowsOutM (sensRows s r0) {g | SignK N s K (glueRows (sensRows s r0) f g)} := by
  filter_upwards [w5_sign_ge_half_cube] with N h s r0 f K hK hfar
  rw [rowsOut_eq_w5G f (fun w => CoreK N s K (2 * kap0 N) w), rowsOut_eq_w5G f (fun w => SignK N s K w)]
  exact h s r0 f K hK hfar

end Census
end IIT

#print axioms IIT.Census.coin_flip
#print axioms IIT.Census.w5_sign_ge_half
