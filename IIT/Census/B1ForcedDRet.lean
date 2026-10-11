/-
Census, B1 forced leaf 9 (`fRet`, retention) of `B1ForcedSkel`, agent "forcedD".

The field fails at `(r0, x, σ)` when some sensitive row `r ∉ {r0, r0^x}` keeps
`X_{U \ K}(r) ≤ X(r0) + N/400 ≤ x0 N + slT + N/400` after removing `|K| ≤ dX = ⌈N/30⌉` units. Then at most
`m = ⌊(x0 N + slT + N/400)/ln 2⌋ + dX ≈ 0.33 N` entries of row `r` lie below `1/2`
(each costs `> ln 2`).

The argument is an **orientation symmetry** (no certificate): reflecting the entries `y ↦ 1 - y` of the rows
`Q = {r, s, s^x}` at a set `F` of columns is measure preserving, keeps the regime event `RegEvX(s, r0, x, σ)`
(row `s` enters only through `x_k = max(y, 1-y)` and, on the effect side, through `pTe(s^x)`, which is invariant
when `s` and `s^x` are reflected together; `r0, r0^x ∉ Q` by `far`), and toggles the below-half pattern of `r` on
`F`. So given the regime event the pattern is uniform, and
`P(RegEvX ∧ #{y_r < 1/2} ≤ m) ≤ 2^m (3/4)^N P(RegEvX)`, i.e. a gain `e^{-N/50}` over the regime rate 1.0072.

PROVED here (sorry-free): `dr_equidist` (abstract), `dr_refl_mp`, `dr_regEvX_refl`, `joint_ret`, and
`leaf9_of_far` (leaf 9 at rate `RfF`, modulo leaf 8 `far` at `RfF2`, exactly like leaves 11-21).
-/
import IIT.Census.B1ForcedB1

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-! ### 1. The abstract equidistribution lemma -/

theorem dr_equidist {X ι : Type*} [MeasurableSpace X] [Fintype ι] [DecidableEq ι] (μ : Measure X)
    (E H : Set X) (P : X → Finset ι) (g : Finset ι → X → X)
    (hE : MeasurableSet E) (hH : MeasurableSet H) (hP : ∀ A, MeasurableSet {x | P x = A})
    (hg : ∀ F, MeasurePreserving (g F) μ μ) (hinv : ∀ F x, g F (g F x) = x)
    (hgH : ∀ F x, x ∈ H → g F x ∈ H) (hgE : ∀ F x, x ∈ H → (g F x ∈ E ↔ x ∈ E))
    (hgP : ∀ F x, x ∈ H → P (g F x) = symmDiff (P x) F) (hnull : μ Hᶜ = 0) (m : ℕ) :
    μ (E ∩ {x | (P x).card ≤ m}) * 2 ^ Fintype.card ι ≤
      ((univ.filter fun A : Finset ι => A.card ≤ m).card : ENNReal) * μ E := by
  set c := μ (E ∩ H ∩ {x | P x = ∅}) with hc
  have hmeasA : ∀ A, MeasurableSet (E ∩ H ∩ {x | P x = A}) := fun A => (hE.inter hH).inter (hP A)
  -- every pattern has the same mass
  have hconst : ∀ A, μ (E ∩ H ∩ {x | P x = A}) = c := by
    intro A
    have hpre : g A ⁻¹' (E ∩ H ∩ {x | P x = ∅}) = E ∩ H ∩ {x | P x = A} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        have hx : x ∈ H := by have := hgH A _ h2; rwa [hinv] at this
        refine ⟨⟨(hgE A x hx).1 h1, hx⟩, ?_⟩
        rw [hgP A x hx] at h3
        exact symmDiff_eq_bot.1 h3
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨(hgE A x h2).2 h1, hgH A x h2⟩, ?_⟩
        rw [hgP A x h2, h3]; exact symmDiff_self _
    rw [← hpre, (hg A).measure_preimage (hmeasA ∅).nullMeasurableSet]
  -- the total mass
  have hdisj : ∀ (S : Finset (Finset ι)), Set.PairwiseDisjoint (↑S) fun A => E ∩ H ∩ {x | P x = A} := by
    intro S A _ B _ hAB
    refine Set.disjoint_left.2 fun x hx hy => hAB ?_
    exact hx.2.symm.trans hy.2
  have htot : μ (E ∩ H) = 2 ^ Fintype.card ι * c := by
    have hU : E ∩ H = ⋃ A ∈ (univ : Finset (Finset ι)), E ∩ H ∩ {x | P x = A} := by
      ext x; simp
    rw [hU, measure_biUnion_finset (hdisj _) (fun A _ => hmeasA A)]
    simp only [hconst, sum_const, card_univ, Fintype.card_finset, nsmul_eq_mul]
    push_cast; ring
  have hsmall : μ (E ∩ {x | (P x).card ≤ m}) ≤
      ((univ.filter fun A : Finset ι => A.card ≤ m).card : ENNReal) * c := by
    have hsub : E ∩ {x | (P x).card ≤ m} ⊆
        (⋃ A ∈ (univ.filter fun A : Finset ι => A.card ≤ m), E ∩ H ∩ {x | P x = A}) ∪ Hᶜ := by
      intro x ⟨hx, hm⟩
      by_cases hxH : x ∈ H
      · left
        simp only [Set.mem_iUnion, mem_filter, mem_univ, true_and, exists_prop]
        exact ⟨P x, hm, ⟨hx, hxH⟩, rfl⟩
      · exact Or.inr hxH
    calc μ (E ∩ {x | (P x).card ≤ m})
        ≤ μ (⋃ A ∈ (univ.filter fun A : Finset ι => A.card ≤ m), E ∩ H ∩ {x | P x = A}) + μ Hᶜ :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ = ∑ A ∈ (univ.filter fun A : Finset ι => A.card ≤ m), μ (E ∩ H ∩ {x | P x = A}) := by
          rw [hnull, add_zero, measure_biUnion_finset (hdisj _) (fun A _ => hmeasA A)]
      _ = _ := by simp only [hconst, sum_const, nsmul_eq_mul]
  calc μ (E ∩ {x | (P x).card ≤ m}) * 2 ^ Fintype.card ι
      ≤ ((univ.filter fun A : Finset ι => A.card ≤ m).card : ENNReal) * c * 2 ^ Fintype.card ι := by
        gcongr
    _ = ((univ.filter fun A : Finset ι => A.card ≤ m).card : ENNReal) * μ (E ∩ H) := by
        rw [htot]; ring
    _ ≤ _ := by gcongr; exact Set.inter_subset_left

/-- The number of small patterns: `#{A ⊆ [n] : |A| ≤ m} ≤ 2^m (3/2)^n`. -/
lemma dr_count_le (n m : ℕ) :
    ((univ.filter fun A : Finset (Fin n) => A.card ≤ m).card : ℝ) ≤ 2 ^ m * (3 / 2 : ℝ) ^ n := by
  have hsum : ∑ A : Finset (Fin n), (1 / 2 : ℝ) ^ A.card * 1 ^ (n - A.card) = (3 / 2 : ℝ) ^ n := by
    have := Finset.sum_pow_mul_eq_add_pow (1 / 2 : ℝ) 1 (univ : Finset (Fin n))
    rw [Finset.powerset_univ, card_univ, Fintype.card_fin] at this
    rw [this]; norm_num
  rw [Finset.card_filter]
  push_cast
  calc ∑ A : Finset (Fin n), (if A.card ≤ m then (1 : ℝ) else 0)
      ≤ ∑ A : Finset (Fin n), 2 ^ m * ((1 / 2 : ℝ) ^ A.card * 1 ^ (n - A.card)) := by
        refine sum_le_sum fun A _ => ?_
        split_ifs with h
        · rw [one_pow, mul_one, one_div_pow, mul_one_div, le_div_iff₀ (by positivity), one_mul]
          exact pow_le_pow_right₀ (by norm_num) h
        · positivity
    _ = 2 ^ m * (3 / 2 : ℝ) ^ n := by rw [← mul_sum, hsum]

/-! ### 2. The reflection of a set of rows on a set of columns -/

/-- Reflect `y ↦ 1 - y` the entries of the rows `Q` in the columns `F`. -/
def drRefl (Q : Finset (State N)) (F : Finset (Fin N)) (w : Param N) : Param N :=
  fun q i => if q ∈ Q ∧ i ∈ F then 1 - w q i else w q i

lemma drRefl_invol (Q : Finset (State N)) (F : Finset (Fin N)) (w : Param N) :
    drRefl Q F (drRefl Q F w) = w := by
  funext q i; unfold drRefl; split_ifs <;> ring

lemma dr_unif_mp : MeasurePreserving (fun u : ℝ => 1 - u) unif unif := by
  have h := (volume.measurePreserving_sub_left (1 : ℝ)).restrict_preimage (s := Set.Icc (0 : ℝ) 1)
    measurableSet_Icc
  have hpre : (fun u : ℝ => 1 - u) ⁻¹' Set.Icc (0 : ℝ) 1 = Set.Icc 0 1 := by
    ext u; simp only [Set.mem_preimage, Set.mem_Icc]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hpre] at h
  exact h

lemma dr_refl_mp (Q : Finset (State N)) (F : Finset (Fin N)) :
    MeasurePreserving (drRefl Q F) (cubeM N) (cubeM N) := by
  have hrow : ∀ q : State N, MeasurePreserving
      (fun v : Fin N → ℝ => fun i => if q ∈ Q ∧ i ∈ F then 1 - v i else v i) (rowM N) (rowM N) := by
    intro q
    refine measurePreserving_pi (fun _ : Fin N => unif) (fun _ : Fin N => unif) (f := fun i u =>
      if q ∈ Q ∧ i ∈ F then 1 - u else u) fun i => ?_
    split_ifs
    · exact dr_unif_mp
    · exact MeasurePreserving.id _
  exact measurePreserving_pi (fun _ : State N => rowM N) (fun _ : State N => rowM N) hrow

/-- Entries of a row equal to a constant: a null event. -/
lemma dr_null_entry (q : State N) (i : Fin N) (c : ℝ) : cubeM N {w | w q i = c} = 0 := by
  have h1 : MeasurePreserving (fun w : Param N => w q) (cubeM N) (rowM N) :=
    measurePreserving_eval (fun _ : State N => rowM N) q
  have h2 : MeasurePreserving (fun v : Fin N → ℝ => v i) (rowM N) unif :=
    measurePreserving_eval (fun _ : Fin N => unif) i
  have h := h2.comp h1
  have : {w : Param N | w q i = c} = ((fun v : Fin N → ℝ => v i) ∘ fun w : Param N => w q) ⁻¹' {c} := rfl
  rw [this, h.measure_preimage (measurableSet_singleton c).nullMeasurableSet]
  unfold unif
  rw [Measure.restrict_apply (measurableSet_singleton c)]
  exact measure_mono_null Set.inter_subset_left (Real.volume_singleton)

/-- The no-half event for the rows `Q`. -/
def drH (Q : Finset (State N)) : Set (Param N) := {w | ∀ q ∈ Q, ∀ i, clamp01 (w q i) ≠ 1 / 2}

lemma dr_clamp_half {u : ℝ} (h : clamp01 u = 1 / 2) : u = 1 / 2 := by
  unfold clamp01 at h
  rcases le_total u 0 with h0 | h0
  · rw [min_eq_right (by linarith : u ≤ 1), max_eq_left h0] at h; norm_num at h
  rcases le_total u 1 with h1 | h1
  · rwa [min_eq_right h1, max_eq_right h0] at h
  · rw [min_eq_left h1, max_eq_right zero_le_one] at h; norm_num at h

lemma dr_H_null (Q : Finset (State N)) : cubeM N (drH Q)ᶜ = 0 := by
  have hsub : (drH Q)ᶜ ⊆ ⋃ q ∈ Q, ⋃ i : Fin N, {w : Param N | w q i = 1 / 2} := by
    intro w hw
    simp only [drH, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_not] at hw
    obtain ⟨q, hq, i, hi⟩ := hw
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    exact ⟨q, hq, i, dr_clamp_half hi⟩
  refine measure_mono_null hsub ?_
  refine (measure_biUnion_null_iff (Q.countable_toSet)).2 fun q _ => ?_
  exact measure_iUnion_null fun i => dr_null_entry q i _

lemma dr_H_meas (Q : Finset (State N)) : MeasurableSet (drH Q) := by
  have : drH Q = ⋂ q ∈ Q, ⋂ i : Fin N, {w : Param N | clamp01 (w q i) ≠ 1 / 2} := by
    ext w; simp [drH]
  rw [this]
  refine Finset.measurableSet_biInter _ fun q _ => MeasurableSet.iInter fun i => ?_
  exact (measurableSet_singleton (1 / 2 : ℝ)).compl.preimage
    (clamp01_measurable.comp ((measurable_pi_apply i).comp (measurable_pi_apply q)))

lemma dr_clamp_refl (u : ℝ) : clamp01 (1 - u) = 1 - clamp01 u := clamp01_one_sub u

lemma dr_H_refl (Q : Finset (State N)) (F : Finset (Fin N)) {w : Param N} (hw : w ∈ drH Q) :
    drRefl Q F w ∈ drH Q := by
  intro q hq i
  unfold drRefl
  split_ifs
  · rw [dr_clamp_refl]; intro h; exact hw q hq i (by linarith)
  · exact hw q hq i

/-- The below-half pattern of row `r`. -/
noncomputable def drPat (r : State N) (w : Param N) : Finset (Fin N) := univ.filter fun i => clamp01 (w r i) < 1 / 2

lemma dr_pat_meas (r : State N) (A : Finset (Fin N)) : MeasurableSet {w : Param N | drPat r w = A} := by
  have : {w : Param N | drPat r w = A} =
      ⋂ i : Fin N, {w : Param N | (clamp01 (w r i) < 1 / 2 ↔ i ∈ A)} := by
    ext w
    simp only [drPat, Set.mem_setOf_eq, Set.mem_iInter, Finset.ext_iff, mem_filter, mem_univ, true_and]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  have hm : MeasurableSet {w : Param N | clamp01 (w r i) < 1 / 2} :=
    measurableSet_lt (clamp01_measurable.comp ((measurable_pi_apply i).comp (measurable_pi_apply r)))
      measurable_const
  by_cases hi : i ∈ A
  · have e : {w : Param N | (clamp01 (w r i) < 1 / 2 ↔ i ∈ A)} = {w | clamp01 (w r i) < 1 / 2} := by
      ext w; simp [hi]
    rw [e]; exact hm
  · have e : {w : Param N | (clamp01 (w r i) < 1 / 2 ↔ i ∈ A)} = {w | clamp01 (w r i) < 1 / 2}ᶜ := by
      ext w; simp [hi]
    rw [e]; exact hm.compl

lemma dr_pat_refl {Q : Finset (State N)} {r : State N} (hr : r ∈ Q) (F : Finset (Fin N)) {w : Param N}
    (hw : w ∈ drH Q) : drPat r (drRefl Q F w) = symmDiff (drPat r w) F := by
  ext i
  rw [Finset.mem_symmDiff]
  simp only [drPat, mem_filter, mem_univ, true_and]
  unfold drRefl
  have h := hw r hr i
  by_cases hi : i ∈ F
  · rw [if_pos ⟨hr, hi⟩, dr_clamp_refl]
    constructor
    · intro h1; right; exact ⟨hi, fun h2 => by linarith⟩
    · rintro (⟨-, h2⟩ | ⟨-, h2⟩)
      · exact absurd hi h2
      · rcases lt_or_gt_of_ne h with h3 | h3
        · exact absurd h3 h2
        · linarith
  · rw [if_neg (fun h' => hi h'.2)]
    constructor
    · intro h1; exact Or.inl ⟨h1, hi⟩
    · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact h1
      · exact absurd h1 hi

/-! ### 3. Invariance of the regime event -/

lemma dr_xE_refl {Q : Finset (State N)} {s : State N} (F : Finset (Fin N)) (w : Param N) (k : Fin N) :
    xE (drRefl Q F w) s k = xE w s k := by
  unfold xE drRefl
  split_ifs
  · rw [dr_clamp_refl, sub_sub_cancel, max_comm]
  · rfl

lemma dr_pTe_refl {Q : Finset (State N)} {s t : State N} (hs : s ∈ Q) (ht : t ∈ Q) (F : Finset (Fin N))
    {w : Param N} (hw : w ∈ drH Q) (k : Fin N) :
    pTe (drRefl Q F w) s t k = pTe w s t k := by
  unfold pTe drRefl
  by_cases hk : k ∈ F
  · simp only [hs, ht, hk, and_self, if_true, dr_clamp_refl]
    have h := hw s hs k
    rcases lt_or_gt_of_ne h with h2 | h2
    · rw [if_pos (by linarith), if_neg (by linarith)]
    · rw [if_neg (by linarith), if_pos h2]; ring
  · simp only [hk, and_false, if_false]

lemma dr_row_refl {Q : Finset (State N)} {q : State N} (hq : q ∉ Q) (F : Finset (Fin N)) (w : Param N) :
    drRefl Q F w q = w q := by
  funext i; unfold drRefl; rw [if_neg (by tauto)]

/-- **The regime event is invariant** under the reflection of `Q ∋ s, s^x` (with `r0, r0^x ∉ Q`), on `drH Q`. -/
theorem dr_regEvX_refl {s r0 : State N} {x : Fin N} {σ : XSide} {Q : Finset (State N)}
    (hs : s ∈ Q) (hsx : flipAt x s ∈ Q) (h0 : r0 ∉ Q) (h1 : flipAt x r0 ∉ Q) (F : Finset (Fin N))
    {w : Param N} (hw : w ∈ drH Q) :
    RegEvX N s r0 x σ (drRefl Q F w) ↔ RegEvX N s r0 x σ w := by
  have e0 := dr_row_refl h0 F w
  have e1 := dr_row_refl h1 F w
  have hx : ∀ k, xE (drRefl Q F w) s k = xE w s k := dr_xE_refl F w
  have hb : ∀ j, baseE (drRefl Q F w) s r0 x σ j = baseE w s r0 x σ j := by
    intro j; cases σ
    · simp only [baseE, e0]
    · simp only [baseE, hx]
  have hc : ∀ j, compE (drRefl Q F w) s r0 x σ j = compE w s r0 x σ j := by
    intro j; cases σ
    · simp only [compE, e1]
    · simp only [compE]; exact dr_pTe_refl hs hsx F hw j
  have hX : XW (drRefl Q F w) r0 = XW w r0 := by unfold XW; rw [e0]
  simp only [RegEvX, CellEvX, lamX, hb, hc, hX, hx, e0]

/-! ### 4. The joint bound for `ret` -/

/-- The retention field with an explicit anchor row. -/
def P0Ret (N : ℕ) (s : State N) : State N → Param N → Fin N → XSide → Prop := fun r0 w x _ =>
  ∀ r ∈ sensRows s r0, r ≠ r0 → r ≠ spRow s r0 x .cause → ∀ K : Finset (Fin N),
    K.card ≤ dX N → XW w r0 + b1Eta * N < XMW w (univ \ K) r

/-- A row that retains too much has few entries below `1/2`. -/
lemma dr_pat_card_le {w : Param N} {r : State N} {K : Finset (Fin N)} {T : ℝ}
    (hpos : ∀ i, 0 < clamp01 (w r i)) (h : XMW w (univ \ K) r ≤ T) : (drPat r w).card ≤ ⌊T / Real.log 2⌋₊ + K.card := by
  have hl2 := b1_log_two_pos
  have hsub : drPat r w ⊆ (drPat r w \ K) ∪ K := by intro i hi; by_cases hK : i ∈ K <;> simp [hi, hK]
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_right ?_ _))
  apply Nat.le_floor
  rw [le_div_iff₀ hl2]
  calc ((drPat r w \ K).card : ℝ) * Real.log 2 = ∑ _i ∈ drPat r w \ K, Real.log 2 := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ drPat r w \ K, -Real.log (clamp01 (w r i)) := by
        refine sum_le_sum fun i hi => ?_
        have hi' : clamp01 (w r i) < 1 / 2 := by
          have := (mem_sdiff.1 hi).1
          simp only [drPat, mem_filter, mem_univ, true_and] at this
          exact this
        have h0 := hpos i
        have : Real.log (clamp01 (w r i)) ≤ Real.log (1 / 2) := Real.log_le_log h0 hi'.le
        rw [one_div, Real.log_inv] at this
        linarith
    _ ≤ ∑ i ∈ univ \ K, -Real.log (clamp01 (w r i)) := by
        refine sum_le_sum_of_subset_of_nonneg (fun i hi => mem_sdiff.2 ⟨mem_univ _, (mem_sdiff.1 hi).2⟩)
          fun i _ _ => b1_neg_log_clamp_nonneg _
    _ ≤ T := h

/-- The far geometry: `r0, r0^x ∉ {s, s^x}`. -/
lemma dr_far_ne (hN7 : 7 ≤ N) {s r0 : State N} (x : Fin N) (hfar : N ≤ 3 * ham r0 s) :
    r0 ≠ s ∧ r0 ≠ flipAt x s ∧ flipAt x r0 ≠ s ∧ flipAt x r0 ≠ flipAt x s := by
  have h3 : 3 ≤ ham r0 s := by omega
  have hs1 : ham (flipAt x s) s ≤ 1 := ham_flipAt_le_one x s
  have hr1 : ham r0 (flipAt x r0) ≤ 1 := by rw [ham_comm]; exact ham_flipAt_le_one x r0
  have t2 := ham_triangle r0 (flipAt x r0) s
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h, ham_self] at h3; omega
  · rw [h] at h3; omega
  · rw [← h] at h3; omega
  · rw [h] at t2 hr1; omega

/-- **Joint bound for `ret`** (per far `(r0, x, σ)`): the regime rate `1.0072` plus the orientation gain `1/50`. -/
theorem joint_ret : ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide), N ≤ 3 * ham r0 s →
    cubeM N {w | RegEvX N s r0 x σ w ∧ ¬ P0Ret N s r0 w x σ} ≤
      ENNReal.ofReal (Real.exp (-(RJ * N)) / 2 ^ N) := by
  have hab := poly_absorb (2 * 61 * Real.exp 21) 6 (δ := (rsR0 : ℝ) + 1 / 50 - RJ) (by unfold RJ rsR0; norm_num)
  filter_upwards [hab, eventually_ge_atTop 7] with N hab hN7 s r0 x σ hfar
  obtain ⟨h0s, h0sx, h1s, h1sx⟩ := dr_far_ne hN7 x hfar
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hl2 := b1_log_two_pos
  set T : ℝ := x0 * N + slT N + b1Eta * N with hT
  set m : ℕ := ⌊T / Real.log 2⌋₊ + dX N with hm
  set Breg : ℝ := 61 * (Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N)
    with hBreg
  set R := (sensRows s r0).filter fun r => r ≠ r0 ∧ r ≠ spRow s r0 x .cause
  have hslT : 0 ≤ slT N := by
    unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    linarith
  have hT0 : 0 ≤ T := by
    have := x0_pos
    have hb : (0 : ℝ) ≤ b1Eta := by unfold b1Eta; norm_num
    rw [hT]; positivity
  -- the cover
  have hsub : {w | RegEvX N s r0 x σ w ∧ ¬ P0Ret N s r0 w x σ} ⊆
      (openCube N)ᶜ ∪ ⋃ r ∈ R, {w | RegEvX N s r0 x σ w} ∩ {w | (drPat r w).card ≤ m} := by
    rintro w ⟨hreg, hP⟩
    by_cases ho : w ∈ openCube N
    · right
      simp only [P0Ret, not_forall, not_lt, exists_prop] at hP
      obtain ⟨r, hr, h1, h2, K, hK, hX⟩ := hP
      have hreg' := hreg
      obtain ⟨c, -, hcell⟩ := hreg'
      have hTt : XW w r0 ≤ x0 * N + slT N := hcell.2.2.1
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
      refine ⟨r, mem_filter.2 ⟨hr, h1, h2⟩, hreg, ?_⟩
      have hpos : ∀ i, 0 < clamp01 (w r i) := fun i => by
        rw [b1_clamp01_of_mem_Ioo (ho r i)]; exact (ho r i).1
      refine (dr_pat_card_le hpos (T := T) (by rw [hT]; linarith)).trans ?_
      rw [hm]; omega
    · exact Or.inl ho
  -- one row `r`
  have hterm : ∀ r ∈ R, cubeM N ({w | RegEvX N s r0 x σ w} ∩ {w | (drPat r w).card ≤ m}) ≤
      ENNReal.ofReal (2 ^ m * (3 / 2 : ℝ) ^ N / 2 ^ N * Breg) := by
    intro r hr
    obtain ⟨_, hr0, hr1⟩ := mem_filter.1 hr
    set Q : Finset (State N) := {r, s, flipAt x s}
    have hrQ : r ∈ Q := by simp [Q]
    have hsQ : s ∈ Q := by simp [Q]
    have hsxQ : flipAt x s ∈ Q := by simp [Q]
    have h0Q : r0 ∉ Q := by
      simp only [Q, mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hr0, h0s, h0sx⟩
    have h1Q : flipAt x r0 ∉ Q := by
      simp only [Q, mem_insert, mem_singleton, not_or]
      exact ⟨fun h => hr1 (by rw [← h]; rfl), h1s, h1sx⟩
    have heq := dr_equidist (cubeM N) {w | RegEvX N s r0 x σ w} (drH Q) (drPat r) (drRefl Q)
      (b1mx_RegEvX N s r0 x σ) (dr_H_meas Q) (dr_pat_meas r) (dr_refl_mp Q) (drRefl_invol Q)
      (fun F w hw => dr_H_refl Q F hw) (fun F w hw => dr_regEvX_refl hsQ hsxQ h0Q h1Q F hw)
      (fun F w hw => dr_pat_refl hrQ F hw) (dr_H_null Q) m
    rw [Fintype.card_fin] at heq
    have hcnt := dr_count_le N m
    have hreg := regEvX_far_le hN7 s r0 x σ hfar
    have h2N : (0 : ENNReal) < 2 ^ N := by positivity
    have h2Nt : (2 : ENNReal) ^ N ≠ ⊤ := by simp
    rw [← ENNReal.le_div_iff_mul_le (Or.inl h2N.ne') (Or.inl h2Nt)] at heq
    refine heq.trans ?_
    have hK : ((univ.filter fun A : Finset (Fin N) => A.card ≤ m).card : ENNReal) ≤
        ENNReal.ofReal (2 ^ m * (3 / 2 : ℝ) ^ N) := by
      rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hcnt
    calc ((univ.filter fun A : Finset (Fin N) => A.card ≤ m).card : ENNReal) *
          cubeM N {w | RegEvX N s r0 x σ w} / 2 ^ N
        ≤ ENNReal.ofReal (2 ^ m * (3 / 2 : ℝ) ^ N) * ENNReal.ofReal Breg / 2 ^ N := by gcongr
      _ = ENNReal.ofReal (2 ^ m * (3 / 2 : ℝ) ^ N / 2 ^ N * Breg) := by
        rw [← ENNReal.ofReal_mul (by positivity), show (2 : ENNReal) ^ N = ENNReal.ofReal (2 ^ N) by
          rw [ENNReal.ofReal_pow (by norm_num)]; simp, ← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1; ring
  -- the per-row factor
  have hdX : (dX N : ℝ) ≤ (N : ℝ) / 30 + 1 := by
    unfold dX
    have h := Nat.div_mul_le_self (N + 29) 30
    have : (((N + 29) / 30 : ℕ) : ℝ) * 30 ≤ N + 29 := by exact_mod_cast h
    linarith
  have hfac : 2 ^ m * (3 / 2 : ℝ) ^ N / 2 ^ N ≤ Real.exp (-(N : ℝ) / 50 + slT N + 1) := by
    have h1 : (2 : ℝ) ^ m ≤ Real.exp (T + (dX N : ℝ) * Real.log 2) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
      apply Real.exp_le_exp.2
      have hfl : (⌊T / Real.log 2⌋₊ : ℝ) ≤ T / Real.log 2 := Nat.floor_le (div_nonneg hT0 hl2.le)
      rw [hm]; push_cast
      rw [le_div_iff₀ hl2] at hfl
      nlinarith
    have h2 : (3 / 2 : ℝ) ^ N / 2 ^ N ≤ Real.exp (-(N : ℝ) / 4) := by
      rw [← div_pow, show (3 / 2 : ℝ) / 2 = 3 / 4 by norm_num]
      have hl : Real.log (3 / 4) ≤ -1 / 4 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 4 by norm_num); linarith
      calc (3 / 4 : ℝ) ^ N = Real.exp (N * Real.log (3 / 4)) := by
            rw [← Real.log_pow, Real.exp_log (by positivity)]
        _ ≤ Real.exp (-(N : ℝ) / 4) := Real.exp_le_exp.2 (by nlinarith)
    have hx0 := x0_lt
    have hl2' := Real.log_two_lt_d9
    calc 2 ^ m * (3 / 2 : ℝ) ^ N / 2 ^ N = 2 ^ m * ((3 / 2 : ℝ) ^ N / 2 ^ N) := by ring
      _ ≤ Real.exp (T + (dX N : ℝ) * Real.log 2) * Real.exp (-(N : ℝ) / 4) := by gcongr
      _ = Real.exp (T + (dX N : ℝ) * Real.log 2 + -(N : ℝ) / 4) := by rw [← Real.exp_add]
      _ ≤ Real.exp (-(N : ℝ) / 50 + slT N + 1) := by
          apply Real.exp_le_exp.2
          rw [hT]; unfold b1Eta
          nlinarith [mul_le_mul_of_nonneg_right hdX hl2.le]
  -- assembly
  have hcard : (R.card : ℝ) ≤ 2 * ((N : ℝ) + 1) ^ 4 := by
    have := (Finset.card_filter_le (sensRows s r0)
      (fun r => r ≠ r0 ∧ r ≠ spRow s r0 x .cause)).trans (card_sensRows_le s r0)
    exact_mod_cast this
  have hBreg0 : 0 ≤ Breg := by positivity
  calc cubeM N {w | RegEvX N s r0 x σ w ∧ ¬ P0Ret N s r0 w x σ}
      ≤ cubeM N (openCube N)ᶜ + cubeM N (⋃ r ∈ R, {w | RegEvX N s r0 x σ w} ∩ {w | (drPat r w).card ≤ m}) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ 0 + ∑ r ∈ R, cubeM N ({w | RegEvX N s r0 x σ w} ∩ {w | (drPat r w).card ≤ m}) := by
        rw [cubeM_compl_openCube]; exact add_le_add le_rfl (measure_biUnion_finset_le _ _)
    _ ≤ 0 + ∑ _r ∈ R, ENNReal.ofReal (2 ^ m * (3 / 2 : ℝ) ^ N / 2 ^ N * Breg) :=
        add_le_add le_rfl (sum_le_sum fun r hr => hterm r hr)
    _ = ENNReal.ofReal (R.card * (2 ^ m * (3 / 2 : ℝ) ^ N / 2 ^ N * Breg)) := by
        rw [zero_add, sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (Real.exp (-(RJ * N)) / 2 ^ N) := by
        apply ENNReal.ofReal_le_ofReal
        have hsl := rs_slack_le N
        have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
        have hslTe : Real.exp (slT N + 1) ≤ Real.exp 21 * ((N : ℝ) + 1) ^ 2 := by
          unfold slT
          rw [show 2 * Real.log N + 20 + 1 = 21 + Real.log ((N : ℝ) ^ 2) by
            rw [Real.log_pow]; push_cast; ring, Real.exp_add, Real.exp_log (by positivity)]
          gcongr; linarith
        have h2N : (0 : ℝ) < 2 ^ N := by positivity
        rw [hBreg]
        have e1 : (R.card : ℝ) * (2 ^ m * (3 / 2 : ℝ) ^ N / 2 ^ N *
            (61 * (Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N))) =
            ((R.card : ℝ) * 61 * (2 ^ m * (3 / 2 : ℝ) ^ N / 2 ^ N) *
              Real.exp (19 * slT N + 17 * (8 + slV N) + 9) * Real.exp (-((rsR0 : ℝ) * N))) / 2 ^ N := by ring
        rw [e1, div_le_div_iff_of_pos_right h2N]
        have hS : Real.exp (19 * slT N + 17 * (8 + slV N) + 9) ≤ Real.exp (4000 + 1400 * Real.log N) :=
          Real.exp_le_exp.2 hsl
        have hf' : 2 ^ m * (3 / 2 : ℝ) ^ N / 2 ^ N ≤
            Real.exp (-(N : ℝ) / 50) * (Real.exp 21 * ((N : ℝ) + 1) ^ 2) := by
          refine hfac.trans ?_
          rw [show -(N : ℝ) / 50 + slT N + 1 = -(N : ℝ) / 50 + (slT N + 1) by ring, Real.exp_add]
          gcongr
        have hA : (R.card : ℝ) * 61 * (2 ^ m * (3 / 2 : ℝ) ^ N / 2 ^ N) *
            Real.exp (19 * slT N + 17 * (8 + slV N) + 9) ≤
            (2 * ((N : ℝ) + 1) ^ 4) * 61 * (Real.exp (-(N : ℝ) / 50) * (Real.exp 21 * ((N : ℝ) + 1) ^ 2)) *
              Real.exp (4000 + 1400 * Real.log N) := by
          gcongr
        have e2 : (2 * ((N : ℝ) + 1) ^ 4) * 61 * (Real.exp (-(N : ℝ) / 50) * (Real.exp 21 * ((N : ℝ) + 1) ^ 2)) *
            Real.exp (4000 + 1400 * Real.log N) =
            (2 * 61 * Real.exp 21 * ((N : ℝ) + 1) ^ 6 * Real.exp (4000 + 1400 * Real.log N)) *
              Real.exp (-(N : ℝ) / 50) := by ring
        have hstep : (R.card : ℝ) * 61 * (2 ^ m * (3 / 2 : ℝ) ^ N / 2 ^ N) *
            Real.exp (19 * slT N + 17 * (8 + slV N) + 9) ≤
            Real.exp (((rsR0 : ℝ) + 1 / 50 - RJ) * N) * Real.exp (-(N : ℝ) / 50) := by
          refine hA.trans ?_
          rw [e2]
          exact mul_le_mul_of_nonneg_right hab (Real.exp_pos _).le
        calc (R.card : ℝ) * 61 * (2 ^ m * (3 / 2 : ℝ) ^ N / 2 ^ N) *
              Real.exp (19 * slT N + 17 * (8 + slV N) + 9) * Real.exp (-((rsR0 : ℝ) * N))
            ≤ Real.exp (((rsR0 : ℝ) + 1 / 50 - RJ) * N) * Real.exp (-(N : ℝ) / 50) *
                Real.exp (-((rsR0 : ℝ) * N)) := mul_le_mul_of_nonneg_right hstep (Real.exp_pos _).le
          _ = Real.exp (-(RJ * N)) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- **Leaf 9 (`ret`)**, proved from leaf 8 (`far`) at rate `RfF2 = 1.0107`. -/
theorem leaf9_of_far
    (h8 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (bField N s (fFar N s)) ≤ ENNReal.ofReal (Real.exp (-(RfF2 * N)))) :
    ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 9) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) :=
  leaf_of_farSplit P0Ret h8 (farPart_of_joint P0Ret joint_ret)

end Census
end IIT
