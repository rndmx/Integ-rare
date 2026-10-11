/-
Census, B1 forced leaf 18 (`failOnly`, agent "forcedF"): assembly.

`P0FailOnly` is the field `fFailOnly` with an explicit anchor row.  For far `r0`, the joint event
`RegEvX(x, σ) ∧ ¬ P0FailOnly` is covered by the pairs `CellEvX(x, σ, c) ∩ CellEvX(x', σ', c')`, `x' ≠ x`; each pair is
bounded by `TFB N` (`tf_cc`, `tf_ee`, `tf_mixed`; non-overlapping same-side cells are disjoint), and
`2 N 61² TFB N ≤ e^{-RJ N}/2^N` eventually.  With leaf 8 at `RfF2` (`leafF8`) this gives leaf 18.
-/
import IIT.Census.B1ForcedFTwoPair

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- The field `failOnly` with an explicit anchor row (definitionally `fFailOnly` at `r0 = tcRow w`). -/
def P0FailOnly (N : ℕ) (s : State N) : State N → Param N → Fin N → XSide → Prop := fun r0 w x _ =>
  ∀ x' : Fin N, x' ≠ x → SingleNotFail w s r0 x'

lemma fs_ham_self (r : State N) : ham r r = 0 := by simp [ham]

/-- Far rows: the four rows of a two-failure pair are distinct. -/
lemma tf_far_ne {s r0 : State N} (hN : 9 ≤ N) (hfar : N ≤ 3 * ham r0 s) (x x' : Fin N) :
    flipAt x r0 ≠ flipAt x' s := by
  intro h
  have t1 := ham_triangle r0 (flipAt x r0) s
  have t2 := ham_triangle (flipAt x r0) (flipAt x' s) s
  have h1 : ham r0 (flipAt x r0) ≤ 1 := by rw [ham_comm]; exact ham_flipAt_le_one x r0
  have h2 := ham_flipAt_le_one x' s
  rw [h, fs_ham_self] at t2
  have : ham (flipAt x r0) s ≤ 1 := by rw [h]; exact h2
  omega

lemma tf_far_ne0 {s r0 : State N} (hN : 9 ≤ N) (hfar : N ≤ 3 * ham r0 s) (x : Fin N) :
    r0 ≠ flipAt x s := by
  intro h
  have h2 := ham_flipAt_le_one x s
  rw [← h] at h2
  omega

lemma tf_far_ne1 {s r0 : State N} (hN : 9 ≤ N) (hfar : N ≤ 3 * ham r0 s) (x : Fin N) :
    flipAt x r0 ≠ s := by
  intro h
  have h2 := ham_flipAt_le_one x r0
  rw [h, ham_comm] at h2
  omega

lemma tf_far_ne2 {s r0 : State N} (hN : 9 ≤ N) (hfar : N ≤ 3 * ham r0 s) : r0 ≠ s := by
  intro h; rw [h, fs_ham_self] at hfar; omega

/-- Disjoint same-side cells. -/
lemma tf_disj {s r0 : State N} {x x' : Fin N} {σ : XSide} {c c' : ℚ × ℚ} (h : c.2 < c'.1) :
    ({w | CellEvX N s r0 x σ c w} ∩ {w | CellEvX N s r0 x' σ c' w} : Set (Param N)) = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨-, ⟨j, hj⟩, -⟩ ⟨hm, -⟩
  have h1 := hm j
  have hq : ((c.2 : ℚ) : ℝ) < ((c'.1 : ℚ) : ℝ) := by exact_mod_cast h
  have e : baseE w s r0 x' σ j = baseE w s r0 x σ j := by cases σ <;> rfl
  rw [e] at h1
  linarith

/-- **One pair of cells** (any sides), far `r0`, `x ≠ x'`. -/
theorem tf_pair (hN : 9 ≤ N) (hδ : deltaU N < 1 / 2) (s r0 : State N) (hfar : N ≤ 3 * ham r0 s)
    (x x' : Fin N) (hxx : x ≠ x') (σ σ' : XSide) {c c' : ℚ × ℚ} (hc : c ∈ cellsX σ) (hc' : c' ∈ cellsX σ') :
    cubeM N ({w | CellEvX N s r0 x σ c w} ∩ {w | CellEvX N s r0 x' σ' c' w}) ≤ ENNReal.ofReal (TFB N) := by
  have hN2 : 2 ≤ N := by omega
  have h0 := tf_far_ne2 hN hfar
  cases σ <;> cases σ'
  · have hcl : c ∈ cellsXCauseData := List.mem_toFinset.1 hc
    have hcl' : c' ∈ cellsXCauseData := List.mem_toFinset.1 hc'
    by_cases hov : c.2 < c'.1
    · rw [tf_disj hov]; simp
    by_cases hov' : c'.2 < c.1
    · rw [Set.inter_comm, tf_disj hov']; simp
    exact tf_cc hN2 s r0 x x' hxx hcl hcl' hov hov' h0 (tf_far_ne1 hN hfar x) (tf_far_ne1 hN hfar x')
  · exact tf_mixed hN2 hδ s r0 x x' (List.mem_toFinset.1 hc) (List.mem_toFinset.1 hc') h0
      (tf_far_ne0 hN hfar x') (tf_far_ne1 hN hfar x) (tf_far_ne hN hfar x x')
  · rw [Set.inter_comm]
    exact tf_mixed hN2 hδ s r0 x' x (List.mem_toFinset.1 hc') (List.mem_toFinset.1 hc) h0
      (tf_far_ne0 hN hfar x) (tf_far_ne1 hN hfar x') (tf_far_ne hN hfar x' x)
  · have hcl : c ∈ cellsXEffectData := List.mem_toFinset.1 hc
    have hcl' : c' ∈ cellsXEffectData := List.mem_toFinset.1 hc'
    by_cases hov : c.2 < c'.1
    · rw [tf_disj hov]; simp
    by_cases hov' : c'.2 < c.1
    · rw [Set.inter_comm, tf_disj hov']; simp
    exact tf_ee hN2 hδ s r0 x x' hxx hcl hcl' hov hov' h0 (tf_far_ne0 hN hfar x) (tf_far_ne0 hN hfar x')

lemma tf_cells_card (σ : XSide) : (cellsX σ).card ≤ 61 := by
  cases σ
  · have : cellsXCauseData.toFinset.card ≤ cellsXCauseData.length := List.toFinset_card_le _
    have hlen : cellsXCauseData.length = 61 := by decide
    simp only [cellsX]; omega
  · have : cellsXEffectData.toFinset.card ≤ cellsXEffectData.length := List.toFinset_card_le _
    have hlen : cellsXEffectData.length = 61 := by decide
    simp only [cellsX]; omega

/-- The slack of `TFB` is `O(log N)`. -/
lemma tf_slack_le (N : ℕ) : 30 * slT N + 40 * (8 + slV N) + 10 ≤ 20000 + 5000 * Real.log N := by
  have hl : (Nat.log 2 N : ℝ) ≤ 2 * Real.log N := by
    have h1 := Real.natLog_le_logb N 2
    push_cast at h1
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have h2 : Real.logb 2 N ≤ 2 * Real.log N := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
      have := Real.log_two_gt_d9
      nlinarith
    linarith
  unfold slT slV D0U; push_cast
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  nlinarith

/-- **Absorption**: `2 · 61² · N · TFB N ≤ e^{-RJ N} / 2^N` eventually. -/
theorem tf_absorb : ∀ᶠ N : ℕ in atTop, 7442 * (N : ℝ) * TFB N ≤ Real.exp (-(RJ * N)) / 2 ^ N := by
  have hlo := Real.isLittleO_log_id_atTop
  have hev : ∀ᶠ x : ℝ in atTop, Real.log 7442 + 20000 + 5001 * Real.log x ≤ x / 100 := by
    have h1 := hlo.def (c := 1 / 1001000) (by norm_num)
    filter_upwards [h1, eventually_ge_atTop (200 * (Real.log 7442 + 20000)), eventually_ge_atTop 1]
      with x hx hx1 hx2
    simp only [Real.norm_eq_abs, id] at hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx2
    rw [abs_of_nonneg hlog, abs_of_nonneg (by linarith)] at hx
    have : 0 ≤ Real.log 7442 := Real.log_nonneg (by norm_num)
    nlinarith
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hev, eventually_ge_atTop 1] with N hN hN1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hsl := tf_slack_le N
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  unfold TFB
  rw [mul_div_assoc', div_le_div_iff_of_pos_right h2N]
  have hCN : 7442 * (N : ℝ) = Real.exp (Real.log 7442 + Real.log N) := by
    rw [Real.exp_add, Real.exp_log (by norm_num), Real.exp_log (by linarith)]
  rw [hCN]
  calc Real.exp (Real.log 7442 + Real.log N) *
        (Real.exp (-((103 / 100 : ℝ) * N)) * Real.exp (30 * slT N + 40 * (8 + slV N) + 10))
      ≤ Real.exp (Real.log 7442 + Real.log N) *
        (Real.exp (-((103 / 100 : ℝ) * N)) * Real.exp (20000 + 5000 * Real.log N)) := by gcongr
    _ = Real.exp (Real.log 7442 + 20000 + 5001 * Real.log N - (103 / 100 : ℝ) * N) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(RJ * N)) := by
        apply Real.exp_le_exp.2; unfold RJ; linarith

/-- **The joint bound of `failOnly`** (per far `(r0, x, σ)`, rate `RJ`). -/
theorem joint_failOnly : ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide), N ≤ 3 * ham r0 s →
    cubeM N {w | RegEvX N s r0 x σ w ∧ ¬ P0FailOnly N s r0 w x σ} ≤
      ENNReal.ofReal (Real.exp (-(RJ * N)) / 2 ^ N) := by
  filter_upwards [tf_absorb, eventually_ge_atTop 9] with N hab hN s r0 x σ hfar
  have hδ : deltaU N < 1 / 2 := by
    unfold deltaU; rw [div_lt_iff₀ (by positivity)]; have : (9 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set B := TFB N with hB
  have hB0 : 0 ≤ B := TFB_nonneg N
  have hsub : {w | RegEvX N s r0 x σ w ∧ ¬ P0FailOnly N s r0 w x σ} ⊆
      ⋃ x' ∈ (univ.erase x : Finset (Fin N)), ⋃ σ' : XSide, ⋃ c ∈ cellsX σ, ⋃ c' ∈ cellsX σ',
        ({w | CellEvX N s r0 x σ c w} ∩ {w | CellEvX N s r0 x' σ' c' w}) := by
    rintro w ⟨⟨c, hc, hcw⟩, hn⟩
    simp only [P0FailOnly, SingleNotFail, not_forall, not_and_or, not_not] at hn
    obtain ⟨x', hx', h'⟩ := hn
    simp only [Set.mem_iUnion, Finset.mem_erase, Finset.mem_univ, and_true]
    rcases h' with ⟨c', hc', hcw'⟩ | ⟨c', hc', hcw'⟩
    · exact ⟨x', hx', .cause, c, hc, c', hc', hcw, hcw'⟩
    · exact ⟨x', hx', .effect, c, hc, c', hc', hcw, hcw'⟩
  refine (measure_mono hsub).trans ?_
  calc cubeM N (⋃ x' ∈ (univ.erase x : Finset (Fin N)), ⋃ σ' : XSide, ⋃ c ∈ cellsX σ, ⋃ c' ∈ cellsX σ',
        ({w | CellEvX N s r0 x σ c w} ∩ {w | CellEvX N s r0 x' σ' c' w}))
      ≤ ∑ x' ∈ (univ.erase x : Finset (Fin N)), ∑ σ' : XSide, ∑ c ∈ cellsX σ, ∑ c' ∈ cellsX σ',
          ENNReal.ofReal B := by
        refine (measure_biUnion_finset_le _ _).trans (sum_le_sum fun x' hx' => ?_)
        refine (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun σ' _ => ?_)
        refine (measure_biUnion_finset_le _ _).trans (sum_le_sum fun c hc => ?_)
        refine (measure_biUnion_finset_le _ _).trans (sum_le_sum fun c' hc' => ?_)
        exact tf_pair hN hδ s r0 hfar x x' (Finset.ne_of_mem_erase hx').symm σ σ' hc hc'
    _ ≤ ∑ _x' : Fin N, ∑ _σ' : XSide, (61 : ENNReal) * ((61 : ENNReal) * ENNReal.ofReal B) := by
        refine (sum_le_sum_of_subset (erase_subset _ _)).trans (sum_le_sum fun x' _ => sum_le_sum fun σ' _ => ?_)
        calc ∑ c ∈ cellsX σ, ∑ c' ∈ cellsX σ', ENNReal.ofReal B
            = ((cellsX σ).card : ENNReal) * (((cellsX σ').card : ENNReal) * ENNReal.ofReal B) := by
              simp only [sum_const, nsmul_eq_mul]
          _ ≤ _ := by
              gcongr
              · exact_mod_cast tf_cells_card σ
              · exact_mod_cast tf_cells_card σ'
    _ = ENNReal.ofReal (7442 * (N : ℝ) * B) := by
        rw [sum_const, sum_const, card_univ, card_univ, Fintype.card_fin,
          show Fintype.card XSide = 2 from rfl, nsmul_eq_mul, nsmul_eq_mul]
        rw [show (7442 : ℝ) * N * B = (N : ℝ) * (2 * (61 * (61 * B))) by ring,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
        simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal hab

/-- **Leaf 18 (`failOnly`), PROVED** (with leaf 8 at `RfF2`, `leafF8`). -/
theorem leafF18 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (forcedBad N s 18) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [leaf_of_farSplit P0FailOnly leafF8 (farPart_of_joint P0FailOnly joint_failOnly)] with N h s
  exact h s

end Census
end IIT

#print axioms IIT.Census.leafF18
