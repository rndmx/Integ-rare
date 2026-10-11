/-
Census, B1 new leaf: `x5e` (effect side, anchor `s^x`), read as `GoodXFail` reads it (on `b1Ext` of the sensitive
rows), for subcubes `|K'| ≤ 2` (**`joint_x5e2`**).

For `|K'| ≤ 2`, `x ∉ K'`, the subcube rows around `t = s^x` other than `t` are at distance `≤ 3` from `s`:
* `|K'| = 1`: the single row `t^a` is in `ballR s 2 ⊆ sensRows`: the `plusFail` event with `k = 1`;
* `|K'| = 2`: the rows `t^a, t^b` are in `ballR s 2`, the third reads `≤ 1`, so `2 meanPlus ≤ (2 + y_a + y_b)/2`:
  the `plus2Fail` event on `{t^a, t^b}`.
Both read rows other than `r0, s, s^x`, hence are independent of `RegEvX`; rate `1.0072 + 1/32`.

The stated field (`|K'| ≤ 3`) is NOT covered: for `|K'| = 3` four of the seven rows are outside `sensRows` and read
`1` (`2 meanPlus = (5 + y_a + y_b + y_c)/4`, log-mean `0.4826 > 0.46`), see B1NewLeaf.
-/
import IIT.Census.B1NewLeaf

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- The corrected `x5e` field (`|K'| ≤ 2`), as `GoodXFail` reads it. -/
def P0X5eExt2 (N : ℕ) (s : State N) : State N → Param N → Fin N → XSide → Prop := fun r0 w x σ =>
  σ = .effect → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 2 → x ∉ K' →
    ∑ i, Real.log (max (2 * b1CutMeanPlus (b1Ext (restrIn (sensRows s r0) w)) (flipAt x s) K' i) 1) ≤
      23 / 50 * (N : ℝ)

lemma x5e_ext_eq {s r0 : State N} (w : Param N) {r : State N} (hr : r ∈ sensRows s r0) :
    b1Ext (restrIn (sensRows s r0) w) r = w r := by
  rw [← b1Restr_eq_restrIn]; exact b1_Ext_Restr s r0 w r hr

lemma x5e_ham_s {s : State N} {x : Fin N} {K' : Finset (Fin N)} {r : State N}
    (hr : r ∈ agree K'ᶜ (flipAt x s)) : ham r s ≤ K'.card + 1 := by
  have t1 := ham_triangle r (flipAt x s) s
  have t2 := ham_le_card_of_mem_agree hr
  have t3 := ham_flipAt_le_one x s
  omega

lemma x5e_mem_sens {s r0 r : State N} (h : ham r s ≤ 2) : r ∈ sensRows s r0 := by
  refine Finset.mem_union_right _ ?_
  simp only [ballR, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [ham_comm]; exact h

lemma x5e_flip_mem {t : State N} {K' : Finset (Fin N)} {a : Fin N} (ha : a ∈ K') :
    flipAt a t ∈ (agree K'ᶜ t).erase t := by
  refine mem_erase.2 ⟨flipAt_ne a t, ?_⟩
  rw [mem_agree]; intro j hj
  have : j ≠ a := fun h => (mem_compl.1 hj) (h ▸ ha)
  simp [flipAt, Function.update_of_ne this]

/-- **Joint bound for the corrected `x5e` field, PROVED.** -/
theorem joint_x5e2 : JointBound P0X5eExt2 := by
  filter_upwards [joint_plus_absorb9, eventually_ge_atTop 15] with N hab hN s r0 x σ hfar
  cases σ with
  | cause =>
    have : {w : Param N | RegEvX N s r0 x .cause w ∧ ¬ P0X5eExt2 N s r0 w x .cause} = ∅ := by
      ext w; simp [P0X5eExt2]
    rw [this, measure_empty]; exact bot_le
  | effect =>
    set t := flipAt x s with ht
    set B := 61 * (Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N) with hB
    have hB0 : 0 ≤ B := by positivity
    set E := Real.exp (-(N : ℝ) / 32) with hE
    set Ka := (subs3 N).filter fun K' => K'.card = 1 ∧ x ∉ K' with hKa
    set Kc := (subs3 N).filter fun K' => K'.card = 2 ∧ x ∉ K' with hKc
    set G : Finset (Fin N) → Finset (State N) := fun K' => K'.image fun a => flipAt a t with hG
    have hGcard : ∀ K' : Finset (Fin N), (G K').card = K'.card := by
      intro K'
      refine card_image_of_injOn fun a _ b _ hab' => ?_
      by_contra hne
      exact fs_flip_ne (Ne.symm hne) t hab'
    have hGsub : ∀ K', G K' ⊆ (agree K'ᶜ t).erase t := by
      intro K' r hr
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hr
      exact x5e_flip_mem ha
    have hfar5 : 5 ≤ ham r0 s := by omega
    have hsub : {w : Param N | RegEvX N s r0 x .effect w ∧ ¬ P0X5eExt2 N s r0 w x .effect} ⊆
        (⋃ K' ∈ Ka, {w | RegEvX N s r0 x .effect w} ∩
          plusFail N ((agree K'ᶜ ((fun _ => t) K')).erase ((fun _ => t) K')) K'.card) ∪
        (⋃ K' ∈ Kc, {w | RegEvX N s r0 x .effect w} ∩ plus2Fail N (G K')) := by
      rintro w ⟨hreg, hn⟩
      simp only [P0X5eExt2, forall_const, not_forall, not_le, exists_prop] at hn
      obtain ⟨K', hne, hc, hxK, hlt⟩ := hn
      rw [← ht] at hlt
      have hK1 : 1 ≤ K'.card := hne.card_pos
      have hagr : ∀ r ∈ agree K'ᶜ t, ham r s ≤ 3 := fun r hr => by
        have := x5e_ham_s hr; omega
      rcases Nat.lt_or_ge K'.card 2 with h1 | h2
      · -- |K'| = 1
        left
        simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
        refine ⟨K', ?_, hreg, ?_⟩
        · simp only [hKa, subs3, mem_filter, mem_univ, true_and]; exact ⟨⟨hK1, by omega⟩, by omega, hxK⟩
        · have hcongr : ∀ i, b1CutMeanPlus (b1Ext (restrIn (sensRows s r0) w)) t K' i =
              b1CutMeanPlus w t K' i := fun i =>
            b1CutMeanPlus_congr (fun r hr => x5e_ext_eq w (x5e_mem_sens (by have := x5e_ham_s hr; omega))) i
          simp only [hcongr] at hlt
          simp only [plusFail, Set.mem_setOf_eq]
          have e2 : ∀ i, 2 * b1CutMeanPlus w t K' i =
              2 * (1 + ∑ r ∈ (agree K'ᶜ t).erase t, clamp01 (w r i)) / 2 ^ K'.card :=
            fun i => by unfold b1CutMeanPlus; ring
          simp only [e2] at hlt
          exact hlt
      · -- |K'| = 2
        right
        have hc2 : K'.card = 2 := by omega
        simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
        refine ⟨K', ?_, hreg, ?_⟩
        · simp only [hKc, subs3, mem_filter, mem_univ, true_and]; exact ⟨⟨hK1, by omega⟩, hc2, hxK⟩
        simp only [plus2Fail, Set.mem_setOf_eq]
        refine lt_of_lt_of_le hlt (Finset.sum_le_sum fun i _ => ?_)
        refine Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _)) (max_le_max ?_ le_rfl)
        -- 2 meanPlus ≤ (2 + Σ_G y)/2
        set F' := (agree K'ᶜ t).erase t with hF'
        have hF'card : F'.card = 3 := by rw [hF', card_agree_erase, hc2]; norm_num
        set v : State N → ℝ := fun r => clamp01 (b1Ext (restrIn (sensRows s r0) w) r i) with hv
        have hGsens : ∀ r ∈ G K', v r = clamp01 (w r i) := by
          intro r hr
          obtain ⟨a, ha, rfl⟩ := mem_image.1 hr
          have h1 : ham (flipAt a t) t ≤ 1 := ham_flipAt_le_one a t
          have h2 : ham t s ≤ 1 := ham_flipAt_le_one x s
          have h3 := ham_triangle (flipAt a t) t s
          simp only [hv]; rw [x5e_ext_eq w (x5e_mem_sens (by omega))]
        have hsplit := Finset.sum_sdiff (f := v) (hGsub K')
        have hrest : ∑ r ∈ F' \ G K', v r ≤ 1 := by
          have hcd : (F' \ G K').card = 1 := by
            rw [card_sdiff_of_subset (hGsub K'), hF'card, hGcard, hc2]
          calc ∑ r ∈ F' \ G K', v r ≤ ∑ _r ∈ F' \ G K', (1 : ℝ) :=
                Finset.sum_le_sum fun r _ => clamp01_le_one _
            _ = 1 := by rw [sum_const, hcd]; simp
        have hGv : ∑ r ∈ G K', v r = ∑ r ∈ G K', clamp01 (w r i) := Finset.sum_congr rfl hGsens
        have hmean : 2 * b1CutMeanPlus (b1Ext (restrIn (sensRows s r0) w)) t K' i =
            2 * (1 + ∑ r ∈ F', v r) / 4 := by
          unfold b1CutMeanPlus; rw [hc2]; simp only [hF', hv]; ring
        rw [hmean]
        have : ∑ r ∈ F', v r ≤ 1 + ∑ r ∈ G K', clamp01 (w r i) := by linarith
        linarith
    have hAp : cubeM N (⋃ K' ∈ Ka, {w | RegEvX N s r0 x .effect w} ∩
        plusFail N ((agree K'ᶜ ((fun _ => t) K')).erase ((fun _ => t) K')) K'.card) ≤
        ENNReal.ofReal (Ka.card * (B * E)) := by
      refine (joint_plus (by omega) s r0 x .effect hfar Ka (fun _ => t)
        (fun K' hK' => by simp only [hKa, subs3, mem_filter, mem_univ, true_and] at hK'; exact hK'.1) ?_).trans
        (le_of_eq (by rw [hB, hE]))
      intro K' hK'
      simp only [hKa, subs3, mem_filter, mem_univ, true_and] at hK'
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · have := x5e_ham_s (mem_erase.1 h).2; omega
      · have h1 := (mem_erase.1 h).2
        rw [mem_agree] at h1
        have := h1 x (by simpa using hK'.2.2)
        simp [ht, flipAt] at this
      · simp only [spRow] at h; exact (mem_erase.1 h).1 rfl
    have hCp : cubeM N (⋃ K' ∈ Kc, {w | RegEvX N s r0 x .effect w} ∩ plus2Fail N (G K')) ≤
        ENNReal.ofReal (Kc.card * (B * E)) := by
      calc cubeM N (⋃ K' ∈ Kc, {w | RegEvX N s r0 x .effect w} ∩ plus2Fail N (G K'))
          ≤ ∑ K' ∈ Kc, cubeM N ({w | RegEvX N s r0 x .effect w} ∩ plus2Fail N (G K')) :=
            measure_biUnion_finset_le _ _
        _ ≤ ∑ _K' ∈ Kc, ENNReal.ofReal (B * E) := by
            refine sum_le_sum fun K' hK' => ?_
            simp only [hKc, subs3, mem_filter, mem_univ, true_and] at hK'
            obtain ⟨-, hc2, hxK⟩ := hK'
            rw [cubeM_inter_indep (G K') _ _ ?_ ?_]
            · rw [ENNReal.ofReal_mul hB0]
              exact mul_le_mul' (regEvX_far_le (by omega) s r0 x .effect hfar)
                (plus2Fail_le _ (by rw [hGcard, hc2]))
            · intro w w' hq hw
              have hr0 : r0 ∉ G K' := fun h => by
                have := x5e_ham_s ((mem_erase.1 (hGsub K' h)).2); omega
              have hs' : s ∉ G K' := fun h => by
                have h1 := (mem_erase.1 (hGsub K' h)).2
                rw [mem_agree] at h1
                have := h1 x (by simpa using hxK)
                simp [ht, flipAt] at this
              have hsp : spRow s r0 x .effect ∉ G K' := by
                simp only [spRow]; exact fun h => (mem_erase.1 (hGsub K' h)).1 rfl
              exact (regEvX_congr (hq r0 hr0) (hq s hs') (hq _ hsp)).1 hw
            · intro w w' hq hw; exact plus2Fail_congr hq hw
        _ = ENNReal.ofReal (Kc.card * (B * E)) := by
            rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ((add_le_add hAp hCp).trans ?_))
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hKa' : (Ka.card : ℝ) ≤ 3 * ((N : ℝ) + 1) ^ 3 := (Nat.cast_le.2 (card_filter_le _ _)).trans card_subs3
    have hKc' : (Kc.card : ℝ) ≤ 3 * ((N : ℝ) + 1) ^ 3 := (Nat.cast_le.2 (card_filter_le _ _)).trans card_subs3
    have hBE : 0 ≤ B * E := by positivity
    have h9 : 9 * ((N : ℝ) + 1) ^ 3 * (B * E) ≤ Real.exp (-(RJ * N)) / 2 ^ N := by
      simpa [hB, hE, mul_assoc] using hab
    have hN3 : 0 ≤ ((N : ℝ) + 1) ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hKa' hBE, mul_le_mul_of_nonneg_right hKc' hBE]

end Census
end IIT

#print axioms IIT.Census.joint_x5e2
