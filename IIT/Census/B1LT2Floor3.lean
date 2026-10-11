/-
Census, B1 lemma LT2, module M4 part 5c: assembly of the variance floor.

* `lt2_q_le`: `P(X_{C₀} ≤ 7N/10) ≤ e^{-0.0257 N}` (Chernoff at `t = 1/4`, `|C₀| ≥ 0.9N`).
* `lt2_floor_det`: pointwise, `Σ_{r ∈ half} f(w r) ≤ Σ_{r ∈ H ∩ half} g² + Σ_{D ∈ 𝒟} S_D(w) + Σ_{ham(s,r) ≤ 6} g²`
  where `𝒟 = {D : 1 ≤ |D| ≤ 4}` and `S_D(w) = Σ_r g(w r)² 1{¬Light(w (r ⊕ D))}`.
-/
import IIT.Census.B1LT2Floor2

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

lemma lt2_card_C0 : (9 / 10 : ℝ) * N ≤ (lt2C0 N).card := by
  have h : (lt2C0 N).card = min N (N - 2 * lt2m N) := by
    unfold lt2C0; exact Fin.card_filter_val_lt
  rw [h, min_eq_right (Nat.sub_le _ _)]
  have h1 : 2 * lt2m N ≤ N := by unfold lt2m; omega
  have h2 : (20 : ℝ) * (lt2m N : ℝ) ≤ N := by
    have : 20 * lt2m N ≤ N := by unfold lt2m; omega
    exact_mod_cast this
  rw [Nat.cast_sub h1]; push_cast; linarith

lemma lt2_log45 : Real.log (4 / 5 : ℝ) ≤ -2231 / 10000 := by
  have hq : Real.log (((4 / 5 : ℚ)) : ℝ) ≤ (((-2231 / 10000 : ℚ)) : ℝ) := crLog_le 0 40 (by decide +kernel)
  push_cast at hq; exact hq

/-- **`P(¬Light) ≤ e^{-0.0257 N}`.** -/
theorem lt2_q_le : ∫ x, lt2hL x ∂rowM N ≤ Real.exp (-(257 / 10000 * (N : ℝ))) := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  set S := {x : Fin N → ℝ | ∑ j ∈ lt2C0 N, -Real.log (clamp01 (x j)) ≤ 7 / 10 * (N : ℝ)}
  have hS : MeasurableSet S := measurableSet_le (Finset.measurable_sum _ fun j _ =>
    (Real.measurable_log.comp (measurable_clamp01.comp (measurable_pi_apply j))).neg) measurable_const
  have e : (fun x => lt2hL (N := N) x) = S.indicator 1 := by
    funext x; unfold lt2hL; by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]; simp only [S, Set.mem_setOf_eq] at hx; rw [if_pos hx]; rfl
    · rw [Set.indicator_of_notMem hx]; simp only [S, Set.mem_setOf_eq] at hx; rw [if_neg hx]
  rw [e, integral_indicator_one hS]
  have h := rowM_negLog_chernoff (N := N) (lt2C0 N) (x := 7 / 10 * N) (t := 1 / 4) (by norm_num)
  have hC := lt2_card_C0 (N := N)
  have hl := lt2_log45
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine (ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le (h.trans (ENNReal.ofReal_le_ofReal ?_)))
  rw [show (1 / (1 + 1 / 4 : ℝ)) = 4 / 5 by norm_num, ← Real.exp_log (show (0 : ℝ) < 4 / 5 by norm_num),
    ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
  nlinarith

lemma lt2_ham_xor (r : State N) (D : Finset (Fin N)) : ham (lt2Xor r D) r = D.card := by
  unfold ham lt2Xor
  congr 1; ext j
  simp only [mem_filter, mem_univ, true_and]
  split_ifs with h <;> simp [h]

/-- The shifts of size `1..4`. -/
def lt2Dset (N : ℕ) : Finset (Finset (Fin N)) := univ.filter fun D => 1 ≤ D.card ∧ D.card ≤ 4

lemma lt2_card_Dset : ((lt2Dset N).card : ℝ) ≤ ((N : ℝ) + 1) ^ 4 := by
  have r0 : State N := fun _ => false
  have hinj : Set.InjOn (fun D => lt2Xor (fun _ => false) D) (lt2Dset N : Set (Finset (Fin N))) := by
    intro D _ D' _ h
    ext j
    have := congrFun h j
    simp only [lt2Xor] at this
    by_cases hj : j ∈ D <;> by_cases hj' : j ∈ D' <;> simp_all
  have hmaps : ∀ D ∈ lt2Dset N, lt2Xor (fun _ => false) D ∈ ballR (fun _ : Fin N => false) 4 := by
    intro D hD
    rw [mem_ballR, b1_ham_comm, lt2_ham_xor]
    exact (mem_filter.1 hD).2.2
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  exact (by exact_mod_cast this.trans (card_ballR_le _ 4) : ((lt2Dset N).card : ℝ) ≤ ((N + 1) ^ 4 : ℕ)).trans
    (by push_cast; exact le_rfl)

/-- **The deterministic inequality of the floor.** -/
theorem lt2_floor_det (s : State N) (w : Param N) (j : Fin N) (t : State N) :
    ∑ r ∈ agree {j} t, lt2fH (w r) ≤
      ∑ r ∈ (lt2H s w).filter (fun r => r ∈ agree {j} t), lt2gNs (w r) ^ 2 +
      ∑ D ∈ lt2Dset N, ∑ r : State N, lt2gNs (w r) ^ 2 * lt2hL (w (lt2Xor r D)) +
      ∑ r ∈ ballR s 6, lt2gNs (w r) ^ 2 := by
  classical
  have hpt : ∀ r ∈ agree {j} t, lt2fH (w r) ≤
      (if r ∈ lt2H s w then lt2gNs (w r) ^ 2 else 0) +
      ∑ D ∈ lt2Dset N, lt2gNs (w r) ^ 2 * lt2hL (w (lt2Xor r D)) +
      (if r ∈ ballR s 6 then lt2gNs (w r) ^ 2 else 0) := by
    intro r _
    have hg2 : 0 ≤ lt2gNs (w r) ^ 2 := sq_nonneg _
    have hT1 : 0 ≤ (if r ∈ lt2H s w then lt2gNs (w r) ^ 2 else 0) := by split_ifs <;> positivity
    have hT2 : 0 ≤ ∑ D ∈ lt2Dset N, lt2gNs (w r) ^ 2 * lt2hL (w (lt2Xor r D)) :=
      Finset.sum_nonneg fun D _ => mul_nonneg hg2 (lt2hL_nonneg _)
    have hT3 : 0 ≤ (if r ∈ ballR s 6 then lt2gNs (w r) ^ 2 else 0) := by split_ifs <;> positivity
    unfold lt2fH
    split_ifs with hL hH hB hB
    · linarith
    · linarith
    · -- `r ∉ H`, `r ∈ ballR s 6`
      linarith
    · -- `r ∉ H`, far from `s`: either `g = 0`, or `r` heavy and not isolated
      by_cases hg : lt2gNs (w r) = 0
      · calc lt2gNs (w r) ^ 2 = 0 := by rw [hg]; norm_num
          _ ≤ _ := by linarith
      · have hX : lt2x1 * N < XW w r := by
          unfold lt2gNs at hg; split_ifs at hg with h
          · exact h
          · exact absurd rfl hg
        have hHv : lt2Heavy w r := ⟨hX, hL⟩
        have hfar : 6 < ham r s := by
          rw [mem_ballR, b1_ham_comm] at hB; omega
        have hnotIso : ¬ lt2Iso w r := fun hI => hH (mem_filter.2 ⟨mem_univ _, hHv, hI, hfar⟩)
        unfold lt2Iso at hnotIso
        push_neg at hnotIso
        obtain ⟨q, hq1, hq4, hql⟩ := hnotIso
        set D := univ.filter fun i => q i ≠ r i
        have hqD : lt2Xor r D = q := by
          funext i; unfold lt2Xor
          by_cases hi : q i = r i
          · rw [if_neg (by simp [D, hi])]; exact hi.symm
          · rw [if_pos (by simp [D, hi])]; cases hq : q i <;> cases hr : r i <;> simp_all
        have hDc : D.card = ham q r := rfl
        have hD : D ∈ lt2Dset N := mem_filter.2 ⟨mem_univ _, by omega, by omega⟩
        have hle : lt2gNs (w r) ^ 2 ≤ ∑ D ∈ lt2Dset N, lt2gNs (w r) ^ 2 * lt2hL (w (lt2Xor r D)) := by
          refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun D => lt2gNs (w r) ^ 2 *
            lt2hL (w (lt2Xor r D))) (fun D _ => mul_nonneg hg2 (lt2hL_nonneg _)) hD)
          rw [hqD, lt2hL_of_not_light hql, mul_one]
        linarith
    · positivity
    · positivity
    · positivity
    · positivity
  calc ∑ r ∈ agree {j} t, lt2fH (w r)
      ≤ ∑ r ∈ agree {j} t, ((if r ∈ lt2H s w then lt2gNs (w r) ^ 2 else 0) +
          ∑ D ∈ lt2Dset N, lt2gNs (w r) ^ 2 * lt2hL (w (lt2Xor r D)) +
          (if r ∈ ballR s 6 then lt2gNs (w r) ^ 2 else 0)) := Finset.sum_le_sum hpt
    _ = ∑ r ∈ (lt2H s w).filter (fun r => r ∈ agree {j} t), lt2gNs (w r) ^ 2 +
          ∑ r ∈ agree {j} t, ∑ D ∈ lt2Dset N, lt2gNs (w r) ^ 2 * lt2hL (w (lt2Xor r D)) +
          ∑ r ∈ (ballR s 6).filter (fun r => r ∈ agree {j} t), lt2gNs (w r) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
          Finset.filter_mem_eq_inter, Finset.filter_mem_eq_inter, Finset.inter_comm (lt2H s w),
          Finset.inter_comm (ballR s 6)]
    _ ≤ _ := by
        refine add_le_add (add_le_add le_rfl ?_) ?_
        · rw [Finset.sum_comm]
          exact Finset.sum_le_sum fun D _ => Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
            fun r _ _ => mul_nonneg (sq_nonneg _) (lt2hL_nonneg _)
        · exact Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun r _ _ => sq_nonneg _

end Census
end IIT
