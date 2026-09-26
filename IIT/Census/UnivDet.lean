/-
Census: a positive `φ_s` of the whole substrate forces a deterministic-looking maximal row.

If `phi z s univ > 0` on the open cube, some maximal cause state `t` of the whole substrate
(a) maximises the row product `rowProd z s`, and (b) beats every column half-mean:
`halfMean z s j (t j) < y z s t j` for every unit `j`.  Otherwise the single-unit cut
`{j}` (inputs) / `univ \ {j}` (outputs) leaves the cause repertoire no more selective,
so `φ_c = 0` at that cut and `φ_s = 0`.
-/
import IIT.Census.Basic
import IIT.MinDep

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-! ### Positivity on the open cube -/

lemma y_pos {z : Param N} (hz : z ∈ openCube N) (s r : State N) (j : Fin N) :
    0 < y z s r j := by
  have h := hz r j
  have hc : clamp01 (z r j) = z r j := by
    unfold clamp01; rw [min_eq_right h.2.le, max_eq_right h.1.le]
  unfold y
  simp only [tpmOf]
  cases s j
  · simp only [Bool.false_eq_true, ↓reduceIte, hc]; linarith [h.2]
  · simp only [↓reduceIte, hc]; exact h.1

lemma rowProd_pos {z : Param N} (hz : z ∈ openCube N) (s r : State N) :
    0 < rowProd z s r :=
  Finset.prod_pos fun j _ => y_pos hz s r j

lemma fullProb_eq_rowProd (z : Param N) (s r : State N) :
    fullProb (tpmOf z) r s = rowProd z s r := rfl

lemma sum_fullProb_pos {z : Param N} (hz : z ∈ openCube N) (s : State N) :
    0 < ∑ v : State N, fullProb (tpmOf z) v s :=
  Finset.sum_pos (fun v _ => rowProd_pos hz s v) Finset.univ_nonempty

lemma avg_pos (f : State N → ℝ) (hf : ∀ t, 0 < f t) : 0 < avgOverStates f :=
  div_pos (Finset.sum_pos (fun t _ => hf t) Finset.univ_nonempty) (by positivity)

/-! ### Step 1: the whole-substrate cause side in terms of row products -/

lemma sysCauseProb_univ_eq {z : Param N} (hz : z ∈ openCube N) (s t : State N) :
    sysCauseProb (tpmOf z) univ s s t = rowProd z s t :=
  sysCauseProb_univ _ _ _ _ (sum_fullProb_pos hz s)

lemma sysIiC_univ_eq {z : Param N} (hz : z ∈ openCube N) (s t : State N) :
    sysIiC (tpmOf z) univ s s t =
      rowProd z s t / ((2 : ℝ) ^ (univ : Finset (Fin N)).card * avgOverStates (rowProd z s))
        * Real.logb 2 (rowProd z s t / avgOverStates (rowProd z s)) := by
  have hc : ∀ t, sysCauseProb (tpmOf z) univ s s t = rowProd z s t :=
    fun t => sysCauseProb_univ_eq hz s t
  unfold sysIiC sysBackCause sysUncCause
  simp only [hc]

/-! ### Step 2: a maximiser of `ii_c` maximises the row product -/

lemma max_of_argmax_iic (f : State N → ℝ) (hf : ∀ t, 0 < f t) (K : ℝ) (hK : 0 < K)
    (t : State N)
    (ht : ∀ t', f t' / (K * avgOverStates f) * Real.logb 2 (f t' / avgOverStates f) ≤
      f t / (K * avgOverStates f) * Real.logb 2 (f t / avgOverStates f)) :
    ∀ t', f t' ≤ f t := by
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image (univ : Finset (State N)) f univ_nonempty
  by_contra hcon
  push Not at hcon
  obtain ⟨t', ht'⟩ := hcon
  have hlt : f t < f m := lt_of_lt_of_le ht' (hm t' (mem_univ _))
  set A := avgOverStates f with hAdef
  have hA : 0 < A := avg_pos f hf
  -- the mean is strictly below the maximum
  have hAm : A < f m := by
    have hsum : ∑ r : State N, f r < ∑ _r : State N, f m :=
      Finset.sum_lt_sum (fun r _ => hm r (mem_univ r)) ⟨t, mem_univ t, hlt⟩
    rw [Finset.sum_const, card_state, nsmul_eq_mul] at hsum
    have h2 : (0 : ℝ) < 2 ^ N := by positivity
    rw [hAdef, avgOverStates, div_lt_iff₀ h2]
    push_cast at hsum
    linarith
  have hKA : 0 < K * A := mul_pos hK hA
  have hgm : 0 < f m / (K * A) * Real.logb 2 (f m / A) := by
    refine mul_pos (div_pos (hf m) hKA) (Real.logb_pos one_lt_two ?_)
    rw [one_lt_div hA]; exact hAm
  have hgt : f t / (K * A) * Real.logb 2 (f t / A) < f m / (K * A) * Real.logb 2 (f m / A) := by
    rcases le_or_gt (f t) A with hle | hgt
    · have hlog : Real.logb 2 (f t / A) ≤ 0 :=
        Real.logb_nonpos one_lt_two (div_nonneg (hf t).le hA.le) ((div_le_one hA).2 hle)
      have : f t / (K * A) * Real.logb 2 (f t / A) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (div_pos (hf t) hKA).le hlog
      linarith
    · have hl1 : 0 < Real.logb 2 (f t / A) :=
        Real.logb_pos one_lt_two ((one_lt_div hA).2 hgt)
      have hl2 : Real.logb 2 (f t / A) < Real.logb 2 (f m / A) :=
        Real.logb_lt_logb one_lt_two (div_pos (hf t) hA) (div_lt_div_of_pos_right hlt hA)
      have hd : f t / (K * A) < f m / (K * A) := div_lt_div_of_pos_right hlt hKA
      exact mul_lt_mul'' hd hl2 (div_pos (hf t) hKA).le hl1.le
  have := ht m
  linarith

lemma rowProd_max_of_mem {z : Param N} (hz : z ∈ openCube N) (s t : State N)
    (ht : t ∈ sysMaxCauseStates (tpmOf z) univ s s) :
    ∀ t', rowProd z s t' ≤ rowProd z s t := by
  have h := mem_argmaxSet.1 ht
  refine max_of_argmax_iic (rowProd z s) (rowProd_pos hz s)
    ((2 : ℝ) ^ (univ : Finset (Fin N)).card) (by positivity) t ?_
  intro t'
  have := h t'
  rw [sysIiC_univ_eq hz, sysIiC_univ_eq hz] at this
  exact this

/-! ### Step 3: the single-unit cut on the cause side -/

lemma hrest_of_two_le (hN : 2 ≤ N) (j : Fin N) : ((univ : Finset (Fin N)).erase j).Nonempty := by
  apply Finset.card_pos.1
  rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
  omega

lemma effUnit_single_eq_halfMean (z : Param N) (s t : State N) (j : Fin N) :
    effUnit (tpmOf z) {j} t j (s j) = halfMean z s j (t j) := by
  have hag : agree ({j} : Finset (Fin N)) t = univ.filter (fun r : State N => r j = t j) := by
    ext r; simp [agree]
  have hcard : ((agree ({j} : Finset (Fin N)) t).card : ℝ) = (2 : ℝ) ^ (N - 1) := by
    rw [card_agree, card_singleton]; push_cast; rfl
  rw [effUnit, hcard, hag]
  rfl

lemma sysPartCauseProb_split {z : Param N} (hz : z ∈ openCube N) (s t : State N) (j : Fin N)
    (hrest : ((univ : Finset (Fin N)).erase j).Nonempty) :
    sysPartCauseProb (tpmOf z) univ s (splitAt (mem_univ j) hrest) s t =
      ∏ i, (if i = j then halfMean z s j (t j) else y z s t i) := by
  unfold sysPartCauseProb
  refine Finset.prod_congr rfl fun i _ => ?_
  set M := ((splitAt (mem_univ j) hrest).cutSet ((splitAt (mem_univ j) hrest).partOf i))ᶜ
  have hw : ∀ w : State N,
      effUnit (tpmOf z) M (merge univ t w) i (s i) * bgWeight (tpmOf z) univ s w
        = effUnit (tpmOf z) M t i (s i) := by
    intro w
    rw [merge_univ, bgWeight_univ _ _ _ (sum_fullProb_pos hz s), mul_one]
  rw [Finset.sum_congr rfl fun w _ => hw w, Finset.sum_const, card_state, nsmul_eq_mul,
    card_univ, Fintype.card_fin]
  have h2 : ((2 : ℝ) ^ N) ≠ 0 := by positivity
  push_cast
  rw [mul_div_cancel_left₀ _ h2]
  by_cases hij : i = j
  · subst hij
    have hM : M = {i} := by
      simp only [M, splitAt_partOf_j, splitAt_cut_j]
      ext x; simp
    simp only [↓reduceIte]
    rw [hM, effUnit_single_eq_halfMean]
  · have hi' : i ∈ (univ : Finset (Fin N)).erase j := mem_erase.2 ⟨hij, mem_univ i⟩
    have hM : M = univ := by
      simp only [M, splitAt_partOf_rest (mem_univ j) hrest hi', splitAt_cut_rest,
        compl_empty]
    simp only [hij, ↓reduceIte]
    rw [hM, effUnit_univ_prob]
    rfl

lemma sysPhiC_split_zero {z : Param N} (hz : z ∈ openCube N) (s t : State N) (j : Fin N)
    (hrest : ((univ : Finset (Fin N)).erase j).Nonempty)
    (hge : y z s t j ≤ halfMean z s j (t j)) :
    sysPhiC (tpmOf z) univ s (splitAt (mem_univ j) hrest) s t = 0 := by
  have hP := rowProd_pos hz s t
  have hle : rowProd z s t ≤ ∏ i, (if i = j then halfMean z s j (t j) else y z s t i) := by
    refine Finset.prod_le_prod (fun i _ => (y_pos hz s t i).le) fun i _ => ?_
    split_ifs with h
    · subst h; exact hge
    · exact le_rfl
  have hQ := lt_of_lt_of_le hP hle
  have hlog : Real.logb 2 (rowProd z s t /
      ∏ i, (if i = j then halfMean z s j (t j) else y z s t i)) ≤ 0 :=
    Real.logb_nonpos one_lt_two (div_nonneg hP.le hQ.le) ((div_le_one hQ).2 hle)
  unfold sysPhiC
  rw [sysCauseProb_univ_eq hz, sysPartCauseProb_split hz s t j hrest, pos,
    max_eq_left hlog, mul_zero]

/-! ### Step 4: a zero partition kills `φ_s` at that state pair -/

lemma sysPhiOfState_eq_zero_of_zero {T : UnitTPM N} {S : Finset (Fin N)} {u s tc te : State N}
    (θ0 : SysPartition N S) (h0 : sysPhiAt T S u θ0 s tc te = 0) :
    sysPhiOfState T S u s tc te = 0 := by
  have : Nonempty (SysPartition N S) := ⟨θ0⟩
  have hns : normalizedSysPhiAt T S u θ0 s tc te = 0 := by
    rw [normalizedSysPhiAt, h0, zero_div]
  obtain ⟨θ1, hθ1⟩ :=
    argminSet_nonempty (fun θ : SysPartition N S => normalizedSysPhiAt T S u θ s tc te)
  have hz1 : normalizedSysPhiAt T S u θ1 s tc te = 0 := by
    apply le_antisymm
    · have := (mem_argminSet.1 hθ1) θ0
      rw [hns] at this; exact this
    · exact div_nonneg (sysPhiAt_nonneg T S u θ1 s tc te) (Nat.cast_nonneg _)
  refine le_antisymm ?_ (sysPhiOfState_nonneg T S u s tc te)
  unfold sysPhiOfState sysMipSetAt
  refine sup'OrZero_le le_rfl fun θ hθ => ?_
  have hr : normalizedSysPhiAt T S u θ s tc te = 0 := by
    apply le_antisymm
    · have := (mem_argminSet.1 hθ) θ1
      rw [hz1] at this; exact this
    · exact div_nonneg (sysPhiAt_nonneg T S u θ s tc te) (Nat.cast_nonneg _)
  have hcc : (sysCutCount θ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (sysCutCount_pos θ).ne'
  rw [normalizedSysPhiAt] at hr
  exact le_of_eq ((div_eq_zero_iff.1 hr).resolve_right hcc)

lemma sysPhiOfState_zero_of_halfMean {z : Param N} (hz : z ∈ openCube N) (hN : 2 ≤ N)
    (s tc te : State N) (j : Fin N) (hge : y z s tc j ≤ halfMean z s j (tc j)) :
    sysPhiOfState (tpmOf z) univ s s tc te = 0 := by
  have hrest := hrest_of_two_le hN j
  refine sysPhiOfState_eq_zero_of_zero (splitAt (mem_univ j) hrest) ?_
  unfold sysPhiAt
  rw [sysPhiC_split_zero hz s tc j hrest hge]
  exact min_eq_left (sysPhiE_nonneg _ _ _ _ _ _)

/-! ### Step 5: assembly -/

theorem exists_maxRow_of_phi_univ_pos (hN : 2 ≤ N) (z : Param N) (hz : z ∈ openCube N)
    (s : State N) (h : 0 < phi z s univ) :
    ∃ t : State N, (∀ t', rowProd z s t' ≤ rowProd z s t) ∧ ∀ j, halfMean z s j (t j) < y z s t j := by
  have key : ∃ tc ∈ sysMaxCauseStates (tpmOf z) univ s s,
      ∀ j, halfMean z s j (tc j) < y z s tc j := by
    by_contra hk
    push Not at hk
    have hle : phi z s univ ≤ 0 := by
      unfold phi sysPhi
      refine sup'OrZero_le le_rfl fun p hp => ?_
      obtain ⟨j, hj⟩ := hk p.1 (mem_product.1 hp).1
      exact le_of_eq (sysPhiOfState_zero_of_halfMean hz hN s p.1 p.2 j hj)
    linarith
  obtain ⟨tc, htc, hj⟩ := key
  exact ⟨tc, rowProd_max_of_mem hz s tc htc, hj⟩

end Census
end IIT
