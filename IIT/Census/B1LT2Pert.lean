/-
Census, B1 lemma LT2, module M4 part 2: the deterministic perturbation lemma.

`w½ := w` with the private entries set to `1/2` (a function of the non-private entries: the shared data `F`).
For `|S| ≤ 2`, every column `i` and pattern `t`:

    |NumNs(w) - NumNs(w½) - Π(w)| ≤ ε(w) := |H|·(N+1)⁴·e^{-7N/10} + (N+1)⁴·θ,

where `Π(w) = Σ_{r ∈ H} 1{(merge S t r, i) ∈ PB(r)} P_ns(r)(y_{merge S t r, i} - 1/2)` is the private sum.
Every row within distance 4 of an `H` row is light (`X_{C₀} > 7N/10`), so its weight is `≤ e^{-7N/10}`.
-/
import IIT.Census.B1LT2Heavy

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- The private entries set to `1/2`. -/
noncomputable def lt2Half (s : State N) (w : Param N) : Param N := by
  classical exact fun r j => if (r, j) ∈ lt2Priv s w then 1 / 2 else w r j

/-- The private sum of a candidate `S`, column `i`, pattern `t`. -/
noncomputable def lt2Pi (s : State N) (w : Param N) (S : Finset (Fin N)) (t : State N) (i : Fin N) : ℝ := by
  classical exact ∑ r ∈ lt2H s w,
    if (merge S t r, i) ∈ lt2PB r then lt2gNs (w r) * (clamp01 (w (merge S t r) i) - 1 / 2) else 0

/-- The deterministic perturbation bound. -/
noncomputable def lt2Eps (s : State N) (w : Param N) : ℝ :=
  (lt2H s w).card * ((N : ℝ) + 1) ^ 4 * Real.exp (-(7 / 10 * (N : ℝ))) + ((N : ℝ) + 1) ^ 4 * lt2θ N

lemma lt2Half_agree (s : State N) (w : Param N) :
    ∀ q ∉ lt2Priv s w, w q.1 q.2 = lt2Half s w q.1 q.2 := by
  classical
  intro q hq; unfold lt2Half; rw [if_neg hq]

lemma lt2Half_of_mem {s : State N} {w : Param N} {q : State N × Fin N} (hq : q ∈ lt2Priv s w) :
    lt2Half s w q.1 q.2 = 1 / 2 := by
  classical
  unfold lt2Half; rw [if_pos hq]

lemma lt2Priv_half (s : State N) (w : Param N) : lt2Priv s (lt2Half s w) = lt2Priv s w :=
  lt2Priv_stop (lt2Half_agree s w)

lemma clamp01_half : clamp01 (1 / 2 : ℝ) = 1 / 2 := clamp01_of_mem ⟨by norm_num, by norm_num⟩

lemma lt2_ham_merge_le (S : Finset (Fin N)) (t v : State N) : ham v (merge S t v) ≤ S.card := by
  unfold ham
  refine Finset.card_le_card fun j hj => ?_
  simp only [mem_filter, mem_univ, true_and] at hj
  by_contra hjS
  exact hj (by rw [merge_not_mem hjS])

/-- The weight is at most `e^{-X_{C₀}}`. -/
lemma lt2gNs_le_exp_C0 (x : Fin N → ℝ) :
    lt2gNs x ≤ Real.exp (-∑ j ∈ lt2C0 N, -Real.log (clamp01 (x j))) := by
  have h1 : lt2gNs x ≤ ∏ j, clamp01 (x j) := by
    unfold lt2gNs; split_ifs
    · exact le_rfl
    · exact Finset.prod_nonneg fun j _ => clamp01_nonneg _
  have h2 : ∏ j, clamp01 (x j) ≤ ∏ j ∈ lt2C0 N, clamp01 (x j) := by
    rw [← Finset.prod_mul_prod_compl (lt2C0 N) (fun j => clamp01 (x j))]
    exact mul_le_of_le_one_right (Finset.prod_nonneg fun j _ => clamp01_nonneg _)
      (Finset.prod_le_one (fun j _ => clamp01_nonneg _) fun j _ => clamp01_le_one _)
  refine h1.trans (h2.trans ?_)
  by_cases hpos : ∀ j ∈ lt2C0 N, 0 < clamp01 (x j)
  · apply le_of_eq
    rw [Finset.sum_neg_distrib, neg_neg, Real.exp_sum]
    exact Finset.prod_congr rfl fun j hj => (Real.exp_log (hpos j hj)).symm
  · push_neg at hpos
    obtain ⟨j, hj, h0⟩ := hpos
    rw [Finset.prod_eq_zero hj (le_antisymm h0 (clamp01_nonneg _))]
    exact (Real.exp_pos _).le

lemma lt2gNs_light {w : Param N} {v : State N} (h : lt2Light w v) :
    lt2gNs (w v) ≤ Real.exp (-(7 / 10 * (N : ℝ))) := by
  refine (lt2gNs_le_exp_C0 (w v)).trans (Real.exp_le_exp.2 ?_)
  unfold lt2Light XMW at h
  linarith

/-- The summand of the error, pointwise. -/
lemma lt2_pert_term (s : State N) (w : Param N) {S : Finset (Fin N)} (hS : S.card ≤ 2) (t : State N) (i : Fin N)
    (v : State N) :
    |clamp01 (w (merge S t v) i) * lt2gNs (w v) - clamp01 (lt2Half s w (merge S t v) i) * lt2gNs (lt2Half s w v)
      - (if v ∈ lt2H s w then (if (merge S t v, i) ∈ lt2PB v then
          lt2gNs (w v) * (clamp01 (w (merge S t v) i) - 1 / 2) else 0) else 0)| ≤
      (if ∃ r ∈ lt2H s w, ham v r ≤ 4 ∧ 1 ≤ ham v r then Real.exp (-(7 / 10 * (N : ℝ))) else 0) +
      (if ham v s ≤ 4 then lt2θ N else 0) := by
  classical
  set m := merge S t v
  set w2 := lt2Half s w
  have hvm : ham v m ≤ 2 := (lt2_ham_merge_le S t v).trans hS
  have hRHS : 0 ≤ (if ∃ r ∈ lt2H s w, ham v r ≤ 4 ∧ 1 ≤ ham v r then Real.exp (-(7 / 10 * (N : ℝ))) else 0) +
      (if ham v s ≤ 4 then lt2θ N else 0) := by
    have := (Real.exp_pos (-(7 / 10 * (N : ℝ)))).le
    have := (Real.exp_pos (-(lt2x1 * N))).le
    split_ifs <;> (try unfold lt2θ) <;> linarith
  by_cases hvH : v ∈ lt2H s w
  · have hH := (mem_filter.1 hvH).2
    have hnl : ¬ lt2Light w v := lt2_heavy_not_light hH.1
    have hrow : w2 v = w v := funext fun j =>
      (lt2Half_agree s w (v, j) (lt2_row_not_Priv hnl (by omega) j)).symm
    rw [if_pos hvH, hrow]
    by_cases hP : (m, i) ∈ lt2PB v
    · have hmem : (m, i) ∈ lt2Priv s w := by
        unfold lt2Priv; exact mem_union_left _ (mem_biUnion.2 ⟨v, hvH, hP⟩)
      rw [if_pos hP, show w2 m i = 1 / 2 from lt2Half_of_mem hmem, clamp01_half]
      rw [show clamp01 (w m i) * lt2gNs (w v) - 1 / 2 * lt2gNs (w v) -
        lt2gNs (w v) * (clamp01 (w m i) - 1 / 2) = 0 by ring, abs_zero]
      exact hRHS
    · have hnot : (m, i) ∉ lt2Priv s w := by
        intro hmem
        unfold lt2Priv at hmem
        rcases mem_union.1 hmem with h | h
        · obtain ⟨r, hr, hq⟩ := mem_biUnion.1 h
          have hPB := lt2_mem_PB hq
          by_cases hrv : r = v
          · subst hrv; exact hP hq
          · have hiso := (mem_filter.1 hr).2.2.1
            have hd := ham_triangle v m r
            have hd1 : 1 ≤ ham v r := by
              by_contra h0
              push_neg at h0
              apply hrv
              funext j
              by_contra hj
              have : 0 < ham v r := Finset.card_pos.2 ⟨j, by simp [Ne.symm hj]⟩
              omega
            exact hnl (hiso v hd1 (by simp only at hPB; omega))
        · have hPB := lt2_mem_PB h
          have hd := ham_triangle v m s
          simp only at hPB
          omega
      rw [if_neg hP, show w2 m i = w m i from (lt2Half_agree s w (m, i) hnot).symm]
      rw [show clamp01 (w m i) * lt2gNs (w v) - clamp01 (w m i) * lt2gNs (w v) - 0 = 0 by ring, abs_zero]
      exact hRHS
  · rw [if_neg hvH, sub_zero]
    have hy1 := clamp01_nonneg (w m i); have hy1' := clamp01_le_one (w m i)
    have hy2 := clamp01_nonneg (w2 m i); have hy2' := clamp01_le_one (w2 m i)
    have hg1 := lt2gNs_nonneg (w v); have hg2 := lt2gNs_nonneg (w2 v)
    by_cases hch : (m, i) ∉ lt2Priv s w ∧ ∀ j, (v, j) ∉ lt2Priv s w
    · have e1 : w2 m i = w m i := (lt2Half_agree s w (m, i) hch.1).symm
      have e2 : w2 v = w v := funext fun j => (lt2Half_agree s w (v, j) (hch.2 j)).symm
      rw [e1, e2, sub_self, abs_zero]; exact hRHS
    · -- some private position at `m` or in the row `v`: `v` is near `H` or near `s`
      have hnear : (∃ r ∈ lt2H s w, ham v r ≤ 4 ∧ 1 ≤ ham v r) ∨ ham v s ≤ 4 := by
        have key : ∀ q : State N × Fin N, q ∈ lt2Priv s w → ham v q.1 ≤ 2 →
            (∃ r ∈ lt2H s w, ham v r ≤ 4 ∧ 1 ≤ ham v r) ∨ ham v s ≤ 4 := by
          intro q hq hvq
          rcases lt2_mem_Priv hq with ⟨r, hr, h1, h2⟩ | h
          · have hd := ham_triangle v q.1 r
            refine Or.inl ⟨r, hr, by omega, ?_⟩
            by_contra h0
            push_neg at h0
            have hvr : v = r := by
              funext j
              by_contra hj
              have : 0 < ham v r := Finset.card_pos.2 ⟨j, by simp [hj]⟩
              omega
            exact hvH (hvr ▸ hr)
          · have hd := ham_triangle v q.1 s
            exact Or.inr (by omega)
        rw [not_and_or] at hch
        rcases hch with h | h
        · push_neg at h; exact key (m, i) h hvm
        · push_neg at h
          obtain ⟨j, hj⟩ := h
          exact key (v, j) hj (by rw [b1_ham_self]; omega)
      have hdiff : |clamp01 (w m i) * lt2gNs (w v) - clamp01 (w2 m i) * lt2gNs (w2 v)| ≤
          max (lt2gNs (w v)) (lt2gNs (w2 v)) := by
        rw [abs_le]; constructor
        · nlinarith [le_max_right (lt2gNs (w v)) (lt2gNs (w2 v))]
        · nlinarith [le_max_left (lt2gNs (w v)) (lt2gNs (w2 v))]
      refine hdiff.trans ?_
      rcases hnear with ⟨r, hr, h4, h1⟩ | hs
      · have hiso := (mem_filter.1 hr).2.2.1
        have hl : lt2Light w v := hiso v h1 h4
        have hl2 : lt2Light w2 v := (lt2_light_congr (lt2Half_agree s w) v).1 hl
        have hb := max_le (lt2gNs_light hl) (lt2gNs_light hl2)
        rw [if_pos ⟨r, hr, h4, h1⟩]
        have : 0 ≤ (if ham v s ≤ 4 then lt2θ N else 0) := by
          split_ifs
          · exact (Real.exp_pos _).le
          · exact le_rfl
        linarith
      · have hb := max_le (lt2gNs_le (w v)) (lt2gNs_le (w2 v))
        rw [if_pos hs]
        have : 0 ≤ (if ∃ r ∈ lt2H s w, ham v r ≤ 4 ∧ 1 ≤ ham v r then Real.exp (-(7 / 10 * (N : ℝ))) else 0) := by
          split_ifs
          · exact (Real.exp_pos _).le
          · exact le_rfl
        linarith

/-- **The deterministic perturbation lemma.** -/
theorem lt2_pert (s : State N) (w : Param N) {S : Finset (Fin N)} (hS : S.card ≤ 2) (t : State N) (i : Fin N) :
    |lt2NumNs w S t i - lt2NumNs (lt2Half s w) S t i - lt2Pi s w S t i| ≤ lt2Eps s w := by
  classical
  set E := Real.exp (-(7 / 10 * (N : ℝ)))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hθ : 0 ≤ lt2θ N := (Real.exp_pos _).le
  have hPi : lt2Pi s w S t i = ∑ v, (if v ∈ lt2H s w then (if (merge S t v, i) ∈ lt2PB v then
      lt2gNs (w v) * (clamp01 (w (merge S t v) i) - 1 / 2) else 0) else 0) := by
    unfold lt2Pi; rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hPi]; unfold lt2NumNs
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun v _ => lt2_pert_term s w hS t i v).trans ?_)
  rw [Finset.sum_add_distrib]
  unfold lt2Eps
  refine add_le_add ?_ ?_
  · calc ∑ v, (if ∃ r ∈ lt2H s w, ham v r ≤ 4 ∧ 1 ≤ ham v r then E else 0)
        ≤ ∑ v, ∑ r ∈ lt2H s w, (if ham r v ≤ 4 then E else 0) := Finset.sum_le_sum fun v _ => by
          split_ifs with h
          · obtain ⟨r, hr, h4, -⟩ := h
            refine le_trans ?_ (Finset.single_le_sum (f := fun r => if ham r v ≤ 4 then E else 0)
              (fun r _ => by split_ifs <;> positivity) hr)
            rw [if_pos (by rw [b1_ham_comm]; exact h4)]
          · exact Finset.sum_nonneg fun r _ => by split_ifs <;> positivity
      _ = ∑ r ∈ lt2H s w, ((ballR r 4).card : ℝ) * E := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; rfl
      _ ≤ ∑ _r ∈ lt2H s w, ((N : ℝ) + 1) ^ 4 * E := Finset.sum_le_sum fun r _ =>
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_ballR_le r 4) hE
      _ = (lt2H s w).card * ((N : ℝ) + 1) ^ 4 * E := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  · have hf : univ.filter (fun v : State N => ham v s ≤ 4) = ballR s 4 := by
      ext v; simp only [mem_filter, mem_univ, true_and, mem_ballR]; rw [b1_ham_comm]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hf]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_ballR_le s 4) hθ

end Census
end IIT
