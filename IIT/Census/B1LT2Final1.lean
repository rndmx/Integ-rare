/-
Census, B1 lemma LT2, module M6f-3: the good pairs and the conditional product bound.

`G(w) = {(a,b) ∈ D₁×D₂ : ¬ Z, a and b not weak}` (shared data only). `Y* = {VF ∧ #G ≥ m²/4 ∧ ∀ p ∈ G, ¬ Succ_p}`.
`lt2_Ystar_prob`: `P(Y*) ≤ e^{-p₂ m²/4}` (resampling the private entries, `lt2_nosucc_prob`).
-/
import IIT.Census.B1LT2ZCount

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- The constants. -/
def lt2x : ℝ := 300000
noncomputable def lt2γ : ℝ := Real.exp (-200)
noncomputable def lt2ρ : ℝ := lt2γ / 10
noncomputable def lt2p2 : ℝ := (lt2ρ * (Real.exp (-(225 * lt2x ^ 2)) / 4)) ^ 16

lemma lt2γ_pos : 0 < lt2γ := Real.exp_pos _
lemma lt2γ_le : lt2γ ≤ 1 / 100 := by
  unfold lt2γ
  have := Real.exp_le_exp.2 (show (-200 : ℝ) ≤ -5 by norm_num)
  have h5 : Real.exp (-5) ≤ 1 / 100 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have he : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    have h27 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have := pow_le_pow_left₀ (by norm_num) h27 5
    rw [he]; norm_num at this ⊢; linarith
  linarith
lemma lt2ρ_nonneg : 0 ≤ lt2ρ := by unfold lt2ρ; exact div_nonneg lt2γ_pos.le (by norm_num)
lemma lt2ρ_le : lt2ρ ≤ 1 / 100 := by unfold lt2ρ; have := lt2γ_le; linarith
lemma lt2p2_pos : 0 < lt2p2 := by
  unfold lt2p2 lt2ρ; have := lt2γ_pos; positivity

/-- A weak effect unit. -/
def lt2Weak (s : State N) (w : Param N) (j : Fin N) : Prop := |clamp01 (w s j) - 1 / 2| < lt2γ

/-- The good pairs. -/
noncomputable def lt2Good (s : State N) (w : Param N) : Finset (Fin N × Fin N) := by
  classical exact (lt2D1 N ×ˢ lt2D2 N).filter fun p => ¬ lt2ZP s w p ∧ ¬ lt2Weak s w p.1 ∧ ¬ lt2Weak s w p.2

/-- The variance floor at `w`. -/
def lt2VF (s : State N) (w : Param N) : Prop :=
  ∀ (j : Fin N) (β : Bool), sigN N ^ 2 / 16 ≤
    ∑ r ∈ (lt2H s w).filter (fun r => r ∈ agree {j} (fun _ => β)), lt2gNs (w r) ^ 2

/-- The conditional event. -/
def lt2Ystar (s : State N) : Set (Param N) :=
  {w | lt2VF s w ∧ ((lt2m N : ℝ)) ^ 2 / 4 ≤ ((lt2Good s w).card : ℝ) ∧
    ∀ p ∈ lt2Good s w, ¬ lt2Succ s w p.1 p.2 lt2x lt2ρ}

/-! ### Measurability -/

lemma lt2_meas_sumH (s : State N) (P : State N → Prop) [DecidablePred P] (g : Param N → State N → ℝ)
    (hg : ∀ r, Measurable fun w => g w r) :
    Measurable fun w : Param N => ∑ r ∈ (lt2H s w).filter P, g w r := by
  classical
  have e : (fun w : Param N => ∑ r ∈ (lt2H s w).filter P, g w r) =
      fun w => ∑ r : State N, {w : Param N | r ∈ lt2H s w}.indicator (fun w => if P r then g w r else 0) w := by
    funext w
    rw [Finset.sum_filter]
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [Finset.sum_ite_mem univ (lt2H s w), Finset.univ_inter]
  rw [e]
  refine Finset.measurable_sum _ fun r _ => Measurable.indicator ?_ (lt2_mset_memH s r)
  split_ifs
  · exact hg r
  · exact measurable_const

lemma lt2_mset_VF (s : State N) : MeasurableSet {w : Param N | lt2VF s w} := by
  classical
  unfold lt2VF
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun β => measurableSet_le measurable_const
    (lt2_meas_sumH s _ (fun w r => lt2gNs (w r) ^ 2) fun r =>
      (lt2gNs_measurable.comp (measurable_pi_apply r)).pow_const 2)

lemma lt2_mset_weak (s : State N) (j : Fin N) : MeasurableSet {w : Param N | lt2Weak s w j} :=
  measurableSet_lt ((measurable_clamp01.comp ((measurable_pi_apply j).comp (measurable_pi_apply s))).sub
    measurable_const).abs measurable_const

lemma lt2_mset_memGood (s : State N) (p : Fin N × Fin N) : MeasurableSet {w : Param N | p ∈ lt2Good s w} := by
  classical
  by_cases hp : p ∈ lt2D1 N ×ˢ lt2D2 N
  · have e : {w : Param N | p ∈ lt2Good s w} =
        {w | lt2ZP s w p}ᶜ ∩ ({w | lt2Weak s w p.1}ᶜ ∩ {w | lt2Weak s w p.2}ᶜ) := by
      ext w; simp [lt2Good, hp]
    rw [e]
    exact (lt2_mset_ZP s p).compl.inter ((lt2_mset_weak s _).compl.inter (lt2_mset_weak s _).compl)
  · have e : {w : Param N | p ∈ lt2Good s w} = ∅ := by
      ext w; simp only [lt2Good, mem_filter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hp h.1
    rw [e]; exact MeasurableSet.empty

lemma lt2_meas_sd (s : State N) (a b : Fin N) (c u v : Bool) :
    Measurable fun w : Param N => lt2sd s w a b c u v := by
  classical
  unfold lt2sd lt2Hf
  exact Real.continuous_sqrt.measurable.comp (lt2_meas_sumH s _ (fun w r => lt2gNs (w r) ^ 2 / 12) fun r =>
    ((lt2gNs_measurable.comp (measurable_pi_apply r)).pow_const 2).div_const _)

lemma lt2_meas_Sres_self (s : State N) (a b : Fin N) (c u v : Bool) :
    Measurable fun w : Param N => lt2Sres s w a b c u v w := by
  classical
  unfold lt2Sres lt2Hf
  exact lt2_meas_sumH s _ (fun w r => lt2gNs (w r) *
      (clamp01 (w (merge {a, b} (lt2pat a b u v) r) (lt2col a b c)) - 1 / 2)) fun r =>
    (lt2gNs_measurable.comp (measurable_pi_apply r)).mul ((lt2_meas_entry _ _).sub measurable_const)

lemma lt2_mset_succ_self (s : State N) (a b : Fin N) (x ρ : ℝ) :
    MeasurableSet {w : Param N | lt2Succ s w a b x ρ} := by
  classical
  unfold lt2Succ
  simp only [Set.setOf_forall]
  refine MeasurableSet.iInter fun κ => ?_
  obtain ⟨e, c, u, v⟩ := κ
  cases e
  · simp only [lt2X, Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · exact measurableSet_le ((lt2_meas_sd s a b c u v).const_mul x) (lt2_meas_Sres_self s a b c u v)
    · exact measurableSet_le (lt2_meas_Sres_self s a b c u v) ((lt2_meas_sd s a b c u v).const_mul x).neg
  · simp only [lt2X, ↓reduceIte]
    split_ifs
    · have e : {w : Param N | w ∈ (if 1 / 2 ≤ clamp01 (w s (lt2col a b c)) then
          {η : Param N | clamp01 (η (lt2rowE s a b u v) (lt2col a b c)) ≤ ρ}
        else {η | 1 - ρ ≤ clamp01 (η (lt2rowE s a b u v) (lt2col a b c))})} =
          ({w | 1 / 2 ≤ clamp01 (w s (lt2col a b c))} ∩ {w | clamp01 (w (lt2rowE s a b u v) (lt2col a b c)) ≤ ρ}) ∪
          ({w | 1 / 2 ≤ clamp01 (w s (lt2col a b c))}ᶜ ∩
            {w | 1 - ρ ≤ clamp01 (w (lt2rowE s a b u v) (lt2col a b c))}) := by
        ext w
        by_cases h : 1 / 2 ≤ clamp01 (w s (lt2col a b c))
        · simp only [Set.mem_setOf_eq]; rw [if_pos h]; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]; tauto
        · simp only [Set.mem_setOf_eq]; rw [if_neg h]; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]; tauto
      rw [e]
      exact ((measurableSet_le measurable_const (lt2_meas_entry _ _)).inter
        (measurableSet_le (lt2_meas_entry _ _) measurable_const)).union
        ((measurableSet_le measurable_const (lt2_meas_entry _ _)).compl.inter
        (measurableSet_le measurable_const (lt2_meas_entry _ _)))
    · simp only [Set.mem_univ, Set.setOf_true]; exact MeasurableSet.univ

lemma lt2_mset_Ystar (s : State N) : MeasurableSet (lt2Ystar (N := N) s) := by
  classical
  have hcard : Measurable fun w : Param N => ((lt2Good s w).card : ℝ) := by
    have e : (fun w : Param N => ((lt2Good s w).card : ℝ)) =
        fun w => ∑ p : Fin N × Fin N, {w : Param N | p ∈ lt2Good s w}.indicator (fun _ => (1 : ℝ)) w := by
      funext w; simp only [Set.indicator_apply, Set.mem_setOf_eq]; rw [Finset.sum_boole]; simp
    rw [e]; exact Finset.measurable_sum _ fun p _ => measurable_const.indicator (lt2_mset_memGood s p)
  have e : lt2Ystar (N := N) s = {w | lt2VF s w} ∩ ({w | ((lt2m N : ℝ)) ^ 2 / 4 ≤ ((lt2Good s w).card : ℝ)} ∩
      ⋂ p : Fin N × Fin N, ({w | p ∈ lt2Good s w}ᶜ ∪ {w | lt2Succ s w p.1 p.2 lt2x lt2ρ}ᶜ)) := by
    ext w; simp only [lt2Ystar, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_union,
      Set.mem_compl_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun p => ?_⟩
      by_cases hp : p ∈ lt2Good s w
      · exact Or.inr (h3 p hp)
      · exact Or.inl hp
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun p hp => (h3 p).resolve_left (not_not.2 hp)⟩
  rw [e]
  exact (lt2_mset_VF s).inter ((measurableSet_le measurable_const hcard).inter
    (MeasurableSet.iInter fun p => (lt2_mset_memGood s p).compl.union (lt2_mset_succ_self s _ _ _ _).compl))

/-! ### The shared data are unchanged by resampling -/

lemma lt2_row_s_notPriv (s : State N) (w : Param N) (j : Fin N) : (s, j) ∉ lt2Priv s w := by
  classical
  intro hq
  unfold lt2Priv at hq
  rcases mem_union.1 hq with h | h
  · obtain ⟨r, hr, hq'⟩ := mem_biUnion.1 h
    have h1 := lt2_mem_PB hq'
    have h2 := ((mem_filter.1 hr).2).2.2
    simp only at h1; rw [b1_ham_comm] at h2; omega
  · have := (lt2_mem_PB h).1; simp only [b1_ham_self] at this; omega

lemma lt2ZP_congr (s : State N) {w w' : Param N} (h : ∀ q ∉ lt2Priv s w, w q.1 q.2 = w' q.1 q.2)
    (p : Fin N × Fin N) : lt2ZP s w' p ↔ lt2ZP s w p := by
  classical
  have hP : lt2Priv s w' = lt2Priv s w := lt2Priv_stop h
  have hHalf : lt2Half s w' = lt2Half s w := by
    funext r j; unfold lt2Half; rw [hP]
    split_ifs with hq
    · rfl
    · exact (h (r, j) hq).symm
  have hEps : lt2Eps s w' = lt2Eps s w := by unfold lt2Eps; rw [lt2H_stop h]
  unfold lt2ZP lt2Fdif; rw [hHalf, hEps]

lemma lt2Good_congr (s : State N) {w w' : Param N} (h : ∀ q ∉ lt2Priv s w, w q.1 q.2 = w' q.1 q.2) :
    lt2Good s w' = lt2Good s w := by
  classical
  have hs : ∀ j, w' s j = w s j := fun j => (h (s, j) (lt2_row_s_notPriv s w j)).symm
  unfold lt2Good lt2Weak
  refine Finset.filter_congr fun p _ => ?_
  rw [lt2ZP_congr s h p, hs, hs]

lemma lt2VF_congr (s : State N) {w w' : Param N} (h : ∀ q ∉ lt2Priv s w, w q.1 q.2 = w' q.1 q.2) :
    lt2VF s w' ↔ lt2VF s w := by
  classical
  have hH : lt2H s w' = lt2H s w := lt2H_stop h
  have hrow : ∀ r ∈ lt2H s w, w' r = w r := fun r hr => funext fun j =>
    (h (r, j) (lt2_row_not_Priv (lt2_heavy_not_light ((mem_filter.1 hr).2).1)
      (by have := ((mem_filter.1 hr).2).2.2; omega) j)).symm
  unfold lt2VF
  rw [hH]
  refine forall₂_congr fun j β => ?_
  rw [Finset.sum_congr rfl fun r hr => by rw [hrow r (mem_filter.1 hr).1]]

/-- **The conditional product bound.** -/
theorem lt2_Ystar_prob (s : State N) (hθ : lt2θ N ≤ sigN N / (14 * 16 * lt2x)) :
    cubeM N (lt2Ystar s) ≤ ENNReal.ofReal (Real.exp (-(lt2p2 * (((lt2m N : ℝ)) ^ 2 / 4)))) := by
  classical
  have hσ : 0 < sigN N := by unfold sigN; positivity
  refine lt2_cond_priv s (lt2_mset_Ystar s) fun A w hA => ?_
  subst hA
  have hag := lt2_replE_agree s w
  by_cases hc : lt2VF s w ∧ ((lt2m N : ℝ)) ^ 2 / 4 ≤ ((lt2Good s w).card : ℝ)
  · have hsub : {η | replE (lt2Priv s w) w η ∈ lt2Ystar s} ⊆
        {η | ∀ p ∈ lt2Good s w, ¬ lt2Succ s (replE (lt2Priv s w) w η) p.1 p.2 lt2x lt2ρ} := by
      intro η hη
      simp only [lt2Ystar, Set.mem_setOf_eq] at hη ⊢
      rw [lt2Good_congr s (hag η)] at hη
      exact hη.2.2
    refine (measure_mono hsub).trans ?_
    have hG : ∀ p ∈ lt2Good s w, p.1 ∈ lt2D1 N ∧ p.2 ∈ lt2D2 N := fun p hp => by
      unfold lt2Good at hp; exact mem_product.1 (mem_filter.1 hp).1
    have hsd : ∀ p ∈ lt2Good s w, ∀ c u v, sigN N / 14 ≤ lt2sd s w p.1 p.2 c u v := fun p _ c u v =>
      lt2_sd_ge s w c u v hc.1
    refine (lt2_nosucc_prob s w (by unfold lt2x; norm_num) lt2ρ_nonneg (by have := lt2ρ_le; linarith)
      (lt2Good s w) hG (fun p hp c u v => ?_) (fun p hp c u v r _ => ?_)).trans (ENNReal.ofReal_le_ofReal ?_)
    · have h1 := hsd p hp c u v
      unfold lt2sd at h1
      have h2 : 0 < Real.sqrt (∑ r ∈ lt2Hf s w p.1 p.2 c u v, lt2gNs (w r) ^ 2 / 12) := lt_of_lt_of_le
        (by positivity) h1
      exact Real.sqrt_pos.1 h2
    · have h1 := hsd p hp c u v
      have h2 := lt2gNs_le (w r)
      calc lt2gNs (w r) ≤ lt2θ N := h2
        _ ≤ sigN N / (14 * 16 * lt2x) := hθ
        _ = sigN N / 14 / (16 * lt2x) := by ring
        _ ≤ lt2sd s w p.1 p.2 c u v / (16 * lt2x) :=
            div_le_div_of_nonneg_right h1 (by unfold lt2x; norm_num)
    · refine Real.exp_le_exp.2 (neg_le_neg ?_)
      have hp2 := lt2p2_pos
      unfold lt2p2 at hp2 ⊢
      exact mul_le_mul_of_nonneg_left hc.2 hp2.le
  · have hempty : {η | replE (lt2Priv s w) w η ∈ lt2Ystar s} = ∅ := by
      ext η
      simp only [lt2Ystar, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -⟩
      rw [lt2VF_congr s (hag η)] at h1
      rw [lt2Good_congr s (hag η)] at h2
      exact hc ⟨h1, h2⟩
    rw [hempty, measure_empty]; exact zero_le

end Census
end IIT
