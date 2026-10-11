/-
Census, B1 lemma LT2 at a general level: the conditional product bound with a general small-ball level `x`.
-/
import IIT.Census.B1LT2L

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

noncomputable def lt2p2X (x : ℝ) : ℝ := (lt2ρ * (Real.exp (-(225 * x ^ 2)) / 4)) ^ 16

lemma lt2p2X_pos (x : ℝ) : 0 < lt2p2X x := by
  unfold lt2p2X lt2ρ; have := lt2γ_pos; positivity

/-- The conditional event. -/
def lt2YstarX (s : State N) (x : ℝ) : Set (Param N) :=
  {w | lt2VF s w ∧ ((lt2m N : ℝ)) ^ 2 / 4 ≤ ((lt2Good s w).card : ℝ) ∧
    ∀ p ∈ lt2Good s w, ¬ lt2Succ s w p.1 p.2 x lt2ρ}

lemma lt2_mset_YstarX (s : State N) (x : ℝ) : MeasurableSet (lt2YstarX (N := N) s x) := by
  classical
  have hcard : Measurable fun w : Param N => ((lt2Good s w).card : ℝ) := by
    have e : (fun w : Param N => ((lt2Good s w).card : ℝ)) =
        fun w => ∑ p : Fin N × Fin N, {w : Param N | p ∈ lt2Good s w}.indicator (fun _ => (1 : ℝ)) w := by
      funext w; simp only [Set.indicator_apply, Set.mem_setOf_eq]; rw [Finset.sum_boole]; simp
    rw [e]; exact Finset.measurable_sum _ fun p _ => measurable_const.indicator (lt2_mset_memGood s p)
  have e : lt2YstarX (N := N) s x = {w | lt2VF s w} ∩ ({w | ((lt2m N : ℝ)) ^ 2 / 4 ≤ ((lt2Good s w).card : ℝ)} ∩
      ⋂ p : Fin N × Fin N, ({w | p ∈ lt2Good s w}ᶜ ∪ {w | lt2Succ s w p.1 p.2 x lt2ρ}ᶜ)) := by
    ext w; simp only [lt2YstarX, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_union,
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

/-- **The conditional product bound.** -/
theorem lt2_Ystar_probX (s : State N) {x : ℝ} (hx1 : 1 ≤ x) (hθ : lt2θ N ≤ sigN N / (14 * 16 * x)) :
    cubeM N (lt2YstarX s x) ≤ ENNReal.ofReal (Real.exp (-(lt2p2X x * (((lt2m N : ℝ)) ^ 2 / 4)))) := by
  classical
  have hσ : 0 < sigN N := by unfold sigN; positivity
  refine lt2_cond_priv s (lt2_mset_YstarX s x) fun A w hA => ?_
  subst hA
  have hag := lt2_replE_agree s w
  by_cases hc : lt2VF s w ∧ ((lt2m N : ℝ)) ^ 2 / 4 ≤ ((lt2Good s w).card : ℝ)
  · have hsub : {η | replE (lt2Priv s w) w η ∈ lt2YstarX s x} ⊆
        {η | ∀ p ∈ lt2Good s w, ¬ lt2Succ s (replE (lt2Priv s w) w η) p.1 p.2 x lt2ρ} := by
      intro η hη
      simp only [lt2YstarX, Set.mem_setOf_eq] at hη ⊢
      rw [lt2Good_congr s (hag η)] at hη
      exact hη.2.2
    refine (measure_mono hsub).trans ?_
    have hG : ∀ p ∈ lt2Good s w, p.1 ∈ lt2D1 N ∧ p.2 ∈ lt2D2 N := fun p hp => by
      unfold lt2Good at hp; exact mem_product.1 (mem_filter.1 hp).1
    have hsd : ∀ p ∈ lt2Good s w, ∀ c u v, sigN N / 14 ≤ lt2sd s w p.1 p.2 c u v := fun p _ c u v =>
      lt2_sd_ge s w c u v hc.1
    refine (lt2_nosucc_prob s w hx1 lt2ρ_nonneg (by have := lt2ρ_le; linarith)
      (lt2Good s w) hG (fun p hp c u v => ?_) (fun p hp c u v r _ => ?_)).trans (ENNReal.ofReal_le_ofReal ?_)
    · have h1 := hsd p hp c u v
      unfold lt2sd at h1
      have h2 : 0 < Real.sqrt (∑ r ∈ lt2Hf s w p.1 p.2 c u v, lt2gNs (w r) ^ 2 / 12) := lt_of_lt_of_le
        (by positivity) h1
      exact Real.sqrt_pos.1 h2
    · have h1 := hsd p hp c u v
      have h2 := lt2gNs_le (w r)
      calc lt2gNs (w r) ≤ lt2θ N := h2
        _ ≤ sigN N / (14 * 16 * x) := hθ
        _ = sigN N / 14 / (16 * x) := by ring
        _ ≤ lt2sd s w p.1 p.2 c u v / (16 * x) :=
            div_le_div_of_nonneg_right h1 (by linarith)
    · refine Real.exp_le_exp.2 (neg_le_neg ?_)
      have hp2 := lt2p2X_pos x
      unfold lt2p2X at hp2 ⊢
      exact mul_le_mul_of_nonneg_left hc.2 hp2.le
  · have hempty : {η | replE (lt2Priv s w) w η ∈ lt2YstarX s x} = ∅ := by
      ext η
      simp only [lt2YstarX, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -⟩
      rw [lt2VF_congr s (hag η)] at h1
      rw [lt2Good_congr s (hag η)] at h2
      exact hc ⟨h1, h2⟩
    rw [hempty, measure_empty]; exact zero_le

end Census
end IIT
