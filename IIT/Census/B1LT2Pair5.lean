/-
Census, B1 lemma LT2, module M6b-7: no good pair succeeds — the conditional product bound.

`lt2Succ s w a b x ρ :⇔ ∀ κ, w ∈ X_κ(w)` (success of the pair read on `w` itself).
`lt2_nosucc_prob`: for `w` and a finset `G ⊆ D₁ × D₂` of pairs each satisfying the small-ball hypotheses,
`P_η(∀ p ∈ G, ¬ Succ_p(replE (Priv w) w η)) ≤ e^{-p₂ |G|}`, `p₂ = (ρ e^{-225x²}/4)^16`.
-/
import IIT.Census.B1LT2Pair4

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- Success of a pair, read on the parameter itself. -/
def lt2Succ (s : State N) (w : Param N) (a b : Fin N) (x ρ : ℝ) : Prop :=
  ∀ κ : Bool × Bool × Bool × Bool, w ∈ lt2X s w a b x ρ κ

lemma lt2_det_succ (s : State N) (w : Param N) (a b : Fin N) (x ρ : ℝ) :
    DetOnE (lt2CP s w a b) (⋂ κ ∈ (univ : Finset (Bool × Bool × Bool × Bool)), lt2X s w a b x ρ κ) := by
  intro η η' h
  simp only [Set.mem_iInter, mem_univ, forall_const]
  refine forall_congr' fun κ => ?_
  exact (lt2_det_X s w a b x ρ κ).mono (fun q hq => mem_biUnion.2 ⟨κ, mem_univ _, hq⟩) η η' h

lemma lt2_mset_succ (s : State N) (w : Param N) (a b : Fin N) (x ρ : ℝ) :
    MeasurableSet (⋂ κ ∈ (univ : Finset (Bool × Bool × Bool × Bool)), lt2X s w a b x ρ κ) :=
  MeasurableSet.biInter (Set.to_countable _) fun κ _ => lt2_mset_X s w a b x ρ κ

/-- **No good pair succeeds.** -/
theorem lt2_nosucc_prob (s : State N) (w : Param N) {x ρ : ℝ} (hx : 1 ≤ x) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (G : Finset (Fin N × Fin N)) (hG : ∀ p ∈ G, p.1 ∈ lt2D1 N ∧ p.2 ∈ lt2D2 N)
    (hV : ∀ p ∈ G, ∀ c u v, 0 < ∑ r ∈ lt2Hf s w p.1 p.2 c u v, lt2gNs (w r) ^ 2 / 12)
    (hc : ∀ p ∈ G, ∀ c u v, ∀ r ∈ lt2Hf s w p.1 p.2 c u v,
      lt2gNs (w r) ≤ lt2sd s w p.1 p.2 c u v / (16 * x)) :
    cubeM N {η | ∀ p ∈ G, ¬ lt2Succ s (replE (lt2Priv s w) w η) p.1 p.2 x ρ} ≤
      ENNReal.ofReal (Real.exp (-((ρ * (Real.exp (-(225 * x ^ 2)) / 4)) ^ 16 * G.card))) := by
  classical
  haveI : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  set p2 := (ρ * (Real.exp (-(225 * x ^ 2)) / 4)) ^ 16
  have hp20 : 0 ≤ p2 := by positivity
  have hp21 : p2 ≤ 1 := by
    have h1 : Real.exp (-(225 * x ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have h2 : ρ * (Real.exp (-(225 * x ^ 2)) / 4) ≤ 1 := by nlinarith [Real.exp_pos (-(225 * x ^ 2))]
    exact pow_le_one₀ (by positivity) h2
  set S : Fin N × Fin N → Set (Param N) := fun p =>
    ⋂ κ ∈ (univ : Finset (Bool × Bool × Bool × Bool)), lt2X s w p.1 p.2 x ρ κ
  have hset : {η | ∀ p ∈ G, ¬ lt2Succ s (replE (lt2Priv s w) w η) p.1 p.2 x ρ} = ⋂ p ∈ G, (S p)ᶜ := by
    ext η
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff, S, mem_univ, forall_const]
    refine forall₂_congr fun p hp => not_congr ?_
    unfold lt2Succ
    exact forall_congr' fun κ => lt2X_replE s w η (hG p hp).1 (hG p hp).2 x ρ κ
  rw [hset, cubeM_iInter_eq_prod_of_detOnE G (fun p => lt2CP s w p.1 p.2)
    (fun p hp q hq hpq => lt2_CP_disj (hG p hp).1 (hG p hp).2 (hG q hq).1 (hG q hq).2 hpq)
    (fun p _ => (lt2_mset_succ s w p.1 p.2 x ρ).compl) (fun p _ => (lt2_det_succ s w p.1 p.2 x ρ).compl)]
  have hone : ∀ p ∈ G, cubeM N (S p)ᶜ ≤ ENNReal.ofReal (1 - p2) := fun p hp => by
    rw [measure_compl (lt2_mset_succ s w p.1 p.2 x ρ) (measure_ne_top _ _), measure_univ,
      ENNReal.ofReal_sub _ hp20, ENNReal.ofReal_one]
    exact tsub_le_tsub_left (lt2_pair_succ_prob s w (lt2_D1_ne_D2 (hG p hp).1 (hG p hp).2) hx hρ0 hρ1
      (hV p hp) (hc p hp)) 1
  calc ∏ p ∈ G, cubeM N (S p)ᶜ ≤ ∏ _p ∈ G, ENNReal.ofReal (1 - p2) := Finset.prod_le_prod' hone
    _ = ENNReal.ofReal ((1 - p2) ^ G.card) := by
        rw [Finset.prod_const, ENNReal.ofReal_pow (by linarith)]
    _ ≤ ENNReal.ofReal (Real.exp (-(p2 * G.card))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc (1 - p2) ^ G.card ≤ Real.exp (-p2) ^ G.card :=
              pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-p2)]) _
          _ = Real.exp (-(p2 * G.card)) := by rw [← Real.exp_nat_mul]; ring_nf

end Census
end IIT
