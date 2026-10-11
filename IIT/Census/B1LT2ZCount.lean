/-
Census, B1 lemma LT2, module M6f-2: few pairs with a large shared difference.

`Z(w) = {p ∈ D₁ × D₂ : some column/pattern has |F(t₀) - F(t)| ≥ 16κσ + 2ε}` (shared data only).
`lt2_Z_count`: eventually `P(#Z ≥ m²/4 + 1) ≤ 16 e^{-2N}` (count transfer + reflection + adverse count).
-/
import IIT.Census.B1LT2EffCount

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

lemma lt2_mset_memPriv (s : State N) (q : State N × Fin N) : MeasurableSet {w : Param N | q ∈ lt2Priv s w} := by
  classical
  have e : {w : Param N | q ∈ lt2Priv s w} = ⋃ A : Finset (State N × Fin N),
      ({w | lt2Priv s w = A} ∩ {_w | q ∈ A}) := by
    ext w; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨A, hA, h⟩ => hA ▸ h⟩
  rw [e]
  exact MeasurableSet.iUnion fun A => (lt2_mset_Priv s A).inter (MeasurableSet.const _)

lemma lt2_meas_half (s : State N) : Measurable (lt2Half (N := N) s) := by
  classical
  refine measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun j => ?_
  show Measurable fun w : Param N => lt2Half s w r j
  unfold lt2Half
  exact Measurable.ite (lt2_mset_memPriv s (r, j)) measurable_const
    ((measurable_pi_apply j).comp (measurable_pi_apply r))

lemma lt2_meas_cardH (s : State N) : Measurable fun w : Param N => ((lt2H s w).card : ℝ) := by
  classical
  have e : (fun w : Param N => ((lt2H s w).card : ℝ)) =
      fun w => ∑ r : State N, {w : Param N | r ∈ lt2H s w}.indicator (fun _ => (1 : ℝ)) w := by
    funext w
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [Finset.sum_boole]; simp
  rw [e]
  exact Finset.measurable_sum _ fun r _ => measurable_const.indicator (lt2_mset_memH s r)

lemma lt2_meas_eps (s : State N) : Measurable (lt2Eps (N := N) s) := by
  unfold lt2Eps
  exact (((lt2_meas_cardH s).mul_const _).mul_const _).add_const _

/-- The shared differences. -/
noncomputable def lt2Fdif (s : State N) (w : Param N) (a b : Fin N) (c u v : Bool) : ℝ :=
  |lt2NumNs (lt2Half s w) {a, b} (lt2pat a b false false) (lt2col a b c) -
    lt2NumNs (lt2Half s w) {a, b} (lt2pat a b u v) (lt2col a b c)|

/-- A large shared difference. -/
def lt2ZP (s : State N) (w : Param N) (p : Fin N × Fin N) : Prop :=
  ∃ c u v : Bool, (u, v) ≠ (false, false) ∧ 16 * lt2κ * sigN N + 2 * lt2Eps s w ≤ lt2Fdif s w p.1 p.2 c u v

/-- The pairs with a large shared difference. -/
noncomputable def lt2Z (s : State N) (w : Param N) : Finset (Fin N × Fin N) := by
  classical exact (lt2D1 N ×ˢ lt2D2 N).filter (lt2ZP s w)

/-- A large true difference. -/
def lt2YP (w : Param N) (p : Fin N × Fin N) : Prop :=
  ∃ c u v : Bool, (u, v) ≠ (false, false) ∧ 16 * lt2κ * sigN N ≤
    |lt2NumNs w {p.1, p.2} (lt2pat p.1 p.2 false false) (lt2col p.1 p.2 c) -
      lt2NumNs w {p.1, p.2} (lt2pat p.1 p.2 u v) (lt2col p.1 p.2 c)|

lemma lt2_meas_Fdif (s : State N) (a b : Fin N) (c u v : Bool) :
    Measurable fun w : Param N => lt2Fdif s w a b c u v := by
  unfold lt2Fdif
  exact (((lt2_meas_NumNs _ _ _).comp (lt2_meas_half s)).sub ((lt2_meas_NumNs _ _ _).comp (lt2_meas_half s))).abs

lemma lt2_mset_ZP (s : State N) (p : Fin N × Fin N) : MeasurableSet {w : Param N | lt2ZP s w p} := by
  unfold lt2ZP
  simp only [Set.setOf_exists]
  refine MeasurableSet.iUnion fun c => MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun v => ?_
  rw [Set.setOf_and]
  exact (MeasurableSet.const _).inter
    (measurableSet_le (measurable_const.add ((lt2_meas_eps s).const_mul _)) (lt2_meas_Fdif s _ _ c u v))

lemma lt2_mset_YP (p : Fin N × Fin N) : MeasurableSet {w : Param N | lt2YP w p} := by
  unfold lt2YP
  simp only [Set.setOf_exists]
  refine MeasurableSet.iUnion fun c => MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun v => ?_
  rw [Set.setOf_and]
  exact (MeasurableSet.const _).inter
    (measurableSet_le measurable_const ((lt2_meas_NumNs _ _ _).sub (lt2_meas_NumNs _ _ _)).abs)

/-- `Z` reads only the shared data. -/
lemma lt2Z_congr (s : State N) {w w' : Param N} (h : ∀ q ∉ lt2Priv s w, w q.1 q.2 = w' q.1 q.2) :
    lt2Z s w' = lt2Z s w := by
  classical
  have hP : lt2Priv s w' = lt2Priv s w := lt2Priv_stop h
  have hHalf : lt2Half s w' = lt2Half s w := by
    funext r j; unfold lt2Half; rw [hP]
    split_ifs with hq
    · rfl
    · exact (h (r, j) hq).symm
  have hEps : lt2Eps s w' = lt2Eps s w := by unfold lt2Eps; rw [lt2H_stop h]
  unfold lt2Z lt2ZP lt2Fdif
  rw [hHalf, hEps]

lemma lt2_mset_cardZ (s : State N) (k : ℕ) : MeasurableSet {w : Param N | k ≤ (lt2Z s w).card} := by
  classical
  have e : ∀ w : Param N, ((lt2Z s w).card : ℝ) =
      ∑ p ∈ lt2D1 N ×ˢ lt2D2 N, {w : Param N | lt2ZP s w p}.indicator (fun _ => (1 : ℝ)) w := by
    intro w
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [Finset.sum_boole]; unfold lt2Z; simp
  have : {w : Param N | k ≤ (lt2Z s w).card} =
      {w | (k : ℝ) ≤ ∑ p ∈ lt2D1 N ×ˢ lt2D2 N, {w : Param N | lt2ZP s w p}.indicator (fun _ => (1 : ℝ)) w} := by
    ext w; simp only [Set.mem_setOf_eq]; rw [← e w]; exact_mod_cast Iff.rfl
  rw [this]
  exact measurableSet_le measurable_const (Finset.measurable_sum _ fun p _ =>
    measurable_const.indicator (lt2_mset_ZP s p))

/-- A large true difference makes the pair adverse. -/
lemma lt2_YP_adv {w : Param N} {p : Fin N × Fin N} (hp : p ∈ lt2D1 N ×ˢ lt2D2 N) (hY : lt2YP w p) :
    p ∈ lt2AdvPairs w := by
  classical
  obtain ⟨ha, hb⟩ := mem_product.1 hp
  unfold lt2AdvPairs
  refine mem_filter.2 ⟨hp, ?_⟩
  by_contra hno
  push_neg at hno
  obtain ⟨c, u, v, -, hle⟩ := hY
  have hσ : 0 < sigN N := by unfold sigN; positivity
  have h := lt2_visible_adv w ha hb c (lt2pat p.1 p.2 false false) (lt2pat p.1 p.2 u v)
    (g := lt2κ * sigN N) (by unfold lt2κ; positivity) fun k hk _ => hno k hk
  have : 0 < lt2κ * sigN N := by unfold lt2κ; positivity
  linarith

/-- **Few pairs with a large shared difference.** -/
theorem lt2_Z_count : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N {w | lt2m N ^ 2 / 4 + 1 ≤ (lt2Z s w).card} ≤ ENNReal.ofReal (16 * Real.exp (-(2 * (N : ℝ)))) := by
  classical
  filter_upwards [lt2_adv_total, eventually_ge_atTop 100] with N hadv hN s
  set m := lt2m N
  set U := lt2D1 N ×ˢ lt2D2 N
  have hUc : U.card = m * m := by rw [card_product, lt2_card_D1, lt2_card_D2]
  have hm : 5 ≤ m := by unfold m lt2m; omega
  have hU : 0 < U.card := by rw [hUc]; positivity
  set mZ := m ^ 2 / 4 + 1
  have hσ : 0 < sigN N := by unfold sigN; positivity
  have htr := lt2_count_transfer s U hU (lt2Z s) (fun w => filter_subset _ _) (fun w w' h => lt2Z_congr s h)
    (m := mZ) (lt2_mset_cardZ s mZ) (fun p => {w : Param N | lt2YP w p}) (fun p => lt2_mset_YP p)
    (fun w p hp => by
      have hp' := mem_filter.1 hp
      obtain ⟨ha, hb⟩ := mem_product.1 hp'.1
      obtain ⟨c, u, v, huv, hthr⟩ := hp'.2
      refine (lt2_reflect_half s w ha hb c (lt2pat p.1 p.2 false false) (lt2pat p.1 p.2 u v)
        (M := 16 * lt2κ * sigN N + 2 * lt2Eps s w) hthr).trans (measure_mono fun η hη => ?_)
      simp only [Set.mem_setOf_eq] at hη ⊢
      exact ⟨c, u, v, huv, by linarith⟩)
  -- the right side is controlled by the adverse pairs
  have hsub : {w : Param N | (mZ : ℝ) / 4 ≤ ((U.filter fun p => w ∈ {w : Param N | lt2YP w p}).card : ℝ)} ⊆
      {w | ((lt2m N : ℝ)) ^ 2 / 16 ≤ ((lt2AdvPairs w).card : ℝ)} := by
    intro w hw
    simp only [Set.mem_setOf_eq] at hw ⊢
    have h1 : (U.filter fun p => lt2YP w p) ⊆ lt2AdvPairs w := fun p hp =>
      lt2_YP_adv (mem_filter.1 hp).1 (mem_filter.1 hp).2
    have h2 : ((U.filter fun p => lt2YP w p).card : ℝ) ≤ (lt2AdvPairs w).card := by
      exact_mod_cast Finset.card_le_card h1
    have h3 : ((lt2m N : ℝ)) ^ 2 / 16 ≤ (mZ : ℝ) / 4 := by
      have : (m : ℝ) ^ 2 ≤ 4 * (mZ : ℝ) := by
        have : m ^ 2 ≤ 4 * mZ := by unfold mZ; omega
        exact_mod_cast this
      linarith
    linarith
  have h1 := htr.trans ((measure_mono hsub).trans hadv)
  have hfac : ENNReal.ofReal (1 / 16) ≤ ENNReal.ofReal ((mZ : ℝ) / (4 * U.card)) := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hUc, le_div_iff₀ (by positivity)]
    have : m * m ≤ 4 * mZ := by unfold mZ; rw [sq]; omega
    have : ((m * m : ℕ) : ℝ) ≤ 4 * (mZ : ℝ) := by exact_mod_cast this
    push_cast at this ⊢; linarith
  have h2 : cubeM N {w | mZ ≤ (lt2Z s w).card} * ENNReal.ofReal (1 / 16) ≤
      ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := (mul_le_mul' le_rfl hfac).trans h1
  calc cubeM N {w | mZ ≤ (lt2Z s w).card}
      = cubeM N {w | mZ ≤ (lt2Z s w).card} * ENNReal.ofReal (1 / 16) * 16 := by
        rw [mul_assoc, ← ENNReal.ofReal_ofNat 16, ← ENNReal.ofReal_mul (by norm_num)]; norm_num
    _ ≤ ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) * 16 := mul_le_mul' h2 le_rfl
    _ = ENNReal.ofReal (16 * Real.exp (-(2 * (N : ℝ)))) := by
        rw [← ENNReal.ofReal_ofNat 16, ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

end Census
end IIT
