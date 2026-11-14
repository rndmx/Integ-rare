/-
Census of IIT 2.0, main theorem (Theorem 6 of the note `pc2-limit.tex`):
under the uniform measure on general TPMs, the probability that the whole system is the
main complex tends to `1`, uniformly in the current state.

Parameter space: `z : Fin N → State N → ℝ`, measure `volume` restricted to the cube
`[0,1]^(Fin N × State N)`.  The TPM `tpmOf z` has `prob i s true = clamp (z i s)`,
`prob i s false = 1 - clamp (z i s)`; on the cube `clamp (z i s) = z i s`, so this is the TPM
of the note, and `tpmOf` is a valid `UnitTPM` for every `z`.
-/
import IIT2.Census.Asymptotics

namespace IIT2

open MeasureTheory Filter Topology Set

variable {N : ℕ}

/-- The cube `[0,1]^(Fin N × State N)`. -/
def cube (N : ℕ) : Set (Fin N → State N → ℝ) := {z | ∀ i s, z i s ∈ Icc (0 : ℝ) 1}

/-- The TPM with `prob i s true = z i s` (clamped to `[0,1]`). -/
noncomputable def tpmOf (z : Fin N → State N → ℝ) : UnitTPM N where
  prob i s b := if b then clamp (z i s) else 1 - clamp (z i s)
  nonneg i s b := by
    cases b
    · simp only [Bool.false_eq_true, if_false]; linarith [clamp_le_one (z i s)]
    · simp only [if_true]; exact clamp_nonneg _
  normalized i s := by simp

lemma clamp_one_sub (u : ℝ) : clamp (1 - u) = 1 - clamp u := by
  unfold clamp
  rcases le_total u 0 with h | h
  · rw [min_eq_right (by linarith : u ≤ 1), max_eq_left h, min_eq_left (by linarith : (1:ℝ) ≤ 1 - u),
      max_eq_right (by norm_num : (0:ℝ) ≤ 1)]; ring
  · rcases le_total u 1 with h' | h'
    · rw [min_eq_right h', max_eq_right h, min_eq_right (by linarith : 1 - u ≤ 1),
        max_eq_right (by linarith : 0 ≤ 1 - u)]
    · rw [min_eq_left h', max_eq_right (by norm_num : (0:ℝ) ≤ 1),
        min_eq_right (by linarith : 1 - u ≤ 1), max_eq_left (by linarith : 1 - u ≤ 0)]; ring

/-! ## Transport to the flat product space -/

/-- The nested product measure. -/
noncomputable def μnest (N : ℕ) : Measure (Fin N → State N → ℝ) :=
  Measure.pi (fun _ : Fin N => Measure.pi (fun _ : State N => unif))

lemma volume_restrict_cube : (volume : Measure (Fin N → State N → ℝ)).restrict (cube N) = μnest N := by
  have hc : cube N = Set.univ.pi (fun _ : Fin N => Set.univ.pi (fun _ : State N => Icc (0 : ℝ) 1)) := by
    ext z; simp only [cube, Set.mem_setOf_eq, Set.mem_univ_pi]
  rw [hc, volume_pi, Measure.restrict_pi_pi]
  unfold μnest
  congr 1; funext i
  rw [volume_pi, Measure.restrict_pi_pi]
  rfl

lemma map_uncurry_μnest :
    Measure.map (MeasurableEquiv.curry (Fin N) (State N) ℝ).symm (μnest N) = μP N := by
  unfold μP
  refine (Measure.pi_eq fun t ht => ?_).symm
  rw [Measure.map_apply (MeasurableEquiv.curry (Fin N) (State N) ℝ).symm.measurable
    (MeasurableSet.univ_pi ht)]
  have : (MeasurableEquiv.curry (Fin N) (State N) ℝ).symm ⁻¹' (Set.univ.pi t) =
      Set.univ.pi (fun i => Set.univ.pi (fun c => t (i, c))) := by
    ext z
    simp [MeasurableEquiv.coe_curry_symm, Set.mem_pi]
  rw [this]
  unfold μnest
  rw [Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

lemma μnest_apply (E : Set (Fin N → State N → ℝ)) :
    μnest N E = μP N ((MeasurableEquiv.curry (Fin N) (State N) ℝ) ⁻¹' E) := by
  rw [← map_uncurry_μnest, MeasurableEquiv.map_apply]
  congr 1

/-- Reflection `ω ↦ (p ↦ ω p or 1 - ω p)`, aligning the current state. -/
noncomputable def reflect (x₁ : State N) (ω : Ωf N) : Ωf N :=
  fun p => if x₁ p.1 then ω p else 1 - ω p

lemma reflect_involutive (x₁ : State N) : Function.Involutive (reflect x₁) := fun ω => by
  funext p; unfold reflect; split_ifs <;> ring

lemma measurable_reflect (x₁ : State N) : Measurable (reflect x₁) := by
  refine measurable_pi_iff.mpr fun p => ?_
  unfold reflect
  split_ifs
  · exact measurable_pi_apply p
  · exact measurable_const.sub (measurable_pi_apply p)

noncomputable def reflectEquiv (x₁ : State N) : Ωf N ≃ᵐ Ωf N where
  toFun := reflect x₁
  invFun := reflect x₁
  left_inv := reflect_involutive x₁
  right_inv := reflect_involutive x₁
  measurable_toFun := measurable_reflect x₁
  measurable_invFun := measurable_reflect x₁

lemma mp_one_sub : MeasurePreserving (fun u : ℝ => 1 - u) unif unif := by
  have h := (Measure.measurePreserving_sub_left volume (1 : ℝ)).restrict_preimage
    (measurableSet_Icc (a := (0 : ℝ)) (b := 1))
  have hpre : (fun u : ℝ => 1 - u) ⁻¹' Icc 0 1 = Icc 0 1 := by
    ext u; simp only [Set.mem_preimage, Set.mem_Icc]; constructor <;> intro h <;>
      constructor <;> linarith [h.1, h.2]
  rw [hpre] at h
  exact h

lemma mp_reflect (x₁ : State N) : MeasurePreserving (reflectEquiv x₁) (μP N) (μP N) := by
  have := measurePreserving_pi (fun _ : Fin N × State N => unif) (fun _ => unif)
    (f := fun p u => if x₁ p.1 then u else 1 - u) (fun p => by
      by_cases h : x₁ p.1
      · simp only [h, if_true]; exact MeasurePreserving.id unif
      · simp only [h, Bool.false_eq_true, if_false]; exact mp_one_sub)
  exact this

lemma qOf_reflect (x₁ : State N) (ω : Ωf N) :
    qOf (tpmOf (Function.curry (reflect x₁ ω))) x₁ = qω ω := by
  funext l c
  simp only [qOf, tpmOf, qω, reflect, Function.curry]
  cases h : x₁ l
  · simp only [Bool.false_eq_true, if_false]; rw [clamp_one_sub]; ring
  · simp

/-! ## The main theorem -/

lemma eventually_two_L_lt : ∀ᶠ N : ℕ in atTop, 2 * Lsel N < N := by
  have hB := (Real.isLittleO_log_id_atTop).bound (show (0 : ℝ) < 1 / 1000 by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hB, eventually_ge_atTop 200] with N hN h1
  simp only [Real.norm_eq_abs, id] at hN
  have hNr : (200 : ℝ) ≤ N := by exact_mod_cast h1
  have hN' : |(N : ℝ)| = N := abs_of_nonneg (Nat.cast_nonneg N)
  rw [hN'] at hN
  have hlog := (le_abs_self _).trans hN
  have hnl := natLog_le N (by omega)
  have hl2 := log_two_gt
  have : (Nat.log 2 N : ℝ) * (69 / 100) ≤ (1 / 1000) * N := by
    have : (Nat.log 2 N : ℝ) * (69 / 100) ≤ (Nat.log 2 N : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    linarith
  have hr : (2 * Lsel N : ℝ) < N := by
    unfold Lsel; push_cast; nlinarith
  exact_mod_cast hr

/-- **Main theorem** (`P(C₂) → 1`): for every sequence of current states, the probability
under the uniform measure on general TPMs that the whole system is the main complex of IIT 2.0
tends to `1`. -/
theorem tendsto_volume_wholeIsMainComplex (s : ∀ N, State N) :
    Tendsto (fun N => volume {z ∈ cube N | WholeIsMainComplex (tpmOf z) (s N)}) atTop (𝓝 1) := by
  -- the event in the flat space
  set E : ∀ N, Set (Ωf N) := fun N =>
    {ω | WholeIsMainComplex (tpmOf (Function.curry (reflect (s N) ω))) (s N)}
  have hvol : ∀ N, volume {z ∈ cube N | WholeIsMainComplex (tpmOf z) (s N)} = μP N (E N) := by
    intro N
    have h1 : {z ∈ cube N | WholeIsMainComplex (tpmOf z) (s N)} =
        {z | WholeIsMainComplex (tpmOf z) (s N)} ∩ cube N := by
      ext z; simp [and_comm]
    have hcm : MeasurableSet (cube N) := by
      have : cube N = Set.univ.pi (fun _ : Fin N => Set.univ.pi (fun _ : State N => Icc (0 : ℝ) 1)) := by
        ext z; simp only [cube, Set.mem_setOf_eq, Set.mem_univ_pi]
      rw [this]
      exact MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_Icc
    rw [h1, ← Measure.restrict_apply' hcm, volume_restrict_cube, μnest_apply]
    rw [← (mp_reflect (s N)).measure_preimage_equiv]
    rfl
  -- lower bound by the good event
  have hlow : ∀ᶠ N in atTop, 1 - badB N ≤ (μP N).real (E N) := by
    filter_upwards [eventually_two_L_lt, eventually_ge_atTop 1] with N hL hN
    have hsub : {ω | GoodA (qω ω) (Lsel N)} ⊆ E N := by
      intro ω hω
      have := wholeIsMainComplex_of_goodA (tpmOf (Function.curry (reflect (s N) ω))) (s N)
        (Lsel N) (by unfold Lsel; omega) hL (by rw [qOf_reflect]; exact hω)
      exact this
    have hbad := bad_bound (N := N) (Lsel N) (by unfold Lsel; omega) hN
    have hu : (1 : ℝ) ≤ (μP N).real {ω | GoodA (qω ω) (Lsel N)} +
        (μP N).real {ω | ¬ GoodA (qω ω) (Lsel N)} := by
      have := measureReal_union_le (μ := μP N) {ω | GoodA (qω ω) (Lsel N)}
        {ω | ¬ GoodA (qω ω) (Lsel N)}
      have hU : ({ω | GoodA (qω ω) (Lsel N)} ∪ {ω | ¬ GoodA (qω ω) (Lsel N)} : Set (Ωf N)) =
          Set.univ := by
        ext ω; simp [em]
      rw [hU, probReal_univ] at this
      exact this
    have hm := measureReal_mono (μ := μP N) hsub
    unfold badB
    linarith
  have hup : ∀ N, (μP N).real (E N) ≤ 1 := fun N => by
    have := measureReal_mono (μ := μP N) (Set.subset_univ (E N)); rwa [probReal_univ] at this
  have hreal : Tendsto (fun N => (μP N).real (E N)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun N => 1 - badB N) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub badB_tendsto
      rw [sub_zero] at this; exact this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 tendsto_const_nhds hlow
      (Eventually.of_forall hup)
  have hEN : ∀ N, μP N (E N) = ENNReal.ofReal ((μP N).real (E N)) := fun N => by
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simp_rw [hvol, hEN]
  have := ENNReal.tendsto_ofReal hreal
  rw [ENNReal.ofReal_one] at this
  exact this

end IIT2

#print axioms IIT2.tendsto_volume_wholeIsMainComplex
