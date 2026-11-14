/-
Census of IIT 2.0, Proposition `prop:rate` of the note `pc2-limit.tex`:
for every sequence of current states, eventually `P(not C₂) ≤ exp(-2N)`.
-/
import IIT2.Census.RateAsymp

namespace IIT2

open MeasureTheory Filter Topology Set

lemma measurableSet_cube (N : ℕ) : MeasurableSet (cube N) := by
  have : cube N = Set.univ.pi (fun _ : Fin N => Set.univ.pi (fun _ : State N => Icc (0 : ℝ) 1)) := by
    ext z; simp only [cube, Set.mem_setOf_eq, Set.mem_univ_pi]
  rw [this]
  exact MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- Transport of a cube event to the flat aligned space. -/
lemma volume_cube_event (N : ℕ) (x₁ : State N) (P : UnitTPM N → Prop) :
    volume {z ∈ cube N | P (tpmOf z)} =
      μP N {ω | P (tpmOf (Function.curry (reflect x₁ ω)))} := by
  have h1 : {z ∈ cube N | P (tpmOf z)} = {z | P (tpmOf z)} ∩ cube N := by
    ext z; simp [and_comm]
  rw [h1, ← Measure.restrict_apply' (measurableSet_cube N), volume_restrict_cube, μnest_apply]
  rw [← (mp_reflect x₁).measure_preimage_equiv]
  rfl

/-- **Rate** (Proposition `prop:rate`): for every sequence of current states, eventually
`P(the whole system is not the main complex) ≤ exp(-2N)`. -/
theorem volume_not_wholeIsMainComplex_le (s : ∀ N, State N) :
    ∀ᶠ N in atTop, volume {z ∈ cube N | ¬ WholeIsMainComplex (tpmOf z) (s N)} ≤
      ENNReal.ofReal (Real.exp (-(2 * N))) := by
  filter_upwards [rateB_le, ev_side] with N hB ⟨hN, hN3, hL⟩
  rw [volume_cube_event N (s N) (fun sys => ¬ WholeIsMainComplex sys (s N))]
  have hsub : {ω : Ωf N | ¬ WholeIsMainComplex (tpmOf (Function.curry (reflect (s N) ω))) (s N)} ⊆
      {ω | ¬ GoodA (qω ω) (Lr N)} := by
    intro ω hω hG
    exact hω (wholeIsMainComplex_of_goodA (tpmOf (Function.curry (reflect (s N) ω))) (s N)
      (Lr N) (by unfold Lr; omega) hL (by rw [qOf_reflect]; exact hG))
  have hreal := (measureReal_mono (μ := μP N) hsub).trans
    ((rate_bad_bound (Lr N) (by unfold Lr; omega) hN hN3).trans hB)
  calc μP N {ω | ¬ WholeIsMainComplex (tpmOf (Function.curry (reflect (s N) ω))) (s N)}
      = ENNReal.ofReal ((μP N).real
          {ω | ¬ WholeIsMainComplex (tpmOf (Function.curry (reflect (s N) ω))) (s N)}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- Real-valued form. -/
theorem volumeReal_not_wholeIsMainComplex_le (s : ∀ N, State N) :
    ∀ᶠ N in atTop, (volume {z ∈ cube N | ¬ WholeIsMainComplex (tpmOf z) (s N)}).toReal ≤
      Real.exp (-(2 * N)) := by
  filter_upwards [volume_not_wholeIsMainComplex_le s] with N h
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at this

end IIT2

#print axioms IIT2.volume_not_wholeIsMainComplex_le
#print axioms IIT2.volumeReal_not_wholeIsMainComplex_le
