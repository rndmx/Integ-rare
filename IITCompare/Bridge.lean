/-
Bridge between the two parameter spaces.

* IIT 4.0 (Integ-rare, `IIT.Census`): `Param N = State N → Fin N → ℝ`, `z s i` = probability that
  unit `i` is ON at `t+1` given state `s`; `tpmOf z` uses `clamp01`.
* IIT 2.0 (`IIT2`): `Fin N → State N → ℝ`, `w i s` = the same probability; `tpmOf w` uses `clamp`.

Both `State` types are `Fin N → Bool` (definitionally equal abbreviations). The bridge is the
argument swap `swapE : Param N ≃ᵐ (Fin N → State N → ℝ)`, proved volume-preserving; it maps the
cube onto the cube and the two TPMs have the same transition probabilities.
-/
import IIT2.Census.RateMain
import IIT.Census.Basic

namespace IITCompare

open MeasureTheory

variable {N : ℕ}

/-- The two state types coincide. -/
example : IIT.State N = IIT2.State N := rfl

/-- Uncurrying is volume-preserving. -/
lemma mp_uncurry (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
    MeasurePreserving (MeasurableEquiv.curry α β ℝ).symm volume volume := by
  refine ⟨(MeasurableEquiv.curry α β ℝ).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun t ht => ?_).symm
  rw [Measure.map_apply (MeasurableEquiv.curry α β ℝ).symm.measurable
    (MeasurableSet.univ_pi ht)]
  have : (MeasurableEquiv.curry α β ℝ).symm ⁻¹' (Set.univ.pi t) =
      Set.univ.pi (fun a => Set.univ.pi (fun b => t (a, b))) := by
    ext z
    simp [MeasurableEquiv.coe_curry_symm, Set.mem_pi]
  rw [this, volume_pi, Measure.pi_pi]
  simp_rw [volume_pi, Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/-- The bridge: `swapE z i s = z s i`. -/
noncomputable def swapE (N : ℕ) : IIT.Census.Param N ≃ᵐ (Fin N → IIT2.State N → ℝ) :=
  (MeasurableEquiv.curry (IIT.State N) (Fin N) ℝ).symm.trans
    ((MeasurableEquiv.piCongrLeft (fun _ => ℝ) (Equiv.prodComm (IIT.State N) (Fin N))).trans
      (MeasurableEquiv.curry (Fin N) (IIT2.State N) ℝ))

lemma swapE_apply (z : IIT.Census.Param N) (i : Fin N) (s : IIT2.State N) :
    swapE N z i s = z s i := by
  simp [swapE, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, MeasurableEquiv.coe_curry_symm,
    MeasurableEquiv.coe_curry]

lemma mp_swapE (N : ℕ) : MeasurePreserving (swapE N) volume volume :=
  (mp_uncurry _ _).trans ((volume_measurePreserving_piCongrLeft (fun _ => ℝ)
    (Equiv.prodComm (IIT.State N) (Fin N))).trans
    (by simpa using (mp_uncurry (Fin N) (IIT2.State N)).symm))

lemma swapE_preimage_cube (N : ℕ) : swapE N ⁻¹' IIT2.cube N = IIT.Census.cube N := by
  ext z
  simp only [Set.mem_preimage, IIT2.cube, IIT.Census.cube, Set.mem_setOf_eq, swapE_apply]
  exact forall_comm

/-- The two TPMs have the same transition probabilities. -/
lemma prob_tpmOf_swapE (z : IIT.Census.Param N) (i : Fin N) (s : IIT2.State N) (b : Bool) :
    (IIT2.tpmOf (swapE N z)).prob i s b = (IIT.Census.tpmOf z).prob i s b := by
  simp only [IIT2.tpmOf, IIT.Census.tpmOf, swapE_apply]
  rfl

/-- `C₂` transported to the IIT 4.0 parameter space. -/
def C2 (N : ℕ) (s : IIT2.State N) : Set (IIT.Census.Param N) :=
  {z | z ∈ IIT.Census.cube N ∧ IIT2.WholeIsMainComplex (IIT2.tpmOf (swapE N z)) s}

lemma C2_eq_preimage (N : ℕ) (s : IIT2.State N) :
    C2 N s = swapE N ⁻¹' {w ∈ IIT2.cube N | IIT2.WholeIsMainComplex (IIT2.tpmOf w) s} := by
  ext z
  have := congrArg (z ∈ ·) (swapE_preimage_cube N)
  simp only [Set.mem_preimage, eq_iff_iff] at this
  simp only [C2, Set.mem_setOf_eq, Set.mem_preimage, this]

lemma volume_C2 (N : ℕ) (s : IIT2.State N) :
    volume (C2 N s) = volume {w ∈ IIT2.cube N | IIT2.WholeIsMainComplex (IIT2.tpmOf w) s} := by
  rw [C2_eq_preimage]; exact (mp_swapE N).measure_preimage_equiv _

/-- The complement of `C₂` inside the cube, transported. -/
lemma volume_cube_not_C2 (N : ℕ) (s : IIT2.State N) :
    volume {z | z ∈ IIT.Census.cube N ∧ ¬ IIT2.WholeIsMainComplex (IIT2.tpmOf (swapE N z)) s} =
      volume {w ∈ IIT2.cube N | ¬ IIT2.WholeIsMainComplex (IIT2.tpmOf w) s} := by
  have : {z | z ∈ IIT.Census.cube N ∧ ¬ IIT2.WholeIsMainComplex (IIT2.tpmOf (swapE N z)) s} =
      swapE N ⁻¹' {w ∈ IIT2.cube N | ¬ IIT2.WholeIsMainComplex (IIT2.tpmOf w) s} := by
    ext z
    have := congrArg (z ∈ ·) (swapE_preimage_cube N)
    simp only [Set.mem_preimage, eq_iff_iff] at this
    simp only [Set.mem_setOf_eq, Set.mem_preimage, this]
  rw [this]; exact (mp_swapE N).measure_preimage_equiv _

end IITCompare
