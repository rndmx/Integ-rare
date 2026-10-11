/-
Census, B1 lemma LT2, module M4 part 4: row pairs `(r, r ⊕ D)` are independent blocks.

For `d ∈ D` the rows split into the pairs `{r, r ⊕ D}` with `r_d = false`; under `cubeM` the pair values
`(w r, w (r ⊕ D))` are iid with law `rowM ⊗ rowM` (`lt2_mp_pairs`). Hence Bernstein applies to pair-local sums
(`lt2_pair_tail`), e.g. `Σ_r f(w r) h(w (r ⊕ D))`.
-/
import IIT.Census.B1LT2HeavyCount

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- Independence transfers along measure-preserving maps. -/
lemma lt2_iIndepFun_of_mp {ι Ω Ω' : Type*} [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Φ : Ω → Ω'} (hΦ : MeasurePreserving Φ μ ν) {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {Y : ∀ i, Ω' → β i} (hY : ∀ i, Measurable (Y i)) (h : iIndepFun Y ν) :
    iIndepFun (fun i ω => Y i (Φ ω)) μ := by
  have h' := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hY i).aemeasurable)).1 h
  refine (iIndepFun_iff_map_fun_eq_pi_map (fun i => ((hY i).comp hΦ.measurable).aemeasurable)).2 ?_
  have e1 : μ.map (fun ω i => Y i (Φ ω)) = ν.map (fun z i => Y i z) := by
    rw [← hΦ.map_eq, Measure.map_map (measurable_pi_iff.mpr hY) hΦ.measurable]; rfl
  have e2 : ∀ i, μ.map (fun ω => Y i (Φ ω)) = ν.map (Y i) := fun i => by
    rw [← hΦ.map_eq, Measure.map_map (hY i) hΦ.measurable]; rfl
  show μ.map (fun ω i => Y i (Φ ω)) = Measure.pi fun i => μ.map (fun ω => Y i (Φ ω))
  rw [e1, h']
  congr 1; funext i; exact (e2 i).symm

/-- The base rows of the pairs. -/
abbrev lt2P0 (d : Fin N) := {r : State N // r d = false}

/-- The pairing `r ↦ r ⊕ D`, from base rows to the other rows. -/
def lt2PairEq (D : Finset (Fin N)) {d : Fin N} (hd : d ∈ D) : lt2P0 d ≃ {r : State N // ¬ r d = false} where
  toFun r := ⟨lt2Xor r.1 D, by rw [lt2Xor_apply_mem hd, r.2]; simp⟩
  invFun r := ⟨lt2Xor r.1 D, by have h2 := r.2; rw [lt2Xor_apply_mem hd]; cases h : r.1 d <;> simp_all⟩
  left_inv r := Subtype.ext (lt2Xor_xor r.1 D)
  right_inv r := Subtype.ext (lt2Xor_xor r.1 D)

/-- The pair map. -/
def lt2PairMap (D : Finset (Fin N)) (d : Fin N) (w : Param N) : lt2P0 d → (Fin N → ℝ) × (Fin N → ℝ) :=
  fun i => (w i.1, w (lt2Xor i.1 D))

/-- **The pair values are iid `rowM ⊗ rowM`.** -/
theorem lt2_mp_pairs (D : Finset (Fin N)) {d : Fin N} (hd : d ∈ D) :
    MeasurePreserving (lt2PairMap D d) (cubeM N) (Measure.pi fun _ : lt2P0 d => (rowM N).prod (rowM N)) := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  set σ := lt2PairEq D hd
  have mp1 := measurePreserving_piEquivPiSubtypeProd (fun _ : State N => rowM N) (fun r : State N => r d = false)
  have mp2 := (measurePreserving_piCongrLeft (fun _ : {r : State N // ¬ r d = false} => rowM N) σ).symm
  have mp12 := (MeasurePreserving.id (Measure.pi fun _ : lt2P0 d => rowM N)).prod mp2
  have mp3 := (measurePreserving_arrowProdEquivProdArrow (Fin N → ℝ) (Fin N → ℝ) (lt2P0 d)
    (fun _ => rowM N) (fun _ => rowM N)).symm
  have mp := mp3.comp (mp12.comp mp1)
  have e : lt2PairMap D d = (MeasurableEquiv.arrowProdEquivProdArrow (Fin N → ℝ) (Fin N → ℝ) (lt2P0 d)).symm ∘
      (Prod.map id (MeasurableEquiv.piCongrLeft (fun _ => Fin N → ℝ) σ).symm ∘
        MeasurableEquiv.piEquivPiSubtypeProd (fun _ : State N => Fin N → ℝ) (fun r : State N => r d = false)) := by
    funext w i
    simp [lt2PairMap, MeasurableEquiv.arrowProdEquivProdArrow, MeasurableEquiv.piEquivPiSubtypeProd,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply, σ, lt2PairEq]
  rw [e]
  unfold cubeM
  exact mp

/-- **Bernstein for pair-local sums.** -/
theorem lt2_pair_tail (D : Finset (Fin N)) {d : Fin N} (hd : d ∈ D)
    (φ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ) (hφ : Measurable φ) {M : ℝ} (hM : ∀ z, |φ z| ≤ M)
    {V ε : ℝ} (hε : 0 ≤ ε) (hV : (Fintype.card (lt2P0 d) : ℝ) * ∫ z, φ z ^ 2 ∂(rowM N).prod (rowM N) ≤ V) :
    (cubeM N).real {w | ε ≤ ∑ i : lt2P0 d, (φ (w i.1, w (lt2Xor i.1 D)) - ∫ z, φ z ∂(rowM N).prod (rowM N))} ≤
      Real.exp (-min (ε ^ 2 / (4 * V)) (ε / (2 * (2 * M)))) := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  haveI : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  set ρ := (rowM N).prod (rowM N)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hφi : Integrable φ ρ :=
    Integrable.of_bound hφ.aestronglyMeasurable M (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hM z)
  set m := ∫ z, φ z ∂ρ
  have hm : |m| ≤ M := by
    calc |m| ≤ ∫ z, |φ z| ∂ρ := abs_integral_le_integral_abs
      _ ≤ ∫ _z, M ∂ρ := integral_mono hφi.abs (integrable_const M) hM
      _ = M := by simp
  have mp := lt2_mp_pairs D hd
  set Y : lt2P0 d → (lt2P0 d → (Fin N → ℝ) × (Fin N → ℝ)) → ℝ := fun i z => φ (z i) - m
  have hYm : ∀ i, Measurable (Y i) := fun i => (hφ.comp (measurable_pi_apply i)).sub measurable_const
  have hindY : iIndepFun Y (Measure.pi fun _ : lt2P0 d => ρ) :=
    iIndepFun_pi (X := fun _ z => φ z - m) fun i => (hφ.sub measurable_const).aemeasurable
  have hind : iIndepFun (fun i w => Y i (lt2PairMap D d w)) (cubeM N) := lt2_iIndepFun_of_mp mp hYm hindY
  have hint : ∀ i (g : (Fin N → ℝ) × (Fin N → ℝ) → ℝ), Measurable g →
      ∫ w, g (lt2PairMap D d w i) ∂cubeM N = ∫ z, g z ∂ρ := by
    intro i g hg
    rw [show (∫ w, g (lt2PairMap D d w i) ∂cubeM N) = ∫ z, g (z i) ∂(cubeM N).map (lt2PairMap D d) from
      (integral_map mp.measurable.aemeasurable (hg.comp (measurable_pi_apply i)).aestronglyMeasurable).symm,
      mp.map_eq]
    exact integral_pi_eval ρ hg.aestronglyMeasurable i
  refine bernstein_upper univ hind (fun i => ((hYm i).comp mp.measurable).aemeasurable) (by linarith) hε
    (fun i _ => ae_of_all _ fun w => ?_) (fun i _ => ?_) ?_
  · simp only [Y]; exact (abs_sub _ _).trans (by linarith [hM (lt2PairMap D d w i), hm])
  · simp only [Y]
    rw [hint i (fun z => φ z - m) (hφ.sub measurable_const), integral_sub hφi (integrable_const _), integral_const]
    simp [m]
  · refine le_trans ?_ hV
    rw [show (Fintype.card (lt2P0 d) : ℝ) * ∫ z, φ z ^ 2 ∂ρ = ∑ _i : lt2P0 d, ∫ z, φ z ^ 2 ∂ρ by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [Y]
    rw [hint i (fun z => (φ z - m) ^ 2) ((hφ.sub measurable_const).pow_const 2)]
    have hφi2 : Integrable (fun z => φ z ^ 2) ρ :=
      Integrable.of_bound (hφ.pow_const 2).aestronglyMeasurable (M ^ 2) (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have := hM z; nlinarith [abs_nonneg (φ z), sq_abs (φ z)])
    have e : ∫ z, (φ z - m) ^ 2 ∂ρ = ∫ z, φ z ^ 2 ∂ρ - m ^ 2 := by
      have : (fun z => (φ z - m) ^ 2) = fun z => φ z ^ 2 - 2 * m * φ z + m ^ 2 := by funext z; ring
      rw [this, integral_add (f := fun z => φ z ^ 2 - 2 * m * φ z) (g := fun _ => m ^ 2)
        (hφi2.sub (hφi.const_mul _)) (integrable_const _),
        integral_sub (f := fun z => φ z ^ 2) (g := fun z => 2 * m * φ z) hφi2 (hφi.const_mul _),
        integral_const_mul, integral_const]
      simp [m]; ring
    rw [e]; nlinarith [sq_nonneg m]

/-- Pair sums of `f(w r) h(w (r ⊕ D))` regrouped by pairs. -/
lemma lt2_pair_regroup (D : Finset (Fin N)) {d : Fin N} (hd : d ∈ D) (g : State N → State N → ℝ) :
    ∑ r : State N, g r (lt2Xor r D) =
      ∑ i : lt2P0 d, (g i.1 (lt2Xor i.1 D) + g (lt2Xor i.1 D) i.1) := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun r : State N => r d = false), Finset.sum_add_distrib]
  congr 1
  rw [← (lt2PairEq D hd).sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [lt2PairEq, Equiv.coe_fn_mk]
  rw [lt2Xor_xor]

end Census
end IIT
