/-
Census, B1 LTBetaHi, module T7 tool: **the argmax-union lemma** (W2 §6.2).

Let `E r0` be events such that, for every `w`, resampling the rows of the ball `Ball(r0, ρ)` other than `r0` lands in
`E r0` with probability `≤ q`. Then `P(w ∈ E (tc w)) ≤ (N+1)^ρ q`, where `tc` is the argmax row — instead of the
`2^N q` of a plain union over `r0`.

Proof: off ties (null), `tc` beats every row outside its ball (`Beat`); `Beat r0` reads only row `r0` and the rows
outside the ball, so conditioning on them gives `P(E r0 ∩ Beat r0) ≤ q P(Beat r0)`; and the rows `r0` with `Beat r0`
are pairwise within distance `ρ`, so they number at most `(N+1)^ρ`.
-/
import IIT.Census.B1ForcedA

namespace IIT
namespace Census

open MeasureTheory Finset

variable {N : ℕ}

/-- `r0` beats every row outside its `ρ`-ball. -/
def amBeat (ρ : ℕ) (r0 : State N) : Set (Param N) := {w | ∀ r, r ∉ ballR r0 ρ → Pw w r < Pw w r0}

/-- The entries of the ball except row `r0`. -/
def amC (ρ : ℕ) (r0 : State N) : Finset (State N × Fin N) := ((ballR r0 ρ).erase r0) ×ˢ univ

lemma amBeat_mset (ρ : ℕ) (r0 : State N) : MeasurableSet (amBeat (N := N) ρ r0) := by
  have e : amBeat (N := N) ρ r0 = ⋂ r, {w : Param N | r ∉ ballR r0 ρ → Pw w r < Pw w r0} := by
    ext w; simp [amBeat]
  rw [e]
  refine MeasurableSet.iInter fun r => ?_
  by_cases hr : r ∈ ballR r0 ρ
  · have : {w : Param N | r ∉ ballR r0 ρ → Pw w r < Pw w r0} = Set.univ := by
      ext w; simp [hr]
    rw [this]; exact MeasurableSet.univ
  · have : {w : Param N | r ∉ ballR r0 ρ → Pw w r < Pw w r0} = {w | Pw w r < Pw w r0} := by
      ext w; simp [hr]
    rw [this]; exact measurableSet_lt (b1m_Pw r) (b1m_Pw r0)

lemma amBeat_det (ρ : ℕ) (r0 : State N) : DetOnE (amC ρ r0)ᶜ (amBeat (N := N) ρ r0) := by
  intro w w' h
  have hrow : ∀ r, (r ∉ ballR r0 ρ ∨ r = r0) → Pw w r = Pw w' r := by
    intro r hr
    unfold Pw
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [h (r, j) (by
      simp only [amC, mem_compl, mem_product, mem_erase, mem_univ, and_true, not_and]
      intro hne hmem
      rcases hr with h1 | h1
      · exact h1 hmem
      · exact hne h1)]
  simp only [amBeat, Set.mem_setOf_eq]
  refine forall_congr' fun r => imp_congr_right fun hr => ?_
  rw [hrow r (Or.inl hr), hrow r0 (Or.inr rfl)]

open Classical in
/-- The beating rows are pairwise within distance `ρ`, hence at most `(N+1)^ρ` of them. -/
lemma amBeat_count (ρ : ℕ) (w : Param N) :
    ((univ.filter fun r0 : State N => w ∈ amBeat ρ r0).card : ENNReal) ≤ ((N + 1) ^ ρ : ℕ) := by
  classical
  set R := univ.filter fun r0 : State N => w ∈ amBeat ρ r0
  rcases R.eq_empty_or_nonempty with h | ⟨r1, hr1⟩
  · rw [h]; simp
  · have hsub : R ⊆ ballR r1 ρ := by
      intro r0 hr0
      by_contra hno
      have h0 := (mem_filter.1 hr0).2
      have h1 := (mem_filter.1 hr1).2
      have hno' : r1 ∉ ballR r0 ρ := by
        rw [mem_ballR] at hno ⊢; rw [b1_ham_comm]; exact hno
      have a := h1 r0 hno
      have b := h0 r1 hno'
      linarith
    exact_mod_cast (card_le_card hsub).trans (card_ballR_le r1 ρ)

/-- **The argmax-union lemma.** -/
theorem cubeM_argmax_union (ρ : ℕ) (E : State N → Set (Param N)) (hE : ∀ r0, MeasurableSet (E r0)) {q : ENNReal}
    (hq : ∀ r0 w, cubeM N {η | replE (amC ρ r0) w η ∈ E r0} ≤ q) :
    cubeM N {w | w ∈ E (tcRow w)} ≤ ((N + 1) ^ ρ : ℕ) * q := by
  classical
  haveI : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  -- off ties, `w ∈ E r0 ∩ Beat r0` for `r0 = tc`
  have hsub : {w | w ∈ E (tcRow w)} ⊆ faTie N ∪ ⋃ r0, (amBeat ρ r0 ∩ E r0) := by
    intro w hw
    by_cases ht : w ∈ faTie N
    · exact Or.inl ht
    · refine Or.inr (Set.mem_iUnion.2 ⟨tcRow w, fun r hr => ?_, hw⟩)
      have hne : r ≠ tcRow w := fun h => hr (h ▸ self_mem_ballR _ ρ)
      exact lt_of_le_of_ne (Pw_le_tcRow w r) fun h => ht ⟨r, tcRow w, hne, h⟩
  have hone : ∀ r0, cubeM N (amBeat ρ r0 ∩ E r0) ≤ q * cubeM N (amBeat ρ r0) := fun r0 =>
    cubeM_inter_le_of_sectionE (amC ρ r0) (amBeat_mset ρ r0) (hE r0) (amBeat_det ρ r0) fun w _ => hq r0 w
  have hsum : ∑ r0, cubeM N (amBeat (N := N) ρ r0) ≤ ((N + 1) ^ ρ : ℕ) := by
    calc ∑ r0, cubeM N (amBeat (N := N) ρ r0)
        = ∑ r0, ∫⁻ w, (amBeat ρ r0).indicator 1 w ∂cubeM N :=
          Finset.sum_congr rfl fun r0 _ => (lintegral_indicator_one (amBeat_mset ρ r0)).symm
      _ = ∫⁻ w, ∑ r0, (amBeat ρ r0).indicator 1 w ∂cubeM N :=
          (lintegral_finset_sum _ fun r0 _ => measurable_one.indicator (amBeat_mset ρ r0)).symm
      _ ≤ ∫⁻ _w, (((N + 1) ^ ρ : ℕ) : ENNReal) ∂cubeM N := by
          refine lintegral_mono fun w => ?_
          have e : ∑ r0, (amBeat (N := N) ρ r0).indicator (1 : Param N → ENNReal) w =
              ((univ.filter fun r0 : State N => w ∈ amBeat ρ r0).card : ENNReal) := by
            simp only [Set.indicator_apply, Pi.one_apply]
            rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
          rw [e]; exact amBeat_count ρ w
      _ = ((N + 1) ^ ρ : ℕ) := by simp
  calc cubeM N {w | w ∈ E (tcRow w)} ≤ cubeM N (faTie N) + cubeM N (⋃ r0, (amBeat ρ r0 ∩ E r0)) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ 0 + ∑ r0, q * cubeM N (amBeat ρ r0) := by
        rw [fa_tie_null]
        exact add_le_add le_rfl ((measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun r0 _ => hone r0))
    _ = q * ∑ r0, cubeM N (amBeat ρ r0) := by rw [zero_add, Finset.mul_sum]
    _ ≤ q * ((N + 1) ^ ρ : ℕ) := mul_le_mul' le_rfl hsum
    _ = ((N + 1) ^ ρ : ℕ) * q := mul_comm _ _

end Census
end IIT
