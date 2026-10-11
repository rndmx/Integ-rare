/-
Census, B1 lower bound, leaf `phi_univ_ge_EX`: measurability of `UnivGood` and its conditional probability
given the fixed rows `rowsA s r0 x` (the analogue of `B1LowerB.RestGood_cond`).

PROVED here: `measurableSet_UnivGood`, and the four fields `low`, `upTe`, `concC`, `concE`
(`B1UnivMass`, `B1UnivConc`).  The two small-cut fields are the remaining leaves:
* `smallC_cond` (W7 §3 item 2, cause side: generic-neighbour means for `1 ≤ |K| < D`, `K ≠ {x}`),
* `smallE_cond` (the same on the effect side, all `K`).
-/
import IIT.Census.B1UnivMass

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

variable {N : ℕ}

/-! ### Measurability -/

lemma ms_imp {α : Type*} [MeasurableSpace α] {p : Prop} {S : Set α} (hS : MeasurableSet S) :
    MeasurableSet {w | p → w ∈ S} := by
  by_cases hp : p
  · simpa [hp] using hS
  · simp [hp]

lemma m_fullProb (s r t : State N) : Measurable fun w : Param N => fullProb (tpmOf (flipP s w)) r t := by
  unfold fullProb
  refine Finset.measurable_prod _ fun k _ => ?_
  have hm : Measurable fun w : Param N => w r k := (measurable_pi_apply k).comp (measurable_pi_apply r)
  simp only [tpmOf, flipP, flipC]
  cases t k <;> cases s k <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact measurable_const.sub (clamp01_measurable.comp (measurable_const.sub hm))
  · exact measurable_const.sub (clamp01_measurable.comp hm)
  · exact clamp01_measurable.comp (measurable_const.sub hm)
  · exact clamp01_measurable.comp hm

lemma m_cmean (Y : Finset (Fin N)) (t : State N) (i : Fin N) :
    Measurable fun w : Param N => cmean w Y t i := by
  unfold cmean
  exact (Finset.measurable_sum _ fun r _ => b1m_clamp r i).div_const _

/-- The effect subcube average through the readings `pTe`. -/
lemma effUnit_teW_eq (w : Param N) (s : State N) (C : Finset (Fin N)) (j : Fin N) :
    effUnit (tpmOf (flipP s w)) Cᶜ s j (teW w s j) =
      (∑ r ∈ agree Cᶜ s, pTe w s r j) / (agree Cᶜ s).card := by
  rw [effUnit]
  congr 1
  refine sum_congr rfl fun r _ => ?_
  have h := prob_teW_row (flipP s w) s r j
  rw [flipP_invol s w] at h
  exact h

lemma m_effUnit (s : State N) (C : Finset (Fin N)) (j : Fin N) :
    Measurable fun w : Param N => effUnit (tpmOf (flipP s w)) Cᶜ s j (teW w s j) := by
  simp_rw [effUnit_teW_eq]
  exact (Finset.measurable_sum _ fun r _ => b1mx_pTe s r j).div_const _

lemma m_logb {f : Param N → ℝ} (hf : Measurable f) : Measurable fun w => Real.logb 2 (f w) := by
  unfold Real.logb
  exact (Real.measurable_log.comp hf).div_const _

lemma m_rowMinU {f : Param N → Fin N → ℝ} (hf : ∀ i, Measurable fun w => f w i) :
    Measurable fun w => rowMinU (f w) := by
  unfold rowMinU
  by_cases h : (univ : Finset (Fin N)).Nonempty
  · simp only [h, dite_true]
    exact b1_measurable_inf' h (f := fun (i : Fin N) w => f w i) fun i _ => hf i
  · simp only [h, dite_false]; exact measurable_const

lemma m_cpx {f : Param N → Fin N → ℝ} {cm : Param N → ℝ} (hf : ∀ i, Measurable fun w => f w i)
    (hcm : Measurable cm) (δ1 : ℝ) (j : Fin N) :
    Measurable fun w => cpx (f w) (cm w) δ1 j := by
  unfold cpx
  exact ((measurable_const.max (Real.measurable_log.comp ((hf j).div hcm))).sub measurable_const).div_const _

theorem measurableSet_UnivGood (s r0 : State N) (x : Fin N) :
    MeasurableSet {w : Param N | UnivGood N s r0 x w} := by
  classical
  set A := rowsA s r0 x
  have hlow : MeasurableSet {w : Param N | ∀ t : State N, 1 / 2 ≤
      ∑ r ∈ Aᶜ, fullProb (tpmOf (flipP s w)) r t} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun t =>
      measurableSet_le measurable_const (Finset.measurable_sum _ fun r _ => m_fullProb s r t)
  have hup : MeasurableSet {w : Param N |
      ∑ r ∈ Aᶜ, fullProb (tpmOf (flipP s w)) r (teW w s) ≤ 3 / 2} := by
    have e : {w : Param N | ∑ r ∈ Aᶜ, fullProb (tpmOf (flipP s w)) r (teW w s) ≤ 3 / 2} =
        ⋃ t0 : State N, ({w | teW w s = t0} ∩
          {w | ∑ r ∈ Aᶜ, fullProb (tpmOf (flipP s w)) r t0 ≤ 3 / 2}) := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h; exact ⟨teW w s, rfl, h⟩
      · rintro ⟨t0, h1, h2⟩; rw [h1]; exact h2
    rw [e]
    exact MeasurableSet.iUnion fun t0 => (b1_measurableSet_teW_eq s t0).inter
      (measurableSet_le (Finset.measurable_sum _ fun r _ => m_fullProb s r t0) measurable_const)
  have hcC : MeasurableSet {w : Param N | ∀ j C, j ∉ C → DU N ≤ C.card →
      |cmean w (univ \ C) r0 j - 1 / 2| ≤ dU N C.card} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun C =>
      MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
    exact measurableSet_le ((m_cmean _ r0 j).sub_const _).abs measurable_const
  have hcE : MeasurableSet {w : Param N | ∀ j C, j ∉ C → DU N ≤ C.card →
      |effUnit (tpmOf (flipP s w)) Cᶜ s j (teW w s j) - 1 / 2| ≤ dU N C.card} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun C =>
      MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
    exact measurableSet_le ((m_effUnit s C j).sub_const _).abs measurable_const
  have hsC : MeasurableSet {w : Param N | ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N → K ≠ {x} →
      8 * (DU N : ℝ) < ∑ j ∈ Kᶜ, min (Real.logb 2 (clamp01 (w r0 j) / cmean w (univ \ K) r0 j))
        (cpx (fun j => clamp01 (w r0 j)) (rowMinU fun j => clamp01 (w r0 j)) (dU N (N - 1)) j)} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun K => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => ?_
    refine measurableSet_lt measurable_const (Finset.measurable_sum _ fun j _ => ?_)
    exact (m_logb ((b1m_clamp r0 j).div (m_cmean _ r0 j))).min
      (m_cpx (f := fun w j => clamp01 (w r0 j)) (fun i => b1m_clamp r0 i)
        (m_rowMinU fun i => b1m_clamp r0 i) _ j)
  have hsE : MeasurableSet {w : Param N | ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N →
      8 * (DU N : ℝ) < ∑ j ∈ Kᶜ,
        min (Real.logb 2 (xE w s j / effUnit (tpmOf (flipP s w)) Kᶜ s j (teW w s j)))
          (cpx (xE w s) (rowMinU (xE w s)) (dU N (N - 1)) j)} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun K => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
    refine measurableSet_lt measurable_const (Finset.measurable_sum _ fun j _ => ?_)
    exact (m_logb ((b1m_xE s j).div (m_effUnit s K j))).min
      (m_cpx (f := fun w j => xE w s j) (fun i => b1m_xE s i) (m_rowMinU fun i => b1m_xE s i) _ j)
  have e : {w : Param N | UnivGood N s r0 x w} =
      ((((({w : Param N | ∀ t : State N, 1 / 2 ≤ ∑ r ∈ Aᶜ, fullProb (tpmOf (flipP s w)) r t} ∩
        {w | ∑ r ∈ Aᶜ, fullProb (tpmOf (flipP s w)) r (teW w s) ≤ 3 / 2}) ∩
        {w | ∀ j C, j ∉ C → DU N ≤ C.card → |cmean w (univ \ C) r0 j - 1 / 2| ≤ dU N C.card}) ∩
        {w | ∀ j C, j ∉ C → DU N ≤ C.card →
          |effUnit (tpmOf (flipP s w)) Cᶜ s j (teW w s j) - 1 / 2| ≤ dU N C.card}) ∩
        {w | ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N → K ≠ {x} →
          8 * (DU N : ℝ) < ∑ j ∈ Kᶜ, min (Real.logb 2 (clamp01 (w r0 j) / cmean w (univ \ K) r0 j))
            (cpx (fun j => clamp01 (w r0 j)) (rowMinU fun j => clamp01 (w r0 j)) (dU N (N - 1)) j)}) ∩
        {w | ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N →
          8 * (DU N : ℝ) < ∑ j ∈ Kᶜ,
            min (Real.logb 2 (xE w s j / effUnit (tpmOf (flipP s w)) Kᶜ s j (teW w s j)))
              (cpx (xE w s) (rowMinU (xE w s)) (dU N (N - 1)) j)}) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨⟨⟨⟨⟨h.low, h.upTe⟩, h.concC⟩, h.concE⟩, h.smallC⟩, h.smallE⟩
    · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩; exact ⟨h1, h2, h3, h4, h5, h6⟩
  rw [e]
  exact ((((hlow.inter hup).inter hcC).inter hcE).inter hsC).inter hsE

end Census
end IIT
