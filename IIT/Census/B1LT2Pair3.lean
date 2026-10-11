/-
Census, B1 lemma LT2, module M6b-5: the success probability of one pair given the shared data.

`lt2_pair_succ_prob`: `P(⋂_κ X_κ) ≥ (ρ e^{-225x²}/4)^16` when every private sum has positive variance and its weights are
`≤ sd/(16x)`.
-/
import IIT.Census.B1LT2Pair2

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

lemma lt2_meas_entry (r : State N) (j : Fin N) : Measurable fun η : Param N => clamp01 (η r j) :=
  measurable_clamp01.comp ((measurable_pi_apply j).comp (measurable_pi_apply r))

lemma lt2_meas_Sres (s : State N) (w : Param N) (a b : Fin N) (c u v : Bool) :
    Measurable (lt2Sres s w a b c u v) := by
  unfold lt2Sres
  exact Finset.measurable_sum _ fun r _ => measurable_const.mul ((lt2_meas_entry _ _).sub measurable_const)

lemma lt2_mset_X (s : State N) (w : Param N) (a b : Fin N) (x ρ : ℝ) (κ : Bool × Bool × Bool × Bool) :
    MeasurableSet (lt2X s w a b x ρ κ) := by
  classical
  unfold lt2X
  split_ifs
  · exact measurableSet_le (lt2_meas_entry _ _) measurable_const
  · exact measurableSet_le measurable_const (lt2_meas_entry _ _)
  · exact MeasurableSet.univ
  · exact measurableSet_le measurable_const (lt2_meas_Sres s w a b _ _ _)
  · exact measurableSet_le (lt2_meas_Sres s w a b _ _ _) measurable_const

lemma lt2_det_X (s : State N) (w : Param N) (a b : Fin N) (x ρ : ℝ) (κ : Bool × Bool × Bool × Bool) :
    DetOnE (lt2C s w a b κ) (lt2X s w a b x ρ κ) := by
  classical
  intro η η' h
  obtain ⟨e, c, u, v⟩ := κ
  cases e
  · have hS : lt2Sres s w a b c u v η = lt2Sres s w a b c u v η' := by
      unfold lt2Sres
      refine Finset.sum_congr rfl fun r hr => ?_
      have hq : (merge {a, b} (lt2pat a b u v) r, lt2col a b c) ∈ lt2C s w a b (false, c, u, v) := by
        simp only [lt2C, Bool.false_eq_true, ↓reduceIte]; exact mem_image_of_mem _ hr
      have := h _ hq
      simp only at this
      rw [this]
    simp only [lt2X, Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · simp only [Set.mem_setOf_eq]; rw [hS]
    · simp only [Set.mem_setOf_eq]; rw [hS]
  · simp only [lt2X, ↓reduceIte]
    split_ifs with hE
    · have hq : (lt2rowE s a b u v, lt2col a b c) ∈ lt2C s w a b (true, c, u, v) := by
        simp only [lt2C, ↓reduceIte, if_pos hE, mem_singleton]
      have := h _ hq; simp only at this
      simp only [Set.mem_setOf_eq]; rw [this]
    · have hq : (lt2rowE s a b u v, lt2col a b c) ∈ lt2C s w a b (true, c, u, v) := by
        simp only [lt2C, ↓reduceIte, if_pos hE, mem_singleton]
      have := h _ hq; simp only at this
      simp only [Set.mem_setOf_eq]; rw [this]
    · exact Iff.rfl

/-- One entry is uniform. -/
lemma lt2_mp_entry (q : State N × Fin N) : MeasurePreserving (fun η : Param N => η q.1 q.2) (cubeM N) unif := by
  unfold cubeM
  have h1 := measurePreserving_eval (fun _ : State N => rowM N) q.1
  have h2 : MeasurePreserving (fun x : Fin N → ℝ => x q.2) (rowM N) unif := by
    unfold rowM; exact measurePreserving_eval (fun _ : Fin N => unif) q.2
  exact h2.comp h1

lemma lt2_unif_box_lo {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : ENNReal.ofReal ρ ≤ unif {u | clamp01 u ≤ ρ} := by
  unfold unif
  rw [Measure.restrict_apply' measurableSet_Icc]
  calc ENNReal.ofReal ρ = volume (Set.Icc (0 : ℝ) ρ) := by rw [Real.volume_Icc, sub_zero]
    _ ≤ volume ({u | clamp01 u ≤ ρ} ∩ Set.Icc (0 : ℝ) 1) := measure_mono fun u hu => by
        refine ⟨?_, hu.1, hu.2.trans h1⟩
        simp only [Set.mem_setOf_eq]; rw [clamp01_of_mem ⟨hu.1, hu.2.trans h1⟩]; exact hu.2

lemma lt2_unif_box_hi {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : ENNReal.ofReal ρ ≤ unif {u | 1 - ρ ≤ clamp01 u} := by
  unfold unif
  rw [Measure.restrict_apply' measurableSet_Icc]
  calc ENNReal.ofReal ρ = volume (Set.Icc (1 - ρ) 1) := by rw [Real.volume_Icc]; congr 1; ring
    _ ≤ volume ({u | 1 - ρ ≤ clamp01 u} ∩ Set.Icc (0 : ℝ) 1) := measure_mono fun u hu => by
        refine ⟨?_, by linarith [hu.1], hu.2⟩
        simp only [Set.mem_setOf_eq]; rw [clamp01_of_mem ⟨by linarith [hu.1], hu.2⟩]; exact hu.1

/-- **The success probability of one pair.** -/
theorem lt2_pair_succ_prob (s : State N) (w : Param N) {a b : Fin N} (hab : a ≠ b) {x ρ : ℝ} (hx : 1 ≤ x)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hV : ∀ c u v, 0 < ∑ r ∈ lt2Hf s w a b c u v, lt2gNs (w r) ^ 2 / 12)
    (hc : ∀ c u v, ∀ r ∈ lt2Hf s w a b c u v, lt2gNs (w r) ≤ lt2sd s w a b c u v / (16 * x)) :
    ENNReal.ofReal ((ρ * (Real.exp (-(225 * x ^ 2)) / 4)) ^ 16) ≤
      cubeM N (⋂ κ ∈ (univ : Finset (Bool × Bool × Bool × Bool)), lt2X s w a b x ρ κ) := by
  classical
  set p1 := Real.exp (-(225 * x ^ 2)) / 4
  have hp1 : 0 ≤ p1 := by positivity
  have hp11 : p1 ≤ 1 := by
    have : Real.exp (-(225 * x ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    simp only [p1]; linarith
  rw [cubeM_iInter_eq_prod_of_detOnE univ (lt2C s w a b) (fun j _ k _ hjk => lt2_C_disj hab j k hjk)
    (fun κ _ => lt2_mset_X s w a b x ρ κ) (fun κ _ => lt2_det_X s w a b x ρ κ)]
  have hcard : (univ : Finset (Bool × Bool × Bool × Bool)).card = 16 := by simp
  rw [← hcard, ← Finset.prod_const, ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)]
  refine Finset.prod_le_prod' fun κ _ => ?_
  obtain ⟨e, c, u, v⟩ := κ
  cases e
  · -- private sum
    have hpre : ENNReal.ofReal (ρ * p1) ≤ ENNReal.ofReal p1 :=
      ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left hp1 hρ1)
    refine hpre.trans ?_
    set Hf := lt2Hf s w a b c u v
    set e : {r // r ∈ Hf} → State N × Fin N := fun r => (merge {a, b} (lt2pat a b u v) r.1, lt2col a b c)
    have he : Function.Injective e := by
      intro r r' h
      have h1 := congrArg Prod.fst h
      exact Subtype.ext (lt2_merge_inj_H (lt2pat a b u v) ((mem_filter.1 r.2).1) ((mem_filter.1 r'.2).1) h1)
    set cf : {r // r ∈ Hf} → ℝ := fun r => lt2gNs (w r.1)
    set V := ∑ r : {r // r ∈ Hf}, cf r ^ 2 / 12
    have hVe : V = ∑ r ∈ Hf, lt2gNs (w r) ^ 2 / 12 := Finset.sum_coe_sort Hf (fun r => lt2gNs (w r) ^ 2 / 12)
    have hsd : lt2sd s w a b c u v = Real.sqrt V := by rw [hVe]; rfl
    have hV0 : 0 < V := by rw [hVe]; exact hV c u v
    have hb : ∀ r, cf r ≤ Real.sqrt V / (16 * x) := fun r => by rw [← hsd]; exact hc c u v r.1 r.2
    have hsum : ∀ η : Param N, lt2Sres s w a b c u v η =
        ∑ r : {r // r ∈ Hf}, cf r * (clamp01 (η (e r).1 (e r).2) - 1 / 2) := fun η =>
      (Finset.sum_coe_sort Hf (fun r => lt2gNs (w r) *
        (clamp01 (η (merge {a, b} (lt2pat a b u v) r) (lt2col a b c)) - 1 / 2))).symm
    simp only [lt2X, Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · refine (lt2_sb_entries e he cf (fun r => lt2gNs_nonneg _) hx rfl hV0 hb).trans (le_of_eq ?_)
      congr 1; ext η; simp only [Set.mem_setOf_eq]; rw [hsd, hsum]
    · refine (lt2_sb_entries_neg e he cf (fun r => lt2gNs_nonneg _) hx rfl hV0 hb).trans (le_of_eq ?_)
      congr 1; ext η; simp only [Set.mem_setOf_eq]; rw [hsd, hsum]
  · -- effect entry
    have hpre : ENNReal.ofReal (ρ * p1) ≤ ENNReal.ofReal ρ :=
      ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hρ0 hp11)
    refine hpre.trans ?_
    simp only [lt2X, ↓reduceIte]
    split_ifs
    · have mp := lt2_mp_entry (N := N) (lt2rowE s a b u v, lt2col a b c)
      rw [show {η : Param N | clamp01 (η (lt2rowE s a b u v) (lt2col a b c)) ≤ ρ} =
          (fun η : Param N => η (lt2rowE s a b u v) (lt2col a b c)) ⁻¹' {u | clamp01 u ≤ ρ} from rfl,
        mp.measure_preimage (measurableSet_le measurable_clamp01 measurable_const).nullMeasurableSet]
      exact lt2_unif_box_lo hρ0 hρ1
    · have mp := lt2_mp_entry (N := N) (lt2rowE s a b u v, lt2col a b c)
      rw [show {η : Param N | 1 - ρ ≤ clamp01 (η (lt2rowE s a b u v) (lt2col a b c))} =
          (fun η : Param N => η (lt2rowE s a b u v) (lt2col a b c)) ⁻¹' {u | 1 - ρ ≤ clamp01 u} from rfl,
        mp.measure_preimage (measurableSet_le measurable_const measurable_clamp01).nullMeasurableSet]
      exact lt2_unif_box_hi hρ0 hρ1
    · rw [measure_univ]; exact ENNReal.ofReal_le_one.2 hρ1

end Census
end IIT
