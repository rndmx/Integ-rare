/-
Census, B1, W14 work package WP5 (part 6): one-sided Gaussian-comparison tails of centred uniform sums
(from the constant `C` of `GCStmt`), transported to signed fresh sums (`EntrySumLawStmt`).

* `w5_tail_up`: `P(Σ_{l<n} (U_l - 1/2) ≥ t) ≤ Q(y) + C n^{-1/8}` for `y √(n/12) < t`;
* `w5_tail_lo`: `P(Σ_{l<n} (U_l - 1/2) ≥ t) ≥ Q(x) - C n^{-1/8}` for `t ≤ x √(n/12)`;
  here `Q(x) = gaussianReal 0 1 (Ioi x)`;
* the same for `cubeM {t ≤ w5S F R k b}` with `n = |R \ F|`.

No `sorry`.
-/
import IIT.Census.B1CntCoinD

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-- The standard Gaussian upper tail `Q(x)`. -/
noncomputable def w5Q (x : ℝ) : ℝ := (ProbabilityTheory.gaussianReal 0 1 (Set.Ioi x)).toReal

lemma w5_toReal_compl {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {s : Set α} (hs : MeasurableSet s) : (μ sᶜ).toReal = 1 - (μ s).toReal := by
  rw [prob_compl_eq_one_sub hs, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
    ENNReal.toReal_one]

lemma w5_Phi_add_Q (x : ℝ) :
    (ProbabilityTheory.gaussianReal 0 1 (Set.Iic x)).toReal + w5Q x = 1 := by
  unfold w5Q
  rw [← Set.compl_Iic, w5_toReal_compl _ measurableSet_Iic]
  ring

lemma w5Q_anti {x y : ℝ} (h : x ≤ y) : w5Q y ≤ w5Q x := by
  unfold w5Q
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ioi_subset_Ioi h))

lemma w5Q_nonneg (x : ℝ) : 0 ≤ w5Q x := ENNReal.toReal_nonneg

lemma w5_measurableSet_sum_le (n : ℕ) (c : ℝ) :
    MeasurableSet {u : Fin n → ℝ | ∑ l, (u l - 1 / 2) ≤ c} :=
  measurableSet_le (Finset.measurable_sum _ fun l _ => (measurable_pi_apply l).sub_const _)
    measurable_const

/-- The GC hypothesis, with its constant. -/
def W5GC (C : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ x : ℝ,
    |((Measure.pi fun _ : Fin n => unif) {u | ∑ l, (u l - 1 / 2) ≤ x * Real.sqrt ((n : ℝ) / 12)}).toReal
        - (ProbabilityTheory.gaussianReal 0 1 (Set.Iic x)).toReal| ≤ C * (n : ℝ) ^ (-(1 / 8 : ℝ))

theorem w5_tail_up {C : ℝ} (hC : W5GC C) {n : ℕ} (hn : 0 < n) {t y : ℝ}
    (h : y * Real.sqrt ((n : ℝ) / 12) < t) :
    ((Measure.pi fun _ : Fin n => unif) {u | ∑ l, (u l - 1 / 2) ∈ Set.Ici t}).toReal ≤
      w5Q y + C * (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
  set μ := Measure.pi fun _ : Fin n => unif
  have hsub : {u : Fin n → ℝ | ∑ l, (u l - 1 / 2) ∈ Set.Ici t} ⊆
      {u | ∑ l, (u l - 1 / 2) ≤ y * Real.sqrt ((n : ℝ) / 12)}ᶜ := by
    intro u hu
    simp only [Set.mem_Ici, Set.mem_ofPred_eq] at hu
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    linarith
  have h1 := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (μ := μ) hsub)
  rw [w5_toReal_compl μ (w5_measurableSet_sum_le n _)] at h1
  have h2 := (abs_le.1 (hC n hn y)).1
  have h3 := w5_Phi_add_Q y
  linarith

theorem w5_tail_lo {C : ℝ} (hC : W5GC C) {n : ℕ} (hn : 0 < n) {t x : ℝ}
    (h : t ≤ x * Real.sqrt ((n : ℝ) / 12)) :
    w5Q x - C * (n : ℝ) ^ (-(1 / 8 : ℝ)) ≤
      ((Measure.pi fun _ : Fin n => unif) {u | ∑ l, (u l - 1 / 2) ∈ Set.Ici t}).toReal := by
  set μ := Measure.pi fun _ : Fin n => unif
  have hsub : {u : Fin n → ℝ | ∑ l, (u l - 1 / 2) ≤ x * Real.sqrt ((n : ℝ) / 12)}ᶜ ⊆
      {u | ∑ l, (u l - 1 / 2) ∈ Set.Ici t} := by
    intro u hu
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hu
    simp only [Set.mem_Ici, Set.mem_ofPred_eq]
    linarith
  have h1 := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (μ := μ) hsub)
  rw [w5_toReal_compl μ (w5_measurableSet_sum_le n _)] at h1
  have h2 := (abs_le.1 (hC n hn x)).2
  have h3 := w5_Phi_add_Q x
  linarith

/-! ### Signed fresh sums -/

lemma w5S_toReal_eq (hESL : EntrySumLawStmt) (F R : Finset (State N)) (k : Fin N) (b : Bool)
    (t : ℝ) :
    (cubeM N {w | t ≤ w5S F R k b w}).toReal =
      ((Measure.pi fun _ : Fin (w5E F R k).card => unif)
        {u | ∑ l, (u l - 1 / 2) ∈ Set.Ici t}).toReal := by
  have e : {w : Param N | t ≤ w5S F R k b w} = {w | w5S F R k b w ∈ Set.Ici t} := rfl
  rw [e, w5S_law hESL F R k b measurableSet_Ici]

theorem w5S_tail_up (hESL : EntrySumLawStmt) {C : ℝ} (hC : W5GC C) (F R : Finset (State N))
    (k : Fin N) (b : Bool) (hn : 0 < (w5E F R k).card) {t y : ℝ}
    (h : y * Real.sqrt (((w5E F R k).card : ℝ) / 12) < t) :
    (cubeM N {w | t ≤ w5S F R k b w}).toReal ≤
      w5Q y + C * ((w5E F R k).card : ℝ) ^ (-(1 / 8 : ℝ)) := by
  rw [w5S_toReal_eq hESL]; exact w5_tail_up hC hn h

theorem w5S_tail_lo (hESL : EntrySumLawStmt) {C : ℝ} (hC : W5GC C) (F R : Finset (State N))
    (k : Fin N) (b : Bool) (hn : 0 < (w5E F R k).card) {t x : ℝ}
    (h : t ≤ x * Real.sqrt (((w5E F R k).card : ℝ) / 12)) :
    w5Q x - C * ((w5E F R k).card : ℝ) ^ (-(1 / 8 : ℝ)) ≤
      (cubeM N {w | t ≤ w5S F R k b w}).toReal := by
  rw [w5S_toReal_eq hESL]; exact w5_tail_lo hC hn h

end Census
end IIT
