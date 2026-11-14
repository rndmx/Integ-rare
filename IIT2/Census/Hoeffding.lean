/-
Census of IIT 2.0: Hoeffding's inequality for `2 a^M_l(x) - 1`, an average of `2^m`
independent centred variables (large `m` part of Proposition 5).
-/
import IIT2.Census.Moments

namespace IIT2

open MeasureTheory ProbabilityTheory Finset Real
open scoped NNReal

variable {N : ℕ}

theorem hoeffding_window (M : Finset (Fin N)) (l : Fin N) (x : State N) (ε : ℝ) (hε : 0 ≤ ε) :
    (μP N).real {ω | ε ≤ |2 * aω M l x ω - 1|} ≤
      2 * Real.exp (-ε ^ 2 * 2 ^ (N - M.card) / 2) := by
  set m := N - M.card with hm
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  set r : ℝ := 2 / 2 ^ m
  have hr : 0 < r := by positivity
  set X : Fin N × State N → Ωf N → ℝ := fun p ω => r * clamp (ω p) - 1 / 2 ^ m
  have hind : iIndepFun X (μP N) :=
    iIndep_coords.comp (fun _ u => r * clamp u - 1 / 2 ^ m)
      (fun _ => (measurable_clamp.const_mul r).sub_const _)
  set cc : ℝ≥0 := (‖r - 0‖₊ / 2) ^ 2
  have hcc : (cc : ℝ) = (1 / 2 ^ m) ^ 2 := by
    simp only [cc, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, sub_zero, Real.norm_eq_abs,
      abs_of_pos hr]
    simp [r]; ring
  have hsub : ∀ p, HasSubgaussianMGF (X p) cc (μP N) := by
    intro p
    have h := hasSubgaussianMGF_of_mem_Icc (μ := μP N) (X := fun ω => r * clamp (ω p))
      (a := 0) (b := r) ((measurable_clamp.comp (measurable_pi_apply p)).const_mul r).aemeasurable
      (ae_of_all _ fun ω => ⟨by have := clamp_nonneg (ω p); positivity,
        by have := clamp_le_one (ω p); nlinarith⟩)
    have hmean : ∫ ω, r * clamp (ω p) ∂(μP N) = 1 / 2 ^ m := by
      rw [integral_const_mul, integral_clamp]; simp [r]; ring
    rw [hmean] at h
    exact h
  set s : Finset (Fin N × State N) := (blk M x).map ⟨fun c => (l, c), fun c c' h => by
    simpa using h⟩
  have hS := HasSubgaussianMGF.sum_of_iIndepFun hind (s := s) (c := fun _ => cc) (fun p _ => hsub p)
  have hsum : ∀ ω, ∑ p ∈ s, X p ω = 2 * aω M l x ω - 1 := by
    intro ω
    rw [Finset.sum_map]
    change (∑ c ∈ blk M x, (r * clamp (ω (l, c)) - 1 / 2 ^ m)) = _
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, card_blk, aω_eq, ← hm]
    simp only [nsmul_eq_mul, r]; push_cast
    field_simp
  have hcsum : ((∑ p ∈ s, (fun _ => cc) p : ℝ≥0) : ℝ) = 1 / 2 ^ m := by
    rw [NNReal.coe_sum]
    simp only [hcc, Finset.sum_const, s, Finset.card_map, card_blk, nsmul_eq_mul]
    rw [← hm]
    push_cast
    field_simp
  have h1 := hS.measure_ge_le hε
  have h2 := hS.neg.measure_ge_le hε
  rw [hcsum] at h1 h2
  have hexp : -ε ^ 2 / (2 * (1 / 2 ^ m)) = -ε ^ 2 * 2 ^ m / 2 := by field_simp
  rw [hexp] at h1 h2
  have hsub' : {ω | ε ≤ |2 * aω M l x ω - 1|} ⊆
      {ω | ε ≤ ∑ p ∈ s, X p ω} ∪ {ω | ε ≤ (-fun ω => ∑ p ∈ s, X p ω) ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union, Pi.neg_apply, hsum] at hω ⊢
    rcases le_abs'.mp hω with h | h
    · right; linarith
    · left; exact h
  calc (μP N).real {ω | ε ≤ |2 * aω M l x ω - 1|}
      ≤ (μP N).real ({ω | ε ≤ ∑ p ∈ s, X p ω} ∪ {ω | ε ≤ (-fun ω => ∑ p ∈ s, X p ω) ω}) :=
        measureReal_mono hsub'
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by linarith

end IIT2
