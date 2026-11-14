/-
Census of IIT 2.0, rate: upper tails with truncation (positive part truncated at `c`, negative
part = lower tail of a nonnegative family) and lower tails (positive part = lower tail of a
nonnegative family, negative part bounded).
-/
import IIT2.Census.RateChernoff

namespace IIT2

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Finset Real

variable {N : ℕ}

lemma avg_neg' (f : State N → ℝ) : avg (fun x => -f x) = -avg f := by
  unfold avg; rw [Finset.sum_neg_distrib, neg_div]

section tails

variable (M : Finset (Fin N)) (G : State N → Ωf N → ℝ)
    (hm : ∀ x, Measurable (G x)) (C : ℝ) (hb : ∀ x ω, |G x ω| ≤ C)
    (hd : ∀ x, DepC (bset M x) (G x)) (σ2 : ℝ) (hσ : ∀ x, ∫ ω, (G x ω) ^ 2 ∂(μP N) ≤ σ2)
include hm hb hd hσ

lemma integral_pos_neg (x : State N) :
    ∫ ω, G x ω ∂(μP N) = ∫ ω, max (G x ω) 0 ∂(μP N) - ∫ ω, max (-G x ω) 0 ∂(μP N) := by
  rw [← integral_sub]
  · congr 1; funext ω; exact (max_zero_sub_eq_self (G x ω)).symm
  · exact integrable_of_bdd ((hm x).max measurable_const) C fun ω => by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _ |>.trans (hb x ω)) ((abs_nonneg _).trans (hb x ω))
  · exact integrable_of_bdd ((hm x).neg.max measurable_const) C fun ω => by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (neg_le_abs _ |>.trans (hb x ω)) ((abs_nonneg _).trans (hb x ω))

lemma sq_int_le_of_abs_le (H : State N → Ωf N → ℝ) (hHm : ∀ x, Measurable (H x))
    (hH : ∀ x ω, |H x ω| ≤ |G x ω|) (x : State N) : ∫ ω, H x ω ^ 2 ∂(μP N) ≤ σ2 := by
  refine le_trans (integral_mono (integrable_of_bdd ((hHm x).pow_const 2) (C ^ 2) fun ω => ?_)
    (integrable_of_bdd ((hm x).pow_const 2) (C ^ 2) fun ω => ?_) fun ω => ?_) (hσ x)
  · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ((hH x ω).trans (hb x ω)) 2
  · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb x ω) 2
  · simp only; rw [← sq_abs (H x ω), ← sq_abs (G x ω)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hH x ω) 2

/-- Upper tail with truncation of the positive part at `c`. -/
theorem upper_tail (c : ℝ) (hc : 0 ≤ c) (lam mu : ℝ) (hl : 0 < lam)
    (hlc : lam * 2 ^ (N - M.card) * c ≤ 1) (hmu : 0 < mu) (t : ℝ) :
    (μP N).real {ω | 2 * t ≤ avg (fun x => G x ω) - avg (fun x => ∫ ω', G x ω' ∂(μP N))} ≤
      (μP N).real {ω | ∃ x, c < G x ω} +
      Real.exp (-lam * 2 ^ N * t + lam ^ 2 * 2 ^ (N - M.card) * 2 ^ N * σ2) +
      Real.exp (-mu * 2 ^ N * t + mu ^ 2 * 2 ^ (N - M.card) * 2 ^ N * σ2) := by
  set P : State N → Ωf N → ℝ := fun x ω => min (max (G x ω) 0) c
  set Q : State N → Ωf N → ℝ := fun x ω => -max (-G x ω) 0
  have hPm : ∀ x, Measurable (P x) := fun x => ((hm x).max measurable_const).min measurable_const
  have hQm : ∀ x, Measurable (Q x) := fun x => ((hm x).neg.max measurable_const).neg
  have hPa : ∀ x ω, |P x ω| ≤ |G x ω| := fun x ω => by
    simp only [P]
    rw [abs_of_nonneg (le_min (le_max_right _ _) hc)]
    exact (min_le_left _ _).trans (max_le (le_abs_self _) (abs_nonneg _))
  have hQa : ∀ x ω, |Q x ω| ≤ |G x ω| := fun x ω => by
    simp only [Q]
    rw [abs_neg, abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have hPd : ∀ x, DepC (bset M x) (P x) := fun x => (hd x).comp' (fun u => min (max u 0) c)
  have hQd : ∀ x, DepC (bset M x) (Q x) := fun x => (hd x).comp' (fun u => -max (-u) 0)
  have hPb : ∀ x ω, |P x ω| ≤ C := fun x ω => (hPa x ω).trans (hb x ω)
  have hQb : ∀ x ω, |Q x ω| ≤ C := fun x ω => (hQa x ω).trans (hb x ω)
  have h1 := chernoff_avg M P hPm C hPb hPd c hc (fun x ω => min_le_right _ _) lam hl hlc σ2
    (sq_int_le_of_abs_le M G hm C hb hd σ2 hσ P hPm hPa) t
  have h2 := chernoff_avg M Q hQm C hQb hQd 0 le_rfl
    (fun x ω => by simp only [Q]; exact neg_nonpos.mpr (le_max_right _ _)) mu hmu (by simp) σ2
    (sq_int_le_of_abs_le M G hm C hb hd σ2 hσ Q hQm hQa) t
  -- means
  have hEP : ∀ x, ∫ ω, P x ω ∂(μP N) ≤ ∫ ω, max (G x ω) 0 ∂(μP N) := fun x =>
    integral_mono (integrable_of_bdd (hPm x) C (hPb x))
      (integrable_of_bdd ((hm x).max measurable_const) C fun ω => by
        rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (le_abs_self _ |>.trans (hb x ω)) ((abs_nonneg _).trans (hb x ω)))
      fun ω => min_le_left _ _
  have hEQ : ∀ x, ∫ ω, Q x ω ∂(μP N) = -∫ ω, max (-G x ω) 0 ∂(μP N) := fun x => integral_neg _
  have hsub : {ω | 2 * t ≤ avg (fun x => G x ω) - avg (fun x => ∫ ω', G x ω' ∂(μP N))} ⊆
      {ω | ∃ x, c < G x ω} ∪
      ({ω | t ≤ avg (fun x => P x ω) - avg (fun x => ∫ ω', P x ω' ∂(μP N))} ∪
       {ω | t ≤ avg (fun x => Q x ω) - avg (fun x => ∫ ω', Q x ω' ∂(μP N))}) := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    by_cases hex : ∃ x, c < G x ω
    · exact Or.inl hex
    right
    push_neg at hex
    have hGω : ∀ x, G x ω = P x ω + Q x ω := fun x => by
      simp only [P, Q]
      rw [min_eq_left (max_le (hex x) hc)]
      linarith [max_zero_sub_eq_self (G x ω)]
    have e1 : avg (fun x => G x ω) = avg (fun x => P x ω) - avg (fun x => -Q x ω) := by
      rw [← avg_sub]; exact avg_congr fun x => by rw [hGω x]; ring
    have e2 : avg (fun x => ∫ ω', G x ω' ∂(μP N)) =
        avg (fun x => ∫ ω', max (G x ω') 0 ∂(μP N)) - avg (fun x => ∫ ω', max (-G x ω') 0 ∂(μP N)) := by
      rw [← avg_sub]; exact avg_congr fun x => integral_pos_neg M G hm C hb hd σ2 hσ x
    have e3 : avg (fun x => ∫ ω', Q x ω' ∂(μP N)) = -avg (fun x => ∫ ω', max (-G x ω') 0 ∂(μP N)) := by
      rw [← avg_neg']; exact avg_congr hEQ
    have e4 : avg (fun x => -Q x ω) = -avg (fun x => Q x ω) := avg_neg' _
    have e5 : avg (fun x => ∫ ω', P x ω' ∂(μP N)) ≤ avg (fun x => ∫ ω', max (G x ω') 0 ∂(μP N)) :=
      avg_mono hEP
    by_contra hcon
    push_neg at hcon
    rw [e1, e2, e4] at hω
    rw [e3] at hcon
    linarith [hcon.1, hcon.2]
  refine (measureReal_mono hsub).trans ?_
  refine (measureReal_union_le _ _).trans ?_
  have := measureReal_union_le (μ := μP N)
    {ω | t ≤ avg (fun x => P x ω) - avg (fun x => ∫ ω', P x ω' ∂(μP N))}
    {ω | t ≤ avg (fun x => Q x ω) - avg (fun x => ∫ ω', Q x ω' ∂(μP N))}
  linarith

/-- Lower tail, negative part bounded by `b`. -/
theorem lower_tail (b : ℝ) (hb0 : 0 ≤ b) (hGb : ∀ x ω, -b ≤ G x ω) (lam mu : ℝ) (hl : 0 < lam)
    (hmu : 0 < mu) (hmb : mu * 2 ^ (N - M.card) * b ≤ 1) (t : ℝ) :
    (μP N).real {ω | 2 * t ≤ avg (fun x => ∫ ω', G x ω' ∂(μP N)) - avg (fun x => G x ω)} ≤
      Real.exp (-lam * 2 ^ N * t + lam ^ 2 * 2 ^ (N - M.card) * 2 ^ N * σ2) +
      Real.exp (-mu * 2 ^ N * t + mu ^ 2 * 2 ^ (N - M.card) * 2 ^ N * σ2) := by
  set P : State N → Ωf N → ℝ := fun x ω => -max (G x ω) 0
  set Q : State N → Ωf N → ℝ := fun x ω => max (-G x ω) 0
  have hPm : ∀ x, Measurable (P x) := fun x => ((hm x).max measurable_const).neg
  have hQm : ∀ x, Measurable (Q x) := fun x => (hm x).neg.max measurable_const
  have hPa : ∀ x ω, |P x ω| ≤ |G x ω| := fun x ω => by
    simp only [P]
    rw [abs_neg, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hQa : ∀ x ω, |Q x ω| ≤ |G x ω| := fun x ω => by
    simp only [Q]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have hPd : ∀ x, DepC (bset M x) (P x) := fun x => (hd x).comp' (fun u => -max u 0)
  have hQd : ∀ x, DepC (bset M x) (Q x) := fun x => (hd x).comp' (fun u => max (-u) 0)
  have hPb : ∀ x ω, |P x ω| ≤ C := fun x ω => (hPa x ω).trans (hb x ω)
  have hQb : ∀ x ω, |Q x ω| ≤ C := fun x ω => (hQa x ω).trans (hb x ω)
  have h1 := chernoff_avg M P hPm C hPb hPd 0 le_rfl
    (fun x ω => by simp only [P]; exact neg_nonpos.mpr (le_max_right _ _)) lam hl (by simp) σ2
    (sq_int_le_of_abs_le M G hm C hb hd σ2 hσ P hPm hPa) t
  have h2 := chernoff_avg M Q hQm C hQb hQd b hb0
    (fun x ω => by simp only [Q]; exact max_le (by linarith [hGb x ω]) hb0) mu hmu hmb σ2
    (sq_int_le_of_abs_le M G hm C hb hd σ2 hσ Q hQm hQa) t
  have hEP : ∀ x, ∫ ω, P x ω ∂(μP N) = -∫ ω, max (G x ω) 0 ∂(μP N) := fun x => integral_neg _
  have hsub : {ω | 2 * t ≤ avg (fun x => ∫ ω', G x ω' ∂(μP N)) - avg (fun x => G x ω)} ⊆
      {ω | t ≤ avg (fun x => P x ω) - avg (fun x => ∫ ω', P x ω' ∂(μP N))} ∪
       {ω | t ≤ avg (fun x => Q x ω) - avg (fun x => ∫ ω', Q x ω' ∂(μP N))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    have e1 : avg (fun x => G x ω) = avg (fun x => -P x ω) - avg (fun x => Q x ω) := by
      rw [← avg_sub]; exact avg_congr fun x => by
        simp only [P, Q]; linarith [max_zero_sub_eq_self (G x ω)]
    have e2 : avg (fun x => ∫ ω', G x ω' ∂(μP N)) =
        avg (fun x => ∫ ω', max (G x ω') 0 ∂(μP N)) - avg (fun x => ∫ ω', Q x ω' ∂(μP N)) := by
      rw [← avg_sub]; exact avg_congr fun x => integral_pos_neg M G hm C hb hd σ2 hσ x
    have e3 : avg (fun x => ∫ ω', P x ω' ∂(μP N)) = -avg (fun x => ∫ ω', max (G x ω') 0 ∂(μP N)) := by
      rw [← avg_neg']; exact avg_congr hEP
    have e4 : avg (fun x => -P x ω) = -avg (fun x => P x ω) := avg_neg' _
    by_contra hcon
    push_neg at hcon
    rw [e1, e2, e4] at hω
    rw [e3] at hcon
    linarith [hcon.1, hcon.2]
  refine (measureReal_mono hsub).trans ?_
  refine (measureReal_union_le _ _).trans ?_
  linarith

end tails

end IIT2
