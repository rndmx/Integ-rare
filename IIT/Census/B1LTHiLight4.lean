/-
Census, B1 LTBetaHi, round-2 items (a)/(c): **glue for T7**.

* `bd_E0_ev`: on the band event the effect threshold `6η/((a₃Z - η) ln 2)` of `lt3_TCprime` is eventually below any
  fixed `E0 > 0` (`η = bdEta w → 0`).
* `lt3WF_stable`: the kept windowed family only reads safe entries (copy of the `lt3WSel_stable` argument).
* **`lt3Adv_replE`**: the adverse members are unchanged when the private entries are resampled
  (`lt3Adv (replE Priv(w) w η) = lt3Adv w`): they are a function of `F = σ(Priv, entries outside Priv)`, so T7 can
  restrict the conditional product to the non-adverse members.
-/
import IIT.Census.B1LTHiLight3

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-- **The effect threshold is eventually small** on the band event: for any `E0 > 0`, eventually,
`bdGood w → Zs ≥ 1/2 → 6η/((a₃ Zs - η) ln 2) ≤ E0` (`η = bdEta w`), and `3η ≤ a₃ Zs`. -/
theorem bd_E0_ev {E0 : ℝ} (hE0 : 0 < E0) : ∀ᶠ N : ℕ in atTop, ∀ w : Param N, bdGood w → 1 / 2 ≤ Zs w →
    3 * bdEta w ≤ lvK 3 * Zs w ∧ 6 * bdEta w / ((lvK 3 * Zs w - bdEta w) * Real.log 2) ≤ E0 := by
  set δ := min (1 / 16) (E0 / 100) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  filter_upwards [bd_exp_ev (c := Real.exp (-3)) (δ := δ / 22) (Real.exp_pos _) (by positivity),
    bd_exp_ev (c := 1 / 7) (δ := δ / 16) (by norm_num) (by positivity)] with N h1 h2 w hG hZ
  have hP := bd_Pw_le_of_light hG.1 (tcRow w)
  have hlvK : lvK 3 = 25 / 48 := by unfold lvK; norm_num
  have he : Real.exp (-(N : ℝ) / 7) = Real.exp (-(1 / 7 * N)) := by congr 1; ring
  have hη : bdEta w ≤ δ := by
    unfold bdEta
    rw [he]
    linarith
  have hη0 := bdEta_nonneg w
  have hδ1 : δ ≤ 1 / 16 := min_le_left _ _
  have hδ2 : δ ≤ E0 / 100 := min_le_right _ _
  have hA : 1 / 4 ≤ lvK 3 * Zs w := by rw [hlvK]; linarith
  have hl2 := Real.log_two_gt_d9
  have hpos : 0 < (lvK 3 * Zs w - bdEta w) * Real.log 2 := mul_pos (by linarith) (by linarith)
  refine ⟨by linarith, ?_⟩
  rw [div_le_iff₀ hpos]
  have k : (1 / 8 : ℝ) * (69 / 100) ≤ (lvK 3 * Zs w - bdEta w) * Real.log 2 :=
    mul_le_mul (by linarith) (by norm_num at hl2 ⊢; linarith) (by norm_num) (by linarith)
  nlinarith

section Stab

variable {s : State N} {ε γ : ℝ} {n : ℕ}

/-- **The kept windowed family only reads safe entries** (when `P(tc) > e^{-3N/10}`). -/
theorem lt3WF_stable {w w' : Param N} (h : ∀ q ∈ lt3WSafe s ε γ w, w q.1 q.2 = w' q.1 q.2)
    (hP : Real.exp (-(3 / 10 * (N : ℝ))) < Pw w (tcRow w)) :
    lt3WF s ε γ n w' = lt3WF s ε γ n w := by
  classical
  have h0 : ∀ q ∈ lt3Safe s ε w, w q.1 q.2 = w' q.1 q.2 := fun q hq => h q (Or.inl hq)
  obtain ⟨-, -, -, -, hL, hB, hQ⟩ := lt3_core_stable (γ := γ) h0 hP
  have hWQ : lt3WQ s ε γ n w' = lt3WQ s ε γ n w := by
    unfold lt3WQ; rw [hB, hQ]
    refine lt3WQOf_congr n fun j hj r hr => ?_
    have e1 : w r j = w' r j := h (r, j) (Or.inr ⟨hj, r, hr, Or.inl rfl⟩)
    have e2 : w (flip r j) j = w' (flip r j) j := h (flip r j, j) (Or.inr ⟨hj, r, hr, Or.inr rfl⟩)
    show (winBin (n + 1) n.succ_pos (clamp01 (w' r j)), winBin (n + 1) n.succ_pos (clamp01 (w' (flip r j) j))) =
      (winBin (n + 1) n.succ_pos (clamp01 (w r j)), winBin (n + 1) n.succ_pos (clamp01 (w (flip r j) j)))
    rw [← e1, ← e2]
  unfold lt3WF; rw [hWQ, hB]
  exact Finset.filter_congr fun S _ => by simp only [hL]

end Stab

/-- **The adverse members do not see the resampled private entries**:
`lt3Adv (replE Priv(w) w η) = lt3Adv w` (they are `F`-measurable). -/
theorem lt3Adv_replE (s : State N) (ε γ : ℝ) (n : ℕ) (κ : ℝ) (w η : Param N) :
    lt3Adv s ε γ n κ (replE (stPriv (lt3WSel s ε γ n) lt3PB w) w η) = lt3Adv s ε γ n κ w := by
  classical
  set A := stPriv (lt3WSel s ε γ n) lt3PB w with hA
  set w' := replE A w η with hw'
  have hnA : ∀ q ∈ lt3WSafe s ε γ w, q ∉ A := fun q hq hqA => by
    obtain ⟨k, hk', hq'⟩ := mem_biUnion.1 hqA
    exact lt3WPB_not_safe w k hk' q hq' hq
  have hsafe : ∀ q ∈ lt3WSafe s ε γ w, w q.1 q.2 = w' q.1 q.2 := by
    rintro ⟨q1, q2⟩ hq
    show w q1 q2 = (if (q1, q2) ∈ A then η q1 q2 else w q1 q2)
    rw [if_neg (hnA _ hq)]
  have hSel : lt3WSel s ε γ n w' = lt3WSel s ε γ n w := lt3WSel_stable hsafe
  have hPriv : stPriv (lt3WSel s ε γ n) lt3PB w' = A := by
    rw [hA]; unfold stPriv; rw [hSel]
  have hHf : lt3Hf s ε γ n w' = lt3Hf s ε γ n w := by
    rw [lt3Hf_def, lt3Hf_def, hPriv, ← hA]
    funext r j
    simp only [stHalf]
    by_cases h : (r, j) ∈ A
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, hw']
      show (if (r, j) ∈ A then η r j else w r j) = w r j
      rw [if_neg h]
  by_cases hP : Real.exp (-(3 / 10 * (N : ℝ))) < Pw w (tcRow w)
  · have hWF : lt3WF s ε γ n w' = lt3WF s ε γ n w := lt3WF_stable hsafe hP
    unfold lt3Adv
    rw [hWF, hHf]
  · have hS0 : lt3WSel s ε γ n w = ∅ := by unfold lt3WSel; rw [if_neg (fun hc => hP hc.1)]
    have hA0 : A = ∅ := by rw [hA]; unfold stPriv; rw [hS0]; simp
    have hww : w' = w := by
      rw [hw', hA0]; funext r j
      show (if (r, j) ∈ (∅ : Finset (State N × Fin N)) then η r j else w r j) = w r j
      rw [if_neg (Finset.notMem_empty _)]
    rw [hww]

end Census
end IIT
