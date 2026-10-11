/-
Census, module B1UnivMIP part 5: from the B1 good events to the W10 hypotheses.

The events are W3 §8.1's `SpreadGood` (threshold `5D`) and `SmallCutGood` (threshold `7D`), and W10's
`SpreadLarge` in count form: fewer than `N/5` units have `Fⱼ - λ_min ≤ η`.  Together with the
smallness of the subcube deviations `δ` they give `KeyHyp` through `keyHyp_of_means`.
-/
import IIT.Census.B1Lemma43

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- A full-cut value is at most `1 + 3δ_{N-1}`. -/
lemma kF_le_of_means {lam : Fin N → Finset (Fin N) → ℝ} {x : Fin N → ℝ}
    {A : Fin N → Finset (Fin N) → ℝ} {δ : ℕ → ℝ}
    (hlam : ∀ j C, lam j C = Real.logb 2 (x j / A j C)) (hx0 : ∀ j, 0 < x j) (hx1 : ∀ j, x j ≤ 1)
    (hA0 : ∀ j C, 0 < A j C) (hq : ∀ j, |A j (univ.erase j) - 1 / 2| ≤ δ (N - 1))
    (hδ0 : 0 ≤ δ (N - 1)) (hδs : δ (N - 1) ≤ 1 / 100) (j : Fin N) :
    kF lam j ≤ 1 + 3 * δ (N - 1) := by
  unfold kF
  rw [hlam]
  have hq' := (abs_le.1 (hq j)).1
  have hA := hA0 j (univ.erase j)
  have h1 : Real.logb 2 (x j / A j (univ.erase j)) ≤ Real.logb 2 (1 / (1 / 2 - δ (N - 1))) :=
    Real.logb_le_logb_of_le one_lt_two (div_pos (hx0 j) hA)
      (div_le_div₀ (by norm_num) (hx1 j) (by linarith) (by linarith))
  have h2 : Real.logb 2 (1 / (1 / 2 - δ (N - 1))) = -Real.logb 2 (1 / 2 - δ (N - 1)) := by
    rw [one_div, Real.logb_inv]
  have h3 := logb_half_sub_ge hδ0 hδs
  linarith

/-- `SpreadLarge` in count form gives (LS). -/
lemma hLS_of_count {f : Fin N → ℝ} {η e : ℝ} {dstar : ℕ} (hf : ∀ j, 0 ≤ f j)
    (hcount : 5 * (univ.filter fun j => f j ≤ η).card < N) (hηe : 2 * e < η) (he0 : 0 ≤ e)
    (hd : 5 * dstar ≤ 3 * N) (Q : Finset (Fin N)) (hQ : N - dstar < Q.card) :
    Q.card * e < ∑ j ∈ Q, f j := by
  set Cl := univ.filter fun j => f j ≤ η
  set G := Q.filter fun j => η < f j
  have hη0 : 0 < η := by linarith
  have hG : Q.card ≤ G.card + Cl.card := by
    have hsub : Q ⊆ G ∪ Cl := fun j hj => by
      by_cases h : η < f j
      · exact mem_union_left _ (mem_filter.2 ⟨hj, h⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨mem_univ j, not_lt.1 h⟩)
    exact (card_le_card hsub).trans (card_union_le _ _)
  have hsum : (G.card : ℝ) * η ≤ ∑ j ∈ Q, f j := by
    calc (G.card : ℝ) * η ≤ ∑ j ∈ G, f j := by
          have := card_nsmul_le_sum G f η fun j hj => (mem_filter.1 hj).2.le
          simpa [nsmul_eq_mul] using this
      _ ≤ ∑ j ∈ Q, f j := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ => hf j
  have hGQ : (Q.card : ℝ) < 2 * G.card := by
    have : Q.card < 2 * G.card := by omega
    exact_mod_cast this
  have hQ0 : (0 : ℝ) < Q.card := by
    have : 0 < Q.card := by omega
    exact_mod_cast this
  nlinarith

/-- **From the B1 events to `KeyHyp`.** -/
theorem keyHyp_of_events {lam : Fin N → Finset (Fin N) → ℝ} {x : Fin N → ℝ}
    {A : Fin N → Finset (Fin N) → ℝ} {δ : ℕ → ℝ} {lmin η : ℝ} {D dstar : ℕ}
    (hlam : ∀ j C, lam j C = Real.logb 2 (x j / A j C)) (hA_empty : ∀ j, A j ∅ = x j)
    (hx0 : ∀ j, 0 < x j) (hx1 : ∀ j, x j ≤ 1) (hA0 : ∀ j C, 0 < A j C) (hA1 : ∀ j C, A j C ≤ 1)
    (hconc : ∀ j C, j ∉ C → D ≤ C.card → |A j C - 1 / 2| ≤ δ C.card)
    (hδ0 : ∀ d, 0 ≤ δ d) (hδs : δ (N - 1) ≤ 1 / 100)
    (hδanti : ∀ d d', D ≤ d → d ≤ d' → δ d' ≤ δ d)
    (hD : 1 ≤ D) (hDN : D ≤ N - 1) (hDd : 2 * D ≤ dstar) (hd5 : 5 * dstar ≤ 3 * N)
    (hP : 0 < lmin) (hmin : ∀ j, lmin ≤ kF lam j) (hj0 : Nonempty (Fin N))
    (hδc : 12 * D * δ (N - 1) + 3 * N * (δ D + δ (N - 1)) < D)
    (hBfar : ∀ d, dstar ≤ d → d + 2 ≤ N → ((N : ℝ) - 1) * (3 * (δ d + δ (N - 1))) < lmin)
    (hS5 : ∀ A' : Finset (Fin N), A'.card < 2 * D → 5 * (D : ℝ) < ∑ j ∈ A'ᶜ, (kF lam j - lmin))
    (hH7 : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < D → 7 * (D : ℝ) < kM lam lmin K)
    (hcount : 5 * (univ.filter fun j => kF lam j - lmin ≤ η).card < N)
    (hη : 6 * (δ (2 * D) + δ (N - 1)) < η) :
    KeyHyp lam lmin (1 + 3 * δ (N - 1)) (fun d => 3 * (δ d + δ (N - 1))) D dstar := by
  have hfull : ∀ j : Fin N, (univ.erase j).card = N - 1 := fun j => by
    rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
  have hq : ∀ j, |A j (univ.erase j) - 1 / 2| ≤ δ (N - 1) := fun j => by
    have := hconc j (univ.erase j) (notMem_erase j univ) (by rw [hfull]; exact hDN)
    rwa [hfull] at this
  obtain ⟨j0⟩ := hj0
  have hlb : lmin ≤ 1 + 3 * δ (N - 1) :=
    (hmin j0).trans (kF_le_of_means hlam hx0 hx1 hA0 hq (hδ0 _) hδs j0)
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hδN := hδ0 (N - 1)
  have hδD := hδ0 D
  refine keyHyp_of_means hlam hA_empty hx0 hA0 hA1 hconc hδ0 hδs hδanti hD hDN hDd hP hmin hBfar
    (fun A' hA' => ?_) (fun K hK1 hKD => ?_) (fun Q hQ => ?_)
  · have := hS5 A' hA'
    nlinarith
  · have := hH7 K hK1 hKD
    nlinarith
  · exact hLS_of_count (fun j => sub_nonneg.2 (hmin j)) hcount (by linarith)
      (by have := hδ0 (2 * D); positivity) hd5 Q hQ

end Census
end IIT
