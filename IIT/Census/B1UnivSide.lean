/-
Census, B1 lower bound, leaf `phi_univ_ge_EX`: one side of `univ` (cause or effect) satisfies the W10
hypotheses (`KeyHyp0` and the small-cut bound (H) on a family of `K`) as soon as
* subcube concentration `|A_j(C) - 1/2| ≤ δ_{|C|}` holds for big cuts (`D ≤ |C|`), and
* the truncated small-cut sums `Σ_{j ∉ K} min(λ_j(K), c'_j) > 8 D` hold for the small `K` of the
  family, where `c'_j = (max 0 (ln (x_j / cm)) - 7 δ_{N-1}) / ln 2` is a lower proxy of
  `F_j - λ_min` (`trunc_gen`) that reads only the side's own top entries `x_j`.
Spread (`hS`) and (LS) are DERIVED from one small-cut sum (a singleton `{k0}`): no separate event.
-/
import IIT.Census.B1UnivFacts
import IIT.Census.B1Events

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- The lower proxy of `F_j - λ_min` (log base 2). -/
noncomputable def cpx (x : Fin N → ℝ) (cm δ1 : ℝ) (j : Fin N) : ℝ :=
  (max 0 (Real.log (x j / cm)) - 7 * δ1) / Real.log 2

lemma cpx_le_one {x : Fin N → ℝ} {cm δ1 : ℝ} (hx0 : ∀ j, 0 < x j) (hx1 : ∀ j, x j ≤ 1)
    (hcm : 1 / 2 ≤ cm) (hδ1 : 0 ≤ δ1) (j : Fin N) : cpx x cm δ1 j ≤ 1 := by
  unfold cpx
  have hl2 := Real.log_pos one_lt_two
  rw [div_le_one hl2]
  have h1 : max 0 (Real.log (x j / cm)) ≤ Real.log 2 := by
    refine max_le hl2.le ?_
    have hcm0 : 0 < cm := by linarith
    have : x j / cm ≤ 2 := by rw [div_le_iff₀ hcm0]; linarith [hx1 j]
    exact Real.log_le_log (div_pos (hx0 j) hcm0) this
  linarith

lemma cpx_le_kF {lam : Fin N → Finset (Fin N) → ℝ} {x : Fin N → ℝ}
    {A : Fin N → Finset (Fin N) → ℝ} {δ1 lmin cm : ℝ}
    (hlam : ∀ j C, lam j C = Real.logb 2 (x j / A j C)) (hx0 : ∀ j, 0 < x j)
    (hA0 : ∀ j C, 0 < A j C) (hq : ∀ j, |A j (univ.erase j) - 1 / 2| ≤ δ1) (hδ : δ1 ≤ 1 / 100)
    (hmin : ∀ j, lmin ≤ kF lam j) {k : Fin N} (hk : x k ≤ cm) (j : Fin N) :
    cpx x cm δ1 j ≤ kF lam j - lmin := by
  have h := trunc_gen hlam hx0 hA0 hq hδ hmin hk j
  unfold cpx
  rw [div_le_iff₀ (Real.log_pos one_lt_two)]
  exact h

/-- **One side of `univ` satisfies the W10 hypotheses.** -/
theorem side_keyHyp {lam : Fin N → Finset (Fin N) → ℝ} {x : Fin N → ℝ}
    {A : Fin N → Finset (Fin N) → ℝ} {δ : ℕ → ℝ} {lmin cm : ℝ} {D dstar : ℕ}
    (hlam : ∀ j C, lam j C = Real.logb 2 (x j / A j C)) (hA_empty : ∀ j, A j ∅ = x j)
    (hx0 : ∀ j, 0 < x j) (hx1 : ∀ j, x j ≤ 1) (hA0 : ∀ j C, 0 < A j C) (hA1 : ∀ j C, A j C ≤ 1)
    (hconc : ∀ j C, j ∉ C → D ≤ C.card → |A j C - 1 / 2| ≤ δ C.card)
    (hδ0 : ∀ d, 0 ≤ δ d) (hδs : δ (N - 1) ≤ 1 / 100)
    (hδanti : ∀ d d', D ≤ d → d ≤ d' → δ d' ≤ δ d)
    (hD : 2 ≤ D) (hDN : D ≤ N - 1) (hDd : 2 * D ≤ dstar) (hdD : dstar ≤ 7 * D)
    (hNδD : (N : ℝ) * δ D ≤ 1 / 100) (hNδ : (N : ℝ) * δ (N - 1) ≤ 1 / 100)
    (hBfar : ∀ d, dstar ≤ d → d + 2 ≤ N → (N : ℝ) * (δ d + δ (N - 1)) ≤ 1 / 10 ^ 6)
    (hP : 1 / 10 ^ 5 ≤ lmin) (hmin : ∀ j, lmin ≤ kF lam j)
    (hcm : ∃ k, x k ≤ cm) (hcm2 : 1 / 2 ≤ cm)
    (good : Finset (Fin N) → Prop) (k0 : Fin N) (hk0 : good {k0})
    (hsmall : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < D → good K →
      8 * (D : ℝ) < ∑ j ∈ Kᶜ, min (lam j K) (cpx x cm (δ (N - 1)) j)) :
    KeyHyp0 lam lmin (1 + 3 * δ (N - 1)) (fun d => 3 * (δ d + δ (N - 1))) D dstar ∧
    ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < D → good K →
      D * ((1 + 3 * δ (N - 1)) + 2 * lmin) + N * (3 * (δ D + δ (N - 1))) < kM lam lmin K := by
  obtain ⟨k, hk⟩ := hcm
  have hfullcard : ∀ j : Fin N, (univ.erase j).card = N - 1 := fun j => by
    rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
  have hq : ∀ j, |A j (univ.erase j) - 1 / 2| ≤ δ (N - 1) := fun j => by
    have := hconc j (univ.erase j) (notMem_erase j univ) (by rw [hfullcard]; omega)
    rwa [hfullcard] at this
  have hδN0 := hδ0 (N - 1)
  have hδD0 := hδ0 D
  have hDr : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hc'c : ∀ j, cpx x cm (δ (N - 1)) j ≤ kF lam j - lmin :=
    fun j => cpx_le_kF hlam hx0 hA0 hq hδs hmin hk j
  have hc'1 : ∀ j, cpx x cm (δ (N - 1)) j ≤ 1 := fun j => cpx_le_one hx0 hx1 hcm2 hδN0 j
  have hc0 : ∀ j, 0 ≤ kF lam j - lmin := fun j => sub_nonneg.2 (hmin j)
  have hlmax : lmin ≤ 1 + 3 * δ (N - 1) :=
    (hmin k).trans (kF_le_of_means hlam hx0 hx1 hA0 hq hδN0 hδs k)
  -- the singleton sum
  have hsing : 8 * (D : ℝ) < ∑ j ∈ ({k0} : Finset (Fin N))ᶜ, cpx x cm (δ (N - 1)) j := by
    have h := hsmall {k0} (by simp) (by rw [card_singleton]; omega) hk0
    exact h.trans_le (sum_le_sum fun j _ => min_le_right _ _)
  -- removing a set `B` from the singleton sum costs at most `|B|`
  have hrem : ∀ B : Finset (Fin N),
      8 * (D : ℝ) - B.card < ∑ j ∈ Bᶜ, (kF lam j - lmin) := by
    intro B
    have h1 : ∑ j ∈ ({k0} : Finset (Fin N))ᶜ, cpx x cm (δ (N - 1)) j =
        ∑ j ∈ ({k0} : Finset (Fin N))ᶜ ∩ B, cpx x cm (δ (N - 1)) j +
          ∑ j ∈ ({k0} : Finset (Fin N))ᶜ \ B, cpx x cm (δ (N - 1)) j :=
      (sum_inter_add_sum_sdiff _ _ _).symm
    have h2 : ∑ j ∈ ({k0} : Finset (Fin N))ᶜ ∩ B, cpx x cm (δ (N - 1)) j ≤ B.card := by
      calc _ ≤ ∑ _j ∈ ({k0} : Finset (Fin N))ᶜ ∩ B, (1 : ℝ) := sum_le_sum fun j _ => hc'1 j
        _ = (({k0} : Finset (Fin N))ᶜ ∩ B).card := by simp
        _ ≤ B.card := by exact_mod_cast card_le_card inter_subset_right
    have h3 : ∑ j ∈ ({k0} : Finset (Fin N))ᶜ \ B, cpx x cm (δ (N - 1)) j ≤
        ∑ j ∈ Bᶜ, (kF lam j - lmin) := by
      calc _ ≤ ∑ j ∈ ({k0} : Finset (Fin N))ᶜ \ B, (kF lam j - lmin) := sum_le_sum fun j _ => hc'c j
        _ ≤ ∑ j ∈ Bᶜ, (kF lam j - lmin) :=
          sum_le_sum_of_subset_of_nonneg (fun j hj => mem_compl.2 (mem_sdiff.1 hj).2)
            fun j _ _ => hc0 j
    linarith
  have hBfar' : ∀ d, dstar ≤ d → d + 2 ≤ N → ((N : ℝ) - 1) * (3 * (δ d + δ (N - 1))) < lmin := by
    intro d hd hd2
    have h := hBfar d hd hd2
    have hdd := hδ0 d
    have : ((N : ℝ) - 1) * (3 * (δ d + δ (N - 1))) ≤ 3 * ((N : ℝ) * (δ d + δ (N - 1))) := by
      nlinarith
    have : (3 : ℝ) * (1 / 10 ^ 6) < 1 / 10 ^ 5 := by norm_num
    linarith
  refine ⟨keyHyp0_of_means hlam hA_empty hx0 hA0 hA1 hconc hδ0 hδs hδanti (by omega) hDN hDd
    (lt_of_lt_of_le (by norm_num) hP) hmin hBfar' (fun A' hA' => ?_) (fun Q hQ => ?_), ?_⟩
  · -- spread
    have h := hrem A'
    have hA'r : (A'.card : ℝ) < 2 * D := by exact_mod_cast hA'
    nlinarith
  · -- (LS)
    have h := hrem Qᶜ
    rw [compl_compl] at h
    have hQc : (Qᶜ.card : ℝ) < dstar := by
      have h1 : Qᶜ.card = N - Q.card := by rw [card_compl, Fintype.card_fin]
      have h2 : Q.card ≤ N := by simpa using card_le_univ Q
      have : Qᶜ.card < dstar := by omega
      exact_mod_cast this
    have hdr : (dstar : ℝ) ≤ 7 * D := by exact_mod_cast hdD
    have hQN : (Q.card : ℝ) ≤ N := by exact_mod_cast (by simpa using card_le_univ Q)
    have h2D := hδanti D (2 * D) le_rfl (by omega)
    have h2D0 := hδ0 (2 * D)
    have : (Q.card : ℝ) * (3 * (δ (2 * D) + δ (N - 1))) ≤ N * (3 * (δ D + δ (N - 1))) := by
      apply mul_le_mul hQN (by linarith) (by positivity) (Nat.cast_nonneg _)
    nlinarith
  · intro K hK1 hKD hKg
    have h := hsmall K hK1 hKD hKg
    have hle : ∑ j ∈ Kᶜ, min (lam j K) (cpx x cm (δ (N - 1)) j) ≤ kM lam lmin K :=
      sum_le_sum fun j _ => min_le_min le_rfl (hc'c j)
    nlinarith

end Census
end IIT
