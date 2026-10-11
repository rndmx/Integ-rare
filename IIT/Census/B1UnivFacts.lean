/-
Census, B1 lower bound, leaf `phi_univ_ge_EX`: deterministic facts read off the fixed rows on `EX`,
and small algebraic tools.

* `EX_y_ge`  : every entry of row `r0` is `≥ f = 1001/2000`.
* `EX_xE_ge` : every `x_k` of row `s` is `≥ 1/2 + 1/10^5`.
* `keyHyp0_of_means` : `keyHyp_of_means` without the small-cut hypothesis (H).
* `sysBackCause_univ_eq` : `β = P(r0)/Z` at `S = univ`.
* `sysEffProb_univ_teW` : `e = eE w s` at `te = teW w s`.
-/
import IIT.Census.B1LowerB
import IIT.Census.B1Tier1
import IIT.Census.B1Proxy
import IIT.Census.B1Couple

set_option maxRecDepth 100000

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-! ### Row facts on `EX` -/

/-- Every unit lies in some pair cell. -/
lemma EX_pair_cover {s r0 : State N} {x : Fin N} {w : Param N} (hw : w ∈ EX N s r0 x) (j : Fin N) :
    ∃ i : Fin KP, (w r0 j, w (flipAt x r0) j) ∈ exIP (cP i) := by
  classical
  by_contra hno
  push Not at hno
  set F : Fin KP → Finset (Fin N) := fun i => univ.filter fun j => (w r0 j, w (flipAt x r0) j) ∈ exIP (cP i)
  have hdisj : ((univ : Finset (Fin KP)) : Set (Fin KP)).PairwiseDisjoint F := by
    intro i _ i' _ hii'
    refine Finset.disjoint_filter.2 fun j _ h1 h2 => ?_
    exact Set.disjoint_left.1 (exIP_disjoint hii') h1 h2
  have hcard : (univ.biUnion F).card = N := by
    rw [card_biUnion hdisj]
    refine Eq.trans ?_ (nP_sum N)
    exact sum_congr rfl fun i _ => hw.1 i
  have hsub : univ.biUnion F ⊆ univ.erase j := by
    intro j' hj'
    obtain ⟨i, -, hi⟩ := mem_biUnion.1 hj'
    refine mem_erase.2 ⟨fun e => ?_, mem_univ _⟩
    rw [e] at hi
    exact hno i (mem_filter.1 hi).2
  have := card_le_card hsub
  rw [hcard, card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin] at this
  have hN : 0 < N := Fin.pos j
  omega

/-- Every entry of row `s` lies in some row-`s` cell. -/
lemma EX_s_cover {s r0 : State N} {x : Fin N} {w : Param N} (hw : w ∈ EX N s r0 x) (k : Fin N) :
    ∃ i : Fin KS, w s k ∈ exIS (cS i) := by
  classical
  by_contra hno
  push Not at hno
  set F : Fin KS → Finset (Fin N) := fun i => univ.filter fun k => w s k ∈ exIS (cS i)
  have hdisj : ((univ : Finset (Fin KS)) : Set (Fin KS)).PairwiseDisjoint F := by
    intro i _ i' _ hii'
    refine Finset.disjoint_filter.2 fun j _ h1 h2 => ?_
    exact Set.disjoint_left.1 (exIS_disjoint hii') h1 h2
  have hcard : (univ.biUnion F).card = N := by
    rw [card_biUnion hdisj]
    refine Eq.trans ?_ (nS_sum N)
    exact sum_congr rfl fun i _ => hw.2 i
  have hsub : univ.biUnion F ⊆ univ.erase k := by
    intro j' hj'
    obtain ⟨i, -, hi⟩ := mem_biUnion.1 hj'
    refine mem_erase.2 ⟨fun e => ?_, mem_univ _⟩
    rw [e] at hi
    exact hno i (mem_filter.1 hi).2
  have := card_le_card hsub
  rw [hcard, card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin] at this
  have hN : 0 < N := Fin.pos k
  omega

/-- **Row `r0` is above `f`.** -/
lemma EX_y_ge {s r0 : State N} {x : Fin N} {w : Param N} (hw : w ∈ EX N s r0 x) (j : Fin N) :
    (1001 / 2000 : ℝ) ≤ clamp01 (w r0 j) := by
  obtain ⟨i, hi⟩ := EX_pair_cover hw j
  have hm := cell_mem (cP_mem i) hi
  have hf : ((exF : ℚ) : ℝ) = 1001 / 2000 := by unfold exF; norm_num
  have hy := exYlo_ge (cP i)
  have hy' : ((exF : ℚ) : ℝ) ≤ (exYlo (cP i) : ℝ) := by exact_mod_cast hy
  rw [hm.2.2.2.2.2.2.2.1]
  linarith [hm.1]

/-- The row-`s` cells avoid a window around `1/2`. -/
def exSGap (C : EXSCell) : Bool :=
  decide (C.x1 ≤ 1 / 2 - 1 / 100000) || decide (1 / 2 + 1 / 100000 ≤ C.x0)

set_option maxHeartbeats 0 in
theorem exSCells_gap : exSCells.all exSGap = true := by decide +kernel

/-- **Row `s` is away from `1/2`.** -/
lemma EX_xE_ge {s r0 : State N} {x : Fin N} {w : Param N} (hw : w ∈ EX N s r0 x) (k : Fin N) :
    (1 / 2 + 1 / 100000 : ℝ) ≤ xE w s k := by
  obtain ⟨i, hi⟩ := EX_s_cover hw k
  have hg := (List.all_eq_true.1 exSCells_gap) (cS i) (cS_mem i)
  obtain ⟨-, h0, -, h1, -⟩ := exS_facts (cS_mem i)
  have h0' : (0 : ℝ) ≤ (cS i).x0 := by exact_mod_cast h0
  have h1' : ((cS i).x1 : ℝ) ≤ 1 := by exact_mod_cast h1
  obtain ⟨hlo, hhi⟩ := hi
  have hc : clamp01 (w s k) = w s k := by
    unfold clamp01; rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  unfold xE
  rw [hc]
  unfold exSGap at hg
  rcases Bool.or_eq_true _ _ ▸ hg with h | h
  · have h' : ((cS i).x1 : ℝ) ≤ 1 / 2 - 1 / 100000 := by
      have := (Rat.cast_le (K := ℝ)).2 (of_decide_eq_true h); push_cast at this; exact this
    exact le_max_of_le_right (by linarith)
  · have h' : (1 / 2 + 1 / 100000 : ℝ) ≤ (cS i).x0 := by
      have := (Rat.cast_le (K := ℝ)).2 (of_decide_eq_true h); push_cast at this; exact this
    exact le_max_of_le_left (by linarith)

/-! ### `KeyHyp0` from subcube means (no small-cut hypothesis) -/

/-- `keyHyp_of_means` without (H). -/
theorem keyHyp0_of_means {lam : Fin N → Finset (Fin N) → ℝ} {x : Fin N → ℝ}
    {A : Fin N → Finset (Fin N) → ℝ} {δ : ℕ → ℝ} {lmin : ℝ} {D dstar : ℕ}
    (hlam : ∀ j C, lam j C = Real.logb 2 (x j / A j C)) (hA_empty : ∀ j, A j ∅ = x j)
    (hx0 : ∀ j, 0 < x j) (hA0 : ∀ j C, 0 < A j C) (hA1 : ∀ j C, A j C ≤ 1)
    (hconc : ∀ j C, j ∉ C → D ≤ C.card → |A j C - 1 / 2| ≤ δ C.card)
    (hδ0 : ∀ d, 0 ≤ δ d) (hδs : δ (N - 1) ≤ 1 / 100)
    (hδanti : ∀ d d', D ≤ d → d ≤ d' → δ d' ≤ δ d)
    (hD : 1 ≤ D) (hDN : D ≤ N - 1) (hDd : 2 * D ≤ dstar)
    (hP : 0 < lmin) (hmin : ∀ j, lmin ≤ kF lam j)
    (hBfar : ∀ d, dstar ≤ d → d + 2 ≤ N →
      ((N : ℝ) - 1) * (3 * (δ d + δ (N - 1))) < lmin)
    (hS : ∀ A' : Finset (Fin N), A'.card < 2 * D →
      2 * D * ((1 + 3 * δ (N - 1)) + lmin) + N * (3 * (δ D + δ (N - 1))) <
        ∑ j ∈ A'ᶜ, (kF lam j - lmin))
    (hLS : ∀ Q : Finset (Fin N), N - dstar < Q.card →
      Q.card * (3 * (δ (2 * D) + δ (N - 1))) < ∑ j ∈ Q, (kF lam j - lmin)) :
    KeyHyp0 lam lmin (1 + 3 * δ (N - 1)) (fun d => 3 * (δ d + δ (N - 1))) D dstar := by
  have hfullcard : ∀ j : Fin N, (univ.erase j).card = N - 1 := fun j => by
    rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
  have hq : ∀ j, |A j (univ.erase j) - 1 / 2| ≤ δ (N - 1) := fun j => by
    have := hconc j (univ.erase j) (notMem_erase j univ) (by rw [hfullcard]; exact hDN)
    rwa [hfullcard] at this
  have hxq : ∀ j, 1 / 2 - δ (N - 1) ≤ x j := by
    intro j
    have hF : 0 < kF lam j := lt_of_lt_of_le hP (hmin j)
    unfold kF at hF
    rw [hlam] at hF
    have h1 : 1 < x j / A j (univ.erase j) := by
      by_contra h; push Not at h
      exact absurd hF (not_lt.2 (Real.logb_nonpos one_lt_two
        (div_pos (hx0 j) (hA0 j _)).le h))
    rw [one_lt_div (hA0 j _)] at h1
    have := (abs_le.1 (hq j)).1
    linarith
  exact
    { lam_empty := fun j => by rw [hlam, hA_empty, div_self (hx0 j).ne', Real.logb_one]
      hP := hP
      hmin := hmin
      ha := by have := hδ0 (N - 1); linarith
      hA := fun j C _ _ => by
        rw [hlam]
        have h1 : Real.logb 2 (x j) ≤ Real.logb 2 (x j / A j C) :=
          Real.logb_le_logb_of_le one_lt_two (hx0 j)
            ((le_div_iff₀ (hA0 j C)).2 (by nlinarith [hA1 j C, hx0 j]))
        have h2 : Real.logb 2 (1 / 2 - δ (N - 1)) ≤ Real.logb 2 (x j) :=
          Real.logb_le_logb_of_le one_lt_two (by linarith) (hxq j)
        have h3 := logb_half_sub_ge (hδ0 (N - 1)) hδs
        linarith
      hD := hD
      hDd := hDd
      hBmid := fun j C hjC hDC => by
        unfold kF
        rw [hlam, hlam]
        have := logb_shift (hx0 j) (hA0 j _) (hA0 j C) (hq j) (hconc j C hjC hDC) hδs
        linarith
      eps_nonneg := fun d => by have := hδ0 d; have := hδ0 (N - 1); positivity
      eps_anti := fun d d' hd hdd' => by have := hδanti d d' hd hdd'; linarith
      hBfar := hBfar
      hS := hS
      hLS := hLS }

/-! ### `β` and `e` at `S = univ` -/

lemma prod_Num_univ (w : Param N) (t : State N) :
    ∏ i, Num w univ univ t i = Pw w t * Zs w ^ N := by
  simp_rw [Num_univ_eq, cmean_univ]
  rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
  rfl

/-- **`β = P(t)/Z`** at `S = univ`. -/
theorem sysBackCause_univ_eq {z : Param N} (hz : z ∈ openCube N) (s t : State N) :
    sysBackCause (tpmOf z) univ s s t = Pw (flipP s z) t / Zs (flipP s z) := by
  rw [sysBackCause_eq_Num hz s t univ, card_univ, Fintype.card_fin, Nat.sub_self, pow_zero, one_mul]
  simp_rw [prod_Num_univ]
  rw [← sum_mul]
  have hZ := Zs_pos hz s
  have hsum : ∑ t' : State N, Pw (flipP s z) t' = Zs (flipP s z) := rfl
  rw [hsum]
  have : Zs (flipP s z) ^ N ≠ 0 := pow_ne_zero _ hZ.ne'
  field_simp

/-- **`e = eE`** at `S = univ`, `te = teW`. -/
theorem sysEffProb_univ_teW (z : Param N) (s : State N) :
    sysEffProb (tpmOf z) univ s s (teW (flipP s z) s) = eE (flipP s z) s := by
  rw [sysEffProb_univ, fullProb, eE]
  exact prod_congr rfl fun k _ => prob_teW z s k

end Census
end IIT
