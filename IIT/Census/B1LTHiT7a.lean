/-
Census, B1 LTBetaHi, T7 part A: **the effect box of a light `s`** (item (e)) and resampling helpers.

For a light current state `s` (`s ∉ lt3H w`), the effect side of a member `S` comes from Lemma EF in every direction
(`tp_eff_dir`): the own entries `w s j` avoid `(1/2 - γ, 1/2 + γ)` (units of `Q` are not in `lt3Ex`), and the
private entries of `s`'s block `lt3PB (S, s)` must lie near `0` or `1` according to the direction of `w s j`.

* `lt3ETgt`, `lt3EBox s S w0 ρ` (the effect box, targets read from `w0`'s row `s`): measurable (`lt3EBox_mset`),
  determined by `lt3PB (S, s)` (`lt3EBox_detOn`), probability `≥ ρ^24` (`lt3EBox_prob`).
* `lt3PB_mem_of_agree`: the private entries of Lemma EF (`r` agreeing with `s` off `S`, flipped at some `i ≠ j`)
  are exactly entries of `lt3PB (S, s)`.
* **`lt3_heff_light`**: own entries outside `(1/2 - γ, 1/2 + γ)` and `w ∈ lt3EBox s S w ρ` give the effect
  conclusion (the `heff` input of `lt3_TCprime`) with `E0 = (1/2+γ)³ log₂(1/(1 - (1/2+γ-ρ)/2))`.
* Resampling the windowed private positions: safe entries, the selection, `Priv` and the row `s` are unchanged
  (`lt3W_replE_safe`, `lt3W_replE_sel`, `lt3W_replE_priv`, `lt3W_replE_row_s`), and `replE_replE`.
-/
import IIT.Census.B1LTHiT6d
import IIT.Census.B1LTHiEffFlip

namespace IIT
namespace Census

open MeasureTheory Finset

set_option linter.unusedSectionVars false

variable {N : ℕ}

/-! ### The effect box -/

/-- The effect target at column `j` of the private entries of `s`'s block: `0` if `y_{s,j} > 1/2`, else `1`. -/
noncomputable def lt3ETgt (w : Param N) (s : State N) (j : Fin N) : ℝ :=
  if 1 / 2 < clamp01 (w s j) then 0 else 1

/-- **The effect box** of member `S` for the current state `s` (targets read from the row `s` of `w0`). -/
def lt3EBox (s : State N) (S : Finset (Fin N)) (w0 : Param N) (ρ : ℝ) : Set (Param N) :=
  {η | ∀ q ∈ lt3PB (S, s), |clamp01 (η q.1 q.2) - lt3ETgt w0 s q.2| ≤ ρ}

lemma lt3EBox_mset (s : State N) (S : Finset (Fin N)) (w0 : Param N) (ρ : ℝ) :
    MeasurableSet (lt3EBox s S w0 ρ) := by
  have e1 : lt3EBox s S w0 ρ = ⋂ q ∈ lt3PB (S, s),
      {η : Param N | |clamp01 (η q.1 q.2) - lt3ETgt w0 s q.2| ≤ ρ} := by
    ext η; simp [lt3EBox]
  rw [e1]
  exact MeasurableSet.biInter (Set.to_countable _) fun q _ =>
    measurableSet_le (continuous_abs.measurable.comp ((b1m_clamp _ _).sub measurable_const)) measurable_const

lemma lt3EBox_detOn (s : State N) (S : Finset (Fin N)) (w0 : Param N) (ρ : ℝ) :
    DetOnE (lt3PB (S, s)) (lt3EBox s S w0 ρ) := by
  intro w w' h
  simp only [lt3EBox, Set.mem_setOf_eq]
  exact forall₂_congr fun q hq => by rw [h q hq]

/-- **The effect box has probability `≥ ρ^24`.** -/
theorem lt3EBox_prob (s : State N) {S : Finset (Fin N)} (hS : S.card ≤ 3) (w0 : Param N) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) : ENNReal.ofReal (ρ ^ 24) ≤ cubeM N (lt3EBox s S w0 ρ) := by
  classical
  have hE : Function.Injective fun b : {q // q ∈ lt3PB (S, s)} => (b.1 : State N × Fin N) :=
    Subtype.val_injective
  have h := cubeM_box_ge (B := {q // q ∈ lt3PB (S, s)}) (fun b => b.1) hE (fun b => lt3ETgt w0 s b.1.2)
    (fun b => by unfold lt3ETgt; split_ifs <;> norm_num) hρ0 hρ1
  rw [Fintype.card_coe] at h
  have hc : (lt3PB (S, s)).card ≤ 24 := lt3PB_card_le (S, s) hS
  refine le_trans (ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hρ0 hρ1 hc)) (h.trans (le_of_eq (congrArg _ ?_)))
  ext η
  simp only [lt3EBox, Set.mem_setOf_eq]
  exact ⟨fun h q hq => h ⟨q, hq⟩, fun h b => h b.1 b.2⟩

/-- **The private entries of Lemma EF are those of `s`'s block.** -/
lemma lt3PB_mem_of_agree {s r : State N} {S : Finset (Fin N)} (hr : r ∈ agree Sᶜ s) {j : Fin N} (hj : j ∈ S)
    (hi : ∃ i ∈ S, i ≠ j ∧ r i ≠ s i) : (r, j) ∈ lt3PB (S, s) := by
  classical
  obtain ⟨i, hiS, hij, hri⟩ := hi
  set R := S.filter fun k => r k ≠ s k with hR
  have hflip : flipS s R = r := by
    funext k
    unfold flipS
    by_cases hk : k ∈ R
    · rw [if_pos hk]
      have h := (mem_filter.1 hk).2
      cases h1 : r k <;> cases h2 : s k <;> simp_all
    · rw [if_neg hk]
      by_cases hkS : k ∈ S
      · have h : ¬ r k ≠ s k := fun h => hk (mem_filter.2 ⟨hkS, h⟩)
        exact (not_not.1 h).symm
      · exact ((mem_agree.1 hr) k (mem_compl.2 hkS)).symm
  unfold lt3PB
  refine mem_image.2 ⟨(R, j), mem_filter.2 ⟨mem_product.2 ⟨mem_powerset.2 (filter_subset _ _), hj⟩, ?_⟩, ?_⟩
  · intro hsub
    have hiR : i ∈ R := mem_filter.2 ⟨hiS, hri⟩
    exact hij (mem_singleton.1 (hsub hiR))
  · exact Prod.ext hflip rfl

/-- **The effect side for a light `s`** (Lemma EF in every direction, item (e)): own entries outside
`(1/2 - γ, 1/2 + γ)`, `s`'s private entries in the effect box. -/
theorem lt3_heff_light {w : Param N} (hw : w ∈ openCube N) (s : State N) {S : Finset (Fin N)} (hS : S.card = 3)
    {γ ρ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1 / 2) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 2 + γ)
    (hB : 7 * ρ ≤ 3 * Real.log 2 * (2 * γ * (1 / 2 + γ) ^ 2))
    (hown : ∀ j ∈ S, clamp01 (w s j) ∉ Set.Ioo (1 / 2 - γ) (1 / 2 + γ))
    (hbox : w ∈ lt3EBox s S w ρ) :
    ∃ te ∈ sysMaxEffStates (tpmOf (flipP s w)) S s s, ∀ θ : SysPartition N S,
      (1 / 2 + γ) ^ 3 * Real.logb 2 (1 / (1 - (1 / 2 + γ - ρ) / 2)) ≤
        sysPhiE (tpmOf (flipP s w)) S s θ s te := by
  classical
  have hc : ∀ r j, clamp01 (w r j) = w r j := fun r j => clamp01_of_mem ⟨(hw r j).1.le, (hw r j).2.le⟩
  refine tp_eff_dir hw s hS (fun j => decide (1 / 2 < clamp01 (w s j))) hγ0 hγ1 hρ0 hρ1 ?_ ?_ hB
  · intro j hj
    have h := hown j hj
    rw [hc] at h
    simp only [Set.mem_Ioo, not_and_or, not_lt] at h
    simp only [hc]
    by_cases hd : 1 / 2 < w s j
    · simp only [hd, decide_true, flipC, ↓reduceIte]
      rcases h with h | h <;> linarith
    · simp only [hd, decide_false, flipC, Bool.false_eq_true, ↓reduceIte]
      rcases h with h | h <;> linarith
  · intro r hr hrs j hj hi
    have hq := hbox (r, j) (lt3PB_mem_of_agree hr hj hi)
    simp only at hq
    unfold lt3ETgt at hq
    rw [hc, hc] at hq
    simp only [hc]
    by_cases hd : 1 / 2 < w s j
    · rw [if_pos hd] at hq
      simp only [hd, decide_true, flipC, ↓reduceIte]
      have := (abs_le.1 hq).2
      linarith
    · rw [if_neg hd] at hq
      simp only [hd, decide_false, flipC, Bool.false_eq_true, ↓reduceIte]
      have := (abs_le.1 hq).1
      linarith

/-! ### Resampling the windowed private positions -/

section RE

variable {s : State N} {ε γ : ℝ} {n : ℕ}

/-- Safe entries are not resampled. -/
lemma lt3W_replE_safe (w η : Param N) :
    ∀ q ∈ lt3WSafe s ε γ w, w q.1 q.2 = replE (stPriv (lt3WSel s ε γ n) lt3PB w) w η q.1 q.2 := by
  classical
  rintro ⟨q1, q2⟩ hq
  have hnA : (q1, q2) ∉ stPriv (lt3WSel s ε γ n) lt3PB w := fun hqA => by
    obtain ⟨k, hk', hq'⟩ := mem_biUnion.1 hqA
    exact lt3WPB_not_safe w k hk' _ hq' hq
  show w q1 q2 = (if (q1, q2) ∈ stPriv (lt3WSel s ε γ n) lt3PB w then η q1 q2 else w q1 q2)
  rw [if_neg hnA]

lemma lt3W_replE_sel (w η : Param N) :
    lt3WSel s ε γ n (replE (stPriv (lt3WSel s ε γ n) lt3PB w) w η) = lt3WSel s ε γ n w :=
  lt3WSel_stable (lt3W_replE_safe w η)

lemma lt3W_replE_priv (w η : Param N) :
    stPriv (lt3WSel s ε γ n) lt3PB (replE (stPriv (lt3WSel s ε γ n) lt3PB w) w η) =
      stPriv (lt3WSel s ε γ n) lt3PB w := by
  show (lt3WSel s ε γ n (replE (stPriv (lt3WSel s ε γ n) lt3PB w) w η)).biUnion lt3PB =
    (lt3WSel s ε γ n w).biUnion lt3PB
  rw [lt3W_replE_sel]

lemma lt3W_replE_row_s (w η : Param N) (j : Fin N) :
    replE (stPriv (lt3WSel s ε γ n) lt3PB w) w η s j = w s j :=
  (lt3W_replE_safe w η (s, j) (Or.inl (Or.inr (Or.inr rfl)))).symm

/-- Private entries are resampled. -/
lemma lt3W_replE_priv_mem (w η : Param N) {q : State N × Fin N} (hq : q ∈ stPriv (lt3WSel s ε γ n) lt3PB w) :
    replE (stPriv (lt3WSel s ε γ n) lt3PB w) w η q.1 q.2 = η q.1 q.2 := by
  show (if (q.1, q.2) ∈ stPriv (lt3WSel s ε γ n) lt3PB w then η q.1 q.2 else w q.1 q.2) = η q.1 q.2
  rw [if_pos hq]

end RE

lemma replE_replE (A : Finset (State N × Fin N)) (w η0 η : Param N) :
    replE A (replE A w η0) η = replE A w η := by
  funext r i
  simp only [replE]
  split_ifs <;> rfl

end Census
end IIT
