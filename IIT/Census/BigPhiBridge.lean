/-
Census of complexes: from the repertoires of `tpmOf z` to the statistics of `BigPhiStats`.

With `w = flipP s z` the probability that row `r` produces the current bit of unit `j` is
`clamp01 (w r j)`.  Every conditioned cause factor of a candidate `S` with purview part `Y ⊆ S`
(mechanism level, `causeFwdAt`/`partCauseFwdAt`, and system level, `sysCauseProb` and the split
`sysPartCauseProb`) equals `Num w S Y t i / Zs w`.  On the effect side, the cut factor of the
split at `j` is `qW`, and the intact effect probability is bounded by `Mrow`.
-/
import IIT.Cond
import IIT.MinDep
import IIT.Census.PairBridge
import IIT.Census.BigPhiStats

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-! ### Flipped coordinates -/

lemma clamp01_one_sub (x : ℝ) : clamp01 (1 - x) = 1 - clamp01 x := by
  unfold clamp01
  rcases le_total x 0 with h | h
  · rw [min_eq_left (by linarith : (1 : ℝ) ≤ 1 - x), max_eq_right zero_le_one,
      min_eq_right (by linarith : x ≤ 1), max_eq_left h]
    ring
  · rcases le_total x 1 with h' | h'
    · rw [min_eq_right (by linarith : 1 - x ≤ 1), max_eq_right (by linarith : (0 : ℝ) ≤ 1 - x),
        min_eq_right h', max_eq_right h]
    · rw [min_eq_right (by linarith : 1 - x ≤ 1), max_eq_left (by linarith : 1 - x ≤ (0 : ℝ)),
        min_eq_left h', max_eq_right zero_le_one]
      ring

/-- The probability of the current bit is the clamped flipped parameter. -/
lemma y_eq_clamp (z : Param N) (s r : State N) (j : Fin N) :
    y z s r j = clamp01 (flipP s z r j) := by
  unfold y tpmOf flipP flipC
  cases s j <;> simp [clamp01_one_sub]

lemma prob_eq_clamp (z : Param N) (s r : State N) (j : Fin N) :
    (tpmOf z).prob j r (s j) = clamp01 (flipP s z r j) :=
  y_eq_clamp z s r j

/-- The row product is `Pw` of the flipped parameters. -/
lemma rowProd_eq_Pw (z : Param N) (s r : State N) : rowProd z s r = Pw (flipP s z) r := by
  unfold rowProd Pw
  exact prod_congr rfl fun j _ => y_eq_clamp z s r j

/-- The Bayes normaliser is `Zs` of the flipped parameters. -/
lemma sum_fullProb_eq_Zs (z : Param N) (s : State N) :
    ∑ v : State N, fullProb (tpmOf z) v s = Zs (flipP s z) := by
  unfold Zs
  exact sum_congr rfl fun v _ => rowProd_eq_Pw z s v

/-! ### Block sums -/

lemma sum_mul_blockW_gen (z : Param N) (s t : State N) (S : Finset (Fin N))
    (g : State N → ℝ) :
    ∑ w : State N, g (merge S t w) * blockW z s S w =
      2 ^ S.card * ∑ v : State N, g (merge S t v) * rowProd z s v := by
  unfold blockW
  have h1 : ∀ w : State N, g (merge S t w) * ∑ v ∈ agree Sᶜ w, rowProd z s v =
      ∑ v : State N, if w ∈ agree Sᶜ v then g (merge S t v) * rowProd z s v else 0 := by
    intro w
    rw [Finset.mul_sum, ← Finset.sum_filter]
    have hset : agree Sᶜ w = univ.filter (fun v => w ∈ agree Sᶜ v) := by
      ext v; simp only [mem_agree, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h j hj => (h j hj).symm, fun h j hj => (h j hj).symm⟩
    rw [← hset]
    refine Finset.sum_congr rfl fun v hv => ?_
    have : merge S t w = merge S t v := by
      funext j
      by_cases hj : j ∈ S
      · simp [merge, hj]
      · simp [merge, hj, (mem_agree.mp hv) j (Finset.mem_compl.mpr hj)]
    rw [this]
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have : univ.filter (fun w => w ∈ agree Sᶜ v) = agree Sᶜ v := by ext; simp
  rw [this, card_agree, Finset.card_compl, Fintype.card_fin,
    Nat.sub_sub_self ((Finset.card_le_univ S).trans_eq (Fintype.card_fin N))]
  push_cast; ring

/-- The conditioned single-unit effect probability is the block mean `meanW`. -/
lemma effUnit_cond_eq_meanW (z : Param N) (s : State N) {S Y : Finset (Fin N)} (hY : Y ⊆ S)
    (t v : State N) (i : Fin N) :
    effUnit (tpmOf z) (condSet S Y) (merge S t v) i (s i) = meanW (flipP s z) S Y t i v := by
  have hc := card_agree_cond hY v t
  simp only [condState] at hc
  rw [effUnit, hc, meanW]
  push_cast
  congr 1
  exact sum_congr rfl fun r _ => prob_eq_clamp z s r i

/-- **The conditioned cause factor.**  For a purview part `Y ⊆ S`, the cause factor of unit `i`
with the background marginalised against the Bayes posterior is `Num / Zs`. -/
theorem condFactor_eq (z : Param N) (s : State N) {S Y : Finset (Fin N)} (hY : Y ⊆ S)
    (t : State N) (i : Fin N) :
    (∑ w : State N, effUnit (tpmOf z) (condSet S Y) (condState S w t) i (s i)
        * bgWeight (tpmOf z) S s w) / (2 : ℝ) ^ S.card =
      Num (flipP s z) S Y t i / Zs (flipP s z) := by
  rw [sum_mul_bgWeight]
  have h2 := sum_mul_blockW_gen z s t S (fun x => effUnit (tpmOf z) (condSet S Y) x i (s i))
  rw [show (∑ w : State N, effUnit (tpmOf z) (condSet S Y) (condState S w t) i (s i)
      * blockW z s S w) = ∑ w : State N, effUnit (tpmOf z) (condSet S Y) (merge S t w) i (s i)
      * blockW z s S w from rfl, h2, sum_fullProb_eq_Zs]
  have h3 : ∀ v : State N, effUnit (tpmOf z) (condSet S Y) (merge S t v) i (s i) * rowProd z s v
      = meanW (flipP s z) S Y t i v * Pw (flipP s z) v := fun v => by
    rw [effUnit_cond_eq_meanW z s hY, rowProd_eq_Pw]
  rw [sum_congr rfl fun v _ => h3 v, ← Num]
  have h : (2 : ℝ) ^ S.card ≠ 0 := by positivity
  rw [div_div, mul_comm (Zs _), ← div_div, mul_div_cancel_left₀ _ h]

/-! ### Mechanism level -/

/-- The conditioned forward cause term of a mechanism at the current state, in the
statistics. -/
theorem causeFwdAt_eq (z : Param N) (s : State N) {S Z : Finset (Fin N)} (hZ : Z ⊆ S)
    (zz : State N) (M : Finset (Fin N)) :
    causeFwdAt (tpmOf z) S s Z zz M s = ∏ i ∈ M, Num (flipP s z) S Z zz i / Zs (flipP s z) := by
  unfold causeFwdAt
  exact prod_congr rfl fun i _ => condFactor_eq z s hZ zz i

/-- The partitioned conditioned cause term: unit `i` sees its purview part `θ.causePart i`. -/
theorem partCauseFwdAt_eq (z : Param N) (s : State N) {S Z M : Finset (Fin N)}
    (zz : State N) (θ : Partition N M Z) (hZ : Z ⊆ S) :
    partCauseFwdAt (tpmOf z) S s Z zz M s θ =
      ∏ i ∈ M, Num (flipP s z) S (θ.causePart i) zz i / Zs (flipP s z) := by
  unfold partCauseFwdAt
  exact prod_congr rfl fun i _ => condFactor_eq z s ((θ.causePart_subset i).trans hZ) zz i

/-! ### System level -/

/-- The system cause probability of pattern `t` in the statistics. -/
theorem sysCauseProb_eq_Num (z : Param N) (s t : State N) (S : Finset (Fin N)) :
    sysCauseProb (tpmOf z) S s s t = ∏ i ∈ S, Num (flipP s z) S S t i / Zs (flipP s z) := by
  unfold sysCauseProb
  refine prod_congr rfl fun i _ => ?_
  rw [← condFactor_eq z s (subset_refl S) t i]
  simp only [condSet, condState, union_compl, effUnit_univ_prob]

lemma compl_erase_eq_condSet {S : Finset (Fin N)} {j : Fin N} (hj : j ∈ S) :
    (S.erase j)ᶜ = condSet S {j} := by
  ext x
  unfold condSet
  by_cases h : x = j
  · subst h; simp
  · simp [h]

/-- The partitioned system cause probability at the split `{j} | S \ {j}`: unit `j` is
conditioned on its own bit only, every other unit is uncut. -/
theorem sysPartCauseProb_splitAt_eq (z : Param N) (s t : State N) {S : Finset (Fin N)}
    {j : Fin N} (hj : j ∈ S) (hrest : (S.erase j).Nonempty) :
    sysPartCauseProb (tpmOf z) S s (splitAt hj hrest) s t =
      (Num (flipP s z) S {j} t j / Zs (flipP s z)) *
        ∏ i ∈ S.erase j, Num (flipP s z) S S t i / Zs (flipP s z) := by
  have hj1 : (∑ w : State N, effUnit (tpmOf z) ((splitAt hj hrest).cutSet
      ((splitAt hj hrest).partOf j))ᶜ (merge S t w) j (s j) * bgWeight (tpmOf z) S s w)
        / (2 : ℝ) ^ S.card = Num (flipP s z) S {j} t j / Zs (flipP s z) := by
    rw [splitAt_partOf_j, splitAt_cut_j, compl_erase_eq_condSet hj,
      ← condFactor_eq z s (singleton_subset_iff.2 hj) t j]
    rfl
  have hi1 : ∀ i ∈ S.erase j, (∑ w : State N, effUnit (tpmOf z) ((splitAt hj hrest).cutSet
      ((splitAt hj hrest).partOf i))ᶜ (merge S t w) i (s i) * bgWeight (tpmOf z) S s w)
        / (2 : ℝ) ^ S.card = Num (flipP s z) S S t i / Zs (flipP s z) := by
    intro i hi
    rw [splitAt_partOf_rest hj hrest hi, splitAt_cut_rest, compl_empty,
      ← condFactor_eq z s (subset_refl S) t i]
    simp only [condSet, condState, union_compl]
  unfold sysPartCauseProb
  rw [← Finset.mul_prod_erase S _ hj, hj1, prod_congr rfl hi1]

/-- The cut effect factor of unit `j` at the split is the statistic `qW`. -/
theorem effUnit_splitAt_eq_qW (z : Param N) (s : State N) {S : Finset (Fin N)} {j : Fin N}
    (hj : j ∈ S) (b : Bool) :
    effUnit (tpmOf z) (S.erase j)ᶜ s j b = qW (flipP s z) s S j b := by
  have hle : S.card - 1 ≤ N :=
    (Nat.sub_le _ _).trans ((Finset.card_le_univ S).trans_eq (Fintype.card_fin N))
  rw [effUnit, card_agree, qW, card_compl, Fintype.card_fin, card_erase_of_mem hj,
    Nat.sub_sub_self hle]
  push_cast
  congr 1
  refine sum_congr rfl fun r _ => ?_
  simp only [tpmOf, flipP, flipC]
  cases b <;> cases s j <;> simp [clamp01_one_sub]

lemma merge_same_bg (S : Finset (Fin N)) (s : State N) : merge S s s = s := by
  funext j
  by_cases h : j ∈ S <;> simp [merge, h]

/-- The intact effect probability of any next pattern is at most `2^(N - |S|) · Mrow`. -/
theorem sysEffProb_le_Mrow (z : Param N) (s te : State N) (S : Finset (Fin N)) :
    sysEffProb (tpmOf z) S s s te ≤ (2 : ℝ) ^ (N - S.card) * Mrow (flipP s z) s := by
  set m : Fin N → ℝ := fun i => max (clamp01 (flipP s z s i)) (1 - clamp01 (flipP s z s i))
    with hm
  have hm_eq : ∀ i, m i = max (clamp01 (z s i)) (1 - clamp01 (z s i)) := by
    intro i
    simp only [hm, flipP, flipC]
    cases s i <;> simp [clamp01_one_sub, max_comm]
  have hhalf : ∀ i, (1 / 2 : ℝ) ≤ m i := by
    intro i
    rw [hm_eq]
    by_cases h : clamp01 (z s i) ≤ 1 / 2
    · exact le_max_of_le_right (by linarith)
    · exact le_max_of_le_left (by linarith)
  have hprob : ∀ i, (tpmOf z).prob i s (te i) ≤ m i := by
    intro i
    rw [hm_eq]
    cases te i
    · simp only [tpmOf, Bool.false_eq_true, ↓reduceIte]; exact le_max_right _ _
    · simp only [tpmOf, ↓reduceIte]; exact le_max_left _ _
  have hS : sysEffProb (tpmOf z) S s s te ≤ ∏ i ∈ S, m i := by
    rw [sysEffProb, merge_same_bg]
    exact prod_le_prod (fun i _ => (tpmOf z).nonneg i s (te i)) fun i _ => hprob i
  have hc : (1 / 2 : ℝ) ^ (N - S.card) ≤ ∏ i ∈ Sᶜ, m i := by
    have := prod_le_prod (s := Sᶜ) (f := fun _ => (1 / 2 : ℝ)) (g := m)
      (fun _ _ => by norm_num) fun i _ => hhalf i
    rwa [prod_const, card_compl, Fintype.card_fin] at this
  have hMrow : Mrow (flipP s z) s = (∏ i ∈ S, m i) * ∏ i ∈ Sᶜ, m i :=
    (prod_mul_prod_compl S m).symm
  have h0 : 0 ≤ ∏ i ∈ S, m i := prod_nonneg fun i _ => le_trans (by norm_num) (hhalf i)
  rw [hMrow]
  calc sysEffProb (tpmOf z) S s s te ≤ ∏ i ∈ S, m i := hS
    _ = (∏ i ∈ S, m i) * ((2 : ℝ) ^ (N - S.card) * (1 / 2 : ℝ) ^ (N - S.card)) := by
        rw [← mul_pow]; norm_num
    _ ≤ (∏ i ∈ S, m i) * ((2 : ℝ) ^ (N - S.card) * ∏ i ∈ Sᶜ, m i) := by gcongr
    _ = (2 : ℝ) ^ (N - S.card) * ((∏ i ∈ S, m i) * ∏ i ∈ Sᶜ, m i) := by ring

/-! ### Positivity on the open cube -/

lemma Zs_pos {z : Param N} (hz : z ∈ openCube N) (s : State N) : 0 < Zs (flipP s z) := by
  rw [← sum_fullProb_eq_Zs]; exact sum_fullProb_pos hz s

lemma meanW_pos {z : Param N} (hz : z ∈ openCube N) (s : State N) (S Y : Finset (Fin N))
    (t : State N) (i : Fin N) (v : State N) : 0 < meanW (flipP s z) S Y t i v := by
  unfold meanW
  refine div_pos (sum_pos (fun r _ => ?_) (agree_nonempty _ _)) (by positivity)
  rw [← y_eq_clamp]; exact y_pos hz s r i

lemma Pw_pos {z : Param N} (hz : z ∈ openCube N) (s r : State N) : 0 < Pw (flipP s z) r := by
  rw [← rowProd_eq_Pw]; exact rowProd_pos hz s r

lemma Num_pos {z : Param N} (hz : z ∈ openCube N) (s : State N) (S Y : Finset (Fin N))
    (t : State N) (i : Fin N) : 0 < Num (flipP s z) S Y t i :=
  sum_pos (fun v _ => mul_pos (meanW_pos hz s S Y t i v) (Pw_pos hz s v)) univ_nonempty

end Census
end IIT
