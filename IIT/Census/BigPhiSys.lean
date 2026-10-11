/-
Census of complexes: system-level bounds for an arbitrary candidate `S`.

A single-unit split `{j} | S \ {j}` has cut count `|S| - 1`, while every partition of `S` has cut
count at most `|S|(|S| - 1)`.  Hence the value of `φ_s` at any minimum information partition is at
most `|S|` times the value at the split (`sysPhi_le_card_mul`).  On the cause side the ratio at the
split is `Num_j(S, t) / Num_j({j}, t)` (`phi_le_cause`); on the effect side it is controlled by the
cut factor `qW`, which gives the bound through `Mrow` (`phi_le_eff`).
-/
import IIT.Census.BigPhiBridge

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-! ### Cut counts -/

/-- The single-unit split `{j} | S \ {j}` severs `|S| - 1` connections. -/
theorem sysCutCount_splitAt {S : Finset (Fin N)} {j : Fin N} (hj : j ∈ S)
    (hrest : (S.erase j).Nonempty) : sysCutCount (splitAt hj hrest) = S.card - 1 := by
  classical
  have hparts : (splitAt hj hrest).parts = {{j}, S.erase j} := rfl
  unfold sysCutCount
  rw [hparts, Finset.sum_pair (erase_ne_singleton hj hrest), splitAt_cut_j, splitAt_cut_rest,
    card_singleton, card_empty, card_erase_of_mem hj]
  simp

/-- A cut set lies inside `S` and avoids its own block. -/
lemma cutSet_subset_sdiff' {S : Finset (Fin N)} (θ : SysPartition N S)
    {p : Finset (Fin N)} (hp : p ∈ θ.parts) : θ.cutSet p ⊆ S \ p := by
  classical
  rw [SysPartition.cutSet]
  cases hd : θ.dir p with
  | inputs => exact subset_rfl
  | both => exact subset_rfl
  | outputs =>
      refine Finset.sup_le fun q hq => ?_
      obtain ⟨hqp, hqne, -⟩ := Finset.mem_filter.1 hq
      intro x hx
      refine Finset.mem_sdiff.2 ⟨θ.parts_subset q hqp hx, ?_⟩
      exact Finset.disjoint_left.1 (θ.parts_disjoint q hqp p hp hqne) hx

/-- The cut count of any partition of `S` is at most `|S|(|S| - 1)`. -/
theorem sysCutCount_le' {S : Finset (Fin N)} (θ : SysPartition N S) :
    sysCutCount θ ≤ S.card * (S.card - 1) := by
  classical
  have hterm : ∀ p ∈ θ.parts, p.card * (θ.cutSet p).card ≤ p.card * (S.card - 1) := by
    intro p hp
    refine Nat.mul_le_mul_left _ ?_
    have h1 : (θ.cutSet p).card ≤ (S \ p).card :=
      Finset.card_le_card (cutSet_subset_sdiff' θ hp)
    have h2 : (S \ p).card = S.card - p.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.2 (θ.parts_subset p hp)]
    have h3 : 0 < p.card := Finset.card_pos.2 (θ.parts_nonempty p hp)
    omega
  have hsum : ∑ p ∈ θ.parts, p.card ≤ S.card := by
    have hbi := Finset.card_biUnion (s := θ.parts) (t := fun p => p)
      (fun p hp q hq hpq => θ.parts_disjoint p hp q hq hpq)
    rw [← hbi]
    refine Finset.card_le_card fun x hx => ?_
    obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.1 hx
    exact θ.parts_subset p hp hxp
  calc sysCutCount θ = ∑ p ∈ θ.parts, p.card * (θ.cutSet p).card := rfl
    _ ≤ ∑ p ∈ θ.parts, p.card * (S.card - 1) := Finset.sum_le_sum hterm
    _ = (∑ p ∈ θ.parts, p.card) * (S.card - 1) := by rw [Finset.sum_mul]
    _ ≤ S.card * (S.card - 1) := Nat.mul_le_mul_right _ hsum

/-! ### The competitor bound -/

/-- **Competitor bound at the single-unit split.**  If the split `{j} | S \ {j}` has value at
most `B` at every cause--effect pair, then `φ_s(S) ≤ |S| · B`: every minimum information
partition has normalised value at most `B / (|S| - 1)` and cut count at most `|S|(|S| - 1)`. -/
theorem sysPhi_le_card_mul (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) {j : Fin N}
    (hj : j ∈ S) (hrest : (S.erase j).Nonempty) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ tc te, sysPhiAt T S u (splitAt hj hrest) s tc te ≤ B) :
    sysPhi T S u s ≤ S.card * B := by
  classical
  have hk : 2 ≤ S.card := by
    have h1 := card_erase_of_mem hj
    have h2 : 0 < (S.erase j).card := card_pos.2 hrest
    omega
  set θ₀ := splitAt hj hrest with hθ₀
  have hcc₀ : (sysCutCount θ₀ : ℝ) = (S.card : ℝ) - 1 := by
    rw [hθ₀, sysCutCount_splitAt hj hrest, Nat.cast_sub (by omega : 1 ≤ S.card)]
    simp
  have hk1 : (0 : ℝ) < (S.card : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hk
    linarith
  have hnn : (0 : ℝ) ≤ (S.card : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) hB0
  refine sup'OrZero_le hnn fun q _ => ?_
  refine sup'OrZero_le hnn fun θ hθ => ?_
  have hmin := (mem_argminSet.1 hθ) θ₀
  have hccθ : (0 : ℝ) < (sysCutCount θ : ℝ) := by exact_mod_cast sysCutCount_pos θ
  rw [normalizedSysPhiAt, normalizedSysPhiAt, hcc₀] at hmin
  have hstep : sysPhiAt T S u θ s q.1 q.2 / (sysCutCount θ : ℝ) ≤ B / ((S.card : ℝ) - 1) :=
    hmin.trans (by gcongr; exact hB q.1 q.2)
  rw [div_le_div_iff₀ hccθ hk1] at hstep
  have hccle : (sysCutCount θ : ℝ) ≤ (S.card : ℝ) * ((S.card : ℝ) - 1) := by
    have h := sysCutCount_le' θ
    have h' : ((sysCutCount θ : ℕ) : ℝ) ≤ ((S.card * (S.card - 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ S.card)] at h'
    simpa using h'
  have h2 : sysPhiAt T S u θ s q.1 q.2 * ((S.card : ℝ) - 1)
      ≤ (S.card * B) * ((S.card : ℝ) - 1) := by
    calc sysPhiAt T S u θ s q.1 q.2 * ((S.card : ℝ) - 1)
        ≤ B * (sysCutCount θ : ℝ) := hstep
      _ ≤ B * ((S.card : ℝ) * ((S.card : ℝ) - 1)) := by gcongr
      _ = (S.card * B) * ((S.card : ℝ) - 1) := by ring
  exact le_of_mul_le_mul_right h2 hk1

/-! ### Selectivity -/

/-- If all cause probabilities are within a factor `c` of each other, the backward cause
probability of any pattern is at most `c / 2^|S|`. -/
theorem sysBackCause_le_of_ratio (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) {c : ℝ}
    (hc : 0 < c) (hpos : ∀ t, 0 < sysCauseProb T S u s t)
    (h : ∀ t t', sysCauseProb T S u s t ≤ c * sysCauseProb T S u s t') (t : State N) :
    sysBackCause T S u s t ≤ c / 2 ^ S.card := by
  have hpt := hpos t
  have hunc : sysCauseProb T S u s t / c ≤ sysUncCause T S u s := by
    rw [sysUncCause, avgOverStates]
    have hsum : (2 : ℝ) ^ N * (sysCauseProb T S u s t / c)
        ≤ ∑ t' : State N, sysCauseProb T S u s t' := by
      have : ∀ t' ∈ (univ : Finset (State N)), sysCauseProb T S u s t / c
          ≤ sysCauseProb T S u s t' := fun t' _ => by
        rw [div_le_iff₀ hc, mul_comm]; exact h t t'
      have hs := Finset.card_nsmul_le_sum univ _ _ this
      rw [card_state, nsmul_eq_mul] at hs
      push_cast at hs
      exact hs
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hk : (0 : ℝ) < 2 ^ S.card := by positivity
  have hq : 0 < sysCauseProb T S u s t / c := div_pos hpt hc
  rw [sysBackCause, div_le_div_iff₀ (mul_pos hk (hq.trans_le hunc)) hk]
  have : sysCauseProb T S u s t ≤ c * sysUncCause T S u s := by
    rw [div_le_iff₀ hc] at hunc; linarith
  nlinarith

/-! ### The cause side at the split -/

lemma hrest_of_card {S : Finset (Fin N)} {j : Fin N} (hS : 2 ≤ S.card) (hj : j ∈ S) :
    (S.erase j).Nonempty := by
  rw [← card_pos, card_erase_of_mem hj]; omega

/-- On the open cube, the cause ratio at the split `{j} | S \ {j}` is the ratio of the two
numerators of unit `j`. -/
lemma cause_ratio_splitAt {z : Param N} (hz : z ∈ openCube N) (s t : State N)
    {S : Finset (Fin N)} {j : Fin N} (hj : j ∈ S) (hrest : (S.erase j).Nonempty) :
    sysCauseProb (tpmOf z) S s s t / sysPartCauseProb (tpmOf z) S s (splitAt hj hrest) s t
      = Num (flipP s z) S S t j / Num (flipP s z) S {j} t j := by
  rw [sysCauseProb_eq_Num, sysPartCauseProb_splitAt_eq z s t hj hrest,
    ← Finset.mul_prod_erase S _ hj]
  have hZ := Zs_pos hz s
  have hP : 0 < ∏ i ∈ S.erase j, Num (flipP s z) S S t i / Zs (flipP s z) :=
    prod_pos fun i _ => div_pos (Num_pos hz s S S t i) hZ
  have h1 := Num_pos hz s S {j} t j
  rw [mul_div_mul_right _ _ hP.ne']
  field_simp

/-- **Cause-side bound (Lemma U, cause form).**  `φ_s(S) ≤ |S| · B` when the cause
integration at the split `{j} | S \ {j}` is at most `B` for every pattern. -/
theorem phi_le_cause {z : Param N} (hz : z ∈ openCube N) {s : State N} {S : Finset (Fin N)}
    (hS : 2 ≤ S.card) {j : Fin N} (hj : j ∈ S) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ tc, sysBackCause (tpmOf z) S s s tc *
        pos (Real.logb 2 (Num (flipP s z) S S tc j / Num (flipP s z) S {j} tc j)) ≤ B) :
    phi z s S ≤ S.card * B := by
  have hrest := hrest_of_card hS hj
  refine sysPhi_le_card_mul (tpmOf z) S s s hj hrest hB0 fun tc te => ?_
  refine (min_le_left _ _).trans ?_
  rw [sysPhiC, cause_ratio_splitAt hz s tc hj hrest]
  exact hB tc

/-! ### The effect side at the split -/

lemma logb_two_le_two_of_le_four {x : ℝ} (h0 : 0 ≤ x) (h4 : x ≤ 4) : Real.logb 2 x ≤ 2 := by
  rcases h0.eq_or_lt with h | h
  · rw [← h, Real.logb_zero]; norm_num
  · calc Real.logb 2 x ≤ Real.logb 2 4 := Real.logb_le_logb_of_le (by norm_num) h h4
      _ = 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow]
        simp

/-- The effect integration at the split is at most twice the intact effect probability when the
cut factor of unit `j` is at least `1/4` for both bits. -/
lemma sysPhiE_splitAt_le {z : Param N} {s : State N} {S : Finset (Fin N)} {j : Fin N}
    (hj : j ∈ S) (hrest : (S.erase j).Nonempty) (hq : ∀ b, 1 / 4 ≤ qW (flipP s z) s S j b)
    (te : State N) :
    sysPhiE (tpmOf z) S s (splitAt hj hrest) s te ≤ sysEffProb (tpmOf z) S s s te * 2 := by
  rw [sysPhiE]
  refine mul_le_mul_of_nonneg_left ?_ (sysEffProb_nonneg _ _ _ _ _)
  refine pos_le (by norm_num) ?_
  set R := ∏ i ∈ S.erase j, (tpmOf z).prob i s (te i) with hR
  have heff : sysEffProb (tpmOf z) S s s te = (tpmOf z).prob j s (te j) * R := by
    rw [sysEffProb, merge_same_bg, ← Finset.mul_prod_erase S _ hj]
  have hpart : sysPartEffProb (tpmOf z) S s (splitAt hj hrest) s te
      = qW (flipP s z) s S j (te j) * R := by
    rw [sysPartEffProb, merge_same_bg, ← Finset.mul_prod_erase S _ hj, splitAt_partOf_j,
      splitAt_cut_j, effUnit_splitAt_eq_qW z s hj]
    congr 1
    refine prod_congr rfl fun i hi => ?_
    rw [splitAt_partOf_rest hj hrest hi, splitAt_cut_rest, compl_empty, effUnit_univ_prob]
  rw [heff, hpart]
  have hR0 : 0 ≤ R := prod_nonneg fun i _ => (tpmOf z).nonneg i s (te i)
  have hq0 : (0 : ℝ) < qW (flipP s z) s S j (te j) := lt_of_lt_of_le (by norm_num) (hq (te j))
  have ha0 := (tpmOf z).nonneg j s (te j)
  have ha1 := (tpmOf z).le_one j s (te j)
  rcases hR0.eq_or_lt with h | h
  · rw [← h, mul_zero, mul_zero, div_zero, Real.logb_zero]; norm_num
  · rw [mul_div_mul_right _ _ h.ne']
    refine logb_two_le_two_of_le_four (div_nonneg ha0 hq0.le) ?_
    rw [div_le_iff₀ hq0]
    linarith [hq (te j)]

/-- **Effect-side bound (Lemma U, effect form).**  If the cut factor of unit `j` at the split is
at least `1/4` for both bits, then `φ_s(S) ≤ |S| · 2^(N - |S|) · Mrow · 2`. -/
theorem phi_le_eff {z : Param N} (hz : z ∈ openCube N) {s : State N} {S : Finset (Fin N)}
    (hS : 2 ≤ S.card) {j : Fin N} (hj : j ∈ S) (hq : ∀ b, 1 / 4 ≤ qW (flipP s z) s S j b) :
    phi z s S ≤ S.card * ((2 : ℝ) ^ (N - S.card) * Mrow (flipP s z) s) * 2 := by
  have hrest := hrest_of_card hS hj
  have hM0 : 0 ≤ (2 : ℝ) ^ (N - S.card) * Mrow (flipP s z) s :=
    (sysEffProb_nonneg (tpmOf z) S s s s).trans (sysEffProb_le_Mrow z s s S)
  rw [mul_assoc]
  refine sysPhi_le_card_mul (tpmOf z) S s s hj hrest (by positivity) fun tc te => ?_
  refine (min_le_right _ _).trans ((sysPhiE_splitAt_le hj hrest hq te).trans ?_)
  gcongr
  exact sysEffProb_le_Mrow z s te S

end Census
end IIT
