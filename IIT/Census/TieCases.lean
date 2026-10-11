/-
Tie theorem, part 3: the pair dichotomy (L6) and its ingredients -- the fully flipped effect
limit (L4), every partition cuts someone (L5, via `exists_cutSet_nonempty`), the explicit
point `y*` (C5) and the witness row (C5').
-/
import IIT.Census.TieBranches

namespace IIT
namespace Census

open Finset Filter Topology

variable {N : ℕ}

lemma tie_merge_self (S : Finset (Fin N)) (s : State N) : merge S s s = s := by
  funext j; simp [merge]

/-! ### Scaling one column by `1/2` -/

/-- `1/2` on unit `k`, `1` elsewhere. -/
noncomputable def halfAt (k : Fin N) : Fin N → ℝ := fun j => if j = k then 1 / 2 else 1

lemma halfAt_mem (k j : Fin N) : 0 < halfAt k j ∧ halfAt k j ≤ 1 := by
  unfold halfAt; split_ifs <;> norm_num

lemma halfAt_ne (k j : Fin N) : halfAt k j ≠ 0 := (halfAt_mem k j).1.ne'

lemma halfAt_of_ne {k j : Fin N} (h : j ≠ k) : halfAt k j = 1 := by simp [halfAt, h]

lemma prod_halfAt_of_notMem {k : Fin N} {S : Finset (Fin N)} (hk : k ∉ S) :
    ∏ j ∈ S, halfAt k j = 1 :=
  prod_eq_one fun _ hj => halfAt_of_ne fun h => hk (h ▸ hj)

lemma prod_halfAt_of_mem {k : Fin N} {S : Finset (Fin N)} (hk : k ∈ S) :
    ∏ j ∈ S, halfAt k j = 1 / 2 := by
  unfold halfAt; rw [prod_ite_eq']; simp [hk]

/-! ### E–E -/

/-- **E–E.** If `k ∈ S' \ S` and the two effect branches agree on the open cube, the first one
vanishes there (it is invariant under halving column `k`, the second one halves). -/
lemma EE {s : State N} {S S' : Finset (Fin N)} {k : Fin N} (hk : k ∈ S') (hkS : k ∉ S)
    (θ : SysPartition N S) (θ' : SysPartition N S') (t t' : State N)
    (heq : ∀ z ∈ openCube N, BE (tpmOf z) s S θ t = BE (tpmOf z) s S' θ' t') :
    ∀ z ∈ openCube N, BE (tpmOf z) s S θ t = 0 := by
  intro z hz
  have hbs := scaleParam_bitScale hz t' (halfAt_mem k)
  have hz' := scaleParam_mem hz t' (halfAt_mem k)
  have h1 := BE_scale hbs s θ t (fun j hj => Or.inl (halfAt_of_ne fun h => hkS (h ▸ hj)))
    (by rw [prod_halfAt_of_notMem hkS]; norm_num)
  have h2 := BE_scale hbs s θ' t' (fun j _ => Or.inr rfl)
    (by rw [prod_halfAt_of_mem hk]; norm_num)
  rw [prod_halfAt_of_notMem hkS] at h1
  rw [prod_halfAt_of_mem hk] at h2
  have := heq _ hz'
  have := heq z hz
  linarith

/-! ### E–C, some unit of the effect state is at its current value -/

lemma EC_single {s : State N} {S S'' : Finset (Fin N)} {k : Fin N} (hk : k ∈ S'')
    (htk : t'' k = s k) (θ : SysPartition N S) (θ'' : SysPartition N S'') (t : State N)
    (heq : ∀ z ∈ openCube N, BE (tpmOf z) s S'' θ'' t'' = BC (tpmOf z) s S θ t) :
    ∀ z ∈ openCube N, BE (tpmOf z) s S'' θ'' t'' = 0 := by
  intro z hz
  have hbs := scaleParam_bitScale hz s (halfAt_mem k)
  have hz' := scaleParam_mem hz s (halfAt_mem k)
  have hS : ∀ j ∈ S'', halfAt k j = 1 ∨ s j = t'' j := by
    intro j _
    by_cases hj : j = k
    · right; rw [hj, htk]
    · left; exact halfAt_of_ne hj
  have h1 := BE_scale hbs s θ'' t'' hS (by rw [prod_halfAt_of_mem hk]; norm_num)
  rw [prod_halfAt_of_mem hk] at h1
  have h2 := BC_scale hbs (halfAt_ne k) S θ t
  have := heq _ hz'
  have := heq z hz
  linarith

/-! ### L4: the fully flipped effect state -/

/-- `sysEffProb` after scaling every current-state column by `l`, for a fully flipped state. -/
noncomputable def flipEff (T : UnitTPM N) (s : State N) (S : Finset (Fin N)) (l : ℝ) : ℝ :=
  ∏ j ∈ S, (1 - l * T.prob j s (s j))

/-- `sysPartEffProb` after the same scaling. -/
noncomputable def flipPartEff (T : UnitTPM N) (s : State N) (S : Finset (Fin N))
    (θ : SysPartition N S) (l : ℝ) : ℝ :=
  ∏ j ∈ S, (∑ r ∈ agree (θ.cutSet (θ.partOf j))ᶜ s, (1 - l * T.prob j r (s j))) /
    ((agree (θ.cutSet (θ.partOf j))ᶜ s).card : ℝ)

lemma BE_flip {T T' : UnitTPM N} {s : State N} {l : ℝ} (h : BitScale T T' s fun _ => l)
    {S : Finset (Fin N)} (θ : SysPartition N S) {t : State N} (ht : ∀ j ∈ S, t j ≠ s j) :
    BE T' s S θ t = flipEff T s S l * Real.logb 2 (flipEff T s S l / flipPartEff T s S θ l) := by
  have key : ∀ j ∈ S, ∀ r, T'.prob j r (t j) = 1 - l * T.prob j r (s j) := by
    intro j hj r
    have h1 := T'.normalized j r
    have h2 := h j r
    have htj : t j = !s j := by
      have := ht j hj
      revert this; cases t j <;> cases s j <;> decide
    rw [htj]
    cases hs : s j <;> rw [hs] at h2 <;> simp only [Bool.not_false, Bool.not_true] <;> linarith
  have he : sysEffProb T' S s s t = flipEff T s S l := by
    unfold sysEffProb flipEff
    rw [tie_merge_self]
    exact prod_congr rfl fun j hj => key j hj s
  have hp : sysPartEffProb T' S s θ s t = flipPartEff T s S θ l := by
    unfold sysPartEffProb flipPartEff effUnit
    rw [tie_merge_self]
    exact prod_congr rfl fun j hj => by rw [sum_congr rfl fun r _ => key j hj r]
  unfold BE
  rw [he, hp]

lemma flipEff_zero (T : UnitTPM N) (s : State N) (S : Finset (Fin N)) : flipEff T s S 0 = 1 := by
  simp [flipEff]

lemma flipPartEff_zero (T : UnitTPM N) (s : State N) (S : Finset (Fin N)) (θ : SysPartition N S) :
    flipPartEff T s S θ 0 = 1 := by
  unfold flipPartEff
  refine prod_eq_one fun j _ => ?_
  simp only [zero_mul, sub_zero, sum_const, nsmul_eq_mul, mul_one]
  exact div_self (Nat.cast_ne_zero.2 (card_agree_pos _ _).ne')

lemma flip_continuousAt (T : UnitTPM N) (s : State N) (S : Finset (Fin N))
    (θ : SysPartition N S) :
    ContinuousAt (fun l => flipEff T s S l * Real.logb 2 (flipEff T s S l / flipPartEff T s S θ l)) 0 := by
  have hE : Continuous fun l => flipEff T s S l := by unfold flipEff; fun_prop
  have hP : Continuous fun l => flipPartEff T s S θ l := by unfold flipPartEff; fun_prop
  unfold Real.logb
  refine hE.continuousAt.mul (ContinuousAt.div_const (ContinuousAt.log
    (hE.continuousAt.div hP.continuousAt (by rw [flipPartEff_zero]; norm_num)) ?_) _)
  show flipEff T s S 0 / flipPartEff T s S θ 0 ≠ 0
  rw [flipEff_zero, flipPartEff_zero]; norm_num

/-- **E–C, fully flipped.** Scaling every current-state column by `l ∈ (0,1)` fixes the cause
branch, so the effect branch is constant in `l`; its limit at `l = 0` is `1 · log 1 = 0`. -/
lemma EC_flip {s : State N} {S S'' : Finset (Fin N)} {t'' : State N}
    (ht : ∀ j ∈ S'', t'' j ≠ s j) (θ : SysPartition N S) (θ'' : SysPartition N S'')
    (t : State N)
    (heq : ∀ z ∈ openCube N, BE (tpmOf z) s S'' θ'' t'' = BC (tpmOf z) s S θ t) :
    ∀ z ∈ openCube N, BE (tpmOf z) s S'' θ'' t'' = 0 := by
  intro z hz
  set G := fun l => flipEff (tpmOf z) s S'' l *
    Real.logb 2 (flipEff (tpmOf z) s S'' l / flipPartEff (tpmOf z) s S'' θ'' l) with hG
  have hconst : ∀ l ∈ Set.Ioo (0 : ℝ) 1, BE (tpmOf z) s S'' θ'' t'' = G l := by
    intro l hl
    have hc : ∀ j : Fin N, 0 < (fun _ => l) j ∧ (fun _ => l) j ≤ 1 := fun _ => ⟨hl.1, hl.2.le⟩
    have hbs := scaleParam_bitScale hz s hc
    have hz' := scaleParam_mem hz s hc
    simp only [hG]
    rw [← BE_flip hbs θ'' ht, heq _ hz', BC_scale hbs (fun _ => hl.1.ne'), ← heq z hz]
  have hG0 : G 0 = 0 := by simp only [hG, flipEff_zero, flipPartEff_zero]; norm_num
  have h1 : Tendsto G (𝓝[>] 0) (𝓝 (G 0)) :=
    (flip_continuousAt (tpmOf z) s S'' θ'').tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto G (𝓝[>] 0) (𝓝 (BE (tpmOf z) s S'' θ'' t'')) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with l hl using hconst l hl
  rw [← hG0]
  exact tendsto_nhds_unique h2 h1

/-- **E–C.** An effect branch that agrees with a cause branch on the open cube vanishes. -/
lemma EC {s : State N} {S S'' : Finset (Fin N)} {t'' : State N} (θ : SysPartition N S)
    (θ'' : SysPartition N S'') (t : State N)
    (heq : ∀ z ∈ openCube N, BE (tpmOf z) s S'' θ'' t'' = BC (tpmOf z) s S θ t) :
    ∀ z ∈ openCube N, BE (tpmOf z) s S'' θ'' t'' = 0 := by
  by_cases h : ∃ k ∈ S'', t'' k = s k
  · obtain ⟨k, hk, htk⟩ := h
    exact EC_single hk htk θ θ'' t heq
  · push Not at h
    exact EC_flip h θ θ'' t heq

/-! ### C5: the explicit point `y*` -/

/-- `y*`: every `y` equals `1/2` except `y_{r0,i} = 3/4`. -/
noncomputable def zstar (s r0 : State N) (i : Fin N) : Param N :=
  fun v j => if j = i ∧ v = r0 then (if s i then 3 / 4 else 1 / 4) else 1 / 2

lemma zstar_mem (s r0 : State N) (i : Fin N) : zstar s r0 i ∈ openCube N := by
  intro v j
  simp only [zstar, Set.mem_Ioo]
  split_ifs <;> norm_num

lemma zstar_prob (s r0 : State N) (i j : Fin N) (v : State N) :
    (tpmOf (zstar s r0 i)).prob j v (s j) = 1 / 2 + if j = i ∧ v = r0 then 1 / 4 else 0 := by
  show (if s j then clamp01 (zstar s r0 i v j) else 1 - clamp01 (zstar s r0 i v j)) = _
  rw [clamp01_eq (Set.Ioo_subset_Icc_self (zstar_mem s r0 i v j))]
  unfold zstar
  by_cases h : j = i ∧ v = r0
  · rw [_root_.if_pos h, _root_.if_pos h, h.1]
    cases s i <;> norm_num
  · rw [_root_.if_neg h, _root_.if_neg h]
    cases s j <;> norm_num

lemma effUnit_zstar (s r0 : State N) (i j : Fin N) (M : Finset (Fin N)) (m : State N) :
    effUnit (tpmOf (zstar s r0 i)) M m j (s j) =
      1 / 2 + (if j = i ∧ r0 ∈ agree M m then 1 / 4 else 0) / ((agree M m).card : ℝ) := by
  have hc : ((agree M m).card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (card_agree_pos M m).ne'
  unfold effUnit
  simp only [zstar_prob]
  rw [sum_add_distrib, sum_const, nsmul_eq_mul]
  by_cases hj : j = i
  · simp only [hj, true_and]
    rw [sum_ite_eq']
    field_simp
  · simp only [hj, false_and, if_false, sum_const_zero]
    field_simp

lemma merge_eq_of_mem_agree {S X : Finset (Fin N)} (hX : X ⊆ S) {t w r0 : State N}
    (hr : ∀ j ∈ S, r0 j = t j) (h : r0 ∈ agree Xᶜ (merge S t w)) : merge S t w = r0 := by
  funext k
  by_cases hk : k ∈ S
  · rw [merge_mem hk, hr k hk]
  · exact ((mem_agree.1 h) k (mem_compl.2 fun hx => hk (hX hx))).symm

/-- **C5(a).** At `y*(r0,i)`, if `i` is cut by `θ` and `r0` agrees with `t` on `S`, the cause
branch is positive. -/
lemma C5a {s r0 t : State N} {i : Fin N} {S : Finset (Fin N)} (θ : SysPartition N S)
    (hi : i ∈ S) (hcut : (θ.cutSet (θ.partOf i)).Nonempty) (hr : ∀ j ∈ S, r0 j = t j) :
    0 < BC (tpmOf (zstar s r0 i)) s S θ t := by
  have hz := zstar_mem s r0 i
  set T := tpmOf (zstar s r0 i) with hT
  have hle : ∀ j ∈ S, ∀ w, effUnit T (θ.cutSet (θ.partOf j))ᶜ (merge S t w) j (s j) ≤
      T.prob j (merge S t w) (s j) := by
    intro j hj w
    rw [hT, effUnit_zstar, zstar_prob]
    have hX : θ.cutSet (θ.partOf j) ⊆ S := (cutSet_partOf_subset θ hj).trans (erase_subset _ _)
    have h1 : (1 : ℝ) ≤ (agree (θ.cutSet (θ.partOf j))ᶜ (merge S t w)).card :=
      Nat.one_le_cast.2 (card_agree_pos _ _)
    split_ifs with ha hb hb
    · have := div_le_self (by norm_num : (0 : ℝ) ≤ 1 / 4) h1; linarith
    · exact absurd ⟨ha.1, merge_eq_of_mem_agree hX hr ha.2⟩ hb
    · simp
    · simp
  have hm : merge S t r0 = r0 := by
    funext k; by_cases hk : k ∈ S
    · rw [merge_mem hk, hr k hk]
    · rw [merge_not_mem hk]
  have hlt : effUnit T (θ.cutSet (θ.partOf i))ᶜ (merge S t r0) i (s i) <
      T.prob i (merge S t r0) (s i) := by
    rw [hm, hT, effUnit_zstar, zstar_prob, _root_.if_pos ⟨rfl, self_mem_agree _ _⟩, _root_.if_pos ⟨rfl, rfl⟩]
    have hcard : (2 : ℝ) ≤ (agree (θ.cutSet (θ.partOf i))ᶜ r0).card := by
      rw [card_agree, card_compl, Fintype.card_fin]
      have h1 : (θ.cutSet (θ.partOf i)).card ≤ N := by
        simpa using card_le_univ (θ.cutSet (θ.partOf i))
      rw [Nat.sub_sub_self h1]
      have : 2 ≤ 2 ^ (θ.cutSet (θ.partOf i)).card :=
        Nat.le_self_pow (Finset.card_pos.2 hcut).ne' 2
      exact_mod_cast this
    have : (1 / 4 : ℝ) / (agree (θ.cutSet (θ.partOf i))ᶜ r0).card < 1 / 4 :=
      div_lt_self (by norm_num) (by linarith)
    linarith
  have hpc : sysPartCauseProb T S s θ s t < sysCauseProb T S s s t := by
    unfold sysPartCauseProb sysCauseProb
    refine Finset.prod_lt_prod (fun j _ => div_pos (sum_pos (fun w _ =>
      mul_pos (effUnit_pos hz _ _ _ _) (bgWeight_pos hz s S w)) univ_nonempty) (by positivity))
      (fun j hj => div_le_div_of_nonneg_right (sum_le_sum fun w _ =>
        mul_le_mul_of_nonneg_right (hle j hj w) (bgWeight_nonneg _ _ _ _)) (by positivity))
      ⟨i, hi, div_lt_div_of_pos_right (sum_lt_sum (fun w _ =>
        mul_le_mul_of_nonneg_right (hle i hi w) (bgWeight_nonneg _ _ _ _))
        ⟨r0, mem_univ _, mul_lt_mul_of_pos_right hlt (bgWeight_pos hz s S r0)⟩)
        (by positivity)⟩
  have hpos := sysPartCauseProb_pos hz s S θ t
  unfold BC
  exact mul_pos (sysBackCause_pos hz s S t) (Real.logb_pos one_lt_two ((one_lt_div hpos).2 hpc))

/-- **C5(b).** At `y*(r0,i)`, if `r0` disagrees with `t'` somewhere on `S'`, the cause branch
is `≤ 0`. -/
lemma C5b {s r0 t' : State N} {i : Fin N} {S' : Finset (Fin N)} (θ' : SysPartition N S')
    (hr : ∃ j ∈ S', r0 j ≠ t' j) : BC (tpmOf (zstar s r0 i)) s S' θ' t' ≤ 0 := by
  obtain ⟨j0, hj0, hne⟩ := hr
  have hz := zstar_mem s r0 i
  set T := tpmOf (zstar s r0 i) with hT
  have hm : ∀ w, merge S' t' w ≠ r0 := fun w h => hne (by rw [← h, merge_mem hj0])
  have hle : ∀ j (M : Finset (Fin N)) w, T.prob j (merge S' t' w) (s j) ≤
      effUnit T M (merge S' t' w) j (s j) := by
    intro j M w
    rw [hT, effUnit_zstar, zstar_prob, _root_.if_neg fun h => hm w h.2, add_zero]
    exact le_add_of_nonneg_right (div_nonneg (by split_ifs <;> norm_num) (Nat.cast_nonneg _))
  have hcp : sysCauseProb T S' s s t' ≤ sysPartCauseProb T S' s θ' s t' := by
    unfold sysCauseProb sysPartCauseProb
    exact Finset.prod_le_prod (fun j _ => div_nonneg (sum_nonneg fun w _ =>
      mul_nonneg (T.nonneg _ _ _) (bgWeight_nonneg _ _ _ _)) (by positivity))
      (fun j _ => div_le_div_of_nonneg_right (sum_le_sum fun w _ =>
        mul_le_mul_of_nonneg_right (hle j _ w) (bgWeight_nonneg _ _ _ _)) (by positivity))
  have hpos := sysPartCauseProb_pos hz s S' θ' t'
  unfold BC
  exact mul_nonpos_of_nonneg_of_nonpos (sysBackCause_nonneg _ _ _ _ _)
    (Real.logb_nonpos one_lt_two (div_nonneg (sysCauseProb_nonneg _ _ _ _ _) hpos.le)
      ((div_le_one hpos).2 hcp))

/-- **C–C** (L5 + C5' + C5). Cause branches of candidates with `S' ⊄ S` differ somewhere on the
open cube. -/
lemma CC_ne {s : State N} {S S' : Finset (Fin N)} (hS : ¬ S' ⊆ S) (θ : SysPartition N S)
    (θ' : SysPartition N S') (t t' : State N) :
    ∃ z ∈ openCube N, BC (tpmOf z) s S θ t ≠ BC (tpmOf z) s S' θ' t' := by
  obtain ⟨p, hp, hne⟩ := θ.exists_cutSet_nonempty
  obtain ⟨i, hi⟩ := θ.parts_nonempty p hp
  have hiS := θ.parts_subset p hp hi
  rw [← θ.partOf_eq hp hi] at hne
  obtain ⟨j, hjS', hjS⟩ := Finset.not_subset.1 hS
  let r0 : State N := fun k => if k ∈ S then t k else !t' k
  refine ⟨zstar s r0 i, zstar_mem s r0 i, ne_of_gt ?_⟩
  refine (C5b θ' ⟨j, hjS', ?_⟩).trans_lt (C5a θ hiS hne fun k hk => by simp [r0, hk])
  simp only [r0, _root_.if_neg hjS]
  cases t' j <;> decide

/-! ### L6: the pair dichotomy -/

/-- Branch index of a candidate `S`: cause/effect, partition, state. -/
abbrev BrIdx (N : ℕ) (S : Finset (Fin N)) := Bool × SysPartition N S × State N

/-- The branch `a` of candidate `S`, as a function of the parameters. -/
noncomputable def br (s : State N) (S : Finset (Fin N)) (a : BrIdx N S) (z : Param N) : ℝ :=
  if a.1 then BC (tpmOf z) s S a.2.1 a.2.2 else BE (tpmOf z) s S a.2.1 a.2.2

/-- **L6.** Two branches of distinct candidates that agree on the whole open cube both vanish
there. -/
lemma br_dichotomy (s : State N) {S S' : Finset (Fin N)} (hne : S ≠ S') (a : BrIdx N S)
    (a' : BrIdx N S') (heq : ∀ z ∈ openCube N, br s S a z = br s S' a' z) :
    ∀ z ∈ openCube N, br s S a z = 0 := by
  obtain ⟨b, θ, t⟩ := a
  obtain ⟨b', θ', t'⟩ := a'
  cases b <;> cases b' <;> simp only [br, Bool.false_eq_true, ↓reduceIte] at heq ⊢
  · -- E–E
    by_cases h : S' ⊆ S
    · have h' : ¬ S ⊆ S' := fun h' => hne (subset_antisymm h' h)
      obtain ⟨k, hkS, hkS'⟩ := Finset.not_subset.1 h'
      have h0 := EE hkS hkS' θ' θ t' t fun z hz => (heq z hz).symm
      exact fun z hz => (heq z hz).trans (h0 z hz)
    · obtain ⟨k, hkS', hkS⟩ := Finset.not_subset.1 h
      exact EE hkS' hkS θ θ' t t' heq
  · -- E–C
    exact EC θ' θ t' heq
  · -- C–E
    have h0 := EC θ θ' t fun z hz => (heq z hz).symm
    exact fun z hz => (heq z hz).trans (h0 z hz)
  · -- C–C: impossible
    exfalso
    by_cases h : S' ⊆ S
    · have h' : ¬ S ⊆ S' := fun h' => hne (subset_antisymm h' h)
      obtain ⟨z, hz, hz'⟩ := CC_ne h' θ' θ t' t
      exact hz' (heq z hz).symm
    · obtain ⟨z, hz, hz'⟩ := CC_ne h θ θ' t t'
      exact hz' (heq z hz)

end Census
end IIT
