/-
Census, module B2 (part): no exact tie between single-cut values of `univ`, almost everywhere.

At a fixed pair `(tc, te)`, `ph_j = min (β Fᶜⱼ) (e Fᵉⱼ)`, and `β Fᶜⱼ`, `e Fᵉⱼ` are the analytic branches
`BC`, `BE` of the split `θⱼ`.  A tie `ph_j = ph_j'` (`j ≠ j'`) puts `z` in the zero set of one of four
branch differences.  Each difference is non-zero at an explicit point of the open cube (all entries
`1/2` except one entry of column `j`), so each zero set is null (Mityagin).
-/
import IIT.Census.B1Proxy
import IIT.Census.TieAnalytic

namespace IIT
namespace Census

open Finset MeasureTheory

variable {N : ℕ}

/-! ### The branches at the split -/

lemma BC_split {z : Param N} (hz : z ∈ openCube N) (s tc : State N) (j : Fin N)
    (hr : ((univ : Finset (Fin N)).erase j).Nonempty) :
    BC (tpmOf z) s univ (splitAt (mem_univ j) hr) tc =
      sysBackCause (tpmOf z) univ s s tc * kF (lamCz z s tc) j := by
  unfold BC
  congr 1
  rw [ur_logb_eq s hz tc _, ur_G, Finset.sum_div]
  rw [← sum_profile_splitAt (lamCz z s tc) (fun i => lamCU_empty _ _ _ (Num_pos hz s _ _ tc i)) j hr]
  rfl

lemma BE_split {z : Param N} (hz : z ∈ openCube N) (s te : State N) (j : Fin N)
    (hr : ((univ : Finset (Fin N)).erase j).Nonempty) :
    BE (tpmOf z) s univ (splitAt (mem_univ j) hr) te =
      sysEffProb (tpmOf z) univ s s te * kF (lamEz z s te) j := by
  unfold BE
  congr 1
  rw [← sum_profile_splitAt (lamEz z s te) (fun i => lamEU_empty hz s te i) j hr]
  rw [sysEffProb, sysPartEffProb, merge_univ, ← prod_div_distrib, Real.logb, Real.log_prod]
  · rw [Finset.sum_div]; rfl
  · intro i _
    exact (div_pos (prob_pos hz i s (te i)) (effUnit_pos hz _ s i (te i))).ne'

/-! ### The witness point -/

/-- All entries `1/2` except the entry `(R, j)`, which is `3/4`. -/
noncomputable def zSpike (R : State N) (j : Fin N) : Param N :=
  fun r i => if r = R ∧ i = j then 3 / 4 else 1 / 2

lemma zSpike_open (R : State N) (j : Fin N) : zSpike R j ∈ openCube N := by
  intro r i; unfold zSpike; split_ifs <;> constructor <;> norm_num

lemma clamp01_half : clamp01 (1 / 2 : ℝ) = 1 / 2 := by unfold clamp01; norm_num
lemma clamp01_3q : clamp01 (3 / 4 : ℝ) = 3 / 4 := by unfold clamp01; norm_num

lemma sum_spike (A : Finset (State N)) {R : State N} (hR : R ∈ A) (g : State N → ℝ)
    (hg : ∀ r, r ≠ R → g r = 1 / 2) :
    ∑ r ∈ A, g r = (A.card : ℝ) / 2 + (g R - 1 / 2) := by
  rw [← add_sum_erase A g hR, sum_congr rfl fun r hr => hg r (ne_of_mem_erase hr), sum_const,
    card_erase_of_mem hR, nsmul_eq_mul]
  have : 1 ≤ A.card := card_pos.2 ⟨R, hR⟩
  rw [Nat.cast_sub this]; push_cast; ring

lemma sum_flat (A : Finset (State N)) (g : State N → ℝ) (hg : ∀ r, g r = 1 / 2) :
    ∑ r ∈ A, g r = (A.card : ℝ) / 2 := by
  rw [sum_congr rfl fun r _ => hg r, sum_const, nsmul_eq_mul]; ring

/-- The spiked ratio is not `1`. -/
lemma logb_spike_ne {a c : ℝ} (hc : 2 ≤ c) (ha : 0 < a) (ha2 : a ≠ 1 / 2) :
    Real.logb 2 (a / ((c / 2 + (a - 1 / 2)) / c)) ≠ 0 := by
  have hden : 0 < (c / 2 + (a - 1 / 2)) / c := div_pos (by linarith) (by linarith)
  have hX : 0 < a / ((c / 2 + (a - 1 / 2)) / c) := div_pos ha hden
  intro h
  unfold Real.logb at h
  rcases div_eq_zero_iff.1 h with h | h
  · rcases Real.log_eq_zero.1 h with h | h | h
    · linarith
    · rw [div_eq_one_iff_eq hden.ne', eq_div_iff (by linarith)] at h
      apply ha2
      have : (a - 1 / 2) * (c - 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h1 | h1 <;> linarith
    · linarith
  · exact (Real.log_pos one_lt_two).ne' h

lemma logb_flat (c : ℝ) (hc : 0 < c) : Real.logb 2 ((1 / 2 : ℝ) / ((c / 2) / c)) = 0 := by
  rw [show (c / 2) / c = (1 / 2 : ℝ) by field_simp, div_self (by norm_num), Real.logb_one]

lemma card_agree_single (t : State N) (j : Fin N) :
    ((agree ({j} : Finset (Fin N)) t).card : ℝ) = (2 : ℝ) ^ (N - 1) := by
  rw [card_agree, card_singleton]; push_cast; rfl

lemma two_pow_ge (hN : 2 ≤ N) : (2 : ℝ) ≤ (2 : ℝ) ^ (N - 1) := by
  calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (N - 1) := pow_le_pow_right₀ (by norm_num) (by omega)

/-- Cause side: an untouched column has `F = 0`. -/
lemma kFC_flat (s tc R : State N) {j j' : Fin N} (hj : j' ≠ j) :
    kF (lamCz (zSpike R j) s tc) j' = 0 := by
  rw [kF_lamCz (zSpike_open R j)]
  have hv : ∀ r, clamp01 (flipP s (zSpike R j) r j') = 1 / 2 := fun r => by
    have hz : zSpike R j r j' = 1 / 2 := by simp [zSpike, hj]
    have h1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    unfold flipP flipC
    rw [hz]; split_ifs <;> simp only [h1, clamp01_half]
  unfold cmean
  rw [sum_flat _ _ hv, hv, card_agree_single, card_singleton]
  exact logb_flat _ (by positivity)

lemma prob_zSpike_other (R r : State N) {j j' : Fin N} (hj : j' ≠ j) (b : Bool) :
    (tpmOf (zSpike R j)).prob j' r b = 1 / 2 := by
  have hz : zSpike R j r j' = 1 / 2 := by simp [zSpike, hj]
  simp only [tpmOf, hz, clamp01_half]; split_ifs <;> norm_num

lemma prob_zSpike_off (R r : State N) (j : Fin N) (hr : r ≠ R) (b : Bool) :
    (tpmOf (zSpike R j)).prob j r b = 1 / 2 := by
  have hz : zSpike R j r j = 1 / 2 := by simp [zSpike, hr]
  simp only [tpmOf, hz, clamp01_half]; split_ifs <;> norm_num

lemma prob_zSpike_at (R : State N) (j : Fin N) (b : Bool) :
    (tpmOf (zSpike R j)).prob j R b = 3 / 4 ∨ (tpmOf (zSpike R j)).prob j R b = 1 / 4 := by
  have hz : zSpike R j R j = 3 / 4 := by simp [zSpike]
  simp only [tpmOf, hz, clamp01_3q]; split_ifs
  · left; rfl
  · right; norm_num

lemma kF_lamEz (z : Param N) (s te : State N) (j : Fin N) :
    kF (lamEz z s te) j = Real.logb 2 ((tpmOf z).prob j s (te j) /
      effUnit (tpmOf z) {j} s j (te j)) := by
  unfold kF lamEz lamEU
  rw [show ((univ : Finset (Fin N)).erase j)ᶜ = {j} by ext; simp]

/-- Effect side: an untouched column has `F = 0`. -/
lemma kFE_flat (s te R : State N) {j j' : Fin N} (hj : j' ≠ j) :
    kF (lamEz (zSpike R j) s te) j' = 0 := by
  rw [kF_lamEz, effUnit, sum_flat _ _ fun r => prob_zSpike_other R r hj _,
    prob_zSpike_other R s hj, card_agree_single]
  exact logb_flat _ (by positivity)

/-- Cause side: the spiked column has `F ≠ 0`. -/
lemma kFC_spike (hN : 2 ≤ N) (s tc : State N) (j : Fin N) :
    kF (lamCz (zSpike tc j) s tc) j ≠ 0 := by
  rw [kF_lamCz (zSpike_open tc j)]
  set g : State N → ℝ := fun r => clamp01 (flipP s (zSpike tc j) r j) with hgdef
  have hoff : ∀ r, r ≠ tc → g r = 1 / 2 := fun r hr => by
    have hz : zSpike tc j r j = 1 / 2 := by simp [zSpike, hr]
    have h1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    simp only [g, flipP, flipC, hz]; split_ifs <;> simp only [h1, clamp01_half]
  have hat : g tc = 3 / 4 ∨ g tc = 1 / 4 := by
    have hz : zSpike tc j tc j = 3 / 4 := by simp [zSpike]
    simp only [g, flipP, flipC, hz]; split_ifs
    · left; exact clamp01_3q
    · right; unfold clamp01; norm_num
  unfold cmean
  rw [sum_spike _ (mem_agree.2 fun _ _ => rfl) g hoff, card_agree_single, card_singleton]
  have hc := two_pow_ge hN
  show Real.logb 2 (g tc / (((2 : ℝ) ^ (N - 1) / 2 + (g tc - 1 / 2)) / (2 : ℝ) ^ (N - 1))) ≠ 0
  rcases hat with h | h <;> rw [h] <;> exact logb_spike_ne hc (by norm_num) (by norm_num)

/-- Effect side: the spiked column has `F ≠ 0`. -/
lemma kFE_spike (hN : 2 ≤ N) (s te : State N) (j : Fin N) :
    kF (lamEz (zSpike s j) s te) j ≠ 0 := by
  rw [kF_lamEz, effUnit,
    sum_spike _ (mem_agree.2 fun _ _ => rfl) _ fun r hr => prob_zSpike_off s r j hr _,
    card_agree_single]
  have hc := two_pow_ge hN
  rcases prob_zSpike_at s j (te j) with h | h <;> rw [h] <;>
    exact logb_spike_ne hc (by norm_num) (by norm_num)

/-! ### The tie set is null -/

lemma min_eq_min_cases {a b c d : ℝ} (h : min a b = min c d) :
    a = c ∨ a = d ∨ b = c ∨ b = d := by
  rcases min_choice a b with h1 | h1 <;> rcases min_choice c d with h2 | h2 <;>
    rw [h1, h2] at h <;> tauto

lemma null_of_analytic_ne {f g : Param N → ℝ} (hf : AnalyticOnNhd ℝ f (openCube N))
    (hg : AnalyticOnNhd ℝ g (openCube N)) {z0 : Param N} (hz0 : z0 ∈ openCube N)
    (hne : f z0 ≠ g z0) : volume {z | z ∈ openCube N ∧ f z = g z} = 0 := by
  refine measure_mono_null ?_ (volume_zero_set_analytic volume (isOpen_openCube N)
    (convex_openCube N).isPreconnected (f := fun z => f z - g z)
    (fun z hz => (hf z hz).fun_sub (hg z hz)) ⟨z0, hz0, sub_ne_zero.2 hne⟩)
  rintro z ⟨hz, he⟩
  exact ⟨hz, sub_eq_zero.2 he⟩

/-- **No exact tie between single-cut values of `univ`, a.e.** For fixed `s, tc, te` and
`j ≠ j₂`, the set of open-cube parameters where `ph_j = ph_j₂` is null. -/
theorem volume_univ_tie (hN : 2 ≤ N) (s tc te : State N) {j j₂ : Fin N} (hjj : j ≠ j₂) :
    volume {z : Param N | z ∈ openCube N ∧
      phT (lamCz z s tc) (lamEz z s te) (sysBackCause (tpmOf z) univ s s tc)
        (sysEffProb (tpmOf z) univ s s te) j =
      phT (lamCz z s tc) (lamEz z s te) (sysBackCause (tpmOf z) univ s s tc)
        (sysEffProb (tpmOf z) univ s s te) j₂} = 0 := by
  have hr : ∀ i : Fin N, ((univ : Finset (Fin N)).erase i).Nonempty := fun i => by
    have := card_erase_of_mem (mem_univ i) (s := (univ : Finset (Fin N)))
    rw [card_univ, Fintype.card_fin] at this
    exact card_pos.1 (by omega)
  have aC : ∀ i, AnalyticOnNhd ℝ (fun z : Param N =>
      BC (tpmOf z) s univ (splitAt (mem_univ i) (hr i)) tc) (openCube N) :=
    fun i z hz => an_BC hz s univ _ tc
  have aE : ∀ i, AnalyticOnNhd ℝ (fun z : Param N =>
      BE (tpmOf z) s univ (splitAt (mem_univ i) (hr i)) te) (openCube N) :=
    fun i z hz => an_BE hz s univ _ te
  have hj2 : j₂ ≠ j := hjj.symm
  have hoC := zSpike_open tc j
  have hoE := zSpike_open s j
  -- the witness values
  have cj : BC (tpmOf (zSpike tc j)) s univ (splitAt (mem_univ j) (hr j)) tc ≠ 0 := by
    rw [BC_split hoC]
    exact mul_ne_zero (sysBackCause_pos hoC s univ tc).ne' (kFC_spike hN s tc j)
  have ej : BE (tpmOf (zSpike s j)) s univ (splitAt (mem_univ j) (hr j)) te ≠ 0 := by
    rw [BE_split hoE]
    exact mul_ne_zero (sysEffProb_pos hoE s univ te).ne' (kFE_spike hN s te j)
  have c2C : BC (tpmOf (zSpike tc j)) s univ (splitAt (mem_univ j₂) (hr j₂)) tc = 0 := by
    rw [BC_split hoC, kFC_flat s tc tc hj2, mul_zero]
  have e2C : BE (tpmOf (zSpike tc j)) s univ (splitAt (mem_univ j₂) (hr j₂)) te = 0 := by
    rw [BE_split hoC, kFE_flat s te tc hj2, mul_zero]
  have c2E : BC (tpmOf (zSpike s j)) s univ (splitAt (mem_univ j₂) (hr j₂)) tc = 0 := by
    rw [BC_split hoE, kFC_flat s tc s hj2, mul_zero]
  have e2E : BE (tpmOf (zSpike s j)) s univ (splitAt (mem_univ j₂) (hr j₂)) te = 0 := by
    rw [BE_split hoE, kFE_flat s te s hj2, mul_zero]
  refine measure_mono_null (t := {z | z ∈ openCube N ∧
      BC (tpmOf z) s univ (splitAt (mem_univ j) (hr j)) tc =
        BC (tpmOf z) s univ (splitAt (mem_univ j₂) (hr j₂)) tc} ∪
      {z | z ∈ openCube N ∧ BC (tpmOf z) s univ (splitAt (mem_univ j) (hr j)) tc =
        BE (tpmOf z) s univ (splitAt (mem_univ j₂) (hr j₂)) te} ∪
      {z | z ∈ openCube N ∧ BE (tpmOf z) s univ (splitAt (mem_univ j) (hr j)) te =
        BC (tpmOf z) s univ (splitAt (mem_univ j₂) (hr j₂)) tc} ∪
      {z | z ∈ openCube N ∧ BE (tpmOf z) s univ (splitAt (mem_univ j) (hr j)) te =
        BE (tpmOf z) s univ (splitAt (mem_univ j₂) (hr j₂)) te}) ?_
    (measure_union_null (measure_union_null (measure_union_null
      (null_of_analytic_ne (aC j) (aC j₂) hoC (by rw [c2C]; exact cj))
      (null_of_analytic_ne (aC j) (aE j₂) hoC (by rw [e2C]; exact cj)))
      (null_of_analytic_ne (aE j) (aC j₂) hoE (by rw [c2E]; exact ej)))
      (null_of_analytic_ne (aE j) (aE j₂) hoE (by rw [e2E]; exact ej)))
  rintro z ⟨hz, he⟩
  unfold phT at he
  rw [← BC_split hz s tc j (hr j), ← BE_split hz s te j (hr j), ← BC_split hz s tc j₂ (hr j₂),
    ← BE_split hz s te j₂ (hr j₂)] at he
  rcases min_eq_min_cases he with h | h | h | h
  · exact Or.inl (Or.inl (Or.inl ⟨hz, h⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨hz, h⟩))
  · exact Or.inl (Or.inr ⟨hz, h⟩)
  · exact Or.inr ⟨hz, h⟩

/-- **`NoExactTie` holds almost everywhere**, at every pair of states simultaneously. -/
theorem volume_univ_tie_any (hN : 2 ≤ N) (s : State N) :
    volume {z : Param N | z ∈ openCube N ∧ ∃ tc te : State N, ∃ j j₂ : Fin N, j ≠ j₂ ∧
      phT (lamCz z s tc) (lamEz z s te) (sysBackCause (tpmOf z) univ s s tc)
        (sysEffProb (tpmOf z) univ s s te) j =
      phT (lamCz z s tc) (lamEz z s te) (sysBackCause (tpmOf z) univ s s tc)
        (sysEffProb (tpmOf z) univ s s te) j₂} = 0 := by
  have h : {z : Param N | z ∈ openCube N ∧ ∃ tc te : State N, ∃ j j₂ : Fin N, j ≠ j₂ ∧
      phT (lamCz z s tc) (lamEz z s te) (sysBackCause (tpmOf z) univ s s tc)
        (sysEffProb (tpmOf z) univ s s te) j =
      phT (lamCz z s tc) (lamEz z s te) (sysBackCause (tpmOf z) univ s s tc)
        (sysEffProb (tpmOf z) univ s s te) j₂} ⊆
      ⋃ tc : State N, ⋃ te : State N, ⋃ j : Fin N, ⋃ j₂ : Fin N,
        (if j = j₂ then ∅ else {z : Param N | z ∈ openCube N ∧
          phT (lamCz z s tc) (lamEz z s te) (sysBackCause (tpmOf z) univ s s tc)
            (sysEffProb (tpmOf z) univ s s te) j =
          phT (lamCz z s tc) (lamEz z s te) (sysBackCause (tpmOf z) univ s s tc)
            (sysEffProb (tpmOf z) univ s s te) j₂}) := by
    rintro z ⟨hz, tc, te, j, j₂, hne, he⟩
    simp only [Set.mem_iUnion]
    exact ⟨tc, te, j, j₂, by rw [if_neg hne]; exact ⟨hz, he⟩⟩
  refine measure_mono_null h (measure_iUnion_null fun tc => measure_iUnion_null fun te =>
    measure_iUnion_null fun j => measure_iUnion_null fun j₂ => ?_)
  split_ifs with hjj
  · exact measure_empty
  · exact volume_univ_tie hN s tc te hjj

/-! ### No tie between row products (blueprint `null_tcRow_tie`) -/

lemma Pw_eq_fullProb (w : Param N) (r : State N) :
    Pw w r = fullProb (tpmOf w) r (fun _ => true) := by
  unfold Pw fullProb tpmOf; simp

/-- **No two distinct rows have the same row product, `cubeM`-a.e.** -/
theorem null_tcRow_tie :
    cubeM N {w : Param N | ∃ r r' : State N, r ≠ r' ∧ Pw w r = Pw w r'} = 0 := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    have : {w : Param 0 | ∃ r r' : State 0, r ≠ r' ∧ Pw w r = Pw w r'} = ∅ := by
      ext w; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro r r' hne; exact absurd (funext fun i => i.elim0) hne
    rw [this, measure_empty]
  set j0 : Fin N := ⟨0, hpos⟩
  have an : ∀ r : State N, AnalyticOnNhd ℝ (fun w : Param N => Pw w r) (openCube N) :=
    fun r w hw => by
      simp only [Pw_eq_fullProb]; exact an_fullProb hw r _
  have hpair : ∀ r r' : State N, r ≠ r' →
      volume {w : Param N | w ∈ openCube N ∧ Pw w r = Pw w r'} = 0 := by
    intro r r' hne
    refine null_of_analytic_ne (an r) (an r') (zSpike_open r j0) ?_
    have hoff : ∀ i, clamp01 (zSpike r j0 r' i) = 1 / 2 := fun i => by
      have : zSpike r j0 r' i = 1 / 2 := by simp [zSpike, Ne.symm hne]
      rw [this, clamp01_half]
    have hon : ∀ i, 1 / 2 ≤ clamp01 (zSpike r j0 r i) := fun i => by
      unfold zSpike; split_ifs
      · rw [clamp01_3q]; norm_num
      · rw [clamp01_half]
    unfold Pw
    rw [prod_congr rfl fun i _ => hoff i]
    refine (prod_lt_prod (fun _ _ => by norm_num) (fun i _ => hon i)
      ⟨j0, mem_univ _, by simp [zSpike, clamp01_3q]; norm_num⟩).ne'
  have hsub : {w : Param N | ∃ r r' : State N, r ≠ r' ∧ Pw w r = Pw w r'} ⊆
      (openCube N)ᶜ ∪ ⋃ r : State N, ⋃ r' : State N,
        (if r = r' then ∅ else {w : Param N | w ∈ openCube N ∧ Pw w r = Pw w r'}) := by
    rintro w ⟨r, r', hne, he⟩
    by_cases hw : w ∈ openCube N
    · right; simp only [Set.mem_iUnion]
      exact ⟨r, r', by rw [if_neg hne]; exact ⟨hw, he⟩⟩
    · exact Or.inl hw
  refine measure_mono_null hsub (measure_union_null cubeM_compl_openCube
    (measure_iUnion_null fun r => measure_iUnion_null fun r' => ?_))
  split_ifs with h
  · exact measure_empty
  · rw [← restrict_cube]
    exact le_antisymm ((Measure.restrict_le_self _).trans (hpair r r' h).le) zero_le

end Census
end IIT
