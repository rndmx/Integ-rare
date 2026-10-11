/-
Census: cut profiles of directional system partitions.

The profile of a system partition `θ` of `S` assigns to each unit `j` the cut set
`C_j = θ.cutSet (θ.partOf j)` of its block.  Every partitioned quantity depends on `θ` only
through the profile on `S`: the partitioned cause probability of `tpmOf z` is
`∏_{j ∈ S} Num w S (S \ C_j) t j / Zs w` with `w = flipP s z`, and the normaliser is
`∑_{j ∈ S} |C_j|`.  Consequently, if one partition strictly beats every partition with a
different profile, `φ_s` at a fixed state pair is that partition's value.  The file also shows
that every maximal cause state maximises `∏_{i ∈ S} Num w S S t i`, that its selectivity is at
least `2^{-|S|}`, and that a conditioned numerator is the average of the full numerators over
the patterns agreeing on the conditioning set.
-/
import IIT.Census.PairQuant
import IIT.Census.BigPhiProbCond

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-! ### Profiles -/

/-- The cut profile of a system partition: unit `j` loses its inputs from `C_j`. -/
noncomputable def profile {S : Finset (Fin N)} (θ : SysPartition N S) (j : Fin N) :
    Finset (Fin N) :=
  θ.cutSet (θ.partOf j)

lemma prof_partOf_mem {S : Finset (Fin N)} (θ : SysPartition N S) {j : Fin N} (hj : j ∈ S) :
    θ.partOf j ∈ θ.parts ∧ j ∈ θ.partOf j := by
  obtain ⟨p, hp, hjp⟩ := θ.parts_cover j hj
  rw [θ.partOf_eq hp hjp]
  exact ⟨hp, hjp⟩

lemma prof_cutSet_subset {S : Finset (Fin N)} (θ : SysPartition N S) (p : Finset (Fin N)) :
    θ.cutSet p ⊆ S := by
  unfold SysPartition.cutSet
  cases θ.dir p
  · exact sdiff_subset
  · refine Finset.sup_le fun q hq => ?_
    exact θ.parts_subset q (mem_filter.1 hq).1
  · exact sdiff_subset

lemma prof_profile_subset {S : Finset (Fin N)} (θ : SysPartition N S) (j : Fin N) :
    profile θ j ⊆ S :=
  prof_cutSet_subset θ _

lemma prof_compl_eq_condSet {S C : Finset (Fin N)} (hC : C ⊆ S) : Cᶜ = condSet S (S \ C) := by
  ext x
  simp only [condSet, mem_compl, mem_union, mem_sdiff]
  constructor
  · intro hx
    by_cases hxS : x ∈ S
    · exact Or.inl ⟨hxS, hx⟩
    · exact Or.inr hxS
  · rintro (⟨_, h⟩ | h)
    · exact h
    · exact fun hc => h (hC hc)

/-- **The partitioned cause probability through the profile.** -/
theorem sysPartCauseProb_eq_profile (z : Param N) (s t : State N) {S : Finset (Fin N)}
    (θ : SysPartition N S) :
    sysPartCauseProb (tpmOf z) S s θ s t =
      ∏ j ∈ S, Num (flipP s z) S (S \ profile θ j) t j / Zs (flipP s z) := by
  unfold sysPartCauseProb
  refine prod_congr rfl fun j _ => ?_
  rw [← condFactor_eq z s sdiff_subset t j]
  change _ = (∑ w : State N, effUnit (tpmOf z) (condSet S (S \ profile θ j)) (merge S t w) j (s j)
      * bgWeight (tpmOf z) S s w) / (2 : ℝ) ^ S.card
  rw [← prof_compl_eq_condSet (prof_profile_subset θ j)]
  rfl

/-- **The normaliser through the profile**: `∑ᵢ |S⁽ⁱ⁾| |X⁽ⁱ⁾| = ∑_{j ∈ S} |C_j|`. -/
theorem sysCutCount_eq_sum_profile {S : Finset (Fin N)} (θ : SysPartition N S) :
    sysCutCount θ = ∑ j ∈ S, (profile θ j).card := by
  classical
  have hmaps : ∀ j ∈ S, θ.partOf j ∈ θ.parts := fun j hj => (prof_partOf_mem θ hj).1
  rw [← sum_fiberwise_of_maps_to hmaps, sysCutCount]
  refine sum_congr rfl fun p hp => ?_
  have hfil : S.filter (fun j => θ.partOf j = p) = p := by
    ext j
    simp only [mem_filter]
    constructor
    · rintro ⟨hj, rfl⟩
      exact (prof_partOf_mem θ hj).2
    · intro hj
      exact ⟨θ.parts_subset p hp hj, θ.partOf_eq hp hj⟩
  have hc : ∀ j ∈ S.filter (fun j => θ.partOf j = p), (profile θ j).card = (θ.cutSet p).card := by
    intro j hj
    rw [profile, (mem_filter.1 hj).2]
  rw [sum_congr rfl hc, sum_const, hfil, smul_eq_mul]

/-! ### Everything depends on the profile only -/

section Congr

variable (T : UnitTPM N) {S : Finset (Fin N)} (u : State N) {θ θ' : SysPartition N S}

lemma prof_sysPartCauseProb_congr (h : ∀ j ∈ S, profile θ j = profile θ' j) (s t : State N) :
    sysPartCauseProb T S u θ s t = sysPartCauseProb T S u θ' s t := by
  unfold sysPartCauseProb
  refine prod_congr rfl fun j hj => ?_
  have := h j hj
  unfold profile at this
  rw [this]

lemma prof_sysPartEffProb_congr (h : ∀ j ∈ S, profile θ j = profile θ' j) (s t : State N) :
    sysPartEffProb T S u θ s t = sysPartEffProb T S u θ' s t := by
  unfold sysPartEffProb
  refine prod_congr rfl fun j hj => ?_
  have := h j hj
  unfold profile at this
  rw [this]

lemma prof_sysPhiC_congr (h : ∀ j ∈ S, profile θ j = profile θ' j) (s t : State N) :
    sysPhiC T S u θ s t = sysPhiC T S u θ' s t := by
  unfold sysPhiC
  rw [prof_sysPartCauseProb_congr T u h]

lemma prof_sysPhiE_congr (h : ∀ j ∈ S, profile θ j = profile θ' j) (s t : State N) :
    sysPhiE T S u θ s t = sysPhiE T S u θ' s t := by
  unfold sysPhiE
  rw [prof_sysPartEffProb_congr T u h]

lemma prof_sysPhiAt_congr (h : ∀ j ∈ S, profile θ j = profile θ' j) (s tc te : State N) :
    sysPhiAt T S u θ s tc te = sysPhiAt T S u θ' s tc te := by
  unfold sysPhiAt
  rw [prof_sysPhiC_congr T u h, prof_sysPhiE_congr T u h]

lemma prof_sysCutCount_congr (h : ∀ j ∈ S, profile θ j = profile θ' j) :
    sysCutCount θ = sysCutCount θ' := by
  rw [sysCutCount_eq_sum_profile, sysCutCount_eq_sum_profile]
  exact sum_congr rfl fun j hj => by rw [h j hj]

end Congr

/-! ### The minimiser lemma -/

/-- **The minimiser lemma.** If every partition whose profile on `S` differs from that of `θs`
has a strictly larger normalised value, then `φ_s` at the pair `(tc, te)` is the value at `θs`.
Partitions with the profile of `θs` all share its value, so the tie rule is immaterial. -/
theorem sysPhiOfState_eq_of_strict (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (θs : SysPartition N S) (s tc te : State N)
    (h : ∀ θ : SysPartition N S, (∃ j ∈ S, profile θ j ≠ profile θs j) →
      sysPhiAt T S u θs s tc te / (sysCutCount θs : ℝ) <
        sysPhiAt T S u θ s tc te / (sysCutCount θ : ℝ)) :
    sysPhiOfState T S u s tc te = sysPhiAt T S u θs s tc te := by
  have hsame : ∀ θ : SysPartition N S, (∀ j ∈ S, profile θ j = profile θs j) →
      sysPhiAt T S u θ s tc te = sysPhiAt T S u θs s tc te ∧
        (sysCutCount θ : ℝ) = sysCutCount θs := fun θ hθ =>
    ⟨prof_sysPhiAt_congr T u hθ s tc te, by rw [prof_sysCutCount_congr hθ]⟩
  have hmem : θs ∈ sysMipSetAt T S u s tc te := by
    unfold sysMipSetAt
    rw [mem_argminSet]
    intro θ
    unfold normalizedSysPhiAt
    by_cases hθ : ∀ j ∈ S, profile θ j = profile θs j
    · obtain ⟨h1, h2⟩ := hsame θ hθ
      rw [h1, h2]
    · push Not at hθ
      exact (h θ hθ).le
  have hall : ∀ θ ∈ sysMipSetAt T S u s tc te,
      sysPhiAt T S u θ s tc te = sysPhiAt T S u θs s tc te := by
    intro θ hθm
    unfold sysMipSetAt at hθm
    rw [mem_argminSet] at hθm
    by_cases hθ : ∀ j ∈ S, profile θ j = profile θs j
    · exact (hsame θ hθ).1
    · push Not at hθ
      exact absurd (hθm θs) (not_le.2 (h θ hθ))
  unfold sysPhiOfState sup'OrZero
  split
  · refine le_antisymm (sup'_le _ _ fun θ hθ => (hall θ hθ).le) ?_
    exact le_sup' (fun θ => sysPhiAt T S u θ s tc te) hmem
  · rename_i hne
    exact absurd ⟨θs, hmem⟩ hne

/-! ### Maximal cause states -/

lemma prof_sysCauseProb_eq (z : Param N) (s t : State N) (S : Finset (Fin N)) :
    sysCauseProb (tpmOf z) S s s t =
      ((Zs (flipP s z)) ^ S.card)⁻¹ * ∏ i ∈ S, Num (flipP s z) S S t i := by
  rw [sysCauseProb_eq_Num, prod_div_distrib, prod_const, div_eq_inv_mul]

/-- **Every maximal cause state maximises the product of the full numerators.** -/
theorem prod_Num_max_of_mem {z : Param N} (hz : z ∈ openCube N) (s tc : State N)
    {S : Finset (Fin N)} (htc : tc ∈ sysMaxCauseStates (tpmOf z) S s s) :
    ∀ t, ∏ i ∈ S, Num (flipP s z) S S t i ≤ ∏ i ∈ S, Num (flipP s z) S S tc i := by
  have h := mem_argmaxSet.1 htc
  have hZ := Zs_pos hz s
  set κ := ((Zs (flipP s z)) ^ S.card)⁻¹ with hκdef
  have hκ : 0 < κ := by positivity
  have hc : ∀ t, sysCauseProb (tpmOf z) S s s t = κ * ∏ i ∈ S, Num (flipP s z) S S t i :=
    fun t => prof_sysCauseProb_eq z s t S
  refine max_of_argmax_iic_scaled (fun t => ∏ i ∈ S, Num (flipP s z) S S t i)
    (fun t => prod_pos fun i _ => Num_pos hz s S S t i) κ ((2 : ℝ) ^ S.card) hκ (by positivity)
    tc fun t' => ?_
  have := h t'
  unfold sysIiC sysBackCause sysUncCause at this
  simp only [hc] at this
  exact this

/-- The selectivity of a maximal cause state is at least `2^{-|S|}`. -/
theorem sysBackCause_ge_of_mem {z : Param N} (hz : z ∈ openCube N) (s tc : State N)
    {S : Finset (Fin N)} (htc : tc ∈ sysMaxCauseStates (tpmOf z) S s s) :
    1 / (2 : ℝ) ^ S.card ≤ sysBackCause (tpmOf z) S s s tc := by
  have hmax := prod_Num_max_of_mem hz s tc htc
  have hZ := Zs_pos hz s
  have hcp : ∀ t, 0 < sysCauseProb (tpmOf z) S s s t := by
    intro t
    rw [prof_sysCauseProb_eq]
    exact mul_pos (by positivity) (prod_pos fun i _ => Num_pos hz s S S t i)
  have hle : ∀ t, sysCauseProb (tpmOf z) S s s t ≤ sysCauseProb (tpmOf z) S s s tc := by
    intro t
    rw [prof_sysCauseProb_eq, prof_sysCauseProb_eq]
    exact mul_le_mul_of_nonneg_left (hmax t) (by positivity)
  have havg : sysUncCause (tpmOf z) S s s ≤ sysCauseProb (tpmOf z) S s s tc := by
    unfold sysUncCause avgOverStates
    rw [div_le_iff₀ (by positivity)]
    calc ∑ t, sysCauseProb (tpmOf z) S s s t
        ≤ ∑ _t : State N, sysCauseProb (tpmOf z) S s s tc := sum_le_sum fun t _ => hle t
      _ = _ := by rw [sum_const, card_state, nsmul_eq_mul]; push_cast; ring
  have hunc : 0 < sysUncCause (tpmOf z) S s s := avg_pos _ hcp
  unfold sysBackCause
  rw [le_div_iff₀ (by positivity)]
  have h2 : (0 : ℝ) < 2 ^ S.card := by positivity
  rw [one_div, ← mul_assoc, inv_mul_cancel₀ h2.ne', one_mul]
  exact havg

/-! ### Averaging identity -/

lemma prof_agree_univ (x : State N) : agree (univ : Finset (Fin N)) x = {x} := by
  ext r
  simp only [mem_agree, mem_univ, forall_const, mem_singleton]
  exact ⟨fun h => funext h, fun h j => by rw [h]⟩

lemma prof_Num_full (w : Param N) (S : Finset (Fin N)) (t : State N) (i : Fin N) :
    Num w S S t i = ∑ v, clamp01 (w (merge S t v) i) * Pw w v := by
  unfold Num meanW
  refine sum_congr rfl fun v _ => ?_
  rw [union_compl, prof_agree_univ, sum_singleton, Nat.sub_self, pow_zero, div_one]

lemma prof_sum_agree_merge (w : Param N) {S Y : Finset (Fin N)} (t v : State N) (i : Fin N) :
    ∑ t' ∈ agree (Y ∪ Sᶜ) t, clamp01 (w (merge S t' v) i) =
      ∑ r ∈ agree (Y ∪ Sᶜ) (merge S t v), clamp01 (w r i) := by
  refine sum_nbij' (fun t' => merge S t' v) (fun r => merge S r t) ?_ ?_ ?_ ?_ ?_
  · intro t' ht'
    rw [mem_agree] at ht' ⊢
    intro j hj
    by_cases hjS : j ∈ S
    · simp only [merge, hjS, ite_true]
      exact ht' j hj
    · simp [merge, hjS]
  · intro r hr
    rw [mem_agree] at hr ⊢
    intro j hj
    by_cases hjS : j ∈ S
    · have := hr j hj
      simp only [merge, hjS, ite_true] at this ⊢
      exact this
    · simp [merge, hjS]
  · intro t' ht'
    rw [mem_agree] at ht'
    funext j
    by_cases hjS : j ∈ S
    · simp [merge, hjS]
    · simp only [merge, hjS, ite_false]
      exact (ht' j (mem_union_right _ (mem_compl.2 hjS))).symm
  · intro r hr
    rw [mem_agree] at hr
    funext j
    by_cases hjS : j ∈ S
    · simp [merge, hjS]
    · have := hr j (mem_union_right _ (mem_compl.2 hjS))
      simp only [merge, hjS, ite_false] at this ⊢
      exact this.symm
  · intro _ _
    rfl

/-- **The averaging identity.** The numerator conditioned on the pattern of `t` on `Y` is the
average of the full numerators over the patterns `t'` that agree with `t` on `Y` and off `S`
(there are `2^(|S| - |Y|)` of them when `Y ⊆ S`). -/
theorem Num_eq_avg (w : Param N) (S Y : Finset (Fin N)) (t : State N) (i : Fin N) :
    Num w S Y t i =
      (∑ t' ∈ agree (Y ∪ Sᶜ) t, Num w S S t' i) / (2 : ℝ) ^ (S.card - Y.card) := by
  simp_rw [prof_Num_full]
  rw [sum_comm, sum_div]
  unfold Num meanW
  refine sum_congr rfl fun v _ => ?_
  rw [← sum_mul, prof_sum_agree_merge, div_mul_eq_mul_div]

end Census
end IIT
