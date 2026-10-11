/-
Census, module B1UnivMIP part 2: the classification of directional partitions of `univ`
(W3 §3, C0-C8).  Every partition's profile has one of the four shapes of `B1KeyLemma`
(Case 1 giant part / 2a two small outputs parts / 2b one small outputs part / 2c none).
-/
import IIT.Census.Profile
import IIT.Census.B1KeyLemma

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- `Out`: the union of the blocks whose outputs are cut (direction `outputs` or `both`). -/
noncomputable def outU (θ : SysPartition N univ) : Finset (Fin N) :=
  (θ.parts.filter fun q => θ.dir q ≠ Dir.inputs).sup id

variable (θ : SysPartition N univ)

lemma mem_outU {x : Fin N} : x ∈ outU θ ↔ ∃ q ∈ θ.parts, θ.dir q ≠ Dir.inputs ∧ x ∈ q := by
  unfold outU
  simp only [mem_sup, mem_filter, id]
  constructor
  · rintro ⟨q, ⟨hq, hd⟩, hx⟩; exact ⟨q, hq, hd, hx⟩
  · rintro ⟨q, hq, hd, hx⟩; exact ⟨q, ⟨hq, hd⟩, hx⟩

lemma subset_outU {p : Finset (Fin N)} (hp : p ∈ θ.parts) (hd : θ.dir p ≠ Dir.inputs) :
    p ⊆ outU θ := fun x hx => (mem_outU θ).2 ⟨p, hp, hd, hx⟩

/-- **C0, outputs blocks.** -/
lemma cutSet_outputs {p : Finset (Fin N)} (hp : p ∈ θ.parts) (hd : θ.dir p = Dir.outputs) :
    θ.cutSet p = outU θ \ p := by
  ext x
  simp only [SysPartition.cutSet, hd, mem_sup, mem_filter, id, mem_sdiff, mem_outU]
  constructor
  · rintro ⟨q, ⟨hq, hqp, hdq⟩, hx⟩
    refine ⟨⟨q, hq, ?_, hx⟩, ?_⟩
    · rcases hdq with h | h <;> rw [h] <;> decide
    · exact fun hxp => disjoint_left.1 (θ.parts_disjoint q hq p hp hqp) hx hxp
  · rintro ⟨⟨q, hq, hdq, hx⟩, hxp⟩
    refine ⟨q, ⟨hq, fun h => hxp (h ▸ hx), ?_⟩, hx⟩
    cases h : θ.dir q
    · exact absurd h hdq
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- **C0, inputs/both blocks.** -/
lemma cutSet_not_outputs {p : Finset (Fin N)} (hd : θ.dir p ≠ Dir.outputs) :
    θ.cutSet p = univ \ p := by
  unfold SysPartition.cutSet
  cases h : θ.dir p
  · rfl
  · exact absurd h hd
  · rfl

lemma cls_part (j : Fin N) : θ.partOf j ∈ θ.parts ∧ j ∈ θ.partOf j :=
  prof_partOf_mem θ (mem_univ j)

lemma cls_other {p : Finset (Fin N)} (hp : p ∈ θ.parts) : ∃ x, x ∉ p := by
  obtain ⟨q, hq, hqp⟩ := exists_mem_ne (lt_of_lt_of_le one_lt_two θ.two_le) p
  obtain ⟨x, hx⟩ := θ.parts_nonempty q hq
  exact ⟨x, fun hxp => disjoint_left.1 (θ.parts_disjoint q hq p hp hqp) hx hxp⟩

/-- C1: no unit is cut from itself. -/
lemma profile_not_self (j : Fin N) : j ∉ profile θ j := by
  obtain ⟨hp, hj⟩ := cls_part θ j
  unfold profile
  by_cases hd : θ.dir (θ.partOf j) = Dir.outputs
  · rw [cutSet_outputs θ hp hd]; exact fun h => (mem_sdiff.1 h).2 hj
  · rw [cutSet_not_outputs θ hd]; exact fun h => (mem_sdiff.1 h).2 hj

lemma profile_eq_of_mem {p : Finset (Fin N)} (hp : p ∈ θ.parts) {j : Fin N} (hj : j ∈ p) :
    profile θ j = θ.cutSet p := by
  unfold profile; rw [θ.partOf_eq hp hj]

/-- **Classification (W3 §3).** With `1 ≤ D` and `2D ≤ N`, the profile of every partition of
`univ` has one of the four shapes. -/
theorem profile_shape {D : ℕ} (hD : 1 ≤ D) :
    Shape1 D (profile θ) ∨ Shape2a D (profile θ) ∨ Shape2b D (profile θ) ∨
      Shape2c D (profile θ) := by
  classical
  by_cases hg : ∃ g ∈ θ.parts, θ.dir g ≠ Dir.outputs ∧ N < g.card + D
  · -- Case 1: a giant part
    left
    obtain ⟨g, hg, hdg, hcard⟩ := hg
    refine ⟨univ \ g, ?_, ?_, fun j hj => ?_⟩
    · obtain ⟨x, hx⟩ := cls_other θ hg
      exact card_pos.2 ⟨x, mem_sdiff.2 ⟨mem_univ x, hx⟩⟩
    · rw [card_univ_diff, Fintype.card_fin]; omega
    · have hjg : j ∈ g := by simpa using hj
      rw [profile_eq_of_mem θ hg hjg, cutSet_not_outputs θ hdg]
  right
  push Not at hg
  -- units of inputs/both blocks have big cuts
  have hnon : ∀ j, θ.dir (θ.partOf j) ≠ Dir.outputs → D ≤ (profile θ j).card := by
    intro j hd
    obtain ⟨hp, -⟩ := cls_part θ j
    unfold profile
    rw [cutSet_not_outputs θ hd, card_univ_diff, Fintype.card_fin]
    have := hg _ hp hd; omega
  have hprofout : ∀ j, θ.dir (θ.partOf j) = Dir.outputs →
      profile θ j = outU θ \ θ.partOf j := fun j hd => by
    unfold profile; rw [cutSet_outputs θ (cls_part θ j).1 hd]
  -- a unit outside `Out` lies in an inputs block
  have hinp : ∀ j, j ∉ outU θ → θ.dir (θ.partOf j) ≠ Dir.outputs := by
    intro j hj hd
    exact hj (subset_outU θ (cls_part θ j).1 (by rw [hd]; decide) (cls_part θ j).2)
  set Os := θ.parts.filter fun p => θ.dir p = Dir.outputs ∧ 1 ≤ (outU θ \ p).card ∧
    (outU θ \ p).card < D with hOs
  -- an outputs block outside `Os` has an empty or big cut
  have hnotOs : ∀ j, θ.dir (θ.partOf j) = Dir.outputs → θ.partOf j ∉ Os →
      profile θ j = ∅ ∨ D ≤ (profile θ j).card := by
    intro j hd hnot
    rw [hprofout j hd]
    by_contra hc
    push Not at hc
    exact hnot (mem_filter.2 ⟨(cls_part θ j).1, hd, card_pos.2 hc.1,
      hc.2⟩)
  by_cases h2 : 2 ≤ Os.card
  · -- Case 2a
    left
    obtain ⟨p, hp, p', hp', hpp'⟩ := one_lt_card.1 h2
    have hp1 := (mem_filter.1 hp)
    have hp1' := (mem_filter.1 hp')
    refine ⟨outU θ, ?_, fun j hj => hnon j (hinp j hj)⟩
    have hpO := subset_outU θ hp1.1 (by rw [hp1.2.1]; decide)
    have hsub : p ⊆ outU θ \ p' := fun x hx =>
      mem_sdiff.2 ⟨hpO hx, fun hx' => disjoint_left.1 (θ.parts_disjoint p hp1.1 p' hp1'.1 hpp') hx hx'⟩
    have h1 := card_le_card hsub
    have h2 := card_sdiff_add_card_eq_card hpO
    omega
  right
  push Not at h2
  rcases Nat.lt_or_ge Os.card 1 with h0 | h1
  · -- Case 2c: no small outputs block
    right
    have hOs0 : Os = ∅ := card_eq_zero.1 (by omega)
    have hcut : ∀ j, profile θ j = ∅ ∨ D ≤ (profile θ j).card := by
      intro j
      by_cases hd : θ.dir (θ.partOf j) = Dir.outputs
      · exact hnotOs j hd (by rw [hOs0]; exact notMem_empty _)
      · exact Or.inr (hnon j hd)
    refine ⟨hcut, ?_⟩
    by_cases hZ : (univ.filter fun j => profile θ j = ∅) = ∅
    · left; rw [hZ, card_empty]; omega
    right
    obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.2 hZ
    have hz' : profile θ z = ∅ := (mem_filter.1 hz).2
    set p0 := θ.partOf z with hp0
    have hp0mem := (cls_part θ z).1
    -- the uncut unit's block is an outputs block equal to `Out`
    have hd0 : θ.dir p0 = Dir.outputs := by
      by_contra hd
      rw [show profile θ z = univ \ p0 from by unfold profile; rw [cutSet_not_outputs θ hd]] at hz'
      obtain ⟨x, hx⟩ := cls_other θ hp0mem
      have : x ∈ univ \ p0 := mem_sdiff.2 ⟨mem_univ x, hx⟩
      rw [hz'] at this; exact notMem_empty x this
    have hOut : outU θ = p0 := by
      have h1 : outU θ \ p0 = ∅ := by rw [← hprofout z hd0]; exact hz'
      exact Subset.antisymm (sdiff_eq_empty_iff_subset.1 h1)
        (subset_outU θ hp0mem (by rw [hd0]; decide))
    have huncut : ∀ x, profile θ x = ∅ → x ∈ p0 := by
      intro x hx0
      by_cases hdx : θ.dir (θ.partOf x) = Dir.outputs
      · have := subset_outU θ (cls_part θ x).1 (by rw [hdx]; decide) (cls_part θ x).2
        rwa [hOut] at this
      · exfalso
        obtain ⟨y, hy⟩ := cls_other θ (cls_part θ x).1
        have h' : profile θ x = univ \ θ.partOf x := by
          unfold profile; rw [cutSet_not_outputs θ hdx]
        have : y ∈ profile θ x := by rw [h']; exact mem_sdiff.2 ⟨mem_univ y, hy⟩
        rw [hx0] at this; exact notMem_empty y this
    -- every cut unit lies in an inputs block disjoint from `p0`
    have hcutunit : ∀ j, profile θ j ≠ ∅ → θ.dir (θ.partOf j) ≠ Dir.outputs ∧ j ∉ p0 := by
      intro j hj
      have hjp0 : j ∉ p0 := by
        intro hjp
        apply hj
        rw [profile_eq_of_mem θ hp0mem hjp, cutSet_outputs θ hp0mem hd0, hOut, sdiff_self, bot_eq_empty]
      refine ⟨fun hd => ?_, hjp0⟩
      have hne : θ.dir (θ.partOf j) ≠ Dir.inputs := by rw [hd]; decide
      exact hjp0 (hOut ▸ subset_outU θ (cls_part θ j).1 hne (cls_part θ j).2)
    intro j hj
    obtain ⟨hdj, hjp0⟩ := hcutunit j hj
    have hpj := cls_part θ j
    have hprofj : profile θ j = univ \ θ.partOf j := by
      unfold profile; rw [cutSet_not_outputs θ hdj]
    refine ⟨fun x hx => ?_, fun i hi => ?_⟩
    · -- an uncut unit lies in `p0`, hence outside `j`'s block
      have hx' : profile θ x = ∅ := (mem_filter.1 hx).2
      have hxp0 : x ∈ p0 := huncut x hx'
      rw [hprofj]
      refine mem_sdiff.2 ⟨mem_univ x, fun hxj => ?_⟩
      have hne : θ.partOf j ≠ p0 := fun h => hjp0 (h ▸ hpj.2)
      exact disjoint_left.1 (θ.parts_disjoint _ hpj.1 p0 hp0mem hne) hxj hxp0
    · -- `i` outside `j`'s cut lies in `j`'s block
      have hij : i ∈ θ.partOf j := by
        rw [hprofj] at hi; simpa using hi
      rw [profile_eq_of_mem θ hpj.1 hij]
      rfl
  · -- Case 2b: exactly one small outputs block
    left
    obtain ⟨ps, hps⟩ := card_eq_one.1 (by omega : Os.card = 1)
    have hpsmem : ps ∈ Os := by rw [hps]; exact mem_singleton_self ps
    have hm := mem_filter.1 hpsmem
    obtain ⟨hpsp, hpsd, hK1, hKD⟩ := (⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2⟩ :
      ps ∈ θ.parts ∧ θ.dir ps = Dir.outputs ∧ 1 ≤ (outU θ \ ps).card ∧ (outU θ \ ps).card < D)
    refine ⟨ps, outU θ \ ps, disjoint_sdiff, hK1, hKD, fun j hj => ?_, fun j hj => ?_,
      fun j hjP hjK => ?_⟩
    · rw [profile_eq_of_mem θ hpsp hj, cutSet_outputs θ hpsp hpsd]
    · by_cases hd : θ.dir (θ.partOf j) = Dir.outputs
      · refine hnotOs j hd fun hmem => ?_
        rw [hps, mem_singleton] at hmem
        exact (mem_sdiff.1 hj).2 (hmem ▸ (cls_part θ j).2)
      · exact Or.inr (hnon j hd)
    · refine hnon j (hinp j fun hjO => hjK (mem_sdiff.2 ⟨hjO, hjP⟩))

/-- **Lemma G' for partitions of `univ`.** For any one-sided data satisfying the W10 hypotheses,
every partition has `E > 0` unless its profile is a union of full cuts. -/
theorem kE_profile {lam : Fin N → Finset (Fin N) → ℝ} {lmin a : ℝ} {eps : ℕ → ℝ} {D dstar : ℕ}
    (h : KeyHyp lam lmin a eps D dstar) (hN : 2 ≤ N) :
    0 < kE lam lmin (profile θ) ∨ ∀ j, profile θ j = ∅ ∨ profile θ j = univ.erase j :=
  kE_key h hN (profile_not_self θ) (profile_shape θ h.hD)

end Census
end IIT
