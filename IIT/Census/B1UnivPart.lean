/-
Census, B1 lower bound, leaf `phi_univ_ge_EX` (W7 §3 item 3, check V): the comparison partition.

For a unit `x` and a set `P ∌ x`, `uxTheta x P` is the partition of `univ` with blocks
`{x}` (direction `↔`), `P` (direction `→`, if nonempty) and the singletons `{j}` of the remaining
units (direction `←`).  Its profile is: `C_x = U \ {x}`, `C_j = {x}` for `j ∈ P`, `C_j = U \ {j}`
for the remaining `j` (a Shape-2b member of `𝓕_x`).
-/
import IIT.Census.Profile

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- The blocks of the comparison partition. -/
def uxParts (x : Fin N) (P : Finset (Fin N)) : Finset (Finset (Fin N)) :=
  (insert {x} (insert P ((univ \ insert x P).image fun j => ({j} : Finset (Fin N))))).filter
    Finset.Nonempty

/-- The directions of the comparison partition. -/
def uxDir (x : Fin N) (P : Finset (Fin N)) (p : Finset (Fin N)) : Dir :=
  if p = {x} then Dir.both else if p = P then Dir.outputs else Dir.inputs

lemma mem_uxParts {x : Fin N} {P p : Finset (Fin N)} :
    p ∈ uxParts x P ↔ (p = {x} ∨ (p = P ∧ P.Nonempty) ∨ ∃ j, j ≠ x ∧ j ∉ P ∧ p = {j}) := by
  unfold uxParts
  simp only [mem_filter, mem_insert, mem_image, mem_sdiff, mem_univ, true_and, not_or]
  constructor
  · rintro ⟨h | h | ⟨j, ⟨hjx, hjP⟩, rfl⟩, hne⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h, h ▸ hne⟩)
    · exact Or.inr (Or.inr ⟨j, hjx, hjP, rfl⟩)
  · rintro (h | ⟨h, hne⟩ | ⟨j, hjx, hjP, rfl⟩)
    · exact ⟨Or.inl h, h ▸ singleton_nonempty x⟩
    · exact ⟨Or.inr (Or.inl h), h ▸ hne⟩
    · exact ⟨Or.inr (Or.inr ⟨j, ⟨hjx, hjP⟩, rfl⟩), singleton_nonempty j⟩

/-- **The comparison partition.** -/
def uxTheta (x : Fin N) (P : Finset (Fin N)) (hxP : x ∉ P) (hN : 2 ≤ N) : SysPartition N univ where
  parts := uxParts x P
  dir := uxDir x P
  parts_nonempty := fun p hp => (mem_filter.1 hp).2
  parts_subset := fun p _ => subset_univ p
  parts_disjoint := by
    intro p hp q hq hpq
    rw [mem_uxParts] at hp hq
    rcases hp with rfl | ⟨rfl, -⟩ | ⟨j, hjx, hjP, rfl⟩ <;>
      rcases hq with rfl | ⟨rfl, -⟩ | ⟨j', hjx', hjP', rfl⟩
    · exact absurd rfl hpq
    · exact disjoint_singleton_left.2 hxP
    · exact disjoint_singleton.2 (Ne.symm hjx')
    · exact disjoint_singleton_right.2 hxP
    · exact absurd rfl hpq
    · exact disjoint_singleton_right.2 hjP'
    · exact disjoint_singleton.2 hjx
    · exact disjoint_singleton_left.2 hjP
    · exact disjoint_singleton.2 fun h => hpq (by rw [h])
  parts_cover := by
    intro i _
    by_cases hix : i = x
    · exact ⟨{x}, mem_uxParts.2 (Or.inl rfl), by rw [hix]; exact mem_singleton_self x⟩
    · by_cases hiP : i ∈ P
      · exact ⟨P, mem_uxParts.2 (Or.inr (Or.inl ⟨rfl, ⟨i, hiP⟩⟩)), hiP⟩
      · exact ⟨{i}, mem_uxParts.2 (Or.inr (Or.inr ⟨i, hix, hiP, rfl⟩)), mem_singleton_self i⟩
  two_le := by
    obtain ⟨j, hj⟩ : ∃ j : Fin N, j ≠ x := by
      by_cases h : x.1 = 0
      · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
      · exact ⟨⟨0, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
    have hx : {x} ∈ uxParts x P := mem_uxParts.2 (Or.inl rfl)
    have hq : ∃ q ∈ uxParts x P, q ≠ {x} := by
      by_cases hjP : j ∈ P
      · refine ⟨P, mem_uxParts.2 (Or.inr (Or.inl ⟨rfl, ⟨j, hjP⟩⟩)), fun e => hxP ?_⟩
        rw [e]; exact mem_singleton_self x
      · exact ⟨{j}, mem_uxParts.2 (Or.inr (Or.inr ⟨j, hj, hjP, rfl⟩)),
          fun e => hj (singleton_injective e)⟩
    obtain ⟨q, hq, hqx⟩ := hq
    exact one_lt_card.2 ⟨{x}, hx, q, hq, Ne.symm hqx⟩

variable {x : Fin N} {P : Finset (Fin N)} {hxP : x ∉ P} {hN : 2 ≤ N}

lemma uxTheta_profile_x : profile (uxTheta x P hxP hN) x = univ.erase x := by
  have hp : (uxTheta x P hxP hN).partOf x = {x} :=
    (uxTheta x P hxP hN).partOf_eq (mem_uxParts.2 (Or.inl rfl)) (mem_singleton_self x)
  unfold profile
  rw [hp, SysPartition.cutSet]
  show (match uxDir x P {x} with
    | Dir.inputs => univ \ {x} | Dir.both => univ \ {x}
    | Dir.outputs => _) = _
  rw [show uxDir x P {x} = Dir.both by simp [uxDir]]
  ext; simp

lemma uxTheta_profile_P {j : Fin N} (hj : j ∈ P) : profile (uxTheta x P hxP hN) j = {x} := by
  have hPx : P ≠ {x} := fun e => hxP (by rw [e]; exact mem_singleton_self x)
  have hp : (uxTheta x P hxP hN).partOf j = P :=
    (uxTheta x P hxP hN).partOf_eq (mem_uxParts.2 (Or.inr (Or.inl ⟨rfl, ⟨j, hj⟩⟩))) hj
  unfold profile
  rw [hp, SysPartition.cutSet]
  have hd : (uxTheta x P hxP hN).dir P = Dir.outputs := by
    show uxDir x P P = Dir.outputs
    simp [uxDir, hPx]
  rw [hd]
  have hfil : ((uxTheta x P hxP hN).parts.filter fun q => q ≠ P ∧
      ((uxTheta x P hxP hN).dir q = Dir.outputs ∨ (uxTheta x P hxP hN).dir q = Dir.both)) = {{x}} := by
    ext q
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨-, hqP, hdq⟩
      change uxDir x P q = Dir.outputs ∨ uxDir x P q = Dir.both at hdq
      unfold uxDir at hdq
      by_contra hqx
      rw [if_neg hqx, if_neg hqP] at hdq
      rcases hdq with h | h <;> cases h
    · rintro rfl
      refine ⟨mem_uxParts.2 (Or.inl rfl), Ne.symm hPx, Or.inr ?_⟩
      show uxDir x P {x} = Dir.both
      simp [uxDir]
  rw [hfil, sup_singleton, id]

lemma uxTheta_profile_R {j : Fin N} (hjx : j ≠ x) (hjP : j ∉ P) :
    profile (uxTheta x P hxP hN) j = univ.erase j := by
  have hp : (uxTheta x P hxP hN).partOf j = {j} :=
    (uxTheta x P hxP hN).partOf_eq (mem_uxParts.2 (Or.inr (Or.inr ⟨j, hjx, hjP, rfl⟩)))
      (mem_singleton_self j)
  unfold profile
  rw [hp, SysPartition.cutSet]
  have hd : (uxTheta x P hxP hN).dir {j} = Dir.inputs := by
    show uxDir x P {j} = Dir.inputs
    have h1 : ({j} : Finset (Fin N)) ≠ {x} := fun e => hjx (singleton_injective e)
    have h2 : ({j} : Finset (Fin N)) ≠ P := fun e => hjP (by rw [← e]; exact mem_singleton_self j)
    simp [uxDir, h1, h2]
  rw [hd]
  ext; simp

end Census
end IIT
