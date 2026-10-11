/-
Census, B1 LTBetaHi, module T2: **private positions are disjoint across the family** (W2 §5.3).

`flipS r R` flips the units of `R` in `r`. Inside an agreement class `Q` (every special row differs from `tc` on none
or all of `Q`), with `|Q| ≥ 7` and members of size `≤ 3` inside `Q`:
(i) `flipS r R = flipS r' R'` forces `r = r'` and `R = R'` (blocks of different heavy rows never share a row);
(ii) a position `(flipS r R, i)` lying in the blocks of two members `S ≠ S'` (two members share `≤ 1` unit) has
`R ⊆ {i}`: it is the row itself or its own-column flip — a shared position, never a private one.
-/
import IIT.Census.B1LT2Heavy

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- Flip the units of `R`. -/
def flipS (r : State N) (R : Finset (Fin N)) : State N := fun j => if j ∈ R then !r j else r j

lemma flipS_eq_iff {r r' : State N} {R R' : Finset (Fin N)} (h : flipS r R = flipS r' R') (j : Fin N) :
    r j ≠ r' j ↔ (j ∈ R ↔ j ∉ R') := by
  have hj := congrFun h j
  simp only [flipS] at hj
  by_cases hR : j ∈ R <;> by_cases hR' : j ∈ R' <;> cases hr : r j <;> cases hr' : r' j <;> simp_all

/-- **(i) Blocks of different rows in an agreement class never share a row.** -/
theorem flipS_inj_agree {Q R R' : Finset (Fin N)} {r r' : State N} (hQ : 7 ≤ Q.card)
    (hRQ : R ⊆ Q) (hR'Q : R' ⊆ Q) (hR : R.card ≤ 3) (hR' : R'.card ≤ 3)
    (hag : (∀ j ∈ Q, r j = r' j) ∨ (∀ j ∈ Q, r j ≠ r' j)) (h : flipS r R = flipS r' R') :
    r = r' ∧ R = R' := by
  classical
  have key := flipS_eq_iff h
  have hdiff : univ.filter (fun j => r j ≠ r' j) ⊆ R ∪ R' := by
    intro j hj
    have := (key j).1 (mem_filter.1 hj).2
    by_cases hjR : j ∈ R
    · exact mem_union_left _ hjR
    · exact mem_union_right _ (by by_contra hn; exact hjR (this.2 hn))
  have hcard : (univ.filter fun j => r j ≠ r' j).card ≤ 6 :=
    (card_le_card hdiff).trans ((card_union_le _ _).trans (by omega))
  have hsame : ∀ j, r j = r' j := by
    rcases hag with hq | hq
    · intro j
      by_contra hne
      have hj : j ∈ R ∪ R' := hdiff (mem_filter.2 ⟨mem_univ _, hne⟩)
      rcases mem_union.1 hj with hj | hj
      · exact hne (hq j (hRQ hj))
      · exact hne (hq j (hR'Q hj))
    · exfalso
      have : Q ⊆ univ.filter fun j => r j ≠ r' j := fun j hj => mem_filter.2 ⟨mem_univ _, hq j hj⟩
      have := card_le_card this
      omega
  refine ⟨funext hsame, ?_⟩
  ext j
  have := key j
  have hn : ¬ (r j ≠ r' j) := fun h => h (hsame j)
  rw [iff_false_left hn] at this
  tauto

/-- **(ii) A position shared by the blocks of two members is the row itself or its own-column flip.** -/
theorem shared_pos_sub {S S' R : Finset (Fin N)} {i : Fin N} (hS : (S ∩ S').card ≤ 1)
    (hRS : R ⊆ S) (hRS' : R ⊆ S') (hi : i ∈ S) (hi' : i ∈ S') : R ⊆ {i} := by
  classical
  intro j hj
  have hjI : j ∈ S ∩ S' := mem_inter.2 ⟨hRS hj, hRS' hj⟩
  have hiI : i ∈ S ∩ S' := mem_inter.2 ⟨hi, hi'⟩
  by_contra hne
  have hne' : j ≠ i := fun e => hne (mem_singleton.2 e)
  have : ({j, i} : Finset (Fin N)) ⊆ S ∩ S' := by
    intro x hx; rcases mem_insert.1 hx with rfl | hx
    · exact hjI
    · rw [mem_singleton.1 hx]; exact hiI
  have := card_le_card this
  rw [card_pair hne'] at this
  omega

/-- **Rows `r^R` (`|R| ≥ 2`) of different members are different** (W2 6.2(e)): members inside the agreement class
`Q` sharing `≤ 1` unit. -/
theorem flipS_member_inj {Q S S' R R' : Finset (Fin N)} {r r' : State N} (hQ : 7 ≤ Q.card)
    (hSQ : S ⊆ Q) (hS'Q : S' ⊆ Q) (hS : S.card ≤ 3) (hS' : S'.card ≤ 3)
    (hfam : S ≠ S' → (S ∩ S').card ≤ 1)
    (hRS : R ⊆ S) (hR'S' : R' ⊆ S') (hR2 : 2 ≤ R.card)
    (hag : (∀ j ∈ Q, r j = r' j) ∨ (∀ j ∈ Q, r j ≠ r' j)) (h : flipS r R = flipS r' R') :
    S = S' ∧ r = r' ∧ R = R' := by
  classical
  obtain ⟨hr, hR⟩ := flipS_inj_agree hQ (hRS.trans hSQ) (hR'S'.trans hS'Q) ((card_le_card hRS).trans hS)
    ((card_le_card hR'S').trans hS') hag h
  subst hR
  refine ⟨?_, hr, rfl⟩
  by_contra hne
  have := card_le_card (subset_inter hRS hR'S')
  have := hfam hne
  omega

end Census
end IIT
