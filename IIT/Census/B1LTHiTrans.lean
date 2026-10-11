/-
Census, B1 LTBetaHi, module T1: the transversal design of triples (W2 §5.2).

For pairwise disjoint `A, B, C` of size `m` (indexed increasingly), `trTriple x y = {a_x, b_y, c_{x+y}}` (`Fin m`
addition, i.e. mod `m`). Any two units from different parts determine the third, so two distinct members share at
most one unit; the family has `m²` members.
-/
import IIT.Census.B1LT2Final

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

section Trans

variable {m : ℕ} {A B C : Finset (Fin N)} (hA : A.card = m) (hB : B.card = m) (hC : C.card = m)

/-- The member indexed by `(x, y)`. -/
def trTriple (x y : Fin m) : Finset (Fin N) :=
  {A.orderEmbOfFin hA x, B.orderEmbOfFin hB y, C.orderEmbOfFin hC (x + y)}

/-- The family. -/
def trFamily : Finset (Finset (Fin N)) :=
  (univ : Finset (Fin m × Fin m)).image fun p => trTriple hA hB hC p.1 p.2

variable {hA hB hC}

lemma trA_mem (x : Fin m) : A.orderEmbOfFin hA x ∈ A := orderEmbOfFin_mem A hA x
lemma trB_mem (y : Fin m) : B.orderEmbOfFin hB y ∈ B := orderEmbOfFin_mem B hB y
lemma trC_mem (z : Fin m) : C.orderEmbOfFin hC z ∈ C := orderEmbOfFin_mem C hC z

/-- **Two members sharing two units are equal** (for pairwise disjoint parts). -/
theorem trTriple_two (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) {x y x' y' : Fin m}
    (h2 : 2 ≤ (trTriple hA hB hC x y ∩ trTriple hA hB hC x' y').card) : (x, y) = (x', y') := by
  classical
  set a := A.orderEmbOfFin hA
  set b := B.orderEmbOfFin hB
  set c := C.orderEmbOfFin hC
  -- a unit of the intersection lies in one part, and there it pins the index
  have hai : ∀ {u v}, a u = a v → u = v := fun h => a.injective h
  have hbi : ∀ {u v}, b u = b v → u = v := fun h => b.injective h
  have hci : ∀ {u v}, c u = c v → u = v := fun h => c.injective h
  have nAB : ∀ u v, a u ≠ b v := fun u v h =>
    Finset.disjoint_left.1 hAB (trA_mem u) (h ▸ trB_mem v)
  have nAC : ∀ u v, a u ≠ c v := fun u v h =>
    Finset.disjoint_left.1 hAC (trA_mem u) (h ▸ trC_mem v)
  have nBC : ∀ u v, b u ≠ c v := fun u v h =>
    Finset.disjoint_left.1 hBC (trB_mem u) (h ▸ trC_mem v)
  -- the intersection is contained in {a x | x = x'} ∪ {b y | y = y'} ∪ {c (x+y) | x+y = x'+y'}
  have hsub : trTriple hA hB hC x y ∩ trTriple hA hB hC x' y' ⊆
      (if x = x' then {a x} else ∅) ∪ (if y = y' then {b y} else ∅) ∪
        (if x + y = x' + y' then {c (x + y)} else ∅) := by
    intro j hj
    simp only [trTriple, mem_inter, mem_insert, mem_singleton] at hj
    obtain ⟨h1, h2⟩ := hj
    simp only [mem_union]
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with h | h | h
    · left; left; rw [if_pos (hai h)]; exact mem_singleton_self _
    · exact absurd h (nAB _ _)
    · exact absurd h (nAC _ _)
    · exact absurd h.symm (nAB _ _)
    · left; right; rw [if_pos (hbi h)]; exact mem_singleton_self _
    · exact absurd h (nBC _ _)
    · exact absurd h.symm (nAC _ _)
    · exact absurd h.symm (nBC _ _)
    · right; rw [if_pos (hci h)]; exact mem_singleton_self _
  have hc := (card_le_card hsub).trans ((card_union_le _ _).trans (add_le_add (card_union_le _ _) le_rfl))
  have k1 : (if x = x' then ({a x} : Finset (Fin N)) else ∅).card = if x = x' then 1 else 0 := by split_ifs <;> simp
  have k2 : (if y = y' then ({b y} : Finset (Fin N)) else ∅).card = if y = y' then 1 else 0 := by split_ifs <;> simp
  have k3 : (if x + y = x' + y' then ({c (x + y)} : Finset (Fin N)) else ∅).card =
      if x + y = x' + y' then 1 else 0 := by split_ifs <;> simp
  rw [k1, k2, k3] at hc
  have h3 : 2 ≤ (if x = x' then 1 else 0) + (if y = y' then 1 else 0) + (if x + y = x' + y' then 1 else 0) := by
    omega
  split_ifs at h3 with hx hy hs hs hy hs hs <;> (try omega)
  all_goals first
    | exact Prod.ext hx hy
    | exact Prod.ext hx (add_left_cancel (hx ▸ hs))
    | exact Prod.ext (add_right_cancel (hy ▸ hs)) hy

/-- **The family has `m²` members.** -/
theorem trFamily_card (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (hm : 3 ≤ m) :
    (trFamily hA hB hC).card = m * m := by
  classical
  unfold trFamily
  rw [card_image_of_injective _ fun p q h => ?_]
  · rw [card_univ, Fintype.card_prod, Fintype.card_fin]
  · have hcard : (trTriple hA hB hC p.1 p.2 ∩ trTriple hA hB hC q.1 q.2).card = 3 := by
      rw [h, inter_self]
      unfold trTriple
      rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp only [mem_singleton]; intro h'
        exact Finset.disjoint_left.1 hBC (trB_mem (hB := hB) q.2) (h' ▸ trC_mem (hC := hC) _)
      · simp only [mem_insert, mem_singleton, not_or]
        exact ⟨fun h' => Finset.disjoint_left.1 hAB (trA_mem (hA := hA) q.1) (h' ▸ trB_mem (hB := hB) _),
          fun h' => Finset.disjoint_left.1 hAC (trA_mem (hA := hA) q.1) (h' ▸ trC_mem (hC := hC) _)⟩
    have := trTriple_two hAB hAC hBC (x := p.1) (y := p.2) (x' := q.1) (y' := q.2) (by omega)
    exact this

/-- **Two distinct members share at most one unit.** -/
theorem trFamily_inter (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) {S S' : Finset (Fin N)}
    (hS : S ∈ trFamily hA hB hC) (hS' : S' ∈ trFamily hA hB hC) (hne : S ≠ S') : (S ∩ S').card ≤ 1 := by
  classical
  obtain ⟨p, -, rfl⟩ := mem_image.1 hS
  obtain ⟨q, -, rfl⟩ := mem_image.1 hS'
  by_contra h
  push_neg at h
  have := trTriple_two hAB hAC hBC (x := p.1) (y := p.2) (x' := q.1) (y' := q.2) (by omega)
  exact hne (by rw [show p = q from this])

end Trans

end Census
end IIT
