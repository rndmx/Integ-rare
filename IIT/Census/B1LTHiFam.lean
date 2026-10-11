/-
Census, B1 LTBetaHi, module T2: **the family of a class `Q`** (W2 6.1(d)).

`Q` listed increasingly is cut into three consecutive blocks `A, B, C` of size `m = |Q|/3`; `qFam Q` is the
transversal design `trFamily` on them: members inside `Q`, of size `≤ 3`, pairwise sharing `≤ 1` unit, `m²` of them.
-/
import IIT.Census.B1LTHiTrans

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- `|Q|/3`. -/
def qM (Q : Finset (Fin N)) : ℕ := Q.card / 3

/-- The `t`-th block (`t ≤ 2`) of `Q`, as an embedding of `Fin m`. -/
def qEmb (Q : Finset (Fin N)) (t : Fin 3) : Fin (qM Q) ↪ Fin N where
  toFun x := Q.orderEmbOfFin rfl ⟨t.val * qM Q + x.val, by
    have hx := x.isLt
    have h1 : t.val * qM Q ≤ 2 * qM Q := Nat.mul_le_mul_right _ (by omega)
    have h3 : 3 * qM Q ≤ Q.card := by unfold qM; omega
    omega⟩
  inj' x y h := by
    have := (Q.orderEmbOfFin rfl).injective h
    simp only [Fin.mk.injEq] at this
    exact Fin.ext (by omega)

lemma qEmb_mem (Q : Finset (Fin N)) (t : Fin 3) (x : Fin (qM Q)) : qEmb Q t x ∈ Q :=
  orderEmbOfFin_mem Q rfl _

lemma qEmb_ne (Q : Finset (Fin N)) {t t' : Fin 3} (htt : t ≠ t') (x y : Fin (qM Q)) : qEmb Q t x ≠ qEmb Q t' y := by
  intro h
  have := (Q.orderEmbOfFin rfl).injective h
  simp only [Fin.mk.injEq] at this
  have hx := x.isLt; have hy := y.isLt
  apply htt
  rcases t with ⟨t, ht⟩; rcases t' with ⟨t', ht'⟩
  simp only [Fin.mk.injEq]
  rcases Nat.lt_or_ge t t' with h1 | h1
  · exfalso
    have : (t + 1) * qM Q ≤ t' * qM Q := Nat.mul_le_mul_right _ h1
    nlinarith
  · rcases Nat.lt_or_ge t' t with h2 | h2
    · exfalso
      have : (t' + 1) * qM Q ≤ t * qM Q := Nat.mul_le_mul_right _ h2
      nlinarith
    · omega

/-- The blocks. -/
def qPart (Q : Finset (Fin N)) (t : Fin 3) : Finset (Fin N) := (univ : Finset (Fin (qM Q))).map (qEmb Q t)

lemma qPart_card (Q : Finset (Fin N)) (t : Fin 3) : (qPart Q t).card = qM Q := by
  simp [qPart]

lemma qPart_sub (Q : Finset (Fin N)) (t : Fin 3) : qPart Q t ⊆ Q := by
  intro j hj
  obtain ⟨x, -, rfl⟩ := mem_map.1 hj
  exact qEmb_mem Q t x

lemma qPart_disj (Q : Finset (Fin N)) {t t' : Fin 3} (h : t ≠ t') : Disjoint (qPart Q t) (qPart Q t') := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  obtain ⟨x, -, rfl⟩ := mem_map.1 hj
  obtain ⟨y, -, hy⟩ := mem_map.1 hj'
  exact qEmb_ne Q h x y hy.symm

/-- **The family of `Q`.** -/
def qFam (Q : Finset (Fin N)) : Finset (Finset (Fin N)) :=
  trFamily (qPart_card Q 0) (qPart_card Q 1) (qPart_card Q 2)

lemma qFam_sub {Q S : Finset (Fin N)} (hS : S ∈ qFam Q) : S ⊆ Q := by
  obtain ⟨p, -, rfl⟩ := mem_image.1 hS
  intro j hj
  simp only [trTriple, mem_insert, mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  · exact qPart_sub Q 0 (orderEmbOfFin_mem _ _ _)
  · exact qPart_sub Q 1 (orderEmbOfFin_mem _ _ _)
  · exact qPart_sub Q 2 (orderEmbOfFin_mem _ _ _)

lemma qFam_card_le {Q S : Finset (Fin N)} (hS : S ∈ qFam Q) : S.card ≤ 3 := by
  obtain ⟨p, -, rfl⟩ := mem_image.1 hS
  unfold trTriple
  exact (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans (by simp)))

lemma qFam_inter {Q S S' : Finset (Fin N)} (hS : S ∈ qFam Q) (hS' : S' ∈ qFam Q) (hne : S ≠ S') :
    (S ∩ S').card ≤ 1 :=
  trFamily_inter (qPart_disj Q (by decide)) (qPart_disj Q (by decide)) (qPart_disj Q (by decide)) hS hS' hne

lemma qFam_card {Q : Finset (Fin N)} (hm : 3 ≤ qM Q) : (qFam Q).card = qM Q * qM Q :=
  trFamily_card (qPart_disj Q (by decide)) (qPart_disj Q (by decide)) (qPart_disj Q (by decide)) hm

end Census
end IIT
