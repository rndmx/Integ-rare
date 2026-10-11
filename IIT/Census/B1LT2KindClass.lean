/-
Census, B1 lemma LT2, module M6d-3c: classification of kinds (pair-level / unit-level) and injectivity.

`lt2aIn k`, `lt2bIn k`: whether `a`, resp. `b`, lies in the support `{col} ∪ R ∪ T` of the kind.
Pair kinds (both): the index map `(a,b) ↦ idx` is injective on `D₁ × D₂`. Unit-`a` kinds (`¬ bIn`): the statistic does
not depend on `b`, and `a ↦ idx(a,a)` is injective on `D₁`; symmetrically for unit-`b` kinds.
-/
import IIT.Census.B1LT2KindProb

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

def lt2aIn (k : LT2Kind) : Prop :=
  k.2.2.2.2.2.1 = true ∨ (k.1 ≠ 0 ∧ k.2.1 = false) ∨ (k.1 = 2 ∧ k.2.2.2.1 = true)

def lt2bIn (k : LT2Kind) : Prop :=
  k.2.2.2.2.2.2 = true ∨ (k.1 ≠ 0 ∧ k.2.1 = true) ∨ (k.1 = 2 ∧ k.2.2.2.2.1 = true)

instance (k : LT2Kind) : Decidable (lt2aIn k) := by unfold lt2aIn; infer_instance
instance (k : LT2Kind) : Decidable (lt2bIn k) := by unfold lt2bIn; infer_instance
instance (k : LT2Kind) : Decidable (lt2kValid k) := by unfold lt2kValid; infer_instance

lemma lt2_mem_sub {a b : Fin N} (x y : Bool) (j : Fin N) :
    j ∈ lt2sub a b x y ↔ (j = a ∧ x = true) ∨ (j = b ∧ y = true) := by
  cases x <;> cases y <;> simp [lt2sub]

lemma lt2_valid_ab {k : LT2Kind} (hk : lt2kValid k) : lt2aIn k ∨ lt2bIn k := by
  rcases hk.1 with h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)

/-- The support of an index, per statistic type. -/
def lt2S0 (T : Finset (Fin N)) : Finset (Fin N) := T
def lt2S1 (q : Fin N × Finset (Fin N)) : Finset (Fin N) := insert q.1 q.2
def lt2S2 (α : LT2Idx N) : Finset (Fin N) := insert α.1 (α.2.1 ∪ α.2.2)

lemma lt2_col_eq (a b : Fin N) (c : Bool) : lt2col a b c = if c then b else a := rfl

/-- Membership in the support of a kind's index. -/
lemma lt2_supp_mem {a b : Fin N} (hab : a ≠ b) (k : LT2Kind) (j : Fin N) :
    (k.1 = 0 → (j ∈ lt2S0 (lt2sub a b k.2.2.2.2.2.1 k.2.2.2.2.2.2) ↔
      (j = a ∧ lt2aIn k) ∨ (j = b ∧ lt2bIn k))) ∧
    (k.1 = 1 → (j ∈ lt2S1 (lt2col a b k.2.1, lt2sub a b k.2.2.2.2.2.1 k.2.2.2.2.2.2) ↔
      (j = a ∧ lt2aIn k) ∨ (j = b ∧ lt2bIn k))) ∧
    (k.1 = 2 → (j ∈ lt2S2 (lt2col a b k.2.1, lt2sub a b k.2.2.2.1 k.2.2.2.2.1,
        lt2sub a b k.2.2.2.2.2.1 k.2.2.2.2.2.2) ↔ (j = a ∧ lt2aIn k) ∨ (j = b ∧ lt2bIn k))) := by
  obtain ⟨st, ci, β, ra, rb, ta, tb⟩ := k
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => ?_⟩
  · simp only at h0; subst h0
    simp only [lt2S0, lt2_mem_sub, lt2aIn, lt2bIn, ne_eq, not_true_eq_false, false_and, or_false,
      show (0 : Fin 3) ≠ 2 by decide]
  · simp only at h1; subst h1
    simp only [lt2S1, mem_insert, lt2_mem_sub, lt2aIn, lt2bIn, lt2_col_eq,
      show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, ne_eq, not_false_eq_true, true_and,
      false_and, or_false]
    cases ci <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      by_cases hja : j = a <;> by_cases hjb : j = b <;> simp_all
  · simp only at h2; subst h2
    simp only [lt2S2, mem_insert, mem_union, lt2_mem_sub, lt2aIn, lt2bIn, lt2_col_eq,
      show (2 : Fin 3) ≠ 0 by decide, ne_eq, not_false_eq_true, true_and]
    cases ci <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      by_cases hja : j = a <;> by_cases hjb : j = b <;> simp_all <;> tauto

/-- **Injectivity from supports (pairs).** -/
lemma lt2_injOn_pairs {β : Type*} (g : Fin N × Fin N → β) (S : β → Finset (Fin N))
    (hS : ∀ p ∈ lt2D1 N ×ˢ lt2D2 N, ∀ j, j ∈ S (g p) ↔ j = p.1 ∨ j = p.2) :
    Set.InjOn g (lt2D1 N ×ˢ lt2D2 N : Finset (Fin N × Fin N)) := by
  intro p hp p' hp' h
  have hp1 := mem_product.1 hp
  have hp1' := mem_product.1 hp'
  have h1 : p.1 = p'.1 ∨ p.1 = p'.2 := (hS p' hp' p.1).1 (h ▸ (hS p hp p.1).2 (Or.inl rfl))
  have h2 : p.2 = p'.1 ∨ p.2 = p'.2 := (hS p' hp' p.2).1 (h ▸ (hS p hp p.2).2 (Or.inr rfl))
  have ha : p.1 = p'.1 := by
    rcases h1 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hp1'.2) (fun h' => lt2_D_disj hp1.1 h')
  have hb : p.2 = p'.2 := by
    rcases h2 with h2 | h2
    · exact absurd (h2 ▸ hp1'.1) (fun h' => lt2_D_disj h' hp1.2)
    · exact h2
  exact Prod.ext ha hb

/-- **Injectivity from supports (units).** -/
lemma lt2_injOn_units {β : Type*} (D : Finset (Fin N)) (g : Fin N → β) (S : β → Finset (Fin N))
    (hS : ∀ a ∈ D, ∀ j, j ∈ S (g a) ↔ j = a) : Set.InjOn g D := by
  intro a ha a' ha' h
  exact ((hS a' ha' a).1 (h ▸ (hS a ha a).2 rfl))

/-- Unit-`a` kinds do not depend on `b`. -/
lemma lt2_stat_unitA (w : Param N) (a b b' : Fin N) {k : LT2Kind} (hk : ¬ lt2bIn k) :
    lt2stat w a b k = lt2stat w a b' k := by
  obtain ⟨st, ci, β, ra, rb, ta, tb⟩ := k
  simp only [lt2bIn, not_or, not_and, ne_eq] at hk
  obtain ⟨htb, hci, hrb⟩ := hk
  have htb' : tb = false := by simpa using htb
  subst htb'
  have hs : ∀ x : Bool, lt2sub a b x false = lt2sub a b' x false := fun x => by simp [lt2sub]
  unfold lt2stat
  simp only
  split_ifs with h0 h1
  · rw [hs]
  · have hci' : ci = false := by simpa using hci h0
    subst hci'; rw [hs]; rfl
  · have hci' : ci = false := by simpa using hci h0
    have hrb' : rb = false := by
      have h2 : st = 2 := by fin_cases st <;> simp_all
      simpa using hrb h2
    subst hci'; subst hrb'; rw [hs, hs]; rfl

/-- Unit-`b` kinds do not depend on `a`. -/
lemma lt2_stat_unitB (w : Param N) (a a' b : Fin N) {k : LT2Kind} (hk : ¬ lt2aIn k) :
    lt2stat w a b k = lt2stat w a' b k := by
  obtain ⟨st, ci, β, ra, rb, ta, tb⟩ := k
  simp only [lt2aIn, not_or, not_and, ne_eq] at hk
  obtain ⟨hta, hci, hra⟩ := hk
  have hta' : ta = false := by simpa using hta
  subst hta'
  have hs : ∀ y : Bool, lt2sub a b false y = lt2sub a' b false y := fun y => by simp [lt2sub]
  unfold lt2stat
  simp only
  split_ifs with h0 h1
  · rw [hs]
  · have hci' : ci = true := by simpa using hci h0
    subst hci'; rw [hs]; rfl
  · have hci' : ci = true := by simpa using hci h0
    have hra' : ra = false := by
      have h2 : st = 2 := by fin_cases st <;> simp_all
      simpa using hra h2
    subst hci'; subst hra'; rw [hs, hs]; rfl

end Census
end IIT
