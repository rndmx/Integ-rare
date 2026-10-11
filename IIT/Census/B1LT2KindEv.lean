/-
Census, B1 lemma LT2, module M6d-3d: the event of each kind, and its probability.

For a valid kind `k` (and fixed `a₀ ∈ D₁`, `b₀ ∈ D₂`):
* pair kinds (`aIn ∧ bIn`): `{m₁ ≤ #{p ∈ D₁×D₂ : κσ ≤ |stat_k(p)|}}`;
* unit-`a` kinds (`¬ bIn`): `{m₃ ≤ #{a ∈ D₁ : κσ ≤ |stat_k(a, b₀)|}}`;
* unit-`b` kinds (`¬ aIn`, `bIn`): `{m₃ ≤ #{b ∈ D₂ : κσ ≤ |stat_k(a₀, b)|}}`.
`lt2_kindEv_prob`: each has probability `≤ 2 e^{-3N}` under the threshold hypotheses.
-/
import IIT.Census.B1LT2KindClass

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- `R ∩ Λ` has odd size for the shifted statistics of a valid kind. -/
lemma lt2_odd_RLam {a b : Fin N} (ha : a ∈ lt2D1 N) (hb : b ∈ lt2D2 N) {ra rb : Bool}
    (hR : ra = true ∨ rb = true) : ((lt2sub a b ra rb) ∩ lt2Lam ra rb).card % 2 = 1 := by
  classical
  have hab := lt2_D1_ne_D2 ha hb
  have hbD1 : b ∉ lt2D1 N := fun h => lt2_D_disj h hb
  have haD2 : a ∉ lt2D2 N := fun h => lt2_D_disj ha h
  cases ra <;> cases rb <;> simp only [Bool.false_eq_true, false_or, or_true, or_false] at hR
  · -- `R = {b}`, `Λ = D₂`
    have : lt2sub a b false true ∩ lt2Lam false true = {b} := by
      ext j; simp only [lt2sub, lt2Lam, mem_inter, mem_union, mem_singleton]; simp
      intro h; subst h; exact hb
    rw [this]; rfl
  · -- `R = {a}`, `Λ = D₁`
    have : lt2sub a b true false ∩ lt2Lam true false = {a} := by
      ext j; simp only [lt2sub, lt2Lam, mem_inter, mem_union, mem_singleton]; simp
      intro h; subst h; exact ha
    rw [this]; rfl
  · -- `R = {a,b}`, `Λ = D₂`
    have : lt2sub a b true true ∩ lt2Lam true true = {b} := by
      ext j; simp only [lt2sub, lt2Lam, mem_inter, mem_union, mem_singleton]; simp
      constructor
      · rintro ⟨h | h, hj⟩
        · subst h; exact absurd hj haD2
        · exact h
      · intro h; subst h; exact ⟨Or.inr rfl, hb⟩
    rw [this]; rfl

lemma lt2_card_sub_le (a b : Fin N) (x y : Bool) : (lt2sub a b x y).card ≤ 2 := by
  unfold lt2sub
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : (if x then ({a} : Finset (Fin N)) else ∅).card ≤ 1 := by split_ifs <;> simp
  have h2 : (if y then ({b} : Finset (Fin N)) else ∅).card ≤ 1 := by split_ifs <;> simp
  omega

/-- The symmetric difference of two small `T`'s is not a class functional of size `≥ 5`. -/
lemma lt2_symmDiff_ne_Lam {T T' Λ : Finset (Fin N)} (hT : T.card ≤ 2) (hT' : T'.card ≤ 2) (hΛ : 5 ≤ Λ.card) :
    symmDiff T T' ≠ Λ := by
  intro h
  have : (symmDiff T T').card ≤ 4 := by
    have hsub : symmDiff T T' ⊆ T ∪ T' := by
      intro x hx; rw [Finset.mem_symmDiff] at hx; rw [mem_union]; tauto
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le T T')
    omega
  rw [h] at this; omega

lemma lt2_card_Lam (ra rb : Bool) : (lt2Lam ra rb : Finset (Fin N)).card = lt2m N := by
  unfold lt2Lam; split_ifs
  · exact lt2_card_D1
  · exact lt2_card_D2

lemma lt2stat_st0 (w : Param N) (a b : Fin N) {k : LT2Kind} (h : k.1 = 0) :
    lt2stat w a b k = lt2mT w (lt2sub a b k.2.2.2.2.2.1 k.2.2.2.2.2.2) := by
  unfold lt2stat; rw [if_pos h]

lemma lt2stat_st1 (w : Param N) (a b : Fin N) {k : LT2Kind} (h : k.1 = 1) :
    lt2stat w a b k = lt2Ot w (lt2col a b k.2.1, lt2sub a b k.2.2.2.2.2.1 k.2.2.2.2.2.2) := by
  unfold lt2stat; rw [if_neg (by rw [h]; decide), if_pos h]

lemma lt2stat_st2 (w : Param N) (a b : Fin N) {k : LT2Kind} (h : k.1 = 2) :
    lt2stat w a b k = lt2N0 (lt2Lam k.2.2.2.1 k.2.2.2.2.1) k.2.2.1 w
      (lt2col a b k.2.1, lt2sub a b k.2.2.2.1 k.2.2.2.2.1, lt2sub a b k.2.2.2.2.2.1 k.2.2.2.2.2.2) := by
  unfold lt2stat; rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide)]

/-- The hypotheses shared by all kinds at size `N`. -/
structure LT2KindHyp (N : ℕ) (m' : ℕ) (P : ℕ) : Prop where
  ev : 3 * (N : ℝ) + (N : ℝ) ^ 2 * 12 ≤ lt2κ * sigN N / (4 * lt2θ N)
  hN : 8 * (1 / 2 : ℝ) ^ N ≤ lt2tG N
  hN1 : (1 : ℝ) ≤ N
  extra : ∀ d m : ℕ, d ≤ N ^ 2 →
    ((d.choose m : ℕ) : ℝ) * 2 ^ m * (lt2B2 N + (d : ℝ) ^ 2 * lt2Bpair N) ≤ Real.exp (-(3 * (N : ℝ)))
  m5 : 5 ≤ lt2m N
  m1 : 1 ≤ m'
  hPm : (P : ℝ) ≤ 12288 * m'
  hmN : (N : ℝ) / 491520 ≤ m'
  hmN2 : (m' : ℝ) ≤ (N : ℝ) ^ 2
  hPN : P ≤ N ^ 2

/-- **A generic kind bound**: index set `P`, each index `p` giving the pair `pr p ∈ D₁ × D₂`, and the support of the
kind's index at `pr p` determining `p`. -/
theorem lt2_kind_prob {α : Type*} (P : Finset α) (pr : α → Fin N × Fin N)
    (hpr : ∀ p ∈ P, (pr p).1 ∈ lt2D1 N ∧ (pr p).2 ∈ lt2D2 N) {k : LT2Kind} (hk : lt2kValid k)
    (hsupp : ∀ p ∈ P, ∀ p' ∈ P, (∀ j, ((j = (pr p).1 ∧ lt2aIn k) ∨ (j = (pr p).2 ∧ lt2bIn k)) ↔
      ((j = (pr p').1 ∧ lt2aIn k) ∨ (j = (pr p').2 ∧ lt2bIn k))) → p = p')
    {m' : ℕ} (H : LT2KindHyp N m' P.card) :
    cubeM N {w | m' ≤ (P.filter fun p => lt2κ * sigN N ≤ |lt2stat w (pr p).1 (pr p).2 k|).card} ≤
      ENNReal.ofReal (2 * Real.exp (-(3 * (N : ℝ)))) := by
  have he : ENNReal.ofReal (Real.exp (-(3 * (N : ℝ)))) ≤ ENNReal.ofReal (2 * Real.exp (-(3 * (N : ℝ)))) :=
    ENNReal.ofReal_le_ofReal (by linarith [Real.exp_pos (-(3 * (N : ℝ)))])
  have hab : ∀ p ∈ P, (pr p).1 ≠ (pr p).2 := fun p hp => lt2_D1_ne_D2 (hpr p hp).1 (hpr p hp).2
  -- injectivity from the support characterization
  have hinj : ∀ {β : Type} (g : α → β) (S : β → Finset (Fin N)),
      (∀ p ∈ P, ∀ j, j ∈ S (g p) ↔ ((j = (pr p).1 ∧ lt2aIn k) ∨ (j = (pr p).2 ∧ lt2bIn k))) →
      Set.InjOn g P := by
    intro β g S hS p hp p' hp' h
    exact hsupp p hp p' hp' fun j => (hS p hp j).symm.trans (h ▸ hS p' hp' j)
  have hTne : ∀ p ∈ P, (lt2sub (pr p).1 (pr p).2 k.2.2.2.2.2.1 k.2.2.2.2.2.2).Nonempty := fun p _ =>
    (lt2_sub_nonempty_iff _ _).2 hk.1
  obtain ⟨st, ci, β, ra, rb, ta, tb⟩ := k
  fin_cases st
  · -- weights
    have hset : ∀ w : Param N, (P.filter fun p => lt2κ * sigN N ≤
        |lt2stat w (pr p).1 (pr p).2 (0, ci, β, ra, rb, ta, tb)|) =
        P.filter fun p => lt2κ * sigN N ≤ |lt2mT w (lt2sub (pr p).1 (pr p).2 ta tb)| := fun w => by
      exact Finset.filter_congr fun p _ => by rw [lt2stat_st0 w _ _ rfl]
    refine (measure_mono fun w hw => ?_).trans ((lt2_kind_mT H.ev P (fun p => lt2sub (pr p).1 (pr p).2 ta tb)
      (hinj _ lt2S0 fun p hp j => ((lt2_supp_mem (hab p hp) (0, ci, β, ra, rb, ta, tb) j).1 rfl))
      hTne H.m1 H.hPm H.hmN H.hmN2).trans he)
    simp only [Set.mem_setOf_eq] at hw ⊢; exact le_of_le_of_eq hw (congrArg Finset.card (hset w))
  · -- own entries
    have hset : ∀ w : Param N, (P.filter fun p => lt2κ * sigN N ≤
        |lt2stat w (pr p).1 (pr p).2 (1, ci, β, ra, rb, ta, tb)|) =
        P.filter fun p => lt2κ * sigN N ≤ |lt2Ot w (lt2col (pr p).1 (pr p).2 ci, lt2sub (pr p).1 (pr p).2 ta tb)| :=
      fun w => Finset.filter_congr fun p _ => by rw [lt2stat_st1 w _ _ rfl]
    refine (measure_mono fun w hw => ?_).trans ((lt2_kind_Ot H.ev P (fun p => (lt2col (pr p).1 (pr p).2 ci, lt2sub (pr p).1 (pr p).2 ta tb))
      (hinj _ lt2S1 fun p hp j => ((lt2_supp_mem (hab p hp) (1, ci, β, ra, rb, ta, tb) j).2.1 rfl))
      hTne H.m1 H.hPm H.hmN H.hmN2).trans he)
    simp only [Set.mem_setOf_eq] at hw ⊢; exact le_of_le_of_eq hw (congrArg Finset.card (hset w))
  · -- shifted entries
    have hset : ∀ w : Param N, (P.filter fun p => lt2κ * sigN N ≤
        |lt2stat w (pr p).1 (pr p).2 (2, ci, β, ra, rb, ta, tb)|) =
        P.filter fun p => lt2κ * sigN N ≤ |lt2N0 (lt2Lam ra rb) β w
          (lt2col (pr p).1 (pr p).2 ci, lt2sub (pr p).1 (pr p).2 ra rb, lt2sub (pr p).1 (pr p).2 ta tb)| :=
      fun w => Finset.filter_congr fun p _ => by rw [lt2stat_st2 w _ _ rfl]
    have hR : ra = true ∨ rb = true := hk.2 rfl
    refine (measure_mono fun w hw => ?_).trans (lt2_kind_N0 (b := β) H.ev H.hN H.hN1 H.extra (lt2Lam ra rb) P
      (fun p => (lt2col (pr p).1 (pr p).2 ci, lt2sub (pr p).1 (pr p).2 ra rb, lt2sub (pr p).1 (pr p).2 ta tb))
      (hinj _ lt2S2 fun p hp j => ((lt2_supp_mem (hab p hp) (2, ci, β, ra, rb, ta, tb) j).2.2 rfl))
      (fun p hp => lt2_odd_RLam (hpr p hp).1 (hpr p hp).2 hR)
      (fun p _ p' _ _ => lt2_symmDiff_ne_Lam (lt2_card_sub_le _ _ _ _) (lt2_card_sub_le _ _ _ _)
        (by rw [lt2_card_Lam]; exact H.m5))
      H.m1 H.hPm H.hmN H.hmN2 H.hPN)
    simp only [Set.mem_setOf_eq] at hw ⊢; exact le_of_le_of_eq hw (congrArg Finset.card (hset w))

end Census
end IIT
