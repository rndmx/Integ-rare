/-
Tie theorem, part 1: branches, value inclusion (L0), positivity on the open cube (L1),
and the column-scaling transforms (L3).

Background = current state throughout (`u = s`).  The transforms are stated at the level of
TPMs (`BitScale T T' b c`: every `prob j · (b j)` is multiplied by `c j`), which covers the
scaling of one column and of all columns at once.
-/
import IIT.Census.PairCause

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-! ### Branches -/

/-- Cause branch `βC(S,θ,t)`: `sysPhiC` without the positive part. -/
noncomputable def BC (T : UnitTPM N) (s : State N) (S : Finset (Fin N)) (θ : SysPartition N S)
    (t : State N) : ℝ :=
  sysBackCause T S s s t * Real.logb 2 (sysCauseProb T S s s t / sysPartCauseProb T S s θ s t)

/-- Effect branch `βE(S,θ,t)`: `sysPhiE` without the positive part. -/
noncomputable def BE (T : UnitTPM N) (s : State N) (S : Finset (Fin N)) (θ : SysPartition N S)
    (t : State N) : ℝ :=
  sysEffProb T S s s t * Real.logb 2 (sysEffProb T S s s t / sysPartEffProb T S s θ s t)

/-! ### L0: `φ_s ∈ {0} ∪ Br(S)` -/

lemma sup'OrZero_cases {α : Type*} (s : Finset α) (f : α → ℝ) :
    sup'OrZero s f = 0 ∨ ∃ a ∈ s, sup'OrZero s f = f a := by
  unfold sup'OrZero
  split
  · rename_i h
    obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_sup' h f
    exact Or.inr ⟨a, ha, he⟩
  · exact Or.inl rfl

lemma pos_mul_cases (a x : ℝ) : a * pos x = 0 ∨ a * pos x = a * x := by
  unfold pos
  rcases le_total x 0 with h | h
  · left; rw [max_eq_left h, mul_zero]
  · right; rw [max_eq_right h]

lemma sysPhi_cases (T : UnitTPM N) (S : Finset (Fin N)) (s : State N) :
    sysPhi T S s s = 0 ∨
      ∃ θ t, sysPhi T S s s = BC T s S θ t ∨ sysPhi T S s s = BE T s S θ t := by
  unfold sysPhi
  rcases sup'OrZero_cases _ _ with h | ⟨p, -, hp⟩
  · exact Or.inl h
  rw [hp]
  unfold sysPhiOfState
  rcases sup'OrZero_cases _ _ with h | ⟨θ, -, hθ⟩
  · exact Or.inl h
  rw [hθ]
  unfold sysPhiAt
  rcases min_choice (sysPhiC T S s θ s p.1) (sysPhiE T S s θ s p.2) with h | h <;> rw [h]
  · unfold sysPhiC
    rcases pos_mul_cases (sysBackCause T S s s p.1) (Real.logb 2 _) with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨θ, p.1, Or.inl h'⟩
  · unfold sysPhiE
    rcases pos_mul_cases (sysEffProb T S s s p.2) (Real.logb 2 _) with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨θ, p.2, Or.inr h'⟩

/-! ### L1: positivity on the open cube -/

lemma clamp01_eq {x : ℝ} (h : x ∈ Set.Icc (0 : ℝ) 1) : clamp01 x = x := by
  unfold clamp01; rw [min_eq_right h.2, max_eq_right h.1]

lemma prob_pos {z : Param N} (hz : z ∈ openCube N) (j : Fin N) (r : State N) (b : Bool) :
    0 < (tpmOf z).prob j r b := by
  have h := hz r j
  have hc := clamp01_eq (Set.Ioo_subset_Icc_self h)
  show 0 < (if b then clamp01 (z r j) else 1 - clamp01 (z r j))
  rw [hc]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]; linarith [h.2]
  · simpa using h.1

lemma effUnit_pos {z : Param N} (hz : z ∈ openCube N) (M : Finset (Fin N)) (m : State N)
    (j : Fin N) (b : Bool) : 0 < effUnit (tpmOf z) M m j b :=
  div_pos (sum_pos (fun r _ => prob_pos hz j r b) (agree_nonempty _ _))
    (Nat.cast_pos.2 (card_agree_pos _ _))

lemma bgWeight_pos {z : Param N} (hz : z ∈ openCube N) (s : State N) (S : Finset (Fin N))
    (w : State N) : 0 < bgWeight (tpmOf z) S s w := by
  rw [bgWeight_eq]; exact div_pos (blockW_pos hz s S w) (sum_fullProb_pos hz s)

lemma sysCauseProb_pos {z : Param N} (hz : z ∈ openCube N) (s : State N) (S : Finset (Fin N))
    (t : State N) : 0 < sysCauseProb (tpmOf z) S s s t :=
  prod_pos fun j _ => div_pos (sum_pos (fun w _ => mul_pos (prob_pos hz _ _ _)
    (bgWeight_pos hz s S w)) univ_nonempty) (by positivity)

lemma sysUncCause_pos {z : Param N} (hz : z ∈ openCube N) (s : State N) (S : Finset (Fin N)) :
    0 < sysUncCause (tpmOf z) S s s :=
  avg_pos _ fun t => sysCauseProb_pos hz s S t

lemma sysBackCause_pos {z : Param N} (hz : z ∈ openCube N) (s : State N) (S : Finset (Fin N))
    (t : State N) : 0 < sysBackCause (tpmOf z) S s s t :=
  div_pos (sysCauseProb_pos hz s S t) (mul_pos (by positivity) (sysUncCause_pos hz s S))

lemma sysPartCauseProb_pos {z : Param N} (hz : z ∈ openCube N) (s : State N)
    (S : Finset (Fin N)) (θ : SysPartition N S) (t : State N) :
    0 < sysPartCauseProb (tpmOf z) S s θ s t :=
  prod_pos fun j _ => div_pos (sum_pos (fun w _ => mul_pos (effUnit_pos hz _ _ _ _)
    (bgWeight_pos hz s S w)) univ_nonempty) (by positivity)

lemma sysEffProb_pos {z : Param N} (hz : z ∈ openCube N) (s : State N) (S : Finset (Fin N))
    (t : State N) : 0 < sysEffProb (tpmOf z) S s s t :=
  prod_pos fun _ _ => prob_pos hz _ _ _

lemma sysPartEffProb_pos {z : Param N} (hz : z ∈ openCube N) (s : State N)
    (S : Finset (Fin N)) (θ : SysPartition N S) (t : State N) :
    0 < sysPartEffProb (tpmOf z) S s θ s t :=
  prod_pos fun _ _ => effUnit_pos hz _ _ _ _

/-! ### L3: column scaling -/

/-- `T'` multiplies every `prob j · (b j)` of `T` by `c j`. -/
def BitScale (T T' : UnitTPM N) (b : Fin N → Bool) (c : Fin N → ℝ) : Prop :=
  ∀ j r, T'.prob j r (b j) = c j * T.prob j r (b j)

section Scale

variable {T T' : UnitTPM N} {b : Fin N → Bool} {c : Fin N → ℝ}

lemma BitScale.apply (h : BitScale T T' b c) {j : Fin N} {x : Bool} (hj : c j = 1 ∨ b j = x)
    (r : State N) : T'.prob j r x = c j * T.prob j r x := by
  rcases hj with hj | rfl
  · have h1 := T.normalized j r
    have h2 := T'.normalized j r
    have h3 := h j r
    rw [hj, one_mul] at h3 ⊢
    cases hb : b j <;> cases x <;> rw [hb] at h3 <;> linarith
  · exact h j r

lemma effUnit_scale (h : BitScale T T' b c) {j : Fin N} {x : Bool} (hj : c j = 1 ∨ b j = x)
    (M : Finset (Fin N)) (m : State N) :
    effUnit T' M m j x = c j * effUnit T M m j x := by
  unfold effUnit
  rw [Finset.sum_congr rfl fun r _ => h.apply hj r, ← Finset.mul_sum, mul_div_assoc]

/-- **L3b/L3c** (effect branches are homogeneous in the scaled columns they read). -/
lemma BE_scale (h : BitScale T T' b c) (s : State N) {S : Finset (Fin N)}
    (θ : SysPartition N S) (t : State N) (hS : ∀ j ∈ S, c j = 1 ∨ b j = t j)
    (hc : ∏ j ∈ S, c j ≠ 0) :
    BE T' s S θ t = (∏ j ∈ S, c j) * BE T s S θ t := by
  have he : sysEffProb T' S s s t = (∏ j ∈ S, c j) * sysEffProb T S s s t := by
    unfold sysEffProb
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j hj => h.apply (hS j hj) _
  have hp : sysPartEffProb T' S s θ s t = (∏ j ∈ S, c j) * sysPartEffProb T S s θ s t := by
    unfold sysPartEffProb
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j hj => effUnit_scale h (hS j hj) _ _
  unfold BE
  rw [he, hp, mul_div_mul_left _ _ hc, mul_assoc]

variable {s : State N}

lemma fullProb_scale (h : BitScale T T' s c) (v : State N) :
    fullProb T' v s = (∏ j, c j) * fullProb T v s := by
  unfold fullProb; rw [← prod_mul_distrib]; exact prod_congr rfl fun j _ => h j v

lemma bgWeight_scale (h : BitScale T T' s c) (hc : ∀ j, c j ≠ 0) (S : Finset (Fin N))
    (w : State N) : bgWeight T' S s w = bgWeight T S s w := by
  unfold bgWeight
  simp only [fullProb_scale h, ← Finset.mul_sum]
  rw [mul_div_assoc, mul_div_mul_left _ _ (prod_ne_zero_iff.2 fun j _ => hc j)]

lemma sysCauseProb_scale (h : BitScale T T' s c) (hc : ∀ j, c j ≠ 0) (S : Finset (Fin N))
    (t : State N) : sysCauseProb T' S s s t = (∏ j ∈ S, c j) * sysCauseProb T S s s t := by
  unfold sysCauseProb
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl fun w _ => by rw [bgWeight_scale h hc, h j, mul_assoc],
    ← Finset.mul_sum, mul_div_assoc]

lemma sysUncCause_scale (h : BitScale T T' s c) (hc : ∀ j, c j ≠ 0) (S : Finset (Fin N)) :
    sysUncCause T' S s s = (∏ j ∈ S, c j) * sysUncCause T S s s := by
  unfold sysUncCause
  simp only [sysCauseProb_scale h hc]
  exact avg_scale _ _

lemma sysPartCauseProb_scale (h : BitScale T T' s c) (hc : ∀ j, c j ≠ 0) (S : Finset (Fin N))
    (θ : SysPartition N S) (t : State N) :
    sysPartCauseProb T' S s θ s t = (∏ j ∈ S, c j) * sysPartCauseProb T S s θ s t := by
  unfold sysPartCauseProb
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl fun w _ => by
      rw [bgWeight_scale h hc, effUnit_scale h (Or.inr rfl), mul_assoc],
    ← Finset.mul_sum, mul_div_assoc]

/-- **L3d** (cause branches are invariant under scaling the current-state columns). -/
lemma BC_scale (h : BitScale T T' s c) (hc : ∀ j, c j ≠ 0) (S : Finset (Fin N))
    (θ : SysPartition N S) (t : State N) : BC T' s S θ t = BC T s S θ t := by
  have hS : ∏ j ∈ S, c j ≠ 0 := prod_ne_zero_iff.2 fun j _ => hc j
  unfold BC sysBackCause
  rw [sysCauseProb_scale h hc, sysUncCause_scale h hc, sysPartCauseProb_scale h hc,
    mul_left_comm, mul_div_mul_left _ _ hS, mul_div_mul_left _ _ hS]

end Scale

/-! ### Realising a scaling inside the open cube (L3a) -/

/-- Multiply `prob j · (b j)` by `c j` at the parameter level. -/
def scaleParam (z : Param N) (b : Fin N → Bool) (c : Fin N → ℝ) : Param N :=
  fun r j => if b j then c j * z r j else 1 - c j * (1 - z r j)

lemma scaleParam_mem {z : Param N} (hz : z ∈ openCube N) (b : Fin N → Bool) {c : Fin N → ℝ}
    (hc : ∀ j, 0 < c j ∧ c j ≤ 1) : scaleParam z b c ∈ openCube N := by
  intro r j
  have h := hz r j
  obtain ⟨h1, h2⟩ := hc j
  simp only [scaleParam, Set.mem_Ioo] at h ⊢
  have h3 := mul_pos h1 h.1
  have h4 := mul_pos h1 (sub_pos.2 h.2)
  split_ifs
  · constructor <;> nlinarith
  · constructor <;> nlinarith

lemma scaleParam_bitScale {z : Param N} (hz : z ∈ openCube N) (b : Fin N → Bool)
    {c : Fin N → ℝ} (hc : ∀ j, 0 < c j ∧ c j ≤ 1) :
    BitScale (tpmOf z) (tpmOf (scaleParam z b c)) b c := by
  intro j r
  have hm := scaleParam_mem hz b hc r j
  show (if b j then clamp01 (scaleParam z b c r j) else 1 - clamp01 (scaleParam z b c r j)) =
    c j * (if b j then clamp01 (z r j) else 1 - clamp01 (z r j))
  rw [clamp01_eq (Set.Ioo_subset_Icc_self hm), clamp01_eq (Set.Ioo_subset_Icc_self (hz r j))]
  unfold scaleParam
  cases b j <;> simp

end Census
end IIT
