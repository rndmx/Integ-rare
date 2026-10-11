/-
Census, B1 count package: measurability of the mechanism-level quantities of `IIT/Cond.lean`
(`phiDAt`, `maxCausePurviewsAt`, `maxEffPurviewsAt`, `distinctionMechsAt`) as functions of the
parameters `z : Param N` through `tpmOf z`.

Used by `B1CountSkel.lean` to show that the bad set `BadMech` of the count package is measurable.
Everything here is a finite Boolean combination of measurable real functions; the proofs follow
the system-level template of `B1Defs.lean` §6 (`b1m_*`).
-/
import IIT.Census.B1DefsX

namespace IIT
namespace Census

open MeasureTheory Finset
open scoped Classical

variable {N : ℕ}

section Gen

variable {X : Type*} [MeasurableSpace X]

/-- A finset-valued map with measurable membership sets has measurable level sets. -/
lemma b1c_measurableSet_eq_of_mem {α : Type*} [Fintype α] {F : X → Finset α}
    (hF : ∀ a, MeasurableSet {x | a ∈ F x}) (A : Finset α) : MeasurableSet {x | F x = A} := by
  have h : {x | F x = A} = ⋂ a, {x | a ∈ F x ↔ a ∈ A} := by
    ext x; simp [Finset.ext_iff]
  rw [h]
  refine MeasurableSet.iInter fun a => ?_
  by_cases ha : a ∈ A
  · convert hF a using 1
    ext x; simp [ha]
  · convert (hF a).compl using 1
    ext x; simp [ha]

/-- `sup'` over a constant nonempty finset of measurable functions. -/
lemma b1c_measurable_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → X → ℝ}
    (hf : ∀ i ∈ s, Measurable (f i)) : Measurable fun x => s.sup' hs fun i => f i x := by
  have h2 : (fun x => s.sup' hs fun i => f i x) = s.sup' hs f := by
    funext x; rw [Finset.sup'_apply]
  rw [h2]
  exact Finset.measurable_sup' hs hf

/-- `sup'` over a measurably varying, always nonempty, argmax set. -/
lemma b1c_measurable_sup'_argmax {α : Type*} [Fintype α] [Nonempty α] {F : X → α → ℝ}
    (hF : ∀ a, Measurable fun x => F x a) {g : X → α → ℝ} (hg : ∀ a, Measurable fun x => g x a) :
    Measurable fun x => (argmaxSet (F x)).sup' (argmaxSet_nonempty _) (g x) := by
  have h : (fun x => (argmaxSet (F x)).sup' (argmaxSet_nonempty _) (g x)) =
      fun x => sup'OrZero (argmaxSet (F x)) (g x) := by
    funext x
    unfold sup'OrZero
    rw [dif_pos (argmaxSet_nonempty _)]
  rw [h]
  exact b1_measurable_sup'OrZero (b1_measurableSet_argmax_eq hF) hg

end Gen

/-! ### The effect side -/

section Eff

variable (S : Finset (Fin N)) (u : State N) (M : Finset (Fin N)) (m : State N)

lemma b1c_effRepAt (Z : Finset (Fin N)) (z : State N) :
    Measurable fun p : Param N => effRepAt (tpmOf p) S u M m Z z := by
  unfold effRepAt effRep
  exact Finset.measurable_prod _ fun k _ => b1m_effUnit _ _ _ _

lemma b1c_uncEffRepAt (Z : Finset (Fin N)) (z : State N) :
    Measurable fun p : Param N => uncEffRepAt (tpmOf p) S u M Z z := by
  unfold uncEffRepAt avgOverStates
  exact (Finset.measurable_sum _ fun m' _ => b1c_effRepAt S u M m' Z z).div_const _

lemma b1c_iiEAt (Z : Finset (Fin N)) (z : State N) :
    Measurable fun p : Param N => iiEAt (tpmOf p) S u M m Z z := by
  unfold iiEAt
  exact (b1c_effRepAt S u M m Z z).mul
    (b1_measurable_logb ((b1c_effRepAt S u M m Z z).div (b1c_uncEffRepAt S u M Z z)))

lemma b1c_partEffRepAt (Z : Finset (Fin N)) (z : State N) (θ : Partition N M Z) :
    Measurable fun p : Param N => partEffRepAt (tpmOf p) S u M m Z z θ := by
  unfold partEffRepAt
  exact Finset.measurable_prod _ fun k _ => b1m_effUnit _ _ _ _

lemma b1c_phiEofPartitionAt (Z : Finset (Fin N)) (z : State N) (θ : Partition N M Z) :
    Measurable fun p : Param N => phiEofPartitionAt (tpmOf p) S u M m Z z θ := by
  unfold phiEofPartitionAt
  exact (b1c_effRepAt S u M m Z z).mul (b1_measurable_pos (b1_measurable_logb
    ((b1c_effRepAt S u M m Z z).div (b1c_partEffRepAt S u M m Z z θ))))

lemma b1c_normalizedPhiAt (Z : Finset (Fin N)) (z : State N) (θ : Partition N M Z) :
    Measurable fun p : Param N => normalizedPhiAt (tpmOf p) S u M m Z z θ := by
  unfold normalizedPhiAt
  exact (b1c_phiEofPartitionAt S u M m Z z θ).div_const _

lemma b1c_phiEatAt (Z : Finset (Fin N)) (z : State N) :
    Measurable fun p : Param N => phiEatAt (tpmOf p) S u M m Z z := by
  unfold phiEatAt mipSetEAt
  exact b1_measurable_sup'OrZero
    (b1_measurableSet_argmin_eq fun θ => b1c_normalizedPhiAt S u M m Z z θ)
    fun θ => b1c_phiEofPartitionAt S u M m Z z θ

lemma b1c_mem_maxEffStatesAt (Z : Finset (Fin N)) (z : State N) :
    MeasurableSet {p : Param N | z ∈ maxEffStatesAt (tpmOf p) S u M m Z} :=
  b1_measurableSet_mem_argmax (fun z => b1c_iiEAt S u M m Z z) z

lemma b1c_phiEpurviewAt (Z : Finset (Fin N)) :
    Measurable fun p : Param N => phiEpurviewAt (tpmOf p) S u M m Z := by
  unfold phiEpurviewAt maxEffStatesAt
  exact b1c_measurable_sup'_argmax (fun z => b1c_iiEAt S u M m Z z)
    fun z => b1c_phiEatAt S u M m Z z

lemma b1c_phiEmechAt : Measurable fun p : Param N => phiEmechAt (tpmOf p) S u M m := by
  unfold phiEmechAt
  exact b1c_measurable_sup' _ fun Z _ => b1c_phiEpurviewAt S u M m Z

lemma b1c_mem_effCandidatesAt_iff (T : UnitTPM N) (q : Finset (Fin N) × State N) :
    q ∈ effCandidatesAt T S u M m ↔ q.1 ⊆ S ∧ q.2 ∈ maxEffStatesAt T S u M m q.1 := by
  unfold effCandidatesAt
  simp only [Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨Z, hZ, z, hz, rfl⟩; exact ⟨hZ, hz⟩
  · intro h; exact ⟨q.1, h.1, q.2, h.2, rfl⟩

lemma b1c_mem_effCandidatesAt (q : Finset (Fin N) × State N) :
    MeasurableSet {p : Param N | q ∈ effCandidatesAt (tpmOf p) S u M m} := by
  simp only [b1c_mem_effCandidatesAt_iff]
  by_cases hq : q.1 ⊆ S
  · simp only [hq, true_and]; exact b1c_mem_maxEffStatesAt S u M m q.1 q.2
  · simp only [hq, false_and, Set.setOf_false]; exact MeasurableSet.empty

lemma b1c_mem_maxEffPurviewsAt (q : Finset (Fin N) × State N) :
    MeasurableSet {p : Param N | q ∈ maxEffPurviewsAt (tpmOf p) S u M m} := by
  have h : {p : Param N | q ∈ maxEffPurviewsAt (tpmOf p) S u M m} =
      {p | q ∈ effCandidatesAt (tpmOf p) S u M m} ∩
        ⋂ q' : Finset (Fin N) × State N, ({p | q' ∈ effCandidatesAt (tpmOf p) S u M m}ᶜ ∪
          {p | phiEatAt (tpmOf p) S u M m q'.1 q'.2 ≤ phiEatAt (tpmOf p) S u M m q.1 q.2}) := by
    ext p
    simp only [maxEffPurviewsAt, Finset.mem_filter, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
    refine and_congr Iff.rfl (forall_congr' fun q' => ?_)
    tauto
  rw [h]
  exact (b1c_mem_effCandidatesAt S u M m q).inter (MeasurableSet.iInter fun q' =>
    (b1c_mem_effCandidatesAt S u M m q').compl.union
      (measurableSet_le (b1c_phiEatAt S u M m q'.1 q'.2) (b1c_phiEatAt S u M m q.1 q.2)))

end Eff

/-! ### The cause side -/

section Cause

variable (S : Finset (Fin N)) (u : State N) (M : Finset (Fin N)) (m : State N)

lemma b1c_causeFwdAt (Z : Finset (Fin N)) (z : State N) :
    Measurable fun p : Param N => causeFwdAt (tpmOf p) S u Z z M m := by
  unfold causeFwdAt
  exact Finset.measurable_prod _ fun i _ => (Finset.measurable_sum _ fun w _ =>
    (b1m_effUnit _ _ _ _).mul (b1m_bgWeight S u w)).div_const _

lemma b1c_uncCauseFwdAt (Z : Finset (Fin N)) :
    Measurable fun p : Param N => uncCauseFwdAt (tpmOf p) S u Z M m := by
  unfold uncCauseFwdAt avgOverStates
  exact (Finset.measurable_sum _ fun z _ => b1c_causeFwdAt S u M m Z z).div_const _

lemma b1c_causeRepAt (Z : Finset (Fin N)) (z : State N) :
    Measurable fun p : Param N => causeRepAt (tpmOf p) S u Z z M m := by
  unfold causeRepAt
  exact (b1c_causeFwdAt S u M m Z z).div (measurable_const.mul (b1c_uncCauseFwdAt S u M m Z))

lemma b1c_iiCAt (Z : Finset (Fin N)) (z : State N) :
    Measurable fun p : Param N => iiCAt (tpmOf p) S u M m Z z := by
  unfold iiCAt
  exact (b1c_causeRepAt S u M m Z z).mul
    (b1_measurable_logb ((b1c_causeFwdAt S u M m Z z).div (b1c_uncCauseFwdAt S u M m Z)))

lemma b1c_partCauseFwdAt (Z : Finset (Fin N)) (z : State N) (θ : Partition N M Z) :
    Measurable fun p : Param N => partCauseFwdAt (tpmOf p) S u Z z M m θ := by
  unfold partCauseFwdAt
  exact Finset.measurable_prod _ fun i _ => (Finset.measurable_sum _ fun w _ =>
    (b1m_effUnit _ _ _ _).mul (b1m_bgWeight S u w)).div_const _

lemma b1c_phiCofPartitionAt (Z : Finset (Fin N)) (z : State N) (θ : Partition N M Z) :
    Measurable fun p : Param N => phiCofPartitionAt (tpmOf p) S u Z z M m θ := by
  unfold phiCofPartitionAt
  exact (b1c_causeRepAt S u M m Z z).mul (b1_measurable_pos (b1_measurable_logb
    ((b1c_causeFwdAt S u M m Z z).div (b1c_partCauseFwdAt S u M m Z z θ))))

lemma b1c_normalizedPhiCAt (Z : Finset (Fin N)) (z : State N) (θ : Partition N M Z) :
    Measurable fun p : Param N => normalizedPhiCAt (tpmOf p) S u Z z M m θ := by
  unfold normalizedPhiCAt
  exact (b1c_phiCofPartitionAt S u M m Z z θ).div_const _

lemma b1c_phiCatAt (Z : Finset (Fin N)) (z : State N) :
    Measurable fun p : Param N => phiCatAt (tpmOf p) S u Z z M m := by
  unfold phiCatAt mipSetCAt
  exact b1_measurable_sup'OrZero
    (b1_measurableSet_argmin_eq fun θ => b1c_normalizedPhiCAt S u M m Z z θ)
    fun θ => b1c_phiCofPartitionAt S u M m Z z θ

lemma b1c_mem_maxCauseStatesAt (Z : Finset (Fin N)) (z : State N) :
    MeasurableSet {p : Param N | z ∈ maxCauseStatesAt (tpmOf p) S u M m Z} :=
  b1_measurableSet_mem_argmax (fun z => b1c_iiCAt S u M m Z z) z

lemma b1c_phiCpurviewAt (Z : Finset (Fin N)) :
    Measurable fun p : Param N => phiCpurviewAt (tpmOf p) S u M m Z := by
  unfold phiCpurviewAt maxCauseStatesAt
  exact b1c_measurable_sup'_argmax (fun z => b1c_iiCAt S u M m Z z)
    fun z => b1c_phiCatAt S u M m Z z

lemma b1c_phiCmechAt : Measurable fun p : Param N => phiCmechAt (tpmOf p) S u M m := by
  unfold phiCmechAt
  exact b1c_measurable_sup' _ fun Z _ => b1c_phiCpurviewAt S u M m Z

lemma b1c_phiDAt : Measurable fun p : Param N => phiDAt (tpmOf p) S u M m := by
  unfold phiDAt
  exact (b1c_phiCmechAt S u M m).min (b1c_phiEmechAt S u M m)

lemma b1c_mem_causeCandidatesAt_iff (T : UnitTPM N) (q : Finset (Fin N) × State N) :
    q ∈ causeCandidatesAt T S u M m ↔ q.1 ⊆ S ∧ q.2 ∈ maxCauseStatesAt T S u M m q.1 := by
  unfold causeCandidatesAt
  simp only [Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨Z, hZ, z, hz, rfl⟩; exact ⟨hZ, hz⟩
  · intro h; exact ⟨q.1, h.1, q.2, h.2, rfl⟩

lemma b1c_mem_causeCandidatesAt (q : Finset (Fin N) × State N) :
    MeasurableSet {p : Param N | q ∈ causeCandidatesAt (tpmOf p) S u M m} := by
  simp only [b1c_mem_causeCandidatesAt_iff]
  by_cases hq : q.1 ⊆ S
  · simp only [hq, true_and]; exact b1c_mem_maxCauseStatesAt S u M m q.1 q.2
  · simp only [hq, false_and, Set.setOf_false]; exact MeasurableSet.empty

lemma b1c_mem_maxCausePurviewsAt (q : Finset (Fin N) × State N) :
    MeasurableSet {p : Param N | q ∈ maxCausePurviewsAt (tpmOf p) S u M m} := by
  have h : {p : Param N | q ∈ maxCausePurviewsAt (tpmOf p) S u M m} =
      {p | q ∈ causeCandidatesAt (tpmOf p) S u M m} ∩
        ⋂ q' : Finset (Fin N) × State N, ({p | q' ∈ causeCandidatesAt (tpmOf p) S u M m}ᶜ ∪
          {p | phiCatAt (tpmOf p) S u q'.1 q'.2 M m ≤ phiCatAt (tpmOf p) S u q.1 q.2 M m}) := by
    ext p
    simp only [maxCausePurviewsAt, Finset.mem_filter, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
    refine and_congr Iff.rfl (forall_congr' fun q' => ?_)
    tauto
  rw [h]
  exact (b1c_mem_causeCandidatesAt S u M m q).inter (MeasurableSet.iInter fun q' =>
    (b1c_mem_causeCandidatesAt S u M m q').compl.union
      (measurableSet_le (b1c_phiCatAt S u M m q'.1 q'.2) (b1c_phiCatAt S u M m q.1 q.2)))

lemma b1c_maxCausePurviewsAt_eq (A : Finset (Finset (Fin N) × State N)) :
    MeasurableSet {p : Param N | maxCausePurviewsAt (tpmOf p) S u M m = A} :=
  b1c_measurableSet_eq_of_mem (fun q => b1c_mem_maxCausePurviewsAt S u M m q) A

end Cause

/-! ### Congruence and the distinction set -/

section Dist

variable (S : Finset (Fin N)) (u s : State N)

lemma b1c_congruent (A B : StatedPurview N) :
    MeasurableSet {p : Param N | Congruent (tpmOf p) S u s A B} := by
  have h : {p : Param N | Congruent (tpmOf p) S u s A B} =
      (⋃ t : State N, if A ⊆ stated S t then {p | t ∈ sysMaxCauseStates (tpmOf p) S u s}
        else ∅) ∩
      (⋃ t : State N, if B ⊆ stated S t then {p | t ∈ sysMaxEffStates (tpmOf p) S u s}
        else ∅) := by
    ext p
    simp only [Congruent, sysStatedCause, sysStatedEffect, Finset.mem_image,
      Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨c, ⟨t, ht, rfl⟩, hAc⟩, ⟨e, ⟨t', ht', rfl⟩, hBe⟩⟩
      refine ⟨⟨t, ?_⟩, ⟨t', ?_⟩⟩
      · rw [if_pos hAc]; exact ht
      · rw [if_pos hBe]; exact ht'
    · rintro ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩
      split_ifs at ht with hAt
      · split_ifs at ht' with hBt
        · exact ⟨⟨_, ⟨t, ht, rfl⟩, hAt⟩, ⟨_, ⟨t', ht', rfl⟩, hBt⟩⟩
        · exact absurd ht' (Set.notMem_empty p)
      · exact absurd ht (Set.notMem_empty p)
  rw [h]
  refine (MeasurableSet.iUnion fun t => ?_).inter (MeasurableSet.iUnion fun t => ?_)
  · split_ifs
    · exact b1m_mem_sysMaxCauseStates S u s t
    · exact MeasurableSet.empty
  · split_ifs
    · exact b1m_mem_sysMaxEffStates S u s t
    · exact MeasurableSet.empty

/-- **Membership of a mechanism in the conditioned distinction set is measurable.** -/
theorem b1c_mem_distinctionMechsAt (M : Finset (Fin N)) :
    MeasurableSet {p : Param N | M ∈ distinctionMechsAt (tpmOf p) S u s} := by
  have h : {p : Param N | M ∈ distinctionMechsAt (tpmOf p) S u s} =
      (if M ⊆ S then Set.univ else ∅) ∩ {p | 0 < phiDAt (tpmOf p) S u M s} ∩
        ⋃ pc : Finset (Fin N) × State N, ⋃ pe : Finset (Fin N) × State N,
          {p | pc ∈ maxCausePurviewsAt (tpmOf p) S u M s} ∩
            {p | pe ∈ maxEffPurviewsAt (tpmOf p) S u M s} ∩
            {p | Congruent (tpmOf p) S u s (stated pc.1 pc.2) (stated pe.1 pe.2)} := by
    ext p
    simp only [distinctionMechsAt, Finset.mem_filter, Finset.mem_powerset, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_iUnion]
    by_cases hM : M ⊆ S
    · simp only [hM, if_true, Set.mem_univ, true_and]
      constructor
      · rintro ⟨h0, pc, hpc, pe, hpe, hcg⟩; exact ⟨h0, pc, pe, ⟨hpc, hpe⟩, hcg⟩
      · rintro ⟨h0, pc, pe, ⟨hpc, hpe⟩, hcg⟩; exact ⟨h0, pc, hpc, pe, hpe, hcg⟩
    · simp only [hM, if_false, Set.mem_empty_iff_false, false_and]
  rw [h]
  refine (MeasurableSet.inter ?_ (measurableSet_lt measurable_const (b1c_phiDAt S u M s))).inter
    (MeasurableSet.iUnion fun pc => MeasurableSet.iUnion fun pe =>
      ((b1c_mem_maxCausePurviewsAt S u M s pc).inter (b1c_mem_maxEffPurviewsAt S u M s pe)).inter
        (b1c_congruent S u s _ _))
  split_ifs
  · exact MeasurableSet.univ
  · exact MeasurableSet.empty

end Dist

end Census
end IIT

#print axioms IIT.Census.b1c_mem_distinctionMechsAt
#print axioms IIT.Census.b1c_maxCausePurviewsAt_eq
#print axioms IIT.Census.b1c_phiDAt
