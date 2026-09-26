/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import IIT.Phi

/-!
# The system level of IIT 4.0: `φ_s`, complexes, and big `Φ`

`[IIT4]` = Albantakis et al., *Integrated information theory (IIT) 4.0*,
PLoS Comput Biol **19**(10): e1011465 (2023).

`IIT/Phi.lean` formalizes the *mechanism* level and stops at `φ_d`.  Big `Φ` needs three
things that live above it, and this file supplies them in order:

1. the **background-conditioned TPMs** `T_e` and `T_c` of a candidate system `S ⊆ U`
   `[IIT4, Eqs 3, 4]` — for effects the background is pinned at its current state, for
   causes it is marginalized against a Bayes-updated posterior.  These differ as soon as
   `S ⊊ U`, which is why the mechanism-level file, using a single `T`, is exact only for
   `S = U`;
2. the system's **maximal cause–effect state** `s'` `[IIT4, Eqs 5–13]`, which is what the
   congruence clause of `[IIT4, Eq 48]` refers to, and **system integrated information**
   `φ_s` over *directional* partitions `[IIT4, Eqs 14–23]`;
3. **complexes** `[IIT4, Eqs 24–26]`, since `[IIT4, Eq 58]` unfolds the `Φ`-structure of a
   maximal substrate.

## This file: Part A — background conditioning and the system repertoires
-/

namespace IIT

open Finset

variable {N : ℕ}

/-! ## Merging a system state with a background state -/

/-- The universe state agreeing with `s` on `S` and with `u` off `S`. -/
def merge (S : Finset (Fin N)) (s u : State N) : State N :=
  fun j => if j ∈ S then s j else u j

@[simp] lemma merge_mem {S : Finset (Fin N)} {s u : State N} {j : Fin N} (h : j ∈ S) :
    merge S s u j = s j := by simp [merge, h]

@[simp] lemma merge_not_mem {S : Finset (Fin N)} {s u : State N} {j : Fin N} (h : j ∉ S) :
    merge S s u j = u j := by simp [merge, h]

lemma merge_univ (s u : State N) : merge Finset.univ s u = s := by
  funext j; simp [merge]

/-- The probability that the universe transitions from `v` to `w`, `[IIT4, Eq 1]` under
conditional independence `[IIT4, Eq 2]`. -/
noncomputable def fullProb (T : UnitTPM N) (v w : State N) : ℝ :=
  ∏ i, T.prob i v (w i)

lemma fullProb_nonneg (T : UnitTPM N) (v w : State N) : 0 ≤ fullProb T v w :=
  Finset.prod_nonneg fun i _ => T.nonneg i v (w i)

lemma fullProb_le_one (T : UnitTPM N) (v w : State N) : fullProb T v w ≤ 1 :=
  Finset.prod_le_one (fun i _ => T.nonneg i v (w i)) (fun i _ => T.le_one i v (w i))

/-! ## `T_e`: the effect TPM of a candidate system `[IIT4, Eq 3]`

"For evaluating effects, the state of the background units is fully determined by the
current state of the universe."  So the background is *pinned*, not averaged. -/

/-- `T_e ≡ p_e(s̄ | s) = p(s̄ | s, w)` `[IIT4, Eq 3]`, the probability that the system `S`
goes from `s` to `s̄` with the background held at its state in `u`. -/
noncomputable def sysEffProb (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (s t : State N) : ℝ :=
  ∏ i ∈ S, T.prob i (merge S s u) (t i)

lemma sysEffProb_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u s t : State N) :
    0 ≤ sysEffProb T S u s t :=
  Finset.prod_nonneg fun i _ => T.nonneg i _ (t i)

lemma sysEffProb_le_one (T : UnitTPM N) (S : Finset (Fin N)) (u s t : State N) :
    sysEffProb T S u s t ≤ 1 :=
  Finset.prod_le_one (fun i _ => T.nonneg i _ (t i)) (fun i _ => T.le_one i _ (t i))

/-- With no background there is nothing to pin: `T_e` is the universe TPM. -/
lemma sysEffProb_univ (T : UnitTPM N) (u s t : State N) :
    sysEffProb T Finset.univ u s t = fullProb T s t := by
  rw [sysEffProb, fullProb, merge_univ]

/-- `p_e(s̄)` `[IIT4, Eq 6]`: the unconstrained effect probability, the marginal of `s̄`
over all system states taken with equal probability.  Because `sysEffProb` depends on `s`
only through its restriction to `S`, averaging over all `2^N` universe states computes the
paper's `|Ω_S|⁻¹ ∑_{s ∈ Ω_S}`. -/
noncomputable def sysUncEff (T : UnitTPM N) (S : Finset (Fin N)) (u t : State N) : ℝ :=
  avgOverStates fun s => sysEffProb T S u s t

lemma sysUncEff_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u t : State N) :
    0 ≤ sysUncEff T S u t := by
  rw [sysUncEff, avgOverStates]
  exact div_nonneg (Finset.sum_nonneg fun s _ => sysEffProb_nonneg T S u s t)
    (by positivity)

/-- `ii_e(s, s̄)` `[IIT4, Eq 5]`: intrinsic effect information, selectivity times
informativeness.  As at the mechanism level there is no positive part here — `ii` is
signed; the positive part enters only at `φ` `[IIT4, Eq 19]`. -/
noncomputable def sysIiE (T : UnitTPM N) (S : Finset (Fin N)) (u s t : State N) : ℝ :=
  sysEffProb T S u s t * Real.logb 2 (sysEffProb T S u s t / sysUncEff T S u t)

/-! ## `T_c`: the cause TPM of a candidate system `[IIT4, Eq 4]`

"For evaluating causes, knowledge of the current state is used to compute the probability
distribution over potential prior states of the background units, which is not necessarily
uniform or deterministic."  So the background is marginalized against the posterior
`(∑_ŝ p(u | ŝ, w̄)) / (∑_û p(u | û))`. -/

/-- The Bayes weight `[IIT4, Eq 4]` on a background prior state `w`:
`(∑_{ŝ ∈ Ω_S} p(u | ŝ, w)) / (∑_{û ∈ Ω_U} p(u | û))`.

The numerator sums over `Ω_S`; since the summand depends on `s` only through `s|_S`, the
sum over all `2^N` universe states overcounts each by `2^(N - |S|)`, which is
divided out. -/
noncomputable def bgWeight (T : UnitTPM N) (S : Finset (Fin N)) (u w : State N) : ℝ :=
  ((∑ s : State N, fullProb T (merge S s w) u) / (2 : ℝ) ^ (N - S.card))
    / ∑ v : State N, fullProb T v u

lemma bgWeight_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u w : State N) :
    0 ≤ bgWeight T S u w := by
  rw [bgWeight]
  refine div_nonneg (div_nonneg (Finset.sum_nonneg fun s _ => fullProb_nonneg T _ u) ?_) ?_
  · positivity
  · exact Finset.sum_nonneg fun v _ => fullProb_nonneg T v u

/-- `T_c ≡ p_c(s | s̄)` `[IIT4, Eq 4]`: the probability that the prior system state `s̄`
produces the current state `s`, with the background marginalized against `bgWeight`.

The inner sum runs over background states `Ω_W`; as above it is taken over all universe
states and the `2^|S|` overcount divided out. -/
noncomputable def sysCauseProb (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (s t : State N) : ℝ :=
  ∏ i ∈ S, ((∑ w : State N, T.prob i (merge S t w) (s i) * bgWeight T S u w)
    / (2 : ℝ) ^ S.card)

/-- The cause probability computed with the **effect-side background convention**: the
background is held at the current state `u` `[IIT4, Eq 3]` instead of being marginalized
against the `[IIT4, Eq 4]` posterior.  This is not what `[IIT4]` prescribes for causes; it
is here only so that `sysCauseProb_eq_pinned_univ` can say precisely when the choice of
background convention makes no difference. -/
noncomputable def sysCauseProbPinned (T : UnitTPM N) (S : Finset (Fin N)) (u s t : State N) :
    ℝ :=
  ∏ i ∈ S, T.prob i (merge S t u) (s i)

/-- **On the whole substrate the background convention is immaterial.**  With `S = U`
there is no background to marginalize: `merge U t w = t` for every `w`, and the Bayes
weight of `[IIT4, Eq 4]` is identically `1`, so the sum over `Ω_W` collapses and the two
conventions agree.  For `S ⊊ U` they differ, which is why every quantity below that
depends on `[IIT4, Eq 4]` is sensitive to the candidate system and the whole-substrate
case is not. -/
theorem sysCauseProb_eq_pinned_univ (T : UnitTPM N) (u s t : State N)
    (hu : 0 < ∑ v : State N, fullProb T v u) :
    sysCauseProb T Finset.univ u s t = sysCauseProbPinned T Finset.univ u s t := by
  have hmerge : ∀ v w : State N, merge (Finset.univ : Finset (Fin N)) v w = v := by
    intro v w; funext j; simp [merge]
  have hbg : ∀ w : State N, bgWeight T (Finset.univ : Finset (Fin N)) u w = 1 := by
    intro w
    rw [bgWeight, Finset.card_univ, Fintype.card_fin, Nat.sub_self, pow_zero, div_one]
    rw [Finset.sum_congr rfl fun v _ => by rw [hmerge v w]]
    exact div_self hu.ne'
  have hcard : ((Finset.univ : Finset (State N)).card : ℝ) = (2 : ℝ) ^ N := by
    rw [card_state]; push_cast; ring
  rw [sysCauseProb, sysCauseProbPinned]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl fun w _ => by rw [hbg w, mul_one, hmerge t w],
    Finset.sum_const, nsmul_eq_mul, hcard, hmerge t u, Finset.card_univ, Fintype.card_fin]
  field_simp

lemma sysCauseProb_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u s t : State N) :
    0 ≤ sysCauseProb T S u s t := by
  refine Finset.prod_nonneg fun i _ => div_nonneg ?_ (by positivity)
  exact Finset.sum_nonneg fun w _ =>
    mul_nonneg (T.nonneg i _ (s i)) (bgWeight_nonneg T S u w)

/-- With no background, the Bayes weight of `[IIT4, Eq 4]` is `1`.

The hypothesis says the current state `u` is reachable at all; without it the weight is
`0 / 0`. -/
lemma bgWeight_univ (T : UnitTPM N) (u w : State N)
    (h : 0 < ∑ v : State N, fullProb T v u) :
    bgWeight T Finset.univ u w = 1 := by
  rw [bgWeight]
  simp only [Finset.card_univ, Fintype.card_fin, Nat.sub_self, pow_zero, div_one]
  rw [Finset.sum_congr rfl fun s _ => by rw [merge_univ]]
  exact div_self h.ne'

/-- **`T_c = T_e` when the candidate system is the whole universe.**  `[IIT4, Eq 4]`
collapses to the plain forward transition probability, since there is no background to
marginalize.  This is what makes the single-`T` mechanism-level development in
`IIT/Phi.lean` exact for `S = univ`, and it is the same collapse PyPhi exhibits
(`condition_tpm` on an empty background is the identity, and `backward_tpm`'s reweighting
factor becomes `1`). -/
lemma sysCauseProb_univ (T : UnitTPM N) (u s t : State N)
    (h : 0 < ∑ v : State N, fullProb T v u) :
    sysCauseProb T Finset.univ u s t = fullProb T t s := by
  rw [sysCauseProb, fullProb]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hw : ∀ w : State N,
      T.prob i (merge Finset.univ t w) (s i) * bgWeight T Finset.univ u w
        = T.prob i t (s i) := by
    intro w
    rw [merge_univ, bgWeight_univ T u w h, mul_one]
  rw [Finset.sum_congr rfl fun w _ => hw w, Finset.sum_const, card_state, nsmul_eq_mul]
  simp only [Finset.card_univ, Fintype.card_fin]
  have h2 : ((2 : ℝ) ^ N) ≠ 0 := by positivity
  push_cast
  field_simp

/-- `p_c(s)` `[IIT4, Eq 8]`: the unconstrained cause probability. -/
noncomputable def sysUncCause (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) : ℝ :=
  avgOverStates fun t => sysCauseProb T S u s t

lemma sysUncCause_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) :
    0 ≤ sysUncCause T S u s := by
  rw [sysUncCause, avgOverStates]
  exact div_nonneg (Finset.sum_nonneg fun t _ => sysCauseProb_nonneg T S u s t)
    (by positivity)

/-- `p_c^-(s̄ | s)` `[IIT4, Eq 9]`: the backward cause probability, by Bayes' rule with a
uniform prior over the system's prior states.  This is the *selectivity* term of `ii_c`. -/
noncomputable def sysBackCause (T : UnitTPM N) (S : Finset (Fin N)) (u s t : State N) : ℝ :=
  sysCauseProb T S u s t / ((2 : ℝ) ^ S.card * sysUncCause T S u s)

lemma sysBackCause_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u s t : State N) :
    0 ≤ sysBackCause T S u s t := by
  rw [sysBackCause]
  refine div_nonneg (sysCauseProb_nonneg T S u s t) ?_
  exact mul_nonneg (by positivity) (sysUncCause_nonneg T S u s)

/-- `ii_c(s, s̄)` `[IIT4, Eq 7]`: intrinsic cause information.  As at the mechanism level
the selectivity is the *backward* probability while the informativeness compares the
*forward* one against its unconstrained value. -/
noncomputable def sysIiC (T : UnitTPM N) (S : Finset (Fin N)) (u s t : State N) : ℝ :=
  sysBackCause T S u s t * Real.logb 2 (sysCauseProb T S u s t / sysUncCause T S u s)

/-- **`[IIT4, Eq 10]`**: the existence condition on the effect side.  "A system `S` in
state `s` has cause-effect power (it takes and makes a difference) if it raises the
probability of a possible effect state compared to chance, which is to say compared to
its unconstrained probability." -/
def HasEffectPower (T : UnitTPM N) (S : Finset (Fin N)) (u s t : State N) : Prop :=
  0 < Real.logb 2 (sysEffProb T S u s t / sysUncEff T S u t)

/-- **`[IIT4, Eq 11]`**: the existence condition on the cause side -- "the probability of
the current state is raised above chance by a possible cause state". -/
def HasCausePower (T : UnitTPM N) (S : Finset (Fin N)) (u s t : State N) : Prop :=
  0 < Real.logb 2 (sysCauseProb T S u s t / sysUncCause T S u s)

/-- Positive intrinsic effect information witnesses `[IIT4, Eq 10]`: the selectivity
factor is a probability, so a positive product forces positive informativeness.  No
positivity of the selectivity need be assumed -- a zero selectivity would make the product
zero, so `0 < ii_e` supplies it. -/
lemma hasEffectPower_of_sysIiE_pos {T : UnitTPM N} {S : Finset (Fin N)} {u s t : State N}
    (h : 0 < sysIiE T S u s t) : HasEffectPower T S u s t := by
  have hp : 0 < sysEffProb T S u s t := by
    rcases (sysEffProb_nonneg T S u s t).lt_or_eq with hlt | heq
    · exact hlt
    · rw [sysIiE, ← heq, zero_mul] at h
      exact absurd h (lt_irrefl 0)
  by_contra hcon
  rw [HasEffectPower, not_lt] at hcon
  rw [sysIiE] at h
  nlinarith [h, hp, hcon]

/-- Positive intrinsic cause information witnesses `[IIT4, Eq 11]`, on the same terms. -/
lemma hasCausePower_of_sysIiC_pos {T : UnitTPM N} {S : Finset (Fin N)} {u s t : State N}
    (h : 0 < sysIiC T S u s t) : HasCausePower T S u s t := by
  have hp : 0 < sysBackCause T S u s t := by
    rcases (sysBackCause_nonneg T S u s t).lt_or_eq with hlt | heq
    · exact hlt
    · rw [sysIiC, ← heq, zero_mul] at h
      exact absurd h (lt_irrefl 0)
  by_contra hcon
  rw [HasCausePower, not_lt] at hcon
  rw [sysIiC] at h
  nlinarith [h, hp, hcon]

/-! ## The system's maximal cause–effect state `[IIT4, Eqs 12, 13]` -/

/-- The set of maximal **effect** states of the system `[IIT4, Eq 12]`, all ties kept per
`[IIT4, S1 Text]`. -/
noncomputable def sysMaxEffStates (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) :
    Finset (State N) :=
  argmaxSet (sysIiE T S u s)

/-- The set of maximal **cause** states of the system `[IIT4, Eq 12]`, cause side. -/
noncomputable def sysMaxCauseStates (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) :
    Finset (State N) :=
  argmaxSet (sysIiC T S u s)

lemma sysMaxEffStates_nonempty (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) :
    (sysMaxEffStates T S u s).Nonempty :=
  argmaxSet_nonempty _

lemma sysMaxCauseStates_nonempty (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) :
    (sysMaxCauseStates T S u s).Nonempty :=
  argmaxSet_nonempty _

/-- `ii_e(T_e, s)` `[IIT4, Eq 13]`: the system's intrinsic effect information, the value at
a maximal effect state. -/
noncomputable def sysIiEmax (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) : ℝ :=
  (sysMaxEffStates T S u s).sup' (sysMaxEffStates_nonempty T S u s) (sysIiE T S u s)

/-- `ii_c(T_c, s)` `[IIT4, Eq 13]`, cause side. -/
noncomputable def sysIiCmax (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) : ℝ :=
  (sysMaxCauseStates T S u s).sup' (sysMaxCauseStates_nonempty T S u s) (sysIiC T S u s)

/-! ## Purview witnesses `[IIT4, Eq 45]`

`IIT/Phi.lean` computes the *value* `φ_e(m)` as a maximum over purviews `[IIT4, Eq 46]`.
Relations need the *witness*: which purview, in which state, attains it.  That is
`[IIT4, Eq 45]`, and it is what `z*_c(m)`, `z*_e(m)` denote.

All ties are kept here, following `[IIT4, S1 Text]`; breaking them is a separate step,
because `[IIT4, S1 Text]` gives guidance here ("the one that supports the most
relations with other distinctions"), not a decision procedure. -/

/-- A purview together with a state of it, as the set of `(unit, state)` tuples — the
`StatedPurview` encoding used for distinctions and relations. -/
def stated (Z : Finset (Fin N)) (z : State N) : StatedPurview N :=
  Z.image fun k => (k, z k)

@[simp] lemma mem_stated {Z : Finset (Fin N)} {z : State N} {p : Fin N × Bool} :
    p ∈ stated Z z ↔ p.1 ∈ Z ∧ p.2 = z p.1 := by
  simp only [stated, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨hk, rfl⟩
  · rintro ⟨h1, h2⟩; exact ⟨p.1, h1, by cases p; simp_all⟩

/-- `stated Z z` is a genuine purview-in-state: no unit carries two states. -/
lemma stated_functional {Z : Finset (Fin N)} {z : State N} {i : Fin N} {b b' : Bool}
    (h : (i, b) ∈ stated Z z) (h' : (i, b') ∈ stated Z z) : b = b' := by
  rw [mem_stated] at h h'
  exact h.2.trans h'.2.symm

lemma card_stated (Z : Finset (Fin N)) (z : State N) : (stated Z z).card = Z.card :=
  Finset.card_image_of_injective _ fun a b h => (Prod.mk.injEq _ _ _ _ ▸ h).1

/-- The candidate effect purviews-with-state of a mechanism: every `Z ⊆ S` paired with
every maximal effect state in `Z` `[IIT4, Eq 36]`. -/
noncomputable def effCandidates (T : UnitTPM N) (S M : Finset (Fin N)) (m : State N) :
    Finset (Finset (Fin N) × State N) :=
  S.powerset.biUnion fun Z => (maxEffStates T M m Z).image fun z => (Z, z)

/-- The candidate cause purviews-with-state of a mechanism. -/
noncomputable def causeCandidates (T : UnitTPM N) (S M : Finset (Fin N)) (m : State N) :
    Finset (Finset (Fin N) × State N) :=
  S.powerset.biUnion fun Z => (maxCauseStates T M m Z).image fun z => (Z, z)

lemma effCandidates_nonempty (T : UnitTPM N) (S M : Finset (Fin N)) (m : State N) :
    (effCandidates T S M m).Nonempty := by
  obtain ⟨z, hz⟩ := argmaxSet_nonempty (iiE T M m ∅)
  refine ⟨(∅, z), ?_⟩
  rw [effCandidates, Finset.mem_biUnion]
  exact ⟨∅, Finset.empty_mem_powerset S, Finset.mem_image_of_mem _ hz⟩

lemma causeCandidates_nonempty (T : UnitTPM N) (S M : Finset (Fin N)) (m : State N) :
    (causeCandidates T S M m).Nonempty := by
  obtain ⟨z, hz⟩ := argmaxSet_nonempty (iiC T M m ∅)
  refine ⟨(∅, z), ?_⟩
  rw [causeCandidates, Finset.mem_biUnion]
  exact ⟨∅, Finset.empty_mem_powerset S, Finset.mem_image_of_mem _ hz⟩

section Witness

open scoped Classical

/-- **`z*_e(m)`** `[IIT4, Eq 45]`: the maximally irreducible effect purviews-with-state of
a mechanism, keeping all ties. -/
noncomputable def maxEffPurviews (T : UnitTPM N) (S M : Finset (Fin N)) (m : State N) :
    Finset (Finset (Fin N) × State N) :=
  (effCandidates T S M m).filter fun p =>
    ∀ q ∈ effCandidates T S M m, phiEat T M m q.1 q.2 ≤ phiEat T M m p.1 p.2

/-- **`z*_c(m)`** `[IIT4, Eq 45]`, cause side. -/
noncomputable def maxCausePurviews (T : UnitTPM N) (S M : Finset (Fin N)) (m : State N) :
    Finset (Finset (Fin N) × State N) :=
  (causeCandidates T S M m).filter fun p =>
    ∀ q ∈ causeCandidates T S M m, phiCat T q.1 q.2 M m ≤ phiCat T p.1 p.2 M m

lemma maxEffPurviews_nonempty (T : UnitTPM N) (S M : Finset (Fin N)) (m : State N) :
    (maxEffPurviews T S M m).Nonempty := by
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (effCandidates T S M m)
    (fun q => phiEat T M m q.1 q.2) (effCandidates_nonempty T S M m)
  exact ⟨p, Finset.mem_filter.2 ⟨hp, hmax⟩⟩

lemma maxCausePurviews_nonempty (T : UnitTPM N) (S M : Finset (Fin N)) (m : State N) :
    (maxCausePurviews T S M m).Nonempty := by
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (causeCandidates T S M m)
    (fun q => phiCat T q.1 q.2 M m) (causeCandidates_nonempty T S M m)
  exact ⟨p, Finset.mem_filter.2 ⟨hp, hmax⟩⟩

/-- The value at a maximally irreducible effect purview is `φ_e(m)` `[IIT4, Eq 46]`: the
witness set of Eq 45 and the value of Eq 46 agree, so `IIT/Phi.lean`'s `phiEmech` really is
the maximum attained at these witnesses. -/
theorem phiEat_of_mem_maxEffPurviews (T : UnitTPM N) (S M : Finset (Fin N)) (m : State N)
    {p : Finset (Fin N) × State N} (hp : p ∈ maxEffPurviews T S M m) :
    phiEat T M m p.1 p.2 = phiEmech T S M m := by
  obtain ⟨hpmem, hpmax⟩ := Finset.mem_filter.1 hp
  refine le_antisymm ?_ ?_
  · rw [phiEmech]
    refine le_trans ?_ (Finset.le_sup' (f := fun Z => phiEpurview T M m Z)
      (Finset.mem_powerset.2 (?_ : p.1 ⊆ S)))
    · rw [phiEpurview]
      obtain ⟨Z, hZ, hz⟩ := Finset.mem_biUnion.1 hpmem
      obtain ⟨z, hzmem, hzeq⟩ := Finset.mem_image.1 hz
      have h1 : p.1 = Z := (Prod.ext_iff.1 hzeq).1.symm
      have h2 : p.2 = z := (Prod.ext_iff.1 hzeq).2.symm
      subst h1; subst h2
      exact Finset.le_sup' (f := fun w => phiEat T M m p.1 w) hzmem
    · obtain ⟨Z, hZ, hz⟩ := Finset.mem_biUnion.1 hpmem
      obtain ⟨z, -, hzeq⟩ := Finset.mem_image.1 hz
      have h1 : p.1 = Z := (Prod.ext_iff.1 hzeq).1.symm
      subst h1
      exact Finset.mem_powerset.1 hZ
  · rw [phiEmech]
    refine Finset.sup'_le _ _ fun Z hZ => ?_
    rw [phiEpurview]
    refine Finset.sup'_le _ _ fun z hz => ?_
    exact hpmax (Z, z) (Finset.mem_biUnion.2 ⟨Z, hZ, Finset.mem_image_of_mem _ hz⟩)

end Witness


/-! ## Directional system partitions `[IIT4, Eqs 14-16]`

These are **not** the mechanism partitions of `[IIT4, Eq 38]`.  A system partition splits
`S` into `k ≥ 2` nonempty blocks and gives each block a *direction*, saying whether its
inputs, its outputs, or both are severed.

PyPhi's default scheme is `SYSTEM_PARTITION_TYPE = "SET_UNI/BI"`
(`_unidirectional_set_partitions`): every nontrivial set partition of the units, crossed
with every assignment of `Direction.CAUSE / EFFECT / BIDIRECTIONAL` to the blocks — and,
since `SYSTEM_PARTITION_INCLUDE_COMPLETE` defaults to `False`, without the complete
partition.  Its `cut_matrix` construction is exactly `[IIT4, Eq 16]`: a `CAUSE` block has
`cut_matrix[S \ p, p] = 1`, an `EFFECT` block has `cut_matrix[p, S \ p] = 1`, and
`BIDIRECTIONAL` sets both. -/

/-- The direction label `δᵢ ∈ {←, →, ↔}` of `[IIT4, Eq 15]`. -/
inductive Dir where
  /-- `←`: the block's inputs are severed (PyPhi `Direction.CAUSE`). -/
  | inputs : Dir
  /-- `→`: the block's outputs are severed (PyPhi `Direction.EFFECT`). -/
  | outputs : Dir
  /-- `↔`: both (PyPhi `Direction.BIDIRECTIONAL`). -/
  | both : Dir
  deriving DecidableEq

instance : Fintype Dir where
  elems := {Dir.inputs, Dir.outputs, Dir.both}
  complete := by intro x; cases x <;> decide

/-- A **directional system partition** `[IIT4, Eqs 14, 15]`: a set partition of `S` into
`k ≥ 2` nonempty blocks, each carrying a direction. -/
structure SysPartition (N : ℕ) (S : Finset (Fin N)) where
  /-- The blocks `S⁽ⁱ⁾`. -/
  parts : Finset (Finset (Fin N))
  /-- The direction `δᵢ` of each block. -/
  dir : Finset (Fin N) → Dir
  parts_nonempty : ∀ p ∈ parts, p.Nonempty
  parts_subset : ∀ p ∈ parts, p ⊆ S
  parts_disjoint : ∀ p ∈ parts, ∀ q ∈ parts, p ≠ q → Disjoint p q
  parts_cover : ∀ i ∈ S, ∃ p ∈ parts, i ∈ p
  /-- `k ≥ 2` `[IIT4, Eq 14]`; PyPhi's `set_partitions(..., nontrivial=True)`. -/
  two_le : 2 ≤ parts.card

namespace SysPartition

variable {S : Finset (Fin N)} (θ : SysPartition N S)

/-- `X⁽ⁱ⁾` `[IIT4, Eq 16]`: the units whose inputs to the block `p` have been severed. -/
noncomputable def cutSet (p : Finset (Fin N)) : Finset (Fin N) :=
  match θ.dir p with
  | Dir.inputs => S \ p
  | Dir.both => S \ p
  | Dir.outputs =>
      (θ.parts.filter fun q => q ≠ p ∧ (θ.dir q = Dir.outputs ∨ θ.dir q = Dir.both)).sup id

/-- The block containing a given unit. -/
noncomputable def partOf (j : Fin N) : Finset (Fin N) :=
  (θ.parts.filter fun p => j ∈ p).sup id

lemma partOf_eq {p : Finset (Fin N)} (hp : p ∈ θ.parts) {j : Fin N} (hj : j ∈ p) :
    θ.partOf j = p := by
  have hfil : θ.parts.filter (fun q => j ∈ q) = {p} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hq, hjq⟩
      by_contra hne
      exact absurd hj (Finset.disjoint_left.1 (θ.parts_disjoint q hq p hp hne) hjq)
    · rintro rfl
      exact ⟨hp, hj⟩
  rw [partOf, hfil, Finset.sup_singleton, id]

lemma cutSet_subset (p : Finset (Fin N)) (hp : p ∈ θ.parts) : θ.cutSet p ⊆ S := by
  rw [cutSet]
  cases hd : θ.dir p
  · exact Finset.sdiff_subset
  · refine Finset.sup_le fun q hq => ?_
    exact θ.parts_subset q (Finset.mem_filter.1 hq).1
  · exact Finset.sdiff_subset

/-- A block whose *inputs* are cut loses all of `S \ p`, which is nonempty since
`k ≥ 2`. -/
lemma cutSet_nonempty_of_inputs {p : Finset (Fin N)} (hp : p ∈ θ.parts)
    (hd : θ.dir p = Dir.inputs ∨ θ.dir p = Dir.both) : (θ.cutSet p).Nonempty := by
  classical
  obtain ⟨q, hq, hqp⟩ : ∃ q ∈ θ.parts, q ≠ p := by
    by_contra hcon
    push Not at hcon
    have hsub : θ.parts ⊆ {p} := fun q hq => Finset.mem_singleton.2 (hcon q hq)
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this
    have := θ.two_le
    omega
  obtain ⟨j, hj⟩ := θ.parts_nonempty q hq
  have hjS : j ∈ S := θ.parts_subset q hq hj
  have hjp : j ∉ p := Finset.disjoint_left.1 (θ.parts_disjoint q hq p hp hqp) hj
  rw [cutSet]
  rcases hd with hd | hd <;> rw [hd]
  · exact ⟨j, Finset.mem_sdiff.2 ⟨hjS, hjp⟩⟩
  · exact ⟨j, Finset.mem_sdiff.2 ⟨hjS, hjp⟩⟩

/-- **Every directional system partition severs something**, so the system MIP never
divides by zero.

The argument is a small case analysis, and it is genuinely necessary: for a single block
with direction `→` the cut set *can* be empty (if every other block has direction `←`).
What cannot happen is that *all* blocks have empty cut sets — a block with `←` or `↔`
always loses `S \ p`, and if every block has `→` then each loses the union of the
others. -/
lemma exists_cutSet_nonempty : ∃ p ∈ θ.parts, (θ.cutSet p).Nonempty := by
  classical
  by_cases hall : ∀ p ∈ θ.parts, θ.dir p = Dir.outputs
  · -- every block has direction `→`: any block loses all the others
    obtain ⟨p, hp⟩ : θ.parts.Nonempty := by
      rw [← Finset.card_pos]
      have := θ.two_le
      omega
    obtain ⟨q, hq, hqp⟩ : ∃ q ∈ θ.parts, q ≠ p := by
      by_contra hcon
      push Not at hcon
      have hsub : θ.parts ⊆ {p} := fun r hr => Finset.mem_singleton.2 (hcon r hr)
      have := Finset.card_le_card hsub
      rw [Finset.card_singleton] at this
      have := θ.two_le
      omega
    obtain ⟨j, hj⟩ := θ.parts_nonempty q hq
    refine ⟨p, hp, ?_⟩
    rw [cutSet, hall p hp]
    have hmem : q ∈ θ.parts.filter
        fun r => r ≠ p ∧ (θ.dir r = Dir.outputs ∨ θ.dir r = Dir.both) :=
      Finset.mem_filter.2 ⟨hq, hqp, Or.inl (hall q hq)⟩
    exact ⟨j, Finset.mem_sup.2 ⟨q, hmem, hj⟩⟩
  · -- some block has direction `←` or `↔`
    push Not at hall
    obtain ⟨p, hp, hd⟩ := hall
    refine ⟨p, hp, θ.cutSet_nonempty_of_inputs hp ?_⟩
    cases hdp : θ.dir p
    · exact Or.inl rfl
    · exact absurd hdp hd
    · exact Or.inr rfl

end SysPartition

/-- The partitioned system effect probability `[IIT4, Eqs 17, 18]`: unit `j`, lying in
block `p`, has its inputs from `X⁽ᵖ⁾` marginalized uniformly while everything else stays
at the current state. -/
noncomputable def sysPartEffProb (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (θ : SysPartition N S) (s t : State N) : ℝ :=
  ∏ j ∈ S, effUnit T (θ.cutSet (θ.partOf j))ᶜ (merge S s u) j (t j)

lemma sysPartEffProb_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (θ : SysPartition N S) (s t : State N) : 0 ≤ sysPartEffProb T S u θ s t :=
  Finset.prod_nonneg fun j _ => effUnit_nonneg T _ _ j (t j)

/-- The partitioned system cause probability, the cause-side analogue of
`[IIT4, Eqs 17, 18]`. -/
noncomputable def sysPartCauseProb (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (θ : SysPartition N S) (s t : State N) : ℝ :=
  ∏ j ∈ S, ((∑ w : State N,
      effUnit T (θ.cutSet (θ.partOf j))ᶜ (merge S t w) j (s j) * bgWeight T S u w)
    / (2 : ℝ) ^ S.card)

lemma sysPartCauseProb_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (θ : SysPartition N S) (s t : State N) : 0 ≤ sysPartCauseProb T S u θ s t := by
  refine Finset.prod_nonneg fun j _ => div_nonneg ?_ (by positivity)
  exact Finset.sum_nonneg fun w _ =>
    mul_nonneg (effUnit_nonneg T _ _ j (s j)) (bgWeight_nonneg T S u w)

/-- The system MIP normalizer `∑ᵢ |S⁽ⁱ⁾| |X⁽ⁱ⁾|` `[IIT4, Eq 23]`.

This is PyPhi's `GeneralKCut.normalization_factor = 1 / np.sum(cut_matrix)`: the cut
matrix has a `1` exactly at each severed connection, and the connections severed into
block `p` number `|p| · |X⁽ᵖ⁾|`. -/
noncomputable def sysCutCount {S : Finset (Fin N)} (θ : SysPartition N S) : ℕ :=
  ∑ p ∈ θ.parts, p.card * (θ.cutSet p).card

/-- **The system normalizer is never zero.**  `[IIT4, Eq 14]` requires `k ≥ 2` blocks, and
that alone forces some block to have both a nonempty mechanism part and a nonempty cut
set: if any block severs its inputs the rest of `S` is cut from it, and if every block
severs only its outputs then each block is cut by the others.  Without this,
`normalizedSysPhiAt` would divide by zero, and Lean's `x / 0 = 0` would make such a
partition an artificial minimum -- which `[IIT4, Eq 38]`'s disintegrating
condition averts at the mechanism level (`cutCount_pos`). -/
theorem sysCutCount_pos {S : Finset (Fin N)} (θ : SysPartition N S) :
    0 < sysCutCount θ := by
  classical
  have h1 : 1 < θ.parts.card := lt_of_lt_of_le one_lt_two θ.two_le
  have other : ∀ r ∈ θ.parts, ∃ q ∈ θ.parts, q ≠ r :=
    fun r _ => Finset.exists_mem_ne h1 r
  have key : ∃ r ∈ θ.parts, (θ.cutSet r).Nonempty := by
    by_cases hall : ∀ r ∈ θ.parts, θ.dir r = Dir.outputs
    · obtain ⟨p, hp⟩ := Finset.card_pos.1 (by omega : 0 < θ.parts.card)
      obtain ⟨q, hq, hqp⟩ := other p hp
      obtain ⟨j, hj⟩ := θ.parts_nonempty q hq
      refine ⟨p, hp, ⟨j, ?_⟩⟩
      simp only [SysPartition.cutSet, hall p hp]
      exact Finset.mem_sup.2 ⟨q, Finset.mem_filter.2 ⟨hq, hqp, Or.inl (hall q hq)⟩, hj⟩
    · push_neg at hall
      obtain ⟨r, hr, hdr⟩ := hall
      obtain ⟨q, hq, hqr⟩ := other r hr
      obtain ⟨j, hj⟩ := θ.parts_nonempty q hq
      have hjS : j ∈ S := θ.parts_subset q hq hj
      have hjr : j ∉ r := fun hjr =>
        (Finset.disjoint_left.1 (θ.parts_disjoint q hq r hr hqr) hj) hjr
      have hcut : θ.cutSet r = S \ r := by
        cases hd : θ.dir r with
        | inputs => simp [SysPartition.cutSet, hd]
        | both => simp [SysPartition.cutSet, hd]
        | outputs => exact absurd hd hdr
      exact ⟨r, hr, ⟨j, by rw [hcut]; exact Finset.mem_sdiff.2 ⟨hjS, hjr⟩⟩⟩
  obtain ⟨r, hr, hne⟩ := key
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨r, hr, ?_⟩
  exact Nat.mul_pos (Finset.card_pos.2 (θ.parts_nonempty r hr)) (Finset.card_pos.2 hne)

/-- Integrated **effect** information of the system for a partition `[IIT4, Eq 19]`. -/
noncomputable def sysPhiE (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (θ : SysPartition N S) (s t : State N) : ℝ :=
  sysEffProb T S u s t *
    pos (Real.logb 2 (sysEffProb T S u s t / sysPartEffProb T S u θ s t))

/-- Integrated **cause** information of the system for a partition `[IIT4, Eq 20]`. -/
noncomputable def sysPhiC (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (θ : SysPartition N S) (s t : State N) : ℝ :=
  sysBackCause T S u s t *
    pos (Real.logb 2 (sysCauseProb T S u s t / sysPartCauseProb T S u θ s t))

lemma sysPhiE_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (θ : SysPartition N S) (s t : State N) : 0 ≤ sysPhiE T S u θ s t :=
  mul_nonneg (sysEffProb_nonneg T S u s t) (pos_nonneg _)

lemma sysPhiC_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (θ : SysPartition N S) (s t : State N) : 0 ≤ sysPhiC T S u θ s t :=
  mul_nonneg (sysBackCause_nonneg T S u s t) (pos_nonneg _)

/-- `φ_s` of a partition **at a fixed cause--effect state pair** `[IIT4, Eq 21]`: the
smaller of the two directions, as `[IIT4]` requires, with the pair held fixed across
both sides and across every partition.

`[IIT4, Eq 12]` selects a single pair `s' = (s'_c, s'_e)` *before* partitioning -- "having
identified the maximal cause-effect state `s'` ... the next step is to evaluate whether
the system specifies [it] ... in a way that is irreducible" -- so the state may not be
re-chosen per partition, nor chosen independently on the two sides. -/
noncomputable def sysPhiAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (θ : SysPartition N S) (s tc te : State N) : ℝ :=
  min (sysPhiC T S u θ s tc) (sysPhiE T S u θ s te)

lemma sysPhiAt_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (θ : SysPartition N S) (s tc te : State N) : 0 ≤ sysPhiAt T S u θ s tc te :=
  le_min (sysPhiC_nonneg T S u θ s tc) (sysPhiE_nonneg T S u θ s te)

/-- The normalized quantity minimized by the system MIP `[IIT4, Eq 23]`, at a fixed
cause--effect state pair. -/
noncomputable def normalizedSysPhiAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (θ : SysPartition N S) (s tc te : State N) : ℝ :=
  sysPhiAt T S u θ s tc te / (sysCutCount θ : ℝ)

section SysFintype

open scoped Classical

noncomputable instance instFintypeSysPartition (S : Finset (Fin N)) :
    Fintype (SysPartition N S) :=
  Fintype.ofInjective
    (fun θ : SysPartition N S => (θ.parts, θ.dir))
    (by
      intro θ1 θ2 h
      have h1 : θ1.parts = θ2.parts := congrArg Prod.fst h
      have h2 : θ1.dir = θ2.dir := congrArg Prod.snd h
      cases θ1
      cases θ2
      simp only at h1 h2
      subst h1
      subst h2
      rfl)

/-- The system MIP **for a given cause--effect state pair** `[IIT4, Eq 22]`. -/
noncomputable def sysMipSetAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (s tc te : State N) : Finset (SysPartition N S) :=
  argminSet fun θ => normalizedSysPhiAt T S u θ s tc te

/-- `φ_s` for a given cause--effect state pair: its value at *that pair's own* minimum
information partition, which is the quantity `[IIT4, S1 Text]` maximizes over ties.

When several system partitions tie on the normalized ratio but differ in unnormalized
`φ_s`, the parenthetical of `[IIT4, p 18]` immediately after Eq 23 selects the one with the
largest unnormalized `φ_s`, and that is the supremum taken here.  `sysCutCount_pos` rules
out the other way a partition could be artificially optimal, division by zero. -/
noncomputable def sysPhiOfState (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (s tc te : State N) : ℝ :=
  sup'OrZero (sysMipSetAt T S u s tc te) fun θ => sysPhiAt T S u θ s tc te

lemma sysPhiOfState_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (s tc te : State N) : 0 ≤ sysPhiOfState T S u s tc te :=
  sup'OrZero_nonneg fun θ _ => sysPhiAt_nonneg T S u θ s tc te

/-- **`φ_s`** `[IIT4, Eq 22]` with `[IIT4, S1 Text]`'s tie rule: among the cause--effect
states satisfying `[IIT4, Eq 12]`, "we select the one for which the system specifies the
maximal integrated information `φ_s(T_e, T_c, s, θ')` **over its minimum partition
`θ'`**".  So the maximum over tied states is taken *outside* the minimum over partitions:
each candidate pair is scored at its own MIP, and the best pair wins.

Taking the supremum inside each partition instead would interchange the quantifiers and
can return a value attained at no tied state at all.

`sup'OrZero` returns `0` when no `k ≥ 2` partition exists, i.e. for an empty or a
single-unit system.  PyPhi agrees on the empty case
(`ShortCircuitConditions.NO_SUBSYSTEM`) but **not** on the single-unit one:
`_unidirectional_set_partitions` yields the complete partition unconditionally when
`|S| = 1`, and with `SINGLE_MICRO_NODES_WITH_SELFLOOPS_HAVE_PHI = True` (its default)
PyPhi reports a nonzero `φ_s` there -- `1.0` for a single COPY unit, and `1.0` for
`S = {A}` of the AND/OR system in state `(1,1)`.  We follow `[IIT4, Eq 14]`'s `k ≥ 2`
requirement instead, so the two differ at `|S| = 1`; the differential tests in `test/`
range over `|S| ≥ 2`. -/
noncomputable def sysPhi (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (s : State N) : ℝ :=
  sup'OrZero ((sysMaxCauseStates T S u s) ×ˢ (sysMaxEffStates T S u s))
    fun p => sysPhiOfState T S u s p.1 p.2

lemma sysPhi_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) :
    0 ≤ sysPhi T S u s :=
  sup'OrZero_nonneg fun p _ => sysPhiOfState_nonneg T S u s p.1 p.2

/-! ### The candidate cause--effect states depend only on the state of `S`

`argmaxSet` in `sysMaxEffStates` and `sysMaxCauseStates` ranges over all `2^N` substrate
states, while `[IIT4, Eqs 5, 7]` range over `Ω_S`.  The two agree: every quantity below
depends on the candidate state `t` only through its restriction to `S`, so the argmax is
a union of fibres of that restriction, each of size `2^(N - |S|)`, and `φ_s` is constant
on each fibre.  Nothing computed here changes; what changes is the *cardinality* of the
tie set, which is why `test/leanref.py` enumerates one representative per state of `S`
before reporting how many ties there are. -/

section Fibres

variable {T : UnitTPM N} {S : Finset (Fin N)} {u s : State N}

lemma merge_congr {t t' w : State N} (h : ∀ i ∈ S, t i = t' i) :
    merge S t w = merge S t' w := by
  funext j
  by_cases hj : j ∈ S
  · simp [merge, hj, h j hj]
  · simp [merge, hj]

lemma sysEffProb_congr {t t' : State N} (h : ∀ i ∈ S, t i = t' i) :
    sysEffProb T S u s t = sysEffProb T S u s t' :=
  Finset.prod_congr rfl fun i hi => by rw [h i hi]

lemma sysUncEff_congr {t t' : State N} (h : ∀ i ∈ S, t i = t' i) :
    sysUncEff T S u t = sysUncEff T S u t' := by
  rw [sysUncEff, sysUncEff, avgOverStates, avgOverStates]
  exact congrArg (· / (2 : ℝ) ^ N) (Finset.sum_congr rfl fun v _ => sysEffProb_congr h)

lemma sysIiE_congr {t t' : State N} (h : ∀ i ∈ S, t i = t' i) :
    sysIiE T S u s t = sysIiE T S u s t' := by
  rw [sysIiE, sysIiE, sysEffProb_congr (T := T) (u := u) (s := s) h, sysUncEff_congr h]

lemma sysCauseProb_congr {t t' : State N} (h : ∀ i ∈ S, t i = t' i) :
    sysCauseProb T S u s t = sysCauseProb T S u s t' :=
  Finset.prod_congr rfl fun i _ => by
    exact congrArg (· / (2 : ℝ) ^ S.card)
      (Finset.sum_congr rfl fun w _ => by rw [merge_congr (w := w) h])

lemma sysBackCause_congr {t t' : State N} (h : ∀ i ∈ S, t i = t' i) :
    sysBackCause T S u s t = sysBackCause T S u s t' := by
  rw [sysBackCause, sysBackCause, sysCauseProb_congr h]

lemma sysIiC_congr {t t' : State N} (h : ∀ i ∈ S, t i = t' i) :
    sysIiC T S u s t = sysIiC T S u s t' := by
  rw [sysIiC, sysIiC, sysBackCause_congr (T := T) (u := u) (s := s) h, sysCauseProb_congr h]

/-- **The tie set of `[IIT4, Eq 12]` is a union of fibres.** -/
theorem mem_sysMaxEffStates_congr {t t' : State N} (h : ∀ i ∈ S, t i = t' i) :
    t ∈ sysMaxEffStates T S u s ↔ t' ∈ sysMaxEffStates T S u s := by
  simp only [sysMaxEffStates, mem_argmaxSet, sysIiE_congr (T := T) (u := u) (s := s) h]

/-- The same on the cause side. -/
theorem mem_sysMaxCauseStates_congr {t t' : State N} (h : ∀ i ∈ S, t i = t' i) :
    t ∈ sysMaxCauseStates T S u s ↔ t' ∈ sysMaxCauseStates T S u s := by
  simp only [sysMaxCauseStates, mem_argmaxSet, sysIiC_congr (T := T) (u := u) (s := s) h]

lemma sysPartEffProb_congr {θ : SysPartition N S} {t t' : State N}
    (h : ∀ i ∈ S, t i = t' i) :
    sysPartEffProb T S u θ s t = sysPartEffProb T S u θ s t' :=
  Finset.prod_congr rfl fun j hj => by rw [h j hj]

lemma sysPartCauseProb_congr {θ : SysPartition N S} {t t' : State N}
    (h : ∀ i ∈ S, t i = t' i) :
    sysPartCauseProb T S u θ s t = sysPartCauseProb T S u θ s t' :=
  Finset.prod_congr rfl fun j _ => by
    exact congrArg (· / (2 : ℝ) ^ S.card)
      (Finset.sum_congr rfl fun w _ => by rw [merge_congr (w := w) h])

lemma sysPhiE_congr {θ : SysPartition N S} {t t' : State N} (h : ∀ i ∈ S, t i = t' i) :
    sysPhiE T S u θ s t = sysPhiE T S u θ s t' := by
  rw [sysPhiE, sysPhiE, sysEffProb_congr (T := T) (u := u) (s := s) h,
    sysPartEffProb_congr (T := T) (u := u) (θ := θ) (s := s) h]

lemma sysPhiC_congr {θ : SysPartition N S} {t t' : State N} (h : ∀ i ∈ S, t i = t' i) :
    sysPhiC T S u θ s t = sysPhiC T S u θ s t' := by
  rw [sysPhiC, sysPhiC, sysBackCause_congr (T := T) (u := u) (s := s) h,
    sysCauseProb_congr (T := T) (u := u) (s := s) h,
    sysPartCauseProb_congr (T := T) (u := u) (θ := θ) (s := s) h]

lemma sysPhiAt_congr {θ : SysPartition N S} {tc tc' te te' : State N}
    (hc : ∀ i ∈ S, tc i = tc' i) (he : ∀ i ∈ S, te i = te' i) :
    sysPhiAt T S u θ s tc te = sysPhiAt T S u θ s tc' te' := by
  rw [sysPhiAt, sysPhiAt, sysPhiC_congr (T := T) (u := u) (θ := θ) (s := s) hc,
    sysPhiE_congr (T := T) (u := u) (θ := θ) (s := s) he]

/-- **`φ_s` at a fixed pair depends only on the pair's restriction to `S`.**  With
`mem_sysMaxEffStates_congr` this says that ranging `argmaxSet` over all `2^N` substrate
states rather than over `Ω_S` leaves `sysPhi` unchanged. -/
theorem sysPhiOfState_congr {tc tc' te te' : State N}
    (hc : ∀ i ∈ S, tc i = tc' i) (he : ∀ i ∈ S, te i = te' i) :
    sysPhiOfState T S u s tc te = sysPhiOfState T S u s tc' te' := by
  classical
  have hnorm : ∀ θ : SysPartition N S,
      normalizedSysPhiAt T S u θ s tc te = normalizedSysPhiAt T S u θ s tc' te' := by
    intro θ
    rw [normalizedSysPhiAt, normalizedSysPhiAt,
      sysPhiAt_congr (T := T) (u := u) (θ := θ) (s := s) hc he]
  rw [sysPhiOfState, sysPhiOfState, sysMipSetAt, sysMipSetAt]
  simp only [argminSet, hnorm]
  exact sup'OrZero_congr (fun θ =>
    sysPhiAt_congr (T := T) (u := u) (θ := θ) (s := s) hc he)

/-- **The enlarged `argmaxSet` changes no value.**  `sysPhi` takes its supremum over the
tie sets as `argmaxSet` produces them, over all of `Ω_U`.  Restricting to any `C` and `E`
that meet every fibre -- one representative per state of `S`, for instance -- gives the
same number.  With `mem_sysMaxEffStates_congr` this is the whole content of the remark
that ranging over `Ω_U` rather than `Ω_S` inflates the *count* of ties and nothing
else. -/
theorem sysPhi_eq_of_reps (C E : Finset (State N))
    (hC : C ⊆ sysMaxCauseStates T S u s) (hE : E ⊆ sysMaxEffStates T S u s)
    (hCf : ∀ t ∈ sysMaxCauseStates T S u s, ∃ t' ∈ C, ∀ i ∈ S, t i = t' i)
    (hEf : ∀ t ∈ sysMaxEffStates T S u s, ∃ t' ∈ E, ∀ i ∈ S, t i = t' i) :
    sup'OrZero (C ×ˢ E) (fun p => sysPhiOfState T S u s p.1 p.2) = sysPhi T S u s := by
  have hnn : ∀ p : State N × State N, 0 ≤ sysPhiOfState T S u s p.1 p.2 :=
    fun p => sysPhiOfState_nonneg T S u s p.1 p.2
  rw [sysPhi]
  refine le_antisymm (sup'OrZero_mono ?_ fun p _ => hnn p)
    (sup'OrZero_le_of_values ?_ fun p _ => hnn p)
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
    exact Finset.mem_product.2 ⟨hC h1, hE h2⟩
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
    obtain ⟨c, hcC, hc⟩ := hCf p.1 h1
    obtain ⟨e, heE, he⟩ := hEf p.2 h2
    exact ⟨(c, e), Finset.mem_product.2 ⟨hcC, heE⟩,
      sysPhiOfState_congr (T := T) (S := S) (u := u) (s := s) hc he⟩

/-- **Each fibre of the tie set has `2 ^ (N - |S|)` states.**  With
`mem_sysMaxEffStates_congr` this is the counting claim: the `[IIT4, Eq 12]` tie set is a
union of `agree S t` fibres, and `card_agree` gives each of them exactly `2 ^ (N - |S|)`
elements, so ranging `argmaxSet` over `Ω_U` rather than `Ω_S` multiplies the number of
ties by that factor while `sysPhiOfState_congr` keeps every value fixed. -/
theorem agree_subset_sysMaxEffStates {t : State N} (h : t ∈ sysMaxEffStates T S u s) :
    agree S t ⊆ sysMaxEffStates T S u s := fun _ ht =>
  (mem_sysMaxEffStates_congr (mem_agree.1 ht)).2 h

/-- The same on the cause side. -/
theorem agree_subset_sysMaxCauseStates {t : State N} (h : t ∈ sysMaxCauseStates T S u s) :
    agree S t ⊆ sysMaxCauseStates T S u s := fun _ ht =>
  (mem_sysMaxCauseStates_congr (mem_agree.1 ht)).2 h

end Fibres

/-! ## PyPhi's rule, and how it relates to `[IIT4, S1 Text]`'s

`pyphi.new_big_phi.sia` does not maximize over the tied cause--effect states.
`Subsystem.intrinsic_information` computes the whole tie set, stores it, and returns
`ties[0]` -- the first in enumeration order -- and `sia` then evaluates every partition
against that one pair.  The branch says so itself, in the docstring of
`system_intrinsic_information`: *"State ties are arbitrarily broken (for now)"*, beside a
`TODO(ties) deal with ties here`.  The machinery for the paper's rule exists in that same
codebase (`STATE_TIE_RESOLUTION = "PHI"`, `resolve_ties.states`) and is wired at the
*mechanism* level -- `find_mip` iterates over all tied states -- but not here.

So PyPhi computes `sysPhiOfState` at one admissible pair where `[IIT4, S1 Text]` takes the
maximum over all of them.  The two theorems below say exactly what that costs. -/

/-- **PyPhi's value never exceeds `[IIT4, Eq 22]`'s.**  Evaluating at one tied pair is one
term of the supremum that `[IIT4, S1 Text]` takes over all of them.  Every disagreement
`test/sweep.py` reports has PyPhi strictly below, as this predicts. -/
theorem sysPhiOfState_le_sysPhi (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    {tc te : State N} (hc : tc ∈ sysMaxCauseStates T S u s)
    (he : te ∈ sysMaxEffStates T S u s) :
    sysPhiOfState T S u s tc te ≤ sysPhi T S u s := by
  rw [sysPhi]
  exact le_sup'OrZero (s := (sysMaxCauseStates T S u s) ×ˢ (sysMaxEffStates T S u s))
    (f := fun p => sysPhiOfState T S u s p.1 p.2) (b := (tc, te))
    (Finset.mem_product.2 ⟨hc, he⟩)

/-- **And it is exact when the maximal cause--effect state is unique on `S`.**  The
hypotheses say the tie sets are single fibres of the restriction to `S`, which is what
`test/sweep.py` measures when it calls a check untied; then every term of the supremum has
the same value, by `sysPhiOfState_congr`.  So PyPhi is exact off the tied set, and the
disagreements are confined to it -- which is what the contingency table reports. -/
theorem sysPhi_eq_of_states_agree (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    {tc te : State N} (hc : tc ∈ sysMaxCauseStates T S u s)
    (he : te ∈ sysMaxEffStates T S u s)
    (huc : ∀ t ∈ sysMaxCauseStates T S u s, ∀ i ∈ S, t i = tc i)
    (hue : ∀ t ∈ sysMaxEffStates T S u s, ∀ i ∈ S, t i = te i) :
    sysPhi T S u s = sysPhiOfState T S u s tc te := by
  refine le_antisymm ?_ (sysPhiOfState_le_sysPhi T S u s hc he)
  rw [sysPhi]
  refine sup'OrZero_le (sysPhiOfState_nonneg T S u s tc te) fun p hp => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
  exact le_of_eq (sysPhiOfState_congr (T := T) (S := S) (u := u) (s := s)
    (huc p.1 h1) (hue p.2 h2))

end SysFintype

/-- **A substrate of fewer than two units admits no system partition.**  `[IIT4, Eq 14]`
asks for `k ≥ 2` nonempty disjoint blocks inside `S`, and two of those already need two
units. -/
theorem isEmpty_sysPartition_of_card_le_one {S : Finset (Fin N)} (hS : S.card ≤ 1) :
    IsEmpty (SysPartition N S) := by
  classical
  refine ⟨fun θ => ?_⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 (lt_of_lt_of_le one_lt_two θ.two_le)
  obtain ⟨i, hi⟩ := θ.parts_nonempty p hp
  obtain ⟨j, hj⟩ := θ.parts_nonempty q hq
  have hij : i ≠ j := fun h =>
    (Finset.disjoint_left.1 (θ.parts_disjoint p hp q hq hpq) hi) (h ▸ hj)
  have : 2 ≤ S.card :=
    Finset.one_lt_card.2 ⟨i, θ.parts_subset p hp hi, j, θ.parts_subset q hq hj, hij⟩
  omega

/-- **`φ_s = 0` below two units.**  This is the deliberate divergence from PyPhi recorded
in `test/singleunit.py`, as a theorem: with no partition to take a minimum over,
`[IIT4, Eq 22]` has nothing to minimize and `sup'OrZero` returns `0`. -/
theorem sysPhi_eq_zero_of_card_le_one (T : UnitTPM N) {S : Finset (Fin N)} (u s : State N)
    (hS : S.card ≤ 1) : sysPhi T S u s = 0 := by
  classical
  haveI := isEmpty_sysPartition_of_card_le_one (N := N) hS
  have hstate : ∀ tc te : State N, sysPhiOfState T S u s tc te = 0 := by
    intro tc te
    rw [sysPhiOfState, sup'OrZero]
    exact dif_neg (by simp [Finset.eq_empty_of_isEmpty (sysMipSetAt T S u s tc te)])
  refine le_antisymm (sup'OrZero_le le_rfl fun p _ => (hstate p.1 p.2).le)
    (sup'OrZero_nonneg fun p _ => (hstate p.1 p.2).ge)

/-! ## Complexes `[IIT4, Eqs 24-26]` -/

/-- **`[IIT4, Eq 24]`**: the maximum of `φ_s` over all candidate substrates within `U`. -/
noncomputable def maxSysPhi (T : UnitTPM N) (U : Finset (Fin N)) (u s : State N) : ℝ :=
  sup'OrZero U.powerset (fun S => sysPhi T S u s)

/-- **`[IIT4, Eq 25]`**: the substrates attaining that maximum, all ties kept. -/
noncomputable def maximalSubstrates (T : UnitTPM N) (U : Finset (Fin N)) (u s : State N) :
    Finset (Finset (Fin N)) :=
  U.powerset.filter fun S => ∀ S' ∈ U.powerset, sysPhi T S' u s ≤ sysPhi T S u s

lemma sysPhi_le_maxSysPhi (T : UnitTPM N) {U S : Finset (Fin N)} (u s : State N)
    (hS : S ∈ U.powerset) : sysPhi T S u s ≤ maxSysPhi T U u s :=
  le_sup'OrZero (f := fun S => sysPhi T S u s) hS

/-- **`[IIT4, Eq 26]`**: `S` is a *complex* when it strictly beats every overlapping
candidate system on `φ_s`.  `[IIT4]` calls this a *sufficient* condition for `S` to be a
maximal substrate.

It is neither weaker nor stronger than being an `[IIT4, Eq 25]` maximizer, and
`IIT/Cond.lean` says exactly how the two differ.  `[IIT4, Eq 26]` compares `S` only
against substrates that *overlap* it, so a complex may lose to a disjoint competitor; and
`[IIT4, Eq 25]`'s `argmax` keeps ties whereas `IsComplex` demands a *strict* maximum, so
tied overlapping substrates yield no complex at all -- see `IsComplex.disjoint_of_ne` and
`test/splitbrain.py` at coupling `w = 1/2`.  Name those two as hypotheses and the
characterizations coincide: `isComplex_iff_mem_argmaxSubstrates`. -/
def IsComplex (T : UnitTPM N) (u : State N) (U S : Finset (Fin N)) (s : State N) : Prop :=
  S ⊆ U ∧ ∀ S' ⊆ U, S' ≠ S → (S ∩ S').Nonempty →
    sysPhi T S' u s < sysPhi T S u s

/-- **At the whole substrate, `[IIT4, Eq 26]` is plain strict maximality.**  The
condition quantifies only over substrates that *overlap* `S`; when `S` is the universe
every nonempty substrate overlaps it, so the intersection hypothesis and the subset
hypothesis both disappear and what remains is that no other nonempty substrate matches
`φ_s`.

This is what `PhiOfComplexAt_univ` and `PhiOfComplexAt_le` assume, stated without the
machinery: for general `N` the development does not construct a witness --
`isComplex_univ_of_pos` exhibits one only at `N = 2`, where every proper subset has at
most one unit and `sysPhi_eq_zero_of_card_le_one` applies -- but the condition is now one
a reader can check on any system, and `test/splitbrain.py` shows numerically where it
holds and where not. -/
theorem isComplex_univ_iff (T : UnitTPM N) (u s : State N) :
    IsComplex T u Finset.univ Finset.univ s ↔
      ∀ S' : Finset (Fin N), S' ≠ Finset.univ → S'.Nonempty →
        sysPhi T S' u s < sysPhi T Finset.univ u s := by
  constructor
  · rintro ⟨-, h⟩ S' hne hnem
    refine h S' (Finset.subset_univ S') hne ?_
    obtain ⟨a, ha⟩ := hnem
    exact ⟨a, Finset.mem_inter.2 ⟨Finset.mem_univ a, ha⟩⟩
  · intro h
    refine ⟨Finset.Subset.refl _, fun S' _ hne hover => ?_⟩
    obtain ⟨a, ha⟩ := hover
    exact h S' hne ⟨a, (Finset.mem_inter.1 ha).2⟩

/-- **`[IIT4, Eq 26]` is satisfied by the empty substrate.**  The condition
quantifies over substrates that *overlap* `S`, and nothing overlaps `∅`.  This is a
property of the source's own formulation, not of the transcription; it is why the
statement that at a symmetric tie no substrate satisfies `[IIT4, Eq 26]` has to be read as
saying that no *nonempty* substrate does. -/
theorem isComplex_empty (T : UnitTPM N) (u s : State N) (U : Finset (Fin N)) :
    IsComplex T u U (∅ : Finset (Fin N)) s := by
  refine ⟨Finset.empty_subset U, fun S' _ _ hne => ?_⟩
  simp only [Finset.empty_inter] at hne
  exact absurd hne (by simp)

lemma IsComplex.unique {T : UnitTPM N} {u s : State N} {U S S' : Finset (Fin N)}
    (h : IsComplex T u U S s) (h' : IsComplex T u U S' s) (hover : (S ∩ S').Nonempty) :
    S = S' := by
  by_contra hne
  have h1 := h.2 S' h'.1 (Ne.symm hne) hover
  have h2 := h'.2 S h.1 hne (by rwa [Finset.inter_comm])
  exact absurd h1 (not_lt.2 h2.le)

/-- **The split brain.**  Two *distinct* complexes are necessarily **disjoint**.

Exclusion (`[IIT4, Eq 26]`) forbids two subjects of experience from sharing any substrate,
but it does *not* forbid two of them outright: `IsComplex` quantifies only over `S'` that
**overlap** `S`, so disjoint maxima coexist without contradiction.  This is exactly IIT's
callosotomy prediction -- sever the corpus callosum and one complex becomes two -- and it
is why `IsComplex.unique` must take `hover` as a hypothesis rather than deriving it.

`test/splitbrain.py` exhibits both regimes on a two-hemisphere model.  With callosal
coupling `w < 1/2` the hemispheres `{A,B}` and `{C,D}` tie at `φ_s` and *both* are
complexes, as this theorem permits.  At `w = 1/2` the ties become **overlapping**
(`{A,C}` and `{B,D}` join them) and no *nonempty* substrate satisfies `[IIT4, Eq 26]`.
That is a statement about `[IIT4, Eq 26]` taken alone: `[IIT4, S1 Text]` prescribes a
fallback in exactly this case -- the tied systems "do not qualify as complexes and we
choose the next best system (based on `φ_s`) that is unique" -- and that fallback needs
the recursive search of `[IIT4, Eqs 24, 25]`.  That search is formalized, as
`complexSearch` in `IIT/Cond.lean`, and related to `[IIT4, Eq 26]` at its first stage by
`isComplex_iff_mem_argmaxSubstrates`; what is not established is the agreement beyond that
stage.  So the tied case is a limit on what this development can certify about
exclusion, not a proof that IIT 4.0 leaves `Φ` undefined. -/
theorem IsComplex.disjoint_of_ne {T : UnitTPM N} {u s : State N} {U S S' : Finset (Fin N)}
    (h : IsComplex T u U S s) (h' : IsComplex T u U S' s) (hne : S ≠ S') : Disjoint S S' := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  by_contra hc
  exact hne (h.unique h' (Finset.nonempty_iff_ne_empty.2 hc))

/-- **A nonempty complex, reduced to one positivity.**  On a two-unit substrate the only
substrates overlapping `U = {0, 1}` and different from it are the two singletons, and
`sysPhi_eq_zero_of_card_le_one` puts both at `0`.  So `[IIT4, Eq 26]` holds of the whole
substrate as soon as `φ_s` is positive there, and `IsComplex` is not an empty predicate.

What is *not* proved here is that positivity for a named `T`: it is a statement about a
logarithm of a product of transition probabilities, and the development computes exact
values inside Lean only at the mechanism level (`IIT/Verify.lean`).  The differential
suites exhibit two-unit systems with `φ_s > 0` -- `test/sweep.py` reports several -- so the
hypothesis is satisfiable, but the witness is numerical rather than machine-checked. -/
theorem isComplex_univ_of_pos {T : UnitTPM 2} {u s : State 2}
    (hpos : 0 < sysPhi T Finset.univ u s) :
    IsComplex T u Finset.univ Finset.univ s := by
  refine ⟨Finset.Subset.refl _, fun S' _ hne _ => ?_⟩
  have hss : S' ⊂ (Finset.univ : Finset (Fin 2)) :=
    lt_of_le_of_ne (Finset.subset_univ S') hne
  have hcard : S'.card ≤ 1 := by
    have := Finset.card_lt_card hss
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [sysPhi_eq_zero_of_card_le_one T u s hcard]
  exact hpos

/-! ## The distinction set `[IIT4, Eq 48]`, relations `[IIT4, Eq 56]`, and `Φ`

The last ingredient is **congruence**: a mechanism specifies a distinction of the complex
only if its cause and effect states agree with the system's own maximal cause–effect state
`s'`.  PyPhi does this in `Concept.resolve_congruence` / `Concept.is_congruent`, which
deletes every distinction having no cause-side *and* effect-side tie congruent with
`sia.system_state`; here the same filter is `Congruent`. -/

/-- The system's maximal **cause** states, as purviews-in-state over `S`: the `s'_c`
of `[IIT4, Eq 48]`.  The effect side is `sysStatedEffect`. -/
noncomputable def sysStatedCause (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) :
    Finset (StatedPurview N) :=
  (sysMaxCauseStates T S u s).image fun t => stated S t

/-- The system's maximal effect states, as purviews-in-state over `S`: the `s'_e` of
`[IIT4, Eq 48]`. -/
noncomputable def sysStatedEffect (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) :
    Finset (StatedPurview N) :=
  (sysMaxEffStates T S u s).image fun t => stated S t

/-- Congruence with the system's cause--effect state `[IIT4, Eq 48]`: the distinction's
stated cause lies inside some maximal system cause state, and its stated effect inside
some maximal system effect state.

**Quantifier choice.**  `[IIT4, Eq 48]` fixes one system state `s' = (s'_c, s'_e)` and
filters every mechanism against it; when the system state is tied, this existential lets
different mechanisms certify against different tied states.  The two readings coincide
whenever `s'` is unique, the generic case; `[IIT4, S1 Text]`'s rule for the tied case
(resolve by `φ_s`, then `Φ`) is not formalized.  `test/condjoin.py` measures what the
choice costs: on its sample the two readings differ on 2 distinction mechanisms of 74, and
only where the system cause-effect state ties. -/
def Congruent (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (zc ze : StatedPurview N) : Prop :=
  (∃ c ∈ sysStatedCause T S u s, zc ⊆ c) ∧ (∃ e ∈ sysStatedEffect T S u s, ze ⊆ e)

section PhiStructure

open scoped Classical

/-- A mechanism specifies a distinction of the complex when it is irreducible and
congruent `[IIT4, Eq 48]`. -/
noncomputable def IsDistinctionMech (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (M : Finset (Fin N)) : Prop :=
  0 < phiD T S M s ∧
    ∃ pc ∈ maxCausePurviews T S M s, ∃ pe ∈ maxEffPurviews T S M s,
      Congruent T S u s (stated pc.1 pc.2) (stated pe.1 pe.2)

/-- **`D`** `[IIT4, Eq 48]`: the mechanisms of `S` specifying a distinction.

**Scope.**  `φ_d` and the maximal purviews here are computed from the substrate TPM `T`,
whose causal marginalization averages every unit outside the *mechanism* uniformly.  For a
candidate system `S ⊊ Fin N` this is *not* the background conditioning of
`[IIT4, Eqs 3, 4]`, which pins `W = U \ S` at `u` on the effect side and reweights it by
`bgWeight` on the cause side; here `S` enters only as the range of candidate
purviews.  These
declarations therefore agree with `[IIT4, Eq 48]` exactly when `S = Finset.univ`, which is
the case the differential tests in `test/` exercise. -/
noncomputable def distinctionMechs (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) :
    Finset (Finset (Fin N)) :=
  S.powerset.filter fun M => IsDistinctionMech T S u s M

lemma mem_distinctionMechs {T : UnitTPM N} {S : Finset (Fin N)} {u s : State N}
    {M : Finset (Fin N)} :
    M ∈ distinctionMechs T S u s ↔ M ⊆ S ∧ IsDistinctionMech T S u s M := by
  rw [distinctionMechs, Finset.mem_filter, Finset.mem_powerset]

/-- The distinction-side sum of `Φ` `[IIT4, Eq 59]`: `∑_{d ∈ D} φ_d`. -/
noncomputable def PhiDistinctions (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) :
    ℝ :=
  ∑ M ∈ distinctionMechs T S u s, phiD T S M s

lemma PhiDistinctions_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) :
    0 ≤ PhiDistinctions T S u s :=
  Finset.sum_nonneg fun M _ => phiD_nonneg T S M s

/-- `∑_{d ∈ D} φ_d ≤ ∑_{M ⊆ S} φ_d`: the congruence filter and the `φ_d > 0` requirement
only remove terms, so `sumPhiD_le` bounds the true distinction sum a fortiori. -/
lemma PhiDistinctions_le_sumPhiD (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) :
    PhiDistinctions T S u s ≤ sumPhiD T S s := by
  rw [PhiDistinctions, sumPhiD]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun M _ _ => phiD_nonneg T S M s
  exact Finset.filter_subset _ _

/-- **`[UB, Eq 6]` for the true distinction sum of a substrate.** -/
theorem PhiDistinctions_le (T : UnitTPM N) (u s : State N) :
    PhiDistinctions T Finset.univ u s ≤ (N : ℝ) ^ 2 / 2 * 2 ^ N :=
  (PhiDistinctions_le_sumPhiD T Finset.univ u s).trans (sumPhiD_le T s)

/-- The empty set is never a distinction mechanism: `[IIT4, Eq 48]` requires `φ_d > 0` and
`phiD_empty_mech` gives `φ_d(∅) = 0`. -/
lemma empty_not_mem_distinctionMechs (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) :
    (∅ : Finset (Fin N)) ∉ distinctionMechs T S u s := fun h => by
  have hpos := ((mem_distinctionMechs.1 h).2).1
  rw [phiD_empty_mech] at hpos
  exact lt_irrefl _ hpos

/-- **`|D| ≤ 2^N - 1`**, the counting hypothesis of `[UB, §2.2, Step 3]`.  The mechanisms
of a substrate are its subsets, of which there are `2^N`, and `∅` is excluded. -/
lemma card_distinctionMechs_le (T : UnitTPM N) (u s : State N) :
    (distinctionMechs T Finset.univ u s).card ≤ 2 ^ N - 1 := by
  classical
  have hsub : distinctionMechs T Finset.univ u s
      ⊆ (Finset.univ : Finset (Fin N)).powerset.erase ∅ := by
    intro M hM
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_powerset.2 (Finset.subset_univ M)⟩
    rintro rfl
    exact empty_not_mem_distinctionMechs T _ u s hM
  refine (Finset.card_le_card hsub).trans_eq ?_
  rw [Finset.card_erase_of_mem (Finset.empty_mem_powerset _), Finset.card_powerset,
    Finset.card_univ, Fintype.card_fin]

/-! ### Relations and `Φ`

To form relations we need each distinction as a `Distinction` bundle, carrying its
purviews-in-state.  Selecting those requires a tie-break, which `[IIT4, S1 Text]` resolves
by maximizing `Φ` itself, a global rule that can still tie.  We therefore parameterize
by an explicit **selector**, and record the tie-break as a hypothesis rather than fixing
one canonical choice. -/

/-- A choice of maximally irreducible cause and effect purviews for each mechanism
`[IIT4, Eq 45]`, constrained to be congruent per `[IIT4, Eq 48]`.

**This is a parameterization, not the `[IIT4, S1 Text]` tie-resolution procedure.** That
procedure has four rules -- for substrates, for system cause-effect states, for mechanism
states within a purview, and across purviews -- of which only the third is imposed here
(as `congruent`). Its cross-purview guidance -- "in case of ties across different
purviews, the maximal cause-effect state will generally correspond to the one that
supports the most relations with other distinctions, which typically favors larger
purviews" -- is not a decision procedure: at this point in the construction
the relations it appeals to are themselves determined by the choice being made,
so instead of formalizing it we quantify over every admissible choice: `PhiOf` takes a
`Selector` as an argument. `test/phioftest.py` shows `Φ` genuinely depends on it. -/
structure Selector (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) where
  /-- The chosen cause purview-with-state. -/
  causeOf : Finset (Fin N) → Finset (Fin N) × State N
  /-- The chosen effect purview-with-state. -/
  effectOf : Finset (Fin N) → Finset (Fin N) × State N
  cause_mem : ∀ M ∈ distinctionMechs T S u s, causeOf M ∈ maxCausePurviews T S M s
  effect_mem : ∀ M ∈ distinctionMechs T S u s, effectOf M ∈ maxEffPurviews T S M s
  cause_nonempty : ∀ M ∈ distinctionMechs T S u s, (stated (causeOf M).1 (causeOf M).2).Nonempty
  effect_nonempty : ∀ M ∈ distinctionMechs T S u s, (stated (effectOf M).1 (effectOf M).2).Nonempty
  /-- The chosen witness must itself be **congruent** with the system cause-effect state.
  `IsDistinctionMech` only asks that *some* congruent witness exist; without this field a
  selector could then pick a different, incongruent tie, contradicting `[IIT4, Eq 48]`.
  PyPhi enforces the same thing: `resolve_ties.purviews` yields *all* maximal purviews and
  `Concept.resolve_congruence` then keeps one congruent with `sia.system_state`. -/
  congruent : ∀ M ∈ distinctionMechs T S u s,
    Congruent T S u s (stated (causeOf M).1 (causeOf M).2)
      (stated (effectOf M).1 (effectOf M).2)

/-- `stated` is nonempty exactly when the purview is. -/
lemma stated_nonempty_iff {Z : Finset (Fin N)} {z : State N} :
    (stated Z z).Nonempty ↔ Z.Nonempty := by
  rw [stated]
  exact Finset.image_nonempty

/-- **A maximally irreducible effect purview of a distinction is nonempty.**  `[IIT4,
Eq 45]` admits `Z = ∅` as a candidate, and `phiEat_empty_purview` shows it specifies
nothing; so once `φ_d(M) > 0` the maximum cannot be attained there. -/
lemma maxEffPurviews_fst_nonempty {T : UnitTPM N} {S M : Finset (Fin N)} {m : State N}
    (hpos : 0 < phiEmech T S M m) {p : Finset (Fin N) × State N}
    (hp : p ∈ maxEffPurviews T S M m) : p.1.Nonempty := by
  rcases Finset.eq_empty_or_nonempty p.1 with h0 | h
  · exfalso
    have := phiEat_of_mem_maxEffPurviews T S M m hp
    rw [h0, phiEat_empty_purview] at this
    exact absurd this.symm hpos.ne'
  · exact h

/-- The same on the cause side. -/
lemma maxCausePurviews_fst_nonempty {T : UnitTPM N} {S M : Finset (Fin N)} {m : State N}
    (hpos : 0 < phiCmech T S M m) {p : Finset (Fin N) × State N}
    (hp : p ∈ maxCausePurviews T S M m) : p.1.Nonempty := by
  rcases Finset.eq_empty_or_nonempty p.1 with h0 | h
  · exfalso
    obtain ⟨-, hmax⟩ := Finset.mem_filter.1 hp
    have hzero : phiCat T p.1 p.2 M m = 0 := by
      rw [h0]; exact phiCat_empty_purview T M m p.2
    have hle : phiCmech T S M m ≤ 0 := by
      rw [phiCmech]
      refine Finset.sup'_le _ _ fun Z hZ => ?_
      rw [phiCpurview]
      refine Finset.sup'_le _ _ fun z hz => ?_
      calc phiCat T Z z M m
          ≤ phiCat T p.1 p.2 M m :=
            hmax (Z, z) (Finset.mem_biUnion.2 ⟨Z, hZ, Finset.mem_image_of_mem _ hz⟩)
        _ = 0 := hzero
    exact absurd hle (not_le.2 hpos)
  · exact h

/-- Every distinction mechanism admits a congruent pair of *nonempty* maximal purviews:
`[IIT4, Eq 48]` supplies the congruent pair, and `φ_d(M) > 0` makes both purviews
nonempty. -/
lemma exists_congruent_pair {T : UnitTPM N} {S : Finset (Fin N)} {u s : State N}
    {M : Finset (Fin N)} (hM : M ∈ distinctionMechs T S u s) :
    ∃ p : (Finset (Fin N) × State N) × (Finset (Fin N) × State N),
      p.1 ∈ maxCausePurviews T S M s ∧ p.2 ∈ maxEffPurviews T S M s ∧
        (stated p.1.1 p.1.2).Nonempty ∧ (stated p.2.1 p.2.2).Nonempty ∧
        Congruent T S u s (stated p.1.1 p.1.2) (stated p.2.1 p.2.2) := by
  obtain ⟨hpos, pc, hpc, pe, hpe, hcong⟩ := (mem_distinctionMechs.1 hM).2
  refine ⟨(pc, pe), hpc, hpe, ?_, ?_, hcong⟩
  · exact stated_nonempty_iff.2
      (maxCausePurviews_fst_nonempty (lt_of_lt_of_le hpos (phiD_le_phiCmech T S M s)) hpc)
  · exact stated_nonempty_iff.2
      (maxEffPurviews_fst_nonempty (lt_of_lt_of_le hpos (phiD_le_phiEmech T S M s)) hpe)

open scoped Classical in
/-- A choice of congruent maximal purviews for every mechanism, arbitrary off the
distinction set. -/
noncomputable def congruentPair (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (M : Finset (Fin N)) : (Finset (Fin N) × State N) × (Finset (Fin N) × State N) :=
  if h : M ∈ distinctionMechs T S u s then (exists_congruent_pair h).choose
  else ((∅, s), (∅, s))

lemma congruentPair_spec {T : UnitTPM N} {S : Finset (Fin N)} {u s : State N}
    {M : Finset (Fin N)} (hM : M ∈ distinctionMechs T S u s) :
    (congruentPair T S u s M).1 ∈ maxCausePurviews T S M s ∧
      (congruentPair T S u s M).2 ∈ maxEffPurviews T S M s ∧
      (stated (congruentPair T S u s M).1.1 (congruentPair T S u s M).1.2).Nonempty ∧
      (stated (congruentPair T S u s M).2.1 (congruentPair T S u s M).2.2).Nonempty ∧
      Congruent T S u s (stated (congruentPair T S u s M).1.1 (congruentPair T S u s M).1.2)
        (stated (congruentPair T S u s M).2.1 (congruentPair T S u s M).2.2) := by
  classical
  rw [congruentPair, dif_pos hM]
  exact (exists_congruent_pair hM).choose_spec

/-- **`Selector` is inhabited.**  Every result below that quantifies over a tie-break --
`distinctions`, `PhiOf`, `sum_distinctions_phi`, `eq16_distinctions` -- therefore has
content: there is something to instantiate it at.  Nothing weaker suffices, since
`Selector` demands a *nonempty* congruent pair while `[IIT4, Eq 48]` demands only a
congruent one. -/
noncomputable instance instNonemptySelector (T : UnitTPM N) (S : Finset (Fin N))
    (u s : State N) : Nonempty (Selector T S u s) :=
  ⟨{ causeOf := fun M => (congruentPair T S u s M).1
     effectOf := fun M => (congruentPair T S u s M).2
     cause_mem := fun M hM => (congruentPair_spec hM).1
     effect_mem := fun M hM => (congruentPair_spec hM).2.1
     cause_nonempty := fun M hM => (congruentPair_spec hM).2.2.1
     effect_nonempty := fun M hM => (congruentPair_spec hM).2.2.2.1
     congruent := fun M hM => (congruentPair_spec hM).2.2.2.2 }⟩

/-- The `Distinction` bundle specified by a mechanism under a given selector. -/
noncomputable def distinctionOf (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (σ : Selector T S u s) (M : Finset (Fin N)) (hM : M ∈ distinctionMechs T S u s) :
    Distinction N where
  mech := M
  zc := stated (σ.causeOf M).1 (σ.causeOf M).2
  ze := stated (σ.effectOf M).1 (σ.effectOf M).2
  zc_nonempty := σ.cause_nonempty M hM
  ze_nonempty := σ.effect_nonempty M hM
  phi := phiD T S M s
  phi_pos := ((mem_distinctionMechs.1 hM).2).1

/-- **`D`** as a `Finset` of `Distinction` bundles `[IIT4, Eq 48]`. -/
noncomputable def distinctions (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (σ : Selector T S u s) : Finset (Distinction N) :=
  (distinctionMechs T S u s).attach.image fun M => distinctionOf T S u s σ M.1 M.2

/-- `card_distinctionMechs_le` transported along the bundling map. -/
lemma card_distinctions_le (T : UnitTPM N) (u s : State N)
    (σ : Selector T Finset.univ u s) :
    (distinctions T Finset.univ u s σ).card ≤ 2 ^ N - 1 := by
  classical
  rw [distinctions]
  exact (Finset.card_image_le.trans_eq (Finset.card_attach)).trans
    (card_distinctionMechs_le T u s)

/-- `relPhi` extended by `0` to the empty set of distinctions. -/
noncomputable def relPhiOrZero (d : Finset (Distinction N)) : ℝ :=
  if h : d.Nonempty then relPhi d h else 0

lemma relPhiOrZero_nonneg (d : Finset (Distinction N)) : 0 ≤ relPhiOrZero d := by
  rw [relPhiOrZero]
  split
  · rename_i h
    rw [relPhi]
    refine mul_nonneg (Nat.cast_nonneg _) ?_
    rw [Finset.le_inf'_iff]
    exact fun D' _ => D'.phiPerUnit_nonneg
  · exact le_refl 0

/-- **`R(D)`** `[IIT4, Eq 56]`: every set of at least two distinctions with `φ_r > 0`. -/
noncomputable def relationSets (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (σ : Selector T S u s) : Finset (Finset (Distinction N)) :=
  (distinctions T S u s σ).powerset.filter fun d =>
    ∃ h : d.Nonempty, 2 ≤ d.card ∧ 0 < relPhi d h

/-- The self-relations `[UB, Eq 9]`: distinctions whose own cause and effect overlap. -/
noncomputable def selfRelationDistinctions (T : UnitTPM N) (S : Finset (Fin N))
    (u s : State N) (σ : Selector T S u s) : Finset (Distinction N) :=
  (distinctions T S u s σ).filter fun d => 0 < selfRelPhi d

/-- **Structure integrated information `Φ`** `[IIT4, Eq 59]`, as a function of the
transition probabilities, the substrate, its state, and a tie-break.

`Φ = ∑_{d ∈ D} φ_d + ∑_{r ∈ R(D)} φ_r + ∑ self-relations`, with `D` cut down by
irreducibility and congruence `[IIT4, Eq 48]` and `R(D)` by `φ_r > 0` `[IIT4, Eq 56]`.
By `[IIT4, Eq 58]` this is the `Φ`-structure of a *complex*, so the intended use is under
`IsComplex`; `PhiOfComplex` records that. -/
noncomputable def PhiOf (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (σ : Selector T S u s) : ℝ :=
  (∑ d ∈ distinctions T S u s σ, d.phi)
    + (∑ d ∈ relationSets T S u s σ, relPhiOrZero d)
    + ∑ d ∈ selfRelationDistinctions T S u s σ, selfRelPhi d

lemma PhiOf_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (σ : Selector T S u s) : 0 ≤ PhiOf T S u s σ := by
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · exact Finset.sum_nonneg fun d _ => d.phi_pos.le
  · exact Finset.sum_nonneg fun d _ => relPhiOrZero_nonneg d
  · exact Finset.sum_nonneg fun d hd => (Finset.mem_filter.1 hd).2.le

/-- `Φ` of a **complex** `[IIT4, Eq 58]`: the intended object, gated on maximal
irreducibility. -/
noncomputable def PhiOfComplex (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (σ : Selector T S u s) {U : Finset (Fin N)} (_h : IsComplex T u U S s) : ℝ :=
  PhiOf T S u s σ

noncomputable instance instFintypeSelector (T : UnitTPM N) (S : Finset (Fin N))
    (u s : State N) : Fintype (Selector T S u s) := by
  classical
  exact Fintype.ofInjective (fun σ : Selector T S u s => (σ.causeOf, σ.effectOf))
    (by
      rintro ⟨c1, e1, _, _, _, _, _⟩ ⟨c2, e2, _, _, _, _, _⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl)

/-- **`Φ` maximized over the tie-break** `[IIT4, S1 Text]`.

`[IIT4, S1 Text]` resolves ties in `[IIT4, Eq 45]` "at the level of the cause-effect
structure, by selecting the `z_{c/e}` that maximizes the system's structure integrated
information `Φ`".  Read locally, at the point where a purview must be chosen, that rule
refers forward to `Φ`.  Read globally it is a maximization over the finite
nonempty set of admissible selections -- `instFintypeSelector` and
`instNonemptySelector` -- and `PhiMax` is that maximum.  So `Φ` under the maximizing
reading *is* a function of the transition probabilities and the state alone; what the
rule costs is that it is a global optimization rather than a per-mechanism choice.  The
development keeps `PhiOf` parameterized as well, because the two readings differ and
PyPhi implements neither. -/
noncomputable def PhiMax (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) : ℝ :=
  sup'OrZero (Finset.univ : Finset (Selector T S u s)) (PhiOf T S u s)

theorem PhiOf_le_PhiMax (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (σ : Selector T S u s) : PhiOf T S u s σ ≤ PhiMax T S u s :=
  le_sup'OrZero (Finset.mem_univ σ)

lemma PhiMax_le_of_forall (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ σ : Selector T S u s, PhiOf T S u s σ ≤ B) :
    PhiMax T S u s ≤ B :=
  sup'OrZero_le hB fun σ _ => h σ

/-- **A distinction's integration per unit is at most the size of its mechanism.**
`[UB, Theorem 1]` bounds `φ_e(m, Z)` by `|M||Z|`, `[IIT4, Eq 46]` attains `φ_e(m)` at a
maximal purview, and `[IIT4, Eq 53]` divides by the size of the support, which contains
that purview.  This is the per-distinction half of `[UB, §2.2, Step 3]`'s estimate on
`S(o)`. -/
lemma phiPerUnit_le_card_mech (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (σ : Selector T S u s) {M : Finset (Fin N)} (hM : M ∈ distinctionMechs T S u s) :
    (distinctionOf T S u s σ M hM).phiPerUnit ≤ (M.card : ℝ) := by
  classical
  set d := distinctionOf T S u s σ M hM with hd
  have hze : d.ze = stated (σ.effectOf M).1 (σ.effectOf M).2 := rfl
  have hsub : d.ze ⊆ d.support := Finset.subset_union_right
  have hcard : ((σ.effectOf M).1.card : ℝ) ≤ (d.support.card : ℝ) := by
    have := Finset.card_le_card hsub
    rw [hze, card_stated] at this
    exact_mod_cast this
  have hpos : 0 < (d.support.card : ℝ) := by
    have : d.ze.Nonempty := d.ze_nonempty
    have h2 : d.support.Nonempty := this.mono hsub
    exact_mod_cast Finset.card_pos.2 h2
  have hphi : d.phi ≤ (M.card : ℝ) * (d.support.card : ℝ) := by
    have h1 : d.phi = phiD T S M s := rfl
    have h2 : phiD T S M s ≤ phiEmech T S M s := phiD_le_phiEmech T S M s
    have h3 : phiEat T M s (σ.effectOf M).1 (σ.effectOf M).2 = phiEmech T S M s :=
      phiEat_of_mem_maxEffPurviews T S M s (σ.effect_mem M hM)
    have h4 : phiEat T M s (σ.effectOf M).1 (σ.effectOf M).2
        ≤ (M.card : ℝ) * ((σ.effectOf M).1.card : ℝ) :=
      phiEat_le T M s (σ.effectOf M).1 (σ.effectOf M).2
    have h5 : (M.card : ℝ) * ((σ.effectOf M).1.card : ℝ)
        ≤ (M.card : ℝ) * (d.support.card : ℝ) :=
      mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)
    rw [h1]
    linarith [h2, h3 ▸ h4, h5]
  rw [Distinction.phiPerUnit, div_le_iff₀ hpos]
  exact hphi

/-- **`[UB, §2.2, Step 3]`'s estimate on `S(o)`, discharged.**  Summing
`phiPerUnit_le_card_mech` over the distinction set and then over all subsets of the
substrate gives `∑_{M ⊆ U} |M| = (N/2) 2^N`, which is exactly the estimate `[UB]` states. -/
theorem sum_phiPerUnit_le (T : UnitTPM N) (u s : State N)
    (σ : Selector T Finset.univ u s) :
    ∑ a ∈ distinctions T Finset.univ u s σ, a.phiPerUnit ≤ ((N : ℝ) / 2) * 2 ^ N := by
  classical
  have hstep : (∑ a ∈ distinctions T Finset.univ u s σ, a.phiPerUnit)
      ≤ ∑ M ∈ distinctionMechs T Finset.univ u s, (M.card : ℝ) := by
    rw [distinctions, Finset.sum_image (by
      rintro ⟨M1, h1⟩ - ⟨M2, h2⟩ - heq
      have : M1 = M2 := congrArg Distinction.mech heq
      subst this
      rfl)]
    rw [← Finset.sum_attach (distinctionMechs T Finset.univ u s) (fun M => (M.card : ℝ))]
    exact Finset.sum_le_sum fun M _ => phiPerUnit_le_card_mech T Finset.univ u s σ M.2
  refine hstep.trans ?_
  have hsum : ∑ M ∈ distinctionMechs T Finset.univ u s, (M.card : ℝ)
      ≤ ∑ M ∈ (Finset.univ : Finset (Fin N)).powerset, (M.card : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun M _ => Finset.mem_powerset.2 (Finset.subset_univ M))
      (fun M _ _ => Nat.cast_nonneg _)
  rw [sum_card_powerset_real] at hsum
  linarith [hsum]

/-- The distinction part of `Φ` is exactly `PhiDistinctions`, hence bounded by
`[UB, Eq 6]`.  This is the bridge from `Φ` back to the bounds paper. -/
theorem sum_distinctions_phi (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (σ : Selector T S u s) :
    (∑ d ∈ distinctions T S u s σ, d.phi) = PhiDistinctions T S u s := by
  classical
  rw [distinctions, PhiDistinctions]
  rw [Finset.sum_image (by
    rintro ⟨M1, h1⟩ - ⟨M2, h2⟩ - heq
    have : M1 = M2 := congrArg Distinction.mech heq
    subst this
    rfl)]
  exact Finset.sum_attach (distinctionMechs T S u s) (fun M => phiD T S M s)

end PhiStructure


end IIT
