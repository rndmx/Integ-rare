/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import IIT.Growth

/-!
# The mechanism level of a candidate system, background-conditioned

`IIT/Phi.lean` builds the mechanism-level calculus with the units outside the *mechanism*
marginalized uniformly.  That is exactly `[UB, Eq 4]`, whose `W = S - M` carries
`|W| = N - |M|` because `[UB]` works inside a single system with no background at all:
`[UB]` never mentions one, and its `N` is the size of the system it studies.

`[IIT4]` is two-stage.  By intrinsicality the units `W = U \ S` are *background
conditions*: they are marginalized against the current state of the universe, giving the
TPMs `T_e` `[IIT4, Eq 3]` and `T_c` `[IIT4, Eq 4]` of the candidate system `S`.  Only then
does the mechanism-level calculus run, marginalizing `X = S \ M` inside the conditioned
system `[IIT4, Eq 28]`, with every probability taken from `T_e` and `T_c`.

The two stages compose into a single change of conditioning:

    effUnitAt T S u M m i b  =  effUnit T (M ∪ Sᶜ) (merge S m u) i b

-- average over the states that agree with `m` on the mechanism *and* with `u` outside the
candidate system.  `card_agree_cond` below is the theorem that this really is
`[IIT4, Eq 28]`: the set marginalized has exactly `2 ^ |S \ M|` elements.  And at
`S = U` the background is empty and everything collapses to `IIT/Phi.lean`, which is why
that file is `[UB]`'s setting and why every existing differential number is unaffected.

The repertoires do instantiate `IIT/Phi.lean` at the conditioned pair.  The *`φ`* does
not, and that distinction is the substance of this file: `[IIT4, Eq 38]`'s partitions cut
`(M, Z)`, and the background is a *condition*, not a part.  Evaluating `φ_e` at the
enlarged mechanism `M ∪ Sᶜ` would admit partitions that sever background units, and since
`[IIT4, Eq 42]` *minimizes* over partitions that is a strict under-estimate rather than a
reformulation.  So the definitions below keep `θ : Partition N M Z` and adjoin `Sᶜ` inside
every block, where it is never severed -- which is also what leaves `cutCount M Z θ`, and
hence `[UB, Theorem 1]`'s constant, unchanged.

## Status

Proved, with no `sorry`:

* `card_agree_cond`                 — the fibre of `[IIT4, Eq 28]` has `2 ^ |S \ M|` elements
* `causeFwdAt_univ`, `phiDAt_univ`  — the mechanism level collapses to `IIT/Phi.lean` at `S = U`
* `card_condSet`, `card_condSet_sub` — conditioning shifts every mechanism by `|Sᶜ|`
* `effRepAt_le_cutCount_smul`       — `[UB, Lemma 2]` conditioned, same cut count
* `theorem_one_at`, `phiDAt_le`     — `[UB, Theorem 1]` conditioned, constant `|M| |S|`
* `phiEatAt_of_mem_maxEffPurviewsAt`, `phiCatAt_of_mem_maxCausePurviewsAt` — `[IIT4, Eq 45]`
* `maxEffPurviewsAt_fst_nonempty`, `maxCausePurviewsAt_fst_nonempty` — nonempty once `φ_d > 0`
* `distinctionMechsAt_univ`, `PhiDistinctionsAt_univ` — `[IIT4, Eq 48]` at `S = U`
* `PhiOf_eq_structure`              — `[IIT4, Eq 59]` factors through the distinction set
* `instNonemptySelectorAt`          — the conditioned tie-break exists
* `distinctionsAt_univ`, `PhiOfAt_univ`, `PhiOfComplexAt_univ` — the join is consistent
* `PhiOfComplexAt_le`               — `[UB, Eqs 6, 16]` for `Φ` of a complex
* `complexSearch_mem_nonempty`      — the `[IIT4, Eqs 24, 25]` recursion terminates
* `isComplex_iff_mem_argmaxSubstrates` — `[IIT4, Eq 26]` agrees with `[IIT4, Eq 25]`
  exactly under two hypotheses, one for each way the source's two characterizations differ

Validated against PyPhi (`feature/iit-4.0`, `b78d0e34`): `test/condtest.py` for the
repertoires, `test/condphi.py` for `φ_d`, `test/condrel.py` for `Φ` of the complex, all on
*proper* candidate subsystems, which is the regime where the conditioning is visible.

What remains genuinely open is only the *recursion*: these theorems relate `[IIT4,
Eq 26]` to the search's first stage, not to the substrates it returns at stage `k > 0`.
-/

namespace IIT

variable {N : ℕ}

open scoped Classical

/-! ## The conditioning context -/

/-- The conditioning set of `[IIT4, Eqs 3, 28]`: the mechanism, together with the
background `U \ S`, which is *held* at its current state rather than marginalized. -/
def condSet (S M : Finset (Fin N)) : Finset (Fin N) := M ∪ Sᶜ

/-- The conditioning state: `m` on the candidate system, the current state `u` outside
it. -/
def condState (S : Finset (Fin N)) (u m : State N) : State N := merge S m u

lemma condSet_univ (M : Finset (Fin N)) : condSet Finset.univ M = M := by
  simp [condSet]

lemma condState_univ (u m : State N) : condState Finset.univ u m = m := by
  funext j
  simp [condState, merge]

lemma disjoint_compl_of_subset {S M : Finset (Fin N)} (hM : M ⊆ S) : Disjoint M Sᶜ :=
  Finset.disjoint_left.2 fun a ha hb =>
    (Finset.mem_compl.1 hb) (hM ha)

/-- **`[IIT4, Eq 28]`'s marginalized set is `X = S \ M`.**

`[IIT4, Eq 28]` marginalizes the units of `X = S \ M`, and only those: the background
`U \ S` is fixed by the current state of the universe, not averaged over.  This says the
conditioned repertoire does exactly that -- the fibre it averages over has `2 ^ |S \ M|`
elements.  Without it, `effUnitAt` would be a plausible-looking definition with no
argument that it is the source's. -/
theorem card_agree_cond {S M : Finset (Fin N)} (hM : M ⊆ S) (u m : State N) :
    (agree (condSet S M) (condState S u m)).card = 2 ^ (S.card - M.card) := by
  rw [card_agree, condSet]
  congr 1
  have hd : Disjoint M Sᶜ := disjoint_compl_of_subset hM
  have hc : (M ∪ Sᶜ).card = M.card + (N - S.card) := by
    rw [Finset.card_union_of_disjoint hd, Finset.card_compl, Fintype.card_fin]
  have h1 : M.card ≤ S.card := Finset.card_le_card hM
  have h2 : S.card ≤ N := by
    simpa [Fintype.card_fin] using Finset.card_le_univ S
  omega

/-! ## The conditioned effect side `[IIT4, Eqs 3, 28-29]` -/

/-- **`[IIT4, Eqs 3, 28]`**: the single-unit effect repertoire of a mechanism inside a
candidate system.  The background `U \ S` is pinned at `u`; `S \ M` is marginalized
uniformly. -/
noncomputable def effUnitAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) (i : Fin N) (b : Bool) : ℝ :=
  effUnit T (condSet S M) (condState S u m) i b

/-- **`[IIT4, Eq 29]`**: the effect repertoire, the product over purview units. -/
noncomputable def effRepAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) (Z : Finset (Fin N)) (z : State N) : ℝ :=
  effRep T (condSet S M) (condState S u m) Z z

@[simp] lemma effUnitAt_univ (T : UnitTPM N) (u : State N) (M : Finset (Fin N))
    (m : State N) (i : Fin N) (b : Bool) :
    effUnitAt T Finset.univ u M m i b = effUnit T M m i b := by
  rw [effUnitAt, condSet_univ, condState_univ]

lemma effRepAt_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) (Z : Finset (Fin N)) (z : State N) :
    0 ≤ effRepAt T S u M m Z z :=
  effRep_nonneg T _ _ Z z

@[simp] lemma effRepAt_univ (T : UnitTPM N) (u : State N) (M : Finset (Fin N))
    (m : State N) (Z : Finset (Fin N)) (z : State N) :
    effRepAt T Finset.univ u M m Z z = effRep T M m Z z := by
  rw [effRepAt, condSet_univ, condState_univ]

/-! ## The conditioned cause side `[IIT4, Eqs 4, 30]`

`[IIT4, Eq 4]` marginalizes the background's *prior* state against the Bayes posterior
`bgWeight`, exactly as `sysCauseProb` does at the system level, with the same `2 ^ |S|`
overcount correction: `bgWeight` depends on `w` only through `w` outside `S`, so summing
over all `2 ^ N` universe states counts each background state `2 ^ |S|` times. -/

/-- **`[IIT4, Eqs 4, 30]`**: the forward term of the cause repertoire, with the background
marginalized against the `[IIT4, Eq 4]` posterior rather than pinned. -/
noncomputable def causeFwdAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (Z : Finset (Fin N)) (z : State N) (M : Finset (Fin N)) (m : State N) : ℝ :=
  ∏ i ∈ M, ((∑ w : State N,
      effUnit T (condSet S Z) (condState S w z) i (m i) * bgWeight T S u w)
    / (2 : ℝ) ^ S.card)

lemma causeFwdAt_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (Z : Finset (Fin N)) (z : State N) (M : Finset (Fin N)) (m : State N) :
    0 ≤ causeFwdAt T S u Z z M m := by
  refine Finset.prod_nonneg fun i _ => div_nonneg ?_ (by positivity)
  exact Finset.sum_nonneg fun w _ =>
    mul_nonneg (effUnit_nonneg T _ _ i (m i)) (bgWeight_nonneg T S u w)

/-- **On the whole substrate the conditioned cause side is `[UB]`'s.**  With `S = U` the
background is empty, `bgWeight` is identically `1`, and the sum over `Ω_W` collapses
against the `2 ^ N` divisor -- so `IIT/Phi.lean`'s `causeFwd` is this definition at
`S = U`, which is why every existing differential number is unaffected.  The hypothesis is
the same non-degeneracy `sysCauseProb_eq_pinned_univ` needs: the current state must be
reachable. -/
theorem causeFwdAt_univ (T : UnitTPM N) (u : State N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) (hu : 0 < ∑ v : State N, fullProb T v u) :
    causeFwdAt T Finset.univ u Z z M m = causeFwd T Z z M m := by
  have hmerge : ∀ v w : State N, condState (Finset.univ : Finset (Fin N)) v w = w := by
    intro v w; funext j; simp [condState, merge]
  have hbg : ∀ w : State N, bgWeight T (Finset.univ : Finset (Fin N)) u w = 1 := by
    intro w
    rw [bgWeight, Finset.card_univ, Fintype.card_fin, Nat.sub_self, pow_zero, div_one]
    rw [Finset.sum_congr rfl fun v _ => by
      rw [show merge (Finset.univ : Finset (Fin N)) v w = v from by
        funext j; simp [merge]]]
    exact div_self hu.ne'
  have hcard : ((Finset.univ : Finset (State N)).card : ℝ) = (2 : ℝ) ^ N := by
    rw [card_state]; push_cast; ring
  rw [causeFwdAt, causeFwd, effRep]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl fun w _ => by
      rw [hbg w, mul_one, hmerge w z, condSet_univ],
    Finset.sum_const, nsmul_eq_mul, hcard, Finset.card_univ, Fintype.card_fin]
  field_simp

/-! ## Conditioned `φ_e`, `φ_c` and `φ_d` `[IIT4, Eqs 31-47]`

**The partition ranges over the mechanism, not over the mechanism-plus-background.**
`[IIT4, Eq 38]`'s partitions cut `(M, Z)`; the background `U \ S` is a *condition*, not a
part, and cutting it would change both the repertoire and the cut count `[IIT4, Eq 43]`.
So the definitions below keep `θ : Partition N M Z` and adjoin `Sᶜ` inside each block:

    partEffRepAt … θ = ∏ k ∈ Z, effUnit T (condSet S (θ.effPart k)) (condState S u m) k (z k)

Because `Sᶜ` lies in *every* block it is never severed, so `cutCount M Z θ` is the same
number here as in `IIT/Phi.lean` and `[UB, Theorem 1]`'s counting argument is untouched.
Taking `phiEmech T S (condSet S M) (condState S u m)` instead would admit partitions that
sever background units; since `φ_e` is a *minimum* over partitions, that is a strict
under-estimate rather than a reformulation.

The unconstrained repertoire needs the same care in mirror image: it averages the
*mechanism* over its states with the background pinned, which is what `avgOverStates` over
`effRepAt` gives, since `effRepAt` depends on `m` only through `m` on `M`. -/

/-- The unconstrained effect repertoire, conditioned `[IIT4, Eqs 3, 31]`. -/
noncomputable def uncEffRepAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M Z : Finset (Fin N)) (z : State N) : ℝ :=
  avgOverStates fun m => effRepAt T S u M m Z z

/-- Intrinsic effect information, conditioned `[IIT4, Eq 32]`. -/
noncomputable def iiEAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) (Z : Finset (Fin N)) (z : State N) : ℝ :=
  effRepAt T S u M m Z z *
    Real.logb 2 (effRepAt T S u M m Z z / uncEffRepAt T S u M Z z)

/-- The maximal effect states, conditioned `[IIT4, Eq 36]`, all ties kept. -/
noncomputable def maxEffStatesAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) (Z : Finset (Fin N)) : Finset (State N) :=
  argmaxSet (iiEAt T S u M m Z)

/-- **The partitioned effect repertoire, conditioned** `[IIT4, Eqs 3, 39]`: the partition
is of `(M, Z)`, and the background rides inside every block. -/
noncomputable def partEffRepAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) (Z : Finset (Fin N)) (z : State N)
    (θ : Partition N M Z) : ℝ :=
  ∏ k ∈ Z, effUnit T (condSet S (θ.effPart k)) (condState S u m) k (z k)

lemma partEffRepAt_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) (Z : Finset (Fin N)) (z : State N)
    (θ : Partition N M Z) : 0 ≤ partEffRepAt T S u M m Z z θ :=
  Finset.prod_nonneg fun k _ => effUnit_nonneg T _ _ k (z k)

/-- `φ_e` at one partition, conditioned `[IIT4, Eq 41]`. -/
noncomputable def phiEofPartitionAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) (Z : Finset (Fin N)) (z : State N)
    (θ : Partition N M Z) : ℝ :=
  effRepAt T S u M m Z z *
    pos (Real.logb 2 (effRepAt T S u M m Z z / partEffRepAt T S u M m Z z θ))

lemma phiEofPartitionAt_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) (Z : Finset (Fin N)) (z : State N)
    (θ : Partition N M Z) : 0 ≤ phiEofPartitionAt T S u M m Z z θ :=
  mul_nonneg (effRepAt_nonneg T S u M m Z z) (pos_nonneg _)

/-- The normalized quantity the MIP minimizes, conditioned `[IIT4, Eq 43]`.  The divisor
is `cutCount M Z θ`: the background sits in every block, so it contributes no cut. -/
noncomputable def normalizedPhiAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) (Z : Finset (Fin N)) (z : State N)
    (θ : Partition N M Z) : ℝ :=
  phiEofPartitionAt T S u M m Z z θ / (cutCount M Z θ : ℝ)

/-- The conditioned effect MIPs `[IIT4, Eq 43]`, all ties kept. -/
noncomputable def mipSetEAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) (Z : Finset (Fin N)) (z : State N) :
    Finset (Partition N M Z) :=
  argminSet (normalizedPhiAt T S u M m Z z)

/-- `φ_e(m, Z)` conditioned `[IIT4, Eq 42]`, MIP ties resolved as in `phiEat`. -/
noncomputable def phiEatAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) (Z : Finset (Fin N)) (z : State N) : ℝ :=
  sup'OrZero (mipSetEAt T S u M m Z z) (phiEofPartitionAt T S u M m Z z)

/-- `φ_e` over one purview at its maximal effect states, conditioned `[IIT4, Eq 44]`. -/
noncomputable def phiEpurviewAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) (Z : Finset (Fin N)) : ℝ :=
  (maxEffStatesAt T S u M m Z).sup' (argmaxSet_nonempty _) fun z =>
    phiEatAt T S u M m Z z

/-- **`φ_e(m)`** conditioned `[IIT4, Eq 46]`: the maximum over purviews `Z ⊆ S`, which is
where the candidate system enters a second time. -/
noncomputable def phiEmechAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) : ℝ :=
  S.powerset.sup' ⟨∅, Finset.empty_mem_powerset S⟩ fun Z => phiEpurviewAt T S u M m Z

/-! ### The cause side

`causeFwdAt` already marginalizes the background against the `[IIT4, Eq 4]` posterior.
Everything below is its `IIT/Phi.lean` counterpart with that substitution, and with the
same treatment of the partition: `θ.causePart k` gets the background adjoined. -/

/-- The unconstrained cause term, conditioned `[IIT4, Eq 4]`. -/
noncomputable def uncCauseFwdAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (Z M : Finset (Fin N)) (m : State N) : ℝ :=
  avgOverStates fun z => causeFwdAt T S u Z z M m

/-- The backward cause probability, conditioned `[IIT4, Eq 33]`. -/
noncomputable def causeRepAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (Z : Finset (Fin N)) (z : State N) (M : Finset (Fin N)) (m : State N) : ℝ :=
  causeFwdAt T S u Z z M m / ((2 : ℝ) ^ Z.card * uncCauseFwdAt T S u Z M m)

lemma uncCauseFwdAt_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (Z M : Finset (Fin N)) (m : State N) : 0 ≤ uncCauseFwdAt T S u Z M m := by
  rw [uncCauseFwdAt, avgOverStates]
  exact div_nonneg (Finset.sum_nonneg fun w _ => causeFwdAt_nonneg T S u Z w M m)
    (by positivity)

lemma causeRepAt_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (Z : Finset (Fin N)) (z : State N) (M : Finset (Fin N)) (m : State N) :
    0 ≤ causeRepAt T S u Z z M m := by
  rw [causeRepAt]
  exact div_nonneg (causeFwdAt_nonneg T S u Z z M m)
    (mul_nonneg (by positivity) (uncCauseFwdAt_nonneg T S u Z M m))

/-- Intrinsic cause information, conditioned `[IIT4, Eq 35]`. -/
noncomputable def iiCAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) (Z : Finset (Fin N)) (z : State N) : ℝ :=
  causeRepAt T S u Z z M m *
    Real.logb 2 (causeFwdAt T S u Z z M m / uncCauseFwdAt T S u Z M m)

/-- The maximal cause states, conditioned, all ties kept. -/
noncomputable def maxCauseStatesAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) (Z : Finset (Fin N)) : Finset (State N) :=
  argmaxSet (iiCAt T S u M m Z)

/-- **The partitioned cause term, conditioned**: each mechanism unit is constrained by the
purview part of its block, with the background adjoined and marginalized. -/
noncomputable def partCauseFwdAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (Z : Finset (Fin N)) (z : State N) (M : Finset (Fin N)) (m : State N)
    (θ : Partition N M Z) : ℝ :=
  ∏ k ∈ M, ((∑ w : State N,
      effUnit T (condSet S (θ.causePart k)) (condState S w z) k (m k) * bgWeight T S u w)
    / (2 : ℝ) ^ S.card)

lemma partCauseFwdAt_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (Z : Finset (Fin N)) (z : State N) (M : Finset (Fin N)) (m : State N)
    (θ : Partition N M Z) : 0 ≤ partCauseFwdAt T S u Z z M m θ := by
  refine Finset.prod_nonneg fun k _ => div_nonneg ?_ (by positivity)
  exact Finset.sum_nonneg fun w _ =>
    mul_nonneg (effUnit_nonneg T _ _ k (m k)) (bgWeight_nonneg T S u w)

/-- `φ_c` at one partition, conditioned. -/
noncomputable def phiCofPartitionAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (Z : Finset (Fin N)) (z : State N) (M : Finset (Fin N)) (m : State N)
    (θ : Partition N M Z) : ℝ :=
  causeRepAt T S u Z z M m *
    pos (Real.logb 2 (causeFwdAt T S u Z z M m / partCauseFwdAt T S u Z z M m θ))

lemma phiCofPartitionAt_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (Z : Finset (Fin N)) (z : State N) (M : Finset (Fin N)) (m : State N)
    (θ : Partition N M Z) : 0 ≤ phiCofPartitionAt T S u Z z M m θ :=
  mul_nonneg (causeRepAt_nonneg T S u Z z M m) (pos_nonneg _)

/-- The normalized cause quantity `[IIT4, Eq 43]`, conditioned. -/
noncomputable def normalizedPhiCAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (Z : Finset (Fin N)) (z : State N) (M : Finset (Fin N)) (m : State N)
    (θ : Partition N M Z) : ℝ :=
  phiCofPartitionAt T S u Z z M m θ / (cutCount M Z θ : ℝ)

/-- The conditioned cause MIPs, all ties kept. -/
noncomputable def mipSetCAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (Z : Finset (Fin N)) (z : State N) (M : Finset (Fin N)) (m : State N) :
    Finset (Partition N M Z) :=
  argminSet (normalizedPhiCAt T S u Z z M m)

/-- `φ_c(m, Z)` conditioned `[UB, S1 Appendix, Eq 17]`. -/
noncomputable def phiCatAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (Z : Finset (Fin N)) (z : State N) (M : Finset (Fin N)) (m : State N) : ℝ :=
  sup'OrZero (mipSetCAt T S u Z z M m) (phiCofPartitionAt T S u Z z M m)

/-- `φ_c` over one purview at its maximal cause states, conditioned. -/
noncomputable def phiCpurviewAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) (Z : Finset (Fin N)) : ℝ :=
  (maxCauseStatesAt T S u M m Z).sup' (argmaxSet_nonempty _) fun z =>
    phiCatAt T S u Z z M m

/-- **`φ_c(m)`** conditioned. -/
noncomputable def phiCmechAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) : ℝ :=
  S.powerset.sup' ⟨∅, Finset.empty_mem_powerset S⟩ fun Z => phiCpurviewAt T S u M m Z

/-- **`φ_d(m) = min(φ_c(m), φ_e(m))`** conditioned `[IIT4, Eq 47]`. -/
noncomputable def phiDAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) : ℝ :=
  min (phiCmechAt T S u M m) (phiEmechAt T S u M m)

/-- Both `φ_e` and `φ_c` are a supremum over an `argminSet`, so both collapses are this
one fact: change the minimized function and the maximized one pointwise, and the value
follows.  Stated over an abstract type so that neither side's proof has to mention
`instFintypePartition`. -/
lemma sup'OrZero_argminSet_congr {α : Type*} [Fintype α] {f g p q : α → ℝ}
    (hfg : ∀ a, f a = g a) (hpq : ∀ a, p a = q a) :
    sup'OrZero (argminSet f) p = sup'OrZero (argminSet g) q := by
  rw [funext hfg]
  exact sup'OrZero_congr hpq

/-- `Finset.sup'` over a set that is being rewritten: `Finset.sup'_congr` transports the
nonemptiness proof along the equality, which the kernel then has to check.  Substituting
first removes the transport, and every purview- and mechanism-level collapse below goes
through this. -/
lemma sup'_congr_of_eq {α : Type*} {s t : Finset α} (hst : s = t) {f g : α → ℝ}
    (hs : s.Nonempty) (ht : t.Nonempty) (h : ∀ a, f a = g a) :
    s.sup' hs f = t.sup' ht g := by
  subst hst
  exact Finset.sup'_congr hs rfl fun a _ => h a

/-! ### The collapse at `S = U`

Every definition above reduces to its `IIT/Phi.lean` counterpart when the candidate system
is the whole substrate, because `condSet Finset.univ X = X` and
`condState Finset.univ u m = m`.  The cause side additionally carries the reachability
`causeFwdAt_univ` needs. -/

@[simp] lemma uncEffRepAt_univ (T : UnitTPM N) (u : State N) (M Z : Finset (Fin N))
    (z : State N) : uncEffRepAt T Finset.univ u M Z z = uncEffRep T M Z z := by
  rw [uncEffRepAt, uncEffRep, avgOverStates, card_state]
  congr 1
  · exact Finset.sum_congr rfl fun m _ => effRepAt_univ T u M m Z z
  · push_cast; ring

@[simp] lemma iiEAt_univ (T : UnitTPM N) (u : State N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) :
    iiEAt T Finset.univ u M m Z z = iiE T M m Z z := by
  rw [iiEAt, iiE, effRepAt_univ, uncEffRepAt_univ]

@[simp] lemma maxEffStatesAt_univ (T : UnitTPM N) (u : State N) (M : Finset (Fin N))
    (m : State N) (Z : Finset (Fin N)) :
    maxEffStatesAt T Finset.univ u M m Z = maxEffStates T M m Z := by
  rw [maxEffStatesAt, maxEffStates]
  exact congrArg argmaxSet (funext fun z => iiEAt_univ T u M m Z z)

@[simp] lemma partEffRepAt_univ (T : UnitTPM N) (u : State N) (M : Finset (Fin N))
    (m : State N) (Z : Finset (Fin N)) (z : State N) (θ : Partition N M Z) :
    partEffRepAt T Finset.univ u M m Z z θ = partEffRep T M m Z z θ := by
  rw [partEffRepAt, partEffRep]
  exact Finset.prod_congr rfl fun k _ => by rw [condSet_univ, condState_univ]

@[simp] lemma phiEofPartitionAt_univ (T : UnitTPM N) (u : State N) (M : Finset (Fin N))
    (m : State N) (Z : Finset (Fin N)) (z : State N) (θ : Partition N M Z) :
    phiEofPartitionAt T Finset.univ u M m Z z θ = phiEofPartition T M m Z z θ := by
  rw [phiEofPartitionAt, phiEofPartition, effRepAt_univ, partEffRepAt_univ]

@[simp] lemma phiEatAt_univ (T : UnitTPM N) (u : State N) (M : Finset (Fin N))
    (m : State N) (Z : Finset (Fin N)) (z : State N) :
    phiEatAt T Finset.univ u M m Z z = phiEat T M m Z z :=
  sup'OrZero_argminSet_congr
    (fun θ => by
      rw [normalizedPhiAt, normalizedPhi, phiEofPartitionAt_univ T u M m Z z θ])
    (fun θ => phiEofPartitionAt_univ T u M m Z z θ)

@[simp] lemma phiEpurviewAt_univ (T : UnitTPM N) (u : State N) (M : Finset (Fin N))
    (m : State N) (Z : Finset (Fin N)) :
    phiEpurviewAt T Finset.univ u M m Z = phiEpurview T M m Z := by
  rw [phiEpurviewAt, phiEpurview]
  exact sup'_congr_of_eq (maxEffStatesAt_univ T u M m Z) _ _
    fun z => phiEatAt_univ T u M m Z z

@[simp] lemma phiEmechAt_univ (T : UnitTPM N) (u : State N) (M : Finset (Fin N))
    (m : State N) : phiEmechAt T Finset.univ u M m = phiEmech T Finset.univ M m := by
  rw [phiEmechAt, phiEmech]
  exact sup'_congr_of_eq rfl _ _ fun Z => phiEpurviewAt_univ T u M m Z

lemma uncCauseFwdAt_univ (T : UnitTPM N) (u : State N) (Z M : Finset (Fin N))
    (m : State N) (hu : 0 < ∑ v : State N, fullProb T v u) :
    uncCauseFwdAt T Finset.univ u Z M m = uncCauseFwd T Z M m := by
  rw [uncCauseFwdAt, uncCauseFwd]
  exact congrArg avgOverStates (funext fun z => causeFwdAt_univ T u Z z M m hu)

lemma causeRepAt_univ (T : UnitTPM N) (u : State N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) (hu : 0 < ∑ v : State N, fullProb T v u) :
    causeRepAt T Finset.univ u Z z M m = causeRep T Z z M m := by
  rw [causeRepAt, causeRep, causeFwdAt_univ T u Z z M m hu, uncCauseFwdAt_univ T u Z M m hu]

lemma iiCAt_univ (T : UnitTPM N) (u : State N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) (hu : 0 < ∑ v : State N, fullProb T v u) :
    iiCAt T Finset.univ u M m Z z = iiC T M m Z z := by
  rw [iiCAt, iiC, causeRepAt_univ T u Z z M m hu, causeFwdAt_univ T u Z z M m hu,
    uncCauseFwdAt_univ T u Z M m hu]

lemma maxCauseStatesAt_univ (T : UnitTPM N) (u : State N) (M : Finset (Fin N))
    (m : State N) (Z : Finset (Fin N)) (hu : 0 < ∑ v : State N, fullProb T v u) :
    maxCauseStatesAt T Finset.univ u M m Z = maxCauseStates T M m Z := by
  rw [maxCauseStatesAt, maxCauseStates]
  exact congrArg argmaxSet (funext fun z => iiCAt_univ T u M m Z z hu)

lemma partCauseFwdAt_univ (T : UnitTPM N) (u : State N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) (θ : Partition N M Z)
    (hu : 0 < ∑ v : State N, fullProb T v u) :
    partCauseFwdAt T Finset.univ u Z z M m θ = partCauseFwd T Z z M m θ := by
  have hmerge : ∀ v w : State N, condState (Finset.univ : Finset (Fin N)) v w = w := by
    intro v w; funext j; simp [condState, merge]
  have hbg : ∀ w : State N, bgWeight T (Finset.univ : Finset (Fin N)) u w = 1 := by
    intro w
    rw [bgWeight, Finset.card_univ, Fintype.card_fin, Nat.sub_self, pow_zero, div_one]
    rw [Finset.sum_congr rfl fun v _ => by
      rw [show merge (Finset.univ : Finset (Fin N)) v w = v from by
        funext j; simp [merge]]]
    exact div_self hu.ne'
  have hcard : ((Finset.univ : Finset (State N)).card : ℝ) = (2 : ℝ) ^ N := by
    rw [card_state]; push_cast; ring
  rw [partCauseFwdAt, partCauseFwd]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl fun w _ => by
      rw [hbg w, mul_one, hmerge w z, condSet_univ],
    Finset.sum_const, nsmul_eq_mul, hcard, Finset.card_univ, Fintype.card_fin]
  field_simp

lemma phiCofPartitionAt_univ (T : UnitTPM N) (u : State N) (Z : Finset (Fin N))
    (z : State N) (M : Finset (Fin N)) (m : State N) (θ : Partition N M Z)
    (hu : 0 < ∑ v : State N, fullProb T v u) :
    phiCofPartitionAt T Finset.univ u Z z M m θ = phiCofPartition T Z z M m θ := by
  rw [phiCofPartitionAt, phiCofPartition, causeRepAt_univ T u Z z M m hu,
    causeFwdAt_univ T u Z z M m hu, partCauseFwdAt_univ T u Z z M m θ hu]

lemma phiCatAt_univ (T : UnitTPM N) (u : State N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) (hu : 0 < ∑ v : State N, fullProb T v u) :
    phiCatAt T Finset.univ u Z z M m = phiCat T Z z M m := by
  exact sup'OrZero_argminSet_congr
    (fun θ => by
      rw [normalizedPhiCAt, normalizedPhiC, phiCofPartitionAt_univ _ _ _ _ _ _ _ hu])
    (fun θ => phiCofPartitionAt_univ T u Z z M m θ hu)

lemma phiCpurviewAt_univ (T : UnitTPM N) (u : State N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (hu : 0 < ∑ v : State N, fullProb T v u) :
    phiCpurviewAt T Finset.univ u M m Z = phiCpurview T M m Z := by
  rw [phiCpurviewAt, phiCpurview]
  exact sup'_congr_of_eq (maxCauseStatesAt_univ T u M m Z hu) _ _
    fun z => phiCatAt_univ T u Z z M m hu

lemma phiCmechAt_univ (T : UnitTPM N) (u : State N) (M : Finset (Fin N)) (m : State N)
    (hu : 0 < ∑ v : State N, fullProb T v u) :
    phiCmechAt T Finset.univ u M m = phiCmech T Finset.univ M m := by
  rw [phiCmechAt, phiCmech]
  exact sup'_congr_of_eq rfl _ _ fun Z => phiCpurviewAt_univ T u M m Z hu

/-- **The whole mechanism level collapses at `S = U`.**  So `IIT/Phi.lean` is this file's
`S = U` instance, and every differential number the validation suites report certifies what it
certified before.  The hypothesis is the reachability the cause side needs -- the same one
`sysCauseProb_eq_pinned_univ` carries, and a condition on when `[IIT4, Eq 4]`'s posterior
is defined rather than a restriction on the theory. -/
theorem phiDAt_univ (T : UnitTPM N) (u : State N) (M : Finset (Fin N)) (m : State N)
    (hu : 0 < ∑ v : State N, fullProb T v u) :
    phiDAt T Finset.univ u M m = phiD T Finset.univ M m := by
  rw [phiDAt, phiD, phiCmechAt_univ T u M m hu, phiEmechAt_univ]

/-! ### `[UB, Theorem 1]` survives conditioning, with the same constant

The background is in every block, so it is never severed: the per-unit exponent of
`[UB, Lemma 1]` is `|condSet S M| - |condSet S (θ.effPart k)| = |M| - |θ.effPart k|`,
which is what `cutCount M Z θ` already sums.  Hence `[UB, Lemma 2]` and `[UB, Theorem 1]`
hold verbatim, with `|M| |Z|` and not the enlarged `|M ∪ Sᶜ| |Z|`. -/

lemma condSet_subset_condSet {S X Y : Finset (Fin N)} (h : X ⊆ Y) :
    condSet S X ⊆ condSet S Y := by
  intro i hi
  rcases Finset.mem_union.1 hi with hx | hc
  · exact Finset.mem_union.2 (Or.inl (h hx))
  · exact Finset.mem_union.2 (Or.inr hc)

/-- **Conditioning adds the same constant to every mechanism**, so differences of
cardinalities -- which is all `cutCount` uses -- are unchanged. -/
lemma card_condSet {S X : Finset (Fin N)} (hX : X ⊆ S) :
    (condSet S X).card = X.card + Sᶜ.card := by
  rw [condSet, Finset.card_union_of_disjoint (disjoint_compl_of_subset hX)]

lemma card_condSet_sub {S X Y : Finset (Fin N)} (hX : X ⊆ S) (hY : Y ⊆ S) :
    (condSet S Y).card - (condSet S X).card = Y.card - X.card := by
  rw [card_condSet hX, card_condSet hY]
  omega

/-- **`[UB, Lemma 2]` conditioned**, with `cutCount M Z θ` unchanged. -/
theorem effRepAt_le_cutCount_smul (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (hM : M ⊆ S) (m : State N) (Z : Finset (Fin N)) (z : State N)
    (θ : Partition N M Z) :
    effRepAt T S u M m Z z ≤ 2 ^ (cutCount M Z θ) * partEffRepAt T S u M m Z z θ := by
  have hpart : ∀ k : Fin N, θ.effPart k ⊆ S := fun k => (θ.effPart_subset k).trans hM
  calc effRepAt T S u M m Z z
      = ∏ k ∈ Z, effUnit T (condSet S M) (condState S u m) k (z k) := rfl
    _ ≤ ∏ k ∈ Z, ((2 : ℝ) ^ ((condSet S M).card - (condSet S (θ.effPart k)).card)
          * effUnit T (condSet S (θ.effPart k)) (condState S u m) k (z k)) :=
        Finset.prod_le_prod (fun k _ => effUnit_nonneg T _ _ k (z k))
          (fun k _ => effUnit_le_of_subset T
            (condSet_subset_condSet (θ.effPart_subset k)) _ k (z k))
    _ = ∏ k ∈ Z, ((2 : ℝ) ^ (M.card - (θ.effPart k).card)
          * effUnit T (condSet S (θ.effPart k)) (condState S u m) k (z k)) := by
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [card_condSet_sub (hpart k) hM]
    _ = (∏ k ∈ Z, (2 : ℝ) ^ (M.card - (θ.effPart k).card)) *
          ∏ k ∈ Z, effUnit T (condSet S (θ.effPart k)) (condState S u m) k (z k) :=
        Finset.prod_mul_distrib
    _ = 2 ^ (cutCount M Z θ) * partEffRepAt T S u M m Z z θ := by
        rw [cutCount, partEffRepAt, Finset.prod_pow_eq_pow_sum]

lemma effRepAt_eq_zero_of_partEffRepAt_eq_zero (T : UnitTPM N) (S : Finset (Fin N))
    (u : State N) (M : Finset (Fin N)) (hM : M ⊆ S) (m : State N) (Z : Finset (Fin N))
    (z : State N) (θ : Partition N M Z) (h : partEffRepAt T S u M m Z z θ = 0) :
    effRepAt T S u M m Z z = 0 := by
  have h1 := effRepAt_le_cutCount_smul T S u M hM m Z z θ
  rw [h, mul_zero] at h1
  exact le_antisymm h1 (effRepAt_nonneg T S u M m Z z)

/-- **`[UB, Theorem 1]` conditioned**: `φ_e` at any partition is still bounded by
`|M| |Z|`.  Conditioning does not cost a factor of the background. -/
theorem theorem_one_at (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (hM : M ⊆ S) (m : State N) (Z : Finset (Fin N)) (z : State N)
    (θ : Partition N M Z) :
    phiEofPartitionAt T S u M m Z z θ ≤ M.card * Z.card := by
  have hcut : (cutCount M Z θ : ℝ) ≤ (M.card : ℝ) * Z.card := by
    exact_mod_cast cutCount_le M Z θ
  rcases eq_or_lt_of_le (partEffRepAt_nonneg T S u M m Z z θ) with h | hpos
  · rw [phiEofPartitionAt,
      effRepAt_eq_zero_of_partEffRepAt_eq_zero T S u M hM m Z z θ h.symm, zero_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have hsel : effRepAt T S u M m Z z ≤ 1 := effRep_le_one T _ _ Z z
    have hinf : pos (Real.logb 2
        (effRepAt T S u M m Z z / partEffRepAt T S u M m Z z θ)) ≤ (cutCount M Z θ : ℝ) := by
      refine pos_le (Nat.cast_nonneg _) ?_
      have hpow : ((2 : ℝ) ^ (cutCount M Z θ)) = (2 : ℝ) ^ ((cutCount M Z θ : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
      rcases eq_or_lt_of_le (effRepAt_nonneg T S u M m Z z) with h0 | h0
      · rw [← h0, zero_div, Real.logb_zero]; exact Nat.cast_nonneg _
      · have hratio : 0 < effRepAt T S u M m Z z / partEffRepAt T S u M m Z z θ :=
          div_pos h0 hpos
        have hle : effRepAt T S u M m Z z / partEffRepAt T S u M m Z z θ
            ≤ 2 ^ (cutCount M Z θ) :=
          (div_le_iff₀ hpos).2 (effRepAt_le_cutCount_smul T S u M hM m Z z θ)
        calc Real.logb 2 (effRepAt T S u M m Z z / partEffRepAt T S u M m Z z θ)
            ≤ Real.logb 2 ((2 : ℝ) ^ (cutCount M Z θ)) :=
              Real.logb_le_logb_of_le (by norm_num) hratio hle
          _ = cutCount M Z θ := by
              rw [hpow, Real.logb_rpow (by norm_num) (by norm_num)]
    calc phiEofPartitionAt T S u M m Z z θ
        = effRepAt T S u M m Z z * pos (Real.logb 2
            (effRepAt T S u M m Z z / partEffRepAt T S u M m Z z θ)) := rfl
      _ ≤ 1 * ((M.card : ℝ) * Z.card) :=
          mul_le_mul hsel (hinf.trans hcut) (pos_nonneg _) zero_le_one
      _ = (M.card : ℝ) * Z.card := one_mul _

lemma phiEatAt_le (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (hM : M ⊆ S) (m : State N) (Z : Finset (Fin N)) (z : State N) :
    phiEatAt T S u M m Z z ≤ M.card * Z.card :=
  sup'OrZero_le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    fun θ _ => theorem_one_at T S u M hM m Z z θ

lemma phiEpurviewAt_le (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (hM : M ⊆ S) (m : State N) (Z : Finset (Fin N)) :
    phiEpurviewAt T S u M m Z ≤ M.card * Z.card :=
  Finset.sup'_le _ _ fun z _ => phiEatAt_le T S u M hM m Z z

/-- **`[UB, Theorem 1]` for the conditioned `φ_d`**, propagated through the exclusion step
`[IIT4, Eq 46]`.  The constant is `|M| |S|`: the same one `phiD_le` proves for the
whole substrate. -/
theorem phiDAt_le (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (hM : M ⊆ S) (m : State N) :
    phiDAt T S u M m ≤ M.card * S.card := by
  refine (min_le_right _ _).trans ?_
  rw [phiEmechAt]
  refine Finset.sup'_le _ _ fun Z hZ => (phiEpurviewAt_le T S u M hM m Z).trans ?_
  have hc : (Z.card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.mem_powerset.1 hZ)
  exact mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)

/-! ## The conditioned purview selection `[IIT4, Eq 45]`

`[IIT4, Eq 45]` picks the purview-with-state maximizing `φ_e`, and `φ_e` is now the
conditioned one, so the candidate set and the maximum must both be taken here rather than
borrowed from `IIT/System.lean`.  Everything else about the selection is unchanged: the
candidates are the maximal effect states over each `Z ⊆ S`, and `∅` is always one, which
is what keeps the set nonempty. -/

/-- The candidate effect purviews-with-state, conditioned. -/
noncomputable def effCandidatesAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) : Finset (Finset (Fin N) × State N) :=
  S.powerset.biUnion fun Z => (maxEffStatesAt T S u M m Z).image fun z => (Z, z)

/-- The candidate cause purviews-with-state, conditioned. -/
noncomputable def causeCandidatesAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) : Finset (Finset (Fin N) × State N) :=
  S.powerset.biUnion fun Z => (maxCauseStatesAt T S u M m Z).image fun z => (Z, z)

lemma effCandidatesAt_nonempty (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) : (effCandidatesAt T S u M m).Nonempty := by
  obtain ⟨z, hz⟩ := argmaxSet_nonempty (iiEAt T S u M m ∅)
  exact ⟨(∅, z), by
    rw [effCandidatesAt, Finset.mem_biUnion]
    exact ⟨∅, Finset.empty_mem_powerset S, Finset.mem_image_of_mem _ hz⟩⟩

lemma causeCandidatesAt_nonempty (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) : (causeCandidatesAt T S u M m).Nonempty := by
  obtain ⟨z, hz⟩ := argmaxSet_nonempty (iiCAt T S u M m ∅)
  exact ⟨(∅, z), by
    rw [causeCandidatesAt, Finset.mem_biUnion]
    exact ⟨∅, Finset.empty_mem_powerset S, Finset.mem_image_of_mem _ hz⟩⟩

/-- **`z*_e(m)`** `[IIT4, Eq 45]`, conditioned. -/
noncomputable def maxEffPurviewsAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) : Finset (Finset (Fin N) × State N) :=
  (effCandidatesAt T S u M m).filter fun p =>
    ∀ q ∈ effCandidatesAt T S u M m,
      phiEatAt T S u M m q.1 q.2 ≤ phiEatAt T S u M m p.1 p.2

/-- **`z*_c(m)`** `[IIT4, Eq 45]`, cause side, conditioned. -/
noncomputable def maxCausePurviewsAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) : Finset (Finset (Fin N) × State N) :=
  (causeCandidatesAt T S u M m).filter fun p =>
    ∀ q ∈ causeCandidatesAt T S u M m,
      phiCatAt T S u q.1 q.2 M m ≤ phiCatAt T S u p.1 p.2 M m

lemma maxEffPurviewsAt_nonempty (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) : (maxEffPurviewsAt T S u M m).Nonempty := by
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (effCandidatesAt T S u M m)
    (fun q => phiEatAt T S u M m q.1 q.2) (effCandidatesAt_nonempty T S u M m)
  exact ⟨p, Finset.mem_filter.2 ⟨hp, hmax⟩⟩

lemma maxCausePurviewsAt_nonempty (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) : (maxCausePurviewsAt T S u M m).Nonempty := by
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (causeCandidatesAt T S u M m)
    (fun q => phiCatAt T S u q.1 q.2 M m) (causeCandidatesAt_nonempty T S u M m)
  exact ⟨p, Finset.mem_filter.2 ⟨hp, hmax⟩⟩

/-- The value at a maximal effect purview **is** `φ_e(m)`, conditioned: the same
two-sided argument as `phiEat_of_mem_maxEffPurviews`, every ingredient conditioned. -/
theorem phiEatAt_of_mem_maxEffPurviewsAt (T : UnitTPM N) (S : Finset (Fin N))
    (u : State N) (M : Finset (Fin N)) (m : State N) {p : Finset (Fin N) × State N}
    (hp : p ∈ maxEffPurviewsAt T S u M m) :
    phiEatAt T S u M m p.1 p.2 = phiEmechAt T S u M m := by
  obtain ⟨hpmem, hpmax⟩ := Finset.mem_filter.1 hp
  obtain ⟨Z, hZ, hz⟩ := Finset.mem_biUnion.1 hpmem
  obtain ⟨z, hzmem, hzeq⟩ := Finset.mem_image.1 hz
  have h1 : p.1 = Z := (Prod.ext_iff.1 hzeq).1.symm
  have h2 : p.2 = z := (Prod.ext_iff.1 hzeq).2.symm
  subst h1; subst h2
  refine le_antisymm ?_ ?_
  · rw [phiEmechAt]
    refine le_trans ?_ (Finset.le_sup'
      (f := fun Y => phiEpurviewAt T S u M m Y) hZ)
    rw [phiEpurviewAt]
    exact Finset.le_sup' (f := fun w => phiEatAt T S u M m p.1 w) hzmem
  · rw [phiEmechAt]
    refine Finset.sup'_le _ _ fun Y hY => ?_
    rw [phiEpurviewAt]
    refine Finset.sup'_le _ _ fun w hw => ?_
    exact hpmax (Y, w) (Finset.mem_biUnion.2 ⟨Y, hY, Finset.mem_image_of_mem _ hw⟩)

/-- The cause-side twin. -/
theorem phiCatAt_of_mem_maxCausePurviewsAt (T : UnitTPM N) (S : Finset (Fin N))
    (u : State N) (M : Finset (Fin N)) (m : State N) {p : Finset (Fin N) × State N}
    (hp : p ∈ maxCausePurviewsAt T S u M m) :
    phiCatAt T S u p.1 p.2 M m = phiCmechAt T S u M m := by
  obtain ⟨hpmem, hpmax⟩ := Finset.mem_filter.1 hp
  obtain ⟨Z, hZ, hz⟩ := Finset.mem_biUnion.1 hpmem
  obtain ⟨z, hzmem, hzeq⟩ := Finset.mem_image.1 hz
  have h1 : p.1 = Z := (Prod.ext_iff.1 hzeq).1.symm
  have h2 : p.2 = z := (Prod.ext_iff.1 hzeq).2.symm
  subst h1; subst h2
  refine le_antisymm ?_ ?_
  · rw [phiCmechAt]
    refine le_trans ?_ (Finset.le_sup'
      (f := fun Y => phiCpurviewAt T S u M m Y) hZ)
    rw [phiCpurviewAt]
    exact Finset.le_sup' (f := fun w => phiCatAt T S u p.1 w M m) hzmem
  · rw [phiCmechAt]
    refine Finset.sup'_le _ _ fun Y hY => ?_
    rw [phiCpurviewAt]
    refine Finset.sup'_le _ _ fun w hw => ?_
    exact hpmax (Y, w) (Finset.mem_biUnion.2 ⟨Y, hY, Finset.mem_image_of_mem _ hw⟩)

/-- `φ_e` over the empty purview is zero, conditioned: both products are empty. -/
lemma phiEatAt_empty_purview (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m z : State N) : phiEatAt T S u M m ∅ z = 0 := by
  refine le_antisymm ?_ (sup'OrZero_nonneg fun θ _ => phiEofPartitionAt_nonneg T S u M m ∅ z θ)
  rw [phiEatAt]
  refine sup'OrZero_le le_rfl fun θ _ => ?_
  simp [phiEofPartitionAt, effRepAt, effRep, partEffRepAt, pos]

/-- `φ_c` over the empty purview is zero, conditioned: every `causePart` is empty, so the
partitioned term is the unpartitioned one. -/
lemma phiCatAt_empty_purview (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m z : State N) : phiCatAt T S u ∅ z M m = 0 := by
  refine le_antisymm ?_
    (sup'OrZero_nonneg fun θ _ => phiCofPartitionAt_nonneg T S u ∅ z M m θ)
  rw [phiCatAt]
  refine sup'OrZero_le le_rfl fun θ _ => ?_
  have hpart : ∀ k : Fin N, θ.causePart k = ∅ :=
    fun k => Finset.subset_empty.1 (θ.causePart_subset k)
  have hpc : partCauseFwdAt T S u ∅ z M m θ = causeFwdAt T S u ∅ z M m := by
    rw [partCauseFwdAt, causeFwdAt]
    exact Finset.prod_congr rfl fun k _ => by rw [hpart k]
  rw [phiCofPartitionAt, hpc]
  rcases eq_or_ne (causeFwdAt T S u ∅ z M m) 0 with h0 | h0
  · simp [h0, pos]
  · rw [div_self h0]
    simp [pos]

/-- **A maximal effect purview is nonempty once `φ_e(m) > 0`**, conditioned: `[IIT4,
Eq 45]` admits `Z = ∅` as a candidate and it specifies nothing, so the maximum cannot sit
there. -/
lemma maxEffPurviewsAt_fst_nonempty {T : UnitTPM N} {S : Finset (Fin N)} {u : State N}
    {M : Finset (Fin N)} {m : State N} (hpos : 0 < phiEmechAt T S u M m)
    {p : Finset (Fin N) × State N} (hp : p ∈ maxEffPurviewsAt T S u M m) :
    p.1.Nonempty := by
  rcases Finset.eq_empty_or_nonempty p.1 with h0 | h
  · exfalso
    have hv := phiEatAt_of_mem_maxEffPurviewsAt T S u M m hp
    rw [h0, phiEatAt_empty_purview] at hv
    exact absurd hv.symm hpos.ne'
  · exact h

/-- The cause-side twin. -/
lemma maxCausePurviewsAt_fst_nonempty {T : UnitTPM N} {S : Finset (Fin N)} {u : State N}
    {M : Finset (Fin N)} {m : State N} (hpos : 0 < phiCmechAt T S u M m)
    {p : Finset (Fin N) × State N} (hp : p ∈ maxCausePurviewsAt T S u M m) :
    p.1.Nonempty := by
  rcases Finset.eq_empty_or_nonempty p.1 with h0 | h
  · exfalso
    have hv := phiCatAt_of_mem_maxCausePurviewsAt T S u M m hp
    rw [h0, phiCatAt_empty_purview] at hv
    exact absurd hv.symm hpos.ne'
  · exact h

/-! ## The conditioned distinction set and `Φ` `[IIT4, Eqs 48, 59]`

`IsDistinctionMech` asks for `φ_d > 0` and a congruent pair of maximal purviews.  Both
are now taken inside the candidate system, so the distinction set of a complex is the one
`[IIT4, Eq 48]` describes rather than the one the substrate-wide repertoires give.  At
`S = U` the two coincide, which is `distinctionMechsAt_univ` below. -/

open scoped Classical in
/-- **`D`** `[IIT4, Eq 48]` for a candidate system, with the background conditioned. -/
noncomputable def distinctionMechsAt (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) :
    Finset (Finset (Fin N)) :=
  S.powerset.filter fun M =>
    0 < phiDAt T S u M s ∧
      ∃ pc ∈ maxCausePurviewsAt T S u M s, ∃ pe ∈ maxEffPurviewsAt T S u M s,
        Congruent T S u s (stated pc.1 pc.2) (stated pe.1 pe.2)

/-- The distinction-side sum of `Φ` `[IIT4, Eq 59]`, conditioned. -/
noncomputable def PhiDistinctionsAt (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) :
    ℝ :=
  ∑ M ∈ distinctionMechsAt T S u s, phiDAt T S u M s

lemma PhiDistinctionsAt_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) :
    0 ≤ PhiDistinctionsAt T S u s :=
  Finset.sum_nonneg fun M hM => le_of_lt (by
    classical
    exact ((Finset.mem_filter.1 hM).2).1)

/-- **At `S = U` the conditioned distinction set is the one `IIT/System.lean` defines.**
So the development the validation suites exercise is the whole-substrate instance of this,
and nothing proved there is superseded. -/
theorem distinctionMechsAt_univ (T : UnitTPM N) (u s : State N)
    (hu : 0 < ∑ v : State N, fullProb T v u) :
    distinctionMechsAt T Finset.univ u s = distinctionMechs T Finset.univ u s := by
  classical
  have he : ∀ M : Finset (Fin N),
      maxEffPurviewsAt T Finset.univ u M s = maxEffPurviews T Finset.univ M s := by
    intro M
    have hc : effCandidatesAt T Finset.univ u M s = effCandidates T Finset.univ M s := by
      rw [effCandidatesAt, effCandidates]
      exact Finset.biUnion_congr rfl fun Z _ => by rw [maxEffStatesAt_univ]
    rw [maxEffPurviewsAt, maxEffPurviews, hc]
    exact Finset.filter_congr fun p _ => by
      simp only [phiEatAt_univ]
  have hcz : ∀ M : Finset (Fin N),
      maxCausePurviewsAt T Finset.univ u M s = maxCausePurviews T Finset.univ M s := by
    intro M
    have hc : causeCandidatesAt T Finset.univ u M s = causeCandidates T Finset.univ M s := by
      rw [causeCandidatesAt, causeCandidates]
      exact Finset.biUnion_congr rfl fun Z _ => by rw [maxCauseStatesAt_univ _ _ _ _ _ hu]
    rw [maxCausePurviewsAt, maxCausePurviews, hc]
    exact Finset.filter_congr fun p _ => by
      simp only [phiCatAt_univ _ _ _ _ _ _ hu]
  ext M
  rw [mem_distinctionMechs]
  simp only [distinctionMechsAt, Finset.mem_filter, IsDistinctionMech,
    phiDAt_univ _ _ _ _ hu, he, hcz, Finset.mem_powerset]

theorem PhiDistinctionsAt_univ (T : UnitTPM N) (u s : State N)
    (hu : 0 < ∑ v : State N, fullProb T v u) :
    PhiDistinctionsAt T Finset.univ u s = PhiDistinctions T Finset.univ u s := by
  rw [PhiDistinctionsAt, PhiDistinctions, distinctionMechsAt_univ T u s hu]
  exact Finset.sum_congr rfl fun M _ => phiDAt_univ T u M s hu

/-- **`[UB, Eq 6]` for a candidate system.**  The distinction sum of a complex is bounded
by the same expression, because each `φ_d` obeys `[UB, Theorem 1]` after conditioning and
there are at most `2 ^ |S|` mechanisms. -/
theorem PhiDistinctionsAt_le (T : UnitTPM N) (u s : State N)
    (hu : 0 < ∑ v : State N, fullProb T v u) :
    PhiDistinctionsAt T Finset.univ u s ≤ (N : ℝ) ^ 2 / 2 * 2 ^ N := by
  rw [PhiDistinctionsAt_univ T u s hu]
  exact PhiDistinctions_le T u s

/-! ## The substrate search `[IIT4, Eqs 24, 25]`

`[IIT4]` does not take a candidate system as given.  It searches: at stage `k` it picks a
substrate maximizing `φ_s` among the subsets of `U_k`, removes it, and repeats on
`U_{k+1} = U_k \ S_k` until nothing is left.  `IsComplex` is the *sufficient condition*
`[IIT4, Eq 26]` states for a substrate to be maximal, and is strictly stronger than being
returned by this search; formalizing the search is what lets the two be compared.

The recursion is on the cardinality of `U`, which strictly decreases because each stage
removes a nonempty substrate. -/

open scoped Classical in
/-- The substrates of `U` maximizing `φ_s` `[IIT4, Eq 25]`, all ties kept. -/
noncomputable def argmaxSubstrates (T : UnitTPM N) (u s : State N) (U : Finset (Fin N)) :
    Finset (Finset (Fin N)) :=
  (U.powerset.filter fun S => S.Nonempty).filter fun S =>
    ∀ S' ∈ U.powerset.filter (fun S' => S'.Nonempty),
      sysPhi T S' u s ≤ sysPhi T S u s

lemma argmaxSubstrates_subset {T : UnitTPM N} {u s : State N} {U S : Finset (Fin N)}
    (h : S ∈ argmaxSubstrates T u s U) : S ⊆ U := by
  classical
  exact Finset.mem_powerset.1 (Finset.mem_filter.1 (Finset.mem_filter.1 h).1).1

lemma argmaxSubstrates_nonempty_elem {T : UnitTPM N} {u s : State N} {U S : Finset (Fin N)}
    (h : S ∈ argmaxSubstrates T u s U) : S.Nonempty := by
  classical
  exact (Finset.mem_filter.1 (Finset.mem_filter.1 h).1).2

/-- **The `[IIT4, Eqs 24, 25]` search**, as a list of maximizing substrates in the order the recursion
produces them.  At each stage a maximizing substrate is chosen -- `[IIT4, S1 Text]`
resolves the choice among ties by `Φ`, and where that also ties the tied systems do not
qualify, so the choice here is a parameter exactly as `Selector` is at the purview level. -/
noncomputable def complexSearch (T : UnitTPM N) (u s : State N)
    (pick : Finset (Fin N) → Finset (Fin N)) : Finset (Fin N) → List (Finset (Fin N))
  | U =>
    if h : (argmaxSubstrates T u s U).Nonempty ∧ (pick U) ∈ argmaxSubstrates T u s U then
      have hne : (pick U).Nonempty := argmaxSubstrates_nonempty_elem h.2
      have hsub : (pick U) ⊆ U := argmaxSubstrates_subset h.2
      have : (U \ pick U).card < U.card := by
        refine Finset.card_lt_card ?_
        obtain ⟨a, ha⟩ := hne
        exact ⟨Finset.sdiff_subset, fun hc => (Finset.mem_sdiff.1 (hc (hsub ha))).2 ha⟩
      pick U :: complexSearch T u s pick (U \ pick U)
    else []
  termination_by U => U.card

/-- **Every substrate the search returns is nonempty.**  That is what this states and no
more: termination is discharged by the recursion measure at the definition, and containment in
`U` is `argmaxSubstrates_subset`, proved separately. -/
theorem complexSearch_mem_nonempty (T : UnitTPM N) (u s : State N)
    (pick : Finset (Fin N) → Finset (Fin N)) :
    ∀ U : Finset (Fin N), ∀ S ∈ complexSearch T u s pick U, S.Nonempty := by
  intro U
  induction U using Finset.strongInduction with
  | _ U ih =>
    intro S hS
    rw [complexSearch] at hS
    split at hS
    · rename_i h
      rcases List.mem_cons.1 hS with rfl | hS'
      · exact argmaxSubstrates_nonempty_elem h.2
      · refine ih (U \ pick U) ?_ S hS'
        obtain ⟨a, ha⟩ := argmaxSubstrates_nonempty_elem h.2
        exact ⟨Finset.sdiff_subset, fun hc =>
          (Finset.mem_sdiff.1 (hc (argmaxSubstrates_subset h.2 ha))).2 ha⟩
    · simp at hS

/-! ### `[IIT4, Eq 26]` against `[IIT4, Eqs 24, 25]`

`IsComplex` is `[IIT4, Eq 26]`, the *sufficient* condition; `argmaxSubstrates` is
`[IIT4, Eq 25]`, what the search actually picks.  They differ in exactly two ways, and
naming each as a hypothesis turns them into a pair of implications:

* `[IIT4, Eq 26]` quantifies only over substrates that **overlap** `S`, while
  `[IIT4, Eq 25]`'s `argmax` ranges over every nonempty subset of `U`.  So a complex can
  lose to a *disjoint* competitor and still satisfy `[IIT4, Eq 26]`; `disjoint_le` is what
  rules that out.
* `[IIT4, Eq 25]` keeps ties, `[IIT4, Eq 26]` demands a strict maximum.  So an argmax
  element is a complex only when the maximum is attained uniquely among overlapping
  competitors; `overlap_ne` is what rules that out.

Neither hypothesis is ours: they are the two places where the source's own two
characterizations of a maximal substrate differ. -/

/-- **A maximizing substrate is a complex** once the maximum is not tied among the
substrates that overlap it. -/
theorem isComplex_of_mem_argmaxSubstrates {T : UnitTPM N} {u s : State N}
    {U S : Finset (Fin N)} (h : S ∈ argmaxSubstrates T u s U)
    (overlap_ne : ∀ S' ⊆ U, S' ≠ S → (S ∩ S').Nonempty →
      sysPhi T S' u s ≠ sysPhi T S u s) :
    IsComplex T u U S s := by
  classical
  refine ⟨argmaxSubstrates_subset h, fun S' hsub hne hover => ?_⟩
  have hS' : S'.Nonempty := by
    obtain ⟨a, ha⟩ := hover
    exact ⟨a, (Finset.mem_inter.1 ha).2⟩
  have hle : sysPhi T S' u s ≤ sysPhi T S u s :=
    (Finset.mem_filter.1 h).2 S'
      (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hsub, hS'⟩)
  exact lt_of_le_of_ne hle (overlap_ne S' hsub hne hover)

/-- **A complex is a maximizing substrate** once it also beats the substrates disjoint
from it, which `[IIT4, Eq 26]` never asks about. -/
theorem mem_argmaxSubstrates_of_isComplex {T : UnitTPM N} {u s : State N}
    {U S : Finset (Fin N)} (h : IsComplex T u U S s) (hne : S.Nonempty)
    (disjoint_le : ∀ S' ⊆ U, Disjoint S S' → sysPhi T S' u s ≤ sysPhi T S u s) :
    S ∈ argmaxSubstrates T u s U := by
  classical
  refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_powerset.2 h.1, hne⟩, ?_⟩
  intro S' hS'
  have hsub : S' ⊆ U := Finset.mem_powerset.1 (Finset.mem_filter.1 hS').1
  rcases eq_or_ne S' S with rfl | hne'
  · exact le_rfl
  · rcases Finset.eq_empty_or_nonempty (S ∩ S') with h0 | hover
    · exact disjoint_le S' hsub (Finset.disjoint_iff_inter_eq_empty.2 h0)
    · exact (h.2 S' hsub hne' hover).le

/-- **And then the search returns it.**  The choice among ties is a parameter, so what is
provable is that a `pick` selecting `S` produces `S`; `[IIT4, S1 Text]` is what fixes
`pick` in the source. -/
theorem mem_complexSearch_of_mem_argmaxSubstrates {T : UnitTPM N} {u s : State N}
    {U S : Finset (Fin N)} (pick : Finset (Fin N) → Finset (Fin N))
    (h : S ∈ argmaxSubstrates T u s U) (hpick : pick U = S) :
    S ∈ complexSearch T u s pick U := by
  rw [complexSearch]
  rw [dif_pos ⟨⟨S, h⟩, by rw [hpick]; exact h⟩]
  exact List.mem_cons.2 (Or.inl hpick.symm)

/-- **The two characterizations agree** under both hypotheses: a substrate satisfies
`[IIT4, Eq 26]` and is returned by the `[IIT4, Eqs 24, 25]` search at its first stage. -/
theorem isComplex_iff_mem_argmaxSubstrates {T : UnitTPM N} {u s : State N}
    {U S : Finset (Fin N)} (hne : S.Nonempty)
    (overlap_ne : ∀ S' ⊆ U, S' ≠ S → (S ∩ S').Nonempty →
      sysPhi T S' u s ≠ sysPhi T S u s)
    (disjoint_le : ∀ S' ⊆ U, Disjoint S S' → sysPhi T S' u s ≤ sysPhi T S u s) :
    IsComplex T u U S s ↔ S ∈ argmaxSubstrates T u s U :=
  ⟨fun h => mem_argmaxSubstrates_of_isComplex h hne disjoint_le,
   fun h => isComplex_of_mem_argmaxSubstrates h overlap_ne⟩

/-! ## `Φ` of the complex -- the join

`IIT/System.lean` finds candidate complexes for arbitrary `S ⊆ U`; `IIT/Phi.lean`
evaluates `Φ` only at `S = U`.  Neither file can state `Φ` *of the complex*, which is
`[IIT4]`'s actual output.  With the mechanism level conditioned, it can be stated. -/

/-- **The distinction sum of the complex** `[IIT4, Eqs 26, 48]`: the first of
`[IIT4, Eq 59]`'s three terms, at the substrate the exclusion postulate selects and with
that substrate's own background conditioning. -/
noncomputable def PhiDistinctionsOfComplexAt (T : UnitTPM N) (u : State N)
    (U S : Finset (Fin N)) (s : State N) (_h : IsComplex T u U S s) : ℝ :=
  PhiDistinctionsAt T S u s

/-- **The join is consistent with the whole-substrate development.**  When the complex is
the entire substrate -- the case `IIT/Phi.lean` was exact for all along -- the
distinction sum of the complex is the one the validation suites exercise. -/
theorem PhiDistinctionsOfComplexAt_univ (T : UnitTPM N) (u s : State N)
    (h : IsComplex T u Finset.univ Finset.univ s)
    (hu : 0 < ∑ v : State N, fullProb T v u) :
    PhiDistinctionsOfComplexAt T u Finset.univ Finset.univ s h
      = PhiDistinctions T Finset.univ u s :=
  PhiDistinctionsAt_univ T u s hu

/-- **`[UB, Eq 6]` for the distinction sum of a complex.** -/
theorem PhiDistinctionsOfComplexAt_le (T : UnitTPM N) (u s : State N)
    (h : IsComplex T u Finset.univ Finset.univ s)
    (hu : 0 < ∑ v : State N, fullProb T v u) :
    PhiDistinctionsOfComplexAt T u Finset.univ Finset.univ s h ≤ (N : ℝ) ^ 2 / 2 * 2 ^ N :=
  PhiDistinctionsAt_le T u s hu

/-! ## `Φ` of a conditioned complex `[IIT4, Eqs 48, 56, 58, 59]`

`PhiDistinctionsAt` is only the first of `[IIT4, Eq 59]`'s three sums.  The other two run
over `R(D)` and the self-relations, and both depend on `(T, S, u, s)` *only* through the
`Finset (Distinction N)` they are handed -- `relPhi` and `selfRelPhi` read the bundles and
nothing else.  So the relation layer is factored out of `IIT/System.lean`'s `PhiOf` once,
proved to be that `PhiOf`, and then reused on the conditioned distinction set. -/

/-- `[IIT4, Eq 56]` on a bare set of distinctions. -/
noncomputable def relationSetsOf (D : Finset (Distinction N)) :
    Finset (Finset (Distinction N)) :=
  D.powerset.filter fun d => ∃ h : d.Nonempty, 2 ≤ d.card ∧ 0 < relPhi d h

/-- `[UB, Eq 9]` on a bare set of distinctions. -/
noncomputable def selfRelationsOf (D : Finset (Distinction N)) : Finset (Distinction N) :=
  D.filter fun d => 0 < selfRelPhi d

/-- **`[IIT4, Eq 59]` as a function of the cause-effect structure alone.** -/
noncomputable def PhiOfStructure (D : Finset (Distinction N)) : ℝ :=
  (∑ d ∈ D, d.phi) + (∑ d ∈ relationSetsOf D, relPhiOrZero d)
    + ∑ d ∈ selfRelationsOf D, selfRelPhi d

/-- **The factoring is exact.**  `IIT/System.lean`'s `Φ` is this function applied to the
distinctions the selector produces, so nothing about `PhiOf` is changed or re-stated. -/
theorem PhiOf_eq_structure (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (σ : Selector T S u s) :
    PhiOf T S u s σ = PhiOfStructure (distinctions T S u s σ) := rfl

lemma PhiOfStructure_nonneg (D : Finset (Distinction N)) : 0 ≤ PhiOfStructure D := by
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · exact Finset.sum_nonneg fun d _ => d.phi_pos.le
  · exact Finset.sum_nonneg fun d _ => relPhiOrZero_nonneg d
  · classical
    exact Finset.sum_nonneg fun d hd => (Finset.mem_filter.1 hd).2.le

/-! ### The conditioned tie-break

`SelectorAt` is `Selector` with every purview maximum taken at the conditioned mechanism
`condSet S M` and the conditioned state `condState S u s`, which is exactly what
`distinctionMechsAt` requires of its members.  At `S = U` the two structures have
definitionally equal fields, which is what makes `PhiOfAt_univ` go through. -/

/-- A tie-break for the conditioned mechanism level `[IIT4, S1 Text]`. -/
structure SelectorAt (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) where
  /-- The chosen cause purview-with-state. -/
  causeOf : Finset (Fin N) → Finset (Fin N) × State N
  /-- The chosen effect purview-with-state. -/
  effectOf : Finset (Fin N) → Finset (Fin N) × State N
  cause_mem : ∀ M ∈ distinctionMechsAt T S u s, causeOf M ∈ maxCausePurviewsAt T S u M s
  effect_mem : ∀ M ∈ distinctionMechsAt T S u s, effectOf M ∈ maxEffPurviewsAt T S u M s
  cause_nonempty : ∀ M ∈ distinctionMechsAt T S u s,
    (stated (causeOf M).1 (causeOf M).2).Nonempty
  effect_nonempty : ∀ M ∈ distinctionMechsAt T S u s,
    (stated (effectOf M).1 (effectOf M).2).Nonempty
  congruent : ∀ M ∈ distinctionMechsAt T S u s,
    Congruent T S u s (stated (causeOf M).1 (causeOf M).2)
      (stated (effectOf M).1 (effectOf M).2)

lemma mem_distinctionMechsAt {T : UnitTPM N} {S : Finset (Fin N)} {u s : State N}
    {M : Finset (Fin N)} :
    M ∈ distinctionMechsAt T S u s ↔ M ⊆ S ∧ (0 < phiDAt T S u M s ∧
      ∃ pc ∈ maxCausePurviewsAt T S u M s, ∃ pe ∈ maxEffPurviewsAt T S u M s,
        Congruent T S u s (stated pc.1 pc.2) (stated pe.1 pe.2)) := by
  classical
  rw [distinctionMechsAt, Finset.mem_filter, Finset.mem_powerset]

/-- The conditioned counterpart of `exists_congruent_pair`: `φ_d > 0` at the conditioned
mechanism forces both maximal purviews to be nonempty, by the same empty-purview values. -/
lemma exists_congruent_pairAt {T : UnitTPM N} {S : Finset (Fin N)} {u s : State N}
    {M : Finset (Fin N)} (hM : M ∈ distinctionMechsAt T S u s) :
    ∃ p : (Finset (Fin N) × State N) × (Finset (Fin N) × State N),
      p.1 ∈ maxCausePurviewsAt T S u M s ∧ p.2 ∈ maxEffPurviewsAt T S u M s ∧
        (stated p.1.1 p.1.2).Nonempty ∧ (stated p.2.1 p.2.2).Nonempty ∧
        Congruent T S u s (stated p.1.1 p.1.2) (stated p.2.1 p.2.2) := by
  obtain ⟨hpos, pc, hpc, pe, hpe, hcong⟩ := (mem_distinctionMechsAt.1 hM).2
  rw [phiDAt] at hpos
  refine ⟨(pc, pe), hpc, hpe, ?_, ?_, hcong⟩
  · exact stated_nonempty_iff.2 (maxCausePurviewsAt_fst_nonempty
      (lt_of_lt_of_le hpos (min_le_left _ _)) hpc)
  · exact stated_nonempty_iff.2 (maxEffPurviewsAt_fst_nonempty
      (lt_of_lt_of_le hpos (min_le_right _ _)) hpe)

open scoped Classical in
noncomputable def congruentPairAt (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (M : Finset (Fin N)) : (Finset (Fin N) × State N) × (Finset (Fin N) × State N) :=
  if h : M ∈ distinctionMechsAt T S u s then (exists_congruent_pairAt h).choose
  else ((∅, s), (∅, s))

lemma congruentPairAt_spec {T : UnitTPM N} {S : Finset (Fin N)} {u s : State N}
    {M : Finset (Fin N)} (hM : M ∈ distinctionMechsAt T S u s) :
    (congruentPairAt T S u s M).1 ∈ maxCausePurviewsAt T S u M s ∧
      (congruentPairAt T S u s M).2 ∈ maxEffPurviewsAt T S u M s ∧
      (stated (congruentPairAt T S u s M).1.1 (congruentPairAt T S u s M).1.2).Nonempty ∧
      (stated (congruentPairAt T S u s M).2.1 (congruentPairAt T S u s M).2.2).Nonempty ∧
      Congruent T S u s
        (stated (congruentPairAt T S u s M).1.1 (congruentPairAt T S u s M).1.2)
        (stated (congruentPairAt T S u s M).2.1 (congruentPairAt T S u s M).2.2) := by
  classical
  rw [congruentPairAt, dif_pos hM]
  exact (exists_congruent_pairAt hM).choose_spec

/-- **`SelectorAt` is inhabited**, so `PhiOfAt` and `PhiOfComplexAt` have content. -/
noncomputable instance instNonemptySelectorAt (T : UnitTPM N) (S : Finset (Fin N))
    (u s : State N) : Nonempty (SelectorAt T S u s) :=
  ⟨{ causeOf := fun M => (congruentPairAt T S u s M).1
     effectOf := fun M => (congruentPairAt T S u s M).2
     cause_mem := fun M hM => (congruentPairAt_spec hM).1
     effect_mem := fun M hM => (congruentPairAt_spec hM).2.1
     cause_nonempty := fun M hM => (congruentPairAt_spec hM).2.2.1
     effect_nonempty := fun M hM => (congruentPairAt_spec hM).2.2.2.1
     congruent := fun M hM => (congruentPairAt_spec hM).2.2.2.2 }⟩

/-! ### The conditioned cause-effect structure and `Φ` -/

/-- The conditioned `Distinction` bundle.  Its `mech` field is `M`, not `condSet S M`:
the distinction belongs to the candidate system, the conditioning only says how its
repertoires were computed. -/
noncomputable def distinctionOfAt (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (σ : SelectorAt T S u s) (M : Finset (Fin N)) (hM : M ∈ distinctionMechsAt T S u s) :
    Distinction N where
  mech := M
  zc := stated (σ.causeOf M).1 (σ.causeOf M).2
  ze := stated (σ.effectOf M).1 (σ.effectOf M).2
  zc_nonempty := σ.cause_nonempty M hM
  ze_nonempty := σ.effect_nonempty M hM
  phi := phiDAt T S u M s
  phi_pos := (mem_distinctionMechsAt.1 hM).2.1

/-- **`D`** conditioned `[IIT4, Eq 48]`. -/
noncomputable def distinctionsAt (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (σ : SelectorAt T S u s) : Finset (Distinction N) :=
  (distinctionMechsAt T S u s).attach.image fun M => distinctionOfAt T S u s σ M.1 M.2

/-- **`Φ`** of a candidate system, conditioned `[IIT4, Eq 59]`: all three sums, not just
the distinctions. -/
noncomputable def PhiOfAt (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (σ : SelectorAt T S u s) : ℝ :=
  PhiOfStructure (distinctionsAt T S u s σ)

lemma PhiOfAt_nonneg (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (σ : SelectorAt T S u s) : 0 ≤ PhiOfAt T S u s σ :=
  PhiOfStructure_nonneg _

/-- A `SelectorAt` on the whole substrate **is** a `Selector`: `condSet` and `condState`
are the identity there and `distinctionMechsAt_univ` matches the domains. -/
noncomputable def SelectorAt.toSelector {T : UnitTPM N} {u s : State N}
    (σ : SelectorAt T Finset.univ u s) (hu : 0 < ∑ v : State N, fullProb T v u) :
    Selector T Finset.univ u s where
  causeOf := σ.causeOf
  effectOf := σ.effectOf
  cause_mem := by
    intro M hM
    have h := σ.cause_mem M (by rwa [distinctionMechsAt_univ T u s hu])
    rwa [show maxCausePurviewsAt T Finset.univ u M s = maxCausePurviews T Finset.univ M s
      from by
        have hc : causeCandidatesAt T Finset.univ u M s
            = causeCandidates T Finset.univ M s := by
          rw [causeCandidatesAt, causeCandidates]
          exact Finset.biUnion_congr rfl fun Z _ => by
            rw [maxCauseStatesAt_univ _ _ _ _ _ hu]
        rw [maxCausePurviewsAt, maxCausePurviews, hc]
        exact Finset.filter_congr fun p _ => by
          simp only [phiCatAt_univ _ _ _ _ _ _ hu]] at h
  effect_mem := by
    intro M hM
    have h := σ.effect_mem M (by rwa [distinctionMechsAt_univ T u s hu])
    rwa [show maxEffPurviewsAt T Finset.univ u M s = maxEffPurviews T Finset.univ M s
      from by
        have hc : effCandidatesAt T Finset.univ u M s = effCandidates T Finset.univ M s := by
          rw [effCandidatesAt, effCandidates]
          exact Finset.biUnion_congr rfl fun Z _ => by rw [maxEffStatesAt_univ]
        rw [maxEffPurviewsAt, maxEffPurviews, hc]
        exact Finset.filter_congr fun p _ => by simp only [phiEatAt_univ]] at h
  cause_nonempty := fun M hM =>
    σ.cause_nonempty M (by rwa [distinctionMechsAt_univ T u s hu])
  effect_nonempty := fun M hM =>
    σ.effect_nonempty M (by rwa [distinctionMechsAt_univ T u s hu])
  congruent := fun M hM => σ.congruent M (by rwa [distinctionMechsAt_univ T u s hu])

/-- **The conditioned cause-effect structure is the unconditioned one at `S = U`.** -/
theorem distinctionsAt_univ (T : UnitTPM N) (u s : State N)
    (σ : SelectorAt T Finset.univ u s) (hu : 0 < ∑ v : State N, fullProb T v u) :
    distinctionsAt T Finset.univ u s σ
      = distinctions T Finset.univ u s (σ.toSelector hu) := by
  classical
  ext d
  simp only [distinctionsAt, distinctions, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists]
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact ⟨M, by rwa [← distinctionMechsAt_univ T u s hu], by
      simp only [distinctionOfAt, distinctionOf, SelectorAt.toSelector,
        phiDAt_univ _ _ _ _ hu]⟩
  · rintro ⟨M, hM, rfl⟩
    exact ⟨M, by rwa [distinctionMechsAt_univ T u s hu], by
      simp only [distinctionOfAt, distinctionOf, SelectorAt.toSelector,
        phiDAt_univ _ _ _ _ hu]⟩

/-- **`Φ` conditioned is `Φ` at `S = U`.**  Every number the validation suites report for `PhiOf`
therefore certifies this `Φ` too. -/
theorem PhiOfAt_univ (T : UnitTPM N) (u s : State N) (σ : SelectorAt T Finset.univ u s)
    (hu : 0 < ∑ v : State N, fullProb T v u) :
    PhiOfAt T Finset.univ u s σ = PhiOf T Finset.univ u s (σ.toSelector hu) := by
  rw [PhiOfAt, PhiOf_eq_structure, distinctionsAt_univ T u s σ hu]

/-! ### Where the tie-break can and cannot reach

`[IIT4, Eq 45]`'s purview `argmax` ties, often heavily, and `SelectorAt` is the parameter
that resolves it.  The two theorems below say exactly how far that parameter reaches.

`sum_distinctionsAt_phi`: the **distinction half** of `[IIT4, Eq 59]` does not depend on
it at all.  `distinctionMechsAt` mentions no selector, and `distinctionOfAt` records
`phiDAt`, which is a function of `(T, S, u, M, s)` alone; the selector supplies only the
purviews `zc` and `ze`.  So `∑ φ_d` is the same number for every admissible tie-break.

The relation terms are not: `relPhi` reads `Distinction.support = zc ∪ ze`, which is
exactly the part the selector chooses.  So all of `Φ`'s dependence on the purview
tie-break is carried by `∑ φ_r`.  `test/condjoin.py` exhibits this against PyPhi -- where
the purview `argmax` ties, our distinction sum matches PyPhi's and our relation sum does
not -- and this pair of theorems is why that pattern is forced rather than incidental. -/

/-- **The distinction half of `Φ` is tie-independent.**  For every `SelectorAt`, the first
sum of `[IIT4, Eq 59]` is `PhiDistinctionsAt`, a function of the transition probabilities,
the candidate system and its state alone. -/
theorem sum_distinctionsAt_phi (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (σ : SelectorAt T S u s) :
    (∑ d ∈ distinctionsAt T S u s σ, d.phi) = PhiDistinctionsAt T S u s := by
  classical
  rw [distinctionsAt, PhiDistinctionsAt]
  rw [Finset.sum_image (by
    rintro ⟨M1, h1⟩ - ⟨M2, h2⟩ - heq
    have : M1 = M2 := congrArg Distinction.mech heq
    subst this
    rfl)]
  exact Finset.sum_attach (distinctionMechsAt T S u s) (fun M => phiDAt T S u M s)

/-- **Two tie-breaks give the same `Φ` exactly when they give the same relation terms.**
The distinction half cancels, by `sum_distinctionsAt_phi`, so the whole difference between
two admissible readings of `[IIT4, Eq 45]` sits in `∑ φ_r` and the self-relations. -/
theorem PhiOfAt_sub_PhiOfAt (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (σ τ : SelectorAt T S u s) :
    PhiOfAt T S u s σ - PhiOfAt T S u s τ
      = ((∑ d ∈ relationSetsOf (distinctionsAt T S u s σ), relPhiOrZero d)
          + ∑ d ∈ selfRelationsOf (distinctionsAt T S u s σ), selfRelPhi d)
        - ((∑ d ∈ relationSetsOf (distinctionsAt T S u s τ), relPhiOrZero d)
          + ∑ d ∈ selfRelationsOf (distinctionsAt T S u s τ), selfRelPhi d) := by
  rw [PhiOfAt, PhiOfAt, PhiOfStructure, PhiOfStructure,
    sum_distinctionsAt_phi T S u s σ, sum_distinctionsAt_phi T S u s τ]
  ring

/-! ## `Φ` of the complex -- the join

`IIT/System.lean` finds complexes among arbitrary `S ⊆ U` but evaluates `Φ` with
substrate-wide repertoires; `IIT/Phi.lean` is exact only at `S = U`.  Neither can state
`Φ` *of the complex*, which is what `[IIT4]` computes.  With the mechanism level
conditioned and the relation layer factored, it can be stated -- all three sums of
`[IIT4, Eq 59]`, at the substrate `[IIT4, Eq 26]` selects, with that substrate's own
background held fixed. -/

/-- **`Φ` of a complex** `[IIT4, Eqs 26, 58, 59]`: the quantity `[IIT4]` computes.
`IsComplex` picks the substrate, `SelectorAt` resolves the ties inside it, and `PhiOfAt`
evaluates all three sums of `[IIT4, Eq 59]` there, with that substrate's own background
held fixed. -/
noncomputable def PhiOfComplexAt (T : UnitTPM N) (u : State N) (U S : Finset (Fin N))
    (s : State N) (σ : SelectorAt T S u s) (_h : IsComplex T u U S s) : ℝ :=
  PhiOfAt T S u s σ

theorem PhiOfComplexAt_nonneg (T : UnitTPM N) (u : State N) (U S : Finset (Fin N))
    (s : State N) (σ : SelectorAt T S u s) (h : IsComplex T u U S s) :
    0 ≤ PhiOfComplexAt T u U S s σ h :=
  PhiOfAt_nonneg T S u s σ

/-- **`Φ` of the whole substrate as a complex is `IIT/System.lean`'s `Φ`.**  So the
differential numbers, which are computed at `S = U`, certify this `Φ`. -/
theorem PhiOfComplexAt_univ (T : UnitTPM N) (u s : State N)
    (σ : SelectorAt T Finset.univ u s) (h : IsComplex T u Finset.univ Finset.univ s)
    (hu : 0 < ∑ v : State N, fullProb T v u) :
    PhiOfComplexAt T u Finset.univ Finset.univ s σ h
      = PhiOfComplex T Finset.univ u s (σ.toSelector hu) h :=
  PhiOfAt_univ T u s σ hu

/-- **`[UB, Eqs 6, 16]` for `Φ` of a complex**, the same bound `PhiOf_le` proves for the
whole substrate, transported across the join. -/
theorem PhiOfComplexAt_le (T : UnitTPM N) (u s : State N)
    (σ : SelectorAt T Finset.univ u s) (h : IsComplex T u Finset.univ Finset.univ s)
    (hN : 1 ≤ N) (hu : 0 < ∑ v : State N, fullProb T v u) :
    PhiOfComplexAt T u Finset.univ Finset.univ s σ h
      ≤ (N : ℝ) ^ 2 / 2 * 2 ^ N
        + ((N : ℝ) ^ 2 / 2 * 2 ^ N
            + (N : ℝ) ^ 2 * 2 ^ N
              * (2 ^ (2 ^ N - 1) / ((2 : ℝ) ^ N - 1) * (1 - 1 / 2 ^ (2 ^ N - 1)) - 1)) := by
  rw [PhiOfComplexAt_univ T u s σ h hu, PhiOfComplex]
  exact PhiOf_le T u s (σ.toSelector hu) hN

end IIT
