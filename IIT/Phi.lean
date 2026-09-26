/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import Mathlib

/-!
# Integrated Information Theory (IIT) 4.0: the definition of `Φ`, and upper bounds

Autoformalization of

* L. Albantakis, L. Barbosa, G. Findlay, M. Grasso, A. M. Haun, W. Marshall,
  W. G. P. Mayner, A. Zaeemzadeh, et al.,
  *Integrated information theory (IIT) 4.0: Formulating the properties of phenomenal
  existence in physical terms*, PLoS Comput Biol **19**(10): e1011465 (2023).

* A. Zaeemzadeh, G. Tononi, *Upper bounds for integrated information*,
  PLoS Comput Biol **20**(8): e1012323 (2024).

Below `[IIT4]` refers to the first paper and `[UB]` to the second.

## Design

Following `[UB, §2.1]` a candidate system has `N` **binary** units.  The
conditional-independence assumption `[IIT4, Eq 2]` is built into `UnitTPM`: a system
is given by its *unit* transition probabilities and the system TPM is their product.
This is the standing assumption of `[UB, §2.1]` ("the system is realizable by a TPM
that is a product of unit TPMs").

**Causal marginalization** `[IIT4, Eq 28]`, `[UB, Eq 4]` is averaging the unit TPM
uniformly over the states agreeing with `m` on the mechanism `M`; the effect
repertoire of a purview is the product over its units `[UB, Eq 5]`.

**Scope: the candidate system is the whole of `Fin N`.**  `[IIT4]` distinguishes two
transition probability functions, `T_e` `[IIT4, Eq 3]` and `T_c` `[IIT4, Eq 4]`, obtained
from a universe `U` by conditioning on the background `W = U \ S`: for effects the
background is *held at its current state*, for causes it is marginalized against the
conditional distribution over its prior states.  Here `UnitTPM` plays the role of that
already-background-conditioned TPM and `Fin N` is the candidate system `S` itself, so
`W = ∅` and `T_e = T_c = T`.  This is exactly the setting of `[UB, §2.1]`, which takes "a
stochastic system `S` consisting of `N` random variables" and marginalizes `W = S - M`
uniformly `[UB, Eq 4]` — precisely `effUnit`.  Consequently the `S` argument threaded
through `phiEmech`, `phiCmech`, `phiD` and `sumPhiD` is the *purview range* of
`[IIT4, Eq 45]` ("over all `Z ⊆ S`"), and these agree with the paper's quantities when
`S = Finset.univ`; `sumPhiD_le` is stated there.  Handling a proper subsystem `S ⊊ U`
needs `[IIT4, Eqs 3, 4]` and is part of the missing system level below.

**Partitions.**  A disintegrating partition of a mechanism-purview pair severs some of
the `|M| * |Z|` causal connections between them.  All the bounds of `[UB]` use about a
partition is *which connections survive*, so a partition is recorded by the assignment
sending each purview unit `k` to the part of `M` still constraining it
(`Partition.part`).  The count `N(θ)` of `[UB, Lemma 2]` is `cutCount`.

## A trap worth recording: `Θ(M, Z)` must exclude the no-cut partition

An earlier version of this file defined a partition as nothing but an assignment
`part : Fin N → Finset (Fin N)` with `part k ⊆ M`.  That admits `part = fun _ => M`, which
severs nothing.  For it `partEffRep = effRep` definitionally, so `φ = effRep * |log 1|₊ = 0`
and `cutCount = 0`; and since Lean evaluates `0 / 0` to `0`, that assignment became a
*global minimiser* of `normalizedPhi`.  Every MIP therefore had `φ = 0`, and `phiEat`,
`phiEmech`, `phiCmech`, `phiD` and `sumPhiD` were all **identically zero** — while still
typechecking and still satisfying every bound proved below.

The fix is not a hack but the second half of `[IIT4, Eq 38]`: a disintegrating partition
must satisfy `M⁽ⁱ⁾ = M ⟹ Z⁽ⁱ⁾ = ∅`, i.e. no purview unit retains the whole mechanism.
That is `Partition.effPart_ne`, and `cutCount_pos` is its payoff.
`phiEat_copyTPM` closes the
loop by exhibiting a system — one deterministic COPY unit — with `φ = 1`, so the
definitions are now provably non-trivial.

## Cross-checks against PyPhi

**Numerical differential tests** were run against PyPhi's `feature/iit-4.0` branch
(dev build `1.2.1.dev1470+gb78d0e342`), not merely source reading:

* one deterministic COPY unit: `repertoire = 1.0`, `partitioned = 0.5`, `φ = 1.0` on both
  sides, matching `phiEat_copyTPM` and `Partition.total`;
* the two-unit AND/OR system in state `(1,1)`, mechanism and purview `{A,B}`: an
  independent brute-force evaluation of *these* definitions reproduces
  `find_mip(EFFECT).phi = 1.4150374992788437` and, after the partition-structure fix
  below, `find_mip(CAUSE).phi = 0.41503749927884376`.

**The block structure of `Partition` was forced by that cause-side test.**  An earlier
version indexed a partition by purview unit alone (`part : Fin N → Finset (Fin N)` with
`part k ⊆ M` and `part k ≠ M`).  That is adequate for the effect direction but *wrong* for
the cause direction: `π_c(m | z) = ∏_{i ∈ M} π_c(mᵢ | z)` is a product over **mechanism**
units, so the cause direction needs each mechanism unit's retained *purview* part.  The
old side condition, transposed, forbade a mechanism unit from retaining the whole purview
— yet PyPhi's cause MIP for the AND/OR system is exactly the partition with blocks
`({A}, {A,B})`, `({B}, ∅)`, which does precisely that, and which `[IIT4, Eq 38]` permits
because no *block* carries the whole mechanism.  Enumerating
`pyphi.partition.mip_partitions`
for `|M| = |Z| = 2` gives nine effect keep-maps and nine cause keep-maps; the block
encoding here induces exactly those, in both directions, from a single partition.

**Source-level confirmations.**

The repertoire layer was checked against the reference implementation on the
`feature/iit-4.0` branch of PyPhi (the mainline implements IIT 3.0 and was ignored).  It
confirms: uniform marginalization of the units outside the mechanism
(`ExplicitTPM.marginalize_out` divides by the raw state count); the effect repertoire as a
product over *purview* units (`_effect_repertoire`); the cause repertoire as a product over
*mechanism* units with the roles exchanged (`forward_cause_probability` carries the comment
"mechanism and purview roles are switched"), which is `causeFwd = effRep` with swapped
arguments; and Bayes normalization by `a / a.sum()` for `π_c(z | m)`.  It also confirms
that a single TPM is correct exactly for the whole-system case: PyPhi conditions
`effect_tpm` on the background and builds `cause_tpm` by a separate backward construction,
which are guaranteed to coincide only when the subsystem is the whole network.  (A proper
subsystem may still coincide in a particular state -- AND/OR restricted to `{A}` in state
`(1,1)` does -- but generally does not: the same restriction in state `(0,1)` gives
`cause = [0, .5, .5, 1]` against `effect = [0, 1, 1, 1]`.)

## What is and is not defined from the transition probabilities

`φ_d` **is** a genuine function of `T` (`phiD`).  Unwinding the definitions, it is built
from `UnitTPM.prob` alone, by causal marginalization, products, `logb`, and finitely many
maxima and minima:

  `effUnit → effRep → phiEofPartition → phiEat → phiEpurview → phiEmech`
  `        ↘ causeFwd → causeRep → phiCofPartition → phiCat → phiCpurview → phiCmech`
  `                                                        phiD = min(φ_c, φ_e)`

and `sumPhiD = ∑_{M ⊆ S} φ_d`, which `sumPhiD_le` bounds by `[UB, Eq 6]`.

**`Φ` itself is not yet a function of `T`.**  `Distinction.phi` is a structure *field*, so
`Phi` sums numbers supplied from outside.  `CauseEffectStructure.SpecifiedBy` and
`Phi_eq_of_specifiedBy` tie those numbers to `phiD`, and `sum_phiD_le_sumPhiD` shows the
distinction part is bounded by `sumPhiD`.  Two ingredients are still missing before `Φ`
can be *defined* outright:

1. the **system level** (`[IIT4, Eqs 3–26]`): `T_e`/`T_c` after background marginalization,
   system `ii`, `φ_s`, and the recursive identification of complexes.  The congruence
   filter in `[IIT4, Eq 48]` refers to the system cause-effect state `s'`, which lives here;
2. a **tie-breaking choice** of the maximally irreducible purviews `z*_c`, `z*_e`.  Per
   `[IIT4, S1 Text]` these may genuinely tie, and the tie is broken by maximizing `Φ` — a
   cascade that can also halt outright ("does not qualify as a complex").  The *values*
   `φ_e(m)`, `φ_c(m)`, `φ_d(m)` are unaffected, which is why they are definable here; the
   *witnesses* needed for relations are not canonical.

## Status

Proved:

* `effUnit_le_of_subset`            — `[UB, Lemma 1]`
* `effRep_le_cutCount_smul`         — `[UB, Lemma 2]`, multiplicative form
* `logb_ratio_le_cutCount`          — `[UB, Lemma 2]`, logarithmic form
* `effUnit_eq_one_of_subset`        — `[UB, Lemma 3]`
* `theorem_one`, `theorem_one'`     — `[UB, Theorem 1]`, effect side
* `theorem_one_cause`, `theorem_one_cause'` — `[UB, Theorem 1]`, cause side
* `selectivity_eq_one_of_phiE_eq`   — `[UB, Lemma 4]`
* `sum_phi_le`                      — `[UB, Eq 6]`
* `sum_phi_le_sq`                   — `[UB, Eq 7]`
* `phiD_le`                         — `[UB, Theorem 1]` for the actual `φ_d`
* `sumPhiD_le`                      — `[UB, Eq 6]` for the actual `∑ φ_d`
* `causeRep_le_one`                 — the cause-side Bayes selectivity is a probability
* `relPhi_le_phi`                   — the bound `φ_r(d) ≤ min_d φ_d` of `[UB, §2.2]`
* `Phi_nonneg`, `Phi_le`, `Phi_eq_of_specifiedBy`, `sum_phiD_le_sumPhiD`
* `cutCount_le`, `cutCount_total`, `card_agree`, …

* `theorem_two`, `theorem_two_partition` — `[UB, Theorem 2]` (inter-order constraints)
* `corollary_one_boundI`                   — `[UB, Corollary 1]`
* `uncEffUnit_ge_of_effUnit_eq_one`  — the `2^(-|M|)` unconstrained bound of `[UB, S3]`
* `attains_max_iff`, `informativeness_split_lt` — the two halves of `[UB, S3, Lemma 7]`

* `theorem_three`, `one_lt_effUnit_singleton_mul`, `prob_eq_one_on_other_fibre`
  — `[UB, Theorem 3]` (intra-order constraints), by leaked determinism through
  neighbouring size-`K` mechanisms rather than `[UB, S3 §3]`'s binomial estimates.

## A remark on `[UB]`

`[UB, Eq 7]` reads `∑ φ ≤ (N(N+1)/4) 2^N`, and the paper also writes this as
`N(N+1) 2^(N-2)`.  Over the naturals with truncated subtraction the second form
gives `2` at `N = 1` and the left side `1`: `1 · 2 · 2^(1-2) = 1 · 2 · 2^0 = 2`.
The identities are therefore formalized here as
`4 * ∑_{t ⊆ s} |t|² = |s|(|s|+1) 2^{|s|}` (`four_mul_sum_sq_card_powerset`) and
`2 * ∑_{t ⊆ s} |t| = |s| 2^{|s|}` (`two_mul_sum_card_powerset`), which are correct for
every `N`, and the real-valued bounds are stated in the paper's `/2` and `/4` form.
-/

namespace IIT

open Finset

variable {N : ℕ}

/-! ## The positive-part operator `|·|₊` -/

/-- The positive-part operator written `|·|₊` in `[IIT4, Eq 19]` and `[UB, Eq 2]`. -/
noncomputable def pos (x : ℝ) : ℝ := max 0 x

lemma pos_nonneg (x : ℝ) : 0 ≤ pos x := le_max_left _ _

lemma pos_mono {x y : ℝ} (h : x ≤ y) : pos x ≤ pos y := max_le_max le_rfl h

/-- **The positive part commutes with a minimum.**  `|·|₊` is monotone, so clamping each
term and then minimizing gives the same number as minimizing and then clamping.

This is what settles the relation between `[IIT4, Eqs 19, 20]`, which write `|·|₊` into
the per-partition `φ`, and PyPhi, whose `pointwise_mutual_information_vector` is the
unclamped `log₂(p/q)` and which minimizes the signed quantity: the two agree on the
*value* of `φ_s`.  What they need not agree on is *which* partition attains it, since
clamping makes every partition of negative `φ` tie at `0`. -/
lemma pos_inf' {ι : Type*} (t : Finset ι) (ht : t.Nonempty) (f : ι → ℝ) :
    t.inf' ht (fun i => pos (f i)) = pos (t.inf' ht f) := by
  refine le_antisymm ?_ (Finset.le_inf' _ _ fun i hi => pos_mono (Finset.inf'_le _ hi))
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' ht f
  exact (Finset.inf'_le _ hj).trans (le_of_eq (by rw [hjeq]))

lemma le_pos (x : ℝ) : x ≤ pos x := le_max_right _ _

lemma pos_le {x c : ℝ} (hc : 0 ≤ c) (h : x ≤ c) : pos x ≤ c := max_le hc h

/-! ## Substrates -/

/-- A state of an `N`-unit substrate of binary units. -/
abbrev State (N : ℕ) := Fin N → Bool

/-- A candidate system `[UB, Table 1]`, given by its unit transition probabilities.
The system TPM is their product, which is conditional independence
`[IIT4, Eq 2]`. -/
structure UnitTPM (N : ℕ) where
  /-- `prob i s b` is the probability that unit `i` is in state `b` at `t+1`
  given the system is in state `s` at `t`. -/
  prob : Fin N → State N → Bool → ℝ
  nonneg : ∀ i s b, 0 ≤ prob i s b
  normalized : ∀ i s, prob i s false + prob i s true = 1

namespace UnitTPM

lemma le_one (T : UnitTPM N) (i : Fin N) (s : State N) (b : Bool) : T.prob i s b ≤ 1 := by
  cases b
  · have h1 := T.normalized i s
    have h2 := T.nonneg i s true
    linarith
  · have h1 := T.normalized i s
    have h2 := T.nonneg i s false
    linarith

end UnitTPM

/-! ## Causal marginalization -/

/-- The states over which background units are causally marginalized: those agreeing
with `m` on the mechanism `M`.  Marginalization is uniform over this set
`[IIT4, Eq 28]`, `[UB, Eq 4]`. -/
def agree (M : Finset (Fin N)) (m : State N) : Finset (State N) :=
  Finset.univ.filter (fun s => ∀ j ∈ M, s j = m j)

lemma mem_agree {M : Finset (Fin N)} {m s : State N} :
    s ∈ agree M m ↔ ∀ j ∈ M, s j = m j := by
  simp [agree]

lemma self_mem_agree (M : Finset (Fin N)) (m : State N) : m ∈ agree M m := by
  simp [mem_agree]

lemma agree_nonempty (M : Finset (Fin N)) (m : State N) : (agree M m).Nonempty :=
  ⟨m, self_mem_agree M m⟩

/-- **`[UB, S3 Appendix, Lemma 5]`**: `M̄ ⊂ M ⊆ S` implies `𝓜(m) ⊂ 𝓜(m̄)` -- a larger
mechanism pins more units, so its marginalization fibre is smaller. -/
lemma agree_subset_agree {M M' : Finset (Fin N)} (h : M' ⊆ M) (m : State N) :
    agree M m ⊆ agree M' m := by
  intro s hs
  rw [mem_agree] at hs ⊢
  exact fun j hj => hs j (h hj)

/-- The marginalization fibre is a product of `Bool`s over the units outside `M`. -/
noncomputable def agreeEquiv (M : Finset (Fin N)) (m : State N) :
    {s : State N // ∀ j ∈ M, s j = m j} ≃ (↥(Mᶜ) → Bool) where
  toFun s := fun j => s.1 j
  invFun g := ⟨fun j => if h : j ∈ M then m j else g ⟨j, Finset.mem_compl.mpr h⟩, by
    intro j hj; simp [hj]⟩
  left_inv := by
    rintro ⟨s, hs⟩
    ext j
    by_cases h : j ∈ M
    · simp [h, hs j h]
    · simp [h]
  right_inv := by
    intro g
    ext j
    have hj : (j : Fin N) ∉ M := Finset.mem_compl.mp j.2
    simp [hj]

lemma card_agree (M : Finset (Fin N)) (m : State N) :
    (agree M m).card = 2 ^ (N - M.card) := by
  have h1 : (agree M m).card = Fintype.card {s : State N // ∀ j ∈ M, s j = m j} := by
    rw [Fintype.card_subtype]
    rfl
  rw [h1, Fintype.card_congr (agreeEquiv M m), Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe, Finset.card_compl, Fintype.card_fin]

lemma card_agree_pos (M : Finset (Fin N)) (m : State N) : 0 < (agree M m).card :=
  Finset.card_pos.2 (agree_nonempty M m)

lemma card_state (N : ℕ) : (Finset.univ : Finset (State N)).card = 2 ^ N := by
  simp [Finset.card_univ]


/-! ## Effect repertoires -/

/-- The effect repertoire of a single purview unit `[UB, Eq 4]`: the unit TPM averaged
uniformly over the causally marginalized background. -/
noncomputable def effUnit (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (i : Fin N) (b : Bool) : ℝ :=
  (∑ s ∈ agree M m, T.prob i s b) / (agree M m).card

/-- `effUnit` in the literal shape of `[UB, Eq 4]`, with the `2 ^ |W|` normalization
explicit (`|W| = N - |M|`). -/
lemma effUnit_eq (T : UnitTPM N) (M : Finset (Fin N)) (m : State N) (i : Fin N)
    (b : Bool) :
    effUnit T M m i b = ((2 : ℝ) ^ (N - M.card))⁻¹ * ∑ s ∈ agree M m, T.prob i s b := by
  rw [effUnit, card_agree, div_eq_inv_mul]
  norm_cast

lemma effUnit_nonneg (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (i : Fin N) (b : Bool) : 0 ≤ effUnit T M m i b :=
  div_nonneg (Finset.sum_nonneg fun s _ => T.nonneg i s b) (Nat.cast_nonneg _)

/-- The effect repertoire of a unit is a probability distribution on `Bool`. -/
lemma effUnit_add (T : UnitTPM N) (M : Finset (Fin N)) (m : State N) (i : Fin N) :
    effUnit T M m i false + effUnit T M m i true = 1 := by
  have hc : ((agree M m).card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (card_agree_pos M m).ne'
  rw [effUnit, effUnit, ← add_div, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun s _ => T.normalized i s)]
  simp [hc]

lemma effUnit_le_one (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (i : Fin N) (b : Bool) : effUnit T M m i b ≤ 1 := by
  have h := effUnit_add T M m i
  cases b
  · have := effUnit_nonneg T M m i true; linarith
  · have := effUnit_nonneg T M m i false; linarith

/-- The effect repertoire over a purview `[UB, Eq 5]`: the product over purview units.
Product probabilities are what discount correlations from units outside the mechanism
`[IIT4, Eq 29]`. -/
noncomputable def effRep (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) : ℝ :=
  ∏ k ∈ Z, effUnit T M m k (z k)

lemma effRep_nonneg (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) : 0 ≤ effRep T M m Z z :=
  Finset.prod_nonneg fun k _ => effUnit_nonneg T M m k (z k)

/-- The **selectivity** term of `[UB, §2.1]` is at most `1`. -/
lemma effRep_le_one (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) : effRep T M m Z z ≤ 1 :=
  Finset.prod_le_one (fun k _ => effUnit_nonneg T M m k (z k))
    (fun k _ => effUnit_le_one T M m k (z k))

/-- The unconstrained effect probability `π_e(z; M)` `[IIT4, Eq 31]`, `[UB, §2.1]`:
the effect repertoire averaged over all states of the mechanism. -/
noncomputable def uncEffRep (T : UnitTPM N) (M : Finset (Fin N))
    (Z : Finset (Fin N)) (z : State N) : ℝ :=
  (∑ m ∈ (Finset.univ : Finset (State N)), effRep T M m Z z) /
    (Finset.univ : Finset (State N)).card

/-- The maximal effect state `[UB, Eq 1]`, `[IIT4, Eq 36]`: the purview state
maximising intrinsic effect information. -/
def IsMaximalEffectState (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) : Prop :=
  ∀ w : State N,
    effRep T M m Z w * Real.logb 2 (effRep T M m Z w / uncEffRep T M Z w) ≤
      effRep T M m Z z * Real.logb 2 (effRep T M m Z z / uncEffRep T M Z z)

/-! ## Partitions -/

/-- A **disintegrating partition** of a mechanism-purview pair `(M, Z)` `[IIT4, Eq 38]`:
a finite family of blocks `(M⁽ⁱ⁾, Z⁽ⁱ⁾)` whose mechanism parts partition `M`, whose
purview parts partition `Z`, and in which a block carrying the whole mechanism must have
an empty purview part — the side condition that makes the partition disintegrating.

**One partition serves both causal directions**, as in the paper and in PyPhi
(`PARTITION_TYPE = 'ALL'`, the `KPartition` scheme): on the effect side each purview unit
is constrained by the mechanism part of its block (`effPart`), on the cause side each
mechanism unit is constrained by the purview part of its block (`causePart`).

This block encoding was fixed against `pyphi.partition.mip_partitions` by enumeration:
for `|M| = |Z| = 2` it induces exactly PyPhi's nine effect keep-maps and nine cause
keep-maps.  An earlier per-purview-unit encoding got the effect side right but wrongly
excluded the cause keep-maps in which one mechanism unit retains the *whole* purview
(blocks `({A}, Z), ({B}, ∅)`) — and PyPhi selects exactly such a partition as the cause
MIP of the AND/OR system, with `φ_c = 0.41503…`, reproduced by the differential test. -/
structure Partition (N : ℕ) (M Z : Finset (Fin N)) where
  /-- The blocks `(M⁽ⁱ⁾, Z⁽ⁱ⁾)`. -/
  blocks : Finset (Finset (Fin N) × Finset (Fin N))
  mech_subset : ∀ b ∈ blocks, b.1 ⊆ M
  purv_subset : ∀ b ∈ blocks, b.2 ⊆ Z
  mech_disjoint : ∀ b ∈ blocks, ∀ b' ∈ blocks, b ≠ b' → Disjoint b.1 b'.1
  purv_disjoint : ∀ b ∈ blocks, ∀ b' ∈ blocks, b ≠ b' → Disjoint b.2 b'.2
  mech_cover : ∀ i ∈ M, ∃ b ∈ blocks, i ∈ b.1
  purv_cover : ∀ k ∈ Z, ∃ b ∈ blocks, k ∈ b.2
  /-- `[IIT4, Eq 38]`: `M⁽ⁱ⁾ = M ⟹ Z⁽ⁱ⁾ = ∅`. -/
  proper : ∀ b ∈ blocks, b.1 = M → b.2 = ∅

namespace Partition

variable {M Z : Finset (Fin N)} (θ : Partition N M Z)

/-- The mechanism part still constraining a given purview unit (effect direction). -/
def effPart (k : Fin N) : Finset (Fin N) :=
  (θ.blocks.filter fun b => k ∈ b.2).sup Prod.fst

/-- The purview part still constraining a given mechanism unit (cause direction). -/
def causePart (k : Fin N) : Finset (Fin N) :=
  (θ.blocks.filter fun b => k ∈ b.1).sup Prod.snd

lemma effPart_eq {b : Finset (Fin N) × Finset (Fin N)} (hb : b ∈ θ.blocks)
    {k : Fin N} (hk : k ∈ b.2) : θ.effPart k = b.1 := by
  have hfil : θ.blocks.filter (fun b' => k ∈ b'.2) = {b} := by
    ext b'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hb', hk'⟩
      by_contra hne
      exact absurd hk (Finset.disjoint_left.1 (θ.purv_disjoint b' hb' b hb hne) hk')
    · rintro rfl
      exact ⟨hb, hk⟩
  rw [effPart, hfil, Finset.sup_singleton]

lemma causePart_eq {b : Finset (Fin N) × Finset (Fin N)} (hb : b ∈ θ.blocks)
    {k : Fin N} (hk : k ∈ b.1) : θ.causePart k = b.2 := by
  have hfil : θ.blocks.filter (fun b' => k ∈ b'.1) = {b} := by
    ext b'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hb', hk'⟩
      by_contra hne
      exact absurd hk (Finset.disjoint_left.1 (θ.mech_disjoint b' hb' b hb hne) hk')
    · rintro rfl
      exact ⟨hb, hk⟩
  rw [causePart, hfil, Finset.sup_singleton]

lemma effPart_subset (k : Fin N) : θ.effPart k ⊆ M := by
  rw [effPart]
  exact Finset.sup_le fun b hb => θ.mech_subset b (Finset.mem_filter.1 hb).1

lemma causePart_subset (k : Fin N) : θ.causePart k ⊆ Z := by
  rw [causePart]
  exact Finset.sup_le fun b hb => θ.purv_subset b (Finset.mem_filter.1 hb).1

/-- A purview unit never retains the whole mechanism: the `[IIT4, Eq 38]` side condition
seen from the effect side, and what forbids the no-cut assignment.  Note there is **no**
mirror statement for `causePart`: a mechanism unit may retain the whole purview, and
PyPhi's cause MIPs use exactly that freedom. -/
lemma effPart_ne {k : Fin N} (hk : k ∈ Z) : θ.effPart k ≠ M := by
  obtain ⟨b, hb, hkb⟩ := θ.purv_cover k hk
  rw [θ.effPart_eq hb hkb]
  intro hbM
  have h2 := θ.proper b hb hbM
  rw [h2] at hkb
  exact absurd hkb (Finset.notMem_empty k)

lemma purv_pairwiseDisjoint :
    (↑θ.blocks : Set (Finset (Fin N) × Finset (Fin N))).PairwiseDisjoint Prod.snd :=
  fun b hb b' hb' hne => θ.purv_disjoint b hb b' hb' hne

lemma mech_pairwiseDisjoint :
    (↑θ.blocks : Set (Finset (Fin N) × Finset (Fin N))).PairwiseDisjoint Prod.fst :=
  fun b hb b' hb' hne => θ.mech_disjoint b hb b' hb' hne

lemma purv_biUnion : θ.blocks.biUnion Prod.snd = Z := by
  ext k
  simp only [Finset.mem_biUnion]
  exact ⟨fun ⟨b, hb, hk⟩ => θ.purv_subset b hb hk, fun hk => θ.purv_cover k hk⟩

lemma mech_biUnion : θ.blocks.biUnion Prod.fst = M := by
  ext i
  simp only [Finset.mem_biUnion]
  exact ⟨fun ⟨b, hb, hi⟩ => θ.mech_subset b hb hi, fun hi => θ.mech_cover i hi⟩

lemma sum_effPart_card :
    ∑ k ∈ Z, (θ.effPart k).card = ∑ b ∈ θ.blocks, b.1.card * b.2.card := by
  classical
  have h1 : ∑ k ∈ Z, (θ.effPart k).card
      = ∑ k ∈ θ.blocks.biUnion Prod.snd, (θ.effPart k).card :=
    Finset.sum_congr θ.purv_biUnion.symm fun _ _ => rfl
  rw [h1, Finset.sum_biUnion θ.purv_pairwiseDisjoint]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.sum_congr rfl fun k hk => by rw [θ.effPart_eq hb hk],
    Finset.sum_const, smul_eq_mul, mul_comm]

lemma sum_causePart_card :
    ∑ k ∈ M, (θ.causePart k).card = ∑ b ∈ θ.blocks, b.1.card * b.2.card := by
  classical
  have h1 : ∑ k ∈ M, (θ.causePart k).card
      = ∑ k ∈ θ.blocks.biUnion Prod.fst, (θ.causePart k).card :=
    Finset.sum_congr θ.mech_biUnion.symm fun _ _ => rfl
  rw [h1, Finset.sum_biUnion θ.mech_pairwiseDisjoint]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.sum_congr rfl fun k hk => by rw [θ.causePart_eq hb hk],
    Finset.sum_const, smul_eq_mul]

lemma sum_effPart_add :
    (∑ k ∈ Z, (M.card - (θ.effPart k).card)) + (∑ b ∈ θ.blocks, b.1.card * b.2.card)
      = M.card * Z.card := by
  rw [← θ.sum_effPart_card, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl fun k _ =>
      Nat.sub_add_cancel (Finset.card_le_card (θ.effPart_subset k)),
    Finset.sum_const, smul_eq_mul, mul_comm]

lemma sum_causePart_add :
    (∑ k ∈ M, (Z.card - (θ.causePart k).card)) + (∑ b ∈ θ.blocks, b.1.card * b.2.card)
      = M.card * Z.card := by
  rw [← θ.sum_causePart_card, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl fun k _ =>
      Nat.sub_add_cancel (Finset.card_le_card (θ.causePart_subset k)),
    Finset.sum_const, smul_eq_mul]

end Partition

/-- The totally disintegrating partition: the whole mechanism in one block with an empty
purview part, the whole purview in another with an empty mechanism part.  Every
connection is severed.  It exists as soon as the mechanism is nonempty; for `M = ∅` there
is no disintegrating partition of a nonempty purview at all, matching `[IIT4, Eq 38]`. -/
def Partition.total {M : Finset (Fin N)} (hM : M.Nonempty) (Z : Finset (Fin N)) :
    Partition N M Z where
  blocks := {(M, ∅), (∅, Z)}
  mech_subset := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact subset_rfl
    · exact Finset.empty_subset M
  purv_subset := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact Finset.empty_subset Z
    · exact subset_rfl
  mech_disjoint := by
    intro b hb b' hb' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb hb'
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · exact Finset.disjoint_empty_right M
    · exact Finset.disjoint_empty_left M
    · exact absurd rfl hne
  purv_disjoint := by
    intro b hb b' hb' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb hb'
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · exact Finset.disjoint_empty_left Z
    · exact Finset.disjoint_empty_right Z
    · exact absurd rfl hne
  mech_cover := fun i hi => ⟨(M, ∅), Finset.mem_insert_self _ _, hi⟩
  purv_cover := fun k hk =>
    ⟨(∅, Z), Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hk⟩
  proper := by
    intro b hb h1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · rfl
    · exact absurd h1.symm hM.ne_empty

lemma Partition.total_effPart {M : Finset (Fin N)} (hM : M.Nonempty) (Z : Finset (Fin N))
    {k : Fin N} (hk : k ∈ Z) : (Partition.total hM Z).effPart k = ∅ :=
  (Partition.total hM Z).effPart_eq
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hk

/-- The partitioned effect repertoire `[IIT4, Eq 39]`: each purview unit constrained by
the mechanism part of its block.

When a block leaves a purview unit with an empty mechanism part, its factor
`effUnit T ∅ m k (z k)` is the fully unconstrained probability of `[IIT4, Eq 40]`
(`agree ∅ m = univ`), and an empty purview part contributes the empty product `1`, which
is `[IIT4, Eq 39]`'s convention `π(∅ | m⁽ⁱ⁾) = 1`. -/
noncomputable def partEffRep (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) (θ : Partition N M Z) : ℝ :=
  ∏ k ∈ Z, effUnit T (θ.effPart k) m k (z k)

lemma partEffRep_nonneg (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) (θ : Partition N M Z) :
    0 ≤ partEffRep T M m Z z θ :=
  Finset.prod_nonneg fun k _ => effUnit_nonneg T _ m k (z k)

/-- `N(θ)` of `[UB, Lemma 2]`: the number of causal connections severed by `θ`, counted
from the effect side. -/
def cutCount (M Z : Finset (Fin N)) (θ : Partition N M Z) : ℕ :=
  ∑ k ∈ Z, (M.card - (θ.effPart k).card)

/-- The severed-connection count is direction-independent: counted per mechanism unit it
is the same number.  Both equal the paper's `|M||Z| - ∑ᵢ |M⁽ⁱ⁾||Z⁽ⁱ⁾|`. -/
lemma cutCount_eq_causeSum {M Z : Finset (Fin N)} (θ : Partition N M Z) :
    cutCount M Z θ = ∑ k ∈ M, (Z.card - (θ.causePart k).card) := by
  have h1 := θ.sum_effPart_add
  have h2 := θ.sum_causePart_add
  rw [cutCount]
  omega

/-- The paper's form of `N(θ)` `[UB, Lemma 2]`, `[IIT4, Eq 43]`. -/
lemma cutCount_eq_blocks {M Z : Finset (Fin N)} (θ : Partition N M Z) :
    cutCount M Z θ = M.card * Z.card - ∑ b ∈ θ.blocks, b.1.card * b.2.card := by
  have h1 := θ.sum_effPart_add
  rw [cutCount]
  omega

/-- A partition severs at most all `|M| * |Z|` connections. -/
lemma cutCount_le (M Z : Finset (Fin N)) (θ : Partition N M Z) :
    cutCount M Z θ ≤ M.card * Z.card := by
  have h : ∑ k ∈ Z, (M.card - (θ.effPart k).card) ≤ ∑ _k ∈ Z, M.card :=
    Finset.sum_le_sum fun k _ => Nat.sub_le _ _
  simpa [cutCount, Finset.sum_const, smul_eq_mul, mul_comm] using h

/-- **A disintegrating partition really does cut something.**  This is what `proper`
buys, and it is precisely what stops `normalizedPhi` from reducing to `0 / 0`. -/
lemma cutCount_pos {M Z : Finset (Fin N)} (hZ : Z.Nonempty) (θ : Partition N M Z) :
    0 < cutCount M Z θ := by
  obtain ⟨k, hk⟩ := hZ
  have hss : θ.effPart k ⊂ M := (θ.effPart_subset k).ssubset_of_ne (θ.effPart_ne hk)
  have hlt : (θ.effPart k).card < M.card := Finset.card_lt_card hss
  rw [cutCount]
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨k, hk, ?_⟩
  omega

/-- The totally disintegrating partition severs exactly `|M| * |Z|` connections: this
is the sense in which, `[UB, §2.1.1]`, "to disintegrate a maximal integrated mechanism
we need to severe all causal connections between the mechanism and the purview". -/
lemma cutCount_total {M : Finset (Fin N)} (hM : M.Nonempty) (Z : Finset (Fin N)) :
    cutCount M Z (Partition.total hM Z) = M.card * Z.card := by
  rw [cutCount, Finset.sum_congr rfl fun k hk => by
    rw [Partition.total_effPart hM Z hk, Finset.card_empty, Nat.sub_zero]]
  rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-! ## `[UB, Lemma 1]`, `[UB, Lemma 2]`, `[UB, Lemma 3]` -/

/-- **`[UB, Lemma 1]`.**  Causal marginalization limits informativeness: passing from a
sub-mechanism `M' ⊆ M` **up** to `M` raises the effect probability of a unit by a factor
of at most `2 ^ (|M| - |M'|)`, whose exponent is the number of connections cut from that
unit.  (In the other direction, `M` down to `M'`, no such bound holds: marginalizing away
a mechanism unit can raise the probability from `0` to anything.)

Proof: the marginalization fibre of `M'` contains that of `M`, so the numerator only
grows, while the normalizing constant grows by exactly `2 ^ (|M| - |M'|)`. -/
theorem effUnit_le_of_subset (T : UnitTPM N) {M M' : Finset (Fin N)} (h : M' ⊆ M)
    (m : State N) (i : Fin N) (b : Bool) :
    effUnit T M m i b ≤ 2 ^ (M.card - M'.card) * effUnit T M' m i b := by
  have hMN : M.card ≤ N := by simpa using Finset.card_le_univ M
  have hM'M : M'.card ≤ M.card := Finset.card_le_card h
  have hsum : (∑ s ∈ agree M m, T.prob i s b) ≤ ∑ s ∈ agree M' m, T.prob i s b :=
    Finset.sum_le_sum_of_subset_of_nonneg (agree_subset_agree h m)
      fun s _ _ => T.nonneg i s b
  have hexp : (M.card - M'.card) + (N - M.card) = N - M'.card := by omega
  have h2p : ((2 : ℝ) ^ (M.card - M'.card)) ≠ 0 := by positivity
  have key : (2 : ℝ) ^ (M.card - M'.card) * ((2 : ℝ) ^ (N - M'.card))⁻¹
      = ((2 : ℝ) ^ (N - M.card))⁻¹ := by
    rw [← hexp, pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ h2p, one_mul]
  rw [effUnit_eq, effUnit_eq, ← mul_assoc, key]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- **`[UB, Lemma 2]`**, multiplicative form: the effect repertoire exceeds its
partitioned version by at most `2 ^ N(θ)`.

This follows from `[UB, Lemma 1]` by multiplicativity across purview units: the
per-unit exponents `|M| - |part k|` add up to exactly `cutCount`. -/
theorem effRep_le_cutCount_smul (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) (θ : Partition N M Z) :
    effRep T M m Z z ≤ 2 ^ (cutCount M Z θ) * partEffRep T M m Z z θ := by
  calc effRep T M m Z z
      = ∏ k ∈ Z, effUnit T M m k (z k) := rfl
    _ ≤ ∏ k ∈ Z, ((2 : ℝ) ^ (M.card - (θ.effPart k).card)
          * effUnit T (θ.effPart k) m k (z k)) :=
        Finset.prod_le_prod (fun k _ => effUnit_nonneg T M m k (z k))
          (fun k _ => effUnit_le_of_subset T (θ.effPart_subset k) m k (z k))
    _ = (∏ k ∈ Z, (2 : ℝ) ^ (M.card - (θ.effPart k).card)) *
          ∏ k ∈ Z, effUnit T (θ.effPart k) m k (z k) := Finset.prod_mul_distrib
    _ = 2 ^ (cutCount M Z θ) * partEffRep T M m Z z θ := by
        rw [cutCount, partEffRep, Finset.prod_pow_eq_pow_sum]

/-- If a partition kills the repertoire, so was the unpartitioned repertoire zero: the
boundary case of `[UB, Lemma 2]`. -/
lemma effRep_eq_zero_of_partEffRep_eq_zero (T : UnitTPM N) (M : Finset (Fin N))
    (m : State N) (Z : Finset (Fin N)) (z : State N) (θ : Partition N M Z)
    (h : partEffRep T M m Z z θ = 0) : effRep T M m Z z = 0 := by
  have h1 := effRep_le_cutCount_smul T M m Z z θ
  rw [h, mul_zero] at h1
  exact le_antisymm h1 (effRep_nonneg T M m Z z)

/-- **`[UB, Lemma 2]`**, logarithmic form as stated in the paper: informativeness is
bounded by the number of connections the partition severs. -/
theorem logb_ratio_le_cutCount (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) (θ : Partition N M Z)
    (hpos : 0 < partEffRep T M m Z z θ) :
    pos (Real.logb 2 (effRep T M m Z z / partEffRep T M m Z z θ))
      ≤ cutCount M Z θ := by
  refine pos_le (Nat.cast_nonneg _) ?_
  have hpow : ((2 : ℝ) ^ (cutCount M Z θ)) = (2 : ℝ) ^ ((cutCount M Z θ : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
  rcases eq_or_lt_of_le (effRep_nonneg T M m Z z) with h0 | h0
  · rw [← h0, zero_div, Real.logb_zero]
    exact Nat.cast_nonneg _
  · have hratio : 0 < effRep T M m Z z / partEffRep T M m Z z θ := div_pos h0 hpos
    have hle : effRep T M m Z z / partEffRep T M m Z z θ ≤ 2 ^ (cutCount M Z θ) :=
      (div_le_iff₀ hpos).2 (effRep_le_cutCount_smul T M m Z z θ)
    calc Real.logb 2 (effRep T M m Z z / partEffRep T M m Z z θ)
        ≤ Real.logb 2 ((2 : ℝ) ^ (cutCount M Z θ)) :=
          Real.logb_le_logb_of_le (by norm_num) hratio hle
      _ = cutCount M Z θ := by
          rw [hpow, Real.logb_rpow (by norm_num) (by norm_num)]

/-- **`[UB, S3, Lemma 6]`** (deterministic mechanism).  If a unit's effect repertoire is
`1`, the underlying transition probability is `1` at *every* state of the marginalization
fibre — an average of numbers in `[0,1]` equals `1` only if every term does. -/
theorem prob_eq_one_of_effUnit_eq_one (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (i : Fin N) (b : Bool) (hdet : effUnit T M m i b = 1) :
    ∀ s ∈ agree M m, T.prob i s b = 1 := by
  have hc : ((agree M m).card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (card_agree_pos M m).ne'
  have hsum : (∑ s ∈ agree M m, T.prob i s b) = (agree M m).card := by
    rw [effUnit, div_eq_one_iff_eq hc] at hdet
    exact hdet
  by_contra hcon
  push Not at hcon
  obtain ⟨s0, hs0mem, hs0⟩ := hcon
  have hlt : (∑ s ∈ agree M m, T.prob i s b) < ∑ _s ∈ agree M m, (1 : ℝ) :=
    Finset.sum_lt_sum (fun s _ => T.le_one i s b)
      ⟨s0, hs0mem, lt_of_le_of_ne (T.le_one i s0 b) hs0⟩
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hlt
  rw [hsum] at hlt
  exact lt_irrefl _ hlt

/-- **`[UB, S3, Lemma 6]`**, the `= 0` half: an average of nonnegative numbers vanishes
only if every term does.  `[UB]`'s own proof of Lemma 7 uses only the `= 1` half; this one
is what the `= 0` half of `[UB, Lemma 3]` (`effUnit_eq_zero_of_subset`) needs. -/
theorem prob_eq_zero_of_effUnit_eq_zero (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (i : Fin N) (b : Bool) (hdet : effUnit T M m i b = 0) :
    ∀ s ∈ agree M m, T.prob i s b = 0 := by
  have hc : ((agree M m).card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (card_agree_pos M m).ne'
  have hsum : (∑ s ∈ agree M m, T.prob i s b) = 0 := by
    rw [effUnit, div_eq_zero_iff] at hdet
    rcases hdet with h | h
    · exact h
    · exact absurd h hc
  exact fun s hs =>
    (Finset.sum_eq_zero_iff_of_nonneg fun s _ => T.nonneg i s b).1 hsum s hs

/-- **The unconstrained lower bound** — the ingredient `[UB, Theorem 2]` turns on.

If a mechanism `M` fully specifies a unit's state, then that state's *unconstrained*
probability is at least `2 ^ (-|M|)`.  The reason is a counting one: `agree M m` has
`2 ^ (N - |M|)` states, the transition probability is `1` at each of them by Lemma 6, and
the unconstrained probability averages over all `2 ^ N` states.

`[UB, S3]` writes this as `π_e(Zᵢ = z*ᵢ) ≥ |M(m)| / |Ω_S| = 2^{N-|M|} / 2^N`. -/
theorem uncEffUnit_ge_of_effUnit_eq_one (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (i : Fin N) (b : Bool) (hdet : effUnit T M m i b = 1) :
    ((2 : ℝ) ^ M.card)⁻¹ ≤ effUnit T ∅ m i b := by
  classical
  have hMN : M.card ≤ N := by simpa using Finset.card_le_univ M
  have hall := prob_eq_one_of_effUnit_eq_one T M m i b hdet
  have hempty : agree (∅ : Finset (Fin N)) m = Finset.univ := by
    ext s; simp [mem_agree]
  -- the fibre of `M` contributes its full cardinality to the total sum
  have hlow : ((agree M m).card : ℝ) ≤ ∑ s : State N, T.prob i s b := by
    have h1 : ∑ s ∈ agree M m, T.prob i s b = ((agree M m).card : ℝ) := by
      rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, mul_one]
    calc ((agree M m).card : ℝ) = ∑ s ∈ agree M m, T.prob i s b := h1.symm
      _ ≤ ∑ s : State N, T.prob i s b :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun s _ _ => T.nonneg i s b
  rw [effUnit, hempty, card_state]
  rw [card_agree] at hlow
  have h2N : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  rw [le_div_iff₀ (by exact_mod_cast h2N)]
  have hpow : ((2 : ℝ) ^ (N - M.card)) * ((2 : ℝ) ^ M.card) = (2 : ℝ) ^ N := by
    rw [← pow_add]
    congr 1
    omega
  have hMpos : (0 : ℝ) < (2 : ℝ) ^ M.card := by positivity
  have hstep : ((2 : ℝ) ^ M.card)⁻¹ * ((2 : ℝ) ^ N) = (2 : ℝ) ^ (N - M.card) := by
    field_simp
    linarith [hpow]
  rw [show (((2 : ℝ) ^ N : ℝ)) = ((2 ^ N : ℕ) : ℝ) by push_cast; ring] at hstep
  calc ((2 : ℝ) ^ M.card)⁻¹ * (((2 ^ N : ℕ)) : ℝ) = (2 : ℝ) ^ (N - M.card) := hstep
    _ ≤ ∑ s : State N, T.prob i s b := by
        have : (((2 ^ (N - M.card) : ℕ)) : ℝ) ≤ ∑ s : State N, T.prob i s b := hlow
        push_cast at this
        exact this

/-- **`[UB, Lemma 3]`**: a superset of a deterministic mechanism is deterministic.

Proof: `effUnit T M m i b` is an average of terms in `[0,1]` over a fibre containing
that of `M'`; if the average is `1` every term is `1`, hence so is the sub-average. -/
theorem effUnit_eq_one_of_subset (T : UnitTPM N) {M M' : Finset (Fin N)} (h : M ⊆ M')
    (m : State N) (i : Fin N) (b : Bool) (hdet : effUnit T M m i b = 1) :
    effUnit T M' m i b = 1 := by
  have hc : ((agree M m).card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (card_agree_pos M m).ne'
  have hsum : (∑ s ∈ agree M m, T.prob i s b) = (agree M m).card := by
    rw [effUnit, div_eq_one_iff_eq hc] at hdet
    exact hdet
  have hall : ∀ s ∈ agree M m, T.prob i s b = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s0, hs0mem, hs0⟩ := hcon
    have hlt : (∑ s ∈ agree M m, T.prob i s b) < ∑ _s ∈ agree M m, (1 : ℝ) :=
      Finset.sum_lt_sum (fun s _ => T.le_one i s b)
        ⟨s0, hs0mem, lt_of_le_of_ne (T.le_one i s0 b) hs0⟩
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hlt
    rw [hsum] at hlt
    exact lt_irrefl _ hlt
  have hsub : agree M' m ⊆ agree M m := agree_subset_agree h m
  have hc' : ((agree M' m).card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (card_agree_pos M' m).ne'
  rw [effUnit, Finset.sum_congr rfl (fun s hs => hall s (hsub hs))]
  simp [hc']

/-- **`[UB, Lemma 3]`, second half.**  `[UB]` states Lemma 3 for both deterministic values:
"if `π_e(Z_i = z_i | m) = 0` then `π_e(Z_i = z_i | m̄) = 0`".  A sub-mechanism averages
over a larger fibre, on all of which the unit already fails to fire. -/
theorem effUnit_eq_zero_of_subset (T : UnitTPM N) {M M' : Finset (Fin N)} (h : M ⊆ M')
    (m : State N) (i : Fin N) (b : Bool) (hdet : effUnit T M m i b = 0) :
    effUnit T M' m i b = 0 := by
  have hall := prob_eq_zero_of_effUnit_eq_zero T M m i b hdet
  have hsub : agree M' m ⊆ agree M m := agree_subset_agree h m
  rw [effUnit, Finset.sum_congr rfl (fun s hs => hall s (hsub hs))]
  simp

/-! ## Integrated effect information, `[UB, Theorem 1]` and `[UB, Lemma 4]` -/

/-- Integrated effect information of a mechanism-purview pair relative to a partition
`[UB, Eq 2]`, `[IIT4, Eq 41]`: selectivity times informativeness. -/
noncomputable def phiEofPartition (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) (θ : Partition N M Z) : ℝ :=
  effRep T M m Z z * pos (Real.logb 2 (effRep T M m Z z / partEffRep T M m Z z θ))

lemma phiEofPartition_nonneg (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) (θ : Partition N M Z) :
    0 ≤ phiEofPartition T M m Z z θ :=
  mul_nonneg (effRep_nonneg T M m Z z) (pos_nonneg _)

/-- The normalised quantity minimised by the minimum information partition
`[IIT4, Eq 43]`, `[UB, Eq 3]`. -/
noncomputable def normalizedPhi (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) (θ : Partition N M Z) : ℝ :=
  phiEofPartition T M m Z z θ / (cutCount M Z θ : ℝ)

/-- **Lean's `x / 0 = 0` cannot create an extra minimum.**  A partition with no severed
connection would divide by zero and so appear optimal; `cutCount_pos` rules that out
whenever the purview is nonempty, and when it is empty `phiEofPartition` is `0` for every
partition, so no partition is favoured.  This is the convention `[IIT4, Eq 38]`'s `proper`
condition exists to make safe. -/
lemma normalizedPhi_wellDefined (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) (θ : Partition N M Z) (hZ : Z.Nonempty) :
    normalizedPhi T M m Z z θ * (cutCount M Z θ : ℝ) = phiEofPartition T M m Z z θ := by
  have h : (0 : ℝ) < (cutCount M Z θ : ℝ) := by exact_mod_cast cutCount_pos hZ θ
  rw [normalizedPhi, div_mul_cancel₀ _ h.ne']

/-- **A partition enters the effect side only through `effPart`.**  Both the partitioned
repertoire `[IIT4, Eq 39]` and the normalizer `[IIT4, Eq 43]` are built from
`θ.effPart k` for `k ∈ Z` and from nothing else, so two partitions agreeing there are
indistinguishable to `normalizedPhi`.  This is what makes the minimum tractable: the
search is not over partitions but over the assignments `k ↦ effPart k`, of which
`effPart_ne` leaves few. -/
theorem partEffRep_congr_effPart {M Z : Finset (Fin N)} {θ ϑ : Partition N M Z}
    (h : ∀ k ∈ Z, θ.effPart k = ϑ.effPart k) (T : UnitTPM N) (m z : State N) :
    partEffRep T M m Z z θ = partEffRep T M m Z z ϑ :=
  Finset.prod_congr rfl fun k hk => by rw [h k hk]

theorem cutCount_congr_effPart {M Z : Finset (Fin N)} {θ ϑ : Partition N M Z}
    (h : ∀ k ∈ Z, θ.effPart k = ϑ.effPart k) : cutCount M Z θ = cutCount M Z ϑ :=
  Finset.sum_congr rfl fun k hk => by rw [h k hk]

theorem normalizedPhi_congr_effPart {M Z : Finset (Fin N)} {θ ϑ : Partition N M Z}
    (h : ∀ k ∈ Z, θ.effPart k = ϑ.effPart k) (T : UnitTPM N) (m z : State N) :
    normalizedPhi T M m Z z θ = normalizedPhi T M m Z z ϑ := by
  rw [normalizedPhi, normalizedPhi, phiEofPartition, phiEofPartition,
    partEffRep_congr_effPart h T m z, cutCount_congr_effPart h]

/-- **Comparing normalized integrated information is comparing integer powers.**

`[IIT4, Eq 43]` selects the partition minimizing `φ / cutCount`, and `φ` is a logarithm, so
the comparison is between `log₂ x / c₁` and `log₂ y / c₂`.  Since `log₂` is monotone and
`c₁, c₂` are positive, that is exactly `x ^ c₂ ≤ y ^ c₁` -- an inequality between rationals
whenever the transition probabilities are rational, decided with no logarithm evaluated
and no tolerance.  This is the reduction `test/exact.py` uses to decide the whole system
level exactly; here it is what lets a minimum information partition be *proved* minimal
rather than reported by a floating-point search. -/
theorem logb_div_le_logb_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) {c₁ c₂ : ℕ}
    (h1 : 0 < c₁) (h2 : 0 < c₂) :
    Real.logb 2 x / c₁ ≤ Real.logb 2 y / c₂ ↔ x ^ c₂ ≤ y ^ c₁ := by
  have hc1 : (0 : ℝ) < c₁ := by exact_mod_cast h1
  have hc2 : (0 : ℝ) < c₂ := by exact_mod_cast h2
  rw [div_le_div_iff₀ hc1 hc2]
  rw [show Real.logb 2 x * c₂ = Real.logb 2 (x ^ c₂) by
        rw [Real.logb_pow]; ring,
      show Real.logb 2 y * c₁ = Real.logb 2 (y ^ c₁) by
        rw [Real.logb_pow]; ring]
  exact Real.logb_le_logb (by norm_num) (by positivity) (by positivity)

/-- `θ` is a minimum information partition (MIP) for `(M, Z)` `[UB, Eq 3]`. -/
def IsMIP (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) (θ : Partition N M Z) : Prop :=
  ∀ ϑ : Partition N M Z, normalizedPhi T M m Z z θ ≤ normalizedPhi T M m Z z ϑ

/-- **`[UB, Theorem 1]`** (effect side).  Integrated effect information is bounded by
the total number of causal connections between mechanism and purview:
`φ_e(m, E) ≤ |M| * |E|`.

The bound is uniform in the partition, so it holds in particular at the minimum
information partition, i.e. for `φ_e(m, E)` itself (`phiEat_le`). -/
theorem theorem_one (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (E : Finset (Fin N)) (z : State N) (θ : Partition N M E)
    (hpos : 0 < partEffRep T M m E z θ) :
    phiEofPartition T M m E z θ ≤ M.card * E.card := by
  have hsel : effRep T M m E z ≤ 1 := effRep_le_one T M m E z
  have hinf : pos (Real.logb 2 (effRep T M m E z / partEffRep T M m E z θ))
      ≤ (cutCount M E θ : ℝ) := logb_ratio_le_cutCount T M m E z θ hpos
  have hcut : (cutCount M E θ : ℝ) ≤ (M.card : ℝ) * E.card := by
    exact_mod_cast cutCount_le M E θ
  calc phiEofPartition T M m E z θ
      = effRep T M m E z
          * pos (Real.logb 2 (effRep T M m E z / partEffRep T M m E z θ)) := rfl
    _ ≤ 1 * ((M.card : ℝ) * E.card) :=
        mul_le_mul hsel (hinf.trans hcut) (pos_nonneg _) zero_le_one
    _ = (M.card : ℝ) * E.card := one_mul _

/-- `[UB, Theorem 1]` at the minimum information partition. -/
theorem theorem_one_mip (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (E : Finset (Fin N)) (z : State N) (θ : Partition N M E)
    (_hmip : IsMIP T M m E z θ) (hpos : 0 < partEffRep T M m E z θ) :
    phiEofPartition T M m E z θ ≤ M.card * E.card :=
  theorem_one T M m E z θ hpos

/-- **`[UB, Lemma 4]`**.  The bound of Theorem 1 is attained only when selectivity is
`1`, i.e. when the mechanism fully specifies its purview. -/
theorem selectivity_eq_one_of_phiE_eq (T : UnitTPM N) (M : Finset (Fin N))
    (m : State N) (E : Finset (Fin N)) (z : State N) (θ : Partition N M E)
    (hpos : 0 < partEffRep T M m E z θ)
    (hMcard : 0 < M.card) (hEcard : 0 < E.card)
    (heq : phiEofPartition T M m E z θ = M.card * E.card) :
    effRep T M m E z = 1 := by
  by_contra hne
  have hsel : effRep T M m E z < 1 := lt_of_le_of_ne (effRep_le_one T M m E z) hne
  have hsel0 : 0 ≤ effRep T M m E z := effRep_nonneg T M m E z
  have hinf : pos (Real.logb 2 (effRep T M m E z / partEffRep T M m E z θ))
      ≤ (cutCount M E θ : ℝ) := logb_ratio_le_cutCount T M m E z θ hpos
  have hcut : (cutCount M E θ : ℝ) ≤ (M.card : ℝ) * E.card := by
    exact_mod_cast cutCount_le M E θ
  have hMpos : (0 : ℝ) < (M.card : ℝ) := by exact_mod_cast hMcard
  have hEpos : (0 : ℝ) < (E.card : ℝ) := by exact_mod_cast hEcard
  have hprodpos : (0 : ℝ) < (M.card : ℝ) * E.card := mul_pos hMpos hEpos
  have hlt : phiEofPartition T M m E z θ < (M.card : ℝ) * E.card := by
    calc phiEofPartition T M m E z θ
        ≤ effRep T M m E z * ((M.card : ℝ) * E.card) :=
          mul_le_mul_of_nonneg_left (hinf.trans hcut) hsel0
      _ < 1 * ((M.card : ℝ) * E.card) := mul_lt_mul_of_pos_right hsel hprodpos
      _ = (M.card : ℝ) * E.card := one_mul _
  rw [heq] at hlt
  exact lt_irrefl _ hlt

/-! ## The cause side

`[IIT4, Eqs 30, 32, 33, 35, 44]`.  The cause repertoire is *structurally the effect
repertoire with mechanism and purview exchanged*: `p_c(m_i | z)` marginalizes the units
outside the **purview** and reads off a **mechanism** unit, whereas `p_e(z_i | m)`
marginalizes outside the mechanism and reads off a purview unit.  So `causeFwd` is
literally `effRep` with its arguments swapped, and every bound proved above transfers.

The one genuine asymmetry `[IIT4, §Intrinsic difference]` is the **selectivity** term: on
the effect side it is the forward probability `π_e(z|m)`, on the cause side the backward
probability `π_c^-(z|m)` obtained by Bayes' rule with a uniform prior over `Ω_Z`. -/

/-- The repertoire depends on the conditioning state only through its restriction to the
conditioning set. -/
lemma agree_eq_of_mem {A : Finset (Fin N)} {a b : State N} (h : b ∈ agree A a) :
    agree A b = agree A a := by
  rw [mem_agree] at h
  ext s
  simp only [mem_agree]
  exact ⟨fun hs j hj => (hs j hj).trans (h j hj),
    fun hs j hj => (hs j hj).trans (h j hj).symm⟩

lemma effUnit_congr (T : UnitTPM N) {A : Finset (Fin N)} {a b : State N}
    (h : b ∈ agree A a) (i : Fin N) (c : Bool) :
    effUnit T A b i c = effUnit T A a i c := by
  rw [effUnit, effUnit, agree_eq_of_mem h]

lemma effRep_congr (T : UnitTPM N) {A : Finset (Fin N)} {a b : State N}
    (h : b ∈ agree A a) (B : Finset (Fin N)) (c : State N) :
    effRep T A b B c = effRep T A a B c :=
  Finset.prod_congr rfl fun k _ => effUnit_congr T h k (c k)

/-- Averaging a function of the system state uniformly over all `2^N` states.  Since the
repertoires depend on the state only through its restriction to a fixed subset, this
equals the paper's `|Ω_A|⁻¹ ∑_{a ∈ Ω_A}` `[IIT4, Eqs 31, 32]`. -/
noncomputable def avgOverStates (f : State N → ℝ) : ℝ :=
  (∑ s : State N, f s) / (2 : ℝ) ^ N

/-- The **cause repertoire** `π_c(m | z)` `[IIT4, Eq 30]`. -/
noncomputable def causeFwd (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) : ℝ :=
  effRep T Z z M m

lemma causeFwd_eq (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) :
    causeFwd T Z z M m = ∏ k ∈ M, effUnit T Z z k (m k) := rfl

lemma causeFwd_nonneg (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) : 0 ≤ causeFwd T Z z M m :=
  effRep_nonneg T Z z M m

lemma causeFwd_le_one (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) : causeFwd T Z z M m ≤ 1 :=
  effRep_le_one T Z z M m

/-- The unconstrained cause probability `π_c(m; Z)` `[IIT4, Eq 32]`. -/
noncomputable def uncCauseFwd (T : UnitTPM N) (Z M : Finset (Fin N)) (m : State N) : ℝ :=
  avgOverStates fun z => causeFwd T Z z M m

/-- The backward (Bayes) cause probability `π_c^-(z | m)` `[IIT4, Eq 33]`,
`[UB, S1 Appendix]`: the
*selectivity* term on the cause side, with a uniform prior over `Ω_Z`. -/
noncomputable def causeRep (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) : ℝ :=
  causeFwd T Z z M m / ((2 : ℝ) ^ Z.card * uncCauseFwd T Z M m)

/-- The unconstrained cause probability is nonnegative. -/
lemma uncCauseFwd_nonneg (T : UnitTPM N) (Z M : Finset (Fin N)) (m : State N) :
    0 ≤ uncCauseFwd T Z M m := by
  rw [uncCauseFwd, avgOverStates]
  exact div_nonneg (Finset.sum_nonneg fun s _ => causeFwd_nonneg T Z s M m) (by positivity)

/-- `2^{|Z|} π_c(m; Z) = ∑_{ẑ ∈ Ω_Z} π_c(m | ẑ)`, the normalizing sum of `[IIT4, Eq 33]`,
bounded below by the single term at `z`.  This is what makes the Bayes selectivity a
probability. -/
lemma causeFwd_le_normalizer (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) :
    causeFwd T Z z M m ≤ (2 : ℝ) ^ Z.card * uncCauseFwd T Z M m := by
  have hZN : Z.card ≤ N := by simpa using Finset.card_le_univ Z
  have hcongr : ∀ s ∈ agree Z z, causeFwd T Z s M m = causeFwd T Z z M m :=
    fun s hs => effRep_congr T hs M m
  have hfib : ∑ s ∈ agree Z z, causeFwd T Z s M m
      = ((2 : ℝ) ^ (N - Z.card)) * causeFwd T Z z M m := by
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul, card_agree]
    norm_cast
  have hsub : ∑ s ∈ agree Z z, causeFwd T Z s M m ≤ ∑ s : State N, causeFwd T Z s M m :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun s _ _ => causeFwd_nonneg T Z s M m
  rw [hfib] at hsub
  have hposA : (0 : ℝ) < (2 : ℝ) ^ (N - Z.card) := by positivity
  have hposB : ((2 : ℝ) ^ Z.card) ≠ 0 := by positivity
  have hpow : ((2 : ℝ) ^ (N - Z.card)) * ((2 : ℝ) ^ Z.card) = (2 : ℝ) ^ N := by
    rw [← pow_add]
    congr 1
    omega
  have key : (2 : ℝ) ^ Z.card * ((∑ s : State N, causeFwd T Z s M m) / (2 : ℝ) ^ N)
      = (∑ s : State N, causeFwd T Z s M m) / (2 : ℝ) ^ (N - Z.card) := by
    rw [← hpow]
    field_simp
  rw [uncCauseFwd, avgOverStates, key, le_div_iff₀ hposA, mul_comm]
  exact hsub

lemma causeRep_nonneg (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) : 0 ≤ causeRep T Z z M m :=
  div_nonneg (causeFwd_nonneg T Z z M m)
    (mul_nonneg (by positivity) (uncCauseFwd_nonneg T Z M m))

/-- The cause-side selectivity is a probability. -/
lemma causeRep_le_one (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) : causeRep T Z z M m ≤ 1 := by
  have hnn : 0 ≤ (2 : ℝ) ^ Z.card * uncCauseFwd T Z M m :=
    mul_nonneg (by positivity) (uncCauseFwd_nonneg T Z M m)
  rcases eq_or_lt_of_le hnn with h | h
  · rw [causeRep, ← h, div_zero]
    norm_num
  · exact (div_le_one h).2 (causeFwd_le_normalizer T Z z M m)

/-- Intrinsic effect information `ii_e(m, z)` `[IIT4, Eq 34]`. -/
noncomputable def iiE (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) : ℝ :=
  effRep T M m Z z * Real.logb 2 (effRep T M m Z z / uncEffRep T M Z z)

/-- Intrinsic cause information `ii_c(m, z)` `[IIT4, Eq 35]`.  Note the asymmetry: the
selectivity is the *backward* probability, the informativeness the *forward* one. -/
noncomputable def iiC (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) : ℝ :=
  causeRep T Z z M m * Real.logb 2 (causeFwd T Z z M m / uncCauseFwd T Z M m)

/-- The partitioned cause repertoire `[IIT4, Eq 39, cause analogue]`: each **mechanism**
unit is constrained by the purview part of its block.  The very same block partition
`θ : Partition N M Z` serves both causal directions. -/
noncomputable def partCauseFwd (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) (θ : Partition N M Z) : ℝ :=
  ∏ k ∈ M, effUnit T (θ.causePart k) z k (m k)

lemma partCauseFwd_nonneg (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) (θ : Partition N M Z) :
    0 ≤ partCauseFwd T Z z M m θ :=
  Finset.prod_nonneg fun k _ => effUnit_nonneg T _ z k (m k)

/-- **`[UB, Lemma 2]`, cause side**, multiplicative form: the same per-unit Lemma 1,
multiplied over mechanism units; the exponents sum to the same `N(θ)` by
`cutCount_eq_causeSum`. -/
theorem causeFwd_le_cutCount_smul (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) (θ : Partition N M Z) :
    causeFwd T Z z M m ≤ 2 ^ (cutCount M Z θ) * partCauseFwd T Z z M m θ := by
  rw [cutCount_eq_causeSum]
  calc causeFwd T Z z M m
      = ∏ k ∈ M, effUnit T Z z k (m k) := rfl
    _ ≤ ∏ k ∈ M, ((2 : ℝ) ^ (Z.card - (θ.causePart k).card)
          * effUnit T (θ.causePart k) z k (m k)) :=
        Finset.prod_le_prod (fun k _ => effUnit_nonneg T Z z k (m k))
          (fun k _ => effUnit_le_of_subset T (θ.causePart_subset k) z k (m k))
    _ = (∏ k ∈ M, (2 : ℝ) ^ (Z.card - (θ.causePart k).card)) *
          ∏ k ∈ M, effUnit T (θ.causePart k) z k (m k) := Finset.prod_mul_distrib
    _ = 2 ^ (∑ k ∈ M, (Z.card - (θ.causePart k).card)) * partCauseFwd T Z z M m θ := by
        rw [partCauseFwd, Finset.prod_pow_eq_pow_sum]

/-- The boundary case: a vanishing partitioned cause repertoire forces the
unpartitioned one to vanish. -/
lemma causeFwd_eq_zero_of_partCauseFwd_eq_zero (T : UnitTPM N) (Z : Finset (Fin N))
    (z : State N) (M : Finset (Fin N)) (m : State N) (θ : Partition N M Z)
    (h : partCauseFwd T Z z M m θ = 0) : causeFwd T Z z M m = 0 := by
  have h1 := causeFwd_le_cutCount_smul T Z z M m θ
  rw [h, mul_zero] at h1
  exact le_antisymm h1 (causeFwd_nonneg T Z z M m)

/-- **`[UB, Lemma 2]`, cause side**, logarithmic form. -/
theorem logb_ratio_le_cutCount_cause (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) (θ : Partition N M Z)
    (hpos : 0 < partCauseFwd T Z z M m θ) :
    pos (Real.logb 2 (causeFwd T Z z M m / partCauseFwd T Z z M m θ))
      ≤ cutCount M Z θ := by
  refine pos_le (Nat.cast_nonneg _) ?_
  have hpow : ((2 : ℝ) ^ (cutCount M Z θ)) = (2 : ℝ) ^ ((cutCount M Z θ : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
  rcases eq_or_lt_of_le (causeFwd_nonneg T Z z M m) with h0 | h0
  · rw [← h0, zero_div, Real.logb_zero]
    exact Nat.cast_nonneg _
  · have hratio : 0 < causeFwd T Z z M m / partCauseFwd T Z z M m θ := div_pos h0 hpos
    have hle : causeFwd T Z z M m / partCauseFwd T Z z M m θ ≤ 2 ^ (cutCount M Z θ) :=
      (div_le_iff₀ hpos).2 (causeFwd_le_cutCount_smul T Z z M m θ)
    calc Real.logb 2 (causeFwd T Z z M m / partCauseFwd T Z z M m θ)
        ≤ Real.logb 2 ((2 : ℝ) ^ (cutCount M Z θ)) :=
          Real.logb_le_logb_of_le (by norm_num) hratio hle
      _ = cutCount M Z θ := by
          rw [hpow, Real.logb_rpow (by norm_num) (by norm_num)]

/-- Integrated **cause** information relative to a partition `[IIT4, Eq 44]`,
`[UB, S1 Appendix, Eq 17]`: the Bayes selectivity times the informativeness of the raw
forward term against its partitioned version.  Differential-tested against PyPhi:
`selectivity · |log₂(fwd / partitioned)|₊` reproduces `find_mip(CAUSE, …).phi` exactly on
the AND/OR system (`0.41503749927884376`). -/
noncomputable def phiCofPartition (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) (θ : Partition N M Z) : ℝ :=
  causeRep T Z z M m *
    pos (Real.logb 2 (causeFwd T Z z M m / partCauseFwd T Z z M m θ))

lemma phiCofPartition_nonneg (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) (θ : Partition N M Z) :
    0 ≤ phiCofPartition T Z z M m θ :=
  mul_nonneg (causeRep_nonneg T Z z M m) (pos_nonneg _)

/-- **`[UB, Theorem 1]`, cause side**: `φ_c(m, C) ≤ |M| |C|`. -/
theorem theorem_one_cause (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (C : Finset (Fin N)) (z : State N) (θ : Partition N M C)
    (hpos : 0 < partCauseFwd T C z M m θ) :
    phiCofPartition T C z M m θ ≤ M.card * C.card := by
  have hsel : causeRep T C z M m ≤ 1 := causeRep_le_one T C z M m
  have hinf : pos (Real.logb 2 (causeFwd T C z M m / partCauseFwd T C z M m θ))
      ≤ (cutCount M C θ : ℝ) := logb_ratio_le_cutCount_cause T C z M m θ hpos
  have hcut : (cutCount M C θ : ℝ) ≤ (M.card : ℝ) * C.card := by
    exact_mod_cast cutCount_le M C θ
  calc phiCofPartition T C z M m θ
      = causeRep T C z M m
          * pos (Real.logb 2 (causeFwd T C z M m / partCauseFwd T C z M m θ)) := rfl
    _ ≤ 1 * ((M.card : ℝ) * C.card) :=
        mul_le_mul hsel (hinf.trans hcut) (pos_nonneg _) zero_le_one
    _ = (M.card : ℝ) * C.card := one_mul _

/-! ## Selection: from `φ` at a partition to `φ_d(m)`

`[IIT4, Eqs 36, 42, 45, 46, 47]`.  Each step of the chain is a maximum or minimum over a
*finite* set, so the resulting **values** are well defined with no arbitrary choice.  This
matters: `[IIT4, S1 Text]` ("Resolving ties") explains that the *witnesses* — which state
`z*` or which purview is selected — may genuinely tie, and are then broken by a cascade
that ends at the level of `Φ` itself, and can even halt (the system "does not qualify as a
complex").  But it also directs that `φ(m, Z)` be compared across all purviews
"**including all possible ties in `ii(m, z)` within a candidate purview**".  Taking the
maximum over the whole tie set, as below, is exactly that prescription, and it makes
`φ_e(m)`, `φ_c(m)` and `φ_d(m)` honest functions of the transition probabilities. -/

section Argmax

open scoped Classical

/-- The set of maximisers of `f`, keeping **all** ties `[IIT4, S1 Text]`. -/
noncomputable def argmaxSet {α : Type*} [Fintype α] (f : α → ℝ) : Finset α :=
  Finset.univ.filter fun a => ∀ b, f b ≤ f a

/-- The set of minimisers of `f`, keeping all ties. -/
noncomputable def argminSet {α : Type*} [Fintype α] (f : α → ℝ) : Finset α :=
  Finset.univ.filter fun a => ∀ b, f a ≤ f b

lemma mem_argmaxSet {α : Type*} [Fintype α] {f : α → ℝ} {a : α} :
    a ∈ argmaxSet f ↔ ∀ b, f b ≤ f a := by
  simp [argmaxSet]

lemma mem_argminSet {α : Type*} [Fintype α] {f : α → ℝ} {a : α} :
    a ∈ argminSet f ↔ ∀ b, f a ≤ f b := by
  simp [argminSet]

lemma argmaxSet_nonempty {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    (argmaxSet f).Nonempty := by
  obtain ⟨a, -, ha⟩ :=
    Finset.exists_max_image (Finset.univ : Finset α) f Finset.univ_nonempty
  exact ⟨a, mem_argmaxSet.2 fun b => ha b (Finset.mem_univ b)⟩

lemma argminSet_nonempty {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    (argminSet f).Nonempty := by
  obtain ⟨a, -, ha⟩ :=
    Finset.exists_min_image (Finset.univ : Finset α) f Finset.univ_nonempty
  exact ⟨a, mem_argminSet.2 fun b => ha b (Finset.mem_univ b)⟩

end Argmax

/-- `Finset.sup'` extended by `0` on the empty set.  This is needed because `Θ(M, Z)` is
genuinely empty when `M = ∅` and `Z ≠ ∅` `[IIT4, Eq 38]`: the empty set is not a
mechanism, and it specifies no integrated information. -/
noncomputable def sup'OrZero {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  if h : s.Nonempty then s.sup' h f else 0

lemma sup'OrZero_le {α : Type*} {s : Finset α} {f : α → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ b ∈ s, f b ≤ a) : sup'OrZero s f ≤ a := by
  rw [sup'OrZero]
  split
  · exact Finset.sup'_le _ _ h
  · exact ha

lemma le_sup'OrZero {α : Type*} {s : Finset α} {f : α → ℝ} {b : α} (hb : b ∈ s) :
    f b ≤ sup'OrZero s f := by
  rw [sup'OrZero]
  split
  · exact Finset.le_sup' _ hb
  · rename_i hne
    exact absurd ⟨b, hb⟩ hne

lemma sup'OrZero_congr {α : Type*} {s : Finset α} {f g : α → ℝ} (h : ∀ a, f a = g a) :
    sup'OrZero s f = sup'OrZero s g :=
  congrArg (sup'OrZero s) (funext h)

lemma sup'OrZero_nonneg {α : Type*} {s : Finset α} {f : α → ℝ}
    (h : ∀ b ∈ s, 0 ≤ f b) : 0 ≤ sup'OrZero s f := by
  rw [sup'OrZero]
  split
  · rename_i hne
    obtain ⟨b, hb⟩ := hne
    exact (h b hb).trans (Finset.le_sup' _ hb)
  · exact le_refl 0

lemma sup'OrZero_mono {α : Type*} {s t : Finset α} {f : α → ℝ} (hst : s ⊆ t)
    (hf : ∀ a ∈ t, 0 ≤ f a) : sup'OrZero s f ≤ sup'OrZero t f :=
  sup'OrZero_le (sup'OrZero_nonneg hf) fun b hb => le_sup'OrZero (hst hb)

/-- If every value taken on `s` is also taken on `t`, the supremum over `s` is no larger.
Used where `t` is a set of representatives for `s` under an equivalence on which `f` is
constant. -/
lemma sup'OrZero_le_of_values {α : Type*} {s t : Finset α} {f : α → ℝ}
    (h : ∀ a ∈ s, ∃ b ∈ t, f a = f b) (hf : ∀ a ∈ t, 0 ≤ f a) :
    sup'OrZero s f ≤ sup'OrZero t f :=
  sup'OrZero_le (sup'OrZero_nonneg hf) fun a ha => by
    obtain ⟨b, hb, hab⟩ := h a ha
    rw [hab]
    exact le_sup'OrZero hb

/-- Partitions of a mechanism-purview pair form a finite type. -/
def Partition.equivSubtype (M Z : Finset (Fin N)) :
    Partition N M Z ≃ {b : Finset (Finset (Fin N) × Finset (Fin N)) //
      (∀ p ∈ b, p.1 ⊆ M) ∧ (∀ p ∈ b, p.2 ⊆ Z) ∧
        (∀ p ∈ b, ∀ q ∈ b, p ≠ q → Disjoint p.1 q.1) ∧
        (∀ p ∈ b, ∀ q ∈ b, p ≠ q → Disjoint p.2 q.2) ∧
        (∀ i ∈ M, ∃ p ∈ b, i ∈ p.1) ∧ (∀ k ∈ Z, ∃ p ∈ b, k ∈ p.2) ∧
        (∀ p ∈ b, p.1 = M → p.2 = ∅)} where
  toFun θ := ⟨θ.blocks, θ.mech_subset, θ.purv_subset, θ.mech_disjoint,
    θ.purv_disjoint, θ.mech_cover, θ.purv_cover, θ.proper⟩
  invFun b := ⟨b.1, b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2.1, b.2.2.2.2.2.1,
    b.2.2.2.2.2.2.1, b.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instFintypePartition (M Z : Finset (Fin N)) :
    Fintype (Partition N M Z) :=
  letI := Classical.decPred fun b : Finset (Finset (Fin N) × Finset (Fin N)) =>
    (∀ p ∈ b, p.1 ⊆ M) ∧ (∀ p ∈ b, p.2 ⊆ Z) ∧
      (∀ p ∈ b, ∀ q ∈ b, p ≠ q → Disjoint p.1 q.1) ∧
      (∀ p ∈ b, ∀ q ∈ b, p ≠ q → Disjoint p.2 q.2) ∧
      (∀ i ∈ M, ∃ p ∈ b, i ∈ p.1) ∧ (∀ k ∈ Z, ∃ p ∈ b, k ∈ p.2) ∧
      (∀ p ∈ b, p.1 = M → p.2 = ∅)
  Fintype.ofEquiv _ (Partition.equivSubtype M Z).symm

/-- `Θ(M, Z)` is nonempty exactly when the mechanism is: `[IIT4, Eq 38]` has no
disintegrating partition of a nonempty purview by an empty mechanism. -/
instance instNonemptyPartition {M : Finset (Fin N)} [hM : Fact M.Nonempty]
    (Z : Finset (Fin N)) : Nonempty (Partition N M Z) :=
  ⟨Partition.total hM.out Z⟩

/-- The set of minimum information partitions on the effect side `[IIT4, Eq 43]`,
`[UB, Eq 3]`, all ties kept. -/
noncomputable def mipSetE (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) : Finset (Partition N M Z) :=
  argminSet (normalizedPhi T M m Z z)

/-- `φ_e(m, Z)` `[IIT4, Eq 42]`: integrated effect information at the MIP.

**Formalization decision, not a quotation.**  `[IIT4, Eq 42]` names *the* minimum
information partition `θ'`; when several partitions tie on the normalized ratio but differ
in unnormalized `φ`, neither `[IIT4, Eq 42]` nor `[IIT4, S1 Text]` (which resolves ties in
`ii`, in cause-effect states, in purviews and among overlapping complexes, but not among
MIPs) says which to take.  We take the supremum.  This choice agrees with PyPhi on every
system in `test/`, but it is ours, not the paper's. -/
noncomputable def phiEat (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) : ℝ :=
  sup'OrZero (mipSetE T M m Z z) (phiEofPartition T M m Z z)

/-- Normalized integrated **cause** information, minimised by the cause-side MIP. -/
noncomputable def normalizedPhiC (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) (θ : Partition N M Z) : ℝ :=
  phiCofPartition T Z z M m θ / (cutCount M Z θ : ℝ)

/-- The set of minimum information partitions on the cause side. -/
noncomputable def mipSetC (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) : Finset (Partition N M Z) :=
  argminSet (normalizedPhiC T Z z M m)

/-- `φ_c(m, Z)` `[UB, S1 Appendix, Eq 17]`: integrated cause information at the MIP.
Ties among cause-side MIPs are resolved as in `phiEat`, by the same formalization
decision. -/
noncomputable def phiCat (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) : ℝ :=
  sup'OrZero (mipSetC T Z z M m) (phiCofPartition T Z z M m)

/-- The maximal effect states within a purview `[IIT4, Eq 36]`, all ties kept. -/
noncomputable def maxEffStates (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) : Finset (State N) :=
  argmaxSet (iiE T M m Z)

/-- The maximal cause states within a purview `[UB, S1 Appendix]`, all ties kept. -/
noncomputable def maxCauseStates (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) : Finset (State N) :=
  argmaxSet (iiC T M m Z)

/-- **`[IIT4, Eq 37]`**: the maximal intrinsic effect information of `m` over `Z`,
`ii_e(m, Z) := ii_e(m, z'_e) = max_{z ∈ Ω_Z} ii_e(m, z)`.  Evaluated on the `Eq 36`
argmax, where `iiE` is constant, so this is the maximum value itself. -/
noncomputable def iiEmax (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) : ℝ :=
  sup'OrZero (maxEffStates T M m Z) (iiE T M m Z)

/-- **`[IIT4, Eq 37]`**, cause side. -/
noncomputable def iiCmax (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) : ℝ :=
  sup'OrZero (maxCauseStates T M m Z) (iiC T M m Z)

/-- `iiEmax` really is the maximum of `iiE` over all purview states. -/
lemma le_iiEmax (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) : iiE T M m Z z ≤ iiEmax T M m Z := by
  obtain ⟨w, hw⟩ := argmaxSet_nonempty (iiE T M m Z)
  exact (mem_argmaxSet.1 hw z).trans (le_sup'OrZero hw)

/-- `iiCmax` really is the maximum of `iiC` over all purview states. -/
lemma le_iiCmax (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) : iiC T M m Z z ≤ iiCmax T M m Z := by
  obtain ⟨w, hw⟩ := argmaxSet_nonempty (iiC T M m Z)
  exact (mem_argmaxSet.1 hw z).trans (le_sup'OrZero hw)

/-- `φ_e` of a mechanism over one purview, at its maximal effect state(s). -/
noncomputable def phiEpurview (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) : ℝ :=
  (maxEffStates T M m Z).sup' (argmaxSet_nonempty _) fun z => phiEat T M m Z z

/-- `φ_c` of a mechanism over one purview, at its maximal cause state(s). -/
noncomputable def phiCpurview (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) : ℝ :=
  (maxCauseStates T M m Z).sup' (argmaxSet_nonempty _) fun z => phiCat T Z z M m

/-- **`φ_e(m)`** `[IIT4, Eq 46]`: the integrated effect information of a mechanism within
the system `S`, maximised over all candidate effect purviews `Z ⊆ S` (exclusion). -/
noncomputable def phiEmech (T : UnitTPM N) (S : Finset (Fin N)) (M : Finset (Fin N))
    (m : State N) : ℝ :=
  S.powerset.sup' ⟨∅, Finset.empty_mem_powerset S⟩ fun Z => phiEpurview T M m Z

/-- **`φ_c(m)`** `[UB, S1 Appendix]`: likewise on the cause side. -/
noncomputable def phiCmech (T : UnitTPM N) (S : Finset (Fin N)) (M : Finset (Fin N))
    (m : State N) : ℝ :=
  S.powerset.sup' ⟨∅, Finset.empty_mem_powerset S⟩ fun Z => phiCpurview T M m Z

/-- **`φ_d(m) = min(φ_c(m), φ_e(m))`** `[IIT4, Eq 47]`: the integrated information of the
causal distinction specified by the mechanism `m` within the system `S`.

This is a genuine function of the transition probabilities: unwinding the definitions,
`phiD` is built from `UnitTPM.prob` alone by causal marginalization, products, `logb`,
and finitely many maxima and minima. -/
noncomputable def phiD (T : UnitTPM N) (S : Finset (Fin N)) (M : Finset (Fin N))
    (m : State N) : ℝ :=
  min (phiCmech T S M m) (phiEmech T S M m)

lemma phiD_le_phiEmech (T : UnitTPM N) (S M : Finset (Fin N)) (m : State N) :
    phiD T S M m ≤ phiEmech T S M m := min_le_right _ _

lemma phiD_le_phiCmech (T : UnitTPM N) (S M : Finset (Fin N)) (m : State N) :
    phiD T S M m ≤ phiCmech T S M m := min_le_left _ _

lemma phiEat_nonneg (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) : 0 ≤ phiEat T M m Z z :=
  sup'OrZero_nonneg fun θ _ => phiEofPartition_nonneg T M m Z z θ

lemma phiCat_nonneg (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) : 0 ≤ phiCat T Z z M m :=
  sup'OrZero_nonneg fun θ _ => phiCofPartition_nonneg T Z z M m θ

lemma phiEpurview_nonneg (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) : 0 ≤ phiEpurview T M m Z := by
  obtain ⟨z, hz⟩ := argmaxSet_nonempty (iiE T M m Z)
  exact (phiEat_nonneg T M m Z z).trans
    (Finset.le_sup' (f := fun w => phiEat T M m Z w) hz)

lemma phiCpurview_nonneg (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) : 0 ≤ phiCpurview T M m Z := by
  obtain ⟨z, hz⟩ := argmaxSet_nonempty (iiC T M m Z)
  exact (phiCat_nonneg T Z z M m).trans
    (Finset.le_sup' (f := fun w => phiCat T Z w M m) hz)

lemma phiEmech_nonneg (T : UnitTPM N) (S M : Finset (Fin N)) (m : State N) :
    0 ≤ phiEmech T S M m :=
  (phiEpurview_nonneg T M m ∅).trans
    (Finset.le_sup' (f := fun Z => phiEpurview T M m Z) (Finset.empty_mem_powerset S))

lemma phiCmech_nonneg (T : UnitTPM N) (S M : Finset (Fin N)) (m : State N) :
    0 ≤ phiCmech T S M m :=
  (phiCpurview_nonneg T M m ∅).trans
    (Finset.le_sup' (f := fun Z => phiCpurview T M m Z) (Finset.empty_mem_powerset S))

lemma phiD_nonneg (T : UnitTPM N) (S M : Finset (Fin N)) (m : State N) :
    0 ≤ phiD T S M m :=
  le_min (phiCmech_nonneg T S M m) (phiEmech_nonneg T S M m)

/-! ### The maximal purview state depends only on the state of the purview

`maxEffStates` and `maxCauseStates` are `argmaxSet` over all `2^N` substrate states, while
`[IIT4, Eq 36]` ranges over `Ω_Z`.  As at the system level (`IIT/System.lean`'s `Fibres`
section) the two agree, because every quantity below reaches the candidate state `z` only
through `agree Z z`, or through `z k` for `k ∈ Z`.  The tie set is therefore a union of
fibres of size `2 ^ (N - |Z|)` on which `φ_e` and `φ_c` are constant. -/

section MechFibres

variable {T : UnitTPM N} {M Z : Finset (Fin N)} {m : State N}

lemma agree_congr {A : Finset (Fin N)} {z z' : State N} (h : ∀ j ∈ A, z j = z' j) :
    agree A z = agree A z' := by
  ext w
  simp only [mem_agree]
  constructor
  · exact fun hw j hj => (hw j hj).trans (h j hj)
  · exact fun hw j hj => (hw j hj).trans (h j hj).symm

lemma effUnit_congr_of_agree {A : Finset (Fin N)} {z z' : State N}
    (h : ∀ j ∈ A, z j = z' j) (k : Fin N) (b : Bool) :
    effUnit T A z k b = effUnit T A z' k b := by
  rw [effUnit, effUnit, agree_congr h]

lemma effRep_congr_of_agree {z z' : State N} (h : ∀ k ∈ Z, z k = z' k) :
    effRep T M m Z z = effRep T M m Z z' :=
  Finset.prod_congr rfl fun k hk => by rw [h k hk]

lemma uncEffRep_congr_of_agree {z z' : State N} (h : ∀ k ∈ Z, z k = z' k) :
    uncEffRep T M Z z = uncEffRep T M Z z' := by
  rw [uncEffRep, uncEffRep]
  exact congrArg (· / ((Finset.univ : Finset (State N)).card : ℝ))
    (Finset.sum_congr rfl fun w _ => effRep_congr_of_agree (T := T) (M := M) (m := w) h)

lemma iiE_congr_of_agree {z z' : State N} (h : ∀ k ∈ Z, z k = z' k) :
    iiE T M m Z z = iiE T M m Z z' := by
  rw [iiE, iiE, effRep_congr_of_agree (T := T) (M := M) (m := m) h,
    uncEffRep_congr_of_agree (T := T) (M := M) h]

/-- **The `[IIT4, Eq 36]` effect tie set is a union of fibres.** -/
theorem mem_maxEffStates_congr {z z' : State N} (h : ∀ k ∈ Z, z k = z' k) :
    z ∈ maxEffStates T M m Z ↔ z' ∈ maxEffStates T M m Z := by
  simp only [maxEffStates, mem_argmaxSet,
    iiE_congr_of_agree (T := T) (M := M) (m := m) h]

lemma causeFwd_congr_of_agree {z z' : State N} (h : ∀ k ∈ Z, z k = z' k) :
    causeFwd T Z z M m = causeFwd T Z z' M m := by
  rw [causeFwd, causeFwd, effRep, effRep]
  exact Finset.prod_congr rfl fun k _ => effUnit_congr_of_agree (T := T) h k (m k)

lemma causeRep_congr_of_agree {z z' : State N} (h : ∀ k ∈ Z, z k = z' k) :
    causeRep T Z z M m = causeRep T Z z' M m := by
  rw [causeRep, causeRep, causeFwd_congr_of_agree (T := T) (M := M) (m := m) h]

lemma iiC_congr_of_agree {z z' : State N} (h : ∀ k ∈ Z, z k = z' k) :
    iiC T M m Z z = iiC T M m Z z' := by
  rw [iiC, iiC, causeRep_congr_of_agree (T := T) (M := M) (m := m) h,
    causeFwd_congr_of_agree (T := T) (M := M) (m := m) h]

/-- **The `[UB, S1 Appendix]` cause tie set is a union of fibres.** -/
theorem mem_maxCauseStates_congr {z z' : State N} (h : ∀ k ∈ Z, z k = z' k) :
    z ∈ maxCauseStates T M m Z ↔ z' ∈ maxCauseStates T M m Z := by
  simp only [maxCauseStates, mem_argmaxSet,
    iiC_congr_of_agree (T := T) (M := M) (m := m) h]

lemma causePart_subset {M Z : Finset (Fin N)} (θ : Partition N M Z) (k : Fin N) :
    θ.causePart k ⊆ Z := by
  rw [Partition.causePart]
  exact Finset.sup_le fun b hb => θ.purv_subset b (Finset.mem_filter.1 hb).1

lemma partEffRep_congr_of_agree {θ : Partition N M Z} {z z' : State N}
    (h : ∀ k ∈ Z, z k = z' k) :
    partEffRep T M m Z z θ = partEffRep T M m Z z' θ :=
  Finset.prod_congr rfl fun k hk => by rw [h k hk]

lemma phiEofPartition_congr_of_agree {θ : Partition N M Z} {z z' : State N}
    (h : ∀ k ∈ Z, z k = z' k) :
    phiEofPartition T M m Z z θ = phiEofPartition T M m Z z' θ := by
  rw [phiEofPartition, phiEofPartition, effRep_congr_of_agree (T := T) (M := M) (m := m) h,
    partEffRep_congr_of_agree (T := T) (M := M) (m := m) (θ := θ) h]

/-- **`φ_e` is constant on the fibres of the restriction to the purview.**  This is the
half of the fibre statement that `phiEpurview`'s supremum depends on. -/
theorem phiEat_congr_of_agree {z z' : State N} (h : ∀ k ∈ Z, z k = z' k) :
    phiEat T M m Z z = phiEat T M m Z z' := by
  have hn : ∀ θ : Partition N M Z,
      normalizedPhi T M m Z z θ = normalizedPhi T M m Z z' θ := fun θ => by
    rw [normalizedPhi, normalizedPhi,
      phiEofPartition_congr_of_agree (T := T) (M := M) (m := m) (θ := θ) h]
  rw [phiEat, phiEat, mipSetE, mipSetE, funext hn]
  exact sup'OrZero_congr fun θ =>
    phiEofPartition_congr_of_agree (T := T) (M := M) (m := m) (θ := θ) h

lemma partCauseFwd_congr_of_agree {θ : Partition N M Z} {z z' : State N}
    (h : ∀ k ∈ Z, z k = z' k) :
    partCauseFwd T Z z M m θ = partCauseFwd T Z z' M m θ :=
  Finset.prod_congr rfl fun k _ =>
    effUnit_congr_of_agree (T := T)
      (fun j hj => h j (causePart_subset θ k hj)) k (m k)

lemma phiCofPartition_congr_of_agree {θ : Partition N M Z} {z z' : State N}
    (h : ∀ k ∈ Z, z k = z' k) :
    phiCofPartition T Z z M m θ = phiCofPartition T Z z' M m θ := by
  rw [phiCofPartition, phiCofPartition,
    causeRep_congr_of_agree (T := T) (M := M) (m := m) h,
    causeFwd_congr_of_agree (T := T) (M := M) (m := m) h,
    partCauseFwd_congr_of_agree (T := T) (M := M) (m := m) (θ := θ) h]

/-- **`φ_c` is constant on the same fibres.** -/
theorem phiCat_congr_of_agree {z z' : State N} (h : ∀ k ∈ Z, z k = z' k) :
    phiCat T Z z M m = phiCat T Z z' M m := by
  have hn : ∀ θ : Partition N M Z,
      normalizedPhiC T Z z M m θ = normalizedPhiC T Z z' M m θ := fun θ => by
    rw [normalizedPhiC, normalizedPhiC,
      phiCofPartition_congr_of_agree (T := T) (M := M) (m := m) (θ := θ) h]
  rw [phiCat, phiCat, mipSetC, mipSetC, funext hn]
  exact sup'OrZero_congr fun θ =>
    phiCofPartition_congr_of_agree (T := T) (M := M) (m := m) (θ := θ) h

/-- Each fibre has `2 ^ (N - |Z|)` states (`card_agree`), and the tie set contains all of
them, so the enlarged `argmaxSet` multiplies the number of ties by that factor. -/
theorem agree_subset_maxEffStates {z : State N} (h : z ∈ maxEffStates T M m Z) :
    agree Z z ⊆ maxEffStates T M m Z := fun _ hw =>
  (mem_maxEffStates_congr (T := T) (M := M) (m := m) (mem_agree.1 hw)).2 h

/-- The same on the cause side. -/
theorem agree_subset_maxCauseStates {z : State N} (h : z ∈ maxCauseStates T M m Z) :
    agree Z z ⊆ maxCauseStates T M m Z := fun _ hw =>
  (mem_maxCauseStates_congr (T := T) (M := M) (m := m) (mem_agree.1 hw)).2 h

end MechFibres

/-! ### The empty purview specifies nothing

`[IIT4, Eq 45]` maximizes over `Z ⊆ S`, and `Z = ∅` is one of the candidates.  It never
wins unless everything is zero: with no purview there is nothing to be informative about,
on either side.  This is what makes a distinction's maximal purviews nonempty, which is
what `Selector` requires of them. -/

lemma phiEat_empty_purview (T : UnitTPM N) (M : Finset (Fin N)) (m z : State N) :
    phiEat T M m ∅ z = 0 := by
  refine le_antisymm ?_ (phiEat_nonneg T M m ∅ z)
  rw [phiEat]
  refine sup'OrZero_le le_rfl fun θ _ => ?_
  simp [phiEofPartition, effRep, partEffRep, pos]

lemma phiCat_empty_purview (T : UnitTPM N) (M : Finset (Fin N)) (m z : State N) :
    phiCat T ∅ z M m = 0 := by
  refine le_antisymm ?_ (phiCat_nonneg T ∅ z M m)
  rw [phiCat]
  refine sup'OrZero_le le_rfl fun θ _ => ?_
  have hpart : ∀ k : Fin N, θ.causePart k = ∅ := by
    intro k
    refine Finset.subset_empty.1 ?_
    rw [Partition.causePart]
    exact Finset.sup_le fun b hb => θ.purv_subset b (Finset.mem_filter.1 hb).1
  have : partCauseFwd T ∅ z M m θ = causeFwd T ∅ z M m := by
    rw [partCauseFwd, causeFwd, effRep]
    exact Finset.prod_congr rfl fun k _ => by rw [hpart k]
  rw [phiCofPartition, this]
  rcases eq_or_ne (causeFwd T ∅ z M m) 0 with h0 | h0
  · simp [h0, pos]
  · rw [div_self h0]
    simp [pos]


/-- **`φ_c` of the empty mechanism vanishes.**  `[IIT4, Eq 44]`'s forward term
`π_e(m | z)` is a product over the mechanism, so for `M = ∅` it is the empty product `1`,
as is its partitioned counterpart; the informativeness `log₂(1/1)` is `0` for every
partition of every purview. -/
lemma phiCat_empty_mech (T : UnitTPM N) (Z : Finset (Fin N)) (z m : State N) :
    phiCat T Z z ∅ m = 0 := by
  refine le_antisymm ?_ (phiCat_nonneg T Z z ∅ m)
  rw [phiCat]
  refine sup'OrZero_le le_rfl fun θ _ => ?_
  simp [phiCofPartition, causeFwd, partCauseFwd, effRep, pos]

lemma phiCmech_empty_mech (T : UnitTPM N) (S : Finset (Fin N)) (m : State N) :
    phiCmech T S ∅ m = 0 := by
  refine le_antisymm ?_ (phiCmech_nonneg T S ∅ m)
  rw [phiCmech]
  refine Finset.sup'_le _ _ fun Z _ => ?_
  rw [phiCpurview]
  exact Finset.sup'_le _ _ fun z _ => (phiCat_empty_mech T Z z m).le

/-- **`φ_d(∅) = 0`**: the empty set is not a mechanism.  `[IIT4, Eq 38]`'s `proper`
condition leaves `Θ(∅, Z)` empty for nonempty `Z`, and the cause side vanishes outright;
`phiD` is the minimum of the two, so it is `0`.  This is what keeps `∅` out of the
distinction set `D` `[IIT4, Eq 48]`, and hence what makes `|D| ≤ 2^N - 1` rather than
`2^N` in `[UB, §2.2, Step 3]`. -/
theorem phiD_empty_mech (T : UnitTPM N) (S : Finset (Fin N)) (m : State N) :
    phiD T S ∅ m = 0 := by
  rw [phiD, phiCmech_empty_mech]
  exact min_eq_left (phiEmech_nonneg T S ∅ m)

/-! ## `Σ φ_d` and the bounds of `[UB]`, applied to the actual definition -/

/-- The sum `∑_{M ⊆ S} φ_d(m)` bounded in `[UB, Eqs 6, 7]`. -/
noncomputable def sumPhiD (T : UnitTPM N) (S : Finset (Fin N)) (m : State N) : ℝ :=
  ∑ M ∈ S.powerset, phiD T S M m

/-- **`[UB, Theorem 1]` without any hypothesis.**  The positivity assumption of
`theorem_one` is unnecessary: when the partitioned repertoire vanishes so does the
unpartitioned one, and `φ` is then `0`. -/
theorem theorem_one' (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (E : Finset (Fin N)) (z : State N) (θ : Partition N M E) :
    phiEofPartition T M m E z θ ≤ M.card * E.card := by
  rcases eq_or_lt_of_le (partEffRep_nonneg T M m E z θ) with h | h
  · have hz := effRep_eq_zero_of_partEffRep_eq_zero T M m E z θ h.symm
    rw [phiEofPartition, hz, zero_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact theorem_one T M m E z θ h

/-- `[UB, Theorem 1]`, cause side, without hypotheses. -/
theorem theorem_one_cause' (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (C : Finset (Fin N)) (z : State N) (θ : Partition N M C) :
    phiCofPartition T C z M m θ ≤ M.card * C.card := by
  rcases eq_or_lt_of_le (partCauseFwd_nonneg T C z M m θ) with h | h
  · have hz : causeFwd T C z M m = 0 :=
      causeFwd_eq_zero_of_partCauseFwd_eq_zero T C z M m θ h.symm
    rw [phiCofPartition, causeRep, hz, zero_div, zero_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact theorem_one_cause T M m C z θ h

lemma phiEat_le (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) : phiEat T M m Z z ≤ M.card * Z.card :=
  sup'OrZero_le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    fun θ _ => theorem_one' T M m Z z θ

lemma phiCat_le (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) : phiCat T Z z M m ≤ M.card * Z.card :=
  sup'OrZero_le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    fun θ _ => theorem_one_cause' T M m Z z θ

lemma phiEpurview_le (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) : phiEpurview T M m Z ≤ M.card * Z.card :=
  Finset.sup'_le _ _ fun z _ => phiEat_le T M m Z z

lemma phiCpurview_le (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) : phiCpurview T M m Z ≤ M.card * Z.card :=
  Finset.sup'_le _ _ fun z _ => phiCat_le T M m Z z

/-- `[UB, Theorem 1]` propagated through the exclusion step `[IIT4, Eq 46]`. -/
lemma phiEmech_le (T : UnitTPM N) (S M : Finset (Fin N)) (m : State N) :
    phiEmech T S M m ≤ M.card * S.card := by
  refine Finset.sup'_le _ _ fun Z hZ => (phiEpurview_le T M m Z).trans ?_
  have : Z.card ≤ S.card := Finset.card_le_card (Finset.mem_powerset.1 hZ)
  have hc : (Z.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast this
  exact mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)

lemma phiCmech_le (T : UnitTPM N) (S M : Finset (Fin N)) (m : State N) :
    phiCmech T S M m ≤ M.card * S.card := by
  refine Finset.sup'_le _ _ fun Z hZ => (phiCpurview_le T M m Z).trans ?_
  have : Z.card ≤ S.card := Finset.card_le_card (Finset.mem_powerset.1 hZ)
  have hc : (Z.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast this
  exact mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)

/-- **`[UB, Theorem 1]` for the actual `φ_d`**: `φ_d(m) ≤ |M| |S|`. -/
theorem phiD_le (T : UnitTPM N) (S M : Finset (Fin N)) (m : State N) :
    phiD T S M m ≤ M.card * S.card :=
  (min_le_right _ _).trans (phiEmech_le T S M m)


/-! ## Distinctions, relations, and `Φ` -/

/-- A purview together with the state of its units, encoded as a set of `(unit, state)`
tuples.  `[IIT4]` works with such tuple sets throughout, because the intersections and
unions defining relations "consider both the units and the state of the units"
`[IIT4, §Composition and causal relations]`; `[UB, §2.2]` follows the same convention. -/
abbrev StatedPurview (N : ℕ) := Finset (Fin N × Bool)

/-- A **causal distinction** `[IIT4, Eq 27]`, `[UB, Table 1]`: an irreducible mechanism
together with its maximally irreducible cause and effect purviews in their maximal
states, and its integrated information `φ_d > 0`. -/
structure Distinction (N : ℕ) where
  /-- The mechanism `M ⊆ S` in its state. -/
  mech : Finset (Fin N)
  /-- The maximally irreducible cause purview in its maximal state, `z*_c`. -/
  zc : StatedPurview N
  /-- The maximally irreducible effect purview in its maximal state, `z*_e`. -/
  ze : StatedPurview N
  /-- Purviews of a distinction are nonempty: a mechanism links an actual cause to an
  actual effect `[IIT4, §Composition and causal distinctions]`. -/
  zc_nonempty : zc.Nonempty
  ze_nonempty : ze.Nonempty
  /-- `φ_d = min {φ_c, φ_e}` `[IIT4, Eq 47]`. -/
  phi : ℝ
  phi_pos : 0 < phi

namespace Distinction

/-- `z*_c ∪ z*_e`, the distinct purview units-in-state of a distinction. -/
def support (d : Distinction N) : StatedPurview N := d.zc ∪ d.ze

lemma support_nonempty (d : Distinction N) : d.support.Nonempty :=
  Finset.Nonempty.inl d.zc_nonempty

lemma card_support_pos (d : Distinction N) : 0 < d.support.card :=
  Finset.card_pos.2 d.support_nonempty

/-- The average integrated information per distinct purview unit `[IIT4, Eq 53]`. -/
noncomputable def phiPerUnit (d : Distinction N) : ℝ := d.phi / d.support.card

lemma phiPerUnit_nonneg (d : Distinction N) : 0 ≤ d.phiPerUnit :=
  div_nonneg d.phi_pos.le (Nat.cast_nonneg _)

end Distinction

/-- The integrated information of a relation `[IIT4, Eq 55]`, `[UB, Eq 8]`: the size of
the congruent overlap times the smallest per-unit integration among the related
distinctions.

This is `[IIT4, Eq 55]` for `|d| ≥ 2`, and every use (`Relation.card_ge_two`,
`relationSets`) is so guarded; at `|d| = 1` the equation instead yields `selfRelPhi`
(`[UB, Eq 9]`), by `facePurview_singleton`. -/
noncomputable def relPhi (d : Finset (Distinction N)) (hd : d.Nonempty) : ℝ :=
  ((d.inf fun D => D.support).card : ℝ) * d.inf' hd Distinction.phiPerUnit

/-- The self-relation of a single distinction `[UB, Eq 9]`. -/
noncomputable def selfRelPhi (d : Distinction N) : ℝ :=
  ((d.zc ∩ d.ze).card : ℝ) * d.phiPerUnit

/-- The congruent overlap of a family of distinctions sits inside each member's
support. -/
lemma inf_support_subset {d : Finset (Distinction N)} {D : Distinction N} (hD : D ∈ d) :
    (d.inf fun D => D.support) ⊆ D.support :=
  Finset.inf_le hD

/-- **`[UB, §2.2]`**: the integrated information of a relation cannot exceed the
integrated information of its weakest distinction, `φ_r(d) ≤ min_{D ∈ d} φ_D`. -/
theorem relPhi_le_phi {d : Finset (Distinction N)} (hd : d.Nonempty)
    {D : Distinction N} (hD : D ∈ d) : relPhi d hd ≤ D.phi := by
  have hsupp : ((d.inf fun D => D.support).card : ℝ) ≤ (D.support.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (inf_support_subset hD)
  have hmin : d.inf' hd Distinction.phiPerUnit ≤ D.phiPerUnit := Finset.inf'_le _ hD
  have hminpos : 0 ≤ d.inf' hd Distinction.phiPerUnit := by
    rw [Finset.le_inf'_iff]
    exact fun D' _ => D'.phiPerUnit_nonneg
  calc relPhi d hd
      = ((d.inf fun D => D.support).card : ℝ) * d.inf' hd Distinction.phiPerUnit := rfl
    _ ≤ (D.support.card : ℝ) * D.phiPerUnit :=
        mul_le_mul hsupp hmin hminpos (Nat.cast_nonneg _)
    _ = D.phi := by
        rw [Distinction.phiPerUnit, mul_div_cancel₀]
        exact Nat.cast_ne_zero.2 D.card_support_pos.ne'

/-! ### Relation faces, and why `[UB, Eq 8]` agrees with `[IIT4, Eq 55]`

`[IIT4, Eq 55]` computes `φ_r` from the **relation purview** `[IIT4, Eq 54]`, the *union of
the face purviews* `⋃_{f ∈ f(d)} o*_f`.  `[UB, Eq 8]` instead uses the single intersection
`⋂_{D ∈ d} (z*_c(D) ∪ z*_e(D))`, which is what `relPhi` implements.  These are not
obviously the same set, and if they differed `relPhi` would be wrong.  They agree, and the
reason is elementary: a face is a choice, for each distinction, of its cause, its effect,
or both; so a unit-in-state lies on *some* face exactly when every distinction of the
relation constrains it on at least one side. -/

/-- The cause (`false`) or effect (`true`) purview of a distinction. -/
def Distinction.side (D : Distinction N) : Bool → StatedPurview N
  | false => D.zc
  | true => D.ze

lemma Distinction.side_subset_support (D : Distinction N) (b : Bool) :
    D.side b ⊆ D.support := by
  cases b
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

lemma mem_finset_inf {ι : Type*} {s : Finset ι} {g : ι → StatedPurview N}
    {u : Fin N × Bool} : u ∈ s.inf g ↔ ∀ i ∈ s, u ∈ g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.inf_insert, ih]

/-- A **relation face** `[IIT4, Eqs 49, 52]`: for each distinction of the relation, a
nonempty choice among its cause and its effect.  A relation over `|d|` distinctions has up
to `3 ^ |d|` faces, matching `[IIT4, §Composition and causal relations]`.

`[IIT4, Eq 49]`'s second clause -- a face's overlap must be nonempty -- is deliberately not
a field: empty faces contribute nothing to the `[IIT4, Eq 55]` union
(`mem_inf_support_iff_exists_face` carries the content either way), and `exists_face_mem`
only ever constructs faces with nonempty purviews. -/
structure Face (d : Finset (Distinction N)) where
  /-- Which sides of each distinction the face selects. -/
  pick : Distinction N → Finset Bool
  pick_nonempty : ∀ D ∈ d, (pick D).Nonempty
  /-- `[IIT4, Eq 49]` requires `|z| > 1`.  For a single distinction that forces the face to
  take *both* its cause and its effect — this is the self-relation case. -/
  pick_self : d.card = 1 → ∀ D ∈ d, pick D = {false, true}

/-- The **face purview** `o*(z)` `[IIT4, Eq 50]`: the congruent overlap of the selected
causes and effects. -/
noncomputable def facePurview {d : Finset (Distinction N)} (f : Face d) : StatedPurview N :=
  d.inf fun D => (f.pick D).inf D.side

/-- Every face purview sits inside the congruent overlap of the supports. -/
theorem facePurview_subset_inf_support {d : Finset (Distinction N)} (f : Face d) :
    facePurview f ⊆ d.inf Distinction.support := by
  intro u hu
  rw [facePurview, mem_finset_inf] at hu
  rw [mem_finset_inf]
  intro D hD
  obtain ⟨b, hb⟩ := f.pick_nonempty D hD
  exact D.side_subset_support b (mem_finset_inf.1 (hu D hD) b hb)

/-- Conversely, anything in the congruent overlap of the supports lies on some face:
select, for each distinction, a side that contains it. -/
theorem exists_face_mem {d : Finset (Distinction N)} (hcard : 2 ≤ d.card)
    {u : Fin N × Bool} (hu : u ∈ d.inf Distinction.support) :
    ∃ f : Face d, u ∈ facePurview f := by
  classical
  refine ⟨⟨fun D => if u ∈ D.zc then {false} else {true}, fun D _ => ?_,
    fun h => absurd h (by omega)⟩, ?_⟩
  · by_cases h : u ∈ D.zc <;> simp [h]
  · rw [facePurview, mem_finset_inf]
    intro D hD
    have hsupp : u ∈ D.support := mem_finset_inf.1 hu D hD
    rw [mem_finset_inf]
    intro b hb
    by_cases h : u ∈ D.zc
    · simp [h] at hb
      subst hb
      exact h
    · simp [h] at hb
      subst hb
      rcases Finset.mem_union.1 hsupp with h1 | h1
      · exact absurd h1 h
      · exact h1

/-- **`[IIT4, Eq 55]` and `[UB, Eq 8]` compute the same purview.**  The relation purview of
`[IIT4, Eq 54]` — the union of all face purviews — is exactly the congruent overlap
`⋂_{D ∈ d} (z*_c(D) ∪ z*_e(D))` that `relPhi` uses.  So the simplified formula of `[UB]` is
not an approximation: it is the same quantity. -/
theorem mem_inf_support_iff_exists_face {d : Finset (Distinction N)} (hcard : 2 ≤ d.card)
    {u : Fin N × Bool} :
    u ∈ d.inf Distinction.support ↔ ∃ f : Face d, u ∈ facePurview f :=
  ⟨exists_face_mem hcard, fun ⟨f, hf⟩ => facePurview_subset_inf_support f hf⟩

/-- At degree one every face is bidirectional, so the face purview is `z*_c ∩ z*_e` — the
**intersection**, not the union.  This is `[UB, Eq 9]`, and it is why a self-relation is
governed by `selfRelPhi` rather than by `relPhi`. -/
theorem facePurview_singleton {D : Distinction N} (f : Face {D}) :
    facePurview f = D.zc ∩ D.ze := by
  have hp : f.pick D = {false, true} :=
    f.pick_self (by simp) D (by simp)
  rw [facePurview]
  rw [show ({D} : Finset (Distinction N)).inf
      (fun E => (f.pick E).inf E.side) = (f.pick D).inf D.side from Finset.inf_singleton]
  rw [hp]
  rw [show ({false, true} : Finset Bool).inf D.side = D.side false ⊓ D.side true by
    rw [Finset.inf_insert, Finset.inf_singleton]]
  rfl

/-- The self-relation bound is `|z*_c ∩ z*_e| / |z*_c ∪ z*_e| ≤ 1`. -/
theorem selfRelPhi_le_phi (D : Distinction N) : selfRelPhi D ≤ D.phi := by
  have hsub : ((D.zc ∩ D.ze).card : ℝ) ≤ (D.support.card : ℝ) := by
    exact_mod_cast Finset.card_le_card
      ((Finset.inter_subset_left).trans Finset.subset_union_left)
  calc selfRelPhi D = ((D.zc ∩ D.ze).card : ℝ) * D.phiPerUnit := rfl
    _ ≤ (D.support.card : ℝ) * D.phiPerUnit :=
        mul_le_mul_of_nonneg_right hsub D.phiPerUnit_nonneg
    _ = D.phi := by
        rw [Distinction.phiPerUnit, mul_div_cancel₀]
        exact Nat.cast_ne_zero.2 D.card_support_pos.ne'

/-- A **causal relation** `[IIT4, Eq 51]`: two or more distinctions bound by the congruent
overlap of their causes and/or effects, with `φ_r > 0`.

Degree is required to be at least `2`.  `[UB, Eq 8]`, which `relPhi` implements, is stated
only for `|d| ≥ 2`; the degree-one case is the *self*-relation of `[UB, Eq 9]`, whose
purview is `z*_c ∩ z*_e` rather than the overlap of supports, and is carried by
`SelfRelation` below.  (PyPhi's `Relation.purview` branches on `is_self_relation` in exactly
this way.)  Collapsing the two would give a self-relation the value `φ_d` instead of
`|z*_c ∩ z*_e| φ_d / |z*_c ∪ z*_e|`. -/
structure Relation (N : ℕ) where
  /-- The distinctions bound by the relation. -/
  distinctions : Finset (Distinction N)
  /-- `[UB, Eq 8]` governs relations of degree `≥ 2`. -/
  card_ge_two : 2 ≤ distinctions.card
  /-- The relation's integrated information `[IIT4, Eq 55]`. -/
  phi : ℝ
  phi_eq : phi = relPhi distinctions (Finset.card_pos.mp (by omega))
  phi_pos : 0 < phi

/-- A **self-relation** `[IIT4, Eq 49]`, `[UB, Eq 9]`: the cause and effect of a *single*
distinction overlapping congruently. -/
structure SelfRelation (N : ℕ) where
  /-- The distinction relating to itself. -/
  distinction : Distinction N
  /-- Its integrated information `[UB, Eq 9]`. -/
  phi : ℝ
  phi_eq : phi = selfRelPhi distinction
  phi_pos : 0 < phi

/-- A **cause-effect structure** `[IIT4, Eqs 57, 58]`: the distinctions specified by a
substrate together with the relations binding them, `C(D) = D ∪ R(D)`.  `[IIT4, Eq 58]`
is the same set with its members written out,
`C(T_e, T_c, s*) = {d(m) = (m, z*, φ_d) ∈ D} ∪ {r(d) = (d, f(d), φ_r) ∈ R(D)}`.  Its two
components are the fields below, with `R(D)` split in two: `[IIT4, Eq 56]` lets `d` range
over *all* subsets of `D`, so `R(D)` carries the singletons as well, and those are the
self-relations of `[UB, Eq 9]`. -/
structure CauseEffectStructure (N : ℕ) where
  /-- The set `D` of causal distinctions `[IIT4, Eq 48]`. -/
  distinctions : Finset (Distinction N)
  /-- The relations of degree `≥ 2` `[IIT4, Eq 56]`. -/
  relations : Finset (Relation N)
  /-- The self-relations `[UB, Eq 9]`. -/
  selfRelations : Finset (SelfRelation N)

/-- **Structure integrated information `Φ`** `[IIT4, Eq 59]`: the sum of the integrated
information of every distinction and relation composing the cause-effect structure of a
complex.  In IIT 4.0 this is the *quantity* of consciousness, the structure itself being
its *quality*. -/
noncomputable def Phi (C : CauseEffectStructure N) : ℝ :=
  (∑ d ∈ C.distinctions, d.phi) + (∑ r ∈ C.relations, r.phi)
    + ∑ r ∈ C.selfRelations, r.phi

lemma Phi_nonneg (C : CauseEffectStructure N) : 0 ≤ Phi C :=
  add_nonneg (add_nonneg (Finset.sum_nonneg fun d _ => d.phi_pos.le)
      (Finset.sum_nonneg fun r _ => r.phi_pos.le))
    (Finset.sum_nonneg fun r _ => r.phi_pos.le)

/-- A cause-effect structure is **specified by** the transition probabilities `T` on the
substrate `S` in state `s` when every distinction carries the `φ_d` computed from `T` by
`[IIT4, Eq 47]`, and the relations bind only distinctions of the structure.

`Relation.phi_eq` already forces `φ_r` to be computed from the distinctions, so this is
the only additional tie needed to pin `Φ` to `T`. -/
def CauseEffectStructure.SpecifiedBy (C : CauseEffectStructure N) (T : UnitTPM N)
    (S : Finset (Fin N)) (s : State N) : Prop :=
  (∀ d ∈ C.distinctions, d.mech ⊆ S ∧ d.phi = phiD T S d.mech s) ∧
  (∀ r ∈ C.relations, r.distinctions ⊆ C.distinctions)

/-- For a structure specified by `T`, `Φ` is determined by the transition probabilities
together with the structure's combinatorics. -/
theorem Phi_eq_of_specifiedBy {C : CauseEffectStructure N} {T : UnitTPM N}
    {S : Finset (Fin N)} {s : State N} (h : C.SpecifiedBy T S s) :
    Phi C = (∑ d ∈ C.distinctions, phiD T S d.mech s)
      + (∑ r ∈ C.relations, r.phi) + ∑ r ∈ C.selfRelations, r.phi := by
  rw [Phi]
  congr 2
  exact Finset.sum_congr rfl fun d hd => (h.1 d hd).2

/-- The distinction part of `Φ` for a structure specified by `T` is at most `sumPhiD`.

The distinction set `D` of `[IIT4, Eq 48]` is cut down from all subsets of `S` by two
further requirements — `φ_d > 0`, and congruence of the distinction's cause-effect state
with the system's `s'` — so summing over all of `S.powerset` can only overshoot.  Hence
`sumPhiD_le` bounds the true `∑_{d ∈ D} φ_d` a fortiori. -/
theorem sum_phiD_le_sumPhiD {C : CauseEffectStructure N} {T : UnitTPM N}
    {S : Finset (Fin N)} {s : State N} (h : C.SpecifiedBy T S s)
    (hinj : ∀ d ∈ C.distinctions, ∀ e ∈ C.distinctions, d.mech = e.mech → d = e) :
    (∑ d ∈ C.distinctions, d.phi) ≤ sumPhiD T S s := by
  classical
  have himg : C.distinctions.image Distinction.mech ⊆ S.powerset :=
    Finset.image_subset_iff.2 fun d hd => Finset.mem_powerset.2 (h.1 d hd).1
  have hsum : ∑ d ∈ C.distinctions, phiD T S d.mech s
      = ∑ M ∈ C.distinctions.image Distinction.mech, phiD T S M s := by
    rw [Finset.sum_image fun d hd e he hde => hinj d hd e he hde]
  rw [Finset.sum_congr rfl fun d hd => (h.1 d hd).2, hsum, sumPhiD]
  exact Finset.sum_le_sum_of_subset_of_nonneg himg fun M _ _ => phiD_nonneg T S M s

/-- Every relation of a cause-effect structure is bounded by each distinction it binds,
so `Φ` is controlled by the distinctions together with the *number* of relations. -/
theorem Phi_le (C : CauseEffectStructure N) (B : ℝ)
    (hd : ∀ d ∈ C.distinctions, d.phi ≤ B)
    (hr : ∀ r ∈ C.relations, r.phi ≤ B)
    (hs : ∀ r ∈ C.selfRelations, r.phi ≤ B) :
    Phi C ≤ (C.distinctions.card + C.relations.card + C.selfRelations.card) * B := by
  have h1 : (∑ d ∈ C.distinctions, d.phi) ≤ C.distinctions.card * B := by
    simpa [Finset.sum_const, nsmul_eq_mul] using
      Finset.sum_le_sum (f := fun d : Distinction N => d.phi) (g := fun _ => B) hd
  have h2 : (∑ r ∈ C.relations, r.phi) ≤ C.relations.card * B := by
    simpa [Finset.sum_const, nsmul_eq_mul] using
      Finset.sum_le_sum (f := fun r : Relation N => r.phi) (g := fun _ => B) hr
  have h3 : (∑ r ∈ C.selfRelations, r.phi) ≤ C.selfRelations.card * B := by
    simpa [Finset.sum_const, nsmul_eq_mul] using
      Finset.sum_le_sum (f := fun r : SelfRelation N => r.phi) (g := fun _ => B) hs
  calc Phi C = (∑ d ∈ C.distinctions, d.phi) + (∑ r ∈ C.relations, r.phi)
        + ∑ r ∈ C.selfRelations, r.phi := rfl
    _ ≤ C.distinctions.card * B + C.relations.card * B + C.selfRelations.card * B :=
        add_le_add (add_le_add h1 h2) h3
    _ = (C.distinctions.card + C.relations.card + C.selfRelations.card) * B := by ring

/-! ## The summation bounds `[UB, Eq 6]` and `[UB, Eq 7]` -/

/-- `2 ∑_{t ⊆ s} |t| = |s| 2^{|s|}`.  Stated with the factor `2` on the left so that it
is correct for `s = ∅` as well (truncated subtraction would break `|s| 2^{|s|-1}`). -/
private lemma two_mul_sum_card_powerset {α : Type*} [DecidableEq α] (s : Finset α) :
    2 * ∑ t ∈ s.powerset, t.card = s.card * 2 ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hcard : ∀ t ∈ s.powerset, (insert a t).card = t.card + 1 := fun t ht =>
        Finset.card_insert_of_notMem fun h => ha (Finset.mem_powerset.1 ht h)
      have hsplit : ∑ t ∈ s.powerset, (insert a t).card
          = (∑ t ∈ s.powerset, t.card) + 2 ^ s.card := by
        rw [Finset.sum_congr rfl hcard, Finset.sum_add_distrib]
        simp [Finset.card_powerset]
      rw [Finset.sum_powerset_insert ha, hsplit, Finset.card_insert_of_notMem ha]
      calc 2 * ((∑ t ∈ s.powerset, t.card) + ((∑ t ∈ s.powerset, t.card) + 2 ^ s.card))
          = (2 * ∑ t ∈ s.powerset, t.card) + (2 * ∑ t ∈ s.powerset, t.card)
              + 2 * 2 ^ s.card := by ring
        _ = s.card * 2 ^ s.card + s.card * 2 ^ s.card + 2 * 2 ^ s.card := by rw [ih]
        _ = (s.card + 1) * 2 ^ (s.card + 1) := by ring

/-- `4 ∑_{t ⊆ s} |t|² = |s| (|s| + 1) 2^{|s|}`.  Again the factor `4` is kept on the
left: the form `|s|(|s|+1) 2^{|s|-2}` of `[UB, Eq 7]` gives `2`, not `1`, at `|s| = 1` when read
with truncated natural subtraction. -/
private lemma four_mul_sum_sq_card_powerset {α : Type*} [DecidableEq α] (s : Finset α) :
    4 * ∑ t ∈ s.powerset, t.card ^ 2 = s.card * (s.card + 1) * 2 ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hcard : ∀ t ∈ s.powerset, (insert a t).card ^ 2
          = t.card ^ 2 + 2 * t.card + 1 := by
        intro t ht
        rw [Finset.card_insert_of_notMem fun h => ha (Finset.mem_powerset.1 ht h)]
        ring
      have hsplit : ∑ t ∈ s.powerset, (insert a t).card ^ 2
          = (∑ t ∈ s.powerset, t.card ^ 2) + 2 * (∑ t ∈ s.powerset, t.card)
            + 2 ^ s.card := by
        rw [Finset.sum_congr rfl hcard, Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum]
        simp [Finset.card_powerset]
      rw [Finset.sum_powerset_insert ha, hsplit, Finset.card_insert_of_notMem ha]
      calc 4 * ((∑ t ∈ s.powerset, t.card ^ 2)
              + ((∑ t ∈ s.powerset, t.card ^ 2) + 2 * (∑ t ∈ s.powerset, t.card)
                + 2 ^ s.card))
          = 2 * (4 * ∑ t ∈ s.powerset, t.card ^ 2)
              + 4 * (2 * ∑ t ∈ s.powerset, t.card) + 4 * 2 ^ s.card := by ring
        _ = 2 * (s.card * (s.card + 1) * 2 ^ s.card) + 4 * (s.card * 2 ^ s.card)
              + 4 * 2 ^ s.card := by rw [ih, two_mul_sum_card_powerset]
        _ = (s.card + 1) * (s.card + 1 + 1) * 2 ^ (s.card + 1) := by ring

/-- `∑_{M ⊆ S} |M| = N 2^N / 2`, over the reals. -/
lemma sum_card_powerset_real (N : ℕ) :
    ∑ M ∈ (Finset.univ : Finset (Fin N)).powerset, (M.card : ℝ) = (N : ℝ) * 2 ^ N / 2 := by
  have h := two_mul_sum_card_powerset (Finset.univ : Finset (Fin N))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have h' : ((2 * ∑ M ∈ (Finset.univ : Finset (Fin N)).powerset, M.card : ℕ) : ℝ)
      = ((N * 2 ^ N : ℕ) : ℝ) := by exact_mod_cast congrArg (fun k : ℕ => k) h
  push_cast at h'
  linarith

/-- `∑_{M ⊆ S} |M|² = N (N+1) 2^N / 4`, over the reals. -/
lemma sum_sq_card_powerset_real (N : ℕ) :
    ∑ M ∈ (Finset.univ : Finset (Fin N)).powerset, ((M.card : ℝ) ^ 2)
      = (N : ℝ) * (N + 1) * 2 ^ N / 4 := by
  have h := four_mul_sum_sq_card_powerset (Finset.univ : Finset (Fin N))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have h' : ((4 * ∑ M ∈ (Finset.univ : Finset (Fin N)).powerset, M.card ^ 2 : ℕ) : ℝ)
      = ((N * (N + 1) * 2 ^ N : ℕ) : ℝ) := by exact_mod_cast congrArg (fun k : ℕ => k) h
  push_cast at h'
  linarith

/-- **`[UB, Eq 6]`**.  Summing Theorem 1 over all mechanisms, with every purview allowed
to be the whole system, gives `∑ φ ≤ (N² / 2) 2^N`. -/
theorem sum_phi_le (N : ℕ) (φ : Finset (Fin N) → ℝ)
    (hφ : ∀ M, φ M ≤ M.card * N) :
    ∑ M ∈ (Finset.univ : Finset (Fin N)).powerset, φ M
      ≤ (N : ℝ) ^ 2 / 2 * 2 ^ N := by
  calc ∑ M ∈ (Finset.univ : Finset (Fin N)).powerset, φ M
      ≤ ∑ M ∈ (Finset.univ : Finset (Fin N)).powerset, ((M.card : ℝ) * N) :=
        Finset.sum_le_sum fun M _ => hφ M
    _ = (∑ M ∈ (Finset.univ : Finset (Fin N)).powerset, (M.card : ℝ)) * N := by
        rw [Finset.sum_mul]
    _ = ((N : ℝ) * 2 ^ N / 2) * N := by rw [sum_card_powerset_real]
    _ = (N : ℝ) ^ 2 / 2 * 2 ^ N := by ring

/-- **`[UB, Eq 7]`**, the bound over unique purviews: matching mechanism and purview
sizes gives `∑ φ ≤ (N(N+1)/4) 2^N`. -/
theorem sum_phi_le_sq (N : ℕ) (φ : Finset (Fin N) → ℝ)
    (hφ : ∀ M, φ M ≤ (M.card : ℝ) ^ 2) :
    ∑ M ∈ (Finset.univ : Finset (Fin N)).powerset, φ M
      ≤ (N : ℝ) * (N + 1) / 4 * 2 ^ N := by
  calc ∑ M ∈ (Finset.univ : Finset (Fin N)).powerset, φ M
      ≤ ∑ M ∈ (Finset.univ : Finset (Fin N)).powerset, ((M.card : ℝ) ^ 2) :=
        Finset.sum_le_sum fun M _ => hφ M
    _ = (N : ℝ) * (N + 1) * 2 ^ N / 4 := sum_sq_card_powerset_real N
    _ = (N : ℝ) * (N + 1) / 4 * 2 ^ N := by ring

/-- **`[UB, Eq 7]` for the development's own `φ`**, in the reading of `[UB, Table 3]`'s
"Bound II" row (`Z*_e = Z*_c = M`, purview equal to mechanism), which is the reading under
which step (a) of `[UB, Eq 7]` -- "each purview can be assigned to only one mechanism" --
holds by construction.  Without pinning the purview, `φ_d` maximizes over all `Z ⊆ S` and
the bound `φ_d(M) ≤ |M|²` need not hold, so no instance exists for `phiD` itself. -/
theorem sum_phiEpurview_le_sq (N : ℕ) (T : UnitTPM N) (m : State N) :
    ∑ M ∈ (Finset.univ : Finset (Fin N)).powerset, phiEpurview T M m M
      ≤ (N : ℝ) * (N + 1) / 4 * 2 ^ N :=
  sum_phi_le_sq N (fun M => phiEpurview T M m M) fun M => by
    simpa [sq] using phiEpurview_le T M m M

/-- The elementary inequality behind step `(a)` of `[UB, Eq 7]`: matching the sizes of
mechanism and purview maximises the bound. -/
lemma mul_add_mul_le_sq_add_sq (a b : ℝ) : a * b + b * a ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- **`[UB, Eq 6]` for the actual definition**: over the whole substrate,
`∑_{M ⊆ S} φ_d(m) ≤ (N²/2) 2^N`.

This is the point of the whole development: the bound of `[UB]` now constrains the `φ_d`
built from the transition probabilities by `[IIT4]`'s definitional chain, rather than an
uninterpreted parameter. -/
theorem sumPhiD_le (T : UnitTPM N) (m : State N) :
    sumPhiD T Finset.univ m ≤ (N : ℝ) ^ 2 / 2 * 2 ^ N := by
  refine sum_phi_le N (fun M => phiD T Finset.univ M m) fun M => ?_
  have h := phiD_le T Finset.univ M m
  simpa [Finset.card_univ, Fintype.card_fin] using h

/-! ### Ingredients for `[UB, Theorem 2]` -/

/-- A product of probabilities equals `1` only if every factor does. -/
lemma effUnit_eq_one_of_effRep_eq_one (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (Z : Finset (Fin N)) (z : State N) (h : effRep T M m Z z = 1) :
    ∀ k ∈ Z, effUnit T M m k (z k) = 1 := by
  intro k hk
  by_contra hne
  have hlt : effUnit T M m k (z k) < 1 :=
    lt_of_le_of_ne (effUnit_le_one T M m k (z k)) hne
  have hprod : effUnit T M m k (z k) * ∏ j ∈ Z.erase k, effUnit T M m j (z j)
      = effRep T M m Z z :=
    Finset.mul_prod_erase Z (fun j => effUnit T M m j (z j)) hk
  have hP1 : (∏ j ∈ Z.erase k, effUnit T M m j (z j)) ≤ 1 :=
    Finset.prod_le_one (fun j _ => effUnit_nonneg T M m j (z j))
      (fun j _ => effUnit_le_one T M m j (z j))
  have hP0 : 0 ≤ ∏ j ∈ Z.erase k, effUnit T M m j (z j) :=
    Finset.prod_nonneg fun j _ => effUnit_nonneg T M m j (z j)
  have : effRep T M m Z z < 1 := by
    rw [← hprod]
    calc effUnit T M m k (z k) * ∏ j ∈ Z.erase k, effUnit T M m j (z j)
        ≤ effUnit T M m k (z k) * 1 :=
          mul_le_mul_of_nonneg_left hP1 (effUnit_nonneg T M m k (z k))
      _ = effUnit T M m k (z k) := mul_one _
      _ < 1 := hlt
  rw [h] at this
  exact lt_irrefl _ this

/-- Attaining the maximal cut count forces the **total** partition: every purview unit
loses every connection. -/
lemma effPart_eq_empty_of_cutCount_max {M Z : Finset (Fin N)} (θ : Partition N M Z)
    (h : cutCount M Z θ = M.card * Z.card) : ∀ k ∈ Z, θ.effPart k = ∅ := by
  have hadd := θ.sum_effPart_add
  rw [cutCount] at h
  have hzero : ∑ b ∈ θ.blocks, b.1.card * b.2.card = 0 := by omega
  intro k hk
  obtain ⟨b, hb, hkb⟩ := θ.purv_cover k hk
  have hbz : b.1.card * b.2.card = 0 :=
    (Finset.sum_eq_zero_iff.1 hzero) b hb
  have hb2 : 0 < b.2.card := Finset.card_pos.2 ⟨k, hkb⟩
  have hb1 : b.1.card = 0 := by
    rcases Nat.mul_eq_zero.1 hbz with h1 | h2
    · exact h1
    · omega
  rw [θ.effPart_eq hb hkb]
  exact Finset.card_eq_zero.1 hb1

/-- With the total partition the partitioned repertoire is the fully unconstrained one. -/
lemma partEffRep_of_total {M Z : Finset (Fin N)} (T : UnitTPM N) (m z : State N)
    (θ : Partition N M Z) (h : ∀ k ∈ Z, θ.effPart k = ∅) :
    partEffRep T M m Z z θ = ∏ k ∈ Z, effUnit T ∅ m k (z k) :=
  Finset.prod_congr rfl fun k hk => by rw [h k hk]

/-- A unit whose effect probability is `1` in one state has probability `0` in the other. -/
lemma effUnit_eq_zero_of_ne {T : UnitTPM N} {M : Finset (Fin N)} {m : State N}
    {k : Fin N} {b b' : Bool} (hb : effUnit T M m k b = 1) (hne : b' ≠ b) :
    effUnit T M m k b' = 0 := by
  have hadd := effUnit_add T M m k
  cases b <;> cases b' <;> simp_all

/-- **The maximal states agree on shared purview units.**  If `M ⊆ M'` and both fully
specify a shared unit, they specify the *same* state for it: `M` forces it, so by
`[UB, Lemma 3]` `M'` forces the same value, and a probability-one state is unique. -/
lemma state_agree_of_det {T : UnitTPM N} {M M' : Finset (Fin N)} (hMM' : M ⊆ M')
    {m z z' : State N} {k : Fin N}
    (h : effUnit T M m k (z k) = 1) (h' : effUnit T M' m k (z' k) = 1) :
    z' k = z k := by
  by_contra hne
  have hM' : effUnit T M' m k (z k) = 1 := effUnit_eq_one_of_subset T hMM' m k (z k) h
  have : effUnit T M' m k (z' k) = 0 := effUnit_eq_zero_of_ne hM' hne
  rw [this] at h'
  exact absurd h' (by norm_num)

/-- The unconstrained probability of a fully specified state is at least `2 ^ (-|M|)`,
in the `logb` form used in the strictness estimate. -/
lemma logb_uncEffUnit_le {T : UnitTPM N} {M : Finset (Fin N)} {m : State N} {k : Fin N}
    {b : Bool} (h : effUnit T M m k b = 1) :
    Real.logb 2 (1 / effUnit T ∅ m k b) ≤ M.card := by
  have hge : ((2 : ℝ) ^ M.card)⁻¹ ≤ effUnit T ∅ m k b :=
    uncEffUnit_ge_of_effUnit_eq_one T M m k b h
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ M.card)⁻¹ := by positivity
  have hu : 0 < effUnit T ∅ m k b := lt_of_lt_of_le hpos hge
  rw [one_div, Real.logb_inv]
  have hle : Real.logb 2 (((2 : ℝ) ^ M.card)⁻¹) ≤ Real.logb 2 (effUnit T ∅ m k b) :=
    Real.logb_le_logb_of_le (by norm_num) hpos hge
  have hval : Real.logb 2 (((2 : ℝ) ^ M.card)⁻¹) = -(M.card : ℝ) := by
    rw [Real.logb_inv]
    congr 1
    rw [show ((2 : ℝ) ^ M.card) = (2 : ℝ) ^ ((M.card : ℕ) : ℝ) by rw [Real.rpow_natCast]]
    rw [Real.logb_rpow (by norm_num) (by norm_num)]
  rw [hval] at hle
  linarith

/-- **Attaining the bound is a strong condition.**  If `φ_e` at some partition equals
`|M||Z|`, then the selectivity is `1`, the partition is total, and every purview unit is
fully specified by the mechanism.  This packages `[UB, Lemma 4]` with the cut-count
analysis. -/
lemma attains_max_iff {T : UnitTPM N} {M Z : Finset (Fin N)} {m z : State N}
    {θ : Partition N M Z} (hZ : Z.Nonempty)
    (h : phiEofPartition T M m Z z θ = M.card * Z.card) :
    effRep T M m Z z = 1 ∧ (∀ k ∈ Z, θ.effPart k = ∅) ∧
      (∀ k ∈ Z, effUnit T M m k (z k) = 1) := by
  have hMpos : 0 < M.card := by
    rcases Nat.eq_zero_or_pos M.card with hM0 | hpos
    · exfalso
      obtain ⟨k, hk⟩ := hZ
      have hMe : M = ∅ := Finset.card_eq_zero.1 hM0
      refine θ.effPart_ne hk (Finset.Subset.antisymm (θ.effPart_subset k) ?_)
      intro x hx
      rw [hMe] at hx
      exact absurd hx (Finset.notMem_empty x)
    · exact hpos
  have hZpos : 0 < Z.card := Finset.card_pos.2 hZ
  have hMZ : (0 : ℝ) < (M.card : ℝ) * Z.card := by
    have h1 : (0 : ℝ) < (M.card : ℝ) := by exact_mod_cast hMpos
    have h2 : (0 : ℝ) < (Z.card : ℝ) := by exact_mod_cast hZpos
    positivity
  have hcut : (cutCount M Z θ : ℝ) ≤ (M.card : ℝ) * Z.card := by
    exact_mod_cast cutCount_le M Z θ
  have hppos : 0 < partEffRep T M m Z z θ := by
    rcases eq_or_lt_of_le (partEffRep_nonneg T M m Z z θ) with h0 | h0
    · exfalso
      have hz := effRep_eq_zero_of_partEffRep_eq_zero T M m Z z θ h0.symm
      rw [phiEofPartition, hz, zero_mul] at h
      rw [← h] at hMZ
      exact lt_irrefl _ hMZ
    · exact h0
  have hinf := logb_ratio_le_cutCount T M m Z z θ hppos
  have hsel : effRep T M m Z z = 1 := by
    by_contra hne
    have hlt : effRep T M m Z z < 1 := lt_of_le_of_ne (effRep_le_one T M m Z z) hne
    have hstrict : phiEofPartition T M m Z z θ < (M.card : ℝ) * Z.card := by
      calc phiEofPartition T M m Z z θ
          ≤ effRep T M m Z z * ((M.card : ℝ) * Z.card) :=
            mul_le_mul_of_nonneg_left (hinf.trans hcut) (effRep_nonneg T M m Z z)
        _ < 1 * ((M.card : ℝ) * Z.card) := mul_lt_mul_of_pos_right hlt hMZ
        _ = (M.card : ℝ) * Z.card := one_mul _
    rw [h] at hstrict
    exact lt_irrefl _ hstrict
  have hcutmax : cutCount M Z θ = M.card * Z.card := by
    rw [phiEofPartition, hsel, one_mul] at h
    rw [hsel, h] at hinf
    have hle := cutCount_le M Z θ
    have hcast : ((M.card * Z.card : ℕ) : ℝ) ≤ (cutCount M Z θ : ℝ) := by
      push_cast
      linarith
    have hnat : M.card * Z.card ≤ cutCount M Z θ := by exact_mod_cast hcast
    omega
  exact ⟨hsel, effPart_eq_empty_of_cutCount_max θ hcutmax,
    effUnit_eq_one_of_effRep_eq_one T M m Z z hsel⟩

/-- **The strictness estimate of `[UB, S3, Lemma 7]`.**

Suppose `M` fully specifies every unit of `Z`.  Then for any other mechanism `M'` that
also fully specifies every unit of `Z'`, the total informativeness against the
unconstrained repertoire splits over `Z' ∩ Z` and `Z' \ Z`: units shared with `Z` are
already pinned by the *smaller* `M`, so they contribute at most `|M|` each, while the rest
contribute at most `|M'|`.  When `M ⊂ M'` and the purviews overlap, the total is strictly
below `|M'||Z'|`. -/
lemma informativeness_split_lt {T : UnitTPM N} {M M' Z Z' : Finset (Fin N)}
    {m z z' : State N}
    (hMM' : M ⊂ M') (hover : (Z ∩ Z').Nonempty)
    (hdet : ∀ k ∈ Z, effUnit T M m k (z k) = 1)
    (hdet' : ∀ k ∈ Z', effUnit T M' m k (z' k) = 1) :
    ∑ k ∈ Z', Real.logb 2 (1 / effUnit T ∅ m k (z' k)) < (M'.card : ℝ) * Z'.card := by
  classical
  have hsub : M ⊆ M' := hMM'.subset
  have hcardlt : M.card < M'.card := Finset.card_lt_card hMM'
  have hshared : ∀ k ∈ Z' ∩ Z,
      Real.logb 2 (1 / effUnit T ∅ m k (z' k)) ≤ (M.card : ℝ) := by
    intro k hk
    obtain ⟨hkZ', hkZ⟩ := Finset.mem_inter.1 hk
    have hz : z' k = z k := state_agree_of_det hsub (hdet k hkZ) (hdet' k hkZ')
    rw [hz]
    exact logb_uncEffUnit_le (hdet k hkZ)
  have hrest : ∀ k ∈ Z' \ Z,
      Real.logb 2 (1 / effUnit T ∅ m k (z' k)) ≤ (M'.card : ℝ) := fun k hk =>
    logb_uncEffUnit_le (hdet' k (Finset.mem_sdiff.1 hk).1)
  have hunion : (Z' ∩ Z) ∪ (Z' \ Z) = Z' := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hdisj : Disjoint (Z' ∩ Z) (Z' \ Z) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    exact (Finset.mem_sdiff.1 ha').2 (Finset.mem_inter.1 ha).2
  have hsum : (∑ k ∈ Z' ∩ Z, Real.logb 2 (1 / effUnit T ∅ m k (z' k)))
      + (∑ k ∈ Z' \ Z, Real.logb 2 (1 / effUnit T ∅ m k (z' k)))
      = ∑ k ∈ Z', Real.logb 2 (1 / effUnit T ∅ m k (z' k)) := by
    rw [← Finset.sum_union hdisj, hunion]
  have hcardsum : (Z' ∩ Z).card + (Z' \ Z).card = Z'.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hovpos : 0 < (Z' ∩ Z).card := by
    obtain ⟨k, hk⟩ := hover
    exact Finset.card_pos.2 ⟨k, Finset.mem_inter.2
      ⟨(Finset.mem_inter.1 hk).2, (Finset.mem_inter.1 hk).1⟩⟩
  have hb1 : (∑ k ∈ Z' ∩ Z, Real.logb 2 (1 / effUnit T ∅ m k (z' k)))
      ≤ ((Z' ∩ Z).card : ℝ) * M.card := by
    calc (∑ k ∈ Z' ∩ Z, Real.logb 2 (1 / effUnit T ∅ m k (z' k)))
        ≤ ∑ _k ∈ Z' ∩ Z, (M.card : ℝ) := Finset.sum_le_sum hshared
      _ = ((Z' ∩ Z).card : ℝ) * M.card := by rw [Finset.sum_const, nsmul_eq_mul]
  have hb2 : (∑ k ∈ Z' \ Z, Real.logb 2 (1 / effUnit T ∅ m k (z' k)))
      ≤ ((Z' \ Z).card : ℝ) * M'.card := by
    calc (∑ k ∈ Z' \ Z, Real.logb 2 (1 / effUnit T ∅ m k (z' k)))
        ≤ ∑ _k ∈ Z' \ Z, (M'.card : ℝ) := Finset.sum_le_sum hrest
      _ = ((Z' \ Z).card : ℝ) * M'.card := by rw [Finset.sum_const, nsmul_eq_mul]
  have hMlt : (M.card : ℝ) < (M'.card : ℝ) := by exact_mod_cast hcardlt
  have hovR : (0 : ℝ) < ((Z' ∩ Z).card : ℝ) := by exact_mod_cast hovpos
  have hcardR : ((Z' ∩ Z).card : ℝ) + ((Z' \ Z).card : ℝ) = (Z'.card : ℝ) := by
    exact_mod_cast hcardsum
  rw [← hsum]
  calc (∑ k ∈ Z' ∩ Z, Real.logb 2 (1 / effUnit T ∅ m k (z' k)))
        + ∑ k ∈ Z' \ Z, Real.logb 2 (1 / effUnit T ∅ m k (z' k))
      ≤ ((Z' ∩ Z).card : ℝ) * M.card + ((Z' \ Z).card : ℝ) * M'.card :=
        add_le_add hb1 hb2
    _ < ((Z' ∩ Z).card : ℝ) * M'.card + ((Z' \ Z).card : ℝ) * M'.card := by
        have := mul_lt_mul_of_pos_left hMlt hovR
        linarith
    _ = (M'.card : ℝ) * Z'.card := by rw [← add_mul, hcardR]; ring

/-- **`[UB, Lemma 4]`, cause side.**  `[UB]` states Lemma 4 for both directions
("Similarly, if `φ_c(m,Z) = |M||Z|` then `π_c(Z = z | m) = 1`"); this is the cause half,
with the Bayes selectivity `causeRep` in place of `effRep`. -/
theorem selectivity_eq_one_of_phiC_eq (T : UnitTPM N) (M : Finset (Fin N))
    (m : State N) (C : Finset (Fin N)) (z : State N) (θ : Partition N M C)
    (hpos : 0 < partCauseFwd T C z M m θ)
    (hMcard : 0 < M.card) (hCcard : 0 < C.card)
    (heq : phiCofPartition T C z M m θ = M.card * C.card) :
    causeRep T C z M m = 1 := by
  by_contra hne
  have hsel : causeRep T C z M m < 1 := lt_of_le_of_ne (causeRep_le_one T C z M m) hne
  have hsel0 : 0 ≤ causeRep T C z M m := causeRep_nonneg T C z M m
  have hinf : pos (Real.logb 2 (causeFwd T C z M m / partCauseFwd T C z M m θ))
      ≤ (cutCount M C θ : ℝ) := logb_ratio_le_cutCount_cause T C z M m θ hpos
  have hcut : (cutCount M C θ : ℝ) ≤ (M.card : ℝ) * C.card := by
    exact_mod_cast cutCount_le M C θ
  have hMpos : (0 : ℝ) < (M.card : ℝ) := by exact_mod_cast hMcard
  have hCpos : (0 : ℝ) < (C.card : ℝ) := by exact_mod_cast hCcard
  have hprodpos : (0 : ℝ) < (M.card : ℝ) * C.card := mul_pos hMpos hCpos
  have hlt : phiCofPartition T C z M m θ < (M.card : ℝ) * C.card := by
    calc phiCofPartition T C z M m θ
        ≤ causeRep T C z M m * ((M.card : ℝ) * C.card) :=
          mul_le_mul_of_nonneg_left (hinf.trans hcut) hsel0
      _ < 1 * ((M.card : ℝ) * C.card) := mul_lt_mul_of_pos_right hsel hprodpos
      _ = (M.card : ℝ) * C.card := one_mul _
  rw [heq] at hlt
  exact lt_irrefl _ hlt

/-! ## `[UB, Theorem 2]`, `[UB, Corollary 1]`, and `[UB, Theorem 3]`

These are stated at the MIP (`phiEat`), as in `[UB]`, rather than at an arbitrary
partition, and every set involved is required nonempty.  Both points matter: with `M = ∅`
the hypothesis of Theorem 2 holds with no content, so nonemptiness is needed for the
statement, not only for its proof. -/

/-- The informativeness at the total partition, written as a sum of per-unit terms. -/
lemma phiEofPartition_total_eq {T : UnitTPM N} {M Z : Finset (Fin N)} {m z : State N}
    {θ : Partition N M Z} (hsel : effRep T M m Z z = 1)
    (htot : ∀ k ∈ Z, θ.effPart k = ∅)
    (hpos : ∀ k ∈ Z, 0 < effUnit T ∅ m k (z k)) :
    phiEofPartition T M m Z z θ
      = pos (∑ k ∈ Z, Real.logb 2 (1 / effUnit T ∅ m k (z k))) := by
  rw [phiEofPartition, hsel, one_mul, partEffRep_of_total T m z θ htot]
  congr 1
  have hprod : Real.logb 2 (∏ k ∈ Z, effUnit T ∅ m k (z k))
      = ∑ k ∈ Z, Real.logb 2 (effUnit T ∅ m k (z k)) := by
    unfold Real.logb
    rw [Real.log_prod (fun k hk => (hpos k hk).ne'), Finset.sum_div]
  rw [one_div, Real.logb_inv, hprod, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_div, Real.logb_inv]

/-- **`[UB, S3 Appendix, Lemma 7]`**, at the level of partitions.

If `(M, Z)` attains its bound `|M||Z|` and `M ⊂ M'` with `Z ∩ Z'` nonempty, then `(M', Z')`
cannot attain `|M'||Z'|`: the units shared with `Z` are already pinned by the smaller `M`,
so they contribute at most `|M| < |M'|` each to the informativeness.

This is `[UB, S3, Lemma 7]`, and with `attains_max_iff` and `informativeness_split_lt` in
hand the assembly is direct. -/
theorem theorem_two_partition {T : UnitTPM N} {M Mbar Z Zbar : Finset (Fin N)}
    {m z zbar : State N} {θ : Partition N M Z} {ϑ : Partition N Mbar Zbar}
    (hZ : Z.Nonempty) (hZbar : Zbar.Nonempty)
    (hmax : phiEofPartition T M m Z z θ = M.card * Z.card)
    (hsub : M ⊂ Mbar) (hover : (Z ∩ Zbar).Nonempty) :
    phiEofPartition T Mbar m Zbar zbar ϑ < Mbar.card * Zbar.card := by
  refine lt_of_le_of_ne (theorem_one' T Mbar m Zbar zbar ϑ) ?_
  intro hmax'
  obtain ⟨hsel, htot, hdet⟩ := attains_max_iff hZ hmax
  obtain ⟨hsel', htot', hdet'⟩ := attains_max_iff hZbar hmax'
  -- every unit of `Zbar` has positive unconstrained probability,
  -- by the `2 ^ (-|Mbar|)` bound
  have hpos' : ∀ k ∈ Zbar, 0 < effUnit T ∅ m k (zbar k) := by
    intro k hk
    have hge := uncEffUnit_ge_of_effUnit_eq_one T Mbar m k (zbar k) (hdet' k hk)
    have : (0 : ℝ) < ((2 : ℝ) ^ Mbar.card)⁻¹ := by positivity
    linarith
  have hsplit : (∑ k ∈ Zbar, Real.logb 2 (1 / effUnit T ∅ m k (zbar k)))
      < (Mbar.card : ℝ) * Zbar.card := by
    exact informativeness_split_lt hsub hover hdet hdet'
  have hval := phiEofPartition_total_eq hsel' htot' hpos'
  rw [hval] at hmax'
  have hle : pos (∑ k ∈ Zbar, Real.logb 2 (1 / effUnit T ∅ m k (zbar k)))
      ≤ (Mbar.card : ℝ) * Zbar.card := by
    refine pos_le ?_ hsplit.le
    exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  -- the positive part is attained by the strict bound, contradiction
  rcases max_cases (0 : ℝ) (∑ k ∈ Zbar, Real.logb 2 (1 / effUnit T ∅ m k (zbar k))) with
    ⟨he, -⟩ | ⟨he, -⟩
  · rw [pos, he] at hmax'
    have hMZbar : (0 : ℝ) < (Mbar.card : ℝ) * Zbar.card := by
      have hM'pos : 0 < Mbar.card :=
        lt_of_le_of_lt (Nat.zero_le _) (Finset.card_lt_card hsub)
      have h1 : (0 : ℝ) < (Mbar.card : ℝ) := by exact_mod_cast hM'pos
      have h2 : (0 : ℝ) < (Zbar.card : ℝ) := by
        have := Finset.card_pos.2 hZbar
        exact_mod_cast this
      exact mul_pos h1 h2
    rw [← hmax'] at hMZbar
    exact lt_irrefl _ hMZbar
  · rw [pos, he] at hmax'
    rw [hmax'] at hsplit
    exact lt_irrefl _ hsplit

/-- **`[UB, S3 Appendix, Lemma 8]`**: the *other* nesting direction of `[UB, Theorem 2]`.

If `(M, Z)` attains its bound and `M̄ ⊂ M` (the sub-mechanism this time) with overlapping
purviews, then `(M̄, Z̄)` cannot attain its own bound either.  `[UB]` derives this from
Lemma 7 by contradiction, and so do we: were `(M̄, Z̄)` to attain, Lemma 7 applied with the
roles exchanged would deny the maximum to `(M, Z)`. -/
theorem theorem_two_partition_sub {T : UnitTPM N} {M Mbar Z Zbar : Finset (Fin N)}
    {m z zbar : State N} {θ : Partition N M Z} {ϑ : Partition N Mbar Zbar}
    (hZ : Z.Nonempty) (hZbar : Zbar.Nonempty)
    (hmax : phiEofPartition T M m Z z θ = M.card * Z.card)
    (hsub : Mbar ⊂ M) (hover : (Z ∩ Zbar).Nonempty) :
    phiEofPartition T Mbar m Zbar zbar ϑ < Mbar.card * Zbar.card := by
  refine lt_of_le_of_ne (theorem_one' T Mbar m Zbar zbar ϑ) ?_
  intro hmax'
  have hlt := theorem_two_partition (M := Mbar) (Mbar := M) (Z := Zbar) (Zbar := Z)
    (z := zbar) (zbar := z) (θ := ϑ) (ϑ := θ) hZbar hZ hmax' hsub
    (by rwa [Finset.inter_comm])
  rw [hmax] at hlt
  exact lt_irrefl _ hlt

/-- **`[UB, Theorem 2]`** in full, at the level of partitions: *both* nesting directions,
exactly as the paper states it (`M̄ ⊂ M` **or** `M̄ ⊃ M`, with overlapping purviews). -/
theorem theorem_two_partition_both {T : UnitTPM N} {M Mbar Z Zbar : Finset (Fin N)}
    {m z zbar : State N} {θ : Partition N M Z} {ϑ : Partition N Mbar Zbar}
    (hZ : Z.Nonempty) (hZbar : Zbar.Nonempty)
    (hmax : phiEofPartition T M m Z z θ = M.card * Z.card)
    (hnest : M ⊂ Mbar ∨ Mbar ⊂ M) (hover : (Z ∩ Zbar).Nonempty) :
    phiEofPartition T Mbar m Zbar zbar ϑ < Mbar.card * Zbar.card := by
  rcases hnest with h | h
  · exact theorem_two_partition hZ hZbar hmax h hover
  · exact theorem_two_partition_sub hZ hZbar hmax h hover

/-- A supremum over a nonempty finite set is attained. -/
lemma exists_mem_of_sup'OrZero_eq {α : Type*} {s : Finset α} {f : α → ℝ} {c : ℝ}
    (hs : s.Nonempty) (h : sup'OrZero s f = c) : ∃ x ∈ s, f x = c := by
  rw [sup'OrZero] at h
  rw [dif_pos hs] at h
  obtain ⟨x, hx, hfx⟩ := Finset.exists_mem_eq_sup' hs f
  exact ⟨x, hx, by rw [← hfx, h]⟩

/-- **`[UB, Theorem 2]`** (inter-order constraints), at the minimum information partition,
in the paper's full form.

Stated exactly as printed: the conclusion is the strict inequality
`φ_e(m̄, Z̄) < |M̄||Z̄|`, and `hnest` is the paper's two alternatives `M̄ ⊂ M` and
`M̄ ⊃ M` (the latter written `M ⊂ M̄`), whose shared side condition `Z ∩ Z̄ ≠ ∅` is
`hover`.  Mechanisms of different orders can be maximally integrated only over
**disjoint** purviews. -/
theorem theorem_two {T : UnitTPM N} {M Mbar Z Zbar : Finset (Fin N)}
    {m z zbar : State N} [Fact M.Nonempty] [Fact Mbar.Nonempty]
    (hZ : Z.Nonempty) (hZbar : Zbar.Nonempty)
    (hmax : phiEat T M m Z z = M.card * Z.card)
    (hnest : Mbar ⊂ M ∨ M ⊂ Mbar) (hover : (Z ∩ Zbar).Nonempty) :
    phiEat T Mbar m Zbar zbar < Mbar.card * Zbar.card := by
  refine lt_of_le_of_ne (phiEat_le T Mbar m Zbar zbar) ?_
  intro hmax'
  obtain ⟨θ, -, hθ⟩ :=
    exists_mem_of_sup'OrZero_eq (argminSet_nonempty (normalizedPhi T M m Z z)) hmax
  obtain ⟨ϑ, -, hϑ⟩ :=
    exists_mem_of_sup'OrZero_eq
      (argminSet_nonempty (normalizedPhi T Mbar m Zbar zbar)) hmax'
  have hlt := theorem_two_partition_both (θ := θ) (ϑ := ϑ) (z := z) (zbar := zbar)
    hZ hZbar hθ hnest.symm hover
  rw [hϑ] at hlt
  exact lt_irrefl _ hlt

/-- **`[UB, Corollary 1]`**, in the reading of `[UB, Table 3]`'s "Bound I" row.

`[UB]` states Corollary 1 as "all the distinctions in a system cannot be maximally
integrated, if the system is composed of more than one unit", and derives it from
Theorem 2.  What Theorem 2 yields is the non-achievability of `[UB, Table 3]`'s
**Bound I** (`∀ M ⊆ S, φ_d = |M||S|` with `Z*_e = Z*_c = S`), which is what is proved
here: no `T` and `m` make every nonempty `M ⊆ S` attain `|M||S|` over the whole system as
purview, once `1 < |S|`.  Each mechanism may choose its own maximal state.

The fully general statement -- every mechanism maximal over its *own* purview -- rests on
more than Theorem 2: with `S = {a,b}`, the assignment `Z(S) = {a}`,
`Z({a}) = Z({b}) = {b}` leaves every nested pair with disjoint purviews, so no instance of
Theorem 2 applies.  `[UB]` closes that case by the counting remark that there are
fewer disjoint purview sets than mechanisms, which we do not formalize. -/
theorem corollary_one_boundI {T : UnitTPM N} {S : Finset (Fin N)} (hS : 1 < S.card)
    (m : State N) :
    ¬ (∀ M : Finset (Fin N), M.Nonempty → M ⊆ S →
        ∃ z : State N, phiEat T M m S z = M.card * S.card) := by
  intro hall
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hS
  have hSne : S.Nonempty := ⟨a, ha⟩
  have hsub : ({a} : Finset (Fin N)) ⊆ S := Finset.singleton_subset_iff.2 ha
  have hssub : ({a} : Finset (Fin N)) ⊂ S :=
    (Finset.ssubset_iff_of_subset hsub).2 ⟨b, hb, by simpa using Ne.symm hab⟩
  haveI : Fact ({a} : Finset (Fin N)).Nonempty := ⟨Finset.singleton_nonempty a⟩
  haveI : Fact S.Nonempty := ⟨hSne⟩
  obtain ⟨z₁, h1⟩ := hall {a} (Finset.singleton_nonempty a) hsub
  obtain ⟨z₂, h2⟩ := hall S hSne (Finset.Subset.refl S)
  have hlt : phiEat T S m S z₂ < (S.card : ℝ) * S.card :=
    theorem_two (M := {a}) (Mbar := S) (Z := S) (Zbar := S) (z := z₁) (zbar := z₂)
      hSne hSne h1 (Or.inr hssub) (by rwa [Finset.inter_self])
  rw [h2] at hlt
  exact lt_irrefl _ hlt

/-- **Step 1 of `[UB, Theorem 3]`**, proved.  `[UB, S3 §3]` opens its proof with
"achieving the maximum value is only possible if the MIP is the complete partition".
That step is exactly `attains_max_iff`: attaining `|M||Z|` forces the minimising partition
to retain *no* mechanism unit at any purview unit. -/
theorem complete_of_phiEat_eq {T : UnitTPM N} {M Z : Finset (Fin N)} {m z : State N}
    [Fact M.Nonempty] (hZ : Z.Nonempty)
    (hmax : phiEat T M m Z z = (M.card : ℝ) * Z.card) :
    ∃ θ : Partition N M Z, θ ∈ argminSet (normalizedPhi T M m Z z) ∧
      ∀ k ∈ Z, θ.effPart k = ∅ := by
  obtain ⟨θ, hmem, hθ⟩ :=
    exists_mem_of_sup'OrZero_eq (argminSet_nonempty (normalizedPhi T M m Z z)) hmax
  exact ⟨θ, hmem, (attains_max_iff hZ hθ).2.1⟩

/-- **`[UB, Theorem 3]`, reduced to its analytic core** — and this reduction *is* proved.

`[UB, S3 §3]` finishes with "since not having the self connections in the cut for
`1 < K < N` gives us a smaller normalized partitioned informativeness, the complete
partition cannot be the MIP".  Phrased as a hypothesis: if *some* partition `ϑ` beats
every complete partition on `normalizedPhi`, the bound cannot be attained.

`theorem_three` reaches the same conclusion with the self-connection partition, but by a
shorter route -- it contradicts `mem_argminSet` directly -- so it does not call this
lemma; the reduction is recorded here on its own. -/
theorem theorem_three_of_exists_better {T : UnitTPM N} {M Z : Finset (Fin N)}
    {m z : State N} [Fact M.Nonempty] (hZ : Z.Nonempty) (ϑ : Partition N M Z)
    (hbetter : ∀ θ : Partition N M Z, (∀ k ∈ Z, θ.effPart k = ∅) →
      normalizedPhi T M m Z z ϑ < normalizedPhi T M m Z z θ) :
    phiEat T M m Z z ≠ (M.card : ℝ) * Z.card := by
  intro hmax
  obtain ⟨θ, hmem, hcomplete⟩ := complete_of_phiEat_eq hZ hmax
  exact absurd (hbetter θ hcomplete) (not_lt.2 (mem_argminSet.1 hmem ϑ))

/-! ### `[UB, Theorem 3]`: the self-connection partition and leaked determinism -/

/-- The partition in which every purview unit keeps exactly its own self-connection:
blocks `{({k}, {k}) : k ∈ M}`.  It is disintegrating (`proper`) precisely because
`1 < |M|`: no block carries the whole mechanism. -/
def selfPartition (M : Finset (Fin N)) (hM : 1 < M.card) : Partition N M M where
  blocks := M.image fun k => ({k}, {k})
  mech_subset := by
    intro b hb
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hb
    simpa using hk
  purv_subset := by
    intro b hb
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hb
    simpa using hk
  mech_disjoint := by
    intro b hb b' hb' hne
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 hb'
    have hkk : k ≠ k' := fun h => hne (by rw [h])
    simpa [Finset.disjoint_singleton] using hkk
  purv_disjoint := by
    intro b hb b' hb' hne
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 hb'
    have hkk : k ≠ k' := fun h => hne (by rw [h])
    simpa [Finset.disjoint_singleton] using hkk
  mech_cover := by
    intro i hi
    exact ⟨({i}, {i}), Finset.mem_image.2 ⟨i, hi, rfl⟩, Finset.mem_singleton_self i⟩
  purv_cover := by
    intro k hk
    exact ⟨({k}, {k}), Finset.mem_image.2 ⟨k, hk, rfl⟩, Finset.mem_singleton_self k⟩
  proper := by
    intro b hb hbM
    exfalso
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hb
    have h1 : M.card = 1 := by
      rw [← hbM]
      exact Finset.card_singleton k
    omega

lemma selfPartition_effPart {M : Finset (Fin N)} (hM : 1 < M.card) {k : Fin N}
    (hk : k ∈ M) : (selfPartition M hM).effPart k = {k} :=
  (selfPartition M hM).effPart_eq (Finset.mem_image.2 ⟨k, hk, rfl⟩)
    (Finset.mem_singleton_self k)

lemma selfPartition_cutCount {M : Finset (Fin N)} (hM : 1 < M.card) :
    cutCount M M (selfPartition M hM) = M.card * (M.card - 1) := by
  rw [cutCount,
    Finset.sum_congr rfl (fun k hk => by
      rw [selfPartition_effPart hM hk, Finset.card_singleton]),
    Finset.sum_const, smul_eq_mul]

/-- **Determinism leaks across mechanisms.**  If every size-`K` mechanism at the state
`m` deterministically specifies some maximal effect state, and unit `k`'s specified value
at the state `m` itself is `b`, then `k` fires `b` with probability `1` on the whole
fibre of *any* size-`K` mechanism containing `k` — the specified values must agree
because the fibres share the state `m` itself, and two Booleans cannot both have
probability `1`. -/
lemma prob_eq_one_on_other_fibre (T : UnitTPM N) {K : ℕ} (m : State N)
    (hdet : ∀ M' : Finset (Fin N), M'.card = K →
      ∃ w ∈ maxEffStates T M' m M', effRep T M' m M' w = 1)
    {M' : Finset (Fin N)} (hM' : M'.card = K) {k : Fin N} (hk : k ∈ M')
    {b : Bool} (hb : T.prob k m b = 1) :
    ∀ s ∈ agree M' m, T.prob k s b = 1 := by
  obtain ⟨w, -, h1⟩ := hdet M' hM'
  have h2 : effUnit T M' m k (w k) = 1 :=
    effUnit_eq_one_of_effRep_eq_one T M' m M' w h1 k hk
  have h3 : ∀ s ∈ agree M' m, T.prob k s (w k) = 1 :=
    prob_eq_one_of_effUnit_eq_one T M' m k (w k) h2
  have h4 : T.prob k m (w k) = 1 := h3 m (mem_agree.2 fun j _ => rfl)
  have hwk : w k = b := by
    by_contra hne
    have hnorm := T.normalized k m
    cases hbv : b with
    | false =>
      rw [hbv] at hb hne
      have hwt : w k = true := by
        cases hwv : w k with
        | false => exact absurd hwv hne
        | true => rfl
      rw [hwt] at h4
      rw [hb, h4] at hnorm
      norm_num at hnorm
    | true =>
      rw [hbv] at hb hne
      have hwf : w k = false := by
        cases hwv : w k with
        | false => rfl
        | true => exact absurd hwv hne
      rw [hwf] at h4
      rw [h4, hb] at hnorm
      norm_num at hnorm
  rw [← hwk]
  exact h3

/-- **The leaked-determinism bound**, the analytic heart of `[UB, Theorem 3]`.  Under the
theorem's hypothesis with `1 < K < N`, once the mechanism `M` (`|M| = K`) fully specifies
unit `k ∈ M`, the *single-unit* marginal for `k` strictly exceeds `2^(1-K)` — because a
neighbouring size-`K` mechanism (swap one unit of `M` for an outside unit) forces at
least one deterministic state **outside** `M`'s own fibre.  One extra state is all the
strictness the theorem needs; the binomial estimates of `[UB, S3 Appendix §3, Eqs 18–21]`
compute the exact extremal value but are not required for the conclusion. -/
lemma one_lt_effUnit_singleton_mul (T : UnitTPM N) {K : ℕ} (hK1 : 1 < K) (hKN : K < N)
    (m : State N)
    (hdet : ∀ M' : Finset (Fin N), M'.card = K →
      ∃ w ∈ maxEffStates T M' m M', effRep T M' m M' w = 1)
    {M : Finset (Fin N)} (hM : M.card = K) {k : Fin N} (hk : k ∈ M)
    {b : Bool} (hb1 : effUnit T M m k b = 1) :
    1 < effUnit T {k} m k b * 2 ^ (K - 1) := by
  -- determinism on our own fibre, and at the state `m` itself
  have hProbM : ∀ s ∈ agree M m, T.prob k s b = 1 :=
    prob_eq_one_of_effUnit_eq_one T M m k b hb1
  have hbm : T.prob k m b = 1 := hProbM m (mem_agree.2 fun j _ => rfl)
  -- a neighbouring size-K mechanism through k: swap i₀ ∈ M for j₀ ∉ M
  have hex : ∃ i₀ ∈ M, i₀ ≠ k := by
    obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.1 (show 1 < M.card by omega)
    by_cases hak : a = k
    · exact ⟨c, hc, fun h => hac (by rw [hak, h])⟩
    · exact ⟨a, ha, hak⟩
  obtain ⟨i₀, hi₀M, hi₀k⟩ := hex
  have hcompl : Mᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin, hM]
    omega
  obtain ⟨j₀, hj₀c⟩ := hcompl
  have hj₀ : j₀ ∉ M := Finset.mem_compl.1 hj₀c
  have hj₀e : j₀ ∉ M.erase i₀ := fun h => hj₀ (Finset.mem_of_mem_erase h)
  have hM''card : (insert j₀ (M.erase i₀)).card = K := by
    rw [Finset.card_insert_of_notMem hj₀e, Finset.card_erase_of_mem hi₀M, hM]
    omega
  have hkM'' : k ∈ insert j₀ (M.erase i₀) :=
    Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨Ne.symm hi₀k, hk⟩)
  have hfibre : ∀ s ∈ agree (insert j₀ (M.erase i₀)) m, T.prob k s b = 1 :=
    prob_eq_one_on_other_fibre T m hdet hM''card hkM'' hbm
  -- the extra state: `m` flipped at i₀
  have hi₀ne : ∀ j, j ≠ i₀ → Function.update m i₀ (!(m i₀)) j = m j := fun j hj =>
    Function.update_of_ne hj _ _
  have hs'M'' : Function.update m i₀ (!(m i₀)) ∈ agree (insert j₀ (M.erase i₀)) m := by
    rw [mem_agree]
    intro j hj
    refine hi₀ne j ?_
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact fun h => hj₀ (h ▸ hi₀M)
    · exact Finset.ne_of_mem_erase hj
  have hs'prob : T.prob k (Function.update m i₀ (!(m i₀))) b = 1 :=
    hfibre _ hs'M''
  have hs'notM : Function.update m i₀ (!(m i₀)) ∉ agree M m := by
    rw [mem_agree]
    intro hcon
    have h5 := hcon i₀ hi₀M
    rw [Function.update_self] at h5
    exact (Bool.not_ne_self (m i₀)) h5
  have hs'k : Function.update m i₀ (!(m i₀)) ∈ agree ({k} : Finset (Fin N)) m := by
    rw [mem_agree]
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    exact hi₀ne _ (Ne.symm hi₀k)
  -- the singleton fibre contains the whole M-fibre plus the extra state
  have hsub : insert (Function.update m i₀ (!(m i₀))) (agree M m)
      ⊆ agree ({k} : Finset (Fin N)) m := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact hs'k
    · exact agree_subset_agree (Finset.singleton_subset_iff.2 hk) m hs
  have hsum : ((agree M m).card : ℝ) + 1
      ≤ ∑ s ∈ agree ({k} : Finset (Fin N)) m, T.prob k s b := by
    have h1 : ∑ s ∈ insert (Function.update m i₀ (!(m i₀))) (agree M m), T.prob k s b
        = 1 + (agree M m).card := by
      rw [Finset.sum_insert hs'notM, hs'prob,
        Finset.sum_congr rfl (fun s hs => hProbM s hs), Finset.sum_const, nsmul_eq_mul,
        mul_one]
    calc ((agree M m).card : ℝ) + 1
        = ∑ s ∈ insert (Function.update m i₀ (!(m i₀))) (agree M m), T.prob k s b := by
          rw [h1]; ring
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun s _ _ => T.nonneg k s b
  -- rewrite the cards and conclude
  have hcards : ((agree ({k} : Finset (Fin N)) m).card : ℝ) = 2 ^ (N - 1) := by
    rw [card_agree, Finset.card_singleton]
    push_cast
    ring
  have hcardM : ((agree M m).card : ℝ) = 2 ^ (N - K) := by
    rw [card_agree, hM]
    push_cast
    ring
  have hpos1 : (0 : ℝ) < 2 ^ (N - 1) := by positivity
  have heff : ((2 : ℝ) ^ (N - K) + 1) / 2 ^ (N - 1) ≤ effUnit T {k} m k b := by
    rw [effUnit, hcards]
    gcongr
    rw [← hcardM]
    linarith [hsum]
  have hexp : (2 : ℝ) ^ (N - K) * 2 ^ (K - 1) = 2 ^ (N - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hpk : (0 : ℝ) < 2 ^ (K - 1) := by positivity
  have hstep : (2 : ℝ) ^ (N - 1) < ((2 : ℝ) ^ (N - K) + 1) * 2 ^ (K - 1) := by
    rw [add_mul, hexp, one_mul]
    linarith
  calc (1 : ℝ) < ((2 : ℝ) ^ (N - K) + 1) * 2 ^ (K - 1) / 2 ^ (N - 1) :=
        (one_lt_div hpos1).2 hstep
    _ = ((2 : ℝ) ^ (N - K) + 1) / 2 ^ (N - 1) * 2 ^ (K - 1) := by ring
    _ ≤ effUnit T {k} m k b * 2 ^ (K - 1) := mul_le_mul_of_nonneg_right heff hpk.le

/-- **`[UB, Theorem 3]`** (intra-order constraints), **proved**.  In a system of `N`
units, if at the current state `m` every mechanism of a fixed size `K` with `1 < K < N`
fully specifies a maximal effect state over its own units (`π_e(Z = z' | m) = 1` for all
`M` with `|M| = K` and `Z = M`, `[UB, §2.1.3]`), then none of them attains its maximum
integrated effect information `|M|²`.

The hypothesis is per-state, exactly as in the paper: quantifying it over *all* states
would be unsatisfiable for the paper's own extremal TPM (`[UB, S3, Eqs 18, 20]`).  That
TPM is deterministic at *every* state (Eqs 18 and 20 between them fix `p(Z_n = 0 | s)` for
all `s`); what holds only at a few states is the *mechanism-level* hypothesis, because a
size-`K` mechanism's marginalization fibre straddles the two regions.  Verified numerically
in `test/thm3test.py`, where the per-state hypothesis holds at 2 of 8 states for
`(N,K) = (3,2)` (all-off and all-on) and 6 of 16 for `(4,3)`, and where this conclusion and
the `one_lt_effUnit_singleton_mul` bound check out for
`(N, K) ∈ {(3,2), (4,2), (4,3), (5,2), (5,3)}`.

The proof follows `[UB, S3 Appendix §3]`'s outline — "achieving the maximum value is
only possible if the MIP is the complete partition", but a partition sparing the
self-connections beats every complete partition on `normalizedPhi` — with one
simplification: instead of the appendix's binomial estimates (its Eqs 18–21, which
compute the extremal TPM's exact values), `one_lt_effUnit_singleton_mul` obtains the
required *strict* inequality from a single extra deterministic state, leaked into the
singleton fibre by a neighbouring size-`K` mechanism.  That is why the result
runs out at `K = N` (no neighbouring mechanism exists — nothing leaks) and at `K = 1` (the
self-connection partition is no longer disintegrating). -/
theorem theorem_three (T : UnitTPM N) {K : ℕ} (hK1 : 1 < K) (hKN : K < N) (m : State N)
    (hdet : ∀ M' : Finset (Fin N), M'.card = K →
      ∃ w ∈ maxEffStates T M' m M', effRep T M' m M' w = 1)
    {M : Finset (Fin N)} (hM : M.card = K) {z : State N}
    (_hz : z ∈ maxEffStates T M m M) :
    phiEat T M m M z ≠ (M.card : ℝ) ^ 2 := by
  intro hmax
  have hMcard1 : 1 < M.card := by omega
  have hMne : M.Nonempty := Finset.card_pos.1 (by omega)
  haveI : Fact M.Nonempty := ⟨hMne⟩
  have hmax' : phiEat T M m M z = (M.card : ℝ) * M.card := by rw [hmax]; ring
  obtain ⟨θ, hθmem, hθval⟩ :=
    exists_mem_of_sup'OrZero_eq (argminSet_nonempty (normalizedPhi T M m M z)) hmax'
  obtain ⟨heffRep, -, hunits⟩ := attains_max_iff hMne hθval
  -- every factor of the self-partition's repertoire strictly exceeds 2^(1-K)
  have hfac : ∀ k ∈ M, 1 < effUnit T {k} m k (z k) * 2 ^ (K - 1) := fun k hk =>
    one_lt_effUnit_singleton_mul T hK1 hKN m hdet hM hk (hunits k hk)
  have hprod : 1 < (∏ k ∈ M, effUnit T {k} m k (z k)) * 2 ^ (K * (K - 1)) := by
    have h1 : 1 < ∏ k ∈ M, (effUnit T {k} m k (z k) * 2 ^ (K - 1)) := by
      obtain ⟨k₀, hk₀⟩ := hMne
      rw [← Finset.mul_prod_erase M _ hk₀]
      have hrest : (1 : ℝ) ≤ ∏ k ∈ M.erase k₀, (effUnit T {k} m k (z k) * 2 ^ (K - 1)) := by
        calc (1 : ℝ) = ∏ _k ∈ M.erase k₀, (1 : ℝ) := (Finset.prod_const_one).symm
          _ ≤ _ := Finset.prod_le_prod (fun i _ => zero_le_one)
              (fun i hi => (hfac i (Finset.mem_of_mem_erase hi)).le)
      have hmul := mul_lt_mul_of_pos_right (hfac k₀ hk₀)
        (lt_of_lt_of_le zero_lt_one hrest)
      rw [one_mul] at hmul
      linarith
    rwa [Finset.prod_mul_distrib, Finset.prod_const, hM, ← pow_mul,
      Nat.mul_comm (K - 1) K] at h1
  -- the self-partition's data
  have hP : partEffRep T M m M z (selfPartition M hMcard1)
      = ∏ k ∈ M, effUnit T {k} m k (z k) := by
    rw [partEffRep]
    exact Finset.prod_congr rfl fun k hk => by rw [selfPartition_effPart hMcard1 hk]
  have hcut : cutCount M M (selfPartition M hMcard1) = K * (K - 1) := by
    rw [selfPartition_cutCount hMcard1, hM]
  have hPpos : 0 < partEffRep T M m M z (selfPartition M hMcard1) := by
    have h2c : (0 : ℝ) < 2 ^ (K * (K - 1)) := by positivity
    rw [hP]
    by_contra hle
    push_neg at hle
    nlinarith [hprod, h2c]
  -- φ at the self-partition is strictly below its cut count …
  have hKK : (0 : ℝ) < ((K * (K - 1) : ℕ) : ℝ) := by
    have h0 : 0 < K * (K - 1) := by
      have h1 : 1 ≤ K - 1 := by omega
      calc 0 < 1 * 1 := by norm_num
        _ ≤ K * (K - 1) := Nat.mul_le_mul (by omega) h1
    exact_mod_cast h0
  have hφself : phiEofPartition T M m M z (selfPartition M hMcard1)
      < ((K * (K - 1) : ℕ) : ℝ) := by
    rw [phiEofPartition, heffRep, one_mul]
    have harg : (1 : ℝ) / partEffRep T M m M z (selfPartition M hMcard1)
        < 2 ^ (K * (K - 1)) := by
      rw [div_lt_iff₀ hPpos]
      calc (1 : ℝ) < (∏ k ∈ M, effUnit T {k} m k (z k)) * 2 ^ (K * (K - 1)) := hprod
        _ = 2 ^ (K * (K - 1)) * partEffRep T M m M z (selfPartition M hMcard1) := by
            rw [hP]; ring
    have hlog : Real.logb 2 (1 / partEffRep T M m M z (selfPartition M hMcard1))
        < ((K * (K - 1) : ℕ) : ℝ) := by
      have h1 : Real.logb 2 (1 / partEffRep T M m M z (selfPartition M hMcard1))
          < Real.logb 2 ((2 : ℝ) ^ (K * (K - 1))) :=
        Real.logb_lt_logb (b := 2) (by norm_num) (one_div_pos.2 hPpos) harg
      rwa [Real.logb_pow, Real.logb_self_eq_one (b := 2) (by norm_num), mul_one] at h1
    rw [pos]
    exact max_lt hKK hlog
  -- … so its normalized φ is below 1, and the MIP's is too
  have hnormself : normalizedPhi T M m M z (selfPartition M hMcard1) < 1 := by
    rw [normalizedPhi, hcut]
    exact (div_lt_one hKK).2 hφself
  have hθlt1 : normalizedPhi T M m M z θ < 1 :=
    lt_of_le_of_lt (mem_argminSet.1 hθmem (selfPartition M hMcard1)) hnormself
  -- contradiction with attaining |M|²
  have hcutθpos : (0 : ℝ) < (cutCount M M θ : ℝ) := by
    exact_mod_cast cutCount_pos hMne θ
  have hcutθle : (cutCount M M θ : ℝ) ≤ (M.card : ℝ) * M.card := by
    exact_mod_cast cutCount_le M M θ
  have hφθ : phiEofPartition T M m M z θ
      = normalizedPhi T M m M z θ * (cutCount M M θ : ℝ) := by
    rw [normalizedPhi, div_mul_cancel₀ _ hcutθpos.ne']
  have hlt : phiEofPartition T M m M z θ < (M.card : ℝ) * M.card := by
    rw [hφθ]
    calc normalizedPhi T M m M z θ * (cutCount M M θ : ℝ)
        < 1 * (cutCount M M θ : ℝ) := mul_lt_mul_of_pos_right hθlt1 hcutθpos
      _ = (cutCount M M θ : ℝ) := one_mul _
      _ ≤ (M.card : ℝ) * M.card := hcutθle
  rw [hθval] at hlt
  exact lt_irrefl _ hlt

/-- **`[UB, Theorem 3]`, strict form.**  The source states the conclusion as a strict
inequality; `theorem_three` gives `≠` and `phiEat_le` supplies `≤`, so the two combine to
the printed statement. -/
theorem theorem_three_lt (T : UnitTPM N) {K : ℕ} (hK1 : 1 < K) (hKN : K < N) (m : State N)
    (hdet : ∀ M' : Finset (Fin N), M'.card = K →
      ∃ w ∈ maxEffStates T M' m M', effRep T M' m M' w = 1)
    {M : Finset (Fin N)} (hM : M.card = K) {z : State N}
    (hz : z ∈ maxEffStates T M m M) :
    phiEat T M m M z < (M.card : ℝ) ^ 2 := by
  refine lt_of_le_of_ne ?_ (theorem_three T hK1 hKN m hdet hM hz)
  have h := phiEat_le T M m M z
  calc phiEat T M m M z ≤ (M.card : ℝ) * M.card := h
    _ = (M.card : ℝ) ^ 2 := by ring


/-! ## Non-vacuity

The statements above are only worth anything if their hypotheses are satisfiable.  In
particular `theorem_one` assumes `0 < partEffRep`, and a `Distinction` bundles several
positivity conditions.  We exhibit witnesses for both. -/

/-- The maximally noisy system: every unit is an independent fair coin. -/
noncomputable def coinTPM (N : ℕ) : UnitTPM N where
  prob := fun _ _ _ => 1 / 2
  nonneg := by intro i s b; norm_num
  normalized := by intro i s; norm_num

lemma coin_effUnit (N : ℕ) (M : Finset (Fin N)) (m : State N) (i : Fin N) (b : Bool) :
    effUnit (coinTPM N) M m i b = 1 / 2 := by
  have hc : ((agree M m).card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (card_agree_pos M m).ne'
  rw [effUnit]
  simp only [coinTPM, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- The hypothesis `0 < partEffRep` of `theorem_one` is satisfiable, so the theorem is
not vacuous. -/
lemma coin_partEffRep_pos (N : ℕ) (M Z : Finset (Fin N)) (m z : State N)
    (θ : Partition N M Z) : 0 < partEffRep (coinTPM N) M m Z z θ := by
  rw [partEffRep]
  exact Finset.prod_pos fun k _ => by rw [coin_effUnit]; norm_num

/-- `[UB, Theorem 1]` instantiated at a system for which its hypothesis genuinely
holds. -/
example (N : ℕ) (M Z : Finset (Fin N)) (m z : State N) (θ : Partition N M Z) :
    phiEofPartition (coinTPM N) M m Z z θ ≤ M.card * Z.card :=
  theorem_one _ M m Z z θ (coin_partEffRep_pos N M Z m z θ)

/-- A concrete distinction, witnessing that `Distinction` is inhabited. -/
noncomputable def exDistinction : Distinction 1 where
  mech := {0}
  zc := {(0, true)}
  ze := {(0, true)}
  zc_nonempty := ⟨(0, true), by simp⟩
  ze_nonempty := ⟨(0, true), by simp⟩
  phi := 1
  phi_pos := one_pos

/-- A cause-effect structure with a single distinction and no relations has `Φ = 1`,
witnessing that `Phi` is not identically zero. -/
example :
    Phi ({ distinctions := {exDistinction}
           relations := ∅
           selfRelations := ∅ } : CauseEffectStructure 1) = 1 := by
  simp [Phi, exDistinction]

/-! ### `φ` is not identically zero

This is the sharp non-vacuity check, and it is the one that matters.  `coinTPM` above is
the *least* interesting system: every unit is an independent fair coin, so it constrains
nothing and its `φ` is `0`.  A formalization in which `φ` happened to be identically `0`
would still typecheck and would still satisfy every bound proved here.

The witness below is a single deterministic COPY unit.  Because `Θ(M, Z)` excludes the
no-cut assignment (`Partition.effPart_ne`, from `[IIT4, Eq 38]`), the only partition of
`({0}, {0})` severs the unit's self-connection, the partitioned repertoire drops from `1`
to `1/2`, and `φ` at the MIP is exactly `1`. -/

/-- One deterministic unit that copies its own state. -/
noncomputable def copyTPM : UnitTPM 1 where
  prob := fun _ s b => if b = s 0 then 1 else 0
  nonneg := fun i s b => by by_cases h : b = s 0 <;> simp [h]
  normalized := fun i s => by cases s 0 <;> simp

private lemma fin1_eq (i : Fin 1) : i = 0 := Subsingleton.elim _ _

private lemma univ_fin1_bool : (Finset.univ : Finset (Fin 1 → Bool))
    = {(fun _ => false), (fun _ => true)} := by
  ext s
  simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
  cases h : s 0
  · left; funext i; rw [fin1_eq i]; exact h
  · right; funext i; rw [fin1_eq i]; exact h

private lemma agree_singleton (m : State 1) : agree {0} m = {m} := by
  ext s
  rw [mem_agree, Finset.mem_singleton]
  exact ⟨fun h => funext fun i => by rw [fin1_eq i]; exact h 0 (by simp),
    by rintro rfl j _; rfl⟩

private lemma agree_empty (m : State 1) :
    agree (∅ : Finset (Fin 1)) m = Finset.univ := by
  ext s; simp [mem_agree]

private lemma copy_eff_one (m : State 1) : effUnit copyTPM {0} m 0 (m 0) = 1 := by
  rw [effUnit, agree_singleton, Finset.sum_singleton, Finset.card_singleton]
  simp [copyTPM]

private lemma copy_eff_half (m : State 1) : effUnit copyTPM ∅ m 0 (m 0) = 1 / 2 := by
  rw [effUnit, agree_empty, univ_fin1_bool]
  have hne : (fun _ => false : Fin 1 → Bool) ≠ (fun _ => true) := by
    intro h; simpa using congrFun h 0
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
    Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  cases h : m 0 <;> simp [copyTPM]

/-- Every disintegrating partition of `({0}, {0})` severs the connection:
`effPart_ne` leaves
no other option.  This is exactly what fails without `[IIT4, Eq 38]`'s side condition. -/
private lemma copy_part_empty (θ : Partition 1 {0} {0}) : θ.effPart 0 = ∅ := by
  have h1 : θ.effPart 0 ⊆ {0} := θ.effPart_subset 0
  have h2 : θ.effPart 0 ≠ {0} := θ.effPart_ne (by simp)
  rcases Finset.subset_singleton_iff.1 h1 with h | h
  · exact h
  · exact absurd h h2

private lemma copy_phiE_one (m : State 1) (θ : Partition 1 {0} {0}) :
    phiEofPartition copyTPM {0} m {0} m θ = 1 := by
  have he : effRep copyTPM {0} m {0} m = 1 := by
    rw [effRep, Finset.prod_singleton]; exact copy_eff_one m
  have hpe : partEffRep copyTPM {0} m {0} m θ = 1 / 2 := by
    rw [partEffRep, Finset.prod_singleton, copy_part_empty θ]; exact copy_eff_half m
  rw [phiEofPartition, he, hpe]
  have hdiv : (1 : ℝ) / (1 / 2) = 2 := by norm_num
  rw [hdiv]
  have h2 : Real.logb 2 (2 : ℝ) = 1 := by simp
  rw [h2]
  simp [pos]

/-- **`φ` is not identically zero.**  For the COPY unit, the integrated effect information
at the minimum information partition is exactly `1`. -/
theorem phiEat_copyTPM (m : State 1) : phiEat copyTPM {0} m {0} m = 1 := by
  have : Fact (({0} : Finset (Fin 1))).Nonempty := ⟨⟨0, by simp⟩⟩
  obtain ⟨θ0, hθ0⟩ := argminSet_nonempty (normalizedPhi copyTPM {0} m {0} m)
  refine le_antisymm (sup'OrZero_le zero_le_one fun θ _ => (copy_phiE_one m θ).le) ?_
  calc (1 : ℝ) = phiEofPartition copyTPM {0} m {0} m θ0 := (copy_phiE_one m θ0).symm
    _ ≤ _ := le_sup'OrZero hθ0

private lemma copy_causePart_empty (θ : Partition 1 {0} {0}) : θ.causePart 0 = ∅ := by
  have h1 : θ.causePart 0 ⊆ {0} := θ.causePart_subset 0
  rcases Finset.subset_singleton_iff.1 h1 with h | h
  · exact h
  · -- a block carrying the whole purview would have to carry the whole mechanism,
    -- which `proper` forbids
    exfalso
    obtain ⟨b, hb, hmem⟩ := θ.mech_cover 0 (by simp)
    have hb2 : b.2 = {0} := by
      have hsub : b.2 ⊆ {0} := θ.purv_subset b hb
      rcases Finset.subset_singleton_iff.1 hsub with h0 | h0
      · exfalso
        have : θ.causePart 0 = ∅ := by
          rw [θ.causePart_eq hb hmem, h0]
        rw [this] at h
        exact absurd h.symm (Finset.singleton_ne_empty 0)
      · exact h0
    have hb1 : b.1 = {0} := by
      have hsub : b.1 ⊆ {0} := θ.mech_subset b hb
      rcases Finset.subset_singleton_iff.1 hsub with h0 | h0
      · rw [h0] at hmem; exact absurd hmem (Finset.notMem_empty 0)
      · exact h0
    have := θ.proper b hb hb1
    rw [hb2] at this
    exact absurd this (Finset.singleton_ne_empty 0)

private lemma copy_causeFwd_one (m : State 1) : causeFwd copyTPM {0} m {0} m = 1 := by
  rw [causeFwd, effRep, Finset.prod_singleton]; exact copy_eff_one m

private lemma copy_uncCauseFwd_half (m : State 1) :
    uncCauseFwd copyTPM {0} {0} m = 1 / 2 := by
  have hz : ∀ z : State 1, causeFwd copyTPM {0} z {0} m
      = if m 0 = z 0 then 1 else 0 := by
    intro z
    rw [causeFwd, effRep, Finset.prod_singleton, effUnit, agree_singleton,
      Finset.sum_singleton, Finset.card_singleton]
    by_cases h : m 0 = z 0 <;> simp [copyTPM, h, eq_comm]
  have hne : (fun _ => false : Fin 1 → Bool) ≠ (fun _ => true) := by
    intro h; simpa using congrFun h 0
  rw [uncCauseFwd, avgOverStates, Finset.sum_congr rfl (fun z _ => hz z), univ_fin1_bool,
    Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  cases h : m 0 <;> norm_num [h]

private lemma copy_causeRep_one (m : State 1) : causeRep copyTPM {0} m {0} m = 1 := by
  rw [causeRep, copy_causeFwd_one, copy_uncCauseFwd_half, Finset.card_singleton]
  norm_num

private lemma copy_phiC_one (m : State 1) (θ : Partition 1 {0} {0}) :
    phiCofPartition copyTPM {0} m {0} m θ = 1 := by
  have hpc : partCauseFwd copyTPM {0} m {0} m θ = 1 / 2 := by
    rw [partCauseFwd, Finset.prod_singleton, copy_causePart_empty θ]
    exact copy_eff_half m
  rw [phiCofPartition, copy_causeRep_one, copy_causeFwd_one, hpc]
  have hdiv : (1 : ℝ) / (1 / 2) = 2 := by norm_num
  rw [hdiv]
  have h2 : Real.logb 2 (2 : ℝ) = 1 := by simp
  rw [h2]
  simp [pos]

/-- **`φ_c` is not identically zero either.**  The cause-side analogue of
`phiEat_copyTPM`: for the COPY unit the integrated *cause* information at the minimum
information partition is also exactly `1`.  Without this, a cause-side instance of the
identically-zero bug recorded above would leave every distinction-level result vacuously
true, since `φ_d` is the minimum of the two directions. -/
theorem phiCat_copyTPM (m : State 1) : phiCat copyTPM {0} m {0} m = 1 := by
  have : Fact (({0} : Finset (Fin 1))).Nonempty := ⟨⟨0, by simp⟩⟩
  obtain ⟨θ0, hθ0⟩ := argminSet_nonempty (normalizedPhiC copyTPM {0} m {0} m)
  refine le_antisymm (sup'OrZero_le zero_le_one fun θ _ => (copy_phiC_one m θ).le) ?_
  calc (1 : ℝ) = phiCofPartition copyTPM {0} m {0} m θ0 := (copy_phiC_one m θ0).symm
    _ ≤ _ := le_sup'OrZero hθ0

private lemma copy_effRep_val (m z : State 1) :
    effRep copyTPM {0} m {0} z = if z 0 = m 0 then 1 else 0 := by
  rw [effRep, Finset.prod_singleton, effUnit, agree_singleton, Finset.sum_singleton,
    Finset.card_singleton]
  by_cases h : z 0 = m 0 <;> simp [copyTPM, h]

private lemma copy_uncEffRep_half (m : State 1) : uncEffRep copyTPM {0} {0} m = 1 / 2 := by
  have hne : (fun _ => false : Fin 1 → Bool) ≠ (fun _ => true) := by
    intro h; simpa using congrFun h 0
  rw [uncEffRep, Finset.sum_congr rfl (fun m' _ => copy_effRep_val m' m), univ_fin1_bool,
    Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
    Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  cases h : m 0 <;> norm_num [h]

private lemma copy_iiE_m (m : State 1) : iiE copyTPM {0} m {0} m = 1 := by
  rw [iiE, copy_effRep_val, if_pos rfl, copy_uncEffRep_half]
  norm_num

private lemma copy_iiE_le (m z : State 1) : iiE copyTPM {0} m {0} z ≤ 1 := by
  by_cases h : z 0 = m 0
  · have hz : z = m := funext fun i => by rw [fin1_eq i]; exact h
    rw [hz, copy_iiE_m]
  · rw [iiE, copy_effRep_val, if_neg h]
    simp

private lemma copy_m_mem_maxEff (m : State 1) : m ∈ maxEffStates copyTPM {0} m {0} := by
  rw [maxEffStates, mem_argmaxSet]
  intro z
  rw [copy_iiE_m]
  exact copy_iiE_le m z

private lemma copy_iiC_m (m : State 1) : iiC copyTPM {0} m {0} m = 1 := by
  rw [iiC, copy_causeRep_one, copy_causeFwd_one, copy_uncCauseFwd_half]
  norm_num

private lemma copy_iiC_le (m z : State 1) : iiC copyTPM {0} m {0} z ≤ 1 := by
  by_cases h : z 0 = m 0
  · have hz : z = m := funext fun i => by rw [fin1_eq i]; exact h
    rw [hz, copy_iiC_m]
  · have hfwd : causeFwd copyTPM {0} z {0} m = 0 := by
      rw [causeFwd, copy_effRep_val, if_neg (fun hc => h hc.symm)]
    rw [iiC, causeRep, hfwd]
    simp

private lemma copy_m_mem_maxCause (m : State 1) :
    m ∈ maxCauseStates copyTPM {0} m {0} := by
  rw [maxCauseStates, mem_argmaxSet]
  intro z
  rw [copy_iiC_m]
  exact copy_iiC_le m z

/-- **A substrate with strictly positive `φ_d`.**  The one-unit COPY substrate has
`φ_d = 1` at its own mechanism and purview, so `[IIT4, Eq 47]` is not identically
zero.

**What this does and does not give.**  It witnesses the `0 < φ_d` conjunct of
`IsDistinctionMech` `[IIT4, Eq 48]` only.  That predicate also demands a congruent
pair of maximal cause and effect purviews, and nothing here shows
`distinctionMechs` is nonempty, nor that `PhiDistinctions` or `Φ` is positive for
any substrate.  Note also that `N = 1` is the one arity at which this development
deliberately differs from PyPhi (`test/singleunit.py`), so the witness cannot be
cross-validated differentially. -/
theorem phiD_copyTPM_pos (m : State 1) : 0 < phiD copyTPM Finset.univ {0} m := by
  have huniv : ({0} : Finset (Fin 1)) ∈ (Finset.univ : Finset (Fin 1)).powerset := by simp
  rw [phiD, lt_min_iff]
  refine ⟨?_, ?_⟩
  · calc (0 : ℝ) < 1 := one_pos
      _ = phiCat copyTPM {0} m {0} m := (phiCat_copyTPM m).symm
      _ ≤ phiCpurview copyTPM {0} m {0} :=
          Finset.le_sup' (f := fun z => phiCat copyTPM {0} z {0} m) (copy_m_mem_maxCause m)
      _ ≤ _ := Finset.le_sup' (f := fun Z => phiCpurview copyTPM {0} m Z) huniv
  · calc (0 : ℝ) < 1 := one_pos
      _ = phiEat copyTPM {0} m {0} m := (phiEat_copyTPM m).symm
      _ ≤ phiEpurview copyTPM {0} m {0} :=
          Finset.le_sup' (f := fun z => phiEat copyTPM {0} m {0} z) (copy_m_mem_maxEff m)
      _ ≤ _ := Finset.le_sup' (f := fun Z => phiEpurview copyTPM {0} m Z) huniv

end IIT
