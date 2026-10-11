/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import IIT.Cond

/-!
# Module A2 of the B1 blueprint: `Φ` from a family of distinctions sharing a unit

A port of ChordNet's `doubly_exp_le_PhiMax_of_family` (`ChordNet/PhiFamily.lean`, written
against Integ v1) to the background-conditioned cause-effect structure of `IIT/Cond.lean`
(Integ v1.1).  The combinatorial argument does not look at the substrate at all:

* a family `F` of distinctions of the structure,
* a single stated unit `p` in **every** member's support, so every subfamily has a nonempty
  congruent overlap `[IIT4, Eq 55]`, and
* a uniform lower bound `c > 0` on each member's `φ_d` per support unit,

give `2 ^ |F| - 1 - |F|` relations (all subfamilies of size `≥ 2`), each with `φ_r ≥ c`.

ChordNet states the bound for `PhiMax` of the unconditioned `Selector`.  Here it is stated
for `PhiOfStructure`, the `[IIT4, Eq 59]` sum as a function of the distinction set alone
(`IIT/Cond.lean`), and hence for `PhiOfAt T S u s σ` for **every** `SelectorAt` `σ`.  No
bridge to `PhiOf` is needed: `PhiOfAt` is `PhiOfStructure` of `distinctionsAt` by definition.

Main results:

* `PhiOfStructure_ge_family` -- the bound on an arbitrary structure.
* `PhiOfAt_ge_family`, `PhiOfAt_ge_family_of_le_card` -- every selector, any candidate
  system; the second takes any `n ≤ |F|`.
* `PhiOfAt_ge_of_mechs` -- the form used at `S = univ`: mechanisms of the conditioned
  distinction set whose unique maximal cause purview is `(univ, t)` and with
  `φ_d ≥ 2 N c` give `Φ ≥ (2 ^ |Ms| - 1 - |Ms|) c` for every selector.
* `two_pow_two_pow_le` -- the arithmetic that turns the count into `2 ^ 2 ^ (N / 8)`.
-/

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

section Family

variable {F : Finset (Distinction N)} {p : Fin N × Bool} {c : ℝ}

/-- **Every subfamily relates**: the shared stated unit keeps the congruent overlap
nonempty, and `c` bounds the per-unit integration from below. -/
lemma le_relPhi_of_sharedUnit (hc : 0 < c) (hp : ∀ d ∈ F, p ∈ d.support)
    (hcF : ∀ d ∈ F, c ≤ d.phiPerUnit)
    {d : Finset (Distinction N)} (hd : d.Nonempty) (hsub : d ⊆ F) :
    c ≤ relPhi d hd := by
  have hpt : p ∈ d.inf Distinction.support := by
    rw [mem_finset_inf]
    exact fun D hD => hp D (hsub hD)
  have hcard : (1 : ℝ) ≤ ((d.inf Distinction.support).card : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.2 ⟨_, hpt⟩)
  have hmin : c ≤ d.inf' hd Distinction.phiPerUnit := by
    rw [Finset.le_inf'_iff]
    exact fun D hD => hcF D (hsub hD)
  calc c = 1 * c := (one_mul _).symm
    _ ≤ ((d.inf Distinction.support).card : ℝ) * d.inf' hd Distinction.phiPerUnit :=
        mul_le_mul hcard hmin hc.le (le_trans zero_le_one hcard)
    _ = relPhi d hd := rfl

/-- Every subfamily of size `≥ 2` is a relation of the structure `D` `[IIT4, Eq 56]`. -/
lemma mem_relationSetsOf_of_sharedUnit {D : Finset (Distinction N)} (hc : 0 < c)
    (hp : ∀ d ∈ F, p ∈ d.support) (hcF : ∀ d ∈ F, c ≤ d.phiPerUnit) (hFD : F ⊆ D)
    {d : Finset (Distinction N)} (hd : d ∈ F.powerset.filter fun t => 2 ≤ t.card) :
    d ∈ relationSetsOf D := by
  obtain ⟨hsub', h2⟩ := Finset.mem_filter.1 hd
  have hsub : d ⊆ F := Finset.mem_powerset.1 hsub'
  have hne : d.Nonempty := Finset.card_pos.mp (by omega)
  exact Finset.mem_filter.2
    ⟨Finset.mem_powerset.2 (hsub.trans hFD), hne, h2,
      lt_of_lt_of_le hc (le_relPhi_of_sharedUnit hc hp hcF hne hsub)⟩

/-- The subsets of `F` of size at least two number `2^|F| - 1 - |F|`: all subsets, less
the empty set and the singletons. -/
lemma card_powerset_filter_two_le (F : Finset (Distinction N)) :
    (F.powerset.filter fun t => 2 ≤ t.card).card = 2 ^ F.card - 1 - F.card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := F.powerset) (p := fun t : Finset (Distinction N) => 2 ≤ t.card)
  have hfil : (F.powerset.filter fun t => ¬ (2 ≤ t.card))
      = insert (∅ : Finset (Distinction N))
          (F.image fun a => ({a} : Finset (Distinction N))) := by
    ext t
    constructor
    · intro ht
      rw [Finset.mem_filter, Finset.mem_powerset] at ht
      obtain ⟨hsub, hlt⟩ := ht
      have hc : t.card = 0 ∨ t.card = 1 := by omega
      rcases hc with h | h
      · rw [Finset.card_eq_zero] at h
        subst h
        exact Finset.mem_insert_self _ _
      · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
        exact Finset.mem_insert_of_mem
          (Finset.mem_image.2 ⟨a, hsub (Finset.mem_singleton_self a), rfl⟩)
    · intro ht
      rw [Finset.mem_insert] at ht
      rcases ht with rfl | ht
      · rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.empty_subset _, by simp⟩
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ht
        rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.singleton_subset_iff.2 ha, by simp⟩
  have hnotmem : (∅ : Finset (Distinction N))
      ∉ F.image fun a => ({a} : Finset (Distinction N)) := by
    intro h
    obtain ⟨a, _, ha⟩ := Finset.mem_image.1 h
    exact Finset.singleton_ne_empty a ha
  have hinj : Function.Injective
      fun a : Distinction N => ({a} : Finset (Distinction N)) := by
    intro a b hab
    simpa using hab
  have hcard1 : (F.powerset.filter fun t => ¬ (2 ≤ t.card)).card = 1 + F.card := by
    rw [hfil, Finset.card_insert_of_notMem hnotmem,
      Finset.card_image_of_injective _ hinj]
    omega
  rw [Finset.card_powerset] at hsplit
  omega

/-- **The relation sum**: `(2^|F| - 1 - |F|) · c` is a lower bound on the `[IIT4, Eq 56]`
sum of `[IIT4, Eq 59]` of any structure `D ⊇ F`. -/
lemma sum_relationSetsOf_ge {D : Finset (Distinction N)} (hc : 0 < c)
    (hp : ∀ d ∈ F, p ∈ d.support) (hcF : ∀ d ∈ F, c ≤ d.phiPerUnit) (hFD : F ⊆ D) :
    ((2 ^ F.card - 1 - F.card : ℕ) : ℝ) * c
      ≤ ∑ d ∈ relationSetsOf D, relPhiOrZero d := by
  classical
  set R₀ := F.powerset.filter fun t => 2 ≤ t.card with hR₀
  have hsub : R₀ ⊆ relationSetsOf D :=
    fun d hd => mem_relationSetsOf_of_sharedUnit hc hp hcF hFD hd
  have hterm : ∀ d ∈ R₀, c ≤ relPhiOrZero d := by
    intro d hd
    obtain ⟨hsub', h2⟩ := Finset.mem_filter.1 hd
    have hdsub : d ⊆ F := Finset.mem_powerset.1 hsub'
    have hne : d.Nonempty := Finset.card_pos.mp (by omega)
    rw [relPhiOrZero, dite_eq_left_of_eq_true (eq_true hne)]
    exact le_relPhi_of_sharedUnit hc hp hcF hne hdsub
  have hnonneg : ∀ d ∈ relationSetsOf D, 0 ≤ relPhiOrZero d :=
    fun d _ => relPhiOrZero_nonneg d
  calc ((2 ^ F.card - 1 - F.card : ℕ) : ℝ) * c
      = (R₀.card : ℝ) * c := by rw [card_powerset_filter_two_le F]
    _ = ∑ _d ∈ R₀, c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ d ∈ R₀, relPhiOrZero d := Finset.sum_le_sum hterm
    _ ≤ ∑ d ∈ relationSetsOf D, relPhiOrZero d :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun d hd _ => hnonneg d hd

/-- **The general bound on an arbitrary cause-effect structure.**  A family `F ⊆ D` of
distinctions sharing a stated support unit, each integrating at least `c > 0` per support
unit, forces `Φ(D) ≥ (2^|F| - 1 - |F|) · c`. -/
theorem PhiOfStructure_ge_family {D F : Finset (Distinction N)} {p : Fin N × Bool} {c : ℝ}
    (hc : 0 < c) (hp : ∀ d ∈ F, p ∈ d.support) (hcF : ∀ d ∈ F, c ≤ d.phiPerUnit)
    (hFD : F ⊆ D) :
    ((2 ^ F.card - 1 - F.card : ℕ) : ℝ) * c ≤ PhiOfStructure D := by
  classical
  have h1 := sum_relationSetsOf_ge hc hp hcF hFD
  rw [PhiOfStructure]
  have hd : 0 ≤ ∑ d ∈ D, d.phi := Finset.sum_nonneg fun d _ => d.phi_pos.le
  have hs : 0 ≤ ∑ d ∈ selfRelationsOf D, selfRelPhi d :=
    Finset.sum_nonneg fun d hd => (Finset.mem_filter.1 hd).2.le
  linarith

/-- The same bound with any `n ≤ |F|` in place of `|F|`: restrict to an `n`-subfamily. -/
theorem PhiOfStructure_ge_family_of_le_card {D F : Finset (Distinction N)}
    {p : Fin N × Bool} {c : ℝ} {n : ℕ} (hc : 0 < c) (hp : ∀ d ∈ F, p ∈ d.support)
    (hcF : ∀ d ∈ F, c ≤ d.phiPerUnit) (hFD : F ⊆ D) (hn : n ≤ F.card) :
    ((2 ^ n - 1 - n : ℕ) : ℝ) * c ≤ PhiOfStructure D := by
  obtain ⟨G, hGF, hGn⟩ := Finset.exists_subset_card_eq hn
  have h := PhiOfStructure_ge_family (D := D) (F := G) hc (fun d hd => hp d (hGF hd))
    (fun d hd => hcF d (hGF hd)) (hGF.trans hFD)
  rwa [hGn] at h

end Family

/-! ## Every selector of the conditioned structure -/

section Selector

variable {T : UnitTPM N} {S : Finset (Fin N)} {u s : State N}

/-- **`Φ` of a candidate system, every selector.**  A family `F` of the conditioned
distinctions `distinctionsAt T S u s σ` sharing a stated unit, each with `φ_d` per support
unit at least `c > 0`, gives `PhiOfAt T S u s σ ≥ (2^|F| - 1 - |F|) · c`. -/
theorem PhiOfAt_ge_family (σ : SelectorAt T S u s) {F : Finset (Distinction N)}
    {p : Fin N × Bool} {c : ℝ} (hc : 0 < c) (hp : ∀ d ∈ F, p ∈ d.support)
    (hcF : ∀ d ∈ F, c ≤ d.phiPerUnit) (hFD : F ⊆ distinctionsAt T S u s σ) :
    ((2 ^ F.card - 1 - F.card : ℕ) : ℝ) * c ≤ PhiOfAt T S u s σ := by
  rw [PhiOfAt]
  exact PhiOfStructure_ge_family hc hp hcF hFD

/-- **The blueprint corollary.**  A family of at least `n` conditioned distinctions sharing
a stated unit, with `phiPerUnit ≥ c > 0`, gives `PhiOfAt ≥ (2^n - 1 - n) · c` for every
selector. -/
theorem PhiOfAt_ge_family_of_le_card (σ : SelectorAt T S u s) {F : Finset (Distinction N)}
    {p : Fin N × Bool} {c : ℝ} {n : ℕ} (hc : 0 < c) (hp : ∀ d ∈ F, p ∈ d.support)
    (hcF : ∀ d ∈ F, c ≤ d.phiPerUnit) (hFD : F ⊆ distinctionsAt T S u s σ)
    (hn : n ≤ F.card) :
    ((2 ^ n - 1 - n : ℕ) : ℝ) * c ≤ PhiOfAt T S u s σ := by
  rw [PhiOfAt]
  exact PhiOfStructure_ge_family_of_le_card hc hp hcF hFD hn

/-- A support has at most `2 N` stated units, so `φ_d ≥ 2 N c` gives `phiPerUnit ≥ c`. -/
lemma le_phiPerUnit_of_two_mul_le {d : Distinction N} {c : ℝ} (hc : 0 ≤ c)
    (h : 2 * N * c ≤ d.phi) : c ≤ d.phiPerUnit := by
  have hpos : (0 : ℝ) < (d.support.card : ℝ) := by exact_mod_cast d.card_support_pos
  rw [Distinction.phiPerUnit, le_div_iff₀ hpos]
  have h1 : d.support.card ≤ Fintype.card (Fin N × Bool) := Finset.card_le_univ _
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h1
  have h2 : (d.support.card : ℝ) ≤ 2 * N := by
    have : (d.support.card : ℝ) ≤ ((N * 2 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this
    linarith
  have h3 : c * (d.support.card : ℝ) ≤ c * (2 * N) := mul_le_mul_of_nonneg_left h2 hc
  linarith

/-- **Blueprint A2, the form used at `S = univ`.**  Let `Ms` be mechanisms of the
conditioned distinction set whose maximal cause purview is unique and equal to `(univ, t)`,
each with `φ_d ≥ 2 N c`, `c > 0`.  Then for **every** selector `σ`,
`PhiOfAt T univ u s σ ≥ (2^|Ms| - 1 - |Ms|) · c`.  The shared stated unit is any `(k, t k)`:
every selector must pick the cause purview `(univ, t)`, so it lies in every support. -/
theorem PhiOfAt_ge_of_mechs (T : UnitTPM N) (u s : State N) (σ : SelectorAt T univ u s)
    (Ms : Finset (Finset (Fin N))) (t : State N) {c : ℝ} (hc : 0 < c)
    (hmem : ∀ M ∈ Ms, M ∈ distinctionMechsAt T univ u s)
    (huniq : ∀ M ∈ Ms, maxCausePurviewsAt T univ u M s = {(univ, t)})
    (hphi : ∀ M ∈ Ms, 2 * N * c ≤ phiDAt T univ u M s) :
    ((2 ^ Ms.card - 1 - Ms.card : ℕ) : ℝ) * c ≤ PhiOfAt T univ u s σ := by
  classical
  rcases Ms.eq_empty_or_nonempty with h0 | ⟨M0, hM0⟩
  · subst h0
    simpa using PhiOfAt_nonneg T univ u s σ
  -- every selector picks the cause purview `(univ, t)`
  have hcause : ∀ M ∈ Ms, σ.causeOf M = (univ, t) := by
    intro M hM
    have h := σ.cause_mem M (hmem M hM)
    rw [huniq M hM] at h
    exact Finset.mem_singleton.1 h
  -- a unit exists (the cause purview of `M0` is nonempty)
  obtain ⟨q, hq⟩ := σ.cause_nonempty M0 (hmem M0 hM0)
  set p : Fin N × Bool := (q.1, t q.1) with hpdef
  set F : Finset (Distinction N) :=
    Ms.attach.image fun M => distinctionOfAt T univ u s σ M.1 (hmem M.1 M.2) with hF
  have hFcard : F.card = Ms.card := by
    rw [hF, Finset.card_image_of_injective, Finset.card_attach]
    intro a b hab
    exact Subtype.ext (congrArg Distinction.mech hab)
  have hFD : F ⊆ distinctionsAt T univ u s σ := by
    intro d hd
    obtain ⟨M, -, rfl⟩ := Finset.mem_image.1 hd
    exact Finset.mem_image.2 ⟨⟨M.1, hmem M.1 M.2⟩, Finset.mem_attach _ _, rfl⟩
  have hp : ∀ d ∈ F, p ∈ d.support := by
    intro d hd
    obtain ⟨M, -, rfl⟩ := Finset.mem_image.1 hd
    apply Finset.mem_union_left
    show p ∈ stated (σ.causeOf M.1).1 (σ.causeOf M.1).2
    rw [hcause M.1 M.2, mem_stated]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hcF : ∀ d ∈ F, c ≤ d.phiPerUnit := by
    intro d hd
    obtain ⟨M, -, rfl⟩ := Finset.mem_image.1 hd
    exact le_phiPerUnit_of_two_mul_le hc.le (hphi M.1 M.2)
  have h := PhiOfAt_ge_family σ hc hp hcF hFD
  rwa [hFcard] at h

/-- `PhiOfAt_ge_of_mechs` with any `n ≤ |Ms|`. -/
theorem PhiOfAt_ge_of_mechs_of_le_card (T : UnitTPM N) (u s : State N)
    (σ : SelectorAt T univ u s) (Ms : Finset (Finset (Fin N))) (t : State N) {c : ℝ}
    {n : ℕ} (hc : 0 < c)
    (hmem : ∀ M ∈ Ms, M ∈ distinctionMechsAt T univ u s)
    (huniq : ∀ M ∈ Ms, maxCausePurviewsAt T univ u M s = {(univ, t)})
    (hphi : ∀ M ∈ Ms, 2 * N * c ≤ phiDAt T univ u M s) (hn : n ≤ Ms.card) :
    ((2 ^ n - 1 - n : ℕ) : ℝ) * c ≤ PhiOfAt T univ u s σ := by
  obtain ⟨G, hGM, hGn⟩ := Finset.exists_subset_card_eq hn
  have h := PhiOfAt_ge_of_mechs T u s σ G t hc (fun M hM => hmem M (hGM hM))
    (fun M hM => huniq M (hGM hM)) (fun M hM => hphi M (hGM hM))
  rwa [hGn] at h

end Selector

/-! ## The arithmetic: from the count to `2 ^ 2 ^ (N / 8)` -/

/-- `2 ^ (L - 1) ≤ 2 ^ L - 1 - L` once `L ≥ 3`. -/
lemma two_pow_pred_le_sub (L : ℕ) (hL : 3 ≤ L) : 2 ^ (L - 1) ≤ 2 ^ L - 1 - L := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 3 := ⟨L - 3, by omega⟩
  have h1 : m < 2 ^ m := Nat.lt_two_pow_self
  have h2 : 2 ^ (m + 3 - 1) = 4 * 2 ^ m := by
    rw [show m + 3 - 1 = m + 2 by omega, pow_add]
    ring
  have h3 : 2 ^ (m + 3) = 8 * 2 ^ m := by
    rw [pow_add]
    ring
  rw [h2, h3]
  omega

/-- **Blueprint A2, the arithmetic.**  With at least `2 ^ (N / 8) + 2 N` distinctions in the
family and per-unit integration `c ≥ 2 ^ (-N)`, the family bound exceeds `2 ^ 2 ^ (N / 8)`. -/
theorem two_pow_two_pow_le (hN : 1 ≤ N) {L : ℕ} (hL : 2 ^ (N / 8) + 2 * N ≤ L) {c : ℝ}
    (hc : (2 : ℝ) ^ (-(N : ℤ)) ≤ c) :
    (2 : ℝ) ^ (2 ^ (N / 8)) ≤ ((2 ^ L - 1 - L : ℕ) : ℝ) * c := by
  set K := 2 ^ (N / 8) with hK
  have hK1 : 1 ≤ K := Nat.one_le_two_pow
  have hL3 : 3 ≤ L := by omega
  have hnat := two_pow_pred_le_sub L hL3
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc
  have h2N : 1 ≤ (2 : ℝ) ^ N * c := by
    rw [zpow_neg, zpow_natCast] at hc
    have := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 2 ^ N)
    rwa [mul_inv_cancel₀ (by positivity)] at this
  have hsplit : (2 : ℝ) ^ (L - 1) = 2 ^ K * 2 ^ N * 2 ^ (L - 1 - N - K) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hge : (2 : ℝ) ^ K * 2 ^ N ≤ 2 ^ (L - 1) := by
    rw [hsplit]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ one_le_two)
  calc (2 : ℝ) ^ K ≤ 2 ^ K * (2 ^ N * c) := le_mul_of_one_le_right (by positivity) h2N
    _ = (2 ^ K * 2 ^ N) * c := by ring
    _ ≤ (2 : ℝ) ^ (L - 1) * c := mul_le_mul_of_nonneg_right hge hc0.le
    _ = ((2 ^ (L - 1) : ℕ) : ℝ) * c := by push_cast; ring
    _ ≤ ((2 ^ L - 1 - L : ℕ) : ℝ) * c :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) hc0.le

end Census
end IIT

#print axioms IIT.Census.PhiOfStructure_ge_family
#print axioms IIT.Census.PhiOfAt_ge_family
#print axioms IIT.Census.PhiOfAt_ge_family_of_le_card
#print axioms IIT.Census.PhiOfAt_ge_of_mechs
#print axioms IIT.Census.PhiOfAt_ge_of_mechs_of_le_card
#print axioms IIT.Census.two_pow_two_pow_le
