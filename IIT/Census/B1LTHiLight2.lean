/-
Census, B1 LTBetaHi, round-2 open item (c), counting part: **few adverse members** (W2 6.1(c),(e) second halves,
Corollary AC', in the form "count, do not exclude": the selection `lt3WSel` is unchanged).

For a class `Q` (`m = qM Q`) the members of `qFam Q` are indexed by `p ∈ Fin m × Fin m` with units
`(a_p, b_p, c_p)` (`lt3uE Q p`, one unit per part). The primitive light statistics of a member are
* **unit-level** (support one unit `x`): `m_{x}`, `Õ_x({x})`, `Ñ^β_{x,{x}}({x})` (class `univ`), counted over all
  `N` units (`lt3UA`, `lt3UnitGood`) at level `κσ_N`;
* **member-specific** (support `≥ 2` units of the member, which pins the member): 44 families (`m_T`; `Õ_i(T)`;
  `Ñ^β_{i,R}(T)` for each column position, nonzero shift mask and parity, class `lt3LamOf Q (lt3LamT R)` with
  `|R ∩ Λ|` odd), each injective in the member index, counted at level `lt2κ σ_N` (`lt3MemGood`).
`lt3_G_of_good`: a member whose statistics are all below these levels has every `|G_{i,R}(T)| ≤ 5/2 κσ_N`.
`lt3_bad_card`: the members with a larger `G` (`lt3Bad`) number at most `3m|UA| + Σ_families |adverse|`.
`lt3_adv_sub_bad`: adverse members at `w½` (`lt3Adv`, level `3κσ_N`) are bad at `w` (perturbation `≤ κσ_N/2`).
**`lt3_adv_ev`**: `P(|Sp| < 12, 7 ≤ m, N ≤ D0 m, m² < 4 |lt3Adv|) ≤ e^{-2N}` for any `D0 ≥ 1` and
`κ ≥ 2500` with `κ² ≥ 4(288 D0 + log(192 e D0))` (member families: `lt2_kind_mT/Ot/N0`; unit families: the count
lemmas at level `κ`, threshold `m₃ = N/(96 D0) + 1`).
-/
import IIT.Census.B1LTHiLight

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-! ### Masks -/

/-- The bits of a mask. -/
def lt3bits (u : Fin (2 ^ 3)) : Finset (Fin 3) := univ.filter fun q : Fin 3 => (u : ℕ).testBit q = true

lemma pkSet_eq_map (e : Fin 3 ↪ Fin N) (u : Fin (2 ^ 3)) : pkSet e u = (lt3bits u).map e := rfl

lemma lt3bits_inj : ∀ u u' : Fin (2 ^ 3), lt3bits u = lt3bits u' → u = u' := by decide

lemma lt3bits_surj : ∀ B : Finset (Fin 3), ∃ u : Fin (2 ^ 3), lt3bits u = B := by decide

lemma lt3bits_zero : lt3bits (0 : Fin (2 ^ 3)) = ∅ := by decide

lemma lt3bits_card_le (u : Fin (2 ^ 3)) : (lt3bits u).card ≤ 3 :=
  (card_le_univ _).trans (by simp)

lemma lt3_F1 : ∀ u : Fin (2 ^ 3), u ≠ 0 → ¬ 2 ≤ (lt3bits u).card → ∃ q, lt3bits u = {q} := by decide

lemma lt3_F2 : ∀ (ci : Fin 3) (u : Fin (2 ^ 3)), u ≠ 0 → ¬ 2 ≤ (insert ci (lt3bits u)).card →
    lt3bits u = {ci} := by decide

lemma lt3_F3 : ∀ (ci : Fin 3) (r t : Fin (2 ^ 3)), r ≠ 0 → t ≠ 0 →
    ¬ 2 ≤ (insert ci (lt3bits r ∪ lt3bits t)).card → lt3bits r = {ci} ∧ lt3bits t = {ci} := by decide

lemma lt3_bits_two : ∀ u : Fin (2 ^ 3), u ≠ 0 → (lt3bits u).card % 2 = 0 → (1 : Fin 3) ∉ lt3bits u →
    (2 : Fin 3) ∈ lt3bits u := by decide

lemma pkSet_card_eq (e : Fin 3 ↪ Fin N) (u : Fin (2 ^ 3)) : (pkSet e u).card = (lt3bits u).card := by
  rw [pkSet_eq_map, card_map]

lemma pkSet_zero (e : Fin 3 ↪ Fin N) : pkSet e 0 = ∅ := by rw [pkSet_eq_map, lt3bits_zero, map_empty]

/-- Every subset of the image of `e` is a `pkSet`. -/
lemma lt3_pkSet_surj (e : Fin 3 ↪ Fin N) {S R : Finset (Fin N)} (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) (hR : R ⊆ S) :
    ∃ u : Fin (2 ^ 3), pkSet e u = R := by
  classical
  obtain ⟨u, hu⟩ := lt3bits_surj (univ.filter fun q => e q ∈ R)
  refine ⟨u, ?_⟩
  rw [pkSet_eq_map, hu]
  ext x
  simp only [Finset.mem_map, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨q, hq, rfl⟩; exact hq
  · intro hx
    obtain ⟨q, rfl⟩ := (hS x).1 (hR hx)
    exact ⟨q, hx, rfl⟩

lemma lt3_pkSet_single (e : Fin 3 ↪ Fin N) {u : Fin (2 ^ 3)} {q : Fin 3} (h : lt3bits u = {q}) :
    pkSet e u = {e q} := by
  rw [pkSet_eq_map, h, map_singleton]

lemma lt3_map_sub (e : Fin 3 ↪ Fin N) {S : Finset (Fin N)} (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
    (B : Finset (Fin 3)) : B.map e ⊆ S := by
  intro x hx
  obtain ⟨q, -, rfl⟩ := Finset.mem_map.1 hx
  exact (hS _).2 ⟨q, rfl⟩

/-! ### Class functionals of the shifted statistics -/

/-- The class type of a shift mask: `0` (odd size; `Λ = univ`), `1` (`Λ = B`), `2` (`Λ = C`). -/
def lt3LamT (u : Fin (2 ^ 3)) : Fin 3 :=
  if (lt3bits u).card % 2 = 1 then 0 else if (1 : Fin 3) ∈ lt3bits u then 1 else 2

/-- The class functional of a type. -/
def lt3LamOf (Q : Finset (Fin N)) (t : Fin 3) : Finset (Fin N) := if t = 0 then univ else qPart Q t

lemma lt3_inter_part (Q : Finset (Fin N)) (e : Fin 3 ↪ Fin N) (he : ∀ q t : Fin 3, e q ∈ qPart Q t ↔ q = t)
    (u : Fin (2 ^ 3)) (t : Fin 3) : (pkSet e u ∩ qPart Q t).card = if t ∈ lt3bits u then 1 else 0 := by
  classical
  have h : pkSet e u ∩ qPart Q t = ((lt3bits u).filter fun q => q = t).map e := by
    ext x
    simp only [pkSet_eq_map, mem_inter, Finset.mem_map, mem_filter]
    constructor
    · rintro ⟨⟨q, hq, rfl⟩, hx⟩; exact ⟨q, ⟨hq, (he q t).1 hx⟩, rfl⟩
    · rintro ⟨q, ⟨hq, rfl⟩, rfl⟩; exact ⟨⟨q, hq, rfl⟩, (he q q).2 rfl⟩
  rw [h, card_map, Finset.filter_eq']
  split_ifs <;> simp

/-- **`|R ∩ Λ|` is odd** for the class of a nonzero shift mask (one unit per part). -/
lemma lt3_odd_Lam (Q : Finset (Fin N)) (e : Fin 3 ↪ Fin N) (he : ∀ q t : Fin 3, e q ∈ qPart Q t ↔ q = t)
    {u : Fin (2 ^ 3)} (hu : u ≠ 0) : (pkSet e u ∩ lt3LamOf Q (lt3LamT u)).card % 2 = 1 := by
  by_cases h1 : (lt3bits u).card % 2 = 1
  · have : lt3LamT u = 0 := by unfold lt3LamT; rw [if_pos h1]
    rw [this]; unfold lt3LamOf; rw [if_pos rfl, inter_univ, pkSet_card_eq]; exact h1
  · by_cases h2 : (1 : Fin 3) ∈ lt3bits u
    · have : lt3LamT u = 1 := by unfold lt3LamT; rw [if_neg h1, if_pos h2]
      rw [this]; unfold lt3LamOf; rw [if_neg (by decide), lt3_inter_part Q e he u 1, if_pos h2]
    · have h3 := lt3_bits_two u hu (by omega) h2
      have : lt3LamT u = 2 := by unfold lt3LamT; rw [if_neg h1, if_neg h2]
      rw [this]; unfold lt3LamOf; rw [if_neg (by decide), lt3_inter_part Q e he u 2, if_pos h3]

lemma lt3LamOf_card {Q : Finset (Fin N)} (h7 : 7 ≤ qM Q) (hN : 7 ≤ N) (t : Fin 3) : 7 ≤ (lt3LamOf Q t).card := by
  unfold lt3LamOf
  split_ifs
  · rw [card_univ, Fintype.card_fin]; exact hN
  · rw [qPart_card]; exact h7

lemma lt3_symmDiff_ne {T T' Λ : Finset (Fin N)} (hT : T.card ≤ 3) (hT' : T'.card ≤ 3) (hΛ : 7 ≤ Λ.card) :
    symmDiff T T' ≠ Λ := by
  intro h
  have : (symmDiff T T').card ≤ 6 := by
    have hsub : symmDiff T T' ⊆ T ∪ T' := by
      intro x hx; rw [Finset.mem_symmDiff] at hx; rw [mem_union]; tauto
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le T T')
    omega
  rw [h] at this; omega

/-! ### The members of `qFam Q`, indexed -/

section Fam

variable (Q : Finset (Fin N))

/-- The units of the member indexed by `p`. -/
def lt3ua (p : Fin (qM Q) × Fin (qM Q)) : Fin N := (qPart Q 0).orderEmbOfFin (qPart_card Q 0) p.1
def lt3ub (p : Fin (qM Q) × Fin (qM Q)) : Fin N := (qPart Q 1).orderEmbOfFin (qPart_card Q 1) p.2
def lt3uc (p : Fin (qM Q) × Fin (qM Q)) : Fin N := (qPart Q 2).orderEmbOfFin (qPart_card Q 2) (p.1 + p.2)

lemma lt3ua_mem (p : Fin (qM Q) × Fin (qM Q)) : lt3ua Q p ∈ qPart Q 0 := orderEmbOfFin_mem _ _ _
lemma lt3ub_mem (p : Fin (qM Q) × Fin (qM Q)) : lt3ub Q p ∈ qPart Q 1 := orderEmbOfFin_mem _ _ _
lemma lt3uc_mem (p : Fin (qM Q) × Fin (qM Q)) : lt3uc Q p ∈ qPart Q 2 := orderEmbOfFin_mem _ _ _

lemma lt3u_ab (p : Fin (qM Q) × Fin (qM Q)) : lt3ua Q p ≠ lt3ub Q p := fun h =>
  Finset.disjoint_left.1 (qPart_disj Q (by decide : (0 : Fin 3) ≠ 1)) (lt3ua_mem Q p) (by rw [h]; exact lt3ub_mem Q p)
lemma lt3u_ac (p : Fin (qM Q) × Fin (qM Q)) : lt3ua Q p ≠ lt3uc Q p := fun h =>
  Finset.disjoint_left.1 (qPart_disj Q (by decide : (0 : Fin 3) ≠ 2)) (lt3ua_mem Q p) (by rw [h]; exact lt3uc_mem Q p)
lemma lt3u_bc (p : Fin (qM Q) × Fin (qM Q)) : lt3ub Q p ≠ lt3uc Q p := fun h =>
  Finset.disjoint_left.1 (qPart_disj Q (by decide : (1 : Fin 3) ≠ 2)) (lt3ub_mem Q p) (by rw [h]; exact lt3uc_mem Q p)

/-- The unit embedding of a member. -/
def lt3uE (p : Fin (qM Q) × Fin (qM Q)) : Fin 3 ↪ Fin N := pkE3 (lt3u_ab Q p) (lt3u_ac Q p) (lt3u_bc Q p)

/-- The member of index `p`. -/
def lt3uS (p : Fin (qM Q) × Fin (qM Q)) : Finset (Fin N) := {lt3ua Q p, lt3ub Q p, lt3uc Q p}

lemma lt3uS_spec (p : Fin (qM Q) × Fin (qM Q)) : ∀ x, x ∈ lt3uS Q p ↔ ∃ i, lt3uE Q p i = x :=
  pkE3_S _ _ _

lemma qFam_eq_image : qFam Q = univ.image (lt3uS Q) := rfl

lemma lt3uE_mem (p : Fin (qM Q) × Fin (qM Q)) (q : Fin 3) : lt3uE Q p q ∈ lt3uS Q p :=
  (lt3uS_spec Q p _).2 ⟨q, rfl⟩

lemma lt3_pkSet_sub (p : Fin (qM Q) × Fin (qM Q)) (u : Fin (2 ^ 3)) : pkSet (lt3uE Q p) u ⊆ lt3uS Q p := by
  rw [pkSet_eq_map]; exact lt3_map_sub _ (lt3uS_spec Q p) _

lemma lt3uE_part (p : Fin (qM Q) × Fin (qM Q)) (q : Fin 3) : lt3uE Q p q ∈ qPart Q q := by
  fin_cases q
  · exact lt3ua_mem Q p
  · exact lt3ub_mem Q p
  · exact lt3uc_mem Q p

lemma lt3uE_part_iff (p : Fin (qM Q) × Fin (qM Q)) (q t : Fin 3) : lt3uE Q p q ∈ qPart Q t ↔ q = t := by
  constructor
  · intro h
    by_contra hne
    exact Finset.disjoint_left.1 (qPart_disj Q hne) (lt3uE_part Q p q) h
  · rintro rfl; exact lt3uE_part Q p q

/-- **Two members sharing two units are equal.** -/
lemma lt3uS_two {p p' : Fin (qM Q) × Fin (qM Q)} (h : 2 ≤ (lt3uS Q p ∩ lt3uS Q p').card) : p = p' := by
  have := trTriple_two (qPart_disj Q (by decide : (0 : Fin 3) ≠ 1)) (qPart_disj Q (by decide : (0 : Fin 3) ≠ 2))
    (qPart_disj Q (by decide : (1 : Fin 3) ≠ 2)) (x := p.1) (y := p.2) (x' := p'.1) (y' := p'.2) h
  exact Prod.ext (congrArg Prod.fst this) (congrArg Prod.snd this)

/-- A set of `≥ 2` units inside two members pins the member. -/
lemma lt3u_sub_inj {p p' : Fin (qM Q) × Fin (qM Q)} {U : Finset (Fin N)} (hU : 2 ≤ U.card)
    (h1 : U ⊆ lt3uS Q p) (h2 : U ⊆ lt3uS Q p') : p = p' :=
  lt3uS_two Q (hU.trans (card_le_card (subset_inter h1 h2)))

/-- At most `3m` members contain a given unit. -/
lemma lt3u_card_mem (x : Fin N) :
    ((univ : Finset (Fin (qM Q) × Fin (qM Q))).filter fun p => x ∈ lt3uS Q p).card ≤ 3 * qM Q := by
  classical
  have hsub : ((univ : Finset (Fin (qM Q) × Fin (qM Q))).filter fun p => x ∈ lt3uS Q p) ⊆
      (univ.filter fun p => lt3ua Q p = x) ∪ (univ.filter fun p => lt3ub Q p = x) ∪
        (univ.filter fun p => lt3uc Q p = x) := by
    intro p hp
    have h := (mem_filter.1 hp).2
    simp only [lt3uS, mem_insert, mem_singleton] at h
    simp only [mem_union, mem_filter, mem_univ, true_and]
    rcases h with h | h | h
    · exact Or.inl (Or.inl h.symm)
    · exact Or.inl (Or.inr h.symm)
    · exact Or.inr h.symm
  have hA : (univ.filter fun p : Fin (qM Q) × Fin (qM Q) => lt3ua Q p = x).card ≤ qM Q := by
    calc _ ≤ (univ : Finset (Fin (qM Q))).card := card_le_card_of_injOn (fun p => p.2) (fun _ _ => mem_univ _)
            (fun p hp p' hp' h => by
              have h1 := (mem_filter.1 hp).2
              have h2 := (mem_filter.1 hp').2
              have : p.1 = p'.1 := ((qPart Q 0).orderEmbOfFin (qPart_card Q 0)).injective (h1.trans h2.symm)
              exact Prod.ext this h)
      _ = qM Q := by simp
  have hB : (univ.filter fun p : Fin (qM Q) × Fin (qM Q) => lt3ub Q p = x).card ≤ qM Q := by
    calc _ ≤ (univ : Finset (Fin (qM Q))).card := card_le_card_of_injOn (fun p => p.1) (fun _ _ => mem_univ _)
            (fun p hp p' hp' h => by
              have h1 := (mem_filter.1 hp).2
              have h2 := (mem_filter.1 hp').2
              have : p.2 = p'.2 := ((qPart Q 1).orderEmbOfFin (qPart_card Q 1)).injective (h1.trans h2.symm)
              exact Prod.ext h this)
      _ = qM Q := by simp
  have hC : (univ.filter fun p : Fin (qM Q) × Fin (qM Q) => lt3uc Q p = x).card ≤ qM Q := by
    calc _ ≤ (univ : Finset (Fin (qM Q))).card := card_le_card_of_injOn (fun p => p.1) (fun _ _ => mem_univ _)
            (fun p hp p' hp' h => by
              have h1 := (mem_filter.1 hp).2
              have h2 := (mem_filter.1 hp').2
              have hs : p.1 + p.2 = p'.1 + p'.2 :=
                ((qPart Q 2).orderEmbOfFin (qPart_card Q 2)).injective (h1.trans h2.symm)
              have h' : p.1 = p'.1 := h
              rw [h'] at hs
              exact Prod.ext h' (add_left_cancel hs))
      _ = qM Q := by simp
  have u1 := card_union_le ((univ.filter fun p : Fin (qM Q) × Fin (qM Q) => lt3ua Q p = x) ∪
    (univ.filter fun p : Fin (qM Q) × Fin (qM Q) => lt3ub Q p = x))
    (univ.filter fun p : Fin (qM Q) × Fin (qM Q) => lt3uc Q p = x)
  have u2 := card_union_le (univ.filter fun p : Fin (qM Q) × Fin (qM Q) => lt3ua Q p = x)
    (univ.filter fun p : Fin (qM Q) × Fin (qM Q) => lt3ub Q p = x)
  have u3 := card_le_card hsub
  omega

/-! #### The member families -/

/-- `m_T` family: `(p, T-mask)` with `|T| ≥ 2`. -/
def lt3Pm : Finset ((Fin (qM Q) × Fin (qM Q)) × Fin (2 ^ 3)) := univ.filter fun x => 2 ≤ (lt3bits x.2).card

/-- `Õ` family: `((p, i), T-mask)` with `T ≠ ∅`, `|{i} ∪ T| ≥ 2`. -/
def lt3Po : Finset (((Fin (qM Q) × Fin (qM Q)) × Fin 3) × Fin (2 ^ 3)) :=
  univ.filter fun x => x.2 ≠ 0 ∧ 2 ≤ (insert x.1.2 (lt3bits x.2)).card

/-- `Ñ` family for a column position `ci` and a shift mask `rb`: `(p, T-mask)` with `T ≠ ∅`,
`|{i} ∪ R ∪ T| ≥ 2`. -/
def lt3Pn (ci : Fin 3) (rb : Fin (2 ^ 3)) : Finset ((Fin (qM Q) × Fin (qM Q)) × Fin (2 ^ 3)) :=
  univ.filter fun x => x.2 ≠ 0 ∧ 2 ≤ (insert ci (lt3bits rb ∪ lt3bits x.2)).card

lemma lt3Pm_card : (lt3Pm Q).card ≤ 8 * (qM Q * qM Q) := by
  refine (card_filter_le _ _).trans (le_of_eq ?_)
  simp only [card_univ, Fintype.card_prod, Fintype.card_fin]; ring

lemma lt3Po_card : (lt3Po Q).card ≤ 24 * (qM Q * qM Q) := by
  refine (card_filter_le _ _).trans (le_of_eq ?_)
  simp only [card_univ, Fintype.card_prod, Fintype.card_fin]; ring

lemma lt3Pn_card (ci : Fin 3) (rb : Fin (2 ^ 3)) : (lt3Pn Q ci rb).card ≤ 8 * (qM Q * qM Q) := by
  refine (card_filter_le _ _).trans (le_of_eq ?_)
  simp only [card_univ, Fintype.card_prod, Fintype.card_fin]; ring

lemma lt3_pkSet_inj (e : Fin 3 ↪ Fin N) {u u' : Fin (2 ^ 3)} (h : pkSet e u = pkSet e u') : u = u' := by
  rw [pkSet_eq_map, pkSet_eq_map] at h
  exact lt3bits_inj _ _ (Finset.map_inj.1 h)

lemma lt3Pm_inj : Set.InjOn (fun x : (Fin (qM Q) × Fin (qM Q)) × Fin (2 ^ 3) => pkSet (lt3uE Q x.1) x.2)
    (lt3Pm Q : Set _) := by
  intro x hx x' hx' h
  have h2 : 2 ≤ (lt3bits x.2).card := (mem_filter.1 hx).2
  simp only at h
  have hp : x.1 = x'.1 := lt3u_sub_inj Q (U := pkSet (lt3uE Q x.1) x.2) (by rw [pkSet_card_eq]; exact h2)
    (lt3_pkSet_sub Q x.1 x.2) (by rw [h]; exact lt3_pkSet_sub Q x'.1 x'.2)
  rw [← hp] at h
  exact Prod.ext hp (lt3_pkSet_inj _ h)

lemma lt3Po_inj : Set.InjOn (fun x : ((Fin (qM Q) × Fin (qM Q)) × Fin 3) × Fin (2 ^ 3) =>
    (lt3uE Q x.1.1 x.1.2, pkSet (lt3uE Q x.1.1) x.2)) (lt3Po Q : Set _) := by
  intro x hx x' hx' h
  have h2 : 2 ≤ (insert x.1.2 (lt3bits x.2)).card := (mem_filter.1 hx).2.2
  simp only [Prod.mk.injEq] at h
  obtain ⟨hi, hT⟩ := h
  set U := insert (lt3uE Q x.1.1 x.1.2) (pkSet (lt3uE Q x.1.1) x.2) with hU
  have hUc : 2 ≤ U.card := by rw [hU, pkSet_eq_map, ← map_insert, card_map]; exact h2
  have hU1 : U ⊆ lt3uS Q x.1.1 := insert_subset (lt3uE_mem Q _ _) (lt3_pkSet_sub Q _ _)
  have hU2 : U ⊆ lt3uS Q x'.1.1 := by
    rw [hU, hi, hT]; exact insert_subset (lt3uE_mem Q _ _) (lt3_pkSet_sub Q _ _)
  have hp : x.1.1 = x'.1.1 := lt3u_sub_inj Q hUc hU1 hU2
  rw [← hp] at hi hT
  have hci : x.1.2 = x'.1.2 := (lt3uE Q x.1.1).injective hi
  exact Prod.ext (Prod.ext hp hci) (lt3_pkSet_inj _ hT)

lemma lt3Pn_inj (ci : Fin 3) (rb : Fin (2 ^ 3)) : Set.InjOn (fun x : (Fin (qM Q) × Fin (qM Q)) × Fin (2 ^ 3) =>
    ((lt3uE Q x.1 ci, pkSet (lt3uE Q x.1) rb, pkSet (lt3uE Q x.1) x.2) : LT2Idx N)) (lt3Pn Q ci rb : Set _) := by
  intro x hx x' hx' h
  have h2 : 2 ≤ (insert ci (lt3bits rb ∪ lt3bits x.2)).card := (mem_filter.1 hx).2.2
  simp only [Prod.mk.injEq] at h
  obtain ⟨hi, hR, hT⟩ := h
  set U := insert (lt3uE Q x.1 ci) (pkSet (lt3uE Q x.1) rb ∪ pkSet (lt3uE Q x.1) x.2) with hU
  have hUc : 2 ≤ U.card := by
    rw [hU, pkSet_eq_map, pkSet_eq_map, ← map_union, ← map_insert, card_map]; exact h2
  have hU1 : U ⊆ lt3uS Q x.1 :=
    insert_subset (lt3uE_mem Q _ _) (union_subset (lt3_pkSet_sub Q _ _) (lt3_pkSet_sub Q _ _))
  have hU2 : U ⊆ lt3uS Q x'.1 := by
    rw [hU, hi, hR, hT]
    exact insert_subset (lt3uE_mem Q _ _) (union_subset (lt3_pkSet_sub Q _ _) (lt3_pkSet_sub Q _ _))
  have hp : x.1 = x'.1 := lt3u_sub_inj Q hUc hU1 hU2
  rw [← hp] at hT
  exact Prod.ext hp (lt3_pkSet_inj _ hT)

/-! #### Adverse sets -/

/-- Adverse indices of the `m_T` family (level `lt2κ σ_N`). -/
noncomputable def lt3AdvM (w : Param N) : Finset ((Fin (qM Q) × Fin (qM Q)) × Fin (2 ^ 3)) :=
  (lt3Pm Q).filter fun x => lt2κ * sigN N ≤ |lt2mT w (pkSet (lt3uE Q x.1) x.2)|

/-- Adverse indices of the `Õ` family. -/
noncomputable def lt3AdvO (w : Param N) : Finset (((Fin (qM Q) × Fin (qM Q)) × Fin 3) × Fin (2 ^ 3)) :=
  (lt3Po Q).filter fun x => lt2κ * sigN N ≤ |lt2Ot w (lt3uE Q x.1.1 x.1.2, pkSet (lt3uE Q x.1.1) x.2)|

/-- Adverse indices of an `Ñ` family. -/
noncomputable def lt3AdvN (ci : Fin 3) (rb : Fin (2 ^ 3)) (β : Bool) (w : Param N) :
    Finset ((Fin (qM Q) × Fin (qM Q)) × Fin (2 ^ 3)) :=
  (lt3Pn Q ci rb).filter fun x => lt2κ * sigN N ≤
    |lt2N0 (lt3LamOf Q (lt3LamT rb)) β w (lt3uE Q x.1 ci, pkSet (lt3uE Q x.1) rb, pkSet (lt3uE Q x.1) x.2)|

/-- Members with a large `G` at `w` (level `5/2 κσ_N`). -/
noncomputable def lt3Bad (κ : ℝ) (w : Param N) : Finset (Fin (qM Q) × Fin (qM Q)) := by
  classical exact univ.filter fun p => ∃ i ∈ lt3uS Q p, ∃ R ⊆ lt3uS Q p, ∃ T ⊆ lt3uS Q p, T.Nonempty ∧
    5 / 2 * (κ * sigN N) < |lt2G w i R T|

end Fam

/-- Units with an adverse unit-level statistic (level `κσ_N`). -/
noncomputable def lt3UA (κ : ℝ) (w : Param N) : Finset (Fin N) := by
  classical exact univ.filter fun x => κ * sigN N ≤ |lt2mT w {x}| ∨ κ * sigN N ≤ |lt2Ot w (x, {x})| ∨
    κ * sigN N ≤ |lt2N0 univ true w (x, {x}, {x})| ∨ κ * sigN N ≤ |lt2N0 univ false w (x, {x}, {x})|

/-! ### The deterministic link: small statistics give small `G` -/

/-- **Small statistics give small `G`**: if every unit-level statistic of the member's units is `< κσ` and every
member-specific statistic is `< lt2κ σ ≤ κσ`, then every `|G_{i,R}(T)|` (`R, T ⊆ S`, `T ≠ ∅`) is `≤ 5/2 κσ`. -/
theorem lt3_G_of_good (Q : Finset (Fin N)) (w : Param N) {κ : ℝ} (hκ : lt2κ ≤ κ)
    (p : Fin (qM Q) × Fin (qM Q))
    (hU : ∀ x ∈ lt3uS Q p, |lt2mT w {x}| < κ * sigN N ∧ |lt2Ot w (x, {x})| < κ * sigN N ∧
      ∀ β, |lt2N0 univ β w (x, {x}, {x})| < κ * sigN N)
    (hMm : ∀ u, (p, u) ∈ lt3Pm Q → |lt2mT w (pkSet (lt3uE Q p) u)| < lt2κ * sigN N)
    (hMo : ∀ ci u, ((p, ci), u) ∈ lt3Po Q → |lt2Ot w (lt3uE Q p ci, pkSet (lt3uE Q p) u)| < lt2κ * sigN N)
    (hMn : ∀ ci rb u β, rb ≠ 0 → (p, u) ∈ lt3Pn Q ci rb →
      |lt2N0 (lt3LamOf Q (lt3LamT rb)) β w (lt3uE Q p ci, pkSet (lt3uE Q p) rb, pkSet (lt3uE Q p) u)| <
        lt2κ * sigN N) :
    ∀ i ∈ lt3uS Q p, ∀ R ⊆ lt3uS Q p, ∀ T ⊆ lt3uS Q p, T.Nonempty → |lt2G w i R T| ≤ 5 / 2 * (κ * sigN N) := by
  intro i hi R hR T hT hTne
  have hσ : 0 ≤ sigN N := by unfold sigN; positivity
  have hκσ : lt2κ * sigN N ≤ κ * sigN N := mul_le_mul_of_nonneg_right hκ hσ
  obtain ⟨ci, rfl⟩ := (lt3uS_spec Q p i).1 hi
  obtain ⟨rb, rfl⟩ := lt3_pkSet_surj (lt3uE Q p) (lt3uS_spec Q p) hR
  obtain ⟨tb, rfl⟩ := lt3_pkSet_surj (lt3uE Q p) (lt3uS_spec Q p) hT
  have htb : tb ≠ 0 := by
    rintro rfl; rw [pkSet_zero] at hTne; exact Finset.not_nonempty_empty hTne
  have hmT : |lt2mT w (pkSet (lt3uE Q p) tb)| ≤ κ * sigN N := by
    by_cases h2 : 2 ≤ (lt3bits tb).card
    · exact (hMm tb (mem_filter.2 ⟨mem_univ _, h2⟩)).le.trans hκσ
    · obtain ⟨q, hq⟩ := lt3_F1 tb htb h2
      rw [lt3_pkSet_single (lt3uE Q p) hq]
      exact (hU (lt3uE Q p q) (lt3uE_mem Q p q)).1.le
  have hm0 := abs_nonneg (lt2mT w (pkSet (lt3uE Q p) tb))
  by_cases hrb : rb = 0
  · subst hrb
    rw [pkSet_zero, lt2G_empty]
    have hOt : |lt2Ot w (lt3uE Q p ci, pkSet (lt3uE Q p) tb)| ≤ κ * sigN N := by
      by_cases h2 : 2 ≤ (insert ci (lt3bits tb)).card
      · exact (hMo ci tb (mem_filter.2 ⟨mem_univ _, htb, h2⟩)).le.trans hκσ
      · have hq := lt3_F2 ci tb htb h2
        rw [lt3_pkSet_single (lt3uE Q p) hq]
        exact (hU (lt3uE Q p ci) (lt3uE_mem Q p ci)).2.1.le
    have h1 : |3 / 4 * lt2mT w (pkSet (lt3uE Q p) tb) + lt2Ot w (lt3uE Q p ci, pkSet (lt3uE Q p) tb)| ≤
        3 / 4 * |lt2mT w (pkSet (lt3uE Q p) tb)| + |lt2Ot w (lt3uE Q p ci, pkSet (lt3uE Q p) tb)| := by
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
    linarith
  · rw [lt2G_shift w (lt3LamOf Q (lt3LamT rb))]
    have hN0 : ∀ β, |lt2N0 (lt3LamOf Q (lt3LamT rb)) β w
        (lt3uE Q p ci, pkSet (lt3uE Q p) rb, pkSet (lt3uE Q p) tb)| ≤ κ * sigN N := by
      intro β
      by_cases h2 : 2 ≤ (insert ci (lt3bits rb ∪ lt3bits tb)).card
      · exact (hMn ci rb tb β hrb (mem_filter.2 ⟨mem_univ _, htb, h2⟩)).le.trans hκσ
      · obtain ⟨hr, ht⟩ := lt3_F3 ci rb tb hrb htb h2
        have hT0 : lt3LamT rb = 0 := by unfold lt3LamT; rw [hr, card_singleton, if_pos (by norm_num)]
        have hL : lt3LamOf Q (0 : Fin 3) = univ := by unfold lt3LamOf; rw [if_pos rfl]
        rw [hT0, hL, lt3_pkSet_single (lt3uE Q p) hr, lt3_pkSet_single (lt3uE Q p) ht]
        exact ((hU (lt3uE Q p ci) (lt3uE_mem Q p ci)).2.2 β).le
    have h2 := hN0 true
    have h3 := hN0 false
    have h4 := abs_add_le (1 / 2 * lt2mT w (pkSet (lt3uE Q p) tb) + lt2N0 (lt3LamOf Q (lt3LamT rb)) true w
      (lt3uE Q p ci, pkSet (lt3uE Q p) rb, pkSet (lt3uE Q p) tb)) (lt2N0 (lt3LamOf Q (lt3LamT rb)) false w
      (lt3uE Q p ci, pkSet (lt3uE Q p) rb, pkSet (lt3uE Q p) tb))
    have h5 := abs_add_le (1 / 2 * lt2mT w (pkSet (lt3uE Q p) tb)) (lt2N0 (lt3LamOf Q (lt3LamT rb)) true w
      (lt3uE Q p ci, pkSet (lt3uE Q p) rb, pkSet (lt3uE Q p) tb))
    have h6 : |1 / 2 * lt2mT w (pkSet (lt3uE Q p) tb)| = 1 / 2 * |lt2mT w (pkSet (lt3uE Q p) tb)| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith

/-! ### Counting the bad members -/

section Count

variable (Q : Finset (Fin N))

/-- Members containing an adverse unit. -/
noncomputable def lt3BadU (κ : ℝ) (w : Param N) : Finset (Fin (qM Q) × Fin (qM Q)) := by
  classical exact univ.filter fun p => ∃ x ∈ lt3UA κ w, x ∈ lt3uS Q p

/-- Members owning an adverse `m_T`. -/
noncomputable def lt3BadM (w : Param N) : Finset (Fin (qM Q) × Fin (qM Q)) :=
  (lt3AdvM Q w).image fun x : (Fin (qM Q) × Fin (qM Q)) × Fin (2 ^ 3) => x.1

/-- Members owning an adverse `Õ`. -/
noncomputable def lt3BadO (w : Param N) : Finset (Fin (qM Q) × Fin (qM Q)) :=
  (lt3AdvO Q w).image fun x : ((Fin (qM Q) × Fin (qM Q)) × Fin 3) × Fin (2 ^ 3) => x.1.1

/-- Members owning an adverse `Ñ` (some column position, nonzero shift, parity). -/
noncomputable def lt3BadN (w : Param N) : Finset (Fin (qM Q) × Fin (qM Q)) :=
  (univ : Finset (Fin 3)).biUnion fun ci =>
    (univ.filter fun rb : Fin (2 ^ 3) => rb ≠ 0).biUnion fun rb =>
      (univ : Finset Bool).biUnion fun β =>
        (lt3AdvN Q ci rb β w).image fun x : (Fin (qM Q) × Fin (qM Q)) × Fin (2 ^ 3) => x.1

/-- **Bad members own an adverse statistic.** -/
lemma lt3_bad_sub (w : Param N) {κ : ℝ} (hκ : lt2κ ≤ κ) :
    lt3Bad Q κ w ⊆ lt3BadU Q κ w ∪ lt3BadM Q w ∪ lt3BadO Q w ∪ lt3BadN Q w := by
  classical
  intro p hp
  by_contra hcon
  simp only [mem_union, not_or] at hcon
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcon
  have hp' := (mem_filter.1 hp).2
  obtain ⟨i, hi, R, hR, T, hT, hTne, hG⟩ := hp'
  have hgood := lt3_G_of_good Q w hκ p
    (fun x hx => by
      have hxU : x ∉ lt3UA κ w := fun hxU => h1 (by
        unfold lt3BadU; exact mem_filter.2 ⟨mem_univ _, x, hxU, hx⟩)
      have hxU' : ¬ (κ * sigN N ≤ |lt2mT w {x}| ∨ κ * sigN N ≤ |lt2Ot w (x, {x})| ∨
          κ * sigN N ≤ |lt2N0 univ true w (x, {x}, {x})| ∨ κ * sigN N ≤ |lt2N0 univ false w (x, {x}, {x})|) :=
        fun h => hxU (by unfold lt3UA; exact mem_filter.2 ⟨mem_univ _, h⟩)
      push Not at hxU'
      obtain ⟨a1, a2, a3, a4⟩ := hxU'
      exact ⟨a1, a2, fun β => by cases β; exact a4; exact a3⟩)
    (fun u hu => by
      by_contra hc
      push Not at hc
      exact h2 (by unfold lt3BadM; exact mem_image.2 ⟨(p, u), mem_filter.2 ⟨hu, hc⟩, rfl⟩))
    (fun ci u hu => by
      by_contra hc
      push Not at hc
      exact h3 (by unfold lt3BadO; exact mem_image.2 ⟨((p, ci), u), mem_filter.2 ⟨hu, hc⟩, rfl⟩))
    (fun ci rb u β hrb hu => by
      by_contra hc
      push Not at hc
      exact h4 (by
        unfold lt3BadN
        exact mem_biUnion.2 ⟨ci, mem_univ _, mem_biUnion.2 ⟨rb, mem_filter.2 ⟨mem_univ _, hrb⟩,
          mem_biUnion.2 ⟨β, mem_univ _, mem_image.2 ⟨(p, u), mem_filter.2 ⟨hu, hc⟩, rfl⟩⟩⟩⟩))
    i hi R hR T hT hTne
  linarith

lemma lt3BadU_card (κ : ℝ) (w : Param N) : (lt3BadU Q κ w).card ≤ 3 * qM Q * (lt3UA κ w).card := by
  classical
  have hs : lt3BadU Q κ w ⊆ (lt3UA κ w).biUnion fun x =>
      (univ : Finset (Fin (qM Q) × Fin (qM Q))).filter fun p => x ∈ lt3uS Q p := by
    intro p hp
    unfold lt3BadU at hp
    obtain ⟨x, hx, hxp⟩ := (mem_filter.1 hp).2
    exact mem_biUnion.2 ⟨x, hx, mem_filter.2 ⟨mem_univ _, hxp⟩⟩
  calc (lt3BadU Q κ w).card ≤ _ := card_le_card hs
    _ ≤ ∑ x ∈ lt3UA κ w, ((univ : Finset (Fin (qM Q) × Fin (qM Q))).filter fun p => x ∈ lt3uS Q p).card :=
        card_biUnion_le
    _ ≤ ∑ _x ∈ lt3UA κ w, 3 * qM Q := Finset.sum_le_sum fun x _ => lt3u_card_mem Q x
    _ = 3 * qM Q * (lt3UA κ w).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

lemma lt3BadN_card (w : Param N) : (lt3BadN Q w).card ≤
    ∑ ci : Fin 3, ∑ rb ∈ (univ.filter fun rb : Fin (2 ^ 3) => rb ≠ 0), ∑ β : Bool, (lt3AdvN Q ci rb β w).card := by
  unfold lt3BadN
  refine card_biUnion_le.trans (Finset.sum_le_sum fun ci _ => ?_)
  refine card_biUnion_le.trans (Finset.sum_le_sum fun rb _ => ?_)
  exact card_biUnion_le.trans (Finset.sum_le_sum fun β _ => card_image_le)

/-- **The bad members are few**: `#Bad ≤ 3m |UA| + |AdvM| + |AdvO| + Σ_{i, R ≠ ∅, β} |AdvN|`. -/
theorem lt3_bad_card (w : Param N) {κ : ℝ} (hκ : lt2κ ≤ κ) :
    (lt3Bad Q κ w).card ≤ 3 * qM Q * (lt3UA κ w).card + (lt3AdvM Q w).card + (lt3AdvO Q w).card +
      ∑ ci : Fin 3, ∑ rb ∈ (univ.filter fun rb : Fin (2 ^ 3) => rb ≠ 0), ∑ β : Bool, (lt3AdvN Q ci rb β w).card := by
  have h0 := card_le_card (lt3_bad_sub Q w hκ)
  have h1 := card_union_le (lt3BadU Q κ w ∪ lt3BadM Q w ∪ lt3BadO Q w) (lt3BadN Q w)
  have h2 := card_union_le (lt3BadU Q κ w ∪ lt3BadM Q w) (lt3BadO Q w)
  have h3 := card_union_le (lt3BadU Q κ w) (lt3BadM Q w)
  have h4 := lt3BadU_card Q κ w
  have h5 : (lt3BadM Q w).card ≤ (lt3AdvM Q w).card := card_image_le
  have h6 : (lt3BadO Q w).card ≤ (lt3AdvO Q w).card := card_image_le
  have h7 := lt3BadN_card Q w
  omega

end Count

/-- `|UA| ≤` the sum of the four unit counts. -/
lemma lt3UA_card (κ : ℝ) (w : Param N) : (lt3UA κ w).card ≤
    (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2mT w {x}|).card +
    (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2Ot w (x, {x})|).card +
    (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2N0 univ true w (x, {x}, {x})|).card +
    (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2N0 univ false w (x, {x}, {x})|).card := by
  classical
  have hs : lt3UA κ w ⊆ (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2mT w {x}|) ∪
      (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2Ot w (x, {x})|) ∪
      (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2N0 univ true w (x, {x}, {x})|) ∪
      (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2N0 univ false w (x, {x}, {x})|) := by
    intro x hx
    unfold lt3UA at hx
    have h := (mem_filter.1 hx).2
    simp only [mem_union, mem_filter, mem_univ, true_and]
    tauto
  have h0 := card_le_card hs
  have h1 := card_union_le ((univ.filter fun x : Fin N => κ * sigN N ≤ |lt2mT w {x}|) ∪
      (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2Ot w (x, {x})|) ∪
      (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2N0 univ true w (x, {x}, {x})|))
    (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2N0 univ false w (x, {x}, {x})|)
  have h2 := card_union_le ((univ.filter fun x : Fin N => κ * sigN N ≤ |lt2mT w {x}|) ∪
      (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2Ot w (x, {x})|))
    (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2N0 univ true w (x, {x}, {x})|)
  have h3 := card_union_le (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2mT w {x}|)
    (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2Ot w (x, {x})|)
  omega

/-! ### Adverse members at `w½` are bad at `w` -/

/-- **Adverse members at `w½` are bad at `w`** when the perturbation is `≤ κσ_N/2`. -/
theorem lt3_adv_sub_bad (s : State N) (ε γ : ℝ) (n : ℕ) (w : Param N) {κ : ℝ}
    (hpert : 2 * lt3PE s ε γ n w ≤ κ * sigN N / 2) :
    lt3Adv s ε γ n κ w ⊆ (lt3Bad (lt3WQ s ε γ n w) κ w).image (lt3uS (lt3WQ s ε γ n w)) := by
  classical
  intro S hS
  unfold lt3Adv at hS
  obtain ⟨hSF, i, hi, R, hR, T, hT, hTne, hG⟩ := mem_filter.1 hS
  have hSQ : S ∈ qFam (lt3WQ s ε γ n w) := by unfold lt3WF at hSF; exact (mem_filter.1 hSF).1
  rw [qFam_eq_image] at hSQ
  obtain ⟨p, -, rfl⟩ := mem_image.1 hSQ
  refine mem_image.2 ⟨p, ?_, rfl⟩
  unfold lt3Bad
  refine mem_filter.2 ⟨mem_univ _, i, hi, R, hR, T, hT, hTne, ?_⟩
  have hp := lt3G_pert s ε γ n w i R T
  have h1 := abs_sub_abs_le_abs_sub (lt2G (lt3Hf s ε γ n w) i R T) (lt2G w i R T)
  rw [abs_sub_comm] at h1
  linarith

lemma lt3_adv_card (s : State N) (ε γ : ℝ) (n : ℕ) (w : Param N) {κ : ℝ}
    (hpert : 2 * lt3PE s ε γ n w ≤ κ * sigN N / 2) :
    (lt3Adv s ε γ n κ w).card ≤ (lt3Bad (lt3WQ s ε γ n w) κ w).card :=
  (card_le_card (lt3_adv_sub_bad s ε γ n w hpert)).trans card_image_le

/-! ### The good events -/

/-- Member-specific counts below `m²/352 + 1` (all 44 families). -/
def lt3MemGood (Q : Finset (Fin N)) (w : Param N) : Prop :=
  (lt3AdvM Q w).card < qM Q * qM Q / 352 + 1 ∧ (lt3AdvO Q w).card < qM Q * qM Q / 352 + 1 ∧
    ∀ ci rb, rb ≠ 0 → ∀ β, (lt3AdvN Q ci rb β w).card < qM Q * qM Q / 352 + 1

/-- Unit-level counts below `m₃`. -/
def lt3UnitGood (κ : ℝ) (m3 : ℕ) (w : Param N) : Prop :=
  (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2mT w {x}|).card < m3 ∧
  (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2Ot w (x, {x})|).card < m3 ∧
  (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2N0 univ true w (x, {x}, {x})|).card < m3 ∧
  (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2N0 univ false w (x, {x}, {x})|).card < m3

lemma lt3_nz_card : (univ.filter fun rb : Fin (2 ^ 3) => rb ≠ 0).card = 7 := by decide

/-- **On the good events at most `m²/4` members are bad** (`96 (m₃ - 1) ≤ m`). -/
theorem lt3_bad_quarter (Q : Finset (Fin N)) (w : Param N) {κ : ℝ} (hκ : lt2κ ≤ κ) {m3 : ℕ}
    (hm3 : 96 * (m3 - 1) ≤ qM Q) (hM : lt3MemGood Q w) (hU : lt3UnitGood κ m3 w) :
    4 * (lt3Bad Q κ w).card ≤ qM Q * qM Q := by
  classical
  have hB := lt3_bad_card Q w hκ
  have hUA := lt3UA_card κ w
  obtain ⟨hu1, hu2, hu3, hu4⟩ := hU
  obtain ⟨hM1, hM2, hM3⟩ := hM
  have hN3 : (∑ ci : Fin 3, ∑ rb ∈ (univ.filter fun rb : Fin (2 ^ 3) => rb ≠ 0), ∑ β : Bool,
      (lt3AdvN Q ci rb β w).card) ≤ 42 * (qM Q * qM Q / 352) := by
    calc _ ≤ ∑ _ci : Fin 3, ∑ _rb ∈ (univ.filter fun rb : Fin (2 ^ 3) => rb ≠ 0), ∑ _β : Bool,
          qM Q * qM Q / 352 := by
          refine Finset.sum_le_sum fun ci _ => Finset.sum_le_sum fun rb hrb => Finset.sum_le_sum fun β _ => ?_
          have := hM3 ci rb (mem_filter.1 hrb).2 β
          omega
      _ = 42 * (qM Q * qM Q / 352) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.sum_const, lt3_nz_card]
          simp only [Finset.card_univ, Fintype.card_bool, Fintype.card_fin, smul_eq_mul]
          ring
  have hUA' : (lt3UA κ w).card ≤ 4 * (m3 - 1) := by omega
  have hk1 : 3 * qM Q * (lt3UA κ w).card ≤ 3 * qM Q * (4 * (m3 - 1)) := Nat.mul_le_mul_left _ hUA'
  have hk2 : 96 * (qM Q * (m3 - 1)) ≤ qM Q * qM Q := by
    calc 96 * (qM Q * (m3 - 1)) = qM Q * (96 * (m3 - 1)) := by ring
      _ ≤ qM Q * qM Q := Nat.mul_le_mul_left _ hm3
  have hk3 : 352 * (qM Q * qM Q / 352) ≤ qM Q * qM Q := Nat.mul_div_le (qM Q * qM Q) 352
  have hk4 : 3 * qM Q * (4 * (m3 - 1)) = 12 * (qM Q * (m3 - 1)) := by ring
  omega

end Census
end IIT
