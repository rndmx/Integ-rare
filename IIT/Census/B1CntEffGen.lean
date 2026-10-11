/-
Census, B1, W14 work package WP3 (effect side), part 2: generic facts about the effect side of a
mechanism (any `T`), used by the te-specific lemmas.
* `phiEatAt_le_total` (W5 Fact E0(a)): `φ_e` at the MIP is at most `φ_e` at the total cut;
* `uncEffRep_single`: at a one-unit purview the unconstrained repertoire is the column mean;
* `phiEofPartition_total`: the total cut replaces every factor by its column mean;
* `phiEat_single_of_gt`: at a one-unit purview, if every partition that keeps part of the
  mechanism has a strictly larger normalised value than the total cut, `φ_e` is the total-cut value.
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §8.  No `sorry`.
-/
import IIT.Census.B1CntBasics

namespace IIT
namespace Census

/-! Helpers live in `IIT.Census.WP3` (avoids name clashes with the other work packages);
the blueprint names are re-exported to `IIT.Census` by `alias` at the end of the file. -/
namespace WP3

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-- **Fact E0(a).** -/
theorem phiEatAt_le_total (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) (Z : Finset (Fin N)) (z : State N) (hM : M.Nonempty)
    (hZ : Z.Nonempty) :
    phiEatAt T S u M m Z z ≤ phiEofPartitionAt T S u M m Z z (Partition.total hM Z) := by
  set θ0 := Partition.total hM Z with hθ0
  have h0 := phiEofPartitionAt_nonneg T S u M m Z z θ0
  refine sup'OrZero_le h0 fun θ hθ => ?_
  have hmin := (mem_argminSet.1 hθ) θ0
  unfold normalizedPhiAt at hmin
  rw [hθ0, cutCount_total] at hmin
  have hcc : (0 : ℝ) < cutCount M Z θ := by exact_mod_cast cutCount_pos hZ θ
  have hle : (cutCount M Z θ : ℝ) ≤ ((M.card * Z.card : ℕ) : ℝ) := by
    exact_mod_cast cutCount_le M Z θ
  have hMZ : (0 : ℝ) < ((M.card * Z.card : ℕ) : ℝ) := by
    have := card_pos.2 hM; have := card_pos.2 hZ; positivity
  rw [div_le_div_iff₀ hcc hMZ] at hmin
  have hφ := phiEofPartitionAt_nonneg T S u M m Z z θ
  rw [← hθ0] at hmin
  nlinarith

/-- The sum of `effUnit` over all mechanism states is `2^{N-|M|}` copies of each row. -/
lemma sum_effUnit_all (T : UnitTPM N) (M : Finset (Fin N)) (k : Fin N) (b : Bool) :
    ∑ m' : State N, effUnit T M m' k b = ∑ r : State N, T.prob k r b := by
  have hc : ∀ m' : State N, ((agree M m').card : ℝ) = 2 ^ (N - M.card) := fun m' => by
    rw [card_agree]; push_cast; ring
  have hpos : (0 : ℝ) < 2 ^ (N - M.card) := by positivity
  unfold effUnit
  simp only [hc]
  rw [← sum_div, div_eq_iff hpos.ne']
  have hsym : ∀ r m' : State N, r ∈ agree M m' ↔ m' ∈ agree M r := fun r m' => by
    simp only [mem_agree]; exact ⟨fun h j hj => (h j hj).symm, fun h j hj => (h j hj).symm⟩
  calc ∑ m' : State N, ∑ r ∈ agree M m', T.prob k r b
      = ∑ m' : State N, ∑ r : State N, if m' ∈ agree M r then T.prob k r b else 0 := by
        refine sum_congr rfl fun m' _ => ?_
        rw [← sum_filter]
        refine sum_congr ?_ fun r _ => rfl
        ext r; simp [hsym r m']
    _ = ∑ r : State N, ∑ m' : State N, if m' ∈ agree M r then T.prob k r b else 0 := sum_comm
    _ = ∑ r : State N, T.prob k r b * 2 ^ (N - M.card) := by
        refine sum_congr rfl fun r _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
        congr 1
        have : (univ.filter fun m' : State N => m' ∈ agree M r) = agree M r := by
          ext m'; simp
        rw [this, card_agree]; push_cast; ring
    _ = (∑ r : State N, T.prob k r b) * 2 ^ (N - M.card) := by rw [sum_mul]

lemma effUnit_empty_eq (T : UnitTPM N) (m : State N) (k : Fin N) (b : Bool) :
    effUnit T ∅ m k b = (∑ r : State N, T.prob k r b) / 2 ^ N := by
  unfold effUnit
  have : agree (∅ : Finset (Fin N)) m = univ := by ext r; simp [mem_agree]
  rw [this, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  push_cast; ring

/-- At a one-unit purview the unconstrained effect repertoire is the column mean. -/
theorem uncEffRep_single (T : UnitTPM N) (M : Finset (Fin N)) (k : Fin N) (z m : State N) :
    uncEffRep T M {k} z = effUnit T ∅ m k (z k) := by
  unfold uncEffRep
  simp only [effRep, prod_singleton]
  rw [sum_effUnit_all, effUnit_empty_eq, card_state]
  push_cast; ring

/-- The total cut replaces every factor by its column mean. -/
theorem partEffRep_total (T : UnitTPM N) (M : Finset (Fin N)) (hM : M.Nonempty) (m : State N)
    (Z : Finset (Fin N)) (z : State N) :
    partEffRep T M m Z z (Partition.total hM Z) = ∏ k ∈ Z, effUnit T ∅ m k (z k) :=
  prod_congr rfl fun k hk => by rw [Partition.total_effPart hM Z hk]

lemma sup'OrZero_eq_of_forall {α : Type*} {s : Finset α} {f : α → ℝ} {c : ℝ} (hs : s.Nonempty)
    (h : ∀ a ∈ s, f a = c) : sup'OrZero s f = c := by
  unfold sup'OrZero
  rw [dif_pos hs]
  obtain ⟨a, ha⟩ := hs
  refine le_antisymm (Finset.sup'_le _ _ fun b hb => (h b hb).le) ?_
  rw [← h a ha]; exact Finset.le_sup' f ha

/-- **One-unit purview, MIP = total cut.** -/
theorem phiEat_single_of_gt (T : UnitTPM N) (M : Finset (Fin N)) (hM : M.Nonempty) (m : State N)
    (k : Fin N) (z : State N)
    (hgt : ∀ θ : Partition N M {k}, θ.effPart k ≠ ∅ →
      normalizedPhi T M m {k} z (Partition.total hM {k}) < normalizedPhi T M m {k} z θ) :
    phiEat T M m {k} z = phiEofPartition T M m {k} z (Partition.total hM {k}) := by
  set θ0 := Partition.total hM {k} with hθ0
  have h0k : θ0.effPart k = ∅ := Partition.total_effPart hM {k} (mem_singleton_self k)
  have heq : ∀ θ : Partition N M {k}, θ.effPart k = ∅ → ∀ k' ∈ ({k} : Finset (Fin N)),
      θ.effPart k' = θ0.effPart k' := fun θ hθ k' hk' => by
    rw [mem_singleton] at hk'; subst hk'; rw [hθ, h0k]
  have hmem0 : θ0 ∈ mipSetE T M m {k} z := by
    unfold mipSetE; rw [mem_argminSet]
    intro θ
    by_cases hθ : θ.effPart k = ∅
    · rw [normalizedPhi_congr_effPart (heq θ hθ)]
    · exact (hgt θ hθ).le
  refine sup'OrZero_eq_of_forall ⟨θ0, hmem0⟩ fun θ hθ => ?_
  have hθ' : θ.effPart k = ∅ := by
    by_contra hne
    have h1 := hgt θ hne
    have h2 := (mem_argminSet.1 hθ) θ0
    linarith
  unfold phiEofPartition
  rw [partEffRep_congr_effPart (heq θ hθ') T m z]

end WP3

alias phiEatAt_le_total := WP3.phiEatAt_le_total

end Census
end IIT

#print axioms IIT.Census.phiEatAt_le_total
#print axioms IIT.Census.WP3.uncEffRep_single
#print axioms IIT.Census.WP3.phiEat_single_of_gt
