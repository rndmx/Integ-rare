/-
Census, B1 small cuts (W12 §6): **block Jensen** for subcube means.

For `a ≠ b ∈ K`, the subcube `agree (U \ K) r0` (`2^|K|` states) is the disjoint union of the `2^{|K|-2}` blocks
`agree (U \ {a,b}) p`, `p ∈ P := agree ((U \ K) ∪ {a,b}) r0` (4 states each). Hence the subcube mean is the mean of
the block means and, by convexity of `x ↦ x^n`,
`(mean_K z)^n ≤ mean_p (mean_{block p} z)^n` (`block_jensen`). The block of `r0` contains `r0`; no other block does.
-/
import IIT.Census.B1SmallCutMom

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- Reset the coordinates of `B` to those of `r0`. -/
def rstB (B : Finset (Fin N)) (r0 r : State N) : State N := fun i => if i ∈ B then r0 i else r i

section Blocks

variable (r0 : State N) (K : Finset (Fin N)) {a b : Fin N}

/-- The block representatives. -/
def blkP (a b : Fin N) : Finset (State N) := agree ((univ \ K) ∪ {a, b}) r0

lemma rstB_mem (hab : ({a, b} : Finset (Fin N)) ⊆ K) {r : State N} (hr : r ∈ agree (univ \ K) r0) :
    rstB {a, b} r0 r ∈ blkP r0 K a b := by
  rw [blkP, mem_agree]
  intro i hi
  unfold rstB
  rcases mem_union.1 hi with h | h
  · by_cases hB : i ∈ ({a, b} : Finset (Fin N))
    · rw [if_pos hB]
    · rw [if_neg hB]; exact (mem_agree.1 hr) i h
  · rw [if_pos h]

lemma fiber_eq (hab : ({a, b} : Finset (Fin N)) ⊆ K) {p : State N} (hp : p ∈ blkP r0 K a b) :
    (agree (univ \ K) r0).filter (fun r => rstB {a, b} r0 r = p) = agree (univ \ {a, b}) p := by
  ext r
  simp only [mem_filter, mem_agree, blkP] at hp ⊢
  constructor
  · rintro ⟨hr, rfl⟩ i hi
    unfold rstB
    rw [if_neg (by simpa using hi)]
  · intro hr
    refine ⟨fun i hi => ?_, ?_⟩
    · have hiB : i ∉ ({a, b} : Finset (Fin N)) := fun h => (mem_sdiff.1 hi).2 (hab h)
      rw [hr i (by simpa using hiB)]
      exact hp i (mem_union_left _ hi)
    · funext i
      unfold rstB
      by_cases hB : i ∈ ({a, b} : Finset (Fin N))
      · rw [if_pos hB]; exact (hp i (mem_union_right _ hB)).symm
      · rw [if_neg hB]; exact hr i (by simpa using hB)

lemma card_blkP (hab : ({a, b} : Finset (Fin N)) ⊆ K) (hne : a ≠ b) :
    (blkP r0 K a b).card = 2 ^ (K.card - 2) := by
  rw [blkP, card_agree]
  congr 1
  have h1 : ((univ \ K) ∪ {a, b}).card = (univ \ K).card + 2 := by
    rw [card_union_of_disjoint (disjoint_left.2 fun x hx hx' => (mem_sdiff.1 hx).2 (hab hx')), card_pair hne]
  rw [h1, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
  have := card_le_univ K; rw [Fintype.card_fin] at this
  have h2 := card_le_card hab; rw [card_pair hne] at h2
  omega

lemma card_block (hne : a ≠ b) (p : State N) : (agree (univ \ {a, b}) p).card = 4 := by
  rw [card_agree, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, card_pair hne]
  have : 2 ≤ N := by
    have := card_le_univ ({a, b} : Finset (Fin N)); rw [card_pair hne, Fintype.card_fin] at this; exact this
  rw [show N - (N - 2) = 2 by omega]; norm_num

/-- **Sum over the subcube = sum over blocks.** -/
theorem sum_subcube_blocks (hab : ({a, b} : Finset (Fin N)) ⊆ K) (z : State N → ℝ) :
    ∑ r ∈ agree (univ \ K) r0, z r = ∑ p ∈ blkP r0 K a b, ∑ r ∈ agree (univ \ {a, b}) p, z r := by
  rw [← sum_fiberwise_of_maps_to (fun r hr => rstB_mem r0 K hab hr)]
  exact sum_congr rfl fun p hp => by rw [fiber_eq r0 K hab hp]

lemma r0_mem_blkP : r0 ∈ blkP r0 K a b := self_mem_agree _ _

lemma r0_mem_block : r0 ∈ agree (univ \ ({a, b} : Finset (Fin N))) r0 := self_mem_agree _ _

lemma r0_not_mem_block {p : State N} (hp : p ∈ blkP r0 K a b) (hne : p ≠ r0) :
    r0 ∉ agree (univ \ ({a, b} : Finset (Fin N))) p := by
  intro h
  apply hne
  funext i
  by_cases hB : i ∈ ({a, b} : Finset (Fin N))
  · exact (mem_agree.1 hp) i (mem_union_right _ hB)
  · exact ((mem_agree.1 h) i (by simpa using hB)).symm

/-- **Block Jensen.** -/
theorem block_jensen (hab : ({a, b} : Finset (Fin N)) ⊆ K) (hne : a ≠ b) (z : State N → ℝ)
    (hz : ∀ r, 0 ≤ z r) (n : ℕ) :
    ((∑ r ∈ agree (univ \ K) r0, z r) / 2 ^ K.card) ^ n ≤
      (1 / 2 ^ (K.card - 2)) * ∑ p ∈ blkP r0 K a b, ((∑ r ∈ agree (univ \ {a, b}) p, z r) / 4) ^ n := by
  have h2 := card_le_card hab; rw [card_pair hne] at h2
  have hK : (2 : ℝ) ^ K.card = 2 ^ (K.card - 2) * 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel h2]
  rw [sum_subcube_blocks r0 K hab z]
  set w : State N → ℝ := fun _ => 1 / 2 ^ (K.card - 2) with hw
  have hwP : ∑ p ∈ blkP r0 K a b, w p = 1 := by
    rw [sum_const, card_blkP r0 K hab hne, nsmul_eq_mul]; push_cast; field_simp
  have e : (∑ p ∈ blkP r0 K a b, ∑ r ∈ agree (univ \ {a, b}) p, z r) / 2 ^ K.card =
      ∑ p ∈ blkP r0 K a b, w p * ((∑ r ∈ agree (univ \ {a, b}) p, z r) / 4) := by
    rw [hK, sum_div]; refine sum_congr rfl fun p _ => ?_; rw [hw]; field_simp
  rw [e, mul_sum]
  exact Real.pow_arith_mean_le_arith_mean_pow (blkP r0 K a b) w
    (fun p => (∑ r ∈ agree (univ \ {a, b}) p, z r) / 4) (fun p _ => by rw [hw]; positivity) hwP
    (fun p _ => div_nonneg (sum_nonneg fun r _ => hz r) (by norm_num)) n

end Blocks

end Census
end IIT
