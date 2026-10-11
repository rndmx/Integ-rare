/-
Census, B1 forced leaves, part A3: the Hamming-ball count used by the field `far`:
`#{r : ham r s ≤ k} ≤ 2^k (3/2)^N` (Chernoff with weight `(1/2)^{ham}`).
-/
import IIT.Census.BigPhiStats

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

lemma fa_half_pow_ham (r s : State N) :
    (1 / 2 : ℝ) ^ ham r s = ∏ i, (if r i ≠ s i then (1 / 2 : ℝ) else 1) := by
  rw [prod_ite, prod_const, prod_const_one, mul_one]; rfl

lemma fa_sum_half_pow_ham (s : State N) : ∑ r : State N, (1 / 2 : ℝ) ^ ham r s = (3 / 2) ^ N := by
  simp_rw [fa_half_pow_ham]
  rw [← Fintype.prod_sum (fun i (b : Bool) => if b ≠ s i then (1 / 2 : ℝ) else 1)]
  rw [prod_congr rfl fun i _ => show (∑ b : Bool, if b ≠ s i then (1 / 2 : ℝ) else 1) = 3 / 2 by
    rw [Fintype.sum_bool]; cases s i <;> norm_num]
  simp [div_pow]

lemma fa_card_near (s : State N) (k : ℕ) :
    (((univ : Finset (State N)).filter fun r => ham r s ≤ k).card : ℝ) ≤ 2 ^ k * (3 / 2) ^ N := by
  rw [← fa_sum_half_pow_ham s, mul_sum, card_eq_sum_ones, Nat.cast_sum, sum_filter]
  refine sum_le_sum fun r _ => ?_
  split_ifs with h
  · push_cast
    rw [show (2 : ℝ) ^ k = 2 ^ (k - ham r s) * 2 ^ ham r s by rw [← pow_add]; congr 1; omega,
      mul_assoc, ← mul_pow]
    norm_num
    exact one_le_pow₀ (by norm_num)
  · positivity

end Census
end IIT
