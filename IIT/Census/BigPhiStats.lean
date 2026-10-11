/-
Census of complexes: the statistics behind the bound on `Φ` of the maximal complex.

Everything is written in flipped coordinates `w : Param N` (for a state `s`, `w = flipP s z`), where
the probability that row `r` produces the current bit of unit `j` is `clamp01 (w r j)`.  The row
product `Pw`, the row product without column `i` (`Qw`), subcube sums of `Qw`, the conditioned cause
numerators `Num` and their means `cNum` given the other columns are polynomials in these entries.
`GoodW` collects the bounds that hold with probability tending to one.
-/
import IIT.Census.Basic

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-! ## Constants -/

/-- `σ_N = (2/3)^(N/2)`, the fluctuation scale of the cause side. -/
noncomputable def sigN (N : ℕ) : ℝ := Real.sqrt ((2 / 3 : ℝ) ^ N)

/-- The largest row product without one column, `e^{-(2/9)(N-1)}`. -/
noncomputable def tauN (N : ℕ) : ℝ := Real.exp (-(2 / 9) * ((N : ℝ) - 1))

/-- The union-bound level for candidates of size `k`. -/
noncomputable def LkN (N k : ℕ) : ℝ := (k : ℝ) * Real.log N + 3 * k + 2 * Real.log N

/-- The size threshold `2 log₂ log₂ N + 4` for the maximal complex. -/
def KN (N : ℕ) : ℕ := 2 * Nat.log 2 (Nat.log 2 N) + 4

/-- Candidates larger than `K2N N` are near the whole substrate. -/
def K2N (N : ℕ) : ℕ := N - (4 * Nat.log 2 N + 16)

/-- The rate in the bound on `Φ` of the maximal complex. -/
noncomputable def rateN (N : ℕ) : ℝ := Real.exp (2 ^ (KN N + 1)) * sigN N

/-- The number of states at Hamming distance `1, …, k` from a given state. -/
def vk (N k : ℕ) : ℕ := ∑ j ∈ Icc 1 k, N.choose j

/-! ## Statistics -/

/-- Row product. -/
noncomputable def Pw (w : Param N) (r : State N) : ℝ := ∏ j, clamp01 (w r j)

/-- Row product without column `i`. -/
noncomputable def Qw (w : Param N) (i : Fin N) (r : State N) : ℝ :=
  ∏ j ∈ univ.erase i, clamp01 (w r j)

/-- Sum of the row products. -/
noncomputable def Zs (w : Param N) : ℝ := ∑ r, Pw w r

/-- Sum of the row products without column `i`. -/
noncomputable def ZQ (w : Param N) (i : Fin N) : ℝ := ∑ r, Qw w i r

/-- Sum of the squared row products without column `i`. -/
noncomputable def SQ2 (w : Param N) (i : Fin N) : ℝ := ∑ r, Qw w i r ^ 2

/-- `Qw`-mass of the subcube of rows agreeing with `m` on `M` (dimension `N - |M|`). -/
noncomputable def subSum (w : Param N) (i : Fin N) (M : Finset (Fin N)) (m : State N) : ℝ :=
  ∑ r ∈ agree M m, Qw w i r

/-- `Qw`-mass of the `S`-block of `r`: the `2^|S|` rows agreeing with `r` off `S`. -/
noncomputable def blockQ (w : Param N) (i : Fin N) (S : Finset (Fin N)) (r : State N) : ℝ :=
  subSum w i Sᶜ r

/-- The variance proxy `∑_blocks (Qw-mass)^2`, written row by row. -/
noncomputable def Vp (w : Param N) (i : Fin N) (S : Finset (Fin N)) : ℝ :=
  ∑ r, Qw w i r * blockQ w i S r

/-- Mean of column `i` over the rows with pattern `t` on `Y` and background `v` off `S`. -/
noncomputable def meanW (w : Param N) (S Y : Finset (Fin N)) (t : State N) (i : Fin N)
    (v : State N) : ℝ :=
  (∑ r ∈ agree (Y ∪ Sᶜ) (merge S t v), clamp01 (w r i)) / (2 : ℝ) ^ (S.card - Y.card)

/-- The conditioned cause numerator of unit `i` for the candidate `S` and purview pattern `t|Y`. -/
noncomputable def Num (w : Param N) (S Y : Finset (Fin N)) (t : State N) (i : Fin N) : ℝ :=
  ∑ v, meanW w S Y t i v * Pw w v

/-- The mean of `Num` given all columns except column `i`. -/
noncomputable def cNum (w : Param N) (S Y : Finset (Fin N)) (t : State N) (i : Fin N) : ℝ :=
  ZQ w i / 4 + subSum w i Y t / (12 * (2 : ℝ) ^ (S.card - Y.card))

/-- Twelve times the difference of two conditional means. -/
noncomputable def DQ (w : Param N) (S Y Y' : Finset (Fin N)) (t : State N) (i : Fin N) : ℝ :=
  subSum w i Y t / (2 : ℝ) ^ (S.card - Y.card) - subSum w i Y' t / (2 : ℝ) ^ (S.card - Y'.card)

/-- Hamming distance. -/
def ham (r r' : State N) : ℕ := (univ.filter fun j => r j ≠ r' j).card

/-- Products of `Qw` over pairs of rows at Hamming distance `1, …, k`. -/
noncomputable def Xk (w : Param N) (k : ℕ) (i : Fin N) : ℝ :=
  ∑ r, ∑ r' ∈ univ.filter (fun r' => 1 ≤ ham r r' ∧ ham r r' ≤ k), Qw w i r * Qw w i r'

/-- The effect-side cut mean of unit `j`: the mean, over the rows of the `S`-block of `s` that agree
with `s` on `j`, of the probability that `j` takes the value `b`. -/
noncomputable def qW (w : Param N) (s : State N) (S : Finset (Fin N)) (j : Fin N) (b : Bool) : ℝ :=
  (∑ r ∈ agree (S.erase j)ᶜ s,
      (if b = s j then clamp01 (w r j) else 1 - clamp01 (w r j))) / (2 : ℝ) ^ (S.card - 1)

/-- The largest probability of any next state from the current state `s`. -/
noncomputable def Mrow (w : Param N) (s : State N) : ℝ :=
  ∏ i, max (clamp01 (w s i)) (1 - clamp01 (w s i))

/-! ## The good event -/

/-- The bounds on the statistics that hold with probability tending to one. -/
structure GoodW (N : ℕ) (s : State N) (w : Param N) : Prop where
  g2 : ∀ i r, Qw w i r ≤ tauN N
  g3 : 1 / 2 ≤ Zs w ∧ Zs w ≤ 2 ∧ ∀ i, ZQ w i ≤ 3
  g4 : ∀ i, SQ2 w i ≤ 6 * (2 / 3 : ℝ) ^ N
  g6 : ∀ i (M : Finset (Fin N)) (m : State N), subSum w i M m ≤
      (2 : ℝ) ^ (N - M.card) * (1 / 2 : ℝ) ^ (N - 1)
        + 16 * N * (Real.sqrt ((2 : ℝ) ^ (N - M.card) * (1 / 3 : ℝ) ^ (N - 1)) + tauN N)
  g11 : ∀ i, |Zs w - ZQ w i / 2| ≤ 16 * N * sigN N
  g12 : ∀ k i, Xk w k i ≤ 4 * (N : ℝ) ^ 3 * vk N k * (1 / 2 : ℝ) ^ N
  g13a : ∀ (S : Finset (Fin N)) i (Y : Finset (Fin N)) t, i ∈ S → Y ⊆ S →
      |Num w S Y t i - cNum w S Y t i| ≤ 2 * Real.sqrt (LkN N S.card * Vp w i S)
  g13b : ∀ (S : Finset (Fin N)) i (Y Y' : Finset (Fin N)) t, i ∈ S → Y ⊆ S → Y' ⊆ S →
      |DQ w S Y Y' t i| ≤ 16 * LkN N S.card * (Real.sqrt 3 * sigN N + tauN N)
  g16 : ∀ (S : Finset (Fin N)) j b, j ∈ S → K2N N < S.card → 1 / 4 ≤ qW w s S j b
  gU : Mrow w s ≤ (4 / 5 : ℝ) ^ N

/-! ## Basic facts -/

lemma Pw_nonneg (w : Param N) (r : State N) : 0 ≤ Pw w r :=
  prod_nonneg fun _ _ => clamp01_nonneg _

lemma Qw_nonneg (w : Param N) (i : Fin N) (r : State N) : 0 ≤ Qw w i r :=
  prod_nonneg fun _ _ => clamp01_nonneg _

lemma Pw_eq_mul_Qw (w : Param N) (i : Fin N) (r : State N) :
    Pw w r = clamp01 (w r i) * Qw w i r := by
  rw [Pw, Qw]
  exact (Finset.mul_prod_erase univ (fun j => clamp01 (w r j)) (mem_univ i)).symm

lemma subSum_nonneg (w : Param N) (i : Fin N) (M : Finset (Fin N)) (m : State N) :
    0 ≤ subSum w i M m :=
  sum_nonneg fun r _ => Qw_nonneg w i r

lemma blockQ_nonneg (w : Param N) (i : Fin N) (S : Finset (Fin N)) (r : State N) :
    0 ≤ blockQ w i S r :=
  subSum_nonneg w i _ r

lemma Vp_nonneg (w : Param N) (i : Fin N) (S : Finset (Fin N)) : 0 ≤ Vp w i S :=
  sum_nonneg fun r _ => mul_nonneg (Qw_nonneg w i r) (blockQ_nonneg w i S r)

lemma ZQ_nonneg (w : Param N) (i : Fin N) : 0 ≤ ZQ w i :=
  sum_nonneg fun r _ => Qw_nonneg w i r

lemma Zs_nonneg (w : Param N) : 0 ≤ Zs w :=
  sum_nonneg fun r _ => Pw_nonneg w r

lemma meanW_nonneg (w : Param N) (S Y : Finset (Fin N)) (t : State N) (i : Fin N) (v : State N) :
    0 ≤ meanW w S Y t i v :=
  div_nonneg (sum_nonneg fun r _ => clamp01_nonneg _) (by positivity)

lemma Num_nonneg (w : Param N) (S Y : Finset (Fin N)) (t : State N) (i : Fin N) :
    0 ≤ Num w S Y t i :=
  sum_nonneg fun v _ => mul_nonneg (meanW_nonneg w S Y t i v) (Pw_nonneg w v)

lemma sigN_pos (N : ℕ) : 0 < sigN N := Real.sqrt_pos.2 (by positivity)

lemma tauN_pos (N : ℕ) : 0 < tauN N := Real.exp_pos _

end Census
end IIT
