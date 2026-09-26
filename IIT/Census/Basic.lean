/-
Census of complexes: shared definitions (parameter cube, TPM of a parameter vector,
row products and column half-means used by the univ-zero and B2 theorems).
-/
import IIT.System

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- Parameters of a TPM: `z s i` is the probability that unit `i` is ON at `t+1`
given state `s` at `t`. -/
abbrev Param (N : ℕ) := State N → Fin N → ℝ

/-- The unit cube of admissible parameters; `volume` restricted to it is the uniform
probability measure on TPMs (conditionally independent binary units). -/
def cube (N : ℕ) : Set (Param N) := {z | ∀ s i, z s i ∈ Set.Icc (0 : ℝ) 1}

/-- Clamp to `[0,1]`, so that every parameter vector gives a TPM; the identity on the cube. -/
noncomputable def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

lemma clamp01_nonneg (x : ℝ) : 0 ≤ clamp01 x := le_max_left _ _

lemma clamp01_le_one (x : ℝ) : clamp01 x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- The TPM with parameters `z`. -/
noncomputable def tpmOf (z : Param N) : UnitTPM N where
  prob i s b := if b then clamp01 (z s i) else 1 - clamp01 (z s i)
  nonneg i s b := by
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, sub_nonneg]; exact clamp01_le_one _
    · simp only [↓reduceIte]; exact clamp01_nonneg _
  normalized i s := by simp

/-- `φ_s` of candidate `S` for parameters `z`, background equal to the current state. -/
noncomputable def phi (z : Param N) (s : State N) (S : Finset (Fin N)) : ℝ :=
  sysPhi (tpmOf z) S s s

/-- The open cube: all entries strictly inside `(0,1)`. -/
def openCube (N : ℕ) : Set (Param N) := {z | ∀ s i, z s i ∈ Set.Ioo (0 : ℝ) 1}

/-- `y z s r j`: probability that row `r` produces the current bit `s j` of unit `j`. -/
noncomputable def y (z : Param N) (s : State N) (r : State N) (j : Fin N) : ℝ :=
  (tpmOf z).prob j r (s j)

/-- Row product `P(r) = ∏ⱼ y r j` (= `fullProb (tpmOf z) r s`). -/
noncomputable def rowProd (z : Param N) (s : State N) (r : State N) : ℝ :=
  ∏ j, y z s r j

/-- Column half-mean: the mean of `y r j` over the `2^(N-1)` rows `r` with `r j = b`. -/
noncomputable def halfMean (z : Param N) (s : State N) (j : Fin N) (b : Bool) : ℝ :=
  (∑ r ∈ univ.filter (fun r : State N => r j = b), y z s r j) / (2 : ℝ) ^ (N - 1)

end Census
end IIT
