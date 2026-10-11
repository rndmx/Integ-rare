/-
Census of complexes: the target of the B1 development.

Case B1: the whole substrate is a complex. The goal is that, conditionally on B1, the structure
integrated information of the whole substrate is doubly exponential: with conditional probability
tending to one, every selector gives `Φ(U) ≥ 2 ^ 2 ^ (N / 8)`.

This file only states the goal (as a `Prop`); it is proved in `B1Main.lean`.
-/
import IIT.Census.Basic
import IIT.Cond

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- Case B1 at the current state `s`: the whole substrate is a complex. -/
def caseB1 (N : ℕ) (s : State N) : Set (Param N) :=
  {z | z ∈ cube N ∧ IsComplex (tpmOf z) s univ univ s}

/-- The bad event inside B1: some selector gives `Φ(U) < 2 ^ 2 ^ (N / 8)`. -/
def smallPhiB1 (N : ℕ) (s : State N) : Set (Param N) :=
  {z | z ∈ caseB1 N s ∧ ∃ σ : SelectorAt (tpmOf z) univ s s,
    PhiOfAt (tpmOf z) univ s s σ < (2 : ℝ) ^ (2 ^ (N / 8))}

/-- **The goal.** Conditionally on B1, `Φ(U)` is doubly exponential with probability tending to one:
the conditional probability of the bad event tends to `0`, for any choice of current states. -/
def B1PhiGoal : Prop :=
  ∀ s : ∀ N, State N,
    Tendsto (fun N => (volume (smallPhiB1 N (s N))).toReal / (volume (caseB1 N (s N))).toReal)
      atTop (𝓝 0)

end Census
end IIT
