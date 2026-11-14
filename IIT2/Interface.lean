/-
Shared input type, copied verbatim from rndmx/Integ release v1.1 (commit 49b4c59),
file IIT/Phi.lean, lines 218-230. Do not modify. It exists only so that later
comparisons with other formalizations take the same input.
-/
import Mathlib

namespace IIT2

/-- A state of an `N`-unit system of binary units. -/
abbrev State (N : ℕ) := Fin N → Bool

/-- A system given by its unit transition probabilities; the system TPM is their
product (conditional independence). -/
structure UnitTPM (N : ℕ) where
  /-- `prob i s b` is the probability that unit `i` is in state `b` at `t+1`
  given the system is in state `s` at `t`. -/
  prob : Fin N → State N → Bool → ℝ
  nonneg : ∀ i s b, 0 ≤ prob i s b
  normalized : ∀ i s, prob i s false + prob i s true = 1

end IIT2
