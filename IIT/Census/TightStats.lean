/-
Census of complexes: the statistics behind the tightness of the maximal complex.

A pair `{a, b}` competes through its cause-side differences `etaP`: for a unit `i` of the pair and a
pattern `(ta, tb)` of the pair, the change of the conditioned cause numerator `Num` from the pattern
`(false, false)` to `(ta, tb)`, in units of `σ_N`.  The event `inA` says that the pattern
`(false, false)` beats the three other patterns by at least `2y` in both coordinates.  `gSharp` is
the sharp (square-root) form of the deviation bound on `DQ`, and `gZ` says that `Zs` is close to one.
-/
import IIT.Census.BigPhiStats

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- The level of the cause numerators of a pair, `1/2 + 2^{-2}/6`. -/
noncomputable def aPair : ℝ := 13 / 24

/-- The scale of the winning pair, in units of `sqrt (log N)`. -/
noncomputable def gamT : ℝ := 7 / 50

/-- The deviation level `y_N = gamT * sqrt (log N)`. -/
noncomputable def yN (N : ℕ) : ℝ := gamT * Real.sqrt (Real.log N)

/-- The constant of the tightness comparison: the best pair has `phi ≥ cstar * sqrt (log N) * σ_N`. -/
noncomputable def cstar : ℝ := 9 / 100

/-- The state with bits `ta` on `a`, `tb` on `b`, and `false` elsewhere. -/
def pat (a b : Fin N) (ta tb : Bool) : State N :=
  fun j => if j = a then ta else if j = b then tb else false

/-- The cause-side difference of unit `i` of the pair `{a, b}` between the pattern `(ta, tb)` and the
pattern `(false, false)`, in units of `σ_N`. -/
noncomputable def etaP (w : Param N) (a b i : Fin N) (ta tb : Bool) : ℝ :=
  (Num w {a, b} {a, b} (pat a b ta tb) i - Num w {a, b} {a, b} (pat a b false false) i) / sigN N

/-- The pattern `(false, false)` beats every other pattern of the pair by `2y` in both units. -/
def inA (w : Param N) (a b : Fin N) (y : ℝ) : Prop :=
  ∀ i ∈ ({a, b} : Finset (Fin N)), ∀ ta tb : Bool, (ta, tb) ≠ (false, false) →
    etaP w a b i ta tb ≤ -2 * y

/-- The sharp deviation bound on the conditional-mean differences `DQ`. -/
def gSharp (N : ℕ) (w : Param N) : Prop :=
  ∀ (S : Finset (Fin N)) i (Y Y' : Finset (Fin N)) t, i ∈ S → Y ⊆ S → Y' ⊆ S →
    |DQ w S Y Y' t i| ≤ 2 * Real.sqrt (6 * sigN N ^ 2 * LkN N S.card) + 2 * tauN N * LkN N S.card

/-- The sum of the row products is close to its mean one. -/
def gZ (N : ℕ) (w : Param N) : Prop := |Zs w - 1| ≤ 16 * N * sigN N

lemma aPair_pos : 0 < aPair := by norm_num [aPair]

lemma gamT_pos : 0 < gamT := by norm_num [gamT]

lemma cstar_pos : 0 < cstar := by norm_num [cstar]

lemma yN_nonneg (N : ℕ) : 0 ≤ yN N :=
  mul_nonneg gamT_pos.le (Real.sqrt_nonneg _)

end Census
end IIT
