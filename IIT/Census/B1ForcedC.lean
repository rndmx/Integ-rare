/-
Census, B1 leaf `B1_forcedX` (D1'): leaf 1 and the partial assembly.

* `leafC1`: leaf 1 (`bPos`). Since defs3, `bPos` asks only for the cause-side positivity `0 < lcMin`
  (the effect-side proxy lemma needs no positivity, `x_j ≥ 1/2`), which `fa_lcMin_pos` forces on
  `B1 \ faTie`; `faTie` is null.
* `B1_forcedX_partial`: the skeleton statement of `B1_forcedX` from exactly the still-missing leaves.
-/
import IIT.Census.B1ForcedA
import IIT.Census.B1ForcedAF
import IIT.Census.B1ForcedB2

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- **Leaf 1** (`bPos`), sorry-free. -/
theorem leafC1 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (forcedBad N s 1) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [eventually_ge_atTop 2] with N hN s
  have hsub : forcedBad N s 1 ⊆ faTie N := by
    intro w hw
    have hw' : w ∈ bPos N s := hw
    obtain ⟨⟨hB, ho⟩, hn⟩ := hw'
    by_contra ht
    exact hn (fa_lcMin_pos hN hB ho ht)
  exact (measure_mono hsub).trans (by rw [fa_tie_null]; exact zero_le)

/-- leaf 8 at `RfF2` gives leaf 8 at `RfF`. -/
theorem leafC8_of_RfF2
    (h8 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (bField N s (fFar N s)) ≤ ENNReal.ofReal (Real.exp (-(RfF2 * N)))) :
    ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 8) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [h8] with N h s
  refine (h s).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  unfold RfF RfF2; nlinarith

/-- **Partial assembly of `B1_forcedX`**: the skeleton statement from exactly the still-missing leaves:
leaf 8 at `RfF2` (`far`; needs the row-coincidence sub-leaf at `RfF2`), leaves 4 (tilt), 5 (link), 7 (Nat),
9 (ret), 18 (failOnly), and the eight joint bounds of `B1ForcedB2` (leaves 12–17, 19, 21).
Proved here: leaves 0, 1, 2, 3, 6, 10, 20 unconditionally; 8, 11 from `h8`; the joint leaves via `leaf_of_joint`. -/
theorem B1_forcedX_partial
    (h8 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (bField N s (fFar N s)) ≤ ENNReal.ofReal (Real.exp (-(RfF2 * N))))
    (h4 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 4) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))))
    (h5 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 5) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))))
    (h7 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 7) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))))
    (h9 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 9) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))))
    (h18 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 18) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))))
    (jNuS : JointBound P0NuS) (jNuTc : JointBound P0NuTc) (jX5 : JointBound P0X5)
    (jPosNear : JointBound P0PosNear) (jX1 : JointBound P0X1) (jX2 : JointBound P0X2)
    (jSRowMu : JointBound P0SRowMu) (jSRowR : JointBound P0SRowR) :
    ∀ᶠ N in atTop, ∀ s : State N,
      cubeM N (B1w N s \ {w | ForcedX N s w}) ≤ ENNReal.ofReal (3 * Real.exp (-(RbadX * N))) := by
  apply B1_forcedX_of_leaves
  intro i
  fin_cases i
  · exact leafA0
  · exact leafC1
  · exact leafA2
  · exact leafA3
  · exact h4
  · exact h5
  · exact leafA6
  · exact h7
  · exact leafC8_of_RfF2 h8
  · exact h9
  · exact leafA10
  · exact leaf11_of_far h8
  · exact leaf_of_joint P0NuS jNuS h8
  · exact leaf_of_joint P0NuTc jNuTc h8
  · exact leaf_of_joint P0X5 jX5 h8
  · exact leaf_of_joint P0PosNear jPosNear h8
  · exact leaf_of_joint P0X1 jX1 h8
  · exact leaf_of_joint P0X2 jX2 h8
  · exact h18
  · exact leaf_of_joint P0SRowMu jSRowMu h8
  · exact leaf20
  · exact leaf_of_joint P0SRowR jSRowR h8

end Census
end IIT

#print axioms IIT.Census.leafC1
#print axioms IIT.Census.B1_forcedX_partial
