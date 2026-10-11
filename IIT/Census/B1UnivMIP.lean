/-
Census, module B1UnivMIP: the structure of the MIP of `univ` (W3 Theorem 5.1 with Lemma G' of W10).

The two sides of Lemma V are instances of `keyHyp_of_means`: on the cause side
`λᶜⱼ(C) = log₂(y_{tc,j} / A_j(C))` with `A_j(C)` the mean of column `j` over the subcube through
`tc` free on `C`; on the effect side `λᵉⱼ(C) = log₂(p_j(te_j) / effUnit Cᶜ s j te_j)`.
`univ_tier3` then gives `φ_s(univ)` at the pair `(tc, te)` as the smallest single-cut value.
-/
import IIT.Census.B1Tier3
import IIT.Census.B1Lemma43

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- The cause side of `univ` at `tc`, as one-sided data. -/
noncomputable def lamCz (z : Param N) (s tc : State N) : Fin N → Finset (Fin N) → ℝ :=
  fun j C => lamCU (flipP s z) tc C j

/-- The effect side of `univ` at `te`, as one-sided data. -/
noncomputable def lamEz (z : Param N) (s te : State N) : Fin N → Finset (Fin N) → ℝ :=
  fun j C => lamEU z s te C j

/-- The cause side has the form required by `keyHyp_of_means`. -/
lemma lamCz_means {z : Param N} (hz : z ∈ openCube N) (s tc : State N) :
    (∀ j C, lamCz z s tc j C = Real.logb 2 (clamp01 (flipP s z tc j) /
      cmean (flipP s z) (univ \ C) tc j)) ∧
    (∀ j, cmean (flipP s z) (univ \ ∅) tc j = clamp01 (flipP s z tc j)) ∧
    (∀ j, 0 < clamp01 (flipP s z tc j)) ∧
    (∀ j C, 0 < cmean (flipP s z) (univ \ C) tc j) ∧
    (∀ j C, cmean (flipP s z) (univ \ C) tc j ≤ 1) :=
  ⟨fun j C => lamCU_eq hz s tc C j, fun j => by rw [sdiff_empty, cmean_univ],
    fun j => by rw [← y_eq_clamp]; exact y_pos hz s tc j,
    fun j C => cmean_pos hz s _ tc j, fun j C => cmean_le_one _ _ tc j⟩

/-- The effect side has the form required by `keyHyp_of_means`. -/
lemma lamEz_means {z : Param N} (hz : z ∈ openCube N) (s te : State N) :
    (∀ j C, lamEz z s te j C = Real.logb 2 ((tpmOf z).prob j s (te j) /
      effUnit (tpmOf z) Cᶜ s j (te j))) ∧
    (∀ j, effUnit (tpmOf z) (∅ : Finset (Fin N))ᶜ s j (te j) = (tpmOf z).prob j s (te j)) ∧
    (∀ j, 0 < (tpmOf z).prob j s (te j)) ∧
    (∀ j (C : Finset (Fin N)), 0 < effUnit (tpmOf z) Cᶜ s j (te j)) ∧
    (∀ j (C : Finset (Fin N)), effUnit (tpmOf z) Cᶜ s j (te j) ≤ 1) :=
  ⟨fun j C => rfl, fun j => by rw [compl_empty, effUnit_univ_prob],
    fun j => prob_pos hz j s (te j), fun j C => effUnit_pos hz _ s j (te j),
    fun j C => effUnit_le_one _ _ s j (te j)⟩

/-- **Tier 3 for `univ`** (W3 Theorem 5.1 with Lemma G'). If both sides satisfy the W10
hypotheses (obtained from `keyHyp_of_means` with `lamCz_means` / `lamEz_means`) with `λ_min`
attained, and the single-cut values have no exact tie, then `φ_s(univ)` at `(tc, te)` is the
smallest single-cut value. -/
theorem univ_tier3 {z : Param N} (hz : z ∈ openCube N) (hN : 2 ≤ N) (s tc te : State N)
    {lc0 le0 ac ae : ℝ} {epc epe : ℕ → ℝ} {D dstar : ℕ}
    (hc : KeyHyp (lamCz z s tc) lc0 ac epc D dstar) (he : KeyHyp (lamEz z s te) le0 ae epe D dstar)
    (hcmin : ∃ j, kF (lamCz z s tc) j = lc0) (hemin : ∃ j, kF (lamEz z s te) j = le0)
    (hT : ∀ j j', j ≠ j' →
      phT (lamCz z s tc) (lamEz z s te) (sysBackCause (tpmOf z) univ s s tc)
        (sysEffProb (tpmOf z) univ s s te) j ≠
      phT (lamCz z s tc) (lamEz z s te) (sysBackCause (tpmOf z) univ s s tc)
        (sysEffProb (tpmOf z) univ s s te) j')
    (jst : Fin N)
    (hjst : ∀ j, phT (lamCz z s tc) (lamEz z s te) (sysBackCause (tpmOf z) univ s s tc)
        (sysEffProb (tpmOf z) univ s s te) jst ≤
      phT (lamCz z s tc) (lamEz z s te) (sysBackCause (tpmOf z) univ s s tc)
        (sysEffProb (tpmOf z) univ s s te) j) :
    sysPhiOfState (tpmOf z) univ s s tc te =
      phT (lamCz z s tc) (lamEz z s te) (sysBackCause (tpmOf z) univ s s tc)
        (sysEffProb (tpmOf z) univ s s te) jst :=
  tier3_profile (tpmOf z) s s tc te hN (sysBackCause_pos hz s univ tc)
    (sysEffProb_pos hz s univ te) (fun θ => univ_sysPhiAt_eq hz s tc te θ) hc he hcmin hemin
    hT jst hjst

end Census
end IIT
