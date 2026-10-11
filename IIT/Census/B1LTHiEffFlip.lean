/-
Census, B1 LTBetaHi, T7 support (item (e), light `s`): **the effect side in every own direction**.

`tp_eff_gamma` (B1LTHiEff) is stated in the frame where the designated effect state is all ON: it needs
`z s j ≥ 1/2 + γ` for every unit of `S`. In the LTBetaHi application the TPM is `tpmOf (flipP s w)` and the own
entries `w s j` (`y`-coordinates) are only known to avoid `(1/2 - γ, 1/2 + γ)`, in either direction.

* `tXor`, and the **output relabelling symmetry** of the effect side: if `T'.prob i r b = T.prob i r (b xor f i)`
  then `sysEffProb`, `sysUncEff`, `sysIiE`, `effUnit`, `sysPartEffProb`, `sysPhiE` of `T'` at `t` equal those of
  `T` at `t xor f`, and `t ∈ sysMaxEffStates T'` iff `t xor f ∈ sysMaxEffStates T` (`maxEff_tXor`, `phiE_tXor`).
* `tpmOf_flipCol`: flipping the columns `j` with `g j = false` (`z ↦ flipC (g j) (z r j)`) relabels the outputs.
* **`tp_eff_dir`**: Lemma EF for an arbitrary direction pattern `g` (own entries `flipC (g j) (w s j) ≥ 1/2 + γ`,
  private entries `flipC (g j) (w r j) ≤ ρ`), concluded for `tpmOf (flipP s w)` itself, with
  `te = (efgTop) xor (g xor s)`.
-/
import IIT.Census.B1LTHiEff
import IIT.Census.UnivProb

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- Output relabelling of a state by a bit mask. -/
def tXor (f : Fin N → Bool) (t : State N) : State N := fun i => xor (t i) (f i)

lemma tXor_tXor (f : Fin N → Bool) (t : State N) : tXor f (tXor f t) = t := by
  funext i; simp [tXor]

section Flip

variable {T T' : UnitTPM N} {f : Fin N → Bool}

lemma effProb_tXor (hT : ∀ i r b, T'.prob i r b = T.prob i r (xor b (f i))) (S : Finset (Fin N))
    (u s t : State N) : sysEffProb T' S u s t = sysEffProb T S u s (tXor f t) := by
  unfold sysEffProb tXor
  exact prod_congr rfl fun i _ => hT _ _ _

lemma uncEff_tXor (hT : ∀ i r b, T'.prob i r b = T.prob i r (xor b (f i))) (S : Finset (Fin N))
    (u t : State N) : sysUncEff T' S u t = sysUncEff T S u (tXor f t) := by
  unfold sysUncEff avgOverStates
  simp only [effProb_tXor hT]

lemma iiE_tXor (hT : ∀ i r b, T'.prob i r b = T.prob i r (xor b (f i))) (S : Finset (Fin N))
    (u s t : State N) : sysIiE T' S u s t = sysIiE T S u s (tXor f t) := by
  unfold sysIiE
  rw [effProb_tXor hT, uncEff_tXor hT]

/-- **Maximal effect states are relabelled.** -/
lemma maxEff_tXor (hT : ∀ i r b, T'.prob i r b = T.prob i r (xor b (f i))) (S : Finset (Fin N))
    (u s t : State N) : t ∈ sysMaxEffStates T' S u s ↔ tXor f t ∈ sysMaxEffStates T S u s := by
  unfold sysMaxEffStates
  rw [mem_argmaxSet, mem_argmaxSet]
  constructor
  · intro h b
    have := h (tXor f b)
    rwa [iiE_tXor hT, iiE_tXor hT, tXor_tXor] at this
  · intro h b
    rw [iiE_tXor hT, iiE_tXor hT]
    exact h _

lemma effUnit_tXor (hT : ∀ i r b, T'.prob i r b = T.prob i r (xor b (f i))) (M : Finset (Fin N))
    (m : State N) (i : Fin N) (b : Bool) : effUnit T' M m i b = effUnit T M m i (xor b (f i)) := by
  unfold effUnit
  simp only [hT]

lemma partEff_tXor (hT : ∀ i r b, T'.prob i r b = T.prob i r (xor b (f i))) (S : Finset (Fin N))
    (u : State N) (θ : SysPartition N S) (s t : State N) :
    sysPartEffProb T' S u θ s t = sysPartEffProb T S u θ s (tXor f t) := by
  unfold sysPartEffProb tXor
  exact prod_congr rfl fun j _ => effUnit_tXor hT _ _ _ _

/-- **Integrated effect information is relabelled.** -/
lemma phiE_tXor (hT : ∀ i r b, T'.prob i r b = T.prob i r (xor b (f i))) (S : Finset (Fin N))
    (u : State N) (θ : SysPartition N S) (s t : State N) :
    sysPhiE T' S u θ s t = sysPhiE T S u θ s (tXor f t) := by
  unfold sysPhiE
  rw [effProb_tXor hT, partEff_tXor hT]

end Flip

/-- **Flipping columns relabels the outputs**: `z' r j = flipC (g j) (z r j)` gives
`(tpmOf z').prob i r b = (tpmOf z).prob i r (b xor ¬g i)`. -/
lemma tpmOf_flipCol (g : Fin N → Bool) (z : Param N) (i : Fin N) (r : State N) (b : Bool) :
    (tpmOf (fun r j => flipC (g j) (z r j))).prob i r b = (tpmOf z).prob i r (xor b (!g i)) := by
  cases hg : g i <;> cases b <;> simp [tpmOf, flipC, hg, clamp01_one_sub]

lemma flipC_mem_Ioo' {b : Bool} {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) : flipC b x ∈ Set.Ioo (0 : ℝ) 1 := by
  cases b
  · simp only [flipC, Bool.false_eq_true, ↓reduceIte, Set.mem_Ioo]
    constructor <;> linarith [hx.1, hx.2]
  · simpa [flipC] using hx

/-- **Lemma EF in every direction** (light `s`). For a direction pattern `g`, own entries
`flipC (g j) (w s j) ≥ 1/2 + γ` and private entries (`(r, j)`, `r` flipped at some `i ≠ j` of `S`)
`flipC (g j) (w r j) ≤ ρ`, `7ρ ≤ 3 ln 2 · 2γ(1/2+γ)²`: the effect side of `tpmOf (flipP s w)` is
`≥ (1/2+γ)³ log₂(1/(1 - (1/2+γ-ρ)/2))` at a maximal effect state, at every partition. -/
theorem tp_eff_dir {w : Param N} (hw : w ∈ openCube N) (s : State N) {S : Finset (Fin N)} (hS : S.card = 3)
    (g : Fin N → Bool) {γ ρ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1 / 2) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 2 + γ)
    (hown : ∀ j ∈ S, 1 / 2 + γ ≤ flipC (g j) (w s j))
    (hpriv : ∀ r ∈ agree Sᶜ s, r ≠ s → ∀ j ∈ S, (∃ i ∈ S, i ≠ j ∧ r i ≠ s i) → flipC (g j) (w r j) ≤ ρ)
    (hB : 7 * ρ ≤ 3 * Real.log 2 * (2 * γ * (1 / 2 + γ) ^ 2)) :
    ∃ te ∈ sysMaxEffStates (tpmOf (flipP s w)) S s s, ∀ θ : SysPartition N S,
      (1 / 2 + γ) ^ 3 * Real.logb 2 (1 / (1 - (1 / 2 + γ - ρ) / 2)) ≤
        sysPhiE (tpmOf (flipP s w)) S s θ s te := by
  set z' : Param N := fun r j => flipC (g j) (w r j) with hz'def
  have hz' : z' ∈ openCube N := fun r i => flipC_mem_Ioo' (hw r i)
  obtain ⟨h1, h2⟩ := tp_eff_gamma hz' s hS hγ0 hγ1 hρ0 hρ1 hown hpriv hB
  have hT : ∀ i r b, (tpmOf z').prob i r b =
      (tpmOf (flipP s w)).prob i r (xor b ((fun i => xor (g i) (s i)) i)) := by
    intro i r b
    have e1 := tpmOf_flipCol g w i r b
    have e2 := tpmOf_flipCol s w i r (xor b (xor (g i) (s i)))
    have e3 : (tpmOf (flipP s w)).prob i r (xor b (xor (g i) (s i))) =
        (tpmOf (fun r j => flipC (s j) (w r j))).prob i r (xor b (xor (g i) (s i))) := rfl
    rw [e3, e2]
    rw [hz'def, e1]
    congr 1
    cases b <;> cases g i <;> cases s i <;> rfl
  refine ⟨tXor (fun i => xor (g i) (s i)) efgTop, (maxEff_tXor hT S s s efgTop).1 h1, fun θ => ?_⟩
  rw [← phiE_tXor hT]
  exact h2 θ

end Census
end IIT
