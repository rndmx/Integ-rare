/-
Leaf `phi_S_le_EX` of B1LowerB (W7 §3 item 4), with `RestGood` strengthened by `SubGood` (B1SubB5), split by
the size of `S` and by `x ∈ S`:
* `|S| ≤ 1`                       : `φ = 0` (here).
* `2 ≤ |S| ≤ K2N`                 : three-row Prop KT, `φ ≤ 32 P(r0)` (B1SubMid.phi_S_le_EX_le_K2N).
* `x ∈ S`, `K2N < |S| < N`        : three-row B5, `φ ≤ e^{-N/4}` (B1SubB5.phi_S_le_EX_nearX).
* `x ∉ S`, `K2N < |S| ≤ N - 2`    : three-row B5 with `EF2`, `φ ≤ e^{-N/4}` (B1SubB5.phi_S_le_EX_nearNotX).
* `S = U \ {x}`                   : tilt `∏(y+U)/2 ≤ 4 P(r0) e^{-N/400}` (B1SubCoX.phi_S_le_EX_coX).
All sorry-free.
-/
import IIT.Census.B1SubMid

namespace IIT
namespace Census

open MeasureTheory Filter Finset

variable {N : ℕ}

/-- Singletons (and `∅`) have `φ = 0`. -/
theorem phi_S_le_EX_tiny {w : Param N} (ho : w ∈ openCube N) (hN : 1 ≤ N) (s : State N)
    {S : Finset (Fin N)} (hS : S.card ≤ 1) : phi (flipP s w) s S < betaW w * N / 10 ^ 6 := by
  have h0 : phi (flipP s w) s S = 0 := sysPhi_eq_zero_of_card_le_one _ _ _ hS
  rw [h0]
  have := betaW_pos ho
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  positivity

/-- **`phi_S_le_EX` with `RestGood` strengthened by `SubGood`** (same conclusion as the leaf). -/
theorem phi_S_le_EX_sub : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    ∀ w ∈ openCube N, w ∈ EX N s r0 x → EXFacts N s r0 x w →
      (RestGood N s r0 x w ∧ SubGood N s r0 x w) →
      ∀ S : Finset (Fin N), S ≠ univ → S.Nonempty → phi (flipP s w) s S < betaW w * N / 10 ^ 6 := by
  filter_upwards [phi_S_le_EX_le_K2N, phi_S_le_EX_nearX, phi_S_le_EX_nearNotX,
    phi_S_le_EX_coX, eventually_ge_atTop 1] with N hsm hnx hnn hco hN
  intro s r0 x hham w ho hw hF ⟨hR, hSG⟩ S hS _
  have hlt : S.card < N := by
    have := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨subset_univ S, hS⟩)
    rwa [card_univ, Fintype.card_fin] at this
  by_cases h1 : S.card ≤ 1
  · exact phi_S_le_EX_tiny ho hN s h1
  push Not at h1
  by_cases hK : S.card ≤ K2N N
  · exact hsm s r0 x hham w ho hw hF hR hSG S h1 hK
  push Not at hK
  by_cases hx : x ∈ S
  · exact hnx s r0 x hham w ho hw hF hR hSG S hx hK hlt
  by_cases h2 : S.card + 2 ≤ N
  · exact hnn s r0 x hham w ho hw hF hR hSG S hx hK h2
  · have hSe : S = univ.erase x := by
      apply eq_of_subset_of_card_le
      · intro j hj; rw [mem_erase]; exact ⟨fun h => hx (h ▸ hj), mem_univ j⟩
      · rw [card_erase_of_mem (mem_univ x), card_univ, Fintype.card_fin]; omega
    rw [hSe]
    exact hco s r0 x hham w ho hw hF hR hSG

end Census
end IIT
