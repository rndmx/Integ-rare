/-
Census, B1, W14 work package WP5 (part 12): the sign and the mean of the counted indicator.

* `coin_sign (hGC hMills hESL)`: `P(Sign_K) ≥ 1/(200 √(ln N))` (`coin_core` + `w5_sign_ge_half`);
* `meanY_of_tools (hGC hMills hSG hESL) : MeanYStmt`:
  `Sign_K ⊆ Y_K ∪ {∃ k ∈ K, Core^{(k)}_K(0) ∧ ¬ D≤_K(k)}`, so `E Y_K ≥ 1/(200 √(ln N)) - 1/N ≥ pY N`.

Blueprint: `iit-census/lean/B1-W14-count-lean.md` §10.  No `sorry`.
-/
import IIT.Census.B1CntCoinCore
import IIT.Census.B1CntCoinFlip

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

theorem coin_sign (hGC : GCStmt) (hMills : MillsStmt) (hESL : EntrySumLawStmt) :
    ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide), ∀ f ∈ GoodX3 N s r0 x σ,
      ∀ K ∈ famX3 N s r0 x σ (b1Ext f),
        ENNReal.ofReal (1 / (200 * Real.sqrt (Real.log N))) ≤
          rowsOutM (sensRows s r0) {g | SignK N s K (glueRows (sensRows s r0) f g)} := by
  filter_upwards [coin_core hGC hMills hESL, w5_sign_ge_half] with N hcore hsign s r0 x σ f hf K hK
  have h1 := hcore s r0 x σ f hf K hK
  have h2 := hsign s r0 f K (famX3_card hK) hf.1.far
  have e : ENNReal.ofReal (1 / (100 * Real.sqrt (Real.log N))) =
      2 * ENNReal.ofReal (1 / (200 * Real.sqrt (Real.log N))) := by
    rw [show (1 : ℝ) / (100 * Real.sqrt (Real.log N)) = 2 * (1 / (200 * Real.sqrt (Real.log N))) by
      by_cases h : Real.sqrt (Real.log N) = 0
      · rw [h]; simp
      · field_simp; ring,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [e] at h1
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 (h1.trans h2)

lemma w5_ev_pY : ∀ᶠ N : ℕ in atTop,
    pY N + 1 / (N : ℝ) ≤ 1 / (200 * Real.sqrt (Real.log N)) := by
  filter_upwards [w5_ev_log100, w5_ev_log_sq, eventually_ge_atTop 1] with N hL hLs hN
  set L := Real.log N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set ℓ := Real.sqrt L with hℓ
  have hℓsq : ℓ ^ 2 = L := Real.sq_sqrt (by linarith)
  have hℓ1 : 1 ≤ ℓ := (Real.le_sqrt' (by norm_num)).2 (by linarith)
  have hℓL : ℓ ≤ L := by nlinarith
  have hLN : 3000 * L ≤ N := by nlinarith
  unfold pY
  have e1 : 1 / (1000 * L) ≤ 1 / (1000 * ℓ) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have e2 : 1 / (N : ℝ) ≤ 4 / (1000 * ℓ) := by
    rw [div_le_div_iff₀ hN0 (by positivity)]; linarith
  have e3 : 1 / (1000 * ℓ) + 4 / (1000 * ℓ) = 1 / (200 * ℓ) := by field_simp; ring
  linarith

theorem meanY_of_tools (hGC : GCStmt) (hMills : MillsStmt) (hSG : SubGaussStmt)
    (hESL : EntrySumLawStmt) : MeanYStmt := by
  filter_upwards [coin_sign hGC hMills hESL, dprime hSG hESL, w5_ev_pY] with N hsign hd hnum
    s r0 x σ f hf K hK
  have h1 := hsign s r0 x σ f hf K hK
  have h2 := hd s r0 x σ f hf K hK
  set G := glueRows (sensRows s r0) f
  have hsub : {g | SignK N s K (G g)} ⊆ {g | YK N s K (G g)} ∪
      {g | ∃ k ∈ K, CoreAt N s K k 0 (G g) ∧ ¬ DleAt N s K k (G g)} := by
    rintro g ⟨k, hk, hc, hpos⟩
    by_cases hD : DleAt N s K k (G g)
    · exact Or.inl ⟨k, hk, hc, hpos, hD⟩
    · exact Or.inr ⟨k, hk, hc, hD⟩
  have h3 : rowsOutM (sensRows s r0) {g | SignK N s K (G g)} ≤
      rowsOutM (sensRows s r0) {g | YK N s K (G g)} + ENNReal.ofReal (1 / (N : ℝ)) :=
    (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl h2))
  have hpY0 : 0 ≤ pY N := by unfold pY; have := Real.log_natCast_nonneg N; positivity
  have h4 : ENNReal.ofReal (pY N) + ENNReal.ofReal (1 / (N : ℝ)) ≤
      rowsOutM (sensRows s r0) {g | YK N s K (G g)} + ENNReal.ofReal (1 / (N : ℝ)) := by
    rw [← ENNReal.ofReal_add hpY0 (by positivity)]
    exact (ENNReal.ofReal_le_ofReal hnum).trans (h1.trans h3)
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h4

end Census
end IIT

#print axioms IIT.Census.coin_sign
#print axioms IIT.Census.meanY_of_tools
