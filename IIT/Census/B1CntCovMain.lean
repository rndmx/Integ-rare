/-
Census, B1, W14 work package WP6 (part 7, assembly): `cheb_of_meanY : GCStmt → EntrySumLawStmt →
MeanYStmt → ChebStmt` (W9 5.8: `Var W ≤ ∑ near |𝒦| + ∑ far c_far`, Chebyshev at `E W/2`).
Also re-exports `famBig_proved : FamBigStmt` (`B1CntCovFam`).
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §11.  No `sorry`.
-/
import IIT.Census.B1CntCovFar
import IIT.Census.B1CntCovNear

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

lemma cheb_final : ∀ᶠ N : ℕ in atTop,
    8 * Real.exp (-((N : ℝ) / 420)) / pY N ^ 2 ≤ Real.exp (-((N : ℝ) / 450)) := by
  filter_upwards [cov_ev_logsq 2 (Real.log 8 + 2 * Real.log 1000 + 2) (1 / 6300) (by norm_num),
    eventually_ge_atTop 3] with N hev hN
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hsq := cov_log_le_sq N
  have hpY : pY N = 1 / (1000 * Real.log N) := rfl
  rw [hpY, one_div, inv_pow, div_inv_eq_mul]
  have hQ : 0 < 8 * (1000 * Real.log N) ^ 2 := by positivity
  have hlogQ : Real.log (8 * (1000 * Real.log N) ^ 2) ≤
      Real.log 8 + 2 * (Real.log 1000 + Real.log N) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      Real.log_mul (by norm_num) hl.ne']
    have := Real.log_le_sub_one_of_pos hl
    push_cast
    linarith
  calc 8 * Real.exp (-((N : ℝ) / 420)) * (1000 * Real.log N) ^ 2
      = Real.exp (Real.log (8 * (1000 * Real.log N) ^ 2) + -((N : ℝ) / 420)) := by
        rw [Real.exp_add, Real.exp_log hQ]; ring
    _ ≤ Real.exp (-((N : ℝ) / 450)) := by
        apply Real.exp_le_exp.2
        nlinarith

/-- **WP6 main: Chebyshev for the count `W`** (W9 5.8): from `E Y_K ≥ pY` (`MeanYStmt`), `cov_far`
on far pairs and `near_pairs3`, `P(W < |𝒦| pY / 2) ≤ 8 e^{-N/420}/pY² ≤ e^{-N/450}`. -/
theorem cheb_of_meanY (hGC : GCStmt) (hESL : EntrySumLawStmt) : MeanYStmt → ChebStmt := by
  intro hMean
  filter_upwards [hMean, cov_far hGC hESL, near_pairs3, cheb_final, eventually_ge_atTop 3]
    with N hmean hcov hnear hfin hN s r0 x σ f hf
  set 𝒦 := famX3 N s r0 x σ (b1Ext f) with h𝒦
  set μ := rowsOutM (sensRows s r0) with hμ
  set A : Finset (Fin N) → Set ({r // r ∉ sensRows s r0} → Fin N → ℝ) :=
    fun K => {g | YK N s K (glueRows (sensRows s r0) f g)} with hA
  set e := Real.exp (-((N : ℝ) / 420)) with he
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hpY : 0 < pY N := by unfold pY; positivity
  have hset : {g | glueRows (sensRows s r0) f g ∈ WBad N s r0 x σ} =
      {ω | ((𝒦.filter fun K => ω ∈ A K).card : ℝ) < 𝒦.card * pY N / 2} := by
    ext g
    simp only [Set.mem_ofPred_eq, WBad, WCnt, famX3_glue, hA, h𝒦]
  rw [hset]
  rcases 𝒦.eq_empty_or_nonempty with h0 | hne
  · have : {ω | ((𝒦.filter fun K => ω ∈ A K).card : ℝ) < 𝒦.card * pY N / 2} = ∅ := by
      ext ω; simp [h0]
    rw [this, measure_empty]; exact zero_le
  have hcard : (0 : ℝ) < 𝒦.card := by exact_mod_cast hne.card_pos
  have hAm : ∀ K, MeasurableSet (A K) := fun K =>
    measurable_glueRows_right (sensRows s r0) f (measurableSet_YK s K)
  -- first moment
  have he1 : 𝒦.card * pY N ≤ ∑ K ∈ 𝒦, (μ (A K)).toReal := by
    calc (𝒦.card : ℝ) * pY N = ∑ _K ∈ 𝒦, pY N := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ K ∈ 𝒦, (μ (A K)).toReal := sum_le_sum fun K hK =>
          (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 (hmean s r0 x σ f hf K hK)
  -- near pairs
  obtain ⟨P, hdisj, hn4, hfam⟩ := famX3_core_good (s := s) (σ := σ) hf.1.x2
  have hlow : 1000 * (lowU N (b1Ext f) r0).card ≤ N := hf.2.lowFew
  have hnearK : ∀ K ∈ 𝒦, (((𝒦.filter fun K' => dX N < 3 * (K ∩ K').card).card : ℝ)) ≤
      𝒦.card * e := by
    intro K hK
    have hK' : K ∈ ((P ∪ lowU N (b1Ext f) r0).powersetCard (dX N)).filter
        (fun K => lowU N (b1Ext f) r0 ⊆ K) := by rw [← hfam]; exact hK
    have := hnear P _ hdisj hn4 hlow K hK'
    rw [← hfam] at this
    exact this
  -- second moment
  have hrow : ∀ K ∈ 𝒦, ∑ K' ∈ 𝒦, ((μ (A K ∩ A K')).toReal - (μ (A K)).toReal * (μ (A K')).toReal) ≤
      2 * 𝒦.card * e := by
    intro K hK
    have hterm : ∀ K' ∈ 𝒦, ((μ (A K ∩ A K')).toReal - (μ (A K)).toReal * (μ (A K')).toReal) ≤
        if dX N < 3 * (K ∩ K').card then 1 else e := by
      intro K' hK'
      split_ifs with hnr
      · have h1 : (μ (A K ∩ A K')).toReal ≤ 1 := by
          rw [← measureReal_def]; exact measureReal_le_one
        have h2 : 0 ≤ (μ (A K)).toReal * (μ (A K')).toReal := by positivity
        linarith
      · have := hcov s r0 x σ f hf K hK K' hK' (by omega)
        exact (le_abs_self _).trans this
    calc ∑ K' ∈ 𝒦, ((μ (A K ∩ A K')).toReal - (μ (A K)).toReal * (μ (A K')).toReal)
        ≤ ∑ K' ∈ 𝒦, (if dX N < 3 * (K ∩ K').card then (1 : ℝ) else e) := sum_le_sum hterm
      _ = ((𝒦.filter fun K' => dX N < 3 * (K ∩ K').card).card : ℝ) +
          ((𝒦.filter fun K' => ¬ dX N < 3 * (K ∩ K').card).card : ℝ) * e := by
          rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
      _ ≤ 𝒦.card * e + 𝒦.card * e := by
          have h1 := hnearK K hK
          have h2 : ((𝒦.filter fun K' => ¬ dX N < 3 * (K ∩ K').card).card : ℝ) ≤ 𝒦.card := by
            exact_mod_cast card_filter_le _ _
          have he0 : 0 ≤ e := (Real.exp_pos _).le
          nlinarith
      _ = 2 * 𝒦.card * e := by ring
  have hV : ∑ K ∈ 𝒦, ∑ K' ∈ 𝒦,
      ((μ (A K ∩ A K')).toReal - (μ (A K)).toReal * (μ (A K')).toReal) ≤ 2 * 𝒦.card ^ 2 * e := by
    calc _ ≤ ∑ _K ∈ 𝒦, 2 * (𝒦.card : ℝ) * e := sum_le_sum hrow
      _ = 2 * 𝒦.card ^ 2 * e := by rw [sum_const, nsmul_eq_mul]; ring
  have hc := count_cheb μ 𝒦 A hAm (e0 := 𝒦.card * pY N) (by positivity) he1 hV
  refine hc.trans (ENNReal.ofReal_le_ofReal ?_)
  have e1 : 4 * (2 * (𝒦.card : ℝ) ^ 2 * e) / ((𝒦.card : ℝ) * pY N) ^ 2 = 8 * e / pY N ^ 2 := by
    field_simp; ring
  rw [e1]
  exact hfin

end Census
end IIT

#print axioms IIT.Census.cheb_of_meanY
#print axioms IIT.Census.famBig_proved
