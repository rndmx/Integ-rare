/-
Census, B1 LTBetaHi, case `s ∈ Sp \ {tc}`: **enough good units for `Top'`**.

On `B1 ∩ openCube ∩ {Lσ_N ≤ β, Zs ≥ 1/2}`, if the current row `s` is special and `≠ tc`, then fewer than `⌈N/21⌉`
good units (`y_tc ≥ 17/20`, `y_s ≥ 7/8`) forces one of: a tie (null), an irregular half-mean (`e^{-2N}`), or the
Case A event at threshold `N/20` (`c2_ev`, `e^{-1.1N}`). Here `y_{tc,j} ≥ 49/100` comes from `fa_cause_pos` and the
half-mean regularity at `δ = 1/100`, `P(tc) ≥ e^{-(x₁-1/800)N}` from `bd_Ptc_ge`, and `P(s) ≥ e^{-x₁N}` from `s ∈ Sp`.
-/
import IIT.Census.B1LTHiCaseA2
import IIT.Census.B1LTHiBand
import IIT.Census.B1ForcedA

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

lemma spgu_pow (N : ℕ) (hN : 30 ≤ N) : 50000 * N ≤ 2 ^ N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    omega

/-- **Half-means are regular at `δ = 1/100`**, with probability `≥ 1 - e^{-2N}`. -/
theorem spgu_half : ∀ᶠ N : ℕ in atTop,
    cubeM N {w | ∃ t j, (1 / 100 : ℝ) < |faColMean w t j - 1 / 2|} ≤ ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
  filter_upwards [eventually_ge_atTop 30] with N hN
  have hN1 : 1 ≤ N := by omega
  have hNr : (30 : ℝ) ≤ N := by exact_mod_cast hN
  have e : {w : Param N | ∃ t j, (1 / 100 : ℝ) < |faColMean w t j - 1 / 2|} =
      ⋃ p : State N × Fin N, {w | (1 / 100 : ℝ) < |faColMean w p.1 p.2 - 1 / 2|} := by
    ext w; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Prod.exists]
  rw [e]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  have hone : ∀ p : State N × Fin N, cubeM N {w | (1 / 100 : ℝ) < |faColMean w p.1 p.2 - 1 / 2|} ≤
      ENNReal.ofReal (2 * Real.exp (-(2 ^ N * (1 / 100 : ℝ) ^ 2))) := fun p =>
    fa_col_dev hN1 p.1 p.2 (by norm_num)
  refine (Finset.sum_le_sum fun p _ => hone p).trans ?_
  rw [Finset.sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hc : ((Fintype.card (State N) * N : ℕ) : ℝ) ≤ Real.exp (2 * N) := by
    have h1 : Fintype.card (State N) = 2 ^ N := by simp
    rw [h1]
    have h2 : ((2 ^ N * N : ℕ) : ℝ) ≤ (2 : ℝ) ^ N * 2 ^ N := by
      push_cast
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.lt_two_pow_self).le) (by positivity)
    refine h2.trans ?_
    rw [← mul_pow, show (2 : ℝ) * 2 = 4 by norm_num]
    calc (4 : ℝ) ^ N ≤ Real.exp 2 ^ N := pow_le_pow_left₀ (by norm_num)
          (by have := Real.add_one_le_exp (2 : ℝ); have := Real.exp_one_gt_d9
              have h22 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
              nlinarith) N
      _ = Real.exp (2 * N) := by rw [← Real.exp_nat_mul]; ring_nf
  have hp : (5 : ℝ) * N ≤ 2 ^ N * (1 / 100) ^ 2 := by
    have := spgu_pow N hN
    have : (50000 : ℝ) * N ≤ 2 ^ N := by exact_mod_cast this
    nlinarith
  calc ((Fintype.card (State N) * N : ℕ) : ℝ) * (2 * Real.exp (-(2 ^ N * (1 / 100 : ℝ) ^ 2)))
      ≤ Real.exp (2 * N) * (2 * Real.exp (-(5 * N))) := by
        gcongr
    _ = 2 * Real.exp (-(3 * (N : ℝ))) := by rw [mul_left_comm, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(2 * (N : ℝ))) := by
        have : 2 * Real.exp (-(3 * (N : ℝ))) = Real.exp (-(2 * (N : ℝ))) * (2 * Real.exp (-(N : ℝ))) := by
          rw [mul_left_comm, ← Real.exp_add]; ring_nf
        rw [this]
        have h1 : Real.exp (-(N : ℝ)) ≤ Real.exp (-30) := Real.exp_le_exp.2 (by linarith)
        have h2 : Real.exp (-30 : ℝ) ≤ 1 / 2 := by
          have := Real.add_one_le_exp (30 : ℝ)
          rw [Real.exp_neg]; rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; linarith
        nlinarith [Real.exp_pos (-(2 * (N : ℝ))), Real.exp_pos (-(N : ℝ))]

/-- **Enough good units in the special case**, off probability `≤ 2 e^{-1.1N}`. -/
theorem spgu_ev {L : ℝ} (hL : 0 < L) : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N {w | w ∈ B1w N s ∧ w ∈ openCube N ∧ L * sigN N ≤ betaW w ∧ 1 / 2 ≤ Zs w ∧ lt3SpC s w ∧
      (lt3GoodU s w).card < ⌈(1 / 21 : ℝ) * N⌉₊} ≤
      ENNReal.ofReal (2 * Real.exp (-((11 / 10 : ℝ) * N))) := by
  filter_upwards [spgu_half, bd_Ptc_ge hL, eventually_ge_atTop 420] with N hhalf hPtc hN s
  classical
  have hsub : {w | w ∈ B1w N s ∧ w ∈ openCube N ∧ L * sigN N ≤ betaW w ∧ 1 / 2 ≤ Zs w ∧ lt3SpC s w ∧
      (lt3GoodU s w).card < ⌈(1 / 21 : ℝ) * N⌉₊} ⊆
      (faTie N ∪ {w | ∃ t j, (1 / 100 : ℝ) < |faColMean w t j - 1 / 2|}) ∪
        {w | ∃ r0, r0 ≠ s ∧ c2Ev r0 s w} := by
    rintro w ⟨hB, hw, hβ, hZ, ⟨hsSp, hne⟩, hcard⟩
    by_cases ht : w ∈ faTie N
    · exact Or.inl (Or.inl ht)
    by_cases hh : ∃ t j, (1 / 100 : ℝ) < |faColMean w t j - 1 / 2|
    · exact Or.inl (Or.inr hh)
    push Not at hh
    refine Or.inr ⟨tcRow w, fun h => hne h.symm, ?_, ?_, fun j => ?_, ?_⟩
    · have := hPtc w hZ hβ; unfold c2Xt; exact this
    · have hpos : ∀ i, 0 < clamp01 (w s i) := fun i => by
        rw [clamp01_of_mem ⟨(hw s i).1.le, (hw s i).2.le⟩]; exact (hw s i).1
      rw [Pw_eq_exp_neg_XW hpos]
      have : XW w s ≤ lt2x1 * N := (mem_filter.1 hsSp).2
      exact Real.exp_le_exp.2 (by linarith)
    · have h1 := fa_cause_pos (by omega) hB hw ht j
      have h2 := abs_le.1 (hh (tcRow w) j)
      linarith [h2.1]
    · have hc2 := (lt3_ceil_bounds hN).2
      have : (lt3GoodU s w).card < N / 20 := lt_of_lt_of_le hcard hc2
      have h3 : ((lt3GoodU s w).card : ℝ) < (N : ℝ) / 20 := by
        have h4 : ((N / 20 : ℕ) : ℝ) ≤ (N : ℝ) / 20 := Nat.cast_div_le
        have h5 : ((lt3GoodU s w).card : ℝ) < ((N / 20 : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      unfold lt3GoodU at h3
      exact h3
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add (le_of_eq fa_tie_null) le_rfl)) (c2_ev s)).trans ?_
  rw [zero_add]
  refine (add_le_add hhalf le_rfl).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have : Real.exp (-(2 * (N : ℝ))) ≤ Real.exp (-((11 / 10 : ℝ) * N)) := Real.exp_le_exp.2 (by nlinarith)
  linarith

end Census
end IIT
