/-
Census, B1 LTBetaHi, case `s ∈ Sp \ {tc}`: **the rate reduction of W8 7.1'**.

If the current row `s` is special, at least three further special rows cost `e^{-(4 I* - 3 log 2) N}`,
`I* = I(x₁) ≥ 0.788`, i.e. rate `≥ 1.07 > 1.046`. So in the case `s ∈ Sp` the rest consists of `tc` and at most one
further special row (`|Sp| ≤ 3`): the bounded RL-u domain `D_u^b`.
-/
import IIT.Census.B1LT2Sp

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- `4 I(x₁) - 3 log 2 ≥ 1.07`. -/
lemma spr_rate : (107 / 100 : ℝ) ≤ 4 * (lt2x1 - 1 - Real.log lt2x1) - 3 * Real.log 2 := by
  obtain ⟨h1, h2⟩ := lt2x1_bounds
  have hlog : Real.log lt2x1 ≤ -1583 / 1000 := by
    have hq : Real.log (((2053 / 10000 : ℚ)) : ℝ) ≤ (((-1583 / 1000 : ℚ)) : ℝ) :=
      crLog_le (-2) 40 (by decide +kernel)
    push_cast at hq
    exact (Real.log_le_log (by linarith) h2).trans hq
  have hl2 := Real.log_two_lt_d9
  linarith

/-- **A special current row with at least three further special rows: `≤ (2^N)^3 e^{-4 N I(x₁)}`.** -/
theorem spr_card_le (s : State N) (hN : 0 < N) :
    cubeM N {w | s ∈ lt2Sp w ∧ 3 ≤ ((lt2Sp w).erase s).card} ≤
      ENNReal.ofReal ((2 ^ N) ^ 3 * Real.exp (-(N * (lt2x1 - 1 - Real.log lt2x1))) ^ 4) := by
  classical
  obtain ⟨hx1, hx2⟩ := lt2x1_bounds
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set p := Real.exp (-(N * (lt2x1 - 1 - Real.log lt2x1)))
  have hp0 : 0 ≤ p := (Real.exp_pos _).le
  have hsub : {w : Param N | s ∈ lt2Sp w ∧ 3 ≤ ((lt2Sp w).erase s).card} ⊆
      ⋃ K ∈ ((univ : Finset (State N)).erase s).powersetCard 3,
        {w | ∀ r ∈ insert s K, XW w r ≤ lt2x1 * N} := by
    rintro w ⟨hs, h3⟩
    obtain ⟨K, hK, hKc⟩ := Finset.exists_subset_card_eq h3
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, mem_powersetCard]
    refine ⟨K, ⟨fun r hr => ?_, hKc⟩, fun r hr => ?_⟩
    · exact mem_erase.2 ⟨(mem_erase.1 (hK hr)).1, mem_univ _⟩
    · rcases mem_insert.1 hr with rfl | hr
      · exact (mem_filter.1 hs).2
      · exact (mem_filter.1 (mem_erase.1 (hK hr)).2).2
  have hrow : rowM N {v | ∑ i, -Real.log (clamp01 (v i)) ≤ lt2x1 * N} ≤ ENNReal.ofReal p := by
    have h := rowM_negLog_sum_le (N := N) univ (x := lt2x1 * N) (by nlinarith) (by
      simp only [card_univ, Fintype.card_fin]; nlinarith)
    simp only [card_univ, Fintype.card_fin] at h
    rw [show lt2x1 * N / N = lt2x1 by field_simp] at h
    exact h
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ K ∈ ((univ : Finset (State N)).erase s).powersetCard 3,
        cubeM N {w | ∀ r ∈ insert s K, XW w r ≤ lt2x1 * N}
      ≤ ∑ _K ∈ ((univ : Finset (State N)).erase s).powersetCard 3, ENNReal.ofReal p ^ 4 := by
        refine Finset.sum_le_sum fun K hK => ?_
        obtain ⟨hKs, hKc⟩ := mem_powersetCard.1 hK
        have hsK : s ∉ K := fun h => (mem_erase.1 (hKs h)).1 rfl
        rw [lt2_all_rows_le, card_insert_of_notMem hsK, hKc]
        exact pow_le_pow_left₀ zero_le hrow 4
    _ = (((univ : Finset (State N)).erase s).powersetCard 3).card * ENNReal.ofReal p ^ 4 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 : ENNReal) ^ N) ^ 3 * ENNReal.ofReal p ^ 4 := by
        gcongr
        rw [Finset.card_powersetCard]
        have h1 : ((univ : Finset (State N)).erase s).card ≤ 2 ^ N := by
          refine (card_erase_le).trans ?_; simp
        have h2 := (Nat.choose_le_pow _ 3).trans (Nat.pow_le_pow_left h1 3)
        exact_mod_cast h2
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hp0, ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_pow (by norm_num)]
        simp

/-- **Rate reduction**: eventually, `P(s ∈ Sp ∧ |Sp \ {s}| ≥ 3) ≤ e^{-1.07N}`. -/
theorem spr_ev : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N {w | s ∈ lt2Sp w ∧ 3 ≤ ((lt2Sp w).erase s).card} ≤
      ENNReal.ofReal (Real.exp (-((107 / 100 : ℝ) * N))) := by
  filter_upwards [eventually_ge_atTop 1] with N hN s
  refine (spr_card_le s hN).trans (ENNReal.ofReal_le_ofReal ?_)
  have hr := spr_rate
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have e : ((2 : ℝ) ^ N) ^ 3 * Real.exp (-(N * (lt2x1 - 1 - Real.log lt2x1))) ^ 4 =
      Real.exp (-(N * (4 * (lt2x1 - 1 - Real.log lt2x1) - 3 * Real.log 2))) := by
    rw [show (2 : ℝ) ^ N = Real.exp (N * Real.log 2) by
      rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_nat_mul, Real.exp_log (by norm_num)],
      ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  rw [e]
  exact Real.exp_le_exp.2 (by nlinarith)

end Census
end IIT
