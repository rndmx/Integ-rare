/-
Census, B1 new leaf `pairLow` (B1GoodX2, cause side): **`joint_pairLow : JointBound P0PairLow`**.

The failure of `pairLow` (`∀ j ≠ x, y_{r0,j} + y_{r1,j} > 1 - 1/N`, `r1 = r0^x`) jointly with the cause regime event:
per certified cell, the regime template (`cellEvX_sub_template`) with the extra per-column window
`1 - 1/N < y + u` on the columns `j ≠ x` (`cubeM_chernoff_three_win`).  The restricted unit factor is
`e^{λK} (I - corr + 1/N)` (`pl_J_le`, `plCorr_eq`), certified (`plCells_ok`) to give the rate
`plR = rsR0 + 13/1000 = 1.0202 > RJ = 1.0108`.
-/
import IIT.Census.B1NewLeafPairInt
import IIT.Census.B1ForcedFSRow

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-! ### 1. The removed mass, exactly -/

/-- **`corr = plCorrQ`.** -/
theorem plCorr_eq (v w : ℚ) (hv : 0 < v) (hvw : v ≤ w) (hw1 : w ≤ 1) (lam P : ℕ)
    (h0 : (P : ℤ) - 4 * lam + 4 ≠ 0) (h1 : (P : ℤ) - 4 * lam + 8 ≠ 0) :
    ∫ y in ((v : ℝ) ^ 4)..1, y ^ ((P : ℝ) / 4) * ((1 - y) * (min 1 ((w : ℝ) ^ 4 / y)) ^ lam) =
      ((plCorrQ v w lam P : ℚ) : ℝ) := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hw0 : 0 < w := lt_of_lt_of_le hv hvw
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw0
  have ha : (0 : ℝ) < (v : ℝ) ^ 4 := by positivity
  have hac : (v : ℝ) ^ 4 ≤ (w : ℝ) ^ 4 := pow_le_pow_left₀ hv'.le (by exact_mod_cast hvw) 4
  have hc1 : (w : ℝ) ^ 4 ≤ 1 := pow_le_one₀ hw'.le (by exact_mod_cast hw1)
  have hc : (0 : ℝ) < (w : ℝ) ^ 4 := by positivity
  have hint : ∀ u b : ℝ, 0 < u → u ≤ b → IntervalIntegrable
      (fun y : ℝ => y ^ ((P : ℝ) / 4) * ((1 - y) * (min 1 ((w : ℝ) ^ 4 / y)) ^ lam)) volume u b := by
    intro u b hu hub
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hub]
    have hy : ∀ y ∈ Set.Icc u b, y ≠ 0 := fun y hy => (lt_of_lt_of_le hu hy.1).ne'
    exact (ContinuousOn.rpow_const continuousOn_id fun y hy' => Or.inl (hy y hy')).mul
      ((continuousOn_const.sub continuousOn_id).mul
        ((ContinuousOn.inf continuousOn_const (ContinuousOn.div continuousOn_const continuousOn_id hy)).pow lam))
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint _ _ ha hac) (hint _ _ hc hc1)]
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  have hpne : (P : ℝ) / 4 ≠ -1 := by intro h; linarith
  have hp1ne : (P : ℝ) / 4 + 1 ≠ -1 := by intro h; linarith
  have hq0 : (P : ℝ) / 4 - lam ≠ -1 := fun h => h0 (by
    have : (((P : ℤ) - 4 * lam + 4 : ℤ) : ℝ) = 0 := by push_cast; linarith
    exact_mod_cast this)
  have hq1 : (P : ℝ) / 4 + 1 - lam ≠ -1 := fun h => h1 (by
    have : (((P : ℤ) - 4 * lam + 8 : ℤ) : ℝ) = 0 := by push_cast; linarith
    exact_mod_cast this)
  have e1 : ∫ y in ((v : ℝ) ^ 4)..((w : ℝ) ^ 4), y ^ ((P : ℝ) / 4) * ((1 - y) * (min 1 ((w : ℝ) ^ 4 / y)) ^ lam) =
      powInt ((v : ℝ) ^ 4) ((w : ℝ) ^ 4) ((P : ℝ) / 4) -
        powInt ((v : ℝ) ^ 4) ((w : ℝ) ^ 4) ((P : ℝ) / 4 + 1) := by
    have heq : Set.EqOn (fun y : ℝ => y ^ ((P : ℝ) / 4) * ((1 - y) * (min 1 ((w : ℝ) ^ 4 / y)) ^ lam))
        (fun y => y ^ ((P : ℝ) / 4) - y ^ ((P : ℝ) / 4 + 1)) (Set.uIcc ((v : ℝ) ^ 4) ((w : ℝ) ^ 4)) := by
      intro y hy
      rw [Set.uIcc_of_le hac] at hy
      have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
      have hm : min 1 ((w : ℝ) ^ 4 / y) = 1 := min_eq_left ((one_le_div hy0).2 hy.2)
      simp only [hm, one_pow, mul_one]
      rw [Real.rpow_add_one hy0.ne']; ring
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_sub
      (rpow_intervalIntegrable ha hac) (rpow_intervalIntegrable ha hac),
      integral_rpow_pos ha hac hpne, integral_rpow_pos ha hac hp1ne]
    rfl
  have e2 : ∫ y in ((w : ℝ) ^ 4)..1, y ^ ((P : ℝ) / 4) * ((1 - y) * (min 1 ((w : ℝ) ^ 4 / y)) ^ lam) =
      ((w : ℝ) ^ 4) ^ lam * (powInt ((w : ℝ) ^ 4) 1 ((P : ℝ) / 4 - lam) -
        powInt ((w : ℝ) ^ 4) 1 ((P : ℝ) / 4 + 1 - lam)) := by
    have heq : Set.EqOn (fun y : ℝ => y ^ ((P : ℝ) / 4) * ((1 - y) * (min 1 ((w : ℝ) ^ 4 / y)) ^ lam))
        (fun y => ((w : ℝ) ^ 4) ^ lam * (y ^ ((P : ℝ) / 4 - lam) - y ^ ((P : ℝ) / 4 + 1 - lam)))
        (Set.uIcc ((w : ℝ) ^ 4) 1) := by
      intro y hy
      rw [Set.uIcc_of_le hc1] at hy
      have hy0 : 0 < y := lt_of_lt_of_le hc hy.1
      have hm : min 1 ((w : ℝ) ^ 4 / y) = (w : ℝ) ^ 4 / y := min_eq_right ((div_le_one hy0).2 hy.1)
      simp only [hm]
      rw [Real.rpow_sub_natCast hy0.ne', Real.rpow_sub_natCast hy0.ne', Real.rpow_add_one hy0.ne', div_pow]
      have : y ^ lam ≠ 0 := pow_ne_zero _ hy0.ne'
      field_simp
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (rpow_intervalIntegrable hc hc1) (rpow_intervalIntegrable hc hc1),
      integral_rpow_pos hc hc1 hq0, integral_rpow_pos hc hc1 hq1]
    rfl
  rw [e1, e2]
  have k1 : ((powIntQ v w ((P : ℤ) + 4) : ℚ) : ℝ) = powInt ((v : ℝ) ^ 4) ((w : ℝ) ^ 4) ((P : ℝ) / 4) :=
    powIntQ_cast hv hw0 _ (by push_cast; ring)
  have k2 : ((powIntQ v w ((P : ℤ) + 8) : ℚ) : ℝ) = powInt ((v : ℝ) ^ 4) ((w : ℝ) ^ 4) ((P : ℝ) / 4 + 1) :=
    powIntQ_cast hv hw0 _ (by push_cast; ring)
  have k3 : ((powIntQ w 1 ((P : ℤ) - 4 * lam + 4) : ℚ) : ℝ) = powInt ((w : ℝ) ^ 4) 1 ((P : ℝ) / 4 - lam) := by
    rw [powIntQ_cast hw0 one_pos _ (q := (P : ℝ) / 4 - lam) (by push_cast; ring)]
    simp
  have k4 : ((powIntQ w 1 ((P : ℤ) - 4 * lam + 8) : ℚ) : ℝ) =
      powInt ((w : ℝ) ^ 4) 1 ((P : ℝ) / 4 + 1 - lam) := by
    rw [powIntQ_cast hw0 one_pos _ (q := (P : ℝ) / 4 + 1 - lam) (by push_cast; ring)]
    simp
  unfold plCorrQ
  rw [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_sub, Rat.cast_pow, Rat.cast_pow, k1, k2, k3, k4]

/-! ### 2. The per-cell unit rate -/

/-- The restricted per-unit bound of a certified cell. -/
noncomputable def plB (C : RSCell) : ℝ :=
  if (13 / 1000 : ℚ) * C.ub ≤ plCorrQ C.v C.w C.lam C.P then (987 / 1000 : ℝ) * C.ub else C.ub

/-- **The restricted integral of a certified cell.** -/
theorem pl_int_le (hN : 0 < N) (C : RSCell) (hok : rsCellOK C = true) :
    ∫ y in ((C.v : ℝ) ^ 4)..1, y ^ ((C.P : ℝ) / 4) * plG N C.lam ((C.w : ℝ) ^ 4) y ≤
      fsI C - ((plCorrQ C.v C.w C.lam C.P : ℚ) : ℝ) + 1 / N := by
  have h' := hok
  simp only [rsCellOK, Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hvw⟩, hw1⟩, hv1⟩, hw2⟩, -⟩, -⟩, h0⟩, h1⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h'
  have hv' : (0 : ℝ) < C.v := by exact_mod_cast hv
  have hw' : (0 : ℝ) < C.w := by exact_mod_cast (lt_of_lt_of_le hv hvw)
  have ha : (0 : ℝ) < (C.v : ℝ) ^ 4 := by positivity
  have ha1 : (C.v : ℝ) ^ 4 ≤ 1 := pow_le_one₀ hv'.le (by exact_mod_cast hv1.le)
  have hc : (0 : ℝ) < (C.w : ℝ) ^ 4 := by positivity
  have hcont : ∀ g : ℝ → ℝ, ContinuousOn g (Set.Icc ((C.v : ℝ) ^ 4) 1) →
      IntervalIntegrable (fun y => y ^ ((C.P : ℝ) / 4) * g y) volume ((C.v : ℝ) ^ 4) 1 := by
    intro g hg
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le ha1]
    exact (ContinuousOn.rpow_const continuousOn_id fun y hy => Or.inl (lt_of_lt_of_le ha hy.1).ne').mul hg
  have hy0 : ∀ y ∈ Set.Icc ((C.v : ℝ) ^ 4) 1, y ≠ 0 := fun y hy => (lt_of_lt_of_le ha hy.1).ne'
  have hmc : ContinuousOn (fun y : ℝ => (1 - y) * (min 1 ((C.w : ℝ) ^ 4 / y)) ^ C.lam)
      (Set.Icc ((C.v : ℝ) ^ 4) 1) :=
    (continuousOn_const.sub continuousOn_id).mul
      ((ContinuousOn.inf continuousOn_const (ContinuousOn.div continuousOn_const continuousOn_id hy0)).pow _)
  have hsplit : ∀ y, y ^ ((C.P : ℝ) / 4) * plG N C.lam ((C.w : ℝ) ^ 4) y =
      y ^ ((C.P : ℝ) / 4) * gX C.lam ((C.w : ℝ) ^ 4) y -
        y ^ ((C.P : ℝ) / 4) * ((1 - y) * (min 1 ((C.w : ℝ) ^ 4 / y)) ^ C.lam) +
        y ^ ((C.P : ℝ) / 4) * (1 / N) := fun y => by unfold plG; ring
  simp_rw [hsplit]
  rw [intervalIntegral.integral_add ((hcont _ (gX_continuousOn _ _ ha)).sub (hcont _ hmc))
      (hcont _ continuousOn_const), intervalIntegral.integral_sub (hcont _ (gX_continuousOn _ _ ha))
      (hcont _ hmc), plCorr_eq C.v C.w hv hvw hw1 C.lam C.P h0 h1]
  have hI : ∫ y in ((C.v : ℝ) ^ 4)..1, y ^ ((C.P : ℝ) / 4) * gX C.lam ((C.w : ℝ) ^ 4) y = fsI C := rfl
  rw [hI]
  have hlast : ∫ y in ((C.v : ℝ) ^ 4)..1, y ^ ((C.P : ℝ) / 4) * (1 / (N : ℝ)) ≤ 1 / N := by
    calc ∫ y in ((C.v : ℝ) ^ 4)..1, y ^ ((C.P : ℝ) / 4) * (1 / (N : ℝ))
        ≤ ∫ _y in ((C.v : ℝ) ^ 4)..1, (1 / (N : ℝ)) := by
          refine intervalIntegral.integral_mono_on ha1 (hcont _ continuousOn_const) intervalIntegrable_const
            fun y hy => ?_
          have : y ^ ((C.P : ℝ) / 4) ≤ 1 := Real.rpow_le_one (by linarith [hy.1]) hy.2 (by positivity)
          have : (0 : ℝ) ≤ 1 / N := by positivity
          nlinarith
      _ = (1 - (C.v : ℝ) ^ 4) * (1 / N) := by rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ 1 / N := by
          have : (0 : ℝ) ≤ 1 / N := by positivity
          nlinarith
  linarith

/-- **The unit rate of a certified restricted cell.** -/
theorem pl_unit (C : RSCell) (hok : rsCellOK C = true) (hpl : plOK C = true) :
    fsI C - ((plCorrQ C.v C.w C.lam C.P : ℚ) : ℝ) ≤ plB C ∧ fsI C ≤ 2 * plB C ∧ (1 : ℝ) / 203 ≤ plB C ∧
      Real.log 2 + Real.log (plB C) + Real.log (rsEx C.lu : ℝ) + ((C.P : ℝ) / 4 + C.lu) * x0 ≤ -(plR : ℝ) := by
  have h' := hok
  simp only [rsCellOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hvw⟩, hw1⟩, hv1⟩, hw2⟩, hk⟩, hp⟩, h0⟩, h1⟩, hub⟩, hq⟩, hx⟩, hhi⟩, hrate⟩ := h'
  have hI := cellIq_eq C.v C.w hv hvw hw1 C.lam C.P
    (fun k hkm => hk k (Finset.mem_range.1 hkm)) hp h0 h1
  have hIub : fsI C ≤ (C.ub : ℝ) := by
    unfold fsI; rw [← hI]; exact_mod_cast hub
  have hIpos := fs_cell_pos C hok
  have hub0 : (0 : ℝ) < C.ub := lt_of_lt_of_le hIpos hIub
  have hEx0 : (0 : ℝ) < rsEx C.lu := by
    have : (0 : ℚ) < rsEx C.lu := by
      unfold rsEx
      have : ((1 : ℚ) / 2) ^ (C.lu + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      apply div_pos (by linarith) (by positivity)
    exact_mod_cast this
  have hcr := crLog_le (q := 2 * C.ub * rsEx C.lu) (r := C.r) C.k C.n (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hq, hx⟩, hhi⟩)
  have hsplit : Real.log (((2 * C.ub * rsEx C.lu : ℚ)) : ℝ) =
      Real.log 2 + Real.log (C.ub : ℝ) + Real.log (rsEx C.lu : ℝ) := by
    push_cast
    rw [Real.log_mul (by positivity) hEx0.ne', Real.log_mul (by norm_num) hub0.ne']
  have ht : (0 : ℝ) ≤ (C.P : ℝ) / 4 + C.lu := by positivity
  have hx0 := cr_x0_bounds.2
  have htx : ((C.P : ℝ) / 4 + C.lu) * x0 ≤ ((C.P : ℝ) / 4 + C.lu) * (crX0hi : ℝ) :=
    mul_le_mul_of_nonneg_left hx0 ht
  have hbase : Real.log 2 + Real.log (C.ub : ℝ) + Real.log (rsEx C.lu : ℝ) + ((C.P : ℝ) / 4 + C.lu) * x0 ≤
      (C.r : ℝ) + ((C.P : ℝ) / 4 + C.lu) * (crX0hi : ℝ) := by linarith
  have hr0 : (C.r : ℝ) + ((C.P : ℝ) / 4 + C.lu) * (crX0hi : ℝ) ≤ -(rsR0 : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 hrate; push_cast at this; exact this
  simp only [plOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hpl
  obtain ⟨⟨h200, hc0⟩, hcase⟩ := hpl
  have h200' : (1 : ℝ) / 200 ≤ C.ub := by
    have := (Rat.cast_le (K := ℝ)).2 h200; push_cast at this; exact this
  have hc0' : (0 : ℝ) ≤ ((plCorrQ C.v C.w C.lam C.P : ℚ) : ℝ) := by exact_mod_cast hc0
  have hplR : (plR : ℝ) = rsR0 + 13 / 1000 := by unfold plR; push_cast; ring
  by_cases h13 : (13 / 1000 : ℚ) * C.ub ≤ plCorrQ C.v C.w C.lam C.P
  · have hB : plB C = (987 / 1000 : ℝ) * C.ub := by unfold plB; rw [if_pos h13]
    have h13' : (13 / 1000 : ℝ) * C.ub ≤ ((plCorrQ C.v C.w C.lam C.P : ℚ) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).2 h13; push_cast at this; exact this
    rw [hB]
    refine ⟨by linarith, by linarith, by linarith, ?_⟩
    rw [Real.log_mul (by norm_num) hub0.ne']
    have hl : Real.log (987 / 1000 : ℝ) ≤ -(13 / 1000) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 987 / 1000 by norm_num); linarith
    rw [hplR]; linarith
  · have hB : plB C = C.ub := by unfold plB; rw [if_neg h13]
    rcases hcase with h | h
    · exact absurd h h13
    have h' : (C.r : ℝ) + ((C.P : ℝ) / 4 + C.lu) * (crX0hi : ℝ) ≤ -(plR : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).2 h; push_cast at this; exact this
    rw [hB]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end Census
end IIT
