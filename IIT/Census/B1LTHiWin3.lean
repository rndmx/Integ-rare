/-
Census, B1 LTBetaHi, module T2 (windowing, step 2): **the windowed good event at the original rate**.

`lt3W_not_good_ev` (B1LTHiWin2) bounds the windowed bad event by `3e^{-1.05N}`, spending a whole `e^{-1.05N}` on the
extra member exclusion. Unfolding the four pieces of `lt3_not_good_le` instead, the five exclusions cost
`4e^{-2N} + e^{-1.05N} ≤ 2e^{-1.05N}`: the rate of `lt3_not_good_ev` is kept, for every bin count `n`
(`lt3W_not_good_ev2`). Together with `lt3W_good_F` this is the probability side of the windowed selection.
-/
import IIT.Census.B1LTHiWin2

namespace IIT
namespace Census

open MeasureTheory Finset

/-- **The windowed good event has probability `≥ 1 - 2e^{-1.05N}`**, for any number `n + 1` of bins
(parameters as `lt3_not_good_ev`). -/
theorem lt3W_not_good_ev2 (s : ∀ N, State N) (ε : ℝ) (n : ℕ) {D : ℕ} (hD : 1 ≤ D) :
    ∀ᶠ N : ℕ in Filter.atTop,
      cubeM N {w | ¬ lt3WGood (s N) ε lt3γ n (N / 20) (N / 600) 14 (N * N / D) w} ≤
        ENNReal.ofReal (2 * Real.exp (-((105 / 100 : ℝ) * N))) := by
  classical
  filter_upwards [lt2_Sp_ev, Filter.eventually_ge_atTop (10 ^ 6 * D)] with N hSp hN
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hNbig : 10 ^ 6 ≤ N := le_trans (Nat.le_mul_of_pos_right _ hD) hN
  have hNr : (10 : ℝ) ^ 6 * D ≤ N := by exact_mod_cast hN
  have hN0 : 0 < N := by omega
  have h1 := lt3_unit_all_excl_le (N := N) (k := N / 20) (K := N / 600) hN0 (by omega) (by omega) (by omega)
  have h2 := lt3_u_excl_leD (N := N) (s N) (γ := lt3γ) (lam := 3600) (D := 1200) lt3γ_pos.le
    (by unfold lt3γ; linarith) (by norm_num) (by norm_num) (K := N / 600) (by
      have : N ≤ 1200 * (N / 600) := by omega
      exact_mod_cast this)
  have hMfl : N * N ≤ 2 * D * (N * N / D) := by
    have h := Nat.div_add_mod (N * N) D
    have hm := Nat.mod_lt (N * N) (show 0 < D by omega)
    have : 2 * D ≤ N * N := by nlinarith
    nlinarith
  have hMr : (N : ℝ) * N ≤ 2 * D * (N * N / D : ℕ) := by exact_mod_cast hMfl
  have hl3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have h4 := lt3_member_ev_le (N := N) (s N) ε lt3γ (k := N / 20) (b := 14) (M := N * N / D) (D := 2 * D)
    (by omega) (by norm_num) (by omega) (by omega) hMfl (by
      have hlog : Real.log (8 * 14 * ((2 * D : ℕ) : ℝ)) ≤ 8 * 14 * ((2 * D : ℕ) : ℝ) :=
        (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
      push_cast at hlog ⊢
      norm_num at hNr hlog ⊢
      linarith) (by
      push_cast
      have hNN : (N : ℝ) * (10 ^ 6 * D) ≤ N * N := mul_le_mul_of_nonneg_left hNr (Nat.cast_nonneg N)
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
      nlinarith)
  have h5 := lt3W_member_ev_le (N := N) (s N) ε lt3γ n (k := N / 20) (b := 14) (M := N * N / D) (D := 2 * D)
    (by omega) (by norm_num) (by omega) (by omega) hMfl (by
      have hlog : Real.log (8 * 14 * ((2 * D : ℕ) : ℝ)) ≤ 8 * 14 * ((2 * D : ℕ) : ℝ) :=
        (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
      push_cast at hlog ⊢
      norm_num at hNr hlog ⊢
      linarith) (by
      push_cast
      have hNN : (N : ℝ) * (10 ^ 6 * D) ≤ N * N := mul_le_mul_of_nonneg_left hNr (Nat.cast_nonneg N)
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
      nlinarith)
  have hsub : {w | ¬ lt3WGood (s N) ε lt3γ n (N / 20) (N / 600) 14 (N * N / D) w} ⊆
      {w | ¬ lt3Good (s N) ε lt3γ (N / 20) (N / 600) 14 (N * N / D) w} ∪
      {w | 7 ≤ (lt3WQ (s N) ε lt3γ n w).card ∧ (lt3Base (s N) w).card ≤ 14 ∧
        N * N / D ≤ ((qFam (lt3WQ (s N) ε lt3γ n w)).filter fun S => ∃ r ∈ lt3Base (s N) w, ∃ R ⊆ S,
          2 ≤ R.card ∧ ¬ stRobust N (N / 20) (w (flipS r R))).card} := by
    intro w hw
    by_cases h1 : lt3Good (s N) ε lt3γ (N / 20) (N / 600) 14 (N * N / D) w
    · right
      by_contra h2
      exact hw ⟨h1, h2⟩
    · exact Or.inl h1
  have e2 : Real.exp ((Real.log 2 - 3600 / 1200) * N) ≤ Real.exp (-(2 * (N : ℝ))) := Real.exp_le_exp.2 (by
    have := Real.log_two_lt_d9; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; nlinarith)
  have e4 : 4 * Real.exp (-(2 * (N : ℝ))) ≤ Real.exp (-((105 / 100 : ℝ) * N)) := by
    have e : Real.exp (-((105 / 100 : ℝ) * N)) = Real.exp (-(2 * (N : ℝ))) * Real.exp (95 / 100 * N) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have h1 := Real.add_one_le_exp (95 / 100 * (N : ℝ))
    have h2 : (10 : ℝ) ^ 6 ≤ N := by exact_mod_cast hNbig
    nlinarith [Real.exp_pos (-(2 * (N : ℝ)))]
  have hE := Real.exp_pos (-((105 / 100 : ℝ) * N))
  have hE2 := Real.exp_pos (-(2 * (N : ℝ)))
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  calc _ ≤ ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) + ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) +
        ENNReal.ofReal (Real.exp (-((105 / 100 : ℝ) * N))) + ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) +
        ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) :=
        add_le_add ((lt3_not_good_le (s N) ε lt3γ (N / 20) (N / 600) 14 (N * N / D)).trans
          (add_le_add (add_le_add (add_le_add h1 (h2.trans (ENNReal.ofReal_le_ofReal e2))) hSp) h4)) h5
    _ = ENNReal.ofReal (4 * Real.exp (-(2 * (N : ℝ))) + Real.exp (-((105 / 100 : ℝ) * N))) := by
        rw [← ENNReal.ofReal_add hE2.le hE2.le, ← ENNReal.ofReal_add (by positivity) hE.le,
          ← ENNReal.ofReal_add (by positivity) hE2.le, ← ENNReal.ofReal_add (by positivity) hE2.le]
        congr 1; ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

end Census
end IIT
