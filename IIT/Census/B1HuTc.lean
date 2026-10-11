/-
Census, B1 forced leaf 7, `NatLT3Hu` part (b), `s = tc` (W12 §7): on `bNat ∩ {s = tc}`, off the proved rare
events (Tier 3, concentration, LTβ at level `9/20`), `Fᶜ_j > 9/20` and every entry of row `s` is `≥ 2/3`
(`htc_floor`). Row `s` is fixed (no union over rows): probability `(1/3)^N`, rate `ln 3 > 1.03`.

* `htc_two_rpow`, **`htc_floor`**, `htc_row_bound`, **`natTc_rare`**.
-/
import IIT.Census.B1LTBeta920
import IIT.Census.B1NotHu
import IIT.Census.B1ForcedFinal2
import IIT.Census.B1Rest6Final
import IIT.Census.PairSecond2

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

lemma htc_two_rpow : (27 / 20 : ℝ) < (2 : ℝ) ^ ((9 : ℝ) / 20) := by
  by_contra h
  push Not at h
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((9 : ℝ) / 20) := by positivity
  have h4 : ((2 : ℝ) ^ ((9 : ℝ) / 20)) ^ (20 : ℕ) = 2 ^ (9 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have : ((2 : ℝ) ^ ((9 : ℝ) / 20)) ^ (20 : ℕ) ≤ (27 / 20 : ℝ) ^ (20 : ℕ) := pow_le_pow_left₀ h0 h 20
  rw [h4] at this
  norm_num at this

/-- **The floor at level `9/20`** (deterministic): `Fᶜ_j > 9/20` and concentration give `y_{tc,j} ≥ 2/3`. -/
theorem htc_floor {s : State N} {w : Param N} (ho : w ∈ openCube N) (hDN : DU N ≤ N - 1)
    (hcC : concCAt N w (tcRow w)) (hδ : dU N (N - 1) ≤ 1 / 10000) {j : Fin N}
    (hF : 9 / 20 < kF (lamCz (flipP s w) s (tcRow w)) j) : 2 / 3 ≤ clamp01 (w (tcRow w) j) := by
  have hz : flipP s w ∈ openCube N := flipP_mem_openCube ho
  obtain ⟨mc1, -, mc3, -, mc5⟩ := lamCz_means hz s (tcRow w)
  rw [flipP_invol s w] at mc1 mc3 mc5
  have hk : kF (lamCz (flipP s w) s (tcRow w)) j =
      Real.logb 2 (clamp01 (w (tcRow w) j) / cmean w (univ \ univ.erase j) (tcRow w) j) := mc1 j (univ.erase j)
  rw [hk] at hF
  have hcard : (univ.erase j).card = N - 1 := by
    rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
  have hA := hcC j (univ.erase j) (notMem_erase j univ) (by rw [hcard]; exact hDN)
  rw [hcard] at hA
  have hAlo : 1 / 2 - 1 / 10000 ≤ cmean w (univ \ univ.erase j) (tcRow w) j := by
    have := (abs_le.1 hA).1; linarith
  have hA0 : 0 < cmean w (univ \ univ.erase j) (tcRow w) j := by linarith
  have hy0 := mc3 j
  have hpos : 0 < clamp01 (w (tcRow w) j) / cmean w (univ \ univ.erase j) (tcRow w) j := div_pos hy0 hA0
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) hpos, lt_div_iff₀ hA0] at hF
  have h2 := htc_two_rpow
  nlinarith

/-- **Row `s` above `2/3`**: probability `(1/3)^N`. -/
theorem htc_row_bound (s : State N) :
    cubeM N {w | ∀ i, 2 / 3 ≤ clamp01 (w s i)} ≤ ENNReal.ofReal ((1 / 3 : ℝ) ^ N) := by
  classical
  set S : State N → Fin N → Set ℝ := fun r _ => if r = s then {y | 2 / 3 ≤ clamp01 y} else Set.univ with hS
  have hsub : {w : Param N | ∀ i, 2 / 3 ≤ clamp01 (w s i)} ⊆ {w | ∀ r j, w r j ∈ S r j} := by
    intro w hw r j
    simp only [hS]
    split_ifs with h
    · subst h; exact hw j
    · trivial
  refine (measure_mono hsub).trans ?_
  rw [ps_cubeM_rows]
  have hone : ∀ r, ∏ j, unif (S r j) = if r = s then ENNReal.ofReal ((1 / 3 : ℝ) ^ N) else 1 := by
    intro r
    by_cases h : r = s
    · rw [if_pos h]
      have hu : unif {y : ℝ | 2 / 3 ≤ clamp01 y} = ENNReal.ofReal (1 / 3) := by
        have e : {y : ℝ | 2 / 3 ≤ clamp01 y} ∩ Set.Icc 0 1 = Set.Icc (2 / 3) 1 := by
          ext y
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc]
          constructor
          · rintro ⟨h1, h2, h3⟩
            rw [clamp01_of_mem ⟨h2, h3⟩] at h1; exact ⟨h1, h3⟩
          · rintro ⟨h1, h3⟩
            refine ⟨?_, by linarith, h3⟩
            rw [clamp01_of_mem ⟨by linarith, h3⟩]; exact h1
        unfold unif
        rw [Measure.restrict_apply (measurableSet_le measurable_const continuous_clamp01.measurable), e,
          Real.volume_Icc]
        norm_num
      simp only [hS, if_pos h, hu, prod_const, card_univ, Fintype.card_fin]
      rw [ENNReal.ofReal_pow (by norm_num)]
    · rw [if_neg h]
      simp only [hS, if_neg h, measure_univ, prod_const_one]
  simp_rw [hone]
  rw [prod_ite_eq' univ s]
  simp

/-- `(1/3)^N ≤ e^{-1.0986 N}`-type numerics: `1/3 ≤ e^{-1.05}`. -/
lemma htc_num : (1 / 3 : ℝ) ≤ Real.exp (-(105 / 100)) := by
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  have h := Real.exp_one_lt_d9
  have h5 : Real.exp (5 / 100) ≤ 1 / (1 - 5 / 100) := by
    have := Real.add_one_le_exp (-(5 / 100 : ℝ))
    have hm : Real.exp (5 / 100) * Real.exp (-(5 / 100)) = 1 := by rw [← Real.exp_add]; norm_num
    have hp := Real.exp_pos (5 / 100 : ℝ)
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hs : Real.exp (105 / 100) = Real.exp 1 * Real.exp (5 / 100) := by rw [← Real.exp_add]; norm_num
  rw [hs, inv_div, div_one]
  calc Real.exp 1 * Real.exp (5 / 100) ≤ 2.7182818286 * (1 / (1 - 5 / 100)) :=
        mul_le_mul h.le h5 (Real.exp_pos _).le (by norm_num)
    _ ≤ 3 := by norm_num

/-- **`s = tc` is rare in the natural regime** (rate `1.03`). -/
theorem natTc_rare : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bNat N s ∩ {w | s = tcRow w}) ≤ ENNReal.ofReal (Real.exp (-(103 / 100 * N))) := by
  set Cm : ℝ := 1035 / 1000 with hCm
  have hT3 : NatTier3Stmt Cm :=
    natTier3_of_rest6 (by norm_num) (by norm_num) natTier3Rest6_proved (lt2_at (by norm_num))
      (ltBeta_at (by norm_num))
  filter_upwards [hT3, ltBeta920_at (C := Cm) (by norm_num), ev_N_dU_top, eventually_ge_atTop 64, g_superexp Cm,
    g_absorb 7 (show (103 / 100 : ℝ) < Cm by norm_num)] with N hT hLb htop hN64 hS hA s
  classical
  have hN3 : 3 ≤ N := by omega
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hDN : DU N ≤ N - 1 := DU_le hN64
  have hδ : dU N (N - 1) ≤ 1 / 10000 := by
    have : dU N (N - 1) ≤ N * dU N (N - 1) := le_mul_of_one_le_left (dU_nonneg N _) (by linarith)
    linarith
  set M : Set (Param N) := {w | ∀ i, 2 / 3 ≤ clamp01 (w s i)} with hM
  set c := 2 ^ N * (N * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2))) with hc
  have hsub : bNat N s ∩ {w | s = tcRow w} ⊆
      (((bNat N s ∩ {w | ¬ ∀ j, phi (flipP s w) s univ ≤ betaW w * kF (lamCz (flipP s w) s (tcRow w)) j}) ∪
        {w | ¬ concCAt N w (tcRow w)}) ∪ (B1w N s ∩ openCube N ∩
          {w | ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 9 / 20 * betaW w})) ∪ M := by
    rintro w ⟨⟨⟨hBw, ho⟩, hNat⟩, htc⟩
    by_contra hall
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, not_or, not_and, not_not, not_forall,
      not_lt] at hall
    obtain ⟨⟨⟨h1, h2⟩, h4⟩, h5⟩ := hall
    have hT3w : ∀ j, phi (flipP s w) s univ ≤ betaW w * kF (lamCz (flipP s w) s (tcRow w)) j := by
      intro j; by_contra hc'; exact h1 ⟨⟨hBw, ho⟩, hNat⟩ ⟨j, by simpa using hc'⟩
    obtain ⟨S, hS2, hS3, hSβ⟩ := h4 ⟨hBw, ho⟩
    have hβ0 := betaW_pos ho
    have hlt := dt_B1_lt hBw (by rw [← card_pos]; omega) (dt_card_ne_univ hS3 (by omega))
    have hF : ∀ j, 9 / 20 < kF (lamCz (flipP s w) s (tcRow w)) j := by
      intro j
      have h := hT3w j
      by_contra hc'
      push Not at hc'
      have : betaW w * kF (lamCz (flipP s w) s (tcRow w)) j ≤ betaW w * (9 / 20) :=
        mul_le_mul_of_nonneg_left hc' hβ0.le
      linarith
    apply h5
    intro i
    have := htc_floor ho hDN h2 hδ (hF i)
    rwa [← htc] at this
  have hMb : cubeM N M ≤ ENNReal.ofReal (Real.exp (-(Cm * N))) := by
    refine (htc_row_bound s).trans (ENNReal.ofReal_le_ofReal ?_)
    calc (1 / 3 : ℝ) ^ N ≤ Real.exp (-(105 / 100)) ^ N := pow_le_pow_left₀ (by norm_num) htc_num N
      _ = Real.exp (-(105 / 100 * N)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-(Cm * N)) := Real.exp_le_exp.2 (by rw [hCm]; nlinarith)
  have hc0 : 0 ≤ c := by positivity
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add (hT s) (concTc_rare hN3 s))) (hLb s))) hMb).trans ?_
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le hc0, ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le,
    ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have hS' : 2 * c ≤ Real.exp (-(Cm * N)) := hS
  have hA' : 7 * Real.exp (-(Cm * N)) ≤ Real.exp (-(103 / 100 * N)) := hA
  have := Real.exp_pos (-(Cm * N))
  clear_value Cm c
  linarith

end Census
end IIT
