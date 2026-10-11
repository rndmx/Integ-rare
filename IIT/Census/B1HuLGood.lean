/-
Census, B1 forced leaf 7, `NatLT3Hu` part (c) (light `s`, W12 §3.3/§7(c)/§8), stage **Good**: the good event and
the member count at `ε = dnEps = 10⁻⁵`.

**The constants of the `ε = 10⁻⁵` light chain** (fixed here, reused by the later `B1HuL*` stages):
* `ε = dnEps = 1/10^5`; `Top = lt3TopG w ε` for light `s` (`¬ lt3SpC s w`), `N/10^5 ≤ |Top| ≤ N/20`.
* level `t = lt3tE5 = 1/400000` (`= ε/4`), window loss `ω' = lt3ωE5 = 1/1600000000` (`= t/4000`),
  box `ρ = lt3ρE5 = 1/20800000000` (`13ρ = t/4000`), grid `n_g = lt3ngE5 = 3200000000` (`= 2/ω'`, `5 ∣ n_g`),
  bins `n_b = lt3nbE5 = 41599999999` (`13/(n_b+1) = ω'/2`), so `13/(n_b+1) + 1/n_g = ω'` (`lt3ωE5_bins`).
* robust window `k = N/20` (unchanged), exclusion count `K = N/3000000` (`= εN/30`, so `15K ≤ |Top|/2`),
  near-half width `γ = lt3γE5 = e^{-λ}/2`, `λ = 2·10^7` (`lt3_u_excl_leD` at ratio `6·10^6`: rate `λ/(6·10^6) - ln 2 ≥ 2`).
* window constant `C = lt3CnE5 = ((n_b+1)²)^14`, member-count scale `M = N²/(10^21 C²)`, kept-family size
  `m ≥ N/(10^10 C)` (`lt3W_good_FE5`, for `N ≥ 10^12 C`), adverse scale `D0 = lt3D0E5 = 2·10^10 C`
  (`N ≤ D0 m`, `lt3_ND0E5`), adverse level `κ = lt3κE5 = lt2κ + 100 D0` (`lt3_adv_evE5`), band level
  `L = lt3LcE5 = 307200000000 κ` (`768000 κ = t L`, `lt3_phiH_le`).
* effect box `ρe = lt3ρeE5 = γ/100`, effect floor `lt3E0eE5`, light success probability
  `lt3pLE5 = ρ^234 ρe^24`.
* Level (`lt3_levelE5`): `c0 ≥ y - ω'`, `y ≥ 1/2` ⇒ `(1-ε) Lv y β ≤ Lv c0 (1 - 483t/800) β`.

Main results: `lt3_not_good_evE5`, `lt3W_not_good_ev2E5` (bad event `≤ 2e^{-1.05N}`, any `ε`, any bin count),
`lt3_good_QE5`, `lt3W_good_FE5`, `lt3W_good_F_lightE5` (on the good event at `ε = dnEps`: `m ≥ N/(10^10 C)`,
`|lt3WQ| ≥ 7`, `m² ≤ 2|lt3WF|`), `lt3_adv_evE5` (`lt3_adv_ev` at the new `D0`, `κ`).
-/
import IIT.Census.B1LTHiWin3
import IIT.Census.B1LTHiT7b
import IIT.Census.B1ForcedDNat

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

set_option linter.unusedSectionVars false

variable {N : ℕ}

/-! ### The constants -/

/-- The level `t = ε/4`. -/
def lt3tE5 : ℚ := 1 / 400000

/-- The window loss `ω' = t/4000`. -/
noncomputable def lt3ωE5 : ℝ := 1 / 1600000000

/-- The box radius `ρ` (`13ρ = t/4000`). -/
noncomputable def lt3ρE5 : ℝ := 1 / 20800000000

/-- The grid `n_g = 2/ω'`. -/
def lt3ngE5 : ℕ := 3200000000

/-- The bins `n_b` (`13/(n_b+1) = ω'/2`). -/
def lt3nbE5 : ℕ := 41599999999

/-- The near-half exponent `λ`. -/
noncomputable def lt3lamE5 : ℝ := 20000000

/-- The near-half width `γ = e^{-λ}/2`. -/
noncomputable def lt3γE5 : ℝ := Real.exp (-20000000) / 2

/-- The window constant `((n_b + 1)²)^{14}`. -/
def lt3CnE5 : ℕ := ((lt3nbE5 + 1) * (lt3nbE5 + 1)) ^ 14

/-- The adverse-count scale `D0 = 2 · 10^10 C`. -/
def lt3D0E5 : ℕ := 2 * 10 ^ 10 * lt3CnE5

/-- The adverse level `κ`. -/
noncomputable def lt3κE5 : ℝ := lt2κ + 100 * (lt3D0E5 : ℝ)

/-- The band level `L = 307200000000 κ` (so that `768000 κ = t L`). -/
noncomputable def lt3LcE5 : ℝ := 307200000000 * lt3κE5

/-- The effect box radius. -/
noncomputable def lt3ρeE5 : ℝ := lt3γE5 / 100

/-- The effect floor of Lemma EF at `γ`, `ρe`. -/
noncomputable def lt3E0eE5 : ℝ := (1 / 2 + lt3γE5) ^ 3 * Real.logb 2 (1 / (1 - (1 / 2 + lt3γE5 - lt3ρeE5) / 2))

/-- The success probability of a light member. -/
noncomputable def lt3pLE5 : ℝ := lt3ρE5 ^ 234 * lt3ρeE5 ^ 24

/-! ### Numeric facts about the constants -/

lemma lt3tE5_pos : 0 < lt3tE5 := by unfold lt3tE5; norm_num

lemma lt3tE5_le : lt3tE5 ≤ 1 / 80 := by unfold lt3tE5; norm_num

lemma lt3tE5_real : ((lt3tE5 : ℚ) : ℝ) = 1 / 400000 := by unfold lt3tE5; push_cast; ring

lemma lt3ngE5_pos : 0 < lt3ngE5 := by unfold lt3ngE5; norm_num

lemma lt3ngE5_dvd : 5 ∣ lt3ngE5 := by unfold lt3ngE5; norm_num

lemma lt3ωE5_bins : 13 * (1 / ((lt3nbE5 + 1 : ℕ) : ℝ)) + 1 / (lt3ngE5 : ℝ) ≤ lt3ωE5 := by
  unfold lt3nbE5 lt3ngE5 lt3ωE5; push_cast; norm_num

lemma lt3ωE5_t : lt3ωE5 ≤ ((lt3tE5 : ℚ) : ℝ) / 4000 := by
  rw [lt3tE5_real]; unfold lt3ωE5; norm_num

lemma lt3ωE5_pos : 0 < lt3ωE5 := by unfold lt3ωE5; norm_num

lemma lt3ρE5_pos : 0 < lt3ρE5 := by unfold lt3ρE5; norm_num

lemma lt3ρE5_le : lt3ρE5 ≤ 1 := by unfold lt3ρE5; norm_num

lemma lt3ρE5_t : 13 * lt3ρE5 ≤ ((lt3tE5 : ℚ) : ℝ) / 4000 := by
  rw [lt3tE5_real]; unfold lt3ρE5; norm_num

lemma lt3γE5_pos : 0 < lt3γE5 := by unfold lt3γE5; positivity

lemma lt3γE5_lt : lt3γE5 < 1 / 2 := by
  unfold lt3γE5
  have : Real.exp (-20000000) < Real.exp 0 := Real.exp_lt_exp.2 (by norm_num)
  rw [Real.exp_zero] at this
  linarith

lemma lt3γE5_exp : 2 * lt3γE5 ≤ Real.exp (-lt3lamE5) := by unfold lt3γE5 lt3lamE5; linarith

lemma lt3CnE5_pos : 0 < lt3CnE5 := by unfold lt3CnE5; positivity

lemma lt3CnE5_ge : ((lt3nbE5 + 1) * (lt3nbE5 + 1)) ^ 14 ≤ lt3CnE5 := le_rfl

lemma lt3D0E5_pos : 1 ≤ lt3D0E5 := by unfold lt3D0E5; have := lt3CnE5_pos; omega

lemma lt3κE5_ge : lt2κ ≤ lt3κE5 := by
  unfold lt3κE5; have : (0 : ℝ) ≤ lt3D0E5 := Nat.cast_nonneg _; linarith

lemma lt3κE5_pos : 0 < lt3κE5 := lt_of_lt_of_le (by unfold lt2κ; norm_num) lt3κE5_ge

lemma lt3LcE5_pos : 0 < lt3LcE5 := by unfold lt3LcE5; have := lt3κE5_pos; positivity

lemma lt3LcE5_one : 1 ≤ lt3LcE5 := by
  unfold lt3LcE5; have := lt3κE5_ge; unfold lt2κ at this; linarith

lemma lt3LcE5_κ : 768000 * lt3κE5 ≤ ((lt3tE5 : ℚ) : ℝ) * lt3LcE5 := by
  rw [lt3tE5_real]; unfold lt3LcE5; have := lt3κE5_pos; nlinarith

/-- The adverse-count condition of `lt3_adv_ev` at `D0 = lt3D0E5`, `κ = lt3κE5`. -/
lemma lt3κE5_sq : 4 * (3 * (96 * (lt3D0E5 : ℝ)) + Real.log (2 * Real.exp 1 * (96 * lt3D0E5))) ≤ lt3κE5 ^ 2 := by
  have hD : (1 : ℝ) ≤ lt3D0E5 := by exact_mod_cast lt3D0E5_pos
  have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hlog : Real.log (2 * Real.exp 1 * (96 * lt3D0E5)) ≤ 2 * Real.exp 1 * (96 * lt3D0E5) :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hκ : 100 * (lt3D0E5 : ℝ) ≤ lt3κE5 := by unfold lt3κE5 lt2κ; linarith
  have hκ2 : (100 * (lt3D0E5 : ℝ)) ^ 2 ≤ lt3κE5 ^ 2 := pow_le_pow_left₀ (by positivity) hκ 2
  have h1 : 2 * Real.exp 1 * (96 * (lt3D0E5 : ℝ)) ≤ 576 * lt3D0E5 := by nlinarith
  nlinarith

lemma lt3ρeE5_pos : 0 < lt3ρeE5 := by unfold lt3ρeE5; have := lt3γE5_pos; positivity

lemma lt3ρeE5_le : lt3ρeE5 ≤ 1 := by unfold lt3ρeE5; have := lt3γE5_lt; linarith

lemma lt3ρeE5_γ : lt3ρeE5 ≤ lt3γE5 := by unfold lt3ρeE5; have := lt3γE5_pos; linarith

lemma lt3ρeE5_B : 7 * lt3ρeE5 ≤ 3 * Real.log 2 * (2 * lt3γE5 * (1 / 2 + lt3γE5) ^ 2) := by
  have hγ := lt3γE5_pos
  have hl := Real.log_two_gt_d9
  have h1 : (1 / 4 : ℝ) ≤ (1 / 2 + lt3γE5) ^ 2 := by nlinarith
  have h2 : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith
  have h3 : 3 * (69 / 100) * (2 * lt3γE5 * (1 / 4)) ≤ 3 * Real.log 2 * (2 * lt3γE5 * (1 / 2 + lt3γE5) ^ 2) := by
    apply mul_le_mul (by linarith) (by nlinarith) (by positivity) (by positivity)
  unfold lt3ρeE5
  nlinarith

lemma lt3E0eE5_pos : 0 < lt3E0eE5 := by
  have hγ := lt3γE5_pos
  have hγ1 := lt3γE5_lt
  have hρ := lt3ρeE5_pos
  have hρ1 := lt3ρeE5_γ
  unfold lt3E0eE5
  refine mul_pos (by positivity) (Real.logb_pos (by norm_num) ?_)
  rw [lt_div_iff₀ (by linarith)]
  linarith

lemma lt3pLE5_pos : 0 < lt3pLE5 := by
  unfold lt3pLE5; have := lt3ρeE5_pos; have := lt3ρE5_pos; positivity

lemma lt3pLE5_le : lt3pLE5 ≤ 1 := by
  unfold lt3pLE5
  have h1 : lt3ρE5 ^ 234 ≤ 1 := pow_le_one₀ lt3ρE5_pos.le lt3ρE5_le
  have h2 : lt3ρeE5 ^ 24 ≤ 1 := pow_le_one₀ lt3ρeE5_pos.le lt3ρeE5_le
  have h3 : 0 ≤ lt3ρeE5 ^ 24 := by have := lt3ρeE5_pos; positivity
  nlinarith

/-- **The natural level** from Lemma TC' at `t = lt3tE5`, `ω' = lt3ωE5`: if `c0 ≥ y - ω'` and `y ≥ 1/2`, then
`(1 - ε) Lv y β ≤ Lv c0 (1 - 483t/800) β` (`ε = dnEps`, any `Lv, β ≥ 0`). -/
lemma lt3_levelE5 {Lv c0 y β : ℝ} (hLv : 0 ≤ Lv) (hβ : 0 ≤ β) (hy : 1 / 2 ≤ y) (hc : y - lt3ωE5 ≤ c0) :
    (1 - dnEps) * Lv * y * β ≤ Lv * c0 * (1 - 483 * ((lt3tE5 : ℚ) : ℝ) / 800) * β := by
  have key : (1 - dnEps) * y ≤ c0 * (1 - 483 * ((lt3tE5 : ℚ) : ℝ) / 800) := by
    rw [lt3tE5_real]; unfold dnEps; unfold lt3ωE5 at hc
    norm_num
    nlinarith
  calc (1 - dnEps) * Lv * y * β = Lv * ((1 - dnEps) * y) * β := by ring
    _ ≤ Lv * (c0 * (1 - 483 * ((lt3tE5 : ℚ) : ℝ) / 800)) * β :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key hLv) hβ
    _ = _ := by ring

/-! ### The good event at `K = N/3000000`, `γ = lt3γE5` -/

open Classical in
/-- **The good event has probability `≥ 1 - 2e^{-1.05N}`** (parameters `k = N/20`, `K = N/3000000`, `b = 14`,
`γ = lt3γE5`, `M = N²/D`; any `ε`). -/
theorem lt3_not_good_evE5 (s : ∀ N, State N) (ε : ℝ) {D : ℕ} (hD : 1 ≤ D) :
    ∀ᶠ N : ℕ in Filter.atTop,
      cubeM N {w | ¬ lt3Good (s N) ε lt3γE5 (N / 20) (N / 3000000) 14 (N * N / D) w} ≤
        ENNReal.ofReal (2 * Real.exp (-((105 / 100 : ℝ) * N))) := by
  filter_upwards [lt2_Sp_ev, Filter.eventually_ge_atTop (10 ^ 6 * D),
    Filter.eventually_ge_atTop 45000000] with N hSp hN hN45
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hNbig : 10 ^ 6 ≤ N := le_trans (Nat.le_mul_of_pos_right _ hD) hN
  have hNr : (10 : ℝ) ^ 6 * D ≤ N := by exact_mod_cast hN
  have hN0 : 0 < N := by omega
  have h1 := lt3_unit_all_excl_le (N := N) (k := N / 20) (K := N / 3000000) hN0 (by omega) (by omega)
    (by omega)
  have h2 := lt3_u_excl_leD (N := N) (s N) (γ := lt3γE5) (lam := 20000000) (D := 6000000) lt3γE5_pos.le
    (by unfold lt3γE5; linarith) (by norm_num) (by norm_num) (K := N / 3000000) (by
      have : N ≤ 6000000 * (N / 3000000) := by omega
      exact_mod_cast this)
  have hMfl : N * N ≤ 2 * D * (N * N / D) := by
    have h := Nat.div_add_mod (N * N) D
    have hm := Nat.mod_lt (N * N) (show 0 < D by omega)
    have : 2 * D ≤ N * N := by nlinarith
    nlinarith
  have hMr : (N : ℝ) * N ≤ 2 * D * (N * N / D : ℕ) := by exact_mod_cast hMfl
  have hl3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have h4 := lt3_member_ev_le (N := N) (s N) ε lt3γE5 (k := N / 20) (b := 14) (M := N * N / D) (D := 2 * D)
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
  refine (lt3_not_good_le (s N) ε lt3γE5 (N / 20) (N / 3000000) 14 (N * N / D)).trans ?_
  have e2 : Real.exp ((Real.log 2 - 20000000 / 6000000) * N) ≤ Real.exp (-(2 * (N : ℝ))) :=
    Real.exp_le_exp.2 (by
      have := Real.log_two_lt_d9; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; nlinarith)
  have e3 : 3 * Real.exp (-(2 * (N : ℝ))) ≤ Real.exp (-((105 / 100 : ℝ) * N)) := by
    have e : Real.exp (-((105 / 100 : ℝ) * N)) = Real.exp (-(2 * (N : ℝ))) * Real.exp (95 / 100 * N) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have h1 := Real.add_one_le_exp (95 / 100 * (N : ℝ))
    have h2 : (10 : ℝ) ^ 6 ≤ N := by exact_mod_cast hNbig
    nlinarith [Real.exp_pos (-(2 * (N : ℝ)))]
  have hE := Real.exp_pos (-((105 / 100 : ℝ) * N))
  calc _ ≤ ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) + ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) +
        ENNReal.ofReal (Real.exp (-((105 / 100 : ℝ) * N))) + ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) :=
        add_le_add (add_le_add (add_le_add h1 (h2.trans (ENNReal.ofReal_le_ofReal e2))) hSp) h4
    _ = ENNReal.ofReal (3 * Real.exp (-(2 * (N : ℝ))) + Real.exp (-((105 / 100 : ℝ) * N))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

/-- **The windowed good event has probability `≥ 1 - 2e^{-1.05N}`**, for any number `n + 1` of bins and any `ε`
(parameters as `lt3_not_good_evE5`). -/
theorem lt3W_not_good_ev2E5 (s : ∀ N, State N) (ε : ℝ) (n : ℕ) {D : ℕ} (hD : 1 ≤ D) :
    ∀ᶠ N : ℕ in Filter.atTop,
      cubeM N {w | ¬ lt3WGood (s N) ε lt3γE5 n (N / 20) (N / 3000000) 14 (N * N / D) w} ≤
        ENNReal.ofReal (2 * Real.exp (-((105 / 100 : ℝ) * N))) := by
  classical
  filter_upwards [lt2_Sp_ev, Filter.eventually_ge_atTop (10 ^ 6 * D),
    Filter.eventually_ge_atTop 45000000] with N hSp hN hN45
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hNbig : 10 ^ 6 ≤ N := le_trans (Nat.le_mul_of_pos_right _ hD) hN
  have hNr : (10 : ℝ) ^ 6 * D ≤ N := by exact_mod_cast hN
  have hN0 : 0 < N := by omega
  have h1 := lt3_unit_all_excl_le (N := N) (k := N / 20) (K := N / 3000000) hN0 (by omega) (by omega)
    (by omega)
  have h2 := lt3_u_excl_leD (N := N) (s N) (γ := lt3γE5) (lam := 20000000) (D := 6000000) lt3γE5_pos.le
    (by unfold lt3γE5; linarith) (by norm_num) (by norm_num) (K := N / 3000000) (by
      have : N ≤ 6000000 * (N / 3000000) := by omega
      exact_mod_cast this)
  have hMfl : N * N ≤ 2 * D * (N * N / D) := by
    have h := Nat.div_add_mod (N * N) D
    have hm := Nat.mod_lt (N * N) (show 0 < D by omega)
    have : 2 * D ≤ N * N := by nlinarith
    nlinarith
  have hMr : (N : ℝ) * N ≤ 2 * D * (N * N / D : ℕ) := by exact_mod_cast hMfl
  have hl3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have h4 := lt3_member_ev_le (N := N) (s N) ε lt3γE5 (k := N / 20) (b := 14) (M := N * N / D) (D := 2 * D)
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
  have h5 := lt3W_member_ev_le (N := N) (s N) ε lt3γE5 n (k := N / 20) (b := 14) (M := N * N / D) (D := 2 * D)
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
  have hsub : {w | ¬ lt3WGood (s N) ε lt3γE5 n (N / 20) (N / 3000000) 14 (N * N / D) w} ⊆
      {w | ¬ lt3Good (s N) ε lt3γE5 (N / 20) (N / 3000000) 14 (N * N / D) w} ∪
      {w | 7 ≤ (lt3WQ (s N) ε lt3γE5 n w).card ∧ (lt3Base (s N) w).card ≤ 14 ∧
        N * N / D ≤ ((qFam (lt3WQ (s N) ε lt3γE5 n w)).filter fun S => ∃ r ∈ lt3Base (s N) w, ∃ R ⊆ S,
          2 ≤ R.card ∧ ¬ stRobust N (N / 20) (w (flipS r R))).card} := by
    intro w hw
    by_cases h1 : lt3Good (s N) ε lt3γE5 (N / 20) (N / 3000000) 14 (N * N / D) w
    · right
      by_contra h2
      exact hw ⟨h1, h2⟩
    · exact Or.inl h1
  have e2 : Real.exp ((Real.log 2 - 20000000 / 6000000) * N) ≤ Real.exp (-(2 * (N : ℝ))) :=
    Real.exp_le_exp.2 (by
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
        add_le_add ((lt3_not_good_le (s N) ε lt3γE5 (N / 20) (N / 3000000) 14 (N * N / D)).trans
          (add_le_add (add_le_add (add_le_add h1 (h2.trans (ENNReal.ofReal_le_ofReal e2))) hSp) h4)) h5
    _ = ENNReal.ofReal (4 * Real.exp (-(2 * (N : ℝ))) + Real.exp (-((105 / 100 : ℝ) * N))) := by
        rw [← ENNReal.ofReal_add hE2.le hE2.le, ← ENNReal.ofReal_add (by positivity) hE.le,
          ← ENNReal.ofReal_add (by positivity) hE2.le, ← ENNReal.ofReal_add (by positivity) hE2.le]
        congr 1; ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

/-! ### Sizes on the good event at `ε = dnEps` -/

lemma lt3_ceil_boundsE5 (hN : 100000 ≤ N) : N / 100000 ≤ ⌈dnEps * N⌉₊ ∧ ⌈dnEps * N⌉₊ ≤ N / 20 := by
  have hNr : (100000 : ℝ) ≤ N := by exact_mod_cast hN
  have hε : dnEps * (N : ℝ) = (N : ℝ) / 100000 := by unfold dnEps; ring
  rw [hε]
  constructor
  · have : ((N / 100000 : ℕ) : ℝ) ≤ (N : ℝ) / 100000 := by
      have := Nat.cast_div_le (m := N) (n := 100000) (α := ℝ); push_cast at this ⊢; linarith
    exact Nat.cast_le.1 (this.trans (Nat.le_ceil _))
  · rw [Nat.ceil_le]
    have h20 : (N : ℝ) / 20 - 1 < ((N / 20 : ℕ) : ℝ) := by
      have : (N : ℝ) < ((N / 20 : ℕ) : ℝ) * 20 + 20 := by exact_mod_cast (by omega : N < N / 20 * 20 + 20)
      linarith
    linarith

/-- **`Top` and `Q` sizes on the good event** (`ε = dnEps`, `K = N/3000000`, `N ≥ 10^5`). -/
theorem lt3_good_QE5 (s : State N) {M : ℕ} (hN : 100000 ≤ N) {w : Param N}
    (hg : lt3Good s dnEps lt3γE5 (N / 20) (N / 3000000) 14 M w)
    (hGU : lt3SpC s w → ⌈dnEps * N⌉₊ ≤ (lt3GoodU s w).card) :
    (lt3Top s w dnEps).card ≤ N / 20 ∧ N / 100000 ≤ (lt3Top s w dnEps).card ∧
      N / 100000 - 15 * (N / 3000000) ≤ 2 ^ 14 * (lt3Q s dnEps lt3γE5 w).card := by
  obtain ⟨hc1, hc2⟩ := lt3_ceil_boundsE5 hN
  have hk1 : 1 ≤ ⌈dnEps * N⌉₊ := le_trans (by omega) hc1
  have hTle : (lt3Top s w dnEps).card ≤ N / 20 :=
    (lt3Top_card_le hk1 hg.1).trans hc2
  have hTge : N / 100000 ≤ (lt3Top s w dnEps).card := by
    refine hc1.trans ?_
    classical
    unfold lt3Top
    split_ifs with hc
    · rw [lt3TopP_card]; exact le_min le_rfl (hGU hc)
    · have := card_ge_yTopW w (ε := dnEps) (hc2.trans (Nat.div_le_self _ _))
      unfold lt3TopG; exact this
  obtain ⟨hB, hEx, hQ, -⟩ := lt3_good_sizes s dnEps lt3γE5 lt3γE5_lt (le_refl 14) hg hTle
  refine ⟨hTle, hTge, ?_⟩
  have h2 : 2 ^ (lt3Base s w).card ≤ 2 ^ 14 := Nat.pow_le_pow_right (by norm_num) hB
  have := Nat.mul_le_mul_right (lt3Q s dnEps lt3γE5 w).card h2
  have : ((lt3Base s w).card + 1) * (N / 3000000) ≤ 15 * (N / 3000000) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **The windowed kept family is large on the good event** (`ε = dnEps`, `C ≥ ((n+1)²)^{14}`,
`M = N²/(10^{21}C²)`, `N ≥ 10^{12} C`): `m ≥ N/(10^{10} C)`, `|lt3WQ| ≥ 7` and `m² ≤ 2|lt3WF|`. -/
theorem lt3W_good_FE5 (s : State N) (n : ℕ) {C : ℕ} (hC : ((n + 1) * (n + 1)) ^ 14 ≤ C) {w : Param N}
    (hN : 10 ^ 12 * C ≤ N)
    (hg : lt3WGood s dnEps lt3γE5 n (N / 20) (N / 3000000) 14 (N * N / (10 ^ 21 * C * C)) w)
    (hGU : lt3SpC s w → ⌈dnEps * N⌉₊ ≤ (lt3GoodU s w).card) :
    N / (10 ^ 10 * C) ≤ qM (lt3WQ s dnEps lt3γE5 n w) ∧
      7 ≤ (lt3WQ s dnEps lt3γE5 n w).card ∧
      qM (lt3WQ s dnEps lt3γE5 n w) * qM (lt3WQ s dnEps lt3γE5 n w) ≤ 2 * (lt3WF s dnEps lt3γE5 n w).card := by
  classical
  have hC1 : 1 ≤ C := le_trans (Nat.one_le_pow _ _ (by positivity)) hC
  have hN' : 10 ^ 12 ≤ N := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hN
  obtain ⟨hg0, hgW⟩ := hg
  obtain ⟨hTle, -, hQ⟩ := lt3_good_QE5 s (by omega) hg0 hGU
  have hF := lt3W_F_card s dnEps lt3γE5 n w hTle
  set Q := lt3Q s dnEps lt3γE5 w
  set Q' := lt3WQ s dnEps lt3γE5 n w
  obtain ⟨hB, -, -, -⟩ := lt3_good_sizes s dnEps lt3γE5 lt3γE5_lt (le_refl 14) hg0 hTle
  have hQ3 : 3 * (N / 10 ^ 10) ≤ Q.card := by omega
  have hQQ' : Q.card ≤ C * Q'.card := by
    refine (lt3WQ_card s dnEps lt3γE5 n w).trans (Nat.mul_le_mul_right _ ?_)
    exact (Nat.pow_le_pow_right (by positivity) hB).trans hC
  set a := N / (10 ^ 10 * C) with ha_def
  have haC : C * a ≤ N / 10 ^ 10 := by
    rw [ha_def, ← Nat.div_div_eq_div_mul]; exact Nat.mul_div_le _ _
  have h3a : 3 * a ≤ Q'.card := by
    have : C * (3 * a) ≤ C * Q'.card := by
      calc C * (3 * a) = 3 * (C * a) := by ring
        _ ≤ 3 * (N / 10 ^ 10) := Nat.mul_le_mul_left _ haC
        _ ≤ Q.card := hQ3
        _ ≤ C * Q'.card := hQQ'
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hm : a ≤ qM Q' := by unfold qM; omega
  have ha100 : 100 ≤ a := by
    rw [ha_def, Nat.le_div_iff_mul_le (by positivity)]; omega
  have h7 : 7 ≤ Q'.card := by omega
  refine ⟨hm, h7, ?_⟩
  have hbad : ((qFam Q').filter fun S => ∃ r ∈ lt3Base s w, ∃ R ⊆ S, 2 ≤ R.card ∧
      ¬ stRobust N (N / 20) (w (flipS r R))).card < N * N / (10 ^ 21 * C * C) := by
    by_contra hc; exact hgW ⟨h7, by omega, not_lt.1 hc⟩
  have hm3 : 3 ≤ qM Q' := by omega
  rw [qFam_card hm3] at hF
  -- `N²/(10^21 C²) ≤ a²/2`
  have hNa : N < 10 ^ 10 * C * (a + 1) := by
    have := Nat.lt_div_mul_add (a := N) (b := 10 ^ 10 * C) (by positivity)
    rw [← ha_def] at this; nlinarith
  have hM : N * N / (10 ^ 21 * C * C) ≤ a * a / 2 := by
    have h0 : (10 ^ 10 * (a + 1)) * (10 ^ 10 * (a + 1)) ≤ 10 ^ 21 * (a * a / 2) := by
      have : 4 * (a + 1) * (a + 1) ≤ 7 * (a * a) := by nlinarith
      have h3 : a * a ≤ 2 * (a * a / 2) + 1 := by omega
      nlinarith
    have h1 : N * N ≤ (10 ^ 10 * C * (a + 1)) * (10 ^ 10 * C * (a + 1)) := Nat.mul_le_mul hNa.le hNa.le
    have h2 : (10 ^ 10 * C * (a + 1)) * (10 ^ 10 * C * (a + 1)) ≤ 10 ^ 21 * C * C * (a * a / 2) := by
      calc (10 ^ 10 * C * (a + 1)) * (10 ^ 10 * C * (a + 1))
          = (C * C) * ((10 ^ 10 * (a + 1)) * (10 ^ 10 * (a + 1))) := by ring
        _ ≤ (C * C) * (10 ^ 21 * (a * a / 2)) := Nat.mul_le_mul_left _ h0
        _ = 10 ^ 21 * C * C * (a * a / 2) := by ring
    exact Nat.div_le_of_le_mul (h1.trans h2)
  have hmm : a * a ≤ qM Q' * qM Q' := Nat.mul_le_mul hm hm
  omega

/-- For light `s` (`s ∉ lt3H w`) the special-current-row case is excluded. -/
lemma lt3_not_SpC_of_light {s : State N} {w : Param N} (hs : s ∉ lt3H w) : ¬ lt3SpC s w :=
  fun h => hs (mem_insert_of_mem h.1)

/-- For light `s`, `Top` is the global `Top` at `ε`. -/
lemma lt3Top_light {s : State N} {w : Param N} (hs : s ∉ lt3H w) (ε : ℝ) : lt3Top s w ε = lt3TopG w ε := by
  classical
  unfold lt3Top; rw [if_neg (lt3_not_SpC_of_light hs)]

/-- **`lt3W_good_FE5` for light `s`** (no `Top'` hypothesis), at the constants `n_b = lt3nbE5`, `C = lt3CnE5`. -/
theorem lt3W_good_F_lightE5 (s : State N) {w : Param N} (hs : s ∉ lt3H w) (hN : 10 ^ 12 * lt3CnE5 ≤ N)
    (hg : lt3WGood s dnEps lt3γE5 lt3nbE5 (N / 20) (N / 3000000) 14
      (N * N / (10 ^ 21 * lt3CnE5 * lt3CnE5)) w) :
    N / (10 ^ 10 * lt3CnE5) ≤ qM (lt3WQ s dnEps lt3γE5 lt3nbE5 w) ∧
      7 ≤ (lt3WQ s dnEps lt3γE5 lt3nbE5 w).card ∧
      qM (lt3WQ s dnEps lt3γE5 lt3nbE5 w) * qM (lt3WQ s dnEps lt3γE5 lt3nbE5 w) ≤
        2 * (lt3WF s dnEps lt3γE5 lt3nbE5 w).card :=
  lt3W_good_FE5 s lt3nbE5 lt3CnE5_ge hN hg fun h => absurd h (lt3_not_SpC_of_light hs)

/-- **From the member count to the adverse-count hypotheses**: `m ≥ N/(10^{10} C)` and `N ≥ 7 · 10^{10} C` give
`7 ≤ m` and `N ≤ D0 m`. -/
lemma lt3_ND0E5 {m : ℕ} (hN7 : 7 * (10 ^ 10 * lt3CnE5) ≤ N) (hm : N / (10 ^ 10 * lt3CnE5) ≤ m) :
    7 ≤ m ∧ N ≤ lt3D0E5 * m := by
  set K := 10 ^ 10 * lt3CnE5 with hK
  have hK0 : 0 < K := by have := lt3CnE5_pos; positivity
  have h7K : 7 ≤ N / K := by rw [Nat.le_div_iff_mul_le hK0]; linarith
  have hm7 : 7 ≤ m := h7K.trans hm
  refine ⟨hm7, ?_⟩
  have hlt := Nat.lt_div_mul_add (a := N) hK0
  have h1 : N / K * K ≤ m * K := Nat.mul_le_mul_right K hm
  have h2 : K ≤ m * K := Nat.le_mul_of_pos_left K (by omega)
  have e : lt3D0E5 * m = 2 * (m * K) := by simp only [lt3D0E5, hK]; ring
  rw [e]; omega

/-- **Few adverse members at the `ε = 10⁻⁵` constants** (`lt3_adv_ev` at `D0 = lt3D0E5`, `κ = lt3κE5`). -/
theorem lt3_adv_evE5 :
    ∀ᶠ N : ℕ in atTop, ∀ (s : State N) (ε γ : ℝ) (n : ℕ),
      cubeM N {w | (lt2Sp w).card < 12 ∧ 7 ≤ qM (lt3WQ s ε γ n w) ∧ N ≤ lt3D0E5 * qM (lt3WQ s ε γ n w) ∧
        qM (lt3WQ s ε γ n w) * qM (lt3WQ s ε γ n w) < 4 * (lt3Adv s ε γ n lt3κE5 w).card} ≤
      ENNReal.ofReal (Real.exp (-(2 * N))) :=
  lt3_adv_ev lt3D0E5_pos lt3κE5_ge lt3κE5_sq

end Census
end IIT
