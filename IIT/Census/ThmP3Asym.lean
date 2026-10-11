/-
Census: asymptotics for the second moment method for triples.

The level is `y_N = √(κ log N)` with `κ = 588/715 = 6 (1 - 1/50) / 7.15`.
* `tp_ev_sqrt_le`, `tp_tendsto_exp`: `β √L + γ ≤ α L` eventually and `exp(-α L + β √L) → 0` for
  `L = log N`, `α > 0`;
* `tp_ev_Glo`: the Gaussian probability of the ball of the first moment is at least `N^{-149/50}`;
* `tp_tendsto_b1`, `tp_tendsto_b2`: the joint half-space bounds for two triples sharing one or two
  units are `o(N^{-124/25})` and `o(N^{-99/25})`;
* `tp_ev_phi`: `σ_N (y_N - e_N) / (8 a₃ ln 2) ≥ 0.31 √(log N) σ_N` eventually.
-/
import IIT.Census.ThmP3Prob

namespace IIT
namespace Census

open MeasureTheory Filter Topology

noncomputable section

lemma tp_tendsto_log : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `β √L + γ ≤ α L` for large `L = log N`. -/
lemma tp_ev_sqrt_le {α : ℝ} (hα : 0 < α) (β γ : ℝ) :
    ∀ᶠ N : ℕ in atTop, β * Real.sqrt (Real.log N) + γ ≤ α * Real.log N := by
  set M := (|β| + |γ| + 1) / α + 1 with hM
  have hM0 : 0 ≤ (|β| + |γ| + 1) / α := by positivity
  have hM1 : 1 ≤ M := by rw [hM]; linarith
  filter_upwards [tp_tendsto_log.eventually_ge_atTop (M ^ 2)] with N hN
  set L := Real.log N
  have hL0 : 0 ≤ L := le_trans (by positivity) hN
  set x := Real.sqrt L
  have hx : M ≤ x := by
    rw [← Real.sqrt_sq (by linarith : 0 ≤ M)]; exact Real.sqrt_le_sqrt hN
  have hxx : x ^ 2 = L := Real.sq_sqrt hL0
  have h1 : |β| + |γ| + 1 ≤ α * x := by
    have : (|β| + |γ| + 1) / α ≤ x := by linarith
    rwa [div_le_iff₀ hα, mul_comm] at this
  have hx1 : 1 ≤ x := le_trans hM1 hx
  rw [← hxx]
  have h2 : (|β| + |γ| + 1) * x ≤ α * x * x := mul_le_mul_of_nonneg_right h1 (by linarith)
  have hb : β * x ≤ |β| * x := mul_le_mul_of_nonneg_right (le_abs_self β) (by linarith)
  have hg : γ ≤ |γ| * x := by nlinarith [le_abs_self γ, abs_nonneg γ]
  nlinarith

/-- `exp(-α L + β √L) → 0` for `α > 0`. -/
lemma tp_tendsto_exp {α : ℝ} (hα : 0 < α) (β : ℝ) :
    Tendsto (fun N : ℕ => Real.exp (-(α * Real.log N) + β * Real.sqrt (Real.log N))) atTop
      (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => -(α / 2) * Real.log N) atTop atBot :=
    tp_tendsto_log.const_mul_atTop_of_neg (by linarith)
  have h2 : Tendsto (fun N : ℕ => Real.exp (-(α / 2) * Real.log N)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h1
  refine squeeze_zero' (Eventually.of_forall fun N => (Real.exp_pos _).le) ?_ h2
  filter_upwards [tp_ev_sqrt_le (α := α / 2) (by linarith) β 0] with N hN
  exact Real.exp_le_exp.2 (by linarith)

/-! ### The level -/

/-- `κ = 588/715`. -/
def tp_kap : ℝ := 588 / 715

/-- The level `y_N = √(κ log N)`. -/
def tp_y (N : ℕ) : ℝ := Real.sqrt (tp_kap * Real.log N)

lemma tp_y_nonneg (N : ℕ) : 0 ≤ tp_y N := Real.sqrt_nonneg _

lemma tp_log_nonneg {N : ℕ} (hN : 1 ≤ N) : 0 ≤ Real.log N :=
  Real.log_nonneg (by exact_mod_cast hN)

lemma tp_y_sq {N : ℕ} (hN : 1 ≤ N) : tp_y N ^ 2 = tp_kap * Real.log N :=
  Real.sq_sqrt (by have := tp_log_nonneg hN; unfold tp_kap; positivity)

lemma tp_y_le {N : ℕ} (hN : 1 ≤ N) : tp_y N ≤ Real.sqrt (Real.log N) :=
  Real.sqrt_le_sqrt (by have := tp_log_nonneg hN; unfold tp_kap; nlinarith)

lemma tp_y_eq {N : ℕ} : tp_y N = Real.sqrt tp_kap * Real.sqrt (Real.log N) :=
  Real.sqrt_mul (by unfold tp_kap; norm_num) _

lemma tp_ev_y_ge (C : ℝ) : ∀ᶠ N : ℕ in atTop, C ≤ tp_y N := by
  filter_upwards [tp_tendsto_log.eventually_ge_atTop (C ^ 2 / tp_kap)] with N hN
  unfold tp_y
  calc C ≤ |C| := le_abs_self C
    _ = Real.sqrt (C ^ 2) := (Real.sqrt_sq_eq_abs C).symm
    _ ≤ Real.sqrt (tp_kap * Real.log N) := by
        apply Real.sqrt_le_sqrt
        rw [div_le_iff₀ (by unfold tp_kap; norm_num)] at hN
        linarith

lemma tp_eps_le_one (N : ℕ) : ps_eps N ≤ 1 := by
  unfold ps_eps; exact pow_le_one₀ (by norm_num) (by norm_num)

/-! ### The joint bounds -/

/-- The exponential bound for two triples sharing one unit is `o(N^{-124/25})`. -/
lemma tp_tendsto_b1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (124 / 25 : ℝ) *
    Real.exp (-(13 * (tp_y N - 3 * (1 + ps_eps N)) ^ 2) / 2)) atTop (𝓝 0) := by
  have hα : (0 : ℝ) < 13 * tp_kap / 2 - 124 / 25 := by unfold tp_kap; norm_num
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ (tp_tendsto_exp hα 78)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL := tp_log_nonneg hN
  have hy2 := tp_y_sq hN
  have hyL := tp_y_le hN
  have hy0 := tp_y_nonneg N
  have hε := ps_eps_pos N
  have hε1 := tp_eps_le_one N
  set c := 3 * (1 + ps_eps N)
  have hc6 : c ≤ 6 := by simp only [c]; linarith
  have hc0 : 0 ≤ c := by simp only [c]; linarith
  rw [Real.rpow_def_of_pos hN0, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hsq : tp_y N ^ 2 - 2 * c * tp_y N ≤ (tp_y N - c) ^ 2 := by nlinarith
  have hcy : c * tp_y N ≤ 6 * Real.sqrt (Real.log N) := by
    have := Real.sqrt_nonneg (Real.log N)
    nlinarith
  nlinarith

/-- The exponential bound for two triples sharing two units is `o(N^{-99/25})`. -/
lemma tp_tendsto_b2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (99 / 25 : ℝ) *
    Real.exp (-(11 * (tp_y N - 3 * (1 + ps_eps N)) ^ 2) / 2)) atTop (𝓝 0) := by
  have hα : (0 : ℝ) < 11 * tp_kap / 2 - 99 / 25 := by unfold tp_kap; norm_num
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ (tp_tendsto_exp hα 66)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL := tp_log_nonneg hN
  have hy2 := tp_y_sq hN
  have hyL := tp_y_le hN
  have hy0 := tp_y_nonneg N
  have hε := ps_eps_pos N
  have hε1 := tp_eps_le_one N
  set c := 3 * (1 + ps_eps N)
  have hc6 : c ≤ 6 := by simp only [c]; linarith
  have hc0 : 0 ≤ c := by simp only [c]; linarith
  rw [Real.rpow_def_of_pos hN0, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hsq : tp_y N ^ 2 - 2 * c * tp_y N ≤ (tp_y N - c) ^ 2 := by nlinarith
  have hcy : c * tp_y N ≤ 6 * Real.sqrt (Real.log N) := by
    have := Real.sqrt_nonneg (Real.log N)
    nlinarith
  nlinarith

/-! ### Exponentially small terms -/

lemma tp_tendsto_tau6 : Tendsto (fun N : ℕ => (N : ℝ) ^ 6 * (tauN N / sigN N)) atTop (𝓝 0) := by
  simp_rw [ps_tau_sig]
  exact tp_tendsto_pow_mul_pow 6 ps_r_nonneg ps_r_lt _

lemma tp_tendsto_eps6 : Tendsto (fun N : ℕ => (N : ℝ) ^ 6 * ps_eps N) atTop (𝓝 0) :=
  (tp_tendsto_pow_mul_pow 6 (r := 99 / 100) (by norm_num) (by norm_num) 1).congr fun N => by
    simp [ps_eps]

lemma tp_tendsto_fg2_6 : Tendsto (fun N : ℕ => (N : ℝ) ^ 6 * fg2 N) atTop (𝓝 0) := by
  have hr : Real.exp (2 / 3) / 2 < 1 := by
    rw [div_lt_one (by norm_num)]; exact exp_two_thirds_lt_two
  have h := tp_tendsto_pow_mul_pow 7 (r := Real.exp (2 / 3) / 2) (by positivity) hr 4
  refine h.congr fun N => ?_
  rw [fg2]; ring

lemma tp_tendsto_small (f : ℕ → ℝ) (hf : Tendsto (fun N : ℕ => (N : ℝ) ^ 6 * f N) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  have h1 : ∀ᶠ N : ℕ in atTop, |f N| ≤ |(N : ℝ) ^ 6 * f N| := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [abs_mul]
    have : (1 : ℝ) ≤ |(N : ℝ) ^ 6| := by
      rw [abs_of_nonneg (by positivity)]; exact one_le_pow₀ (by exact_mod_cast hN)
    nlinarith [abs_nonneg (f N)]
  rw [tendsto_zero_iff_abs_tendsto_zero] at hf ⊢
  exact squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) h1 hf

/-- The radius of the first moment is at least `1/2` eventually. -/
lemma tp_ev_radius : ∀ᶠ N : ℕ in atTop, 16 * tauN N / sigN N + ps_eps N ≤ 1 / 2 := by
  have h1 := tp_tendsto_small _ tp_tendsto_tau6
  have h2 := tp_tendsto_small _ tp_tendsto_eps6
  have h := (h1.const_mul 16).add h2
  simp only [mul_zero, add_zero] at h
  filter_upwards [h.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with N hN
  have e : 16 * tauN N / sigN N = 16 * (tauN N / sigN N) := by ring
  rw [e]; exact hN

/-! ### The first moment -/

/-- **The Gaussian ball of the first moment** has probability at least `N^{-149/50}`. -/
lemma tp_ev_Glo : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(149 / 50 : ℝ)) ≤
    (tp_G1 3).real (tp_ball (tp_cen (tp_y N)) (1 - 16 * tauN N / sigN N - ps_eps N)) := by
  set ρ := 1 / (2 * tp_R 3) with hρ
  have hR := tp_R_pos 3
  have hρ0 : 0 < ρ := by positivity
  set c := ρ * Real.sqrt 33 with hc
  have hc0 : 0 ≤ c := by positivity
  set K0 := (2 * ρ / Real.sqrt (2 * Real.pi)) ^ 33 with hK0
  have hK0p : 0 < K0 := by have := Real.pi_pos; positivity
  filter_upwards [eventually_ge_atTop 1, tp_ev_radius,
    tp_ev_sqrt_le (α := 1 / 25) (by norm_num) (3 * c) (c ^ 2 / 2 - Real.log K0)]
    with N hN hrad hsq
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL := tp_log_nonneg hN
  have hy2 := tp_y_sq hN
  have hyL := tp_y_le hN
  have hy0 := tp_y_nonneg N
  have hball : tp_ball (tp_cen (tp_y N)) (ρ * tp_R 3) ⊆
      tp_ball (tp_cen (tp_y N)) (1 - 16 * tauN N / sigN N - ps_eps N) := by
    intro x hx p
    have := hx p
    have e : ρ * tp_R 3 = 1 / 2 := by rw [hρ]; field_simp
    rw [e] at this
    linarith
  refine le_trans ?_ (measureReal_mono hball)
  refine le_trans ?_ (tp_G1_ball_ge hy0 hρ0)
  rw [Real.rpow_def_of_pos hN0, ← hK0, ← hc, ← Real.exp_log hK0p, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h715 : Real.sqrt (715 / 100) ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h715' : 0 ≤ Real.sqrt (715 / 100) := Real.sqrt_nonneg _
  have hsq715 : Real.sqrt (715 / 100) ^ 2 = 715 / 100 := Real.sq_sqrt (by norm_num)
  have hsL := Real.sqrt_nonneg (Real.log N)
  have hk : tp_kap * (715 / 100) = 147 / 25 := by unfold tp_kap; norm_num
  have hexp : (tp_y N * Real.sqrt (715 / 100) + c) ^ 2 ≤
      147 / 25 * Real.log N + 6 * c * Real.sqrt (Real.log N) + c ^ 2 := by
    have e1 : (tp_y N * Real.sqrt (715 / 100)) ^ 2 = 147 / 25 * Real.log N := by
      rw [mul_pow, hy2, hsq715, ← hk]; ring
    have e2 : tp_y N * Real.sqrt (715 / 100) ≤ 3 * Real.sqrt (Real.log N) := by
      nlinarith
    nlinarith
  have hsq' : 3 * c * Real.sqrt (Real.log N) + (c ^ 2 / 2 - Real.log K0) ≤ 1 / 25 * Real.log N :=
    hsq
  nlinarith

/-! ### The final constant -/

lemma tp_sqrt_kap : 9068 / 10000 ≤ Real.sqrt tp_kap := by
  rw [Real.le_sqrt (by norm_num) (by unfold tp_kap; norm_num)]
  unfold tp_kap; norm_num

/-- **The level exceeds `0.31 √(log N) σ_N`.** -/
lemma tp_ev_phi : ∀ᶠ N : ℕ in atTop, (31 / 100) * Real.sqrt (Real.log N) * sigN N ≤
    sigN N * (tp_y N - 6 * tp_eta N ^ 2 / ((tl_aTrip - tp_eta N) * sigN N)) /
      (8 * tl_aTrip * Real.log 2) := by
  filter_upwards [eventually_ge_atTop 1, tp_eta_le,
    ev_pow_mul_sigN 1 (C := 150) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 100),
    ev_pow_mul_sigN 2 (C := 270000) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 100),
    tp_tendsto_log.eventually_ge_atTop 1] with N hN hηle hs1 hs2 hL1
  have hσ := sigN_pos N
  have hη0 := tp_eta_nonneg hN
  set η := tp_eta N
  have hη1 : η ≤ 1 / 100 := by rw [pow_one] at hs1; linarith
  have haT : tl_aTrip = 25 / 48 := by unfold tl_aTrip; norm_num
  rw [haT]
  have hA : (1 : ℝ) / 2 ≤ 25 / 48 - η := by linarith
  have he : 6 * η ^ 2 / ((25 / 48 - η) * sigN N) ≤ 1 / 100 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : η ^ 2 ≤ (150 * N * sigN N) ^ 2 := pow_le_pow_left₀ hη0 hηle 2
    have h2 : (150 * (N : ℝ) * sigN N) ^ 2 = 22500 * (N : ℝ) ^ 2 * sigN N * sigN N := by ring
    have h3 : 270000 * (N : ℝ) ^ 2 * sigN N * sigN N ≤ 1 / 100 * sigN N := by
      have := mul_le_mul_of_nonneg_right hs2 hσ.le
      linarith
    nlinarith
  have hsL : 1 ≤ Real.sqrt (Real.log N) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hy : 9068 / 10000 * Real.sqrt (Real.log N) ≤ tp_y N := by
    rw [tp_y_eq]
    exact mul_le_mul_of_nonneg_right tp_sqrt_kap (Real.sqrt_nonneg _)
  have hlog := Real.log_two_lt_d9
  have hlog0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [le_div_iff₀ (by positivity)]
  have key : 31 / 100 * (8 * (25 / 48) * Real.log 2) ≤ 8954 / 10000 := by nlinarith
  have hsL0 := Real.sqrt_nonneg (Real.log N)
  nlinarith [mul_le_mul_of_nonneg_left key (mul_nonneg hsL0 hσ.le)]

end

end Census
end IIT
