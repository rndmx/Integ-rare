/-
Census, Theorem E: the parameters of the upper bound and their asymptotics.

With `σ = σ_N`, the level `A = a_k`, the band `η_N = N σ_N`, the upper reduction of
`UpperReduce` produces the shift `e_N = 4kη²/((A-η)σ)`, the factor `ρ_N = ((A+η)/(A-η))^k`, the
effect threshold `δ_N = ρ_N 2^{-k} · 2kη/((A-η) ln 2)` and, for `φ_s > c √(ln N) σ_N`, the level
`y_N = c √(ln N) 2^k a_k ln 2 / ρ_N - e_N` of the certificate form.  This file proves
* `N^n σ_N → 0`, `N^n e_N → 0`, `ρ_N → 1` and eventually `3 η_N ≤ a_k`;
* eventually `y_N ≥ λ √(ln N) + 1` for every `λ < c 2^k a_k ln 2` (`te_ev_y`);
* eventually `δ_N ≤ a_N^k b_N` with `a_N = (1 - 1/(20k))^N`, `b_N = (9/10)^N` (`te_ev_del`);
* `N^k · N^{-K} → 0` for `K > k` in the form used by the half-space bounds.
-/
import IIT.Census.ThmEField
import IIT.Census.BigPhiArith

namespace IIT
namespace Census

open Filter Topology

noncomputable section

/-! ### Parameters -/

/-- The band `η_N = N σ_N`. -/
def te_eta (N : ℕ) : ℝ := N * sigN N

/-- The shift `e_N`. -/
def te_e (k N : ℕ) : ℝ := ur_err k (bg_ak k) (te_eta N) (sigN N)

/-- The band factor `ρ_N`. -/
def te_rho (k N : ℕ) : ℝ := ur_rho k (bg_ak k) (te_eta N)

/-- The effect threshold `δ_N`. -/
def te_del (k N : ℕ) : ℝ :=
  te_rho k N / 2 ^ k * (2 * k * te_eta N / ((bg_ak k - te_eta N) * Real.log 2))

/-- The constant `κ_k = 2^k a_k ln 2`. -/
def te_kap (k : ℕ) : ℝ := 2 ^ k * bg_ak k * Real.log 2

/-- The level `y_N` of the certificate form. -/
def te_y (k : ℕ) (c : ℝ) (N : ℕ) : ℝ :=
  c * Real.sqrt (Real.log N) * te_kap k / te_rho k N - te_e k N

/-- The smoothing width, re-exported. -/
lemma te_eps_pos (N : ℕ) : 0 < ps_eps N := ps_eps_pos N

/-! ### Elementary bounds -/

lemma te_ak_ge (k : ℕ) : 1 / 2 ≤ bg_ak k := by
  unfold bg_ak; have : (0 : ℝ) ≤ ((2 : ℝ) ^ k)⁻¹ := by positivity
  linarith

lemma te_ak_le (k : ℕ) : bg_ak k ≤ 1 := by
  unfold bg_ak
  have : ((2 : ℝ) ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  linarith

lemma te_kap_pos (k : ℕ) : 0 < te_kap k := by
  unfold te_kap
  have := te_ak_ge k
  have := Real.log_pos one_lt_two
  positivity

lemma te_sig_le (N : ℕ) : sigN N ≤ (41 / 50 : ℝ) ^ N := by
  unfold sigN
  rw [show (41 / 50 : ℝ) ^ N = Real.sqrt (((41 / 50 : ℝ) ^ N) ^ 2) by
    rw [Real.sqrt_sq (by positivity)]]
  refine Real.sqrt_le_sqrt ?_
  rw [← pow_mul, mul_comm, pow_mul]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) N

lemma te_eta_nonneg (N : ℕ) : 0 ≤ te_eta N := by
  unfold te_eta; have := sigN_pos N; positivity

/-- `N^n σ_N → 0`. -/
lemma te_tendsto_sig (n : ℕ) : Tendsto (fun N : ℕ => (N : ℝ) ^ n * sigN N) atTop (𝓝 0) := by
  have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one n
    (show |(41 / 50 : ℝ)| < 1 by rw [abs_of_pos (by norm_num)]; norm_num)
  refine squeeze_zero (fun N => by have := sigN_pos N; positivity) (fun N => ?_) h
  exact mul_le_mul_of_nonneg_left (te_sig_le N) (by positivity)

lemma te_tendsto_eta : Tendsto te_eta atTop (𝓝 0) := by
  have h := te_tendsto_sig 1
  show Tendsto (fun N : ℕ => (N : ℝ) * sigN N) atTop (𝓝 0)
  simpa using h

lemma te_ev_eta_small {ε : ℝ} (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, te_eta N ≤ ε :=
  (tendsto_order.1 te_tendsto_eta).2 ε hε |>.mono fun _ h => h.le

lemma te_ev_three_eta (k : ℕ) : ∀ᶠ N : ℕ in atTop, 3 * te_eta N ≤ bg_ak k := by
  filter_upwards [te_ev_eta_small (show (0 : ℝ) < 1 / 6 by norm_num)] with N hN
  have := te_ak_ge k
  linarith

/-- `N^n e_N → 0`. -/
lemma te_tendsto_e (k n : ℕ) : Tendsto (fun N : ℕ => (N : ℝ) ^ n * te_e k N) atTop (𝓝 0) := by
  have h := (te_tendsto_sig (n + 2)).const_mul (16 * (k : ℝ))
  rw [mul_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · filter_upwards [te_ev_eta_small (show (0 : ℝ) < 1 / 4 by norm_num)] with N hN
    have hA := te_ak_ge k
    have hσ := sigN_pos N
    unfold te_e ur_err
    have : 0 < bg_ak k - te_eta N := by linarith
    positivity
  · filter_upwards [te_ev_eta_small (show (0 : ℝ) < 1 / 4 by norm_num)] with N hN
    have hA := te_ak_ge k
    have hσ := sigN_pos N
    have hAη : 1 / 4 ≤ bg_ak k - te_eta N := by linarith
    unfold te_e ur_err
    rw [te_eta]
    have hpos : 0 < (bg_ak k - N * sigN N) * sigN N := by
      have : 0 < bg_ak k - N * sigN N := by rw [te_eta] at hAη; linarith
      positivity
    rw [mul_div_assoc', div_le_iff₀ hpos]
    have hA' : 1 / 4 ≤ bg_ak k - N * sigN N := by rw [te_eta] at hAη; exact hAη
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hN : (0 : ℝ) ≤ (N : ℝ) ^ n := by positivity
    have key : (N : ℝ) ^ n * (4 * k * (N * sigN N) ^ 2) ≤
        16 * k * ((N : ℝ) ^ (n + 2) * sigN N) * ((1 / 4) * sigN N) := by
      rw [pow_add]; ring_nf; nlinarith [sq_nonneg (sigN N), hσ]
    calc (N : ℝ) ^ n * (4 * k * (N * sigN N) ^ 2)
        ≤ 16 * k * ((N : ℝ) ^ (n + 2) * sigN N) * ((1 / 4) * sigN N) := key
      _ ≤ 16 * k * ((N : ℝ) ^ (n + 2) * sigN N) * ((bg_ak k - N * sigN N) * sigN N) := by
          gcongr

lemma te_e_nonneg (k : ℕ) : ∀ᶠ N : ℕ in atTop, 0 ≤ te_e k N := by
  filter_upwards [te_ev_eta_small (show (0 : ℝ) < 1 / 4 by norm_num)] with N hN
  have hA := te_ak_ge k
  have hσ := sigN_pos N
  unfold te_e ur_err
  have : 0 < bg_ak k - te_eta N := by linarith
  positivity

lemma te_tendsto_rho (k : ℕ) : Tendsto (te_rho k) atTop (𝓝 1) := by
  have hA := te_ak_ge k
  have h1 : Tendsto (fun N => (bg_ak k + te_eta N) / (bg_ak k - te_eta N)) atTop
      (𝓝 ((bg_ak k + 0) / (bg_ak k - 0))) :=
    (tendsto_const_nhds.add te_tendsto_eta).div (tendsto_const_nhds.sub te_tendsto_eta)
      (by simp; linarith)
  rw [add_zero, sub_zero, div_self (by linarith)] at h1
  have h2 := h1.pow k
  rw [one_pow] at h2
  exact h2

lemma te_rho_pos (k : ℕ) : ∀ᶠ N : ℕ in atTop, 0 < te_rho k N := by
  filter_upwards [te_ev_eta_small (show (0 : ℝ) < 1 / 4 by norm_num)] with N hN
  have hA := te_ak_ge k
  have := te_eta_nonneg N
  unfold te_rho ur_rho
  have : 0 < bg_ak k - te_eta N := by linarith
  positivity

/-- **The level grows**: eventually `y_N ≥ λ √(ln N) + 1` for `λ < c κ_k`. -/
lemma te_ev_y (k : ℕ) {c l : ℝ} (hl : l < c * te_kap k) :
    ∀ᶠ N : ℕ in atTop, l * Real.sqrt (Real.log N) + 1 ≤ te_y k c N := by
  set m := (l + c * te_kap k) / 2 with hm
  have hml : l < m := by rw [hm]; linarith
  have hmc : m < c * te_kap k := by rw [hm]; linarith
  -- eventually `c κ / ρ_N ≥ m`
  have hq : Tendsto (fun N => c * te_kap k / te_rho k N) atTop (𝓝 (c * te_kap k / 1)) :=
    tendsto_const_nhds.div (te_tendsto_rho k) one_ne_zero
  rw [div_one] at hq
  have hev1 : ∀ᶠ N : ℕ in atTop, m ≤ c * te_kap k / te_rho k N :=
    ((tendsto_order.1 hq).1 m hmc).mono fun _ h => h.le
  have hev2 : ∀ᶠ N : ℕ in atTop, te_e k N ≤ 1 := by
    have h := te_tendsto_e k 0
    simp only [pow_zero, one_mul] at h
    exact ((tendsto_order.1 h).2 1 one_pos).mono fun _ h => h.le
  have hsq : Tendsto (fun N : ℕ => Real.sqrt (Real.log N)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hev3 : ∀ᶠ N : ℕ in atTop, 2 / (m - l) ≤ Real.sqrt (Real.log N) :=
    hsq.eventually_ge_atTop _
  filter_upwards [hev1, hev2, hev3] with N h1 h2 h3
  have hs0 : 0 ≤ Real.sqrt (Real.log N) := Real.sqrt_nonneg _
  have hml' : 0 < m - l := by linarith
  have h3' : 2 ≤ (m - l) * Real.sqrt (Real.log N) := by
    rw [div_le_iff₀ hml'] at h3; linarith
  unfold te_y
  have : c * Real.sqrt (Real.log N) * te_kap k / te_rho k N =
      (c * te_kap k / te_rho k N) * Real.sqrt (Real.log N) := by ring
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_right h1 hs0]

/-- **The effect threshold is small**: eventually `δ_N ≤ a_N^k b_N`. -/
lemma te_ev_del (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ N : ℕ in atTop, te_del k N ≤
      ((1 - 1 / (20 * k : ℝ)) ^ N) ^ k * (9 / 10 : ℝ) ^ N := by
  have hA := te_ak_ge k
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  -- Bernoulli: `(1 - 1/(20k))^k ≥ 19/20`
  have hB : (19 / 20 : ℝ) ≤ (1 - 1 / (20 * k : ℝ)) ^ k := by
    have h := one_add_mul_le_pow (a := -(1 / (20 * k : ℝ))) (by
      have : 1 / (20 * k : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      linarith) k
    have e : (1 : ℝ) + k * -(1 / (20 * k)) = 19 / 20 := by field_simp; ring
    rw [e, ← sub_eq_add_neg] at h
    exact h
  have hbase : (0 : ℝ) ≤ 1 - 1 / (20 * k : ℝ) := by
    have : 1 / (20 * k : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have hlow : ∀ N : ℕ, ((171 / 200 : ℝ)) ^ N ≤
      ((1 - 1 / (20 * k : ℝ)) ^ N) ^ k * (9 / 10 : ℝ) ^ N := by
    intro N
    rw [← pow_mul, mul_comm N k, pow_mul]
    calc (171 / 200 : ℝ) ^ N = (19 / 20 : ℝ) ^ N * (9 / 10 : ℝ) ^ N := by
          rw [← mul_pow]; norm_num
      _ ≤ ((1 - 1 / (20 * k : ℝ)) ^ k) ^ N * (9 / 10 : ℝ) ^ N := by
          gcongr
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hrho : ∀ᶠ N : ℕ in atTop, te_rho k N ≤ 2 :=
    ((tendsto_order.1 (te_tendsto_rho k)).2 2 (by norm_num)).mono fun _ h => h.le
  have hgeo := ev_poly_geom 1 (r := (164 / 171 : ℝ)) (by norm_num) (by norm_num) (32 * k)
    one_pos
  filter_upwards [hrho, te_rho_pos k, te_ev_eta_small (show (0 : ℝ) < 1 / 4 by norm_num),
    hgeo] with N hr hr0 hη hg
  refine le_trans ?_ (hlow N)
  have hσ := sigN_pos N
  have hη0 := te_eta_nonneg N
  have hAη : 1 / 4 ≤ bg_ak k - te_eta N := by linarith
  unfold te_del
  have hden : 0 < (bg_ak k - te_eta N) * Real.log 2 := by positivity
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  -- `δ_N ≤ 32 k η_N`
  have hstep : te_rho k N / 2 ^ k * (2 * k * te_eta N / ((bg_ak k - te_eta N) * Real.log 2)) ≤
      32 * k * te_eta N := by
    have h1 : te_rho k N / 2 ^ k ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h2 : 2 * k * te_eta N / ((bg_ak k - te_eta N) * Real.log 2) ≤ 16 * k * te_eta N := by
      rw [div_le_iff₀ hden]
      have : (1 / 8 : ℝ) ≤ (bg_ak k - te_eta N) * Real.log 2 := by nlinarith
      have hkη : 0 ≤ (k : ℝ) * te_eta N := by positivity
      nlinarith
    calc te_rho k N / 2 ^ k * (2 * k * te_eta N / ((bg_ak k - te_eta N) * Real.log 2))
        ≤ 2 * (16 * k * te_eta N) := by
          apply mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ = 32 * k * te_eta N := by ring
  refine hstep.trans ?_
  have hsig := te_sig_le N
  have hsplit : (41 / 50 : ℝ) ^ N = (164 / 171 : ℝ) ^ N * (171 / 200 : ℝ) ^ N := by
    rw [← mul_pow]; norm_num
  unfold te_eta
  calc 32 * k * (N * sigN N) ≤ 32 * k * (N * (41 / 50 : ℝ) ^ N) := by gcongr
    _ = (32 * k * (N : ℝ) ^ 1 * (164 / 171 : ℝ) ^ N) * (171 / 200 : ℝ) ^ N := by
        rw [hsplit]; ring
    _ ≤ 1 * (171 / 200 : ℝ) ^ N := by gcongr
    _ = (171 / 200 : ℝ) ^ N := one_mul _

/-- `N^n q^N → 0` for `0 ≤ q < 1`. -/
lemma te_tendsto_geom (n : ℕ) {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) (C : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ n * (C * q ^ N)) atTop (𝓝 0) := by
  have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one n
    (by rwa [abs_of_nonneg h0])).const_mul C
  rw [mul_zero] at h
  exact h.congr fun N => by ring

/-- `N^n exp(-K ln N) → 0` for `n < K`. -/
lemma te_tendsto_exp_log (n : ℕ) {K : ℝ} (hK : n < K) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ n * Real.exp (-(K * Real.log N))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := Real.tendsto_exp_atBot.comp
    (Filter.Tendsto.const_mul_atTop_of_neg (sub_neg.2 hK) hlog |>.congr (fun _ => rfl))
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp_apply]
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hN0, ← Real.exp_add]
  congr 1
  ring

end

end Census
end IIT
