/-
Census: Theorem P3 for triples — the strong extreme-value lower bound.

With probability tending to one some 3-set `S` has `φ_s(S) ≥ 0.31 √(log N) σ_N`
(`tendsto_triple_lower`).  The level `y_N = √(κ log N)`, `κ = 588/715`, is the level of the
second moment method of `ThmP3Cheb`: the first moment grows like `N^{1/50}` (`tp_ev_Glo`), disjoint
pairs of triples are asymptotically independent (the slab bound `tp_ball_succ_le`), pairs sharing
one or two units are negligible (`tp_tendsto_b1`, `tp_tendsto_b2`), and on the event of a triple
the deterministic bound `tp_det` gives `φ_s(S) ≥ σ_N (y_N - e_N) / (8 a₃ ln 2)`, which exceeds
`0.31 √(log N) σ_N` (`tp_ev_phi`); the constant `(31/100) · 8 a₃ ln 2 < √κ` leaves the margin.
-/
import IIT.Census.ThmP3Cheb
import IIT.Census.BigPhiMain
import IIT.Census.UnivZero
import IIT.Census.SharpDev

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

noncomputable section

variable {N : ℕ}

/-- The constant of Theorem P3 for triples. -/
def tp_c3 : ℝ := 31 / 100

/-! ### Rpow bookkeeping -/

/-- The lower bound for the first moment. -/
def tp_ell (N : ℕ) : ℝ := (N : ℝ) ^ (-(149 / 50 : ℝ))

lemma tp_ell_pos (hN : 1 ≤ N) : 0 < tp_ell N :=
  Real.rpow_pos_of_pos (by exact_mod_cast hN) _

lemma tp_rpow_nat (_hN : 1 ≤ N) (k : ℕ) : (N : ℝ) ^ (k : ℝ) = (N : ℝ) ^ k := Real.rpow_natCast _ k

lemma tp_rpow_le6 (hN : 1 ≤ N) {p : ℝ} (hp : p ≤ 6) : (N : ℝ) ^ p ≤ (N : ℝ) ^ 6 := by
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [← tp_rpow_nat hN 6]
  exact Real.rpow_le_rpow_of_exponent_le h1 (by norm_num; linarith)

lemma tp_ell_M (hN : 1 ≤ N) : (N : ℝ) ^ 3 * tp_ell N = (N : ℝ) ^ (1 / 50 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [tp_ell, ← tp_rpow_nat hN 3, ← Real.rpow_add hN0]
  norm_num

lemma tp_ell_sq (hN : 1 ≤ N) : 1 / tp_ell N ^ 2 = (N : ℝ) ^ (149 / 25 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [tp_ell, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, one_div, ← Real.rpow_neg hN0.le]
  norm_num

lemma tp_rpow_sub (hN : 1 ≤ N) (p : ℝ) (k : ℕ) :
    (N : ℝ) ^ p / (N : ℝ) ^ k = (N : ℝ) ^ (p - k) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.rpow_sub hN0, Real.rpow_natCast]

/-! ### The asymptotic quantities -/

/-- The Gaussian probability of the ball of the first moment. -/
def tp_G (N : ℕ) : ℝ :=
  (tp_G1 3).real (tp_ball (tp_cen (tp_y N)) (1 - 16 * tauN N / sigN N - ps_eps N))

/-- The slab bound between the two balls. -/
def tp_D (N : ℕ) : ℝ :=
  24 * (2 * ((144 * tauN N / sigN N + 2 * ps_eps N) / Real.sqrt (2 * Real.pi * (2 * gg_c2 3))))

/-- The first-moment error. -/
def tp_u (N : ℕ) : ℝ := tp_pE * tp_err (tp_E2s 3) (tp_E3s 3) N + fg2 N

/-- The exponentially small part of the second-moment error. -/
def tp_V (N : ℕ) : ℝ :=
  tp_pE ^ 2 * (2 * tp_D N + tp_D N ^ 2 + tp_err (tp_E2j 3 0) (tp_E3j 3 0) N) + fg2 N

lemma tp_D_nonneg (N : ℕ) : 0 ≤ tp_D N := by
  have := tauN_pos N; have := sigN_pos N; have := ps_eps_pos N
  have := gg_c2_pos 3
  unfold tp_D; positivity

lemma tp_u_nonneg (N : ℕ) : 0 ≤ tp_u N := by
  have := tp_errs_nonneg N; have := ps_fg2_nonneg N; have := tp_pE_pos
  unfold tp_u; positivity

lemma tp_V_nonneg (N : ℕ) : 0 ≤ tp_V N := by
  have := tp_errj_nonneg 0 N; have := ps_fg2_nonneg N; have := tp_D_nonneg N
  unfold tp_V; positivity

/-- **Slab bound**: the larger ball exceeds the smaller one by at most `tp_D N`. -/
lemma tp_Gh_le (N : ℕ) (hr : 0 ≤ 1 - 16 * tauN N / sigN N - ps_eps N) :
    (tp_G1 3).real (tp_ball (tp_cen (tp_y N)) (1 + 128 * tauN N / sigN N + ps_eps N)) ≤
      tp_G N + tp_D N := by
  have hδ : 0 ≤ 144 * tauN N / sigN N + 2 * ps_eps N := by
    have := tauN_pos N; have := sigN_pos N; have := ps_eps_pos N; positivity
  have hc : ∀ p, tp_base 3 p = p → tp_cen (tp_y N) p = 0 := by
    intro p hp
    simp only [tp_cen, tp_Dz, tp_Dif, hp, sub_self, mul_zero]
  have h := tp_ball_succ_le (tp_DA (tp_base 3) (gg_A 3)) (by have := gg_c2_pos 3; positivity)
    (tp_G1_rows 3 hc) hr hδ
  have e : 1 - 16 * tauN N / sigN N - ps_eps N + (144 * tauN N / sigN N + 2 * ps_eps N) =
      1 + 128 * tauN N / sigN N + ps_eps N := by ring
  rw [e] at h
  have h24 : ((3 * 2 ^ 3 : ℕ) : ℝ) = 24 := by norm_num
  rw [h24] at h
  exact h

/-! ### The main estimate -/

/-- The final bound. -/
def tp_Tb (N : ℕ) : ℝ :=
  24 / tp_pE * (N : ℝ) ^ (-(1 / 50 : ℝ)) + 4 / tp_pE ^ 2 *
    ((N : ℝ) ^ 6 * (tp_V N + 2 * tp_u N) +
      36 * ((N : ℝ) ^ (124 / 25 : ℝ) *
          Real.exp (-(13 * (tp_y N - 3 * (1 + ps_eps N)) ^ 2) / 2) +
        (N : ℝ) ^ 6 * tp_err (tp_E2j 3 1) (tp_E3j 3 1) N) +
      108 * ((N : ℝ) ^ (99 / 25 : ℝ) *
          Real.exp (-(11 * (tp_y N - 3 * (1 + ps_eps N)) ^ 2) / 2) +
        (N : ℝ) ^ 6 * tp_err (tp_E2j 3 2) (tp_E3j 3 2) N))

lemma tp_tendsto_D6 : Tendsto (fun N : ℕ => (N : ℝ) ^ 6 * tp_D N) atTop (𝓝 0) := by
  set K := Real.sqrt (2 * Real.pi * (2 * gg_c2 3))
  have h := (tp_tendsto_tau6.const_mul (48 * 144 / K)).add (tp_tendsto_eps6.const_mul (48 * 2 / K))
  simp only [mul_zero, add_zero] at h
  refine h.congr fun N => ?_
  rw [tp_D]
  ring

lemma tp_tendsto_T : Tendsto tp_Tb atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 50 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 50)).comp tendsto_natCast_atTop_atTop
  have hD := tp_tendsto_D6
  have hDD : Tendsto (fun N : ℕ => (N : ℝ) ^ 6 * tp_D N ^ 2) atTop (𝓝 0) := by
    have := hD.mul (tp_tendsto_small _ hD)
    rw [mul_zero] at this
    exact this.congr fun N => by ring
  have hj0 := tp_tendsto_err (tp_E2j 3 0) (tp_E3j 3 0) 6
  have hs := tp_tendsto_err (tp_E2s 3) (tp_E3s 3) 6
  have hf := tp_tendsto_fg2_6
  have hVa : Tendsto (fun N : ℕ => (N : ℝ) ^ 6 * tp_V N) atTop (𝓝 0) := by
    have h := ((((hD.const_mul 2).add hDD).add hj0).const_mul (tp_pE ^ 2)).add hf
    simp only [mul_zero, add_zero] at h
    refine h.congr fun N => ?_
    rw [tp_V]; ring
  have hua : Tendsto (fun N : ℕ => (N : ℝ) ^ 6 * tp_u N) atTop (𝓝 0) := by
    have h := (hs.const_mul tp_pE).add hf
    simp only [mul_zero, add_zero] at h
    refine h.congr fun N => ?_
    rw [tp_u]; ring
  have hV : Tendsto (fun N : ℕ => (N : ℝ) ^ 6 * (tp_V N + 2 * tp_u N)) atTop (𝓝 0) := by
    have h := hVa.add (hua.const_mul 2)
    simp only [mul_zero, add_zero] at h
    exact h.congr fun N => by ring
  have hB1 := (tp_tendsto_b1.add (tp_tendsto_err (tp_E2j 3 1) (tp_E3j 3 1) 6)).const_mul 36
  have hB2 := (tp_tendsto_b2.add (tp_tendsto_err (tp_E2j 3 2) (tp_E3j 3 2) 6)).const_mul 108
  have hin := ((hV.add hB1).add hB2).const_mul (4 / tp_pE ^ 2)
  have h := (h1.const_mul (24 / tp_pE)).add hin
  simp only [mul_zero, add_zero] at h
  exact h

lemma tp_rpow_124 {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (149 / 25 : ℝ) / N = (N : ℝ) ^ (124 / 25 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [show (124 / 25 : ℝ) = 149 / 25 - 1 by norm_num, Real.rpow_sub hN0, Real.rpow_one]

lemma tp_rpow_99 {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (149 / 25 : ℝ) / (N : ℝ) ^ 2 = (N : ℝ) ^ (99 / 25 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [show (99 / 25 : ℝ) = 149 / 25 - 2 by norm_num, Real.rpow_sub hN0, Real.rpow_two]

/-- The overlap terms after multiplication by `N^{149/25}`. -/
lemma tp_W_le {N : ℕ} (hN : 7 ≤ N) (y : ℝ) :
    (3 * (N : ℝ) ^ 2 * tp_b1 N y + 9 * N * tp_b2 N y) / (N.choose 3 : ℝ) *
        (N : ℝ) ^ (149 / 25 : ℝ) ≤
      36 * ((N : ℝ) ^ (124 / 25 : ℝ) * Real.exp (-(13 * (y - 3 * (1 + ps_eps N)) ^ 2) / 2) +
        (N : ℝ) ^ 6 * tp_err (tp_E2j 3 1) (tp_E3j 3 1) N) +
      108 * ((N : ℝ) ^ (99 / 25 : ℝ) * Real.exp (-(11 * (y - 3 * (1 + ps_eps N)) ^ 2) / 2) +
        (N : ℝ) ^ 6 * tp_err (tp_E2j 3 2) (tp_E3j 3 2) N) := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hM12 : (N : ℝ) ^ 3 / 12 ≤ (N.choose 3 : ℝ) := tp_choose_ge (by omega)
  have hb1 := tp_b1_nonneg N y
  have hb2 := tp_b2_nonneg N y
  have hp : 0 < (N : ℝ) ^ (149 / 25 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hnum : 0 ≤ 3 * (N : ℝ) ^ 2 * tp_b1 N y + 9 * N * tp_b2 N y := by positivity
  have hW : (3 * (N : ℝ) ^ 2 * tp_b1 N y + 9 * N * tp_b2 N y) / (N.choose 3 : ℝ) ≤
      36 * tp_b1 N y / N + 108 * tp_b2 N y / (N : ℝ) ^ 2 := by
    calc (3 * (N : ℝ) ^ 2 * tp_b1 N y + 9 * N * tp_b2 N y) / (N.choose 3 : ℝ)
        ≤ (3 * (N : ℝ) ^ 2 * tp_b1 N y + 9 * N * tp_b2 N y) / ((N : ℝ) ^ 3 / 12) :=
          div_le_div_of_nonneg_left hnum (by positivity) hM12
      _ = 36 * tp_b1 N y / N + 108 * tp_b2 N y / (N : ℝ) ^ 2 := by
          field_simp; ring
  have e1 : 36 * tp_b1 N y / N * (N : ℝ) ^ (149 / 25 : ℝ) =
      36 * ((N : ℝ) ^ (124 / 25 : ℝ) * tp_b1 N y) := by
    rw [← tp_rpow_124 hN1]; field_simp
  have e2 : 108 * tp_b2 N y / (N : ℝ) ^ 2 * (N : ℝ) ^ (149 / 25 : ℝ) =
      108 * ((N : ℝ) ^ (99 / 25 : ℝ) * tp_b2 N y) := by
    rw [← tp_rpow_99 hN1]; field_simp
  have h1 : (N : ℝ) ^ (124 / 25 : ℝ) * tp_b1 N y ≤
      (N : ℝ) ^ (124 / 25 : ℝ) * Real.exp (-(13 * (y - 3 * (1 + ps_eps N)) ^ 2) / 2) +
        (N : ℝ) ^ 6 * tp_err (tp_E2j 3 1) (tp_E3j 3 1) N := by
    rw [tp_b1, mul_add]
    have := mul_le_mul_of_nonneg_right (tp_rpow_le6 hN1 (p := 124 / 25) (by norm_num))
      (tp_errj_nonneg 1 N)
    linarith
  have h2 : (N : ℝ) ^ (99 / 25 : ℝ) * tp_b2 N y ≤
      (N : ℝ) ^ (99 / 25 : ℝ) * Real.exp (-(11 * (y - 3 * (1 + ps_eps N)) ^ 2) / 2) +
        (N : ℝ) ^ 6 * tp_err (tp_E2j 3 2) (tp_E3j 3 2) N := by
    rw [tp_b2, mul_add]
    have := mul_le_mul_of_nonneg_right (tp_rpow_le6 hN1 (p := 99 / 25) (by norm_num))
      (tp_errj_nonneg 2 N)
    linarith
  calc (3 * (N : ℝ) ^ 2 * tp_b1 N y + 9 * N * tp_b2 N y) / (N.choose 3 : ℝ) *
        (N : ℝ) ^ (149 / 25 : ℝ)
      ≤ (36 * tp_b1 N y / N + 108 * tp_b2 N y / (N : ℝ) ^ 2) * (N : ℝ) ^ (149 / 25 : ℝ) :=
        mul_le_mul_of_nonneg_right hW hp.le
    _ = 36 * ((N : ℝ) ^ (124 / 25 : ℝ) * tp_b1 N y) +
        108 * ((N : ℝ) ^ (99 / 25 : ℝ) * tp_b2 N y) := by rw [add_mul, e1, e2]
    _ ≤ _ := by linarith

/-- **The bound at fixed `N`**, under the eventual conditions. -/
lemma tp_Z_le_T {N : ℕ} (hN : 7 ≤ N) (s : State N) (hG : tp_ell N ≤ tp_G N)
    (hrad : 16 * tauN N / sigN N + ps_eps N ≤ 1 / 2) (hy : 7 ≤ tp_y N)
    (hu : tp_u N ≤ tp_pE * tp_ell N / 2) :
    (cubeM N).real (tp_Z N s (tp_y N)) ≤ tp_Tb N := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hM12 : (N : ℝ) ^ 3 / 12 ≤ (N.choose 3 : ℝ) := tp_choose_ge (by omega)
  have hM0 : 0 < (N.choose 3 : ℝ) := lt_of_lt_of_le (by positivity) hM12
  have hpE := tp_pE_pos
  have hpE1 := tp_pE_le_one
  have hℓ := tp_ell_pos hN1
  have hε := ps_eps_pos N
  have hε1 := tp_eps_le_one N
  have hy' : 3 * (1 + ps_eps N) < tp_y N := by linarith
  have hD0 : 0 ≤ tp_D N := tp_D_nonneg N
  have hb1 := tp_b1_nonneg N (tp_y N)
  have hb2 := tp_b2_nonneg N (tp_y N)
  have hW0 : 0 ≤ (3 * (N : ℝ) ^ 2 * tp_b1 N (tp_y N) + 9 * N * tp_b2 N (tp_y N)) /
      (N.choose 3 : ℝ) := by positivity
  have hV0 := tp_V_nonneg N
  have hu0 : 0 ≤ tp_u N := tp_u_nonneg N
  have hG1 : tp_G N ≤ 1 := measureReal_le_one
  have ha_eq : tp_a N (tp_y N) = tp_pE * tp_G N - tp_u N := by
    rw [tp_a, tp_u, tp_G]; ring
  have hr0 : 0 ≤ 1 - 16 * tauN N / sigN N - ps_eps N := by linarith
  have hGh := tp_Gh_le N hr0
  have hGh0 : 0 ≤ (tp_G1 3).real (tp_ball (tp_cen (tp_y N))
      (1 + 128 * tauN N / sigN N + ps_eps N)) := measureReal_nonneg
  have hG0 : 0 ≤ tp_G N := measureReal_nonneg
  set W := (3 * (N : ℝ) ^ 2 * tp_b1 N (tp_y N) + 9 * N * tp_b2 N (tp_y N)) /
      (N.choose 3 : ℝ) with hW
  have hb : tp_b0 N (tp_y N) + W ≤ tp_pE ^ 2 * tp_G N ^ 2 + (tp_V N + W) := by
    have h1 : (tp_G1 3).real (tp_ball (tp_cen (tp_y N))
        (1 + 128 * tauN N / sigN N + ps_eps N)) ^ 2 ≤ tp_G N ^ 2 + 2 * tp_D N + tp_D N ^ 2 := by
      have := pow_le_pow_left₀ hGh0 hGh 2
      nlinarith
    have hp2 : 0 ≤ tp_pE ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_left h1 hp2
    rw [tp_b0, tp_V]
    nlinarith
  obtain ⟨ha, hfin⟩ := ps_final_alg hpE hpE1 hG1 hℓ hG hu0 hu (by positivity) ha_eq hb hM0
  have hbd := tp_bound hN s hy' ha
  have e1 : ((N.choose 3 : ℝ) * tp_b0 N (tp_y N) + 3 * N ^ 2 * tp_b1 N (tp_y N) +
      9 * N * tp_b2 N (tp_y N)) / ((N.choose 3 : ℝ) * tp_a N (tp_y N) ^ 2) =
      (tp_b0 N (tp_y N) + W) / tp_a N (tp_y N) ^ 2 := by
    rw [hW]
    have : tp_a N (tp_y N) ≠ 0 := ha.ne'
    field_simp
    ring
  rw [e1] at hbd
  refine hbd.trans (hfin.trans ?_)
  have hA : 2 / ((N.choose 3 : ℝ) * (tp_pE * tp_ell N)) ≤
      24 / tp_pE * (N : ℝ) ^ (-(1 / 50 : ℝ)) := by
    have hMl : (N : ℝ) ^ (1 / 50 : ℝ) / 12 ≤ (N.choose 3 : ℝ) * tp_ell N := by
      rw [← tp_ell_M hN1]
      have := mul_le_mul_of_nonneg_right hM12 hℓ.le
      linarith
    have hp : 0 < (N : ℝ) ^ (1 / 50 : ℝ) := Real.rpow_pos_of_pos hN0 _
    rw [Real.rpow_neg hN0.le]
    calc 2 / ((N.choose 3 : ℝ) * (tp_pE * tp_ell N))
        = 2 / tp_pE / ((N.choose 3 : ℝ) * tp_ell N) := by field_simp
      _ ≤ 2 / tp_pE / ((N : ℝ) ^ (1 / 50 : ℝ) / 12) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hMl
      _ = 24 / tp_pE * ((N : ℝ) ^ (1 / 50 : ℝ))⁻¹ := by field_simp; ring
  have hB : 4 * (tp_V N + W + 2 * tp_u N) / (tp_pE * tp_ell N) ^ 2 =
      4 / tp_pE ^ 2 * ((tp_V N + 2 * tp_u N) * (N : ℝ) ^ (149 / 25 : ℝ) +
        W * (N : ℝ) ^ (149 / 25 : ℝ)) := by
    rw [← tp_ell_sq hN1]
    field_simp
    ring
  have hVu : (tp_V N + 2 * tp_u N) * (N : ℝ) ^ (149 / 25 : ℝ) ≤
      (N : ℝ) ^ 6 * (tp_V N + 2 * tp_u N) := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (tp_rpow_le6 hN1 (by norm_num)) (by positivity)
  have hWb := tp_W_le hN (tp_y N)
  rw [hB, tp_Tb]
  have h4 : (0 : ℝ) ≤ 4 / tp_pE ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left (add_le_add hVu hWb) h4
  linarith

/-- **No triple has its event** with probability tending to `0`. -/
theorem tp_tendsto_Z (s : ∀ N, State N) :
    Tendsto (fun N => (cubeM N).real (tp_Z N (s N) (tp_y N))) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tp_tendsto_T
    (Eventually.of_forall fun N => measureReal_nonneg) ?_
  have hu6 : Tendsto (fun N : ℕ => (N : ℝ) ^ 6 * tp_u N) atTop (𝓝 0) := by
    have h := ((tp_tendsto_err (tp_E2s 3) (tp_E3s 3) 6).const_mul tp_pE).add tp_tendsto_fg2_6
    simp only [mul_zero, add_zero] at h
    refine h.congr fun N => ?_
    rw [tp_u]; ring
  have hp2 : (0 : ℝ) < tp_pE / 2 := by have := tp_pE_pos; positivity
  filter_upwards [eventually_ge_atTop 7, tp_ev_Glo, tp_ev_radius, tp_ev_y_ge 7,
    hu6.eventually (ge_mem_nhds hp2)] with N hN hG hrad hy hu
  refine tp_Z_le_T hN (s N) hG hrad hy ?_
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have h6 : (0 : ℝ) < (N : ℝ) ^ 6 := by positivity
  have hle : ((N : ℝ) ^ 6)⁻¹ ≤ tp_ell N := by
    rw [tp_ell, ← tp_rpow_nat hN1 6, ← Real.rpow_neg hN0.le]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by norm_num)
  have hu' : tp_u N ≤ tp_pE / 2 * ((N : ℝ) ^ 6)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ h6]; linarith
  have := mul_le_mul_of_nonneg_left hle hp2.le
  linarith

/-! ### The main theorem -/

/-- The good event of the pair lemma for `gZ`, in plain coordinates. -/
def tp_notGZ (N : ℕ) (s : State N) : Set (Param N) := {z | z ∈ cube N ∧ ¬ gZ N (flipP s z)}

lemma tp_volume_notGZ_le (s : State N) : volume (tp_notGZ N s) ≤ cubeM N {w | ¬ gZ N w} := by
  have hsub : tp_notGZ N s ⊆ flipE s ⁻¹' (cube N ∩ {w | ¬ gZ N w}) := by
    rintro z ⟨hz, hG⟩
    exact ⟨flipP_cube hz s, hG⟩
  calc volume (tp_notGZ N s) ≤ volume (flipE s ⁻¹' (cube N ∩ {w | ¬ gZ N w})) := measure_mono hsub
    _ = cubeM N {w | ¬ gZ N w} := by
        rw [(mp_flipE s).measure_preimage_equiv, volume_cube_inter]

/-- **Theorem P3 for triples.** With probability tending to one, some 3-set `S` has
`φ_s(S) ≥ 0.31 √(log N) σ_N`. -/
theorem tendsto_triple_lower (s : ∀ N, State N) :
    Tendsto (fun N => volume {z | z ∈ cube N ∧ ¬ ∃ S : Finset (Fin N), S.card = 3 ∧
      tp_c3 * Real.sqrt (Real.log N) * sigN N ≤ phi z (s N) S}) atTop (𝓝 0) := by
  have hZ : Tendsto (fun N => ENNReal.ofReal ((cubeM N).real (tp_Z N (s N) (tp_y N)))) atTop
      (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tp_tendsto_Z s)
  have hG : Tendsto (fun N => volume (notGoodSet N (s N))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tendsto_cubeM_notGood s)
      (fun _ => zero_le) fun N => volume_notGoodSet_le (s N)
  have hgZ : Tendsto (fun N => volume (tp_notGZ N (s N))) atTop (𝓝 0) := by
    have h : Tendsto (fun N => ENNReal.ofReal (fZ N)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]; exact ENNReal.tendsto_ofReal tendsto_fZ
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
      fun N => (tp_volume_notGZ_le (s N)).trans cubeM_not_gZ
  have hsum := (hG.add hgZ).add hZ
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [tp_det, tp_ev_phi, tp_ev_y_ge 20000] with N hdet hphi hy
  set A := {z | z ∈ cube N ∧ ¬ ∃ S : Finset (Fin N), S.card = 3 ∧
      tp_c3 * Real.sqrt (Real.log N) * sigN N ≤ phi z (s N) S}
  have hsub : A ⊆ (cube N \ openCube N) ∪ notGoodSet N (s N) ∪ tp_notGZ N (s N) ∪
      flipE (s N) ⁻¹' (cube N ∩ tp_Z N (s N) (tp_y N)) := by
    rintro z ⟨hz, hno⟩
    by_cases ho : z ∈ openCube N
    · by_cases hGw : GoodW N (s N) (flipP (s N) z)
      · by_cases hgz : gZ N (flipP (s N) z)
        · refine Or.inr ⟨flipP_cube hz (s N), fun T hT => hno ⟨T.1, T.2, ?_⟩⟩
          have hT' : flipP (s N) z ∈ tp_A (s N) (tp_y N) T.1 T.2 := hT
          have hbox : tp_effBoxZ z (s N) T.1 := by
            have h := tp_boxW_effBox hT'.2
            have e : flipP (s N) (flipP (s N) z) = z := flipP_invol (s N) z
            rwa [e] at h
          have h := hdet (s N) z T.1 T.2 (tp_y N) ho hGw hgz hbox hy hT'.1
          unfold tp_c3
          exact hphi.trans h
        · exact Or.inl (Or.inr ⟨hz, hgz⟩)
      · exact Or.inl (Or.inl (Or.inr ⟨hz, hGw⟩))
    · exact Or.inl (Or.inl (Or.inl ⟨hz, ho⟩))
  calc volume A ≤ volume ((cube N \ openCube N) ∪ notGoodSet N (s N) ∪ tp_notGZ N (s N) ∪
        flipE (s N) ⁻¹' (cube N ∩ tp_Z N (s N) (tp_y N))) := measure_mono hsub
    _ ≤ volume (cube N \ openCube N) + volume (notGoodSet N (s N)) +
        volume (tp_notGZ N (s N)) + volume (flipE (s N) ⁻¹' (cube N ∩ tp_Z N (s N) (tp_y N))) :=
        (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ = volume (notGoodSet N (s N)) + volume (tp_notGZ N (s N)) +
        ENNReal.ofReal ((cubeM N).real (tp_Z N (s N) (tp_y N))) := by
        rw [volume_cube_diff_openCube, zero_add, (mp_flipE (s N)).measure_preimage_equiv,
          volume_cube_inter, ofReal_measureReal]

end

end Census
end IIT
