/-
Census of complexes: Gaussian comparison for the pair statistics.

Removing the block of a state, the six cause-side differences of a pair are a sum of `2^(N-2) - 1`
iid summands (`PairBlocks`), and for two disjoint pairs the twelve differences are a sum of
`2^(N-4) - 1` iid summands (`PairBlocks2`).  Lindeberg's replacement method with the smooth orthant
functions (`Lindeberg`) and Gaussian stability (`GaussBox`) compare these sums with the explicit
Gaussian limit laws, with smoothing width `ε_N = (99/100)^N`:
* `ps_rest_low`: the probability of a lower orthant is at least the Gaussian orthant at level
  `c - ε_N`, minus an error `ps_err6 N`;
* `ps_rest_up`: for two pairs, the probability of an upper orthant is at most the square of the
  six-dimensional Gaussian orthant at level `c + ε_N`, plus an error `ps_err12 N`;
* both errors are `o(N^{-2})`.
-/
import IIT.Census.Lindeberg
import IIT.Census.GaussBox
import IIT.Census.PairBlocks2

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

noncomputable section

variable {N : ℕ}

/-! ### The two descriptions of the limit covariance agree -/

lemma ps_gam_eq (p q : Fin 6) : gbox_Gam p q = pb_Gam p q := by
  fin_cases p <;> fin_cases q <;> norm_num [gbox_Gam, pb_Gam, pb_pu, pb_pt, gbox_c1, gbox_c2]

lemma ps_gam12_eq (j l : Fin 12) : gbox_Gam12 j l = pb_Gam2 j l := by
  refine pb_fin12_cases (P := fun j => gbox_Gam12 j l = pb_Gam2 j l) (fun p => ?_)
    (fun p => ?_) j <;>
  refine pb_fin12_cases (P := fun l => gbox_Gam12 _ l = pb_Gam2 _ l) (fun q => ?_)
    (fun q => ?_) l
  · rw [gbox_Gam12_ll, pb_Gam2_LL, ps_gam_eq]
  · rw [gbox_Gam12_lr, pb_Gam2_LR]
  · rw [gbox_Gam12_rl, pb_Gam2_RL]
  · rw [gbox_Gam12_rr, pb_Gam2_RR, ps_gam_eq]

/-! ### Smoothing width and error terms -/

/-- The smoothing width `ε_N = (99/100)^N`. -/
def ps_eps (N : ℕ) : ℝ := (99 / 100 : ℝ) ^ N

lemma ps_eps_pos (N : ℕ) : 0 < ps_eps N := by unfold ps_eps; positivity

lemma ps_K_div_eps (N : ℕ) : lind_Kpsi / ps_eps N = lind_Kpsi * (100 / 99 : ℝ) ^ N := by
  rw [ps_eps, div_eq_mul_inv, ← inv_pow]
  norm_num

/-- The Lindeberg error with second-moment constant `C2` and third-moment constant `C3`. -/
def ps_err (C2 C3 : ℝ) (N : ℕ) : ℝ :=
  (lind_Kpsi / ps_eps N) ^ 2 * (C2 * (3 / 4 : ℝ) ^ N) / 2 +
    (lind_Kpsi / ps_eps N) ^ 3 * (C3 * (23 / 25 : ℝ) ^ N) / 6

/-- The error of the six-dimensional comparison. -/
def ps_err6 (N : ℕ) : ℝ := ps_err 180 (3456 + 3 * gbox_C3 gbox_T6) N

/-- The error of the twelve-dimensional comparison. -/
def ps_err12 (N : ℕ) : ℝ := ps_err 2448 (442368 + 6 * gbox_C3 gbox_T12) N

lemma ps_err_nonneg {C2 C3 : ℝ} (h2 : 0 ≤ C2) (h3 : 0 ≤ C3) (N : ℕ) : 0 ≤ ps_err C2 C3 N := by
  have := ps_eps_pos N
  have := lind_Kpsi_pos
  unfold ps_err; positivity

lemma ps_tendsto_sq_mul_pow {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (C : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * (C * r ^ N)) atTop (𝓝 0) := by
  have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 (by rwa [abs_of_nonneg hr0])).const_mul C
  rw [mul_zero] at h
  refine h.congr fun N => ?_
  ring

lemma ps_pow_aux (K r q C : ℝ) (n k : ℕ) :
    (K * r ^ n) ^ k * (C * q ^ n) = K ^ k * C * (r ^ k * q) ^ n := by
  rw [mul_pow (r ^ k) q, ← pow_mul, mul_comm k n, pow_mul]
  ring

/-- The Lindeberg errors are `o(N^{-2})`. -/
theorem ps_tendsto_err (C2 C3 : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * ps_err C2 C3 N) atTop (𝓝 0) := by
  have e : ∀ N : ℕ, (N : ℝ) ^ 2 * ps_err C2 C3 N =
      (N : ℝ) ^ 2 * (lind_Kpsi ^ 2 / 2 * C2 * ((100 / 99 : ℝ) ^ 2 * (3 / 4)) ^ N) +
      (N : ℝ) ^ 2 * (lind_Kpsi ^ 3 / 6 * C3 * ((100 / 99 : ℝ) ^ 3 * (23 / 25)) ^ N) := by
    intro N
    rw [ps_err, ps_K_div_eps, ps_pow_aux, ps_pow_aux]
    ring
  simp_rw [e]
  rw [← add_zero (0 : ℝ)]
  exact (ps_tendsto_sq_mul_pow (by norm_num) (by norm_num) _).add
    (ps_tendsto_sq_mul_pow (by norm_num) (by norm_num) _)

/-! ### An elementary bound on `1/√(B-1)` -/

lemma ps_inv_sqrt_le {B : ℕ} {k A : ℝ} (hB : 2 ≤ B) (hk : (B : ℝ) * k = 2 ^ N) (hA : 0 ≤ A)
    (hkA : 2 * k ≤ A ^ 2) : 1 / Real.sqrt ((B - 1 : ℕ) : ℝ) ≤ A * (3 / 4 : ℝ) ^ N := by
  have hBr : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hcast : ((B - 1 : ℕ) : ℝ) = B - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ B)]; simp
  set X := (1 / 2 : ℝ) ^ N with hX
  have hX0 : 0 ≤ X := by positivity
  have h2N : X * ((B : ℝ) * k) = 1 := by rw [hk, hX, ← mul_pow]; norm_num
  set t := k * X with ht
  have htB : t * B = 1 := by rw [ht]; linarith [h2N]
  have ht0 : 0 ≤ t := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have h1 : ((B - 1 : ℕ) : ℝ)⁻¹ ≤ 2 * k * X := by
    rw [hcast, inv_le_iff_one_le_mul₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hBr ht0]
  have hk0 : 0 ≤ k := by
    have : (0 : ℝ) < 2 ^ N := by positivity
    by_contra hneg; push Not at hneg; nlinarith
  have h2 : 2 * k * X ≤ (A * (3 / 4 : ℝ) ^ N) ^ 2 := by
    have hX' : X ≤ ((3 / 4 : ℝ) ^ N) ^ 2 := by
      rw [hX, ← pow_mul, mul_comm, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) N
    rw [mul_pow]
    exact mul_le_mul hkA hX' hX0 (sq_nonneg _)
  rw [one_div, ← Real.sqrt_inv]
  calc Real.sqrt (((B - 1 : ℕ) : ℝ)⁻¹) ≤ Real.sqrt ((A * (3 / 4 : ℝ) ^ N) ^ 2) :=
        Real.sqrt_le_sqrt (h1.trans h2)
    _ = A * (3 / 4 : ℝ) ^ N := Real.sqrt_sq (by positivity)

/-! ### The six-dimensional lower comparison -/

lemma ps_measurable_sum {B d : ℕ} : Measurable fun x : Fin B → Fin d → ℝ => ∑ k, x k :=
  Finset.measurable_sum _ fun k _ => measurable_pi_apply k

lemma ps_measurable_sumXr (a b : Fin N) (s : State N) :
    Measurable fun w : Param N => ∑ k, pb_Xr a b s w k :=
  Finset.measurable_sum _ fun k _ => (measurable_pi_apply k).comp (pb_measurable_Xr a b s)

lemma ps_measurable_sumYr (a b c d : Fin N) (s : State N) :
    Measurable fun w : Param N => ∑ k, pb_Yr a b c d s w k :=
  Finset.measurable_sum _ fun k _ => (measurable_pi_apply k).comp (pb_measurable_Yr a b c d s)

lemma ps_B_four {a b : Fin N} (hab : a ≠ b) : (pb_B a b : ℝ) * 4 = 2 ^ N := by
  rw [pb_B_eq hab]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by have := pb_two_le hab; omega⟩
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

lemma ps_B2_sixteen {a b c d : Fin N} (h : pb_dist4 a b c d) :
    (pb_B2 a b c d : ℝ) * 16 = 2 ^ N := by
  rw [pb_B2_eq h]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 4 := ⟨N - 4, by have := pb_four_le h; omega⟩
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

/-- `B'·|I - Γ/B'| = |B' I - Γ|`. -/
lemma ps_mul_abs_sub_div {B I G : ℝ} (hB : 0 < B) : B * |I - G / B| = |B * I - G| := by
  rw [← abs_of_pos hB, ← abs_mul, abs_of_pos hB]
  congr 1
  field_simp

/-- The third-moment term of the scaled Gaussian summands. -/
lemma ps_gauss_third {m d B : ℕ} (T : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ)) (hB : 0 < B) :
    (B : ℝ) * ∫ x, (∑ j, |x j|) ^ 3 ∂(gbox_sumLaw T B) = gbox_C3 T * (1 / Real.sqrt B) := by
  rw [gbox_sumLaw_cube]
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hs : 0 < Real.sqrt B := Real.sqrt_pos.2 hB'
  have hss : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB'.le
  have h3 : Real.sqrt B ^ 3 = B * Real.sqrt B := by linear_combination Real.sqrt B * hss
  rw [h3]
  field_simp

/-- **Lower comparison** for one pair: removing the block of `s`, the lower orthant at level `c`
has probability at least the Gaussian orthant at level `c - ε_N`, minus `ps_err6 N`. -/
theorem ps_rest_low {a b : Fin N} (hab : a ≠ b) (s : State N) (hB : 2 ≤ pb_B a b) (c : ℝ) :
    gbox_G6.real {x | ∀ p, x p ≤ c - ps_eps N} - ps_err6 N ≤
      (cubeM N).real {w | ∀ p, (∑ k, pb_Xr a b s w k) p ≤ c} := by
  set ε := ps_eps N with hεdef
  have hε : 0 < ε := ps_eps_pos N
  set B' := pb_B a b - 1 with hB'def
  have hB' : 0 < B' := by omega
  have hB'r : (0 : ℝ) < B' := by exact_mod_cast hB'
  set cv : Fin 6 → ℝ := fun _ => c with hcv
  have hg := ps_measurable_sumXr a b s
  have h1 := lind_integral_orthLow_le (μ := cubeM N) hg cv hε
  have h2 : ∫ w, orthLow cv ε (∑ k, pb_Xr a b s w k) ∂cubeM N =
      ∫ x, orthLow cv ε (∑ k, x k) ∂(Measure.pi fun _ : Fin B' => pb_nu a b) := by
    rw [← pb_map_Xr hab s]
    exact (integral_map (pb_measurable_Xr a b s).aemeasurable
      ((measurable_orthLow cv ε).comp ps_measurable_sum).aestronglyMeasurable).symm
  have h3 := lind_orthLow_pi (ν := pb_nu a b) (γ := gbox_sumLaw gbox_T6 B') (pb_nu_mean a b)
    (gbox_sumLaw_coord _ _) (pb_nu_integrable3 a b) (gbox_sumLaw_integrable_cube _ _) cv hε B'
  have h4 := gbox_integral_sum_pi_G6 hB' (measurable_orthLow cv ε)
  have h5 := lind_real_le_integral_orthLow (μ := gbox_G6) measurable_id cv hε
  -- the error term
  set K := lind_Kpsi / ε with hK
  have hK0 : 0 ≤ K := by have := lind_Kpsi_pos; positivity
  have hsec : (B' : ℝ) * ∑ j, ∑ k, |∫ x, x j * x k ∂pb_nu a b -
      ∫ x, x j * x k ∂gbox_sumLaw gbox_T6 B'| ≤ 180 * (3 / 4 : ℝ) ^ N := by
    rw [Finset.mul_sum]
    calc ∑ j, (B' : ℝ) * ∑ k, |∫ x, x j * x k ∂pb_nu a b -
          ∫ x, x j * x k ∂gbox_sumLaw gbox_T6 B'|
        ≤ ∑ _j : Fin 6, ∑ _k : Fin 6, 5 * (3 / 4 : ℝ) ^ N := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun k _ => ?_
          rw [gbox_sumLaw6_mul hB', ps_gam_eq, ps_mul_abs_sub_div hB'r]
          exact pb_nu_second_pred hab j k
      _ = 180 * (3 / 4 : ℝ) ^ N := by simp; ring
  have hthird : (B' : ℝ) * (∫ x, (∑ j, |x j|) ^ 3 ∂pb_nu a b +
      ∫ x, (∑ j, |x j|) ^ 3 ∂gbox_sumLaw gbox_T6 B') ≤
      (3456 + 3 * gbox_C3 gbox_T6) * (23 / 25 : ℝ) ^ N := by
    have hν0 : 0 ≤ ∫ x, (∑ j, |x j|) ^ 3 ∂pb_nu a b :=
      integral_nonneg fun x => pow_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) 3
    have hBB : (B' : ℝ) ≤ pb_B a b := by exact_mod_cast Nat.sub_le _ _
    have hν := pb_nu_third hab
    have hγ := ps_gauss_third gbox_T6 hB'
    have hs := ps_inv_sqrt_le (N := N) (k := 4) (A := 3) hB (ps_B_four hab) (by norm_num)
      (by norm_num)
    have hC := gbox_C3_nonneg gbox_T6
    have h34 : (3 / 4 : ℝ) ^ N ≤ (23 / 25 : ℝ) ^ N :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) N
    rw [mul_add, hγ]
    calc (B' : ℝ) * ∫ x, (∑ j, |x j|) ^ 3 ∂pb_nu a b + gbox_C3 gbox_T6 * (1 / Real.sqrt B')
        ≤ (pb_B a b : ℝ) * ∫ x, (∑ j, |x j|) ^ 3 ∂pb_nu a b +
            gbox_C3 gbox_T6 * (3 * (3 / 4 : ℝ) ^ N) := by
          gcongr
      _ ≤ 3456 * (23 / 25 : ℝ) ^ N + gbox_C3 gbox_T6 * (3 * (23 / 25 : ℝ) ^ N) := by
          gcongr
      _ = (3456 + 3 * gbox_C3 gbox_T6) * (23 / 25 : ℝ) ^ N := by ring
  have herr : (B' : ℝ) * (K ^ 2 / 2 * ∑ j, ∑ k, |∫ x, x j * x k ∂pb_nu a b -
      ∫ x, x j * x k ∂gbox_sumLaw gbox_T6 B'| + K ^ 3 / 6 * (∫ x, (∑ j, |x j|) ^ 3 ∂pb_nu a b +
      ∫ x, (∑ j, |x j|) ^ 3 ∂gbox_sumLaw gbox_T6 B')) ≤ ps_err6 N := by
    rw [ps_err6, ps_err, ← hK]
    have e : (B' : ℝ) * (K ^ 2 / 2 * ∑ j, ∑ k, |∫ x, x j * x k ∂pb_nu a b -
        ∫ x, x j * x k ∂gbox_sumLaw gbox_T6 B'| + K ^ 3 / 6 * (∫ x, (∑ j, |x j|) ^ 3 ∂pb_nu a b +
        ∫ x, (∑ j, |x j|) ^ 3 ∂gbox_sumLaw gbox_T6 B')) =
        K ^ 2 * ((B' : ℝ) * ∑ j, ∑ k, |∫ x, x j * x k ∂pb_nu a b -
        ∫ x, x j * x k ∂gbox_sumLaw gbox_T6 B'|) / 2 + K ^ 3 * ((B' : ℝ) *
        (∫ x, (∑ j, |x j|) ^ 3 ∂pb_nu a b + ∫ x, (∑ j, |x j|) ^ 3 ∂gbox_sumLaw gbox_T6 B')) / 6 := by
      ring
    rw [e]
    gcongr
  have h5' : gbox_G6.real {x | ∀ p, x p ≤ c - ε} ≤ ∫ x, orthLow cv ε x ∂gbox_G6 := h5
  rw [abs_le] at h3
  have h1' : ∫ w, orthLow cv ε (∑ k, pb_Xr a b s w k) ∂cubeM N ≤
      (cubeM N).real {w | ∀ p, (∑ k, pb_Xr a b s w k) p ≤ c} := h1
  linarith [h3.1]

/-- **Upper comparison** for two disjoint pairs: removing the superblock of `s`, the upper orthant
at level `c` has probability at most the square of the six-dimensional Gaussian orthant at level
`c + ε_N`, plus `ps_err12 N`. -/
theorem ps_rest_up {a b c d : Fin N} (h : pb_dist4 a b c d) (s : State N) (hB : 2 ≤ pb_B2 a b c d)
    (c0 : ℝ) :
    (cubeM N).real {w | ∀ q, (∑ k, pb_Yr a b c d s w k) q ≤ c0} ≤
      (gbox_G6.real {x | ∀ p, x p ≤ c0 + ps_eps N}) ^ 2 + ps_err12 N := by
  set ε := ps_eps N with hεdef
  have hε : 0 < ε := ps_eps_pos N
  set B' := pb_B2 a b c d - 1 with hB'def
  have hB' : 0 < B' := by omega
  have hB'r : (0 : ℝ) < B' := by exact_mod_cast hB'
  set cv : Fin 12 → ℝ := fun _ => c0 with hcv
  have hg := ps_measurable_sumYr a b c d s
  have h1 := lind_real_le_integral_orthUp (μ := cubeM N) hg cv hε
  have h2 : ∫ w, orthUp cv ε (∑ k, pb_Yr a b c d s w k) ∂cubeM N =
      ∫ x, orthUp cv ε (∑ k, x k) ∂(Measure.pi fun _ : Fin B' => pb_nu2 a b c d) := by
    rw [← pb_map_Yr h s]
    exact (integral_map (pb_measurable_Yr a b c d s).aemeasurable
      ((measurable_orthUp cv ε).comp ps_measurable_sum).aestronglyMeasurable).symm
  have h3 := lind_orthUp_pi (ν := pb_nu2 a b c d) (γ := gbox_sumLaw gbox_T12 B')
    (pb_nu2_mean a b c d) (gbox_sumLaw_coord _ _) (pb_nu2_integrable3 a b c d)
    (gbox_sumLaw_integrable_cube _ _) cv hε B'
  have h4 := gbox_integral_sum_pi_G12 hB' (measurable_orthUp cv ε)
  have h5 := lind_integral_orthUp_le (μ := gbox_G12) measurable_id cv hε
  set K := lind_Kpsi / ε with hK
  have hK0 : 0 ≤ K := by have := lind_Kpsi_pos; positivity
  have hsec : (B' : ℝ) * ∑ j, ∑ k, |∫ x, x j * x k ∂pb_nu2 a b c d -
      ∫ x, x j * x k ∂gbox_sumLaw gbox_T12 B'| ≤ 2448 * (3 / 4 : ℝ) ^ N := by
    rw [Finset.mul_sum]
    calc ∑ j, (B' : ℝ) * ∑ k, |∫ x, x j * x k ∂pb_nu2 a b c d -
          ∫ x, x j * x k ∂gbox_sumLaw gbox_T12 B'|
        ≤ ∑ _j : Fin 12, ∑ _k : Fin 12, 17 * (3 / 4 : ℝ) ^ N := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun k _ => ?_
          rw [gbox_sumLaw12_mul hB', ps_gam12_eq, ps_mul_abs_sub_div hB'r]
          exact pb_nu2_second_pred h j k
      _ = 2448 * (3 / 4 : ℝ) ^ N := by simp; ring
  have hthird : (B' : ℝ) * (∫ x, (∑ j, |x j|) ^ 3 ∂pb_nu2 a b c d +
      ∫ x, (∑ j, |x j|) ^ 3 ∂gbox_sumLaw gbox_T12 B') ≤
      (442368 + 6 * gbox_C3 gbox_T12) * (23 / 25 : ℝ) ^ N := by
    have hν0 : 0 ≤ ∫ x, (∑ j, |x j|) ^ 3 ∂pb_nu2 a b c d :=
      integral_nonneg fun x => pow_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) 3
    have hBB : (B' : ℝ) ≤ pb_B2 a b c d := by exact_mod_cast Nat.sub_le _ _
    have hν := pb_nu2_third h
    have hγ := ps_gauss_third gbox_T12 hB'
    have hs := ps_inv_sqrt_le (N := N) (k := 16) (A := 6) hB (ps_B2_sixteen h) (by norm_num)
      (by norm_num)
    have hC := gbox_C3_nonneg gbox_T12
    have h34 : (3 / 4 : ℝ) ^ N ≤ (23 / 25 : ℝ) ^ N :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) N
    rw [mul_add, hγ]
    calc (B' : ℝ) * ∫ x, (∑ j, |x j|) ^ 3 ∂pb_nu2 a b c d + gbox_C3 gbox_T12 * (1 / Real.sqrt B')
        ≤ (pb_B2 a b c d : ℝ) * ∫ x, (∑ j, |x j|) ^ 3 ∂pb_nu2 a b c d +
            gbox_C3 gbox_T12 * (6 * (3 / 4 : ℝ) ^ N) := by
          gcongr
      _ ≤ 442368 * (23 / 25 : ℝ) ^ N + gbox_C3 gbox_T12 * (6 * (23 / 25 : ℝ) ^ N) := by
          gcongr
      _ = (442368 + 6 * gbox_C3 gbox_T12) * (23 / 25 : ℝ) ^ N := by ring
  have herr : (B' : ℝ) * (K ^ 2 / 2 * ∑ j, ∑ k, |∫ x, x j * x k ∂pb_nu2 a b c d -
      ∫ x, x j * x k ∂gbox_sumLaw gbox_T12 B'| + K ^ 3 / 6 * (∫ x, (∑ j, |x j|) ^ 3 ∂pb_nu2 a b c d +
      ∫ x, (∑ j, |x j|) ^ 3 ∂gbox_sumLaw gbox_T12 B')) ≤ ps_err12 N := by
    rw [ps_err12, ps_err, ← hK]
    have e : (B' : ℝ) * (K ^ 2 / 2 * ∑ j, ∑ k, |∫ x, x j * x k ∂pb_nu2 a b c d -
        ∫ x, x j * x k ∂gbox_sumLaw gbox_T12 B'| + K ^ 3 / 6 *
        (∫ x, (∑ j, |x j|) ^ 3 ∂pb_nu2 a b c d +
        ∫ x, (∑ j, |x j|) ^ 3 ∂gbox_sumLaw gbox_T12 B')) =
        K ^ 2 * ((B' : ℝ) * ∑ j, ∑ k, |∫ x, x j * x k ∂pb_nu2 a b c d -
        ∫ x, x j * x k ∂gbox_sumLaw gbox_T12 B'|) / 2 + K ^ 3 * ((B' : ℝ) *
        (∫ x, (∑ j, |x j|) ^ 3 ∂pb_nu2 a b c d +
          ∫ x, (∑ j, |x j|) ^ 3 ∂gbox_sumLaw gbox_T12 B')) / 6 := by
      ring
    rw [e]
    gcongr
  have h5' : ∫ x, orthUp cv ε x ∂gbox_G12 ≤
      (gbox_G6.real {x | ∀ p, x p ≤ c0 + ε}) ^ 2 := by
    refine h5.trans (le_of_eq ?_)
    exact gbox_G12_box (c0 + ε)
  rw [abs_le] at h3
  have h1' : (cubeM N).real {w | ∀ q, (∑ k, pb_Yr a b c d s w k) q ≤ c0} ≤
      ∫ w, orthUp cv ε (∑ k, pb_Yr a b c d s w k) ∂cubeM N := h1
  linarith [h3.2]

end

end Census
end IIT
