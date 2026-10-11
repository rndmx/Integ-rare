/-
Census, Theorem E: Gaussian comparison for linear images of the field of an ordered `k`-set.

For an injection `e : Fin k → Fin N` the field `te_xi he w = ∑_β X_β` is the sum of the block
summands of `BlocksGenK`.  For a matrix `L : Fin m → Fin (k 2^k) → ℝ` the vectors `L X_β` are iid,
and Lindeberg's method with the smooth orthant function (`Lindeberg`) together with Gaussian
stability (`GaussGen`) gives
`P(L ξ ≤ c) ≤ P(L G_k ≤ c + ε_N) + ps_err C₂ C₃ N` (`te_lind_up`), with constants depending only
on `k` and `Λ = ∑ |L j p|`.  Consequences: the half-space bound `te_halfspace_le` and the slab
bound `te_slab_le`, and the decay `N^n · ps_err C₂ C₃ N → 0` (`te_tendsto_err`).
-/
import IIT.Census.PairSecond
import IIT.Census.BlocksGenK

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

noncomputable section

variable {N k : ℕ}

/-! ### The field and linear maps -/

/-- The field of the ordered `k`-set `e`, in `σ_N` units and centred at `a_k`. -/
def te_xi {e : Fin k → Fin N} (he : Function.Injective e) (w : Param N) : Fin (k * 2 ^ k) → ℝ :=
  ∑ β, bg_sX he β w

lemma te_xi_apply {e : Fin k → Fin N} (he : Function.Injective e) (w : Param N)
    (p : Fin (k * 2 ^ k)) :
    te_xi he w p =
      (Num w (bg_U e) (bg_U e) (bg_pst e (gg_pat k p)) (e (gg_unit k p)) - bg_ak k) / sigN N :=
  bg_s_sum he w p

/-- The linear map with matrix `L`. -/
def te_lin {m d : ℕ} (L : Fin m → Fin d → ℝ) (x : Fin d → ℝ) : Fin m → ℝ :=
  fun j => ∑ p, L j p * x p

/-- The total mass `Λ = ∑_{j,p} |L j p|`. -/
def te_Lam {m d : ℕ} (L : Fin m → Fin d → ℝ) : ℝ := ∑ j, ∑ p, |L j p|

lemma te_Lam_nonneg {m d : ℕ} (L : Fin m → Fin d → ℝ) : 0 ≤ te_Lam L :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _

lemma te_measurable_lin {m d : ℕ} (L : Fin m → Fin d → ℝ) : Measurable (te_lin L) :=
  Measurable.of_eval fun j =>
    Finset.measurable_sum _ fun p _ => (measurable_pi_apply p).const_mul _

lemma te_lin_sum {m d B : ℕ} (L : Fin m → Fin d → ℝ) (x : Fin B → Fin d → ℝ) :
    te_lin L (∑ β, x β) = ∑ β, te_lin L (x β) := by
  funext j
  simp only [te_lin, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

lemma te_abs_lin_le {m d : ℕ} (L : Fin m → Fin d → ℝ) (x : Fin d → ℝ) :
    ∑ j, |te_lin L x j| ≤ te_Lam L * ∑ p, |x p| := by
  unfold te_lin te_Lam
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (lind_abs_le_sum_abs x p) (abs_nonneg _)

/-! ### Moments of the image law -/

section Moments

variable {m d : ℕ} (L : Fin m → Fin d → ℝ) {ν : Measure (Fin d → ℝ)} [IsProbabilityMeasure ν]

lemma te_map_mean (h0 : ∀ p, ∫ x, x p ∂ν = 0)
    (h3 : Integrable (fun x => (∑ p, |x p|) ^ 3) ν) (j : Fin m) :
    ∫ y, y j ∂(ν.map (te_lin L)) = 0 := by
  rw [integral_map (te_measurable_lin L).aemeasurable
    (measurable_pi_apply j).aestronglyMeasurable]
  simp only [te_lin]
  rw [integral_finsetSum _ fun p _ => (lind_integrable_coord h3 p).const_mul _]
  simp [integral_const_mul, h0]

lemma te_map_mul (h3 : Integrable (fun x => (∑ p, |x p|) ^ 3) ν) (j j' : Fin m) :
    ∫ y, y j * y j' ∂(ν.map (te_lin L)) =
      ∑ p, ∑ q, L j p * L j' q * ∫ x, x p * x q ∂ν := by
  have hm : Measurable fun y : Fin m → ℝ => y j * y j' := by fun_prop
  rw [integral_map (te_measurable_lin L).aemeasurable hm.aestronglyMeasurable]
  simp only [te_lin, Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun p _ => integrable_finset_sum _ fun q _ =>
    ((lind_integrable_mul h3 p q).const_mul (L j p * L j' q)).congr
      (Filter.Eventually.of_forall fun x => by ring)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum _ fun q _ =>
    ((lind_integrable_mul h3 p q).const_mul (L j p * L j' q)).congr
      (Filter.Eventually.of_forall fun x => by ring)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

lemma te_measurable_abs3 {n : ℕ} : Measurable fun y : Fin n → ℝ => (∑ j, |y j|) ^ 3 :=
  (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).abs).pow_const 3

lemma te_map_int3 (h3 : Integrable (fun x => (∑ p, |x p|) ^ 3) ν) :
    Integrable (fun y => (∑ j, |y j|) ^ 3) (ν.map (te_lin L)) := by
  rw [integrable_map_measure te_measurable_abs3.aestronglyMeasurable
    (te_measurable_lin L).aemeasurable]
  refine (h3.const_mul (te_Lam L ^ 3)).mono'
    (te_measurable_abs3.comp (te_measurable_lin L)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, Real.norm_eq_abs]
  have h0 : 0 ≤ ∑ j, |te_lin L x j| := sum_nonneg fun _ _ => abs_nonneg _
  rw [abs_of_nonneg (pow_nonneg h0 3), ← mul_pow]
  exact pow_le_pow_left₀ h0 (te_abs_lin_le L x) 3

lemma te_map_third (h3 : Integrable (fun x => (∑ p, |x p|) ^ 3) ν) :
    ∫ y, (∑ j, |y j|) ^ 3 ∂(ν.map (te_lin L)) ≤ te_Lam L ^ 3 * ∫ x, (∑ p, |x p|) ^ 3 ∂ν := by
  rw [integral_map (te_measurable_lin L).aemeasurable te_measurable_abs3.aestronglyMeasurable,
    ← integral_const_mul]
  refine integral_mono ((te_map_int3 L h3).comp_measurable (te_measurable_lin L) |>.congr
    (Filter.Eventually.of_forall fun _ => rfl)) (h3.const_mul _) fun x => ?_
  have h0 : 0 ≤ ∑ j, |te_lin L x j| := sum_nonneg fun _ _ => abs_nonneg _
  simp only
  rw [← mul_pow]
  exact pow_le_pow_left₀ h0 (te_abs_lin_le L x) 3

end Moments

/-! ### Error constants -/

/-- The third absolute moment of `G_k`. -/
def te_C3G (k : ℕ) : ℝ := ∫ x, (∑ p, |x p|) ^ 3 ∂(gg_G k)

lemma te_C3G_nonneg (k : ℕ) : 0 ≤ te_C3G k :=
  integral_nonneg fun x => pow_nonneg (sum_nonneg fun _ _ => abs_nonneg _) 3

/-- Second-moment constant. -/
def te_C2 (k : ℕ) (Λ : ℝ) : ℝ := Λ ^ 2 * 2 ^ k

/-- Third-moment constant. -/
def te_C3 (k : ℕ) (Λ : ℝ) : ℝ := Λ ^ 3 * (8 * ((k : ℝ) * 2 ^ k) ^ 3 * 4 ^ k + te_C3G k * 2 ^ k)

lemma te_inv_sqrt_le {e : Fin k → Fin N} (he : Function.Injective e) :
    1 / Real.sqrt (bg_sB e) ≤ 2 ^ k * (3 / 4 : ℝ) ^ N := by
  have hB : (bg_sB e : ℝ) = 2 ^ (N - k) := by rw [bg_sB_eq he]; push_cast; rfl
  have hk := bg_s_le he
  have hB0 : (0 : ℝ) < bg_sB e := by rw [hB]; positivity
  have hBk : (bg_sB e : ℝ) * 2 ^ k = 2 ^ N := by
    rw [hB, ← pow_add, Nat.sub_add_cancel hk]
  rw [one_div, ← Real.sqrt_inv]
  have h1 : (bg_sB e : ℝ)⁻¹ ≤ (2 ^ k * (3 / 4 : ℝ) ^ N) ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ hB0]
    have h2 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have h3 : (1 : ℝ) ≤ 2 ^ N * ((3 / 4 : ℝ) ^ N) ^ 2 := by
      rw [← pow_mul, mul_comm N 2, pow_mul, ← mul_pow]
      exact one_le_pow₀ (by norm_num)
    calc (1 : ℝ) ≤ 2 ^ N * ((3 / 4 : ℝ) ^ N) ^ 2 := h3
      _ = bg_sB e * 2 ^ k * ((3 / 4 : ℝ) ^ N) ^ 2 := by rw [hBk]
      _ ≤ bg_sB e * 2 ^ k * ((3 / 4 : ℝ) ^ N) ^ 2 * 2 ^ k := by
          have : 0 ≤ (bg_sB e : ℝ) * 2 ^ k * ((3 / 4 : ℝ) ^ N) ^ 2 := by positivity
          nlinarith
      _ = (2 ^ k * (3 / 4 : ℝ) ^ N) ^ 2 * bg_sB e := by ring
  calc Real.sqrt (bg_sB e : ℝ)⁻¹ ≤ Real.sqrt ((2 ^ k * (3 / 4 : ℝ) ^ N) ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = 2 ^ k * (3 / 4 : ℝ) ^ N := Real.sqrt_sq (by positivity)

/-! ### The comparison -/

lemma te_sB_pos {e : Fin k → Fin N} (he : Function.Injective e) : 0 < bg_sB e := by
  rw [bg_sB_eq he]; positivity

lemma te_measurable_Y {m : ℕ} {e : Fin k → Fin N} (he : Function.Injective e)
    (L : Fin m → Fin (k * 2 ^ k) → ℝ) :
    Measurable fun w : Param N => ∑ b, te_lin L (bg_sXs he w b) :=
  Finset.measurable_sum _ fun b _ =>
    (te_measurable_lin L).comp ((measurable_pi_apply b).comp (bg_measurable_Xs _ _ _ _))

/-- **Gaussian comparison** for a linear image of the field: the lower orthant at level `c` has
probability at most the Gaussian orthant at level `c + ε_N`, plus the Lindeberg error. -/
theorem te_lind_up {m : ℕ} {e : Fin k → Fin N} (he : Function.Injective e)
    (L : Fin m → Fin (k * 2 ^ k) → ℝ) (c : Fin m → ℝ) :
    (cubeM N).real {w | ∀ j, te_lin L (te_xi he w) j ≤ c j} ≤
      (gg_G k).real {x | ∀ j, te_lin L x j ≤ c j + ps_eps N} +
        ps_err (te_C2 k (te_Lam L)) (te_C3 k (te_Lam L)) N := by
  set ε := ps_eps N with hεdef
  have hε : 0 < ε := ps_eps_pos N
  set B := bg_sB e with hBdef
  have hB : 0 < B := te_sB_pos he
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  set ν := (bg_snu e).map (te_lin L) with hν
  set γ := (gg_GsumLaw k B).map (te_lin L) with hγ
  have hxi : ∀ w, te_lin L (te_xi he w) = ∑ b, te_lin L (bg_sXs he w b) := by
    intro w
    rw [te_xi, ← bg_s_sum_Xs, te_lin_sum]
  have hset : {w : Param N | ∀ j, te_lin L (te_xi he w) j ≤ c j} =
      {w | ∀ j, (∑ b, te_lin L (bg_sXs he w b)) j ≤ c j} := by
    ext w; simp only [Set.mem_setOf_eq, hxi]
  rw [hset]
  have hY := te_measurable_Y he L
  have h1 := lind_real_le_integral_orthUp (μ := cubeM N) hY c hε
  -- law of the image summands
  have hg : Measurable fun (x : Fin B → Fin (k * 2 ^ k) → ℝ) (b : Fin B) => te_lin L (x b) :=
    Measurable.of_eval fun b => (te_measurable_lin L).comp (measurable_pi_apply b)
  have hW : Measurable fun w (b : Fin B) => te_lin L (bg_sXs he w b) :=
    hg.comp (bg_measurable_Xs _ _ _ _)
  have hmapY : (cubeM N).map (fun w b => te_lin L (bg_sXs he w b)) =
      Measure.pi fun _ : Fin B => ν := by
    calc (cubeM N).map (fun w b => te_lin L (bg_sXs he w b))
        = ((cubeM N).map (bg_sXs he)).map (fun x (b : Fin B) => te_lin L (x b)) :=
          (Measure.map_map hg (bg_measurable_Xs _ _ _ _)).symm
      _ = Measure.pi fun _ : Fin B => ν := by
          rw [bg_s_map_Xs he]
          exact Measure.pi_map_pi fun _ => (te_measurable_lin L).aemeasurable
  have hsumM : Measurable fun y : Fin B → Fin m → ℝ => ∑ b, y b :=
    Finset.measurable_sum _ fun b _ => measurable_pi_apply b
  have hf : Measurable fun y : Fin B → Fin m → ℝ => orthUp c ε (∑ b, y b) :=
    (measurable_orthUp c ε).comp hsumM
  have h2 : ∫ w, orthUp c ε (∑ b, te_lin L (bg_sXs he w b)) ∂cubeM N =
      ∫ y, orthUp c ε (∑ b, y b) ∂(Measure.pi fun _ : Fin B => ν) := by
    rw [← hmapY, integral_map hW.aemeasurable hf.aestronglyMeasurable]
  have h3 := lind_orthUp_pi (ν := ν) (γ := γ)
    (te_map_mean L (bg_snu_mean he) (bg_snu_integrable3 he))
    (te_map_mean L (gg_GsumLaw_coord k B) (gg_GsumLaw_integrable_cube k B))
    (te_map_int3 L (bg_snu_integrable3 he)) (te_map_int3 L (gg_GsumLaw_integrable_cube k B))
    c hε B
  -- the Gaussian side
  have hmapG : (Measure.pi fun _ : Fin B => gg_GsumLaw k B).map
      (fun x (b : Fin B) => te_lin L (x b)) = Measure.pi fun _ : Fin B => γ :=
    Measure.pi_map_pi fun _ => (te_measurable_lin L).aemeasurable
  have h4 : ∫ y, orthUp c ε (∑ b, y b) ∂(Measure.pi fun _ : Fin B => γ) =
      ∫ x, orthUp c ε (te_lin L x) ∂(gg_G k) := by
    rw [← hmapG, integral_map hg.aemeasurable hf.aestronglyMeasurable]
    have e2 : ∀ x : Fin B → Fin (k * 2 ^ k) → ℝ,
        orthUp c ε (∑ b, te_lin L (x b)) = orthUp c ε (te_lin L (∑ b, x b)) := by
      intro x; rw [te_lin_sum]
    simp_rw [e2]
    exact gg_G_integral_sum_pi k hB ((measurable_orthUp c ε).comp (te_measurable_lin L))
  have h5 := lind_integral_orthUp_le (μ := gg_G k) (te_measurable_lin L) c hε
  -- the error term
  set K := lind_Kpsi / ε with hK
  have hK0 : 0 ≤ K := by have := lind_Kpsi_pos; positivity
  set Λ := te_Lam L with hΛ
  have hΛ0 : 0 ≤ Λ := te_Lam_nonneg L
  have hsec : (B : ℝ) * ∑ j, ∑ j', |∫ y, y j * y j' ∂ν - ∫ y, y j * y j' ∂γ| ≤
      te_C2 k Λ * (3 / 4 : ℝ) ^ N := by
    have hpq : ∀ p q : Fin (k * 2 ^ k), (B : ℝ) * |∫ x, x p * x q ∂bg_snu e -
        ∫ x, x p * x q ∂gg_GsumLaw k B| ≤ 2 ^ k * (3 / 4 : ℝ) ^ N := by
      intro p q
      rw [gg_GsumLaw_mul k hB, ps_mul_abs_sub_div hBr]
      exact bg_snu_second he p q
    have hjj : ∀ j j', (B : ℝ) * |∫ y, y j * y j' ∂ν - ∫ y, y j * y j' ∂γ| ≤
        (∑ p, |L j p|) * (∑ q, |L j' q|) * (2 ^ k * (3 / 4 : ℝ) ^ N) := by
      intro j j'
      rw [te_map_mul L (bg_snu_integrable3 he), te_map_mul L (gg_GsumLaw_integrable_cube k B),
        ← Finset.sum_sub_distrib]
      calc (B : ℝ) * |∑ p, (∑ q, L j p * L j' q * ∫ x, x p * x q ∂bg_snu e -
            ∑ q, L j p * L j' q * ∫ x, x p * x q ∂gg_GsumLaw k B)|
          ≤ (B : ℝ) * ∑ p, ∑ q, |L j p| * |L j' q| * |∫ x, x p * x q ∂bg_snu e -
              ∫ x, x p * x q ∂gg_GsumLaw k B| := by
            refine mul_le_mul_of_nonneg_left ?_ hBr.le
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
            rw [← Finset.sum_sub_distrib]
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
            rw [← mul_sub, abs_mul, abs_mul]
        _ = ∑ p, ∑ q, |L j p| * |L j' q| * ((B : ℝ) * |∫ x, x p * x q ∂bg_snu e -
              ∫ x, x p * x q ∂gg_GsumLaw k B|) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun q _ => by ring
        _ ≤ ∑ p, ∑ q, |L j p| * |L j' q| * (2 ^ k * (3 / 4 : ℝ) ^ N) :=
            Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ =>
              mul_le_mul_of_nonneg_left (hpq p q) (by positivity)
        _ = (∑ p, |L j p|) * (∑ q, |L j' q|) * (2 ^ k * (3 / 4 : ℝ) ^ N) := by
            rw [Finset.sum_mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.sum_mul]
    rw [Finset.mul_sum]
    calc ∑ j, (B : ℝ) * ∑ j', |∫ y, y j * y j' ∂ν - ∫ y, y j * y j' ∂γ|
        ≤ ∑ j, ∑ j', (∑ p, |L j p|) * (∑ q, |L j' q|) * (2 ^ k * (3 / 4 : ℝ) ^ N) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun j' _ => hjj j j'
      _ = (∑ j, ∑ p, |L j p|) * (∑ j', ∑ q, |L j' q|) * (2 ^ k * (3 / 4 : ℝ) ^ N) := by
          rw [Finset.sum_mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
      _ = te_C2 k Λ * (3 / 4 : ℝ) ^ N := by rw [te_C2, hΛ, te_Lam]; ring
  have hthird : (B : ℝ) * (∫ y, (∑ j, |y j|) ^ 3 ∂ν + ∫ y, (∑ j, |y j|) ^ 3 ∂γ) ≤
      te_C3 k Λ * (23 / 25 : ℝ) ^ N := by
    have hν3 := te_map_third L (bg_snu_integrable3 he)
    have hγ3 := te_map_third L (gg_GsumLaw_integrable_cube k B)
    rw [gg_GsumLaw_cube] at hγ3
    have hsn := bg_snu_third he
    have hs := te_inv_sqrt_le he
    have hC := te_C3G_nonneg k
    have h34 : (3 / 4 : ℝ) ^ N ≤ (23 / 25 : ℝ) ^ N :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) N
    have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hBr
    have hss : Real.sqrt B ^ 2 = B := Real.sq_sqrt hBr.le
    have hgauss : (B : ℝ) * (te_C3G k / Real.sqrt B ^ 3) = te_C3G k * (1 / Real.sqrt B) := by
      have h3' : Real.sqrt B ^ 3 = B * Real.sqrt B := by rw [pow_succ, hss]
      rw [h3']; field_simp
    have hΛ3 : 0 ≤ Λ ^ 3 := pow_nonneg hΛ0 3
    calc (B : ℝ) * (∫ y, (∑ j, |y j|) ^ 3 ∂ν + ∫ y, (∑ j, |y j|) ^ 3 ∂γ)
        ≤ (B : ℝ) * (Λ ^ 3 * ∫ x, (∑ p, |x p|) ^ 3 ∂bg_snu e +
            Λ ^ 3 * (te_C3G k / Real.sqrt B ^ 3)) :=
          mul_le_mul_of_nonneg_left (add_le_add hν3 hγ3) hBr.le
      _ = Λ ^ 3 * ((B : ℝ) * ∫ x, (∑ p, |x p|) ^ 3 ∂bg_snu e) +
            Λ ^ 3 * (te_C3G k * (1 / Real.sqrt B)) := by rw [← hgauss]; ring
      _ ≤ Λ ^ 3 * (8 * ((k : ℝ) * 2 ^ k) ^ 3 * 4 ^ k * (23 / 25 : ℝ) ^ N) +
            Λ ^ 3 * (te_C3G k * (2 ^ k * (23 / 25 : ℝ) ^ N)) := by
          gcongr
          exact hs.trans (mul_le_mul_of_nonneg_left h34 (by positivity))
      _ = te_C3 k Λ * (23 / 25 : ℝ) ^ N := by rw [te_C3]; ring
  have herr : (B : ℝ) * (K ^ 2 / 2 * ∑ j, ∑ j', |∫ y, y j * y j' ∂ν - ∫ y, y j * y j' ∂γ| +
      K ^ 3 / 6 * (∫ y, (∑ j, |y j|) ^ 3 ∂ν + ∫ y, (∑ j, |y j|) ^ 3 ∂γ)) ≤
      ps_err (te_C2 k Λ) (te_C3 k Λ) N := by
    rw [ps_err, ← hK]
    have e : (B : ℝ) * (K ^ 2 / 2 * ∑ j, ∑ j', |∫ y, y j * y j' ∂ν - ∫ y, y j * y j' ∂γ| +
        K ^ 3 / 6 * (∫ y, (∑ j, |y j|) ^ 3 ∂ν + ∫ y, (∑ j, |y j|) ^ 3 ∂γ)) =
        K ^ 2 * ((B : ℝ) * ∑ j, ∑ j', |∫ y, y j * y j' ∂ν - ∫ y, y j * y j' ∂γ|) / 2 +
        K ^ 3 * ((B : ℝ) * (∫ y, (∑ j, |y j|) ^ 3 ∂ν + ∫ y, (∑ j, |y j|) ^ 3 ∂γ)) / 6 := by
      ring
    rw [e]
    gcongr
  rw [abs_le] at h3
  linarith [h3.2]

/-! ### Error decay -/

/-- The Lindeberg errors decay faster than every power of `N`. -/
theorem te_tendsto_err (n : ℕ) (C2 C3 : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ n * ps_err C2 C3 N) atTop (𝓝 0) := by
  have hpow : ∀ {r : ℝ}, 0 ≤ r → r < 1 → ∀ C : ℝ,
      Tendsto (fun N : ℕ => (N : ℝ) ^ n * (C * r ^ N)) atTop (𝓝 0) := by
    intro r hr0 hr C
    have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one n
      (by rwa [abs_of_nonneg hr0])).const_mul C
    rw [mul_zero] at h
    exact h.congr fun N => by ring
  have e : ∀ N : ℕ, (N : ℝ) ^ n * ps_err C2 C3 N =
      (N : ℝ) ^ n * (lind_Kpsi ^ 2 / 2 * C2 * ((100 / 99 : ℝ) ^ 2 * (3 / 4)) ^ N) +
      (N : ℝ) ^ n * (lind_Kpsi ^ 3 / 6 * C3 * ((100 / 99 : ℝ) ^ 3 * (23 / 25)) ^ N) := by
    intro N
    rw [ps_err, ps_K_div_eps, ps_pow_aux, ps_pow_aux]
    ring
  simp_rw [e]
  rw [← add_zero (0 : ℝ)]
  exact (hpow (by norm_num) (by norm_num) _).add (hpow (by norm_num) (by norm_num) _)

/-! ### Half-spaces and slabs -/

/-- The one-row matrix of `-v`. -/
def te_row (v : Fin (k * 2 ^ k) → ℝ) : Fin 1 → Fin (k * 2 ^ k) → ℝ := fun _ p => -v p

lemma te_Lam_row (v : Fin (k * 2 ^ k) → ℝ) : te_Lam (te_row v) = ∑ p, |v p| := by
  simp [te_Lam, te_row]

/-- **Half-space bound**: `P(h ≤ ⟨v, ξ⟩) ≤ exp(-(h - ε_N)² / (2 vᵀ C_k v)) + err` for
`ε_N < h`. -/
theorem te_halfspace_le {e : Fin k → Fin N} (he : Function.Injective e)
    (v : Fin (k * 2 ^ k) → ℝ) {h : ℝ} (hh : ps_eps N < h) :
    (cubeM N).real {w | h ≤ ∑ p, v p * te_xi he w p} ≤
      Real.exp (-(h - ps_eps N) ^ 2 / (2 * gg_quad (gg_C k) v)) +
        ps_err (te_C2 k (∑ p, |v p|)) (te_C3 k (∑ p, |v p|)) N := by
  have h1 := te_lind_up he (te_row v) (fun _ => -h)
  rw [te_Lam_row] at h1
  have hs1 : {w : Param N | h ≤ ∑ p, v p * te_xi he w p} =
      {w | ∀ j, te_lin (te_row v) (te_xi he w) j ≤ (fun _ : Fin 1 => -h) j} := by
    ext w
    simp only [Set.mem_setOf_eq, te_lin, te_row, neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff]
    exact ⟨fun h' _ => h', fun h' => h' 0⟩
  have hs2 : {x : Fin (k * 2 ^ k) → ℝ | ∀ j, te_lin (te_row v) x j ≤ (fun _ : Fin 1 => -h) j +
      ps_eps N} = {x | h - ps_eps N ≤ ∑ p, v p * x p} := by
    ext x
    simp only [Set.mem_setOf_eq, te_lin, te_row, neg_mul, Finset.sum_neg_distrib]
    constructor
    · intro h'; have := h' 0; linarith
    · intro h' _; linarith
  rw [hs1]
  rw [hs2] at h1
  linarith [gg_G_halfspace_le k v (h := h - ps_eps N) (by linarith)]

/-- The two-row matrix of `(r, -r)`. -/
def te_rows2 (r : Fin (k * 2 ^ k) → ℝ) : Fin 2 → Fin (k * 2 ^ k) → ℝ :=
  fun j p => if j = 0 then r p else -r p

lemma te_Lam_rows2 (r : Fin (k * 2 ^ k) → ℝ) : te_Lam (te_rows2 r) = 2 * ∑ p, |r p| := by
  simp [te_Lam, te_rows2, Fin.sum_univ_two]; ring

/-- Gaussian slab bound: `P(|X| ≤ b) ≤ 2 b / √(2 π V)` for `X ~ N(0, V)`, `V > 0`. -/
lemma te_gauss_slab {V : ℝ} (hV : 0 < V) (b : ℝ) :
    (gaussianReal 0 V.toNNReal).real {x | |x| ≤ b} ≤ 2 * |b| / Real.sqrt (2 * Real.pi * V) := by
  have hv : V.toNNReal ≠ 0 := by simp [hV]
  have hVc : ((V.toNNReal : ℝ)) = V := Real.coe_toNNReal _ hV.le
  have hs : {x : ℝ | |x| ≤ b} ⊆ Set.Icc (-|b|) |b| := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    rw [Set.mem_Icc]
    constructor <;> [linarith [neg_abs_le x, le_abs_self b]; linarith [le_abs_self x, le_abs_self b]]
  have hmono : (gaussianReal 0 V.toNNReal).real {x | |x| ≤ b} ≤
      (gaussianReal 0 V.toNNReal).real (Set.Icc (-|b|) |b|) := measureReal_mono hs
  refine hmono.trans ?_
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 hv, ENNReal.toReal_ofReal
    (setIntegral_nonneg measurableSet_Icc fun x _ => gaussianPDFReal_nonneg 0 _ x)]
  have hbd : ∀ x ∈ Set.Icc (-|b|) |b|, ‖gaussianPDFReal 0 V.toNNReal x‖ ≤
      1 / Real.sqrt (2 * Real.pi * V) := by
    intro x _
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 _ x), gaussianPDFReal_def,
      hVc]
    have hexp : Real.exp (-(x - 0) ^ 2 / (2 * V)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ (x - 0) ^ 2 / (2 * V) := by positivity
      linarith [neg_div (2 * V) ((x - 0) ^ 2)]
    have hpos : 0 ≤ (Real.sqrt (2 * Real.pi * V))⁻¹ := by positivity
    calc (Real.sqrt (2 * Real.pi * V))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * V))
        ≤ (Real.sqrt (2 * Real.pi * V))⁻¹ * 1 := mul_le_mul_of_nonneg_left hexp hpos
      _ = 1 / Real.sqrt (2 * Real.pi * V) := by ring
  have hI := norm_setIntegral_le_of_norm_le_const (by simp : volume (Set.Icc (-|b|) |b|) < ⊤) hbd
  rw [Real.norm_eq_abs] at hI
  refine (le_abs_self _).trans (hI.trans ?_)
  rw [Real.volume_real_Icc]
  have : max (|b| - -|b|) 0 = 2 * |b| := by
    rw [max_eq_left (by linarith [abs_nonneg b])]; ring
  rw [this]
  ring_nf
  exact le_rfl

/-- **Slab bound**: for `r` with `rᵀ C_k r > 0`,
`P(|⟨r, ξ⟩| ≤ a) ≤ 2 (|a| + ε_N) / √(2 π rᵀ C_k r) + err`. -/
theorem te_slab_le {e : Fin k → Fin N} (he : Function.Injective e)
    (r : Fin (k * 2 ^ k) → ℝ) (hr : 0 < gg_quad (gg_C k) r) (a : ℝ) :
    (cubeM N).real {w | |∑ p, r p * te_xi he w p| ≤ a} ≤
      2 * (|a| + ps_eps N) / Real.sqrt (2 * Real.pi * gg_quad (gg_C k) r) +
        ps_err (te_C2 k (2 * ∑ p, |r p|)) (te_C3 k (2 * ∑ p, |r p|)) N := by
  have h1 := te_lind_up he (te_rows2 r) (fun _ => a)
  rw [te_Lam_rows2] at h1
  have hs1 : {w : Param N | |∑ p, r p * te_xi he w p| ≤ a} =
      {w | ∀ j, te_lin (te_rows2 r) (te_xi he w) j ≤ (fun _ : Fin 2 => a) j} := by
    ext w
    simp only [Set.mem_setOf_eq, te_lin, te_rows2, Fin.forall_fin_two, ite_true,
      Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false, neg_mul, Finset.sum_neg_distrib,
      abs_le]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
  have hs2 : {x : Fin (k * 2 ^ k) → ℝ | ∀ j, te_lin (te_rows2 r) x j ≤ (fun _ : Fin 2 => a) j +
      ps_eps N} = (fun x => ∑ p, r p * x p) ⁻¹' {y | |y| ≤ a + ps_eps N} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, te_lin, te_rows2, Fin.forall_fin_two,
      ite_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false, neg_mul,
      Finset.sum_neg_distrib, abs_le]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
  rw [hs1]
  rw [hs2] at h1
  refine h1.trans (add_le_add ?_ le_rfl)
  have hmeas : Measurable fun x : Fin (k * 2 ^ k) → ℝ => ∑ p, r p * x p :=
    Finset.measurable_sum _ fun p _ => (measurable_pi_apply p).const_mul _
  have hC : gg_C k = gg_cov (gg_A k) := funext fun p => funext fun q => (gg_cov_A k p q).symm
  rw [measureReal_def, ← Measure.map_apply hmeas (measurableSet_le (by fun_prop) measurable_const),
    gg_G, gg_law_functional, ← hC, ← measureReal_def]
  refine (te_gauss_slab hr _).trans ?_
  have hε := ps_eps_pos N
  gcongr
  exact (abs_add_le _ _).trans (by rw [abs_of_pos hε])

end

end Census
end IIT
