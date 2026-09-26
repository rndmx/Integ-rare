/-
Census pair step, part 5: the central limit theorem and the pair-step bound.

Fix `L`.  For `N = 2L + n` the parameters are arranged in `2^n` iid superblocks (`Ψ`,
`omM`).  The rescaled statistics `Vloc` of the superblocks other than the one of `s` are
independent, centred, with covariances summing to the diagonal `Cmat` and fourth moments
summing to `0` (`(9/10)^n`), so the multivariate Lyapunov CLT (`CLTProof`) applies.  The local
boxes `Ek` of the superblock of `s` are independent of these statistics and of each other,
each of probability `qE = 10^{-10}`; the superblock of `s` itself only shifts the
statistics by `o(σ)` (Markov).  Hence

  `limsup_N vol(allBad N L (s N)) ≤ (1 - qE · gBox)^L`.
-/
import IIT.Census.CLTProof
import IIT.Census.PairGauss

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

/-- **Proved in `CLTProof.lean`.** Multivariate central limit theorem for triangular arrays of
independent, centred random vectors under Lyapunov's condition (fourth moments), in portmanteau
form for closed sets. References: Billingsley, *Probability and Measure*, Thm 27.3 and Thm 29.4
(Cramér–Wold); van der Vaart, *Asymptotic Statistics*, Prop. 2.27; portmanteau: Billingsley,
*Convergence of Probability Measures*, Thm 2.1. -/
theorem clt_lyapunov_closed {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, MeasureTheory.Measure (Ω n))
    [∀ n, MeasureTheory.IsProbabilityMeasure (P n)] (m : ℕ → ℕ)
    (X : ∀ n, Fin (m n) → Ω n → EuclideanSpace ℝ ι) (C : Matrix ι ι ℝ)
    (hmeas : ∀ n j, Measurable (X n j)) (hind : ∀ n, ProbabilityTheory.iIndepFun (X n) (P n))
    (hint : ∀ n j, MeasureTheory.Integrable (fun ω => ‖X n j ω‖ ^ 4) (P n))
    (hmean : ∀ n j, ∫ ω, X n j ω ∂P n = 0)
    (hcov : ∀ a b : ι, Filter.Tendsto (fun n => ∑ j, ∫ ω, X n j ω a * X n j ω b ∂P n) Filter.atTop (nhds (C a b)))
    (hlyap : Filter.Tendsto (fun n => ∑ j, ∫ ω, ‖X n j ω‖ ^ 4 ∂P n) Filter.atTop (nhds 0))
    (F : Set (EuclideanSpace ℝ ι)) (hF : IsClosed F) :
    Filter.limsup (fun n => P n {ω | ∑ j, X n j ω ∈ F}) Filter.atTop ≤ ProbabilityTheory.multivariateGaussian 0 C F :=
  clt_lyapunov_closed_thm P m X C hmeas hind hint hmean hcov hlyap F hF

noncomputable section

variable {L n : ℕ}

/-! ### Normalisation and the summands -/

/-- The normalising variance `σ² = 2^n 3^{-R} 4^L`. -/
def sig2 (L n : ℕ) : ℝ := 2 ^ n * (1 / 3) ^ R L n * 4 ^ L

/-- The normalisation `σ`. -/
def sig (L n : ℕ) : ℝ := Real.sqrt (sig2 L n)

lemma sig2_pos : 0 < sig2 L n := by unfold sig2; positivity

lemma sig_pos : 0 < sig L n := Real.sqrt_pos.mpr sig2_pos

lemma sig_mul_self : sig L n * sig L n = sig2 L n := Real.mul_self_sqrt sig2_pos.le

/-- Rescaled statistic vector of one superblock. -/
def Vloc (z : Loc L n) : EuclideanSpace ℝ (Ix L) := WithLp.toLp 2 fun a => Tst z a / sig L n

lemma Vloc_apply (z : Loc L n) (a : Ix L) : Vloc z a = Tst z a / sig L n := rfl

@[fun_prop]
lemma measurable_Vloc : Measurable (Vloc (L := L) (n := n)) := by unfold Vloc; fun_prop

/-- Enumeration of the superblocks. -/
def eO (n : ℕ) : Fin (Fintype.card (Outer n)) ≃ Outer n := (Fintype.equivFin _).symm

/-- Summand of superblock `w`: `Vloc`, except `0` on the superblock `w₀` of `s`. -/
def Gw (w₀ w : Outer n) (z : Loc L n) : EuclideanSpace ℝ (Ix L) := if w = w₀ then 0 else Vloc z

/-- The triangular array of the CLT. -/
def Xs (w₀ : Outer n) (j : Fin (Fintype.card (Outer n))) (ω : Om L n) :
    EuclideanSpace ℝ (Ix L) := Gw w₀ (eO n j) (ω (eO n j))

@[fun_prop]
lemma measurable_Gw (w₀ w : Outer n) : Measurable (Gw (L := L) w₀ w) := by
  unfold Gw; split_ifs
  · exact measurable_const
  · exact measurable_Vloc

lemma measurable_Xs (w₀ : Outer n) (j : Fin (Fintype.card (Outer n))) :
    Measurable (Xs (L := L) w₀ j) := (measurable_Gw _ _).comp (measurable_pi_apply _)

lemma iIndepFun_Xs (w₀ : Outer n) : iIndepFun (Xs (L := L) w₀) (omM L n) := by
  have h := iIndepFun_pi (μ := fun _ : Outer n => locM L n) (X := fun w => Gw (L := L) w₀ w)
    (fun w => (measurable_Gw w₀ w).aemeasurable)
  exact (iIndepFun_precomp_of_bijective (eO n).bijective).mpr h

lemma integral_eval_omM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (w : Outer n)
    {g : Loc L n → E} (hg : AEStronglyMeasurable g (locM L n)) :
    ∫ ω, g (ω w) ∂omM L n = ∫ z, g z ∂locM L n := by
  have hmp := measurePreserving_eval (fun _ : Outer n => locM L n) w
  rw [← hmp.map_eq] at hg ⊢
  exact (integral_map (measurable_pi_apply w).aemeasurable hg).symm

/-! ### Bounds -/

lemma Sm_le (z : Loc L n) : Sm z ≤ 4 ^ L := by
  calc Sm z ≤ ∑ _π : Pb L, (1 : ℝ) := Finset.sum_le_sum fun π _ => rowP_le_one z π
    _ = 4 ^ L := by simp

lemma norm_Vloc_sq (z : Loc L n) : ‖Vloc z‖ ^ 2 = ∑ a, Tst z a ^ 2 / sig2 L n := by
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Vloc_apply, div_pow, sq (sig L n), sig_mul_self]

lemma norm_Vloc_sq_le (z : Loc L n) :
    ‖Vloc z‖ ^ 2 ≤ Fintype.card (Ix L) * 64 / sig2 L n * Sm z ^ 2 := by
  rw [norm_Vloc_sq]
  calc ∑ a, Tst z a ^ 2 / sig2 L n ≤ ∑ _a : Ix L, 64 * Sm z ^ 2 / sig2 L n := by
        refine Finset.sum_le_sum fun a _ => div_le_div_of_nonneg_right ?_ sig2_pos.le
        have h := abs_Tst_le z a
        have h0 := abs_nonneg (Tst z a)
        rw [← sq_abs]
        nlinarith
    _ = _ := by simp; ring

lemma norm_Vloc_pow4_le (z : Loc L n) :
    ‖Vloc z‖ ^ 4 ≤ (Fintype.card (Ix L) * 64 / sig2 L n) ^ 2 * Sm z ^ 4 := by
  have h := norm_Vloc_sq_le z
  have h0 : 0 ≤ ‖Vloc z‖ ^ 2 := by positivity
  calc ‖Vloc z‖ ^ 4 = (‖Vloc z‖ ^ 2) ^ 2 := by ring
    _ ≤ (Fintype.card (Ix L) * 64 / sig2 L n * Sm z ^ 2) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = _ := by ring

/-- A uniform bound on `‖Vloc‖²`. -/
def vB (L n : ℕ) : ℝ := Fintype.card (Ix L) * 64 / sig2 L n * (4 ^ L) ^ 2

lemma norm_Vloc_sq_le' (z : Loc L n) : ‖Vloc z‖ ^ 2 ≤ vB L n := by
  refine (norm_Vloc_sq_le z).trans ?_
  unfold vB
  have : 0 ≤ Fintype.card (Ix L) * 64 / sig2 L n := by have := sig2_pos (L := L) (n := n); positivity
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Sm_nonneg z) (Sm_le z) 2) this

lemma norm_Gw_sq_le (w₀ w : Outer n) (z : Loc L n) : ‖Gw w₀ w z‖ ^ 2 ≤ vB L n := by
  unfold Gw; split_ifs
  · rw [norm_zero, zero_pow two_ne_zero]; unfold vB; have := sig2_pos (L := L) (n := n)
    positivity
  · exact norm_Vloc_sq_le' z

lemma norm_le_of_sq_le {x B : ℝ} (hx : 0 ≤ x) (h : x ^ 2 ≤ B) : x ≤ B + 1 := by
  nlinarith

lemma integrable_Vloc : Integrable (Vloc (L := L) (n := n)) (locM L n) :=
  Integrable.of_bound measurable_Vloc.aestronglyMeasurable (vB L n + 1)
    (ae_of_all _ fun z => norm_le_of_sq_le (norm_nonneg _) (norm_Vloc_sq_le' z))

lemma integrable_Xs_pow4 (w₀ : Outer n) (j : Fin (Fintype.card (Outer n))) :
    Integrable (fun ω => ‖Xs (L := L) w₀ j ω‖ ^ 4) (omM L n) :=
  Integrable.of_bound (by have := measurable_Xs (L := L) w₀ j; fun_prop) (vB L n ^ 2)
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 4)]
      have h := norm_Gw_sq_le (L := L) w₀ (eO n j) (ω (eO n j))
      have h0 : 0 ≤ ‖Xs w₀ j ω‖ ^ 2 := by positivity
      calc ‖Xs w₀ j ω‖ ^ 4 = (‖Xs w₀ j ω‖ ^ 2) ^ 2 := by ring
        _ ≤ vB L n ^ 2 := pow_le_pow_left₀ h0 h 2)

/-! ### Mean zero -/

lemma integral_Vloc : ∫ z, Vloc z ∂locM L n = (0 : EuclideanSpace ℝ (Ix L)) := by
  ext a
  have h := (EuclideanSpace.proj a : EuclideanSpace ℝ (Ix L) →L[ℝ] ℝ).integral_comp_comm
    (integrable_Vloc (L := L) (n := n))
  simp only [EuclideanSpace.coe_proj] at h
  rw [← h]
  simp only [Vloc_apply]
  rw [integral_div, integral_Tst]
  simp

lemma integral_Xs (w₀ : Outer n) (j : Fin (Fintype.card (Outer n))) :
    ∫ ω, Xs (L := L) w₀ j ω ∂omM L n = 0 := by
  unfold Xs
  rw [integral_eval_omM (eO n j) (measurable_Gw w₀ _).aestronglyMeasurable]
  unfold Gw
  split_ifs
  · simp
  · exact integral_Vloc

/-! ### Covariances -/

/-- `σ²` as a geometric sequence in `n`. -/
def c1 (L : ℕ) : ℝ := 4 ^ L * (1 / 3) ^ (2 * L)

lemma c1_pos : 0 < c1 L := by unfold c1; positivity

lemma sig2_eq : sig2 L n = c1 L * (2 / 3) ^ n := by
  unfold sig2 c1
  rw [R_eq, pow_add, show (2 / 3 : ℝ) ^ n = 2 ^ n * (1 / 3) ^ n by rw [← mul_pow]; norm_num]
  ring

lemma pow_R (x : ℝ) : x ^ R L n = x ^ (2 * L) * x ^ n := by rw [R_eq, pow_add]

lemma sum_eO_ite (w₀ : Outer n) (c : ℝ) :
    ∑ j, (if eO n j = w₀ then (0 : ℝ) else c) = (2 ^ n - 1) * c := by
  rw [(eO n).sum_comp (fun w => if w = w₀ then (0 : ℝ) else c)]
  have : ∀ w : Outer n, (if w = w₀ then (0 : ℝ) else c) = c - (if w = w₀ then c else 0) := by
    intro w; split_ifs <;> ring
  simp_rw [this, Finset.sum_sub_distrib]
  simp [Finset.sum_const]
  ring

lemma integral_Xs_mul (w₀ : Outer n) (j : Fin (Fintype.card (Outer n))) (a b : Ix L) :
    ∫ ω, Xs (L := L) w₀ j ω a * Xs w₀ j ω b ∂omM L n =
      if eO n j = w₀ then 0 else (∫ z, Tst z a * Tst z b ∂locM L n) / sig2 L n := by
  unfold Xs
  rw [integral_eval_omM (eO n j) (g := fun z => Gw (L := L) w₀ (eO n j) z a * Gw w₀ (eO n j) z b)
    (by have := measurable_Gw (L := L) w₀ (eO n j); fun_prop)]
  unfold Gw
  split_ifs
  · simp
  · simp only [Vloc_apply]
    rw [← integral_div]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only
    rw [← sig_mul_self]
    have := sig_pos (L := L) (n := n)
    field_simp

lemma cov_sum (w₀ : Outer n) (a b : Ix L) :
    ∑ j, ∫ ω, Xs (L := L) w₀ j ω a * Xs w₀ j ω b ∂omM L n =
      (1 - (1 / 2) ^ n) * dd a b + (2 ^ n - 1) / sig2 L n * Off (n := n) a b := by
  simp_rw [integral_Xs_mul]
  rw [sum_eO_ite, integral_TT]
  unfold sig2
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have h3 : ((1 : ℝ) / 2) ^ n = 1 / 2 ^ n := one_div_pow 2 n
  rw [h3]
  field_simp

lemma abs_off_term (a b : Ix L) :
    |(2 ^ n - 1) / sig2 L n * Off (n := n) a b| ≤
      (16 ^ L * 64 * (1 / 4) ^ (2 * L) / c1 L) * (3 / 4) ^ n := by
  rw [abs_mul]
  have hs := sig2_pos (L := L) (n := n)
  have h1 : |(2 ^ n - 1) / sig2 L n| ≤ 2 ^ n / sig2 L n := by
    rw [abs_div, abs_of_pos hs]
    refine div_le_div_of_nonneg_right ?_ hs.le
    rw [abs_le]; constructor <;> nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (by norm_num) (n := n)]
  calc |(2 ^ n - 1) / sig2 L n| * |Off (n := n) a b|
      ≤ 2 ^ n / sig2 L n * (16 ^ L * (64 * (1 / 4) ^ R L n)) :=
        mul_le_mul h1 (abs_Off_le a b) (abs_nonneg _) (by positivity)
    _ = _ := by
        rw [sig2_eq, pow_R,
          show (3 / 4 : ℝ) ^ n = 2 ^ n * (1 / 4) ^ n / (2 / 3) ^ n by
            rw [← mul_pow, ← div_pow]; norm_num]
        have := c1_pos (L := L)
        field_simp

lemma tendsto_cov_sum (w₀ : ∀ n, Outer n) (a b : Ix L) :
    Tendsto (fun n => ∑ j, ∫ ω, Xs (L := L) (w₀ n) j ω a * Xs (w₀ n) j ω b ∂omM L n) atTop
      (𝓝 (Cmat L a b)) := by
  simp_rw [cov_sum]
  have hC : Cmat L a b = (1 - 0) * dd a b + 0 := by
    simp [Cmat, dd, Matrix.diagonal_apply]
  rw [hC]
  refine ((tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))).mul tendsto_const_nhds).add ?_
  have hlim : Tendsto (fun n : ℕ => (16 ^ L * 64 * (1 / 4) ^ (2 * L) / c1 L) * (3 / 4 : ℝ) ^ n)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num)).const_mul (16 ^ L * 64 * (1 / 4) ^ (2 * L) / c1 L)
  exact squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact abs_off_term a b) hlim

/-! ### Lyapunov -/

lemma measurable_norm_Gw_pow (w₀ w : Outer n) :
    Measurable fun z => ‖Gw (L := L) w₀ w z‖ ^ 4 := by
  have := measurable_Gw (L := L) w₀ w; fun_prop

lemma integral_norm_Gw_pow4_le (w₀ w : Outer n) :
    ∫ z, ‖Gw (L := L) w₀ w z‖ ^ 4 ∂locM L n ≤
      (Fintype.card (Ix L) * 64 / sig2 L n) ^ 2 * ((4 ^ L) ^ 4 * (1 / 5) ^ R L n) := by
  have hint : Integrable (fun z => ‖Gw (L := L) w₀ w z‖ ^ 4) (locM L n) :=
    Integrable.of_bound (by have := measurable_Gw (L := L) w₀ w; fun_prop) (vB L n ^ 2)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 4)]
        have h := norm_Gw_sq_le (L := L) w₀ w z
        have h0 : 0 ≤ ‖Gw w₀ w z‖ ^ 2 := by positivity
        calc ‖Gw w₀ w z‖ ^ 4 = (‖Gw w₀ w z‖ ^ 2) ^ 2 := by ring
          _ ≤ vB L n ^ 2 := pow_le_pow_left₀ h0 h 2)
  calc ∫ z, ‖Gw (L := L) w₀ w z‖ ^ 4 ∂locM L n
      ≤ ∫ z, (Fintype.card (Ix L) * 64 / sig2 L n) ^ 2 * Sm z ^ 4 ∂locM L n := by
        refine integral_mono hint ((integrable_Sm_pow 4).const_mul _) fun z => ?_
        unfold Gw; split_ifs
        · rw [norm_zero, zero_pow (by norm_num)]; have := Sm_nonneg z; positivity
        · exact norm_Vloc_pow4_le z
    _ ≤ _ := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left integral_Sm_pow4_le (by positivity)

lemma lyap_sum_le (w₀ : Outer n) :
    ∑ j, ∫ ω, ‖Xs (L := L) w₀ j ω‖ ^ 4 ∂omM L n ≤
      2 ^ n * ((Fintype.card (Ix L) * 64 / sig2 L n) ^ 2 * ((4 ^ L) ^ 4 * (1 / 5) ^ R L n)) := by
  calc ∑ j, ∫ ω, ‖Xs (L := L) w₀ j ω‖ ^ 4 ∂omM L n
      ≤ ∑ _j : Fin (Fintype.card (Outer n)),
          (Fintype.card (Ix L) * 64 / sig2 L n) ^ 2 * ((4 ^ L) ^ 4 * (1 / 5) ^ R L n) := by
        refine Finset.sum_le_sum fun j _ => ?_
        unfold Xs
        rw [integral_eval_omM (eO n j) (g := fun z => ‖Gw (L := L) w₀ (eO n j) z‖ ^ 4)
          (measurable_norm_Gw_pow w₀ (eO n j)).aestronglyMeasurable]
        exact integral_norm_Gw_pow4_le w₀ _
    _ = _ := by simp [Finset.sum_const]

lemma lyap_bound_eq :
    2 ^ n * ((Fintype.card (Ix L) * 64 / sig2 L n) ^ 2 * ((4 ^ L) ^ 4 * (1 / 5) ^ R L n)) =
      ((Fintype.card (Ix L) * 64) ^ 2 * (4 ^ L) ^ 4 * (1 / 5) ^ (2 * L) / c1 L ^ 2) *
        (9 / 10) ^ n := by
  rw [sig2_eq, pow_R, show (9 / 10 : ℝ) ^ n = 2 ^ n * (1 / 5) ^ n / ((2 / 3) ^ n * (2 / 3) ^ n) by
    rw [← mul_pow, ← mul_pow, ← div_pow]; norm_num]
  have := c1_pos (L := L)
  field_simp

lemma tendsto_lyap (w₀ : ∀ n, Outer n) :
    Tendsto (fun n => ∑ j, ∫ ω, ‖Xs (L := L) (w₀ n) j ω‖ ^ 4 ∂omM L n) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => Finset.sum_nonneg fun j _ =>
    integral_nonneg fun ω => pow_nonneg (norm_nonneg _) 4) (fun n => (lyap_sum_le (w₀ n)).trans
      lyap_bound_eq.le) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 9 / 10)
    (by norm_num)).const_mul ((Fintype.card (Ix L) * 64) ^ 2 * (4 ^ L) ^ 4 * (1 / 5) ^ (2 * L) /
      c1 L ^ 2)

/-! ### The events -/

/-- The sum of the array: rescaled statistics of all superblocks but the one of `s`. -/
def Vp (w₀ : Outer n) (ω : Om L n) : EuclideanSpace ℝ (Ix L) := ∑ j, Xs (L := L) w₀ j ω

lemma Vp_eq (w₀ : Outer n) (ω : Om L n) :
    Vp w₀ ω = ∑ i : (univ.erase w₀ : Finset (Outer n)), Gw (L := L) w₀ i.1 (ω i.1) := by
  unfold Vp Xs
  rw [(eO n).sum_comp (fun w => Gw (L := L) w₀ w (ω w)),
    ← Finset.add_sum_erase univ (fun w => Gw (L := L) w₀ w (ω w)) (mem_univ w₀)]
  have h0 : Gw (L := L) w₀ w₀ (ω w₀) = 0 := by simp [Gw]
  rw [h0, zero_add]
  exact (Finset.sum_coe_sort (univ.erase w₀) (fun w => Gw (L := L) w₀ w (ω w))).symm

lemma Vp_apply (w₀ : Outer n) (ω : Om L n) (a : Ix L) :
    Vp w₀ ω a = ∑ w ∈ univ.erase w₀, Tst (ω w) a / sig L n := by
  rw [Vp_eq, Finset.sum_coe_sort (univ.erase w₀) (fun w => Gw (L := L) w₀ w (ω w)),
    WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun w hw => ?_
  simp only [Gw, if_neg (Finset.ne_of_mem_erase hw)]
  rfl

lemma Tfull_split (w₀ : Outer n) (ω : Om L n) (a : Ix L) :
    Tfull ω a = sig L n * Vp w₀ ω a + Tst (ω w₀) a := by
  rw [Vp_apply, Finset.mul_sum, Tfull,
    ← Finset.add_sum_erase univ (fun w => Tst (ω w) a) (mem_univ w₀), add_comm]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have := sig_pos (L := L) (n := n)
  field_simp

/-- Pattern of the local boxes. -/
def PatSet (π₀ : Pb L) (A : Finset (Fin L)) : Set (Loc L n) := {ζ | ∀ k, (Ek π₀ k ζ ↔ k ∈ A)}

/-- The superblock of `s` is heavy. -/
def B2 (w₀ : Outer n) : Set (Om L n) := {ω | sig L n / 32 ≤ Sm (ω w₀)}

lemma BadΩ_sub (π₀ : Pb L) (w₀ : Outer n) :
    BadΩ π₀ w₀ ⊆ (⋃ A : Finset (Fin L), {ω : Om L n | ω w₀ ∈ PatSet π₀ A} ∩
      {ω | Vp w₀ ω ∈ FA A}) ∪ B2 w₀ := by
  classical
  intro ω hω
  by_cases hB : ω ∈ B2 w₀
  · exact Or.inr hB
  left
  simp only [B2, Set.mem_setOf_eq, not_le] at hB
  refine Set.mem_iUnion.mpr ⟨univ.filter (fun k => Ek π₀ k (ω w₀)), ?_, ?_⟩
  · intro k; simp
  · intro k hk hgood
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    refine hω k ⟨hk, fun c => ?_⟩
    obtain ⟨h1, h2⟩ := hgood c
    have hs := sig_pos (L := L) (n := n)
    have ht0 := abs_Tst_le (ω w₀) (k, 0, c)
    have ht1 := abs_Tst_le (ω w₀) (k, 1, c)
    rw [Tfull_split w₀ ω, Tfull_split w₀ ω]
    obtain ⟨a0, b0⟩ := abs_le.mp ht0
    obtain ⟨a1, b1⟩ := abs_le.mp ht1
    obtain ⟨c1, d1⟩ := abs_lt.mp h2
    rw [abs_lt]
    constructor <;> nlinarith

/-! ### Independence of the superblock of `s` from the others -/

lemma iIndepFun_coord : iIndepFun (fun w (ω : Om L n) => ω w) (omM L n) := by
  have := iIndepFun_pi (μ := fun _ : Outer n => locM L n) (X := fun _ => id)
    (fun _ => aemeasurable_id)
  exact this

lemma indep_w₀_Vp (w₀ : Outer n) :
    IndepFun (fun ω : Om L n => ω w₀) (Vp (L := L) w₀) (omM L n) := by
  have h2 := (iIndepFun_coord (L := L) (n := n)).indepFun_finset {w₀} (univ.erase w₀)
    (Finset.disjoint_singleton_left.mpr (Finset.notMem_erase w₀ univ))
    (fun w => measurable_pi_apply w)
  have hφ : (fun ω : Om L n => ω w₀) =
      (fun y : (↥({w₀} : Finset (Outer n)) → Loc L n) => y ⟨w₀, Finset.mem_singleton_self w₀⟩) ∘
        (fun ω (i : ({w₀} : Finset (Outer n))) => ω i) := rfl
  have hψ : Vp (L := L) w₀ =
      (fun y : (↥(univ.erase w₀ : Finset (Outer n)) → Loc L n) =>
        ∑ i : (univ.erase w₀ : Finset (Outer n)), Gw (L := L) w₀ i.1 (y i)) ∘
        (fun ω (i : (univ.erase w₀ : Finset (Outer n))) => ω i) := by
    funext ω; exact Vp_eq w₀ ω
  rw [hφ, hψ]
  exact h2.comp (measurable_pi_apply _)
    (Finset.measurable_sum _ fun i _ => (measurable_Gw _ _).comp (measurable_pi_apply i))

/-! ### Measurability -/

lemma measurableSet_Jt (π₀ : Pb L) (k : Fin L) (q : Qt) : MeasurableSet (Jt π₀ k q) := by
  unfold Jt Jb; split_ifs <;> exact measurableSet_Ioo

lemma measurableSet_Ek (π₀ : Pb L) (k : Fin L) : MeasurableSet {ζ : Loc L n | Ek π₀ k ζ} := by
  have : {ζ : Loc L n | Ek π₀ k ζ} = ⋂ q, (fun ζ : Loc L n => ζ (cpt π₀ k q)) ⁻¹' Jt π₀ k q := by
    ext; simp [Ek]
  rw [this]
  exact MeasurableSet.iInter fun q => measurable_pi_apply _ (measurableSet_Jt π₀ k q)

lemma measurableSet_PatSet (π₀ : Pb L) (A : Finset (Fin L)) :
    MeasurableSet (PatSet (n := n) π₀ A) := by
  have : PatSet (n := n) π₀ A = ⋂ k, (if k ∈ A then {ζ | Ek π₀ k ζ} else {ζ | Ek π₀ k ζ}ᶜ) := by
    ext ζ
    simp only [PatSet, Set.mem_setOf_eq, Set.mem_iInter]
    refine forall_congr' fun k => ?_
    by_cases hk : k ∈ A <;> simp [hk]
  rw [this]
  exact MeasurableSet.iInter fun k => by
    split_ifs
    · exact measurableSet_Ek π₀ k
    · exact (measurableSet_Ek π₀ k).compl

/-! ### The pattern probabilities -/

/-- The local box coordinates, by pair. -/
def Yb (π₀ : Pb L) (ζ : Loc L n) : Fin L → Qt → ℝ := fun k q => ζ (cpt π₀ k q)

lemma mp_Yb (π₀ : Pb L) : MeasurePreserving (Yb (n := n) π₀) (locM L n)
    (Measure.pi fun _ : Fin L => Measure.pi fun _ : Qt => unif) := by
  have hg : Function.Injective fun p : Fin L × Qt => cpt (n := n) π₀ p.1 p.2 := by
    rintro ⟨k, q⟩ ⟨l, q'⟩ h
    obtain ⟨rfl, rfl⟩ := (cpt_eq_iff π₀ k l q q').mp h
    rfl
  have h1 := map_comp_inj _ hg unif
  have h2 := Measure.infinitePi_map_curry (X := ℝ) (fun (_ : Fin L) (_ : Qt) => unif)
  simp only [Measure.infinitePi_eq_pi] at h2
  refine ⟨?_, ?_⟩
  · exact Measurable.of_eval fun k => Measurable.of_eval fun q => measurable_pi_apply _
  · have : Yb (n := n) π₀ = (MeasurableEquiv.curry (Fin L) Qt ℝ) ∘
        (fun ζ : Loc L n => fun p : Fin L × Qt => ζ (cpt π₀ p.1 p.2)) := rfl
    have hf : Measurable (fun ζ : Loc L n => fun p : Fin L × Qt => ζ (cpt π₀ p.1 p.2)) :=
      Measurable.of_eval fun p => measurable_pi_apply _
    rw [this, ← Measure.map_map (MeasurableEquiv.measurable _) hf, locM, h1, h2]

/-- Probability of one local box: `(1/100)^2 (1/10)^6`. -/
def qE : ENNReal := ENNReal.ofReal ((1 / 100) ^ 2 * (1 / 10) ^ 6)

lemma unif_Ioo {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) : unif (Set.Ioo a b) = ENNReal.ofReal (b - a) := by
  unfold unif
  rw [Measure.restrict_apply measurableSet_Ioo,
    Set.inter_eq_left.mpr (Set.Ioo_subset_Icc_self.trans (Set.Icc_subset_Icc ha hb)),
    Real.volume_Ioo]

lemma unif_Jt (π₀ : Pb L) (k : Fin L) (q : Qt) :
    unif (Jt π₀ k q) = ENNReal.ofReal (if q.1 = π₀ k then 1 / 100 else 1 / 10) := by
  unfold Jt Jb
  split_ifs <;> rw [unif_Ioo] <;> norm_num

/-- The local box of pair `k`. -/
def BoxQ (π₀ : Pb L) (k : Fin L) : Set (Qt → ℝ) := Set.univ.pi (Jt π₀ k)

lemma measurableSet_BoxQ (π₀ : Pb L) (k : Fin L) : MeasurableSet (BoxQ π₀ k) :=
  MeasurableSet.univ_pi fun q => measurableSet_Jt π₀ k q

lemma prod_len (v : PS) :
    ∏ q : Qt, (if q.1 = v then (1 : ℝ) / 100 else 1 / 10) = (1 / 100) ^ 2 * (1 / 10) ^ 6 := by
  rw [Fintype.prod_prod_type]
  have h : ∀ u : PS, ∏ _e : Fin 2, (if u = v then (1 : ℝ) / 100 else 1 / 10) =
      if u = v then (1 / 100) ^ 2 else (1 / 10) ^ 2 := by
    intro u; split_ifs <;> simp
  simp_rw [h]
  rw [Fintype.prod_eq_mul_prod_compl v, if_pos rfl,
    Finset.prod_congr rfl (fun u hu => if_neg (by simpa using hu)), Finset.prod_const,
    Finset.card_compl]
  simp
  norm_num

lemma measure_BoxQ (π₀ : Pb L) (k : Fin L) :
    (Measure.pi fun _ : Qt => unif) (BoxQ π₀ k) = qE := by
  rw [BoxQ, Measure.pi_pi]
  simp_rw [unif_Jt]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun q _ => by split_ifs <;> norm_num), prod_len]
  rfl

lemma qE_le_one : qE ≤ 1 := by
  unfold qE; rw [ENNReal.ofReal_le_one]; norm_num

lemma locM_PatSet (π₀ : Pb L) (A : Finset (Fin L)) :
    locM L n (PatSet π₀ A) = qE ^ A.card * (1 - qE) ^ (L - A.card) := by
  have hpre : PatSet (n := n) π₀ A = Yb π₀ ⁻¹'
      Set.univ.pi (fun k => if k ∈ A then BoxQ π₀ k else (BoxQ π₀ k)ᶜ) := by
    ext ζ
    simp only [PatSet, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi, Ek, BoxQ]
    refine forall_congr' fun k => ?_
    by_cases hk : k ∈ A <;> simp [hk] <;> exact Iff.rfl
  rw [hpre, (mp_Yb π₀).measure_preimage (MeasurableSet.univ_pi fun k => by
    split_ifs
    · exact measurableSet_BoxQ π₀ k
    · exact (measurableSet_BoxQ π₀ k).compl).nullMeasurableSet, Measure.pi_pi]
  have : ∀ k, (Measure.pi fun _ : Qt => unif) (if k ∈ A then BoxQ π₀ k else (BoxQ π₀ k)ᶜ) =
      if k ∈ A then qE else 1 - qE := by
    intro k
    split_ifs
    · exact measure_BoxQ π₀ k
    · rw [prob_compl_eq_one_sub (measurableSet_BoxQ π₀ k), measure_BoxQ]
  simp_rw [this]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  · congr 1; ext k; simp
  · rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
    simp

lemma omM_inter (π₀ : Pb L) (w₀ : Outer n) (A : Finset (Fin L)) :
    omM L n ({ω : Om L n | ω w₀ ∈ PatSet π₀ A} ∩ {ω | Vp w₀ ω ∈ FA A}) =
      qE ^ A.card * (1 - qE) ^ (L - A.card) * omM L n {ω | Vp w₀ ω ∈ FA A} := by
  have h := (indep_w₀_Vp (L := L) w₀).measure_inter_preimage_eq_mul (PatSet π₀ A) (FA A)
    (measurableSet_PatSet π₀ A) (isClosed_FA A).measurableSet
  change omM L n ((fun ω : Om L n => ω w₀) ⁻¹' PatSet π₀ A ∩ Vp w₀ ⁻¹' FA A) = _
  rw [h, ← locM_PatSet π₀ A]
  congr 1
  exact (measurePreserving_eval (fun _ : Outer n => locM L n) w₀).measure_preimage
    (measurableSet_PatSet π₀ A).nullMeasurableSet

/-! ### The heavy superblock (Markov) -/

/-- Constant of the Markov bound. -/
def c2 (L : ℕ) : ℝ := 1024 * (4 ^ L) ^ 2 * (1 / 3) ^ (2 * L) / c1 L

lemma omM_B2_le (w₀ : Outer n) : omM L n (B2 w₀) ≤ ENNReal.ofReal (c2 L * (1 / 2) ^ n) := by
  have hs := sig_pos (L := L) (n := n)
  have hmeas : MeasurableSet {z : Loc L n | (sig L n / 32) ^ 2 ≤ Sm z ^ 2} :=
    measurableSet_le measurable_const (measurable_Sm.pow_const 2)
  calc omM L n (B2 w₀) ≤ omM L n ((fun ω : Om L n => ω w₀) ⁻¹'
        {z : Loc L n | (sig L n / 32) ^ 2 ≤ Sm z ^ 2}) := by
        refine measure_mono fun ω hω => ?_
        simp only [B2, Set.mem_setOf_eq] at hω
        exact pow_le_pow_left₀ (by positivity) hω 2
    _ = locM L n {z : Loc L n | (sig L n / 32) ^ 2 ≤ Sm z ^ 2} :=
        (measurePreserving_eval (fun _ : Outer n => locM L n) w₀).measure_preimage
          hmeas.nullMeasurableSet
    _ = ENNReal.ofReal ((locM L n).real {z : Loc L n | (sig L n / 32) ^ 2 ≤ Sm z ^ 2}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (c2 L * (1 / 2) ^ n) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hM := mul_meas_ge_le_integral_of_nonneg (μ := locM L n)
          (ae_of_all _ fun z => pow_nonneg (Sm_nonneg z) 2) (integrable_Sm_pow 2)
          ((sig L n / 32) ^ 2)
        have hI := integral_Sm_sq_le (L := L) (n := n)
        have hε : 0 < (sig L n / 32) ^ 2 := by positivity
        have hle : (locM L n).real {z : Loc L n | (sig L n / 32) ^ 2 ≤ Sm z ^ 2} ≤
            ((4 ^ L) ^ 2 * (1 / 3) ^ R L n) / (sig L n / 32) ^ 2 := by
          rw [le_div_iff₀' hε]; exact hM.trans hI
        refine hle.trans (le_of_eq ?_)
        have e1 : (sig L n / 32) ^ 2 = sig2 L n / 1024 := by
          rw [div_pow, sq (sig L n), sig_mul_self]; norm_num
        rw [e1, sig2_eq, pow_R,
          show (1 / 2 : ℝ) ^ n = (1 / 3) ^ n / (2 / 3) ^ n by rw [← div_pow]; norm_num]
        unfold c2
        have := c1_pos (L := L)
        field_simp

/-! ### The limit -/

lemma omM_BadΩ_le (π₀ : Pb L) (w₀ : Outer n) :
    omM L n (BadΩ π₀ w₀) ≤ ∑ A : Finset (Fin L), qE ^ A.card * (1 - qE) ^ (L - A.card) *
      omM L n {ω | Vp w₀ ω ∈ FA A} + ENNReal.ofReal (c2 L * (1 / 2) ^ n) := by
  calc omM L n (BadΩ π₀ w₀)
      ≤ omM L n ((⋃ A : Finset (Fin L), {ω : Om L n | ω w₀ ∈ PatSet π₀ A} ∩
          {ω | Vp w₀ ω ∈ FA A}) ∪ B2 w₀) := measure_mono (BadΩ_sub π₀ w₀)
    _ ≤ omM L n (⋃ A : Finset (Fin L), {ω : Om L n | ω w₀ ∈ PatSet π₀ A} ∩
          {ω | Vp w₀ ω ∈ FA A}) + omM L n (B2 w₀) := measure_union_le _ _
    _ ≤ (∑ A : Finset (Fin L), omM L n ({ω : Om L n | ω w₀ ∈ PatSet π₀ A} ∩
          {ω | Vp w₀ ω ∈ FA A})) + ENNReal.ofReal (c2 L * (1 / 2) ^ n) :=
        add_le_add (measure_iUnion_fintype_le _ _) (omM_B2_le w₀)
    _ = _ := by simp_rw [omM_inter]

lemma limsup_add_le_nat (u v : ℕ → ENNReal) :
    limsup (u + v) atTop ≤ limsup u atTop + limsup v atTop := by
  simp only [limsup_eq_iInf_iSup_of_nat]
  rw [ENNReal.iInf_add_iInf fun i j => ⟨max i j, add_le_add
    (biSup_mono fun k hk => (le_max_left i j).trans hk)
    (biSup_mono fun k hk => (le_max_right i j).trans hk)⟩]
  refine iInf_mono fun m => iSup₂_le fun i hi => ?_
  exact add_le_add (le_iSup₂ (f := fun i (_ : i ≥ m) => u i) i hi)
    (le_iSup₂ (f := fun i (_ : i ≥ m) => v i) i hi)

lemma qE_ne_top : qE ≠ ⊤ := ENNReal.ofReal_ne_top

lemma limsup_sum_le {ι : Type*} (s : Finset ι) (u : ι → ℕ → ENNReal) :
    limsup (fun n => ∑ i ∈ s, u i n) atTop ≤ ∑ i ∈ s, limsup (u i) atTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (limsup_add_le_nat (u a) (fun n => ∑ i ∈ s, u i n)).trans (add_le_add le_rfl ih)

lemma limsup_BadΩ (π₀ : ℕ → Pb L) (w₀ : ∀ n, Outer n) :
    limsup (fun n => omM L n (BadΩ (π₀ n) (w₀ n))) atTop ≤ (qE * (1 - gBox) + (1 - qE)) ^ L := by
  have hclt : ∀ A : Finset (Fin L), limsup (fun n => omM L n {ω | Vp (w₀ n) ω ∈ FA A}) atTop ≤
      multivariateGaussian 0 (Cmat L) (FA A) := fun A =>
    clt_lyapunov_closed (fun n => omM L n) (fun n => Fintype.card (Outer n))
      (fun n => Xs (L := L) (w₀ n)) (Cmat L) (fun n j => measurable_Xs _ _)
      (fun n => iIndepFun_Xs _) (fun n j => integrable_Xs_pow4 _ _) (fun n j => integral_Xs _ _)
      (fun a b => tendsto_cov_sum w₀ a b) (tendsto_lyap w₀) (FA A) (isClosed_FA A)
  have hB : limsup (fun n => ENNReal.ofReal (c2 L * (1 / 2) ^ n)) atTop = 0 := by
    have : Tendsto (fun n => ENNReal.ofReal (c2 L * (1 / 2) ^ n)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).const_mul (c2 L))
    exact this.limsup_eq
  calc limsup (fun n => omM L n (BadΩ (π₀ n) (w₀ n))) atTop
      ≤ limsup (fun n => (∑ A : Finset (Fin L), qE ^ A.card * (1 - qE) ^ (L - A.card) *
          omM L n {ω | Vp (w₀ n) ω ∈ FA A}) + ENNReal.ofReal (c2 L * (1 / 2) ^ n)) atTop :=
        limsup_le_limsup (Eventually.of_forall fun n => omM_BadΩ_le _ _)
    _ ≤ limsup (fun n => ∑ A : Finset (Fin L), qE ^ A.card * (1 - qE) ^ (L - A.card) *
          omM L n {ω | Vp (w₀ n) ω ∈ FA A}) atTop +
        limsup (fun n => ENNReal.ofReal (c2 L * (1 / 2) ^ n)) atTop :=
        limsup_add_le_nat _ _
    _ ≤ (∑ A : Finset (Fin L), qE ^ A.card * (1 - qE) ^ (L - A.card) *
          multivariateGaussian 0 (Cmat L) (FA A)) + 0 := by
        rw [hB]
        refine add_le_add ((limsup_sum_le _ _).trans (Finset.sum_le_sum fun A _ => ?_)) le_rfl
        rw [ENNReal.limsup_const_mul_of_ne_top (a := qE ^ A.card * (1 - qE) ^ (L - A.card))
          (ENNReal.mul_ne_top (ENNReal.pow_ne_top qE_ne_top)
          (ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)))]
        exact mul_le_mul_right (hclt A) _
    _ = ∑ A : Finset (Fin L), (qE * (1 - gBox)) ^ A.card * (1 - qE) ^ (L - A.card) := by
        rw [add_zero]
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [gauss_FA, mul_pow]; ring
    _ = (qE * (1 - gBox) + (1 - qE)) ^ L := Fin.sum_pow_mul_eq_add_pow _ _

/-- The constant `p` of the pair step. -/
def pStep : ℝ := (1 / 100) ^ 2 * (1 / 10) ^ 6 * gBox.toReal

lemma gBox_ne_top : gBox ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one

lemma pStep_pos : 0 < pStep :=
  mul_pos (by norm_num) (ENNReal.toReal_pos gBox_pos.ne' gBox_ne_top)

lemma pStep_le_one : pStep ≤ 1 := by
  have h : gBox.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  have h0 : 0 ≤ gBox.toReal := ENNReal.toReal_nonneg
  unfold pStep; nlinarith

lemma const_eq : (qE * (1 - gBox) + (1 - qE)) ^ L = ENNReal.ofReal ((1 - pStep) ^ L) := by
  have hg : gBox = ENNReal.ofReal gBox.toReal := (ENNReal.ofReal_toReal gBox_ne_top).symm
  have hg1 : gBox.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  have hg0 : 0 ≤ gBox.toReal := ENNReal.toReal_nonneg
  set gr := gBox.toReal
  set qr : ℝ := (1 / 100) ^ 2 * (1 / 10) ^ 6
  have hq0 : 0 ≤ qr := by positivity
  have hq1 : qr ≤ 1 := by norm_num [qr]
  have e1 : 1 - gBox = ENNReal.ofReal (1 - gr) := by
    rw [ENNReal.ofReal_sub _ hg0, ENNReal.ofReal_one, ← hg]
  have e2 : 1 - qE = ENNReal.ofReal (1 - qr) := by
    rw [ENNReal.ofReal_sub _ hq0, ENNReal.ofReal_one]; rfl
  have e3 : qE * (1 - gBox) + (1 - qE) = ENNReal.ofReal (1 - pStep) := by
    rw [e1, e2, qE, ← ENNReal.ofReal_mul hq0, ← ENNReal.ofReal_add (by nlinarith)
      (by linarith)]
    congr 1
    unfold pStep; ring
  rw [e3, ENNReal.ofReal_pow (by linarith [pStep_le_one])]

/-- **Pair step.** For every fixed number `L` of disjoint pairs, the probability that all of
them are bad is asymptotically at most `(1 - p)^L`, with `p > 0` independent of `L`. -/
theorem limsup_allBad (s : ∀ N, State N) : ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∀ L : ℕ,
    Filter.limsup (fun N => volume (allBad N L (s N))) Filter.atTop ≤
      ENNReal.ofReal ((1 - p) ^ L) := by
  refine ⟨pStep, pStep_pos, pStep_le_one, fun L => ?_⟩
  let π₀ : ℕ → Pb L := fun n => ((eRow L n).symm (s (2 * L + n))).1
  let w₀ : ∀ n, Outer n := fun n => ((eRow L n).symm (s (2 * L + n))).2
  let F : ℕ → ENNReal := fun n => omM L n (BadΩ (π₀ n) (w₀ n))
  have hvol : ∀ N, 2 * L ≤ N → volume (allBad N L (s N)) ≤ F (N - 2 * L) := by
    intro N hN
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hN
    rw [Nat.add_sub_cancel_left]
    have hs : s (2 * L + n) = eRow L n (π₀ n, w₀ n) := by simp [π₀, w₀]
    rw [hs]
    exact volume_allBad_le _ _
  calc Filter.limsup (fun N => volume (allBad N L (s N))) atTop
      ≤ Filter.limsup (fun N => F (N - 2 * L)) atTop :=
        limsup_le_limsup (eventually_atTop.mpr ⟨2 * L, hvol⟩)
    _ = Filter.limsup F atTop := by
        change limsSup (map (F ∘ fun N => N - 2 * L) atTop) = limsSup (map F atTop)
        rw [← Filter.map_map, Filter.map_sub_atTop_eq_nat]
    _ ≤ (qE * (1 - gBox) + (1 - qE)) ^ L := limsup_BadΩ π₀ w₀
    _ = ENNReal.ofReal ((1 - pStep) ^ L) := const_eq

end

end Census
end IIT
