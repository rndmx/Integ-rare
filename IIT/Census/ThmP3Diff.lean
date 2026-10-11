/-
Census: Lindeberg comparison for the difference fields of one or two triples.

For a base map `b : Fin d → Fin d` the difference map is `x ↦ (x p - x (b p))_p` (`tp_Dif`); for
a `k`-set, `b p` is the coordinate of the same unit at pattern `0` (`tp_base`), and for two sets it
acts within each set (`tp_baseJ`).  If `μ.map Y` is the product of `B` copies of a centred law `ν`
whose second moments are within `e2` of `C / B` (with `C = A Aᵀ`) and whose third absolute moments
are at most `e3 / B`, then for the smooth box functions of `ThmP3Box` the expectation of the box
function of the difference of `∑ Y` is within an explicit error of the expectation under the
Gaussian law of the difference of `A Z` (`tp_compare`), with smoothing width `ε_N = (99/100)^N`;
`N^p` times the error tends to `0` for every `p` (`tp_tendsto_err`).  The comparisons for one
triple with the block of `s` removed (`tp_compare_single`), for two triples with the superblock of
`s` removed (`tp_compare_rest`) and for two triples over all superblocks (`tp_compare_full`).
-/
import IIT.Census.ThmP3Box
import IIT.Census.BlocksGenJ
import IIT.Census.CertDataBase
import IIT.Census.PairSecond

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

noncomputable section

variable {d : ℕ}

/-! ### Difference maps -/

/-- The difference map `x ↦ (x p - x (b p))_p`. -/
def tp_Dif (b : Fin d → Fin d) (x : Fin d → ℝ) : Fin d → ℝ := fun p => x p - x (b p)

lemma tp_Dif_sum {B : ℕ} (b : Fin d → Fin d) (x : Fin B → Fin d → ℝ) :
    tp_Dif b (∑ β, x β) = ∑ β, tp_Dif b (x β) := by
  funext p
  simp only [tp_Dif, Finset.sum_apply, Finset.sum_sub_distrib]

lemma measurable_tp_Dif (b : Fin d → Fin d) : Measurable (tp_Dif b) := by
  unfold tp_Dif; fun_prop

lemma tp_abs_Dif_le (b : Fin d → Fin d) (x : Fin d → ℝ) :
    ∑ p, |tp_Dif b x p| ≤ (d + 1) * ∑ p, |x p| := by
  have h1 : ∑ p, |tp_Dif b x p| ≤ ∑ p, (|x p| + ∑ q, |x q|) := by
    refine sum_le_sum fun p _ => ?_
    unfold tp_Dif
    exact (abs_sub _ _).trans (add_le_add le_rfl (lind_abs_le_sum_abs x (b p)))
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  linarith

/-- The coefficient matrix of the difference of `A Z`. -/
def tp_DA {ι : Type*} (b : Fin d → Fin d) (A : Fin d → ι → ℝ) : Fin d → ι → ℝ :=
  fun p j => A p j - A (b p) j

lemma tp_cov_DA {ι : Type*} [Fintype ι] (b : Fin d → Fin d) (A : Fin d → ι → ℝ) (p q : Fin d) :
    gg_cov (tp_DA b A) p q = gg_cov A p q - gg_cov A p (b q) - gg_cov A (b p) q
      + gg_cov A (b p) (b q) := by
  simp only [gg_cov, tp_DA, ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun j _ => by ring

/-! ### The error term -/

/-- The Lindeberg error for box functions, with constants `C2` and `C3`. -/
def tp_err (C2 C3 : ℝ) (N : ℕ) : ℝ :=
  (2 * (lind_Kpsi / ps_eps N)) ^ 2 / 2 * (C2 * (3 / 4 : ℝ) ^ N) +
    (2 * (lind_Kpsi / ps_eps N)) ^ 3 / 6 * (C3 * (23 / 25 : ℝ) ^ N)

lemma tp_err_nonneg {C2 C3 : ℝ} (h2 : 0 ≤ C2) (h3 : 0 ≤ C3) (N : ℕ) : 0 ≤ tp_err C2 C3 N := by
  have := ps_eps_pos N
  have := lind_Kpsi_pos
  unfold tp_err; positivity

lemma tp_err_mono {C2 C3 C2' C3' : ℝ} (h2 : C2 ≤ C2') (h3 : C3 ≤ C3') (N : ℕ) :
    tp_err C2 C3 N ≤ tp_err C2' C3' N := by
  have := ps_eps_pos N
  have := lind_Kpsi_pos
  unfold tp_err
  gcongr

lemma tp_tendsto_pow_mul_pow (p : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (C : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ p * (C * r ^ N)) atTop (𝓝 0) := by
  have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one p (by rwa [abs_of_nonneg hr0])).const_mul C
  rw [mul_zero] at h
  refine h.congr fun N => ?_
  ring

/-- The error is `o(N^{-p})` for every `p`. -/
theorem tp_tendsto_err (C2 C3 : ℝ) (p : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ p * tp_err C2 C3 N) atTop (𝓝 0) := by
  have e : ∀ N : ℕ, (N : ℝ) ^ p * tp_err C2 C3 N =
      (N : ℝ) ^ p * (4 * lind_Kpsi ^ 2 / 2 * C2 * ((100 / 99 : ℝ) ^ 2 * (3 / 4)) ^ N) +
      (N : ℝ) ^ p * (8 * lind_Kpsi ^ 3 / 6 * C3 * ((100 / 99 : ℝ) ^ 3 * (23 / 25)) ^ N) := by
    intro N
    have e1 : ((100 / 99 : ℝ) ^ N) ^ 2 = ((100 / 99 : ℝ) ^ 2) ^ N := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    have e3 : ((100 / 99 : ℝ) ^ N) ^ 3 = ((100 / 99 : ℝ) ^ 3) ^ N := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [tp_err, ps_K_div_eps]
    simp only [mul_pow, e1, e3]
    ring
  simp_rw [e]
  rw [← add_zero (0 : ℝ)]
  exact (tp_tendsto_pow_mul_pow p (by norm_num) (by norm_num) _).add
    (tp_tendsto_pow_mul_pow p (by norm_num) (by norm_num) _)

/-! ### The generic comparison -/

section Compare

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [IsProbabilityMeasure μ] in
/-- **Lindeberg comparison for the difference of a sum of iid vectors.** -/
theorem tp_compare {B : ℕ} (hB : 0 < B) {Y : Ω → Fin B → Fin d → ℝ} (hY : Measurable Y)
    {ν : Measure (Fin d → ℝ)} [IsProbabilityMeasure ν]
    (hmap : μ.map Y = Measure.pi fun _ => ν) (hν0 : ∀ p, ∫ x, x p ∂ν = 0)
    (hν3 : Integrable (fun x => (∑ p, |x p|) ^ 3) ν) (A : Fin d → ι → ℝ) (b : Fin d → Fin d)
    {e2 e3 : ℝ} (h2 : ∀ p q, |(B : ℝ) * ∫ x, x p * x q ∂ν - gg_cov A p q| ≤ e2)
    (h3 : (B : ℝ) * ∫ x, (∑ p, |x p|) ^ 3 ∂ν ≤ e3)
    (c : Fin d → ℝ) (r : ℝ) {ε : ℝ} (hε : 0 < ε) (bb : ℝ) :
    |∫ ω, tp_boxF c r ε bb (tp_Dif b (∑ β, Y ω β)) ∂μ
        - ∫ x, tp_boxF c r ε bb x ∂(gg_law (tp_DA b A))| ≤
      (2 * (lind_Kpsi / ε)) ^ 2 / 2 * ((d : ℝ) ^ 2 * (4 * e2)) +
        (2 * (lind_Kpsi / ε)) ^ 3 / 6 * (((d : ℝ) + 1) ^ 3 * e3 +
          (∫ x, (∑ p, |x p|) ^ 3 ∂(gg_law (tp_DA b A))) / Real.sqrt B) := by
  set D := tp_Dif (d := d) b
  have hD := measurable_tp_Dif (d := d) b
  set F := tp_boxF c r ε bb
  have hF := measurable_tp_boxF c r ε bb
  set ν' := ν.map D with hν'
  set γ' := gg_sumLaw (tp_DA b A) B with hγ'
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  -- the left side as an integral over the product of `ν'`
  have hS : Measurable (fun x : Fin B → Fin d → ℝ => ∑ β, x β) :=
    Finset.measurable_sum _ fun β _ => measurable_pi_apply β
  have hpi : (Measure.pi fun _ : Fin B => ν).map (fun x β => D (x β)) =
      Measure.pi fun _ : Fin B => ν' :=
    Measure.pi_map_pi (fun _ => hD.aemeasurable)
  have hmapD : Measurable (fun x : Fin B → Fin d → ℝ => fun β => D (x β)) :=
    Measurable.of_eval fun β => hD.comp (measurable_pi_apply β)
  have hL : ∫ ω, F (D (∑ β, Y ω β)) ∂μ = ∫ x, F (∑ β, x β) ∂(Measure.pi fun _ : Fin B => ν') := by
    rw [← hpi, integral_map (f := fun x : Fin B → Fin d → ℝ => F (∑ β, x β)) hmapD.aemeasurable
      (hF.comp hS).aestronglyMeasurable]
    have e1 : ∫ ω, F (D (∑ β, Y ω β)) ∂μ = ∫ x, F (D (∑ β, x β)) ∂(μ.map Y) :=
      (integral_map (f := fun x : Fin B → Fin d → ℝ => F (D (∑ β, x β))) hY.aemeasurable
        (hF.comp (hD.comp hS)).aestronglyMeasurable).symm
    rw [e1, hmap]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [D, tp_Dif_sum]
  have hR : ∫ x, F (∑ β, x β) ∂(Measure.pi fun _ : Fin B => γ') =
      ∫ x, F x ∂(gg_law (tp_DA b A)) := gg_integral_sum_pi _ hB hF
  -- moments of `ν'`
  have hcoord : ∀ p, Integrable (fun x : Fin d → ℝ => x p) ν := lind_integrable_coord hν3
  have hmul : ∀ p q, Integrable (fun x : Fin d → ℝ => x p * x q) ν := lind_integrable_mul hν3
  have hν'0 : ∀ p, ∫ x, x p ∂ν' = 0 := by
    intro p
    rw [hν', integral_map (f := fun x : Fin d → ℝ => x p) hD.aemeasurable
      (measurable_pi_apply p).aestronglyMeasurable]
    simp only [tp_Dif]
    rw [integral_sub (hcoord p) (hcoord (b p)), hν0, hν0, sub_zero]
  have hmeas3 : Measurable (fun x : Fin d → ℝ => (∑ p, |x p|) ^ 3) := by fun_prop
  have hν'3 : Integrable (fun x => (∑ p, |x p|) ^ 3) ν' := by
    rw [hν', integrable_map_measure hmeas3.aestronglyMeasurable hD.aemeasurable]
    refine Integrable.mono' (hν3.const_mul (((d : ℝ) + 1) ^ 3)) (hmeas3.comp hD).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    simp only [Function.comp_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), ← mul_pow]
    exact pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) (tp_abs_Dif_le b x) 3
  have hsec : ∀ p q, ∫ x, x p * x q ∂ν' = ∫ x, x p * x q ∂ν - ∫ x, x p * x (b q) ∂ν
      - ∫ x, x (b p) * x q ∂ν + ∫ x, x (b p) * x (b q) ∂ν := by
    intro p q
    rw [hν', integral_map (f := fun x : Fin d → ℝ => x p * x q) hD.aemeasurable
      ((measurable_pi_apply p).mul (measurable_pi_apply q)).aestronglyMeasurable]
    simp only [tp_Dif]
    have e : (fun x : Fin d → ℝ => (x p - x (b p)) * (x q - x (b q))) =
        fun x => x p * x q - x p * x (b q) - x (b p) * x q + x (b p) * x (b q) := by
      funext x; ring
    rw [e, integral_add (f := fun x : Fin d → ℝ => x p * x q - x p * x (b q) - x (b p) * x q)
      (g := fun x => x (b p) * x (b q))
      (((hmul p q).sub (hmul p (b q))).sub (hmul (b p) q)) (hmul (b p) (b q)),
      integral_sub (f := fun x : Fin d → ℝ => x p * x q - x p * x (b q))
      (g := fun x => x (b p) * x q) ((hmul p q).sub (hmul p (b q))) (hmul (b p) q),
      integral_sub (f := fun x : Fin d → ℝ => x p * x q) (g := fun x => x p * x (b q))
      (hmul p q) (hmul p (b q))]
  have hγsec : ∀ p q, ∫ x, x p * x q ∂γ' = gg_cov (tp_DA b A) p q / B := fun p q =>
    gg_sumLaw_mul _ hB p q
  -- the Lindeberg bound
  have hlin := tp_box_pi (ν := ν') (γ := γ') hν'0 (gg_sumLaw_coord _ _) hν'3
    (gg_sumLaw_integrable_cube _ _) c r hε bb B
  rw [← hL, hR] at hlin
  refine hlin.trans ?_
  set K := 2 * (lind_Kpsi / ε) with hK
  have hK0 : 0 ≤ K := by have := lind_Kpsi_pos; positivity
  have hmis : (B : ℝ) * ∑ p, ∑ q, |∫ x, x p * x q ∂ν' - ∫ x, x p * x q ∂γ'| ≤
      (d : ℝ) ^ 2 * (4 * e2) := by
    rw [mul_sum]
    calc ∑ p, (B : ℝ) * ∑ q, |∫ x, x p * x q ∂ν' - ∫ x, x p * x q ∂γ'|
        ≤ ∑ _p : Fin d, ∑ _q : Fin d, 4 * e2 := by
          refine sum_le_sum fun p _ => ?_
          rw [mul_sum]
          refine sum_le_sum fun q _ => ?_
          rw [hsec, hγsec, tp_cov_DA, ps_mul_abs_sub_div hBr]
          have a1 := h2 p q
          have a2 := h2 p (b q)
          have a3 := h2 (b p) q
          have a4 := h2 (b p) (b q)
          have e : (B : ℝ) * (∫ x, x p * x q ∂ν - ∫ x, x p * x (b q) ∂ν
              - ∫ x, x (b p) * x q ∂ν + ∫ x, x (b p) * x (b q) ∂ν) -
              (gg_cov A p q - gg_cov A p (b q) - gg_cov A (b p) q + gg_cov A (b p) (b q)) =
              ((B : ℝ) * ∫ x, x p * x q ∂ν - gg_cov A p q)
              - ((B : ℝ) * ∫ x, x p * x (b q) ∂ν - gg_cov A p (b q))
              - ((B : ℝ) * ∫ x, x (b p) * x q ∂ν - gg_cov A (b p) q)
              + ((B : ℝ) * ∫ x, x (b p) * x (b q) ∂ν - gg_cov A (b p) (b q)) := by ring
          rw [e]
          calc _ ≤ |((B : ℝ) * ∫ x, x p * x q ∂ν - gg_cov A p q)
                - ((B : ℝ) * ∫ x, x p * x (b q) ∂ν - gg_cov A p (b q))
                - ((B : ℝ) * ∫ x, x (b p) * x q ∂ν - gg_cov A (b p) q)| +
                |(B : ℝ) * ∫ x, x (b p) * x (b q) ∂ν - gg_cov A (b p) (b q)| := abs_add_le _ _
            _ ≤ (|(B : ℝ) * ∫ x, x p * x q ∂ν - gg_cov A p q|
                + |(B : ℝ) * ∫ x, x p * x (b q) ∂ν - gg_cov A p (b q)|
                + |(B : ℝ) * ∫ x, x (b p) * x q ∂ν - gg_cov A (b p) q|) +
                |(B : ℝ) * ∫ x, x (b p) * x (b q) ∂ν - gg_cov A (b p) (b q)| := by
                  gcongr
                  exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
            _ ≤ 4 * e2 := by linarith
      _ = (d : ℝ) ^ 2 * (4 * e2) := by simp; ring
  have hthird : (B : ℝ) * (∫ x, (∑ p, |x p|) ^ 3 ∂ν' + ∫ x, (∑ p, |x p|) ^ 3 ∂γ') ≤
      ((d : ℝ) + 1) ^ 3 * e3 + (∫ x, (∑ p, |x p|) ^ 3 ∂(gg_law (tp_DA b A))) / Real.sqrt B := by
    have h1 : ∫ x, (∑ p, |x p|) ^ 3 ∂ν' ≤ ((d : ℝ) + 1) ^ 3 * ∫ x, (∑ p, |x p|) ^ 3 ∂ν := by
      rw [hν', integral_map (f := fun x : Fin d → ℝ => (∑ p, |x p|) ^ 3) hD.aemeasurable
        hmeas3.aestronglyMeasurable, ← integral_const_mul]
      refine integral_mono_of_nonneg (ae_of_all _ fun x => by positivity)
        (hν3.const_mul _) (ae_of_all _ fun x => ?_)
      simp only
      rw [← mul_pow]
      exact pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) (tp_abs_Dif_le b x) 3
    have h2' : (B : ℝ) * ∫ x, (∑ p, |x p|) ^ 3 ∂γ' =
        (∫ x, (∑ p, |x p|) ^ 3 ∂(gg_law (tp_DA b A))) / Real.sqrt B := by
      rw [hγ', gg_sumLaw_cube]
      have hs : 0 < Real.sqrt B := Real.sqrt_pos.2 hBr
      have hss : Real.sqrt B ^ 2 = B := Real.sq_sqrt hBr.le
      have h3' : Real.sqrt B ^ 3 = B * Real.sqrt B := by linear_combination Real.sqrt B * hss
      rw [h3']
      field_simp
    rw [mul_add, h2']
    have hd0 : (0 : ℝ) ≤ ((d : ℝ) + 1) ^ 3 := by positivity
    have := mul_le_mul_of_nonneg_left h1 hBr.le
    nlinarith [mul_le_mul_of_nonneg_left h3 hd0]
  have e : (B : ℝ) * (K ^ 2 / 2 * ∑ p, ∑ q, |∫ x, x p * x q ∂ν' - ∫ x, x p * x q ∂γ'| +
      K ^ 3 / 6 * (∫ x, (∑ p, |x p|) ^ 3 ∂ν' + ∫ x, (∑ p, |x p|) ^ 3 ∂γ')) =
      K ^ 2 / 2 * ((B : ℝ) * ∑ p, ∑ q, |∫ x, x p * x q ∂ν' - ∫ x, x p * x q ∂γ'|) +
      K ^ 3 / 6 * ((B : ℝ) * (∫ x, (∑ p, |x p|) ^ 3 ∂ν' + ∫ x, (∑ p, |x p|) ^ 3 ∂γ')) := by ring
  rw [e]
  gcongr

end Compare

/-! ### Base maps of one and two `k`-sets -/

variable (k : ℕ)

/-- The coordinate of the same unit at pattern `0`. -/
def tp_base (p : Fin (k * 2 ^ k)) : Fin (k * 2 ^ k) := cd_idx k (gg_unit k p) ⟨0, by positivity⟩

/-- The base map of the joint coordinates (within each set). -/
def tp_baseJ (P : Fin (2 * (k * 2 ^ k))) : Fin (2 * (k * 2 ^ k)) :=
  gg_jidx k (gg_jw k P) (tp_base k (gg_jp k P))

/-- The Gaussian law of the difference field of a `k`-set. -/
def tp_G1 : Measure (Fin (k * 2 ^ k) → ℝ) := gg_law (tp_DA (tp_base k) (gg_A k))

/-- The Gaussian law of the joint difference field of two `k`-sets sharing `m` units. -/
def tp_G2 (m : ℕ) : Measure (Fin (2 * (k * 2 ^ k)) → ℝ) := gg_law (tp_DA (tp_baseJ k) (gg_AJ k m))

instance : IsProbabilityMeasure (tp_G1 k) := by unfold tp_G1; infer_instance

instance (m : ℕ) : IsProbabilityMeasure (tp_G2 k m) := by unfold tp_G2; infer_instance

/-- Third absolute moment of the single Gaussian difference law. -/
def tp_C3G1 : ℝ := ∫ x, (∑ p, |x p|) ^ 3 ∂(tp_G1 k)

/-- Third absolute moment of the joint Gaussian difference law. -/
def tp_C3G2 (m : ℕ) : ℝ := ∫ x, (∑ P, |x P|) ^ 3 ∂(tp_G2 k m)

lemma tp_C3G1_nonneg : 0 ≤ tp_C3G1 k :=
  integral_nonneg fun _ => pow_nonneg (sum_nonneg fun _ _ => abs_nonneg _) 3

lemma tp_C3G2_nonneg (m : ℕ) : 0 ≤ tp_C3G2 k m :=
  integral_nonneg fun _ => pow_nonneg (sum_nonneg fun _ _ => abs_nonneg _) 3

/-! ### The three comparisons -/

variable {N : ℕ}

lemma tp_pow_le (N : ℕ) : (3 / 4 : ℝ) ^ N ≤ (23 / 25 : ℝ) ^ N :=
  pow_le_pow_left₀ (by norm_num) (by norm_num) N

/-- The difference field of one `k`-set, with the block of `s` removed. -/
def tp_restD {e : Fin k → Fin N} (he : Function.Injective e) (s : State N) (w : Param N) :
    Fin (k * 2 ^ k) → ℝ :=
  tp_Dif (tp_base k) (∑ b, bg_sXr he s w b)

lemma measurable_tp_restD {e : Fin k → Fin N} (he : Function.Injective e) (s : State N) :
    Measurable (tp_restD k he s) :=
  (measurable_tp_Dif _).comp (Finset.measurable_sum _ fun b _ =>
    (measurable_pi_apply b).comp (bg_measurable_Xr _ _ _ _ s))

/-- The error constants of the single comparison. -/
def tp_E2s : ℝ := ((k * 2 ^ k : ℕ) : ℝ) ^ 2 * (4 * (3 * 4 ^ k))

def tp_E3s : ℝ := (((k * 2 ^ k : ℕ) : ℝ) + 1) ^ 3 * (8 * ((k : ℝ) * 2 ^ k) ^ 3 * 4 ^ k)
  + tp_C3G1 k * (2 * 2 ^ k)

/-- **Single comparison**: removing the block of `s`, the box expectations of the difference field
are within `tp_err` of the Gaussian ones. -/
theorem tp_compare_single {e : Fin k → Fin N} (he : Function.Injective e) (s : State N)
    (hB : 2 ≤ bg_sB e) (c : Fin (k * 2 ^ k) → ℝ) (r bb : ℝ) :
    |∫ w, tp_boxF c r (ps_eps N) bb (tp_restD k he s w) ∂cubeM N
        - ∫ x, tp_boxF c r (ps_eps N) bb x ∂(tp_G1 k)| ≤ tp_err (tp_E2s k) (tp_E3s k) N := by
  have hB' : 0 < bg_sB e - 1 := by omega
  have hmeasX : Measurable (bg_sXr he s) := bg_measurable_Xr _ _ _ _ s
  have h2 : ∀ p q, |((bg_sB e - 1 : ℕ) : ℝ) * ∫ x, x p * x q ∂bg_snu e - gg_cov (gg_A k) p q|
      ≤ 3 * 4 ^ k * (3 / 4 : ℝ) ^ N := fun p q => by
    rw [gg_cov_A]; exact bg_snu_second_pred he p q
  have hν3 := bg_snu_integrable3 he
  have hint0 : 0 ≤ ∫ x, (∑ p, |x p|) ^ 3 ∂bg_snu e :=
    integral_nonneg fun x => pow_nonneg (sum_nonneg fun _ _ => abs_nonneg _) 3
  have h3 : ((bg_sB e - 1 : ℕ) : ℝ) * ∫ x, (∑ p, |x p|) ^ 3 ∂bg_snu e ≤
      8 * ((k : ℝ) * 2 ^ k) ^ 3 * 4 ^ k * (23 / 25 : ℝ) ^ N := by
    refine le_trans ?_ (bg_snu_third he)
    have : ((bg_sB e - 1 : ℕ) : ℝ) ≤ bg_sB e := by exact_mod_cast Nat.sub_le _ _
    exact mul_le_mul_of_nonneg_right this hint0
  have hc := tp_compare (cubeM N) hB' hmeasX (bg_s_map_Xr he s) (bg_snu_mean he) hν3 (gg_A k)
    (tp_base k) h2 h3 c r (ps_eps_pos N) bb
  refine hc.trans ?_
  -- `1 / √(B - 1) ≤ 2^(k/2+1) (3/4)^N`
  have hk2 : (bg_sB e : ℝ) * 2 ^ k = 2 ^ N := by
    rw [bg_sB_eq he]; push_cast; rw [← pow_add, Nat.sub_add_cancel (bg_s_le he)]
  have hs := ps_inv_sqrt_le (N := N) (k := 2 ^ k) (A := 2 * 2 ^ k) hB hk2 (by positivity)
    (by nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (by norm_num) (n := k)])
  have hC3 := tp_C3G1_nonneg k
  have hsq : (tp_C3G1 k) / Real.sqrt ((bg_sB e - 1 : ℕ) : ℝ) ≤
      tp_C3G1 k * (2 * 2 ^ k) * (23 / 25 : ℝ) ^ N := by
    rw [div_eq_mul_one_div, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hs.trans (by
      have h1 := tp_pow_le N
      have h2 : (0 : ℝ) ≤ 2 * 2 ^ k := (by positivity)
      nlinarith)) hC3
  unfold tp_err tp_E2s tp_E3s
  have hK := lind_Kpsi_pos
  have hε := ps_eps_pos N
  have hd : (0 : ℝ) ≤ (((k * 2 ^ k : ℕ) : ℝ) + 1) ^ 3 := by positivity
  have hG1 : tp_C3G1 k = ∫ x, (∑ p, |x p|) ^ 3 ∂gg_law (tp_DA (tp_base k) (gg_A k)) := rfl
  rw [← hG1]
  gcongr ?_ + ?_
  · apply le_of_eq; ring
  · have : ((((k * 2 ^ k : ℕ) : ℝ)) + 1) ^ 3 * (8 * ((k : ℝ) * 2 ^ k) ^ 3 * 4 ^ k * (23 / 25 : ℝ) ^ N)
        + tp_C3G1 k / Real.sqrt ((bg_sB e - 1 : ℕ) : ℝ) ≤
        ((((k * 2 ^ k : ℕ) : ℝ) + 1) ^ 3 * (8 * ((k : ℝ) * 2 ^ k) ^ 3 * 4 ^ k)
          + tp_C3G1 k * (2 * 2 ^ k)) * (23 / 25 : ℝ) ^ N := by nlinarith
    gcongr

/-- The joint difference field of two `k`-sets, with the superblock of `s` removed. -/
def tp_restDJ {m : ℕ} {e0 e1 : Fin k → Fin N} (h : bg_JPair k m e0 e1) (s : State N) (w : Param N) :
    Fin (2 * (k * 2 ^ k)) → ℝ :=
  tp_Dif (tp_baseJ k) (∑ b, bg_jXr h s w b)

/-- The joint difference field of two `k`-sets (all superblocks). -/
def tp_fullDJ {m : ℕ} {e0 e1 : Fin k → Fin N} (h : bg_JPair k m e0 e1) (w : Param N) :
    Fin (2 * (k * 2 ^ k)) → ℝ :=
  tp_Dif (tp_baseJ k) (∑ b, bg_jXs h w b)

lemma measurable_tp_restDJ {m : ℕ} {e0 e1 : Fin k → Fin N} (h : bg_JPair k m e0 e1) (s : State N) :
    Measurable (tp_restDJ k h s) :=
  (measurable_tp_Dif _).comp (Finset.measurable_sum _ fun b _ =>
    (measurable_pi_apply b).comp (bg_measurable_Xr _ _ _ _ s))

lemma measurable_tp_fullDJ {m : ℕ} {e0 e1 : Fin k → Fin N} (h : bg_JPair k m e0 e1) :
    Measurable (tp_fullDJ k h) :=
  (measurable_tp_Dif _).comp (Finset.measurable_sum _ fun b _ =>
    (measurable_pi_apply b).comp (bg_measurable_Xs _ _ _ _))

/-- The error constants of the joint comparisons. -/
def tp_E2j (m : ℕ) : ℝ := ((2 * (k * 2 ^ k) : ℕ) : ℝ) ^ 2 * (4 * (3 * ((2 : ℝ) ^ (2 * k - m)) ^ 2))

def tp_E3j (m : ℕ) : ℝ := (((2 * (k * 2 ^ k) : ℕ) : ℝ) + 1) ^ 3 *
    (8 * (2 * ((k : ℝ) * 2 ^ k)) ^ 3 * ((2 : ℝ) ^ (2 * k - m)) ^ 2)
  + tp_C3G2 k m * (2 * 2 ^ (2 * k - m))

lemma tp_jB_mul {m : ℕ} {e0 e1 : Fin k → Fin N} (h : bg_JPair k m e0 e1) :
    (bg_jB e0 e1 m : ℝ) * 2 ^ (2 * k - m) = 2 ^ N := by
  rw [bg_jB_eq h]; push_cast; rw [← pow_add, Nat.sub_add_cancel (bg_j_le h)]

lemma tp_joint_final {m : ℕ} {B : ℕ} (hB : 2 ≤ B) (hk : (B : ℝ) * 2 ^ (2 * k - m) = 2 ^ N)
    {B' : ℕ} (hB' : B - 1 ≤ B') (_hB'0 : 0 < B') {x2 x3 : ℝ}
    (hx2 : x2 ≤ ((2 * (k * 2 ^ k) : ℕ) : ℝ) ^ 2 * (4 * (3 * ((2 : ℝ) ^ (2 * k - m)) ^ 2 *
      (3 / 4 : ℝ) ^ N)))
    (hx3 : x3 ≤ (((2 * (k * 2 ^ k) : ℕ) : ℝ) + 1) ^ 3 *
      (8 * (2 * ((k : ℝ) * 2 ^ k)) ^ 3 * ((2 : ℝ) ^ (2 * k - m)) ^ 2 * (23 / 25 : ℝ) ^ N)) :
    (2 * (lind_Kpsi / ps_eps N)) ^ 2 / 2 * x2 +
      (2 * (lind_Kpsi / ps_eps N)) ^ 3 / 6 * (x3 + tp_C3G2 k m / Real.sqrt B') ≤
      tp_err (tp_E2j k m) (tp_E3j k m) N := by
  have hs := ps_inv_sqrt_le (N := N) (k := 2 ^ (2 * k - m)) (A := 2 * 2 ^ (2 * k - m)) hB hk
    (by positivity) (by nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (by norm_num) (n := 2 * k - m)])
  have hsB : 1 / Real.sqrt B' ≤ 1 / Real.sqrt ((B - 1 : ℕ) : ℝ) := by
    have h1 : (0 : ℝ) < ((B - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < B - 1)
    have h2 : ((B - 1 : ℕ) : ℝ) ≤ B' := by exact_mod_cast hB'
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 h1) (Real.sqrt_le_sqrt h2)
  have hC3 := tp_C3G2_nonneg k m
  have hsq : tp_C3G2 k m / Real.sqrt B' ≤ tp_C3G2 k m * (2 * 2 ^ (2 * k - m)) * (23 / 25 : ℝ) ^ N := by
    rw [div_eq_mul_one_div, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((hsB.trans hs).trans ?_) hC3
    have h1 := tp_pow_le N
    have h2 : (0 : ℝ) ≤ 2 * 2 ^ (2 * k - m) := (by positivity)
    nlinarith
  unfold tp_err tp_E2j tp_E3j
  have hK := lind_Kpsi_pos
  have hε := ps_eps_pos N
  gcongr ?_ + ?_
  · calc (2 * (lind_Kpsi / ps_eps N)) ^ 2 / 2 * x2
        ≤ (2 * (lind_Kpsi / ps_eps N)) ^ 2 / 2 * (((2 * (k * 2 ^ k) : ℕ) : ℝ) ^ 2 *
          (4 * (3 * ((2 : ℝ) ^ (2 * k - m)) ^ 2 * (3 / 4 : ℝ) ^ N))) := by gcongr
      _ = _ := by ring
  · gcongr
    nlinarith

/-- **Joint comparison** with the superblock of `s` removed. -/
theorem tp_compare_rest {m : ℕ} {e0 e1 : Fin k → Fin N} (h : bg_JPair k m e0 e1) (s : State N)
    (hB : 2 ≤ bg_jB e0 e1 m) (c : Fin (2 * (k * 2 ^ k)) → ℝ) (r bb : ℝ) :
    |∫ w, tp_boxF c r (ps_eps N) bb (tp_restDJ k h s w) ∂cubeM N
        - ∫ x, tp_boxF c r (ps_eps N) bb x ∂(tp_G2 k m)| ≤ tp_err (tp_E2j k m) (tp_E3j k m) N := by
  have hB' : 0 < bg_jB e0 e1 m - 1 := by omega
  have hmeasX : Measurable (bg_jXr h s) := bg_measurable_Xr _ _ _ _ s
  have h2 : ∀ P Q, |((bg_jB e0 e1 m - 1 : ℕ) : ℝ) * ∫ x, x P * x Q ∂bg_jnu e0 e1 m
      - gg_cov (gg_AJ k m) P Q| ≤ 3 * ((2 : ℝ) ^ (2 * k - m)) ^ 2 * (3 / 4 : ℝ) ^ N :=
    fun P Q => by rw [gg_cov_AJ k m h.1]; exact bg_jnu_second_pred h P Q
  have hint0 : 0 ≤ ∫ x, (∑ P, |x P|) ^ 3 ∂bg_jnu e0 e1 m :=
    integral_nonneg fun x => pow_nonneg (sum_nonneg fun _ _ => abs_nonneg _) 3
  have h3 : ((bg_jB e0 e1 m - 1 : ℕ) : ℝ) * ∫ x, (∑ P, |x P|) ^ 3 ∂bg_jnu e0 e1 m ≤
      8 * (2 * ((k : ℝ) * 2 ^ k)) ^ 3 * ((2 : ℝ) ^ (2 * k - m)) ^ 2 * (23 / 25 : ℝ) ^ N := by
    refine le_trans ?_ (bg_jnu_third h)
    have : ((bg_jB e0 e1 m - 1 : ℕ) : ℝ) ≤ bg_jB e0 e1 m := by exact_mod_cast Nat.sub_le _ _
    exact mul_le_mul_of_nonneg_right this hint0
  have hc := tp_compare (cubeM N) hB' hmeasX (bg_j_map_Xr h s) (bg_jnu_mean h)
    (bg_jnu_integrable3 h) (gg_AJ k m) (tp_baseJ k) h2 h3 c r (ps_eps_pos N) bb
  refine hc.trans (tp_joint_final k hB (tp_jB_mul k h) le_rfl hB' ?_ ?_)
  · apply le_of_eq; ring
  · have hd : (0 : ℝ) ≤ (((2 * (k * 2 ^ k) : ℕ) : ℝ) + 1) ^ 3 := by positivity
    exact le_rfl

/-- **Joint comparison** over all superblocks. -/
theorem tp_compare_full {m : ℕ} {e0 e1 : Fin k → Fin N} (h : bg_JPair k m e0 e1)
    (hB : 2 ≤ bg_jB e0 e1 m) (c : Fin (2 * (k * 2 ^ k)) → ℝ) (r bb : ℝ) :
    |∫ w, tp_boxF c r (ps_eps N) bb (tp_fullDJ k h w) ∂cubeM N
        - ∫ x, tp_boxF c r (ps_eps N) bb x ∂(tp_G2 k m)| ≤ tp_err (tp_E2j k m) (tp_E3j k m) N := by
  have hB' : 0 < bg_jB e0 e1 m := by omega
  have hmeasX : Measurable (bg_jXs h) := bg_measurable_Xs _ _ _ _
  have h2 : ∀ P Q, |(bg_jB e0 e1 m : ℝ) * ∫ x, x P * x Q ∂bg_jnu e0 e1 m
      - gg_cov (gg_AJ k m) P Q| ≤ 2 ^ (2 * k - m) * (3 / 4 : ℝ) ^ N :=
    fun P Q => by rw [gg_cov_AJ k m h.1]; exact bg_jnu_second h P Q
  have hc := tp_compare (cubeM N) hB' hmeasX (bg_j_map_Xs h) (bg_jnu_mean h)
    (bg_jnu_integrable3 h) (gg_AJ k m) (tp_baseJ k) h2 (bg_jnu_third h) c r (ps_eps_pos N) bb
  refine hc.trans (tp_joint_final k hB (tp_jB_mul k h) (Nat.sub_le _ _) hB' ?_ le_rfl)
  have h1 : (2 : ℝ) ^ (2 * k - m) ≤ 3 * ((2 : ℝ) ^ (2 * k - m)) ^ 2 := by
    have : (1 : ℝ) ≤ 2 ^ (2 * k - m) := one_le_pow₀ (by norm_num)
    nlinarith
  have h34 : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ N := by positivity
  have hd : (0 : ℝ) ≤ ((2 * (k * 2 ^ k) : ℕ) : ℝ) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_right h1 h34
  calc ((2 * (k * 2 ^ k) : ℕ) : ℝ) ^ 2 * (4 * (2 ^ (2 * k - m) * (3 / 4 : ℝ) ^ N))
      ≤ ((2 * (k * 2 ^ k) : ℕ) : ℝ) ^ 2 * (4 * (3 * ((2 : ℝ) ^ (2 * k - m)) ^ 2 * (3 / 4 : ℝ) ^ N)) := by
        gcongr
    _ = _ := rfl

end

end Census
end IIT
