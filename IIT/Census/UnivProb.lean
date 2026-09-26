/-
Census of complexes: the "universe wins at its maximal row" event has vanishing probability.
-/
import IIT.Census.Basic
import IIT.Census.ErlangProof

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset ProbabilityTheory

noncomputable section

variable {N : ℕ}

/-- Parameters for which some row `t` is a global maximum of the row products and beats the
half-means in every column. -/
def badUniv (N : ℕ) (s : State N) : Set (Param N) :=
  {z | z ∈ cube N ∧ ∃ t : State N, (∀ t', rowProd z s t' ≤ rowProd z s t) ∧
    ∀ j, halfMean z s j (t j) < y z s t j}

/-- **Proved in `ErlangProof.lean`.** Erlang tail bound for products of uniforms: if `U₁,…,U_N` are iid
uniform on `[0,1]`, `P(∏ Uᵢ ≥ e^{-x}) = e^{-x} ∑_{k ≥ N} x^k/k! ≥ e^{-x} x^N / N!`
(the sum of `N` iid `Exp(1)` variables is `Gamma(N,1)`; e.g. Feller, Vol. II, §I.3). -/
theorem erlang_lower (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal (Real.exp (-x) * x ^ N / N.factorial) ≤
      volume {v : Fin N → ℝ | (∀ i, v i ∈ Set.Icc (0:ℝ) 1) ∧ Real.exp (-x) ≤ ∏ i, v i} :=
  erlang_lower_thm N x hx

/-! ### The coordinate flip `x ↦ 1 - x` on columns with `s j = false` -/

/-- Flip a coordinate when the bit is `false`. -/
def flipC (b : Bool) (x : ℝ) : ℝ := if b then x else 1 - x

lemma flipC_invol (b : Bool) : Function.Involutive (flipC b) := by
  intro x; cases b <;> simp [flipC]

lemma mp_flipC (b : Bool) : MeasurePreserving (flipC b) volume volume := by
  cases b
  · have : flipC false = fun x => 1 - x := by funext x; simp [flipC]
    rw [this]; exact Measure.measurePreserving_sub_left volume (1 : ℝ)
  · have : flipC true = id := by funext x; simp [flipC]
    rw [this]; exact MeasurePreserving.id _

/-- The flip on parameter vectors. -/
def flipP (s : State N) (z : Param N) : Param N := fun r j => flipC (s j) (z r j)

lemma mp_flipP (s : State N) : MeasurePreserving (flipP s) volume volume :=
  volume_preserving_pi (fun _ => volume_preserving_pi (fun j => mp_flipC (s j)))

lemma flipP_invol (s : State N) : Function.Involutive (flipP s) := by
  intro z; funext r j; exact flipC_invol (s j) (z r j)

/-- The flip as a measurable equivalence. -/
def flipE (s : State N) : Param N ≃ᵐ Param N where
  toEquiv := (flipP_invol s).toPerm _
  measurable_toFun := (mp_flipP s).measurable
  measurable_invFun := (mp_flipP s).measurable

lemma mp_flipE (s : State N) : MeasurePreserving (flipE s) volume volume := mp_flipP s

/-! ### Plain-coordinate events -/

/-- Half-mean in plain coordinates. -/
def hm (w : Param N) (j : Fin N) (b : Bool) : ℝ :=
  (∑ r ∈ univ.filter (fun r : State N => r j = b), w r j) / (2 : ℝ) ^ (N - 1)

/-- The row-product threshold `e^{-N/4}`. -/
def θ (N : ℕ) : ℝ := Real.exp (-((N : ℝ) / 4))

/-- The column threshold `1/2 - 1/100`. -/
def a0 : ℝ := 49 / 100

def A3 (N : ℕ) : Set (Param N) := {w | ∃ j b, hm w j b ≤ a0}
def B4 (N : ℕ) : Set (Param N) := {w | ∀ t : State N, ∏ j, w t j < θ N}
def C5 (N : ℕ) : Set (Param N) := {w | ∃ t : State N, (∀ j, a0 < w t j) ∧ θ N ≤ ∏ j, w t j}

lemma clamp01_of_mem {x : ℝ} (h : x ∈ Set.Icc (0 : ℝ) 1) : clamp01 x = x := by
  unfold clamp01; rw [min_eq_right h.2, max_eq_right h.1]

lemma y_eq {z : Param N} (hz : z ∈ cube N) (s r : State N) (j : Fin N) :
    y z s r j = flipP s z r j := by
  simp only [y, tpmOf, flipP, flipC, clamp01_of_mem (hz r j)]

lemma flipP_cube {z : Param N} (hz : z ∈ cube N) (s : State N) : flipP s z ∈ cube N := by
  intro r j
  have h := hz r j
  simp only [flipP, flipC]
  cases s j <;> simp [h.1, h.2]

lemma bad_sub (s : State N) :
    badUniv N s ⊆ flipE s ⁻¹' (cube N ∩ (A3 N ∪ B4 N ∪ C5 N)) := by
  rintro z ⟨hz, t, hmax, hbeat⟩
  set w := flipP s z with hw
  have hE : (flipE s) z = w := rfl
  simp only [Set.mem_preimage, hE]
  refine ⟨flipP_cube hz s, ?_⟩
  have hy : ∀ r j, y z s r j = w r j := fun r j => y_eq hz s r j
  have hrow : ∀ r, rowProd z s r = ∏ j, w r j := fun r => by
    simp only [rowProd, hy]
  have hhm : ∀ j b, halfMean z s j b = hm w j b := fun j b => by
    simp only [halfMean, hm, hy]
  by_cases hA : ∃ j b, hm w j b ≤ a0
  · exact Or.inl (Or.inl hA)
  by_cases hB : ∀ t : State N, ∏ j, w t j < θ N
  · exact Or.inl (Or.inr hB)
  push Not at hA hB
  obtain ⟨t0, ht0⟩ := hB
  refine Or.inr ⟨t, fun j => ?_, ?_⟩
  · have := hbeat j
    rw [hhm, hy] at this
    exact (hA j (t j)).trans this
  · have := hmax t0
    rw [hrow, hrow] at this
    exact ht0.trans this

/-! ### The uniform product measures -/

/-- Uniform measure on `[0,1]`. -/
def unif : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unif := ⟨by simp [unif, Real.volume_Icc]⟩

/-- Uniform measure on a row. -/
def rowM (N : ℕ) : Measure (Fin N → ℝ) := Measure.pi fun _ => unif

/-- Uniform measure on the parameter cube. -/
def cubeM (N : ℕ) : Measure (Param N) := Measure.pi fun _ => rowM N

instance : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
instance : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance

/-- The row cube. -/
def cubeRow (N : ℕ) : Set (Fin N → ℝ) := Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1

lemma measurableSet_cubeRow : MeasurableSet (cubeRow N) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

lemma restrict_row : (volume : Measure (Fin N → ℝ)).restrict (cubeRow N) = rowM N := by
  rw [volume_pi, cubeRow, Measure.restrict_pi_pi]; rfl

lemma cube_eq : cube N = Set.univ.pi fun _ => cubeRow N := by
  ext z; simp only [cube, cubeRow, Set.mem_ofPred_eq, Set.mem_univ_pi]

lemma restrict_cube : (volume : Measure (Param N)).restrict (cube N) = cubeM N := by
  rw [cube_eq, volume_pi, Measure.restrict_pi_pi]; simp_rw [restrict_row]; rfl

lemma measurableSet_cube : MeasurableSet (cube N) := by
  rw [cube_eq]
  exact MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_Icc

lemma volume_cube_inter (X : Set (Param N)) : volume (cube N ∩ X) = cubeM N X := by
  rw [← restrict_cube, Measure.restrict_apply' measurableSet_cube, Set.inter_comm]

/-! ### (b) no row reaches `θ`: probability `≤ e N / ρ^N` -/

/-- The Erlang lower bound at `x = N/4`. -/
def piN (N : ℕ) : ℝ := Real.exp (-((N : ℝ) / 4)) * ((N : ℝ) / 4) ^ N / N.factorial

lemma piN_le (N : ℕ) :
    ENNReal.ofReal (piN N) ≤ rowM N {v | θ N ≤ ∏ j, v j} := by
  refine (erlang_lower N ((N : ℝ) / 4) (by positivity)).trans ?_
  rw [← restrict_row, Measure.restrict_apply' measurableSet_cubeRow]
  refine measure_mono fun v hv => ⟨hv.2, fun i _ => hv.1 i⟩

lemma measurable_rowProd : Measurable fun v : Fin N → ℝ => ∏ j, v j := by fun_prop

lemma P_B4_pow (N : ℕ) :
    cubeM N (B4 N) ≤ ENNReal.ofReal (Real.exp (-piN N)) ^ (2 ^ N) := by
  have hB : B4 N = Set.univ.pi fun _ => {v : Fin N → ℝ | ∏ j, v j < θ N} := by
    ext w; simp [B4]
  rw [hB, cubeM, Measure.pi_pi, Finset.prod_const, card_state]
  gcongr
  have hc : {v : Fin N → ℝ | ∏ j, v j < θ N} = {v | θ N ≤ ∏ j, v j}ᶜ := by
    ext v; simp
  rw [hc, prob_compl_eq_one_sub (measurableSet_le measurable_const measurable_rowProd)]
  have hp : 0 ≤ piN N := by unfold piN; positivity
  calc 1 - rowM N {v | θ N ≤ ∏ j, v j} ≤ 1 - ENNReal.ofReal (piN N) := by
        gcongr; exact piN_le N
    _ = ENNReal.ofReal (1 - piN N) := by rw [ENNReal.ofReal_sub _ hp, ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (Real.exp (-piN N)) := by
        gcongr; linarith [Real.add_one_le_exp (-piN N)]

lemma fact_le {N : ℕ} (hN : 1 ≤ N) :
    (N.factorial : ℝ) ≤ Real.exp 1 * N * (N : ℝ) ^ N / Real.exp 1 ^ N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have h : Stirling.stirlingSeq (n + 1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le n)
  rw [Stirling.stirlingSeq_one, Stirling.stirlingSeq] at h
  set m : ℝ := ((n + 1 : ℕ) : ℝ) with hm
  have hm1 : 1 ≤ m := by rw [hm]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have h2 : 0 < √2 := by positivity
  have hs : √(2 * m) = √2 * √m := Real.sqrt_mul (by norm_num) _
  have hsq : √m ≤ m := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hpos : 0 < √(2 * m) * (m / Real.exp 1) ^ (n + 1) := by positivity
  rw [div_le_div_iff₀ hpos h2, hs] at h
  have key : ((n + 1).factorial : ℝ) ≤ Real.exp 1 * √m * (m / Real.exp 1) ^ (n + 1) := by
    have : ((n + 1).factorial : ℝ) * √2 ≤ (Real.exp 1 * √m * (m / Real.exp 1) ^ (n + 1)) * √2 :=
      h.trans_eq (by ring)
    exact le_of_mul_le_mul_right this h2
  calc ((n + 1).factorial : ℝ) ≤ Real.exp 1 * √m * (m / Real.exp 1) ^ (n + 1) := key
    _ ≤ Real.exp 1 * m * (m / Real.exp 1) ^ (n + 1) := by gcongr
    _ = _ := by rw [div_pow]; ring

/-- `ρ = e^{3/4}/2 > 1`. -/
def rho : ℝ := Real.exp 1 * Real.exp (-1 / 4) / 2

lemma one_lt_rho : 1 < rho := by
  have h : Real.exp 1 * Real.exp (-1 / 4) = Real.exp (3 / 4) := by
    rw [← Real.exp_add]; norm_num
  have := Real.quadratic_le_exp_of_nonneg (x := 3 / 4) (by norm_num)
  unfold rho; rw [h]; linarith

lemma two_pow_piN {N : ℕ} (hN : 1 ≤ N) :
    rho ^ N / (Real.exp 1 * N) ≤ 2 ^ N * piN N := by
  have hf := fact_le hN
  have hq : Real.exp (-((N : ℝ) / 4)) = Real.exp (-1 / 4) ^ N := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hfpos : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have h4 : (4 : ℝ) ^ N = 2 ^ N * 2 ^ N := by rw [← mul_pow]; norm_num
  unfold piN; rw [hq]
  calc rho ^ N / (Real.exp 1 * N)
      = 2 ^ N * (Real.exp (-1 / 4) ^ N * ((N : ℝ) / 4) ^ N /
          (Real.exp 1 * N * (N : ℝ) ^ N / Real.exp 1 ^ N)) := by
        unfold rho
        rw [div_pow (N : ℝ) 4, h4, div_pow _ (2 : ℝ), mul_pow]
        field_simp
    _ ≤ _ := by gcongr

lemma P_B4 {N : ℕ} (hN : 1 ≤ N) :
    cubeM N (B4 N) ≤ ENNReal.ofReal (Real.exp 1 * N / rho ^ N) := by
  refine (P_B4_pow N).trans ?_
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le]
  gcongr
  have hX := two_pow_piN hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlow : 0 < rho ^ N / (Real.exp 1 * N) := by
    have := one_lt_rho; positivity
  have hXpos : 0 < 2 ^ N * piN N := hlow.trans_le hX
  rw [← Real.exp_nat_mul]
  have he : ((2 ^ N : ℕ) : ℝ) * -piN N = -(2 ^ N * piN N) := by push_cast; ring
  rw [he, Real.exp_neg]
  calc (Real.exp (2 ^ N * piN N))⁻¹ ≤ (2 ^ N * piN N)⁻¹ := by
        apply inv_anti₀ hXpos; linarith [Real.add_one_le_exp (2 ^ N * piN N)]
    _ ≤ (rho ^ N / (Real.exp 1 * N))⁻¹ := inv_anti₀ hlow hX
    _ = _ := by rw [inv_div]

/-! ### (c) a row above `θ` with every entry above `a0`: Markov bound -/

/-- The Markov weight `x ↦ x · 1_{x > a0}`. -/
def fI (x : ℝ) : ENNReal := (Set.Ioi a0).indicator (fun x => ENNReal.ofReal x) x

lemma measurable_fI : Measurable fI := ENNReal.measurable_ofReal.indicator measurableSet_Ioi

/-- `∫_{a0}^1 x dx`. -/
def Iint : ℝ := (1 - a0 ^ 2) / 2

lemma lintegral_fI : ∫⁻ x, fI x ∂unif = ENNReal.ofReal Iint := by
  have hset : Set.Ioi a0 ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc a0 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc, a0]
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith, h3⟩
  unfold fI unif
  rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, hset,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le (by norm_num [a0]), integral_id]; unfold Iint; norm_num
  · exact (continuous_id.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  · exact ae_restrict_of_forall_mem measurableSet_Ioc fun x hx =>
      (lt_trans (by norm_num [a0]) hx.1).le

lemma θ_pos (N : ℕ) : 0 < θ N := Real.exp_pos _

lemma rowM_markov (N : ℕ) :
    rowM N {v | (∀ j, a0 < v j) ∧ θ N ≤ ∏ j, v j} ≤
      ENNReal.ofReal (θ N)⁻¹ * ENNReal.ofReal Iint ^ N := by
  set G : (Fin N → ℝ) → ENNReal := fun v => ∏ j, fI (v j) with hGdef
  have hG : Measurable G :=
    Finset.measurable_prod _ fun j _ => measurable_fI.comp (measurable_pi_apply j)
  have hsub : {v : Fin N → ℝ | (∀ j, a0 < v j) ∧ θ N ≤ ∏ j, v j} ⊆
      {v | ENNReal.ofReal (θ N) ≤ G v} := by
    rintro v ⟨h1, h2⟩
    have : G v = ENNReal.ofReal (∏ j, v j) := by
      rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => (lt_trans (by norm_num [a0]) (h1 j)).le)]
      exact Finset.prod_congr rfl fun j _ => Set.indicator_of_mem (h1 j) _
    show _ ≤ G v
    rw [this]; exact ENNReal.ofReal_le_ofReal h2
  have hind : iIndepFun (fun j (v : Fin N → ℝ) => fI (v j)) (rowM N) := by
    unfold rowM; exact iIndepFun_pi (X := fun _ x => fI x) (fun _ => measurable_fI.aemeasurable)
  have hint : ∫⁻ v, G v ∂rowM N = ENNReal.ofReal Iint ^ N := by
    rw [hGdef, lintegral_prod_eq_prod_lintegral_of_indepFun univ _ hind
      (fun j => measurable_fI.comp (measurable_pi_apply j))]
    have : ∀ j : Fin N, ∫⁻ v, fI (v j) ∂rowM N = ENNReal.ofReal Iint := fun j => by
      rw [← lintegral_fI]
      exact (measurePreserving_eval (fun _ : Fin N => unif) j).lintegral_comp measurable_fI
    simp [this]
  have hθ := θ_pos N
  calc rowM N {v | (∀ j, a0 < v j) ∧ θ N ≤ ∏ j, v j}
      ≤ rowM N {v | ENNReal.ofReal (θ N) ≤ G v} := measure_mono hsub
    _ = ENNReal.ofReal (θ N)⁻¹ * (ENNReal.ofReal (θ N) * rowM N {v | ENNReal.ofReal (θ N) ≤ G v}) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hθ.le), inv_mul_cancel₀ hθ.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ _ := by
        gcongr
        exact (mul_meas_ge_le_lintegral₀ hG.aemeasurable _).trans hint.le

/-- `κ = 2 e^{1/4} ∫_{a0}^1 x dx < 1`. -/
def kappa : ℝ := 2 * Real.exp (1 / 4) * Iint

lemma kappa_lt_one : kappa < 1 := by
  have h : Real.exp (1 / 4) < 1.3 := by
    by_contra h
    push Not at h
    have h4 : (1.3 : ℝ) ^ 4 ≤ Real.exp (1 / 4) ^ 4 := pow_le_pow_left₀ (by norm_num) h 4
    rw [← Real.exp_nat_mul] at h4
    norm_num at h4
    linarith [Real.exp_one_lt_d9]
  unfold kappa Iint a0; nlinarith [Real.exp_pos (1 / 4)]

lemma kappa_nonneg : 0 ≤ kappa := by
  unfold kappa Iint a0; have := Real.exp_pos (1 / 4); positivity

lemma P_C5 (N : ℕ) : cubeM N (C5 N) ≤ ENNReal.ofReal (kappa ^ N) := by
  have hC : C5 N = ⋃ t : State N,
      (fun w : Param N => w t) ⁻¹' {v | (∀ j, a0 < v j) ∧ θ N ≤ ∏ j, v j} := by
    ext w; simp [C5]
  have hθ' : (θ N)⁻¹ = Real.exp (1 / 4) ^ N := by
    unfold θ; rw [← Real.exp_neg, neg_neg, ← Real.exp_nat_mul]; ring_nf
  have hI : 0 ≤ Iint := by unfold Iint a0; norm_num
  rw [hC]
  calc cubeM N (⋃ t : State N, _) ≤ ∑ t : State N, cubeM N ((fun w : Param N => w t) ⁻¹'
        {v | (∀ j, a0 < v j) ∧ θ N ≤ ∏ j, v j}) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _t : State N, ENNReal.ofReal (θ N)⁻¹ * ENNReal.ofReal Iint ^ N := by
        refine Finset.sum_le_sum fun t _ => ?_
        have hmp := measurePreserving_eval (fun _ : State N => rowM N) t
        refine (Measure.le_map_apply hmp.measurable.aemeasurable _).trans ?_
        unfold cubeM; rw [hmp.map_eq]; exact rowM_markov N
    _ = ENNReal.ofReal (kappa ^ N) := by
        rw [Finset.sum_const, card_state, nsmul_eq_mul, ← ENNReal.ofReal_pow hI,
          ← ENNReal.ofReal_mul (inv_nonneg.2 (θ_pos N).le), ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        push_cast
        rw [hθ']; unfold kappa; ring

/-! ### (a) some half-mean at most `a0`: Chebyshev -/

lemma unif_ae : ∀ᵐ x ∂unif, x ∈ Set.Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc

lemma memLp_unif : MemLp (fun x : ℝ => x) 2 unif :=
  MemLp.of_bound aestronglyMeasurable_id 1 (unif_ae.mono fun x hx => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hx.1, hx.2])

lemma integral_unif : ∫ x, x ∂unif = 1 / 2 := by
  unfold unif
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, integral_id]
  norm_num

lemma mp_coord (r : State N) (j : Fin N) :
    MeasurePreserving (fun w : Param N => w r j) (cubeM N) unif :=
  (measurePreserving_eval (fun _ : Fin N => unif) j).comp
    (measurePreserving_eval (fun _ : State N => rowM N) r)

lemma card_filter (j : Fin N) (b : Bool) :
    ((univ.filter (fun r : State N => r j = b)).card : ℝ) = 2 ^ (N - 1) := by
  have : univ.filter (fun r : State N => r j = b) = agree {j} (fun _ => b) := by
    ext r; simp [agree]
  rw [this, card_agree, Finset.card_singleton]; push_cast; ring

lemma P_A3_one (j : Fin N) (b : Bool) :
    cubeM N {w | hm w j b ≤ a0} ≤ ENNReal.ofReal (5000 / 2 ^ N) := by
  set F := univ.filter (fun r : State N => r j = b) with hF
  set X : State N → Param N → ℝ := fun r w => w r j with hX
  have hmem : ∀ r, MemLp (X r) 2 (cubeM N) := fun r =>
    memLp_unif.comp_measurePreserving (mp_coord r j)
  have hEX : ∀ r, ∫ w, X r w ∂cubeM N = 1 / 2 := fun r => by
    rw [← integral_unif, ← (mp_coord r j).map_eq,
      integral_map (mp_coord r j).measurable.aemeasurable measurable_id'.aestronglyMeasurable]
  have hvar : ∀ r, variance (X r) (cubeM N) ≤ 1 / 4 := fun r => by
    have hae : ∀ᵐ w ∂cubeM N, X r w ∈ Set.Icc (0 : ℝ) 1 :=
      ae_of_ae_map (mp_coord r j).measurable.aemeasurable (by rw [(mp_coord r j).map_eq]; exact unif_ae)
    have := variance_le_sq_of_bounded hae (mp_coord r j).measurable.aemeasurable
    norm_num at this ⊢; exact this
  have hindep : iIndepFun X (cubeM N) := by
    unfold cubeM; exact iIndepFun_pi (X := fun (_ : State N) (v : Fin N → ℝ) => v j) (fun _ => (measurable_pi_apply j).aemeasurable)
  set S := ∑ r ∈ F, X r with hS
  have hSmem : MemLp S 2 (cubeM N) := memLp_finsetSum' F fun r _ => hmem r
  have hSvar : variance S (cubeM N) ≤ 2 ^ (N - 1) / 4 := by
    rw [hS, IndepFun.variance_sum (fun r _ => hmem r) (fun r _ k _ hrk => hindep.indepFun hrk)]
    calc ∑ r ∈ F, variance (X r) (cubeM N) ≤ ∑ _r ∈ F, (1 / 4 : ℝ) := sum_le_sum fun r _ => hvar r
      _ = _ := by rw [sum_const, nsmul_eq_mul, card_filter]; ring
  have hSw : ∀ w, S w = ∑ r ∈ F, w r j := fun w => by simp only [hS, hX, Finset.sum_apply]
  have hSmean : ∫ w, S w ∂cubeM N = 2 ^ (N - 1) / 2 := by
    simp only [hSw]
    rw [integral_finsetSum F fun r _ => (hmem r).integrable one_le_two]
    rw [sum_congr rfl fun r _ => hEX r, sum_const, nsmul_eq_mul, card_filter]; ring
  have hM : (0 : ℝ) < 2 ^ (N - 1) := by positivity
  have hsub : {w | hm w j b ≤ a0} ⊆ {w | 2 ^ (N - 1) / 100 ≤ |S w - ∫ w, S w ∂cubeM N|} := by
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    rw [hSmean, hSw, abs_sub_comm]
    unfold hm at hw; rw [div_le_iff₀ hM] at hw
    refine le_trans ?_ (le_abs_self _)
    unfold a0 at hw; linarith
  have h2 : (2 : ℝ) ^ N ≤ 2 * 2 ^ (N - 1) := by
    rcases N with _ | n
    · norm_num
    · rw [Nat.add_sub_cancel, pow_succ]; linarith
  calc cubeM N {w | hm w j b ≤ a0}
      ≤ cubeM N {w | 2 ^ (N - 1) / 100 ≤ |S w - ∫ w, S w ∂cubeM N|} := measure_mono hsub
    _ ≤ ENNReal.ofReal (variance S (cubeM N) / (2 ^ (N - 1) / 100) ^ 2) :=
        meas_ge_le_variance_div_sq hSmem (by positivity)
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        calc variance S (cubeM N) / (2 ^ (N - 1) / 100) ^ 2
            ≤ (2 ^ (N - 1) / 4) / (2 ^ (N - 1) / 100) ^ 2 := by gcongr
          _ = 2500 / 2 ^ (N - 1) := by field_simp; ring
          _ ≤ 5000 / 2 ^ N := by rw [div_le_div_iff₀ hM (by positivity)]; linarith

lemma P_A3 (N : ℕ) : cubeM N (A3 N) ≤ ENNReal.ofReal (10000 * N / 2 ^ N) := by
  have hA : A3 N = ⋃ j, ⋃ b, {w : Param N | hm w j b ≤ a0} := by ext w; simp [A3]
  rw [hA]
  calc cubeM N (⋃ j, ⋃ b, {w : Param N | hm w j b ≤ a0})
      ≤ ∑ j, cubeM N (⋃ b, {w : Param N | hm w j b ≤ a0}) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ j, ∑ b, cubeM N {w : Param N | hm w j b ≤ a0} :=
        sum_le_sum fun j _ => measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin N, ∑ _b : Bool, ENNReal.ofReal (5000 / 2 ^ N) :=
        sum_le_sum fun j _ => sum_le_sum fun b _ => P_A3_one j b
    _ = _ := by
        simp only [sum_const, card_univ, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
        have : (10000 * (N : ℝ) / 2 ^ N) = N * (2 * (5000 / 2 ^ N)) := by ring
        rw [this, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
        norm_num

/-! ### Main theorem -/

/-- **The universe essentially never wins at its maximal row.** Under the uniform measure on
TPMs, the probability that some maximal row beats every column half-mean tends to `0`. -/
theorem tendsto_volume_badUniv (s : ∀ N, State N) :
    Tendsto (fun N => volume (badUniv N (s N))) atTop (𝓝 0) := by
  have hbound : ∀ N, 1 ≤ N → volume (badUniv N (s N)) ≤
      ENNReal.ofReal (10000 * N / 2 ^ N) + ENNReal.ofReal (Real.exp 1 * N / rho ^ N) +
        ENNReal.ofReal (kappa ^ N) := by
    intro N hN
    calc volume (badUniv N (s N))
        ≤ volume (flipE (s N) ⁻¹' (cube N ∩ (A3 N ∪ B4 N ∪ C5 N))) := measure_mono (bad_sub _)
      _ = cubeM N (A3 N ∪ B4 N ∪ C5 N) := by
          rw [(mp_flipE _).measure_preimage_equiv, volume_cube_inter]
      _ ≤ cubeM N (A3 N) + cubeM N (B4 N) + cubeM N (C5 N) :=
          (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
      _ ≤ _ := by gcongr; exacts [P_A3 N, P_B4 hN, P_C5 N]
  have h1 : Tendsto (fun N : ℕ => 10000 * (N : ℝ) / 2 ^ N) atTop (𝓝 0) := by
    convert (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)).const_mul
      10000 using 1
    · funext N; ring
    · simp
  have h2 : Tendsto (fun N : ℕ => Real.exp 1 * N / rho ^ N) atTop (𝓝 0) := by
    convert (tendsto_pow_const_div_const_pow_of_one_lt 1 one_lt_rho).const_mul
      (Real.exp 1) using 1
    · funext N; ring
    · simp
  have h3 := tendsto_pow_atTop_nhds_zero_of_lt_one kappa_nonneg kappa_lt_one
  have hsum : Tendsto (fun N : ℕ => ENNReal.ofReal (10000 * N / 2 ^ N) +
      ENNReal.ofReal (Real.exp 1 * N / rho ^ N) + ENNReal.ofReal (kappa ^ N)) atTop (𝓝 0) := by
    have := ((ENNReal.tendsto_ofReal h1).add (ENNReal.tendsto_ofReal h2)).add
      (ENNReal.tendsto_ofReal h3)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ((eventually_ge_atTop 1).mono hbound)

end

end Census
end IIT
