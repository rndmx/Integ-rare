/-
Census, B1, W14 WP4, part C: the Chebyshev fields FE4(a), FE4(b) (normalisers) and FE7(b)' (fresh effect
mass at `te`), plus the one-row moments used by FE7(a).
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §9; math W5 §4 (FE4), W9 §5.1 (FE7(b)').  No `sorry`.
-/
import IIT.Census.B1CntFreshB

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### One-row moments -/

/-- An entry read as itself (`b = true`) or reflected (`b = false`). -/
noncomputable def frPhi (b : Bool) (y : ℝ) : ℝ := if b then clamp01 y else 1 - clamp01 y

lemma frPhi_mem (b : Bool) (y : ℝ) : frPhi b y ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 := clamp01_nonneg y
  have h1 := clamp01_le_one y
  unfold frPhi; split_ifs <;> constructor <;> linarith

lemma measurable_frPhi (b : Bool) : Measurable (frPhi b) := by
  unfold frPhi; split_ifs
  · exact clamp01_measurable
  · exact measurable_const.sub clamp01_measurable

lemma frC_int_cl : ∫ y, clamp01 y ∂unif = 1 / 2 := by
  have := integral_cl_pow 1; simp only [pow_one] at this; rw [this]; norm_num

lemma frC_int_cl_sq : ∫ y, clamp01 y ^ 2 ∂unif = 1 / 3 := by
  rw [integral_cl_pow 2]; norm_num

lemma frC_integrable_cl_pow (e : ℕ) : Integrable (fun y => clamp01 y ^ e) unif :=
  Integrable.of_bound (clamp01_measurable.pow_const e).aestronglyMeasurable 1 (ae_of_all _ fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (clamp01_nonneg y) e)]
    exact pow_le_one₀ (clamp01_nonneg y) (clamp01_le_one y))

lemma integral_frPhi (b : Bool) : ∫ y, frPhi b y ∂unif = 1 / 2 := by
  have hi : Integrable (fun y => clamp01 y) unif := by
    simpa using frC_integrable_cl_pow 1
  cases b
  · simp only [frPhi, Bool.false_eq_true, ite_false]
    rw [integral_sub (integrable_const 1) hi, integral_const, frC_int_cl]
    simp only [probReal_univ, smul_eq_mul, one_mul]; norm_num
  · simp only [frPhi, ite_true]; exact frC_int_cl

lemma integral_frPhi_sq (b : Bool) : ∫ y, frPhi b y ^ 2 ∂unif = 1 / 3 := by
  have hi : Integrable (fun y => clamp01 y) unif := by
    simpa using frC_integrable_cl_pow 1
  cases b
  · simp only [frPhi, Bool.false_eq_true, ite_false]
    have e : ∀ y, (1 - clamp01 y) ^ 2 = 1 + (-2) * clamp01 y + clamp01 y ^ 2 := fun y => by ring
    simp_rw [e]
    have hA : Integrable (fun y => 1 + (-2) * clamp01 y) unif := (integrable_const 1).add (hi.const_mul _)
    have hB : Integrable (fun y => (-2) * clamp01 y) unif := hi.const_mul _
    rw [integral_add hA (frC_integrable_cl_pow 2), integral_add (integrable_const 1) hB,
      integral_const, integral_const_mul, frC_int_cl, frC_int_cl_sq]
    simp only [probReal_univ, smul_eq_mul, one_mul]; norm_num
  · simp only [frPhi, ite_true]; exact frC_int_cl_sq

lemma frC_integral_row_prod (φ : Fin N → ℝ → ℝ) :
    ∫ v, ∏ k, φ k (v k) ∂rowM N = ∏ k, ∫ y, φ k y ∂unif := by
  unfold rowM; exact integral_fintype_prod_eq_prod φ

/-- The row function `v ↦ Π_k φ_{b_k}(v_k)`. -/
noncomputable def frRowPhi (b : Fin N → Bool) (v : Fin N → ℝ) : ℝ := ∏ k, frPhi (b k) (v k)

lemma frRowPhi_mem (b : Fin N → Bool) (v : Fin N → ℝ) : frRowPhi b v ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨prod_nonneg fun k _ => (frPhi_mem _ _).1,
    prod_le_one (fun k _ => (frPhi_mem _ _).1) fun k _ => (frPhi_mem _ _).2⟩

lemma measurable_frRowPhi (b : Fin N → Bool) : Measurable (frRowPhi b) :=
  Finset.measurable_prod _ fun k _ => (measurable_frPhi (b k)).comp (measurable_pi_apply k)

lemma integral_frRowPhi (b : Fin N → Bool) : ∫ v, frRowPhi b v ∂rowM N = (1 / 2) ^ N := by
  unfold frRowPhi
  rw [frC_integral_row_prod (fun k => frPhi (b k))]
  simp [integral_frPhi]

lemma integral_frRowPhi_sq (b : Fin N → Bool) : ∫ v, frRowPhi b v ^ 2 ∂rowM N = (1 / 3) ^ N := by
  unfold frRowPhi
  simp_rw [← prod_pow]
  rw [frC_integral_row_prod (fun k y => frPhi (b k) y ^ 2)]
  simp [integral_frPhi_sq]

/-- `rowTX` of a fresh row is `frRowPhi` of that row. -/
lemma rowTX_eq_frRowPhi (w : Param N) (s r t : State N) :
    rowTX w s r t = frRowPhi (fun k => decide (t k = s k)) (w r) := by
  unfold rowTX frRowPhi frPhi
  refine prod_congr rfl fun k _ => ?_
  by_cases h : t k = s k <;> simp [h]

/-- The partial product `Π_{i ∈ M} y_i` as a row function. -/
noncomputable def frRowM (M : Finset (Fin N)) (v : Fin N → ℝ) : ℝ := ∏ i ∈ M, clamp01 (v i)

lemma frRowM_mem (M : Finset (Fin N)) (v : Fin N → ℝ) : frRowM M v ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨prod_nonneg fun k _ => clamp01_nonneg _,
    prod_le_one (fun k _ => clamp01_nonneg _) fun k _ => clamp01_le_one _⟩

lemma measurable_frRowM (M : Finset (Fin N)) : Measurable (frRowM M) :=
  Finset.measurable_prod _ fun k _ => clamp01_measurable.comp (measurable_pi_apply k)

lemma integral_frRowM_pow (M : Finset (Fin N)) (p : ℕ) :
    ∫ v, frRowM M v ^ p ∂rowM N = (1 / ((p : ℝ) + 1)) ^ M.card := by
  have e : ∀ v : Fin N → ℝ, frRowM M v ^ p = ∏ k, (if k ∈ M then clamp01 (v k) ^ p else 1) := by
    intro v; unfold frRowM; rw [← prod_pow, prod_ite_mem_eq]
  simp_rw [e]
  rw [frC_integral_row_prod (fun k y => if k ∈ M then clamp01 y ^ p else 1)]
  have e2 : ∀ k, ∫ y, (if k ∈ M then clamp01 y ^ p else (1 : ℝ)) ∂unif =
      if k ∈ M then 1 / ((p : ℝ) + 1) else 1 := by
    intro k; split_ifs
    · exact integral_cl_pow p
    · simp
  simp_rw [e2]
  rw [prod_ite_mem_eq, prod_const]

/-! ### Chebyshev over the fresh rows -/

lemma frC_cheb_fresh (F : Finset (State N)) (g : (Fin N → ℝ) → ℝ) (hg : Measurable g)
    (hb : ∀ v, g v ∈ Set.Icc (0 : ℝ) 1) {m1 m2 c θ : ℝ} (hm1 : ∫ v, g v ∂rowM N = m1)
    (hm2 : ∫ v, g v ^ 2 ∂rowM N = m2) (hc : 0 < c) (hθ : 2 ^ N * m1 + c ≤ θ) :
    cubeM N {w | θ < ∑ r ∈ univ.filter (fun r => r ∉ F), g (w r)} ≤
      ENNReal.ofReal (2 ^ N * m2 / c ^ 2) := by
  set G : State N → (Fin N → ℝ) → ℝ := fun r v => if r ∉ F then g v else 0 with hGdef
  have hG : ∀ r, Measurable (G r) := fun r => by
    by_cases h : r ∉ F
    · simp only [hGdef, h, not_false_eq_true, ite_true]; exact hg
    · simp only [hGdef, h, ite_false]; exact measurable_const
  have hGb : ∀ r v, |G r v| ≤ 1 := fun r v => by
    by_cases h : r ∉ F
    · simp only [hGdef, h, not_false_eq_true, ite_true]
      rw [abs_of_nonneg (hb v).1]; exact (hb v).2
    · have h' : r ∈ F := not_not.1 h
      simp [hGdef, h']
  have hm1' : 0 ≤ m1 := hm1 ▸ integral_nonneg fun v => (hb v).1
  have hm2' : 0 ≤ m2 := hm2 ▸ integral_nonneg fun v => sq_nonneg _
  have hcard : ((univ : Finset (State N)).card : ℝ) = 2 ^ N := by rw [card_state]; push_cast; rfl
  have hE1 : ∑ r, ∫ v, G r v ∂rowM N ≤ 2 ^ N * m1 := by
    calc ∑ r, ∫ v, G r v ∂rowM N ≤ ∑ _r : State N, m1 := sum_le_sum fun r _ => by
          by_cases h : r ∉ F
          · simp only [hGdef, h, not_false_eq_true, ite_true]; exact hm1.le
          · simp only [hGdef, h, ite_false, integral_zero]; exact hm1'
      _ = 2 ^ N * m1 := by rw [sum_const, nsmul_eq_mul, hcard]
  have hE2 : ∑ r, ∫ v, G r v ^ 2 ∂rowM N ≤ 2 ^ N * m2 := by
    calc ∑ r, ∫ v, G r v ^ 2 ∂rowM N ≤ ∑ _r : State N, m2 := sum_le_sum fun r _ => by
          by_cases h : r ∉ F
          · simp only [hGdef, h, not_false_eq_true, ite_true]; exact hm2.le
          · simp only [hGdef, h, ite_false]; simp [hm2']
      _ = 2 ^ N * m2 := by rw [sum_const, nsmul_eq_mul, hcard]
  have hsum : ∀ w : Param N, ∑ r ∈ univ.filter (fun r => r ∉ F), g (w r) = ∑ r, G r (w r) :=
    fun w => by rw [sum_filter]
  refine (measure_mono ?_).trans ((frA_cheb_rows G hG hGb hc).trans ?_)
  · intro w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    rw [hsum] at hw
    exact le_abs.2 (Or.inl (by linarith))
  · apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_right hE2 (sq_nonneg c)

/-! ### Numerics -/

lemma frC_pow_le_exp {q : ℝ} (hq : 0 < q) (n : ℕ) : q ^ n ≤ Real.exp ((q - 1) * n) := by
  rw [← Real.exp_log (pow_pos hq n), Real.log_pow]
  apply Real.exp_le_exp.2
  have := Real.log_le_sub_one_of_pos hq
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

lemma frC_log_three_gt : (109 / 100 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have he := Real.exp_one_lt_d9
  have h9 : Real.exp (9 / 100) ≤ 100 / 91 := by
    have h := Real.add_one_le_exp (-(9 / 100) : ℝ)
    rw [Real.exp_neg] at h
    have hp := Real.exp_pos (9 / 100 : ℝ)
    rw [le_inv_comm₀ (by norm_num) hp] at h
    linarith
  have e : Real.exp (109 / 100) = Real.exp 1 * Real.exp (9 / 100) := by
    rw [← Real.exp_add]; norm_num
  rw [e]
  have h0 : 0 ≤ Real.exp (9 / 100) := (Real.exp_pos _).le
  calc Real.exp 1 * Real.exp (9 / 100) ≤ 2.7182818286 * (100 / 91) :=
        mul_le_mul he.le h9 h0 (by norm_num)
    _ < 3 := by norm_num

lemma frC_dX_le (N : ℕ) : 30 * dX N ≤ N + 29 := by unfold dX; omega
lemma frC_dX_ge (N : ℕ) : N ≤ 30 * dX N := by unfold dX; omega

/-- `C(N, d) ≤ 2^{7d}` for `d = dX N`. -/
lemma frC_choose_le (N : ℕ) : ((N.choose (dX N) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (7 * dX N) := by
  set d := dX N with hd
  have h1 : ((N.choose d : ℕ) : ℝ) ≤ (N : ℝ) ^ d / (d.factorial : ℝ) := Nat.choose_le_pow_div d N
  have hfac : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  have h2 : (d : ℝ) ^ d / d.factorial ≤ Real.exp d := Real.pow_div_factorial_le_exp (d : ℝ) (Nat.cast_nonneg d) d
  have hN30 : (N : ℝ) ≤ 30 * d := by exact_mod_cast frC_dX_ge N
  have h3 : (N : ℝ) ^ d ≤ (30 : ℝ) ^ d * (d : ℝ) ^ d := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg N) hN30 d
  have he3 : Real.exp d ≤ (3 : ℝ) ^ d := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le (by have := Real.exp_one_lt_d9; linarith) d
  calc ((N.choose d : ℕ) : ℝ) ≤ (N : ℝ) ^ d / d.factorial := h1
    _ ≤ (30 : ℝ) ^ d * (d : ℝ) ^ d / d.factorial := by gcongr
    _ = (30 : ℝ) ^ d * ((d : ℝ) ^ d / d.factorial) := by ring
    _ ≤ (30 : ℝ) ^ d * (3 : ℝ) ^ d := by gcongr; exact h2.trans he3
    _ = (90 : ℝ) ^ d := by rw [← mul_pow]; norm_num
    _ ≤ (128 : ℝ) ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
    _ = (2 : ℝ) ^ (7 * d) := by rw [pow_mul]; norm_num

/-! ### FE4(a) -/

/-- **FE4(a)**: failure `≤ (2/3)^N`. -/
theorem freshFE4a : FreshFieldProb FE4aX (1 / 180) := by
  refine Eventually.of_forall fun N s r0 f => ?_
  refine (frA_transfer (sensRows s r0) f (FE4aX N s r0)
    (B := {w | 2 < ∑ r ∈ univ.filter (fun r => r ∉ sensRows s r0), frRowM univ (w r)})
    fun w hw => ?_).trans ?_
  · simp only [FE4aX, not_le] at hw
    simp only [Set.mem_ofPred_eq]
    have e : ∑ r ∈ freshRows s r0, Pw (glueRows (sensRows s r0) f (restrOut (sensRows s r0) w)) r =
        ∑ r ∈ univ.filter (fun r => r ∉ sensRows s r0), frRowM univ (w r) := by
      unfold freshRows
      refine sum_congr rfl fun r hr => ?_
      unfold Pw frRowM
      rw [frA_glue_fresh _ f w (mem_filter.1 hr).2]
    rwa [e] at hw
  · have hm1 : ∫ v, frRowM univ v ∂rowM N = (1 / 2) ^ N := by
      have := integral_frRowM_pow (N := N) univ 1
      simp only [pow_one, card_univ, Fintype.card_fin] at this; rw [this]; norm_num
    have hm2 : ∫ v, frRowM univ v ^ 2 ∂rowM N = (1 / 3) ^ N := by
      have := integral_frRowM_pow (N := N) univ 2
      simp only [card_univ, Fintype.card_fin] at this; rw [this]; norm_num
    refine (frC_cheb_fresh _ _ (measurable_frRowM univ) (frRowM_mem univ) hm1 hm2 one_pos ?_).trans ?_
    · rw [← mul_pow]; norm_num
    · apply ENNReal.ofReal_le_ofReal
      rw [one_pow, div_one, ← mul_pow]
      refine (frC_pow_le_exp (by norm_num) N).trans (Real.exp_le_exp.2 ?_)
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith

/-! ### FE4(b) -/

lemma frC_fe4b_one (s r0 : State N) (K : Finset (Fin N)) (hK : K.card = dX N) :
    cubeM N {w | (2 : ℝ) ^ (dX N + 1) <
        ∑ r ∈ univ.filter (fun r => r ∉ sensRows s r0), frRowM (univ \ K) (w r)} ≤
      ENNReal.ofReal (2 ^ N * (1 / 3) ^ (N - dX N) / ((2 : ℝ) ^ dX N) ^ 2) := by
  have hMc : (univ \ K).card = N - dX N := by
    rw [card_sdiff_of_subset (subset_univ K), card_univ, Fintype.card_fin, hK]
  have hm1 : ∫ v, frRowM (univ \ K) v ∂rowM N = (1 / 2) ^ (N - dX N) := by
    have := integral_frRowM_pow (N := N) (univ \ K) 1
    simp only [pow_one, hMc] at this; rw [this]; norm_num
  have hm2 : ∫ v, frRowM (univ \ K) v ^ 2 ∂rowM N = (1 / 3) ^ (N - dX N) := by
    have := integral_frRowM_pow (N := N) (univ \ K) 2
    simp only [hMc] at this; rw [this]; norm_num
  have hdN : dX N ≤ N := by
    have := K.card_le_univ; rw [Fintype.card_fin] at this; omega
  refine frC_cheb_fresh _ _ (measurable_frRowM _) (frRowM_mem _) hm1 hm2 (by positivity) ?_
  have e : (2 : ℝ) ^ N * (1 / 2) ^ (N - dX N) = 2 ^ dX N := by
    have : (2 : ℝ) ^ N = 2 ^ dX N * 2 ^ (N - dX N) := by rw [← pow_add]; congr 1; omega
    rw [this, mul_assoc, ← mul_pow]; norm_num
  rw [e, pow_succ]; linarith

/-- **FE4(b)**: failure `≤ C(N, d) 2^N 3^{-(N-d)} 4^{-d} ≤ 2^{7d+N} 3^{-N}`. -/
theorem freshFE4b : FreshFieldProb FE4bX (1 / 180) := by
  filter_upwards [eventually_ge_atTop 100] with N hN s r0 f
  set Kf := (univ : Finset (Fin N)).powersetCard (dX N) with hKf
  refine (frA_transfer (sensRows s r0) f (FE4bX N s r0)
    (B := ⋃ K ∈ Kf, {w | (2 : ℝ) ^ (dX N + 1) <
      ∑ r ∈ univ.filter (fun r => r ∉ sensRows s r0), frRowM (univ \ K) (w r)})
    fun w hw => ?_).trans ?_
  · simp only [FE4bX, not_forall, not_le, exists_prop] at hw
    obtain ⟨K, hK, hlt⟩ := hw
    refine Set.mem_biUnion (x := K) (Finset.mem_coe.2 (mem_powersetCard.2 ⟨subset_univ _, hK⟩)) ?_
    simp only [Set.mem_ofPred_eq]
    have e : ∑ r ∈ freshRows s r0, ∏ i ∈ univ \ K,
        clamp01 (glueRows (sensRows s r0) f (restrOut (sensRows s r0) w) r i) =
        ∑ r ∈ univ.filter (fun r => r ∉ sensRows s r0), frRowM (univ \ K) (w r) := by
      unfold freshRows
      refine sum_congr rfl fun r hr => ?_
      unfold frRowM
      rw [frA_glue_fresh _ f w (mem_filter.1 hr).2]
    rwa [e] at hlt
  · refine (measure_biUnion_finset_le Kf _).trans ?_
    refine (sum_le_sum fun K hK => frC_fe4b_one s r0 K (mem_powersetCard.1 hK).2).trans ?_
    rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [card_powersetCard, card_univ, Fintype.card_fin]
    set d := dX N with hd
    have hdN : d ≤ N := by have := frC_dX_le N; omega
    have hch := frC_choose_le N
    rw [← hd] at hch
    have h3 : (1 / 3 : ℝ) ^ (N - d) = 3 ^ d / 3 ^ N := by
      have : (3 : ℝ) ^ N = 3 ^ d * 3 ^ (N - d) := by rw [← pow_add]; congr 1; omega
      rw [this, one_div_pow]; field_simp
    have hterm : (2 : ℝ) ^ N * (1 / 3) ^ (N - d) / ((2 : ℝ) ^ d) ^ 2 ≤ 2 ^ N / 3 ^ N := by
      rw [h3]
      have h34 : (3 : ℝ) ^ d ≤ ((2 : ℝ) ^ d) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) d
      have hp : (0 : ℝ) < ((2 : ℝ) ^ d) ^ 2 := by positivity
      rw [div_le_div_iff₀ hp (by positivity)]
      have : (2 : ℝ) ^ N * (3 ^ d / 3 ^ N) * 3 ^ N = 2 ^ N * 3 ^ d := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left h34 (by positivity)
    have hterm0 : 0 ≤ (2 : ℝ) ^ N * (1 / 3) ^ (N - d) / ((2 : ℝ) ^ d) ^ 2 := by positivity
    have hl2 := Real.log_two_lt_d9
    have hl3 := frC_log_three_gt
    have hd30 : (30 : ℝ) * d ≤ N + 29 := by exact_mod_cast frC_dX_le N
    have hN' : (100 : ℝ) ≤ N := by exact_mod_cast hN
    calc ((N.choose d : ℕ) : ℝ) * (2 ^ N * (1 / 3) ^ (N - d) / ((2 : ℝ) ^ d) ^ 2)
        ≤ (2 : ℝ) ^ (7 * d) * (2 ^ N / 3 ^ N) := mul_le_mul hch hterm hterm0 (by positivity)
      _ = Real.exp (((7 * d : ℕ) : ℝ) * Real.log 2 + N * Real.log 2 - N * Real.log 3) := by
          rw [Real.exp_sub, Real.exp_add, ← Real.log_rpow (by norm_num), ← Real.log_rpow (by norm_num),
            ← Real.log_rpow (by norm_num), Real.exp_log (by positivity), Real.exp_log (by positivity),
            Real.exp_log (by positivity), Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast]
          ring
      _ ≤ Real.exp (-(1 / 180 * N)) := by
          apply Real.exp_le_exp.2
          push_cast
          have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          nlinarith

/-! ### FE7(b)' -/

lemma frC_teW_glue (s r0 : State N) (f : sensRows s r0 → Fin N → ℝ) (g : {r // r ∉ sensRows s r0} → Fin N → ℝ) :
    teW (glueRows (sensRows s r0) f g) s =
      fun k => if 1 / 2 < clamp01 (f ⟨s, mem_sensRows_s s r0⟩ k) then s k else !s k := by
  unfold teW; rw [glueRows_of_mem _ f g (mem_sensRows_s s r0)]

lemma frC_sigN_sq (N : ℕ) : sigN N ^ 2 = (2 / 3 : ℝ) ^ N := by
  unfold sigN; rw [Real.sq_sqrt (by positivity)]

/-- **FE7(b)'**: Chebyshev, failure `≤ e^{-N/50}`. -/
theorem freshFE7b : FreshFieldProb FE7bX (1 / 180) := by
  refine Eventually.of_forall fun N s r0 f => ?_
  set te : State N := fun k => if 1 / 2 < clamp01 (f ⟨s, mem_sensRows_s s r0⟩ k) then s k else !s k
    with hte
  set b : Fin N → Bool := fun k => decide (te k = s k) with hb
  set c : ℝ := Real.exp ((N : ℝ) / 100) * sigN N with hc
  have hc0 : 0 < c := mul_pos (Real.exp_pos _) (sigN_pos N)
  refine (frA_transfer (sensRows s r0) f (FE7bX N s r0)
    (B := {w | 1 + c < ∑ r ∈ univ.filter (fun r => r ∉ sensRows s r0), frRowPhi b (w r)})
    fun w hw => ?_).trans ?_
  · simp only [FE7bX, not_le] at hw
    simp only [Set.mem_ofPred_eq]
    rw [frC_teW_glue] at hw
    have e : ∑ r ∈ freshRows s r0,
        rowTX (glueRows (sensRows s r0) f (restrOut (sensRows s r0) w)) s r te =
        ∑ r ∈ univ.filter (fun r => r ∉ sensRows s r0), frRowPhi b (w r) := by
      unfold freshRows
      refine sum_congr rfl fun r hr => ?_
      rw [rowTX_eq_frRowPhi, frA_glue_fresh _ f w (mem_filter.1 hr).2]
    rw [← hte] at hw
    rwa [e] at hw
  · refine (frC_cheb_fresh _ _ (measurable_frRowPhi b) (frRowPhi_mem b) (integral_frRowPhi b)
      (integral_frRowPhi_sq b) hc0 ?_).trans ?_
    · rw [← mul_pow]; norm_num
    · apply ENNReal.ofReal_le_ofReal
      have hsq : c ^ 2 = Real.exp ((N : ℝ) / 50) * (2 / 3 : ℝ) ^ N := by
        rw [hc, mul_pow, frC_sigN_sq, ← Real.exp_nat_mul]; congr 2; ring
      rw [hsq, ← mul_pow]
      have hp : (0 : ℝ) < (2 / 3 : ℝ) ^ N := by positivity
      have e2 : ((2 : ℝ) * (1 / 3)) ^ N / (Real.exp ((N : ℝ) / 50) * (2 / 3) ^ N) =
          Real.exp (-((N : ℝ) / 50)) := by
        rw [show (2 : ℝ) * (1 / 3) = 2 / 3 by norm_num, Real.exp_neg]; field_simp
      rw [e2]
      exact Real.exp_le_exp.2 (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; nlinarith)

end Census
end IIT

#print axioms IIT.Census.freshFE4a
#print axioms IIT.Census.freshFE4b
#print axioms IIT.Census.freshFE7b
