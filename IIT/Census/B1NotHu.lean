/-
Census, B1 forced leaf 7: **`NatNotHuStmt`** (W12 §2): in the natural regime a heavy current row `s ≠ tc`
(`P(s) > λ_u P(tc)`) is rare, at rate `1.03`, for ANY `λ_u > 0`.

On `bNat ∩ ¬H_u`, off the proved rare events (Tier 3 bound, concentration, tilt, LTβ):
* LTβ + B1 + Tier 3: `β/4 < φ(U) ≤ β Fᶜ_j`, so `Fᶜ_j > 1/4` and every entry of tc's row is `≥ 0.594`
  (`nh_floor`);
* tilt: `X(tc) ≤ x₀N + slT`; `¬H_u`: `X(s) < X(tc) + ln(1/λ_u)`.
Rows `tc ≠ s` are independent: `joint_template` with multipliers `6` (tilt) and `4` (row `s`) and the window
`y ≥ 0.594` gives `e^{6B + 4L} ((1 - f³)/15)^N` per row `tc`, and with the union over `tc` the rate is
`-ln(2 e^{6x₀}(1 - f³)/15) = -ln(0.45 (1 - f³)) ≥ 1.031` (`nh_rate_num`).

* `nh_two_rpow`, **`nh_floor`** (deterministic), **`nh_pair_bound`**, `nh_rate_num`,
  **`natNotHu_of`**: `NatTier3Stmt C'`, `LTBetaStmt (1/4) C'`, `LT2Stmt 1 C'` (`1.03 < C' ≤ 1.4`) give
  `NatNotHuStmt λ_u (103/100)`.
-/
import IIT.Census.B1Tier3NoLow

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- The floor constant. -/
noncomputable def nhF : ℝ := 297 / 500

lemma nh_two_rpow : (1189 / 1000 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 4) := by
  by_contra h
  push Not at h
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  have h4 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) ≤ (1189 / 1000 : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ h0 h 4
  rw [h4] at this
  norm_num at this

/-- **The raised floor** (deterministic): `Fᶜ_j > 1/4` and concentration give `y_{tc,j} ≥ 0.594`. -/
theorem nh_floor {s : State N} {w : Param N} (ho : w ∈ openCube N) (hDN : DU N ≤ N - 1)
    (hcC : concCAt N w (tcRow w)) (hδ : dU N (N - 1) ≤ 1 / 10000) {j : Fin N}
    (hF : 1 / 4 < kF (lamCz (flipP s w) s (tcRow w)) j) : nhF ≤ clamp01 (w (tcRow w) j) := by
  have hz : flipP s w ∈ openCube N := flipP_mem_openCube ho
  obtain ⟨mc1, -, mc3, -, mc5⟩ := lamCz_means hz s (tcRow w)
  rw [flipP_invol s w] at mc1 mc3 mc5
  have hk : kF (lamCz (flipP s w) s (tcRow w)) j =
      Real.logb 2 (clamp01 (w (tcRow w) j) / cmean w (univ \ univ.erase j) (tcRow w) j) := mc1 j (univ.erase j)
  rw [hk] at hF
  have hcard : (univ.erase j).card = N - 1 := by
    rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
  have hA := hcC j (univ.erase j) (notMem_erase j univ) (by rw [hcard]; exact hDN)
  rw [hcard] at hA
  have hAlo : 1 / 2 - 1 / 10000 ≤ cmean w (univ \ univ.erase j) (tcRow w) j := by
    have := (abs_le.1 hA).1; linarith
  have hA0 : 0 < cmean w (univ \ univ.erase j) (tcRow w) j := by linarith
  have hy0 := mc3 j
  have hpos : 0 < clamp01 (w (tcRow w) j) / cmean w (univ \ univ.erase j) (tcRow w) j := div_pos hy0 hA0
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) hpos, lt_div_iff₀ hA0] at hF
  have h2 := nh_two_rpow
  unfold nhF
  nlinarith

/-- **One pair of rows** (`r0 ≠ s`): window, tilt and heavy `s`. -/
theorem nh_pair_bound (hN : 2 ≤ N) {s r0 : State N} (hne : r0 ≠ s) (B L : ℝ) :
    cubeM N {w | (∀ i, nhF ≤ clamp01 (w r0 i)) ∧ XW w r0 ≤ B ∧ XW w s ≤ XW w r0 + L} ≤
      ENNReal.ofReal (Real.exp (6 * B + 4 * L) * ((1 - nhF ^ 3) / 15) ^ N) := by
  classical
  -- a third row
  obtain ⟨r1, hr1⟩ : ∃ r1 : State N, r1 ≠ r0 ∧ r1 ≠ s := by
    have hc : 2 < (univ : Finset (State N)).card := by
      rw [card_univ]; simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
    obtain ⟨r1, hr⟩ : ∃ r1 : State N, r1 ∉ ({r0, s} : Finset (State N)) := by
      by_contra h
      push Not at h
      have h1 : (univ : Finset (State N)) ⊆ {r0, s} := fun x _ => h x
      have h2 := card_le_card h1
      have h3 := card_le_two (a := r0) (b := s)
      omega
    refine ⟨r1, fun h => hr (by simp [h]), fun h => hr (by simp [h])⟩
  set ell : ℝ → ℝ := fun y => -Real.log (clamp01 y) with hell
  set ellU : ℝ → ℝ := fun y => -Real.log (clamp01 y) - L / N with hellU
  have hmn : Measurable fun y : ℝ => -Real.log (clamp01 y) := measurable_negLogClamp
  have hT := joint_template (fun _ => r0) (fun _ => r1) (fun _ => s) (fun _ => hr1.1.symm) (fun _ => hne)
    (fun _ => hr1.2) ell ellU (fun _ _ => 0) hmn (hmn.sub_const _) measurable_const
    {y | nhF ≤ clamp01 y} (measurableSet_le measurable_const continuous_clamp01.measurable)
    B 6 4 0 (by norm_num) (by norm_num) le_rfl
  have hN0 : (0 : ℝ) < N := by
    have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hsub : {w : Param N | (∀ i, nhF ≤ clamp01 (w r0 i)) ∧ XW w r0 ≤ B ∧ XW w s ≤ XW w r0 + L} ⊆
      {w | (∀ i, w r0 i ∈ {y | nhF ≤ clamp01 y}) ∧ ∑ i, ell (w r0 i) ≤ B ∧
        ∑ i, ellU (w s i) ≤ ∑ i, ell (w r0 i) ∧ ∑ _i : Fin N, (0 : ℝ) ≤ 0} := by
    rintro w ⟨hW, hB, hS⟩
    have e : ∑ i, ellU (w s i) = XW w s - L := by
      simp only [hellU, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      unfold XW; field_simp
    refine ⟨hW, hB, ?_, by simp⟩
    rw [e]
    have e2 : ∑ i, ell (w r0 i) = XW w r0 := rfl
    rw [e2]; linarith
  refine (measure_mono hsub).trans (hT.trans_eq ?_)
  -- the window integral `∫_{y ≥ f} y² = (1 - f³)/3`
  have hf0 : (0 : ℝ) < nhF := by unfold nhF; norm_num
  have hf1 : nhF ≤ 1 := by unfold nhF; norm_num
  have hone : ∫⁻ _u, ENNReal.ofReal (Real.exp (-0 * (fun _ _ => (0 : ℝ)) (0 : ℝ) (0 : ℝ))) ∂unif = 1 := by
    simp only [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, lintegral_const, one_mul]
    unfold unif; simp
  have hI1 : ∫⁻ y in {y | nhF ≤ clamp01 y}, ENNReal.ofReal (Real.exp ((4 - 6) * ell y)) *
      ∫⁻ u, ENNReal.ofReal (Real.exp (-0 * (fun _ _ => (0 : ℝ)) y u)) ∂unif ∂unif =
      ENNReal.ofReal ((1 - nhF ^ 3) / 3) := by
    have hT1 : MeasurableSet {y : ℝ | nhF ≤ clamp01 y} :=
      measurableSet_le measurable_const continuous_clamp01.measurable
    have hc : ∀ y ∈ {y : ℝ | nhF ≤ clamp01 y}, ENNReal.ofReal (Real.exp ((4 - 6) * ell y)) *
        ∫⁻ u, ENNReal.ofReal (Real.exp (-0 * (fun _ _ => (0 : ℝ)) y u)) ∂unif =
        ENNReal.ofReal (clamp01 y ^ 2) := by
      intro y hy
      have hy0 : 0 < clamp01 y := hf0.trans_le hy
      simp only [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, lintegral_const, one_mul]
      have hu : (unif : Measure ℝ) Set.univ = 1 := by unfold unif; simp
      rw [hu, mul_one, hell]
      congr 1
      rw [show (4 - 6 : ℝ) * -Real.log (clamp01 y) = 2 * Real.log (clamp01 y) by ring,
        show (2 : ℝ) * Real.log (clamp01 y) = ((2 : ℕ) : ℝ) * Real.log (clamp01 y) by norm_num,
        Real.exp_nat_mul, Real.exp_log hy0]
    rw [setLIntegral_congr_fun hT1 hc, ← lintegral_indicator hT1]
    have hind : ∀ y, ({y : ℝ | nhF ≤ clamp01 y}.indicator fun y => ENNReal.ofReal (clamp01 y ^ 2)) y =
        ((Set.Ici nhF).indicator fun u => ENNReal.ofReal (u ^ 2)) (clamp01 y) := by
      intro y
      by_cases h : nhF ≤ clamp01 y
      · rw [Set.indicator_of_mem (show y ∈ {y : ℝ | nhF ≤ clamp01 y} from h),
          Set.indicator_of_mem (show clamp01 y ∈ Set.Ici nhF from h)]
      · rw [Set.indicator_of_notMem (show y ∉ {y : ℝ | nhF ≤ clamp01 y} from h),
          Set.indicator_of_notMem (show clamp01 y ∉ Set.Ici nhF from h)]
    simp_rw [hind]
    rw [lintegral_unif_clamp (fun u => ((Set.Ici nhF).indicator fun u => ENNReal.ofReal (u ^ 2)) u),
      unif_eq_Ioc, lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    have hset : Set.Ici nhF ∩ Set.Ioc 0 1 = Set.Icc nhF 1 := by
      ext u; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, hf0.trans_le h1, h3⟩
    rw [hset, ← setLIntegral_congr Ioc_ae_eq_Icc,
      setLIntegral_Ioc_ofReal hf1 ((continuous_pow 2).intervalIntegrable _ _)
        (fun u hu => pow_nonneg (hf0.le.trans hu.1.le) _), integral_pow]
    congr 1; norm_num
  have hm4 : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp ((-4) * -Real.log (clamp01 x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hmn.const_mul _))
  have hI2 : ∫⁻ x, ENNReal.ofReal (Real.exp (-4 * ellU x)) ∂unif =
      ENNReal.ofReal (Real.exp (4 * L / N)) * ENNReal.ofReal (1 / 5) := by
    have e : ∀ x, ENNReal.ofReal (Real.exp (-4 * ellU x)) =
        ENNReal.ofReal (Real.exp (4 * L / N)) * ENNReal.ofReal (Real.exp ((-4) * -Real.log (clamp01 x))) := by
      intro x; rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; congr 2; simp only [hellU]; ring
    simp_rw [e]
    rw [lintegral_const_mul _ hm4, lintegral_unif_negLog (by norm_num)]
    norm_num
  have hq : 0 ≤ (1 - nhF ^ 3) / 3 := by unfold nhF; norm_num
  rw [hI1, hI2, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hq,
    ← ENNReal.ofReal_pow (mul_nonneg hq (by positivity)), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  have h4 : (N : ℝ) * (4 * L / N) = 4 * L := by field_simp
  have e3 : ((1 - nhF ^ 3) / 3 * (Real.exp (4 * L / N) * (1 / 5))) ^ N =
      Real.exp (4 * L) * ((1 - nhF ^ 3) / 15) ^ N := by
    rw [show (1 - nhF ^ 3) / 3 * (Real.exp (4 * L / N) * (1 / 5)) =
      Real.exp (4 * L / N) * ((1 - nhF ^ 3) / 15) by ring, mul_pow, ← Real.exp_nat_mul, h4]
  rw [e3, Real.exp_add]; ring

/-! ### Numerics -/

/-- `2 e^{6x₀} (1 - f³)/15 ≤ e^{-1.031}`. -/
lemma nh_rate_num : 2 * Real.exp (6 * x0) * ((1 - nhF ^ 3) / 15) ≤ Real.exp (-(1031 / 1000)) := by
  have h6 : Real.exp (6 * x0) = 27 / 8 := by
    unfold x0
    rw [show 6 * (Real.log (3 / 2) / 2) = ((3 : ℕ) : ℝ) * Real.log (3 / 2) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  rw [h6]
  have he1 := Real.exp_one_lt_d9
  have h31 : Real.exp (31 / 1000) * (969 / 1000) ≤ 1 := by
    have h := Real.add_one_le_exp (-(31 / 1000 : ℝ))
    have hm : Real.exp (31 / 1000) * Real.exp (-(31 / 1000)) = 1 := by rw [← Real.exp_add]; norm_num
    have hp := Real.exp_pos (31 / 1000 : ℝ)
    nlinarith
  have hsplit : Real.exp (1031 / 1000) = Real.exp 1 * Real.exp (31 / 1000) := by
    rw [← Real.exp_add]; norm_num
  have hpos := Real.exp_pos (1031 / 1000 : ℝ)
  have hup : Real.exp (1031 / 1000) ≤ 2806 / 1000 := by
    rw [hsplit]
    have hp := Real.exp_pos (31 / 1000 : ℝ)
    have he31 : Real.exp (31 / 1000) ≤ 1000 / 969 := by linarith
    calc Real.exp 1 * Real.exp (31 / 1000) ≤ 2.7182818286 * (1000 / 969) :=
          mul_le_mul he1.le he31 hp.le (by norm_num)
      _ ≤ 2806 / 1000 := by norm_num
  rw [Real.exp_neg, le_inv_comm₀ (by unfold nhF; norm_num) hpos]
  refine hup.trans ?_
  unfold nhF; norm_num

/-- `12 log N + K ≤ N / 2000` eventually. -/
lemma nh_poly (K : ℝ) : ∀ᶠ N : ℕ in atTop, 6 * slT N + K ≤ (N : ℝ) / 2000 := by
  have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 48000 by norm_num))
  filter_upwards [hev, eventually_ge_atTop (⌈4000 * (|K| + 120)⌉₊ + 1)] with N h1 hN
  have hNr : (⌈4000 * (|K| + 120)⌉₊ + 1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc := Nat.le_ceil (4000 * (|K| + 120))
  have hN0 : (0 : ℝ) < N := by have := abs_nonneg K; linarith
  simp only [Function.comp, pow_one, one_mul, add_zero] at h1
  rw [div_lt_iff₀ hN0] at h1
  unfold slT
  have := le_abs_self K
  nlinarith

/-! ### `NatNotHuStmt` -/

/-- **`¬H_u` is rare in the natural regime** (rate `1.03`, any `λ_u > 0`). -/
theorem natNotHu_of {lamU C' : ℝ} (hl : 0 < lamU) (hC1 : 103 / 100 < C') (hC2 : C' ≤ 14 / 10)
    (hT3 : NatTier3Stmt C') (hLTb : LTBetaStmt (1 / 4) C') (hLT2 : LT2Stmt 1 C') :
    NatNotHuStmt lamU (103 / 100) := by
  set Cm := min C' (10305 / 10000) with hCm
  have hCm1 : 103 / 100 < Cm := lt_min hC1 (by norm_num)
  have hCmC : Cm ≤ C' := min_le_left _ _
  have hCm2 : Cm ≤ 10305 / 10000 := min_le_right _ _
  set L := Real.log (1 / lamU) with hL
  filter_upwards [hT3, hLTb, tilt_bound hC2 hLT2, ev_N_dU_top, eventually_ge_atTop 64, g_superexp Cm,
    nh_poly (4 * L), g_absorb 7 hCm1] with N hT hLb hTl htop hN64 hS hpoly hA s
  classical
  have hN3 : 3 ≤ N := by omega
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hDN : DU N ≤ N - 1 := DU_le hN64
  have hδ : dU N (N - 1) ≤ 1 / 10000 := by
    have : dU N (N - 1) ≤ N * dU N (N - 1) := le_mul_of_one_le_left (dU_nonneg N _) (by linarith)
    linarith
  set B := x0 * N + slT N with hB
  set M : Set (Param N) := ⋃ r0 : State N, if r0 = s then ∅ else
    {w | (∀ i, nhF ≤ clamp01 (w r0 i)) ∧ XW w r0 ≤ B ∧ XW w s ≤ XW w r0 + L} with hM
  set c := 2 ^ N * (N * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2))) with hc
  have hsub : bNat N s ∩ {w | ¬ HuW s w lamU} ⊆
      (((bNat N s ∩ {w | ¬ ∀ j, phi (flipP s w) s univ ≤ betaW w * kF (lamCz (flipP s w) s (tcRow w)) j}) ∪
        {w | ¬ concCAt N w (tcRow w)}) ∪ (bTilt N s ∪ (B1w N s ∩ openCube N ∩
          {w | ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 1 / 4 * betaW w}))) ∪ M := by
    rintro w ⟨⟨⟨hBw, ho⟩, hNat⟩, hHu⟩
    by_contra hall
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, not_or, not_and, not_not, not_forall,
      not_lt] at hall
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hall
    have hT3w : ∀ j, phi (flipP s w) s univ ≤ betaW w * kF (lamCz (flipP s w) s (tcRow w)) j := by
      intro j; by_contra hc'; exact h1 ⟨⟨hBw, ho⟩, hNat⟩ ⟨j, by simpa using hc'⟩
    have hTilt : XW w (tcRow w) ≤ B := by
      by_contra ht; exact h3 ⟨⟨hBw, ho⟩, ht⟩
    obtain ⟨S, hS2, hS3, hSβ⟩ := h4 ⟨hBw, ho⟩
    simp only [HuW, not_or, not_le] at hHu
    obtain ⟨hne, hP⟩ := hHu
    -- the floor
    have hβ0 := betaW_pos ho
    have hlt := dt_B1_lt hBw (by rw [← card_pos]; omega) (dt_card_ne_univ hS3 (by omega))
    have hF : ∀ j, 1 / 4 < kF (lamCz (flipP s w) s (tcRow w)) j := by
      intro j
      have h := hT3w j
      by_contra hc'
      push Not at hc'
      have : betaW w * kF (lamCz (flipP s w) s (tcRow w)) j ≤ betaW w * (1 / 4) :=
        mul_le_mul_of_nonneg_left hc' hβ0.le
      linarith
    have hfl : ∀ i, nhF ≤ clamp01 (w (tcRow w) i) := fun i => nh_floor ho hDN h2 hδ (hF i)
    -- `X(s) ≤ X(tc) + L`
    have hpos : ∀ r i, 0 < clamp01 (w r i) := fun r i => by
      rw [b1_clamp01_of_mem_Ioo (ho _ i)]; exact (ho _ i).1
    rw [Pw_eq_exp_neg_XW (hpos _), Pw_eq_exp_neg_XW (hpos _)] at hP
    have hXs : XW w s ≤ XW w (tcRow w) + L := by
      have h1' : Real.log (lamU * Real.exp (-XW w (tcRow w))) < Real.log (Real.exp (-XW w s)) :=
        Real.log_lt_log (by positivity) hP
      rw [Real.log_mul hl.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at h1'
      have hL' : L = -Real.log lamU := by rw [hL, one_div, Real.log_inv]
      linarith
    apply h5
    refine Set.mem_iUnion.2 ⟨tcRow w, ?_⟩
    rw [if_neg (fun h => hne h.symm)]
    exact ⟨hfl, hTilt, hXs⟩
  -- the measure of `M`
  have hMb : cubeM N M ≤ ENNReal.ofReal (Real.exp (6 * slT N + 4 * L) * Real.exp (-(1031 / 1000 * (N : ℝ)))) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    have hone : ∀ r0 : State N, cubeM N (if r0 = s then ∅ else
        {w | (∀ i, nhF ≤ clamp01 (w r0 i)) ∧ XW w r0 ≤ B ∧ XW w s ≤ XW w r0 + L}) ≤
        ENNReal.ofReal (Real.exp (6 * B + 4 * L) * ((1 - nhF ^ 3) / 15) ^ N) := by
      intro r0
      split_ifs with h
      · simp
      · exact nh_pair_bound (by omega) h B L
    refine (Finset.sum_le_sum fun r0 _ => hone r0).trans ?_
    rw [sum_const, card_state, nsmul_eq_mul]
    have h2 : ((2 ^ N : ℕ) : ENNReal) = ENNReal.ofReal ((2 : ℝ) ^ N) := by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp
    have hq0 : 0 ≤ (1 - nhF ^ 3) / 15 := by unfold nhF; norm_num
    rw [h2, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hr0 : 0 ≤ 2 * Real.exp (6 * x0) * ((1 - nhF ^ 3) / 15) := by positivity
    have key : (2 : ℝ) ^ N * (Real.exp (6 * B + 4 * L) * ((1 - nhF ^ 3) / 15) ^ N) =
        Real.exp (6 * slT N + 4 * L) * (2 * Real.exp (6 * x0) * ((1 - nhF ^ 3) / 15)) ^ N := by
      rw [hB, mul_pow, mul_pow, ← Real.exp_nat_mul,
        show 6 * (x0 * N + slT N) + 4 * L = (6 * slT N + 4 * L) + N * (6 * x0) by ring, Real.exp_add]
      ring
    rw [key]
    refine mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hr0 nh_rate_num N).trans (le_of_eq ?_))
      (Real.exp_pos _).le
    rw [← Real.exp_nat_mul]; ring_nf
  -- the total
  have hNr0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hE1 : Real.exp (-(C' * N)) ≤ Real.exp (-(Cm * N)) := Real.exp_le_exp.2 (by nlinarith)
  have hE2 : Real.exp (6 * slT N + 4 * L) * Real.exp (-(1031 / 1000 * (N : ℝ))) ≤ Real.exp (-(Cm * N)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
  have hc0 : 0 ≤ c := by positivity
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add (hT s) (concTc_rare hN3 s))) ((measure_union_le _ _).trans (add_le_add (hTl s) (hLb s)))))
    hMb).trans ?_
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le hc0, ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le,
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hS' : 2 * c ≤ Real.exp (-(Cm * N)) := hS
  have hA' : 7 * Real.exp (-(Cm * N)) ≤ Real.exp (-(103 / 100 * N)) := hA
  have := Real.exp_pos (-(C' * N))
  linarith

end Census
end IIT
