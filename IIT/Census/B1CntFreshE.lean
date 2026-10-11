/-
Census, B1, W14 WP4, part E: FE5 (near-full normalisers).

For `|K| = d`, `M = U \ K`, `N - J ≤ |Z| = l < N`: the `2^l` subcubes `agree Z y` (`y` a representative,
`y = false` off `Z`) are pairwise disjoint; at least `2^l - |Sens| ≥ 2^{l-1}` of them avoid `Sens`; on those
`Y_y = Π_{i ∈ M} Ā_i(agree Z y) ∈ [0,1]` are independent (disjoint row blocks, `iIndepFun_pi_blocks`) with
mean `2^{-m}` (column independence).  `multChernoff_lower` with `m0 = 2^l / 2^{m+1}` gives
`P ≤ e^{-m0/8} ≤ e^{-2N}` (`m0/8 ≥ 2^d / 2^{J+4}`), union over `≤ 4^N` pairs `(K, Z)`.
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §9; math W5 §4 FE5, W9 §5.1.  No `sorry`.
-/
import IIT.Census.B1CntFreshD

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### Representatives of the subcubes `agree Z ·` -/

/-- Representatives: patterns that are `false` off `Z`. -/
noncomputable def frR (Z : Finset (Fin N)) : Finset (State N) := agree Zᶜ (fun _ => false)

/-- Representatives whose subcube avoids `F`. -/
noncomputable def frFR (F : Finset (State N)) (Z : Finset (Fin N)) : Finset (State N) :=
  (frR Z).filter fun y => ∀ r ∈ agree Z y, r ∉ F

/-- The representative of a row. -/
def frRho (Z : Finset (Fin N)) (r : State N) : State N := fun j => if j ∈ Z then r j else false

/-- `Y_y = Π_{i ∈ M} Ā_i(agree Z y)`. -/
noncomputable def frY (M Z : Finset (Fin N)) (y : State N) (w : Param N) : ℝ :=
  ∏ i ∈ M, cmCol Z y (colsOf w i)

lemma card_frR (Z : Finset (Fin N)) : (frR Z).card = 2 ^ Z.card := by
  unfold frR; rw [card_agree, card_compl, Fintype.card_fin]
  congr 1; have := Z.card_le_univ; rw [Fintype.card_fin] at this; omega

lemma agree_eq_of_mem {Z : Finset (Fin N)} {y z : State N} (hz : z ∈ agree Z y) :
    agree Z z = agree Z y := by
  ext r
  simp only [mem_agree] at hz ⊢
  exact ⟨fun h j hj => (h j hj).trans (hz j hj), fun h j hj => (h j hj).trans (hz j hj).symm⟩

lemma frR_eq_of_agree {Z : Finset (Fin N)} {y y' : State N} (hy : y ∈ frR Z) (hy' : y' ∈ frR Z)
    {r : State N} (hr : r ∈ agree Z y) (hr' : r ∈ agree Z y') : y = y' := by
  unfold frR at hy hy'
  rw [mem_agree] at hy hy' hr hr'
  funext j
  by_cases hj : j ∈ Z
  · exact (hr j hj).symm.trans (hr' j hj)
  · rw [hy j (mem_compl.2 hj), hy' j (mem_compl.2 hj)]

lemma frR_disjoint {Z : Finset (Fin N)} {y y' : State N} (hy : y ∈ frR Z) (hy' : y' ∈ frR Z)
    (hne : y ≠ y') : Disjoint (agree Z y) (agree Z y') := by
  rw [Finset.disjoint_left]
  intro r hr hr'
  exact hne (frR_eq_of_agree hy hy' hr hr')

lemma frRho_mem (Z : Finset (Fin N)) (r : State N) : frRho Z r ∈ frR Z := by
  unfold frR frRho; rw [mem_agree]; intro j hj
  simp [mem_compl.1 hj]

lemma frRho_eq {Z : Finset (Fin N)} {y r : State N} (hy : y ∈ frR Z) (hr : r ∈ agree Z y) :
    frRho Z r = y :=
  frR_eq_of_agree (frRho_mem Z r) hy (by unfold frRho; rw [mem_agree]; intro j hj; simp [hj]) hr

lemma card_frFR_ge (F : Finset (State N)) (Z : Finset (Fin N)) :
    (2 : ℝ) ^ Z.card - F.card ≤ (frFR F Z).card := by
  have h := card_filter_add_card_filter_not (s := frR Z) (fun y => ∀ r ∈ agree Z y, r ∉ F)
  rw [card_frR] at h
  have hsub : (frR Z).filter (fun y => ¬ ∀ r ∈ agree Z y, r ∉ F) ⊆ F.image (frRho Z) := by
    intro y hy
    rw [mem_filter] at hy
    obtain ⟨hyR, hy⟩ := hy
    simp only [not_forall, not_not] at hy
    obtain ⟨r, hr, hrF⟩ := hy
    exact mem_image.2 ⟨r, hrF, frRho_eq hyR hr⟩
  have h2 := (card_le_card hsub).trans card_image_le
  have h3 : ((frFR F Z).card : ℝ) + ((frR Z).filter (fun y => ¬ ∀ r ∈ agree Z y, r ∉ F)).card =
      2 ^ Z.card := by unfold frFR; exact_mod_cast h
  have h4 : (((frR Z).filter (fun y => ¬ ∀ r ∈ agree Z y, r ∉ F)).card : ℝ) ≤ F.card := by
    exact_mod_cast h2
  linarith

/-- Lower bound of the full pattern sum by the fresh representatives. -/
lemma frE_sum_ge {Z : Finset (Fin N)} (φ : State N → ℝ) (hφ0 : ∀ z, 0 ≤ φ z)
    (hφ : ∀ y z, z ∈ agree Z y → φ z = φ y) (S : Finset (State N)) (hS : S ⊆ frR Z) :
    (2 : ℝ) ^ (N - Z.card) * ∑ y ∈ S, φ y ≤ ∑ z : State N, φ z := by
  have hdisj : Set.PairwiseDisjoint (↑S) (fun y => agree Z y) := by
    intro y hy y' hy' hne
    exact frR_disjoint (hS hy) (hS hy') hne
  calc (2 : ℝ) ^ (N - Z.card) * ∑ y ∈ S, φ y = ∑ y ∈ S, ∑ z ∈ agree Z y, φ z := by
        rw [mul_sum]
        refine sum_congr rfl fun y _ => ?_
        rw [sum_congr rfl fun z hz => hφ y z hz, sum_const, card_agree, nsmul_eq_mul]
        push_cast; ring
    _ = ∑ z ∈ S.biUnion (fun y => agree Z y), φ z := (sum_biUnion hdisj).symm
    _ ≤ ∑ z : State N, φ z := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun z _ _ => hφ0 z

/-! ### Moments and independence of the `Y_y` -/

lemma frY_mem (M Z : Finset (Fin N)) (y : State N) (w : Param N) :
    frY M Z y w ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨prod_nonneg fun i _ => cmCol_nonneg _ _ _,
    prod_le_one (fun i _ => cmCol_nonneg _ _ _) fun i _ => cmCol_le_one _ _ _⟩

lemma measurable_frY (M Z : Finset (Fin N)) (y : State N) : Measurable (frY M Z y) :=
  Finset.measurable_prod _ fun i _ => (measurable_cmCol Z y).comp (measurable_colOf i)

lemma frE_integral_cmCol (Z : Finset (Fin N)) (y : State N) : ∫ c, cmCol Z y c ∂colLaw N = 1 / 2 := by
  unfold cmCol
  rw [integral_div, integral_finsetSum _ fun r _ => integrable_col_cl r,
    sum_congr rfl fun r _ => integral_col r, sum_const, card_agree, nsmul_eq_mul]
  push_cast
  field_simp

lemma integral_frY (M Z : Finset (Fin N)) (y : State N) :
    ∫ w, frY M Z y w ∂cubeM N = (1 / 2) ^ M.card := by
  set g : Fin N → (State N → ℝ) → ℝ := fun i c => if i ∈ M then cmCol Z y c else 1 with hg
  have hgm : ∀ i, Measurable (g i) := fun i => by
    by_cases h : i ∈ M
    · simp only [hg, h, ite_true]; exact measurable_cmCol Z y
    · simp only [hg, h, ite_false]; exact measurable_const
  have e : ∀ w : Param N, frY M Z y w = ∏ i, g i (colsOf w i) := by
    intro w; unfold frY; simp only [hg]; rw [prod_ite_mem_eq]
  simp_rw [e]
  rw [iIndepFun_cols.integral_fun_prod_comp (fun i => (measurable_colOf i).aemeasurable)
    (fun i => (hgm i).aestronglyMeasurable)]
  have hfac : ∀ i, ∫ w, g i (colsOf w i) ∂cubeM N = if i ∈ M then 1 / 2 else 1 := by
    intro i
    rw [← integral_map (mp_colOf i).measurable.aemeasurable (hgm i).aestronglyMeasurable,
      (mp_colOf i).map_eq]
    by_cases h : i ∈ M
    · simp only [hg, h, ite_true]; exact frE_integral_cmCol Z y
    · simp [hg, h]
  simp_rw [hfac]
  rw [prod_ite_mem_eq, prod_const]

/-- **One pair `(K, Z)`**: `P(Σ_{y fresh} Y_y ≤ m0/2) ≤ e^{-m0/8}`. -/
lemma frE_fe5_one (F : Finset (State N)) (M Z : Finset (Fin N)) {m0 : ℝ} (hm0 : 0 ≤ m0)
    (hmean : m0 ≤ (frFR F Z).card * (1 / 2 : ℝ) ^ M.card) :
    cubeM N {w | ∑ y ∈ frFR F Z, frY M Z y w ≤ m0 / 2} ≤
      ENNReal.ofReal (Real.exp (-(m0 / 8))) := by
  set S := frFR F Z with hS
  set X : State N → Param N → ℝ := fun y w => if y ∈ S then frY M Z y w else 0 with hX
  set C : State N → Finset (State N) := fun y => if y ∈ S then agree Z y else ∅ with hC
  have hSR : S ⊆ frR Z := filter_subset _ _
  have hXm : ∀ y, Measurable (X y) := fun y => by
    by_cases h : y ∈ S
    · simp only [hX, h, ite_true]; exact measurable_frY M Z y
    · simp only [hX, h, ite_false]; exact measurable_const
  have hXb : ∀ y w, X y w ∈ Set.Icc (0 : ℝ) 1 := fun y w => by
    by_cases h : y ∈ S
    · simp only [hX, h, ite_true]; exact frY_mem M Z y w
    · simp only [hX, h, ite_false]; exact ⟨le_rfl, zero_le_one⟩
  have hind : iIndepFun X (cubeM N) := by
    have e : cubeM N = Measure.pi (fun _ : State N => rowM N) := rfl
    rw [e]
    refine iIndepFun_pi_blocks (fun _ : State N => rowM N) C ?_ hXm ?_
    · intro y y' hne
      by_cases h : y ∈ S
      · by_cases h' : y' ∈ S
        · simp only [hC, h, h', ite_true]; exact frR_disjoint (hSR h) (hSR h') hne
        · simp only [hC, h', ite_false]; exact disjoint_empty_right _
      · simp only [hC, h, ite_false]; exact disjoint_empty_left _
    · intro y ω ω' hω
      by_cases h : y ∈ S
      · simp only [hX, h, ite_true]
        unfold frY cmCol colsOf
        refine prod_congr rfl fun i _ => ?_
        congr 1
        refine sum_congr rfl fun r hr => ?_
        rw [hω r (by simp only [hC, h, ite_true]; exact hr)]
      · simp only [hX, h, ite_false]
  have hmean' : m0 ≤ ∑ y ∈ S, ∫ w, X y w ∂cubeM N := by
    have : ∑ y ∈ S, ∫ w, X y w ∂cubeM N = S.card * (1 / 2 : ℝ) ^ M.card := by
      rw [sum_congr rfl fun y hy => by simp only [hX, hy, ite_true]; exact integral_frY M Z y,
        sum_const, nsmul_eq_mul]
    rw [this]; exact hmean
  have h := multChernoff_lower (μ := cubeM N) S hind hXm hXb hm0 hmean'
  have hset : {w : Param N | ∑ y ∈ S, frY M Z y w ≤ m0 / 2} = {w | ∑ y ∈ S, X y w ≤ m0 / 2} := by
    ext w
    simp only [Set.mem_ofPred_eq]
    have e : ∑ y ∈ S, X y w = ∑ y ∈ S, frY M Z y w :=
      sum_congr rfl fun y hy => by simp only [hX, hy, ite_true]
    rw [e]
  rw [hset]; exact h

/-! ### Eventual numerics -/

lemma frE_two_pow_J (hN : 1 ≤ N) : (2 : ℝ) ^ JC N ≤ 2 ^ 16 * (N : ℝ) ^ 6 := by
  have h : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hr : (2 : ℝ) ^ Nat.log 2 N ≤ N := by exact_mod_cast h
  unfold JC
  rw [pow_add, pow_mul', mul_comm]
  gcongr

lemma frE_ev1 : ∀ᶠ N : ℕ in atTop, 4 * ((N : ℝ) + 1) ^ 4 * 2 ^ JC N ≤ 2 ^ N := by
  filter_upwards [eventually_ge_atTop 1, frA_ev_logsq 13 10 (δ := 1 / 2) (by norm_num)] with N hN hev
  have hJ := frE_two_pow_J hN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow := frA_pow_le_exp hN 10
  have hL := frA_log_nonneg N
  have h13 : (2 : ℝ) ^ 18 ≤ Real.exp 13 := by
    have := frB_two_pow_le 18
    exact this.trans (Real.exp_le_exp.2 (by norm_num))
  have h2N : Real.exp (1 / 2 * N) ≤ (2 : ℝ) ^ N := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ N), Real.log_pow]
    apply Real.exp_le_exp.2
    have := Real.log_two_gt_d9
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hN6 : (N : ℝ) ^ 6 ≤ ((N : ℝ) + 1) ^ 6 := pow_le_pow_left₀ (by positivity) (by linarith) 6
  calc 4 * ((N : ℝ) + 1) ^ 4 * 2 ^ JC N ≤ 4 * ((N : ℝ) + 1) ^ 4 * (2 ^ 16 * ((N : ℝ) + 1) ^ 6) := by
        gcongr; exact hJ.trans (by gcongr)
    _ = 2 ^ 18 * ((N : ℝ) + 1) ^ 10 := by ring
    _ ≤ Real.exp 13 * Real.exp (((10 : ℕ) : ℝ) * (Real.log N + 1)) := by gcongr
    _ = Real.exp (13 + 10 * (Real.log N + 1)) := by rw [← Real.exp_add]; push_cast; ring_nf
    _ ≤ Real.exp (1 / 2 * N) := Real.exp_le_exp.2 (by nlinarith)
    _ ≤ 2 ^ N := h2N

lemma frE_ev2 : ∀ᶠ N : ℕ in atTop, 2 * (N : ℝ) * 2 ^ (JC N + 4) ≤ 2 ^ dX N := by
  filter_upwards [eventually_ge_atTop 1, frA_ev_logsq 15 7 (δ := 1 / 45) (by norm_num)] with N hN hev
  have hJ := frE_two_pow_J hN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow := frA_pow_le_exp hN 7
  have hL := frA_log_nonneg N
  have h15 : (2 : ℝ) ^ 21 ≤ Real.exp 15 := by
    have := frB_two_pow_le 21
    exact this.trans (Real.exp_le_exp.2 (by norm_num))
  have hd : (N : ℝ) ≤ 30 * dX N := by exact_mod_cast frC_dX_ge N
  have h2d : Real.exp (1 / 45 * N) ≤ (2 : ℝ) ^ dX N := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ dX N), Real.log_pow]
    apply Real.exp_le_exp.2
    have := Real.log_two_gt_d9
    have h0 : (0 : ℝ) ≤ dX N := Nat.cast_nonneg _
    nlinarith
  have hN7 : (N : ℝ) ^ 7 ≤ ((N : ℝ) + 1) ^ 7 := pow_le_pow_left₀ (by positivity) (by linarith) 7
  calc 2 * (N : ℝ) * 2 ^ (JC N + 4) = 2 ^ 5 * N * 2 ^ JC N := by rw [pow_add]; ring
    _ ≤ 2 ^ 5 * N * (2 ^ 16 * (N : ℝ) ^ 6) := by gcongr
    _ = 2 ^ 21 * (N : ℝ) ^ 7 := by ring
    _ ≤ Real.exp 15 * Real.exp (((7 : ℕ) : ℝ) * (Real.log N + 1)) := by gcongr; exact hN7.trans hpow
    _ = Real.exp (15 + 7 * (Real.log N + 1)) := by rw [← Real.exp_add]; push_cast; ring_nf
    _ ≤ Real.exp (1 / 45 * N) := Real.exp_le_exp.2 (by nlinarith)
    _ ≤ 2 ^ dX N := h2d

/-! ### FE5 -/

/-- **FE5**: failure `≤ 4^N e^{-2N}` (eventually; the true bound is doubly exponential). -/
theorem freshFE5 : FreshFieldProb FE5X (1 / 180) := by
  filter_upwards [eventually_ge_atTop 1, frE_ev1, frE_ev2] with N hN h1 h2 s r0 f
  set d := dX N with hd
  have hdN : d ≤ N := by have := frC_dX_le N; omega
  set Kf := (univ : Finset (Fin N)).powersetCard d with hKf
  set 𝒵 := (univ : Finset (Finset (Fin N))).filter fun Z => N ≤ Z.card + JC N ∧ Z.card < N with h𝒵
  set m0 : Finset (Fin N) → ℝ := fun Z => (2 : ℝ) ^ Z.card / 2 ^ (N - d + 1) with hm0
  have hFc : ((sensRows s r0).card : ℝ) ≤ 2 * ((N : ℝ) + 1) ^ 4 := by
    have := card_sensRows_le s r0; exact_mod_cast this
  -- the per-`Z` facts
  have hZbig : ∀ Z ∈ 𝒵, (2 : ℝ) ^ N ≤ 2 ^ Z.card * 2 ^ JC N := by
    intro Z hZ
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (mem_filter.1 hZ).2.1
  refine (frA_transfer (sensRows s r0) f (FE5X N s r0)
    (B := ⋃ K ∈ Kf, ⋃ Z ∈ 𝒵, {w | ∑ y ∈ frFR (sensRows s r0) Z, frY (univ \ K) Z y w ≤ m0 Z / 2})
    fun w hw => ?_).trans ?_
  · simp only [FE5X, not_forall, not_le, exists_prop] at hw
    obtain ⟨K, hK, Z, hZJ, hZN, hlt⟩ := hw
    refine Set.mem_biUnion (x := K) (Finset.mem_coe.2 (mem_powersetCard.2 ⟨subset_univ _, hK⟩)) ?_
    refine Set.mem_biUnion (x := Z) (Finset.mem_coe.2 (mem_filter.2 ⟨mem_univ _, hZJ, hZN⟩)) ?_
    simp only [Set.mem_ofPred_eq]
    set wg := glueRows (sensRows s r0) f (restrOut (sensRows s r0) w) with hwg
    set φ : State N → ℝ := fun z => ∏ i ∈ univ \ K, subMean wg Z z i with hφ
    have hφ0 : ∀ z, 0 ≤ φ z := fun z => prod_nonneg fun i _ => by
      rw [subMean_eq_colMean, colMean_eq_cmCol]; exact cmCol_nonneg _ _ _
    have hφc : ∀ y z, z ∈ agree Z y → φ z = φ y := by
      intro y z hz
      simp only [hφ]
      refine prod_congr rfl fun i _ => ?_
      unfold subMean; rw [agree_eq_of_mem hz]
    have hfr : ∀ y ∈ frFR (sensRows s r0) Z, φ y = frY (univ \ K) Z y w := by
      intro y hy
      have hyf := (mem_filter.1 hy).2
      simp only [hφ]; unfold frY
      refine prod_congr rfl fun i _ => ?_
      rw [subMean_eq_colMean, colMean_eq_cmCol]
      unfold cmCol colsOf
      congr 1
      exact sum_congr rfl fun r hr => by rw [hwg, frA_glue_fresh _ f w (hyf r hr)]
    have hge := frE_sum_ge φ hφ0 hφc (frFR (sensRows s r0) Z) (filter_subset _ _)
    rw [sum_congr rfl hfr] at hge
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    have hZle : Z.card ≤ N := hZN.le
    have hsplit : (2 : ℝ) ^ N = 2 ^ (N - Z.card) * 2 ^ Z.card := by
      rw [← pow_add]; congr 1; omega
    have hP : (∑ z : State N, φ z) * 2 ^ (N - d + 2) < 2 ^ N := by
      have h := hlt
      rw [div_lt_div_iff₀ h2N (by positivity), one_mul] at h
      exact h
    have hS : (∑ y ∈ frFR (sensRows s r0) Z, frY (univ \ K) Z y w) * 2 ^ (N - d + 2) < 2 ^ Z.card := by
      have hpos : (0 : ℝ) < 2 ^ (N - Z.card) := by positivity
      have h3 : 2 ^ (N - Z.card) * ((∑ y ∈ frFR (sensRows s r0) Z, frY (univ \ K) Z y w) * 2 ^ (N - d + 2)) <
          2 ^ (N - Z.card) * 2 ^ Z.card := by
        calc 2 ^ (N - Z.card) * ((∑ y ∈ frFR (sensRows s r0) Z, frY (univ \ K) Z y w) * 2 ^ (N - d + 2))
            = (2 ^ (N - Z.card) * ∑ y ∈ frFR (sensRows s r0) Z, frY (univ \ K) Z y w) * 2 ^ (N - d + 2) := by ring
          _ ≤ (∑ z : State N, φ z) * 2 ^ (N - d + 2) :=
              mul_le_mul_of_nonneg_right hge (by positivity)
          _ < 2 ^ N := hP
          _ = 2 ^ (N - Z.card) * 2 ^ Z.card := hsplit
      exact lt_of_mul_lt_mul_left h3 hpos.le
    simp only [hm0]
    have e2 : (2 : ℝ) ^ (N - d + 1) * 2 = 2 ^ (N - d + 2) := by
      rw [← pow_succ]
    rw [div_div, e2, le_div_iff₀ (by positivity)]
    exact hS.le
  · have hone : ∀ K ∈ Kf, ∀ Z ∈ 𝒵, cubeM N {w | ∑ y ∈ frFR (sensRows s r0) Z, frY (univ \ K) Z y w ≤ m0 Z / 2} ≤
        ENNReal.ofReal (Real.exp (-(2 * N))) := by
      intro K hK Z hZ
      have hKc : K.card = d := (mem_powersetCard.1 hK).2
      have hMc : (univ \ K).card = N - d := by
        rw [card_sdiff_of_subset (subset_univ K), card_univ, Fintype.card_fin, hKc]
      have hm0nn : 0 ≤ m0 Z := by simp only [hm0]; positivity
      have hJp : (0 : ℝ) < 2 ^ JC N := by positivity
      have hZb := hZbig Z hZ
      have h4 : 4 * ((N : ℝ) + 1) ^ 4 ≤ 2 ^ Z.card := by
        by_contra hc
        have hc' := mul_lt_mul_of_pos_right (not_le.mp hc) hJp
        linarith
      have hcard : (2 : ℝ) ^ Z.card / 2 ≤ (frFR (sensRows s r0) Z).card := by
        have := card_frFR_ge (sensRows s r0) Z; linarith
      have hmean : m0 Z ≤ (frFR (sensRows s r0) Z).card * (1 / 2 : ℝ) ^ (univ \ K).card := by
        rw [hMc]
        calc m0 Z = 2 ^ Z.card / 2 * (1 / 2 : ℝ) ^ (N - d) := by
              simp only [hm0]; rw [pow_succ, one_div_pow]; field_simp
          _ ≤ (frFR (sensRows s r0) Z).card * (1 / 2 : ℝ) ^ (N - d) := by gcongr
      refine (frE_fe5_one (sensRows s r0) (univ \ K) Z hm0nn hmean).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
      have hX : 2 * (N : ℝ) * 2 ^ (JC N + 4) * 2 ^ (N - d) ≤ 2 ^ Z.card * 2 ^ JC N := by
        calc 2 * (N : ℝ) * 2 ^ (JC N + 4) * 2 ^ (N - d) ≤ 2 ^ d * 2 ^ (N - d) := by gcongr
          _ = 2 ^ N := by rw [← pow_add]; congr 1; omega
          _ ≤ _ := hZb
      have hY : 2 * (N : ℝ) * 16 * 2 ^ (N - d) ≤ 2 ^ Z.card := by
        have e : 2 * (N : ℝ) * 2 ^ (JC N + 4) * 2 ^ (N - d) =
            (2 * (N : ℝ) * 16 * 2 ^ (N - d)) * 2 ^ JC N := by rw [pow_add]; ring
        rw [e] at hX
        exact le_of_mul_le_mul_right hX hJp
      have hm8 : 2 * (N : ℝ) ≤ m0 Z / 8 := by
        simp only [hm0]
        have e : (2 : ℝ) ^ Z.card / 2 ^ (N - d + 1) / 8 = 2 ^ Z.card / (2 ^ (N - d) * 16) := by
          rw [pow_succ]; field_simp; ring
        rw [e, le_div_iff₀ (by positivity)]
        linarith
      linarith
    refine (measure_biUnion_finset_le Kf _).trans ?_
    refine (sum_le_sum fun K hK => (measure_biUnion_finset_le 𝒵 _).trans
      (sum_le_sum fun Z hZ => hone K hK Z hZ)).trans ?_
    rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hK2 : (Kf.card : ℝ) ≤ 2 ^ N := by
      rw [hKf, card_powersetCard, card_univ, Fintype.card_fin]
      exact_mod_cast Nat.choose_le_two_pow N d
    have hZ2 : (𝒵.card : ℝ) ≤ 2 ^ N := by
      have : 𝒵.card ≤ 2 ^ N := (card_filter_le _ _).trans (by simp)
      exact_mod_cast this
    have h7 := frB_two_pow_le N
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    calc (Kf.card : ℝ) * ((𝒵.card : ℝ) * Real.exp (-(2 * N)))
        ≤ Real.exp (7 / 10 * N) * (Real.exp (7 / 10 * N) * Real.exp (-(2 * N))) := by
          gcongr
          · exact hK2.trans h7
          · exact hZ2.trans h7
      _ = Real.exp (-(6 / 10 * N)) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-(1 / 180 * N)) := Real.exp_le_exp.2 (by linarith)

end Census
end IIT

#print axioms IIT.Census.freshFE5
