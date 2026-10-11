/-
Census, B1 small cuts (W12 §6): **the effect side** (`smallE` at `teW`, `2 ≤ |K| < D`).

At `teW` the centre value is `x = max(y_s, 1 - y_s)` and the subcube terms are `p(r, teW_j)`, i.e. `y_r` when
`y_s > 1/2` and `1 - y_r` otherwise. Hence the effect integrand of a column is the cause integrand (centre `s`)
of the column or of the reflected column `1 - c`; the column law is reflection invariant, so the per-column
integral is at most `2 R` (`sce_col_bound`). The rest is the cause argument with the link tilt
`Σ -ln x ≤ x₀ N + 2 slT` and no union over the centre row.
-/
import IIT.Census.B1SmallCutCause
import IIT.Census.B1ForcedDRet

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- The reflected column. -/
def colRefl (c : State N → ℝ) : State N → ℝ := fun r => 1 - c r

lemma colRefl_mp : MeasurePreserving (colRefl (N := N)) (colLaw N) (colLaw N) := by
  unfold colLaw
  exact measurePreserving_pi (fun _ => unif) (fun _ => unif) fun _ => dr_unif_mp

/-- The effect centre value of a column. -/
noncomputable def sceX (s : State N) (c : State N → ℝ) : ℝ := max (clamp01 (c s)) (1 - clamp01 (c s))

/-- The effect subcube mean of a column. -/
noncomputable def sceA (s : State N) (K : Finset (Fin N)) (c : State N → ℝ) : ℝ :=
  if 1 / 2 < clamp01 (c s) then scX s K c else scX s K (colRefl c)

/-- The per-column effect small-cut term. -/
noncomputable def sceV (s : State N) (K : Finset (Fin N)) (mp : ℝ) (c : State N → ℝ) : ℝ :=
  min (Real.logb 2 (sceX s c / sceA s K c)) (Real.logb 2 (sceX s c / mp))

lemma sce_refl_clamp (c : State N → ℝ) (r : State N) : clamp01 (colRefl c r) = 1 - clamp01 (c r) :=
  clamp01_one_sub _

/-- **The per-column effect bound: at most twice the cause bound.** -/
theorem sce_col_bound (s : State N) (K : Finset (Fin N)) {a b : Fin N} (hab : ({a, b} : Finset (Fin N)) ⊆ K)
    (hne : a ≠ b) {m mp : ℝ} (hm : 0 < m) (hmp : 0 < mp) (n μ : ℕ) :
    ∫⁻ c, {c : State N → ℝ | m ≤ sceX s c}.indicator (fun c => ENNReal.ofReal (Real.exp
        (-((n : ℝ) * Real.log 2 * sceV s K mp c + μ * -Real.log (sceX s c))))) c ∂colLaw N ≤
      2 * ∫⁻ u, {u : ℝ | m ≤ clamp01 u}.indicator (fun u => ENNReal.ofReal (scG mp n μ (clamp01 u))) u ∂unif := by
  set g : (State N → ℝ) → ENNReal := fun c => {c : State N → ℝ | m ≤ clamp01 (c s)}.indicator
    (fun c => ENNReal.ofReal (Real.exp (-((n : ℝ) * Real.log 2 * min (Real.logb 2 (clamp01 (c s) / scX s K c))
      (Real.logb 2 (clamp01 (c s) / mp)) + μ * -Real.log (clamp01 (c s)))))) c with hg
  have hgm : Measurable g := by
    have hy : Measurable fun c : State N → ℝ => clamp01 (c s) :=
      continuous_clamp01.measurable.comp (measurable_pi_apply s)
    refine Measurable.indicator ?_ (measurableSet_le measurable_const hy)
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.neg ?_))
    unfold Real.logb
    exact (measurable_const.mul ((((hy.div (measurable_scX s K)).log).div_const _).min
      (((hy.div_const mp).log).div_const _))).add (measurable_const.mul hy.log.neg)
  have hpt : ∀ c, {c : State N → ℝ | m ≤ sceX s c}.indicator (fun c => ENNReal.ofReal (Real.exp
      (-((n : ℝ) * Real.log 2 * sceV s K mp c + μ * -Real.log (sceX s c))))) c ≤ g c + g (colRefl c) := by
    intro c
    by_cases hc : 1 / 2 < clamp01 (c s)
    · have hx : sceX s c = clamp01 (c s) := max_eq_left (by linarith)
      have hA : sceA s K c = scX s K c := if_pos hc
      refine le_trans (le_of_eq ?_) le_self_add
      simp only [hg, Set.indicator_apply, Set.mem_setOf_eq, sceV, hx, hA]
    · have hx : sceX s c = clamp01 (colRefl c s) := by
        rw [sce_refl_clamp]; exact max_eq_right (by linarith)
      have hA : sceA s K c = scX s K (colRefl c) := if_neg hc
      refine le_trans (le_of_eq ?_) le_add_self
      simp only [hg, Set.indicator_apply, Set.mem_setOf_eq, sceV, hx, hA]
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_left hgm, (colRefl_mp (N := N)).lintegral_comp hgm, ← two_mul]
  exact mul_le_mul' le_rfl (sc_col_bound s K hab hne hm hmp)

lemma measurable_sceX (s : State N) : Measurable (sceX s) := by
  unfold sceX
  have hy : Measurable fun c : State N → ℝ => clamp01 (c s) := continuous_clamp01.measurable.comp (measurable_pi_apply s)
  exact hy.max (measurable_const.sub hy)

lemma sceX_nonneg (s : State N) (c : State N → ℝ) : 0 ≤ sceX s c :=
  (clamp01_nonneg _).trans (le_max_left _ _)

lemma sceX_le_one (s : State N) (c : State N → ℝ) : sceX s c ≤ 1 :=
  max_le (clamp01_le_one _) (by linarith [clamp01_nonneg (c s)])

lemma measurable_sceV (s : State N) (K : Finset (Fin N)) (mp : ℝ) : Measurable (sceV s K mp) := by
  have hy : Measurable fun c : State N → ℝ => clamp01 (c s) := continuous_clamp01.measurable.comp (measurable_pi_apply s)
  have hA : Measurable (sceA s K) := by
    unfold sceA
    exact Measurable.ite (measurableSet_lt measurable_const hy) (measurable_scX s K)
      ((measurable_scX s K).comp (measurable_pi_iff.2 fun r => measurable_const.sub (measurable_pi_apply r)))
  unfold sceV Real.logb
  exact ((((measurable_sceX s).div hA).log).div_const _).min ((((measurable_sceX s).div_const mp).log).div_const _)

/-- The effect event of one cut, one cell. -/
def sceE (r0 : State N) (K : Finset (Fin N)) (m mp T B : ℝ) : Set (Param N) :=
  {w | (∀ j, m ≤ sceX r0 (fun r => w r j)) ∧ ∑ j, -Real.log (sceX r0 (fun r => w r j)) ≤ B ∧
    ∑ j ∈ Kᶜ, sceV r0 K mp (fun r => w r j) ≤ T}

/-- **Chernoff for the effect side, one cut.** -/
theorem sce_chernoff (r0 : State N) (K : Finset (Fin N)) {a b : Fin N} (hab : ({a, b} : Finset (Fin N)) ⊆ K)
    (hne : a ≠ b) {m mp : ℝ} (hm : 0 < m) (hmp : 0 < mp) (n μ : ℕ) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∫⁻ u, {u : ℝ | m ≤ clamp01 u}.indicator (fun u => ENNReal.ofReal (scG mp n μ (clamp01 u))) u ∂unif ≤
      ENNReal.ofReal R) (T B : ℝ) :
    cubeM N (sceE r0 K m mp T B) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * Real.log 2 * T + μ * B) * (2 * R) ^ (N - K.card)) := by
  classical
  haveI := colLaw_isProb (N := N)
  set F : Fin 2 → Fin N → (State N → ℝ) → ℝ := ![fun j c => if j ∈ K then 0 else sceV r0 K mp c,
    fun _ c => -Real.log (sceX r0 c)] with hF
  have hFm : ∀ k j, Measurable (F k j) := by
    intro k j
    fin_cases k
    · simp only [hF, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      split_ifs
      · exact measurable_const
      · exact measurable_sceV r0 K mp
    · simp only [hF, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons]
      exact (measurable_sceX r0).log.neg
  set A : Fin 2 → ℝ := ![T, B] with hA
  set tt : Fin 2 → ℝ := ![(n : ℝ) * Real.log 2, μ] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 2)), 0 ≤ tt k := by
    intro k _; fin_cases k
    · simp only [htt, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; exact mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (by norm_num)).le
    · simp [htt]
  set W : Fin N → Set (State N → ℝ) := fun _ => {c | m ≤ sceX r0 c} with hW
  have hWm : ∀ j, MeasurableSet (W j) := fun j => measurableSet_le measurable_const (measurable_sceX r0)
  have hmain := cubeM_chernoff_cols univ F hFm A tt htt0 W hWm
  have hsub : sceE r0 K m mp T B ⊆ {w | (∀ j, (fun r => w r j) ∈ W j) ∧
      ∀ k ∈ (univ : Finset (Fin 2)), ∑ j, F k j (fun r => w r j) ≤ A k} := by
    rintro w ⟨hfl, hX, hS⟩
    refine ⟨fun j => hfl j, fun k _ => ?_⟩
    fin_cases k
    · simp only [hF, hA, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [sum_ite, sum_const_zero, zero_add, filter_not, ← compl_eq_univ_sdiff]
      simpa using hS
    · simp only [hF, hA, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons]
      exact hX
  refine (measure_mono hsub).trans (hmain.trans ?_)
  have hsumA : ∑ k ∈ (univ : Finset (Fin 2)), tt k * A k = (n : ℝ) * Real.log 2 * T + μ * B := by
    simp [htt, hA, Fin.sum_univ_two]
  rw [hsumA]
  -- the columns
  have hcolK : ∀ j ∈ K, ∫⁻ c in W j, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 2)), tt k * F k j c))
      ∂colLaw N ≤ 1 := by
    intro j hj
    refine (setLIntegral_mono' (g := fun _ => (1 : ENNReal)) (hWm j) fun c _ => ?_).trans ?_
    · simp only [Fin.sum_univ_two, hF, htt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        if_pos hj, mul_zero, zero_add]
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2 ?_)
      have := Real.log_nonpos (sceX_nonneg r0 c) (sceX_le_one r0 c)
      have : (0 : ℝ) ≤ μ := Nat.cast_nonneg _
      nlinarith
    · rw [setLIntegral_const]
      calc 1 * (colLaw N) (W j) ≤ 1 * 1 := mul_le_mul' le_rfl prob_le_one
        _ = 1 := one_mul 1
  have hcolN : ∀ j ∉ K, ∫⁻ c in W j, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 2)), tt k * F k j c))
      ∂colLaw N ≤ ENNReal.ofReal (2 * R) := by
    intro j hj
    have e : ∀ c, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 2)), tt k * F k j c)) =
        ENNReal.ofReal (Real.exp (-((n : ℝ) * Real.log 2 * sceV r0 K mp c + μ * -Real.log (sceX r0 c)))) := by
      intro c
      simp only [Fin.sum_univ_two, hF, htt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        if_neg hj]
    simp_rw [e]
    rw [← lintegral_indicator (hWm j), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    exact (sce_col_bound r0 K hab hne hm hmp n μ).trans (mul_le_mul' le_rfl hR)
  -- the product
  rw [← Finset.prod_compl_mul_prod K]
  have hp1 : ∏ j ∈ K, ∫⁻ c in W j, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 2)), tt k * F k j c))
      ∂colLaw N ≤ 1 := prod_le_one' fun j hj => hcolK j hj
  have hp2 : ∏ j ∈ Kᶜ, ∫⁻ c in W j, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 2)), tt k * F k j c))
      ∂colLaw N ≤ ENNReal.ofReal (2 * R) ^ (N - K.card) := by
    calc _ ≤ ∏ _j ∈ Kᶜ, ENNReal.ofReal (2 * R) := prod_le_prod' fun j hj => hcolN j (mem_compl.1 hj)
      _ = ENNReal.ofReal (2 * R) ^ (N - K.card) := by rw [prod_const, card_compl, Fintype.card_fin]
  calc ENNReal.ofReal (Real.exp ((n : ℝ) * Real.log 2 * T + μ * B)) *
        ((∏ j ∈ Kᶜ, _) * ∏ j ∈ K, _)
      ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * Real.log 2 * T + μ * B)) * (ENNReal.ofReal (2 * R) ^ (N - K.card) * 1) :=
        mul_le_mul' le_rfl (mul_le_mul' hp2 hp1)
    _ = ENNReal.ofReal (Real.exp ((n : ℝ) * Real.log 2 * T + μ * B) * (2 * R) ^ (N - K.card)) := by
        rw [mul_one, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- The probability of `teW` at row `s` is `xE`. -/
lemma prob_teW_xE (s : State N) (w : Param N) (j : Fin N) :
    (tpmOf (flipP s w)).prob j s (teW w s j) = xE w s j := by
  rw [g_prob_te]
  unfold teW xE
  by_cases h : 1 / 2 < clamp01 (w s j)
  · rw [if_pos h, if_pos rfl, max_eq_left (by linarith)]
  · rw [if_neg h, if_neg (by cases s j <;> simp), max_eq_right (by linarith)]

/-- The effect subcube mean at `teW` is `sceA`. -/
lemma sce_effUnit_teW (s : State N) (w : Param N) (K : Finset (Fin N)) (j : Fin N) :
    effUnit (tpmOf (flipP s w)) Kᶜ s j (teW w s j) = sceA s K (fun r => w r j) := by
  rw [effUnit, card_agree, card_compl, Fintype.card_fin]
  have hK : K.card ≤ N := by have := card_le_univ K; rwa [Fintype.card_fin] at this
  rw [show N - (N - K.card) = K.card by omega, compl_eq_univ_sdiff]
  unfold sceA scX
  by_cases h : 1 / 2 < clamp01 (w s j)
  · rw [if_pos h]; push_cast
    congr 1
    refine sum_congr rfl fun r _ => ?_
    rw [g_prob_te]; unfold teW; rw [if_pos h, if_pos rfl]
  · rw [if_neg h]; push_cast
    congr 1
    refine sum_congr rfl fun r _ => ?_
    rw [g_prob_te, sce_refl_clamp]; unfold teW; rw [if_neg h, if_neg (by cases s j <;> simp)]

theorem sce_incl {s : State N} {w : Param N} (ho : w ∈ openCube N) (hcE : concEAll N s w)
    (hDN : DU N ≤ N - 1) (hδ : dU N (N - 1) ≤ 1 / 2500)
    (hN : 1 ≤ N) {K : Finset (Fin N)} {T : ℝ}
    (hkM : kM (lamEz (flipP s w) s (teW w s)) (leMinAt s w (teW w s)) K ≤ T) {B : ℝ}
    (hX : ∑ j, -Real.log (xE w s j) ≤ B) :
    ∃ i < 51, w ∈ sceE s K (scM i) (scMp i) T B := by
  classical
  have hz : flipP s w ∈ openCube N := flipP_mem_openCube ho
  obtain ⟨me1, -, -, me4, -⟩ := lamEz_means hz s (teW w s)
  set y : Fin N → ℝ := fun j => xE w s j with hy
  set A : Fin N → ℝ := fun j => effUnit (tpmOf (flipP s w)) (univ.erase j)ᶜ s j (teW w s j) with hA
  have hFy : ∀ j, kF (lamEz (flipP s w) s (teW w s)) j = Real.logb 2 (y j / A j) := fun j => by
    show lamEz (flipP s w) s (teW w s) j (univ.erase j) = _
    rw [me1, prob_teW_xE]
  have hcard : ∀ j : Fin N, (univ.erase j).card = N - 1 := fun j => by
    rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
  have hAc : ∀ j, |A j - 1 / 2| ≤ dU N (N - 1) := fun j => by
    have := hcE (teW w s) j (univ.erase j) (notMem_erase j univ) (by rw [hcard j]; exact hDN)
    rwa [hcard j] at this
  have hAl : ∀ j, 1 / 2 - 1 / 2500 ≤ A j := fun j => by have := (abs_le.1 (hAc j)).1; linarith
  have hAu : ∀ j, A j ≤ 1 / 2 + 1 / 2500 := fun j => by have := (abs_le.1 (hAc j)).2; linarith
  have hA0 : ∀ j, 0 < A j := fun j => by have := hAl j; linarith
  have hy0 : ∀ j, 0 < y j := fun j => xE_pos w s j
  have hy1 : ∀ j, y j < 1 := fun j => by
    show max (clamp01 (w s j)) (1 - clamp01 (w s j)) < 1
    rw [b1_clamp01_of_mem_Ioo (ho s j)]
    exact max_lt (ho s j).2 (by linarith [(ho s j).1])
  have hfl : ∀ j, 49 / 100 ≤ y j := fun j => by have := xE_ge_half w s j; linarith
  -- the minimal entry and its cell
  have hne : (univ : Finset (Fin N)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  obtain ⟨jm, -, hjm⟩ := exists_min_image univ y hne
  set ym := y jm with hym
  set i := ⌊(ym - 49 / 100) * 100⌋₊ with hi
  have hym0 : 49 / 100 ≤ ym := hfl jm
  have hym1 := hy1 jm
  have hx0 : 0 ≤ (ym - 49 / 100) * 100 := by nlinarith
  have hfl1 : (i : ℝ) ≤ (ym - 49 / 100) * 100 := Nat.floor_le hx0
  have hfl2 : (ym - 49 / 100) * 100 < i + 1 := Nat.lt_floor_add_one _
  have hi51 : i < 51 := by
    have : (i : ℝ) < 51 := by linarith
    exact_mod_cast this
  have hsc : ((scM i : ℚ) : ℝ) = 49 / 100 + i / 100 := by unfold scM; push_cast; ring
  have hscp : ((scMp i : ℚ) : ℝ) = 49 / 100 + i / 100 + 12 / 1000 := by unfold scMp scM; push_cast; ring
  have hlo : ((scM i : ℚ) : ℝ) ≤ ym := by rw [hsc]; linarith
  have hhi : ym + 2 / 1000 ≤ ((scMp i : ℚ) : ℝ) := by rw [hscp]; linarith
  refine ⟨i, hi51, fun j => hlo.trans (hjm j (mem_univ j)), hX, ?_⟩
  -- the small-cut terms
  have hbdd : BddBelow (Set.range (kF (lamEz (flipP s w) s (teW w s)))) := (Set.finite_range _).bddBelow
  have hlc : leMinAt s w (teW w s) ≤ kF (lamEz (flipP s w) s (teW w s)) jm := ciInf_le hbdd jm
  refine le_trans (sum_le_sum fun j _ => ?_) hkM
  unfold sceV
  have hl : Real.logb 2 (sceX s (fun r => w r j) / sceA s K (fun r => w r j)) =
      lamEz (flipP s w) s (teW w s) j K := by
    rw [me1 j K, prob_teW_xE, sce_effUnit_teW]; rfl
  rw [hl]
  refine min_le_min le_rfl ?_
  -- `log₂(y_j / m') ≤ F_j - λ_min`
  have hmp0 : (0 : ℝ) < ((scMp i : ℚ) : ℝ) := by linarith
  have key : Real.logb 2 (y j / ((scMp i : ℚ) : ℝ)) ≤
      kF (lamEz (flipP s w) s (teW w s)) j - kF (lamEz (flipP s w) s (teW w s)) jm := by
    rw [hFy, hFy, ← Real.logb_div (div_pos (hy0 j) (hA0 j)).ne' (div_pos (hy0 jm) (hA0 jm)).ne']
    refine Real.logb_le_logb_of_le (by norm_num) (div_pos (hy0 j) hmp0) ?_
    rw [div_div_div_eq, div_le_div_iff₀ hmp0 (mul_pos (hA0 j) (hy0 jm))]
    have hymle : ym ≤ 1 := hym1.le
    have hym0' : 0 ≤ ym := by linarith
    have k1 := mul_le_mul_of_nonneg_left hhi (hA0 jm).le
    have k2 : (1 / 2 - 1 / 2500) * (ym + 2 / 1000) ≤ A jm * (ym + 2 / 1000) :=
      mul_le_mul_of_nonneg_right (hAl jm) (by linarith)
    have k3 : A j * ym ≤ (1 / 2 + 1 / 2500) * ym := mul_le_mul_of_nonneg_right (hAu j) hym0'
    have h1 : A j * ym ≤ A jm * ((scMp i : ℚ) : ℝ) := by nlinarith
    have := mul_le_mul_of_nonneg_left h1 (hy0 j).le
    nlinarith
  show Real.logb 2 (y j / ((scMp i : ℚ) : ℝ)) ≤ _
  linarith

/-! ### Numerics and the union (effect) -/

/-- The subexponential factor of the union. -/
lemma sce_rate_num : ∀ᶠ N : ℕ in atTop, Real.log 51 + Real.log (DU N) + (DU N : ℝ) * Real.log ((N : ℝ) + 1) +
    (DU N : ℝ) * (82 * Real.log 2) + 16 * slT N ≤ (N : ℝ) / 25 := by
  filter_upwards [sc_logsq 60, eventually_ge_atTop 2] with N h hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set L := Real.log ((N : ℝ) + 1) with hLdef
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hlogN : Real.log N ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hD := DU_le_log N
  have hD0 : (1 : ℝ) ≤ DU N := by have : 1 ≤ DU N := by unfold DU; omega
                                  exact_mod_cast this
  have hlD : Real.log (DU N) ≤ DU N := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hl51 : Real.log 51 ≤ 50 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have hl2 : Real.log 2 < 7 / 10 := by have := Real.log_two_lt_d9; linarith
  have hDL : (DU N : ℝ) ≤ 6 * L + 20 := by linarith
  unfold slT
  have k1 : (DU N : ℝ) * L ≤ (6 * L + 20) * L := mul_le_mul_of_nonneg_right hDL hL
  have k2 : (DU N : ℝ) * (82 * Real.log 2) ≤ (6 * L + 20) * 58 := by
    have : 82 * Real.log 2 ≤ 58 := by linarith
    nlinarith
  nlinarith

/-- **One term of the union.** -/
theorem sce_term_bound (hN : 1 ≤ N) (r0 : State N) {K : Finset (Fin N)} (hK2 : 2 ≤ K.card) (hKD : K.card ≤ DU N)
    {i : ℕ} (hi : i < 51) :
    cubeM N (sceE r0 K ((scM i : ℚ) : ℝ) ((scMp i : ℚ) : ℝ) (7 * DU N) (x0 * N + 2 * slT N)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ N * (Real.exp ((77 * Real.log 2) * DU N + 16 * slT N) * (32 : ℝ) ^ DU N *
        (95 / 600) ^ N)) := by
  classical
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hslT : 0 ≤ slT N := by
    unfold slT; have := Real.log_nonneg hNr; linarith
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < K.card)
  have habK : ({a, b} : Finset (Fin N)) ⊆ K := by
    intro x hx; rcases mem_insert.1 hx with rfl | hx; exact ha; rw [mem_singleton.1 hx]; exact hb
  obtain ⟨n, μ, R, hR0, hR1, hRc, hμe, hn11, hμ8, hRint⟩ := sc_cell_bound i hi
  have hm0 : (0 : ℝ) < ((scM i : ℚ) : ℝ) := by unfold scM; push_cast; positivity
  have hmp0 : (0 : ℝ) < ((scMp i : ℚ) : ℝ) := by unfold scMp scM; push_cast; positivity
  refine (sce_chernoff r0 K habK hab hm0 hmp0 n μ hR0 hRint _ _).trans (ENNReal.ofReal_le_ofReal ?_)
  set q : ℝ := (3 / 2 : ℝ) ^ (μ / 2) with hq
  have hq1 : 1 ≤ q := one_le_pow₀ (by norm_num)
  have hq8 : q ≤ 81 / 16 := by
    calc q ≤ (3 / 2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 81 / 16 := by norm_num
  have hexpB : Real.exp ((μ : ℝ) * (x0 * N + 2 * slT N)) = q ^ N * Real.exp (μ * (2 * slT N)) := by
    rw [mul_add, Real.exp_add, sc_exp_tilt hμe N]
  have hqR : q * R ≤ 95 / 600 := by
    have : 6 * (q * R) ≤ 95 / 100 := by rw [← mul_assoc]; exact hRc
    linarith
  set k := K.card with hk
  have hkN : k ≤ N := by have := card_le_univ K; rwa [Fintype.card_fin] at this
  have hqRpow : q ^ N * R ^ (N - k) ≤ (81 / 16 : ℝ) ^ DU N * (600 / 95 : ℝ) ^ DU N * (95 / 600) ^ N := by
    have e1 : q ^ N * R ^ (N - k) = q ^ k * (q * R) ^ (N - k) := by
      rw [mul_pow, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hkN]
    rw [e1]
    have h1 : q ^ k ≤ (81 / 16 : ℝ) ^ DU N :=
      (pow_le_pow_left₀ (by linarith) hq8 k).trans (pow_le_pow_right₀ (by norm_num) hKD)
    have h2 : (q * R) ^ (N - k) ≤ (95 / 600 : ℝ) ^ (N - k) :=
      pow_le_pow_left₀ (mul_nonneg (by linarith) hR0) hqR _
    have h3 : (95 / 600 : ℝ) ^ (N - k) ≤ (600 / 95 : ℝ) ^ DU N * (95 / 600) ^ N := by
      have e2 : (95 / 600 : ℝ) ^ N = (95 / 600) ^ (N - k) * (95 / 600) ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hkN]
      have h4 : 1 ≤ (600 / 95 : ℝ) ^ DU N * (95 / 600) ^ k := by
        have e3 : (600 / 95 : ℝ) ^ k * (95 / 600) ^ k = 1 := by rw [← mul_pow]; norm_num
        have h5 : (600 / 95 : ℝ) ^ k ≤ (600 / 95 : ℝ) ^ DU N := pow_le_pow_right₀ (by norm_num) hKD
        have h6 : (0 : ℝ) < (95 / 600) ^ k := by positivity
        nlinarith
      rw [e2]
      have h7 : (0 : ℝ) < (95 / 600) ^ (N - k) := by positivity
      nlinarith
    calc q ^ k * (q * R) ^ (N - k) ≤ (81 / 16 : ℝ) ^ DU N * ((600 / 95 : ℝ) ^ DU N * (95 / 600) ^ N) :=
          mul_le_mul h1 (h2.trans h3) (by positivity) (by positivity)
      _ = _ := by ring
  have hexpT : Real.exp ((n : ℝ) * Real.log 2 * (7 * DU N)) ≤ Real.exp ((77 * Real.log 2) * DU N) := by
    refine Real.exp_le_exp.2 ?_
    have hn : (n : ℝ) ≤ 11 := by exact_mod_cast hn11
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hD : (0 : ℝ) ≤ DU N := Nat.cast_nonneg _
    have e1 : (n : ℝ) * Real.log 2 * (7 * DU N) = (7 * n) * (Real.log 2 * DU N) := by ring
    have e2 : (77 * Real.log 2) * DU N = 77 * (Real.log 2 * DU N) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hl2.le hD)
  have hexpS : Real.exp (μ * (2 * slT N)) ≤ Real.exp (16 * slT N) := by
    refine Real.exp_le_exp.2 ?_
    have : (μ : ℝ) ≤ 8 := by exact_mod_cast hμ8
    nlinarith
  have h32 : (81 / 16 : ℝ) ^ DU N * (600 / 95 : ℝ) ^ DU N ≤ 32 ^ DU N := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h2pow : (2 * R) ^ (N - k) ≤ (2 : ℝ) ^ N * R ^ (N - k) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)) (pow_nonneg hR0 _)
  rw [Real.exp_add, hexpB]
  calc Real.exp ((n : ℝ) * Real.log 2 * (7 * DU N)) * (q ^ N * Real.exp (μ * (2 * slT N))) * (2 * R) ^ (N - k)
      ≤ Real.exp ((n : ℝ) * Real.log 2 * (7 * DU N)) * (q ^ N * Real.exp (μ * (2 * slT N))) *
          ((2 : ℝ) ^ N * R ^ (N - k)) := mul_le_mul_of_nonneg_left h2pow (by positivity)
    _ = (2 : ℝ) ^ N * (Real.exp ((n : ℝ) * Real.log 2 * (7 * DU N)) * Real.exp (μ * (2 * slT N)) *
          (q ^ N * R ^ (N - k))) := by ring
    _ ≤ (2 : ℝ) ^ N * (Real.exp ((77 * Real.log 2) * DU N) * Real.exp (16 * slT N) *
        ((81 / 16 : ℝ) ^ DU N * (600 / 95 : ℝ) ^ DU N * (95 / 600) ^ N)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul (mul_le_mul hexpT hexpS (Real.exp_pos _).le (Real.exp_pos _).le) hqRpow
          (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg hR0 _)) (by positivity)
    _ ≤ (2 : ℝ) ^ N * (Real.exp ((77 * Real.log 2) * DU N) * Real.exp (16 * slT N) * (32 ^ DU N * (95 / 600) ^ N)) := by
        gcongr
    _ = (2 : ℝ) ^ N * (Real.exp ((77 * Real.log 2) * DU N + 16 * slT N) * (32 : ℝ) ^ DU N * (95 / 600) ^ N) := by
        rw [Real.exp_add]; ring

/-- The final numerics of the union. -/
lemma sce_union_num : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ N * ((DU N * ((N : ℝ) + 1) ^ DU N) * (51 *
    (Real.exp ((77 * Real.log 2) * DU N + 16 * slT N) * (32 : ℝ) ^ DU N * (95 / 600) ^ N))) ≤
    Real.exp (-(11 / 10 * (N : ℝ))) := by
  filter_upwards [sce_rate_num, eventually_ge_atTop 1] with N hnum hN
  have hD0 : (0 : ℝ) < DU N := by
    have : 1 ≤ DU N := by unfold DU; omega
    exact_mod_cast this
  have h95 : (2 : ℝ) ^ N * (95 / 600) ^ N ≤ Real.exp (-(114 / 100 * (N : ℝ))) := by
    rw [← mul_pow]
    calc ((2 : ℝ) * (95 / 600)) ^ N ≤ Real.exp (-(114 / 100)) ^ N := pow_le_pow_left₀ (by norm_num) sc_base_num N
      _ = Real.exp (-(114 / 100 * (N : ℝ))) := by rw [← Real.exp_nat_mul]; ring_nf
  have hfac : (51 : ℝ) * (DU N * ((N : ℝ) + 1) ^ DU N) * (Real.exp ((77 * Real.log 2) * DU N + 16 * slT N) *
      (32 : ℝ) ^ DU N) ≤ Real.exp ((N : ℝ) / 25) := by
    have e3 : Real.exp ((DU N : ℝ) * Real.log ((N : ℝ) + 1)) = ((N : ℝ) + 1) ^ DU N := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    have e4 : Real.exp ((DU N : ℝ) * (5 * Real.log 2)) = (32 : ℝ) ^ DU N := by
      rw [show (DU N : ℝ) * (5 * Real.log 2) = ((5 * DU N : ℕ) : ℝ) * Real.log 2 by push_cast; ring,
        Real.exp_nat_mul, Real.exp_log (by norm_num), pow_mul]; norm_num
    have hrepr : (51 : ℝ) * (DU N * ((N : ℝ) + 1) ^ DU N) * (Real.exp ((77 * Real.log 2) * DU N + 16 * slT N) *
        (32 : ℝ) ^ DU N) = Real.exp (Real.log 51 + Real.log (DU N) + (DU N : ℝ) * Real.log ((N : ℝ) + 1) +
          ((77 * Real.log 2) * DU N + 16 * slT N) + (DU N : ℝ) * (5 * Real.log 2)) := by
      simp only [Real.exp_add, Real.exp_log (show (0 : ℝ) < 51 by norm_num), Real.exp_log hD0, e3, e4]
      ring
    rw [hrepr]
    refine Real.exp_le_exp.2 ?_
    have e5 : (77 * Real.log 2) * DU N + (DU N : ℝ) * (5 * Real.log 2) = (DU N : ℝ) * (82 * Real.log 2) := by ring
    linarith
  calc (2 : ℝ) ^ N * ((DU N * ((N : ℝ) + 1) ^ DU N) * (51 *
        (Real.exp ((77 * Real.log 2) * DU N + 16 * slT N) * (32 : ℝ) ^ DU N * (95 / 600) ^ N)))
      = (51 : ℝ) * (DU N * ((N : ℝ) + 1) ^ DU N) *
          (Real.exp ((77 * Real.log 2) * DU N + 16 * slT N) * (32 : ℝ) ^ DU N) *
          ((2 : ℝ) ^ N * (95 / 600) ^ N) := by ring
    _ ≤ Real.exp ((N : ℝ) / 25) * Real.exp (-(114 / 100 * (N : ℝ))) :=
        mul_le_mul hfac h95 (by positivity) (Real.exp_pos _).le
    _ = Real.exp (-(11 / 10 * (N : ℝ))) := by rw [← Real.exp_add]; ring_nf

/-- The effect-side small-cut failure (`2 ≤ |K| < D`) at `teW`, on concentration and the link tilt. -/
def sceBadEv (N : ℕ) (s : State N) : Set (Param N) :=
  {w | w ∈ openCube N ∧ concEAll N s w ∧ ∑ j, -Real.log (xE w s j) ≤ x0 * N + 2 * slT N ∧
    ∃ K : Finset (Fin N), 2 ≤ K.card ∧ K.card < DU N ∧
      kM (lamEz (flipP s w) s (teW w s)) (leMinAt s w (teW w s)) K ≤ 7 * DU N}

/-- **The effect-side small-cut failure is rare** (rate `1.1`). -/
theorem sceBad_rare : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (sceBadEv N s) ≤ ENNReal.ofReal (Real.exp (-(11 / 10 * (N : ℝ)))) := by
  filter_upwards [eventually_ge_atTop 64, ev_N_dU_top, sce_union_num] with N hN64 htop hnum s
  classical
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hDN : DU N ≤ N - 1 := DU_le hN64
  have hδ : dU N (N - 1) ≤ 1 / 2500 := by
    have : dU N (N - 1) ≤ N * dU N (N - 1) := le_mul_of_one_le_left (dU_nonneg N _) (by linarith)
    linarith
  set S := (univ : Finset (Finset (Fin N))).filter fun K => 2 ≤ K.card ∧ K.card < DU N with hS
  set q0 : ℝ := (2 : ℝ) ^ N * (Real.exp ((77 * Real.log 2) * DU N + 16 * slT N) * (32 : ℝ) ^ DU N *
    (95 / 600) ^ N) with hq0
  have hsub : sceBadEv N s ⊆ ⋃ K ∈ S, ⋃ i ∈ range 51,
      sceE s K ((scM i : ℚ) : ℝ) ((scMp i : ℚ) : ℝ) (7 * DU N) (x0 * N + 2 * slT N) := by
    rintro w ⟨ho, hcE, hX, K, hK2, hKD, hkM⟩
    obtain ⟨i, hi, hw⟩ := sce_incl ho hcE hDN hδ (by omega) hkM hX
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨K, mem_filter.2 ⟨mem_univ _, hK2, hKD⟩, i, mem_range.2 hi, hw⟩
  have hq00 : 0 ≤ q0 := by positivity
  have hK : ∀ K ∈ S, cubeM N (⋃ i ∈ range 51,
      sceE s K ((scM i : ℚ) : ℝ) ((scMp i : ℚ) : ℝ) (7 * DU N) (x0 * N + 2 * slT N)) ≤ ENNReal.ofReal (51 * q0) := by
    intro K hK
    obtain ⟨-, hK2, hKD⟩ := mem_filter.1 hK
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i hi => sce_term_bound (by omega) s hK2 hKD.le (mem_range.1 hi)).trans
      (le_of_eq ?_)
    rw [sum_const, card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num), hq0]
    push_cast; ring_nf
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  refine (Finset.sum_le_sum hK).trans ?_
  rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hSc : (S.card : ℝ) ≤ DU N * ((N : ℝ) + 1) ^ DU N := by
    have := sc_cuts_card (N := N) (DU N)
    exact_mod_cast this
  refine le_trans ?_ hnum
  rw [hq0]
  have h0 : 0 ≤ (51 : ℝ) * (Real.exp ((77 * Real.log 2) * DU N + 16 * slT N) * (32 : ℝ) ^ DU N * (95 / 600) ^ N) := by
    positivity
  calc (S.card : ℝ) * (51 * ((2 : ℝ) ^ N * (Real.exp ((77 * Real.log 2) * DU N + 16 * slT N) * (32 : ℝ) ^ DU N *
        (95 / 600) ^ N)))
      = (2 : ℝ) ^ N * ((S.card : ℝ) * (51 * (Real.exp ((77 * Real.log 2) * DU N + 16 * slT N) * (32 : ℝ) ^ DU N *
          (95 / 600) ^ N))) := by ring
    _ ≤ _ := by gcongr

end Census
end IIT
