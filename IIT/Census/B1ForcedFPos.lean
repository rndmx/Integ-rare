/-
Census, B1 forced leaf 15 (`posNear`, agent "forcedF"): the joint bound of the field `posNear`.

For a subcube `K'` around `r0` the small-cut term is `g_i = min(log(y_i/m_i), log(y_i/b1Cap))` with `y = y_{r0}` and
`m_i` the plus mean of the other subcube rows.  Replacing a subcube row read by the regime event (`r0^x`, cause
side, `x ∈ K'`) by `1` gives `m̃ ≥ m`, and `e^{-g̃} = max(m̃, b1Cap)/y`; the column Chernoff bound factorizes into
the regime template with the `y`-exponent lowered by one (certificate `B1ForcedFPosCert`) and the subcube factor
`E max(m̃, b1Cap) ≤ 19/25` (`posM_le`).
-/
import IIT.Census.B1ForcedFJoint
import IIT.Census.B1ForcedFPosCert
import IIT.Census.B1ForcedFTwoLeaf

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset ProbabilityTheory

variable {N : ℕ}

/-! ### Factorization of a column integral over disjoint row sets -/

/-- The extension by zero of a partial column. -/
def colExt (S : Finset (State N)) (v : S → ℝ) : State N → ℝ := fun r => if h : r ∈ S then v ⟨r, h⟩ else 0

lemma measurable_colExt (S : Finset (State N)) : Measurable (colExt S) := by
  refine measurable_pi_iff.mpr fun r => ?_
  by_cases h : r ∈ S
  · simp only [colExt, dif_pos h]; exact measurable_pi_apply _
  · simp only [colExt, dif_neg h]; exact measurable_const

theorem lintegral_colLaw_mul_local (S T : Finset (State N)) (hST : Disjoint S T)
    (f g : (State N → ℝ) → ENNReal) (hf : Measurable f) (hg : Measurable g)
    (hfS : ∀ c c' : State N → ℝ, (∀ r ∈ S, c r = c' r) → f c = f c')
    (hgT : ∀ c c' : State N → ℝ, (∀ r ∈ T, c r = c' r) → g c = g c') :
    ∫⁻ c, f c * g c ∂colLaw N = (∫⁻ c, f c ∂colLaw N) * ∫⁻ c, g c ∂colLaw N := by
  have hind := iIndepFun_colLaw.indepFun_finset S T hST (fun r => measurable_pi_apply r)
  set φ : (S → ℝ) → ENNReal := fun v => f (colExt S v)
  set ψ : (T → ℝ) → ENNReal := fun v => g (colExt T v)
  have hφ : Measurable φ := hf.comp (measurable_colExt S)
  have hψ : Measurable ψ := hg.comp (measurable_colExt T)
  have ef : ∀ c, f c = φ (fun i : S => c i) := fun c => hfS _ _ fun r hr => by
    simp [φ, colExt, hr]
  have eg : ∀ c, g c = ψ (fun i : T => c i) := fun c => hgT _ _ fun r hr => by
    simp [ψ, colExt, hr]
  have hind2 := hind.comp hφ hψ
  simp_rw [ef, eg]
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (hφ.comp (measurable_pi_iff.mpr
    fun i => measurable_pi_apply _)).aemeasurable (hψ.comp (measurable_pi_iff.mpr
    fun i => measurable_pi_apply _)).aemeasurable hind2

/-! ### The subcube factor `E max(m̃, b1Cap)` -/

lemma col_maxCap_le (G : Finset (State N)) (k j : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    ∫⁻ c, ENNReal.ofReal (max ((1 + j + ∑ r ∈ G, clamp01 (c r)) / 2 ^ k) b1Cap) ∂colLaw N ≤
      ENNReal.ofReal ((1 + j + G.card / 2) / 2 ^ k +
        Real.exp (μ * b1Cap - μ * (1 + j) / 2 ^ k) * ((1 - Real.exp (-(μ / 2 ^ k))) / (μ / 2 ^ k)) ^ G.card /
          (Real.exp 1 * μ)) := by
  haveI := colLaw_isProb (N := N)
  set κ : ℝ := μ / 2 ^ k with hκ
  have hκ0 : 0 < κ := by positivity
  set A : (State N → ℝ) → ℝ := fun c => (1 + j + ∑ r ∈ G, clamp01 (c r)) / 2 ^ k with hA
  have hpt : ∀ c, ENNReal.ofReal (max (A c) b1Cap) ≤
      ENNReal.ofReal ((1 + j) / 2 ^ k) + ∑ r ∈ G, ENNReal.ofReal (1 / 2 ^ k * clamp01 (c r)) +
        ENNReal.ofReal (Real.exp (μ * b1Cap - μ * (1 + j) / 2 ^ k) / (Real.exp 1 * μ)) *
          ∏ r ∈ G, ENNReal.ofReal (Real.exp (-κ * clamp01 (c r))) := by
    intro c
    have h1 : max (A c) b1Cap ≤ A c + Real.exp (μ * (b1Cap - A c)) / (Real.exp 1 * μ) := by
      have := pos_le_exp_div (z := b1Cap - A c) hμ
      rcases le_total (A c) b1Cap with h | h
      · rw [max_eq_right h]; rw [max_eq_left (by linarith)] at this; linarith
      · rw [max_eq_left h]; have : 0 ≤ Real.exp (μ * (b1Cap - A c)) / (Real.exp 1 * μ) := by positivity
        linarith
    have h2 : Real.exp (μ * (b1Cap - A c)) =
        Real.exp (μ * b1Cap - μ * (1 + j) / 2 ^ k) * ∏ r ∈ G, Real.exp (-κ * clamp01 (c r)) := by
      rw [← Real.exp_sum, ← Real.exp_add]; congr 1
      simp only [hA, hκ]; rw [← Finset.mul_sum]
      field_simp; ring
    have h3 : A c = (1 + j) / 2 ^ k + ∑ r ∈ G, 1 / 2 ^ k * clamp01 (c r) := by
      simp only [hA]; rw [← Finset.mul_sum]; ring
    have hcl : ∀ r ∈ G, 0 ≤ 1 / 2 ^ k * clamp01 (c r) := fun r _ => mul_nonneg (by positivity) (clamp01_nonneg _)
    calc ENNReal.ofReal (max (A c) b1Cap)
        ≤ ENNReal.ofReal (A c + Real.exp (μ * (b1Cap - A c)) / (Real.exp 1 * μ)) := ENNReal.ofReal_le_ofReal h1
      _ = _ := by
          rw [h2, h3, ENNReal.ofReal_add (add_nonneg (by positivity) (Finset.sum_nonneg hcl)) (by positivity),
            ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg hcl), ENNReal.ofReal_sum_of_nonneg hcl,
            show Real.exp (μ * b1Cap - μ * (1 + j) / 2 ^ k) * (∏ r ∈ G, Real.exp (-κ * clamp01 (c r))) /
                (Real.exp 1 * μ) = Real.exp (μ * b1Cap - μ * (1 + j) / 2 ^ k) / (Real.exp 1 * μ) *
                  ∏ r ∈ G, Real.exp (-κ * clamp01 (c r)) by ring,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_prod_of_nonneg (fun r _ => (Real.exp_pos _).le)]
  have hm1 : ∀ r, Measurable fun c : State N → ℝ => ENNReal.ofReal (1 / 2 ^ k * clamp01 (c r)) :=
    fun r => ENNReal.measurable_ofReal.comp (measurable_const.mul (clamp01_measurable.comp (measurable_pi_apply r)))
  have hfe : Measurable fun u : ℝ => ENNReal.ofReal (Real.exp (-κ * clamp01 u)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (clamp01_measurable.const_mul _))
  have hm2 : Measurable fun c : State N → ℝ => ∏ r ∈ G, ENNReal.ofReal (Real.exp (-κ * clamp01 (c r))) :=
    Finset.measurable_prod _ fun r _ => hfe.comp (measurable_pi_apply r)
  have hlin : ∫⁻ u, ENNReal.ofReal (1 / 2 ^ k * clamp01 u) ∂unif = ENNReal.ofReal (1 / 2 ^ k * (1 / 2)) := by
    have := lintegral_unif_pow 1
    simp only [pow_one] at this
    rw [show (fun u : ℝ => ENNReal.ofReal (1 / 2 ^ k * clamp01 u)) =
        fun u => ENNReal.ofReal (1 / 2 ^ k) * ENNReal.ofReal (clamp01 u) from
      funext fun u => ENNReal.ofReal_mul (by positivity),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, this, ← ENNReal.ofReal_mul (by positivity)]
    norm_num
  have hexp : ∫⁻ u, ENNReal.ofReal (Real.exp (-κ * clamp01 u)) ∂unif =
      ENNReal.ofReal ((1 - Real.exp (-κ)) / κ) := by
    rw [lintegral_unif_exp (by linarith : -κ ≠ 0)]
    congr 1
    field_simp
    ring
  calc ∫⁻ c, ENNReal.ofReal (max (A c) b1Cap) ∂colLaw N
      ≤ ∫⁻ c, (ENNReal.ofReal ((1 + j) / 2 ^ k) + ∑ r ∈ G, ENNReal.ofReal (1 / 2 ^ k * clamp01 (c r)) +
          ENNReal.ofReal (Real.exp (μ * b1Cap - μ * (1 + j) / 2 ^ k) / (Real.exp 1 * μ)) *
            ∏ r ∈ G, ENNReal.ofReal (Real.exp (-κ * clamp01 (c r)))) ∂colLaw N := lintegral_mono hpt
    _ = ENNReal.ofReal ((1 + j) / 2 ^ k) + ∑ r ∈ G, ENNReal.ofReal (1 / 2 ^ k * (1 / 2)) +
          ENNReal.ofReal (Real.exp (μ * b1Cap - μ * (1 + j) / 2 ^ k) / (Real.exp 1 * μ)) *
            ENNReal.ofReal ((1 - Real.exp (-κ)) / κ) ^ G.card := by
        rw [lintegral_add_right _ (hm2.const_mul _), lintegral_add_right _ (Finset.measurable_sum _ fun r _ => hm1 r),
          lintegral_const, measure_univ, mul_one, lintegral_finsetSum _ fun r _ => hm1 r,
          lintegral_const_mul _ hm2, lintegral_colLaw_prod G hfe, hexp]
        congr 2
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [lintegral_colLaw_eval (f := fun u => ENNReal.ofReal (1 / 2 ^ k * clamp01 u)) r
          (ENNReal.measurable_ofReal.comp (measurable_const.mul clamp01_measurable)), hlin]
    _ = _ := by
        have hq : 0 ≤ (1 - Real.exp (-κ)) / κ := by
          have : Real.exp (-κ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
          exact div_nonneg (by linarith) hκ0.le
        rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_pow hq, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

lemma q_le_inv {κ : ℝ} (hκ : 0 < κ) : (1 - Real.exp (-κ)) / κ ≤ 1 / κ := by
  apply div_le_div_of_nonneg_right _ hκ.le
  have := Real.exp_pos (-κ); linarith

lemma q_nonneg {κ : ℝ} (hκ : 0 < κ) : 0 ≤ (1 - Real.exp (-κ)) / κ := by
  have : Real.exp (-κ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  exact div_nonneg (by linarith) hκ.le

lemma exp_neg_one_ge : (3678 / 10000 : ℝ) ≤ Real.exp (-1) := by
  obtain ⟨-, he2⟩ := exp_one_bounds
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
  linarith

lemma exp_neg_two_ge : (1 / 7.39 : ℝ) ≤ Real.exp (-2) := by
  obtain ⟨-, he2⟩ := exp_one_bounds
  have h : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hlt : Real.exp 2 < 7.39 := by rw [h]; nlinarith [Real.exp_pos 1]
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 2)]
  norm_num; linarith

lemma exp_nat_le (n : ℕ) : Real.exp n ≤ (27183 / 10000 : ℝ) ^ n := by
  obtain ⟨-, he2⟩ := exp_one_bounds
  rw [show (n : ℝ) = n * 1 by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le he2.le n

/-- The numeric part: `a + e^{E} q^m/(e μ) ≤ 19/25` from `e^{E} ≤ e^n` and `q ≤ qb`. -/
lemma posM_num {a E q μ qb : ℝ} {m n : ℕ} (hμ : 0 < μ) (hE : E ≤ n) (hq0 : 0 ≤ q) (hq : q ≤ qb)
    (h : a + (27183 / 10000 : ℝ) ^ n * qb ^ m / (2718 / 1000 * μ) ≤ 19 / 25) :
    a + Real.exp E * q ^ m / (Real.exp 1 * μ) ≤ 19 / 25 := by
  obtain ⟨he1, -⟩ := exp_one_bounds
  have h1 : Real.exp E ≤ (27183 / 10000 : ℝ) ^ n := (Real.exp_le_exp.2 hE).trans (exp_nat_le n)
  have h2 : q ^ m ≤ qb ^ m := pow_le_pow_left₀ hq0 hq m
  have hqb : 0 ≤ qb ^ m := pow_nonneg (hq0.trans hq) m
  have h3 : Real.exp E * q ^ m ≤ (27183 / 10000 : ℝ) ^ n * qb ^ m :=
    mul_le_mul h1 h2 (pow_nonneg hq0 m) (by positivity)
  have h4 : Real.exp E * q ^ m / (Real.exp 1 * μ) ≤ (27183 / 10000 : ℝ) ^ n * qb ^ m / (2718 / 1000 * μ) := by
    apply div_le_div₀ (mul_nonneg (by positivity) hqb) h3 (by positivity)
    exact mul_le_mul_of_nonneg_right he1.le hμ.le
  linarith

/-- **The subcube factor**: `E max(m̃, b1Cap) ≤ 19/25` for `|K'| = k ≤ 4` and `j ≤ 1` replaced rows. -/
theorem posM_le (G : Finset (State N)) (k j : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (hj : j ≤ 1)
    (hkj : k = 1 → j = 0) (hcard : G.card = 2 ^ k - 1 - j) :
    ∫⁻ c, ENNReal.ofReal (max ((1 + j + ∑ r ∈ G, clamp01 (c r)) / 2 ^ k) b1Cap) ∂colLaw N ≤
      ENNReal.ofReal (19 / 25) := by
  have hb : b1Cap = 63 / 125 := rfl
  have e1 := exp_neg_one_ge
  have e2 := exp_neg_two_ge
  interval_cases k <;> interval_cases j
  · -- (1, 0): μ = 250
    refine (col_maxCap_le G 1 0 (μ := 250) (by norm_num)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hc : G.card = 1 := by simpa using hcard
    rw [hc]
    refine posM_num (qb := 1 / 125) (n := 1) (by norm_num) (by rw [hb]; norm_num) (q_nonneg (by norm_num))
      ((q_le_inv (by norm_num)).trans (by norm_num)) (by norm_num)
  · exact absurd (hkj rfl) (by norm_num)
  · -- (2, 0): μ = 8, κ = 2
    refine (col_maxCap_le G 2 0 (μ := 8) (by norm_num)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hc : G.card = 3 := by simpa using hcard
    rw [hc]
    refine posM_num (qb := 4324 / 10000) (n := 3) (by norm_num) (by rw [hb]; norm_num) (q_nonneg (by norm_num))
      ?_ (by norm_num)
    rw [show (8 : ℝ) / 2 ^ 2 = 2 by norm_num, div_le_iff₀ (by norm_num)]; linarith
  · -- (2, 1): μ = 16, κ = 4
    refine (col_maxCap_le G 2 1 (μ := 16) (by norm_num)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hc : G.card = 2 := by simpa using hcard
    rw [hc]
    refine posM_num (qb := 1 / 4) (n := 1) (by norm_num) (by rw [hb]; norm_num) (q_nonneg (by norm_num))
      ((q_le_inv (by norm_num)).trans (by norm_num)) (by norm_num)
  · -- (3, 0): μ = 8, κ = 1
    refine (col_maxCap_le G 3 0 (μ := 8) (by norm_num)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hc : G.card = 7 := by simpa using hcard
    rw [hc]
    refine posM_num (qb := 6322 / 10000) (n := 4) (by norm_num) (by rw [hb]; norm_num) (q_nonneg (by norm_num))
      ?_ (by norm_num)
    rw [show (8 : ℝ) / 2 ^ 3 = 1 by norm_num, div_one]; linarith
  · -- (3, 1): μ = 8, κ = 1
    refine (col_maxCap_le G 3 1 (μ := 8) (by norm_num)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hc : G.card = 6 := by simpa using hcard
    rw [hc]
    refine posM_num (qb := 6322 / 10000) (n := 3) (by norm_num) (by rw [hb]; norm_num) (q_nonneg (by norm_num))
      ?_ (by norm_num)
    rw [show (8 : ℝ) / 2 ^ 3 = 1 by norm_num, div_one]; linarith
  · -- (4, 0): μ = 16, κ = 1
    refine (col_maxCap_le G 4 0 (μ := 16) (by norm_num)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hc : G.card = 15 := by simpa using hcard
    rw [hc]
    refine posM_num (qb := 6322 / 10000) (n := 8) (by norm_num) (by rw [hb]; norm_num) (q_nonneg (by norm_num))
      ?_ (by norm_num)
    rw [show (16 : ℝ) / 2 ^ 4 = 1 by norm_num, div_one]; linarith
  · -- (4, 1): μ = 16, κ = 1
    refine (col_maxCap_le G 4 1 (μ := 16) (by norm_num)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hc : G.card = 14 := by simpa using hcard
    rw [hc]
    refine posM_num (qb := 6322 / 10000) (n := 7) (by norm_num) (by rw [hb]; norm_num) (q_nonneg (by norm_num))
      ?_ (by norm_num)
    rw [show (16 : ℝ) / 2 ^ 4 = 1 by norm_num, div_one]; linarith

/-! ### The posNear cell bounds -/

/-- The dominating subcube mean of a column (`j` replaced rows set to `1`). -/
noncomputable def pnMt (c : State N → ℝ) (G : Finset (State N)) (k j : ℕ) : ℝ :=
  (1 + j + ∑ r ∈ G, clamp01 (c r)) / 2 ^ k

/-- The dominated small-cut term of a column. -/
noncomputable def pnGt (c : State N → ℝ) (r0 : State N) (G : Finset (State N)) (k j : ℕ) : ℝ :=
  min (Real.log (clamp01 (c r0) / pnMt c G k j)) (Real.log (clamp01 (c r0) / b1Cap))

lemma pnMt_pos (c : State N → ℝ) (G : Finset (State N)) (k j : ℕ) : 0 < pnMt c G k j := by
  unfold pnMt
  have : 0 ≤ ∑ r ∈ G, clamp01 (c r) := Finset.sum_nonneg fun r _ => clamp01_nonneg _
  positivity

lemma measurable_pnMt (G : Finset (State N)) (k j : ℕ) : Measurable fun c : State N → ℝ => pnMt c G k j := by
  unfold pnMt
  exact (measurable_const.add (Finset.measurable_sum _ fun r _ =>
    clamp01_measurable.comp (measurable_pi_apply r))).div_const _

lemma measurable_pnGt (r0 : State N) (G : Finset (State N)) (k j : ℕ) :
    Measurable fun c : State N → ℝ => pnGt c r0 G k j := by
  unfold pnGt
  have hy : Measurable fun c : State N → ℝ => clamp01 (c r0) := clamp01_measurable.comp (measurable_pi_apply r0)
  exact (Real.measurable_log.comp (hy.div (measurable_pnMt G k j))).min
    (Real.measurable_log.comp (hy.div_const _))

/-- `e^{-g̃} = max(m̃, b1Cap) · e^{-log y}` for `y > 0`. -/
lemma exp_neg_pnGt {c : State N → ℝ} {r0 : State N} {G : Finset (State N)} {k j : ℕ} (hy : 0 < clamp01 (c r0)) :
    Real.exp (-pnGt c r0 G k j) = max (pnMt c G k j) b1Cap * Real.exp (-Real.log (clamp01 (c r0))) := by
  have hm := pnMt_pos c G k j
  have hb : (0 : ℝ) < b1Cap := by unfold b1Cap; norm_num
  unfold pnGt
  rw [Real.exp_neg (Real.log _), Real.exp_log hy]
  rcases le_total (pnMt c G k j) b1Cap with h | h
  · rw [max_eq_right h]
    have : Real.log (clamp01 (c r0) / b1Cap) ≤ Real.log (clamp01 (c r0) / pnMt c G k j) :=
      Real.log_le_log (div_pos hy hb) (div_le_div_of_nonneg_left hy.le hm h)
    rw [min_eq_right this, Real.exp_neg, Real.exp_log (div_pos hy hb)]; field_simp
  · rw [max_eq_left h]
    have : Real.log (clamp01 (c r0) / pnMt c G k j) ≤ Real.log (clamp01 (c r0) / b1Cap) :=
      Real.log_le_log (div_pos hy hm) (div_le_div_of_nonneg_left hy.le hb h)
    rw [min_eq_left this, Real.exp_neg, Real.exp_log (div_pos hy hm)]; field_simp

/-- The posNear per-cell bound. -/
noncomputable def PNB (N : ℕ) : ℝ :=
  Real.exp (-((pnRT : ℝ) * N)) * Real.exp (30 * slT N + 40 * (8 + slV N) + 10) / 2 ^ N

/-- Three-row column integral of a product of an indicator and functions of the three entries. -/
lemma lint_colLaw_three_split {r1 r2 r3 : State N} (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (W : Set ℝ) (hW : MeasurableSet W) (A C : ℝ → ENNReal) (B : ℝ → ℝ → ENNReal)
    (hA : Measurable A) (hC : Measurable C) (hB : Measurable fun p : ℝ × ℝ => B p.1 p.2) :
    ∫⁻ c, W.indicator (fun y => A y) (c r1) * B (c r1) (c r2) * C (c r3) ∂colLaw N =
      (∫⁻ y in W, A y * ∫⁻ u, B y u ∂unif ∂unif) * ∫⁻ z, C z ∂unif := by
  have hg : Measurable fun p : ℝ × ℝ × ℝ => W.indicator (fun y => A y) p.1 * B p.1 p.2.1 * C p.2.2 :=
    (((hA.indicator hW).comp measurable_fst).mul (hB.comp (measurable_fst.prodMk
      (measurable_fst.comp measurable_snd)))).mul (hC.comp (measurable_snd.comp measurable_snd))
  rw [lintegral_colLaw_triple h12 h13 h23 hg]
  have hBu : ∀ y, Measurable fun u => B y u := fun y => hB.comp (measurable_const.prodMk measurable_id)
  have step : ∀ y u, ∫⁻ z, W.indicator (fun y => A y) y * B y u * C z ∂unif =
      W.indicator (fun y => A y) y * B y u * ∫⁻ z, C z ∂unif := fun y u => lintegral_const_mul _ hC
  simp_rw [step]
  have step2 : ∀ y, ∫⁻ u, W.indicator (fun y => A y) y * B y u * ∫⁻ z, C z ∂unif ∂unif =
      W.indicator (fun y => A y) y * (∫⁻ u, B y u ∂unif) * ∫⁻ z, C z ∂unif := fun y => by
    rw [lintegral_mul_const _ ((hBu y).const_mul _), lintegral_const_mul _ (hBu y)]
  simp_rw [step2]
  have hm : Measurable fun y => W.indicator (fun y => A y) y * ∫⁻ u, B y u ∂unif :=
    (hA.indicator hW).mul hB.lintegral_prod_right'
  rw [lintegral_mul_const _ hm, ← lintegral_indicator hW]
  congr 1
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ W
  · simp [Set.indicator_of_mem hy]
  · simp [Set.indicator_of_notMem hy]

/-! ### Soundness of the posNear records -/

lemma pnValid_spec (C : RSCell) (h : pnValid C = true) :
    0 < C.v ∧ C.v ≤ C.w ∧ C.w ≤ 1 ∧ C.v < 1 ∧ (1 : ℚ) / 2 ≤ C.w ^ 4 ∧
      fsI C = ((cellIq C.v C.w C.lam C.P : ℚ) : ℝ) ∧ cellIq C.v C.w C.lam C.P ≤ C.ub := by
  simp only [pnValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hvw⟩, hw1⟩, hv1⟩, hw2⟩, hk⟩, hp⟩, h0⟩, h1⟩, hub⟩ := h
  refine ⟨hv, hvw, hw1, hv1, hw2, ?_, hub⟩
  rw [cellIq_eq C.v C.w hv hvw hw1 C.lam C.P (fun k hkm => hk k (Finset.mem_range.1 hkm)) hp h0 h1]
  rfl

/-- **Cause-side posNear record**: `log 2 + log I + log rsEx + log M + ((P+4)/4 + l_u) x0 + 1/25 ≤ -RT`. -/
lemma pnC_sound (C : RSCell) (h : pnOKC C = true) :
    0 < fsI C ∧ Real.log 2 + Real.log (fsI C) + Real.log (rsEx C.lu : ℝ) + Real.log (pnM : ℝ) +
      (((C.P : ℝ) + 4) / 4 + C.lu) * x0 + 1 / 25 ≤ -(pnRT : ℝ) := by
  simp only [pnOKC, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hval, hq⟩, hx⟩, hhi⟩, hrate⟩ := h
  obtain ⟨hv, hvw, -, hv1, hw2, hI, hub⟩ := pnValid_spec C hval
  have hIpos : 0 < fsI C := cellI_pos C hv hvw hv1 hw2
  refine ⟨hIpos, ?_⟩
  have hlogI : Real.log (fsI C) ≤ Real.log (C.ub : ℝ) :=
    Real.log_le_log hIpos (by rw [hI]; exact_mod_cast hub)
  have hub0 : (0 : ℝ) < C.ub := lt_of_lt_of_le hIpos (by rw [hI]; exact_mod_cast hub)
  have hEx0 : (0 : ℝ) < rsEx C.lu := by
    have : (0 : ℚ) < rsEx C.lu := by
      unfold rsEx
      have : ((1 : ℚ) / 2) ^ (C.lu + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      apply div_pos (by linarith) (by positivity)
    exact_mod_cast this
  have hM0 : (0 : ℝ) < pnM := by unfold pnM; norm_num
  have hcr := crLog_le (q := 2 * C.ub * rsEx C.lu * pnM) (r := C.r) C.k C.n (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hq, hx⟩, hhi⟩)
  have hsplit : Real.log (((2 * C.ub * rsEx C.lu * pnM : ℚ)) : ℝ) =
      Real.log 2 + Real.log (C.ub : ℝ) + Real.log (rsEx C.lu : ℝ) + Real.log (pnM : ℝ) := by
    push_cast
    rw [Real.log_mul (by positivity) hM0.ne', Real.log_mul (by positivity) hEx0.ne',
      Real.log_mul (by norm_num) hub0.ne']
  have ht : (0 : ℝ) ≤ ((C.P : ℝ) + 4) / 4 + C.lu := by positivity
  have hx0 := cr_x0_bounds.2
  have hr : ((C.r : ℚ) : ℝ) + (((C.P : ℝ) + 4) / 4 + C.lu) * (crX0hi : ℝ) + 1 / 25 ≤ -(pnRT : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 hrate; push_cast at this; exact this
  nlinarith [mul_le_mul_of_nonneg_left hx0 ht]

lemma rsExm1_cast (l : ℕ) : ((rsExm1 l : ℚ) : ℝ) = 2 * (1 - (1 / 2 : ℝ) ^ l) / l := by
  unfold rsExm1; push_cast; ring

/-- **Effect-side posNear record**. -/
lemma pnE_sound (C : RSCell) (h : pnOKE C = true) :
    0 < fsI C ∧ 1 ≤ C.lu ∧ Real.log 2 + Real.log (fsI C) + Real.log (rsExm1 C.lu : ℝ) + Real.log (pnM : ℝ) +
      ((C.P : ℝ) / 4 + C.lu) * x0 + 1 / 25 ≤ -(pnRT : ℝ) := by
  simp only [pnOKE, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hval, hlu⟩, hq⟩, hx⟩, hhi⟩, hrate⟩ := h
  obtain ⟨hv, hvw, -, hv1, hw2, hI, hub⟩ := pnValid_spec C hval
  have hIpos : 0 < fsI C := cellI_pos C hv hvw hv1 hw2
  refine ⟨hIpos, hlu, ?_⟩
  have hlogI : Real.log (fsI C) ≤ Real.log (C.ub : ℝ) :=
    Real.log_le_log hIpos (by rw [hI]; exact_mod_cast hub)
  have hub0 : (0 : ℝ) < C.ub := lt_of_lt_of_le hIpos (by rw [hI]; exact_mod_cast hub)
  have hEx0 : (0 : ℝ) < rsExm1 C.lu := by
    rw [rsExm1_cast]
    have : (1 / 2 : ℝ) ^ C.lu < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    have : (1 : ℝ) ≤ C.lu := by exact_mod_cast hlu
    apply div_pos (by linarith) (by linarith)
  have hM0 : (0 : ℝ) < pnM := by unfold pnM; norm_num
  have hcr := crLog_le (q := 2 * C.ub * rsExm1 C.lu * pnM) (r := C.r) C.k C.n (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hq, hx⟩, hhi⟩)
  have hsplit : Real.log (((2 * C.ub * rsExm1 C.lu * pnM : ℚ)) : ℝ) =
      Real.log 2 + Real.log (C.ub : ℝ) + Real.log (rsExm1 C.lu : ℝ) + Real.log (pnM : ℝ) := by
    push_cast
    rw [Real.log_mul (by positivity) hM0.ne', Real.log_mul (by positivity) hEx0.ne',
      Real.log_mul (by norm_num) hub0.ne']
  have ht : (0 : ℝ) ≤ (C.P : ℝ) / 4 + C.lu := by positivity
  have hx0 := cr_x0_bounds.2
  have hr : ((C.r : ℚ) : ℝ) + ((C.P : ℝ) / 4 + C.lu) * (crX0hi : ℝ) + 1 / 25 ≤ -(pnRT : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 hrate; push_cast at this; exact this
  nlinarith [mul_le_mul_of_nonneg_left hx0 ht]

/-- The final arithmetic of a posNear cell. -/
lemma pn_final (hN : 1 ≤ N) {t a b I : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 16) (ha0 : 0 ≤ a) (ha : a ≤ 34)
    (hb0 : 0 ≤ b) (hb : b ≤ 10) (hI : 0 ≤ I) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 10)
    (hrate : Real.exp (t * x0 + 1 / 25) * I ≤ Real.exp (-(pnRT : ℝ)) / 2) :
    Real.exp (t * (x0 * N + slT N) + N / 25) *
      (Real.exp (a * fsK N) * Real.exp (b * (slT N / N)) * I * (1 + κ * deltaU N)) ^ N ≤ PNB N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ0 : 0 ≤ deltaU N := by unfold deltaU; positivity
  have hδN : deltaU N * N ≤ 1 := by
    unfold deltaU; rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  have hslT : 0 ≤ slT N := by
    unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    linarith
  have hKN := fsK_mul_le hN
  have hKN0 := fsK_mul_nonneg (N := N)
  have e1 : (Real.exp (a * fsK N) * Real.exp (b * (slT N / N)) * I * (1 + κ * deltaU N)) ^ N =
      Real.exp (a * (fsK N * N)) * Real.exp (b * slT N) * I ^ N * (1 + κ * deltaU N) ^ N := by
    rw [mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 3
    · ring
    · field_simp
  have h2 : (1 + κ * deltaU N) ^ N ≤ Real.exp 10 := by
    calc (1 + κ * deltaU N) ^ N ≤ Real.exp (κ * deltaU N) ^ N := by
          gcongr; linarith [Real.add_one_le_exp (κ * deltaU N)]
      _ = Real.exp (κ * (deltaU N * N)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp 10 := Real.exp_le_exp.2 (by nlinarith)
  have h3 : Real.exp (t * (x0 * N) + N / 25) * I ^ N ≤ Real.exp (-((pnRT : ℝ) * N)) / 2 ^ N := by
    have := pow_le_pow_left₀ (by positivity) hrate N
    calc Real.exp (t * (x0 * N) + N / 25) * I ^ N = (Real.exp (t * x0 + 1 / 25) * I) ^ N := by
          rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
      _ ≤ (Real.exp (-(pnRT : ℝ)) / 2) ^ N := this
      _ = Real.exp (-((pnRT : ℝ) * N)) / 2 ^ N := by rw [div_pow, ← Real.exp_nat_mul]; ring_nf
  have h5 : Real.exp (t * slT N) * (Real.exp (a * (fsK N * N)) * Real.exp (b * slT N)) ≤
      Real.exp (30 * slT N + 40 * (8 + slV N)) := by
    rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
  rw [e1]
  have hIN : 0 ≤ I ^ N := pow_nonneg hI N
  calc Real.exp (t * (x0 * N + slT N) + N / 25) *
        (Real.exp (a * (fsK N * N)) * Real.exp (b * slT N) * I ^ N * (1 + κ * deltaU N) ^ N)
      = (Real.exp (t * (x0 * N) + N / 25) * I ^ N) *
          (Real.exp (t * slT N) * (Real.exp (a * (fsK N * N)) * Real.exp (b * slT N))) *
            (1 + κ * deltaU N) ^ N := by
        rw [show t * (x0 * N + slT N) + N / 25 = (t * (x0 * N) + N / 25) + t * slT N by ring, Real.exp_add]; ring
    _ ≤ (Real.exp (-((pnRT : ℝ) * N)) / 2 ^ N) * Real.exp (30 * slT N + 40 * (8 + slV N)) * Real.exp 10 := by
        gcongr
    _ = PNB N := by unfold PNB; rw [Real.exp_add (30 * slT N + 40 * (8 + slV N)) 10]; ring

/-- The posNear cause partner. -/
lemma pn_cause_partner (hN0 : 0 < N) {c : ℚ × ℚ} (hc : c ∈ cellsXCauseData) :
    ∃ C ∈ pnCellsC, pnOKC C = true ∧ C.lam ≤ 17 ∧ C.lu ≤ 5 ∧ C.P ≤ 40 ∧
      (∀ (s r0 : State N) (x : Fin N), {w : Param N | CellEvX N s r0 x .cause c w} ⊆
        {w | CellEvX N s r0 x .cause (C.v ^ 4, C.w ^ 4) w}) ∧
      (1 : ℝ) / 2 ≤ (((C.v ^ 4, C.w ^ 4) : ℚ × ℚ).2 : ℝ) ∧ (0 : ℝ) < (((C.v ^ 4, C.w ^ 4) : ℚ × ℚ).1 : ℝ) ∧
      (((C.v ^ 4, C.w ^ 4) : ℚ × ℚ).1 : ℝ) ≤ 1 := by
  have hall := pnLinkC_all
  rw [List.all_eq_true] at hall
  obtain ⟨C, hC, hlink⟩ := List.any_eq_true.1 (hall c hc)
  have hok : pnOKC C = true := (List.all_eq_true.1 pnCellsC_ok) C hC
  have hb := (List.all_eq_true.1 pnBoundsC) C hC
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨hlam, hlu⟩, hP⟩ := hb
  simp only [rsLink, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hlink
  obtain ⟨⟨hv4, hcap⟩, hc2⟩ := hlink
  have hval : pnValid C = true := by
    simp only [pnOKC, Bool.and_eq_true] at hok; exact hok.1.1.1.1
  obtain ⟨hv, hvw, -, hv1, hw2, -, -⟩ := pnValid_spec C hval
  refine ⟨C, hC, hok, hlam, hlu, hP, fun s r0 x => ?_, ?_, ?_, ?_⟩
  · exact cellEvX_mono hN0 s r0 x (by exact_mod_cast hv4)
      (by
        rcases hcap with h | h
        · left; exact_mod_cast h
        · right; simp only [h]; norm_num)
      (by exact_mod_cast hc2) (by push_cast; exact pow_pos (by exact_mod_cast (lt_of_lt_of_le hv hvw)) 4)
  · have := (Rat.cast_le (K := ℝ)).2 hw2; push_cast at this ⊢; exact this
  · push_cast; exact pow_pos (by exact_mod_cast hv) 4
  · push_cast; exact pow_le_one₀ (by exact_mod_cast hv.le) (by exact_mod_cast hv1.le)

set_option maxHeartbeats 1000000 in
/-- **posNear, cause cell.** -/
theorem pn_cause_cell (hN : 2 ≤ N) (s r0 : State N) (x : Fin N) {c : ℚ × ℚ} (hc : c ∈ cellsXCauseData)
    (G : Finset (State N)) (k j : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (hj : j ≤ 1) (hkj : k = 1 → j = 0)
    (hcard : G.card = 2 ^ k - 1 - j) (hG0 : r0 ∉ G) (hG1 : flipAt x r0 ∉ G) (hG2 : s ∉ G)
    (h1 : r0 ≠ s) (h3 : flipAt x r0 ≠ s) :
    cubeM N ({w | CellEvX N s r0 x .cause c w} ∩
      {w | ∑ i, pnGt (fun r => w r i) r0 G k j < (N : ℝ) / 25}) ≤ ENNReal.ofReal (PNB N) := by
  have hN0 : 0 < N := by omega
  obtain ⟨C, hC, hok, hlam, hlu, hP, hmono1, hcm1, hm0, hm1⟩ := pn_cause_partner hN0 hc
  set c1 : ℚ × ℚ := (C.v ^ 4, C.w ^ 4) with hc1
  have hsubC := cellEvX_sub_template hN0 s r0 x c1 hcm1
  set lu : ℝ := (C.lu : ℝ) with hludef
  set t : ℝ := ((C.P : ℝ) + 4) / 4 + lu with ht
  have hlu0 : 0 ≤ lu := Nat.cast_nonneg _
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hell : Measurable fun y : ℝ => -Real.log (clamp01 y) :=
    (Real.measurable_log.comp clamp01_measurable).neg
  set F : Fin 4 → Fin N → (State N → ℝ) → ℝ :=
    ![fun _ col => -Real.log (clamp01 (col r0)), fun _ col => ellSX N (col s) - -Real.log (clamp01 (col r0)),
      fun _ col => gXev N c1 (col r0) (col (flipAt x r0)), fun _ col => pnGt col r0 G k j] with hF
  have hpair : Measurable fun col : State N → ℝ => (col r0, col (flipAt x r0)) :=
    (measurable_pi_apply r0).prodMk (measurable_pi_apply (flipAt x r0))
  have hgx : Measurable fun col : State N → ℝ => gXev N c1 (col r0) (col (flipAt x r0)) :=
    (fs_gXev_meas (N := N) c1).comp hpair
  have hFm : ∀ k i, Measurable (F k i) := by
    intro k i
    fin_cases k
    · exact hell.comp (measurable_pi_apply r0)
    · exact (fs_ellSX_meas.comp (measurable_pi_apply s)).sub (hell.comp (measurable_pi_apply r0))
    · exact hgx
    · exact measurable_pnGt r0 G k j
  set a : Fin 4 → ℝ := ![x0 * N + slT N, 0, 0, (N : ℝ) / 25] with ha
  set tt : Fin 4 → ℝ := ![t, lu, (C.lam : ℝ), 1] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 4)), 0 ≤ tt k := by
    intro k _; fin_cases k
    · simpa [htt] using ht0
    · simpa [htt] using hlu0
    · simp [htt]
    · simp [htt]
  set Wy : Set ℝ := {y : ℝ | (c1.1 : ℝ) ≤ clamp01 y} with hWy
  have hWym : MeasurableSet Wy := measurableSet_le measurable_const clamp01_measurable
  set W : Fin N → Set (State N → ℝ) := fun _ => {col | col r0 ∈ Wy} with hW
  have hWm : ∀ i, MeasurableSet (W i) := fun _ => measurable_pi_apply r0 hWym
  have hmain := cubeM_chernoff_cols univ F hFm a tt htt0 W hWm
  have hsub : ({w | CellEvX N s r0 x .cause c w} ∩
      {w | ∑ i, pnGt (fun r => w r i) r0 G k j < (N : ℝ) / 25} : Set (Param N)) ⊆
      {w | (∀ i, (fun r => w r i) ∈ W i) ∧ ∀ k ∈ (univ : Finset (Fin 4)), ∑ i, F k i (fun r => w r i) ≤ a k} := by
    rintro w ⟨hw1, hw2⟩
    obtain ⟨hW1, hT, hL, hV⟩ := hsubC (hmono1 s r0 x hw1)
    refine ⟨fun i => hW1 i, fun k _ => ?_⟩
    fin_cases k
    · simpa [hF, ha] using hT
    · simp only [hF, ha]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [sum_sub_distrib]
      have : ∑ i, ellSX N (w s i) = ∑ i, ellUX N (w s i) := rfl
      rw [this]; linarith
    · simpa [hF, ha] using hV
    · simpa [hF, ha] using hw2.le
  -- the column factor
  obtain ⟨hI0, hrateC⟩ := pnC_sound C hok
  set I := fsI C with hI
  set Ex : ℝ := (rsEx C.lu : ℝ) with hEx
  have hEx' : Ex = 2 * (1 - (1 / 2 : ℝ) ^ (C.lu + 1)) / (C.lu + 1) := by rw [hEx, rsEx_cast]
  have hEx0 : 0 < Ex := by
    rw [hEx']; have : (1 / 2 : ℝ) ^ (C.lu + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    apply div_pos (by linarith) (by positivity)
  set E := Real.exp (lu * (slT N / N)) with hE
  set J : ℝ := Real.exp ((C.lam : ℝ) * fsK N) * E * (I * Ex * (19 / 25)) * (1 + 0 * deltaU N) with hJ
  have hJ0 : 0 ≤ J := by
    have hδ0 : 0 ≤ deltaU N := by unfold deltaU; positivity
    rw [hJ]; positivity
  have hcol : ∀ i : Fin N, ∫⁻ col in W i, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)),
      tt k * F k i col)) ∂colLaw N ≤ ENNReal.ofReal J := by
    intro i
    set A : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp ((lu + 1 - t) * -Real.log (clamp01 y))) with hA
    set B : ℝ → ℝ → ENNReal := fun y u => ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXev N c1 y u)) with hB
    set Cz : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp (-lu * ellSX N z)) with hCz
    set g : (State N → ℝ) → ENNReal := fun col => ENNReal.ofReal (max (pnMt col G k j) b1Cap) with hg
    have hAm : Measurable A := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hell.const_mul _))
    have hBm : Measurable fun p : ℝ × ℝ => B p.1 p.2 :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((fs_gXev_meas c1).const_mul _))
    have hCm : Measurable Cz := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (fs_ellSX_meas.const_mul _))
    have hgm : Measurable g := ENNReal.measurable_ofReal.comp ((measurable_pnMt G k j).max measurable_const)
    have hpt : ∀ col, (W i).indicator (fun col => ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)),
        tt k * F k i col))) col = (Wy.indicator (fun y => A y) (col r0) * B (col r0) (col (flipAt x r0)) *
          Cz (col s)) * g col := by
      intro col
      by_cases hcol : col ∈ W i
      · have hy : col r0 ∈ Wy := hcol
        rw [Set.indicator_of_mem hcol, Set.indicator_of_mem hy]
        have hy0 : 0 < clamp01 (col r0) := lt_of_lt_of_le hm0 hy
        simp only [hA, hB, hCz, hg]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have e3 := exp_neg_pnGt (G := G) (k := k) (j := j) hy0
        have hsum : -∑ k ∈ (univ : Finset (Fin 4)), tt k * F k i col =
            ((lu + 1 - t) * -Real.log (clamp01 (col r0)) + -(C.lam : ℝ) * gXev N c1 (col r0) (col (flipAt x r0)) +
              -lu * ellSX N (col s)) + (-pnGt col r0 G k j - -Real.log (clamp01 (col r0))) := by
          simp [Fin.sum_univ_four, hF, htt]; ring
        rw [hsum, Real.exp_add, Real.exp_sub, e3, Real.exp_add, Real.exp_add]
        field_simp
      · have hy : col r0 ∉ Wy := hcol
        rw [Set.indicator_of_notMem hcol, Set.indicator_of_notMem hy, zero_mul, zero_mul, zero_mul]
    rw [← lintegral_indicator (hWm i), lintegral_congr hpt]
    have hf : Measurable fun col : State N → ℝ => Wy.indicator (fun y => A y) (col r0) *
        B (col r0) (col (flipAt x r0)) * Cz (col s) :=
      (((hAm.indicator hWym).comp (measurable_pi_apply r0)).mul (hBm.comp hpair)).mul
          (hCm.comp (measurable_pi_apply s))
    rw [lintegral_colLaw_mul_local {r0, flipAt x r0, s} G (by
        rw [Finset.disjoint_left]; intro r hr hrG
        simp only [mem_insert, mem_singleton] at hr
        rcases hr with rfl | rfl | rfl
        · exact hG0 hrG
        · exact hG1 hrG
        · exact hG2 hrG) _ _ hf hgm
      (fun c c' h => by
        simp only [h r0 (by simp), h (flipAt x r0) (by simp), h s (by simp)])
      (fun c c' h => by
        simp only [hg, pnMt]
        rw [Finset.sum_congr rfl fun r hr => by rw [h r hr]])]
    rw [lint_colLaw_three_split (flipAt_ne x r0).symm h1 h3 Wy hWym A Cz B hAm hCm hBm]
    have hJ1 := cell_J_le (N := N) C.lam c1 hcm1 hm0 hm1 (t := t) (lamU := lu + 1) (by
      rw [ht]; have : (0 : ℝ) ≤ (C.P : ℝ) / 4 := by positivity
      linarith)
    have e1 : (∫ y in (c1.1 : ℝ)..1, y ^ (t - (lu + 1)) * gX C.lam (c1.2 : ℝ) y) = I := by
      rw [show t - (lu + 1) = (C.P : ℝ) / 4 by rw [ht]; ring]
      simp only [hc1, hI, fsI]; push_cast; rfl
    rw [e1] at hJ1
    have hE2 : ∫⁻ z, Cz z ∂unif = ENNReal.ofReal (E * Ex) := by
      simp only [hCz, hE]; rw [hEx']; exact lintegral_ellUX C.lu
    have hM := posM_le (N := N) G k j hk1 hk4 hj hkj hcard
    rw [hE2]
    calc (∫⁻ y in Wy, A y * ∫⁻ u, B y u ∂unif ∂unif) * ENNReal.ofReal (E * Ex) * ∫⁻ col, g col ∂colLaw N
        ≤ ENNReal.ofReal (Real.exp ((C.lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) * I) *
            ENNReal.ofReal (E * Ex) * ENNReal.ofReal (19 / 25) :=
          mul_le_mul' (mul_le_mul' hJ1 le_rfl) hM
      _ = ENNReal.ofReal J := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hJ]
          congr 1; unfold fsK; ring
  refine (measure_mono hsub).trans (hmain.trans ?_)
  have hsum : ∑ k ∈ (univ : Finset (Fin 4)), tt k * a k = t * (x0 * N + slT N) + N / 25 := by
    simp [Fin.sum_univ_four, htt, ha]
  rw [hsum]
  calc ENNReal.ofReal (Real.exp (t * (x0 * N + slT N) + N / 25)) *
        ∏ i, ∫⁻ col in W i, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)), tt k * F k i col)) ∂colLaw N
      ≤ ENNReal.ofReal (Real.exp (t * (x0 * N + slT N) + N / 25)) * ∏ _i : Fin N, ENNReal.ofReal J := by
        gcongr with i; exact hcol i
    _ = ENNReal.ofReal (Real.exp (t * (x0 * N + slT N) + N / 25) * J ^ N) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow hJ0,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ ENNReal.ofReal (PNB N) := by
        apply ENNReal.ofReal_le_ofReal
        have hlamR : (C.lam : ℝ) ≤ 17 := by exact_mod_cast hlam
        have hluR : lu ≤ 5 := by rw [hludef]; exact_mod_cast hlu
        have hPR : (C.P : ℝ) ≤ 40 := by exact_mod_cast hP
        rw [hJ]
        refine pn_final (a := (C.lam : ℝ)) (b := lu) (I := I * Ex * (19 / 25)) (by omega) ht0
          (by rw [ht]; linarith) (Nat.cast_nonneg _) (by linarith) hlu0
          (by linarith) (mul_nonneg (mul_nonneg hI0.le hEx0.le) (by norm_num)) 0 le_rfl (by norm_num) ?_
        -- rate
        have hM0 : (0 : ℝ) < pnM := by unfold pnM; norm_num
        have hMv : ((pnM : ℚ) : ℝ) = 19 / 25 := by unfold pnM; push_cast; ring
        rw [le_div_iff₀ (by norm_num)]
        have e : Real.exp (t * x0 + 1 / 25) * (I * Ex * (19 / 25)) * 2 =
            Real.exp (Real.log 2 + Real.log I + Real.log Ex + Real.log (pnM : ℝ) + t * x0 + 1 / 25) := by
          simp only [Real.exp_add]
          rw [Real.exp_log (by norm_num), Real.exp_log hI0, Real.exp_log hEx0, Real.exp_log hM0, hMv]; ring
        rw [e]; apply Real.exp_le_exp.2
        rw [ht, hludef, hEx]; linarith

lemma pnE_H_ge (p : ℕ) (hp1 : 1 ≤ p) (hp : p ≤ 5) :
    (1 : ℝ) / 10 ≤ (1 - (1 / 2 : ℝ) ^ (p - 1 + 1)) / (((p - 1 : ℕ) : ℝ) + 1) := by
  interval_cases p <;> norm_num

set_option maxHeartbeats 1000000 in
/-- **posNear, effect cell.** -/
theorem pn_eff_cell (hN : 2 ≤ N) (hδ : deltaU N < 1 / 2) (s r0 : State N) (x : Fin N) {c : ℚ × ℚ}
    (hc : c ∈ cellsXEffectData) (G : Finset (State N)) (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (hcard : G.card = 2 ^ k - 1 - 0) (hG0 : r0 ∉ G) (hG1 : flipAt x s ∉ G) (hG2 : s ∉ G)
    (h1 : r0 ≠ s) (h2 : r0 ≠ flipAt x s) :
    cubeM N ({w | CellEvX N s r0 x .effect c w} ∩
      {w | ∑ i, pnGt (fun r => w r i) r0 G k 0 < (N : ℝ) / 25}) ≤ ENNReal.ofReal (PNB N) := by
  have hN0 : 0 < N := by omega
  have hδ0 : 0 < deltaU N := by unfold deltaU; positivity
  -- the posNear partner
  have hall := pnLinkE_all
  rw [List.all_eq_true] at hall
  obtain ⟨C, hC, hlink⟩ := List.any_eq_true.1 (hall c hc)
  have hok : pnOKE C = true := (List.all_eq_true.1 pnCellsE_ok) C hC
  have hb := (List.all_eq_true.1 pnBoundsE) C hC
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨hlam, hlu⟩, hP⟩ := hb
  simp only [rsLinkE, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hlink
  obtain ⟨⟨hv4, hcap⟩, hc2⟩ := hlink
  obtain ⟨hI0, hp1, hrateE⟩ := pnE_sound C hok
  have hval : pnValid C = true := by
    simp only [pnOKE, Bool.and_eq_true] at hok; exact hok.1.1.1.1.1
  obtain ⟨hv, hvw, -, hv1, hw2, -, -⟩ := pnValid_spec C hval
  set c1 : ℚ × ℚ := (c.1, C.w ^ 4) with hc1
  have hc12 : (c1.2 : ℝ) = (C.w : ℝ) ^ 4 := by simp only [hc1]; push_cast; rfl
  have hw4 : (1 : ℝ) / 2 ≤ (C.w : ℝ) ^ 4 := by have := (Rat.cast_le (K := ℝ)).2 hw2; push_cast at this; exact this
  have hcm1 : (1 : ℝ) / 2 ≤ (c1.2 : ℝ) := by rw [hc12]; exact hw4
  have hc2R : (1 : ℝ) / 2 ≤ (c.2 : ℝ) := by have := (Rat.cast_le (K := ℝ)).2 hc2; push_cast at this; exact this
  have hmono := cellEvX_mono_eff s r0 x (c := c) (c' := c1) (by simp only [hc1])
    (by
      rw [hc12]
      rcases hcap with h | h
      · left; have := (Rat.cast_le (K := ℝ)).2 h; push_cast at this; exact this
      · right; rw [h]; norm_num)
    (by linarith) (by linarith)
  have hsubE := cellEvX_eff_sub_template hN0 s r0 x c1 hcm1 hδ
  set lu : ℝ := (C.P : ℝ) / 4 with hludef
  set p : ℕ := C.lu with hpdef
  set t : ℝ := lu + p with ht
  have hlu0 : 0 ≤ lu := by positivity
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hell : Measurable fun y : ℝ => -Real.log (clamp01 y) :=
    (Real.measurable_log.comp clamp01_measurable).neg
  have hpair : Measurable fun col : State N → ℝ => (col s, col (flipAt x s)) :=
    (measurable_pi_apply s).prodMk (measurable_pi_apply (flipAt x s))
  have hgx : Measurable fun col : State N → ℝ => gXevE N c1 (col s) (col (flipAt x s)) :=
    (fs_gE_meas (N := N) c1).comp hpair
  set F : Fin 4 → Fin N → (State N → ℝ) → ℝ :=
    ![fun _ col => -Real.log (clamp01 (col r0)), fun _ col => ellSX N (col s) - -Real.log (clamp01 (col r0)),
      fun _ col => gXevE N c1 (col s) (col (flipAt x s)), fun _ col => pnGt col r0 G k 0] with hF
  have hFm : ∀ k i, Measurable (F k i) := by
    intro k i
    fin_cases k
    · exact hell.comp (measurable_pi_apply r0)
    · exact (fs_ellSX_meas.comp (measurable_pi_apply s)).sub (hell.comp (measurable_pi_apply r0))
    · exact hgx
    · exact measurable_pnGt r0 G k 0
  set a : Fin 4 → ℝ := ![x0 * N + slT N, 0, 0, (N : ℝ) / 25] with ha
  set tt : Fin 4 → ℝ := ![t, lu, (C.lam : ℝ), 1] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 4)), 0 ≤ tt k := by
    intro k _; fin_cases k
    · simpa [htt] using ht0
    · simpa [htt] using hlu0
    · simp [htt]
    · simp [htt]
  set Wz : Set ℝ := {y : ℝ | (c1.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} with hWz
  have hWzm : MeasurableSet Wz :=
    measurableSet_le measurable_const (clamp01_measurable.max (measurable_const.sub clamp01_measurable))
  set Wy : Set ℝ := {y : ℝ | 1 / 2 - deltaU N ≤ y} with hWy
  have hWym : MeasurableSet Wy := measurableSet_le measurable_const measurable_id
  set W : Fin N → Set (State N → ℝ) := fun _ => {col | col s ∈ Wz ∧ col r0 ∈ Wy} with hW
  have hWm : ∀ i, MeasurableSet (W i) := fun _ => by
    show MeasurableSet ({col : State N → ℝ | col s ∈ Wz} ∩ {col | col r0 ∈ Wy})
    exact (measurable_pi_apply s hWzm).inter (measurable_pi_apply r0 hWym)
  have hmain := cubeM_chernoff_cols univ F hFm a tt htt0 W hWm
  have hsub : ({w | CellEvX N s r0 x .effect c w} ∩
      {w | ∑ i, pnGt (fun r => w r i) r0 G k 0 < (N : ℝ) / 25} : Set (Param N)) ⊆
      {w | (∀ i, (fun r => w r i) ∈ W i) ∧ ∀ k ∈ (univ : Finset (Fin 4)), ∑ i, F k i (fun r => w r i) ≤ a k} := by
    rintro w ⟨hw1, hw2⟩
    obtain ⟨hW1, hT, hL, hV, hFl⟩ := hsubE (hmono hw1)
    refine ⟨fun i => ⟨hW1 i, hFl i⟩, fun k _ => ?_⟩
    fin_cases k
    · simpa [hF, ha] using hT
    · simp only [hF, ha]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [sum_sub_distrib]; linarith
    · simpa [hF, ha] using hV
    · simpa [hF, ha] using hw2.le
  -- the column factor
  set I := fsI C with hI
  set H : ℝ := (1 - (1 / 2 : ℝ) ^ (p - 1 + 1)) / (((p - 1 : ℕ) : ℝ) + 1) with hH
  have hH10 : (1 : ℝ) / 10 ≤ H := pnE_H_ge p hp1 (by omega)
  have hHpos : 0 < H := by linarith
  set Exm : ℝ := (rsExm1 p : ℝ) with hExm
  have hExm' : Exm = 2 * H := by
    rw [hExm, rsExm1_cast, hH]
    have : ((p - 1 : ℕ) : ℝ) + 1 = p := by rw [Nat.cast_sub hp1]; push_cast; ring
    rw [Nat.sub_add_cancel hp1, this]; ring
  have hExm0 : 0 < Exm := by rw [hExm']; linarith
  set E := Real.exp (lu * (slT N / N)) with hE
  set J : ℝ := Real.exp ((C.lam : ℝ) * fsK N) * E * (I * Exm * (19 / 25)) * (1 + (1 / H) * deltaU N) with hJ
  have hJ0 : 0 ≤ J := by
    rw [hJ]
    exact mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hI0.le hExm0.le) (by norm_num)))
      (by positivity)
  have hcol : ∀ i : Fin N, ∫⁻ col in W i, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)),
      tt k * F k i col)) ∂colLaw N ≤ ENNReal.ofReal J := by
    intro i
    set A : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp (-lu * ellSX N z)) with hA
    set B : ℝ → ℝ → ENNReal := fun z v => ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXevE N c1 z v)) with hB
    set Cy : ℝ → ENNReal := Wy.indicator fun y => ENNReal.ofReal (Real.exp ((lu + 1 - t) * -Real.log (clamp01 y)))
      with hCy
    set g : (State N → ℝ) → ENNReal := fun col => ENNReal.ofReal (max (pnMt col G k 0) b1Cap) with hg
    have hAm : Measurable A := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (fs_ellSX_meas.const_mul _))
    have hBm : Measurable fun q : ℝ × ℝ => B q.1 q.2 :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((fs_gE_meas c1).const_mul _))
    have hCm : Measurable Cy :=
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hell.const_mul _))).indicator hWym
    have hgm : Measurable g := ENNReal.measurable_ofReal.comp ((measurable_pnMt G k 0).max measurable_const)
    have hpt : ∀ col, (W i).indicator (fun col => ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)),
        tt k * F k i col))) col = (Wz.indicator (fun z => A z) (col s) * B (col s) (col (flipAt x s)) *
          Cy (col r0)) * g col := by
      intro col
      by_cases hcol : col ∈ W i
      · obtain ⟨hz, hy⟩ := hcol
        rw [Set.indicator_of_mem (show col ∈ W i from ⟨hz, hy⟩), Set.indicator_of_mem hz, hCy,
          Set.indicator_of_mem hy]
        have hy0 : 0 < clamp01 (col r0) := by
          have : 0 < col r0 := by linarith [show (1 : ℝ) / 2 - deltaU N ≤ col r0 from hy]
          unfold clamp01; exact lt_max_of_lt_right (lt_min one_pos this)
        simp only [hA, hB, hg]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have e3 := exp_neg_pnGt (G := G) (k := k) (j := 0) hy0
        have hsum : -∑ k ∈ (univ : Finset (Fin 4)), tt k * F k i col =
            (-lu * ellSX N (col s) + -(C.lam : ℝ) * gXevE N c1 (col s) (col (flipAt x s)) +
              (lu + 1 - t) * -Real.log (clamp01 (col r0))) + (-pnGt col r0 G k 0 - -Real.log (clamp01 (col r0))) := by
          simp [Fin.sum_univ_four, hF, htt]; ring
        rw [hsum, Real.exp_add, Real.exp_sub, e3, Real.exp_add, Real.exp_add]
        field_simp
      · rw [Set.indicator_of_notMem hcol]
        simp only [hW, Set.mem_setOf_eq, not_and_or] at hcol
        rcases hcol with hz | hy
        · rw [Set.indicator_of_notMem hz, zero_mul, zero_mul, zero_mul]
        · rw [hCy, Set.indicator_of_notMem hy, mul_zero, zero_mul]
    rw [← lintegral_indicator (hWm i), lintegral_congr hpt]
    have hf : Measurable fun col : State N → ℝ => Wz.indicator (fun z => A z) (col s) *
        B (col s) (col (flipAt x s)) * Cy (col r0) :=
      (((hAm.indicator hWzm).comp (measurable_pi_apply s)).mul (hBm.comp hpair)).mul
          (hCm.comp (measurable_pi_apply r0))
    rw [lintegral_colLaw_mul_local {s, flipAt x s, r0} G (by
        rw [Finset.disjoint_left]; intro r hr hrG
        simp only [mem_insert, mem_singleton] at hr
        rcases hr with rfl | rfl | rfl
        · exact hG2 hrG
        · exact hG1 hrG
        · exact hG0 hrG) _ _ hf hgm
      (fun c c' h => by
        simp only [h s (by simp), h (flipAt x s) (by simp), h r0 (by simp)])
      (fun c c' h => by
        simp only [hg, pnMt]
        rw [Finset.sum_congr rfl fun r hr => by rw [h r hr]])]
    rw [lint_colLaw_three_split (flipAt_ne x s).symm (Ne.symm h1) (Ne.symm h2) Wz hWzm A Cy B hAm hCm hBm]
    have hb0 : (0 : ℝ) < (C.v : ℝ) ^ 4 := by have : (0 : ℝ) < C.v := by exact_mod_cast hv
                                             positivity
    have hb1 : (C.v : ℝ) ^ 4 ≤ 1 := pow_le_one₀ (by exact_mod_cast hv.le) (by exact_mod_cast hv1.le)
    have hbm : (C.v : ℝ) ^ 4 ≤ max (1 / 2) (c1.1 : ℝ) := by
      simp only [hc1]; have := (Rat.cast_le (K := ℝ)).2 hv4; push_cast at this; exact this
    have hS := s_factor_le (N := N) C.lam c1 hcm1 hlu0 hb0 hbm hb1
    have e2 : (∫ X in (C.v : ℝ) ^ 4..1, X ^ lu * gX C.lam (c1.2 : ℝ) X) = I := by
      rw [hc12]; simp only [hI, fsI, hludef]
    rw [e2] at hS
    have hFl := tf_floor_factor (N := N) (p - 1) (t := t) (lu := lu + 1)
      (by rw [ht]; push_cast [Nat.cast_sub hp1]; ring) hδ
    have hCy' : ∫⁻ y, Cy y ∂unif ≤ ENNReal.ofReal (H + deltaU N) := by
      rw [hCy, lintegral_indicator hWym]; exact hFl
    have hM := posM_le (N := N) G k 0 hk1 hk4 (by norm_num) (fun _ => rfl) hcard
    calc (∫⁻ z in Wz, A z * ∫⁻ v, B z v ∂unif ∂unif) * (∫⁻ y, Cy y ∂unif) * ∫⁻ col, g col ∂colLaw N
        ≤ ENNReal.ofReal (Real.exp (lu * (slT N / N)) *
            Real.exp ((C.lam : ℝ) * (7 * deltaU N + (slV N + Real.log 2) / N)) * (2 * I)) *
            ENNReal.ofReal (H + deltaU N) * ENNReal.ofReal (19 / 25) :=
          mul_le_mul' (mul_le_mul' hS hCy') hM
      _ = ENNReal.ofReal J := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hJ, hExm']
          congr 1; rw [hE]; unfold fsK; field_simp
  refine (measure_mono hsub).trans (hmain.trans ?_)
  have hsum : ∑ k ∈ (univ : Finset (Fin 4)), tt k * a k = t * (x0 * N + slT N) + N / 25 := by
    simp [Fin.sum_univ_four, htt, ha]
  rw [hsum]
  calc ENNReal.ofReal (Real.exp (t * (x0 * N + slT N) + N / 25)) *
        ∏ i, ∫⁻ col in W i, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)), tt k * F k i col)) ∂colLaw N
      ≤ ENNReal.ofReal (Real.exp (t * (x0 * N + slT N) + N / 25)) * ∏ _i : Fin N, ENNReal.ofReal J := by
        gcongr with i; exact hcol i
    _ = ENNReal.ofReal (Real.exp (t * (x0 * N + slT N) + N / 25) * J ^ N) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow hJ0,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ ENNReal.ofReal (PNB N) := by
        apply ENNReal.ofReal_le_ofReal
        have hlamR : (C.lam : ℝ) ≤ 17 := by exact_mod_cast hlam
        have hpR : (p : ℝ) ≤ 5 := by rw [hpdef]; exact_mod_cast hlu
        have hPR : (C.P : ℝ) ≤ 40 := by exact_mod_cast hP
        rw [hJ]
        refine pn_final (a := (C.lam : ℝ)) (b := lu) (I := I * Exm * (19 / 25)) (by omega) ht0
          (by rw [ht, hludef]; linarith) (Nat.cast_nonneg _) (by linarith) hlu0
          (by rw [hludef]; linarith) (mul_nonneg (mul_nonneg hI0.le hExm0.le) (by norm_num)) (1 / H)
          (by positivity) (by rw [div_le_iff₀ hHpos]; linarith) ?_
        have hM0 : (0 : ℝ) < pnM := by unfold pnM; norm_num
        have hMv : ((pnM : ℚ) : ℝ) = 19 / 25 := by unfold pnM; push_cast; ring
        rw [le_div_iff₀ (by norm_num)]
        have e : Real.exp (t * x0 + 1 / 25) * (I * Exm * (19 / 25)) * 2 =
            Real.exp (Real.log 2 + Real.log I + Real.log Exm + Real.log (pnM : ℝ) + t * x0 + 1 / 25) := by
          simp only [Real.exp_add]
          rw [Real.exp_log (by norm_num), Real.exp_log hI0, Real.exp_log hExm0, Real.exp_log hM0, hMv]; ring
        rw [e]; apply Real.exp_le_exp.2
        exact hrateE

/-! ### Assembly of the posNear joint bound -/

/-- The subsets of size `1..4`. -/
noncomputable def subs4 (N : ℕ) : Finset (Finset (Fin N)) :=
  (univ : Finset (Finset (Fin N))).filter fun K' => 1 ≤ K'.card ∧ K'.card ≤ 4

lemma card_subs4 : ((subs4 N).card : ℝ) ≤ 4 * ((N : ℝ) + 1) ^ 4 := by
  have hsub : subs4 N ⊆ (univ.powersetCard 1) ∪ (univ.powersetCard 2) ∪ (univ.powersetCard 3) ∪
      (univ.powersetCard 4) := by
    intro K' hK'
    simp only [subs4, mem_filter, mem_univ, true_and] at hK'
    simp only [mem_union, mem_powersetCard, subset_univ, true_and]
    omega
  have h := (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_right
    ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)) _))
  simp only [card_powersetCard, card_univ, Fintype.card_fin] at h
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hb : ∀ j : ℕ, j ≤ 4 → ((N.choose j : ℕ) : ℝ) ≤ ((N : ℝ) + 1) ^ 4 := by
    intro j hj
    have h1 : ((N.choose j : ℕ) : ℝ) ≤ (N : ℝ) ^ j := by exact_mod_cast Nat.choose_le_pow N j
    have h2 : (N : ℝ) ^ j ≤ ((N : ℝ) + 1) ^ j := pow_le_pow_left₀ hN0 (by linarith) j
    have h3 : ((N : ℝ) + 1) ^ j ≤ ((N : ℝ) + 1) ^ 4 := pow_le_pow_right₀ (by linarith) hj
    linarith
  have hcast : ((subs4 N).card : ℝ) ≤ (N.choose 1 : ℝ) + (N.choose 2 : ℝ) + (N.choose 3 : ℝ) + (N.choose 4 : ℝ) := by
    exact_mod_cast h
  linarith [hb 1 (by norm_num), hb 2 (by norm_num), hb 3 (by norm_num), hb 4 (by norm_num)]

/-- Absorption: `4 · 61 · (N+1)^4 · PNB N ≤ e^{-RJ N} / 2^N` eventually. -/
theorem pn_absorb : ∀ᶠ N : ℕ in atTop, 4 * ((N : ℝ) + 1) ^ 4 * (61 * PNB N) ≤ Real.exp (-(RJ * N)) / 2 ^ N := by
  have hlo := Real.isLittleO_log_id_atTop
  have hev : ∀ᶠ x : ℝ in atTop, Real.log 244 + 4 * Real.log 2 + 20000 + 5004 * Real.log x ≤ x / 500 := by
    have h1 := hlo.def (c := 1 / 5004000) (by norm_num)
    filter_upwards [h1, eventually_ge_atTop (1000 * (Real.log 244 + 4 * Real.log 2 + 20000)), eventually_ge_atTop 1]
      with x hx hx1 hx2
    simp only [Real.norm_eq_abs, id] at hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx2
    rw [abs_of_nonneg hlog, abs_of_nonneg (by linarith)] at hx
    have : 0 ≤ Real.log 244 := Real.log_nonneg (by norm_num)
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hev, eventually_ge_atTop 1] with N hN hN1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hsl := tf_slack_le N
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  unfold PNB
  rw [show 4 * ((N : ℝ) + 1) ^ 4 * (61 * (Real.exp (-((pnRT : ℝ) * N)) *
      Real.exp (30 * slT N + 40 * (8 + slV N) + 10) / 2 ^ N)) =
      (244 * ((N : ℝ) + 1) ^ 4 * (Real.exp (-((pnRT : ℝ) * N)) * Real.exp (30 * slT N + 40 * (8 + slV N) + 10))) /
        2 ^ N by ring, div_le_div_iff_of_pos_right h2N]
  have hpow : ((N : ℝ) + 1) ^ 4 ≤ Real.exp (4 * (Real.log 2 + Real.log N)) := by
    rw [← Real.log_mul (by norm_num) (by linarith),
      show (4 : ℝ) * Real.log (2 * N) = Real.log ((2 * N) ^ 4) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 4
  have h244 : (244 : ℝ) = Real.exp (Real.log 244) := (Real.exp_log (by norm_num)).symm
  calc 244 * ((N : ℝ) + 1) ^ 4 * (Real.exp (-((pnRT : ℝ) * N)) * Real.exp (30 * slT N + 40 * (8 + slV N) + 10))
      ≤ Real.exp (Real.log 244) * Real.exp (4 * (Real.log 2 + Real.log N)) *
          (Real.exp (-((pnRT : ℝ) * N)) * Real.exp (20000 + 5000 * Real.log N)) := by
        rw [← h244]; gcongr
    _ = Real.exp (Real.log 244 + 4 * Real.log 2 + 20000 + 5004 * Real.log N - (pnRT : ℝ) * N) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(RJ * N)) := by
        apply Real.exp_le_exp.2; unfold RJ pnRT; push_cast; linarith

/-- The small-cut term dominates its column surrogate. -/
lemma b1CutGX_ge_pnGt {w : Param N} {r0 : State N} {K' : Finset (Fin N)} {G : Finset (State N)} {j : ℕ}
    (i : Fin N) (hm : b1CutMeanPlus w r0 K' i ≤ pnMt (fun r => w r i) G K'.card j) :
    pnGt (fun r => w r i) r0 G K'.card j ≤ b1CutGX w r0 K' i := by
  unfold pnGt b1CutGX
  refine min_le_min ?_ le_rfl
  rcases (clamp01_nonneg (w r0 i)).eq_or_lt with h0 | hpos
  · simp [← h0]
  · have hmp : 0 < b1CutMeanPlus w r0 K' i := by
      unfold b1CutMeanPlus
      have : 0 ≤ ∑ r ∈ (agree K'ᶜ r0).erase r0, clamp01 (w r i) := Finset.sum_nonneg fun r _ => clamp01_nonneg _
      positivity
    exact Real.log_le_log (div_pos hpos (pnMt_pos _ _ _ _)) (div_le_div_of_nonneg_left hpos.le hmp hm)

/-- **`joint_posNear`, PROVED.** -/
theorem joint_posNearF : JointBound P0PosNear := by
  filter_upwards [pn_absorb, eventually_ge_atTop 18] with N hab hN s r0 x σ hfar
  have hN2 : 2 ≤ N := by omega
  have hδ : deltaU N < 1 / 2 := by
    unfold deltaU; rw [div_lt_iff₀ (by positivity)]; have : (18 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have h0 := tf_far_ne2 (by omega) hfar
  -- the per-K' data
  set rep : Finset (Fin N) → Prop := fun K' => σ = .cause ∧ x ∈ K' with hrep
  set G : Finset (Fin N) → Finset (State N) := fun K' =>
    if σ = .cause ∧ x ∈ K' then ((agree K'ᶜ r0).erase r0).erase (flipAt x r0) else (agree K'ᶜ r0).erase r0 with hG
  set jj : Finset (Fin N) → ℕ := fun K' => if σ = .cause ∧ x ∈ K' then 1 else 0 with hjj
  set Ks := (subs4 N).filter fun K' => σ = .cause → K' ≠ {x} with hKs
  have hsub : {w : Param N | RegEvX N s r0 x σ w ∧ ¬ P0PosNear N s r0 w x σ} ⊆
      ⋃ K' ∈ Ks, ⋃ c ∈ cellsX σ, ({w | CellEvX N s r0 x σ c w} ∩
        {w | ∑ i, pnGt (fun r => w r i) r0 (G K') K'.card (jj K') < (N : ℝ) / 25}) := by
    rintro w ⟨⟨c, hc, hcw⟩, hn⟩
    simp only [P0PosNear, not_forall, not_le, exists_prop] at hn
    obtain ⟨K', hne, hc4, hcx, hlt⟩ := hn
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
    refine ⟨K', ?_, c, hc, hcw, lt_of_le_of_lt (Finset.sum_le_sum fun i _ => b1CutGX_ge_pnGt i ?_) hlt⟩
    · simp only [hKs, subs4, mem_filter, mem_univ, true_and]; exact ⟨⟨hne.card_pos, hc4⟩, hcx⟩
    · unfold b1CutMeanPlus pnMt
      apply div_le_div_of_nonneg_right _ (by positivity)
      simp only [hG, hjj]
      split_ifs with hr
      · have hmem : flipAt x r0 ∈ (agree K'ᶜ r0).erase r0 := by
          refine mem_erase.2 ⟨flipAt_ne x r0, ?_⟩
          rw [mem_agree]; intro j hj
          have : j ≠ x := fun h => (mem_compl.1 hj) (h ▸ hr.2)
          simp [flipAt, Function.update_of_ne this]
        rw [← Finset.add_sum_erase _ _ hmem]
        have := clamp01_le_one (w (flipAt x r0) i)
        push_cast; linarith
      · push_cast; linarith
  refine (measure_mono hsub).trans ?_
  have hterm : ∀ K' ∈ Ks, ∀ c ∈ cellsX σ, cubeM N ({w | CellEvX N s r0 x σ c w} ∩
      {w | ∑ i, pnGt (fun r => w r i) r0 (G K') K'.card (jj K') < (N : ℝ) / 25}) ≤ ENNReal.ofReal (PNB N) := by
    intro K' hK' c hc
    simp only [hKs, subs4, mem_filter, mem_univ, true_and] at hK'
    obtain ⟨⟨hk1, hk4⟩, hcx⟩ := hK'
    have hs_notin : s ∉ agree K'ᶜ r0 := fun h => by
      have := ham_le_card_of_mem_agree h; rw [ham_comm] at this; omega
    cases σ with
    | cause =>
      by_cases hxK : x ∈ K'
      · have hG' : G K' = ((agree K'ᶜ r0).erase r0).erase (flipAt x r0) := by simp [hG, hxK]
        have hj' : jj K' = 1 := by simp [hjj, hxK]
        rw [hG', hj']
        have hmem : flipAt x r0 ∈ (agree K'ᶜ r0).erase r0 := by
          refine mem_erase.2 ⟨flipAt_ne x r0, ?_⟩
          rw [mem_agree]; intro j hj
          have : j ≠ x := fun h => (mem_compl.1 hj) (h ▸ hxK)
          simp [flipAt, Function.update_of_ne this]
        have hk2 : 2 ≤ K'.card := by
          by_contra hlt
          have : K'.card = 1 := by omega
          obtain ⟨a, ha⟩ := Finset.card_eq_one.1 this
          rw [ha] at hxK; simp at hxK; subst hxK
          exact hcx rfl ha
        exact pn_cause_cell hN2 s r0 x (List.mem_toFinset.1 hc) _ K'.card 1 hk1 hk4 le_rfl (by omega)
          (by rw [card_erase_of_mem hmem, card_agree_erase])
          (fun h => (mem_erase.1 (mem_erase.1 h).2).1 rfl) (fun h => (mem_erase.1 h).1 rfl)
          (fun h => hs_notin (mem_erase.1 (mem_erase.1 h).2).2) h0 (tf_far_ne1 (by omega) hfar x)
      · have hG' : G K' = (agree K'ᶜ r0).erase r0 := by simp [hG, hxK]
        have hj' : jj K' = 0 := by simp [hjj, hxK]
        rw [hG', hj']
        exact pn_cause_cell hN2 s r0 x (List.mem_toFinset.1 hc) _ K'.card 0 hk1 hk4 (by norm_num) (fun _ => rfl)
          (by simp [card_agree_erase]) (fun h => (mem_erase.1 h).1 rfl)
          (fun h => by
            have h1 := (mem_erase.1 h).2
            rw [mem_agree] at h1
            have := h1 x (by simpa using hxK)
            simp [flipAt] at this)
          (fun h => hs_notin (mem_erase.1 h).2) h0 (tf_far_ne1 (by omega) hfar x)
    | effect =>
      have hG' : G K' = (agree K'ᶜ r0).erase r0 := by simp [hG]
      have hj' : jj K' = 0 := by simp [hjj]
      rw [hG', hj']
      exact pn_eff_cell hN2 hδ s r0 x (List.mem_toFinset.1 hc) _ K'.card hk1 hk4 (by simp [card_agree_erase])
        (fun h => (mem_erase.1 h).1 rfl)
        (fun h => by
          have h1 := ham_le_card_of_mem_agree (mem_erase.1 h).2
          have t1 := ham_triangle r0 (flipAt x s) s
          have t2 := ham_flipAt_le_one x s
          rw [ham_comm] at h1; omega)
        (fun h => hs_notin (mem_erase.1 h).2) h0 (tf_far_ne0 (by omega) hfar x)
  calc cubeM N (⋃ K' ∈ Ks, ⋃ c ∈ cellsX σ, ({w | CellEvX N s r0 x σ c w} ∩
        {w | ∑ i, pnGt (fun r => w r i) r0 (G K') K'.card (jj K') < (N : ℝ) / 25}))
      ≤ ∑ K' ∈ Ks, ∑ c ∈ cellsX σ, cubeM N ({w | CellEvX N s r0 x σ c w} ∩
          {w | ∑ i, pnGt (fun r => w r i) r0 (G K') K'.card (jj K') < (N : ℝ) / 25}) :=
        (measure_biUnion_finset_le _ _).trans (sum_le_sum fun K' _ => measure_biUnion_finset_le _ _)
    _ ≤ ∑ _K' ∈ Ks, ∑ _c ∈ cellsX σ, ENNReal.ofReal (PNB N) :=
        sum_le_sum fun K' hK' => sum_le_sum fun c hc => hterm K' hK' c hc
    _ ≤ ∑ _K' ∈ Ks, (61 : ENNReal) * ENNReal.ofReal (PNB N) := by
        refine sum_le_sum fun K' _ => ?_
        rw [sum_const, nsmul_eq_mul]; gcongr; exact_mod_cast tf_cells_card σ
    _ = ENNReal.ofReal (Ks.card * (61 * PNB N)) := by
        have hP0 : 0 ≤ PNB N := by unfold PNB; positivity
        rw [sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (p := (Ks.card : ℝ)) (q := 61 * PNB N) (Nat.cast_nonneg _),
          ENNReal.ofReal_mul (p := 61) (q := PNB N) (by norm_num), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hP0 : 0 ≤ PNB N := by unfold PNB; positivity
        have hKc : (Ks.card : ℝ) ≤ 4 * ((N : ℝ) + 1) ^ 4 := (Nat.cast_le.2 (card_filter_le _ _)).trans card_subs4
        exact le_trans (mul_le_mul_of_nonneg_right hKc (by positivity)) hab

end Census
end IIT

#print axioms IIT.Census.joint_posNearF
