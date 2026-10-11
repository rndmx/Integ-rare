/-
Census, B1 small cuts (W12 §6): **the per-column bound**.

For a column `c` (entries `y = c r0` of the centre row and `c r` of the subcube rows), with
`X = mean_{agree (U\K) r0} c`, `V = min(log₂(y/X), log₂(y/m'))`, `t = n ln 2`, multiplier `μ ≥ n` on `-ln y`:

  `∫_{y ≥ m} e^{-(t V + μ(-ln y))} dcolLaw ≤ ∫_{y ≥ m} y^{μ-n} ((momF 3 y n + momF 4 0 n)/4^n + m'^n) dy`,

uniformly in `|K| ≥ 2` (block Jensen; the centre block contributes `momF 3 y n`, the others `momF 4 0 n`).
-/
import IIT.Census.B1SmallCutBlock

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- The pointwise bound: `e^{-(n ln 2 · min(log₂(Y/X), log₂(Y/m')) + μ(-ln Y))} ≤ Y^{μ-n}(X^n + m'^n)`. -/
lemma sc_pt_bound {Y X m' : ℝ} (hY : 0 < Y) (hX : 0 < X) (hm' : 0 < m') {n μ : ℕ} :
    Real.exp (-((n : ℝ) * Real.log 2 * min (Real.logb 2 (Y / X)) (Real.logb 2 (Y / m')) + μ * -Real.log Y)) ≤
      (Y ^ μ / Y ^ n) * (X ^ n + m' ^ n) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have key : ∀ Z : ℝ, 0 < Z → Real.exp (-((n : ℝ) * Real.log 2 * Real.logb 2 (Y / Z) + μ * -Real.log Y)) =
      (Y ^ μ / Y ^ n) * Z ^ n := by
    intro Z hZ
    rw [Real.logb, mul_assoc, mul_div_cancel₀ _ hl2.ne', Real.log_div hY.ne' hZ.ne']
    have e : -((n : ℝ) * (Real.log Y - Real.log Z) + μ * -Real.log Y) =
        ((μ : ℕ) : ℝ) * Real.log Y + (n : ℝ) * Real.log Z - (n : ℝ) * Real.log Y := by ring
    rw [e, Real.exp_sub, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hY,
      Real.exp_log hZ]
    field_simp
  rcases le_total (Real.logb 2 (Y / X)) (Real.logb 2 (Y / m')) with h | h
  · rw [min_eq_left h, key X hX]
    have : 0 ≤ (Y ^ μ / Y ^ n) * m' ^ n := by positivity
    nlinarith
  · rw [min_eq_right h, key m' hm']
    have : 0 ≤ (Y ^ μ / Y ^ n) * X ^ n := by positivity
    nlinarith

/-- Measurability of the weight `y^μ / y^n`. -/
lemma meas_wt {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f) (μ n : ℕ) :
    Measurable fun x => clamp01 (f x) ^ μ / clamp01 (f x) ^ n :=
  ((continuous_clamp01.measurable.comp hf).pow_const μ).div ((continuous_clamp01.measurable.comp hf).pow_const n)

section Col

variable (r0 : State N) (K : Finset (Fin N)) {a b : Fin N}

/-- The subcube mean of a column. -/
noncomputable def scX (c : State N → ℝ) : ℝ := (∑ r ∈ agree (univ \ K) r0, clamp01 (c r)) / 2 ^ K.card

/-- The per-column weight in the y-integral. -/
noncomputable def scG (m' : ℝ) (n μ : ℕ) (y : ℝ) : ℝ :=
  (y ^ μ / y ^ n) * ((momF 3 y n + momF 4 0 n) / 4 ^ n + m' ^ n)

/-- The block mean. -/
noncomputable def scB (a b : Fin N) (p : State N) (c : State N → ℝ) : ℝ :=
  (∑ r ∈ agree (univ \ ({a, b} : Finset (Fin N))) p, clamp01 (c r)) / 4

lemma measurable_scB (p : State N) : Measurable (scB a b p) := by
  unfold scB
  exact (Finset.measurable_sum _ fun r _ => continuous_clamp01.measurable.comp (measurable_pi_apply r)).div_const _

/-- The block moment, centre block. -/
lemma sc_block_r0 (hne : a ≠ b) {m : ℝ} {n μ : ℕ} :
    ∫⁻ c, {c : State N → ℝ | m ≤ clamp01 (c r0)}.indicator
        (fun c => ENNReal.ofReal ((clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n) * scB a b r0 c ^ n)) c ∂colLaw N =
      ∫⁻ u, {u : ℝ | m ≤ clamp01 u}.indicator
        (fun u => ENNReal.ofReal ((clamp01 u ^ μ / clamp01 u ^ n) * (momF 3 (clamp01 u) n / 4 ^ n))) u ∂unif := by
  classical
  have hr0 : r0 ∉ (agree (univ \ ({a, b} : Finset (Fin N))) r0).erase r0 := notMem_erase r0 _
  have hcard : ((agree (univ \ ({a, b} : Finset (Fin N))) r0).erase r0).card = 3 := by
    rw [card_erase_of_mem (r0_mem_block r0), card_block hne]
  have hsum : ∀ c : State N → ℝ, scB a b r0 c = (clamp01 (c r0) +
      ∑ i : ((agree (univ \ ({a, b} : Finset (Fin N))) r0).erase r0), clamp01 (c i)) / 4 := by
    intro c; unfold scB
    rw [← add_sum_erase _ _ (r0_mem_block (a := a) (b := b) r0),
      ← sum_coe_sort ((agree (univ \ ({a, b} : Finset (Fin N))) r0).erase r0)]
  generalize hS : (agree (univ \ ({a, b} : Finset (Fin N))) r0).erase r0 = S0 at hr0 hcard hsum
  set h : ℝ → (S0 → ℝ) → ENNReal := fun u v => {u : ℝ | m ≤ clamp01 u}.indicator
    (fun u => ENNReal.ofReal ((clamp01 u ^ μ / clamp01 u ^ n) * ((clamp01 u + ∑ i : S0, clamp01 (v i)) / 4) ^ n)) u with hh
  have hmeas : Measurable fun p : ℝ × (S0 → ℝ) => h p.1 p.2 := by
    refine Measurable.indicator ?_ (measurableSet_le measurable_const (continuous_clamp01.measurable.comp measurable_fst))
    exact ENNReal.measurable_ofReal.comp ((meas_wt measurable_fst μ n).mul
      ((((continuous_clamp01.measurable.comp measurable_fst).add (Finset.measurable_sum _ fun i _ =>
        continuous_clamp01.measurable.comp ((measurable_pi_apply i).comp measurable_snd))).div_const _).pow_const _))
  have e1 : ∀ c : State N → ℝ, {c : State N → ℝ | m ≤ clamp01 (c r0)}.indicator
      (fun c => ENNReal.ofReal ((clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n) * scB a b r0 c ^ n)) c = h (c r0) (fun i : S0 => c i) := by
    intro c
    simp only [hh, Set.indicator, Set.mem_setOf_eq, hsum]
  simp_rw [e1]
  rw [colLaw_split r0 S0 hr0 h hmeas]
  refine lintegral_congr fun u => ?_
  simp only [hh, Set.indicator, Set.mem_setOf_eq]
  split_ifs with hu
  · have hfac : ∀ c : State N → ℝ, ENNReal.ofReal ((clamp01 u ^ μ / clamp01 u ^ n) *
        ((clamp01 u + ∑ i : S0, clamp01 (c i)) / 4) ^ n) = ENNReal.ofReal ((clamp01 u ^ μ / clamp01 u ^ n) / 4 ^ n) *
          ENNReal.ofReal ((clamp01 u + ∑ i : S0, clamp01 (c i)) ^ n) := by
      intro c
      rw [← ENNReal.ofReal_mul (by have := clamp01_nonneg u; positivity), div_pow]; ring_nf
    simp_rw [hfac]
    have hmF : Measurable fun c : State N → ℝ => ENNReal.ofReal ((clamp01 u + ∑ i : S0, clamp01 (c i)) ^ n) :=
      ENNReal.measurable_ofReal.comp (((Finset.measurable_sum (univ : Finset S0) fun (i : S0) _ =>
        continuous_clamp01.measurable.comp (measurable_pi_apply (i : State N))).const_add (clamp01 u)).pow_const n)
    rw [lintegral_const_mul _ hmF]
    have hsp := colLaw_sum_pow S0 (clamp01 u) (clamp01_nonneg u) n
    rw [hcard] at hsp
    have e2 : ∫⁻ c, ENNReal.ofReal ((clamp01 u + ∑ i : S0, clamp01 (c i)) ^ n) ∂colLaw N =
        ∫⁻ c, ENNReal.ofReal ((clamp01 u + ∑ r ∈ S0, clamp01 (c r)) ^ n) ∂colLaw N :=
      lintegral_congr fun c => by rw [sum_coe_sort S0 (fun q => clamp01 (c q))]
    rw [e2, hsp, ← ENNReal.ofReal_mul (by have := clamp01_nonneg u; positivity)]
    congr 1; ring
  · simp

/-- The block moment, other blocks. -/
lemma sc_block_other (hne : a ≠ b) {p : State N} (hp : p ∈ blkP r0 K a b) (hpr : p ≠ r0) {m : ℝ} {n μ : ℕ} :
    ∫⁻ c, {c : State N → ℝ | m ≤ clamp01 (c r0)}.indicator
        (fun c => ENNReal.ofReal ((clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n) * scB a b p c ^ n)) c ∂colLaw N =
      (∫⁻ u, {u : ℝ | m ≤ clamp01 u}.indicator (fun u => ENNReal.ofReal ((clamp01 u ^ μ / clamp01 u ^ n))) u ∂unif) *
        ENNReal.ofReal (momF 4 0 n / 4 ^ n) := by
  classical
  have hdisj : Disjoint ({r0} : Finset (State N)) (agree (univ \ ({a, b} : Finset (Fin N))) p) :=
    disjoint_singleton_left.2 (r0_not_mem_block r0 K hp hpr)
  have hsplit : ∀ c : State N → ℝ, {c : State N → ℝ | m ≤ clamp01 (c r0)}.indicator
      (fun c => ENNReal.ofReal ((clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n) * scB a b p c ^ n)) c =
      ({c : State N → ℝ | m ≤ clamp01 (c r0)}.indicator (fun c => ENNReal.ofReal ((clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n))) c) *
        ENNReal.ofReal (scB a b p c ^ n) := by
    intro c
    by_cases hc : m ≤ clamp01 (c r0)
    · rw [Set.indicator_of_mem (show c ∈ {c : State N → ℝ | m ≤ clamp01 (c r0)} from hc),
        Set.indicator_of_mem (show c ∈ {c : State N → ℝ | m ≤ clamp01 (c r0)} from hc),
        ← ENNReal.ofReal_mul (div_nonneg (pow_nonneg (clamp01_nonneg _) _) (pow_nonneg (clamp01_nonneg _) _))]
    · rw [Set.indicator_of_notMem (show c ∉ {c : State N → ℝ | m ≤ clamp01 (c r0)} from hc),
        Set.indicator_of_notMem (show c ∉ {c : State N → ℝ | m ≤ clamp01 (c r0)} from hc), zero_mul]
  simp_rw [hsplit]
  have hf : Measurable fun c : State N → ℝ => {c : State N → ℝ | m ≤ clamp01 (c r0)}.indicator
      (fun c => ENNReal.ofReal ((clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n))) c :=
    (ENNReal.measurable_ofReal.comp (meas_wt (measurable_pi_apply r0) μ n)).indicator
      (measurableSet_le measurable_const (continuous_clamp01.measurable.comp (measurable_pi_apply r0)))
  have hg : Measurable fun c : State N → ℝ => ENNReal.ofReal (scB a b p c ^ n) :=
    ENNReal.measurable_ofReal.comp ((measurable_scB p).pow_const _)
  rw [lintegral_colLaw_mul_local {r0} (agree (univ \ ({a, b} : Finset (Fin N))) p) hdisj _ _ hf hg
    (fun c c' h => by simp only [Set.indicator, Set.mem_setOf_eq, h r0 (mem_singleton_self r0)])
    (fun c c' h => by unfold scB; rw [sum_congr rfl fun r hr => by rw [h r hr]])]
  congr 1
  · -- the centre factor
    have hm := lintegral_map (μ := colLaw N) (f := {u : ℝ | m ≤ clamp01 u}.indicator
      (fun u => ENNReal.ofReal ((clamp01 u ^ μ / clamp01 u ^ n))))
      ((ENNReal.measurable_ofReal.comp (meas_wt measurable_id μ n)).indicator
        (measurableSet_le measurable_const continuous_clamp01.measurable)) (measurable_pi_apply r0)
    rw [colLaw_map_eval r0] at hm
    rw [hm]
    rfl
  · -- the block moment
    have hsp := colLaw_sum_pow (agree (univ \ ({a, b} : Finset (Fin N))) p) 0 le_rfl n
    rw [card_block hne] at hsp
    have hmF : Measurable fun c : State N → ℝ =>
        ENNReal.ofReal ((0 + ∑ r ∈ agree (univ \ ({a, b} : Finset (Fin N))) p, clamp01 (c r)) ^ n) :=
      ENNReal.measurable_ofReal.comp (((Finset.measurable_sum (agree (univ \ ({a, b} : Finset (Fin N))) p)
        fun (r : State N) _ => continuous_clamp01.measurable.comp (measurable_pi_apply r)).const_add 0).pow_const n)
    have e3 : (fun c : State N → ℝ => ENNReal.ofReal (scB a b p c ^ n)) =
        fun c => ENNReal.ofReal (1 / 4 ^ n) *
          ENNReal.ofReal ((0 + ∑ r ∈ agree (univ \ ({a, b} : Finset (Fin N))) p, clamp01 (c r)) ^ n) := by
      funext c; unfold scB
      rw [← ENNReal.ofReal_mul (by positivity), zero_add, div_pow]; ring_nf
    rw [e3, lintegral_const_mul _ hmF, hsp, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring

/-- **The per-column bound** (uniform in `|K| ≥ 2`). -/
theorem sc_col_bound (hab : ({a, b} : Finset (Fin N)) ⊆ K) (hne : a ≠ b) {m m' : ℝ} (hm : 0 < m)
    (hm' : 0 < m') {n μ : ℕ} :
    ∫⁻ c, {c : State N → ℝ | m ≤ clamp01 (c r0)}.indicator (fun c => ENNReal.ofReal (Real.exp
        (-((n : ℝ) * Real.log 2 * min (Real.logb 2 (clamp01 (c r0) / scX r0 K c))
          (Real.logb 2 (clamp01 (c r0) / m')) + μ * -Real.log (clamp01 (c r0)))))) c ∂colLaw N ≤
      ∫⁻ u, {u : ℝ | m ≤ clamp01 u}.indicator (fun u => ENNReal.ofReal (scG m' n μ (clamp01 u))) u ∂unif := by
  classical
  set P := blkP r0 K a b with hP
  set w : ℝ := 1 / 2 ^ (K.card - 2) with hw
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 1 := by rw [hw, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hPc : (P.card : ℝ) * w = 1 := by
    rw [hP, card_blkP r0 K hab hne, hw]; push_cast; field_simp
  set W : Set (State N → ℝ) := {c | m ≤ clamp01 (c r0)} with hW
  have hWm : MeasurableSet W := measurableSet_le measurable_const (continuous_clamp01.measurable.comp (measurable_pi_apply r0))
  -- the pointwise bound
  set R : (State N → ℝ) → ENNReal := fun c => W.indicator (fun c => ENNReal.ofReal ((clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n) *
    scB a b r0 c ^ n)) c * ENNReal.ofReal w +
    ∑ p ∈ P.erase r0, W.indicator (fun c => ENNReal.ofReal ((clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n) * scB a b p c ^ n)) c *
      ENNReal.ofReal w +
    W.indicator (fun c => ENNReal.ofReal ((clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n))) c * ENNReal.ofReal (m' ^ n) with hR
  have hpt : ∀ c, W.indicator (fun c => ENNReal.ofReal (Real.exp
      (-((n : ℝ) * Real.log 2 * min (Real.logb 2 (clamp01 (c r0) / scX r0 K c))
        (Real.logb 2 (clamp01 (c r0) / m')) + μ * -Real.log (clamp01 (c r0)))))) c ≤ R c := by
    intro c
    by_cases hc : c ∈ W
    · have hY : 0 < clamp01 (c r0) := hm.trans_le hc
      have hz : ∀ r, 0 ≤ clamp01 (c r) := fun r => clamp01_nonneg _
      have hX : 0 < scX r0 K c := by
        unfold scX
        have : clamp01 (c r0) ≤ ∑ r ∈ agree (univ \ K) r0, clamp01 (c r) :=
          single_le_sum (fun r _ => hz r) (self_mem_agree _ _)
        exact div_pos (hY.trans_le this) (by positivity)
      have h1 := sc_pt_bound hY hX hm' (n := n) (μ := μ)
      have h2 := block_jensen r0 K hab hne (fun r => clamp01 (c r)) hz n
      have hsP : ∑ p ∈ P, ((∑ r ∈ agree (univ \ ({a, b} : Finset (Fin N))) p, clamp01 (c r)) / 4) ^ n =
          scB a b r0 c ^ n + ∑ p ∈ P.erase r0, scB a b p c ^ n := by
        rw [← add_sum_erase _ _ (r0_mem_blkP r0 K)]; rfl
      rw [hsP] at h2
      have hYp : 0 ≤ (clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n) := div_nonneg (pow_nonneg hY.le _) (pow_nonneg hY.le _)
      have hBn : ∀ p, 0 ≤ scB a b p c ^ n := fun p => pow_nonneg (div_nonneg (sum_nonneg fun r _ => hz r)
        (by norm_num)) _
      have hreal : Real.exp (-((n : ℝ) * Real.log 2 * min (Real.logb 2 (clamp01 (c r0) / scX r0 K c))
          (Real.logb 2 (clamp01 (c r0) / m')) + μ * -Real.log (clamp01 (c r0)))) ≤
          (clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n) * scB a b r0 c ^ n * w +
            ∑ p ∈ P.erase r0, (clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n) * scB a b p c ^ n * w +
            (clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n) * m' ^ n := by
        refine h1.trans ?_
        have hX' : scX r0 K c ^ n ≤ w * (scB a b r0 c ^ n + ∑ p ∈ P.erase r0, scB a b p c ^ n) := h2
        have e : ∑ p ∈ P.erase r0, (clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n) * scB a b p c ^ n * w =
            (clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n) * w * ∑ p ∈ P.erase r0, scB a b p c ^ n := by
          rw [mul_sum]; exact sum_congr rfl fun p _ => by ring
        rw [e]
        nlinarith [mul_le_mul_of_nonneg_left hX' hYp]
      simp only [hR, Set.indicator_of_mem hc]
      rw [← ENNReal.ofReal_mul (mul_nonneg hYp (hBn r0)), ← ENNReal.ofReal_mul hYp]
      have hsum : ∑ p ∈ P.erase r0, ENNReal.ofReal ((clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n) * scB a b p c ^ n) * ENNReal.ofReal w =
          ENNReal.ofReal (∑ p ∈ P.erase r0, (clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n) * scB a b p c ^ n * w) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => mul_nonneg (mul_nonneg hYp (hBn p)) hw0)]
        exact sum_congr rfl fun p _ => (ENNReal.ofReal_mul (mul_nonneg hYp (hBn p))).symm
      have hq1 : 0 ≤ (clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n) * scB a b r0 c ^ n * w := mul_nonneg (mul_nonneg hYp (hBn r0)) hw0
      have hq2 : 0 ≤ ∑ p ∈ P.erase r0, (clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n) * scB a b p c ^ n * w :=
        sum_nonneg fun p _ => mul_nonneg (mul_nonneg hYp (hBn p)) hw0
      have hq3 : 0 ≤ (clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n) * m' ^ n := mul_nonneg hYp (pow_nonneg hm'.le _)
      rw [hsum, ← ENNReal.ofReal_add hq1 hq2, ← ENNReal.ofReal_add (add_nonneg hq1 hq2) hq3]
      exact ENNReal.ofReal_le_ofReal hreal
    · simp [Set.indicator_of_notMem hc]
  refine (lintegral_mono hpt).trans ?_
  -- integrate the bound
  have hmI : ∀ p, Measurable fun c => W.indicator (fun c => ENNReal.ofReal ((clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n) *
      scB a b p c ^ n)) c := fun p =>
    (ENNReal.measurable_ofReal.comp ((meas_wt (measurable_pi_apply r0) μ n).mul
      ((measurable_scB p).pow_const _))).indicator hWm
  have hmT : Measurable fun c => W.indicator (fun c => ENNReal.ofReal ((clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n))) c :=
    (ENNReal.measurable_ofReal.comp (meas_wt (measurable_pi_apply r0) μ n)).indicator
      hWm
  set TW := ∫⁻ u, {u : ℝ | m ≤ clamp01 u}.indicator (fun u => ENNReal.ofReal ((clamp01 u ^ μ / clamp01 u ^ n))) u ∂unif with hTW
  have hTWc : ∫⁻ c, W.indicator (fun c => ENNReal.ofReal ((clamp01 (c r0) ^ μ / clamp01 (c r0) ^ n))) c ∂colLaw N = TW := by
    have hm := lintegral_map (μ := colLaw N) (f := {u : ℝ | m ≤ clamp01 u}.indicator
      (fun u => ENNReal.ofReal ((clamp01 u ^ μ / clamp01 u ^ n))))
      ((ENNReal.measurable_ofReal.comp (meas_wt measurable_id μ n)).indicator
        (measurableSet_le measurable_const continuous_clamp01.measurable)) (measurable_pi_apply r0)
    rw [colLaw_map_eval r0] at hm
    rw [hTW, hm]; rfl
  have hint : ∫⁻ c, R c ∂colLaw N =
      (∫⁻ u, {u : ℝ | m ≤ clamp01 u}.indicator
        (fun u => ENNReal.ofReal ((clamp01 u ^ μ / clamp01 u ^ n) * (momF 3 (clamp01 u) n / 4 ^ n))) u ∂unif) * ENNReal.ofReal w +
      ∑ p ∈ P.erase r0, (TW * ENNReal.ofReal (momF 4 0 n / 4 ^ n)) * ENNReal.ofReal w +
      TW * ENNReal.ofReal (m' ^ n) := by
    simp only [hR]
    rw [lintegral_add_right _ (hmT.mul_const _), lintegral_add_right _
      (Finset.measurable_sum _ fun p _ => (hmI p).mul_const _), lintegral_mul_const _ (hmI r0),
      lintegral_finset_sum _ (fun p _ => (hmI p).mul_const _), lintegral_mul_const _ hmT, hTWc,
      sc_block_r0 r0 hne]
    congr 2
    refine sum_congr rfl fun p hp => ?_
    rw [lintegral_mul_const _ (hmI p), sc_block_other r0 K hne (mem_of_mem_erase hp) (ne_of_mem_erase hp)]
  rw [hint]
  -- weights: `w ≤ 1`, `(|P| - 1) w ≤ 1`
  have hw1' : ENNReal.ofReal w ≤ 1 := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hw1
  have hcnt : ((P.erase r0).card : ENNReal) * ENNReal.ofReal w ≤ 1 := by
    rw [card_erase_of_mem (r0_mem_blkP r0 K), ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have : ((P.card - 1 : ℕ) : ℝ) ≤ P.card := by exact_mod_cast Nat.sub_le _ _
    nlinarith
  rw [sum_const, nsmul_eq_mul]
  set A0 := ∫⁻ u, {u : ℝ | m ≤ clamp01 u}.indicator
    (fun u => ENNReal.ofReal ((clamp01 u ^ μ / clamp01 u ^ n) * (momF 3 (clamp01 u) n / 4 ^ n))) u ∂unif with hA0
  have hfinal : ∫⁻ u, {u : ℝ | m ≤ clamp01 u}.indicator (fun u => ENNReal.ofReal (scG m' n μ (clamp01 u))) u ∂unif =
      A0 + TW * ENNReal.ofReal (momF 4 0 n / 4 ^ n) + TW * ENNReal.ofReal (m' ^ n) := by
    have hpt2 : ∀ u, {u : ℝ | m ≤ clamp01 u}.indicator (fun u => ENNReal.ofReal (scG m' n μ (clamp01 u))) u =
        {u : ℝ | m ≤ clamp01 u}.indicator
          (fun u => ENNReal.ofReal ((clamp01 u ^ μ / clamp01 u ^ n) * (momF 3 (clamp01 u) n / 4 ^ n))) u +
        {u : ℝ | m ≤ clamp01 u}.indicator (fun u => ENNReal.ofReal ((clamp01 u ^ μ / clamp01 u ^ n))) u *
          ENNReal.ofReal (momF 4 0 n / 4 ^ n) +
        {u : ℝ | m ≤ clamp01 u}.indicator (fun u => ENNReal.ofReal ((clamp01 u ^ μ / clamp01 u ^ n))) u *
          ENNReal.ofReal (m' ^ n) := by
      intro u
      by_cases hu : u ∈ {u : ℝ | m ≤ clamp01 u}
      · simp only [Set.indicator_of_mem hu]
        have h0 : 0 ≤ clamp01 u := clamp01_nonneg u
        have h3 := momF_nonneg 3 _ h0 n
        have h4 := momF_nonneg 4 0 le_rfl n
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; unfold scG; ring
      · simp [Set.indicator_of_notMem hu]
    have hmu : Measurable fun u : ℝ => {u : ℝ | m ≤ clamp01 u}.indicator
        (fun u => ENNReal.ofReal ((clamp01 u ^ μ / clamp01 u ^ n))) u :=
      (ENNReal.measurable_ofReal.comp (meas_wt measurable_id μ n)).indicator
        (measurableSet_le measurable_const continuous_clamp01.measurable)
    simp_rw [hpt2]
    rw [lintegral_add_right _ (hmu.mul_const _), lintegral_add_right _ (hmu.mul_const _),
      lintegral_mul_const _ hmu, lintegral_mul_const _ hmu]
  rw [hfinal]
  have hA0w : A0 * ENNReal.ofReal w ≤ A0 := by
    calc A0 * ENNReal.ofReal w ≤ A0 * 1 := mul_le_mul' le_rfl hw1'
      _ = A0 := mul_one _
  have hTw : ((P.erase r0).card : ENNReal) * (TW * ENNReal.ofReal (momF 4 0 n / 4 ^ n) * ENNReal.ofReal w) ≤
      TW * ENNReal.ofReal (momF 4 0 n / 4 ^ n) := by
    calc ((P.erase r0).card : ENNReal) * (TW * ENNReal.ofReal (momF 4 0 n / 4 ^ n) * ENNReal.ofReal w)
        = (TW * ENNReal.ofReal (momF 4 0 n / 4 ^ n)) * (((P.erase r0).card : ENNReal) * ENNReal.ofReal w) := by ring
      _ ≤ (TW * ENNReal.ofReal (momF 4 0 n / 4 ^ n)) * 1 := mul_le_mul' le_rfl hcnt
      _ = _ := mul_one _
  exact add_le_add (add_le_add hA0w hTw) le_rfl

end Col

end Census
end IIT
