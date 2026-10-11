/-
Census, B1 small cuts (W12 §6): **the per-cell certificate**.

Cells of the minimal entry: `m_i = 49/100 + i/100` (`i < 51`), `m'_i = m_i + 12/1000`. For each cell a choice
`(L, n, μ)` (table `scTab`) and the Riemann upper sum `scCellR` (`L` cells, monotone bounds: `momF 3 · n` is
increasing, the weight `y^μ/y^n` is monotone) of `∫_{m}^{1} scG m' n μ y dy`. The kernel check `scOK`:
`6 (3/2)^{μ/2} R ≤ 95/100` and `R ≤ 1` for every cell (per-unit rate `≥ ln(6/0.95·…) > ln 3 + …`).

* `momFQ_cast`, `momF_mono`, `sc_weight_le`, **`sc_cell_sound`**, **`scOK_true`**, **`sc_cell_bound`**.
-/
import IIT.Census.B1SmallCutCol

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

/-! ### Rational moments -/

/-- Forward differences over `ℚ`. -/
def iterDQ : ℕ → (ℚ → ℚ) → ℚ → ℚ
  | 0, f => f
  | r + 1, f => fun a => iterDQ r f (a + 1) - iterDQ r f a

/-- `momF` over `ℚ`. -/
def momFQ (r : ℕ) (a : ℚ) (n : ℕ) : ℚ :=
  (n.factorial : ℚ) / ((n + r).factorial : ℚ) * iterDQ r (fun x => x ^ (n + r)) a

lemma iterD_pow_cast (r p : ℕ) (a : ℚ) :
    iterD r (fun x : ℝ => x ^ p) (a : ℝ) = ((iterDQ r (fun x => x ^ p) a : ℚ) : ℝ) := by
  induction r generalizing a with
  | zero => simp [iterD, iterDQ]
  | succ r ih =>
    rw [iterD_succ, show ((a : ℝ) + 1) = ((a + 1 : ℚ) : ℝ) by push_cast; ring, ih, ih]
    simp [iterDQ]

lemma momFQ_cast (r : ℕ) (a : ℚ) (n : ℕ) : ((momFQ r a n : ℚ) : ℝ) = momF r (a : ℝ) n := by
  unfold momFQ momF
  rw [iterD_pow_cast]
  push_cast; ring

/-- `momF r · n` is nondecreasing on `[0, ∞)`. -/
theorem momF_mono (r n : ℕ) : ∀ {a a' : ℝ}, 0 ≤ a → a ≤ a' → momF r a n ≤ momF r a' n := by
  induction r with
  | zero => intro a a' ha haa; rw [momF_zero, momF_zero]; exact pow_le_pow_left₀ ha haa n
  | succ r ih =>
    intro a a' ha haa
    rw [momF_succ, momF_succ]
    refine intervalIntegral.integral_mono_on (by norm_num)
      (((continuous_momF r n).comp (continuous_const.add continuous_id : Continuous fun u : ℝ => a + u)).intervalIntegrable _ _)
      (((continuous_momF r n).comp (continuous_const.add continuous_id : Continuous fun u : ℝ => a' + u)).intervalIntegrable _ _)
      fun u hu => ih (by linarith [hu.1]) (by linarith)

/-- The weight `y^μ/y^n` on a cell is at most its value at one endpoint. -/
lemma sc_weight_le {yl y yr : ℝ} (hyl : 0 < yl) (h1 : yl ≤ y) (h2 : y ≤ yr) (μ n : ℕ) :
    y ^ μ / y ^ n ≤ max (yl ^ μ / yl ^ n) (yr ^ μ / yr ^ n) := by
  have hy : 0 < y := hyl.trans_le h1
  have hyr : 0 < yr := hy.trans_le h2
  rcases le_total n μ with h | h
  · refine le_max_of_le_right ?_
    rw [div_eq_mul_inv, div_eq_mul_inv, ← pow_sub₀ y hy.ne' h, ← pow_sub₀ yr hyr.ne' h]
    exact pow_le_pow_left₀ hy.le h2 _
  · refine le_max_of_le_left ?_
    have e : ∀ z : ℝ, 0 < z → z ^ μ / z ^ n = 1 / z ^ (n - μ) := by
      intro z hz
      rw [pow_sub₀ z hz.ne' h]
      have : (0 : ℝ) < z ^ μ := pow_pos hz _
      have : (0 : ℝ) < z ^ n := pow_pos hz _
      field_simp
    rw [e y hy, e yl hyl]
    exact one_div_le_one_div_of_le (pow_pos hyl _) (pow_le_pow_left₀ hyl.le h1 _)

/-! ### The cell sum -/

/-- The Riemann upper sum for one cell of `m`. -/
def scCellR (m mp : ℚ) (n μ L : ℕ) : ℚ :=
  ∑ l ∈ Finset.range L,
    (max ((m + (1 - m) * l / L) ^ μ / (m + (1 - m) * l / L) ^ n)
        ((m + (1 - m) * (l + 1) / L) ^ μ / (m + (1 - m) * (l + 1) / L) ^ n) *
      ((momFQ 3 (m + (1 - m) * (l + 1) / L) n + momFQ 4 0 n) / 4 ^ n + mp ^ n)) * ((1 - m) / L)

/-- **Soundness of the cell sum.** -/
theorem sc_cell_sound {m mp : ℚ} (hm0 : 0 < m) (hm1 : m < 1) (hmp : 0 < mp) (n μ L : ℕ) (hL : 0 < L) :
    ∫⁻ u, {u : ℝ | (m : ℝ) ≤ clamp01 u}.indicator (fun u => ENNReal.ofReal (scG (mp : ℝ) n μ (clamp01 u))) u ∂unif ≤
      ENNReal.ofReal ((scCellR m mp n μ L : ℚ) : ℝ) := by
  have hm0r : (0 : ℝ) < m := by exact_mod_cast hm0
  have hm1r : (m : ℝ) < 1 := by exact_mod_cast hm1
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  -- reduce to a set integral over `(m, 1]`
  have hred : ∫⁻ u, {u : ℝ | (m : ℝ) ≤ clamp01 u}.indicator
      (fun u => ENNReal.ofReal (scG (mp : ℝ) n μ (clamp01 u))) u ∂unif =
      ∫⁻ y in Set.Icc (m : ℝ) 1, ENNReal.ofReal (scG (mp : ℝ) n μ y) := by
    unfold unif
    rw [← lintegral_indicator measurableSet_Icc]
    rw [lintegral_indicator measurableSet_Icc] at *
    have hset : ∀ u ∈ Set.Icc (0 : ℝ) 1, {u : ℝ | (m : ℝ) ≤ clamp01 u}.indicator
        (fun u => ENNReal.ofReal (scG (mp : ℝ) n μ (clamp01 u))) u =
        (Set.Icc (m : ℝ) 1).indicator (fun y => ENNReal.ofReal (scG (mp : ℝ) n μ y)) u := by
      intro u hu
      by_cases h : (m : ℝ) ≤ u
      · rw [Set.indicator_of_mem (show u ∈ {u : ℝ | (m : ℝ) ≤ clamp01 u} by
          simp only [Set.mem_setOf_eq, clamp01_of_mem hu]; exact h),
          Set.indicator_of_mem (show u ∈ Set.Icc (m : ℝ) 1 from ⟨h, hu.2⟩), clamp01_of_mem hu]
      · rw [Set.indicator_of_notMem (show u ∉ {u : ℝ | (m : ℝ) ≤ clamp01 u} by
          simp only [Set.mem_setOf_eq, clamp01_of_mem hu]; exact h),
          Set.indicator_of_notMem (show u ∉ Set.Icc (m : ℝ) 1 from fun h' => h h'.1)]
    rw [setLIntegral_congr_fun measurableSet_Icc hset, lintegral_indicator measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc,
      Set.inter_eq_left.2 (Set.Icc_subset_Icc hm0r.le le_rfl)]
  rw [hred, ← setLIntegral_congr Ioc_ae_eq_Icc]
  -- the grid
  set c : ℕ → ℝ := fun l => (m : ℝ) + (1 - m) * l / L with hc
  have hcmono : Monotone c := by
    intro l l' h
    simp only [hc]
    have : (l : ℝ) ≤ l' := by exact_mod_cast h
    have : (1 - (m : ℝ)) * l / L ≤ (1 - m) * l' / L :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this (by linarith)) hLr.le
    linarith
  have hc0 : c 0 = m := by simp [hc]
  have hcL : c L = 1 := by simp only [hc]; field_simp; ring
  set B : ℕ → ℝ := fun l => max (c l ^ μ / c l ^ n) (c (l + 1) ^ μ / c (l + 1) ^ n) *
    ((momF 3 (c (l + 1)) n + momF 4 0 n) / 4 ^ n + (mp : ℝ) ^ n) with hB
  have hcpos : ∀ l, 0 < c l := fun l => by
    simp only [hc]; have : 0 ≤ (1 - (m : ℝ)) * l / L := by positivity
    linarith
  have hcell := setLIntegral_Ioc_le_cells c hcmono (fun y => ENNReal.ofReal (scG (mp : ℝ) n μ y)) B L
    (fun l _ y hy => by
      refine ENNReal.ofReal_le_ofReal ?_
      have hyl := hcpos l
      have hy0 : 0 < y := hyl.trans hy.1
      unfold scG
      have hw := sc_weight_le hyl hy.1.le hy.2 μ n
      have h3 := momF_mono 3 n hy0.le hy.2
      have hpos3 := momF_nonneg 3 y hy0.le n
      have hpos4 := momF_nonneg 4 0 le_rfl n
      have hwy : 0 ≤ y ^ μ / y ^ n := by positivity
      have hK : (momF 3 y n + momF 4 0 n) / 4 ^ n + (mp : ℝ) ^ n ≤
          (momF 3 (c (l + 1)) n + momF 4 0 n) / 4 ^ n + (mp : ℝ) ^ n := by
        have : (momF 3 y n + momF 4 0 n) / 4 ^ n ≤ (momF 3 (c (l + 1)) n + momF 4 0 n) / 4 ^ n :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        linarith
      have hK0 : 0 ≤ (momF 3 y n + momF 4 0 n) / 4 ^ n + (mp : ℝ) ^ n := by positivity
      exact mul_le_mul hw hK hK0 (le_trans hwy hw))
  rw [hc0, hcL] at hcell
  refine hcell.trans (le_of_eq ?_)
  -- the cast
  have hBn : ∀ l, 0 ≤ B l := fun l => by
    simp only [hB]
    have := momF_nonneg 3 (c (l + 1)) (hcpos _).le n
    have := momF_nonneg 4 0 le_rfl n
    have : 0 ≤ c l ^ μ / c l ^ n := by have := hcpos l; positivity
    have : 0 ≤ max (c l ^ μ / c l ^ n) (c (l + 1) ^ μ / c (l + 1) ^ n) := le_max_of_le_left this
    positivity
  have hsum : ∑ l ∈ Finset.range L, ENNReal.ofReal (B l) * ENNReal.ofReal (c (l + 1) - c l) =
      ENNReal.ofReal (∑ l ∈ Finset.range L, B l * (c (l + 1) - c l)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => mul_nonneg (hBn l) (sub_nonneg.2 (hcmono (Nat.le_succ l))))]
    exact sum_congr rfl fun l _ => (ENNReal.ofReal_mul (hBn l)).symm
  rw [hsum]
  congr 1
  unfold scCellR
  push_cast
  refine sum_congr rfl fun l _ => ?_
  rw [momFQ_cast, momFQ_cast]
  simp only [hB, hc]
  push_cast
  ring_nf

/-! ### The table and the kernel check -/

/-- `(L, n, μ)` for the cells `i < 51`. -/
def scTab : List (ℕ × ℕ × ℕ) := [(8, 8, 8), (8, 8, 8), (8, 8, 8), (8, 8, 8), (8, 8, 8), (8, 8, 8), (8, 8, 8), (8, 8, 8), (8, 8, 8), (8, 8, 8), (8, 8, 8), (8, 8, 8), (8, 8, 8), (8, 8, 8), (8, 9, 8), (8, 9, 8), (8, 9, 8), (8, 9, 8), (8, 9, 8), (8, 9, 8), (8, 10, 6), (8, 10, 6), (8, 10, 6), (8, 10, 6), (8, 11, 2), (8, 11, 2), (8, 10, 2), (8, 10, 0), (8, 9, 0), (8, 9, 0), (8, 8, 0), (8, 8, 0), (8, 7, 0), (8, 7, 0), (8, 6, 0), (8, 6, 0), (8, 5, 0), (8, 5, 0), (8, 4, 0), (8, 4, 0), (8, 3, 0), (8, 3, 0), (8, 2, 0), (8, 2, 0), (8, 2, 0), (8, 2, 0), (8, 2, 0), (8, 2, 0), (8, 2, 0), (8, 2, 0), (8, 2, 0)]

/-- The cell of the minimal entry. -/
def scM (i : ℕ) : ℚ := 49 / 100 + i / 100

/-- The cap `m' = m + 0.012`. -/
def scMp (i : ℕ) : ℚ := scM i + 12 / 1000

/-- The check of one cell. -/
def scCheck (i : ℕ) : Bool :=
  match scTab.getD i (8, 2, 0) with
  | (L, n, μ) =>
    decide (6 * (3 / 2 : ℚ) ^ (μ / 2) * scCellR (scM i) (scMp i) n μ L ≤ 95 / 100) &&
      decide (scCellR (scM i) (scMp i) n μ L ≤ 1) && decide (0 ≤ scCellR (scM i) (scMp i) n μ L) &&
      decide (μ % 2 = 0) && decide (0 < L) && decide (n ≤ 11) && decide (μ ≤ 8)

theorem scOK : ∀ i < 51, scCheck i = true := by decide +kernel

/-- **The certified bound of one cell.** -/
theorem sc_cell_bound (i : ℕ) (hi : i < 51) : ∃ n μ : ℕ, ∃ R : ℝ, 0 ≤ R ∧ R ≤ 1 ∧
    6 * (3 / 2 : ℝ) ^ (μ / 2) * R ≤ 95 / 100 ∧ μ % 2 = 0 ∧ n ≤ 11 ∧ μ ≤ 8 ∧
    ∫⁻ u, {u : ℝ | ((scM i : ℚ) : ℝ) ≤ clamp01 u}.indicator
      (fun u => ENNReal.ofReal (scG ((scMp i : ℚ) : ℝ) n μ (clamp01 u))) u ∂unif ≤ ENNReal.ofReal R := by
  have hc := scOK i hi
  unfold scCheck at hc
  rcases hT : scTab.getD i (8, 2, 0) with ⟨L, n, μ⟩
  rw [hT] at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
  have hm0 : 0 < scM i := by unfold scM; positivity
  have hm1 : scM i < 1 := by unfold scM; have : (i : ℚ) < 51 := by exact_mod_cast hi
                             linarith
  have hmp : 0 < scMp i := by unfold scMp; positivity
  have h1' : (6 : ℝ) * (3 / 2 : ℝ) ^ (μ / 2) * ((scCellR (scM i) (scMp i) n μ L : ℚ) : ℝ) ≤ 95 / 100 := by
    have := (Rat.cast_le (K := ℝ)).2 h1
    push_cast at this; exact this
  refine ⟨n, μ, ((scCellR (scM i) (scMp i) n μ L : ℚ) : ℝ), by exact_mod_cast h3, by exact_mod_cast h2,
    h1', h4, h6, h7, sc_cell_sound hm0 hm1 hmp n μ L h5⟩

end Census
end IIT
