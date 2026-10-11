/-
Census, B1 count, WP1 (generic toolkit, no IIT), part 3: the two consumer forms of GC
(blueprint `B1-W14-count-lean.md` §6, used by WP5/WP6).

* `gc_interval`: `P(a σ < S ≤ b σ) ≤ (b - a)/√(2π) + 2 C n^{-1/8}`;
* `gc_tail`: `|P(|S| ≥ z σ) - 2 Q(z)| ≤ 2 C n^{-1/8}` for `z ≥ 0` (`Q(z) = N(0,1)(z, ∞)`).
  NOTE: the hypothesis `0 ≤ z` is necessary (for `z → -∞` the left side tends to `|1 - 2| = 1`).
Gaussian facts: `gauss_singleton`, `gauss_Ici`, `gauss_symm` (`Φ(-z) = Q(z)`), `gauss_Ioi` (`Q = 1 - Φ`).
-/
import IIT.Census.B1CntTool2

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

noncomputable section

/-! ### Gaussian facts -/

lemma gauss_singleton (z : ℝ) : gaussianReal 0 1 {z} = 0 := by
  rw [gaussianReal_apply 0 one_ne_zero]
  exact setLIntegral_measure_zero _ _ Real.volume_singleton

lemma gauss_Ici (z : ℝ) :
    (gaussianReal 0 1).real (Set.Ici z) = (gaussianReal 0 1).real (Set.Ioi z) := by
  have hs : Set.Ici z = Set.Ioi z ∪ {z} := by
    ext y
    simp only [Set.mem_Ici, Set.mem_union, Set.mem_Ioi, Set.mem_singleton_iff]
    constructor
    · intro h; rcases eq_or_lt_of_le h with h | h
      · exact Or.inr h.symm
      · exact Or.inl h
    · rintro (h | h)
      · exact h.le
      · exact h.ge
  rw [hs, measureReal_union (s₁ := Set.Ioi z) (s₂ := {z}) (by simp) (measurableSet_singleton z)]
  simp [measureReal_def, gauss_singleton]

/-- `Φ(-z) = Q(z)`. -/
lemma gauss_symm (z : ℝ) :
    (gaussianReal 0 1).real (Set.Iic (-z)) = (gaussianReal 0 1).real (Set.Ioi z) := by
  have h := gaussianReal_map_neg (μ := 0) (v := 1)
  rw [neg_zero] at h
  rw [← gauss_Ici]
  conv_lhs => rw [← h]
  rw [map_measureReal_apply measurable_neg measurableSet_Iic]
  congr 1
  ext y
  simp

/-- `Q(z) = 1 - Φ(z)`. -/
lemma gauss_Ioi (z : ℝ) :
    (gaussianReal 0 1).real (Set.Ioi z) = 1 - (gaussianReal 0 1).real (Set.Iic z) := by
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

/-! ### GC with a strict inequality -/

lemma gc_lt_bound {C : ℝ}
    (h : ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      |((Measure.pi fun _ : Fin n => unif)
          {u | ∑ l, (u l - 1 / 2) ≤ x * Real.sqrt ((n : ℝ) / 12)}).toReal
        - (gaussianReal 0 1 (Set.Iic x)).toReal| ≤ C * (n : ℝ) ^ (-(1 / 8 : ℝ)))
    {n : ℕ} (hn : 0 < n) (x : ℝ) :
    |(Measure.pi fun _ : Fin n => unif).real
        {u | ∑ l, (u l - 1 / 2) < x * Real.sqrt ((n : ℝ) / 12)}
      - (gaussianReal 0 1).real (Set.Iic x)| ≤ C * (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
  have hσ : 0 < Real.sqrt ((n : ℝ) / 12) := Real.sqrt_pos.2 (by positivity)
  have hx := abs_sub_le_iff.1 (h n hn x)
  simp only [← measureReal_def] at hx
  rw [abs_sub_le_iff]
  constructor
  · have hm : (Measure.pi fun _ : Fin n => unif).real
        {u | ∑ l, (u l - 1 / 2) < x * Real.sqrt ((n : ℝ) / 12)} ≤
        (Measure.pi fun _ : Fin n => unif).real
        {u | ∑ l, (u l - 1 / 2) ≤ x * Real.sqrt ((n : ℝ) / 12)} :=
      measureReal_mono fun u hu => by
        simp only [Set.mem_ofPred_eq] at hu ⊢; exact le_of_lt hu
    linarith [hx.1]
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hd := abs_sub_le_iff.1 (h n hn (x - δ))
    simp only [← measureReal_def] at hd
    have hl := abs_sub_le_iff.1 (gaussCDF_lip (x - δ) x)
    simp only [← measureReal_def, show x - δ - x = -δ by ring, abs_neg, abs_of_pos hδ] at hl
    have hs : 1 ≤ Real.sqrt (2 * Real.pi) := Real.one_le_sqrt.2 (by nlinarith [Real.pi_gt_three])
    have hdiv : δ / Real.sqrt (2 * Real.pi) ≤ δ := div_le_self hδ.le hs
    have hm : (Measure.pi fun _ : Fin n => unif).real
        {u | ∑ l, (u l - 1 / 2) ≤ (x - δ) * Real.sqrt ((n : ℝ) / 12)} ≤
        (Measure.pi fun _ : Fin n => unif).real
        {u | ∑ l, (u l - 1 / 2) < x * Real.sqrt ((n : ℝ) / 12)} :=
      measureReal_mono fun u hu => by
        simp only [Set.mem_ofPred_eq] at hu ⊢
        have : (x - δ) * Real.sqrt ((n : ℝ) / 12) < x * Real.sqrt ((n : ℝ) / 12) := by nlinarith
        linarith
    linarith [hd.2, hl.2]

/-! ### The consumer forms -/

/-- **GC on an interval.** -/
theorem gc_interval (hGC : GCStmt) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ a b : ℝ, a ≤ b →
    (Measure.pi fun _ : Fin n => unif)
        {u | a * Real.sqrt ((n : ℝ) / 12) < ∑ l, (u l - 1 / 2) ∧
          ∑ l, (u l - 1 / 2) ≤ b * Real.sqrt ((n : ℝ) / 12)} ≤
      ENNReal.ofReal ((b - a) / Real.sqrt (2 * Real.pi) + 2 * C * (n : ℝ) ^ (-(1 / 8 : ℝ))) := by
  obtain ⟨C, hC, h⟩ := hGC
  refine ⟨C, hC, fun n hn a b hab => ?_⟩
  have hσ : 0 ≤ Real.sqrt ((n : ℝ) / 12) := Real.sqrt_nonneg _
  have hsub : {u : Fin n → ℝ | ∑ l, (u l - 1 / 2) ≤ a * Real.sqrt ((n : ℝ) / 12)} ⊆
      {u | ∑ l, (u l - 1 / 2) ≤ b * Real.sqrt ((n : ℝ) / 12)} :=
    fun u hu => by
      simp only [Set.mem_ofPred_eq] at hu ⊢; exact le_trans hu (mul_le_mul_of_nonneg_right hab hσ)
  have hset : {u : Fin n → ℝ | a * Real.sqrt ((n : ℝ) / 12) < ∑ l, (u l - 1 / 2) ∧
        ∑ l, (u l - 1 / 2) ≤ b * Real.sqrt ((n : ℝ) / 12)} =
      {u | ∑ l, (u l - 1 / 2) ≤ b * Real.sqrt ((n : ℝ) / 12)} \
        {u | ∑ l, (u l - 1 / 2) ≤ a * Real.sqrt ((n : ℝ) / 12)} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_le]
    tauto
  rw [hset, ← ofReal_measureReal, measureReal_sdiff hsub (measurableSet_le (by fun_prop) measurable_const)]
  apply ENNReal.ofReal_le_ofReal
  have ha := abs_sub_le_iff.1 (h n hn a)
  have hb := abs_sub_le_iff.1 (h n hn b)
  have hl := abs_sub_le_iff.1 (gaussCDF_lip b a)
  rw [abs_of_nonneg (sub_nonneg.2 hab)] at hl
  simp only [← measureReal_def] at ha hb hl
  linarith [ha.2, hb.1, hl.1]

/-- **GC for the two-sided tail** (`z ≥ 0`). -/
theorem gc_tail (hGC : GCStmt) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ z : ℝ, 0 ≤ z →
    |((Measure.pi fun _ : Fin n => unif)
        {u | z * Real.sqrt ((n : ℝ) / 12) ≤ |∑ l, (u l - 1 / 2)|}).toReal -
      2 * (ProbabilityTheory.gaussianReal 0 1 (Set.Ioi z)).toReal| ≤
        2 * C * (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := hGC
  refine ⟨C, hC, fun n hn z hz => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hε : 0 < (n : ℝ) ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos hn' _
  have hσ : 0 < Real.sqrt ((n : ℝ) / 12) := Real.sqrt_pos.2 (by positivity)
  rw [← measureReal_def, ← measureReal_def]
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · -- `z = 0`: both sides are `1`
    subst hz0
    have hQ : (gaussianReal 0 1).real (Set.Ioi 0) = 1 / 2 := by
      have h1 := gauss_symm 0
      have h2 := gauss_Ioi 0
      rw [neg_zero] at h1
      linarith
    have hU : {u : Fin n → ℝ | 0 * Real.sqrt ((n : ℝ) / 12) ≤ |∑ l, (u l - 1 / 2)|} = Set.univ := by
      ext u; simp
    rw [hU, hQ, probReal_univ]
    norm_num
    positivity
  · -- `z > 0`: the two tails are disjoint
    set σ := Real.sqrt ((n : ℝ) / 12) with hσdef
    have hzσ : 0 < z * σ := mul_pos hzpos hσ
    have hset : {u : Fin n → ℝ | z * σ ≤ |∑ l, (u l - 1 / 2)|} =
        {u | ∑ l, (u l - 1 / 2) < z * σ}ᶜ ∪ {u | ∑ l, (u l - 1 / 2) ≤ (-z) * σ} := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, not_lt, le_abs, neg_mul]
      constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (by linarith)
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (by linarith)
    have hdisj : Disjoint ({u : Fin n → ℝ | ∑ l, (u l - 1 / 2) < z * σ}ᶜ)
        {u | ∑ l, (u l - 1 / 2) ≤ (-z) * σ} := by
      refine Set.disjoint_left.2 fun u h1 h2 => ?_
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at h1 h2
      nlinarith
    have hmlt : MeasurableSet {u : Fin n → ℝ | ∑ l, (u l - 1 / 2) < z * σ} :=
      measurableSet_lt (by fun_prop) measurable_const
    rw [hset, measureReal_union hdisj (measurableSet_le (by fun_prop) measurable_const),
      probReal_compl_eq_one_sub hmlt]
    have h1 := abs_sub_le_iff.1 (gc_lt_bound h hn z)
    have h2 := abs_sub_le_iff.1 (h n hn (-z))
    simp only [← measureReal_def] at h2
    have hq1 := gauss_Ioi z
    have hq2 := gauss_symm z
    rw [abs_sub_le_iff]
    constructor
    · linarith [h1.2, h2.1]
    · linarith [h1.1, h2.2]

end

end Census
end IIT
