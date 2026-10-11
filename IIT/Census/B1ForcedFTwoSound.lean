/-
Census, B1 forced leaf 18 (agent "forcedF"): soundness of the two-failure same-side records.

* `GhR lam c y`: the Laurent form of `gX lam c y` above the cap, for every `y`; `gX_le_GhR`: `gX ≤ GhR` on
  `(0, 1]` when `c ≥ 1/2` (equality above the cap; below it, `(λ+1)(GhR - gX)/y = 2λ r^{λ+1} - (λ+1) r^λ + 1 - λ ≥ 0`
  with `r = c/y ≥ 1`).
* `tf_TI_eq`: the record's rational `tfTIq` is the exact value of `∫_{v⁴}^1 y^{P/4} gX(λ, w⁴, y) GhR(λ₂, cap₂, y) dy`.
* `tfRec_sound`: the certified rate inequality.
-/
import IIT.Census.B1ForcedFTwoCertDef
import IIT.Census.CertRSXSound

namespace IIT
namespace Census

open MeasureTheory Finset

/-- The Laurent form of `gX` above the cap (valid for every `y`). -/
noncomputable def GhR (lam : ℕ) (c y : ℝ) : ℝ :=
  binS lam y / (((lam : ℝ) + 1) * 2 ^ lam * y ^ lam) +
    (2 * c * c ^ lam - (2 * c) ^ (lam + 1) / (((lam : ℝ) + 1) * 2 ^ lam)) / y ^ lam - c ^ lam * y / y ^ lam

lemma gX_le_GhR (lam : ℕ) {c y : ℝ} (hy : 0 < y) (hc : 1 / 2 ≤ c) : gX lam c y ≤ GhR lam c y := by
  have hc0 : 0 < c := by linarith
  rcases le_total c y with hcy | hyc
  · rw [gX_above lam hc0 hcy]; rfl
  · rw [gX_below lam hy hyc]
    unfold GhR
    set r := c / y with hr
    have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ hy]; linarith
    have hcr : c = r * y := by rw [hr]; field_simp
    have hyl : 0 < y ^ lam := pow_pos hy lam
    have hl : (0 : ℝ) < (lam : ℝ) + 1 := by positivity
    -- the key polynomial inequality
    have key : 0 ≤ 2 * (lam : ℝ) * r ^ (lam + 1) - ((lam : ℝ) + 1) * r ^ lam + 1 - lam := by
      have hrl : 1 ≤ r ^ lam := one_le_pow₀ hr1
      rcases Nat.eq_zero_or_pos lam with h0 | hpos
      · subst h0; simp
      · have hl1 : (1 : ℝ) ≤ lam := by exact_mod_cast hpos
        have h1 : ((lam : ℝ) - 1) ≤ 2 * lam * r - lam - 1 := by nlinarith
        have h2 : r ^ lam * ((lam : ℝ) - 1) ≤ r ^ lam * (2 * lam * r - lam - 1) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        have h3 : ((lam : ℝ) - 1) ≤ r ^ lam * ((lam : ℝ) - 1) := by nlinarith
        have e : 2 * (lam : ℝ) * r ^ (lam + 1) - ((lam : ℝ) + 1) * r ^ lam + 1 - lam =
            r ^ lam * (2 * lam * r - lam - 1) - ((lam : ℝ) - 1) := by rw [pow_succ]; ring
        rw [e]; linarith
    -- the difference, explicitly
    have hdiff : (binS lam y / (((lam : ℝ) + 1) * 2 ^ lam * y ^ lam) +
        (2 * c * c ^ lam - (2 * c) ^ (lam + 1) / (((lam : ℝ) + 1) * 2 ^ lam)) / y ^ lam - c ^ lam * y / y ^ lam) -
        ((1 - 2 / ((lam : ℝ) + 1)) * y + binS lam y / (((lam : ℝ) + 1) * 2 ^ lam * y ^ lam)) =
        y / ((lam : ℝ) + 1) * (2 * (lam : ℝ) * r ^ (lam + 1) - ((lam : ℝ) + 1) * r ^ lam + 1 - lam) := by
      rw [hcr, mul_pow, mul_pow, mul_pow, pow_succ r lam, pow_succ y lam, pow_succ (2 : ℝ) lam]
      field_simp
      ring
    have : 0 ≤ y / ((lam : ℝ) + 1) * (2 * (lam : ℝ) * r ^ (lam + 1) - ((lam : ℝ) + 1) * r ^ lam + 1 - lam) :=
      mul_nonneg (by positivity) key
    linarith

/-- The real coefficients of `GhR` (cast of `tfCoef`). -/
lemma tfCoef_cast (lam2 : ℕ) (c : ℚ) (k : ℕ) :
    ((tfCoef lam2 c k : ℚ) : ℝ) = ((lam2 + 1).choose k : ℝ) / (((lam2 : ℝ) + 1) * 2 ^ lam2) +
      (if k = 0 then 2 * (c : ℝ) ^ (lam2 + 1) - (2 * (c : ℝ)) ^ (lam2 + 1) / (((lam2 : ℝ) + 1) * 2 ^ lam2) else 0) +
      (if k = 1 then -(c : ℝ) ^ lam2 else 0) := by
  unfold tfCoef
  split_ifs <;> push_cast <;> ring

/-- `y^{P/4} · y^k / y^λ = y^{(P - 4λ + 4k)/4}`. -/
lemma rpow_shift {y : ℝ} (hy : 0 < y) {P lam : ℕ} (h : 4 * lam ≤ P) (k : ℕ) :
    y ^ ((P : ℝ) / 4) * y ^ k / y ^ lam = y ^ (((P - 4 * lam + 4 * k : ℕ) : ℝ) / 4) := by
  have hc : (((P - 4 * lam + 4 * k : ℕ) : ℝ) / 4) = (P : ℝ) / 4 + k - lam := by
    rw [Nat.cast_add, Nat.cast_sub h]; push_cast; ring
  rw [hc, Real.rpow_sub hy, Real.rpow_add hy, Real.rpow_natCast, Real.rpow_natCast]

/-- `y^{P/4} GhR(λ₂, c, y)` as the sum of the shifted monomials. -/
lemma rpow_mul_GhR {y : ℝ} (hy : 0 < y) {P lam2 : ℕ} (h : 4 * lam2 ≤ P) (c : ℚ) :
    y ^ ((P : ℝ) / 4) * GhR lam2 (c : ℝ) y =
      ∑ k ∈ range (lam2 + 2), ((tfCoef lam2 c k : ℚ) : ℝ) * y ^ (((P - 4 * lam2 + 4 * k : ℕ) : ℝ) / 4) := by
  simp_rw [tfCoef_cast, ← rpow_shift hy h]
  have hyl : y ^ lam2 ≠ 0 := pow_ne_zero _ hy.ne'
  have hl : (lam2 : ℝ) + 1 ≠ 0 := by positivity
  set D : ℝ := ((lam2 : ℝ) + 1) * 2 ^ lam2 with hD
  have hD0 : D ≠ 0 := by rw [hD]; positivity
  set Y := y ^ ((P : ℝ) / 4) with hY
  set B : ℝ := 2 * (c : ℝ) ^ (lam2 + 1) - (2 * (c : ℝ)) ^ (lam2 + 1) / D with hB
  simp_rw [add_mul, Finset.sum_add_distrib]
  have h0 : ∑ k ∈ range (lam2 + 2), (if k = 0 then B else 0) * (Y * y ^ k / y ^ lam2) = B * (Y / y ^ lam2) := by
    rw [Finset.sum_eq_single 0 (fun k _ hk => by rw [if_neg hk, zero_mul]) (fun h => absurd (by simp) h)]
    simp
  have h1 : ∑ k ∈ range (lam2 + 2), (if k = 1 then -(c : ℝ) ^ lam2 else 0) * (Y * y ^ k / y ^ lam2) =
      -(c : ℝ) ^ lam2 * (Y * y / y ^ lam2) := by
    rw [Finset.sum_eq_single 1 (fun k _ hk => by rw [if_neg hk, zero_mul]) (fun h => absurd (by simp) h)]
    simp
  have hA : ∑ k ∈ range (lam2 + 2), ((lam2 + 1).choose k : ℝ) / D * (Y * y ^ k / y ^ lam2) =
      Y * (binS lam2 y / (D * y ^ lam2)) := by
    unfold binS
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  rw [h0, h1, hA]
  unfold GhR
  rw [← hD]
  have e2 : (2 * (c : ℝ) * (c : ℝ) ^ lam2 - (2 * (c : ℝ)) ^ (lam2 + 1) / D) = B := by rw [hB, pow_succ]; ring
  rw [e2]
  field_simp
  ring

lemma tfExpOK_spec {lam P : ℕ} (h : tfExpOK lam P = true) :
    (∀ k ∈ range (lam + 2), (P : ℤ) + 4 * k - 4 * lam + 4 ≠ 0) ∧ (P : ℤ) + 8 ≠ 0 ∧
      (P : ℤ) - 4 * lam + 4 ≠ 0 ∧ (P : ℤ) - 4 * lam + 8 ≠ 0 := by
  simp only [tfExpOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hk, h1⟩, h2⟩, h3⟩ := h
  exact ⟨fun k hkm => hk k (Finset.mem_range.1 hkm), h1, h2, h3⟩

lemma GhR_continuousOn (lam : ℕ) (c : ℝ) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun y => GhR lam c y) (Set.Icc a 1) := by
  have hy : ∀ y ∈ Set.Icc a 1, y ^ lam ≠ 0 := fun y hy => pow_ne_zero _ (lt_of_lt_of_le ha hy.1).ne'
  have hy' : ∀ y ∈ Set.Icc a 1, ((lam : ℝ) + 1) * 2 ^ lam * y ^ lam ≠ 0 := fun y hy' => by
    have := hy y hy'; positivity
  unfold GhR binS
  refine ContinuousOn.sub (ContinuousOn.add ?_ ?_) ?_
  · exact ContinuousOn.div (continuousOn_finset_sum _ fun k _ => continuousOn_const.mul (continuousOn_pow k))
      (continuousOn_const.mul (continuousOn_pow lam)) hy'
  · exact ContinuousOn.div continuousOn_const (continuousOn_pow lam) hy
  · exact ContinuousOn.div (continuousOn_const.mul continuousOn_id) (continuousOn_pow lam) hy

lemma rpow_gX_intervalIntegrable (lam : ℕ) (c : ℝ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (q : ℝ) :
    IntervalIntegrable (fun y => y ^ q * gX lam c y) volume a 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le ha1]
  exact (ContinuousOn.rpow_const continuousOn_id fun y hy => Or.inl (lt_of_lt_of_le ha hy.1).ne').mul
    (gX_continuousOn lam _ ha)

/-- **The record's rational is the exact integral.** -/
theorem tf_TI_eq (R : TFRec) (hv : 0 < R.v) (hvw : R.v ≤ R.w) (hw1 : R.w ≤ 1) (h4 : 4 * R.lam2 ≤ R.P)
    (hexp : ∀ k ∈ range (R.lam2 + 2), tfExpOK R.lam (R.P - 4 * R.lam2 + 4 * k) = true) :
    ((tfTIq R : ℚ) : ℝ) =
      ∫ y in ((R.v : ℝ) ^ 4)..1, y ^ ((R.P : ℝ) / 4) * gX R.lam ((R.w : ℝ) ^ 4) y * GhR R.lam2 (R.cap2 : ℝ) y := by
  have hv' : (0 : ℝ) < (R.v : ℝ) ^ 4 := by have : (0 : ℝ) < R.v := by exact_mod_cast hv
                                           positivity
  have hv1 : (R.v : ℝ) ^ 4 ≤ 1 := pow_le_one₀ (by exact_mod_cast hv.le) (by exact_mod_cast hvw.trans hw1)
  have hpt : ∀ y ∈ Set.uIcc ((R.v : ℝ) ^ 4) 1,
      y ^ ((R.P : ℝ) / 4) * gX R.lam ((R.w : ℝ) ^ 4) y * GhR R.lam2 (R.cap2 : ℝ) y =
        ∑ k ∈ range (R.lam2 + 2), ((tfCoef R.lam2 R.cap2 k : ℚ) : ℝ) *
          (y ^ (((R.P - 4 * R.lam2 + 4 * k : ℕ) : ℝ) / 4) * gX R.lam ((R.w : ℝ) ^ 4) y) := by
    intro y hy
    rw [Set.uIcc_of_le hv1] at hy
    have hy0 : 0 < y := lt_of_lt_of_le hv' hy.1
    rw [mul_comm (y ^ ((R.P : ℝ) / 4)) (gX R.lam ((R.w : ℝ) ^ 4) y), mul_assoc, rpow_mul_GhR hy0 h4,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_finset_sum (fun k _ =>
    (rpow_gX_intervalIntegrable R.lam _ hv' hv1 _).const_mul _)]
  unfold tfTIq
  rw [Rat.cast_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Rat.cast_mul]
  rw [intervalIntegral.integral_const_mul]
  obtain ⟨hk', hp, h0, h1⟩ := tfExpOK_spec (hexp k hk)
  rw [cellIq_eq R.v R.w hv hvw hw1 R.lam _ hk' hp h0 h1]

/-- **Soundness of one record**: `TI > 0` and `log 2 + log TI + log rsEx(l2) + (P/4 + l2) x0 ≤ -RT`. -/
theorem tfRec_sound (R : TFRec) (h : tfOK R = true) :
    0 < (∫ y in ((R.v : ℝ) ^ 4)..1, y ^ ((R.P : ℝ) / 4) * gX R.lam ((R.w : ℝ) ^ 4) y *
        GhR R.lam2 (R.cap2 : ℝ) y) ∧
    Real.log 2 + Real.log (∫ y in ((R.v : ℝ) ^ 4)..1, y ^ ((R.P : ℝ) / 4) * gX R.lam ((R.w : ℝ) ^ 4) y *
        GhR R.lam2 (R.cap2 : ℝ) y) + Real.log (rsEx R.l2 : ℝ) + ((R.P : ℝ) / 4 + R.l2) * x0 ≤ -(tfRT : ℝ) := by
  simp only [tfOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hvw⟩, hw1⟩, hv1⟩, hw2⟩, hc2⟩, hc21⟩, h4⟩, hexp⟩, hub⟩, hq⟩, hx⟩, hhi⟩, hrate⟩ := h
  have hexp' : ∀ k ∈ range (R.lam2 + 2), tfExpOK R.lam (R.P - 4 * R.lam2 + 4 * k) = true :=
    fun k hk => hexp k (Finset.mem_range.1 hk)
  have hI := tf_TI_eq R hv hvw hw1 h4 hexp'
  set TI := ∫ y in ((R.v : ℝ) ^ 4)..1, y ^ ((R.P : ℝ) / 4) * gX R.lam ((R.w : ℝ) ^ 4) y *
        GhR R.lam2 (R.cap2 : ℝ) y with hTI
  have hv' : (0 : ℝ) < R.v := by exact_mod_cast hv
  have hv4 : (0 : ℝ) < (R.v : ℝ) ^ 4 := by positivity
  have hv41 : (R.v : ℝ) ^ 4 < 1 := pow_lt_one₀ hv'.le (by exact_mod_cast hv1) (by norm_num)
  have hw4 : (1 : ℝ) / 2 ≤ (R.w : ℝ) ^ 4 := by
    have := (Rat.cast_le (K := ℝ)).2 hw2; push_cast at this; exact this
  have hc2' : (1 : ℝ) / 2 ≤ (R.cap2 : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 hc2; push_cast at this; exact this
  have hpos : 0 < TI := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun y hy => ?_) hv41
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hv41.le]
      exact ((ContinuousOn.rpow_const continuousOn_id fun y hy => Or.inl (lt_of_lt_of_le hv4 hy.1).ne').mul
        (gX_continuousOn R.lam _ hv4)).mul (GhR_continuousOn R.lam2 _ hv4)
    · have hy0 : 0 < y := lt_trans hv4 hy.1
      have hg := gX_pos R.lam (c := (R.w : ℝ) ^ 4) hy0 hy.2.le (by linarith) (by linarith [hy.2])
      have hg2 := gX_pos R.lam2 (c := (R.cap2 : ℝ)) hy0 hy.2.le (by linarith) (by linarith [hy.2])
      have hG := gX_le_GhR R.lam2 hy0 hc2'
      exact mul_pos (mul_pos (Real.rpow_pos_of_pos hy0 _) hg) (lt_of_lt_of_le hg2 hG)
  refine ⟨hpos, ?_⟩
  have hlogI : Real.log TI ≤ Real.log (R.ub : ℝ) :=
    Real.log_le_log hpos (by rw [← hI]; exact_mod_cast hub)
  have hub0 : (0 : ℝ) < R.ub := lt_of_lt_of_le hpos (by rw [← hI]; exact_mod_cast hub)
  have hEx0 : (0 : ℝ) < rsEx R.l2 := by
    have : (0 : ℚ) < rsEx R.l2 := by
      unfold rsEx
      have : ((1 : ℚ) / 2) ^ (R.l2 + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      apply div_pos (by linarith) (by positivity)
    exact_mod_cast this
  have hcr := crLog_le (q := 2 * R.ub * rsEx R.l2) (r := R.r) R.k R.n (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hq, hx⟩, hhi⟩)
  have hsplit : Real.log (((2 * R.ub * rsEx R.l2 : ℚ)) : ℝ) =
      Real.log 2 + Real.log (R.ub : ℝ) + Real.log (rsEx R.l2 : ℝ) := by
    push_cast
    rw [Real.log_mul (by positivity) hEx0.ne', Real.log_mul (by norm_num) hub0.ne']
  have ht : (0 : ℝ) ≤ (R.P : ℝ) / 4 + R.l2 := by positivity
  have hx0 := cr_x0_bounds.2
  have hr : ((R.r : ℚ) : ℝ) + ((R.P : ℝ) / 4 + R.l2) * (crX0hi : ℝ) ≤ -(tfRT : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 hrate; push_cast at this; exact this
  nlinarith [mul_le_mul_of_nonneg_left hx0 ht]

end Census
end IIT
