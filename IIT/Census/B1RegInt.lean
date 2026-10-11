/-
Census, module D1' part 3 (Lemma RS): the exact outer integral of a regime-X cell.

`gX λ c y` is a Laurent polynomial in `y` on each side of `c` (binomial expansion of `(1+y)^{λ+1}`), so
`∫_a^1 y^p gX λ c y dy` is a finite sum of `(b^{e} - a^{e})/e`.  With `a`, `c` rational fourth powers and
`4p ∈ ℕ`, every term is rational: no Riemann sum is needed (the certified margin of the regime-X cells is only
about `3·10⁻⁴`).
-/
import IIT.Census.B1RegMGF

namespace IIT
namespace Census

open Finset

/-- The binomial sum `Σ_{k ≤ λ+1} C(λ+1,k) y^k = (1+y)^{λ+1}`. -/
noncomputable def binS (lam : ℕ) (y : ℝ) : ℝ := ∑ k ∈ range (lam + 2), ((lam + 1).choose k : ℝ) * y ^ k

lemma binS_eq (lam : ℕ) (y : ℝ) : binS lam y = (1 + y) ^ (lam + 1) := by
  unfold binS
  rw [add_comm (1 : ℝ) y, add_pow]
  exact sum_congr rfl fun k _ => by rw [one_pow, mul_one, mul_comm]

/-- **Laurent form of `gX` above the cap** (`y ≥ c`). -/
lemma gX_above (lam : ℕ) {c y : ℝ} (hc : 0 < c) (hcy : c ≤ y) :
    gX lam c y = binS lam y / (((lam : ℝ) + 1) * 2 ^ lam * y ^ lam) +
      (2 * c * c ^ lam - (2 * c) ^ (lam + 1) / (((lam : ℝ) + 1) * 2 ^ lam)) / y ^ lam -
      c ^ lam * y / y ^ lam := by
  have hy : 0 < y := lt_of_lt_of_le hc hcy
  unfold gX
  rw [min_eq_right hcy, min_eq_right ((div_le_one hy).2 hcy), binS_eq]
  have hyl : y ^ lam ≠ 0 := pow_ne_zero _ hy.ne'
  have hl : (lam : ℝ) + 1 ≠ 0 := by positivity
  rw [div_pow, mul_pow]
  field_simp
  ring

/-- **Laurent form of `gX` below the cap** (`0 < y ≤ c`). -/
lemma gX_below (lam : ℕ) {c y : ℝ} (hy : 0 < y) (hyc : y ≤ c) :
    gX lam c y = (1 - 2 / ((lam : ℝ) + 1)) * y + binS lam y / (((lam : ℝ) + 1) * 2 ^ lam * y ^ lam) := by
  unfold gX
  rw [min_eq_left hyc, min_eq_left ((one_le_div hy).2 hyc), binS_eq]
  have hyl : y ^ lam ≠ 0 := pow_ne_zero _ hy.ne'
  have hl : (lam : ℝ) + 1 ≠ 0 := by positivity
  rw [one_pow, mul_one, mul_pow]
  field_simp
  ring

/-- `∫_a^b y^q = (b^{q+1} - a^{q+1})/(q+1)` for `0 < a ≤ b`, `q ≠ -1`. -/
lemma integral_rpow_pos {a b q : ℝ} (ha : 0 < a) (hab : a ≤ b) (hq : q ≠ -1) :
    ∫ y in a..b, y ^ q = (b ^ (q + 1) - a ^ (q + 1)) / (q + 1) := by
  rw [integral_rpow (Or.inr ⟨hq, fun h => by
    rw [Set.uIcc_of_le hab] at h; linarith [h.1]⟩)]

/-- Pointwise: `y^p · gX` above the cap as a combination of real powers. -/
lemma rpow_mul_gX_above (lam : ℕ) {c y p : ℝ} (hc : 0 < c) (hcy : c ≤ y) :
    y ^ p * gX lam c y =
      (∑ k ∈ range (lam + 2), ((lam + 1).choose k : ℝ) / (((lam : ℝ) + 1) * 2 ^ lam) *
          y ^ (p + k - lam)) +
        (2 * c * c ^ lam - (2 * c) ^ (lam + 1) / (((lam : ℝ) + 1) * 2 ^ lam)) * y ^ (p - lam) -
        c ^ lam * y ^ (p + 1 - lam) := by
  have hy : 0 < y := lt_of_lt_of_le hc hcy
  have hpow : ∀ e : ℝ, ∀ k : ℕ, y ^ (e + k - lam) = y ^ e * y ^ k / y ^ lam := fun e k => by
    rw [Real.rpow_sub hy, Real.rpow_add hy, Real.rpow_natCast, Real.rpow_natCast]
  rw [gX_above lam hc hcy, binS]
  have h1 : y ^ (p - lam) = y ^ p * y ^ (0 : ℕ) / y ^ lam := by
    rw [← hpow]; push_cast; ring_nf
  have h2 : y ^ (p + 1 - lam) = y ^ p * y ^ (1 : ℕ) / y ^ lam := by
    rw [← hpow]; push_cast; ring_nf
  rw [h1, h2]
  simp only [hpow, Finset.sum_div, Finset.mul_sum]
  have hyl : y ^ lam ≠ 0 := pow_ne_zero _ hy.ne'
  have hl : (lam : ℝ) + 1 ≠ 0 := by positivity
  rw [mul_sub, mul_add, Finset.mul_sum, pow_zero, pow_one]
  congr 1
  · congr 1
    · refine sum_congr rfl fun k _ => ?_
      field_simp
    · field_simp
  · field_simp

/-- Pointwise: `y^p · gX` below the cap as a combination of real powers. -/
lemma rpow_mul_gX_below (lam : ℕ) {c y p : ℝ} (hy : 0 < y) (hyc : y ≤ c) :
    y ^ p * gX lam c y =
      (1 - 2 / ((lam : ℝ) + 1)) * y ^ (p + 1) +
        ∑ k ∈ range (lam + 2), ((lam + 1).choose k : ℝ) / (((lam : ℝ) + 1) * 2 ^ lam) *
          y ^ (p + k - lam) := by
  have hpow : ∀ e : ℝ, ∀ k : ℕ, y ^ (e + k - lam) = y ^ e * y ^ k / y ^ lam := fun e k => by
    rw [Real.rpow_sub hy, Real.rpow_add hy, Real.rpow_natCast, Real.rpow_natCast]
  rw [gX_below lam hy hyc, binS, Real.rpow_add hy, Real.rpow_one]
  simp only [hpow, Finset.sum_div, Finset.mul_sum]
  have hyl : y ^ lam ≠ 0 := pow_ne_zero _ hy.ne'
  have hl : (lam : ℝ) + 1 ≠ 0 := by positivity
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine sum_congr rfl fun k _ => ?_
    field_simp

/-- `∫_a^b y^q` with the convention used by the certificate. -/
noncomputable def powInt (a b q : ℝ) : ℝ := (b ^ (q + 1) - a ^ (q + 1)) / (q + 1)

lemma rpow_intervalIntegrable {a b q : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun y : ℝ => y ^ q) MeasureTheory.volume a b :=
  intervalIntegral.intervalIntegrable_rpow (Or.inr fun h => by
    rw [Set.uIcc_of_le hab] at h; linarith [h.1])

lemma sum_rpow_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (n : ℕ) (f q : ℕ → ℝ) :
    IntervalIntegrable (fun x : ℝ => ∑ k ∈ range n, f k * x ^ q k) MeasureTheory.volume a b := by
  have := IntervalIntegrable.sum (range n) fun k _ =>
    (rpow_intervalIntegrable ha hab (q := q k)).const_mul (f k)
  simpa only [Finset.sum_fn] using this

/-- **The exact outer integral above the cap.** -/
theorem integral_above (lam : ℕ) {c b p : ℝ} (hc : 0 < c) (hcb : c ≤ b)
    (hk : ∀ k ∈ range (lam + 2), p + k - lam ≠ -1) (h0 : p - lam ≠ -1) (h1 : p + 1 - lam ≠ -1) :
    ∫ y in c..b, y ^ p * gX lam c y =
      (∑ k ∈ range (lam + 2), ((lam + 1).choose k : ℝ) / (((lam : ℝ) + 1) * 2 ^ lam) *
          powInt c b (p + k - lam)) +
        (2 * c * c ^ lam - (2 * c) ^ (lam + 1) / (((lam : ℝ) + 1) * 2 ^ lam)) * powInt c b (p - lam) -
        c ^ lam * powInt c b (p + 1 - lam) := by
  have heq : Set.EqOn (fun y => y ^ p * gX lam c y) (fun y =>
      (∑ k ∈ range (lam + 2), ((lam + 1).choose k : ℝ) / (((lam : ℝ) + 1) * 2 ^ lam) *
          y ^ (p + k - lam)) +
        (2 * c * c ^ lam - (2 * c) ^ (lam + 1) / (((lam : ℝ) + 1) * 2 ^ lam)) * y ^ (p - lam) -
        c ^ lam * y ^ (p + 1 - lam)) (Set.uIcc c b) := fun y hy => by
    rw [Set.uIcc_of_le hcb] at hy
    exact rpow_mul_gX_above lam hc hy.1
  have hI : ∀ q : ℝ, IntervalIntegrable (fun y : ℝ => y ^ q) MeasureTheory.volume c b :=
    fun q => rpow_intervalIntegrable hc hcb
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_sub, intervalIntegral.integral_add,
    intervalIntegral.integral_finset_sum]
  · simp only [intervalIntegral.integral_const_mul]
    rw [integral_rpow_pos hc hcb h0, integral_rpow_pos hc hcb h1]
    congr 2
    exact sum_congr rfl fun k hkm => by rw [integral_rpow_pos hc hcb (hk k hkm)]; rfl
  · exact fun k _ => (hI _).const_mul _
  · exact sum_rpow_intervalIntegrable hc hcb _ _ _
  · exact (hI _).const_mul _
  · exact (sum_rpow_intervalIntegrable hc hcb _ _ _).add ((hI _).const_mul _)
  · exact (hI _).const_mul _

/-- **The exact outer integral below the cap.** -/
theorem integral_below (lam : ℕ) {a b c p : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hk : ∀ k ∈ range (lam + 2), p + k - lam ≠ -1) (hp : p + 1 ≠ -1) :
    ∫ y in a..b, y ^ p * gX lam c y =
      (1 - 2 / ((lam : ℝ) + 1)) * powInt a b (p + 1) +
        ∑ k ∈ range (lam + 2), ((lam + 1).choose k : ℝ) / (((lam : ℝ) + 1) * 2 ^ lam) *
          powInt a b (p + k - lam) := by
  have heq : Set.EqOn (fun y => y ^ p * gX lam c y) (fun y =>
      (1 - 2 / ((lam : ℝ) + 1)) * y ^ (p + 1) +
        ∑ k ∈ range (lam + 2), ((lam + 1).choose k : ℝ) / (((lam : ℝ) + 1) * 2 ^ lam) *
          y ^ (p + k - lam)) (Set.uIcc a b) := fun y hy => by
    rw [Set.uIcc_of_le hab] at hy
    exact rpow_mul_gX_below lam (lt_of_lt_of_le ha hy.1) (hy.2.trans hbc)
  have hI : ∀ q : ℝ, IntervalIntegrable (fun y : ℝ => y ^ q) MeasureTheory.volume a b :=
    fun q => rpow_intervalIntegrable ha hab
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_add,
    intervalIntegral.integral_finset_sum]
  · simp only [intervalIntegral.integral_const_mul]
    rw [integral_rpow_pos ha hab hp]
    congr 1
    exact sum_congr rfl fun k hkm => by rw [integral_rpow_pos ha hab (hk k hkm)]; rfl
  · exact fun k _ => (hI _).const_mul _
  · exact (hI _).const_mul _
  · exact sum_rpow_intervalIntegrable ha hab _ _ _

/-- Real powers of a fourth power: `(v⁴)^{m/4} = v^m`. -/
lemma rpow_fourth (v : ℝ) (hv : 0 < v) (m : ℤ) : (v ^ 4) ^ ((m : ℝ) / 4) = v ^ m := by
  rw [← Real.rpow_natCast v 4, ← Real.rpow_mul hv.le, ← Real.rpow_intCast]
  congr 1; push_cast; ring

/-- `powInt` between fourth powers, for an exponent `q` with `4(q+1) = m`. -/
lemma powInt_fourth {v w : ℝ} (hv : 0 < v) (hw : 0 < w) (m : ℤ) {q : ℝ} (hq : q + 1 = (m : ℝ) / 4) :
    powInt (v ^ 4) (w ^ 4) q = (w ^ m - v ^ m) / ((m : ℝ) / 4) := by
  unfold powInt
  rw [hq, rpow_fourth v hv, rpow_fourth w hw]

/-- **Splitting the outer integral at the cap** (`m_lo ≤ c_m ≤ 1`). -/
theorem integral_split (lam : ℕ) {a c p : ℝ} (ha : 0 < a) (hac : a ≤ c) (hc1 : c ≤ 1)
    (hk : ∀ k ∈ range (lam + 2), p + k - lam ≠ -1) (hp : p + 1 ≠ -1) (h0 : p - lam ≠ -1)
    (h1 : p + 1 - lam ≠ -1) :
    ∫ y in a..1, y ^ p * gX lam c y =
      ((1 - 2 / ((lam : ℝ) + 1)) * powInt a c (p + 1) +
        ∑ k ∈ range (lam + 2), ((lam + 1).choose k : ℝ) / (((lam : ℝ) + 1) * 2 ^ lam) *
          powInt a c (p + k - lam)) +
      ((∑ k ∈ range (lam + 2), ((lam + 1).choose k : ℝ) / (((lam : ℝ) + 1) * 2 ^ lam) *
          powInt c 1 (p + k - lam)) +
        (2 * c * c ^ lam - (2 * c) ^ (lam + 1) / (((lam : ℝ) + 1) * 2 ^ lam)) * powInt c 1 (p - lam) -
        c ^ lam * powInt c 1 (p + 1 - lam)) := by
  have hc : 0 < c := lt_of_lt_of_le ha hac
  have hint : ∀ u v : ℝ, 0 < u → u ≤ v →
      IntervalIntegrable (fun y => y ^ p * gX lam c y) MeasureTheory.volume u v := by
    intro u v hu huv
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le huv]
    refine ContinuousOn.mul (ContinuousOn.rpow_const continuousOn_id fun y hy =>
      Or.inl (lt_of_lt_of_le hu hy.1).ne') ?_
    unfold gX
    have hy : ∀ y ∈ Set.Icc u v, y ≠ 0 := fun y hy => (lt_of_lt_of_le hu hy.1).ne'
    have hmin : ContinuousOn (fun y : ℝ => min y c) (Set.Icc u v) :=
      ContinuousOn.inf continuousOn_id continuousOn_const
    refine ContinuousOn.add (ContinuousOn.mul ((continuousOn_const.mul hmin).sub continuousOn_id)
      ((ContinuousOn.inf continuousOn_const (ContinuousOn.div continuousOn_const continuousOn_id hy)).pow lam))
      (ContinuousOn.div ?_ ?_ fun y hy' => ?_)
    · exact ((continuousOn_const.add continuousOn_id).pow _).sub ((continuousOn_const.mul hmin).pow _)
    · exact continuousOn_const.mul ((continuousOn_const.mul continuousOn_id).pow _)
    · have := hy y hy'; positivity
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint a c ha hac) (hint c 1 hc hc1),
    integral_below lam ha hac le_rfl hk hp, integral_above lam hc hc1 hk h0 h1]

/-! ### The computable rational value of a cell integral -/

/-- `∫_{v⁴}^{w⁴} y^q dy` for `4(q+1) = m`, as a rational. -/
def powIntQ (v w : ℚ) (m : ℤ) : ℚ := (w ^ m - v ^ m) / ((m : ℚ) / 4)

/-- The exact cell integral `∫_{v⁴}^1 y^{P/4} gX λ (w⁴) y dy` for `v ≤ w ≤ 1` (cap inside `[v⁴, 1]`). -/
def cellIq (v w : ℚ) (lam P : ℕ) : ℚ :=
  let a : ℚ := 1 / ((lam + 1) * 2 ^ lam)
  let c : ℚ := w ^ 4
  ((1 - 2 / ((lam : ℚ) + 1)) * powIntQ v w ((P : ℤ) + 8) +
      ∑ k ∈ range (lam + 2), ((lam + 1).choose k : ℚ) * a *
        powIntQ v w ((P : ℤ) + 4 * k - 4 * lam + 4)) +
    ((∑ k ∈ range (lam + 2), ((lam + 1).choose k : ℚ) * a *
        powIntQ w 1 ((P : ℤ) + 4 * k - 4 * lam + 4)) +
      (2 * c * c ^ lam - (2 * c) ^ (lam + 1) * a) * powIntQ w 1 ((P : ℤ) - 4 * lam + 4) -
      c ^ lam * powIntQ w 1 ((P : ℤ) - 4 * lam + 8))

lemma powIntQ_cast {v w : ℚ} (hv : 0 < v) (hw : 0 < w) (m : ℤ) {q : ℝ} (hq : q + 1 = (m : ℝ) / 4) :
    ((powIntQ v w m : ℚ) : ℝ) = powInt ((v : ℝ) ^ 4) ((w : ℝ) ^ 4) q := by
  rw [powInt_fourth (by exact_mod_cast hv) (by exact_mod_cast hw) m hq, powIntQ]
  push_cast; ring

/-- **The cell integral equals the computable rational** (`0 < v ≤ w ≤ 1`, all exponents `≠ -1`). -/
theorem cellIq_eq (v w : ℚ) (hv : 0 < v) (hvw : v ≤ w) (hw1 : w ≤ 1) (lam P : ℕ)
    (hk : ∀ k ∈ range (lam + 2), (P : ℤ) + 4 * k - 4 * lam + 4 ≠ 0) (hp : (P : ℤ) + 8 ≠ 0)
    (h0 : (P : ℤ) - 4 * lam + 4 ≠ 0) (h1 : (P : ℤ) - 4 * lam + 8 ≠ 0) :
    ((cellIq v w lam P : ℚ) : ℝ) =
      ∫ y in ((v : ℝ) ^ 4)..1, y ^ ((P : ℝ) / 4) * gX lam ((w : ℝ) ^ 4) y := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hw' : (0 : ℝ) < w := by exact_mod_cast (lt_of_lt_of_le hv hvw)
  have hvw' : (v : ℝ) ^ 4 ≤ (w : ℝ) ^ 4 := pow_le_pow_left₀ hv'.le (by exact_mod_cast hvw) 4
  have hw1' : (w : ℝ) ^ 4 ≤ 1 := pow_le_one₀ hw'.le (by exact_mod_cast hw1)
  have hcast : ∀ m : ℤ, ((m : ℝ) / 4 - 1) + 1 = (m : ℝ) / 4 := fun m => by ring
  -- exponent conditions in real form
  have hne : ∀ m : ℤ, m ≠ 0 → (m : ℝ) / 4 - 1 ≠ -1 := fun m hm h => by
    have : (m : ℝ) = 0 := by linarith
    exact hm (by exact_mod_cast this)
  have hkR : ∀ k ∈ range (lam + 2), (P : ℝ) / 4 + k - lam ≠ -1 := fun k hkm h => by
    apply hk k hkm; have : (((P : ℤ) + 4 * k - 4 * lam + 4 : ℤ) : ℝ) = 0 := by push_cast; linarith
    exact_mod_cast this
  have hpR : (P : ℝ) / 4 + 1 ≠ -1 := fun h => hp (by
    have : (((P : ℤ) + 8 : ℤ) : ℝ) = 0 := by push_cast; linarith
    exact_mod_cast this)
  have h0R : (P : ℝ) / 4 - lam ≠ -1 := fun h => h0 (by
    have : (((P : ℤ) - 4 * lam + 4 : ℤ) : ℝ) = 0 := by push_cast; linarith
    exact_mod_cast this)
  have h1R : (P : ℝ) / 4 + 1 - lam ≠ -1 := fun h => h1 (by
    have : (((P : ℤ) - 4 * lam + 8 : ℤ) : ℝ) = 0 := by push_cast; linarith
    exact_mod_cast this)
  rw [integral_split lam (by positivity) hvw' hw1' hkR hpR h0R h1R]
  have e1 : ∀ (a b : ℚ) (m : ℤ) (q : ℝ), 0 < a → 0 < b → q + 1 = (m : ℝ) / 4 →
      powInt ((a : ℝ) ^ 4) ((b : ℝ) ^ 4) q = ((powIntQ a b m : ℚ) : ℝ) :=
    fun a b m q ha hb hq => (powIntQ_cast ha hb m hq).symm
  have e1one : ∀ (a : ℚ) (m : ℤ) (q : ℝ), 0 < a → q + 1 = (m : ℝ) / 4 →
      powInt ((a : ℝ) ^ 4) 1 q = ((powIntQ a 1 m : ℚ) : ℝ) := fun a m q ha hq => by
    have := e1 a 1 m q ha one_pos hq; simpa using this
  rw [show powInt ((v : ℝ) ^ 4) ((w : ℝ) ^ 4) ((P : ℝ) / 4 + 1) =
      ((powIntQ v w ((P : ℤ) + 8) : ℚ) : ℝ) from
    e1 v w ((P : ℤ) + 8) _ hv (lt_of_lt_of_le hv hvw) (by push_cast; ring)]
  rw [show powInt ((w : ℝ) ^ 4) 1 ((P : ℝ) / 4 - lam) =
      ((powIntQ w 1 ((P : ℤ) - 4 * lam + 4) : ℚ) : ℝ) from
    e1one w ((P : ℤ) - 4 * lam + 4) _ (lt_of_lt_of_le hv hvw) (by push_cast; ring)]
  rw [show powInt ((w : ℝ) ^ 4) 1 ((P : ℝ) / 4 + 1 - lam) =
      ((powIntQ w 1 ((P : ℤ) - 4 * lam + 8) : ℚ) : ℝ) from
    e1one w ((P : ℤ) - 4 * lam + 8) _ (lt_of_lt_of_le hv hvw) (by push_cast; ring)]
  rw [sum_congr rfl fun k _ => show ((lam + 1).choose k : ℝ) / (((lam : ℝ) + 1) * 2 ^ lam) *
      powInt ((v : ℝ) ^ 4) ((w : ℝ) ^ 4) ((P : ℝ) / 4 + k - lam) =
      ((((lam + 1).choose k : ℚ) * (1 / ((lam + 1) * 2 ^ lam)) *
        powIntQ v w ((P : ℤ) + 4 * k - 4 * lam + 4) : ℚ) : ℝ) from by
    rw [e1 v w ((P : ℤ) + 4 * k - 4 * lam + 4) _ hv (lt_of_lt_of_le hv hvw) (by push_cast; ring)]
    push_cast; ring]
  rw [sum_congr rfl fun k _ => show ((lam + 1).choose k : ℝ) / (((lam : ℝ) + 1) * 2 ^ lam) *
      powInt ((w : ℝ) ^ 4) 1 ((P : ℝ) / 4 + k - lam) =
      ((((lam + 1).choose k : ℚ) * (1 / ((lam + 1) * 2 ^ lam)) *
        powIntQ w 1 ((P : ℤ) + 4 * k - 4 * lam + 4) : ℚ) : ℝ) from by
    rw [e1one w ((P : ℤ) + 4 * k - 4 * lam + 4) _ (lt_of_lt_of_le hv hvw) (by push_cast; ring)]
    push_cast; ring]
  unfold cellIq
  push_cast
  ring

end Census
end IIT
