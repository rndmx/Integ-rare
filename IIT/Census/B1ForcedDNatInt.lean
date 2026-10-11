/-
Census, B1 forced leaf 7 (natural regime): the real-analysis side of the natural-cell certificate.

* `dn_y_factor`  : the tc-row column factor `∫_{y ≥ v⁴} y^p e^{-μ 1{y > c}} ≤ ∫_{v⁴}^c y^p + e^{-μ} ∫_c^1 y^p`;
* `dn_fold_factor`: the row-`s` factor `E[x^q] = 2 (1 - 2^{-(q+1)})/(q+1)`, `x = max(y, 1 - y)`, real `q ≥ 0`;
* `dn_e2_le`, `dn_expLo_le`, `dn_rpow_four`: casting the rational data of `B1ForcedDNatCert`.
-/
import IIT.Census.B1ForcedDNatCert
import IIT.Census.B1Chernoff

namespace IIT
namespace Census

open MeasureTheory Finset

noncomputable section

/-- `∫_a^b y^p` over `(a, b]`, `0 < a`. -/
lemma dn_setLIntegral_rpow {a b p : ℝ} (ha : 0 < a) (hab : a ≤ b) (hp : p ≠ -1) :
    ∫⁻ u in Set.Ioc a b, ENNReal.ofReal (u ^ p) = ENNReal.ofReal ((b ^ (p + 1) - a ^ (p + 1)) / (p + 1)) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]; intro h; linarith [h.1]
  rw [setLIntegral_Ioc_ofReal hab (intervalIntegral.intervalIntegrable_rpow (Or.inr h0))
    (fun u hu => Real.rpow_nonneg (by linarith [hu.1]) _), integral_rpow (Or.inr ⟨hp, h0⟩)]

/-- `(b^q - a^q)/q ≥ 0` for `0 < a ≤ b`, `q = p + 1 ≠ 0`. -/
lemma dn_div_rpow_nonneg {a b p : ℝ} (ha : 0 < a) (hab : a ≤ b) (hp : p ≠ -1) :
    0 ≤ (b ^ (p + 1) - a ^ (p + 1)) / (p + 1) := by
  rcases lt_or_gt_of_ne (show p + 1 ≠ 0 by intro h; exact hp (by linarith)) with h | h
  · exact div_nonneg_of_nonpos (by linarith [Real.rpow_le_rpow_of_nonpos ha hab h.le]) h.le
  · exact div_nonneg (by linarith [Real.rpow_le_rpow ha.le hab h.le]) h.le

/-- **The tc-row column factor.** -/
theorem dn_y_factor {v4 c p μ : ℝ} (hv : 0 < v4) (hvc : v4 ≤ c) (hc1 : c ≤ 1) (hp : p ≠ -1) :
    ∫⁻ y in {y : ℝ | v4 ≤ clamp01 y},
        ENNReal.ofReal (Real.exp (p * Real.log (clamp01 y) - μ * (if c < clamp01 y then 1 else 0))) ∂unif ≤
      ENNReal.ofReal ((c ^ (p + 1) - v4 ^ (p + 1)) / (p + 1) +
        Real.exp (-μ) * ((1 - c ^ (p + 1)) / (p + 1))) := by
  have hmeasW : MeasurableSet {y : ℝ | v4 ≤ clamp01 y} := measurableSet_le measurable_const clamp01_measurable
  set F : ℝ → ENNReal := fun u =>
    if v4 ≤ u then ENNReal.ofReal (Real.exp (p * Real.log u - μ * (if c < u then 1 else 0))) else 0 with hF
  have e1 : ∫⁻ y in {y : ℝ | v4 ≤ clamp01 y},
      ENNReal.ofReal (Real.exp (p * Real.log (clamp01 y) - μ * (if c < clamp01 y then 1 else 0))) ∂unif =
      ∫⁻ y, F (clamp01 y) ∂unif := by
    rw [← lintegral_indicator hmeasW]
    refine lintegral_congr fun y => ?_
    simp only [Set.indicator, Set.mem_setOf_eq, hF]
  rw [e1, lintegral_unif_clamp F, lintegral_unif_eq_Ioc]
  set G : ℝ → ENNReal := fun u =>
    (Set.Icc v4 c).indicator (fun u => ENNReal.ofReal (u ^ p)) u +
      (Set.Ioc c 1).indicator (fun u => ENNReal.ofReal (Real.exp (-μ) * u ^ p)) u with hG
  have hFG : ∀ u ∈ Set.Ioc (0 : ℝ) 1, F u ≤ G u := by
    intro u hu
    simp only [hF, hG]
    split_ifs with h1 h2
    · -- `c < u`
      have hu0 : 0 < u := hu.1
      have hnot : u ∉ Set.Icc v4 c := fun h => absurd h.2 (not_le.2 h2)
      rw [Set.indicator_of_notMem hnot, zero_add, Set.indicator_of_mem (show u ∈ Set.Ioc c 1 from ⟨h2, hu.2⟩)]
      apply ENNReal.ofReal_le_ofReal
      rw [mul_one, sub_eq_add_neg, Real.exp_add, Real.rpow_def_of_pos hu0, mul_comm (Real.log u), mul_comm]
    · have hu0 : 0 < u := hu.1
      rw [Set.indicator_of_mem (show u ∈ Set.Icc v4 c from ⟨h1, not_lt.1 h2⟩)]
      refine le_trans (le_of_eq ?_) le_self_add
      rw [mul_zero, sub_zero, Real.rpow_def_of_pos hu0, mul_comm]
    · exact bot_le
  have hmeas1 : Measurable fun u : ℝ => ENNReal.ofReal (u ^ p) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const p)
  have hmeas2 : Measurable fun u : ℝ => ENNReal.ofReal (Real.exp (-μ) * u ^ p) :=
    ENNReal.measurable_ofReal.comp ((measurable_id.pow_const p).const_mul _)
  calc ∫⁻ u in Set.Ioc (0 : ℝ) 1, F u
      ≤ ∫⁻ u in Set.Ioc (0 : ℝ) 1, G u := setLIntegral_mono' measurableSet_Ioc hFG
    _ ≤ ∫⁻ u, G u := setLIntegral_le_lintegral _ _
    _ = (∫⁻ u in Set.Icc v4 c, ENNReal.ofReal (u ^ p)) +
          ∫⁻ u in Set.Ioc c 1, ENNReal.ofReal (Real.exp (-μ) * u ^ p) := by
        rw [lintegral_add_left (hmeas1.indicator measurableSet_Icc), lintegral_indicator measurableSet_Icc,
          lintegral_indicator measurableSet_Ioc]
    _ = ENNReal.ofReal ((c ^ (p + 1) - v4 ^ (p + 1)) / (p + 1)) +
          ENNReal.ofReal (Real.exp (-μ) * ((1 - c ^ (p + 1)) / (p + 1))) := by
        congr 1
        · rw [← setLIntegral_congr Ioc_ae_eq_Icc]
          exact dn_setLIntegral_rpow hv hvc hp
        · have hc0 : 0 < c := lt_of_lt_of_le hv hvc
          rw [setLIntegral_Ioc_ofReal hc1
            ((intervalIntegral.intervalIntegrable_rpow (Or.inr (by
              rw [Set.uIcc_of_le hc1]; intro h; linarith [h.1]))).const_mul _)
            (fun u hu => mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith [hu.1]) _)),
            intervalIntegral.integral_const_mul,
            integral_rpow (Or.inr ⟨hp, by rw [Set.uIcc_of_le hc1]; intro h; linarith [h.1]⟩),
            Real.one_rpow]
    _ = _ := by
        have hc0 : 0 < c := lt_of_lt_of_le hv hvc
        rw [ENNReal.ofReal_add (dn_div_rpow_nonneg hv hvc hp)
          (mul_nonneg (Real.exp_pos _).le (by
            simpa [Real.one_rpow] using dn_div_rpow_nonneg hc0 hc1 hp))]

/-- `max(u, 1-u) ≥ 1/2`. -/
lemma dn_fold_ge (u : ℝ) : 1 / 2 ≤ max u (1 - u) := by
  rcases le_total u (1 / 2) with h | h
  · exact le_max_of_le_right (by linarith)
  · exact le_max_of_le_left h

/-- **The row-`s` factor**: `E[max(y, 1 - y)^q] = 2 (1 - 2^{-(q+1)})/(q+1)` for real `q ≥ 0`. -/
theorem dn_fold_factor {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (q * Real.log (max (clamp01 x) (1 - clamp01 x)))) ∂unif =
      ENNReal.ofReal (2 * (1 - (1 / 2 : ℝ) ^ (q + 1)) / (q + 1)) := by
  have hpos : ∀ u : ℝ, 0 < max u (1 - u) := fun u => lt_of_lt_of_le (by norm_num) (dn_fold_ge u)
  have e0 : ∀ x : ℝ, ENNReal.ofReal (Real.exp (q * Real.log (max (clamp01 x) (1 - clamp01 x)))) =
      (fun u => ENNReal.ofReal (max u (1 - u) ^ q)) (clamp01 x) := by
    intro x
    show _ = ENNReal.ofReal (max (clamp01 x) (1 - clamp01 x) ^ q)
    rw [Real.rpow_def_of_pos (hpos _), mul_comm]
  simp_rw [e0]
  have hc : Continuous fun u : ℝ => max u (1 - u) ^ q :=
    (continuous_id.max (continuous_const.sub continuous_id)).rpow_const fun u => Or.inl (hpos u).ne'
  rw [lintegral_unif_clamp (fun u => ENNReal.ofReal (max u (1 - u) ^ q)),
    lintegral_unif_ofReal (hc.intervalIntegrable 0 1) fun u _ => Real.rpow_nonneg (hpos u).le _,
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (1 / 2))
      (hc.intervalIntegrable (1 / 2) 1)]
  have e1 : ∫ u in (0 : ℝ)..1 / 2, max u (1 - u) ^ q = ∫ u in (1 / 2 : ℝ)..1, u ^ q := by
    rw [intervalIntegral.integral_congr (g := fun u => (1 - u) ^ q) fun u hu => ?_]
    · have := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ q) (1 : ℝ) (a := 0) (b := 1 / 2)
      rw [this]; norm_num
    · rw [Set.uIcc_of_le (by norm_num)] at hu
      show max u (1 - u) ^ q = (1 - u) ^ q
      rw [max_eq_right (by linarith [hu.2])]
  have e2 : ∫ u in (1 / 2 : ℝ)..1, max u (1 - u) ^ q = ∫ u in (1 / 2 : ℝ)..1, u ^ q := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hu
    show max u (1 - u) ^ q = u ^ q
    rw [max_eq_left (by linarith [hu.1])]
  rw [e1, e2, integral_rpow (Or.inl (by linarith)), Real.one_rpow]
  congr 1
  ring

/-- `e2 ≤ 2^{-(L/4 + 1)}` from `e2⁴ 2^{L+4} ≤ 1`. -/
lemma dn_e2_le {e2 : ℚ} {L : ℕ} (h0 : 0 ≤ e2) (h : e2 ^ 4 * 2 ^ (L + 4) ≤ 1) :
    (e2 : ℝ) ≤ (1 / 2 : ℝ) ^ ((L : ℝ) / 4 + 1) := by
  have h0' : (0 : ℝ) ≤ e2 := by exact_mod_cast h0
  have hR : ((e2 : ℝ)) ^ 4 * 2 ^ (L + 4) ≤ 1 := by exact_mod_cast h
  have hb : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ ((L : ℝ) / 4 + 1) := Real.rpow_nonneg (by norm_num) _
  have e4 : ((1 / 2 : ℝ) ^ ((L : ℝ) / 4 + 1)) ^ 4 = (1 / 2 : ℝ) ^ (L + 4) := by
    rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_natCast]
    congr 1; push_cast; ring
  have h2 : (0 : ℝ) < 2 ^ (L + 4) := by positivity
  have : (e2 : ℝ) ^ 4 ≤ ((1 / 2 : ℝ) ^ ((L : ℝ) / 4 + 1)) ^ 4 := by
    rw [e4, one_div_pow, le_div_iff₀ h2]; exact hR
  exact (pow_le_pow_iff_left₀ h0' hb (by norm_num)).1 this

lemma dnExpLo_cast (x : ℚ) (n : ℕ) :
    ((dnExpLo x n : ℚ) : ℝ) = ∑ i ∈ range n, (x : ℝ) ^ i / (i.factorial : ℝ) := by
  induction n with
  | zero => simp [dnExpLo]
  | succ n ih => rw [dnExpLo, sum_range_succ, ← ih]; push_cast; ring

/-- The rational exponential lower bound. -/
lemma dn_expLo_le {x : ℚ} (hx : 0 ≤ x) (n : ℕ) : ((dnExpLo x n : ℚ) : ℝ) ≤ Real.exp x := by
  rw [dnExpLo_cast]
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast hx) n

/-- `(v⁴)^{P/4 + 1} = v^{P+4}` for `v > 0`. -/
lemma dn_rpow_four {v : ℝ} (hv : 0 < v) (P : ℤ) :
    (v ^ 4) ^ ((P : ℝ) / 4 + 1) = v ^ (P + 4) := by
  rw [← Real.rpow_natCast_mul hv.le, show ((4 : ℕ) : ℝ) * ((P : ℝ) / 4 + 1) = ((P + 4 : ℤ) : ℝ) by push_cast; ring,
    Real.rpow_intCast]

/-- The real cell integral equals the rational `dnIq`. -/
lemma dn_Iq_eq {v w : ℚ} (hv : 0 < v) (hw : 0 < w) (P : ℤ) (a : ℕ) :
    (((w : ℝ) ^ 4) ^ ((P : ℝ) / 4 + 1) - ((v : ℝ) ^ 4) ^ ((P : ℝ) / 4 + 1)) / ((P : ℝ) / 4 + 1) +
        Real.exp (-(a * Real.log 2)) * ((1 - ((w : ℝ) ^ 4) ^ ((P : ℝ) / 4 + 1)) / ((P : ℝ) / 4 + 1)) =
      ((dnIq v w P a : ℚ) : ℝ) := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  rw [dn_rpow_four hv', dn_rpow_four hw']
  have hm : Real.exp (-(a * Real.log 2)) = (1 / 2 : ℝ) ^ a := by
    rw [Real.exp_neg, ← Real.log_rpow (by norm_num), Real.exp_log (by positivity), Real.rpow_natCast]
    simp
  rw [hm]
  have hq : (P : ℝ) / 4 + 1 = (((P : ℚ) + 4) / 4 : ℚ) := by push_cast; ring
  rw [hq]
  unfold dnIq
  push_cast
  ring

end

end Census
end IIT
