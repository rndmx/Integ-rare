/-
Census, B1 lemma LT2, module M2: the special (heavy) rows (`iit-census/lean/LT2-PLAN.md`, W2 §2 G0).

`Sp(w) = {r : X(r) ≤ x₁ N}`, `x₁ = x0 + 1/400` (so the other rows have `P(r) < θ = σ_N e^{-N/400}`).
`P(|Sp| ≥ k) ≤ (2^N e^{-N I(x₁)})^k` (union over `k`-sets of rows, rows independent, Cramér for each row), and with
`k = 12`, `12 (I(x₁) - log 2) ≥ 1.05`.  On `β < σ_N`, `Z ≤ 13` every weight is `< 13 σ_N`.
-/
import IIT.Census.B1Chernoff
import IIT.Census.CertRatesCore

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- The special-row threshold `x₁ = x0 + 1/400`. -/
noncomputable def lt2x1 : ℝ := x0 + 1 / 400

/-- The special rows. -/
noncomputable def lt2Sp (w : Param N) : Finset (State N) := univ.filter fun r => XW w r ≤ lt2x1 * N

/-- Rows in a fixed set all special: product of the row probabilities. -/
lemma lt2_all_rows_le (K : Finset (State N)) (x : ℝ) :
    cubeM N {w | ∀ r ∈ K, XW w r ≤ x} = rowM N {v | ∑ i, -Real.log (clamp01 (v i)) ≤ x} ^ K.card := by
  set S : Set (Fin N → ℝ) := {v | ∑ i, -Real.log (clamp01 (v i)) ≤ x}
  have hset : {w : Param N | ∀ r ∈ K, XW w r ≤ x} = Set.pi Set.univ fun r => if r ∈ K then S else Set.univ := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h r; split_ifs with hr
      · exact h r hr
      · trivial
    · intro h r hr; have := h r; rw [if_pos hr] at this; exact this
  rw [hset]
  unfold cubeM
  rw [Measure.pi_pi]
  rw [show (fun r => rowM N (if r ∈ K then S else Set.univ)) = fun r => if r ∈ K then rowM N S else 1 by
    funext r; split_ifs <;> simp]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, Finset.filter_mem_eq_inter,
    Finset.univ_inter]

/-- **`P(|Sp| ≥ k) ≤ (2^N e^{-N I(x₁)})^k`** for `0 < x₁ ≤ 1`. -/
theorem lt2_Sp_card_le (k : ℕ) (hN : 0 < N) {x1 : ℝ} (hx0 : 0 < x1) (hx1 : x1 ≤ 1) :
    cubeM N {w | k ≤ (univ.filter fun r => XW w r ≤ x1 * N).card} ≤
      ENNReal.ofReal ((2 ^ N * Real.exp (-(N * (x1 - 1 - Real.log x1)))) ^ k) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsub : {w : Param N | k ≤ (univ.filter fun r => XW w r ≤ x1 * N).card} ⊆
      ⋃ K ∈ (univ : Finset (State N)).powersetCard k, {w | ∀ r ∈ K, XW w r ≤ x1 * N} := by
    intro w hw
    simp only [Set.mem_setOf_eq] at hw
    obtain ⟨K, hK, hKc⟩ := Finset.exists_subset_card_eq hw
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, mem_powersetCard]
    exact ⟨K, ⟨subset_univ _, hKc⟩, fun r hr => (mem_filter.1 (hK hr)).2⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hrow : rowM N {v | ∑ i, -Real.log (clamp01 (v i)) ≤ x1 * N} ≤
      ENNReal.ofReal (Real.exp (-(N * (x1 - 1 - Real.log x1)))) := by
    have h := rowM_negLog_sum_le (N := N) univ (x := x1 * N) (by positivity) (by
      simp only [card_univ, Fintype.card_fin]; nlinarith)
    simp only [card_univ, Fintype.card_fin] at h
    rw [show x1 * N / N = x1 by field_simp] at h
    exact h
  calc ∑ K ∈ (univ : Finset (State N)).powersetCard k, cubeM N {w | ∀ r ∈ K, XW w r ≤ x1 * N}
      ≤ ∑ _K ∈ (univ : Finset (State N)).powersetCard k,
          ENNReal.ofReal (Real.exp (-(N * (x1 - 1 - Real.log x1)))) ^ k := by
        refine Finset.sum_le_sum fun K hK => ?_
        rw [lt2_all_rows_le, (mem_powersetCard.1 hK).2]
        exact pow_le_pow_left₀ zero_le hrow k
    _ = ((univ : Finset (State N)).powersetCard k).card *
          ENNReal.ofReal (Real.exp (-(N * (x1 - 1 - Real.log x1)))) ^ k := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 : ENNReal) ^ N) ^ k * ENNReal.ofReal (Real.exp (-(N * (x1 - 1 - Real.log x1)))) ^ k := by
        gcongr
        rw [Finset.card_powersetCard, Finset.card_univ]
        have h1 : (Fintype.card (State N)).choose k ≤ (Fintype.card (State N)) ^ k := Nat.choose_le_pow _ _
        have h2 : Fintype.card (State N) = 2 ^ N := by simp
        rw [h2] at h1 ⊢
        exact_mod_cast h1
    _ = _ := by
        rw [← mul_pow, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [ENNReal.ofReal_pow (by norm_num)]; simp

lemma lt2x1_bounds : (2027 / 10000 : ℝ) + 1 / 400 ≤ lt2x1 ∧ lt2x1 ≤ 2053 / 10000 := by
  have h := cr_x0_bounds
  unfold lt2x1
  have h1 : ((crX0lo : ℚ) : ℝ) ≥ 2027 / 10000 := by unfold crX0lo; push_cast; norm_num
  have h2 : ((crX0hi : ℚ) : ℝ) ≤ 2028 / 10000 := by unfold crX0hi; push_cast; norm_num
  constructor <;> linarith [h.1, h.2]

/-- `12 (I(x₁) - log 2) ≥ 1.05`. -/
lemma lt2_rate : (105 / 100 : ℝ) ≤ 12 * (lt2x1 - 1 - Real.log lt2x1 - Real.log 2) := by
  obtain ⟨h1, h2⟩ := lt2x1_bounds
  have hlog : Real.log lt2x1 ≤ -1583 / 1000 := by
    have hq : Real.log (((2053 / 10000 : ℚ)) : ℝ) ≤ (((-1583 / 1000 : ℚ)) : ℝ) :=
      crLog_le (-2) 40 (by decide +kernel)
    push_cast at hq
    exact (Real.log_le_log (by linarith) h2).trans hq
  have hl2 := Real.log_two_lt_d9
  linarith

/-- **The special rows are fewer than 12** off probability `e^{-1.05 N}`. -/
theorem lt2_Sp_ev : ∀ᶠ N : ℕ in atTop, cubeM N {w | 12 ≤ (lt2Sp (N := N) w).card} ≤
    ENNReal.ofReal (Real.exp (-((105 / 100 : ℝ) * N))) := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  obtain ⟨h1, h2⟩ := lt2x1_bounds
  refine (lt2_Sp_card_le 12 hN (by linarith) (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
  have hr := lt2_rate
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have e : (2 ^ N * Real.exp (-(N * (lt2x1 - 1 - Real.log lt2x1)))) ^ 12 =
      Real.exp (-(N * (12 * (lt2x1 - 1 - Real.log lt2x1 - Real.log 2)))) := by
    rw [show (2 : ℝ) ^ N = Real.exp (N * Real.log 2) by
      rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_nat_mul, Real.exp_log (by norm_num)],
      ← Real.exp_add, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  rw [e]
  apply Real.exp_le_exp.2
  nlinarith

/-- On `β < σ_N` and `Z ≤ 13`, every weight is `< 13 σ_N`. -/
lemma lt2_Pw_lt {w : Param N} (hβ : betaW w < sigN N) (hZ0 : 0 < Zs w) (hZ : Zs w ≤ 13) (r : State N) :
    Pw w r < 13 * sigN N := by
  have h := Pw_le_tcRow w r
  have hb : Pw w (tcRow w) < sigN N * Zs w := by
    unfold betaW at hβ; rwa [div_lt_iff₀ hZ0] at hβ
  have hσ : 0 < sigN N := by unfold sigN; positivity
  nlinarith

end Census
end IIT

#print axioms IIT.Census.lt2_Sp_ev
