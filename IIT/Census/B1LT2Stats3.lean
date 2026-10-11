/-
Census, B1 lemma LT2, module M3 part 3: the shifted-entry statistics Ñ, conditional tail
(`iit-census/lean/LT2-PLAN.md`, route replacing W2 Lemma P2).

`Ñ⁰_{i,R}(T) = Σ_{v ∈ Ω₀} P_ns(v) (y_{v⊕R,i} - 1/2) χ_T(v)` with the parity class `Ω₀ = {v : Σ_{j∈Λ} v_j even}`
and `|R ∩ Λ|` odd, so `v ⊕ R ∉ Ω₀`.  Given the rows of `Ω₀`, a signed sum is `Σ_{q ∉ Ω₀} Y_q(row q)` with
`Y_q(x) = Σ_i c_{q,i} (y_i - 1/2)`: independent rows, centred, `E Y_q² = Σ_i c_{q,i}²/12`.
-/
import IIT.Census.B1LT2Stats2
import IIT.Census.B1Prod

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ} {b : Bool}

/-! ### Shifts and parity classes -/

/-- `v ⊕ R`: flip the coordinates in `R`. -/
def lt2Xor (v : State N) (R : Finset (Fin N)) : State N := fun j => if j ∈ R then !v j else v j

lemma lt2Xor_xor (v : State N) (R : Finset (Fin N)) : lt2Xor (lt2Xor v R) R = v := by
  funext j; unfold lt2Xor; split_ifs <;> simp

/-- Parity of `v` on `Λ`. -/
def lt2Par (Λ : Finset (Fin N)) (v : State N) : Bool := (Λ.filter fun j => v j = true).card % 2 == 1

/-- The class `Ω₀` (even parity on `Λ`). -/
def lt2Om0 (Λ : Finset (Fin N)) (b : Bool) : Finset (State N) := univ.filter fun v => lt2Par Λ v = b

lemma lt2Par_xor (Λ R : Finset (Fin N)) (v : State N) (h : (R ∩ Λ).card % 2 = 1) :
    lt2Par Λ (lt2Xor v R) = !lt2Par Λ v := by
  unfold lt2Par
  -- the filters differ exactly on `R ∩ Λ`
  set A := Λ.filter fun j => v j = true
  set A' := Λ.filter fun j => lt2Xor v R j = true
  have hsd : A' = symmDiff A (R ∩ Λ) := by
    ext j
    simp only [A, A', mem_filter, Finset.mem_symmDiff, mem_inter, lt2Xor]
    by_cases hj : j ∈ R <;> by_cases hΛ : j ∈ Λ <;> cases hvj : v j <;> simp [hj, hΛ, hvj]
  have hcard : (A'.card + (A ∩ (R ∩ Λ)).card * 2) % 2 = (A.card + (R ∩ Λ).card) % 2 := by
    rw [hsd]
    have e1 : symmDiff A (R ∩ Λ) = (A ∪ (R ∩ Λ)) \ (A ∩ (R ∩ Λ)) := symmDiff_eq_sup_sdiff_inf A (R ∩ Λ)
    rw [e1, Finset.card_sdiff, Finset.inter_eq_left.2 Finset.inter_subset_union]
    have := Finset.card_union_add_card_inter A (R ∩ Λ)
    have := Finset.card_le_card (Finset.inter_subset_union (s := A) (t := R ∩ Λ))
    omega
  have : A'.card % 2 = (A.card + 1) % 2 := by omega
  cases h1 : A.card % 2 == 1 <;> simp_all <;> omega

lemma lt2_xor_not_mem_Om0 {Λ R : Finset (Fin N)} (h : (R ∩ Λ).card % 2 = 1) {v : State N}
    (hv : v ∈ lt2Om0 Λ b) : lt2Xor v R ∉ lt2Om0 Λ b := by
  simp only [lt2Om0, mem_filter, mem_univ, true_and] at hv ⊢
  rw [lt2Par_xor Λ R v h, hv]; cases b <;> simp

/-! ### The conditional tail -/

/-- An index `(i, R, T)` of a shifted-entry statistic. -/
abbrev LT2Idx (N : ℕ) := Fin N × Finset (Fin N) × Finset (Fin N)

/-- `Ñ⁰`: the `Ω₀` half of a shifted-entry statistic. -/
noncomputable def lt2N0 (Λ : Finset (Fin N)) (b : Bool) (w : Param N) (α : LT2Idx N) : ℝ :=
  ∑ v ∈ lt2Om0 Λ b, lt2gNs (w v) * (clamp01 (w (lt2Xor v α.2.1) α.1) - 1 / 2) * lt2Chi α.2.2 v

/-- The coefficient of the entry `(q, i)` in a signed sum (a function of the `Ω₀` rows only). -/
noncomputable def lt2Coef (Λ : Finset (Fin N)) (b : Bool) (A A' : Finset (LT2Idx N)) (w : Param N) (q : State N) (i : Fin N) :
    ℝ :=
  ∑ α ∈ A.filter (fun α => α.1 = i), (if α ∈ A' then (1 : ℝ) else -1) *
    (if lt2Xor q α.2.1 ∈ lt2Om0 Λ b then lt2gNs (w (lt2Xor q α.2.1)) * lt2Chi α.2.2 (lt2Xor q α.2.1) else 0)

/-- **Regrouping by entries**: a signed sum of `Ñ⁰`'s is `Σ_{q ∉ Ω₀} Σ_i c_{q,i} (y_{q,i} - 1/2)`. -/
lemma lt2_N0_regroup (Λ : Finset (Fin N)) (A A' : Finset (LT2Idx N))
    (hA : ∀ α ∈ A, (α.2.1 ∩ Λ).card % 2 = 1) (w : Param N) :
    ∑ α ∈ A, (if α ∈ A' then lt2N0 Λ b w α else -lt2N0 Λ b w α) =
      ∑ q ∈ (lt2Om0 Λ b)ᶜ, ∑ i, lt2Coef Λ b A A' w q i * (clamp01 (w q i) - 1 / 2) := by
  -- both sides equal Σ_α s_α Σ_{v ∈ Ω₀} (...) ; reindex v ↦ q = v ⊕ R
  have hα : ∀ α ∈ A, (if α ∈ A' then lt2N0 Λ b w α else -lt2N0 Λ b w α) =
      ∑ q ∈ (lt2Om0 Λ b)ᶜ, (if α ∈ A' then (1 : ℝ) else -1) *
        ((if lt2Xor q α.2.1 ∈ lt2Om0 Λ b then lt2gNs (w (lt2Xor q α.2.1)) * lt2Chi α.2.2 (lt2Xor q α.2.1) else 0) *
          (clamp01 (w q α.1) - 1 / 2)) := by
    intro α hαA
    have hodd := hA α hαA
    unfold lt2N0
    have hre : ∑ v ∈ lt2Om0 Λ b, lt2gNs (w v) * (clamp01 (w (lt2Xor v α.2.1) α.1) - 1 / 2) * lt2Chi α.2.2 v =
        ∑ q ∈ (lt2Om0 Λ b)ᶜ, (if lt2Xor q α.2.1 ∈ lt2Om0 Λ b then
          lt2gNs (w (lt2Xor q α.2.1)) * lt2Chi α.2.2 (lt2Xor q α.2.1) else 0) * (clamp01 (w q α.1) - 1 / 2) := by
      refine Finset.sum_nbij' (fun v => lt2Xor v α.2.1) (fun q => lt2Xor q α.2.1) ?_ ?_ ?_ ?_ ?_
      · intro v hv; exact mem_compl.2 (lt2_xor_not_mem_Om0 hodd hv)
      · intro q hq
        have hq := mem_compl.1 hq
        by_contra hc
        have h1 : lt2Xor q α.2.1 ∈ (lt2Om0 Λ b)ᶜ := mem_compl.2 hc
        -- `q ∉ Ω₀` and `q ⊕ R ∉ Ω₀` contradict the parity flip
        simp only [lt2Om0, mem_compl, mem_filter, mem_univ, true_and] at hq h1
        rw [lt2Par_xor Λ α.2.1 q hodd] at h1
        cases h : lt2Par Λ q <;> cases b <;> simp_all
      · intro v _; exact lt2Xor_xor v α.2.1
      · intro q _; exact lt2Xor_xor q α.2.1
      · intro v hv
        rw [lt2Xor_xor, if_pos hv]; ring
    split_ifs
    · rw [hre]; exact Finset.sum_congr rfl fun q _ => by ring
    · rw [hre, ← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun q _ => by ring
  rw [Finset.sum_congr rfl hα, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold lt2Coef
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_fiberwise A (fun α => α.1)]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α hα => by
    rw [(mem_filter.1 hα).2]; ring

/-! ### Bernstein over independent rows of centred entries -/

lemma lt2_int_half (i : Fin N) : ∫ x, (clamp01 (x i) - 1 / 2) ∂rowM N = 0 := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  have hmp : MeasurePreserving (fun x : Fin N → ℝ => x i) (rowM N) unif :=
    measurePreserving_eval (fun _ : Fin N => unif) i
  rw [← integral_map (φ := fun x : Fin N → ℝ => x i) (f := fun u => clamp01 u - 1 / 2)
    (measurable_pi_apply i).aemeasurable ((clamp01_measurable.sub measurable_const).aestronglyMeasurable), hmp.map_eq,
    lt2_int_unif_poly (fun u => u - 1 / 2) (by fun_prop),
    intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _) intervalIntegrable_const,
    integral_id]
  norm_num

/-- `E[(Σ_i c_i (y_i - 1/2))²] = Σ_i c_i² / 12`. -/
lemma lt2_row_quad_half (c : Fin N → ℝ) :
    ∫ x, (∑ i, c i * (clamp01 (x i) - 1 / 2)) ^ 2 ∂rowM N = (∑ i, c i ^ 2) / 12 := by
  have hcross : ∀ i k, ∫ x, (clamp01 (x i) - 1 / 2) * (clamp01 (x k) - 1 / 2) ∂rowM N =
      if i = k then 1 / 12 else 0 := by
    intro i k
    set f : Fin N → ℝ → ℝ := fun j u => (if j = i then clamp01 u - 1 / 2 else 1) *
      (if j = k then clamp01 u - 1 / 2 else 1) with hf
    have e : ∀ x : Fin N → ℝ, (clamp01 (x i) - 1 / 2) * (clamp01 (x k) - 1 / 2) = ∏ j, f j (x j) := by
      intro x; simp only [hf, Finset.prod_mul_distrib, Finset.prod_ite_eq', mem_univ, if_true]
    simp_rw [e]
    unfold rowM
    rw [integral_fintype_prod_eq_prod (f := f)]
    haveI : IsProbabilityMeasure unif := sb_unif_prob
    have h1 : ∫ u, clamp01 u - 1 / 2 ∂unif = 0 := by
      rw [lt2_int_unif_poly (fun u => u - 1 / 2) (by fun_prop),
        intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _) intervalIntegrable_const,
        integral_id]; norm_num
    have h2 : ∫ u, (clamp01 u - 1 / 2) * (clamp01 u - 1 / 2) ∂unif = 1 / 12 := by
      rw [lt2_int_unif_poly (fun u => (u - 1 / 2) * (u - 1 / 2)) (by fun_prop)]
      have := sb_int_sq
      rw [← this]; congr 1; funext u; ring
    split_ifs with hik
    · subst hik
      rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
      rw [Finset.prod_eq_one fun j hj => by
        simp only [hf, if_neg (Finset.ne_of_mem_erase hj), mul_one]; simp]
      simp only [hf, if_true, mul_one]; exact h2
    · refine Finset.prod_eq_zero (mem_univ i) ?_
      simp only [hf, if_true, if_neg hik, mul_one]; exact h1
  have hint : ∀ i k, Integrable (fun x : Fin N → ℝ => (clamp01 (x i) - 1 / 2) * (clamp01 (x k) - 1 / 2)) (rowM N) := by
    intro i k
    haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
    refine Integrable.of_bound (((clamp01_measurable.comp (measurable_pi_apply i)).sub measurable_const).mul
      ((clamp01_measurable.comp (measurable_pi_apply k)).sub measurable_const)).aestronglyMeasurable 1
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |clamp01 (x i) - 1 / 2| ≤ 1 := abs_le.2 ⟨by linarith [clamp01_nonneg (x i)], by linarith [clamp01_le_one (x i)]⟩
    have h2 : |clamp01 (x k) - 1 / 2| ≤ 1 := abs_le.2 ⟨by linarith [clamp01_nonneg (x k)], by linarith [clamp01_le_one (x k)]⟩
    nlinarith [abs_nonneg (clamp01 (x i) - 1 / 2), abs_nonneg (clamp01 (x k) - 1 / 2)]
  have e : ∀ x : Fin N → ℝ, (∑ i, c i * (clamp01 (x i) - 1 / 2)) ^ 2 =
      ∑ i, ∑ k, c i * c k * ((clamp01 (x i) - 1 / 2) * (clamp01 (x k) - 1 / 2)) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e]
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun k _ => (hint i k).const_mul _]
  simp_rw [integral_finset_sum _ fun k _ => (hint _ k).const_mul _, integral_const_mul, hcross]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Bernstein over the rows outside `F`** for `Σ_q Σ_i c_{q,i} (y_{q,i} - 1/2)`. -/
theorem lt2_rows_half_tail (F : Finset (State N)) (c : {r // r ∉ F} → Fin N → ℝ) {M ε : ℝ} (hε : 0 ≤ ε)
    (hM0 : 0 ≤ M) (hM : ∀ q, (∑ i, |c q i|) / 2 ≤ M) {V : ℝ} (hV : (∑ q, ∑ i, c q i ^ 2) / 12 ≤ V) :
    (rowsOutM F).real {g | ε ≤ ∑ q, ∑ i, c q i * (clamp01 (g q i) - 1 / 2)} ≤
      Real.exp (-min (ε ^ 2 / (4 * V)) (ε / (2 * M))) := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  haveI : IsProbabilityMeasure (rowsOutM F) := by unfold rowsOutM; infer_instance
  set Y : {r // r ∉ F} → ({r // r ∉ F} → Fin N → ℝ) → ℝ := fun q g => ∑ i, c q i * (clamp01 (g q i) - 1 / 2)
  have hYm : ∀ q, Measurable fun x : Fin N → ℝ => ∑ i, c q i * (clamp01 (x i) - 1 / 2) := fun q =>
    Finset.measurable_sum _ fun i _ => measurable_const.mul ((clamp01_measurable.comp (measurable_pi_apply i)).sub
      measurable_const)
  have hind : iIndepFun Y (rowsOutM F) := by
    unfold rowsOutM
    exact iIndepFun_pi (X := fun q (x : Fin N → ℝ) => ∑ i, c q i * (clamp01 (x i) - 1 / 2))
      fun q => (hYm q).aemeasurable
  have hmp : ∀ q, MeasurePreserving (fun g : {r // r ∉ F} → Fin N → ℝ => g q) (rowsOutM F) (rowM N) :=
    fun q => measurePreserving_eval (fun _ : {r // r ∉ F} => rowM N) q
  have hint : ∀ q (f : (Fin N → ℝ) → ℝ), Measurable f →
      ∫ g, f (g q) ∂rowsOutM F = ∫ x, f x ∂rowM N := by
    intro q f hf
    rw [← (hmp q).map_eq]
    exact (integral_map (measurable_pi_apply q).aemeasurable hf.aestronglyMeasurable).symm
  refine bernstein_upper univ hind (fun q => ((hYm q).comp (measurable_pi_apply q)).aemeasurable) hM0
    hε (fun q _ => ae_of_all _ fun g => ?_) (fun q _ => ?_) ?_
  · refine ((Finset.abs_sum_le_sum_abs _ _).trans ?_).trans (hM q)
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul]
    have : |clamp01 (g q i) - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith [clamp01_nonneg (g q i)],
      by linarith [clamp01_le_one (g q i)]⟩
    nlinarith [abs_nonneg (c q i)]
  · show ∫ g, Y q g ∂rowsOutM F = 0
    simp only [Y]
    rw [hint q _ (hYm q), integral_finset_sum _ fun i _ => ?_]
    · simp_rw [integral_const_mul, lt2_int_half, mul_zero, Finset.sum_const_zero]
    · refine (Integrable.of_bound ((clamp01_measurable.comp (measurable_pi_apply i)).sub
        measurable_const).aestronglyMeasurable 1 (ae_of_all _ fun x => ?_)).const_mul _
      show ‖clamp01 (x i) - 1 / 2‖ ≤ 1
      rw [Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith [clamp01_nonneg (x i)], by linarith [clamp01_le_one (x i)]⟩
  · refine le_trans (le_of_eq ?_) hV
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Y]
    rw [hint q (fun x => (∑ i, c q i * (clamp01 (x i) - 1 / 2)) ^ 2) ((hYm q).pow_const 2), lt2_row_quad_half]

end Census
end IIT
