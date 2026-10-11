/-
Census, B1 lemma LT2, module M3 part 3b: tools for the variance event of the shifted-entry statistics.

* `lt2_rowsout_tail`: Bernstein over the rows outside a set `F` (law `rowsOutM F`).
* `lt2_Om0_indicator`: `1{v ∈ Ω₀} = (1 + χ_Λ(v))/2`, hence `lt2_sum_Om0_chi`: `Σ_{v ∈ Ω₀} χ_U(v) = 0` for
  `U ∉ {∅, Λ}`.
-/
import IIT.Census.B1LT2Stats3

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ} {b : Bool}

/-! ### Bernstein over the rows outside `F` -/

theorem lt2_rowsout_tail (F : Finset (State N)) (G : {r // r ∉ F} → (Fin N → ℝ) → ℝ)
    (hG : ∀ q, Measurable (G q)) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ q x, |G q x| ≤ M)
    (h0 : ∀ q, ∫ x, G q x ∂rowM N = 0) {V ε : ℝ} (hε : 0 ≤ ε)
    (hV : ∑ q, ∫ x, G q x ^ 2 ∂rowM N ≤ V) :
    (rowsOutM F).real {g | ε ≤ ∑ q, G q (g q)} ≤ Real.exp (-min (ε ^ 2 / (4 * V)) (ε / (2 * M))) := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  haveI : IsProbabilityMeasure (rowsOutM F) := by unfold rowsOutM; infer_instance
  have hind : iIndepFun (fun q (g : {r // r ∉ F} → Fin N → ℝ) => G q (g q)) (rowsOutM F) := by
    unfold rowsOutM
    exact iIndepFun_pi (X := G) fun q => (hG q).aemeasurable
  have hint : ∀ q (f : (Fin N → ℝ) → ℝ), Measurable f →
      ∫ g, f (g q) ∂rowsOutM F = ∫ x, f x ∂rowM N := by
    intro q f hf
    have hmp : MeasurePreserving (fun g : {r // r ∉ F} → Fin N → ℝ => g q) (rowsOutM F) (rowM N) :=
      measurePreserving_eval (fun _ : {r // r ∉ F} => rowM N) q
    rw [← hmp.map_eq]
    exact (integral_map (measurable_pi_apply q).aemeasurable hf.aestronglyMeasurable).symm
  refine bernstein_upper univ hind (fun q => ((hG q).comp (measurable_pi_apply q)).aemeasurable) hM0 hε
    (fun q _ => ae_of_all _ fun g => hM q (g q)) (fun q _ => ?_) ?_
  · rw [hint q (G q) (hG q)]; exact h0 q
  · refine le_trans (le_of_eq (Finset.sum_congr rfl fun q _ => ?_)) hV
    exact hint q (fun x => G q x ^ 2) ((hG q).pow_const 2)

/-- Two-sided version. -/
theorem lt2_rowsout_abs (F : Finset (State N)) (G : {r // r ∉ F} → (Fin N → ℝ) → ℝ)
    (hG : ∀ q, Measurable (G q)) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ q x, |G q x| ≤ M)
    (h0 : ∀ q, ∫ x, G q x ∂rowM N = 0) {V ε : ℝ} (hε : 0 ≤ ε)
    (hV : ∑ q, ∫ x, G q x ^ 2 ∂rowM N ≤ V) :
    (rowsOutM F).real {g | ε ≤ |∑ q, G q (g q)|} ≤ 2 * Real.exp (-min (ε ^ 2 / (4 * V)) (ε / (2 * M))) := by
  haveI : IsProbabilityMeasure (rowsOutM F) := by unfold rowsOutM; infer_instance
  have hsub : {g : {r // r ∉ F} → Fin N → ℝ | ε ≤ |∑ q, G q (g q)|} ⊆
      {g | ε ≤ ∑ q, G q (g q)} ∪ {g | ε ≤ ∑ q, (fun q x => -G q x) q (g q)} := by
    intro g hg
    simp only [Set.mem_setOf_eq, Set.mem_union] at hg ⊢
    rcases le_abs'.1 hg with h | h
    · right; rw [Finset.sum_neg_distrib]; linarith
    · left; exact h
  have h1 := lt2_rowsout_tail F G hG hM0 hM h0 hε hV
  have h2 := lt2_rowsout_tail F (fun q x => -G q x) (fun q => (hG q).neg) hM0
    (fun q x => by rw [abs_neg]; exact hM q x) (fun q => by rw [integral_neg, h0 q, neg_zero]) hε
    (by simpa only [neg_sq] using hV)
  calc (rowsOutM F).real {g | ε ≤ |∑ q, G q (g q)|}
      ≤ (rowsOutM F).real ({g | ε ≤ ∑ q, G q (g q)} ∪ {g | ε ≤ ∑ q, (fun q x => -G q x) q (g q)}) :=
        measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by linarith

/-! ### Sums of characters over a parity class -/

lemma lt2_Om0_indicator (Λ : Finset (Fin N)) (v : State N) :
    (if v ∈ lt2Om0 Λ b then (1 : ℝ) else 0) = (1 + (if b then -1 else 1) * lt2Chi Λ v) / 2 := by
  have hchi : lt2Chi Λ v = if lt2Par Λ v then -1 else 1 := by
    unfold lt2Chi lt2Par
    rw [← Finset.prod_filter_mul_prod_filter_not Λ (fun j => v j = true)]
    have hA : ∏ j ∈ Λ.filter (fun j => v j = true), (if v j then (-1 : ℝ) else 1) =
        (-1) ^ (Λ.filter fun j => v j = true).card := by
      rw [Finset.prod_congr rfl (fun j hj => if_pos (mem_filter.1 hj).2), Finset.prod_const]
    have hB : ∏ j ∈ Λ.filter (fun j => ¬ v j = true), (if v j then (-1 : ℝ) else 1) = 1 :=
      Finset.prod_eq_one fun j hj => if_neg (mem_filter.1 hj).2
    rw [hA, hB, mul_one, neg_one_pow_eq_pow_mod_two]
    rcases Nat.mod_two_eq_zero_or_one (Λ.filter fun j => v j = true).card with h | h <;> simp [h]
  simp only [lt2Om0, mem_filter, mem_univ, true_and, hchi]
  cases lt2Par Λ v <;> cases b <;> norm_num

/-- **`Σ_{v ∈ Ω₀} χ_U(v) = 0`** for `U ≠ ∅` and `U ≠ Λ`. -/
lemma lt2_sum_Om0_chi (Λ U : Finset (Fin N)) (hU : U.Nonempty) (hUΛ : U ≠ Λ) :
    ∑ v ∈ lt2Om0 Λ b, lt2Chi U v = 0 := by
  have h1 : ∑ v ∈ lt2Om0 Λ b, lt2Chi U v = ∑ v, (if v ∈ lt2Om0 Λ b then (1 : ℝ) else 0) * lt2Chi U v := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1]
  simp_rw [lt2_Om0_indicator, add_div, add_mul, Finset.sum_add_distrib]
  have h2 : ∑ v : State N, 1 / 2 * lt2Chi U v = 0 := by rw [← Finset.mul_sum, lt2_sum_chi hU, mul_zero]
  have h3 : ∑ v : State N, (if b then -1 else 1) * lt2Chi Λ v / 2 * lt2Chi U v = 0 := by
    have := lt2_sum_chi_mul Λ U
    rw [if_neg (Ne.symm hUΛ)] at this
    rw [show (∑ v : State N, (if b then -1 else 1) * lt2Chi Λ v / 2 * lt2Chi U v) =
        (if b then -1 else 1) * (∑ v : State N, lt2Chi Λ v * lt2Chi U v) / 2 by
      rw [Finset.mul_sum, Finset.sum_div]; exact Finset.sum_congr rfl fun v _ => by ring, this, mul_zero, zero_div]
  rw [h2, h3, add_zero]

/-! ### Shift algebra -/

lemma lt2Xor_comp (v : State N) (R R' : Finset (Fin N)) :
    lt2Xor (lt2Xor v R) R' = lt2Xor v (symmDiff R R') := by
  funext j; unfold lt2Xor
  simp only [Finset.mem_symmDiff]
  by_cases h1 : j ∈ R <;> by_cases h2 : j ∈ R' <;> simp [h1, h2]

lemma lt2Chi_xor (T D : Finset (Fin N)) (v : State N) :
    lt2Chi T (lt2Xor v D) = (-1) ^ (T ∩ D).card * lt2Chi T v := by
  unfold lt2Chi lt2Xor
  rw [← Finset.prod_filter_mul_prod_filter_not T (· ∈ D), ← Finset.prod_filter_mul_prod_filter_not T (· ∈ D)]
  have h1 : ∏ j ∈ T.filter (· ∈ D), (if (if j ∈ D then !v j else v j) then (-1 : ℝ) else 1) =
      (-1) ^ (T ∩ D).card * ∏ j ∈ T.filter (· ∈ D), (if v j then (-1 : ℝ) else 1) := by
    rw [Finset.filter_mem_eq_inter, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [if_pos (mem_inter.1 hj).2]; cases v j <;> simp
  have h2 : ∏ j ∈ T.filter (· ∉ D), (if (if j ∈ D then !v j else v j) then (-1 : ℝ) else 1) =
      ∏ j ∈ T.filter (· ∉ D), (if v j then (-1 : ℝ) else 1) :=
    Finset.prod_congr rfl fun j hj => by rw [if_neg (mem_filter.1 hj).2]
  rw [h1, h2]; ring

lemma lt2Chi_mul_xor (T T' D : Finset (Fin N)) (v : State N) :
    lt2Chi T v * lt2Chi T' (lt2Xor v D) = (-1) ^ (T' ∩ D).card * lt2Chi (symmDiff T T') v := by
  rw [lt2Chi_xor, ← lt2Chi_mul]; ring

/-! ### The Gram statistics -/

/-- `Gm(D, U) = Σ_{v ∈ Ω_b} P_ns(v) P_ns(v ⊕ D) χ_U(v)`. -/
noncomputable def lt2Gm (Λ : Finset (Fin N)) (b : Bool) (D U : Finset (Fin N)) (w : Param N) : ℝ :=
  ∑ v ∈ lt2Om0 Λ b, lt2gNs (w v) * lt2gNs (w (lt2Xor v D)) * lt2Chi U v

/-- **The conditional variance as Gram statistics.** -/
theorem lt2_coef_sq (Λ : Finset (Fin N)) (A A' : Finset (LT2Idx N)) (hA : ∀ α ∈ A, (α.2.1 ∩ Λ).card % 2 = 1)
    (w : Param N) (i : Fin N) :
    ∑ q ∈ (lt2Om0 Λ b)ᶜ, lt2Coef Λ b A A' w q i ^ 2 ≤
      ∑ α ∈ A.filter (fun α => α.1 = i), ∑ α' ∈ A.filter (fun α => α.1 = i),
        |lt2Gm Λ b (symmDiff α.2.1 α'.2.1) (symmDiff α.2.2 α'.2.2) w| := by
  set Ai := A.filter (fun α => α.1 = i)
  set sg : LT2Idx N → ℝ := fun α => if α ∈ A' then 1 else -1
  have hsg : ∀ α, |sg α| = 1 := fun α => by simp only [sg]; split_ifs <;> norm_num
  -- on the complement of Ω_b every shift lands in Ω_b
  have hin : ∀ α ∈ Ai, ∀ q ∈ (lt2Om0 Λ b)ᶜ, lt2Xor q α.2.1 ∈ lt2Om0 Λ b := by
    intro α hα q hq
    have hodd := hA α (mem_filter.1 hα).1
    have hq' := mem_compl.1 hq
    simp only [lt2Om0, mem_filter, mem_univ, true_and] at hq' ⊢
    rw [lt2Par_xor Λ α.2.1 q hodd]
    cases h : lt2Par Λ q <;> cases b <;> simp_all
  have hc : ∀ q ∈ (lt2Om0 Λ b)ᶜ, lt2Coef Λ b A A' w q i =
      ∑ α ∈ Ai, sg α * (lt2gNs (w (lt2Xor q α.2.1)) * lt2Chi α.2.2 (lt2Xor q α.2.1)) := by
    intro q hq
    unfold lt2Coef
    exact Finset.sum_congr rfl fun α hα => by rw [if_pos (hin α hα q hq)]
  have hsq : ∑ q ∈ (lt2Om0 Λ b)ᶜ, lt2Coef Λ b A A' w q i ^ 2 =
      ∑ α ∈ Ai, ∑ α' ∈ Ai, sg α * sg α' * ∑ q ∈ (lt2Om0 Λ b)ᶜ,
        (lt2gNs (w (lt2Xor q α.2.1)) * lt2Chi α.2.2 (lt2Xor q α.2.1)) *
          (lt2gNs (w (lt2Xor q α'.2.1)) * lt2Chi α'.2.2 (lt2Xor q α'.2.1)) := by
    rw [Finset.sum_congr rfl fun q hq => by rw [hc q hq]]
    simp_rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun α' _ => Finset.sum_congr rfl fun q _ => by ring
  -- reindex `v = q ⊕ R`
  have hre : ∀ α ∈ Ai, ∀ α' : LT2Idx N, ∑ q ∈ (lt2Om0 Λ b)ᶜ,
      (lt2gNs (w (lt2Xor q α.2.1)) * lt2Chi α.2.2 (lt2Xor q α.2.1)) *
        (lt2gNs (w (lt2Xor q α'.2.1)) * lt2Chi α'.2.2 (lt2Xor q α'.2.1)) =
      (-1) ^ (α'.2.2 ∩ symmDiff α.2.1 α'.2.1).card *
        lt2Gm Λ b (symmDiff α.2.1 α'.2.1) (symmDiff α.2.2 α'.2.2) w := by
    intro α hα α'
    have hodd := hA α (mem_filter.1 hα).1
    unfold lt2Gm
    rw [Finset.mul_sum]
    refine Finset.sum_nbij' (fun q => lt2Xor q α.2.1) (fun v => lt2Xor v α.2.1) ?_ ?_ ?_ ?_ ?_
    · intro q hq; exact hin α hα q hq
    · intro v hv; exact mem_compl.2 (lt2_xor_not_mem_Om0 hodd hv)
    · intro q _; exact lt2Xor_xor q α.2.1
    · intro v _; exact lt2Xor_xor v α.2.1
    · intro q _
      have key : lt2Xor (lt2Xor q α.2.1) (symmDiff α.2.1 α'.2.1) = lt2Xor q α'.2.1 := by
        rw [lt2Xor_comp, symmDiff_symmDiff_cancel_left]
      have hm := lt2Chi_mul_xor α.2.2 α'.2.2 (symmDiff α.2.1 α'.2.1) (lt2Xor q α.2.1)
      rw [key] at hm
      rw [key]
      calc lt2gNs (w (lt2Xor q α.2.1)) * lt2Chi α.2.2 (lt2Xor q α.2.1) *
            (lt2gNs (w (lt2Xor q α'.2.1)) * lt2Chi α'.2.2 (lt2Xor q α'.2.1))
          = lt2gNs (w (lt2Xor q α.2.1)) * lt2gNs (w (lt2Xor q α'.2.1)) *
              (lt2Chi α.2.2 (lt2Xor q α.2.1) * lt2Chi α'.2.2 (lt2Xor q α'.2.1)) := by ring
        _ = _ := by rw [hm]; ring
  rw [hsq]
  refine Finset.sum_le_sum fun α hα => Finset.sum_le_sum fun α' _ => ?_
  rw [hre α hα α']
  calc sg α * sg α' * ((-1) ^ (α'.2.2 ∩ symmDiff α.2.1 α'.2.1).card *
        lt2Gm Λ b (symmDiff α.2.1 α'.2.1) (symmDiff α.2.2 α'.2.2) w)
      ≤ |sg α * sg α' * ((-1) ^ (α'.2.2 ∩ symmDiff α.2.1 α'.2.1).card *
        lt2Gm Λ b (symmDiff α.2.1 α'.2.1) (symmDiff α.2.2 α'.2.2) w)| := le_abs_self _
    _ = _ := by rw [abs_mul, abs_mul, abs_mul, hsg, hsg, abs_pow, abs_neg, abs_one, one_pow]; ring

end Census
end IIT
