/-
Census, B1 lemma LT2, module M4 part 5b: the three pieces of the variance floor.

* `lt2_A_tail`: lower tail of `A = Σ_{r ∈ agree {j} t} f(w r)` (row-local Bernstein, variance `(2/5)^N`).
* `lt2_B_tail`: for `1 ≤ |D|`, upper tail of `Σ_r g(w r)² 1{¬Light(w (r ⊕ D))}` (pair Bernstein).
* `lt2_C_le`: `Σ_{ham(r,s) ≤ 6} g² ≤ (N+1)^6 θ²` (deterministic).
-/
import IIT.Census.B1LT2Floor

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

lemma lt2fH_sq_le (x : Fin N → ℝ) : lt2fH x ^ 2 ≤ lt2gNs x ^ 4 := by
  unfold lt2fH; split_ifs
  · ring_nf; exact le_rfl
  · simp; positivity

lemma lt2_int_fH_bounds : 0 ≤ ∫ x, lt2fH x ∂rowM N ∧ ∫ x, lt2fH x ∂rowM N ≤ lt2θ N ^ 2 := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  refine ⟨integral_nonneg lt2fH_nonneg, ?_⟩
  calc ∫ x, lt2fH x ∂rowM N ≤ ∫ _x, lt2θ N ^ 2 ∂rowM N :=
        integral_mono_of_nonneg (ae_of_all _ lt2fH_nonneg) (integrable_const _) (ae_of_all _ lt2fH_le)
    _ = lt2θ N ^ 2 := by simp

/-- **Lower tail of the heavy-window mass on a half-cube.** -/
theorem lt2_A_tail (j : Fin N) (t : State N) {ε : ℝ} (hε : 0 ≤ ε) :
    (cubeM N).real {w | ε ≤ (agree {j} t).card * ∫ x, lt2fH x ∂rowM N - ∑ r ∈ agree {j} t, lt2fH (w r)} ≤
      Real.exp (-min (ε ^ 2 / (4 * (2 / 5 : ℝ) ^ N)) (ε / (2 * (2 * lt2θ N ^ 2)))) := by
  classical
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  set m := ∫ x, lt2fH x ∂rowM N
  obtain ⟨hm0, hm1⟩ := lt2_int_fH_bounds (N := N)
  set G : State N → (Fin N → ℝ) → ℝ := fun v x => if v ∈ agree {j} t then m - lt2fH x else 0
  have hfi : Integrable (lt2fH (N := N)) (rowM N) :=
    Integrable.of_bound lt2fH_measurable.aestronglyMeasurable (lt2θ N ^ 2) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (lt2fH_nonneg x)]; exact lt2fH_le x)
  have hG : ∀ v, Measurable (G v) := fun v => by
    simp only [G]; split_ifs
    · exact measurable_const.sub lt2fH_measurable
    · exact measurable_const
  have hM : ∀ v x, |G v x| ≤ lt2θ N ^ 2 := by
    intro v x; simp only [G]; split_ifs
    · rw [abs_le]; constructor <;> linarith [lt2fH_nonneg x, lt2fH_le x]
    · simp; positivity
  have h0 : ∑ v, ∫ x, G v x ∂rowM N = 0 := by
    refine Finset.sum_eq_zero fun v _ => ?_
    simp only [G]; split_ifs
    · rw [integral_sub (integrable_const _) hfi, integral_const]; simp [m]
    · simp
  have hV : ∑ v, ∫ x, G v x ^ 2 ∂rowM N ≤ (2 / 5 : ℝ) ^ N := by
    have hone : ∀ v, ∫ x, G v x ^ 2 ∂rowM N ≤ (1 / 5 : ℝ) ^ N := by
      intro v
      have h4 := lt2gNs_pow_int (N := N) 4
      have hg4 : Integrable (fun x : Fin N → ℝ => lt2gNs x ^ 4) (rowM N) :=
        Integrable.of_bound (lt2gNs_measurable.pow_const 4).aestronglyMeasurable 1 (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (lt2gNs_nonneg x) 4)]
          exact pow_le_one₀ (lt2gNs_nonneg x) ((lt2gNs_le x).trans lt2θ_le_one))
      simp only [G]; split_ifs
      · calc ∫ x, (m - lt2fH x) ^ 2 ∂rowM N = ∫ x, lt2fH x ^ 2 ∂rowM N - m ^ 2 := by
              have hfi2 : Integrable (fun x => lt2fH (N := N) x ^ 2) (rowM N) :=
                Integrable.of_bound (lt2fH_measurable.pow_const 2).aestronglyMeasurable 1 (ae_of_all _ fun x => by
                  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
                  exact pow_le_one₀ (lt2fH_nonneg x) ((lt2fH_le x).trans
                    (pow_le_one₀ (Real.exp_pos _).le lt2θ_le_one)))
              have e : (fun x : Fin N → ℝ => (m - lt2fH x) ^ 2) = fun x => lt2fH x ^ 2 - 2 * m * lt2fH x + m ^ 2 := by
                funext x; ring
              rw [e, integral_add (f := fun x => lt2fH x ^ 2 - 2 * m * lt2fH x) (g := fun _ => m ^ 2)
                (hfi2.sub (hfi.const_mul _)) (integrable_const _),
                integral_sub (f := fun x => lt2fH x ^ 2) (g := fun x => 2 * m * lt2fH x) hfi2 (hfi.const_mul _),
                integral_const_mul, integral_const]
              simp [m]; ring
          _ ≤ ∫ x, lt2gNs x ^ 4 ∂rowM N := by
              have : ∫ x, lt2fH x ^ 2 ∂rowM N ≤ ∫ x, lt2gNs x ^ 4 ∂rowM N :=
                integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) hg4 (ae_of_all _ lt2fH_sq_le)
              nlinarith [sq_nonneg m]
          _ ≤ (1 / 5 : ℝ) ^ N := by (norm_num at h4 ⊢) <;> exact h4
      · simp
    calc ∑ v, ∫ x, G v x ^ 2 ∂rowM N ≤ ∑ _v : State N, (1 / 5 : ℝ) ^ N := Finset.sum_le_sum fun v _ => hone v
      _ = (2 / 5 : ℝ) ^ N := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; simp [div_pow]; ring
  have h := lt2_rowloc_tail G hG hM h0 hε hV
  refine le_trans (le_of_eq ?_) h
  congr 1; ext w
  simp only [Set.mem_setOf_eq, G]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]

/-- The non-light indicator of a row (`X_{C₀} ≤ 7N/10`). -/
noncomputable def lt2hL (x : Fin N → ℝ) : ℝ :=
  if ∑ j ∈ lt2C0 N, -Real.log (clamp01 (x j)) ≤ 7 / 10 * (N : ℝ) then 1 else 0

lemma lt2hL_measurable : Measurable (lt2hL (N := N)) :=
  Measurable.ite (measurableSet_le (Finset.measurable_sum _ fun j _ =>
    (Real.measurable_log.comp (measurable_clamp01.comp (measurable_pi_apply j))).neg) measurable_const)
    measurable_const measurable_const

lemma lt2hL_sq (x : Fin N → ℝ) : lt2hL x ^ 2 = lt2hL x := by unfold lt2hL; split_ifs <;> norm_num

lemma lt2hL_nonneg (x : Fin N → ℝ) : 0 ≤ lt2hL x := by unfold lt2hL; split_ifs <;> norm_num
lemma lt2hL_le_one (x : Fin N → ℝ) : lt2hL x ≤ 1 := by unfold lt2hL; split_ifs <;> norm_num

lemma lt2hL_of_not_light {w : Param N} {q : State N} (h : ¬ lt2Light w q) : lt2hL (w q) = 1 := by
  unfold lt2Light XMW at h; unfold lt2hL; rw [if_pos (not_lt.1 h)]

/-- **Upper tail of the non-isolated mass along one shift `D`.** -/
theorem lt2_B_tail {D : Finset (Fin N)} {d : Fin N} (hd : d ∈ D) {ε : ℝ} (hε : 0 ≤ ε) :
    (cubeM N).real {w | ε + 2 * (2 ^ N * ((1 / 3 : ℝ) ^ N * ∫ x, lt2hL x ∂rowM N)) ≤
        ∑ r : State N, lt2gNs (w r) ^ 2 * lt2hL (w (lt2Xor r D))} ≤
      Real.exp (-min (ε ^ 2 / (4 * (4 * (2 / 5 : ℝ) ^ N))) (ε / (2 * (2 * (2 * lt2θ N ^ 2))))) := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  set ρ := (rowM N).prod (rowM N)
  set q := ∫ x, lt2hL x ∂rowM N
  set f : (Fin N → ℝ) → ℝ := fun x => lt2gNs x ^ 2
  have hfm : Measurable f := lt2gNs_measurable.pow_const 2
  have hf0 : ∀ x, 0 ≤ f x := fun x => sq_nonneg _
  have hf1 : ∀ x, f x ≤ lt2θ N ^ 2 := fun x => pow_le_pow_left₀ (lt2gNs_nonneg x) (lt2gNs_le x) 2
  have hθ1 : lt2θ N ^ 2 ≤ 1 := pow_le_one₀ (Real.exp_pos _).le lt2θ_le_one
  have hfi : Integrable f (rowM N) := Integrable.of_bound hfm.aestronglyMeasurable 1 (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]; exact (hf1 x).trans hθ1)
  have hfi2 : Integrable (fun x => f x ^ 2) (rowM N) :=
    Integrable.of_bound (hfm.pow_const 2).aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact pow_le_one₀ (hf0 x) ((hf1 x).trans hθ1))
  have hhi : Integrable (lt2hL (N := N)) (rowM N) := Integrable.of_bound lt2hL_measurable.aestronglyMeasurable 1
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (lt2hL_nonneg x)]; exact lt2hL_le_one x)
  have hq0 : 0 ≤ q := integral_nonneg lt2hL_nonneg
  have hEf : ∫ x, f x ∂rowM N ≤ (1 / 3 : ℝ) ^ N := by
    have := lt2gNs_pow_int (N := N) 2; norm_num at this ⊢; exact this
  have hEf0 : 0 ≤ ∫ x, f x ∂rowM N := integral_nonneg hf0
  have hEf2 : ∫ x, f x ^ 2 ∂rowM N ≤ (1 / 5 : ℝ) ^ N := by
    have := lt2gNs_pow_int (N := N) 4
    have e : (fun x => f x ^ 2) = fun x => lt2gNs x ^ 4 := by funext x; simp only [f]; ring
    rw [e]; norm_num at this ⊢; exact this
  set φ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ := fun z => f z.1 * lt2hL z.2 + f z.2 * lt2hL z.1
  have hφm : Measurable φ :=
    ((hfm.comp measurable_fst).mul (lt2hL_measurable.comp measurable_snd)).add
      ((hfm.comp measurable_snd).mul (lt2hL_measurable.comp measurable_fst))
  have hφM : ∀ z, |φ z| ≤ 2 * lt2θ N ^ 2 := by
    intro z; simp only [φ]
    rw [abs_of_nonneg (add_nonneg (mul_nonneg (hf0 _) (lt2hL_nonneg _)) (mul_nonneg (hf0 _) (lt2hL_nonneg _)))]
    have h1 := mul_le_mul (hf1 z.1) (lt2hL_le_one z.2) (lt2hL_nonneg _) (sq_nonneg _)
    have h2 := mul_le_mul (hf1 z.2) (lt2hL_le_one z.1) (lt2hL_nonneg _) (sq_nonneg _)
    linarith
  have hEφ : ∫ z, φ z ∂ρ = 2 * ((∫ x, f x ∂rowM N) * q) := by
    simp only [φ, ρ]
    rw [integral_add (hfi.mul_prod hhi) (hhi.mul_prod hfi |>.congr (ae_of_all _ fun z => by ring)) ]
    · rw [integral_prod_mul (f := f) (g := lt2hL)]
      rw [show (∫ z : (Fin N → ℝ) × (Fin N → ℝ), f z.2 * lt2hL z.1 ∂(rowM N).prod (rowM N)) =
        ∫ z : (Fin N → ℝ) × (Fin N → ℝ), lt2hL z.1 * f z.2 ∂(rowM N).prod (rowM N) by
          congr 1; funext z; ring, integral_prod_mul (f := lt2hL) (g := f)]
      ring
  have hEφ2 : ∫ z, φ z ^ 2 ∂ρ ≤ 4 * ((1 / 5 : ℝ) ^ N * q) := by
    have hpt : ∀ z : (Fin N → ℝ) × (Fin N → ℝ), φ z ^ 2 ≤ 2 * (f z.1 ^ 2 * lt2hL z.2) + 2 * (lt2hL z.1 * f z.2 ^ 2) := by
      intro z; simp only [φ]
      have e1 := lt2hL_sq z.1; have e2 := lt2hL_sq z.2
      nlinarith [sq_nonneg (f z.1 * lt2hL z.2 - f z.2 * lt2hL z.1)]
    have hI1 : Integrable (fun z : (Fin N → ℝ) × (Fin N → ℝ) => f z.1 ^ 2 * lt2hL z.2) ρ := hfi2.mul_prod hhi
    have hI2 : Integrable (fun z : (Fin N → ℝ) × (Fin N → ℝ) => lt2hL z.1 * f z.2 ^ 2) ρ := hhi.mul_prod hfi2
    calc ∫ z, φ z ^ 2 ∂ρ ≤ ∫ z, (2 * (f z.1 ^ 2 * lt2hL z.2) + 2 * (lt2hL z.1 * f z.2 ^ 2)) ∂ρ :=
          integral_mono_of_nonneg (ae_of_all _ fun z => sq_nonneg _) ((hI1.const_mul 2).add (hI2.const_mul 2))
            (ae_of_all _ hpt)
      _ = 2 * ((∫ x, f x ^ 2 ∂rowM N) * q) + 2 * (q * ∫ x, f x ^ 2 ∂rowM N) := by
          rw [integral_add (hI1.const_mul 2) (hI2.const_mul 2), integral_const_mul, integral_const_mul,
            integral_prod_mul (f := fun x => f x ^ 2) (g := lt2hL), integral_prod_mul (f := lt2hL) (g := fun x => f x ^ 2)]
      _ ≤ 4 * ((1 / 5 : ℝ) ^ N * q) := by nlinarith
  have hcard : (Fintype.card (lt2P0 d) : ℝ) ≤ 2 ^ N := by
    have : Fintype.card (lt2P0 d) ≤ Fintype.card (State N) := Fintype.card_subtype_le _
    have h2 : Fintype.card (State N) = 2 ^ N := by simp
    rw [h2] at this; exact_mod_cast this
  have hq1 : q ≤ 1 := by
    calc q ≤ ∫ _x, (1 : ℝ) ∂rowM N := integral_mono hhi (integrable_const _) lt2hL_le_one
      _ = 1 := by simp
  have hV : (Fintype.card (lt2P0 d) : ℝ) * ∫ z, φ z ^ 2 ∂ρ ≤ 4 * (2 / 5 : ℝ) ^ N := by
    have h0 : 0 ≤ ∫ z, φ z ^ 2 ∂ρ := integral_nonneg fun z => sq_nonneg _
    calc (Fintype.card (lt2P0 d) : ℝ) * ∫ z, φ z ^ 2 ∂ρ ≤ 2 ^ N * (4 * ((1 / 5 : ℝ) ^ N * q)) :=
          mul_le_mul hcard hEφ2 h0 (by positivity)
      _ = 4 * (2 / 5 : ℝ) ^ N * q := by rw [div_pow, div_pow]; field_simp; ring
      _ ≤ 4 * (2 / 5 : ℝ) ^ N := mul_le_of_le_one_right (by positivity) hq1
  have h := lt2_pair_tail D hd φ hφm hφM hε hV
  refine le_trans (measureReal_mono (fun w hw => ?_)) h
  simp only [Set.mem_setOf_eq] at hw ⊢
  have hreg := lt2_pair_regroup D hd (fun r r' => lt2gNs (w r) ^ 2 * lt2hL (w r'))
  try simp only at hreg
  rw [hreg] at hw
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hEφ]
  have hmean : (Fintype.card (lt2P0 d) : ℝ) * (2 * ((∫ x, f x ∂rowM N) * q)) ≤ 2 * (2 ^ N * ((1 / 3 : ℝ) ^ N * q)) := by
    have := mul_le_mul_of_nonneg_right hEf hq0
    have hc0 : (0 : ℝ) ≤ Fintype.card (lt2P0 d) := Nat.cast_nonneg _
    nlinarith [mul_le_mul hcard (mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 2))
      (by positivity) (by positivity)]
  have hsum : ∑ i : lt2P0 d, φ (w i.1, w (lt2Xor i.1 D)) =
      ∑ i : lt2P0 d, (lt2gNs (w i.1) ^ 2 * lt2hL (w (lt2Xor i.1 D)) + lt2gNs (w (lt2Xor i.1 D)) ^ 2 * lt2hL (w i.1)) :=
    Finset.sum_congr rfl fun i _ => rfl
  rw [hsum]
  linarith

end Census
end IIT
