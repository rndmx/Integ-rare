/-
Census, B1 lemma LT2, module M3 part 3d: the Gram events with `D ≠ ∅` (second split).

For `d ∈ D` and `|D ∩ Λ|` even, `Gm(D,U) = Σ_{u ∈ Ω_b, u_d = 0} g(u) g(u⊕D) (χ_U(u) + χ_U(u⊕D))`
(`lt2_Gm_split`).  Conditionally on the rows `F = {v : v_d = 1}`, this is a linear sum over the independent rows
`u ∉ F` with coefficients `|c_u| ≤ 2θ` (`lt2_Gm_glue`).
-/
import IIT.Census.B1LT2Gram2

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ} {b : Bool}

lemma lt2Par_xor_even (Λ D : Finset (Fin N)) (v : State N) (h : (D ∩ Λ).card % 2 = 0) :
    lt2Par Λ (lt2Xor v D) = lt2Par Λ v := by
  unfold lt2Par
  set A := Λ.filter fun j => v j = true
  set A' := Λ.filter fun j => lt2Xor v D j = true
  have hsd : A' = symmDiff A (D ∩ Λ) := by
    ext j
    simp only [A, A', mem_filter, Finset.mem_symmDiff, mem_inter, lt2Xor]
    by_cases hj : j ∈ D <;> by_cases hΛ : j ∈ Λ <;> cases hvj : v j <;> simp [hj, hΛ, hvj]
  have hcard : A'.card % 2 = A.card % 2 := by
    rw [hsd]
    have e1 : symmDiff A (D ∩ Λ) = (A ∪ (D ∩ Λ)) \ (A ∩ (D ∩ Λ)) := symmDiff_eq_sup_sdiff_inf A (D ∩ Λ)
    rw [e1, Finset.card_sdiff, Finset.inter_eq_left.2 Finset.inter_subset_union]
    have := Finset.card_union_add_card_inter A (D ∩ Λ)
    have := Finset.card_le_card (Finset.inter_subset_union (s := A) (t := D ∩ Λ))
    have := Finset.card_le_card (Finset.inter_subset_right (s₁ := A) (s₂ := D ∩ Λ))
    omega
  rw [hcard]

lemma lt2Xor_apply_mem {v : State N} {D : Finset (Fin N)} {d : Fin N} (hd : d ∈ D) :
    lt2Xor v D d = !v d := by unfold lt2Xor; rw [if_pos hd]

/-- **The split along a coordinate of `D`.** -/
lemma lt2_Gm_split (Λ : Finset (Fin N)) {D : Finset (Fin N)} (U : Finset (Fin N)) {d : Fin N} (hd : d ∈ D)
    (hD : (D ∩ Λ).card % 2 = 0) (w : Param N) :
    lt2Gm Λ b D U w = ∑ u ∈ (lt2Om0 Λ b).filter (fun u => u d = false),
      lt2gNs (w u) * lt2gNs (w (lt2Xor u D)) * (lt2Chi U u + lt2Chi U (lt2Xor u D)) := by
  unfold lt2Gm
  rw [← Finset.sum_filter_add_sum_filter_not (lt2Om0 Λ b) (fun u => u d = false)]
  have hsecond : ∑ v ∈ (lt2Om0 Λ b).filter (fun u => ¬ u d = false),
      lt2gNs (w v) * lt2gNs (w (lt2Xor v D)) * lt2Chi U v =
      ∑ u ∈ (lt2Om0 Λ b).filter (fun u => u d = false),
        lt2gNs (w (lt2Xor u D)) * lt2gNs (w u) * lt2Chi U (lt2Xor u D) := by
    refine Finset.sum_nbij' (fun v => lt2Xor v D) (fun u => lt2Xor u D) ?_ ?_ ?_ ?_ ?_
    · intro v hv
      obtain ⟨h1, h2⟩ := mem_filter.1 hv
      refine mem_filter.2 ⟨?_, ?_⟩
      · simp only [lt2Om0, mem_filter, mem_univ, true_and] at h1 ⊢; rw [lt2Par_xor_even Λ D v hD, h1]
      · rw [lt2Xor_apply_mem hd]; cases h : v d <;> simp_all
    · intro u hu
      obtain ⟨h1, h2⟩ := mem_filter.1 hu
      refine mem_filter.2 ⟨?_, ?_⟩
      · simp only [lt2Om0, mem_filter, mem_univ, true_and] at h1 ⊢; rw [lt2Par_xor_even Λ D u hD, h1]
      · rw [lt2Xor_apply_mem hd, h2]; simp
    · intro v _; exact lt2Xor_xor v D
    · intro u _; exact lt2Xor_xor u D
    · intro v _; rw [lt2Xor_xor]
  rw [hsecond, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ => by ring

/-! ### Conditioning on the rows with `v_d = 1` -/

/-- The rows with `v_d = 1`. -/
def lt2Fd (d : Fin N) : Finset (State N) := univ.filter fun v => v d = true

/-- The rows of `f`, extended by `0`. -/
noncomputable def lt2fF {F : Finset (State N)} (f : F → Fin N → ℝ) (r : State N) : Fin N → ℝ :=
  if h : r ∈ F then f ⟨r, h⟩ else 0

/-- The coefficient of the free row `u` given the rows `f` of `F`. -/
noncomputable def lt2cG (Λ : Finset (Fin N)) (b : Bool) (D U : Finset (Fin N)) (d : Fin N)
    (f : lt2Fd d → Fin N → ℝ) (u : State N) : ℝ :=
  if u ∈ lt2Om0 Λ b then lt2gNs (lt2fF f (lt2Xor u D)) * (lt2Chi U u + lt2Chi U (lt2Xor u D)) else 0

lemma lt2_Gm_glue (Λ : Finset (Fin N)) {D : Finset (Fin N)} (U : Finset (Fin N)) {d : Fin N} (hd : d ∈ D)
    (hD : (D ∩ Λ).card % 2 = 0) (f : lt2Fd d → Fin N → ℝ) (g : {r // r ∉ lt2Fd d} → Fin N → ℝ) :
    lt2Gm Λ b D U (glueRows (lt2Fd d) f g) = ∑ q, lt2gNs (g q) * lt2cG Λ b D U d f q.1 := by
  rw [lt2_Gm_split Λ U hd hD]
  have hnotF : ∀ u : State N, u d = false → u ∉ lt2Fd d := fun u hu h => by
    simp only [lt2Fd, mem_filter, mem_univ, true_and] at h; simp_all
  have hF : ∀ u : State N, u d = false → lt2Xor u D ∈ lt2Fd d := fun u hu => by
    simp only [lt2Fd, mem_filter, mem_univ, true_and]; rw [lt2Xor_apply_mem hd, hu]; rfl
  -- rewrite the sum over the subtype as a sum over the complement
  have hsub : ∑ q : {r // r ∉ lt2Fd d}, lt2gNs (g q) * lt2cG Λ b D U d f q.1 =
      ∑ u ∈ (lt2Fd d)ᶜ, lt2gNs (glueRows (lt2Fd d) f g u) * lt2cG Λ b D U d f u := by
    have e : ∀ q : {r // r ∉ lt2Fd d}, lt2gNs (g q) * lt2cG Λ b D U d f q.1 =
        (fun u => lt2gNs (glueRows (lt2Fd d) f g u) * lt2cG Λ b D U d f u) q.1 := by
      intro q; simp only; rw [glueRows_of_not_mem (lt2Fd d) f g q.2]
    rw [Finset.sum_congr rfl fun q _ => e q]
    exact (Finset.sum_subtype (lt2Fd d)ᶜ (p := fun r => r ∉ lt2Fd d) (fun r => mem_compl)
      (fun u => lt2gNs (glueRows (lt2Fd d) f g u) * lt2cG Λ b D U d f u)).symm
  rw [hsub]
  have hsubset : (lt2Om0 Λ b).filter (fun u => u d = false) ⊆ (lt2Fd d)ᶜ := fun u hu =>
    mem_compl.2 (hnotF u (mem_filter.1 hu).2)
  rw [← Finset.sum_subset hsubset (fun u hu hnot => ?_)]
  · refine Finset.sum_congr rfl fun u hu => ?_
    obtain ⟨hu1, hu2⟩ := mem_filter.1 hu
    unfold lt2cG lt2fF
    rw [if_pos hu1, dif_pos (hF u hu2), glueRows_of_mem (lt2Fd d) f g (hF u hu2)]
    ring
  · have hu' : u ∉ lt2Om0 Λ b := fun h => hnot (mem_filter.2 ⟨h, by
      have := mem_compl.1 hu
      simp only [lt2Fd, mem_filter, mem_univ, true_and] at this
      cases h' : u d <;> simp_all⟩)
    unfold lt2cG; rw [if_neg hu', mul_zero]

/-! ### The conditional bound -/

lemma lt2_sum_fF_le (D : Finset (Fin N)) {d : Fin N} (hd : d ∈ D) (f : lt2Fd d → Fin N → ℝ) (φ : ℝ → ℝ)
    (hφ : ∀ x, 0 ≤ x → 0 ≤ φ x) :
    ∑ q : {r // r ∉ lt2Fd d}, φ (lt2gNs (lt2fF f (lt2Xor q.1 D))) ≤ ∑ p : lt2Fd d, φ (lt2gNs (f p)) := by
  have hF : ∀ q : {r // r ∉ lt2Fd d}, lt2Xor q.1 D ∈ lt2Fd d := fun q => by
    have := q.2
    simp only [lt2Fd, mem_filter, mem_univ, true_and] at this ⊢
    rw [lt2Xor_apply_mem hd]; cases h : q.1 d <;> simp_all
  set i : {r // r ∉ lt2Fd d} → lt2Fd d := fun q => ⟨lt2Xor q.1 D, hF q⟩
  have hinj : Function.Injective i := fun q q' h => by
    have := congrArg Subtype.val h
    simp only [i] at this
    exact Subtype.ext (by rw [← lt2Xor_xor q.1 D, this, lt2Xor_xor])
  calc ∑ q : {r // r ∉ lt2Fd d}, φ (lt2gNs (lt2fF f (lt2Xor q.1 D)))
      = ∑ q : {r // r ∉ lt2Fd d}, φ (lt2gNs (f (i q))) := Finset.sum_congr rfl fun q _ => by
        simp only [i, lt2fF, dif_pos (hF q)]
    _ = ∑ p ∈ univ.image i, φ (lt2gNs (f p)) :=
        (Finset.sum_image (f := fun p => φ (lt2gNs (f p))) (s := univ) (g := i) fun q _ q' _ h => hinj h).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun p _ _ => hφ _ (lt2gNs_nonneg _)

lemma lt2cG_abs (Λ : Finset (Fin N)) (D U : Finset (Fin N)) (d : Fin N) (f : lt2Fd d → Fin N → ℝ) (u : State N) :
    |lt2cG Λ b D U d f u| ≤ 2 * lt2gNs (lt2fF f (lt2Xor u D)) := by
  unfold lt2cG
  split_ifs
  · rw [abs_mul, abs_of_nonneg (lt2gNs_nonneg _)]
    have : |lt2Chi U u + lt2Chi U (lt2Xor u D)| ≤ 2 := (abs_add_le _ _).trans (by
      rw [lt2Chi_abs, lt2Chi_abs]; norm_num)
    nlinarith [lt2gNs_nonneg (lt2fF f (lt2Xor u D))]
  · rw [abs_zero]; exact mul_nonneg zero_le_two (lt2gNs_nonneg _)

/-- **The conditional tail of a `D ≠ ∅` Gram statistic.** -/
theorem lt2_Gm_cond (Λ : Finset (Fin N)) {D : Finset (Fin N)} (U : Finset (Fin N)) {d : Fin N} (hd : d ∈ D)
    (f : lt2Fd d → Fin N → ℝ) (hS1 : ∑ p : lt2Fd d, lt2gNs (f p) ≤ 2)
    (hS2 : ∑ p : lt2Fd d, lt2gNs (f p) ^ 2 ≤ 2 * sigN N ^ 2) {t : ℝ} (ht : 8 * (1 / 2 : ℝ) ^ N ≤ t) :
    (rowsOutM (lt2Fd d)).real {g | t ≤ |∑ q, lt2gNs (g q) * lt2cG Λ b D U d f q.1|} ≤
      2 * Real.exp (-min ((t / 2) ^ 2 / (4 * (8 * (1 / 3 : ℝ) ^ N * sigN N ^ 2))) ((t / 2) / (2 * (2 * lt2θ N ^ 2)))) := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  haveI : IsProbabilityMeasure (rowsOutM (lt2Fd d)) := by unfold rowsOutM; infer_instance
  set m1 := ∫ x, lt2gNs x ∂rowM N
  have hm1 : 0 ≤ m1 := integral_nonneg fun x => lt2gNs_nonneg x
  have hm1u : m1 ≤ (1 / 2 : ℝ) ^ N := by
    have h := lt2gNs_pow_int (N := N) 1
    simp only [pow_one] at h
    exact h.trans (le_of_eq (by norm_num))
  have hm1θ : m1 ≤ lt2θ N := by
    calc m1 ≤ ∫ _x, lt2θ N ∂rowM N := integral_mono_of_nonneg (ae_of_all _ fun x => lt2gNs_nonneg x)
          (integrable_const _) (ae_of_all _ lt2gNs_le)
      _ = lt2θ N := by simp
  set c : {r // r ∉ lt2Fd d} → ℝ := fun q => lt2cG Λ b D U d f q.1
  have hcabs : ∀ q, |c q| ≤ 2 * lt2gNs (lt2fF f (lt2Xor q.1 D)) := fun q => lt2cG_abs Λ D U d f q.1
  have hc2θ : ∀ q, |c q| ≤ 2 * lt2θ N := fun q => (hcabs q).trans (by linarith [lt2gNs_le (lt2fF f (lt2Xor q.1 D))])
  -- the mean term
  have hmean : |m1 * ∑ q, c q| ≤ t / 2 := by
    rw [abs_mul, abs_of_nonneg hm1]
    have h1 : |∑ q, c q| ≤ 4 := by
      calc |∑ q, c q| ≤ ∑ q, |c q| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ q : {r // r ∉ lt2Fd d}, 2 * lt2gNs (lt2fF f (lt2Xor q.1 D)) := Finset.sum_le_sum fun q _ => hcabs q
        _ ≤ ∑ p : lt2Fd d, 2 * lt2gNs (f p) :=
            lt2_sum_fF_le D hd f (fun x => 2 * x) (fun x hx => by positivity)
        _ ≤ 4 := by rw [← Finset.mul_sum]; linarith
    nlinarith [abs_nonneg (∑ q, c q)]
  -- the centred part
  have hgm : Measurable (lt2gNs (N := N)) := lt2gNs_measurable
  have hint1 : Integrable (lt2gNs (N := N)) (rowM N) :=
    Integrable.of_bound hgm.aestronglyMeasurable (lt2θ N) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (lt2gNs_nonneg x)]; exact lt2gNs_le x)
  have hint2 : Integrable (fun x => lt2gNs (N := N) x ^ 2) (rowM N) :=
    Integrable.of_bound (hgm.pow_const 2).aestronglyMeasurable (lt2θ N ^ 2) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (lt2gNs_nonneg x) (lt2gNs_le x) 2)
  have hvar1 : ∫ x, (lt2gNs x - m1) ^ 2 ∂rowM N ≤ (1 / 3 : ℝ) ^ N := by
    have e : (fun x : Fin N → ℝ => (lt2gNs x - m1) ^ 2) = fun x => lt2gNs x ^ 2 - 2 * m1 * lt2gNs x + m1 ^ 2 := by
      funext x; ring
    rw [e, integral_add (f := fun x => lt2gNs x ^ 2 - 2 * m1 * lt2gNs x) (g := fun _ => m1 ^ 2)
      (hint2.sub (hint1.const_mul _)) (integrable_const _),
      integral_sub (f := fun x => lt2gNs x ^ 2) (g := fun x => 2 * m1 * lt2gNs x) hint2 (hint1.const_mul _),
      integral_const_mul, integral_const]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    have := lt2gNs_pow_int (N := N) 2
    norm_num at this ⊢
    nlinarith
  have htpos : 0 ≤ t / 2 := by
    have : (0 : ℝ) < (1 / 2) ^ N := by positivity
    linarith
  have hG := lt2_rowsout_abs (lt2Fd d) (fun q x => (lt2gNs x - m1) * c q)
    (fun q => (hgm.sub measurable_const).mul_const _) (M := 2 * lt2θ N ^ 2) (by positivity)
    (fun q x => by
      rw [abs_mul]
      have h1 : |lt2gNs x - m1| ≤ lt2θ N := abs_sub_le_iff.2 ⟨by linarith [lt2gNs_le x], by
        linarith [lt2gNs_nonneg x]⟩
      calc |lt2gNs x - m1| * |c q| ≤ lt2θ N * (2 * lt2θ N) :=
            mul_le_mul h1 (hc2θ q) (abs_nonneg _) (Real.exp_pos _).le
        _ = 2 * lt2θ N ^ 2 := by ring)
    (fun q => by rw [integral_mul_const, integral_sub hint1 (integrable_const _), integral_const]; simp [m1])
    (V := 8 * (1 / 3 : ℝ) ^ N * sigN N ^ 2) (ε := t / 2) htpos (by
      calc ∑ q, ∫ x, ((lt2gNs x - m1) * c q) ^ 2 ∂rowM N
          = ∑ q, (∫ x, (lt2gNs x - m1) ^ 2 ∂rowM N) * c q ^ 2 := Finset.sum_congr rfl fun q _ => by
            rw [← integral_mul_const]; exact integral_congr_ae (ae_of_all _ fun x => by ring)
        _ ≤ ∑ q, (1 / 3 : ℝ) ^ N * (4 * lt2gNs (lt2fF f (lt2Xor q.1 D)) ^ 2) := Finset.sum_le_sum fun q _ => by
            refine mul_le_mul hvar1 ?_ (sq_nonneg _) (by positivity)
            have := hcabs q
            calc c q ^ 2 = |c q| ^ 2 := (sq_abs _).symm
              _ ≤ (2 * lt2gNs (lt2fF f (lt2Xor q.1 D))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
              _ = _ := by ring
        _ = 4 * (1 / 3 : ℝ) ^ N * ∑ q : {r // r ∉ lt2Fd d}, lt2gNs (lt2fF f (lt2Xor q.1 D)) ^ 2 := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
        _ ≤ 4 * (1 / 3 : ℝ) ^ N * ∑ p : lt2Fd d, lt2gNs (f p) ^ 2 :=
            mul_le_mul_of_nonneg_left (lt2_sum_fF_le D hd f (fun x => x ^ 2) (fun x _ => sq_nonneg x)) (by positivity)
        _ ≤ 4 * (1 / 3 : ℝ) ^ N * (2 * sigN N ^ 2) := mul_le_mul_of_nonneg_left hS2 (by positivity)
        _ = 8 * (1 / 3 : ℝ) ^ N * sigN N ^ 2 := by ring)
  refine (measureReal_mono ?_).trans hG
  intro g hg
  simp only [Set.mem_setOf_eq] at hg ⊢
  have e : ∑ q, lt2gNs (g q) * c q = ∑ q, (lt2gNs (g q) - m1) * c q + m1 * ∑ q, c q := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun q _ => by ring
  have h1 : t ≤ |∑ q, (lt2gNs (g q) - m1) * c q + m1 * ∑ q, c q| := by rw [← e]; exact hg
  have h2 := abs_add_le (∑ q, (lt2gNs (g q) - m1) * c q) (m1 * ∑ q, c q)
  linarith

/-! ### The unconditional `D ≠ ∅` Gram event -/

lemma lt2_measurable_Gm (Λ : Finset (Fin N)) (D U : Finset (Fin N)) :
    Measurable fun w : Param N => lt2Gm Λ b D U w := by
  unfold lt2Gm
  exact Finset.measurable_sum _ fun v _ => ((lt2gNs_measurable.comp (measurable_pi_apply v)).mul
    (lt2gNs_measurable.comp (measurable_pi_apply _))).mul_const _

/-- **`D ≠ ∅` Gram event**, unconditional. -/
theorem lt2_Gm_offD (Λ : Finset (Fin N)) {D : Finset (Fin N)} (U : Finset (Fin N)) {d : Fin N} (hd : d ∈ D)
    (hD : (D ∩ Λ).card % 2 = 0) {t : ℝ} (ht : 8 * (1 / 2 : ℝ) ^ N ≤ t) :
    cubeM N {w | t ≤ |lt2Gm Λ b D U w|} ≤
      ENNReal.ofReal (2 * Real.exp (-min ((t / 2) ^ 2 / (4 * (8 * (1 / 3 : ℝ) ^ N * sigN N ^ 2)))
        ((t / 2) / (2 * (2 * lt2θ N ^ 2))))) +
      cubeM N {w | 2 < ∑ v ∈ lt2Fd d, lt2gNs (w v)} +
      cubeM N {w | 2 * sigN N ^ 2 < ∑ v ∈ lt2Fd d, lt2gNs (w v) ^ 2} := by
  set F := lt2Fd d
  set X := {w : Param N | t ≤ |lt2Gm Λ b D U w|}
  have hX : MeasurableSet X := measurableSet_le measurable_const (lt2_measurable_Gm (b := b) Λ D U).abs
  set G : Set (F → Fin N → ℝ) := {f | ∑ p : F, lt2gNs (f p) ≤ 2 ∧ ∑ p : F, lt2gNs (f p) ^ 2 ≤ 2 * sigN N ^ 2}
  have hGm : MeasurableSet G := by
    have m1 : Measurable fun f : F → Fin N → ℝ => ∑ p : F, lt2gNs (f p) :=
      Finset.measurable_sum _ fun p _ => lt2gNs_measurable.comp (measurable_pi_apply p)
    have m2 : Measurable fun f : F → Fin N → ℝ => ∑ p : F, lt2gNs (f p) ^ 2 :=
      Finset.measurable_sum _ fun p _ => (lt2gNs_measurable.comp (measurable_pi_apply p)).pow_const 2
    exact (measurableSet_le m1 measurable_const).inter (measurableSet_le m2 measurable_const)
  set δ := ENNReal.ofReal (2 * Real.exp (-min ((t / 2) ^ 2 / (4 * (8 * (1 / 3 : ℝ) ^ N * sigN N ^ 2)))
        ((t / 2) / (2 * (2 * lt2θ N ^ 2)))))
  have hcond : ∀ f ∈ G, rowsOutM F {g | glueRows F f g ∈ X} ≤ δ := by
    intro f hf
    haveI : IsProbabilityMeasure (rowsOutM F) := by unfold rowsOutM; infer_instance
    have h := lt2_Gm_cond (b := b) Λ U hd f hf.1 hf.2 ht
    have e : {g | glueRows F f g ∈ X} = {g | t ≤ |∑ q, lt2gNs (g q) * lt2cG Λ b D U d f q.1|} := by
      ext g; simp only [X, Set.mem_setOf_eq]; rw [lt2_Gm_glue Λ U hd hD f g]
    rw [e, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h
  have h1 := cubeM_inter_restrIn_le F hX hGm hcond
  have hsplit : X ⊆ (X ∩ {w | restrIn F w ∈ G}) ∪ ({w | 2 < ∑ v ∈ F, lt2gNs (w v)} ∪
      {w | 2 * sigN N ^ 2 < ∑ v ∈ F, lt2gNs (w v) ^ 2}) := by
    intro w hw
    by_cases hg : restrIn F w ∈ G
    · exact Or.inl ⟨hw, hg⟩
    · right
      simp only [G, Set.mem_setOf_eq, not_and_or, not_le] at hg
      have e1 : ∑ p : F, lt2gNs (restrIn F w p) = ∑ v ∈ F, lt2gNs (w v) :=
        Finset.sum_coe_sort F (fun v => lt2gNs (w v))
      have e2 : ∑ p : F, lt2gNs (restrIn F w p) ^ 2 = ∑ v ∈ F, lt2gNs (w v) ^ 2 :=
        Finset.sum_coe_sort F (fun v => lt2gNs (w v) ^ 2)
      rcases hg with h | h
      · left; simp only [Set.mem_setOf_eq]; rw [← e1]; exact h
      · right; simp only [Set.mem_setOf_eq]; rw [← e2]; exact h
  calc cubeM N X ≤ cubeM N (X ∩ {w | restrIn F w ∈ G}) + (cubeM N {w | 2 < ∑ v ∈ F, lt2gNs (w v)} +
        cubeM N {w | 2 * sigN N ^ 2 < ∑ v ∈ F, lt2gNs (w v) ^ 2}) :=
        (measure_mono hsplit).trans ((measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _)))
    _ ≤ δ + (cubeM N {w | 2 < ∑ v ∈ F, lt2gNs (w v)} + cubeM N {w | 2 * sigN N ^ 2 < ∑ v ∈ F, lt2gNs (w v) ^ 2}) := by
        gcongr
        refine h1.trans ?_
        haveI : IsProbabilityMeasure (rowsInM F) := by unfold rowsInM; infer_instance
        calc δ * rowsInM F G ≤ δ * 1 := by gcongr; exact prob_le_one
          _ = δ := mul_one _
    _ = _ := by rw [add_assoc]

end Census
end IIT
