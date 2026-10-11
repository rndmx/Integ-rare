/-
Census, B1 lemma LT2, module M3 part 3f: the unconditional tail of a signed sum of `Ñ⁰` statistics.

On the good-Gram event `Γ'(Fam)` (a function of the `Ω_b` rows: diagonal `≤ 2σ²`, off-diagonal `≤ σ²/N⁴`), the
conditional variance given the `Ω_b` rows is `≤ (2σ²|A| + |A|²σ²/N⁴)/12`; integrating over the `Ω_b` rows
(`cubeM_inter_restrIn_le`) gives `lt2_N0_tail`.
-/
import IIT.Census.B1LT2Gram4

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ} {b : Bool}

/-- Odd + odd intersections give an even symmetric difference. -/
lemma lt2_symmDiff_even {R R' Λ : Finset (Fin N)} (h : (R ∩ Λ).card % 2 = 1) (h' : (R' ∩ Λ).card % 2 = 1) :
    (symmDiff R R' ∩ Λ).card % 2 = 0 := by
  have e : symmDiff R R' ∩ Λ = symmDiff (R ∩ Λ) (R' ∩ Λ) := by
    ext j; simp only [mem_inter, Finset.mem_symmDiff]; tauto
  rw [e]
  have e1 : symmDiff (R ∩ Λ) (R' ∩ Λ) = ((R ∩ Λ) ∪ (R' ∩ Λ)) \ ((R ∩ Λ) ∩ (R' ∩ Λ)) :=
    symmDiff_eq_sup_sdiff_inf _ _
  rw [e1, Finset.card_sdiff, Finset.inter_eq_left.2 Finset.inter_subset_union]
  have := Finset.card_union_add_card_inter (R ∩ Λ) (R' ∩ Λ)
  have := Finset.card_le_card (Finset.inter_subset_union (s := R ∩ Λ) (t := R' ∩ Λ))
  omega

/-- The good-Gram event of a family. -/
def lt2GoodGram (Λ : Finset (Fin N)) (b : Bool) (Fam : Finset (LT2Idx N)) (w : Param N) : Prop :=
  ∑ v ∈ lt2Om0 Λ b, lt2gNs (w v) ^ 2 ≤ 2 * sigN N ^ 2 ∧
    ∀ α ∈ Fam, ∀ α' ∈ Fam, α.1 = α'.1 → α ≠ α' →
      |lt2Gm Λ b (symmDiff α.2.1 α'.2.1) (symmDiff α.2.2 α'.2.2) w| ≤ sigN N ^ 2 / (N : ℝ) ^ 4

lemma lt2Gm_diag (Λ : Finset (Fin N)) (w : Param N) :
    lt2Gm Λ b ∅ ∅ w = ∑ v ∈ lt2Om0 Λ b, lt2gNs (w v) ^ 2 := by
  unfold lt2Gm; simp only [lt2Xor_empty]
  exact Finset.sum_congr rfl fun v _ => by unfold lt2Chi; simp; ring

/-- **The conditional-variance bound on the good-Gram event.** -/
lemma lt2_var_on_good (Λ : Finset (Fin N)) (Fam : Finset (LT2Idx N))
    (hFam : ∀ α ∈ Fam, (α.2.1 ∩ Λ).card % 2 = 1) {A : Finset (LT2Idx N)} (hA : A ⊆ Fam) (A' : Finset (LT2Idx N))
    {w : Param N} (hw : lt2GoodGram Λ b Fam w) :
    ∑ i, ∑ q ∈ (lt2Om0 Λ b)ᶜ, lt2Coef Λ b A A' w q i ^ 2 ≤
      2 * sigN N ^ 2 * A.card + (A.card : ℝ) ^ 2 * (sigN N ^ 2 / (N : ℝ) ^ 4) := by
  have hσ : 0 ≤ sigN N ^ 2 / (N : ℝ) ^ 4 := by positivity
  calc ∑ i, ∑ q ∈ (lt2Om0 Λ b)ᶜ, lt2Coef Λ b A A' w q i ^ 2
      ≤ ∑ i, ∑ α ∈ A.filter (fun α => α.1 = i), ∑ α' ∈ A.filter (fun α => α.1 = i),
          |lt2Gm Λ b (symmDiff α.2.1 α'.2.1) (symmDiff α.2.2 α'.2.2) w| :=
        Finset.sum_le_sum fun i _ => lt2_coef_sq Λ A A' (fun α hα => hFam α (hA hα)) w i
    _ ≤ ∑ i, ∑ α ∈ A.filter (fun α => α.1 = i), (2 * sigN N ^ 2 +
          (A.filter (fun α => α.1 = i)).card * (sigN N ^ 2 / (N : ℝ) ^ 4)) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun α hα => ?_
        rw [← Finset.add_sum_erase _ _ hα]
        refine add_le_add ?_ ?_
        · rw [symmDiff_self, symmDiff_self]
          show |lt2Gm Λ b ∅ ∅ w| ≤ 2 * sigN N ^ 2
          rw [lt2Gm_diag, abs_of_nonneg (Finset.sum_nonneg fun v _ => sq_nonneg _)]; exact hw.1
        · calc ∑ α' ∈ (A.filter (fun α => α.1 = i)).erase α,
                |lt2Gm Λ b (symmDiff α.2.1 α'.2.1) (symmDiff α.2.2 α'.2.2) w|
              ≤ ∑ _α' ∈ (A.filter (fun α => α.1 = i)).erase α, sigN N ^ 2 / (N : ℝ) ^ 4 :=
                Finset.sum_le_sum fun α' hα' => by
                  obtain ⟨hne, hα'A⟩ := mem_erase.1 hα'
                  have h1 := (mem_filter.1 hα).2; have h2 := (mem_filter.1 hα'A).2
                  exact hw.2 α (hA (mem_filter.1 hα).1) α' (hA (mem_filter.1 hα'A).1) (h1.trans h2.symm)
                    (Ne.symm hne)
            _ ≤ (A.filter (fun α => α.1 = i)).card * (sigN N ^ 2 / (N : ℝ) ^ 4) := by
                rw [Finset.sum_const, nsmul_eq_mul]
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_erase_le) hσ
    _ = ∑ i, ((A.filter (fun α => α.1 = i)).card * (2 * sigN N ^ 2) +
          ((A.filter (fun α => α.1 = i)).card : ℝ) ^ 2 * (sigN N ^ 2 / (N : ℝ) ^ 4)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 2 * sigN N ^ 2 * A.card + (A.card : ℝ) ^ 2 * (sigN N ^ 2 / (N : ℝ) ^ 4) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
        have hcard : ∑ i, ((A.filter (fun α => α.1 = i)).card : ℝ) = A.card := by
          have := Finset.card_eq_sum_card_fiberwise (f := fun α : LT2Idx N => α.1) (s := A) (t := univ)
            (fun α _ => mem_univ _)
          exact_mod_cast this.symm
        have hsq : ∑ i, ((A.filter (fun α => α.1 = i)).card : ℝ) ^ 2 ≤ (A.card : ℝ) ^ 2 := by
          rw [← hcard, sq, Finset.sum_mul_sum]
          refine Finset.sum_le_sum fun i _ => ?_
          rw [sq]
          exact Finset.single_le_sum (f := fun j => ((A.filter (fun α => α.1 = i)).card : ℝ) *
            ((A.filter (fun α => α.1 = j)).card : ℝ)) (fun j _ => by positivity) (mem_univ i)
        rw [hcard]
        nlinarith [mul_le_mul_of_nonneg_right hsq hσ]

/-! ### Locality in the `Ω_b` rows -/

lemma lt2Coef_local (Λ : Finset (Fin N)) (A A' : Finset (LT2Idx N)) {w w' : Param N}
    (h : ∀ r ∈ lt2Om0 Λ b, w r = w' r) (q : State N) (i : Fin N) :
    lt2Coef Λ b A A' w q i = lt2Coef Λ b A A' w' q i := by
  unfold lt2Coef
  refine Finset.sum_congr rfl fun α _ => ?_
  congr 1
  split_ifs with hm
  · rw [h _ hm]
  · rfl

lemma lt2GoodGram_local (Λ : Finset (Fin N)) (Fam : Finset (LT2Idx N))
    (hFam : ∀ α ∈ Fam, (α.2.1 ∩ Λ).card % 2 = 1) {w w' : Param N} (h : ∀ r ∈ lt2Om0 Λ b, w r = w' r) :
    lt2GoodGram Λ b Fam w ↔ lt2GoodGram Λ b Fam w' := by
  have hG : ∀ α ∈ Fam, ∀ α' ∈ Fam,
      lt2Gm Λ b (symmDiff α.2.1 α'.2.1) (symmDiff α.2.2 α'.2.2) w =
        lt2Gm Λ b (symmDiff α.2.1 α'.2.1) (symmDiff α.2.2 α'.2.2) w' := by
    intro α hα α' hα'
    have hev := lt2_symmDiff_even (hFam α hα) (hFam α' hα')
    unfold lt2Gm
    refine Finset.sum_congr rfl fun v hv => ?_
    have hv' : lt2Xor v (symmDiff α.2.1 α'.2.1) ∈ lt2Om0 Λ b := by
      simp only [lt2Om0, mem_filter, mem_univ, true_and] at hv ⊢
      rw [lt2Par_xor_even Λ _ v hev, hv]
    rw [h v hv, h _ hv']
  have hd : ∑ v ∈ lt2Om0 Λ b, lt2gNs (w v) ^ 2 = ∑ v ∈ lt2Om0 Λ b, lt2gNs (w' v) ^ 2 :=
    Finset.sum_congr rfl fun v hv => by rw [h v hv]
  unfold lt2GoodGram
  rw [hd]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun α hα α' hα' hi hne => (hG α hα α' hα').symm ▸ h2 α hα α' hα' hi hne⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun α hα α' hα' hi hne => (hG α hα α' hα') ▸ h2 α hα α' hα' hi hne⟩

/-! ### The conditional and unconditional tails -/

lemma lt2_coef_abs_sum (Λ : Finset (Fin N)) (A A' : Finset (LT2Idx N)) (w : Param N) (q : State N) :
    ∑ i, |lt2Coef Λ b A A' w q i| ≤ lt2θ N * A.card := by
  calc ∑ i, |lt2Coef Λ b A A' w q i|
      ≤ ∑ i, ∑ α ∈ A.filter (fun α => α.1 = i), lt2θ N := Finset.sum_le_sum fun i _ => by
        unfold lt2Coef
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ => ?_)
        rw [abs_mul]
        have h1 : |(if α ∈ A' then (1 : ℝ) else -1)| = 1 := by split_ifs <;> norm_num
        rw [h1, one_mul]
        split_ifs
        · rw [abs_mul, lt2Chi_abs, mul_one, abs_of_nonneg (lt2gNs_nonneg _)]; exact lt2gNs_le _
        · rw [abs_zero]; exact (Real.exp_pos _).le
    _ = lt2θ N * A.card := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.sum_mul]
        have := Finset.card_eq_sum_card_fiberwise (f := fun α : LT2Idx N => α.1) (s := A) (t := univ)
          (fun α _ => mem_univ _)
        rw [show (∑ i, ((A.filter (fun α => α.1 = i)).card : ℝ)) = A.card by exact_mod_cast this.symm]
        ring

/-- **Tail of a signed sum of `Ñ⁰`'s**, unconditional. -/
theorem lt2_N0_tail (Λ : Finset (Fin N)) (Fam : Finset (LT2Idx N))
    (hFam : ∀ α ∈ Fam, (α.2.1 ∩ Λ).card % 2 = 1) {A : Finset (LT2Idx N)} (hA : A ⊆ Fam)
    (A' : Finset (LT2Idx N)) {ε : ℝ} (hε : 0 ≤ ε) :
    cubeM N {w | ε ≤ ∑ α ∈ A, (if α ∈ A' then lt2N0 Λ b w α else -lt2N0 Λ b w α)} ≤
      ENNReal.ofReal (Real.exp (-min (ε ^ 2 / (4 * ((2 * sigN N ^ 2 * A.card +
        (A.card : ℝ) ^ 2 * (sigN N ^ 2 / (N : ℝ) ^ 4)) / 12))) (ε / (2 * (lt2θ N * A.card / 2))))) +
      cubeM N {w | ¬ lt2GoodGram Λ b Fam w} := by
  set F := lt2Om0 Λ b
  set X := {w : Param N | ε ≤ ∑ α ∈ A, (if α ∈ A' then lt2N0 Λ b w α else -lt2N0 Λ b w α)}
  have hX : MeasurableSet X := by
    refine measurableSet_le measurable_const (Finset.measurable_sum _ fun α _ => ?_)
    have hm : Measurable fun w : Param N => lt2N0 Λ b w α := by
      unfold lt2N0
      refine Finset.measurable_sum _ fun v _ => ?_
      have hc : Measurable fun w : Param N => clamp01 (w (lt2Xor v α.2.1) α.1) :=
        clamp01_measurable.comp ((measurable_pi_apply α.1).comp (measurable_pi_apply (lt2Xor v α.2.1)))
      exact ((lt2gNs_measurable.comp (measurable_pi_apply v)).mul (hc.sub measurable_const)).mul_const _
    split_ifs
    · exact hm
    · exact hm.neg
  set w0 : (F → Fin N → ℝ) → Param N := fun f => glueRows F f (fun _ _ => 0)
  have hGood : MeasurableSet {w : Param N | lt2GoodGram Λ b Fam w} := by
    simp only [lt2GoodGram, Set.setOf_and, Set.setOf_forall]
    refine (measurableSet_le (Finset.measurable_sum _ fun v _ =>
      (lt2gNs_measurable.comp (measurable_pi_apply v)).pow_const 2) measurable_const).inter ?_
    refine MeasurableSet.iInter fun α => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun α' =>
      MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
    exact measurableSet_le (lt2_measurable_Gm Λ _ _).abs measurable_const
  have hsplit : cubeM N X ≤ cubeM N (X ∩ {w | lt2GoodGram Λ b Fam w}) + cubeM N {w | ¬ lt2GoodGram Λ b Fam w} :=
    calc cubeM N X ≤ cubeM N ((X ∩ {w | lt2GoodGram Λ b Fam w}) ∪ {w | ¬ lt2GoodGram Λ b Fam w}) :=
          measure_mono fun w hw => by
            by_cases h : lt2GoodGram Λ b Fam w
            · exact Or.inl ⟨hw, h⟩
            · exact Or.inr h
      _ ≤ _ := measure_union_le _ _
  refine hsplit.trans (add_le_add_left ?_ _)
  refine cubeM_le_of_rows F (hX.inter hGood) fun f => ?_
  by_cases hf : lt2GoodGram Λ b Fam (w0 f)
  · have hloc : ∀ g, ∀ r ∈ lt2Om0 Λ b, glueRows F f g r = w0 f r := fun g => glueRows_agree F f _ g
    set c : {r // r ∉ F} → Fin N → ℝ := fun q i => lt2Coef Λ b A A' (w0 f) q.1 i
    have hsub : {g | glueRows F f g ∈ X ∩ {w | lt2GoodGram Λ b Fam w}} ⊆
        {g | ε ≤ ∑ q, ∑ i, c q i * (clamp01 (g q i) - 1 / 2)} := by
      intro g hg
      obtain ⟨hgX, -⟩ := hg
      simp only [X, Set.mem_setOf_eq] at hgX ⊢
      rw [lt2_N0_regroup Λ A A' (fun α hα => hFam α (hA hα)) (glueRows F f g),
        Finset.sum_subtype Fᶜ (p := fun r => r ∉ F) (fun r => mem_compl)
          (fun q => ∑ i, lt2Coef Λ b A A' (glueRows F f g) q i * (clamp01 (glueRows F f g q i) - 1 / 2))] at hgX
      refine hgX.trans (le_of_eq (Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_))
      simp only [c]
      rw [lt2Coef_local Λ A A' (hloc g), glueRows_of_not_mem F f g q.2]
    have hM0 : 0 ≤ lt2θ N * A.card / 2 := by unfold lt2θ; positivity
    have hM : ∀ q, (∑ i, |c q i|) / 2 ≤ lt2θ N * A.card / 2 := fun q => by
      have := lt2_coef_abs_sum (b := b) Λ A A' (w0 f) q.1; simp only [c]; linarith
    have hV : (∑ q, ∑ i, c q i ^ 2) / 12 ≤
        (2 * sigN N ^ 2 * A.card + (A.card : ℝ) ^ 2 * (sigN N ^ 2 / (N : ℝ) ^ 4)) / 12 := by
      have h := lt2_var_on_good Λ Fam hFam hA A' hf
      rw [Finset.sum_comm, Finset.sum_subtype Fᶜ (p := fun r => r ∉ F) (fun r => mem_compl)
        (fun q => ∑ i, lt2Coef Λ b A A' (w0 f) q i ^ 2)] at h
      exact div_le_div_of_nonneg_right h (by norm_num)
    calc rowsOutM F {g | glueRows F f g ∈ X ∩ {w | lt2GoodGram Λ b Fam w}}
        ≤ rowsOutM F {g | ε ≤ ∑ q, ∑ i, c q i * (clamp01 (g q i) - 1 / 2)} := measure_mono hsub
      _ = ENNReal.ofReal ((rowsOutM F).real {g | ε ≤ ∑ q, ∑ i, c q i * (clamp01 (g q i) - 1 / 2)}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (lt2_rows_half_tail F c hε hM0 hM hV)
  · have he : {g | glueRows F f g ∈ X ∩ {w | lt2GoodGram Λ b Fam w}} = ∅ := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, hg⟩
      exact hf ((lt2GoodGram_local Λ Fam hFam (glueRows_agree F f g (fun _ _ => 0))).2 hg)
    rw [he, measure_empty]; exact zero_le

/-! ### Failure of the good-Gram event -/

/-- The off-diagonal Gram threshold `t = σ²/N⁴`. -/
noncomputable def lt2tG (N : ℕ) : ℝ := sigN N ^ 2 / (N : ℝ) ^ 4

/-- The `S2` tail rate. -/
noncomputable def lt2B2 (N : ℕ) : ℝ :=
  Real.exp (-min ((sigN N ^ 2) ^ 2 / (4 * (2 / 5 : ℝ) ^ N)) (sigN N ^ 2 / (2 * (2 * lt2θ N ^ 2))))

/-- The per-pair failure rate (sum of the `D = ∅` and `D ≠ ∅` bounds). -/
noncomputable def lt2Bpair (N : ℕ) : ℝ :=
  2 * Real.exp (-min (lt2tG N ^ 2 / (4 * (2 / 5 : ℝ) ^ N)) (lt2tG N / (2 * (2 * lt2θ N ^ 2)))) +
  2 * Real.exp (-min ((lt2tG N / 2) ^ 2 / (4 * (8 * (1 / 3 : ℝ) ^ N * sigN N ^ 2)))
    ((lt2tG N / 2) / (2 * (2 * lt2θ N ^ 2)))) +
  Real.exp (-min (1 / (4 * sigN N ^ 2)) (1 / (4 * lt2θ N))) + lt2B2 N

lemma lt2Bpair_nonneg : 0 ≤ lt2Bpair N := by unfold lt2Bpair lt2B2; positivity

lemma lt2_pair_fail (Λ : Finset (Fin N)) {α α' : LT2Idx N}
    (hα : (α.2.1 ∩ Λ).card % 2 = 1) (hα' : (α'.2.1 ∩ Λ).card % 2 = 1) (hi : α.1 = α'.1) (hne : α ≠ α')
    (hT : α.2.1 = α'.2.1 → symmDiff α.2.2 α'.2.2 ≠ Λ) (hN : 8 * (1 / 2 : ℝ) ^ N ≤ lt2tG N) :
    cubeM N {w | lt2tG N ≤ |lt2Gm Λ b (symmDiff α.2.1 α'.2.1) (symmDiff α.2.2 α'.2.2) w|} ≤
      ENNReal.ofReal (lt2Bpair N) := by
  have ht : 0 ≤ lt2tG N := by unfold lt2tG; positivity
  have e1 : 0 ≤ Real.exp (-min (1 / (4 * sigN N ^ 2)) (1 / (4 * lt2θ N))) := (Real.exp_pos _).le
  have e2 : 0 ≤ lt2B2 N := (Real.exp_pos _).le
  set Bz := 2 * Real.exp (-min (lt2tG N ^ 2 / (4 * (2 / 5 : ℝ) ^ N)) (lt2tG N / (2 * (2 * lt2θ N ^ 2))))
  set Bo := 2 * Real.exp (-min ((lt2tG N / 2) ^ 2 / (4 * (8 * (1 / 3 : ℝ) ^ N * sigN N ^ 2)))
    ((lt2tG N / 2) / (2 * (2 * lt2θ N ^ 2))))
  have hBz : 0 ≤ Bz := by positivity
  have hBo : 0 ≤ Bo := by positivity
  by_cases hD : symmDiff α.2.1 α'.2.1 = ∅
  · have hR : α.2.1 = α'.2.1 := symmDiff_eq_bot.1 hD
    have hU : (symmDiff α.2.2 α'.2.2).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hU
      have hT' : α.2.2 = α'.2.2 := symmDiff_eq_bot.1 hU
      exact hne (Prod.ext hi (Prod.ext hR hT'))
    rw [hD]
    refine (lt2_Gm_zero Λ _ hU (hT hR) ht).trans (ENNReal.ofReal_le_ofReal ?_)
    unfold lt2Bpair; linarith
  · obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.2 hD
    refine (lt2_Gm_offD Λ _ hd (lt2_symmDiff_even hα hα') hN).trans ?_
    have h1 := lt2_S1_tail (lt2Fd (N := N) d)
    have h2 := lt2_S2_tail (lt2Fd (N := N) d)
    calc _ ≤ ENNReal.ofReal Bo + ENNReal.ofReal (Real.exp (-min (1 / (4 * sigN N ^ 2)) (1 / (4 * lt2θ N)))) +
          ENNReal.ofReal (lt2B2 N) := add_le_add (add_le_add le_rfl h1) h2
      _ = ENNReal.ofReal (Bo + Real.exp (-min (1 / (4 * sigN N ^ 2)) (1 / (4 * lt2θ N))) + lt2B2 N) := by
          rw [ENNReal.ofReal_add (by positivity) e2, ENNReal.ofReal_add hBo e1]
      _ ≤ ENNReal.ofReal (lt2Bpair N) := ENNReal.ofReal_le_ofReal (by unfold lt2Bpair; linarith)

/-- **The good-Gram event fails with probability `≤ B₂ + |Fam|² B_pair`.** -/
theorem lt2_GoodGram_fail (Λ : Finset (Fin N)) (Fam : Finset (LT2Idx N))
    (hFam : ∀ α ∈ Fam, (α.2.1 ∩ Λ).card % 2 = 1)
    (hT : ∀ α ∈ Fam, ∀ α' ∈ Fam, α.2.1 = α'.2.1 → symmDiff α.2.2 α'.2.2 ≠ Λ)
    (hN : 8 * (1 / 2 : ℝ) ^ N ≤ lt2tG N) :
    cubeM N {w | ¬ lt2GoodGram Λ b Fam w} ≤ ENNReal.ofReal (lt2B2 N + (Fam.card : ℝ) ^ 2 * lt2Bpair N) := by
  set S : LT2Idx N → LT2Idx N → Set (Param N) := fun α α' =>
    {w | α.1 = α'.1 ∧ α ≠ α' ∧ lt2tG N ≤ |lt2Gm Λ b (symmDiff α.2.1 α'.2.1) (symmDiff α.2.2 α'.2.2) w|}
  have hS : ∀ α ∈ Fam, ∀ α' ∈ Fam, cubeM N (S α α') ≤ ENNReal.ofReal (lt2Bpair N) := by
    intro α hα α' hα'
    by_cases hc : α.1 = α'.1 ∧ α ≠ α'
    · exact (measure_mono fun w hw => hw.2.2).trans
        (lt2_pair_fail Λ (hFam α hα) (hFam α' hα') hc.1 hc.2 (hT α hα α' hα') hN)
    · have : S α α' = ∅ := by
        ext w; simp only [S, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hc ⟨h.1, h.2.1⟩
      rw [this, measure_empty]; exact zero_le
  have hsub : {w | ¬ lt2GoodGram Λ b Fam w} ⊆
      {w | 2 * sigN N ^ 2 < ∑ v ∈ lt2Om0 Λ b, lt2gNs (w v) ^ 2} ∪ ⋃ α ∈ Fam, ⋃ α' ∈ Fam, S α α' := by
    intro w hw
    simp only [Set.mem_setOf_eq, lt2GoodGram, not_and_or, not_le, not_forall] at hw
    rcases hw with h | ⟨α, hα, α', hα', hi, hne, h⟩
    · exact Or.inl h
    · refine Or.inr ?_
      simp only [Set.mem_iUnion]
      exact ⟨α, hα, α', hα', hi, hne, h.le⟩
  have hsq : 0 ≤ (Fam.card : ℝ) ^ 2 := by positivity
  calc cubeM N {w | ¬ lt2GoodGram Λ b Fam w}
      ≤ cubeM N {w | 2 * sigN N ^ 2 < ∑ v ∈ lt2Om0 Λ b, lt2gNs (w v) ^ 2} +
          cubeM N (⋃ α ∈ Fam, ⋃ α' ∈ Fam, S α α') := (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (lt2B2 N) + ∑ α ∈ Fam, ∑ α' ∈ Fam, cubeM N (S α α') :=
        add_le_add (lt2_S2_tail _) ((measure_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun α _ => measure_biUnion_finset_le _ _))
    _ ≤ ENNReal.ofReal (lt2B2 N) + ∑ _α ∈ Fam, ∑ _α' ∈ Fam, ENNReal.ofReal (lt2Bpair N) :=
        add_le_add le_rfl (Finset.sum_le_sum fun α hα => Finset.sum_le_sum fun α' hα' => hS α hα α' hα')
    _ = ENNReal.ofReal (lt2B2 N + (Fam.card : ℝ) ^ 2 * lt2Bpair N) := by
        rw [ENNReal.ofReal_add (show 0 ≤ lt2B2 N from (Real.exp_pos _).le) (mul_nonneg hsq lt2Bpair_nonneg),
          ENNReal.ofReal_mul hsq]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        ring

/-- **Adverse count for the `Ñ^b` statistics** (either parity class `b`). -/
theorem lt2_N0_count (Λ : Finset (Fin N)) (Fam : Finset (LT2Idx N))
    (hFam : ∀ α ∈ Fam, (α.2.1 ∩ Λ).card % 2 = 1)
    (hT : ∀ α ∈ Fam, ∀ α' ∈ Fam, α.2.1 = α'.2.1 → symmDiff α.2.2 α'.2.2 ≠ Λ)
    (hN : 8 * (1 / 2 : ℝ) ^ N ≤ lt2tG N) (hN0 : N ≠ 0) {κ : ℝ} (hκ : 0 < κ) (m : ℕ) (hm : 1 ≤ m) :
    cubeM N {w | m ≤ (Fam.filter fun α => κ * sigN N ≤ |lt2N0 Λ b w α|).card} ≤
      ENNReal.ofReal ((Fam.card.choose m) * 2 ^ m *
        (Real.exp (-min (3 * m * κ ^ 2 / (2 + m / (N : ℝ) ^ 4)) (κ * sigN N / lt2θ N)) +
          (lt2B2 N + (Fam.card : ℝ) ^ 2 * lt2Bpair N))) := by
  have hσ : 0 < sigN N := by unfold sigN; positivity
  have hθ : 0 < lt2θ N := Real.exp_pos _
  have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hfail : 0 ≤ lt2B2 N + (Fam.card : ℝ) ^ 2 * lt2Bpair N :=
    add_nonneg (Real.exp_pos _).le (mul_nonneg (by positivity) lt2Bpair_nonneg)
  refine lt2_count_union Fam (fun α w => lt2N0 Λ b w α) m (fun A hA hAc A' _ => ?_)
    (add_nonneg (Real.exp_pos _).le hfail)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := lt2_N0_tail (b := b) Λ Fam hFam hA A' (ε := m * (κ * sigN N)) (by positivity)
  refine h.trans ?_
  rw [ENNReal.ofReal_add (Real.exp_pos _).le hfail]
  refine add_le_add (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) (lt2_GoodGram_fail Λ Fam hFam hT hN)
  rw [hAc]
  have e1 : (m * (κ * sigN N)) ^ 2 / (4 * ((2 * sigN N ^ 2 * m + (m : ℝ) ^ 2 * (sigN N ^ 2 / (N : ℝ) ^ 4)) / 12)) =
      3 * m * κ ^ 2 / (2 + m / (N : ℝ) ^ 4) := by
    field_simp; ring
  have e2 : m * (κ * sigN N) / (2 * (lt2θ N * m / 2)) = κ * sigN N / lt2θ N := by
    field_simp
  rw [e1, e2]

end Census
end IIT
