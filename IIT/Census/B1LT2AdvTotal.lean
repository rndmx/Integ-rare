/-
Census, B1 lemma LT2, module M6d-4: few adverse pairs.

`lt2_adv_total`: eventually, `P(#{(a,b) ∈ D₁×D₂ : some valid kind has |stat| ≥ κσ} ≥ m²/16) ≤ e^{-2N}`.
Thresholds `m₃ = m/12288 + 1` (units), `m₁ = m₃ m` (pairs); 192 kinds, each `≤ 2e^{-3N}`.
-/
import IIT.Census.B1LT2KindEv

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- The adverse pairs. -/
noncomputable def lt2AdvPairs (w : Param N) : Finset (Fin N × Fin N) := by
  classical exact (lt2D1 N ×ˢ lt2D2 N).filter fun p =>
    ∃ k : LT2Kind, lt2kValid k ∧ lt2κ * sigN N ≤ |lt2stat w p.1 p.2 k|

/-- The event of a kind. -/
noncomputable def lt2KEv (a0 b0 : Fin N) (m3 : ℕ) (k : LT2Kind) : Set (Param N) := by
  classical exact
  if ¬ lt2bIn k then {w | m3 ≤ ((lt2D1 N).filter fun a => lt2κ * sigN N ≤ |lt2stat w a b0 k|).card}
  else if ¬ lt2aIn k then {w | m3 ≤ ((lt2D2 N).filter fun b => lt2κ * sigN N ≤ |lt2stat w a0 b k|).card}
  else {w | m3 * lt2m N ≤ ((lt2D1 N ×ˢ lt2D2 N).filter fun p => lt2κ * sigN N ≤ |lt2stat w p.1 p.2 k|).card}

/-- Deterministic: outside all kind events, few adverse pairs. -/
lemma lt2_adv_det (w : Param N) {a0 b0 : Fin N} (ha0 : a0 ∈ lt2D1 N) (hb0 : b0 ∈ lt2D2 N) (m3 : ℕ)
    (hw : ∀ k, lt2kValid k → w ∉ lt2KEv a0 b0 m3 k) :
    (lt2AdvPairs w).card ≤ 192 * (m3 * lt2m N) := by
  classical
  set m := lt2m N
  have hD1 := lt2_card_D1 (N := N)
  have hD2 := lt2_card_D2 (N := N)
  -- per kind
  have hper : ∀ k, lt2kValid k →
      ((lt2D1 N ×ˢ lt2D2 N).filter fun p => lt2κ * sigN N ≤ |lt2stat w p.1 p.2 k|).card ≤ m3 * m := by
    intro k hk
    have hnot := hw k hk
    unfold lt2KEv at hnot
    by_cases hB : lt2bIn k
    · by_cases hA : lt2aIn k
      · simp only [hB, hA, not_true_eq_false, ↓reduceIte, Set.mem_setOf_eq, not_le] at hnot
        exact hnot.le
      · simp only [hB, hA, not_true_eq_false, not_false_eq_true, ↓reduceIte, Set.mem_setOf_eq, not_le] at hnot
        have e : ((lt2D1 N ×ˢ lt2D2 N).filter fun p => lt2κ * sigN N ≤ |lt2stat w p.1 p.2 k|) =
            lt2D1 N ×ˢ ((lt2D2 N).filter fun b => lt2κ * sigN N ≤ |lt2stat w a0 b k|) := by
          ext ⟨a, b⟩
          simp only [mem_filter, mem_product]
          rw [lt2_stat_unitB w a a0 b hA]; tauto
        rw [e, card_product, hD1, mul_comm]
        exact Nat.mul_le_mul_right _ hnot.le
    · simp only [hB, not_false_eq_true, ↓reduceIte, Set.mem_setOf_eq, not_le] at hnot
      have e : ((lt2D1 N ×ˢ lt2D2 N).filter fun p => lt2κ * sigN N ≤ |lt2stat w p.1 p.2 k|) =
          ((lt2D1 N).filter fun a => lt2κ * sigN N ≤ |lt2stat w a b0 k|) ×ˢ lt2D2 N := by
        ext ⟨a, b⟩
        simp only [mem_filter, mem_product]
        rw [lt2_stat_unitA w a b b0 hB]; tauto
      rw [e, card_product, hD2]
      exact Nat.mul_le_mul_right _ hnot.le
  -- sum over kinds
  have hsub : lt2AdvPairs w ⊆ (univ.filter lt2kValid).biUnion fun k =>
      (lt2D1 N ×ˢ lt2D2 N).filter fun p => lt2κ * sigN N ≤ |lt2stat w p.1 p.2 k| := by
    intro p hp
    unfold lt2AdvPairs at hp
    obtain ⟨hpD, k, hk, hle⟩ := mem_filter.1 hp
    exact mem_biUnion.2 ⟨k, mem_filter.2 ⟨mem_univ _, hk⟩, mem_filter.2 ⟨hpD, hle⟩⟩
  calc (lt2AdvPairs w).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ univ.filter lt2kValid, ((lt2D1 N ×ˢ lt2D2 N).filter
          fun p => lt2κ * sigN N ≤ |lt2stat w p.1 p.2 k|).card := Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ univ.filter lt2kValid, m3 * m :=
        Finset.sum_le_sum fun k hk => hper k (mem_filter.1 hk).2
    _ ≤ ∑ _k : LT2Kind, m3 * m := Finset.sum_le_sum_of_subset (filter_subset _ _)
    _ = 192 * (m3 * m) := by simp

/-- **Few adverse pairs.** -/
theorem lt2_adv_total : ∀ᶠ N : ℕ in atTop,
    cubeM N {w | ((lt2m N : ℝ)) ^ 2 / 16 ≤ ((lt2AdvPairs w).card : ℝ)} ≤ ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
  classical
  filter_upwards [lt2_ev_kind, lt2_extra_small, eventually_ge_atTop 90000] with N hev hextra hN
  obtain ⟨hev1, hev2, hev3⟩ := hev
  set m := lt2m N with hmdef
  set m3 := m / 12288 + 1 with hm3def
  have hm : 4500 ≤ m := by rw [hmdef]; unfold lt2m; omega
  have hmN : 20 * m ≤ N ∧ N < 20 * m + 20 := by rw [hmdef]; unfold lt2m; omega
  have hm3a : m < 12288 * m3 := by rw [hm3def]; omega
  have hm3b : m3 ≤ m := by rw [hm3def]; omega
  have hm31 : 1 ≤ m3 := by rw [hm3def]; omega
  have hNm3 : N ≤ 491520 * m3 := by omega
  have hmN2 : m ≤ N := by omega
  -- base points
  have hND1 : N - 2 * m < N := by omega
  set a0 : Fin N := ⟨N - 2 * m, hND1⟩
  set b0 : Fin N := ⟨N - 1, by omega⟩
  have ha0 : a0 ∈ lt2D1 N := by
    simp only [lt2D1, mem_filter, mem_univ, true_and, a0]; rw [← hmdef]; omega
  have hb0 : b0 ∈ lt2D2 N := by
    simp only [lt2D2, mem_filter, mem_univ, true_and, b0]; rw [← hmdef]; omega
  have hD1 := lt2_card_D1 (N := N)
  have hD2 := lt2_card_D2 (N := N)
  have hNr : (1 : ℝ) ≤ N := hev3
  -- real forms of the threshold facts
  have rN : (N : ℝ) / 491520 ≤ (m3 : ℝ) := by
    rw [div_le_iff₀ (by norm_num)]; exact_mod_cast (by omega : N ≤ m3 * 491520)
  have rN' : (N : ℝ) / 491520 ≤ ((m3 * m : ℕ) : ℝ) := by
    refine rN.trans ?_; exact_mod_cast (Nat.le_mul_of_pos_right m3 (by omega))
  have hsq : ∀ x : ℕ, x ≤ N → (x : ℝ) ≤ (N : ℝ) ^ 2 := fun x hx => by
    have : (x : ℝ) ≤ N := by exact_mod_cast hx
    nlinarith
  have hsqN : ∀ x : ℕ, x ≤ N → x ≤ N ^ 2 := fun x hx => hx.trans (Nat.le_self_pow (by norm_num) N)
  -- each kind event is small
  have hK : ∀ k, lt2kValid k → cubeM N (lt2KEv a0 b0 m3 k) ≤ ENNReal.ofReal (2 * Real.exp (-(3 * (N : ℝ)))) := by
    intro k hk
    unfold lt2KEv
    by_cases hB : lt2bIn k
    · by_cases hA : lt2aIn k
      · simp only [hB, hA, not_true_eq_false, ↓reduceIte]
        have H : LT2KindHyp N (m3 * m) (lt2D1 N ×ˢ lt2D2 N).card := by
          rw [card_product, hD1, hD2]
          exact ⟨hev1, hev2, hev3, hextra, by omega, Nat.one_le_iff_ne_zero.2 (by positivity),
            by exact_mod_cast (show m * m ≤ 12288 * (m3 * m) by nlinarith), rN',
            by exact_mod_cast (show m3 * m ≤ N ^ 2 by rw [sq]; exact Nat.mul_le_mul (hm3b.trans hmN2) hmN2),
            by rw [sq]; exact Nat.mul_le_mul hmN2 hmN2⟩
        refine lt2_kind_prob (lt2D1 N ×ˢ lt2D2 N) id (fun p hp => mem_product.1 hp) hk ?_ H
        intro p hp p' hp' h
        have hp1 := mem_product.1 hp; have hp1' := mem_product.1 hp'
        have h1 := (h p.1).1 (Or.inl ⟨rfl, hA⟩)
        have h2 := (h p.2).1 (Or.inr ⟨rfl, hB⟩)
        simp only [id] at h1 h2
        refine Prod.ext ?_ ?_
        · rcases h1 with ⟨h, -⟩ | ⟨h, -⟩
          · exact h
          · exact absurd (h ▸ hp1'.2) fun h' => lt2_D_disj hp1.1 h'
        · rcases h2 with ⟨h, -⟩ | ⟨h, -⟩
          · exact absurd (h ▸ hp1'.1) fun h' => lt2_D_disj h' hp1.2
          · exact h
      · simp only [hB, hA, not_true_eq_false, not_false_eq_true, ↓reduceIte]
        have H : LT2KindHyp N m3 (lt2D2 N).card := by
          rw [hD2]
          exact ⟨hev1, hev2, hev3, hextra, by omega, hm31, by exact_mod_cast hm3a.le, rN,
            hsq _ (by omega), hsqN _ hmN2⟩
        exact lt2_kind_prob (lt2D2 N) (fun b => (a0, b)) (fun b hb => ⟨ha0, hb⟩) hk
          (fun b _ b' _ h => by
            have := (h b).1 (Or.inr ⟨rfl, hB⟩)
            rcases this with ⟨_, h'⟩ | ⟨h', _⟩
            · exact absurd h' hA
            · exact h') H
    · simp only [hB, not_false_eq_true, ↓reduceIte]
      have hA : lt2aIn k := (lt2_valid_ab hk).resolve_right hB
      have H : LT2KindHyp N m3 (lt2D1 N).card := by
        rw [hD1]
        exact ⟨hev1, hev2, hev3, hextra, by omega, hm31, by exact_mod_cast hm3a.le, rN,
          hsq _ (by omega), hsqN _ hmN2⟩
      exact lt2_kind_prob (lt2D1 N) (fun a => (a, b0)) (fun a ha => ⟨ha, hb0⟩) hk
        (fun a _ a' _ h => by
          have := (h a).1 (Or.inl ⟨rfl, hA⟩)
          rcases this with ⟨h', _⟩ | ⟨_, h'⟩
          · exact h'
          · exact absurd h' hB) H
  -- the inclusion
  have hsub : {w : Param N | ((lt2m N : ℝ)) ^ 2 / 16 ≤ ((lt2AdvPairs w).card : ℝ)} ⊆
      ⋃ k ∈ univ.filter lt2kValid, lt2KEv a0 b0 m3 k := by
    intro w hw
    by_contra hnot
    simp only [Set.mem_iUnion, mem_filter, mem_univ, true_and, not_exists] at hnot
    have hdet := lt2_adv_det w ha0 hb0 m3 fun k hk hwk => hnot k hk hwk
    have h1 : ((lt2AdvPairs w).card : ℝ) ≤ 192 * ((m3 : ℝ) * m) := by exact_mod_cast hdet
    have h2 : (192 : ℝ) * ((m3 : ℝ) * m) < (m : ℝ) ^ 2 / 16 := by
      have h3 : (12288 : ℝ) * ((m3 : ℝ) - 1) ≤ m := by
        have : 12288 * (m3 - 1) ≤ m := by rw [hm3def]; omega
        have h4 : ((m3 - 1 : ℕ) : ℝ) = (m3 : ℝ) - 1 := by push_cast [Nat.cast_sub hm31]; ring
        rw [← h4]; exact_mod_cast this
      have hm' : (4500 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith
    simp only [Set.mem_setOf_eq] at hw
    rw [← hmdef] at hw
    linarith
  calc cubeM N {w | ((lt2m N : ℝ)) ^ 2 / 16 ≤ ((lt2AdvPairs w).card : ℝ)}
      ≤ ∑ k ∈ univ.filter lt2kValid, cubeM N (lt2KEv a0 b0 m3 k) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _k ∈ univ.filter lt2kValid, ENNReal.ofReal (2 * Real.exp (-(3 * (N : ℝ)))) :=
        Finset.sum_le_sum fun k hk => hK k (mem_filter.1 hk).2
    _ ≤ ∑ _k : LT2Kind, ENNReal.ofReal (2 * Real.exp (-(3 * (N : ℝ)))) :=
        Finset.sum_le_sum_of_subset (filter_subset _ _)
    _ = ENNReal.ofReal (192 * (2 * Real.exp (-(3 * (N : ℝ))))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by norm_num)]
        simp
    _ ≤ ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : (384 : ℝ) ≤ Real.exp N := by
          have := Real.add_one_le_exp (N : ℝ)
          have : (90000 : ℝ) ≤ N := by exact_mod_cast hN
          linarith
        have h2 : Real.exp N * Real.exp (-(3 * (N : ℝ))) = Real.exp (-(2 * (N : ℝ))) := by
          rw [← Real.exp_add]; ring_nf
        have h3 := Real.exp_pos (-(3 * (N : ℝ)))
        nlinarith

end Census
end IIT
