/-
Census, B1 lemma LT2, module M6e-1: the deterministic margin of a good successful pair.

`Num = NumNs + Spec` (`Spec` = the special rows, `∈ [0, Σ_{Sp} P)`), `NumNs(w) = F + Π + E` (`lt2_pert`), `Π` = the
private sum of the success events. For a good pair (`|F-diff| < 16κσ + 2ε`, `ε ≤ σ`, `Σ_{Sp} P < 156σ`), a successful
pair has `Num(t₀) - Num(t) ≥ 312σ` for every other pattern `t`, in both columns (`x = 300000`).
-/
import IIT.Census.B1LT2AdvTotal

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- `Num = NumNs + Spec`. -/
lemma lt2_Num_split (w : Param N) (S : Finset (Fin N)) (t : State N) (i : Fin N) :
    Num w S S t i = lt2NumNs w S t i + ∑ v ∈ lt2Sp w, clamp01 (w (merge S t v) i) * Pw w v := by
  classical
  have hP : ∀ v, clamp01 (w (merge S t v) i) * Pw w v = clamp01 (w (merge S t v) i) * lt2gNs (w v) +
      (if v ∈ lt2Sp w then clamp01 (w (merge S t v) i) * Pw w v else 0) := by
    intro v
    have hmem : v ∈ lt2Sp w ↔ XW w v ≤ lt2x1 * N := by simp [lt2Sp]
    by_cases hv : v ∈ lt2Sp w
    · have h := hmem.1 hv
      have hg : lt2gNs (w v) = 0 := by
        unfold lt2gNs; rw [if_neg]; unfold XW at h; linarith
      rw [if_pos hv, hg]; ring
    · have h : lt2x1 * N < XW w v := lt_of_not_ge fun h' => hv (hmem.2 h')
      have hg : lt2gNs (w v) = Pw w v := by
        unfold lt2gNs Pw; rw [if_pos]; unfold XW at h; exact h
      rw [if_neg hv, hg]; ring
  rw [prof_Num_full, lt2NumNs, Finset.sum_congr rfl fun v _ => hP v, Finset.sum_add_distrib,
    Finset.sum_ite_mem, Finset.univ_inter]

lemma lt2_Spec_bounds (w : Param N) (S : Finset (Fin N)) (t : State N) (i : Fin N) :
    0 ≤ ∑ v ∈ lt2Sp w, clamp01 (w (merge S t v) i) * Pw w v ∧
      ∑ v ∈ lt2Sp w, clamp01 (w (merge S t v) i) * Pw w v ≤ ∑ v ∈ lt2Sp w, Pw w v := by
  have hP : ∀ v, 0 ≤ Pw w v := fun v => Finset.prod_nonneg fun j _ => clamp01_nonneg _
  refine ⟨Finset.sum_nonneg fun v _ => mul_nonneg (clamp01_nonneg _) (hP v),
    Finset.sum_le_sum fun v _ => ?_⟩
  calc clamp01 (w (merge S t v) i) * Pw w v ≤ 1 * Pw w v :=
        mul_le_mul_of_nonneg_right (clamp01_le_one _) (hP v)
    _ = Pw w v := one_mul _

/-- The private sum of the success events is the private sum of the decomposition. -/
lemma lt2_Sres_eq_Pi (s : State N) (w : Param N) {a b : Fin N} (ha : a ∈ lt2D1 N) (hb : b ∈ lt2D2 N)
    (c u v : Bool) :
    lt2Pi s w {a, b} (lt2pat a b u v) (lt2col a b c) = lt2Sres s w a b c u v w := by
  rw [← lt2_pair_set a b c, lt2Pi_eq_PiE s w _ (lt2_orient ha hb c)]
  unfold lt2PiE lt2Sres lt2Hf
  rw [lt2_pair_set]

lemma lt2_sqrt192 : Real.sqrt 192 ≤ 14 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- The standard deviation of a private sum is at least `σ/14`, by the variance floor. -/
lemma lt2_sd_ge (s : State N) (w : Param N) {a b : Fin N} (c u v : Bool)
    (hVF : ∀ (j : Fin N) (β : Bool), sigN N ^ 2 / 16 ≤
      ∑ r ∈ (lt2H s w).filter (fun r => r ∈ agree {j} (fun _ => β)), lt2gNs (w r) ^ 2) :
    sigN N / 14 ≤ lt2sd s w a b c u v := by
  classical
  have hσ : 0 < sigN N := by unfold sigN; positivity
  set j := lt2oth a b c
  set β := !(lt2pat a b u v j)
  have hset : lt2Hf s w a b c u v = (lt2H s w).filter (fun r => r ∈ agree {j} (fun _ => β)) := by
    unfold lt2Hf
    refine Finset.filter_congr fun r _ => ?_
    simp only [agree, mem_filter, mem_univ, true_and, mem_singleton, forall_eq, β]
    cases r j <;> cases lt2pat a b u v j <;> simp
  have h := hVF j β
  unfold lt2sd
  rw [hset, ← Finset.sum_div]
  have h192 : sigN N ^ 2 / 192 ≤ (∑ r ∈ (lt2H s w).filter (fun r => r ∈ agree {j} (fun _ => β)),
      lt2gNs (w r) ^ 2) / 12 := by linarith
  calc sigN N / 14 ≤ sigN N / Real.sqrt 192 :=
        div_le_div_of_nonneg_left hσ.le (by positivity) lt2_sqrt192
    _ = Real.sqrt (sigN N ^ 2 / 192) := by
        rw [Real.sqrt_div' _ (by norm_num), Real.sqrt_sq hσ.le]
    _ ≤ _ := Real.sqrt_le_sqrt h192

/-- **The margin of a good successful pair.** -/
theorem lt2_margin (s : State N) (w : Param N) {a b : Fin N} (ha : a ∈ lt2D1 N) (hb : b ∈ lt2D2 N) {ρ : ℝ}
    (hSp : ∑ v ∈ lt2Sp w, Pw w v < 156 * sigN N) (hEps : lt2Eps s w ≤ sigN N)
    (hVF : ∀ (j : Fin N) (β : Bool), sigN N ^ 2 / 16 ≤
      ∑ r ∈ (lt2H s w).filter (fun r => r ∈ agree {j} (fun _ => β)), lt2gNs (w r) ^ 2)
    (hF : ∀ (c u v : Bool), (u, v) ≠ (false, false) →
      |lt2NumNs (lt2Half s w) {a, b} (lt2pat a b false false) (lt2col a b c) -
        lt2NumNs (lt2Half s w) {a, b} (lt2pat a b u v) (lt2col a b c)| < 16 * lt2κ * sigN N + 2 * lt2Eps s w)
    (hsucc : lt2Succ s w a b 300000 ρ) (c u v : Bool) (huv : (u, v) ≠ (false, false)) :
    Num w {a, b} {a, b} (lt2pat a b u v) (lt2col a b c) + 312 * sigN N ≤
      Num w {a, b} {a, b} (lt2pat a b false false) (lt2col a b c) := by
  have hσ : 0 < sigN N := by unfold sigN; positivity
  have hcard : ({a, b} : Finset (Fin N)).card ≤ 2 := Finset.card_insert_le _ _
  set i := lt2col a b c
  set t0 := lt2pat a b false false
  set t := lt2pat a b u v
  -- the special rows
  have hs0 := lt2_Spec_bounds w {a, b} t0 i
  have hs1 := lt2_Spec_bounds w {a, b} t i
  -- the decomposition
  have hp0 := lt2_pert s w hcard t0 i
  have hp1 := lt2_pert s w hcard t i
  rw [lt2_Sres_eq_Pi s w ha hb] at hp0 hp1
  rw [abs_le] at hp0 hp1
  -- the success events
  have hS0 := hsucc (false, c, false, false)
  have hS1 := hsucc (false, c, u, v)
  simp only [lt2X, Bool.false_eq_true, ↓reduceIte, and_self, Set.mem_setOf_eq] at hS0
  have huv' : ¬ (u = false ∧ v = false) := fun h => huv (by rw [h.1, h.2])
  simp only [lt2X, Bool.false_eq_true, ↓reduceIte, if_neg huv', Set.mem_setOf_eq] at hS1
  have hsd0 := lt2_sd_ge s w (a := a) (b := b) c false false hVF
  have hsd1 := lt2_sd_ge s w (a := a) (b := b) c u v hVF
  have hF' := hF c u v huv
  rw [abs_lt] at hF'
  rw [lt2_Num_split, lt2_Num_split]
  unfold lt2κ at hF'
  nlinarith

end Census
end IIT
