/-
Census, B1 lemma LT2, module M6e-2: a good successful pair reaches `φ ≥ 3σ`.

Bridge to M1 (`lt2_pair_phi`): `U = 4 Num` (`U_eq_two_pow_mul_Num`), the margin `312σ` (`lt2_margin`) gives
`sameArgQ` with `Δ = 1248σ`; the effect probabilities are the clamped entries (oriented by `y_{s,col} ≥ 1/2`).
-/
import IIT.Census.B1LT2Margin
import IIT.Census.B1LT2Det
import IIT.Census.PairLower

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

lemma lt2_Num_pat (w : Param N) {a b : Fin N} (hab : a ≠ b) (t : State N) (i : Fin N) :
    Num w {a, b} {a, b} t i = Num w {a, b} {a, b} (lt2pat a b (t a) (t b)) i := by
  rw [prof_Num_full, prof_Num_full]
  exact Finset.sum_congr rfl fun v _ => by rw [lt2_merge_pat hab t v]

lemma lt2_prob_same (s : State N) (w : Param N) (r : State N) (j : Fin N) :
    (tpmOf (flipP s w)).prob j r (s j) = clamp01 (w r j) := by
  rw [prob_eq_clamp, flipP_invol s w]

lemma lt2_prob_not (s : State N) (w : Param N) (r : State N) (j : Fin N) :
    (tpmOf (flipP s w)).prob j r (!s j) = 1 - clamp01 (w r j) := by
  have hn := (tpmOf (flipP s w)).normalized j r
  have h := lt2_prob_same s w r j
  cases hs : s j <;> rw [hs] at h <;> simp only [Bool.not_false, Bool.not_true] <;> linarith

lemma lt2_rowE_eq (s : State N) {a b : Fin N} (hab : a ≠ b) (u v : Bool) :
    lt2rowE s a b u v = fun j => if j = a then u else if j = b then v else s j := by
  funext j
  unfold lt2rowE lt2pat merge
  by_cases hja : j = a
  · subst hja; simp
  · by_cases hjb : j = b
    · subst hjb; simp [hja]
    · simp [hja, hjb]

lemma lt2_flip_b_eq (s : State N) {a b : Fin N} (hab : a ≠ b) :
    flip s b = lt2rowE s a b (s a) (!s b) := by
  rw [lt2_rowE_eq s hab]; funext j
  unfold flip
  by_cases hja : j = a
  · subst hja; simp [Function.update_of_ne hab]
  · by_cases hjb : j = b
    · subst hjb; simp [hja]
    · simp [hja, hjb, Function.update_of_ne hjb]

lemma lt2_flip_a_eq (s : State N) {a b : Fin N} (hab : a ≠ b) :
    flip s a = lt2rowE s a b (!s a) (s b) := by
  rw [lt2_rowE_eq s hab]; funext j
  unfold flip
  by_cases hja : j = a
  · subst hja; simp
  · by_cases hjb : j = b
    · subst hjb; simp [hja, Function.update_of_ne hja]
    · simp [hja, hjb, Function.update_of_ne hja]

lemma lt2_flip_ab_eq (s : State N) {a b : Fin N} (hab : a ≠ b) :
    flip (flip s a) b = lt2rowE s a b (!s a) (!s b) := by
  rw [lt2_rowE_eq s hab]; funext j
  unfold flip
  by_cases hja : j = a
  · subst hja; simp [Function.update_of_ne hab]
  · by_cases hjb : j = b
    · subst hjb; simp [hja]
    · simp [hja, hjb, Function.update_of_ne hja, Function.update_of_ne hjb]

/-- The oriented effect bound from a success event. -/
lemma lt2_eff_bound (s : State N) (w : Param N) {a b : Fin N} {x ρ : ℝ} (c u v : Bool)
    (hE : lt2isEff s a b c u v) (hS : w ∈ lt2X s w a b x ρ (true, c, u, v)) :
    (tpmOf (flipP s w)).prob (lt2col a b c) (lt2rowE s a b u v)
      (if 1 / 2 ≤ clamp01 (w s (lt2col a b c)) then s (lt2col a b c) else !s (lt2col a b c)) ≤ ρ := by
  classical
  simp only [lt2X, ↓reduceIte, if_pos hE] at hS
  split_ifs with h
  · rw [if_pos h] at hS; rw [lt2_prob_same]; exact hS
  · rw [if_neg h] at hS; rw [lt2_prob_not]; simp only [Set.mem_setOf_eq] at hS; linarith

lemma lt2_eff_main (s : State N) (w : Param N) (j : Fin N) {γ : ℝ}
    (hj : γ ≤ |clamp01 (w s j) - 1 / 2|) :
    1 / 2 + γ ≤ (tpmOf (flipP s w)).prob j s (if 1 / 2 ≤ clamp01 (w s j) then s j else !s j) := by
  split_ifs with h
  · rw [lt2_prob_same]; rw [abs_of_nonneg (by linarith)] at hj; linarith
  · rw [lt2_prob_not]; rw [abs_of_neg (by linarith)] at hj; linarith

/-- **A good successful pair reaches `3σ`.** -/
theorem lt2_pair_good_phi (s : State N) (w : Param N) (hw : w ∈ openCube N) {a b : Fin N}
    (ha : a ∈ lt2D1 N) (hb : b ∈ lt2D2 N) {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hρ0 : 0 ≤ ρ)
    (hργ : 10 * ρ ≤ γ) (hρ1 : ρ ≤ 1 / 100) (hσ15 : sigN N ≤ 1 / 15) (hZ : Zs w ≤ 13)
    (hSp : ∑ v ∈ lt2Sp w, Pw w v < 156 * sigN N) (hEps : lt2Eps s w ≤ sigN N)
    (hVF : ∀ (j : Fin N) (β : Bool), sigN N ^ 2 / 16 ≤
      ∑ r ∈ (lt2H s w).filter (fun r => r ∈ agree {j} (fun _ => β)), lt2gNs (w r) ^ 2)
    (hF : ∀ (c u v : Bool), (u, v) ≠ (false, false) →
      |lt2NumNs (lt2Half s w) {a, b} (lt2pat a b false false) (lt2col a b c) -
        lt2NumNs (lt2Half s w) {a, b} (lt2pat a b u v) (lt2col a b c)| < 16 * lt2κ * sigN N + 2 * lt2Eps s w)
    (hea : γ ≤ |clamp01 (w s a) - 1 / 2|) (heb : γ ≤ |clamp01 (w s b) - 1 / 2|)
    (hsucc : lt2Succ s w a b 300000 ρ) :
    3 * sigN N ≤ phi (flipP s w) s {a, b} := by
  have hab := lt2_D1_ne_D2 ha hb
  have hσ : 0 < sigN N := by unfold sigN; positivity
  set z := flipP s w
  have hz : z ∈ openCube N := flipP_mem_openCube hw
  have hzw : flipP s z = w := flipP_invol s w
  have hcard : ({a, b} : Finset (Fin N)).card = 2 := card_pair hab
  have hU : ∀ i t, U z s {a, b} i t = 4 * Num w {a, b} {a, b} t i := fun i t => by
    rw [U_eq_two_pow_mul_Num hz, hzw, hcard]; norm_num
  have hsame : sameArgQ z s a b (1248 * sigN N) := by
    refine ⟨lt2pat a b false false, fun t ht => ?_⟩
    have huv : (t a, t b) ≠ (false, false) := by
      intro h
      simp only [Prod.mk.injEq] at h
      rcases ht with h' | h'
      · exact h' (by rw [h.1]; simp [lt2pat])
      · exact h' (by rw [h.2]; simp [lt2pat, Ne.symm hab])
    have m0 := lt2_margin s w ha hb hSp hEps hVF hF hsucc false (t a) (t b) huv
    have m1 := lt2_margin s w ha hb hSp hEps hVF hF hsucc true (t a) (t b) huv
    simp only [lt2col, Bool.false_eq_true, ↓reduceIte] at m0 m1
    rw [hU, hU, hU, hU, lt2_Num_pat w hab t a, lt2_Num_pat w hab t b]
    constructor <;> linarith
  have hZ' : ∑ v : State N, rowProd z s v ≤ 13 := by
    have : ∑ v : State N, rowProd z s v = Zs w := by
      unfold Zs; exact Finset.sum_congr rfl fun v _ => by rw [rowProd_eq_Pw, hzw]
    rw [this]; exact hZ
  -- the effect side
  have hEa1 : lt2isEff s a b false (s a) (!s b) := by simp [lt2isEff]
  have hEa2 : lt2isEff s a b false (!s a) (!s b) := by simp [lt2isEff]
  have hEb1 : lt2isEff s a b true (!s a) (s b) := by simp [lt2isEff]
  have hEb2 : lt2isEff s a b true (!s a) (!s b) := by simp [lt2isEff]
  have p1 := lt2_eff_bound s w false (s a) (!s b) hEa1 (hsucc _)
  have p2 := lt2_eff_bound s w false (!s a) (!s b) hEa2 (hsucc _)
  have p3 := lt2_eff_bound s w true (!s a) (s b) hEb1 (hsucc _)
  have p4 := lt2_eff_bound s w true (!s a) (!s b) hEb2 (hsucc _)
  simp only [lt2col, Bool.false_eq_true, ↓reduceIte] at p1 p2 p3 p4
  rw [← lt2_flip_b_eq s hab] at p1
  rw [← lt2_flip_ab_eq s hab] at p2 p4
  rw [← lt2_flip_a_eq s hab] at p3
  have h := lt2_pair_phi hz s hab (by positivity) hsame hZ' _ _ hγ0 hγ2 hρ0 hργ hρ1
    (lt2_eff_main s w a hea) (lt2_eff_main s w b heb) p1 p2 p3 p4
  have : min (1 / 5) (1248 * sigN N / 416) = 3 * sigN N := by
    rw [show 1248 * sigN N / 416 = 3 * sigN N by ring]; exact min_eq_right (by linarith)
  rw [this] at h; exact h

end Census
end IIT
