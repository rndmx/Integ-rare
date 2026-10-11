/-
Census, B1 lemma LT2 at a general level `L ≥ 1` (needed by LTBetaHi on `σ ≤ β < Lσ`): the margin and the pair bound.
-/
import IIT.Census.B1LT2Final

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

lemma lt2_Pw_ltL {w : Param N} {L : ℝ} (hL : 0 ≤ L) (hβ : betaW w < L * sigN N) (hZ0 : 0 < Zs w) (hZ : Zs w ≤ 13) (r : State N) :
    Pw w r < 13 * L * sigN N := by
  have h := Pw_le_tcRow w r
  have hb : Pw w (tcRow w) < L * sigN N * Zs w := by
    unfold betaW at hβ; rwa [div_lt_iff₀ hZ0] at hβ
  have hσ : 0 < sigN N := by unfold sigN; positivity
  have := mul_le_mul_of_nonneg_left hZ (mul_nonneg hL hσ.le)
  nlinarith

/-- **The margin of a good successful pair.** -/
theorem lt2_marginL (s : State N) (w : Param N) {a b : Fin N} (ha : a ∈ lt2D1 N) (hb : b ∈ lt2D2 N) {ρ x L : ℝ} (hx : 7 * (40004 + 468 * L) ≤ x) (hL : 1 ≤ L)
    (hSp : ∑ v ∈ lt2Sp w, Pw w v < 156 * L * sigN N) (hEps : lt2Eps s w ≤ sigN N)
    (hVF : ∀ (j : Fin N) (β : Bool), sigN N ^ 2 / 16 ≤
      ∑ r ∈ (lt2H s w).filter (fun r => r ∈ agree {j} (fun _ => β)), lt2gNs (w r) ^ 2)
    (hF : ∀ (c u v : Bool), (u, v) ≠ (false, false) →
      |lt2NumNs (lt2Half s w) {a, b} (lt2pat a b false false) (lt2col a b c) -
        lt2NumNs (lt2Half s w) {a, b} (lt2pat a b u v) (lt2col a b c)| < 16 * lt2κ * sigN N + 2 * lt2Eps s w)
    (hsucc : lt2Succ s w a b x ρ) (c u v : Bool) (huv : (u, v) ≠ (false, false)) :
    Num w {a, b} {a, b} (lt2pat a b u v) (lt2col a b c) + 312 * L * sigN N ≤
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
  have hx0 : 0 ≤ x := by nlinarith
  have k0 := mul_le_mul_of_nonneg_left hsd0 hx0
  have k1 := mul_le_mul_of_nonneg_left hsd1 hx0
  have k2 : 7 * (40004 + 468 * L) * sigN N ≤ x * sigN N := mul_le_mul_of_nonneg_right hx hσ.le
  nlinarith

/-- **A good successful pair reaches `3σ`.** -/
theorem lt2_pair_good_phiL (s : State N) (w : Param N) (hw : w ∈ openCube N) {a b : Fin N}
    (ha : a ∈ lt2D1 N) (hb : b ∈ lt2D2 N) {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hρ0 : 0 ≤ ρ)
    (hργ : 10 * ρ ≤ γ) (hρ1 : ρ ≤ 1 / 100) {x L : ℝ} (hx : 7 * (40004 + 468 * L) ≤ x) (hL : 1 ≤ L)
    (hσ15 : 3 * L * sigN N ≤ 1 / 5) (hZ : Zs w ≤ 13)
    (hSp : ∑ v ∈ lt2Sp w, Pw w v < 156 * L * sigN N) (hEps : lt2Eps s w ≤ sigN N)
    (hVF : ∀ (j : Fin N) (β : Bool), sigN N ^ 2 / 16 ≤
      ∑ r ∈ (lt2H s w).filter (fun r => r ∈ agree {j} (fun _ => β)), lt2gNs (w r) ^ 2)
    (hF : ∀ (c u v : Bool), (u, v) ≠ (false, false) →
      |lt2NumNs (lt2Half s w) {a, b} (lt2pat a b false false) (lt2col a b c) -
        lt2NumNs (lt2Half s w) {a, b} (lt2pat a b u v) (lt2col a b c)| < 16 * lt2κ * sigN N + 2 * lt2Eps s w)
    (hea : γ ≤ |clamp01 (w s a) - 1 / 2|) (heb : γ ≤ |clamp01 (w s b) - 1 / 2|)
    (hsucc : lt2Succ s w a b x ρ) :
    3 * L * sigN N ≤ phi (flipP s w) s {a, b} := by
  have hab := lt2_D1_ne_D2 ha hb
  have hσ : 0 < sigN N := by unfold sigN; positivity
  set z := flipP s w
  have hz : z ∈ openCube N := flipP_mem_openCube hw
  have hzw : flipP s z = w := flipP_invol s w
  have hcard : ({a, b} : Finset (Fin N)).card = 2 := card_pair hab
  have hU : ∀ i t, U z s {a, b} i t = 4 * Num w {a, b} {a, b} t i := fun i t => by
    rw [U_eq_two_pow_mul_Num hz, hzw, hcard]; norm_num
  have hsame : sameArgQ z s a b (1248 * L * sigN N) := by
    refine ⟨lt2pat a b false false, fun t ht => ?_⟩
    have huv : (t a, t b) ≠ (false, false) := by
      intro h
      simp only [Prod.mk.injEq] at h
      rcases ht with h' | h'
      · exact h' (by rw [h.1]; simp [lt2pat])
      · exact h' (by rw [h.2]; simp [lt2pat, Ne.symm hab])
    have m0 := lt2_marginL s w ha hb hx hL hSp hEps hVF hF hsucc false (t a) (t b) huv
    have m1 := lt2_marginL s w ha hb hx hL hSp hEps hVF hF hsucc true (t a) (t b) huv
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
  have h := lt2_pair_phi hz s hab (by have := hσ; nlinarith) hsame hZ' _ _ hγ0 hγ2 hρ0 hργ hρ1
    (lt2_eff_main s w a hea) (lt2_eff_main s w b heb) p1 p2 p3 p4
  have : min (1 / 5) (1248 * L * sigN N / 416) = 3 * L * sigN N := by
    rw [show 1248 * L * sigN N / 416 = 3 * L * sigN N by ring]; exact min_eq_right (by linarith)
  rw [this] at h; exact h

end Census
end IIT
