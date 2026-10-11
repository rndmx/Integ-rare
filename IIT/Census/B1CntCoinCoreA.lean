/-
Census, B1, W14 work package WP5 (part 9): the deterministic half of the coin (W5 Lemma E2'):
the events `E_k^b` (fresh sums only) lie in `Core^{(k)}_K(2κ0)`.

`E_k^b`: `a λ1 ≤ ±S_k < a λ3`, `|S_c| < a λ2` for every column `c ≠ k` (both orientations), and
`±T_j(k) < a θ` for every `j ∈ M`, where `S_c` is the fresh sum of column `c` on `C_0 = agree M s` and
`T_j(k)` the fresh sum of column `k` on `C_j = agree M (s^j)`; the fixed rows move each coin variable by at
most `κ0/2`.

No `sorry`.
-/
import IIT.Census.B1CntCoinCNum2

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-- The algebra of `E_k^b ⊆ Core^{(k)}_K(2κ0)`, for the coin `k` (orientation `σ = ±1`). -/
lemma w5_core_alg {a κ0 κN A0 x2 m' f S σ : ℝ} (ha : 0 < a) (hκ0 : 0 < κ0) (hκN : 4 * κ0 ≤ κN)
    (hA0 : 0 ≤ A0) (hm' : 7 / 8 ≤ m') (hm1 : m' ≤ 1) (hσ : σ = 1 ∨ σ = -1)
    (hf : |f * a - S| ≤ κ0 * a / 2)
    (h1 : a * (A0 + 2 * κN + 3 * κ0) ≤ σ * S) (h3 : σ * S < a * (x2 - 3 * κ0)) :
    0 < σ * f ∧ A0 + 2 * κN + 2 * κ0 < |f| ∧ |f| < x2 - 2 * κ0 ∧
      ∀ h T : ℝ, |h * a - T| ≤ κ0 * a / 2 → σ * T < a * (m' * A0) →
        sgnMul f h < m' * |f| - κN - 2 * κ0 := by
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hσabs : |σ| = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  -- `g = σ f`
  have hg : |σ * f * a - σ * S| ≤ κ0 * a / 2 := by
    rw [show σ * f * a - σ * S = σ * (f * a - S) by ring, abs_mul, hσabs, one_mul]; exact hf
  have hg' := abs_le.1 hg
  have hglo : A0 + 2 * κN + 5 / 2 * κ0 ≤ σ * f := by
    have : a * (A0 + 2 * κN + 5 / 2 * κ0) ≤ a * (σ * f) := by nlinarith
    exact le_of_mul_le_mul_left this ha
  have hghi : σ * f < x2 - 5 / 2 * κ0 := by
    have : a * (σ * f) < a * (x2 - 5 / 2 * κ0) := by nlinarith
    exact lt_of_mul_lt_mul_left this ha.le
  have hgpos : 0 < σ * f := by linarith
  have habs : |f| = σ * f := by
    rw [← abs_of_pos hgpos, abs_mul, hσabs, one_mul]
  refine ⟨hgpos, by rw [habs]; linarith, by rw [habs]; linarith, ?_⟩
  intro h T hh hT
  have hsg : sgnMul f h = σ * h := by
    unfold sgnMul
    rcases hσ with hs | hs
    · rw [hs] at hgpos; rw [if_pos (by linarith), hs, one_mul]
    · rw [hs] at hgpos; rw [if_neg (by linarith), hs]; ring
  rw [hsg, habs]
  have hh' : |σ * h * a - σ * T| ≤ κ0 * a / 2 := by
    rw [show σ * h * a - σ * T = σ * (h * a - T) by ring, abs_mul, hσabs, one_mul]; exact hh
  have hh'' := abs_le.1 hh'
  have hσh : σ * h < m' * A0 + κ0 / 2 := by
    have : a * (σ * h) < a * (m' * A0 + κ0 / 2) := by nlinarith
    exact lt_of_mul_lt_mul_left this ha.le
  have : m' * (A0 + 2 * κN + 5 / 2 * κ0) ≤ m' * (σ * f) :=
    mul_le_mul_of_nonneg_left hglo (by linarith)
  nlinarith

/-- The orientation of a coin event: `w5S … b = σ · w5S … (w5or f k)`, `σ = ±1`. -/
lemma w5_sign_choice {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (k : Fin N) (b : Bool) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ (R : Finset (State N)) (w : Param N),
      w5S (sensRows s r0) R k b w = σ * w5S (sensRows s r0) R k (w5or f k) w := by
  by_cases hb : b = w5or f k
  · exact ⟨1, Or.inl rfl, fun R w => by rw [hb, one_mul]⟩
  · have : b = !(w5or f k) := by
      cases b <;> cases h : w5or f k <;> simp_all
    exact ⟨-1, Or.inr rfl, fun R w => by rw [this, w5S_not]; ring⟩

lemma w5_C0_Cj_disj (s : State N) (K : Finset (Fin N)) {j : Fin N} (hj : j ∈ univ \ K) :
    Disjoint (agree (univ \ K) s) (agree (univ \ K) (flipAt j s)) := by
  rw [Finset.disjoint_left]
  intro r h1 h2
  have e1 := (mem_agree.1 h1) j hj
  have e2 := (mem_agree.1 h2) j hj
  rw [e1] at e2
  unfold flipAt at e2
  simp at e2

lemma w5_kap0_pos (hd : 1 ≤ dX N) : 0 < kap0 N := by
  unfold kap0
  have : (0 : ℝ) < dX N := by exact_mod_cast hd
  positivity

lemma w5_kapN_ge (N : ℕ) : 4 * kap0 N ≤ kapN N := by
  unfold kapN
  have := Real.log_natCast_nonneg N
  have := w5_epsN_nonneg N
  have : 0 ≤ 6 * Real.log N / 2 ^ dX N := by positivity
  linarith

/-- **`E_k^b ⊆ Core^{(k)}_K(2κ0)`.** -/
lemma w5_E_core {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (K : Finset (Fin N)) (k : Fin N)
    (b : Bool) (w : Param N) (hfar : N ≤ 3 * ham r0 s) (hdM : N - (univ \ K).card = dX N)
    (hd2 : 2 ≤ dX N) (hD : 3 * dX N + 19 ≤ N) (hm16 : 16 ≤ mX N)
    (h1 : 2 ^ dX N * w5lam1 N ≤ w5S (sensRows s r0) (agree (univ \ K) s) k b w)
    (h3 : ¬ 2 ^ dX N * w5lam3 N ≤ w5S (sensRows s r0) (agree (univ \ K) s) k b w)
    (h2 : ∀ c, c ≠ k → ∀ b' : Bool,
      ¬ 2 ^ dX N * w5lam2 N ≤ w5S (sensRows s r0) (agree (univ \ K) s) c b' w)
    (h4 : ∀ j ∈ univ \ K,
      ¬ 2 ^ dX N * w5th N ≤ w5S (sensRows s r0) (agree (univ \ K) (flipAt j s)) k b w) :
    CoreAt N s K k (2 * kap0 N) (w5G f w) := by
  set a : ℝ := 2 ^ dX N with ha_def
  have ha : 0 < a := by positivity
  have hκ0 : 0 < kap0 N := w5_kap0_pos (by omega)
  have hκN := w5_kapN_ge N
  have hA0 := w5_A0C_nonneg N
  have hm0 : 0 < mX N := by linarith
  have hm' : 7 / 8 ≤ 1 - 2 / mX N := by
    have : 2 / mX N ≤ 1 / 8 := by rw [div_le_iff₀ hm0]; linarith
    linarith
  have hm1 : 1 - 2 / mX N ≤ 1 := by have : 0 ≤ 2 / mX N := by positivity
                                    linarith
  have hk0a : kap0 N * a / 2 = (dX N : ℝ) ^ 2 / 2 := by
    unfold kap0; rw [← ha_def]; field_simp
  -- the fixed parts
  have hfix : ∀ (t : State N), ham s t ≤ 2 → ∀ c, |w5fix f (agree (univ \ K) t) c| ≤ kap0 N * a / 2 := by
    intro t ht c
    have h0 := w5fix_scaled_le f hfar K t ht hdM hd2 hD c
    rw [← ha_def, div_le_iff₀ ha] at h0
    rw [hk0a]
    have e : (dX N : ℝ) ^ 2 / a / 2 * a = (dX N : ℝ) ^ 2 / 2 := by field_simp
    linarith
  have hs0 : ham s s ≤ 2 := by simp [ham_self]
  have hfc : ∀ c, |fK (w5G f w) s K c * a -
      w5S (sensRows s r0) (agree (univ \ K) s) c (w5or f c) w| ≤ kap0 N * a / 2 := by
    intro c
    have e := w5_fK_w5G f K c w hdM
    rw [← ha_def] at e
    rw [e, add_sub_cancel_right]
    exact hfix s hs0 c
  obtain ⟨σ, hσ, hσS⟩ := w5_sign_choice f k b
  rw [hσS] at h1 h3
  have h3' : σ * w5S (sensRows s r0) (agree (univ \ K) s) k (w5or f k) w < a * (x2C N - 3 * kap0 N) := by
    unfold w5lam3 at h3; push_neg at h3; exact h3
  have h1' : a * (A0C N + 2 * kapN N + 3 * kap0 N) ≤
      σ * w5S (sensRows s r0) (agree (univ \ K) s) k (w5or f k) w := by
    unfold w5lam1 at h1; exact h1
  obtain ⟨_, hL1, hL2, hN⟩ := w5_core_alg ha hκ0 hκN hA0 hm' hm1 hσ (hfc k) h1' h3'
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · intro c hc
    have hc1 := h2 c hc (w5or f c)
    have hc2 := h2 c hc (!(w5or f c))
    rw [w5S_not] at hc2
    push_neg at hc1 hc2
    unfold w5lam2 at hc1 hc2
    have hS : |w5S (sensRows s r0) (agree (univ \ K) s) c (w5or f c) w| <
        a * (A0C N + kapN N - 5 / 2 * kap0 N) := abs_lt.2 ⟨by linarith, hc1⟩
    have hfc' := abs_le.1 (hfc c)
    have habs : |fK (w5G f w) s K c| * a < a * (A0C N + kapN N - 2 * kap0 N) := by
      rw [abs_lt] at hS
      rcases abs_cases (fK (w5G f w) s K c) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> nlinarith
    have := lt_of_mul_lt_mul_left (by linarith [habs] : a * |fK (w5G f w) s K c| <
      a * (A0C N + kapN N - 2 * kap0 N)) ha.le
    linarith
  · intro j hj
    have hj2 : ham s (flipAt j s) ≤ 2 := by
      have := ham_flipAt_le_one j s; rw [ham_comm] at this; omega
    have hhj : |hK (w5G f w) s K j k * a -
        w5S (sensRows s r0) (agree (univ \ K) (flipAt j s)) k (w5or f k) w| ≤ kap0 N * a / 2 := by
      have e := w5_hK_w5G f K j k w hdM
      rw [← ha_def] at e
      rw [e, add_sub_cancel_right]
      exact hfix _ hj2 k
    have hT := h4 j hj
    rw [hσS] at hT
    push_neg at hT
    unfold w5th at hT
    exact hN _ _ hhj hT

end Census
end IIT
