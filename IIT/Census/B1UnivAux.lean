/-
Census, B1 lower bound, leaf `phi_univ_ge_EX`: abstract inequalities used by `univ_lower_det`
(check V gives a negative excess for the comparison partition; check M0 gives the cause value).
-/
import IIT.Census.B1UnivSide
import IIT.Census.B1UnivPart

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- **The excess of the comparison partition** is at most `(N-1)((F_x - λ_min) + M(x))`. -/
theorem uxTheta_excess {lam : Fin N → Finset (Fin N) → ℝ} {lmin : ℝ} (hP : 0 ≤ lmin) {x : Fin N}
    {P : Finset (Fin N)} (hxP : x ∉ P) (hN2 : 2 ≤ N)
    (hPdef : ∀ j, j ∈ P ↔ (j ≠ x ∧ lam j {x} ≤ kF lam j - lmin)) :
    ((N : ℝ) - 1) * ∑ j, lam j (profile (uxTheta x P hxP hN2) j) -
        lmin * ∑ j, ((profile (uxTheta x P hxP hN2) j).card : ℝ) ≤
      ((N : ℝ) - 1) * ((kF lam x - lmin) + kM lam lmin {x}) := by
  set θ := uxTheta x P hxP hN2
  have hfullcard : ∀ j : Fin N, (univ.erase j).card = N - 1 := fun j => by
    rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hunit : ∀ j ∈ univ.erase x, ((N : ℝ) - 1) * lam j (profile θ j) - lmin * (profile θ j).card ≤
      ((N : ℝ) - 1) * min (lam j {x}) (kF lam j - lmin) := by
    intro j hj
    have hjx : j ≠ x := ne_of_mem_erase hj
    by_cases hjP : j ∈ P
    · rw [uxTheta_profile_P hjP, card_singleton]
      have hle : lam j {x} ≤ kF lam j - lmin := ((hPdef j).1 hjP).2
      rw [min_eq_left hle]
      push_cast; linarith
    · rw [uxTheta_profile_R hjx hjP, hfullcard, hcast]
      have hlt : ¬ lam j {x} ≤ kF lam j - lmin := fun h => hjP ((hPdef j).2 ⟨hjx, h⟩)
      rw [min_eq_right (le_of_lt (not_le.1 hlt))]
      unfold kF; ring_nf; rfl
  have hunitx : ((N : ℝ) - 1) * lam x (profile θ x) - lmin * (profile θ x).card =
      ((N : ℝ) - 1) * (kF lam x - lmin) := by
    rw [uxTheta_profile_x, hfullcard, hcast]; unfold kF; ring
  have hsplit : ((N : ℝ) - 1) * ∑ j, lam j (profile θ j) - lmin * ∑ j, ((profile θ j).card : ℝ) =
      ∑ j, (((N : ℝ) - 1) * lam j (profile θ j) - lmin * (profile θ j).card) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
  rw [hsplit, ← add_sum_erase _ _ (mem_univ x), hunitx]
  have hcompl : ({x}ᶜ : Finset (Fin N)) = univ.erase x := by ext; simp
  have := sum_le_sum hunit
  rw [kM, hcompl, mul_add, mul_sum]
  linarith

/-- **Check V ⇒ negative excess**: `(F_x - λ_min) + M(x) < 0`. -/
theorem vsum_neg {lam : Fin N → Finset (Fin N) → ℝ} {lmin δ1 : ℝ} {x : Fin N} {lamv y : Fin N → ℝ}
    (hNbig : (10 : ℝ) ^ 7 ≤ N) (hδ0 : 0 ≤ δ1) (hNδ : (N : ℝ) * δ1 ≤ 1 / 100)
    (hcj : ∀ j, (kF lam j - lmin) * Real.log 2 ≤ Real.log (y j / (1001 / 2000)) + 5 * δ1)
    (hlamx : ∀ j, lam j {x} * Real.log 2 = lamv j)
    (hlamlb : ∀ j, -(1 / 2 : ℝ) ≤ lamv j) (hy : ∀ j, (1001 / 2000 : ℝ) ≤ y j) (hy1 : ∀ j, y j ≤ 1)
    (hV : ∑ j, min (lamv j) (Real.log (y j / (1001 / 2000))) ≤ -((N : ℝ) / (2 * 10 ^ 6))) :
    (kF lam x - lmin) + kM lam lmin {x} < 0 := by
  have hl2 := Real.log_pos one_lt_two
  have hcompl : ({x}ᶜ : Finset (Fin N)) = univ.erase x := by ext; simp
  have hterm : ∀ j, min (lam j {x}) (kF lam j - lmin) * Real.log 2 ≤
      min (lamv j) (Real.log (y j / (1001 / 2000))) + 5 * δ1 := by
    intro j
    rw [min_mul_of_nonneg _ _ hl2.le, hlamx]
    have h1 := hcj j
    have h2 := min_le_left (lamv j) ((kF lam j - lmin) * Real.log 2)
    have h3 := min_le_right (lamv j) ((kF lam j - lmin) * Real.log 2)
    rcases min_choice (lamv j) (Real.log (y j / (1001 / 2000))) with h | h <;> rw [h]
    · linarith
    · linarith
  have hsumM : kM lam lmin {x} * Real.log 2 ≤
      ∑ j ∈ univ.erase x, min (lamv j) (Real.log (y j / (1001 / 2000))) + N * δ1 * 5 := by
    rw [kM, hcompl, sum_mul]
    refine (sum_le_sum fun j _ => hterm j).trans ?_
    rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    have h1 : (((univ.erase x).card : ℕ) : ℝ) ≤ N := by
      exact_mod_cast (card_le_univ _).trans (by simp)
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 5 * δ1)
    linarith
  have hx_term : -(1 / 2 : ℝ) ≤ min (lamv x) (Real.log (y x / (1001 / 2000))) := by
    refine le_min (hlamlb x) ?_
    have : 0 ≤ Real.log (y x / (1001 / 2000)) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith [hy x])
    linarith
  have hsplitV := add_sum_erase univ (fun j => min (lamv j) (Real.log (y j / (1001 / 2000)))) (mem_univ x)
  have hcx : (kF lam x - lmin) * Real.log 2 ≤ 1 := by
    have h1 := hcj x
    have h0 : 0 < y x := by linarith [hy x]
    have h2 : Real.log (y x / (1001 / 2000)) ≤ y x / (1001 / 2000) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos h0 (by norm_num))
    have h4 : y x / (1001 / 2000) ≤ 2000 / 1001 := by
      rw [div_le_iff₀ (by norm_num)]; linarith [hy1 x]
    have hδs : δ1 ≤ 1 / 10 ^ 6 := by
      have := mul_le_mul_of_nonneg_left hNbig hδ0
      nlinarith
    linarith
  have hNV : (5 : ℝ) ≤ (N : ℝ) / (2 * 10 ^ 6) := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  have htot : ((kF lam x - lmin) + kM lam lmin {x}) * Real.log 2 < 0 := by
    rw [add_mul]; linarith
  by_contra hc; push Not at hc
  have := mul_nonneg hc hl2.le
  linarith

/-- **Check M0 ⇒ the cause value**: `kM0 ≥ N/10⁵ - 1.02`. -/
theorem kM0_ge {lam : Fin N → Finset (Fin N) → ℝ} {δ1 : ℝ} {x : Fin N} {lamv y : Fin N → ℝ}
    (hNbig : (10 : ℝ) ^ 7 ≤ N) (hδ0 : 0 ≤ δ1) (hNδ : (N : ℝ) * δ1 ≤ 1 / 100)
    (hkF : ∀ j, Real.log (2 * y j) - 2 * δ1 ≤ kF lam j * Real.log 2)
    (hlamx : ∀ j, lam j {x} * Real.log 2 = lamv j)
    (hy0 : ∀ j, 0 < y j) (hy1 : ∀ j, y j ≤ 1)
    (hM0 : (N : ℝ) / 10 ^ 5 ≤ ∑ j, min (lamv j) (Real.log (2 * y j))) :
    (N : ℝ) / 10 ^ 5 - 102 / 100 ≤ kM0 lam x := by
  have hl2 := Real.log_pos one_lt_two
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hterm : ∀ j, min (lamv j) (Real.log (2 * y j)) - 2 * δ1 ≤ min (lam j {x}) (kF lam j) * Real.log 2 := by
    intro j
    rw [min_mul_of_nonneg _ _ hl2.le, hlamx]
    have h0 := hkF j
    have h1 := min_le_left (lamv j) (Real.log (2 * y j))
    have h2 := min_le_right (lamv j) (Real.log (2 * y j))
    exact le_min (by linarith) (by linarith)
  have hsum : ∑ j ∈ univ.erase x, (min (lamv j) (Real.log (2 * y j)) - 2 * δ1) ≤ kM0 lam x * Real.log 2 := by
    rw [kM0, sum_mul]; exact sum_le_sum fun j _ => hterm j
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul] at hsum
  have hsplitM := add_sum_erase univ (fun j => min (lamv j) (Real.log (2 * y j))) (mem_univ x)
  have hxt : min (lamv x) (Real.log (2 * y x)) ≤ 1 := by
    refine (min_le_right _ _).trans ?_
    have : Real.log (2 * y x) ≤ 2 * y x - 1 := Real.log_le_sub_one_of_pos (by linarith [hy0 x])
    linarith [hy1 x]
  have hcard : (((univ.erase x).card : ℕ) : ℝ) * (2 * δ1) ≤ 2 / 100 := by
    have h1 : (((univ.erase x).card : ℕ) : ℝ) ≤ N := by
      exact_mod_cast (card_le_univ _).trans (by simp)
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 2 * δ1)
    linarith
  have hge : (N : ℝ) / 10 ^ 5 - 102 / 100 ≤ kM0 lam x * Real.log 2 := by linarith
  have hnn : 0 ≤ (N : ℝ) / 10 ^ 5 - 102 / 100 := by
    rw [sub_nonneg, le_div_iff₀ (by norm_num)]; linarith
  have h0 : 0 ≤ kM0 lam x := by
    by_contra h; push Not at h; nlinarith
  nlinarith

end Census
end IIT
