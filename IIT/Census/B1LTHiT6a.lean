/-
Census, B1 LTBetaHi, module T6 (part A): foundations of Lemma TC'.

* (L0) `pkFlip_pkFlip`: flipping twice is flipping by the XOR of the masks; `pkFlip_seven_xor`: on the three
  units, the complementary mask `7 ⊕ u` gives the negated bits.
* (L1) `merge_pkFlip_class`: a heavy row `r` agreeing with `tc` on `S` sees `merge S (tc ⊕ u) r = r ⊕ u`; a row
  disagreeing on all of `S` sees `r ⊕ (7 ⊕ u)`.
* (L2) `num_split_heavy`: `Num` splits as a heavy part over `H` and a light part over `Hᶜ`.
* (L4) The real-valued value form `rlV8R` / pattern sums `rlPSR`, their link to `lp3V` (`rlV8R_eq_lp3V`), the
  agreement with the rational checker forms (`rlV8R_cast`, `rlPSR_cast`), and perturbation (`36 ω`, `3 ω`).
-/
import IIT.Census.B1PairK
import IIT.Census.B1LTHiCertRL4

namespace IIT
namespace Census

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-! ### (L0) Double flips -/

lemma rlXor_lt {a b k : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k :=
  Nat.xor_lt_two_pow ha hb

/-- The XOR of two masks. -/
def pkXor {k : ℕ} (U u : Fin (2 ^ k)) : Fin (2 ^ k) := ⟨(U : ℕ) ^^^ (u : ℕ), rlXor_lt U.2 u.2⟩

/-- **(L0)** Flipping by `U` then by `u` is flipping by `U ⊕ u`. -/
lemma pkFlip_pkFlip {k : ℕ} (e : Fin k ↪ Fin N) (t : State N) (U u : Fin (2 ^ k)) :
    pkFlip e (pkFlip e t U) u = pkFlip e t (pkXor U u) := by
  funext j
  by_cases hj : ∃ q, e q = j
  · obtain ⟨q, rfl⟩ := hj
    rw [pkFlip_e, pkFlip_e, pkFlip_e]
    simp only [pkXor, Nat.testBit_xor]
    cases (U : ℕ).testBit q <;> cases (u : ℕ).testBit q <;> simp
  · push Not at hj
    rw [pkFlip_of_not _ _ _ hj, pkFlip_of_not _ _ _ hj, pkFlip_of_not _ _ _ hj]

/-- The complementary mask `7 ⊕ u` of a 3-bit mask. -/
def pkCo (u : Fin (2 ^ 3)) : Fin (2 ^ 3) := ⟨7 ^^^ (u : ℕ), rlXor_lt (by norm_num) u.2⟩

lemma pkCo_testBit (u : Fin (2 ^ 3)) (q : Fin 3) :
    ((pkCo u : ℕ)).testBit q = !((u : ℕ).testBit q) := by
  simp only [pkCo, Nat.testBit_xor]
  have : (7 : ℕ).testBit q = true := by fin_cases q <;> decide
  rw [this]; simp

/-- On the units, the complementary mask negates the flipped bits. -/
lemma pkFlip_seven_xor (e : Fin 3 ↪ Fin N) (t : State N) (u : Fin (2 ^ 3)) (q : Fin 3) :
    pkFlip e t (pkCo u) (e q) = !(pkFlip e t u (e q)) := by
  rw [pkFlip_e, pkFlip_e, pkCo_testBit]
  cases (u : ℕ).testBit q <;> simp

/-! ### (L1) Agreement classes of heavy rows -/

/-- **(L1)** The merged state seen by a heavy row, by agreement class on `S`. -/
lemma merge_pkFlip_class (e : Fin 3 ↪ Fin N) {S : Finset (Fin N)} (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
    {tc r : State N} (u : Fin (2 ^ 3)) :
    ((∀ j ∈ S, r j = tc j) → merge S (pkFlip e tc u) r = pkFlip e r u) ∧
    ((∀ j ∈ S, r j ≠ tc j) → merge S (pkFlip e tc u) r = pkFlip e r (pkCo u)) := by
  constructor
  · intro hA
    funext j
    by_cases hj : j ∈ S
    · rw [merge_mem hj]
      obtain ⟨q, rfl⟩ := (hS j).1 hj
      rw [pkFlip_e, pkFlip_e, hA _ hj]
    · rw [merge_not_mem hj, pkFlip_of_not]
      intro q hq; exact hj ((hS j).2 ⟨q, hq⟩)
  · intro hB
    funext j
    by_cases hj : j ∈ S
    · rw [merge_mem hj]
      obtain ⟨q, rfl⟩ := (hS _).1 hj
      have h := hB _ hj
      have hr : r (e q) = !tc (e q) := by
        cases hr : r (e q) <;> cases ht : tc (e q) <;> simp_all
      rw [pkFlip_e, pkFlip_e, pkCo_testBit, hr]
      cases (u : ℕ).testBit q <;> simp
    · rw [merge_not_mem hj, pkFlip_of_not]
      intro q hq; exact hj ((hS j).2 ⟨q, hq⟩)

/-! ### (L2) Heavy / light split of `Num` -/

/-- **(L2)** `Num` as a heavy part over `H` plus a light part over `Hᶜ`. -/
lemma num_split_heavy (w : Param N) (S : Finset (Fin N)) (H : Finset (State N)) (t : State N) (i : Fin N) :
    Num w S S t i = ∑ r ∈ H, clamp01 (w (merge S t r) i) * Pw w r
      + ∑ v ∈ Hᶜ, clamp01 (w (merge S t v) i) * Pw w v := by
  rw [prof_Num_full]; exact (sum_add_sum_compl H _).symm

/-! ### (L4) The real-valued value form -/

/-- The real table as a function of naturals. -/
noncomputable def rlMR (M : Fin 8 → Fin 3 → ℝ) (u i : ℕ) : ℝ :=
  M ⟨u % 8, Nat.mod_lt _ (by decide)⟩ ⟨i % 3, Nat.mod_lt _ (by decide)⟩

/-- `8 v_C` at target `Ts`, real version. -/
noncomputable def rlV8R (C : List (List Bool)) (Ts : ℕ) (M : Fin 8 → Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ u : Fin 8, (cd_fz 3 C 0 (u + 8 * i) : ℝ) * rlMR M (Ts ^^^ (u : ℕ)) i

/-- Pattern sums, real version. -/
noncomputable def rlPSR (M : Fin 8 → Fin 3 → ℝ) (u : ℕ) : ℝ := ∑ i : Fin 3, rlMR M u i

/-- The real value form is `8 lp3V` of the shifted table. -/
lemma rlV8R_eq_lp3V (C : List (List Bool)) (Ts : ℕ) (M : Fin 8 → Fin 3 → ℝ) :
    rlV8R C Ts M = 8 * lp3V C (fun i u => rlMR M (Ts ^^^ (u : ℕ)) i) := by
  rw [← lp3V_lin]; rfl

/-- Agreement with the rational checker form. -/
lemma rlV8R_cast (C : List (List Bool)) (Ts : ℕ) (M : Fin 8 → Fin 3 → ℚ) :
    rlV8R C Ts (fun u i => (M u i : ℝ)) = ((rlV8 C Ts M : ℚ) : ℝ) := by
  simp only [rlV8R, rlV8, rlS3, rlS8, rlMR, rlM, Fin.sum_univ_three, Fin.sum_univ_eight]
  push_cast
  rfl

lemma rlPSR_cast (M : Fin 8 → Fin 3 → ℚ) (u : ℕ) :
    rlPSR (fun u i => (M u i : ℝ)) u = ((rlPS M u : ℚ) : ℝ) := by
  simp only [rlPSR, rlPS, rlS3, rlMR, rlM, Fin.sum_univ_three]
  push_cast
  rfl

lemma rlAbs_cast (C : List (List Bool)) :
    ((rlAbs C : ℚ) : ℝ) = ∑ i : Fin 3, ∑ u : Fin 8, |(cd_fz 3 C 0 (u + 8 * i) : ℝ)| := by
  simp only [rlAbs, rlS3, rlS8, Fin.sum_univ_three, Fin.sum_univ_eight]
  push_cast
  rfl

/-- **Perturbation of the real value form.** -/
theorem rlV8R_pert' (C : List (List Bool)) (Ts : ℕ) {M M0 : Fin 8 → Fin 3 → ℝ} {ω : ℝ}
    (h : ∀ u i, |M u i - M0 u i| ≤ ω) :
    |rlV8R C Ts M - rlV8R C Ts M0| ≤ (rlAbs C : ℝ) * ω := by
  rw [rlAbs_cast, rlV8R, rlV8R, ← sum_sub_distrib, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [← sum_sub_distrib, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun u _ => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (h _ _) (abs_nonneg _)

theorem rlV8R_pert {C : List (List Bool)} (hC : C ∈ lp3Profiles) (Ts : ℕ) {M M0 : Fin 8 → Fin 3 → ℝ} {ω : ℝ}
    (h : ∀ u i, |M u i - M0 u i| ≤ ω) :
    |rlV8R C Ts M - rlV8R C Ts M0| ≤ 36 * ω := by
  have hω : 0 ≤ ω := (abs_nonneg _).trans (h 0 0)
  have hb : ((rlAbs C : ℚ) : ℝ) ≤ 36 := by exact_mod_cast rlAbs_le' hC
  exact (rlV8R_pert' C Ts h).trans (mul_le_mul_of_nonneg_right hb hω)

theorem rlPSR_pert {M M0 : Fin 8 → Fin 3 → ℝ} {ω : ℝ} (h : ∀ u i, |M u i - M0 u i| ≤ ω) (u : ℕ) :
    |rlPSR M u - rlPSR M0 u| ≤ 3 * ω := by
  simp only [rlPSR, rlMR, Fin.sum_univ_three]
  have h0 := abs_le.1 (h ⟨u % 8, Nat.mod_lt _ (by decide)⟩ ⟨0 % 3, Nat.mod_lt _ (by decide)⟩)
  have h1 := abs_le.1 (h ⟨u % 8, Nat.mod_lt _ (by decide)⟩ ⟨1 % 3, Nat.mod_lt _ (by decide)⟩)
  have h2 := abs_le.1 (h ⟨u % 8, Nat.mod_lt _ (by decide)⟩ ⟨2 % 3, Nat.mod_lt _ (by decide)⟩)
  rw [abs_le]; constructor <;> simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at * <;>
    linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

end Census
end IIT
