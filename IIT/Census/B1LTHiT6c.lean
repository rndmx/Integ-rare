/-
Census, B1 LTBetaHi, module T6 (part C): the decomposition and the deterministic core of Lemma TC'.

* (L6) `lt3_hdec`: at the patterns `t0 ⊕ u` with `t0 = tc ⊕ Ts`, the full numerator of unit `e i` is
  `σ M(Ts ⊕ u, i) + light(t0, i)` up to `σ (V1 + V2) ρ + φL`, from `num_split_heavy`, `lemmaM_blocks` and the box
  equality `lo + wd · φ = M`.
* (L7) `triple_lower_rl`: the TC' core, a copy of `triple_lower_tilt` with the RL table conditions (V), (G), (P)
  (`rlV8R` / `rlPSR`) in place of the `q(t)` table; generic in the level (`Vv`, `Gg`, `Pp`).
-/
import IIT.Census.B1LTHiT6b

namespace IIT
namespace Census

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-! ### (L6) The decomposition -/

/-- The light part of `Num(S, S, t, j)`: rows outside the heavy set `H`. -/
noncomputable def lt3Light (w : Param N) (S : Finset (Fin N)) (H : Finset (State N)) (t : State N)
    (j : Fin N) : ℝ :=
  ∑ v ∈ Hᶜ, clamp01 (w (merge S t v) j) * Pw w v

/-- **(L6)** The decomposition of the numerators at the patterns `t0 ⊕ u`, `t0 = tc ⊕ Ts`. -/
theorem lt3_hdec (w : Param N) (e : Fin 3 ↪ Fin N) {S : Finset (Fin N)} (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
    (tc : State N) (H : Finset (State N)) {σ ρ φL : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ)
    (hH : ∀ r ∈ H, (∀ j ∈ S, r j = tc j) ∨ (∀ j ∈ S, r j ≠ tc j))
    (φ : Fin (2 ^ 3) → Fin 3 → ℝ)
    (hA : ∀ r ∈ lt3HA S tc H, ∀ (u : Fin (2 ^ 3)) (i : Fin 3), ¬((u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ)) →
      |clamp01 (w (pkFlip e r u) (e i)) - φ u i| ≤ ρ)
    (hB : ∀ r ∈ lt3HB S tc H, ∀ (u : Fin (2 ^ 3)) (i : Fin 3), ¬((u : ℕ) = 7 ∨ (u : ℕ) = 7 - 2 ^ (i : ℕ)) →
      |clamp01 (w (pkFlip e r (pkCo u)) (e i)) - φ u i| ≤ ρ)
    (M : Fin 8 → Fin 3 → ℝ) (Ts : Fin (2 ^ 3))
    (hbox : ∀ (v : Fin (2 ^ 3)) (i : Fin 3),
      rlLoR (lt3RealData w e S tc H σ) v i + rlWdR (lt3RealData w e S tc H σ) v i * φ v i = rlMR M v i)
    (hlight : ∀ (u : Fin (2 ^ 3)) (i : Fin 3),
      |lt3Light w S H (pkFlip e (pkFlip e tc Ts) u) (e i) - lt3Light w S H (pkFlip e tc Ts) (e i)| ≤ φL)
    (i : Fin 3) (u : Fin (2 ^ 3)) :
    |Num w S S (pkFlip e (pkFlip e tc Ts) u) (e i) -
        (σ * rlMR M ((Ts : ℕ) ^^^ (u : ℕ)) i + lt3Light w S H (pkFlip e tc Ts) (e i))| ≤
      σ * (((lt3RealData w e S tc H σ).V1 + (lt3RealData w e S tc H σ).V2) * ρ) + φL := by
  have hM := lemmaM_blocks w e hS tc H hσ hρ hH φ hA hB (pkXor Ts u) i
  rw [hbox, ← pkFlip_pkFlip] at hM
  have hMv : rlMR M (pkXor Ts u : ℕ) i = rlMR M ((Ts : ℕ) ^^^ (u : ℕ)) i := rfl
  rw [hMv] at hM
  rw [num_split_heavy w S H _ (e i)]
  set h := ∑ r ∈ H, clamp01 (w (merge S (pkFlip e (pkFlip e tc Ts) u) r) (e i)) * Pw w r with hh
  set X := ((lt3RealData w e S tc H σ).V1 + (lt3RealData w e S tc H σ).V2) * ρ with hX
  have hσM : |h - σ * rlMR M ((Ts : ℕ) ^^^ (u : ℕ)) i| ≤ σ * X := by
    have e1 : h - σ * rlMR M ((Ts : ℕ) ^^^ (u : ℕ)) i = σ * (h / σ - rlMR M ((Ts : ℕ) ^^^ (u : ℕ)) i) := by
      field_simp
    rw [e1, abs_mul, abs_of_pos hσ]
    exact mul_le_mul_of_nonneg_left hM hσ.le
  have hL := hlight u i
  have a1 := abs_le.1 hσM
  have a2 := abs_le.1 hL
  have hL' : ∑ v ∈ Hᶜ, clamp01 (w (merge S (pkFlip e (pkFlip e tc Ts) u) v) (e i)) * Pw w v =
      lt3Light w S H (pkFlip e (pkFlip e tc Ts) u) (e i) := rfl
  rw [hL', abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]

/-! ### (L7) The deterministic core of Lemma TC' -/

section TCp

variable {a b c : Fin N}

lemma rl_xor_ne {Ts : ℕ} {u : Fin 8} (hu : u ≠ 0) : Ts ^^^ (u : ℕ) ≠ Ts := by
  intro h
  apply hu
  have h2 : Ts ^^^ (Ts ^^^ (u : ℕ)) = Ts ^^^ Ts := by rw [h]
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h2
  exact Fin.ext h2

/-- **Lemma TC', deterministic core.** Order the triple as `(a, b, c)`; let the full numerators at the
patterns `t0 ⊕ u` be within `φ` of `σ M(Ts ⊕ u, i) + B_i` for a real RL table `M` satisfying the value
bound (V) `Vv ≤ v*`, the gap (G) `Gg` and the pattern margin (P) `Pp`. With the level band `η`, the
smallness conditions and an effect side `≥ E0`:
`φ_s(S) ≥ σ (y - 6η²/((A - η) σ)) / (8 A ln 2)` for every `0 < y ≤ Vv - 6φ/σ`. -/
theorem triple_lower_rl {z : Param N} (hz : z ∈ openCube N) (s : State N)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (t0 : State N) {Ts : ℕ} (hTs : Ts < 8)
    (M : Fin 8 → Fin 3 → ℝ) (B : Fin N → ℝ) {A η δ σ φ y Vv Gg Pp Fm E0 : ℝ}
    (hη : 0 ≤ η) (hηA : 3 * η ≤ A) (hA : 0 < A) (hδ : 0 ≤ δ) (hσ : 0 < σ)
    (hlev : ∀ Y ⊆ ({a, b, c} : Finset (Fin N)), ∀ t', ∀ i ∈ ({a, b, c} : Finset (Fin N)),
      |Num (flipP s z) {a, b, c} Y t' i - A| ≤ η)
    (hdec : ∀ (i : Fin 3) (u : Fin 8), |Num (flipP s z) {a, b, c} {a, b, c}
      (pkFlip (pkE3 hab hac hbc) t0 u) (pkE3 hab hac hbc i) -
        (σ * rlMR M (Ts ^^^ (u : ℕ)) i + B (pkE3 hab hac hbc i))| ≤ φ)
    (hV : Vv ≤ rlV8R lp3CStar Ts M / 8)
    (hG : ∀ C ∈ lp3Profiles, C ≠ lp3CStar →
      Gg ≤ rlV8R C Ts M / (8 * (cd_cc 3 C : ℝ)) - rlV8R lp3CStar Ts M / 40)
    (hP : ∀ u < 8, u ≠ Ts → Pp ≤ rlPSR M Ts - rlPSR M u)
    (hFmax : rlV8R lp3CStar Ts M / 8 ≤ Fm)
    (hy : 0 < y) (hyV : y ≤ Vv - 6 * φ / σ)
    (hδG : δ * (Fm + 6 * φ / σ) / 5 + 6 * (6 * φ / σ) / 5 ≤ Gg)
    (hsmall : 36 * η ^ 2 < δ * y * σ * (A - η))
    (hmsmall : 24 * A * η ^ 2 < (A - η) ^ 2 * (σ * Pp - 6 * φ))
    (hE0 : 6 * η / ((A - η) * Real.log 2) ≤ E0)
    (heff : ∃ te ∈ sysMaxEffStates (tpmOf z) {a, b, c} s s,
      ∀ θ : SysPartition N {a, b, c}, E0 ≤ sysPhiE (tpmOf z) {a, b, c} s θ s te) :
    σ * (y - 6 * η ^ 2 / ((A - η) * σ)) / (8 * A * Real.log 2) ≤ phi z s {a, b, c} := by
  set e := pkE3 hab hac hbc with he
  have hS := pkE3_S hab hac hbc
  set E := 6 * φ / σ with hE
  have hφ : 0 ≤ φ := (abs_nonneg _).trans (hdec 0 0)
  have hE0' : 0 ≤ E := by positivity
  set θs := tl_thetaStar a b c hab hac hbc
  set ξ : Fin 3 → Fin 8 → ℝ := fun i u => rlMR M (Ts ^^^ (u : ℕ)) i with hξ
  have hbr : ∀ θ : SysPartition N {a, b, c},
      |tl_F (flipP s z) θ t0 σ - lp3V (lpTab e hS θ) ξ| ≤ E := fun θ =>
    pk_F_bridge hσ rfl (pk_bridge3 (flipP s z) e hS θ t0 ξ B hdec)
  have hlpV : ∀ C, lp3V C ξ = rlV8R C Ts M / 8 := fun C => by
    rw [rlV8R_eq_lp3V]; ring
  set Fs := rlV8R lp3CStar Ts M / 8 with hFs0
  have hvs : lp3V (lpTab e hS θs) ξ = Fs := by
    rw [lp3V_congr (pk_lpTab_star hab hac hbc) ξ, hlpV]
  have hFs := abs_le.1 (hbr θs)
  rw [hvs] at hFs
  -- the regularity hypothesis
  have hreg : ∀ θ : SysPartition N {a, b, c},
      (∃ j ∈ ({a, b, c} : Finset (Fin N)), profile θ j ≠ profile θs j) →
      (1 + δ) * tl_F (flipP s z) θs t0 σ / 5 ≤ tl_F (flipP s z) θ t0 σ / (sysCutCount θ : ℝ) := by
    intro θ hθ
    have hmem : lpTab e hS θ ∈ lp3Profiles := lpTab_mem e hS θ
    have hC := hG _ hmem (pk_lpTab_ne_star hab hac hbc θ hθ)
    rw [lpTab_cc] at hC
    have hFθ := abs_le.1 (hbr θ)
    rw [hlpV] at hFθ
    have hk1 : (1 : ℝ) ≤ sysCutCount θ := by exact_mod_cast sysCutCount_pos θ
    have hk0 : (0 : ℝ) < sysCutCount θ := by linarith
    set Fθ := rlV8R (lpTab e hS θ) Ts M with hFθd
    have hC' : Fs / 5 + Gg ≤ Fθ / 8 / (sysCutCount θ : ℝ) := by
      have e1 : Fθ / (8 * (sysCutCount θ : ℝ)) = Fθ / 8 / (sysCutCount θ : ℝ) := by
        rw [div_div]
      have e2 : rlV8R lp3CStar Ts M / 40 = Fs / 5 := by rw [hFs0]; ring
      rw [e1, e2] at hC; linarith
    have h1 : (1 + δ) * tl_F (flipP s z) θs t0 σ / 5 ≤ (1 + δ) * (Fs + E) / 5 := by
      have := mul_le_mul_of_nonneg_left hFs.2 (by linarith : (0 : ℝ) ≤ 1 + δ)
      linarith
    have h2 : (1 + δ) * (Fs + E) / 5 ≤ Fs / 5 + Gg - E := by
      have h3 : δ * (Fs + E) ≤ δ * (Fm + E) := mul_le_mul_of_nonneg_left (by linarith) hδ
      have : (1 + δ) * (Fs + E) / 5 = Fs / 5 + E / 5 + δ * (Fs + E) / 5 := by ring
      rw [this]
      have h4 : 6 * E / 5 = E / 5 + E := by ring
      linarith
    have h3 : Fθ / 8 / (sysCutCount θ : ℝ) ≤ tl_F (flipP s z) θ t0 σ / (sysCutCount θ : ℝ) + E := by
      have : Fθ / 8 / (sysCutCount θ : ℝ) ≤ (tl_F (flipP s z) θ t0 σ + E) / (sysCutCount θ : ℝ) :=
        div_le_div_of_nonneg_right (by linarith [hFθ.1]) hk0.le
      rw [add_div] at this
      linarith [div_le_self hE0' hk1]
    linarith
  -- the pattern margin
  have hmarg : ∀ u : Fin 8, u ≠ 0 → ∑ i : Fin 3, ξ i u + Pp ≤ ∑ i : Fin 3, ξ i 0 := by
    intro u hu
    have hlt : Ts ^^^ (u : ℕ) < 8 := by
      have hu8 : (u : ℕ) < 2 ^ 3 := u.2
      have := Nat.xor_lt_two_pow (n := 3) (by simpa using hTs) hu8; simpa using this
    have h := hP _ hlt (rl_xor_ne hu)
    have e0 : ∑ i : Fin 3, ξ i 0 = rlPSR M Ts := by
      simp only [hξ, rlPSR, Fin.val_zero, Nat.xor_zero]
    have eu : ∑ i : Fin 3, ξ i u = rlPSR M (Ts ^^^ (u : ℕ)) := rfl
    rw [e0, eu]; linarith
  have hmarg' : ∀ t' : State N, (∃ j ∈ ({a, b, c} : Finset (Fin N)), t' j ≠ t0 j) →
      ∑ i ∈ ({a, b, c} : Finset (Fin N)), Num (flipP s z) {a, b, c} {a, b, c} t' i
        + (σ * Pp - 6 * φ) ≤
        ∑ i ∈ ({a, b, c} : Finset (Fin N)), Num (flipP s z) {a, b, c} {a, b, c} t0 i := by
    intro t' ht'
    set u := pkEnc 3 (fun q => decide (t' (e q) ≠ t0 (e q))) with hu
    have hagr := pk_flip_enc e hS t0 t'
    have hu0 : u ≠ 0 := by
      intro h0
      obtain ⟨j, hj, hjne⟩ := ht'
      have := hagr j hj
      rw [← hu, h0, pkFlip_zero e t0 _ rfl] at this
      exact hjne this.symm
    have hNt : ∀ i, Num (flipP s z) {a, b, c} {a, b, c} t' i =
        Num (flipP s z) {a, b, c} {a, b, c} (pkFlip e t0 u) i := fun i =>
      Num_congr (fun j hj => (hagr j hj).symm) _ i
    rw [pk_sum_S e hS, pk_sum_S e hS]
    simp only [hNt]
    have hup : ∀ i : Fin 3, Num (flipP s z) {a, b, c} {a, b, c} (pkFlip e t0 u) (e i) ≤
        σ * ξ i u + B (e i) + φ := fun i => by linarith [(abs_le.1 (hdec i u)).2]
    have hlo : ∀ i : Fin 3, σ * ξ i 0 + B (e i) - φ ≤
        Num (flipP s z) {a, b, c} {a, b, c} t0 (e i) := fun i => by
      have := (abs_le.1 (hdec i 0)).1
      rw [pkFlip_zero e t0 0 rfl] at this
      linarith
    have hm := mul_le_mul_of_nonneg_left (hmarg u hu0) hσ.le
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at hm ⊢
    linarith [hup 0, hup 1, hup 2, hlo 0, hlo 1, hlo 2]
  have hFy : y ≤ tl_F (flipP s z) θs t0 σ := by linarith [hFs.1]
  exact pk_tl_triple_lower_gen' hz s hab hac hbc t0 hη hηA hA hδ hy hσ hlev hreg hFy hmarg'
    hsmall hmsmall hE0 heff

end TCp

end Census
end IIT
