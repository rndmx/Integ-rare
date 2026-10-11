/-
Census, B1 LTBetaHi, module T6 (part B): Lemma M and the real windowed RL table.

* Real per-unit two-block data `RLDR` (an `ℝ` copy of `RLDw`), its interval ends `rlLoR` / `rlWdR`, and the data
  `lt3RealData` of a heavy set `H`: rows of `H` agreeing with `tc` on `S` (`lt3HA`) and the others (`lt3HB`,
  disagreeing on all of `S` under `hH`), weights `Pw w r / σ`.
* (L3) `lemmaM_blocks`: the heavy part of `Num(S, S, tc ⊕ u, e i)` (divided by `σ`) is `rlLoR + rlWdR · φ u i` up to
  `(V1 + V2) ρ` when every private entry is within `ρ` of its target `φ u i`.
* (L5) `rl_real_window`: real windowed data, floored to the grid `ℤ/n` (`5 ∣ n`), is RL_sym-admissible
  (`rl_sym_full`); the table `max(M0, rlLoR)` lies in the real per-unit box and satisfies (V), (G), (P) weakened by
  `36 (ω + 1/n)`, `6 (ω + 1/n)`, `6 (ω + 1/n)`. The level `t ∈ [0, 1/80]` stays a parameter.
-/
import IIT.Census.B1LTHiT6a

namespace IIT
namespace Census

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-! ### Real per-unit data -/

/-- Real per-unit two-block data. -/
structure RLDR where
  G1 : Fin 3 → ℝ
  F1 : Fin 3 → ℝ
  G2 : Fin 3 → ℝ
  F2 : Fin 3 → ℝ
  V1 : ℝ
  V2 : ℝ

/-- Lower end of the real interval of `(u, i)`. -/
def rlLoR (d : RLDR) (u : ℕ) (i : Fin 3) : ℝ :=
  if u = 0 then d.G1 i else if u = rlBit i then d.F1 i else if u = 7 then d.G2 i
  else if u = 7 - rlBit i then d.F2 i else 0

/-- Width of the real interval of `(u, i)`. -/
def rlWdR (d : RLDR) (u : ℕ) (i : Fin 3) : ℝ :=
  if u = 0 ∨ u = rlBit i then d.V2 else if u = 7 ∨ u = 7 - rlBit i then d.V1 else d.V1 + d.V2

/-- The interval of `(u, i)` as the sum of an `A`-block part and a `B`-block part. -/
lemma rlLoR_split (d : RLDR) (u : Fin (2 ^ 3)) (i : Fin 3) :
    rlLoR d u i = (if (u : ℕ) = 0 then d.G1 i else if (u : ℕ) = 2 ^ (i : ℕ) then d.F1 i else 0) +
      (if (u : ℕ) = 7 then d.G2 i else if (u : ℕ) = 7 - 2 ^ (i : ℕ) then d.F2 i else 0) ∧
    rlWdR d u i = (if (u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ) then 0 else d.V1) +
      (if (u : ℕ) = 7 ∨ (u : ℕ) = 7 - 2 ^ (i : ℕ) then 0 else d.V2) := by
  fin_cases u <;> fin_cases i <;> simp [rlLoR, rlWdR, rlBit]

/-- Rows of `H` agreeing with `tc` on `S`. -/
def lt3HA (S : Finset (Fin N)) (tc : State N) (H : Finset (State N)) : Finset (State N) :=
  H.filter fun r => ∀ j ∈ S, r j = tc j

/-- The other rows of `H`. -/
def lt3HB (S : Finset (Fin N)) (tc : State N) (H : Finset (State N)) : Finset (State N) :=
  H.filter fun r => ¬ ∀ j ∈ S, r j = tc j

/-- **Real per-unit data** of the heavy set `H` (weights `Pw w r / σ`). -/
noncomputable def lt3RealData (w : Param N) (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) (tc : State N)
    (H : Finset (State N)) (σ : ℝ) : RLDR where
  G1 i := ∑ r ∈ lt3HA S tc H, Pw w r / σ * clamp01 (w r (e i))
  F1 i := ∑ r ∈ lt3HA S tc H, Pw w r / σ * clamp01 (w (flip r (e i)) (e i))
  G2 i := ∑ r ∈ lt3HB S tc H, Pw w r / σ * clamp01 (w r (e i))
  F2 i := ∑ r ∈ lt3HB S tc H, Pw w r / σ * clamp01 (w (flip r (e i)) (e i))
  V1 := ∑ r ∈ lt3HA S tc H, Pw w r / σ
  V2 := ∑ r ∈ lt3HB S tc H, Pw w r / σ

/-- Flipping by the one-bit mask `2^q` is `flip` at `e q`. -/
lemma pkFlip_bit {k : ℕ} (e : Fin k ↪ Fin N) (t : State N) (u : Fin (2 ^ k)) (q : Fin k)
    (hu : (u : ℕ) = 2 ^ (q : ℕ)) : pkFlip e t u = flip t (e q) := by
  funext j
  by_cases hj : j = e q
  · subst hj
    rw [pkFlip_e, hu]
    simp [flip, Nat.testBit_two_pow]
  · rw [flip, Function.update_of_ne hj]
    unfold pkFlip
    rw [ite_eq_right]
    rintro ⟨q', hq', hb⟩
    rw [hu, Nat.testBit_two_pow] at hb
    have h1 : (q : ℕ) = q' := by simpa using hb
    have h2 : q = q' := Fin.ext h1
    subst h2
    exact hj hq'.symm

/-- A weighted average of values within `ρ` of `φ`. -/
lemma rl_avg_close {ι : Type*} (T : Finset ι) (c x : ι → ℝ) (φ ρ : ℝ) (hc : ∀ r ∈ T, 0 ≤ c r)
    (hx : ∀ r ∈ T, |x r - φ| ≤ ρ) :
    |∑ r ∈ T, c r * x r - (∑ r ∈ T, c r) * φ| ≤ (∑ r ∈ T, c r) * ρ := by
  rw [sum_mul, sum_mul, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r hr => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (hc r hr)]
  exact mul_le_mul_of_nonneg_left (hx r hr) (hc r hr)

/-- **(L3) Lemma M.** The heavy block sum is `lo + wd · φ` up to `(V1 + V2) ρ`. -/
theorem lemmaM_blocks (w : Param N) (e : Fin 3 ↪ Fin N) {S : Finset (Fin N)} (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
    (tc : State N) (H : Finset (State N)) {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ)
    (hH : ∀ r ∈ H, (∀ j ∈ S, r j = tc j) ∨ (∀ j ∈ S, r j ≠ tc j))
    (φ : Fin (2 ^ 3) → Fin 3 → ℝ)
    (hA : ∀ r ∈ lt3HA S tc H, ∀ (u : Fin (2 ^ 3)) (i : Fin 3), ¬((u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ)) →
      |clamp01 (w (pkFlip e r u) (e i)) - φ u i| ≤ ρ)
    (hB : ∀ r ∈ lt3HB S tc H, ∀ (u : Fin (2 ^ 3)) (i : Fin 3), ¬((u : ℕ) = 7 ∨ (u : ℕ) = 7 - 2 ^ (i : ℕ)) →
      |clamp01 (w (pkFlip e r (pkCo u)) (e i)) - φ u i| ≤ ρ)
    (u : Fin (2 ^ 3)) (i : Fin 3) :
    |(∑ r ∈ H, clamp01 (w (merge S (pkFlip e tc u) r) (e i)) * Pw w r) / σ -
        (rlLoR (lt3RealData w e S tc H σ) u i + rlWdR (lt3RealData w e S tc H σ) u i * φ u i)| ≤
      ((lt3RealData w e S tc H σ).V1 + (lt3RealData w e S tc H σ).V2) * ρ := by
  set d := lt3RealData w e S tc H σ with hd
  have hw0 : ∀ r, 0 ≤ Pw w r / σ := fun r => div_nonneg (Pw_nonneg w r) hσ.le
  have hV1 : 0 ≤ d.V1 := sum_nonneg fun r _ => hw0 r
  have hV2 : 0 ≤ d.V2 := sum_nonneg fun r _ => hw0 r
  -- split into the two blocks
  have hsplit : (∑ r ∈ H, clamp01 (w (merge S (pkFlip e tc u) r) (e i)) * Pw w r) / σ =
      (∑ r ∈ lt3HA S tc H, Pw w r / σ * clamp01 (w (pkFlip e r u) (e i))) +
      (∑ r ∈ lt3HB S tc H, Pw w r / σ * clamp01 (w (pkFlip e r (pkCo u)) (e i))) := by
    rw [← sum_filter_add_sum_filter_not H (fun r => ∀ j ∈ S, r j = tc j), add_div, sum_div, sum_div]
    congr 1
    · refine sum_congr rfl fun r hr => ?_
      rw [(merge_pkFlip_class e hS (tc := tc) (r := r) u).1 (mem_filter.1 hr).2]; ring
    · refine sum_congr rfl fun r hr => ?_
      have hr' := mem_filter.1 hr
      have hdis : ∀ j ∈ S, r j ≠ tc j := (hH r hr'.1).resolve_left hr'.2
      rw [(merge_pkFlip_class e hS (tc := tc) (r := r) u).2 hdis]; ring
  -- the A block
  have hAb : |(∑ r ∈ lt3HA S tc H, Pw w r / σ * clamp01 (w (pkFlip e r u) (e i))) -
      ((if (u : ℕ) = 0 then d.G1 i else if (u : ℕ) = 2 ^ (i : ℕ) then d.F1 i else 0) +
        (if (u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ) then 0 else d.V1) * φ u i)| ≤ d.V1 * ρ := by
    by_cases h0 : (u : ℕ) = 0
    · have : ∀ r, pkFlip e r u = r := fun r => pkFlip_zero e r u h0
      simp only [h0, ite_true, true_or, zero_mul, add_zero, this, hd, lt3RealData, sub_self, abs_zero]
      exact mul_nonneg hV1 hρ
    by_cases hb : (u : ℕ) = 2 ^ (i : ℕ)
    · have : ∀ r, pkFlip e r u = flip r (e i) := fun r => pkFlip_bit e r u i hb
      rw [if_neg h0, if_pos hb, if_pos (Or.inr hb)]
      simp only [zero_mul, add_zero, this, hd, lt3RealData, sub_self,
        abs_zero]
      exact mul_nonneg hV1 hρ
    · simp only [h0, hb, ite_false, or_self, zero_add, hd, lt3RealData]
      exact rl_avg_close _ _ _ _ _ (fun r _ => hw0 r) fun r hr => hA r hr u i (by tauto)
  -- the B block
  have hBb : |(∑ r ∈ lt3HB S tc H, Pw w r / σ * clamp01 (w (pkFlip e r (pkCo u)) (e i))) -
      ((if (u : ℕ) = 7 then d.G2 i else if (u : ℕ) = 7 - 2 ^ (i : ℕ) then d.F2 i else 0) +
        (if (u : ℕ) = 7 ∨ (u : ℕ) = 7 - 2 ^ (i : ℕ) then 0 else d.V2) * φ u i)| ≤ d.V2 * ρ := by
    by_cases h7 : (u : ℕ) = 7
    · have hc : ((pkCo u : Fin (2 ^ 3)) : ℕ) = 0 := by simp only [pkCo, h7]; decide
      have : ∀ r, pkFlip e r (pkCo u) = r := fun r => pkFlip_zero e r _ hc
      simp only [h7, ite_true, true_or, zero_mul, add_zero, this, hd, lt3RealData, sub_self, abs_zero]
      exact mul_nonneg hV2 hρ
    by_cases hb : (u : ℕ) = 7 - 2 ^ (i : ℕ)
    · have hc : ((pkCo u : Fin (2 ^ 3)) : ℕ) = 2 ^ (i : ℕ) := by
        simp only [pkCo]; rw [hb]; fin_cases i <;> decide
      have : ∀ r, pkFlip e r (pkCo u) = flip r (e i) := fun r => pkFlip_bit e r _ i hc
      rw [if_neg h7, if_pos hb, if_pos (Or.inr hb)]
      simp only [zero_mul, add_zero, this, hd, lt3RealData, sub_self,
        abs_zero]
      exact mul_nonneg hV2 hρ
    · simp only [h7, hb, ite_false, or_self, zero_add, hd, lt3RealData]
      exact rl_avg_close _ _ _ _ _ (fun r _ => hw0 r) fun r hr => hB r hr u i (by tauto)
  obtain ⟨hlo, hwd⟩ := rlLoR_split d u i
  rw [hsplit, hlo, hwd]
  have a1 := abs_le.1 hAb
  have a2 := abs_le.1 hBb
  rw [abs_le]; constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2]

/-! ### (L5) The real windowed table -/

/-- Minimum of three reals. -/
noncomputable def rlMin3R (f : Fin 3 → ℝ) : ℝ := min (f 0) (min (f 1) (f 2))

lemma rlMin3R_le (f : Fin 3 → ℝ) (i : Fin 3) : rlMin3R f ≤ f i := by
  unfold rlMin3R; fin_cases i <;> simp

lemma le_rlMin3R {f : Fin 3 → ℝ} {a : ℝ} (h : ∀ i, a ≤ f i) : a ≤ rlMin3R f :=
  le_min (h 0) (le_min (h 1) (h 2))

/-- The real window condition. -/
def RLDR.win (d : RLDR) (ω : ℝ) : Prop :=
  ∀ i : Fin 3, d.G1 i - rlMin3R d.G1 ≤ ω ∧ d.F1 i - rlMin3R d.F1 ≤ ω ∧ d.G2 i - rlMin3R d.G2 ≤ ω ∧
    d.F2 i - rlMin3R d.F2 ≤ ω

/-- Grid floor `⌊x n⌋ / n`. -/
noncomputable def rlFl (n : ℕ) (x : ℝ) : ℚ := (⌊x * n⌋ : ℚ) / n

lemma rlFl_cast (n : ℕ) (x : ℝ) : ((rlFl n x : ℚ) : ℝ) = (⌊x * n⌋ : ℝ) / n := by
  unfold rlFl; push_cast; rfl

lemma rlFl_le {n : ℕ} (hn : 0 < n) (x : ℝ) : ((rlFl n x : ℚ) : ℝ) ≤ x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [rlFl_cast, div_le_iff₀ hn']
  exact Int.floor_le _

lemma rlFl_gt {n : ℕ} (hn : 0 < n) (x : ℝ) : x - 1 / n ≤ ((rlFl n x : ℚ) : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [rlFl_cast, le_div_iff₀ hn', sub_mul, one_div_mul_cancel hn'.ne']
  exact (Int.sub_one_lt_floor _).le

lemma rlFl_mono {n : ℕ} {x y : ℝ} (h : x ≤ y) : rlFl n x ≤ rlFl n y := by
  unfold rlFl
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact_mod_cast Int.floor_mono (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg n))

lemma rlFl_ge_int {n : ℕ} (hn : 0 < n) (k : ℤ) {x : ℝ} (h : (k : ℝ) / n ≤ x) : (k : ℚ) / n ≤ rlFl n x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold rlFl
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  have : (k : ℝ) ≤ x * n := by rwa [div_le_iff₀ hn'] at h
  exact_mod_cast Int.le_floor.2 this

/-- The floored symmetric datum. -/
noncomputable def rlFlD (n : ℕ) (d : RLDR) : RLD :=
  ⟨rlFl n (rlMin3R d.G1), rlFl n (rlMin3R d.F1), rlFl n (rlMin3R d.G2), rlFl n (rlMin3R d.F2),
    rlFl n d.V1, rlFl n d.V2⟩

lemma rlFl_min_close {n : ℕ} (hn : 0 < n) {f : Fin 3 → ℝ} {ω : ℝ} (hw : ∀ i, f i - rlMin3R f ≤ ω) (i : Fin 3) :
    ((rlFl n (rlMin3R f) : ℚ) : ℝ) ≤ f i ∧ f i - ((rlFl n (rlMin3R f) : ℚ) : ℝ) ≤ ω + 1 / n := by
  have h1 := rlFl_le hn (rlMin3R f)
  have h2 := rlFl_gt hn (rlMin3R f)
  have h3 := rlMin3R_le f i
  have h4 := hw i
  constructor <;> linarith

lemma rlLo_flD_le {n : ℕ} (hn : 0 < n) (d : RLDR) {ω : ℝ} (hω : 0 ≤ ω) (hw : d.win ω) (u : ℕ) (i : Fin 3) :
    ((rlLo (rlFlD n d) u i : ℚ) : ℝ) ≤ rlLoR d u i ∧
      rlLoR d u i - ((rlLo (rlFlD n d) u i : ℚ) : ℝ) ≤ ω + 1 / n := by
  have hn' : (0 : ℝ) ≤ 1 / n := by positivity
  unfold rlLo rlLoR rlFlD
  split_ifs
  · exact rlFl_min_close hn (fun j => (hw j).1) i
  · exact rlFl_min_close hn (fun j => (hw j).2.1) i
  · exact rlFl_min_close hn (fun j => (hw j).2.2.1) i
  · exact rlFl_min_close hn (fun j => (hw j).2.2.2) i
  · push_cast; constructor <;> linarith

lemma rlWd_flD_le {n : ℕ} (hn : 0 < n) (d : RLDR) (u : ℕ) (i : Fin 3) :
    ((rlWd (rlFlD n d) u i : ℚ) : ℝ) ≤ rlWdR d u i := by
  have h1 := rlFl_le hn d.V1
  have h2 := rlFl_le hn d.V2
  unfold rlWd rlWdR rlFlD
  split_ifs <;> push_cast <;> linarith

/-- **(L5) RL on real windowed data.** -/
theorem rl_real_window (dR : RLDR) {n : ℕ} (hn : 0 < n) (h5 : 5 ∣ n) {ω : ℝ} (hω : 0 ≤ ω) (hw : dR.win ω)
    (hG1 : ∀ i, 4 / 5 ≤ dR.G1 i) (hGV : ∀ i, dR.G1 i ≤ dR.V1) (hF1 : ∀ i, 0 ≤ dR.F1 i)
    (hF1V : ∀ i, dR.F1 i ≤ dR.V1) (hV1 : 1 ≤ dR.V1) (hG2 : ∀ i, 0 ≤ dR.G2 i) (hF2 : ∀ i, 0 ≤ dR.F2 i)
    (hG2V : ∀ i, dR.G2 i ≤ dR.V2) (hF2V : ∀ i, dR.F2 i ≤ dR.V2) {t : ℚ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 80) :
    ∃ Ts < 8, ∃ M : Fin 8 → Fin 3 → ℝ, ∃ c0 : ℝ,
      4 / 5 ≤ c0 ∧ (∀ i, c0 ≤ dR.G1 i) ∧ (∀ i, dR.G1 i ≤ c0 + (ω + 1 / n)) ∧
      (∀ (u : Fin 8) (i : Fin 3), rlLoR dR u i ≤ M u i ∧ M u i ≤ rlLoR dR u i + rlWdR dR u i) ∧
      8 * c0 * (5 / 3 - t) - 36 * (ω + 1 / n) ≤ rlV8R lp3CStar Ts M ∧
      (∀ C ∈ lp3Profiles, C ≠ lp3CStar →
        c0 * t / 20 - 6 * (ω + 1 / n) ≤ rlV8R C Ts M / (8 * (cd_cc 3 C : ℝ)) - rlV8R lp3CStar Ts M / 40) ∧
      (∀ u < 8, u ≠ Ts → 1 / 20 - 6 * (ω + 1 / n) ≤ rlPSR M Ts - rlPSR M u) := by
  obtain ⟨m, hm⟩ := h5
  have hm0 : 0 < m := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) ≤ 1 / n := by positivity
  set d0 := rlFlD n dR with hd0
  -- hypotheses of `rl_sym_full` for the floored datum
  have h45 : (4 : ℚ) / 5 ≤ d0.G1 := by
    have e1 : ((4 * m : ℤ) : ℝ) / n = 4 / 5 := by
      rw [hm]; push_cast; field_simp
    have e2 : ((4 * m : ℤ) : ℚ) / n = 4 / 5 := by
      rw [hm]; push_cast; field_simp
    have := rlFl_ge_int hn (4 * m) (x := rlMin3R dR.G1) (by rw [e1]; exact le_rlMin3R hG1)
    rw [e2] at this; exact this
  have hz : ∀ {x : ℝ}, 0 ≤ x → (0 : ℚ) ≤ rlFl n x := fun {x} hx => by
    have := rlFl_ge_int hn 0 (x := x) (by simpa using hx); simpa using this
  have hV1' : (1 : ℚ) ≤ d0.V1 := by
    have := rlFl_ge_int hn (n : ℤ) (x := dR.V1) (by push_cast; rw [div_self hnR.ne']; exact hV1)
    have e : ((n : ℤ) : ℚ) / n = 1 := by
      push_cast; exact div_self (by exact_mod_cast hn.ne')
    rw [e] at this; exact this
  obtain ⟨Ts, M0, hM0⟩ := rl_sym_full d0 h45 (rlFl_mono ((rlMin3R_le _ 0).trans (hGV 0)))
    (hz (le_rlMin3R hF1)) (rlFl_mono ((rlMin3R_le _ 0).trans (hF1V 0))) hV1' (hz (le_rlMin3R hG2))
    (hz (le_rlMin3R hF2)) (rlFl_mono ((rlMin3R_le _ 0).trans (hG2V 0)))
    (rlFl_mono ((rlMin3R_le _ 0).trans (hF2V 0))) ht0 ht
  -- `Ts < 8` from (P)
  have hTs : Ts < 8 := by
    by_contra hT
    have h := hM0.2.2.2 (Ts % 8) (Nat.mod_lt _ (by decide)) (by omega)
    have e : rlPS M0 Ts = rlPS M0 (Ts % 8) := by simp [rlPS, rlS3, rlM, Nat.mod_mod]
    linarith
  have hV2 : 0 ≤ dR.V2 := (hG2 0).trans (hG2V 0)
  have hwdR : ∀ u i, 0 ≤ rlWdR dR u i := by
    intro u i; unfold rlWdR; split_ifs <;> linarith
  have hM0v : ∀ (u : Fin 8) (i : Fin 3), rlM M0 u i = M0 u i := by
    intro u i; simp [rlM, Nat.mod_eq_of_lt u.2, Nat.mod_eq_of_lt i.2]
  have hbox0 : ∀ (u : Fin 8) (i : Fin 3),
      ((rlLo d0 u i : ℚ) : ℝ) ≤ (M0 u i : ℝ) ∧ (M0 u i : ℝ) ≤ ((rlLo d0 u i + rlWd d0 u i : ℚ) : ℝ) := by
    intro u i
    have h := hM0.1 u u.2 i i.2
    rw [hM0v] at h
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  set ω' := ω + 1 / n with hω'
  set M : Fin 8 → Fin 3 → ℝ := fun u i => max (M0 u i : ℝ) (rlLoR dR u i) with hM
  have hclose : ∀ u i, |M u i - (fun u i => (M0 u i : ℝ)) u i| ≤ ω' := by
    intro u i
    simp only [hM]
    have hb := hbox0 u i
    have hl := rlLo_flD_le hn dR hω hw u i
    rw [abs_le]; constructor
    · have := le_max_left (M0 u i : ℝ) (rlLoR dR u i); linarith
    · rcases le_total (M0 u i : ℝ) (rlLoR dR u i) with h | h
      · rw [max_eq_right h]; linarith [hb.1, hl.2]
      · rw [max_eq_left h]; linarith
  have hstar : lp3CStar ∈ lp3Profiles := by decide +kernel
  set c0 : ℝ := ((d0.G1 : ℚ) : ℝ) with hc0
  have hc0G : ∀ i, c0 ≤ dR.G1 i ∧ dR.G1 i - c0 ≤ ω' := fun i => rlFl_min_close hn (fun j => (hw j).1) i
  have hc45 : (4 : ℝ) / 5 ≤ c0 := by
    have h : (((4 : ℚ) / 5 : ℚ) : ℝ) ≤ c0 := by rw [hc0]; exact_mod_cast h45
    norm_num at h; exact h
  refine ⟨Ts, hTs, M, c0, hc45, fun i => (hc0G i).1,
    fun i => by linarith [(hc0G i).2], fun u i => ?_, ?_, fun C hC hne => ?_, fun u hu hne => ?_⟩
  · have hb := hbox0 u i
    have hl := rlLo_flD_le hn dR hω hw u i
    have hwd := rlWd_flD_le hn dR u i
    push_cast at hb
    refine ⟨le_max_right _ _, max_le (by linarith [hb.2, hl.1]) (by linarith [hwdR u i])⟩
  · have hp := abs_le.1 (rlV8R_pert hstar Ts hclose)
    rw [rlV8R_cast] at hp
    have hv : 8 * c0 * (5 / 3 - (t : ℝ)) ≤ ((rlV8 lp3CStar Ts M0 : ℚ) : ℝ) := by
      have h : ((8 * d0.G1 * (5 / 3 - t) : ℚ) : ℝ) ≤ ((rlV8 lp3CStar Ts M0 : ℚ) : ℝ) := by
        exact_mod_cast hM0.2.1
      push_cast at h; rw [hc0]; linarith
    linarith [hp.1]
  · have hω0 : 0 ≤ ω' := by positivity
    have hcc : (1 : ℝ) ≤ (cd_cc 3 C : ℝ) := by
      have := profiles3_cc_pos C (by simpa [profiles3] using hC); exact_mod_cast this
    have hg : 1 / 20 * c0 * (t : ℝ) ≤ ((rlV8 C Ts M0 : ℚ) : ℝ) / (8 * (cd_cc 3 C : ℝ)) -
        ((rlV8 lp3CStar Ts M0 : ℚ) : ℝ) / 40 := by
      have h : ((1 / 20 * d0.G1 * t : ℚ) : ℝ) ≤
          ((rlV8 C Ts M0 / (8 * (cd_cc 3 C : ℚ)) - rlV8 lp3CStar Ts M0 / 40 : ℚ) : ℝ) := by
        exact_mod_cast hM0.2.2.1 C hC hne
      push_cast at h; rw [hc0]; linarith
    have pc := rlV8R_pert hC Ts hclose
    rw [rlV8R_cast] at pc
    have ps := rlV8R_pert hstar Ts hclose
    rw [rlV8R_cast] at ps
    have e1 : |rlV8R C Ts M / (8 * (cd_cc 3 C : ℝ)) - ((rlV8 C Ts M0 : ℚ) : ℝ) / (8 * (cd_cc 3 C : ℝ))| ≤
        36 * ω' / 8 := by
      have hc8 : (0 : ℝ) < 8 * (cd_cc 3 C : ℝ) := by linarith
      rw [← sub_div, abs_div, abs_of_pos hc8, div_le_iff₀ hc8]
      nlinarith
    have e2 : |rlV8R lp3CStar Ts M / 40 - ((rlV8 lp3CStar Ts M0 : ℚ) : ℝ) / 40| ≤ 36 * ω' / 40 := by
      rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 40)]
      linarith
    have e1' := abs_le.1 e1
    have e2' := abs_le.1 e2
    linarith [e1'.1, e2'.2]
  · have a1 := abs_le.1 (rlPSR_pert hclose Ts)
    have a2 := abs_le.1 (rlPSR_pert hclose u)
    rw [rlPSR_cast] at a1 a2
    have hp : (1 : ℝ) / 20 ≤ ((rlPS M0 Ts : ℚ) : ℝ) - ((rlPS M0 u : ℚ) : ℝ) := by
      have h : ((1 / 20 : ℚ) : ℝ) ≤ ((rlPS M0 Ts - rlPS M0 u : ℚ) : ℝ) := by
        exact_mod_cast hM0.2.2.2 u hu hne
      push_cast at h; linarith
    linarith [a1.1, a2.2]

end Census
end IIT
