/-
Census, module B1UnivMIP part 1: the one-sided key lemma (W3 Lemma 4.2), in the corrected form
of W10 (Lemma G': the gap hypothesis replaced by (B_mid), (B_far) and (LS)).

Everything here is abstract: one side's data `lam j C` and a profile `C : Fin N → Finset (Fin N)`.
The combinatorics of system partitions enters only through four *shapes* of the profile
(W3 §3 Cases 1, 2a, 2b, 2c); a separate module shows that every partition of `univ` has one.

`δⱼ = (N-1)·λⱼ(Cⱼ) - λ_min·|Cⱼ|`, `E = Σⱼ δⱼ`.  Conclusion: `E ≥ 0`, and `E > 0` unless every
`Cⱼ` is empty or the full cut `univ.erase j`.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

section KeyLemma

variable (lam : Fin N → Finset (Fin N) → ℝ) (lmin : ℝ)

/-- `Fⱼ = λⱼ(U \ {j})`, the full-cut value. -/
def kF (j : Fin N) : ℝ := lam j (univ.erase j)

/-- `δⱼ` for the profile `C`. -/
def kDelta (C : Fin N → Finset (Fin N)) (j : Fin N) : ℝ :=
  ((N : ℝ) - 1) * lam j (C j) - lmin * (C j).card

/-- The excess `E = Σⱼ δⱼ`. -/
def kE (C : Fin N → Finset (Fin N)) : ℝ := ∑ j, kDelta lam lmin C j

/-- `M(K) = Σ_{j ∉ K} min(λⱼ(K), Fⱼ - λ_min)`. -/
def kM (K : Finset (Fin N)) : ℝ := ∑ j ∈ Kᶜ, min (lam j K) (kF lam j - lmin)

/-- The hypotheses of Lemma G' (W10 §1) except the small-cut hypothesis (H). -/
structure KeyHyp0 (a : ℝ) (eps : ℕ → ℝ) (D dstar : ℕ) : Prop where
  lam_empty : ∀ j, lam j ∅ = 0
  hP : 0 < lmin
  hmin : ∀ j, lmin ≤ kF lam j
  ha : 0 ≤ a
  hA : ∀ j C, j ∉ C → C.Nonempty → -a ≤ lam j C
  hD : 1 ≤ D
  hDd : 2 * D ≤ dstar
  hBmid : ∀ j C, j ∉ C → D ≤ C.card → kF lam j - eps C.card ≤ lam j C
  eps_nonneg : ∀ d, 0 ≤ eps d
  eps_anti : ∀ d d', D ≤ d → d ≤ d' → eps d' ≤ eps d
  hBfar : ∀ d, dstar ≤ d → d + 2 ≤ N → ((N : ℝ) - 1) * eps d < lmin
  hS : ∀ A : Finset (Fin N), A.card < 2 * D →
    2 * D * (a + lmin) + N * eps D < ∑ j ∈ Aᶜ, (kF lam j - lmin)
  hLS : ∀ Q : Finset (Fin N), N - dstar < Q.card →
    Q.card * eps (2 * D) < ∑ j ∈ Q, (kF lam j - lmin)

/-- The hypotheses of Lemma G' (W10 §1). -/
structure KeyHyp (a : ℝ) (eps : ℕ → ℝ) (D dstar : ℕ) : Prop extends KeyHyp0 lam lmin a eps D dstar where
  hH : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < D →
    D * (a + 2 * lmin) + N * eps D < kM lam lmin K

/-! ### The four shapes (W3 §3) -/

/-- Case 1: a giant part `U \ K`, all of whose units are cut from `K`. -/
def Shape1 (D : ℕ) (C : Fin N → Finset (Fin N)) : Prop :=
  ∃ K : Finset (Fin N), 1 ≤ K.card ∧ K.card < D ∧ ∀ j ∉ K, C j = K

/-- Case 2a: outside a small set `O` every cut is big. -/
def Shape2a (D : ℕ) (C : Fin N → Finset (Fin N)) : Prop :=
  ∃ O : Finset (Fin N), O.card < 2 * D ∧ ∀ j ∉ O, D ≤ (C j).card

/-- Case 2b: a part `P` cut from a small `K`; units of `K` are uncut or big, the rest big. -/
def Shape2b (D : ℕ) (C : Fin N → Finset (Fin N)) : Prop :=
  ∃ P K : Finset (Fin N), Disjoint P K ∧ 1 ≤ K.card ∧ K.card < D ∧ (∀ j ∈ P, C j = K) ∧
    (∀ j ∈ K, C j = ∅ ∨ D ≤ (C j).card) ∧ ∀ j, j ∉ P → j ∉ K → D ≤ (C j).card

/-- Case 2c: no small cuts; the uncut set `Z` is small, or every cut contains `Z` and the
complements of the cuts are blocks (inputs parts). -/
def Shape2c (D : ℕ) (C : Fin N → Finset (Fin N)) : Prop :=
  (∀ j, C j = ∅ ∨ D ≤ (C j).card) ∧
    ((univ.filter fun j => C j = ∅).card < 2 * D ∨
      ∀ j, C j ≠ ∅ → (univ.filter fun i => C i = ∅) ⊆ C j ∧ ∀ i, i ∉ C j → C i = C j)

/-! ### Per-unit bounds -/

variable {lam lmin} {a : ℝ} {eps : ℕ → ℝ} {D dstar : ℕ}

lemma k_card_add_one {C : Finset (Fin N)} {j : Fin N} (hj : j ∉ C) : ((C.card : ℝ) + 1) ≤ N := by
  have h := card_le_univ (insert j C)
  rw [card_insert_of_notMem hj, Fintype.card_fin] at h
  exact_mod_cast h

lemma kDelta_gen (h : KeyHyp0 lam lmin a eps D dstar) {C : Fin N → Finset (Fin N)} {j : Fin N}
    (hj : j ∉ C j) : -(((N : ℝ) - 1) * (a + lmin)) ≤ kDelta lam lmin C j := by
  have hc := k_card_add_one hj
  have hN1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by have := (C j).card.cast_nonneg (α := ℝ); linarith
  unfold kDelta
  rcases (C j).eq_empty_or_nonempty with he | hne
  · rw [he, card_empty, Nat.cast_zero, mul_zero, sub_zero, h.lam_empty, mul_zero]
    nlinarith [h.ha, h.hP]
  · have h1 := h.hA j (C j) hj hne
    have h2 : lmin * (C j).card ≤ lmin * ((N : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) h.hP.le
    nlinarith

/-- A big cut: `δⱼ ≥ (N-1)(Fⱼ - λ_min - ε_d)` for any `D ≤ d ≤ |Cⱼ|`. -/
lemma kDelta_big (h : KeyHyp0 lam lmin a eps D dstar) {C : Fin N → Finset (Fin N)} {j : Fin N}
    (hj : j ∉ C j) {d : ℕ} (hDd : D ≤ d) (hd : d ≤ (C j).card) :
    ((N : ℝ) - 1) * (kF lam j - lmin - eps d) ≤ kDelta lam lmin C j := by
  have hc := k_card_add_one hj
  have hN1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by have := (C j).card.cast_nonneg (α := ℝ); linarith
  have h1 := h.hBmid j (C j) hj (hDd.trans hd)
  have h2 := h.eps_anti d (C j).card hDd hd
  have h3 : lmin * (C j).card ≤ lmin * ((N : ℝ) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) h.hP.le
  unfold kDelta
  have h4 : ((N : ℝ) - 1) * (kF lam j - eps d) ≤ ((N : ℝ) - 1) * lam j (C j) :=
    mul_le_mul_of_nonneg_left (by linarith) hN1
  nlinarith

/-- A far non-full cut: `δⱼ > (N-1)(Fⱼ - λ_min)`. -/
lemma kDelta_far (h : KeyHyp0 lam lmin a eps D dstar) {C : Fin N → Finset (Fin N)} {j : Fin N}
    (hj : j ∉ C j) (hd : dstar ≤ (C j).card) (hnf : (C j).card + 2 ≤ N) :
    ((N : ℝ) - 1) * (kF lam j - lmin) < kDelta lam lmin C j := by
  have hDd : D ≤ (C j).card := by have := h.hDd; omega
  have h1 := h.hBmid j (C j) hj hDd
  have h2 := h.hBfar _ hd hnf
  have hc : ((C j).card : ℝ) + 2 ≤ N := by exact_mod_cast hnf
  have hN1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by have := (C j).card.cast_nonneg (α := ℝ); linarith
  have h4 : ((N : ℝ) - 1) * (kF lam j - eps (C j).card) ≤ ((N : ℝ) - 1) * lam j (C j) :=
    mul_le_mul_of_nonneg_left (by linarith) hN1
  have h5 : lmin ≤ lmin * ((N : ℝ) - 1 - (C j).card) := by
    nlinarith [h.hP]
  unfold kDelta
  nlinarith

/-- The full cut: `δⱼ = (N-1)(Fⱼ - λ_min)`. -/
lemma kDelta_full {C : Fin N → Finset (Fin N)} {j : Fin N} (hfull : C j = univ.erase j) :
    kDelta lam lmin C j = ((N : ℝ) - 1) * (kF lam j - lmin) := by
  unfold kDelta kF
  rw [hfull, card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · exact absurd j.2 (by omega)
  · rw [Nat.cast_sub (by omega)]; push_cast; ring

/-- An empty cut: `δⱼ = 0`. -/
lemma kDelta_empty (h : KeyHyp0 lam lmin a eps D dstar) {C : Fin N → Finset (Fin N)} {j : Fin N}
    (he : C j = ∅) : kDelta lam lmin C j = 0 := by
  unfold kDelta; rw [he, h.lam_empty, card_empty]; simp

/-! ### The shape lemmas -/

lemma k_sum_split (C : Fin N → Finset (Fin N)) (A : Finset (Fin N)) :
    kE lam lmin C = ∑ j ∈ Aᶜ, kDelta lam lmin C j + ∑ j ∈ A, kDelta lam lmin C j := by
  unfold kE; rw [add_comm, sum_add_sum_compl]

lemma k_card_compl (A : Finset (Fin N)) : ((Aᶜ.card : ℕ) : ℝ) = (N : ℝ) - A.card := by
  rw [card_compl, Fintype.card_fin, Nat.cast_sub (by simpa using card_le_univ A)]

lemma k_sum_ge_card {A : Finset (Fin N)} {f : Fin N → ℝ} {c : ℝ} (h : ∀ j ∈ A, c ≤ f j) :
    (A.card : ℝ) * c ≤ ∑ j ∈ A, f j := by
  have := card_nsmul_le_sum A f c h
  simpa [nsmul_eq_mul] using this

/-- **Case 1.** -/
theorem kE_pos_shape1_K (h : KeyHyp0 lam lmin a eps D dstar) (hN : 2 ≤ N)
    {C : Fin N → Finset (Fin N)} (hC0 : ∀ j, j ∉ C j) (K : Finset (Fin N)) (hK1 : 1 ≤ K.card)
    (hKD : K.card < D) (hCK : ∀ j ∉ K, C j = K)
    (hHK : D * (a + 2 * lmin) + N * eps D < kM lam lmin K) :
    0 < kE lam lmin C := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [k_sum_split C K]
  have hin : ∑ j ∈ Kᶜ, kDelta lam lmin C j =
      ((N : ℝ) - 1) * ∑ j ∈ Kᶜ, lam j K - (Kᶜ.card : ℝ) * (lmin * K.card) := by
    have hc' : (Kᶜ.card : ℝ) * (lmin * K.card) = ∑ _j ∈ Kᶜ, lmin * (K.card : ℝ) := by
      rw [sum_const, nsmul_eq_mul]
    rw [mul_sum, hc', ← sum_sub_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [kDelta, hCK j (mem_compl.1 hj)]
  have hM : kM lam lmin K ≤ ∑ j ∈ Kᶜ, lam j K := sum_le_sum fun j _ => min_le_left _ _
  have hK : ∑ j ∈ K, kDelta lam lmin C j ≥ (K.card : ℝ) * (-(((N : ℝ) - 1) * (a + lmin))) :=
    k_sum_ge_card fun j _ => kDelta_gen h (hC0 j)
  have hH := hHK
  have hc := k_card_compl K
  have hk1 : (1 : ℝ) ≤ K.card := by exact_mod_cast hK1
  have hkD : (K.card : ℝ) ≤ D := by exact_mod_cast hKD.le
  have hε := h.eps_nonneg D
  have h1 : ((N : ℝ) - 1) * kM lam lmin K ≤ ((N : ℝ) - 1) * ∑ j ∈ Kᶜ, lam j K :=
    mul_le_mul_of_nonneg_left hM (by linarith)
  have h2 : (Kᶜ.card : ℝ) * (lmin * K.card) ≤ ((N : ℝ) - 1) * (lmin * K.card) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg h.hP.le (by linarith))
  have h3 : (K.card : ℝ) * (a + 2 * lmin) ≤ D * (a + 2 * lmin) :=
    mul_le_mul_of_nonneg_right hkD (by linarith [h.ha, h.hP])
  have h4 : 0 < ((N : ℝ) - 1) * (kM lam lmin K - K.card * (a + 2 * lmin)) :=
    mul_pos (by linarith) (by nlinarith [mul_nonneg (N.cast_nonneg (α := ℝ)) hε])
  nlinarith

/-- **Case 2a.** -/
theorem kE_pos_shape2a (h : KeyHyp0 lam lmin a eps D dstar) (hN : 2 ≤ N)
    {C : Fin N → Finset (Fin N)} (hC0 : ∀ j, j ∉ C j) (hs : Shape2a D C) :
    0 < kE lam lmin C := by
  obtain ⟨O, hO, hbig⟩ := hs
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [k_sum_split C O]
  have h1 : ∑ j ∈ Oᶜ, ((N : ℝ) - 1) * (kF lam j - lmin - eps D) ≤
      ∑ j ∈ Oᶜ, kDelta lam lmin C j :=
    sum_le_sum fun j hj => kDelta_big h (hC0 j) le_rfl (hbig j (mem_compl.1 hj))
  have h1' : ∑ j ∈ Oᶜ, ((N : ℝ) - 1) * (kF lam j - lmin - eps D) =
      ((N : ℝ) - 1) * (∑ j ∈ Oᶜ, (kF lam j - lmin) - Oᶜ.card * eps D) := by
    rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul]
  have h2 : ∑ j ∈ O, kDelta lam lmin C j ≥ (O.card : ℝ) * (-(((N : ℝ) - 1) * (a + lmin))) :=
    k_sum_ge_card fun j _ => kDelta_gen h (hC0 j)
  have hS := h.hS O hO
  have hc := k_card_compl O
  have hε := h.eps_nonneg D
  have hoD : (O.card : ℝ) ≤ 2 * D := by exact_mod_cast hO.le
  have h3 : (Oᶜ.card : ℝ) * eps D ≤ N * eps D :=
    mul_le_mul_of_nonneg_right (by have := O.card.cast_nonneg (α := ℝ); linarith) hε
  have h4 : (O.card : ℝ) * (a + lmin) ≤ 2 * D * (a + lmin) :=
    mul_le_mul_of_nonneg_right hoD (by linarith [h.ha, h.hP])
  have h5 : 0 < ((N : ℝ) - 1) * (∑ j ∈ Oᶜ, (kF lam j - lmin) - Oᶜ.card * eps D -
      O.card * (a + lmin)) := mul_pos (by linarith) (by linarith)
  nlinarith

/-- **Case 2b.** -/
theorem kE_pos_shape2b_K (h : KeyHyp0 lam lmin a eps D dstar) (hN : 2 ≤ N)
    {C : Fin N → Finset (Fin N)} (hC0 : ∀ j, j ∉ C j) (P K : Finset (Fin N)) (hK1 : 1 ≤ K.card)
    (hKD : K.card < D) (hPK : ∀ j ∈ P, C j = K) (hKu : ∀ j ∈ K, C j = ∅ ∨ D ≤ (C j).card)
    (hrest : ∀ j, j ∉ P → j ∉ K → D ≤ (C j).card)
    (hHK : D * (a + 2 * lmin) + N * eps D < kM lam lmin K) :
    0 < kE lam lmin C := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hε := h.eps_nonneg D
  have hn1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by linarith
  have hk0 : (0 : ℝ) ≤ K.card := K.card.cast_nonneg
  set hv : Fin N → ℝ := fun j => if j ∈ P then lam j K else kF lam j - lmin with hvdef
  set c : ℝ := lmin * K.card + ((N : ℝ) - 1) * eps D with hcdef
  rw [k_sum_split C K]
  have hout : ∀ j ∈ Kᶜ, ((N : ℝ) - 1) * hv j - c ≤ kDelta lam lmin C j := by
    intro j hj
    have hjK := mem_compl.1 hj
    by_cases hjP : j ∈ P
    · simp only [hvdef, if_pos hjP, hcdef]
      rw [kDelta, hPK j hjP]
      nlinarith [mul_nonneg hn1 hε]
    · simp only [hvdef, if_neg hjP, hcdef]
      have := kDelta_big h (hC0 j) le_rfl (hrest j hjP hjK)
      nlinarith [mul_nonneg h.hP.le hk0]
  have hin : ∀ j ∈ K, -(((N : ℝ) - 1) * eps D) ≤ kDelta lam lmin C j := by
    intro j hj
    rcases hKu j hj with he | hb
    · rw [kDelta_empty h he]; nlinarith [mul_nonneg hn1 hε]
    · have := kDelta_big h (hC0 j) le_rfl hb
      have := h.hmin j
      nlinarith [mul_nonneg hn1 (sub_nonneg.2 (h.hmin j))]
  have s1 : ∑ j ∈ Kᶜ, (((N : ℝ) - 1) * hv j - c) ≤ ∑ j ∈ Kᶜ, kDelta lam lmin C j :=
    sum_le_sum hout
  have s1' : ∑ j ∈ Kᶜ, (((N : ℝ) - 1) * hv j - c) =
      ((N : ℝ) - 1) * ∑ j ∈ Kᶜ, hv j - Kᶜ.card * c := by
    rw [sum_sub_distrib, mul_sum, sum_const, nsmul_eq_mul]
  have s2 : (K.card : ℝ) * (-(((N : ℝ) - 1) * eps D)) ≤ ∑ j ∈ K, kDelta lam lmin C j :=
    k_sum_ge_card hin
  have hM : kM lam lmin K ≤ ∑ j ∈ Kᶜ, hv j := by
    refine sum_le_sum fun j _ => ?_
    simp only [hvdef]; split_ifs
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hH := hHK
  have hc := k_card_compl K
  have hk1 : (1 : ℝ) ≤ K.card := by exact_mod_cast hK1
  have hkD : (K.card : ℝ) < D := by exact_mod_cast hKD
  have h1 : ((N : ℝ) - 1) * kM lam lmin K ≤ ((N : ℝ) - 1) * ∑ j ∈ Kᶜ, hv j :=
    mul_le_mul_of_nonneg_left hM hn1
  have h2 : (Kᶜ.card : ℝ) * (lmin * K.card) ≤ ((N : ℝ) - 1) * (lmin * K.card) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg h.hP.le hk0)
  have h3 : (K.card : ℝ) * lmin ≤ D * (a + 2 * lmin) := by nlinarith [h.ha, h.hP]
  have h4 : 0 < ((N : ℝ) - 1) * (kM lam lmin K - lmin * K.card - N * eps D) :=
    mul_pos (by linarith) (by nlinarith)
  have hexp : (Kᶜ.card : ℝ) * c + K.card * (((N : ℝ) - 1) * eps D) =
      (Kᶜ.card : ℝ) * (lmin * K.card) + N * (((N : ℝ) - 1) * eps D) := by
    rw [hcdef, hc]; ring
  nlinarith

/-- **Case 2c.** `E ≥ 0`, and `E > 0` unless every cut is empty or full. -/
theorem kE_shape2c (h : KeyHyp0 lam lmin a eps D dstar) (hN : 2 ≤ N)
    {C : Fin N → Finset (Fin N)} (hC0 : ∀ j, j ∉ C j) (hs : Shape2c D C) :
    0 < kE lam lmin C ∨ ∀ j, C j = ∅ ∨ C j = univ.erase j := by
  obtain ⟨hcut, hZ⟩ := hs
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  set Z := univ.filter fun j => C j = ∅ with hZdef
  have hmemZ : ∀ j, j ∈ Z ↔ C j = ∅ := fun j => by simp [hZdef]
  have hZδ : ∑ j ∈ Z, kDelta lam lmin C j = 0 :=
    sum_eq_zero fun j hj => kDelta_empty h ((hmemZ j).1 hj)
  have hbigZ : ∀ j ∉ Z, D ≤ (C j).card := fun j hj =>
    (hcut j).resolve_left fun he => hj ((hmemZ j).2 he)
  by_cases hsmall : Z.card < 2 * D
  · -- `Z` small: spread over `Zᶜ`
    left
    rw [k_sum_split C Z, hZδ, add_zero]
    have h1 : ∑ j ∈ Zᶜ, ((N : ℝ) - 1) * (kF lam j - lmin - eps D) ≤
        ∑ j ∈ Zᶜ, kDelta lam lmin C j :=
      sum_le_sum fun j hj => kDelta_big h (hC0 j) le_rfl (hbigZ j (mem_compl.1 hj))
    have h1' : ∑ j ∈ Zᶜ, ((N : ℝ) - 1) * (kF lam j - lmin - eps D) =
        ((N : ℝ) - 1) * (∑ j ∈ Zᶜ, (kF lam j - lmin) - Zᶜ.card * eps D) := by
      rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul]
    have hS := h.hS Z hsmall
    have hc := k_card_compl Z
    have hε := h.eps_nonneg D
    have h3 : (Zᶜ.card : ℝ) * eps D ≤ N * eps D :=
      mul_le_mul_of_nonneg_right (by have := Z.card.cast_nonneg (α := ℝ); linarith) hε
    have h4 : 0 ≤ 2 * D * (a + lmin) := by
      have := h.ha; have := h.hP; positivity
    have h5 : 0 < ((N : ℝ) - 1) * (∑ j ∈ Zᶜ, (kF lam j - lmin) - Zᶜ.card * eps D) :=
      mul_pos hn1 (by linarith)
    linarith
  · have hstr := hZ.resolve_left hsmall
    push Not at hsmall
    -- the moderate units: cut, with a cut below `dstar`
    set Bg := univ.filter fun j => C j ≠ ∅ ∧ (C j).card < dstar with hBgdef
    have hmemB : ∀ j, j ∈ Bg ↔ C j ≠ ∅ ∧ (C j).card < dstar := fun j => by simp [hBgdef]
    have hsubC : ∀ j, j ∉ C j → C j ⊆ univ.erase j := fun j hj x hx =>
      mem_erase.2 ⟨fun h => hj (h ▸ hx), mem_univ x⟩
    -- every unit outside `Bg` has `δ ≥ (N-1)(F - λ_min) ≥ 0`, strictly if its cut is not full
    have hrest : ∀ j ∉ Bg, ((N : ℝ) - 1) * (kF lam j - lmin) ≤ kDelta lam lmin C j ∨
        C j = ∅ := by
      intro j hj
      by_cases he : C j = ∅
      · exact Or.inr he
      left
      by_cases hf : C j = univ.erase j
      · rw [kDelta_full hf]
      · have hd : dstar ≤ (C j).card := by
          by_contra hlt; push Not at hlt; exact hj ((hmemB j).2 ⟨he, hlt⟩)
        have hlt := card_lt_card (ssubset_of_subset_of_ne (hsubC j (hC0 j)) hf)
        rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin] at hlt
        exact (kDelta_far h (hC0 j) hd (by omega)).le
    have hrest0 : ∀ j ∉ Bg, 0 ≤ kDelta lam lmin C j := by
      intro j hj
      rcases hrest j hj with h1 | h1
      · exact le_trans (mul_nonneg hn1.le (sub_nonneg.2 (h.hmin j))) h1
      · rw [kDelta_empty h h1]
    have hBgj : ∀ j ∈ Bg, ((N : ℝ) - 1) * (kF lam j - lmin - eps (2 * D)) ≤
        kDelta lam lmin C j := by
      intro j hj
      have hne := ((hmemB j).1 hj).1
      have hZC := card_le_card (hstr j hne).1
      exact kDelta_big h (hC0 j) (by have := h.hD; omega) (le_trans hsmall hZC)
    have hBgδ : ((N : ℝ) - 1) * (∑ j ∈ Bg, (kF lam j - lmin) - Bg.card * eps (2 * D)) ≤
        ∑ j ∈ Bg, kDelta lam lmin C j := by
      have := sum_le_sum hBgj
      rwa [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul] at this
    have hcomp0 : 0 ≤ ∑ j ∈ Bgᶜ, kDelta lam lmin C j :=
      sum_nonneg fun j hj => hrest0 j (mem_compl.1 hj)
    rcases Bg.eq_empty_or_nonempty with hBe | ⟨j0, hj0⟩
    · -- no moderate unit
      by_cases hall : ∀ j, C j = ∅ ∨ C j = univ.erase j
      · exact Or.inr hall
      left
      push Not at hall
      obtain ⟨j, hje, hjf⟩ := hall
      have hjB : j ∉ Bg := by rw [hBe]; exact notMem_empty j
      have hd : dstar ≤ (C j).card := by
        by_contra hlt; push Not at hlt; exact hjB ((hmemB j).2 ⟨hje.ne_empty, hlt⟩)
      have hlt := card_lt_card (ssubset_of_subset_of_ne (hsubC j (hC0 j)) hjf)
      rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin] at hlt
      have hpos : 0 < kDelta lam lmin C j :=
        lt_of_le_of_lt (mul_nonneg hn1.le (sub_nonneg.2 (h.hmin j)))
          (kDelta_far h (hC0 j) hd (by omega))
      unfold kE
      exact sum_pos' (fun i _ => hrest0 i (by rw [hBe]; exact notMem_empty i))
        ⟨j, mem_univ j, hpos⟩
    · -- a moderate unit: its whole block is moderate, so (LS) applies to `Bg`
      left
      have hne0 := ((hmemB j0).1 hj0).1
      have hsub : (C j0)ᶜ ⊆ Bg := by
        intro i hi
        have hCi := (hstr j0 hne0).2 i (mem_compl.1 hi)
        rw [hmemB, hCi]; exact (hmemB j0).1 hj0
      have hcard : N - dstar < Bg.card := by
        have h1 := card_le_card hsub
        have h2 := k_card_compl (C j0)
        have h3 : (C j0)ᶜ.card = N - (C j0).card := by
          rw [card_compl, Fintype.card_fin]
        have h4 := ((hmemB j0).1 hj0).2
        have h5 : (C j0).card + 1 ≤ N := by
          have := card_le_univ (insert j0 (C j0))
          rwa [card_insert_of_notMem (hC0 j0), Fintype.card_fin] at this
        omega
      have hLS := h.hLS Bg hcard
      rw [k_sum_split C Bg]
      have : 0 < ((N : ℝ) - 1) * (∑ j ∈ Bg, (kF lam j - lmin) - Bg.card * eps (2 * D)) :=
        mul_pos hn1 (by linarith)
      linarith

/-- **Lemma G' (W10), one side.** If the profile has one of the four shapes, then `E > 0`
unless every cut is empty or full (a union of full cuts), in which case `E ≥ 0`. -/
theorem kE_key (h : KeyHyp lam lmin a eps D dstar) (hN : 2 ≤ N)
    {C : Fin N → Finset (Fin N)} (hC0 : ∀ j, j ∉ C j)
    (hs : Shape1 D C ∨ Shape2a D C ∨ Shape2b D C ∨ Shape2c D C) :
    0 < kE lam lmin C ∨ ∀ j, C j = ∅ ∨ C j = univ.erase j := by
  rcases hs with ⟨K, hK1, hKD, hCK⟩ | h2 | ⟨P, K, -, hK1, hKD, hPK, hKu, hrest⟩ | h4
  · exact Or.inl (kE_pos_shape1_K h.toKeyHyp0 hN hC0 K hK1 hKD hCK (h.hH K hK1 hKD))
  · exact Or.inl (kE_pos_shape2a h.toKeyHyp0 hN hC0 h2)
  · exact Or.inl (kE_pos_shape2b_K h.toKeyHyp0 hN hC0 P K hK1 hKD hPK hKu hrest (h.hH K hK1 hKD))
  · exact kE_shape2c h.toKeyHyp0 hN hC0 h4

/-- On a union of full cuts, `E = (N-1) Σ_{cut j} (Fⱼ - λ_min) ≥ 0`. -/
theorem kE_nonneg_of_full (h : KeyHyp0 lam lmin a eps D dstar) {C : Fin N → Finset (Fin N)}
    (hf : ∀ j, C j = ∅ ∨ C j = univ.erase j) : 0 ≤ kE lam lmin C := by
  unfold kE
  refine sum_nonneg fun j _ => ?_
  rcases hf j with he | hfull
  · rw [kDelta_empty h he]
  · rw [kDelta_full hfull]
    have : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by have := j.2; omega)
    exact mul_nonneg (by linarith) (sub_nonneg.2 (h.hmin j))

end KeyLemma

end Census
end IIT
