/-
Census, W3 Theorem 6.1 (Tier 1'), step 1, with Lemma G' (W10).

If the small-cut hypothesis (H) holds for every `K` except the singleton `{x}` (the failing unit), the key lemma
still gives `E > 0` for every profile, except unions of full cuts and the profiles of the family `𝓕_x`:
Shape 1 with `K = {x}` (everyone outside `x` is cut from `x`) and Shape 2b with `K = {x}`.
-/
import IIT.Census.B1Tier3

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- The profiles of the family `𝓕_x` (W3 C10), in the shape language of `B1KeyLemma`. -/
def FamFx (D : ℕ) (x : Fin N) (C : Fin N → Finset (Fin N)) : Prop :=
  (∀ j, j ≠ x → C j = {x}) ∨
    ∃ P : Finset (Fin N), x ∉ P ∧ (∀ j ∈ P, C j = {x}) ∧ (C x = ∅ ∨ D ≤ (C x).card) ∧
      ∀ j, j ∉ P → j ≠ x → D ≤ (C j).card

section

variable {lam : Fin N → Finset (Fin N) → ℝ} {lmin a : ℝ} {eps : ℕ → ℝ} {D dstar : ℕ}

/-- **Tier 1, step 1 (abstract).** -/
theorem kE_key_fail (h : KeyHyp0 lam lmin a eps D dstar) (hN : 2 ≤ N) (x : Fin N)
    (hH : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < D → K ≠ {x} →
      D * (a + 2 * lmin) + N * eps D < kM lam lmin K)
    {C : Fin N → Finset (Fin N)} (hC0 : ∀ j, j ∉ C j)
    (hs : Shape1 D C ∨ Shape2a D C ∨ Shape2b D C ∨ Shape2c D C) :
    0 < kE lam lmin C ∨ (∀ j, C j = ∅ ∨ C j = univ.erase j) ∨ FamFx D x C := by
  rcases hs with ⟨K, hK1, hKD, hCK⟩ | h2 | ⟨P, K, hPK', hK1, hKD, hPK, hKu, hrest⟩ | h4
  · by_cases hKx : K = {x}
    · subst hKx
      exact Or.inr (Or.inr (Or.inl fun j hj => hCK j (by simpa using hj)))
    · exact Or.inl (kE_pos_shape1_K h hN hC0 K hK1 hKD hCK (hH K hK1 hKD hKx))
  · exact Or.inl (kE_pos_shape2a h hN hC0 h2)
  · by_cases hKx : K = {x}
    · subst hKx
      refine Or.inr (Or.inr (Or.inr ⟨P, ?_, hPK, hKu x (mem_singleton_self x), fun j hjP hjx =>
        hrest j hjP (by simpa using hjx)⟩))
      exact fun hxP => disjoint_left.1 hPK' hxP (mem_singleton_self x)
    · exact Or.inl (kE_pos_shape2b_K h hN hC0 P K hK1 hKD hPK hKu hrest (hH K hK1 hKD hKx))
  · rcases kE_shape2c h hN hC0 h4 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- `M₀(x) = Σ_{j ≠ x} min(λⱼ({x}), Fⱼ)`: the cut-from-`x` sum with the full-cut truncation. -/
def kM0 (lam : Fin N → Finset (Fin N) → ℝ) (x : Fin N) : ℝ :=
  ∑ j ∈ univ.erase x, min (lam j {x}) (kF lam j)

/-- **The value of an `𝓕_x` profile** (W7 §3 item 3): `Λ(C) ≥ M₀(x) - (N-1) ε_D - a`. -/
theorem famFx_Lambda_ge (h : KeyHyp0 lam lmin a eps D dstar) (x : Fin N)
    {C : Fin N → Finset (Fin N)} (hC0 : ∀ j, j ∉ C j) (hF : FamFx D x C) :
    kM0 lam x - ((N : ℝ) - 1) * eps D - a ≤ ∑ j, lam j (C j) := by
  have hx : -a ≤ lam x (C x) := by
    rcases (C x).eq_empty_or_nonempty with he | hne
    · rw [he, h.lam_empty]; linarith [h.ha]
    · exact h.hA x (C x) (hC0 x) hne
  have hcard : (((univ : Finset (Fin N)).erase x).card : ℝ) = (N : ℝ) - 1 := by
    rw [card_erase_of_mem (mem_univ x), card_univ, Fintype.card_fin,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (by have := x.2; omega))]; simp
  have hε := h.eps_nonneg D
  have hunit : ∀ j ∈ (univ : Finset (Fin N)).erase x,
      min (lam j {x}) (kF lam j) - eps D ≤ lam j (C j) := by
    intro j hj
    have hjx : j ≠ x := ne_of_mem_erase hj
    rcases hF with h1 | ⟨P, -, hP, -, hrest⟩
    · rw [h1 j hjx]; linarith [min_le_left (lam j {x}) (kF lam j)]
    · by_cases hjP : j ∈ P
      · rw [hP j hjP]; linarith [min_le_left (lam j {x}) (kF lam j)]
      · have := h.hBmid j (C j) (hC0 j) (hrest j hjP hjx)
        have := h.eps_anti D (C j).card le_rfl (hrest j hjP hjx)
        linarith [min_le_right (lam j {x}) (kF lam j)]
  have hsum := sum_le_sum hunit
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcard] at hsum
  rw [← add_sum_erase _ _ (mem_univ x)]
  unfold kM0
  linarith

/-- **Tier 1, step 1, for partitions of `univ`.** -/
theorem kE_profile_fail (θ : SysPartition N univ) (h : KeyHyp0 lam lmin a eps D dstar)
    (hN : 2 ≤ N) (x : Fin N)
    (hH : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < D → K ≠ {x} →
      D * (a + 2 * lmin) + N * eps D < kM lam lmin K) :
    0 < kE lam lmin (profile θ) ∨ (∀ j, profile θ j = ∅ ∨ profile θ j = univ.erase j) ∨
      FamFx D x (profile θ) :=
  kE_key_fail h hN x hH (profile_not_self θ) (profile_shape θ h.hD)

end

/-! ### Tier 1, step 2: the MIP is in `𝓕_x`, and the lower bound on `φ_s(univ)` -/

section Lower

variable (T : UnitTPM N) (u s tc te : State N)
  {lc le : Fin N → Finset (Fin N) → ℝ} {β e lc0 le0 ac ae : ℝ} {epc epe : ℕ → ℝ} {D dstar : ℕ}

/-- **Lower bound on `φ_s(univ)` when the unit `x` fails on the cause side** (W3 Theorem 6.1 + W7 §3 item 3).
Hypotheses: the value formula (Lemma V), the W10 hypotheses on both sides with (H) failing only at `{x}` on the
cause side, `λ_min` attained, and a partition beating the best single cut (W7's check V). -/
theorem phi_lower_fail (hN : 2 ≤ N) (hβ : 0 < β) (he : 0 < e)
    (hval : ∀ θ : SysPartition N univ, sysPhiAt T univ u θ s tc te =
      min (β * pos (∑ j, lc j (profile θ j))) (e * pos (∑ j, le j (profile θ j))))
    (hc : KeyHyp0 lc lc0 ac epc D dstar) (x : Fin N)
    (hHc : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < D → K ≠ {x} →
      D * (ac + 2 * lc0) + N * epc D < kM lc lc0 K)
    (hee : KeyHyp le le0 ae epe D dstar)
    (hcmin : ∃ j, kF lc j = lc0) (hemin : ∃ j, kF le j = le0)
    (jst : Fin N) (hjst : ∀ j, phT lc le β e jst ≤ phT lc le β e j)
    (hV : ∃ θm : SysPartition N univ, sysPhiAt T univ u θm s tc te / (sysCutCount θm : ℝ) <
      phT lc le β e jst / ((N : ℝ) - 1)) :
    min (β * (kM0 lc x - ((N : ℝ) - 1) * epc D - ac)) (e * (kM0 le x - ((N : ℝ) - 1) * epe D - ae))
      ≤ sysPhiOfState T univ u s tc te := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hFc : ∀ j, 0 < kF lc j := fun j => lt_of_lt_of_le hc.hP (hc.hmin j)
  have hFe : ∀ j, 0 < kF le j := fun j => lt_of_lt_of_le hee.hP (hee.hmin j)
  have hphc : phT lc le β e jst ≤ β * lc0 := by
    obtain ⟨j, hj⟩ := hcmin
    exact (hjst j).trans ((min_le_left _ _).trans (by rw [hj]))
  have hphe : phT lc le β e jst ≤ e * le0 := by
    obtain ⟨j, hj⟩ := hemin
    exact (hjst j).trans ((min_le_right _ _).trans (by rw [hj]))
  -- a member of the MIP set
  have : Nonempty (SysPartition N univ) := ⟨hV.choose⟩
  obtain ⟨θ, hθ⟩ := argminSet_nonempty
    (fun θ : SysPartition N univ => normalizedSysPhiAt T univ u θ s tc te)
  have hle : sysPhiAt T univ u θ s tc te ≤ sysPhiOfState T univ u s tc te := by
    unfold sysPhiOfState sup'OrZero
    split
    · exact le_sup' (fun θ => sysPhiAt T univ u θ s tc te) hθ
    · rename_i hne; exact absurd ⟨θ, hθ⟩ hne
  -- its ratio is below the best single cut's
  obtain ⟨θm, hθm⟩ := hV
  have hratio : sysPhiAt T univ u θ s tc te / (sysCutCount θ : ℝ) <
      phT lc le β e jst / ((N : ℝ) - 1) :=
    lt_of_le_of_lt ((mem_argminSet.1 hθ) θm) hθm
  have hccpos : (0 : ℝ) < sysCutCount θ := by exact_mod_cast sysCutCount_pos θ
  have hcc : (sysCutCount θ : ℝ) = ∑ j, ((profile θ j).card : ℝ) := by
    rw [sysCutCount_eq_sum_profile]; push_cast; rfl
  rw [div_lt_div_iff₀ hccpos hn1] at hratio
  -- so its profile is in `𝓕_x`
  have hfam : FamFx D x (profile θ) := by
    by_contra hnf
    set Λc := ∑ j, lc j (profile θ j) with hΛc
    set Λe := ∑ j, le j (profile θ j) with hΛe
    set cc : ℝ := ∑ j, ((profile θ j).card : ℝ) with hccdef
    rw [hval, hcc, min_mul_of_nonneg _ _ hn1.le] at hratio
    have herase : ∀ j : Fin N, (univ.erase j) ≠ ∅ := fun j h => by
      have := card_erase_of_mem (mem_univ j)
      rw [h, card_empty, card_univ, Fintype.card_fin] at this; omega
    by_cases hf : ∀ j, profile θ j = ∅ ∨ profile θ j = univ.erase j
    · -- union of full cuts: ratio ≥ ph_min/(N-1) (Lemma J), contradiction
      set J := univ.filter fun j => profile θ j ≠ ∅ with hJ
      have hsumJ : ∀ lam : Fin N → Finset (Fin N) → ℝ, (∀ i, lam i ∅ = 0) →
          ∑ j, lam j (profile θ j) = ∑ j ∈ J, kF lam j := by
        intro lam hl
        rw [hJ, sum_filter]
        refine sum_congr rfl fun j _ => ?_
        rcases hf j with h0 | h1
        · rw [h0, hl, if_neg (by simp)]
        · rw [if_pos (by rw [h1]; exact herase j), h1]; rfl
      have hccJ : cc = J.card * ((N : ℝ) - 1) := by
        rw [hccdef, hJ, ← sum_filter_add_sum_filter_not univ (fun j => profile θ j ≠ ∅)]
        rw [sum_eq_zero (s := univ.filter fun j => ¬profile θ j ≠ ∅) (fun j hj => by
          rw [not_not.1 (mem_filter.1 hj).2]; simp), add_zero]
        rw [sum_congr rfl fun j hj => by
          rw [(hf j).resolve_left (mem_filter.1 hj).2, card_erase_of_mem (mem_univ j), card_univ,
            Fintype.card_fin, Nat.cast_sub (by omega)]]
        rw [sum_const, nsmul_eq_mul]; push_cast; ring
      have hge : (J.card : ℝ) * phT lc le β e jst ≤ ∑ j ∈ J, phT lc le β e j := by
        have := sum_le_sum (s := J) fun j (_ : j ∈ J) => hjst j
        simpa [sum_const, nsmul_eq_mul] using this
      have hmin := sum_min_le_min_sum J (fun j => β * kF lc j) (fun j => e * kF le j)
      rw [← mul_sum, ← mul_sum] at hmin
      have hpc : pos Λc = ∑ j ∈ J, kF lc j := by
        rw [hΛc, hsumJ lc hc.lam_empty, pos, max_eq_right (sum_nonneg fun j _ => (hFc j).le)]
      have hpe : pos Λe = ∑ j ∈ J, kF le j := by
        rw [hΛe, hsumJ le hee.lam_empty, pos, max_eq_right (sum_nonneg fun j _ => (hFe j).le)]
      rw [hpc, hpe, ← min_mul_of_nonneg _ _ hn1.le, hccJ] at hratio
      have h1 : ∑ j ∈ J, phT lc le β e j ≤ min (β * ∑ j ∈ J, kF lc j) (e * ∑ j ∈ J, kF le j) := hmin
      nlinarith [mul_le_mul_of_nonneg_right hge hn1.le, mul_le_mul_of_nonneg_right h1 hn1.le]
    · -- otherwise both excesses are positive (Lemma G' / Tier 1 step 1), and Lemma D(b) contradicts
      have hEc : 0 < kE lc lc0 (profile θ) := by
        rcases kE_profile_fail θ hc hN x hHc with h | h | h
        · exact h
        · exact absurd h hf
        · exact absurd h hnf
      have hEe := (kE_profile θ hee hN).resolve_right hf
      rw [kE_eq] at hEc hEe
      have hcc0 : 0 ≤ cc := le_of_lt (by rw [← hcc]; exact hccpos)
      have hΛc0 : 0 < Λc := by
        by_contra h; push Not at h
        nlinarith [mul_nonneg hc.hP.le hcc0, mul_nonpos_iff.2 (Or.inl ⟨hn1.le, h⟩)]
      have hΛe0 : 0 < Λe := by
        by_contra h; push Not at h
        nlinarith [mul_nonneg hee.hP.le hcc0, mul_nonpos_iff.2 (Or.inl ⟨hn1.le, h⟩)]
      rw [pos, pos, max_eq_right hΛc0.le, max_eq_right hΛe0.le] at hratio
      rcases min_choice (β * Λc * ((N : ℝ) - 1)) (e * Λe * ((N : ℝ) - 1)) with hm | hm <;>
        rw [hm] at hratio
      · have h1 : phT lc le β e jst * cc ≤ β * lc0 * cc := mul_le_mul_of_nonneg_right hphc hcc0
        have h2 : β * (lc0 * cc) < β * (((N : ℝ) - 1) * Λc) := mul_lt_mul_of_pos_left (by linarith) hβ
        nlinarith
      · have h1 : phT lc le β e jst * cc ≤ e * le0 * cc := mul_le_mul_of_nonneg_right hphe hcc0
        have h2 : e * (le0 * cc) < e * (((N : ℝ) - 1) * Λe) := mul_lt_mul_of_pos_left (by linarith) he
        nlinarith
  -- the value of an `𝓕_x` member
  have hLc := famFx_Lambda_ge hc x (profile_not_self θ) hfam
  have hLe := famFx_Lambda_ge hee.toKeyHyp0 x (profile_not_self θ) hfam
  refine le_trans ?_ hle
  rw [hval]
  exact min_le_min
    (mul_le_mul_of_nonneg_left (hLc.trans (le_max_right _ _)) hβ.le)
    (mul_le_mul_of_nonneg_left (hLe.trans (le_max_right _ _)) he.le)

end Lower

end Census
end IIT
