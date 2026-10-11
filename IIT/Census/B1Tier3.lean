/-
Census, module B1UnivMIP part 3: Tier 3 (W3 Theorem 5.1) at the profile level, with Lemma G'
(W10) in place of the gap hypothesis.

If the value of every partition of `univ` at a fixed pair is
`min (β · pos Σⱼ λᶜⱼ(Cⱼ)) (e · pos Σⱼ λᵉⱼ(Cⱼ))` (Lemma V, `univ_sysPhiAt_eq`), both sides satisfy
the W10 hypotheses with `λ_min = min_j F_j`, and the single-cut values `ph_j` have no exact tie,
then `φ_s` at that pair is `min_j ph_j`.
-/
import IIT.Census.B1Classify
import IIT.Census.BigPhiSys
import IIT.Census.B1UnivSys

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

lemma profile_splitAt_self (j : Fin N) (hr : ((univ : Finset (Fin N)).erase j).Nonempty) :
    profile (splitAt (mem_univ j) hr) j = univ.erase j := by
  unfold profile; rw [splitAt_partOf_j, splitAt_cut_j]

lemma profile_splitAt_ne {j i : Fin N} (hr : ((univ : Finset (Fin N)).erase j).Nonempty)
    (hij : i ≠ j) : profile (splitAt (mem_univ j) hr) i = ∅ := by
  unfold profile
  rw [splitAt_partOf_rest (mem_univ j) hr (mem_erase.2 ⟨hij, mem_univ i⟩), splitAt_cut_rest]

lemma sum_profile_splitAt (lam : Fin N → Finset (Fin N) → ℝ) (hl : ∀ i, lam i ∅ = 0) (j : Fin N)
    (hr : ((univ : Finset (Fin N)).erase j).Nonempty) :
    ∑ i, lam i (profile (splitAt (mem_univ j) hr) i) = kF lam j := by
  rw [← add_sum_erase _ _ (mem_univ j), profile_splitAt_self, sum_eq_zero, add_zero]
  · rfl
  · intro i hi
    rw [profile_splitAt_ne hr (ne_of_mem_erase hi), hl]

lemma kE_eq (lam : Fin N → Finset (Fin N) → ℝ) (lmin : ℝ) (C : Fin N → Finset (Fin N)) :
    kE lam lmin C = ((N : ℝ) - 1) * ∑ j, lam j (C j) - lmin * ∑ j, ((C j).card : ℝ) := by
  unfold kE kDelta
  rw [sum_sub_distrib, mul_sum, mul_sum]

section Tier3

variable (T : UnitTPM N) (u s tc te : State N)
  {lc le : Fin N → Finset (Fin N) → ℝ} {β e lc0 le0 ac ae : ℝ} {epc epe : ℕ → ℝ} {D dstar : ℕ}

/-- The single-cut value `ph_j = min(β Fᶜⱼ, e Fᵉⱼ)`. -/
def phT (lc le : Fin N → Finset (Fin N) → ℝ) (β e : ℝ) (j : Fin N) : ℝ :=
  min (β * kF lc j) (e * kF le j)

/-- **Tier 3** (W3 Theorem 5.1, with Lemma G'). -/
theorem tier3_profile (hN : 2 ≤ N) (hβ : 0 < β) (he : 0 < e)
    (hval : ∀ θ : SysPartition N univ, sysPhiAt T univ u θ s tc te =
      min (β * pos (∑ j, lc j (profile θ j))) (e * pos (∑ j, le j (profile θ j))))
    (hc : KeyHyp lc lc0 ac epc D dstar) (hee : KeyHyp le le0 ae epe D dstar)
    (hcmin : ∃ j, kF lc j = lc0) (hemin : ∃ j, kF le j = le0)
    (hT : ∀ j j', j ≠ j' → phT lc le β e j ≠ phT lc le β e j')
    (jst : Fin N) (hjst : ∀ j, phT lc le β e jst ≤ phT lc le β e j) :
    sysPhiOfState T univ u s tc te = phT lc le β e jst := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hr : ((univ : Finset (Fin N)).erase jst).Nonempty := by
    obtain ⟨x, hx⟩ : ∃ x : Fin N, x ≠ jst := by
      by_contra h; push Not at h
      have : (univ : Finset (Fin N)).card ≤ 1 :=
        card_le_one.2 fun a _ b _ => (h a).trans (h b).symm
      rw [card_univ, Fintype.card_fin] at this; omega
    exact ⟨x, mem_erase.2 ⟨hx, mem_univ x⟩⟩
  set θs := splitAt (mem_univ jst) hr
  have hFc : ∀ j, 0 < kF lc j := fun j => lt_of_lt_of_le hc.hP (hc.hmin j)
  have hFe : ∀ j, 0 < kF le j := fun j => lt_of_lt_of_le hee.hP (hee.hmin j)
  have hvs : sysPhiAt T univ u θs s tc te = phT lc le β e jst := by
    rw [hval, sum_profile_splitAt lc hc.lam_empty, sum_profile_splitAt le hee.lam_empty, phT,
      pos, pos, max_eq_right (hFc jst).le, max_eq_right (hFe jst).le]
  have hccs : (sysCutCount θs : ℝ) = (N : ℝ) - 1 := by
    rw [sysCutCount_splitAt, card_univ, Fintype.card_fin, Nat.cast_sub (by omega)]; simp
  -- `ph_jst` is at most `β λᶜ_min` and `e λᵉ_min`
  have hphc : phT lc le β e jst ≤ β * lc0 := by
    obtain ⟨j, hj⟩ := hcmin
    exact (hjst j).trans ((min_le_left _ _).trans (by rw [hj]))
  have hphe : phT lc le β e jst ≤ e * le0 := by
    obtain ⟨j, hj⟩ := hemin
    exact (hjst j).trans ((min_le_right _ _).trans (by rw [hj]))
  rw [sysPhiOfState_eq_of_strict T univ u θs s tc te, hvs]
  intro θ hθ
  obtain ⟨j0, -, hj0⟩ := hθ
  rw [hvs, hccs]
  have hccpos : (0 : ℝ) < sysCutCount θ := by exact_mod_cast sysCutCount_pos θ
  have hcc : (sysCutCount θ : ℝ) = ∑ j, ((profile θ j).card : ℝ) := by
    rw [sysCutCount_eq_sum_profile]; push_cast; rfl
  rw [div_lt_div_iff₀ hn1 hccpos]
  set Λc := ∑ j, lc j (profile θ j) with hΛc
  set Λe := ∑ j, le j (profile θ j) with hΛe
  set cc : ℝ := ∑ j, ((profile θ j).card : ℝ) with hccdef
  have hph0 : 0 ≤ phT lc le β e jst :=
    le_min (mul_nonneg hβ.le (hFc jst).le) (mul_nonneg he.le (hFe jst).le)
  rw [hval, hcc, min_mul_of_nonneg _ _ hn1.le]
  have herase : ∀ j : Fin N, (univ.erase j) ≠ ∅ := fun j h => by
    have := card_erase_of_mem (mem_univ j)
    rw [h, card_empty, card_univ, Fintype.card_fin] at this; omega
  by_cases hf : ∀ j, profile θ j = ∅ ∨ profile θ j = univ.erase j
  · -- a union of full cuts `J`, different from `{jst}`: Lemma J
    set J := univ.filter fun j => profile θ j ≠ ∅ with hJ
    have hsumJ : ∀ lam : Fin N → Finset (Fin N) → ℝ, (∀ i, lam i ∅ = 0) →
        ∑ j, lam j (profile θ j) = ∑ j ∈ J, kF lam j := by
      intro lam hl
      rw [hJ, sum_filter]
      refine sum_congr rfl fun j _ => ?_
      rcases hf j with h0 | h1
      · rw [h0, hl, if_neg (by simp)]
      · rw [if_pos (by rw [h1]; exact herase j), h1]
        rfl
    have hccJ : cc = J.card * ((N : ℝ) - 1) := by
      rw [hccdef, hJ, ← sum_filter_add_sum_filter_not univ (fun j => profile θ j ≠ ∅)]
      rw [sum_eq_zero (s := univ.filter fun j => ¬profile θ j ≠ ∅) (fun j hj => by
        rw [not_not.1 (mem_filter.1 hj).2]; simp), add_zero]
      rw [sum_congr rfl fun j hj => by
        rw [(hf j).resolve_left (mem_filter.1 hj).2, card_erase_of_mem (mem_univ j), card_univ,
          Fintype.card_fin, Nat.cast_sub (by omega)]]
      rw [sum_const, nsmul_eq_mul]; push_cast; ring
    have hJne : J.Nonempty := by
      rw [nonempty_iff_ne_empty]; intro h
      rw [hcc, hccJ, h, card_empty] at hccpos; simp at hccpos
    obtain ⟨i, hiJ, hij⟩ : ∃ i ∈ J, i ≠ jst := by
      by_contra hno
      push Not at hno
      apply hj0
      by_cases h0 : j0 = jst
      · subst h0
        rw [profile_splitAt_self]
        refine (hf j0).resolve_left fun he => ?_
        obtain ⟨k, hk⟩ := hJne
        have := hno k hk; subst this
        exact (mem_filter.1 hk).2 he
      · rw [profile_splitAt_ne hr h0]
        by_contra hne
        exact h0 (hno j0 (mem_filter.2 ⟨mem_univ _, hne⟩))
    have hlt : (J.card : ℝ) * phT lc le β e jst < ∑ j ∈ J, phT lc le β e j := by
      have := sum_lt_sum (s := J) (f := fun _ => phT lc le β e jst)
        (g := fun j => phT lc le β e j) (fun j _ => hjst j)
        ⟨i, hiJ, lt_of_le_of_ne (hjst i) (hT i jst hij).symm⟩
      simpa [sum_const, nsmul_eq_mul] using this
    have hmin := sum_min_le_min_sum J (fun j => β * kF lc j) (fun j => e * kF le j)
    rw [← mul_sum, ← mul_sum] at hmin
    have hpc : pos Λc = ∑ j ∈ J, kF lc j := by
      rw [hΛc, hsumJ lc hc.lam_empty, pos, max_eq_right (sum_nonneg fun j _ => (hFc j).le)]
    have hpe : pos Λe = ∑ j ∈ J, kF le j := by
      rw [hΛe, hsumJ le hee.lam_empty, pos, max_eq_right (sum_nonneg fun j _ => (hFe j).le)]
    rw [hpc, hpe, ← min_mul_of_nonneg _ _ hn1.le, hccJ]
    have : ∑ j ∈ J, phT lc le β e j ≤ min (β * ∑ j ∈ J, kF lc j) (e * ∑ j ∈ J, kF le j) := hmin
    nlinarith [mul_lt_mul_of_pos_right hlt hn1, mul_le_mul_of_nonneg_right this hn1.le]
  · -- not a union of full cuts: both excesses are positive (Lemma G'), then Lemma D(b)
    have hEc := (kE_profile θ hc hN).resolve_right hf
    have hEe := (kE_profile θ hee hN).resolve_right hf
    rw [kE_eq] at hEc hEe
    have hcc0 : 0 ≤ cc := le_of_lt (by rw [← hcc]; exact hccpos)
    have hΛc0 : 0 < Λc := by
      by_contra h; push Not at h
      nlinarith [mul_nonneg hc.hP.le hcc0, mul_nonpos_iff.2 (Or.inl ⟨hn1.le, h⟩)]
    have hΛe0 : 0 < Λe := by
      by_contra h; push Not at h
      nlinarith [mul_nonneg hee.hP.le hcc0, mul_nonpos_iff.2 (Or.inl ⟨hn1.le, h⟩)]
    rw [pos, pos, max_eq_right hΛc0.le, max_eq_right hΛe0.le]
    refine lt_min ?_ ?_
    · have h1 : phT lc le β e jst * cc ≤ β * lc0 * cc := mul_le_mul_of_nonneg_right hphc hcc0
      have h2 : β * (lc0 * cc) < β * (((N : ℝ) - 1) * Λc) := mul_lt_mul_of_pos_left (by linarith) hβ
      nlinarith
    · have h1 : phT lc le β e jst * cc ≤ e * le0 * cc := mul_le_mul_of_nonneg_right hphe hcc0
      have h2 : e * (le0 * cc) < e * (((N : ℝ) - 1) * Λe) := mul_lt_mul_of_pos_left (by linarith) he
      nlinarith

end Tier3

end Census
end IIT
