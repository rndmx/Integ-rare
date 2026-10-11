/-
Census, B1 LTBetaHi, module T2: **the concrete triple stopping set** (W2 6.1, Lemma SS).

Choices (all reading only "safe" entries: `Topᶜ` columns, rows that are not light, and the row `s`):
* `lt3L w q :⇔ X_{Top^c}(q) > 3N/10` (light); `lt3Base = {tc, s} ∪ Sp`;
* `lt3Ex`: units of `Top` with a non-light flip `r^j` (`r ∈ Base`) or `|y_{s,j} - 1/2| < γ`;
* `lt3Q`: an agreement class of `Top \ Ex` for `Base` (`agree_class`); `qFam` its transversal family;
* `lt3F`: members all of whose rows `r^R` (`r ∈ Base`, `|R| ≥ 2`) are light;
* `lt3Sel = lt3F × Base` when `P(tc) > e^{-3N/10}` and `|Q| ≥ 7`, else `∅`;
* `lt3PB (S, r) = {(r^R, i) : R ⊆ S, i ∈ S, R ⊄ {i}}` (W2 5.1: all non-shared block positions).
Main result `lt3Priv_detOn`: `{Priv = A}` is `Aᶜ`-determined.
-/
import IIT.Census.B1LTHiSolid
import IIT.Census.B1LTHiFam
import IIT.Census.B1LTHiWindow

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-! ### The safe-set form of the abstract stopping lemma -/

theorem stPriv_stop_safe {κ : Type*} (Safe : Param N → Set (State N × Fin N)) (Sel : Param N → Finset κ)
    (PB : κ → Finset (State N × Fin N))
    (hSel : ∀ w w' : Param N, (∀ q ∈ Safe w, w q.1 q.2 = w' q.1 q.2) → Sel w' = Sel w)
    (hsafe : ∀ w, ∀ k ∈ Sel w, ∀ q ∈ PB k, q ∉ Safe w)
    {w w' : Param N} (h : ∀ q ∉ stPriv Sel PB w, w q.1 q.2 = w' q.1 q.2) :
    stPriv Sel PB w' = stPriv Sel PB w := by
  have : ∀ q ∈ Safe w, w q.1 q.2 = w' q.1 q.2 := fun q hq => h q fun hp => by
    obtain ⟨k, hk, hq'⟩ := mem_biUnion.1 hp
    exact hsafe w k hk q hq' hq
  unfold stPriv; rw [hSel w w' this]

theorem stPriv_detOn_safe {κ : Type*} (Safe : Param N → Set (State N × Fin N)) (Sel : Param N → Finset κ)
    (PB : κ → Finset (State N × Fin N))
    (hSel : ∀ w w' : Param N, (∀ q ∈ Safe w, w q.1 q.2 = w' q.1 q.2) → Sel w' = Sel w)
    (hsafe : ∀ w, ∀ k ∈ Sel w, ∀ q ∈ PB k, q ∉ Safe w) (A : Finset (State N × Fin N)) :
    DetOnE Aᶜ {w | stPriv Sel PB w = A} := by
  intro w w' hw
  show stPriv Sel PB w = A ↔ stPriv Sel PB w' = A
  constructor
  · intro hA
    rw [stPriv_stop_safe Safe Sel PB hSel hsafe (w := w) (w' := w')
      fun q hq => hw q (mem_compl.2 (hA ▸ hq)), hA]
  · intro hA
    rw [stPriv_stop_safe Safe Sel PB hSel hsafe (w := w') (w' := w)
      fun q hq => (hw q (mem_compl.2 (hA ▸ hq))).symm, hA]

/-! ### The concrete choices -/

section Inst

variable (s : State N) (ε γ : ℝ)

/-- Light rows: `X_{Top^c} > 3N/10`. -/
def lt3L (w : Param N) (q : State N) : Prop := 3 / 10 * (N : ℝ) < XMW w (lt3Top s w ε)ᶜ q

/-- The base rows `{tc, s} ∪ Sp`. -/
noncomputable def lt3Base (w : Param N) : Finset (State N) := insert (tcRow w) (insert s (lt2Sp w))

/-- Excluded units of `Top`. -/
noncomputable def lt3Ex (w : Param N) : Finset (Fin N) := by
  classical exact (lt3Top s w ε).filter fun j =>
    (∃ r ∈ lt3Base s w, ¬ lt3L s ε w (flip r j)) ∨ clamp01 (w s j) ∈ Set.Ioo (1 / 2 - γ) (1 / 2 + γ)

/-- The agreement class, as a function of its data. -/
noncomputable def lt3QOf (B : Finset (State N)) (U : Finset (Fin N)) (t : State N) : Finset (Fin N) :=
  (agree_class B U t).choose

lemma lt3QOf_spec (B : Finset (State N)) (U : Finset (Fin N)) (t : State N) :
    lt3QOf B U t ⊆ U ∧ U.card ≤ 2 ^ B.card * (lt3QOf B U t).card ∧
      ∀ r ∈ B, (∀ j ∈ lt3QOf B U t, r j = t j) ∨ (∀ j ∈ lt3QOf B U t, r j ≠ t j) :=
  (agree_class B U t).choose_spec

noncomputable def lt3Q (w : Param N) : Finset (Fin N) :=
  lt3QOf (lt3Base s w) (lt3Top s w ε \ lt3Ex s ε γ w) (tcRow w)

/-- Kept members. -/
noncomputable def lt3F (w : Param N) : Finset (Finset (Fin N)) := by
  classical exact (qFam (lt3Q s ε γ w)).filter fun S =>
    ∀ r ∈ lt3Base s w, ∀ R ⊆ S, 2 ≤ R.card → lt3L s ε w (flipS r R)

/-- The selection. -/
noncomputable def lt3Sel (w : Param N) : Finset (Finset (Fin N) × State N) := by
  classical exact
    if Real.exp (-(3 / 10 * (N : ℝ))) < Pw w (tcRow w) ∧ 7 ≤ (lt3Q s ε γ w).card then
      (lt3F s ε γ w) ×ˢ (lt3Base s w)
    else ∅

/-- The private block of member `S` and base row `r`. -/
noncomputable def lt3PB (k : Finset (Fin N) × State N) : Finset (State N × Fin N) := by
  classical exact ((k.1.powerset ×ˢ k.1).filter fun p => ¬ p.1 ⊆ {p.2}).image fun p => (flipS k.2 p.1, p.2)

/-- The safe positions: `Top^c` columns, rows that are not light, the row `s`. -/
def lt3Safe (w : Param N) : Set (State N × Fin N) :=
  {q | q.2 ∉ lt3Top s w ε ∨ ¬ lt3L s ε w q.1 ∨ q.1 = s}

end Inst

/-! ### Stability of the choices -/

lemma flipS_single (r : State N) (j : Fin N) : flipS r {j} = flip r j := by
  funext i
  by_cases h : i = j
  · subst h; simp [flipS, flip]
  · simp [flipS, flip, h]

/-- If `P(tc) ≤ e^{-cN}` at `w`, the same holds at `w'` (changes only in `C₀`-agreeing light rows). -/
lemma lt3_small_stable (C0 : Finset (Fin N)) (c : ℝ) {w w' : Param N}
    (hP : Pw w (tcRow w) ≤ Real.exp (-(c * N)))
    (hC : ∀ q, ∀ j ∈ C0, w q j = w' q j) (hN : ∀ r, ¬ c * N < XMW w C0 r → ∀ j, w r j = w' r j) :
    Pw w' (tcRow w') ≤ Real.exp (-(c * N)) := by
  set r := tcRow w'
  by_cases hl : c * N < XMW w C0 r
  · have hX : XMW w' C0 r = XMW w C0 r := by
      unfold XMW; exact Finset.sum_congr rfl fun j hj => by rw [hC r j hj]
    exact (st_Pw_le_exp C0 w' r).trans (Real.exp_le_exp.2 (by rw [hX]; linarith))
  · have : Pw w' r = Pw w r := by
      unfold Pw; exact Finset.prod_congr rfl fun j _ => by rw [hN r hl j]
    rw [this]; exact (Pw_le_tcRow w r).trans hP

section Stab

variable {s : State N} {ε γ : ℝ}

/-- **The selection only reads safe entries.** -/
theorem lt3Sel_stable {w w' : Param N} (h : ∀ q ∈ lt3Safe s ε w, w q.1 q.2 = w' q.1 q.2) :
    lt3Sel s ε γ w' = lt3Sel s ε γ w := by
  classical
  have hC : ∀ q, ∀ j ∈ (lt3Top s w ε)ᶜ, w q j = w' q j := fun q j hj =>
    h (q, j) (Or.inl (mem_compl.1 hj))
  have hN : ∀ r, ¬ 3 / 10 * (N : ℝ) < XMW w (lt3Top s w ε)ᶜ r → ∀ j, w r j = w' r j := fun r hr j =>
    h (r, j) (Or.inr (Or.inl hr))
  have hs : w' s = w s := funext fun j => (h (s, j) (Or.inr (Or.inr rfl))).symm
  by_cases hP : Real.exp (-(3 / 10 * (N : ℝ))) < Pw w (tcRow w)
  · obtain ⟨ht, hrow, hPt, hTop, hSp⟩ := lt3_frame_stable ε (le_trans lt2x1_bounds.2 (by norm_num)) hP hC hN hs
    have hL : ∀ q, lt3L s ε w' q ↔ lt3L s ε w q := fun q => by
      unfold lt3L; rw [hTop]; exact (stLight_congr _ _ hC q).symm
    have hB : lt3Base s w' = lt3Base s w := by unfold lt3Base; rw [ht, hSp]
    have hEx : lt3Ex s ε γ w' = lt3Ex s ε γ w := by
      unfold lt3Ex; rw [hTop, hB, hs]
      exact Finset.filter_congr fun j _ => by simp only [hL]
    have hQ : lt3Q s ε γ w' = lt3Q s ε γ w := by unfold lt3Q; rw [hB, hTop, hEx, ht]
    have hF : lt3F s ε γ w' = lt3F s ε γ w := by
      unfold lt3F; rw [hQ, hB]
      exact Finset.filter_congr fun S _ => by simp only [hL]
    unfold lt3Sel
    rw [hQ, hF, hB, hPt]
  · have hP' : ¬ Real.exp (-(3 / 10 * (N : ℝ))) < Pw w' (tcRow w') :=
      not_lt.2 (lt3_small_stable _ _ (not_lt.1 hP) hC hN)
    unfold lt3Sel
    rw [if_neg (fun hc => hP' hc.1), if_neg (fun hc => hP hc.1)]

/-- **Private positions are never safe.** -/
theorem lt3PB_not_safe (w : Param N) (k : Finset (Fin N) × State N) (hk : k ∈ lt3Sel s ε γ w)
    (q : State N × Fin N) (hq : q ∈ lt3PB k) : q ∉ lt3Safe s ε w := by
  classical
  unfold lt3Sel at hk
  split_ifs at hk with hc
  swap
  · simp at hk
  obtain ⟨hSF, hr⟩ := mem_product.1 hk
  obtain ⟨hSQ', hSlight⟩ := mem_filter.1 hSF
  have hSQ : k.1 ⊆ lt3Q s ε γ w := qFam_sub hSQ'
  have hQspec := lt3QOf_spec (lt3Base s w) (lt3Top s w ε \ lt3Ex s ε γ w) (tcRow w)
  have hQU : lt3Q s ε γ w ⊆ lt3Top s w ε \ lt3Ex s ε γ w := hQspec.1
  unfold lt3PB at hq
  obtain ⟨⟨R, i⟩, hp, rfl⟩ := mem_image.1 hq
  obtain ⟨hRi, hnot⟩ := mem_filter.1 hp
  obtain ⟨hR, hi⟩ := mem_product.1 hRi
  have hR : R ⊆ k.1 := mem_powerset.1 hR
  have hTE : ∀ j ∈ k.1, j ∈ lt3Top s w ε ∧ j ∉ lt3Ex s ε γ w := fun j hj => mem_sdiff.1 (hQU (hSQ hj))
  rintro (hcol | hlight | hrow)
  · exact hcol (hTE i hi).1
  · -- the row is light
    apply hlight
    by_cases h2 : 2 ≤ R.card
    · exact hSlight k.2 hr R hR h2
    · obtain ⟨j, hjR, hji⟩ : ∃ j ∈ R, j ≠ i := by
        by_contra hno; push Not at hno
        exact hnot fun x hx => mem_singleton.2 (hno x hx)
      have hRj : R = {j} := by
        refine Finset.eq_singleton_iff_unique_mem.2 ⟨hjR, fun x hx => ?_⟩
        by_contra hxj
        have : ({x, j} : Finset (Fin N)) ⊆ R := by
          intro y hy; rcases mem_insert.1 hy with rfl | hy
          · exact hx
          · rw [mem_singleton.1 hy]; exact hjR
        have := card_le_card this
        rw [card_pair hxj] at this; omega
      rw [hRj, flipS_single]
      have hj := hTE j (hR hjR)
      by_contra hl
      exact hj.2 (mem_filter.2 ⟨hj.1, Or.inl ⟨k.2, hr, hl⟩⟩)
  · -- the row is not `s`
    have hsB : s ∈ lt3Base s w := mem_insert_of_mem (mem_insert_self _ _)
    have hag := agree_pair_tc (hQspec.2.2 k.2 hr) (hQspec.2.2 s hsB)
    have hRne : R.Nonempty := by
      by_contra he; rw [not_nonempty_iff_eq_empty] at he; subst he; exact hnot (empty_subset _)
    have hrow' : flipS k.2 R = s := hrow
    have hsflip : flipS k.2 R = flipS s ∅ := by rw [hrow']; funext j; simp [flipS]
    obtain ⟨-, hRe⟩ := flipS_inj_agree hc.2 (hR.trans hSQ) (empty_subset _)
      ((card_le_card hR).trans (qFam_card_le hSQ')) (by simp) hag hsflip
    exact hRne.ne_empty hRe

/-- **Lemma SS for triples**: `{Priv = A}` is determined by the entries outside `A`. -/
theorem lt3Priv_detOn (A : Finset (State N × Fin N)) :
    DetOnE Aᶜ {w | stPriv (lt3Sel s ε γ) lt3PB w = A} :=
  stPriv_detOn_safe (lt3Safe s ε) (lt3Sel s ε γ) lt3PB (fun _ _ h => lt3Sel_stable h)
    (fun w k hk q hq => lt3PB_not_safe w k hk q hq) A

end Stab

end Census
end IIT
