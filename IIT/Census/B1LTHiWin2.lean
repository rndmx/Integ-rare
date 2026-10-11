/-
Census, B1 LTBetaHi, module T2 (amendment, gaps G3/G4 of the 2026-10-08 scope): **the windowed triple stopping set**.

`lt3Q` is refined by a window step: the shared per-unit values `y_{r,j}` and `y_{r^j,j}` (`r ∈ Base`, `j ∈ Q`) are cut
into `n+1` bins and `lt3WQ` is a largest bin class, `|Q| ≤ ((n+1)²)^{|Base|} |lt3WQ|` (`lt3WQ_card`); on it every such
value varies by at most `1/(n+1)` (`lt3WQ_window`, the window `d.win ω` of `rl_window`). The selection `lt3WSel` also
requires the floor `y_{tc,j} ≥ 4/5` on `lt3WQ` (`rl_sym_full`; `lt3WQ_floor`). The newly read entries `(r, j)` and
`(r^j, j)` are never private (W2 5.1: own-column flips are shared), so Lemma SS (`lt3WPriv_detOn`), measurability,
conditioning, perturbation, disjointness and the size of the kept family (`lt3W_good_F`) carry over.
-/
import IIT.Census.B1LTHiGood

namespace IIT
namespace Census

open MeasureTheory Finset

variable {N : ℕ}

/-! ### The bin class -/

/-- **Bin class**: a sub-class `Q' ⊆ Q` with `|Q| ≤ (m²)^{|B|} |Q'|` on which the key `f · r` is constant (`r ∈ B`). -/
theorem win_class {m : ℕ} (hm : 0 < m) (B : Finset (State N)) (Q : Finset (Fin N))
    (f : Fin N → State N → Fin m × Fin m) :
    ∃ Q' ⊆ Q, Q.card ≤ (m * m) ^ B.card * Q'.card ∧ ∀ j ∈ Q', ∀ j' ∈ Q', ∀ r ∈ B, f j r = f j' r := by
  classical
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨y, hy⟩ := exists_big_fiber Q (fun j (r : B) => f j r.1)
  rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at hy
  refine ⟨Q.filter fun j => (fun r : B => f j r.1) = y, filter_subset _ _, hy, fun j hj j' hj' r hr => ?_⟩
  have a := congrFun (mem_filter.1 hj).2 ⟨r, hr⟩
  have b := congrFun (mem_filter.1 hj').2 ⟨r, hr⟩
  exact a.trans b.symm

/-- The bin class of a key. -/
noncomputable def lt3WQOf0 (n : ℕ) (B : Finset (State N)) (Q : Finset (Fin N))
    (f : Fin N → State N → Fin (n + 1) × Fin (n + 1)) : Finset (Fin N) :=
  (win_class n.succ_pos B Q f).choose

/-- The key restricted to `Q × B`. -/
noncomputable def lt3WKeyR (n : ℕ) (B : Finset (State N)) (Q : Finset (Fin N))
    (f : Fin N → State N → Fin (n + 1) × Fin (n + 1)) : Fin N → State N → Fin (n + 1) × Fin (n + 1) := by
  classical exact fun j r => if j ∈ Q ∧ r ∈ B then f j r else (0, 0)

/-- The bin class, read only on `Q × B`. -/
noncomputable def lt3WQOf (n : ℕ) (B : Finset (State N)) (Q : Finset (Fin N))
    (f : Fin N → State N → Fin (n + 1) × Fin (n + 1)) : Finset (Fin N) :=
  lt3WQOf0 n B Q (lt3WKeyR n B Q f)

lemma lt3WQOf_spec (n : ℕ) (B : Finset (State N)) (Q : Finset (Fin N))
    (f : Fin N → State N → Fin (n + 1) × Fin (n + 1)) :
    lt3WQOf n B Q f ⊆ Q ∧ Q.card ≤ ((n + 1) * (n + 1)) ^ B.card * (lt3WQOf n B Q f).card ∧
      ∀ j ∈ lt3WQOf n B Q f, ∀ j' ∈ lt3WQOf n B Q f, ∀ r ∈ B, f j r = f j' r := by
  classical
  obtain ⟨h1, h2, h3⟩ := (win_class n.succ_pos B Q (lt3WKeyR n B Q f)).choose_spec
  refine ⟨h1, h2, fun j hj j' hj' r hr => ?_⟩
  have := h3 j hj j' hj' r hr
  unfold lt3WKeyR at this
  rwa [if_pos ⟨h1 hj, hr⟩, if_pos ⟨h1 hj', hr⟩] at this

lemma lt3WQOf_congr (n : ℕ) {B : Finset (State N)} {Q : Finset (Fin N)}
    {f g : Fin N → State N → Fin (n + 1) × Fin (n + 1)} (h : ∀ j ∈ Q, ∀ r ∈ B, f j r = g j r) :
    lt3WQOf n B Q f = lt3WQOf n B Q g := by
  classical
  have e : lt3WKeyR n B Q f = lt3WKeyR n B Q g := by
    funext j r
    unfold lt3WKeyR
    split_ifs with hc
    · exact h j hc.1 r hc.2
    · rfl
  unfold lt3WQOf; rw [e]

/-! ### The windowed choices -/

section Inst

variable (s : State N) (ε γ : ℝ) (n : ℕ)

/-- The bins of all entries. -/
noncomputable def lt3Bins (w : Param N) : State N → Fin N → Fin (n + 1) :=
  fun r j => winBin (n + 1) n.succ_pos (clamp01 (w r j))

/-- The key of unit `j` and base row `r`: the bins of `y_{r,j}` and `y_{r^j,j}`. -/
def lt3Key (b : State N → Fin N → Fin (n + 1)) (j : Fin N) (r : State N) : Fin (n + 1) × Fin (n + 1) :=
  (b r j, b (flip r j) j)

/-- The windowed class. -/
noncomputable def lt3WQ (w : Param N) : Finset (Fin N) :=
  lt3WQOf n (lt3Base s w) (lt3Q s ε γ w) (lt3Key n (lt3Bins n w))

/-- Kept members of the windowed class. -/
noncomputable def lt3WF (w : Param N) : Finset (Finset (Fin N)) := by
  classical exact (qFam (lt3WQ s ε γ n w)).filter fun S =>
    ∀ r ∈ lt3Base s w, ∀ R ⊆ S, 2 ≤ R.card → lt3L s ε w (flipS r R)

/-- The windowed selection (with the floor `y_{tc,j} ≥ 4/5`). -/
noncomputable def lt3WSel (w : Param N) : Finset (Finset (Fin N) × State N) := by
  classical exact
    if Real.exp (-(3 / 10 * (N : ℝ))) < Pw w (tcRow w) ∧ 7 ≤ (lt3WQ s ε γ n w).card ∧
        ∀ j ∈ lt3WQ s ε γ n w, 4 / 5 ≤ clamp01 (w (tcRow w) j) then
      (lt3WF s ε γ n w) ×ˢ (lt3Base s w)
    else ∅

/-- The safe positions: those of `lt3Safe`, and `(r, j)`, `(r^j, j)` for `r ∈ Base`, `j ∈ Q`. -/
def lt3WSafe (w : Param N) : Set (State N × Fin N) :=
  lt3Safe s ε w ∪ {q | q.2 ∈ lt3Q s ε γ w ∧ ∃ r ∈ lt3Base s w, q.1 = r ∨ q.1 = flip r q.2}

end Inst

/-! ### Properties of the windowed class -/

section Props

variable (s : State N) (ε γ : ℝ) (n : ℕ)

lemma lt3WQ_sub (w : Param N) : lt3WQ s ε γ n w ⊆ lt3Q s ε γ w := (lt3WQOf_spec n _ _ _).1

/-- **Size of the windowed class**: `|Q| ≤ ((n+1)²)^{|Base|} |lt3WQ|`. -/
theorem lt3WQ_card (w : Param N) :
    (lt3Q s ε γ w).card ≤ ((n + 1) * (n + 1)) ^ (lt3Base s w).card * (lt3WQ s ε γ n w).card :=
  (lt3WQOf_spec n _ _ _).2.1

/-- **The window**: on `lt3WQ`, `y_{r,·}` and `y_{r^·,·}` (`r ∈ Base`) vary by at most `1/(n+1)`. -/
theorem lt3WQ_window (w : Param N) {j j' : Fin N} (hj : j ∈ lt3WQ s ε γ n w) (hj' : j' ∈ lt3WQ s ε γ n w)
    {r : State N} (hr : r ∈ lt3Base s w) :
    |clamp01 (w r j) - clamp01 (w r j')| ≤ 1 / ((n + 1 : ℕ) : ℝ) ∧
      |clamp01 (w (flip r j) j) - clamp01 (w (flip r j') j')| ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
  have h := (lt3WQOf_spec n _ _ _).2.2 j hj j' hj' r hr
  simp only [lt3Key, lt3Bins, Prod.mk.injEq] at h
  exact ⟨winBin_close (n + 1) n.succ_pos (clamp01_nonneg _) (clamp01_le_one _) (clamp01_nonneg _)
      (clamp01_le_one _) h.1,
    winBin_close (n + 1) n.succ_pos (clamp01_nonneg _) (clamp01_le_one _) (clamp01_nonneg _)
      (clamp01_le_one _) h.2⟩

/-- **The floor**: in the special-current-row case, or if the `Top` threshold is `≥ 4/5`, `y_{tc,j} ≥ 4/5` on `lt3WQ`. -/
theorem lt3WQ_floor (w : Param N) (h : lt3SpC s w ∨ 4 / 5 ≤ b1YTopR w (tcRow w) ε) :
    ∀ j ∈ lt3WQ s ε γ n w, 4 / 5 ≤ clamp01 (w (tcRow w) j) := by
  classical
  intro j hj
  have hQU : lt3Q s ε γ w ⊆ lt3Top s w ε \ lt3Ex s ε γ w :=
    (lt3QOf_spec (lt3Base s w) (lt3Top s w ε \ lt3Ex s ε γ w) (tcRow w)).1
  have hT := (mem_sdiff.1 (hQU (lt3WQ_sub s ε γ n w hj))).1
  by_cases hc : lt3SpC s w
  · have := lt3Top_floorP hc hT; linarith
  · have h' := h.resolve_left hc
    unfold lt3Top at hT; rw [if_neg hc] at hT; unfold lt3TopG at hT
    have := (mem_filter.1 hT).2
    linarith

end Props

/-! ### Stability -/

section Stab

variable {s : State N} {ε γ : ℝ} {n : ℕ}

/-- The frame data of `lt3Sel_stable`: agreement on `lt3Safe` and `P(tc) > e^{-3N/10}` keep `tc`, its row, `P(tc)`,
`Top`, the lightness, `Base` and `Q`. -/
theorem lt3_core_stable {w w' : Param N} (h : ∀ q ∈ lt3Safe s ε w, w q.1 q.2 = w' q.1 q.2)
    (hP : Real.exp (-(3 / 10 * (N : ℝ))) < Pw w (tcRow w)) :
    tcRow w' = tcRow w ∧ w' (tcRow w) = w (tcRow w) ∧ Pw w' (tcRow w') = Pw w (tcRow w) ∧
      lt3Top s w' ε = lt3Top s w ε ∧ (∀ q, lt3L s ε w' q ↔ lt3L s ε w q) ∧ lt3Base s w' = lt3Base s w ∧
      lt3Q s ε γ w' = lt3Q s ε γ w := by
  classical
  have hC : ∀ q, ∀ j ∈ (lt3Top s w ε)ᶜ, w q j = w' q j := fun q j hj =>
    h (q, j) (Or.inl (mem_compl.1 hj))
  have hN : ∀ r, ¬ 3 / 10 * (N : ℝ) < XMW w (lt3Top s w ε)ᶜ r → ∀ j, w r j = w' r j := fun r hr j =>
    h (r, j) (Or.inr (Or.inl hr))
  have hs : w' s = w s := funext fun j => (h (s, j) (Or.inr (Or.inr rfl))).symm
  obtain ⟨ht, hrow, hPt, hTop, hSp⟩ := lt3_frame_stable ε (le_trans lt2x1_bounds.2 (by norm_num)) hP hC hN hs
  have hL : ∀ q, lt3L s ε w' q ↔ lt3L s ε w q := fun q => by
    unfold lt3L; rw [hTop]; exact (stLight_congr _ _ hC q).symm
  have hB : lt3Base s w' = lt3Base s w := by unfold lt3Base; rw [ht, hSp]
  have hEx : lt3Ex s ε γ w' = lt3Ex s ε γ w := by
    unfold lt3Ex; rw [hTop, hB, hs]
    exact Finset.filter_congr fun j _ => by simp only [hL]
  have hQ : lt3Q s ε γ w' = lt3Q s ε γ w := by unfold lt3Q; rw [hB, hTop, hEx, ht]
  exact ⟨ht, hrow, hPt, hTop, hL, hB, hQ⟩

/-- **The windowed selection only reads safe entries.** -/
theorem lt3WSel_stable {w w' : Param N} (h : ∀ q ∈ lt3WSafe s ε γ w, w q.1 q.2 = w' q.1 q.2) :
    lt3WSel s ε γ n w' = lt3WSel s ε γ n w := by
  classical
  have h0 : ∀ q ∈ lt3Safe s ε w, w q.1 q.2 = w' q.1 q.2 := fun q hq => h q (Or.inl hq)
  have hC : ∀ q, ∀ j ∈ (lt3Top s w ε)ᶜ, w q j = w' q j := fun q j hj =>
    h0 (q, j) (Or.inl (mem_compl.1 hj))
  have hN : ∀ r, ¬ 3 / 10 * (N : ℝ) < XMW w (lt3Top s w ε)ᶜ r → ∀ j, w r j = w' r j := fun r hr j =>
    h0 (r, j) (Or.inr (Or.inl hr))
  by_cases hP : Real.exp (-(3 / 10 * (N : ℝ))) < Pw w (tcRow w)
  · obtain ⟨ht, hrow, hPt, -, hL, hB, hQ⟩ := lt3_core_stable (γ := γ) h0 hP
    have hWQ : lt3WQ s ε γ n w' = lt3WQ s ε γ n w := by
      unfold lt3WQ; rw [hB, hQ]
      refine lt3WQOf_congr n fun j hj r hr => ?_
      have e1 : w r j = w' r j := h (r, j) (Or.inr ⟨hj, r, hr, Or.inl rfl⟩)
      have e2 : w (flip r j) j = w' (flip r j) j := h (flip r j, j) (Or.inr ⟨hj, r, hr, Or.inr rfl⟩)
      show (winBin (n + 1) n.succ_pos (clamp01 (w' r j)), winBin (n + 1) n.succ_pos (clamp01 (w' (flip r j) j))) =
        (winBin (n + 1) n.succ_pos (clamp01 (w r j)), winBin (n + 1) n.succ_pos (clamp01 (w (flip r j) j)))
      rw [← e1, ← e2]
    have hF : lt3WF s ε γ n w' = lt3WF s ε γ n w := by
      unfold lt3WF; rw [hWQ, hB]
      exact Finset.filter_congr fun S _ => by simp only [hL]
    unfold lt3WSel
    rw [hWQ, hF, hB, hPt, ht, hrow]
  · have hP' : ¬ Real.exp (-(3 / 10 * (N : ℝ))) < Pw w' (tcRow w') :=
      not_lt.2 (lt3_small_stable _ _ (not_lt.1 hP) hC hN)
    unfold lt3WSel
    rw [if_neg (fun hc => hP' hc.1), if_neg (fun hc => hP hc.1)]

/-- **Private positions are never safe** (in particular the read entries `(r, j)`, `(r^j, j)` are not private). -/
theorem lt3WPB_not_safe (w : Param N) (k : Finset (Fin N) × State N) (hk : k ∈ lt3WSel s ε γ n w)
    (q : State N × Fin N) (hq : q ∈ lt3PB k) : q ∉ lt3WSafe s ε γ w := by
  classical
  unfold lt3WSel at hk
  split_ifs at hk with hc
  swap
  · simp at hk
  obtain ⟨hSF, hr⟩ := mem_product.1 hk
  obtain ⟨hSQ', hSlight⟩ := mem_filter.1 hSF
  have hWsub := lt3WQ_sub s ε γ n w
  have hSQ : k.1 ⊆ lt3Q s ε γ w := (qFam_sub hSQ').trans hWsub
  have h7 : 7 ≤ (lt3Q s ε γ w).card := hc.2.1.trans (card_le_card hWsub)
  have hk3 : k.1.card ≤ 3 := qFam_card_le hSQ'
  have hQspec := lt3QOf_spec (lt3Base s w) (lt3Top s w ε \ lt3Ex s ε γ w) (tcRow w)
  have hQU : lt3Q s ε γ w ⊆ lt3Top s w ε \ lt3Ex s ε γ w := hQspec.1
  unfold lt3PB at hq
  obtain ⟨⟨R, i⟩, hp, rfl⟩ := mem_image.1 hq
  obtain ⟨hRi, hnot⟩ := mem_filter.1 hp
  obtain ⟨hR, hi⟩ := mem_product.1 hRi
  have hR : R ⊆ k.1 := mem_powerset.1 hR
  have hR3 : R.card ≤ 3 := (card_le_card hR).trans hk3
  have hTE : ∀ j ∈ k.1, j ∈ lt3Top s w ε ∧ j ∉ lt3Ex s ε γ w := fun j hj => mem_sdiff.1 (hQU (hSQ hj))
  have hRne : R.Nonempty := by
    by_contra he; rw [not_nonempty_iff_eq_empty] at he; subst he; exact hnot (empty_subset _)
  -- a block row equal to a base row `r'` is impossible
  have hbase : ∀ r' ∈ lt3Base s w, flipS k.2 R ≠ r' := by
    intro r' hr' hrow'
    have hag := agree_pair_tc (hQspec.2.2 k.2 hr) (hQspec.2.2 r' hr')
    have hsflip : flipS k.2 R = flipS r' ∅ := by rw [hrow']; funext j; simp [flipS]
    obtain ⟨-, hRe⟩ := flipS_inj_agree h7 (hR.trans hSQ) (empty_subset _) hR3 (by simp) hag hsflip
    exact hRne.ne_empty hRe
  intro hs
  rcases hs with hs | ⟨-, r', hr', hrow | hrow⟩
  · rcases hs with hcol | hlight | hrow
    · exact hcol (hTE i hi).1
    · apply hlight
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
    · exact hbase s (mem_insert_of_mem (mem_insert_self _ _)) hrow
  · exact hbase r' hr' hrow
  · -- the own-column flip `(r'^i, i)`
    have hrow' : flipS k.2 R = flipS r' {i} := by rw [flipS_single]; exact hrow
    have hag := agree_pair_tc (hQspec.2.2 k.2 hr) (hQspec.2.2 r' hr')
    obtain ⟨-, hRe⟩ := flipS_inj_agree h7 (hR.trans hSQ) (singleton_subset_iff.2 (hSQ hi)) hR3 (by simp) hag
      hrow'
    exact hnot (by rw [hRe])

/-- **Lemma SS for windowed triples**: `{Priv = A}` is determined by the entries outside `A`. -/
theorem lt3WPriv_detOn (A : Finset (State N × Fin N)) :
    DetOnE Aᶜ {w | stPriv (lt3WSel s ε γ n) lt3PB w = A} :=
  stPriv_detOn_safe (lt3WSafe s ε γ) (lt3WSel s ε γ n) lt3PB (fun _ _ h => lt3WSel_stable h)
    (fun w k hk q hq => lt3WPB_not_safe w k hk q hq) A

/-- **Private blocks of different selected pairs are disjoint** (W2 5.3). -/
theorem lt3WPB_disjoint (w : Param N) {k k' : Finset (Fin N) × State N}
    (hk : k ∈ lt3WSel s ε γ n w) (hk' : k' ∈ lt3WSel s ε γ n w) (hne : k ≠ k') :
    Disjoint (lt3PB k) (lt3PB k') := by
  classical
  unfold lt3WSel at hk hk'
  split_ifs at hk hk' with hc
  swap
  · simp at hk
  obtain ⟨hS, hr⟩ := mem_product.1 hk
  obtain ⟨hS', hr'⟩ := mem_product.1 hk'
  have hWsub := lt3WQ_sub s ε γ n w
  have h7 : 7 ≤ (lt3Q s ε γ w).card := hc.2.1.trans (card_le_card hWsub)
  have hSQ := (qFam_sub (mem_filter.1 hS).1).trans hWsub
  have hS'Q := (qFam_sub (mem_filter.1 hS').1).trans hWsub
  have hspec := lt3QOf_spec (lt3Base s w) (lt3Top s w ε \ lt3Ex s ε γ w) (tcRow w)
  rw [Finset.disjoint_left]
  intro q hq hq'
  unfold lt3PB at hq hq'
  obtain ⟨⟨R, i⟩, hp, rfl⟩ := mem_image.1 hq
  obtain ⟨⟨R', i'⟩, hp', he⟩ := mem_image.1 hq'
  obtain ⟨hRi, hnot⟩ := mem_filter.1 hp
  obtain ⟨hR'i, -⟩ := mem_filter.1 hp'
  obtain ⟨hR, hi⟩ := mem_product.1 hRi
  obtain ⟨hR', hi'⟩ := mem_product.1 hR'i
  have hR := mem_powerset.1 hR
  have hR' := mem_powerset.1 hR'
  simp only [Prod.mk.injEq] at he
  obtain ⟨hfl, rfl⟩ := he
  obtain ⟨hrr, hRR⟩ := flipS_inj_agree h7 (hR'.trans hS'Q) (hR.trans hSQ)
    ((card_le_card hR').trans (qFam_card_le (mem_filter.1 hS').1))
    ((card_le_card hR).trans (qFam_card_le (mem_filter.1 hS).1))
    (agree_pair_tc (hspec.2.2 _ hr') (hspec.2.2 _ hr)) hfl
  subst hRR
  by_cases hSS : k.1 = k'.1
  · exact hne (Prod.ext hSS hrr.symm)
  · exact hnot (shared_pos_sub (qFam_inter (mem_filter.1 hS).1 (mem_filter.1 hS').1 hSS) hR hR' hi hi')

end Stab

/-! ### Measurability -/

section Data

variable (s : State N) (ε γ : ℝ) (n : ℕ)

/-- The floor pattern of the row `tc`. -/
noncomputable def lt3Fl (w : Param N) : Fin N → Bool := by
  classical exact fun j => decide (4 / 5 ≤ clamp01 (w (tcRow w) j))

lemma fibM_Fl : FibM (lt3Fl (N := N)) := by
  classical
  refine fibM_fun fun j => ?_
  unfold lt3Fl
  exact fibM_decide (b1_measurableSet_at_tcRow (P := fun w r => 4 / 5 ≤ clamp01 (w r j))
    fun r => measurableSet_le measurable_const (b1m_clamp r j))

lemma measurable_winBin_val (m : ℕ) (hm : 0 < m) : Measurable fun x : ℝ => ((winBin m hm x : Fin m) : ℕ) := by
  show Measurable fun x : ℝ => min ⌊x * (m : ℝ)⌋₊ (m - 1)
  exact (measurable_from_top (f := fun k : ℕ => min k (m - 1))).comp
    (Nat.measurable_floor.comp (measurable_id.mul_const _))

lemma fibM_Bins : FibM (lt3Bins (N := N) n) := by
  refine fibM_fun fun r => fibM_fun fun j => ?_
  intro b
  have e : {w : Param N | lt3Bins n w r j = b} =
      (fun w : Param N => ((winBin (n + 1) n.succ_pos (clamp01 (w r j)) : Fin (n + 1)) : ℕ)) ⁻¹' {b.val} := by
    ext w; simp [lt3Bins, Fin.ext_iff]
  rw [e]
  exact ((measurable_winBin_val (n + 1) n.succ_pos).comp (b1m_clamp r j)) (measurableSet_singleton _)

/-- The windowed selection as a function of the data. -/
noncomputable def lt3WSelOf (d : State N × Bool × Finset (Fin N) × Finset (State N) × (State N → Bool) ×
    (Fin N → Bool)) (b : State N → Fin N → Fin (n + 1)) (fl : Fin N → Bool) :
    Finset (Finset (Fin N) × State N) := by
  classical exact
    let t := d.1; let P := d.2.1; let T := d.2.2.1; let Sp := d.2.2.2.1; let Lv := d.2.2.2.2.1
    let Hv := d.2.2.2.2.2
    let B := insert t (insert s Sp)
    let Ex := T.filter fun j => (∃ r ∈ B, Lv (flip r j) = false) ∨ Hv j = true
    let Q := lt3QOf B (T \ Ex) t
    let Q' := lt3WQOf n B Q (lt3Key n b)
    let F := (qFam Q').filter fun S => ∀ r ∈ B, ∀ R ⊆ S, 2 ≤ R.card → Lv (flipS r R) = true
    if P = true ∧ 7 ≤ Q'.card ∧ (∀ j ∈ Q', fl j = true) then F ×ˢ B else ∅

lemma lt3WSel_eq (w : Param N) :
    lt3WSel s ε γ n w = lt3WSelOf s n (tcRow w, lt3Pv w, lt3Top s w ε, lt2Sp w, lt3LvOf (lt3Top s w ε) w, lt3Hv s γ w)
      (lt3Bins n w) (lt3Fl w) := by
  classical
  have hEx : lt3Ex s ε γ w = (lt3Top s w ε).filter fun j =>
      (∃ r ∈ lt3Base s w, lt3LvOf (lt3Top s w ε) w (flip r j) = false) ∨ lt3Hv s γ w j = true := by
    unfold lt3Ex
    refine Finset.filter_congr fun j _ => ?_
    simp only [lt3L_iff, Bool.not_eq_true, lt3Hv, decide_eq_true_eq]
  have hQ : lt3Q s ε γ w = lt3QOf (lt3Base s w) (lt3Top s w ε \ ((lt3Top s w ε).filter fun j =>
      (∃ r ∈ lt3Base s w, lt3LvOf (lt3Top s w ε) w (flip r j) = false) ∨ lt3Hv s γ w j = true)) (tcRow w) := by
    unfold lt3Q; rw [hEx]
  have hF : lt3WF s ε γ n w = (qFam (lt3WQ s ε γ n w)).filter fun S =>
      ∀ r ∈ lt3Base s w, ∀ R ⊆ S, 2 ≤ R.card → lt3LvOf (lt3Top s w ε) w (flipS r R) = true := by
    unfold lt3WF
    exact Finset.filter_congr fun S _ => by simp only [lt3L_iff]
  have hWQ : lt3WQ s ε γ n w = lt3WQOf n (lt3Base s w) (lt3QOf (lt3Base s w) (lt3Top s w ε \ ((lt3Top s w ε).filter
      fun j => (∃ r ∈ lt3Base s w, lt3LvOf (lt3Top s w ε) w (flip r j) = false) ∨ lt3Hv s γ w j = true))
      (tcRow w)) (lt3Key n (lt3Bins n w)) := by
    unfold lt3WQ; rw [hQ]
  unfold lt3WSel lt3WSelOf
  simp only [lt3Pv, lt3Fl, decide_eq_true_eq]
  rw [hF, hWQ]
  rfl

end Data

/-- **`{Sel = K}` is measurable.** -/
theorem lt3W_mset_Sel (s : State N) (ε γ : ℝ) (n : ℕ) : FibM (lt3WSel s ε γ n) := by
  have e : lt3WSel s ε γ n = fun w => lt3WSelOf s n
      (tcRow w, lt3Pv w, lt3Top s w ε, lt2Sp w, lt3LvOf (lt3Top s w ε) w, lt3Hv s γ w) (lt3Bins n w) (lt3Fl w) :=
    funext fun w => lt3WSel_eq s ε γ n w
  rw [e]
  exact fibM_comp (fibM_pair (fibM_pair fibM_tcRow (fibM_pair fibM_Pv (fibM_pair (fibM_Top s ε) (fibM_pair fibM_Sp
    (fibM_pair (fibM_Lv s ε) (fibM_Hv s γ)))))) (fibM_pair (fibM_Bins n) fibM_Fl))
    (fun p => lt3WSelOf s n p.1 p.2.1 p.2.2)

/-- **`{Priv = A}` is measurable.** -/
theorem lt3W_mset_Priv (s : State N) (ε γ : ℝ) (n : ℕ) (A : Finset (State N × Fin N)) :
    MeasurableSet {w : Param N | stPriv (lt3WSel s ε γ n) lt3PB w = A} := by
  have := fibM_comp (lt3W_mset_Sel s ε γ n) (fun K => K.biUnion lt3PB)
  exact this A

/-- **Conditioning on the windowed private positions** (W2 Lemma CI). -/
theorem lt3W_cond_priv (s : State N) (ε γ : ℝ) (n : ℕ) {Y : Set (Param N)} (hY : MeasurableSet Y) {p : ENNReal}
    (h : ∀ A w, stPriv (lt3WSel s ε γ n) lt3PB w = A → cubeM N {η | replE A w η ∈ Y} ≤ p) : cubeM N Y ≤ p := by
  have : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  rw [measure_eq_sum_partition (cubeM N) (lt3W_mset_Priv s ε γ n) Y]
  calc ∑ A, cubeM N (Y ∩ {w | stPriv (lt3WSel s ε γ n) lt3PB w = A})
      ≤ ∑ A, p * cubeM N {w | stPriv (lt3WSel s ε γ n) lt3PB w = A} :=
        Finset.sum_le_sum fun A _ => by
          rw [Set.inter_comm]
          exact cubeM_inter_le_of_sectionE A (lt3W_mset_Priv s ε γ n A) hY (lt3WPriv_detOn A)
            fun w hw => h A w hw
    _ = p * ∑ A, cubeM N (Set.univ ∩ {w | stPriv (lt3WSel s ε γ n) lt3PB w = A}) := by
        rw [Finset.mul_sum]; simp only [Set.univ_inter]
    _ = p := by
        rw [← measure_eq_sum_partition (cubeM N) (lt3W_mset_Priv s ε γ n) Set.univ, measure_univ, mul_one]

/-- **The deterministic perturbation bound for windowed triples** (W2 (6.1)). -/
theorem lt3W_pert (s : State N) (ε γ : ℝ) (n : ℕ) (w : Param N) (V : Finset (State N))
    (hV : ∀ v ∈ V, v ∉ lt2Sp w)
    (σ : State N → State N) (i : Fin N) (g : (Fin N → ℝ) → ℝ) (hg0 : ∀ x, 0 ≤ g x)
    (hgP : ∀ x, g x ≤ ∏ j, clamp01 (x j)) (nσ : ℕ) (hfib : ∀ q, (V.filter fun v => σ v = q).card ≤ nσ) :
    |∑ v ∈ V, clamp01 (w (σ v) i) * g (w v) -
        ∑ v ∈ V, clamp01 (stHalf (stPriv (lt3WSel s ε γ n) lt3PB w) w (σ v) i) *
          g (stHalf (stPriv (lt3WSel s ε γ n) lt3PB w) w v)| ≤
      ((stPriv (lt3WSel s ε γ n) lt3PB w).card * (1 + nσ) : ℕ) *
        (Real.exp (-(3 / 10 * (N : ℝ))) + Real.exp (-(lt2x1 * N))) := by
  classical
  have hns : ∀ q ∈ stPriv (lt3WSel s ε γ n) lt3PB w, q ∉ lt3Safe s ε w := fun q hq hs => by
    obtain ⟨k, hk, hq⟩ := mem_biUnion.1 hq
    exact lt3WPB_not_safe w k hk q hq (Or.inl hs)
  refine st_pert _ w V σ i g hg0 hgP (lt3Top s w ε)ᶜ (3 / 10) _ (Real.exp_pos _).le
    (fun q hq hc => (hns q hq) (Or.inl (mem_compl.1 hc)))
    (fun v _ ⟨j, hj⟩ => by
      by_contra hl
      exact hns (v, j) hj (Or.inr (Or.inl hl)))
    (fun v hv _ => Or.inr ?_) nσ hfib
  have hX : lt2x1 * N < XW w v := by
    have := hV v hv
    simp only [lt2Sp, mem_filter, mem_univ, true_and, not_le] at this
    exact this
  refine (hgP (w v)).trans ?_
  have := st_Pw_le_exp univ w v
  rw [XMW_univ] at this
  exact this.trans (Real.exp_le_exp.2 (by linarith))

/-- `|Priv| ≤ 24 |Sel|`. -/
theorem lt3W_Priv_card (s : State N) (ε γ : ℝ) (n : ℕ) (w : Param N) :
    (stPriv (lt3WSel s ε γ n) lt3PB w).card ≤ 24 * (lt3WSel s ε γ n w).card := by
  classical
  unfold stPriv
  refine card_biUnion_le.trans ?_
  calc ∑ k ∈ lt3WSel s ε γ n w, (lt3PB k).card ≤ ∑ _k ∈ lt3WSel s ε γ n w, 24 := sum_le_sum fun k hk => by
        refine lt3PB_card_le k ?_
        unfold lt3WSel at hk
        split_ifs at hk
        · exact qFam_card_le (mem_filter.1 (mem_product.1 hk).1).1
        · simp at hk
    _ = 24 * (lt3WSel s ε γ n w).card := by rw [sum_const, smul_eq_mul, mul_comm]

/-! ### The good event and the size of the kept family -/

open Classical in
/-- **Size of the windowed kept family** (deterministic). -/
theorem lt3W_F_card (s : State N) (ε γ : ℝ) (n : ℕ) (w : Param N) {k : ℕ} (hTop : (lt3Top s w ε).card ≤ k) :
    (qFam (lt3WQ s ε γ n w)).card ≤ (lt3WF s ε γ n w).card + ((qFam (lt3WQ s ε γ n w)).filter fun S =>
      ∃ r ∈ lt3Base s w, ∃ R ⊆ S, 2 ≤ R.card ∧ ¬ stRobust N k (w (flipS r R))).card := by
  have hsub : qFam (lt3WQ s ε γ n w) ⊆ lt3WF s ε γ n w ∪ (qFam (lt3WQ s ε γ n w)).filter fun S =>
      ∃ r ∈ lt3Base s w, ∃ R ⊆ S, 2 ≤ R.card ∧ ¬ stRobust N k (w (flipS r R)) := by
    intro S hS
    by_cases hk : S ∈ lt3WF s ε γ n w
    · exact mem_union_left _ hk
    · refine mem_union_right _ (mem_filter.2 ⟨hS, ?_⟩)
      unfold lt3WF at hk
      simp only [mem_filter, not_and, not_forall] at hk
      obtain ⟨r, hr, R, hR, h2, hl⟩ := hk hS
      exact ⟨r, hr, R, hR, h2, fun hro => hl (stRobust_top hro hTop)⟩
  exact (card_le_card hsub).trans (card_union_le _ _)

open Classical in
/-- **Member exclusion for the windowed family** (W2 6.2(e)). -/
theorem lt3W_member_ev (s : State N) (ε γ : ℝ) (n : ℕ) {k : ℕ} (hN : 0 < N) (hk : 20 * k ≤ N) (b M : ℕ) :
    cubeM N {w | 7 ≤ (lt3WQ s ε γ n w).card ∧ (lt3Base s w).card ≤ b ∧
      M ≤ ((qFam (lt3WQ s ε γ n w)).filter fun S => ∃ r ∈ lt3Base s w, ∃ R ⊆ S, 2 ≤ R.card ∧
        ¬ stRobust N k (w (flipS r R))).card} ≤
      (lt3Dat N b).card * ENNReal.ofReal (((8 * b * (N * N)).choose M) *
        (N.choose k * Real.exp (-(44 / 100 * (N : ℝ)))) ^ M) := by
  refine (measure_mono fun w hw => ?_).trans (lt3_member_excl_union hN hk (lt3Dat N b)
    (fun d hd => (mem_filter.1 hd).2) (b := b) (f := N * N)
    (fun d hd => by
      obtain ⟨p, hp, rfl⟩ := mem_image.1 (mem_filter.1 hd).1
      exact (mem_filter.1 (mem_product.1 hp).2).2)
    (fun d hd => by
      obtain ⟨p, -, rfl⟩ := mem_image.1 (mem_filter.1 hd).1
      exact qFam_card_le_sq p.1) M)
  obtain ⟨h7, hb, hM⟩ := hw
  set Q := lt3WQ s ε γ n w
  have hWsub : Q ⊆ lt3Q s ε γ w := lt3WQ_sub s ε γ n w
  have hspec := lt3QOf_spec (lt3Base s w) (lt3Top s w ε \ lt3Ex s ε γ w) (tcRow w)
  have hag : ∀ r ∈ lt3Base s w, (∀ j ∈ Q, r j = tcRow w j) ∨ (∀ j ∈ Q, r j ≠ tcRow w j) := fun r hr => by
    rcases hspec.2.2 r hr with h | h
    · exact Or.inl fun j hj => h j (hWsub hj)
    · exact Or.inr fun j hj => h j (hWsub hj)
  have hadm : lt3Adm (Q, lt3Base s w, qFam Q) :=
    ⟨h7, fun r hr r' hr' => agree_pair_tc (hag r hr) (hag r' hr'),
      fun S hS => qFam_sub hS, fun S hS => qFam_card_le hS, fun S hS S' hS' hne => qFam_inter hS hS' hne⟩
  refine ⟨(Q, lt3Base s w, qFam Q), mem_filter.2 ⟨mem_image.2 ⟨(Q, lt3Base s w),
    mem_product.2 ⟨mem_univ _, mem_filter.2 ⟨mem_univ _, hb⟩⟩, rfl⟩, hadm⟩, hM⟩

open Classical in
/-- **The windowed member exclusion is `≤ e^{-2N}`** (hypotheses as `lt3_member_ev_le`). -/
theorem lt3W_member_ev_le (s : State N) (ε γ : ℝ) (n : ℕ) {k b M D : ℕ} (hD : 1 ≤ D) (hb : 1 ≤ b)
    (hk2 : N ≤ 21 * k) (hk1 : 20 * k ≤ N) (hM : N * N ≤ D * M)
    (hN1 : 1 + Real.log (8 * b * D) + 100 ≤ 23 / 100 * (N : ℝ))
    (hN2 : (((b : ℝ) + 1) * Real.log 3 + 2) * N ≤ 100 * M) :
    cubeM N {w | 7 ≤ (lt3WQ s ε γ n w).card ∧ (lt3Base s w).card ≤ b ∧
      M ≤ ((qFam (lt3WQ s ε γ n w)).filter fun S => ∃ r ∈ lt3Base s w, ∃ R ⊆ S, 2 ≤ R.card ∧
        ¬ stRobust N k (w (flipS r R))).card} ≤ ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; have := Real.log_nonneg (show (1 : ℝ) ≤ 8 * b * D by
        have : (1 : ℝ) ≤ b := by exact_mod_cast hb
        have : (1 : ℝ) ≤ D := by exact_mod_cast hD
        nlinarith)
      norm_num at hN1; linarith
    · exact h
  refine (lt3W_member_ev s ε γ n hNpos hk1 b M).trans ?_
  set p := (N.choose k : ℝ) * Real.exp (-(44 / 100 * (N : ℝ)))
  have hp0 : 0 ≤ p := by positivity
  have hp : p ≤ Real.exp (-(23 / 100 * (N : ℝ))) := st_robust_rate hk2 hk1
  have hDat : ((lt3Dat N b).card : ℝ) ≤ Real.exp (((b : ℝ) + 1) * Real.log 3 * N) := by
    have h1 : ((lt3Dat N b).card : ℝ) ≤ ((2 ^ N * (2 ^ N + 1) ^ b : ℕ) : ℝ) := by exact_mod_cast lt3Dat_card b
    have h2 : ((2 ^ N * (2 ^ N + 1) ^ b : ℕ) : ℝ) ≤ ((3 ^ N) ^ (b + 1) : ℕ) := by
      have a1 : 2 ^ N ≤ 3 ^ N := Nat.pow_le_pow_left (by norm_num) N
      have a2 : 2 ^ N + 1 ≤ 3 ^ N := by
        rcases Nat.eq_zero_or_pos N with h | h
        · omega
        · have : 2 ^ N < 3 ^ N := Nat.pow_lt_pow_left (by norm_num) (by omega)
          omega
      have : 2 ^ N * (2 ^ N + 1) ^ b ≤ (3 ^ N) ^ (b + 1) := by
        rw [pow_succ']; exact Nat.mul_le_mul a1 (Nat.pow_le_pow_left a2 b)
      exact_mod_cast this
    refine h1.trans (h2.trans (le_of_eq ?_))
    rw [show ((b : ℝ) + 1) * Real.log 3 * N = ((N * (b + 1) : ℕ) : ℝ) * Real.log 3 by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (by norm_num)]
    push_cast; ring
  have hc : ((8 * b * (N * N) : ℕ) : ℝ) ≤ (8 * b * D : ℝ) * M := by
    have : 8 * b * (N * N) ≤ 8 * b * D * M := by rw [mul_assoc (8 * b) D M]; exact Nat.mul_le_mul_left _ hM
    exact_mod_cast this
  have hrate := lt3_member_rate (b := b) (f := N * N) (M := M) (a := ((b : ℝ) + 1) * Real.log 3)
    (c := 8 * b * D) (by
      have : (1 : ℝ) ≤ b := by exact_mod_cast hb
      have : (1 : ℝ) ≤ D := by exact_mod_cast hD
      nlinarith) hDat hp0 hp (by exact_mod_cast hc) hN1 hN2
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hrate

open Classical in
/-- The windowed good event: `lt3Good` and the member exclusion for the windowed family. -/
def lt3WGood (s : State N) (ε γ : ℝ) (n k K b M : ℕ) (w : Param N) : Prop :=
  lt3Good s ε γ k K b M w ∧
  ¬ (7 ≤ (lt3WQ s ε γ n w).card ∧ (lt3Base s w).card ≤ b ∧
      M ≤ ((qFam (lt3WQ s ε γ n w)).filter fun S => ∃ r ∈ lt3Base s w, ∃ R ⊆ S, 2 ≤ R.card ∧
        ¬ stRobust N k (w (flipS r R))).card)

/-- **The windowed good event has probability `≥ 1 - 3e^{-1.05N}`** (parameters as `lt3_not_good_ev`). -/
theorem lt3W_not_good_ev (s : ∀ N, State N) (ε : ℝ) (n : ℕ) {D : ℕ} (hD : 1 ≤ D) :
    ∀ᶠ N : ℕ in Filter.atTop,
      cubeM N {w | ¬ lt3WGood (s N) ε lt3γ n (N / 20) (N / 600) 14 (N * N / D) w} ≤
        ENNReal.ofReal (3 * Real.exp (-((105 / 100 : ℝ) * N))) := by
  classical
  filter_upwards [lt3_not_good_ev s ε hD, Filter.eventually_ge_atTop (10 ^ 6 * D)] with N hold hN
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hNbig : 10 ^ 6 ≤ N := le_trans (Nat.le_mul_of_pos_right _ hD) hN
  have hNr : (10 : ℝ) ^ 6 * D ≤ N := by exact_mod_cast hN
  have hN0 : 0 < N := by omega
  have hMfl : N * N ≤ 2 * D * (N * N / D) := by
    have h := Nat.div_add_mod (N * N) D
    have hm := Nat.mod_lt (N * N) (show 0 < D by omega)
    have : 2 * D ≤ N * N := by nlinarith
    nlinarith
  have hMr : (N : ℝ) * N ≤ 2 * D * (N * N / D : ℕ) := by exact_mod_cast hMfl
  have hl3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have h4 := lt3W_member_ev_le (N := N) (s N) ε lt3γ n (k := N / 20) (b := 14) (M := N * N / D) (D := 2 * D)
    (by omega) (by norm_num) (by omega) (by omega) hMfl (by
      have hlog : Real.log (8 * 14 * ((2 * D : ℕ) : ℝ)) ≤ 8 * 14 * ((2 * D : ℕ) : ℝ) :=
        (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
      push_cast at hlog ⊢
      norm_num at hNr hlog ⊢
      linarith) (by
      push_cast
      have hNN : (N : ℝ) * (10 ^ 6 * D) ≤ N * N := mul_le_mul_of_nonneg_left hNr (Nat.cast_nonneg N)
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
      nlinarith)
  have hsub : {w | ¬ lt3WGood (s N) ε lt3γ n (N / 20) (N / 600) 14 (N * N / D) w} ⊆
      {w | ¬ lt3Good (s N) ε lt3γ (N / 20) (N / 600) 14 (N * N / D) w} ∪
      {w | 7 ≤ (lt3WQ (s N) ε lt3γ n w).card ∧ (lt3Base (s N) w).card ≤ 14 ∧
        N * N / D ≤ ((qFam (lt3WQ (s N) ε lt3γ n w)).filter fun S => ∃ r ∈ lt3Base (s N) w, ∃ R ⊆ S,
          2 ≤ R.card ∧ ¬ stRobust N (N / 20) (w (flipS r R))).card} := by
    intro w hw
    by_cases h1 : lt3Good (s N) ε lt3γ (N / 20) (N / 600) 14 (N * N / D) w
    · right
      by_contra h2
      exact hw ⟨h1, h2⟩
    · exact Or.inl h1
  have e2 : Real.exp (-(2 * (N : ℝ))) ≤ Real.exp (-((105 / 100 : ℝ) * N)) :=
    Real.exp_le_exp.2 (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith)
  have hE := Real.exp_pos (-((105 / 100 : ℝ) * N))
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  calc _ ≤ ENNReal.ofReal (2 * Real.exp (-((105 / 100 : ℝ) * N))) +
        ENNReal.ofReal (Real.exp (-((105 / 100 : ℝ) * N))) :=
        add_le_add hold (h4.trans (ENNReal.ofReal_le_ofReal e2))
    _ = ENNReal.ofReal (3 * Real.exp (-((105 / 100 : ℝ) * N))) := by
        rw [← ENNReal.ofReal_add (by positivity) hE.le]
        congr 1; ring

/-- **The windowed kept family is large on the good event** (`ε = 1/21`, `C ≥ ((n+1)²)^{14}`, `M = N²/(10^{14}C²)`,
`N ≥ 10^8 C`): `m ≥ N/(2300000 C)`, `|lt3WQ| ≥ 7` and `m² ≤ 2|lt3WF|`. -/
theorem lt3W_good_F (s : State N) (n : ℕ) {C : ℕ} (hC : ((n + 1) * (n + 1)) ^ 14 ≤ C) {w : Param N}
    (hN : 10 ^ 8 * C ≤ N)
    (hg : lt3WGood s (1 / 21) lt3γ n (N / 20) (N / 600) 14 (N * N / (10 ^ 14 * C * C)) w)
    (hGU : lt3SpC s w → ⌈(1 / 21 : ℝ) * N⌉₊ ≤ (lt3GoodU s w).card) :
    N / (2300000 * C) ≤ qM (lt3WQ s (1 / 21) lt3γ n w) ∧
      7 ≤ (lt3WQ s (1 / 21) lt3γ n w).card ∧
      qM (lt3WQ s (1 / 21) lt3γ n w) * qM (lt3WQ s (1 / 21) lt3γ n w) ≤ 2 * (lt3WF s (1 / 21) lt3γ n w).card := by
  classical
  have hC1 : 1 ≤ C := le_trans (Nat.one_le_pow _ _ (by positivity)) hC
  have hN' : 10 ^ 8 ≤ N := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hN
  obtain ⟨hg0, hgW⟩ := hg
  obtain ⟨hTle, -, hQ⟩ := lt3_good_Q s (by omega) hg0 hGU
  have hF := lt3W_F_card s (1 / 21) lt3γ n w hTle
  set Q := lt3Q s (1 / 21) lt3γ w
  set Q' := lt3WQ s (1 / 21) lt3γ n w
  obtain ⟨hB, -, -, -⟩ := lt3_good_sizes s (1 / 21) lt3γ lt3γ_lt (le_refl 14) hg0 hTle
  have hQ3 : 3 * (N / 2300000) ≤ Q.card := by omega
  have hQQ' : Q.card ≤ C * Q'.card := by
    refine (lt3WQ_card s (1 / 21) lt3γ n w).trans (Nat.mul_le_mul_right _ ?_)
    exact (Nat.pow_le_pow_right (by positivity) hB).trans hC
  set a := N / (2300000 * C) with ha_def
  have haC : C * a ≤ N / 2300000 := by
    rw [ha_def, ← Nat.div_div_eq_div_mul]; exact Nat.mul_div_le _ _
  have h3a : 3 * a ≤ Q'.card := by
    have : C * (3 * a) ≤ C * Q'.card := by
      calc C * (3 * a) = 3 * (C * a) := by ring
        _ ≤ 3 * (N / 2300000) := Nat.mul_le_mul_left _ haC
        _ ≤ Q.card := hQ3
        _ ≤ C * Q'.card := hQQ'
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hm : a ≤ qM Q' := by unfold qM; omega
  have ha43 : 43 ≤ a := by
    rw [ha_def, Nat.le_div_iff_mul_le (by positivity)]; omega
  have h7 : 7 ≤ Q'.card := by omega
  refine ⟨hm, h7, ?_⟩
  have hbad : ((qFam Q').filter fun S => ∃ r ∈ lt3Base s w, ∃ R ⊆ S, 2 ≤ R.card ∧
      ¬ stRobust N (N / 20) (w (flipS r R))).card < N * N / (10 ^ 14 * C * C) := by
    by_contra hc; exact hgW ⟨h7, by omega, not_lt.1 hc⟩
  have hm3 : 3 ≤ qM Q' := by omega
  rw [qFam_card hm3] at hF
  -- `N²/(10^14 C²) ≤ a²/2`
  have hNa : N < 2300000 * C * (a + 1) := by
    have := Nat.lt_div_mul_add (a := N) (b := 2300000 * C) (by positivity)
    rw [← ha_def] at this; nlinarith
  have hM : N * N / (10 ^ 14 * C * C) ≤ a * a / 2 := by
    have h0 : (2300000 * (a + 1)) * (2300000 * (a + 1)) ≤ 10 ^ 14 * (a * a / 2) := by
      have : 4 * (a + 1) * (a + 1) ≤ 7 * (a * a) := by nlinarith
      have h3 : a * a ≤ 2 * (a * a / 2) + 1 := by omega
      nlinarith
    have h1 : N * N ≤ (2300000 * C * (a + 1)) * (2300000 * C * (a + 1)) := Nat.mul_le_mul hNa.le hNa.le
    have h2 : (2300000 * C * (a + 1)) * (2300000 * C * (a + 1)) ≤ 10 ^ 14 * C * C * (a * a / 2) := by
      calc (2300000 * C * (a + 1)) * (2300000 * C * (a + 1))
          = (C * C) * ((2300000 * (a + 1)) * (2300000 * (a + 1))) := by ring
        _ ≤ (C * C) * (10 ^ 14 * (a * a / 2)) := Nat.mul_le_mul_left _ h0
        _ = 10 ^ 14 * C * C * (a * a / 2) := by ring
    exact Nat.div_le_of_le_mul (h1.trans h2)
  have hmm : a * a ≤ qM Q' * qM Q' := Nat.mul_le_mul hm hm
  omega

end Census
end IIT
