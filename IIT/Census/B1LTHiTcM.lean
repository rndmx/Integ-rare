/-
Census, B1 LTBetaHi, RL-tc part 2d: **the success region of a member when `s = tc`** (open item (b) for `s = tc`).

* The member's RL-tc data: the rest data `lt3TcRestD` (heavy rows other than `tc`), tc's shared entries
  `lt3TcX`, `lt3TcF`, and the Hilbert-chosen table `lt3TcTab` (a function of these data only);
  **`lt3TcTab_spec`**: for a member of `lt3WSel` (`|Sp| < 12`) the table satisfies `RLTcWin` with window loss
  `1/320000` (`rltc_real_window` with `n_b = 8319999`, `n_g = 640000`).
* `lt3W_replE_frame`: resampling `Priv` keeps `tc`, the heavy set, the heavy rows, their own flips at `S` and their
  weights; hence the member's RL-tc data and table (`lt3TcData_replE`).
* The success region: the rest box (targets `lt3Tgt` of the rest table) `∩` `tc`'s box (targets `clamp01 ∘ T.Y`);
  measurable, determined by the member's private blocks, probability `≥ ρ^{18|H|} ≥ ρ^234` (independent boxes on
  disjoint blocks).
* **`lt3_tc_member_ev`** (`L ≥ lt3Lc`): for `s = tc`, every non-adverse member has a success region of probability
  `≥ lt3pT = (1/4160000)^234` (`LT3MemberOK`); the conclusion uses `lt3_TCprime_tc` (cause, two targets) and
  `lt3_heff_tc` (effect, Lemma EFG from the same table and box).
* `LT3SpHyp L p`: what is left of `LT3HeavyHyp` — the heavy current states `s ∈ Sp \ {tc}` (RL-u, W8 §7.1/§8.3);
  **`lt3Heavy_of_Sp`**: `LT3SpHyp L p → LT3HeavyHyp L (min p lt3pT)`, and **`ltBetaHi_of_Sp`**.
-/
import IIT.Census.B1LTHiT7c
import IIT.Census.B1LTHiTcC

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-! ### The member's RL-tc data and table -/

/-- The rest data of a member: the heavy rows other than `tc`, weights `P(r)/P(tc)`. -/
noncomputable def lt3TcRestD (w : Param N) (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) : RLDR :=
  lt3RealData w e S (tcRow w) ((lt3H w).erase (tcRow w)) (Pw w (tcRow w))

/-- tc's own entries on the units. -/
noncomputable def lt3TcX (w : Param N) (e : Fin 3 ↪ Fin N) : Fin 3 → ℝ := fun i => clamp01 (w (tcRow w) (e i))

/-- tc's own-flip entries on the units. -/
noncomputable def lt3TcF (w : Param N) (e : Fin 3 ↪ Fin N) : Fin 3 → ℝ :=
  fun i => clamp01 (w (flip (tcRow w) (e i)) (e i))

/-- **The chosen RL-tc table** of a member (Hilbert choice; a function of the member's data). -/
noncomputable def lt3TcTab (w : Param N) (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) : TcTab :=
  Classical.epsilon (RLTcWin (lt3TcRestD w e S) (lt3TcX w e) (lt3TcF w e) (1 / 320000))

/-- **The chosen table satisfies the windowed RL-tc conclusion** for a member of `lt3WSel` (`|Sp| < 12`). -/
theorem lt3TcTab_spec {s : State N} {ε γ : ℝ} {w : Param N} (hw : w ∈ openCube N) {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {r0 : State N}
    (hk : (({a, b, c} : Finset (Fin N)), r0) ∈ lt3WSel s ε γ 8319999 w) (hSp : (lt2Sp w).card < 12) :
    RLTcWin (lt3TcRestD w (pkE3 hab hac hbc) {a, b, c}) (lt3TcX w (pkE3 hab hac hbc))
      (lt3TcF w (pkE3 hab hac hbc)) (1 / 320000) (lt3TcTab w (pkE3 hab hac hbc) {a, b, c}) := by
  classical
  obtain ⟨-, -, hfl, -, -, hSWQ, -⟩ := lt3W_mem hk
  set e := pkE3 hab hac hbc with he
  have hS := pkE3_S hab hac hbc
  have heS : ∀ i, e i ∈ ({a, b, c} : Finset (Fin N)) := fun i => (hS _).2 ⟨i, rfl⟩
  have hσ := b1_Pw_pos hw (tcRow w)
  have hPw : ∀ r, Pw w r ≤ Pw w (tcRow w) := fun r => Pw_le_tcRow w r
  set tc := tcRow w with htc
  set H' := (lt3H w).erase tc with hH'
  have htcH : tc ∈ lt3H w := mem_insert_self _ _
  have hH'c : H'.card ≤ 12 := by rw [hH', card_erase_of_mem htcH]; have := lt3H_card hSp; omega
  set wb : ℝ := 1 / ((8319999 + 1 : ℕ) : ℝ) with hwb
  have hwb0 : 0 ≤ wb := by positivity
  have hwin : ∀ r ∈ H', ∀ i i' : Fin 3,
      |clamp01 (w r (e i)) - clamp01 (w r (e i'))| ≤ wb ∧
      |clamp01 (w (flip r (e i)) (e i)) - clamp01 (w (flip r (e i')) (e i'))| ≤ wb :=
    fun r hr i i' => lt3WQ_window s ε γ 8319999 w (hSWQ (heS i)) (hSWQ (heS i'))
      (lt3H_sub_base s w (mem_of_mem_erase hr))
  have hd := lt3RD_win w e {a, b, c} tc H' hσ hPw hwb0 hwin
  have hd' : (lt3TcRestD w e {a, b, c}).win (13 * wb) :=
    RLDR.win_mono hd (mul_le_mul_of_nonneg_right (by exact_mod_cast hH'c.trans (by norm_num)) hwb0)
  have htcw : ∀ i i' : Fin 3, |clamp01 (w tc (e i)) - clamp01 (w tc (e i'))| ≤ wb ∧
      |clamp01 (w (flip tc (e i)) (e i)) - clamp01 (w (flip tc (e i')) (e i'))| ≤ wb :=
    fun i i' => lt3WQ_window s ε γ 8319999 w (hSWQ (heS i)) (hSWQ (heS i')) (lt3H_sub_base s w htcH)
  have hwb13 : wb ≤ 13 * wb := by linarith
  have hxw : ∀ i, lt3TcX w e i - rlMin3R (lt3TcX w e) ≤ 13 * wb :=
    sub_rlMin3R_le fun i i' => ((abs_le.1 (htcw i i').1).2).trans hwb13
  have hfw : ∀ i, lt3TcF w e i - rlMin3R (lt3TcF w e) ≤ 13 * wb :=
    sub_rlMin3R_le fun i i' => ((abs_le.1 (htcw i i').2).2).trans hwb13
  obtain ⟨hG1n, hF1n, hG2n, hF2n, hG1V, hF1V, hG2V, hF2V, hV1n, hV2n, hVH⟩ :=
    lt3RD_bounds w e {a, b, c} tc H' hσ hPw
  have hV22 : (lt3TcRestD w e {a, b, c}).V1 ≤ 22 := by
    have : (lt3TcRestD w e {a, b, c}).V1 + (lt3TcRestD w e {a, b, c}).V2 ≤ 12 :=
      hVH.trans (by exact_mod_cast hH'c)
    have h2 : 0 ≤ (lt3TcRestD w e {a, b, c}).V2 := hV2n
    linarith
  have hn : ((13 * wb) + 1 / ((640000 : ℕ) : ℝ)) = 1 / 320000 := by rw [hwb]; push_cast; norm_num
  obtain ⟨T, hT⟩ := rltc_real_window (lt3TcRestD w e {a, b, c}) (lt3TcX w e) (lt3TcF w e) (n := 640000)
    (by norm_num) (by norm_num) (by positivity) hd' hxw hfw (by rw [hn]; norm_num)
    hG1n hG1V hF1n hF1V hV22 hG2n hF2n hG2V hF2V (fun i => hfl _ (hSWQ (heS i))) (fun i => clamp01_le_one _)
    (fun i => clamp01_nonneg _) (fun i => clamp01_le_one _)
  rw [hn] at hT
  exact Classical.epsilon_spec ⟨T, hT⟩

/-! ### Resampling the private entries keeps the member's data -/

/-- **The frame under resampling `Priv`.** -/
theorem lt3W_replE_frame {s : State N} {ε γ : ℝ} {nb : ℕ} {w : Param N} {a b c : Fin N} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) {r0 : State N} (hk : (({a, b, c} : Finset (Fin N)), r0) ∈ lt3WSel s ε γ nb w)
    (η : Param N) :
    tcRow (replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η) = tcRow w ∧
      lt3H (replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η) = lt3H w ∧
      (∀ r ∈ lt3H w, replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η r = w r) ∧
      (∀ r ∈ lt3H w, ∀ i : Fin 3, replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η
        (flip r (pkE3 hab hac hbc i)) (pkE3 hab hac hbc i) = w (flip r (pkE3 hab hac hbc i)) (pkE3 hab hac hbc i)) ∧
      Pw (replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η) (tcRow w) = Pw w (tcRow w) ∧
      ∀ r ∈ lt3H w, Pw (replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η) r = Pw w r := by
  classical
  obtain ⟨hP, -, -, -, -, hSWQ, -⟩ := lt3W_mem hk
  set e := pkE3 hab hac hbc with he
  have hS := pkE3_S hab hac hbc
  set S : Finset (Fin N) := {a, b, c} with hSdef
  set A := stPriv (lt3WSel s ε γ nb) lt3PB w with hA
  set w' := replE A w η with hw'
  have hSQ : S ⊆ lt3Q s ε γ w := hSWQ.trans (lt3WQ_sub s ε γ nb w)
  have hnA : ∀ q ∈ lt3WSafe s ε γ w, q ∉ A := fun q hq hqA => by
    obtain ⟨k, hk', hq'⟩ := mem_biUnion.1 hqA
    exact lt3WPB_not_safe w k hk' q hq' hq
  have hsafe : ∀ q ∈ lt3WSafe s ε γ w, w q.1 q.2 = w' q.1 q.2 := by
    rintro ⟨q1, q2⟩ hq
    show w q1 q2 = (if (q1, q2) ∈ A then η q1 q2 else w q1 q2)
    rw [if_neg (hnA _ hq)]
  have hC : ∀ q, ∀ j ∈ (lt3Top s w ε)ᶜ, w q j = w' q j := fun q j hj =>
    hsafe (q, j) (Or.inl (Or.inl (mem_compl.1 hj)))
  have hN : ∀ r, ¬ 3 / 10 * (N : ℝ) < XMW w (lt3Top s w ε)ᶜ r → ∀ j, w r j = w' r j := fun r hr j =>
    hsafe (r, j) (Or.inl (Or.inr (Or.inl hr)))
  have hs' : w' s = w s := funext fun j => (hsafe (s, j) (Or.inl (Or.inr (Or.inr rfl)))).symm
  obtain ⟨ht, -, hPt, -, hSp⟩ := lt3_frame_stable ε (le_trans lt2x1_bounds.2 (by norm_num)) hP hC hN hs'
  have hH : lt3H w' = lt3H w := by unfold lt3H; rw [ht, hSp]
  have hrow : ∀ r ∈ lt3H w, w' r = w r := by
    intro r hr
    have hnl : ¬ 3 / 10 * (N : ℝ) < XMW w (lt3Top s w ε)ᶜ r := by
      intro hl
      rcases mem_insert.1 hr with rfl | hsp
      · have := (st_Pw_le_exp _ w (tcRow w)).trans_lt
          (Real.exp_lt_exp.2 (by linarith : -XMW w (lt3Top s w ε)ᶜ (tcRow w) < -(3 / 10 * (N : ℝ))))
        linarith
      · have hx : XW w r ≤ lt2x1 * N := by
          simpa [lt2Sp] using hsp
        have h1 := XMW_le_XW w (lt3Top s w ε)ᶜ r
        have h2 := lt2x1_bounds
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith
    funext j
    exact (hN r hnl j).symm
  have hflip : ∀ r ∈ lt3H w, ∀ i : Fin 3, w' (flip r (e i)) (e i) = w (flip r (e i)) (e i) := fun r hr i =>
    (hsafe (flip r (e i), e i) (Or.inr ⟨hSQ ((hS _).2 ⟨i, rfl⟩), r, lt3H_sub_base s w hr, Or.inr rfl⟩)).symm
  have hPw : ∀ r ∈ lt3H w, Pw w' r = Pw w r := fun r hr => by unfold Pw; rw [hrow r hr]
  exact ⟨ht, hH, hrow, hflip, hPw _ (mem_insert_self _ _), hPw⟩

/-- **The member's RL-tc data, hence its table, are unchanged by resampling `Priv`.** -/
theorem lt3TcData_replE {s : State N} {ε γ : ℝ} {nb : ℕ} {w : Param N} {a b c : Fin N} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) {r0 : State N} (hk : (({a, b, c} : Finset (Fin N)), r0) ∈ lt3WSel s ε γ nb w)
    (η : Param N) :
    lt3TcRestD (replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η) (pkE3 hab hac hbc) {a, b, c} =
        lt3TcRestD w (pkE3 hab hac hbc) {a, b, c} ∧
      lt3TcX (replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η) (pkE3 hab hac hbc) = lt3TcX w (pkE3 hab hac hbc) ∧
      lt3TcF (replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η) (pkE3 hab hac hbc) = lt3TcF w (pkE3 hab hac hbc) ∧
      lt3TcTab (replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η) (pkE3 hab hac hbc) {a, b, c} =
        lt3TcTab w (pkE3 hab hac hbc) {a, b, c} := by
  classical
  obtain ⟨ht, hH, hrow, hflip, hPt, hPw⟩ := lt3W_replE_frame hab hac hbc hk η
  set w' := replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η with hw'
  have htcH : tcRow w ∈ lt3H w := mem_insert_self _ _
  have hD : lt3TcRestD w' (pkE3 hab hac hbc) {a, b, c} = lt3TcRestD w (pkE3 hab hac hbc) {a, b, c} := by
    unfold lt3TcRestD
    rw [ht, hH, hPt]
    unfold lt3RealData
    congr 1 <;> (try funext i) <;> refine sum_congr rfl fun r hr => ?_ <;>
      simp only [hPw r (mem_of_mem_erase (mem_filter.1 hr).1), hrow r (mem_of_mem_erase (mem_filter.1 hr).1),
        hflip r (mem_of_mem_erase (mem_filter.1 hr).1)]
  have hX : lt3TcX w' (pkE3 hab hac hbc) = lt3TcX w (pkE3 hab hac hbc) := by
    funext i; unfold lt3TcX; rw [ht, hrow _ htcH]
  have hF : lt3TcF w' (pkE3 hab hac hbc) = lt3TcF w (pkE3 hab hac hbc) := by
    funext i; unfold lt3TcF; rw [ht, hflip _ htcH]
  refine ⟨hD, hX, hF, ?_⟩
  unfold lt3TcTab
  rw [hD, hX, hF]

/-! ### The success region -/

/-- The probability of the tc-member region. -/
noncomputable def lt3pT : ℝ := (1 / 4160000 : ℝ) ^ 234

lemma lt3pT_pos : 0 < lt3pT := by unfold lt3pT; positivity

/-- The two boxes of a tc-member: the rest box and `tc`'s box (targets read from `w`). -/
def lt3TcRegion (w : Param N) (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) (ρ : ℝ) : Set (Param N) :=
  lt3Box e S (tcRow w) ((lt3H w).erase (tcRow w))
      (lt3Tgt (lt3TcRestD w e S) (lt3TcRest w e (tcRow w) (lt3TcTab w e S))) ρ ∩
    lt3Box e S (tcRow w) {tcRow w} (fun u i => clamp01 ((lt3TcTab w e S).Y u i)) ρ

/-- **Lemma TC' for `s = tc`, packaged at a member** (deterministic, `t = 1/80`): `φ_s(S) ≥ β/4`. -/
theorem lt3_tc_quarter {w : Param N} (hw : w ∈ openCube N) (s : State N) (hs : s = tcRow w) {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hSp : (lt2Sp w).card < 12)
    (hH : ∀ r ∈ lt3H w, (∀ j ∈ ({a, b, c} : Finset (Fin N)), r j = tcRow w j) ∨
      (∀ j ∈ ({a, b, c} : Finset (Fin N)), r j ≠ tcRow w j))
    (hT : RLTcWin (lt3TcRestD w (pkE3 hab hac hbc) {a, b, c}) (lt3TcX w (pkE3 hab hac hbc))
      (lt3TcF w (pkE3 hab hac hbc)) (1 / 320000) (lt3TcTab w (pkE3 hab hac hbc) {a, b, c}))
    (hreg : w ∈ lt3TcRegion w (pkE3 hab hac hbc) {a, b, c} (1 / 4160000))
    {φL η : ℝ}
    (hlight : ∀ (t0 : State N) (u : Fin (2 ^ 3)) (i : Fin 3),
      |lt3Light w {a, b, c} (lt3H w) (pkFlip (pkE3 hab hac hbc) t0 u) (pkE3 hab hac hbc i) -
        lt3Light w {a, b, c} (lt3H w) t0 (pkE3 hab hac hbc i)| ≤ φL)
    (hφL : φL ≤ Pw w (tcRow w) / 320000) (hη0 : 0 ≤ η)
    (hlev : ∀ Y ⊆ ({a, b, c} : Finset (Fin N)), ∀ t', ∀ i ∈ ({a, b, c} : Finset (Fin N)),
      |Num w {a, b, c} Y t' i - lvK 3 * Zs w| ≤ η)
    (hηs : η ^ 2 ≤ Pw w (tcRow w) * (lvK 3 * Zs w) / (8 * 10 ^ 7))
    (hE0 : 6 * η / ((lvK 3 * Zs w - η) * Real.log 2) ≤ lt3E0tc) :
    1 / 4 * betaW w ≤ phi (flipP s w) s {a, b, c} := by
  classical
  set e := pkE3 hab hac hbc with he
  have hS := pkE3_S hab hac hbc
  set T := lt3TcTab w e {a, b, c} with hTdef
  obtain ⟨hregR, hregT⟩ := hreg
  have hY01 := hT.2.2.2.2.2.1
  have hc45 := hT.2.1
  -- tc's box with the raw targets
  have hboxT : w ∈ lt3Box e {a, b, c} (tcRow w) {tcRow w} (fun u i => T.Y u i) (1 / 4160000) := by
    intro x hx
    have h := hregT x hx
    obtain ⟨hx1, hv⟩ := mem_lt3BoxIdx.1 hx
    have hx1' : x.1 = tcRow w := mem_singleton.1 hx1
    have hag : ∀ j ∈ ({a, b, c} : Finset (Fin N)), x.1 j = tcRow w j := fun j _ => by rw [hx1']
    simp only [lt3BoxTgt, if_pos hag] at h ⊢
    have hcl : clamp01 (T.Y x.2.1 x.2.2) = T.Y x.2.1 x.2.2 :=
      clamp01_of_mem ⟨(hY01 x.2.1 x.2.2 hv).1, (hY01 x.2.1 x.2.2 hv).2⟩
    rwa [hcl] at h
  -- the effect side
  have hρY : ∀ (u : Fin (2 ^ 3)) (i : Fin 3), ¬((u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ)) →
      |clamp01 (w (pkFlip e s u) (e i)) - T.Y u i| ≤ 1 / 4160000 := by
    intro u i hv
    have h := hboxT (tcRow w, u, i) (mem_lt3BoxIdx.2 ⟨mem_singleton_self _, hv⟩)
    simp only [lt3BoxE, lt3BoxTgt] at h
    rw [if_pos (fun _ _ => trivial)] at h
    rw [hs]; exact h
  have hTs : RLTcWin (lt3TcRestD w e {a, b, c}) (fun i => clamp01 (w s (e i)))
      (fun i => clamp01 (w (flip s (e i)) (e i))) (1 / 320000) T := by
    rw [hs]; exact hT
  have heff := lt3_heff_tc hw s e hS hTs (by norm_num) (by norm_num) (by norm_num) hρY
  have hmain := lt3_TCprime_tc hw s hab hac hbc (lt3H w) (lt3H_card hSp) (mem_insert_self _ _) hH T hT
    (by norm_num) (by norm_num) (by norm_num) hregR hboxT hlight hφL hη0 hlev hηs hE0 heff
  have hβ : 0 ≤ betaW w := div_nonneg (Pw_nonneg w _) (b1_Zs_pos hw).le
  have hlt := levTrip_gt
  have k1 : (577 / 1000 : ℝ) * (4 / 5) ≤ levTrip * T.c0 := mul_le_mul hlt.le hc45 (by norm_num) levTrip_pos.le
  have k2 : (1 : ℝ) / 4 ≤ levTrip * T.c0 * (79 / 80) := by nlinarith
  calc 1 / 4 * betaW w ≤ levTrip * T.c0 * (79 / 80) * betaW w := mul_le_mul_of_nonneg_right k2 hβ
    _ ≤ phi (flipP s w) s {a, b, c} := hmain

/-- **A non-adverse member of `s = tc` has a success region of probability `≥ lt3pT`** (`N` large, any band
level `L ≥ lt3Lc`). -/
theorem lt3_tc_member_ev {L : ℝ} (hL : lt3Lc ≤ L) : ∀ᶠ N : ℕ in atTop,
    ∀ (s : State N) (w : Param N) (S : Finset (Fin N)),
    w ∈ openCube N → (lt2Sp w).card < 12 → (S, s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w →
    S ∉ lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w → s = tcRow w → LT3MemberOK L lt3pT s w S := by
  have hL0 : 0 < L := lt3Lc_pos.trans_le hL
  have hLκ : 768000 * lt3κ ≤ (1 / 80 : ℝ) * L := by have := lt3Lc_κ; linarith
  filter_upwards [bd_band (t := 1 / 80) (L := L) (by norm_num) hL0, bd_E0_ev lt3E0tc_pos, bd_tc_Sp_ev hL0,
    lt3_pert_ev (t := 1 / 80) (by norm_num)] with N hBand hE0 hTc hPert
  intro s w S hw hSp hk hnadv hs
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hS⟩ := lt3WSel_three hk
  have hS' : S = {a, b, c} := hS
  subst hS'
  set A := stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w with hA
  set e := pkE3 hab hac hbc with he
  have hSe := pkE3_S hab hac hbc
  obtain ⟨-, h7, -, -, -, hSWQ, hag⟩ := lt3W_mem hk
  set tc := tcRow w with htc
  set H' := (lt3H w).erase tc with hH'
  have htcH : tc ∈ lt3H w := mem_insert_self _ _
  have hH'c : H'.card ≤ 12 := by rw [hH', card_erase_of_mem htcH]; have := lt3H_card hSp; omega
  set T := lt3TcTab w e {a, b, c} with hTdef
  have hT := lt3TcTab_spec hw hab hac hbc hk hSp
  set ρ : ℝ := 1 / 4160000 with hρ
  set Ur := lt3Box e {a, b, c} tc H' (lt3Tgt (lt3TcRestD w e {a, b, c}) (lt3TcRest w e tc T)) ρ with hUr
  set Ut := lt3Box e {a, b, c} tc {tc} (fun u i => clamp01 (T.Y u i)) ρ with hUt
  have hU : lt3TcRegion w e {a, b, c} ρ = Ur ∩ Ut := rfl
  -- blocks
  have hsubR : H'.biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)) ⊆
      (lt3Base s w).biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)) :=
    biUnion_subset_biUnion_of_subset_left _ ((erase_subset _ _).trans (lt3H_sub_base s w))
  have hsubT : ({tc} : Finset (State N)).biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)) ⊆
      (lt3Base s w).biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)) :=
    biUnion_subset_biUnion_of_subset_left _ (singleton_subset_iff.2 (lt3H_sub_base s w htcH))
  have hdisj : Disjoint (H'.biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)))
      (({tc} : Finset (State N)).biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r))) := by
    rw [Finset.disjoint_biUnion_left]
    intro r hr
    rw [singleton_biUnion]
    have hrH := mem_of_mem_erase hr
    refine lt3WPB_disjoint w (lt3W_mem_base hk (lt3H_sub_base s w hrH)) (lt3W_mem_base hk (lt3H_sub_base s w htcH)) ?_
    intro h
    exact (ne_of_mem_erase hr) (Prod.ext_iff.1 h).2
  have hUrm : MeasurableSet Ur := lt3Box_mset _ _ _ _ _ _
  have hUtm : MeasurableSet Ut := lt3Box_mset _ _ _ _ _ _
  have hUrd := lt3Box_detOn hSe tc H' (lt3Tgt (lt3TcRestD w e {a, b, c}) (lt3TcRest w e tc T)) ρ
  have hUtd := lt3Box_detOn hSe tc {tc} (fun u i => clamp01 (T.Y u i)) ρ
  refine ⟨Ur ∩ Ut, hUrm.inter hUtm, (hUrd.mono hsubR).inter (hUtd.mono hsubT), ?_, ?_⟩
  · -- probability
    rw [cubeM_inter_eq_mul_of_detOnE hdisj hUrm hUtm hUrd hUtd]
    have hSQ : ({a, b, c} : Finset (Fin N)) ⊆ lt3Q s (1 / 21) lt3γ w := hSWQ.trans (lt3WQ_sub _ _ _ _ _)
    have hQ7 : 7 ≤ (lt3Q s (1 / 21) lt3γ w).card := h7.trans (card_le_card (lt3WQ_sub _ _ _ _ _))
    obtain ⟨hG1n, hF1n, hG2n, hF2n, hG1V, hF1V, hG2V, hF2V, hV1n, hV2n, -⟩ :=
      lt3RD_bounds w e {a, b, c} tc H' (b1_Pw_pos hw tc) (fun r => Pw_le_tcRow w r)
    have hlw := rlLoR_wd_bounds _ hG1n hF1n hG2n hF2n hG1V hF1V hG2V hF2V hV1n hV2n
    have hTg := lt3Tgt_spec (lt3TcRestD w e {a, b, c}) (lt3TcRest w e tc T) (fun u i => hT.2.2.2.2.1 u i)
      (fun u i => (hlw u i).2.1)
    have hρ0 : (0 : ℝ) ≤ ρ := by rw [hρ]; norm_num
    have hρ1 : ρ ≤ 1 := by rw [hρ]; norm_num
    have hpR := lt3Box_prob hSe hSQ hQ7 (H := H') (tc := tc)
      (fun r hr => hag r (lt3H_sub_base s w (mem_of_mem_erase hr))) (fun u i => (hTg u i).2) hρ0 hρ1
    have hpT := lt3Box_prob hSe hSQ hQ7 (H := {tc}) (tc := tc)
      (fun r hr => by rw [mem_singleton.1 hr]; exact Or.inl fun j _ => rfl)
      (τ := fun u i => clamp01 (T.Y u i)) (fun u i => ⟨clamp01_nonneg _, clamp01_le_one _⟩) hρ0 hρ1
    rw [card_singleton] at hpT
    have hpow : ρ ^ 234 ≤ ρ ^ (18 * H'.card) * ρ ^ (18 * 1) := by
      rw [← pow_add]
      exact pow_le_pow_of_le_one hρ0 hρ1 (by omega)
    unfold lt3pT
    rw [← hρ]
    calc ENNReal.ofReal (ρ ^ 234) ≤ ENNReal.ofReal (ρ ^ (18 * H'.card) * ρ ^ (18 * 1)) :=
          ENNReal.ofReal_le_ofReal hpow
      _ = ENNReal.ofReal (ρ ^ (18 * H'.card)) * ENNReal.ofReal (ρ ^ (18 * 1)) :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ cubeM N Ur * cubeM N Ut := mul_le_mul' hpR hpT
  · -- the conclusion
    rintro η ⟨hηr, hηt⟩ hw' hZ' hβ' hbd' hSp'
    set w' := replE A w η with hw'def
    obtain ⟨ht, hHw, hrow, hflip, hPt, hPw⟩ := lt3W_replE_frame hab hac hbc hk η
    obtain ⟨hD, hX, hF, hTab⟩ := lt3TcData_replE hab hac hbc hk η
    have hk' : (({a, b, c} : Finset (Fin N)), s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w' := by
      rw [hw'def, hA, lt3W_replE_sel]; exact hk
    have hF' := (lt3W_mem hk').2.2.2.1
    have hAdv' : ({a, b, c} : Finset (Fin N)) ∉ lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w' := by
      rw [hw'def, hA, lt3Adv_replE]; exact hnadv
    have hs' : s = tcRow w' := by rw [hs, ht]
    -- the region at `w'`
    have hreg' : w' ∈ lt3TcRegion w' e {a, b, c} ρ := by
      have hTc' : lt3TcRest w' e (tcRow w') (lt3TcTab w' e {a, b, c}) = lt3TcRest w e tc T := by
        funext u i
        unfold lt3TcRest
        rw [ht, hTab]
        have hrow' : w' (tcRow w) = w (tcRow w) := hrow _ htcH
        have hflip' : ∀ i : Fin 3, w' (flip (tcRow w) (e i)) (e i) = w (flip (tcRow w) (e i)) (e i) :=
          hflip _ htcH
        simp only [hrow', hflip']
        rfl
      unfold lt3TcRegion
      rw [hTc', ht, hHw, hD, hTab]
      have hdet : ∀ q ∈ (lt3H w).biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)),
          η q.1 q.2 = w' q.1 q.2 := by
        rintro ⟨q1, q2⟩ hq
        obtain ⟨r, hr, hq'⟩ := mem_biUnion.1 hq
        have hqA : (q1, q2) ∈ A := mem_biUnion.2 ⟨(({a, b, c} : Finset (Fin N)), r),
          lt3W_mem_base hk (lt3H_sub_base s w hr), hq'⟩
        show η q1 q2 = (if (q1, q2) ∈ A then η q1 q2 else w q1 q2)
        rw [if_pos hqA]
      refine ⟨(hUrd η w' fun q hq => hdet q ?_).1 hηr, (hUtd η w' fun q hq => hdet q ?_).1 hηt⟩
      · exact (biUnion_subset_biUnion_of_subset_left _ (erase_subset _ _)) hq
      · exact (biUnion_subset_biUnion_of_subset_left _ (singleton_subset_iff.2 htcH)) hq
    -- the table at `w'`
    have hT' := lt3TcTab_spec hw' hab hac hbc hk' hSp'
    -- agreement classes at `w'`
    obtain ⟨-, -, -, -, -, hSWQ', hag'⟩ := lt3W_mem hk'
    have hSQ' : ({a, b, c} : Finset (Fin N)) ⊆ lt3Q s (1 / 21) lt3γ w' := hSWQ'.trans (lt3WQ_sub _ _ _ _ _)
    have hHag : ∀ r ∈ lt3H w', (∀ j ∈ ({a, b, c} : Finset (Fin N)), r j = tcRow w' j) ∨
        (∀ j ∈ ({a, b, c} : Finset (Fin N)), r j ≠ tcRow w' j) := fun r hr => by
      rcases hag' r (lt3H_sub_base s w' hr) with h | h
      · exact Or.inl fun j hj => h j (hSQ' hj)
      · exact Or.inr fun j hj => h j (hSQ' hj)
    -- the light part
    have htc' : tcRow w' ∈ lt2Sp w' := hTc w' hw' hZ' hβ'
    have hHalf := lt3_hHalf_of_not_adv s (1 / 21) lt3γ 8319999 lt3κ_pos.le htc' hab hac hbc hF' hAdv'
    have hφH : 48 * lt3κ * sigN N ≤ (1 / 80) / 8000 * Pw w' (tcRow w') :=
      lt3_phiH_le (κ := lt3κ) (t := 1 / 80) (L := L) lt3κ_pos.le (by norm_num) hLκ hZ' hβ'
    obtain ⟨hP', hη0, hηs, hlev⟩ := hBand w' hbd' hZ' hβ' hSp'
    obtain ⟨-, hE0'⟩ := hE0 w' hbd' hZ'
    set Ep := ((((stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w').card * (1 + 8) : ℕ) : ℝ) *
      (Real.exp (-(3 / 10 * (N : ℝ))) + Real.exp (-(lt2x1 * N)))) with hEp
    have hPcard := (lt3W_Priv_card s (1 / 21) lt3γ 8319999 w').trans
      (Nat.mul_le_mul_left 24 (lt3WSel_card s (1 / 21) lt3γ 8319999 hSp'))
    have hEp2 : 2 * Ep ≤ (1 / 80) / 8000 * Pw w' (tcRow w') := by
      have h1 := hPert _ hPcard
      have h2 : (1 / 80 : ℝ) / 8000 * Real.exp (-((lt2x1 - 1 / 800) * N)) ≤ (1 / 80) / 8000 * Pw w' (tcRow w') :=
        mul_le_mul_of_nonneg_left hP' (by norm_num)
      rw [hEp]; linarith
    have hS3 : ({a, b, c} : Finset (Fin N)).card ≤ 3 := card_le_three
    have hlight : ∀ (t0 : State N) (u : Fin (2 ^ 3)) (i : Fin 3),
        |lt3Light w' {a, b, c} (lt3H w') (pkFlip e t0 u) (e i) - lt3Light w' {a, b, c} (lt3H w') t0 (e i)| ≤
          48 * lt3κ * sigN N + 2 * Ep := by
      intro t0 u i
      have h1 := abs_le.1 (lt3Light_pert s (1 / 21) lt3γ 8319999 w' hS3 (H := lt3H w') (subset_insert _ _)
        (pkFlip e t0 u) (e i))
      have h2 := abs_le.1 (lt3Light_pert s (1 / 21) lt3γ 8319999 w' hS3 (H := lt3H w') (subset_insert _ _) t0 (e i))
      have h3 := abs_le.1 (hHalf t0 u i)
      rw [← hEp] at h1 h2
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
    have hφL : 48 * lt3κ * sigN N + 2 * Ep ≤ Pw w' (tcRow w') / 320000 := by
      have e1 : (1 / 80 : ℝ) / 8000 * Pw w' (tcRow w') = Pw w' (tcRow w') / 640000 := by ring
      rw [e1] at hφH hEp2
      linarith
    have hηs' : bdEta w' ^ 2 ≤ Pw w' (tcRow w') * (lvK 3 * Zs w') / (8 * 10 ^ 7) := by
      have e1 : (1 / 80 : ℝ) / 10 ^ 6 * Pw w' (tcRow w') * (lvK 3 * Zs w') =
          Pw w' (tcRow w') * (lvK 3 * Zs w') / (8 * 10 ^ 7) := by ring
      linarith
    exact lt3_tc_quarter hw' s hs' hab hac hbc hSp' hHag hT' hreg' hlight hφL hη0
      (hlev a b c hab hac hbc) hηs' hE0'

/-! ### What is left of the heavy hypothesis -/

/-- **The remaining heavy case**: current states `s ∈ Sp \ {tc}` (W8 §7.1, RL-u). -/
def LT3SpHyp (L p : ℝ) : Prop :=
  0 < p ∧ ∀ᶠ N : ℕ in atTop, ∀ (s : State N) (w : Param N) (S : Finset (Fin N)),
    w ∈ openCube N → 1 / 2 ≤ Zs w → L * sigN N ≤ betaW w → bdGood w → (lt2Sp w).card < 12 →
    lt3WGood s (1 / 21) lt3γ 8319999 (N / 20) (N / 600) 14 (N * N / (10 ^ 14 * lt3Cn * lt3Cn)) w →
    (S, s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w → S ∉ lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w →
    s ∈ lt3H w → s ≠ tcRow w → LT3MemberOK L p s w S

/-- **The heavy hypothesis reduces to `s ∈ Sp \ {tc}`**: the case `s = tc` is `lt3_tc_member_ev`. -/
theorem lt3Heavy_of_Sp {L p : ℝ} (hL : lt3Lc ≤ L) (hH : LT3SpHyp L p) : LT3HeavyHyp L (min p lt3pT) := by
  refine ⟨lt_min hH.1 lt3pT_pos, ?_⟩
  filter_upwards [hH.2, lt3_tc_member_ev hL] with N h1 h2
  intro s w S hw hZ hβ hbd hSp hG hk hnadv hsH
  by_cases hs : s = tcRow w
  · exact (h2 s w S hw hSp hk hnadv hs).mono (min_le_right _ _)
  · exact (h1 s w S hw hZ hβ hbd hSp hG hk hnadv hsH hs).mono (min_le_left _ _)

/-- **LTBetaHi from the remaining heavy case** `s ∈ Sp \ {tc}`. -/
theorem ltBetaHi_of_Sp {L p : ℝ} (hL : lt3Lc ≤ L) (hH : LT3SpHyp L p) : LTBetaHiStmt (1 / 4) (104 / 100) :=
  ltBetaHi_of_heavy hL (lt3Heavy_of_Sp hL hH)

end Census
end IIT
