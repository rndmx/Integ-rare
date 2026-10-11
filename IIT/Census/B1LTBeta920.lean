/-
Census, B1: the LTβ chain at level `9/20` (copy of the `1/4` chain; internal levels `0.456` (tc/u), `0.458` (light)).
-/
import IIT.Census.B1LTHiFin
import IIT.Census.B1LTHiFloor

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}
/-- **The LT3 band** (`β ≥ L σ_N`). -/
def LT3HiStmtQ9 (L C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (B1w N s ∩ openCube N ∩ {w | L * sigN N ≤ betaW w ∧ ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 →
      phi (flipP s w) s S < 9 / 20 * betaW w}) ≤ ENNReal.ofReal (Real.exp (-(C * N)))

/-- **LTBetaHi from LT2 at level `L` and the LT3 band.** -/
theorem ltBetaHi_of_LT2L_LT3Q9 {L C C₁ C₂ : ℝ} (hL : 0 < L) (h1 : C < C₁) (h2 : C < C₂) (hLT : LT2Stmt L C₁)
    (hHi : LT3HiStmtQ9 L C₂) : LTBetaHiStmt (9 / 20) C := by
  filter_upwards [hLT, hHi, g_union_rate h1 h2] with N hA hB hU s
  refine (measure_mono ?_).trans (hU _ _ (hA s) (hB s))
  rintro w ⟨⟨hw, hcube⟩, hlo, hall⟩
  by_cases hb : L * sigN N ≤ betaW w
  · exact Or.inr ⟨⟨hw, hcube⟩, hb, hall⟩
  · refine Or.inl ⟨not_le.1 hb, fun S hS => ?_⟩
    have := hall S (by omega) (by omega)
    have hσ : 0 < sigN N := by unfold sigN; positivity
    nlinarith [not_le.1 hb]

/-- **LTBetaHi from the LT3 band alone** (LT2 at level `L` is proved). -/
theorem ltBetaHi_of_LT3Q9 {L C₂ : ℝ} (hL : 1 ≤ L) (h2 : 104 / 100 < C₂) (hHi : LT3HiStmtQ9 L C₂) :
    LTBetaHiStmt (9 / 20) (104 / 100) :=
  ltBetaHi_of_LT2L_LT3Q9 (by linarith) (by norm_num) h2 (lt2_provedL L hL) hHi


/-- floor statement -/
def LT3HiFlStmtQ9 (L C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (B1w N s ∩ openCube N ∩ {w | L * sigN N ≤ betaW w ∧ 1 / 2 ≤ Zs w ∧
      4 / 5 ≤ b1YTopR w (tcRow w) (1 / 21) ∧
      ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 9 / 20 * betaW w}) ≤
      ENNReal.ofReal (Real.exp (-(C * N)))

/-- **`Zs ≥ 1/2` and the floor may be assumed**: `LT3HiFlStmtQ9 L C₁ → LT3HiStmtQ9 L C` (`C < C₁`, `C < 1.4`). -/
theorem lt3Hi_of_floorQ9 {L C C₁ : ℝ} (hL : 0 < L) (h1 : C < C₁) (h2 : C < 14 / 10)
    (hFl : LT3HiFlStmtQ9 L C₁) : LT3HiStmtQ9 L C := by
  filter_upwards [hFl, flr_Zs_low, flr_floor hL, g_union_rate h1 h2] with N hA hB hF hU s
  refine (measure_mono ?_).trans (hU _ _ (hA s) hB)
  rintro w ⟨⟨hw, hcube⟩, hβ, hall⟩
  by_cases hZ : 1 / 2 ≤ Zs w
  · exact Or.inl ⟨⟨hw, hcube⟩, hβ, hZ, hF w hZ hβ, hall⟩
  · exact Or.inr (not_le.1 hZ).le

/-- **LTBetaHi from the floored LT3 band.** -/
theorem ltBetaHi_of_LT3FlQ9 {L C₂ : ℝ} (hL : 1 ≤ L) (h2 : 104 / 100 < C₂) (hFl : LT3HiFlStmtQ9 L C₂) :
    LTBetaHiStmt (9 / 20) (104 / 100) := by
  set C := (104 / 100 + min C₂ (14 / 10)) / 2 with hC
  have hm := lt_min h2 (by norm_num : (104 / 100 : ℝ) < 14 / 10)
  have hC1 : C < C₂ := by have := min_le_left C₂ (14 / 10); linarith
  have hC2 : C < 14 / 10 := by have := min_le_right C₂ (14 / 10); linarith
  exact ltBetaHi_of_LT3Q9 hL (by linarith) (lt3Hi_of_floorQ9 (by linarith) hC1 hC2 hFl)

/-! ### For T7: the selection is non-trivial on the floored band -/


/-- **`φ_s(S) ≥ β/4` for a successful member, `N` large** (`t = 1/80`, bins `n_b = 8319999`, grid `n_g = 640000`,
box `ρ = 1/4160000`, window loss `ω' = 1/320000`; light statistic `≤ σ/640000`, band `η² ≤ σ a₃Z/(8·10^7)`). -/
theorem lt3W_TCprime_quarterQ9 :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (w : Param N) (s : State N) (ε γ : ℝ) (a b c : Fin N) (hab : a ≠ b)
      (hac : a ≠ c) (hbc : b ≠ c) (r0 : State N) (φH η E0 : ℝ), w ∈ openCube N →
      (({a, b, c} : Finset (Fin N)), r0) ∈ lt3WSel s ε γ 8319999 w → (lt2Sp w).card < 12 →
      lt3WSucc (1 / 80) (1 / 320000) (1 / 4160000) (pkE3 hab hac hbc) {a, b, c} w →
      (∀ (t0 : State N) (u : Fin (2 ^ 3)) (i : Fin 3),
        |lt3Light (stHalf (stPriv (lt3WSel s ε γ 8319999) lt3PB w) w) {a, b, c} (lt3H w)
            (pkFlip (pkE3 hab hac hbc) t0 u) (pkE3 hab hac hbc i) -
          lt3Light (stHalf (stPriv (lt3WSel s ε γ 8319999) lt3PB w) w) {a, b, c} (lt3H w) t0
            (pkE3 hab hac hbc i)| ≤ φH) →
      φH ≤ Pw w (tcRow w) / 640000 →
      Real.exp (-((lt2x1 - 1 / 800) * N)) ≤ Pw w (tcRow w) → 0 ≤ η →
      (∀ Y ⊆ ({a, b, c} : Finset (Fin N)), ∀ t', ∀ i ∈ ({a, b, c} : Finset (Fin N)),
        |Num w {a, b, c} Y t' i - lvK 3 * Zs w| ≤ η) →
      η ^ 2 ≤ Pw w (tcRow w) * (lvK 3 * Zs w) / (8 * 10 ^ 7) →
      6 * η / ((lvK 3 * Zs w - η) * Real.log 2) ≤ E0 →
      (∃ te ∈ sysMaxEffStates (tpmOf (flipP s w)) {a, b, c} s s,
        ∀ θ : SysPartition N {a, b, c}, E0 ≤ sysPhiE (tpmOf (flipP s w)) {a, b, c} s θ s te) →
      9 / 20 * betaW w ≤ phi (flipP s w) s {a, b, c} := by
  filter_upwards [lt3W_TCprime_ev (t := 1 / 80) (by norm_num) le_rfl] with N hN w s ε γ a b c hab hac hbc r0 φH η
    E0 hw hk hSp hsucc hHalf hφH hσN hη0 hlev hηs hE0 heff
  have hc : ((1 / 80 : ℚ) : ℝ) = 1 / 80 := by push_cast; ring
  obtain ⟨c0, hc0, -, hphi⟩ := hN w s ε γ 8319999 a b c hab hac hbc r0 640000 (1 / 320000) (1 / 4160000) φH η E0
    hw hk hSp (by norm_num) (by norm_num) (by push_cast; norm_num) (by rw [hc]; norm_num) (by norm_num)
    (by rw [hc]; norm_num) hsucc hHalf (by rw [hc]; linarith) hσN hη0 hlev (by rw [hc]; linarith) hE0 heff
  rw [hc] at hphi
  have hβ : 0 ≤ betaW w := div_nonneg (Pw_nonneg w _) (b1_Zs_pos hw).le
  have hlt := levTrip_gt
  have k1 : (577 / 1000 : ℝ) * (4 / 5) ≤ levTrip * c0 := mul_le_mul hlt.le hc0 (by norm_num) levTrip_pos.le
  have k2 : (9 : ℝ) / 20 ≤ levTrip * c0 * (1 - 483 * (1 / 80) / 800) := by nlinarith
  calc 9 / 20 * betaW w ≤ levTrip * c0 * (1 - 483 * (1 / 80) / 800) * betaW w :=
        mul_le_mul_of_nonneg_right k2 hβ
    _ ≤ phi (flipP s w) s {a, b, c} := hphi


/-- **The conclusion of a successful member** at a resampled parameter `w'` (good conditions ⇒ `φ_s(S) ≥ β/4`). -/
def LT3ConclQ9 (L : ℝ) (s : State N) (w' : Param N) (S : Finset (Fin N)) : Prop :=
  w' ∈ openCube N → 1 / 2 ≤ Zs w' → L * sigN N ≤ betaW w' → bdGood w' → (lt2Sp w').card < 12 →
    9 / 20 * betaW w' ≤ phi (flipP s w') s S

/-- **A success region of member `S`** given the conditioning point `w`: measurable, determined by the member's
private blocks, of probability `≥ p`, and `LT3ConclQ9` holds at `replE Priv(w) w η` for every `η` in it. -/
def LT3MemberOKQ9 (L p : ℝ) (s : State N) (w : Param N) (S : Finset (Fin N)) : Prop :=
  ∃ U : Set (Param N), MeasurableSet U ∧ DetOnE ((lt3Base s w).biUnion fun r => lt3PB (S, r)) U ∧
    ENNReal.ofReal p ≤ cubeM N U ∧
    ∀ η ∈ U, LT3ConclQ9 L s (replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w) w η) S

lemma LT3MemberOKQ9.mono {L p p' : ℝ} {s : State N} {w : Param N} {S : Finset (Fin N)}
    (h : LT3MemberOKQ9 L p s w S) (hp : p' ≤ p) : LT3MemberOKQ9 L p' s w S := by
  obtain ⟨U, h1, h2, h3, h4⟩ := h
  exact ⟨U, h1, h2, (ENNReal.ofReal_le_ofReal hp).trans h3, h4⟩

/-- Units of a member avoid the weak band of `s` (they are in `Q ⊆ Top \ Ex`). -/
lemma lt3W_own_strongQ9 {s : State N} {ε γ : ℝ} {nb : ℕ} {w : Param N} {S : Finset (Fin N)} {r0 : State N}
    (hk : (S, r0) ∈ lt3WSel s ε γ nb w) :
    ∀ j ∈ S, clamp01 (w s j) ∉ Set.Ioo (1 / 2 - γ) (1 / 2 + γ) := by
  classical
  intro j hj hin
  obtain ⟨-, -, -, -, -, hSWQ, -⟩ := lt3W_mem hk
  have hjQ : j ∈ lt3Q s ε γ w := lt3WQ_sub s ε γ nb w (hSWQ hj)
  have hjU : j ∈ lt3Top s w ε \ lt3Ex s ε γ w :=
    (lt3QOf_spec (lt3Base s w) (lt3Top s w ε \ lt3Ex s ε γ w) (tcRow w)).1 hjQ
  obtain ⟨hjT, hjE⟩ := mem_sdiff.1 hjU
  exact hjE (mem_filter.2 ⟨hjT, Or.inr hin⟩)

/-! ### The light member -/

/-- **A non-adverse member of a light `s` has a success region of probability `≥ lt3pL`** (`N` large, any band
level `L ≥ lt3Lc`). -/
theorem lt3_light_member_evQ9 {L : ℝ} (hL : lt3Lc ≤ L) : ∀ᶠ N : ℕ in atTop,
    ∀ (s : State N) (w : Param N) (S : Finset (Fin N)),
    w ∈ openCube N → (lt2Sp w).card < 12 → (S, s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w →
    S ∉ lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w → s ∉ lt3H w → LT3MemberOKQ9 L lt3pL s w S := by
  have hL0 : 0 < L := lt3Lc_pos.trans_le hL
  have hLκ : 768000 * lt3κ ≤ (1 / 80 : ℝ) * L := by have := lt3Lc_κ; linarith
  filter_upwards [lt3W_TCprime_quarterQ9, bd_band (t := 1 / 80) (L := L) (by norm_num) hL0,
    bd_E0_ev lt3E0e_pos, bd_tc_Sp_ev hL0] with N hQ hBand hE0 hTc
  intro s w S hw hSp hk hnadv hsH
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hS⟩ := lt3WSel_three hk
  have hS' : S = {a, b, c} := hS
  subst hS'
  set A := stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w with hA
  set e := pkE3 hab hac hbc with he
  obtain ⟨-, hUm, hUd, hUp⟩ := lt3WSucc_prob hw hab hac hbc hk hSp (ng := 640000) (by norm_num) (by norm_num)
    (t := 1 / 80) (by norm_num) (by norm_num) (ω' := 1 / 320000) (ρ := 1 / 4160000) (by push_cast; norm_num)
    (by norm_num) (by norm_num)
  set Uc := {η : Param N | lt3WSucc (1 / 80) (1 / 320000) (1 / 4160000) e {a, b, c} (replE A w η)} with hUc
  set Ue := lt3EBox s {a, b, c} w lt3ρe with hUe
  have hsB : s ∈ lt3Base s w := mem_insert_of_mem (mem_insert_self _ _)
  have hsub1 : (lt3H w).biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)) ⊆
      (lt3Base s w).biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)) :=
    biUnion_subset_biUnion_of_subset_left _ (lt3H_sub_base s w)
  have hsub2 : lt3PB (({a, b, c} : Finset (Fin N)), s) ⊆
      (lt3Base s w).biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)) :=
    subset_biUnion_of_mem (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)) hsB
  have hdisj : Disjoint ((lt3H w).biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)))
      (lt3PB (({a, b, c} : Finset (Fin N)), s)) := by
    rw [Finset.disjoint_biUnion_left]
    intro r hr
    refine lt3WPB_disjoint w (lt3W_mem_base hk (lt3H_sub_base s w hr)) hk ?_
    intro h
    have hrs : r = s := (Prod.ext_iff.1 h).2
    exact hsH (hrs ▸ hr)
  have hS3 : ({a, b, c} : Finset (Fin N)).card = 3 := by
    rw [card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]
  refine ⟨Uc ∩ Ue, hUm.inter (lt3EBox_mset _ _ _ _), (hUd.mono hsub1).inter ((lt3EBox_detOn _ _ _ _).mono hsub2),
    ?_, ?_⟩
  · -- probability
    rw [cubeM_inter_eq_mul_of_detOnE hdisj hUm (lt3EBox_mset _ _ _ _) hUd (lt3EBox_detOn _ _ _ _)]
    have hEp := lt3EBox_prob s (S := ({a, b, c} : Finset (Fin N))) (by rw [hS3]) w lt3ρe_pos.le lt3ρe_le
    unfold lt3pL
    rw [ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' hUp hEp
  · -- the conclusion
    rintro η ⟨hηc, hηe⟩ hw' hZ' hβ' hbd' hSp'
    set w' := replE A w η with hw'def
    have hk' : (({a, b, c} : Finset (Fin N)), s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w' := by
      rw [hw'def, hA, lt3W_replE_sel]; exact hk
    have hF' := (lt3W_mem hk').2.2.2.1
    have hAdv' : ({a, b, c} : Finset (Fin N)) ∉ lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w' := by
      rw [hw'def, hA, lt3Adv_replE]; exact hnadv
    have htc' : tcRow w' ∈ lt2Sp w' := hTc w' hw' hZ' hβ'
    have hHalf := lt3_hHalf_of_not_adv s (1 / 21) lt3γ 8319999 lt3κ_pos.le htc' hab hac hbc hF' hAdv'
    have hφH : 48 * lt3κ * sigN N ≤ Pw w' (tcRow w') / 640000 := by
      have := lt3_phiH_le (κ := lt3κ) (t := 1 / 80) (L := L) lt3κ_pos.le (by norm_num) hLκ hZ' hβ'
      linarith
    obtain ⟨hP', hη0, hηs, hlev⟩ := hBand w' hbd' hZ' hβ' hSp'
    obtain ⟨-, hE0'⟩ := hE0 w' hbd' hZ'
    have hηs' : bdEta w' ^ 2 ≤ Pw w' (tcRow w') * (lvK 3 * Zs w') / (8 * 10 ^ 7) := by
      have e1 : (1 / 80 : ℝ) / 10 ^ 6 * Pw w' (tcRow w') * (lvK 3 * Zs w') =
          Pw w' (tcRow w') * (lvK 3 * Zs w') / (8 * 10 ^ 7) := by ring
      linarith
    -- the effect side
    have hbox' : w' ∈ lt3EBox s {a, b, c} w' lt3ρe := by
      intro q hq
      have hqA : q ∈ A := mem_biUnion.2 ⟨_, hk, hq⟩
      have h1 : w' q.1 q.2 = η q.1 q.2 := by rw [hw'def, hA]; exact lt3W_replE_priv_mem w η hqA
      have h2 : lt3ETgt w' s q.2 = lt3ETgt w s q.2 := by
        unfold lt3ETgt; rw [hw'def, hA, lt3W_replE_row_s]
      rw [h1, h2]
      exact hηe q hq
    have heff := lt3_heff_light hw' s hS3 lt3γ_pos.le lt3γ_lt.le lt3ρe_pos.le
      (by have := lt3ρe_le; have := lt3γ_pos; unfold lt3ρe; linarith) lt3ρe_B (lt3W_own_strongQ9 hk') hbox'
    have hsucc : lt3WSucc (1 / 80) (1 / 320000) (1 / 4160000) (pkE3 hab hac hbc) {a, b, c} w' := hηc
    exact hQ w' s (1 / 21) lt3γ a b c hab hac hbc s (48 * lt3κ * sigN N) (bdEta w') lt3E0e hw' hk' hSp'
      hsucc hHalf hφH hP' hη0 (hlev a b c hab hac hbc) hηs' hE0' heff


/-- **Open item (b), as a hypothesis.** For a heavy current state (`s ∈ lt3H w = {tc} ∪ Sp`), `s`'s private block is
a cause block, so the effect side must come from the RL-tc certificate, whose box pins `tc`'s private entries
(`Y`) separately from the other heavy rows (`M - Y`): the cause box of `lt3WSucc` (one target `lt3Tgt` for all rows
of a class) does not cover it. `LT3HeavyHypQ9 L p` asks exactly what that box delivers: every non-adverse member of
a heavy `s` has a success region of probability `≥ p` (band level `L`). The windowed good event `lt3WGood` at the
conditioning point is available (checker, 2026-10-08); the floor `4/5 ≤ y_top(tc)` follows from `Zs ≥ 1/2`,
`Lσ_N ≤ β` by `flr_floor`. -/
def LT3HeavyHypQ9 (L p : ℝ) : Prop :=
  0 < p ∧ ∀ᶠ N : ℕ in atTop, ∀ (s : State N) (w : Param N) (S : Finset (Fin N)),
    w ∈ openCube N → 1 / 2 ≤ Zs w → L * sigN N ≤ betaW w → bdGood w → (lt2Sp w).card < 12 →
    lt3WGood s (1 / 21) lt3γ 8319999 (N / 20) (N / 600) 14 (N * N / (10 ^ 14 * lt3Cn * lt3Cn)) w →
    (S, s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w → S ∉ lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w →
    s ∈ lt3H w → LT3MemberOKQ9 L p s w S

/-- **A box gives a success region**: targets `τ ∈ [0, 1]` on the member's private blocks and the deterministic
implication give `LT3MemberOKQ9` with probability `ρ^312` (`|Base| ≤ 13`, `|lt3PB| ≤ 24`). -/
theorem lt3MemberOK_of_boxQ9 {L ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {s : State N} {w : Param N}
    {S : Finset (Fin N)} (hS : S.card ≤ 3) (hSp : (lt2Sp w).card < 12) (τ : State N × Fin N → ℝ)
    (hτ : ∀ q, 0 ≤ τ q ∧ τ q ≤ 1)
    (himp : ∀ η : Param N, (∀ q ∈ (lt3Base s w).biUnion (fun r => lt3PB (S, r)), |clamp01 (η q.1 q.2) - τ q| ≤ ρ) →
      LT3ConclQ9 L s (replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w) w η) S) :
    LT3MemberOKQ9 L (ρ ^ 312) s w S := by
  classical
  set B := (lt3Base s w).biUnion (fun r => lt3PB (S, r)) with hB
  refine ⟨{η | ∀ q ∈ B, |clamp01 (η q.1 q.2) - τ q| ≤ ρ}, ?_, ?_, ?_, fun η hη => himp η hη⟩
  · have e1 : {η : Param N | ∀ q ∈ B, |clamp01 (η q.1 q.2) - τ q| ≤ ρ} =
        ⋂ q ∈ B, {η : Param N | |clamp01 (η q.1 q.2) - τ q| ≤ ρ} := by
      ext η; simp
    rw [e1]
    exact MeasurableSet.biInter (Set.to_countable _) fun q _ =>
      measurableSet_le (continuous_abs.measurable.comp ((b1m_clamp _ _).sub measurable_const)) measurable_const
  · intro η η' h
    simp only [Set.mem_setOf_eq]
    exact forall₂_congr fun q hq => by rw [h q hq]
  · have hE : Function.Injective fun b : {q // q ∈ B} => (b.1 : State N × Fin N) := Subtype.val_injective
    have h := cubeM_box_ge (B := {q // q ∈ B}) (fun b => b.1) hE (fun b => τ b.1) (fun b => hτ b.1) hρ0 hρ1
    rw [Fintype.card_coe] at h
    have hBase : (lt3Base s w).card ≤ 13 :=
      (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans (by omega)))
    have hc : B.card ≤ 312 := by
      refine card_biUnion_le.trans ?_
      calc ∑ r ∈ lt3Base s w, (lt3PB (S, r)).card ≤ ∑ _r ∈ lt3Base s w, 24 :=
            sum_le_sum fun r _ => lt3PB_card_le (S, r) hS
        _ = 24 * (lt3Base s w).card := by rw [sum_const, smul_eq_mul, mul_comm]
        _ ≤ 312 := by omega
    refine le_trans (ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hρ0 hρ1 hc))
      (h.trans (le_of_eq (congrArg _ ?_)))
    ext η
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h q hq => h ⟨q, hq⟩, fun h b => h b.1 b.2⟩

/-! ### The conditional product -/

/-- **No member succeeds**: success regions on disjoint private blocks, `P ≤ e^{-p |G|}`. -/
theorem lt3_nosucc_prodQ9 {L p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : State N) (w : Param N)
    (G : Finset (Finset (Fin N))) (hG : ∀ S ∈ G, (S, s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w)
    (hOK : ∀ S ∈ G, LT3MemberOKQ9 L p s w S) :
    cubeM N {η | ∀ S ∈ G, ¬ LT3ConclQ9 L s (replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w) w η) S} ≤
      ENNReal.ofReal (Real.exp (-(p * G.card))) := by
  classical
  have : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  set A := stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w with hA
  set C : Finset (Fin N) → Finset (State N × Fin N) := fun S => (lt3Base s w).biUnion fun r => lt3PB (S, r)
    with hC
  have hOK' : ∀ S : Finset (Fin N), ∃ U : Set (Param N), S ∈ G → (MeasurableSet U ∧ DetOnE (C S) U ∧
      ENNReal.ofReal p ≤ cubeM N U ∧ ∀ η ∈ U, LT3ConclQ9 L s (replE A w η) S) := by
    intro S
    by_cases hS : S ∈ G
    · obtain ⟨U, hU⟩ := hOK S hS
      exact ⟨U, fun _ => hU⟩
    · exact ⟨∅, fun h => absurd h hS⟩
  choose U hU using hOK'
  have hsub : {η | ∀ S ∈ G, ¬ LT3ConclQ9 L s (replE A w η) S} ⊆ ⋂ S ∈ G, (U S)ᶜ := by
    intro η hη
    simp only [Set.mem_iInter, Set.mem_compl_iff]
    intro S hS hηU
    exact hη S hS ((hU S hS).2.2.2 η hηU)
  have hdisj : ∀ j ∈ G, ∀ k ∈ G, j ≠ k → Disjoint (C j) (C k) := by
    intro j hj k hk hjk
    simp only [hC]
    rw [Finset.disjoint_biUnion_left]
    intro r hr
    rw [Finset.disjoint_biUnion_right]
    intro r' hr'
    exact lt3WPB_disjoint w (lt3W_mem_base (hG j hj) hr) (lt3W_mem_base (hG k hk) hr')
      (fun h => hjk (Prod.ext_iff.1 h).1)
  refine (measure_mono hsub).trans ?_
  rw [cubeM_iInter_eq_prod_of_detOnE G C hdisj (fun S hS => (hU S hS).1.compl)
    (fun S hS => (hU S hS).2.1.compl)]
  have hone : ∀ S ∈ G, cubeM N (U S)ᶜ ≤ ENNReal.ofReal (1 - p) := fun S hS => by
    rw [measure_compl (hU S hS).1 (measure_ne_top _ _), measure_univ, ENNReal.ofReal_sub _ hp0,
      ENNReal.ofReal_one]
    exact tsub_le_tsub_left (hU S hS).2.2.1 1
  calc ∏ S ∈ G, cubeM N (U S)ᶜ ≤ ∏ _S ∈ G, ENNReal.ofReal (1 - p) := Finset.prod_le_prod' hone
    _ = ENNReal.ofReal ((1 - p) ^ G.card) := by
        rw [Finset.prod_const, ENNReal.ofReal_pow (by linarith)]
    _ ≤ ENNReal.ofReal (Real.exp (-(p * G.card))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc (1 - p) ^ G.card ≤ Real.exp (-p) ^ G.card :=
              pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-p)]) _
          _ = Real.exp (-(p * G.card)) := by rw [← Real.exp_nat_mul]; ring_nf

/-! ### The events -/

/-- The good event of T7: the windowed good event, the band event, and no excess of adverse members. -/
def lt3T7GoodQ9 (s : State N) (w : Param N) : Prop :=
  lt3WGood s (1 / 21) lt3γ 8319999 (N / 20) (N / 600) 14 (N * N / (10 ^ 14 * lt3Cn * lt3Cn)) w ∧ bdGood w ∧
  ¬ ((lt2Sp w).card < 12 ∧ 7 ≤ qM (lt3WQ s (1 / 21) lt3γ 8319999 w) ∧
      N ≤ lt3D0 * qM (lt3WQ s (1 / 21) lt3γ 8319999 w) ∧
      qM (lt3WQ s (1 / 21) lt3γ 8319999 w) * qM (lt3WQ s (1 / 21) lt3γ 8319999 w) <
        4 * (lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w).card)

/-- The measurable target: no pair or triple reaches `β/4` on `{Lσ_N ≤ β, Zs ≥ 1/2}` (open cube). -/
def lt3T7TmQ9 (L : ℝ) (s : State N) : Set (Param N) :=
  {w | w ∈ openCube N ∧ L * sigN N ≤ betaW w ∧ 1 / 2 ≤ Zs w ∧
    (lt3SpC s w → ⌈(1 / 21 : ℝ) * N⌉₊ ≤ (lt3GoodU s w).card) ∧
    ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 9 / 20 * betaW w}

/-- The conditioned event: the target intersected with a measurable subset of the good event. -/
def lt3T7YQ9 (L : ℝ) (s : State N) : Set (Param N) :=
  lt3T7TmQ9 L s ∩ (toMeasurable (cubeM N) {w | ¬ lt3T7GoodQ9 s w})ᶜ

lemma lt3T7Tm_msetQ9 (L : ℝ) (s : State N) : MeasurableSet (lt3T7TmQ9 L s) := by
  classical
  have e : lt3T7TmQ9 L s = openCube N ∩ ({w | L * sigN N ≤ betaW w} ∩ ({w | 1 / 2 ≤ Zs w} ∩
      ({w | lt3SpC s w → ⌈(1 / 21 : ℝ) * N⌉₊ ≤ (lt3GoodU s w).card} ∩
      ⋂ S : Finset (Fin N), {w | 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 9 / 20 * betaW w}))) := by
    ext w
    simp only [lt3T7TmQ9, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  have hGU : MeasurableSet {w : Param N | lt3SpC s w → ⌈(1 / 21 : ℝ) * N⌉₊ ≤ (lt3GoodU s w).card} := by
    have h := fibM_comp (f := fun w : Param N => ((lt2Sp w, tcRow w), lt3GoodU s w))
      (fibM_pair fibM_SpTc (fibM_GoodU s))
      (fun d => decide (s ∈ d.1.1 ∧ s ≠ d.1.2 → ⌈(1 / 21 : ℝ) * N⌉₊ ≤ d.2.card)) true
    convert h using 1
    ext w
    simp only [Set.mem_setOf_eq, decide_eq_true_eq]
    rfl
  refine b1_measurableSet_openCube.inter ((measurableSet_le measurable_const b1m_betaW).inter
    ((measurableSet_le measurable_const b1m_Zs).inter (hGU.inter (MeasurableSet.iInter fun S => ?_))))
  by_cases h : 2 ≤ S.card ∧ S.card ≤ 3
  · have e2 : {w : Param N | 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 9 / 20 * betaW w} =
        {w | phi (flipP s w) s S < 9 / 20 * betaW w} := by
      ext w
      simp only [Set.mem_setOf_eq]
      exact ⟨fun hw => hw h.1 h.2, fun hw _ _ => hw⟩
    rw [e2]
    exact measurableSet_lt (b1m_phi_flip s S) (b1m_betaW.const_mul _)
  · have e2 : {w : Param N | 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 9 / 20 * betaW w} = Set.univ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ h
    rw [e2]
    exact MeasurableSet.univ

lemma lt3T7Y_msetQ9 (L : ℝ) (s : State N) : MeasurableSet (lt3T7YQ9 L s) :=
  (lt3T7Tm_msetQ9 L s).inter (measurableSet_toMeasurable _ _).compl

lemma lt3T7Y_goodQ9 {L : ℝ} {s : State N} {w : Param N} (h : w ∈ lt3T7YQ9 L s) : lt3T7GoodQ9 s w := by
  by_contra hc
  exact h.2 (subset_toMeasurable _ _ hc)

/-! ### Numerics -/

/-- **The conditional product is `≤ e^{-2N}`**: `m ≥ N/K` (`K = 2300000 C`), `m² ≤ 4g` give `2N ≤ p g`. -/
lemma lt3_prod_numQ9 {p : ℝ} (hp : 0 < p) : ∀ᶠ N : ℕ in atTop, ∀ m g : ℕ, N / (2300000 * lt3Cn) ≤ m →
    m * m ≤ 4 * g → 2 * (N : ℝ) ≤ p * g := by
  set K : ℕ := 2300000 * lt3Cn with hK
  have hK0 : 0 < K := by have := lt3Cn_pos; positivity
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  filter_upwards [eventually_ge_atTop (2 * K), eventually_ge_atTop ⌈32 * (K : ℝ) ^ 2 / p⌉₊] with N h1 h2 m g hm hg
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1r : 2 * (K : ℝ) ≤ N := by exact_mod_cast h1
  have h2r : 32 * (K : ℝ) ^ 2 / p ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast h2)
  have hlt := Nat.lt_div_mul_add (a := N) hK0
  have hlt' : (N : ℝ) < (N / K : ℕ) * K + K := by exact_mod_cast hlt
  have hmr : ((N / K : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
  -- `N/(2K) ≤ m`
  have hq : (N : ℝ) ≤ 2 * K * m := by nlinarith
  have hgr : ((m : ℝ)) * m ≤ 4 * g := by exact_mod_cast hg
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- `N² ≤ 4K² m² ≤ 16 K² g`
  have hN2 : (N : ℝ) * N ≤ 16 * (K : ℝ) ^ 2 * g := by nlinarith
  have h32 : 32 * (K : ℝ) ^ 2 ≤ p * N := by
    rw [div_le_iff₀ hp] at h2r; linarith
  -- `2N · 16K² ≤ p N · 16 K² g / N`, i.e. `2N ≤ p g`
  by_cases hNz : (N : ℝ) = 0
  · rw [hNz]; have : (0 : ℝ) ≤ p * g := by positivity
    linarith
  · have hNpos : 0 < (N : ℝ) := lt_of_le_of_ne hN0 (Ne.symm hNz)
    have hK2 : 0 < (K : ℝ) ^ 2 := by positivity
    have key : 2 * (N : ℝ) * (16 * (K : ℝ) ^ 2) ≤ p * g * (16 * (K : ℝ) ^ 2) := by
      have e1 : 2 * (N : ℝ) * (16 * (K : ℝ) ^ 2) = N * (32 * (K : ℝ) ^ 2) := by ring
      have e2 : (N : ℝ) * (32 * (K : ℝ) ^ 2) ≤ N * (p * N) := mul_le_mul_of_nonneg_left h32 hN0
      have e3 : (N : ℝ) * (p * N) ≤ p * (16 * (K : ℝ) ^ 2 * g) := by
        have := mul_le_mul_of_nonneg_left hN2 hp.le
        nlinarith
      nlinarith
    exact le_of_mul_le_mul_right key (by positivity)

/-- `2 e^{-1.05N} + e^{-1.2N} + 2 e^{-2N} + 2 e^{-1.1N} ≤ e^{-1.047N}` for `N` large. -/
lemma lt3_rate_numQ9 : ∀ᶠ N : ℕ in atTop, Real.exp (-(2 * (N : ℝ))) +
    (2 * Real.exp (-((105 / 100 : ℝ) * N)) + Real.exp (-(6 / 5 * (N : ℝ))) + Real.exp (-(2 * (N : ℝ)))) +
      2 * Real.exp (-((11 / 10 : ℝ) * N)) ≤ Real.exp (-(1047 / 1000 * (N : ℝ))) := by
  filter_upwards [eventually_ge_atTop 2000] with N hN
  have hNr : (2000 : ℝ) ≤ N := by exact_mod_cast hN
  set E := Real.exp (-((105 / 100 : ℝ) * N)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have e1 : Real.exp (-(2 * (N : ℝ))) ≤ E := Real.exp_le_exp.2 (by linarith)
  have e2 : Real.exp (-(6 / 5 * (N : ℝ))) ≤ E := Real.exp_le_exp.2 (by linarith)
  have hsplit : Real.exp (-(1047 / 1000 * (N : ℝ))) = E * Real.exp (3 / 1000 * N) := by
    rw [hE, ← Real.exp_add]; ring_nf
  have e3 : Real.exp (-((11 / 10 : ℝ) * N)) ≤ E := Real.exp_le_exp.2 (by linarith)
  have h5 : (7 : ℝ) ≤ Real.exp (3 / 1000 * N) := by
    have := Real.add_one_le_exp (3 / 1000 * (N : ℝ)); linarith
  rw [hsplit]
  nlinarith

/-! ### One section -/

/-- **A nonempty section of the conditioned event is `≤ e^{-2N}`** (`N` large, uniformly in `s`). -/
theorem lt3_T7_sectQ9 {L p : ℝ} (hL : lt3Lc ≤ L) (hH : LT3HeavyHypQ9 L p) : ∀ᶠ N : ℕ in atTop,
    ∀ (s : State N) (w0 : Param N), w0 ∈ lt3T7YQ9 L s →
    cubeM N {η | replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w0) w0 η ∈ lt3T7YQ9 L s} ≤
      ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
  obtain ⟨hp, hHv⟩ := hH
  set p0 := min (min p lt3pL) 1 with hp0def
  have hp0 : 0 < p0 := lt_min (lt_min hp lt3pL_pos) one_pos
  have hp01 : p0 ≤ 1 := min_le_right _ _
  have hp0p : p0 ≤ p := (min_le_left _ _).trans (min_le_left _ _)
  have hp0L : p0 ≤ lt3pL := (min_le_left _ _).trans (min_le_right _ _)
  filter_upwards [hHv, lt3_light_member_evQ9 hL, lt3WSel_of_floor_ev (lt3Lc_pos.trans_le hL), eventually_ge_atTop (10 ^ 8 * lt3Cn),
    eventually_ge_atTop (7 * (2300000 * lt3Cn)), lt3_prod_numQ9 hp0] with N hHN hLN hSelF hN8 hN7 hnum
  intro s w0 hw0
  classical
  have hgood := lt3T7Y_goodQ9 hw0
  obtain ⟨⟨hcube, hβ, hZ, hGU, -⟩, -⟩ := hw0
  obtain ⟨hWG, hbd, hnadv⟩ := hgood
  obtain ⟨hm, h7, hm2⟩ := lt3W_good_F s 8319999 lt3Cn_ge hN8 hWG hGU
  have hSp : (lt2Sp w0).card < 12 := hWG.1.2.2.2.1
  have hSel := hSelF s lt3γ 8319999 w0 hZ hβ h7
  set m := qM (lt3WQ s (1 / 21) lt3γ 8319999 w0) with hmdef
  set K := 2300000 * lt3Cn with hK
  have hK0 : 0 < K := by have := lt3Cn_pos; positivity
  have h7K : 7 ≤ N / K := by rw [Nat.le_div_iff_mul_le hK0]; linarith
  have hm7 : 7 ≤ m := h7K.trans hm
  have hND : N ≤ lt3D0 * m := by
    have hlt := Nat.lt_div_mul_add (a := N) hK0
    have h1 : N / K * K ≤ m * K := Nat.mul_le_mul_right K hm
    have h2 : K ≤ m * K := Nat.le_mul_of_pos_left K (by omega)
    have e : lt3D0 * m = 2 * (m * K) := by simp only [lt3D0, hK]; ring
    rw [e]; omega
  have hAdv : 4 * (lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w0).card ≤ m * m := by
    by_contra hc
    exact hnadv ⟨hSp, hm7, hND, not_le.1 hc⟩
  set G := lt3WF s (1 / 21) lt3γ 8319999 w0 \ lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w0 with hGdef
  have hGc : m * m ≤ 4 * G.card := by
    have h1 : (lt3WF s (1 / 21) lt3γ 8319999 w0).card - (lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w0).card ≤
        G.card := Finset.le_card_sdiff _ _
    have h2 : m * m ≤ 2 * (lt3WF s (1 / 21) lt3γ 8319999 w0).card := hm2
    omega
  have hsB : s ∈ lt3Base s w0 := mem_insert_of_mem (mem_insert_self _ _)
  have hGk : ∀ S ∈ G, (S, s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w0 := fun S hS => by
    rw [hSel]; exact mem_product.2 ⟨(mem_sdiff.1 hS).1, hsB⟩
  have hOK : ∀ S ∈ G, LT3MemberOKQ9 L p0 s w0 S := by
    intro S hS
    have hnS := (mem_sdiff.1 hS).2
    by_cases hsH : s ∈ lt3H w0
    · exact (hHN s w0 S hcube hZ hβ hbd hSp hWG (hGk S hS) hnS hsH).mono hp0p
    · exact (hLN s w0 S hcube hSp (hGk S hS) hnS hsH).mono hp0L
  have hsub : {η | replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w0) w0 η ∈ lt3T7YQ9 L s} ⊆
      {η | ∀ S ∈ G, ¬ LT3ConclQ9 L s (replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w0) w0 η) S} := by
    intro η hη S hS hconc
    have hg' := lt3T7Y_goodQ9 hη
    obtain ⟨⟨hc', hβ', hZ', -, hφ'⟩, -⟩ := hη
    obtain ⟨a, b, c, hab, hac, hbc, hS3⟩ := lt3WSel_three (hGk S hS)
    have hS3' : S = {a, b, c} := hS3
    have hcard : S.card = 3 := by
      rw [hS3', card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]
    have h1 := hconc hc' hZ' hβ' hg'.2.1 hg'.1.1.2.2.2.1
    have h2 := hφ' S (by omega) (by omega)
    linarith
  refine (measure_mono hsub).trans ((lt3_nosucc_prodQ9 hp0.le hp01 s w0 G hGk hOK).trans ?_)
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have := hnum m G.card hm hGc
  linarith

/-! ### The assembly -/

/-- Uniformity in the current state: a bound along every sequence of states holds uniformly. -/
lemma ev_forall_stateQ9 {P : ∀ N : ℕ, State N → Prop} (h : ∀ sq : ∀ N, State N, ∀ᶠ N in atTop, P N (sq N)) :
    ∀ᶠ N in atTop, ∀ s : State N, P N s := by
  classical
  by_contra hc
  have hfr : ∃ᶠ N in atTop, ∃ s : State N, ¬ P N s := by
    rw [Filter.not_eventually] at hc
    exact hc.mono fun N hN => not_forall.1 hN
  let sq : ∀ N, State N := fun N => if h : ∃ s : State N, ¬ P N s then h.choose else fun _ => false
  have h2 : ∃ᶠ N in atTop, ¬ P N (sq N) := hfr.mono fun N hN => by
    show ¬ P N (if h : ∃ s : State N, ¬ P N s then h.choose else fun _ => false)
    rw [dif_pos hN]
    exact hN.choose_spec
  exact h2 ((h sq).mono fun N hN hN' => hN' hN)

/-- **The floored LT3 band, from the heavy hypothesis** (open item (b)). -/
theorem lt3HiFl_of_heavyQ9 {L p : ℝ} (hL : lt3Lc ≤ L) (hH : LT3HeavyHypQ9 L p) : LT3HiFlStmtQ9 L (1047 / 1000) := by
  unfold LT3HiFlStmtQ9
  refine ev_forall_stateQ9 (P := fun N s => cubeM N (B1w N s ∩ openCube N ∩ {w | L * sigN N ≤ betaW w ∧
      1 / 2 ≤ Zs w ∧ 4 / 5 ≤ b1YTopR w (tcRow w) (1 / 21) ∧
      ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 9 / 20 * betaW w}) ≤
      ENNReal.ofReal (Real.exp (-(1047 / 1000 * (N : ℝ))))) fun sq => ?_
  have hD1 : 1 ≤ 10 ^ 14 * lt3Cn * lt3Cn := Nat.succ_le_of_lt (by have := lt3Cn_pos; positivity)
  filter_upwards [lt3_T7_sectQ9 hL hH, lt3W_not_good_ev2 sq (1 / 21) 8319999 hD1, bd_not_good_ev,
    lt3_adv_ev lt3D0_pos lt3κ_ge lt3κ_sq, lt3_rate_numQ9, spgu_ev (lt3Lc_pos.trans_le hL)]
    with N hsect hWG hbd hadv hrate hgu
  set s := sq N with hs
  have : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  -- the conditioned event
  have hY : cubeM N (lt3T7YQ9 L s) ≤ ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
    refine lt3W_cond_priv s (1 / 21) lt3γ 8319999 (lt3T7Y_msetQ9 L s) fun A w hA => ?_
    by_cases hne : ∃ η0, replE A w η0 ∈ lt3T7YQ9 L s
    · obtain ⟨η0, hη0⟩ := hne
      have hP0 : stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB (replE A w η0) = A :=
        ((lt3WPriv_detOn (s := s) (ε := 1 / 21) (γ := lt3γ) (n := 8319999) A).replE_out w η0).2 hA
      have e : {η | replE A w η ∈ lt3T7YQ9 L s} =
          {η | replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB (replE A w η0)) (replE A w η0) η ∈
            lt3T7YQ9 L s} := by
        ext η
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hP0, replE_replE]
      rw [e]
      exact hsect s _ hη0
    · push Not at hne
      have e : {η | replE A w η ∈ lt3T7YQ9 L s} = ∅ := by
        ext η
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact hne η
      rw [e, measure_empty]
      exact zero_le
  -- the bad event
  have hbad : {w | ¬ lt3T7GoodQ9 s w} ⊆
      ({w | ¬ lt3WGood s (1 / 21) lt3γ 8319999 (N / 20) (N / 600) 14 (N * N / (10 ^ 14 * lt3Cn * lt3Cn)) w} ∪
        {w | ¬ bdGood w}) ∪
      {w | (lt2Sp w).card < 12 ∧ 7 ≤ qM (lt3WQ s (1 / 21) lt3γ 8319999 w) ∧
        N ≤ lt3D0 * qM (lt3WQ s (1 / 21) lt3γ 8319999 w) ∧
        qM (lt3WQ s (1 / 21) lt3γ 8319999 w) * qM (lt3WQ s (1 / 21) lt3γ 8319999 w) <
          4 * (lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w).card} := by
    intro w hw
    by_cases h1 : lt3WGood s (1 / 21) lt3γ 8319999 (N / 20) (N / 600) 14 (N * N / (10 ^ 14 * lt3Cn * lt3Cn)) w
    · by_cases h2 : bdGood w
      · exact Or.inr (not_not.1 fun h3 => hw ⟨h1, h2, h3⟩)
      · exact Or.inl (Or.inr h2)
    · exact Or.inl (Or.inl h1)
  have hbadM : cubeM N {w | ¬ lt3T7GoodQ9 s w} ≤ ENNReal.ofReal (2 * Real.exp (-((105 / 100 : ℝ) * N)) +
      Real.exp (-(6 / 5 * (N : ℝ))) + Real.exp (-(2 * (N : ℝ)))) := by
    refine (measure_mono hbad).trans ((measure_union_le _ _).trans ?_)
    refine (add_le_add ((measure_union_le _ _).trans (add_le_add hWG hbd)) (hadv s (1 / 21) lt3γ 8319999)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  -- the target
  have hT : B1w N s ∩ openCube N ∩ {w | L * sigN N ≤ betaW w ∧ 1 / 2 ≤ Zs w ∧
      4 / 5 ≤ b1YTopR w (tcRow w) (1 / 21) ∧
      ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 9 / 20 * betaW w} ⊆
      (lt3T7YQ9 L s ∪ toMeasurable (cubeM N) {w | ¬ lt3T7GoodQ9 s w}) ∪
        {w | w ∈ B1w N s ∧ w ∈ openCube N ∧ L * sigN N ≤ betaW w ∧ 1 / 2 ≤ Zs w ∧ lt3SpC s w ∧
          (lt3GoodU s w).card < ⌈(1 / 21 : ℝ) * N⌉₊} := by
    rintro w ⟨⟨hB, hc⟩, hβ, hZ, -, hall⟩
    by_cases hgw : lt3SpC s w → ⌈(1 / 21 : ℝ) * N⌉₊ ≤ (lt3GoodU s w).card
    · by_cases h : w ∈ toMeasurable (cubeM N) {w | ¬ lt3T7GoodQ9 s w}
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl ⟨⟨hc, hβ, hZ, hgw, hall⟩, h⟩)
    · push Not at hgw
      exact Or.inr ⟨hB, hc, hβ, hZ, hgw.1, hgw.2⟩
  refine (measure_mono hT).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add le_rfl (le_of_eq (measure_toMeasurable _))))
    (hgu s)).trans ?_
  refine (add_le_add (add_le_add hY hbadM) le_rfl).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hrate

/-- **The LT3 band (`LT3HiStmtQ9`, B1LTHiSplit) from the heavy hypothesis**, at any `L ≥ lt3Lc`, rate `1.046`. -/
theorem lt3Hi_of_heavyQ9 {L p : ℝ} (hL : lt3Lc ≤ L) (hH : LT3HeavyHypQ9 L p) : LT3HiStmtQ9 L (1046 / 1000) :=
  lt3Hi_of_floorQ9 (lt3Lc_pos.trans_le hL) (by norm_num) (by norm_num) (lt3HiFl_of_heavyQ9 hL hH)

/-- **LTBetaHi from the heavy hypothesis**: `LT3HeavyHypQ9 L p → LTBetaHiStmt (1/4) (104/100)` (`L ≥ lt3Lc`). -/
theorem ltBetaHi_of_heavyQ9 {L p : ℝ} (hL : lt3Lc ≤ L) (hH : LT3HeavyHypQ9 L p) : LTBetaHiStmt (9 / 20) (104 / 100) :=
  ltBetaHi_of_LT3FlQ9 (lt3Lc_one.trans hL) (by norm_num) (lt3HiFl_of_heavyQ9 hL hH)


/-- **Lemma TC' for `s = tc`, packaged at a member** (deterministic, `t = 1/80`): `φ_s(S) ≥ β/4`. -/
theorem lt3_tc_quarterQ9 {w : Param N} (hw : w ∈ openCube N) (s : State N) (hs : s = tcRow w) {a b c : Fin N}
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
    9 / 20 * betaW w ≤ phi (flipP s w) s {a, b, c} := by
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
  have k2 : (9 : ℝ) / 20 ≤ levTrip * T.c0 * (79 / 80) := by nlinarith
  calc 9 / 20 * betaW w ≤ levTrip * T.c0 * (79 / 80) * betaW w := mul_le_mul_of_nonneg_right k2 hβ
    _ ≤ phi (flipP s w) s {a, b, c} := hmain

/-- **A non-adverse member of `s = tc` has a success region of probability `≥ lt3pT`** (`N` large, any band
level `L ≥ lt3Lc`). -/
theorem lt3_tc_member_evQ9 {L : ℝ} (hL : lt3Lc ≤ L) : ∀ᶠ N : ℕ in atTop,
    ∀ (s : State N) (w : Param N) (S : Finset (Fin N)),
    w ∈ openCube N → (lt2Sp w).card < 12 → (S, s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w →
    S ∉ lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w → s = tcRow w → LT3MemberOKQ9 L lt3pT s w S := by
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
    exact lt3_tc_quarterQ9 hw' s hs' hab hac hbc hSp' hHag hT' hreg' hlight hφL hη0
      (hlev a b c hab hac hbc) hηs' hE0'

/-! ### What is left of the heavy hypothesis -/

/-- **The remaining heavy case**: current states `s ∈ Sp \ {tc}` (W8 §7.1, RL-u). -/
def LT3SpHypQ9 (L p : ℝ) : Prop :=
  0 < p ∧ ∀ᶠ N : ℕ in atTop, ∀ (s : State N) (w : Param N) (S : Finset (Fin N)),
    w ∈ openCube N → 1 / 2 ≤ Zs w → L * sigN N ≤ betaW w → bdGood w → (lt2Sp w).card < 12 →
    lt3WGood s (1 / 21) lt3γ 8319999 (N / 20) (N / 600) 14 (N * N / (10 ^ 14 * lt3Cn * lt3Cn)) w →
    (S, s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w → S ∉ lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w →
    s ∈ lt3H w → s ≠ tcRow w → LT3MemberOKQ9 L p s w S

/-- **The heavy hypothesis reduces to `s ∈ Sp \ {tc}`**: the case `s = tc` is `lt3_tc_member_evQ9`. -/
theorem lt3Heavy_of_SpQ9 {L p : ℝ} (hL : lt3Lc ≤ L) (hH : LT3SpHypQ9 L p) : LT3HeavyHypQ9 L (min p lt3pT) := by
  refine ⟨lt_min hH.1 lt3pT_pos, ?_⟩
  filter_upwards [hH.2, lt3_tc_member_evQ9 hL] with N h1 h2
  intro s w S hw hZ hβ hbd hSp hG hk hnadv hsH
  by_cases hs : s = tcRow w
  · exact (h2 s w S hw hSp hk hnadv hs).mono (min_le_right _ _)
  · exact (h1 s w S hw hZ hβ hbd hSp hG hk hnadv hsH hs).mono (min_le_left _ _)

/-- **LTBetaHi from the remaining heavy case** `s ∈ Sp \ {tc}`. -/
theorem ltBetaHi_of_SpQ9 {L p : ℝ} (hL : lt3Lc ≤ L) (hH : LT3SpHypQ9 L p) : LTBetaHiStmt (9 / 20) (104 / 100) :=
  ltBetaHi_of_heavyQ9 hL (lt3Heavy_of_SpQ9 hL hH)


/-- **Lemma TC' for `s ∈ Sp \ {tc}`, packaged at a member** (deterministic, `t = 1/80`): `φ_s(S) ≥ β/4`. -/
theorem lt3_u_quarterQ9 {w : Param N} (hw : w ∈ openCube N) (s : State N) (hsH : s ∈ lt3H w) (hstc : s ≠ tcRow w)
    (hH2 : ((lt3H w).erase s).card ≤ 2) {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hSp : (lt2Sp w).card < 12)
    (hH : ∀ r ∈ lt3H w, (∀ j ∈ ({a, b, c} : Finset (Fin N)), r j = tcRow w j) ∨
      (∀ j ∈ ({a, b, c} : Finset (Fin N)), r j ≠ tcRow w j))
    (hT : lt3Uthr (lt3Uds w {a, b, c} s) - 1 / 1000 ≤ (lt3UTab w (pkE3 hab hac hbc) {a, b, c} s).2 ∧
      RLUWin (lt3Uds w {a, b, c} s) (lt3URestD w (pkE3 hab hac hbc) {a, b, c} s)
        (lt3Uwu w (pkE3 hab hac hbc) {a, b, c} s) (lt3UX w (pkE3 hab hac hbc) s) (lt3UF w (pkE3 hab hac hbc) s)
        (1 / 320000) (lt3UTab w (pkE3 hab hac hbc) {a, b, c} s).2 (lt3UTab w (pkE3 hab hac hbc) {a, b, c} s).1)
    (hreg : w ∈ lt3URegion w (pkE3 hab hac hbc) {a, b, c} s (1 / 4160000))
    {φL η : ℝ}
    (hlight : ∀ (t0 : State N) (u : Fin (2 ^ 3)) (i : Fin 3),
      |lt3Light w {a, b, c} (lt3H w) (pkFlip (pkE3 hab hac hbc) t0 u) (pkE3 hab hac hbc i) -
        lt3Light w {a, b, c} (lt3H w) t0 (pkE3 hab hac hbc i)| ≤ φL)
    (hφL : φL ≤ Pw w (tcRow w) / 320000) (hη0 : 0 ≤ η)
    (hlev : ∀ Y ⊆ ({a, b, c} : Finset (Fin N)), ∀ t', ∀ i ∈ ({a, b, c} : Finset (Fin N)),
      |Num w {a, b, c} Y t' i - lvK 3 * Zs w| ≤ η)
    (hηs : η ^ 2 ≤ Pw w (tcRow w) * (lvK 3 * Zs w) / (8 * 10 ^ 7))
    (hE0 : 6 * η / ((lvK 3 * Zs w - η) * Real.log 2) ≤ lt3E0u (1 / 2)) :
    9 / 20 * betaW w ≤ phi (flipP s w) s {a, b, c} := by
  classical
  set e := pkE3 hab hac hbc with he
  have hS := pkE3_S hab hac hbc
  set T := (lt3UTab w e {a, b, c} s).1 with hTdef
  set x0 := (lt3UTab w e {a, b, c} s).2 with hx0def
  obtain ⟨hx0, hTw⟩ := hT
  obtain ⟨hregR, hregT⟩ := hreg
  have hY01 := hTw.2.2.2.2.2.1
  have hc45 := hTw.2.1
  -- `s`'s box with the raw targets
  have hboxT : w ∈ lt3Box e {a, b, c} s {s} (fun u i => T.Y u i) (1 / 4160000) := by
    intro x hx
    have h := hregT x hx
    obtain ⟨hx1, hv⟩ := mem_lt3BoxIdx.1 hx
    have hx1' : x.1 = s := mem_singleton.1 hx1
    have hag : ∀ j ∈ ({a, b, c} : Finset (Fin N)), x.1 j = s j := fun j _ => by rw [hx1']
    simp only [lt3BoxTgt, if_pos hag] at h ⊢
    have hcl : clamp01 (T.Y x.2.1 x.2.2) = T.Y x.2.1 x.2.2 :=
      clamp01_of_mem ⟨(hY01 x.2.1 x.2.2 hv).1, (hY01 x.2.1 x.2.2 hv).2⟩
    rwa [hcl] at h
  -- the effect side
  have hρY : ∀ (u : Fin (2 ^ 3)) (i : Fin 3), ¬((u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ)) →
      |clamp01 (w (pkFlip e s u) (e i)) - T.Y u i| ≤ 1 / 4160000 := by
    intro u i hv
    have h := hboxT (s, u, i) (mem_lt3BoxIdx.2 ⟨mem_singleton_self _, hv⟩)
    simp only [lt3BoxE, lt3BoxTgt] at h
    rwa [if_pos (fun _ _ => trivial)] at h
  have hax : (1 / 2 : ℝ) ≤ x0 := by
    unfold lt3Uthr at hx0; split_ifs at hx0 <;> linarith
  have heff := lt3_heff_u hw s e hS hTw (a := 1 / 2) (by norm_num) hax (by norm_num) (by norm_num) (by norm_num) hρY
  -- the scale
  have hsag := lt3Uds_spec (hH s hsH)
  have hσ1 := lt3Usig_ge hw e {a, b, c} s
  have hσ0 := b1_Pw_pos hw (tcRow w)
  have hσ2 : lt3Usig w e {a, b, c} s ≤ 2 * Zs w := by
    have hS0 : ({a, b, c} : Finset (Fin N)).Nonempty := ⟨a, by simp⟩
    have htcH' : tcRow w ∈ (lt3H w).erase s := mem_erase.2 ⟨fun h => hstc h.symm, mem_insert_self _ _⟩
    obtain ⟨hV1, -⟩ := lt3U_V_bounds e hS0 htcH' hH2 hσ0 (fun r => Pw_le_tcRow w r)
    obtain ⟨hl1, -, hlV⟩ := lt3Ulam_bounds hw e {a, b, c} s
    have hl2 : lt3Ulam w e {a, b, c} s ≤ 2 := hlV.trans (max_le (by norm_num) hV1)
    have hZ : Pw w (tcRow w) ≤ Zs w :=
      single_le_sum (f := fun r => Pw w r) (fun r _ => Pw_nonneg w r) (mem_univ _)
    unfold lt3Usig
    nlinarith
  have hA0 : 0 ≤ lvK 3 * Zs w := mul_nonneg (lvK_pos 3).le (b1_Zs_pos hw).le
  have hφL' : φL ≤ lt3Usig w e {a, b, c} s / 320000 := hφL.trans (div_le_div_of_nonneg_right hσ1 (by norm_num))
  have hηs' : η ^ 2 ≤ lt3Usig w e {a, b, c} s * (lvK 3 * Zs w) / (8 * 10 ^ 7) :=
    hηs.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hσ1 hA0) (by norm_num))
  have hmain := lt3_TCprime_u hw s hab hac hbc (lt3H w) (lt3H_card hSp) hsH (lt3Uds w {a, b, c} s) hsag hH
    hσ1 hσ2 T hTw (by norm_num) (by norm_num) (by norm_num) hregR hboxT hlight hφL' hη0 hlev hηs' hE0 heff
  have hβ : 0 ≤ betaW w := div_nonneg (Pw_nonneg w _) (b1_Zs_pos hw).le
  have hlt := levTrip_gt
  have k1 : (577 / 1000 : ℝ) * (4 / 5) ≤ levTrip * T.c0 := mul_le_mul hlt.le hc45 (by norm_num) levTrip_pos.le
  have k2 : (9 : ℝ) / 20 ≤ levTrip * T.c0 * (79 / 80) := by nlinarith
  calc 9 / 20 * betaW w ≤ levTrip * T.c0 * (79 / 80) * betaW w := mul_le_mul_of_nonneg_right k2 hβ
    _ ≤ phi (flipP s w) s {a, b, c} := hmain

/-- **A non-adverse member with `s ∈ Sp \ {tc}` and `|H \ {s}| ≤ 2` has a success region of probability
`≥ lt3pT`** (`N` large, any band level `L ≥ lt3Lc`). -/
theorem lt3_u_member_evQ9 {L : ℝ} (hL : lt3Lc ≤ L) : ∀ᶠ N : ℕ in atTop,
    ∀ (s : State N) (w : Param N) (S : Finset (Fin N)),
    w ∈ openCube N → (lt2Sp w).card < 12 → (S, s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w →
    S ∉ lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w → s ∈ lt3H w → s ≠ tcRow w → ((lt3H w).erase s).card ≤ 2 →
    LT3MemberOKQ9 L lt3pT s w S := by
  have hL0 : 0 < L := lt3Lc_pos.trans_le hL
  have hLκ : 768000 * lt3κ ≤ (1 / 80 : ℝ) * L := by have := lt3Lc_κ; linarith
  filter_upwards [bd_band (t := 1 / 80) (L := L) (by norm_num) hL0, bd_E0_ev (lt3E0u_pos (a := 1 / 2) (by norm_num)),
    bd_tc_Sp_ev hL0, lt3_pert_ev (t := 1 / 80) (by norm_num)] with N hBand hE0 hTc hPert
  intro s w S hw hSp hk hnadv hsH hstc hH2
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hS⟩ := lt3WSel_three hk
  have hS' : S = {a, b, c} := hS
  subst hS'
  set A := stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w with hA
  set e := pkE3 hab hac hbc with he
  have hSe := pkE3_S hab hac hbc
  obtain ⟨-, h7, -, -, -, hSWQ, hag⟩ := lt3W_mem hk
  set tc := tcRow w with htc
  set H' := (lt3H w).erase s with hH'
  set T := (lt3UTab w e {a, b, c} s).1 with hTdef
  have hT := lt3UTab_spec hw hab hac hbc hk hsH hstc hH2
  set ρ : ℝ := 1 / 4160000 with hρ
  set ds := lt3Uds w {a, b, c} s with hds
  set wu := lt3Uwu w e {a, b, c} s with hwu
  set Ur := lt3Box e {a, b, c} tc H' (lt3Tgt (lt3URestD w e {a, b, c} s) (lt3URest w e s ds wu T)) ρ with hUr
  set Ut := lt3Box e {a, b, c} s {s} (fun u i => clamp01 (T.Y u i)) ρ with hUt
  -- blocks
  have hsubR : H'.biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)) ⊆
      (lt3Base s w).biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)) :=
    biUnion_subset_biUnion_of_subset_left _ ((erase_subset _ _).trans (lt3H_sub_base s w))
  have hsubT : ({s} : Finset (State N)).biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)) ⊆
      (lt3Base s w).biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)) :=
    biUnion_subset_biUnion_of_subset_left _ (singleton_subset_iff.2 (lt3H_sub_base s w hsH))
  have hdisj : Disjoint (H'.biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)))
      (({s} : Finset (State N)).biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r))) := by
    rw [Finset.disjoint_biUnion_left]
    intro r hr
    rw [singleton_biUnion]
    have hrH := mem_of_mem_erase hr
    refine lt3WPB_disjoint w (lt3W_mem_base hk (lt3H_sub_base s w hrH)) (lt3W_mem_base hk (lt3H_sub_base s w hsH)) ?_
    intro h
    exact (ne_of_mem_erase hr) (Prod.ext_iff.1 h).2
  have hUrm : MeasurableSet Ur := lt3Box_mset _ _ _ _ _ _
  have hUtm : MeasurableSet Ut := lt3Box_mset _ _ _ _ _ _
  have hUrd := lt3Box_detOn hSe tc H' (lt3Tgt (lt3URestD w e {a, b, c} s) (lt3URest w e s ds wu T)) ρ
  have hUtd := lt3Box_detOn hSe s {s} (fun u i => clamp01 (T.Y u i)) ρ
  refine ⟨Ur ∩ Ut, hUrm.inter hUtm, (hUrd.mono hsubR).inter (hUtd.mono hsubT), ?_, ?_⟩
  · -- probability
    rw [cubeM_inter_eq_mul_of_detOnE hdisj hUrm hUtm hUrd hUtd]
    have hSQ : ({a, b, c} : Finset (Fin N)) ⊆ lt3Q s (1 / 21) lt3γ w := hSWQ.trans (lt3WQ_sub _ _ _ _ _)
    have hQ7 : 7 ≤ (lt3Q s (1 / 21) lt3γ w).card := h7.trans (card_le_card (lt3WQ_sub _ _ _ _ _))
    have hσ1 := lt3Usig_ge hw e {a, b, c} s
    have hσ : 0 < lt3Usig w e {a, b, c} s := (b1_Pw_pos hw tc).trans_le hσ1
    obtain ⟨hG1n, hF1n, hG2n, hF2n, hG1V, hF1V, hG2V, hF2V, hV1n, hV2n, -⟩ :=
      lt3RD_bounds w e {a, b, c} tc H' hσ (fun r => (Pw_le_tcRow w r).trans hσ1)
    have hlw := rlLoR_wd_bounds _ hG1n hF1n hG2n hF2n hG1V hF1V hG2V hF2V hV1n hV2n
    have hTg := lt3Tgt_spec (lt3URestD w e {a, b, c} s) (lt3URest w e s ds wu T) (fun u i => hT.2.2.2.2.2.1 u i)
      (fun u i => (hlw u i).2.1)
    have hρ0 : (0 : ℝ) ≤ ρ := by rw [hρ]; norm_num
    have hρ1 : ρ ≤ 1 := by rw [hρ]; norm_num
    have hpR := lt3Box_prob hSe hSQ hQ7 (H := H') (tc := tc)
      (fun r hr => hag r (lt3H_sub_base s w (mem_of_mem_erase hr))) (fun u i => (hTg u i).2) hρ0 hρ1
    have hpT := lt3Box_prob hSe hSQ hQ7 (H := {s}) (tc := s)
      (fun r hr => by rw [mem_singleton.1 hr]; exact Or.inl fun j _ => rfl)
      (τ := fun u i => clamp01 (T.Y u i)) (fun u i => ⟨clamp01_nonneg _, clamp01_le_one _⟩) hρ0 hρ1
    rw [card_singleton] at hpT
    have hH'c : H'.card ≤ 2 := hH2
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
    obtain ⟨hD, hds', hwu', hTab⟩ := lt3UData_replE hab hac hbc hk hsH η
    have hk' : (({a, b, c} : Finset (Fin N)), s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w' := by
      rw [hw'def, hA, lt3W_replE_sel]; exact hk
    have hF' := (lt3W_mem hk').2.2.2.1
    have hAdv' : ({a, b, c} : Finset (Fin N)) ∉ lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w' := by
      rw [hw'def, hA, lt3Adv_replE]; exact hnadv
    have hsH' : s ∈ lt3H w' := by rw [hHw]; exact hsH
    have hstc' : s ≠ tcRow w' := by rw [ht]; exact hstc
    have hH2' : ((lt3H w').erase s).card ≤ 2 := by rw [hHw]; exact hH2
    -- the region at `w'`
    have hreg' : w' ∈ lt3URegion w' e {a, b, c} s ρ := by
      have hU' : lt3URest w' e s ds wu T = lt3URest w e s ds wu T := by
        funext u i
        unfold lt3URest
        have hrow' : w' s = w s := hrow _ hsH
        have hflip' : ∀ i : Fin 3, w' (flip s (e i)) (e i) = w (flip s (e i)) (e i) := hflip _ hsH
        simp only [hrow', hflip']
      unfold lt3URegion
      rw [hds', hwu', hTab, hD, ← hds, ← hwu, ← hTdef, hU', ht, hHw]
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
      · exact (biUnion_subset_biUnion_of_subset_left _ (singleton_subset_iff.2 hsH)) hq
    -- the table at `w'`
    have hT' := lt3UTab_spec hw' hab hac hbc hk' hsH' hstc' hH2'
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
    exact lt3_u_quarterQ9 hw' s hsH' hstc' hH2' hab hac hbc hSp' hHag hT' hreg' hlight hφL hη0
      (hlev a b c hab hac hbc) hηs' hE0'


def lt3T7Tm2Q9 (L : ℝ) (s : State N) : Set (Param N) :=
  {w | w ∈ lt3T7TmQ9 L s ∧ (s ∈ lt2Sp w → ((lt2Sp w).erase s).card < 3)}

/-- The conditioned event. -/
def lt3T7Y2Q9 (L : ℝ) (s : State N) : Set (Param N) :=
  lt3T7Tm2Q9 L s ∩ (toMeasurable (cubeM N) {w | ¬ lt3T7GoodQ9 s w})ᶜ

lemma lt3T7Tm2_msetQ9 (L : ℝ) (s : State N) : MeasurableSet (lt3T7Tm2Q9 L s) := by
  classical
  have e : lt3T7Tm2Q9 L s = lt3T7TmQ9 L s ∩ {w | s ∈ lt2Sp w → ((lt2Sp w).erase s).card < 3} := rfl
  rw [e]
  refine (lt3T7Tm_msetQ9 L s).inter ?_
  have h := fibM_comp (f := fun w : Param N => (lt2Sp w, tcRow w)) fibM_SpTc
    (fun d => decide (s ∈ d.1 → (d.1.erase s).card < 3)) true
  convert h using 1
  ext w
  simp only [Set.mem_setOf_eq, decide_eq_true_eq]

lemma lt3T7Y2_msetQ9 (L : ℝ) (s : State N) : MeasurableSet (lt3T7Y2Q9 L s) :=
  (lt3T7Tm2_msetQ9 L s).inter (measurableSet_toMeasurable _ _).compl

lemma lt3T7Y2_goodQ9 {L : ℝ} {s : State N} {w : Param N} (h : w ∈ lt3T7Y2Q9 L s) : lt3T7GoodQ9 s w := by
  by_contra hc
  exact h.2 (subset_toMeasurable _ _ hc)

/-- `|H \ {s}| ≤ 2` from `|Sp \ {s}| < 3` and `tc ∈ Sp`. -/
lemma lt3H_erase_cardQ9 {w : Param N} {s : State N} (htc : tcRow w ∈ lt2Sp w) (h : ((lt2Sp w).erase s).card < 3) :
    ((lt3H w).erase s).card ≤ 2 := by
  have e : lt3H w = lt2Sp w := insert_eq_of_mem htc
  rw [e]; omega

/-- **A nonempty section of the conditioned event is `≤ e^{-2N}`** (`N` large, uniformly in `s`), with every heavy
member discharged. -/
theorem lt3_T7_sect2Q9 {L : ℝ} (hL : lt3Lc ≤ L) : ∀ᶠ N : ℕ in atTop,
    ∀ (s : State N) (w0 : Param N), w0 ∈ lt3T7Y2Q9 L s →
    cubeM N {η | replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w0) w0 η ∈ lt3T7Y2Q9 L s} ≤
      ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
  set p0 := min (min lt3pT lt3pL) 1 with hp0def
  have hp0 : 0 < p0 := lt_min (lt_min lt3pT_pos lt3pL_pos) one_pos
  have hp01 : p0 ≤ 1 := min_le_right _ _
  have hp0T : p0 ≤ lt3pT := (min_le_left _ _).trans (min_le_left _ _)
  have hp0L : p0 ≤ lt3pL := (min_le_left _ _).trans (min_le_right _ _)
  have hL0 : 0 < L := lt3Lc_pos.trans_le hL
  filter_upwards [lt3_tc_member_evQ9 hL, lt3_u_member_evQ9 hL, lt3_light_member_evQ9 hL, lt3WSel_of_floor_ev hL0,
    bd_tc_Sp_ev hL0, eventually_ge_atTop (10 ^ 8 * lt3Cn), eventually_ge_atTop (7 * (2300000 * lt3Cn)),
    lt3_prod_numQ9 hp0] with N hTcN hUN hLN hSelF hTcSp hN8 hN7 hnum
  intro s w0 hw0
  classical
  have hgood := lt3T7Y2_goodQ9 hw0
  obtain ⟨⟨⟨hcube, hβ, hZ, hGU, -⟩, hspr⟩, -⟩ := hw0
  obtain ⟨hWG, hbd, hnadv⟩ := hgood
  obtain ⟨hm, h7, hm2⟩ := lt3W_good_F s 8319999 lt3Cn_ge hN8 hWG hGU
  have hSp : (lt2Sp w0).card < 12 := hWG.1.2.2.2.1
  have hSel := hSelF s lt3γ 8319999 w0 hZ hβ h7
  set m := qM (lt3WQ s (1 / 21) lt3γ 8319999 w0) with hmdef
  set K := 2300000 * lt3Cn with hK
  have hK0 : 0 < K := by have := lt3Cn_pos; positivity
  have h7K : 7 ≤ N / K := by rw [Nat.le_div_iff_mul_le hK0]; linarith
  have hm7 : 7 ≤ m := h7K.trans hm
  have hND : N ≤ lt3D0 * m := by
    have hlt := Nat.lt_div_mul_add (a := N) hK0
    have h1 : N / K * K ≤ m * K := Nat.mul_le_mul_right K hm
    have h2 : K ≤ m * K := Nat.le_mul_of_pos_left K (by omega)
    have e : lt3D0 * m = 2 * (m * K) := by simp only [lt3D0, hK]; ring
    rw [e]; omega
  have hAdv : 4 * (lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w0).card ≤ m * m := by
    by_contra hc
    exact hnadv ⟨hSp, hm7, hND, not_le.1 hc⟩
  set G := lt3WF s (1 / 21) lt3γ 8319999 w0 \ lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w0 with hGdef
  have hGc : m * m ≤ 4 * G.card := by
    have h1 : (lt3WF s (1 / 21) lt3γ 8319999 w0).card - (lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w0).card ≤
        G.card := Finset.le_card_sdiff _ _
    have h2 : m * m ≤ 2 * (lt3WF s (1 / 21) lt3γ 8319999 w0).card := hm2
    omega
  have hsB : s ∈ lt3Base s w0 := mem_insert_of_mem (mem_insert_self _ _)
  have hGk : ∀ S ∈ G, (S, s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w0 := fun S hS => by
    rw [hSel]; exact mem_product.2 ⟨(mem_sdiff.1 hS).1, hsB⟩
  have hOK : ∀ S ∈ G, LT3MemberOKQ9 L p0 s w0 S := by
    intro S hS
    have hnS := (mem_sdiff.1 hS).2
    by_cases hsH : s ∈ lt3H w0
    · by_cases hs : s = tcRow w0
      · exact (hTcN s w0 S hcube hSp (hGk S hS) hnS hs).mono hp0T
      · have hsSp : s ∈ lt2Sp w0 := (mem_insert.1 hsH).resolve_left hs
        have hH2 := lt3H_erase_cardQ9 (hTcSp w0 hcube hZ hβ) (hspr hsSp)
        exact (hUN s w0 S hcube hSp (hGk S hS) hnS hsH hs hH2).mono hp0T
    · exact (hLN s w0 S hcube hSp (hGk S hS) hnS hsH).mono hp0L
  have hsub : {η | replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w0) w0 η ∈ lt3T7Y2Q9 L s} ⊆
      {η | ∀ S ∈ G, ¬ LT3ConclQ9 L s (replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w0) w0 η) S} := by
    intro η hη S hS hconc
    have hg' := lt3T7Y2_goodQ9 hη
    obtain ⟨⟨⟨hc', hβ', hZ', -, hφ'⟩, -⟩, -⟩ := hη
    obtain ⟨a, b, c, hab, hac, hbc, hS3⟩ := lt3WSel_three (hGk S hS)
    have hS3' : S = {a, b, c} := hS3
    have hcard : S.card = 3 := by
      rw [hS3', card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]
    have h1 := hconc hc' hZ' hβ' hg'.2.1 hg'.1.1.2.2.2.1
    have h2 := hφ' S (by omega) (by omega)
    linarith
  refine (measure_mono hsub).trans ((lt3_nosucc_prodQ9 hp0.le hp01 s w0 G hGk hOK).trans ?_)
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have := hnum m G.card hm hGc
  linarith

/-- `e^{-2N} + (2e^{-1.05N} + e^{-1.2N} + e^{-2N}) + 2e^{-1.1N} + e^{-1.07N} ≤ e^{-1.047N}` for `N` large. -/
lemma lt3_rate_num2Q9 : ∀ᶠ N : ℕ in atTop, Real.exp (-(2 * (N : ℝ))) +
    (2 * Real.exp (-((105 / 100 : ℝ) * N)) + Real.exp (-(6 / 5 * (N : ℝ))) + Real.exp (-(2 * (N : ℝ)))) +
      2 * Real.exp (-((11 / 10 : ℝ) * N)) + Real.exp (-((107 / 100 : ℝ) * N)) ≤
      Real.exp (-(1047 / 1000 * (N : ℝ))) := by
  filter_upwards [eventually_ge_atTop 3000] with N hN
  have hNr : (3000 : ℝ) ≤ N := by exact_mod_cast hN
  set E := Real.exp (-((105 / 100 : ℝ) * N)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have e1 : Real.exp (-(2 * (N : ℝ))) ≤ E := Real.exp_le_exp.2 (by linarith)
  have e2 : Real.exp (-(6 / 5 * (N : ℝ))) ≤ E := Real.exp_le_exp.2 (by linarith)
  have e3 : Real.exp (-((11 / 10 : ℝ) * N)) ≤ E := Real.exp_le_exp.2 (by linarith)
  have e4 : Real.exp (-((107 / 100 : ℝ) * N)) ≤ E := Real.exp_le_exp.2 (by linarith)
  have hsplit : Real.exp (-(1047 / 1000 * (N : ℝ))) = E * Real.exp (3 / 1000 * N) := by
    rw [hE, ← Real.exp_add]; ring_nf
  have h5 : (9 : ℝ) ≤ Real.exp (3 / 1000 * N) := by
    have := Real.add_one_le_exp (3 / 1000 * (N : ℝ)); linarith
  rw [hsplit]
  nlinarith

/-- **The floored LT3 band, unconditionally** (`L ≥ lt3Lc`). -/
theorem lt3HiFl_finalQ9 {L : ℝ} (hL : lt3Lc ≤ L) : LT3HiFlStmtQ9 L (1047 / 1000) := by
  unfold LT3HiFlStmtQ9
  refine ev_forall_stateQ9 (P := fun N s => cubeM N (B1w N s ∩ openCube N ∩ {w | L * sigN N ≤ betaW w ∧
      1 / 2 ≤ Zs w ∧ 4 / 5 ≤ b1YTopR w (tcRow w) (1 / 21) ∧
      ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 9 / 20 * betaW w}) ≤
      ENNReal.ofReal (Real.exp (-(1047 / 1000 * (N : ℝ))))) fun sq => ?_
  have hD1 : 1 ≤ 10 ^ 14 * lt3Cn * lt3Cn := Nat.succ_le_of_lt (by have := lt3Cn_pos; positivity)
  filter_upwards [lt3_T7_sect2Q9 hL, lt3W_not_good_ev2 sq (1 / 21) 8319999 hD1, bd_not_good_ev,
    lt3_adv_ev lt3D0_pos lt3κ_ge lt3κ_sq, lt3_rate_num2Q9, spgu_ev (lt3Lc_pos.trans_le hL), spr_ev]
    with N hsect hWG hbd hadv hrate hgu hspr
  set s := sq N with hs
  have : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  -- the conditioned event
  have hY : cubeM N (lt3T7Y2Q9 L s) ≤ ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
    refine lt3W_cond_priv s (1 / 21) lt3γ 8319999 (lt3T7Y2_msetQ9 L s) fun A w hA => ?_
    by_cases hne : ∃ η0, replE A w η0 ∈ lt3T7Y2Q9 L s
    · obtain ⟨η0, hη0⟩ := hne
      have hP0 : stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB (replE A w η0) = A :=
        ((lt3WPriv_detOn (s := s) (ε := 1 / 21) (γ := lt3γ) (n := 8319999) A).replE_out w η0).2 hA
      have e : {η | replE A w η ∈ lt3T7Y2Q9 L s} =
          {η | replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB (replE A w η0)) (replE A w η0) η ∈
            lt3T7Y2Q9 L s} := by
        ext η
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hP0, replE_replE]
      rw [e]
      exact hsect s _ hη0
    · push Not at hne
      have e : {η | replE A w η ∈ lt3T7Y2Q9 L s} = ∅ := by
        ext η
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact hne η
      rw [e, measure_empty]
      exact zero_le
  -- the bad event
  have hbad : {w | ¬ lt3T7GoodQ9 s w} ⊆
      ({w | ¬ lt3WGood s (1 / 21) lt3γ 8319999 (N / 20) (N / 600) 14 (N * N / (10 ^ 14 * lt3Cn * lt3Cn)) w} ∪
        {w | ¬ bdGood w}) ∪
      {w | (lt2Sp w).card < 12 ∧ 7 ≤ qM (lt3WQ s (1 / 21) lt3γ 8319999 w) ∧
        N ≤ lt3D0 * qM (lt3WQ s (1 / 21) lt3γ 8319999 w) ∧
        qM (lt3WQ s (1 / 21) lt3γ 8319999 w) * qM (lt3WQ s (1 / 21) lt3γ 8319999 w) <
          4 * (lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w).card} := by
    intro w hw
    by_cases h1 : lt3WGood s (1 / 21) lt3γ 8319999 (N / 20) (N / 600) 14 (N * N / (10 ^ 14 * lt3Cn * lt3Cn)) w
    · by_cases h2 : bdGood w
      · exact Or.inr (not_not.1 fun h3 => hw ⟨h1, h2, h3⟩)
      · exact Or.inl (Or.inr h2)
    · exact Or.inl (Or.inl h1)
  have hbadM : cubeM N {w | ¬ lt3T7GoodQ9 s w} ≤ ENNReal.ofReal (2 * Real.exp (-((105 / 100 : ℝ) * N)) +
      Real.exp (-(6 / 5 * (N : ℝ))) + Real.exp (-(2 * (N : ℝ)))) := by
    refine (measure_mono hbad).trans ((measure_union_le _ _).trans ?_)
    refine (add_le_add ((measure_union_le _ _).trans (add_le_add hWG hbd)) (hadv s (1 / 21) lt3γ 8319999)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  -- the target
  have hT : B1w N s ∩ openCube N ∩ {w | L * sigN N ≤ betaW w ∧ 1 / 2 ≤ Zs w ∧
      4 / 5 ≤ b1YTopR w (tcRow w) (1 / 21) ∧
      ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 9 / 20 * betaW w} ⊆
      ((lt3T7Y2Q9 L s ∪ toMeasurable (cubeM N) {w | ¬ lt3T7GoodQ9 s w}) ∪
        {w | w ∈ B1w N s ∧ w ∈ openCube N ∧ L * sigN N ≤ betaW w ∧ 1 / 2 ≤ Zs w ∧ lt3SpC s w ∧
          (lt3GoodU s w).card < ⌈(1 / 21 : ℝ) * N⌉₊}) ∪
        {w | s ∈ lt2Sp w ∧ 3 ≤ ((lt2Sp w).erase s).card} := by
    rintro w ⟨⟨hB, hc⟩, hβ, hZ, -, hall⟩
    by_cases hsp : s ∈ lt2Sp w → ((lt2Sp w).erase s).card < 3
    · refine Or.inl ?_
      by_cases hgw : lt3SpC s w → ⌈(1 / 21 : ℝ) * N⌉₊ ≤ (lt3GoodU s w).card
      · by_cases h : w ∈ toMeasurable (cubeM N) {w | ¬ lt3T7GoodQ9 s w}
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl ⟨⟨⟨hc, hβ, hZ, hgw, hall⟩, hsp⟩, h⟩)
      · push Not at hgw
        exact Or.inr ⟨hB, hc, hβ, hZ, hgw.1, hgw.2⟩
    · push Not at hsp
      exact Or.inr hsp
  refine (measure_mono hT).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add le_rfl (le_of_eq (measure_toMeasurable _)))) (hgu s))) (hspr s)).trans ?_
  refine (add_le_add (add_le_add (add_le_add hY hbadM) le_rfl) le_rfl).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hrate

/-- **The LT3 band (`LT3HiStmtQ9`)**, at any `L ≥ lt3Lc`, rate `1.046`. -/
theorem lt3Hi_finalQ9 {L : ℝ} (hL : lt3Lc ≤ L) : LT3HiStmtQ9 L (1046 / 1000) :=
  lt3Hi_of_floorQ9 (lt3Lc_pos.trans_le hL) (by norm_num) (by norm_num) (lt3HiFl_finalQ9 hL)

/-- **LTBetaHi, proved**: `LTBetaHiStmt (1/4) (104/100)`. -/
theorem ltBetaHi_finalQ9 : LTBetaHiStmt (9 / 20) (104 / 100) :=
  ltBetaHi_of_LT3FlQ9 lt3Lc_one (by norm_num) (lt3HiFl_finalQ9 (L := lt3Lc) le_rfl)


/-- **LTβ from LT2 and the high-`β` statement.** -/
theorem ltBeta_of_LT2_hiQ9 {C C₁ C₂ : ℝ} (h1 : C < C₁) (h2 : C < C₂) (hLT : LT2Stmt 1 C₁)
    (hHi : LTBetaHiStmt (9 / 20) C₂) : LTBetaStmt (9 / 20) C := by
  filter_upwards [hLT, hHi, g_union_rate h1 h2] with N hL hH hU s
  refine (measure_mono ?_).trans (hU _ _ (hL s) (hH s))
  rintro w ⟨hw, hall⟩
  by_cases hb : sigN N ≤ betaW w
  · exact Or.inr ⟨hw, hb, hall⟩
  · refine Or.inl ⟨by linarith [not_le.1 hb], fun S hS => ?_⟩
    have := hall S (by omega) (by omega)
    have hβ := betaW_nonneg w
    linarith [not_le.1 hb]
/-- **LTβ at level `9/20`.** -/
theorem ltBeta920_at {C : ℝ} (hC : C < 104 / 100) : LTBetaStmt (9 / 20) C :=
  ltBeta_of_LT2_hiQ9 hC hC lt2_proved ltBetaHi_finalQ9

end Census
end IIT
