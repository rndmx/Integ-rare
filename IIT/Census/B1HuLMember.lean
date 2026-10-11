/-
Census, B1 forced leaf 7, `NatLT3Hu` part (c) (light `s`), stage **Member**: the natural level of a successful
member and the success region of a light member, at the `ε = dnEps = 10⁻⁵` constants of `B1HuLGood`.

* `lt3_member_TopG`: for light `s` (`s ∉ lt3H w`) the units of a member of `lt3WSel s ε γ n_b w` lie in the global
  `Top(ε)`, i.e. `y_top(ε) ≤ y_{tc,j}`.
* `lt3_level_natE5`: `c0 ≥ 4/5`, `c0 ≥ y - ω'` ⇒ `(1 - ε) Lv y β ≤ Lv c0 (1 - 483t/800) β` (any `y`; `y ≥ 1/2` is
  `lt3_levelE5`, `y < 1/2` is absorbed by `c0 ≥ 4/5`).
* **`lt3W_TCprime_natE5`** (the analogue of `lt3W_TCprime_quarter`): Lemma TC' (`lt3W_TCprime_ev`) at
  `t = lt3tE5`, `n_b = lt3nbE5`, `n_g = lt3ngE5`, `ω' = lt3ωE5`, `ρ = lt3ρE5` gives the **natural level**
  `(1 - dnEps) levTrip y_top(dnEps) β ≤ φ_s({a,b,c})` for members of a light `s`.
* `LT3ConclE5`, `LT3MemberOKE5`: the conclusion / success region at the natural level and the `ε = 10⁻⁵` selection.
* **`lt3_light_member_evE5`** (analogue of `lt3_light_member_ev`): for `L ≥ lt3LcE5`, every non-adverse member of a
  light `s` has a success region of probability `≥ lt3pLE5` (cause box `ρ^234` of `lt3WSucc_prob` times effect box
  `ρe^24`). The band (`bd_band`), `bd_E0_ev`, `bd_tc_Sp_ev`, `lt3_hHalf_of_not_adv`, `lt3_phiH_le`, `lt3_heff_light`,
  `lt3EBox_*` are generic and used as is; `lt3H` is unchanged by resampling (`lt3W_replE_frame`), so `s` stays light.
* `lt3_nosucc_prodE5`: the conditional product `e^{-p|G|}` for `LT3MemberOKE5` (copy of `lt3_nosucc_prod`).
-/
import IIT.Census.B1HuLGood
import IIT.Census.B1LTHiTcM

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-! ### The natural level -/

/-- **Members of a light `s` lie in the global `Top(ε)`.** -/
lemma lt3_member_TopG {s : State N} {ε γ : ℝ} {nb : ℕ} {w : Param N} {S : Finset (Fin N)} {r0 : State N}
    (hk : (S, r0) ∈ lt3WSel s ε γ nb w) (hs : s ∉ lt3H w) :
    ∀ j ∈ S, b1YTopR w (tcRow w) ε ≤ clamp01 (w (tcRow w) j) := by
  classical
  intro j hj
  obtain ⟨-, -, -, -, -, hSWQ, -⟩ := lt3W_mem hk
  have hjQ : j ∈ lt3Q s ε γ w := lt3WQ_sub s ε γ nb w (hSWQ hj)
  have hjU : j ∈ lt3Top s w ε \ lt3Ex s ε γ w :=
    (lt3QOf_spec (lt3Base s w) (lt3Top s w ε \ lt3Ex s ε γ w) (tcRow w)).1 hjQ
  have hjT := (mem_sdiff.1 hjU).1
  rw [lt3Top_light hs] at hjT
  unfold lt3TopG at hjT
  exact (mem_filter.1 hjT).2

/-- **The natural level from `c0`** (any `y`): `c0 ≥ 4/5` and `c0 ≥ y - ω'` give
`(1 - ε) Lv y β ≤ Lv c0 (1 - 483t/800) β`. -/
lemma lt3_level_natE5 {Lv c0 y β : ℝ} (hLv : 0 ≤ Lv) (hβ : 0 ≤ β) (hc45 : 4 / 5 ≤ c0)
    (hc : y - lt3ωE5 ≤ c0) :
    (1 - dnEps) * Lv * y * β ≤ Lv * c0 * (1 - 483 * ((lt3tE5 : ℚ) : ℝ) / 800) * β := by
  by_cases hy : 1 / 2 ≤ y
  · exact lt3_levelE5 hLv hβ hy hc
  · push Not at hy
    have key : (1 - dnEps) * y ≤ c0 * (1 - 483 * ((lt3tE5 : ℚ) : ℝ) / 800) := by
      rw [lt3tE5_real]; unfold dnEps
      norm_num
      nlinarith
    calc (1 - dnEps) * Lv * y * β = Lv * ((1 - dnEps) * y) * β := by ring
      _ ≤ Lv * (c0 * (1 - 483 * ((lt3tE5 : ℚ) : ℝ) / 800)) * β :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key hLv) hβ
      _ = _ := by ring

/-- **The natural level for a successful member of a light `s`, `N` large** (`t = lt3tE5`, bins `lt3nbE5`, grid
`lt3ngE5`, box `lt3ρE5`, window loss `lt3ωE5`; light statistic `≤ tσ/8000`, band `η² ≤ (t/10^6) σ a₃ Z`). -/
theorem lt3W_TCprime_natE5 :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (w : Param N) (s : State N) (γ : ℝ) (a b c : Fin N) (hab : a ≠ b)
      (hac : a ≠ c) (hbc : b ≠ c) (r0 : State N) (φH η E0 : ℝ), w ∈ openCube N → s ∉ lt3H w →
      (({a, b, c} : Finset (Fin N)), r0) ∈ lt3WSel s dnEps γ lt3nbE5 w → (lt2Sp w).card < 12 →
      lt3WSucc lt3tE5 lt3ωE5 lt3ρE5 (pkE3 hab hac hbc) {a, b, c} w →
      (∀ (t0 : State N) (u : Fin (2 ^ 3)) (i : Fin 3),
        |lt3Light (stHalf (stPriv (lt3WSel s dnEps γ lt3nbE5) lt3PB w) w) {a, b, c} (lt3H w)
            (pkFlip (pkE3 hab hac hbc) t0 u) (pkE3 hab hac hbc i) -
          lt3Light (stHalf (stPriv (lt3WSel s dnEps γ lt3nbE5) lt3PB w) w) {a, b, c} (lt3H w) t0
            (pkE3 hab hac hbc i)| ≤ φH) →
      φH ≤ ((lt3tE5 : ℚ) : ℝ) / 8000 * Pw w (tcRow w) →
      Real.exp (-((lt2x1 - 1 / 800) * N)) ≤ Pw w (tcRow w) → 0 ≤ η →
      (∀ Y ⊆ ({a, b, c} : Finset (Fin N)), ∀ t', ∀ i ∈ ({a, b, c} : Finset (Fin N)),
        |Num w {a, b, c} Y t' i - lvK 3 * Zs w| ≤ η) →
      η ^ 2 ≤ ((lt3tE5 : ℚ) : ℝ) / 10 ^ 6 * Pw w (tcRow w) * (lvK 3 * Zs w) →
      6 * η / ((lvK 3 * Zs w - η) * Real.log 2) ≤ E0 →
      (∃ te ∈ sysMaxEffStates (tpmOf (flipP s w)) {a, b, c} s s,
        ∀ θ : SysPartition N {a, b, c}, E0 ≤ sysPhiE (tpmOf (flipP s w)) {a, b, c} s θ s te) →
      (1 - dnEps) * levTrip * yTopW w dnEps * betaW w ≤ phi (flipP s w) s {a, b, c} := by
  filter_upwards [lt3W_TCprime_ev lt3tE5_pos lt3tE5_le] with N hN w s γ a b c hab hac hbc r0 φH η E0 hw hs hk
    hSp hsucc hHalf hφH hσN hη0 hlev hηs hE0 heff
  obtain ⟨c0, hc0, hcj, hphi⟩ := hN w s dnEps γ lt3nbE5 a b c hab hac hbc r0 lt3ngE5 lt3ωE5 lt3ρE5 φH η E0
    hw hk hSp lt3ngE5_pos lt3ngE5_dvd lt3ωE5_bins lt3ωE5_t lt3ρE5_pos.le lt3ρE5_t hsucc hHalf hφH hσN hη0 hlev
    hηs hE0 heff
  have hβ : 0 ≤ betaW w := betaW_nonneg w
  have ha : a ∈ ({a, b, c} : Finset (Fin N)) := mem_insert_self _ _
  have hy : yTopW w dnEps - lt3ωE5 ≤ c0 := by
    have h1 := lt3_member_TopG hk hs a ha
    have h2 := hcj a ha
    unfold yTopW; linarith
  exact (lt3_level_natE5 levTrip_pos.le hβ hc0 hy).trans hphi

/-! ### Success regions at the natural level -/

/-- **The conclusion of a successful member at the natural level** (`ε = dnEps`). -/
def LT3ConclE5 (L : ℝ) (s : State N) (w' : Param N) (S : Finset (Fin N)) : Prop :=
  w' ∈ openCube N → 1 / 2 ≤ Zs w' → L * sigN N ≤ betaW w' → bdGood w' → (lt2Sp w').card < 12 →
    (1 - dnEps) * levTrip * yTopW w' dnEps * betaW w' ≤ phi (flipP s w') s S

/-- **A success region of member `S`** for the `ε = 10⁻⁵` selection: measurable, determined by the member's private
blocks, of probability `≥ p`, and `LT3ConclE5` holds at `replE Priv(w) w η` for every `η` in it. -/
def LT3MemberOKE5 (L p : ℝ) (s : State N) (w : Param N) (S : Finset (Fin N)) : Prop :=
  ∃ U : Set (Param N), MeasurableSet U ∧ DetOnE ((lt3Base s w).biUnion fun r => lt3PB (S, r)) U ∧
    ENNReal.ofReal p ≤ cubeM N U ∧
    ∀ η ∈ U, LT3ConclE5 L s (replE (stPriv (lt3WSel s dnEps lt3γE5 lt3nbE5) lt3PB w) w η) S

lemma LT3MemberOKE5.mono {L p p' : ℝ} {s : State N} {w : Param N} {S : Finset (Fin N)}
    (h : LT3MemberOKE5 L p s w S) (hp : p' ≤ p) : LT3MemberOKE5 L p' s w S := by
  obtain ⟨U, h1, h2, h3, h4⟩ := h
  exact ⟨U, h1, h2, (ENNReal.ofReal_le_ofReal hp).trans h3, h4⟩

/-! ### The light member -/

/-- **A non-adverse member of a light `s` has a success region of probability `≥ lt3pLE5`** at the natural level
(`N` large, any band level `L ≥ lt3LcE5`). -/
theorem lt3_light_member_evE5 {L : ℝ} (hL : lt3LcE5 ≤ L) : ∀ᶠ N : ℕ in atTop,
    ∀ (s : State N) (w : Param N) (S : Finset (Fin N)),
    w ∈ openCube N → (lt2Sp w).card < 12 → (S, s) ∈ lt3WSel s dnEps lt3γE5 lt3nbE5 w →
    S ∉ lt3Adv s dnEps lt3γE5 lt3nbE5 lt3κE5 w → s ∉ lt3H w → LT3MemberOKE5 L lt3pLE5 s w S := by
  have hL0 : 0 < L := lt3LcE5_pos.trans_le hL
  have ht0 : (0 : ℝ) < ((lt3tE5 : ℚ) : ℝ) := by exact_mod_cast lt3tE5_pos
  have hLκ : 768000 * lt3κE5 ≤ ((lt3tE5 : ℚ) : ℝ) * L :=
    lt3LcE5_κ.trans (mul_le_mul_of_nonneg_left hL ht0.le)
  filter_upwards [lt3W_TCprime_natE5, bd_band (t := ((lt3tE5 : ℚ) : ℝ)) (L := L) ht0 hL0,
    bd_E0_ev lt3E0eE5_pos, bd_tc_Sp_ev hL0] with N hQ hBand hE0 hTc
  intro s w S hw hSp hk hnadv hsH
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hS⟩ := lt3WSel_three hk
  have hS' : S = {a, b, c} := hS
  subst hS'
  set A := stPriv (lt3WSel s dnEps lt3γE5 lt3nbE5) lt3PB w with hA
  set e := pkE3 hab hac hbc with he
  obtain ⟨-, hUm, hUd, hUp⟩ := lt3WSucc_prob hw hab hac hbc hk hSp (ng := lt3ngE5) lt3ngE5_pos lt3ngE5_dvd
    (t := lt3tE5) lt3tE5_pos.le lt3tE5_le (ω' := lt3ωE5) (ρ := lt3ρE5) lt3ωE5_bins lt3ρE5_pos.le lt3ρE5_le
  set Uc := {η : Param N | lt3WSucc lt3tE5 lt3ωE5 lt3ρE5 e {a, b, c} (replE A w η)} with hUc
  set Ue := lt3EBox s {a, b, c} w lt3ρeE5 with hUe
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
    have hEp := lt3EBox_prob s (S := ({a, b, c} : Finset (Fin N))) (by rw [hS3]) w lt3ρeE5_pos.le lt3ρeE5_le
    unfold lt3pLE5
    have hρ := lt3ρE5_pos
    rw [ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' hUp hEp
  · -- the conclusion
    rintro η ⟨hηc, hηe⟩ hw' hZ' hβ' hbd' hSp'
    set w' := replE A w η with hw'def
    have hk' : (({a, b, c} : Finset (Fin N)), s) ∈ lt3WSel s dnEps lt3γE5 lt3nbE5 w' := by
      rw [hw'def, hA, lt3W_replE_sel]; exact hk
    have hF' := (lt3W_mem hk').2.2.2.1
    have hAdv' : ({a, b, c} : Finset (Fin N)) ∉ lt3Adv s dnEps lt3γE5 lt3nbE5 lt3κE5 w' := by
      rw [hw'def, hA, lt3Adv_replE]; exact hnadv
    have hsH' : s ∉ lt3H w' := by
      rw [hw'def, hA, (lt3W_replE_frame hab hac hbc hk η).2.1]; exact hsH
    have htc' : tcRow w' ∈ lt2Sp w' := hTc w' hw' hZ' hβ'
    have hHalf := lt3_hHalf_of_not_adv s dnEps lt3γE5 lt3nbE5 lt3κE5_pos.le htc' hab hac hbc hF' hAdv'
    have hφH : 48 * lt3κE5 * sigN N ≤ ((lt3tE5 : ℚ) : ℝ) / 8000 * Pw w' (tcRow w') :=
      lt3_phiH_le lt3κE5_pos.le ht0 hLκ hZ' hβ'
    obtain ⟨hP', hη0, hηs, hlev⟩ := hBand w' hbd' hZ' hβ' hSp'
    obtain ⟨-, hE0'⟩ := hE0 w' hbd' hZ'
    -- the effect side
    have hbox' : w' ∈ lt3EBox s {a, b, c} w' lt3ρeE5 := by
      intro q hq
      have hqA : q ∈ A := mem_biUnion.2 ⟨_, hk, hq⟩
      have h1 : w' q.1 q.2 = η q.1 q.2 := by rw [hw'def, hA]; exact lt3W_replE_priv_mem w η hqA
      have h2 : lt3ETgt w' s q.2 = lt3ETgt w s q.2 := by
        unfold lt3ETgt; rw [hw'def, hA, lt3W_replE_row_s]
      rw [h1, h2]
      exact hηe q hq
    have heff := lt3_heff_light hw' s hS3 lt3γE5_pos.le lt3γE5_lt.le lt3ρeE5_pos.le
      (by have := lt3ρeE5_γ; have := lt3γE5_pos; linarith) lt3ρeE5_B (lt3W_own_strong hk') hbox'
    have hsucc : lt3WSucc lt3tE5 lt3ωE5 lt3ρE5 (pkE3 hab hac hbc) {a, b, c} w' := hηc
    exact hQ w' s lt3γE5 a b c hab hac hbc s (48 * lt3κE5 * sigN N) (bdEta w') lt3E0eE5 hw' hsH' hk' hSp'
      hsucc hHalf hφH hP' hη0 (hlev a b c hab hac hbc) hηs hE0' heff

/-! ### The conditional product -/

/-- **No member succeeds** (natural level, `ε = 10⁻⁵` selection): success regions on disjoint private blocks,
`P ≤ e^{-p |G|}`. -/
theorem lt3_nosucc_prodE5 {L p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : State N) (w : Param N)
    (G : Finset (Finset (Fin N))) (hG : ∀ S ∈ G, (S, s) ∈ lt3WSel s dnEps lt3γE5 lt3nbE5 w)
    (hOK : ∀ S ∈ G, LT3MemberOKE5 L p s w S) :
    cubeM N {η | ∀ S ∈ G, ¬ LT3ConclE5 L s (replE (stPriv (lt3WSel s dnEps lt3γE5 lt3nbE5) lt3PB w) w η) S} ≤
      ENNReal.ofReal (Real.exp (-(p * G.card))) := by
  classical
  have : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  set A := stPriv (lt3WSel s dnEps lt3γE5 lt3nbE5) lt3PB w with hA
  set C : Finset (Fin N) → Finset (State N × Fin N) := fun S => (lt3Base s w).biUnion fun r => lt3PB (S, r)
    with hC
  have hOK' : ∀ S : Finset (Fin N), ∃ U : Set (Param N), S ∈ G → (MeasurableSet U ∧ DetOnE (C S) U ∧
      ENNReal.ofReal p ≤ cubeM N U ∧ ∀ η ∈ U, LT3ConclE5 L s (replE A w η) S) := by
    intro S
    by_cases hS : S ∈ G
    · obtain ⟨U, hU⟩ := hOK S hS
      exact ⟨U, fun _ => hU⟩
    · exact ⟨∅, fun h => absurd h hS⟩
  choose U hU using hOK'
  have hsub : {η | ∀ S ∈ G, ¬ LT3ConclE5 L s (replE A w η) S} ⊆ ⋂ S ∈ G, (U S)ᶜ := by
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

end Census
end IIT
