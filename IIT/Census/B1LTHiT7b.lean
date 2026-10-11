/-
Census, B1 LTBetaHi, T7 part B: **the constants, the member success region, and the light member**.

* Constants of the T7 instance: bins `n_b = 8319999` (as in `lt3W_TCprime_quarter`), the window constant
  `lt3Cn = ((n_b+1)²)^14` (`lt3W_good_F`), `lt3D0 = 4600000 · lt3Cn` (`lt3_adv_ev`), the adverse level
  `lt3κ = lt2κ + 100 · lt3D0`, the band level `lt3Lc = 61440000 · lt3κ` (`768000 κ = L/80`, `lt3_phiH_le`), the effect
  box radius `lt3ρe = γ₀/100`, the effect floor `lt3E0e`, the light success probability
  `lt3pL = (1/4160000)^234 · lt3ρe^24`.
* `LT3Concl L s w' S`: at a resampled parameter `w'` satisfying the good conditions (`openCube`, `Zs ≥ 1/2`,
  `Lσ_N ≤ β`, the band event `bdGood`, `|Sp| < 12`), member `S` reaches `β/4`.
* `LT3MemberOK L p s w S`: a **success region** for member `S` given the conditioning point `w`: a measurable set
  `U` of resampled private entries, determined by `S`'s private blocks `⋃_{r ∈ Base} lt3PB (S, r)`, of probability
  `≥ p`, on which `LT3Concl` holds at `replE Priv(w) w η`.
* **`lt3_light_member_ev`** (light `s`, `s ∉ lt3H w`): every non-adverse member has a success region of probability
  `≥ lt3pL`: the cause box of `lt3WSucc_prob` (`ρ^234`) times the effect box of `s`'s block (`lt3ρe^24`), which are
  independent (disjoint private blocks). On it: Lemma TC' (`lt3W_TCprime_quarter`) with the band (`bd_band`), the
  light statistic of a non-adverse member (`lt3_hHalf_of_not_adv`, `lt3_phiH_le`), `bd_E0_ev`, and the effect side
  `lt3_heff_light`.
-/
import IIT.Census.B1LTHiT7a
import IIT.Census.B1LTHiLight4

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-! ### The constants -/

/-- The window constant `((n_b + 1)²)^{14}` at `n_b = 8319999`. -/
def lt3Cn : ℕ := ((8319999 + 1) * (8319999 + 1)) ^ 14

/-- The adverse-count scale `D0 = 4600000 C`. -/
def lt3D0 : ℕ := 4600000 * lt3Cn

/-- The adverse level `κ`. -/
noncomputable def lt3κ : ℝ := lt2κ + 100 * (lt3D0 : ℝ)

/-- The band level `L = 61440000 κ` (so that `768000 κ = L/80`). -/
noncomputable def lt3Lc : ℝ := 61440000 * lt3κ

/-- The effect box radius. -/
noncomputable def lt3ρe : ℝ := lt3γ / 100

/-- The effect floor of Lemma EF at `γ₀`, `lt3ρe`. -/
noncomputable def lt3E0e : ℝ := (1 / 2 + lt3γ) ^ 3 * Real.logb 2 (1 / (1 - (1 / 2 + lt3γ - lt3ρe) / 2))

/-- The success probability of a light member. -/
noncomputable def lt3pL : ℝ := (1 / 4160000 : ℝ) ^ 234 * lt3ρe ^ 24

lemma lt3Cn_pos : 0 < lt3Cn := by unfold lt3Cn; positivity

lemma lt3Cn_ge : ((8319999 + 1) * (8319999 + 1)) ^ 14 ≤ lt3Cn := le_rfl

lemma lt3D0_pos : 1 ≤ lt3D0 := by unfold lt3D0; have := lt3Cn_pos; omega

lemma lt3κ_ge : lt2κ ≤ lt3κ := by
  unfold lt3κ; have : (0 : ℝ) ≤ lt3D0 := Nat.cast_nonneg _; linarith

lemma lt3κ_pos : 0 < lt3κ := lt_of_lt_of_le (by unfold lt2κ; norm_num) lt3κ_ge

lemma lt3Lc_pos : 0 < lt3Lc := by unfold lt3Lc; have := lt3κ_pos; positivity

lemma lt3Lc_one : 1 ≤ lt3Lc := by
  unfold lt3Lc; have := lt3κ_ge; unfold lt2κ at this; linarith

lemma lt3Lc_κ : 768000 * lt3κ ≤ (1 / 80 : ℝ) * lt3Lc := by unfold lt3Lc; linarith

/-- The adverse-count condition of `lt3_adv_ev` at `D0 = lt3D0`, `κ = lt3κ`. -/
lemma lt3κ_sq : 4 * (3 * (96 * (lt3D0 : ℝ)) + Real.log (2 * Real.exp 1 * (96 * lt3D0))) ≤ lt3κ ^ 2 := by
  have hD : (1 : ℝ) ≤ lt3D0 := by exact_mod_cast lt3D0_pos
  have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hlog : Real.log (2 * Real.exp 1 * (96 * lt3D0)) ≤ 2 * Real.exp 1 * (96 * lt3D0) :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hκ : 100 * (lt3D0 : ℝ) ≤ lt3κ := by unfold lt3κ lt2κ; linarith
  have hκ2 : (100 * (lt3D0 : ℝ)) ^ 2 ≤ lt3κ ^ 2 := pow_le_pow_left₀ (by positivity) hκ 2
  have h1 : 2 * Real.exp 1 * (96 * (lt3D0 : ℝ)) ≤ 576 * lt3D0 := by nlinarith
  nlinarith

lemma lt3ρe_pos : 0 < lt3ρe := by unfold lt3ρe; have := lt3γ_pos; positivity

lemma lt3ρe_le : lt3ρe ≤ 1 := by unfold lt3ρe; have := lt3γ_lt; linarith

lemma lt3ρe_B : 7 * lt3ρe ≤ 3 * Real.log 2 * (2 * lt3γ * (1 / 2 + lt3γ) ^ 2) := by
  have hγ := lt3γ_pos
  have hl := Real.log_two_gt_d9
  have h1 : (1 / 4 : ℝ) ≤ (1 / 2 + lt3γ) ^ 2 := by nlinarith
  have h2 : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith
  have h3 : 3 * (69 / 100) * (2 * lt3γ * (1 / 4)) ≤ 3 * Real.log 2 * (2 * lt3γ * (1 / 2 + lt3γ) ^ 2) := by
    apply mul_le_mul (by linarith) (by nlinarith) (by positivity) (by positivity)
  unfold lt3ρe
  nlinarith

lemma lt3E0e_pos : 0 < lt3E0e := by
  have hγ := lt3γ_pos
  have hγ1 := lt3γ_lt
  have hρ := lt3ρe_pos
  have hρ1 : lt3ρe ≤ lt3γ := by unfold lt3ρe; linarith
  unfold lt3E0e
  refine mul_pos (by positivity) (Real.logb_pos (by norm_num) ?_)
  rw [lt_div_iff₀ (by linarith)]
  linarith

lemma lt3pL_pos : 0 < lt3pL := by unfold lt3pL; have := lt3ρe_pos; positivity

lemma lt3pL_le : lt3pL ≤ 1 := by
  unfold lt3pL
  have h1 : (1 / 4160000 : ℝ) ^ 234 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : lt3ρe ^ 24 ≤ 1 := pow_le_one₀ lt3ρe_pos.le lt3ρe_le
  have h3 : 0 ≤ lt3ρe ^ 24 := by have := lt3ρe_pos; positivity
  nlinarith

/-! ### Success regions -/

/-- **The conclusion of a successful member** at a resampled parameter `w'` (good conditions ⇒ `φ_s(S) ≥ β/4`). -/
def LT3Concl (L : ℝ) (s : State N) (w' : Param N) (S : Finset (Fin N)) : Prop :=
  w' ∈ openCube N → 1 / 2 ≤ Zs w' → L * sigN N ≤ betaW w' → bdGood w' → (lt2Sp w').card < 12 →
    1 / 4 * betaW w' ≤ phi (flipP s w') s S

/-- **A success region of member `S`** given the conditioning point `w`: measurable, determined by the member's
private blocks, of probability `≥ p`, and `LT3Concl` holds at `replE Priv(w) w η` for every `η` in it. -/
def LT3MemberOK (L p : ℝ) (s : State N) (w : Param N) (S : Finset (Fin N)) : Prop :=
  ∃ U : Set (Param N), MeasurableSet U ∧ DetOnE ((lt3Base s w).biUnion fun r => lt3PB (S, r)) U ∧
    ENNReal.ofReal p ≤ cubeM N U ∧
    ∀ η ∈ U, LT3Concl L s (replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w) w η) S

lemma LT3MemberOK.mono {L p p' : ℝ} {s : State N} {w : Param N} {S : Finset (Fin N)}
    (h : LT3MemberOK L p s w S) (hp : p' ≤ p) : LT3MemberOK L p' s w S := by
  obtain ⟨U, h1, h2, h3, h4⟩ := h
  exact ⟨U, h1, h2, (ENNReal.ofReal_le_ofReal hp).trans h3, h4⟩

/-- Units of a member avoid the weak band of `s` (they are in `Q ⊆ Top \ Ex`). -/
lemma lt3W_own_strong {s : State N} {ε γ : ℝ} {nb : ℕ} {w : Param N} {S : Finset (Fin N)} {r0 : State N}
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
theorem lt3_light_member_ev {L : ℝ} (hL : lt3Lc ≤ L) : ∀ᶠ N : ℕ in atTop,
    ∀ (s : State N) (w : Param N) (S : Finset (Fin N)),
    w ∈ openCube N → (lt2Sp w).card < 12 → (S, s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w →
    S ∉ lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w → s ∉ lt3H w → LT3MemberOK L lt3pL s w S := by
  have hL0 : 0 < L := lt3Lc_pos.trans_le hL
  have hLκ : 768000 * lt3κ ≤ (1 / 80 : ℝ) * L := by have := lt3Lc_κ; linarith
  filter_upwards [lt3W_TCprime_quarter, bd_band (t := 1 / 80) (L := L) (by norm_num) hL0,
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
      (by have := lt3ρe_le; have := lt3γ_pos; unfold lt3ρe; linarith) lt3ρe_B (lt3W_own_strong hk') hbox'
    have hsucc : lt3WSucc (1 / 80) (1 / 320000) (1 / 4160000) (pkE3 hab hac hbc) {a, b, c} w' := hηc
    exact hQ w' s (1 / 21) lt3γ a b c hab hac hbc s (48 * lt3κ * sigN N) (bdEta w') lt3E0e hw' hk' hSp'
      hsucc hHalf hφH hP' hη0 (hlev a b c hab hac hbc) hηs' hE0' heff

end Census
end IIT
