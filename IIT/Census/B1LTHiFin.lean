/-
Census, B1 LTBetaHi, final assembly: **`LTBetaHiStmt (1/4) (104/100)` with no open hypothesis**.

The heavy hypothesis of B1LTHiT7c is discharged member by member: `s ∉ lt3H` by `lt3_light_member_ev`, `s = tc` by
`lt3_tc_member_ev`, and `s ∈ Sp \ {tc}` by `lt3_u_member_ev`. The last one needs `|H \ {s}| ≤ 2`, i.e. at most two
other special rows; the target therefore also asks `s ∈ Sp → |Sp \ {s}| < 3` (`lt3T7Tm2`), and the excluded event
costs `e^{-1.07N}` (`spr_ev`).

* `lt3T7Tm2`, `lt3T7Y2` (measurable), **`lt3_T7_sect2`** (a nonempty section is `≤ e^{-2N}`),
  `lt3_rate_num2` (`... + e^{-1.07N} ≤ e^{-1.047N}`), **`lt3HiFl_final`** (`LT3HiFlStmt L (1047/1000)`, `L ≥ lt3Lc`),
  **`lt3Hi_final`** and **`ltBetaHi_final`**: `LTBetaHiStmt (1/4) (104/100)`.
-/
import IIT.Census.B1LTHiUM
import IIT.Census.B1LTHiSpRed

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-- The target, with at most two other special rows when `s` is special. -/
def lt3T7Tm2 (L : ℝ) (s : State N) : Set (Param N) :=
  {w | w ∈ lt3T7Tm L s ∧ (s ∈ lt2Sp w → ((lt2Sp w).erase s).card < 3)}

/-- The conditioned event. -/
def lt3T7Y2 (L : ℝ) (s : State N) : Set (Param N) :=
  lt3T7Tm2 L s ∩ (toMeasurable (cubeM N) {w | ¬ lt3T7Good s w})ᶜ

lemma lt3T7Tm2_mset (L : ℝ) (s : State N) : MeasurableSet (lt3T7Tm2 L s) := by
  classical
  have e : lt3T7Tm2 L s = lt3T7Tm L s ∩ {w | s ∈ lt2Sp w → ((lt2Sp w).erase s).card < 3} := rfl
  rw [e]
  refine (lt3T7Tm_mset L s).inter ?_
  have h := fibM_comp (f := fun w : Param N => (lt2Sp w, tcRow w)) fibM_SpTc
    (fun d => decide (s ∈ d.1 → (d.1.erase s).card < 3)) true
  convert h using 1
  ext w
  simp only [Set.mem_setOf_eq, decide_eq_true_eq]

lemma lt3T7Y2_mset (L : ℝ) (s : State N) : MeasurableSet (lt3T7Y2 L s) :=
  (lt3T7Tm2_mset L s).inter (measurableSet_toMeasurable _ _).compl

lemma lt3T7Y2_good {L : ℝ} {s : State N} {w : Param N} (h : w ∈ lt3T7Y2 L s) : lt3T7Good s w := by
  by_contra hc
  exact h.2 (subset_toMeasurable _ _ hc)

/-- `|H \ {s}| ≤ 2` from `|Sp \ {s}| < 3` and `tc ∈ Sp`. -/
lemma lt3H_erase_card {w : Param N} {s : State N} (htc : tcRow w ∈ lt2Sp w) (h : ((lt2Sp w).erase s).card < 3) :
    ((lt3H w).erase s).card ≤ 2 := by
  have e : lt3H w = lt2Sp w := insert_eq_of_mem htc
  rw [e]; omega

/-- **A nonempty section of the conditioned event is `≤ e^{-2N}`** (`N` large, uniformly in `s`), with every heavy
member discharged. -/
theorem lt3_T7_sect2 {L : ℝ} (hL : lt3Lc ≤ L) : ∀ᶠ N : ℕ in atTop,
    ∀ (s : State N) (w0 : Param N), w0 ∈ lt3T7Y2 L s →
    cubeM N {η | replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w0) w0 η ∈ lt3T7Y2 L s} ≤
      ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
  set p0 := min (min lt3pT lt3pL) 1 with hp0def
  have hp0 : 0 < p0 := lt_min (lt_min lt3pT_pos lt3pL_pos) one_pos
  have hp01 : p0 ≤ 1 := min_le_right _ _
  have hp0T : p0 ≤ lt3pT := (min_le_left _ _).trans (min_le_left _ _)
  have hp0L : p0 ≤ lt3pL := (min_le_left _ _).trans (min_le_right _ _)
  have hL0 : 0 < L := lt3Lc_pos.trans_le hL
  filter_upwards [lt3_tc_member_ev hL, lt3_u_member_ev hL, lt3_light_member_ev hL, lt3WSel_of_floor_ev hL0,
    bd_tc_Sp_ev hL0, eventually_ge_atTop (10 ^ 8 * lt3Cn), eventually_ge_atTop (7 * (2300000 * lt3Cn)),
    lt3_prod_num hp0] with N hTcN hUN hLN hSelF hTcSp hN8 hN7 hnum
  intro s w0 hw0
  classical
  have hgood := lt3T7Y2_good hw0
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
  have hOK : ∀ S ∈ G, LT3MemberOK L p0 s w0 S := by
    intro S hS
    have hnS := (mem_sdiff.1 hS).2
    by_cases hsH : s ∈ lt3H w0
    · by_cases hs : s = tcRow w0
      · exact (hTcN s w0 S hcube hSp (hGk S hS) hnS hs).mono hp0T
      · have hsSp : s ∈ lt2Sp w0 := (mem_insert.1 hsH).resolve_left hs
        have hH2 := lt3H_erase_card (hTcSp w0 hcube hZ hβ) (hspr hsSp)
        exact (hUN s w0 S hcube hSp (hGk S hS) hnS hsH hs hH2).mono hp0T
    · exact (hLN s w0 S hcube hSp (hGk S hS) hnS hsH).mono hp0L
  have hsub : {η | replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w0) w0 η ∈ lt3T7Y2 L s} ⊆
      {η | ∀ S ∈ G, ¬ LT3Concl L s (replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w0) w0 η) S} := by
    intro η hη S hS hconc
    have hg' := lt3T7Y2_good hη
    obtain ⟨⟨⟨hc', hβ', hZ', -, hφ'⟩, -⟩, -⟩ := hη
    obtain ⟨a, b, c, hab, hac, hbc, hS3⟩ := lt3WSel_three (hGk S hS)
    have hS3' : S = {a, b, c} := hS3
    have hcard : S.card = 3 := by
      rw [hS3', card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]
    have h1 := hconc hc' hZ' hβ' hg'.2.1 hg'.1.1.2.2.2.1
    have h2 := hφ' S (by omega) (by omega)
    linarith
  refine (measure_mono hsub).trans ((lt3_nosucc_prod hp0.le hp01 s w0 G hGk hOK).trans ?_)
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have := hnum m G.card hm hGc
  linarith

/-- `e^{-2N} + (2e^{-1.05N} + e^{-1.2N} + e^{-2N}) + 2e^{-1.1N} + e^{-1.07N} ≤ e^{-1.047N}` for `N` large. -/
lemma lt3_rate_num2 : ∀ᶠ N : ℕ in atTop, Real.exp (-(2 * (N : ℝ))) +
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
theorem lt3HiFl_final {L : ℝ} (hL : lt3Lc ≤ L) : LT3HiFlStmt L (1047 / 1000) := by
  unfold LT3HiFlStmt
  refine ev_forall_state (P := fun N s => cubeM N (B1w N s ∩ openCube N ∩ {w | L * sigN N ≤ betaW w ∧
      1 / 2 ≤ Zs w ∧ 4 / 5 ≤ b1YTopR w (tcRow w) (1 / 21) ∧
      ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 1 / 4 * betaW w}) ≤
      ENNReal.ofReal (Real.exp (-(1047 / 1000 * (N : ℝ))))) fun sq => ?_
  have hD1 : 1 ≤ 10 ^ 14 * lt3Cn * lt3Cn := Nat.succ_le_of_lt (by have := lt3Cn_pos; positivity)
  filter_upwards [lt3_T7_sect2 hL, lt3W_not_good_ev2 sq (1 / 21) 8319999 hD1, bd_not_good_ev,
    lt3_adv_ev lt3D0_pos lt3κ_ge lt3κ_sq, lt3_rate_num2, spgu_ev (lt3Lc_pos.trans_le hL), spr_ev]
    with N hsect hWG hbd hadv hrate hgu hspr
  set s := sq N with hs
  have : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  -- the conditioned event
  have hY : cubeM N (lt3T7Y2 L s) ≤ ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
    refine lt3W_cond_priv s (1 / 21) lt3γ 8319999 (lt3T7Y2_mset L s) fun A w hA => ?_
    by_cases hne : ∃ η0, replE A w η0 ∈ lt3T7Y2 L s
    · obtain ⟨η0, hη0⟩ := hne
      have hP0 : stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB (replE A w η0) = A :=
        ((lt3WPriv_detOn (s := s) (ε := 1 / 21) (γ := lt3γ) (n := 8319999) A).replE_out w η0).2 hA
      have e : {η | replE A w η ∈ lt3T7Y2 L s} =
          {η | replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB (replE A w η0)) (replE A w η0) η ∈
            lt3T7Y2 L s} := by
        ext η
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hP0, replE_replE]
      rw [e]
      exact hsect s _ hη0
    · push Not at hne
      have e : {η | replE A w η ∈ lt3T7Y2 L s} = ∅ := by
        ext η
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact hne η
      rw [e, measure_empty]
      exact zero_le
  -- the bad event
  have hbad : {w | ¬ lt3T7Good s w} ⊆
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
  have hbadM : cubeM N {w | ¬ lt3T7Good s w} ≤ ENNReal.ofReal (2 * Real.exp (-((105 / 100 : ℝ) * N)) +
      Real.exp (-(6 / 5 * (N : ℝ))) + Real.exp (-(2 * (N : ℝ)))) := by
    refine (measure_mono hbad).trans ((measure_union_le _ _).trans ?_)
    refine (add_le_add ((measure_union_le _ _).trans (add_le_add hWG hbd)) (hadv s (1 / 21) lt3γ 8319999)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  -- the target
  have hT : B1w N s ∩ openCube N ∩ {w | L * sigN N ≤ betaW w ∧ 1 / 2 ≤ Zs w ∧
      4 / 5 ≤ b1YTopR w (tcRow w) (1 / 21) ∧
      ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 1 / 4 * betaW w} ⊆
      ((lt3T7Y2 L s ∪ toMeasurable (cubeM N) {w | ¬ lt3T7Good s w}) ∪
        {w | w ∈ B1w N s ∧ w ∈ openCube N ∧ L * sigN N ≤ betaW w ∧ 1 / 2 ≤ Zs w ∧ lt3SpC s w ∧
          (lt3GoodU s w).card < ⌈(1 / 21 : ℝ) * N⌉₊}) ∪
        {w | s ∈ lt2Sp w ∧ 3 ≤ ((lt2Sp w).erase s).card} := by
    rintro w ⟨⟨hB, hc⟩, hβ, hZ, -, hall⟩
    by_cases hsp : s ∈ lt2Sp w → ((lt2Sp w).erase s).card < 3
    · refine Or.inl ?_
      by_cases hgw : lt3SpC s w → ⌈(1 / 21 : ℝ) * N⌉₊ ≤ (lt3GoodU s w).card
      · by_cases h : w ∈ toMeasurable (cubeM N) {w | ¬ lt3T7Good s w}
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

/-- **The LT3 band (`LT3HiStmt`)**, at any `L ≥ lt3Lc`, rate `1.046`. -/
theorem lt3Hi_final {L : ℝ} (hL : lt3Lc ≤ L) : LT3HiStmt L (1046 / 1000) :=
  lt3Hi_of_floor (lt3Lc_pos.trans_le hL) (by norm_num) (by norm_num) (lt3HiFl_final hL)

/-- **LTBetaHi, proved**: `LTBetaHiStmt (1/4) (104/100)`. -/
theorem ltBetaHi_final : LTBetaHiStmt (1 / 4) (104 / 100) :=
  ltBetaHi_of_LT3Fl lt3Lc_one (by norm_num) (lt3HiFl_final (L := lt3Lc) le_rfl)

end Census
end IIT
