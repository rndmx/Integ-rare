/-
Census, B1 forced leaf 7 (`bNat`, the natural regime) of `B1ForcedSkel`, agent "forcedD".

W7 §8.2: in the natural regime the forcing goes through Tier 3 and LT3:
* (Tier 3, W3 Thm 5.1 + Lemma G') `φ_s(U) = min_j ph_j ≤ β Fᶜ_j` for every `j`              [`NatTier3Stmt`];
* (LT3 at the tilt, W2 §8 + W8/W11) some triple has `φ_s ≥ (1-ε) levTrip y_top β`, `ε = 10⁻⁵` [`NatLT3Stmt`];
* B1 (`U` beats the triple) then forces `log₂(y_j/q_j) > (1-ε) levTrip y_top` for every `j`, so with the half-means
  regular every entry of `tc` is `≥ (1/2 - 10⁻⁶) e^{(2/5)(1-ε) y_top}`.
Together with the tilt (leaf 4) and the link (leaf 5) this puts `w` in the certified natural event `DNEv`
(`B1ForcedDNatProb`), whose probability is `≤ 236 e^{32 slT} e^{-1.0106 N}` by the kernel-checked certificate of
the 118 cells (`B1ForcedDNatCert`, W7 `w7_certNat` with quantised multipliers, min rate 1.01064).

PROVED here (sorry-free): `dn_nat_det` (the deduction `NatEv ∩ Tier3 ∩ LT3 ∩ T ∩ L ∩ halves ⊆ DNEv`) and
`leaf7_of` (leaf 7 at rate `RfF` from `NatTier3Stmt`, `NatLT3Stmt`, `LT2Stmt`, `LTBetaStmt`).
-/
import IIT.Census.B1ForcedDTilt
import IIT.Census.B1ForcedDNatProb
import IIT.Census.B1ForcedB1

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- `ε` of the natural certificate. -/
noncomputable def dnEps : ℝ := 1 / 10 ^ 5

/-- **Tier 3 in the natural regime** (W3 Theorem 5.1 with Lemma G', `univ_tier3`): off a rare event of B1 ∩ Nat,
`φ_s(U) ≤ β · Fᶜ_j` for every unit `j`. -/
def NatTier3Stmt (C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bNat N s ∩ {w | ¬ ∀ j, phi (flipP s w) s univ ≤
      betaW w * kF (lamCz (flipP s w) s (tcRow w)) j}) ≤ ENNReal.ofReal (Real.exp (-(C * N)))

/-- **LT3 at the tilt in the natural regime** (W2 §8, W8, W11 with Top'): off a rare event of B1 ∩ Nat, some
triple reaches `(1-ε) levTrip y_top β`. -/
def NatLT3Stmt (C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bNat N s ∩ {w | ∀ S : Finset (Fin N), S.card = 3 →
      phi (flipP s w) s S < (1 - dnEps) * levTrip * yTopW w dnEps * betaW w}) ≤
      ENNReal.ofReal (Real.exp (-(C * N)))

/-! ### The deduction -/

lemma dn_yTop_mem (hN : 1 ≤ N) (w : Param N) : 0 ≤ yTopW w dnEps ∧ yTopW w dnEps ≤ 1 := by
  have hk : ⌈dnEps * N⌉₊ ≤ N := by
    apply Nat.ceil_le.2
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    unfold dnEps; nlinarith
  refine ⟨(b1_YMinR_nonneg w _).trans (b1_YMinR_le_YTopR w _ (by omega) hk), ?_⟩
  exact (b1_YTopR_le_YMaxR w _ _).trans (b1_YMaxR_le_one w _)

/-- `2^{levTrip · u} = e^{(2/5) u}`. -/
lemma dn_two_rpow_levTrip (u : ℝ) : (2 : ℝ) ^ (levTrip * u) = Real.exp (2 / 5 * u) := by
  rw [Real.rpow_def_of_pos (by norm_num), levTrip_eq]
  congr 1
  have := b1_log_two_pos
  field_simp

/-- **The forced floor**: from `log₂(y/q) > (1-ε) levTrip y_top` and `|q - 1/2| ≤ δ ≤ 10⁻⁶`. -/
lemma dn_floor_of {y q δ u : ℝ} (hq : |q - 1 / 2| ≤ δ) (hδ : δ ≤ 1 / 10 ^ 6)
    (h : levTrip * u < Real.logb 2 (y / q)) (hy : 0 < y) :
    (1 / 2 - 1 / 10 ^ 6) * Real.exp (2 / 5 * u) ≤ y := by
  have hq0 : 1 / 2 - 1 / 10 ^ 6 ≤ q := by have := (abs_le.1 hq).1; linarith
  have hqp : 0 < q := by linarith
  have h2 := (Real.lt_logb_iff_rpow_lt one_lt_two (div_pos hy hqp)).1 h
  rw [dn_two_rpow_levTrip, lt_div_iff₀ hqp] at h2
  have := Real.exp_pos (2 / 5 * u)
  nlinarith

/-- **Leaf 7, deterministic part.** -/
theorem dn_nat_det (hN : 4 ≤ N) (hδ : 1 / ((N : ℝ) + 1) ≤ 1 / 10 ^ 6) {s : State N} {w : Param N}
    (hw : w ∈ bNat N s)
    (h3 : ∀ j, phi (flipP s w) s univ ≤ betaW w * kF (lamCz (flipP s w) s (tcRow w)) j)
    (hLT : ∃ S : Finset (Fin N), S.card = 3 ∧
      (1 - dnEps) * levTrip * yTopW w dnEps * betaW w ≤ phi (flipP s w) s S)
    (hhalf : w ∉ dtHalfBad N) (hT : w ∉ bTilt N s) (hL : w ∉ bLink N s) :
    w ∈ DNEv N s (slT N) := by
  obtain ⟨⟨hB, ho⟩, -⟩ := hw
  have hT' : XW w (tcRow w) ≤ x0 * N + slT N := by by_contra h; exact hT ⟨⟨hB, ho⟩, h⟩
  have hL' : ∑ k, -Real.log (xE w s k) ≤ XW w (tcRow w) + slT N := by by_contra h; exact hL ⟨⟨hB, ho⟩, h⟩
  obtain ⟨S, hS3, hSge⟩ := hLT
  have hβ := betaW_pos ho
  set u := (1 - dnEps) * yTopW w dnEps with hu
  have hz : flipP s w ∈ openCube N := flipP_mem_openCube ho
  have hzw : flipP s (flipP s w) = w := flipP_invol s w
  -- every full cut beats the triple level
  have hF : ∀ j, levTrip * u < kF (lamCz (flipP s w) s (tcRow w)) j := by
    intro j
    have hne : S.Nonempty := by rw [← card_pos]; omega
    have hlt := dt_B1_lt hB hne (dt_card_ne_univ (le_of_eq hS3) (by omega))
    have h := lt_of_le_of_lt hSge (lt_of_lt_of_le hlt (h3 j))
    have : levTrip * u * betaW w < kF (lamCz (flipP s w) s (tcRow w)) j * betaW w := by
      rw [hu]; linarith
    exact lt_of_mul_lt_mul_right this hβ.le
  -- the floor on the row `tc`
  have hfloor : ∀ j, (1 / 2 - 1 / 10 ^ 6) * Real.exp (2 / 5 * u) ≤ clamp01 (w (tcRow w) j) := by
    intro j
    obtain ⟨hm, -, -, -, -⟩ := lamCz_means hz s (tcRow w)
    have hk := hF j
    unfold kF at hk
    rw [hm, hzw] at hk
    have hsd : (univ \ univ.erase j : Finset (Fin N)) = {j} := by ext i; simp
    rw [hsd, cmean_single_eq] at hk
    have hq : |faColMean w (tcRow w) j - 1 / 2| ≤ 1 / ((N : ℝ) + 1) := by
      by_contra hc; exact hhalf ⟨tcRow w, j, not_le.1 hc⟩
    have hy : 0 < clamp01 (w (tcRow w) j) := by
      rw [b1_clamp01_of_mem_Ioo (ho _ j)]; exact (ho _ j).1
    exact dn_floor_of (hq.trans hδ) le_rfl hk hy |>.trans' (by
      have : 1 / ((N : ℝ) + 1) ≤ 1 / 10 ^ 6 := hδ
      exact le_rfl)
  -- the cell
  obtain ⟨hy0, hy1⟩ := dn_yTop_mem (by omega) w
  obtain ⟨C, hC, htlo, hthi⟩ := dnChain_cover dnCells 0 dnCells_chain (yTopW w dnEps) (by simpa using hy0) hy1
  obtain ⟨h1, h2, h3', h4, h5, h6, -⟩ := dnCellOK_spec ((List.all_eq_true.1 dnCells_ok) C hC)
  -- floor in the cell
  have hv : ∀ j, ((C.v : ℝ)) ^ 4 ≤ clamp01 (w (tcRow w) j) := by
    intro j
    refine le_trans ?_ (hfloor j)
    have h5' : ((C.v : ℝ)) ^ 4 ≤ (1 / 2 - 1 / 10 ^ 6) * ((dnExpLo (2 / 5 * (1 - 1 / 10 ^ 5) * C.tlo) 12 : ℚ) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).2 h5; push_cast at this ⊢; exact this
    refine h5'.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    refine (dn_expLo_le (by have : (0 : ℚ) ≤ 1 - 1 / 10 ^ 5 := by norm_num
                            positivity) 12).trans (Real.exp_le_exp.2 ?_)
    push_cast
    have hε : dnEps = 1 / 10 ^ 5 := rfl
    rw [hu, hε]
    rw [hε] at htlo
    have : (0 : ℝ) ≤ 2 / 5 * (1 - 1 / 10 ^ 5) := by norm_num
    nlinarith
  -- count in the cell
  have hcount : ((univ.filter fun j => ((C.w : ℝ)) ^ 4 < clamp01 (w (tcRow w) j)).card : ℝ) ≤ (N : ℝ) / 10 ^ 5 := by
    have hk1 : 1 ≤ ⌈dnEps * N⌉₊ := by
      apply Nat.one_le_iff_ne_zero.2
      intro h0
      rw [Nat.ceil_eq_zero] at h0
      unfold dnEps at h0
      have : (4 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hlt := b1Kth_lt_count (f := fun i => clamp01 (w (tcRow w) i)) hk1
    have hsub : (univ.filter fun j => ((C.w : ℝ)) ^ 4 < clamp01 (w (tcRow w) j)) ⊆
        univ.filter fun j => b1Kth (fun i => clamp01 (w (tcRow w) i)) ⌈dnEps * N⌉₊ < clamp01 (w (tcRow w) j) := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      have h6' : ((C.thi : ℚ) : ℝ) ≤ ((C.w : ℝ)) ^ 4 := by
        have := (Rat.cast_le (K := ℝ)).2 h6; push_cast at this; exact this
      have : yTopW w dnEps = b1Kth (fun i => clamp01 (w (tcRow w) i)) ⌈dnEps * N⌉₊ := rfl
      linarith
    have hc := lt_of_le_of_lt (card_le_card hsub) hlt
    have := (Nat.lt_ceil).1 hc
    unfold dnEps at this
    linarith
  -- the certified event
  refine ⟨C, hC, tcRow w, ?_⟩
  by_cases hr : tcRow w = s
  · left
    refine ⟨hr, ?_⟩
    rw [← hr]
    exact ⟨hv, hcount, hT'⟩
  · right
    exact ⟨hr, hv, hcount, hT', hL'⟩

/-! ### Leaf 7 -/

lemma dn_delta_small : ∀ᶠ N : ℕ in atTop, 1 / ((N : ℝ) + 1) ≤ 1 / 10 ^ 6 := by
  filter_upwards [eventually_ge_atTop (10 ^ 6)] with N hN
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (10 ^ 6 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

lemma dn_cert_absorb : ∀ᶠ N : ℕ in atTop,
    236 * (Real.exp (-((dnR : ℝ) * N)) * Real.exp (32 * slT N)) ≤ Real.exp (-(10105 / 10000 + 1 / 20000 : ℝ) * N) := by
  have hab := poly_absorb 236 0 (δ := (dnR : ℝ) - (10105 / 10000 + 1 / 20000)) (by unfold dnR; norm_num)
  filter_upwards [hab, eventually_ge_atTop 1] with N hab hN1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hsl : 32 * slT N ≤ 4000 + 1400 * Real.log N := by unfold slT; nlinarith
  simp only [pow_zero, mul_one] at hab
  have e : Real.exp (-(10105 / 10000 + 1 / 20000 : ℝ) * N) =
      Real.exp (((dnR : ℝ) - (10105 / 10000 + 1 / 20000)) * N) * Real.exp (-((dnR : ℝ) * N)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  have h1 : 236 * Real.exp (32 * slT N) ≤ Real.exp (((dnR : ℝ) - (10105 / 10000 + 1 / 20000)) * N) :=
    le_trans (by gcongr) hab
  have hx := Real.exp_pos (-((dnR : ℝ) * N))
  nlinarith

/-- **Leaf 7 (`bNat`)**, from Tier 3 + LT3 in the natural regime (and the leaf-4/5 statements LT2, LTβ). -/
theorem leaf7_of (h3 : NatTier3Stmt RfD) (hT3 : NatLT3Stmt RfD) (hLT2 : LT2Stmt 1 RfD)
    (hLTb : LTBetaStmt (1 / 4) RfD) : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 7) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  have habs := dt_absorb 9
  have hhalfr : ∀ᶠ N : ℕ in atTop, Real.exp (-(10105 / 10000 + 1 / 20000 : ℝ) * N) +
      9 * Real.exp (-(RfD * N)) ≤ Real.exp (-(RfF * N)) := by
    have ht : Tendsto (fun N : ℕ => Real.exp (-((RfD - RfF) * N))) atTop (𝓝 0) := by
      have hpos : 0 < RfD - RfF := by unfold RfD RfF; norm_num
      apply Real.tendsto_exp_atBot.comp
      apply tendsto_neg_atTop_atBot.comp
      exact (tendsto_natCast_atTop_atTop).const_mul_atTop hpos
    have ht2 : Tendsto (fun N : ℕ => Real.exp (-((1 / 20000 : ℝ) * N))) atTop (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      apply tendsto_neg_atTop_atBot.comp
      exact (tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
    filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 18)),
      ht2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with N h1 h2
    have e1 : Real.exp (-(10105 / 10000 + 1 / 20000 : ℝ) * N) =
        Real.exp (-((1 / 20000 : ℝ) * N)) * Real.exp (-(RfF * N)) := by
      rw [← Real.exp_add]; unfold RfF; congr 1; ring
    have e2 : Real.exp (-(RfD * N)) = Real.exp (-((RfD - RfF) * N)) * Real.exp (-(RfF * N)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e1, e2]
    have hx := Real.exp_pos (-(RfF * N))
    nlinarith
  filter_upwards [h3, hT3, leaf4_strong hLT2, leaf5_strong hLTb, dt_half_all, dn_cert_absorb,
    dn_delta_small, hhalfr, eventually_ge_atTop 4] with N h3 hT3 h4 h5 hH hA hδ hfin hN s
  set E1 := bNat N s ∩ {w | ¬ ∀ j, phi (flipP s w) s univ ≤ betaW w * kF (lamCz (flipP s w) s (tcRow w)) j}
  set E2 := bNat N s ∩ {w | ∀ S : Finset (Fin N), S.card = 3 →
      phi (flipP s w) s S < (1 - dnEps) * levTrip * yTopW w dnEps * betaW w}
  have hsub : forcedBad N s 7 ⊆ E1 ∪ E2 ∪ dtHalfBad N ∪ bTilt N s ∪ bLink N s ∪ DNEv N s (slT N) := by
    intro w hw
    have hw' : w ∈ bNat N s := hw
    by_cases c1 : w ∈ E1
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl c1))))
    by_cases c2 : w ∈ E2
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr c2))))
    by_cases c3 : w ∈ dtHalfBad N
    · exact Or.inl (Or.inl (Or.inl (Or.inr c3)))
    by_cases c4 : w ∈ bTilt N s
    · exact Or.inl (Or.inl (Or.inr c4))
    by_cases c5 : w ∈ bLink N s
    · exact Or.inl (Or.inr c5)
    refine Or.inr (dn_nat_det hN hδ hw' ?_ ?_ c3 c4 c5)
    · by_contra h; exact c1 ⟨hw', h⟩
    · by_contra h
      push Not at h
      exact c2 ⟨hw', h⟩
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have he2 : Real.exp (-(2 * N)) ≤ Real.exp (-(RfD * N)) := Real.exp_le_exp.2 (by unfold RfD; nlinarith)
  have hslT : 0 ≤ slT N := by
    unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    linarith
  calc cubeM N (forcedBad N s 7)
      ≤ cubeM N E1 + cubeM N E2 + cubeM N (dtHalfBad N) + cubeM N (bTilt N s) + cubeM N (bLink N s) +
          cubeM N (DNEv N s (slT N)) := by
        refine (measure_mono hsub).trans ?_
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(RfD * N))) + ENNReal.ofReal (Real.exp (-(RfD * N))) +
          ENNReal.ofReal (Real.exp (-(RfD * N))) + ENNReal.ofReal (3 * Real.exp (-(RfD * N))) +
          ENNReal.ofReal (3 * Real.exp (-(RfD * N))) +
          ENNReal.ofReal (Real.exp (-(10105 / 10000 + 1 / 20000 : ℝ) * N)) := by
        gcongr
        · exact h3 s
        · exact hT3 s
        · exact hH.trans (ENNReal.ofReal_le_ofReal he2)
        · exact h4 s
        · exact h5 s
        · refine (dnNatEv_le (by omega) s hslT).trans (ENNReal.ofReal_le_ofReal ?_)
          exact hA
    _ = ENNReal.ofReal (9 * Real.exp (-(RfD * N)) + Real.exp (-(10105 / 10000 + 1 / 20000 : ℝ) * N)) := by
        have h0 := Real.exp_pos (-(RfD * N))
        rw [← ENNReal.ofReal_add h0.le h0.le, ← ENNReal.ofReal_add (by positivity) h0.le,
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
        congr 1; ring
    _ ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := ENNReal.ofReal_le_ofReal (by linarith)

end Census
end IIT
