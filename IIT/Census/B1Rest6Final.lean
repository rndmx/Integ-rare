/-
Census, B1: **`NatTier3Rest6Stmt (1039/1000)` proved** (W12 §1).

On `bNat` (B1, open cube, natural singletons) the residual Tier 3 event `Tier3Rest6` fails only on:
* the concentration failures `¬concC(tc)`, `¬concE` (superexponential);
* the tilt `bTilt` (LT2), the link `bLink` (LTβ), the floor `bFloor` (half-means, rate 2), each at rate `> 1.039`;
* the cluster events `clrBadC`, `clrBadE` (count, spread; superexponential);
* the small-cut events `scBadCEv`, `sceBadEv` for `2 ≤ |K| < D` (rate 1.1).
Singletons come from `NatEv` (`7 D0U ≥ 7 D`).
-/
import IIT.Census.B1SmallCutEff
import IIT.Census.B1ForcedFinal2
import IIT.Census.B1ForcedA

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- The floor leaf at rate `2` (half-means through `dt_half_all`). -/
theorem floor_bound2 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bFloor N s) ≤ ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
  filter_upwards [dt_half_all, eventually_ge_atTop 2] with N h hN s
  have hsub : bFloor N s ⊆ faTie N ∪ dtHalfBad N := by
    intro w hw
    obtain ⟨⟨hB, ho⟩, hn⟩ := hw
    by_cases ht : w ∈ faTie N
    · exact Or.inl ht
    right
    simp only [Set.mem_setOf_eq, not_forall, not_le] at hn
    obtain ⟨j, hj⟩ := hn
    have hc := fa_cause_pos hN hB ho ht j
    refine ⟨tcRow w, j, ?_⟩
    have hδ0 : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    rw [abs_sub_comm, abs_of_pos (by unfold deltaU at hj; linarith)]
    unfold deltaU at hj
    linarith
  calc cubeM N (bFloor N s) ≤ cubeM N (faTie N) + cubeM N (dtHalfBad N) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ 0 + ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by rw [fa_tie_null]; gcongr
    _ = _ := zero_add _

/-- The link leaf at any rate `C ≤ 1.4` (as `leaf5_strong`). -/
theorem link_bound {C : ℝ} (hC : C ≤ 14 / 10) (hLT : LTBetaStmt (1 / 4) C) : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bLink N s) ≤ ENNReal.ofReal (3 * Real.exp (-(C * N))) := by
  filter_upwards [hLT, dt_half_all, dt_Zs_bad, eventually_ge_atTop 4] with N hL hH hZ hN s
  set Ev := B1w N s ∩ openCube N ∩ {w | ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 →
      phi (flipP s w) s S < 1 / 4 * betaW w}
  have hsub : bLink N s ⊆ dtHalfBad N ∪ dtZBad N ∪ Ev := by
    intro w hw
    by_cases h1 : w ∈ dtHalfBad N
    · exact Or.inl (Or.inl h1)
    by_cases h2 : w ∈ dtZBad N
    · exact Or.inl (Or.inr h2)
    exact Or.inr (dt_link_det hN hw h1 h2)
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have he : Real.exp (-(2 * N)) ≤ Real.exp (-(C * N)) := Real.exp_le_exp.2 (by nlinarith)
  have he' : Real.exp (-(14 / 10 * N)) ≤ Real.exp (-(C * N)) := Real.exp_le_exp.2 (by nlinarith)
  calc cubeM N (bLink N s)
      ≤ cubeM N (dtHalfBad N) + cubeM N (dtZBad N) + cubeM N Ev :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
    _ ≤ ENNReal.ofReal (Real.exp (-(C * N))) + ENNReal.ofReal (Real.exp (-(C * N))) +
          ENNReal.ofReal (Real.exp (-(C * N))) := by
        gcongr
        · exact hH.trans (ENNReal.ofReal_le_ofReal he)
        · exact hZ.trans (ENNReal.ofReal_le_ofReal he')
        · exact hL s
    _ = ENNReal.ofReal (3 * Real.exp (-(C * N))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
          ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
        ring_nf

lemma D0U_ge_DU (N : ℕ) : DU N ≤ D0U N := by unfold DU D0U; omega

/-- **`NatTier3Rest6Stmt` at rate `1.039`.** -/
theorem natTier3Rest6_proved : NatTier3Rest6Stmt (1039 / 1000) := by
  have hm : (1039 / 1000 : ℝ) < 10395 / 10000 := by norm_num
  filter_upwards [tilt_bound (C := 104 / 100) (by norm_num) (lt2_at le_rfl),
    link_bound (C := 10395 / 10000) (by norm_num) (ltBeta_at (by norm_num)), floor_bound2,
    clrBadC_rare 2, clrBadE_rare 2, scBadC_rare, sceBad_rare, g_superexp 2, g_absorb 20 hm,
    eventually_ge_atTop 100] with N hTl hLk hFl hcC hcE hsC hsE hS hA hN100 s
  classical
  have hN3 : 3 ≤ N := by omega
  set c := 2 ^ N * (N * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2))) with hc
  have hNr : (100 : ℝ) ≤ N := by exact_mod_cast hN100
  have hsub : bNat N s ∩ {w | ¬ Tier3Rest6 N s w} ⊆
      ((({w | ¬ concCAt N w (tcRow w)} ∪ {w | ¬ concEAll N s w}) ∪ (bTilt N s ∪ bLink N s ∪ bFloor N s)) ∪
        (clrBadC N s ∪ clrBadE N s)) ∪ (scBadCEv N s ∪ sceBadEv N s) := by
    rintro w ⟨⟨⟨hB, ho⟩, hNat⟩, hn⟩
    by_contra hall
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hall
    obtain ⟨⟨⟨⟨hcCw, hcEw⟩, ⟨⟨hTw, hLw⟩, hFw⟩⟩, ⟨hCw, hEw⟩⟩, ⟨hSCw, hSEw⟩⟩ := hall
    apply hn
    -- the tilt, link, floor
    have hTilt : XW w (tcRow w) ≤ x0 * N + slT N := by
      by_contra h; exact hTw ⟨⟨hB, ho⟩, h⟩
    have hLink : ∑ k, -Real.log (xE w s k) ≤ XW w (tcRow w) + slT N := by
      by_contra h; exact hLw ⟨⟨hB, ho⟩, h⟩
    have hFloor : ∀ j, 1 / 2 - deltaU N ≤ clamp01 (w (tcRow w) j) := by
      by_contra h; exact hFw ⟨⟨hB, ho⟩, h⟩
    have hdel : deltaU N ≤ 1 / 100 := by
      unfold deltaU; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hfl : ∀ j, 49 / 100 ≤ clamp01 (w (tcRow w) j) := fun j => by have := hFloor j; linarith
    -- the cluster fields
    have hCl : (∀ A' : Finset (Fin N), A'.card < 2 * DU N →
        5 * (DU N : ℝ) < ∑ j ∈ A'ᶜ, (kF (lamCz (flipP s w) s (tcRow w)) j - lcMin s w)) ∧
        5 * (univ.filter fun j => kF (lamCz (flipP s w) s (tcRow w)) j - lcMin s w ≤ 1 / (N : ℝ)).card < N := by
      by_contra h; exact hCw ⟨ho, hcCw, h⟩
    have hEl : (∀ A' : Finset (Fin N), A'.card < 2 * DU N →
        5 * (DU N : ℝ) < ∑ j ∈ A'ᶜ, (kF (lamEz (flipP s w) s (teW w s)) j - leMinAt s w (teW w s))) ∧
        5 * (univ.filter fun j => kF (lamEz (flipP s w) s (teW w s)) j - leMinAt s w (teW w s) ≤
          1 / (N : ℝ)).card < N := by
      by_contra h; exact hEw ⟨ho, hcEw, h⟩
    have hDD : (7 * (DU N : ℝ)) ≤ 7 * D0U N := by
      have : (DU N : ℝ) ≤ D0U N := by exact_mod_cast D0U_ge_DU N
      linarith
    refine ⟨ho, hCl.1, fun K hK1 hKD => ?_, hCl.2, ⟨hEl.1, fun K hK1 hKD => ?_, hEl.2⟩⟩
    · rcases Nat.lt_or_ge K.card 2 with h2 | h2
      · obtain ⟨x, rfl⟩ := card_eq_one.1 (show K.card = 1 by omega)
        exact lt_of_le_of_lt hDD (hNat x).1
      · by_contra hle; push Not at hle
        exact hSCw ⟨ho, hcCw, hfl, hTilt, K, h2, hKD, hle⟩
    · rcases Nat.lt_or_ge K.card 2 with h2 | h2
      · obtain ⟨x, rfl⟩ := card_eq_one.1 (show K.card = 1 by omega)
        exact lt_of_le_of_lt hDD (hNat x).2
      · by_contra hle; push Not at hle
        exact hSEw ⟨ho, hcEw, by linarith, K, h2, hKD, hle⟩
  -- the measure
  have hc0 : 0 ≤ c := by positivity
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have e1 : Real.exp (-(104 / 100 * (N : ℝ))) ≤ Real.exp (-(10395 / 10000 * (N : ℝ))) :=
    Real.exp_le_exp.2 (by nlinarith)
  have e2 : Real.exp (-(2 * (N : ℝ))) ≤ Real.exp (-(10395 / 10000 * (N : ℝ))) := Real.exp_le_exp.2 (by nlinarith)
  have e3 : Real.exp (-(11 / 10 * (N : ℝ))) ≤ Real.exp (-(10395 / 10000 * (N : ℝ))) :=
    Real.exp_le_exp.2 (by nlinarith)
  set E := Real.exp (-(10395 / 10000 * (N : ℝ))) with hE
  have hS' : 2 * c ≤ Real.exp (-(2 * (N : ℝ))) := hS
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add ((measure_union_le _ _).trans (add_le_add (concTc_rare hN3 s) (concEAll_rare hN3 s)))
      ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add (hTl s) (hLk s)))
        (hFl s))))) ((measure_union_le _ _).trans (add_le_add (hcC s) (hcE s)))))
    ((measure_union_le _ _).trans (add_le_add (hsC s) (hsE s)))).trans ?_
  have p1 : (0 : ℝ) ≤ 3 * Real.exp (-(104 / 100 * (N : ℝ))) := by positivity
  have p2 : (0 : ℝ) ≤ 3 * E := by positivity
  have p3 : (0 : ℝ) ≤ Real.exp (-(2 * (N : ℝ))) := (Real.exp_pos _).le
  have p4 : (0 : ℝ) ≤ 2 * Real.exp (-(2 * (N : ℝ))) + 2 * Real.exp (-(2 * (N : ℝ))) := by positivity
  have p5 : (0 : ℝ) ≤ Real.exp (-(11 / 10 * (N : ℝ))) + Real.exp (-(11 / 10 * (N : ℝ))) := by positivity
  have q2 : (0 : ℝ) ≤ 2 * Real.exp (-(2 * (N : ℝ))) := by positivity
  have q3 : (0 : ℝ) ≤ Real.exp (-(11 / 10 * (N : ℝ))) := (Real.exp_pos _).le
  rw [← ENNReal.ofReal_add q2 q2, ← ENNReal.ofReal_add q3 q3]
  rw [← ENNReal.ofReal_add hc0 hc0, ← ENNReal.ofReal_add p1 p2, ← ENNReal.ofReal_add (add_nonneg p1 p2) p3,
    ← ENNReal.ofReal_add (add_nonneg hc0 hc0) (add_nonneg (add_nonneg p1 p2) p3),
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg hc0 hc0) (add_nonneg (add_nonneg p1 p2) p3)) p4,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg hc0 hc0) (add_nonneg (add_nonneg p1 p2) p3)) p4) p5]
  refine ENNReal.ofReal_le_ofReal ?_
  have hA' : 20 * E ≤ Real.exp (-(1039 / 1000 * (N : ℝ))) := hA
  linarith

end Census
end IIT
