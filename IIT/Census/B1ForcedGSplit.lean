/-
Census, B1 forced leaves 4, 5, 7: reductions of the four open statements of `B1ForcedD*`, agent "forcedG".

PROVED here (sorry-free):
* `g_absorb`            : `K e^{-C' N} ≤ e^{-C N}` eventually when `C < C'`.
* `ltBeta_of_LT2_hi`    : `LTBetaStmt (1/4) C` from `LT2Stmt 1 C₁` and `LTBetaHiStmt (1/4) C₂` (`C < C₁, C₂`):
                          below `σ_N` the LT2 pair (`≥ 3σ_N > β/4`) does it; above `σ_N` it is the high-`β` statement.
* `natLT3_of_split`     : `NatLT3Stmt C` from `NatLT3HuStmt lamU C₁` (LT3 under `H_u`, W2 §8 with RL of W8) and
                          `NatNotHuStmt lamU C₂` (`bNat ∩ ¬H_u` is rare, W11 Case A ≥ 1.3060, Case B ≥ 1.3122).
* `natTier3_det`        : DETERMINISTIC Tier 3 upper bound: on `Tier3Good`, `φ_s(U) ≤ β Fᶜ_j` for every `j`
                          (W3 Thm 5.1 + Lemma G', through `univ_tier3`).
* `natTier3_of_good`    : `NatTier3Stmt C` from `NatTier3GoodStmt C` (`bNat ∖ Tier3Good` is rare).
-/
import IIT.Census.B1ForcedDNat
import IIT.Census.B1UnivMIP
import IIT.Census.B1Events

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-! ### Rates -/

/-- `K e^{-C' N} ≤ e^{-C N}` eventually, for `C < C'`. -/
lemma g_absorb (K : ℝ) {C C' : ℝ} (hC : C < C') :
    ∀ᶠ N : ℕ in atTop, K * Real.exp (-(C' * N)) ≤ Real.exp (-(C * N)) := by
  have ht : Tendsto (fun N : ℕ => Real.exp (-((C' - C) * N))) atTop (𝓝 0) := by
    have hpos : 0 < C' - C := by linarith
    apply Real.tendsto_exp_atBot.comp
    apply tendsto_neg_atTop_atBot.comp
    exact (tendsto_natCast_atTop_atTop).const_mul_atTop hpos
  filter_upwards [(ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (|K| + 1))))] with N hN
  have e : Real.exp (-(C' * N)) = Real.exp (-((C' - C) * N)) * Real.exp (-(C * N)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  have h1 := Real.exp_pos (-(C * N))
  have h2 := Real.exp_pos (-((C' - C) * N))
  have hK : K ≤ |K| := le_abs_self K
  have : (|K| + 1) * Real.exp (-((C' - C) * N)) < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hN; linarith
  nlinarith [abs_nonneg K, mul_le_mul_of_nonneg_right hK (mul_nonneg h2.le h1.le)]

/-- Two rare events at rates `C₁, C₂ > C` give a union rare at rate `C`. -/
lemma g_union_rate {C C₁ C₂ : ℝ} (h1 : C < C₁) (h2 : C < C₂) :
    ∀ᶠ N : ℕ in atTop, ∀ A B : Set (Param N),
      cubeM N A ≤ ENNReal.ofReal (Real.exp (-(C₁ * N))) →
      cubeM N B ≤ ENNReal.ofReal (Real.exp (-(C₂ * N))) →
      cubeM N (A ∪ B) ≤ ENNReal.ofReal (Real.exp (-(C * N))) := by
  have hm : C < (C + min C₁ C₂) / 2 := by have := lt_min h1 h2; linarith
  have hm' : (C + min C₁ C₂) / 2 < min C₁ C₂ := by have := lt_min h1 h2; linarith
  filter_upwards [g_absorb 2 hm] with N hN A B hA hB
  set C' := (C + min C₁ C₂) / 2
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have e1 : Real.exp (-(C₁ * N)) ≤ Real.exp (-(C' * N)) :=
    Real.exp_le_exp.2 (by have := (hm'.trans_le (min_le_left C₁ C₂)); nlinarith)
  have e2 : Real.exp (-(C₂ * N)) ≤ Real.exp (-(C' * N)) :=
    Real.exp_le_exp.2 (by have := (hm'.trans_le (min_le_right C₁ C₂)); nlinarith)
  calc cubeM N (A ∪ B) ≤ cubeM N A + cubeM N B := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(C' * N))) + ENNReal.ofReal (Real.exp (-(C' * N))) :=
        add_le_add (hA.trans (ENNReal.ofReal_le_ofReal e1)) (hB.trans (ENNReal.ofReal_le_ofReal e2))
    _ = ENNReal.ofReal (2 * Real.exp (-(C' * N))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]; ring_nf
    _ ≤ ENNReal.ofReal (Real.exp (-(C * N))) := ENNReal.ofReal_le_ofReal hN

/-! ### LTβ: split at `β = σ_N` -/

/-- **The pair/triple level bound above `σ_N`** (W2 §8 LT3 + W8 RL + W11 Top', with the tilt): on B1 with
`β ≥ σ_N`, some pair or triple reaches `c β`. -/
def LTBetaHiStmt (c C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (B1w N s ∩ openCube N ∩ {w | sigN N ≤ betaW w ∧ ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 →
      phi (flipP s w) s S < c * betaW w}) ≤ ENNReal.ofReal (Real.exp (-(C * N)))

/-- **LTβ from LT2 and the high-`β` statement.** -/
theorem ltBeta_of_LT2_hi {C C₁ C₂ : ℝ} (h1 : C < C₁) (h2 : C < C₂) (hLT : LT2Stmt 1 C₁)
    (hHi : LTBetaHiStmt (1 / 4) C₂) : LTBetaStmt (1 / 4) C := by
  filter_upwards [hLT, hHi, g_union_rate h1 h2] with N hL hH hU s
  refine (measure_mono ?_).trans (hU _ _ (hL s) (hH s))
  rintro w ⟨hw, hall⟩
  by_cases hb : sigN N ≤ betaW w
  · exact Or.inr ⟨hw, hb, hall⟩
  · refine Or.inl ⟨by linarith [not_le.1 hb], fun S hS => ?_⟩
    have := hall S (by omega) (by omega)
    have hβ := betaW_nonneg w
    linarith [not_le.1 hb]

/-! ### NatLT3: split along `H_u` -/

/-- W2's `H_u`: the current row is `tc` or is much lighter than `tc`. -/
def HuW (s : State N) (w : Param N) (lamU : ℝ) : Prop := s = tcRow w ∨ Pw w s ≤ lamU * Pw w (tcRow w)

/-- **LT3 under `H_u`** in the natural regime (W2 Thm LT3, with `H_Sp` removed by RL = W8 Thm RL_sym/RL-tc,
`β ≥ L σ_N` from LT2(L) + Tier 3, `y_top ≥ 4/5` from the tilt). -/
def NatLT3HuStmt (lamU C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bNat N s ∩ {w | HuW s w lamU ∧ ∀ S : Finset (Fin N), S.card = 3 →
      phi (flipP s w) s S < (1 - dnEps) * levTrip * yTopW w dnEps * betaW w}) ≤
      ENNReal.ofReal (Real.exp (-(C * N)))

/-- **`¬H_u` is rare in the natural regime** (W11: Case A ≥ 1.3060 by Chernoff; Case B ≥ 1.3122 by
LT3-with-Top' + Tier 3 + the raised floor 0.7008 + s heavy). -/
def NatNotHuStmt (lamU C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bNat N s ∩ {w | ¬ HuW s w lamU}) ≤ ENNReal.ofReal (Real.exp (-(C * N)))

/-- **NatLT3 from the `H_u` split.** -/
theorem natLT3_of_split {lamU C C₁ C₂ : ℝ} (h1 : C < C₁) (h2 : C < C₂) (hHu : NatLT3HuStmt lamU C₁)
    (hNot : NatNotHuStmt lamU C₂) : NatLT3Stmt C := by
  filter_upwards [hHu, hNot, g_union_rate h1 h2] with N hA hB hU s
  refine (measure_mono ?_).trans (hU _ _ (hA s) (hB s))
  rintro w ⟨hw, hall⟩
  by_cases h : HuW s w lamU
  · exact Or.inl ⟨hw, h, hall⟩
  · exact Or.inr ⟨hw, h⟩

/-! ### NatTier3: the deterministic part -/

/-- `λ_min` on the effect side at an arbitrary effect state `te`. -/
noncomputable def leMinAt (s : State N) (w : Param N) (te : State N) : ℝ :=
  ⨅ j, kF (lamEz (flipP s w) s te) j

/-- The single-cut values at `(tcRow, te)`. -/
noncomputable def phTAt (s : State N) (w : Param N) (te : State N) (j : Fin N) : ℝ :=
  phT (lamCz (flipP s w) s (tcRow w)) (lamEz (flipP s w) s te)
    (sysBackCause (tpmOf (flipP s w)) univ s s (tcRow w))
    (sysEffProb (tpmOf (flipP s w)) univ s s te) j

/-- **The Tier 3 good event**: `tcRow w` is the unique maximal cause state of `U`, and at EVERY maximal effect state
`te` the W10 hypotheses hold on both sides (with `λ_min = lcMin`, `leMinAt te`, a common `D, d*`) and the single-cut
values have no exact tie.  (The maximal effect state need not be `teW`: W5's Lemma TE needs every `x_k ≥ 1/2 + μ`,
which fails with only polynomially small probability.) -/
structure Tier3Good (N : ℕ) (s : State N) (w : Param N) : Prop where
  mem_open : w ∈ openCube N
  stateC : sysMaxCauseStates (tpmOf (flipP s w)) univ s s = {tcRow w}
  key : ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) univ s s, ∃ (ac ae : ℝ) (epc epe : ℕ → ℝ) (D dstar : ℕ),
    KeyHyp (lamCz (flipP s w) s (tcRow w)) (lcMin s w) ac epc D dstar ∧
    KeyHyp (lamEz (flipP s w) s te) (leMinAt s w te) ae epe D dstar
  noTie : ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) univ s s, ∀ j j', j ≠ j' → phTAt s w te j ≠ phTAt s w te j'

lemma g_ciInf_attained (hN : 1 ≤ N) (f : Fin N → ℝ) : ∃ j, f j = ⨅ j, f j := by
  have : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  exact exists_eq_ciInf_of_finite

/-- **Tier 3, deterministic upper bound**: on `Tier3Good`, `φ_s(U) ≤ β · Fᶜ_j` for every unit `j`. -/
theorem natTier3_det (hN : 2 ≤ N) {s : State N} {w : Param N} (hg : Tier3Good N s w) (j : Fin N) :
    phi (flipP s w) s univ ≤ betaW w * kF (lamCz (flipP s w) s (tcRow w)) j := by
  have hz : flipP s w ∈ openCube N := flipP_mem_openCube hg.mem_open
  have hβ : sysBackCause (tpmOf (flipP s w)) univ s s (tcRow w) = betaW w := by
    rw [sysBackCause_univ_eq hz, flipP_invol s w]; rfl
  unfold phi sysPhi
  -- nonnegativity of the bound, from any maximal effect state
  obtain ⟨te0, hte0⟩ := sysMaxEffStates_nonempty (tpmOf (flipP s w)) univ s s
  obtain ⟨_, _, _, _, _, _, hc0, _⟩ := hg.key te0 hte0
  have hFc0 : 0 ≤ kF (lamCz (flipP s w) s (tcRow w)) j := (hc0.hP.trans_le (hc0.hmin j)).le
  have hX0 : 0 ≤ betaW w * kF (lamCz (flipP s w) s (tcRow w)) j := mul_nonneg (betaW_nonneg w) hFc0
  refine sup'OrZero_le hX0 fun q hq => ?_
  rw [hg.stateC, mem_product, mem_singleton] at hq
  obtain ⟨q1, te⟩ := q
  obtain ⟨rfl, hte⟩ := hq
  obtain ⟨ac, ae, epc, epe, D, dstar, hc, he⟩ := hg.key te hte
  obtain ⟨jst, -, hjst⟩ := exists_min_image (univ : Finset (Fin N)) (phTAt s w te)
    ⟨⟨0, by omega⟩, mem_univ _⟩
  have h3 := univ_tier3 hz hN s (tcRow w) te hc he
    (g_ciInf_attained (by omega) _) (g_ciInf_attained (by omega) _) (hg.noTie te hte) jst
    (fun j' => hjst j' (mem_univ j'))
  simp only
  rw [h3]
  calc phTAt s w te jst ≤ phTAt s w te j := hjst j (mem_univ j)
    _ ≤ sysBackCause (tpmOf (flipP s w)) univ s s (tcRow w) * kF (lamCz (flipP s w) s (tcRow w)) j :=
        min_le_left _ _
    _ = betaW w * kF (lamCz (flipP s w) s (tcRow w)) j := by rw [hβ]

/-- **The residual probabilistic statement of Tier 3**: `bNat ∖ Tier3Good` is rare. -/
def NatTier3GoodStmt (C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bNat N s ∩ {w | ¬ Tier3Good N s w}) ≤ ENNReal.ofReal (Real.exp (-(C * N)))

/-- **NatTier3 from the good event.** -/
theorem natTier3_of_good {C : ℝ} (h : NatTier3GoodStmt C) : NatTier3Stmt C := by
  filter_upwards [h, eventually_ge_atTop 2] with N hN hN2 s
  refine (measure_mono ?_).trans (hN s)
  rintro w ⟨hw, hnot⟩
  refine ⟨hw, fun hg => hnot fun j => natTier3_det hN2 hg j⟩

end Census
end IIT
