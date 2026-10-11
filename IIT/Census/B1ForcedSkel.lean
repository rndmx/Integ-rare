/-
Census, B1 leaf `B1_forcedX` (D1'): skeleton.

`B1w \ ForcedX` is covered by `(openCube)ᶜ` (null) and 22 explicit bad events:
* `bZs`      : `Zs` outside `[1/2, 13]` (B3 regularity);
* six proxy events (hypotheses of the proxy lemmas `regEv_of_fail_cause/effect`): positivity of the
  cause-side minimal full-cut value (the effect side needs none: `x_j ≥ 1/2` always), the cause and effect half-means, tilt (T, from LT2 + B3), link (L),
  profile floor (Y);
* `bNat`     : the natural regime (no failing singleton on either side), excluded by LT3 + CNat;
* 14 field events: `RegEvX` holds at some `(x, σ)` at `tcRow w` but one `B1FGoodX` field fails.
The deterministic cover (`forced_cover`) and the measure assembly (`B1_forcedX_of_leaves`) are proved;
each bad event is a separately stated leaf with rate `RfF = 1.0105 > RbadX = 1.01` (all certified rates of
W7 §7 are ≥ 1.010803).
-/
import IIT.Census.B1Proxy

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- Common rate of the forcing leaves (W7 §7: minimum certified exclusion rate 1.010803). -/
noncomputable def RfF : ℝ := 10105 / 10000

/-! ### The proxy quantities at `(tcRow w, teW w s)` (flipped coordinates `w`, `z = flipP s w`) -/

/-- `λ_min` on the cause side: the smallest full-cut value. -/
noncomputable def lcMin (s : State N) (w : Param N) : ℝ :=
  ⨅ j, kF (lamCz (flipP s w) s (tcRow w)) j

/-- `λ_min` on the effect side. -/
noncomputable def leMin (s : State N) (w : Param N) : ℝ :=
  ⨅ j, kF (lamEz (flipP s w) s (teW w s)) j

/-- The natural regime: every singleton is `SmallCutGood` (threshold `7·D0U`) on both sides. -/
def NatEv (N : ℕ) (s : State N) (w : Param N) : Prop :=
  ∀ x : Fin N, 7 * (D0U N : ℝ) < kM (lamCz (flipP s w) s (tcRow w)) (lcMin s w) {x} ∧
    7 * (D0U N : ℝ) < kM (lamEz (flipP s w) s (teW w s)) (leMin s w) {x}

/-! ### The bad events -/

def bZs (N : ℕ) (s : State N) : Set (Param N) := B1w N s ∩ {w | ¬ (1 / 2 ≤ Zs w ∧ Zs w ≤ b1ZMax)}
def bPos (N : ℕ) (s : State N) : Set (Param N) :=
  B1w N s ∩ openCube N ∩ {w | ¬ 0 < lcMin s w}
def bHalfC (N : ℕ) (s : State N) : Set (Param N) :=
  B1w N s ∩ openCube N ∩ {w | ¬ ∀ j, |cmean w {j} (tcRow w) j - 1 / 2| ≤ deltaU N}
def bHalfE (N : ℕ) (s : State N) : Set (Param N) :=
  B1w N s ∩ openCube N ∩ {w | ¬ ∀ j,
    |effUnit (tpmOf (flipP s w)) (univ.erase j)ᶜ s j (teW w s j) - 1 / 2| ≤ deltaU N}
def bTilt (N : ℕ) (s : State N) : Set (Param N) :=
  B1w N s ∩ openCube N ∩ {w | ¬ XW w (tcRow w) ≤ x0 * N + slT N}
def bLink (N : ℕ) (s : State N) : Set (Param N) :=
  B1w N s ∩ openCube N ∩ {w | ¬ ∑ k, -Real.log (xE w s k) ≤ XW w (tcRow w) + slT N}
def bFloor (N : ℕ) (s : State N) : Set (Param N) :=
  B1w N s ∩ openCube N ∩ {w | ¬ ∀ j, 1 / 2 - deltaU N ≤ clamp01 (w (tcRow w) j)}
def bNat (N : ℕ) (s : State N) : Set (Param N) := B1w N s ∩ openCube N ∩ {w | NatEv N s w}

/-- Field events: the regime event holds at `(tcRow w, x, σ)` but the field `P` fails. -/
def bField (N : ℕ) (s : State N) (P : Param N → Fin N → XSide → Prop) : Set (Param N) :=
  B1w N s ∩ openCube N ∩ {w | ∃ x σ, RegEvX N s (tcRow w) x σ w ∧ ¬ P w x σ}

/-! The fourteen fields of `B1FGoodX` other than `regEv`, `openRows`, at `r0 = tcRow w`. -/
def fFar (N : ℕ) (s : State N) : Param N → Fin N → XSide → Prop := fun w _ _ => N ≤ 3 * ham (tcRow w) s
def fRet (N : ℕ) (s : State N) : Param N → Fin N → XSide → Prop := fun w x _ =>
  ∀ r ∈ sensRows s (tcRow w), r ≠ tcRow w → r ≠ spRow s (tcRow w) x .cause → ∀ K : Finset (Fin N),
    K.card ≤ dX N → XW w (tcRow w) + b1Eta * N < XMW w (univ \ K) r
def fRetR1 (N : ℕ) (_s : State N) : Param N → Fin N → XSide → Prop := fun w x σ =>
  σ = .cause → (N : ℝ) / 400 ≤
    ∑ j ∈ univ.erase x, Real.log (clamp01 (w (tcRow w) j) / clamp01 (w (flipAt x (tcRow w)) j))
def fRowExc (N : ℕ) (s : State N) : Param N → Fin N → XSide → Prop := fun w x σ =>
  ∀ r ∈ sensRows s (tcRow w), r ≠ tcRow w → r ≠ s → r ≠ spRow s (tcRow w) x σ →
    ∑ i, pos (clamp01 (w r i) - b1Cap) ≤ (N : ℝ) / 5
def fNuS (N : ℕ) (s : State N) : Param N → Fin N → XSide → Prop := fun w _ _ =>
  ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 2 →
    ∑ i, Real.log (max (2 * b1CutMeanS w s (tcRow w) K' i) 1) ≤ 23 / 50 * (N : ℝ)
def fNuTc (N : ℕ) (_s : State N) : Param N → Fin N → XSide → Prop := fun w _ σ =>
  σ = .effect → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 3 →
    ∑ i, Real.log (max (2 * b1CutMeanPlus w (tcRow w) K' i) 1) ≤ 23 / 50 * (N : ℝ)
def fX5 (N : ℕ) (_s : State N) : Param N → Fin N → XSide → Prop := fun w x σ =>
  σ = .cause → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 3 → x ∉ K' →
    ∑ i, Real.log (max (2 * b1CutMeanPlus w (flipAt x (tcRow w)) K' i) 1) ≤ 23 / 50 * (N : ℝ)
def fPosNear (N : ℕ) (_s : State N) : Param N → Fin N → XSide → Prop := fun w x σ =>
  ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 4 → (σ = .cause → K' ≠ {x}) →
    (N : ℝ) / 25 ≤ ∑ i, b1CutGX w (tcRow w) K' i
def fX1 (N : ℕ) (s : State N) : Param N → Fin N → XSide → Prop := fun w x σ =>
  σ = .cause → -((N : ℝ) / 2000) ≤
    ∑ j ∈ univ.erase x, min (lamX w s (tcRow w) x .cause j) (Real.log (clamp01 (w (tcRow w) j) / cX))
def fX2 (N : ℕ) (_s : State N) : Param N → Fin N → XSide → Prop := fun w x σ =>
  σ = .cause → N ≤ 4 * (NegX w (tcRow w) x).card
def fFailOnly (N : ℕ) (s : State N) : Param N → Fin N → XSide → Prop := fun w x _ =>
  ∀ x' : Fin N, x' ≠ x → SingleNotFail w s (tcRow w) x'
def fSRowMu (N : ℕ) (s : State N) : Param N → Fin N → XSide → Prop := fun w _ _ =>
  ∀ h : (univ : Finset (Fin N)).Nonempty,
    Real.exp ((N : ℝ) / 100) * sigN N ≤ univ.inf' h (fun k => xE w s k - 1 / 2)
def fSRowE (N : ℕ) (s : State N) : Param N → Fin N → XSide → Prop := fun w _ _ =>
  (2 : ℝ) ^ (-(N : ℝ) / 2) ≤ eE w s
def fSRowR (N : ℕ) (s : State N) : Param N → Fin N → XSide → Prop := fun w _ _ =>
  ∑ r ∈ (sensRows s (tcRow w)).erase s, ∏ k, pTe w s r k ≤ sigN N

/-- The 22 bad events, indexed. -/
def forcedBad (N : ℕ) (s : State N) : Fin 22 → Set (Param N) :=
  ![bZs N s, bPos N s, bHalfC N s, bHalfE N s, bTilt N s, bLink N s, bFloor N s, bNat N s,
    bField N s (fFar N s), bField N s (fRet N s), bField N s (fRetR1 N s), bField N s (fRowExc N s),
    bField N s (fNuS N s), bField N s (fNuTc N s), bField N s (fX5 N s), bField N s (fPosNear N s),
    bField N s (fX1 N s), bField N s (fX2 N s), bField N s (fFailOnly N s), bField N s (fSRowMu N s),
    bField N s (fSRowE N s), bField N s (fSRowR N s)]

/-! ### Deterministic part -/

/-- **Regime from the proxy hypotheses**: off the natural regime, some unit fails on some side, and the proxy
lemma places the F-data in `RegEvX` at `tcRow w`. -/
theorem regEv_of_notNat {s : State N} {w : Param N} (hw : w ∈ openCube N)
    (hδ : deltaU N ≤ 1 / 1000000) (hP : 0 < lcMin s w)
    (hqc : ∀ j, |cmean w {j} (tcRow w) j - 1 / 2| ≤ deltaU N)
    (hqe : ∀ j, |effUnit (tpmOf (flipP s w)) (univ.erase j)ᶜ s j (teW w s j) - 1 / 2| ≤ deltaU N)
    (hT : XW w (tcRow w) ≤ x0 * N + slT N)
    (hL : ∑ k, -Real.log (xE w s k) ≤ XW w (tcRow w) + slT N)
    (hY : ∀ j, 1 / 2 - deltaU N ≤ clamp01 (w (tcRow w) j)) (hNat : ¬ NatEv N s w) :
    ∃ x σ, RegEvX N s (tcRow w) x σ w := by
  have hz : flipP s w ∈ openCube N := flipP_mem_openCube hw
  have e : flipP s (flipP s w) = w := flipP_invol s w
  unfold NatEv at hNat
  push Not at hNat
  obtain ⟨x, hx⟩ := hNat
  by_cases hc : 7 * (D0U N : ℝ) < kM (lamCz (flipP s w) s (tcRow w)) (lcMin s w) {x}
  · have he := hx hc
    refine ⟨x, .effect, ?_⟩
    have := regEv_of_fail_effect hz s (tcRow w) x
      (by rw [e]; exact fun j => ciInf_le (Finite.bddBelow_range _) j)
      (by rw [e]; exact hqe) hδ (by rw [e]; exact he)
      (by rw [e]; exact hT) (by rw [e]; exact hL) (by rw [e]; exact hY)
    rwa [e] at this
  · push Not at hc
    refine ⟨x, .cause, ?_⟩
    have := regEv_of_fail_cause hz s (tcRow w) x hP
      (fun j => ciInf_le (Finite.bddBelow_range _) j)
      (by rw [e]; exact hqc) hδ hc (by rw [e]; exact hT) (by rw [e]; exact hL)
    rwa [e] at this

/-- **The cover**: `B1w \ ForcedX ⊆ (openCube)ᶜ ∪ ⋃ i, forcedBad i`. -/
theorem forced_cover {s : State N} (hN : 0 < N) (hδ : deltaU N ≤ 1 / 1000000) :
    B1w N s \ {w | ForcedX N s w} ⊆ (openCube N)ᶜ ∪ ⋃ i, forcedBad N s i := by
  rintro w ⟨hB, hF⟩
  by_contra hc
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion, not_or, not_not, not_exists] at hc
  obtain ⟨hw, hbad⟩ := hc
  have g : ∀ i : Fin 22, w ∉ forcedBad N s i := hbad
  have hBo : w ∈ B1w N s ∩ openCube N := ⟨hB, hw⟩
  have hZ : 1 / 2 ≤ Zs w ∧ Zs w ≤ b1ZMax := by
    by_contra h; exact g 0 ⟨hB, h⟩
  have hP : 0 < lcMin s w := by by_contra h; exact g 1 ⟨hBo, h⟩
  have hqc : ∀ j, |cmean w {j} (tcRow w) j - 1 / 2| ≤ deltaU N := by by_contra h; exact g 2 ⟨hBo, h⟩
  have hqe : ∀ j, |effUnit (tpmOf (flipP s w)) (univ.erase j)ᶜ s j (teW w s j) - 1 / 2| ≤ deltaU N := by
    by_contra h; exact g 3 ⟨hBo, h⟩
  have hT : XW w (tcRow w) ≤ x0 * N + slT N := by by_contra h; exact g 4 ⟨hBo, h⟩
  have hL : ∑ k, -Real.log (xE w s k) ≤ XW w (tcRow w) + slT N := by by_contra h; exact g 5 ⟨hBo, h⟩
  have hY : ∀ j, 1 / 2 - deltaU N ≤ clamp01 (w (tcRow w) j) := by by_contra h; exact g 6 ⟨hBo, h⟩
  have hNat : ¬ NatEv N s w := fun h => g 7 ⟨hBo, h⟩
  obtain ⟨x, σ, hreg⟩ := regEv_of_notNat hw hδ hP hqc hqe hT hL hY hNat
  have fld : ∀ (i : Fin 22) (P : Param N → Fin N → XSide → Prop),
      forcedBad N s i = bField N s P → P w x σ := by
    intro i P hi
    by_contra h
    exact g i (hi ▸ ⟨hBo, x, σ, hreg, h⟩)
  apply hF
  refine ⟨hw, hZ, x, σ, ?_⟩
  exact
    { regEv := hreg
      openRows := fun r _ i => hw r i
      far := fld 8 _ rfl
      ret := fld 9 _ rfl
      retR1 := fld 10 _ rfl
      rowExc := fld 11 _ rfl
      nuS := fld 12 _ rfl
      nuTc := fld 13 _ rfl
      x5 := fld 14 _ rfl
      posNear := fld 15 _ rfl
      x1 := fld 16 _ rfl
      x2 := fld 17 _ rfl
      failOnly := fld 18 _ rfl
      sRowMu' := fld 19 _ rfl
      sRowE := fld 20 _ rfl
      sRowR := fld 21 _ rfl }

lemma deltaU_small : ∀ᶠ N : ℕ in atTop, deltaU N ≤ 1 / 1000000 := by
  filter_upwards [eventually_ge_atTop 999999] with N hN
  unfold deltaU
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (999999 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

/-- `22 e^{-RfF N} ≤ 3 e^{-RbadX N}` eventually. -/
lemma absorb22 : ∀ᶠ N : ℕ in atTop,
    22 * Real.exp (-(RfF * N)) ≤ 3 * Real.exp (-(RbadX * N)) := by
  have ht : Tendsto (fun N : ℕ => Real.exp (-((RfF - RbadX) * N))) atTop (𝓝 0) := by
    have hpos : 0 < RfF - RbadX := by unfold RfF RbadX; norm_num
    apply Real.tendsto_exp_atBot.comp
    apply tendsto_neg_atTop_atBot.comp
    exact (tendsto_natCast_atTop_atTop).const_mul_atTop hpos
  filter_upwards [(ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 3 / 22)))] with N hN
  have e : Real.exp (-(RfF * N)) = Real.exp (-((RfF - RbadX) * N)) * Real.exp (-(RbadX * N)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  have := Real.exp_pos (-(RbadX * N))
  nlinarith

/-- **Assembly**: the 22 leaf bounds give `B1_forcedX`. -/
theorem B1_forcedX_of_leaves
    (hleaf : ∀ i : Fin 22, ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s i) ≤ ENNReal.ofReal (Real.exp (-(RfF * N)))) :
    ∀ᶠ N in atTop, ∀ s : State N,
      cubeM N (B1w N s \ {w | ForcedX N s w}) ≤ ENNReal.ofReal (3 * Real.exp (-(RbadX * N))) := by
  have hall : ∀ᶠ N : ℕ in atTop, ∀ i : Fin 22, ∀ s : State N,
      cubeM N (forcedBad N s i) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) :=
    Filter.eventually_all.2 hleaf
  filter_upwards [hall, deltaU_small, absorb22, eventually_ge_atTop 1] with N hl hδ hab hN s
  calc cubeM N (B1w N s \ {w | ForcedX N s w})
      ≤ cubeM N ((openCube N)ᶜ ∪ ⋃ i, forcedBad N s i) := measure_mono (forced_cover hN hδ)
    _ ≤ cubeM N (openCube N)ᶜ + cubeM N (⋃ i, forcedBad N s i) := measure_union_le _ _
    _ ≤ 0 + ∑ i, cubeM N (forcedBad N s i) := by
        rw [cubeM_compl_openCube]; exact add_le_add le_rfl (measure_iUnion_fintype_le _ _)
    _ ≤ 0 + ∑ _i : Fin 22, ENNReal.ofReal (Real.exp (-(RfF * N))) :=
        add_le_add le_rfl (Finset.sum_le_sum fun i _ => hl i s)
    _ = ENNReal.ofReal (22 * Real.exp (-(RfF * N))) := by
        rw [zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (by norm_num)]
        simp
    _ ≤ ENNReal.ofReal (3 * Real.exp (-(RbadX * N))) := ENNReal.ofReal_le_ofReal hab

end Census
end IIT
