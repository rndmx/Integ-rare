/-
Census, B1: the final assembly of `CountX3Stmt` from the work-package statements of W14
(`iit-census/lean/B1-W14-count-lean.md`).  Everything here is PROVED; the open content sits in the
hypotheses, each the main statement of one work package (defined in `B1CntDefs3.lean`):

* WP2: `CauseDetStmt`, `SysCauseStmt`;   * WP3: `EffDetStmt`, `SysEffStmt`;
* WP4: `FreshProbStmt`;                   * WP5: `RetMarkovStmt`, `MeanYStmt`;
* WP6: `FamBigStmt`, `MeanYStmt → ChebStmt`.

Route (W9 §4.2 + §5.8).  Lemma DET: for `GoodW3` data outside `BadCountX`, every `K ∈ famX3` with
`Y_K ∧ Ret_K` gives a certified mechanism `U \ K` (`distOK_of_sides`), and there are at least
`W - RF ≥ |famX3| pY/4 ≥ LCnt N` of them.  Theorem CE: `BadCountX` has fresh probability
`≤ e^{-N/200} + e^{-N/40} + e^{-N/450} ≤ e^{-N/500}`; WP4's `FreshProbStmt` is itself assembled
here (`freshProb_of_fields`) from the ten per-field statements `FreshFieldProb FE·X (1/180)`.
-/
import IIT.Census.B1CntDefs3

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

lemma phiFloor_pos (hN : 1 ≤ N) : 0 < phiFloor N := by
  unfold phiFloor
  have : (0 : ℝ) < N := Nat.cast_pos.2 hN
  positivity

/-- **Lemma DIST, assembly**: the four side statements give `DistOK`. -/
theorem distOK_of_sides {s r0 : State N} {w : Param N} {M : Finset (Fin N)} (hN : 1 ≤ N)
    (hsc : sysMaxCauseStates (tpmOf (flipP s w)) univ s s = {r0})
    (hse : sysMaxEffStates (tpmOf (flipP s w)) univ s s = {teW w s})
    (hcp : maxCausePurviewsAt (tpmOf (flipP s w)) univ s M s = {(univ, r0)})
    (hcphi : phiFloor N ≤ phiCmechAt (tpmOf (flipP s w)) univ s M s)
    (hpe : ∃ pe ∈ maxEffPurviewsAt (tpmOf (flipP s w)) univ s M s,
      stated pe.1 pe.2 ⊆ stated univ (teW w s))
    (hephi : phiFloor N ≤ phiEmechAt (tpmOf (flipP s w)) univ s M s) :
    DistOK s r0 w M := by
  have hmin : phiFloor N ≤ phiDAt (tpmOf (flipP s w)) univ s M s := le_min hcphi hephi
  obtain ⟨pe, hpe, hsub⟩ := hpe
  have hcong : Congruent (tpmOf (flipP s w)) univ s s (stated univ r0) (stated pe.1 pe.2) := by
    unfold Congruent
    refine ⟨⟨stated univ r0, ?_, subset_refl _⟩, ⟨stated univ (teW w s), ?_, hsub⟩⟩
    · unfold sysStatedCause
      exact mem_image_of_mem _ (by rw [hsc]; exact mem_singleton_self _)
    · unfold sysStatedEffect
      exact mem_image_of_mem _ (by rw [hse]; exact mem_singleton_self _)
  have hpc : ((univ : Finset (Fin N)), r0) ∈ maxCausePurviewsAt (tpmOf (flipP s w)) univ s M s := by
    rw [hcp]; exact mem_singleton_self _
  unfold DistOK
  exact ⟨mem_distinctionMechsAt.2 ⟨subset_univ _, (phiFloor_pos hN).trans_le hmin,
    (univ, r0), hpc, pe, hpe, hcong⟩, hcp, hmin⟩

lemma card_filter_le_and_add {α : Type*} (F : Finset α) (P Q : α → Prop) :
    (F.filter P).card ≤ (F.filter fun a => P a ∧ Q a).card + (F.filter fun a => ¬ Q a).card := by
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro a ha
  rw [mem_filter] at ha
  by_cases hq : Q a
  · exact mem_union_left _ (mem_filter.2 ⟨ha.1, ha.2, hq⟩)
  · exact mem_union_right _ (mem_filter.2 ⟨ha.1, hq⟩)

/-- **Lemma DET** (W9 §4.2): outside `BadCountX`, good data are outside `BadFam3`. -/
theorem not_badFam_of (hC : CauseDetStmt) (hSC : SysCauseStmt) (hE : EffDetStmt)
    (hSE : SysEffStmt) (hF : FamBigStmt) :
    ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N),
      GoodW3 N s r0 x σ w → w ∉ BadCountX N s r0 x σ → w ∉ BadFam3 N s r0 x σ := by
  filter_upwards [hC, hSC, hE, hSE, hF, eventually_ge_atTop 1] with N hC hSC hE hSE hF hN
  intro s r0 x σ w hg hbad
  have hfr : CountFreshX N s r0 w := by
    by_contra h; exact hbad (Or.inl (Or.inl h))
  have hret : (RFCnt N s r0 x σ w : ℝ) ≤ ((famX3 N s r0 x σ w).card : ℝ) * pY N / 4 := by
    by_contra h; exact hbad (Or.inl (Or.inr (not_le.1 h)))
  have hW : ((famX3 N s r0 x σ w).card : ℝ) * pY N / 2 ≤ (WCnt N s r0 x σ w : ℝ) := by
    by_contra h; exact hbad (Or.inr (not_le.1 h))
  have hsub : (famX3 N s r0 x σ w).filter (fun K => YK N s K w ∧ RetK N s r0 K w) ⊆
      (famX3 N s r0 x σ w).filter (fun K => DistOK s r0 w (univ \ K)) := by
    intro K hK
    rw [mem_filter] at hK ⊢
    obtain ⟨hKf, hY, hR⟩ := hK
    obtain ⟨hcp, hcphi⟩ := hC s r0 x σ w hg hfr K hKf hR
    obtain ⟨hpe, hephi⟩ := hE s r0 x σ w hg hfr K hKf hY
    exact ⟨hKf, distOK_of_sides hN (hSC s r0 x σ w hg hfr) (hSE s r0 x σ w hg hfr) hcp hcphi
      hpe hephi⟩
  have hcnt := (card_filter_le_and_add (famX3 N s r0 x σ w) (fun K => YK N s K w)
    (fun K => RetK N s r0 K w)).trans (Nat.add_le_add_right (card_le_card hsub) _)
  have hL : (WCnt N s r0 x σ w : ℝ) ≤
      (((famX3 N s r0 x σ w).filter fun K => DistOK s r0 w (univ \ K)).card : ℝ) +
        (RFCnt N s r0 x σ w : ℝ) := by
    unfold WCnt RFCnt
    exact_mod_cast hcnt
  have hfam := hF s r0 x σ w hg
  show ¬ ((famX3 N s r0 x σ w).filter fun K => DistOK s r0 w (univ \ K)).card < LCnt N
  rw [not_lt]
  have hreal : (LCnt N : ℝ) ≤
      (((famX3 N s r0 x σ w).filter fun K => DistOK s r0 w (univ \ K)).card : ℝ) := by
    linarith
  exact_mod_cast hreal

lemma exp_three_le_cCnt (hN : 9000 ≤ N) :
    Real.exp (-((N : ℝ) / 200)) + Real.exp (-((N : ℝ) / 40)) + Real.exp (-((N : ℝ) / 450)) ≤
      Real.exp (-(cCnt * N)) := by
  have hN' : (9000 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : Real.exp (-((N : ℝ) / 200)) ≤ Real.exp (-((N : ℝ) / 450)) :=
    Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (-((N : ℝ) / 40)) ≤ Real.exp (-((N : ℝ) / 450)) :=
    Real.exp_le_exp.2 (by linarith)
  have h3 : 3 * Real.exp (-((N : ℝ) / 450)) ≤ Real.exp (-(cCnt * N)) := by
    have e : -(cCnt * (N : ℝ)) = (N : ℝ) / 4500 + -((N : ℝ) / 450) := by unfold cCnt; ring
    rw [e, Real.exp_add]
    have h4 : (3 : ℝ) ≤ Real.exp ((N : ℝ) / 4500) := by
      have := Real.add_one_le_exp ((N : ℝ) / 4500)
      linarith
    exact mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
  linarith

lemma measure_union_le_of {α : Type*} [MeasurableSpace α] {μ : Measure α} {A B : Set α}
    {a b : ENNReal} (hA : μ A ≤ a) (hB : μ B ≤ b) : μ (A ∪ B) ≤ a + b :=
  (measure_union_le A B).trans (add_le_add hA hB)

lemma ten_exp_le (hN : 20000 ≤ N) :
    10 * Real.exp (-((1 / 180 : ℝ) * N)) ≤ Real.exp (-((N : ℝ) / 200)) := by
  have hN' : (20000 : ℝ) ≤ N := by exact_mod_cast hN
  have e : -((N : ℝ) / 200) = (N : ℝ) / 1800 + -((1 / 180 : ℝ) * N) := by ring
  rw [e, Real.exp_add]
  have h4 : (10 : ℝ) ≤ Real.exp ((N : ℝ) / 1800) := by
    have := Real.add_one_le_exp ((N : ℝ) / 1800)
    linarith
  exact mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le

/-- **WP4 assembly**: the ten per-field bounds give `FreshProbStmt`. -/
theorem freshProb_of_fields (h0 : FreshFieldProb FE0X (1 / 180)) (h1 : FreshFieldProb FE1X (1 / 180))
    (h2 : FreshFieldProb FE2X (1 / 180)) (h3 : FreshFieldProb FE3X (1 / 180))
    (h4a : FreshFieldProb FE4aX (1 / 180)) (h4b : FreshFieldProb FE4bX (1 / 180))
    (h5 : FreshFieldProb FE5X (1 / 180)) (h6 : FreshFieldProb FE6X (1 / 180))
    (h7a : FreshFieldProb FE7aX (1 / 180)) (h7b : FreshFieldProb FE7bX (1 / 180)) :
    FreshProbStmt := by
  filter_upwards [h0, h1, h2, h3, h4a, h4b, h5, h6, h7a, h7b, eventually_ge_atTop 20000] with
    N h0 h1 h2 h3 h4a h4b h5 h6 h7a h7b hN
  intro s r0 x σ f _
  have hsub : {g | ¬ CountFreshX N s r0 (glueRows (sensRows s r0) f g)} ⊆
      {g | ¬ FE0X N s r0 (glueRows (sensRows s r0) f g)} ∪
      {g | ¬ FE1X N s r0 (glueRows (sensRows s r0) f g)} ∪
      {g | ¬ FE2X N s r0 (glueRows (sensRows s r0) f g)} ∪
      {g | ¬ FE3X N s r0 (glueRows (sensRows s r0) f g)} ∪
      {g | ¬ FE4aX N s r0 (glueRows (sensRows s r0) f g)} ∪
      {g | ¬ FE4bX N s r0 (glueRows (sensRows s r0) f g)} ∪
      {g | ¬ FE5X N s r0 (glueRows (sensRows s r0) f g)} ∪
      {g | ¬ FE6X N s r0 (glueRows (sensRows s r0) f g)} ∪
      {g | ¬ FE7aX N s r0 (glueRows (sensRows s r0) f g)} ∪
      {g | ¬ FE7bX N s r0 (glueRows (sensRows s r0) f g)} := by
    intro g hg
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨g0, g1⟩, g2⟩, g3⟩, g4a⟩, g4b⟩, g5⟩, g6⟩, g7a⟩, g7b⟩ := hn
    exact hg ⟨g0, g1, g2, g3, g4a, g4b, g5, g6, g7a, g7b⟩
  have key := measure_union_le_of (measure_union_le_of (measure_union_le_of (measure_union_le_of
    (measure_union_le_of (measure_union_le_of (measure_union_le_of (measure_union_le_of
    (measure_union_le_of (h0 s r0 f) (h1 s r0 f)) (h2 s r0 f)) (h3 s r0 f)) (h4a s r0 f))
    (h4b s r0 f)) (h5 s r0 f)) (h6 s r0 f)) (h7a s r0 f)) (h7b s r0 f)
  refine (measure_mono hsub).trans (key.trans ?_)
  set e := ENNReal.ofReal (Real.exp (-((1 / 180 : ℝ) * N)))
  have h10 : e + e + e + e + e + e + e + e + e + e = ENNReal.ofReal (10 * Real.exp (-((1 / 180 : ℝ) * N))) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    ring
  rw [h10]
  exact ENNReal.ofReal_le_ofReal (ten_exp_le hN)

/-- **`CountX3Stmt` from the work-package statements.** -/
theorem countX3_of (hC : CauseDetStmt) (hSC : SysCauseStmt) (hE : EffDetStmt) (hSE : SysEffStmt)
    (hF : FamBigStmt) (hP : FreshProbStmt) (hR : RetMarkovStmt) (hW : ChebStmt) :
    CountX3Stmt := by
  have hdet := not_badFam_of hC hSC hE hSE hF
  filter_upwards [hdet, hP, hR, hW, eventually_ge_atTop 9000] with N hdet hP hR hW hN
  intro s r0 x σ f hf
  have hsub : {g | glueRows (sensRows s r0) f g ∈ BadFam3 N s r0 x σ} ⊆
      ({g | ¬ CountFreshX N s r0 (glueRows (sensRows s r0) f g)} ∪
        {g | glueRows (sensRows s r0) f g ∈ RetBad N s r0 x σ}) ∪
        {g | glueRows (sensRows s r0) f g ∈ WBad N s r0 x σ} := by
    intro g hg
    by_contra hn
    exact hdet s r0 x σ _ (goodW3_glue hf g) (fun hb => hn hb) hg
  calc rowsOutM (sensRows s r0) {g | glueRows (sensRows s r0) f g ∈ BadFam3 N s r0 x σ}
      ≤ rowsOutM (sensRows s r0) (({g | ¬ CountFreshX N s r0 (glueRows (sensRows s r0) f g)} ∪
          {g | glueRows (sensRows s r0) f g ∈ RetBad N s r0 x σ}) ∪
          {g | glueRows (sensRows s r0) f g ∈ WBad N s r0 x σ}) := measure_mono hsub
    _ ≤ rowsOutM (sensRows s r0) {g | ¬ CountFreshX N s r0 (glueRows (sensRows s r0) f g)} +
          rowsOutM (sensRows s r0) {g | glueRows (sensRows s r0) f g ∈ RetBad N s r0 x σ} +
          rowsOutM (sensRows s r0) {g | glueRows (sensRows s r0) f g ∈ WBad N s r0 x σ} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (Real.exp (-((N : ℝ) / 200))) +
          ENNReal.ofReal (Real.exp (-((N : ℝ) / 40))) +
          ENNReal.ofReal (Real.exp (-((N : ℝ) / 450))) :=
        add_le_add (add_le_add (hP s r0 x σ f hf) (hR s r0 x σ f hf)) (hW s r0 x σ f hf)
    _ = ENNReal.ofReal (Real.exp (-((N : ℝ) / 200)) + Real.exp (-((N : ℝ) / 40)) +
          Real.exp (-((N : ℝ) / 450))) := by
        rw [ENNReal.ofReal_add, ENNReal.ofReal_add] <;> positivity
    _ ≤ ENNReal.ofReal (Real.exp (-(cCnt * N))) := ENNReal.ofReal_le_ofReal (exp_three_le_cCnt hN)

/-- The same, with WP6 given as `MeanYStmt → ChebStmt` and WP5's `MeanYStmt`. -/
theorem countX3_of_wps (hC : CauseDetStmt) (hSC : SysCauseStmt) (hE : EffDetStmt)
    (hSE : SysEffStmt) (hF : FamBigStmt) (hP : FreshProbStmt) (hR : RetMarkovStmt)
    (hMean : MeanYStmt) (hCheb : MeanYStmt → ChebStmt) : CountX3Stmt :=
  countX3_of hC hSC hE hSE hF hP hR (hCheb hMean)

/-- **`B1PhiGoal`** from the work packages, the new rate leaf and the measurability of `NewX`. -/
theorem b1PhiGoal_of_wps (hm : NewX3MeasStmt) (hNew : NewLeaf3Stmt) (hC : CauseDetStmt)
    (hSC : SysCauseStmt) (hE : EffDetStmt) (hSE : SysEffStmt) (hF : FamBigStmt)
    (hP : FreshProbStmt) (hR : RetMarkovStmt) (hMean : MeanYStmt)
    (hCheb : MeanYStmt → ChebStmt) : B1PhiGoal :=
  b1PhiGoal_of_X3 hm hNew (countX3_of_wps hC hSC hE hSE hF hP hR hMean hCheb)

end Census
end IIT

#print axioms IIT.Census.freshProb_of_fields
#print axioms IIT.Census.distOK_of_sides
#print axioms IIT.Census.not_badFam_of
#print axioms IIT.Census.countX3_of
#print axioms IIT.Census.countX3_of_wps
#print axioms IIT.Census.b1PhiGoal_of_wps
#print axioms IIT.Census.goodW3_glue
#print axioms IIT.Census.famX3_glue
#print axioms IIT.Census.mem_famX3_floor
#print axioms IIT.Census.effUnit_flipP_teW
#print axioms IIT.Census.fullProb_flipP
