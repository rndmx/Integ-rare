/-
Census, B1: the strengthened good F-data `GoodX2` (W12 §9, W13 audits) and the transfer through it.

`count_exp_famX` is false for `GoodFX` (W12 §9: a row-`r0` entry just below `1/2` kills `φ_c(univ, r0)`; the
competitor purview `U \ {x}` beats any exponential floor). `GoodX2` adds three F-fields (`NewX`):
* `floor`: every entry of row `r0` is `≥ 1/2 + e^{-N/200}`;
* `pairLow` (cause side): some unit `j ≠ x` has `y_{r0,j} + y_{r1,j} ≤ 1 - 1/N` (kills `φ_c(U \ {x})`);
* `x5e` (effect side): `x5` mirrored at the row `s^x`.
Their failure jointly with the regime event is a new rate leaf (`NewLeafStmt`, rate `RbadX`), and the count is
restated over `GoodX2` (`CountX2Stmt`). `b1PhiGoal_of_X2` assembles `B1PhiGoal` from these two statements.
-/
import IIT.Census.B1HuFinal

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- The three new F-fields. -/
structure NewX (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N) : Prop where
  floor : ∀ j, 1 / 2 + Real.exp (-((N : ℝ) / 200)) ≤ clamp01 (w r0 j)
  pairLow : σ = .cause → ∃ j, j ≠ x ∧ clamp01 (w r0 j) + clamp01 (w (flipAt x r0) j) ≤ 1 - 1 / (N : ℝ)
  x5e : σ = .effect → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 3 → x ∉ K' →
      ∑ i, Real.log (max (2 * b1CutMeanPlus w (flipAt x s) K' i) 1) ≤ 23 / 50 * (N : ℝ)

/-- The strengthened good set. -/
def GoodX2 (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) : Set (sensRows s r0 → Fin N → ℝ) :=
  {f | B1FGoodX N s r0 x σ (b1Ext f) ∧ NewX N s r0 x σ (b1Ext f)}

/-- The set of F-data that are good but fail a new field. -/
def GoodXFail (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) : Set (sensRows s r0 → Fin N → ℝ) :=
  {f | B1FGoodX N s r0 x σ (b1Ext f) ∧ ¬ NewX N s r0 x σ (b1Ext f)}

/-- **The new rate leaf**: the new fields fail jointly with `GoodFX` at rate `RbadX`. -/
def NewLeafStmt : Prop :=
  ∀ᶠ N in atTop, ∀ s : State N,
    ∑ r0 : State N, ∑ x : Fin N, ∑ σ : XSide, rowsInM (sensRows s r0) (GoodXFail N s r0 x σ)
      ≤ ENNReal.ofReal (Real.exp (-(RbadX * N)))

/-- **The count over `GoodX2`** (the corrected `count_exp_famX`). -/
def CountX2Stmt : Prop :=
  ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide),
    ∀ f ∈ GoodX2 N s r0 x σ,
      rowsOutM (sensRows s r0) {g | glueRows (sensRows s r0) f g ∈ BadFam N s r0 x σ}
        ≤ ENNReal.ofReal (Real.exp (-(cCnt * N)))

/-- Measurability of the new fields (as a hypothesis-free statement on `Param N`). -/
def NewXMeasStmt : Prop :=
  ∀ (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide), MeasurableSet {w : Param N | NewX N s r0 x σ w}

theorem measurableSet_goodX2 (hm : NewXMeasStmt) {s r0 : State N} {x : Fin N} {σ : XSide} :
    MeasurableSet (GoodX2 N s r0 x σ) := by
  have e : GoodX2 N s r0 x σ = GoodFX N s r0 x σ ∩ {f | NewX N s r0 x σ (b1Ext f)} := rfl
  rw [e]
  exact measurableSet_goodFX.inter (b1_measurable_Ext s r0 (hm N s r0 x σ))

theorem goodX2_sub (s r0 : State N) (x : Fin N) (σ : XSide) : GoodX2 N s r0 x σ ⊆ GoodFX N s r0 x σ :=
  fun _ h => h.1

/-- Membership in `famX` is measurable. -/
lemma measurableSet_mem_famX (s r0 : State N) (x : Fin N) (σ : XSide) (K : Finset (Fin N)) :
    MeasurableSet {w : Param N | K ∈ famX N s r0 x σ w} := by
  cases σ with
  | cause =>
    have e : {w : Param N | K ∈ famX N s r0 x .cause w} =
        (⋂ j ∈ K, {w : Param N | j ∈ NegX w r0 x}) ∩ {_w | K.card = dX N} := by
      ext w
      simp only [famX, mem_powersetCard, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      exact ⟨fun h => ⟨fun j hj => h.1 hj, h.2⟩, fun h => ⟨fun j hj => h.1 j hj, h.2⟩⟩
    rw [e]
    exact (Finset.measurableSet_biInter K fun j _ => b1mx_measurableSet_mem_NegX r0 x j).inter
      (MeasurableSet.const _)
  | effect => exact MeasurableSet.const _

theorem measurableSet_BadFam (s r0 : State N) (x : Fin N) (σ : XSide) :
    MeasurableSet (BadFam N s r0 x σ) := by
  classical
  have e : BadFam N s r0 x σ = {w | LCnt N ≤ (univ.filter fun K : Finset (Fin N) =>
      K ∈ famX N s r0 x σ w ∧ DistOK s r0 w (univ \ K)).card}ᶜ := by
    ext w
    simp only [BadFam, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [show (famX N s r0 x σ w).filter (fun K => DistOK s r0 w (univ \ K)) =
      univ.filter fun K => K ∈ famX N s r0 x σ w ∧ DistOK s r0 w (univ \ K) by
      ext K; simp]
  rw [e]
  refine (b1_measurableSet_card_filter_ge (P := fun w K => K ∈ famX N s r0 x σ w ∧ DistOK s r0 w (univ \ K))
    (fun K => (measurableSet_mem_famX s r0 x σ K).inter (measurableSet_DistOK s r0 (univ \ K))) _).compl

/-- **Transfer through `GoodX2`.** -/
theorem small_B1_le_X2_of (hm : NewXMeasStmt) (hNew : NewLeafStmt) (hcnt : CountX2Stmt) :
    ∀ᶠ N in atTop, ∀ s : State N,
    cubeM N (SmallW N s ∩ B1w N s) ≤
      cubeM N (B1w N s \ {w | ForcedX N s w}) + ENNReal.ofReal (Real.exp (-(RbadX * N))) +
        ENNReal.ofReal (Real.exp (-(Rcnt * N))) := by
  filter_upwards [goodFX_rate', hNew, hcnt, eventually_ge_atTop 1] with N hRS hNw hC hN1 s
  set piece : State N → Fin N → XSide → Set (Param N) := fun r0 x σ =>
    BadFam N s r0 x σ ∩ {w | restrIn (sensRows s r0) w ∈ GoodX2 N s r0 x σ}
  set fail : State N → Fin N → XSide → Set (Param N) := fun r0 x σ =>
    {w | restrIn (sensRows s r0) w ∈ GoodXFail N s r0 x σ}
  have hsub : SmallW N s ∩ B1w N s ⊆ (B1w N s \ {w | ForcedX N s w}) ∪
      ((⋃ r0 : State N, ⋃ x : Fin N, ⋃ σ : XSide, fail r0 x σ) ∪
        ⋃ r0 : State N, ⋃ x : Fin N, ⋃ σ : XSide, piece r0 x σ) := by
    rintro w ⟨hS, hB⟩
    by_cases hF : ForcedX N s w
    · right
      obtain ⟨x, σ, hg⟩ := forcedX_restr hF
      by_cases hn : NewX N s (tcRow w) x σ (b1Ext (restrIn (sensRows s (tcRow w)) w))
      · right
        simp only [Set.mem_iUnion]
        refine ⟨tcRow w, x, σ, ?_, ⟨hg, hn⟩⟩
        by_contra hnot
        exact notSmall_of_not_badMech hN1
          (fun hb => hnot (badMech_subset_badFam s (tcRow w) x σ hb)) hS
      · left
        simp only [Set.mem_iUnion]
        exact ⟨tcRow w, x, σ, hg, hn⟩
    · exact Or.inl ⟨hB, hF⟩
  have hpiece : ∀ r0 x σ, cubeM N (piece r0 x σ) ≤
      ENNReal.ofReal (Real.exp (-(cCnt * N))) * rowsInM (sensRows s r0) (GoodX2 N s r0 x σ) :=
    fun r0 x σ => cubeM_inter_restrIn_le (sensRows s r0) (measurableSet_BadFam s r0 x σ)
      (measurableSet_goodX2 hm) (hC s r0 x σ)
  have hfail : ∀ r0 x σ, cubeM N (fail r0 x σ) = rowsInM (sensRows s r0) (GoodXFail N s r0 x σ) :=
    fun r0 x σ => cubeM_restrIn_preimage (sensRows s r0) _
  have hX2le : ∀ r0 x σ, rowsInM (sensRows s r0) (GoodX2 N s r0 x σ) ≤
      rowsInM (sensRows s r0) (GoodFX N s r0 x σ) := fun r0 x σ => measure_mono (goodX2_sub s r0 x σ)
  calc cubeM N (SmallW N s ∩ B1w N s)
      ≤ cubeM N (B1w N s \ {w | ForcedX N s w}) +
          (cubeM N (⋃ r0 : State N, ⋃ x : Fin N, ⋃ σ : XSide, fail r0 x σ) +
            cubeM N (⋃ r0 : State N, ⋃ x : Fin N, ⋃ σ : XSide, piece r0 x σ)) :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _)))
    _ ≤ cubeM N (B1w N s \ {w | ForcedX N s w}) +
          (∑ r0 : State N, ∑ x : Fin N, ∑ σ : XSide, cubeM N (fail r0 x σ) +
            ∑ r0 : State N, ∑ x : Fin N, ∑ σ : XSide, cubeM N (piece r0 x σ)) := by
        gcongr
        · refine (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun r0 _ => ?_)
          refine (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun x _ => ?_)
          exact measure_iUnion_fintype_le _ _
        · refine (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun r0 _ => ?_)
          refine (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun x _ => ?_)
          exact measure_iUnion_fintype_le _ _
    _ ≤ cubeM N (B1w N s \ {w | ForcedX N s w}) +
          (ENNReal.ofReal (Real.exp (-(RbadX * N))) +
            ∑ r0 : State N, ∑ x : Fin N, ∑ σ : XSide,
              ENNReal.ofReal (Real.exp (-(cCnt * N))) * rowsInM (sensRows s r0) (GoodFX N s r0 x σ)) := by
        gcongr
        · simp only [hfail]; exact hNw s
        · exact (hpiece r0 x σ).trans (mul_le_mul' le_rfl (hX2le r0 x σ))
    _ = cubeM N (B1w N s \ {w | ForcedX N s w}) +
          (ENNReal.ofReal (Real.exp (-(RbadX * N))) + ENNReal.ofReal (Real.exp (-(cCnt * N))) *
            ∑ r0 : State N, ∑ x : Fin N, ∑ σ : XSide, rowsInM (sensRows s r0) (GoodFX N s r0 x σ)) := by
        simp only [mul_sum]
    _ ≤ cubeM N (B1w N s \ {w | ForcedX N s w}) +
          (ENNReal.ofReal (Real.exp (-(RbadX * N))) +
            ENNReal.ofReal (Real.exp (-(cCnt * N))) * ENNReal.ofReal (Real.exp (-(RXf * N)))) := by
        gcongr
        exact hRS s
    _ = cubeM N (B1w N s \ {w | ForcedX N s w}) + ENNReal.ofReal (Real.exp (-(RbadX * N))) +
          ENNReal.ofReal (Real.exp (-(Rcnt * N))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_assoc]
        congr 4
        unfold Rcnt cCnt RXf; ring

/-- **`B1PhiGoal` from the new rate leaf and the corrected count.** -/
theorem b1PhiGoal_of_X2 (hm : NewXMeasStmt) (hNew : NewLeafStmt) (hcnt : CountX2Stmt) : B1PhiGoal := by
  intro s
  have ha : (0 : ℝ) < RbadX - RLBX := by unfold RbadX RLBX; norm_num
  have hb : (0 : ℝ) < Rcnt - RLBX := by unfold Rcnt RLBX; norm_num
  have hlim : Tendsto (fun N : ℕ => 4 * Real.exp (-((RbadX - RLBX) * N)) +
      Real.exp (-((Rcnt - RLBX) * N))) atTop (𝓝 0) := by
    have h1 : ∀ c : ℝ, 0 < c → Tendsto (fun N : ℕ => Real.exp (-(c * N))) atTop (𝓝 0) := by
      intro c hc
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
    simpa using ((h1 _ ha).const_mul 4).add (h1 _ hb)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun N => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) ?_
  filter_upwards [B1_lowerX_final, B1_forcedX_of_nat one_pos natTier3Rest6_proved HuFinal.natLT3Hu_proved,
    small_B1_le_X2_of hm hNew hcnt] with N hLB hF hT
  rw [← cubeM_SmallW_inter, ← cubeM_B1w]
  set D := (cubeM N (B1w N (s N))).toReal
  have hD : 0 < D := lt_of_lt_of_le (Real.exp_pos _) (hLB (s N))
  have hnum : (cubeM N (SmallW N (s N) ∩ B1w N (s N))).toReal ≤
      4 * Real.exp (-(RbadX * N)) + Real.exp (-(Rcnt * N)) := by
    have h := (hT (s N)).trans (add_le_add (add_le_add (hF (s N)) le_rfl) le_rfl)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)] at h
    refine (ENNReal.toReal_le_of_le_ofReal (by positivity) h).trans (le_of_eq ?_)
    ring
  rw [div_le_iff₀ hD]
  have hLB' := hLB (s N)
  have e1 : 4 * Real.exp (-((RbadX - RLBX) * N)) * Real.exp (-(RLBX * N)) =
      4 * Real.exp (-(RbadX * N)) := by
    rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have e2 : Real.exp (-((Rcnt - RLBX) * N)) * Real.exp (-(RLBX * N)) = Real.exp (-(Rcnt * N)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc (cubeM N (SmallW N (s N) ∩ B1w N (s N))).toReal
      ≤ 4 * Real.exp (-(RbadX * N)) + Real.exp (-(Rcnt * N)) := hnum
    _ = (4 * Real.exp (-((RbadX - RLBX) * N)) + Real.exp (-((Rcnt - RLBX) * N))) *
          Real.exp (-(RLBX * N)) := by rw [add_mul, e1, e2]
    _ ≤ (4 * Real.exp (-((RbadX - RLBX) * N)) + Real.exp (-((Rcnt - RLBX) * N))) * D :=
        mul_le_mul_of_nonneg_left hLB' (by positivity)

end Census
end IIT
