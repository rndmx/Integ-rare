/-
Census, B1: the corrected good F-data `GoodX3` and family `famX3` (supersedes `B1GoodX2`).

The leaf agent (B1NewLeaf*.lean) found: a pointwise floor on row `r0` is NOT rate-excludable (cause cell 0 has
`m_lo = 0.499999`; effect `CellEvX` floor is `1/2 - deltaU`), and `x5e` at `|K'| = 3` is false on `b1Ext`.
Fix: the low units `lowU = {j | y_{r0,j} < 1/2 + e^{-N/200}}` are put into every counted `K` (`famX3`), and the
F-fields (`NewX3`) are: few low units (`≤ N/1000`), `pairLow` with a non-low witness, `x5e` at `|K'| ≤ 2`.
Any family works for the transfer (`badMech_subset_badFam3`).
-/
import IIT.Census.B1GoodX2

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

open scoped Classical

/-- The low units of row `r0`. -/
noncomputable def lowU (N : ℕ) (w : Param N) (r0 : State N) : Finset (Fin N) := by
  classical exact univ.filter fun j => clamp01 (w r0 j) < 1 / 2 + Real.exp (-((N : ℝ) / 200))

/-- The three new F-fields. -/
structure NewX3 (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N) : Prop where
  lowFew : 1000 * (lowU N w r0).card ≤ N
  pairLow : σ = .cause → ∃ j, j ≠ x ∧ 1 / 2 + Real.exp (-((N : ℝ) / 200)) ≤ clamp01 (w r0 j) ∧
      clamp01 (w r0 j) + clamp01 (w (flipAt x r0) j) ≤ 1 - 1 / (N : ℝ)
  x5e : σ = .effect → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 2 → x ∉ K' →
      ∑ i, Real.log (max (2 * b1CutMeanPlus w (flipAt x s) K' i) 1) ≤ 23 / 50 * (N : ℝ)

/-- The counted family: `dX`-sets containing every low unit, the rest in `NegX` (cause) or anywhere (effect). -/
noncomputable def famX3 (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N) :
    Finset (Finset (Fin N)) := by
  classical exact
  match σ with
  | .cause => ((NegX w r0 x ∪ lowU N w r0).powersetCard (dX N)).filter fun K => lowU N w r0 ⊆ K
  | .effect => ((univ : Finset (Fin N)).powersetCard (dX N)).filter fun K => lowU N w r0 ⊆ K

/-- The bad set of the count over `famX3`. -/
def BadFam3 (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) : Set (Param N) :=
  {w | ((famX3 N s r0 x σ w).filter fun K => DistOK s r0 w (univ \ K)).card < LCnt N}

theorem badMech_subset_badFam3 (s r0 : State N) (x : Fin N) (σ : XSide) :
    BadMech N s ⊆ BadFam3 N s r0 x σ := by
  intro w hw
  have h1 := hw r0
  show ((famX3 N s r0 x σ w).filter fun K => DistOK s r0 w (univ \ K)).card < LCnt N
  refine lt_of_le_of_lt ?_ h1
  have hinj : Function.Injective fun K : Finset (Fin N) => univ \ K := by
    intro K K' hKK'
    have := congrArg (fun A : Finset (Fin N) => univ \ A) hKK'
    simpa [Finset.sdiff_sdiff_eq_self (subset_univ _)] using this
  rw [← card_image_of_injective _ hinj]
  refine card_le_card fun M hM => ?_
  obtain ⟨K, hK, rfl⟩ := mem_image.1 hM
  exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hK).2⟩

/-- The strengthened good set. -/
def GoodX3 (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) : Set (sensRows s r0 → Fin N → ℝ) :=
  {f | B1FGoodX N s r0 x σ (b1Ext f) ∧ NewX3 N s r0 x σ (b1Ext f)}

/-- Good F-data failing a new field. -/
def GoodX3Fail (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) : Set (sensRows s r0 → Fin N → ℝ) :=
  {f | B1FGoodX N s r0 x σ (b1Ext f) ∧ ¬ NewX3 N s r0 x σ (b1Ext f)}

/-- **The new rate leaf**. -/
def NewLeaf3Stmt : Prop :=
  ∀ᶠ N in atTop, ∀ s : State N,
    ∑ r0 : State N, ∑ x : Fin N, ∑ σ : XSide, rowsInM (sensRows s r0) (GoodX3Fail N s r0 x σ)
      ≤ ENNReal.ofReal (Real.exp (-(RbadX * N)))

/-- **The corrected count.** -/
def CountX3Stmt : Prop :=
  ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide),
    ∀ f ∈ GoodX3 N s r0 x σ,
      rowsOutM (sensRows s r0) {g | glueRows (sensRows s r0) f g ∈ BadFam3 N s r0 x σ}
        ≤ ENNReal.ofReal (Real.exp (-(cCnt * N)))

/-- Measurability of the new fields. -/
def NewX3MeasStmt : Prop :=
  ∀ (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide), MeasurableSet {w : Param N | NewX3 N s r0 x σ w}

theorem measurableSet_goodX3 (hm : NewX3MeasStmt) {s r0 : State N} {x : Fin N} {σ : XSide} :
    MeasurableSet (GoodX3 N s r0 x σ) := by
  have e : GoodX3 N s r0 x σ = GoodFX N s r0 x σ ∩ {f | NewX3 N s r0 x σ (b1Ext f)} := rfl
  rw [e]
  exact measurableSet_goodFX.inter (b1_measurable_Ext s r0 (hm N s r0 x σ))

theorem goodX3_sub (s r0 : State N) (x : Fin N) (σ : XSide) : GoodX3 N s r0 x σ ⊆ GoodFX N s r0 x σ :=
  fun _ h => h.1

lemma measurableSet_mem_lowU (r0 : State N) (j : Fin N) : MeasurableSet {w : Param N | j ∈ lowU N w r0} := by
  have e : {w : Param N | j ∈ lowU N w r0} = {w | clamp01 (w r0 j) < 1 / 2 + Real.exp (-((N : ℝ) / 200))} := by
    ext w; simp [lowU]
  rw [e]
  exact measurableSet_lt (b1m_clamp r0 j) measurable_const

lemma measurableSet_lowU_sub (r0 : State N) (K : Finset (Fin N)) :
    MeasurableSet {w : Param N | lowU N w r0 ⊆ K} := by
  have e : {w : Param N | lowU N w r0 ⊆ K} = ⋂ j ∈ (univ \ K), {w | j ∈ lowU N w r0}ᶜ := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
    constructor
    · intro h j hj hl
      exact (mem_sdiff.1 hj).2 (h hl)
    · intro h j hl
      by_contra hj
      exact h j (mem_sdiff.2 ⟨mem_univ _, hj⟩) hl
  rw [e]
  exact Finset.measurableSet_biInter _ fun j _ => (measurableSet_mem_lowU r0 j).compl

lemma measurableSet_mem_famX3 (s r0 : State N) (x : Fin N) (σ : XSide) (K : Finset (Fin N)) :
    MeasurableSet {w : Param N | K ∈ famX3 N s r0 x σ w} := by
  cases σ with
  | cause =>
    have e : {w : Param N | K ∈ famX3 N s r0 x .cause w} =
        (⋂ j ∈ K, ({w : Param N | j ∈ NegX w r0 x} ∪ {w | j ∈ lowU N w r0})) ∩ {_w | K.card = dX N} ∩
          {w | lowU N w r0 ⊆ K} := by
      ext w
      simp only [famX3, mem_filter, mem_powersetCard, mem_union, Set.mem_setOf_eq, Set.mem_inter_iff,
        Set.mem_iInter, Set.mem_union]
      exact ⟨fun h => ⟨⟨fun j hj => mem_union.1 (h.1.1 hj), h.1.2⟩, h.2⟩,
        fun h => ⟨⟨fun j hj => mem_union.2 (h.1.1 j hj), h.1.2⟩, h.2⟩⟩
    rw [e]
    exact ((Finset.measurableSet_biInter K fun j _ =>
      (b1mx_measurableSet_mem_NegX r0 x j).union (measurableSet_mem_lowU r0 j)).inter
      (MeasurableSet.const _)).inter (measurableSet_lowU_sub r0 K)
  | effect =>
    have e : {w : Param N | K ∈ famX3 N s r0 x .effect w} = {_w | K.card = dX N} ∩ {w | lowU N w r0 ⊆ K} := by
      ext w
      simp [famX3, mem_filter, mem_powersetCard]
    rw [e]
    exact (MeasurableSet.const _).inter (measurableSet_lowU_sub r0 K)

theorem measurableSet_BadFam3 (s r0 : State N) (x : Fin N) (σ : XSide) :
    MeasurableSet (BadFam3 N s r0 x σ) := by
  classical
  have e : BadFam3 N s r0 x σ = {w | LCnt N ≤ (univ.filter fun K : Finset (Fin N) =>
      K ∈ famX3 N s r0 x σ w ∧ DistOK s r0 w (univ \ K)).card}ᶜ := by
    ext w
    simp only [BadFam3, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [show (famX3 N s r0 x σ w).filter (fun K => DistOK s r0 w (univ \ K)) =
      univ.filter fun K => K ∈ famX3 N s r0 x σ w ∧ DistOK s r0 w (univ \ K) by
      ext K; simp]
  rw [e]
  refine (b1_measurableSet_card_filter_ge (P := fun w K => K ∈ famX3 N s r0 x σ w ∧ DistOK s r0 w (univ \ K))
    (fun K => (measurableSet_mem_famX3 s r0 x σ K).inter (measurableSet_DistOK s r0 (univ \ K))) _).compl

/-- **Transfer through `GoodX3`.** -/
theorem small_B1_le_X3_of (hm : NewX3MeasStmt) (hNew : NewLeaf3Stmt) (hcnt : CountX3Stmt) :
    ∀ᶠ N in atTop, ∀ s : State N,
    cubeM N (SmallW N s ∩ B1w N s) ≤
      cubeM N (B1w N s \ {w | ForcedX N s w}) + ENNReal.ofReal (Real.exp (-(RbadX * N))) +
        ENNReal.ofReal (Real.exp (-(Rcnt * N))) := by
  filter_upwards [goodFX_rate', hNew, hcnt, eventually_ge_atTop 1] with N hRS hNw hC hN1 s
  set piece : State N → Fin N → XSide → Set (Param N) := fun r0 x σ =>
    BadFam3 N s r0 x σ ∩ {w | restrIn (sensRows s r0) w ∈ GoodX3 N s r0 x σ}
  set fail : State N → Fin N → XSide → Set (Param N) := fun r0 x σ =>
    {w | restrIn (sensRows s r0) w ∈ GoodX3Fail N s r0 x σ}
  have hsub : SmallW N s ∩ B1w N s ⊆ (B1w N s \ {w | ForcedX N s w}) ∪
      ((⋃ r0 : State N, ⋃ x : Fin N, ⋃ σ : XSide, fail r0 x σ) ∪
        ⋃ r0 : State N, ⋃ x : Fin N, ⋃ σ : XSide, piece r0 x σ) := by
    rintro w ⟨hS, hB⟩
    by_cases hF : ForcedX N s w
    · right
      obtain ⟨x, σ, hg⟩ := forcedX_restr hF
      by_cases hn : NewX3 N s (tcRow w) x σ (b1Ext (restrIn (sensRows s (tcRow w)) w))
      · right
        simp only [Set.mem_iUnion]
        refine ⟨tcRow w, x, σ, ?_, ⟨hg, hn⟩⟩
        by_contra hnot
        exact notSmall_of_not_badMech hN1
          (fun hb => hnot (badMech_subset_badFam3 s (tcRow w) x σ hb)) hS
      · left
        simp only [Set.mem_iUnion]
        exact ⟨tcRow w, x, σ, hg, hn⟩
    · exact Or.inl ⟨hB, hF⟩
  have hpiece : ∀ r0 x σ, cubeM N (piece r0 x σ) ≤
      ENNReal.ofReal (Real.exp (-(cCnt * N))) * rowsInM (sensRows s r0) (GoodX3 N s r0 x σ) :=
    fun r0 x σ => cubeM_inter_restrIn_le (sensRows s r0) (measurableSet_BadFam3 s r0 x σ)
      (measurableSet_goodX3 hm) (hC s r0 x σ)
  have hfail : ∀ r0 x σ, cubeM N (fail r0 x σ) = rowsInM (sensRows s r0) (GoodX3Fail N s r0 x σ) :=
    fun r0 x σ => cubeM_restrIn_preimage (sensRows s r0) _
  have hX3le : ∀ r0 x σ, rowsInM (sensRows s r0) (GoodX3 N s r0 x σ) ≤
      rowsInM (sensRows s r0) (GoodFX N s r0 x σ) := fun r0 x σ => measure_mono (goodX3_sub s r0 x σ)
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
        · exact (hpiece r0 x σ).trans (mul_le_mul' le_rfl (hX3le r0 x σ))
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
theorem b1PhiGoal_of_X3 (hm : NewX3MeasStmt) (hNew : NewLeaf3Stmt) (hcnt : CountX3Stmt) : B1PhiGoal := by
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
    small_B1_le_X3_of hm hNew hcnt] with N hLB hF hT
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
