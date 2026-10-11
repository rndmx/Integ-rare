/-
Census, B1: the new rate leaf of `GoodX2` (`NewLeafStmt`, B1GoodX2), reduced to per-field joint bounds.

* `newXMeas_proved : NewXMeasStmt` (B1NewLeafMeas).
* `joint_pairLow : JointBound P0PairLow` (B1NewLeafPair2): `pairLow` jointly with the cause regime, rate 1.0202.
* `newLeaf_of`: `JointBound P0Floor → JointBound P0X5eExt → NewLeafStmt` (the sum over `(r0, x, σ)` of the three
  joint bounds, `6 N e^{-RJ N} ≤ e^{-RbadX N}`).

OPEN (and NOT provable as the fields are stated in B1GoodX2):
* `JointBound P0Floor`: the regime event does not keep row `r0` away from `1/2` by an exponentially small margin.
  Cause side: cell 0 of `cellsXCauseData` has `m_lo = 0.499999 < 1/2`, so the floor-failure window
  `[0.499999, 1/2 + e^{-N/200})` has width `≈ 10⁻⁶` (no exponential gain); the certified rate of that cell is
  1.007346 and the best continuous-multiplier Chernoff rate of its template is 1.00781 < `RbadX = 1.01`.
  Effect side: `CellEvX`'s floor on row `r0` is `1/2 - deltaU N = 1/2 - 1/(N+1)`; the window
  `[1/2 - 1/(N+1), 1/2 + e^{-N/200})` has width `≈ 1/N` and the tilted law of `r0` has density `≈ 0.53` at `1/2`,
  so one of the `N` entries lands in it with probability `Θ(1)`: the floor failure has the regime's own rate.
* `JointBound P0X5eExt`: `x5e` is evaluated on `b1Ext f` (rows outside `sensRows = ballR r0 4 ∪ ballR s 2` read
  `1`).  For `|K'| = 3`, `x ∉ K'`, four of the seven subcube rows around `s^x` are at distance 3-4 from `s`, hence
  read `1`: `2 meanPlus = (5 + y_a + y_b + y_c)/4`, whose log has mean `≈ 0.4826 > 0.46`.  So `x5e` fails on all but
  an `e^{-cN}` fraction of the regime; the joint bound is false.  With `K'.card ≤ 2` the field is fine
  (`|K'| = 2`: `(2 + y_a + y_b)/2`, `plus2Fail`, rate `1/32`; `|K'| = 1`: `plusFail` with `k = 1`).
-/
import IIT.Census.B1NewLeafMeas
import IIT.Census.B1NewLeafPair2

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- The `floor` field with an explicit anchor row. -/
def P0Floor (N : ℕ) (_s : State N) : State N → Param N → Fin N → XSide → Prop := fun r0 w _ _ =>
  ∀ j, 1 / 2 + Real.exp (-((N : ℝ) / 200)) ≤ clamp01 (w r0 j)

/-- The `x5e` field as `GoodXFail` reads it: on the sensitive rows of `w`, extended by `1`. -/
def P0X5eExt (N : ℕ) (s : State N) : State N → Param N → Fin N → XSide → Prop := fun r0 w x σ =>
  σ = .effect → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 3 → x ∉ K' →
    ∑ i, Real.log (max (2 * b1CutMeanPlus (b1Ext (restrIn (sensRows s r0) w)) (flipAt x s) K' i) 1) ≤
      23 / 50 * (N : ℝ)

lemma nl_r0_mem (s r0 : State N) : r0 ∈ sensRows s r0 :=
  Finset.mem_union_left _ (by simp [ballR, ham_self])

lemma nl_r1_mem (s r0 : State N) (x : Fin N) : flipAt x r0 ∈ sensRows s r0 := by
  refine Finset.mem_union_left _ ?_
  simp only [ballR, Finset.mem_filter, Finset.mem_univ, true_and]
  have := ham_flipAt_le_one x r0; rw [ham_comm] at this; omega

/-- **`GoodXFail` lies in the three per-field failure events** (for far `r0`). -/
theorem goodXFail_sub (s r0 : State N) (x : Fin N) (σ : XSide) :
    {w : Param N | restrIn (sensRows s r0) w ∈ GoodXFail N s r0 x σ} ⊆
      {w | N ≤ 3 * ham r0 s ∧ RegEvX N s r0 x σ w ∧ ¬ P0Floor N s r0 w x σ} ∪
        {w | N ≤ 3 * ham r0 s ∧ RegEvX N s r0 x σ w ∧ ¬ P0PairLow N s r0 w x σ} ∪
          {w | N ≤ 3 * ham r0 s ∧ RegEvX N s r0 x σ w ∧ ¬ P0X5eExt N s r0 w x σ} := by
  intro w hw
  obtain ⟨hg, hn⟩ := hw
  have hE : ∀ r ∈ sensRows s r0, b1Ext (restrIn (sensRows s r0) w) r = w r := by
    intro r hr; rw [← b1Restr_eq_restrIn]; exact b1_Ext_Restr s r0 w r hr
  have hg' : B1FGoodX N s r0 x σ w := (B1FGoodX.congr hE).2 hg
  have h0 := hE r0 (nl_r0_mem s r0)
  have h1 := hE _ (nl_r1_mem s r0 x)
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_and, not_not] at hcon
  obtain ⟨⟨hA, hB⟩, hC⟩ := hcon
  have fA := hA hg'.far hg'.regEv
  have fB := hB hg'.far hg'.regEv
  have fC := hC hg'.far hg'.regEv
  apply hn
  refine ⟨fun j => ?_, fun hσ => ?_, fun hσ => fC hσ⟩
  · rw [h0]; exact fA j
  · obtain ⟨j, hj, hle⟩ := fB hσ
    exact ⟨j, hj, by rw [h0, h1]; exact hle⟩

/-- Absorption: `6 N e^{-RJ N} ≤ e^{-RbadX N}`. -/
lemma nl_absorb : ∀ᶠ N : ℕ in atTop, 6 * (N : ℝ) * Real.exp (-(RJ * N)) ≤ Real.exp (-(RbadX * N)) := by
  have hab := poly_absorb 6 1 (δ := RJ - RbadX) (by unfold RJ RbadX; norm_num)
  filter_upwards [hab, eventually_ge_atTop 1] with N hab hN1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hNr
  have h1 : (1 : ℝ) ≤ Real.exp (4000 + 1400 * Real.log N) := Real.one_le_exp (by positivity)
  have e2 : Real.exp (-(RbadX * N)) = Real.exp ((RJ - RbadX) * N) * Real.exp (-(RJ * N)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e2]
  have hx := Real.exp_pos (-(RJ * N))
  have : 6 * (N : ℝ) ≤ Real.exp ((RJ - RbadX) * N) := by
    refine le_trans ?_ hab
    rw [pow_one]
    nlinarith
  nlinarith

/-- **`NewLeafStmt` from the floor and `x5e` joint bounds** (`pairLow` is `joint_pairLow`). -/
theorem newLeaf_of (hfl : JointBound P0Floor) (hx5 : JointBound P0X5eExt) : NewLeafStmt := by
  filter_upwards [hfl, joint_pairLow, hx5, nl_absorb] with N h1 h2 h3 hab s
  set E : ℝ := Real.exp (-(RJ * N)) / 2 ^ N with hE
  have hE0 : 0 ≤ E := by positivity
  have hpiece : ∀ (r0 : State N) (x : Fin N) (σ : XSide)
      (P : ∀ N, State N → State N → Param N → Fin N → XSide → Prop),
      (∀ (s r0 : State N) (x : Fin N) (σ : XSide), N ≤ 3 * ham r0 s →
        cubeM N {w | RegEvX N s r0 x σ w ∧ ¬ P N s r0 w x σ} ≤ ENNReal.ofReal (Real.exp (-(RJ * N)) / 2 ^ N)) →
      cubeM N {w | N ≤ 3 * ham r0 s ∧ RegEvX N s r0 x σ w ∧ ¬ P N s r0 w x σ} ≤ ENNReal.ofReal E := by
    intro r0 x σ P hP
    by_cases hf : N ≤ 3 * ham r0 s
    · exact le_trans (measure_mono fun w hw => hw.2) (hP s r0 x σ hf)
    · have : {w | N ≤ 3 * ham r0 s ∧ RegEvX N s r0 x σ w ∧ ¬ P N s r0 w x σ} = ∅ :=
        Set.eq_empty_of_forall_notMem fun w hw => hf hw.1
      rw [this, measure_empty]; exact bot_le
  have hterm : ∀ r0 x σ, rowsInM (sensRows s r0) (GoodXFail N s r0 x σ) ≤ ENNReal.ofReal (3 * E) := by
    intro r0 x σ
    rw [← cubeM_restrIn_preimage (sensRows s r0)]
    refine (measure_mono (goodXFail_sub s r0 x σ)).trans ?_
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add (measure_union_le _ _) le_rfl).trans ?_
    calc _ ≤ ENNReal.ofReal E + ENNReal.ofReal E + ENNReal.ofReal E :=
          add_le_add (add_le_add (hpiece r0 x σ P0Floor h1) (hpiece r0 x σ P0PairLow h2))
            (hpiece r0 x σ P0X5eExt h3)
      _ = ENNReal.ofReal (3 * E) := by
          rw [← ENNReal.ofReal_add hE0 hE0, ← ENNReal.ofReal_add (by positivity) hE0]; ring_nf
  calc ∑ r0 : State N, ∑ x : Fin N, ∑ σ : XSide, rowsInM (sensRows s r0) (GoodXFail N s r0 x σ)
      ≤ ∑ _r0 : State N, ∑ _x : Fin N, ∑ _σ : XSide, ENNReal.ofReal (3 * E) :=
        sum_le_sum fun r0 _ => sum_le_sum fun x _ => sum_le_sum fun σ _ => hterm r0 x σ
    _ = ENNReal.ofReal (2 ^ N * N * 2 * (3 * E)) := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show Fintype.card XSide = 2 from rfl, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        rw [ENNReal.ofReal_mul (p := (2 : ℝ) ^ N * N * 2) (by positivity),
          ENNReal.ofReal_mul (p := (2 : ℝ) ^ N * N) (by positivity),
          ENNReal.ofReal_mul (p := (2 : ℝ) ^ N) (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_natCast]
        simp; ring
    _ ≤ ENNReal.ofReal (Real.exp (-(RbadX * N))) := by
        apply ENNReal.ofReal_le_ofReal
        have e1 : 2 ^ N * N * 2 * (3 * E) = 6 * N * Real.exp (-(RJ * N)) := by
          rw [hE]; field_simp; ring
        rw [e1]; exact hab

end Census
end IIT

#print axioms IIT.Census.newXMeas_proved
#print axioms IIT.Census.joint_pairLow
#print axioms IIT.Census.newLeaf_of
