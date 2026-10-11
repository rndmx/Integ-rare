/-
Census, B1: **`b1PhiGoal` from the three remaining statements** (W12), with no `sorry`:
`NatTier3Rest6Stmt (1039/1000)`, `NatLT3HuStmt λ_u (103/100)` and the count `count_exp_famX` (as a hypothesis).
Copies the transfer and the final limit of `B1Skeleton.lean` with the skeleton's `sorry` leaves replaced by
`B1_lowerX_final`, `B1_forcedX_of_nat` and `count_package_of ∘ count_exp_mech_of`.
-/
import IIT.Census.B1ForcedFinal2
import IIT.Census.B1CountSkel
import IIT.Census.B1Final

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

theorem small_B1_le_X_of
    (hCP : ∀ᶠ N in atTop, ∀ s : State N,
      ∃ Bad : State N → Fin N → XSide → Set (Param N),
        (∀ r0 x σ, MeasurableSet (Bad r0 x σ)) ∧
        (∀ r0 x σ (w : Param N), restrIn (sensRows s r0) w ∈ GoodFX N s r0 x σ →
          w ∉ Bad r0 x σ → w ∉ SmallW N s) ∧
        (∀ r0 x σ, ∀ f ∈ GoodFX N s r0 x σ,
          rowsOutM (sensRows s r0) {g | glueRows (sensRows s r0) f g ∈ Bad r0 x σ}
            ≤ ENNReal.ofReal (Real.exp (-(cCnt * N))))) :
    ∀ᶠ N in atTop, ∀ s : State N,
    cubeM N (SmallW N s ∩ B1w N s) ≤
      cubeM N (B1w N s \ {w | ForcedX N s w}) + ENNReal.ofReal (Real.exp (-(Rcnt * N))) := by
  filter_upwards [goodFX_rate', hCP] with N hRS hCnt s
  obtain ⟨Bad, hmeas, hdet, hexp⟩ := hCnt s
  set piece : State N → Fin N → XSide → Set (Param N) := fun r0 x σ =>
    Bad r0 x σ ∩ {w | restrIn (sensRows s r0) w ∈ GoodFX N s r0 x σ}
  have hsub : SmallW N s ∩ B1w N s ⊆
      (B1w N s \ {w | ForcedX N s w}) ∪ ⋃ r0 : State N, ⋃ x : Fin N, ⋃ σ : XSide, piece r0 x σ := by
    rintro w ⟨hS, hB⟩
    by_cases hF : ForcedX N s w
    · right
      obtain ⟨x, σ, hg⟩ := forcedX_restr hF
      simp only [Set.mem_iUnion]
      refine ⟨tcRow w, x, σ, ?_, hg⟩
      by_contra hnot
      exact hdet _ x σ w hg hnot hS
    · exact Or.inl ⟨hB, hF⟩
  have hpiece : ∀ r0 x σ, cubeM N (piece r0 x σ) ≤
      ENNReal.ofReal (Real.exp (-(cCnt * N))) * rowsInM (sensRows s r0) (GoodFX N s r0 x σ) :=
    fun r0 x σ => cubeM_inter_restrIn_le (sensRows s r0) (hmeas r0 x σ) measurableSet_goodFX
      (hexp r0 x σ)
  calc cubeM N (SmallW N s ∩ B1w N s)
      ≤ cubeM N ((B1w N s \ {w | ForcedX N s w}) ∪
          ⋃ r0 : State N, ⋃ x : Fin N, ⋃ σ : XSide, piece r0 x σ) := measure_mono hsub
    _ ≤ cubeM N (B1w N s \ {w | ForcedX N s w}) +
          cubeM N (⋃ r0 : State N, ⋃ x : Fin N, ⋃ σ : XSide, piece r0 x σ) := measure_union_le _ _
    _ ≤ cubeM N (B1w N s \ {w | ForcedX N s w}) +
          ∑ r0 : State N, ∑ x : Fin N, ∑ σ : XSide, cubeM N (piece r0 x σ) := by
        gcongr
        refine (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun r0 _ => ?_)
        refine (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun x _ => ?_)
        exact measure_iUnion_fintype_le _ _
    _ ≤ cubeM N (B1w N s \ {w | ForcedX N s w}) +
          ∑ r0 : State N, ∑ x : Fin N, ∑ σ : XSide,
            ENNReal.ofReal (Real.exp (-(cCnt * N))) * rowsInM (sensRows s r0) (GoodFX N s r0 x σ) := by
        gcongr with r0 _ x _ σ _
        exact hpiece r0 x σ
    _ = cubeM N (B1w N s \ {w | ForcedX N s w}) +
          ENNReal.ofReal (Real.exp (-(cCnt * N))) *
            ∑ r0 : State N, ∑ x : Fin N, ∑ σ : XSide, rowsInM (sensRows s r0) (GoodFX N s r0 x σ) := by
        simp only [mul_sum]
    _ ≤ cubeM N (B1w N s \ {w | ForcedX N s w}) +
          ENNReal.ofReal (Real.exp (-(cCnt * N))) * ENNReal.ofReal (Real.exp (-(RXf * N))) := by
        gcongr
        exact hRS s
    _ = cubeM N (B1w N s \ {w | ForcedX N s w}) + ENNReal.ofReal (Real.exp (-(Rcnt * N))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 3
        unfold Rcnt cCnt RXf; ring

theorem b1PhiGoal_of_leaves {lamU : ℝ} (hl : 0 < lamU) (hRest6 : NatTier3Rest6Stmt (1039 / 1000))
    (hHu : NatLT3HuStmt lamU (103 / 100))
    (hfam : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide),
      ∀ f ∈ GoodFX N s r0 x σ,
        rowsOutM (sensRows s r0) {g | glueRows (sensRows s r0) f g ∈ BadFam N s r0 x σ}
          ≤ ENNReal.ofReal (Real.exp (-(cCnt * N)))) : B1PhiGoal := by
  intro s
  have ha : (0 : ℝ) < RbadX - RLBX := by unfold RbadX RLBX; norm_num
  have hb : (0 : ℝ) < Rcnt - RLBX := by unfold Rcnt RLBX; norm_num
  -- the upper envelope tends to 0
  have hlim : Tendsto (fun N : ℕ => 3 * Real.exp (-((RbadX - RLBX) * N)) +
      Real.exp (-((Rcnt - RLBX) * N))) atTop (𝓝 0) := by
    have h1 : ∀ c : ℝ, 0 < c → Tendsto (fun N : ℕ => Real.exp (-(c * N))) atTop (𝓝 0) := by
      intro c hc
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
    simpa using ((h1 _ ha).const_mul 3).add (h1 _ hb)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun N => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) ?_
  filter_upwards [B1_lowerX_final, B1_forcedX_of_nat hl hRest6 hHu,
    small_B1_le_X_of (count_package_of (count_exp_mech_of hfam))] with N hLB hF hT
  rw [← cubeM_SmallW_inter, ← cubeM_B1w]
  set D := (cubeM N (B1w N (s N))).toReal
  have hD : 0 < D := lt_of_lt_of_le (Real.exp_pos _) (hLB (s N))
  have hnum : (cubeM N (SmallW N (s N) ∩ B1w N (s N))).toReal ≤
      3 * Real.exp (-(RbadX * N)) + Real.exp (-(Rcnt * N)) := by
    have h := (hT (s N)).trans (add_le_add (hF (s N)) le_rfl)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at h
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
  rw [div_le_iff₀ hD]
  have hLB' := hLB (s N)
  have e1 : 3 * Real.exp (-((RbadX - RLBX) * N)) * Real.exp (-(RLBX * N)) =
      3 * Real.exp (-(RbadX * N)) := by
    rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have e2 : Real.exp (-((Rcnt - RLBX) * N)) * Real.exp (-(RLBX * N)) = Real.exp (-(Rcnt * N)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc (cubeM N (SmallW N (s N) ∩ B1w N (s N))).toReal
      ≤ 3 * Real.exp (-(RbadX * N)) + Real.exp (-(Rcnt * N)) := hnum
    _ = (3 * Real.exp (-((RbadX - RLBX) * N)) + Real.exp (-((Rcnt - RLBX) * N))) *
          Real.exp (-(RLBX * N)) := by rw [add_mul, e1, e2]
    _ ≤ (3 * Real.exp (-((RbadX - RLBX) * N)) + Real.exp (-((Rcnt - RLBX) * N))) * D :=
        mul_le_mul_of_nonneg_left hLB' (by positivity)

end Census
end IIT
