/-
Census of complexes: the good event `GoodW` has probability tending to one.

The complement of `GoodW N s` is contained in the union of the ten part-failure sets; each has
`cubeM`-probability at most an explicit function of `N` tending to `0`, so the union bound gives
`cubeM N {w | ¬ GoodW N (s N) w} → 0` for every sequence of states `s`.
-/
import IIT.Census.BigPhiProbBasic
import IIT.Census.BigPhiProbSub
import IIT.Census.BigPhiProbCond

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

noncomputable section

variable {N : ℕ}

/-- The complement of the good event is covered by the ten part-failure sets, so its probability is
at most the sum of their probabilities. -/
theorem cubeM_notGood_le (s : State N) :
    cubeM N {w | ¬ GoodW N s w} ≤
      cubeM N {w | ¬ ∀ i r, Qw w i r ≤ tauN N}
      + cubeM N {w | ¬ (1 / 2 ≤ Zs w ∧ Zs w ≤ 2 ∧ ∀ i, ZQ w i ≤ 3)}
      + cubeM N {w | ¬ ∀ i, SQ2 w i ≤ 6 * (2 / 3 : ℝ) ^ N}
      + cubeM N {w | ¬ ∀ i (M : Finset (Fin N)) (m : State N), subSum w i M m ≤
          (2 : ℝ) ^ (N - M.card) * (1 / 2 : ℝ) ^ (N - 1)
            + 16 * N * (Real.sqrt ((2 : ℝ) ^ (N - M.card) * (1 / 3 : ℝ) ^ (N - 1)) + tauN N)}
      + cubeM N {w | ¬ ∀ i, |Zs w - ZQ w i / 2| ≤ 16 * N * sigN N}
      + cubeM N {w | ¬ ∀ k i, Xk w k i ≤ 4 * (N : ℝ) ^ 3 * vk N k * (1 / 2 : ℝ) ^ N}
      + cubeM N {w | ¬ ∀ (S : Finset (Fin N)) i (Y : Finset (Fin N)) t, i ∈ S → Y ⊆ S →
          |Num w S Y t i - cNum w S Y t i| ≤ 2 * Real.sqrt (LkN N S.card * Vp w i S)}
      + cubeM N {w | ¬ ∀ (S : Finset (Fin N)) i (Y Y' : Finset (Fin N)) t, i ∈ S → Y ⊆ S →
          Y' ⊆ S → |DQ w S Y Y' t i| ≤ 16 * LkN N S.card * (Real.sqrt 3 * sigN N + tauN N)}
      + cubeM N {w | ¬ ∀ (S : Finset (Fin N)) j b, j ∈ S → K2N N < S.card →
          1 / 4 ≤ qW w s S j b}
      + cubeM N {w | ¬ Mrow w s ≤ (4 / 5 : ℝ) ^ N} := by
  refine (measure_mono (μ := cubeM N) (t :=
      {w | ¬ ∀ i r, Qw w i r ≤ tauN N}
      ∪ {w | ¬ (1 / 2 ≤ Zs w ∧ Zs w ≤ 2 ∧ ∀ i, ZQ w i ≤ 3)}
      ∪ {w | ¬ ∀ i, SQ2 w i ≤ 6 * (2 / 3 : ℝ) ^ N}
      ∪ {w | ¬ ∀ i (M : Finset (Fin N)) (m : State N), subSum w i M m ≤
          (2 : ℝ) ^ (N - M.card) * (1 / 2 : ℝ) ^ (N - 1)
            + 16 * N * (Real.sqrt ((2 : ℝ) ^ (N - M.card) * (1 / 3 : ℝ) ^ (N - 1)) + tauN N)}
      ∪ {w | ¬ ∀ i, |Zs w - ZQ w i / 2| ≤ 16 * N * sigN N}
      ∪ {w | ¬ ∀ k i, Xk w k i ≤ 4 * (N : ℝ) ^ 3 * vk N k * (1 / 2 : ℝ) ^ N}
      ∪ {w | ¬ ∀ (S : Finset (Fin N)) i (Y : Finset (Fin N)) t, i ∈ S → Y ⊆ S →
          |Num w S Y t i - cNum w S Y t i| ≤ 2 * Real.sqrt (LkN N S.card * Vp w i S)}
      ∪ {w | ¬ ∀ (S : Finset (Fin N)) i (Y Y' : Finset (Fin N)) t, i ∈ S → Y ⊆ S →
          Y' ⊆ S → |DQ w S Y Y' t i| ≤ 16 * LkN N S.card * (Real.sqrt 3 * sigN N + tauN N)}
      ∪ {w | ¬ ∀ (S : Finset (Fin N)) j b, j ∈ S → K2N N < S.card →
          1 / 4 ≤ qW w s S j b}
      ∪ {w | ¬ Mrow w s ≤ (4 / 5 : ℝ) ^ N}) ?_).trans ?_
  · intro w hw
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h2, h3⟩, h4⟩, h6⟩, h11⟩, h12⟩, h13a⟩, h13b⟩, h16⟩, hU⟩ := h
    exact hw ⟨h2, h3, h4, h6, h11, h12, h13a, h13b, h16, hU⟩
  · refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
    refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
    refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
    refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
    refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
    refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
    refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
    refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
    exact measure_union_le _ _

/-- A sequence of measures bounded by `ENNReal.ofReal (f N)` with `f → 0` tends to `0`. -/
lemma tendsto_zero_of_le_ofReal {a : ℕ → ENNReal} {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0))
    (h : ∀ N, a N ≤ ENNReal.ofReal (f N)) : Tendsto a atTop (𝓝 0) := by
  have hf' : Tendsto (fun N => ENNReal.ofReal (f N)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hf
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hf' (fun _ => zero_le) h

/-- The good event has probability tending to one: `cubeM N {w | ¬ GoodW N (s N) w} → 0`. -/
theorem tendsto_cubeM_notGood (s : ∀ N, State N) :
    Tendsto (fun N => cubeM N {w | ¬ GoodW N (s N) w}) atTop (𝓝 0) := by
  have h2 := tendsto_zero_of_le_ofReal tendsto_fg2 fun N => cubeM_not_g2 (N := N)
  have h3 := tendsto_zero_of_le_ofReal tendsto_fg3 fun N => cubeM_not_g3 (N := N)
  have h4 := tendsto_zero_of_le_ofReal tendsto_fg4 fun N => cubeM_not_g4 (N := N)
  have h6 := tendsto_zero_of_le_ofReal tendsto_fg6 fun N => cubeM_not_g6 (N := N)
  have h11 := tendsto_zero_of_le_ofReal tendsto_fg11 fun N => cubeM_not_g11 (N := N)
  have h12 := tendsto_zero_of_le_ofReal tendsto_fg12 fun N => cubeM_not_g12 (N := N)
  have h13a := tendsto_zero_of_le_ofReal tendsto_fg13a fun N => cubeM_not_g13a (N := N)
  have h13b := tendsto_zero_of_le_ofReal tendsto_fg13b fun N => cubeM_not_g13b (N := N)
  have h16 := tendsto_zero_of_le_ofReal tendsto_fg16 fun N => cubeM_not_g16 (s N)
  have hU := tendsto_zero_of_le_ofReal tendsto_fgU fun N => cubeM_not_gU (s N)
  have hsum := ((((((((h2.add h3).add h4).add h6).add h11).add h12).add h13a).add h13b).add
    h16).add hU
  simp only [add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun N => cubeM_notGood_le (s N)

end

end Census
end IIT
