/-
**The whole system is almost never integrated.** Under the uniform measure on TPMs
(background = current state), `P(φ_s(univ) > 0) → 0` as `N → ∞`.

Deterministic core: `UnivDet.exists_maxRow_of_phi_univ_pos` (a positive `φ_s(univ)` forces the
most probable past row to beat every column half-mean). Probability: `UnivProb.tendsto_volume_badUniv`
(that event is rare; uses the Erlang tail bound `erlang_lower`). Here: the boundary of the
cube is null, and the two are combined.
-/
import IIT.Census.UnivDet
import IIT.Census.UnivProb

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- A single coordinate hyperplane `{z | z s i = c}` is Lebesgue-null. -/
lemma volume_coord_eq (s : State N) (i : Fin N) (c : ℝ) :
    volume {z : Param N | z s i = c} = 0 := by
  classical
  have : {z : Param N | z s i = c} =
      Set.univ.pi fun s' : State N => Set.univ.pi fun i' : Fin N =>
        if s' = s ∧ i' = i then ({c} : Set ℝ) else Set.univ := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi]
    constructor
    · rintro h s' i'
      split_ifs with hs
      · obtain ⟨rfl, rfl⟩ := hs; exact h
      · trivial
    · intro h
      simpa using h s i
  rw [this, volume_pi_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
  rw [volume_pi_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp

/-- The cube minus the open cube is null. -/
lemma volume_cube_diff_openCube (N : ℕ) : volume (cube N \ openCube N) = 0 := by
  have hsub : cube N \ openCube N ⊆
      ⋃ s : State N, ⋃ i : Fin N, ({z : Param N | z s i = 0} ∪ {z | z s i = 1}) := by
    rintro z ⟨hz, hno⟩
    simp only [openCube, Set.mem_ofPred_eq, not_forall] at hno
    obtain ⟨s, i, hsi⟩ := hno
    have hc := hz s i
    simp only [Set.mem_Icc] at hc
    simp only [Set.mem_Ioo, not_and_or, not_lt] at hsi
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq]
    refine ⟨s, i, ?_⟩
    rcases hsi with h | h
    · exact Or.inl (le_antisymm h hc.1)
    · exact Or.inr (le_antisymm hc.2 h)
  refine measure_mono_null hsub ?_
  refine (measure_iUnion_null fun s => measure_iUnion_null fun i => ?_)
  exact measure_union_null (volume_coord_eq s i 0) (volume_coord_eq s i 1)

/-- The event that the whole substrate has positive `φ_s`. -/
def univPos (N : ℕ) (s : State N) : Set (Param N) :=
  {z | z ∈ cube N ∧ 0 < phi z s univ}

lemma univPos_subset (hN : 2 ≤ N) (s : State N) :
    univPos N s ⊆ (cube N \ openCube N) ∪ badUniv N s := by
  rintro z ⟨hz, hpos⟩
  by_cases ho : z ∈ openCube N
  · exact Or.inr ⟨hz, exists_maxRow_of_phi_univ_pos hN z ho s hpos⟩
  · exact Or.inl ⟨hz, ho⟩

/-- **Theorem (univ-zero).** Under the uniform measure on TPMs, the probability that the
whole substrate has positive system integrated information tends to `0`. -/
theorem tendsto_volume_univPos (s : ∀ N, State N) :
    Tendsto (fun N => volume (univPos N (s N))) atTop (𝓝 0) := by
  have hb := tendsto_volume_badUniv s
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  calc volume (univPos N (s N))
      ≤ volume ((cube N \ openCube N) ∪ badUniv N (s N)) := measure_mono (univPos_subset hN _)
    _ ≤ volume (cube N \ openCube N) + volume (badUniv N (s N)) := measure_union_le _ _
    _ = volume (badUniv N (s N)) := by rw [volume_cube_diff_openCube, zero_add]

end Census
end IIT
