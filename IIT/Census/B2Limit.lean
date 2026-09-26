/-
Census of complexes under the uniform measure on TPMs: the proper-subset complex (case B2)
has probability tending to one (`tendsto_volume_B2`).

Inputs: univ-zero (`UnivZero.tendsto_volume_univPos`), the pair step
(`PairReduce.noPos_subset` + `PairCLT.limsup_allBad`) and the tie theorem
(`Ties.volume_ties_null`). The Erlang tail bound (`ErlangProof`), the multivariate Lyapunov
CLT (`CLTProof`) and Mityagin's zero-set theorem (`MityaginProof`) are proved here. `#print axioms tendsto_volume_B2` = [propext, Classical.choice, Quot.sound].
-/
import IIT.Census.UnivZero
import IIT.Census.Ties
import IIT.Census.PairCLT

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- **Case B2**: some nonempty proper subset is a complex (`U = univ`, `u = s`).
`Nonempty` matters: the empty set overlaps nothing and is vacuously a complex. -/
def caseB2 (N : ℕ) (s : State N) : Set (Param N) :=
  {z | ∃ S : Finset (Fin N), S.Nonempty ∧ S ≠ univ ∧ IsComplex (tpmOf z) s univ S s}

/-- Bad event of Theorem 1: no proper candidate strictly beats the whole substrate. -/
def notBeaten (N : ℕ) (s : State N) : Set (Param N) :=
  {z | z ∈ cube N ∧ ∀ S : Finset (Fin N), S ≠ univ → phi z s S ≤ phi z s univ}

/-- Bad event of Theorem 2: an exact tie at a positive value between distinct candidates. -/
def ties (N : ℕ) (s : State N) : Set (Param N) :=
  {z | z ∈ cube N ∧ ∃ S S' : Finset (Fin N), S ≠ S' ∧ 0 < phi z s S ∧ phi z s S = phi z s S'}

/-! ## The two analytic inputs -/

/-- Bad event of the pair step: no proper candidate has positive `φ_s`. -/
def noPos (N : ℕ) (s : State N) : Set (Param N) :=
  {z | z ∈ cube N ∧ ∀ S : Finset (Fin N), S ≠ univ → phi z s S ≤ 0}

/-- **Pair step**: with probability tending to one some proper candidate
(a pair) has positive `φ_s`. -/
theorem tendsto_noPos (s : ∀ N, State N) :
    Tendsto (fun N => volume (noPos N (s N))) atTop (𝓝 0) := by
  have hsub : ∀ L, ∀ᶠ N in atTop, volume (noPos N (s N)) ≤ volume (allBad N L (s N)) := by
    intro L
    filter_upwards [eventually_ge_atTop 3] with N hN
    calc volume (noPos N (s N))
        ≤ volume ((cube N \ openCube N) ∪ allBad N L (s N)) := measure_mono (noPos_subset hN L _)
      _ ≤ volume (cube N \ openCube N) + volume (allBad N L (s N)) := measure_union_le _ _
      _ = volume (allBad N L (s N)) := by rw [volume_cube_diff_openCube, zero_add]
  obtain ⟨p, hp0, hp1, hlim⟩ := limsup_allBad s
  have hbound : ∀ L, limsup (fun N => volume (noPos N (s N))) atTop ≤ ENNReal.ofReal ((1 - p) ^ L) :=
    fun L => (limsup_le_limsup (hsub L)).trans (hlim L)
  have hgeom : Tendsto (fun L : ℕ => ENNReal.ofReal ((1 - p) ^ L)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith))
  have hls : limsup (fun N => volume (noPos N (s N))) atTop ≤ 0 :=
    ge_of_tendsto' hgeom hbound
  exact tendsto_of_le_liminf_of_limsup_le (zero_le.trans (le_liminf_of_le (by isBoundedDefault)
    (Eventually.of_forall fun _ => zero_le))) hls

lemma notBeaten_subset (s : State N) : notBeaten N s ⊆ univPos N s ∪ noPos N s := by
  rintro z ⟨hz, hb⟩
  by_cases hu : 0 < phi z s univ
  · exact Or.inl ⟨hz, hu⟩
  · refine Or.inr ⟨hz, fun S hS => (hb S hS).trans (not_lt.mp hu)⟩

/-- **Theorem 1**: the whole substrate is beaten by a proper
candidate with probability tending to one. -/
theorem tendsto_notBeaten (s : ∀ N, State N) :
    Tendsto (fun N => volume (notBeaten N (s N))) atTop (𝓝 0) := by
  have h := (tendsto_volume_univPos s).add (tendsto_noPos s)
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun _ => zero_le) fun N => ?_
  exact (measure_mono (notBeaten_subset (s N))).trans (measure_union_le _ _)

/-- **Theorem 2**: positive ties between distinct candidates are null. -/
theorem volume_ties (s : State N) : volume (ties N s) = 0 := by
  exact volume_ties_null s

/-! ## The deterministic step -/

/-- If no two distinct candidates tie at a positive value, and some proper candidate
strictly beats the whole substrate, then a nonempty proper subset is a complex: take a
maximiser of `φ_s` over all subsets. -/
theorem mem_B2_of (z : Param N) (s : State N)
    (hties : ∀ S S' : Finset (Fin N), S ≠ S' → 0 < phi z s S → phi z s S ≠ phi z s S')
    (hbeat : ∃ S : Finset (Fin N), S ≠ univ ∧ phi z s univ < phi z s S) :
    z ∈ caseB2 N s := by
  obtain ⟨S₀, hS₀, hlt⟩ := hbeat
  obtain ⟨M, -, hM⟩ := (univ : Finset (Finset (Fin N))).exists_max_image (phi z s)
    ⟨S₀, mem_univ _⟩
  have hM' : ∀ S', phi z s S' ≤ phi z s M := fun S' => hM S' (mem_univ _)
  have huniv_nonneg : 0 ≤ phi z s univ := sysPhi_nonneg _ _ _ _
  have hMpos : 0 < phi z s M := lt_of_le_of_lt huniv_nonneg (lt_of_lt_of_le hlt (hM' S₀))
  have hMne : M ≠ univ := by
    rintro rfl
    exact absurd (hM' S₀) (not_le.mpr hlt)
  have hMnon : M.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    have h0 : phi z s ∅ = 0 :=
      sysPhi_eq_zero_of_card_le_one _ _ _ (by simp)
    linarith
  refine ⟨M, hMnon, hMne, subset_univ _, fun S' _ hne _ => ?_⟩
  exact lt_of_le_of_ne (hM' S') (hties M S' (Ne.symm hne) hMpos).symm

/-! ## Measure bookkeeping -/

lemma volume_cube (N : ℕ) : volume (cube N) = 1 := by
  have : cube N = Set.univ.pi fun _ : State N => Set.univ.pi fun _ : Fin N => Set.Icc (0 : ℝ) 1 := by
    ext z; simp only [cube, Set.mem_setOf_eq, Set.mem_univ_pi]
  rw [this, volume_pi_pi]
  simp only [volume_pi_pi, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
    Finset.prod_const_one]

/-- The cube is covered by caseB2 and the two bad events. -/
lemma cube_subset (s : State N) : cube N ⊆ (cube N ∩ caseB2 N s) ∪ notBeaten N s ∪ ties N s := by
  intro z hz
  by_cases hb : ∀ S : Finset (Fin N), S ≠ univ → phi z s S ≤ phi z s univ
  · exact Or.inl (Or.inr ⟨hz, hb⟩)
  by_cases ht : ∃ S S' : Finset (Fin N), S ≠ S' ∧ 0 < phi z s S ∧ phi z s S = phi z s S'
  · exact Or.inr ⟨hz, ht⟩
  push Not at hb ht
  exact Or.inl (Or.inl ⟨hz, mem_B2_of z s (fun S S' h hp => ht S S' h hp) hb⟩)

/-- **Main theorem.** Under the uniform measure on TPMs, the probability that a nonempty
proper subset is a complex tends to one as the number of units tends to infinity, for any
choice of current state `s N` (background `u = s`). -/
theorem tendsto_volume_B2 (s : ∀ N, State N) :
    Tendsto (fun N => volume (cube N ∩ caseB2 N (s N))) atTop (𝓝 1) := by
  have hbad := tendsto_notBeaten s
  -- lower bound: 1 ≤ vol(cube ∩ caseB2) + vol(notBeaten) + 0
  have hlow : ∀ N, 1 ≤ volume (cube N ∩ caseB2 N (s N)) + volume (notBeaten N (s N)) := by
    intro N
    calc (1 : ENNReal) = volume (cube N) := (volume_cube N).symm
      _ ≤ volume ((cube N ∩ caseB2 N (s N)) ∪ notBeaten N (s N) ∪ ties N (s N)) :=
          measure_mono (cube_subset (s N))
      _ ≤ volume ((cube N ∩ caseB2 N (s N)) ∪ notBeaten N (s N)) + volume (ties N (s N)) :=
          measure_union_le _ _
      _ ≤ volume (cube N ∩ caseB2 N (s N)) + volume (notBeaten N (s N)) + 0 := by
          rw [volume_ties]; gcongr; exact measure_union_le _ _
      _ = _ := add_zero _
  have hup : ∀ N, volume (cube N ∩ caseB2 N (s N)) ≤ 1 := fun N =>
    (measure_mono Set.inter_subset_left).trans (volume_cube N).le
  -- squeeze: 1 - vol(notBeaten) ≤ vol(cube ∩ caseB2) ≤ 1
  have hlow' : Tendsto (fun N => 1 - volume (notBeaten N (s N))) atTop (𝓝 1) := by
    simpa using (ENNReal.Tendsto.sub tendsto_const_nhds hbad (Or.inl ENNReal.one_ne_top))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow' tendsto_const_nhds (fun N => ?_) hup
  exact tsub_le_iff_right.mpr (hlow N)

end Census
end IIT
