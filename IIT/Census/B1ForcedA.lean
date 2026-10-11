/-
Census, B1 forced leaves 0..10 of `B1ForcedSkel` (`hleaf i`), part A: the leaves that are unconditional
or deterministic modulo null/superexponential events.

* leaf 0 (`bZs`)    : PROVED (`leafA0`), via `cubeM_Zs_out_le`.
* leaf 2 (`bHalfC`) : PROVED (`leafA2`), Hoeffding + union (`fa_half_all`).
* leaf 3 (`bHalfE`) : PROVED (`leafA3`), the effect half-mean is a column half-mean or its complement.
* leaf 6 (`bFloor`) : PROVED (`leafA6`): on B1 (no row tie) `y_{tc,j} > halfMean_j` (UnivDet), so the
                      floor fails only if a half-mean deviates.
* leaf 1 (`bPos`)   : reduced (`leafA1_of_effect`) to its effect half `bPosE`; the cause half is
                      deterministic on B1 (`fa_lcMin_pos`).
-/
import IIT.Census.B1ForcedSkel
import IIT.Census.B1Ties
import IIT.Census.B1ForcedAZs
import IIT.Census.B1ForcedAHalf

namespace IIT
namespace Census

open MeasureTheory Filter Finset

variable {N : ℕ}

/-! ### leaf 0 -/

theorem leafA0 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (forcedBad N s 0) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [cubeM_Zs_out_le] with N h s
  refine (measure_mono ?_).trans (by unfold RfF; exact h)
  intro w hw
  have hw' : w ∈ bZs N s := hw
  simpa [b1ZMax] using hw'.2

/-! ### leaves 2, 3 -/

lemma fa_effUnit_half (hN : 1 ≤ N) (w : Param N) (s : State N) (j : Fin N) (b : Bool) :
    |effUnit (tpmOf (flipP s w)) (univ.erase j)ᶜ s j b - 1 / 2| = |faColMean w s j - 1 / 2| := by
  have hM : (univ.erase j)ᶜ = ({j} : Finset (Fin N)) := by ext i; simp
  have hp : ∀ r : State N, (tpmOf (flipP s w)).prob j r b =
      if b = s j then clamp01 (w r j) else 1 - clamp01 (w r j) := by
    intro r
    cases b <;> cases h : s j <;> simp [tpmOf, flipP, flipC, h, clamp01_one_sub]
  have hc : (((agree {j} s).card : ℕ) : ℝ) = (2 : ℝ) ^ (N - 1) := by
    rw [card_agree, card_singleton]; push_cast; ring
  unfold effUnit
  rw [hM, hc]
  simp_rw [hp]
  split_ifs
  · rfl
  · rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, hc]
    unfold faColMean
    have h2 : (0 : ℝ) < 2 ^ (N - 1) := by positivity
    rw [show ((2 : ℝ) ^ (N - 1) - ∑ r ∈ agree {j} s, clamp01 (w r j)) / 2 ^ (N - 1) - 1 / 2 =
        -((∑ r ∈ agree {j} s, clamp01 (w r j)) / 2 ^ (N - 1) - 1 / 2) by field_simp; ring, abs_neg]

theorem leafA2 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (forcedBad N s 2) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [fa_half_all] with N h s
  refine (measure_mono ?_).trans (by unfold RfF; exact h)
  intro w hw
  have hw' : w ∈ bHalfC N s := hw
  obtain ⟨_, hn⟩ := hw'
  simp only [Set.mem_setOf_eq, not_forall, not_le] at hn
  obtain ⟨j, hj⟩ := hn
  refine ⟨tcRow w, j, ?_⟩
  rw [← cmean_single_eq]
  simpa [deltaU] using hj

theorem leafA3 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (forcedBad N s 3) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [fa_half_all, eventually_ge_atTop 1] with N h hN s
  refine (measure_mono ?_).trans (by unfold RfF; exact h)
  intro w hw
  have hw' : w ∈ bHalfE N s := hw
  obtain ⟨_, hn⟩ := hw'
  simp only [Set.mem_setOf_eq, not_forall, not_le] at hn
  obtain ⟨j, hj⟩ := hn
  refine ⟨s, j, ?_⟩
  rw [← fa_effUnit_half hN w s j (teW w s j)]
  simpa [deltaU] using hj

/-! ### The cause side is forced on B1 -/

/-- the null event of a tie between row products -/
def faTie (N : ℕ) : Set (Param N) := {w | ∃ r r' : State N, r ≠ r' ∧ Pw w r = Pw w r'}

lemma fa_tie_null : cubeM N (faTie N) = 0 := null_tcRow_tie

/-- **On B1 (no tie), `y_{tc,j}` exceeds the half-mean of column `j`.** -/
theorem fa_cause_pos (hN : 2 ≤ N) {s : State N} {w : Param N} (hB : w ∈ B1w N s)
    (hw : w ∈ openCube N) (hnt : w ∉ faTie N) (j : Fin N) :
    faColMean w (tcRow w) j < clamp01 (w (tcRow w) j) := by
  set z := flipP s w with hzdef
  have hz : z ∈ openCube N := flipP_mem_openCube hw
  have hzw : flipP s z = w := flipP_invol s w
  have hpos : 0 < phi z s univ := (caseB1_subset_univPos hN s hB).2
  obtain ⟨t, hmax, hj⟩ := exists_maxRow_of_phi_univ_pos hN z hz s hpos
  have hrow : ∀ r, rowProd z s r = Pw w r := fun r => by
    unfold rowProd Pw; simp_rw [y_eq_clamp, hzw]
  have ht : t = tcRow w := by
    by_contra hne
    have h1 := Pw_le_tcRow w t
    have h2 := hmax (tcRow w)
    rw [hrow, hrow] at h2
    exact hnt ⟨t, tcRow w, hne, le_antisymm h1 h2⟩
  have := hj j
  rw [b1_halfMean_eq, hzw, y_eq_clamp, hzw, ht] at this
  have e : b1HalfW w j (tcRow w j) = faColMean w (tcRow w) j := by
    unfold b1HalfW faColMean
    congr 2
    ext r; simp [agree]
  rwa [e] at this

/-- **The cause half of `bPos` is deterministic on B1.** -/
theorem fa_lcMin_pos (hN : 2 ≤ N) {s : State N} {w : Param N} (hB : w ∈ B1w N s)
    (hw : w ∈ openCube N) (hnt : w ∉ faTie N) : 0 < lcMin s w := by
  have hz : flipP s w ∈ openCube N := flipP_mem_openCube hw
  have hzw : flipP s (flipP s w) = w := flipP_invol s w
  obtain ⟨hm, -, -, hcp, -⟩ := lamCz_means hz s (tcRow w)
  haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  obtain ⟨j0, hj0⟩ := exists_eq_ciInf_of_finite (f := fun j => kF (lamCz (flipP s w) s (tcRow w)) j)
  unfold lcMin
  rw [← hj0]
  show 0 < lamCz (flipP s w) s (tcRow w) j0 (univ.erase j0)
  rw [hm]
  have hsd : (univ \ univ.erase j0 : Finset (Fin N)) = {j0} := by ext i; simp
  have hc := hcp j0 (univ.erase j0)
  rw [hsd, hzw] at hc ⊢
  rw [cmean_single_eq] at hc ⊢
  have hlt := fa_cause_pos hN hB hw hnt j0
  exact Real.logb_pos (by norm_num) ((one_lt_div hc).2 hlt)

/-! ### leaf 6 -/

/-- the superexponential half-mean event -/
def faHalfBad (N : ℕ) : Set (Param N) :=
  {w | ∃ t j, (1 / ((N : ℝ) + 1)) < |faColMean w t j - 1 / 2|}

theorem leafA6 : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (forcedBad N s 6) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [fa_half_all, eventually_ge_atTop 2] with N h hN s
  have hsub : forcedBad N s 6 ⊆ faTie N ∪ faHalfBad N := by
    intro w hw
    have hw' : w ∈ bFloor N s := hw
    obtain ⟨⟨hB, ho⟩, hn⟩ := hw'
    by_cases ht : w ∈ faTie N
    · exact Or.inl ht
    right
    simp only [Set.mem_setOf_eq, not_forall, not_le] at hn
    obtain ⟨j, hj⟩ := hn
    have hc := fa_cause_pos hN hB ho ht j
    refine ⟨tcRow w, j, ?_⟩
    have hδ0 : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    rw [abs_sub_comm, abs_of_pos (by unfold deltaU at hj; linarith)]
    unfold deltaU at hj
    linarith
  calc cubeM N (forcedBad N s 6) ≤ cubeM N (faTie N) + cubeM N (faHalfBad N) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ 0 + ENNReal.ofReal (Real.exp (-(RfF * N))) := by
        rw [fa_tie_null]; gcongr; unfold RfF; exact h
    _ = _ := zero_add _

/-! ### leaf 1, modulo its effect half -/

/-- The effect half of `bPos` (see the report: NOT forced by B1, since `teW` need not be U's effect state). -/
def bPosE (N : ℕ) (s : State N) : Set (Param N) :=
  B1w N s ∩ openCube N ∩ {w | ¬ 0 < leMin s w}

theorem bPos_subset (hN : 2 ≤ N) (s : State N) : forcedBad N s 1 ⊆ faTie N ∪ bPosE N s := by
  intro w hw
  have hw' : w ∈ bPos N s := hw
  obtain ⟨⟨hB, ho⟩, hn⟩ := hw'
  by_cases ht : w ∈ faTie N
  · exact Or.inl ht
  exact absurd (fa_lcMin_pos hN hB ho ht) hn

theorem leafA1_of_effect
    (hE : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (bPosE N s) ≤ ENNReal.ofReal (Real.exp (-(RfF * N)))) :
    ∀ᶠ N : ℕ in atTop, ∀ s : State N,
      cubeM N (forcedBad N s 1) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [hE, eventually_ge_atTop 2] with N h hN s
  calc cubeM N (forcedBad N s 1) ≤ cubeM N (faTie N) + cubeM N (bPosE N s) :=
        (measure_mono (bPos_subset hN s)).trans (measure_union_le _ _)
    _ ≤ 0 + ENNReal.ofReal (Real.exp (-(RfF * N))) := by rw [fa_tie_null]; gcongr; exact h s
    _ = _ := zero_add _

end Census
end IIT
