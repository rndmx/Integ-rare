/-
Tightness of the maximal complex.

For every sequence of current states `s N`, with probability tending to one over the cube, every
maximiser of `φ_s` has at most `21` units (`tendsto_volume_argmax_gt21`).

Eventually in `N`, the bad set is contained in the null boundary of the cube, the failures of the
events `GoodW`, `gSharp`, `gZ` in flipped coordinates, and the event that no pair lies in the
orthant `inA` with an effective box. Off this set the best pair has `φ_s ≥ cstar √(log N) σ_N`,
while every candidate with at least `22` units has a strictly smaller `φ_s`.
-/
import IIT.Census.BigPhiMain
import IIT.Census.SharpDev
import IIT.Census.TightEnvelope
import IIT.Census.PairLower
import IIT.Census.PairSecond2
import IIT.Census.UnivZero

namespace IIT
namespace Census

open MeasureTheory Finset Filter Topology

variable {N : ℕ}

/-- Points of the cube where a property of the flipped parameters fails. -/
def tm_flipBad (N : ℕ) (s : State N) (P : Param N → Prop) : Set (Param N) :=
  {z | z ∈ cube N ∧ ¬ P (flipP s z)}

lemma tm_volume_flipBad_le (s : State N) (P : Param N → Prop) :
    volume (tm_flipBad N s P) ≤ cubeM N {w | ¬ P w} := by
  have hsub : tm_flipBad N s P ⊆ flipE s ⁻¹' (cube N ∩ {w | ¬ P w}) := by
    rintro z ⟨hz, hG⟩
    exact ⟨flipP_cube hz s, hG⟩
  calc volume (tm_flipBad N s P)
      ≤ volume (flipE s ⁻¹' (cube N ∩ {w | ¬ P w})) := measure_mono hsub
    _ = cubeM N {w | ¬ P w} := by
        rw [(mp_flipE s).measure_preimage_equiv, volume_cube_inter]

/-- No pair lies in the orthant with an effective box. -/
def tm_noPair (N : ℕ) (s : State N) : Set (Param N) :=
  {z | z ∈ cube N ∧ ¬ ∃ a b : Fin N, a ≠ b ∧ effBox z s a b ∧ inA (flipP s z) a b (yN N)}

/-- The exceptional set of the tightness argument. -/
def tm_exc (N : ℕ) (s : State N) : Set (Param N) :=
  (cube N \ openCube N) ∪ tm_flipBad N s (GoodW N s) ∪ tm_flipBad N s (gSharp N)
    ∪ tm_flipBad N s (gZ N) ∪ tm_noPair N s

lemma tm_tendsto_exc (s : ∀ N, State N) :
    Tendsto (fun N => volume (tm_exc N (s N))) atTop (𝓝 0) := by
  have hG : Tendsto (fun N => volume (tm_flipBad N (s N) (GoodW N (s N)))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tendsto_cubeM_notGood s)
      (fun _ => zero_le) fun N => tm_volume_flipBad_le (s N) _
  have hSh : Tendsto (fun N => volume (tm_flipBad N (s N) (gSharp N))) atTop (𝓝 0) := by
    have h := tendsto_zero_of_le_ofReal tendsto_fSharp fun N => cubeM_not_gSharp (N := N)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun _ => zero_le) fun N => tm_volume_flipBad_le (s N) _
  have hZ : Tendsto (fun N => volume (tm_flipBad N (s N) (gZ N))) atTop (𝓝 0) := by
    have h := tendsto_zero_of_le_ofReal tendsto_fZ fun N => cubeM_not_gZ (N := N)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun _ => zero_le) fun N => tm_volume_flipBad_le (s N) _
  have hP : Tendsto (fun N => volume (tm_noPair N (s N))) atTop (𝓝 0) :=
    tendsto_noPairOrthant s
  have hsum := ((hG.add hSh).add hZ).add hP
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun N => ?_
  unfold tm_exc
  refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  refine (measure_union_le _ _).trans ?_
  rw [volume_cube_diff_openCube, zero_add]

lemma tm_eventually_const : ∀ᶠ N : ℕ in atTop,
    sigN N / 128 < cstar * Real.sqrt (Real.log N) * sigN N := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop 1] with N hN
  have h1 : 1 ≤ Real.sqrt (Real.log N) := by
    rw [Real.one_le_sqrt]; exact hN
  have hσ := sigN_pos N
  have : (1 : ℝ) / 128 < cstar * Real.sqrt (Real.log N) := by
    unfold cstar; nlinarith
  nlinarith

/-- **Tightness of the maximal complex.** With probability tending to one, every maximiser of
`φ_s` has at most `21` units. -/
theorem tendsto_volume_argmax_gt21 (s : ∀ N, State N) :
    Tendsto (fun N => volume {z | z ∈ cube N ∧ ∃ S : Finset (Fin N),
      (∀ S', phi z (s N) S' ≤ phi z (s N) S) ∧ 21 < S.card}) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (tm_tendsto_exc s)
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [detA, eventually_envelope, eventually_pair_lower, tm_eventually_const]
    with N hA hE hL hc
  refine measure_mono ?_
  rintro z ⟨hz, S, hmax, hk⟩
  by_contra hexc
  simp only [tm_exc, Set.mem_union, not_or] at hexc
  obtain ⟨⟨⟨⟨hbd, hG⟩, hSh⟩, hZ⟩, hP⟩ := hexc
  have ho : z ∈ openCube N := by by_contra h; exact hbd ⟨hz, h⟩
  have hG' : GoodW N (s N) (flipP (s N) z) := by by_contra h; exact hG ⟨hz, h⟩
  have hSh' : gSharp N (flipP (s N) z) := by by_contra h; exact hSh ⟨hz, h⟩
  have hZ' : gZ N (flipP (s N) z) := by by_contra h; exact hZ ⟨hz, h⟩
  obtain ⟨a, b, hab, hbox, hin⟩ : ∃ a b : Fin N, a ≠ b ∧ effBox z (s N) a b ∧
      inA (flipP (s N) z) a b (yN N) := by
    by_contra h; exact hP ⟨hz, h⟩
  have hlow := hL (s N) z a b ho hG' hZ' hab hbox hin
  have hm := hmax {a, b}
  by_cases hK : S.card ≤ KN N
  · have := hE (s N) z ho hG' hSh' S (by omega) hK
    linarith
  · have := hA (s N) z ho hG' S (not_le.1 hK)
    linarith

end Census
end IIT
