/-
Census of complexes: `Φ` of the maximal complex vanishes.

For every sequence of current states `s N`, with probability tending to one over the cube:
* every maximiser of `φ_s` has at most `KN N` units (`tendsto_volume_bigArgmax`);
* every maximiser of `φ_s` has `Φ ≤ rateN N` for every selector (`tendsto_volume_PhiArgmax_rate`);
* hence, for every `ε > 0`, every maximiser has `Φ < ε` (`tendsto_volume_PhiArgmax`).

Eventually in `N`, the bad sets are contained in the null boundary of the cube, the event that no
pair reaches `φ_s ≥ σ_N / 128`, and the failure of the good event in flipped coordinates.
-/
import IIT.Census.BigPhiDet
import IIT.Census.BigPhiGood
import IIT.Census.PairQuant

namespace IIT
namespace Census

open MeasureTheory Finset Filter Topology

variable {N : ℕ}

/-- The good event fails for the flipped parameters. -/
def notGoodSet (N : ℕ) (s : State N) : Set (Param N) :=
  {z | z ∈ cube N ∧ ¬ GoodW N s (flipP s z)}

lemma volume_notGoodSet_le (s : State N) :
    volume (notGoodSet N s) ≤ cubeM N {w | ¬ GoodW N s w} := by
  have hsub : notGoodSet N s ⊆ flipE s ⁻¹' (cube N ∩ {w | ¬ GoodW N s w}) := by
    rintro z ⟨hz, hG⟩
    exact ⟨flipP_cube hz s, hG⟩
  calc volume (notGoodSet N s)
      ≤ volume (flipE s ⁻¹' (cube N ∩ {w | ¬ GoodW N s w})) := measure_mono hsub
    _ = cubeM N {w | ¬ GoodW N s w} := by
        rw [(mp_flipE s).measure_preimage_equiv, volume_cube_inter]

/-- The exceptional set `(cube \ openCube) ∪ noGoodPair ∪ notGoodSet` has volume tending to `0`. -/
lemma tendsto_volume_exc (s : ∀ N, State N) :
    Tendsto (fun N => volume ((cube N \ openCube N) ∪ noGoodPair N (s N) (1 / 128)
      ∪ notGoodSet N (s N))) atTop (𝓝 0) := by
  have hG : Tendsto (fun N => volume (notGoodSet N (s N))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tendsto_cubeM_notGood s)
      (fun _ => zero_le) fun N => volume_notGoodSet_le (s N)
  have hsum := (tendsto_noGoodPair s).add hG
  rw [zero_add] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun N => ?_
  calc volume ((cube N \ openCube N) ∪ noGoodPair N (s N) (1 / 128) ∪ notGoodSet N (s N))
      ≤ volume (cube N \ openCube N) + volume (noGoodPair N (s N) (1 / 128))
        + volume (notGoodSet N (s N)) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ = _ := by rw [volume_cube_diff_openCube, zero_add]

lemma tendsto_volume_of_eventually_subset (s : ∀ N, State N) {A : ∀ N, Set (Param N)}
    (h : ∀ᶠ N in atTop, A N ⊆ (cube N \ openCube N) ∪ noGoodPair N (s N) (1 / 128)
      ∪ notGoodSet N (s N)) :
    Tendsto (fun N => volume (A N)) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (tendsto_volume_exc s)
    (Eventually.of_forall fun _ => zero_le) (h.mono fun _ hN => measure_mono hN)

/-- Off the exceptional set, some pair has `φ_s ≥ σ_N / 128`. -/
lemma exists_pair_ge {s : State N} {z : Param N} (hz : z ∈ cube N)
    (hP : z ∉ noGoodPair N s (1 / 128)) :
    ∃ a b : Fin N, a ≠ b ∧ sigN N / 128 ≤ phi z s {a, b} := by
  by_contra hne
  apply hP
  refine ⟨hz, fun a b hab => ?_⟩
  by_contra hlt
  exact hne ⟨a, b, hab, by rw [not_lt] at hlt; linarith⟩

/-- Eventually in `N`, off the exceptional set, every maximiser of `φ_s` has at most `KN N` units. -/
lemma eventually_argmax_small : ∀ᶠ N in atTop, ∀ (s : State N) (z : Param N), z ∈ cube N →
    z ∉ (cube N \ openCube N) ∪ noGoodPair N s (1 / 128) ∪ notGoodSet N s →
    ∀ S : Finset (Fin N), (∀ S', phi z s S' ≤ phi z s S) → S.card ≤ KN N ∧
      z ∈ openCube N ∧ GoodW N s (flipP s z) := by
  filter_upwards [detA] with N hA s z hz hexc S hmax
  simp only [Set.mem_union, not_or] at hexc
  obtain ⟨⟨hbd, hP⟩, hG⟩ := hexc
  have ho : z ∈ openCube N := by
    by_contra h; exact hbd ⟨hz, h⟩
  have hG' : GoodW N s (flipP s z) := by
    by_contra h; exact hG ⟨hz, h⟩
  refine ⟨?_, ho, hG'⟩
  by_contra hk
  rw [not_le] at hk
  obtain ⟨a, b, _, hab⟩ := exists_pair_ge hz hP
  have := hA s z ho hG' S hk
  have := hmax {a, b}
  linarith

/-- **Size of the maximal complex.** With probability tending to one, every maximiser of `φ_s`
has at most `KN N` units. -/
theorem tendsto_volume_bigArgmax (s : ∀ N, State N) :
    Tendsto (fun N => volume {z | z ∈ cube N ∧ ∃ S : Finset (Fin N),
      (∀ S', phi z (s N) S' ≤ phi z (s N) S) ∧ KN N < S.card}) atTop (𝓝 0) := by
  refine tendsto_volume_of_eventually_subset s ?_
  filter_upwards [eventually_argmax_small] with N h
  rintro z ⟨hz, S, hmax, hk⟩
  by_contra hexc
  have := (h (s N) z hz hexc S hmax).1
  omega

/-- **Rate for `Φ` of the maximal complex.** With probability tending to one, every maximiser of
`φ_s` has `Φ ≤ rateN N` for every selector. -/
theorem tendsto_volume_PhiArgmax_rate (s : ∀ N, State N) :
    Tendsto (fun N => volume {z | z ∈ cube N ∧ ∃ S : Finset (Fin N),
      (∀ S', phi z (s N) S' ≤ phi z (s N) S) ∧
      ∃ σ' : SelectorAt (tpmOf z) S (s N) (s N), rateN N < PhiOfAt (tpmOf z) S (s N) (s N) σ'})
      atTop (𝓝 0) := by
  refine tendsto_volume_of_eventually_subset s ?_
  filter_upwards [eventually_argmax_small, detB] with N h hB
  rintro z ⟨hz, S, hmax, σ', hlt⟩
  by_contra hexc
  obtain ⟨hk, ho, hG⟩ := h (s N) z hz hexc S hmax
  exact absurd (hB (s N) z ho hG S hk σ') (not_le.2 hlt)

/-- **`Φ` of the maximal complex vanishes.** For every `ε > 0`, with probability tending to one,
every maximiser of `φ_s` has `Φ < ε` for every selector. -/
theorem tendsto_volume_PhiArgmax (s : ∀ N, State N) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => volume {z | z ∈ cube N ∧ ∃ S : Finset (Fin N),
      (∀ S', phi z (s N) S' ≤ phi z (s N) S) ∧
      ∃ σ' : SelectorAt (tpmOf z) S (s N) (s N), ε ≤ PhiOfAt (tpmOf z) S (s N) (s N) σ'})
      atTop (𝓝 0) := by
  have hr : ∀ᶠ N in atTop, rateN N < ε := (tendsto_order.1 tendsto_rateN).2 ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_volume_PhiArgmax_rate s) (Eventually.of_forall fun _ => zero_le)
    (hr.mono fun N hN => measure_mono ?_)
  rintro z ⟨hz, S, hmax, σ', hle⟩
  exact ⟨hz, S, hmax, σ', lt_of_lt_of_le hN hle⟩

end Census
end IIT
