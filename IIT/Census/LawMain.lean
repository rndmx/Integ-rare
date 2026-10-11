/-
The limit law for the size of the maximal complex.

For every sequence of current states `s N`, with probability tending to one over the cube, every
maximiser of `φ_s` has exactly three units (`tendsto_volume_argmax_ne3`).

The bad set is contained in the failure set of the triple lower bound (Theorem P3), the union
set of Theorem E (sizes `2 ≤ k ≤ 21`, `k ≠ 3`), and the exceptional set of the tightness
argument (sizes `≥ 22`). Off these sets some triple has `φ_s ≥ 0.31 √(log N) σ_N`, while every
candidate of another size has a strictly smaller `φ_s`.
-/
import IIT.Census.ThmP3
import IIT.Census.ThmE
import IIT.Census.TightMain

namespace IIT
namespace Census

open MeasureTheory Finset Filter Topology

/-- **Limit law.** With probability tending to one, every maximiser of `φ_s` has exactly three
units. -/
theorem tendsto_volume_argmax_ne3 (s : ∀ N, State N) :
    Tendsto (fun N => volume {z | z ∈ cube N ∧ ∃ S : Finset (Fin N),
      (∀ S', phi z (s N) S' ≤ phi z (s N) S) ∧ S.card ≠ 3}) atTop (𝓝 0) := by
  have hsum := ((tendsto_triple_lower s).add (te_thmE_union s)).add (tm_tendsto_exc s)
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [detA, eventually_envelope, tm_eventually_const] with N hA hE hc
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans
    (add_le_add (measure_union_le _ _) le_rfl))
  rintro z ⟨hz, S, hmax, h3⟩
  by_contra hbad
  rw [Set.mem_union, Set.mem_union, not_or, not_or] at hbad
  obtain ⟨⟨hP, hEU⟩, hexc⟩ := hbad
  obtain ⟨T, -, hT⟩ : ∃ T : Finset (Fin N), T.card = 3 ∧
      tp_c3 * Real.sqrt (Real.log N) * sigN N ≤ phi z (s N) T := by
    by_contra h; exact hP ⟨hz, h⟩
  have hEU' : ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 21 → S.card ≠ 3 →
      phi z (s N) S ≤ 2896 / 10000 * Real.sqrt (Real.log N) * sigN N := by
    intro S h2 h21 h3
    by_contra h; exact hEU ⟨hz, S, h2, h21, h3, not_le.1 h⟩
  have hσ := sigN_pos N
  have hr : 0 ≤ Real.sqrt (Real.log N) := Real.sqrt_nonneg _
  have hpos : 0 < Real.sqrt (Real.log N) * sigN N := by
    unfold cstar at hc; nlinarith
  have hTS := hmax T
  have hlow : 31 / 100 * (Real.sqrt (Real.log N) * sigN N) ≤ phi z (s N) S := by
    have := hT.trans hTS; unfold tp_c3 at this; linarith
  by_cases h1 : S.card ≤ 1
  · have h0 : phi z (s N) S = 0 := sysPhi_eq_zero_of_card_le_one _ _ _ h1
    nlinarith
  by_cases h21 : S.card ≤ 21
  · have := hEU' S (by omega) h21 h3
    nlinarith
  simp only [tm_exc, Set.mem_union, not_or] at hexc
  obtain ⟨⟨⟨⟨hbd, hG⟩, hSh⟩, -⟩, -⟩ := hexc
  have ho : z ∈ openCube N := by by_contra h; exact hbd ⟨hz, h⟩
  have hG' : GoodW N (s N) (flipP (s N) z) := by by_contra h; exact hG ⟨hz, h⟩
  have hSh' : gSharp N (flipP (s N) z) := by by_contra h; exact hSh ⟨hz, h⟩
  unfold cstar at hE hc
  by_cases hK : S.card ≤ KN N
  · have := hE (s N) z ho hG' hSh' S (by omega) hK
    nlinarith
  · have := hA (s N) z ho hG' S (not_le.1 hK)
    nlinarith

end Census
end IIT
