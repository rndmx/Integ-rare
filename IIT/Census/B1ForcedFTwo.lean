/-
Census, B1 forced leaf 18 (`failOnly`, agent "forcedF"): two failing units.

The field `failOnly` fails jointly with the regime event at `(r0, x, σ)` iff the regime event also holds at some
`x' ≠ x` (either side).  Per `(r0, x, x', σ, σ')` the two cell events share the tilt (row `r0`) and the link (row `s`);
the joint Chernoff bound uses four rows per column (`cubeM_chernoff_four`, two windows):
* `σ ≠ σ'`: the per-unit factor splits into the certified cause integral (row `r0`) times the certified effect
  integral (row `s`); rate `≥ 2 R0 + log(3/2) + log(3/4) ≥ 2.13` per `r0` (no new certificate);
* `σ = σ'`: the second `gX` factor is bounded by its Laurent form above the cap (`Ghigh`), giving a sum of
  shifted certified integrals (certificate `B1ForcedFTwoCert`).
-/
import IIT.Census.B1ForcedFSelf

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset ProbabilityTheory

variable {N : ℕ}

/-! ### Four rows per column -/

lemma colLaw_map_quad {r1 r2 r3 r4 : State N} (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h14 : r1 ≠ r4)
    (h23 : r2 ≠ r3) (h24 : r2 ≠ r4) (h34 : r3 ≠ r4) :
    (colLaw N).map (fun c => ((c r1, c r2), (c r3, c r4))) = (unif.prod unif).prod (unif.prod unif) := by
  have hind := iIndepFun_colLaw.indepFun_prodMk_prodMk (fun r => measurable_pi_apply r) r1 r2 r3 r4
    h13 h14 h23 h24
  rw [hind.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop), colLaw_map_pair h12, colLaw_map_pair h34]

lemma lintegral_colLaw_quad {r1 r2 r3 r4 : State N} (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h14 : r1 ≠ r4)
    (h23 : r2 ≠ r3) (h24 : r2 ≠ r4) (h34 : r3 ≠ r4) {g : (ℝ × ℝ) × (ℝ × ℝ) → ENNReal} (hg : Measurable g) :
    ∫⁻ c, g ((c r1, c r2), (c r3, c r4)) ∂colLaw N =
      ∫⁻ y, ∫⁻ u, ∫⁻ z, ∫⁻ v, g ((y, u), (z, v)) ∂unif ∂unif ∂unif ∂unif := by
  have hpm : Measurable fun c : State N → ℝ => ((c r1, c r2), (c r3, c r4)) := by fun_prop
  calc ∫⁻ c, g ((c r1, c r2), (c r3, c r4)) ∂colLaw N
      = ∫⁻ p, g p ∂(colLaw N).map (fun c => ((c r1, c r2), (c r3, c r4))) := (lintegral_map hg hpm).symm
    _ = ∫⁻ p, ∫⁻ q, g (p, q) ∂(unif.prod unif) ∂(unif.prod unif) := by
        rw [colLaw_map_quad h12 h13 h14 h23 h24 h34, lintegral_prod _ hg.aemeasurable]
    _ = ∫⁻ y, ∫⁻ u, ∫⁻ q, g ((y, u), q) ∂(unif.prod unif) ∂unif ∂unif := by
        rw [lintegral_prod _ (hg.lintegral_prod_right').aemeasurable]
    _ = _ := by
        refine lintegral_congr fun y => lintegral_congr fun u => ?_
        exact lintegral_prod (fun q => g ((y, u), q)) (hg.comp measurable_prodMk_left).aemeasurable

/-- **Joint Chernoff for four rows** with windows on the first and third entries. -/
theorem cubeM_chernoff_four {κ : Type*} (ra rb rc rd : Fin N → State N)
    (hab : ∀ i, ra i ≠ rb i) (hac : ∀ i, ra i ≠ rc i) (had : ∀ i, ra i ≠ rd i)
    (hbc : ∀ i, rb i ≠ rc i) (hbd : ∀ i, rb i ≠ rd i) (hcd : ∀ i, rc i ≠ rd i)
    (K : Finset κ) (f : κ → Fin N → (ℝ × ℝ) × (ℝ × ℝ) → ℝ) (hf : ∀ k i, Measurable (f k i))
    (a t : κ → ℝ) (ht : ∀ k ∈ K, 0 ≤ t k) (Wa Wc : Fin N → Set ℝ) (hWa : ∀ i, MeasurableSet (Wa i))
    (hWc : ∀ i, MeasurableSet (Wc i)) :
    cubeM N {w | (∀ i, w (ra i) i ∈ Wa i ∧ w (rc i) i ∈ Wc i) ∧
        ∀ k ∈ K, ∑ i, f k i ((w (ra i) i, w (rb i) i), (w (rc i) i, w (rd i) i)) ≤ a k} ≤
      ENNReal.ofReal (Real.exp (∑ k ∈ K, t k * a k)) *
        ∏ i, ∫⁻ y in Wa i, ∫⁻ u, ∫⁻ z in Wc i, ∫⁻ v,
          ENNReal.ofReal (Real.exp (-∑ k ∈ K, t k * f k i ((y, u), (z, v)))) ∂unif ∂unif ∂unif ∂unif := by
  have hWm : ∀ i, MeasurableSet {c : State N → ℝ | c (ra i) ∈ Wa i ∧ c (rc i) ∈ Wc i} := fun i =>
    (measurable_pi_apply (ra i) (hWa i)).inter (measurable_pi_apply (rc i) (hWc i))
  have h := cubeM_chernoff_cols K (fun k i c => f k i ((c (ra i), c (rb i)), (c (rc i), c (rd i))))
    (fun k i => (hf k i).comp (by fun_prop)) a t ht
    (fun i => {c | c (ra i) ∈ Wa i ∧ c (rc i) ∈ Wc i}) hWm
  refine h.trans_eq ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  set H : (ℝ × ℝ) × (ℝ × ℝ) → ENNReal := fun p =>
    ENNReal.ofReal (Real.exp (-∑ k ∈ K, t k * f k i p)) with hH
  have hHm : Measurable H := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (Finset.measurable_sum _ fun k _ => (hf k i).const_mul (t k)).neg)
  set S : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {p | p.1.1 ∈ Wa i ∧ p.2.1 ∈ Wc i} with hS
  have hSm : MeasurableSet S :=
    (measurable_fst.comp measurable_fst (hWa i)).inter (measurable_fst.comp measurable_snd (hWc i))
  rw [← lintegral_indicator (hWm i)]
  have e1 : ∀ c : State N → ℝ, ({c | c (ra i) ∈ Wa i ∧ c (rc i) ∈ Wc i} : Set (State N → ℝ)).indicator
      (fun c => H ((c (ra i), c (rb i)), (c (rc i), c (rd i)))) c =
      S.indicator H ((c (ra i), c (rb i)), (c (rc i), c (rd i))) := fun c => by
    by_cases hc : c (ra i) ∈ Wa i ∧ c (rc i) ∈ Wc i
    · rw [Set.indicator_of_mem (show c ∈ {c : State N → ℝ | c (ra i) ∈ Wa i ∧ c (rc i) ∈ Wc i} from hc),
        Set.indicator_of_mem (show ((c (ra i), c (rb i)), (c (rc i), c (rd i))) ∈ S from hc)]
    · rw [Set.indicator_of_notMem (show c ∉ {c : State N → ℝ | c (ra i) ∈ Wa i ∧ c (rc i) ∈ Wc i} from hc),
        Set.indicator_of_notMem (show ((c (ra i), c (rb i)), (c (rc i), c (rd i))) ∉ S from hc)]
  refine (lintegral_congr e1).trans ?_
  rw [lintegral_colLaw_quad (hab i) (hac i) (had i) (hbc i) (hbd i) (hcd i) (hHm.indicator hSm),
    ← lintegral_indicator (hWa i)]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ Wa i
  · rw [Set.indicator_of_mem hy]
    refine lintegral_congr fun u => ?_
    rw [← lintegral_indicator (hWc i)]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ Wc i
    · rw [Set.indicator_of_mem hz]
      refine lintegral_congr fun v => ?_
      exact Set.indicator_of_mem (show ((y, u), (z, v)) ∈ S from ⟨hy, hz⟩) _
    · rw [Set.indicator_of_notMem hz]
      calc _ = ∫⁻ _v : ℝ, (0 : ENNReal) ∂unif :=
            lintegral_congr fun v => Set.indicator_of_notMem (show ((y, u), (z, v)) ∉ S from
              fun h => hz h.2) _
        _ = 0 := by simp
  · rw [Set.indicator_of_notMem hy]
    calc _ = ∫⁻ _u : ℝ, ∫⁻ _z : ℝ, ∫⁻ _v : ℝ, (0 : ENNReal) ∂unif ∂unif ∂unif :=
          lintegral_congr fun u => lintegral_congr fun z => lintegral_congr fun v =>
            Set.indicator_of_notMem (show ((y, u), (z, v)) ∉ S from fun h => hy h.1) _
      _ = 0 := by simp

end Census
end IIT
