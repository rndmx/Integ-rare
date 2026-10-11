/-
Census, B1 lemma LT2, module M6b-2: small balls for weighted sums of distinct entries under `cubeM`.

`lt2_sb_entries`: for an injective family `e : B → State N × Fin N` and weights `0 ≤ c ≤ √V/(16x)`,
`P(x√V ≤ Σ_b c_b (y_{e b} - 1/2)) ≥ e^{-225x²}/4`; `lt2_sb_entries_neg`: the same for `≤ -x√V` (reflection `y ↦ 1-y`).
-/
import IIT.Census.B1LT2Succ
import IIT.Census.B1SmallBall
import IIT.Census.BigPhiBridge

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- **Small ball for distinct entries.** -/
theorem lt2_sb_entries {B : Type*} [Fintype B] [DecidableEq B] (e : B → State N × Fin N)
    (he : Function.Injective e) (c : B → ℝ) (hc0 : ∀ b, 0 ≤ c b) {x V : ℝ} (hx : 1 ≤ x)
    (hV : V = ∑ b, c b ^ 2 / 12) (hV0 : 0 < V) (hb : ∀ b, c b ≤ Real.sqrt V / (16 * x)) :
    ENNReal.ofReal (Real.exp (-(225 * x ^ 2)) / 4) ≤
      cubeM N {η | x * Real.sqrt V ≤ ∑ b, c b * (clamp01 (η (e b).1 (e b).2) - 1 / 2)} := by
  have mp := lt2_mp_inj e he
  have h := small_ball c hc0 hx hV hV0 hb
  have hm : MeasurableSet {ω : B → ℝ | x * Real.sqrt V ≤ sbPi c ω} :=
    measurableSet_le measurable_const (Finset.measurable_sum _ fun b _ =>
      measurable_const.mul ((measurable_clamp01.comp (measurable_pi_apply b)).sub measurable_const))
  rw [← mp.measure_preimage hm.nullMeasurableSet] at h
  exact h

lemma lt2_unif_reflect : MeasurePreserving (fun u : ℝ => 1 - u) unif unif := by
  unfold unif
  have h := (volume : Measure ℝ).measurePreserving_sub_left 1
  have hpre : (fun u : ℝ => 1 - u) ⁻¹' Set.Icc (0 : ℝ) 1 = Set.Icc 0 1 := by
    ext u; simp only [Set.mem_preimage, Set.mem_Icc]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have := h.restrict_preimage (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc
  rw [hpre] at this
  exact this

/-- **Mirrored small ball.** -/
theorem lt2_sb_entries_neg {B : Type*} [Fintype B] [DecidableEq B] (e : B → State N × Fin N)
    (he : Function.Injective e) (c : B → ℝ) (hc0 : ∀ b, 0 ≤ c b) {x V : ℝ} (hx : 1 ≤ x)
    (hV : V = ∑ b, c b ^ 2 / 12) (hV0 : 0 < V) (hb : ∀ b, c b ≤ Real.sqrt V / (16 * x)) :
    ENNReal.ofReal (Real.exp (-(225 * x ^ 2)) / 4) ≤
      cubeM N {η | ∑ b, c b * (clamp01 (η (e b).1 (e b).2) - 1 / 2) ≤ -(x * Real.sqrt V)} := by
  have mp := lt2_mp_inj e he
  have mpR : MeasurePreserving (fun (ω : B → ℝ) (b : B) => 1 - ω b) (Measure.pi fun _ : B => unif)
      (Measure.pi fun _ : B => unif) :=
    measurePreserving_pi (fun _ => unif) (fun _ => unif) fun _ => lt2_unif_reflect
  have h := small_ball c hc0 hx hV hV0 hb
  have hm : MeasurableSet {ω : B → ℝ | x * Real.sqrt V ≤ sbPi c ω} :=
    measurableSet_le measurable_const (Finset.measurable_sum _ fun b _ =>
      measurable_const.mul ((measurable_clamp01.comp (measurable_pi_apply b)).sub measurable_const))
  rw [← mpR.measure_preimage hm.nullMeasurableSet] at h
  have hm2 : MeasurableSet ((fun (ω : B → ℝ) (b : B) => 1 - ω b) ⁻¹' {ω : B → ℝ | x * Real.sqrt V ≤ sbPi c ω}) :=
    mpR.measurable hm
  rw [← mp.measure_preimage hm2.nullMeasurableSet] at h
  refine h.trans (le_of_eq (congrArg _ ?_))
  ext η
  simp only [Set.mem_preimage, Set.mem_setOf_eq, sbPi]
  have e1 : ∑ b, c b * (clamp01 (1 - η (e b).1 (e b).2) - 1 / 2) =
      -∑ b, c b * (clamp01 (η (e b).1 (e b).2) - 1 / 2) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by rw [clamp01_one_sub]; ring
  rw [e1]; constructor <;> intro h <;> linarith

end Census
end IIT
