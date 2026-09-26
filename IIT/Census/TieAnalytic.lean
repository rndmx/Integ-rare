/-
Tie theorem, part 2: zero sets of real-analytic functions are null (`MityaginProof`),
the open cube is open and convex, and the branches are analytic on it (L2).

The clamp in `tpmOf` is harmless: at a point of the open cube each coordinate stays in
`(0,1)` nearby, so every `prob` is locally affine (`AnalyticAt.congr`).
-/
import IIT.Census.TieBranches
import IIT.Census.MityaginProof

namespace IIT
namespace Census

open Finset MeasureTheory Filter Topology

variable {N : ℕ}

/-- **Proved in `MityaginProof.lean`.** The zero set of a real-analytic function that does not vanish
identically on a connected open set is null: if `f` is analytic on an open preconnected set
`U` of a finite-dimensional real space and `f x ≠ 0` for some `x ∈ U`, then
`{x ∈ U | f x = 0}` has Haar measure zero.
(B. Mityagin, *The zero set of a real analytic function*, Math. Notes 2020 /
arXiv:1512.07276.)  Stated there for `ℝⁿ` with Lebesgue measure; the Haar version follows by
a linear isomorphism. -/
theorem volume_zero_set_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U) {f : E → ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hne : ∃ x ∈ U, f x ≠ 0) : μ {x ∈ U | f x = 0} = 0 :=
  volume_zero_set_analytic_thm μ hU hc hf hne

instance isAddHaarMeasure_param : (volume : Measure (Param N)).IsAddHaarMeasure := by
  have := isAddHaarMeasure_volume_pi (Fin N)
  infer_instance

/-! ### The open cube -/

lemma isOpen_openCube (N : ℕ) : IsOpen (openCube N) := by
  have : openCube N = ⋂ r : State N, ⋂ j : Fin N, (fun z : Param N => z r j) ⁻¹' Set.Ioo 0 1 := by
    ext z; simp [openCube]
  rw [this]
  exact isOpen_iInter_of_finite fun r => isOpen_iInter_of_finite fun j =>
    isOpen_Ioo.preimage (by fun_prop)

lemma convex_openCube (N : ℕ) : Convex ℝ (openCube N) := by
  intro x hx y hy a b ha hb hab r j
  exact (convex_Ioo (0 : ℝ) 1) (hx r j) (hy r j) ha hb hab

/-! ### L2: analyticity -/

section Analytic

variable {z0 : Param N}

lemma an_prob (hz : z0 ∈ openCube N) (j : Fin N) (v : State N) (b : Bool) :
    AnalyticAt ℝ (fun z : Param N => (tpmOf z).prob j v b) z0 := by
  have ho : IsOpen {z : Param N | z v j ∈ Set.Ioo (0 : ℝ) 1} :=
    isOpen_Ioo.preimage (by fun_prop)
  have hev : (fun z : Param N => if b then z v j else 1 - z v j) =ᶠ[𝓝 z0]
      fun z => (tpmOf z).prob j v b := by
    filter_upwards [ho.mem_nhds (hz v j)] with z hz'
    show _ = (if b then clamp01 (z v j) else 1 - clamp01 (z v j))
    rw [clamp01_eq (Set.Ioo_subset_Icc_self hz')]
  have hc : AnalyticAt ℝ (fun z : Param N => z v j) z0 :=
    ((ContinuousLinearMap.proj (R := ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : State N => Fin N → ℝ) v)).analyticAt z0
  refine AnalyticAt.congr ?_ hev
  cases b
  · exact analyticAt_const.fun_sub hc
  · exact hc

lemma an_fullProb (hz : z0 ∈ openCube N) (v w : State N) :
    AnalyticAt ℝ (fun z : Param N => fullProb (tpmOf z) v w) z0 := by
  unfold fullProb
  exact Finset.analyticAt_fun_prod _ fun i _ => an_prob hz i v (w i)

lemma an_bgWeight (hz : z0 ∈ openCube N) (s : State N) (S : Finset (Fin N)) (w : State N) :
    AnalyticAt ℝ (fun z : Param N => bgWeight (tpmOf z) S s w) z0 := by
  unfold bgWeight
  refine AnalyticAt.fun_div (AnalyticAt.fun_div ?_ analyticAt_const (by positivity))
    (Finset.analyticAt_fun_sum _ fun v _ => an_fullProb hz v s) (sum_fullProb_pos hz s).ne'
  exact Finset.analyticAt_fun_sum _ fun v _ => an_fullProb hz _ s

lemma an_effUnit (hz : z0 ∈ openCube N) (M : Finset (Fin N)) (m : State N) (j : Fin N)
    (b : Bool) : AnalyticAt ℝ (fun z : Param N => effUnit (tpmOf z) M m j b) z0 := by
  unfold effUnit
  exact AnalyticAt.fun_div (Finset.analyticAt_fun_sum _ fun r _ => an_prob hz j r b)
    analyticAt_const (Nat.cast_ne_zero.2 (card_agree_pos M m).ne')

lemma an_sysCauseProb (hz : z0 ∈ openCube N) (s : State N) (S : Finset (Fin N))
    (t : State N) : AnalyticAt ℝ (fun z : Param N => sysCauseProb (tpmOf z) S s s t) z0 := by
  unfold sysCauseProb
  exact Finset.analyticAt_fun_prod _ fun j _ => AnalyticAt.fun_div
    (Finset.analyticAt_fun_sum _ fun w _ => (an_prob hz _ _ _).fun_mul (an_bgWeight hz s S w))
    analyticAt_const (by positivity)

lemma an_sysPartCauseProb (hz : z0 ∈ openCube N) (s : State N) (S : Finset (Fin N))
    (θ : SysPartition N S) (t : State N) :
    AnalyticAt ℝ (fun z : Param N => sysPartCauseProb (tpmOf z) S s θ s t) z0 := by
  unfold sysPartCauseProb
  exact Finset.analyticAt_fun_prod _ fun j _ => AnalyticAt.fun_div
    (Finset.analyticAt_fun_sum _ fun w _ =>
      (an_effUnit hz _ _ _ _).fun_mul (an_bgWeight hz s S w))
    analyticAt_const (by positivity)

lemma an_sysBackCause (hz : z0 ∈ openCube N) (s : State N) (S : Finset (Fin N))
    (t : State N) : AnalyticAt ℝ (fun z : Param N => sysBackCause (tpmOf z) S s s t) z0 := by
  unfold sysBackCause sysUncCause avgOverStates
  refine AnalyticAt.fun_div (an_sysCauseProb hz s S t) (analyticAt_const.fun_mul
    (AnalyticAt.fun_div (Finset.analyticAt_fun_sum _ fun t _ => an_sysCauseProb hz s S t)
      analyticAt_const (by positivity))) ?_
  have := sysUncCause_pos hz s S
  unfold sysUncCause avgOverStates at this
  positivity

lemma an_sysEffProb (hz : z0 ∈ openCube N) (s : State N) (S : Finset (Fin N))
    (t : State N) : AnalyticAt ℝ (fun z : Param N => sysEffProb (tpmOf z) S s s t) z0 := by
  unfold sysEffProb
  exact Finset.analyticAt_fun_prod _ fun j _ => an_prob hz _ _ _

lemma an_sysPartEffProb (hz : z0 ∈ openCube N) (s : State N) (S : Finset (Fin N))
    (θ : SysPartition N S) (t : State N) :
    AnalyticAt ℝ (fun z : Param N => sysPartEffProb (tpmOf z) S s θ s t) z0 := by
  unfold sysPartEffProb
  exact Finset.analyticAt_fun_prod _ fun j _ => an_effUnit hz _ _ _ _

lemma an_logb_div {f g : Param N → ℝ} (hf : AnalyticAt ℝ f z0) (hg : AnalyticAt ℝ g z0)
    (hf0 : 0 < f z0) (hg0 : 0 < g z0) :
    AnalyticAt ℝ (fun z => Real.logb 2 (f z / g z)) z0 := by
  unfold Real.logb
  have h1 : AnalyticAt ℝ (fun z => f z / g z) z0 := hf.fun_div hg hg0.ne'
  have h2 : AnalyticAt ℝ (fun z => Real.log (f z / g z)) z0 :=
    AnalyticAt.comp (f := fun z => f z / g z) (x := z0) (analyticAt_log (div_pos hf0 hg0)) h1
  exact h2.fun_div analyticAt_const
    (Real.log_pos one_lt_two).ne'

lemma an_BC (hz : z0 ∈ openCube N) (s : State N) (S : Finset (Fin N)) (θ : SysPartition N S)
    (t : State N) : AnalyticAt ℝ (fun z : Param N => BC (tpmOf z) s S θ t) z0 := by
  unfold BC
  exact (an_sysBackCause hz s S t).fun_mul (an_logb_div (an_sysCauseProb hz s S t)
    (an_sysPartCauseProb hz s S θ t) (sysCauseProb_pos hz s S t)
    (sysPartCauseProb_pos hz s S θ t))

lemma an_BE (hz : z0 ∈ openCube N) (s : State N) (S : Finset (Fin N)) (θ : SysPartition N S)
    (t : State N) : AnalyticAt ℝ (fun z : Param N => BE (tpmOf z) s S θ t) z0 := by
  unfold BE
  exact (an_sysEffProb hz s S t).fun_mul (an_logb_div (an_sysEffProb hz s S t)
    (an_sysPartEffProb hz s S θ t) (sysEffProb_pos hz s S t) (sysPartEffProb_pos hz s S θ t))

end Analytic

end Census
end IIT
