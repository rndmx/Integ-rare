/-
Census, B1 small cuts (W12 §6): **exact moments of sums of independent uniforms** under the column law.

`iterD r f a` is the `r`-th forward difference `Δ^r f (a)`; `momF r a n := n!/(n+r)! · Δ^r (x ↦ x^{n+r}) (a)`.
* `integral_iterD` : `∫₀¹ Δ^r g (a+u) du = Δ^{r+1} G (a)` for an antiderivative `G` of `g`;
* `momF_succ` : `momF (r+1) a n = ∫₀¹ momF r (a+u) n du`, `momF_nonneg`;
* `colLaw_split` : a function of `c r` and of the coordinates in `S ∌ r` integrates iteratively;
* **`colLaw_sum_pow`** : `E (a + Σ_{r ∈ S} c_r)^n = momF |S| a n`.
-/
import IIT.Census.B1Rest6Cluster
import IIT.Census.B1ForcedFPos

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-! ### Forward differences -/

/-- The `r`-th forward difference. -/
noncomputable def iterD : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | r + 1, f => fun a => iterD r f (a + 1) - iterD r f a

lemma iterD_succ (r : ℕ) (f : ℝ → ℝ) (a : ℝ) : iterD (r + 1) f a = iterD r f (a + 1) - iterD r f a := rfl

lemma iterD_smul (r : ℕ) (c : ℝ) (f : ℝ → ℝ) (a : ℝ) : iterD r (fun x => c * f x) a = c * iterD r f a := by
  induction r generalizing a with
  | zero => rfl
  | succ r ih => rw [iterD_succ, iterD_succ, ih, ih]; ring

lemma continuous_iterD (r : ℕ) {f : ℝ → ℝ} (hf : Continuous f) : Continuous (iterD r f) := by
  induction r with
  | zero => exact hf
  | succ r ih => exact (ih.comp (continuous_id.add continuous_const)).sub ih

/-- **Integration commutes with the differences.** -/
theorem integral_iterD (r : ℕ) {g G : ℝ → ℝ} (hg : Continuous g) (hG : ∀ x, HasDerivAt G (g x) x) (a : ℝ) :
    ∫ u in (0 : ℝ)..1, iterD r g (a + u) = iterD (r + 1) G a := by
  induction r generalizing a with
  | zero =>
    show ∫ u in (0 : ℝ)..1, g (a + u) = G (a + 1) - G a
    rw [intervalIntegral.integral_comp_add_left g a]
    simp only [add_zero]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hG x) (hg.intervalIntegrable _ _)
  | succ r ih =>
    have hc := continuous_iterD r hg
    have e : (fun u => iterD (r + 1) g (a + u)) = fun u => iterD r g ((a + 1) + u) - iterD r g (a + u) := by
      funext u; rw [iterD_succ]; congr 2; ring
    have i1 : IntervalIntegrable (fun u => iterD r g ((a + 1) + u)) volume 0 1 :=
      (hc.comp (continuous_const.add continuous_id : Continuous fun u : ℝ => (a + 1) + u)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun u => iterD r g (a + u)) volume 0 1 :=
      (hc.comp (continuous_const.add continuous_id : Continuous fun u : ℝ => a + u)).intervalIntegrable _ _
    rw [e, intervalIntegral.integral_sub i1 i2, ih, ih, iterD_succ (r + 1) G a]

/-! ### The moments -/

/-- `E (a + Σ_{i<r} u_i)^n` in closed form. -/
noncomputable def momF (r : ℕ) (a : ℝ) (n : ℕ) : ℝ :=
  (n.factorial : ℝ) / ((n + r).factorial : ℝ) * iterD r (fun x => x ^ (n + r)) a

lemma momF_zero (a : ℝ) (n : ℕ) : momF 0 a n = a ^ n := by
  unfold momF
  have : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [add_zero, iterD]
  rw [div_self this, one_mul]

/-- **The recursion** `momF (r+1) a n = ∫₀¹ momF r (a+u) n du`. -/
theorem momF_succ (r : ℕ) (a : ℝ) (n : ℕ) : momF (r + 1) a n = ∫ u in (0 : ℝ)..1, momF r (a + u) n := by
  unfold momF
  rw [intervalIntegral.integral_const_mul]
  have hG : ∀ x : ℝ, HasDerivAt (fun x => x ^ (n + r + 1) / ((n + r + 1 : ℕ) : ℝ)) (x ^ (n + r)) x := by
    intro x
    have h := (hasDerivAt_pow (n + r + 1) x).div_const ((n + r + 1 : ℕ) : ℝ)
    rw [Nat.add_sub_cancel] at h
    have hc : ((n + r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have e : ((n + r + 1 : ℕ) : ℝ) * x ^ (n + r) / ((n + r + 1 : ℕ) : ℝ) = x ^ (n + r) := by field_simp
    rwa [e] at h
  rw [integral_iterD r (continuous_pow _) hG a]
  have hD : iterD (r + 1) (fun x => x ^ (n + r + 1) / ((n + r + 1 : ℕ) : ℝ)) a =
      (1 / ((n + r + 1 : ℕ) : ℝ)) * iterD (r + 1) (fun x => x ^ (n + (r + 1))) a := by
    rw [← iterD_smul]; congr 1; funext x; rw [show n + (r + 1) = n + r + 1 by ring]; ring
  rw [hD, show n + (r + 1) = n + r + 1 by ring, Nat.factorial_succ]
  push_cast
  have h1 : ((n + r).factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((n : ℝ) + r + 1) ≠ 0 := by positivity
  field_simp

lemma momF_nonneg (r : ℕ) : ∀ a : ℝ, 0 ≤ a → ∀ n : ℕ, 0 ≤ momF r a n := by
  induction r with
  | zero => intro a ha n; rw [momF_zero]; positivity
  | succ r ih =>
    intro a ha n
    rw [momF_succ]
    exact intervalIntegral.integral_nonneg (by norm_num) fun u hu => ih _ (by linarith [hu.1]) n

lemma continuous_momF (r n : ℕ) : Continuous fun a => momF r a n := by
  unfold momF
  exact continuous_const.mul (continuous_iterD r (continuous_pow _))

/-! ### Independence split under the column law -/

/-- A function of `c r` and of the coordinates in `S ∌ r`. -/
theorem colLaw_split (r : State N) (S : Finset (State N)) (hr : r ∉ S) (h : ℝ → (S → ℝ) → ENNReal)
    (hh : Measurable fun p : ℝ × (S → ℝ) => h p.1 p.2) :
    ∫⁻ c, h (c r) (fun i : S => c i) ∂colLaw N =
      ∫⁻ u, ∫⁻ c, h u (fun i : S => c i) ∂colLaw N ∂unif := by
  haveI := colLaw_isProb (N := N)
  have hdisj : Disjoint ({r} : Finset (State N)) S := disjoint_singleton_left.2 hr
  have hind := iIndepFun_colLaw.indepFun_finset {r} S hdisj (fun q => measurable_pi_apply q)
  have hev : Measurable fun v : ({r} : Finset (State N)) → ℝ => v ⟨r, mem_singleton_self r⟩ :=
    measurable_pi_apply _
  have hind2 : IndepFun (fun c : State N → ℝ => c r) (fun c (i : S) => c i) (colLaw N) :=
    hind.comp hev measurable_id
  have hX : Measurable fun c : State N → ℝ => c r := measurable_pi_apply r
  have hY : Measurable fun c : State N → ℝ => fun i : S => c i :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hind2
  have hXmap : (colLaw N).map (fun c => c r) = unif := colLaw_map_eval r
  calc ∫⁻ c, h (c r) (fun i : S => c i) ∂colLaw N
      = ∫⁻ p, h p.1 p.2 ∂(colLaw N).map (fun c => (c r, fun i : S => c i)) :=
        (lintegral_map hh (hX.prodMk hY)).symm
    _ = ∫⁻ p, h p.1 p.2 ∂(unif.prod ((colLaw N).map fun c (i : S) => c i)) := by
        rw [show (fun c : State N → ℝ => (c r, fun i : S => c i)) = fun c => (c r, fun i : S => c i) from rfl,
          hmap, hXmap]
    _ = ∫⁻ u, ∫⁻ v, h u v ∂((colLaw N).map fun c (i : S) => c i) ∂unif := lintegral_prod _ hh.aemeasurable
    _ = ∫⁻ u, ∫⁻ c, h u (fun i : S => c i) ∂colLaw N ∂unif := by
        refine lintegral_congr fun u => ?_
        exact lintegral_map (hh.comp (measurable_const.prodMk measurable_id)) hY

/-! ### The moment identity -/

/-- **`E (a + Σ_{r ∈ S} c_r)^n = momF |S| a n`** under the column law (entries clamped). -/
theorem colLaw_sum_pow (S : Finset (State N)) : ∀ a : ℝ, 0 ≤ a → ∀ n : ℕ,
    ∫⁻ c, ENNReal.ofReal ((a + ∑ r ∈ S, clamp01 (c r)) ^ n) ∂colLaw N = ENNReal.ofReal (momF S.card a n) := by
  haveI := colLaw_isProb (N := N)
  induction S using Finset.induction_on with
  | empty =>
    intro a ha n
    simp [momF_zero]
  | insert r S hr ih =>
    intro a ha n
    have e : ∀ c : State N → ℝ, (a + ∑ q ∈ insert r S, clamp01 (c q)) ^ n =
        ((a + clamp01 (c r)) + ∑ i : S, clamp01 (c i)) ^ n := by
      intro c; rw [sum_insert hr, ← sum_coe_sort S]; ring
    simp_rw [e]
    have hm : Measurable fun p : ℝ × (S → ℝ) =>
        ENNReal.ofReal (((a + clamp01 p.1) + ∑ i : S, clamp01 (p.2 i)) ^ n) :=
      ENNReal.measurable_ofReal.comp (((measurable_const.add (continuous_clamp01.measurable.comp measurable_fst)).add
        (Finset.measurable_sum _ fun i _ => continuous_clamp01.measurable.comp
          ((measurable_pi_apply i).comp measurable_snd))).pow_const n)
    rw [colLaw_split r S hr (fun u v => ENNReal.ofReal (((a + clamp01 u) + ∑ i : S, clamp01 (v i)) ^ n)) hm]
    have hin : ∀ u, ∫⁻ c, ENNReal.ofReal (((a + clamp01 u) + ∑ i : S, clamp01 (c i)) ^ n) ∂colLaw N =
        ENNReal.ofReal (momF S.card (a + clamp01 u) n) := by
      intro u
      have := ih (a + clamp01 u) (add_nonneg ha (clamp01_nonneg u)) n
      rw [← this]
      refine lintegral_congr fun c => ?_
      rw [sum_coe_sort S (fun q => clamp01 (c q))]
    simp_rw [hin]
    have hcm : IntervalIntegrable (fun u => momF S.card (a + u) n) volume 0 1 :=
      ((continuous_momF S.card n).comp (continuous_const.add continuous_id :
        Continuous fun u : ℝ => a + u)).intervalIntegrable 0 1
    rw [lintegral_unif_clamp (fun u => ENNReal.ofReal (momF S.card (a + u) n)),
      lintegral_unif_ofReal hcm (fun u hu => momF_nonneg _ _ (by linarith [hu.1]) n),
      card_insert_of_notMem hr, momF_succ]

end Census
end IIT
