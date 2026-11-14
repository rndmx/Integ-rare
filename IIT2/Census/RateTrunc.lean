/-
Census of IIT 2.0, rate: the truncation event. Convex-order bound
`E[(2a)^θ] ≤ 2^θ/(θ+1)` (Jensen for `u ↦ u^θ` on the block average), hence
`E[W_M^θ] ≤ (2^θ/(θ+1))^{|M|}` and Markov: `P(W_M(x) > w₀) ≤ (2^θ/(θ+1))^{|M|} / w₀^θ`.
-/
import IIT2.Census.RateTails

namespace IIT2

open MeasureTheory ProbabilityTheory Finset Real

variable {N : ℕ}

lemma integral_clamp_pow (p : Fin N × State N) (θ : ℕ) :
    ∫ ω, clamp (ω p) ^ θ ∂(μP N) = 1 / (θ + 1) := by
  rw [integral_coord_clamp p (fun u => u ^ θ) (measurable_id.pow_const θ), integral_pow]
  simp

lemma integral_two_a_pow_le (M : Finset (Fin N)) (l : Fin N) (x : State N) (θ : ℕ) :
    ∫ ω, (2 * aω M l x ω) ^ θ ∂(μP N) ≤ 2 ^ θ / (θ + 1) := by
  set m := N - M.card
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have hw' : ∑ _c ∈ blk M x, (1 / (2 : ℝ) ^ m) = 1 := by
    rw [Finset.sum_const, card_blk, nsmul_eq_mul]; push_cast; field_simp; try rfl
  have hpt : ∀ ω, (2 * aω M l x ω) ^ θ ≤
      2 ^ θ * ∑ c ∈ blk M x, (1 / (2 : ℝ) ^ m) * clamp (ω (l, c)) ^ θ := by
    intro ω
    rw [mul_pow, aω_eq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := Real.pow_arith_mean_le_arith_mean_pow (blk M x) (fun _ => 1 / (2 : ℝ) ^ m)
      (fun c => clamp (ω (l, c))) (fun _ _ => by positivity) hw' (fun _ _ => clamp_nonneg _) θ
    have e : (∑ c ∈ blk M x, clamp (ω (l, c))) / 2 ^ (N - M.card) =
        ∑ c ∈ blk M x, (1 / (2 : ℝ) ^ m) * clamp (ω (l, c)) := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun c _ => ?_; ring
    rw [e]; exact this
  have hint : ∀ c, Integrable (fun ω : Ωf N => clamp (ω (l, c)) ^ θ) (μP N) := fun c =>
    integrable_clamp_fun (l, c) (fun u => u ^ θ) (measurable_id.pow_const θ) 1 fun u => by
      rw [abs_of_nonneg (pow_nonneg (clamp_nonneg u) θ)]
      exact pow_le_one₀ (clamp_nonneg u) (clamp_le_one u)
  have hint2 : Integrable (fun ω => 2 ^ θ * ∑ c ∈ blk M x,
      (1 / (2 : ℝ) ^ m) * clamp (ω (l, c)) ^ θ) (μP N) :=
    (integrable_finsetSum _ fun c _ => (hint c).const_mul _).const_mul _
  have hintl : Integrable (fun ω => (2 * aω M l x ω) ^ θ) (μP N) :=
    integrable_of_bdd (((measurable_aω M l x).const_mul 2).pow_const θ) (2 ^ θ) fun ω => by
      rw [abs_of_nonneg (by have := aω_nonneg M l x ω; positivity)]
      exact pow_le_pow_left₀ (by have := aω_nonneg M l x ω; positivity)
        (by linarith [aω_le_one M l x ω]) θ
  refine (integral_mono hintl hint2 hpt).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_finsetSum _ fun c _ => (hint c).const_mul _]
  simp_rw [integral_const_mul, integral_clamp_pow]
  rw [Finset.sum_const, card_blk, nsmul_eq_mul]
  push_cast
  field_simp
  try rfl

lemma integral_W_pow_le (M : Finset (Fin N)) (x : State N) (θ : ℕ) :
    ∫ ω, Wω M x ω ^ θ ∂(μP N) ≤ (2 ^ θ / (θ + 1)) ^ M.card := by
  simp_rw [Wω_eq, ← Finset.prod_pow]
  rw [integral_prod_units M (fun l ω => (2 * aω M l x ω) ^ θ)
    (fun l => ((measurable_aω M l x).const_mul 2).pow_const θ)
    (fun l => (aω_depC_unit M l x).comp' (fun u => (2 * u) ^ θ))]
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod (fun l _ => integral_nonneg fun ω => by
    have := aω_nonneg M l x ω; positivity) fun l _ => integral_two_a_pow_le M l x θ

/-- Markov bound for the truncation event of one `(M, x)`. -/
theorem trunc_prob (M : Finset (Fin N)) (x : State N) (θ : ℕ) (w₀ : ℝ) (hw : 0 < w₀) :
    (μP N).real {ω | w₀ < Wω M x ω} ≤ (2 ^ θ / (θ + 1)) ^ M.card / w₀ ^ θ := by
  have hint : Integrable (fun ω => Wω M x ω ^ θ) (μP N) :=
    integrable_of_bdd ((measurable_Wω M x).pow_const θ) ((2 ^ M.card) ^ θ) fun ω => by
      rw [abs_of_nonneg (pow_nonneg (Wω_nonneg M x ω) θ)]
      exact pow_le_pow_left₀ (Wω_nonneg M x ω) (Wω_le M x ω) θ
  have h1 := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => pow_nonneg (Wω_nonneg M x ω) θ)
    hint (w₀ ^ θ)
  have h2 : (μP N).real {ω | w₀ < Wω M x ω} ≤ (μP N).real {ω | w₀ ^ θ ≤ Wω M x ω ^ θ} :=
    measureReal_mono fun ω hω => by
      simp only [Set.mem_setOf_eq] at hω ⊢
      exact pow_le_pow_left₀ hw.le hω.le θ
  rw [le_div_iff₀ (by positivity)]
  have := integral_W_pow_le M x θ
  nlinarith [pow_pos hw θ]

end IIT2
