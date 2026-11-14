/-
Census of IIT 2.0: second-moment bound for block-dependent averages, and Chebyshev.
If `G x` depends only on the coordinates of the block of `x` (all units), then the terms of
`avg_x G x` with different blocks are independent, and
`E[(avg G - avg E G)^2] ≤ σ² / 2^{|M|}`.
-/
import IIT2.Census.Blocks

namespace IIT2

open MeasureTheory ProbabilityTheory Finset Real

variable {N : ℕ}

/-- Coordinates of the block of `x`, all units. -/
def bset (M : Finset (Fin N)) (x : State N) : Finset (Fin N × State N) :=
  Finset.univ ×ˢ blk M x

lemma abs_avg_le {f : State N → ℝ} {C : ℝ} (h : ∀ x, |f x| ≤ C) : |avg f| ≤ C := by
  rw [abs_le]
  constructor
  · rw [← avg_const (N := N) (-C)]; exact avg_mono fun x => (abs_le.mp (h x)).1
  · rw [← avg_const (N := N) C]; exact avg_mono fun x => (abs_le.mp (h x)).2

lemma measurable_avg {G : State N → Ωf N → ℝ} (hm : ∀ x, Measurable (G x)) :
    Measurable (fun ω => avg (fun x => G x ω)) := by
  unfold avg
  exact (Finset.measurable_sum _ fun x _ => hm x).div_const _

lemma integral_sq_sub_le {f : Ωf N → ℝ} (hf : Measurable f) (C : ℝ) (hb : ∀ ω, |f ω| ≤ C) :
    ∫ ω, (f ω - ∫ ω', f ω' ∂(μP N)) ^ 2 ∂(μP N) ≤ ∫ ω, f ω ^ 2 ∂(μP N) := by
  set m := ∫ ω', f ω' ∂(μP N)
  have hi : Integrable f (μP N) := integrable_of_bdd hf C hb
  have hi2 : Integrable (fun ω => f ω ^ 2) (μP N) :=
    integrable_of_bdd (hf.pow_const 2) (C ^ 2) fun ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb ω) 2
  have hi3 : Integrable (fun ω => (f ω - m) ^ 2) (μP N) :=
    integrable_of_bdd ((hf.sub_const m).pow_const 2) ((C + |m|) ^ 2) fun ω => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by linarith [hb ω])) 2
  have : ∫ ω, f ω ^ 2 ∂(μP N) - ∫ ω, (f ω - m) ^ 2 ∂(μP N) = m ^ 2 := by
    rw [← integral_sub hi2 hi3]
    have : ∀ ω, f ω ^ 2 - (f ω - m) ^ 2 = 2 * m * f ω - m ^ 2 := fun ω => by ring
    simp_rw [this]
    rw [integral_sub (hi.const_mul _) (integrable_const _), integral_const_mul, integral_const]
    simp; ring
  nlinarith [sq_nonneg m]

/-- The variance bound for block-dependent averages. -/
theorem var_avg_le (M : Finset (Fin N)) (G : State N → Ωf N → ℝ)
    (hm : ∀ x, Measurable (G x)) (C : ℝ) (hb : ∀ x ω, |G x ω| ≤ C)
    (hd : ∀ x, DepC (bset M x) (G x)) (σ2 : ℝ) (hσ : ∀ x, ∫ ω, (G x ω) ^ 2 ∂(μP N) ≤ σ2) :
    ∫ ω, (avg (fun x => G x ω) - avg (fun x => ∫ ω', G x ω' ∂(μP N))) ^ 2 ∂(μP N)
      ≤ σ2 / 2 ^ M.card := by
  classical
  set m : State N → ℝ := fun x => ∫ ω', G x ω' ∂(μP N)
  set H : State N → Ωf N → ℝ := fun x ω => G x ω - m x
  set K : ℝ := (Fintype.card (State N) : ℝ)
  have hK : K = 2 ^ N := by simp [K]
  have hKpos : 0 < K := card_pos
  have hHm : ∀ x, Measurable (H x) := fun x => (hm x).sub_const _
  have hHb : ∀ x ω, |H x ω| ≤ C + |m x| := fun x ω =>
    (abs_sub _ _).trans (by linarith [hb x ω])
  have hHd : ∀ x, DepC (bset M x) (H x) := fun x ω ω' h => by
    simp only [H]; rw [hd x ω ω' h]
  have hpt : ∀ ω, (avg (fun x => G x ω) - avg m) ^ 2 =
      (∑ x, ∑ x', H x ω * H x' ω) / K ^ 2 := by
    intro ω
    rw [← avg_sub]
    unfold avg
    rw [div_pow, sq, Finset.sum_mul_sum]
  simp_rw [hpt]
  have hint : ∀ x x', Integrable (fun ω => H x ω * H x' ω) (μP N) := fun x x' =>
    integrable_of_bdd ((hHm x).mul (hHm x')) ((C + |m x|) * (C + |m x'|)) fun ω => by
      rw [abs_mul]
      exact mul_le_mul (hHb x ω) (hHb x' ω) (abs_nonneg _)
        ((abs_nonneg _).trans (hHb x ω))
  rw [integral_div, integral_finset_sum _ fun x _ => integrable_finset_sum _ fun x' _ => hint x x']
  simp_rw [integral_finset_sum _ fun x' _ => hint _ x']
  have hHsq : ∀ x, ∫ ω, H x ω ^ 2 ∂(μP N) ≤ σ2 := fun x =>
    (integral_sq_sub_le (hm x) C (hb x)).trans (hσ x)
  have hterm : ∀ x x', ∫ ω, H x ω * H x' ω ∂(μP N) ≤ if x' ∈ blk M x then σ2 else 0 := by
    intro x x'
    split_ifs with hx
    · have hi2 : ∀ y, Integrable (fun ω => H y ω ^ 2) (μP N) := fun y =>
        integrable_of_bdd ((hHm y).pow_const 2) ((C + |m y|) ^ 2) fun ω => by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hHb y ω) 2
      have hle : ∫ ω, H x ω * H x' ω ∂(μP N) ≤
          ∫ ω, (H x ω ^ 2 + H x' ω ^ 2) / 2 ∂(μP N) :=
        integral_mono (hint x x') (((hi2 x).add (hi2 x')).div_const 2) fun ω => by
          nlinarith [sq_nonneg (H x ω - H x' ω)]
      rw [integral_div, integral_add (hi2 x) (hi2 x')] at hle
      linarith [hHsq x, hHsq x']
    · have hdis : Disjoint (bset M x) (bset M x') :=
        Finset.disjoint_product.mpr (Or.inr (blk_disjoint hx))
      rw [integral_mul_of_depC hdis (hHm x) (hHm x') (hHd x) (hHd x')]
      have : ∫ ω, H x ω ∂(μP N) = 0 := by
        simp only [H]
        rw [integral_sub (integrable_of_bdd (hm x) C (hb x)) (integrable_const _),
          integral_const]
        simp [m]
      rw [this, zero_mul]
  have hsum : ∑ x, ∑ x', ∫ ω, H x ω * H x' ω ∂(μP N) ≤
      ∑ x : State N, σ2 * (2 : ℝ) ^ (N - M.card) := by
    refine Finset.sum_le_sum fun x _ => ?_
    refine (Finset.sum_le_sum fun x' _ => hterm x x').trans (le_of_eq ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have : Finset.univ.filter (fun x' => x' ∈ blk M x) = blk M x := by ext; simp
    rw [this, card_blk]; push_cast; ring
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  change _ / K ^ 2 ≤ _
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsplit := two_pow_split (N := N) M
  have hK' : (Fintype.card (State N) : ℝ) = 2 ^ N := hK
  rw [hK'] at hsum
  rw [hK]
  calc (∑ x, ∑ x', ∫ ω, H x ω * H x' ω ∂(μP N)) * 2 ^ M.card
      ≤ (2 ^ N * (σ2 * 2 ^ (N - M.card))) * 2 ^ M.card :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = σ2 * (2 ^ N) ^ 2 := by rw [hsplit]; ring

/-- Chebyshev's inequality for bounded functions. -/
theorem cheb (F : Ωf N → ℝ) (hF : Measurable F) (C : ℝ) (hb : ∀ ω, |F ω| ≤ C) (c δ : ℝ)
    (hδ : 0 < δ) :
    (μP N).real {ω | δ ≤ |F ω - c|} ≤ (∫ ω, (F ω - c) ^ 2 ∂(μP N)) / δ ^ 2 := by
  have hint : Integrable (fun ω => (F ω - c) ^ 2) (μP N) :=
    integrable_of_bdd ((hF.sub_const c).pow_const 2) ((C + |c|) ^ 2) fun ω => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by linarith [hb ω])) 2
  have h1 := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => sq_nonneg (F ω - c))
    hint (δ ^ 2)
  have h2 : (μP N).real {ω | δ ≤ |F ω - c|} ≤ (μP N).real {ω | δ ^ 2 ≤ (F ω - c) ^ 2} :=
    measureReal_mono (fun ω hω => by
      simp only [Set.mem_setOf_eq] at hω ⊢
      rw [← sq_abs (F ω - c)]
      exact pow_le_pow_left₀ hδ.le hω 2)
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- Chebyshev for a block-dependent average. -/
theorem cheb_avg (M : Finset (Fin N)) (G : State N → Ωf N → ℝ)
    (hm : ∀ x, Measurable (G x)) (C : ℝ) (hb : ∀ x ω, |G x ω| ≤ C)
    (hd : ∀ x, DepC (bset M x) (G x)) (σ2 : ℝ) (hσ : ∀ x, ∫ ω, (G x ω) ^ 2 ∂(μP N) ≤ σ2)
    (δ : ℝ) (hδ : 0 < δ) :
    (μP N).real {ω | δ ≤ |avg (fun x => G x ω) - avg (fun x => ∫ ω', G x ω' ∂(μP N))|}
      ≤ σ2 / 2 ^ M.card / δ ^ 2 := by
  refine (cheb _ (measurable_avg hm) C (fun ω => abs_avg_le fun x => hb x ω) _ δ hδ).trans ?_
  exact div_le_div_of_nonneg_right (var_avg_le M G hm C hb hd σ2 hσ) (by positivity)

end IIT2
