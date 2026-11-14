/-
Census of IIT 2.0: means and second moments of `W_M(x)`, `W_M log W_M`, `W_X log W_M`
(small `m` part of Proposition 5), and the resulting Chebyshev bounds.
-/
import IIT2.Census.Hoeffding

namespace IIT2

open MeasureTheory ProbabilityTheory Finset Real

variable {N : ℕ}

/-- Logarithm of a product, distributed over the factors (zero-safe). -/
lemma prod_mul_logb_prod (s t : Finset (Fin N)) (hst : s ⊆ t) (u v : Fin N → ℝ)
    (h0 : (∃ l ∈ s, v l = 0) → ∏ l ∈ t, u l = 0) :
    (∏ l ∈ t, u l) * logb 2 (∏ l ∈ s, v l) =
      ∑ l ∈ s, ∏ l' ∈ t, (u l' * if l' = l then logb 2 (v l') else 1) := by
  by_cases h : ∀ l ∈ s, v l ≠ 0
  · rw [Real.logb_prod _ _ h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' t l, if_pos (hst hl)]
  · push Not at h
    rw [h0 h, zero_mul]
    refine (Finset.sum_eq_zero fun l hl => ?_).symm
    rw [Finset.prod_mul_distrib, h0 h, zero_mul]

lemma measurable_logb_comp {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f) :
    Measurable (fun ω => logb 2 (f ω)) := (Real.measurable_log.comp hf).div_const _

/-! ## `W_M(x)` -/

noncomputable def Wω (M : Finset (Fin N)) (x : State N) (ω : Ωf N) : ℝ := WA (qω ω) M x

lemma Wω_eq (M : Finset (Fin N)) (x : State N) (ω : Ωf N) :
    Wω M x ω = ∏ l ∈ M, 2 * aω M l x ω := rfl

lemma measurable_Wω (M : Finset (Fin N)) (x : State N) : Measurable (Wω M x) := by
  have : Wω M x = fun ω => ∏ l ∈ M, 2 * aω M l x ω := funext (Wω_eq M x)
  rw [this]
  exact Finset.measurable_prod _ fun l _ => (measurable_aω M l x).const_mul 2

lemma Wω_nonneg (M : Finset (Fin N)) (x : State N) (ω : Ωf N) : 0 ≤ Wω M x ω :=
  Finset.prod_nonneg fun l _ => by have := aω_nonneg M l x ω; positivity

lemma Wω_le (M : Finset (Fin N)) (x : State N) (ω : Ωf N) : Wω M x ω ≤ 2 ^ M.card := by
  rw [Wω_eq, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun l _ => by have := aω_nonneg M l x ω; positivity)
    (fun l _ => by have := aω_le_one M l x ω; linarith)

lemma Wω_depC (M : Finset (Fin N)) (x : State N) : DepC (bset M x) (Wω M x) := fun ω ω' h => by
  rw [Wω_eq, Wω_eq]
  exact Finset.prod_congr rfl fun l _ => by rw [aω_depC_bset M l x ω ω' h]

lemma Wω_univ (x : State N) (ω : Ωf N) :
    Wω Finset.univ x ω = ∏ l, 2 * clamp (ω (l, x)) := by
  rw [Wω_eq]; simp_rw [aω_univ]

lemma integral_Wω (M : Finset (Fin N)) (x : State N) : ∫ ω, Wω M x ω ∂(μP N) = 1 := by
  simp_rw [Wω_eq]
  rw [integral_prod_units M (fun l ω => 2 * aω M l x ω)
    (fun l => (measurable_aω M l x).const_mul 2)
    (fun l ω ω' h => by simp only; rw [aω_depC_unit M l x ω ω' h])]
  simp_rw [integral_two_aω]; simp

lemma integral_Wω_sq (M : Finset (Fin N)) (x : State N) :
    ∫ ω, Wω M x ω ^ 2 ∂(μP N) ≤ (4 / 3) ^ M.card := by
  simp_rw [Wω_eq, ← Finset.prod_pow]
  rw [integral_prod_units M (fun l ω => (2 * aω M l x ω) ^ 2)
    (fun l => ((measurable_aω M l x).const_mul 2).pow_const 2)
    (fun l ω ω' h => by simp only; rw [aω_depC_unit M l x ω ω' h])]
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod (fun l _ => integral_nonneg fun ω => sq_nonneg _)
    (fun l _ => integral_sq_two_aω_le M l x)

/-! ## `W_M log W_M` -/

noncomputable def FY (M : Finset (Fin N)) (l : Fin N) (x : State N) (l' : Fin N) (ω : Ωf N) : ℝ :=
  2 * aω M l' x ω * if l' = l then logb 2 (2 * aω M l' x ω) else 1

noncomputable def GY (M : Finset (Fin N)) (x : State N) (ω : Ωf N) : ℝ :=
  Wω M x ω * logb 2 (Wω M x ω)

lemma GY_eq (M : Finset (Fin N)) (x : State N) (ω : Ωf N) :
    GY M x ω = ∑ l ∈ M, ∏ l' ∈ M, FY M l x l' ω := by
  unfold GY FY
  rw [Wω_eq]
  exact prod_mul_logb_prod M M subset_rfl _ _ fun ⟨l, hl, h⟩ => Finset.prod_eq_zero hl h

lemma measurable_FY (M : Finset (Fin N)) (l : Fin N) (x : State N) (l' : Fin N) :
    Measurable (FY M l x l') := by
  unfold FY
  by_cases h : l' = l
  · simp only [h, if_true]
    exact ((measurable_aω M l x).const_mul 2).mul
      (measurable_logb_comp ((measurable_aω M l x).const_mul 2))
  · simp only [h, if_false, mul_one]; exact (measurable_aω M l' x).const_mul 2

lemma FY_depC_unit (M : Finset (Fin N)) (l : Fin N) (x : State N) (l' : Fin N) :
    DepC (unitSet l') (FY M l x l') := fun ω ω' h => by
  unfold FY; rw [aω_depC_unit M l' x ω ω' h]

lemma FY_depC_bset (M : Finset (Fin N)) (l : Fin N) (x : State N) (l' : Fin N) :
    DepC (bset M x) (FY M l x l') := fun ω ω' h => by
  unfold FY; rw [aω_depC_bset M l' x ω ω' h]

lemma abs_FY_le (M : Finset (Fin N)) (l : Fin N) (x : State N) (l' : Fin N) (ω : Ωf N) :
    |FY M l x l' ω| ≤ 2 := by
  have h0 := aω_nonneg M l' x ω
  have h1 := aω_le_one M l' x ω
  unfold FY
  split_ifs
  · exact abs_psi_le_two (by linarith) (by linarith)
  · rw [mul_one, abs_of_nonneg (by linarith)]; linarith

lemma integral_FY (M : Finset (Fin N)) (l : Fin N) (x : State N) (l' : Fin N) :
    ∫ ω, FY M l x l' ω ∂(μP N) =
      if l' = l then ∫ ω, 2 * aω M l x ω * logb 2 (2 * aω M l x ω) ∂(μP N) else 1 := by
  unfold FY
  split_ifs with h
  · subst h; rfl
  · simp_rw [mul_one]; exact integral_two_aω M l' x

lemma integral_FY_sq (M : Finset (Fin N)) (l : Fin N) (x : State N) (l' : Fin N) :
    ∫ ω, FY M l x l' ω ^ 2 ∂(μP N) ≤ 4 / 3 * (if l' = l then 3 else 1) := by
  by_cases h : l' = l
  · rw [if_pos h]
    have : ∀ ω, FY M l x l' ω ^ 2 ≤ 4 := fun ω => by
      have := abs_FY_le M l x l' ω
      nlinarith [sq_abs (FY M l x l' ω), abs_nonneg (FY M l x l' ω)]
    calc ∫ ω, FY M l x l' ω ^ 2 ∂(μP N) ≤ ∫ ω, (4 : ℝ) ∂(μP N) :=
          integral_mono (integrable_of_bdd ((measurable_FY M l x l').pow_const 2) 4 fun ω => by
            rw [abs_of_nonneg (sq_nonneg _)]; exact this ω) (integrable_const _) this
      _ = 4 / 3 * 3 := by simp <;> norm_num
  · rw [if_neg h, mul_one]
    unfold FY
    simp only [h, if_false, mul_one]
    exact integral_sq_two_aω_le M l' x

lemma integral_GY (M : Finset (Fin N)) (x : State N) :
    ∫ ω, GY M x ω ∂(μP N) =
      ∑ l ∈ M, ∫ ω, 2 * aω M l x ω * logb 2 (2 * aω M l x ω) ∂(μP N) := by
  simp_rw [GY_eq]
  rw [integral_finset_sum _ fun l _ => integrable_of_bdd
    (Finset.measurable_prod _ fun l' _ => measurable_FY M l x l') (2 ^ M.card) fun ω => by
      rw [Finset.abs_prod, ← Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun l' _ => abs_FY_le M l x l' ω]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [integral_prod_units M (FY M l x) (measurable_FY M l x) (FY_depC_unit M l x)]
  simp_rw [integral_FY]
  rw [Finset.prod_ite_eq' M l, if_pos hl]

lemma abs_GY_le (M : Finset (Fin N)) (x : State N) (ω : Ωf N) :
    |GY M x ω| ≤ M.card * 2 ^ M.card := by
  rw [GY_eq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ l ∈ M, |∏ l' ∈ M, FY M l x l' ω| ≤ 2 ^ M.card := fun l _ => by
    rw [Finset.abs_prod, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun l' _ => abs_FY_le M l x l' ω
  refine (Finset.sum_le_sum this).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]

lemma integral_GY_sq (M : Finset (Fin N)) (x : State N) :
    ∫ ω, GY M x ω ^ 2 ∂(μP N) ≤ M.card * (M.card * (3 * (4 / 3) ^ M.card)) := by
  have hT : ∀ l ∈ M, ∫ ω, (∏ l' ∈ M, FY M l x l' ω) ^ 2 ∂(μP N) ≤ 3 * (4 / 3) ^ M.card := by
    intro l hl
    simp_rw [← Finset.prod_pow]
    rw [integral_prod_units M (fun l' ω => FY M l x l' ω ^ 2)
      (fun l' => (measurable_FY M l x l').pow_const 2)
      (fun l' ω ω' h => by simp only; rw [FY_depC_unit M l x l' ω ω' h])]
    calc ∏ l' ∈ M, ∫ ω, FY M l x l' ω ^ 2 ∂(μP N)
        ≤ ∏ l' ∈ M, (4 / 3 * (if l' = l then (3 : ℝ) else 1)) :=
          Finset.prod_le_prod (fun _ _ => integral_nonneg fun ω => sq_nonneg _)
            fun l' _ => integral_FY_sq M l x l'
      _ = 3 * (4 / 3) ^ M.card := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_ite_eq' M l, if_pos hl]
          ring
  have hpt : ∀ ω, GY M x ω ^ 2 ≤ M.card * ∑ l ∈ M, (∏ l' ∈ M, FY M l x l' ω) ^ 2 := fun ω => by
    rw [GY_eq]; exact sq_sum_le_card_mul_sum_sq
  have hint : ∀ l, Integrable (fun ω => (∏ l' ∈ M, FY M l x l' ω) ^ 2) (μP N) := fun l =>
    integrable_of_bdd ((Finset.measurable_prod _ fun l' _ => measurable_FY M l x l').pow_const 2)
      ((2 ^ M.card) ^ 2) fun ω => by
        rw [abs_pow]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        rw [Finset.abs_prod, ← Finset.prod_const]
        exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun l' _ => abs_FY_le M l x l' ω
  have hmeasGY : Measurable (GY M x) :=
    (measurable_Wω M x).mul (measurable_logb_comp (measurable_Wω M x))
  calc ∫ ω, GY M x ω ^ 2 ∂(μP N)
      ≤ ∫ ω, (M.card : ℝ) * ∑ l ∈ M, (∏ l' ∈ M, FY M l x l' ω) ^ 2 ∂(μP N) :=
        integral_mono (integrable_of_bdd (hmeasGY.pow_const 2) ((M.card * 2 ^ M.card) ^ 2)
          fun ω => by
            rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_GY_le M x ω) 2)
          ((integrable_finset_sum _ fun l _ => hint l).const_mul _) hpt
    _ = M.card * ∑ l ∈ M, ∫ ω, (∏ l' ∈ M, FY M l x l' ω) ^ 2 ∂(μP N) := by
        rw [integral_const_mul, integral_finset_sum _ fun l _ => hint l]
    _ ≤ M.card * ∑ l ∈ M, (3 * (4 / 3 : ℝ) ^ M.card) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hT) (by positivity)
    _ = M.card * (M.card * (3 * (4 / 3) ^ M.card)) := by rw [Finset.sum_const, nsmul_eq_mul]

lemma measurable_GY (M : Finset (Fin N)) (x : State N) : Measurable (GY M x) :=
  (measurable_Wω M x).mul (measurable_logb_comp (measurable_Wω M x))

lemma GY_depC (M : Finset (Fin N)) (x : State N) : DepC (bset M x) (GY M x) := fun ω ω' h => by
  unfold GY; rw [Wω_depC M x ω ω' h]

/-! ## `W_X log W_M` -/

noncomputable def FT (M : Finset (Fin N)) (l : Fin N) (x : State N) (l' : Fin N) (ω : Ωf N) : ℝ :=
  2 * clamp (ω (l', x)) * if l' = l then logb 2 (2 * aω M l' x ω) else 1

noncomputable def GT (M : Finset (Fin N)) (x : State N) (ω : Ωf N) : ℝ :=
  Wω Finset.univ x ω * logb 2 (Wω M x ω)

lemma GT_eq (M : Finset (Fin N)) (x : State N) (ω : Ωf N) :
    GT M x ω = ∑ l ∈ M, ∏ l' ∈ Finset.univ, FT M l x l' ω := by
  unfold GT FT
  rw [Wω_univ, Wω_eq]
  refine prod_mul_logb_prod M Finset.univ (Finset.subset_univ M) _ _ fun ⟨l, hl, h⟩ => ?_
  refine Finset.prod_eq_zero (Finset.mem_univ l) ?_
  have hq := clamp_le_aω M l x ω
  have : aω M l x ω = 0 := by linarith
  rw [this, mul_zero] at hq
  have := clamp_nonneg (ω (l, x))
  have : clamp (ω (l, x)) = 0 := by linarith
  rw [this, mul_zero]

lemma measurable_FT (M : Finset (Fin N)) (l : Fin N) (x : State N) (l' : Fin N) :
    Measurable (FT M l x l') := by
  unfold FT
  have hc : Measurable (fun ω : Ωf N => 2 * clamp (ω (l', x))) :=
    (measurable_clamp.comp (measurable_pi_apply _)).const_mul 2
  by_cases h : l' = l
  · simp only [h, if_true]
    exact (h ▸ hc).mul (measurable_logb_comp ((measurable_aω M l x).const_mul 2))
  · simp only [h, if_false, mul_one]; exact hc

lemma FT_depC_unit (M : Finset (Fin N)) (l : Fin N) (x : State N) (l' : Fin N) :
    DepC (unitSet l') (FT M l x l') := fun ω ω' h => by
  unfold FT
  rw [aω_depC_unit M l' x ω ω' h, h (l', x) (by simp [unitSet])]

lemma abs_FT_le (M : Finset (Fin N)) (l : Fin N) (x : State N) (l' : Fin N) (ω : Ωf N) :
    |FT M l x l' ω| ≤ 2 ^ (N - M.card + 1) := by
  unfold FT
  split_ifs with h
  · exact abs_q_logb_le M l' x ω
  · rw [mul_one, abs_of_nonneg (by have := clamp_nonneg (ω (l', x)); positivity)]
    have := clamp_le_one (ω (l', x))
    have : (2 : ℝ) ≤ 2 ^ (N - M.card + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (N - M.card + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith

lemma integral_FT_sq (M : Finset (Fin N)) (l : Fin N) (x : State N) (l' : Fin N) :
    ∫ ω, FT M l x l' ω ^ 2 ∂(μP N) ≤ 4 / 3 * (if l' = l then 3 * 4 ^ (N - M.card) else 1) := by
  by_cases h : l' = l
  · rw [if_pos h]
    have hb : ∀ ω, FT M l x l' ω ^ 2 ≤ 4 ^ (N - M.card + 1) := fun ω => by
      have := abs_FT_le M l x l' ω
      calc FT M l x l' ω ^ 2 = |FT M l x l' ω| ^ 2 := (sq_abs _).symm
        _ ≤ (2 ^ (N - M.card + 1)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = 4 ^ (N - M.card + 1) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    calc ∫ ω, FT M l x l' ω ^ 2 ∂(μP N) ≤ ∫ ω, ((4 : ℝ) ^ (N - M.card + 1)) ∂(μP N) :=
          integral_mono (integrable_of_bdd ((measurable_FT M l x l').pow_const 2)
            (4 ^ (N - M.card + 1)) fun ω => by
              rw [abs_of_nonneg (sq_nonneg _)]; exact hb ω) (integrable_const _) hb
      _ = 4 / 3 * (3 * 4 ^ (N - M.card)) := by simp; rw [pow_succ]; ring
  · rw [if_neg h, mul_one]
    unfold FT
    simp only [h, if_false, mul_one]
    have : ∀ ω : Ωf N, (2 * clamp (ω (l', x))) ^ 2 = 4 * clamp (ω (l', x)) ^ 2 := fun ω => by ring
    simp_rw [this]
    rw [integral_const_mul, integral_clamp_sq]; norm_num

lemma integral_FT (M : Finset (Fin N)) (l : Fin N) (x : State N) (l' : Fin N) :
    ∫ ω, FT M l x l' ω ∂(μP N) =
      if l' = l then ∫ ω, 2 * clamp (ω (l, x)) * logb 2 (2 * aω M l x ω) ∂(μP N) else 1 := by
  unfold FT
  split_ifs with h
  · subst h; rfl
  · simp_rw [mul_one]
    rw [integral_const_mul, integral_clamp]; norm_num

lemma measurable_GT (M : Finset (Fin N)) (x : State N) : Measurable (GT M x) :=
  (measurable_Wω _ x).mul (measurable_logb_comp (measurable_Wω M x))

lemma GT_depC (M : Finset (Fin N)) (x : State N) : DepC (bset M x) (GT M x) := fun ω ω' h => by
  unfold GT
  rw [Wω_depC M x ω ω' h]
  congr 1
  rw [Wω_univ, Wω_univ]
  exact Finset.prod_congr rfl fun l _ => by
    rw [h (l, x) (Finset.mem_product.mpr ⟨Finset.mem_univ _, self_mem_blk M x⟩)]

lemma abs_termT_le (M : Finset (Fin N)) (l : Fin N) (x : State N) (ω : Ωf N) :
    |∏ l' ∈ Finset.univ, FT M l x l' ω| ≤ (2 ^ (N - M.card + 1)) ^ N := by
  rw [Finset.abs_prod]
  calc ∏ l' ∈ Finset.univ, |FT M l x l' ω| ≤ ∏ _l' ∈ (Finset.univ : Finset (Fin N)),
        (2 : ℝ) ^ (N - M.card + 1) :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun l' _ => abs_FT_le M l x l' ω
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma abs_GT_le (M : Finset (Fin N)) (x : State N) (ω : Ωf N) :
    |GT M x ω| ≤ M.card * (2 ^ (N - M.card + 1)) ^ N := by
  rw [GT_eq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun l _ => abs_termT_le M l x ω).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]

lemma integral_GT (M : Finset (Fin N)) (x : State N) :
    ∫ ω, GT M x ω ∂(μP N) =
      ∑ l ∈ M, ∫ ω, 2 * clamp (ω (l, x)) * logb 2 (2 * aω M l x ω) ∂(μP N) := by
  simp_rw [GT_eq]
  rw [integral_finset_sum _ fun l _ => integrable_of_bdd
    (Finset.measurable_prod _ fun l' _ => measurable_FT M l x l') _ (abs_termT_le M l x)]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [integral_prod_units _ (FT M l x) (measurable_FT M l x) (FT_depC_unit M l x)]
  simp_rw [integral_FT]
  rw [Finset.prod_ite_eq' _ l, if_pos (Finset.mem_univ l)]

lemma integral_GT_sq (M : Finset (Fin N)) (x : State N) :
    ∫ ω, GT M x ω ^ 2 ∂(μP N) ≤
      M.card * (M.card * (3 * 4 ^ (N - M.card) * (4 / 3) ^ N)) := by
  have hT : ∀ l ∈ M, ∫ ω, (∏ l' ∈ Finset.univ, FT M l x l' ω) ^ 2 ∂(μP N) ≤
      3 * 4 ^ (N - M.card) * (4 / 3) ^ N := by
    intro l hl
    simp_rw [← Finset.prod_pow]
    rw [integral_prod_units _ (fun l' ω => FT M l x l' ω ^ 2)
      (fun l' => (measurable_FT M l x l').pow_const 2)
      (fun l' ω ω' h => by simp only; rw [FT_depC_unit M l x l' ω ω' h])]
    calc ∏ l' ∈ Finset.univ, ∫ ω, FT M l x l' ω ^ 2 ∂(μP N)
        ≤ ∏ l' ∈ Finset.univ, (4 / 3 * (if l' = l then (3 * 4 ^ (N - M.card) : ℝ) else 1)) :=
          Finset.prod_le_prod (fun _ _ => integral_nonneg fun ω => sq_nonneg _)
            fun l' _ => integral_FT_sq M l x l'
      _ = 3 * 4 ^ (N - M.card) * (4 / 3) ^ N := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_ite_eq' _ l,
            if_pos (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin]
          ring
  have hpt : ∀ ω, GT M x ω ^ 2 ≤
      M.card * ∑ l ∈ M, (∏ l' ∈ Finset.univ, FT M l x l' ω) ^ 2 := fun ω => by
    rw [GT_eq]; exact sq_sum_le_card_mul_sum_sq
  have hint : ∀ l, Integrable (fun ω => (∏ l' ∈ Finset.univ, FT M l x l' ω) ^ 2) (μP N) :=
    fun l => integrable_of_bdd
      ((Finset.measurable_prod _ fun l' _ => measurable_FT M l x l').pow_const 2)
      ((((2 : ℝ) ^ (N - M.card + 1)) ^ N) ^ 2) fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_termT_le M l x ω) 2
  calc ∫ ω, GT M x ω ^ 2 ∂(μP N)
      ≤ ∫ ω, (M.card : ℝ) * ∑ l ∈ M, (∏ l' ∈ Finset.univ, FT M l x l' ω) ^ 2 ∂(μP N) :=
        integral_mono (integrable_of_bdd ((measurable_GT M x).pow_const 2) _ fun ω => by
            rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_GT_le M x ω) 2)
          ((integrable_finset_sum _ fun l _ => hint l).const_mul _) hpt
    _ = M.card * ∑ l ∈ M, ∫ ω, (∏ l' ∈ Finset.univ, FT M l x l' ω) ^ 2 ∂(μP N) := by
        rw [integral_const_mul, integral_finset_sum _ fun l _ => hint l]
    _ ≤ M.card * ∑ l ∈ M, (3 * 4 ^ (N - M.card) * (4 / 3 : ℝ) ^ N) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hT) (by positivity)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ## Means of the averages -/

lemma integrable_q_logb (M : Finset (Fin N)) (l : Fin N) (x : State N) :
    Integrable (fun ω => 2 * clamp (ω (l, x)) * logb 2 (2 * aω M l x ω)) (μP N) :=
  integrable_of_bdd (((measurable_clamp.comp (measurable_pi_apply _)).const_mul 2).mul
    (measurable_logb_comp ((measurable_aω M l x).const_mul 2))) _ (abs_q_logb_le M l x)

lemma integrable_psi_a (M : Finset (Fin N)) (l : Fin N) (x : State N) :
    Integrable (fun ω => 2 * aω M l x ω * logb 2 (2 * aω M l x ω)) (μP N) :=
  integrable_of_bdd (measurable_psi_comp ((measurable_aω M l x).const_mul 2)) 2 fun ω =>
    abs_psi_le_two (by linarith [aω_nonneg M l x ω]) (by linarith [aω_le_one M l x ω])

lemma integral_avg {f : State N → Ωf N → ℝ} (hf : ∀ x, Integrable (f x) (μP N)) :
    ∫ ω, avg (fun x => f x ω) ∂(μP N) = avg (fun x => ∫ ω, f x ω ∂(μP N)) := by
  unfold avg
  rw [integral_div, integral_finset_sum _ fun x _ => hf x]

/-- Mixing in expectation: `avg_x E[2 q_l(x) log₂ 2a_l(x)] = avg_x E[ψ(2 a_l(x))]`. -/
lemma avg_integral_q_logb (M : Finset (Fin N)) (l : Fin N) :
    avg (fun x => ∫ ω, 2 * clamp (ω (l, x)) * logb 2 (2 * aω M l x ω) ∂(μP N)) =
      avg (fun x => ∫ ω, 2 * aω M l x ω * logb 2 (2 * aω M l x ω) ∂(μP N)) := by
  rw [← integral_avg (integrable_q_logb M l), ← integral_avg (integrable_psi_a M l)]
  congr 1; funext ω
  have hdep : DepOn M (fun x => 2 * logb 2 (2 * aω M l x ω)) := fun x y h => by
    have := aω_depOn M l ω x y h; simp only at this ⊢; rw [this]
  have := avg_q_mul_eq (qω ω) M l _ hdep
  have e1 : ∀ x, 2 * clamp (ω (l, x)) * logb 2 (2 * aω M l x ω) =
      qω ω l x * (2 * logb 2 (2 * aω M l x ω)) := fun x => by simp only [qω]; ring
  have e2 : ∀ x, 2 * aω M l x ω * logb 2 (2 * aω M l x ω) =
      aA (qω ω) M l x * (2 * logb 2 (2 * aω M l x ω)) := fun x => by simp only [aω]; ring
  rw [avg_congr e1, avg_congr e2, this]

lemma meanT_eq (M : Finset (Fin N)) :
    avg (fun x => ∫ ω, GT M x ω ∂(μP N)) =
      ∑ l ∈ M, avg (fun x => ∫ ω, 2 * aω M l x ω * logb 2 (2 * aω M l x ω) ∂(μP N)) := by
  simp_rw [integral_GT]
  rw [avg_sum]
  exact Finset.sum_congr rfl fun l _ => avg_integral_q_logb M l

lemma meanY_eq (M : Finset (Fin N)) :
    avg (fun x => ∫ ω, GY M x ω ∂(μP N)) =
      ∑ l ∈ M, avg (fun x => ∫ ω, 2 * aω M l x ω * logb 2 (2 * aω M l x ω) ∂(μP N)) := by
  simp_rw [integral_GY]
  rw [avg_sum]

lemma mean_le (M : Finset (Fin N)) (hM : M ≠ Finset.univ) :
    ∑ l ∈ M, avg (fun x => ∫ ω, 2 * aω M l x ω * logb 2 (2 * aω M l x ω) ∂(μP N)) ≤
      1311 / 10000 * N := by
  calc _ ≤ ∑ _l ∈ M, (1311 / 10000 : ℝ) := Finset.sum_le_sum fun l _ => by
        rw [← avg_const (N := N) (1311 / 10000 : ℝ)]
        exact avg_mono fun x => integral_psi_le M hM l x
    _ = M.card * (1311 / 10000) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ N * (1311 / 10000) := by
        have := Finset.card_le_univ M; simp only [Fintype.card_fin] at this
        have : (M.card : ℝ) ≤ N := by exact_mod_cast this
        nlinarith
    _ = _ := by ring

lemma mean_univ :
    ∑ l ∈ (Finset.univ : Finset (Fin N)), avg (fun x => ∫ ω, 2 * aω Finset.univ l x ω *
      logb 2 (2 * aω Finset.univ l x ω) ∂(μP N)) = N * ((Real.log 2 - 1 / 2) / Real.log 2) := by
  simp_rw [integral_psi_univ, avg_const]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end IIT2
