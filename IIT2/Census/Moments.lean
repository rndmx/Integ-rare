/-
Census of IIT 2.0: moments of the single-unit factors `2 a^M_l(x)`.
-/
import IIT2.Census.Variance

namespace IIT2

open MeasureTheory ProbabilityTheory Finset Real

variable {N : ℕ}

/-- `a^M_l(x)` as a random variable. -/
noncomputable def aω (M : Finset (Fin N)) (l : Fin N) (x : State N) (ω : Ωf N) : ℝ :=
  aA (qω ω) M l x

lemma aω_eq (M : Finset (Fin N)) (l : Fin N) (x : State N) (ω : Ωf N) :
    aω M l x ω = (∑ c ∈ blk M x, clamp (ω (l, c))) / 2 ^ (N - M.card) := by
  unfold aω; rw [aA_eq_blk]; rfl

lemma measurable_aω (M : Finset (Fin N)) (l : Fin N) (x : State N) : Measurable (aω M l x) := by
  have : aω M l x = fun ω => (∑ c ∈ blk M x, clamp (ω (l, c))) / 2 ^ (N - M.card) :=
    funext (aω_eq M l x)
  rw [this]
  exact (Finset.measurable_sum _ fun c _ => measurable_clamp.comp (measurable_pi_apply _)).div_const _

lemma aω_nonneg (M : Finset (Fin N)) (l : Fin N) (x : State N) (ω : Ωf N) : 0 ≤ aω M l x ω := by
  rw [aω_eq]; exact div_nonneg (Finset.sum_nonneg fun c _ => clamp_nonneg _) (by positivity)

lemma aω_le_one (M : Finset (Fin N)) (l : Fin N) (x : State N) (ω : Ωf N) : aω M l x ω ≤ 1 := by
  rw [aω_eq, div_le_one (by positivity)]
  calc ∑ c ∈ blk M x, clamp (ω (l, c)) ≤ ∑ c ∈ blk M x, (1 : ℝ) :=
        Finset.sum_le_sum fun c _ => clamp_le_one _
    _ = 2 ^ (N - M.card) := by rw [Finset.sum_const, card_blk]; simp

lemma clamp_le_aω (M : Finset (Fin N)) (l : Fin N) (x : State N) (ω : Ωf N) :
    clamp (ω (l, x)) ≤ 2 ^ (N - M.card) * aω M l x ω := by
  rw [aω_eq, mul_div_cancel₀ _ (by positivity)]
  exact Finset.single_le_sum (f := fun c => clamp (ω (l, c))) (fun c _ => clamp_nonneg _)
    (self_mem_blk M x)

lemma aω_depC_unit (M : Finset (Fin N)) (l : Fin N) (x : State N) :
    DepC (unitSet l) (aω M l x) := fun ω ω' h => by
  rw [aω_eq, aω_eq]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by
    rw [h (l, c) (by simp [unitSet])]

lemma aω_depC_bset (M : Finset (Fin N)) (l : Fin N) (x : State N) :
    DepC (bset M x) (aω M l x) := fun ω ω' h => by
  rw [aω_eq, aω_eq]
  congr 1
  exact Finset.sum_congr rfl fun c hc => by
    rw [h (l, c) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hc⟩)]

lemma aω_depOn (M : Finset (Fin N)) (l : Fin N) (ω : Ωf N) :
    DepOn M (fun x => aω M l x ω) := fun x y hxy => by
  unfold aω aA
  refine avg_congr fun e => ?_
  have : mix M x e = mix M y e := by
    funext j
    by_cases hj : j ∈ M
    · simp [mix, hj, hxy j hj]
    · simp [mix, hj]
  rw [this]

lemma aω_univ (l : Fin N) (x : State N) (ω : Ωf N) :
    aω Finset.univ l x ω = clamp (ω (l, x)) := by
  unfold aω; rw [aA_univ]; rfl

/-! ## Elementary inequalities for `ψ(v) = v log₂ v` -/

lemma log_two_gt : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith

lemma abs_psi_le_two {v : ℝ} (h0 : 0 ≤ v) (h2 : v ≤ 2) : |v * logb 2 v| ≤ 2 := by
  have hl := log_two_gt
  rcases h0.lt_or_eq with hv | hv
  · rcases le_or_gt 1 v with h1 | h1
    · have hb0 : 0 ≤ logb 2 v := Real.logb_nonneg (by norm_num) h1
      have hb1 : logb 2 v ≤ 1 := by
        rw [Real.logb_le_iff_le_rpow (by norm_num) hv]; simpa using h2
      rw [abs_of_nonneg (mul_nonneg h0 hb0)]; nlinarith
    · have hlog : Real.log v ≤ 0 := Real.log_nonpos h0 h1.le
      have h3 := Real.one_sub_inv_le_log_of_pos hv
      have h4 : v * Real.log v ≥ v - 1 := by
        have : v * (1 - v⁻¹) = v - 1 := by field_simp
        nlinarith
      unfold logb
      rw [abs_le]
      constructor
      · rw [mul_div_assoc', le_div_iff₀ (by linarith)]; nlinarith
      · rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  · rw [← hv]; simp

lemma psi_le_quad {v : ℝ} (h0 : 0 ≤ v) :
    v * logb 2 v ≤ ((v - 1) + (v - 1) ^ 2) / Real.log 2 := by
  have hl := log_two_gt
  unfold logb
  rw [mul_div_assoc', div_le_div_iff_of_pos_right (by linarith)]
  rcases h0.lt_or_eq with hv | hv
  · have := Real.log_le_sub_one_of_pos hv
    nlinarith
  · rw [← hv]; simp

lemma abs_q_logb_le (M : Finset (Fin N)) (l : Fin N) (x : State N) (ω : Ωf N) :
    |2 * clamp (ω (l, x)) * logb 2 (2 * aω M l x ω)| ≤ 2 ^ (N - M.card + 1) := by
  have ha0 := aω_nonneg M l x ω
  have hq := clamp_le_aω M l x ω
  have hq0 := clamp_nonneg (ω (l, x))
  rcases ha0.lt_or_eq with ha | ha
  · have hpsi := abs_psi_le_two (v := 2 * aω M l x ω) (by linarith)
      (by linarith [aω_le_one M l x ω])
    rw [abs_mul] at hpsi ⊢
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * clamp (ω (l, x)))]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * aω M l x ω)] at hpsi
    have h2 : 2 * clamp (ω (l, x)) ≤ 2 ^ (N - M.card) * (2 * aω M l x ω) := by nlinarith
    calc 2 * clamp (ω (l, x)) * |logb 2 (2 * aω M l x ω)|
        ≤ 2 ^ (N - M.card) * (2 * aω M l x ω) * |logb 2 (2 * aω M l x ω)| :=
          mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
      _ = 2 ^ (N - M.card) * (2 * aω M l x ω * |logb 2 (2 * aω M l x ω)|) := by ring
      _ ≤ 2 ^ (N - M.card) * 2 := mul_le_mul_of_nonneg_left hpsi (by positivity)
      _ = 2 ^ (N - M.card + 1) := by rw [pow_succ]
  · have : clamp (ω (l, x)) = 0 := by
      rw [← ha, mul_zero] at hq; linarith
    rw [this]; simp

/-! ## Moments of a single clamped uniform -/

lemma integral_clamp (p : Fin N × State N) : ∫ ω, clamp (ω p) ∂(μP N) = 1 / 2 := by
  have := integral_coord_clamp p (fun u => u) measurable_id
  rw [this, integral_id]; norm_num

lemma integrable_clamp (p : Fin N × State N) : Integrable (fun ω => clamp (ω p)) (μP N) :=
  integrable_of_bdd (measurable_clamp.comp (measurable_pi_apply p)) 1 fun ω => by
    rw [abs_of_nonneg (clamp_nonneg _)]; exact clamp_le_one _

lemma integral_clamp_sq (p : Fin N × State N) : ∫ ω, clamp (ω p) ^ 2 ∂(μP N) = 1 / 3 := by
  rw [integral_coord_clamp p (fun u => u ^ 2) (measurable_id.pow_const 2)]
  rw [integral_pow]; norm_num

lemma integral_clamp_centered_sq (p : Fin N × State N) :
    ∫ ω, (clamp (ω p) - 1 / 2) ^ 2 ∂(μP N) = 1 / 12 := by
  rw [integral_coord_clamp p (fun u => (u - 1 / 2) ^ 2)
    ((measurable_id.sub_const _).pow_const 2)]
  rw [intervalIntegral.integral_comp_sub_right (fun u => u ^ 2), integral_pow]
  norm_num

lemma integrable_clamp_fun (p : Fin N × State N) (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ)
    (hC : ∀ u, |g (clamp u)| ≤ C) : Integrable (fun ω => g (clamp (ω p))) (μP N) :=
  integrable_of_bdd (hg.comp (measurable_clamp.comp (measurable_pi_apply p))) C fun ω => hC _

/-! ## Moments of `2 a^M_l(x)` -/

lemma integral_aω (M : Finset (Fin N)) (l : Fin N) (x : State N) :
    ∫ ω, aω M l x ω ∂(μP N) = 1 / 2 := by
  simp_rw [aω_eq]
  rw [integral_div, integral_finset_sum _ fun c _ => integrable_clamp (l, c)]
  simp_rw [integral_clamp]
  rw [Finset.sum_const, card_blk, nsmul_eq_mul]
  have : (2 : ℝ) ^ (N - M.card) ≠ 0 := by positivity
  push_cast
  field_simp

lemma integral_two_aω (M : Finset (Fin N)) (l : Fin N) (x : State N) :
    ∫ ω, 2 * aω M l x ω ∂(μP N) = 1 := by
  rw [integral_const_mul, integral_aω]; norm_num

lemma sq_two_aω_le (M : Finset (Fin N)) (l : Fin N) (x : State N) (ω : Ωf N) :
    (2 * aω M l x ω) ^ 2 ≤ 4 * (∑ c ∈ blk M x, clamp (ω (l, c)) ^ 2) / 2 ^ (N - M.card) := by
  rw [aω_eq]
  have hcs := sq_sum_le_card_mul_sum_sq (s := blk M x) (f := fun c => clamp (ω (l, c)))
  rw [card_blk] at hcs
  push_cast at hcs
  set S := ∑ c ∈ blk M x, clamp (ω (l, c))
  set Q := ∑ c ∈ blk M x, clamp (ω (l, c)) ^ 2
  set P : ℝ := 2 ^ (N - M.card)
  have hp : 0 < P := by positivity
  calc (2 * (S / P)) ^ 2 = 4 * S ^ 2 / P / P := by ring
    _ ≤ 4 * (P * Q) / P / P := by gcongr
    _ = 4 * Q / P := by field_simp

lemma integral_sq_two_aω_le (M : Finset (Fin N)) (l : Fin N) (x : State N) :
    ∫ ω, (2 * aω M l x ω) ^ 2 ∂(μP N) ≤ 4 / 3 := by
  have hint2 : ∀ c, Integrable (fun ω : Ωf N => clamp (ω (l, c)) ^ 2) (μP N) := fun c =>
    integrable_clamp_fun (l, c) (fun u => u ^ 2) (measurable_id.pow_const 2) 1 fun u => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [clamp_nonneg u, clamp_le_one u]
  have hR : Integrable (fun ω : Ωf N =>
      4 * (∑ c ∈ blk M x, clamp (ω (l, c)) ^ 2) / 2 ^ (N - M.card)) (μP N) :=
    ((integrable_finset_sum _ fun c _ => hint2 c).const_mul 4).div_const _
  have hL : Integrable (fun ω => (2 * aω M l x ω) ^ 2) (μP N) :=
    integrable_of_bdd ((measurable_aω M l x).const_mul 2 |>.pow_const 2) 4 fun ω => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [aω_nonneg M l x ω, aω_le_one M l x ω]
  refine (integral_mono hL hR (sq_two_aω_le M l x)).trans (le_of_eq ?_)
  rw [integral_div, integral_const_mul, integral_finset_sum _ fun c _ => hint2 c]
  simp_rw [integral_clamp_sq]
  rw [Finset.sum_const, card_blk]
  have : (2 : ℝ) ^ (N - M.card) ≠ 0 := by positivity
  field_simp
  simp; ring

/-- `E[(2a - 1)^2] = 1/(3 · 2^m)`, here only `≤ 1/12` for `m ≥ 2`. -/
lemma integral_sq_two_aω_sub_one (M : Finset (Fin N)) (l : Fin N) (x : State N)
    (hm : 2 ≤ N - M.card) : ∫ ω, (2 * aω M l x ω - 1) ^ 2 ∂(μP N) ≤ 1 / 12 := by
  set m := N - M.card
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  set X : State N → Ωf N → ℝ := fun c ω => 2 / 2 ^ m * (clamp (ω (l, c)) - 1 / 2)
  have hsum : ∀ ω, 2 * aω M l x ω - 1 = ∑ c ∈ blk M x, X c ω := by
    intro ω
    simp only [X]
    rw [aω_eq, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, card_blk]
    simp only [nsmul_eq_mul]; push_cast
    field_simp
    ring
  have hXm : ∀ c, Measurable (X c) := fun c =>
    ((measurable_clamp.comp (measurable_pi_apply _)).sub_const _).const_mul _
  have hXd : ∀ c, DepC {(l, c)} (X c) := fun c ω ω' h => by
    simp only [X]; rw [h (l, c) (Finset.mem_singleton_self _)]
  have hXb : ∀ c ω, |X c ω| ≤ 2 / 2 ^ m := fun c ω => by
    simp only [X]
    rw [abs_mul, abs_of_pos (by positivity)]
    have : |clamp (ω (l, c)) - 1 / 2| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [clamp_nonneg (ω (l, c)), clamp_le_one (ω (l, c))]
    calc 2 / 2 ^ m * |clamp (ω (l, c)) - 1 / 2| ≤ 2 / 2 ^ m * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 / 2 ^ m := mul_one _
  have hint : ∀ c c', Integrable (fun ω => X c ω * X c' ω) (μP N) := fun c c' =>
    integrable_of_bdd ((hXm c).mul (hXm c')) ((2 / 2 ^ m) * (2 / 2 ^ m)) fun ω => by
      rw [abs_mul]; exact mul_le_mul (hXb c ω) (hXb c' ω) (abs_nonneg _) (by positivity)
  simp_rw [hsum, sq, Finset.sum_mul_sum]
  rw [integral_finset_sum _ fun c _ => integrable_finset_sum _ fun c' _ => hint c c']
  simp_rw [integral_finset_sum _ fun c' _ => hint _ c']
  have hEX : ∀ c, ∫ ω, X c ω ∂(μP N) = 0 := fun c => by
    simp only [X]
    rw [integral_const_mul, integral_sub (integrable_clamp (l, c))
      (integrable_const _), integral_clamp, integral_const]
    simp
  have hterm : ∀ c c', ∫ ω, X c ω * X c' ω ∂(μP N) =
      if c = c' then (2 / 2 ^ m) ^ 2 * (1 / 12) else 0 := by
    intro c c'
    split_ifs with hcc
    · subst hcc
      have : ∀ ω, X c ω * X c ω = (2 / 2 ^ m) ^ 2 * (clamp (ω (l, c)) - 1 / 2) ^ 2 :=
        fun ω => by simp only [X]; ring
      simp_rw [this]
      rw [integral_const_mul, integral_clamp_centered_sq]
    · rw [integral_mul_of_depC (Finset.disjoint_singleton.mpr (fun h => hcc (Prod.ext_iff.mp h).2))
        (hXm c) (hXm c') (hXd c) (hXd c'), hEX, zero_mul]
  simp_rw [hterm]
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_ite_eq (blk M x) c _]
  have : ∀ c ∈ blk M x, (if c ∈ blk M x then (2 / 2 ^ m : ℝ) ^ 2 * (1 / 12) else 0) =
      (2 / 2 ^ m) ^ 2 * (1 / 12) := fun c hc => by rw [if_pos hc]
  rw [Finset.sum_congr rfl this, Finset.sum_const, card_blk, nsmul_eq_mul]
  push_cast
  have h4 : (4 : ℝ) ≤ 2 ^ m := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  rw [div_pow]
  have : (2 : ℝ) ^ m * ((2 : ℝ) ^ 2 / (2 ^ m) ^ 2 * (1 / 12)) = 1 / (3 * 2 ^ m) := by
    field_simp; ring
  rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- `E[ψ(2 a^X_l(x))] = d0 = (ln 2 - 1/2)/ln 2`. -/
lemma integral_psi_univ (l : Fin N) (x : State N) :
    ∫ ω, 2 * aω Finset.univ l x ω * logb 2 (2 * aω Finset.univ l x ω) ∂(μP N) =
      (Real.log 2 - 1 / 2) / Real.log 2 := by
  simp_rw [aω_univ]
  have hm : Measurable (fun u : ℝ => 2 * u * logb 2 (2 * u)) :=
    (measurable_id.const_mul 2).mul ((Real.measurable_log.comp (measurable_id.const_mul 2)).div_const _)
  rw [integral_coord_clamp (l, x) (fun u => 2 * u * logb 2 (2 * u)) hm]
  unfold logb
  have : (fun u : ℝ => 2 * u * (Real.log (2 * u) / Real.log 2)) =
      fun u => (2 * u * Real.log (2 * u)) / Real.log 2 := by funext u; ring
  rw [this, intervalIntegral.integral_div, integral_d0]

lemma measurable_psi_comp {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f) :
    Measurable (fun ω => f ω * logb 2 (f ω)) :=
  hf.mul ((Real.measurable_log.comp hf).div_const _)

/-- For `M ≠ X`: `E[ψ(2 a^M_l(x))] ≤ 0.1311`. -/
lemma integral_psi_le (M : Finset (Fin N)) (hM : M ≠ Finset.univ) (l : Fin N) (x : State N) :
    ∫ ω, 2 * aω M l x ω * logb 2 (2 * aω M l x ω) ∂(μP N) ≤ 1311 / 10000 := by
  have hl := log_two_gt
  have hcard : M.card < N := by
    have := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hM)
    simpa using this
  have hmeas : Measurable (fun ω => 2 * aω M l x ω * logb 2 (2 * aω M l x ω)) :=
    measurable_psi_comp ((measurable_aω M l x).const_mul 2)
  rcases Nat.lt_or_ge (N - M.card) 2 with hm | hm
  · -- m = 1: two independent uniforms
    have hm1 : N - M.card = 1 := by omega
    have hc2 : (blk M x).card = 2 := by rw [card_blk, hm1]; rfl
    obtain ⟨c₁, c₂, hne, hblk⟩ := Finset.card_eq_two.mp hc2
    have ha : ∀ ω, 2 * aω M l x ω = clamp (ω (l, c₁)) + clamp (ω (l, c₂)) := fun ω => by
      rw [aω_eq, hblk, Finset.sum_pair hne, hm1]; ring
    simp_rw [ha]
    have hg : Measurable (Function.uncurry fun u v : ℝ => (u + v) * logb 2 (u + v)) :=
      measurable_psi_comp (f := fun z : ℝ × ℝ => z.1 + z.2) (measurable_fst.add measurable_snd)
    rw [integral_two_coords (p₁ := (l, c₁)) (p₂ := (l, c₂)) (fun h => hne (Prod.ext_iff.mp h).2)
      (fun u v => (u + v) * logb 2 (u + v)) hg 2 (fun u v => abs_psi_le_two
        (by linarith [clamp_nonneg u, clamp_nonneg v]) (by linarith [clamp_le_one u, clamp_le_one v]))]
    unfold logb
    have : ∀ u : ℝ, (fun v : ℝ => (u + v) * (Real.log (u + v) / Real.log 2)) =
        fun v => (u + v) * Real.log (u + v) / Real.log 2 := fun u => by funext v; ring
    simp_rw [this, intervalIntegral.integral_div]
    rw [integral_d1]
    exact d1_lt.le
  · -- m ≥ 2: quadratic bound
    have hle : ∀ ω, 2 * aω M l x ω * logb 2 (2 * aω M l x ω) ≤
        ((2 * aω M l x ω - 1) + (2 * aω M l x ω - 1) ^ 2) / Real.log 2 := fun ω =>
      psi_le_quad (by linarith [aω_nonneg M l x ω])
    have hint1 : Integrable (fun ω => 2 * aω M l x ω - 1) (μP N) :=
      integrable_of_bdd (((measurable_aω M l x).const_mul 2).sub_const 1) 1 fun ω => by
        rw [abs_le]; constructor <;> linarith [aω_nonneg M l x ω, aω_le_one M l x ω]
    have hint2 : Integrable (fun ω => (2 * aω M l x ω - 1) ^ 2) (μP N) :=
      integrable_of_bdd ((((measurable_aω M l x).const_mul 2).sub_const 1).pow_const 2) 1
        fun ω => by
          rw [abs_of_nonneg (sq_nonneg _)]
          nlinarith [aω_nonneg M l x ω, aω_le_one M l x ω]
    have hpsi : Integrable (fun ω => 2 * aω M l x ω * logb 2 (2 * aω M l x ω)) (μP N) :=
      integrable_of_bdd hmeas 2 fun ω => abs_psi_le_two (by linarith [aω_nonneg M l x ω])
        (by linarith [aω_le_one M l x ω])
    have hsi : Integrable (fun ω => ((2 * aω M l x ω - 1) + (2 * aω M l x ω - 1) ^ 2) /
        Real.log 2) (μP N) := (hint1.add hint2).div_const _
    refine (integral_mono hpsi hsi hle).trans ?_
    rw [integral_div, integral_add hint1 hint2]
    have h0 : ∫ ω, (2 * aω M l x ω - 1) ∂(μP N) = 0 := by
      rw [integral_sub ((measurable_aω M l x).const_mul 2 |> fun h =>
        integrable_of_bdd h 2 fun ω => by
          rw [abs_le]; constructor <;> linarith [aω_nonneg M l x ω, aω_le_one M l x ω])
        (integrable_const _), integral_two_aω, integral_const]
      simp
    rw [h0, zero_add]
    have := integral_sq_two_aω_sub_one M l x hm
    calc (∫ ω, (2 * aω M l x ω - 1) ^ 2 ∂(μP N)) / Real.log 2 ≤ (1 / 12) / Real.log 2 :=
          div_le_div_of_nonneg_right this (by linarith)
      _ ≤ 1311 / 10000 := var_bound_lt.le

end IIT2
