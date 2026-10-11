/-
Census, B1 lemma LT2, module M3 part 1 (`iit-census/lean/LT2-PLAN.md`; W2 §3-4, Lemmas P1a and AC).

* Characters `lt2Chi T v = ∏_{j ∈ T} (±1)` on states, their orthogonality `Σ_v χ_T χ_{T'} = 2^N 1{T = T'}`.
* `lt2_count_union`: if `m` of the statistics of a family are `≥ K` in absolute value, some signed sum over an
  `m`-subset is `≥ m K`; a union over the `C(d, m)` subsets and `2^m` sign patterns.
* `lt2_rowlin_tail`: Bernstein for a row-local linear statistic `Σ_v g(w v) c_v` with `Σ_v c_v = 0`.
* The weight statistics `m_T = Σ_v P_ns(v) χ_T(v)`: signed sums have variance `≤ σ_N² |A|` (Parseval), summands
  `≤ 2θ|A|`, hence `lt2_mT_count`.
-/
import IIT.Census.B1LT2Sp
import IIT.Census.Bernstein
import IIT.Census.ColSplit

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-! ### Characters -/

/-- The character `χ_T(v) = ∏_{j ∈ T} (-1)^{v_j}`. -/
noncomputable def lt2Chi (T : Finset (Fin N)) (v : State N) : ℝ := ∏ j ∈ T, if v j then -1 else 1

lemma lt2Chi_sq (T : Finset (Fin N)) (v : State N) : lt2Chi T v * lt2Chi T v = 1 := by
  unfold lt2Chi; rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun j _ => by split_ifs <;> norm_num

lemma lt2Chi_abs (T : Finset (Fin N)) (v : State N) : |lt2Chi T v| = 1 := by
  unfold lt2Chi; rw [Finset.abs_prod]; exact Finset.prod_eq_one fun j _ => by split_ifs <;> norm_num

lemma lt2Chi_mul (T T' : Finset (Fin N)) (v : State N) :
    lt2Chi T v * lt2Chi T' v = lt2Chi (symmDiff T T') v := by
  unfold lt2Chi
  have hsplit : ∀ U : Finset (Fin N), (∏ j ∈ U, if v j then (-1 : ℝ) else 1) =
      ∏ j ∈ univ, if j ∈ U then (if v j then -1 else 1) else 1 := by
    intro U; rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [hsplit T, hsplit T', hsplit (symmDiff T T'), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Finset.mem_symmDiff]
  by_cases h1 : j ∈ T <;> by_cases h2 : j ∈ T' <;> simp [h1, h2] <;> split_ifs <;> norm_num

/-- Flip of one coordinate. -/
lemma lt2Chi_flip {T : Finset (Fin N)} {j : Fin N} (hj : j ∈ T) (v : State N) :
    lt2Chi T (Function.update v j (!v j)) = -lt2Chi T v := by
  unfold lt2Chi
  rw [← Finset.mul_prod_erase T _ hj, ← Finset.mul_prod_erase T _ hj]
  have hrest : ∏ k ∈ T.erase j, (if Function.update v j (!v j) k then (-1 : ℝ) else 1) =
      ∏ k ∈ T.erase j, (if v k then (-1 : ℝ) else 1) :=
    Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [hrest, Function.update_self]
  cases v j <;> simp

/-- **`Σ_v χ_T(v) = 0` for `T ≠ ∅`** (pair `v` with its flip at a point of `T`). -/
lemma lt2_sum_chi {T : Finset (Fin N)} (hT : T.Nonempty) : ∑ v : State N, lt2Chi T v = 0 := by
  obtain ⟨j, hj⟩ := hT
  set φ : State N → State N := fun v => Function.update v j (!v j) with hφ
  have hinv : Function.Involutive φ := fun v => by
    funext k; by_cases h : k = j
    · subst h; simp [hφ]
    · simp [hφ, Function.update_of_ne h]
  have h := Equiv.sum_comp (hinv.toPerm φ) (fun v => lt2Chi T v)
  have h2 : ∑ v : State N, lt2Chi T (φ v) = -∑ v : State N, lt2Chi T v := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun v _ => lt2Chi_flip hj v
  simp only [Function.Involutive.coe_toPerm] at h
  linarith

/-- **Orthogonality**: `Σ_v χ_T χ_{T'} = 2^N 1{T = T'}`. -/
lemma lt2_sum_chi_mul (T T' : Finset (Fin N)) :
    ∑ v : State N, lt2Chi T v * lt2Chi T' v = if T = T' then (2 : ℝ) ^ N else 0 := by
  split_ifs with h
  · subst h; simp only [lt2Chi_sq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]; simp
  · simp_rw [lt2Chi_mul]
    exact lt2_sum_chi (Finset.nonempty_of_ne_empty fun he => h (symmDiff_eq_bot.1 he))

/-! ### The count union bound -/

/-- **Count union bound.** -/
theorem lt2_count_union {α : Type*} [DecidableEq α] (Fam : Finset α) (X : α → Param N → ℝ) {K B : ℝ} (m : ℕ)
    (htail : ∀ A ⊆ Fam, A.card = m → ∀ A' ⊆ A,
      cubeM N {w | m * K ≤ ∑ a ∈ A, (if a ∈ A' then X a w else -X a w)} ≤ ENNReal.ofReal B) (hB : 0 ≤ B) :
    cubeM N {w | m ≤ (Fam.filter fun a => K ≤ |X a w|).card} ≤
      ENNReal.ofReal ((Fam.card.choose m) * 2 ^ m * B) := by
  have hsub : {w : Param N | m ≤ (Fam.filter fun a => K ≤ |X a w|).card} ⊆
      ⋃ A ∈ Fam.powersetCard m, ⋃ A' ∈ A.powerset,
        {w | m * K ≤ ∑ a ∈ A, (if a ∈ A' then X a w else -X a w)} := by
    intro w hw
    simp only [Set.mem_setOf_eq] at hw
    obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq hw
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, mem_powersetCard, mem_powerset]
    refine ⟨A, ⟨hA.trans (filter_subset _ _), hAc⟩, A.filter fun a => 0 ≤ X a w, filter_subset _ _, ?_⟩
    have hterm : ∀ a ∈ A, K ≤ (if a ∈ A.filter (fun a => 0 ≤ X a w) then X a w else -X a w) := by
      intro a ha
      have hK := (mem_filter.1 (hA ha)).2
      have hm : a ∈ A.filter (fun a => 0 ≤ X a w) ↔ 0 ≤ X a w := by simp [ha]
      split_ifs with h
      · rwa [abs_of_nonneg (hm.1 h)] at hK
      · rwa [abs_of_neg (not_le.1 (fun h0 => h (hm.2 h0)))] at hK
    calc (m : ℝ) * K = ∑ _a ∈ A, K := by rw [Finset.sum_const, hAc, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hterm
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ A ∈ Fam.powersetCard m, cubeM N (⋃ A' ∈ A.powerset,
        {w | m * K ≤ ∑ a ∈ A, (if a ∈ A' then X a w else -X a w)})
      ≤ ∑ A ∈ Fam.powersetCard m, ∑ A' ∈ A.powerset,
          cubeM N {w | m * K ≤ ∑ a ∈ A, (if a ∈ A' then X a w else -X a w)} :=
        Finset.sum_le_sum fun A _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ A ∈ Fam.powersetCard m, ∑ _A' ∈ A.powerset, ENNReal.ofReal B := by
        refine Finset.sum_le_sum fun A hA => Finset.sum_le_sum fun A' hA' => ?_
        obtain ⟨h1, h2⟩ := mem_powersetCard.1 hA
        exact htail A h1 h2 A' (mem_powerset.1 hA')
    _ = ∑ A ∈ Fam.powersetCard m, (2 : ENNReal) ^ m * ENNReal.ofReal B := by
        refine Finset.sum_congr rfl fun A hA => ?_
        rw [Finset.sum_const, Finset.card_powerset, (mem_powersetCard.1 hA).2, nsmul_eq_mul]; push_cast; rfl
    _ = ENNReal.ofReal ((Fam.card.choose m) * 2 ^ m * B) := by
        rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat, mul_assoc]

/-! ### Row-local linear statistics -/

lemma lt2_int_row (f : (Fin N → ℝ) → ℝ) (hf : Measurable f) (v : State N) :
    ∫ w, f (w v) ∂cubeM N = ∫ x, f x ∂rowM N := by
  have hmp : MeasurePreserving (fun w : Param N => w v) (cubeM N) (rowM N) :=
    measurePreserving_eval (fun _ : State N => rowM N) v
  rw [← hmp.map_eq]
  exact (integral_map (measurable_pi_apply v).aemeasurable hf.aestronglyMeasurable).symm

/-- **Bernstein for a row-local linear statistic** `Σ_v g(w v) c_v` with `Σ_v c_v = 0`. -/
theorem lt2_rowlin_tail (g : (Fin N → ℝ) → ℝ) (hg : Measurable g) {G : ℝ} (hG : ∀ x, |g x| ≤ G)
    (c : State N → ℝ) (hc : ∑ v, c v = 0) {Cm V ε : ℝ} (hCm : ∀ v, |c v| ≤ Cm) (hε : 0 ≤ ε)
    (hV : (∫ x, g x ^ 2 ∂rowM N) * ∑ v, c v ^ 2 ≤ V) :
    (cubeM N).real {w | ε ≤ ∑ v, g (w v) * c v} ≤
      Real.exp (-min (ε ^ 2 / (4 * V)) (ε / (2 * (2 * G * Cm)))) := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  haveI : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG 0)
  have hCm0 : 0 ≤ Cm := (abs_nonneg _).trans (hCm 0)
  have hgi : Integrable g (rowM N) := Integrable.of_bound hg.aestronglyMeasurable G (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]; exact hG x)
  set Eg := ∫ x, g x ∂rowM N
  have hEg : |Eg| ≤ G := by
    calc |Eg| ≤ ∫ x, |g x| ∂rowM N := abs_integral_le_integral_abs
      _ ≤ ∫ _x, G ∂rowM N := integral_mono hgi.abs (integrable_const G) hG
      _ = G := by simp
  set X : State N → Param N → ℝ := fun v w => (g (w v) - Eg) * c v with hX
  have hind : iIndepFun X (cubeM N) := by
    have := iIndepFun_rows (N := N) (fun v x => (g x - Eg) * c v) (fun v => (hg.sub measurable_const).mul_const _)
    exact this
  have hmeas : ∀ v, AEMeasurable (X v) (cubeM N) := fun v =>
    (((hg.comp (measurable_pi_apply v)).sub measurable_const).mul_const _).aemeasurable
  have hmp : ∀ v, MeasurePreserving (fun w : Param N => w v) (cubeM N) (rowM N) := fun v =>
    measurePreserving_eval (fun _ : State N => rowM N) v
  have hsum : ∀ w, ∑ v, g (w v) * c v = ∑ v, X v w := by
    intro w
    simp only [hX, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hc, mul_zero, sub_zero]
  simp_rw [hsum]
  refine bernstein_upper univ hind hmeas (by positivity) hε (fun v _ => ae_of_all _ fun w => ?_)
    (fun v _ => ?_) ?_
  · simp only [hX]
    rw [abs_mul]
    have h1 : |g (w v) - Eg| ≤ 2 * G := (abs_sub _ _).trans (by linarith [hG (w v), hEg])
    exact mul_le_mul h1 (hCm v) (abs_nonneg _) (by positivity)
  · simp only [hX]
    rw [integral_mul_const, lt2_int_row (fun x => g x - Eg) (hg.sub measurable_const) v,
      integral_sub hgi (integrable_const _), integral_const]
    simp [Eg]
  · calc ∑ v ∈ univ, ∫ w, X v w ^ 2 ∂cubeM N
        = ∑ v, (∫ x, (g x - Eg) ^ 2 ∂rowM N) * c v ^ 2 := by
          refine Finset.sum_congr rfl fun v _ => ?_
          simp only [hX, mul_pow]
          rw [integral_mul_const, lt2_int_row (fun x => (g x - Eg) ^ 2) ((hg.sub measurable_const).pow_const 2) v]
      _ ≤ ∑ v, (∫ x, g x ^ 2 ∂rowM N) * c v ^ 2 := by
          refine Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have hgi2 : Integrable (fun x => g x ^ 2) (rowM N) :=
            Integrable.of_bound (hg.pow_const 2).aestronglyMeasurable (G ^ 2) (ae_of_all _ fun x => by
              rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
              have := hG x
              nlinarith [abs_nonneg (g x), sq_abs (g x)])
          have e : ∫ x, (g x - Eg) ^ 2 ∂rowM N = ∫ x, g x ^ 2 ∂rowM N - Eg ^ 2 := by
            have : (fun x => (g x - Eg) ^ 2) = fun x => g x ^ 2 - 2 * Eg * g x + Eg ^ 2 := by
              funext x; ring
            rw [this, integral_add (f := fun x => g x ^ 2 - 2 * Eg * g x) (g := fun _ => Eg ^ 2)
              (hgi2.sub (hgi.const_mul _)) (integrable_const _),
              integral_sub (f := fun x => g x ^ 2) (g := fun x => 2 * Eg * g x) hgi2 (hgi.const_mul _),
              integral_const_mul, integral_const]
            simp [Eg]; ring
          rw [e]; nlinarith [sq_nonneg Eg]
      _ = (∫ x, g x ^ 2 ∂rowM N) * ∑ v, c v ^ 2 := by rw [Finset.mul_sum]
      _ ≤ V := hV

/-! ### The weight statistics `m_T` -/

/-- The truncated (non-special) row weight, as a function of the row. -/
noncomputable def lt2gNs (x : Fin N → ℝ) : ℝ :=
  if lt2x1 * N < ∑ j, -Real.log (clamp01 (x j)) then ∏ j, clamp01 (x j) else 0

/-- `θ = e^{-x₁ N}`. -/
noncomputable def lt2θ (N : ℕ) : ℝ := Real.exp (-(lt2x1 * N))

lemma lt2gNs_measurable : Measurable (lt2gNs (N := N)) := by
  unfold lt2gNs
  refine Measurable.ite (measurableSet_lt measurable_const ?_) measurable_rowPw measurable_const
  exact Finset.measurable_sum _ fun j _ => (Real.measurable_log.comp (clamp01_measurable.comp
    (measurable_pi_apply j))).neg

lemma lt2gNs_nonneg (x : Fin N → ℝ) : 0 ≤ lt2gNs x := by
  unfold lt2gNs; split_ifs
  · exact Finset.prod_nonneg fun j _ => clamp01_nonneg _
  · exact le_rfl

lemma lt2gNs_le (x : Fin N → ℝ) : lt2gNs x ≤ lt2θ N := by
  unfold lt2gNs lt2θ
  split_ifs with h
  · by_cases hpos : ∀ j, 0 < clamp01 (x j)
    · have e : ∏ j, clamp01 (x j) = Real.exp (-∑ j, -Real.log (clamp01 (x j))) := by
        rw [Finset.sum_neg_distrib, neg_neg, Real.exp_sum]
        exact Finset.prod_congr rfl fun j _ => (Real.exp_log (hpos j)).symm
      rw [e]; exact Real.exp_le_exp.2 (by linarith)
    · push Not at hpos
      obtain ⟨j, hj⟩ := hpos
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (le_antisymm hj (clamp01_nonneg _))]
      exact (Real.exp_pos _).le
  · exact (Real.exp_pos _).le

lemma lt2gNs_sq_int : ∫ x, lt2gNs x ^ 2 ∂rowM N ≤ (1 / 3 : ℝ) ^ N := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  have hle : ∀ x : Fin N → ℝ, lt2gNs x ^ 2 ≤ (∏ j, clamp01 (x j)) ^ 2 := by
    intro x
    have h0 := lt2gNs_nonneg x
    have h1 : lt2gNs x ≤ ∏ j, clamp01 (x j) := by
      unfold lt2gNs; split_ifs
      · exact le_rfl
      · exact Finset.prod_nonneg fun j _ => clamp01_nonneg _
    exact pow_le_pow_left₀ h0 h1 2
  have hi : Integrable (fun x : Fin N → ℝ => (∏ j, clamp01 (x j)) ^ 2) (rowM N) :=
    Integrable.of_bound (measurable_rowPw.pow_const 2).aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_one₀ (Finset.prod_nonneg fun j _ => clamp01_nonneg _)
        (Finset.prod_le_one (fun j _ => clamp01_nonneg _) fun j _ => clamp01_le_one _))
  calc ∫ x, lt2gNs x ^ 2 ∂rowM N ≤ ∫ x, (∏ j, clamp01 (x j)) ^ 2 ∂rowM N :=
        integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) hi (ae_of_all _ hle)
    _ = (1 / 3 : ℝ) ^ N := by rw [integral_rowP_pow' 2]; norm_num

/-- The weight statistic `m_T = Σ_v P_ns(v) χ_T(v)`. -/
noncomputable def lt2mT (w : Param N) (T : Finset (Fin N)) : ℝ := ∑ v, lt2gNs (w v) * lt2Chi T v

/-- **Tail of a signed sum of weight statistics** over a set `A` of nonempty `T`'s. -/
theorem lt2_mT_signed_tail (A A' : Finset (Finset (Fin N))) (hA : ∀ T ∈ A, T.Nonempty) {ε : ℝ} (hε : 0 ≤ ε) :
    (cubeM N).real {w | ε ≤ ∑ T ∈ A, (if T ∈ A' then lt2mT w T else -lt2mT w T)} ≤
      Real.exp (-min (ε ^ 2 / (4 * ((2 / 3 : ℝ) ^ N * A.card))) (ε / (2 * (2 * lt2θ N * A.card)))) := by
  set c : State N → ℝ := fun v => ∑ T ∈ A, (if T ∈ A' then lt2Chi T v else -lt2Chi T v) with hcdef
  have hrewrite : ∀ w : Param N, ∑ T ∈ A, (if T ∈ A' then lt2mT w T else -lt2mT w T) =
      ∑ v, lt2gNs (w v) * c v := by
    intro w
    simp only [hcdef, Finset.mul_sum, lt2mT]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun T _ => ?_
    split_ifs
    · rfl
    · rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun v _ => by ring
  simp_rw [hrewrite]
  have hsign : ∀ T, (if T ∈ A' then (1 : ℝ) else -1) ^ 2 = 1 := fun T => by split_ifs <;> norm_num
  have hcform : ∀ v, c v = ∑ T ∈ A, (if T ∈ A' then (1 : ℝ) else -1) * lt2Chi T v := fun v =>
    Finset.sum_congr rfl fun T _ => by split_ifs <;> ring
  refine lt2_rowlin_tail lt2gNs lt2gNs_measurable (G := lt2θ N) (fun x => by
      rw [abs_of_nonneg (lt2gNs_nonneg x)]; exact lt2gNs_le x) c ?_ (Cm := A.card) (fun v => ?_) hε ?_
  · rw [Finset.sum_comm.trans (Finset.sum_congr rfl fun T hT => ?_)]
    · exact Finset.sum_const_zero
    · show ∑ v, (if T ∈ A' then lt2Chi T v else -lt2Chi T v) = 0
      split_ifs
      · exact lt2_sum_chi (hA T hT)
      · rw [Finset.sum_neg_distrib, lt2_sum_chi (hA T hT), neg_zero]
  · rw [hcform]
    calc |∑ T ∈ A, (if T ∈ A' then (1 : ℝ) else -1) * lt2Chi T v|
        ≤ ∑ T ∈ A, |(if T ∈ A' then (1 : ℝ) else -1) * lt2Chi T v| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ _T ∈ A, (1 : ℝ) := Finset.sum_congr rfl fun T _ => by
          rw [abs_mul, lt2Chi_abs]; split_ifs <;> norm_num
      _ = A.card := by simp
  · have hsq : ∑ v, c v ^ 2 = (2 : ℝ) ^ N * A.card := by
      simp_rw [hcform, sq, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ T ∈ A, ∑ v, ∑ T' ∈ A, (if T ∈ A' then (1 : ℝ) else -1) * lt2Chi T v *
          ((if T' ∈ A' then (1 : ℝ) else -1) * lt2Chi T' v) = (2 : ℝ) ^ N := by
        intro T hT
        rw [Finset.sum_comm]
        rw [Finset.sum_eq_single T]
        · have := lt2_sum_chi_mul T T
          rw [if_pos rfl] at this
          rw [← this]
          refine Finset.sum_congr rfl fun v _ => ?_
          have h1 := hsign T
          calc (if T ∈ A' then (1 : ℝ) else -1) * lt2Chi T v * ((if T ∈ A' then (1 : ℝ) else -1) * lt2Chi T v)
              = (if T ∈ A' then (1 : ℝ) else -1) ^ 2 * (lt2Chi T v * lt2Chi T v) := by ring
            _ = _ := by rw [h1, one_mul]
        · intro T' _ hne
          have h := lt2_sum_chi_mul T T'
          rw [if_neg (Ne.symm hne)] at h
          calc ∑ v, (if T ∈ A' then (1 : ℝ) else -1) * lt2Chi T v * ((if T' ∈ A' then (1 : ℝ) else -1) * lt2Chi T' v)
              = (if T ∈ A' then (1 : ℝ) else -1) * (if T' ∈ A' then (1 : ℝ) else -1) *
                  ∑ v, lt2Chi T v * lt2Chi T' v := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
            _ = 0 := by rw [h, mul_zero]
        · intro h; exact absurd hT h
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [hsq]
    calc (∫ x, lt2gNs x ^ 2 ∂rowM N) * ((2 : ℝ) ^ N * A.card) ≤ (1 / 3 : ℝ) ^ N * ((2 : ℝ) ^ N * A.card) :=
          mul_le_mul_of_nonneg_right lt2gNs_sq_int (by positivity)
      _ = (2 / 3 : ℝ) ^ N * A.card := by rw [← mul_assoc, ← mul_pow]; norm_num

lemma lt2_sigN_sq (N : ℕ) : sigN N ^ 2 = (2 / 3 : ℝ) ^ N := by
  unfold sigN; rw [Real.sq_sqrt (by positivity)]

/-- **Adverse count for the weight statistics** (W2 Lemma AC, `m_T` family). -/
theorem lt2_mT_count (Fam : Finset (Finset (Fin N))) (hFam : ∀ T ∈ Fam, T.Nonempty) {κ : ℝ} (hκ : 0 < κ)
    (m : ℕ) (hm : 1 ≤ m) :
    cubeM N {w | m ≤ (Fam.filter fun T => κ * sigN N ≤ |lt2mT w T|).card} ≤
      ENNReal.ofReal ((Fam.card.choose m) * 2 ^ m *
        Real.exp (-min (m * κ ^ 2 / 4) (κ * sigN N / (4 * lt2θ N)))) := by
  haveI : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  have hσ : 0 < sigN N := by unfold sigN; positivity
  have hθ : 0 < lt2θ N := Real.exp_pos _
  refine lt2_count_union Fam (fun T w => lt2mT w T) m (fun A hA hAc A' _ => ?_) (by positivity)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := lt2_mT_signed_tail A A' (fun T hT => hFam T (hA hT)) (ε := m * (κ * sigN N)) (by positivity)
  rw [← ENNReal.ofReal_toReal (measure_ne_top (cubeM N) _)]
  refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
  congr 2
  rw [hAc]
  congr 1
  · rw [mul_pow, mul_pow, lt2_sigN_sq]; field_simp
  · field_simp; norm_num

end Census
end IIT

#print axioms IIT.Census.lt2_mT_count
