/-
Census: the deterministic upper reduction for a system `S` of any size `k = |S|`.

Write `w = flipP s z` and suppose every numerator `Num w S Y t i` (`Y ⊆ S`, `i ∈ S`) is within
`η` of a level `A` with `3η ≤ A`.  With
`F_θ(t) = (∑_{i ∈ S} (Num w S S t i - Num w S (S \ C_i) t i)) / σ` (`C_i` the cut profile) and
`Σξ(t) = (∑_{i ∈ S} (Num w S S t i - A)) / σ`, if `φ_s(S) > X ≥ 0` then either

* some `t` is an `e`-near-argmax of `Σξ`, some `θ` is an `e`-near-minimiser of `F_·(t)/cc` and
  `X < ρ^k 2^{-k} σ/(A ln 2) · (F_θ(t) + e)`, where `e = 4kη²/((A-η)σ)`, `ρ = (A+η)/(A-η)`; or
* some tied effect state `te` and partition `θ` have
  `X < k² φ_e(θ, te)` and `φ_e(θ, te) < ρ^k 2^{-k} · 2kη/((A-η) ln 2)` (a small effect side).

The proof uses the log sandwich `(X - Y)/X ≤ ln (X/Y) ≤ (X - Y)/Y`, the fact that a tied cause
state maximises `∏_i Num_i`, and the selectivity bound `ρ^k 2^{-k}` on the level band.
-/
import IIT.Census.Profile

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-! ### Objects -/

/-- The difference `D_i(θ, t) = Num_i(S, t) - Num_i(S \ C_i, t)`. -/
noncomputable def ur_D (w : Param N) {S : Finset (Fin N)} (θ : SysPartition N S) (t : State N)
    (i : Fin N) : ℝ :=
  Num w S S t i - Num w S (S \ profile θ i) t i

/-- The linear form `F_θ(t) = (∑_{i ∈ S} D_i(θ, t)) / σ`. -/
noncomputable def ur_F (w : Param N) {S : Finset (Fin N)} (θ : SysPartition N S) (t : State N)
    (σ : ℝ) : ℝ :=
  (∑ i ∈ S, ur_D w θ t i) / σ

/-- The field sum `Σξ(t) = (∑_{i ∈ S} (Num_i(S, t) - A)) / σ`. -/
noncomputable def ur_xi (w : Param N) (S : Finset (Fin N)) (A σ : ℝ) (t : State N) : ℝ :=
  (∑ i ∈ S, (Num w S S t i - A)) / σ

/-- The shift `e = 4kη²/((A-η)σ)`. -/
noncomputable def ur_err (k : ℕ) (A η σ : ℝ) : ℝ := 4 * k * η ^ 2 / ((A - η) * σ)

/-- The band factor `ρ^k = ((A+η)/(A-η))^k`. -/
noncomputable def ur_rho (k : ℕ) (A η : ℝ) : ℝ := ((A + η) / (A - η)) ^ k

/-- The log-ratio sum `G_θ(t) = ∑_{i ∈ S} ln (Num_i(S, t) / Num_i(S \ C_i, t))`. -/
noncomputable def ur_G (w : Param N) {S : Finset (Fin N)} (θ : SysPartition N S) (t : State N) :
    ℝ :=
  ∑ i ∈ S, Real.log (Num w S S t i / Num w S (S \ profile θ i) t i)

/-! ### Real inequalities -/

lemma ur_frac_near {A η Z D : ℝ} (hη : 0 ≤ η) (hηA : η < A) (hZ : |Z - A| ≤ η)
    (hD : |D| ≤ 2 * η) : |D / Z - D / A| ≤ 2 * η ^ 2 / (A * (A - η)) := by
  have hA : 0 < A := by linarith
  have hZl : A - η ≤ Z := by rw [abs_le] at hZ; linarith
  have hZ0 : 0 < Z := by linarith
  have hAη : 0 < A - η := by linarith
  rw [show D / Z - D / A = D * (A - Z) / (Z * A) by field_simp, abs_div, abs_mul,
    abs_of_pos (mul_pos hZ0 hA), div_le_div_iff₀ (mul_pos hZ0 hA) (mul_pos hA hAη)]
  have h1 : |D| * |A - Z| ≤ 2 * η * η :=
    mul_le_mul hD (by rw [abs_sub_comm]; exact hZ) (abs_nonneg _) (by linarith)
  have h2 : 0 ≤ |D| * |A - Z| := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 (mul_pos hA hAη).le,
    mul_le_mul_of_nonneg_left hZl (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (sq_nonneg η)) hA.le)]

/-- **Log sandwich.** For `X, Y` within `η` of `A`, `ln (X/Y)` is within `2η²/(A(A-η))` of
`(X - Y)/A`. -/
lemma ur_log_near {A η X Y : ℝ} (hη : 0 ≤ η) (hηA : η < A) (hX : |X - A| ≤ η)
    (hY : |Y - A| ≤ η) : |Real.log (X / Y) - (X - Y) / A| ≤ 2 * η ^ 2 / (A * (A - η)) := by
  have hXl : A - η ≤ X := by rw [abs_le] at hX; linarith
  have hYl : A - η ≤ Y := by rw [abs_le] at hY; linarith
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hD : |X - Y| ≤ 2 * η := by
    calc |X - Y| = |(X - A) - (Y - A)| := by ring_nf
      _ ≤ |X - A| + |Y - A| := abs_sub _ _
      _ ≤ 2 * η := by linarith
  have e1 := ur_frac_near hη hηA hX hD
  have e2 := ur_frac_near hη hηA hY hD
  have l1 : (X - Y) / X ≤ Real.log (X / Y) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hY0 hX0)
    rw [Real.log_div hY0.ne' hX0.ne'] at h
    rw [Real.log_div hX0.ne' hY0.ne']
    have : Y / X - 1 = -((X - Y) / X) := by field_simp; ring
    linarith
  have l2 : Real.log (X / Y) ≤ (X - Y) / Y := by
    have h := Real.log_le_sub_one_of_pos (div_pos hX0 hY0)
    have : X / Y - 1 = (X - Y) / Y := by field_simp
    linarith
  rw [abs_le] at e1 e2 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

/-- Transport of a normalised comparison through `R`-perturbations. -/
lemma ur_min_arith {a b c d R cA cB : ℝ} (hR : 0 ≤ R) (hcA : 1 ≤ cA) (hcB : 1 ≤ cB)
    (ha : |a - c| ≤ R) (hb : |b - d| ≤ R) (h : a / cA ≤ b / cB) : c / cA ≤ d / cB + 2 * R := by
  rw [abs_le] at ha hb
  have h1 : c / cA ≤ a / cA + R := by
    calc c / cA ≤ (a + R) / cA := div_le_div_of_nonneg_right (by linarith) (by linarith)
      _ = a / cA + R / cA := add_div _ _ _
      _ ≤ a / cA + R := by linarith [div_le_self hR hcA]
  have h2 : b / cB - R ≤ d / cB := by
    calc b / cB - R ≤ b / cB - R / cB := by linarith [div_le_self hR hcB]
      _ = (b - R) / cB := (sub_div _ _ _).symm
      _ ≤ d / cB := div_le_div_of_nonneg_right (by linarith) (by linarith)
  linarith

lemma ur_exists_gt {α : Type*} {s : Finset α} {f : α → ℝ} {X : ℝ} (hX : 0 ≤ X)
    (h : X < sup'OrZero s f) : ∃ b ∈ s, X < f b := by
  by_contra hne
  push Not at hne
  exact absurd h (not_lt.2 (sup'OrZero_le hX hne))

/-! ### The cause side -/

section Cause

variable {z : Param N} (s : State N) {S : Finset (Fin N)}

lemma ur_logb_eq (hz : z ∈ openCube N) (tc : State N) (θ : SysPartition N S) :
    Real.logb 2 (sysCauseProb (tpmOf z) S s s tc / sysPartCauseProb (tpmOf z) S s θ s tc) =
      ur_G (flipP s z) θ tc / Real.log 2 := by
  have hZ := Zs_pos hz s
  rw [sysCauseProb_eq_Num, sysPartCauseProb_eq_profile, ← prod_div_distrib]
  have hq : ∀ i ∈ S, Num (flipP s z) S S tc i / Zs (flipP s z) /
      (Num (flipP s z) S (S \ profile θ i) tc i / Zs (flipP s z)) =
      Num (flipP s z) S S tc i / Num (flipP s z) S (S \ profile θ i) tc i := by
    intro i _
    have := Num_pos hz s S (S \ profile θ i) tc i
    field_simp
  rw [prod_congr rfl hq, Real.logb, Real.log_prod]
  · rfl
  · intro i _
    exact (div_pos (Num_pos hz s S S tc i) (Num_pos hz s S _ tc i)).ne'

/-- `G_θ(t)` is within `|S| · 2η²/(A(A-η))` of `(∑_{i ∈ S} D_i(θ, t)) / A`. -/
lemma ur_G_near {A η : ℝ} (hη : 0 ≤ η) (hηA : η < A) (w : Param N) (t : State N)
    (hlev : ∀ Y ⊆ S, ∀ i ∈ S, |Num w S Y t i - A| ≤ η) (θ : SysPartition N S) :
    |ur_G w θ t - (∑ i ∈ S, ur_D w θ t i) / A| ≤ S.card * (2 * η ^ 2 / (A * (A - η))) := by
  unfold ur_G
  rw [sum_div, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [← nsmul_eq_mul]
  refine sum_le_card_nsmul _ _ _ fun i hi => ?_
  exact ur_log_near hη hηA (hlev S (subset_refl _) i hi) (hlev _ sdiff_subset i hi)

/-- **Selectivity on the band**: `sysBackCause ≤ ρ^k 2^{-k}`. -/
lemma ur_back_le (hz : z ∈ openCube N) {A η : ℝ} (hη : 0 ≤ η) (hηA : η < A)
    (hlev : ∀ t, ∀ i ∈ S, |Num (flipP s z) S S t i - A| ≤ η) (tc : State N) :
    sysBackCause (tpmOf z) S s s tc ≤ ur_rho S.card A η / 2 ^ S.card := by
  have hZ := Zs_pos hz s
  set κ := ((Zs (flipP s z)) ^ S.card)⁻¹
  have hκ : 0 < κ := by positivity
  have hAη : 0 < A - η := by linarith
  have hlo : ∀ t, κ * (A - η) ^ S.card ≤ sysCauseProb (tpmOf z) S s s t := by
    intro t
    rw [prof_sysCauseProb_eq]
    refine mul_le_mul_of_nonneg_left ?_ hκ.le
    rw [← prod_const]
    exact prod_le_prod (fun _ _ => hAη.le) fun i hi => by
      have := hlev t i hi; rw [abs_le] at this; linarith
  have hhi : sysCauseProb (tpmOf z) S s s tc ≤ κ * (A + η) ^ S.card := by
    rw [prof_sysCauseProb_eq]
    refine mul_le_mul_of_nonneg_left ?_ hκ.le
    rw [← prod_const]
    exact prod_le_prod (fun i _ => (Num_pos hz s S S tc i).le) fun i hi => by
      have := hlev tc i hi; rw [abs_le] at this; linarith
  have hunc : κ * (A - η) ^ S.card ≤ sysUncCause (tpmOf z) S s s := by
    unfold sysUncCause avgOverStates
    rw [le_div_iff₀ (by positivity)]
    calc κ * (A - η) ^ S.card * 2 ^ N = ∑ _t : State N, κ * (A - η) ^ S.card := by
          rw [sum_const, card_state, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := sum_le_sum fun t _ => hlo t
  have hden : 0 < (2 : ℝ) ^ S.card * sysUncCause (tpmOf z) S s s := by
    have : 0 < κ * (A - η) ^ S.card := by positivity
    exact mul_pos (by positivity) (lt_of_lt_of_le this hunc)
  have hrho : ur_rho S.card A η * (κ * (A - η) ^ S.card) = κ * (A + η) ^ S.card := by
    unfold ur_rho
    rw [div_pow]
    have : (A - η) ^ S.card ≠ 0 := pow_ne_zero _ hAη.ne'
    field_simp
  have hr0 : 0 ≤ ur_rho S.card A η := pow_nonneg (div_nonneg (by linarith) hAη.le) _
  unfold sysBackCause
  rw [div_le_iff₀ hden]
  have h2 : (0 : ℝ) < 2 ^ S.card := by positivity
  calc sysCauseProb (tpmOf z) S s s tc ≤ κ * (A + η) ^ S.card := hhi
    _ = ur_rho S.card A η * (κ * (A - η) ^ S.card) := hrho.symm
    _ ≤ ur_rho S.card A η * sysUncCause (tpmOf z) S s s := mul_le_mul_of_nonneg_left hunc hr0
    _ = _ := by field_simp

/-- **A tied cause state is a near-argmax of `Σξ`.** -/
lemma ur_near_argmax (hz : z ∈ openCube N) {A η σ : ℝ} (hη : 0 ≤ η) (hηA : η < A)
    (hσ : 0 < σ) (hlev : ∀ t, ∀ i ∈ S, |Num (flipP s z) S S t i - A| ≤ η) {tc : State N}
    (htc : tc ∈ sysMaxCauseStates (tpmOf z) S s s) (t : State N) :
    ur_xi (flipP s z) S A σ t ≤ ur_xi (flipP s z) S A σ tc + ur_err S.card A η σ := by
  set w := flipP s z
  have hA : 0 < A := by linarith
  have hAη : 0 < A - η := by linarith
  set ε := 2 * η ^ 2 / (A * (A - η)) with hε
  set L : State N → ℝ := fun t => ∑ i ∈ S, Real.log (Num w S S t i / A)
  set Sx : State N → ℝ := fun t => ∑ i ∈ S, (Num w S S t i - A)
  have hnear : ∀ t, |L t - Sx t / A| ≤ S.card * ε := by
    intro t
    simp only [L, Sx]
    rw [sum_div, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [← nsmul_eq_mul]
    refine sum_le_card_nsmul _ _ _ fun i hi => ?_
    have h := ur_log_near hη hηA (hlev t i hi) (Y := A) (by simp [hη])
    simpa using h
  have hL : ∀ t, L t = Real.log (∏ i ∈ S, Num w S S t i) - S.card * Real.log A := by
    intro t
    simp only [L]
    rw [Real.log_prod (fun i _ => (Num_pos hz s S S t i).ne')]
    rw [← nsmul_eq_mul, ← sum_const, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => Real.log_div (Num_pos hz s S S t i).ne' hA.ne'
  have hmono : L t ≤ L tc := by
    rw [hL, hL]
    have := Real.log_le_log (prod_pos fun i _ => Num_pos hz s S S t i)
      (prod_Num_max_of_mem hz s tc htc t)
    linarith
  have h1 := abs_le.1 (hnear t)
  have h2 := abs_le.1 (hnear tc)
  have hk : Sx t / A ≤ Sx tc / A + 2 * (S.card * ε) := by linarith [h1.1, h2.2]
  have hk' : Sx t ≤ Sx tc + 2 * (S.card * ε) * A := by
    have := mul_le_mul_of_nonneg_right hk hA.le
    rw [add_mul, div_mul_cancel₀ _ hA.ne', div_mul_cancel₀ _ hA.ne'] at this
    exact this
  have he : ur_err S.card A η σ = 2 * (S.card * ε) * A / σ := by
    unfold ur_err; rw [hε]; field_simp; ring
  unfold ur_xi
  rw [he, ← add_div]
  exact div_le_div_of_nonneg_right hk' hσ.le

end Cause

lemma ur_cc_le {S : Finset (Fin N)} (θ : SysPartition N S) :
    (sysCutCount θ : ℝ) ≤ (S.card : ℝ) ^ 2 := by
  rw [sysCutCount_eq_sum_profile]
  have h : ∑ j ∈ S, (profile θ j).card ≤ S.card * S.card := by
    have := sum_le_card_nsmul S (fun j => (profile θ j).card) S.card
      fun j _ => card_le_card (prof_profile_subset θ j)
    rwa [smul_eq_mul] at this
  rw [sq]
  exact_mod_cast h

/-! ### The reduction -/

/-- **Upper reduction.** With `w = flipP s z`, if every numerator of `S` is within `η` of `A`
(`3η ≤ A`) and `φ_s(S) > X ≥ 0`, then either

* there are a state `t` and a partition `θ` with `t` an `e`-near-argmax of `Σξ`, `θ` an
  `e`-near-minimiser of `F_·(t)/cc` and `X < ρ^k 2^{-k} σ/(A ln 2) · (F_θ(t) + e)`; or
* some tied effect state `te` and partition `θ` have `X < k² φ_e(θ, te)` while
  `φ_e(θ, te) < ρ^k 2^{-k} · 2kη/((A-η) ln 2)`,

where `k = |S|`, `e = ur_err k A η σ = 4kη²/((A-η)σ)`, `ρ^k = ur_rho k A η`. -/
theorem ur_upper_reduce {z : Param N} (hz : z ∈ openCube N) (s : State N) {S : Finset (Fin N)}
    {A η σ X : ℝ} (hη : 0 ≤ η) (hηA : 3 * η ≤ A) (hA : 0 < A) (hσ : 0 < σ) (hX : 0 ≤ X)
    (hlev : ∀ Y ⊆ S, ∀ t, ∀ i ∈ S, |Num (flipP s z) S Y t i - A| ≤ η)
    (hphi : X < phi z s S) :
    (∃ (t : State N) (θ : SysPartition N S),
      (∀ t', ur_xi (flipP s z) S A σ t' ≤ ur_xi (flipP s z) S A σ t + ur_err S.card A η σ) ∧
      (∀ θ' : SysPartition N S, ur_F (flipP s z) θ t σ / (sysCutCount θ : ℝ) ≤
        ur_F (flipP s z) θ' t σ / (sysCutCount θ' : ℝ) + ur_err S.card A η σ) ∧
      X < ur_rho S.card A η / 2 ^ S.card * (σ / (A * Real.log 2)) *
        (ur_F (flipP s z) θ t σ + ur_err S.card A η σ)) ∨
    (∃ te ∈ sysMaxEffStates (tpmOf z) S s s, ∃ θ : SysPartition N S,
      X < (S.card : ℝ) ^ 2 * sysPhiE (tpmOf z) S s θ s te ∧
      sysPhiE (tpmOf z) S s θ s te <
        ur_rho S.card A η / 2 ^ S.card * (2 * S.card * η / ((A - η) * Real.log 2))) := by
  set w := flipP s z with hw
  have hηA' : η < A := by linarith
  have hAη : 0 < A - η := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨p, hp, hpX⟩ := ur_exists_gt hX hphi
  obtain ⟨hc, he⟩ := mem_product.1 hp
  obtain ⟨θh, hθh, hθX⟩ := ur_exists_gt hX hpX
  set tc := p.1
  set te := p.2
  have hmip := mem_argminSet.1 hθh
  have hlevS : ∀ t, ∀ i ∈ S, |Num w S S t i - A| ≤ η := fun t i hi =>
    hlev S (subset_refl _) t i hi
  have hbU := ur_back_le s hz hη hηA' hlevS tc
  have hb0 : 0 < sysBackCause (tpmOf z) S s s tc :=
    lt_of_lt_of_le (by positivity) (sysBackCause_ge_of_mem hz s tc hc)
  set b := sysBackCause (tpmOf z) S s s tc
  set ρ := ur_rho S.card A η / 2 ^ S.card
  set R := S.card * (2 * η ^ 2 / (A * (A - η))) with hR
  have hR0 : 0 ≤ R := by positivity
  set P : SysPartition N S → ℝ := fun θ => ∑ i ∈ S, ur_D w θ tc i with hP
  have hC : ∀ θ : SysPartition N S, sysPhiC (tpmOf z) S s θ s tc =
      b * pos (ur_G w θ tc / Real.log 2) := by
    intro θ
    unfold sysPhiC
    rw [ur_logb_eq s hz tc θ]
  have hnear : ∀ θ : SysPartition N S, |ur_G w θ tc - P θ / A| ≤ R := fun θ =>
    ur_G_near hη hηA' w tc (fun Y hY i hi => hlev Y hY tc i hi) θ
  have hcc1 : ∀ θ : SysPartition N S, (1 : ℝ) ≤ sysCutCount θ := fun θ => by
    exact_mod_cast sysCutCount_pos θ
  -- every cause side is small
  have hCle : ∀ θ : SysPartition N S, sysPhiC (tpmOf z) S s θ s tc ≤
      ρ * (2 * S.card * η / ((A - η) * Real.log 2)) := by
    intro θ
    have h1 := (abs_le.1 (hnear θ)).2
    have h2 : P θ ≤ S.card * (2 * η) := by
      have hs := sum_le_card_nsmul S (fun i => ur_D w θ tc i) (2 * η) fun i hi => by
        have hx := hlev S (subset_refl _) tc i hi
        have hy' := hlev _ (sdiff_subset : S \ profile θ i ⊆ S) tc i hi
        rw [abs_le] at hx hy'
        unfold ur_D; linarith
      rwa [nsmul_eq_mul] at hs
    have h3 : P θ / A ≤ S.card * (2 * η) / A := div_le_div_of_nonneg_right h2 hA.le
    have h4 : S.card * (2 * η) / A + R = 2 * S.card * η / (A - η) := by
      rw [hR]; field_simp; ring
    have hG : ur_G w θ tc ≤ 2 * S.card * η / (A - η) := by linarith
    have hp : pos (ur_G w θ tc / Real.log 2) ≤ 2 * S.card * η / ((A - η) * Real.log 2) := by
      unfold pos
      refine max_le (by positivity) ?_
      rw [← div_div]
      exact div_le_div_of_nonneg_right hG hlog2.le
    rw [hC θ]
    exact mul_le_mul hbU hp (pos_nonneg _) (div_nonneg (pow_nonneg (div_nonneg (by linarith) hAη.le) _) (by positivity))
  by_cases hcase : ∀ θ : SysPartition N S,
      sysPhiC (tpmOf z) S s θ s tc ≤ sysPhiE (tpmOf z) S s θ s te
  · left
    have hAt : ∀ θ, sysPhiAt (tpmOf z) S s θ s tc te = sysPhiC (tpmOf z) S s θ s tc :=
      fun θ => min_eq_left (hcase θ)
    have hθX' : X < b * pos (ur_G w θh tc / Real.log 2) := by
      have := hθX; simp only [hAt, hC] at this; exact this
    have hGh : 0 < ur_G w θh tc := by
      by_contra hneg
      push Not at hneg
      have : pos (ur_G w θh tc / Real.log 2) = 0 :=
        max_eq_left (div_nonpos_of_nonpos_of_nonneg hneg hlog2.le)
      rw [this, mul_zero] at hθX'
      linarith
    have hposh : pos (ur_G w θh tc / Real.log 2) = ur_G w θh tc / Real.log 2 :=
      max_eq_right (div_pos hGh hlog2).le
    -- the normalised comparison of the `G`s
    have hGcmp : ∀ θ : SysPartition N S, ur_G w θh tc / (sysCutCount θh : ℝ) ≤
        ur_G w θ tc / (sysCutCount θ : ℝ) := by
      intro θ
      have hm := hmip θ
      unfold normalizedSysPhiAt at hm
      rw [hAt, hAt, hC, hC, hposh] at hm
      have hc0 : (0 : ℝ) < sysCutCount θ := by linarith [hcc1 θ]
      have hch0 : (0 : ℝ) < sysCutCount θh := by linarith [hcc1 θh]
      have hGθ : 0 < ur_G w θ tc := by
        by_contra hneg
        push Not at hneg
        have : pos (ur_G w θ tc / Real.log 2) = 0 :=
          max_eq_left (div_nonpos_of_nonpos_of_nonneg hneg hlog2.le)
        rw [this, mul_zero, zero_div] at hm
        have : 0 < b * (ur_G w θh tc / Real.log 2) / (sysCutCount θh : ℝ) := by positivity
        linarith
      have hpθ : pos (ur_G w θ tc / Real.log 2) = ur_G w θ tc / Real.log 2 :=
        max_eq_right (div_pos hGθ hlog2).le
      rw [hpθ] at hm
      have e1 : b * (ur_G w θh tc / Real.log 2) / (sysCutCount θh : ℝ) =
          b / Real.log 2 * (ur_G w θh tc / (sysCutCount θh : ℝ)) := by ring
      have e2 : b * (ur_G w θ tc / Real.log 2) / (sysCutCount θ : ℝ) =
          b / Real.log 2 * (ur_G w θ tc / (sysCutCount θ : ℝ)) := by ring
      rw [e1, e2] at hm
      exact le_of_mul_le_mul_left hm (div_pos hb0 hlog2)
    have hFeq : ∀ θ : SysPartition N S, ur_F w θ tc σ / (sysCutCount θ : ℝ) =
        A / σ * (P θ / A / (sysCutCount θ : ℝ)) := by
      intro θ
      unfold ur_F
      field_simp
      rfl
    have herr : A / σ * (2 * R) = ur_err S.card A η σ := by
      unfold ur_err; rw [hR]; field_simp; ring
    refine ⟨tc, θh, fun t' => ur_near_argmax s hz hη hηA' hσ hlevS hc t', ?_, ?_⟩
    · intro θ
      have key := ur_min_arith hR0 (hcc1 θh) (hcc1 θ) (hnear θh) (hnear θ) (hGcmp θ)
      have := mul_le_mul_of_nonneg_left key (div_pos hA hσ).le
      rw [mul_add, herr, ← hFeq, ← hFeq] at this
      exact this
    · have hGup : ur_G w θh tc ≤ P θh / A + R := by linarith [(abs_le.1 (hnear θh)).2]
      have hval : σ / (A * Real.log 2) * (ur_F w θh tc σ + ur_err S.card A η σ) =
          (P θh / A + 2 * R) / Real.log 2 := by
        unfold ur_F ur_err; rw [hR]; field_simp; ring
      have hle1 : ur_G w θh tc / Real.log 2 ≤ (P θh / A + 2 * R) / Real.log 2 :=
        div_le_div_of_nonneg_right (by linarith) hlog2.le
      have hnn : 0 ≤ (P θh / A + 2 * R) / Real.log 2 :=
        le_trans (div_pos hGh hlog2).le hle1
      rw [hposh] at hθX'
      calc X < b * (ur_G w θh tc / Real.log 2) := hθX'
        _ ≤ ρ * ((P θh / A + 2 * R) / Real.log 2) := mul_le_mul hbU hle1
            (div_pos hGh hlog2).le (div_nonneg (pow_nonneg (div_nonneg (by linarith) hAη.le) _) (by positivity))
        _ = _ := by rw [mul_assoc, hval]
  · right
    push Not at hcase
    obtain ⟨θ0, h0⟩ := hcase
    refine ⟨te, he, θ0, ?_, lt_of_lt_of_le h0 (hCle θ0)⟩
    have hm := hmip θ0
    unfold normalizedSysPhiAt at hm
    have hE0 := sysPhiE_nonneg (tpmOf z) S s θ0 s te
    have hch0 : (0 : ℝ) < sysCutCount θh := by linarith [hcc1 θh]
    have h1 : sysPhiAt (tpmOf z) S s θ0 s tc te / (sysCutCount θ0 : ℝ) ≤
        sysPhiE (tpmOf z) S s θ0 s te :=
      (div_le_self (sysPhiAt_nonneg _ _ _ _ _ _ _) (hcc1 θ0)).trans (min_le_right _ _)
    have h2 : sysPhiAt (tpmOf z) S s θh s tc te ≤
        sysPhiE (tpmOf z) S s θ0 s te * (sysCutCount θh : ℝ) := by
      rw [← div_le_iff₀ hch0]; exact hm.trans h1
    calc X < sysPhiAt (tpmOf z) S s θh s tc te := hθX
      _ ≤ sysPhiE (tpmOf z) S s θ0 s te * (sysCutCount θh : ℝ) := h2
      _ ≤ sysPhiE (tpmOf z) S s θ0 s te * (S.card : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (ur_cc_le θh) hE0
      _ = _ := by ring

/-- **Upper reduction when effect sides are either zero or not small.** If for every tied
effect state and every partition the effect side is `0` or at least
`ρ^k 2^{-k} · 2kη/((A-η) ln 2)`, only the first alternative of `ur_upper_reduce` remains. -/
theorem ur_upper_reduce_of_eff {z : Param N} (hz : z ∈ openCube N) (s : State N)
    {S : Finset (Fin N)} {A η σ X : ℝ} (hη : 0 ≤ η) (hηA : 3 * η ≤ A) (hA : 0 < A)
    (hσ : 0 < σ) (hX : 0 ≤ X)
    (hlev : ∀ Y ⊆ S, ∀ t, ∀ i ∈ S, |Num (flipP s z) S Y t i - A| ≤ η)
    (heff : ∀ te ∈ sysMaxEffStates (tpmOf z) S s s, ∀ θ : SysPartition N S,
      sysPhiE (tpmOf z) S s θ s te = 0 ∨
        ur_rho S.card A η / 2 ^ S.card * (2 * S.card * η / ((A - η) * Real.log 2)) ≤
          sysPhiE (tpmOf z) S s θ s te)
    (hphi : X < phi z s S) :
    ∃ (t : State N) (θ : SysPartition N S),
      (∀ t', ur_xi (flipP s z) S A σ t' ≤ ur_xi (flipP s z) S A σ t + ur_err S.card A η σ) ∧
      (∀ θ' : SysPartition N S, ur_F (flipP s z) θ t σ / (sysCutCount θ : ℝ) ≤
        ur_F (flipP s z) θ' t σ / (sysCutCount θ' : ℝ) + ur_err S.card A η σ) ∧
      X < ur_rho S.card A η / 2 ^ S.card * (σ / (A * Real.log 2)) *
        (ur_F (flipP s z) θ t σ + ur_err S.card A η σ) := by
  rcases ur_upper_reduce hz s hη hηA hA hσ hX hlev hphi with h | ⟨te, hte, θ, h1, h2⟩
  · exact h
  · rcases heff te hte θ with h0 | hbig
    · rw [h0, mul_zero] at h1; exact absurd h1 (not_lt.2 hX)
    · exact absurd hbig (not_le.2 h2)

end Census
end IIT
