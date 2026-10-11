/-
Census of complexes: the block decomposition of the field of a `k`-set.

For an ordered `k`-set, given by an injection `e : Fin k → Fin N`, the rows of the parameter cube
split into `2^(N-k)` blocks of `2^k` rows agreeing off the image of `e`; row `t` of a block carries
the pattern `t` (bit `i` of `t` on the unit `e i`).  With coordinates `p = t + 2^k i` as in
`GaussGen` and `a_k = 1/2 + 2^{-k}/6`, the summand of block `β` is
`X_β p = (W_β · clamp01 (w (row t of β) (e i)) - a_k / 2^(N-k)) / σ_N`, `W_β` the sum of the row
products of the block, and `∑_β X_β p = (Num w S S (pattern t) (e i) - a_k) / σ_N` (`bg_s_sum`).

Under `cubeM N` the summands are iid with law `bg_snu e`, which has zero means (`bg_snu_mean`),
second moments `|2^(N-k) ∫ x p x q dν - C_k[p,q]| ≤ 2^k (3/4)^N` with `C_k = gg_C k` the covariance
of `GaussGen` (`bg_snu_second`), and third absolute moments
`2^(N-k) ∫ (∑ |x p|)^3 dν ≤ 8 (k 2^k)^3 4^k (23/25)^N` (`bg_snu_third`).  Removing the block of a
state `s` leaves `2^(N-k) - 1` iid summands (`bg_s_map_Xr`) independent of the rows of that block
(`bg_s_indep_rest`), and changes every coordinate by at most `2^k τ_N / σ_N` on `g2`
(`bg_s_abs_sub_rest_le`).
-/
import IIT.Census.BlocksGen
import IIT.Census.GaussGen

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

set_option linter.unusedSectionVars false

noncomputable section

variable {N k : ℕ}

/-- The level `a_k = 1/2 + 2^{-k}/6` of the cause numerators of a `k`-set. -/
def bg_ak (k : ℕ) : ℝ := 1 / 2 + ((2 : ℝ) ^ k)⁻¹ / 6

/-- `∑_u [t = u] a + [t ≠ u] b = |α| b + (a - b)`. -/
lemma bg_sum_ite {α : Type*} [Fintype α] [DecidableEq α] (t : α) (a b : ℝ) :
    ∑ u, (if t = u then a else b) = Fintype.card α * b + (a - b) := by
  have h : ∀ u, (if t = u then a else b) = b + (if t = u then a - b else 0) := by
    intro u; split_ifs <;> ring
  simp only [h, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, sum_ite_eq, mem_univ,
    ite_true]

section Single

variable {e : Fin k → Fin N}

/-- The rows parametrised by (block, pattern). -/
def bg_sg (he : Function.Injective e) : bg_Bg e × Fin (2 ^ k) ≃ State N :=
  bg_eqv (bg_bits k) he (bg_bits_inj k) (Fintype.card_fin _)

/-- The row of a coordinate: the row of its pattern. -/
abbrev bg_sρ (k : ℕ) (p : Fin (k * 2 ^ k)) : Fin (2 ^ k) → Fin (2 ^ k) := fun _ => gg_pat k p

/-- The unit of a coordinate. -/
def bg_sj (e : Fin k → Fin N) (p : Fin (k * 2 ^ k)) : Fin N := e (gg_unit k p)

/-- The centring constant `a_k / 2^(N-k)`. -/
def bg_sc (N k : ℕ) (_p : Fin (k * 2 ^ k)) : ℝ := bg_ak k / 2 ^ (N - k)

/-- The summand of block `β`. -/
def bg_sX (he : Function.Injective e) (β : bg_Bg e) (w : Param N) : Fin (k * 2 ^ k) → ℝ :=
  bg_X (bg_sg he) (bg_sρ k) (bg_sj e) (bg_sc N k) β w

/-- The common law of the block summands. -/
def bg_snu (e : Fin k → Fin N) : Measure (Fin (k * 2 ^ k) → ℝ) :=
  bg_nu (bg_sρ k) (bg_sj e) (bg_sc N k)

instance (e : Fin k → Fin N) : IsProbabilityMeasure (bg_snu e) := by
  unfold bg_snu; infer_instance

/-- The number of blocks. -/
def bg_sB (e : Fin k → Fin N) : ℕ := Fintype.card (bg_Bg e)

lemma bg_sB_eq (he : Function.Injective e) : bg_sB e = 2 ^ (N - k) := bg_card_Bg he

lemma bg_s_le (he : Function.Injective e) : k ≤ N := bg_le_of_inj he

/-- The summand in closed form. -/
lemma bg_sX_apply (he : Function.Injective e) (β : bg_Bg e) (w : Param N) (p : Fin (k * 2 ^ k)) :
    bg_sX he β w p = (pb_W (fun u => w (bg_sg he (β, u))) *
      clamp01 (w (bg_sg he (β, gg_pat k p)) (e (gg_unit k p))) - bg_ak k / 2 ^ (N - k)) /
        sigN N := by
  simp only [bg_sX, bg_X, bg_F, bg_sc, bg_sj]
  rw [bg_G_const]

lemma bg_sB_mul (he : Function.Injective e) :
    (bg_sB e : ℝ) * Fintype.card (Fin (2 ^ k)) = 2 ^ N := by
  rw [bg_sB_eq he, Fintype.card_fin]
  push_cast
  rw [← pow_add, Nat.sub_add_cancel (bg_s_le he)]

/-- The centring constant is the exact mean. -/
lemma bg_s_hc (he : Function.Injective e) (p : Fin (k * 2 ^ k)) :
    bg_sc N k p = bg_mean N (bg_sρ k p) := by
  simp only [bg_sc, bg_mean, bg_sρ, bg_ak]
  rw [bg_sum_ite, Fintype.card_fin]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + k := ⟨N - k, (Nat.sub_add_cancel (bg_s_le he)).symm⟩
  rw [Nat.add_sub_cancel, pow_add, one_div_pow, one_div_pow]
  push_cast
  field_simp
  ring

/-- **Block decomposition** of the field of the `k`-set. -/
theorem bg_s_sum (he : Function.Injective e) (w : Param N) (p : Fin (k * 2 ^ k)) :
    (∑ β, bg_sX he β w) p =
      (Num w (bg_U e) (bg_U e) (bg_pst e (gg_pat k p)) (e (gg_unit k p)) - bg_ak k) / sigN N := by
  have hm : ∀ β u, merge (bg_U e) (bg_pst e (gg_pat k p)) (bg_sg he (β, u)) =
      bg_sg he (β, bg_sρ k p u) := by
    intro β u
    simp only [bg_sg, bg_eqv_apply]
    refine bg_merge_row (bg_bits k) he subset_rfl _ _ (fun u g => ?_) β u
    simp only [bg_E_mem, ↓reduceIte, bg_pst_E he]
  rw [show (∑ β, bg_sX he β w) = ∑ β, bg_X (bg_sg he) (bg_sρ k) (bg_sj e) (bg_sc N k) β w from rfl,
    bg_sum_X _ _ _ _ _ _ p hm w]
  congr 2
  rw [show (Fintype.card (bg_Bg e) : ℝ) = bg_sB e from rfl, bg_sB_eq he, bg_sc]
  push_cast
  field_simp

/-- The family of block summands, indexed by `Fin (bg_sB e)`. -/
def bg_sXs (he : Function.Injective e) (w : Param N) : Fin (bg_sB e) → Fin (k * 2 ^ k) → ℝ :=
  bg_Xs (bg_sg he) (bg_sρ k) (bg_sj e) (bg_sc N k) w

lemma bg_s_sum_Xs (he : Function.Injective e) (w : Param N) :
    ∑ b, bg_sXs he w b = ∑ β, bg_sX he β w :=
  bg_sum_Xs _ _ _ _ w

/-- **Law of the block summands**: iid with law `bg_snu e`. -/
theorem bg_s_map_Xs (he : Function.Injective e) :
    (cubeM N).map (bg_sXs he) = Measure.pi fun _ : Fin (bg_sB e) => bg_snu e :=
  bg_map_Xs _ _ _ _

/-- **Zero means**. -/
theorem bg_snu_mean (he : Function.Injective e) (p : Fin (k * 2 ^ k)) :
    ∫ x, x p ∂bg_snu e = 0 :=
  bg_nu_mean (bg_s_hc he) p

/-- The correlation sum of two coordinates is the covariance `C_k` of `GaussGen`. -/
lemma bg_s_corr (he : Function.Injective e) (p q : Fin (k * 2 ^ k)) :
    ((Fintype.card (Fin (2 ^ k)) : ℝ))⁻¹ *
        ∑ u, bg_corr (bg_sρ k p) (bg_sρ k q) (bg_sj e p) (bg_sj e q) u = gg_C k p q := by
  have hpq : (gg_pat k p = gg_pat k q ∧ e (gg_unit k p) = e (gg_unit k q)) ↔ p = q := by
    constructor
    · rintro ⟨h1, h2⟩
      exact finProdFinEquiv.symm.injective (Prod.ext (he h2) h1)
    · rintro rfl; exact ⟨rfl, rfl⟩
  simp only [bg_corr, bg_corr0, bg_sρ, bg_sj, hpq, Fintype.card_fin, gg_C, gg_c0, gg_c1, gg_c2]
  push_cast
  have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
  by_cases h : p = q
  · subst h
    simp only [ite_true, bg_sum_ite, Fintype.card_fin]
    push_cast
    field_simp
    ring
  · simp only [h, ite_false, mul_zero, add_zero]
    by_cases ht : gg_pat k p = gg_pat k q
    · have e1 : ∀ u, (if gg_pat k p = u then (3 / 4 : ℝ) else 1 / 2) *
          (if gg_pat k q = u then 3 / 4 else 1 / 2) = if gg_pat k p = u then 9 / 16 else 1 / 4 := by
        intro u; rw [ht]; split_ifs <;> norm_num
      rw [Finset.sum_congr rfl fun u _ => e1 u, bg_sum_ite]
      simp only [ht, ite_true, Fintype.card_fin]
      push_cast
      field_simp
      ring
    · have e1 : ∀ u, (if gg_pat k p = u then (3 / 4 : ℝ) else 1 / 2) *
          (if gg_pat k q = u then 3 / 4 else 1 / 2) =
            1 / 4 + (if gg_pat k p = u then 1 / 8 else 0) + (if gg_pat k q = u then 1 / 8 else 0) := by
        intro u
        split_ifs with h1 h2 h2
        · exact absurd (h1.trans h2.symm) ht
        all_goals norm_num
      simp only [e1, ht, ite_false, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
        sum_ite_eq, mem_univ, ite_true, nsmul_eq_mul]
      push_cast
      field_simp
      ring

/-- **Second moments**: `|2^(N-k) ∫ x p x q dν - C_k[p,q]| ≤ 2^k (3/4)^N`. -/
theorem bg_snu_second (he : Function.Injective e) (p q : Fin (k * 2 ^ k)) :
    |(bg_sB e : ℝ) * ∫ x, x p * x q ∂bg_snu e - gg_C k p q| ≤ 2 ^ k * (3 / 4 : ℝ) ^ N := by
  have h := bg_nu_second (j := bg_sj e) (bg_s_hc he) (bg_sB_mul he) p q
  rw [bg_s_corr he, Fintype.card_fin] at h
  push_cast at h
  exact h

/-- **Second moments** with `2^(N-k) - 1` summands. -/
theorem bg_snu_second_pred (he : Function.Injective e) (p q : Fin (k * 2 ^ k)) :
    |((bg_sB e - 1 : ℕ) : ℝ) * ∫ x, x p * x q ∂bg_snu e - gg_C k p q| ≤
      3 * 4 ^ k * (3 / 4 : ℝ) ^ N := by
  have h := bg_nu_second_pred (j := bg_sj e) (bg_s_hc he) (bg_sB_mul he) p q
  rw [bg_s_corr he, Fintype.card_fin] at h
  push_cast at h
  rw [show (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  exact h

/-- Integrability of the third absolute moment. -/
theorem bg_snu_integrable3 (he : Function.Injective e) :
    Integrable (fun x => (∑ p, |x p|) ^ 3) (bg_snu e) :=
  bg_nu_integrable3 (bg_s_hc he)

/-- **Third moments**: `2^(N-k) ∫ (∑ |x p|)^3 dν ≤ 8 (k 2^k)^3 4^k (23/25)^N`. -/
theorem bg_snu_third (he : Function.Injective e) :
    (bg_sB e : ℝ) * ∫ x, (∑ p, |x p|) ^ 3 ∂bg_snu e ≤
      8 * ((k : ℝ) * 2 ^ k) ^ 3 * 4 ^ k * (23 / 25 : ℝ) ^ N := by
  have h := bg_nu_third (j := bg_sj e) (bg_s_hc he) (bg_sB_mul he)
  rw [Fintype.card_fin, Fintype.card_fin] at h
  push_cast at h
  rw [show (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  exact h

/-! ### Removing the block of a state -/

/-- The summands of the blocks other than the block of `s`. -/
def bg_sXr (he : Function.Injective e) (s : State N) (w : Param N) :
    Fin (bg_sB e - 1) → Fin (k * 2 ^ k) → ℝ :=
  bg_Xr (bg_sg he) (bg_sρ k) (bg_sj e) (bg_sc N k) s w

/-- **Law of the remaining summands**: iid with law `bg_snu e`. -/
theorem bg_s_map_Xr (he : Function.Injective e) (s : State N) :
    (cubeM N).map (bg_sXr he s) = Measure.pi fun _ : Fin (bg_sB e - 1) => bg_snu e :=
  bg_map_Xr _ _ _ _ s

/-- The field is the sum of the remaining summands plus the summand of the block of `s`. -/
theorem bg_s_sum_eq_rest (he : Function.Injective e) (s : State N) (w : Param N) :
    ∑ β, bg_sX he β w = ∑ b, bg_sXr he s w b + bg_sX he ((bg_sg he).symm s).1 w :=
  bg_sum_eq_rest _ _ _ _ s w

/-- **Removing the block of `s`** changes every coordinate by at most `2^k τ_N / σ_N` on `g2`. -/
theorem bg_s_abs_sub_rest_le (he : Function.Injective e) (s : State N) {w : Param N}
    (h2 : ∀ i r, Qw w i r ≤ tauN N) (p : Fin (k * 2 ^ k)) :
    |(∑ β, bg_sX he β w) p - (∑ b, bg_sXr he s w b) p| ≤ 2 ^ k * tauN N / sigN N := by
  have h := bg_abs_sub_rest_le (bg_sg he) (j := bg_sj e) (bg_s_hc he) s h2 p
  rw [Fintype.card_fin] at h
  push_cast at h
  exact h

/-- The rows of the block of `s`. -/
def bg_sblockRows (he : Function.Injective e) (s : State N) (w : Param N) :
    Fin (2 ^ k) → Fin N → ℝ :=
  bg_blockRows (bg_sg he) s w

/-- **Independence**: the remaining summands are independent of the rows of the block of `s`. -/
theorem bg_s_indep_rest (he : Function.Injective e) (s : State N) :
    IndepFun (bg_sblockRows he s) (bg_sXr he s) (cubeM N) :=
  bg_indep_rest _ _ _ _ s

/-- The rows of the block of `s` are the rows agreeing with `s` off the image of `e`. -/
lemma bg_s_blockRows_eq (he : Function.Injective e) (s : State N) (t : Fin (2 ^ k)) (j : Fin N)
    (hj : j ∉ bg_U e) : bg_sg he (((bg_sg he).symm s).1, t) j = s j := by
  have h1 : bg_sg he (((bg_sg he).symm s).1, ((bg_sg he).symm s).2) = s :=
    (bg_sg he).apply_symm_apply s
  have h2 := congrFun h1 j
  simp only [bg_sg, bg_eqv_apply] at h2 ⊢
  rw [bg_row_out _ _ _ hj] at h2 ⊢
  exact h2

end Single

end

end Census
end IIT
