/-
Census: Gaussian estimates for the difference fields of one and two triples.

* `tp_ball_ge`: a small-ball lower bound for the difference of `A Z` around the difference of a
  point `x = C u` of the range of the covariance, with cost `⟨u, x⟩`; for a triple and the interior
  point `y z` of `CertDataPoint` the cost is at most `7.15 y²` (`tp_G1_ball_ge`).
* `tp_ball_succ_le`: enlarging a box by `δ` adds at most `d · 2δ/√(2π v₀)` to its probability when
  every coordinate either vanishes identically or has variance at least `v₀`.
* `tp_G2_zero_ball`: for two disjoint triples the difference fields are independent, so the
  probability of a product of boxes factorises.
* `tp_G2_halfspace`: the half-space tail of the joint difference field, with the covariance form
  pulled back along the difference map (`tp_quad_DA`).
-/
import IIT.Census.ThmP3Diff
import IIT.Census.CertDataPoint

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

noncomputable section

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma tp_T_DA (b : Fin d → Fin d) (A : Fin d → ι → ℝ) (Z : ι → ℝ) :
    gg_T (tp_DA b A) Z = tp_Dif b (gg_T A Z) := by
  funext p
  simp only [gg_T_apply, tp_Dif, tp_DA, sub_mul, sum_sub_distrib]

/-! ### Small balls -/

/-- **Small-ball lower bound for a difference field** around the difference of `x = C u`. -/
theorem tp_ball_ge (b : Fin d → Fin d) (A : Fin d → ι → ℝ) (u x : Fin d → ℝ)
    (hux : ∀ p, ∑ q, gg_cov A p q * u q = x p) {ρ R : ℝ} (hρ : 0 < ρ)
    (hR : ∀ p, ∑ j, |tp_DA b A p j| ≤ R) :
    (2 * ρ / Real.sqrt (2 * Real.pi)) ^ Fintype.card ι
        * Real.exp (-(Real.sqrt (∑ p, u p * x p) + ρ * Real.sqrt (Fintype.card ι)) ^ 2 / 2)
      ≤ (gg_law (tp_DA b A)).real (tp_ball (tp_Dif b x) (ρ * R)) := by
  set a : ι → ℝ := fun j => ∑ p, A p j * u p with ha
  have hTa : ∀ p, gg_T A a p = x p := by
    intro p
    rw [← hux p, gg_T_apply]
    simp only [ha, gg_cov, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun j _ => by ring
  have hcost : ∑ j, a j ^ 2 = ∑ p, u p * x p := by
    have := gg_sum_sq_eq_quad A u
    simp only [ha]
    rw [show (∑ j, (∑ p, A p j * u p) ^ 2) = ∑ j, (∑ p, u p * A p j) ^ 2 by
      simp only [mul_comm], this, gg_quad]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hux p, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [gg_law, map_measureReal_apply (gg_T (tp_DA b A)).measurable
    (tp_measurableSet_ball (tp_Dif b x) (ρ * R))]
  refine le_trans ?_ (measureReal_mono (s₁ := Set.univ.pi fun j => Set.Icc (a j - ρ) (a j + ρ)) ?_)
  · refine le_trans ?_ (gg_std_box_ge a hρ)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have := gg_sum_abs_add_sq_le a hρ.le
    rw [hcost] at this
    linarith
  · intro Z hZ
    simp only [Set.mem_preimage]
    intro p
    have e : tp_Dif b x p = gg_T (tp_DA b A) a p := by
      rw [tp_T_DA]; simp only [tp_Dif, hTa]
    rw [e, gg_T_apply, gg_T_apply, ← Finset.sum_sub_distrib]
    calc |∑ j, (tp_DA b A p j * Z j - tp_DA b A p j * a j)|
        ≤ ∑ j, |tp_DA b A p j * Z j - tp_DA b A p j * a j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |tp_DA b A p j| * ρ := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hj := hZ j (Set.mem_univ j)
          rw [← mul_sub, abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [abs_le]; constructor <;> linarith [hj.1, hj.2]
      _ = ρ * ∑ j, |tp_DA b A p j| := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ ρ * R := mul_le_mul_of_nonneg_left (hR p) hρ.le

/-- The row-sum bound for the difference field of a `k`-set. -/
def tp_R (k : ℕ) : ℝ := 2 * (Real.sqrt (gg_c0 k) + Real.sqrt (gg_c1 k) + Real.sqrt (gg_c2 k))

lemma tp_R_pos (k : ℕ) : 0 < tp_R k := by
  unfold tp_R
  have := Real.sqrt_pos.2 (gg_c0_pos k)
  positivity

lemma tp_DA_row (k : ℕ) (p : Fin (k * 2 ^ k)) :
    ∑ j, |tp_DA (tp_base k) (gg_A k) p j| ≤ tp_R k := by
  have h1 : ∑ j, |tp_DA (tp_base k) (gg_A k) p j| ≤
      ∑ j, |gg_A k p j| + ∑ j, |gg_A k (tp_base k p) j| := by
    rw [← sum_add_distrib]
    exact sum_le_sum fun j _ => abs_sub _ _
  rw [gg_A_row, gg_A_row] at h1
  unfold tp_R
  linarith

/-- The difference of the interior point `z`. -/
def tp_Dz : Fin (3 * 2 ^ 3) → ℝ := tp_Dif (tp_base 3) cd_z

/-- **The ball around `y Δz`**: its probability under the Gaussian difference law of a triple is at
least `(2ρ/√(2π))^33 exp(-(y √7.15 + ρ √33)² / 2)`. -/
theorem tp_G1_ball_ge {y ρ : ℝ} (hy : 0 ≤ y) (hρ : 0 < ρ) :
    (2 * ρ / Real.sqrt (2 * Real.pi)) ^ 33
        * Real.exp (-(y * Real.sqrt (715 / 100) + ρ * Real.sqrt 33) ^ 2 / 2)
      ≤ (tp_G1 3).real (tp_ball (fun p => y * tp_Dz p) (ρ * tp_R 3)) := by
  have hux : ∀ p, ∑ q, gg_cov (gg_A 3) p q * (y * cd_u q) = y * cd_z p := by
    intro p
    rw [← cd_point_Cu p, Finset.mul_sum]
    exact sum_congr rfl fun q _ => by rw [gg_cov_A]; ring
  have h := tp_ball_ge (tp_base 3) (gg_A 3) (fun q => y * cd_u q) (fun p => y * cd_z p) hux hρ
    (tp_DA_row 3)
  have hcard : Fintype.card (gg_ι 3) = 33 := by rw [gg_card_ι]; norm_num
  have hDif : tp_Dif (tp_base 3) (fun p => y * cd_z p) = fun p => y * tp_Dz p := by
    funext p; simp only [tp_Dif, tp_Dz]; ring
  rw [hcard, hDif] at h
  refine le_trans ?_ h
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have hq : Real.sqrt (∑ p, y * cd_u p * (y * cd_z p)) ≤ y * Real.sqrt (715 / 100) := by
    have e : ∑ p, y * cd_u p * (y * cd_z p) = y ^ 2 * ∑ p, cd_u p * cd_z p := by
      rw [mul_sum]; exact sum_congr rfl fun p _ => by ring
    rw [e]
    calc Real.sqrt (y ^ 2 * ∑ p, cd_u p * cd_z p) ≤ Real.sqrt (y ^ 2 * (715 / 100)) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left cd_point_q (sq_nonneg y))
      _ = y * Real.sqrt (715 / 100) := by
          rw [Real.sqrt_mul (sq_nonneg y), Real.sqrt_sq hy]
  have h0 : 0 ≤ Real.sqrt (∑ p, y * cd_u p * (y * cd_z p)) := Real.sqrt_nonneg _
  have h33 : ((33 : ℕ) : ℝ) = 33 := by norm_num
  rw [h33]
  have hs : 0 ≤ ρ * Real.sqrt 33 := by positivity
  nlinarith

/-! ### Slabs -/

lemma tp_coord_law (A : Fin d → ι → ℝ) (p : Fin d) :
    (gg_law A).map (fun x => x p) = gaussianReal 0 (gg_cov A p p).toNNReal := by
  have h := gg_law_functional A (Pi.single p (1 : ℝ) : Fin d → ℝ)
  have e1 : (fun x : Fin d → ℝ => ∑ q, (Pi.single p (1 : ℝ) : Fin d → ℝ) q * x q) = fun x => x p := by
    funext x; simp [Pi.single_apply]
  have e2 : gg_quad (gg_cov A) (Pi.single p (1 : ℝ) : Fin d → ℝ) = gg_cov A p p := by
    simp [gg_quad, Pi.single_apply]
  rw [e1, e2] at h
  exact h

lemma tp_coord_Icc_le (A : Fin d → ι → ℝ) (p : Fin d) {v0 : ℝ} (hv0 : 0 < v0)
    (hv : v0 ≤ gg_cov A p p) (a w : ℝ) (hw : 0 ≤ w) :
    (gg_law A).real {x | x p ∈ Set.Icc a (a + w)} ≤ w / Real.sqrt (2 * Real.pi * v0) := by
  have hset : {x : Fin d → ℝ | x p ∈ Set.Icc a (a + w)} = (fun x => x p) ⁻¹' Set.Icc a (a + w) :=
    rfl
  rw [hset, ← map_measureReal_apply (measurable_pi_apply p) measurableSet_Icc, tp_coord_law]
  have hvpos : 0 < gg_cov A p p := hv0.trans_le hv
  have hne : (gg_cov A p p).toNNReal ≠ 0 := by simpa using hvpos
  refine (gbox_gauss_Icc_le hne a w hw).trans ?_
  rw [Real.coe_toNNReal _ hvpos.le, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) hw
  exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])

/-- **Enlarging a box.** If every coordinate either vanishes identically (with centre `0`) or has
variance at least `v₀`, the box of radius `r + δ` has probability at most that of the box of radius
`r` plus `d · 2δ/√(2π v₀)`. -/
theorem tp_ball_succ_le (A : Fin d → ι → ℝ) {c : Fin d → ℝ} {v0 : ℝ} (hv0 : 0 < v0)
    (hrow : ∀ p, ((∀ j, A p j = 0) ∧ c p = 0) ∨ v0 ≤ gg_cov A p p) {r δ : ℝ} (hr : 0 ≤ r)
    (hδ : 0 ≤ δ) :
    (gg_law A).real (tp_ball c (r + δ)) ≤
      (gg_law A).real (tp_ball c r) + d * (2 * (δ / Real.sqrt (2 * Real.pi * v0))) := by
  set E : Fin d → Set (Fin d → ℝ) := fun p => {x | r < |x p - c p| ∧ |x p - c p| ≤ r + δ}
  have hsub : tp_ball c (r + δ) ⊆ tp_ball c r ∪ ⋃ p, E p := by
    intro x hx
    by_cases h : x ∈ tp_ball c r
    · exact Or.inl h
    · obtain ⟨p, hp⟩ := not_forall.1 h
      exact Or.inr (Set.mem_iUnion.2 ⟨p, not_le.1 hp, hx p⟩)
  have hE : ∀ p, (gg_law A).real (E p) ≤ 2 * (δ / Real.sqrt (2 * Real.pi * v0)) := by
    intro p
    rcases hrow p with ⟨h0, hc⟩ | hv
    · have : (gg_law A).real (E p) = 0 := by
        have hmeas : MeasurableSet (E p) := by
          have hf : Measurable (fun x : Fin d → ℝ => |x p - c p|) := by fun_prop
          exact (measurableSet_lt measurable_const hf).inter (measurableSet_le hf measurable_const)
        rw [gg_law, map_measureReal_apply (gg_T A).measurable hmeas]
        have hempty : (gg_T A) ⁻¹' E p = ∅ := by
          ext Z
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
            E, gg_T_apply, h0, zero_mul, sum_const_zero, hc, sub_zero, abs_zero, not_and]
          intro h; exact absurd h (not_lt.2 hr)
        rw [hempty, measureReal_empty]
      rw [this]; positivity
    · have hsub2 : E p ⊆ {x | x p ∈ Set.Icc (c p + r) (c p + r + δ)} ∪
          {x | x p ∈ Set.Icc (c p - r - δ) (c p - r - δ + δ)} := by
        intro x ⟨h1, h2⟩
        rcases le_or_gt 0 (x p - c p) with hs | hs
        · rw [abs_of_nonneg hs] at h1 h2
          exact Or.inl ⟨by linarith, by linarith⟩
        · rw [abs_of_neg hs] at h1 h2
          exact Or.inr ⟨by linarith, by linarith⟩
      calc (gg_law A).real (E p) ≤ (gg_law A).real ({x | x p ∈ Set.Icc (c p + r) (c p + r + δ)} ∪
            {x | x p ∈ Set.Icc (c p - r - δ) (c p - r - δ + δ)}) := measureReal_mono hsub2
        _ ≤ _ := measureReal_union_le _ _
        _ ≤ δ / Real.sqrt (2 * Real.pi * v0) + δ / Real.sqrt (2 * Real.pi * v0) :=
            add_le_add (tp_coord_Icc_le A p hv0 hv _ δ hδ) (tp_coord_Icc_le A p hv0 hv _ δ hδ)
        _ = _ := by ring
  calc (gg_law A).real (tp_ball c (r + δ)) ≤ (gg_law A).real (tp_ball c r ∪ ⋃ p, E p) :=
        measureReal_mono hsub
    _ ≤ (gg_law A).real (tp_ball c r) + ∑ p, (gg_law A).real (E p) :=
        (measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_iUnion_fintype_le _))
    _ ≤ (gg_law A).real (tp_ball c r) + ∑ _p : Fin d, 2 * (δ / Real.sqrt (2 * Real.pi * v0)) :=
        add_le_add le_rfl (sum_le_sum fun p _ => hE p)
    _ = _ := by simp

/-- The coordinates of the difference field of a `k`-set: the pattern-`0` coordinates vanish, the
others have variance `2 c₁ + 2 c₂ ≥ 2 c₂`. -/
lemma tp_G1_rows (k : ℕ) {c : Fin (k * 2 ^ k) → ℝ} (hc : ∀ p, tp_base k p = p → c p = 0)
    (p : Fin (k * 2 ^ k)) :
    ((∀ j, tp_DA (tp_base k) (gg_A k) p j = 0) ∧ c p = 0) ∨
      2 * gg_c2 k ≤ gg_cov (tp_DA (tp_base k) (gg_A k)) p p := by
  by_cases hp : tp_base k p = p
  · left
    refine ⟨fun j => ?_, hc p hp⟩
    simp only [tp_DA, hp, sub_self]
  · right
    rw [tp_cov_DA, gg_cov_A, gg_cov_A, gg_cov_A, gg_cov_A]
    have hpat : gg_pat k (tp_base k p) = ⟨0, by positivity⟩ := by
      simp only [tp_base, gg_pat_idx]
    have hne : gg_pat k p ≠ gg_pat k (tp_base k p) := by
      intro h
      apply hp
      have hu : gg_unit k (tp_base k p) = gg_unit k p := by simp only [tp_base, gg_unit_idx]
      exact finProdFinEquiv.symm.injective (Prod.ext hu h.symm)
    have hne' : p ≠ tp_base k p := fun h => hp h.symm
    simp only [gg_C, hne, hne', hne.symm, hne'.symm, ite_true, ite_false]
    have := (gg_c1_pos k).le
    linarith

/-! ### Two disjoint sets -/

variable (k : ℕ)

/-- The joint vector of two vectors of the coordinates of a `k`-set. -/
def tp_join (c c' : Fin (k * 2 ^ k) → ℝ) : Fin (2 * (k * 2 ^ k)) → ℝ :=
  fun P => if gg_jw k P = 0 then c (gg_jp k P) else c' (gg_jp k P)

lemma tp_jidx_jw_jp (P : Fin (2 * (k * 2 ^ k))) : gg_jidx k (gg_jw k P) (gg_jp k P) = P := by
  simp only [gg_jidx, gg_jw, gg_jp, Prod.mk.eta, Equiv.apply_symm_apply]

lemma tp_jw_baseJ (P : Fin (2 * (k * 2 ^ k))) : gg_jw k (tp_baseJ k P) = gg_jw k P := by
  simp [tp_baseJ]

lemma tp_jp_baseJ (P : Fin (2 * (k * 2 ^ k))) : gg_jp k (tp_baseJ k P) = tp_base k (gg_jp k P) := by
  simp [tp_baseJ]

lemma tp_fin2_ne {a b : Fin 2} (h : a ≠ b) : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  rcases gg_fin2 a with rfl | rfl <;> rcases gg_fin2 b with rfl | rfl <;> simp_all

/-- Across two disjoint sets the joint covariance is the constant `c₀ + β`. -/
lemma tp_CJ0_cross {P Q : Fin (2 * (k * 2 ^ k))} (hw : gg_jw k P ≠ gg_jw k Q) :
    gg_CJ k 0 P Q = gg_c0 k + gg_beta k 0 := by
  unfold gg_CJ
  rw [ite_eq_right hw]
  have hg : gg_glob k 0 P ≠ gg_glob k 0 Q := by
    have h1 := (gg_unit k (gg_jp k P)).2
    have h2 := (gg_unit k (gg_jp k Q)).2
    unfold gg_glob
    rcases tp_fin2_ne hw with ⟨a, b⟩ | ⟨a, b⟩ <;> simp [a, b] <;> omega
  have hs : gg_shb k 0 (gg_jw k P) (gg_pat k (gg_jp k P))
      = gg_shb k 0 (gg_jw k Q) (gg_pat k (gg_jp k Q)) := by
    have h1 := (gg_shb k 0 (gg_jw k P) (gg_pat k (gg_jp k P))).2
    have h2 := (gg_shb k 0 (gg_jw k Q) (gg_pat k (gg_jp k Q))).2
    simp only [pow_zero] at h1 h2
    exact Fin.ext (by omega)
  simp [hg, hs]

/-- The block representation of two independent copies of the difference field. -/
def tp_Ablk : Fin (2 * (k * 2 ^ k)) → (gg_ι k ⊕ gg_ι k) → ℝ
  | P, Sum.inl j => if gg_jw k P = 0 then tp_DA (tp_base k) (gg_A k) (gg_jp k P) j else 0
  | P, Sum.inr j => if gg_jw k P = 0 then 0 else tp_DA (tp_base k) (gg_A k) (gg_jp k P) j

lemma tp_cov_Ablk (P Q : Fin (2 * (k * 2 ^ k))) :
    gg_cov (tp_Ablk k) P Q = if gg_jw k P = gg_jw k Q then
      gg_cov (tp_DA (tp_base k) (gg_A k)) (gg_jp k P) (gg_jp k Q) else 0 := by
  rw [gg_cov, Fintype.sum_sum_type]
  simp only [tp_Ablk]
  rcases gg_fin2 (gg_jw k P) with h1 | h1 <;> rcases gg_fin2 (gg_jw k Q) with h2 | h2 <;>
    simp [h1, h2, gg_cov]

lemma tp_cov_DA2_zero (P Q : Fin (2 * (k * 2 ^ k))) :
    gg_cov (tp_DA (tp_baseJ k) (gg_AJ k 0)) P Q = gg_cov (tp_Ablk k) P Q := by
  rw [tp_cov_DA, gg_cov_AJ k 0 (Nat.zero_le k), gg_cov_AJ k 0 (Nat.zero_le k),
    gg_cov_AJ k 0 (Nat.zero_le k), gg_cov_AJ k 0 (Nat.zero_le k), tp_cov_Ablk]
  by_cases hw : gg_jw k P = gg_jw k Q
  · rw [ite_eq_left hw, tp_cov_DA, gg_cov_A, gg_cov_A, gg_cov_A, gg_cov_A]
    conv_lhs => rw [← tp_jidx_jw_jp k P, ← tp_jidx_jw_jp k Q]
    rw [← hw]
    simp only [tp_baseJ, gg_jw_jidx, gg_jp_jidx, gg_CJ_jidx]
  · rw [ite_eq_right hw, tp_CJ0_cross k hw,
      tp_CJ0_cross k (P := P) (Q := tp_baseJ k Q) (by rw [tp_jw_baseJ]; exact hw),
      tp_CJ0_cross k (P := tp_baseJ k P) (Q := Q) (by rw [tp_jw_baseJ]; exact hw),
      tp_CJ0_cross k (P := tp_baseJ k P) (Q := tp_baseJ k Q) (by rw [tp_jw_baseJ, tp_jw_baseJ]; exact hw)]
    ring

lemma tp_G2_zero_eq : tp_G2 k 0 = gg_law (tp_Ablk k) :=
  gg_law_eq_of_cov _ _ (tp_cov_DA2_zero k)

/-- **Two disjoint triples**: the probability of a product of boxes is the product of the
probabilities. -/
theorem tp_G2_zero_ball (c c' : Fin (k * 2 ^ k) → ℝ) (r : ℝ) :
    (tp_G2 k 0).real (tp_ball (tp_join k c c') r) =
      (tp_G1 k).real (tp_ball c r) * (tp_G1 k).real (tp_ball c' r) := by
  set T1 := gg_T (tp_DA (tp_base k) (gg_A k))
  set S1 := T1 ⁻¹' tp_ball c r
  set S2 := T1 ⁻¹' tp_ball c' r
  have hS1 : MeasurableSet S1 := T1.measurable (tp_measurableSet_ball _ _)
  have hS2 : MeasurableSet S2 := T1.measurable (tp_measurableSet_ball _ _)
  set e := MeasurableEquiv.sumPiEquivProdPi (fun _ : gg_ι k ⊕ gg_ι k => ℝ)
  have hmp := measurePreserving_sumPiEquivProdPi (fun _ : gg_ι k ⊕ gg_ι k => gaussianReal 0 1)
  have hpre : gg_T (tp_Ablk k) ⁻¹' tp_ball (tp_join k c c') r = e ⁻¹' (S1 ×ˢ S2) := by
    ext Z
    have hT : ∀ P, gg_T (tp_Ablk k) Z P = if gg_jw k P = 0 then T1 (fun j => Z (Sum.inl j)) (gg_jp k P)
        else T1 (fun j => Z (Sum.inr j)) (gg_jp k P) := by
      intro P
      simp only [gg_T_apply, Fintype.sum_sum_type, tp_Ablk, T1]
      split_ifs <;> simp
    have he1 : (e Z).1 = fun j => Z (Sum.inl j) := rfl
    have he2 : (e Z).2 = fun j => Z (Sum.inr j) := rfl
    simp only [Set.mem_preimage, tp_ball, Set.mem_ofPred_eq, Set.mem_prod, S1, S2, he1, he2]
    constructor
    · intro h
      refine ⟨fun p => ?_, fun p => ?_⟩
      · have := h (gg_jidx k 0 p)
        simpa [hT, tp_join] using this
      · have := h (gg_jidx k 1 p)
        simpa [hT, tp_join] using this
    · rintro ⟨h1, h2⟩ P
      rw [hT]
      simp only [tp_join]
      split_ifs
      · exact h1 _
      · exact h2 _
  rw [tp_G2_zero_eq, gg_law, map_measureReal_apply (gg_T (tp_Ablk k)).measurable
    (tp_measurableSet_ball (tp_join k c c') r), hpre, gg_std]
  rw [measureReal_def, hmp.measure_preimage (hS1.prod hS2).nullMeasurableSet, Measure.prod_prod,
    ENNReal.toReal_mul]
  simp only [tp_G1, gg_law]
  rw [map_measureReal_apply T1.measurable (tp_measurableSet_ball c r),
    map_measureReal_apply T1.measurable (tp_measurableSet_ball c' r), measureReal_def,
    measureReal_def, gg_std]

/-! ### Half-spaces -/

/-- The transpose of the difference map. -/
def tp_DT (b : Fin d → Fin d) (v : Fin d → ℝ) : Fin d → ℝ :=
  fun q => v q - ∑ p ∈ univ.filter (fun p => b p = q), v p

omit [Fintype ι] [DecidableEq ι] in
lemma tp_sum_DT (b : Fin d → Fin d) (A : Fin d → ι → ℝ) (v : Fin d → ℝ) (j : ι) :
    ∑ p, v p * tp_DA b A p j = ∑ q, tp_DT b v q * A q j := by
  simp only [tp_DA, tp_DT, mul_sub, sub_mul, sum_sub_distrib, sum_mul]
  congr 1
  rw [← Finset.sum_fiberwise_of_maps_to (g := b) (t := univ) (fun p _ => mem_univ (b p))]
  exact sum_congr rfl fun q _ => sum_congr rfl fun p hp => by rw [(mem_filter.1 hp).2]

lemma tp_quad_DA (b : Fin d → Fin d) (A : Fin d → ι → ℝ) (v : Fin d → ℝ) :
    gg_quad (gg_cov (tp_DA b A)) v = gg_quad (gg_cov A) (tp_DT b v) := by
  rw [← gg_sum_sq_eq_quad, ← gg_sum_sq_eq_quad]
  exact sum_congr rfl fun j _ => by rw [tp_sum_DT]

/-- **Half-space tail of the joint difference field.** -/
theorem tp_G2_halfspace {m : ℕ} (hm : m ≤ k) (v : Fin (2 * (k * 2 ^ k)) → ℝ) {h : ℝ}
    (hh : 0 < h) :
    (tp_G2 k m).real {x | h ≤ ∑ P, v P * x P} ≤
      Real.exp (-h ^ 2 / (2 * gg_quad (gg_CJ k m) (tp_DT (tp_baseJ k) v))) := by
  have e : gg_quad (gg_CJ k m) (tp_DT (tp_baseJ k) v) =
      gg_quad (gg_cov (tp_DA (tp_baseJ k) (gg_AJ k m))) v := by
    rw [tp_quad_DA]
    congr 1
    exact funext fun P => funext fun Q => (gg_cov_AJ k m hm P Q).symm
  rw [e]
  exact gg_law_halfspace_le _ v hh

end

end Census
end IIT
