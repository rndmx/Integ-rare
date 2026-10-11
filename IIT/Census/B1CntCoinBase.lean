/-
Census, B1, W14 work package WP5 (part 2): the infrastructure of the coin (W5 §§6.1-6.6).

* signed fresh column sums `w5S F R k b w = Σ_{r ∈ R \ F} ±(clamp01 (w r k) - 1/2)`, their law
  (`EntrySumLawStmt`), the entries they read (`DetOnE`), measurability;
* the glued parameter `w5G f w = glueRows Sens f (restrOut Sens w)` (so `rowsOutM`-probabilities of glued events
  are `cubeM`-probabilities, `rowsOutM_glue_eq_cubeM`), the orientation `w5or f k` of column `k` (read on the
  fixed row `s`), and the split `Σ_{r ∈ R} (pTe - 1/2) = fixed part + fresh part`;
* geometry: a subcube through a point of `Ball(s, 2)` meets `Sens` only in `Ball(s, 2)` (`far`), with at most
  `Σ_{m ≤ 2} C(D, m)` rows (`≤ d²` at `D = d`);
* the reflection `w5refl k` of column `k` (measure preserving), which negates the fresh sums of column `k`.

Blueprint: `iit-census/lean/B1-W14-count-lean.md` §10.  No `sorry`.
-/
import IIT.Census.B1CntBasics

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### Signed fresh sums -/

/-- `±(u - 1/2)`. -/
noncomputable def w5sg (b : Bool) (u : ℝ) : ℝ := if b then u - 1 / 2 else 1 / 2 - u

lemma w5sg_not (b : Bool) (u : ℝ) : w5sg (!b) u = - w5sg b u := by
  cases b <;> simp [w5sg]

lemma w5sg_one_sub (b : Bool) (u : ℝ) : w5sg b (1 - u) = - w5sg b u := by
  cases b <;> simp [w5sg] <;> ring

lemma abs_w5sg_clamp_le (b : Bool) (u : ℝ) : |w5sg b (clamp01 u)| ≤ 1 / 2 := by
  have h0 := clamp01_nonneg u
  have h1 := clamp01_le_one u
  cases b <;> simp only [w5sg, Bool.false_eq_true, ↓reduceIte] <;> rw [abs_le] <;>
    constructor <;> linarith

/-- The signed fresh sum of column `k` over the rows of `R` outside `F`. -/
noncomputable def w5S (F R : Finset (State N)) (k : Fin N) (b : Bool) (w : Param N) : ℝ :=
  ∑ r ∈ R.filter (fun r => r ∉ F), w5sg b (clamp01 (w r k))

/-- The entries read by `w5S F R k`. -/
noncomputable def w5E (F R : Finset (State N)) (k : Fin N) : Finset (State N × Fin N) :=
  (R.filter fun r => r ∉ F) ×ˢ {k}

lemma w5E_card (F R : Finset (State N)) (k : Fin N) :
    (w5E F R k).card = (R.filter fun r => r ∉ F).card := by
  simp [w5E]

lemma w5S_not (F R : Finset (State N)) (k : Fin N) (b : Bool) (w : Param N) :
    w5S F R k (!b) w = - w5S F R k b w := by
  unfold w5S; rw [← sum_neg_distrib]; exact sum_congr rfl fun r _ => w5sg_not b _

lemma w5S_eq_E (F R : Finset (State N)) (k : Fin N) (b : Bool) (w : Param N) :
    w5S F R k b w = ∑ e ∈ w5E F R k, (if (fun _ : State N × Fin N => b) e then
      clamp01 (w e.1 e.2) - 1 / 2 else 1 / 2 - clamp01 (w e.1 e.2)) := by
  unfold w5S w5E
  rw [sum_product]
  refine sum_congr rfl fun r _ => ?_
  rw [sum_singleton]
  rfl

lemma measurable_w5S (F R : Finset (State N)) (k : Fin N) (b : Bool) :
    Measurable (w5S F R k b) := by
  unfold w5S w5sg
  refine Finset.measurable_sum _ fun r _ => ?_
  have hm : Measurable fun w : Param N => clamp01 (w r k) :=
    measurable_clamp01.comp ((measurable_pi_apply k).comp (measurable_pi_apply r))
  cases b
  · exact measurable_const.sub hm
  · exact hm.sub measurable_const

/-- **The law of a signed fresh sum** (`EntrySumLawStmt`). -/
theorem w5S_law (hESL : EntrySumLawStmt) (F R : Finset (State N)) (k : Fin N) (b : Bool)
    {S : Set ℝ} (hS : MeasurableSet S) :
    cubeM N {w | w5S F R k b w ∈ S} =
      (Measure.pi fun _ : Fin (w5E F R k).card => unif) {u | ∑ l, (u l - 1 / 2) ∈ S} := by
  have h := hESL N (w5E F R k) (fun _ => b) S hS
  rw [← h]
  congr 1
  ext w
  simp only [Set.mem_ofPred_eq]
  rw [w5S_eq_E]

/-- A signed fresh sum reads only its entries. -/
lemma w5S_detOn (F R : Finset (State N)) (k : Fin N) (b : Bool) (S : Set ℝ) :
    DetOnE (w5E F R k) {w | w5S F R k b w ∈ S} := by
  intro w w' hw
  have : w5S F R k b w = w5S F R k b w' := by
    unfold w5S
    refine sum_congr rfl fun r hr => ?_
    have := hw (r, k) (mem_product.2 ⟨hr, mem_singleton_self k⟩)
    simp only at this
    rw [this]
  simp only [Set.mem_ofPred_eq, this]

/-- Entry sets of different columns are disjoint. -/
lemma w5E_disj_col (F R R' : Finset (State N)) {k k' : Fin N} (h : k ≠ k') :
    Disjoint (w5E F R k) (w5E F R' k') := by
  rw [Finset.disjoint_left]
  intro e he he'
  simp only [w5E, mem_product, mem_singleton] at he he'
  exact h (he.2.symm.trans he'.2)

/-- Entry sets of disjoint row sets are disjoint. -/
lemma w5E_disj_row (F : Finset (State N)) {R R' : Finset (State N)} (h : Disjoint R R')
    (k k' : Fin N) : Disjoint (w5E F R k) (w5E F R' k') := by
  rw [Finset.disjoint_left]
  intro e he he'
  simp only [w5E, mem_product, mem_filter] at he he'
  exact Finset.disjoint_left.1 h he.1.1 he'.1.1

/-! ### The glued parameter -/

/-- The parameter with the sensitive rows `f` and the fresh rows of `w`. -/
noncomputable def w5G {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (w : Param N) : Param N :=
  glueRows (sensRows s r0) f (restrOut (sensRows s r0) w)

lemma w5G_fresh {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (w : Param N) {r : State N}
    (hr : r ∉ sensRows s r0) : w5G f w r = w r := by
  unfold w5G; rw [glueRows_of_not_mem _ f _ hr]; rfl

lemma w5G_sens {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (w : Param N) {r : State N}
    (hr : r ∈ sensRows s r0) : w5G f w r = b1Ext f r :=
  glue_eq_b1Ext f _ r hr

lemma measurable_w5G {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) : Measurable (w5G f) :=
  (measurable_glueRows_right _ f).comp (measurable_restrOut _)

/-- `rowsOutM`-probabilities of glued events are `cubeM`-probabilities of `w5G`-events. -/
lemma rowsOut_eq_w5G {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (P : Param N → Prop) :
    rowsOutM (sensRows s r0) {g | P (glueRows (sensRows s r0) f g)} = cubeM N {w | P (w5G f w)} :=
  rowsOutM_glue_eq_cubeM _ f {w | P w}

/-- The orientation of column `k` (read on the fixed row `s`). -/
noncomputable def w5or {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (k : Fin N) : Bool :=
  decide (1 / 2 < clamp01 (b1Ext f s k))

lemma pTe_w5G_fresh {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (w : Param N) {r : State N}
    (hr : r ∉ sensRows s r0) (k : Fin N) :
    pTe (w5G f w) s r k - 1 / 2 = w5sg (w5or f k) (clamp01 (w r k)) := by
  unfold pTe w5or w5sg
  rw [w5G_sens f w (mem_sensRows_s s r0), w5G_fresh f w hr]
  by_cases h : 1 / 2 < clamp01 (b1Ext f s k)
  · rw [if_pos h, decide_eq_true h, if_pos rfl]
  · rw [if_neg h, decide_eq_false h]; simp only [Bool.false_eq_true, ↓reduceIte]; ring

lemma pTe_w5G_sens {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (w : Param N) {r : State N}
    (hr : r ∈ sensRows s r0) (k : Fin N) : pTe (w5G f w) s r k = pTe (b1Ext f) s r k := by
  unfold pTe
  rw [w5G_sens f w (mem_sensRows_s s r0), w5G_sens f w hr]

/-- The fixed (sensitive-row) part of a column sum. -/
noncomputable def w5fix {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (R : Finset (State N))
    (k : Fin N) : ℝ :=
  ∑ r ∈ R.filter (fun r => r ∈ sensRows s r0), (pTe (b1Ext f) s r k - 1 / 2)

/-- **Fixed + fresh split** of a column sum. -/
lemma sum_pTe_w5G {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (R : Finset (State N))
    (k : Fin N) (w : Param N) :
    ∑ r ∈ R, (pTe (w5G f w) s r k - 1 / 2) =
      w5fix f R k + w5S (sensRows s r0) R k (w5or f k) w := by
  rw [← sum_filter_add_sum_filter_not R (fun r => r ∈ sensRows s r0)]
  unfold w5fix w5S
  congr 1
  · exact sum_congr rfl fun r hr => by rw [pTe_w5G_sens f w (mem_filter.1 hr).2]
  · exact sum_congr rfl fun r hr => pTe_w5G_fresh f w (mem_filter.1 hr).2 k

lemma w5_abs_pTe_sub_half_le (w : Param N) (s r : State N) (k : Fin N) :
    |pTe w s r k - 1 / 2| ≤ 1 / 2 := by
  have h0 := clamp01_nonneg (w r k)
  have h1 := clamp01_le_one (w r k)
  unfold pTe
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma abs_w5fix_le {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (R : Finset (State N))
    (k : Fin N) : |w5fix f R k| ≤ ((R.filter fun r => r ∈ sensRows s r0).card : ℝ) / 2 := by
  unfold w5fix
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ r ∈ R.filter (fun r => r ∈ sensRows s r0), |pTe (b1Ext f) s r k - 1 / 2|
      ≤ ∑ _r ∈ R.filter (fun r => r ∈ sensRows s r0), (1 / 2 : ℝ) :=
        sum_le_sum fun r _ => w5_abs_pTe_sub_half_le _ _ _ _
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

/-- `effDevA` of the glued parameter: fixed part + fresh part, over the subcube size. -/
lemma effDevA_w5G {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (w : Param N)
    (A : Finset (Fin N)) (t : State N) (k : Fin N) :
    effDevA (w5G f w) s A t k * 2 ^ (N - A.card) =
      w5fix f (agree A t) k + w5S (sensRows s r0) (agree A t) k (w5or f k) w := by
  have hc : ((agree A t).card : ℝ) = 2 ^ (N - A.card) := by rw [card_agree]; push_cast; rfl
  unfold effDevA
  rw [hc, div_mul_cancel₀ _ (by positivity), sum_pTe_w5G]

/-! ### Geometry: the sensitive rows of a subcube through `Ball(s, 2)` -/

/-- Sharp form of `card_agree_ball_le`. -/
theorem w5_card_agree_ball_le_choose (A : Finset (Fin N)) (t c : State N) (ρ : ℕ) :
    ((agree A t).filter fun r => ham c r ≤ ρ).card ≤
      ∑ m ∈ range (ρ + 1), (N - A.card).choose m := by
  set φ : State N → Finset (Fin N) := fun r => Aᶜ.filter fun i => r i ≠ c i with hφ
  have hinj : Set.InjOn φ ↑((agree A t).filter fun r => ham c r ≤ ρ) := by
    intro r hr r' hr' h
    simp only [coe_filter, Set.mem_ofPred_eq] at hr hr'
    funext i
    by_cases hi : i ∈ A
    · rw [(mem_agree.1 hr.1) i hi, (mem_agree.1 hr'.1) i hi]
    · have hh := congrArg (fun S => i ∈ S) h
      simp only [hφ, mem_filter, mem_compl, hi, not_false_eq_true, true_and, eq_iff_iff] at hh
      cases h1 : r i <;> cases h2 : r' i <;> cases h3 : c i <;> simp_all
  have hmaps : Set.MapsTo φ ↑((agree A t).filter fun r => ham c r ≤ ρ)
      ↑(Aᶜ.powerset.filter fun S => S.card ≤ ρ) := by
    intro r hr
    simp only [coe_filter, Set.mem_ofPred_eq] at hr
    simp only [coe_filter, Set.mem_ofPred_eq, mem_powerset]
    refine ⟨filter_subset _ _, le_trans (card_le_card ?_) hr.2⟩
    intro i hi
    simp only [hφ, mem_filter] at hi
    simp only [mem_filter, mem_univ, true_and]
    exact fun e => hi.2 e.symm
  refine (card_le_card_of_injOn φ hmaps hinj).trans ?_
  have hAc : Aᶜ.card = N - A.card := by rw [card_compl, Fintype.card_fin]
  have hsub : Aᶜ.powerset.filter (fun S => S.card ≤ ρ) ⊆
      (range (ρ + 1)).biUnion fun m => Aᶜ.powersetCard m := by
    intro S hS
    rw [mem_filter, mem_powerset] at hS
    rw [mem_biUnion]
    exact ⟨S.card, mem_range.2 (Nat.lt_succ_of_le hS.2), mem_powersetCard.2 ⟨hS.1, rfl⟩⟩
  refine (card_le_card hsub).trans ((card_biUnion_le).trans ?_)
  simp only [card_powersetCard, hAc]
  exact le_rfl

lemma w5_sum_choose_two_le (d : ℕ) (hd : 2 ≤ d) : ∑ m ∈ range 3, d.choose m ≤ d ^ 2 := by
  simp only [sum_range_succ, sum_range_zero, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.choose_two_right, zero_add]
  have h : 2 * (d * (d - 1) / 2) ≤ d * (d - 1) := Nat.mul_div_le _ _
  have h2 : d * (d - 1) + d = d * d := by
    rcases d with _ | d
    · simp
    · simp only [Nat.add_sub_cancel]; ring
  have h3 : 2 * d ≤ d * d := Nat.mul_le_mul_right d hd
  rw [sq]
  omega

/-- In a subcube through a point `t ∈ Ball(s, 2)` of dimension `D` with `3D + 19 ≤ N`, the sensitive rows
lie in `Ball(s, 2)` (`far`). -/
lemma w5_sens_sub_ball {s r0 : State N} (hfar : N ≤ 3 * ham r0 s) (A : Finset (Fin N))
    (t : State N) (ht : ham s t ≤ 2) (hD : 3 * (N - A.card) + 19 ≤ N) :
    (agree A t).filter (fun r => r ∈ sensRows s r0) ⊆ (agree A t).filter (fun r => ham s r ≤ 2) := by
  intro r hr
  rw [mem_filter] at hr ⊢
  refine ⟨hr.1, ?_⟩
  rcases mem_union.1 hr.2 with h | h
  · simp only [ballR, mem_filter, mem_univ, true_and] at h
    exact absurd ⟨h, ht⟩ (agree_not_both_balls hfar A t hD hr.1 (self_mem_agree A t))
  · simp only [ballR, mem_filter, mem_univ, true_and] at h; exact h

/-- **At most `d²` sensitive rows** in a subcube of dimension `d ≥ 2` through `Ball(s, 2)`. -/
lemma w5_sens_card_le {s r0 : State N} (hfar : N ≤ 3 * ham r0 s) (A : Finset (Fin N))
    (t : State N) (ht : ham s t ≤ 2) {d : ℕ} (hd : N - A.card = d) (hd2 : 2 ≤ d)
    (hD : 3 * d + 19 ≤ N) :
    ((agree A t).filter (fun r => r ∈ sensRows s r0)).card ≤ d ^ 2 := by
  refine (card_le_card (w5_sens_sub_ball hfar A t ht (by omega))).trans ?_
  refine (w5_card_agree_ball_le_choose A t s 2).trans ?_
  rw [hd]
  exact w5_sum_choose_two_le d hd2

/-- At most `(D+1)²` sensitive rows in a subcube of dimension `D` through `Ball(s, 2)`. -/
lemma w5_sens_card_le' {s r0 : State N} (hfar : N ≤ 3 * ham r0 s) (A : Finset (Fin N))
    (t : State N) (ht : ham s t ≤ 2) (hD : 3 * (N - A.card) + 19 ≤ N) :
    ((agree A t).filter (fun r => r ∈ sensRows s r0)).card ≤ (N - A.card + 1) ^ 2 :=
  (card_le_card (w5_sens_sub_ball hfar A t ht hD)).trans (card_agree_ball_le A t s 2)

/-! ### The reflection of a column (W5 E4') -/

/-- Reflect `y ↦ 1 - y` the column `k` (all rows). -/
noncomputable def w5refl (k : Fin N) (w : Param N) : Param N :=
  fun r i => if i = k then 1 - w r i else w r i

lemma w5_unif_refl : MeasurePreserving (fun u : ℝ => 1 - u) unif unif := by
  have h := (volume.measurePreserving_sub_left (1 : ℝ)).restrict_preimage (s := Set.Icc (0 : ℝ) 1)
    measurableSet_Icc
  have hpre : (fun u : ℝ => 1 - u) ⁻¹' Set.Icc (0 : ℝ) 1 = Set.Icc 0 1 := by
    ext u; simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hpre] at h
  exact h

theorem mp_w5refl (k : Fin N) : MeasurePreserving (w5refl k) (cubeM N) (cubeM N) := by
  have hrow : MeasurePreserving (fun v : Fin N → ℝ => fun i => if i = k then 1 - v i else v i)
      (rowM N) (rowM N) := by
    refine measurePreserving_pi (fun _ : Fin N => unif) (fun _ : Fin N => unif)
      (f := fun i u => if i = k then 1 - u else u) fun i => ?_
    split_ifs
    · exact w5_unif_refl
    · exact MeasurePreserving.id _
  exact measurePreserving_pi (fun _ : State N => rowM N) (fun _ : State N => rowM N)
    (fun _ => hrow)

lemma w5S_refl_self (F R : Finset (State N)) (k : Fin N) (b : Bool) (w : Param N) :
    w5S F R k b (w5refl k w) = - w5S F R k b w := by
  unfold w5S
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun r _ => ?_
  simp [w5refl, clamp01_one_sub, w5sg_one_sub]

lemma w5S_refl_ne (F R : Finset (State N)) {c k : Fin N} (hc : c ≠ k) (b : Bool) (w : Param N) :
    w5S F R c b (w5refl k w) = w5S F R c b w := by
  unfold w5S
  refine sum_congr rfl fun r _ => ?_
  simp only [w5refl, if_neg hc]

end Census
end IIT
