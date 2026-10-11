/-
Census of complexes: the joint block decomposition of two disjoint pairs.

For two pairs `{a, b}` and `{c, d}` of four distinct units, the rows of the parameter cube split into
`2^(N-4)` superblocks of sixteen rows agreeing off `{a, b, c, d}`.  Each superblock contains four
blocks of `{a, b}` and four blocks of `{c, d}`.  The twelve cause-side differences of the two pairs,
collected in `pb_eta2 w a b c d = Fin.append (pb_eta w a b) (pb_eta w c d)`, are sums over the
superblocks of summands `pb_Y` which, under `cubeM N`, are independent with a common law `pb_nu2`.

This file proves
* the decomposition `pb_eta2_eq_sum` and the law `pb_map_Ys`;
* the moments of `pb_nu2`: zero means, cross second moments between the two pairs exactly `0`
  (`pb_nu2_cross`), diagonal second moments `∫ x (L p) x (L q) dν2 = 4 ∫ x p x q dν`
  (`pb_nu2_left`, `pb_nu2_right`), hence `|2^(N-4) ∫ x q x q' dν2 - pb_Gam2 q q'| ≤ (3/4)^N / 2`
  (`pb_nu2_second`), and third absolute moments `2^(N-4) ∫ (∑ |x q|)^3 dν2 ≤ 442368 (23/25)^N`
  (`pb_nu2_third`);
* the removal of the superblock of a state `s` (`pb_map_Yr`, `pb_indep_rest2`,
  `pb_abs_eta2_sub_le`, with error `16 tauN N / sigN N` on `g2`).
-/
import IIT.Census.PairBlocks

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

noncomputable section

variable {N : ℕ}

/-- Four distinct units. -/
def pb_dist4 (a b c d : Fin N) : Prop := a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

/-- Backgrounds of the superblocks of `{a, b, c, d}`. -/
abbrev PbBlk2 (a b c d : Fin N) := {j : Fin N // j ∉ ({a, b, c, d} : Finset (Fin N))} → Bool

/-- Row `(t, t')` of superblock `γ` (pattern `t` on `{a, b}` and `t'` on `{c, d}`). -/
def pb_row2 (a b c d : Fin N) (γ : PbBlk2 a b c d) (τ : PbPat × PbPat) : State N :=
  fun j => if ha : j = a then τ.1.1 else if hb : j = b then τ.1.2 else
    if hc : j = c then τ.2.1 else if hd : j = d then τ.2.2 else γ ⟨j, by simp [ha, hb, hc, hd]⟩

/-- The superblock of a row. -/
def pb_blk2 (a b c d : Fin N) (r : State N) : PbBlk2 a b c d := fun j => r j.1

section Rows2

variable {a b c d : Fin N}

lemma pb_row2_out (γ : PbBlk2 a b c d) (τ : PbPat × PbPat) {j : Fin N}
    (hj : j ∉ ({a, b, c, d} : Finset (Fin N))) : pb_row2 a b c d γ τ j = γ ⟨j, hj⟩ := by
  have ha : j ≠ a := by rintro rfl; simp at hj
  have hb : j ≠ b := by rintro rfl; simp at hj
  have hc : j ≠ c := by rintro rfl; simp at hj
  have hd : j ≠ d := by rintro rfl; simp at hj
  simp [pb_row2, ha, hb, hc, hd]

lemma pb_row2_a (γ : PbBlk2 a b c d) (τ : PbPat × PbPat) : pb_row2 a b c d γ τ a = τ.1.1 := by
  simp [pb_row2]

lemma pb_row2_b (h : pb_dist4 a b c d) (γ : PbBlk2 a b c d) (τ : PbPat × PbPat) :
    pb_row2 a b c d γ τ b = τ.1.2 := by
  simp [pb_row2, h.1.symm]

lemma pb_row2_c (h : pb_dist4 a b c d) (γ : PbBlk2 a b c d) (τ : PbPat × PbPat) :
    pb_row2 a b c d γ τ c = τ.2.1 := by
  simp [pb_row2, h.2.1.symm, h.2.2.2.1.symm]

lemma pb_row2_d (h : pb_dist4 a b c d) (γ : PbBlk2 a b c d) (τ : PbPat × PbPat) :
    pb_row2 a b c d γ τ d = τ.2.2 := by
  simp [pb_row2, h.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.symm]

lemma pb_blk2_row2 (γ : PbBlk2 a b c d) (τ : PbPat × PbPat) :
    pb_blk2 a b c d (pb_row2 a b c d γ τ) = γ := by
  funext ⟨j, hj⟩
  exact pb_row2_out γ τ hj

lemma pb_row2_blk2 (r : State N) :
    pb_row2 a b c d (pb_blk2 a b c d r) ((r a, r b), (r c, r d)) = r := by
  funext j
  by_cases ha : j = a
  · subst ha; simp [pb_row2]
  by_cases hb : j = b
  · subst hb; simp [pb_row2, ha]
  by_cases hc : j = c
  · subst hc; simp [pb_row2, ha, hb]
  by_cases hd : j = d
  · subst hd; simp [pb_row2, ha, hb, hc]
  simp [pb_row2, ha, hb, hc, hd, pb_blk2]

/-- A row agreeing with `s` off `{a, b, c, d}` is a row of the superblock of `s`. -/
lemma pb_row2_of_agree {r s : State N} (h : ∀ j ∉ ({a, b, c, d} : Finset (Fin N)), r j = s j) :
    r = pb_row2 a b c d (pb_blk2 a b c d s) ((r a, r b), (r c, r d)) := by
  have hb : pb_blk2 a b c d r = pb_blk2 a b c d s := by
    funext ⟨j, hj⟩; exact h j hj
  rw [← hb, pb_row2_blk2]

/-- Rows are parametrised by (superblock, pattern on `{a, b}`, pattern on `{c, d}`). -/
def pb_eqv2 (h : pb_dist4 a b c d) : PbBlk2 a b c d × (PbPat × PbPat) ≃ State N where
  toFun k := pb_row2 a b c d k.1 k.2
  invFun r := (pb_blk2 a b c d r, ((r a, r b), (r c, r d)))
  left_inv := by
    rintro ⟨γ, ⟨t, t'⟩⟩
    simp [pb_blk2_row2, pb_row2_a, pb_row2_b h, pb_row2_c h, pb_row2_d h]
  right_inv r := pb_row2_blk2 r

lemma pb_merge_row2_ab (h : pb_dist4 a b c d) (γ : PbBlk2 a b c d) (u t' : PbPat) (t : State N) :
    merge {a, b} t (pb_row2 a b c d γ (u, t')) = pb_row2 a b c d γ ((t a, t b), t') := by
  funext j
  by_cases ha : j = a
  · subst ha; simp [merge, pb_row2]
  by_cases hb : j = b
  · subst hb; simp [merge, pb_row2, ha]
  have hj : j ∉ ({a, b} : Finset (Fin N)) := by simp [ha, hb]
  rw [merge_not_mem hj]
  simp [pb_row2, ha, hb]

lemma pb_merge_row2_cd (h : pb_dist4 a b c d) (γ : PbBlk2 a b c d) (t u : PbPat) (t0 : State N) :
    merge {c, d} t0 (pb_row2 a b c d γ (t, u)) = pb_row2 a b c d γ (t, (t0 c, t0 d)) := by
  funext j
  by_cases hc : j = c
  · subst hc; simp [merge, pb_row2, h.2.1.symm, h.2.2.2.1.symm]
  by_cases hd : j = d
  · subst hd; simp [merge, pb_row2, hc, h.2.2.1.symm, h.2.2.2.2.1.symm]
  have hj : j ∉ ({c, d} : Finset (Fin N)) := by simp [hc, hd]
  rw [merge_not_mem hj]
  simp [pb_row2, hc, hd]

/-- The parametrisation of the `{a, b}`-blocks: block `(γ, t')`, row `t`. -/
def pb_eqvL (h : pb_dist4 a b c d) : (PbBlk2 a b c d × PbPat) × PbPat ≃ State N :=
  (Equiv.prodAssoc _ _ _).trans
    ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)).trans (pb_eqv2 h))

/-- The parametrisation of the `{c, d}`-blocks: block `(γ, t)`, row `t'`. -/
def pb_eqvR (h : pb_dist4 a b c d) : (PbBlk2 a b c d × PbPat) × PbPat ≃ State N :=
  (Equiv.prodAssoc _ _ _).trans (pb_eqv2 h)

@[simp] lemma pb_eqvL_apply (h : pb_dist4 a b c d) (γ : PbBlk2 a b c d) (t' t : PbPat) :
    pb_eqvL h ((γ, t'), t) = pb_row2 a b c d γ (t, t') := rfl

@[simp] lemma pb_eqvR_apply (h : pb_dist4 a b c d) (γ : PbBlk2 a b c d) (t t' : PbPat) :
    pb_eqvR h ((γ, t), t') = pb_row2 a b c d γ (t, t') := rfl

/-- The `{a, b}`-block of a row of a superblock is a row of that block. -/
lemma pb_row_eq_row2_ab (h : pb_dist4 a b c d) (s : State N) (t : PbPat) :
    pb_row a b (pb_blk a b s) t =
      pb_row2 a b c d (pb_blk2 a b c d s) (t, (s c, s d)) := by
  rw [pb_row2_of_agree (a := a) (b := b) (c := c) (d := d) (r := pb_row a b (pb_blk a b s) t)
    (s := s) fun j hj => pb_row_out _ _ (by simp at hj ⊢; tauto)]
  rw [pb_row_a, pb_row_b h.1]
  have hc : c ∉ ({a, b} : Finset (Fin N)) := by simp [h.2.1.symm, h.2.2.2.1.symm]
  have hd : d ∉ ({a, b} : Finset (Fin N)) := by simp [h.2.2.1.symm, h.2.2.2.2.1.symm]
  rw [pb_row_out _ _ hc, pb_row_out _ _ hd]
  rfl

/-- The `{c, d}`-block of a row of a superblock is a row of that block. -/
lemma pb_row_eq_row2_cd (h : pb_dist4 a b c d) (s : State N) (t' : PbPat) :
    pb_row c d (pb_blk c d s) t' =
      pb_row2 a b c d (pb_blk2 a b c d s) ((s a, s b), t') := by
  rw [pb_row2_of_agree (a := a) (b := b) (c := c) (d := d) (r := pb_row c d (pb_blk c d s) t')
    (s := s) fun j hj => pb_row_out _ _ (by simp at hj ⊢; tauto)]
  rw [pb_row_a, pb_row_b h.2.2.2.2.2]
  have ha : a ∉ ({c, d} : Finset (Fin N)) := by simp [h.2.1, h.2.2.1]
  have hb : b ∉ ({c, d} : Finset (Fin N)) := by simp [h.2.2.2.1, h.2.2.2.2.1]
  rw [pb_row_out _ _ ha, pb_row_out _ _ hb]
  rfl

end Rows2

/-! ### Superblock summands -/

lemma pb_fin12_cases {P : Fin 12 → Prop} (hL : ∀ p : Fin 6, P (Fin.castAdd 6 p))
    (hR : ∀ p : Fin 6, P (Fin.natAdd 6 p)) (q : Fin 12) : P q :=
  Fin.addCases (m := 6) (n := 6) hL hR q

/-- The summand of a superblock, as a function of its sixteen rows: the sum of the four
`{a, b}`-block summands, then the sum of the four `{c, d}`-block summands. -/
def pb_F2 (a b c d : Fin N) (z : PbPat × PbPat → Fin N → ℝ) : Fin 12 → ℝ :=
  Fin.append (∑ t', pb_F a b fun t => z (t, t')) (∑ t, pb_F c d fun t' => z (t, t'))

/-- The twelve cause-side differences of the two pairs. -/
def pb_eta2 (w : Param N) (a b c d : Fin N) : Fin 12 → ℝ :=
  Fin.append (pb_eta w a b) (pb_eta w c d)

/-- The summand of superblock `γ`. -/
def pb_Y (a b c d : Fin N) (γ : PbBlk2 a b c d) (w : Param N) : Fin 12 → ℝ :=
  pb_F2 a b c d fun τ => w (pb_row2 a b c d γ τ)

/-- The law of the sixteen rows of a superblock. -/
def pb_supM (N : ℕ) : Measure (PbPat × PbPat → Fin N → ℝ) := Measure.pi fun _ => rowM N

instance : IsProbabilityMeasure (pb_supM N) := by unfold pb_supM; infer_instance

lemma pb_measurable_F2 (a b c d : Fin N) : Measurable (pb_F2 a b c d) := by
  refine Measurable.of_eval (pb_fin12_cases (fun p => ?_) (fun p => ?_))
  · simp only [pb_F2, Fin.append_left, Finset.sum_apply]
    exact Finset.measurable_sum _ fun t' _ => (measurable_pi_apply p).comp
      ((pb_measurable_F a b).comp (Measurable.of_eval fun _ => measurable_pi_apply _))
  · simp only [pb_F2, Fin.append_right, Finset.sum_apply]
    exact Finset.measurable_sum _ fun t _ => (measurable_pi_apply p).comp
      ((pb_measurable_F c d).comp (Measurable.of_eval fun _ => measurable_pi_apply _))

/-- The common law of the superblock summands. -/
def pb_nu2 (a b c d : Fin N) : Measure (Fin 12 → ℝ) := (pb_supM N).map (pb_F2 a b c d)

instance (a b c d : Fin N) : IsProbabilityMeasure (pb_nu2 a b c d) := by
  unfold pb_nu2; infer_instance

lemma pb_measurable_Y (a b c d : Fin N) (γ : PbBlk2 a b c d) : Measurable (pb_Y a b c d γ) :=
  (pb_measurable_F2 a b c d).comp (Measurable.of_eval fun _ => measurable_pi_apply _)

/-- The number of superblocks. -/
def pb_B2 (a b c d : Fin N) : ℕ := Fintype.card (PbBlk2 a b c d)

lemma pb_card4 {a b c d : Fin N} (h : pb_dist4 a b c d) :
    ({a, b, c, d} : Finset (Fin N)).card = 4 := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := h
  rw [card_insert_of_notMem (by simp [hab, hac, had]), card_insert_of_notMem (by simp [hbc, hbd]),
    card_pair hcd]

lemma pb_B2_eq {a b c d : Fin N} (h : pb_dist4 a b c d) : pb_B2 a b c d = 2 ^ (N - 4) := by
  rw [pb_B2, Fintype.card_fun, Fintype.card_bool]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_coe, pb_card4 h, Fintype.card_fin]

lemma pb_four_le {a b c d : Fin N} (h : pb_dist4 a b c d) : 4 ≤ N := by
  have h2 := Finset.card_le_univ ({a, b, c, d} : Finset (Fin N))
  rw [Fintype.card_fin, pb_card4 h] at h2
  exact h2

lemma pb_B2_pos (a b c d : Fin N) : 0 < pb_B2 a b c d := Fintype.card_pos

lemma pb_B_eq_four_B2 {a b c d : Fin N} (h : pb_dist4 a b c d) :
    pb_B a b = 4 * pb_B2 a b c d := by
  rw [pb_B_eq h.1, pb_B2_eq h]
  have := pb_four_le h
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 4 := ⟨N - 4, by omega⟩
  rw [show n + 4 - 2 = n + 2 by omega, Nat.add_sub_cancel, pow_add]
  ring

/-- Enumeration of the superblocks. -/
def pb_e2 (a b c d : Fin N) : Fin (pb_B2 a b c d) ≃ PbBlk2 a b c d := (Fintype.equivFin _).symm

/-- The family of superblock summands, indexed by `Fin (pb_B2 a b c d)`. -/
def pb_Ys (a b c d : Fin N) (w : Param N) : Fin (pb_B2 a b c d) → Fin 12 → ℝ :=
  fun k => pb_Y a b c d (pb_e2 a b c d k) w

lemma pb_measurable_Ys (a b c d : Fin N) : Measurable (pb_Ys a b c d (N := N)) :=
  Measurable.of_eval fun _ => pb_measurable_Y a b c d _

/-- **Joint block decomposition**: `η₂ = ∑_γ Y_γ`. -/
theorem pb_eta2_eq_sum_blk {a b c d : Fin N} (h : pb_dist4 a b c d) (w : Param N) :
    pb_eta2 w a b c d = ∑ γ, pb_Y a b c d γ w := by
  have hL := pb_eta_regroup h.1 (pb_eqvL h) (fun k u t => by
    obtain ⟨γ, t'⟩ := k; exact pb_merge_row2_ab h γ u t' t) w
  have hR := pb_eta_regroup h.2.2.2.2.2 (pb_eqvR h) (fun k u t => by
    obtain ⟨γ, t⟩ := k; exact pb_merge_row2_cd h γ t u _) w
  rw [Fintype.sum_prod_type] at hL hR
  funext q
  refine pb_fin12_cases (P := fun q => pb_eta2 w a b c d q = (∑ γ, pb_Y a b c d γ w) q)
    (fun p => ?_) (fun p => ?_) q
  · simp only [pb_eta2, Fin.append_left, hL, Finset.sum_apply, pb_Y, pb_F2]
    rfl
  · simp only [pb_eta2, Fin.append_right, hR, Finset.sum_apply, pb_Y, pb_F2]
    rfl

/-- **Joint block decomposition**, enumerated form. -/
theorem pb_eta2_eq_sum {a b c d : Fin N} (h : pb_dist4 a b c d) (w : Param N) :
    pb_eta2 w a b c d = ∑ k, pb_Ys a b c d w k := by
  rw [pb_eta2_eq_sum_blk h, ← (pb_e2 a b c d).sum_comp]
  rfl

/-- **Law of the superblock summands**: iid with law `pb_nu2`. -/
theorem pb_map_Y {a b c d : Fin N} (h : pb_dist4 a b c d) :
    (cubeM N).map (fun w (γ : PbBlk2 a b c d) => pb_Y a b c d γ w) =
      Measure.pi fun _ : PbBlk2 a b c d => pb_nu2 a b c d :=
  pb_map_blocks (fun k => pb_row2 a b c d k.1 k.2) (pb_eqv2 h).injective (pb_F2 a b c d)
    (pb_measurable_F2 a b c d)

/-- **Law of the superblock summands**, enumerated form. -/
theorem pb_map_Ys {a b c d : Fin N} (h : pb_dist4 a b c d) :
    (cubeM N).map (pb_Ys a b c d) = Measure.pi fun _ : Fin (pb_B2 a b c d) => pb_nu2 a b c d := by
  have hc : pb_Ys a b c d = (fun (x : PbBlk2 a b c d → Fin 12 → ℝ) k => x (pb_e2 a b c d k)) ∘
      fun w (γ : PbBlk2 a b c d) => pb_Y a b c d γ w := rfl
  rw [hc, ← Measure.map_map (Measurable.of_eval fun k => measurable_pi_apply _)
    (Measurable.of_eval fun γ => pb_measurable_Y a b c d γ), pb_map_Y h]
  exact map_comp_inj _ (pb_e2 a b c d).injective _

/-! ### Moments of the superblock law -/

lemma pb_F2_left (a b c d : Fin N) (z : PbPat × PbPat → Fin N → ℝ) (p : Fin 6) :
    pb_F2 a b c d z (Fin.castAdd 6 p) = ∑ t', pb_F a b (fun t => z (t, t')) p := by
  simp [pb_F2, Fin.append_left, Finset.sum_apply]

lemma pb_F2_right (a b c d : Fin N) (z : PbPat × PbPat → Fin N → ℝ) (p : Fin 6) :
    pb_F2 a b c d z (Fin.natAdd 6 p) = ∑ t, pb_F c d (fun t' => z (t, t')) p := by
  rw [pb_F2, Fin.append_right, Finset.sum_apply]

lemma pb_integral_nu2 {a b c d : Fin N} {g : (Fin 12 → ℝ) → ℝ} (hg : Measurable g) :
    ∫ x, g x ∂pb_nu2 a b c d = ∫ z, g (pb_F2 a b c d z) ∂pb_supM N :=
  integral_map (pb_measurable_F2 a b c d).aemeasurable hg.aestronglyMeasurable

/-- Exchanging the patterns `s` and `(false, false)` on `{a, b}`. -/
def pb_swL (s : PbPat) (τ : PbPat × PbPat) : PbPat × PbPat := (Equiv.swap s (false, false) τ.1, τ.2)

/-- Exchanging the patterns `s` and `(false, false)` on `{c, d}`. -/
def pb_swR (s : PbPat) (τ : PbPat × PbPat) : PbPat × PbPat := (τ.1, Equiv.swap s (false, false) τ.2)

lemma pb_swL_inj (s : PbPat) : Function.Injective (pb_swL s) := by
  rintro ⟨x1, x2⟩ ⟨y1, y2⟩ h
  simp only [pb_swL, Prod.mk.injEq] at h
  rw [(Equiv.injective _) h.1, h.2]

lemma pb_swR_inj (s : PbPat) : Function.Injective (pb_swR s) := by
  rintro ⟨x1, x2⟩ ⟨y1, y2⟩ h
  simp only [pb_swR, Prod.mk.injEq] at h
  rw [h.1, (Equiv.injective _) h.2]

lemma pb_F2_swL_left (a b c d : Fin N) (z : PbPat × PbPat → Fin N → ℝ) (p : Fin 6) :
    pb_F2 a b c d (fun τ => z (pb_swL (pb_pt p) τ)) (Fin.castAdd 6 p) =
      -pb_F2 a b c d z (Fin.castAdd 6 p) := by
  rw [pb_F2_left, pb_F2_left, ← sum_neg_distrib]
  refine sum_congr rfl fun t' _ => ?_
  exact pb_F_swap a b (fun t => z (t, t')) p

lemma pb_F2_swL_right (a b c d : Fin N) (z : PbPat × PbPat → Fin N → ℝ) (s : PbPat) (q : Fin 6) :
    pb_F2 a b c d (fun τ => z (pb_swL s τ)) (Fin.natAdd 6 q) = pb_F2 a b c d z (Fin.natAdd 6 q) := by
  rw [pb_F2_right, pb_F2_right]
  exact Equiv.sum_comp (Equiv.swap s (false, false)) fun t => pb_F c d (fun t' => z (t, t')) q

lemma pb_F2_swR_right (a b c d : Fin N) (z : PbPat × PbPat → Fin N → ℝ) (p : Fin 6) :
    pb_F2 a b c d (fun τ => z (pb_swR (pb_pt p) τ)) (Fin.natAdd 6 p) =
      -pb_F2 a b c d z (Fin.natAdd 6 p) := by
  rw [pb_F2_right, pb_F2_right, ← sum_neg_distrib]
  refine sum_congr rfl fun t _ => ?_
  exact pb_F_swap c d (fun t' => z (t, t')) p

lemma pb_measurable_F2_apply (a b c d : Fin N) (q : Fin 12) :
    Measurable fun z : PbPat × PbPat → Fin N → ℝ => pb_F2 a b c d z q :=
  (measurable_pi_apply q).comp (pb_measurable_F2 a b c d)

/-- **Zero means** of `pb_nu2`. -/
theorem pb_nu2_mean (a b c d : Fin N) (q : Fin 12) : ∫ x, x q ∂pb_nu2 a b c d = 0 := by
  rw [pb_integral_nu2 (measurable_pi_apply q)]
  unfold pb_supM
  refine pb_fin12_cases (P := fun q => ∫ z, pb_F2 a b c d z q ∂(Measure.pi fun _ => rowM N) = 0)
    (fun p => ?_) (fun p => ?_) q
  · have h := pb_integral_comp_inj (pb_swL (pb_pt p)) (pb_swL_inj _)
      (pb_measurable_F2_apply a b c d (Fin.castAdd 6 p))
    simp only [pb_F2_swL_left, integral_neg] at h
    linarith
  · have h := pb_integral_comp_inj (pb_swR (pb_pt p)) (pb_swR_inj _)
      (pb_measurable_F2_apply a b c d (Fin.natAdd 6 p))
    simp only [pb_F2_swR_right, integral_neg] at h
    linarith

/-- **Cross second moments** between the two pairs vanish exactly. -/
theorem pb_nu2_cross (a b c d : Fin N) (p q : Fin 6) :
    ∫ x, x (Fin.castAdd 6 p) * x (Fin.natAdd 6 q) ∂pb_nu2 a b c d = 0 := by
  rw [pb_integral_nu2 (g := fun x => x (Fin.castAdd 6 p) * x (Fin.natAdd 6 q))
    ((measurable_pi_apply _).mul (measurable_pi_apply _))]
  unfold pb_supM
  have h := pb_integral_comp_inj (pb_swL (pb_pt p)) (pb_swL_inj _)
    (f := fun z => pb_F2 a b c d z (Fin.castAdd 6 p) * pb_F2 a b c d z (Fin.natAdd 6 q))
    ((pb_measurable_F2_apply a b c d (Fin.castAdd 6 p)).mul
      (pb_measurable_F2_apply a b c d (Fin.natAdd 6 q)))
  simp only [pb_F2_swL_left, pb_F2_swL_right, neg_mul, integral_neg] at h
  linarith

/-- Generic form of the row regrouping for an iid product over any finite set of rows. -/
lemma pb_map_rows_gen {I ι κ : Type*} [Fintype I] [Fintype ι] [Fintype κ] (g : ι × κ → I)
    (hg : Function.Injective g) :
    (Measure.pi fun _ : I => rowM N).map (fun x (k : ι) (t : κ) => x (g (k, t))) =
      Measure.pi fun _ : ι => Measure.pi fun _ : κ => rowM N := by
  have h1 := map_comp_inj g hg (rowM N)
  have h2 := Measure.infinitePi_map_curry (X := Fin N → ℝ) (fun (_ : ι) (_ : κ) => rowM N)
  simp only [Measure.infinitePi_eq_pi] at h2
  have hψ : Measurable fun (x : I → Fin N → ℝ) (j : ι × κ) => x (g j) :=
    Measurable.of_eval fun j => measurable_pi_apply (g j)
  rw [← h2, ← h1, Measure.map_map (MeasurableEquiv.measurable _) hψ]
  rfl

/-- Integrals of functions of the four `{a, b}`-blocks of a superblock. -/
lemma pb_integral_colsL {f : (PbPat → PbPat → Fin N → ℝ) → ℝ} (hf : Measurable f) :
    ∫ z, f (fun t' t => z (t, t')) ∂pb_supM N =
      ∫ x, f x ∂(Measure.pi fun _ : PbPat => pb_blkM N) := by
  have h := pb_map_rows_gen (N := N) (fun k : PbPat × PbPat => (k.2, k.1))
    (fun x y hxy => by simpa [Prod.ext_iff, and_comm] using hxy)
  have hφ : Measurable fun (z : PbPat × PbPat → Fin N → ℝ) (t' : PbPat) (t : PbPat) => z (t, t') :=
    Measurable.of_eval fun _ => Measurable.of_eval fun _ => measurable_pi_apply _
  unfold pb_supM
  rw [← integral_map hφ.aemeasurable (by rw [h]; exact hf.aestronglyMeasurable), h]
  rfl

/-- Integrals of functions of the four `{c, d}`-blocks of a superblock. -/
lemma pb_integral_colsR {f : (PbPat → PbPat → Fin N → ℝ) → ℝ} (hf : Measurable f) :
    ∫ z, f (fun t t' => z (t, t')) ∂pb_supM N =
      ∫ x, f x ∂(Measure.pi fun _ : PbPat => pb_blkM N) := by
  have h := pb_map_rows_gen (N := N) (fun k : PbPat × PbPat => k) (fun x y hxy => hxy)
  have hφ : Measurable fun (z : PbPat × PbPat → Fin N → ℝ) (t : PbPat) (t' : PbPat) => z (t, t') :=
    Measurable.of_eval fun _ => Measurable.of_eval fun _ => measurable_pi_apply _
  unfold pb_supM
  rw [← integral_map hφ.aemeasurable (by rw [h]; exact hf.aestronglyMeasurable), h]
  rfl

/-- Four iid block summands: the second moment of their sum. -/
lemma pb_integral_four {a b : Fin N} (p q : Fin 6) :
    ∫ x, (∑ k, pb_F a b (x k) p) * (∑ k, pb_F a b (x k) q)
        ∂(Measure.pi fun _ : PbPat => pb_blkM N) = 4 * ∫ y, y p * y q ∂pb_nu a b := by
  set μ := Measure.pi fun _ : PbPat => pb_blkM N
  have hs := sigN_pos N
  have hFm : ∀ p : Fin 6, Measurable fun y : PbPat → Fin N → ℝ => pb_F a b y p :=
    fun p => (measurable_pi_apply p).comp (pb_measurable_F a b)
  have hbd : ∀ (y : PbPat → Fin N → ℝ) (p : Fin 6), |pb_F a b y p| ≤ 4 / sigN N := fun y p =>
    (pb_abs_F_le a b y p).trans (by gcongr; exact pb_W_le_four y)
  have hI : ∀ k k' : PbPat, Integrable (fun x : PbPat → PbPat → Fin N → ℝ =>
      pb_F a b (x k) p * pb_F a b (x k') q) μ := fun k k' =>
    Integrable.of_bound (((hFm p).comp (measurable_pi_apply k)).mul
      ((hFm q).comp (measurable_pi_apply k'))).aestronglyMeasurable (4 / sigN N * (4 / sigN N))
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hbd _ p) (hbd _ q) (abs_nonneg _) (by positivity))
  have h0 : ∀ p : Fin 6, ∫ y, pb_F a b y p ∂pb_blkM N = 0 := fun p => by
    rw [← pb_nu_mean a b p, pb_integral_nu (measurable_pi_apply p)]
  have hterm : ∀ k k' : PbPat, ∫ x, pb_F a b (x k) p * pb_F a b (x k') q ∂μ =
      if k = k' then ∫ y, y p * y q ∂pb_nu a b else 0 := by
    intro k k'
    split_ifs with hkk
    · subst hkk
      rw [pb_integral_nu (g := fun y => y p * y q)
        ((measurable_pi_apply p).mul (measurable_pi_apply q))]
      exact integral_pi_eval (pb_blkM N) (g := fun y => pb_F a b y p * pb_F a b y q)
        ((hFm p).mul (hFm q)).aestronglyMeasurable k
    · rw [integral_pi_mul_of_ne (pb_blkM N) hkk (hFm p) (hFm q), h0 p, zero_mul]
  simp_rw [sum_mul_sum]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun k' _ => hI k k']
  simp_rw [integral_finsetSum _ fun k' _ => hI _ k', hterm]
  simp [Finset.sum_ite_eq]

/-- **Diagonal second moments**, first pair: `∫ x (L p) x (L q) dν2 = 4 ∫ x p x q dν`. -/
theorem pb_nu2_left (a b c d : Fin N) (p q : Fin 6) :
    ∫ x, x (Fin.castAdd 6 p) * x (Fin.castAdd 6 q) ∂pb_nu2 a b c d =
      4 * ∫ y, y p * y q ∂pb_nu a b := by
  rw [pb_integral_nu2 (g := fun x => x (Fin.castAdd 6 p) * x (Fin.castAdd 6 q))
    ((measurable_pi_apply _).mul (measurable_pi_apply _))]
  simp only [pb_F2_left]
  have hm : Measurable fun x : PbPat → PbPat → Fin N → ℝ =>
      (∑ k, pb_F a b (x k) p) * (∑ k, pb_F a b (x k) q) :=
    (Finset.measurable_sum _ fun k _ => ((measurable_pi_apply p).comp (pb_measurable_F a b)).comp
      (measurable_pi_apply k)).mul
      (Finset.measurable_sum _ fun k _ => ((measurable_pi_apply q).comp (pb_measurable_F a b)).comp
      (measurable_pi_apply k))
  rw [pb_integral_colsL (f := fun x => (∑ k, pb_F a b (x k) p) * (∑ k, pb_F a b (x k) q)) hm]
  exact pb_integral_four p q

/-- **Diagonal second moments**, second pair: `∫ x (R p) x (R q) dν2 = 4 ∫ x p x q dν`. -/
theorem pb_nu2_right (a b c d : Fin N) (p q : Fin 6) :
    ∫ x, x (Fin.natAdd 6 p) * x (Fin.natAdd 6 q) ∂pb_nu2 a b c d =
      4 * ∫ y, y p * y q ∂pb_nu c d := by
  rw [pb_integral_nu2 (g := fun x => x (Fin.natAdd 6 p) * x (Fin.natAdd 6 q))
    ((measurable_pi_apply _).mul (measurable_pi_apply _))]
  simp only [pb_F2_right]
  have hm : Measurable fun x : PbPat → PbPat → Fin N → ℝ =>
      (∑ k, pb_F c d (x k) p) * (∑ k, pb_F c d (x k) q) :=
    (Finset.measurable_sum _ fun k _ => ((measurable_pi_apply p).comp (pb_measurable_F c d)).comp
      (measurable_pi_apply k)).mul
      (Finset.measurable_sum _ fun k _ => ((measurable_pi_apply q).comp (pb_measurable_F c d)).comp
      (measurable_pi_apply k))
  rw [pb_integral_colsR (f := fun x => (∑ k, pb_F c d (x k) p) * (∑ k, pb_F c d (x k) q)) hm]
  exact pb_integral_four p q

/-- The limit covariance of the twelve coordinates: two independent copies of `pb_Gam`. -/
def pb_Gam2 (q q' : Fin 12) : ℝ :=
  if (q.val < 6) = (q'.val < 6) then pb_Gam ⟨q.val % 6, Nat.mod_lt _ (by norm_num)⟩
    ⟨q'.val % 6, Nat.mod_lt _ (by norm_num)⟩ else 0

lemma pb_Gam2_LL (p q : Fin 6) : pb_Gam2 (Fin.castAdd 6 p) (Fin.castAdd 6 q) = pb_Gam p q := by
  unfold pb_Gam2
  simp [Nat.mod_eq_of_lt p.2, Nat.mod_eq_of_lt q.2]

lemma pb_Gam2_RR (p q : Fin 6) : pb_Gam2 (Fin.natAdd 6 p) (Fin.natAdd 6 q) = pb_Gam p q := by
  unfold pb_Gam2
  simp [Nat.mod_eq_of_lt p.2, Nat.mod_eq_of_lt q.2]

lemma pb_Gam2_LR (p q : Fin 6) : pb_Gam2 (Fin.castAdd 6 p) (Fin.natAdd 6 q) = 0 := by
  unfold pb_Gam2
  simp [p.2]

lemma pb_Gam2_RL (p q : Fin 6) : pb_Gam2 (Fin.natAdd 6 p) (Fin.castAdd 6 q) = 0 := by
  unfold pb_Gam2
  simp [q.2]

/-- **Second moments** of the superblock law: `|2^(N-4) ∫ x q x q' dν2 - Γ₂ q q'| ≤ (3/4)^N / 2`. -/
theorem pb_nu2_second {a b c d : Fin N} (h : pb_dist4 a b c d) (q q' : Fin 12) :
    |(pb_B2 a b c d : ℝ) * ∫ x, x q * x q' ∂pb_nu2 a b c d - pb_Gam2 q q'| ≤
      (3 / 4 : ℝ) ^ N / 2 := by
  have hB : (pb_B a b : ℝ) = 4 * pb_B2 a b c d := by exact_mod_cast pb_B_eq_four_B2 h
  have hB' : (pb_B c d : ℝ) = 4 * pb_B2 a b c d := by
    rw [← hB, pb_B_eq h.2.2.2.2.2, pb_B_eq h.1]
  have hpos : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ N / 2 := by positivity
  refine pb_fin12_cases (P := fun q => |(pb_B2 a b c d : ℝ) * ∫ x, x q * x q' ∂pb_nu2 a b c d -
    pb_Gam2 q q'| ≤ (3 / 4 : ℝ) ^ N / 2) (fun p => ?_) (fun p => ?_) q <;>
  refine pb_fin12_cases (P := fun q' => |(pb_B2 a b c d : ℝ) * ∫ x, x _ * x q' ∂pb_nu2 a b c d -
    pb_Gam2 _ q'| ≤ (3 / 4 : ℝ) ^ N / 2) (fun r => ?_) (fun r => ?_) q'
  · rw [pb_nu2_left, pb_Gam2_LL, ← mul_assoc, mul_comm _ (4 : ℝ), ← hB]
    exact pb_nu_second h.1 p r
  · have hc := pb_nu2_cross a b c d p r
    rw [hc, pb_Gam2_LR]; simpa using hpos
  · have hc := pb_nu2_cross a b c d r p
    rw [show (∫ x, x (Fin.natAdd 6 p) * x (Fin.castAdd 6 r) ∂pb_nu2 a b c d) =
      ∫ x, x (Fin.castAdd 6 r) * x (Fin.natAdd 6 p) ∂pb_nu2 a b c d by
        congr 1; funext x; ring, hc, pb_Gam2_RL]
    simpa using hpos
  · rw [pb_nu2_right, pb_Gam2_RR, ← mul_assoc, mul_comm _ (4 : ℝ), ← hB']
    exact pb_nu_second h.2.2.2.2.2 p r

/-- The second moments with `2^(N-4) - 1` summands. -/
theorem pb_nu2_second_pred {a b c d : Fin N} (h : pb_dist4 a b c d) (q q' : Fin 12) :
    |((pb_B2 a b c d - 1 : ℕ) : ℝ) * ∫ x, x q * x q' ∂pb_nu2 a b c d - pb_Gam2 q q'| ≤
      17 * (3 / 4 : ℝ) ^ N := by
  have h1 := pb_nu2_second h q q'
  have hI : |∫ x, x q * x q' ∂pb_nu2 a b c d| ≤ 16 * (3 / 4 : ℝ) ^ N := by
    refine pb_fin12_cases (P := fun q => |∫ x, x q * x q' ∂pb_nu2 a b c d| ≤
      16 * (3 / 4 : ℝ) ^ N) (fun p => ?_) (fun p => ?_) q <;>
    refine pb_fin12_cases (P := fun q' => |∫ x, x _ * x q' ∂pb_nu2 a b c d| ≤
      16 * (3 / 4 : ℝ) ^ N) (fun r => ?_) (fun r => ?_) q'
    · rw [pb_nu2_left, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
      linarith [pb_abs_nu_second_le h.1 p r]
    · rw [pb_nu2_cross]; simp; positivity
    · rw [show (∫ x, x (Fin.natAdd 6 p) * x (Fin.castAdd 6 r) ∂pb_nu2 a b c d) =
        ∫ x, x (Fin.castAdd 6 r) * x (Fin.natAdd 6 p) ∂pb_nu2 a b c d by
          congr 1; funext x; ring, pb_nu2_cross]
      simp; positivity
    · rw [pb_nu2_right, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
      linarith [pb_abs_nu_second_le h.2.2.2.2.2 p r]
  rw [Nat.cast_sub (pb_B2_pos a b c d), Nat.cast_one]
  set I := ∫ x, x q * x q' ∂pb_nu2 a b c d
  calc |((pb_B2 a b c d : ℝ) - 1) * I - pb_Gam2 q q'| =
        |((pb_B2 a b c d : ℝ) * I - pb_Gam2 q q') - I| := by ring_nf
    _ ≤ |(pb_B2 a b c d : ℝ) * I - pb_Gam2 q q'| + |I| := abs_sub _ _
    _ ≤ (3 / 4 : ℝ) ^ N / 2 + 16 * (3 / 4 : ℝ) ^ N := add_le_add h1 hI
    _ ≤ 17 * (3 / 4 : ℝ) ^ N := by nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 3 / 4) N]

/-! ### Third moments of the superblock law -/

lemma pb_W_cols (z : PbPat × PbPat → Fin N → ℝ) :
    ∑ t', pb_W (fun t => z (t, t')) = pb_W z ∧ ∑ t, pb_W (fun t' => z (t, t')) = pb_W z := by
  constructor
  · rw [pb_W, Fintype.sum_prod_type (f := fun τ : PbPat × PbPat => pb_P z τ), Finset.sum_comm]
    rfl
  · rw [pb_W, Fintype.sum_prod_type (f := fun τ : PbPat × PbPat => pb_P z τ)]
    rfl

lemma pb_sum_abs_F2_le (a b c d : Fin N) (z : PbPat × PbPat → Fin N → ℝ) :
    ∑ q, |pb_F2 a b c d z q| ≤ 12 * (pb_W z / sigN N) := by
  have hs := sigN_pos N
  rw [show (∑ q : Fin 12, |pb_F2 a b c d z q|) = ∑ q : Fin (6 + 6), |pb_F2 a b c d z q| from rfl,
    Fin.sum_univ_add]
  simp only [pb_F2_left, pb_F2_right]
  have hL : ∑ p : Fin 6, |∑ t', pb_F a b (fun t => z (t, t')) p| ≤ 6 * (pb_W z / sigN N) := by
    calc ∑ p : Fin 6, |∑ t', pb_F a b (fun t => z (t, t')) p|
        ≤ ∑ _p : Fin 6, ∑ t', pb_W (fun t => z (t, t')) / sigN N :=
          sum_le_sum fun p _ => (abs_sum_le_sum_abs _ _).trans
            (sum_le_sum fun t' _ => pb_abs_F_le a b _ p)
      _ = 6 * (pb_W z / sigN N) := by
          rw [← sum_div, (pb_W_cols z).1]; simp
  have hR : ∑ p : Fin 6, |∑ t, pb_F c d (fun t' => z (t, t')) p| ≤ 6 * (pb_W z / sigN N) := by
    calc ∑ p : Fin 6, |∑ t, pb_F c d (fun t' => z (t, t')) p|
        ≤ ∑ _p : Fin 6, ∑ t, pb_W (fun t' => z (t, t')) / sigN N :=
          sum_le_sum fun p _ => (abs_sum_le_sum_abs _ _).trans
            (sum_le_sum fun t _ => pb_abs_F_le c d _ p)
      _ = 6 * (pb_W z / sigN N) := by
          rw [← sum_div, (pb_W_cols z).2]; simp
  linarith

lemma pb_measurable_abs3_12 : Measurable fun x : Fin 12 → ℝ => (∑ q, |x q|) ^ 3 :=
  (Finset.measurable_sum _ fun q _ => (measurable_pi_apply q).abs).pow_const 3

lemma pb_W_le_16 (z : PbPat × PbPat → Fin N → ℝ) : pb_W z ≤ 16 := by
  have := pb_W_le z
  simp only [Fintype.card_prod, Fintype.card_bool] at this
  norm_num at this
  exact this

/-- Integrability of the third absolute moment of `pb_nu2`. -/
theorem pb_nu2_integrable3 (a b c d : Fin N) :
    Integrable (fun x => (∑ q, |x q|) ^ 3) (pb_nu2 a b c d) := by
  rw [pb_nu2, integrable_map_measure pb_measurable_abs3_12.aestronglyMeasurable
    (pb_measurable_F2 a b c d).aemeasurable]
  refine Integrable.of_bound
    (pb_measurable_abs3_12.comp (pb_measurable_F2 a b c d)).aestronglyMeasurable
    ((12 * (16 / sigN N)) ^ 3) (ae_of_all _ fun z => ?_)
  have hs := sigN_pos N
  have h1 := pb_sum_abs_F2_le a b c d z
  have h2 := pb_W_le_16 z
  have h0 : 0 ≤ ∑ q, |pb_F2 a b c d z q| := sum_nonneg fun q _ => abs_nonneg _
  simp only [Function.comp, Real.norm_eq_abs]
  rw [abs_of_nonneg (pow_nonneg h0 3)]
  refine pow_le_pow_left₀ h0 (h1.trans ?_) 3
  gcongr

/-- **Third moments** of the superblock law: `2^(N-4) ∫ (∑ |x q|)^3 dν2 ≤ 442368 (23/25)^N`. -/
theorem pb_nu2_third {a b c d : Fin N} (h : pb_dist4 a b c d) :
    (pb_B2 a b c d : ℝ) * ∫ x, (∑ q, |x q|) ^ 3 ∂pb_nu2 a b c d ≤ 442368 * (23 / 25 : ℝ) ^ N := by
  have hs := sigN_pos N
  have hW3 := pb_integral_W3 (N := N) (K := PbPat × PbPat)
  simp only [Fintype.card_prod, Fintype.card_bool] at hW3
  have hIW : Integrable (fun z : PbPat × PbPat → Fin N → ℝ => pb_W z ^ 3) (pb_supM N) :=
    Integrable.of_bound (pb_measurable_W.pow_const 3).aestronglyMeasurable (16 ^ 3)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (pb_W_nonneg z) 3)]
        exact pow_le_pow_left₀ (pb_W_nonneg z) (pb_W_le_16 z) 3)
  have hbd : ∫ z, (∑ q, |pb_F2 a b c d z q|) ^ 3 ∂pb_supM N ≤
      1728 / sigN N ^ 3 * (4096 * (1 / 4 : ℝ) ^ N) := by
    calc ∫ z, (∑ q, |pb_F2 a b c d z q|) ^ 3 ∂pb_supM N
        ≤ ∫ z, 1728 / sigN N ^ 3 * pb_W z ^ 3 ∂pb_supM N := by
          refine integral_mono_of_nonneg (ae_of_all _ fun z =>
            pow_nonneg (sum_nonneg fun q _ => abs_nonneg _) 3) (hIW.const_mul _)
            (ae_of_all _ fun z => ?_)
          have h1 := pb_sum_abs_F2_le a b c d z
          calc (∑ q, |pb_F2 a b c d z q|) ^ 3 ≤ (12 * (pb_W z / sigN N)) ^ 3 :=
                pow_le_pow_left₀ (sum_nonneg fun q _ => abs_nonneg _) h1 3
            _ = 1728 / sigN N ^ 3 * pb_W z ^ 3 := by field_simp; ring
      _ = 1728 / sigN N ^ 3 * ∫ z, pb_W z ^ 3 ∂pb_supM N := integral_const_mul _ _
      _ ≤ 1728 / sigN N ^ 3 * (4096 * (1 / 4 : ℝ) ^ N) := by
          gcongr
          unfold pb_supM; norm_num at hW3 ⊢; linarith
  rw [pb_nu2, integral_map (pb_measurable_F2 a b c d).aemeasurable
    pb_measurable_abs3_12.aestronglyMeasurable]
  have hB16 : (pb_B2 a b c d : ℝ) * 16 = 2 ^ N := by
    rw [pb_B2_eq h]
    have := pb_four_le h
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 4 := ⟨N - 4, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  have hh := pb_half_div_sig3 N
  have hBp : (0 : ℝ) ≤ pb_B2 a b c d := Nat.cast_nonneg _
  calc (pb_B2 a b c d : ℝ) * ∫ z, (∑ q, |pb_F2 a b c d z q|) ^ 3 ∂pb_supM N
      ≤ (pb_B2 a b c d : ℝ) * (1728 / sigN N ^ 3 * (4096 * (1 / 4 : ℝ) ^ N)) := by gcongr
    _ = 442368 * ((1 / 2 : ℝ) ^ N / sigN N ^ 3) := by
        have e : (2 : ℝ) ^ N * (1 / 4) ^ N = (1 / 2) ^ N := by rw [← mul_pow]; norm_num
        rw [← e, ← hB16]
        field_simp
        ring
    _ ≤ 442368 * (23 / 25 : ℝ) ^ N := by gcongr

/-! ### Removing the superblock of a state -/

/-- Enumeration of the superblocks other than the superblock of `s`. -/
def pb_er2 (a b c d : Fin N) (s : State N) :
    Fin (pb_B2 a b c d - 1) ≃ {γ : PbBlk2 a b c d // γ ≠ pb_blk2 a b c d s} :=
  (Fintype.equivFinOfCardEq (pb_card_ne (pb_blk2 a b c d s))).symm

/-- The summands of the superblocks other than the superblock of `s`. -/
def pb_Yr (a b c d : Fin N) (s : State N) (w : Param N) : Fin (pb_B2 a b c d - 1) → Fin 12 → ℝ :=
  fun k => pb_Y a b c d (pb_er2 a b c d s k).1 w

lemma pb_measurable_Yr (a b c d : Fin N) (s : State N) : Measurable (pb_Yr a b c d s) :=
  Measurable.of_eval fun _ => pb_measurable_Y a b c d _

/-- **Law of the remaining superblock summands**: iid with law `pb_nu2`. -/
theorem pb_map_Yr {a b c d : Fin N} (h : pb_dist4 a b c d) (s : State N) :
    (cubeM N).map (pb_Yr a b c d s) =
      Measure.pi fun _ : Fin (pb_B2 a b c d - 1) => pb_nu2 a b c d := by
  have hc : pb_Yr a b c d s =
      (fun (x : PbBlk2 a b c d → Fin 12 → ℝ) k => x (pb_er2 a b c d s k).1) ∘
      fun w (γ : PbBlk2 a b c d) => pb_Y a b c d γ w := rfl
  rw [hc, ← Measure.map_map (Measurable.of_eval fun k => measurable_pi_apply _)
    (Measurable.of_eval fun γ => pb_measurable_Y a b c d γ), pb_map_Y h]
  exact map_comp_inj _ (Subtype.val_injective.comp (pb_er2 a b c d s).injective) _

/-- `η₂` is the sum of the remaining summands plus the summand of the superblock of `s`. -/
theorem pb_eta2_eq_rest {a b c d : Fin N} (h : pb_dist4 a b c d) (s : State N) (w : Param N) :
    pb_eta2 w a b c d = ∑ k, pb_Yr a b c d s w k + pb_Y a b c d (pb_blk2 a b c d s) w := by
  rw [pb_eta2_eq_sum_blk h, Fintype.sum_eq_add_sum_compl (pb_blk2 a b c d s), add_comm]
  congr 1
  rw [Finset.sum_subtype ({pb_blk2 a b c d s}ᶜ : Finset (PbBlk2 a b c d))
    (p := fun γ => γ ≠ pb_blk2 a b c d s) (by simp), ← (pb_er2 a b c d s).sum_comp]
  rfl

/-- On `g2` each superblock summand is at most `16 tauN N / sigN N` in every coordinate. -/
lemma pb_abs_Y_le {a b c d : Fin N} {w : Param N} (h2 : ∀ i r, Qw w i r ≤ tauN N)
    (γ : PbBlk2 a b c d) (q : Fin 12) : |pb_Y a b c d γ w q| ≤ 16 * tauN N / sigN N := by
  have hP : ∀ (y : PbPat → Fin N → ℝ), (∀ u, ∃ r, y u = w r) → ∀ u, pb_P y u ≤ tauN N := by
    intro y hy u
    obtain ⟨r, hr⟩ := hy u
    have := pb_Pw_le_tau a h2 r
    simp only [pb_P, hr]; exact this
  refine pb_fin12_cases (P := fun q => |pb_Y a b c d γ w q| ≤ 16 * tauN N / sigN N)
    (fun p => ?_) (fun p => ?_) q
  · rw [pb_Y, pb_F2_left]
    calc |∑ t', pb_F a b (fun t => w (pb_row2 a b c d γ (t, t'))) p|
        ≤ ∑ t' : PbPat, |pb_F a b (fun t => w (pb_row2 a b c d γ (t, t'))) p| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t' : PbPat, 4 * tauN N / sigN N :=
          sum_le_sum fun t' _ => pb_abs_F_le_tau a b (hP _ fun u => ⟨_, rfl⟩) p
      _ = 16 * tauN N / sigN N := by simp; ring
  · rw [pb_Y, pb_F2_right]
    calc |∑ t, pb_F c d (fun t' => w (pb_row2 a b c d γ (t, t'))) p|
        ≤ ∑ t : PbPat, |pb_F c d (fun t' => w (pb_row2 a b c d γ (t, t'))) p| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t : PbPat, 4 * tauN N / sigN N :=
          sum_le_sum fun t _ => pb_abs_F_le_tau c d (hP _ fun u => ⟨_, rfl⟩) p
      _ = 16 * tauN N / sigN N := by simp; ring

/-- **Removing the superblock of `s`** changes every coordinate of `η₂` by at most
`16 τ_N / σ_N` on `g2`. -/
theorem pb_abs_eta2_sub_le {a b c d : Fin N} (h : pb_dist4 a b c d) (s : State N) {w : Param N}
    (h2 : ∀ i r, Qw w i r ≤ tauN N) (q : Fin 12) :
    |pb_eta2 w a b c d q - (∑ k, pb_Yr a b c d s w k) q| ≤ 16 * tauN N / sigN N := by
  rw [pb_eta2_eq_rest h s w, Pi.add_apply, add_sub_cancel_left]
  exact pb_abs_Y_le h2 _ q

/-- The sixteen rows of the superblock of `s`, as a random element. -/
def pb_blockRows2 (a b c d : Fin N) (s : State N) (w : Param N) : PbPat × PbPat → Fin N → ℝ :=
  fun τ => w (pb_row2 a b c d (pb_blk2 a b c d s) τ)

lemma pb_measurable_blockRows2 (a b c d : Fin N) (s : State N) :
    Measurable (pb_blockRows2 a b c d s) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- **Independence**: the remaining superblock summands are independent of the rows of the
superblock of `s`. -/
theorem pb_indep_rest2 (a b c d : Fin N) (s : State N) :
    IndepFun (pb_blockRows2 a b c d s) (pb_Yr a b c d s) (cubeM N) := by
  have hI : iIndepFun (fun r (w : Param N) => w r) (cubeM N) :=
    iIndepFun_rows (fun _ v => v) fun _ => measurable_id
  set Sr := univ.filter fun r : State N => pb_blk2 a b c d r = pb_blk2 a b c d s
  set Tr := univ.filter fun r : State N => pb_blk2 a b c d r ≠ pb_blk2 a b c d s
  have hST : Disjoint Sr Tr := by
    rw [Finset.disjoint_filter]; intro r _ h h'; exact h' h
  have h := hI.indepFun_finset Sr Tr hST fun r => measurable_pi_apply r
  have hS : ∀ τ, pb_row2 a b c d (pb_blk2 a b c d s) τ ∈ Sr := fun τ => by
    simp [Sr, pb_blk2_row2]
  have hT : ∀ k τ, pb_row2 a b c d (pb_er2 a b c d s k).1 τ ∈ Tr := fun k τ => by
    simp only [Tr, mem_filter, mem_univ, true_and, pb_blk2_row2]
    exact (pb_er2 a b c d s k).2
  let φ : (Sr → Fin N → ℝ) → PbPat × PbPat → Fin N → ℝ := fun x τ => x ⟨_, hS τ⟩
  let ψ : (Tr → Fin N → ℝ) → Fin (pb_B2 a b c d - 1) → Fin 12 → ℝ :=
    fun x k => pb_F2 a b c d fun τ => x ⟨_, hT k τ⟩
  have hφ : Measurable φ := Measurable.of_eval fun _ => measurable_pi_apply _
  have hψ : Measurable ψ := Measurable.of_eval fun _ =>
    (pb_measurable_F2 a b c d).comp (Measurable.of_eval fun _ => measurable_pi_apply _)
  exact h.comp hφ hψ

end

end Census
end IIT
