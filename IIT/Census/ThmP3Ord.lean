/-
Census: ordered triples, their fields, relabellings, and the joint layout of two triples.

* `tp_ord S`: the increasing ordering of a 3-set `S`; `tp_fld e w`: the centred field of an ordered
  triple, `ξ_i(t) = (Num_i(t) - a₃)/σ_N`, which is the sum of the block summands (`tp_fld_sum`) and a
  coordinate of the joint superblock sum of two triples (`tp_fld_j0`, `tp_fld_j1`).
* Relabelling the units of the ordering by `σ` relabels the coordinates by `(i, t) ↦ (σ i, σ·t)`
  (`tp_fld_comp`, `tp_dfld_comp`); on naturals this is `tp_relN` (`tp_rel_val`), so the
  relabelled difference of the interior point is `tp_zD` (`tp_Dz_rel`).
* Two triples sharing one or two units have orderings `σ`-related to the increasing ones that are
  in the joint layout `bg_JPair` (`tp_jpair1`, `tp_jpair2`); disjoint triples are in the layout
  with `m = 0` as they are (`tp_jpair0`).
-/
import IIT.Census.ThmP3CertS

namespace IIT
namespace Census

open Finset

noncomputable section

variable {N : ℕ}

/-! ### Ordered triples -/

/-- The increasing ordering of a 3-set. -/
def tp_ord (S : Finset (Fin N)) (hS : S.card = 3) : Fin 3 → Fin N := fun i => S.orderEmbOfFin hS i

lemma tp_ord_inj (S : Finset (Fin N)) (hS : S.card = 3) : Function.Injective (tp_ord S hS) :=
  (S.orderEmbOfFin hS).injective

lemma tp_ord_mem (S : Finset (Fin N)) (hS : S.card = 3) (i : Fin 3) : tp_ord S hS i ∈ S :=
  S.orderEmbOfFin_mem hS i

lemma tp_ord_surj (S : Finset (Fin N)) (hS : S.card = 3) {x : Fin N} (hx : x ∈ S) :
    ∃ i, tp_ord S hS i = x := by
  have h := S.range_orderEmbOfFin hS
  have : x ∈ Set.range (S.orderEmbOfFin hS) := by rw [h]; exact hx
  obtain ⟨i, hi⟩ := this
  exact ⟨i, hi⟩

lemma tp_U_comp_perm (e : Fin 3 → Fin N) (σ : Equiv.Perm (Fin 3)) : bg_U (e ∘ σ) = bg_U e := by
  unfold bg_U
  rw [← image_image, image_univ_equiv]

lemma tp_U_ord (S : Finset (Fin N)) (hS : S.card = 3) : bg_U (tp_ord S hS) = S := by
  ext x
  simp only [bg_U, mem_image, mem_univ, true_and]
  exact ⟨fun ⟨i, hi⟩ => hi ▸ tp_ord_mem S hS i, fun hx => tp_ord_surj S hS hx⟩

/-! ### Fields -/

/-- The centred field of an ordered triple. -/
def tp_fld (e : Fin 3 → Fin N) (w : Param N) : Fin (3 * 2 ^ 3) → ℝ :=
  fun p => (Num w (bg_U e) (bg_U e) (bg_pst e (gg_pat 3 p)) (e (gg_unit 3 p)) - bg_ak 3) / sigN N

/-- The difference field of an ordered triple. -/
def tp_dfld (e : Fin 3 → Fin N) (w : Param N) : Fin (3 * 2 ^ 3) → ℝ :=
  tp_Dif (tp_base 3) (tp_fld e w)

lemma tp_fld_sum {e : Fin 3 → Fin N} (he : Function.Injective e) (w : Param N) :
    ∑ β, bg_sX he β w = tp_fld e w := funext (bg_s_sum he w)

lemma tp_fld_j0 {m : ℕ} {e0 e1 : Fin 3 → Fin N} (h : bg_JPair 3 m e0 e1) (w : Param N)
    (p : Fin (3 * 2 ^ 3)) : (∑ γ, bg_jX h γ w) (gg_jidx 3 0 p) = tp_fld e0 w p :=
  bg_j_sum0 h w p

lemma tp_fld_j1 {m : ℕ} {e0 e1 : Fin 3 → Fin N} (h : bg_JPair 3 m e0 e1) (w : Param N)
    (p : Fin (3 * 2 ^ 3)) : (∑ γ, bg_jX h γ w) (gg_jidx 3 1 p) = tp_fld e1 w p :=
  bg_j_sum1 h w p

/-- The joint difference field is the pair of the difference fields. -/
lemma tp_fullDJ_eq {m : ℕ} {e0 e1 : Fin 3 → Fin N} (h : bg_JPair 3 m e0 e1) (w : Param N) :
    tp_fullDJ 3 h w = tp_join 3 (tp_dfld e0 w) (tp_dfld e1 w) := by
  funext P
  have hs : ∑ b, bg_jXs h w b = ∑ γ, bg_jX h γ w := bg_j_sum_Xs h w
  obtain ⟨w', p, rfl⟩ : ∃ w' p, P = gg_jidx 3 w' p := ⟨_, _, (tp_jidx_jw_jp 3 P).symm⟩
  simp only [tp_fullDJ, tp_Dif, hs, tp_join, tp_dfld, tp_baseJ, gg_jw_jidx, gg_jp_jidx]
  rcases gg_fin2 w' with rfl | rfl
  · rw [tp_fld_j0, tp_fld_j0]; simp
  · rw [tp_fld_j1, tp_fld_j1]; simp

/-! ### Relabellings -/

lemma tp_bits_bitPerm (σ : Equiv.Perm (Fin 3)) (t : Fin (2 ^ 3)) (g : Fin 3) :
    bg_bits 3 (gg_bitPerm 3 σ t) (σ g) = bg_bits 3 t g := by
  have h := congrArg Fin.val (gg_bitPerm_bit 3 σ t g)
  rw [finFunctionFinEquiv_symm_apply_val, finFunctionFinEquiv_symm_apply_val] at h
  simp only [bg_bits, Nat.testBit_eq_decide_div_mod_eq, h]

lemma tp_pst_comp {e : Fin 3 → Fin N} (he : Function.Injective e) (σ : Equiv.Perm (Fin 3))
    (t : Fin (2 ^ 3)) : bg_pst (e ∘ σ) t = bg_pst e (gg_bitPerm 3 σ t) := by
  have he' : Function.Injective (e ∘ σ) := he.comp σ.injective
  funext j
  by_cases hj : j ∈ bg_U e
  · obtain ⟨g, rfl⟩ := bg_mem_U e hj
    have : e g = (e ∘ σ) (σ.symm g) := by simp
    rw [this, bg_pst_E he', Function.comp_apply, bg_pst_E he, ← tp_bits_bitPerm σ t]
  · have hj' : j ∉ bg_U (e ∘ σ) := by rw [tp_U_comp_perm]; exact hj
    simp only [bg_pst]
    rw [bg_row_out _ _ _ hj, bg_row_out _ _ _ hj']

/-- The coordinate relabelling of a unit permutation. -/
def tp_rel (σ : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin (3 * 2 ^ 3)) :=
  gg_relabel 3 σ (gg_bitPerm 3 σ)

lemma tp_fld_comp {e : Fin 3 → Fin N} (he : Function.Injective e) (σ : Equiv.Perm (Fin 3))
    (w : Param N) (p : Fin (3 * 2 ^ 3)) : tp_fld (e ∘ σ) w p = tp_fld e w (tp_rel σ p) := by
  simp only [tp_fld, tp_rel, tp_U_comp_perm, tp_pst_comp he, gg_unit_relabel, gg_pat_relabel,
    Function.comp_apply]

lemma tp_bitPerm_zero (σ : Equiv.Perm (Fin 3)) : gg_bitPerm 3 σ ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := by
  apply Fin.ext
  rw [gg_bitPerm, Equiv.trans_apply, Equiv.trans_apply, finFunctionFinEquiv_apply]
  refine sum_eq_zero fun i _ => ?_
  rw [Equiv.arrowCongr_apply]
  have h0 : finFunctionFinEquiv.symm (0 : Fin (2 ^ 3)) (σ.symm i) = 0 :=
    Fin.ext (by rw [finFunctionFinEquiv_symm_apply_val]; simp)
  simp [h0]

lemma tp_rel_base (σ : Equiv.Perm (Fin 3)) (p : Fin (3 * 2 ^ 3)) :
    tp_rel σ (tp_base 3 p) = tp_base 3 (tp_rel σ p) := by
  apply finProdFinEquiv.symm.injective
  refine Prod.ext ?_ ?_
  · show gg_unit 3 (tp_rel σ (tp_base 3 p)) = gg_unit 3 (tp_base 3 (tp_rel σ p))
    simp only [tp_rel, tp_base, gg_unit_relabel, gg_unit_idx]
  · show gg_pat 3 (tp_rel σ (tp_base 3 p)) = gg_pat 3 (tp_base 3 (tp_rel σ p))
    simp only [tp_rel, tp_base, gg_pat_relabel, gg_pat_idx]
    exact tp_bitPerm_zero σ

lemma tp_dfld_comp {e : Fin 3 → Fin N} (he : Function.Injective e) (σ : Equiv.Perm (Fin 3))
    (w : Param N) (p : Fin (3 * 2 ^ 3)) : tp_dfld (e ∘ σ) w p = tp_dfld e w (tp_rel σ p) := by
  simp only [tp_dfld, tp_Dif, tp_fld_comp he, tp_rel_base]

/-! ### The relabelling on naturals -/

/-- The list of images of a unit permutation. -/
def tp_pl (σ : Equiv.Perm (Fin 3)) : List ℕ := [(σ 0 : ℕ), σ 1, σ 2]

lemma tp_pl_mem (σ : Equiv.Perm (Fin 3)) : tp_pl σ ∈ tp_plist := by
  revert σ; decide

lemma tp_bitPerm_val (σ : Equiv.Perm (Fin 3)) (t : Fin (2 ^ 3)) :
    (gg_bitPerm 3 σ t : ℕ) = tp_bpN (tp_pl σ) t := by
  rw [gg_bitPerm, Equiv.trans_apply, Equiv.trans_apply, finFunctionFinEquiv_apply]
  simp only [Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_apply,
    finFunctionFinEquiv_symm_apply_val]
  rw [← Equiv.sum_comp σ]
  simp only [Equiv.symm_apply_apply]
  rw [tp_bpN, cd_nsumN_eq, ← Fin.sum_univ_eq_sum_range (fun q => (t : ℕ) / 2 ^ q % 2 *
    2 ^ (tp_pl σ).getD q 0) 3]
  refine sum_congr rfl fun q _ => ?_
  fin_cases q <;> simp [tp_pl]

lemma tp_rel_val (σ : Equiv.Perm (Fin 3)) (p : Fin (3 * 2 ^ 3)) :
    (tp_rel σ p : ℕ) = tp_relN (tp_pl σ) p := by
  have h1 : (tp_rel σ p : ℕ) = (gg_bitPerm 3 σ (gg_pat 3 p) : ℕ) + 2 ^ 3 * (σ (gg_unit 3 p) : ℕ) :=
    rfl
  rw [h1, tp_bitPerm_val, gg_pat_val, tp_relN]
  have hu : (σ (gg_unit 3 p) : ℕ) = (tp_pl σ).getD (p / 8) 0 := by
    have hv : (gg_unit 3 p : ℕ) = p / 8 := by rw [gg_unit_val]; norm_num
    have hlt : (p : ℕ) / 8 < 3 := by have := p.2; norm_num at this; omega
    have hg : gg_unit 3 p = ⟨p / 8, hlt⟩ := Fin.ext hv
    rw [hg]
    interval_cases h : (p : ℕ) / 8 <;> simp [tp_pl]
  rw [hu]
  norm_num

lemma tp_cd_z_val (q : Fin (3 * 2 ^ 3)) : cd_z q = (cd_zi.getD q 0 : ℝ) / 2 ^ 24 := by
  rw [cd_z, cd_Dz]; norm_num

/-- The relabelled difference of the interior point. -/
lemma tp_Dz_rel (σ : Equiv.Perm (Fin 3)) (p : Fin (3 * 2 ^ 3)) :
    tp_Dz (tp_rel σ p) = (tp_zD (tp_pl σ) p : ℝ) / 2 ^ 24 := by
  simp only [tp_Dz, tp_Dif]
  rw [← tp_rel_base, tp_cd_z_val, tp_cd_z_val, tp_rel_val, tp_rel_val, tp_base_val, tp_zD]
  push_cast
  ring

/-- The joint centre of two relabelled triples. -/
lemma tp_join_rel (σ0 σ1 : Equiv.Perm (Fin 3)) (y : ℝ) (P : Fin (2 * (3 * 2 ^ 3))) :
    tp_join 3 (fun p => y * tp_Dz (tp_rel σ0 p)) (fun p => y * tp_Dz (tp_rel σ1 p)) P =
      y * ((tp_zc (tp_pl σ0) (tp_pl σ1) P : ℝ) / 2 ^ 24) := by
  have hjw := cd_jw_val 3 P
  have hjp := cd_jp_val 3 P
  norm_num at hjw hjp
  simp only [tp_join, tp_zc]
  rcases gg_fin2 (gg_jw 3 P) with h0 | h1
  · have hP : (P : ℕ) < 24 := by
      have := congrArg Fin.val h0; rw [hjw] at this; simp at this; omega
    have hp : (gg_jp 3 P : ℕ) = P := by rw [hjp, Nat.mod_eq_of_lt hP]
    rw [ite_eq_left h0, tp_Dz_rel, ite_eq_left hP, hp]
  · have hP : ¬ (P : ℕ) < 24 := by
      have := congrArg Fin.val h1; rw [hjw] at this; simp at this; omega
    have hp : (gg_jp 3 P : ℕ) = P - 24 := by
      have := P.2; norm_num at this
      rw [hjp]; omega
    rw [ite_eq_right (by rw [h1]; decide), tp_Dz_rel, ite_eq_right hP, hp]

/-! ### The joint layout of two triples -/

/-- Disjoint triples are in the joint layout with `m = 0`. -/
lemma tp_jpair0 {S S' : Finset (Fin N)} (hS : S.card = 3) (hS' : S'.card = 3) (hd : Disjoint S S') :
    bg_JPair 3 0 (tp_ord S hS) (tp_ord S' hS') := by
  refine ⟨Nat.zero_le _, tp_ord_inj S hS, tp_ord_inj S' hS', fun i i' => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact absurd (h ▸ tp_ord_mem S' hS' i') (disjoint_left.1 hd (tp_ord_mem S hS i))
  · have := i.2; have := i'.2; omega

lemma tp_perm3 {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ σ : Equiv.Perm (Fin 3), σ 0 = a ∧ σ 1 = b ∧ σ 2 = c := by
  have hinj : Function.Injective (![a, b, c] : Fin 3 → Fin 3) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj), rfl, rfl, rfl⟩

/-- Triples sharing one unit has orderings in the joint layout with `m = 1`. -/
lemma tp_jpair1 {S S' : Finset (Fin N)} (hS : S.card = 3) (hS' : S'.card = 3)
    (h1 : (S ∩ S').card = 1) :
    ∃ σ0 σ1 : Equiv.Perm (Fin 3), bg_JPair 3 1 (tp_ord S hS ∘ σ0) (tp_ord S' hS' ∘ σ1) := by
  obtain ⟨x, hx⟩ := card_eq_one.1 h1
  have hxS : x ∈ S ∩ S' := by rw [hx]; exact mem_singleton_self x
  obtain ⟨i0, hi0⟩ := tp_ord_surj S hS (mem_inter.1 hxS).1
  obtain ⟨j0, hj0⟩ := tp_ord_surj S' hS' (mem_inter.1 hxS).2
  refine ⟨Equiv.swap i0 2, Equiv.swap j0 0, by norm_num, (tp_ord_inj S hS).comp (Equiv.injective _),
    (tp_ord_inj S' hS').comp (Equiv.injective _), fun i i' => ⟨fun h => ?_, fun h => ?_⟩⟩
  · simp only [Function.comp_apply] at h
    have hm : tp_ord S hS (Equiv.swap i0 2 i) ∈ S ∩ S' :=
      mem_inter.2 ⟨tp_ord_mem S hS _, h ▸ tp_ord_mem S' hS' _⟩
    rw [hx, mem_singleton, ← hi0] at hm
    have hm' : tp_ord S' hS' (Equiv.swap j0 0 i') ∈ S ∩ S' :=
      mem_inter.2 ⟨h ▸ tp_ord_mem S hS _, tp_ord_mem S' hS' _⟩
    rw [hx, mem_singleton, ← hj0] at hm'
    have e1 := tp_ord_inj S hS hm
    have e2 := tp_ord_inj S' hS' hm'
    have hi : i = 2 := by
      have := congrArg (Equiv.swap i0 2) e1
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    have hi' : i' = 0 := by
      have := congrArg (Equiv.swap j0 0) e2
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    subst hi hi'
    rfl
  · have hi : i = 2 := Fin.ext (by have := i.2; have := i'.2; simp; omega)
    have hi' : i' = 0 := Fin.ext (by have := i.2; have := i'.2; simp; omega)
    subst hi hi'
    simp only [Function.comp_apply, Equiv.swap_apply_right, hi0, hj0]

/-- Triples sharing two units have orderings in the joint layout with `m = 2`. -/
lemma tp_jpair2 {S S' : Finset (Fin N)} (hS : S.card = 3) (hS' : S'.card = 3)
    (h2 : (S ∩ S').card = 2) :
    ∃ σ0 σ1 : Equiv.Perm (Fin 3), bg_JPair 3 2 (tp_ord S hS ∘ σ0) (tp_ord S' hS' ∘ σ1) := by
  obtain ⟨x1, x2, hx12, hx⟩ := card_eq_two.1 h2
  have hx1 : x1 ∈ S ∩ S' := by rw [hx]; simp
  have hx2 : x2 ∈ S ∩ S' := by rw [hx]; simp
  have hd1 : (S \ S').card = 1 := by
    have := card_sdiff_add_card_inter S S'
    omega
  have hd2 : (S' \ S).card = 1 := by
    have := card_sdiff_add_card_inter S' S
    rw [inter_comm] at this
    omega
  obtain ⟨u, hu⟩ := card_eq_one.1 hd1
  obtain ⟨v, hv⟩ := card_eq_one.1 hd2
  have huS : u ∈ S \ S' := by rw [hu]; exact mem_singleton_self u
  have hvS : v ∈ S' \ S := by rw [hv]; exact mem_singleton_self v
  obtain ⟨iu, hiu⟩ := tp_ord_surj S hS (mem_sdiff.1 huS).1
  obtain ⟨i1, hi1⟩ := tp_ord_surj S hS (mem_inter.1 hx1).1
  obtain ⟨i2, hi2⟩ := tp_ord_surj S hS (mem_inter.1 hx2).1
  obtain ⟨j1, hj1⟩ := tp_ord_surj S' hS' (mem_inter.1 hx1).2
  obtain ⟨j2, hj2⟩ := tp_ord_surj S' hS' (mem_inter.1 hx2).2
  obtain ⟨jv, hjv⟩ := tp_ord_surj S' hS' (mem_sdiff.1 hvS).1
  have hux1 : u ≠ x1 := fun h => (mem_sdiff.1 huS).2 (h ▸ (mem_inter.1 hx1).2)
  have hux2 : u ≠ x2 := fun h => (mem_sdiff.1 huS).2 (h ▸ (mem_inter.1 hx2).2)
  have hvx1 : v ≠ x1 := fun h => (mem_sdiff.1 hvS).2 (h ▸ (mem_inter.1 hx1).1)
  have hvx2 : v ≠ x2 := fun h => (mem_sdiff.1 hvS).2 (h ▸ (mem_inter.1 hx2).1)
  have huv : u ≠ v := fun h => (mem_sdiff.1 huS).2 (h ▸ (mem_sdiff.1 hvS).1)
  have ne : ∀ {a b : Fin 3} {e : Fin 3 → Fin N} {p q : Fin N}, e a = p → e b = q → p ≠ q → a ≠ b :=
    fun ha hb hpq hab => hpq (by rw [← ha, ← hb, hab])
  obtain ⟨σ0, h00, h01, h02⟩ := tp_perm3 (ne hiu hi1 hux1) (ne hiu hi2 hux2) (ne hi1 hi2 hx12)
  obtain ⟨σ1, h10, h11, h12⟩ := tp_perm3 (ne hj1 hj2 hx12) (ne hj1 hjv (Ne.symm hvx1))
    (ne hj2 hjv (Ne.symm hvx2))
  refine ⟨σ0, σ1, by norm_num, (tp_ord_inj S hS).comp (Equiv.injective _),
    (tp_ord_inj S' hS').comp (Equiv.injective _), fun i i' => ?_⟩
  have a0 : tp_ord S hS (σ0 0) = u := by rw [h00, hiu]
  have a1 : tp_ord S hS (σ0 1) = x1 := by rw [h01, hi1]
  have a2 : tp_ord S hS (σ0 2) = x2 := by rw [h02, hi2]
  have b0 : tp_ord S' hS' (σ1 0) = x1 := by rw [h10, hj1]
  have b1 : tp_ord S' hS' (σ1 1) = x2 := by rw [h11, hj2]
  have b2 : tp_ord S' hS' (σ1 2) = v := by rw [h12, hjv]
  fin_cases i <;> fin_cases i' <;>
    simp [a0, a1, a2, b0, b1, b2, hux1, hux2, huv, hx12, hx12.symm, hvx1.symm, hvx2.symm]

end

end Census
end IIT
