/-
Census: from the field of a triple to the hypotheses of `tl_triple_lower`.

For an ordered triple `e` onto `S` and `w = flipP s z`, the forms of `TripleLower` are the forms of
`CertDataBase` evaluated at the field `ξ = tp_fld e w`, shifted by any per-unit constants:
`tl_F w θ t₀ σ_N = cd_F 3 C 0 ξ'` where `C` is the profile of `θ` pulled back along `e`
(`tp_F_bridge`), `sysCutCount θ = cd_cc 3 C` (`tp_cc_bridge`), and the argmax rows are the sums of
the numerators at the patterns (`tp_marg_bridge`).  On the good event every numerator of a triple is
within `tp_eta N` of `a₃ = 25/48` (`tp_levels`).  Combining these with `tl_triple_lower`, the
effect box (`tp_eff`) and the interior point (`cd_point_ball`): if the difference field of the
increasing ordering of `S` is within `1` of `y Δz` with `y ≥ 20000`, then
`φ_s(S) ≥ σ_N (y - e_N) / (8 a₃ ln 2)` (`tp_det`).
-/
import IIT.Census.ThmP3Ord
import IIT.Census.ThmP3Eff
import IIT.Census.CertDataStar
import IIT.Census.CertDataClass
import IIT.Census.BigPhiDet
import IIT.Census.TightStats

namespace IIT
namespace Census

open Finset

noncomputable section

variable {N : ℕ}

/-! ### Patterns -/

lemma tp_pst_zero (e : Fin 3 → Fin N) : bg_pst e ⟨0, by norm_num⟩ = (tl_t0 : State N) := by
  funext j
  simp only [bg_pst, bg_row, tl_t0]
  split_ifs
  · simp [bg_bits]
  · rfl

/-- The pattern of a state along `e`. -/
def tp_patOf (e : Fin 3 → Fin N) (t : State N) : Fin (2 ^ 3) :=
  finFunctionFinEquiv fun q : Fin 3 => if t (e q) then 1 else 0

lemma tp_bits_ffe (u : Fin (2 ^ 3)) (g : Fin 3) :
    bg_bits 3 u g = decide ((finFunctionFinEquiv.symm u g : ℕ) = 1) := by
  rw [bg_bits, Nat.testBit_eq_decide_div_mod_eq, finFunctionFinEquiv_symm_apply_val]

lemma tp_pst_patOf {e : Fin 3 → Fin N} (he : Function.Injective e) (t : State N)
    (ht : ∀ j ∉ bg_U e, t j = false) : bg_pst e (tp_patOf e t) = t := by
  funext j
  by_cases hj : j ∈ bg_U e
  · obtain ⟨g, rfl⟩ := bg_mem_U e hj
    rw [bg_pst_E he, tp_bits_ffe, tp_patOf, Equiv.symm_apply_apply]
    cases t (e g) <;> simp
  · rw [ht j hj]
    simp only [bg_pst]
    rw [bg_row_out _ _ _ hj]

lemma tp_patOf_pst {e : Fin 3 → Fin N} (he : Function.Injective e) (u : Fin (2 ^ 3)) :
    tp_patOf e (bg_pst e u) = u := by
  apply finFunctionFinEquiv.symm.injective
  rw [tp_patOf, Equiv.symm_apply_apply]
  funext q
  rw [bg_pst_E he, tp_bits_ffe]
  have h2 := (finFunctionFinEquiv.symm u q).2
  apply Fin.ext
  by_cases h : (finFunctionFinEquiv.symm u q : ℕ) = 1
  · simp [h]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, Fin.val_zero]
    omega

/-! ### The averaging sums -/

section Bridge

variable {e : Fin 3 → Fin N} (he : Function.Injective e) {S : Finset (Fin N)} (hU : bg_U e = S)

include he hU

/-- The states agreeing with `t₀` off a cut set `C ⊆ S` are the patterns of `e` vanishing off
`C`. -/
lemma tp_sum_agree {C : Finset (Fin N)} (hCS : C ⊆ S) (Cl : List (List Bool)) (i : Fin 3)
    (hC : ∀ j : Fin 3, e j ∈ C ↔ cd_at Cl i j = true) (F : State N → ℝ) :
    ∑ t ∈ agree ((S \ C) ∪ Sᶜ) tl_t0, F t =
      ∑ u : Fin (2 ^ 3), if cd_agree 3 (cd_at Cl i) u 0 = true then F (bg_pst e u) else 0 := by
  rw [← sum_filter]
  have hmemA : ∀ t, t ∈ agree ((S \ C) ∪ Sᶜ) tl_t0 ↔ ∀ j, j ∉ C → t j = false := by
    intro t
    rw [mem_agree]
    constructor
    · intro h j hj
      by_cases hjS : j ∈ S
      · exact h j (mem_union_left _ (mem_sdiff.2 ⟨hjS, hj⟩))
      · exact h j (mem_union_right _ (mem_compl.2 hjS))
    · intro h j hj
      rcases mem_union.1 hj with h1 | h1
      · exact h j (mem_sdiff.1 h1).2
      · exact h j (fun hc => (mem_compl.1 h1) (hCS hc))
  have hag : ∀ u : Fin (2 ^ 3), cd_agree 3 (cd_at Cl i) u 0 = true ↔
      ∀ q : Fin 3, cd_at Cl i q = false → bg_bits 3 u q = false := by
    intro u
    rw [cd_agree_iff]
    constructor
    · intro h q hq
      have := h q q.2 hq
      simpa [bg_bits] using this
    · intro h q hq hr
      have := h ⟨q, hq⟩ hr
      simpa [bg_bits] using this
  refine sum_nbij' (fun t => tp_patOf e t) (fun u => bg_pst e u) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    have ht' := (hmemA t).1 ht
    simp only [mem_filter, mem_univ, true_and]
    rw [hag]
    intro q hq
    have hq' : e q ∉ C := fun h => by rw [(hC q).1 h] at hq; exact absurd hq (by simp)
    rw [tp_bits_ffe, tp_patOf, Equiv.symm_apply_apply, ht' _ hq']
    simp
  · intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    rw [hag] at hu
    rw [hmemA]
    intro j hj
    by_cases hjU : j ∈ bg_U e
    · obtain ⟨g, rfl⟩ := bg_mem_U e hjU
      rw [bg_pst_E he]
      exact hu g (by
        have := (hC g).not.1 hj
        simpa using this)
    · simp only [bg_pst]; rw [bg_row_out _ _ _ hjU]
  · intro t ht
    have ht' := (hmemA t).1 ht
    exact tp_pst_patOf he t fun j hj => ht' j (fun hc => hj (hU ▸ hCS hc))
  · intro u _
    exact tp_patOf_pst he u
  · intro t ht
    have ht' := (hmemA t).1 ht
    rw [tp_pst_patOf he t fun j hj => ht' j (fun hc => hj (hU ▸ hCS hc))]

omit he in
lemma tp_cut_eq {C : Finset (Fin N)} (hCS : C ⊆ S) (Cl : List (List Bool)) (i : Fin 3)
    (hC : ∀ j : Fin 3, e j ∈ C ↔ cd_at Cl i j = true) :
    C = (univ.filter fun j : Fin 3 => cd_at Cl i j = true).image e := by
  ext x
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · intro hx
    obtain ⟨g, rfl⟩ := bg_mem_U e (hU ▸ hCS hx)
    exact ⟨g, (hC g).1 hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact (hC g).2 hg

lemma tp_card_cut {C : Finset (Fin N)} (hCS : C ⊆ S) (Cl : List (List Bool)) (i : Fin 3)
    (hC : ∀ j : Fin 3, e j ∈ C ↔ cd_at Cl i j = true) : C.card = cd_card 3 Cl i := by
  rw [tp_cut_eq hU hCS Cl i hC, card_image_of_injective _ he, cd_card, cd_cnt_eq]

lemma tp_count {C : Finset (Fin N)} (hCS : C ⊆ S) (Cl : List (List Bool)) (i : Fin 3)
    (hC : ∀ j : Fin 3, e j ∈ C ↔ cd_at Cl i j = true) :
    (∑ u : Fin (2 ^ 3), if cd_agree 3 (cd_at Cl i) u 0 = true then (1 : ℝ) else 0) =
      2 ^ cd_card 3 Cl i := by
  have h := tp_sum_agree he hU hCS Cl i hC (fun _ => (1 : ℝ))
  rw [← h, sum_const, nsmul_eq_mul, mul_one, card_agree]
  have hS3 : S.card ≤ N := by simpa using card_le_univ S
  have hCS' : C.card ≤ S.card := card_le_card hCS
  have hM : ((S \ C) ∪ Sᶜ).card = N - C.card := by
    rw [card_union_of_disjoint (disjoint_left.2 fun x hx hx' =>
      (mem_compl.1 hx') (mem_sdiff.1 hx).1), card_sdiff_of_subset hCS, card_compl,
      Fintype.card_fin]
    omega
  rw [hM, tp_card_cut he hU hCS Cl i hC]
  have : C.card ≤ N := hCS'.trans hS3
  rw [tp_card_cut he hU hCS Cl i hC] at this
  push_cast
  congr 1
  omega

omit he in
lemma tp_Num_fld (w : Param N) (u : Fin (2 ^ 3)) (i : Fin 3) :
    Num w S S (bg_pst e u) (e i) = bg_ak 3 + sigN N * tp_fld e w (cd_idx 3 i u) := by
  have hσ := sigN_pos N
  unfold tp_fld
  rw [gg_pat_idx, gg_unit_idx, hU]
  field_simp
  ring

lemma tp_sum_S (f : Fin N → ℝ) : ∑ x ∈ S, f x = ∑ i : Fin 3, f (e i) := by
  rw [← hU, bg_U, sum_image fun x _ y _ h => he h]

/-- **The forms through the field.** -/
theorem tp_F_bridge (w : Param N) (θ : SysPartition N S) (Cl : List (List Bool))
    (hC : ∀ i j : Fin 3, e j ∈ profile θ (e i) ↔ cd_at Cl i j = true)
    (ξ' : Fin (3 * 2 ^ 3) → ℝ) (c : Fin 3 → ℝ)
    (hξ : ∀ p, ξ' p = tp_fld e w p + c (gg_unit 3 p)) :
    tl_F w θ tl_t0 (sigN N) = cd_F 3 Cl 0 ξ' := by
  have hσ := sigN_pos N
  have hF := cd_F_eq 3 Cl ⟨0, by norm_num⟩ ξ'
  rw [hF, tl_F, tp_sum_S he hU, sum_div]
  refine sum_congr rfl fun i _ => ?_
  have hCS := prof_profile_subset θ (e i)
  set C := profile θ (e i) with hCdef
  have hCi : ∀ j : Fin 3, e j ∈ C ↔ cd_at Cl i j = true := hC i
  have hcount := tp_count he hU hCS Cl i hCi
  have hcard : S.card - (S \ C).card = cd_card 3 Cl i := by
    rw [card_sdiff_of_subset hCS, ← tp_card_cut he hU hCS Cl i hCi]
    have := card_le_card hCS
    omega
  set A : Fin (2 ^ 3) → Prop := fun u => cd_agree 3 (cd_at Cl i) u 0 = true
  have hsum : ∑ t ∈ agree ((S \ C) ∪ Sᶜ) tl_t0, Num w S S t (e i) =
      (bg_ak 3 - sigN N * c i) * 2 ^ cd_card 3 Cl i +
        sigN N * ∑ u : Fin (2 ^ 3), (if A u then ξ' (cd_idx 3 i u) else 0) := by
    rw [tp_sum_agree he hU hCS Cl i hCi, ← hcount, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun u _ => ?_
    simp only [A]
    split_ifs
    · rw [tp_Num_fld hU, hξ, gg_unit_idx]; ring
    · ring
  have h0 : Num w S S tl_t0 (e i) = bg_ak 3 + sigN N * (ξ' (cd_idx 3 i ⟨0, by norm_num⟩) - c i) := by
    rw [← tp_pst_zero e, tp_Num_fld hU, hξ, gg_unit_idx]; ring
  have hNum := Num_eq_avg w S (S \ C) tl_t0 (e i)
  have hsd : (S \ C) ∪ Sᶜ = (S \ C) ∪ Sᶜ := rfl
  rw [hsum, hcard] at hNum
  unfold tl_D
  rw [hNum, h0]
  have h2 : (0 : ℝ) < 2 ^ cd_card 3 Cl i := by positivity
  field_simp
  ring

/-- **The normaliser through the profile table.** -/
theorem tp_cc_bridge (θ : SysPartition N S) (Cl : List (List Bool))
    (hC : ∀ i j : Fin 3, e j ∈ profile θ (e i) ↔ cd_at Cl i j = true) :
    (sysCutCount θ : ℝ) = cd_cc 3 Cl := by
  rw [sysCutCount_eq_sum_profile, cd_cc, cd_nsumN_eq]
  push_cast
  rw [tp_sum_S he hU (fun x => ((profile θ x).card : ℝ)),
    ← Fin.sum_univ_eq_sum_range (fun i => ((cd_card 3 Cl i : ℕ) : ℝ)) 3]
  refine sum_congr rfl fun i _ => ?_
  rw [tp_card_cut he hU (prof_profile_subset θ (e i)) Cl i (hC i)]

/-- **The argmax rows through the field.** -/
theorem tp_marg_bridge (w : Param N) (ξ' : Fin (3 * 2 ^ 3) → ℝ) (c : Fin 3 → ℝ)
    (hξ : ∀ p, ξ' p = tp_fld e w p + c (gg_unit 3 p)) (t : Fin (2 ^ 3)) :
    cd_lin 3 (cd_argc 3 t) ξ' * sigN N =
      ∑ x ∈ S, Num w S S tl_t0 x - ∑ x ∈ S, Num w S S (bg_pst e t) x := by
  rw [cd_lin_argc, tp_sum_S he hU, tp_sum_S he hU, ← sum_sub_distrib, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [← tp_pst_zero e, tp_Num_fld hU, tp_Num_fld hU, hξ, hξ, gg_unit_idx, gg_unit_idx]
  ring

end Bridge

/-! ### Levels -/

/-- The level precision of a triple on the good event. -/
def tp_eta (N : ℕ) : ℝ :=
  dsmall N 3 + 17 * N * sigN N + 2 * LkN N 3 * (Real.sqrt 3 * sigN N + tauN N)

lemma tp_eta_nonneg {N : ℕ} (hN : 1 ≤ N) : 0 ≤ tp_eta N := by
  have := LkN_nonneg' 3 hN
  have := sigN_pos N
  have := tauN_pos N
  have : 0 ≤ dsmall N 3 := by unfold dsmall; positivity
  unfold tp_eta; positivity

lemma tp_subSum_empty (w : Param N) (i : Fin N) (t : State N) : subSum w i ∅ t = ZQ w i := by
  unfold subSum ZQ
  congr 1
  ext r; simp [mem_agree]

/-- **Levels**: on the good event every numerator of a triple is within `tp_eta N` of `a₃`. -/
theorem tp_levels {s : State N} {w : Param N} (hG : GoodW N s w) (hZ : gZ N w) (hN : 1 ≤ N)
    {S : Finset (Fin N)} (hS : S.card = 3) {Y : Finset (Fin N)} (hY : Y ⊆ S) (t : State N)
    {i : Fin N} (hi : i ∈ S) : |Num w S Y t i - tl_aTrip| ≤ tp_eta N := by
  have h1 := dev_le_dsmall hG hN hi hY t
  rw [hS] at h1
  have h3 := hG.g13b S i Y ∅ t hi hY (empty_subset S)
  rw [hS] at h3
  have h11 := hG.g11 i
  have hz : |Zs w - 1| ≤ 16 * N * sigN N := hZ
  have hY3 : Y.card ≤ 3 := hS ▸ card_le_card hY
  have hDQ : DQ w S Y ∅ t i = subSum w i Y t / 2 ^ (3 - Y.card) - ZQ w i / 8 := by
    rw [DQ, tp_subSum_empty, hS, card_empty]; norm_num
  have hc : cNum w S Y t i = ZQ w i * (25 / 96) + DQ w S Y ∅ t i / 12 := by
    rw [hDQ, cNum, hS]
    have h2 : (0 : ℝ) < 2 ^ (3 - Y.card) := by positivity
    field_simp
    ring
  have hL := LkN_nonneg' 3 hN
  have hσ := sigN_pos N
  have hτ := tauN_pos N
  rw [abs_le] at h1 h3 h11 hz
  rw [abs_le, tp_eta, tl_aTrip]
  rw [hc] at h1
  have hs3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  constructor <;> nlinarith

/-- `tp_eta N ≤ 150 N σ_N` for large `N`. -/
lemma tp_eta_le : ∀ᶠ N : ℕ in Filter.atTop, tp_eta N ≤ 150 * N * sigN N := by
  filter_upwards [Filter.eventually_ge_atTop 1,
    ev_poly_geom 7 vkRate_pos.le vkRate_lt_one 1024 one_pos] with N hN hρ
  have hk : 3 ≤ KN N := by unfold KN; omega
  have hV := Vbd_le_seven hN hk hρ
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg hN'
  have hl1 : Real.log N ≤ N := Real.log_le_self (by positivity)
  have hL : LkN N 3 ≤ 14 * N := by unfold LkN; push_cast; nlinarith
  have hL0 := LkN_nonneg' 3 hN
  have hσ := sigN_pos N
  have hτ := tauN_le_two_sigN N
  have hτ0 := tauN_pos N
  have hs3 : Real.sqrt 3 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hds : dsmall N 3 ≤ 20 * N * sigN N := by
    unfold dsmall
    have : Real.sqrt (LkN N 3 * Vbd N 3) ≤ 10 * N * sigN N := by
      rw [Real.sqrt_le_left (by positivity)]
      have h7 : LkN N 3 * Vbd N 3 ≤ 14 * N * (7 * sigN N ^ 2) :=
        mul_le_mul hL hV (by unfold Vbd; have := vkRate_pos; positivity) (by positivity)
      nlinarith
    linarith
  have hs3' : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  unfold tp_eta
  have : 2 * LkN N 3 * (Real.sqrt 3 * sigN N + tauN N) ≤ 2 * (14 * N) * (4 * sigN N) := by
    gcongr; nlinarith
  nlinarith

lemma tp_ord_ne (S : Finset (Fin N)) (hS : S.card = 3) {i j : Fin 3} (h : i ≠ j) :
    tp_ord S hS i ≠ tp_ord S hS j := fun e => h (tp_ord_inj S hS e)

lemma tp_S_eq (S : Finset (Fin N)) (hS : S.card = 3) :
    S = {tp_ord S hS 0, tp_ord S hS 1, tp_ord S hS 2} := by
  ext x
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hx
    obtain ⟨i, rfl⟩ := tp_ord_surj S hS hx
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl) <;> exact tp_ord_mem S hS _

lemma tp_ord3_eq (S : Finset (Fin N)) (hS : S.card = 3) (h01 h02 h12) (i : Fin 3) :
    cd_ord3 (tp_ord S hS 0) (tp_ord S hS 1) (tp_ord S hS 2) h01 h02 h12 i = tp_ord S hS i := by
  fin_cases i <;> rfl

/-- **The deterministic lower bound for a triple.** For large `N`, on the good event, in the effect
box, if the difference field of the increasing ordering of `S` lies within `1` of `y Δz` with
`y ≥ 20000`, then `φ_s(S) ≥ σ_N (y - 6 η²/((a₃ - η) σ_N)) / (8 a₃ ln 2)`, `η = tp_eta N`. -/
theorem tp_det : ∀ᶠ N : ℕ in Filter.atTop, ∀ (s : State N) (z : Param N) (S : Finset (Fin N))
    (hS : S.card = 3) (y : ℝ), z ∈ openCube N → GoodW N s (flipP s z) → gZ N (flipP s z) →
    tp_effBoxZ z s S → 20000 ≤ y →
    (∀ p, |tp_dfld (tp_ord S hS) (flipP s z) p - y * tp_Dz p| ≤ 1) →
    sigN N * (y - 6 * tp_eta N ^ 2 / ((tl_aTrip - tp_eta N) * sigN N)) /
      (8 * tl_aTrip * Real.log 2) ≤ phi z s S := by
  filter_upwards [Filter.eventually_ge_atTop 1, tp_eta_le,
    ev_pow_mul_sigN 1 (C := 150) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 100),
    ev_pow_mul_sigN 2 (C := 810000) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 1000)]
    with N hN hηle hsm1 hsm2
  intro s z S hS y hz hG hZ hbox hy hball
  set w := flipP s z with hw
  set e := tp_ord S hS with he_def
  have he : Function.Injective e := tp_ord_inj S hS
  set a := e 0
  set b := e 1
  set c := e 2
  have hab : a ≠ b := tp_ord_ne S hS (by decide)
  have hac : a ≠ c := tp_ord_ne S hS (by decide)
  have hbc : b ≠ c := tp_ord_ne S hS (by decide)
  have hSabc : S = {a, b, c} := tp_S_eq S hS
  have hU : bg_U e = ({a, b, c} : Finset (Fin N)) := by rw [tp_U_ord, ← hSabc]
  have hcard : ({a, b, c} : Finset (Fin N)).card = 3 := tl_card3 hab hac hbc
  have hσ := sigN_pos N
  have hη0 := tp_eta_nonneg hN
  set η := tp_eta N with hηdef
  have hηs : η ≤ 1 / 100 := by
    have : 150 * (N : ℝ) ^ 1 * sigN N ≤ 1 / 100 := hsm1
    rw [pow_one] at this; linarith
  have hy0 : 0 < y := by linarith
  -- the shifted field
  set ξ := tp_fld e w with hξdef
  set cs : Fin 3 → ℝ := fun i =>
    y * cd_z (cd_idx 3 i ⟨0, by norm_num⟩) - ξ (cd_idx 3 i ⟨0, by norm_num⟩) with hcs
  set ξ' : Fin (3 * 2 ^ 3) → ℝ := fun p => ξ p + cs (gg_unit 3 p) with hξ'def
  have hξ' : ∀ p, ξ' p = tp_fld e w p + cs (gg_unit 3 p) := fun p => rfl
  have hball' : ∀ p, |ξ' p - y * cd_z p| ≤ y / 20000 := by
    intro p
    have h1 := hball p
    have e1 : ξ' p - y * cd_z p = tp_dfld e w p - y * tp_Dz p := by
      simp only [hξ'def, hcs, tp_dfld, tp_Dz, tp_Dif, tp_base, hξdef]
      ring
    rw [e1]
    have : (1 : ℝ) ≤ y / 20000 := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  obtain ⟨hargs, hFs, hmins⟩ := cd_point_ball hy0.le ξ' hball'
  have hstar : ∀ i j : Fin 3, e j ∈ profile (tl_thetaStar a b c hab hac hbc) (e i) ↔
      cd_at cd_Cstar i j = true := by
    intro i j
    have := cd_star_profile a b c hab hac hbc i j
    rwa [tp_ord3_eq S hS hab hac hbc, tp_ord3_eq S hS hab hac hbc] at this
  have hFstar : tl_F w (tl_thetaStar a b c hab hac hbc) tl_t0 (sigN N) = cd_F 3 cd_Cstar 0 ξ' :=
    tp_F_bridge he hU w _ cd_Cstar hstar ξ' cs hξ'
  have hcc5 : cd_cc 3 cd_Cstar = 5 := by decide
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have haT : tl_aTrip = 25 / 48 := by unfold tl_aTrip; norm_num
  have hreg : ∀ θ : SysPartition N {a, b, c},
      (∃ j ∈ ({a, b, c} : Finset (Fin N)), profile θ j ≠
        profile (tl_thetaStar a b c hab hac hbc) j) →
      (1 + 1 / 100) * tl_F w (tl_thetaStar a b c hab hac hbc) tl_t0 (sigN N) / 5 ≤
        tl_F w θ tl_t0 (sigN N) / (sysCutCount θ : ℝ) := by
    intro θ hθ
    obtain ⟨g, δ, hv, hp⟩ := cd_classify (cd_ord3 a b c hab hac hbc) (fun x =>
      (cd_ord3_onto a b c hab hac hbc x)) θ
    have hp' : ∀ i j : Fin 3, e j ∈ profile θ (e i) ↔ cd_at (cd_profOf 3 g δ) i j = true := by
      intro i j
      have := hp i j
      rwa [tp_ord3_eq S hS hab hac hbc, tp_ord3_eq S hS hab hac hbc] at this
    by_cases hC : cd_profOf 3 g δ = cd_Cstar
    · exfalso
      obtain ⟨x, hx, hne⟩ := hθ
      apply hne
      rw [← hU] at hx
      obtain ⟨i, rfl⟩ := bg_mem_U e hx
      ext v
      constructor
      · intro hv'
        have hvS : v ∈ bg_U e := hU ▸ prof_profile_subset θ (e i) hv'
        obtain ⟨j, rfl⟩ := bg_mem_U e hvS
        exact (hstar i j).2 (hC ▸ (hp' i j).1 hv')
      · intro hv'
        have hvS : v ∈ bg_U e := hU ▸ prof_profile_subset _ (e i) hv'
        obtain ⟨j, rfl⟩ := bg_mem_U e hvS
        exact (hp' i j).2 (hC ▸ (hstar i j).1 hv')
    · have hm := hmins g δ hv hC
      have hFθ := tp_F_bridge he hU w θ (cd_profOf 3 g δ) hp' ξ' cs hξ'
      have hcc := tp_cc_bridge he hU θ (cd_profOf 3 g δ) hp'
      rw [hFstar, hFθ, hcc]
      rw [hcc5] at hm
      push_cast at hm
      linarith
  have hmarg : ∀ ta tb tc : Bool, (ta || tb || tc) = true →
      ∑ i ∈ ({a, b, c} : Finset (Fin N)), Num w {a, b, c} {a, b, c}
          (tl_pat3 a b c ta tb tc) i + y * sigN N ≤
        ∑ i ∈ ({a, b, c} : Finset (Fin N)), Num w {a, b, c} {a, b, c} tl_t0 i := by
    intro ta tb tc htrue
    set t := tp_patOf e (tl_pat3 a b c ta tb tc) with htdef
    have hpat : bg_pst e t = tl_pat3 a b c ta tb tc := by
      refine tp_pst_patOf he _ fun j hj => ?_
      rw [hU] at hj
      simp only [mem_insert, mem_singleton, not_or] at hj
      simp [tl_pat3, hj.1, hj.2.1, hj.2.2]
    have ht0 : (t : ℕ) ≠ 0 := by
      intro h0
      have : t = ⟨0, by norm_num⟩ := Fin.ext h0
      rw [this, tp_pst_zero] at hpat
      have ha' := congrFun hpat a
      have hb' := congrFun hpat b
      have hc' := congrFun hpat c
      simp [tl_pat3, tl_t0, hab.symm, hac.symm, hbc.symm] at ha' hb' hc'
      subst ha' hb' hc'
      simp at htrue
    have hrow := hargs t (Nat.pos_of_ne_zero ht0) t.2
    have hm := tp_marg_bridge he hU w ξ' cs hξ' t
    rw [hpat] at hm
    nlinarith
  have hsmall : 36 * η ^ 2 < 1 / 100 * y * sigN N * (tl_aTrip - η) := by
    have h1 : 36 * η ^ 2 ≤ 810000 * (N : ℝ) ^ 2 * sigN N * sigN N := by
      have : η ^ 2 ≤ (150 * N * sigN N) ^ 2 := pow_le_pow_left₀ hη0 hηle 2
      nlinarith
    have h2 : 810000 * (N : ℝ) ^ 2 * sigN N ≤ 1 / 1000 := hsm2
    rw [haT]
    have h3 : 1 / 1000 * sigN N < 1 / 100 * y * sigN N * (25 / 48 - η) := by
      have h6 : (1 : ℝ) ≤ y := by linarith
      have h7 : (1 : ℝ) / 2 ≤ 25 / 48 - η := by linarith
      have h5 : 1 / 2 ≤ y * (25 / 48 - η) := by nlinarith
      have h8 := mul_le_mul_of_nonneg_left h5 hσ.le
      have e8 : 1 / 100 * y * sigN N * (25 / 48 - η) = sigN N * (y * (25 / 48 - η)) / 100 := by ring
      rw [e8]
      nlinarith
    nlinarith
  have hmsmall : 24 * tl_aTrip * η ^ 2 < (tl_aTrip - η) ^ 2 * (y * sigN N) := by
    have h1 : η ^ 2 ≤ 22500 * (N : ℝ) ^ 2 * sigN N * sigN N := by
      have : η ^ 2 ≤ (150 * N * sigN N) ^ 2 := pow_le_pow_left₀ hη0 hηle 2
      nlinarith
    have h2 : 810000 * (N : ℝ) ^ 2 * sigN N ≤ 1 / 1000 := hsm2
    rw [haT]
    have : (1 : ℝ) ≤ y := by linarith
    have h4 : (1 : ℝ) / 4 ≤ (25 / 48 - η) ^ 2 := by nlinarith
    nlinarith
  have hE0 : 6 * η / ((tl_aTrip - η) * Real.log 2) ≤ 2 / 5 := by
    rw [haT]
    have hpos : 0 < (25 / 48 - η) * Real.log 2 := by
      have : 0 < 25 / 48 - η := by linarith
      positivity
    rw [div_le_iff₀ hpos]
    have := Real.log_two_gt_d9
    nlinarith
  have hbox' : tp_effBoxZ z s {a, b, c} := hSabc ▸ hbox
  have hphi := tl_triple_lower hz s hab hac hbc (η := η) (δ := 1 / 100) (y := y) (σ := sigN N)
    (E0 := 2 / 5) hη0 (by rw [haT]; linarith) (by norm_num) hy0 hσ
    (fun Y hY t i hi => tp_levels hG hZ hN hcard hY t hi) hreg
    (by rw [hFstar]; exact hFs) hmarg hsmall hmsmall hE0 (tp_eff hz s hcard hbox')
  rw [hSabc]
  exact hphi

end

end Census
end IIT
