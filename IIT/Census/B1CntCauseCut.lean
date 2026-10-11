/-
Census, B1, W14 work package WP2 (cause side), part 2: the small-cut sums at `r0`.

`csG w r0 K' i = min(X_i(K'), ln(y_i/c_X))`, `X_i(K') = ln(y_{r0,i}/Ā_i(C_{K'}(r0)))` (W5 §2, W7 4.3).
* `K' = {x}` on the cause side (`x1`, `famX3_cause_sub`, `lowFew`, the floor): `cs_sum_G_x`;
* `1 ≤ |K'| ≤ 4` otherwise (`posNear`): `cs_sum_G_posNear`;
* `5 ≤ |K'| ≤ J` (W5 Lemma P5 with `rowExc`, `FE2`, the Jensen bound): `cs_sum_G_P5`;
* assembled over `M = univ \ K`: `cs_smallCut`.
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §7 (`cp_ratio`, `phiCat_h3`).  No `sorry`.
-/
import IIT.Census.B1CntCauseGen

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-- The cause cut term `g_i(K') = min(X_i(K'), ln(y_i/c_X))` at the row `r0`. -/
noncomputable def csG (w : Param N) (r0 : State N) (K' : Finset (Fin N)) (i : Fin N) : ℝ :=
  min (Real.log (clamp01 (w r0 i) / subMean w K'ᶜ r0 i)) (Real.log (clamp01 (w r0 i) / cX))

lemma cs_cX_pos : (0 : ℝ) < cX := by unfold cX; norm_num

lemma cs_b1Cap_pos : (0 : ℝ) < b1Cap := by unfold b1Cap; norm_num

lemma cs_log_two_lt : Real.log 2 < 6932 / 10000 := by
  have := Real.log_two_lt_d9; linarith

lemma cs_log_two_gt : 6931 / 10000 < Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

lemma csG_le_log2 (w : Param N) (r0 : State N) (K' : Finset (Fin N)) (i : Fin N) :
    csG w r0 K' i ≤ Real.log 2 := by
  refine (min_le_right _ _).trans ?_
  rcases eq_or_lt_of_le (clamp01_nonneg (w r0 i)) with h0 | hpos
  · rw [← h0, zero_div, Real.log_zero]; exact (Real.log_pos (by norm_num)).le
  · refine Real.log_le_log (div_pos hpos cs_cX_pos) ?_
    rw [div_le_iff₀ cs_cX_pos]; unfold cX; linarith [clamp01_le_one (w r0 i)]

/-- Removing the `d` units of `K` from a sum of terms `≤ B`. -/
lemma cs_sum_sdiff_ge (K : Finset (Fin N)) (f : Fin N → ℝ) {B : ℝ} (hf : ∀ i ∈ K, f i ≤ B) :
    ∑ i, f i - K.card * B ≤ ∑ i ∈ univ \ K, f i := by
  have h := sum_sdiff (f := f) (subset_univ K)
  have hK : ∑ i ∈ K, f i ≤ K.card * B := by
    calc ∑ i ∈ K, f i ≤ ∑ _i ∈ K, B := sum_le_sum hf
      _ = K.card * B := by rw [sum_const, nsmul_eq_mul]
  linarith

lemma cs_card_agree_compl (K' : Finset (Fin N)) (t : State N) :
    ((agree K'ᶜ t).card : ℝ) = 2 ^ K'.card := by
  rw [card_agree, card_compl, Fintype.card_fin]
  have h1 : K'.card ≤ N := by simpa using card_le_univ K'
  have : N - (N - K'.card) = K'.card := by omega
  rw [this]; push_cast; rfl

lemma cs_subMean_le_meanPlus (w : Param N) (t : State N) (K' : Finset (Fin N)) (i : Fin N) :
    subMean w K'ᶜ t i ≤ b1CutMeanPlus w t K' i := by
  unfold subMean b1CutMeanPlus
  rw [cs_card_agree_compl, ← add_sum_erase _ _ (self_mem_agree K'ᶜ t)]
  exact div_le_div_of_nonneg_right (by linarith [clamp01_le_one (w t i)]) (by positivity)

lemma cs_b1CutGX_le_csG {w : Param N} (hw : w ∈ openCube N) (r0 : State N) (K' : Finset (Fin N))
    (i : Fin N) : b1CutGX w r0 K' i ≤ csG w r0 K' i := by
  unfold b1CutGX csG
  have hy := cs_clamp_pos hw r0 i
  have hA := cs_subMean_pos hw K'ᶜ r0 i
  have hmp := cs_subMean_le_meanPlus w r0 K' i
  apply min_le_min
  · exact Real.log_le_log (div_pos hy (lt_of_lt_of_le hA hmp))
      (div_le_div_of_nonneg_left hy.le hA hmp)
  · exact Real.log_le_log (div_pos hy cs_b1Cap_pos)
      (div_le_div_of_nonneg_left hy.le cs_cX_pos (by unfold cX b1Cap; norm_num))

/-! ### `1 ≤ |K'| ≤ 4`: `posNear` -/

theorem cs_sum_G_posNear {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    (hg : GoodW3 N s r0 x σ w) (hw : w ∈ openCube N) (K : Finset (Fin N))
    {K' : Finset (Fin N)} (hne : K'.Nonempty) (h4 : K'.card ≤ 4) (hx : σ = .cause → K' ≠ {x}) :
    (N : ℝ) / 25 - K.card * Real.log 2 ≤ ∑ i ∈ univ \ K, csG w r0 K' i := by
  have hp := hg.1.posNear K' hne h4 hx
  have h1 : (N : ℝ) / 25 ≤ ∑ i, csG w r0 K' i :=
    hp.trans (sum_le_sum fun i _ => cs_b1CutGX_le_csG hw r0 K' i)
  have h2 := cs_sum_sdiff_ge K (csG w r0 K') (fun i _ => csG_le_log2 w r0 K' i)
  linarith

/-! ### `K' = {x}` on the cause side -/

lemma cs_csG_single_eq (w : Param N) (s r0 : State N) (x j : Fin N) :
    csG w r0 {x} j = min (lamX w s r0 x .cause j) (Real.log (clamp01 (w r0 j) / cX)) := by
  unfold csG
  rw [cs_subMean_pair]
  show min (Real.log (clamp01 (w r0 j) / ((clamp01 (w r0 j) + clamp01 (w (flipAt x r0) j)) / 2)))
      _ = min (Real.log (2 * clamp01 (w r0 j) / (clamp01 (w r0 j) + clamp01 (w (flipAt x r0) j)))) _
  rw [div_div_eq_mul_div, mul_comm (clamp01 (w r0 j)) 2]

theorem cs_sum_G_x {s r0 : State N} {x : Fin N} {w : Param N} (hg : GoodW3 N s r0 x .cause w)
    (hw : w ∈ openCube N) {K : Finset (Fin N)} (hK : K ∈ famX3 N s r0 x .cause w)
    (ha : Real.exp (-((N : ℝ) / 200)) ≤ 1 / 1000) :
    -((N : ℝ) / 2000) + ((dX N : ℝ) - (lowU N w r0).card) / 26 + Real.log (2 / 3) ≤
      ∑ i ∈ univ \ K, csG w r0 {x} i := by
  set f : Fin N → ℝ := fun i => csG w r0 {x} i with hf
  have hx1 : -((N : ℝ) / 2000) ≤ ∑ j ∈ univ.erase x, f j := by
    have := hg.1.x1 rfl
    simpa only [hf, cs_csG_single_eq w s r0 x] using this
  have hsub := famX3_cause_sub hK
  have hlowK := lowU_sub_of_mem_famX3 hK
  have hKcard := famX3_card hK
  -- `x ∈ K` forces `x` low
  have hxlow : x ∈ K → x ∈ lowU N w r0 := by
    intro hxK
    rcases mem_union.1 (hsub hxK) with h | h
    · exact absurd h (by simp [NegX])
    · exact h
  -- decomposition
  have hdec : ∑ i ∈ univ \ K, f i =
      ∑ j ∈ univ.erase x, f j - ∑ j ∈ K.erase x, f j + (if x ∈ K then 0 else f x) := by
    have h1 := sum_sdiff (f := f) (subset_univ K)
    have h2 := add_sum_erase univ f (mem_univ x)
    by_cases hxK : x ∈ K
    · have h3 := add_sum_erase K f hxK
      rw [if_pos hxK]; linarith
    · rw [if_neg hxK, erase_eq_of_notMem hxK]; linarith
  -- the `K`-terms
  set h : Fin N → ℝ := fun j => if j ∈ lowU N w r0 then 0 else 1 / 26 with hh
  have hfK : ∀ j ∈ K, f j ≤ -h j := by
    intro j hj
    have hy := cs_clamp_pos hw r0 j
    by_cases hl : j ∈ lowU N w r0
    · simp only [hh, if_pos hl, neg_zero, hf]
      refine (min_le_right _ _).trans (Real.log_nonpos (div_pos hy cs_cX_pos).le ?_)
      rw [div_le_one cs_cX_pos]
      simp only [lowU, mem_filter, mem_univ, true_and] at hl
      unfold cX; linarith
    · simp only [hh, if_neg hl, hf, cs_csG_single_eq w s r0 x]
      have hn : j ∈ NegX w r0 x := by
        rcases mem_union.1 (hsub hj) with h' | h'
        · exact h'
        · exact absurd h' hl
      simp only [NegX, mem_filter] at hn
      have hU := cs_clamp_pos hw (flipAt x r0) j
      refine (min_le_left _ _).trans ?_
      show Real.log (2 * clamp01 (w r0 j) / (clamp01 (w r0 j) + clamp01 (w (flipAt x r0) j))) ≤ _
      have hle : 2 * clamp01 (w r0 j) / (clamp01 (w r0 j) + clamp01 (w (flipAt x r0) j)) ≤
          25 / 26 := by
        rw [div_le_iff₀ (by linarith)]; linarith [hn.2]
      calc _ ≤ Real.log (25 / 26) := Real.log_le_log (by positivity) hle
        _ ≤ 25 / 26 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
        _ = -(1 / 26) := by norm_num
  have hKsum : ∑ j ∈ K.erase x, f j ≤ -(∑ j ∈ K, h j) := by
    have e : ∑ j ∈ K.erase x, h j = ∑ j ∈ K, h j := by
      by_cases hxK : x ∈ K
      · exact sum_erase K (by simp [hh, hxlow hxK])
      · rw [erase_eq_of_notMem hxK]
    rw [← e, ← sum_neg_distrib]
    exact sum_le_sum fun j hj => hfK j (mem_of_mem_erase hj)
  have hhsum : ∑ j ∈ K, h j = ((dX N : ℝ) - (lowU N w r0).card) / 26 := by
    rw [hh, sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul, ← sdiff_eq_filter,
      card_sdiff_of_subset hlowK, Nat.cast_sub (card_le_card hlowK), hKcard]
    ring
  -- the unit `x`
  have hxterm : Real.log (2 / 3) ≤ (if x ∈ K then 0 else f x) := by
    split_ifs with hxK
    · exact Real.log_nonpos (by norm_num) (by norm_num)
    · have hfl := mem_famX3_floor hK hxK
      have hy := cs_clamp_pos hw r0 x
      have hU := cs_clamp_pos hw (flipAt x r0) x
      have hU1 := clamp01_le_one (w (flipAt x r0) x)
      have hexp : 0 < Real.exp (-((N : ℝ) / 200)) := Real.exp_pos _
      simp only [hf, cs_csG_single_eq w s r0 x]
      refine le_min ?_ ?_
      · show Real.log (2 / 3) ≤
          Real.log (2 * clamp01 (w r0 x) / (clamp01 (w r0 x) + clamp01 (w (flipAt x r0) x)))
        refine Real.log_le_log (by norm_num) ?_
        rw [le_div_iff₀ (by linarith)]; linarith
      · refine Real.log_le_log (by norm_num) ?_
        rw [le_div_iff₀ cs_cX_pos]; unfold cX; linarith
  rw [hdec]
  linarith

/-! ### `5 ≤ |K'|`: W5 Lemma P5 -/

/-- Row excess `Σ_i (y_{r,i} - b1Cap)^+`. -/
noncomputable def csExc (w : Param N) (r : State N) : ℝ := ∑ i, pos (clamp01 (w r i) - b1Cap)

lemma csExc_le (w : Param N) (r : State N) : csExc w r ≤ N * (62 / 125) := by
  unfold csExc
  calc ∑ i, pos (clamp01 (w r i) - b1Cap) ≤ ∑ _i : Fin N, (62 / 125 : ℝ) := by
        refine sum_le_sum fun i _ => pos_le (by norm_num) ?_
        unfold b1Cap; linarith [clamp01_le_one (w r i)]
    _ = N * (62 / 125) := by simp

/-- At most `q` special rows (excess `≤ 62N/125`), all others `≤ N/5`. -/
lemma cs_sum_exc_le (w : Param N) (C Sp : Finset (State N)) {q : ℕ} (hq : Sp.card ≤ q)
    (h : ∀ r ∈ C, r ∉ Sp → csExc w r ≤ N / 5) :
    ∑ r ∈ C, csExc w r ≤ N / 5 * C.card + q * (N * (37 / 125)) := by
  rw [← sum_filter_add_sum_filter_not C (fun r => r ∈ Sp)]
  have h1 : ∑ r ∈ C with r ∈ Sp, csExc w r ≤ (C.filter (· ∈ Sp)).card * (N * (62 / 125)) := by
    calc _ ≤ ∑ r ∈ C with r ∈ Sp, N * (62 / 125 : ℝ) := sum_le_sum fun r _ => csExc_le w r
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have h2 : ∑ r ∈ C with r ∉ Sp, csExc w r ≤ (C.filter (· ∉ Sp)).card * ((N : ℝ) / 5) := by
    calc _ ≤ ∑ r ∈ C with r ∉ Sp, ((N : ℝ) / 5) :=
          sum_le_sum fun r hr => h r (mem_filter.1 hr).1 (mem_filter.1 hr).2
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hc := card_filter_add_card_filter_not (s := C) (fun r => r ∈ Sp)
  have hcq : (C.filter (· ∈ Sp)).card ≤ q :=
    (card_le_card fun r hr => (mem_filter.1 hr).2).trans hq
  have hcR : ((C.filter (· ∈ Sp)).card : ℝ) + (C.filter (· ∉ Sp)).card = C.card := by
    exact_mod_cast hc
  have hcqR : ((C.filter (· ∈ Sp)).card : ℝ) ≤ q := by exact_mod_cast hcq
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

lemma cs_csG_ge_logmax {w : Param N} (hw : w ∈ openCube N) (r0 : State N) (K' : Finset (Fin N))
    (i : Fin N) :
    Real.log (clamp01 (w r0 i)) - Real.log (max (subMean w K'ᶜ r0 i) b1Cap) ≤ csG w r0 K' i := by
  unfold csG
  have hy := cs_clamp_pos hw r0 i
  have hA := cs_subMean_pos hw K'ᶜ r0 i
  have hm : 0 < max (subMean w K'ᶜ r0 i) b1Cap := lt_of_lt_of_le hA (le_max_left _ _)
  refine le_min ?_ ?_
  · rw [Real.log_div hy.ne' hA.ne']
    linarith [Real.log_le_log hA (le_max_left (subMean w K'ᶜ r0 i) b1Cap)]
  · rw [Real.log_div hy.ne' cs_cX_pos.ne']
    have : Real.log cX ≤ Real.log (max (subMean w K'ᶜ r0 i) b1Cap) :=
      Real.log_le_log cs_cX_pos ((by unfold cX b1Cap; norm_num : cX ≤ b1Cap).trans (le_max_right _ _))
    linarith

/-- Rows of the subcube `C_{K'}(r0)` other than `r0`, `r0^x` have excess `≤ N/5`. -/
lemma cs_exc_r0cube {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    (hg : GoodW3 N s r0 x σ w) (hfr : CountFreshX N s r0 w) {K' : Finset (Fin N)}
    (hJ : K'.card ≤ JC N) (hfar : 3 * K'.card + 3 < N) :
    ∀ r ∈ agree K'ᶜ r0, r ∉ ({r0, flipAt x r0} : Finset (State N)) → csExc w r ≤ N / 5 := by
  intro r hr hsp
  have hd : ham r r0 ≤ K'.card := ham_le_card_of_mem_agree hr
  have hfar0 := hg.1.far
  simp only [mem_insert, mem_singleton, not_or] at hsp
  by_cases hS : r ∈ sensRows s r0
  · refine hg.1.rowExc r hS hsp.1 ?_ ?_
    · rintro rfl
      have := ham_comm r0 r; omega
    · cases σ with
      | cause => exact hsp.2
      | effect =>
        intro e
        have h1 : ham (flipAt x s) s ≤ 1 := ham_flipAt_le_one x s
        have h2 := ham_triangle r0 (flipAt x s) s
        have h3 := ham_comm r0 r
        simp only [spRow] at e
        rw [e] at hd h3
        omega
  · exact hfr.fe2 r hS ⟨r0, mem_sensRows_r0 s r0, hd.trans hJ⟩

theorem cs_sum_G_P5 {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    (hg : GoodW3 N s r0 x σ w) (hfr : CountFreshX N s r0 w) (hw : w ∈ openCube N)
    {K' : Finset (Fin N)} (h5 : 5 ≤ K'.card) (hJ : K'.card ≤ JC N) (hfar : 3 * K'.card + 3 < N) :
    -XW w r0 + N * (555 / 2000) ≤ ∑ i, csG w r0 K' i := by
  set C := agree K'ᶜ r0 with hC
  have hCc : (C.card : ℝ) = 2 ^ K'.card := cs_card_agree_compl K' r0
  have h32 : (32 : ℝ) ≤ C.card := by
    rw [hCc]
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ K'.card := pow_le_pow_right₀ (by norm_num) h5
  have hex := cs_sum_exc_le w C {r0, flipAt x r0} (q := 2) (card_le_two)
    (cs_exc_r0cube hg hfr hJ hfar)
  have hρ : ∑ r ∈ C, ∑ i, pos (clamp01 (w r i) - b1Cap) ≤ (437 / 2000) * N * C.card := by
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    change ∑ r ∈ C, csExc w r ≤ _
    refine hex.trans ?_
    push_cast
    nlinarith
  have hjen := cs_sum_log_max_le w K'ᶜ r0 cs_b1Cap_pos hρ
  have hlog : Real.log (b1Cap + 437 / 2000) ≤ -(555 / 2000) := by
    have := Real.log_le_sub_one_of_pos (by unfold b1Cap; norm_num : (0 : ℝ) < b1Cap + 437 / 2000)
    unfold b1Cap at this ⊢; linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hXW : ∑ i, Real.log (clamp01 (w r0 i)) = -XW w r0 := by
    unfold XW; rw [← sum_neg_distrib]; simp
  calc -XW w r0 + N * (555 / 2000)
      ≤ ∑ i, Real.log (clamp01 (w r0 i)) - ∑ i, Real.log (max (subMean w K'ᶜ r0 i) b1Cap) := by
        rw [hXW]; nlinarith
    _ = ∑ i, (Real.log (clamp01 (w r0 i)) - Real.log (max (subMean w K'ᶜ r0 i) b1Cap)) := by
        rw [sum_sub_distrib]
    _ ≤ ∑ i, csG w r0 K' i := sum_le_sum fun i _ => cs_csG_ge_logmax hw r0 K' i

/-! ### Assembly over `M = univ \ K` -/

/-- The small-cut sums over `M = univ \ K` (cases of W5 Lemma CP / W7 4.3 / W13 F2). -/
theorem cs_smallCut {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    (hg : GoodW3 N s r0 x σ w) (hfr : CountFreshX N s r0 w) (hw : w ∈ openCube N)
    {K : Finset (Fin N)} (hK : K ∈ famX3 N s r0 x σ w)
    (hN : 10000 ≤ N) (hslT : slT N ≤ N / 1000) (ha : Real.exp (-((N : ℝ) / 200)) ≤ 1 / 1000)
    {K' : Finset (Fin N)} (hne : K'.Nonempty) (hJ : K'.card ≤ JC N) (hfar : 3 * K'.card + 3 < N) :
    (N : ℝ) / 2000 ≤ ∑ i ∈ univ \ K, csG w r0 K' i ∧
      (¬ (σ = .cause ∧ K' = {x}) → (N : ℝ) / 100 ≤ ∑ i ∈ univ \ K, csG w r0 K' i) := by
  have hNr : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have hKc : (K.card : ℝ) = dX N := by rw [famX3_card hK]
  have hd1 := cs_dX_le N
  have hd2 := cs_dX_ge N
  have hl2 := cs_log_two_lt
  have hl2' := cs_log_two_gt
  have hmain : ¬ (σ = .cause ∧ K' = {x}) → (N : ℝ) / 100 ≤ ∑ i ∈ univ \ K, csG w r0 K' i := by
    intro hnot
    by_cases h4 : K'.card ≤ 4
    · have hx : σ = .cause → K' ≠ {x} := fun hσ e => hnot ⟨hσ, e⟩
      have h := cs_sum_G_posNear hg hw K hne h4 hx
      rw [hKc] at h
      nlinarith
    · have h5 : 5 ≤ K'.card := by omega
      have h := cs_sum_G_P5 hg hfr hw h5 hJ hfar
      have h2 := cs_sum_sdiff_ge K (csG w r0 K') (fun i _ => csG_le_log2 w r0 K' i)
      have htilt := cnt_tilt hg
      have hx0 := x0_lt
      rw [hKc] at h2
      have : x0 * N ≤ 2029 / 10000 * N := mul_le_mul_of_nonneg_right hx0.le (by positivity)
      nlinarith
  refine ⟨?_, hmain⟩
  by_cases hc : σ = .cause ∧ K' = {x}
  · obtain ⟨hσ, rfl⟩ := hc
    subst hσ
    have h := cs_sum_G_x hg hw hK ha
    have hlow : (1000 : ℝ) * (lowU N w r0).card ≤ N := by exact_mod_cast hg.2.lowFew
    have hl23 : -(1 / 2 : ℝ) ≤ Real.log (2 / 3) := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
      rw [show (2 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, Real.log_inv]; linarith
    linarith
  · have := hmain hc; linarith

end Census
end IIT
