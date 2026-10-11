/-
Census, B1 lower bound, leaf `phi_univ_ge_EX`: the margin certificate (`B1UnivCert`) on the real side.

`cause_cells_sum` : on `EX`, `Σ_j (ln(y_j/y_m) - numRC v y_j U_j / f) ≥ N·marg_v - 3 KP²`;
`effect_cells_sum`: on `EX`, `Σ_k (ln(x_k/x_m) - numRE v x_k / fe) ≥ N·marg_v - 3 KS²`.
-/
import IIT.Census.B1UnivCert
import IIT.Census.B1UnivLoss

set_option maxRecDepth 100000

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-! ### Real loss numerators -/

noncomputable def numRC : ℕ → ℝ → ℝ → ℝ
  | 0, y, _ => (y + 1 - 2 * (1001 / 2000)) ^ 2 / 4
  | 1, y, u => max ((y + u - 1) / 4 + 1 / 2 - 1001 / 2000) 0 + 1021 / 10000 / 2
  | 2, y, _ => max ((y - 1 / 2) / 4 + 1 / 2 - 1001 / 2000) 0 + 1 / 16
  | _, y, u => max (max (max (y + u - 1) (y - 1 / 2)) 0 / 8 + 1 / 2 - 1001 / 2000) 0 + 1021 / 10000 / 2

noncomputable def numRE : ℕ → ℝ → ℝ
  | 0, x => (x + 1 - 2 * (1 / 2 + 1 / 100000)) ^ 2 / 4
  | 1, x => max ((x - 1 / 2) / 4 + 1 / 2 - (1 / 2 + 1 / 100000)) 0 + 1 / 16
  | _, x => max ((x - 1 / 2) / 8 + 1 / 2 - (1 / 2 + 1 / 100000)) 0 + 1021 / 10000 / 2

lemma qmax_cast (a b : ℚ) : ((qmax a b : ℚ) : ℝ) = max (a : ℝ) b := by
  unfold qmax
  split_ifs with h
  · rw [max_eq_right (by exact_mod_cast h)]
  · rw [max_eq_left (by exact_mod_cast (le_of_lt (not_le.1 h)))]

lemma numRC_cast (v : ℕ) (y u : ℚ) : numRC v y u = ((ucNum v y u : ℚ) : ℝ) := by
  rcases v with _ | _ | _ | v <;> simp only [numRC, ucNum, ucF, ucSig] <;> push_cast [qmax_cast] <;> ring_nf

lemma numRE_cast (v : ℕ) (x : ℚ) : numRE v x = ((ueNum v x : ℚ) : ℝ) := by
  rcases v with _ | _ | v <;> simp only [numRE, ueNum, ueFe, ucSig] <;> push_cast [qmax_cast] <;> ring_nf

lemma numRC_mono (v : ℕ) {y y' u u' : ℝ} (hy0 : 1 / 2 ≤ y) (hy : y ≤ y') (hu : u ≤ u') :
    numRC v y u ≤ numRC v y' u' := by
  rcases v with _ | _ | _ | v
  · simp only [numRC]
    have : 0 ≤ y + 1 - 2 * (1001 / 2000 : ℝ) := by linarith
    have : y + 1 - 2 * (1001 / 2000 : ℝ) ≤ y' + 1 - 2 * (1001 / 2000) := by linarith
    have := pow_le_pow_left₀ (by assumption) this 2
    linarith
  · simp only [numRC]; gcongr <;> linarith
  · simp only [numRC]; gcongr <;> linarith
  · simp only [numRC]; gcongr <;> linarith

lemma numRE_mono (v : ℕ) {x x' : ℝ} (hx0 : 1 / 2 ≤ x) (hx : x ≤ x') : numRE v x ≤ numRE v x' := by
  rcases v with _ | _ | v
  · simp only [numRE]
    have h1 : 0 ≤ x + 1 - 2 * (1 / 2 + 1 / 100000 : ℝ) := by linarith
    have h2 : x + 1 - 2 * (1 / 2 + 1 / 100000 : ℝ) ≤ x' + 1 - 2 * (1 / 2 + 1 / 100000) := by linarith
    have := pow_le_pow_left₀ h1 h2 2
    linarith
  · simp only [numRE]; gcongr
  · simp only [numRE]; gcongr

/-! ### The strip and cell logs -/

lemma ucStrip_real {sa : ℕ} (hsa : sa < 40) :
    ((ucStripL.getD sa 0 : ℚ) : ℝ) ≤ Real.log (((ucY sa / ucYm : ℚ) : ℝ)) := by
  have h := List.all_eq_true.1 ucStrip_ok sa (List.mem_range.2 hsa)
  exact crLog_ge (ucStripK.getD sa 0) 25 h

set_option maxHeartbeats 0 in
lemma ucB_abs_le (v : ℕ) : exPCells.all (fun C => decide (|ucB v C| ≤ 3)) = true := by
  rcases v with _ | _ | _ | v
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · have e : ∀ C, ucB (v + 3) C = ucB 3 C := fun C => by simp [ucB, ucNum]
    simp only [e]
    decide +kernel

/-! ### Sums over cells -/

/-- A sum over units dominates the cell-wise lower bounds, given the pair type. -/
lemma sum_ge_pair_cells {s r0 : State N} {x : Fin N} {w : Param N} (hw : w ∈ EX N s r0 x)
    (h : Fin N → ℝ) (B : Fin KP → ℝ)
    (hB : ∀ i j, (w r0 j, w (flipAt x r0) j) ∈ exIP (cP i) → B i ≤ h j) :
    ∑ i, (nP N i : ℝ) * B i ≤ ∑ j, h j := by
  classical
  set F : Fin KP → Finset (Fin N) := fun i => univ.filter fun j => (w r0 j, w (flipAt x r0) j) ∈ exIP (cP i)
  have hdisj : ((univ : Finset (Fin KP)) : Set (Fin KP)).PairwiseDisjoint F := by
    intro i _ i' _ hii'
    refine Finset.disjoint_filter.2 fun j _ h1 h2 => ?_
    exact Set.disjoint_left.1 (exIP_disjoint hii') h1 h2
  have hcov : univ.biUnion F = univ := by
    ext j; simp only [mem_biUnion, mem_univ, true_and, iff_true]
    obtain ⟨i, hi⟩ := EX_pair_cover hw j
    exact ⟨i, mem_filter.2 ⟨mem_univ j, hi⟩⟩
  rw [← hcov, sum_biUnion hdisj]
  refine sum_le_sum fun i _ => ?_
  have hc : (F i).card = nP N i := hw.1 i
  calc (nP N i : ℝ) * B i = ∑ _j ∈ F i, B i := by rw [sum_const, hc, nsmul_eq_mul]
    _ ≤ ∑ j ∈ F i, h j := sum_le_sum fun j hj => hB i j (mem_filter.1 hj).2

lemma nP_wsum_ge (N : ℕ) (B : Fin KP → ℝ) :
    N * ∑ i, ((cP i).a : ℝ) * B i - KP * ∑ i, |B i| ≤ ∑ i, (nP N i : ℝ) * B i := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := nP_err N i
  have : -(KP * |B i|) ≤ ((nP N i : ℝ) - (cP i).a * N) * B i := by
    have := neg_abs_le (((nP N i : ℝ) - (cP i).a * N) * B i)
    rw [abs_mul] at this
    nlinarith [mul_le_mul_of_nonneg_right h (abs_nonneg (B i))]
  nlinarith

lemma ucSum_cast (v : ℕ) : ((ucSum v : ℚ) : ℝ) = ∑ i : Fin KP, ((cP i).a : ℝ) * (ucB v (cP i) : ℝ) := by
  simp only [cP]
  rw [Fin.sum_univ_fun_getElem exPCells (fun C : EXPCell => (C.a : ℝ) * (ucB v C : ℝ))]
  unfold ucSum
  push_cast [List.map_map]; congr 1
  exact List.map_congr_left fun C _ => by simp

/-- **The cause-side margin on the real side.** -/
theorem cause_cells_sum {s r0 : State N} {x : Fin N} {w : Param N} (hw : w ∈ EX N s r0 x) (v : ℕ) :
    N * (ucMarg v : ℝ) - 3 * (KP : ℝ) ^ 2 ≤
      ∑ j, (Real.log (clamp01 (w r0 j) / ((ucYm : ℚ) : ℝ)) -
        numRC v (clamp01 (w r0 j)) (clamp01 (w (flipAt x r0) j)) / (1001 / 2000)) := by
  have hYm : (0 : ℝ) < ((ucYm : ℚ) : ℝ) := by unfold ucYm ucF; rw [exHy_val]; norm_num
  have hcell : ∀ i j, (w r0 j, w (flipAt x r0) j) ∈ exIP (cP i) →
      ((ucB v (cP i) : ℚ) : ℝ) ≤ Real.log (clamp01 (w r0 j) / ((ucYm : ℚ) : ℝ)) -
        numRC v (clamp01 (w r0 j)) (clamp01 (w (flipAt x r0) j)) / (1001 / 2000) := by
    intro i j hij
    have hm := cell_mem (cP_mem i) hij
    obtain ⟨hylo, hy1, hyh, hu0, hu1, -, -, hc1, hc2⟩ := hm
    have hsa : (cP i).sa < 40 := (exP_facts (cP_mem i)).2.1
    have hyhi : w r0 j < ((ucY ((cP i).sa + 1) : ℚ) : ℝ) := by
      have := hij.1.2
      have e : ((exYlo (cP i) + exHy : ℚ) : ℝ) = ((ucY ((cP i).sa + 1) : ℚ) : ℝ) := by
        unfold exYlo ucY ucF exF; push_cast; ring
      rw [← e]; exact this
    have hylo' : ((ucY (cP i).sa : ℚ) : ℝ) ≤ w r0 j := by
      have e : ((exYlo (cP i) : ℚ) : ℝ) = ((ucY (cP i).sa : ℚ) : ℝ) := by
        unfold exYlo ucY ucF exF; push_cast; ring
      rw [← e]; exact hylo
    rw [hc1, hc2]
    -- gain
    have hg : ((ucStripL.getD (cP i).sa 0 : ℚ) : ℝ) ≤ Real.log (w r0 j / ((ucYm : ℚ) : ℝ)) := by
      refine (ucStrip_real hsa).trans ?_
      have hq : (0 : ℝ) < ((ucY (cP i).sa / ucYm : ℚ) : ℝ) := by
        push_cast; apply div_pos _ hYm; unfold ucY ucF; push_cast; rw [exHy_val]; positivity
      apply Real.log_le_log hq
      push_cast
      exact div_le_div_of_nonneg_right hylo' hYm.le
    -- loss
    have hl : numRC v (w r0 j) (w (flipAt x r0) j) ≤ ((ucNum v (ucY ((cP i).sa + 1)) (cP i).u1 : ℚ) : ℝ) := by
      rw [← numRC_cast]
      exact numRC_mono v hyh hyhi.le hu1.le
    unfold ucB
    push_cast
    rw [show ((ucF : ℚ) : ℝ) = 1001 / 2000 by unfold ucF; norm_num]
    have := div_le_div_of_nonneg_right hl (by norm_num : (0 : ℝ) ≤ 1001 / 2000)
    linarith
  have h1 := sum_ge_pair_cells hw _ _ hcell
  have h2 := nP_wsum_ge N (fun i => ((ucB v (cP i) : ℚ) : ℝ))
  have h3 : ∑ i : Fin KP, |((ucB v (cP i) : ℚ) : ℝ)| ≤ 3 * KP := by
    have hall := List.all_eq_true.1 (ucB_abs_le v)
    calc ∑ i : Fin KP, |((ucB v (cP i) : ℚ) : ℝ)| ≤ ∑ _i : Fin KP, (3 : ℝ) := by
          refine sum_le_sum fun i _ => ?_
          have := of_decide_eq_true (hall (cP i) (cP_mem i))
          have : (|ucB v (cP i)| : ℚ) ≤ 3 := this
          exact_mod_cast (by exact_mod_cast this : ((|ucB v (cP i)| : ℚ) : ℝ) ≤ 3)
      _ = 3 * KP := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have h4 : (ucMarg v : ℝ) ≤ ∑ i : Fin KP, ((cP i).a : ℝ) * ((ucB v (cP i) : ℚ) : ℝ) := by
    rw [← ucSum_cast]
    have : ucMarg v ≤ ucSum v := by
      rcases v with _ | _ | _ | v
      · exact ucSum_ok0
      · exact ucSum_ok1
      · exact ucSum_ok2
      · have e1 : ucMarg (v + 3) = ucMarg 3 := rfl
        have e2 : ucSum (v + 3) = ucSum 3 := by simp [ucSum, ucB, ucNum]
        rw [e1, e2]; exact ucSum_ok3
    exact_mod_cast this
  have hKP : (0 : ℝ) ≤ KP := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have h5 := mul_le_mul_of_nonneg_left h4 hN0
  have h6 := mul_le_mul_of_nonneg_left h3 hKP
  nlinarith


/-! ### The effect side -/

set_option maxHeartbeats 0 in
theorem ueCellK_len : ueCellK.length = 400 := by decide +kernel

lemma KS_eq : KS = 400 := by simp only [KS, exSCells_len]

lemma list_sum_zip {α β : Type*} (n : ℕ) (l1 : List α) (l2 : List β) (h1 : l1.length = n)
    (h2 : l2.length = n) (g : α × β → ℚ) :
    ((l1.zip l2).map g).sum =
      ∑ i : Fin n, g (l1[i.1]'(by rw [h1]; exact i.2), l2[i.1]'(by rw [h2]; exact i.2)) := by
  induction n generalizing l1 l2 with
  | zero =>
    rw [List.length_eq_zero_iff] at h1 h2; subst h1; subst h2; simp
  | succ n ih =>
    cases l1 with
    | nil => simp at h1
    | cons a t =>
      cases l2 with
      | nil => simp at h2
      | cons b t2 =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
        rw [List.zip_cons_cons, List.map_cons, List.sum_cons, ih t t2 h1 h2, Fin.sum_univ_succ]
        rfl

lemma ueCell_real (i : Fin KS) :
    ((ueCellL.getD i 0 : ℚ) : ℝ) ≤ Real.log (((ueXlo (cS i) / ueXmBD : ℚ) : ℝ)) := by
  have hL : i.1 < ueCellL.length := by rw [ueCellL_len]; exact lt_of_lt_of_eq i.2 KS_eq
  have hK : i.1 < ueCellK.length := by rw [ueCellK_len]; exact lt_of_lt_of_eq i.2 KS_eq
  have hz : i.1 < (exSCells.zip (ueCellL.zip ueCellK)).length := by
    have h0 : exSCells.length = 400 := exSCells_len
    simp only [List.length_zip, ueCellL_len, ueCellK_len, h0]
    have := lt_of_lt_of_eq i.2 KS_eq; omega
  have hmem := List.getElem_mem hz
  have h := List.all_eq_true.1 ueCell_ok _ hmem
  simp only [List.getElem_zip] at h
  have e1 : ueCellL.getD i 0 = ueCellL[i.1] := List.getD_eq_getElem _ _ hL
  rw [e1]
  exact crLog_ge _ 25 h

/-- The `x` value of a unit in a row-`s` cell lies between the cell ends. -/
lemma xE_cell {s : State N} {w : Param N} {i : Fin KS} {k : Fin N}
    (hk : w s k ∈ exIS (cS i)) :
    ((ueXlo (cS i) : ℚ) : ℝ) ≤ xE w s k ∧ xE w s k ≤ ((ueXhi (cS i) : ℚ) : ℝ) := by
  have hg := (List.all_eq_true.1 exSCells_gap) (cS i) (cS_mem i)
  obtain ⟨-, h0, hlt, h1, -⟩ := exS_facts (cS_mem i)
  obtain ⟨hlo, hhi⟩ := hk
  have h0' : (0 : ℝ) ≤ (cS i).x0 := by exact_mod_cast h0
  have h1' : ((cS i).x1 : ℝ) ≤ 1 := by exact_mod_cast h1
  have hc : clamp01 (w s k) = w s k := by
    unfold clamp01; rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  unfold xE ueXlo ueXhi
  rw [hc]
  unfold exSGap at hg
  rcases Bool.or_eq_true _ _ ▸ hg with h | h
  · have h' : ((cS i).x1 : ℝ) ≤ 1 / 2 - 1 / 100000 := by
      have := (Rat.cast_le (K := ℝ)).2 (of_decide_eq_true h); push_cast at this; exact this
    have hn : ¬ (1 / 2 : ℚ) ≤ (cS i).x0 := by
      have := of_decide_eq_true h
      intro hx; linarith
    rw [if_neg hn, if_neg hn]
    push_cast
    rw [max_eq_right (by linarith)]
    constructor <;> linarith
  · have h' : (1 / 2 + 1 / 100000 : ℝ) ≤ (cS i).x0 := by
      have := (Rat.cast_le (K := ℝ)).2 (of_decide_eq_true h); push_cast at this; exact this
    have hp : (1 / 2 : ℚ) ≤ (cS i).x0 := by
      have := of_decide_eq_true h; linarith
    rw [if_pos hp, if_pos hp]
    rw [max_eq_left (by linarith)]
    exact ⟨hlo, hhi.le⟩

lemma sum_ge_s_cells {s r0 : State N} {x : Fin N} {w : Param N} (hw : w ∈ EX N s r0 x)
    (h : Fin N → ℝ) (B : Fin KS → ℝ) (hB : ∀ i k, w s k ∈ exIS (cS i) → B i ≤ h k) :
    ∑ i, (nS N i : ℝ) * B i ≤ ∑ k, h k := by
  classical
  set F : Fin KS → Finset (Fin N) := fun i => univ.filter fun k => w s k ∈ exIS (cS i)
  have hdisj : ((univ : Finset (Fin KS)) : Set (Fin KS)).PairwiseDisjoint F := by
    intro i _ i' _ hii'
    refine Finset.disjoint_filter.2 fun j _ h1 h2 => ?_
    exact Set.disjoint_left.1 (exIS_disjoint hii') h1 h2
  have hcov : univ.biUnion F = univ := by
    ext k; simp only [mem_biUnion, mem_univ, true_and, iff_true]
    obtain ⟨i, hi⟩ := EX_s_cover hw k
    exact ⟨i, mem_filter.2 ⟨mem_univ k, hi⟩⟩
  rw [← hcov, sum_biUnion hdisj]
  refine sum_le_sum fun i _ => ?_
  have hc : (F i).card = nS N i := hw.2 i
  calc (nS N i : ℝ) * B i = ∑ _j ∈ F i, B i := by rw [sum_const, hc, nsmul_eq_mul]
    _ ≤ ∑ j ∈ F i, h j := sum_le_sum fun j hj => hB i j (mem_filter.1 hj).2

lemma nS_wsum_ge (N : ℕ) (B : Fin KS → ℝ) :
    N * ∑ i, ((cS i).a : ℝ) * B i - KS * ∑ i, |B i| ≤ ∑ i, (nS N i : ℝ) * B i := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := nS_err N i
  have : -(KS * |B i|) ≤ ((nS N i : ℝ) - (cS i).a * N) * B i := by
    have := neg_abs_le (((nS N i : ℝ) - (cS i).a * N) * B i)
    rw [abs_mul] at this
    nlinarith [mul_le_mul_of_nonneg_right h (abs_nonneg (B i))]
  nlinarith

/-- The per-cell bound of the effect side. -/
def ueB (v : ℕ) (i : Fin KS) : ℚ := ueCellL.getD i 0 - ueNum v (ueXhi (cS i)) / ueFe

lemma ueSum_eq (v : ℕ) : ueSum v = ∑ i : Fin KS, (cS i).a * ueB v i := by
  unfold ueSum
  rw [list_sum_zip KS exSCells ueCellL rfl (by rw [ueCellL_len, KS_eq])]
  refine Fintype.sum_congr _ _ fun i => ?_
  simp only [ueB, cS]
  congr 2
  rw [List.getD_eq_getElem]

set_option maxHeartbeats 0 in
lemma ueB_abs_le_list (v : ℕ) : (List.range 400).all (fun i =>
    decide (|ueCellL.getD i 0 - ueNum v (ueXhi (exSCells.getD i ⟨0, 0, 0, 0, 0, 0⟩)) / ueFe| ≤ 3)) = true := by
  rcases v with _ | _ | v
  · decide +kernel
  · decide +kernel
  · have e : ∀ x, ueNum (v + 2) x = ueNum 2 x := fun x => by simp [ueNum]
    simp only [e]
    decide +kernel

lemma ueB_abs_le (v : ℕ) (i : Fin KS) : |ueB v i| ≤ 3 := by
  have hi : i.1 < 400 := lt_of_lt_of_eq i.2 KS_eq
  have h := List.all_eq_true.1 (ueB_abs_le_list v) i.1 (List.mem_range.2 hi)
  have e : exSCells.getD i ⟨0, 0, 0, 0, 0, 0⟩ = cS i := by
    rw [List.getD_eq_getElem]; rfl
  rw [e] at h
  exact of_decide_eq_true h

/-- **The effect-side margin on the real side.** -/
theorem effect_cells_sum {s r0 : State N} {x : Fin N} {w : Param N} (hw : w ∈ EX N s r0 x) (v : ℕ) :
    N * (ueMarg v : ℝ) - 3 * (KS : ℝ) ^ 2 ≤
      ∑ k, (Real.log (xE w s k / ((ueXmBD : ℚ) : ℝ)) - numRE v (xE w s k) / (1 / 2 + 1 / 100000)) := by
  have hXm : (0 : ℝ) < ((ueXmBD : ℚ) : ℝ) := by unfold ueXmBD; norm_num
  have hcell : ∀ i k, w s k ∈ exIS (cS i) →
      ((ueB v i : ℚ) : ℝ) ≤ Real.log (xE w s k / ((ueXmBD : ℚ) : ℝ)) - numRE v (xE w s k) / (1 / 2 + 1 / 100000) := by
    intro i k hk
    obtain ⟨hlo, hhi⟩ := xE_cell hk
    have hxlo0 : (0 : ℝ) < ((ueXlo (cS i) : ℚ) : ℝ) := by
      have := ueCell_real i
      by_contra hc; push Not at hc
      have hq : ((ueXlo (cS i) / ueXmBD : ℚ) : ℝ) ≤ 0 := by
        push_cast; exact div_nonpos_of_nonpos_of_nonneg hc hXm.le
      have h1 := List.all_eq_true.1 ueCell_ok
      -- positivity is part of the kernel check
      have hz : i.1 < (exSCells.zip (ueCellL.zip ueCellK)).length := by
        have h0 : exSCells.length = 400 := exSCells_len
        simp only [List.length_zip, ueCellL_len, ueCellK_len, h0]
        have := lt_of_lt_of_eq i.2 KS_eq; omega
      have hp := h1 _ (List.getElem_mem hz)
      simp only [List.getElem_zip, Bool.and_eq_true, decide_eq_true_eq] at hp
      have : (0 : ℝ) < ((ueXlo (cS i) / ueXmBD : ℚ) : ℝ) := by exact_mod_cast hp.1.1
      linarith
    have hg : ((ueCellL.getD i 0 : ℚ) : ℝ) ≤ Real.log (xE w s k / ((ueXmBD : ℚ) : ℝ)) := by
      refine (ueCell_real i).trans (Real.log_le_log (by push_cast; positivity) ?_)
      push_cast
      exact div_le_div_of_nonneg_right hlo hXm.le
    have hl : numRE v (xE w s k) ≤ ((ueNum v (ueXhi (cS i)) : ℚ) : ℝ) := by
      rw [← numRE_cast]; exact numRE_mono v (xE_ge_half w s k) hhi
    unfold ueB
    push_cast
    rw [show ((ueFe : ℚ) : ℝ) = 1 / 2 + 1 / 100000 by unfold ueFe; norm_num]
    have := div_le_div_of_nonneg_right hl (by norm_num : (0 : ℝ) ≤ 1 / 2 + 1 / 100000)
    linarith
  have h1 := sum_ge_s_cells hw _ _ hcell
  have h2 := nS_wsum_ge N (fun i => ((ueB v i : ℚ) : ℝ))
  have h3 : ∑ i : Fin KS, |((ueB v i : ℚ) : ℝ)| ≤ 3 * KS := by
    calc ∑ i : Fin KS, |((ueB v i : ℚ) : ℝ)| ≤ ∑ _i : Fin KS, (3 : ℝ) := by
          refine sum_le_sum fun i _ => ?_
          have := ueB_abs_le v i
          exact_mod_cast (by exact_mod_cast this : ((|ueB v i| : ℚ) : ℝ) ≤ 3)
      _ = 3 * KS := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have h4 : (ueMarg v : ℝ) ≤ ∑ i : Fin KS, ((cS i).a : ℝ) * ((ueB v i : ℚ) : ℝ) := by
    have : ueMarg v ≤ ueSum v := by
      rcases v with _ | _ | v
      · exact ueSum_ok0
      · exact ueSum_ok1
      · have e1 : ueMarg (v + 2) = ueMarg 2 := rfl
        have e2 : ueSum (v + 2) = ueSum 2 := by simp [ueSum, ueNum]
        rw [e1, e2]; exact ueSum_ok2
    rw [ueSum_eq] at this
    exact_mod_cast this
  have hKS : (0 : ℝ) ≤ KS := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have h5 := mul_le_mul_of_nonneg_left h4 hN0
  have h6 := mul_le_mul_of_nonneg_left h3 hKS
  nlinarith

end Census
end IIT
