/-
Census, B1 lower bound (C1'), part (a): the explicit regime-X type event `EX` and `P(EX) ≥ e^{-(KL_p + KL_s + ε) N}`.

Data: `CertEX` (corrected coarse design 40 × 100, row `s` 200 × 2, `g5_lbX_cert_coarse2.py`).
* Pair cells `IP i = [f + sa·hy, f + (sa+1)·hy) × [u0, u1)` for the entries `(w r0 j, w (r0^x) j)`;
* row-`s` cells `IS i = [x0, x1)` for the entries `w s k`.
-/
import IIT.Census.CertEX
import IIT.Census.CertRatesTypeEvent
import IIT.Census.B1TypeGen
import IIT.Census.B1DefsX

namespace IIT
namespace Census

open MeasureTheory Finset

/-! ### Pairwise from a chain of a relation transitive on the list -/

lemma pairwise_of_isChain {α : Type} {R : α → α → Prop} (P : α → Prop)
    (htr : ∀ a b c, P a → P b → P c → R a b → R b c → R a c) :
    ∀ l : List α, (∀ x ∈ l, P x) → l.IsChain R → l.Pairwise R
  | [], _, _ => List.Pairwise.nil
  | [_], _, _ => List.pairwise_singleton _ _
  | a :: b :: l, hP, h => by
      have hc := List.isChain_cons_cons.1 h
      have ih := pairwise_of_isChain P htr (b :: l) (fun x hx => hP x (List.mem_cons_of_mem _ hx)) hc.2
      refine List.Pairwise.cons (fun c hc' => ?_) ih
      rcases List.mem_cons.1 hc' with rfl | hcl
      · exact hc.1
      · exact htr a b c (hP a (by simp)) (hP b (by simp)) (hP c (by simp [hcl])) hc.1
          (List.rel_of_pairwise_cons ih hcl)

/-! ### Cell facts -/

/-- The certified facts of a pair cell. -/
lemma exP_facts {C : EXPCell} (hC : C ∈ exPCells) :
    0 < C.a ∧ C.sa < 40 ∧ 0 ≤ C.u0 ∧ C.u0 < C.u1 ∧ C.u1 ≤ 1 ∧ C.a ≤ C.Q * (exHy * (C.u1 - C.u0)) ∧
      Real.log C.Q ≤ C.r := by
  have h := (List.all_eq_true.1 exPCells_ok) C hC
  rw [exPOK] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, hl⟩ := h
  refine ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3, of_decide_eq_true h4,
    of_decide_eq_true h5, of_decide_eq_true h6, crLog_le C.k 30 ?_⟩
  simp only [Bool.and_eq_true]; exact hl

lemma exS_facts {C : EXSCell} (hC : C ∈ exSCells) :
    0 < C.a ∧ 0 ≤ C.x0 ∧ C.x0 < C.x1 ∧ C.x1 ≤ 1 ∧ C.a ≤ C.Q * (C.x1 - C.x0) ∧ Real.log C.Q ≤ C.r := by
  have h := (List.all_eq_true.1 exSCells_ok) C hC
  rw [exSOK] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hl⟩ := h
  refine ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3, of_decide_eq_true h4,
    of_decide_eq_true h5, crLog_le C.k 30 ?_⟩
  simp only [Bool.and_eq_true]; exact hl

lemma exHy_val : exHy = 999 / 80000 := by unfold exHy; norm_num

/-- Lower `y` end of a pair cell. -/
def exYlo (C : EXPCell) : ℚ := exF + C.sa * exHy

/-- The pair cell as a subset of `ℝ²`. -/
def exIP (C : EXPCell) : Set (ℝ × ℝ) :=
  Set.Ico (exYlo C : ℝ) (exYlo C + exHy : ℚ) ×ˢ Set.Ico (C.u0 : ℝ) C.u1

/-- The row-`s` cell. -/
def exIS (C : EXSCell) : Set ℝ := Set.Ico (C.x0 : ℝ) C.x1

lemma unif_Ico {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    unif (Set.Ico a b) = ENNReal.ofReal (b - a) := by
  unfold unif
  rw [Measure.restrict_apply measurableSet_Ico,
    Set.inter_eq_left.2 (Set.Ico_subset_Icc_self.trans (Set.Icc_subset_Icc ha hb)), Real.volume_Ico]

lemma exHy_pos : (0 : ℚ) < exHy := by rw [exHy_val]; norm_num

lemma exP_measure {C : EXPCell} (hC : C ∈ exPCells) :
    (unif.prod unif) (exIP C) = ENNReal.ofReal ((exHy : ℝ) * (C.u1 - C.u0)) := by
  obtain ⟨-, hsa, hu0, hu01, hu1, -⟩ := exP_facts hC
  have hy0 : (0 : ℝ) ≤ exYlo C := by
    have : (0 : ℚ) ≤ exYlo C := by unfold exYlo exF; have := exHy_pos; positivity
    exact_mod_cast this
  have hyy : (exYlo C : ℝ) ≤ ((exYlo C + exHy : ℚ) : ℝ) := by
    have := exHy_pos; exact_mod_cast (by linarith : exYlo C ≤ exYlo C + exHy)
  have hy1 : ((exYlo C + exHy : ℚ) : ℝ) ≤ 1 := by
    have : exYlo C + exHy ≤ 1 := by
      unfold exYlo exF; rw [exHy_val]
      have : (C.sa : ℚ) ≤ 39 := by exact_mod_cast Nat.lt_succ_iff.1 hsa
      linarith
    exact_mod_cast this
  have hhy : (0 : ℝ) ≤ exHy := by exact_mod_cast exHy_pos.le
  rw [exIP, Measure.prod_prod, unif_Ico hy0 hyy hy1,
    unif_Ico (by exact_mod_cast hu0) (by exact_mod_cast hu01.le) (by exact_mod_cast hu1),
    ← ENNReal.ofReal_mul (by linarith)]
  congr 1; push_cast; ring

lemma exS_measure {C : EXSCell} (hC : C ∈ exSCells) :
    unif (exIS C) = ENNReal.ofReal ((C.x1 : ℝ) - C.x0) := by
  obtain ⟨-, h0, h01, h1, -⟩ := exS_facts hC
  exact unif_Ico (by exact_mod_cast h0) (by exact_mod_cast h01.le) (by exact_mod_cast h1)

/-- `log (a / ℓ) ≤ r` for a pair cell. -/
lemma exP_log_le {C : EXPCell} (hC : C ∈ exPCells) :
    Real.log ((C.a : ℝ) / ((exHy : ℝ) * (C.u1 - C.u0))) ≤ C.r := by
  obtain ⟨ha, -, -, hu01, -, hQ, hr⟩ := exP_facts hC
  have hl : (0 : ℝ) < (exHy : ℝ) * (C.u1 - C.u0) := by
    have : (0 : ℚ) < exHy * (C.u1 - C.u0) := mul_pos exHy_pos (by linarith)
    exact_mod_cast this
  refine le_trans (Real.log_le_log (by positivity) ?_) hr
  rw [div_le_iff₀ hl]; exact_mod_cast hQ

lemma exS_log_le {C : EXSCell} (hC : C ∈ exSCells) :
    Real.log ((C.a : ℝ) / ((C.x1 : ℝ) - C.x0)) ≤ C.r := by
  obtain ⟨ha, -, h01, -, hQ, hr⟩ := exS_facts hC
  have hl : (0 : ℝ) < (C.x1 : ℝ) - C.x0 := by
    have : (C.x0 : ℝ) < C.x1 := by exact_mod_cast h01
    linarith
  refine le_trans (Real.log_le_log (by positivity) ?_) hr
  rw [div_le_iff₀ hl]; exact_mod_cast hQ

/-! ### Disjointness -/

lemma exP_disj_of_rel {C D : EXPCell} (h : exPRel C D = true) : Disjoint (exIP C) (exIP D) := by
  unfold exPRel at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [exIP, exIP, Set.disjoint_prod]
  rcases h with h | ⟨-, h⟩
  · left
    have : exYlo C + exHy ≤ exYlo D := by
      unfold exYlo
      have : (C.sa : ℚ) + 1 ≤ D.sa := by exact_mod_cast h
      nlinarith [exHy_pos]
    have h' : ((exYlo C + exHy : ℚ) : ℝ) ≤ exYlo D := by exact_mod_cast this
    exact Set.disjoint_left.2 fun y hy hy' => by linarith [hy.2, hy'.1]
  · right
    have h' : (C.u1 : ℝ) ≤ D.u0 := by exact_mod_cast h
    exact Set.disjoint_left.2 fun y hy hy' => by linarith [hy.2, hy'.1]

lemma exS_disj_of_rel {C D : EXSCell} (h : exSRel C D = true) : Disjoint (exIS C) (exIS D) := by
  unfold exSRel at h
  have h' : (C.x1 : ℝ) ≤ D.x0 := by exact_mod_cast of_decide_eq_true h
  exact Set.disjoint_left.2 fun y hy hy' => by unfold exIS at hy hy'; linarith [hy.2, hy'.1]

lemma exPCells_pairwise : exPCells.Pairwise fun C D => exPRel C D = true := by
  refine pairwise_of_isChain (fun C : EXPCell => C.u0 < C.u1) ?_ exPCells
    (fun C hC => (exP_facts hC).2.2.2.1) (chainB_isChain _ _ exPCells_chainB)
  intro a b c _ hb _ hab hbc
  unfold exPRel at *
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *
  rcases hab with h1 | ⟨h1, h1'⟩ <;> rcases hbc with h2 | ⟨h2, h2'⟩
  · left; omega
  · left; omega
  · left; omega
  · right; exact ⟨h1.trans h2, by linarith⟩

lemma exSCells_pairwise : exSCells.Pairwise fun C D => exSRel C D = true := by
  refine pairwise_of_isChain (fun C : EXSCell => C.x0 < C.x1) ?_ exSCells
    (fun C hC => (exS_facts hC).2.2.1) (chainB_isChain _ _ exSCells_chainB)
  intro a b c _ hb _ hab hbc
  unfold exSRel at *
  simp only [decide_eq_true_eq] at *
  linarith

/-- Index sets. -/
abbrev KP : ℕ := exPCells.length
abbrev KS : ℕ := exSCells.length

/-- Pair cell number `i`, row-`s` cell number `i`. -/
def cP (i : Fin KP) : EXPCell := exPCells[i.1]'i.2
def cS (i : Fin KS) : EXSCell := exSCells[i.1]'i.2

lemma cP_mem (i : Fin KP) : cP i ∈ exPCells := List.getElem_mem i.2
lemma cS_mem (i : Fin KS) : cS i ∈ exSCells := List.getElem_mem i.2

lemma exIP_disjoint : Pairwise fun i j : Fin KP => Disjoint (exIP (cP i)) (exIP (cP j)) := by
  intro i j hij
  have hp := List.pairwise_iff_getElem.1 exPCells_pairwise
  rcases lt_or_gt_of_ne hij with h | h
  · exact exP_disj_of_rel (hp i.1 j.1 i.2 j.2 h)
  · exact (exP_disj_of_rel (hp j.1 i.1 j.2 i.2 h)).symm

lemma exIS_disjoint : Pairwise fun i j : Fin KS => Disjoint (exIS (cS i)) (exIS (cS j)) := by
  intro i j hij
  have hp := List.pairwise_iff_getElem.1 exSCells_pairwise
  rcases lt_or_gt_of_ne hij with h | h
  · exact exS_disj_of_rel (hp i.1 j.1 i.2 j.2 h)
  · exact (exS_disj_of_rel (hp j.1 i.1 j.2 i.2 h)).symm

/-! ### Masses and rounded counts -/

/-- Masses extended by `0` to `ℕ`. -/
noncomputable def aP (j : ℕ) : ℝ := if h : j < KP then ((exPCells[j]'h).a : ℝ) else 0
noncomputable def aS (j : ℕ) : ℝ := if h : j < KS then ((exSCells[j]'h).a : ℝ) else 0

lemma aP_nonneg (j : ℕ) : 0 ≤ aP j := by
  unfold aP; split_ifs with h
  · exact_mod_cast (exP_facts (List.getElem_mem h)).1.le
  · exact le_rfl

lemma aS_nonneg (j : ℕ) : 0 ≤ aS j := by
  unfold aS; split_ifs with h
  · exact_mod_cast (exS_facts (List.getElem_mem h)).1.le
  · exact le_rfl

lemma aP_fin (i : Fin KP) : aP i = ((cP i).a : ℝ) := by simp [aP, cP, i.2]
lemma aS_fin (i : Fin KS) : aS i = ((cS i).a : ℝ) := by simp [aS, cS, i.2]

lemma aP_sum : ∑ j ∈ range KP, aP j = 1 := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [aP_fin, cP]
  have := Fin.sum_univ_fun_getElem exPCells (fun C : EXPCell => (C.a : ℝ))
  rw [this]
  have h1 := exPCells_sum
  have : ((exPCells.map EXPCell.a).sum : ℝ) = 1 := by exact_mod_cast h1
  rw [← this]; push_cast [List.map_map]; rfl

lemma aS_sum : ∑ j ∈ range KS, aS j = 1 := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [aS_fin, cS]
  have := Fin.sum_univ_fun_getElem exSCells (fun C : EXSCell => (C.a : ℝ))
  rw [this]
  have h1 := exSCells_sum
  have : ((exSCells.map EXSCell.a).sum : ℝ) = 1 := by exact_mod_cast h1
  rw [← this]; push_cast [List.map_map]; rfl

lemma KP_pos : 1 ≤ KP := by simp only [KP, exPCells_len]; norm_num
lemma KS_pos : 1 ≤ KS := by simp only [KS, exSCells_len]; norm_num

/-- The rounded counts. -/
noncomputable def nP (N : ℕ) (i : Fin KP) : ℕ := crCounts aP KP N i
noncomputable def nS (N : ℕ) (i : Fin KS) : ℕ := crCounts aS KS N i

lemma nP_sum (N : ℕ) : ∑ i, nP N i = N := by
  unfold nP
  rw [Fin.sum_univ_eq_sum_range (fun j => crCounts aP KP N j)]
  exact crCounts_sum aP_nonneg aP_sum KP_pos N

lemma nS_sum (N : ℕ) : ∑ i, nS N i = N := by
  unfold nS
  rw [Fin.sum_univ_eq_sum_range (fun j => crCounts aS KS N j)]
  exact crCounts_sum aS_nonneg aS_sum KS_pos N

lemma nP_err (N : ℕ) (i : Fin KP) : |(nP N i : ℝ) - ((cP i).a : ℝ) * N| ≤ KP := by
  rw [← aP_fin]; exact crCounts_abs_le aP_nonneg aP_sum KP_pos N i

lemma nS_err (N : ℕ) (i : Fin KS) : |(nS N i : ℝ) - ((cS i).a : ℝ) * N| ≤ KS := by
  rw [← aS_fin]; exact crCounts_abs_le aS_nonneg aS_sum KS_pos N i

/-! ### The event and its probability -/

open Classical in
/-- **The regime-X lower-bound event** `E_X(s, r0, x)`: the joint type of the entries `(w r0 j, w (r0^x) j)` over the
pair cells and the type of the entries `w s k` over the row-`s` cells. -/
noncomputable def EX (N : ℕ) (s r0 : State N) (x : Fin N) : Set (Param N) :=
  {w | (∀ i : Fin KP, (univ.filter fun j => (w r0 j, w (flipAt x r0) j) ∈ exIP (cP i)).card = nP N i) ∧
    ∀ i : Fin KS, (univ.filter fun k => w s k ∈ exIS (cS i)).card = nS N i}

/-- Cell lengths. -/
noncomputable def ellP (i : Fin KP) : ℝ := (exHy : ℝ) * ((cP i).u1 - (cP i).u0)
noncomputable def ellS (i : Fin KS) : ℝ := ((cS i).x1 : ℝ) - (cS i).x0

lemma ellP_pos (i : Fin KP) : 0 < ellP i := by
  obtain ⟨-, -, -, h, -⟩ := exP_facts (cP_mem i)
  have : (0 : ℚ) < exHy * ((cP i).u1 - (cP i).u0) := mul_pos exHy_pos (by linarith)
  unfold ellP; exact_mod_cast this

lemma ellS_pos (i : Fin KS) : 0 < ellS i := by
  obtain ⟨-, -, h, -⟩ := exS_facts (cS_mem i)
  have : (0 : ℚ) < (cS i).x1 - (cS i).x0 := by linarith
  unfold ellS; exact_mod_cast this

/-- The rounding constants. -/
noncomputable def cstP : ℝ := (KP : ℝ) * ∑ i, |Real.log (((cP i).a : ℝ) / ellP i)| + (KP : ℝ) ^ 2 * ∑ i, 1 / ((cP i).a : ℝ)
noncomputable def cstS : ℝ := (KS : ℝ) * ∑ i, |Real.log (((cS i).a : ℝ) / ellS i)| + (KS : ℝ) ^ 2 * ∑ i, 1 / ((cS i).a : ℝ)

lemma KLP_le : ∑ i, ((cP i).a : ℝ) * Real.log (((cP i).a : ℝ) / ellP i) ≤ exKLPhi := by
  calc ∑ i, ((cP i).a : ℝ) * Real.log (((cP i).a : ℝ) / ellP i) ≤ ∑ i, ((cP i).a : ℝ) * (cP i).r :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (exP_log_le (cP_mem i))
          (by exact_mod_cast (exP_facts (cP_mem i)).1.le)
    _ = (((exPCells.map fun C => C.a * C.r).sum : ℚ) : ℝ) := by
        simp only [cP]
        rw [Fin.sum_univ_fun_getElem exPCells (fun C : EXPCell => (C.a : ℝ) * C.r)]
        push_cast [List.map_map]; congr 1; exact List.map_congr_left fun C _ => by simp
    _ ≤ exKLPhi := by exact_mod_cast exPCells_KL

lemma KLS_le : ∑ i, ((cS i).a : ℝ) * Real.log (((cS i).a : ℝ) / ellS i) ≤ exKLShi := by
  calc ∑ i, ((cS i).a : ℝ) * Real.log (((cS i).a : ℝ) / ellS i) ≤ ∑ i, ((cS i).a : ℝ) * (cS i).r :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (exS_log_le (cS_mem i))
          (by exact_mod_cast (exS_facts (cS_mem i)).1.le)
    _ = (((exSCells.map fun C => C.a * C.r).sum : ℚ) : ℝ) := by
        simp only [cS]
        rw [Fin.sum_univ_fun_getElem exSCells (fun C : EXSCell => (C.a : ℝ) * C.r)]
        push_cast [List.map_map]; congr 1; exact List.map_congr_left fun C _ => by simp
    _ ≤ exKLShi := by exact_mod_cast exSCells_KL

lemma aP_sum_fin : ∑ i : Fin KP, ((cP i).a : ℝ) = 1 := by
  simp only [← aP_fin]; rw [Fin.sum_univ_eq_sum_range aP]; exact aP_sum

lemma aS_sum_fin : ∑ i : Fin KS, ((cS i).a : ℝ) = 1 := by
  simp only [← aS_fin]; rw [Fin.sum_univ_eq_sum_range aS]; exact aS_sum

open Classical in
/-- **`P(E_X)`, explicit form.** -/
theorem EX_prob_ge {N : ℕ} (hN : 0 < N) (s r0 : State N) (x : Fin N) (h0 : r0 ≠ s)
    (h1 : flipAt x r0 ≠ s) :
    ENNReal.ofReal (Real.exp (-(N * exKLPhi + cstP)) / ((N : ℝ) + 1) ^ KP) *
        ENNReal.ofReal (Real.exp (-(N * exKLShi + cstS)) / ((N : ℝ) + 1) ^ KS) ≤
      cubeM N (EX N s r0 x) := by
  set A : Set ((Fin N → ℝ) × (Fin N → ℝ)) :=
    {ab | ∀ i : Fin KP, (univ.filter fun j => (ab.1 j, ab.2 j) ∈ exIP (cP i)).card = nP N i} with hA
  set B : Set (Fin N → ℝ) := {v | ∀ i : Fin KS, (univ.filter fun k => v k ∈ exIS (cS i)).card = nS N i}
    with hB
  have hIP : ∀ i, MeasurableSet (exIP (cP i)) := fun i => measurableSet_Ico.prod measurableSet_Ico
  have hIS : ∀ i, MeasurableSet (exIS (cS i)) := fun i => measurableSet_Ico
  have hAm : MeasurableSet A := by
    have : A = ⋂ i : Fin KP, {ab : (Fin N → ℝ) × (Fin N → ℝ) |
        (univ.filter fun j => (ab.1 j, ab.2 j) ∈ exIP (cP i)).card = nP N i} := by ext ab; simp [A]
    rw [this]
    refine MeasurableSet.iInter fun i => measurableSet_card_filter
      (fun (j : Fin N) (ab : (Fin N → ℝ) × (Fin N → ℝ)) => (ab.1 j, ab.2 j) ∈ exIP (cP i)) (fun j => ?_) _
    exact (((measurable_pi_apply j).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd)) (hIP i)
  have hBm : MeasurableSet B := cr_measurableSet_type_event _ hIS exIS_disjoint (nS_sum N)
  -- independence of the pair of rows (r0, r0^x) and the row s
  have hind := (iIndepFun_rows (N := N) (fun _ v => v) fun _ => measurable_id).indepFun_prodMk
    (fun _ => measurable_pi_apply _) r0 (flipAt x r0) s h0 h1
  have hsplit := hind.measure_inter_preimage_eq_mul A B hAm hBm
  have hEX : EX N s r0 x = (fun w : Param N => (w r0, w (flipAt x r0))) ⁻¹' A ∩ (fun w : Param N => w s) ⁻¹' B := by
    ext w; simp [EX, A, B]
  rw [hEX, hsplit]
  have hmp : MeasurePreserving (fun w : Param N => w s) (cubeM N) (rowM N) :=
    measurePreserving_eval (fun _ : State N => rowM N) s
  rw [hmp.measure_preimage hBm.nullMeasurableSet]
  gcongr
  · -- the pair rows
    have hpair := pairType_ge (flipAt_ne x r0).symm (exIP ∘ cP) hIP exIP_disjoint ellP
      (fun i => exP_measure (cP_mem i)) ellP_pos (nP N) (nP_sum N)
    have hset : (fun w : Param N => (w r0, w (flipAt x r0))) ⁻¹' A =
        {w : Param N | ∀ j, (univ.filter fun i => (w r0 i, w (flipAt x r0) i) ∈ (exIP ∘ cP) j).card = nP N j} := by
      ext w; simp [A]
    rw [hset]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hpair
    refine div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) (by positivity)
    have hr := cr_type_rate_le (fun i => ((cP i).a : ℝ)) ellP
      (fun i => by exact_mod_cast (exP_facts (cP_mem i)).1) aP_sum_fin ellP_pos (nP N) (nP_sum N) hN (KP : ℝ)
      (nP_err N)
    have hK := KLP_le
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have := mul_le_mul_of_nonneg_left hK hN0
    unfold cstP
    linarith
  · -- the row s
    have hsub : ∀ i, (exIS ∘ cS) i ⊆ Set.Icc 0 1 := fun i => by
      obtain ⟨-, h0, -, h1, -⟩ := exS_facts (cS_mem i)
      exact Set.Ico_subset_Icc_self.trans (Set.Icc_subset_Icc (by exact_mod_cast h0) (by exact_mod_cast h1))
    have hvol : ∀ i, volume ((exIS ∘ cS) i) = ENNReal.ofReal (ellS i) := fun i => by
      simp only [Function.comp, exIS, ellS, Real.volume_Ico]
    have hrow := cr_type_event_ge_KL (exIS ∘ cS) hIS exIS_disjoint hsub ellS hvol ellS_pos
      (fun i => ((cS i).a : ℝ)) (fun i => by exact_mod_cast (exS_facts (cS_mem i)).1) aS_sum_fin
      (nS N) (nS_sum N) hN (KS : ℝ) (nS_err N)
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hrow
    refine div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) (by positivity)
    have hK := KLS_le
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have := mul_le_mul_of_nonneg_left hK hN0
    unfold cstS
    linarith

open Filter in
/-- **`P(E_X) ≥ e^{-(KL_p + KL_s + 10⁻⁵) N}`** for all large `N`. -/
theorem EX_prob_ev : ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N), r0 ≠ s → flipAt x r0 ≠ s →
    Real.exp (-(((exKLPhi : ℝ) + exKLShi + 1 / 10 ^ 5) * N)) ≤ (cubeM N (EX N s r0 x)).toReal := by
  set c : ℝ := |cstP| + |cstS| with hc
  set K : ℝ := (KP : ℝ) + KS with hK
  have hlo := Real.isLittleO_log_id_atTop
  -- c + K log (N+1) ≤ 10⁻⁵ N eventually
  have hev : ∀ᶠ y : ℝ in atTop, c + K * Real.log (y + 1) ≤ y / 10 ^ 5 := by
    have hK0 : 0 ≤ K := by positivity
    have h1 := hlo.def (c := 1 / (4 * 10 ^ 5 * (K + 1))) (by positivity)
    have h1' := (tendsto_atTop_add_const_right atTop 1 tendsto_id).eventually h1
    filter_upwards [h1', eventually_ge_atTop (4 * 10 ^ 5 * (c + K + 1)), eventually_ge_atTop 1] with y hy hyc hy1
    simp only [Real.norm_eq_abs, id] at hy
    have hl0 : 0 ≤ Real.log (y + 1) := Real.log_nonneg (by linarith)
    rw [abs_of_nonneg hl0, abs_of_nonneg (by linarith)] at hy
    have hc0 : 0 ≤ c := by positivity
    have hKl : K * Real.log (y + 1) ≤ K * ((y + 1) / (4 * 10 ^ 5 * (K + 1))) := by
      have := mul_le_mul_of_nonneg_left hy hK0
      calc K * Real.log (y + 1) ≤ K * (1 / (4 * 10 ^ 5 * (K + 1)) * (y + 1)) := this
        _ = K * ((y + 1) / (4 * 10 ^ 5 * (K + 1))) := by ring
    have hfrac : K * ((y + 1) / (4 * 10 ^ 5 * (K + 1))) ≤ (y + 1) / (4 * 10 ^ 5) := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have : c ≤ y / (4 * 10 ^ 5) := by rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hev, eventually_ge_atTop 1] with N hN hN1 s r0 x h0 h1
  have hNpos : 0 < N := hN1
  have hb := EX_prob_ge hNpos s r0 x h0 h1
  rw [← ENNReal.ofReal_mul (by positivity)] at hb
  refine le_trans ?_ ((ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hb)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hpow : ((N : ℝ) + 1) ^ KP * ((N : ℝ) + 1) ^ KS = Real.exp (K * Real.log (N + 1)) := by
    rw [← pow_add, ← Real.exp_log (by positivity : (0 : ℝ) < ((N : ℝ) + 1) ^ (KP + KS)), Real.log_pow, hK]
    push_cast; ring_nf
  rw [div_mul_div_comm, ← Real.exp_add, hpow, ← Real.exp_sub]
  apply Real.exp_le_exp.2
  have hcP := le_abs_self cstP
  have hcS := le_abs_self cstS
  nlinarith

/-- The rate of `E_X` after the union over `r0` (`- ln 2`) is below `RLBX = 1.0085`. -/
theorem EX_rate_lt : ((exKLPhi : ℝ) + exKLShi + 1 / 10 ^ 5) - Real.log 2 < RLBX := by
  have h := exRate
  have hq : ((exKLPhi + exKLShi - 6931471803 / 10000000000 : ℚ) : ℝ) ≤ ((10083 / 10000 : ℚ) : ℝ) := by
    exact_mod_cast h
  push_cast at hq
  have hl := Real.log_two_gt_d9
  unfold RLBX
  linarith

end Census
end IIT
