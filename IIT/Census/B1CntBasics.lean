/-
Census, B1, W14 work package WP0 (basics) for the count over `GoodX3`: geometry of subcubes (W5 Lemma S),
deviation of subcube means from FE1 (W5 FE1'), small bridges, and measurability of the count events.
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §5.  No `sorry`.
-/
import IIT.Census.B1CntGlue3

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### Openness and reachability -/

theorem cnt_flipP_open {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    (hg : GoodW3 N s r0 x σ w) (hfr : CountFreshX N s r0 w) : flipP s w ∈ openCube N :=
  flipP_mem_openCube (cnt_mem_openCube hg hfr)

theorem cnt_reach {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    (hg : GoodW3 N s r0 x σ w) (hfr : CountFreshX N s r0 w) :
    0 < ∑ v : State N, fullProb (tpmOf (flipP s w)) v s := by
  have hw := cnt_mem_openCube hg hfr
  have hpos : 0 < fullProb (tpmOf (flipP s w)) s s := by
    rw [fullProb_flipP]
    unfold rowTX
    refine prod_pos fun k _ => ?_
    have hk := (hw s k).1
    simpa [b1_clamp01_of_mem_Ioo (hw s k)] using hk
  exact lt_of_lt_of_le hpos (single_le_sum (f := fun v => fullProb (tpmOf (flipP s w)) v s)
    (fun v _ => fullProb_nonneg _ _ _) (mem_univ s))

/-! ### Geometry (W5 Lemma S) -/

lemma sum_choose_le_succ_pow (D ρ : ℕ) :
    ∑ m ∈ range (ρ + 1), D.choose m ≤ (D + 1) ^ ρ := by
  rw [add_pow]
  refine sum_le_sum fun m hm => ?_
  have hmρ : m ≤ ρ := Nat.lt_succ_iff.1 (mem_range.1 hm)
  have h1 : 1 ≤ ρ.choose m := Nat.choose_pos hmρ
  calc D.choose m ≤ D ^ m := Nat.choose_le_pow D m
    _ ≤ D ^ m * 1 ^ (ρ - m) * ρ.choose m := by rw [one_pow, mul_one]; exact Nat.le_mul_of_pos_right _ h1

theorem card_agree_ball_le (A : Finset (Fin N)) (t c : State N) (ρ : ℕ) :
    ((agree A t).filter fun r => ham c r ≤ ρ).card ≤ (N - A.card + 1) ^ ρ := by
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
  exact sum_choose_le_succ_pow _ _

lemma ham_le_of_mem_agree {A : Finset (Fin N)} {t r r' : State N} (hr : r ∈ agree A t)
    (hr' : r' ∈ agree A t) : ham r r' ≤ N - A.card := by
  have hAc : Aᶜ.card = N - A.card := by rw [card_compl, Fintype.card_fin]
  rw [← hAc]
  refine card_le_card fun i hi => ?_
  simp only [mem_filter, mem_univ, true_and] at hi
  rw [mem_compl]
  intro hiA
  exact hi ((mem_agree.1 hr i hiA).trans (mem_agree.1 hr' i hiA).symm)

theorem agree_not_both_balls {s r0 : State N} (hfar : N ≤ 3 * ham r0 s) (A : Finset (Fin N))
    (t : State N) (hD : 3 * (N - A.card) + 19 ≤ N) {r r' : State N} (hr : r ∈ agree A t)
    (hr' : r' ∈ agree A t) : ¬ (ham r0 r ≤ 4 ∧ ham s r' ≤ 2) := by
  rintro ⟨h1, h2⟩
  have h3 := ham_le_of_mem_agree hr hr'
  have h4 : ham r0 s ≤ ham r0 r + ham r r' + ham r' s :=
    (ham_triangle r0 r' s).trans (Nat.add_le_add_right (ham_triangle r0 r r') _)
  have h5 : ham r' s = ham s r' := ham_comm _ _
  omega

/-! ### Small bridges -/

theorem subMean_eq_colMean (w : Param N) (A : Finset (Fin N)) (t : State N) (i : Fin N) :
    subMean w A t i = colMean w A t i := by
  unfold subMean colMean
  rw [card_agree]
  push_cast
  rfl

theorem rowTX_teW (w : Param N) (s r : State N) : rowTX w s r (teW w s) = ∏ k, pTe w s r k := by
  unfold rowTX
  refine prod_congr rfl fun k _ => ?_
  unfold teW pTe
  split_ifs <;> simp_all

theorem measurable_glueRows_right (F : Finset (State N)) (f : F → Fin N → ℝ) :
    Measurable (glueRows F f) :=
  (measurable_glueRows F).comp (measurable_const.prodMk measurable_id)

/-! ### Deviation of subcube means (W5 FE1') -/

lemma abs_sum_sub_half_le_split (w : Param N) (F : Finset (State N)) (C : Finset (State N))
    (i : Fin N) (hw : ∀ r, 0 ≤ clamp01 (w r i) ∧ clamp01 (w r i) ≤ 1) :
    |∑ r ∈ C, (clamp01 (w r i) - 1 / 2)| ≤
      |∑ r ∈ C.filter (fun r => r ∉ F), (clamp01 (w r i) - 1 / 2)| +
        ((C.filter fun r => r ∈ F).card : ℝ) / 2 := by
  rw [← sum_filter_add_sum_filter_not C (fun r => r ∈ F)]
  refine (abs_add_le _ _).trans ?_
  rw [add_comm]
  refine add_le_add le_rfl ((abs_sum_le_sum_abs _ _).trans ?_)
  have hb : ∀ r, |clamp01 (w r i) - 1 / 2| ≤ 1 / 2 := fun r => by
    rw [abs_le]; constructor <;> linarith [(hw r).1, (hw r).2]
  calc ∑ r ∈ C.filter (fun r => r ∈ F), |clamp01 (w r i) - 1 / 2|
      ≤ ∑ _r ∈ C.filter (fun r => r ∈ F), (1 / 2 : ℝ) := sum_le_sum fun r _ => hb r
    _ = ((C.filter fun r => r ∈ F).card : ℝ) / 2 := by rw [sum_const, nsmul_eq_mul]; ring

lemma sqrt_mul_div_pow (N D : ℕ) :
    2 * Real.sqrt ((N : ℝ) * 2 ^ D) / 2 ^ D = 2 * Real.sqrt ((N : ℝ) / 2 ^ D) := by
  have h2 : (0 : ℝ) < 2 ^ D := by positivity
  have hsq : Real.sqrt ((2 : ℝ) ^ D) * Real.sqrt ((2 : ℝ) ^ D) = 2 ^ D := Real.mul_self_sqrt h2.le
  have hsp : 0 < Real.sqrt ((2 : ℝ) ^ D) := Real.sqrt_pos.2 h2
  rw [Real.sqrt_mul' _ h2.le, Real.sqrt_div' _ h2.le]
  set a := Real.sqrt ((2 : ℝ) ^ D)
  rw [← hsq]
  field_simp

theorem cnt_subDev : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N),
    GoodW3 N s r0 x σ w → CountFreshX N s r0 w →
      ∀ (A : Finset (Fin N)) (t : State N) (i : Fin N), A.card + D0C N ≤ N →
        |subMean w A t i - 1 / 2| ≤ 2 * Real.sqrt ((N : ℝ) / 2 ^ (N - A.card)) +
          2 * ((N - A.card + 1 : ℕ) : ℝ) ^ 4 / 2 ^ (N - A.card) := by
  refine Eventually.of_forall fun N s r0 x σ w hg hfr A t i hA => ?_
  set D := N - A.card with hDdef
  have hcard : ((agree A t).card : ℝ) = 2 ^ D := by rw [card_agree]; push_cast; rfl
  have h2 : (0 : ℝ) < 2 ^ D := by positivity
  have hmean : subMean w A t i - 1 / 2 = (∑ r ∈ agree A t, (clamp01 (w r i) - 1 / 2)) / 2 ^ D := by
    unfold subMean
    rw [hcard, sum_sub_distrib, sum_const, nsmul_eq_mul, hcard]
    field_simp
  have hsplit := abs_sum_sub_half_le_split w (sensRows s r0) (agree A t) i
    fun r => ⟨clamp01_nonneg _, clamp01_le_one _⟩
  have hfresh := hfr.fe1 t A hA i
  have hsens : (((agree A t).filter fun r => r ∈ sensRows s r0).card : ℝ) ≤
      2 * ((D + 1 : ℕ) : ℝ) ^ 4 := by
    have hsub : (agree A t).filter (fun r => r ∈ sensRows s r0) ⊆
        ((agree A t).filter fun r => ham r0 r ≤ 4) ∪ ((agree A t).filter fun r => ham s r ≤ 2) := by
      intro r hr
      rw [mem_filter] at hr
      rcases mem_union.1 hr.2 with h | h
      · refine mem_union_left _ (mem_filter.2 ⟨hr.1, ?_⟩)
        simp only [ballR, mem_filter, mem_univ, true_and] at h; exact h
      · refine mem_union_right _ (mem_filter.2 ⟨hr.1, ?_⟩)
        simp only [ballR, mem_filter, mem_univ, true_and] at h; exact h
    have hc := (card_le_card hsub).trans (card_union_le _ _)
    have hb1 : ((agree A t).filter fun r => ham r0 r ≤ 4).card ≤ (D + 1) ^ 4 :=
      card_agree_ball_le A t r0 4
    have hb2 : ((agree A t).filter fun r => ham s r ≤ 2).card ≤ (D + 1) ^ 2 :=
      card_agree_ball_le A t s 2
    have hle : (D + 1) ^ 2 ≤ (D + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have : ((agree A t).filter fun r => r ∈ sensRows s r0).card ≤ 2 * (D + 1) ^ 4 := by omega
    exact_mod_cast this
  rw [hmean, abs_div, abs_of_pos h2, div_le_iff₀ h2]
  calc |∑ r ∈ agree A t, (clamp01 (w r i) - 1 / 2)|
      ≤ 2 * Real.sqrt ((N : ℝ) * 2 ^ D) + 2 * ((D + 1 : ℕ) : ℝ) ^ 4 / 2 := by
        refine hsplit.trans (add_le_add hfresh ?_)
        linarith
    _ ≤ (2 * Real.sqrt ((N : ℝ) / 2 ^ D) + 2 * ((D + 1 : ℕ) : ℝ) ^ 4 / 2 ^ D) * 2 ^ D := by
        rw [add_mul, div_mul_cancel₀ _ h2.ne', ← sqrt_mul_div_pow N D, div_mul_cancel₀ _ h2.ne']
        have : (0 : ℝ) ≤ ((D + 1 : ℕ) : ℝ) ^ 4 := by positivity
        linarith

theorem cnt_colDev : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N),
    GoodW3 N s r0 x σ w → CountFreshX N s r0 w → ∀ (t : State N) (i : Fin N),
      |subMean w ∅ t i - 1 / 2| ≤ epsN N := by
  filter_upwards [eventually_ge_atTop 64] with N hN s r0 x σ w hg hfr t i
  have hD0 : (∅ : Finset (Fin N)).card + D0C N ≤ N := by
    simp only [card_empty, zero_add, D0C]
    have h2 : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
    have key : ∀ L : ℕ, 6 ≤ L → 2 * L + 14 ≤ 2 ^ L := by
      intro L hL
      induction L, hL using Nat.le_induction with
      | base => norm_num
      | succ n hn ih => rw [pow_succ]; omega
    by_cases hL : Nat.log 2 N ≤ 5
    · omega
    · exact (key _ (by omega)).trans h2
  have hN4 : (N : ℝ) ≥ 64 := by exact_mod_cast hN
  have hcard : ((agree (∅ : Finset (Fin N)) t).card : ℝ) = 2 ^ N := by
    rw [card_agree]; simp
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  have hmean : subMean w ∅ t i - 1 / 2 =
      (∑ r ∈ agree (∅ : Finset (Fin N)) t, (clamp01 (w r i) - 1 / 2)) / 2 ^ N := by
    unfold subMean
    rw [hcard, sum_sub_distrib, sum_const, nsmul_eq_mul, hcard]
    field_simp
  have hsplit := abs_sum_sub_half_le_split w (sensRows s r0) (agree (∅ : Finset (Fin N)) t) i
    fun r => ⟨clamp01_nonneg _, clamp01_le_one _⟩
  have hfresh := hfr.fe1 t ∅ hD0 i
  simp only [card_empty, Nat.sub_zero] at hfresh
  have hsens : (((agree (∅ : Finset (Fin N)) t).filter fun r => r ∈ sensRows s r0).card : ℝ) ≤
      4 * (N : ℝ) ^ 4 := by
    have h1 : ((agree (∅ : Finset (Fin N)) t).filter fun r => r ∈ sensRows s r0).card ≤
        (sensRows s r0).card := by
      refine card_le_card fun r hr => (mem_filter.1 hr).2
    have h2' := card_sensRows_le s r0
    have h3 : ((((agree (∅ : Finset (Fin N)) t).filter fun r => r ∈ sensRows s r0).card : ℕ) : ℝ) ≤
        2 * ((N : ℝ) + 1) ^ 4 := by exact_mod_cast h1.trans h2'
    have h4 : ((N : ℝ) + 1) ^ 4 ≤ 2 * (N : ℝ) ^ 4 := by nlinarith [sq_nonneg ((N : ℝ) ^ 2), sq_nonneg (N : ℝ)]
    linarith
  rw [hmean, abs_div, abs_of_pos h2, div_le_iff₀ h2]
  unfold epsN
  calc |∑ r ∈ agree (∅ : Finset (Fin N)) t, (clamp01 (w r i) - 1 / 2)|
      ≤ 2 * Real.sqrt ((N : ℝ) * 2 ^ N) + 4 * (N : ℝ) ^ 4 / 2 := by
        refine hsplit.trans (add_le_add hfresh ?_)
        linarith
    _ = (2 * Real.sqrt ((N : ℝ) / 2 ^ N) + 2 * (N : ℝ) ^ 4 / 2 ^ N) * 2 ^ N := by
        rw [add_mul, div_mul_cancel₀ _ h2.ne', ← sqrt_mul_div_pow N N, div_mul_cancel₀ _ h2.ne']
        ring

/-! ### Measurability -/

lemma measurable_effDevA (s : State N) (A : Finset (Fin N)) (t : State N) (k : Fin N) :
    Measurable fun w : Param N => effDevA w s A t k :=
  (Finset.measurable_sum _ fun r _ => (b1mx_pTe s r k).sub_const _).div_const _

lemma measurable_sgnMul {f g : Param N → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun w => sgnMul (f w) (g w) := by
  unfold sgnMul
  exact Measurable.ite (measurableSet_lt measurable_const hf) hg hg.neg

theorem measurableSet_CoreAt (s : State N) (K : Finset (Fin N)) (k : Fin N) (κ : ℝ) :
    MeasurableSet {w : Param N | CoreAt N s K k κ w} := by
  have hf : ∀ k', Measurable fun w : Param N => fK w s K k' := fun k' =>
    measurable_effDevA s _ s k'
  have ha : ∀ k', Measurable fun w : Param N => |fK w s K k'| := fun k' =>
    continuous_abs.measurable.comp (hf k')
  have hh : ∀ j, Measurable fun w : Param N => hK w s K j k := fun j =>
    measurable_effDevA s _ _ k
  unfold CoreAt
  refine b1_mset_and (measurableSet_lt measurable_const (ha k)) (b1_mset_and
    (measurableSet_lt (ha k) measurable_const) (b1_mset_and ?_ ?_))
  · exact b1_mset_forall fun k' => b1_mset_imp (MeasurableSet.const _)
      (measurableSet_lt (ha k') measurable_const)
  · exact b1_mset_forall fun j => b1_mset_imp (MeasurableSet.const _)
      (measurableSet_lt (measurable_sgnMul (hf k) (hh j))
        (((ha k).const_mul _).sub_const _ |>.sub_const _))

lemma measurableSet_DleAt (s : State N) (K : Finset (Fin N)) (k : Fin N) :
    MeasurableSet {w : Param N | DleAt N s K k w} := by
  have hf : Measurable fun w : Param N => fK w s K k := measurable_effDevA s _ s k
  have ha : Measurable fun w : Param N => |fK w s K k| := continuous_abs.measurable.comp hf
  unfold DleAt
  refine b1_mset_forall fun A => b1_mset_imp (MeasurableSet.const _) (b1_mset_imp
    (MeasurableSet.const _) (b1_mset_imp (MeasurableSet.const _) (b1_mset_imp
    (MeasurableSet.const _) ?_)))
  exact measurableSet_lt (measurable_sgnMul hf (measurable_effDevA s A s k))
    ((ha.mul_const _).sub_const _)

theorem measurableSet_YK (s : State N) (K : Finset (Fin N)) :
    MeasurableSet {w : Param N | YK N s K w} := by
  unfold YK
  refine b1_mset_exists fun k => b1_mset_and (MeasurableSet.const _) (b1_mset_and
    (measurableSet_CoreAt s K k 0) (b1_mset_and
      (measurableSet_lt measurable_const (measurable_effDevA s _ s k)) (measurableSet_DleAt s K k)))

theorem measurableSet_SignK (s : State N) (K : Finset (Fin N)) :
    MeasurableSet {w : Param N | SignK N s K w} := by
  unfold SignK
  exact b1_mset_exists fun k => b1_mset_and (MeasurableSet.const _) (b1_mset_and
    (measurableSet_CoreAt s K k 0) (measurableSet_lt measurable_const (measurable_effDevA s _ s k)))

theorem measurableSet_RetK (s r0 : State N) (K : Finset (Fin N)) :
    MeasurableSet {w : Param N | RetK N s r0 K w} := by
  unfold RetK
  exact b1_mset_forall fun r => b1_mset_imp (MeasurableSet.const _)
    (measurableSet_lt measurable_const (b1m_XMW _ r))

lemma measurable_card_filter {α : Type*} [Fintype α] {P : Param N → α → Prop}
    [∀ w, DecidablePred (P w)] (hP : ∀ a, MeasurableSet {w | P w a}) :
    Measurable fun w => ((univ : Finset α).filter (P w)).card := by
  refine measurable_to_countable' fun n => ?_
  have e : (fun w => ((univ : Finset α).filter (P w)).card) ⁻¹' {n} =
      {w | n ≤ ((univ : Finset α).filter (P w)).card} \
        {w | n + 1 ≤ ((univ : Finset α).filter (P w)).card} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq, not_le]
    omega
  rw [e]
  exact (b1_measurableSet_card_filter_ge hP n).diff (b1_measurableSet_card_filter_ge hP (n + 1))

lemma measurable_WCnt (s r0 : State N) (x : Fin N) (σ : XSide) :
    Measurable fun w : Param N => WCnt N s r0 x σ w := by
  have e : (fun w : Param N => WCnt N s r0 x σ w) = fun w =>
      ((univ : Finset (Finset (Fin N))).filter fun K => K ∈ famX3 N s r0 x σ w ∧ YK N s K w).card := by
    funext w; unfold WCnt; congr 1; ext K; simp
  rw [e]
  exact measurable_card_filter
    fun K => (measurableSet_mem_famX3 s r0 x σ K).inter (measurableSet_YK s K)

lemma measurable_RFCnt (s r0 : State N) (x : Fin N) (σ : XSide) :
    Measurable fun w : Param N => RFCnt N s r0 x σ w := by
  have e : (fun w : Param N => RFCnt N s r0 x σ w) = fun w =>
      ((univ : Finset (Finset (Fin N))).filter fun K =>
        K ∈ famX3 N s r0 x σ w ∧ ¬ RetK N s r0 K w).card := by
    funext w; unfold RFCnt; congr 1; ext K; simp
  rw [e]
  exact measurable_card_filter
    fun K => (measurableSet_mem_famX3 s r0 x σ K).inter (measurableSet_RetK s r0 K).compl

lemma measurable_famX3_card (s r0 : State N) (x : Fin N) (σ : XSide) :
    Measurable fun w : Param N => (famX3 N s r0 x σ w).card := by
  have e : (fun w : Param N => (famX3 N s r0 x σ w).card) = fun w =>
      ((univ : Finset (Finset (Fin N))).filter fun K => K ∈ famX3 N s r0 x σ w).card := by
    funext w; congr 1; ext K; simp
  rw [e]
  exact measurable_card_filter
    fun K => measurableSet_mem_famX3 s r0 x σ K

theorem measurableSet_WBad (s r0 : State N) (x : Fin N) (σ : XSide) :
    MeasurableSet (WBad N s r0 x σ) :=
  measurableSet_lt (measurable_from_nat.comp (measurable_WCnt s r0 x σ))
    (((measurable_from_nat.comp (measurable_famX3_card s r0 x σ)).mul_const _).div_const _)

theorem measurableSet_RetBad (s r0 : State N) (x : Fin N) (σ : XSide) :
    MeasurableSet (RetBad N s r0 x σ) :=
  measurableSet_lt (((measurable_from_nat.comp (measurable_famX3_card s r0 x σ)).mul_const _).div_const _)
    (measurable_from_nat.comp (measurable_RFCnt s r0 x σ))

end Census
end IIT

#print axioms IIT.Census.card_agree_ball_le
#print axioms IIT.Census.agree_not_both_balls
#print axioms IIT.Census.cnt_subDev
#print axioms IIT.Census.cnt_colDev
#print axioms IIT.Census.measurableSet_YK
#print axioms IIT.Census.measurableSet_WBad
#print axioms IIT.Census.measurableSet_RetBad
