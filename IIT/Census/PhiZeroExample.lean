/-
Census: a complex with `φ_s > 0` and `Φ = 0`.

The two-unit deterministic system `A' = ¬A ∧ B`, `B' = ¬B ∧ A` in the all-off state.
The whole substrate is a complex with `φ_s > 0` (exact value `1`, not needed here), yet no
mechanism specifies a distinction:
* `{A, B}` has `φ_e = 0`: the partition `({B}, A') | ({A}, B')` reproduces its effect
  repertoire exactly;
* `{A}` (and `{B}`, symmetrically) has `φ_d > 0`, but every maximally irreducible effect
  purview sets `A' = 1`, while the system's unique maximal effect state is all-off: the
  congruent candidates reach at most `log₂(4/3) < 1/2 ≤ φ_e({A})`.
So the distinction set is empty and `Φ = 0` for every tie-break selector.
-/
import IIT.Census.PairCause

namespace IIT
namespace Census

open Finset

/-! ### The example -/

/-- Next state: `A' = ¬A ∧ B`, `B' = ¬B ∧ A`. -/
def exNext (s : State 2) : State 2 := ![!(s 0) && s 1, !(s 1) && s 0]

/-- The deterministic TPM of `exNext`. -/
noncomputable def exTPM : UnitTPM 2 where
  prob i s b := if exNext s i = b then 1 else 0
  nonneg i s b := by split_ifs <;> norm_num
  normalized i s := by cases exNext s i <;> simp

/-- The all-off state. -/
def exState : State 2 := fun _ => false

/-! ### Evaluation helpers -/

lemma ex_prob (i : Fin 2) (s : State 2) (b : Bool) :
    exTPM.prob i s b = if exNext s i = b then 1 else 0 := rfl

lemma sum_state2 (f : State 2 → ℝ) :
    ∑ s : State 2, f s =
      f ![false, false] + f ![false, true] + f ![true, false] + f ![true, true] := by
  rw [← (piFinTwoEquiv fun _ => Bool).symm.sum_comp]
  simp [Fintype.sum_prod_type]
  ring

lemma effUnit_eq_sum (M : Finset (Fin 2)) (m : State 2) (k : Fin 2) (x : Bool) :
    effUnit exTPM M m k x =
      (∑ s : State 2, if (∀ j ∈ M, s j = m j) then exTPM.prob k s x else 0) /
        (2 : ℝ) ^ (2 - M.card) := by
  rw [effUnit, card_agree, agree, Finset.sum_filter]
  norm_num

lemma exNext_exState : exNext exState = exState := by
  funext i; fin_cases i <;> rfl

lemma ex_fullProb (v w : State 2) :
    fullProb exTPM v w = if exNext v = w then 1 else 0 := by
  rw [fullProb, Fin.prod_univ_two, ex_prob, ex_prob]
  by_cases h0 : exNext v 0 = w 0 <;> by_cases h1 : exNext v 1 = w 1 <;>
    simp [h0, h1, funext_iff, Fin.forall_fin_two]

lemma ex_sum_fullProb : ∑ v : State 2, fullProb exTPM v exState = 2 := by
  rw [sum_state2]
  simp only [ex_fullProb]
  norm_num [exNext, exState, funext_iff, Fin.forall_fin_two]

lemma ex_sum_pos : 0 < ∑ v : State 2, fullProb exTPM v exState := by
  rw [ex_sum_fullProb]; norm_num

lemma fin_one_add_one : (1 : Fin 2) + 1 = 0 := by decide

lemma logb_two_two : Real.logb 2 2 = 1 := Real.logb_self_eq_one one_lt_two

lemma pos_logb_eq_zero {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) : pos (Real.logb 2 c) = 0 :=
  max_eq_left (Real.logb_nonpos one_lt_two h0 h1)

lemma logb_four_thirds_pos : 0 < Real.logb 2 (4 / 3) :=
  Real.logb_pos one_lt_two (by norm_num)

lemma logb_four_thirds_lt : Real.logb 2 (4 / 3) < 1 / 2 := by
  have h : Real.logb 2 ((4 / 3) ^ 2) < Real.logb 2 2 :=
    Real.logb_lt_logb one_lt_two (by norm_num) (by norm_num)
  rw [Real.logb_pow, logb_two_two] at h
  push_cast at h
  linarith

/-! ### The system level: `φ_s > 0` -/

lemma ex_sysEffProb (t : State 2) :
    sysEffProb exTPM univ exState exState t = if exState = t then 1 else 0 := by
  rw [sysEffProb_univ, ex_fullProb, exNext_exState]

lemma ex_sysUncEff : sysUncEff exTPM univ exState exState = 1 / 2 := by
  rw [sysUncEff, avgOverStates]
  simp only [sysEffProb_univ]
  rw [ex_sum_fullProb]; norm_num

lemma ex_sysIiE_self : sysIiE exTPM univ exState exState exState = 1 := by
  rw [sysIiE, ex_sysEffProb, ex_sysUncEff]; norm_num [logb_two_two]

lemma ex_sysIiE_ne {t : State 2} (ht : exState ≠ t) :
    sysIiE exTPM univ exState exState t = 0 := by
  rw [sysIiE, ex_sysEffProb]; simp [ht]

lemma mem_ex_sysMaxEffStates {t : State 2} :
    t ∈ sysMaxEffStates exTPM univ exState exState ↔ t = exState := by
  rw [sysMaxEffStates, mem_argmaxSet]
  constructor
  · intro h
    by_contra hne
    have := h exState
    rw [ex_sysIiE_self, ex_sysIiE_ne (Ne.symm hne)] at this
    norm_num at this
  · rintro rfl w
    rw [ex_sysIiE_self]
    by_cases hw : exState = w
    · rw [← hw, ex_sysIiE_self]
    · rw [ex_sysIiE_ne hw]; norm_num

lemma ex_sysCauseProb (t : State 2) :
    sysCauseProb exTPM univ exState exState t = fullProb exTPM t exState :=
  sysCauseProb_univ exTPM exState exState t ex_sum_pos

lemma ex_sysUncCause : sysUncCause exTPM univ exState exState = 1 / 2 := by
  rw [sysUncCause, avgOverStates]
  simp only [ex_sysCauseProb]
  rw [ex_sum_fullProb]; norm_num

lemma ex_sysBackCause (t : State 2) :
    sysBackCause exTPM univ exState exState t = fullProb exTPM t exState / 2 := by
  rw [sysBackCause, ex_sysCauseProb, ex_sysUncCause]
  norm_num

lemma ex_sysIiC (t : State 2) :
    sysIiC exTPM univ exState exState t =
      fullProb exTPM t exState / 2 * Real.logb 2 (fullProb exTPM t exState / (1 / 2)) := by
  rw [sysIiC, ex_sysBackCause, ex_sysCauseProb, ex_sysUncCause]

lemma ex_sysIiC_self : sysIiC exTPM univ exState exState exState = 1 / 2 := by
  rw [ex_sysIiC, ex_fullProb, exNext_exState]; norm_num [logb_two_two]

lemma exState_mem_sysMaxCauseStates : exState ∈ sysMaxCauseStates exTPM univ exState exState := by
  rw [sysMaxCauseStates, mem_argmaxSet]
  intro w
  rw [ex_sysIiC_self, ex_sysIiC, ex_fullProb]
  split_ifs <;> norm_num [logb_two_two]

/-- The per-unit factor of the partitioned repertoires at the all-off state. -/
noncomputable def exFactor (θ : SysPartition 2 univ) (j : Fin 2) : ℝ :=
  effUnit exTPM (θ.cutSet (θ.partOf j))ᶜ exState j false

lemma ex_cut_cases (θ : SysPartition 2 univ) (j : Fin 2) :
    θ.cutSet (θ.partOf j) = ∅ ∨ θ.cutSet (θ.partOf j) = {j + 1} :=
  Finset.subset_singleton_iff.1 ((cutSet_partOf_subset θ (mem_univ j)).trans
    (by fin_cases j <;> decide))

lemma effUnit_univ_exState (j : Fin 2) : effUnit exTPM univ exState j false = 1 := by
  rw [effUnit_univ_prob, ex_prob, exNext_exState]; rfl

lemma effUnit_cut_exState (j : Fin 2) :
    effUnit exTPM ({j + 1} : Finset (Fin 2))ᶜ exState j false = 1 / 2 := by
  rw [effUnit_eq_sum, sum_state2]
  fin_cases j <;> norm_num [ex_prob, exNext, exState, Finset.card_compl]

lemma exFactor_cases (θ : SysPartition 2 univ) (j : Fin 2) :
    (θ.cutSet (θ.partOf j) = ∅ ∧ exFactor θ j = 1) ∨
      ((θ.cutSet (θ.partOf j)).Nonempty ∧ exFactor θ j = 1 / 2) := by
  rcases ex_cut_cases θ j with h | h
  · left; refine ⟨h, ?_⟩
    rw [exFactor, h, compl_empty, effUnit_univ_exState]
  · right; refine ⟨by rw [h]; exact singleton_nonempty _, ?_⟩
    rw [exFactor, h, effUnit_cut_exState]

lemma exFactor_bound (θ : SysPartition 2 univ) :
    0 < exFactor θ 0 * exFactor θ 1 ∧ exFactor θ 0 * exFactor θ 1 ≤ 1 / 2 := by
  obtain ⟨p, hp, hne⟩ := θ.exists_cutSet_nonempty
  obtain ⟨j, hj⟩ := θ.parts_nonempty p hp
  rw [← θ.partOf_eq hp hj] at hne
  have hcut : ∃ j : Fin 2, (θ.cutSet (θ.partOf j)).Nonempty := ⟨j, hne⟩
  rcases exFactor_cases θ 0 with ⟨h0, e0⟩ | ⟨h0, e0⟩ <;>
    rcases exFactor_cases θ 1 with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rw [e0, e1] <;>
    try norm_num
  exfalso
  obtain ⟨j, hj⟩ := hcut
  fin_cases j
  · simp [h0] at hj
  · simp [h1] at hj

lemma ex_sysPartEffProb (θ : SysPartition 2 univ) :
    sysPartEffProb exTPM univ exState θ exState exState = exFactor θ 0 * exFactor θ 1 := by
  rw [sysPartEffProb, merge_univ, Fin.prod_univ_two]; rfl

lemma ex_partCause_factor (C : Finset (Fin 2)) (j : Fin 2) :
    (∑ w : State 2, effUnit exTPM C (merge univ exState w) j (exState j) *
        bgWeight exTPM univ exState w) / (2 : ℝ) ^ (univ : Finset (Fin 2)).card =
      effUnit exTPM C exState j false := by
  simp only [merge_univ, bgWeight_univ exTPM exState _ ex_sum_pos, mul_one, sum_const,
    card_univ, Fintype.card_fin, Fintype.card_pi, Fintype.card_bool, nsmul_eq_mul]
  norm_num
  rfl

lemma ex_sysPartCauseProb (θ : SysPartition 2 univ) :
    sysPartCauseProb exTPM univ exState θ exState exState = exFactor θ 0 * exFactor θ 1 := by
  rw [sysPartCauseProb, Fin.prod_univ_two, ex_partCause_factor, ex_partCause_factor]; rfl

lemma one_lt_inv_factor (θ : SysPartition 2 univ) :
    0 < pos (Real.logb 2 (1 / (exFactor θ 0 * exFactor θ 1))) := by
  obtain ⟨hp, hle⟩ := exFactor_bound θ
  refine lt_max_of_lt_right (Real.logb_pos one_lt_two ?_)
  rw [one_lt_div hp]; linarith

lemma ex_sysPhiAt_pos (θ : SysPartition 2 univ) :
    0 < sysPhiAt exTPM univ exState θ exState exState exState := by
  have h := one_lt_inv_factor θ
  refine lt_min ?_ ?_
  · rw [sysPhiC, ex_sysPartCauseProb, ex_sysBackCause, ex_sysCauseProb, ex_fullProb,
      exNext_exState]
    simp only [ite_true]
    positivity
  · rw [sysPhiE, ex_sysPartEffProb, ex_sysEffProb]
    simpa using h

theorem ex_sysPhi_pos : 0 < sysPhi exTPM univ exState exState := by
  have : Nonempty (SysPartition 2 univ) :=
    ⟨splitAt (mem_univ (0 : Fin 2)) ⟨1, by decide⟩⟩
  obtain ⟨θ, hθ⟩ :=
    argminSet_nonempty (fun θ => normalizedSysPhiAt exTPM univ exState θ exState exState exState)
  have h1 : 0 < sysPhiOfState exTPM univ exState exState exState exState := by
    unfold sysPhiOfState sysMipSetAt
    exact (ex_sysPhiAt_pos θ).trans_le
      (le_sup'OrZero (f := fun θ => sysPhiAt exTPM univ exState θ exState exState exState) hθ)
  exact h1.trans_le (sysPhiOfState_le_sysPhi _ _ _ _ exState_mem_sysMaxCauseStates
    (mem_ex_sysMaxEffStates.2 rfl))

/-! ### The mechanism `{A, B}`: `φ_e = 0` -/

/-- A disintegrating partition of `({A, B}, Z)` that reproduces the effect repertoire:
`A'` stays with `B`, `B'` stays with `A`. -/
def exPart (Z : Finset (Fin 2)) : Partition 2 univ Z where
  blocks := {({1}, Z.filter (· = 0)), ({0}, Z.filter (· = 1))}
  mech_subset := fun _ _ => subset_univ _
  purv_subset := by
    intro b hb
    rcases mem_insert.1 hb with rfl | hb
    · exact filter_subset _ _
    · rw [mem_singleton.1 hb]; exact filter_subset _ _
  mech_disjoint := by
    intro b hb b' hb' hne
    rcases mem_insert.1 hb with rfl | hb <;> rcases mem_insert.1 hb' with rfl | hb'
    · exact absurd rfl hne
    · rw [mem_singleton.1 hb']; exact disjoint_singleton.2 (by decide)
    · rw [mem_singleton.1 hb]; exact disjoint_singleton.2 (by decide)
    · rw [mem_singleton.1 hb, mem_singleton.1 hb'] at hne; exact absurd rfl hne
  purv_disjoint := by
    intro b hb b' hb' hne
    rcases mem_insert.1 hb with rfl | hb <;> rcases mem_insert.1 hb' with rfl | hb'
    · exact absurd rfl hne
    · rw [mem_singleton.1 hb']
      show Disjoint (Z.filter (· = 0)) (Z.filter (· = 1))
      exact disjoint_filter.2 fun x _ h0 h1 => absurd (h0.symm.trans h1) (by decide)
    · rw [mem_singleton.1 hb]
      show Disjoint (Z.filter (· = 1)) (Z.filter (· = 0))
      exact disjoint_filter.2 fun x _ h1 h0 => absurd (h0.symm.trans h1) (by decide)
    · rw [mem_singleton.1 hb, mem_singleton.1 hb'] at hne; exact absurd rfl hne
  mech_cover := by
    intro i _
    fin_cases i
    · exact ⟨_, mem_insert_of_mem (mem_singleton_self _), mem_singleton_self _⟩
    · exact ⟨_, mem_insert_self _ _, mem_singleton_self _⟩
  purv_cover := by
    intro k hk
    fin_cases k
    · exact ⟨_, mem_insert_self _ _, mem_filter.2 ⟨hk, rfl⟩⟩
    · exact ⟨_, mem_insert_of_mem (mem_singleton_self _), mem_filter.2 ⟨hk, rfl⟩⟩
  proper := by
    intro b hb h
    rcases mem_insert.1 hb with rfl | hb
    · exact absurd (show ({1} : Finset (Fin 2)) = univ from h) (by decide)
    · rw [mem_singleton.1 hb] at h
      exact absurd (show ({0} : Finset (Fin 2)) = univ from h) (by decide)

lemma exPart_effPart {Z : Finset (Fin 2)} {k : Fin 2} (hk : k ∈ Z) :
    (exPart Z).effPart k = {k + 1} := by
  fin_cases k
  · rw [(exPart Z).effPart_eq (mem_insert_self _ _) (mem_filter.2 ⟨hk, rfl⟩)]; rfl
  · rw [(exPart Z).effPart_eq (mem_insert_of_mem (mem_singleton_self _))
      (mem_filter.2 ⟨hk, rfl⟩)]; rfl

lemma effUnit_exPart (k : Fin 2) (x : Bool) :
    effUnit exTPM {k + 1} exState k x = effUnit exTPM univ exState k x := by
  rw [effUnit_eq_sum, effUnit_eq_sum, sum_state2, sum_state2]
  fin_cases k <;> cases x <;>
    norm_num [ex_prob, exNext, exState, Fin.forall_fin_two, fin_one_add_one]

lemma phiEofPartition_exPart (Z : Finset (Fin 2)) (z : State 2) :
    phiEofPartition exTPM univ exState Z z (exPart Z) = 0 := by
  have hP : partEffRep exTPM univ exState Z z (exPart Z) = effRep exTPM univ exState Z z :=
    prod_congr rfl fun k hk => by rw [exPart_effPart hk, effUnit_exPart]
  rw [phiEofPartition, hP]
  rcases eq_or_ne (effRep exTPM univ exState Z z) 0 with h | h
  · rw [h, zero_mul]
  · rw [div_self h, Real.logb_one]; simp [pos]

/-- If some partition leaves no integrated effect information, the MIP value is `0`. -/
lemma phiEat_eq_zero_of_partition {N : ℕ} {T : UnitTPM N} {M Z : Finset (Fin N)}
    {m z : State N} (hZ : Z.Nonempty) (θ0 : Partition N M Z)
    (h0 : phiEofPartition T M m Z z θ0 = 0) : phiEat T M m Z z = 0 := by
  refine le_antisymm (sup'OrZero_le le_rfl fun θ hθ => ?_) (phiEat_nonneg T M m Z z)
  have hmin := mem_argminSet.1 hθ θ0
  have hc : (0 : ℝ) < cutCount M Z θ := by exact_mod_cast cutCount_pos hZ θ
  rw [normalizedPhi, normalizedPhi, h0, zero_div, div_le_iff₀ hc, zero_mul] at hmin
  exact hmin

lemma ex_phiEmech_univ : phiEmech exTPM univ univ exState ≤ 0 := by
  refine Finset.sup'_le _ _ fun Z _ => Finset.sup'_le _ _ fun z _ => ?_
  rcases Z.eq_empty_or_nonempty with rfl | hZ
  · rw [phiEat_empty_purview]
  · rw [phiEat_eq_zero_of_partition hZ (exPart Z) (phiEofPartition_exPart Z z)]

lemma not_isDistinctionMech_univ : ¬ IsDistinctionMech exTPM univ exState exState univ := by
  rintro ⟨hpos, -⟩
  have := (phiD_le_phiEmech exTPM univ univ exState).trans ex_phiEmech_univ
  linarith

/-! ### The mechanisms `{A}` and `{B}`: incongruent -/

instance exFactSingleton (a : Fin 2) : Fact (({a} : Finset (Fin 2)).Nonempty) :=
  ⟨singleton_nonempty a⟩

lemma effPart_single {a : Fin 2} {Z : Finset (Fin 2)} (θ : Partition 2 {a} Z) {k : Fin 2}
    (hk : k ∈ Z) : θ.effPart k = ∅ := by
  rcases Finset.subset_singleton_iff.1 (θ.effPart_subset k) with h | h
  · exact h
  · exact absurd h (θ.effPart_ne hk)

/-- A one-unit mechanism has a single effect-side cut: every purview unit is marginalized. -/
lemma phiEat_single (a : Fin 2) (Z : Finset (Fin 2)) (z : State 2) :
    phiEat exTPM {a} exState Z z =
      effRep exTPM {a} exState Z z * pos (Real.logb 2 (effRep exTPM {a} exState Z z /
        ∏ k ∈ Z, effUnit exTPM ∅ exState k (z k))) := by
  have hC : ∀ θ : Partition 2 {a} Z, phiEofPartition exTPM {a} exState Z z θ =
      effRep exTPM {a} exState Z z * pos (Real.logb 2 (effRep exTPM {a} exState Z z /
        ∏ k ∈ Z, effUnit exTPM ∅ exState k (z k))) := fun θ => by
    rw [phiEofPartition, partEffRep, prod_congr rfl fun k hk => by rw [effPart_single θ hk]]
  obtain ⟨θ0, hθ0⟩ := argminSet_nonempty (normalizedPhi exTPM {a} exState Z z)
  refine le_antisymm (sup'OrZero_le ?_ fun θ _ => (hC θ).le) ?_
  · rw [← hC θ0]; exact phiEofPartition_nonneg _ _ _ _ _ θ0
  · rw [← hC θ0]; exact le_sup'OrZero hθ0

lemma effUnit_single_exState (a k : Fin 2) :
    effUnit exTPM {a} exState k false = if k = a then 1 / 2 else 1 := by
  rw [effUnit_eq_sum, sum_state2]
  fin_cases a <;> fin_cases k <;> norm_num [ex_prob, exNext, exState]

lemma effUnit_single_self_true (a : Fin 2) : effUnit exTPM {a} exState a true = 1 / 2 := by
  rw [effUnit_eq_sum, sum_state2]
  fin_cases a <;> norm_num [ex_prob, exNext, exState]

lemma effUnit_empty_exState (k : Fin 2) (x : Bool) :
    effUnit exTPM ∅ exState k x = if x then 1 / 4 else 3 / 4 := by
  rw [effUnit_eq_sum, sum_state2]
  fin_cases k <;> cases x <;> norm_num [ex_prob, exNext]

lemma ex_uncEffRep (a : Fin 2) (w : State 2) :
    uncEffRep exTPM {a} {a} w = if w a then 1 / 4 else 3 / 4 := by
  rw [uncEffRep, card_state]
  simp only [effRep, prod_singleton]
  rw [sum_state2]
  simp only [effUnit_eq_sum, sum_state2]
  generalize w a = x
  fin_cases a <;> cases x <;> norm_num [ex_prob, exNext]

/-- The witness effect state: `a` on, the other unit off. -/
def exW (a : Fin 2) : State 2 := fun i => decide (i = a)

lemma exW_self (a : Fin 2) : exW a a = true := by simp [exW]

lemma ex_iiE (a : Fin 2) (w : State 2) :
    iiE exTPM {a} exState {a} w =
      1 / 2 * Real.logb 2 (1 / 2 / (if w a then 1 / 4 else 3 / 4)) := by
  have h : effRep exTPM {a} exState {a} w = 1 / 2 := by
    rw [effRep, prod_singleton]
    cases hw : w a
    · rw [effUnit_single_exState]; simp
    · exact effUnit_single_self_true a
  rw [iiE, ex_uncEffRep, h]

lemma exW_mem_maxEffStates (a : Fin 2) : exW a ∈ maxEffStates exTPM {a} exState {a} := by
  rw [maxEffStates, mem_argmaxSet]
  intro w
  have hW : iiE exTPM {a} exState {a} (exW a) = 1 / 2 := by
    rw [ex_iiE, exW_self]; norm_num [logb_two_two]
  rw [hW, ex_iiE]
  cases w a
  · have := Real.logb_nonpos one_lt_two (x := 1 / 2 / (3 / 4)) (by norm_num) (by norm_num)
    simp only [Bool.false_eq_true, ite_false]
    linarith
  · simp only [ite_true]; norm_num [logb_two_two]

lemma ex_phiEat_witness (a : Fin 2) : phiEat exTPM {a} exState {a} (exW a) = 1 / 2 := by
  rw [phiEat_single, effRep, prod_singleton, prod_singleton, exW_self,
    effUnit_single_self_true, effUnit_empty_exState]
  norm_num [logb_two_two, pos]

lemma ex_phiEmech_single_ge (a : Fin 2) : 1 / 2 ≤ phiEmech exTPM univ {a} exState := by
  calc (1 / 2 : ℝ) = phiEat exTPM {a} exState {a} (exW a) := (ex_phiEat_witness a).symm
    _ ≤ phiEpurview exTPM {a} exState {a} :=
        Finset.le_sup' (f := fun z => phiEat exTPM {a} exState {a} z) (exW_mem_maxEffStates a)
    _ ≤ phiEmech exTPM univ {a} exState :=
        Finset.le_sup' (f := fun Z => phiEpurview exTPM {a} exState Z)
          (mem_powerset.2 (subset_univ _))

lemma max_logb_two_thirds : max 0 (Real.logb 2 (2 / 3)) = 0 :=
  pos_logb_eq_zero (by norm_num) (by norm_num)

lemma max_logb_eight_ninths : max 0 (Real.logb 2 (8 / 9)) = 0 :=
  pos_logb_eq_zero (by norm_num) (by norm_num)

lemma max_logb_four_thirds : max 0 (Real.logb 2 (4 / 3)) = Real.logb 2 (4 / 3) :=
  max_eq_right logb_four_thirds_pos.le

/-- Every effect purview congruent with the all-off system effect state reaches at most
`log₂(4/3)`. -/
lemma ex_phiEat_congruent (a : Fin 2) (Z : Finset (Fin 2)) (z : State 2)
    (hz : ∀ k ∈ Z, z k = false) : phiEat exTPM {a} exState Z z ≤ Real.logb 2 (4 / 3) := by
  rw [phiEat_congr_of_agree (z' := exState) hz, phiEat_single, effRep]
  have key : ∀ Z : Finset (Fin 2), Z = ∅ ∨ Z = {0} ∨ Z = {1} ∨ Z = univ := by decide
  have hl := logb_four_thirds_pos
  have e : ∀ k : Fin 2, exState k = false := fun _ => rfl
  rcases key Z with rfl | rfl | rfl | rfl <;>
    simp only [prod_empty, prod_singleton, Fin.prod_univ_two, e, effUnit_single_exState,
      effUnit_empty_exState] <;>
    fin_cases a <;>
    norm_num [pos, max_logb_two_thirds, max_logb_eight_ninths, max_logb_four_thirds, hl.le]

lemma not_isDistinctionMech_single (a : Fin 2) :
    ¬ IsDistinctionMech exTPM univ exState exState {a} := by
  rintro ⟨-, pc, -, pe, hpe, -, e, he, hsub⟩
  obtain ⟨te, hte, rfl⟩ := mem_image.1 he
  rw [mem_ex_sysMaxEffStates] at hte
  subst hte
  have hz : ∀ k ∈ pe.1, pe.2 k = false := fun k hk => by
    have h := hsub ((mem_stated (p := (k, pe.2 k))).2 ⟨hk, rfl⟩)
    exact (mem_stated.1 h).2
  have h1 := phiEat_of_mem_maxEffPurviews exTPM univ {a} exState hpe
  have h2 := ex_phiEmech_single_ge a
  have h3 := ex_phiEat_congruent a pe.1 pe.2 hz
  linarith [logb_four_thirds_lt]

/-! ### No distinction, hence `Φ = 0` -/

lemma ex_distinctionMechs : distinctionMechs exTPM univ exState exState = ∅ := by
  refine eq_empty_of_forall_notMem fun M hM => ?_
  have hD := (mem_distinctionMechs.1 hM).2
  have key : ∀ M : Finset (Fin 2), M = ∅ ∨ M = {0} ∨ M = {1} ∨ M = univ := by decide
  rcases key M with rfl | rfl | rfl | rfl
  · exact empty_not_mem_distinctionMechs exTPM univ exState exState hM
  · exact not_isDistinctionMech_single 0 hD
  · exact not_isDistinctionMech_single 1 hD
  · exact not_isDistinctionMech_univ hD

lemma ex_distinctions (σ : Selector exTPM univ exState exState) :
    distinctions exTPM univ exState exState σ = ∅ := by
  classical
  refine eq_empty_of_forall_notMem fun d hd => ?_
  obtain ⟨⟨M, hM⟩, -, -⟩ := mem_image.1 hd
  rw [ex_distinctionMechs] at hM
  exact notMem_empty M hM

lemma ex_PhiOf (σ : Selector exTPM univ exState exState) :
    PhiOf exTPM univ exState exState σ = 0 := by
  have hD := ex_distinctions σ
  have hR : relationSets exTPM univ exState exState σ = ∅ := by
    rw [relationSets, hD, powerset_empty]; simp
  have hS : selfRelationDistinctions exTPM univ exState exState σ = ∅ := by
    rw [selfRelationDistinctions, hD, filter_empty]
  rw [PhiOf, hD, hR, hS]; simp

lemma ex_PhiMax : PhiMax exTPM univ exState exState = 0 :=
  le_antisymm (PhiMax_le_of_forall _ _ _ _ le_rfl fun σ => (ex_PhiOf σ).le)
    (sup'OrZero_nonneg fun σ _ => PhiOf_nonneg _ _ _ _ σ)

/-- **A complex with `φ_s > 0` and `Φ = 0`.**  For the two-unit system `A' = ¬A ∧ B`,
`B' = ¬B ∧ A` in the all-off state, the whole substrate is a complex (`[IIT4, Eq 26]`) with
positive system integrated information, yet it specifies no distinction, so its structure
integrated information vanishes for every tie-break. -/
theorem complex_phiS_pos_Phi_zero :
    IsComplex exTPM exState univ univ exState ∧ 0 < sysPhi exTPM univ exState exState ∧
      PhiMax exTPM univ exState exState = 0 :=
  ⟨isComplex_univ_of_pos ex_sysPhi_pos, ex_sysPhi_pos, ex_PhiMax⟩

end Census
end IIT
