/-
Census: the effect side of a three-unit system in the effect box.

If the three units of `S` are nearly ON at the current state `s` (entries in `(99/100, 1)`) and
nearly OFF on the other seven rows of the `S`-block of `s` (entries in `(0, 1/100)`), then every
maximal effect state is ON on `S` (`tp_te_true`), and every partition of `S` has effect side at
least `2/5` at such a state (`tp_eff`).
-/
import IIT.Census.Profile

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- The effect box of a system `S` at the current state `s`, for the unflipped parameters. -/
def tp_effBoxZ (z : Param N) (s : State N) (S : Finset (Fin N)) : Prop :=
  (∀ j ∈ S, 99 / 100 < z s j) ∧ ∀ r ∈ agree Sᶜ s, r ≠ s → ∀ j ∈ S, z r j < 1 / 100

lemma tp_logb_lower {p q x : ℝ} (hp : 0 < p) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (h : p ≤ (1 - x) * q) : x ≤ Real.logb 2 (q / p) := by
  have h1x : 0 < 1 - x := by linarith
  have hy : 1 / (1 - x) ≤ q / p := by
    rw [div_le_div_iff₀ h1x hp]; nlinarith
  have hl1 : x ≤ Real.log (1 / (1 - x)) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_sub_one_of_pos h1x
    linarith
  have hl2 : Real.log (1 / (1 - x)) ≤ Real.log (q / p) :=
    Real.log_le_log (by positivity) hy
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; norm_num at this; linarith
  rw [Real.logb, le_div_iff₀ hlog2]
  nlinarith

lemma tp_card_le (S : Finset (Fin N)) : S.card ≤ N := by
  simpa using card_le_univ S

lemma tp_card_block (s : State N) (S : Finset (Fin N)) : (agree Sᶜ s).card = 2 ^ S.card := by
  rw [card_agree, card_compl, Fintype.card_fin, Nat.sub_sub_self (tp_card_le S)]

lemma tp_mem_block (s : State N) (S : Finset (Fin N)) : s ∈ agree Sᶜ s := self_mem_agree _ _

/-- The unconstrained effect probability is the average over the `S`-block of `s`. -/
lemma tp_unc_eq (T : UnitTPM N) (S : Finset (Fin N)) (s t : State N) :
    sysUncEff T S s t = (∑ r ∈ agree Sᶜ s, ∏ j ∈ S, T.prob j r (t j)) / 2 ^ S.card := by
  unfold sysUncEff avgOverStates sysEffProb
  rw [sum_merge_eq S s (fun v => ∏ j ∈ S, T.prob j v (t j))]
  have hS := tp_card_le S
  rw [show (2 : ℝ) ^ N = 2 ^ (N - S.card) * 2 ^ S.card by
    rw [← pow_add, Nat.sub_add_cancel hS]]
  field_simp

lemma tp_eff_eq (T : UnitTPM N) (S : Finset (Fin N)) (s t : State N) :
    sysEffProb T S s s t = ∏ j ∈ S, T.prob j s (t j) := by
  rw [sysEffProb, merge_self]

/-- A product of factors in `[0, 1]` is at most any one factor. -/
lemma tp_prod_le_one_factor {S : Finset (Fin N)} {f : Fin N → ℝ} (h0 : ∀ j ∈ S, 0 ≤ f j)
    (h1 : ∀ j ∈ S, f j ≤ 1) {j0 : Fin N} (hj0 : j0 ∈ S) : ∏ j ∈ S, f j ≤ f j0 := by
  rw [← mul_prod_erase S f hj0]
  have hp : ∏ j ∈ S.erase j0, f j ≤ 1 :=
    prod_le_one (fun j hj => h0 j (mem_of_mem_erase hj)) fun j hj => h1 j (mem_of_mem_erase hj)
  have hp0 : 0 ≤ ∏ j ∈ S.erase j0, f j := prod_nonneg fun j hj => h0 j (mem_of_mem_erase hj)
  nlinarith [h0 j0 hj0]

section Box

variable {z : Param N} (hz : z ∈ openCube N) (s : State N) {S : Finset (Fin N)}

include hz

omit hz in
/-- `ii_e ≤ |S| · p_e` at every state: the unconstrained probability is at least `p_e / 2^|S|`. -/
lemma tp_iiE_le (hS : S.card = 3) (t : State N) :
    sysIiE (tpmOf z) S s s t ≤ 3 * sysEffProb (tpmOf z) S s s t := by
  set T := tpmOf z
  set e := sysEffProb T S s s t with he
  have he0 : 0 ≤ e := sysEffProb_nonneg T S s s t
  have hu : e / 8 ≤ sysUncEff T S s t := by
    rw [tp_unc_eq, hS, he, tp_eff_eq]
    have h1 : ∏ j ∈ S, T.prob j s (t j) ≤ ∑ r ∈ agree Sᶜ s, ∏ j ∈ S, T.prob j r (t j) :=
      single_le_sum (f := fun r => ∏ j ∈ S, T.prob j r (t j))
        (fun r _ => prod_nonneg fun j _ => T.nonneg j r (t j)) (tp_mem_block s S)
    norm_num
    linarith
  rcases he0.eq_or_lt with h0 | hpos
  · rw [sysIiE, ← he, ← h0]; simp
  · have hu0 : 0 < sysUncEff T S s t := by linarith [div_pos hpos (by norm_num : (0 : ℝ) < 8)]
    have hr : e / sysUncEff T S s t ≤ 8 := by
      rw [div_le_iff₀ hu0]; linarith
    have hl : Real.logb 2 (e / sysUncEff T S s t) ≤ 3 := by
      have h8 : Real.logb 2 8 = 3 := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one one_lt_two]
        norm_num
      rw [← h8]
      exact Real.logb_le_logb_of_le one_lt_two (div_pos hpos hu0) hr
    rw [sysIiE, ← he]
    nlinarith

/-- **The maximal effect states are ON on `S`.** -/
theorem tp_te_true (hS : S.card = 3) (hbox : tp_effBoxZ z s S) :
    ∀ te ∈ sysMaxEffStates (tpmOf z) S s s, ∀ j ∈ S, te j = true := by
  obtain ⟨h1, h0⟩ := hbox
  set T := tpmOf z
  have hP : ∀ r i x, T.prob i r x = if x then z r i else 1 - z r i := prob_of_mem hz
  set tT : State N := fun _ => true
  -- the all-ON state has `ii_e ≥ 97/100`
  have heT : 97 / 100 ≤ sysEffProb T S s s tT := by
    rw [tp_eff_eq]
    have e1 : ∀ j ∈ S, T.prob j s (tT j) = z s j := fun j _ => by rw [hP]; simp [tT]
    rw [prod_congr rfl e1]
    have := prod_le_prod (s := S) (f := fun _ => (99 / 100 : ℝ)) (g := fun j => z s j)
      (fun _ _ => by norm_num) fun j hj => (h1 j hj).le
    rw [prod_const, hS] at this
    linarith
  have huT : sysUncEff T S s tT ≤ 107 / 800 := by
    rw [tp_unc_eq, hS]
    have hs := sum_erase_add (agree Sᶜ s) (fun r => ∏ j ∈ S, T.prob j r (tT j)) (tp_mem_block s S)
    have hSn : S.Nonempty := by rw [← card_pos, hS]; norm_num
    obtain ⟨j0, hj0⟩ := hSn
    have hrest : ∑ r ∈ (agree Sᶜ s).erase s, ∏ j ∈ S, T.prob j r (tT j) ≤ 7 * (1 / 100) := by
      have hc : ((agree Sᶜ s).erase s).card = 7 := by
        rw [card_erase_of_mem (tp_mem_block s S), tp_card_block, hS]; rfl
      calc ∑ r ∈ (agree Sᶜ s).erase s, ∏ j ∈ S, T.prob j r (tT j)
          ≤ ∑ _r ∈ (agree Sᶜ s).erase s, (1 / 100 : ℝ) := by
            refine sum_le_sum fun r hr => ?_
            have hle := tp_prod_le_one_factor (f := fun j => T.prob j r (tT j))
              (fun j _ => T.nonneg j r _) (fun j _ => T.le_one j r _) hj0
            have := h0 r (mem_of_mem_erase hr) (ne_of_mem_erase hr) j0 hj0
            rw [hP] at hle
            simp only [tT, ↓reduceIte] at hle ⊢
            linarith
        _ = 7 * (1 / 100) := by rw [sum_const, hc]; norm_num
    have hself : ∏ j ∈ S, T.prob j s (tT j) ≤ 1 :=
      prod_le_one (fun j _ => T.nonneg j s _) fun j _ => T.le_one j s _
    rw [← hs]
    norm_num
    linarith
  have hiT : 97 / 100 ≤ sysIiE T S s s tT := by
    have hu0 : 0 < sysUncEff T S s tT := by
      rw [tp_unc_eq]
      refine div_pos ?_ (by positivity)
      refine lt_of_lt_of_le ?_ (single_le_sum (f := fun r => ∏ j ∈ S, T.prob j r (tT j))
        (fun r _ => prod_nonneg fun j _ => T.nonneg j r (tT j)) (tp_mem_block s S))
      have := tp_eff_eq T S s tT
      linarith
    have hr : 2 ≤ sysEffProb T S s s tT / sysUncEff T S s tT := by
      rw [le_div_iff₀ hu0]; linarith
    have hl : 1 ≤ Real.logb 2 (sysEffProb T S s s tT / sysUncEff T S s tT) := by
      rw [← Real.logb_self_eq_one (b := 2) one_lt_two]
      exact Real.logb_le_logb_of_le one_lt_two (by norm_num) hr
    rw [sysIiE]
    nlinarith
  intro te hte j hj
  by_contra hne
  have hf : te j = false := by simpa using hne
  have hmax := (mem_argmaxSet.1 hte) tT
  have he : sysEffProb T S s s te < 1 / 100 := by
    rw [tp_eff_eq]
    have hle := tp_prod_le_one_factor (f := fun i => T.prob i s (te i))
      (fun i _ => T.nonneg i s _) (fun i _ => T.le_one i s _) hj
    rw [hf, hP] at hle
    simp only [Bool.false_eq_true, ↓reduceIte] at hle
    have := h1 j hj
    linarith
  have := tp_iiE_le (z := z) s hS te
  linarith

/-- One factor of the partitioned effect probability. -/
lemma tp_effUnit_bound (hbox : tp_effBoxZ z s S) {j : Fin N} (hj : j ∈ S) {M : Finset (Fin N)}
    (hM : M ⊆ S) :
    0 < effUnit (tpmOf z) Mᶜ s j true ∧ effUnit (tpmOf z) Mᶜ s j true ≤ z s j ∧
      (M.Nonempty → effUnit (tpmOf z) Mᶜ s j true ≤ (z s j + 1 / 100) / 2) := by
  obtain ⟨h1, h0⟩ := hbox
  have hP := prob_of_mem hz
  have hsub : agree Mᶜ s ⊆ agree Sᶜ s := agree_subset_agree (compl_subset_compl.2 hM) s
  have hmem : s ∈ agree Mᶜ s := self_mem_agree _ _
  have hcard : (agree Mᶜ s).card = 2 ^ M.card := tp_card_block s M
  have hc0 : (0 : ℝ) < (agree Mᶜ s).card := by rw [hcard]; positivity
  have hzj := h1 j hj
  have hrow : ∀ r ∈ agree Mᶜ s, r ≠ s → z r j < 1 / 100 := fun r hr hrs =>
    h0 r (hsub hr) hrs j hj
  have hval : effUnit (tpmOf z) Mᶜ s j true = (∑ r ∈ agree Mᶜ s, z r j) / (agree Mᶜ s).card := by
    rw [effUnit]
    congr 1
    exact sum_congr rfl fun r _ => by rw [hP]; simp
  have hsplit := sum_erase_add (agree Mᶜ s) (fun r => z r j) hmem
  have hrest0 : 0 ≤ ∑ r ∈ (agree Mᶜ s).erase s, z r j :=
    sum_nonneg fun r _ => (hz r j).1.le
  have hrest : ∑ r ∈ (agree Mᶜ s).erase s, z r j ≤ ((agree Mᶜ s).card - 1) * (1 / 100) := by
    calc ∑ r ∈ (agree Mᶜ s).erase s, z r j ≤ ∑ _r ∈ (agree Mᶜ s).erase s, (1 / 100 : ℝ) :=
          sum_le_sum fun r hr => (hrow r (mem_of_mem_erase hr) (ne_of_mem_erase hr)).le
      _ = ((agree Mᶜ s).card - 1) * (1 / 100) := by
          rw [sum_const, card_erase_of_mem hmem, nsmul_eq_mul]
          rw [Nat.cast_sub (card_pos.2 ⟨s, hmem⟩)]
          simp
  rw [hval]
  refine ⟨div_pos (by rw [← hsplit]; linarith [(hz s j).1]) hc0, ?_, fun hne => ?_⟩
  · rw [div_le_iff₀ hc0, ← hsplit]
    nlinarith
  · have h2 : (2 : ℝ) ≤ (agree Mᶜ s).card := by
      rw [hcard]
      have : 1 ≤ M.card := card_pos.2 hne
      have : (2 : ℕ) ≤ 2 ^ M.card := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ M.card := Nat.pow_le_pow_right (by norm_num) this
      exact_mod_cast this
    rw [div_le_iff₀ hc0, ← hsplit]
    nlinarith

/-- **Effect side in the box**: some maximal effect state has `φ_e ≥ 2/5` at every partition. -/
theorem tp_eff (hS : S.card = 3) (hbox : tp_effBoxZ z s S) :
    ∃ te ∈ sysMaxEffStates (tpmOf z) S s s, ∀ θ : SysPartition N S,
      2 / 5 ≤ sysPhiE (tpmOf z) S s θ s te := by
  obtain ⟨te, hte⟩ := sysMaxEffStates_nonempty (tpmOf z) S s s
  refine ⟨te, hte, fun θ => ?_⟩
  have htrue := tp_te_true hz s hS hbox te hte
  set T := tpmOf z
  have hP : ∀ r i x, T.prob i r x = if x then z r i else 1 - z r i := prob_of_mem hz
  have h1 := hbox.1
  have he : sysEffProb T S s s te = ∏ j ∈ S, z s j := by
    rw [tp_eff_eq]
    exact prod_congr rfl fun j hj => by rw [hP, htrue j hj]; simp
  have hpe : sysPartEffProb T S s θ s te =
      ∏ j ∈ S, effUnit T (θ.cutSet (θ.partOf j))ᶜ s j true := by
    rw [sysPartEffProb, merge_self]
    exact prod_congr rfl fun j hj => by rw [htrue j hj]
  have hfac := fun j (hj : j ∈ S) =>
    tp_effUnit_bound hz s hbox hj ((cutSet_partOf_subset θ hj).trans (erase_subset j S))
  -- a unit with a nonempty cut
  obtain ⟨p, hp, hne⟩ := θ.exists_cutSet_nonempty
  obtain ⟨j0, hj0p⟩ := θ.parts_nonempty p hp
  have hj0 : j0 ∈ S := θ.parts_subset p hp hj0p
  rw [← θ.partOf_eq hp hj0p] at hne
  have hz0 := h1 j0 hj0
  have hE0 : 97 / 100 ≤ sysEffProb T S s s te := by
    rw [he]
    have := prod_le_prod (s := S) (f := fun _ => (99 / 100 : ℝ)) (g := fun j => z s j)
      (fun _ _ => by norm_num) fun j hj => (h1 j hj).le
    rw [prod_const, hS] at this
    linarith
  have hrest0 : 0 ≤ ∏ j ∈ S.erase j0, z s j :=
    prod_nonneg fun j _ => (hz s j).1.le
  have hpe_le : sysPartEffProb T S s θ s te ≤ (1 - 49 / 100) * sysEffProb T S s s te := by
    rw [hpe, he, ← mul_prod_erase S _ hj0, ← mul_prod_erase S (fun j => z s j) hj0]
    have hA := (hfac j0 hj0).2.2 hne
    have hB : ∏ j ∈ S.erase j0, effUnit T (θ.cutSet (θ.partOf j))ᶜ s j true ≤
        ∏ j ∈ S.erase j0, z s j :=
      prod_le_prod (fun j hj => (hfac j (mem_of_mem_erase hj)).1.le)
        fun j hj => (hfac j (mem_of_mem_erase hj)).2.1
    have hB0 : 0 ≤ ∏ j ∈ S.erase j0, effUnit T (θ.cutSet (θ.partOf j))ᶜ s j true :=
      prod_nonneg fun j hj => (hfac j (mem_of_mem_erase hj)).1.le
    have hA0 := (hfac j0 hj0).1
    calc effUnit T (θ.cutSet (θ.partOf j0))ᶜ s j0 true *
          ∏ j ∈ S.erase j0, effUnit T (θ.cutSet (θ.partOf j))ᶜ s j true
        ≤ ((z s j0 + 1 / 100) / 2) * ∏ j ∈ S.erase j0, z s j :=
          mul_le_mul hA hB hB0 (by linarith)
      _ ≤ (1 - 49 / 100) * (z s j0 * ∏ j ∈ S.erase j0, z s j) := by
          nlinarith
  have hpe0 : 0 < sysPartEffProb T S s θ s te := by
    rw [hpe]
    exact prod_pos fun j hj => (hfac j hj).1
  have hlog := tp_logb_lower hpe0 (by norm_num) (by norm_num) hpe_le
  have hpos : 49 / 100 ≤ pos (Real.logb 2 (sysEffProb T S s s te /
      sysPartEffProb T S s θ s te)) := le_max_of_le_right hlog
  unfold sysPhiE
  calc (2 / 5 : ℝ) ≤ 97 / 100 * (49 / 100) := by norm_num
    _ ≤ _ := mul_le_mul hE0 hpos (by norm_num) (by linarith)

end Box

end Census
end IIT
