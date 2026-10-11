/-
Census: the effect side of a two-unit candidate system `S = {a, b}`, and `φ_s > 0`.

With background pinned at the current state `s`, the effect side only sees the four rows
of the `S`-block of `s`.  If both units are nearly ON at `s` and near-coin-flips on the
other three block rows (`effBox`), the maximal effect state is ON at `a` and `b`, and every
partition strictly lowers its probability, so `φ_e > 0`.  Combined with `sysPhiC_pair_pos`
this gives `φ_s({a, b}) > 0`.
-/
import IIT.Census.PairCause

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- The effect-side box: both units nearly ON at `s`, near `1/2` on the other block rows. -/
def effBox (z : Param N) (s : State N) (a b : Fin N) : Prop :=
  z s a ∈ Set.Ioo (99/100 : ℝ) 1 ∧ z s b ∈ Set.Ioo (99/100 : ℝ) 1 ∧
  ∀ r ∈ ({flip s a, flip s b, flip (flip s a) b} : Finset (State N)),
    z r a ∈ Set.Ioo (9/20 : ℝ) (11/20) ∧ z r b ∈ Set.Ioo (9/20 : ℝ) (11/20)

/-! ### Basic rewriting -/

lemma prob_of_mem {z : Param N} (hz : z ∈ openCube N) (r : State N) (i : Fin N) (x : Bool) :
    (tpmOf z).prob i r x = if x then z r i else 1 - z r i := by
  have h := hz r i
  have hc : clamp01 (z r i) = z r i := by
    unfold clamp01; rw [min_eq_right h.2.le, max_eq_right h.1.le]
  simp only [tpmOf, hc]

lemma flip_self (t : State N) (k : Fin N) : flip t k k = !t k := by simp [flip]

lemma flip_ne_apply (t : State N) {k j : Fin N} (h : j ≠ k) : flip t k j = t j := by
  simp [flip, Function.update_of_ne h]

lemma merge_self (S : Finset (Fin N)) (s : State N) : merge S s s = s := by
  funext j; unfold merge; split_ifs <;> rfl

/-! ### The four rows of the block -/

lemma mem_block {a b : Fin N} (hab : a ≠ b) {s v : State N} (hv : v ∈ agree ({a, b}ᶜ) s) :
    v = s ∨ v = flip s a ∨ v = flip s b ∨ v = flip (flip s a) b := by
  rw [mem_agree] at hv
  have hv' : ∀ j, j ≠ a → j ≠ b → v j = s j := fun j h1 h2 => hv j (by simp [h1, h2])
  have key : ∀ x y : Bool, x ≠ y → x = !y := by decide
  have hba : b ≠ a := hab.symm
  by_cases ha : v a = s a <;> by_cases hb : v b = s b
  · left; funext j
    by_cases hja : j = a
    · rw [hja]; exact ha
    by_cases hjb : j = b
    · rw [hjb]; exact hb
    exact hv' j hja hjb
  · right; right; left; funext j
    by_cases hja : j = a
    · rw [hja, flip_ne_apply _ hab]; exact ha
    by_cases hjb : j = b
    · rw [hjb, flip_self]; exact key _ _ hb
    rw [flip_ne_apply _ hjb]; exact hv' j hja hjb
  · right; left; funext j
    by_cases hja : j = a
    · rw [hja, flip_self]; exact key _ _ ha
    by_cases hjb : j = b
    · rw [hjb, flip_ne_apply _ hba]; exact hb
    rw [flip_ne_apply _ hja]; exact hv' j hja hjb
  · right; right; right; funext j
    by_cases hja : j = a
    · rw [hja, flip_ne_apply _ hab, flip_self]; exact key _ _ ha
    by_cases hjb : j = b
    · rw [hjb, flip_self, flip_ne_apply _ hba]; exact key _ _ hb
    rw [flip_ne_apply _ hjb, flip_ne_apply _ hja]; exact hv' j hja hjb

lemma agree_pair {a b : Fin N} (hab : a ≠ b) (s : State N) :
    agree ({a, b}ᶜ) s = {s, flip s a, flip s b, flip (flip s a) b} := by
  ext v
  constructor
  · intro hv
    rcases mem_block hab hv with h | h | h | h <;> simp [h]
  · simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl | rfl | rfl) <;> rw [mem_agree] <;> intro j hj <;>
      simp only [mem_compl, mem_insert, mem_singleton, not_or] at hj <;>
      simp [flip, Function.update_apply, hj.1, hj.2]

lemma sum_block {a b : Fin N} (hab : a ≠ b) (s : State N) (f : State N → ℝ) :
    ∑ v ∈ agree ({a, b}ᶜ) s, f v =
      f s + f (flip s a) + f (flip s b) + f (flip (flip s a) b) := by
  have atA : ∀ x y : State N, x a ≠ y a → x ≠ y := fun x y h e => h (congrFun e a)
  have d1 : s ≠ flip s a := flip_ne s a
  have d2 : s ≠ flip s b := flip_ne s b
  have d3 : s ≠ flip (flip s a) b := atA _ _ (by simp [flip_ne_apply _ hab, flip_self])
  have d4 : flip s a ≠ flip s b := atA _ _ (by simp [flip_ne_apply _ hab, flip_self])
  have d5 : flip s a ≠ flip (flip s a) b := flip_ne _ b
  have d6 : flip s b ≠ flip (flip s a) b := atA _ _ (by simp [flip_ne_apply _ hab, flip_self])
  rw [agree_pair hab, sum_insert (by simp [d1, d2, d3]), sum_insert (by simp [d4, d5]),
    sum_pair d6]
  ring

lemma two_le_of_ne {a b : Fin N} (hab : a ≠ b) : 2 ≤ N := by
  have := Finset.card_le_univ ({a, b} : Finset (Fin N))
  rwa [card_pair hab, Fintype.card_fin] at this

/-- Four times the unconstrained effect probability is the sum over the four block rows. -/
lemma unc_pair (T : UnitTPM N) {a b : Fin N} (hab : a ≠ b) (s t : State N) :
    4 * sysUncEff T {a, b} s t =
      T.prob a s (t a) * T.prob b s (t b) +
      T.prob a (flip s a) (t a) * T.prob b (flip s a) (t b) +
      T.prob a (flip s b) (t a) * T.prob b (flip s b) (t b) +
      T.prob a (flip (flip s a) b) (t a) * T.prob b (flip (flip s a) b) (t b) := by
  unfold sysUncEff avgOverStates sysEffProb
  rw [sum_merge_eq {a, b} s (fun v => ∏ i ∈ ({a, b} : Finset (Fin N)), T.prob i v (t i)),
    sum_block hab, card_pair hab]
  simp only [prod_pair hab]
  have hp : (2 : ℝ) ^ N = 2 ^ (N - 2) * 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel (two_le_of_ne hab)]
  rw [hp]
  field_simp

lemma eff_pair (T : UnitTPM N) {a b : Fin N} (hab : a ≠ b) (s t : State N) :
    sysEffProb T {a, b} s s t = T.prob a s (t a) * T.prob b s (t b) := by
  rw [sysEffProb, merge_self, prod_pair hab]

/-! ### The maximal effect state is ON at `a` and `b` -/

lemma te_true (z : Param N) (hz : z ∈ openCube N) (s : State N) {a b : Fin N} (hab : a ≠ b)
    (hbox : effBox z s a b) :
    ∀ te ∈ sysMaxEffStates (tpmOf z) {a, b} s s, te a = true ∧ te b = true := by
  obtain ⟨⟨hsa, -⟩, ⟨hsb, -⟩, hr⟩ := hbox
  have r1 := hr (flip s a) (by simp)
  have r2 := hr (flip s b) (by simp)
  have r3 := hr (flip (flip s a) b) (by simp)
  have hP := prob_of_mem hz
  have z01 := fun r i => hz r i
  -- rows of the box: every factor lies in `(9/20, 11/20)`
  have box : ∀ r, (z r a ∈ Set.Ioo (9/20 : ℝ) (11/20) ∧ z r b ∈ Set.Ioo (9/20 : ℝ) (11/20)) →
      ∀ x y : Bool, 81/400 < (tpmOf z).prob a r x * (tpmOf z).prob b r y ∧
        (tpmOf z).prob a r x * (tpmOf z).prob b r y < 121/400 := by
    rintro r ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ x y
    rw [hP, hP]
    cases x <;> cases y <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> nlinarith
  have hsa1 := z01 s a
  have hsb1 := z01 s b
  have iiE : ∀ t, sysIiE (tpmOf z) {a, b} s s t =
      (tpmOf z).prob a s (t a) * (tpmOf z).prob b s (t b) *
        Real.logb 2 ((tpmOf z).prob a s (t a) * (tpmOf z).prob b s (t b) /
          sysUncEff (tpmOf z) {a, b} s t) := by
    intro t; rw [sysIiE, eff_pair _ hab]
  -- the all-ON state has positive `ii_e`
  have hpos : 0 < sysIiE (tpmOf z) {a, b} s s (fun _ => true) := by
    have hu := unc_pair (tpmOf z) hab s (fun _ => true)
    have b1 := box _ r1 true true
    have b2 := box _ r2 true true
    have b3 := box _ r3 true true
    rw [iiE]
    simp only [hP, ↓reduceIte] at hu b1 b2 b3 ⊢
    have he : 9801/10000 < z s a * z s b := by nlinarith
    have hu0 : 0 < sysUncEff (tpmOf z) {a, b} s (fun _ => true) := by nlinarith
    refine mul_pos (by nlinarith) (Real.logb_pos one_lt_two ?_)
    rw [one_lt_div hu0]; nlinarith
  intro te hte
  have hmax := (mem_argmaxSet.1 hte) (fun _ => true)
  by_contra hne
  have hle : sysIiE (tpmOf z) {a, b} s s te ≤ 0 := by
    have hu := unc_pair (tpmOf z) hab s te
    have b1 := box _ r1 (te a) (te b)
    have b2 := box _ r2 (te a) (te b)
    have b3 := box _ r3 (te a) (te b)
    have e0 : 0 ≤ (tpmOf z).prob a s (te a) * (tpmOf z).prob b s (te b) :=
      mul_nonneg ((tpmOf z).nonneg _ _ _) ((tpmOf z).nonneg _ _ _)
    have e1 : (tpmOf z).prob a s (te a) * (tpmOf z).prob b s (te b) < 1/100 := by
      have la := (tpmOf z).le_one a s (te a)
      have lb := (tpmOf z).le_one b s (te b)
      have na := (tpmOf z).nonneg a s (te a)
      have nb := (tpmOf z).nonneg b s (te b)
      rcases Bool.eq_false_or_eq_true (te a) with ha | ha <;>
        rcases Bool.eq_false_or_eq_true (te b) with hb | hb
      · exact absurd ⟨ha, hb⟩ hne
      · rw [hb] at lb nb ⊢; rw [hP s b false] at lb nb ⊢
        simp only [Bool.false_eq_true, ↓reduceIte] at lb nb ⊢; nlinarith
      · rw [ha] at la na ⊢; rw [hP s a false] at la na ⊢
        simp only [Bool.false_eq_true, ↓reduceIte] at la na ⊢; nlinarith
      · rw [ha] at la na ⊢; rw [hP s a false] at la na ⊢
        simp only [Bool.false_eq_true, ↓reduceIte] at la na ⊢; nlinarith
    have hu0 : 0 < sysUncEff (tpmOf z) {a, b} s te := by nlinarith
    rw [iiE]
    refine mul_nonpos_of_nonneg_of_nonpos e0 (Real.logb_nonpos one_lt_two
      (div_nonneg e0 hu0.le) ((div_le_one hu0).2 ?_))
    nlinarith
  linarith

/-! ### One factor of the partitioned effect probability -/

lemma effFactor_bound {z : Param N} (hz : z ∈ openCube N) (s : State N) (M : Finset (Fin N))
    {i k : Fin N} (hM : M = ∅ ∨ M = {k}) (hlt : z (flip s k) i < z s i) :
    0 < effUnit (tpmOf z) Mᶜ s i true ∧ effUnit (tpmOf z) Mᶜ s i true ≤ z s i ∧
      (M.Nonempty → effUnit (tpmOf z) Mᶜ s i true < z s i) := by
  have h1 := hz s i
  have h2 := hz (flip s k) i
  rcases hM with rfl | rfl
  · rw [compl_empty, effUnit_univ_prob, prob_of_mem hz]
    exact ⟨h1.1, le_rfl, fun h => absurd h (by simp)⟩
  · rw [effUnit_compl_single, prob_of_mem hz, prob_of_mem hz]
    simp only [↓reduceIte]
    refine ⟨by linarith [h1.1, h2.1], by linarith, fun _ => by linarith⟩

/-! ### `φ_e > 0` at every partition -/

theorem sysPhiE_pair_pos (z : Param N) (hz : z ∈ openCube N) (s : State N) {a b : Fin N}
    (hab : a ≠ b) (hbox : effBox z s a b) :
    ∀ te ∈ sysMaxEffStates (tpmOf z) {a, b} s s, ∀ θ : SysPartition N {a, b},
      0 < sysPhiE (tpmOf z) {a, b} s θ s te := by
  intro te hte θ
  obtain ⟨hta, htb⟩ := te_true z hz s hab hbox te hte
  obtain ⟨⟨hsa, -⟩, ⟨hsb, -⟩, hr⟩ := hbox
  have ra := (hr (flip s b) (by simp)).1
  have rb := (hr (flip s a) (by simp)).2
  have haS : a ∈ ({a, b} : Finset (Fin N)) := mem_insert_self _ _
  have hbS : b ∈ ({a, b} : Finset (Fin N)) := mem_insert_of_mem (mem_singleton_self _)
  have hea : ({a, b} : Finset (Fin N)).erase a ⊆ {b} := by
    intro x hx; simp only [mem_erase, mem_insert, mem_singleton] at hx ⊢; tauto
  have heb : ({a, b} : Finset (Fin N)).erase b ⊆ {a} := by
    intro x hx; simp only [mem_erase, mem_insert, mem_singleton] at hx ⊢; tauto
  obtain ⟨pa, la, sa⟩ := effFactor_bound hz s _ (cut_cases_pair θ hea haS)
    (show z (flip s b) a < z s a by linarith [ra.2])
  obtain ⟨pb, lb, sb⟩ := effFactor_bound hz s _ (cut_cases_pair θ heb hbS)
    (show z (flip s a) b < z s b by linarith [rb.2])
  have hE : sysEffProb (tpmOf z) {a, b} s s te = z s a * z s b := by
    rw [eff_pair _ hab, hta, htb, prob_of_mem hz, prob_of_mem hz]; simp
  have hP : sysPartEffProb (tpmOf z) {a, b} s θ s te =
      effUnit (tpmOf z) (θ.cutSet (θ.partOf a))ᶜ s a true *
        effUnit (tpmOf z) (θ.cutSet (θ.partOf b))ᶜ s b true := by
    rw [sysPartEffProb, merge_self, prod_pair hab, hta, htb]
  have hlt : sysPartEffProb (tpmOf z) {a, b} s θ s te < sysEffProb (tpmOf z) {a, b} s s te := by
    rw [hE, hP]
    rcases exists_cut_pair θ with hc | hc
    · calc _ < z s a * _ := mul_lt_mul_of_pos_right (sa hc) pb
        _ ≤ _ := mul_le_mul_of_nonneg_left lb (by linarith)
    · calc _ < _ * z s b := mul_lt_mul_of_pos_left (sb hc) pa
        _ ≤ _ := mul_le_mul_of_nonneg_right la (by linarith)
  have hP0 : 0 < sysPartEffProb (tpmOf z) {a, b} s θ s te := by rw [hP]; exact mul_pos pa pb
  have hlog : 0 < Real.logb 2 (sysEffProb (tpmOf z) {a, b} s s te /
      sysPartEffProb (tpmOf z) {a, b} s θ s te) :=
    Real.logb_pos one_lt_two ((one_lt_div hP0).2 hlt)
  unfold sysPhiE
  refine mul_pos (hP0.trans hlt) ?_
  rw [pos]; exact lt_max_of_lt_right hlog

/-! ### `φ_s > 0` -/

theorem phi_pair_pos (z : Param N) (hz : z ∈ openCube N) (s : State N) {a b : Fin N}
    (hab : a ≠ b) (hbox : effBox z s a b)
    (hU : ∀ tc : State N, (∀ t, U z s {a, b} a t * U z s {a, b} b t ≤
        U z s {a, b} a tc * U z s {a, b} b tc) →
      U z s {a, b} a (flip tc b) < U z s {a, b} a tc ∧
        U z s {a, b} b (flip tc a) < U z s {a, b} b tc) :
    0 < phi z s {a, b} := by
  obtain ⟨tc, htc⟩ := sysMaxCauseStates_nonempty (tpmOf z) {a, b} s s
  obtain ⟨te, hte⟩ := sysMaxEffStates_nonempty (tpmOf z) {a, b} s s
  have hpos : ∀ θ, 0 < sysPhiAt (tpmOf z) {a, b} s θ s tc te := fun θ =>
    lt_min (sysPhiC_pair_pos z hz s hab hU tc htc θ) (sysPhiE_pair_pos z hz s hab hbox te hte θ)
  have hS : (({a, b} : Finset (Fin N)).erase a).Nonempty :=
    ⟨b, mem_erase.2 ⟨hab.symm, by simp⟩⟩
  have : Nonempty (SysPartition N {a, b}) := ⟨splitAt (mem_insert_self a {b}) hS⟩
  obtain ⟨θ, hθ⟩ :=
    argminSet_nonempty (fun θ => normalizedSysPhiAt (tpmOf z) {a, b} s θ s tc te)
  have h1 : 0 < sysPhiOfState (tpmOf z) {a, b} s s tc te := by
    unfold sysPhiOfState sysMipSetAt
    exact (hpos θ).trans_le (le_sup'OrZero (f := fun θ => sysPhiAt (tpmOf z) {a, b} s θ s tc te) hθ)
  unfold phi
  exact h1.trans_le (sysPhiOfState_le_sysPhi _ _ _ _ htc hte)

end Census
end IIT
