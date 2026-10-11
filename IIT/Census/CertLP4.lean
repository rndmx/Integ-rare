/-
Census: the 4-set LP (certificate C15b of B1-W6-certificates, lemma `lp4_bound`; addendum to module
A5 of B1-BLUEPRINT).  Same model and certificate scheme as `CertLP3`, with `k = 4`:

    lp4V C ξ = ∑_i (ξ i 0 - 2^{-|C_i|} ∑_{u ⊆ C_i} ξ i u),     ξ : Fin 4 → Fin 16 → ℝ,

`ξ i 0 = y_i` (row `tc`, column `i`), `ξ i u` = row `tc` flipped on the pattern `u`, column `i`.
The 150 profiles (`profiles4`) are exactly the tables `cd_profOf 4 g δ` of the admissible pairs
(`profiles4_complete`, `profiles4_realized`); a system partition of a 4-set is transported by
`lpTab` (`lpTab_mem4`, `lpTab_cc`, `lpTab_at`, `lpTab_agree4`).

* `lp4_bound` (149 kernel-checked rational dual certificates, `CertLP4Data`): a non-all-cut profile
  that minimises `lp4V / cc` up to `e` on the box `ξ ∈ [0,1]^64` has `lp4V ≤ 11/4 + (165/4) e`
  (the maximal dual `Λ` is exactly `165/4`).  `lp4_bound_sys` is the statement for system
  partitions of a 4-set.
* The all-cut profile (cc 12) is excluded; `allCut_mip_tie` of `CertLP3` covers it (any `S`).
-/
import IIT.Census.CertLP4Data
import IIT.Census.CertLP3

namespace IIT
namespace Census

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-! ### The linear model -/

/-- The value of the profile `C` in the linear model. -/
noncomputable def lp4V (C : List (List Bool)) (ξ : Fin 4 → Fin 16 → ℝ) : ℝ :=
  ∑ i : Fin 4, (ξ i 0 - ((2 : ℝ) ^ cd_card 4 C i)⁻¹ *
    ∑ u : Fin 16, if cd_agree 4 (cd_at C i) u 0 = true then ξ i u else 0)

/-- The linear form with integer coefficients `a (u + 16 i)`. -/
noncomputable def lp4Lin (a : ℕ → ℤ) (ξ : Fin 4 → Fin 16 → ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ u : Fin 16, (a (u + 16 * i) : ℝ) * ξ i u

/-- `∑_{q < 64} f q` as a double sum over units and patterns (kernel friendly). -/
def lp4Sum (f : ℕ → ℤ) : ℤ := cd_nsum 4 fun i => cd_nsum 16 fun u => f (u + 16 * i)

lemma lp4Sum_cast (f : ℕ → ℤ) :
    (lp4Sum f : ℝ) = ∑ i : Fin 4, ∑ u : Fin 16, (f (u + 16 * i) : ℝ) := by
  have h : ∀ i : ℕ, (((cd_nsum 16 fun u => f (u + 16 * i)) : ℤ) : ℝ)
      = ∑ u : Fin 16, (f (u + 16 * i) : ℝ) := by
    intro i
    rw [cd_nsum_eq]
    push_cast
    exact (Fin.sum_univ_eq_sum_range (fun u => (f (u + 16 * i) : ℝ)) 16).symm
  rw [lp4Sum, cd_nsum_eq]
  push_cast
  simp only [h]
  exact (Fin.sum_univ_eq_sum_range (fun i => ∑ u : Fin 16, (f (u + 16 * i) : ℝ)) 4).symm

lemma lp4Lin_add (a b : ℕ → ℤ) (ξ : Fin 4 → Fin 16 → ℝ) :
    lp4Lin (fun q => a q + b q) ξ = lp4Lin a ξ + lp4Lin b ξ := by
  unfold lp4Lin
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun u _ => ?_
  push_cast; ring

lemma lp4Lin_sub (a b : ℕ → ℤ) (ξ : Fin 4 → Fin 16 → ℝ) :
    lp4Lin (fun q => a q - b q) ξ = lp4Lin a ξ - lp4Lin b ξ := by
  unfold lp4Lin
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun u _ => ?_
  push_cast; ring

lemma lp4Lin_smul (c : ℤ) (a : ℕ → ℤ) (ξ : Fin 4 → Fin 16 → ℝ) :
    lp4Lin (fun q => c * a q) ξ = c * lp4Lin a ξ := by
  unfold lp4Lin
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun u _ => ?_
  push_cast; ring

lemma lp4Lin_congr {a b : ℕ → ℤ} (h : ∀ q < 64, a q = b q) (ξ : Fin 4 → Fin 16 → ℝ) :
    lp4Lin a ξ = lp4Lin b ξ := by
  unfold lp4Lin
  refine sum_congr rfl fun i _ => sum_congr rfl fun u _ => ?_
  have := i.2
  have := u.2
  rw [h _ (by omega)]

/-- On the box, a linear form is at most the sum of the positive parts of its coefficients. -/
lemma lp4Lin_le_pos (a : ℕ → ℤ) {ξ : Fin 4 → Fin 16 → ℝ}
    (hbox : ∀ i u, 0 ≤ ξ i u ∧ ξ i u ≤ 1) :
    lp4Lin a ξ ≤ ((lp4Sum fun q => max (a q) 0 : ℤ) : ℝ) := by
  rw [lp4Sum_cast, lp4Lin]
  refine sum_le_sum fun i _ => sum_le_sum fun u _ => ?_
  obtain ⟨h0, h1⟩ := hbox i u
  have hm : (a (u + 16 * i) : ℝ) ≤ ((max (a (u + 16 * i)) 0 : ℤ) : ℝ) := by
    exact_mod_cast le_max_left _ _
  have hm0 : (0 : ℝ) ≤ ((max (a (u + 16 * i)) 0 : ℤ) : ℝ) := by
    exact_mod_cast le_max_right _ _
  calc (a (u + 16 * i) : ℝ) * ξ i u ≤ ((max (a (u + 16 * i)) 0 : ℤ) : ℝ) * ξ i u :=
        mul_le_mul_of_nonneg_right hm h0
    _ ≤ ((max (a (u + 16 * i)) 0 : ℤ) : ℝ) * 1 := mul_le_mul_of_nonneg_left h1 hm0
    _ = _ := mul_one _

lemma lp4_mod16 (i : Fin 4) (u : Fin 16) : ((u : ℕ) + 16 * (i : ℕ)) % 2 ^ 4 = u := by
  have := u.2
  rw [show (2 : ℕ) ^ 4 = 16 from rfl]
  omega

lemma lp4_div16 (i : Fin 4) (u : Fin 16) : ((u : ℕ) + 16 * (i : ℕ)) / 2 ^ 4 = i := by
  have := u.2
  rw [show (2 : ℕ) ^ 4 = 16 from rfl]
  omega

lemma lp4_card_le (C : List (List Bool)) (i : ℕ) : cd_card 4 C i ≤ 4 := by
  rw [cd_card, cd_cnt_eq]
  exact (card_filter_le _ _).trans (by simp)

/-- **The model value is the integer form `cd_fz`** (the coefficients of `2^4 F_C(0)`). -/
theorem lp4V_lin (C : List (List Bool)) (ξ : Fin 4 → Fin 16 → ℝ) :
    lp4Lin (cd_fz 4 C 0) ξ = 16 * lp4V C ξ := by
  unfold lp4Lin lp4V
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  have hc := lp4_card_le C i
  simp only [cd_fz, lp4_mod16, lp4_div16]
  push_cast
  simp only [sub_mul, sum_sub_distrib, ite_mul, zero_mul]
  rw [Finset.sum_eq_single (0 : Fin 16) (fun u _ hu => by simp [hu]) (by simp)]
  have hs : (∑ u : Fin 16, if cd_agree 4 (cd_at C i) u 0 = true
        then (2 : ℝ) ^ (4 - cd_card 4 C i) * ξ i u else 0)
      = (2 : ℝ) ^ (4 - cd_card 4 C i) * ∑ u : Fin 16,
          if cd_agree 4 (cd_at C i) u 0 = true then ξ i u else 0 := by
    rw [mul_sum]
    exact sum_congr rfl fun u _ => by split_ifs <;> simp
  simp only [Fin.val_zero, ite_true]
  rw [hs, pow_sub₀ _ (by norm_num) hc]
  ring

/-! ### Congruence: the model sees a table only through `cd_at` on `Fin 4` -/

lemma lp4_nsumN_congr {n : ℕ} {f f' : ℕ → ℕ} (h : ∀ j < n, f j = f' j) :
    cd_nsumN n f = cd_nsumN n f' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cd_nsumN, cd_nsumN, ih fun j hj => h j (by omega), h n (by omega)]

section Congr

variable {C C' : List (List Bool)} (h : ∀ i j : Fin 4, cd_at C i j = cd_at C' i j)
include h

lemma lp4_card_congr (i : Fin 4) : cd_card 4 C i = cd_card 4 C' i :=
  lp3_cnt_congr fun j hj => h i ⟨j, hj⟩

lemma lp4_agree_congr (i : Fin 4) (u t : ℕ) :
    cd_agree 4 (cd_at C i) u t = cd_agree 4 (cd_at C' i) u t := by
  rw [Bool.eq_iff_iff, cd_agree_iff, cd_agree_iff]
  constructor
  · intro H q hq hr
    exact H q hq (by rw [h i ⟨q, hq⟩]; exact hr)
  · intro H q hq hr
    exact H q hq (by rw [← h i ⟨q, hq⟩]; exact hr)

lemma lp4V_congr (ξ : Fin 4 → Fin 16 → ℝ) : lp4V C ξ = lp4V C' ξ := by
  unfold lp4V
  refine sum_congr rfl fun i _ => ?_
  rw [lp4_card_congr h i]
  congr 2
  exact sum_congr rfl fun u _ => by rw [lp4_agree_congr h i]

lemma lp4cc_congr : cd_cc 4 C = cd_cc 4 C' := by
  unfold cd_cc
  exact lp4_nsumN_congr fun i hi => lp4_card_congr h ⟨i, hi⟩

end Congr

/-! ### The 150 profiles -/

/-- The cut profiles of a 4-set (`lp4Profiles` of `CertLP4Data`). -/
def profiles4 : List (List (List Bool)) := lp4Profiles

/-- **Completeness**: every admissible pair has its profile in the list. -/
theorem profiles4_complete (g δ : List ℕ) (hv : cd_valid 4 g δ = true) :
    cd_profOf 4 g δ ∈ profiles4 :=
  lp3_mem_of_contains (cd_forall_valid 4 (fun g δ => profiles4.contains (cd_profOf 4 g δ))
    (by decide +kernel) g δ hv)

/-- Every listed profile is the profile of an admissible pair. -/
theorem profiles4_realized (C : List (List Bool)) (hC : C ∈ profiles4) :
    ∃ g δ, cd_valid 4 g δ = true ∧ cd_profOf 4 g δ = C := by
  have h : profiles4.all (fun C => (cd_gen 4).any (fun x => cd_profOf 4 x.1 x.2 == C)) = true := by
    decide +kernel
  rw [List.all_eq_true] at h
  obtain ⟨x, hx, hxe⟩ := List.any_eq_true.1 (h C hC)
  refine ⟨x.1, x.2, ?_, by simpa using hxe⟩
  unfold cd_gen at hx
  exact (List.mem_filter.1 hx).2

theorem profiles4_length : profiles4.length = 150 := by decide +kernel

theorem profiles4_nodup : profiles4.Nodup := by decide +kernel

theorem lp4AllCut_mem : lp4AllCut ∈ profiles4 := by decide +kernel

theorem lp4AllCut_cc : cd_cc 4 lp4AllCut = 12 := by decide +kernel

lemma profiles4_cc_pos (C : List (List Bool)) (hC : C ∈ profiles4) : 0 < cd_cc 4 C := by
  have h : profiles4.all (fun C => decide (0 < cd_cc 4 C)) = true := by decide +kernel
  rw [List.all_eq_true] at h
  simpa using h C hC

lemma lp4AllCut_at (i j : Fin 4) : cd_at lp4AllCut i j = true ↔ i ≠ j := by
  revert i j; decide

section Bridge4

variable {S : Finset (Fin N)} (e : Fin 4 ↪ Fin N) (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
  (θ : SysPartition N S)

theorem lpTab_mem4 : lpTab e hS θ ∈ profiles4 := by
  obtain ⟨g, δ, hv, he⟩ := lpTab_valid e hS θ
  rw [he]
  exact profiles4_complete g δ hv

lemma lpTab_ne_allCut4 (hne : ∃ j ∈ S, profile θ j ≠ S.erase j) : lpTab e hS θ ≠ lp4AllCut := by
  intro h
  obtain ⟨j, hj, hne⟩ := hne
  refine hne (lpTab_allCut_of e hS θ (fun i j => ?_) j hj)
  rw [h]
  exact lp4AllCut_at i j

/-- The pattern condition of the model through the profile. -/
lemma lpTab_agree4 (i : Fin 4) (u : Fin 16) :
    cd_agree 4 (cd_at (lpTab e hS θ) i) u 0 = true ↔
      ∀ q : Fin 4, (u : ℕ).testBit q = true → e q ∈ profile θ (e i) := by
  rw [cd_agree_iff]
  constructor
  · intro H q hq
    by_contra hn
    have h1 : cd_at (lpTab e hS θ) i q = false := by
      rw [← Bool.not_eq_true, lpTab_at]; exact hn
    have := H q q.2 h1
    rw [Nat.zero_testBit] at this
    rw [this] at hq
    exact Bool.false_ne_true hq
  · intro H q hq hr
    rw [Nat.zero_testBit]
    by_contra hn
    have h1 := (lpTab_at e hS θ i ⟨q, hq⟩).2 (H ⟨q, hq⟩ (by simpa using hn))
    rw [hr] at h1
    exact Bool.false_ne_true h1

end Bridge4

/-! ### Dual certificates -/

/-- The minimiser row `cc_C · a_{C'} - cc_{C'} · a_C` (so that it is `16 (cc_C v_{C'} - cc_{C'} v_C)`). -/
def lp4Row (C C' : List (List Bool)) (q : ℕ) : ℤ :=
  (cd_cc 4 C : ℤ) * cd_fz 4 C' 0 q - (cd_cc 4 C' : ℤ) * cd_fz 4 C 0 q

/-- Weighted rows. -/
def lp4CombL (C : List (List Bool)) (rows : List (List (List Bool) × ℕ)) (q : ℕ) : ℤ :=
  (rows.map fun r => (r.2 : ℤ) * lp4Row C r.1 q).sum

/-- The slack factor `Λ = ∑ μ_m cc_C cc_m` of weighted rows. -/
def lp4LamL (C : List (List Bool)) (rows : List (List (List Bool) × ℕ)) : ℕ :=
  (rows.map fun r => r.2 * (cd_cc 4 C * cd_cc 4 r.1)).sum

/-- `W = wF f + ∑ μ_m row_m + ν a_C`. -/
def lp4W (c : LP3Cert) (f : ℕ → ℤ) (q : ℕ) : ℤ :=
  (c.wF : ℤ) * f q + lp4CombL c.C c.rows q + (c.nu : ℤ) * cd_fz 4 c.C 0 q

/-- The sum of the positive parts of `W`. -/
def lp4U (c : LP3Cert) (f : ℕ → ℤ) : ℤ := lp4Sum fun q => max (lp4W c f q) 0

/-- Admissibility of the rows of a certificate. -/
def lp4RowsOK (c : LP3Cert) : Bool :=
  decide (0 < c.wF) && decide (0 < cd_cc 4 c.C) &&
    c.rows.all fun r => profiles4.contains r.1 && decide (0 < cd_cc 4 r.1)

lemma lp4Lin_row (C C' : List (List Bool)) (ξ : Fin 4 → Fin 16 → ℝ) :
    lp4Lin (lp4Row C C') ξ = 16 * ((cd_cc 4 C : ℝ) * lp4V C' ξ - (cd_cc 4 C' : ℝ) * lp4V C ξ) := by
  have e : lp4Row C C' = fun q => (cd_cc 4 C : ℤ) * cd_fz 4 C' 0 q - (cd_cc 4 C' : ℤ) * cd_fz 4 C 0 q :=
    rfl
  rw [e, lp4Lin_sub, lp4Lin_smul, lp4Lin_smul, lp4V_lin, lp4V_lin]
  push_cast
  ring

/-- One minimiser row is bounded below by the slack. -/
lemma lp4_row_lower {C C' : List (List Bool)} {ξ : Fin 4 → Fin 16 → ℝ} {e : ℝ}
    (hc : 0 < cd_cc 4 C) (hc' : 0 < cd_cc 4 C')
    (hmin : lp4V C ξ / cd_cc 4 C ≤ lp4V C' ξ / cd_cc 4 C' + e) :
    -(16 * e * ((cd_cc 4 C : ℝ) * cd_cc 4 C')) ≤ lp4Lin (lp4Row C C') ξ := by
  rw [lp4Lin_row]
  have hp : (0 : ℝ) < cd_cc 4 C := by exact_mod_cast hc
  have hq : (0 : ℝ) < cd_cc 4 C' := by exact_mod_cast hc'
  have h1 := mul_le_mul_of_nonneg_right hmin (le_of_lt (mul_pos hp hq))
  have e1 : lp4V C ξ / (cd_cc 4 C : ℝ) * ((cd_cc 4 C : ℝ) * cd_cc 4 C')
      = lp4V C ξ * cd_cc 4 C' := by field_simp
  have e2 : (lp4V C' ξ / (cd_cc 4 C' : ℝ) + e) * ((cd_cc 4 C : ℝ) * cd_cc 4 C')
      = lp4V C' ξ * cd_cc 4 C + e * ((cd_cc 4 C : ℝ) * cd_cc 4 C') := by field_simp
  rw [e1, e2] at h1
  nlinarith

lemma lp4Lin_combL (C : List (List Bool)) (rows : List (List (List Bool) × ℕ))
    (ξ : Fin 4 → Fin 16 → ℝ) :
    lp4Lin (lp4CombL C rows) ξ = (rows.map fun r => (r.2 : ℝ) * lp4Lin (lp4Row C r.1) ξ).sum := by
  induction rows with
  | nil => simp [lp4CombL, lp4Lin]
  | cons a l ih =>
    have e : lp4CombL C (a :: l) = fun q => (a.2 : ℤ) * lp4Row C a.1 q + lp4CombL C l q := by
      funext q; simp [lp4CombL]
    rw [e, lp4Lin_add, lp4Lin_smul, ih]
    simp

/-- The weighted rows are bounded below by `-16 e Λ`. -/
lemma lp4_combL_lower (C : List (List Bool)) (rows : List (List (List Bool) × ℕ))
    {ξ : Fin 4 → Fin 16 → ℝ} {e : ℝ} (hc : 0 < cd_cc 4 C)
    (hrows : ∀ r ∈ rows, r.1 ∈ profiles4 ∧ 0 < cd_cc 4 r.1)
    (hmin : ∀ C' ∈ profiles4, lp4V C ξ / cd_cc 4 C ≤ lp4V C' ξ / cd_cc 4 C' + e) :
    -(16 * e * (lp4LamL C rows : ℝ)) ≤ lp4Lin (lp4CombL C rows) ξ := by
  rw [lp4Lin_combL]
  induction rows with
  | nil => simp [lp4LamL]
  | cons a l ih =>
    have ha := lp4_row_lower hc (hrows a List.mem_cons_self).2 (hmin a.1 (hrows a List.mem_cons_self).1)
    have hl := ih fun r hr => hrows r (List.mem_cons_of_mem _ hr)
    simp only [lp4LamL, List.map_cons, List.sum_cons] at hl ⊢
    push_cast at hl ⊢
    have hw : (0 : ℝ) ≤ a.2 := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left ha hw]

/-- **Soundness of a certificate** (general target form `f`, value row weight `ν`):
on the box, if `c.C` is a minimiser up to `e` and `L ≤ v_C`, then
`wF · ⟨f, ξ⟩ ≤ U - 16 ν L + 16 e Λ`. -/
theorem lp4_gen_sound (c : LP3Cert) (f : ℕ → ℤ) (hok : lp4RowsOK c = true)
    {ξ : Fin 4 → Fin 16 → ℝ} (hbox : ∀ i u, 0 ≤ ξ i u ∧ ξ i u ≤ 1) {e : ℝ}
    (hmin : ∀ C' ∈ profiles4, lp4V c.C ξ / cd_cc 4 c.C ≤ lp4V C' ξ / cd_cc 4 C' + e)
    {L : ℝ} (hL : L ≤ lp4V c.C ξ) :
    (c.wF : ℝ) * lp4Lin f ξ ≤ (lp4U c f : ℝ) - 16 * c.nu * L + 16 * e * lp4LamL c.C c.rows := by
  simp only [lp4RowsOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨_, hc⟩, hrows⟩ := hok
  have hrows' : ∀ r ∈ c.rows, r.1 ∈ profiles4 ∧ 0 < cd_cc 4 r.1 := fun r hr => by
    have := hrows r hr
    exact ⟨lp3_mem_of_contains this.1, this.2⟩
  have hW : lp4Lin (lp4W c f) ξ ≤ (lp4U c f : ℝ) := lp4Lin_le_pos (lp4W c f) hbox
  have hlin : lp4Lin (lp4W c f) ξ
      = c.wF * lp4Lin f ξ + lp4Lin (lp4CombL c.C c.rows) ξ + c.nu * (16 * lp4V c.C ξ) := by
    have eW : lp4W c f = fun q => ((c.wF : ℤ) * f q + lp4CombL c.C c.rows q)
        + (c.nu : ℤ) * cd_fz 4 c.C 0 q := rfl
    rw [eW, lp4Lin_add, lp4Lin_add, lp4Lin_smul, lp4Lin_smul, lp4V_lin]
    push_cast
    ring
  have hcomb := lp4_combL_lower c.C c.rows hc hrows' hmin
  have hnu : (0 : ℝ) ≤ c.nu := Nat.cast_nonneg _
  have h2 : (c.nu : ℝ) * L ≤ c.nu * lp4V c.C ξ := mul_le_mul_of_nonneg_left hL hnu
  rw [hlin] at hW
  linarith

/-! ### The 149 certificates: `v_C ≤ 11/4 + (165/4) e` -/

/-- The check of a bound certificate: `ν = 0`, `U ≤ 44 wF`, `4 Λ ≤ 165 wF`. -/
def lp4Check (c : LP3Cert) : Bool :=
  lp4RowsOK c && (c.nu == 0) && decide (lp4U c (cd_fz 4 c.C 0) ≤ 44 * c.wF) &&
    decide (4 * lp4LamL c.C c.rows ≤ 165 * c.wF)

theorem lp4_check_sound (c : LP3Cert) (hc : lp4Check c = true) {ξ : Fin 4 → Fin 16 → ℝ}
    (hbox : ∀ i u, 0 ≤ ξ i u ∧ ξ i u ≤ 1) {e : ℝ} (he : 0 ≤ e)
    (hmin : ∀ C' ∈ profiles4, lp4V c.C ξ / cd_cc 4 c.C ≤ lp4V C' ξ / cd_cc 4 C' + e) :
    lp4V c.C ξ ≤ 11 / 4 + 165 / 4 * e := by
  simp only [lp4Check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨hok, hnu⟩, hU⟩, hLam⟩ := hc
  have h := lp4_gen_sound c (cd_fz 4 c.C 0) hok hbox hmin (le_refl (lp4V c.C ξ))
  rw [lp4V_lin, hnu] at h
  have hw : (0 : ℝ) < c.wF := by
    simp only [lp4RowsOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact_mod_cast hok.1.1
  have hU' : (lp4U c (cd_fz 4 c.C 0) : ℝ) ≤ 44 * c.wF := by exact_mod_cast hU
  have hL' : 4 * (lp4LamL c.C c.rows : ℝ) ≤ 165 * c.wF := by exact_mod_cast hLam
  have h4 := mul_le_mul_of_nonneg_left hL' he
  push_cast at h
  have h3 : (c.wF : ℝ) * (4 * lp4V c.C ξ) ≤ c.wF * (11 + 165 * e) := by nlinarith
  have h5 := le_of_mul_le_mul_left h3 hw
  linarith

/-- The kernel check over all 149 non-all-cut profiles. -/
def lp4AllOK : Bool :=
  profiles4.all fun C => (C == lp4AllCut) || lp4Certs.any fun c => (c.C == C) && lp4Check c

theorem lp4AllOK_true : lp4AllOK = true := by decide +kernel

/-- **The 4-set LP bound** (C15b).  A non-all-cut profile of a 4-set that minimises `lp4V / cc` up
to `e` on the box has value at most `11/4 + (165/4) e`. -/
theorem lp4_bound {C : List (List Bool)} (hC : C ∈ profiles4) (hne : C ≠ lp4AllCut)
    {ξ : Fin 4 → Fin 16 → ℝ} (hbox : ∀ i u, 0 ≤ ξ i u ∧ ξ i u ≤ 1) {e : ℝ} (he : 0 ≤ e)
    (hmin : ∀ C' ∈ profiles4, lp4V C ξ / cd_cc 4 C ≤ lp4V C' ξ / cd_cc 4 C' + e) :
    lp4V C ξ ≤ 11 / 4 + 165 / 4 * e := by
  have h := lp4AllOK_true
  simp only [lp4AllOK, List.all_eq_true] at h
  have hC' := h C hC
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true] at hC'
  rcases hC' with h1 | ⟨c, _, hcC, hchk⟩
  · exact absurd h1 hne
  · subst hcC
    exact lp4_check_sound c hchk hbox he hmin

/-- **The 4-set LP bound for a system partition** of a 4-set `S` ordered by `e`: if the model
value of `θ` (through its table) minimises `value / sysCutCount` over all partitions of `S` up to
`ε`, and `θ` does not have the all-cut profile, then its value is at most `11/4 + (165/4) ε`. -/
theorem lp4_bound_sys {S : Finset (Fin N)} (e : Fin 4 ↪ Fin N) (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
    (θ : SysPartition N S) (hne : ∃ j ∈ S, profile θ j ≠ S.erase j)
    {ξ : Fin 4 → Fin 16 → ℝ} (hbox : ∀ i u, 0 ≤ ξ i u ∧ ξ i u ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hmin : ∀ θ' : SysPartition N S, lp4V (lpTab e hS θ) ξ / sysCutCount θ ≤
      lp4V (lpTab e hS θ') ξ / sysCutCount θ' + ε) :
    lp4V (lpTab e hS θ) ξ ≤ 11 / 4 + 165 / 4 * ε := by
  refine lp4_bound (lpTab_mem4 e hS θ) (lpTab_ne_allCut4 e hS θ hne) hbox hε fun C' hC' => ?_
  obtain ⟨g, δ, hv, rfl⟩ := profiles4_realized C' hC'
  obtain ⟨θ', hθ'⟩ := lpTab_realize e hS g δ hv
  have hv' : lp4V (cd_profOf 4 g δ) ξ = lp4V (lpTab e hS θ') ξ := (lp4V_congr hθ' ξ).symm
  have hcc' : cd_cc 4 (cd_profOf 4 g δ) = sysCutCount θ' := by
    rw [← lp4cc_congr hθ', lpTab_cc]
  rw [hv', hcc', lpTab_cc]
  exact hmin θ'

end Census
end IIT
