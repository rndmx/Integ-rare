/-
Census: the triple LP (module A5 of B1-BLUEPRINT, certificate C15).

**The linear model.**  A 3-set with units `0, 1, 2` at the tilt: `ξ i 0 = y_i` is the entry of the
cause row `tc` in column `i`, and `ξ i u` (`u : Fin 8`, bit `q` of `u` = unit `q` flipped) is the entry
of the row `tc` flipped on `u` in column `i`.  A cut profile is a table `C : List (List Bool)`
(`cd_at C i j`: unit `i` loses unit `j`), and

    lp3V C ξ = ∑_i (ξ i 0 - 2^{-|C_i|} ∑_{u ⊆ C_i} ξ i u)
             = ∑_i (1 - 2^{-|C_i|}) (y_i - mean_{∅ ≠ T ⊆ C_i} p_{i,T}),     cc(C) = ∑_i |C_i|.

The 22 profiles (`profiles3`) are the distinct tables `cd_profOf 3 g δ` of the admissible pairs of
`cd_gen 3` (Lean's directional `SysPartition` semantics, `cd_classify`/`cd_realize`):
`profiles3_complete` and `profiles3_realized` show that the list is exactly that set, and `lpTab`
transports a partition of a `k`-set to its table (`lpTab_mem`, `lpTab_cc`, `lpTab_at`, `lpTab_agree`).

**Results.**
* `lp3_bound_sharp` / `lp3_bound` (21 kernel-checked rational dual certificates, `CertLP3Data`): if a
  non-all-cut profile `C` minimises `lp3V / cc` over `profiles3` up to an additive slack `e` and
  `ξ ∈ [0,1]^24`, then `lp3V C ξ ≤ 5/3 + (40/3) e` (blueprint form: `5/3 + 40 e`).
  `lp3_bound_sys` is the same statement for a system partition of a 3-set.
* The all-cut profile.  Model: `v_all = ∑_i v(single cut i)` exactly, `cc = 6 = 2 + 2 + 2`
  (`lp3_allCut_model`), so it is a near-miniser only at a near tie (`lp3_allCut_near_tie`).  Real
  quantities (any `S`, open cube): the cause and effect log-ratios of the all-cut partition are the
  sums of those of the single-unit cuts (`allCut_logb_cause`, `allCut_logb_effect`); if the all-cut
  partition lies in the MIP set with a positive value, then every single-unit cut has value
  `φ_all / |S|` (`allCut_mip_tie`): an exact tie of the single-cut values.
* `lp3_interior` (W2, Section 7.1, Lemma LP-q): the explicit point `q(t)` (`lp3Q`: `y = 1`,
  `p[0,{2}] = p[1,{0,2}] = p[2,{0,1}] = 1/3 + t`, the other six private roles `0`).  For
  `0 ≤ t ≤ 2/3`: `v_{C*} = 5/3 - t`, every other profile has `v_C / cc_C ≥ v_{C*}/5 + 3t/40` (the 21
  inequalities, linear in `t`, kernel-checked at both ends), every value is `≥ 2/3 - t/4`.
  `lp3_interior_scaled`: the same for any `ξ` with `ξ i 0 - ξ i u = c (1 - q(t)_{i,u})` (the shift
  trick `p = y - c (1 - q(t))`), with the multiplicative form `(1 + 9t/40) v_{C*}/5 ≤ v_C/cc_C`
  used by `tl_triple_lower_gen`.  `C*` (`lp3CStar`) is the profile of `tl_thetaStar`.
* `lp3_private_range` (12 certificates): for a cc-5 profile and a unit cut from both others, the
  pair-private coordinate is `≤ 2/5 + 9 e` on `{C minimiser up to e, lp3V C ≥ 5/3 - 1/100 - e}`.
* `cc_le_five_of_ne_allCut`, `cc_le_11_of_ne_allCut`: a partition of a 3-set (4-set) whose profile
  is not all-cut has `sysCutCount ≤ 5` (`≤ 11`).

**Deviations from the blueprint** (A5; otherwise as written there):
* one array `ξ : Fin 3 → Fin 8 → ℝ` indexed by patterns (the coordinates of `CertDataBase`)
  replaces `y : Fin 3 → ℝ`, `p : Fin 3 → Fin 4 → ℝ`: `y_i = ξ i 0`, `p_{i,T} = ξ i (mask T)`; the box
  hypothesis is `∀ i u, 0 ≤ ξ i u ≤ 1`;
* the constant of `lp3_bound` is `40/3` (the exact dual optimum), which implies the blueprint's `40`;
* the blueprint's "`ph(all) ≥ ∑ ph(θ_i)`" is false in general (the positive parts break additivity
  when a single-cut log-ratio is negative).  What is true and proved: exact additivity of the
  log-ratios, and the tie statement `allCut_mip_tie` under `0 < φ_all` (a zero value is harmless);
  the nullity of such ties is B2's job;
* `lp3_interior` follows the W2 change (explicit `q(t)`, no solver data) instead of the blueprint's
  `p*` with margins `≥ 1/10^4` and value `≥ 5/3 - 1/10^3`; the range of `t` is `[0, 2/3]`.
-/
import IIT.Census.CertLP3Data
import IIT.Census.CertDataClass
import IIT.Census.TieBranches

namespace IIT
namespace Census

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-! ### The linear model -/

/-- The value of the profile `C` in the linear model. -/
noncomputable def lp3V (C : List (List Bool)) (ξ : Fin 3 → Fin 8 → ℝ) : ℝ :=
  ∑ i : Fin 3, (ξ i 0 - ((2 : ℝ) ^ cd_card 3 C i)⁻¹ *
    ∑ u : Fin 8, if cd_agree 3 (cd_at C i) u 0 = true then ξ i u else 0)

/-- The linear form with integer coefficients `a (u + 8 i)`. -/
noncomputable def lp3Lin (a : ℕ → ℤ) (ξ : Fin 3 → Fin 8 → ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ u : Fin 8, (a (u + 8 * i) : ℝ) * ξ i u

/-- `∑_{q < 24} f q` as a double sum over units and patterns (kernel friendly). -/
def lp3Sum (f : ℕ → ℤ) : ℤ := cd_nsum 3 fun i => cd_nsum 8 fun u => f (u + 8 * i)

lemma lp3Sum_cast (f : ℕ → ℤ) :
    (lp3Sum f : ℝ) = ∑ i : Fin 3, ∑ u : Fin 8, (f (u + 8 * i) : ℝ) := by
  have h : ∀ i : ℕ, (((cd_nsum 8 fun u => f (u + 8 * i)) : ℤ) : ℝ)
      = ∑ u : Fin 8, (f (u + 8 * i) : ℝ) := by
    intro i
    rw [cd_nsum_eq]
    push_cast
    exact (Fin.sum_univ_eq_sum_range (fun u => (f (u + 8 * i) : ℝ)) 8).symm
  rw [lp3Sum, cd_nsum_eq]
  push_cast
  simp only [h]
  exact (Fin.sum_univ_eq_sum_range (fun i => ∑ u : Fin 8, (f (u + 8 * i) : ℝ)) 3).symm

lemma lp3Lin_add (a b : ℕ → ℤ) (ξ : Fin 3 → Fin 8 → ℝ) :
    lp3Lin (fun q => a q + b q) ξ = lp3Lin a ξ + lp3Lin b ξ := by
  unfold lp3Lin
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun u _ => ?_
  push_cast; ring

lemma lp3Lin_sub (a b : ℕ → ℤ) (ξ : Fin 3 → Fin 8 → ℝ) :
    lp3Lin (fun q => a q - b q) ξ = lp3Lin a ξ - lp3Lin b ξ := by
  unfold lp3Lin
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun u _ => ?_
  push_cast; ring

lemma lp3Lin_smul (c : ℤ) (a : ℕ → ℤ) (ξ : Fin 3 → Fin 8 → ℝ) :
    lp3Lin (fun q => c * a q) ξ = c * lp3Lin a ξ := by
  unfold lp3Lin
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun u _ => ?_
  push_cast; ring

lemma lp3Lin_congr {a b : ℕ → ℤ} (h : ∀ q < 24, a q = b q) (ξ : Fin 3 → Fin 8 → ℝ) :
    lp3Lin a ξ = lp3Lin b ξ := by
  unfold lp3Lin
  refine sum_congr rfl fun i _ => sum_congr rfl fun u _ => ?_
  have := i.2
  have := u.2
  rw [h _ (by omega)]

/-- On the box, a linear form is at most the sum of the positive parts of its coefficients. -/
lemma lp3Lin_le_pos (a : ℕ → ℤ) {ξ : Fin 3 → Fin 8 → ℝ}
    (hbox : ∀ i u, 0 ≤ ξ i u ∧ ξ i u ≤ 1) :
    lp3Lin a ξ ≤ ((lp3Sum fun q => max (a q) 0 : ℤ) : ℝ) := by
  rw [lp3Sum_cast, lp3Lin]
  refine sum_le_sum fun i _ => sum_le_sum fun u _ => ?_
  obtain ⟨h0, h1⟩ := hbox i u
  have hm : (a (u + 8 * i) : ℝ) ≤ ((max (a (u + 8 * i)) 0 : ℤ) : ℝ) := by
    exact_mod_cast le_max_left _ _
  have hm0 : (0 : ℝ) ≤ ((max (a (u + 8 * i)) 0 : ℤ) : ℝ) := by
    exact_mod_cast le_max_right _ _
  calc (a (u + 8 * i) : ℝ) * ξ i u ≤ ((max (a (u + 8 * i)) 0 : ℤ) : ℝ) * ξ i u :=
        mul_le_mul_of_nonneg_right hm h0
    _ ≤ ((max (a (u + 8 * i)) 0 : ℤ) : ℝ) * 1 := mul_le_mul_of_nonneg_left h1 hm0
    _ = _ := mul_one _

lemma lp3_mod8 (i : Fin 3) (u : Fin 8) : ((u : ℕ) + 8 * (i : ℕ)) % 2 ^ 3 = u := by
  have := u.2
  rw [show (2 : ℕ) ^ 3 = 8 from rfl]
  omega

lemma lp3_div8 (i : Fin 3) (u : Fin 8) : ((u : ℕ) + 8 * (i : ℕ)) / 2 ^ 3 = i := by
  have := u.2
  rw [show (2 : ℕ) ^ 3 = 8 from rfl]
  omega

lemma lp3_card_le (C : List (List Bool)) (i : ℕ) : cd_card 3 C i ≤ 3 := by
  rw [cd_card, cd_cnt_eq]
  exact (card_filter_le _ _).trans (by simp)

/-- **The model value is the integer form `cd_fz`** (the coefficients of `2^3 F_C(0)`). -/
theorem lp3V_lin (C : List (List Bool)) (ξ : Fin 3 → Fin 8 → ℝ) :
    lp3Lin (cd_fz 3 C 0) ξ = 8 * lp3V C ξ := by
  unfold lp3Lin lp3V
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  have hc := lp3_card_le C i
  simp only [cd_fz, lp3_mod8, lp3_div8]
  push_cast
  simp only [sub_mul, sum_sub_distrib, ite_mul, zero_mul]
  rw [Finset.sum_eq_single (0 : Fin 8) (fun u _ hu => by simp [hu]) (by simp)]
  have hs : (∑ u : Fin 8, if cd_agree 3 (cd_at C i) u 0 = true
        then (2 : ℝ) ^ (3 - cd_card 3 C i) * ξ i u else 0)
      = (2 : ℝ) ^ (3 - cd_card 3 C i) * ∑ u : Fin 8,
          if cd_agree 3 (cd_at C i) u 0 = true then ξ i u else 0 := by
    rw [mul_sum]
    exact sum_congr rfl fun u _ => by split_ifs <;> simp
  simp only [Fin.val_zero, ite_true]
  rw [hs, pow_sub₀ _ (by norm_num) hc]
  ring

/-! ### Congruence: the model sees a table only through `cd_at` on `Fin 3` -/

lemma lp3_cnt_congr {n : ℕ} {f f' : ℕ → Bool} (h : ∀ j < n, f j = f' j) : cd_cnt n f = cd_cnt n f' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cd_cnt, cd_cnt, ih fun j hj => h j (by omega), h n (by omega)]

section Congr

variable {C C' : List (List Bool)} (h : ∀ i j : Fin 3, cd_at C i j = cd_at C' i j)
include h

lemma lp3_card_congr (i : Fin 3) : cd_card 3 C i = cd_card 3 C' i :=
  lp3_cnt_congr fun j hj => h i ⟨j, hj⟩

lemma lp3_agree_congr (i : Fin 3) (u t : ℕ) :
    cd_agree 3 (cd_at C i) u t = cd_agree 3 (cd_at C' i) u t := by
  rw [Bool.eq_iff_iff, cd_agree_iff, cd_agree_iff]
  constructor
  · intro H q hq hr
    exact H q hq (by rw [h i ⟨q, hq⟩]; exact hr)
  · intro H q hq hr
    exact H q hq (by rw [← h i ⟨q, hq⟩]; exact hr)

lemma lp3V_congr (ξ : Fin 3 → Fin 8 → ℝ) : lp3V C ξ = lp3V C' ξ := by
  unfold lp3V
  refine sum_congr rfl fun i _ => ?_
  rw [lp3_card_congr h i]
  congr 2
  exact sum_congr rfl fun u _ => by rw [lp3_agree_congr h i]

lemma lp3cc_congr : cd_cc 3 C = cd_cc 3 C' := by
  have h0 := lp3_card_congr h 0
  have h1 := lp3_card_congr h 1
  have h2 := lp3_card_congr h 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  simp only [cd_cc, cd_nsumN, h0, h1, h2]

end Congr

/-! ### The 22 profiles -/

/-- The cut profiles of a 3-set (`lp3Profiles` of `CertLP3Data`). -/
def profiles3 : List (List (List Bool)) := lp3Profiles

lemma lp3_mem_of_contains {C : List (List Bool)} {l : List (List (List Bool))}
    (h : l.contains C = true) : C ∈ l := by
  simpa using h

/-- **Completeness**: every admissible pair has its profile in the list. -/
theorem profiles3_complete (g δ : List ℕ) (hv : cd_valid 3 g δ = true) :
    cd_profOf 3 g δ ∈ profiles3 :=
  lp3_mem_of_contains (cd_forall_valid 3 (fun g δ => profiles3.contains (cd_profOf 3 g δ))
    (by decide +kernel) g δ hv)

/-- Every listed profile is the profile of an admissible pair. -/
theorem profiles3_realized (C : List (List Bool)) (hC : C ∈ profiles3) :
    ∃ g δ, cd_valid 3 g δ = true ∧ cd_profOf 3 g δ = C := by
  have h : profiles3.all (fun C => (cd_gen 3).any (fun x => cd_profOf 3 x.1 x.2 == C)) = true := by
    decide +kernel
  rw [List.all_eq_true] at h
  obtain ⟨x, hx, hxe⟩ := List.any_eq_true.1 (h C hC)
  refine ⟨x.1, x.2, ?_, by simpa using hxe⟩
  unfold cd_gen at hx
  exact (List.mem_filter.1 hx).2

theorem profiles3_length : profiles3.length = 22 := by decide +kernel

theorem profiles3_nodup : profiles3.Nodup := by decide +kernel

theorem lp3AllCut_mem : lp3AllCut ∈ profiles3 := by decide +kernel

theorem lp3CStar_mem : lp3CStar ∈ profiles3 := by decide +kernel

theorem lp3AllCut_cc : cd_cc 3 lp3AllCut = 6 := by decide +kernel

theorem lp3CStar_cc : cd_cc 3 lp3CStar = 5 := by decide +kernel

lemma profiles3_cc_pos (C : List (List Bool)) (hC : C ∈ profiles3) : 0 < cd_cc 3 C := by
  have h : profiles3.all (fun C => decide (0 < cd_cc 3 C)) = true := by decide +kernel
  rw [List.all_eq_true] at h
  simpa using h C hC

lemma lp3AllCut_at (i j : Fin 3) : cd_at lp3AllCut i j = true ↔ i ≠ j := by
  revert i j; decide

/-! ### From system partitions to tables -/

section Bridge

variable {k : ℕ} {S : Finset (Fin N)} (e : Fin k ↪ Fin N) (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
  (θ : SysPartition N S)

/-- The table of a partition along the ordering `e` (an admissible profile, by `cd_classify`). -/
noncomputable def lpTab : List (List Bool) :=
  cd_profOf k (Classical.choose (cd_classify e hS θ))
    (Classical.choose (Classical.choose_spec (cd_classify e hS θ)))

lemma lpTab_valid : ∃ g δ, cd_valid k g δ = true ∧ lpTab e hS θ = cd_profOf k g δ :=
  ⟨_, _, (Classical.choose_spec (Classical.choose_spec (cd_classify e hS θ))).1, rfl⟩

lemma lpTab_at (i j : Fin k) : cd_at (lpTab e hS θ) i j = true ↔ e j ∈ profile θ (e i) :=
  ((Classical.choose_spec (Classical.choose_spec (cd_classify e hS θ))).2 i j).symm

lemma lpTab_card (i : Fin k) : cd_card k (lpTab e hS θ) i = (profile θ (e i)).card := by
  rw [cd_card, cd_cnt_eq]
  have hm : (univ.filter fun j : Fin k => cd_at (lpTab e hS θ) i j = true).map e
      = profile θ (e i) := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact (lpTab_at e hS θ i j).1 hj
    · intro hx
      obtain ⟨j, rfl⟩ := (hS x).1 (prof_profile_subset θ _ hx)
      exact ⟨j, (lpTab_at e hS θ i j).2 hx, rfl⟩
  rw [← hm, card_map]

/-- The normaliser of the table is the system cut count. -/
theorem lpTab_cc : cd_cc k (lpTab e hS θ) = sysCutCount θ := by
  have hSm : S = univ.map e := by
    ext x
    simp [hS x]
  rw [sysCutCount_eq_sum_profile, cd_cc, cd_nsumN_eq,
    ← Fin.sum_univ_eq_sum_range (cd_card k (lpTab e hS θ)) k]
  simp only [lpTab_card e hS θ]
  have h2 : ∑ j ∈ S, (profile θ j).card = ∑ j ∈ univ.map e, (profile θ j).card :=
    Finset.sum_congr hSm fun _ _ => rfl
  rw [h2, sum_map]

/-- A table whose off-diagonal entries are all set comes from the all-cut profile. -/
lemma lpTab_allCut_of (h : ∀ i j : Fin k, cd_at (lpTab e hS θ) i j = true ↔ i ≠ j) :
    ∀ x ∈ S, profile θ x = S.erase x := by
  intro x hx
  obtain ⟨i, rfl⟩ := (hS x).1 hx
  ext y
  constructor
  · intro hy
    obtain ⟨j, rfl⟩ := (hS y).1 (prof_profile_subset θ _ hy)
    have hij := (h i j).1 ((lpTab_at e hS θ i j).2 hy)
    exact mem_erase.2 ⟨fun he => hij (e.injective he).symm, (hS _).2 ⟨j, rfl⟩⟩
  · intro hy
    obtain ⟨hne, hyS⟩ := mem_erase.1 hy
    obtain ⟨j, rfl⟩ := (hS _).1 hyS
    exact (lpTab_at e hS θ i j).1 ((h i j).2 fun hij => hne (by rw [hij]))

/-- A partition realising a given admissible table. -/
lemma lpTab_realize (g δ : List ℕ) (hv : cd_valid k g δ = true) :
    ∃ θ' : SysPartition N S, ∀ i j : Fin k,
      cd_at (lpTab e hS θ') i j = cd_at (cd_profOf k g δ) i j := by
  obtain ⟨θ', hθ'⟩ := cd_realize e g δ hS hv
  refine ⟨θ', fun i j => ?_⟩
  rw [Bool.eq_iff_iff, lpTab_at, hθ']

end Bridge

/-- An ordering of a finset of known size. -/
lemma lp_embed {S : Finset (Fin N)} {k : ℕ} (hk : S.card = k) :
    ∃ e : Fin k ↪ Fin N, ∀ x, x ∈ S ↔ ∃ i, e i = x := by
  refine ⟨(S.orderEmbOfFin hk).toEmbedding, fun x => ?_⟩
  rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin S hk]
  rfl

section Bridge3

variable {S : Finset (Fin N)} (e : Fin 3 ↪ Fin N) (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
  (θ : SysPartition N S)

theorem lpTab_mem : lpTab e hS θ ∈ profiles3 := by
  obtain ⟨g, δ, hv, he⟩ := lpTab_valid e hS θ
  rw [he]
  exact profiles3_complete g δ hv

lemma lpTab_ne_allCut (hne : ∃ j ∈ S, profile θ j ≠ S.erase j) : lpTab e hS θ ≠ lp3AllCut := by
  intro h
  obtain ⟨j, hj, hne⟩ := hne
  refine hne (lpTab_allCut_of e hS θ (fun i j => ?_) j hj)
  rw [h]
  exact lp3AllCut_at i j

/-- The pattern condition of the model through the profile. -/
lemma lpTab_agree (i : Fin 3) (u : Fin 8) :
    cd_agree 3 (cd_at (lpTab e hS θ) i) u 0 = true ↔
      ∀ q : Fin 3, (u : ℕ).testBit q = true → e q ∈ profile θ (e i) := by
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

end Bridge3

/-! ### Dual certificates -/

/-- The minimiser row `cc_C · a_{C'} - cc_{C'} · a_C` (so that it is `8 (cc_C v_{C'} - cc_{C'} v_C)`). -/
def lp3Row (C C' : List (List Bool)) (q : ℕ) : ℤ :=
  (cd_cc 3 C : ℤ) * cd_fz 3 C' 0 q - (cd_cc 3 C' : ℤ) * cd_fz 3 C 0 q

/-- Weighted rows. -/
def lp3CombL (C : List (List Bool)) (rows : List (List (List Bool) × ℕ)) (q : ℕ) : ℤ :=
  (rows.map fun r => (r.2 : ℤ) * lp3Row C r.1 q).sum

/-- The slack factor `Λ = ∑ μ_m cc_C cc_m` of weighted rows. -/
def lp3LamL (C : List (List Bool)) (rows : List (List (List Bool) × ℕ)) : ℕ :=
  (rows.map fun r => r.2 * (cd_cc 3 C * cd_cc 3 r.1)).sum

/-- `W = wF f + ∑ μ_m row_m + ν a_C`. -/
def lp3W (c : LP3Cert) (f : ℕ → ℤ) (q : ℕ) : ℤ :=
  (c.wF : ℤ) * f q + lp3CombL c.C c.rows q + (c.nu : ℤ) * cd_fz 3 c.C 0 q

/-- The sum of the positive parts of `W`. -/
def lp3U (c : LP3Cert) (f : ℕ → ℤ) : ℤ := lp3Sum fun q => max (lp3W c f q) 0

/-- Admissibility of the rows of a certificate. -/
def lp3RowsOK (c : LP3Cert) : Bool :=
  decide (0 < c.wF) && decide (0 < cd_cc 3 c.C) &&
    c.rows.all fun r => profiles3.contains r.1 && decide (0 < cd_cc 3 r.1)

lemma lp3Lin_row (C C' : List (List Bool)) (ξ : Fin 3 → Fin 8 → ℝ) :
    lp3Lin (lp3Row C C') ξ = 8 * ((cd_cc 3 C : ℝ) * lp3V C' ξ - (cd_cc 3 C' : ℝ) * lp3V C ξ) := by
  have e : lp3Row C C' = fun q => (cd_cc 3 C : ℤ) * cd_fz 3 C' 0 q - (cd_cc 3 C' : ℤ) * cd_fz 3 C 0 q :=
    rfl
  rw [e, lp3Lin_sub, lp3Lin_smul, lp3Lin_smul, lp3V_lin, lp3V_lin]
  push_cast
  ring

/-- One minimiser row is bounded below by the slack. -/
lemma lp3_row_lower {C C' : List (List Bool)} {ξ : Fin 3 → Fin 8 → ℝ} {e : ℝ}
    (hc : 0 < cd_cc 3 C) (hc' : 0 < cd_cc 3 C')
    (hmin : lp3V C ξ / cd_cc 3 C ≤ lp3V C' ξ / cd_cc 3 C' + e) :
    -(8 * e * ((cd_cc 3 C : ℝ) * cd_cc 3 C')) ≤ lp3Lin (lp3Row C C') ξ := by
  rw [lp3Lin_row]
  have hp : (0 : ℝ) < cd_cc 3 C := by exact_mod_cast hc
  have hq : (0 : ℝ) < cd_cc 3 C' := by exact_mod_cast hc'
  have h1 := mul_le_mul_of_nonneg_right hmin (le_of_lt (mul_pos hp hq))
  have e1 : lp3V C ξ / (cd_cc 3 C : ℝ) * ((cd_cc 3 C : ℝ) * cd_cc 3 C')
      = lp3V C ξ * cd_cc 3 C' := by field_simp
  have e2 : (lp3V C' ξ / (cd_cc 3 C' : ℝ) + e) * ((cd_cc 3 C : ℝ) * cd_cc 3 C')
      = lp3V C' ξ * cd_cc 3 C + e * ((cd_cc 3 C : ℝ) * cd_cc 3 C') := by field_simp
  rw [e1, e2] at h1
  nlinarith

lemma lp3Lin_combL (C : List (List Bool)) (rows : List (List (List Bool) × ℕ))
    (ξ : Fin 3 → Fin 8 → ℝ) :
    lp3Lin (lp3CombL C rows) ξ = (rows.map fun r => (r.2 : ℝ) * lp3Lin (lp3Row C r.1) ξ).sum := by
  induction rows with
  | nil => simp [lp3CombL, lp3Lin]
  | cons a l ih =>
    have e : lp3CombL C (a :: l) = fun q => (a.2 : ℤ) * lp3Row C a.1 q + lp3CombL C l q := by
      funext q; simp [lp3CombL]
    rw [e, lp3Lin_add, lp3Lin_smul, ih]
    simp

/-- The weighted rows are bounded below by `-8 e Λ`. -/
lemma lp3_combL_lower (C : List (List Bool)) (rows : List (List (List Bool) × ℕ))
    {ξ : Fin 3 → Fin 8 → ℝ} {e : ℝ} (hc : 0 < cd_cc 3 C)
    (hrows : ∀ r ∈ rows, r.1 ∈ profiles3 ∧ 0 < cd_cc 3 r.1)
    (hmin : ∀ C' ∈ profiles3, lp3V C ξ / cd_cc 3 C ≤ lp3V C' ξ / cd_cc 3 C' + e) :
    -(8 * e * (lp3LamL C rows : ℝ)) ≤ lp3Lin (lp3CombL C rows) ξ := by
  rw [lp3Lin_combL]
  induction rows with
  | nil => simp [lp3LamL]
  | cons a l ih =>
    have ha := lp3_row_lower hc (hrows a List.mem_cons_self).2 (hmin a.1 (hrows a List.mem_cons_self).1)
    have hl := ih fun r hr => hrows r (List.mem_cons_of_mem _ hr)
    simp only [lp3LamL, List.map_cons, List.sum_cons] at hl ⊢
    push_cast at hl ⊢
    have hw : (0 : ℝ) ≤ a.2 := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left ha hw]

/-- **Soundness of a certificate** (general target form `f`, value row weight `ν`):
on the box, if `c.C` is a minimiser up to `e` and `L ≤ v_C`, then
`wF · ⟨f, ξ⟩ ≤ U - 8 ν L + 8 e Λ`. -/
theorem lp3_gen_sound (c : LP3Cert) (f : ℕ → ℤ) (hok : lp3RowsOK c = true)
    {ξ : Fin 3 → Fin 8 → ℝ} (hbox : ∀ i u, 0 ≤ ξ i u ∧ ξ i u ≤ 1) {e : ℝ}
    (hmin : ∀ C' ∈ profiles3, lp3V c.C ξ / cd_cc 3 c.C ≤ lp3V C' ξ / cd_cc 3 C' + e)
    {L : ℝ} (hL : L ≤ lp3V c.C ξ) :
    (c.wF : ℝ) * lp3Lin f ξ ≤ (lp3U c f : ℝ) - 8 * c.nu * L + 8 * e * lp3LamL c.C c.rows := by
  simp only [lp3RowsOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨_, hc⟩, hrows⟩ := hok
  have hrows' : ∀ r ∈ c.rows, r.1 ∈ profiles3 ∧ 0 < cd_cc 3 r.1 := fun r hr => by
    have := hrows r hr
    exact ⟨lp3_mem_of_contains this.1, this.2⟩
  have hW : lp3Lin (lp3W c f) ξ ≤ (lp3U c f : ℝ) := lp3Lin_le_pos (lp3W c f) hbox
  have hlin : lp3Lin (lp3W c f) ξ
      = c.wF * lp3Lin f ξ + lp3Lin (lp3CombL c.C c.rows) ξ + c.nu * (8 * lp3V c.C ξ) := by
    have eW : lp3W c f = fun q => ((c.wF : ℤ) * f q + lp3CombL c.C c.rows q)
        + (c.nu : ℤ) * cd_fz 3 c.C 0 q := rfl
    rw [eW, lp3Lin_add, lp3Lin_add, lp3Lin_smul, lp3Lin_smul, lp3V_lin]
    push_cast
    ring
  have hcomb := lp3_combL_lower c.C c.rows hc hrows' hmin
  have hnu : (0 : ℝ) ≤ c.nu := Nat.cast_nonneg _
  have h2 : (c.nu : ℝ) * L ≤ c.nu * lp3V c.C ξ := mul_le_mul_of_nonneg_left hL hnu
  rw [hlin] at hW
  linarith

/-! ### The 21 certificates: `v_C ≤ 5/3 + (40/3) e` -/

/-- The check of a bound certificate: `ν = 0`, `3 U ≤ 40 wF`, `3 Λ ≤ 40 wF`. -/
def lp3Check (c : LP3Cert) : Bool :=
  lp3RowsOK c && (c.nu == 0) && decide (3 * lp3U c (cd_fz 3 c.C 0) ≤ 40 * c.wF) &&
    decide (3 * lp3LamL c.C c.rows ≤ 40 * c.wF)

theorem lp3_check_sound (c : LP3Cert) (hc : lp3Check c = true) {ξ : Fin 3 → Fin 8 → ℝ}
    (hbox : ∀ i u, 0 ≤ ξ i u ∧ ξ i u ≤ 1) {e : ℝ} (he : 0 ≤ e)
    (hmin : ∀ C' ∈ profiles3, lp3V c.C ξ / cd_cc 3 c.C ≤ lp3V C' ξ / cd_cc 3 C' + e) :
    lp3V c.C ξ ≤ 5 / 3 + 40 / 3 * e := by
  simp only [lp3Check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨hok, hnu⟩, hU⟩, hLam⟩ := hc
  have h := lp3_gen_sound c (cd_fz 3 c.C 0) hok hbox hmin (le_refl (lp3V c.C ξ))
  rw [lp3V_lin, hnu] at h
  have hw : (0 : ℝ) < c.wF := by
    simp only [lp3RowsOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact_mod_cast hok.1.1
  have hU' : 3 * (lp3U c (cd_fz 3 c.C 0) : ℝ) ≤ 40 * c.wF := by exact_mod_cast hU
  have hL' : 3 * (lp3LamL c.C c.rows : ℝ) ≤ 40 * c.wF := by exact_mod_cast hLam
  have h4 := mul_le_mul_of_nonneg_left hL' he
  push_cast at h
  have h3 : (c.wF : ℝ) * (24 * lp3V c.C ξ) ≤ c.wF * (40 + 320 * e) := by nlinarith
  have h5 := le_of_mul_le_mul_left h3 hw
  linarith

/-- The kernel check over all 21 non-all-cut profiles. -/
def lp3AllOK : Bool :=
  profiles3.all fun C => (C == lp3AllCut) || lp3Certs.any fun c => (c.C == C) && lp3Check c

theorem lp3AllOK_true : lp3AllOK = true := by decide +kernel

/-- **The triple LP bound (sharp constant).**  A non-all-cut profile that minimises `lp3V / cc` up
to `e` on the box has value at most `5/3 + (40/3) e`. -/
theorem lp3_bound_sharp {C : List (List Bool)} (hC : C ∈ profiles3) (hne : C ≠ lp3AllCut)
    {ξ : Fin 3 → Fin 8 → ℝ} (hbox : ∀ i u, 0 ≤ ξ i u ∧ ξ i u ≤ 1) {e : ℝ} (he : 0 ≤ e)
    (hmin : ∀ C' ∈ profiles3, lp3V C ξ / cd_cc 3 C ≤ lp3V C' ξ / cd_cc 3 C' + e) :
    lp3V C ξ ≤ 5 / 3 + 40 / 3 * e := by
  have h := lp3AllOK_true
  simp only [lp3AllOK, List.all_eq_true] at h
  have hC' := h C hC
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true] at hC'
  rcases hC' with h1 | ⟨c, _, hcC, hchk⟩
  · exact absurd h1 hne
  · subst hcC
    exact lp3_check_sound c hchk hbox he hmin

/-- **The triple LP bound** (the form of the blueprint). -/
theorem lp3_bound {C : List (List Bool)} (hC : C ∈ profiles3) (hne : C ≠ lp3AllCut)
    {ξ : Fin 3 → Fin 8 → ℝ} (hbox : ∀ i u, 0 ≤ ξ i u ∧ ξ i u ≤ 1) {e : ℝ} (he : 0 ≤ e)
    (hmin : ∀ C' ∈ profiles3, lp3V C ξ / cd_cc 3 C ≤ lp3V C' ξ / cd_cc 3 C' + e) :
    lp3V C ξ ≤ 5 / 3 + 40 * e := by
  have := lp3_bound_sharp hC hne hbox he hmin
  linarith

/-- **The triple LP bound for a system partition** of a 3-set `S` ordered by `e`: if the model
value of `θ` (through its table) minimises `value / sysCutCount` over all partitions of `S` up to
`ε`, and `θ` does not have the all-cut profile, then its value is at most `5/3 + (40/3) ε`. -/
theorem lp3_bound_sys {S : Finset (Fin N)} (e : Fin 3 ↪ Fin N) (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
    (θ : SysPartition N S) (hne : ∃ j ∈ S, profile θ j ≠ S.erase j)
    {ξ : Fin 3 → Fin 8 → ℝ} (hbox : ∀ i u, 0 ≤ ξ i u ∧ ξ i u ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hmin : ∀ θ' : SysPartition N S, lp3V (lpTab e hS θ) ξ / sysCutCount θ ≤
      lp3V (lpTab e hS θ') ξ / sysCutCount θ' + ε) :
    lp3V (lpTab e hS θ) ξ ≤ 5 / 3 + 40 / 3 * ε := by
  refine lp3_bound_sharp (lpTab_mem e hS θ) (lpTab_ne_allCut e hS θ hne) hbox hε fun C' hC' => ?_
  obtain ⟨g, δ, hv, rfl⟩ := profiles3_realized C' hC'
  obtain ⟨θ', hθ'⟩ := lpTab_realize e hS g δ hv
  have hv' : lp3V (cd_profOf 3 g δ) ξ = lp3V (lpTab e hS θ') ξ := (lp3V_congr hθ' ξ).symm
  have hcc' : cd_cc 3 (cd_profOf 3 g δ) = sysCutCount θ' := by
    rw [← lp3cc_congr hθ', lpTab_cc]
  rw [hv', hcc', lpTab_cc]
  exact hmin θ'

/-! ### The all-cut profile in the model -/

/-- The single-unit cut of unit `i` (unit `i` loses both others, the others lose nothing). -/
def lp3Single (i : ℕ) : List (List Bool) :=
  (List.range 3).map fun a => (List.range 3).map fun b => (a == i) && (b != i)

theorem lp3Single_mem :
    lp3Single 0 ∈ profiles3 ∧ lp3Single 1 ∈ profiles3 ∧ lp3Single 2 ∈ profiles3 := by
  decide +kernel

theorem lp3Single_cc :
    cd_cc 3 (lp3Single 0) = 2 ∧ cd_cc 3 (lp3Single 1) = 2 ∧ cd_cc 3 (lp3Single 2) = 2 := by
  decide +kernel

lemma lp3_allCut_fz : ∀ q < 24, cd_fz 3 lp3AllCut 0 q =
    cd_fz 3 (lp3Single 0) 0 q + cd_fz 3 (lp3Single 1) 0 q + cd_fz 3 (lp3Single 2) 0 q := by
  have h : (List.range 24).all (fun q => cd_fz 3 lp3AllCut 0 q ==
      cd_fz 3 (lp3Single 0) 0 q + cd_fz 3 (lp3Single 1) 0 q + cd_fz 3 (lp3Single 2) 0 q) = true := by
    decide +kernel
  intro q hq
  rw [List.all_eq_true] at h
  simpa using h q (List.mem_range.2 hq)

/-- **Exact additivity in the model**: `v_all = ∑_i v(single cut i)` (and `cc = 6 = 2 + 2 + 2`). -/
theorem lp3_allCut_model (ξ : Fin 3 → Fin 8 → ℝ) :
    lp3V lp3AllCut ξ = lp3V (lp3Single 0) ξ + lp3V (lp3Single 1) ξ + lp3V (lp3Single 2) ξ := by
  have h := lp3Lin_congr lp3_allCut_fz ξ
  rw [lp3V_lin, lp3Lin_add, lp3Lin_add, lp3V_lin, lp3V_lin, lp3V_lin] at h
  linarith

/-- **The all-cut profile is a near-minimiser only at a near tie**: if it minimises `v / cc` up to
`e`, every single-unit cut ratio is within `2 e` of the all-cut ratio. -/
theorem lp3_allCut_near_tie {ξ : Fin 3 → Fin 8 → ℝ} {e : ℝ}
    (hmin : ∀ C' ∈ profiles3, lp3V lp3AllCut ξ / cd_cc 3 lp3AllCut ≤ lp3V C' ξ / cd_cc 3 C' + e) :
    ∀ i < 3, |lp3V (lp3Single i) ξ / 2 - lp3V lp3AllCut ξ / 6| ≤ 2 * e := by
  obtain ⟨h0, h1, h2⟩ := lp3Single_mem
  obtain ⟨c0, c1, c2⟩ := lp3Single_cc
  have a0 := hmin _ h0
  have a1 := hmin _ h1
  have a2 := hmin _ h2
  rw [lp3AllCut_cc, c0] at a0
  rw [lp3AllCut_cc, c1] at a1
  rw [lp3AllCut_cc, c2] at a2
  have hs := lp3_allCut_model ξ
  push_cast at a0 a1 a2
  intro i hi
  interval_cases i <;> rw [abs_le] <;> constructor <;> linarith

/-! ### The all-cut profile for the real quantities -/

/-- The profile of the single-unit cut `splitAt`. -/
lemma lp_splitAt_profile {S : Finset (Fin N)} {j : Fin N} (hj : j ∈ S)
    (hrest : (S.erase j).Nonempty) :
    ∀ x ∈ S, profile (splitAt hj hrest) x = if x = j then S.erase j else ∅ := by
  intro x hx
  unfold profile
  by_cases h : x = j
  · subst h
    rw [ite_eq_left rfl, splitAt_partOf_j, splitAt_cut_j]
  · rw [ite_eq_right h, splitAt_partOf_rest hj hrest (mem_erase.2 ⟨h, hx⟩), splitAt_cut_rest]

/-- A family of single-unit cuts of `S` (`|S| ≥ 2`). -/
lemma lp_single_family {S : Finset (Fin N)} (hS2 : 2 ≤ S.card) :
    ∃ θ1 : Fin N → SysPartition N S,
      ∀ i ∈ S, ∀ j ∈ S, profile (θ1 i) j = if j = i then S.erase i else ∅ := by
  classical
  have hrest : ∀ i ∈ S, (S.erase i).Nonempty := fun i hi => by
    rw [← card_pos, card_erase_of_mem hi]; omega
  obtain ⟨i0, hi0⟩ : S.Nonempty := card_pos.1 (by omega)
  refine ⟨fun i => if hi : i ∈ S then splitAt hi (hrest i hi) else splitAt hi0 (hrest i0 hi0),
    fun i hi j hj => ?_⟩
  simp only [dite_eq_left hi]
  exact lp_splitAt_profile hi (hrest i hi) j hj

lemma lp_prod_div_single {S : Finset (Fin N)} (a : Fin N → ℝ) (b : ℝ) {i : Fin N} (hi : i ∈ S)
    (ha : ∀ j ∈ S, a j ≠ 0) :
    (∏ j ∈ S, a j) / ∏ j ∈ S, (if j = i then b else a j) = a i / b := by
  rw [← mul_prod_erase S a hi, ← mul_prod_erase S (fun j => if j = i then b else a j) hi]
  rw [ite_eq_left rfl]
  have hE : ∏ j ∈ S.erase i, (if j = i then b else a j) = ∏ j ∈ S.erase i, a j :=
    prod_congr rfl fun j hj => ite_eq_right (ne_of_mem_erase hj)
  rw [hE]
  exact mul_div_mul_right _ _ (prod_ne_zero_iff.2 fun j hj => ha j (mem_of_mem_erase hj))

/-- Additivity of the log-ratio over the single-unit cuts, for factors `F X j` (unit `j`, cut set
`X`) of the unpartitioned (`X = ∅`) and partitioned products. -/
lemma lp_allCut_logb_gen {S : Finset (Fin N)} (F : Finset (Fin N) → Fin N → ℝ)
    (hpos : ∀ j ∈ S, 0 < F ∅ j ∧ 0 < F (S.erase j) j)
    (θA : SysPartition N S) (hA : ∀ j ∈ S, profile θA j = S.erase j)
    (θ1 : Fin N → SysPartition N S)
    (h1 : ∀ i ∈ S, ∀ j ∈ S, profile (θ1 i) j = if j = i then S.erase i else ∅) :
    Real.logb 2 ((∏ j ∈ S, F ∅ j) / ∏ j ∈ S, F (profile θA j) j) =
      ∑ i ∈ S, Real.logb 2 ((∏ j ∈ S, F ∅ j) / ∏ j ∈ S, F (profile (θ1 i) j) j) := by
  have hA' : ∏ j ∈ S, F (profile θA j) j = ∏ j ∈ S, F (S.erase j) j :=
    prod_congr rfl fun j hj => by rw [hA j hj]
  have h1' : ∀ i ∈ S, ∏ j ∈ S, F (profile (θ1 i) j) j
      = ∏ j ∈ S, (if j = i then F (S.erase i) i else F ∅ j) := fun i hi =>
    prod_congr rfl fun j hj => by
      rw [h1 i hi j hj]
      split_ifs with h
      · rw [h]
      · rfl
  rw [hA', ← prod_div_distrib,
    Real.logb_prod _ _ fun j hj => (div_pos (hpos j hj).1 (hpos j hj).2).ne']
  refine sum_congr rfl fun i hi => ?_
  rw [h1' i hi, lp_prod_div_single (F ∅) _ hi fun j hj => (hpos j hj).1.ne']

/-- **Cause side**: the log-ratio of the all-cut partition is the sum of those of the single-unit
cuts (same subcubes). -/
theorem allCut_logb_cause {z : Param N} (hz : z ∈ openCube N) (s : State N) {S : Finset (Fin N)}
    (θA : SysPartition N S) (hA : ∀ j ∈ S, profile θA j = S.erase j)
    (θ1 : Fin N → SysPartition N S)
    (h1 : ∀ i ∈ S, ∀ j ∈ S, profile (θ1 i) j = if j = i then S.erase i else ∅) (t : State N) :
    Real.logb 2 (sysCauseProb (tpmOf z) S s s t / sysPartCauseProb (tpmOf z) S s θA s t) =
      ∑ i ∈ S, Real.logb 2 (sysCauseProb (tpmOf z) S s s t /
        sysPartCauseProb (tpmOf z) S s (θ1 i) s t) := by
  set F : Finset (Fin N) → Fin N → ℝ := fun X j =>
    (∑ w : State N, effUnit (tpmOf z) Xᶜ (merge S t w) j (s j) * bgWeight (tpmOf z) S s w)
      / 2 ^ S.card with hF
  have hP : sysCauseProb (tpmOf z) S s s t = ∏ j ∈ S, F ∅ j := by
    unfold sysCauseProb
    refine prod_congr rfl fun j _ => ?_
    simp only [hF, compl_empty, effUnit_univ_prob]
  have hQ : ∀ θ : SysPartition N S,
      sysPartCauseProb (tpmOf z) S s θ s t = ∏ j ∈ S, F (profile θ j) j := fun θ => rfl
  have hpos : ∀ X j, 0 < F X j := fun X j =>
    div_pos (sum_pos (fun w _ => mul_pos (effUnit_pos hz _ _ _ _) (bgWeight_pos hz s S w))
      univ_nonempty) (by positivity)
  simp only [hP, hQ]
  exact lp_allCut_logb_gen F (fun j _ => ⟨hpos _ _, hpos _ _⟩) θA hA θ1 h1

/-- **Effect side**: the same additivity for the effect log-ratio. -/
theorem allCut_logb_effect {z : Param N} (hz : z ∈ openCube N) (s : State N) {S : Finset (Fin N)}
    (θA : SysPartition N S) (hA : ∀ j ∈ S, profile θA j = S.erase j)
    (θ1 : Fin N → SysPartition N S)
    (h1 : ∀ i ∈ S, ∀ j ∈ S, profile (θ1 i) j = if j = i then S.erase i else ∅) (t : State N) :
    Real.logb 2 (sysEffProb (tpmOf z) S s s t / sysPartEffProb (tpmOf z) S s θA s t) =
      ∑ i ∈ S, Real.logb 2 (sysEffProb (tpmOf z) S s s t /
        sysPartEffProb (tpmOf z) S s (θ1 i) s t) := by
  set F : Finset (Fin N) → Fin N → ℝ := fun X j => effUnit (tpmOf z) Xᶜ (merge S s s) j (t j) with hF
  have hP : sysEffProb (tpmOf z) S s s t = ∏ j ∈ S, F ∅ j := by
    unfold sysEffProb
    refine prod_congr rfl fun j _ => ?_
    simp only [hF, compl_empty, effUnit_univ_prob]
  have hQ : ∀ θ : SysPartition N S,
      sysPartEffProb (tpmOf z) S s θ s t = ∏ j ∈ S, F (profile θ j) j := fun θ => rfl
  have hpos : ∀ X j, 0 < F X j := fun X j => effUnit_pos hz _ _ _ _
  simp only [hP, hQ]
  exact lp_allCut_logb_gen F (fun j _ => ⟨hpos _ _, hpos _ _⟩) θA hA θ1 h1

lemma lp_pos_of_mul {B x : ℝ} (h : 0 < B * pos x) : 0 < x := by
  by_contra hx
  push Not at hx
  have : pos x = 0 := by unfold pos; exact max_eq_left hx
  rw [this, mul_zero] at h
  exact lt_irrefl _ h

lemma lp_pos_eq {x : ℝ} (hx : 0 ≤ x) : pos x = x := by
  unfold pos; exact max_eq_right hx

/-- **The all-cut partition is a minimum information partition only at an exact tie.**  For any
`S` (open cube, background = current state): if the all-cut partition `θA` lies in the MIP set at
`(tc, te)` with a positive value, then every single-unit cut has value `φ(θA) / |S|`.  Hence all
single-unit cut values are equal and positive (`allCut_mip_tie'`). -/
theorem allCut_mip_tie {z : Param N} (hz : z ∈ openCube N) (s : State N) {S : Finset (Fin N)}
    (θA : SysPartition N S) (hA : ∀ j ∈ S, profile θA j = S.erase j)
    (θ1 : Fin N → SysPartition N S)
    (h1 : ∀ i ∈ S, ∀ j ∈ S, profile (θ1 i) j = if j = i then S.erase i else ∅)
    (tc te : State N) (hmip : θA ∈ sysMipSetAt (tpmOf z) S s s tc te)
    (hpos : 0 < sysPhiAt (tpmOf z) S s θA s tc te) :
    ∀ i ∈ S, sysPhiAt (tpmOf z) S s θA s tc te =
      (S.card : ℝ) * sysPhiAt (tpmOf z) S s (θ1 i) s tc te := by
  set T := tpmOf z with hT
  -- cut counts
  have hccA : sysCutCount θA = S.card * (S.card - 1) := by
    rw [sysCutCount_eq_sum_profile, sum_congr rfl fun j hj => by rw [hA j hj, card_erase_of_mem hj],
      sum_const, smul_eq_mul]
  have hcc1 : ∀ i ∈ S, sysCutCount (θ1 i) = S.card - 1 := by
    intro i hi
    rw [sysCutCount_eq_sum_profile, sum_congr rfl fun j hj => by rw [h1 i hi j hj],
      Finset.sum_eq_single i (fun j _ hji => by rw [ite_eq_right hji, card_empty]) (fun h => absurd hi h),
      ite_eq_left rfl, card_erase_of_mem hi]
  have h0 : 0 < S.card * (S.card - 1) := hccA ▸ sysCutCount_pos θA
  have hn : 0 < S.card := by
    rcases Nat.eq_zero_or_pos S.card with h | h
    · rw [h, zero_mul] at h0; exact absurd h0 (lt_irrefl 0)
    · exact h
  have hm : 0 < S.card - 1 := by
    rcases Nat.eq_zero_or_pos (S.card - 1) with h | h
    · rw [h, mul_zero] at h0; exact absurd h0 (lt_irrefl 0)
    · exact h
  have hn' : (0 : ℝ) < S.card := by exact_mod_cast hn
  have hm' : (0 : ℝ) < ((S.card - 1 : ℕ) : ℝ) := by exact_mod_cast hm
  set ph : SysPartition N S → ℝ := fun θ => sysPhiAt T S s θ s tc te with hph
  -- the MIP inequality against each single cut
  have hle : ∀ i ∈ S, ph θA ≤ S.card * ph (θ1 i) := by
    intro i hi
    have hmin := (mem_argminSet.1 hmip) (θ1 i)
    unfold normalizedSysPhiAt at hmin
    rw [hccA, hcc1 i hi] at hmin
    push_cast at hmin
    rw [div_le_div_iff₀ (by positivity) hm'] at hmin
    have : ph θA * ((S.card - 1 : ℕ) : ℝ) ≤ (S.card * ph (θ1 i)) * ((S.card - 1 : ℕ) : ℝ) := by
      simp only [hph]; nlinarith
    exact le_of_mul_le_mul_right this hm'
  -- decomposition into cause and effect sides
  set B := sysBackCause T S s s tc
  set E := sysEffProb T S s s te
  set LC : SysPartition N S → ℝ := fun θ =>
    Real.logb 2 (sysCauseProb T S s s tc / sysPartCauseProb T S s θ s tc) with hLC
  set LE : SysPartition N S → ℝ := fun θ =>
    Real.logb 2 (sysEffProb T S s s te / sysPartEffProb T S s θ s te) with hLE
  have hdec : ∀ θ, ph θ = min (B * pos (LC θ)) (E * pos (LE θ)) := fun θ => rfl
  have hphi_pos : ∀ i ∈ S, 0 < ph (θ1 i) := by
    intro i hi
    have := hle i hi
    by_contra hc
    push Not at hc
    nlinarith
  have hLpos : ∀ i ∈ S, 0 < LC (θ1 i) ∧ 0 < LE (θ1 i) := by
    intro i hi
    have h := hphi_pos i hi
    rw [hdec, lt_min_iff] at h
    exact ⟨lp_pos_of_mul h.1, lp_pos_of_mul h.2⟩
  have hLCA : LC θA = ∑ i ∈ S, LC (θ1 i) := allCut_logb_cause hz s θA hA θ1 h1 tc
  have hLEA : LE θA = ∑ i ∈ S, LE (θ1 i) := allCut_logb_effect hz s θA hA θ1 h1 te
  have hphA : ph θA = min (B * ∑ i ∈ S, LC (θ1 i)) (E * ∑ i ∈ S, LE (θ1 i)) := by
    rw [hdec, hLCA, hLEA,
      lp_pos_eq (sum_nonneg fun i hi => (hLpos i hi).1.le),
      lp_pos_eq (sum_nonneg fun i hi => (hLpos i hi).2.le)]
  have hphi : ∀ i ∈ S, ph (θ1 i) = min (B * LC (θ1 i)) (E * LE (θ1 i)) := by
    intro i hi
    rw [hdec, lp_pos_eq (hLpos i hi).1.le, lp_pos_eq (hLpos i hi).2.le]
  -- superadditivity
  have hsum : ∑ i ∈ S, ph (θ1 i) ≤ ph θA := by
    rw [hphA]
    refine le_min ?_ ?_
    · rw [mul_sum]
      exact sum_le_sum fun i hi => by rw [hphi i hi]; exact min_le_left _ _
    · rw [mul_sum]
      exact sum_le_sum fun i hi => by rw [hphi i hi]; exact min_le_right _ _
  -- the minimum single cut
  obtain ⟨i0, hi0S⟩ : S.Nonempty := card_pos.1 hn
  obtain ⟨j0, hj0, hj0min⟩ := S.exists_min_image (fun i => ph (θ1 i)) ⟨i0, hi0S⟩
  have hnonneg : ∀ i ∈ S, 0 ≤ ph (θ1 i) - ph (θ1 j0) := fun i hi => sub_nonneg.2 (hj0min i hi)
  have hsum0 : ∑ i ∈ S, (ph (θ1 i) - ph (θ1 j0)) = 0 := by
    refine le_antisymm ?_ (sum_nonneg hnonneg)
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
    have := hle j0 hj0
    linarith
  have heq : ∀ i ∈ S, ph (θ1 i) = ph (θ1 j0) := fun i hi =>
    sub_eq_zero.1 ((sum_eq_zero_iff_of_nonneg hnonneg).1 hsum0 i hi)
  have hsumv : ∑ i ∈ S, ph (θ1 i) = S.card * ph (θ1 j0) := by
    rw [sum_congr rfl heq, sum_const, nsmul_eq_mul]
  have hA0 : ph θA = S.card * ph (θ1 j0) := le_antisymm (hle j0 hj0) (hsumv ▸ hsum)
  intro i hi
  show ph θA = S.card * ph (θ1 i)
  rw [hA0, heq i hi]

/-- The exact tie: all single-unit cut values are equal and positive. -/
theorem allCut_mip_tie' {z : Param N} (hz : z ∈ openCube N) (s : State N) {S : Finset (Fin N)}
    (θA : SysPartition N S) (hA : ∀ j ∈ S, profile θA j = S.erase j)
    (θ1 : Fin N → SysPartition N S)
    (h1 : ∀ i ∈ S, ∀ j ∈ S, profile (θ1 i) j = if j = i then S.erase i else ∅)
    (tc te : State N) (hmip : θA ∈ sysMipSetAt (tpmOf z) S s s tc te)
    (hpos : 0 < sysPhiAt (tpmOf z) S s θA s tc te) :
    ∀ i ∈ S, ∀ j ∈ S,
      sysPhiAt (tpmOf z) S s (θ1 i) s tc te = sysPhiAt (tpmOf z) S s (θ1 j) s tc te ∧
      0 < sysPhiAt (tpmOf z) S s (θ1 i) s tc te := by
  have h := allCut_mip_tie hz s θA hA θ1 h1 tc te hmip hpos
  intro i hi j hj
  have hn : (0 : ℝ) < S.card := by
    have : 0 < S.card := card_pos.2 ⟨i, hi⟩
    exact_mod_cast this
  have hi' := h i hi
  have hj' := h j hj
  constructor
  · have : (S.card : ℝ) * sysPhiAt (tpmOf z) S s (θ1 i) s tc te
        = S.card * sysPhiAt (tpmOf z) S s (θ1 j) s tc te := by rw [← hi', ← hj']
    exact mul_left_cancel₀ hn.ne' this
  · by_contra hc
    push Not at hc
    nlinarith

/-! ### The interior point `q(t)` (W2, Lemma LP-q) -/

/-- The private roles of `q(t)`: `p[0,{2}]`, `p[1,{0,2}]`, `p[2,{0,1}]` (units `a, b, c = 0, 1, 2`,
patterns `4, 5, 3`). -/
def lp3QRole (i u : ℕ) : Bool := (i == 0 && u == 4) || (i == 1 && u == 5) || (i == 2 && u == 3)

/-- The point `q(t)`: `y = 1`, the three roles `1/3 + t`, every other entry `0`. -/
noncomputable def lp3Q (t : ℝ) (i : Fin 3) (u : Fin 8) : ℝ :=
  if (u : ℕ) = 0 then 1 else if lp3QRole i u = true then 1 / 3 + t else 0

/-- Integer data of `q(t) = n0/3 + t n1`. -/
def lp3QN0 (q : ℕ) : ℤ := if q % 8 = 0 then 3 else if lp3QRole (q / 8) (q % 8) then 1 else 0

/-- Integer data of `q(t) = n0/3 + t n1`. -/
def lp3QN1 (q : ℕ) : ℤ := if q % 8 = 0 then 0 else if lp3QRole (q / 8) (q % 8) then 1 else 0

lemma lp3Q_eq (t : ℝ) (i : Fin 3) (u : Fin 8) :
    lp3Q t i u = (lp3QN0 (u + 8 * i) : ℝ) / 3 + t * lp3QN1 (u + 8 * i) := by
  have h1 : ((u : ℕ) + 8 * (i : ℕ)) % 8 = u := by have := u.2; omega
  have h2 : ((u : ℕ) + 8 * (i : ℕ)) / 8 = i := by have := u.2; omega
  unfold lp3Q lp3QN0 lp3QN1
  rw [h1, h2]
  split_ifs <;> push_cast <;> ring

lemma lp3Lin_Q (a : ℕ → ℤ) (t : ℝ) :
    lp3Lin a (lp3Q t) = (lp3Sum (fun q => a q * lp3QN0 q) : ℝ) / 3
      + t * lp3Sum (fun q => a q * lp3QN1 q) := by
  rw [lp3Sum_cast, lp3Sum_cast]
  unfold lp3Lin
  simp only [lp3Q_eq]
  push_cast
  rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun u _ => ?_
  ring

/-- The check that `⟨f, q(t)⟩ + k0/3 + k1 t ≥ 0` at `t = 0` and `t = 2/3`. -/
def lp3TCheck (f : ℕ → ℤ) (k0 k1 : ℤ) : Bool :=
  decide (0 ≤ lp3Sum (fun q => f q * lp3QN0 q) + k0) &&
    decide (0 ≤ (lp3Sum (fun q => f q * lp3QN0 q) + k0)
      + 2 * (lp3Sum (fun q => f q * lp3QN1 q) + k1))

lemma lp3TCheck_sound {f : ℕ → ℤ} {k0 k1 : ℤ} (h : lp3TCheck f k0 k1 = true) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 2 / 3) :
    0 ≤ lp3Lin f (lp3Q t) + k0 / 3 + k1 * t := by
  simp only [lp3TCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hA, hAB⟩ := h
  rw [lp3Lin_Q]
  set s0 := lp3Sum (fun q => f q * lp3QN0 q)
  set s1 := lp3Sum (fun q => f q * lp3QN1 q)
  have hA' : (0 : ℝ) ≤ (s0 : ℝ) + k0 := by exact_mod_cast hA
  have hAB' : (0 : ℝ) ≤ ((s0 : ℝ) + k0) + 2 * ((s1 : ℝ) + k1) := by exact_mod_cast hAB
  have h1 := mul_nonneg hA' (by linarith : (0 : ℝ) ≤ 1 - 3 * t / 2)
  have h2 := mul_nonneg hAB' ht0
  nlinarith

/-- The gap form `25 a_C - 5 cc_C a_{C*}` (`= 200 v_C - 40 cc_C v_{C*}`). -/
def lp3GapF (C : List (List Bool)) (q : ℕ) : ℤ :=
  25 * cd_fz 3 C 0 q - 5 * (cd_cc 3 C : ℤ) * cd_fz 3 lp3CStar 0 q

/-- The kernel check of Lemma LP-q. -/
def lp3QOK : Bool :=
  (lp3Sum (fun q => cd_fz 3 lp3CStar 0 q * lp3QN0 q) == 40) &&
  (lp3Sum (fun q => cd_fz 3 lp3CStar 0 q * lp3QN1 q) == -8) &&
  profiles3.all fun C =>
    ((C == lp3CStar) || lp3TCheck (lp3GapF C) 0 (-15 * (cd_cc 3 C : ℤ))) &&
      lp3TCheck (cd_fz 3 C 0) (-16) 2

theorem lp3QOK_true : lp3QOK = true := by decide +kernel

/-- **Lemma LP-q (the interior point).**  For `0 ≤ t ≤ 2/3`: `v_{C*}(q(t)) = 5/3 - t`, every other
profile satisfies `v_C / cc_C ≥ v_{C*}/5 + 3t/40` (so `C*` is the strict minimiser for `t > 0`), and
every profile has value `≥ 2/3 - t/4`. -/
theorem lp3_interior {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 2 / 3) :
    lp3V lp3CStar (lp3Q t) = 5 / 3 - t ∧
    (∀ C ∈ profiles3, C ≠ lp3CStar →
      lp3V lp3CStar (lp3Q t) / 5 + 3 * t / 40 ≤ lp3V C (lp3Q t) / cd_cc 3 C) ∧
    (∀ C ∈ profiles3, 2 / 3 - t / 4 ≤ lp3V C (lp3Q t)) := by
  have h := lp3QOK_true
  simp only [lp3QOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨e0, e1⟩, hall⟩ := h
  have hv : lp3V lp3CStar (lp3Q t) = 5 / 3 - t := by
    have hq := lp3Lin_Q (cd_fz 3 lp3CStar 0) t
    rw [lp3V_lin, e0, e1] at hq
    push_cast at hq
    linarith
  refine ⟨hv, fun C hC hne => ?_, fun C hC => ?_⟩
  · have hchk := (hall C hC).1
    rcases hchk with h1 | h1
    · exact absurd h1 hne
    · have key := lp3TCheck_sound h1 ht0 ht1
      have hf : lp3Lin (lp3GapF C) (lp3Q t)
          = 25 * (8 * lp3V C (lp3Q t)) - 5 * (cd_cc 3 C : ℝ) * (8 * lp3V lp3CStar (lp3Q t)) := by
        have e : lp3GapF C =
            fun q => 25 * cd_fz 3 C 0 q - (5 * (cd_cc 3 C : ℤ)) * cd_fz 3 lp3CStar 0 q := rfl
        rw [e, lp3Lin_sub, lp3Lin_smul, lp3Lin_smul, lp3V_lin, lp3V_lin]
        push_cast
        ring
      rw [hf] at key
      push_cast at key
      have hcc : (0 : ℝ) < cd_cc 3 C := by exact_mod_cast profiles3_cc_pos C hC
      rw [le_div_iff₀ hcc]
      nlinarith
  · have key := lp3TCheck_sound (hall C hC).2 ht0 ht1
    rw [lp3V_lin] at key
    push_cast at key
    linarith

/-- The sum over units of `q(t)` at a nonzero pattern: `1/3 + t` at the three role patterns, `0`
elsewhere. -/
theorem lp3Q_pattern (t : ℝ) (u : Fin 8) (hu : u ≠ 0) :
    ∑ i : Fin 3, lp3Q t i u = if (u : ℕ) = 3 ∨ (u : ℕ) = 4 ∨ (u : ℕ) = 5 then 1 / 3 + t else 0 := by
  fin_cases u
  · exact absurd rfl hu
  all_goals simp [lp3Q, lp3QRole, Fin.sum_univ_three]

lemma lp3Q_box {t : ℝ} (ht0 : -1 / 3 ≤ t) (ht1 : t ≤ 2 / 3) (i : Fin 3) (u : Fin 8) :
    0 ≤ lp3Q t i u ∧ lp3Q t i u ≤ 1 := by
  unfold lp3Q
  split_ifs <;> constructor <;> linarith

/-! ### Scaling and shifting (`p = y - c (1 - q(t))`) -/

/-- Shape facts of the 22 forms: every unit's coefficients sum to `0`, and a pattern that flips the
unit itself has coefficient `0`. -/
def lp3ShapeOK : Bool :=
  profiles3.all fun C => (List.range 3).all fun i =>
    (cd_nsum 8 (fun u => cd_fz 3 C 0 (u + 8 * i)) == 0) &&
      (List.range 8).all fun u => !(u.testBit i) || (cd_fz 3 C 0 (u + 8 * i) == 0)

theorem lp3ShapeOK_true : lp3ShapeOK = true := by decide +kernel

lemma lp3Lin_scale (a : ℕ → ℤ) (hsum : ∀ i : Fin 3, cd_nsum 8 (fun u => a (u + 8 * i)) = 0)
    (hself : ∀ (i : Fin 3) (u : Fin 8), (u : ℕ).testBit i = true → a (u + 8 * i) = 0)
    {ξ ξ' : Fin 3 → Fin 8 → ℝ} {c : ℝ}
    (h : ∀ (i : Fin 3) (u : Fin 8), (u : ℕ).testBit i = false → ξ i 0 - ξ i u = c * (ξ' i 0 - ξ' i u)) :
    lp3Lin a ξ = c * lp3Lin a ξ' := by
  have hs : ∀ i : Fin 3, ∑ u : Fin 8, (a (u + 8 * i) : ℝ) = 0 := by
    intro i
    have := hsum i
    rw [cd_nsum_eq] at this
    rw [Fin.sum_univ_eq_sum_range (fun u => (a (u + 8 * i) : ℝ)) 8]
    exact_mod_cast this
  have key : ∀ (ζ : Fin 3 → Fin 8 → ℝ) (i : Fin 3), ∑ u : Fin 8, (a (u + 8 * i) : ℝ) * ζ i u
      = ∑ u : Fin 8, (a (u + 8 * i) : ℝ) * (ζ i u - ζ i 0) := by
    intro ζ i
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hs i, zero_mul, sub_zero]
  unfold lp3Lin
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [key ξ i, key ξ' i, mul_sum]
  refine sum_congr rfl fun u _ => ?_
  by_cases hb : (u : ℕ).testBit i = true
  · rw [hself i u hb]; simp
  · have := h i u (by simpa using hb)
    linear_combination (-(a (u + 8 * i) : ℝ)) * this

/-- **Scaling**: if `ξ i 0 - ξ i u = c (ξ' i 0 - ξ' i u)` for every pattern `u` not flipping `i`,
then every profile value scales by `c`. -/
theorem lp3V_scale {C : List (List Bool)} (hC : C ∈ profiles3) {ξ ξ' : Fin 3 → Fin 8 → ℝ} {c : ℝ}
    (h : ∀ (i : Fin 3) (u : Fin 8), (u : ℕ).testBit i = false → ξ i 0 - ξ i u = c * (ξ' i 0 - ξ' i u)) :
    lp3V C ξ = c * lp3V C ξ' := by
  have hk := lp3ShapeOK_true
  simp only [lp3ShapeOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    Bool.or_eq_true, Bool.not_eq_true'] at hk
  have hC' := hk C hC
  have hl := lp3Lin_scale (cd_fz 3 C 0) (fun i => (hC' i i.2).1)
    (fun i u hb => by
      rcases (hC' i i.2).2 u u.2 with h1 | h1
      · rw [hb] at h1; exact absurd h1 (by decide)
      · exact h1) h
  rw [lp3V_lin, lp3V_lin] at hl
  linarith

/-- **Lemma LP-q at scale `c`** (the tc block with targets `p = y - c (1 - q(t))`): values are
`c · v(q(t))`, `C*` beats every other profile by `c · 3t/40` in the ratio, in the multiplicative
form of `tl_triple_lower_gen` by the factor `1 + 9t/40`, and every value is `≥ c (2/3 - t/4)`. -/
theorem lp3_interior_scaled {c t : ℝ} (hc : 0 ≤ c) (ht0 : 0 ≤ t) (ht1 : t ≤ 2 / 3)
    {ξ : Fin 3 → Fin 8 → ℝ}
    (hξ : ∀ (i : Fin 3) (u : Fin 8), (u : ℕ).testBit i = false → ξ i 0 - ξ i u = c * (1 - lp3Q t i u)) :
    lp3V lp3CStar ξ = c * (5 / 3 - t) ∧
    (∀ C ∈ profiles3, C ≠ lp3CStar →
      lp3V lp3CStar ξ / 5 + c * (3 * t / 40) ≤ lp3V C ξ / cd_cc 3 C) ∧
    (∀ C ∈ profiles3, C ≠ lp3CStar →
      (1 + 9 * t / 40) * lp3V lp3CStar ξ / 5 ≤ lp3V C ξ / cd_cc 3 C) ∧
    (∀ C ∈ profiles3, c * (2 / 3 - t / 4) ≤ lp3V C ξ) := by
  obtain ⟨hv, hgap, hlow⟩ := lp3_interior ht0 ht1
  have h' : ∀ (i : Fin 3) (u : Fin 8), (u : ℕ).testBit i = false →
      ξ i 0 - ξ i u = c * (lp3Q t i 0 - lp3Q t i u) := by
    intro i u hb
    have : lp3Q t i 0 = 1 := by simp [lp3Q]
    rw [this]
    exact hξ i u hb
  have hs : ∀ C ∈ profiles3, lp3V C ξ = c * lp3V C (lp3Q t) := fun C hC => lp3V_scale hC h'
  have hvs : lp3V lp3CStar ξ = c * (5 / 3 - t) := by rw [hs _ lp3CStar_mem, hv]
  have hgap' : ∀ C ∈ profiles3, C ≠ lp3CStar →
      lp3V lp3CStar ξ / 5 + c * (3 * t / 40) ≤ lp3V C ξ / cd_cc 3 C := by
    intro C hC hne
    have := mul_le_mul_of_nonneg_left (hgap C hC hne) hc
    rw [hs C hC, hs _ lp3CStar_mem, mul_div_assoc c (lp3V C (lp3Q t)),
      mul_div_assoc c (lp3V lp3CStar (lp3Q t))]
    rw [mul_add] at this
    linarith
  refine ⟨hvs, hgap', fun C hC hne => ?_, fun C hC => ?_⟩
  · have := hgap' C hC hne
    rw [hvs] at this ⊢
    have h2 : 9 * t / 40 * (c * (5 / 3 - t)) / 5 ≤ c * (3 * t / 40) := by
      nlinarith [mul_nonneg hc (sq_nonneg t), mul_nonneg hc ht0]
    have e : (1 + 9 * t / 40) * (c * (5 / 3 - t)) / 5
        = c * (5 / 3 - t) / 5 + 9 * t / 40 * (c * (5 / 3 - t)) / 5 := by ring
    rw [e]
    linarith
  · rw [hs C hC]
    exact mul_le_mul_of_nonneg_left (hlow C hC) hc

/-! ### The near-optimal range of the pair-private coordinates -/

/-- The pattern flipping exactly the cut set of unit `i`. -/
def lp3Mask (C : List (List Bool)) (i : ℕ) : ℕ :=
  (if cd_at C i 0 then 1 else 0) + (if cd_at C i 1 then 2 else 0) + (if cd_at C i 2 then 4 else 0)

/-- The coordinate functional. -/
def lp3Unit (q0 q : ℕ) : ℤ := if q = q0 then 1 else 0

lemma lp3Lin_unit (i : Fin 3) (u : Fin 8) (ξ : Fin 3 → Fin 8 → ℝ) :
    lp3Lin (lp3Unit (u + 8 * i)) ξ = ξ i u := by
  unfold lp3Lin lp3Unit
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single u]
    · simp
    · intro u' _ hu'
      rw [ite_eq_right]
      · simp
      · intro h
        apply hu'
        ext
        omega
    · simp
  · intro i' _ hi'
    refine sum_eq_zero fun u' _ => ?_
    rw [ite_eq_right]
    · simp
    · intro h
      apply hi'
      ext
      have := u'.2
      have := u.2
      omega
  · simp

/-- The check of a range certificate for the coordinate `q0`:
`5 (U - 8 ν (5/3 - 1/100)) ≤ 2 wF` and `8 (Λ + ν) ≤ 9 wF`. -/
def lp3RangeCheck (c : LP3Cert) (q0 : ℕ) : Bool :=
  lp3RowsOK c && decide (1500 * lp3U c (lp3Unit q0) - 19880 * (c.nu : ℤ) ≤ 600 * (c.wF : ℤ)) &&
    decide (8 * (lp3LamL c.C c.rows + c.nu) ≤ 9 * c.wF)

theorem lp3_range_sound (c : LP3Cert) (q0 : ℕ) (hc : lp3RangeCheck c q0 = true) (i : Fin 3)
    (u : Fin 8) (hq : q0 = u + 8 * i) {ξ : Fin 3 → Fin 8 → ℝ}
    (hbox : ∀ i u, 0 ≤ ξ i u ∧ ξ i u ≤ 1) {e : ℝ} (he : 0 ≤ e)
    (hmin : ∀ C' ∈ profiles3, lp3V c.C ξ / cd_cc 3 c.C ≤ lp3V C' ξ / cd_cc 3 C' + e)
    (hval : 5 / 3 - 1 / 100 - e ≤ lp3V c.C ξ) :
    ξ i u ≤ 2 / 5 + 9 * e := by
  simp only [lp3RangeCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hok, hU⟩, hLam⟩ := hc
  have h := lp3_gen_sound c (lp3Unit q0) hok hbox hmin hval
  rw [hq, lp3Lin_unit] at h
  have hw : (0 : ℝ) < c.wF := by
    simp only [lp3RowsOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact_mod_cast hok.1.1
  have hU' : 1500 * (lp3U c (lp3Unit q0) : ℝ) - 19880 * c.nu ≤ 600 * c.wF := by exact_mod_cast hU
  have hL' : 8 * ((lp3LamL c.C c.rows : ℝ) + c.nu) ≤ 9 * c.wF := by exact_mod_cast hLam
  have h4 := mul_le_mul_of_nonneg_left hL' he
  rw [← hq] at h
  have h3 : (c.wF : ℝ) * ξ i u ≤ c.wF * (2 / 5 + 9 * e) := by nlinarith
  exact le_of_mul_le_mul_left h3 hw

/-- The kernel check over the 6 cc-5 profiles and their units cut from both others. -/
def lp3RangeOK : Bool :=
  profiles3.all fun C => (cd_cc 3 C != 5) || (List.range 3).all fun i =>
    (cd_card 3 C i != 2) || lp3RangeCerts.any fun x =>
      (x.1.C == C) && (x.2 == lp3Mask C i + 8 * i) && lp3RangeCheck x.1 x.2

theorem lp3RangeOK_true : lp3RangeOK = true := by decide +kernel

/-- **The near-optimal range of the pair-private coordinates.**  For a cc-5 profile `C` and a unit
`i` cut from both others, the pair-private coordinate (row `tc` flipped on the two others, column
`i`) is at most `2/5 + 9 e` whenever `C` minimises `v / cc` up to `e` and `v_C ≥ 5/3 - 1/100 - e`.
(The exact supremum at `e = 0` is `0.3493`.) -/
theorem lp3_private_range {C : List (List Bool)} (hC : C ∈ profiles3) (h5 : cd_cc 3 C = 5)
    (i : Fin 3) (hi : cd_card 3 C i = 2) (u : Fin 8) (hu : (u : ℕ) = lp3Mask C i)
    {ξ : Fin 3 → Fin 8 → ℝ} (hbox : ∀ i u, 0 ≤ ξ i u ∧ ξ i u ≤ 1) {e : ℝ} (he : 0 ≤ e)
    (hmin : ∀ C' ∈ profiles3, lp3V C ξ / cd_cc 3 C ≤ lp3V C' ξ / cd_cc 3 C' + e)
    (hval : 5 / 3 - 1 / 100 - e ≤ lp3V C ξ) :
    ξ i u ≤ 2 / 5 + 9 * e := by
  have h := lp3RangeOK_true
  simp only [lp3RangeOK, List.all_eq_true] at h
  have h' := h C hC
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, List.mem_range,
    List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h'
  rcases h' with h1 | h2
  · exact absurd h5 h1
  · rcases h2 i i.2 with h3 | ⟨x, _, ⟨hxC, hxq⟩, hchk⟩
    · exact absurd hi h3
    · subst hxC
      exact lp3_range_sound x.1 x.2 hchk i u (by rw [hxq, hu]) hbox he hmin hval

/-! ### Cut counts of non-all-cut partitions -/

/-- The table is all-cut. -/
def lpIsAllCut (k : ℕ) (C : List (List Bool)) : Bool :=
  (List.range k).all fun i => (List.range k).all fun j => cd_at C i j == (i != j)

lemma lpIsAllCut_sound {k : ℕ} {C : List (List Bool)} (h : lpIsAllCut k C = true) (i j : Fin k) :
    cd_at C i j = true ↔ i ≠ j := by
  simp only [lpIsAllCut, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [h i i.2 j j.2, bne_iff_ne, ne_eq, ne_eq, Fin.val_inj]

theorem cc_le_of_ne_allCut_gen {k : ℕ} (bound : ℕ)
    (hk : (cd_gen k).all (fun x => decide (cd_cc k (cd_profOf k x.1 x.2) ≤ bound) ||
      lpIsAllCut k (cd_profOf k x.1 x.2)) = true)
    {S : Finset (Fin N)} (e : Fin k ↪ Fin N) (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
    (θ : SysPartition N S) (h : ∃ j ∈ S, profile θ j ≠ S.erase j) : sysCutCount θ ≤ bound := by
  obtain ⟨g, δ, hv, htab⟩ := lpTab_valid e hS θ
  have hx := cd_forall_valid k (fun g δ => decide (cd_cc k (cd_profOf k g δ) ≤ bound) ||
    lpIsAllCut k (cd_profOf k g δ)) hk g δ hv
  rw [← lpTab_cc e hS θ, htab]
  rw [Bool.or_eq_true] at hx
  rcases hx with h1 | h2
  · simpa using h1
  · exfalso
    obtain ⟨j, hj, hne⟩ := h
    refine hne (lpTab_allCut_of e hS θ (fun i j => ?_) j hj)
    rw [htab]
    exact lpIsAllCut_sound h2 i j

/-- A partition of a 3-set whose profile is not all-cut has cut count at most `5`. -/
theorem cc_le_five_of_ne_allCut {S : Finset (Fin N)} (hS : S.card = 3) (θ : SysPartition N S)
    (h : ∃ j ∈ S, profile θ j ≠ S.erase j) : sysCutCount θ ≤ 5 := by
  obtain ⟨e, he⟩ := lp_embed hS
  exact cc_le_of_ne_allCut_gen 5 (by decide +kernel) e he θ h

/-- A partition of a 4-set whose profile is not all-cut has cut count at most `11`. -/
theorem cc_le_11_of_ne_allCut {S : Finset (Fin N)} (hS : S.card = 4) (θ : SysPartition N S)
    (h : ∃ j ∈ S, profile θ j ≠ S.erase j) : sysCutCount θ ≤ 11 := by
  obtain ⟨e, he⟩ := lp_embed hS
  exact cc_le_of_ne_allCut_gen 11 (by decide +kernel) e he θ h

end Census
end IIT
