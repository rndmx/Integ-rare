/-
Census: forms, regions and kernel-checkable certificates for the Gaussian rates.

A cut profile of a `k`-set with units `0, …, k-1` is a table `C : List (List Bool)`; entry
`cd_at C i j` says that unit `i` has lost its inputs from unit `j`.  Coordinates of the field are
`p = t + 2^k i` (unit `i`, pattern `t`, bit `q` of `t` = state of unit `q`), as in `GaussGen`.

* `cd_fz k C t` is the integer coefficient vector of `2^k F_C(t)`, where
  `F_C(t)(ξ) = ∑_i (ξ_i(t) - 2^{-|C_i|} ∑_{u agreeing with t off C_i} ξ_i(u))` (`cd_F_eq`);
  `cd_cc k C = ∑_i |C_i|`.
* Profiles are produced from a set partition given by its minimal-representative map `g`
  and a direction code `δ` per block (`0` inputs, `1` outputs, `2` both): `cd_profOf k g δ`;
  admissible pairs are those with `cd_valid k g δ`.
* `cd_region k C0 ε y ξ`: the argmax rows (pattern `0` beats every other pattern up to `ε`), the
  minimiser rows `F_C/cc(C) ≥ F_C0/cc(C0) - ε` for every admissible profile, and `F_C0 ≥ y`.
* Integer mirrors of `C_k` and of the joint covariance (`cd_Cz`, `cd_CJz`) with cast lemmas, and
  the structured quadratic form of `C_k` (`cd_quad_C`).
* A certificate is a list of rows with natural weights and the claimed vector `v`; a Boolean check
  (evaluated by the kernel on integers) implies the half-space inclusion
  `region ⊆ {⟨v, ξ⟩ ≥ h y - Λ ε}` and the rate inequality `L · vᵀ C v ≤ h²`
  (`cd_check_sound`, `cd_checkJ_sound`); degenerate regions carry a Gordan certificate
  (`cd_checkG_sound`).
-/
import IIT.Census.GaussGen

namespace IIT
namespace Census

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ### Computable sums and profile tables -/

/-- `∑_{i < n} f i`, by structural recursion (kernel friendly). -/
def cd_nsum : ℕ → (ℕ → ℤ) → ℤ
  | 0, _ => 0
  | n + 1, f => cd_nsum n f + f n

lemma cd_nsum_eq (n : ℕ) (f : ℕ → ℤ) : cd_nsum n f = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cd_nsum, ih, sum_range_succ]

/-- Number of `j < n` with `f j`. -/
def cd_cnt : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n + 1, f => cd_cnt n f + (if f n then 1 else 0)

lemma cd_cnt_eq (n : ℕ) (f : ℕ → Bool) :
    cd_cnt n f = (univ.filter fun j : Fin n => f j = true).card := by
  rw [card_filter, Fin.sum_univ_eq_sum_range (fun j => if f j = true then 1 else 0)]
  induction n with
  | zero => rfl
  | succ n ih => rw [cd_cnt, ih, sum_range_succ]

/-- Entry `(i, j)` of a profile table. -/
def cd_at (C : List (List Bool)) (i j : ℕ) : Bool := (C.getD i []).getD j false

/-- `|C_i|`. -/
def cd_card (k : ℕ) (C : List (List Bool)) (i : ℕ) : ℕ := cd_cnt k (cd_at C i)

/-- `∑_{i < n} f i` in `ℕ`, by structural recursion. -/
def cd_nsumN : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => cd_nsumN n f + f n

lemma cd_nsumN_eq (n : ℕ) (f : ℕ → ℕ) : cd_nsumN n f = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cd_nsumN, ih, sum_range_succ]

/-- The normaliser `cc(C) = ∑_i |C_i|`. -/
def cd_cc (k : ℕ) (C : List (List Bool)) : ℕ := cd_nsumN k (cd_card k C)

/-! ### Forms -/

/-- `u` agrees with `t` on every unit `q < k` outside the cut row `r`. -/
def cd_agree (k : ℕ) (r : ℕ → Bool) (u t : ℕ) : Bool :=
  (List.range k).all fun q => r q || (u.testBit q == t.testBit q)

lemma cd_agree_iff (k : ℕ) (r : ℕ → Bool) (u t : ℕ) :
    cd_agree k r u t = true ↔ ∀ q < k, r q = false → u.testBit q = t.testBit q := by
  unfold cd_agree
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro h q hq hr
    rcases h q hq with h | h
    · simp [hr] at h
    · exact h
  · intro h q hq
    by_cases hr : r q = true
    · exact Or.inl hr
    · exact Or.inr (h q hq (by simpa using hr))

/-- Integer coefficients of `2^k F_C(t)`: coordinate `p` (unit `p / 2^k`, pattern `p % 2^k`). -/
def cd_fz (k : ℕ) (C : List (List Bool)) (t p : ℕ) : ℤ :=
  (if p % 2 ^ k = t then ((2 ^ k : ℕ) : ℤ) else 0)
    - (if cd_agree k (cd_at C (p / 2 ^ k)) (p % 2 ^ k) t
        then ((2 ^ (k - cd_card k C (p / 2 ^ k)) : ℕ) : ℤ) else 0)

/-- Coefficients of the argmax row `∑_i (ξ_i(0) - ξ_i(t))`. -/
def cd_argc (k t p : ℕ) : ℤ := (if p % 2 ^ k = 0 then 1 else 0) - (if p % 2 ^ k = t then 1 else 0)

section Real

variable (k : ℕ)

/-- The coordinate of unit `i` and pattern `t`. -/
def cd_idx (i : Fin k) (t : Fin (2 ^ k)) : Fin (k * 2 ^ k) := finProdFinEquiv (i, t)

lemma cd_idx_val (i : Fin k) (t : Fin (2 ^ k)) : (cd_idx k i t : ℕ) = t + 2 ^ k * i := rfl

lemma cd_idx_div (i : Fin k) (t : Fin (2 ^ k)) : (cd_idx k i t : ℕ) / 2 ^ k = i := by
  rw [cd_idx_val, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt t.2, zero_add]

lemma cd_idx_mod (i : Fin k) (t : Fin (2 ^ k)) : (cd_idx k i t : ℕ) % 2 ^ k = t := by
  rw [cd_idx_val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt t.2]

lemma gg_unit_idx (i : Fin k) (t : Fin (2 ^ k)) : gg_unit k (cd_idx k i t) = i := by
  simp [gg_unit, cd_idx]

lemma gg_pat_idx (i : Fin k) (t : Fin (2 ^ k)) : gg_pat k (cd_idx k i t) = t := by
  simp [gg_pat, cd_idx]

/-- The linear functional with integer coefficients `c`. -/
noncomputable def cd_lin (c : ℕ → ℤ) (ξ : Fin (k * 2 ^ k) → ℝ) : ℝ := ∑ p : Fin (k * 2 ^ k), (c p : ℝ) * ξ p

/-- The form `F_C(t)`. -/
noncomputable def cd_F (C : List (List Bool)) (t : ℕ) (ξ : Fin (k * 2 ^ k) → ℝ) : ℝ :=
  cd_lin k (cd_fz k C t) ξ / 2 ^ k

lemma cd_lin_reindex (c : ℕ → ℤ) (ξ : Fin (k * 2 ^ k) → ℝ) :
    cd_lin k c ξ = ∑ i : Fin k, ∑ u : Fin (2 ^ k), (c (u + 2 ^ k * i) : ℝ) * ξ (cd_idx k i u) := by
  unfold cd_lin
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin k × Fin (2 ^ k) ≃ _), Fintype.sum_prod_type]
  rfl

lemma cd_lin_add (c d : ℕ → ℤ) (ξ : Fin (k * 2 ^ k) → ℝ) :
    cd_lin k (fun p => c p + d p) ξ = cd_lin k c ξ + cd_lin k d ξ := by
  unfold cd_lin; push_cast; rw [← sum_add_distrib]; exact sum_congr rfl fun _ _ => by ring

lemma cd_lin_sub (c d : ℕ → ℤ) (ξ : Fin (k * 2 ^ k) → ℝ) :
    cd_lin k (fun p => c p - d p) ξ = cd_lin k c ξ - cd_lin k d ξ := by
  unfold cd_lin; push_cast; rw [← sum_sub_distrib]; exact sum_congr rfl fun _ _ => by ring

lemma cd_lin_smul (a : ℤ) (c : ℕ → ℤ) (ξ : Fin (k * 2 ^ k) → ℝ) :
    cd_lin k (fun p => a * c p) ξ = a * cd_lin k c ξ := by
  unfold cd_lin; push_cast; rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring

lemma cd_lin_zero (ξ : Fin (k * 2 ^ k) → ℝ) : cd_lin k (fun _ => 0) ξ = 0 := by
  simp [cd_lin]

/-- The argmax row in coordinates: `∑_i (ξ_i(0) - ξ_i(t))`. -/
theorem cd_lin_argc (t : Fin (2 ^ k)) (ξ : Fin (k * 2 ^ k) → ℝ) :
    cd_lin k (cd_argc k t) ξ
      = ∑ i : Fin k, (ξ (cd_idx k i ⟨0, by positivity⟩) - ξ (cd_idx k i t)) := by
  rw [cd_lin_reindex]
  refine sum_congr rfl fun i _ => ?_
  have e : ∀ u : Fin (2 ^ k), ((u : ℕ) + 2 ^ k * i) % 2 ^ k = u := fun u => by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt u.2]
  simp only [cd_argc, e]
  push_cast
  simp only [sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul]
  congr 1
  · rw [Finset.sum_eq_single (⟨0, by positivity⟩ : Fin (2 ^ k))
      (fun u _ hu => by simp [Fin.val_ne_of_ne hu]) (by simp)]
    simp
  · rw [Finset.sum_eq_single t (fun u _ hu => by simp [Fin.val_ne_of_ne hu]) (by simp)]
    simp

/-- The form in coordinates:
`F_C(t)(ξ) = ∑_i (ξ_i(t) - 2^{-|C_i|} ∑_{u agreeing with t off C_i} ξ_i(u))`. -/
theorem cd_F_eq (C : List (List Bool)) (t : Fin (2 ^ k)) (ξ : Fin (k * 2 ^ k) → ℝ) :
    cd_F k C t ξ = ∑ i : Fin k, (ξ (cd_idx k i t)
      - ((2 : ℝ) ^ cd_card k C i)⁻¹ * ∑ u : Fin (2 ^ k),
          (if cd_agree k (cd_at C i) u t then ξ (cd_idx k i u) else 0)) := by
  rw [cd_F, cd_lin_reindex, sum_div]
  refine sum_congr rfl fun i _ => ?_
  have e : ∀ u : Fin (2 ^ k), ((u : ℕ) + 2 ^ k * i) % 2 ^ k = u := fun u => by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt u.2]
  have e2 : ∀ u : Fin (2 ^ k), ((u : ℕ) + 2 ^ k * i) / 2 ^ k = i := fun u => by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt u.2, zero_add]
  have hc : cd_card k C i ≤ k := by
    rw [cd_card, cd_cnt_eq]
    exact (card_filter_le _ _).trans (by simp)
  simp only [cd_fz, e, e2]
  push_cast
  simp only [sub_mul, sum_sub_distrib, ite_mul, zero_mul]
  have h2 : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  have hs : ∀ a : ℝ, (∑ u : Fin (2 ^ k), if cd_agree k (cd_at C i) u t = true
        then a * ξ (cd_idx k i u) else 0)
      = a * ∑ u : Fin (2 ^ k), if cd_agree k (cd_at C i) u t = true then ξ (cd_idx k i u) else 0 := by
    intro a
    rw [mul_sum]
    exact sum_congr rfl fun u _ => by split_ifs <;> simp
  rw [Finset.sum_eq_single t (fun u _ hu => by simp [Fin.val_ne_of_ne hu]) (by simp)]
  simp only [ite_true]
  rw [hs, pow_sub₀ _ (by norm_num) hc]
  field_simp

end Real

/-! ### Integer mirrors of the covariances -/

section Cov

variable (k m : ℕ)

/-- `240 · 2^k · C_k[p, q]`. -/
def cd_Cz (p q : ℕ) : ℤ :=
  60 * ((2 ^ k : ℕ) + 1) + (if p % 2 ^ k = q % 2 ^ k then 15 else 0)
    + (if p = q then 20 * ((2 ^ k : ℕ) : ℤ) - 11 else 0)

lemma cd_Cz_cast (p q : Fin (k * 2 ^ k)) :
    (cd_Cz k p q : ℝ) = 240 * 2 ^ k * gg_C k p q := by
  have hp : (gg_pat k p = gg_pat k q) ↔ (p : ℕ) % 2 ^ k = q % 2 ^ k := by
    rw [Fin.ext_iff, gg_pat_val, gg_pat_val]
  have hpq : (p = q) ↔ (p : ℕ) = q := Fin.ext_iff
  simp only [cd_Cz, gg_C, gg_c0, gg_c1, gg_c2, hp, hpq]
  have h2 : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  split_ifs <;> push_cast <;> field_simp <;> ring

/-- The quadratic form of `C_k` through its structure:
`vᵀ C_k v = c₀ (∑ v)² + c₁ ∑_t (∑_i v_i(t))² + c₂ ∑ v²`. -/
theorem cd_quad_C (v : Fin (k * 2 ^ k) → ℝ) :
    gg_quad (gg_C k) v = gg_c0 k * (∑ p, v p) ^ 2
      + gg_c1 k * ∑ t : Fin (2 ^ k), (∑ i : Fin k, v (cd_idx k i t)) ^ 2
      + gg_c2 k * ∑ p, v p ^ 2 := by
  have hsplit : ∀ p q : Fin (k * 2 ^ k), v p * v q * gg_C k p q
      = gg_c0 k * (v p * v q) + gg_c1 k * (v p * v q * (if gg_pat k p = gg_pat k q then 1 else 0))
        + gg_c2 k * (v p * v q * (if p = q then 1 else 0)) := by
    intro p q; unfold gg_C; ring
  have h1 : ∑ p, ∑ q, v p * v q = (∑ p, v p) ^ 2 := by
    rw [sq, sum_mul_sum]
  have h3 : ∑ p, ∑ q, v p * v q * (if p = q then (1 : ℝ) else 0) = ∑ p, v p ^ 2 := by
    refine sum_congr rfl fun p _ => ?_
    rw [Finset.sum_eq_single p (fun q _ hq => by simp [Ne.symm hq]) (by simp)]
    simp [sq]
  have h2 : ∑ p, ∑ q, v p * v q * (if gg_pat k p = gg_pat k q then (1 : ℝ) else 0)
      = ∑ t : Fin (2 ^ k), (∑ i : Fin k, v (cd_idx k i t)) ^ 2 := by
    let e : Fin k × Fin (2 ^ k) ≃ Fin (k * 2 ^ k) := finProdFinEquiv
    have hx : ∀ x : Fin k × Fin (2 ^ k), e x = cd_idx k x.1 x.2 := fun _ => rfl
    rw [← e.sum_comp]
    simp_rw [← e.sum_comp (fun q => v (e _) * v q * _)]
    simp only [hx, gg_pat_idx, Fintype.sum_prod_type]
    have : ∀ (i : Fin k) (t : Fin (2 ^ k)), ∑ j : Fin k, ∑ u : Fin (2 ^ k),
        v (cd_idx k i t) * v (cd_idx k j u) * (if t = u then (1 : ℝ) else 0)
        = ∑ j : Fin k, v (cd_idx k i t) * v (cd_idx k j t) := by
      intro i t
      refine sum_congr rfl fun j _ => ?_
      rw [Finset.sum_eq_single t (fun u _ hu => by simp [Ne.symm hu]) (by simp)]
      simp
    simp only [this]
    rw [sum_comm]
    refine sum_congr rfl fun t _ => ?_
    rw [sq, sum_mul_sum]
  have h1' : ∑ p, v p * ∑ q, v q = (∑ p, v p) ^ 2 := by rw [← sum_mul, sq]
  unfold gg_quad
  simp only [hsplit, sum_add_distrib, ← mul_sum, h1, h1', h2, h3]

/-- The field vector with coordinates read from an integer list. -/
noncomputable def cd_vec (d : ℕ) (l : List ℤ) : Fin d → ℝ := fun p => (l.getD p 0 : ℝ)

/-- `240 · 2^k · vᵀ C_k v` for `v` read from a list, computed in `O(k 2^k)` list reads. -/
def cd_Qz (l : List ℤ) : ℤ :=
  60 * ((2 ^ k : ℕ) + 1) * (cd_nsum (k * 2 ^ k) fun p => l.getD p 0) ^ 2
    + 15 * cd_nsum (2 ^ k) (fun t => (cd_nsum k fun i => l.getD (t + 2 ^ k * i) 0) ^ 2)
    + (20 * ((2 ^ k : ℕ) : ℤ) - 11) * cd_nsum (k * 2 ^ k) (fun p => (l.getD p 0) ^ 2)

lemma cd_Qz_cast (l : List ℤ) :
    (cd_Qz k l : ℝ) = 240 * 2 ^ k * gg_quad (gg_C k) (cd_vec (k * 2 ^ k) l) := by
  rw [cd_quad_C]
  simp only [cd_Qz, cd_nsum_eq, cd_vec]
  push_cast
  simp only [cd_idx_val]
  have hi : ∀ t : Fin (2 ^ k), (∑ i : Fin k, ((l.getD (t + 2 ^ k * i) 0 : ℤ) : ℝ))
      = ∑ i ∈ range k, ((l.getD (t + 2 ^ k * i) 0 : ℤ) : ℝ) :=
    fun t => Fin.sum_univ_eq_sum_range (fun i => ((l.getD (t + 2 ^ k * i) 0 : ℤ) : ℝ)) k
  simp only [hi]
  rw [Fin.sum_univ_eq_sum_range (fun t => (∑ i ∈ range k, ((l.getD (t + 2 ^ k * i) 0 : ℤ) : ℝ)) ^ 2)]
  have hA : ∑ x : Fin (k * 2 ^ k), ((l.getD x 0 : ℤ) : ℝ) = ∑ x ∈ range (k * 2 ^ k), ((l.getD x 0 : ℤ) : ℝ) :=
    Fin.sum_univ_eq_sum_range (fun x => ((l.getD x 0 : ℤ) : ℝ)) _
  have hB : ∑ x : Fin (k * 2 ^ k), ((l.getD x 0 : ℤ) : ℝ) ^ 2
      = ∑ x ∈ range (k * 2 ^ k), ((l.getD x 0 : ℤ) : ℝ) ^ 2 :=
    Fin.sum_univ_eq_sum_range (fun x => ((l.getD x 0 : ℤ) : ℝ) ^ 2) _
  simp only [hA, hB, gg_c0, gg_c1, gg_c2]
  have h2 : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  field_simp
  ring

end Cov

/-! ### The joint covariance -/

section Joint

variable (k m : ℕ)

/-- Shared bits of the pattern `t` of the set `w` (`w = 0`: high bits; `w = 1`: low bits). -/
def cd_shb (w t : ℕ) : ℕ := if w = 0 then t / 2 ^ (k - m) else t % 2 ^ m

/-- The label in the union of the unit of coordinate `p` of the set `w`. -/
def cd_glob (w p : ℕ) : ℕ := (if w = 0 then 0 else k - m) + p / 2 ^ k

/-- `240 · 2^{2k-m} · C_J[P, Q]` for joint coordinates `P = p + (k 2^k) w`. -/
def cd_CJz (P Q : ℕ) : ℤ :=
  let d := k * 2 ^ k
  let K : ℤ := ((2 ^ (k - m) : ℕ) : ℤ)
  60 * ((2 ^ k : ℕ) + 1) * K +
    if P / d = Q / d then
      (if P % d % 2 ^ k = Q % d % 2 ^ k then 15 * K else 0)
        + (if P = Q then (20 * ((2 ^ k : ℕ) : ℤ) - 11) * K else 0)
    else if cd_shb k m (P / d) (P % d % 2 ^ k) = cd_shb k m (Q / d) (Q % d % 2 ^ k) then
      15 + (if cd_glob k m (P / d) (P % d) = cd_glob k m (Q / d) (Q % d)
        then 20 * ((2 ^ m : ℕ) : ℤ) - 11 else 0)
    else 0

lemma cd_jw_val (P : Fin (2 * (k * 2 ^ k))) : (gg_jw k P : ℕ) = P / (k * 2 ^ k) := by
  simp [gg_jw, finProdFinEquiv_symm_apply, Fin.divNat]

lemma cd_jp_val (P : Fin (2 * (k * 2 ^ k))) : (gg_jp k P : ℕ) = P % (k * 2 ^ k) := by
  simp [gg_jp, finProdFinEquiv_symm_apply, Fin.modNat]

lemma cd_shb_val (P : Fin (2 * (k * 2 ^ k))) :
    (gg_shb k m (gg_jw k P) (gg_pat k (gg_jp k P)) : ℕ)
      = cd_shb k m (P / (k * 2 ^ k)) (P % (k * 2 ^ k) % 2 ^ k) := by
  unfold gg_shb cd_shb
  have hw : (gg_jw k P = 0) ↔ P / (k * 2 ^ k) = 0 := by
    rw [Fin.ext_iff, cd_jw_val]; rfl
  by_cases h : gg_jw k P = 0
  · rw [ite_eq_left h, ite_eq_left (hw.1 h)]
    simp [gg_hi0, gg_pat_val, cd_jp_val]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hw.2 h'))]
    simp [gg_lo1, gg_pat_val, cd_jp_val]

lemma cd_glob_val (P : Fin (2 * (k * 2 ^ k))) :
    gg_glob k m P = cd_glob k m (P / (k * 2 ^ k)) (P % (k * 2 ^ k)) := by
  unfold gg_glob cd_glob
  have hw : (gg_jw k P = 0) ↔ P / (k * 2 ^ k) = 0 := by
    rw [Fin.ext_iff, cd_jw_val]; rfl
  rw [gg_unit_val, cd_jp_val]
  by_cases h : gg_jw k P = 0
  · rw [ite_eq_left h, ite_eq_left (hw.1 h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hw.2 h'))]

lemma cd_CJz_cast (hm : m ≤ k) (P Q : Fin (2 * (k * 2 ^ k))) :
    (cd_CJz k m P Q : ℝ) = 240 * 2 ^ (2 * k - m) * gg_CJ k m P Q := by
  have hw : (gg_jw k P = gg_jw k Q) ↔ (P : ℕ) / (k * 2 ^ k) = Q / (k * 2 ^ k) := by
    rw [Fin.ext_iff, cd_jw_val, cd_jw_val]
  have hp : (gg_pat k (gg_jp k P) = gg_pat k (gg_jp k Q))
      ↔ (P : ℕ) % (k * 2 ^ k) % 2 ^ k = Q % (k * 2 ^ k) % 2 ^ k := by
    rw [Fin.ext_iff, gg_pat_val, gg_pat_val, cd_jp_val, cd_jp_val]
  have hs : (gg_shb k m (gg_jw k P) (gg_pat k (gg_jp k P)) = gg_shb k m (gg_jw k Q) (gg_pat k (gg_jp k Q)))
      ↔ cd_shb k m (P / (k * 2 ^ k)) (P % (k * 2 ^ k) % 2 ^ k)
        = cd_shb k m (Q / (k * 2 ^ k)) (Q % (k * 2 ^ k) % 2 ^ k) := by
    rw [Fin.ext_iff, cd_shb_val, cd_shb_val]
  have hPQ : (P = Q) ↔ (P : ℕ) = Q := Fin.ext_iff
  have hsplit := gg_pow_split k m hm
  simp only [cd_CJz, gg_CJ, hw, hp, hs, hPQ, cd_glob_val, gg_c0, gg_c1, gg_c2, gg_beta, gg_alpha]
  rw [hsplit]
  have h2 : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  have h3 : ((2 : ℝ) ^ (k - m)) ≠ 0 := by positivity
  have h4 : ((2 : ℝ) ^ m) ≠ 0 := by positivity
  split_ifs <;> push_cast <;> field_simp <;> ring

/-- `240 · 2^{2k-m} · vᵀ C_J v` for `v` read from a list (a double sum). -/
def cd_QJz (l : List ℤ) : ℤ :=
  cd_nsum (2 * (k * 2 ^ k)) fun P => l.getD P 0 * cd_nsum (2 * (k * 2 ^ k)) fun Q => l.getD Q 0 * cd_CJz k m P Q

lemma cd_QJz_cast (hm : m ≤ k) (l : List ℤ) :
    (cd_QJz k m l : ℝ) = 240 * 2 ^ (2 * k - m) * gg_quad (gg_CJ k m) (cd_vec (2 * (k * 2 ^ k)) l) := by
  unfold cd_QJz gg_quad cd_vec
  simp only [cd_nsum_eq]
  push_cast
  rw [mul_sum, ← Fin.sum_univ_eq_sum_range (fun P => ((l.getD P 0 : ℤ) : ℝ)
    * ∑ Q ∈ range (2 * (k * 2 ^ k)), ((l.getD Q 0 : ℤ) : ℝ) * (cd_CJz k m P Q : ℝ))]
  refine sum_congr rfl fun P _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun Q => ((l.getD Q 0 : ℤ) : ℝ) * (cd_CJz k m P Q : ℝ)), mul_sum,
    mul_sum]
  refine sum_congr rfl fun Q _ => ?_
  rw [cd_CJz_cast k m hm]
  ring

end Joint

/-! ### Profiles of directional set partitions -/

/-- The profile of the partition with minimal-representative map `g` (unit `i` lies in the block
of `g i`) and block directions `δ` (code `0` inputs, `1` outputs, `2` both, read at the
representative): unit `i` loses unit `j` iff `j` lies in another block and either the block of `i`
does not have direction outputs, or the block of `j` does not have direction inputs. -/
def cd_profOf (k : ℕ) (g δ : List ℕ) : List (List Bool) :=
  (List.range k).map fun i => (List.range k).map fun j =>
    (g.getD j 0 != g.getD i 0) && (δ.getD (g.getD i 0) 0 != 1 || δ.getD (g.getD j 0) 0 != 0)

/-- Admissible pairs: `g i ≤ i`, `g (g i) = g i`, directions `≤ 2` at representatives and `0`
elsewhere, at least two blocks. -/
def cd_valid (k : ℕ) (g δ : List ℕ) : Bool :=
  (g.length == k) && (δ.length == k) &&
  (List.range k).all (fun i => decide (g.getD i 0 ≤ i) && (g.getD (g.getD i 0) 0 == g.getD i 0) &&
      (if g.getD i 0 == i then decide (δ.getD i 0 ≤ 2) else δ.getD i 0 == 0)) &&
  (List.range k).any (fun i => g.getD i 0 != 0)

lemma cd_at_profOf (k : ℕ) (g δ : List ℕ) {i j : ℕ} (hi : i < k) (hj : j < k) :
    cd_at (cd_profOf k g δ) i j
      = ((g.getD j 0 != g.getD i 0) && (δ.getD (g.getD i 0) 0 != 1 || δ.getD (g.getD j 0) 0 != 0)) := by
  simp [cd_at, cd_profOf, List.getD_eq_getElem?_getD, hi, hj]

/-! ### Regions and rows -/

section Region

variable (k : ℕ)

/-- The region `P_{0, C0}` with slack `ε` at level `y`: argmax rows, minimiser rows against every
admissible profile, and `F_{C0}(0) ≥ y`. -/
def cd_region (C0 : List (List Bool)) (ε y : ℝ) (ξ : Fin (k * 2 ^ k) → ℝ) : Prop :=
  (∀ t : ℕ, 0 < t → t < 2 ^ k → -ε ≤ cd_lin k (cd_argc k t) ξ) ∧
  (∀ g δ : List ℕ, cd_valid k g δ = true →
    -ε ≤ cd_F k (cd_profOf k g δ) 0 ξ / (cd_cc k (cd_profOf k g δ) : ℝ)
      - cd_F k C0 0 ξ / (cd_cc k C0 : ℝ)) ∧
  y ≤ cd_F k C0 0 ξ

/-- A row of a certificate: an argmax row or a minimiser row (given by an admissible pair). -/
inductive cd_Row
  | arg (t : ℕ)
  | min (g δ : List ℕ)

/-- Integer coefficients of a row (the minimiser row is scaled by `2^k cc(C0) cc(C)`). -/
def cd_rowc (C0 : List (List Bool)) : cd_Row → ℕ → ℤ
  | .arg t, p => cd_argc k t p
  | .min g δ, p => (cd_cc k C0 : ℤ) * cd_fz k (cd_profOf k g δ) 0 p
      - (cd_cc k (cd_profOf k g δ) : ℤ) * cd_fz k C0 0 p

/-- The slack scale of a row. -/
def cd_rowS (C0 : List (List Bool)) : cd_Row → ℕ
  | .arg _ => 1
  | .min g δ => 2 ^ k * cd_cc k C0 * cd_cc k (cd_profOf k g δ)

/-- Admissibility of a row. -/
def cd_rowOK : cd_Row → Bool
  | .arg t => decide (0 < t) && decide (t < 2 ^ k)
  | .min g δ => cd_valid k g δ && decide (0 < cd_cc k (cd_profOf k g δ))

lemma cd_row_lower {C0 : List (List Bool)} {ε y : ℝ} {ξ : Fin (k * 2 ^ k) → ℝ}
    (hR : cd_region k C0 ε y ξ) (h0 : 0 < cd_cc k C0) (r : cd_Row) (hr : cd_rowOK k r = true) :
    -(cd_rowS k C0 r : ℝ) * ε ≤ cd_lin k (cd_rowc k C0 r) ξ := by
  cases r with
  | arg t =>
    simp only [cd_rowOK, Bool.and_eq_true, decide_eq_true_eq] at hr
    simp only [cd_rowS, cd_rowc, Nat.cast_one, neg_mul, one_mul]
    exact hR.1 t hr.1 hr.2
  | min g δ =>
    simp only [cd_rowOK, Bool.and_eq_true, decide_eq_true_eq] at hr
    have h := hR.2.1 g δ hr.1
    have hc0 : (0 : ℝ) < cd_cc k C0 := by exact_mod_cast h0
    have hc : (0 : ℝ) < cd_cc k (cd_profOf k g δ) := by exact_mod_cast hr.2
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    have hrc : cd_rowc k C0 (cd_Row.min g δ) = fun p => (cd_cc k C0 : ℤ) * cd_fz k (cd_profOf k g δ) 0 p
        - (cd_cc k (cd_profOf k g δ) : ℤ) * cd_fz k C0 0 p := rfl
    simp only [cd_rowS]
    rw [hrc, cd_lin_sub, cd_lin_smul, cd_lin_smul]
    simp only [cd_F] at h
    have e : (cd_cc k C0 : ℝ) * cd_lin k (cd_fz k (cd_profOf k g δ) 0) ξ
        - (cd_cc k (cd_profOf k g δ) : ℝ) * cd_lin k (cd_fz k C0 0) ξ
        = (2 ^ k * cd_cc k C0 * cd_cc k (cd_profOf k g δ) : ℝ)
          * (cd_lin k (cd_fz k (cd_profOf k g δ) 0) ξ / 2 ^ k / (cd_cc k (cd_profOf k g δ) : ℝ)
            - cd_lin k (cd_fz k C0 0) ξ / 2 ^ k / (cd_cc k C0 : ℝ)) := by
      field_simp
    push_cast
    rw [e]
    have hpos : (0 : ℝ) < 2 ^ k * cd_cc k C0 * cd_cc k (cd_profOf k g δ) := by positivity
    nlinarith

/-- A nonnegative combination of rows. -/
def cd_comb (C0 : List (List Bool)) (rows : List (cd_Row × ℕ)) (p : ℕ) : ℤ :=
  (rows.map fun r => (r.2 : ℤ) * cd_rowc k C0 r.1 p).sum

/-- The total slack of a combination. -/
def cd_Lam (C0 : List (List Bool)) (rows : List (cd_Row × ℕ)) : ℕ :=
  (rows.map fun r => r.2 * cd_rowS k C0 r.1).sum

lemma cd_lin_comb (C0 : List (List Bool)) (rows : List (cd_Row × ℕ)) (ξ : Fin (k * 2 ^ k) → ℝ) :
    cd_lin k (cd_comb k C0 rows) ξ = (rows.map fun r => (r.2 : ℝ) * cd_lin k (cd_rowc k C0 r.1) ξ).sum := by
  induction rows with
  | nil => simp [cd_comb, cd_lin]
  | cons a l ih =>
    have e : cd_comb k C0 (a :: l) = fun p => (a.2 : ℤ) * cd_rowc k C0 a.1 p + cd_comb k C0 l p := by
      funext p; simp [cd_comb]
    rw [e, cd_lin_add, cd_lin_smul, ih]
    simp

lemma cd_comb_lower {C0 : List (List Bool)} {ε y : ℝ} {ξ : Fin (k * 2 ^ k) → ℝ}
    (hR : cd_region k C0 ε y ξ) (h0 : 0 < cd_cc k C0) (rows : List (cd_Row × ℕ))
    (hr : ∀ r ∈ rows, cd_rowOK k r.1 = true) :
    -(cd_Lam k C0 rows : ℝ) * ε ≤ cd_lin k (cd_comb k C0 rows) ξ := by
  rw [cd_lin_comb]
  induction rows with
  | nil => simp [cd_Lam]
  | cons a l ih =>
    have ha := cd_row_lower k hR h0 a.1 (hr a List.mem_cons_self)
    have hl := ih fun r hr' => hr r (List.mem_cons_of_mem _ hr')
    simp only [cd_Lam, List.map_cons, List.sum_cons] at hl ⊢
    rw [Nat.cast_add, Nat.cast_mul]
    have hw : (0 : ℝ) ≤ a.2 := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left ha hw]

end Region

/-! ### Certificates -/

section Cert

variable (k : ℕ)

/-- A half-space certificate for the region of `C0`: weighted rows, the weight of the row
`F_{C0}(0) ≥ y`, and the claimed vector `v = ∑ w_r row_r + w_F 2^k F_{C0}(0)`. -/
structure cd_Cert where
  C0 : List (List Bool)
  rows : List (cd_Row × ℕ)
  wF : ℕ
  v : List ℤ

/-- The combination a certificate claims. -/
def cd_vc (c : cd_Cert) (p : ℕ) : ℤ := cd_comb k c.C0 c.rows p + (c.wF : ℤ) * cd_fz k c.C0 0 p

/-- The threshold `h = w_F 2^k`. -/
def cd_h (c : cd_Cert) : ℕ := c.wF * 2 ^ k

/-- The kernel check of a certificate against the rate `Ln / Ld`. -/
def cd_check (c : cd_Cert) (Ln Ld : ℕ) : Bool :=
  decide (0 < c.wF) && decide (0 < cd_cc k c.C0) && c.rows.all (fun r => cd_rowOK k r.1) &&
  (List.range (k * 2 ^ k)).all (fun p => c.v.getD p 0 == cd_vc k c p) &&
  decide ((Ln : ℤ) * cd_Qz k c.v ≤ (Ld : ℤ) * (240 * ((2 ^ k : ℕ) : ℤ)) * ((cd_h k c : ℕ) : ℤ) ^ 2)

lemma cd_sum_vec_eq (c : cd_Cert) (hv : ∀ p < k * 2 ^ k, c.v.getD p 0 = cd_vc k c p)
    (ξ : Fin (k * 2 ^ k) → ℝ) :
    ∑ p, cd_vec (k * 2 ^ k) c.v p * ξ p = cd_lin k (cd_vc k c) ξ := by
  unfold cd_lin cd_vec
  exact sum_congr rfl fun p _ => by rw [hv p p.2]

/-- **Soundness of a half-space certificate.** Every point of the region with slack `ε` at level
`y` satisfies `⟨v, ξ⟩ ≥ h y - Λ ε`, and `(Ln/Ld) vᵀ C_k v ≤ h²`. -/
theorem cd_check_sound (c : cd_Cert) (Ln Ld : ℕ) (hc : cd_check k c Ln Ld = true) (hLd : 0 < Ld) :
    (∀ (ξ : Fin (k * 2 ^ k) → ℝ) (ε y : ℝ), 0 ≤ ε → cd_region k c.C0 ε y ξ →
      (cd_h k c : ℝ) * y - (cd_Lam k c.C0 c.rows : ℝ) * ε
        ≤ ∑ p, cd_vec (k * 2 ^ k) c.v p * ξ p) ∧
    (Ln : ℝ) / Ld * gg_quad (gg_C k) (cd_vec (k * 2 ^ k) c.v) ≤ (cd_h k c : ℝ) ^ 2 := by
  simp only [cd_check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨_, h0⟩, hrows⟩, hv⟩, hrate⟩ := hc
  refine ⟨fun ξ ε y _ hR => ?_, ?_⟩
  · rw [cd_sum_vec_eq k c hv]
    have e : cd_vc k c = fun p => cd_comb k c.C0 c.rows p + (c.wF : ℤ) * cd_fz k c.C0 0 p := rfl
    rw [e, cd_lin_add, cd_lin_smul]
    have h1 := cd_comb_lower k hR h0 c.rows hrows
    have h2 := hR.2.2
    simp only [cd_F] at h2
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    have h3 : (2 : ℝ) ^ k * y ≤ cd_lin k (cd_fz k c.C0 0) ξ := by
      rw [le_div_iff₀ hp] at h2; linarith
    have hw : (0 : ℝ) ≤ c.wF := Nat.cast_nonneg _
    simp only [cd_h]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left h3 hw]
  · have hq := cd_Qz_cast k c.v
    have hr : ((Ln : ℤ) : ℝ) * (cd_Qz k c.v : ℝ)
        ≤ ((Ld : ℤ) : ℝ) * (240 * ((2 ^ k : ℕ) : ℝ)) * ((cd_h k c : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hrate
    rw [hq] at hr
    push_cast at hr
    have hLd' : (0 : ℝ) < Ld := by exact_mod_cast hLd
    have hp : (0 : ℝ) < 240 * 2 ^ k := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hLd']
    nlinarith

/-- A Gordan certificate for a degenerate region: `w₀ row₀ + ∑ w_r row_r = 0` with `row₀ ≠ 0`. -/
structure cd_GCert where
  C0 : List (List Bool)
  r0 : cd_Row
  w0 : ℕ
  rows : List (cd_Row × ℕ)

/-- The kernel check of a Gordan certificate. -/
def cd_checkG (c : cd_GCert) : Bool :=
  decide (0 < cd_cc k c.C0) && cd_rowOK k c.r0 && decide (0 < c.w0) &&
  c.rows.all (fun r => cd_rowOK k r.1) &&
  (List.range (k * 2 ^ k)).all (fun p => (c.w0 : ℤ) * cd_rowc k c.C0 c.r0 p + cd_comb k c.C0 c.rows p == 0) &&
  (List.range (k * 2 ^ k)).any (fun p => cd_rowc k c.C0 c.r0 p != 0)

/-- **Soundness of a Gordan certificate.** On the region with slack `ε`, the nonzero row `row₀`
is within `(S₀ + Λ) ε` of `0`. -/
theorem cd_checkG_sound (c : cd_GCert) (hc : cd_checkG k c = true) :
    (∃ p : Fin (k * 2 ^ k), cd_rowc k c.C0 c.r0 p ≠ 0) ∧
    ∀ (ξ : Fin (k * 2 ^ k) → ℝ) (ε y : ℝ), 0 ≤ ε → cd_region k c.C0 ε y ξ →
      |cd_lin k (cd_rowc k c.C0 c.r0) ξ| ≤ ((cd_rowS k c.C0 c.r0 : ℝ) + cd_Lam k c.C0 c.rows) * ε := by
  simp only [cd_checkG, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    List.mem_range, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨⟨⟨⟨h0, hr0⟩, hw0⟩, hrows⟩, hzero⟩, ⟨p, hp, hne⟩⟩ := hc
  refine ⟨⟨⟨p, hp⟩, hne⟩, fun ξ ε y hε hR => ?_⟩
  have hsum : cd_lin k (fun p => (c.w0 : ℤ) * cd_rowc k c.C0 c.r0 p + cd_comb k c.C0 c.rows p) ξ = 0 := by
    unfold cd_lin
    exact sum_eq_zero fun q _ => by simp only [hzero q q.2]; simp
  rw [cd_lin_add, cd_lin_smul] at hsum
  have h1 := cd_comb_lower k hR h0 c.rows hrows
  have h2 := cd_row_lower k hR h0 c.r0 hr0
  have hw : (1 : ℝ) ≤ c.w0 := by exact_mod_cast hw0
  have hL : (0 : ℝ) ≤ (cd_Lam k c.C0 c.rows : ℝ) * ε := mul_nonneg (Nat.cast_nonneg _) hε
  have hS : (0 : ℝ) ≤ (cd_rowS k c.C0 c.r0 : ℝ) * ε := mul_nonneg (Nat.cast_nonneg _) hε
  push_cast at hsum
  rw [abs_le]
  constructor
  · nlinarith
  · by_contra hcon
    push Not at hcon
    have : (cd_Lam k c.C0 c.rows : ℝ) * ε < (c.w0 : ℝ) * cd_lin k (cd_rowc k c.C0 c.r0) ξ := by
      nlinarith
    linarith

end Cert

/-! ### Joint certificates -/

section JointCert

variable (k m : ℕ)

/-- A half-space certificate for the product of the regions of `C0` (first set) and `C1` (second
set) in the joint coordinates `P = p + (k 2^k) w`. -/
structure cd_JCert where
  C0 : List (List Bool)
  C1 : List (List Bool)
  rows0 : List (cd_Row × ℕ)
  rows1 : List (cd_Row × ℕ)
  wF0 : ℕ
  wF1 : ℕ
  v : List ℤ

/-- The combination a joint certificate claims. -/
def cd_vcJ (c : cd_JCert) (P : ℕ) : ℤ :=
  if P < k * 2 ^ k then cd_comb k c.C0 c.rows0 P + (c.wF0 : ℤ) * cd_fz k c.C0 0 P
  else cd_comb k c.C1 c.rows1 (P - k * 2 ^ k) + (c.wF1 : ℤ) * cd_fz k c.C1 0 (P - k * 2 ^ k)

/-- The threshold `h = (w_{F,0} + w_{F,1}) 2^k`. -/
def cd_hJ (c : cd_JCert) : ℕ := (c.wF0 + c.wF1) * 2 ^ k

/-- The total slack of a joint certificate. -/
def cd_LamJ (c : cd_JCert) : ℕ := cd_Lam k c.C0 c.rows0 + cd_Lam k c.C1 c.rows1

/-- The kernel check of a joint certificate against the rate `Ln / Ld`. -/
def cd_checkJ (c : cd_JCert) (Ln Ld : ℕ) : Bool :=
  decide (0 < cd_cc k c.C0) && decide (0 < cd_cc k c.C1) &&
  c.rows0.all (fun r => cd_rowOK k r.1) && c.rows1.all (fun r => cd_rowOK k r.1) &&
  (List.range (2 * (k * 2 ^ k))).all (fun P => c.v.getD P 0 == cd_vcJ k c P) &&
  decide ((Ln : ℤ) * cd_QJz k m c.v
    ≤ (Ld : ℤ) * (240 * ((2 ^ (2 * k - m) : ℕ) : ℤ)) * ((cd_hJ k c : ℕ) : ℤ) ^ 2)

lemma cd_sum_joint (f : ℕ → ℤ) (ξ : Fin (2 * (k * 2 ^ k)) → ℝ) :
    ∑ P : Fin (2 * (k * 2 ^ k)), (f P : ℝ) * ξ P
      = cd_lin k f (fun p => ξ (gg_jidx k 0 p))
        + cd_lin k (fun p => f (p + k * 2 ^ k)) (fun p => ξ (gg_jidx k 1 p)) := by
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin 2 × Fin (k * 2 ^ k) ≃ _), Fintype.sum_prod_type,
    Fin.sum_univ_two]
  unfold cd_lin gg_jidx
  congr 1
  all_goals
    refine sum_congr rfl fun p _ => ?_
    simp [finProdFinEquiv_apply_val, add_comm]

/-- **Soundness of a joint certificate.** If the first set's field lies in the region of `C0` and
the second set's in that of `C1` (slack `ε`, level `y`), then `⟨v, ξ⟩ ≥ h y - Λ ε`; and
`(Ln/Ld) vᵀ C_J v ≤ h²`. -/
theorem cd_checkJ_sound (hm : m ≤ k) (c : cd_JCert) (Ln Ld : ℕ) (hc : cd_checkJ k m c Ln Ld = true)
    (hLd : 0 < Ld) :
    (∀ (ξ : Fin (2 * (k * 2 ^ k)) → ℝ) (ε y : ℝ), 0 ≤ ε →
      cd_region k c.C0 ε y (fun p => ξ (gg_jidx k 0 p)) →
      cd_region k c.C1 ε y (fun p => ξ (gg_jidx k 1 p)) →
      (cd_hJ k c : ℝ) * y - (cd_LamJ k c : ℝ) * ε ≤ ∑ P, cd_vec (2 * (k * 2 ^ k)) c.v P * ξ P) ∧
    (Ln : ℝ) / Ld * gg_quad (gg_CJ k m) (cd_vec (2 * (k * 2 ^ k)) c.v) ≤ (cd_hJ k c : ℝ) ^ 2 := by
  simp only [cd_checkJ, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, hr0⟩, hr1⟩, hv⟩, hrate⟩ := hc
  refine ⟨fun ξ ε y _ hR0 hR1 => ?_, ?_⟩
  · have e1 : ∑ P, cd_vec (2 * (k * 2 ^ k)) c.v P * ξ P
        = ∑ P : Fin (2 * (k * 2 ^ k)), (cd_vcJ k c P : ℝ) * ξ P :=
      sum_congr rfl fun P _ => by rw [cd_vec, hv P P.2]
    rw [e1, cd_sum_joint]
    have eb : (fun p : ℕ => cd_vcJ k c (p + k * 2 ^ k)) = fun p =>
        cd_comb k c.C1 c.rows1 p + (c.wF1 : ℤ) * cd_fz k c.C1 0 p := by
      funext p; simp [cd_vcJ]
    have la : cd_lin k (fun p => cd_vcJ k c p) (fun p => ξ (gg_jidx k 0 p))
        = cd_lin k (fun p => cd_comb k c.C0 c.rows0 p + (c.wF0 : ℤ) * cd_fz k c.C0 0 p)
            (fun p => ξ (gg_jidx k 0 p)) := by
      unfold cd_lin
      exact sum_congr rfl fun p _ => by simp [cd_vcJ, p.2]
    rw [la, eb, cd_lin_add, cd_lin_smul, cd_lin_add, cd_lin_smul]
    have a1 := cd_comb_lower k hR0 h0 c.rows0 hr0
    have a2 := cd_comb_lower k hR1 h1 c.rows1 hr1
    have b1 := hR0.2.2
    have b2 := hR1.2.2
    simp only [cd_F] at b1 b2
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    rw [le_div_iff₀ hp] at b1 b2
    have hw0 : (0 : ℝ) ≤ c.wF0 := Nat.cast_nonneg _
    have hw1 : (0 : ℝ) ≤ c.wF1 := Nat.cast_nonneg _
    simp only [cd_hJ, cd_LamJ]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left b1 hw0, mul_le_mul_of_nonneg_left b2 hw1]
  · have hq := cd_QJz_cast k m hm c.v
    have hr : ((Ln : ℤ) : ℝ) * (cd_QJz k m c.v : ℝ)
        ≤ ((Ld : ℤ) : ℝ) * (240 * ((2 ^ (2 * k - m) : ℕ) : ℝ)) * ((cd_hJ k c : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hrate
    rw [hq] at hr
    push_cast at hr
    have hLd' : (0 : ℝ) < Ld := by exact_mod_cast hLd
    have hp : (0 : ℝ) < 240 * 2 ^ (2 * k - m) := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hLd']
    nlinarith

end JointCert

/-! ### Covered regions -/

/-- The region of `C0` is covered at rate `Ln / Ld`: by a half-space certificate, or it is
degenerate with a Gordan certificate. -/
def cd_Covered (k Ln Ld : ℕ) (C0 : List (List Bool)) : Prop :=
  (∃ c : cd_Cert, c.C0 = C0 ∧ cd_check k c Ln Ld = true) ∨
    (∃ c : cd_GCert, c.C0 = C0 ∧ cd_checkG k c = true)

/-- **What a covered region gives.** Either a half-space `⟨v, ξ⟩ ≥ h y - Λ ε` containing the region
with `(Ln/Ld) vᵀ C_k v ≤ h²`, or a nonzero functional `r` with `|⟨r, ξ⟩| ≤ Λ ε` on the region. -/
theorem cd_covered_sound {k Ln Ld : ℕ} {C0 : List (List Bool)} (hLd : 0 < Ld)
    (h : cd_Covered k Ln Ld C0) :
    (∃ (v : Fin (k * 2 ^ k) → ℝ) (hh Λ : ℝ), 0 < hh ∧ 0 ≤ Λ ∧
        (Ln : ℝ) / Ld * gg_quad (gg_C k) v ≤ hh ^ 2 ∧
        ∀ (ξ : Fin (k * 2 ^ k) → ℝ) (ε y : ℝ), 0 ≤ ε → cd_region k C0 ε y ξ →
          hh * y - Λ * ε ≤ ∑ p, v p * ξ p) ∨
    (∃ (r : Fin (k * 2 ^ k) → ℝ) (Λ : ℝ), r ≠ 0 ∧ 0 ≤ Λ ∧
        ∀ (ξ : Fin (k * 2 ^ k) → ℝ) (ε y : ℝ), 0 ≤ ε → cd_region k C0 ε y ξ →
          |∑ p, r p * ξ p| ≤ Λ * ε) := by
  rcases h with ⟨c, rfl, hc⟩ | ⟨c, rfl, hc⟩
  · left
    have hw : 0 < c.wF := by
      simp only [cd_check, Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.1.1.1.1
    obtain ⟨h1, h2⟩ := cd_check_sound k c Ln Ld hc hLd
    refine ⟨cd_vec (k * 2 ^ k) c.v, cd_h k c, cd_Lam k c.C0 c.rows, ?_, Nat.cast_nonneg _, h2, h1⟩
    unfold cd_h
    positivity
  · right
    obtain ⟨⟨p, hp⟩, h2⟩ := cd_checkG_sound k c hc
    refine ⟨fun q => (cd_rowc k c.C0 c.r0 q : ℝ), (cd_rowS k c.C0 c.r0 : ℝ) + cd_Lam k c.C0 c.rows,
      fun h0 => hp (by have := congrFun h0 p; simpa using this), by positivity, fun ξ ε y hε hR => ?_⟩
    exact h2 ξ ε y hε hR

end Census
end IIT
