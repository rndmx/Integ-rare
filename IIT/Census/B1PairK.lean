/-
Census of complexes, B1 development, module A8 (`B1-BLUEPRINT.md` module A8, as amended by
`B1-BLUEPRINT-AMEND.md`; `B1-W2-LT.md` Sections 7-8; `B1-W1-STAB.md` D1, D4): candidates with one
heavy block — pairs, triples and 4-sets at the tilt.

Notation (flipped coordinates, as in `BigPhiStats`): `w = flipP s z`, `y_{r,i} = clamp01 (w r i)`,
`r0` the heavy row (`tcRow w` at the tilt), `σ = Pw w r0`, `A = lvK k · Zs w` the level of a
`k`-set numerator, `η` the level band (`|Num - A| ≤ η`), `ρ^k = ur_rho k A η`,
`e = ur_err k A η σ = 4kη²/((A-η)σ)`.  For a `k`-set `S` ordered by `e : Fin k ↪ Fin N` and a
pattern `u : Fin (2^k)`, `pkFlip e t u` is `t` flipped on `{e q : bit q of u}`.

Contents.
1. Patterns (`pkEnc`, `pkFlip`, `pkSub`) and the identity `pk_sum_agree`: the sum over the
   patterns `u ⊆ C` of `G (t ⊕ u)` is the sum over `agree ((S \ C) ∪ Sᶜ) t`.
2. **Bridge** from the numerators to the LP models (`pk_bridge3`, `pk_bridge4`): if
   `|Num_i(S, t ⊕ u) - (σ ξ_{i,u} + B_i)| ≤ φ` for every unit and pattern, then
   `|Σ_{j∈S} D_j(θ, t) - σ · lpkV (lpTab e hS θ) ξ| ≤ 2kφ`.
3. **LP bounds at scale `y0`** (`lp3_bound_own(_sys)`, `lp4_bound_own(_sys)`): with `ξ ≥ 0` and the
   own entries `ξ_{i,0} ≤ y0` only (no upper box), a non-all-cut near-minimiser has
   `v ≤ (5/3) y0 + (40/3) e` (triples), `v ≤ (11/4) y0 + (165/4) e` (4-sets).  New kernel checks
   `lp3AllOwnOK_true`, `lp4AllOwnOK_true`: every positive coefficient of the 21 (149) certificates
   of `CertLP3Data` (`CertLP4Data`) sits on an own entry.
4. `ur_upper_reduce_mip`: `ur_upper_reduce` with the maximal states and `θ ∈ sysMipSetAt` exposed.
5. Single cuts `pkSingle`, the no-tie condition `NoSingleTie` (two single-cut values differ, or one
   is `0`), and `allCut_zero_of_noTie` (via `allCut_mip_tie'`): off the tie every all-cut MIP
   partition has value `0`.
6. **Pairs** (Fable's Lemma 11.2): `pair_phiOfState` —
   `min φ_a φ_b ≤ φ_s(tc, te) ≤ 2 min φ_a φ_b`, and `= min φ_a φ_b` under `NoSingleTie`, where
   `φ_a = pairCutVal … a tc te = min(back · (log₂ LR_a)⁺, e_S · (log₂ LR'_a)⁺)` (the minimum of the
   four single-cut sides); `pair_phi_eq` (system level, sup over the maximal pairs);
   `pair_sysPhiC_single'`, `pair_Num_single'` (`Num_a({a}, t) = (Num_a(t) + Num_a(t^b))/2`);
   the level form `pair_cause_le(_b)` / `pair_cause_ge(_b)`:
   `(1/4) D/(2(A+η) ln 2) ≤ φ_c(θ_a, tc) ≤ (ρ²/4) max(D,0)/(2(A-η) ln 2)`, `D = Num_a(tc) - Num_a(tc^b)`
   (level `1/(8 lvK 2 ln 2)` for `A = lvK 2 · Zs`); `pair_lower_core`, `pair_lower_tilt`.
7. Heavy row and bulk: `Num_eq_heavy_rest` (exact: `Num_i(S,t) = Pw(r0) y_{(t,r0),i} + pkRest`),
   `pk_hdec_of_rest` (the decomposition hypothesis from a bulk bound `|pkRest - B_i| ≤ φ`),
   `pk_hlev_of_full` (the band for every `Y ⊆ S` from the full numerators).
8. **Upper bounds** (deterministic cores and tilt forms, `c` = bound on the own entries
   `y_{(tc_S, r0|Sᶜ), i}` at the maximal cause states of `S`):
   * `pair_upper_core`: `φ_s({a,b}) ≤ (ρ²/4)(σc + 2φ)/(2(A-η) ln 2)`;
     `pair_upper_tilt(_abs)`: `≤ ρ² · A/(A-η) · β/(8 lvK 2 ln 2) · (c + 2φ/P(tc))`;
   * `triple_upper_core`: `φ_s(S) ≤ (ρ³/8) σ/(A ln 2) ((5/3)c + (43/3)e + 166 φ/σ)`;
     `triple_upper_tilt`: `≤ ρ³ · levTrip · β · (c + (43/5)e + (498/5)φ/P(tc))`,
     `triple_upper_tilt_abs` (`c = 1`), `triple_upper_tilt_ymax` (`c = y_max`);
   * `four_upper_core`: `φ_s(S) ≤ (ρ⁴/16) σ/(A ln 2) ((11/4)c + (169/4)e + 668 φ/σ)`;
     `four_upper_tilt(_abs)`: `≤ ρ⁴ · (165/196) levTrip · β · (c + (169/11)e + (2672/11)φ/P(tc))`.
   Hypotheses: level band `η`, heavy-row decomposition with bulk fluctuation `φ`, own-entry bound
   `c`, `NoSingleTie` at every maximal pair (all-cut profile), no effect window at the threshold of
   `ur_upper_reduce_mip` (`heff`: `φ_e = 0` or `φ_e ≥ ρ^k 2^{-k} 2kη/((A-η) ln 2)`).
9. `tl_tc_agree`, **`pk_tl_triple_lower_gen'`** (W2 7.5): general base pattern `t0` and separate
   pattern margin `m` (`24 A η² < (A-η)² m`).
10. **`triple_lower_tilt`** (deterministic core of W2's Lemma TC): heavy profile `ξ` at the eight
   patterns `t0 ⊕ u` with the shift-trick targets `ξ_{i,0} - ξ_{i,u} = c0 (1 - q(t)_{i,u})`,
   margin `m0`, fluctuation `φ` ⟹ `φ_s(S) ≥ σ((c0(5/3-t) - 6φ/σ) - 6η²/((A-η)σ))/(8A ln 2)`;
   `lp3Q_margin`: the W2 (7.1) pattern margins `c0 (8/3 - t) - 1`.
11. **Effect lemmas** (copies of `ThmP3Eff` with `x_i ≥ 1/2 + γ`): `pk_iiE_le`, `eff_te_agree`
   (the maximal effect state), `eff_phiE_ge` (`φ_e ≥ p_e · log₂(1/λ)` from cut factors `≤ λ x_j`;
   gives EF-tc with the caller's `λ`), `eff_EF` (Lemma EF: private entries `≤ ρ`,
   `3(2^k-1)2^k ρ < 4kγ` ⟹ unique maximal effect state on `S` and `φ_e ≥ (1/2+γ)^k (1 - 3ρ)`).

Deviations from the (amended) blueprint — every false or unprovable statement fixed minimally:
* **`triple_upper_tilt` at the level `levTrip · y_max · β` is false in general.**  The maximal cause
  state of a triple can be the fully flipped pattern `tc^S` (W1-STAB D1, D4), where the own entries
  of the LP are entries of the rows `tc^S`, not of `tc`, and are not bounded by `y_max`.  Fix: the
  level is `levTrip · c · β` with `c` a bound on the own entries at the maximal cause states
  (`hown`).  `c = 1` always works (`triple_upper_tilt_abs`: the absolute level that C1 and W1's
  (S2) need); `c = y_max` holds when every maximal cause state agrees with `tc` on `S`
  (`triple_upper_tilt_ymax`, extra hypothesis `hagree`).  The same parameter `c` is offered for
  pairs and 4-sets (the requested absolute forms are `c = 1`).
* **Pairs: the exact formula needs the no-tie hypothesis.**  At an exact tie `φ_a = φ_b > 0` the
  both-cut partitions (cut count 2, value `≥ φ_a + φ_b` by exact log-ratio additivity) join the MIP
  set and the IIT tie rule reports the larger value, up to `2 min`.  `pair_phiOfState` states the
  sandwich and the equality under `NoSingleTie`; the pair upper bounds assume `NoSingleTie` at every
  maximal state pair (its complement is a null set, B2).  The same hypothesis excludes the all-cut
  profile of triples and 4-sets (via `allCut_mip_tie'`).
* `k_upper_tilt` (`5 ≤ k`) is not provided: superseded by `B1NearUniv.propKT` (amendment).
* The fluctuation `η_fl` of the blueprint is made explicit as the bulk `pkRest` (all rows but
  `r0`): hypothesis `|Num_i(S,t) - (σ y_{(t,r0),i} + B_i)| ≤ φ`, equivalently `|pkRest - B_i| ≤ φ`
  (`pk_hdec_of_rest`).  `σ = Pw(r0)`; the light rows of the `tc`-block are part of the bulk.
* The effect alternative of the upper reduction is excluded by an explicit hypothesis `heff` (in
  `Forced` this is `noEffWin` together with `threshold ≤ β`), not by a probabilistic argument.
* `triple_lower_tilt` follows W2 (targets `y_i - c(1 - q(t))`, not `c · p*`): it is the
  deterministic core of Lemma TC; the random configuration enters only through `ξ`, `φ`, `m0`.
* `pk_tl_triple_lower_gen'`: the pattern margin quantifies over all states differing from `t0` on `S`.
* Effect lemmas: `ThmP3Eff`'s box (`99/100`, `1/100`) is replaced by `x_j ≥ 1/2 + γ` and private
  entries `≤ ρ`; EF-tc is `eff_te_agree` + `eff_phiE_ge` with the caller's `(U0, λ)`.
* No new axioms; the two new kernel checks use `decide +kernel` (no `native_decide`).
-/
import IIT.Census.B1Defs
import IIT.Census.B1Couple
import IIT.Census.CertLP4
import IIT.Census.UpperReduce
import IIT.Census.TripleLower
import IIT.Census.ThmP3Eff
import IIT.Census.BigPhiSys

namespace IIT
namespace Census

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-! ## 1. Patterns of a `k`-set -/

section Patterns

variable {k : ℕ}

/-- The pattern index (in `Fin (2^k)`) whose bit `q` is `b q`. -/
noncomputable def pkEnc (k : ℕ) (b : Fin k → Bool) : Fin (2 ^ k) :=
  finFunctionFinEquiv (fun q => if b q then (1 : Fin 2) else 0)

lemma pk_testBit_iff (u : Fin (2 ^ k)) (q : Fin k) :
    (u : ℕ).testBit q = true ↔ ((finFunctionFinEquiv.symm u q : Fin 2) : ℕ) = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, finFunctionFinEquiv_symm_apply_val, decide_eq_true_iff]

lemma pk_testBit_enc (b : Fin k → Bool) (q : Fin k) : ((pkEnc k b : ℕ)).testBit q = b q := by
  have h := pk_testBit_iff (pkEnc k b) q
  unfold pkEnc at h ⊢
  rw [Equiv.symm_apply_apply] at h
  cases hb : b q <;> simpa [hb] using h

lemma pk_enc_bits (u : Fin (2 ^ k)) : pkEnc k (fun q => (u : ℕ).testBit q) = u := by
  apply finFunctionFinEquiv.symm.injective
  unfold pkEnc
  rw [Equiv.symm_apply_apply]
  funext q
  apply Fin.ext
  have hlt := (finFunctionFinEquiv.symm u q).isLt
  have hiff := pk_testBit_iff u q
  by_cases h : (u : ℕ).testBit q = true
  · rw [ite_eq_left h, hiff.1 h]; rfl
  · rw [ite_eq_right h]
    have : ((finFunctionFinEquiv.symm u q : Fin 2) : ℕ) ≠ 1 := fun h' => h (hiff.2 h')
    have h0 : ((0 : Fin 2) : ℕ) = 0 := rfl
    rw [h0]
    omega

/-- `t` with the bits of the units `e q` (`q` a bit of `u`) flipped. -/
def pkFlip (e : Fin k ↪ Fin N) (t : State N) (u : Fin (2 ^ k)) : State N :=
  fun j => if ∃ q : Fin k, e q = j ∧ (u : ℕ).testBit q = true then !t j else t j

lemma pkFlip_e (e : Fin k ↪ Fin N) (t : State N) (u : Fin (2 ^ k)) (q : Fin k) :
    pkFlip e t u (e q) = if (u : ℕ).testBit q = true then !t (e q) else t (e q) := by
  unfold pkFlip
  by_cases h : (u : ℕ).testBit q = true
  · rw [ite_eq_left ⟨q, rfl, h⟩, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨q', hq', h'⟩
    rw [e.injective hq'] at h'
    exact h h'

lemma pkFlip_of_not (e : Fin k ↪ Fin N) (t : State N) (u : Fin (2 ^ k)) {j : Fin N}
    (hj : ∀ q, e q ≠ j) : pkFlip e t u j = t j := by
  unfold pkFlip
  rw [ite_eq_right]
  rintro ⟨q, hq, -⟩
  exact hj q hq

lemma pkFlip_zero (e : Fin k ↪ Fin N) (t : State N) (u : Fin (2 ^ k)) (hu : (u : ℕ) = 0) :
    pkFlip e t u = t := by
  funext j
  unfold pkFlip
  rw [ite_eq_right]
  rintro ⟨q, -, hq⟩
  rw [hu, Nat.zero_testBit] at hq
  exact Bool.false_ne_true hq

/-- The pattern `u` lies inside `C` (every flipped unit is in `C`). -/
def pkSub (e : Fin k ↪ Fin N) (C : Finset (Fin N)) (u : Fin (2 ^ k)) : Prop :=
  ∀ q : Fin k, (u : ℕ).testBit q = true → e q ∈ C

instance pkSub_dec (e : Fin k ↪ Fin N) (C : Finset (Fin N)) : DecidablePred (pkSub e C) :=
  fun u => by unfold pkSub; infer_instance

/-- **Patterns and subcubes.** The sum over the patterns `u ⊆ C` of a function of the flipped
state `t ⊕ u` is the sum over the states agreeing with `t` off `C` (for `C ⊆ S`, `S = e(Fin k)`). -/
theorem pk_sum_agree (e : Fin k ↪ Fin N) {S C : Finset (Fin N)}
    (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) (hC : C ⊆ S) (t : State N) (G : State N → ℝ) :
    ∑ u : Fin (2 ^ k), (if pkSub e C u then G (pkFlip e t u) else 0)
      = ∑ t' ∈ agree ((S \ C) ∪ Sᶜ) t, G t' := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun u => pkFlip e t u)
    (fun t' => pkEnc k (fun q => decide (t' (e q) ≠ t (e q)))) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    rw [mem_agree]
    intro j hj
    rw [pkFlip, ite_eq_right]
    rintro ⟨q, rfl, hq⟩
    have hC' := hu q hq
    rcases mem_union.1 hj with h | h
    · exact (mem_sdiff.1 h).2 hC'
    · exact (mem_compl.1 h) (hC hC')
  · intro t' ht'
    simp only [mem_filter, mem_univ, true_and]
    intro q hq
    rw [pk_testBit_enc] at hq
    have hne : t' (e q) ≠ t (e q) := of_decide_eq_true hq
    rw [mem_agree] at ht'
    by_contra hnC
    have heS : e q ∈ S := (hS _).2 ⟨q, rfl⟩
    exact hne (ht' _ (mem_union_left _ (mem_sdiff.2 ⟨heS, hnC⟩)))
  · intro u _
    show pkEnc k (fun q => decide (pkFlip e t u (e q) ≠ t (e q))) = u
    conv_rhs => rw [← pk_enc_bits u]
    congr 1
    funext q
    rw [pkFlip_e]
    cases h : (u : ℕ).testBit q <;> cases t (e q) <;> simp
  · intro t' ht'
    rw [mem_agree] at ht'
    show pkFlip e t (pkEnc k fun q => decide (t' (e q) ≠ t (e q))) = t'
    funext j
    by_cases hj : ∃ q, e q = j
    · obtain ⟨q, rfl⟩ := hj
      rw [pkFlip_e, pk_testBit_enc]
      cases h1 : t' (e q) <;> cases h2 : t (e q) <;> simp
    · push Not at hj
      rw [pkFlip_of_not e t _ hj]
      have hjS : j ∉ S := fun h => by
        obtain ⟨q, hq⟩ := (hS j).1 h
        exact hj q hq
      exact (ht' j (mem_union_right _ (mem_compl.2 hjS))).symm
  · intro u _
    rfl

/-- The number of patterns inside `C` is `2^|C|`. -/
theorem pk_card_sub (e : Fin k ↪ Fin N) {S C : Finset (Fin N)}
    (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) (hC : C ⊆ S) :
    ∑ u : Fin (2 ^ k), (if pkSub e C u then (1 : ℝ) else 0) = (2 : ℝ) ^ C.card := by
  have h := pk_sum_agree e hS hC (fun _ => false) (fun _ => (1 : ℝ))
  rw [h, sum_const, card_agree, nsmul_eq_mul, mul_one]
  have hdisj : Disjoint (S \ C) Sᶜ :=
    disjoint_left.2 fun x hx hx' => (mem_compl.1 hx') (mem_sdiff.1 hx).1
  rw [card_union_of_disjoint hdisj, card_sdiff_of_subset hC, card_compl, Fintype.card_fin]
  have hSN : S.card ≤ N := card_le_N S
  have hCS : C.card ≤ S.card := card_le_card hC
  push_cast
  congr 1
  omega

/-- **One unit of the bridge.** If `F` at every flipped pattern `t ⊕ u` is within `φ` of
`σ ξ_u + b`, then the conditioned-minus-averaged form of `F` is within `2φ` of `σ` times the
model form `ξ_0 - 2^{-|C|} ∑_{u ⊆ C} ξ_u`. -/
theorem pk_unit_bridge (e : Fin k ↪ Fin N) {S C : Finset (Fin N)}
    (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) (hC : C ⊆ S) (t : State N) (F : State N → ℝ)
    (ξ : Fin (2 ^ k) → ℝ) (u0 : Fin (2 ^ k)) (hu0 : (u0 : ℕ) = 0) {σ b φ : ℝ}
    (hF : ∀ u, |F (pkFlip e t u) - (σ * ξ u + b)| ≤ φ) :
    |(F t - (∑ t' ∈ agree ((S \ C) ∪ Sᶜ) t, F t') / (2 : ℝ) ^ C.card)
      - σ * (ξ u0 - ((2 : ℝ) ^ C.card)⁻¹ *
          ∑ u : Fin (2 ^ k), if pkSub e C u then ξ u else 0)| ≤ 2 * φ := by
  set d : Fin (2 ^ k) → ℝ := fun u => F (pkFlip e t u) - (σ * ξ u + b) with hd
  have hsum := pk_sum_agree e hS hC t F
  have hcard := pk_card_sub e hS hC
  have hpow : (0 : ℝ) < 2 ^ C.card := by positivity
  have hFt : F t = σ * ξ u0 + b + d u0 := by
    simp only [hd, pkFlip_zero e t u0 hu0]; ring
  have hsplit : ∑ u : Fin (2 ^ k), (if pkSub e C u then F (pkFlip e t u) else 0)
      = σ * (∑ u : Fin (2 ^ k), if pkSub e C u then ξ u else 0)
        + b * (∑ u : Fin (2 ^ k), if pkSub e C u then (1 : ℝ) else 0)
        + ∑ u : Fin (2 ^ k), if pkSub e C u then d u else 0 := by
    rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun u _ => ?_
    by_cases hu : pkSub e C u
    · simp only [hu, ite_true, hd]; ring
    · simp only [hu, ite_false]; ring
  have hdb : |∑ u : Fin (2 ^ k), (if pkSub e C u then d u else 0)| ≤ φ * 2 ^ C.card := by
    calc |∑ u : Fin (2 ^ k), (if pkSub e C u then d u else 0)|
        ≤ ∑ u : Fin (2 ^ k), (if pkSub e C u then φ else 0) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun u _ => ?_)
          by_cases hu : pkSub e C u
          · simp only [hu, ite_true]; exact hF u
          · simp only [hu, ite_false, abs_zero, le_refl]
      _ = φ * 2 ^ C.card := by
          rw [← hcard, mul_sum]
          refine sum_congr rfl fun u _ => ?_
          by_cases hu : pkSub e C u
          · simp only [hu, ite_true, mul_one]
          · simp only [hu, ite_false, mul_zero]
  rw [← hsum, hsplit, hcard, hFt]
  set Sξ := ∑ u : Fin (2 ^ k), if pkSub e C u then ξ u else 0
  set Sd := ∑ u : Fin (2 ^ k), if pkSub e C u then d u else 0
  have key : σ * ξ u0 + b + d u0 - (σ * Sξ + b * 2 ^ C.card + Sd) / 2 ^ C.card
      - σ * (ξ u0 - (2 ^ C.card)⁻¹ * Sξ) = d u0 - Sd / 2 ^ C.card := by
    field_simp
    ring
  rw [key]
  have h1 : |d u0| ≤ φ := hF u0
  have h2 : |Sd / 2 ^ C.card| ≤ φ := by
    rw [abs_div, abs_of_pos hpow, div_le_iff₀ hpow]; exact hdb
  calc _ ≤ |d u0| + |Sd / 2 ^ C.card| := abs_sub _ _
    _ ≤ 2 * φ := by linarith

/-- The table condition of `lpTab` is the pattern condition `pkSub`. -/
lemma pk_lpTab_agree {S : Finset (Fin N)} (e : Fin k ↪ Fin N)
    (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) (θ : SysPartition N S) (i : Fin k) (u : ℕ) :
    cd_agree k (cd_at (lpTab e hS θ) i) u 0 = true ↔
      ∀ q : Fin k, u.testBit q = true → e q ∈ profile θ (e i) := by
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

/-- The sum over a `k`-set is the sum over its ordering. -/
lemma pk_sum_S {S : Finset (Fin N)} (e : Fin k ↪ Fin N) (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
    (f : Fin N → ℝ) : ∑ j ∈ S, f j = ∑ i : Fin k, f (e i) := by
  have hSm : S = univ.map e := by
    ext x
    simp [hS x]
  rw [Finset.sum_congr hSm fun _ _ => rfl, sum_map]

lemma pk_card_S {S : Finset (Fin N)} (e : Fin k ↪ Fin N) (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) :
    S.card = k := by
  have hSm : S = univ.map e := by
    ext x
    simp [hS x]
  rw [hSm, card_map, card_univ, Fintype.card_fin]

/-- One unit of the numerator difference `D_j(θ, t)` in the pattern form. -/
lemma pk_ur_D_eq (w : Param N) {S : Finset (Fin N)} (e : Fin k ↪ Fin N)
    (θ : SysPartition N S) (t : State N) (i : Fin k) :
    ur_D w θ t (e i) = Num w S S t (e i) -
      (∑ t' ∈ agree ((S \ profile θ (e i)) ∪ Sᶜ) t, Num w S S t' (e i)) /
        (2 : ℝ) ^ (profile θ (e i)).card := by
  unfold ur_D
  rw [Num_eq_avg w S (S \ profile θ (e i)) t (e i)]
  congr 3
  have hC := prof_profile_subset θ (e i)
  rw [card_sdiff_of_subset hC]
  have := card_le_card hC
  omega

end Patterns

/-! ## 2. The bridge from the numerators to the LP models -/

/-- **Bridge for triples.** If every full numerator of the triple `S` (ordered by `e`) at the
patterns `t ⊕ u` is within `φ` of `σ ξ_{i,u} + B_i`, then `∑_{j ∈ S} D_j(θ, t)` is within `6φ` of
`σ` times the triple LP value of the table of `θ`. -/
theorem pk_bridge3 (w : Param N) {S : Finset (Fin N)} (e : Fin 3 ↪ Fin N)
    (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) (θ : SysPartition N S) (t : State N)
    (ξ : Fin 3 → Fin 8 → ℝ) {σ φ : ℝ} (B : Fin N → ℝ)
    (h : ∀ i u, |Num w S S (pkFlip e t u) (e i) - (σ * ξ i u + B (e i))| ≤ φ) :
    |∑ j ∈ S, ur_D w θ t j - σ * lp3V (lpTab e hS θ) ξ| ≤ 6 * φ := by
  rw [pk_sum_S e hS, lp3V, mul_sum, ← sum_sub_distrib]
  have hunit : ∀ i : Fin 3, |ur_D w θ t (e i) - σ * (ξ i 0 -
      ((2 : ℝ) ^ cd_card 3 (lpTab e hS θ) i)⁻¹ *
        ∑ u : Fin 8, if cd_agree 3 (cd_at (lpTab e hS θ) i) u 0 = true then ξ i u else 0)|
        ≤ 2 * φ := by
    intro i
    have hsum : (∑ u : Fin 8, if cd_agree 3 (cd_at (lpTab e hS θ) i) u 0 = true then ξ i u else 0)
        = ∑ u : Fin (2 ^ 3), if pkSub e (profile θ (e i)) u then ξ i u else 0 := by
      refine sum_congr rfl fun u _ => ?_
      exact if_congr (pk_lpTab_agree e hS θ i u) rfl rfl
    rw [hsum, lpTab_card, pk_ur_D_eq w e θ t i]
    exact pk_unit_bridge e hS (prof_profile_subset θ (e i)) t (fun t' => Num w S S t' (e i))
      (ξ i) 0 rfl (fun u => h i u)
  calc |∑ i : Fin 3, (ur_D w θ t (e i) - σ * (ξ i 0 -
        ((2 : ℝ) ^ cd_card 3 (lpTab e hS θ) i)⁻¹ *
          ∑ u : Fin 8, if cd_agree 3 (cd_at (lpTab e hS θ) i) u 0 = true then ξ i u else 0))|
      ≤ ∑ i : Fin 3, 2 * φ := (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => hunit i)
    _ = 6 * φ := by rw [sum_const, card_univ, Fintype.card_fin]; ring

/-- **Bridge for 4-sets** (same statement, `8φ`). -/
theorem pk_bridge4 (w : Param N) {S : Finset (Fin N)} (e : Fin 4 ↪ Fin N)
    (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) (θ : SysPartition N S) (t : State N)
    (ξ : Fin 4 → Fin 16 → ℝ) {σ φ : ℝ} (B : Fin N → ℝ)
    (h : ∀ i u, |Num w S S (pkFlip e t u) (e i) - (σ * ξ i u + B (e i))| ≤ φ) :
    |∑ j ∈ S, ur_D w θ t j - σ * lp4V (lpTab e hS θ) ξ| ≤ 8 * φ := by
  rw [pk_sum_S e hS, lp4V, mul_sum, ← sum_sub_distrib]
  have hunit : ∀ i : Fin 4, |ur_D w θ t (e i) - σ * (ξ i 0 -
      ((2 : ℝ) ^ cd_card 4 (lpTab e hS θ) i)⁻¹ *
        ∑ u : Fin 16, if cd_agree 4 (cd_at (lpTab e hS θ) i) u 0 = true then ξ i u else 0)|
        ≤ 2 * φ := by
    intro i
    have hsum : (∑ u : Fin 16, if cd_agree 4 (cd_at (lpTab e hS θ) i) u 0 = true then ξ i u else 0)
        = ∑ u : Fin (2 ^ 4), if pkSub e (profile θ (e i)) u then ξ i u else 0 := by
      refine sum_congr rfl fun u _ => ?_
      exact if_congr (pk_lpTab_agree e hS θ i u) rfl rfl
    rw [hsum, lpTab_card, pk_ur_D_eq w e θ t i]
    exact pk_unit_bridge e hS (prof_profile_subset θ (e i)) t (fun t' => Num w S S t' (e i))
      (ξ i) 0 rfl (fun u => h i u)
  calc |∑ i : Fin 4, (ur_D w θ t (e i) - σ * (ξ i 0 -
        ((2 : ℝ) ^ cd_card 4 (lpTab e hS θ) i)⁻¹ *
          ∑ u : Fin 16, if cd_agree 4 (cd_at (lpTab e hS θ) i) u 0 = true then ξ i u else 0))|
      ≤ ∑ i : Fin 4, 2 * φ := (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => hunit i)
    _ = 8 * φ := by rw [sum_const, card_univ, Fintype.card_fin]; ring

/-! ## 3. The LP bounds with the own entries bounded by `y0` -/

/-- Every positive coefficient of the certificate form `W` sits on an own entry (pattern `0`). -/
def lp3OwnOK (c : LP3Cert) : Bool :=
  (List.range 24).all fun q => (q % 8 == 0) || decide (lp3W c (cd_fz 3 c.C 0) q ≤ 0)

/-- Each of the 21 non-all-cut profiles has a certificate passing `lp3Check` and `lp3OwnOK`. -/
def lp3AllOwnOK : Bool :=
  profiles3.all fun C => (C == lp3AllCut) ||
    lp3Certs.any fun c => (c.C == C) && lp3Check c && lp3OwnOK c

theorem lp3AllOwnOK_true : lp3AllOwnOK = true := by decide +kernel

lemma lp3Lin_le_own (a : ℕ → ℤ) (ha : ∀ q < 24, q % 8 ≠ 0 → a q ≤ 0)
    {ξ : Fin 3 → Fin 8 → ℝ} (hnn : ∀ i u, 0 ≤ ξ i u) {y0 : ℝ} (hown : ∀ i, ξ i 0 ≤ y0) :
    lp3Lin a ξ ≤ y0 * ((lp3Sum fun q => max (a q) 0 : ℤ) : ℝ) := by
  rw [lp3Sum_cast, lp3Lin, mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun u _ => ?_
  have hm0 : (0 : ℝ) ≤ ((max (a (u + 8 * i)) 0 : ℤ) : ℝ) := by exact_mod_cast le_max_right _ _
  have hm : (a (u + 8 * i) : ℝ) ≤ ((max (a (u + 8 * i)) 0 : ℤ) : ℝ) := by
    exact_mod_cast le_max_left _ _
  by_cases hu : (u : ℕ) = 0
  · have hu' : u = 0 := Fin.ext hu
    subst hu'
    calc _ ≤ _ := mul_le_mul_of_nonneg_right hm (hnn i 0)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hown i) hm0
      _ = _ := mul_comm _ _
  · have hu8 := u.2
    have hi3 := i.2
    have hq : ((u : ℕ) + 8 * (i : ℕ)) % 8 ≠ 0 := by omega
    have hlt : (u : ℕ) + 8 * (i : ℕ) < 24 := by omega
    have hneg := ha _ hlt hq
    have hmax : max (a (u + 8 * i)) 0 = 0 := max_eq_right hneg
    rw [hmax]
    push_cast
    rw [mul_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hneg) (hnn i u)

/-- Soundness of a certificate whose positive coefficients sit on own entries: the box is
replaced by `ξ ≥ 0` and `ξ i 0 ≤ y0`. -/
theorem lp3_gen_sound_own (c : LP3Cert) (f : ℕ → ℤ) (hok : lp3RowsOK c = true)
    (hW0 : ∀ q < 24, q % 8 ≠ 0 → lp3W c f q ≤ 0)
    {ξ : Fin 3 → Fin 8 → ℝ} (hnn : ∀ i u, 0 ≤ ξ i u) {y0 : ℝ} (hown : ∀ i, ξ i 0 ≤ y0) {e : ℝ}
    (hmin : ∀ C' ∈ profiles3, lp3V c.C ξ / cd_cc 3 c.C ≤ lp3V C' ξ / cd_cc 3 C' + e)
    {L : ℝ} (hL : L ≤ lp3V c.C ξ) :
    (c.wF : ℝ) * lp3Lin f ξ ≤ y0 * (lp3U c f : ℝ) - 8 * c.nu * L
      + 8 * e * lp3LamL c.C c.rows := by
  simp only [lp3RowsOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨_, hc⟩, hrows⟩ := hok
  have hrows' : ∀ r ∈ c.rows, r.1 ∈ profiles3 ∧ 0 < cd_cc 3 r.1 := fun r hr => by
    have := hrows r hr
    exact ⟨lp3_mem_of_contains this.1, this.2⟩
  have hW : lp3Lin (lp3W c f) ξ ≤ y0 * (lp3U c f : ℝ) := lp3Lin_le_own (lp3W c f) hW0 hnn hown
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

/-- **The triple LP bound at scale `y0`.** If the own entries `ξ i 0` are at most `y0` (and all
entries are `≥ 0`), a non-all-cut near-minimiser has value at most `(5/3) y0 + (40/3) e`. -/
theorem lp3_bound_own {C : List (List Bool)} (hC : C ∈ profiles3) (hne : C ≠ lp3AllCut)
    {ξ : Fin 3 → Fin 8 → ℝ} (hnn : ∀ i u, 0 ≤ ξ i u) {y0 : ℝ} (hy0 : 0 ≤ y0)
    (hown : ∀ i, ξ i 0 ≤ y0) {e : ℝ} (he : 0 ≤ e)
    (hmin : ∀ C' ∈ profiles3, lp3V C ξ / cd_cc 3 C ≤ lp3V C' ξ / cd_cc 3 C' + e) :
    lp3V C ξ ≤ 5 / 3 * y0 + 40 / 3 * e := by
  have h := lp3AllOwnOK_true
  simp only [lp3AllOwnOK, List.all_eq_true] at h
  have hC' := h C hC
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true] at hC'
  rcases hC' with h1 | ⟨c, _, ⟨hcC, hchk⟩, hown'⟩
  · exact absurd h1 hne
  · subst hcC
    simp only [lp3Check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
    obtain ⟨⟨⟨hok, hnu⟩, hU⟩, hLam⟩ := hchk
    have hW0 : ∀ q < 24, q % 8 ≠ 0 → lp3W c (cd_fz 3 c.C 0) q ≤ 0 := by
      simp only [lp3OwnOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hown'
      intro q hq h8
      rcases hown' q hq with h | h
      · exact absurd h h8
      · exact h
    have hg := lp3_gen_sound_own c (cd_fz 3 c.C 0) hok hW0 hnn hown hmin (le_refl (lp3V c.C ξ))
    rw [lp3V_lin, hnu] at hg
    have hw : (0 : ℝ) < c.wF := by
      simp only [lp3RowsOK, Bool.and_eq_true, decide_eq_true_eq] at hok
      exact_mod_cast hok.1.1
    have hU' : 3 * (lp3U c (cd_fz 3 c.C 0) : ℝ) ≤ 40 * c.wF := by exact_mod_cast hU
    have hL' : 3 * (lp3LamL c.C c.rows : ℝ) ≤ 40 * c.wF := by exact_mod_cast hLam
    have h4 := mul_le_mul_of_nonneg_left hL' he
    have h5 := mul_le_mul_of_nonneg_left hU' hy0
    push_cast at hg
    have h3 : (c.wF : ℝ) * (24 * lp3V c.C ξ) ≤ c.wF * (40 * y0 + 320 * e) := by nlinarith
    have h6 := le_of_mul_le_mul_left h3 hw
    linarith

/-- **The triple LP bound at scale `y0`, for a system partition** of a 3-set ordered by `e`. -/
theorem lp3_bound_own_sys {S : Finset (Fin N)} (e : Fin 3 ↪ Fin N)
    (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) (θ : SysPartition N S)
    (hne : ∃ j ∈ S, profile θ j ≠ S.erase j)
    {ξ : Fin 3 → Fin 8 → ℝ} (hnn : ∀ i u, 0 ≤ ξ i u) {y0 : ℝ} (hy0 : 0 ≤ y0)
    (hown : ∀ i, ξ i 0 ≤ y0) {ε : ℝ} (hε : 0 ≤ ε)
    (hmin : ∀ θ' : SysPartition N S, lp3V (lpTab e hS θ) ξ / sysCutCount θ ≤
      lp3V (lpTab e hS θ') ξ / sysCutCount θ' + ε) :
    lp3V (lpTab e hS θ) ξ ≤ 5 / 3 * y0 + 40 / 3 * ε := by
  refine lp3_bound_own (lpTab_mem e hS θ) (lpTab_ne_allCut e hS θ hne) hnn hy0 hown hε
    fun C' hC' => ?_
  obtain ⟨g, δ, hv, rfl⟩ := profiles3_realized C' hC'
  obtain ⟨θ', hθ'⟩ := lpTab_realize e hS g δ hv
  have hv' : lp3V (cd_profOf 3 g δ) ξ = lp3V (lpTab e hS θ') ξ := (lp3V_congr hθ' ξ).symm
  have hcc' : cd_cc 3 (cd_profOf 3 g δ) = sysCutCount θ' := by
    rw [← lp3cc_congr hθ', lpTab_cc]
  rw [hv', hcc', lpTab_cc]
  exact hmin θ'

/-- The 4-set analogue of `lp3OwnOK`. -/
def lp4OwnOK (c : LP3Cert) : Bool :=
  (List.range 64).all fun q => (q % 16 == 0) || decide (lp4W c (cd_fz 4 c.C 0) q ≤ 0)

/-- Each of the 149 non-all-cut 4-set profiles has a certificate passing `lp4Check` and
`lp4OwnOK`. -/
def lp4AllOwnOK : Bool :=
  profiles4.all fun C => (C == lp4AllCut) ||
    lp4Certs.any fun c => (c.C == C) && lp4Check c && lp4OwnOK c

theorem lp4AllOwnOK_true : lp4AllOwnOK = true := by decide +kernel

lemma lp4Lin_le_own (a : ℕ → ℤ) (ha : ∀ q < 64, q % 16 ≠ 0 → a q ≤ 0)
    {ξ : Fin 4 → Fin 16 → ℝ} (hnn : ∀ i u, 0 ≤ ξ i u) {y0 : ℝ} (hown : ∀ i, ξ i 0 ≤ y0) :
    lp4Lin a ξ ≤ y0 * ((lp4Sum fun q => max (a q) 0 : ℤ) : ℝ) := by
  rw [lp4Sum_cast, lp4Lin, mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun u _ => ?_
  have hm0 : (0 : ℝ) ≤ ((max (a (u + 16 * i)) 0 : ℤ) : ℝ) := by exact_mod_cast le_max_right _ _
  have hm : (a (u + 16 * i) : ℝ) ≤ ((max (a (u + 16 * i)) 0 : ℤ) : ℝ) := by
    exact_mod_cast le_max_left _ _
  by_cases hu : (u : ℕ) = 0
  · have hu' : u = 0 := Fin.ext hu
    subst hu'
    calc _ ≤ _ := mul_le_mul_of_nonneg_right hm (hnn i 0)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hown i) hm0
      _ = _ := mul_comm _ _
  · have hu8 := u.2
    have hi3 := i.2
    have hq : ((u : ℕ) + 16 * (i : ℕ)) % 16 ≠ 0 := by omega
    have hlt : (u : ℕ) + 16 * (i : ℕ) < 64 := by omega
    have hneg := ha _ hlt hq
    have hmax : max (a (u + 16 * i)) 0 = 0 := max_eq_right hneg
    rw [hmax]
    push_cast
    rw [mul_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hneg) (hnn i u)

theorem lp4_gen_sound_own (c : LP3Cert) (f : ℕ → ℤ) (hok : lp4RowsOK c = true)
    (hW0 : ∀ q < 64, q % 16 ≠ 0 → lp4W c f q ≤ 0)
    {ξ : Fin 4 → Fin 16 → ℝ} (hnn : ∀ i u, 0 ≤ ξ i u) {y0 : ℝ} (hown : ∀ i, ξ i 0 ≤ y0) {e : ℝ}
    (hmin : ∀ C' ∈ profiles4, lp4V c.C ξ / cd_cc 4 c.C ≤ lp4V C' ξ / cd_cc 4 C' + e)
    {L : ℝ} (hL : L ≤ lp4V c.C ξ) :
    (c.wF : ℝ) * lp4Lin f ξ ≤ y0 * (lp4U c f : ℝ) - 16 * c.nu * L
      + 16 * e * lp4LamL c.C c.rows := by
  simp only [lp4RowsOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨_, hc⟩, hrows⟩ := hok
  have hrows' : ∀ r ∈ c.rows, r.1 ∈ profiles4 ∧ 0 < cd_cc 4 r.1 := fun r hr => by
    have := hrows r hr
    exact ⟨lp3_mem_of_contains this.1, this.2⟩
  have hW : lp4Lin (lp4W c f) ξ ≤ y0 * (lp4U c f : ℝ) := lp4Lin_le_own (lp4W c f) hW0 hnn hown
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

/-- **The 4-set LP bound at scale `y0`.** -/
theorem lp4_bound_own {C : List (List Bool)} (hC : C ∈ profiles4) (hne : C ≠ lp4AllCut)
    {ξ : Fin 4 → Fin 16 → ℝ} (hnn : ∀ i u, 0 ≤ ξ i u) {y0 : ℝ} (hy0 : 0 ≤ y0)
    (hown : ∀ i, ξ i 0 ≤ y0) {e : ℝ} (he : 0 ≤ e)
    (hmin : ∀ C' ∈ profiles4, lp4V C ξ / cd_cc 4 C ≤ lp4V C' ξ / cd_cc 4 C' + e) :
    lp4V C ξ ≤ 11 / 4 * y0 + 165 / 4 * e := by
  have h := lp4AllOwnOK_true
  simp only [lp4AllOwnOK, List.all_eq_true] at h
  have hC' := h C hC
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true] at hC'
  rcases hC' with h1 | ⟨c, _, ⟨hcC, hchk⟩, hown'⟩
  · exact absurd h1 hne
  · subst hcC
    simp only [lp4Check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
    obtain ⟨⟨⟨hok, hnu⟩, hU⟩, hLam⟩ := hchk
    have hW0 : ∀ q < 64, q % 16 ≠ 0 → lp4W c (cd_fz 4 c.C 0) q ≤ 0 := by
      simp only [lp4OwnOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hown'
      intro q hq h8
      rcases hown' q hq with h | h
      · exact absurd h h8
      · exact h
    have hg := lp4_gen_sound_own c (cd_fz 4 c.C 0) hok hW0 hnn hown hmin (le_refl (lp4V c.C ξ))
    rw [lp4V_lin, hnu] at hg
    have hw : (0 : ℝ) < c.wF := by
      simp only [lp4RowsOK, Bool.and_eq_true, decide_eq_true_eq] at hok
      exact_mod_cast hok.1.1
    have hU' : (lp4U c (cd_fz 4 c.C 0) : ℝ) ≤ 44 * c.wF := by exact_mod_cast hU
    have hL' : 4 * (lp4LamL c.C c.rows : ℝ) ≤ 165 * c.wF := by exact_mod_cast hLam
    have h4 := mul_le_mul_of_nonneg_left hL' he
    have h5 := mul_le_mul_of_nonneg_left hU' hy0
    push_cast at hg
    have h3 : (c.wF : ℝ) * (64 * lp4V c.C ξ) ≤ c.wF * (176 * y0 + 2640 * e) := by nlinarith
    have h6 := le_of_mul_le_mul_left h3 hw
    linarith

/-- **The 4-set LP bound at scale `y0`, for a system partition** of a 4-set ordered by `e`. -/
theorem lp4_bound_own_sys {S : Finset (Fin N)} (e : Fin 4 ↪ Fin N)
    (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) (θ : SysPartition N S)
    (hne : ∃ j ∈ S, profile θ j ≠ S.erase j)
    {ξ : Fin 4 → Fin 16 → ℝ} (hnn : ∀ i u, 0 ≤ ξ i u) {y0 : ℝ} (hy0 : 0 ≤ y0)
    (hown : ∀ i, ξ i 0 ≤ y0) {ε : ℝ} (hε : 0 ≤ ε)
    (hmin : ∀ θ' : SysPartition N S, lp4V (lpTab e hS θ) ξ / sysCutCount θ ≤
      lp4V (lpTab e hS θ') ξ / sysCutCount θ' + ε) :
    lp4V (lpTab e hS θ) ξ ≤ 11 / 4 * y0 + 165 / 4 * ε := by
  refine lp4_bound_own (lpTab_mem4 e hS θ) (lpTab_ne_allCut4 e hS θ hne) hnn hy0 hown hε
    fun C' hC' => ?_
  obtain ⟨g, δ, hv, rfl⟩ := profiles4_realized C' hC'
  obtain ⟨θ', hθ'⟩ := lpTab_realize e hS g δ hv
  have hv' : lp4V (cd_profOf 4 g δ) ξ = lp4V (lpTab e hS θ') ξ := (lp4V_congr hθ' ξ).symm
  have hcc' : cd_cc 4 (cd_profOf 4 g δ) = sysCutCount θ' := by
    rw [← lp4cc_congr hθ', lpTab_cc]
  rw [hv', hcc', lpTab_cc]
  exact hmin θ'

/-! ## 4. The upper reduction exposing the minimum information partition -/

/-- **Upper reduction with the MIP exposed** (a copy of `ur_upper_reduce`).  With
`w = flipP s z`, if every numerator of `S` is within `η` of `A` (`3η ≤ A`) and `φ_s(S) > X ≥ 0`,
then either
* there are maximal states `tc`, `te` and a partition `θ ∈ sysMipSetAt … tc te` with
  `X < sysPhiAt θ tc te`, `tc` an `e`-near-argmax of `Σξ`, `θ` an `e`-near-minimiser of
  `F_·(tc)/cc` and `X < ρ^k 2^{-k} σ/(A ln 2) · (F_θ(tc) + e)`; or
* some tied effect state `te` and partition `θ` have `X < k² φ_e(θ, te)` while
  `φ_e(θ, te) < ρ^k 2^{-k} · 2kη/((A-η) ln 2)`. -/
theorem ur_upper_reduce_mip {z : Param N} (hz : z ∈ openCube N) (s : State N)
    {S : Finset (Fin N)} {A η σ X : ℝ} (hη : 0 ≤ η) (hηA : 3 * η ≤ A) (hA : 0 < A)
    (hσ : 0 < σ) (hX : 0 ≤ X)
    (hlev : ∀ Y ⊆ S, ∀ t, ∀ i ∈ S, |Num (flipP s z) S Y t i - A| ≤ η)
    (hphi : X < phi z s S) :
    (∃ tc ∈ sysMaxCauseStates (tpmOf z) S s s, ∃ te ∈ sysMaxEffStates (tpmOf z) S s s,
      ∃ θ ∈ sysMipSetAt (tpmOf z) S s s tc te,
      X < sysPhiAt (tpmOf z) S s θ s tc te ∧
      (∀ t', ur_xi (flipP s z) S A σ t' ≤ ur_xi (flipP s z) S A σ tc + ur_err S.card A η σ) ∧
      (∀ θ' : SysPartition N S, ur_F (flipP s z) θ tc σ / (sysCutCount θ : ℝ) ≤
        ur_F (flipP s z) θ' tc σ / (sysCutCount θ' : ℝ) + ur_err S.card A η σ) ∧
      X < ur_rho S.card A η / 2 ^ S.card * (σ / (A * Real.log 2)) *
        (ur_F (flipP s z) θ tc σ + ur_err S.card A η σ)) ∨
    (∃ te ∈ sysMaxEffStates (tpmOf z) S s s, ∃ θ : SysPartition N S,
      X < (S.card : ℝ) ^ 2 * sysPhiE (tpmOf z) S s θ s te ∧
      sysPhiE (tpmOf z) S s θ s te <
        ur_rho S.card A η / 2 ^ S.card * (2 * S.card * η / ((A - η) * Real.log 2))) := by
  set w := flipP s z with hw
  have hηA' : η < A := by linarith
  have hAη : 0 < A - η := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨p, hp, hpX⟩ := ur_exists_gt hX hphi
  obtain ⟨hc, he⟩ := mem_product.1 hp
  obtain ⟨θh, hθh, hθX⟩ := ur_exists_gt hX hpX
  set tc := p.1
  set te := p.2
  have hmip := mem_argminSet.1 hθh
  have hlevS : ∀ t, ∀ i ∈ S, |Num w S S t i - A| ≤ η := fun t i hi =>
    hlev S (subset_refl _) t i hi
  have hbU := ur_back_le s hz hη hηA' hlevS tc
  have hb0 : 0 < sysBackCause (tpmOf z) S s s tc :=
    lt_of_lt_of_le (by positivity) (sysBackCause_ge_of_mem hz s tc hc)
  set b := sysBackCause (tpmOf z) S s s tc
  set ρ := ur_rho S.card A η / 2 ^ S.card
  set R := S.card * (2 * η ^ 2 / (A * (A - η))) with hR
  have hR0 : 0 ≤ R := by positivity
  set P : SysPartition N S → ℝ := fun θ => ∑ i ∈ S, ur_D w θ tc i with hP
  have hC : ∀ θ : SysPartition N S, sysPhiC (tpmOf z) S s θ s tc =
      b * pos (ur_G w θ tc / Real.log 2) := by
    intro θ
    unfold sysPhiC
    rw [ur_logb_eq s hz tc θ]
  have hnear : ∀ θ : SysPartition N S, |ur_G w θ tc - P θ / A| ≤ R := fun θ =>
    ur_G_near hη hηA' w tc (fun Y hY i hi => hlev Y hY tc i hi) θ
  have hcc1 : ∀ θ : SysPartition N S, (1 : ℝ) ≤ sysCutCount θ := fun θ => by
    exact_mod_cast sysCutCount_pos θ
  have hCle : ∀ θ : SysPartition N S, sysPhiC (tpmOf z) S s θ s tc ≤
      ρ * (2 * S.card * η / ((A - η) * Real.log 2)) := by
    intro θ
    have h1 := (abs_le.1 (hnear θ)).2
    have h2 : P θ ≤ S.card * (2 * η) := by
      have hs := sum_le_card_nsmul S (fun i => ur_D w θ tc i) (2 * η) fun i hi => by
        have hx := hlev S (subset_refl _) tc i hi
        have hy' := hlev _ (sdiff_subset : S \ profile θ i ⊆ S) tc i hi
        rw [abs_le] at hx hy'
        unfold ur_D; linarith
      rwa [nsmul_eq_mul] at hs
    have h3 : P θ / A ≤ S.card * (2 * η) / A := div_le_div_of_nonneg_right h2 hA.le
    have h4 : S.card * (2 * η) / A + R = 2 * S.card * η / (A - η) := by
      rw [hR]; field_simp; ring
    have hG : ur_G w θ tc ≤ 2 * S.card * η / (A - η) := by linarith
    have hp : pos (ur_G w θ tc / Real.log 2) ≤ 2 * S.card * η / ((A - η) * Real.log 2) := by
      unfold pos
      refine max_le (by positivity) ?_
      rw [← div_div]
      exact div_le_div_of_nonneg_right hG hlog2.le
    rw [hC θ]
    exact mul_le_mul hbU hp (pos_nonneg _)
      (div_nonneg (pow_nonneg (div_nonneg (by linarith) hAη.le) _) (by positivity))
  by_cases hcase : ∀ θ : SysPartition N S,
      sysPhiC (tpmOf z) S s θ s tc ≤ sysPhiE (tpmOf z) S s θ s te
  · left
    have hAt : ∀ θ, sysPhiAt (tpmOf z) S s θ s tc te = sysPhiC (tpmOf z) S s θ s tc :=
      fun θ => min_eq_left (hcase θ)
    have hθX' : X < b * pos (ur_G w θh tc / Real.log 2) := by
      have := hθX; simp only [hAt, hC] at this; exact this
    have hGh : 0 < ur_G w θh tc := by
      by_contra hneg
      push Not at hneg
      have : pos (ur_G w θh tc / Real.log 2) = 0 :=
        max_eq_left (div_nonpos_of_nonpos_of_nonneg hneg hlog2.le)
      rw [this, mul_zero] at hθX'
      linarith
    have hposh : pos (ur_G w θh tc / Real.log 2) = ur_G w θh tc / Real.log 2 :=
      max_eq_right (div_pos hGh hlog2).le
    have hGcmp : ∀ θ : SysPartition N S, ur_G w θh tc / (sysCutCount θh : ℝ) ≤
        ur_G w θ tc / (sysCutCount θ : ℝ) := by
      intro θ
      have hm := hmip θ
      unfold normalizedSysPhiAt at hm
      rw [hAt, hAt, hC, hC, hposh] at hm
      have hc0 : (0 : ℝ) < sysCutCount θ := by linarith [hcc1 θ]
      have hch0 : (0 : ℝ) < sysCutCount θh := by linarith [hcc1 θh]
      have hGθ : 0 < ur_G w θ tc := by
        by_contra hneg
        push Not at hneg
        have : pos (ur_G w θ tc / Real.log 2) = 0 :=
          max_eq_left (div_nonpos_of_nonpos_of_nonneg hneg hlog2.le)
        rw [this, mul_zero, zero_div] at hm
        have : 0 < b * (ur_G w θh tc / Real.log 2) / (sysCutCount θh : ℝ) := by positivity
        linarith
      have hpθ : pos (ur_G w θ tc / Real.log 2) = ur_G w θ tc / Real.log 2 :=
        max_eq_right (div_pos hGθ hlog2).le
      rw [hpθ] at hm
      have e1 : b * (ur_G w θh tc / Real.log 2) / (sysCutCount θh : ℝ) =
          b / Real.log 2 * (ur_G w θh tc / (sysCutCount θh : ℝ)) := by ring
      have e2 : b * (ur_G w θ tc / Real.log 2) / (sysCutCount θ : ℝ) =
          b / Real.log 2 * (ur_G w θ tc / (sysCutCount θ : ℝ)) := by ring
      rw [e1, e2] at hm
      exact le_of_mul_le_mul_left hm (div_pos hb0 hlog2)
    have hFeq : ∀ θ : SysPartition N S, ur_F w θ tc σ / (sysCutCount θ : ℝ) =
        A / σ * (P θ / A / (sysCutCount θ : ℝ)) := by
      intro θ
      unfold ur_F
      field_simp
      rfl
    have herr : A / σ * (2 * R) = ur_err S.card A η σ := by
      unfold ur_err; rw [hR]; field_simp; ring
    refine ⟨tc, hc, te, he, θh, hθh, hθX, fun t' => ur_near_argmax s hz hη hηA' hσ hlevS hc t',
      ?_, ?_⟩
    · intro θ
      have key := ur_min_arith hR0 (hcc1 θh) (hcc1 θ) (hnear θh) (hnear θ) (hGcmp θ)
      have := mul_le_mul_of_nonneg_left key (div_pos hA hσ).le
      rw [mul_add, herr, ← hFeq, ← hFeq] at this
      exact this
    · have hGup : ur_G w θh tc ≤ P θh / A + R := by linarith [(abs_le.1 (hnear θh)).2]
      have hval : σ / (A * Real.log 2) * (ur_F w θh tc σ + ur_err S.card A η σ) =
          (P θh / A + 2 * R) / Real.log 2 := by
        unfold ur_F ur_err; rw [hR]; field_simp; ring
      have hle1 : ur_G w θh tc / Real.log 2 ≤ (P θh / A + 2 * R) / Real.log 2 :=
        div_le_div_of_nonneg_right (by linarith) hlog2.le
      rw [hposh] at hθX'
      calc X < b * (ur_G w θh tc / Real.log 2) := hθX'
        _ ≤ ρ * ((P θh / A + 2 * R) / Real.log 2) := mul_le_mul hbU hle1
            (div_pos hGh hlog2).le
            (div_nonneg (pow_nonneg (div_nonneg (by linarith) hAη.le) _) (by positivity))
        _ = _ := by rw [mul_assoc, hval]
  · right
    push Not at hcase
    obtain ⟨θ0, h0⟩ := hcase
    refine ⟨te, he, θ0, ?_, lt_of_lt_of_le h0 (hCle θ0)⟩
    have hm := hmip θ0
    unfold normalizedSysPhiAt at hm
    have hE0 := sysPhiE_nonneg (tpmOf z) S s θ0 s te
    have hch0 : (0 : ℝ) < sysCutCount θh := by linarith [hcc1 θh]
    have h1 : sysPhiAt (tpmOf z) S s θ0 s tc te / (sysCutCount θ0 : ℝ) ≤
        sysPhiE (tpmOf z) S s θ0 s te :=
      (div_le_self (sysPhiAt_nonneg _ _ _ _ _ _ _) (hcc1 θ0)).trans (min_le_right _ _)
    have h2 : sysPhiAt (tpmOf z) S s θh s tc te ≤
        sysPhiE (tpmOf z) S s θ0 s te * (sysCutCount θh : ℝ) := by
      rw [← div_le_iff₀ hch0]; exact hm.trans h1
    calc X < sysPhiAt (tpmOf z) S s θh s tc te := hθX
      _ ≤ sysPhiE (tpmOf z) S s θ0 s te * (sysCutCount θh : ℝ) := h2
      _ ≤ sysPhiE (tpmOf z) S s θ0 s te * (S.card : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (ur_cc_le θh) hE0
      _ = _ := by ring

/-! ## 5. Single-unit cuts, the no-tie condition and the all-cut profile -/

/-- The single-unit cut of unit `i` (unit `i` loses all of `S \ {i}`); an arbitrary single cut
if `i ∉ S`. -/
noncomputable def pkSingle {S : Finset (Fin N)} (hS2 : 2 ≤ S.card) (i : Fin N) :
    SysPartition N S :=
  if hi : i ∈ S then splitAt hi (hrest_of_card hS2 hi)
  else splitAt (card_pos.1 (by omega : 0 < S.card)).choose_spec
    (hrest_of_card hS2 (card_pos.1 (by omega : 0 < S.card)).choose_spec)

lemma pkSingle_profile {S : Finset (Fin N)} (hS2 : 2 ≤ S.card) {i : Fin N} (hi : i ∈ S) :
    ∀ j ∈ S, profile (pkSingle hS2 i) j = if j = i then S.erase i else ∅ := by
  intro j hj
  unfold pkSingle
  rw [dite_eq_left hi]
  exact lp_splitAt_profile hi _ j hj

lemma pkSingle_cc {S : Finset (Fin N)} (hS2 : 2 ≤ S.card) {i : Fin N} (hi : i ∈ S) :
    sysCutCount (pkSingle hS2 i) = S.card - 1 := by
  unfold pkSingle
  rw [dite_eq_left hi]
  exact sysCutCount_splitAt hi _

/-- **No exact tie of the single-unit cut values** at the state pair `(tc, te)`: two single-cut
values differ, or one of them is `0`.  (The complement is a null set, B2.) -/
def NoSingleTie (T : UnitTPM N) (S : Finset (Fin N)) (hS2 : 2 ≤ S.card) (s tc te : State N) :
    Prop :=
  ∃ i ∈ S, ∃ j ∈ S, sysPhiAt T S s (pkSingle hS2 i) s tc te ≠
      sysPhiAt T S s (pkSingle hS2 j) s tc te ∨
    sysPhiAt T S s (pkSingle hS2 i) s tc te = 0

/-- **The all-cut profile off the single-cut tie** (via `allCut_mip_tie'`): if the single-cut
values do not tie, every all-cut partition in the MIP set has value `0`. -/
theorem allCut_zero_of_noTie {z : Param N} (hz : z ∈ openCube N) (s : State N)
    {S : Finset (Fin N)} (hS2 : 2 ≤ S.card) {tc te : State N}
    (hnt : NoSingleTie (tpmOf z) S hS2 s tc te) {θ : SysPartition N S}
    (hθ : θ ∈ sysMipSetAt (tpmOf z) S s s tc te) (hA : ∀ j ∈ S, profile θ j = S.erase j) :
    sysPhiAt (tpmOf z) S s θ s tc te = 0 := by
  by_contra hne
  have hpos : 0 < sysPhiAt (tpmOf z) S s θ s tc te :=
    lt_of_le_of_ne (sysPhiAt_nonneg _ _ _ _ _ _ _) (Ne.symm hne)
  have htie := allCut_mip_tie' hz s θ hA (pkSingle hS2)
    (fun i hi j hj => pkSingle_profile hS2 hi j hj) tc te hθ hpos
  obtain ⟨i, hi, j, hj, h⟩ := hnt
  rcases h with h | h
  · exact h (htie i hi j hj).1
  · exact (htie i hi i hi).2.ne' h

/-! ## 6. Pairs: the exact formula (Fable's Lemma 11.2) and the upper bound at the tilt -/

lemma pk_flipP_open {s : State N} {w : Param N} (hw : w ∈ openCube N) :
    flipP s w ∈ openCube N := by
  intro r i
  have h := hw r i
  unfold flipP flipC
  cases s i
  · simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_Ioo]
    constructor <;> linarith [h.1, h.2]
  · simpa using h

section Pair

variable {a b : Fin N}

lemma pk_pair_card (hab : a ≠ b) : 2 ≤ ({a, b} : Finset (Fin N)).card := by
  rw [card_pair hab]

lemma pk_pair_erase_a (hab : a ≠ b) : ({a, b} : Finset (Fin N)).erase a = {b} := by
  ext x
  simp only [mem_erase, mem_insert, mem_singleton]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact absurd h2 h1
    · exact h2
  · rintro rfl
    exact ⟨fun h => hab h.symm, Or.inr rfl⟩

lemma pk_pair_erase_b (hab : a ≠ b) : ({a, b} : Finset (Fin N)).erase b = {a} := by
  ext x
  simp only [mem_erase, mem_insert, mem_singleton]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact h2
    · exact absurd h2 h1
  · rintro rfl
    exact ⟨hab, Or.inl rfl⟩

lemma pk_pair_single_a (hab : a ≠ b) :
    profile (pkSingle (pk_pair_card hab) a) a = {b} ∧
      profile (pkSingle (pk_pair_card hab) a) b = ∅ := by
  have ha : a ∈ ({a, b} : Finset (Fin N)) := mem_insert_self _ _
  have hb : b ∈ ({a, b} : Finset (Fin N)) := mem_insert_of_mem (mem_singleton_self _)
  have h := pkSingle_profile (pk_pair_card hab) ha
  refine ⟨?_, ?_⟩
  · rw [h a ha, ite_eq_left rfl, pk_pair_erase_a hab]
  · rw [h b hb, ite_eq_right (fun e => hab e.symm)]

lemma pk_pair_single_b (hab : a ≠ b) :
    profile (pkSingle (pk_pair_card hab) b) a = ∅ ∧
      profile (pkSingle (pk_pair_card hab) b) b = {a} := by
  have ha : a ∈ ({a, b} : Finset (Fin N)) := mem_insert_self _ _
  have hb : b ∈ ({a, b} : Finset (Fin N)) := mem_insert_of_mem (mem_singleton_self _)
  have h := pkSingle_profile (pk_pair_card hab) hb
  refine ⟨?_, ?_⟩
  · rw [h a ha, ite_eq_right hab]
  · rw [h b hb, ite_eq_left rfl, pk_pair_erase_b hab]

lemma pk_pair_cc (hab : a ≠ b) (θ : SysPartition N {a, b}) :
    sysCutCount θ = (profile θ a).card + (profile θ b).card := by
  rw [sysCutCount_eq_sum_profile, sum_pair hab]

/-- **The three cut structures of a pair**: `a` cut (profile of the single cut of `a`), `b` cut, or
both cut (the all-cut profile). -/
lemma pk_pair_classify (hab : a ≠ b) (θ : SysPartition N {a, b}) :
    (∀ j ∈ ({a, b} : Finset (Fin N)), profile θ j = profile (pkSingle (pk_pair_card hab) a) j) ∨
    (∀ j ∈ ({a, b} : Finset (Fin N)), profile θ j = profile (pkSingle (pk_pair_card hab) b) j) ∨
    (∀ j ∈ ({a, b} : Finset (Fin N)), profile θ j = ({a, b} : Finset (Fin N)).erase j) := by
  have hea : ({a, b} : Finset (Fin N)).erase a ⊆ {b} := (pk_pair_erase_a hab).le
  have heb : ({a, b} : Finset (Fin N)).erase b ⊆ {a} := (pk_pair_erase_b hab).le
  have hA := cut_cases_pair θ hea (mem_insert_self _ _)
  have hB := cut_cases_pair θ heb (mem_insert_of_mem (mem_singleton_self _))
  change profile θ a = ∅ ∨ profile θ a = {b} at hA
  change profile θ b = ∅ ∨ profile θ b = {a} at hB
  obtain ⟨sa1, sa2⟩ := pk_pair_single_a hab
  obtain ⟨sb1, sb2⟩ := pk_pair_single_b hab
  have hall : ∀ P : Fin N → Prop, P a → P b → ∀ j ∈ ({a, b} : Finset (Fin N)), P j := by
    intro P h1 h2 j hj
    rcases mem_insert.1 hj with rfl | hj
    · exact h1
    · rw [mem_singleton.1 hj]; exact h2
  rcases hA with ha | ha <;> rcases hB with hb | hb
  · exfalso
    have := sysCutCount_pos θ
    rw [pk_pair_cc hab, ha, hb] at this
    simp at this
  · exact Or.inr (Or.inl (hall _ (by rw [ha, sb1]) (by rw [hb, sb2])))
  · exact Or.inl (hall _ (by rw [ha, sa1]) (by rw [hb, sa2]))
  · exact Or.inr (Or.inr (hall _ (by rw [ha, pk_pair_erase_a hab])
      (by rw [hb, pk_pair_erase_b hab])))

/-- The value of the single cut of unit `i` of the pair at the state pair `(tc, te)`. -/
noncomputable def pairCutVal (z : Param N) (s : State N) (hab : a ≠ b) (i : Fin N)
    (tc te : State N) : ℝ :=
  sysPhiAt (tpmOf z) {a, b} s (pkSingle (pk_pair_card hab) i) s tc te

/-- **Superadditivity of the all-cut value** over the single cuts, when every single cut has a
positive value (exact additivity of the log-ratios, `allCut_logb_cause/effect`). -/
theorem pk_allCut_superadd {z : Param N} (hz : z ∈ openCube N) (s : State N)
    {S : Finset (Fin N)} (hS2 : 2 ≤ S.card) (tc te : State N) (θ : SysPartition N S)
    (hθ : ∀ j ∈ S, profile θ j = S.erase j)
    (hpos : ∀ i ∈ S, 0 < sysPhiAt (tpmOf z) S s (pkSingle hS2 i) s tc te) :
    ∑ i ∈ S, sysPhiAt (tpmOf z) S s (pkSingle hS2 i) s tc te ≤
      sysPhiAt (tpmOf z) S s θ s tc te := by
  have h1 : ∀ i ∈ S, ∀ j ∈ S, profile (pkSingle hS2 i) j = if j = i then S.erase i else ∅ :=
    fun i hi j hj => pkSingle_profile hS2 hi j hj
  have hLC := allCut_logb_cause hz s θ hθ (pkSingle hS2) h1 tc
  have hLE := allCut_logb_effect hz s θ hθ (pkSingle hS2) h1 te
  have hpc : ∀ i ∈ S, 0 < Real.logb 2 (sysCauseProb (tpmOf z) S s s tc /
      sysPartCauseProb (tpmOf z) S s (pkSingle hS2 i) s tc) := fun i hi =>
    lp_pos_of_mul (lt_min_iff.1 (hpos i hi)).1
  have hpe : ∀ i ∈ S, 0 < Real.logb 2 (sysEffProb (tpmOf z) S s s te /
      sysPartEffProb (tpmOf z) S s (pkSingle hS2 i) s te) := fun i hi =>
    lp_pos_of_mul (lt_min_iff.1 (hpos i hi)).2
  unfold sysPhiAt sysPhiC sysPhiE
  rw [hLC, hLE, lp_pos_eq (sum_nonneg fun i hi => (hpc i hi).le),
    lp_pos_eq (sum_nonneg fun i hi => (hpe i hi).le)]
  refine le_min ?_ ?_
  · rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    rw [lp_pos_eq (hpc i hi).le]
    exact min_le_left _ _
  · rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    rw [lp_pos_eq (hpe i hi).le]
    exact min_le_right _ _

lemma pk_pair_superadd {z : Param N} (hz : z ∈ openCube N) (s : State N) (hab : a ≠ b)
    (tc te : State N) (θ : SysPartition N {a, b})
    (hθ : ∀ j ∈ ({a, b} : Finset (Fin N)), profile θ j = ({a, b} : Finset (Fin N)).erase j)
    (ha : 0 < pairCutVal z s hab a tc te) (hb : 0 < pairCutVal z s hab b tc te) :
    pairCutVal z s hab a tc te + pairCutVal z s hab b tc te ≤
      sysPhiAt (tpmOf z) {a, b} s θ s tc te := by
  have h := pk_allCut_superadd hz s (pk_pair_card hab) tc te θ hθ fun i hi => by
    rcases mem_insert.1 hi with rfl | hi
    · exact ha
    · rw [mem_singleton.1 hi]; exact hb
  rw [sum_pair hab] at h
  exact h

/-- **The exact pair formula** (Fable's Lemma 11.2, (11.2)).  At every state pair `(tc, te)`,
with `φ_a`, `φ_b` the values of the two single cuts (each the minimum of its cause side
`back · (log₂ LR_a)⁺` and its effect side `e_S · (log₂ LR'_a)⁺`):
`min φ_a φ_b ≤ φ_s(tc, te) ≤ 2 min φ_a φ_b`, and `φ_s(tc, te) = min φ_a φ_b` off the exact tie
`φ_a = φ_b > 0` (`NoSingleTie`).  At the tie the both-cut partitions may join the MIP set and
report `φ_a + φ_b`. -/
theorem pair_phiOfState {z : Param N} (hz : z ∈ openCube N) (s : State N) (hab : a ≠ b)
    (tc te : State N) :
    min (pairCutVal z s hab a tc te) (pairCutVal z s hab b tc te) ≤
        sysPhiOfState (tpmOf z) {a, b} s s tc te ∧
      sysPhiOfState (tpmOf z) {a, b} s s tc te ≤
        2 * min (pairCutVal z s hab a tc te) (pairCutVal z s hab b tc te) ∧
      (NoSingleTie (tpmOf z) {a, b} (pk_pair_card hab) s tc te →
        sysPhiOfState (tpmOf z) {a, b} s s tc te =
          min (pairCutVal z s hab a tc te) (pairCutVal z s hab b tc te)) := by
  have h2 := pk_pair_card hab
  have ha : a ∈ ({a, b} : Finset (Fin N)) := mem_insert_self _ _
  have hb : b ∈ ({a, b} : Finset (Fin N)) := mem_insert_of_mem (mem_singleton_self _)
  have ccA : (sysCutCount (pkSingle h2 a) : ℝ) = 1 := by
    rw [pkSingle_cc h2 ha, card_pair hab]; norm_num
  have ccB : (sysCutCount (pkSingle h2 b) : ℝ) = 1 := by
    rw [pkSingle_cc h2 hb, card_pair hab]; norm_num
  have hφa0 : 0 ≤ pairCutVal z s hab a tc te := sysPhiAt_nonneg _ _ _ _ _ _ _
  have hφb0 : 0 ≤ pairCutVal z s hab b tc te := sysPhiAt_nonneg _ _ _ _ _ _ _
  have hcc1 : ∀ θ : SysPartition N {a, b}, (1 : ℝ) ≤ sysCutCount θ := fun θ => by
    exact_mod_cast sysCutCount_pos θ
  have hcc2 : ∀ θ : SysPartition N {a, b}, (sysCutCount θ : ℝ) ≤ 2 := fun θ => by
    have h := sysCutCount_le' θ
    rw [card_pair hab] at h
    exact_mod_cast h
  have hvalA : ∀ θ : SysPartition N {a, b},
      (∀ j ∈ ({a, b} : Finset (Fin N)), profile θ j = profile (pkSingle h2 a) j) →
      sysPhiAt (tpmOf z) {a, b} s θ s tc te = pairCutVal z s hab a tc te ∧
        (sysCutCount θ : ℝ) = 1 := fun θ hθ =>
    ⟨prof_sysPhiAt_congr (tpmOf z) s hθ s tc te, by rw [prof_sysCutCount_congr hθ, ccA]⟩
  have hvalB : ∀ θ : SysPartition N {a, b},
      (∀ j ∈ ({a, b} : Finset (Fin N)), profile θ j = profile (pkSingle h2 b) j) →
      sysPhiAt (tpmOf z) {a, b} s θ s tc te = pairCutVal z s hab b tc te ∧
        (sysCutCount θ : ℝ) = 1 := fun θ hθ =>
    ⟨prof_sysPhiAt_congr (tpmOf z) s hθ s tc te, by rw [prof_sysCutCount_congr hθ, ccB]⟩
  have hvalAll : ∀ θ : SysPartition N {a, b},
      (∀ j ∈ ({a, b} : Finset (Fin N)), profile θ j = ({a, b} : Finset (Fin N)).erase j) →
      (sysCutCount θ : ℝ) = 2 := fun θ hθ => by
    rw [pk_pair_cc hab, hθ a ha, hθ b hb, pk_pair_erase_a hab, pk_pair_erase_b hab,
      card_singleton]
    norm_num
  set φa := pairCutVal z s hab a tc te with hφa
  set φb := pairCutVal z s hab b tc te with hφb
  -- every partition has value `≥ min φa φb`
  have hge : ∀ θ : SysPartition N {a, b}, min φa φb ≤ sysPhiAt (tpmOf z) {a, b} s θ s tc te := by
    intro θ
    rcases le_or_gt (min φa φb) 0 with hm | hm
    · exact hm.trans (sysPhiAt_nonneg _ _ _ _ _ _ _)
    · have hpa : 0 < φa := lt_of_lt_of_le hm (min_le_left _ _)
      have hpb : 0 < φb := lt_of_lt_of_le hm (min_le_right _ _)
      rcases pk_pair_classify hab θ with h | h | h
      · rw [(hvalA θ h).1]; exact min_le_left _ _
      · rw [(hvalB θ h).1]; exact min_le_right _ _
      · have := pk_pair_superadd hz s hab tc te θ h hpa hpb
        linarith [min_le_left φa φb]
  -- every MIP partition has value `≤ 2 min φa φb`
  have hle : ∀ θ ∈ sysMipSetAt (tpmOf z) {a, b} s s tc te,
      sysPhiAt (tpmOf z) {a, b} s θ s tc te ≤ 2 * min φa φb := by
    intro θ hθ
    have hm := mem_argminSet.1 hθ
    have hmA := hm (pkSingle h2 a)
    have hmB := hm (pkSingle h2 b)
    unfold normalizedSysPhiAt at hmA hmB
    rw [ccA, div_one] at hmA
    rw [ccB, div_one] at hmB
    have hc0 : (0 : ℝ) < sysCutCount θ := lt_of_lt_of_le one_pos (hcc1 θ)
    rw [div_le_iff₀ hc0] at hmA hmB
    change sysPhiAt (tpmOf z) {a, b} s θ s tc te ≤ φa * (sysCutCount θ : ℝ) at hmA
    change sysPhiAt (tpmOf z) {a, b} s θ s tc te ≤ φb * (sysCutCount θ : ℝ) at hmB
    have hmin0 : 0 ≤ min φa φb := le_min hφa0 hφb0
    have h3 := mul_le_mul_of_nonneg_left (hcc2 θ) hmin0
    rcases min_choice φa φb with h | h <;> rw [h] at h3 ⊢ <;> nlinarith
  have hne : (sysMipSetAt (tpmOf z) {a, b} s s tc te).Nonempty := by
    have : Nonempty (SysPartition N {a, b}) := ⟨pkSingle h2 a⟩
    exact argminSet_nonempty _
  have h2m : 0 ≤ 2 * min φa φb := by have := le_min hφa0 hφb0; linarith
  have hlow : min φa φb ≤ sysPhiOfState (tpmOf z) {a, b} s s tc te := by
    obtain ⟨θ, hθ⟩ := hne
    unfold sysPhiOfState
    exact (hge θ).trans
      (le_sup'OrZero (f := fun θ => sysPhiAt (tpmOf z) {a, b} s θ s tc te) hθ)
  have hup : sysPhiOfState (tpmOf z) {a, b} s s tc te ≤ 2 * min φa φb := by
    unfold sysPhiOfState
    exact sup'OrZero_le h2m hle
  refine ⟨hlow, hup, fun hnt => ?_⟩
  -- off the tie
  have hcase : φa ≠ φb ∨ min φa φb = 0 := by
    obtain ⟨i, hi, j, hj, h⟩ := hnt
    have hi' : i = a ∨ i = b := by
      rcases mem_insert.1 hi with h | h
      · exact Or.inl h
      · exact Or.inr (mem_singleton.1 h)
    have hj' : j = a ∨ j = b := by
      rcases mem_insert.1 hj with h | h
      · exact Or.inl h
      · exact Or.inr (mem_singleton.1 h)
    rcases h with h | h
    · rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
      · exact absurd rfl h
      · exact Or.inl h
      · exact Or.inl (Ne.symm h)
      · exact absurd rfl h
    · right
      rcases hi' with rfl | rfl
      · exact le_antisymm ((min_le_left _ _).trans (le_of_eq h)) (le_min hφa0 hφb0)
      · exact le_antisymm ((min_le_right _ _).trans (le_of_eq h)) (le_min hφa0 hφb0)
  have hzero : min φa φb = 0 → sysPhiOfState (tpmOf z) {a, b} s s tc te = min φa φb := by
    intro hm0
    rw [hm0] at hlow hup ⊢
    linarith
  rcases hcase with hneq | h0
  · rcases le_or_gt (min φa φb) 0 with hm | hm
    · exact hzero (le_antisymm hm (le_min hφa0 hφb0))
    · have hpa : 0 < φa := lt_of_lt_of_le hm (min_le_left _ _)
      have hpb : 0 < φb := lt_of_lt_of_le hm (min_le_right _ _)
      have hall : ∀ θ : SysPartition N {a, b},
          (∀ j ∈ ({a, b} : Finset (Fin N)), profile θ j = ({a, b} : Finset (Fin N)).erase j) →
          min φa φb < sysPhiAt (tpmOf z) {a, b} s θ s tc te / (sysCutCount θ : ℝ) := by
        intro θ hθ
        rw [hvalAll θ hθ]
        have := pk_pair_superadd hz s hab tc te θ hθ hpa hpb
        rcases lt_or_gt_of_ne hneq with hlt | hlt
        · rw [min_eq_left hlt.le]; linarith
        · rw [min_eq_right hlt.le]; linarith
      rcases lt_or_gt_of_ne hneq with hlt | hlt
      · have hst := sysPhiOfState_eq_of_strict (tpmOf z) {a, b} s (pkSingle h2 a) s tc te
          fun θ hθ => by
            change φa / (sysCutCount (pkSingle h2 a) : ℝ) < _
            rw [ccA, div_one]
            rcases pk_pair_classify hab θ with h | h | h
            · obtain ⟨j, hj, hjne⟩ := hθ
              exact absurd (h j hj) hjne
            · rw [(hvalB θ h).1, (hvalB θ h).2, div_one]; exact hlt
            · have := hall θ h
              rwa [min_eq_left hlt.le] at this
        rw [hst, min_eq_left hlt.le]
        rfl
      · have hst := sysPhiOfState_eq_of_strict (tpmOf z) {a, b} s (pkSingle h2 b) s tc te
          fun θ hθ => by
            change φb / (sysCutCount (pkSingle h2 b) : ℝ) < _
            rw [ccB, div_one]
            rcases pk_pair_classify hab θ with h | h | h
            · rw [(hvalA θ h).1, (hvalA θ h).2, div_one]; exact hlt
            · obtain ⟨j, hj, hjne⟩ := hθ
              exact absurd (h j hj) hjne
            · have := hall θ h
              rwa [min_eq_right hlt.le] at this
        rw [hst, min_eq_right hlt.le]
        rfl
  · exact hzero h0

/-- The cause side of the single cut of `i` in the numerators:
`φ_c(θ_i, tc) = back(tc) · (log₂ (Num_i(S, tc) / Num_i({i}, tc)))⁺` (any `S`, `i ∈ S`). -/
lemma pair_sysPhiC_single' {z : Param N} (hz : z ∈ openCube N) (s : State N) {S : Finset (Fin N)}
    (hS2 : 2 ≤ S.card) {i : Fin N} (hi : i ∈ S) (tc : State N) :
    sysPhiC (tpmOf z) S s (pkSingle hS2 i) s tc =
      sysBackCause (tpmOf z) S s s tc *
        pos (Real.logb 2 (Num (flipP s z) S S tc i / Num (flipP s z) S {i} tc i)) := by
  unfold sysPhiC pkSingle
  rw [dite_eq_left hi, cause_ratio_splitAt hz s tc hi]

/-- The conditioned numerator of the single cut of `i` in the pair `S = {i, j}` is the mean over
the flip of `j`. -/
lemma pair_Num_single' (w : Param N) {S : Finset (Fin N)} {i j : Fin N} (hij : i ≠ j)
    (hS : S = {i, j}) (t : State N) :
    Num w S {i} t i = (Num w S S t i + Num w S S (flip t j) i) / 2 := by
  subst hS
  rw [Num_eq_avg w {i, j} {i} t i]
  have hset : ({i} : Finset (Fin N)) ∪ ({i, j} : Finset (Fin N))ᶜ = ({j} : Finset (Fin N))ᶜ := by
    ext x
    simp only [mem_union, mem_singleton, mem_compl, mem_insert]
    constructor
    · rintro (rfl | h)
      · exact hij
      · exact fun hx => h (Or.inr hx)
    · intro hx
      by_cases hxa : x = i
      · exact Or.inl hxa
      · exact Or.inr (fun h => h.elim hxa hx)
  rw [hset, agree_compl_single, sum_pair (flip_ne t j), card_pair hij, card_singleton]
  norm_num

/-- **Pair, cause side of a single cut at the level `A`, upper form** (unit `i` of `S = {i, j}`).
With every full numerator within `η` of `A`, at every state `tc`:
`φ_c(θ_i, tc) ≤ (ρ²/4) · max(D_i, 0) / (2 (A - η) ln 2)`, `D_i = Num_i(tc) - Num_i(tc^j)`. -/
theorem pair_cause_le' {z : Param N} (hz : z ∈ openCube N) (s : State N) {S : Finset (Fin N)}
    (hS2 : 2 ≤ S.card) {i j : Fin N} (hij : i ≠ j) (hS : S = {i, j})
    {A η : ℝ} (hη : 0 ≤ η) (hηA : η < A)
    (hlev : ∀ t, ∀ k ∈ S, |Num (flipP s z) S S t k - A| ≤ η) (tc : State N) :
    sysPhiC (tpmOf z) S s (pkSingle hS2 i) s tc ≤
      ur_rho 2 A η / 4 * (max (Num (flipP s z) S S tc i -
        Num (flipP s z) S S (flip tc j) i) 0 / (2 * (A - η) * Real.log 2)) := by
  set w := flipP s z
  have hi : i ∈ S := by rw [hS]; exact mem_insert_self _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hAη : 0 < A - η := by linarith
  rw [pair_sysPhiC_single' hz s hS2 hi tc]
  have hback := ur_back_le s hz hη hηA hlev tc
  rw [hS, card_pair hij] at hback
  rw [← hS] at hback
  norm_num at hback
  set X := Num w S S tc i
  set X' := Num w S S (flip tc j) i
  have hX := abs_le.1 (hlev tc i hi)
  have hX' := abs_le.1 (hlev (flip tc j) i hi)
  have hY : Num w S {i} tc i = (X + X') / 2 := pair_Num_single' w hij hS tc
  have hYpos : A - η ≤ (X + X') / 2 := by linarith
  have hYp : 0 < (X + X') / 2 := lt_of_lt_of_le hAη hYpos
  have hXp : 0 < X := by linarith
  have hlogle := pos_logb_div_le_pos hXp hYp
  rw [← hY] at hlogle
  have hr0 : 0 ≤ ur_rho 2 A η := pow_nonneg (div_nonneg (by linarith) hAη.le) _
  have hstep : max (X - (X + X') / 2) 0 / ((X + X') / 2 * Real.log 2) ≤
      max (X - X') 0 / (2 * (A - η) * Real.log 2) := by
    have e1 : max (X - (X + X') / 2) 0 = max (X - X') 0 / 2 := by
      rw [show X - (X + X') / 2 = (X - X') / 2 by ring]
      rcases le_total (X - X') 0 with h | h
      · rw [max_eq_right (by linarith), max_eq_right h]; ring
      · rw [max_eq_left (by linarith), max_eq_left h]
    rw [e1, div_div]
    apply div_le_div_of_nonneg_left (le_max_right _ _) (by positivity)
    nlinarith
  calc sysBackCause (tpmOf z) S s s tc * pos (Real.logb 2 (X / Num w S {i} tc i))
      ≤ ur_rho 2 A η / 4 * (max (X - (X + X') / 2) 0 / ((X + X') / 2 * Real.log 2)) := by
        rw [hY] at hlogle ⊢
        exact mul_le_mul hback hlogle (pos_nonneg _) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hstep (by positivity)

/-- **Pair, cause side of a single cut at the level `A`, lower form** (unit `i` of `S = {i, j}`):
at a maximal cause state, `(1/4) D_i / (2 (A + η) ln 2) ≤ φ_c(θ_i, tc)` when `D_i ≥ 0`. -/
theorem pair_cause_ge' {z : Param N} (hz : z ∈ openCube N) (s : State N) {S : Finset (Fin N)}
    (hS2 : 2 ≤ S.card) {i j : Fin N} (hij : i ≠ j) (hS : S = {i, j})
    {A η : ℝ} (hηA : η < A)
    (hlev : ∀ t, ∀ k ∈ S, |Num (flipP s z) S S t k - A| ≤ η)
    {tc : State N} (htc : tc ∈ sysMaxCauseStates (tpmOf z) S s s)
    (hD : Num (flipP s z) S S (flip tc j) i ≤ Num (flipP s z) S S tc i) :
    1 / 4 * ((Num (flipP s z) S S tc i - Num (flipP s z) S S (flip tc j) i)
      / (2 * (A + η) * Real.log 2)) ≤ sysPhiC (tpmOf z) S s (pkSingle hS2 i) s tc := by
  set w := flipP s z
  have hi : i ∈ S := by rw [hS]; exact mem_insert_self _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [pair_sysPhiC_single' hz s hS2 hi tc]
  have hback : 1 / 4 ≤ sysBackCause (tpmOf z) S s s tc := by
    subst hS
    exact sysBackCause_pair_ge hz s tc hij htc
  set X := Num w S S tc i
  set X' := Num w S S (flip tc j) i
  have hX := abs_le.1 (hlev tc i hi)
  have hX' := abs_le.1 (hlev (flip tc j) i hi)
  have hY : Num w S {i} tc i = (X + X') / 2 := pair_Num_single' w hij hS tc
  have hXp : 0 < X := Num_pos hz s _ _ tc i
  have hX'p : 0 < X' := Num_pos hz s _ _ (flip tc j) i
  have hYp : 0 < (X + X') / 2 := by linarith
  have hlog : (X - X') / (2 * X) ≤ Real.log (X / ((X + X') / 2)) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hYp hXp)
    rw [Real.log_div hYp.ne' hXp.ne'] at h
    rw [Real.log_div hXp.ne' hYp.ne']
    have : (X + X') / 2 / X - 1 = -((X - X') / (2 * X)) := by field_simp; ring
    linarith
  have hD0 : 0 ≤ X - X' := by linarith
  have hApos : 0 < A + η := by linarith
  have hstep : (X - X') / (2 * (A + η) * Real.log 2) ≤
      pos (Real.logb 2 (X / Num w S {i} tc i)) := by
    refine le_trans ?_ (le_max_right _ _)
    rw [hY, Real.logb]
    rw [div_le_div_iff₀ (by positivity) hlog2]
    have h1 : (X - X') / (2 * (A + η)) ≤ (X - X') / (2 * X) :=
      div_le_div_of_nonneg_left hD0 (by linarith) (by linarith)
    have h3 : X - X' ≤ Real.log (X / ((X + X') / 2)) * (2 * (A + η)) := by
      have := h1.trans hlog
      rwa [div_le_iff₀ (by positivity)] at this
    calc (X - X') * Real.log 2 ≤ Real.log (X / ((X + X') / 2)) * (2 * (A + η)) * Real.log 2 :=
          mul_le_mul_of_nonneg_right h3 hlog2.le
      _ = _ := by ring
  calc 1 / 4 * ((X - X') / (2 * (A + η) * Real.log 2))
      ≤ sysBackCause (tpmOf z) S s s tc * pos (Real.logb 2 (X / Num w S {i} tc i)) :=
        mul_le_mul hback hstep (div_nonneg hD0 (by positivity)) (sysBackCause_nonneg _ _ _ _ _)
    _ = _ := rfl

/-- `pair_cause_le'` for the unit `a` of `{a, b}`. -/
theorem pair_cause_le {z : Param N} (hz : z ∈ openCube N) (s : State N) (hab : a ≠ b)
    {A η : ℝ} (hη : 0 ≤ η) (hηA : η < A)
    (hlev : ∀ t, ∀ i ∈ ({a, b} : Finset (Fin N)),
      |Num (flipP s z) {a, b} {a, b} t i - A| ≤ η) (tc : State N) :
    sysPhiC (tpmOf z) {a, b} s (pkSingle (pk_pair_card hab) a) s tc ≤
      ur_rho 2 A η / 4 * (max (Num (flipP s z) {a, b} {a, b} tc a -
        Num (flipP s z) {a, b} {a, b} (flip tc b) a) 0 / (2 * (A - η) * Real.log 2)) :=
  pair_cause_le' hz s (pk_pair_card hab) hab rfl hη hηA hlev tc

/-- `pair_cause_le'` for the unit `b` of `{a, b}`. -/
theorem pair_cause_le_b {z : Param N} (hz : z ∈ openCube N) (s : State N) (hab : a ≠ b)
    {A η : ℝ} (hη : 0 ≤ η) (hηA : η < A)
    (hlev : ∀ t, ∀ i ∈ ({a, b} : Finset (Fin N)),
      |Num (flipP s z) {a, b} {a, b} t i - A| ≤ η) (tc : State N) :
    sysPhiC (tpmOf z) {a, b} s (pkSingle (pk_pair_card hab) b) s tc ≤
      ur_rho 2 A η / 4 * (max (Num (flipP s z) {a, b} {a, b} tc b -
        Num (flipP s z) {a, b} {a, b} (flip tc a) b) 0 / (2 * (A - η) * Real.log 2)) :=
  pair_cause_le' hz s (pk_pair_card hab) hab.symm (pair_comm a b) hη hηA hlev tc

/-- `pair_cause_ge'` for the unit `a` of `{a, b}`. -/
theorem pair_cause_ge {z : Param N} (hz : z ∈ openCube N) (s : State N) (hab : a ≠ b)
    {A η : ℝ} (hηA : η < A)
    (hlev : ∀ t, ∀ i ∈ ({a, b} : Finset (Fin N)),
      |Num (flipP s z) {a, b} {a, b} t i - A| ≤ η)
    {tc : State N} (htc : tc ∈ sysMaxCauseStates (tpmOf z) {a, b} s s)
    (hD : Num (flipP s z) {a, b} {a, b} (flip tc b) a ≤ Num (flipP s z) {a, b} {a, b} tc a) :
    1 / 4 * ((Num (flipP s z) {a, b} {a, b} tc a - Num (flipP s z) {a, b} {a, b} (flip tc b) a)
      / (2 * (A + η) * Real.log 2)) ≤
      sysPhiC (tpmOf z) {a, b} s (pkSingle (pk_pair_card hab) a) s tc :=
  pair_cause_ge' hz s (pk_pair_card hab) hab rfl hηA hlev htc hD

/-- `pair_cause_ge'` for the unit `b` of `{a, b}`. -/
theorem pair_cause_ge_b {z : Param N} (hz : z ∈ openCube N) (s : State N) (hab : a ≠ b)
    {A η : ℝ} (hηA : η < A)
    (hlev : ∀ t, ∀ i ∈ ({a, b} : Finset (Fin N)),
      |Num (flipP s z) {a, b} {a, b} t i - A| ≤ η)
    {tc : State N} (htc : tc ∈ sysMaxCauseStates (tpmOf z) {a, b} s s)
    (hD : Num (flipP s z) {a, b} {a, b} (flip tc a) b ≤ Num (flipP s z) {a, b} {a, b} tc b) :
    1 / 4 * ((Num (flipP s z) {a, b} {a, b} tc b - Num (flipP s z) {a, b} {a, b} (flip tc a) b)
      / (2 * (A + η) * Real.log 2)) ≤
      sysPhiC (tpmOf z) {a, b} s (pkSingle (pk_pair_card hab) b) s tc :=
  pair_cause_ge' hz s (pk_pair_card hab) hab.symm (pair_comm a b) hηA hlev htc hD

lemma pk_sup'OrZero_congr_on {α : Type*} {s : Finset α} {f g : α → ℝ}
    (h : ∀ x ∈ s, f x = g x) : sup'OrZero s f = sup'OrZero s g := by
  unfold sup'OrZero
  split
  · rename_i hne
    exact Finset.sup'_congr hne rfl h
  · rfl

/-- **The pair formula at the system level** (Lemma 11.2 with the tie rule over maximal states):
off the single-cut ties, `φ_s({a, b})` is the largest, over the maximal state pairs, of
`min(φ_a, φ_b)`. -/
theorem pair_phi_eq {z : Param N} (hz : z ∈ openCube N) (s : State N) (hab : a ≠ b)
    (hnt : ∀ tc ∈ sysMaxCauseStates (tpmOf z) {a, b} s s,
      ∀ te ∈ sysMaxEffStates (tpmOf z) {a, b} s s,
        NoSingleTie (tpmOf z) {a, b} (pk_pair_card hab) s tc te) :
    phi z s {a, b} = sup'OrZero (sysMaxCauseStates (tpmOf z) {a, b} s s ×ˢ
      sysMaxEffStates (tpmOf z) {a, b} s s)
        (fun p => min (pairCutVal z s hab a p.1 p.2) (pairCutVal z s hab b p.1 p.2)) := by
  have heq : ∀ p ∈ sysMaxCauseStates (tpmOf z) {a, b} s s ×ˢ
      sysMaxEffStates (tpmOf z) {a, b} s s, sysPhiOfState (tpmOf z) {a, b} s s p.1 p.2 =
        min (pairCutVal z s hab a p.1 p.2) (pairCutVal z s hab b p.1 p.2) := by
    intro p hp
    obtain ⟨h1, h2⟩ := mem_product.1 hp
    exact (pair_phiOfState hz s hab p.1 p.2).2.2 (hnt p.1 h1 p.2 h2)
  unfold phi sysPhi
  exact pk_sup'OrZero_congr_on heq

/-- **Pairs, lower bound (deterministic core).** If at every maximal cause state both flips lose
at least `Δ ≥ 0` (`Num_a(tc^b) + Δ ≤ Num_a(tc)`, `Num_b(tc^a) + Δ ≤ Num_b(tc)`) and some maximal
effect state has every effect side `≥ E0`, then `φ_s({a, b}) ≥ min(Δ/(8 (A + η) ln 2), E0)`. -/
theorem pair_lower_core {z : Param N} (hz : z ∈ openCube N) (s : State N) (hab : a ≠ b)
    {A η Δ E0 : ℝ} (hηA : η < A) (hΔ : 0 ≤ Δ)
    (hlev : ∀ t, ∀ i ∈ ({a, b} : Finset (Fin N)),
      |Num (flipP s z) {a, b} {a, b} t i - A| ≤ η)
    (hD : ∀ tc ∈ sysMaxCauseStates (tpmOf z) {a, b} s s,
      Num (flipP s z) {a, b} {a, b} (flip tc b) a + Δ ≤ Num (flipP s z) {a, b} {a, b} tc a ∧
      Num (flipP s z) {a, b} {a, b} (flip tc a) b + Δ ≤ Num (flipP s z) {a, b} {a, b} tc b)
    (heff : ∃ te ∈ sysMaxEffStates (tpmOf z) {a, b} s s,
      ∀ θ : SysPartition N {a, b}, E0 ≤ sysPhiE (tpmOf z) {a, b} s θ s te) :
    min (Δ / (8 * (A + η) * Real.log 2)) E0 ≤ phi z s {a, b} := by
  obtain ⟨te, hte, hE⟩ := heff
  obtain ⟨tc, htc⟩ := sysMaxCauseStates_nonempty (tpmOf z) {a, b} s s
  have ha : a ∈ ({a, b} : Finset (Fin N)) := mem_insert_self _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hApos : 0 < A + η := by
    have h := abs_le.1 (hlev tc a ha)
    have := Num_pos hz s {a, b} {a, b} tc a
    linarith
  have hden : 0 < 8 * (A + η) * Real.log 2 := by positivity
  obtain ⟨hDa, hDb⟩ := hD tc htc
  have hcut : ∀ X X' : ℝ, X' + Δ ≤ X →
      Δ / (8 * (A + η) * Real.log 2) ≤ 1 / 4 * ((X - X') / (2 * (A + η) * Real.log 2)) := by
    intro X X' h
    rw [show 1 / 4 * ((X - X') / (2 * (A + η) * Real.log 2)) =
      (X - X') / (8 * (A + η) * Real.log 2) by field_simp; ring]
    exact div_le_div_of_nonneg_right (by linarith) hden.le
  have hφa : min (Δ / (8 * (A + η) * Real.log 2)) E0 ≤ pairCutVal z s hab a tc te := by
    unfold pairCutVal sysPhiAt
    refine le_min ((min_le_left _ _).trans ((hcut _ _ hDa).trans ?_)) ((min_le_right _ _).trans (hE _))
    exact pair_cause_ge hz s hab hηA hlev htc (by linarith)
  have hφb : min (Δ / (8 * (A + η) * Real.log 2)) E0 ≤ pairCutVal z s hab b tc te := by
    unfold pairCutVal sysPhiAt
    refine le_min ((min_le_left _ _).trans ((hcut _ _ hDb).trans ?_)) ((min_le_right _ _).trans (hE _))
    exact pair_cause_ge_b hz s hab hηA hlev htc (by linarith)
  calc min (Δ / (8 * (A + η) * Real.log 2)) E0
      ≤ min (pairCutVal z s hab a tc te) (pairCutVal z s hab b tc te) := le_min hφa hφb
    _ ≤ sysPhiOfState (tpmOf z) {a, b} s s tc te := (pair_phiOfState hz s hab tc te).1
    _ ≤ phi z s {a, b} := sysPhiOfState_le_sysPhi _ _ _ _ htc hte

lemma pk_merge_eq {S : Finset (Fin N)} {r0 tc : State N} (hag : ∀ j ∈ S, tc j = r0 j) :
    merge S tc r0 = r0 := by
  funext j
  by_cases hj : j ∈ S
  · rw [merge_mem hj]; exact hag j hj
  · rw [merge_not_mem hj]

lemma pk_merge_flip {S : Finset (Fin N)} {r0 tc : State N} (hag : ∀ j ∈ S, tc j = r0 j)
    {k : Fin N} (hk : k ∈ S) : merge S (flip tc k) r0 = flip r0 k := by
  funext j
  by_cases hj : j ∈ S
  · rw [merge_mem hj]
    by_cases hjk : j = k
    · subst hjk; simp only [flip, Function.update_self]; rw [hag j hj]
    · simp only [flip, Function.update_of_ne hjk]; exact hag j hj
  · rw [merge_not_mem hj]
    have hjk : j ≠ k := fun h => hj (h ▸ hk)
    simp only [flip, Function.update_of_ne hjk]

/-- **Pairs at the tilt, lower bound** (`A = a_2 Z`, heavy row `tc = tcRow w`): if the maximal
cause states of `{a, b}` agree with `tc` on `{a, b}`, the heavy-row decomposition holds with
fluctuation `φ`, and `Δ ≤ P(tc) (y_{tc,a} - y_{tc^b,a}) - 2φ`, `Δ ≤ P(tc) (y_{tc,b} - y_{tc^a,b}) - 2φ`,
then `φ_s({a, b}) ≥ min(Δ/(8 (a_2 Z + η) ln 2), E0)` (Fable's `0.3607 min(D_a, D_b)`). -/
theorem pair_lower_tilt {w : Param N} (hw : w ∈ openCube N) (s : State N) (hab : a ≠ b)
    {η φ Δ E0 : ℝ} (B : Fin N → ℝ) (hηA : η < lvK 2 * Zs w) (hΔ : 0 ≤ Δ)
    (hlev : ∀ t, ∀ i ∈ ({a, b} : Finset (Fin N)), |Num w {a, b} {a, b} t i - lvK 2 * Zs w| ≤ η)
    (hdec : ∀ t, ∀ i ∈ ({a, b} : Finset (Fin N)), |Num w {a, b} {a, b} t i -
      (Pw w (tcRow w) * clamp01 (w (merge {a, b} t (tcRow w)) i) + B i)| ≤ φ)
    (hagree : ∀ tc ∈ sysMaxCauseStates (tpmOf (flipP s w)) {a, b} s s,
      ∀ j ∈ ({a, b} : Finset (Fin N)), tc j = tcRow w j)
    (hΔa : Δ ≤ Pw w (tcRow w) * (clamp01 (w (tcRow w) a) - clamp01 (w (flip (tcRow w) b) a))
      - 2 * φ)
    (hΔb : Δ ≤ Pw w (tcRow w) * (clamp01 (w (tcRow w) b) - clamp01 (w (flip (tcRow w) a) b))
      - 2 * φ)
    (heff : ∃ te ∈ sysMaxEffStates (tpmOf (flipP s w)) {a, b} s s,
      ∀ θ : SysPartition N {a, b}, E0 ≤ sysPhiE (tpmOf (flipP s w)) {a, b} s θ s te) :
    min (Δ / (8 * (lvK 2 * Zs w + η) * Real.log 2)) E0 ≤ phi (flipP s w) s {a, b} := by
  have hz := pk_flipP_open (s := s) hw
  have hinv : flipP s (flipP s w) = w := flipP_invol s w
  have ha : a ∈ ({a, b} : Finset (Fin N)) := mem_insert_self _ _
  have hb : b ∈ ({a, b} : Finset (Fin N)) := mem_insert_of_mem (mem_singleton_self _)
  have hm : ∀ tc ∈ sysMaxCauseStates (tpmOf (flipP s w)) {a, b} s s,
      merge {a, b} tc (tcRow w) = tcRow w ∧
      merge {a, b} (flip tc b) (tcRow w) = flip (tcRow w) b ∧
      merge {a, b} (flip tc a) (tcRow w) = flip (tcRow w) a := fun tc htc =>
    ⟨pk_merge_eq (hagree tc htc), pk_merge_flip (hagree tc htc) hb,
      pk_merge_flip (hagree tc htc) ha⟩
  refine pair_lower_core hz s hab hηA hΔ (by rw [hinv]; exact hlev) (fun tc htc => ?_) heff
  obtain ⟨m0, m1, m2⟩ := hm tc htc
  rw [hinv]
  have h1 := abs_le.1 (hdec tc a ha)
  have h2 := abs_le.1 (hdec (flip tc b) a ha)
  have h3 := abs_le.1 (hdec tc b hb)
  have h4 := abs_le.1 (hdec (flip tc a) b hb)
  rw [m0] at h1 h3
  rw [m1] at h2
  rw [m2] at h4
  constructor <;> nlinarith

end Pair

/-! ## 7. The heavy row, the bulk, and the level band -/

/-- The bulk part of a full numerator: all rows except the heavy row `r0`. -/
noncomputable def pkRest (w : Param N) (S : Finset (Fin N)) (r0 t : State N) (i : Fin N) : ℝ :=
  ∑ v ∈ univ.erase r0, clamp01 (w (merge S t v) i) * Pw w v

/-- **Heavy-row split** (exact): `Num_i(S, t) = Pw(r0) · y_{(t, r0|_{Sᶜ}), i} + R_i(t)`. -/
lemma Num_eq_heavy_rest (w : Param N) (S : Finset (Fin N)) (r0 t : State N) (i : Fin N) :
    Num w S S t i = Pw w r0 * clamp01 (w (merge S t r0) i) + pkRest w S r0 t i := by
  rw [prof_Num_full, ← add_sum_erase _ _ (mem_univ r0), pkRest]
  ring

/-- The decomposition hypothesis of the upper bounds from a bound `φ` on the bulk fluctuation:
`|R_i(t) - B_i| ≤ φ` for every pattern `t`. -/
lemma pk_hdec_of_rest {w : Param N} {S : Finset (Fin N)} {r0 : State N} {B : Fin N → ℝ} {φ : ℝ}
    (h : ∀ t, ∀ i ∈ S, |pkRest w S r0 t i - B i| ≤ φ) :
    ∀ t, ∀ i ∈ S, |Num w S S t i - (Pw w r0 * clamp01 (w (merge S t r0) i) + B i)| ≤ φ := by
  intro t i hi
  rw [Num_eq_heavy_rest w S r0 t i]
  have := h t i hi
  rwa [show Pw w r0 * clamp01 (w (merge S t r0) i) + pkRest w S r0 t i -
    (Pw w r0 * clamp01 (w (merge S t r0) i) + B i) = pkRest w S r0 t i - B i by ring]

/-- **The level band of every conditioned numerator from the full ones** (averaging identity). -/
lemma pk_hlev_of_full {w : Param N} {S : Finset (Fin N)} {A η : ℝ}
    (h : ∀ t, ∀ i ∈ S, |Num w S S t i - A| ≤ η) :
    ∀ Y ⊆ S, ∀ t, ∀ i ∈ S, |Num w S Y t i - A| ≤ η := by
  intro Y hY t i hi
  rw [Num_eq_avg w S Y t i]
  have hdisj : Disjoint Y Sᶜ := disjoint_left.2 fun x hx hx' => (mem_compl.1 hx') (hY hx)
  have hcard : ((agree (Y ∪ Sᶜ) t).card : ℝ) = (2 : ℝ) ^ (S.card - Y.card) := by
    rw [card_agree, card_union_of_disjoint hdisj, card_compl, Fintype.card_fin]
    have hSN : S.card ≤ N := card_le_N S
    have hYS : Y.card ≤ S.card := card_le_card hY
    push_cast
    congr 1
    omega
  have hpow : (0 : ℝ) < 2 ^ (S.card - Y.card) := by positivity
  have hsum : |∑ t' ∈ agree (Y ∪ Sᶜ) t, Num w S S t' i - (2 : ℝ) ^ (S.card - Y.card) * A|
      ≤ (2 : ℝ) ^ (S.card - Y.card) * η := by
    rw [← hcard, ← nsmul_eq_mul, ← sum_const, ← sum_sub_distrib, ← nsmul_eq_mul, ← sum_const]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t' _ => h t' i hi)
  rw [show (∑ t' ∈ agree (Y ∪ Sᶜ) t, Num w S S t' i) / 2 ^ (S.card - Y.card) - A =
    (∑ t' ∈ agree (Y ∪ Sᶜ) t, Num w S S t' i - 2 ^ (S.card - Y.card) * A) / 2 ^ (S.card - Y.card)
    by field_simp, abs_div, abs_of_pos hpow, div_le_iff₀ hpow]
  linarith

/-- Transport of a normalised near-minimiser through perturbations of size `E`. -/
lemma pk_ratio_transfer {F F' v v' cc cc' e E : ℝ} (hc : 1 ≤ cc) (hc' : 1 ≤ cc') (hE : 0 ≤ E)
    (h1 : |F - v| ≤ E) (h2 : |F' - v'| ≤ E) (h : F / cc ≤ F' / cc' + e) :
    v / cc ≤ v' / cc' + (e + 2 * E) := by
  rw [abs_le] at h1 h2
  have hc0 : 0 < cc := by linarith
  have hc0' : 0 < cc' := by linarith
  have a1 : v / cc ≤ F / cc + E := by
    have : v / cc ≤ (F + E) / cc := div_le_div_of_nonneg_right (by linarith) hc0.le
    have h3 : E / cc ≤ E := div_le_self hE hc
    rw [add_div] at this
    linarith
  have a2 : F' / cc' ≤ v' / cc' + E := by
    have : F' / cc' ≤ (v' + E) / cc' := div_le_div_of_nonneg_right (by linarith) hc0'.le
    have h3 : E / cc' ≤ E := div_le_self hE hc'
    rw [add_div] at this
    linarith
  linarith

/-- `F_θ(t)` is the bridge sum divided by `σ`. -/
lemma pk_F_bridge {F Tsum v σ K : ℝ} (hσ : 0 < σ) (hF : F = Tsum / σ) (h : |Tsum - σ * v| ≤ K) :
    |F - v| ≤ K / σ := by
  rw [hF, show Tsum / σ - v = (Tsum - σ * v) / σ by field_simp, abs_div, abs_of_pos hσ]
  exact div_le_div_of_nonneg_right h hσ.le

/-! ## 8. Upper bounds at the tilt -/

/-- **Pairs, upper bound (deterministic core).** With every full numerator of `{a, b}` within `η`
of `A`, the heavy-row decomposition `|Num_i(t) - (σ y_{(t,r0),i} + B_i)| ≤ φ`, the own entry of
`a` at every maximal cause state at most `c`, and no exact single-cut tie:
`φ_s({a, b}) ≤ (ρ²/4) (σ c + 2φ) / (2 (A - η) ln 2)`. -/
theorem pair_upper_core {z : Param N} (hz : z ∈ openCube N) (s : State N) {a b : Fin N}
    (hab : a ≠ b) (r0 : State N) {A η σ φ c : ℝ} (B : Fin N → ℝ) (hη : 0 ≤ η) (hηA : η < A)
    (hσ : 0 ≤ σ) (hc : 0 ≤ c)
    (hlev : ∀ t, ∀ i ∈ ({a, b} : Finset (Fin N)),
      |Num (flipP s z) {a, b} {a, b} t i - A| ≤ η)
    (hdec : ∀ t, ∀ i ∈ ({a, b} : Finset (Fin N)), |Num (flipP s z) {a, b} {a, b} t i -
      (σ * clamp01 (flipP s z (merge {a, b} t r0) i) + B i)| ≤ φ)
    (hown : ∀ tc ∈ sysMaxCauseStates (tpmOf z) {a, b} s s,
      clamp01 (flipP s z (merge {a, b} tc r0) a) ≤ c)
    (hnt : ∀ tc ∈ sysMaxCauseStates (tpmOf z) {a, b} s s,
      ∀ te ∈ sysMaxEffStates (tpmOf z) {a, b} s s,
        NoSingleTie (tpmOf z) {a, b} (pk_pair_card hab) s tc te) :
    phi z s {a, b} ≤ ur_rho 2 A η / 4 * ((σ * c + 2 * φ) / (2 * (A - η) * Real.log 2)) := by
  have ha : a ∈ ({a, b} : Finset (Fin N)) := mem_insert_self _ _
  have hφ : 0 ≤ φ := (abs_nonneg _).trans (hdec (fun _ => false) a ha)
  have hAη : 0 < A - η := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hden : 0 < 2 * (A - η) * Real.log 2 := by positivity
  have hr : 0 ≤ ur_rho 2 A η / 4 := by unfold ur_rho; positivity
  have hnum : 0 ≤ σ * c + 2 * φ := by positivity
  have hB0 : 0 ≤ ur_rho 2 A η / 4 * ((σ * c + 2 * φ) / (2 * (A - η) * Real.log 2)) :=
    mul_nonneg hr (div_nonneg hnum hden.le)
  unfold phi sysPhi
  refine sup'OrZero_le hB0 fun p hp => ?_
  obtain ⟨htc, hte⟩ := mem_product.1 hp
  rw [(pair_phiOfState hz s hab p.1 p.2).2.2 (hnt p.1 htc p.2 hte)]
  refine (min_le_left _ _).trans ?_
  unfold pairCutVal sysPhiAt
  refine (min_le_left _ _).trans ((pair_cause_le hz s hab hη hηA hlev p.1).trans ?_)
  refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (max_le ?_ hnum) hden.le) hr
  have h1 := abs_le.1 (hdec p.1 a ha)
  have h2 := abs_le.1 (hdec (flip p.1 b) a ha)
  have hy := hown p.1 htc
  have hy0 := clamp01_nonneg (flipP s z (merge {a, b} (flip p.1 b) r0) a)
  nlinarith [mul_le_mul_of_nonneg_left hy hσ, mul_nonneg hσ hy0]

/-- **Pairs at the tilt** (`A = a_2 Z`, `σ = P(tc)`, `r0 = tc`):
`φ_s({a, b}) ≤ ρ² · A/(A - η) · β/(8 a_2 ln 2) · (c + 2φ/P(tc))`.  With `c = 1` this is the
pair level `1/(8 a_2 ln 2) = 0.333` of the blueprint, times `β`, up to the explicit errors. -/
theorem pair_upper_tilt {w : Param N} (hw : w ∈ openCube N) (s : State N) {a b : Fin N}
    (hab : a ≠ b) {η φ c : ℝ} (B : Fin N → ℝ) (hη : 0 ≤ η) (hηA : η < lvK 2 * Zs w)
    (hc : 0 ≤ c)
    (hlev : ∀ t, ∀ i ∈ ({a, b} : Finset (Fin N)), |Num w {a, b} {a, b} t i - lvK 2 * Zs w| ≤ η)
    (hdec : ∀ t, ∀ i ∈ ({a, b} : Finset (Fin N)), |Num w {a, b} {a, b} t i -
      (Pw w (tcRow w) * clamp01 (w (merge {a, b} t (tcRow w)) i) + B i)| ≤ φ)
    (hown : ∀ tc ∈ sysMaxCauseStates (tpmOf (flipP s w)) {a, b} s s,
      clamp01 (w (merge {a, b} tc (tcRow w)) a) ≤ c)
    (hnt : ∀ tc ∈ sysMaxCauseStates (tpmOf (flipP s w)) {a, b} s s,
      ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) {a, b} s s,
        NoSingleTie (tpmOf (flipP s w)) {a, b} (pk_pair_card hab) s tc te) :
    phi (flipP s w) s {a, b} ≤ ur_rho 2 (lvK 2 * Zs w) η *
      (lvK 2 * Zs w / (lvK 2 * Zs w - η)) * (betaW w / (8 * lvK 2 * Real.log 2)) *
        (c + 2 * φ / Pw w (tcRow w)) := by
  have hz := pk_flipP_open (s := s) hw
  have hinv : flipP s (flipP s w) = w := flipP_invol s w
  have hP := b1_Pw_pos hw (tcRow w)
  have hZ := b1_Zs_pos hw
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hk := lvK_pos 2
  have h := pair_upper_core hz s hab (tcRow w) B hη hηA hP.le hc (by rw [hinv]; exact hlev)
    (by rw [hinv]; exact hdec) (by rw [hinv]; exact hown) hnt
  refine h.trans (le_of_eq ?_)
  have hAη : lvK 2 * Zs w - η ≠ 0 := by linarith
  unfold betaW
  field_simp
  ring

/-- **Pairs at the tilt, absolute level** (`c = 1`):
`φ_s({a, b}) ≤ ρ² · A/(A - η) · β/(8 a_2 ln 2) · (1 + 2φ/P(tc))`. -/
theorem pair_upper_tilt_abs {w : Param N} (hw : w ∈ openCube N) (s : State N) {a b : Fin N}
    (hab : a ≠ b) {η φ : ℝ} (B : Fin N → ℝ) (hη : 0 ≤ η) (hηA : η < lvK 2 * Zs w)
    (hlev : ∀ t, ∀ i ∈ ({a, b} : Finset (Fin N)), |Num w {a, b} {a, b} t i - lvK 2 * Zs w| ≤ η)
    (hdec : ∀ t, ∀ i ∈ ({a, b} : Finset (Fin N)), |Num w {a, b} {a, b} t i -
      (Pw w (tcRow w) * clamp01 (w (merge {a, b} t (tcRow w)) i) + B i)| ≤ φ)
    (hnt : ∀ tc ∈ sysMaxCauseStates (tpmOf (flipP s w)) {a, b} s s,
      ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) {a, b} s s,
        NoSingleTie (tpmOf (flipP s w)) {a, b} (pk_pair_card hab) s tc te) :
    phi (flipP s w) s {a, b} ≤ ur_rho 2 (lvK 2 * Zs w) η *
      (lvK 2 * Zs w / (lvK 2 * Zs w - η)) * (betaW w / (8 * lvK 2 * Real.log 2)) *
        (1 + 2 * φ / Pw w (tcRow w)) :=
  pair_upper_tilt hw s hab B hη hηA zero_le_one hlev hdec (fun _ _ => clamp01_le_one _) hnt

/-- **Triples, upper bound (deterministic core).** Let `S` be a triple ordered by `e`, every
numerator of `S` within `η` of `A` (`3η ≤ A`), the heavy-row decomposition with fluctuation `φ`,
every own entry `y_{(tc, r0),i}` at a maximal cause state at most `c`, no exact single-cut tie
(this excludes the all-cut profile, `allCut_zero_of_noTie`), and no effect window at the
threshold of `ur_upper_reduce_mip`.  Then (LP certificate C15 at scale `c`)
`φ_s(S) ≤ (ρ³/8) σ/(A ln 2) · ((5/3) c + (43/3) e + 166 φ/σ)`, `e = ur_err 3 A η σ`. -/
theorem triple_upper_core {z : Param N} (hz : z ∈ openCube N) (s : State N)
    {S : Finset (Fin N)} (e : Fin 3 ↪ Fin N) (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
    (hS2 : 2 ≤ S.card) (r0 : State N) {A η σ φ c : ℝ} (B : Fin N → ℝ) (hη : 0 ≤ η)
    (hηA : 3 * η ≤ A) (hA : 0 < A) (hσ : 0 < σ) (hc : 0 ≤ c)
    (hlev : ∀ Y ⊆ S, ∀ t, ∀ i ∈ S, |Num (flipP s z) S Y t i - A| ≤ η)
    (hdec : ∀ t, ∀ i ∈ S, |Num (flipP s z) S S t i -
      (σ * clamp01 (flipP s z (merge S t r0) i) + B i)| ≤ φ)
    (hown : ∀ tc ∈ sysMaxCauseStates (tpmOf z) S s s, ∀ i ∈ S,
      clamp01 (flipP s z (merge S tc r0) i) ≤ c)
    (hnt : ∀ tc ∈ sysMaxCauseStates (tpmOf z) S s s, ∀ te ∈ sysMaxEffStates (tpmOf z) S s s,
      NoSingleTie (tpmOf z) S hS2 s tc te)
    (heff : ∀ te ∈ sysMaxEffStates (tpmOf z) S s s, ∀ θ : SysPartition N S,
      sysPhiE (tpmOf z) S s θ s te = 0 ∨
        ur_rho 3 A η / 8 * (6 * η / ((A - η) * Real.log 2)) ≤ sysPhiE (tpmOf z) S s θ s te) :
    phi z s S ≤ ur_rho 3 A η / 8 * (σ / (A * Real.log 2)) *
      (5 / 3 * c + 43 / 3 * ur_err 3 A η σ + 166 * φ / σ) := by
  have hS3 : S.card = 3 := pk_card_S e hS
  have hAη : 0 < A - η := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have he0S : e 0 ∈ S := (hS _).2 ⟨0, rfl⟩
  have hφ : 0 ≤ φ := (abs_nonneg _).trans (hdec (fun _ => false) (e 0) he0S)
  have herr : 0 ≤ ur_err 3 A η σ := by
    unfold ur_err; exact div_nonneg (by positivity) (mul_pos hAη hσ).le
  have hr : 0 ≤ ur_rho 3 A η / 8 := by
    unfold ur_rho; exact div_nonneg (pow_nonneg (div_nonneg (by linarith) hAη.le) _) (by norm_num)
  set Bd := ur_rho 3 A η / 8 * (σ / (A * Real.log 2)) *
    (5 / 3 * c + 43 / 3 * ur_err 3 A η σ + 166 * φ / σ) with hBd
  have hBd0 : 0 ≤ Bd := mul_nonneg (mul_nonneg hr (by positivity)) (by positivity)
  by_contra hlt
  push Not at hlt
  have e1 : ur_rho S.card A η / 2 ^ S.card = ur_rho 3 A η / 8 := by rw [hS3]; norm_num
  have e2 : ur_err S.card A η σ = ur_err 3 A η σ := by rw [hS3]
  have e3 : ur_rho S.card A η / 2 ^ S.card * (2 * S.card * η / ((A - η) * Real.log 2)) =
      ur_rho 3 A η / 8 * (6 * η / ((A - η) * Real.log 2)) := by
    rw [hS3]; push_cast; ring
  rcases ur_upper_reduce_mip hz s hη hηA hA hσ hBd0 hlev hlt with
    ⟨tc, htc, te, hte, θ, hθ, hX, -, hmin, hXb⟩ | ⟨te, hte, θ, h1, h2⟩
  · rw [e1, e2] at hXb
    rw [e2] at hmin
    have hne : ∃ j ∈ S, profile θ j ≠ S.erase j := by
      by_contra hall
      push Not at hall
      have := allCut_zero_of_noTie hz s hS2 (hnt tc htc te hte) hθ hall
      linarith
    set ξ : Fin 3 → Fin 8 → ℝ := fun i u =>
      clamp01 (flipP s z (merge S (pkFlip e tc u) r0) (e i)) with hξ
    set E := 6 * φ / σ with hE
    have hE0 : 0 ≤ E := by positivity
    have hbr : ∀ θ' : SysPartition N S,
        |ur_F (flipP s z) θ' tc σ - lp3V (lpTab e hS θ') ξ| ≤ E := fun θ' =>
      pk_F_bridge hσ rfl (pk_bridge3 (flipP s z) e hS θ' tc ξ B
        fun i u => hdec (pkFlip e tc u) (e i) ((hS _).2 ⟨i, rfl⟩))
    have hcc1 : ∀ θ' : SysPartition N S, (1 : ℝ) ≤ sysCutCount θ' := fun θ' => by
      exact_mod_cast sysCutCount_pos θ'
    have hmin' : ∀ θ' : SysPartition N S, lp3V (lpTab e hS θ) ξ / sysCutCount θ ≤
        lp3V (lpTab e hS θ') ξ / sysCutCount θ' + (ur_err 3 A η σ + 2 * E) := fun θ' =>
      pk_ratio_transfer (hcc1 θ) (hcc1 θ') hE0 (hbr θ) (hbr θ') (hmin θ')
    have hnn : ∀ i u, 0 ≤ ξ i u := fun i u => clamp01_nonneg _
    have hown' : ∀ i, ξ i 0 ≤ c := by
      intro i
      simp only [hξ]
      rw [pkFlip_zero e tc 0 rfl]
      exact hown tc htc (e i) ((hS _).2 ⟨i, rfl⟩)
    have hLP := lp3_bound_own_sys e hS θ hne hnn hc hown' (by positivity) hmin'
    have hF := (abs_le.1 (hbr θ)).2
    have hkey : ur_F (flipP s z) θ tc σ + ur_err 3 A η σ ≤
        5 / 3 * c + 43 / 3 * ur_err 3 A η σ + 166 * φ / σ := by
      have : 166 * φ / σ = 83 / 3 * E := by rw [hE]; ring
      rw [this]
      linarith
    have hpos : 0 ≤ ur_rho 3 A η / 8 * (σ / (A * Real.log 2)) := mul_nonneg hr (by positivity)
    have := mul_le_mul_of_nonneg_left hkey hpos
    linarith
  · rw [e3] at h2
    rw [hS3] at h1
    rcases heff te hte θ with h0 | hbig
    · rw [h0, mul_zero] at h1
      linarith
    · linarith

/-- **4-sets, upper bound (deterministic core)** (LP certificate C15b at scale `c`):
`φ_s(S) ≤ (ρ⁴/16) σ/(A ln 2) · ((11/4) c + (169/4) e + 668 φ/σ)`, `e = ur_err 4 A η σ`. -/
theorem four_upper_core {z : Param N} (hz : z ∈ openCube N) (s : State N)
    {S : Finset (Fin N)} (e : Fin 4 ↪ Fin N) (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
    (hS2 : 2 ≤ S.card) (r0 : State N) {A η σ φ c : ℝ} (B : Fin N → ℝ) (hη : 0 ≤ η)
    (hηA : 3 * η ≤ A) (hA : 0 < A) (hσ : 0 < σ) (hc : 0 ≤ c)
    (hlev : ∀ Y ⊆ S, ∀ t, ∀ i ∈ S, |Num (flipP s z) S Y t i - A| ≤ η)
    (hdec : ∀ t, ∀ i ∈ S, |Num (flipP s z) S S t i -
      (σ * clamp01 (flipP s z (merge S t r0) i) + B i)| ≤ φ)
    (hown : ∀ tc ∈ sysMaxCauseStates (tpmOf z) S s s, ∀ i ∈ S,
      clamp01 (flipP s z (merge S tc r0) i) ≤ c)
    (hnt : ∀ tc ∈ sysMaxCauseStates (tpmOf z) S s s, ∀ te ∈ sysMaxEffStates (tpmOf z) S s s,
      NoSingleTie (tpmOf z) S hS2 s tc te)
    (heff : ∀ te ∈ sysMaxEffStates (tpmOf z) S s s, ∀ θ : SysPartition N S,
      sysPhiE (tpmOf z) S s θ s te = 0 ∨
        ur_rho 4 A η / 16 * (8 * η / ((A - η) * Real.log 2)) ≤ sysPhiE (tpmOf z) S s θ s te) :
    phi z s S ≤ ur_rho 4 A η / 16 * (σ / (A * Real.log 2)) *
      (11 / 4 * c + 169 / 4 * ur_err 4 A η σ + 668 * φ / σ) := by
  have hS4 : S.card = 4 := pk_card_S e hS
  have hAη : 0 < A - η := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have he0S : e 0 ∈ S := (hS _).2 ⟨0, rfl⟩
  have hφ : 0 ≤ φ := (abs_nonneg _).trans (hdec (fun _ => false) (e 0) he0S)
  have herr : 0 ≤ ur_err 4 A η σ := by
    unfold ur_err; exact div_nonneg (by positivity) (mul_pos hAη hσ).le
  have hr : 0 ≤ ur_rho 4 A η / 16 := by
    unfold ur_rho; exact div_nonneg (pow_nonneg (div_nonneg (by linarith) hAη.le) _) (by norm_num)
  set Bd := ur_rho 4 A η / 16 * (σ / (A * Real.log 2)) *
    (11 / 4 * c + 169 / 4 * ur_err 4 A η σ + 668 * φ / σ) with hBd
  have hBd0 : 0 ≤ Bd := mul_nonneg (mul_nonneg hr (by positivity)) (by positivity)
  by_contra hlt
  push Not at hlt
  have e1 : ur_rho S.card A η / 2 ^ S.card = ur_rho 4 A η / 16 := by rw [hS4]; norm_num
  have e2 : ur_err S.card A η σ = ur_err 4 A η σ := by rw [hS4]
  have e3 : ur_rho S.card A η / 2 ^ S.card * (2 * S.card * η / ((A - η) * Real.log 2)) =
      ur_rho 4 A η / 16 * (8 * η / ((A - η) * Real.log 2)) := by
    rw [hS4]; push_cast; ring
  rcases ur_upper_reduce_mip hz s hη hηA hA hσ hBd0 hlev hlt with
    ⟨tc, htc, te, hte, θ, hθ, hX, -, hmin, hXb⟩ | ⟨te, hte, θ, h1, h2⟩
  · rw [e1, e2] at hXb
    rw [e2] at hmin
    have hne : ∃ j ∈ S, profile θ j ≠ S.erase j := by
      by_contra hall
      push Not at hall
      have := allCut_zero_of_noTie hz s hS2 (hnt tc htc te hte) hθ hall
      linarith
    set ξ : Fin 4 → Fin 16 → ℝ := fun i u =>
      clamp01 (flipP s z (merge S (pkFlip e tc u) r0) (e i)) with hξ
    set E := 8 * φ / σ with hE
    have hE0 : 0 ≤ E := by positivity
    have hbr : ∀ θ' : SysPartition N S,
        |ur_F (flipP s z) θ' tc σ - lp4V (lpTab e hS θ') ξ| ≤ E := fun θ' =>
      pk_F_bridge hσ rfl (pk_bridge4 (flipP s z) e hS θ' tc ξ B
        fun i u => hdec (pkFlip e tc u) (e i) ((hS _).2 ⟨i, rfl⟩))
    have hcc1 : ∀ θ' : SysPartition N S, (1 : ℝ) ≤ sysCutCount θ' := fun θ' => by
      exact_mod_cast sysCutCount_pos θ'
    have hmin' : ∀ θ' : SysPartition N S, lp4V (lpTab e hS θ) ξ / sysCutCount θ ≤
        lp4V (lpTab e hS θ') ξ / sysCutCount θ' + (ur_err 4 A η σ + 2 * E) := fun θ' =>
      pk_ratio_transfer (hcc1 θ) (hcc1 θ') hE0 (hbr θ) (hbr θ') (hmin θ')
    have hnn : ∀ i u, 0 ≤ ξ i u := fun i u => clamp01_nonneg _
    have hown' : ∀ i, ξ i 0 ≤ c := by
      intro i
      simp only [hξ]
      rw [pkFlip_zero e tc 0 rfl]
      exact hown tc htc (e i) ((hS _).2 ⟨i, rfl⟩)
    have hLP := lp4_bound_own_sys e hS θ hne hnn hc hown' (by positivity) hmin'
    have hF := (abs_le.1 (hbr θ)).2
    have hkey : ur_F (flipP s z) θ tc σ + ur_err 4 A η σ ≤
        11 / 4 * c + 169 / 4 * ur_err 4 A η σ + 668 * φ / σ := by
      have : 668 * φ / σ = 167 / 2 * E := by rw [hE]; ring
      rw [this]
      linarith
    have hpos : 0 ≤ ur_rho 4 A η / 16 * (σ / (A * Real.log 2)) := mul_nonneg hr (by positivity)
    have := mul_le_mul_of_nonneg_left hkey hpos
    linarith
  · rw [e3] at h2
    rw [hS4] at h1
    rcases heff te hte θ with h0 | hbig
    · rw [h0, mul_zero] at h1
      linarith
    · linarith

/-- **Triples at the tilt** (`A = a_3 Z`, `σ = P(tc)`, `r0 = tc`):
`φ_s(S) ≤ ρ³ · levTrip · β · (c + (43/5) e + (498/5) φ/P(tc))`, `c` a bound on the own entries
`y_{(tc_S, tcRow|_{Sᶜ}), i}` at the maximal cause states of `S`. -/
theorem triple_upper_tilt {w : Param N} (hw : w ∈ openCube N) (s : State N)
    {S : Finset (Fin N)} (e : Fin 3 ↪ Fin N) (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
    (hS2 : 2 ≤ S.card) {η φ c : ℝ} (B : Fin N → ℝ) (hη : 0 ≤ η)
    (hηA : 3 * η ≤ lvK 3 * Zs w) (hc : 0 ≤ c)
    (hlev : ∀ t, ∀ i ∈ S, |Num w S S t i - lvK 3 * Zs w| ≤ η)
    (hdec : ∀ t, ∀ i ∈ S, |Num w S S t i -
      (Pw w (tcRow w) * clamp01 (w (merge S t (tcRow w)) i) + B i)| ≤ φ)
    (hown : ∀ tc ∈ sysMaxCauseStates (tpmOf (flipP s w)) S s s, ∀ i ∈ S,
      clamp01 (w (merge S tc (tcRow w)) i) ≤ c)
    (hnt : ∀ tc ∈ sysMaxCauseStates (tpmOf (flipP s w)) S s s,
      ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) S s s,
        NoSingleTie (tpmOf (flipP s w)) S hS2 s tc te)
    (heff : ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) S s s, ∀ θ : SysPartition N S,
      sysPhiE (tpmOf (flipP s w)) S s θ s te = 0 ∨
        ur_rho 3 (lvK 3 * Zs w) η / 8 * (6 * η / ((lvK 3 * Zs w - η) * Real.log 2)) ≤
          sysPhiE (tpmOf (flipP s w)) S s θ s te) :
    phi (flipP s w) s S ≤ ur_rho 3 (lvK 3 * Zs w) η * levTrip * betaW w *
      (c + 43 / 5 * ur_err 3 (lvK 3 * Zs w) η (Pw w (tcRow w)) +
        498 / 5 * φ / Pw w (tcRow w)) := by
  have hz := pk_flipP_open (s := s) hw
  have hinv : flipP s (flipP s w) = w := flipP_invol s w
  have hP := b1_Pw_pos hw (tcRow w)
  have hZ := b1_Zs_pos hw
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hk := lvK_pos 3
  have h := triple_upper_core hz s e hS hS2 (tcRow w) B hη hηA (by positivity) hP hc
    (by rw [hinv]; exact pk_hlev_of_full hlev) (by rw [hinv]; exact hdec)
    (by rw [hinv]; exact hown) hnt heff
  refine h.trans (le_of_eq ?_)
  rw [levTrip]
  unfold betaW
  field_simp
  ring

/-- **Triples at the tilt, absolute level** (`c = 1`): `φ_s(S) ≤ ρ³ levTrip β (1 + …)`. -/
theorem triple_upper_tilt_abs {w : Param N} (hw : w ∈ openCube N) (s : State N)
    {S : Finset (Fin N)} (e : Fin 3 ↪ Fin N) (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
    (hS2 : 2 ≤ S.card) {η φ : ℝ} (B : Fin N → ℝ) (hη : 0 ≤ η)
    (hηA : 3 * η ≤ lvK 3 * Zs w)
    (hlev : ∀ t, ∀ i ∈ S, |Num w S S t i - lvK 3 * Zs w| ≤ η)
    (hdec : ∀ t, ∀ i ∈ S, |Num w S S t i -
      (Pw w (tcRow w) * clamp01 (w (merge S t (tcRow w)) i) + B i)| ≤ φ)
    (hnt : ∀ tc ∈ sysMaxCauseStates (tpmOf (flipP s w)) S s s,
      ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) S s s,
        NoSingleTie (tpmOf (flipP s w)) S hS2 s tc te)
    (heff : ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) S s s, ∀ θ : SysPartition N S,
      sysPhiE (tpmOf (flipP s w)) S s θ s te = 0 ∨
        ur_rho 3 (lvK 3 * Zs w) η / 8 * (6 * η / ((lvK 3 * Zs w - η) * Real.log 2)) ≤
          sysPhiE (tpmOf (flipP s w)) S s θ s te) :
    phi (flipP s w) s S ≤ ur_rho 3 (lvK 3 * Zs w) η * levTrip * betaW w *
      (1 + 43 / 5 * ur_err 3 (lvK 3 * Zs w) η (Pw w (tcRow w)) +
        498 / 5 * φ / Pw w (tcRow w)) :=
  triple_upper_tilt hw s e hS hS2 B hη hηA zero_le_one hlev hdec
    (fun _ _ _ _ => clamp01_le_one _) hnt heff

/-- **Triples at the tilt, level `y_max`** (the blueprint's form; see the header: it needs the
maximal cause states of `S` to agree with `tc` on `S`, which fails when the flipped state `tc^S`
is maximal). -/
theorem triple_upper_tilt_ymax {w : Param N} (hw : w ∈ openCube N) (s : State N)
    {S : Finset (Fin N)} (e : Fin 3 ↪ Fin N) (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
    (hS2 : 2 ≤ S.card) {η φ : ℝ} (B : Fin N → ℝ) (hη : 0 ≤ η)
    (hηA : 3 * η ≤ lvK 3 * Zs w)
    (hlev : ∀ t, ∀ i ∈ S, |Num w S S t i - lvK 3 * Zs w| ≤ η)
    (hdec : ∀ t, ∀ i ∈ S, |Num w S S t i -
      (Pw w (tcRow w) * clamp01 (w (merge S t (tcRow w)) i) + B i)| ≤ φ)
    (hagree : ∀ tc ∈ sysMaxCauseStates (tpmOf (flipP s w)) S s s, ∀ j ∈ S, tc j = tcRow w j)
    (hnt : ∀ tc ∈ sysMaxCauseStates (tpmOf (flipP s w)) S s s,
      ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) S s s,
        NoSingleTie (tpmOf (flipP s w)) S hS2 s tc te)
    (heff : ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) S s s, ∀ θ : SysPartition N S,
      sysPhiE (tpmOf (flipP s w)) S s θ s te = 0 ∨
        ur_rho 3 (lvK 3 * Zs w) η / 8 * (6 * η / ((lvK 3 * Zs w - η) * Real.log 2)) ≤
          sysPhiE (tpmOf (flipP s w)) S s θ s te) :
    phi (flipP s w) s S ≤ ur_rho 3 (lvK 3 * Zs w) η * levTrip * betaW w *
      (yMaxW w + 43 / 5 * ur_err 3 (lvK 3 * Zs w) η (Pw w (tcRow w)) +
        498 / 5 * φ / Pw w (tcRow w)) := by
  refine triple_upper_tilt hw s e hS hS2 B hη hηA ((clamp01_nonneg _).trans (le_yMaxW w (e 0)))
    hlev hdec (fun tc htc i _ => ?_) hnt heff
  have hm : merge S tc (tcRow w) = tcRow w := by
    funext j
    by_cases hj : j ∈ S
    · rw [merge_mem hj]; exact hagree tc htc j hj
    · rw [merge_not_mem hj]
  rw [hm]
  exact le_yMaxW w i

/-- **4-sets at the tilt** (`A = a_4 Z`): `φ_s(S) ≤ ρ⁴ · (165/196) levTrip · β ·
(c + (169/11) e + (2672/11) φ/P(tc))`. -/
theorem four_upper_tilt {w : Param N} (hw : w ∈ openCube N) (s : State N)
    {S : Finset (Fin N)} (e : Fin 4 ↪ Fin N) (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
    (hS2 : 2 ≤ S.card) {η φ c : ℝ} (B : Fin N → ℝ) (hη : 0 ≤ η)
    (hηA : 3 * η ≤ lvK 4 * Zs w) (hc : 0 ≤ c)
    (hlev : ∀ t, ∀ i ∈ S, |Num w S S t i - lvK 4 * Zs w| ≤ η)
    (hdec : ∀ t, ∀ i ∈ S, |Num w S S t i -
      (Pw w (tcRow w) * clamp01 (w (merge S t (tcRow w)) i) + B i)| ≤ φ)
    (hown : ∀ tc ∈ sysMaxCauseStates (tpmOf (flipP s w)) S s s, ∀ i ∈ S,
      clamp01 (w (merge S tc (tcRow w)) i) ≤ c)
    (hnt : ∀ tc ∈ sysMaxCauseStates (tpmOf (flipP s w)) S s s,
      ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) S s s,
        NoSingleTie (tpmOf (flipP s w)) S hS2 s tc te)
    (heff : ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) S s s, ∀ θ : SysPartition N S,
      sysPhiE (tpmOf (flipP s w)) S s θ s te = 0 ∨
        ur_rho 4 (lvK 4 * Zs w) η / 16 * (8 * η / ((lvK 4 * Zs w - η) * Real.log 2)) ≤
          sysPhiE (tpmOf (flipP s w)) S s θ s te) :
    phi (flipP s w) s S ≤ ur_rho 4 (lvK 4 * Zs w) η * (165 / 196 * levTrip) * betaW w *
      (c + 169 / 11 * ur_err 4 (lvK 4 * Zs w) η (Pw w (tcRow w)) +
        2672 / 11 * φ / Pw w (tcRow w)) := by
  have hz := pk_flipP_open (s := s) hw
  have hinv : flipP s (flipP s w) = w := flipP_invol s w
  have hP := b1_Pw_pos hw (tcRow w)
  have hZ := b1_Zs_pos hw
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hk := lvK_pos 4
  have h := four_upper_core hz s e hS hS2 (tcRow w) B hη hηA (by positivity) hP hc
    (by rw [hinv]; exact pk_hlev_of_full hlev) (by rw [hinv]; exact hdec)
    (by rw [hinv]; exact hown) hnt heff
  refine h.trans (le_of_eq ?_)
  rw [levTrip, lvK_three, lvK_four]
  unfold betaW
  field_simp
  ring

/-- **4-sets at the tilt, absolute level** (`c = 1`). -/
theorem four_upper_tilt_abs {w : Param N} (hw : w ∈ openCube N) (s : State N)
    {S : Finset (Fin N)} (e : Fin 4 ↪ Fin N) (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
    (hS2 : 2 ≤ S.card) {η φ : ℝ} (B : Fin N → ℝ) (hη : 0 ≤ η)
    (hηA : 3 * η ≤ lvK 4 * Zs w)
    (hlev : ∀ t, ∀ i ∈ S, |Num w S S t i - lvK 4 * Zs w| ≤ η)
    (hdec : ∀ t, ∀ i ∈ S, |Num w S S t i -
      (Pw w (tcRow w) * clamp01 (w (merge S t (tcRow w)) i) + B i)| ≤ φ)
    (hnt : ∀ tc ∈ sysMaxCauseStates (tpmOf (flipP s w)) S s s,
      ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) S s s,
        NoSingleTie (tpmOf (flipP s w)) S hS2 s tc te)
    (heff : ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) S s s, ∀ θ : SysPartition N S,
      sysPhiE (tpmOf (flipP s w)) S s θ s te = 0 ∨
        ur_rho 4 (lvK 4 * Zs w) η / 16 * (8 * η / ((lvK 4 * Zs w - η) * Real.log 2)) ≤
          sysPhiE (tpmOf (flipP s w)) S s θ s te) :
    phi (flipP s w) s S ≤ ur_rho 4 (lvK 4 * Zs w) η * (165 / 196 * levTrip) * betaW w *
      (1 + 169 / 11 * ur_err 4 (lvK 4 * Zs w) η (Pw w (tcRow w)) +
        2672 / 11 * φ / Pw w (tcRow w)) :=
  four_upper_tilt hw s e hS hS2 B hη hηA zero_le_one hlev hdec
    (fun _ _ _ _ => clamp01_le_one _) hnt heff

/-! ## 9. The triple lower bound with a general base pattern and a separate margin (W2 7.5) -/

/-- **Every tied cause state agrees with the base pattern `t0` on the triple**, given the pattern
margin `m` (`Σ_i Num_i(t) + m ≤ Σ_i Num_i(t0)` for `t ≠ t0` on `S`). -/
lemma tl_tc_agree {z : Param N} (hz : z ∈ openCube N) (s : State N) {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (t0 : State N) {A η m : ℝ} (hη : 0 ≤ η)
    (hηA : η < A)
    (hlev : ∀ t, ∀ i ∈ ({a, b, c} : Finset (Fin N)),
      |Num (flipP s z) {a, b, c} {a, b, c} t i - A| ≤ η)
    (hmarg : ∀ t : State N, (∃ j ∈ ({a, b, c} : Finset (Fin N)), t j ≠ t0 j) →
      ∑ i ∈ ({a, b, c} : Finset (Fin N)), Num (flipP s z) {a, b, c} {a, b, c} t i + m ≤
        ∑ i ∈ ({a, b, c} : Finset (Fin N)), Num (flipP s z) {a, b, c} {a, b, c} t0 i)
    (hsm : 24 * A * η ^ 2 < (A - η) ^ 2 * m) {tc : State N}
    (htc : tc ∈ sysMaxCauseStates (tpmOf z) {a, b, c} s s) :
    ∀ j ∈ ({a, b, c} : Finset (Fin N)), tc j = t0 j := by
  by_contra hne
  push Not at hne
  have hm := hmarg tc hne
  have haS : a ∈ ({a, b, c} : Finset (Fin N)) := by simp
  have hbS : b ∈ ({a, b, c} : Finset (Fin N)) := by simp
  have hcS : c ∈ ({a, b, c} : Finset (Fin N)) := by simp
  rw [tl_sum3 hab hac hbc, tl_sum3 hab hac hbc] at hm
  have hmax := prod_Num_max_of_mem hz s tc htc t0
  rw [tl_prod3 hab hac hbc, tl_prod3 hab hac hbc] at hmax
  have := tl_prod_gap hη hηA (hlev t0 a haS) (hlev t0 b hbS) (hlev t0 c hcS)
    (hlev tc a haS) (hlev tc b hbS) (hlev tc c hcS) hm hsm
  linarith

/-- **`pk_tl_triple_lower_gen'`** (W2, 7.5): `tl_triple_lower_gen` with (i) an arbitrary base
pattern `t0` (patterns `t` differing from `t0` on `S` instead of `tl_pat3`), and (ii) a separate
pattern margin `m` with `24 A η² < (A - η)² m`.  Conclusion unchanged:
`φ_s(S) ≥ σ (y - 6η²/((A - η) σ)) / (8 A ln 2)`. -/
theorem pk_tl_triple_lower_gen' {z : Param N} (hz : z ∈ openCube N) (s : State N) {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (t0 : State N) {A η δ y σ m E0 : ℝ}
    (hη : 0 ≤ η) (hηA : 3 * η ≤ A) (hA : 0 < A) (hδ : 0 ≤ δ) (hy : 0 < y) (hσ : 0 < σ)
    (hlev : ∀ Y ⊆ ({a, b, c} : Finset (Fin N)), ∀ t, ∀ i ∈ ({a, b, c} : Finset (Fin N)),
      |Num (flipP s z) {a, b, c} Y t i - A| ≤ η)
    (hreg : ∀ θ : SysPartition N {a, b, c},
      (∃ j ∈ ({a, b, c} : Finset (Fin N)), profile θ j ≠
        profile (tl_thetaStar a b c hab hac hbc) j) →
      (1 + δ) * tl_F (flipP s z) (tl_thetaStar a b c hab hac hbc) t0 σ / 5 ≤
        tl_F (flipP s z) θ t0 σ / (sysCutCount θ : ℝ))
    (hFy : y ≤ tl_F (flipP s z) (tl_thetaStar a b c hab hac hbc) t0 σ)
    (hmarg : ∀ t : State N, (∃ j ∈ ({a, b, c} : Finset (Fin N)), t j ≠ t0 j) →
      ∑ i ∈ ({a, b, c} : Finset (Fin N)), Num (flipP s z) {a, b, c} {a, b, c} t i + m ≤
        ∑ i ∈ ({a, b, c} : Finset (Fin N)), Num (flipP s z) {a, b, c} {a, b, c} t0 i)
    (hsmall : 36 * η ^ 2 < δ * y * σ * (A - η))
    (hmsmall : 24 * A * η ^ 2 < (A - η) ^ 2 * m)
    (hE0 : 6 * η / ((A - η) * Real.log 2) ≤ E0)
    (heff : ∃ te ∈ sysMaxEffStates (tpmOf z) {a, b, c} s s,
      ∀ θ : SysPartition N {a, b, c}, E0 ≤ sysPhiE (tpmOf z) {a, b, c} s θ s te) :
    σ * (y - 6 * η ^ 2 / ((A - η) * σ)) / (8 * A * Real.log 2) ≤ phi z s {a, b, c} := by
  set S : Finset (Fin N) := {a, b, c} with hSdef
  set w := flipP s z
  set θs := tl_thetaStar a b c hab hac hbc
  have hηA' : η < A := by
    rcases hη.lt_or_eq with h | h
    · linarith
    · rw [← h]; exact hA
  have hAη : 0 < A - η := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcard : S.card = 3 := tl_card3 hab hac hbc
  obtain ⟨te, hte, hE⟩ := heff
  obtain ⟨tc, htc⟩ := sysMaxCauseStates_nonempty (tpmOf z) S s s
  have htc0 := tl_tc_agree hz s hab hac hbc t0 hη hηA'
    (fun t i hi => hlev S (subset_refl _) t i hi) hmarg hmsmall htc
  set R := 3 * (2 * η ^ 2 / (A * (A - η))) with hR
  have hR0 : 0 ≤ R := by positivity
  set P : SysPartition N S → ℝ := fun θ => ∑ i ∈ S, ur_D w θ t0 i with hP
  have hnear : ∀ θ : SysPartition N S, |ur_G w θ t0 - P θ / A| ≤ R := by
    intro θ
    have := ur_G_near hη hηA' w t0 (fun Y hY i hi => hlev Y hY t0 i hi) θ
    rw [hcard] at this
    push_cast at this
    exact this
  have hGeq : ∀ θ : SysPartition N S, ur_G w θ tc = ur_G w θ t0 := by
    intro θ
    unfold ur_G
    refine sum_congr rfl fun i _ => ?_
    have h1 : Num w S S tc i = Num w S S t0 i := Num_congr (fun j hj => htc0 j hj) w i
    have h2 : Num w S (S \ profile θ i) tc i = Num w S (S \ profile θ i) t0 i :=
      Num_congr (fun j hj => htc0 j (sdiff_subset hj)) w i
    rw [h1, h2]
  have hback := sysBackCause_ge_of_mem hz s tc htc
  rw [hcard] at hback
  have hb0 : 0 < sysBackCause (tpmOf z) S s s tc := lt_of_lt_of_le (by norm_num) hback
  have hb1 := tl_backCause_le_one s hz hη hηA (fun t i hi => hlev S (subset_refl _) t i hi) tc
  have hC : ∀ θ : SysPartition N S, sysPhiC (tpmOf z) S s θ s tc =
      sysBackCause (tpmOf z) S s s tc * pos (ur_G w θ t0 / Real.log 2) := by
    intro θ
    unfold sysPhiC
    rw [ur_logb_eq s hz tc θ, hGeq θ]
  have hDle : ∀ θ : SysPartition N S, ur_G w θ t0 ≤ 6 * η / (A - η) := by
    intro θ
    have h1 := (abs_le.1 (hnear θ)).2
    have h2 : P θ ≤ 3 * (2 * η) := by
      have hs := sum_le_card_nsmul S (fun i => ur_D w θ t0 i) (2 * η) fun i hi => by
        have hx := hlev S (subset_refl _) t0 i hi
        have hy' := hlev _ (sdiff_subset : S \ profile θ i ⊆ S) t0 i hi
        rw [abs_le] at hx hy'
        unfold ur_D; linarith
      rw [hcard, nsmul_eq_mul] at hs
      simp only [hP]
      push_cast at hs
      linarith
    have h3 : P θ / A ≤ 6 * η / A := by
      rw [div_le_div_iff_of_pos_right hA]; linarith
    have h4 : 6 * η / A + R = 6 * η / (A - η) := by
      rw [hR]; field_simp; ring
    linarith
  have hCle : ∀ θ : SysPartition N S, sysPhiC (tpmOf z) S s θ s tc ≤ E0 := by
    intro θ
    rw [hC θ]
    have hp : pos (ur_G w θ t0 / Real.log 2) ≤ 6 * η / ((A - η) * Real.log 2) := by
      unfold pos
      refine max_le (by positivity) ?_
      rw [← div_div]
      exact div_le_div_of_nonneg_right (hDle θ) hlog2.le
    have h0 : 0 ≤ pos (ur_G w θ t0 / Real.log 2) := pos_nonneg _
    calc _ ≤ 1 * pos (ur_G w θ t0 / Real.log 2) := mul_le_mul_of_nonneg_right hb1 h0
      _ ≤ _ := by rw [one_mul]; exact hp.trans hE0
  have hAt : ∀ θ : SysPartition N S, sysPhiAt (tpmOf z) S s θ s tc te =
      sysPhiC (tpmOf z) S s θ s tc := fun θ =>
    min_eq_left ((hCle θ).trans (hE θ))
  have hFs : tl_F w θs t0 σ = P θs / σ := rfl
  have hPs : y * σ ≤ P θs := by
    rw [hFs, le_div_iff₀ hσ] at hFy; exact hFy
  have hLs : y * σ / A ≤ P θs / A := div_le_div_of_nonneg_right hPs hA.le
  have hsm' : 6 * R < δ * (y * σ / A) := by
    rw [hR]
    have : 36 * η ^ 2 / (A * (A - η)) < δ * y * σ * (A - η) / (A * (A - η)) :=
      div_lt_div_of_pos_right hsmall (mul_pos hA hAη)
    have e1 : δ * y * σ * (A - η) / (A * (A - η)) = δ * (y * σ / A) := by
      field_simp
    have e2 : 6 * (3 * (2 * η ^ 2 / (A * (A - η)))) = 36 * η ^ 2 / (A * (A - η)) := by ring
    linarith
  have hδL : δ * (y * σ / A) ≤ δ * (P θs / A) := mul_le_mul_of_nonneg_left hLs hδ
  have hLs0 : 0 ≤ P θs / A := le_trans (by positivity) hLs
  have hcc5 : (sysCutCount θs : ℝ) = 5 := by
    rw [tl_cc_star hab hac hbc]; norm_num
  have hstrict : ∀ θ : SysPartition N S, (∃ j ∈ S, profile θ j ≠ profile θs j) →
      sysPhiAt (tpmOf z) S s θs s tc te / (sysCutCount θs : ℝ) <
        sysPhiAt (tpmOf z) S s θ s tc te / (sysCutCount θ : ℝ) := by
    intro θ hθ
    have hk1 : (1 : ℝ) ≤ sysCutCount θ := by exact_mod_cast sysCutCount_pos θ
    set k : ℝ := (sysCutCount θ : ℝ) with hk
    have hk0 : 0 < k := by linarith
    have hr := hreg θ hθ
    have hFθ : tl_F w θ t0 σ = P θ / σ := rfl
    rw [hFs, hFθ, div_div, le_div_iff₀ (mul_pos hσ hk0)] at hr
    have hr' : k * (1 + δ) * (P θs / A) ≤ 5 * (P θ / A) := by
      have : (1 + δ) * (P θs / σ) / 5 * (σ * k) = k * (1 + δ) * P θs / 5 := by
        field_simp
      rw [this] at hr
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 5)] at hr
      have : k * (1 + δ) * (P θs / A) = (k * (1 + δ) * P θs) / A := by ring
      rw [this, show 5 * (P θ / A) = (P θ * 5) / A by ring]
      exact div_le_div_of_nonneg_right hr hA.le
    have hGθ := abs_le.1 (hnear θ)
    have hGs := abs_le.1 (hnear θs)
    obtain ⟨hkey1, hkey0⟩ := tl_arith (Gs := ur_G w θs t0) (Gθ := ur_G w θ t0) hk1 hR0 hLs0 hr'
      (lt_of_lt_of_le hsm' hδL)
      (by linarith [hGθ.1]) (by linarith [hGs.2])
    rw [hAt, hAt, hC, hC, hcc5]
    have hpθ : pos (ur_G w θ t0 / Real.log 2) = ur_G w θ t0 / Real.log 2 :=
      max_eq_right (div_pos hkey0 hlog2).le
    rw [hpθ]
    set bb := sysBackCause (tpmOf z) S s s tc
    rcases le_or_gt (ur_G w θs t0) 0 with hneg | hposs
    · have : pos (ur_G w θs t0 / Real.log 2) = 0 :=
        max_eq_left (div_nonpos_of_nonpos_of_nonneg hneg hlog2.le)
      rw [this, mul_zero, zero_div]
      exact div_pos (mul_pos hb0 (div_pos hkey0 hlog2)) hk0
    · have : pos (ur_G w θs t0 / Real.log 2) = ur_G w θs t0 / Real.log 2 :=
        max_eq_right (div_pos hposs hlog2).le
      rw [this, div_lt_div_iff₀ (by norm_num) hk0]
      have : bb * (ur_G w θs t0 / Real.log 2) * k = bb / Real.log 2 * (k * ur_G w θs t0) := by
        ring
      rw [this]
      have : bb * (ur_G w θ t0 / Real.log 2) * 5 = bb / Real.log 2 * (5 * ur_G w θ t0) := by ring
      rw [this]
      exact mul_lt_mul_of_pos_left hkey1 (div_pos hb0 hlog2)
  have hval := sysPhiOfState_eq_of_strict (tpmOf z) S s θs s tc te hstrict
  have hle := sysPhiOfState_le_sysPhi (tpmOf z) S s s htc hte
  unfold phi
  refine le_trans ?_ hle
  rw [hval, hAt, hC]
  have hGlow : y * σ / A - R ≤ ur_G w θs t0 := by linarith [(abs_le.1 (hnear θs)).1]
  have hp1 : (y * σ / A - R) / Real.log 2 ≤ pos (ur_G w θs t0 / Real.log 2) :=
    le_max_of_le_right (div_le_div_of_nonneg_right hGlow hlog2.le)
  have hp0 : 0 ≤ pos (ur_G w θs t0 / Real.log 2) := pos_nonneg _
  have htarget : σ * (y - 6 * η ^ 2 / ((A - η) * σ)) / (8 * A * Real.log 2) =
      1 / 8 * ((y * σ / A - R) / Real.log 2) := by
    rw [hR]; field_simp; ring
  rw [htarget]
  calc 1 / 8 * ((y * σ / A - R) / Real.log 2) ≤ 1 / 8 * pos (ur_G w θs t0 / Real.log 2) :=
        mul_le_mul_of_nonneg_left hp1 (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (by rw [show (1 : ℝ) / 8 = 1 / 2 ^ 3 by norm_num]; exact hback) hp0

/-! ## 10. The deterministic core of Lemma TC (W2 7.2): targets `y_i - c (1 - q(t))` -/

section TC

variable {a b c : Fin N}

/-- The ordering `(a, b, c)` of a triple. -/
def pkE3 (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Fin 3 ↪ Fin N :=
  ⟨![a, b, c], by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp [hab, hac, hbc, hab.symm, hac.symm, hbc.symm] at h ⊢⟩

lemma pkE3_zero (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : pkE3 hab hac hbc 0 = a := rfl
lemma pkE3_one (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : pkE3 hab hac hbc 1 = b := rfl
lemma pkE3_two (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : pkE3 hab hac hbc 2 = c := rfl

lemma pkE3_S (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ x, x ∈ ({a, b, c} : Finset (Fin N)) ↔ ∃ i, pkE3 hab hac hbc i = x := by
  intro x
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, pkE3_zero hab hac hbc⟩
    · exact ⟨1, pkE3_one hab hac hbc⟩
    · exact ⟨2, pkE3_two hab hac hbc⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [pkE3_zero, pkE3_one, pkE3_two]

lemma pk_lp3CStar_at (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (i j : Fin 3) :
    cd_at lp3CStar i j = true ↔
      pkE3 hab hac hbc j ∈ profile (tl_thetaStar a b c hab hac hbc) (pkE3 hab hac hbc i) := by
  have hT : ∀ i j : Fin 3, cd_at lp3CStar i j =
      decide ((i = 0 ∧ j = 2) ∨ (i = 1 ∧ j ≠ 1) ∨ (i = 2 ∧ j ≠ 2)) := by decide
  rw [hT]
  fin_cases i <;> fin_cases j <;>
    simp [pkE3_zero, pkE3_one, pkE3_two, tl_profile_a, tl_profile_b, tl_profile_c, hab, hac, hbc,
      hab.symm, hac.symm, hbc.symm]

lemma pk_lpTab_star (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (i j : Fin 3) :
    cd_at (lpTab (pkE3 hab hac hbc) (pkE3_S hab hac hbc) (tl_thetaStar a b c hab hac hbc)) i j =
      cd_at lp3CStar i j :=
  Bool.eq_iff_iff.2 ((lpTab_at _ _ _ i j).trans (pk_lp3CStar_at hab hac hbc i j).symm)

lemma pk_lpTab_ne_star (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (θ : SysPartition N {a, b, c})
    (hθ : ∃ j ∈ ({a, b, c} : Finset (Fin N)), profile θ j ≠
      profile (tl_thetaStar a b c hab hac hbc) j) :
    lpTab (pkE3 hab hac hbc) (pkE3_S hab hac hbc) θ ≠ lp3CStar := by
  intro h
  obtain ⟨j, hj, hjne⟩ := hθ
  apply hjne
  obtain ⟨i, rfl⟩ := (pkE3_S hab hac hbc j).1 hj
  ext y
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := (pkE3_S hab hac hbc y).1 (prof_profile_subset θ _ hy)
    have := (lpTab_at (pkE3 hab hac hbc) (pkE3_S hab hac hbc) θ i k).2 hy
    rw [h] at this
    exact (pk_lp3CStar_at hab hac hbc i k).1 this
  · intro hy
    obtain ⟨k, rfl⟩ := (pkE3_S hab hac hbc y).1 (prof_profile_subset _ _ hy)
    have := (pk_lp3CStar_at hab hac hbc i k).2 hy
    rw [← h] at this
    exact (lpTab_at (pkE3 hab hac hbc) (pkE3_S hab hac hbc) θ i k).1 this

/-- The state `t'` agrees on `S` with `t0` flipped on the pattern where they differ. -/
lemma pk_flip_enc {k : ℕ} (e : Fin k ↪ Fin N) {S : Finset (Fin N)}
    (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) (t0 t' : State N) :
    ∀ j ∈ S, pkFlip e t0 (pkEnc k (fun q => decide (t' (e q) ≠ t0 (e q)))) j = t' j := by
  intro j hj
  obtain ⟨q, rfl⟩ := (hS j).1 hj
  rw [pkFlip_e, pk_testBit_enc]
  cases t' (e q) <;> cases t0 (e q) <;> simp

/-- **Lemma TC, deterministic core** (W2 7.2).  Order the triple as `(a, b, c)`; let the full
numerators at the eight patterns `t0 ⊕ u` be within `φ` of `σ ξ_{i,u} + B_i`, where the heavy
profile `ξ` has the shift-trick targets `ξ_{i,0} - ξ_{i,u} = c0 (1 - q(t)_{i,u})` (`u` not
flipping `i`) and pattern margin `m0`.  With the level band `η`, the smallness conditions and
an effect side `≥ E0`:
`φ_s(S) ≥ σ ((c0 (5/3 - t) - 6φ/σ) - 6η²/((A - η) σ)) / (8 A ln 2)`. -/
theorem triple_lower_tilt {z : Param N} (hz : z ∈ openCube N) (s : State N)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (t0 : State N) {A η δ σ φ c0 t m0 E0 : ℝ}
    (B : Fin N → ℝ) (ξ : Fin 3 → Fin 8 → ℝ)
    (hη : 0 ≤ η) (hηA : 3 * η ≤ A) (hA : 0 < A) (hδ : 0 ≤ δ) (hσ : 0 < σ) (hc0 : 0 ≤ c0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 2 / 3)
    (hlev : ∀ Y ⊆ ({a, b, c} : Finset (Fin N)), ∀ t', ∀ i ∈ ({a, b, c} : Finset (Fin N)),
      |Num (flipP s z) {a, b, c} Y t' i - A| ≤ η)
    (hξ : ∀ (i : Fin 3) (u : Fin 8), (u : ℕ).testBit i = false →
      ξ i 0 - ξ i u = c0 * (1 - lp3Q t i u))
    (hdec : ∀ (i : Fin 3) (u : Fin 8), |Num (flipP s z) {a, b, c} {a, b, c}
      (pkFlip (pkE3 hab hac hbc) t0 u) (pkE3 hab hac hbc i) -
        (σ * ξ i u + B (pkE3 hab hac hbc i))| ≤ φ)
    (hmarg : ∀ u : Fin 8, u ≠ 0 → ∑ i : Fin 3, ξ i u + m0 ≤ ∑ i : Fin 3, ξ i 0)
    (hy : 0 < c0 * (5 / 3 - t) - 6 * φ / σ)
    (hδ' : (1 + δ) * (c0 * (5 / 3 - t) + 6 * φ / σ) + 30 * φ / σ ≤
      (1 + 9 * t / 40) * (c0 * (5 / 3 - t)))
    (hsmall : 36 * η ^ 2 < δ * (c0 * (5 / 3 - t) - 6 * φ / σ) * σ * (A - η))
    (hmsmall : 24 * A * η ^ 2 < (A - η) ^ 2 * (σ * m0 - 6 * φ))
    (hE0 : 6 * η / ((A - η) * Real.log 2) ≤ E0)
    (heff : ∃ te ∈ sysMaxEffStates (tpmOf z) {a, b, c} s s,
      ∀ θ : SysPartition N {a, b, c}, E0 ≤ sysPhiE (tpmOf z) {a, b, c} s θ s te) :
    σ * ((c0 * (5 / 3 - t) - 6 * φ / σ) - 6 * η ^ 2 / ((A - η) * σ)) / (8 * A * Real.log 2) ≤
      phi z s {a, b, c} := by
  set e := pkE3 hab hac hbc with he
  have hS := pkE3_S hab hac hbc
  set E := 6 * φ / σ with hE
  have hφ : 0 ≤ φ := (abs_nonneg _).trans (hdec 0 0)
  have hE0' : 0 ≤ E := by positivity
  set θs := tl_thetaStar a b c hab hac hbc
  have hbr : ∀ θ : SysPartition N {a, b, c},
      |tl_F (flipP s z) θ t0 σ - lp3V (lpTab e hS θ) ξ| ≤ E := fun θ =>
    pk_F_bridge hσ rfl (pk_bridge3 (flipP s z) e hS θ t0 ξ B hdec)
  obtain ⟨hv, -, hreg0, -⟩ := lp3_interior_scaled hc0 ht0 ht1 hξ
  have hvs : lp3V (lpTab e hS θs) ξ = c0 * (5 / 3 - t) := by
    rw [lp3V_congr (pk_lpTab_star hab hac hbc) ξ, hv]
  have hFs := abs_le.1 (hbr θs)
  rw [hvs] at hFs
  -- the regularity hypothesis
  have hreg : ∀ θ : SysPartition N {a, b, c},
      (∃ j ∈ ({a, b, c} : Finset (Fin N)), profile θ j ≠ profile θs j) →
      (1 + δ) * tl_F (flipP s z) θs t0 σ / 5 ≤ tl_F (flipP s z) θ t0 σ / (sysCutCount θ : ℝ) := by
    intro θ hθ
    have hC := hreg0 _ (lpTab_mem e hS θ) (pk_lpTab_ne_star hab hac hbc θ hθ)
    rw [lpTab_cc, hv] at hC
    have hFθ := abs_le.1 (hbr θ)
    have hk1 : (1 : ℝ) ≤ sysCutCount θ := by exact_mod_cast sysCutCount_pos θ
    have hk0 : (0 : ℝ) < sysCutCount θ := by linarith
    have h1 : (1 + δ) * tl_F (flipP s z) θs t0 σ / 5 ≤ (1 + δ) * (c0 * (5 / 3 - t) + E) / 5 := by
      have := mul_le_mul_of_nonneg_left hFs.2 (by linarith : (0 : ℝ) ≤ 1 + δ)
      linarith
    have h2 : (1 + δ) * (c0 * (5 / 3 - t) + E) / 5 ≤
        (1 + 9 * t / 40) * (c0 * (5 / 3 - t)) / 5 - E := by
      have : 30 * φ / σ = 5 * E := by rw [hE]; ring
      rw [this] at hδ'
      linarith
    have h3 : lp3V (lpTab e hS θ) ξ / (sysCutCount θ : ℝ) ≤
        tl_F (flipP s z) θ t0 σ / (sysCutCount θ : ℝ) + E := by
      have : lp3V (lpTab e hS θ) ξ / (sysCutCount θ : ℝ) ≤
          (tl_F (flipP s z) θ t0 σ + E) / (sysCutCount θ : ℝ) :=
        div_le_div_of_nonneg_right (by linarith [hFθ.1]) hk0.le
      rw [add_div] at this
      linarith [div_le_self hE0' hk1]
    linarith
  -- the pattern margin
  have hmarg' : ∀ t' : State N, (∃ j ∈ ({a, b, c} : Finset (Fin N)), t' j ≠ t0 j) →
      ∑ i ∈ ({a, b, c} : Finset (Fin N)), Num (flipP s z) {a, b, c} {a, b, c} t' i
        + (σ * m0 - 6 * φ) ≤
        ∑ i ∈ ({a, b, c} : Finset (Fin N)), Num (flipP s z) {a, b, c} {a, b, c} t0 i := by
    intro t' ht'
    set u := pkEnc 3 (fun q => decide (t' (e q) ≠ t0 (e q))) with hu
    have hagr := pk_flip_enc e hS t0 t'
    have hu0 : u ≠ 0 := by
      intro h0
      obtain ⟨j, hj, hjne⟩ := ht'
      have := hagr j hj
      rw [← hu, h0, pkFlip_zero e t0 _ rfl] at this
      exact hjne this.symm
    have hNt : ∀ i, Num (flipP s z) {a, b, c} {a, b, c} t' i =
        Num (flipP s z) {a, b, c} {a, b, c} (pkFlip e t0 u) i := fun i =>
      Num_congr (fun j hj => (hagr j hj).symm) _ i
    rw [pk_sum_S e hS, pk_sum_S e hS]
    simp only [hNt]
    have hup : ∀ i : Fin 3, Num (flipP s z) {a, b, c} {a, b, c} (pkFlip e t0 u) (e i) ≤
        σ * ξ i u + B (e i) + φ := fun i => by linarith [(abs_le.1 (hdec i u)).2]
    have hlo : ∀ i : Fin 3, σ * ξ i 0 + B (e i) - φ ≤
        Num (flipP s z) {a, b, c} {a, b, c} t0 (e i) := fun i => by
      have := (abs_le.1 (hdec i 0)).1
      rw [pkFlip_zero e t0 0 rfl] at this
      linarith
    have hm := mul_le_mul_of_nonneg_left (hmarg u hu0) hσ.le
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at hm ⊢
    linarith [hup 0, hup 1, hup 2, hlo 0, hlo 1, hlo 2]
  have hFy : c0 * (5 / 3 - t) - 6 * φ / σ ≤ tl_F (flipP s z) θs t0 σ := by linarith [hFs.1]
  exact pk_tl_triple_lower_gen' hz s hab hac hbc t0 hη hηA hA hδ hy hσ hlev hreg hFy hmarg'
    hsmall hmsmall hE0 heff

/-- **The pattern margins of the `q(t)` configuration** (W2 (7.1)): with the targets on the
entries not flipping their unit, own entries `≥ c0`, own single flips `≤ 1` and the other
(pattern-only) entries `≤ ρ ≤ 1/3`, every pattern `u ≠ 0` loses at least `c0 (8/3 - t) - 1`. -/
theorem lp3Q_margin {c0 t ρ : ℝ} (ht : 0 ≤ t) (hρ : ρ ≤ 1 / 3) {ξ : Fin 3 → Fin 8 → ℝ}
    (hc0 : 0 ≤ c0)
    (hξ : ∀ (i : Fin 3) (u : Fin 8), (u : ℕ).testBit i = false →
      ξ i 0 - ξ i u = c0 * (1 - lp3Q t i u))
    (hown : ∀ i, c0 ≤ ξ i 0) (hone : ∀ i u, ξ i u ≤ 1)
    (hpriv : ∀ (i : Fin 3) (u : Fin 8), (u : ℕ).testBit i = true → (u : ℕ) ≠ 2 ^ (i : ℕ) →
      ξ i u ≤ ρ) :
    ∀ u : Fin 8, u ≠ 0 → ∑ i : Fin 3, ξ i u + (c0 * (8 / 3 - t) - 1) ≤ ∑ i : Fin 3, ξ i 0 := by
  intro u hu
  let g : Fin 3 → ℝ := fun i => if (u : ℕ).testBit i = true then
    (if (u : ℕ) = 2 ^ (i : ℕ) then c0 - 1 else c0 - ρ) else c0 * (1 - lp3Q t i u)
  have hg : ∀ i, g i ≤ ξ i 0 - ξ i u := by
    intro i
    simp only [g]
    by_cases hb : (u : ℕ).testBit i = true
    · rw [ite_eq_left hb]
      by_cases hs : (u : ℕ) = 2 ^ (i : ℕ)
      · rw [ite_eq_left hs]; linarith [hown i, hone i u]
      · rw [ite_eq_right hs]; linarith [hown i, hpriv i u hb hs]
    · rw [ite_eq_right hb, hξ i u (by simpa using hb)]
  have hsum : c0 * (8 / 3 - t) - 1 ≤ ∑ i : Fin 3, g i := by
    simp only [g, Fin.sum_univ_three]
    fin_cases u
    · exact absurd rfl hu
    all_goals
      simp (config := { decide := true }) [lp3Q, lp3QRole]
      nlinarith
  have h := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 3))) => hg i)
  rw [sum_sub_distrib] at h
  linarith

end TC

/-! ## 11. Effect lemmas (copies of `ThmP3Eff` with `x_i ≥ 1/2 + γ`; W2 7.4, Lemmas EF, EF-tc) -/

section Effect

/-- `ii_e ≤ |S| · p_e` at every state (the unconstrained probability is at least `p_e / 2^|S|`). -/
lemma pk_iiE_le (T : UnitTPM N) (S : Finset (Fin N)) (s t : State N) :
    sysIiE T S s s t ≤ S.card * sysEffProb T S s s t := by
  set e := sysEffProb T S s s t with he
  have he0 : 0 ≤ e := sysEffProb_nonneg T S s s t
  have hpow : (0 : ℝ) < 2 ^ S.card := by positivity
  have hu : e / 2 ^ S.card ≤ sysUncEff T S s t := by
    rw [tp_unc_eq, he, tp_eff_eq]
    refine div_le_div_of_nonneg_right ?_ hpow.le
    exact single_le_sum (f := fun r => ∏ j ∈ S, T.prob j r (t j))
      (fun r _ => prod_nonneg fun j _ => T.nonneg j r (t j)) (tp_mem_block s S)
  rcases he0.eq_or_lt with h0 | hpos
  · rw [sysIiE, ← he, ← h0]; simp
  · have hu0 : 0 < sysUncEff T S s t := lt_of_lt_of_le (div_pos hpos hpow) hu
    have hr : e / sysUncEff T S s t ≤ 2 ^ S.card := by
      rw [div_le_iff₀ hu0]
      rw [div_le_iff₀ hpow] at hu
      linarith
    have hl : Real.logb 2 (e / sysUncEff T S s t) ≤ S.card := by
      calc Real.logb 2 (e / sysUncEff T S s t) ≤ Real.logb 2 (2 ^ S.card) :=
            Real.logb_le_logb_of_le one_lt_two (div_pos hpos hu0) hr
        _ = S.card := by rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]
    rw [sysIiE, ← he]
    nlinarith

lemma pk_prob_not (T : UnitTPM N) (j : Fin N) (r : State N) (b : Bool) :
    T.prob j r (!b) = 1 - T.prob j r b := by
  have h := T.normalized j r
  cases b <;> simp <;> linarith

/-- **The maximal effect state** (generalises `tp_te_true`).  If every unit of `S` has
probability `x_j ≥ 1/2 + γ` of `te_j` from the current row, the other rows of the `S`-block of `s`
contribute at most `U0` to the unconstrained probability of `te`, and
`|S| · (1/2 - γ)/(1/2 + γ) < log₂(2^|S| e*/(e* + U0))` (`e* = p_e(te)`), then every maximal effect
state agrees with `te` on `S`. -/
theorem eff_te_agree {z : Param N} (s : State N) {S : Finset (Fin N)} (te : State N)
    {γ U0 : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1 / 2)
    (hx : ∀ j ∈ S, 1 / 2 + γ ≤ (tpmOf z).prob j s (te j))
    (hU : ∑ r ∈ (agree Sᶜ s).erase s, ∏ j ∈ S, (tpmOf z).prob j r (te j) ≤ U0)
    (hgap : (S.card : ℝ) * ((1 / 2 - γ) / (1 / 2 + γ)) <
      Real.logb 2 (2 ^ S.card * sysEffProb (tpmOf z) S s s te /
        (sysEffProb (tpmOf z) S s s te + U0))) :
    ∀ te' ∈ sysMaxEffStates (tpmOf z) S s s, ∀ j ∈ S, te' j = te j := by
  set T := tpmOf z
  set r := (1 / 2 - γ) / (1 / 2 + γ) with hr
  have hden : 0 < 1 / 2 + γ := by linarith
  have hr0 : 0 ≤ r := div_nonneg (by linarith) hden.le
  have he : sysEffProb T S s s te = ∏ j ∈ S, T.prob j s (te j) := tp_eff_eq T S s te
  have hepos : 0 < sysEffProb T S s s te := by
    rw [he]; exact prod_pos fun j hj => lt_of_lt_of_le (by linarith) (hx j hj)
  have hU0 : 0 ≤ U0 :=
    le_trans (sum_nonneg fun r _ => prod_nonneg fun j _ => T.nonneg j r _) hU
  have hpow : (0 : ℝ) < 2 ^ S.card := by positivity
  have hunc : sysUncEff T S s te ≤ (sysEffProb T S s s te + U0) / 2 ^ S.card := by
    rw [tp_unc_eq]
    refine div_le_div_of_nonneg_right ?_ hpow.le
    rw [← sum_erase_add _ _ (tp_mem_block s S), he]
    linarith
  have huncpos : 0 < sysUncEff T S s te := by
    rw [tp_unc_eq]
    refine div_pos ?_ hpow
    refine lt_of_lt_of_le ?_ (single_le_sum (f := fun r => ∏ j ∈ S, T.prob j r (te j))
      (fun r _ => prod_nonneg fun j _ => T.nonneg j r _) (tp_mem_block s S))
    rw [← he]; exact hepos
  have hiite : sysEffProb T S s s te * Real.logb 2 (2 ^ S.card * sysEffProb T S s s te /
      (sysEffProb T S s s te + U0)) ≤ sysIiE T S s s te := by
    unfold sysIiE
    refine mul_le_mul_of_nonneg_left ?_ hepos.le
    refine Real.logb_le_logb_of_le one_lt_two (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) huncpos]
    rw [le_div_iff₀ hpow] at hunc
    nlinarith
  intro te' hte' j hj
  by_contra hne
  have hflip : ∀ i, te' i ≠ te i → te' i = !(te i) := by
    intro i h
    cases h1 : te' i <;> cases h2 : te i <;> simp_all
  have he' : sysEffProb T S s s te' ≤ r * sysEffProb T S s s te := by
    rw [tp_eff_eq, he, ← mul_prod_erase S _ hj, ← mul_prod_erase S (fun j => T.prob j s (te j)) hj]
    have hf : T.prob j s (te' j) ≤ r * T.prob j s (te j) := by
      rw [hflip j hne, pk_prob_not]
      have hxj := hx j hj
      have hx1 := T.le_one j s (te j)
      rw [hr, div_mul_eq_mul_div, le_div_iff₀ hden]
      nlinarith
    have hrest : ∏ i ∈ S.erase j, T.prob i s (te' i) ≤ ∏ i ∈ S.erase j, T.prob i s (te i) := by
      refine prod_le_prod (fun i _ => T.nonneg i s _) fun i hi => ?_
      by_cases hti : te' i = te i
      · rw [hti]
      · rw [hflip i hti, pk_prob_not]
        linarith [hx i (mem_of_mem_erase hi)]
    have hp0 : 0 ≤ ∏ i ∈ S.erase j, T.prob i s (te' i) := prod_nonneg fun i _ => T.nonneg i s _
    calc T.prob j s (te' j) * ∏ i ∈ S.erase j, T.prob i s (te' i)
        ≤ (r * T.prob j s (te j)) * ∏ i ∈ S.erase j, T.prob i s (te i) :=
          mul_le_mul hf hrest hp0 (mul_nonneg hr0 (T.nonneg j s _))
      _ = _ := by ring
  have hii' := pk_iiE_le T S s te'
  have hmax := (mem_argmaxSet.1 hte') te
  have h1 : (S.card : ℝ) * sysEffProb T S s s te' ≤ S.card * r * sysEffProb T S s s te := by
    have := mul_le_mul_of_nonneg_left he' (Nat.cast_nonneg S.card)
    linarith
  have h2 := mul_lt_mul_of_pos_left hgap hepos
  change sysIiE T S s s te ≤ sysIiE T S s s te' at hmax
  nlinarith

/-- **The effect side at a maximal effect state** (generalises `tp_eff`).  If every cut factor
is at most `λ` times the intact factor, `effUnit_{Cᶜ}(te_j) ≤ λ x_j` for `∅ ≠ C ⊆ S \ {j}`, then
at any state `te'` agreeing with `te` on `S`, every partition has
`φ_e ≥ p_e(te) · log₂(1/λ)`. -/
theorem eff_phiE_ge {z : Param N} (hz : z ∈ openCube N) (s : State N) {S : Finset (Fin N)}
    (te te' : State N) (hagree : ∀ j ∈ S, te' j = te j) {lam : ℝ} (hl0 : 0 < lam)
    (hl1 : lam ≤ 1)
    (hcut : ∀ j ∈ S, ∀ C ⊆ S.erase j, C.Nonempty →
      effUnit (tpmOf z) Cᶜ s j (te j) ≤ lam * (tpmOf z).prob j s (te j))
    (θ : SysPartition N S) :
    sysEffProb (tpmOf z) S s s te * Real.logb 2 (1 / lam) ≤ sysPhiE (tpmOf z) S s θ s te' := by
  set T := tpmOf z
  have hE : sysEffProb T S s s te' = sysEffProb T S s s te :=
    sysEffProb_congr fun j hj => hagree j hj
  have hP : sysPartEffProb T S s θ s te' = ∏ j ∈ S, effUnit T (profile θ j)ᶜ s j (te j) := by
    unfold sysPartEffProb
    rw [merge_self]
    exact prod_congr rfl fun j hj => by rw [hagree j hj]; rfl
  have he : sysEffProb T S s s te = ∏ j ∈ S, T.prob j s (te j) := tp_eff_eq T S s te
  have hfac : ∀ j ∈ S, effUnit T (profile θ j)ᶜ s j (te j) ≤ T.prob j s (te j) := by
    intro j hj
    rcases (profile θ j).eq_empty_or_nonempty with h0 | hne
    · rw [h0, compl_empty, effUnit_univ_prob]
    · have := hcut j hj (profile θ j) (cutSet_partOf_subset θ hj) hne
      have hx0 := T.nonneg j s (te j)
      nlinarith
  have hpos : ∀ j ∈ S, 0 < effUnit T (profile θ j)ᶜ s j (te j) := fun j _ =>
    effUnit_pos hz _ _ _ _
  obtain ⟨p, hp, hne⟩ := θ.exists_cutSet_nonempty
  obtain ⟨j0, hj0p⟩ := θ.parts_nonempty p hp
  have hj0 : j0 ∈ S := θ.parts_subset p hp hj0p
  have hprof0 : profile θ j0 = θ.cutSet p := by unfold profile; rw [θ.partOf_eq hp hj0p]
  have hPle : sysPartEffProb T S s θ s te' ≤ lam * sysEffProb T S s s te := by
    rw [hP, he, ← mul_prod_erase S _ hj0, ← mul_prod_erase S (fun j => T.prob j s (te j)) hj0]
    have h0 := hcut j0 hj0 (profile θ j0) (cutSet_partOf_subset θ hj0) (hprof0 ▸ hne)
    have hr : ∏ j ∈ S.erase j0, effUnit T (profile θ j)ᶜ s j (te j) ≤
        ∏ j ∈ S.erase j0, T.prob j s (te j) :=
      prod_le_prod (fun j hj => (hpos j (mem_of_mem_erase hj)).le)
        fun j hj => hfac j (mem_of_mem_erase hj)
    have hr0 : 0 ≤ ∏ j ∈ S.erase j0, effUnit T (profile θ j)ᶜ s j (te j) :=
      prod_nonneg fun j hj => (hpos j (mem_of_mem_erase hj)).le
    calc effUnit T (profile θ j0)ᶜ s j0 (te j0) * ∏ j ∈ S.erase j0, effUnit T (profile θ j)ᶜ s j (te j)
        ≤ (lam * T.prob j0 s (te j0)) * ∏ j ∈ S.erase j0, T.prob j s (te j) :=
          mul_le_mul h0 hr hr0 (mul_nonneg hl0.le (T.nonneg j0 s _))
      _ = _ := by ring
  have hPpos : 0 < sysPartEffProb T S s θ s te' := by rw [hP]; exact prod_pos hpos
  have hepos : 0 < sysEffProb T S s s te := by
    have : 0 < lam * sysEffProb T S s s te := lt_of_lt_of_le hPpos hPle
    exact pos_of_mul_pos_right this hl0.le
  unfold sysPhiE
  rw [hE]
  refine mul_le_mul_of_nonneg_left ?_ hepos.le
  refine le_trans ?_ (le_max_right _ _)
  refine Real.logb_le_logb_of_le one_lt_two (by positivity) ?_
  rw [div_le_div_iff₀ hl0 hPpos]
  linarith

/-- **Lemma EF** (W2 7.4, `u ≠ tc`): with `x_j ≥ 1/2 + γ`, the entries of the other rows of the
`S`-block of `s` read by the cut factors (`r_j = s_j`) at most `ρ`, some factor `≤ ρ` in every
such row, and `3 (2^k - 1) 2^k ρ < 4 k γ` (`k = |S|`, e.g. `ρ ≤ γ/16` for `k ≤ 3`): every maximal
effect state agrees with `te` on `S`, and every partition has
`φ_e ≥ (1/2 + γ)^k (1 - 3ρ)`. -/
theorem eff_EF {z : Param N} (hz : z ∈ openCube N) (s : State N) {S : Finset (Fin N)}
    (te : State N) {γ ρ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1 / 2) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 4)
    (hx : ∀ j ∈ S, 1 / 2 + γ ≤ (tpmOf z).prob j s (te j))
    (hcutρ : ∀ r ∈ agree Sᶜ s, r ≠ s → ∀ j ∈ S, r j = s j → (tpmOf z).prob j r (te j) ≤ ρ)
    (hrowρ : ∀ r ∈ agree Sᶜ s, r ≠ s → ∃ j ∈ S, (tpmOf z).prob j r (te j) ≤ ρ)
    (hργ : 3 * ((2 : ℝ) ^ S.card - 1) * 2 ^ S.card * ρ < 4 * S.card * γ) :
    (∀ te' ∈ sysMaxEffStates (tpmOf z) S s s, ∀ j ∈ S, te' j = te j) ∧
    ∀ te' ∈ sysMaxEffStates (tpmOf z) S s s, ∀ θ : SysPartition N S,
      (1 / 2 + γ) ^ S.card * (1 - 3 * ρ) ≤ sysPhiE (tpmOf z) S s θ s te' := by
  set T := tpmOf z
  set k := S.card with hk
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hpow1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2' : 2 / 3 < Real.log 2 := by have := Real.log_two_gt_d9; norm_num at this; linarith
  have he : sysEffProb T S s s te = ∏ j ∈ S, T.prob j s (te j) := tp_eff_eq T S s te
  have hestar : (1 / 2 + γ) ^ k ≤ sysEffProb T S s s te := by
    rw [he, hk, ← prod_const]
    exact prod_le_prod (fun _ _ => by linarith) hx
  have hhalf : (1 / 2 : ℝ) ^ k ≤ (1 / 2 + γ) ^ k := pow_le_pow_left₀ (by norm_num) (by linarith) _
  have hepos : 0 < sysEffProb T S s s te := lt_of_lt_of_le (by positivity) (hhalf.trans hestar)
  -- the rest of the unconstrained probability
  set U0 := ((2 : ℝ) ^ k - 1) * ρ with hU0
  have hU : ∑ r ∈ (agree Sᶜ s).erase s, ∏ j ∈ S, T.prob j r (te j) ≤ U0 := by
    have hcardE : (((agree Sᶜ s).erase s).card : ℝ) = 2 ^ k - 1 := by
      rw [card_erase_of_mem (tp_mem_block s S), tp_card_block, Nat.cast_sub (Nat.one_le_two_pow)]
      push_cast; rfl
    have hs := sum_le_card_nsmul ((agree Sᶜ s).erase s) (fun r => ∏ j ∈ S, T.prob j r (te j)) ρ
      fun r hr => by
        obtain ⟨j0, hj0, hle⟩ := hrowρ r (mem_of_mem_erase hr) (ne_of_mem_erase hr)
        exact (tp_prod_le_one_factor (f := fun j => T.prob j r (te j))
          (fun j _ => T.nonneg j r _) (fun j _ => T.le_one j r _) hj0).trans hle
    rw [nsmul_eq_mul, hcardE] at hs
    exact hs
  -- the gap
  have hgap : (k : ℝ) * ((1 / 2 - γ) / (1 / 2 + γ)) <
      Real.logb 2 (2 ^ k * sysEffProb T S s s te / (sysEffProb T S s s te + U0)) := by
    set x := U0 / sysEffProb T S s s te with hx'
    have hx0 : 0 ≤ x := div_nonneg (by positivity) hepos.le
    have hxle : x ≤ U0 * 2 ^ k := by
      rw [hx', div_le_iff₀ hepos]
      have h2 : (1 : ℝ) ≤ 2 ^ k * sysEffProb T S s s te := by
        have := mul_le_mul_of_nonneg_left (hhalf.trans hestar) hpow.le
        rwa [← mul_pow, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow] at this
      have hU0nn : 0 ≤ U0 := mul_nonneg (by linarith) hρ0
      calc U0 = U0 * 1 := (mul_one _).symm
        _ ≤ U0 * (2 ^ k * sysEffProb T S s s te) := mul_le_mul_of_nonneg_left h2 hU0nn
        _ = _ := by ring
    have heq : 2 ^ k * sysEffProb T S s s te / (sysEffProb T S s s te + U0) =
        2 ^ k / (1 + x) := by
      rw [hx']; field_simp
    have hlogx : Real.log (1 + x) ≤ x := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + x); linarith
    have hlb : (k : ℝ) - x / Real.log 2 ≤
        Real.logb 2 (2 ^ k * sysEffProb T S s s te / (sysEffProb T S s s te + U0)) := by
      rw [heq, Real.logb, Real.log_div (by positivity) (by linarith), Real.log_pow]
      rw [sub_div, mul_div_assoc, div_self hlog2.ne', mul_one]
      have := div_le_div_of_nonneg_right hlogx hlog2.le
      linarith
    have hxl : x / Real.log 2 ≤ 3 / 2 * x := by
      rw [div_le_iff₀ hlog2]; nlinarith
    have hr : (1 / 2 - γ) / (1 / 2 + γ) ≤ 1 - 2 * γ := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : (k : ℝ) * ((1 / 2 - γ) / (1 / 2 + γ)) ≤ k - 2 * k * γ := by
      have := mul_le_mul_of_nonneg_left hr hk0; linarith
    have h3 : 3 / 2 * (U0 * 2 ^ k) < 2 * k * γ := by
      rw [hU0]; nlinarith
    linarith
  have hagree := eff_te_agree (z := z) s te hγ hγ1 hx hU hgap
  refine ⟨hagree, fun te' hte' θ => ?_⟩
  -- the cut factors
  have hcut : ∀ j ∈ S, ∀ C ⊆ S.erase j, C.Nonempty →
      effUnit T Cᶜ s j (te j) ≤ (1 + 2 * ρ) / 2 * T.prob j s (te j) := by
    intro j hj C hC hCne
    have hCS : C ⊆ S := hC.trans (erase_subset j S)
    have hjC : j ∉ C := fun h => (mem_erase.1 (hC h)).1 rfl
    have hsub : agree Cᶜ s ⊆ agree Sᶜ s := agree_subset_agree (compl_subset_compl.2 hCS) s
    have hmem : s ∈ agree Cᶜ s := self_mem_agree _ _
    have hcard : ((agree Cᶜ s).card : ℝ) = 2 ^ C.card := by
      rw [tp_card_block]; push_cast; rfl
    have hm2 : (2 : ℝ) ≤ 2 ^ C.card := by
      have : 1 ≤ C.card := card_pos.2 hCne
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ C.card := pow_le_pow_right₀ (by norm_num) this
    have hrest : ∑ r ∈ (agree Cᶜ s).erase s, T.prob j r (te j) ≤ (2 ^ C.card - 1) * ρ := by
      have hs := sum_le_card_nsmul ((agree Cᶜ s).erase s) (fun r => T.prob j r (te j)) ρ
        fun r hr => hcutρ r (hsub (mem_of_mem_erase hr)) (ne_of_mem_erase hr) j hj
          ((mem_agree.1 (mem_of_mem_erase hr)) j (mem_compl.2 hjC))
      rw [nsmul_eq_mul, card_erase_of_mem hmem, Nat.cast_sub (card_pos.2 ⟨s, hmem⟩), hcard] at hs
      push_cast at hs
      exact hs
    have hxj := hx j hj
    have hx1 := T.le_one j s (te j)
    rw [effUnit, hcard, ← sum_erase_add _ _ hmem, div_le_iff₀ (by positivity)]
    have hρx : ρ ≤ T.prob j s (te j) := by linarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 ^ C.card / 2 - 1) (by linarith : (0 : ℝ) ≤
      T.prob j s (te j) - ρ), mul_nonneg hρ0 (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 ^ C.card)
        (by linarith : (0 : ℝ) ≤ T.prob j s (te j) - 1 / 2))]
  have hl0 : 0 < (1 + 2 * ρ) / 2 := by linarith
  have hl1 : (1 + 2 * ρ) / 2 ≤ 1 := by linarith
  have hphi := eff_phiE_ge hz s te te' (hagree te' hte') hl0 hl1 hcut θ
  have hlog : 1 - 3 * ρ ≤ Real.logb 2 (1 / ((1 + 2 * ρ) / 2)) := by
    rw [show 1 / ((1 + 2 * ρ) / 2) = 2 / (1 + 2 * ρ) by field_simp, Real.logb,
      Real.log_div (by norm_num) (by linarith), sub_div, div_self hlog2.ne']
    have h1 : Real.log (1 + 2 * ρ) ≤ 2 * ρ := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + 2 * ρ); linarith
    have h2 : Real.log (1 + 2 * ρ) / Real.log 2 ≤ 3 * ρ := by
      rw [div_le_iff₀ hlog2]
      have hl0' : 0 ≤ Real.log (1 + 2 * ρ) := Real.log_nonneg (by linarith)
      nlinarith
    linarith
  have h13 : 0 ≤ 1 - 3 * ρ := by linarith
  calc (1 / 2 + γ) ^ k * (1 - 3 * ρ) ≤ sysEffProb T S s s te * (1 - 3 * ρ) :=
        mul_le_mul_of_nonneg_right hestar h13
    _ ≤ sysEffProb T S s s te * Real.logb 2 (1 / ((1 + 2 * ρ) / 2)) :=
        mul_le_mul_of_nonneg_left hlog hepos.le
    _ ≤ _ := hphi

end Effect

end Census
end IIT
