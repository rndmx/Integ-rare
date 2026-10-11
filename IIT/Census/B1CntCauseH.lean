/-
Census, B1, W14 work package WP2 (cause side), part 4 (sub-package 2B, first half): the competitors
`(h2)` (small purviews) and `(h3)` (near-full purviews at the `r0`-pattern).

* `cs_phiCat_le_rep`: `φ_c(Z, z) ≤ causeRep(Z, z) · |M||Z|` (total cut, W5 (V1'));
* `cs_causeRep_le`: the FE5 normaliser bound;
* `cs_cutOne`: the partition cutting one unit fully, and `cs_phiCat_eq_zero_of`;
* `cs_phiCat_h2` (W5 (h2), FE1'), `cs_phiCat_h3` (W5 (h3), W13-cause G1/G2: `pairLow` kills
  `Z = U \ {x}` on the cause side; otherwise the small-cut sums of `B1CntCauseCut`).
Numeric inputs are explicit hypotheses.  Blueprint: `iit-census/lean/B1-W14-count-lean.md` §7.
No `sorry`.
-/
import IIT.Census.B1CntCauseCP

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### Generic upper bounds -/

theorem cs_phiCat_le_rep (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N) (M : Finset (Fin N))
    (m : State N) (hM : M.Nonempty) (hZ : Z.Nonempty)
    (hpos : 0 < partCauseFwd T Z z M m (Partition.total hM Z)) :
    phiCat T Z z M m ≤ causeRep T Z z M m * (M.card * Z.card) := by
  refine (cs_phiCat_le_total T Z z M m hM hZ).trans ?_
  unfold phiCofPartition
  refine mul_le_mul_of_nonneg_left ?_ (causeRep_nonneg _ _ _ _ _)
  have := logb_ratio_le_cutCount_cause T Z z M m _ hpos
  rw [cutCount_total] at this
  exact_mod_cast this

lemma cs_partCauseFwd_total_pos {w : Param N} (hw : w ∈ openCube N) (s : State N)
    (Z : Finset (Fin N)) (z : State N) (M : Finset (Fin N)) (hM : M.Nonempty) :
    0 < partCauseFwd (tpmOf (flipP s w)) Z z M s (Partition.total hM Z) := by
  rw [cs_partCauseFwd_eq]; exact prod_pos fun i _ => cs_subMean_pos hw _ z i

theorem cs_causeRep_le (s : State N) (w : Param N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) {B : ℝ} (hB : 0 < B)
    (hunc : B ≤ (∑ z' : State N, ∏ i ∈ M, subMean w Z z' i) / 2 ^ N) :
    causeRep (tpmOf (flipP s w)) Z z M s ≤ (∏ i ∈ M, subMean w Z z i) / (2 ^ Z.card * B) := by
  unfold causeRep uncCauseFwd avgOverStates
  simp only [cs_causeFwd_eq]
  refine div_le_div_of_nonneg_left (prod_nonneg fun i _ => ?_) (by positivity) ?_
  · unfold subMean; exact div_nonneg (sum_nonneg fun r _ => clamp01_nonneg _) (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left hunc (by positivity)

/-! ### Cutting one unit -/

/-- The partition `{({j}, ∅), (M \ {j}, Z)}`. -/
def cs_cutOne {M : Finset (Fin N)} (Z : Finset (Fin N)) {j : Fin N} (hj : j ∈ M) :
    Partition N M Z where
  blocks := {({j}, ∅), (M.erase j, Z)}
  mech_subset := by
    intro b hb; simp only [mem_insert, mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact singleton_subset_iff.2 hj
    · exact erase_subset _ _
  purv_subset := by
    intro b hb; simp only [mem_insert, mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact empty_subset _
    · exact subset_rfl
  mech_disjoint := by
    intro b hb b' hb' hne
    simp only [mem_insert, mem_singleton] at hb hb'
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · exact disjoint_singleton_left.2 (notMem_erase j M)
    · exact disjoint_singleton_right.2 (notMem_erase j M)
    · exact absurd rfl hne
  purv_disjoint := by
    intro b hb b' hb' hne
    simp only [mem_insert, mem_singleton] at hb hb'
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · exact disjoint_empty_left _
    · exact disjoint_empty_right _
    · exact absurd rfl hne
  mech_cover := fun i hi => by
    by_cases h : i = j
    · exact ⟨({j}, ∅), mem_insert_self _ _, by simp [h]⟩
    · exact ⟨(M.erase j, Z), mem_insert_of_mem (mem_singleton_self _), mem_erase.2 ⟨h, hi⟩⟩
  purv_cover := fun k hk => ⟨(M.erase j, Z), mem_insert_of_mem (mem_singleton_self _), hk⟩
  proper := by
    intro b hb h1
    simp only [mem_insert, mem_singleton] at hb
    rcases hb with rfl | rfl
    · rfl
    · have h1' : M.erase j = M := h1
      have : j ∈ M.erase j := by rw [h1']; exact hj
      exact absurd this (notMem_erase j M)

lemma cs_cutOne_causePart_self {M : Finset (Fin N)} (Z : Finset (Fin N)) {j : Fin N} (hj : j ∈ M) :
    (cs_cutOne Z hj).causePart j = ∅ :=
  (cs_cutOne Z hj).causePart_eq (b := ({j}, ∅)) (mem_insert_self _ _) (mem_singleton_self j)

lemma cs_cutOne_causePart_other {M : Finset (Fin N)} (Z : Finset (Fin N)) {j : Fin N} (hj : j ∈ M)
    {i : Fin N} (hi : i ∈ M) (hij : i ≠ j) : (cs_cutOne Z hj).causePart i = Z :=
  (cs_cutOne Z hj).causePart_eq (b := (M.erase j, Z)) (mem_insert_of_mem (mem_singleton_self _))
    (mem_erase.2 ⟨hij, hi⟩)

lemma cs_phiCat_eq_zero_of (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N) (M : Finset (Fin N))
    (m : State N) (hZ : Z.Nonempty) (θ0 : Partition N M Z)
    (h0 : phiCofPartition T Z z M m θ0 = 0) : phiCat T Z z M m = 0 := by
  refine le_antisymm (sup'OrZero_le le_rfl fun θ hθ => ?_)
    (sup'OrZero_nonneg fun θ _ => phiCofPartition_nonneg _ _ _ _ _ _)
  have hmin := (mem_argminSet.1 hθ) θ0
  unfold normalizedPhiC at hmin
  rw [h0, zero_div] at hmin
  have hcc : (0 : ℝ) < cutCount M Z θ := Nat.cast_pos.2 (cutCount_pos hZ θ)
  have := (div_le_iff₀ hcc).1 hmin
  rwa [zero_mul] at this

/-! ### `(h2)`: small purviews -/

lemma cs_two_pow_JC_gt (hN : 1 ≤ N) : 1024 * (N : ℝ) ^ 6 < 2 ^ JC N := by
  have h := cs_lt_two_pow_natLog N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (2 : ℝ) ^ JC N = 2 ^ 16 * (2 ^ Nat.log 2 N) ^ 6 := by
    unfold JC; rw [← pow_mul, ← pow_add]; ring_nf
  rw [e]
  have h6 : (N : ℝ) ^ 6 < (2 * 2 ^ Nat.log 2 N) ^ 6 := pow_lt_pow_left₀ h hN0.le (by norm_num)
  nlinarith [h6]

/-- FE1' deviation at dimension `D > J` is at most `1/N²`. -/
lemma cs_delta_le_inv_sq (hN : 1 ≤ N) {D : ℕ} (hD : JC N < D) (hDN : D ≤ N) :
    2 * Real.sqrt ((N : ℝ) / 2 ^ D) + 2 * ((D + 1 : ℕ) : ℝ) ^ 4 / 2 ^ D ≤ 1 / (N : ℝ) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hJ := cs_two_pow_JC_gt hN
  have h2D : 2048 * (N : ℝ) ^ 6 ≤ 2 ^ D := by
    have : (2 : ℝ) ^ (JC N + 1) ≤ 2 ^ D := pow_le_pow_right₀ (by norm_num) hD
    rw [pow_succ] at this; linarith
  have h2Dpos : (0 : ℝ) < 2 ^ D := by positivity
  have hN6 : 0 < (N : ℝ) ^ 6 := by positivity
  -- the square-root term
  have hs : Real.sqrt ((N : ℝ) / 2 ^ D) ≤ 1 / (4 * (N : ℝ) ^ 2) := by
    rw [show 1 / (4 * (N : ℝ) ^ 2) = Real.sqrt ((1 / (4 * (N : ℝ) ^ 2)) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ h2Dpos, div_pow, one_pow]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hN1 5]
  -- the polynomial term
  have hD1 : ((D + 1 : ℕ) : ℝ) ≤ 2 * N := by
    have : (D : ℝ) ≤ N := by exact_mod_cast hDN
    push_cast; linarith
  have hp : 2 * ((D + 1 : ℕ) : ℝ) ^ 4 / 2 ^ D ≤ 1 / (64 * (N : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ h2Dpos (by positivity)]
    have h4 : ((D + 1 : ℕ) : ℝ) ^ 4 ≤ (2 * N) ^ 4 := pow_le_pow_left₀ (by positivity) hD1 4
    nlinarith
  have : 2 * (1 / (4 * (N : ℝ) ^ 2)) + 1 / (64 * (N : ℝ) ^ 2) ≤ 1 / (N : ℝ) ^ 2 := by
    field_simp; norm_num
  linarith

/-- FE1' deviation divided by the number `2^{|Z|}` of purview patterns. -/
lemma cs_delta_scaled (N z : ℕ) (hz : z ≤ N) :
    (2 * Real.sqrt ((N : ℝ) / 2 ^ (N - z)) + 2 * ((N - z + 1 : ℕ) : ℝ) ^ 4 / 2 ^ (N - z)) / 2 ^ z ≤
      2 * Real.sqrt ((N : ℝ) / 2 ^ N) + 2 * ((N : ℝ) + 1) ^ 4 / 2 ^ N := by
  have hz2 : (0 : ℝ) < 2 ^ z := by positivity
  have hsplit : (2 : ℝ) ^ (N - z) * 2 ^ z = 2 ^ N := by rw [← pow_add, Nat.sub_add_cancel hz]
  rw [add_div]
  refine add_le_add ?_ ?_
  · rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [show Real.sqrt ((N : ℝ) / 2 ^ (N - z)) / 2 ^ z =
        Real.sqrt ((N : ℝ) / 2 ^ (N - z) / (2 ^ z) ^ 2) by
      rw [Real.sqrt_div (by positivity : (0:ℝ) ≤ (N : ℝ) / 2 ^ (N - z)) ((2 ^ z) ^ 2),
        Real.sqrt_sq hz2.le]]
    refine Real.sqrt_le_sqrt ?_
    rw [div_div]
    refine div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity) ?_
    rw [sq, ← mul_assoc, hsplit]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
  · rw [div_div, hsplit]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have : ((N - z + 1 : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by
      push_cast [Nat.cast_sub hz]; have := Nat.cast_nonneg (α := ℝ) z; linarith
    nlinarith [pow_le_pow_left₀ (Nat.cast_nonneg _) this 4]

/-- **`(h2)`** (W5 (h2), Phi level): `φ_c(Z, z) ≤ 12 N (η + ε)` for `|Z| + J < N`. -/
theorem cs_phiCat_h2 {s : State N} {w : Param N} (hw : w ∈ openCube N) (K : Finset (Fin N))
    (hMne : (univ \ K).Nonempty) (hN : 12 ≤ N)
    {Z : Finset (Fin N)} (z : State N) (hZ : Z.Nonempty) (_hZJ : Z.card + JC N < N)
    {δ ε η : ℝ} (hsubZ : ∀ (t : State N) (i : Fin N), |subMean w Z t i - 1 / 2| ≤ δ)
    (hδ : δ ≤ 1 / (N : ℝ) ^ 2) (hδZ : δ / 2 ^ Z.card ≤ η)
    (hcol : ∀ (t : State N) (i : Fin N), |subMean w ∅ t i - 1 / 2| ≤ ε) (hε : ε ≤ 1 / 4) :
    phiCat (tpmOf (flipP s w)) Z z (univ \ K) s ≤ 12 * N * (η + ε) := by
  set M := univ \ K with hMdef
  set T := tpmOf (flipP s w)
  have hNr : (12 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) (hsubZ z ⟨0, by omega⟩)
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hcol z ⟨0, by omega⟩)
  have hδs : δ ≤ 1 / 144 := by
    refine hδ.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hMc : (M.card : ℝ) ≤ N := by exact_mod_cast (card_le_univ M).trans (by simp)
  have hA : ∀ t i, subMean w Z t i ≤ 1 / 2 + δ ∧ 1 / 2 - δ ≤ subMean w Z t i := fun t i =>
    ⟨by linarith [(abs_le.1 (hsubZ t i)).2], by linarith [(abs_le.1 (hsubZ t i)).1]⟩
  -- the selectivity
  have hrep : causeRep T Z z M s ≤ 2 / 2 ^ Z.card := by
    have hB : (0 : ℝ) < (1 / 2 - δ) ^ M.card := by apply pow_pos; linarith
    have hunc : (1 / 2 - δ) ^ M.card ≤ (∑ z' : State N, ∏ i ∈ M, subMean w Z z' i) / 2 ^ N := by
      rw [le_div_iff₀ (by positivity)]
      calc (1 / 2 - δ) ^ M.card * 2 ^ N = ∑ _z' : State N, (1 / 2 - δ) ^ M.card := by
            rw [sum_const, card_state, nsmul_eq_mul]; push_cast; ring
        _ ≤ ∑ z' : State N, ∏ i ∈ M, subMean w Z z' i := by
            refine sum_le_sum fun z' _ => ?_
            rw [← prod_const]
            exact prod_le_prod (fun _ _ => by linarith) fun i _ => (hA z' i).2
    refine (cs_causeRep_le s w Z z M hB hunc).trans ?_
    have hcf : ∏ i ∈ M, subMean w Z z i ≤ (1 / 2 + δ) ^ M.card := by
      rw [← prod_const]
      exact prod_le_prod (fun i _ => (cs_subMean_pos hw Z z i).le) fun i _ => (hA z i).1
    have hR : (1 / 2 + δ) ^ M.card ≤ 2 * (1 / 2 - δ) ^ M.card := by
      have h1 : 1 / 2 + δ ≤ (1 / 2 - δ) * (1 + 8 * δ) := by nlinarith
      have h2 : (1 + 8 * δ) ^ M.card ≤ 2 := by
        calc (1 + 8 * δ) ^ M.card ≤ Real.exp (8 * δ) ^ M.card :=
              pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (8 * δ)]) _
          _ = Real.exp (M.card * (8 * δ)) := by rw [← Real.exp_nat_mul]
          _ ≤ Real.exp (8 / N) := by
              refine Real.exp_le_exp.2 ?_
              calc (M.card : ℝ) * (8 * δ) ≤ N * (8 * (1 / (N : ℝ) ^ 2)) := by
                    apply mul_le_mul hMc (by linarith) (by positivity) hNpos.le
                _ = 8 / N := by field_simp
          _ ≤ 2 := by
              have : 8 / (N : ℝ) ≤ Real.log 2 := by
                rw [div_le_iff₀ hNpos]; nlinarith [cs_log_two_gt]
              calc Real.exp (8 / N) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 this
                _ = 2 := Real.exp_log (by norm_num)
      calc (1 / 2 + δ) ^ M.card ≤ ((1 / 2 - δ) * (1 + 8 * δ)) ^ M.card :=
            pow_le_pow_left₀ (by linarith) h1 _
        _ = (1 / 2 - δ) ^ M.card * (1 + 8 * δ) ^ M.card := mul_pow _ _ _
        _ ≤ (1 / 2 - δ) ^ M.card * 2 := mul_le_mul_of_nonneg_left h2 hB.le
        _ = 2 * (1 / 2 - δ) ^ M.card := by ring
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc (∏ i ∈ M, subMean w Z z i) * 2 ^ Z.card ≤ (2 * (1 / 2 - δ) ^ M.card) * 2 ^ Z.card :=
          mul_le_mul_of_nonneg_right (hcf.trans hR) (by positivity)
      _ = 2 * (2 ^ Z.card * (1 / 2 - δ) ^ M.card) := by ring
  -- the log-ratio of the total cut
  have hLR : pos (Real.logb 2 (causeFwd T Z z M s / partCauseFwd T Z z M s
      (Partition.total hMne Z))) ≤ 6 * N * (δ + ε) := by
    refine pos_le (by positivity) ?_
    rw [cs_causeFwd_eq, cs_partCauseFwd_eq, ← prod_div_distrib, Real.logb, Real.log_prod]
    · rw [div_le_iff₀ (Real.log_pos (by norm_num))]
      have hterm : ∀ i ∈ M, Real.log (subMean w Z z i /
          subMean w ((Partition.total hMne Z).causePart i) z i) ≤ 4 * (δ + ε) := by
        intro i hi
        rw [cs_causePart_total hMne hi]
        have ha := cs_subMean_pos hw ∅ z i
        have hb := (abs_le.1 (hcol z i)).1
        have hb' := (abs_le.1 (hcol z i)).2
        refine (Real.log_le_sub_one_of_pos (div_pos (cs_subMean_pos hw Z z i) ha)).trans ?_
        rw [div_sub_one ha.ne', div_le_iff₀ ha]
        have hde : 0 ≤ δ + ε := by linarith
        nlinarith [(hA z i).1, mul_nonneg hde (by linarith : (0:ℝ) ≤ subMean w ∅ z i - 1 / 4)]
      calc ∑ i ∈ M, Real.log (subMean w Z z i /
            subMean w ((Partition.total hMne Z).causePart i) z i) ≤ ∑ _i ∈ M, 4 * (δ + ε) :=
            sum_le_sum hterm
        _ = M.card * (4 * (δ + ε)) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ 6 * N * (δ + ε) * Real.log 2 := by
            have := cs_log_two_gt
            have hde : 0 ≤ δ + ε := by linarith
            have h1 := mul_le_mul_of_nonneg_right hMc (by linarith : (0:ℝ) ≤ 4 * (δ + ε))
            have h2 : 0 ≤ (N : ℝ) * (δ + ε) * (6 * Real.log 2 - 4) :=
              mul_nonneg (mul_nonneg hNpos.le hde) (by linarith)
            nlinarith
    · intro i _
      exact (div_pos (cs_subMean_pos hw Z z i) (cs_subMean_pos hw _ z i)).ne'
  -- combine
  have htot := cs_phiCat_le_total T Z z M s hMne hZ
  unfold phiCofPartition at htot
  have hZ2 : (1 : ℝ) ≤ 2 ^ Z.card := one_le_pow₀ (by norm_num)
  calc phiCat T Z z M s ≤ causeRep T Z z M s * pos (Real.logb 2 (causeFwd T Z z M s /
        partCauseFwd T Z z M s (Partition.total hMne Z))) := htot
    _ ≤ (2 / 2 ^ Z.card) * (6 * N * (δ + ε)) :=
        mul_le_mul hrep hLR (pos_nonneg _) (by positivity)
    _ = 12 * N * (δ / 2 ^ Z.card + ε / 2 ^ Z.card) := by ring
    _ ≤ 12 * N * (η + ε) := by
        refine mul_le_mul_of_nonneg_left (add_le_add hδZ ?_) (by positivity)
        exact div_le_self hε0 hZ2

/-! ### `(h3)`: near-full purviews at the `r0`-pattern -/

lemma cs_arith_lt {P e n Y X D G a : ℝ} (hP : 0 < P) (hX : 0 < X) (hD : 0 < D) (hen : 0 ≤ e * n)
    (hYD : Y * D ≤ X * G) (hk : e * n * G < a) : P * e * n * Y / X < P * a / D := by
  rw [div_lt_div_iff₀ hX hD]
  calc P * e * n * Y * D = P * (e * n) * (Y * D) := by ring
    _ ≤ P * (e * n) * (X * G) := mul_le_mul_of_nonneg_left hYD (mul_nonneg hP.le hen)
    _ = P * X * (e * n * G) := by ring
    _ < P * X * a := mul_lt_mul_of_pos_left hk (mul_pos hP hX)
    _ = P * a * X := by ring

/-- The selectivity at `(univ, r0)` against the row product `P_M(r0)`. -/
lemma cs_causeRep_univ_ge_PM {s r0 : State N} {w : Param N} (hw : w ∈ openCube N)
    (hfr : CountFreshX N s r0 w) (hsens : 2 * ((N : ℝ) + 1) ^ 4 ≤ 2 ^ (dX N + 1))
    {K : Finset (Fin N)} (hK : K.card = dX N) :
    (∏ i ∈ univ \ K, clamp01 (w r0 i)) / 2 ^ (dX N + 2) ≤
      causeRep (tpmOf (flipP s w)) univ r0 (univ \ K) s := by
  rw [cs_causeRep_univ_eq]
  simp only [cs_causeFwd_univ_eq]
  have hpos : 0 < ∑ t : State N, ∏ i ∈ univ \ K, clamp01 (w t i) :=
    sum_pos (fun t _ => prod_pos fun i _ => cs_clamp_pos hw t i) ⟨r0, mem_univ _⟩
  exact div_le_div_of_nonneg_left (prod_nonneg fun i _ => clamp01_nonneg _) hpos
    (cs_normC w hfr hsens hK)

/-- `∏_M Ā_i(C_{K'}(r0)) ≤ P_M(r0) · exp(-Σ_M g_i(K'))`. -/
lemma cs_prod_le_exp {w : Param N} (hw : w ∈ openCube N) (r0 : State N) (M K' : Finset (Fin N)) :
    ∏ i ∈ M, subMean w K'ᶜ r0 i ≤
      (∏ i ∈ M, clamp01 (w r0 i)) * Real.exp (-∑ i ∈ M, csG w r0 K' i) := by
  rw [← sum_neg_distrib, Real.exp_sum, ← prod_mul_distrib]
  refine prod_le_prod (fun i _ => (cs_subMean_pos hw _ r0 i).le) fun i _ => ?_
  have hy := cs_clamp_pos hw r0 i
  have hA := cs_subMean_pos hw K'ᶜ r0 i
  have h1 : subMean w K'ᶜ r0 i =
      clamp01 (w r0 i) * Real.exp (-Real.log (clamp01 (w r0 i) / subMean w K'ᶜ r0 i)) := by
    rw [Real.exp_neg, Real.exp_log (div_pos hy hA)]; field_simp
  rw [h1]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hy.le
  have : csG w r0 K' i ≤ Real.log (clamp01 (w r0 i) / subMean w K'ᶜ r0 i) := min_le_left _ _
  linarith

/-- **`(h3)`** (W5 (h3), W7 4.3 (iv), W13-cause G1/G2; Phi level). -/
theorem cs_phiCat_h3 {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    (hg : GoodW3 N s r0 x σ w) (hfr : CountFreshX N s r0 w) (hw : w ∈ openCube N)
    {K : Finset (Fin N)} (hK : K ∈ famX3 N s r0 x σ w)
    (hN : 10000 ≤ N) (hslT : slT N ≤ N / 1000) (ha : Real.exp (-((N : ℝ) / 200)) ≤ 1 / 2000)
    (hεN : epsN N < 1 / (2 * N)) (hJ3 : 3 * JC N + 3 < N)
    (hsens : 2 * ((N : ℝ) + 1) ^ 4 ≤ 2 ^ (dX N + 1))
    (hcol : ∀ (t : State N) (i : Fin N), |subMean w ∅ t i - 1 / 2| ≤ epsN N)
    (hH3 : (N : ℝ) ^ 2 * 2 ^ (JC N + 4) * Real.exp (-((N : ℝ) / 100)) <
      Real.exp (-((N : ℝ) / 200)))
    {Z : Finset (Fin N)} (z : State N) (hZu : Z ≠ univ) (hZJ : N ≤ Z.card + JC N)
    (hzr : ∀ i ∈ Z, z i = r0 i) :
    phiCat (tpmOf (flipP s w)) Z z (univ \ K) s <
      causeRep (tpmOf (flipP s w)) univ r0 (univ \ K) s * Real.exp (-((N : ℝ) / 200)) := by
  set a := Real.exp (-((N : ℝ) / 200)) with hadef
  have hapos : 0 < a := Real.exp_pos _
  have hKc := famX3_card hK
  have hNr : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hdN : dX N ≤ N := cs_dX_le_N (by omega)
  have hMne : (univ \ K).Nonempty := by
    rw [← card_pos, cs_card_M hKc]
    have := cs_dX_le N
    have h1 : dX N < N := by
      have : (dX N : ℝ) < N := by linarith
      exact_mod_cast this
    omega
  have hZc : Z.card < N := by
    have := card_lt_card ((subset_univ Z).ssubset_of_ne hZu); simpa using this
  have hZne : Z.Nonempty := by
    rw [← card_pos]; unfold JC at hJ3 hZJ; omega
  have hPM : 0 < ∏ i ∈ univ \ K, clamp01 (w r0 i) := prod_pos fun i _ => cs_clamp_pos hw r0 i
  have hRHS : (∏ i ∈ univ \ K, clamp01 (w r0 i)) * a / 2 ^ (dX N + 2) ≤
      causeRep (tpmOf (flipP s w)) univ r0 (univ \ K) s * a := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right (cs_causeRep_univ_ge_PM hw hfr hsens hKc) hapos.le
  have hRHSpos : 0 < causeRep (tpmOf (flipP s w)) univ r0 (univ \ K) s * a :=
    lt_of_lt_of_le (by positivity) hRHS
  by_cases hc : σ = .cause ∧ Z = ({x} : Finset (Fin N))ᶜ
  · -- `pairLow`: one unit's full cut has a negative log-ratio
    obtain ⟨hσ, hZx⟩ := hc
    obtain ⟨j, hjx, hjfl, hjpair⟩ := hg.2.pairLow hσ
    have hU := cs_clamp_pos hw (flipAt x r0) j
    have hjM : j ∈ univ \ K := by
      refine mem_sdiff.2 ⟨mem_univ _, fun hjK => ?_⟩
      subst hσ
      rcases mem_union.1 (famX3_cause_sub hK hjK) with hn | hl
      · simp only [NegX, mem_filter] at hn
        have h1 : (1 : ℝ) / N > 0 := by positivity
        linarith [hn.2]
      · simp only [lowU, mem_filter, mem_univ, true_and] at hl
        linarith
    refine lt_of_eq_of_lt (cs_phiCat_eq_zero_of _ Z z _ s hZne (cs_cutOne Z hjM) ?_) hRHSpos
    unfold phiCofPartition
    have hle : Real.logb 2 (causeFwd (tpmOf (flipP s w)) Z z (univ \ K) s /
        partCauseFwd (tpmOf (flipP s w)) Z z (univ \ K) s (cs_cutOne Z hjM)) ≤ 0 := by
      have hQ : 0 < ∏ i ∈ (univ \ K).erase j, subMean w Z z i :=
        prod_pos fun i _ => cs_subMean_pos hw _ z i
      have hnum : ∏ i ∈ univ \ K, subMean w Z z i =
          subMean w Z z j * ∏ i ∈ (univ \ K).erase j, subMean w Z z i :=
        (mul_prod_erase _ _ hjM).symm
      have hden : ∏ i ∈ univ \ K, subMean w ((cs_cutOne Z hjM).causePart i) z i =
          subMean w ∅ z j * ∏ i ∈ (univ \ K).erase j, subMean w Z z i := by
        rw [← mul_prod_erase _ _ hjM, cs_cutOne_causePart_self]
        refine congrArg (subMean w ∅ z j * ·) ?_
        exact prod_congr rfl fun i hi => by
          rw [cs_cutOne_causePart_other Z hjM (mem_of_mem_erase hi) (ne_of_mem_erase hi)]
      rw [cs_causeFwd_eq, cs_partCauseFwd_eq, hnum, hden]
      have hAj : subMean w Z z j ≤ subMean w ∅ z j := by
        have e1 : subMean w Z z j = subMean w Z r0 j := by
          unfold subMean; rw [agree_congr hzr]
        rw [e1, hZx, cs_subMean_pair]
        have hcj := (abs_le.1 (hcol z j)).1
        have : (1 : ℝ) / (2 * N) = 1 / 2 * (1 / N) := by field_simp
        linarith
      have hD : 0 < subMean w ∅ z j * ∏ i ∈ (univ \ K).erase j, subMean w Z z i :=
        mul_pos (cs_subMean_pos hw _ z j) hQ
      refine Real.logb_nonpos (by norm_num)
        (div_nonneg (mul_pos (cs_subMean_pos hw _ z j) hQ).le hD.le) ?_
      rw [div_le_one hD]
      exact mul_le_mul_of_nonneg_right hAj hQ.le
    rw [show pos (Real.logb 2 (causeFwd (tpmOf (flipP s w)) Z z (univ \ K) s /
        partCauseFwd (tpmOf (flipP s w)) Z z (univ \ K) s (cs_cutOne Z hjM))) = 0 from
      max_eq_left hle, mul_zero]
  · -- the small-cut sums of `K'' = Zᶜ`
    set K'' := Zᶜ with hK''
    have hZK : Z = K''ᶜ := by rw [hK'', compl_compl]
    have hK''ne : K''.Nonempty := by
      obtain ⟨k, hk⟩ : ∃ k, k ∉ Z := by
        by_contra h; push Not at h; exact hZu (eq_univ_of_forall h)
      exact ⟨k, by rw [hK'']; exact mem_compl.2 hk⟩
    have hK''c : K''.card = N - Z.card := by rw [hK'', card_compl, Fintype.card_fin]
    have hJ : K''.card ≤ JC N := by rw [hK''c]; omega
    have hfar : 3 * K''.card + 3 < N := by rw [hK''c]; omega
    have hnot : ¬ (σ = .cause ∧ K'' = {x}) := by
      rintro ⟨hσ, hx⟩; exact hc ⟨hσ, by rw [hZK, hx]⟩
    have hsc := (cs_smallCut hg hfr hw hK hN hslT (ha.trans (by norm_num)) hK''ne hJ hfar).2 hnot
    -- the forward term
    have hcf : causeFwd (tpmOf (flipP s w)) Z z (univ \ K) s ≤
        (∏ i ∈ univ \ K, clamp01 (w r0 i)) * Real.exp (-((N : ℝ) / 100)) := by
      rw [cs_causeFwd_eq]
      have e1 : ∀ i, subMean w Z z i = subMean w K''ᶜ r0 i := fun i => by
        unfold subMean; rw [agree_congr hzr, hZK]
      simp only [e1]
      refine (cs_prod_le_exp hw r0 _ K'').trans (mul_le_mul_of_nonneg_left ?_ hPM.le)
      exact Real.exp_le_exp.2 (by linarith)
    -- FE5
    have hB : (0 : ℝ) < 1 / 2 ^ (N - dX N + 2) := by positivity
    have hunc := hfr.fe5 K hKc Z hZJ hZc
    have hrep := cs_causeRep_le s w Z z (univ \ K) hB hunc
    have hle := cs_phiCat_le_rep (tpmOf (flipP s w)) Z z (univ \ K) s hMne hZne
      (cs_partCauseFwd_total_pos hw s Z z _ hMne)
    have hMZ : ((univ \ K).card : ℝ) * Z.card ≤ (N : ℝ) ^ 2 := by
      have h1 : ((univ \ K).card : ℝ) ≤ N := by exact_mod_cast (card_le_univ _).trans (by simp)
      have h2 : (Z.card : ℝ) ≤ N := by exact_mod_cast hZc.le
      nlinarith [Nat.cast_nonneg (α := ℝ) Z.card]
    have hrep0 := causeRep_nonneg (tpmOf (flipP s w)) Z z (univ \ K) s
    have hstep : phiCat (tpmOf (flipP s w)) Z z (univ \ K) s ≤
        (∏ i ∈ univ \ K, clamp01 (w r0 i)) * Real.exp (-((N : ℝ) / 100)) * (N : ℝ) ^ 2 *
          2 ^ (N - dX N + 2) / 2 ^ Z.card := by
      refine hle.trans ((mul_le_mul_of_nonneg_left hMZ hrep0).trans ?_)
      calc causeRep (tpmOf (flipP s w)) Z z (univ \ K) s * (N : ℝ) ^ 2
          ≤ (causeFwd (tpmOf (flipP s w)) Z z (univ \ K) s /
              (2 ^ Z.card * (1 / 2 ^ (N - dX N + 2)))) * (N : ℝ) ^ 2 := by
            rw [← cs_causeFwd_eq] at hrep
            exact mul_le_mul_of_nonneg_right hrep (by positivity)
        _ ≤ ((∏ i ∈ univ \ K, clamp01 (w r0 i)) * Real.exp (-((N : ℝ) / 100)) /
              (2 ^ Z.card * (1 / 2 ^ (N - dX N + 2)))) * (N : ℝ) ^ 2 := by gcongr
        _ = _ := by field_simp
    refine lt_of_le_of_lt hstep (lt_of_lt_of_le ?_ hRHS)
    refine cs_arith_lt hPM (by positivity) (by positivity) (by positivity) ?_ (G := 2 ^ (JC N + 4))
      (by linarith)
    rw [← pow_add, ← pow_add]
    calc (2 : ℝ) ^ (N - dX N + 2 + (dX N + 2)) = 2 ^ (N + 4) := by
          congr 1; omega
      _ ≤ 2 ^ (Z.card + (JC N + 4)) := pow_le_pow_right₀ (by norm_num) (by omega)

end Census
end IIT
