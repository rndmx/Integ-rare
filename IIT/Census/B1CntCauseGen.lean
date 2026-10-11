/-
Census, B1, W14 work package WP2 (cause side), part 1: generic lemmas.

* MIP bounds for `phiCat` (Phi level) and their `phiCatAt` forms (`phiCatAt_ge_of_ratio`,
  `phiCatAt_le_total`), the structure of partitions with purview `univ` (`cutCount_univ_ge`,
  same-or-disjoint purview parts, the "full purview" type);
* the Jensen bound on subcube means (`cs_sum_log_max_le`, `logW_le_jensen`);
* subcube means on the open cube (positivity, `univ`, the pair subcube `{r, r^x}`);
* asymptotic tools (`cs_ev_log_le`).
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §7.  No `sorry`.
-/
import IIT.Census.B1CntBasics

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### MIP bounds -/

theorem cs_phiCat_ge_of_ratio (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) (hM : M.Nonempty)
    {L c : ℝ} (hL : 0 ≤ L) (hc : 0 ≤ c) (hcc : ∀ θ : Partition N M Z, L ≤ (cutCount M Z θ : ℝ))
    (hratio : ∀ θ : Partition N M Z,
      c ≤ Real.logb 2 (causeFwd T Z z M m / partCauseFwd T Z z M m θ) / (cutCount M Z θ : ℝ)) :
    causeRep T Z z M m * (L * c) ≤ phiCat T Z z M m := by
  have : Nonempty (Partition N M Z) := ⟨Partition.total hM Z⟩
  obtain ⟨θ, hθ⟩ := argminSet_nonempty (normalizedPhiC T Z z M m)
  set LR := Real.logb 2 (causeFwd T Z z M m / partCauseFwd T Z z M m θ)
  have key : L * c ≤ pos LR := by
    have hcc0 : (0 : ℝ) ≤ cutCount M Z θ := Nat.cast_nonneg _
    rcases eq_or_lt_of_le hcc0 with h0 | hpos
    · have hL0 : L = 0 := le_antisymm (by have := hcc θ; rw [← h0] at this; exact this) hL
      rw [hL0, zero_mul]; exact pos_nonneg _
    · calc L * c ≤ (cutCount M Z θ : ℝ) * c := mul_le_mul_of_nonneg_right (hcc θ) hc
        _ ≤ (cutCount M Z θ : ℝ) * (LR / cutCount M Z θ) :=
            mul_le_mul_of_nonneg_left (hratio θ) hcc0
        _ = LR := mul_div_cancel₀ _ hpos.ne'
        _ ≤ pos LR := le_pos _
  calc causeRep T Z z M m * (L * c) ≤ causeRep T Z z M m * pos LR :=
        mul_le_mul_of_nonneg_left key (causeRep_nonneg _ _ _ _ _)
    _ = phiCofPartition T Z z M m θ := rfl
    _ ≤ phiCat T Z z M m := le_sup'OrZero hθ

theorem cs_phiCat_le_total (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) (hM : M.Nonempty) (hZ : Z.Nonempty) :
    phiCat T Z z M m ≤ phiCofPartition T Z z M m (Partition.total hM Z) := by
  refine sup'OrZero_le (phiCofPartition_nonneg _ _ _ _ _ _) fun θ hθ => ?_
  have hmin := (mem_argminSet.1 hθ) (Partition.total hM Z)
  unfold normalizedPhiC at hmin
  have hccθ : (0 : ℝ) < cutCount M Z θ := Nat.cast_pos.2 (cutCount_pos hZ θ)
  have hcct : (cutCount M Z θ : ℝ) ≤ cutCount M Z (Partition.total hM Z) := by
    rw [cutCount_total]; exact_mod_cast cutCount_le M Z θ
  have hcct0 : (0 : ℝ) < cutCount M Z (Partition.total hM Z) := lt_of_lt_of_le hccθ hcct
  have hφt := phiCofPartition_nonneg T Z z M m (Partition.total hM Z)
  rw [div_le_div_iff₀ hccθ hcct0] at hmin
  have h2 : phiCofPartition T Z z M m θ * (cutCount M Z (Partition.total hM Z) : ℝ) ≤
      phiCofPartition T Z z M m (Partition.total hM Z) * (cutCount M Z (Partition.total hM Z) : ℝ) :=
    hmin.trans (mul_le_mul_of_nonneg_left hcct hφt)
  exact le_of_mul_le_mul_right h2 hcct0

/-- `phiCatAt_ge_of_ratio` (blueprint §7), `phiCatAt` form, at `S = univ`. -/
theorem cs_phiCatAt_univ_ge_of_ratio (T : UnitTPM N) (u : State N) (hu : 0 < ∑ v : State N, fullProb T v u)
    (Z : Finset (Fin N)) (z : State N) (M : Finset (Fin N)) (m : State N) (hM : M.Nonempty)
    {L c : ℝ} (hL : 0 ≤ L) (hc : 0 ≤ c) (hcc : ∀ θ : Partition N M Z, L ≤ (cutCount M Z θ : ℝ))
    (hratio : ∀ θ : Partition N M Z,
      c ≤ Real.logb 2 (causeFwd T Z z M m / partCauseFwd T Z z M m θ) / (cutCount M Z θ : ℝ)) :
    causeRepAt T univ u Z z M m * (L * c) ≤ phiCatAt T univ u Z z M m := by
  rw [causeRepAt_univ T u Z z M m hu, phiCatAt_univ T u Z z M m hu]
  exact cs_phiCat_ge_of_ratio T Z z M m hM hL hc hcc hratio

/-- The partitioned cause term of the total partition: every mechanism unit fully cut. -/
lemma cs_causePart_total {M Z : Finset (Fin N)} (hM : M.Nonempty) {i : Fin N} (hi : i ∈ M) :
    (Partition.total hM Z).causePart i = ∅ :=
  (Partition.total hM Z).causePart_eq (Finset.mem_insert_self _ _) hi

lemma cs_partCauseFwd_total (T : UnitTPM N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (m : State N) (hM : M.Nonempty) :
    partCauseFwd T Z z M m (Partition.total hM Z) = ∏ i ∈ M, effUnit T ∅ z i (m i) := by
  unfold partCauseFwd
  exact prod_congr rfl fun i hi => by rw [cs_causePart_total hM hi]

/-! ### Partitions with purview `univ` -/

lemma cs_causePart_eq_or_disjoint {M Z : Finset (Fin N)} (θ : Partition N M Z) {i i' : Fin N}
    (hi : i ∈ M) (hi' : i' ∈ M) :
    θ.causePart i = θ.causePart i' ∨ Disjoint (θ.causePart i) (θ.causePart i') := by
  obtain ⟨b, hb, hib⟩ := θ.mech_cover i hi
  obtain ⟨b', hb', hib'⟩ := θ.mech_cover i' hi'
  rw [θ.causePart_eq hb hib, θ.causePart_eq hb' hib']
  by_cases h : b = b'
  · left; rw [h]
  · right; exact θ.purv_disjoint b hb b' hb' h

/-- If some unit keeps the whole (nonempty) purview `Z`, another unit keeps nothing. -/
lemma cs_exists_causePart_empty {M Z : Finset (Fin N)} (θ : Partition N M Z) (hZ : Z.Nonempty)
    {i0 : Fin N} (hi0 : i0 ∈ M) (h0 : θ.causePart i0 = Z) :
    ∃ i1 ∈ M, θ.causePart i1 = ∅ := by
  obtain ⟨b, hb, hib⟩ := θ.mech_cover i0 hi0
  rw [θ.causePart_eq hb hib] at h0
  have hbM : b.1 ≠ M := by
    intro e
    have := θ.proper b hb e
    rw [h0] at this
    exact hZ.ne_empty this
  have hss : b.1 ⊂ M := (θ.mech_subset b hb).ssubset_of_ne hbM
  obtain ⟨i1, hi1M, hi1b⟩ := exists_of_ssubset hss
  obtain ⟨b', hb', hib'⟩ := θ.mech_cover i1 hi1M
  have hne : b' ≠ b := fun e => hi1b (e ▸ hib')
  refine ⟨i1, hi1M, ?_⟩
  rw [θ.causePart_eq hb' hib']
  have hd := θ.purv_disjoint b' hb' b hb hne
  rw [h0] at hd
  exact Finset.subset_empty.1 fun k hk => absurd ((θ.purv_subset b' hb') hk)
    (Finset.disjoint_left.1 hd hk)

/-- **`cutCount_univ_ge`** (W5 Lemma PS(c)). -/
theorem cutCount_univ_ge (M : Finset (Fin N)) (θ : Partition N M univ) :
    M.card ≤ cutCount M univ θ := by
  rw [cutCount_eq_causeSum]
  by_cases h : ∃ i0 ∈ M, θ.causePart i0 = univ
  · obtain ⟨i0, hi0, h0⟩ := h
    rcases (univ : Finset (Fin N)).eq_empty_or_nonempty with hU | hU
    · have : M = ∅ := Finset.subset_empty.1 (hU ▸ subset_univ M)
      rw [Finset.card_eq_zero.2 this]; exact Nat.zero_le _
    obtain ⟨i1, hi1, h1⟩ := cs_exists_causePart_empty θ hU hi0 h0
    have hle : (univ : Finset (Fin N)).card - (θ.causePart i1).card ≤
        ∑ k ∈ M, ((univ : Finset (Fin N)).card - (θ.causePart k).card) :=
      single_le_sum (f := fun k => (univ : Finset (Fin N)).card - (θ.causePart k).card)
        (fun _ _ => Nat.zero_le _) hi1
    rw [h1, card_empty, Nat.sub_zero] at hle
    exact (card_le_univ M).trans hle
  · push Not at h
    calc M.card = ∑ _k ∈ M, 1 := by rw [sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ k ∈ M, ((univ : Finset (Fin N)).card - (θ.causePart k).card) := by
        refine sum_le_sum fun k hk => ?_
        have hlt : (θ.causePart k).card < (univ : Finset (Fin N)).card :=
          card_lt_card ((subset_univ _).ssubset_of_ne (h k hk))
        omega

/-- Every unit keeps all of `univ` or nothing, once some unit keeps `univ`. -/
lemma cs_causePart_univ_or_empty {M : Finset (Fin N)} (θ : Partition N M univ) {i0 : Fin N}
    (hi0 : i0 ∈ M) (h0 : θ.causePart i0 = univ) {i : Fin N} (hi : i ∈ M) :
    θ.causePart i = univ ∨ θ.causePart i = ∅ := by
  rcases cs_causePart_eq_or_disjoint θ hi hi0 with h | h
  · left; rw [h, h0]
  · right; rw [h0] at h
    exact Finset.subset_empty.1 fun k hk => absurd (mem_univ k) (Finset.disjoint_left.1 h hk)

/-! ### The Jensen bound on subcube means -/

/-- `Σ_i log max(Ā_i, c) ≤ N log(c + ρ)` when the subcube's rows have average excess `≤ ρ N`
(EI4 + EI5 of W5 §2). -/
theorem cs_sum_log_max_le (w : Param N) (A : Finset (Fin N)) (t : State N) {c ρ : ℝ} (hc : 0 < c)
    (hρ : ∑ r ∈ agree A t, ∑ i, pos (clamp01 (w r i) - c) ≤ ρ * N * (agree A t).card) :
    ∑ i, Real.log (max (subMean w A t i) c) ≤ N * Real.log (c + ρ) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  set C := agree A t with hCdef
  have hC : (0 : ℝ) < C.card := Nat.cast_pos.2 (card_agree_pos A t)
  set x : Fin N → ℝ := fun i => max (subMean w A t i) c with hx
  have hxpos : ∀ i, 0 < x i := fun i => lt_of_lt_of_le hc (le_max_right _ _)
  -- per-column: max(Ā, c) ≤ c + mean_r pos(y - c)
  have hcol : ∀ i, x i ≤ c + (∑ r ∈ C, pos (clamp01 (w r i) - c)) / C.card := by
    intro i
    have hmean : subMean w A t i - c = (∑ r ∈ C, (clamp01 (w r i) - c)) / C.card := by
      unfold subMean
      rw [← hCdef, sum_sub_distrib, sum_const, nsmul_eq_mul]
      field_simp
    have h1 : subMean w A t i - c ≤ (∑ r ∈ C, pos (clamp01 (w r i) - c)) / C.card := by
      rw [hmean]
      exact div_le_div_of_nonneg_right (sum_le_sum fun r _ => le_pos _) hC.le
    have h2 : 0 ≤ (∑ r ∈ C, pos (clamp01 (w r i) - c)) / C.card :=
      div_nonneg (sum_nonneg fun r _ => pos_nonneg _) hC.le
    show max (subMean w A t i) c ≤ _
    exact max_le (by linarith) (by linarith)
  have hsumx : ∑ i, x i ≤ N * (c + ρ) := by
    calc ∑ i, x i ≤ ∑ i, (c + (∑ r ∈ C, pos (clamp01 (w r i) - c)) / C.card) :=
          sum_le_sum fun i _ => hcol i
      _ = N * c + (∑ r ∈ C, ∑ i, pos (clamp01 (w r i) - c)) / C.card := by
          rw [sum_add_distrib, ← sum_div, sum_comm]; simp
      _ ≤ N * c + (ρ * N * C.card) / C.card := by gcongr
      _ = N * (c + ρ) := by field_simp
  set a := (∑ i, x i) / N with ha
  have hapos : 0 < a := div_pos (sum_pos (fun i _ => hxpos i) ⟨⟨0, hN⟩, mem_univ _⟩) hNr
  have hlog : ∀ i, Real.log (x i) ≤ Real.log a + (x i / a - 1) := by
    intro i
    have := Real.log_le_sub_one_of_pos (div_pos (hxpos i) hapos)
    rw [Real.log_div (hxpos i).ne' hapos.ne'] at this
    linarith
  have hsum1 : ∑ i, Real.log (x i) ≤ N * Real.log a := by
    calc ∑ i, Real.log (x i) ≤ ∑ i, (Real.log a + (x i / a - 1)) := sum_le_sum fun i _ => hlog i
      _ = N * Real.log a + ((∑ i, x i) / a - N) := by
          rw [sum_add_distrib, sum_sub_distrib, ← sum_div]; simp
      _ = N * Real.log a := by
          have hS : 0 < ∑ i, x i := sum_pos (fun i _ => hxpos i) ⟨⟨0, hN⟩, mem_univ _⟩
          have : (∑ i, x i) / a = N := by rw [ha]; field_simp
          rw [this]; ring
  have hale : a ≤ c + ρ := by
    rw [ha, div_le_iff₀ hNr]; linarith
  calc ∑ i, Real.log (max (subMean w A t i) c) = ∑ i, Real.log (x i) := rfl
    _ ≤ N * Real.log a := hsum1
    _ ≤ N * Real.log (c + ρ) := mul_le_mul_of_nonneg_left (Real.log_le_log hapos hale) hNr.le

/-- **`logW_le_jensen`** (W13-cause G3). -/
theorem logW_le_jensen (w : Param N) (A : Finset (Fin N)) (t : State N) {ρ : ℝ}
    (hρ : ∑ r ∈ agree A t, ∑ i, pos (clamp01 (w r i) - b1Cap) ≤ ρ * N * (agree A t).card) :
    ∑ i, Real.log (max (2 * subMean w A t i) 1) ≤ N * Real.log (2 * (b1Cap + ρ)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hcap : (0 : ℝ) < b1Cap := by unfold b1Cap; norm_num
  have hJ := cs_sum_log_max_le w A t hcap hρ
  have hρ0 : 0 ≤ ρ := by
    have h0 : (0 : ℝ) ≤ ρ * N * (agree A t).card :=
      le_trans (sum_nonneg fun r _ => sum_nonneg fun i _ => pos_nonneg _) hρ
    have hNC : (0 : ℝ) < N * (agree A t).card :=
      mul_pos (Nat.cast_pos.2 hN) (Nat.cast_pos.2 (card_agree_pos A t))
    rw [mul_assoc] at h0
    by_contra hneg; push Not at hneg
    linarith [mul_neg_of_neg_of_pos hneg hNC]
  have hcρ : 0 < b1Cap + ρ := by linarith
  have hterm : ∀ i, Real.log (max (2 * subMean w A t i) 1) ≤
      Real.log 2 + Real.log (max (subMean w A t i) b1Cap) := by
    intro i
    have hm : 0 < max (subMean w A t i) b1Cap := lt_of_lt_of_le hcap (le_max_right _ _)
    rw [← Real.log_mul (by norm_num) hm.ne']
    refine Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _)) ?_
    refine max_le ?_ ?_
    · have := le_max_left (subMean w A t i) b1Cap; linarith
    · have := le_max_right (subMean w A t i) b1Cap; unfold b1Cap at this ⊢; linarith
  calc ∑ i, Real.log (max (2 * subMean w A t i) 1)
      ≤ ∑ i : Fin N, (Real.log 2 + Real.log (max (subMean w A t i) b1Cap)) :=
        sum_le_sum fun i _ => hterm i
    _ = N * Real.log 2 + ∑ i, Real.log (max (subMean w A t i) b1Cap) := by
        rw [sum_add_distrib]; simp
    _ ≤ N * Real.log 2 + N * Real.log (b1Cap + ρ) := by linarith
    _ = N * Real.log (2 * (b1Cap + ρ)) := by
        rw [Real.log_mul (by norm_num) hcρ.ne']; ring

/-! ### Subcube means on the open cube -/

lemma cs_clamp_pos {w : Param N} (hw : w ∈ openCube N) (r : State N) (i : Fin N) :
    0 < clamp01 (w r i) := by
  rw [b1_clamp01_of_mem_Ioo (hw r i)]; exact (hw r i).1

lemma cs_subMean_pos {w : Param N} (hw : w ∈ openCube N) (A : Finset (Fin N)) (t : State N)
    (i : Fin N) : 0 < subMean w A t i :=
  div_pos (sum_pos (fun r _ => cs_clamp_pos hw r i) (agree_nonempty A t))
    (Nat.cast_pos.2 (card_agree_pos A t))

lemma cs_subMean_le_one (w : Param N) (A : Finset (Fin N)) (t : State N) (i : Fin N) :
    subMean w A t i ≤ 1 := by
  unfold subMean
  rw [div_le_one (Nat.cast_pos.2 (card_agree_pos A t))]
  calc ∑ r ∈ agree A t, clamp01 (w r i) ≤ ∑ _r ∈ agree A t, (1 : ℝ) :=
        sum_le_sum fun r _ => clamp01_le_one _
    _ = (agree A t).card := by rw [sum_const, nsmul_eq_mul, mul_one]

lemma cs_subMean_univ (w : Param N) (t : State N) (i : Fin N) :
    subMean w univ t i = clamp01 (w t i) := by
  unfold subMean
  rw [agree_univ_eq, sum_singleton, card_singleton, Nat.cast_one, div_one]

lemma cs_mem_agree_compl_single {x : Fin N} {r v : State N} :
    v ∈ agree ({x}ᶜ : Finset (Fin N)) r ↔ v = r ∨ v = flipAt x r := by
  rw [mem_agree]
  constructor
  · intro h
    by_cases hx : v x = r x
    · left; funext j
      by_cases hj : j = x
      · rw [hj, hx]
      · exact h j (by simpa using hj)
    · right; funext j
      by_cases hj : j = x
      · subst hj; simp only [flipAt, Function.update_self]
        cases h1 : v j <;> cases h2 : r j <;> simp_all
      · rw [flipAt, Function.update_of_ne hj]; exact h j (by simpa using hj)
  · rintro (rfl | rfl) j hj
    · rfl
    · have hj' : j ≠ x := by simpa using hj
      rw [flipAt, Function.update_of_ne hj']

lemma cs_agree_compl_single (x : Fin N) (r : State N) :
    agree ({x}ᶜ : Finset (Fin N)) r = {r, flipAt x r} := by
  ext v; rw [cs_mem_agree_compl_single, mem_insert, mem_singleton]

lemma cs_subMean_pair (w : Param N) (x : Fin N) (r : State N) (i : Fin N) :
    subMean w ({x}ᶜ : Finset (Fin N)) r i = (clamp01 (w r i) + clamp01 (w (flipAt x r) i)) / 2 := by
  unfold subMean
  rw [cs_agree_compl_single, sum_pair (flipAt_ne x r).symm,
    card_pair (flipAt_ne x r).symm]
  norm_num

/-! ### Asymptotic tools -/

lemma cs_ev_log_le {c : ℝ} (hc : 0 < c) : ∀ᶠ N : ℕ in atTop, Real.log N ≤ c * N := by
  have h := Real.isLittleO_log_id_atTop.bound hc
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h] with N hN
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp only [Real.norm_eq_abs, id] at hN
  rw [abs_of_nonneg h0] at hN
  exact (le_abs_self _).trans hN

lemma cs_natLog_le (hN : 1 ≤ N) : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
  have h1 : (2 : ℝ) ^ Nat.log 2 N ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have h2 := Real.log_le_log (by positivity) h1
  rwa [Real.log_pow] at h2

lemma cs_lt_two_pow_natLog (N : ℕ) : (N : ℝ) < 2 * 2 ^ Nat.log 2 N := by
  have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
  rw [pow_succ] at this
  exact_mod_cast (by omega : N < 2 * 2 ^ Nat.log 2 N)

lemma cs_dX_le (N : ℕ) : (dX N : ℝ) ≤ N / 30 + 1 := by
  have : 30 * dX N ≤ N + 29 := by unfold dX; omega
  have h : (30 : ℝ) * dX N ≤ N + 29 := by exact_mod_cast this
  linarith

lemma cs_dX_ge (N : ℕ) : (N : ℝ) / 30 ≤ dX N := by
  have : N ≤ 30 * dX N := by unfold dX; omega
  have h : (N : ℝ) ≤ 30 * dX N := by exact_mod_cast this
  linarith

lemma cs_dX_le_N (hN : 1 ≤ N) : dX N ≤ N := by unfold dX; omega

lemma cs_mX_eq (hN : 1 ≤ N) : mX N = (N : ℝ) - dX N := by
  unfold mX; rw [Nat.cast_sub (cs_dX_le_N hN)]

end Census
end IIT
