/-
Census of complexes, B1 development, module A6 (part 2): type events with rounded counts
(the probabilistic frame of certificate C1, `B1-W6-certificates.md` Section 2.1).

For pairwise disjoint cells `I j` (`j : Fin k`) and counts `n j` with `∑ n j = N`, the type event
`{v | ∀ j, #{i | v i ∈ I j} = n j}`:
* covers every coordinate (`cr_type_cover`), so sums over the coordinates are controlled by the
  cells (`cr_type_sum_le`, `cr_type_sum_ge`, `cr_type_count_ge`);
* is a finite union of boxes (`cr_type_event_subset`), hence measurable
  (`cr_measurableSet_type_event`), with the multinomial upper bound
  `P ≤ exp (-N Σ (n_j/N) log ((n_j/N)/ℓ_j))` (`cr_type_event_le`, via
  `cr_fibTypeCount_mul_le`: `#T(n) ∏ n_j^{n_j} ≤ N^N`);
* has the rounding estimates `cr_type_rate_le`/`cr_type_rate_ge`: for target fractions `a_j > 0`
  (`∑ a = 1`) and `|n_j - a_j N| ≤ E`,
  `|N Σ (n_j/N) log((n_j/N)/ℓ_j) - N KL(a)| ≤ E Σ |log (a_j/ℓ_j)| + E² Σ 1/a_j`, where
  `KL(a) = Σ a_j log (a_j/ℓ_j)`; combined with A4's `type_event_ge_rowM` this gives
  `cr_type_event_ge_KL` and `cr_type_event_le_KL`.
* `crCounts a K N j` are the rounded counts `⌊a_j N⌋` (`j ≥ 1`) with the remainder in cell `0`
  (`crCounts_sum`, `crCounts_le`, `crCounts_gt`, `crCounts_zero_ge`, `crCounts_abs_le`,
  `crCounts_wsum_le`, `crCounts_wsum_ge`).
-/
import IIT.Census.CertRatesCore

namespace IIT
namespace Census

open MeasureTheory Finset

noncomputable section

variable {N k : ℕ}

/-! ### Covering and sums over a type event -/

section Cover

variable (I : Fin k → Set ℝ) [∀ j, DecidablePred (· ∈ I j)]

lemma cr_filter_disjoint (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) (v : Fin N → ℝ)
    {j j' : Fin k} (h : j ≠ j') :
    Disjoint (univ.filter fun i => v i ∈ I j) (univ.filter fun i => v i ∈ I j') :=
  Finset.disjoint_filter.2 fun _ _ h1 h2 => Set.disjoint_left.1 (hdisj h) h1 h2

/-- Every coordinate of a point of a type event (`∑ n = N`) lies in some cell. -/
lemma cr_type_cover (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) {n : Fin k → ℕ}
    (hn : ∑ j, n j = N) {v : Fin N → ℝ} (hv : ∀ j, (univ.filter fun i => v i ∈ I j).card = n j)
    (i : Fin N) : ∃ j, v i ∈ I j := by
  classical
  by_contra h
  push Not at h
  have hsub : (univ : Finset (Fin k)).biUnion (fun j => univ.filter fun i' => v i' ∈ I j) ⊆
      univ.erase i := by
    intro i' hi'
    rw [Finset.mem_biUnion] at hi'
    obtain ⟨j, _, hj⟩ := hi'
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_erase]
    refine ⟨?_, mem_univ _⟩
    rintro rfl
    exact h j hj.2
  have hpd : ((univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun j => univ.filter fun i' => v i' ∈ I j) :=
    fun j _ j' _ hjj' => cr_filter_disjoint I hdisj v hjj'
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hpd, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
    Fintype.card_fin] at hcard
  simp only [hv, hn] at hcard
  have := i.2
  omega

/-- The cell function of a point of a type event. -/
lemma cr_type_cell (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) {n : Fin k → ℕ}
    (hn : ∑ j, n j = N) {v : Fin N → ℝ} (hv : ∀ j, (univ.filter fun i => v i ∈ I j).card = n j) :
    ∃ σ : Fin N → Fin k, (∀ i, v i ∈ I (σ i)) ∧
      ∀ j, (univ.filter fun i => σ i = j) = univ.filter fun i => v i ∈ I j := by
  choose σ hσ using cr_type_cover I hdisj hn hv
  refine ⟨σ, hσ, fun j => ?_⟩
  ext i
  simp only [Finset.mem_filter, mem_univ, true_and]
  constructor
  · rintro rfl; exact hσ i
  · intro h
    by_contra hne
    exact Set.disjoint_left.1 (hdisj hne) (hσ i) h

/-- **Upper sum bound**: if `g ≤ G j` on the cell `I j`, then `∑_i g (v i) ≤ ∑_j n_j G_j`. -/
lemma cr_type_sum_le (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) {n : Fin k → ℕ}
    (hn : ∑ j, n j = N) {v : Fin N → ℝ} (hv : ∀ j, (univ.filter fun i => v i ∈ I j).card = n j)
    (g : ℝ → ℝ) (G : Fin k → ℝ) (hG : ∀ j, ∀ y ∈ I j, g y ≤ G j) :
    ∑ i, g (v i) ≤ ∑ j, (n j : ℝ) * G j := by
  obtain ⟨σ, hσ, hfib⟩ := cr_type_cell I hdisj hn hv
  rw [← Finset.sum_fiberwise univ σ (fun i => g (v i))]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [hfib j, ← hv j]
  calc ∑ i ∈ univ.filter (fun i => v i ∈ I j), g (v i)
      ≤ ∑ _i ∈ univ.filter (fun i => v i ∈ I j), G j :=
        Finset.sum_le_sum fun i hi => hG j _ (Finset.mem_filter.1 hi).2
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Lower sum bound**: if `G j ≤ g` on the cell `I j`, then `∑_j n_j G_j ≤ ∑_i g (v i)`. -/
lemma cr_type_sum_ge (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) {n : Fin k → ℕ}
    (hn : ∑ j, n j = N) {v : Fin N → ℝ} (hv : ∀ j, (univ.filter fun i => v i ∈ I j).card = n j)
    (g : ℝ → ℝ) (G : Fin k → ℝ) (hG : ∀ j, ∀ y ∈ I j, G j ≤ g y) :
    ∑ j, (n j : ℝ) * G j ≤ ∑ i, g (v i) := by
  have h := cr_type_sum_le I hdisj hn hv (fun y => -g y) (fun j => -G j) fun j y hy => by
    simp only [neg_le_neg_iff]; exact hG j y hy
  simp only [Finset.sum_neg_distrib, mul_neg] at h
  linarith

/-- **Counts**: `#{i | v i ∈ S} ≥ ∑_{j ∈ J} n_j` when the cells of `J` lie in `S`. -/
lemma cr_type_count_ge (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) {n : Fin k → ℕ}
    (hn : ∑ j, n j = N) {v : Fin N → ℝ} (hv : ∀ j, (univ.filter fun i => v i ∈ I j).card = n j)
    (S : Set ℝ) [DecidablePred (· ∈ S)] (J : Finset (Fin k)) (hJ : ∀ j ∈ J, I j ⊆ S) :
    ∑ j ∈ J, n j ≤ (univ.filter fun i => v i ∈ S).card := by
  have h := cr_type_sum_ge I hdisj hn hv (fun y => if y ∈ S then (1 : ℝ) else 0)
    (fun j => if j ∈ J then 1 else 0) fun j y hy => by
      by_cases hj : j ∈ J
      · rw [if_pos hj, if_pos (hJ j hj hy)]
      · rw [if_neg hj]; split_ifs <;> norm_num
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, univ_inter, Finset.sum_boole] at h
  have h' : ((∑ j ∈ J, n j : ℕ) : ℝ) ≤ ((univ.filter fun i => v i ∈ S).card : ℝ) := by
    push_cast; exact h
  exact_mod_cast h'

end Cover

/-! ### The type event as a union of boxes; the multinomial upper bound -/

section Upper

variable (I : Fin k → Set ℝ) [∀ j, DecidablePred (· ∈ I j)]

lemma cr_type_event_subset (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) {n : Fin k → ℕ}
    (hn : ∑ j, n j = N) :
    {v : Fin N → ℝ | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} ⊆
      ⋃ σ ∈ univ.filter (fun σ : Fin N → Fin k => fibType σ = n), fibTypeBox I σ := by
  intro v hv
  obtain ⟨σ, hσ, hfib⟩ := cr_type_cell I hdisj hn hv
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨σ, Finset.mem_filter.2 ⟨mem_univ _, funext fun j => ?_⟩, fun i _ => hσ i⟩
  unfold fibType
  rw [hfib j, hv j]

lemma cr_type_event_eq (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) {n : Fin k → ℕ}
    (hn : ∑ j, n j = N) :
    {v : Fin N → ℝ | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} =
      ⋃ σ ∈ univ.filter (fun σ : Fin N → Fin k => fibType σ = n), fibTypeBox I σ :=
  (cr_type_event_subset I hdisj hn).antisymm (Set.iUnion₂_subset fun _ hσ =>
    fibTypeBox_sub_event I hdisj (Finset.mem_filter.1 hσ).2)

/-- Type events are measurable. -/
theorem cr_measurableSet_type_event (hI : ∀ j, MeasurableSet (I j))
    (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) {n : Fin k → ℕ} (hn : ∑ j, n j = N) :
    MeasurableSet {v : Fin N → ℝ | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} := by
  rw [cr_type_event_eq I hdisj hn]
  exact Finset.measurableSet_biUnion _ fun σ _ => MeasurableSet.univ_pi fun i => hI (σ i)

/-- **Multinomial bound**: `#T(n) ∏ n_j^{n_j} ≤ N^N`. -/
lemma cr_fibTypeCount_mul_le (n : Fin k → ℕ) (hn : ∑ j, n j = N) :
    fibTypeCount N k n * ∏ j, n j ^ n j ≤ N ^ N := by
  have h1 : N ^ N = ∑ σ : Fin N → Fin k, ∏ j, n j ^ fibType σ j := by
    have e1 : N ^ N = ∏ _i : Fin N, ∑ j, n j := by
      rw [Finset.prod_const, hn, Finset.card_univ, Fintype.card_fin]
    rw [e1, Fintype.prod_sum (fun (_ : Fin N) (j : Fin k) => n j)]
    exact Finset.sum_congr rfl fun σ _ => prod_comp_eq_prod_pow_fibType n σ
  rw [h1, fibTypeCount]
  calc (univ.filter fun σ : Fin N → Fin k => fibType σ = n).card * ∏ j, n j ^ n j
      = ∑ σ ∈ univ.filter (fun σ : Fin N → Fin k => fibType σ = n), ∏ j, n j ^ fibType σ j := by
        rw [Finset.card_eq_sum_ones, Finset.sum_mul]
        exact Finset.sum_congr rfl fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2, one_mul]
    _ ≤ ∑ σ, ∏ j, n j ^ fibType σ j := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- **Type event upper bound**: `P ≤ exp (-N Σ (n_j/N) log ((n_j/N)/ℓ_j))`. -/
theorem cr_type_event_le (hI : ∀ j, MeasurableSet (I j))
    (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) (ℓ : Fin k → ℝ)
    (hℓ : ∀ j, volume (I j) = ENNReal.ofReal (ℓ j)) (hℓpos : ∀ j, 0 < ℓ j)
    (n : Fin k → ℕ) (hn : ∑ j, n j = N) :
    rowM N {v : Fin N → ℝ | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} ≤
      ENNReal.ofReal (Real.exp (-(N * ∑ j, ((n j : ℝ) / N) * Real.log (((n j : ℝ) / N) / ℓ j)))) := by
  have hrow : rowM N {v : Fin N → ℝ | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} ≤
      volume {v : Fin N → ℝ | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} := by
    rw [← restrict_row]; exact Measure.restrict_le_self _
  refine hrow.trans ((measure_mono (cr_type_event_subset I hdisj hn)).trans ?_)
  rw [volume_fibTypeBoxes I hI hdisj ℓ hℓ (fun j => (hℓpos j).le) n, exp_type_rate ℓ hℓpos n hn]
  refine ENNReal.ofReal_le_ofReal ?_
  have hC := cr_fibTypeCount_mul_le n hn
  have hC' : (fibTypeCount N k n : ℝ) * ∏ j, (n j : ℝ) ^ n j ≤ (N : ℝ) ^ N := by exact_mod_cast hC
  have hnn : 0 < ∏ j, (n j : ℝ) ^ n j := Finset.prod_pos fun j _ => by
    rcases Nat.eq_zero_or_pos (n j) with h | h
    · simp [h]
    · have : (0 : ℝ) < n j := by exact_mod_cast h
      positivity
  have hℓ0 : 0 ≤ ∏ j, ℓ j ^ n j := Finset.prod_nonneg fun j _ => pow_nonneg (hℓpos j).le _
  rw [le_div_iff₀ hnn]
  calc (fibTypeCount N k n : ℝ) * (∏ j, ℓ j ^ n j) * ∏ j, (n j : ℝ) ^ n j
      = ((fibTypeCount N k n : ℝ) * ∏ j, (n j : ℝ) ^ n j) * ∏ j, ℓ j ^ n j := by ring
    _ ≤ (N : ℝ) ^ N * ∏ j, ℓ j ^ n j := mul_le_mul_of_nonneg_right hC' hℓ0

end Upper

/-! ### Rounding: the rate of the rounded type versus `KL` -/

section Rounding

/-- Per-cell identity/inequality behind the rounding estimates. -/
lemma cr_type_term_le {a ℓ : ℝ} (ha : 0 < a) (hℓ : 0 < ℓ) (n : ℕ) {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * (((n : ℝ) / N) * Real.log (((n : ℝ) / N) / ℓ)) ≤
      N * a * Real.log (a / ℓ) + ((n : ℝ) - N * a) * Real.log (a / ℓ) +
        ((n : ℝ) - N * a) ^ 2 / (N * a) + ((n : ℝ) - N * a) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNa : 0 < (N : ℝ) * a := mul_pos hNr ha
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp only [Nat.cast_zero, zero_div, zero_mul, mul_zero, zero_sub]
    have : (-((N : ℝ) * a)) ^ 2 / (N * a) = N * a := by field_simp
    rw [this]; ring_nf; exact le_refl _
  · have hn : (0 : ℝ) < n := by exact_mod_cast h
    have hsplit : ((n : ℝ) / N) / ℓ = ((n : ℝ) / (N * a)) * (a / ℓ) := by
      field_simp
    rw [hsplit, Real.log_mul (by positivity) (by positivity)]
    have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) / (N * a) by positivity)
    have e1 : (N : ℝ) * ((n : ℝ) / N * (Real.log ((n : ℝ) / (N * a)) + Real.log (a / ℓ))) =
        n * Real.log ((n : ℝ) / (N * a)) + n * Real.log (a / ℓ) := by
      field_simp
    rw [e1]
    have h2 : (n : ℝ) * Real.log ((n : ℝ) / (N * a)) ≤ n * ((n : ℝ) / (N * a) - 1) :=
      mul_le_mul_of_nonneg_left hlog hn.le
    have e2 : (n : ℝ) * ((n : ℝ) / (N * a) - 1) = ((n : ℝ) - N * a) ^ 2 / (N * a) + ((n : ℝ) - N * a) := by
      field_simp
      ring
    nlinarith

lemma cr_type_term_ge {a ℓ : ℝ} (ha : 0 < a) (hℓ : 0 < ℓ) (n : ℕ) {N : ℕ} (hN : 0 < N) :
    N * a * Real.log (a / ℓ) + ((n : ℝ) - N * a) * Real.log (a / ℓ) + ((n : ℝ) - N * a) ≤
      (N : ℝ) * (((n : ℝ) / N) * Real.log (((n : ℝ) / N) / ℓ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNa : 0 < (N : ℝ) * a := mul_pos hNr ha
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp only [Nat.cast_zero, zero_div, zero_mul, mul_zero, zero_sub]
    nlinarith
  · have hn : (0 : ℝ) < n := by exact_mod_cast h
    have hsplit : ((n : ℝ) / N) / ℓ = ((n : ℝ) / (N * a)) * (a / ℓ) := by
      field_simp
    rw [hsplit, Real.log_mul (by positivity) (by positivity)]
    have hlog := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < (n : ℝ) / (N * a) by positivity)
    have e1 : (N : ℝ) * ((n : ℝ) / N * (Real.log ((n : ℝ) / (N * a)) + Real.log (a / ℓ))) =
        n * Real.log ((n : ℝ) / (N * a)) + n * Real.log (a / ℓ) := by
      field_simp
    rw [e1]
    have h2 : (n : ℝ) * (1 - ((n : ℝ) / (N * a))⁻¹) ≤ n * Real.log ((n : ℝ) / (N * a)) :=
      mul_le_mul_of_nonneg_left hlog hn.le
    have e2 : (n : ℝ) * (1 - ((n : ℝ) / (N * a))⁻¹) = (n : ℝ) - N * a := by
      field_simp
    nlinarith

/-- **Rounding, upper**: `N Σ (n_j/N) log((n_j/N)/ℓ_j) ≤ N KL + E Σ |D_j| + E² Σ 1/a_j`
(`D_j = log (a_j/ℓ_j)`, `|n_j - a_j N| ≤ E`, `N ≥ 1`). -/
theorem cr_type_rate_le (a ℓ : Fin k → ℝ) (ha : ∀ j, 0 < a j) (hsum : ∑ j, a j = 1)
    (hℓ : ∀ j, 0 < ℓ j) (n : Fin k → ℕ) (hn : ∑ j, n j = N) (hN : 0 < N) (E : ℝ)
    (hE : ∀ j, |(n j : ℝ) - a j * N| ≤ E) :
    N * ∑ j, ((n j : ℝ) / N) * Real.log (((n j : ℝ) / N) / ℓ j) ≤
      N * ∑ j, a j * Real.log (a j / ℓ j) + E * ∑ j, |Real.log (a j / ℓ j)| +
        E ^ 2 * ∑ j, 1 / a j := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have hzero : ∑ j, ((n j : ℝ) - N * a j) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_one]
    have : ((∑ j, n j : ℕ) : ℝ) = N := by exact_mod_cast hn
    push_cast at this
    linarith
  have hterm : ∀ j, (N : ℝ) * (((n j : ℝ) / N) * Real.log (((n j : ℝ) / N) / ℓ j)) ≤
      N * (a j * Real.log (a j / ℓ j)) + E * |Real.log (a j / ℓ j)| + E ^ 2 * (1 / a j) +
        ((n j : ℝ) - N * a j) := by
    intro j
    have h1 := cr_type_term_le (ha j) (hℓ j) (n j) hN
    have hEj : |(n j : ℝ) - N * a j| ≤ E := by rw [mul_comm]; exact hE j
    have h2 : ((n j : ℝ) - N * a j) * Real.log (a j / ℓ j) ≤ E * |Real.log (a j / ℓ j)| := by
      calc ((n j : ℝ) - N * a j) * Real.log (a j / ℓ j)
          ≤ |((n j : ℝ) - N * a j) * Real.log (a j / ℓ j)| := le_abs_self _
        _ = |(n j : ℝ) - N * a j| * |Real.log (a j / ℓ j)| := abs_mul _ _
        _ ≤ E * |Real.log (a j / ℓ j)| := mul_le_mul_of_nonneg_right hEj (abs_nonneg _)
    have h3 : ((n j : ℝ) - N * a j) ^ 2 / (N * a j) ≤ E ^ 2 * (1 / a j) := by
      have hsq : ((n j : ℝ) - N * a j) ^ 2 ≤ E ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hEj 2
      rw [div_le_iff₀ (mul_pos hNr (ha j))]
      have hE0 : 0 ≤ E ^ 2 := sq_nonneg E
      have : E ^ 2 * (1 / a j) * (N * a j) = E ^ 2 * N := by field_simp [(ha j).ne']
      rw [this]; nlinarith
    have e : (N : ℝ) * a j * Real.log (a j / ℓ j) = N * (a j * Real.log (a j / ℓ j)) := by ring
    linarith
  calc ∑ j, (N : ℝ) * (((n j : ℝ) / N) * Real.log (((n j : ℝ) / N) / ℓ j))
      ≤ ∑ j, ((N : ℝ) * (a j * Real.log (a j / ℓ j)) + E * |Real.log (a j / ℓ j)| +
          E ^ 2 * (1 / a j) + ((n j : ℝ) - N * a j)) := Finset.sum_le_sum fun j _ => hterm j
    _ = _ := by
        rw [Finset.sum_add_distrib, hzero, add_zero, Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- **Rounding, lower**: `N KL - E Σ |D_j| ≤ N Σ (n_j/N) log((n_j/N)/ℓ_j)`. -/
theorem cr_type_rate_ge (a ℓ : Fin k → ℝ) (ha : ∀ j, 0 < a j) (hsum : ∑ j, a j = 1)
    (hℓ : ∀ j, 0 < ℓ j) (n : Fin k → ℕ) (hn : ∑ j, n j = N) (hN : 0 < N) (E : ℝ)
    (hE : ∀ j, |(n j : ℝ) - a j * N| ≤ E) :
    N * ∑ j, a j * Real.log (a j / ℓ j) - E * ∑ j, |Real.log (a j / ℓ j)| ≤
      N * ∑ j, ((n j : ℝ) / N) * Real.log (((n j : ℝ) / N) / ℓ j) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have hzero : ∑ j, ((n j : ℝ) - N * a j) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_one]
    have : ((∑ j, n j : ℕ) : ℝ) = N := by exact_mod_cast hn
    push_cast at this
    linarith
  have hterm : ∀ j, (N : ℝ) * (a j * Real.log (a j / ℓ j)) - E * |Real.log (a j / ℓ j)| +
      ((n j : ℝ) - N * a j) ≤ (N : ℝ) * (((n j : ℝ) / N) * Real.log (((n j : ℝ) / N) / ℓ j)) := by
    intro j
    have h1 := cr_type_term_ge (ha j) (hℓ j) (n j) hN
    have hEj : |(n j : ℝ) - N * a j| ≤ E := by rw [mul_comm]; exact hE j
    have h2 : -(E * |Real.log (a j / ℓ j)|) ≤ ((n j : ℝ) - N * a j) * Real.log (a j / ℓ j) := by
      have : |((n j : ℝ) - N * a j) * Real.log (a j / ℓ j)| ≤ E * |Real.log (a j / ℓ j)| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hEj (abs_nonneg _)
      linarith [neg_abs_le (((n j : ℝ) - N * a j) * Real.log (a j / ℓ j))]
    have e : (N : ℝ) * a j * Real.log (a j / ℓ j) = N * (a j * Real.log (a j / ℓ j)) := by ring
    linarith
  calc ∑ j, (N : ℝ) * (a j * Real.log (a j / ℓ j)) - ∑ j, E * |Real.log (a j / ℓ j)|
      = ∑ j, ((N : ℝ) * (a j * Real.log (a j / ℓ j)) - E * |Real.log (a j / ℓ j)| +
          ((n j : ℝ) - N * a j)) := by
        rw [Finset.sum_add_distrib, hzero, add_zero, Finset.sum_sub_distrib]
    _ ≤ _ := Finset.sum_le_sum fun j _ => hterm j

/-- **Type event, lower bound with `KL`** (A4's `type_event_ge_rowM` plus rounding). -/
theorem cr_type_event_ge_KL (I : Fin k → Set ℝ) [∀ j, DecidablePred (· ∈ I j)]
    (hI : ∀ j, MeasurableSet (I j)) (hdisj : Pairwise fun j j' => Disjoint (I j) (I j'))
    (hsub : ∀ j, I j ⊆ Set.Icc 0 1) (ℓ : Fin k → ℝ)
    (hℓ : ∀ j, volume (I j) = ENNReal.ofReal (ℓ j)) (hℓpos : ∀ j, 0 < ℓ j)
    (a : Fin k → ℝ) (ha : ∀ j, 0 < a j) (hsum : ∑ j, a j = 1)
    (n : Fin k → ℕ) (hn : ∑ j, n j = N) (hN : 0 < N) (E : ℝ)
    (hE : ∀ j, |(n j : ℝ) - a j * N| ≤ E) :
    ENNReal.ofReal (Real.exp (-(N * ∑ j, a j * Real.log (a j / ℓ j) +
        (E * ∑ j, |Real.log (a j / ℓ j)| + E ^ 2 * ∑ j, 1 / a j))) / ((N : ℝ) + 1) ^ k) ≤
      rowM N {v : Fin N → ℝ | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} := by
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (type_event_ge_rowM I hI hdisj hsub ℓ hℓ hℓpos n hn)
  refine div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) (by positivity)
  have := cr_type_rate_le a ℓ ha hsum hℓpos n hn hN E hE
  linarith

/-- **Type event, upper bound with `KL`**. -/
theorem cr_type_event_le_KL (I : Fin k → Set ℝ) [∀ j, DecidablePred (· ∈ I j)]
    (hI : ∀ j, MeasurableSet (I j)) (hdisj : Pairwise fun j j' => Disjoint (I j) (I j'))
    (ℓ : Fin k → ℝ) (hℓ : ∀ j, volume (I j) = ENNReal.ofReal (ℓ j)) (hℓpos : ∀ j, 0 < ℓ j)
    (a : Fin k → ℝ) (ha : ∀ j, 0 < a j) (hsum : ∑ j, a j = 1)
    (n : Fin k → ℕ) (hn : ∑ j, n j = N) (hN : 0 < N) (E : ℝ)
    (hE : ∀ j, |(n j : ℝ) - a j * N| ≤ E) :
    rowM N {v : Fin N → ℝ | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} ≤
      ENNReal.ofReal (Real.exp (-(N * ∑ j, a j * Real.log (a j / ℓ j) -
        E * ∑ j, |Real.log (a j / ℓ j)|))) := by
  refine (cr_type_event_le I hI hdisj ℓ hℓ hℓpos n hn).trans (ENNReal.ofReal_le_ofReal ?_)
  refine Real.exp_le_exp.2 ?_
  have := cr_type_rate_ge a ℓ ha hsum hℓpos n hn hN E hE
  linarith

end Rounding

/-! ### Rounded counts -/

section Counts

/-- Rounded counts: `⌊a_j N⌋` for `1 ≤ j`, and the remainder `N - Σ_{1 ≤ i < K} ⌊a_i N⌋` in
cell `0`. -/
def crCounts (a : ℕ → ℝ) (K N : ℕ) (j : ℕ) : ℕ :=
  if j = 0 then N - ∑ i ∈ Finset.Ico 1 K, ⌊a i * N⌋₊ else ⌊a j * N⌋₊

variable {a : ℕ → ℝ} {K : ℕ}

lemma cr_sum_range_eq_zero_add (f : ℕ → ℝ) (hK : 1 ≤ K) :
    ∑ j ∈ range K, f j = f 0 + ∑ j ∈ Finset.Ico 1 K, f j := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]

lemma crCounts_floor_sum_le (ha : ∀ j, 0 ≤ a j) (hs : ∑ j ∈ range K, a j = 1) (hK : 1 ≤ K)
    (N : ℕ) : ∑ i ∈ Finset.Ico 1 K, ⌊a i * N⌋₊ ≤ N := by
  have h : ((∑ i ∈ Finset.Ico 1 K, ⌊a i * N⌋₊ : ℕ) : ℝ) ≤ N := by
    push_cast
    calc ∑ i ∈ Finset.Ico 1 K, (⌊a i * N⌋₊ : ℝ) ≤ ∑ i ∈ Finset.Ico 1 K, a i * N :=
          Finset.sum_le_sum fun i _ => Nat.floor_le (mul_nonneg (ha i) (Nat.cast_nonneg _))
      _ = (∑ i ∈ Finset.Ico 1 K, a i) * N := by rw [Finset.sum_mul]
      _ ≤ 1 * N := by
          refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
          rw [← hs, cr_sum_range_eq_zero_add a hK]
          linarith [ha 0]
      _ = N := one_mul _
  exact_mod_cast h

lemma crCounts_sum (ha : ∀ j, 0 ≤ a j) (hs : ∑ j ∈ range K, a j = 1) (hK : 1 ≤ K) (N : ℕ) :
    ∑ j ∈ range K, crCounts a K N j = N := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have h1 := crCounts_floor_sum_le ha hs hK N
  have h2 : ∑ j ∈ Finset.Ico (0 + 1) K, crCounts a K N j = ∑ i ∈ Finset.Ico 1 K, ⌊a i * N⌋₊ :=
    Finset.sum_congr rfl fun j hj => by
      rw [crCounts, if_neg (by simp at hj; omega)]
  rw [h2, crCounts, if_pos rfl]
  omega

lemma crCounts_le (ha : ∀ j, 0 ≤ a j) {j : ℕ} (hj : j ≠ 0) (N : ℕ) :
    (crCounts a K N j : ℝ) ≤ a j * N := by
  rw [crCounts, if_neg hj]
  exact Nat.floor_le (mul_nonneg (ha j) (Nat.cast_nonneg _))

lemma crCounts_gt {j : ℕ} (hj : j ≠ 0) (N : ℕ) : a j * N - 1 < (crCounts a K N j : ℝ) := by
  rw [crCounts, if_neg hj]
  linarith [Nat.lt_floor_add_one (a j * N)]

lemma crCounts_zero_ge (ha : ∀ j, 0 ≤ a j) (hs : ∑ j ∈ range K, a j = 1) (hK : 1 ≤ K) (N : ℕ) :
    a 0 * N ≤ (crCounts a K N 0 : ℝ) := by
  have h1 := crCounts_floor_sum_le ha hs hK N
  rw [crCounts, if_pos rfl, Nat.cast_sub h1]
  push_cast
  have hsum : a 0 * N = N - (∑ i ∈ Finset.Ico 1 K, a i) * N := by
    have := cr_sum_range_eq_zero_add a hK
    rw [hs] at this
    have e : a 0 = 1 - ∑ i ∈ Finset.Ico 1 K, a i := by linarith
    rw [e]; ring
  rw [hsum, Finset.sum_mul]
  have : ∑ i ∈ Finset.Ico 1 K, (⌊a i * N⌋₊ : ℝ) ≤ ∑ i ∈ Finset.Ico 1 K, a i * N :=
    Finset.sum_le_sum fun i _ => Nat.floor_le (mul_nonneg (ha i) (Nat.cast_nonneg _))
  linarith

lemma crCounts_zero_le (ha : ∀ j, 0 ≤ a j) (hs : ∑ j ∈ range K, a j = 1) (hK : 1 ≤ K) (N : ℕ) :
    (crCounts a K N 0 : ℝ) ≤ a 0 * N + K := by
  have h1 := crCounts_floor_sum_le ha hs hK N
  rw [crCounts, if_pos rfl, Nat.cast_sub h1]
  push_cast
  have hsum : a 0 * N = N - (∑ i ∈ Finset.Ico 1 K, a i) * N := by
    have := cr_sum_range_eq_zero_add a hK
    rw [hs] at this
    have e : a 0 = 1 - ∑ i ∈ Finset.Ico 1 K, a i := by linarith
    rw [e]; ring
  rw [hsum, Finset.sum_mul]
  have h2 : ∑ i ∈ Finset.Ico 1 K, (a i * N - 1) ≤ ∑ i ∈ Finset.Ico 1 K, (⌊a i * N⌋₊ : ℝ) :=
    Finset.sum_le_sum fun i _ => by linarith [Nat.lt_floor_add_one (a i * N)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one] at h2
  have hK' : ((K - 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast Nat.sub_le K 1
  linarith

/-- `|n_j - a_j N| ≤ K` for every cell `j < K`. -/
lemma crCounts_abs_le (ha : ∀ j, 0 ≤ a j) (hs : ∑ j ∈ range K, a j = 1) (hK : 1 ≤ K) (N j : ℕ) :
    |(crCounts a K N j : ℝ) - a j * N| ≤ K := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    have h1 := crCounts_zero_ge ha hs hK N
    have h2 := crCounts_zero_le ha hs hK N
    rw [abs_le]; constructor <;> linarith
  · have h1 := crCounts_le (K := K) ha h.ne' N
    have h2 := crCounts_gt (a := a) (K := K) h.ne' N
    rw [abs_le]; constructor <;> linarith

/-- `Σ_j j n_j ≤ N Σ_j j a_j`. -/
lemma crCounts_wsum_le (ha : ∀ j, 0 ≤ a j) (N : ℕ) :
    ∑ j ∈ range K, (j : ℝ) * crCounts a K N j ≤ N * ∑ j ∈ range K, (j : ℝ) * a j := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; simp
  · have := crCounts_le (K := K) ha h.ne' N
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith

/-- `N Σ_j j a_j - K² ≤ Σ_j j n_j`. -/
lemma crCounts_wsum_ge (N : ℕ) :
    N * ∑ j ∈ range K, (j : ℝ) * a j - (K : ℝ) ^ 2 ≤ ∑ j ∈ range K, (j : ℝ) * crCounts a K N j := by
  have h1 : ∀ j ∈ range K, (N : ℝ) * ((j : ℝ) * a j) - K ≤ (j : ℝ) * crCounts a K N j := by
    intro j hj
    have hjK : (j : ℝ) ≤ K := by exact_mod_cast (Finset.mem_range.1 hj).le
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp
    · have := crCounts_gt (a := a) (K := K) h.ne' N
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
  have h2 := Finset.sum_le_sum h1
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
    at h2
  nlinarith [h2]

end Counts

end

end Census
end IIT
