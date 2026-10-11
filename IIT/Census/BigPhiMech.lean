/-
Census of complexes: the mechanism-level `Φ` of a candidate system is bounded by its cause
ratios.

`PhiOfAt T S u s σ` is at most `(2 ^ 2 ^ |S| + 2 ^ (|S| + 1)) * B` as soon as every cause
ratio `pos (log₂ (causeFwdAt / partCauseFwdAt))` over all mechanisms, purviews, purview states
and partitions is at most `B`.  The three steps are: relations and self-relations are bounded
by distinctions, and there are at most `2 ^ |S|` distinctions; `φ_d ≤ φ_c` and the maximum
over purviews and partitions is bounded termwise; the cause selectivity `causeRepAt` is at
most one.  Finally a product ratio is bounded by the sum of the relative factor gaps.
-/
import IIT.Cond
import IIT.Census.BigPhiBridge

namespace IIT
namespace Census

open Finset
open scoped Classical

variable {N : ℕ}

/-! ### The cause selectivity is a probability -/

lemma causeFwdAt_congr_of_agree (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (Z : Finset (Fin N)) {z z' : State N} (M : Finset (Fin N)) (m : State N)
    (h : ∀ k ∈ Z, z k = z' k) :
    causeFwdAt T S u Z z M m = causeFwdAt T S u Z z' M m := by
  unfold causeFwdAt
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  refine effUnit_congr_of_agree (T := T) (fun j hj => ?_) i (m i)
  unfold condState merge
  by_cases hjS : j ∈ S
  · have hjZ : j ∈ Z := by
      rcases Finset.mem_union.1 hj with h1 | h1
      · exact h1
      · exact absurd hjS (Finset.mem_compl.1 h1)
    simp [hjS, h j hjZ]
  · simp [hjS]

lemma causeFwdAt_le_normalizer (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (Z : Finset (Fin N)) (z : State N) (M : Finset (Fin N)) (m : State N) :
    causeFwdAt T S u Z z M m ≤ (2 : ℝ) ^ Z.card * uncCauseFwdAt T S u Z M m := by
  have hZN : Z.card ≤ N := by simpa using Finset.card_le_univ Z
  have hcongr : ∀ s ∈ agree Z z, causeFwdAt T S u Z s M m = causeFwdAt T S u Z z M m :=
    fun s hs => causeFwdAt_congr_of_agree T S u Z M m (fun k hk => (mem_agree.1 hs) k hk)
  have hfib : ∑ s ∈ agree Z z, causeFwdAt T S u Z s M m
      = ((2 : ℝ) ^ (N - Z.card)) * causeFwdAt T S u Z z M m := by
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul, card_agree]
    norm_cast
  have hsub : ∑ s ∈ agree Z z, causeFwdAt T S u Z s M m ≤
      ∑ s : State N, causeFwdAt T S u Z s M m :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun s _ _ => causeFwdAt_nonneg T S u Z s M m
  rw [hfib] at hsub
  have hposA : (0 : ℝ) < (2 : ℝ) ^ (N - Z.card) := by positivity
  have hpow : ((2 : ℝ) ^ (N - Z.card)) * ((2 : ℝ) ^ Z.card) = (2 : ℝ) ^ N := by
    rw [← pow_add]
    congr 1
    omega
  have key : (2 : ℝ) ^ Z.card * ((∑ s : State N, causeFwdAt T S u Z s M m) / (2 : ℝ) ^ N)
      = (∑ s : State N, causeFwdAt T S u Z s M m) / (2 : ℝ) ^ (N - Z.card) := by
    rw [← hpow]
    field_simp
  rw [uncCauseFwdAt, avgOverStates, key, le_div_iff₀ hposA, mul_comm]
  exact hsub

/-- **The conditioned cause selectivity is at most one.** -/
theorem causeRepAt_le_one (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (Z : Finset (Fin N)) (zz : State N) (M : Finset (Fin N)) (m : State N) :
    causeRepAt T S u Z zz M m ≤ 1 := by
  have hnn : 0 ≤ (2 : ℝ) ^ Z.card * uncCauseFwdAt T S u Z M m :=
    mul_nonneg (by positivity) (uncCauseFwdAt_nonneg T S u Z M m)
  rcases eq_or_lt_of_le hnn with h | h
  · rw [causeRepAt, ← h, div_zero]
    norm_num
  · exact (div_le_one h).2 (causeFwdAt_le_normalizer T S u Z zz M m)

lemma phiCofPartitionAt_le_ratio (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (Z : Finset (Fin N)) (zz : State N) (M : Finset (Fin N)) (m : State N)
    (θ : Partition N M Z) :
    phiCofPartitionAt T S u Z zz M m θ ≤
      pos (Real.logb 2 (causeFwdAt T S u Z zz M m / partCauseFwdAt T S u Z zz M m θ)) :=
  mul_le_of_le_one_left (pos_nonneg _) (causeRepAt_le_one T S u Z zz M m)

/-- `φ_c(m)` is at most any bound on the cause ratio over all purviews, states and
partitions. -/
lemma phiCmechAt_le_of_forall (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
    (M : Finset (Fin N)) (m : State N) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ Z ⊆ S, ∀ zz : State N, ∀ θ : Partition N M Z,
      pos (Real.logb 2 (causeFwdAt T S u Z zz M m / partCauseFwdAt T S u Z zz M m θ)) ≤ B) :
    phiCmechAt T S u M m ≤ B := by
  rw [phiCmechAt]
  refine Finset.sup'_le _ _ fun Z hZ => ?_
  rw [phiCpurviewAt]
  refine Finset.sup'_le _ _ fun zz _ => ?_
  rw [phiCatAt]
  exact sup'OrZero_le hB fun θ _ =>
    (phiCofPartitionAt_le_ratio T S u Z zz M m θ).trans (h Z (Finset.mem_powerset.1 hZ) zz θ)

/-! ### Relations are bounded by distinctions -/

lemma relPhiOrZero_le_of_mem {d : Finset (Distinction N)} {D : Distinction N} (hD : D ∈ d) :
    relPhiOrZero d ≤ D.phi := by
  rw [relPhiOrZero]
  split
  · exact relPhi_le_phi _ hD
  · rename_i hne
    exact absurd ⟨D, hD⟩ hne

lemma card_relationSetsOf_le (D : Finset (Distinction N)) :
    (relationSetsOf D).card ≤ 2 ^ D.card := by
  rw [relationSetsOf]
  exact (Finset.card_filter_le _ _).trans (Finset.card_powerset D).le

lemma card_selfRelationsOf_le (D : Finset (Distinction N)) :
    (selfRelationsOf D).card ≤ D.card := by
  rw [selfRelationsOf]
  exact Finset.card_filter_le _ _

/-- **`Φ` of a structure is at most (number of distinctions, relation sets and
self-relations) times a bound on the distinctions.** -/
theorem PhiOfStructure_le (D : Finset (Distinction N)) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ d ∈ D, d.phi ≤ B) :
    PhiOfStructure D ≤ ((D.card : ℝ) + 2 ^ D.card + D.card) * B := by
  have h1 : ∑ d ∈ D, d.phi ≤ (D.card : ℝ) * B := by
    have := Finset.sum_le_card_nsmul D (fun d => d.phi) B h
    simpa [nsmul_eq_mul] using this
  have h2 : ∑ d ∈ relationSetsOf D, relPhiOrZero d ≤ (2 : ℝ) ^ D.card * B := by
    have hle : ∀ d ∈ relationSetsOf D, relPhiOrZero d ≤ B := by
      intro d hd
      rw [relationSetsOf] at hd
      obtain ⟨hdP, ⟨D0, hD0⟩, -, -⟩ := Finset.mem_filter.1 hd
      exact (relPhiOrZero_le_of_mem hD0).trans (h D0 (Finset.mem_powerset.1 hdP hD0))
    have := Finset.sum_le_card_nsmul (relationSetsOf D) relPhiOrZero B hle
    rw [nsmul_eq_mul] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ hB)
    exact_mod_cast card_relationSetsOf_le D
  have h3 : ∑ d ∈ selfRelationsOf D, selfRelPhi d ≤ (D.card : ℝ) * B := by
    have hle : ∀ d ∈ selfRelationsOf D, selfRelPhi d ≤ B := by
      intro d hd
      rw [selfRelationsOf] at hd
      exact (selfRelPhi_le_phi d).trans (h d (Finset.mem_filter.1 hd).1)
    have := Finset.sum_le_card_nsmul (selfRelationsOf D) selfRelPhi B hle
    rw [nsmul_eq_mul] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ hB)
    exact_mod_cast card_selfRelationsOf_le D
  rw [PhiOfStructure]
  nlinarith [h1, h2, h3]

/-- **There are at most `2 ^ |S|` conditioned distinctions.** -/
theorem card_distinctionsAt_le (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (σ : SelectorAt T S u s) : (distinctionsAt T S u s σ).card ≤ 2 ^ S.card := by
  rw [distinctionsAt]
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_attach, distinctionMechsAt]
  exact (Finset.card_filter_le _ _).trans (Finset.card_powerset S).le

lemma mem_distinctionsAt_phi {T : UnitTPM N} {S : Finset (Fin N)} {u s : State N}
    {σ : SelectorAt T S u s} {d : Distinction N} (hd : d ∈ distinctionsAt T S u s σ) :
    d.mech ⊆ S ∧ d.phi = phiDAt T S u d.mech s := by
  rw [distinctionsAt] at hd
  obtain ⟨⟨M, hM⟩, -, rfl⟩ := Finset.mem_image.1 hd
  exact ⟨(mem_distinctionMechsAt.1 hM).1, rfl⟩

/-- **Theorem B, steps (a)-(c).**  If every cause ratio of the candidate `S` is at most
`B`, then its conditioned `Φ` is at most `(2 ^ 2 ^ |S| + 2 ^ (|S| + 1)) * B`. -/
theorem PhiOfAt_le_of_ratio (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N)
    (σ : SelectorAt T S u s) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ M ⊆ S, ∀ Z ⊆ S, ∀ zz : State N, ∀ θ : Partition N M Z,
      pos (Real.logb 2 (causeFwdAt T S u Z zz M s / partCauseFwdAt T S u Z zz M s θ)) ≤ B) :
    PhiOfAt T S u s σ ≤ ((2 : ℝ) ^ (2 ^ S.card) + 2 ^ (S.card + 1)) * B := by
  rw [PhiOfAt]
  set D := distinctionsAt T S u s σ with hDdef
  have hd : ∀ d ∈ D, d.phi ≤ B := by
    intro d hdD
    obtain ⟨hmS, hphi⟩ := mem_distinctionsAt_phi hdD
    rw [hphi, phiDAt]
    exact (min_le_left _ _).trans
      (phiCmechAt_le_of_forall T S u d.mech s hB (h d.mech hmS))
  refine (PhiOfStructure_le D hB hd).trans (mul_le_mul_of_nonneg_right ?_ hB)
  have hc : D.card ≤ 2 ^ S.card := card_distinctionsAt_le T S u s σ
  have hc' : (D.card : ℝ) ≤ (2 : ℝ) ^ S.card := by exact_mod_cast hc
  have hp : (2 : ℝ) ^ D.card ≤ (2 : ℝ) ^ (2 ^ S.card) :=
    pow_le_pow_right₀ (by norm_num) hc
  have hq : (2 : ℝ) ^ (S.card + 1) = 2 * (2 : ℝ) ^ S.card := by ring
  rw [hq]
  linarith

/-! ### A product ratio against its factor gaps -/

/-- **The positive part of `log₂ (∏ a / ∏ b)` is at most the sum of the relative gaps.** -/
theorem pos_logb_prod_div_le {ι : Type*} (M : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ M, 0 < a i) (hb : ∀ i ∈ M, 0 < b i) :
    pos (Real.logb 2 ((∏ i ∈ M, a i) / ∏ i ∈ M, b i)) ≤
      ∑ i ∈ M, |a i - b i| / (b i * Real.log 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hrhs : 0 ≤ ∑ i ∈ M, |a i - b i| / (b i * Real.log 2) :=
    Finset.sum_nonneg fun i hi => div_nonneg (abs_nonneg _) (mul_pos (hb i hi) hl2).le
  refine pos_le hrhs ?_
  have hA : (∏ i ∈ M, a i) ≠ 0 := (Finset.prod_pos ha).ne'
  have hB : (∏ i ∈ M, b i) ≠ 0 := (Finset.prod_pos hb).ne'
  have hlog : Real.log ((∏ i ∈ M, a i) / ∏ i ∈ M, b i) =
      ∑ i ∈ M, (Real.log (a i) - Real.log (b i)) := by
    rw [Real.log_div hA hB, Real.log_prod (fun i hi => (ha i hi).ne'),
      Real.log_prod (fun i hi => (hb i hi).ne'), Finset.sum_sub_distrib]
  rw [Real.logb, hlog, Finset.sum_div]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [← div_div]
  refine div_le_div_of_nonneg_right ?_ hl2.le
  have hai := ha i hi
  have hbi := hb i hi
  rw [← Real.log_div hai.ne' hbi.ne']
  refine (Real.log_le_sub_one_of_pos (div_pos hai hbi)).trans ?_
  rw [div_sub_one hbi.ne']
  exact div_le_div_of_nonneg_right (le_abs_self _) hbi.le

end Census
end IIT
