/-
Census: the method-of-types lower bound for a general coordinate space.

`B1Chernoff.type_event_ge` is stated for real coordinates under Lebesgue measure.  The lower-bound event
E_X of regime X (W7 §3, coarse design `g5_lbX_cert_coarse.py`) is a joint type of PAIRS of entries
(y_{r0,j}, y_{r1,j}) ∈ ℝ², so the same bound is needed for an arbitrary measurable coordinate space `E` with a
σ-finite measure `μ` and the product measure `Measure.pi (fun _ => μ)` (gap G5, second bullet).  The proof is
`type_event_ge`'s, with `volume_pi_pi` replaced by `Measure.pi_pi`; the combinatorial part
(`fibTypeCount`, `type_exp_le`) is reused unchanged.
-/
import IIT.Census.B1Chernoff

namespace IIT
namespace Census

open MeasureTheory Finset

section TypeGen

variable {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] {N k : ℕ}

/-- The box of coordinate vectors whose `i`-th coordinate lies in the cell `σ i`. -/
def genTypeBox (I : Fin k → Set E) (σ : Fin N → Fin k) : Set (Fin N → E) :=
  Set.univ.pi fun i => I (σ i)

lemma genTypeBox_sub_event (I : Fin k → Set E) [∀ j, DecidablePred (· ∈ I j)]
    (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) {n : Fin k → ℕ} {σ : Fin N → Fin k}
    (hσ : fibType σ = n) :
    genTypeBox I σ ⊆ {v | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} := by
  intro v hv j
  have hv' : ∀ i, v i ∈ I (σ i) := fun i => hv i (Set.mem_univ i)
  show (univ.filter fun i => v i ∈ I j).card = n j
  rw [← hσ]
  unfold fibType
  congr 1
  refine Finset.filter_congr fun i _ => ⟨fun h => ?_, fun h => h ▸ hv' i⟩
  by_contra hne
  exact Set.disjoint_left.1 (hdisj hne) (hv' i) h

lemma genTypeBox_disjoint {I : Fin k → Set E} (hdisj : Pairwise fun j j' => Disjoint (I j) (I j'))
    {σ σ' : Fin N → Fin k} (h : σ ≠ σ') : Disjoint (genTypeBox I σ) (genTypeBox I σ') := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  rw [Set.disjoint_left]
  intro v hv hv'
  exact Set.disjoint_left.1 (hdisj hi) (hv i (Set.mem_univ i)) (hv' i (Set.mem_univ i))

lemma measure_genTypeBoxes (I : Fin k → Set E) (hI : ∀ j, MeasurableSet (I j))
    (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) (ℓ : Fin k → ℝ)
    (hℓ : ∀ j, μ (I j) = ENNReal.ofReal (ℓ j)) (hℓ0 : ∀ j, 0 ≤ ℓ j) (n : Fin k → ℕ) :
    Measure.pi (fun _ : Fin N => μ)
        (⋃ σ ∈ univ.filter (fun σ : Fin N → Fin k => fibType σ = n), genTypeBox I σ) =
      ENNReal.ofReal (fibTypeCount N k n * ∏ j, ℓ j ^ n j) := by
  rw [measure_biUnion_finset (fun σ _ σ' _ h => genTypeBox_disjoint hdisj h)
    (fun σ _ => MeasurableSet.univ_pi fun i => hI (σ i))]
  have hbox : ∀ σ ∈ univ.filter (fun σ : Fin N → Fin k => fibType σ = n),
      Measure.pi (fun _ : Fin N => μ) (genTypeBox I σ) = ENNReal.ofReal (∏ j, ℓ j ^ n j) := by
    intro σ hσ
    rw [genTypeBox, Measure.pi_pi, Finset.prod_congr rfl fun i _ => hℓ (σ i),
      ← ENNReal.ofReal_prod_of_nonneg fun i _ => hℓ0 _, prod_comp_eq_prod_pow_fibType,
      (Finset.mem_filter.1 hσ).2]
  rw [Finset.sum_congr rfl hbox, Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  rfl

/-- **Type event lower bound, general coordinate space.** -/
theorem type_event_ge_gen (I : Fin k → Set E) [∀ j, DecidablePred (· ∈ I j)]
    (hI : ∀ j, MeasurableSet (I j)) (hdisj : Pairwise fun j j' => Disjoint (I j) (I j'))
    (ℓ : Fin k → ℝ) (hℓ : ∀ j, μ (I j) = ENNReal.ofReal (ℓ j)) (hℓpos : ∀ j, 0 < ℓ j)
    (n : Fin k → ℕ) (hn : ∑ j, n j = N) :
    ENNReal.ofReal (Real.exp (-(N * ∑ j, ((n j : ℝ) / N) * Real.log (((n j : ℝ) / N) / ℓ j))) /
        ((N : ℝ) + 1) ^ k) ≤
      Measure.pi (fun _ : Fin N => μ) {v : Fin N → E | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} :=
  calc _ ≤ ENNReal.ofReal (fibTypeCount N k n * ∏ j, ℓ j ^ n j) :=
        ENNReal.ofReal_le_ofReal (type_exp_le ℓ hℓpos n hn)
    _ = Measure.pi (fun _ : Fin N => μ)
          (⋃ σ ∈ univ.filter (fun σ : Fin N → Fin k => fibType σ = n), genTypeBox I σ) :=
        (measure_genTypeBoxes μ I hI hdisj ℓ hℓ (fun j => (hℓpos j).le) n).symm
    _ ≤ _ := measure_mono (Set.iUnion₂_subset fun _ hσ =>
        genTypeBox_sub_event I hdisj (Finset.mem_filter.1 hσ).2)

end TypeGen

/-! ### Joint types of two rows of the cube -/

section PairType

variable {N k : ℕ}

/-- A type count is a measurable condition. -/
lemma measurableSet_card_filter {X : Type*} [MeasurableSpace X] (p : Fin N → X → Prop)
    [∀ i, DecidablePred (p i)] (hp : ∀ i, MeasurableSet {x | p i x}) (m : ℕ) :
    MeasurableSet {x | (univ.filter fun i => p i x).card = m} := by
  classical
  have h : {x | (univ.filter fun i => p i x).card = m} =
      ⋃ A : Finset (Fin N), ⋃ (_ : A.card = m),
        ⋂ i, (if i ∈ A then {x | p i x} else {x | p i x}ᶜ) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, exists_prop]
    constructor
    · intro hx
      refine ⟨univ.filter fun i => p i x, hx, fun i => ?_⟩
      by_cases hi : p i x
      · rw [if_pos (by simp [hi])]; exact hi
      · rw [if_neg (by simp [hi])]; exact hi
    · rintro ⟨A, hA, hx⟩
      have : (univ.filter fun i => p i x) = A := by
        ext i
        simp only [mem_filter, mem_univ, true_and]
        have := hx i
        by_cases hi : i ∈ A
        · rw [if_pos hi] at this; exact ⟨fun _ => hi, fun _ => this⟩
        · rw [if_neg hi] at this; exact ⟨fun h => absurd h this, fun h => absurd h hi⟩
      rw [this]; exact hA
  rw [h]
  refine MeasurableSet.iUnion fun A => MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun i => ?_
  split_ifs
  · exact hp i
  · exact (hp i).compl

/-- The joint law of two distinct rows is the product of the row laws. -/
lemma map_two_rows {r0 r1 : State N} (h : r0 ≠ r1) :
    (cubeM N).map (fun w : Param N => (w r0, w r1)) = (rowM N).prod (rowM N) := by
  have hm : Measurable (fun w : Param N => (w r0, w r1)) :=
    (measurable_pi_apply r0).prodMk (measurable_pi_apply r1)
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply hm (hs.prod ht)]
  exact cubeM_two_rows h hs ht

/-- **Pair-type lower bound** (gap G5): the joint type of the entries `(y_{r0,i}, y_{r1,i})` of two distinct
rows over cells `I j ⊆ ℝ²`, under `cubeM`. -/
theorem pairType_ge {r0 r1 : State N} (h : r0 ≠ r1) (I : Fin k → Set (ℝ × ℝ))
    [∀ j, DecidablePred (· ∈ I j)] (hI : ∀ j, MeasurableSet (I j))
    (hdisj : Pairwise fun j j' => Disjoint (I j) (I j')) (ℓ : Fin k → ℝ)
    (hℓ : ∀ j, (unif.prod unif) (I j) = ENNReal.ofReal (ℓ j)) (hℓpos : ∀ j, 0 < ℓ j)
    (n : Fin k → ℕ) (hn : ∑ j, n j = N) :
    ENNReal.ofReal (Real.exp (-(N * ∑ j, ((n j : ℝ) / N) * Real.log (((n j : ℝ) / N) / ℓ j))) /
        ((N : ℝ) + 1) ^ k) ≤
      cubeM N {w : Param N | ∀ j, (univ.filter fun i => (w r0 i, w r1 i) ∈ I j).card = n j} := by
  set S : Set ((Fin N → ℝ) × (Fin N → ℝ)) :=
    {ab | ∀ j, (univ.filter fun i => (ab.1 i, ab.2 i) ∈ I j).card = n j}
  have hm : Measurable (fun w : Param N => (w r0, w r1)) :=
    (measurable_pi_apply r0).prodMk (measurable_pi_apply r1)
  have hS : MeasurableSet S := by
    have : S = ⋂ j, {ab : (Fin N → ℝ) × (Fin N → ℝ) |
        (univ.filter fun i => (ab.1 i, ab.2 i) ∈ I j).card = n j} := by
      ext ab; simp [S]
    rw [this]
    refine MeasurableSet.iInter fun j => measurableSet_card_filter
      (fun (i : Fin N) (ab : (Fin N → ℝ) × (Fin N → ℝ)) => (ab.1 i, ab.2 i) ∈ I j) (fun i => ?_) _
    exact (((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)) (hI j)
  have h1 : (rowM N).prod (rowM N) S ≤
      cubeM N {w : Param N | ∀ j, (univ.filter fun i => (w r0 i, w r1 i) ∈ I j).card = n j} := by
    rw [← map_two_rows h, Measure.map_apply hm hS]
    exact le_rfl
  have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin N) (fun _ => unif) (fun _ => unif)
  have h2 : (rowM N).prod (rowM N) S =
      Measure.pi (fun _ : Fin N => unif.prod unif)
        {v : Fin N → ℝ × ℝ | ∀ j, (univ.filter fun i => v i ∈ I j).card = n j} := by
    unfold rowM
    rw [← hmp.measure_preimage_equiv]
    rfl
  exact (h2 ▸ type_event_ge_gen (unif.prod unif) I hI hdisj ℓ hℓ hℓpos n hn).trans h1

end PairType

end Census
end IIT
