/-
Census: the effect box of a triple in flipped coordinates, its probability, and its independence
from the summands of the other (super)blocks.

`tp_boxW s S` constrains the columns of `S` on the rows of the `S`-block of `s`: the entry at `s`
lies in `Jb (s j)` and the entries at the other seven rows in `Jb (!s j)`; after the flip this is
the effect box `tp_effBoxZ` (`tp_boxW_effBox`).  Its probability is `(1/100)^24`
(`tp_cubeM_boxW`), two boxes of disjoint triples are independent (`tp_cubeM_boxW_inter`), and a box
is an event of the rows of any (super)block of `s` containing the `S`-block (`tp_box_rows`).
-/
import IIT.Census.ThmP3Det
import IIT.Census.PairSecond2

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

noncomputable section

variable {N : ℕ}

/-- The constraint on the entry `(r, j)`. -/
def tp_T (s : State N) (S : Finset (Fin N)) (r : State N) (j : Fin N) : Set ℝ :=
  if r ∈ agree Sᶜ s ∧ j ∈ S then (if r = s then Jb (s j) else Jb (!s j)) else Set.univ

/-- The effect box of the triple `S` in flipped coordinates. -/
def tp_boxW (s : State N) (S : Finset (Fin N)) : Set (Param N) := {w | ∀ r j, w r j ∈ tp_T s S r j}

/-- The probability of the effect box. -/
def tp_pE : ℝ := (1 / 100) ^ 24

lemma tp_pE_pos : 0 < tp_pE := by norm_num [tp_pE]

lemma tp_pE_le_one : tp_pE ≤ 1 := by norm_num [tp_pE]

lemma tp_measurableSet_T (s : State N) (S : Finset (Fin N)) (r : State N) (j : Fin N) :
    MeasurableSet (tp_T s S r j) := by
  unfold tp_T Jb
  split_ifs <;> first | exact measurableSet_Ioo | exact MeasurableSet.univ

lemma tp_measurableSet_boxW (s : State N) (S : Finset (Fin N)) : MeasurableSet (tp_boxW s S) :=
  ps_measurableSet_rows _ fun r j => tp_measurableSet_T s S r j

lemma tp_flipC_Jb_not (b : Bool) {x : ℝ} (hx : x ∈ Jb (!b)) :
    flipC b x ∈ Set.Ioo (0 : ℝ) (1 / 100) := by
  cases b <;> simp [Jb, flipC] at hx ⊢ <;> constructor <;> linarith [hx.1, hx.2]

/-- The box gives the effect box of the unflipped parameters. -/
theorem tp_boxW_effBox {s : State N} {S : Finset (Fin N)} {w : Param N} (hw : w ∈ tp_boxW s S) :
    tp_effBoxZ (flipP s w) s S := by
  refine ⟨fun j hj => ?_, fun r hr hrs j hj => ?_⟩
  · have h := hw s j
    rw [tp_T, ite_eq_left ⟨self_mem_agree _ _, hj⟩, ite_eq_left rfl] at h
    exact (flipC_Jb _ h).1
  · have h := hw r j
    rw [tp_T, ite_eq_left ⟨hr, hj⟩, ite_eq_right hrs] at h
    exact (tp_flipC_Jb_not _ h).2

lemma tp_prod_row (s : State N) {S : Finset (Fin N)} (hS : S.card = 3) (r : State N) :
    ∏ j, unif (tp_T s S r j) =
      if r ∈ agree Sᶜ s then ENNReal.ofReal (1 / 100) ^ 3 else 1 := by
  by_cases hr : r ∈ agree Sᶜ s
  · rw [ite_eq_left hr, ← hS, ← prod_const, ← prod_filter_mul_prod_filter_not univ (fun j => j ∈ S)]
    have h1 : ∏ j ∈ univ.filter (fun j => j ∈ S), unif (tp_T s S r j) =
        ∏ _j ∈ S, ENNReal.ofReal (1 / 100) := by
      rw [filter_mem_eq_inter, univ_inter]
      refine prod_congr rfl fun j hj => ?_
      rw [tp_T, ite_eq_left ⟨hr, hj⟩]
      split_ifs <;> exact ps_unif_Jb _
    have h2 : ∏ j ∈ univ.filter (fun j => ¬ j ∈ S), unif (tp_T s S r j) = 1 := by
      refine prod_eq_one fun j hj => ?_
      rw [tp_T, ite_eq_right (fun h => (mem_filter.1 hj).2 h.2), measure_univ]
    rw [h1, h2, mul_one]
  · rw [ite_eq_right hr]
    refine prod_eq_one fun j _ => ?_
    rw [tp_T, ite_eq_right (fun h => hr h.1), measure_univ]

/-- **The probability of the effect box.** -/
theorem tp_cubeM_boxW (s : State N) {S : Finset (Fin N)} (hS : S.card = 3) :
    cubeM N (tp_boxW s S) = ENNReal.ofReal tp_pE := by
  rw [tp_boxW, ps_cubeM_rows]
  simp_rw [tp_prod_row s hS]
  rw [← prod_filter, prod_const, filter_mem_eq_inter, univ_inter, tp_card_block, hS, ← pow_mul,
    ← ENNReal.ofReal_pow (by norm_num), tp_pE]
  norm_num

lemma tp_real_boxW (s : State N) {S : Finset (Fin N)} (hS : S.card = 3) :
    (cubeM N).real (tp_boxW s S) = tp_pE := by
  rw [measureReal_def, tp_cubeM_boxW s hS, ENNReal.toReal_ofReal tp_pE_pos.le]

/-- **Boxes of disjoint triples are independent.** -/
theorem tp_cubeM_boxW_inter (s : State N) {S S' : Finset (Fin N)} (hd : Disjoint S S') :
    cubeM N (tp_boxW s S ∩ tp_boxW s S') = cubeM N (tp_boxW s S) * cubeM N (tp_boxW s S') := by
  have e : tp_boxW s S ∩ tp_boxW s S' = {w | ∀ r j, w r j ∈ tp_T s S r j ∩ tp_T s S' r j} := by
    ext w
    simp only [tp_boxW, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h r j => ⟨h.1 r j, h.2 r j⟩, fun h => ⟨fun r j => (h r j).1, fun r j => (h r j).2⟩⟩
  rw [e, tp_boxW, tp_boxW, ps_cubeM_rows, ps_cubeM_rows, ps_cubeM_rows, ← prod_mul_distrib]
  refine prod_congr rfl fun r _ => ?_
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  by_cases hj : j ∈ S
  · have hj' : j ∉ S' := disjoint_left.1 hd hj
    rw [show tp_T s S' r j = Set.univ by rw [tp_T, ite_eq_right (fun h => hj' h.2)],
      Set.inter_univ, measure_univ, mul_one]
  · rw [show tp_T s S r j = Set.univ by rw [tp_T, ite_eq_right (fun h => hj h.2)],
      Set.univ_inter, measure_univ, one_mul]

lemma tp_real_boxW_inter (s : State N) {S S' : Finset (Fin N)} (hS : S.card = 3)
    (hS' : S'.card = 3) (hd : Disjoint S S') :
    (cubeM N).real (tp_boxW s S ∩ tp_boxW s S') = tp_pE ^ 2 := by
  rw [measureReal_def, tp_cubeM_boxW_inter s hd, tp_cubeM_boxW s hS, tp_cubeM_boxW s hS',
    ENNReal.toReal_mul, ENNReal.toReal_ofReal tp_pE_pos.le, sq]

/-! ### Boxes as events of the block rows -/

section Rows

variable {n : ℕ} {E : Fin n → Fin N} {K : Type*} [Fintype K] {bits : K → Fin n → Bool}
  (hE : Function.Injective E) (hb : Function.Injective bits) (hK : Fintype.card K = 2 ^ n)

include hE hb hK

/-- Every row agreeing with `s` off the image of `E` is a row of the superblock of `s`. -/
lemma tp_row_of_agree (s : State N) {r : State N} (hr : r ∈ agree (bg_U E)ᶜ s) :
    bg_eqv bits hE hb hK (((bg_eqv bits hE hb hK).symm s).1,
      ((bg_eqv bits hE hb hK).symm r).2) = r := by
  set g := bg_eqv bits hE hb hK
  have hr' : g (g.symm r) = r := g.apply_symm_apply r
  have hs' : g (g.symm s) = s := g.apply_symm_apply s
  funext j
  by_cases hj : j ∈ bg_U E
  · obtain ⟨q, rfl⟩ := bg_mem_U E hj
    have := congrFun hr' (E q)
    simp only [g, bg_eqv_apply] at this ⊢
    rw [bg_row_E bits hE] at this ⊢
    exact this
  · have h1 := congrFun hs' j
    simp only [g, bg_eqv_apply] at h1 ⊢
    rw [bg_row_out bits _ _ hj] at h1 ⊢
    rw [h1]
    exact ((mem_agree.1 hr) j (mem_compl.2 hj)).symm

/-- **A box on the rows agreeing with `s` off the image of `E` is an event of the rows of the
superblock of `s`.** -/
theorem tp_box_rows (s : State N) (T : State N → Fin N → Set ℝ)
    (hT : ∀ r j, r ∉ agree (bg_U E)ᶜ s → T r j = Set.univ) :
    {w : Param N | ∀ r j, w r j ∈ T r j} = bg_blockRows (bg_eqv bits hE hb hK) s ⁻¹'
      {y | ∀ u j, y u j ∈ T (bg_eqv bits hE hb hK (((bg_eqv bits hE hb hK).symm s).1, u)) j} := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, bg_blockRows]
  constructor
  · intro h u j; exact h _ j
  · intro h r j
    by_cases hr : r ∈ agree (bg_U E)ᶜ s
    · have := h ((bg_eqv bits hE hb hK).symm r).2 j
      rwa [tp_row_of_agree hE hb hK s hr] at this
    · rw [hT r j hr]; trivial

end Rows

lemma tp_T_univ {s : State N} {S U : Finset (Fin N)} (hSU : S ⊆ U) (r : State N) (j : Fin N)
    (hr : r ∉ agree Uᶜ s) : tp_T s S r j = Set.univ := by
  rw [tp_T, ite_eq_right]
  rintro ⟨h1, _⟩
  exact hr (agree_subset_agree (compl_subset_compl.2 hSU) s h1)

end

end Census
end IIT
