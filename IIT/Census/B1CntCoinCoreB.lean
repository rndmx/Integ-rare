/-
Census, B1, W14 work package WP5 (part 10): the coin events `E_k^b` as sets, their disjointness, their
inclusion in `Core_K(2κ0)`, and the probability of one `E_k^b` (independence of disjoint entry sets, GC
tails at the explicit levels, Mills).

No `sorry`.
-/
import IIT.Census.B1CntCoinCoreA

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### The sets -/

/-- `{a λ1 ≤ S_k^b < a λ3}` on `C_0`. -/
def w5Bset (s r0 : State N) (K : Finset (Fin N)) (k : Fin N) (b : Bool) : Set (Param N) :=
  {w | 2 ^ dX N * w5lam1 N ≤ w5S (sensRows s r0) (agree (univ \ K) s) k b w} \
    {w | 2 ^ dX N * w5lam3 N ≤ w5S (sensRows s r0) (agree (univ \ K) s) k b w}

/-- `{a λ2 ≤ S_c^{b'}}` on `C_0`. -/
def w5Gc (s r0 : State N) (K : Finset (Fin N)) (c : Fin N) (b' : Bool) : Set (Param N) :=
  {w | 2 ^ dX N * w5lam2 N ≤ w5S (sensRows s r0) (agree (univ \ K) s) c b' w}

/-- `{a θ ≤ T_j(k)^b}` on `C_j`. -/
def w5Gj (s r0 : State N) (K : Finset (Fin N)) (j k : Fin N) (b : Bool) : Set (Param N) :=
  {w | 2 ^ dX N * w5th N ≤ w5S (sensRows s r0) (agree (univ \ K) (flipAt j s)) k b w}

def w5Bad (s r0 : State N) (K : Finset (Fin N)) (k : Fin N) (b : Bool) : Set (Param N) :=
  (⋃ c ∈ univ.erase k, ⋃ b' ∈ (univ : Finset Bool), w5Gc s r0 K c b') ∪
    ⋃ j ∈ univ \ K, w5Gj s r0 K j k b

def w5Ev (s r0 : State N) (K : Finset (Fin N)) (k : Fin N) (b : Bool) : Set (Param N) :=
  w5Bset s r0 K k b \ w5Bad s r0 K k b

lemma measurableSet_w5Bset (s r0 : State N) (K : Finset (Fin N)) (k : Fin N) (b : Bool) :
    MeasurableSet (w5Bset s r0 K k b) :=
  (measurableSet_w5S_ge _ _ _ _ _).diff (measurableSet_w5S_ge _ _ _ _ _)

lemma measurableSet_w5Gc (s r0 : State N) (K : Finset (Fin N)) (c : Fin N) (b : Bool) :
    MeasurableSet (w5Gc s r0 K c b) := measurableSet_w5S_ge _ _ _ _ _

lemma measurableSet_w5Gj (s r0 : State N) (K : Finset (Fin N)) (j k : Fin N) (b : Bool) :
    MeasurableSet (w5Gj s r0 K j k b) := measurableSet_w5S_ge _ _ _ _ _

lemma measurableSet_w5Bad (s r0 : State N) (K : Finset (Fin N)) (k : Fin N) (b : Bool) :
    MeasurableSet (w5Bad s r0 K k b) :=
  (Finset.measurableSet_biUnion _ fun c _ => Finset.measurableSet_biUnion _ fun b' _ =>
    measurableSet_w5Gc s r0 K c b').union
    (Finset.measurableSet_biUnion _ fun j _ => measurableSet_w5Gj s r0 K j k b)

lemma measurableSet_w5Ev (s r0 : State N) (K : Finset (Fin N)) (k : Fin N) (b : Bool) :
    MeasurableSet (w5Ev s r0 K k b) :=
  (measurableSet_w5Bset s r0 K k b).diff (measurableSet_w5Bad s r0 K k b)

lemma w5S_detOn_ge (F R : Finset (State N)) (k : Fin N) (b : Bool) (t : ℝ) :
    DetOnE (w5E F R k) {w : Param N | t ≤ w5S F R k b w} :=
  w5S_detOn F R k b (Set.Ici t)

/-! ### Inclusion and disjointness -/

lemma w5Ev_core {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (K : Finset (Fin N)) (k : Fin N)
    (b : Bool) (hfar : N ≤ 3 * ham r0 s) (hdM : N - (univ \ K).card = dX N)
    (hd2 : 2 ≤ dX N) (hD : 3 * dX N + 19 ≤ N) (hm16 : 16 ≤ mX N) {w : Param N}
    (hw : w ∈ w5Ev s r0 K k b) : CoreAt N s K k (2 * kap0 N) (w5G f w) := by
  obtain ⟨⟨h1, h3⟩, hbad⟩ := hw
  refine w5_E_core f K k b w hfar hdM hd2 hD hm16 h1 h3 ?_ ?_
  · intro c hc b' hc'
    exact hbad (Or.inl (by
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨c, mem_erase.2 ⟨hc, mem_univ c⟩, b', mem_univ _, hc'⟩))
  · intro j hj hj'
    exact hbad (Or.inr (by
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨j, hj, hj'⟩))

lemma w5_lam_order (hd : 1 ≤ dX N) : 0 < w5lam1 N ∧ w5lam2 N < w5lam1 N := by
  have h0 := w5_kap0_pos hd
  have h1 := w5_kapN_ge N
  have h2 := w5_A0C_nonneg N
  unfold w5lam1 w5lam2
  constructor <;> linarith

lemma w5Ev_disj (s r0 : State N) (K : Finset (Fin N)) (hd : 1 ≤ dX N) {k k' : Fin N} {b b' : Bool}
    (hne : (k, b) ≠ (k', b')) : Disjoint (w5Ev s r0 K k b) (w5Ev s r0 K k' b') := by
  obtain ⟨hl1, hl2⟩ := w5_lam_order hd
  have ha : (0 : ℝ) < 2 ^ dX N := by positivity
  rw [Set.disjoint_left]
  intro w hw hw'
  obtain ⟨⟨h1, _⟩, _⟩ := hw
  obtain ⟨⟨h1', _⟩, hbad'⟩ := hw'
  simp only [Set.mem_ofPred_eq] at h1 h1'
  by_cases hkk : k = k'
  · subst hkk
    have hbb : b' = !b := by
      have : b ≠ b' := fun h => hne (by rw [h])
      cases b <;> cases b' <;> simp_all
    rw [hbb, w5S_not] at h1'
    have : 0 < 2 ^ dX N * w5lam1 N := mul_pos ha hl1
    linarith
  · apply hbad'
    refine Or.inl ?_
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨k, mem_erase.2 ⟨hkk, mem_univ k⟩, b, mem_univ _, ?_⟩
    show 2 ^ dX N * w5lam2 N ≤ _
    have : 2 ^ dX N * w5lam2 N < 2 ^ dX N * w5lam1 N := mul_lt_mul_of_pos_left hl2 ha
    linarith

/-! ### Real-valued measure tools -/

lemma w5_toReal_sub_inter_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (A B : Set α) : (μ A).toReal - (μ (A ∩ B)).toReal ≤ (μ (A \ B)).toReal := by
  have h : μ A ≤ μ (A \ B) + μ (A ∩ B) := by
    calc μ A ≤ μ ((A \ B) ∪ (A ∩ B)) := measure_mono (by
          intro x hx; by_cases h : x ∈ B
          · exact Or.inr ⟨hx, h⟩
          · exact Or.inl ⟨hx, h⟩)
      _ ≤ _ := measure_union_le _ _
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) h
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
  linarith

lemma w5_toReal_diff {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (A B : Set α) : (μ A).toReal - (μ B).toReal ≤ (μ (A \ B)).toReal := by
  have := w5_toReal_sub_inter_le μ A B
  have : (μ (A ∩ B)).toReal ≤ (μ B).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_right)
  linarith

/-! ### Fresh counts of the coin subcubes -/

lemma w5_fresh_card {s r0 : State N} (hfar : N ≤ 3 * ham r0 s) (K : Finset (Fin N)) (t : State N)
    (ht : ham s t ≤ 2) (k : Fin N) (hdM : N - (univ \ K).card = dX N) (hd2 : 2 ≤ dX N)
    (hD : 3 * dX N + 19 ≤ N) :
    (2 : ℝ) ^ dX N - (dX N : ℝ) ^ 2 ≤ ((w5E (sensRows s r0) (agree (univ \ K) t) k).card : ℝ) ∧
      ((w5E (sensRows s r0) (agree (univ \ K) t) k).card : ℝ) ≤ 2 ^ dX N := by
  rw [w5E_card]
  have hc : (agree (univ \ K) t).card = 2 ^ dX N := by rw [card_agree, hdM]
  have hsplit := Finset.card_filter_add_card_filter_not (s := agree (univ \ K) t)
    (fun r => r ∈ sensRows s r0)
  have hS := w5_sens_card_le (r0 := r0) hfar (univ \ K) t ht hdM hd2 hD
  rw [hc] at hsplit
  constructor
  · have : 2 ^ dX N ≤ (dX N) ^ 2 + ((agree (univ \ K) t).filter fun r => r ∉ sensRows s r0).card := by
      omega
    have : ((2 ^ dX N : ℕ) : ℝ) ≤ ((dX N) ^ 2 : ℕ) +
        (((agree (univ \ K) t).filter fun r => r ∉ sensRows s r0).card : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  · have : ((agree (univ \ K) t).filter fun r => r ∉ sensRows s r0).card ≤ 2 ^ dX N := by omega
    exact_mod_cast this

end Census
end IIT
