/-
Census, B1 lemma LT2, module M3 part 4: Lemma D1/D2 (W2 §3), the character decomposition of the light numerators.

* `lt2NumNs w S t i := Σ_v y_{merge S t v, i} P_ns(v)` (the numerator with the special rows removed).
* `lt2G w i R T := Σ_v P_ns(v) y_{v⊕R, i} χ_T(v)`.
* `lt2_D1`: `NumNs(S,t,i) = 2^{-|S|} Σ_{R ⊆ S} Σ_{T ⊆ S} χ_T(t ⊕ R) G_{i,R}(T)`.
* `lt2_D2`: `|NumNs(t₀) - NumNs(t)| ≤ 2^{1-|S|} Σ_{R ⊆ S} Σ_{∅ ≠ T ⊆ S} |G_{i,R}(T)|` (the `T = ∅` part cancels).
* `lt2G_empty`, `lt2G_shift`: `G_{i,∅}(T) = (3/4) m_T + Õ_i(T)`, `G_{i,R}(T) = (1/2) m_T + Ñ⁰ + Ñ¹`.
-/
import IIT.Census.B1LT2Ntail

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- The light numerator (special rows removed). -/
noncomputable def lt2NumNs (w : Param N) (S : Finset (Fin N)) (t : State N) (i : Fin N) : ℝ :=
  ∑ v, clamp01 (w (merge S t v) i) * lt2gNs (w v)

/-- The shifted-entry character sums. -/
noncomputable def lt2G (w : Param N) (i : Fin N) (R T : Finset (Fin N)) : ℝ :=
  ∑ v, lt2gNs (w v) * clamp01 (w (lt2Xor v R) i) * lt2Chi T v

lemma lt2Chi_pair (T : Finset (Fin N)) (a c : State N) :
    lt2Chi T a * lt2Chi T c = ∏ j ∈ T, (if a j = c j then (1 : ℝ) else -1) := by
  unfold lt2Chi; rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  cases a j <;> cases c j <;> norm_num

lemma lt2_powerset_chi (S : Finset (Fin N)) (a c : State N) :
    ∑ T ∈ S.powerset, lt2Chi T a * lt2Chi T c = if ∀ j ∈ S, a j = c j then (2 : ℝ) ^ S.card else 0 := by
  simp_rw [lt2Chi_pair]
  rw [← Finset.prod_one_add]
  split_ifs with h
  · rw [Finset.prod_congr rfl fun j hj => by rw [if_pos (h j hj)], Finset.prod_const]; norm_num
  · push_neg at h
    obtain ⟨j, hj, hne⟩ := h
    exact Finset.prod_eq_zero hj (by rw [if_neg hne]; norm_num)

lemma lt2Xor_eq_iff (v t : State N) (R : Finset (Fin N)) (j : Fin N) :
    lt2Xor v R j = t j ↔ v j = lt2Xor t R j := by
  unfold lt2Xor; split_ifs <;> cases v j <;> cases t j <;> simp

/-- The unique shift `R ⊆ S` with `v ⊕ R = t` on `S`. -/
lemma lt2_merge_unique (S : Finset (Fin N)) (t v : State N) (F : Finset (Fin N) → ℝ) :
    ∑ R ∈ S.powerset, (if ∀ j ∈ S, lt2Xor v R j = t j then F R else 0) =
      F (S.filter fun j => v j ≠ t j) := by
  set R0 := S.filter fun j => v j ≠ t j
  have hR0 : ∀ j ∈ S, lt2Xor v R0 j = t j := by
    intro j hj
    unfold lt2Xor
    by_cases h : v j = t j
    · rw [if_neg (by simp [R0, h])]; exact h
    · rw [if_pos (by simp [R0, hj, h])]; cases hv : v j <;> cases ht : t j <;> simp_all
  rw [Finset.sum_eq_single_of_mem R0 (mem_powerset.2 (filter_subset _ _)) fun R hRp hne => ?_, if_pos hR0]
  rw [if_neg]
  intro hR
  apply hne
  have hRS := mem_powerset.1 hRp
  ext j
  simp only [R0, mem_filter]
  constructor
  · intro hj
    have h := hR j (hRS hj)
    unfold lt2Xor at h; rw [if_pos hj] at h
    exact ⟨hRS hj, by cases hv : v j <;> cases ht : t j <;> simp_all⟩
  · rintro ⟨hjS, hne'⟩
    by_contra hj
    have h := hR j hjS
    unfold lt2Xor at h; rw [if_neg hj] at h
    exact hne' h

lemma lt2Xor_filter_eq_merge (S : Finset (Fin N)) (t v : State N) :
    lt2Xor v (S.filter fun j => v j ≠ t j) = merge S t v := by
  funext j
  unfold lt2Xor merge
  by_cases hj : j ∈ S
  · rw [if_pos hj]
    by_cases h : v j = t j
    · rw [if_neg (by simp [h])]; exact h
    · rw [if_pos (by simp [hj, h])]; cases hv : v j <;> cases ht : t j <;> simp_all
  · rw [if_neg hj, if_neg (by simp [hj])]

/-- **Lemma D1.** -/
theorem lt2_D1 (w : Param N) (S : Finset (Fin N)) (t : State N) (i : Fin N) :
    lt2NumNs w S t i =
      (∑ R ∈ S.powerset, ∑ T ∈ S.powerset, lt2Chi T (lt2Xor t R) * lt2G w i R T) / 2 ^ S.card := by
  have h2 : (2 : ℝ) ^ S.card ≠ 0 := by positivity
  have hv : ∀ v : State N, clamp01 (w (merge S t v) i) * lt2gNs (w v) =
      (∑ R ∈ S.powerset, ∑ T ∈ S.powerset,
        lt2Chi T (lt2Xor t R) * (lt2gNs (w v) * clamp01 (w (lt2Xor v R) i) * lt2Chi T v)) / 2 ^ S.card := by
    intro v
    rw [← lt2Xor_filter_eq_merge S t v,
      ← lt2_merge_unique S t v (fun R => clamp01 (w (lt2Xor v R) i) * lt2gNs (w v)), eq_div_iff h2,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun R _ => ?_
    have hc := lt2_powerset_chi S v (lt2Xor t R)
    have hiff : (∀ j ∈ S, lt2Xor v R j = t j) ↔ ∀ j ∈ S, v j = lt2Xor t R j :=
      forall₂_congr fun j _ => lt2Xor_eq_iff v t R j
    have e : ∑ T ∈ S.powerset, lt2Chi T (lt2Xor t R) * (lt2gNs (w v) * clamp01 (w (lt2Xor v R) i) * lt2Chi T v) =
        (∑ T ∈ S.powerset, lt2Chi T v * lt2Chi T (lt2Xor t R)) * (clamp01 (w (lt2Xor v R) i) * lt2gNs (w v)) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun T _ => by ring
    rw [e, hc]
    by_cases h : ∀ j ∈ S, lt2Xor v R j = t j
    · rw [if_pos h, if_pos (hiff.1 h)]; ring
    · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]; ring
  unfold lt2NumNs
  rw [Finset.sum_congr rfl fun v _ => hv v, ← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  unfold lt2G; rw [Finset.mul_sum]

lemma lt2Chi_empty (v : State N) : lt2Chi ∅ v = 1 := by simp [lt2Chi]

/-- **Lemma D2** (pattern differences; the `T = ∅` part cancels). -/
theorem lt2_D2 (w : Param N) (S : Finset (Fin N)) (t0 t : State N) (i : Fin N) :
    |lt2NumNs w S t0 i - lt2NumNs w S t i| ≤
      2 * (∑ R ∈ S.powerset, ∑ T ∈ S.powerset.filter (fun T => T.Nonempty), |lt2G w i R T|) / 2 ^ S.card := by
  have h2 : (0 : ℝ) < 2 ^ S.card := by positivity
  rw [lt2_D1, lt2_D1, ← sub_div, abs_div, abs_of_pos h2, mul_sum]
  refine div_le_div_of_nonneg_right ?_ h2.le
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun R _ => ?_)
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_filter]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun T _ => ?_)
  rw [← sub_mul, abs_mul]
  split_ifs with hT
  · have : |lt2Chi T (lt2Xor t0 R) - lt2Chi T (lt2Xor t R)| ≤ 2 :=
      (abs_sub _ _).trans (by rw [lt2Chi_abs, lt2Chi_abs]; norm_num)
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  · rw [Finset.not_nonempty_iff_eq_empty.1 hT, lt2Chi_empty, lt2Chi_empty]; simp

/-- `G_{i,∅}(T) = (3/4) m_T + Õ_i(T)`. -/
lemma lt2G_empty (w : Param N) (i : Fin N) (T : Finset (Fin N)) :
    lt2G w i ∅ T = 3 / 4 * lt2mT w T + lt2Ot w (i, T) := by
  unfold lt2G lt2mT lt2Ot
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => by rw [lt2Xor_empty]; ring

/-- `G_{i,R}(T) = (1/2) m_T + Ñ⁰ + Ñ¹` for any class functional `Λ`. -/
lemma lt2G_shift (w : Param N) (Λ : Finset (Fin N)) (i : Fin N) (R T : Finset (Fin N)) :
    lt2G w i R T = 1 / 2 * lt2mT w T + lt2N0 Λ true w (i, R, T) + lt2N0 Λ false w (i, R, T) := by
  have hsplit : ∀ f : State N → ℝ, ∑ v, f v = ∑ v ∈ lt2Om0 Λ true, f v + ∑ v ∈ lt2Om0 Λ false, f v := by
    intro f
    unfold lt2Om0
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun v => lt2Par Λ v = true)]
    congr 1
    refine Finset.sum_congr (by ext v; simp) fun _ _ => rfl
  unfold lt2N0
  rw [add_assoc, ← hsplit, lt2mT, Finset.mul_sum, ← Finset.sum_add_distrib]
  unfold lt2G
  exact Finset.sum_congr rfl fun v _ => by ring

end Census
end IIT
