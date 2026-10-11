/-
Census, B1 lemma LT2, module M6b-3: the private sums of a pair after resampling the private entries.

* `lt2pat a b u v`: the pattern with `a ↦ u`, `b ↦ v`; `merge {a,b} t r` depends only on `(t a, t b)`.
* `lt2_merge_inj_H`: `r ↦ merge {i,o} t r` is injective on `H` (heavy rows are pairwise > 4 apart).
* `lt2PiE_replE`: with `A = Priv(w)`, `Π_i(t)(replE A w η) = Σ_{r ∈ H(w), r_o ≠ t_o} P_ns(w r)(y^η_{merge, i} - 1/2)`.
-/
import IIT.Census.B1LT2SB

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- The pattern `a ↦ u`, `b ↦ v`. -/
def lt2pat (a b : Fin N) (u v : Bool) : State N := fun j => if j = a then u else if j = b then v else false

lemma lt2_merge_pat {a b : Fin N} (hab : a ≠ b) (t r : State N) :
    merge {a, b} t r = merge {a, b} (lt2pat a b (t a) (t b)) r := by
  funext j
  unfold merge lt2pat
  by_cases hja : j = a
  · subst hja; simp
  · by_cases hjb : j = b
    · subst hjb; simp [hja]
    · simp [hja, hjb]

/-- Heavy isolated rows are more than 4 apart. -/
lemma lt2_H_sep {s : State N} {w : Param N} {r r' : State N} (hr : r ∈ lt2H s w) (hr' : r' ∈ lt2H s w)
    (hd : ham r' r ≤ 4) : r' = r := by
  classical
  by_contra hne
  have h1 : 1 ≤ ham r' r := by
    by_contra h0
    push_neg at h0
    apply hne; funext j; by_contra hj
    have : 0 < ham r' r := Finset.card_pos.2 ⟨j, by simp [hj]⟩
    omega
  have hiso := (mem_filter.1 hr).2.2.1
  have hheavy := (mem_filter.1 hr').2.1
  exact lt2_heavy_not_light hheavy (hiso r' h1 hd)

lemma lt2_ham_merge_merge (S : Finset (Fin N)) (t r r' : State N) (h : merge S t r = merge S t r') :
    ham r' r ≤ S.card := by
  unfold ham
  refine Finset.card_le_card fun j hj => ?_
  simp only [mem_filter, mem_univ, true_and] at hj
  by_contra hjS
  have := congrFun h j
  rw [merge_not_mem hjS, merge_not_mem hjS] at this
  exact hj this.symm

/-- **Injectivity on `H`.** -/
lemma lt2_merge_inj_H {s : State N} {w : Param N} {i o : Fin N} (t : State N) {r r' : State N}
    (hr : r ∈ lt2H s w) (hr' : r' ∈ lt2H s w) (h : merge {i, o} t r = merge {i, o} t r') : r = r' := by
  have hd := lt2_ham_merge_merge {i, o} t r r' h
  have hc : ({i, o} : Finset (Fin N)).card ≤ 2 := Finset.card_insert_le _ _
  exact (lt2_H_sep hr hr' (by omega)).symm

/-- **The private sum after resampling the private entries.** -/
theorem lt2PiE_replE (s : State N) (w η : Param N) {i o : Fin N} (t : State N)
    (hio : (i ∈ lt2D1 N ∧ o ∈ lt2D2 N) ∨ (i ∈ lt2D2 N ∧ o ∈ lt2D1 N)) :
    lt2PiE s (replE (lt2Priv s w) w η) i o t =
      ∑ r ∈ (lt2H s w).filter (fun r => r o ≠ t o),
        lt2gNs (w r) * (clamp01 (η (merge {i, o} t r) i) - 1 / 2) := by
  classical
  set A := lt2Priv s w
  set w' := replE A w η
  have hagree : ∀ q ∉ lt2Priv s w, w q.1 q.2 = w' q.1 q.2 := fun q hq => by
    simp only [w', replE]; rw [if_neg (show (q.1, q.2) ∉ A from hq)]
  have hH : lt2H s w' = lt2H s w := lt2H_stop hagree
  unfold lt2PiE
  rw [hH]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨hrH, hro⟩ := mem_filter.1 hr
  have hH' := (mem_filter.1 hrH).2
  have hrow : w' r = w r := funext fun j =>
    (hagree (r, j) (lt2_row_not_Priv (lt2_heavy_not_light hH'.1) (by omega) j)).symm
  have hpriv : (merge {i, o} t r, i) ∈ A := by
    have hPB := (lt2_mem_PB_merge hio).2 hro
    show (merge {i, o} t r, i) ∈ lt2Priv s w
    unfold lt2Priv; exact mem_union_left _ (mem_biUnion.2 ⟨r, hrH, hPB⟩)
  have hent : w' (merge {i, o} t r) i = η (merge {i, o} t r) i := by
    simp only [w', replE]; rw [if_pos hpriv]
  rw [hrow, hent]

end Census
end IIT
