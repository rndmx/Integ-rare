/-
Census, B1 lemma LT2, module M6b-6: blocks of different pairs are disjoint; the events after resampling.

* `lt2_C_form`: every entry of a pair block is `(row, col)` with `col ∈ {a,b}`, `row` differing from a base row
  (`∈ H` or `= s`) only inside `{a,b}`, and at the other column.
* `lt2_CP_disj`: the blocks `CP(a,b) = ⋃_κ C_κ` of distinct pairs `(a,b) ∈ D₁ × D₂` are disjoint.
* `lt2X_replE`: `replE (Priv w) w η ∈ X_κ(replE …) ↔ η ∈ X_κ(w)` (the events only read shared data and the block).
-/
import IIT.Census.B1LT2Pair3

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- The block of a pair. -/
noncomputable def lt2CP (s : State N) (w : Param N) (a b : Fin N) : Finset (State N × Fin N) :=
  (univ : Finset (Bool × Bool × Bool × Bool)).biUnion (lt2C s w a b)

lemma lt2_col_mem (a b : Fin N) (c : Bool) : lt2col a b c = a ∨ lt2col a b c = b := by
  cases c <;> simp [lt2col]

lemma lt2_merge_diff {a b : Fin N} (t base : State N) (j : Fin N) (h : merge {a, b} t base j ≠ base j) :
    j = a ∨ j = b := by
  by_contra hj
  push_neg at hj
  exact h (merge_not_mem (by simp [hj.1, hj.2]))

/-- **The shape of a block entry.** -/
lemma lt2_C_form {s : State N} {w : Param N} {a b : Fin N} (hab : a ≠ b) {κ : Bool × Bool × Bool × Bool}
    {q : State N × Fin N} (hq : q ∈ lt2C s w a b κ) :
    ∃ base, (base ∈ lt2H s w ∨ base = s) ∧ (q.2 = a ∨ q.2 = b) ∧
      (∀ j, q.1 j ≠ base j → j = a ∨ j = b) ∧
      (q.1 (if q.2 = a then b else a) ≠ base (if q.2 = a then b else a)) := by
  classical
  obtain ⟨e, c, u, v⟩ := κ
  have hoth : (if lt2col a b c = a then b else a) = lt2oth a b c := by
    cases c <;> simp [lt2col, lt2oth, Ne.symm hab]
  cases e
  · simp only [lt2C, Bool.false_eq_true, ↓reduceIte, mem_image] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    obtain ⟨hrH, hro⟩ := mem_filter.1 hr
    refine ⟨r, Or.inl hrH, lt2_col_mem a b c, fun j hj => lt2_merge_diff _ r j hj, ?_⟩
    simp only
    rw [hoth, merge_mem (by cases c <;> simp [lt2oth])]
    exact fun h => hro h.symm
  · simp only [lt2C, ↓reduceIte] at hq
    split_ifs at hq with hE
    · rw [mem_singleton] at hq; subst hq
      refine ⟨s, Or.inr rfl, lt2_col_mem a b c, fun j hj => lt2_merge_diff _ s j hj, ?_⟩
      simp only [lt2rowE]
      rw [hoth, merge_mem (by cases c <;> simp [lt2oth])]
      cases c <;> simp only [lt2isEff, Bool.false_eq_true, ↓reduceIte, lt2oth, lt2pat] at hE ⊢
      all_goals first
        | exact hE
        | exact Ne.symm hE
        | (simp only [if_neg (Ne.symm hab)]; first | exact hE | exact Ne.symm hE)
    · simp at hq

lemma lt2_ham_le_of_diff {x y : State N} {a b : Fin N} (h : ∀ j, x j ≠ y j → j = a ∨ j = b) : ham x y ≤ 2 := by
  classical
  unfold ham
  calc (univ.filter fun j => x j ≠ y j).card ≤ ({a, b} : Finset (Fin N)).card :=
        Finset.card_le_card fun j hj => by
          simp only [mem_filter, mem_univ, true_and] at hj
          rcases h j hj with h' | h' <;> simp [h']
    _ ≤ 2 := Finset.card_insert_le _ _

/-- **Blocks of distinct pairs are disjoint.** -/
theorem lt2_CP_disj {s : State N} {w : Param N} {a b a' b' : Fin N} (ha : a ∈ lt2D1 N) (hb : b ∈ lt2D2 N)
    (ha' : a' ∈ lt2D1 N) (hb' : b' ∈ lt2D2 N) (hne : (a, b) ≠ (a', b')) :
    Disjoint (lt2CP s w a b) (lt2CP s w a' b') := by
  classical
  have hab := lt2_D1_ne_D2 ha hb
  have hab' := lt2_D1_ne_D2 ha' hb'
  rw [Finset.disjoint_left]
  intro q hq hq'
  obtain ⟨κ, -, hκ⟩ := mem_biUnion.1 hq
  obtain ⟨κ', -, hκ'⟩ := mem_biUnion.1 hq'
  obtain ⟨base, hbase, hcol, hdiff, hoth⟩ := lt2_C_form hab hκ
  obtain ⟨base', hbase', hcol', hdiff', hoth'⟩ := lt2_C_form hab' hκ'
  -- the bases coincide
  have h1 := lt2_ham_le_of_diff hdiff
  have h2 := lt2_ham_le_of_diff hdiff'
  have h3 := ham_triangle base' q.1 base
  rw [b1_ham_comm base' q.1] at h3
  have hbb : base' = base := by
    rcases hbase with hH | rfl <;> rcases hbase' with hH' | rfl
    · exact lt2_H_sep hH hH' (by omega)
    · exfalso; have := ((mem_filter.1 hH).2).2.2; rw [b1_ham_comm] at h3; omega
    · exfalso; have := ((mem_filter.1 hH').2).2.2; omega
    · rfl
  subst hbb
  -- the columns
  apply hne
  have hD : ∀ j, j ∈ lt2D1 N → j ∈ lt2D2 N → False := fun j h1 h2 => lt2_D_disj h1 h2
  rcases hcol with hc | hc <;> rcases hcol' with hc' | hc'
  · -- column in `D₁`: `a = a'`, the other columns `b, b'` both differ
    have haa : a = a' := hc.symm.trans hc'
    subst haa
    rw [if_pos hc] at hoth; rw [if_pos hc'] at hoth'
    rcases hdiff' b hoth with h | h
    · exact absurd h (Ne.symm hab)
    · rw [h]
  · exfalso; exact hD q.2 (hc ▸ ha) (hc' ▸ hb')
  · exfalso; exact hD q.2 (hc' ▸ ha') (hc ▸ hb)
  · have hbb : b = b' := hc.symm.trans hc'
    subst hbb
    rw [if_neg (by rw [hc]; exact Ne.symm hab)] at hoth
    rw [if_neg (by rw [hc']; exact Ne.symm hab')] at hoth'
    rcases hdiff' a hoth with h | h
    · rw [h]
    · exact absurd h hab

lemma lt2_pair_set (a b : Fin N) (c : Bool) : ({lt2col a b c, lt2oth a b c} : Finset (Fin N)) = {a, b} := by
  cases c
  · rfl
  · exact Finset.pair_comm b a

lemma lt2_orient {a b : Fin N} (ha : a ∈ lt2D1 N) (hb : b ∈ lt2D2 N) (c : Bool) :
    (lt2col a b c ∈ lt2D1 N ∧ lt2oth a b c ∈ lt2D2 N) ∨ (lt2col a b c ∈ lt2D2 N ∧ lt2oth a b c ∈ lt2D1 N) := by
  cases c
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨hb, ha⟩

/-- A pair-block position over a base row in `H ∪ {s}` is private. -/
lemma lt2_priv_entry {s : State N} {w : Param N} {a b : Fin N} (ha : a ∈ lt2D1 N) (hb : b ∈ lt2D2 N)
    (c u v : Bool) {base : State N} (hbase : base ∈ lt2H s w ∨ base = s)
    (hne : base (lt2oth a b c) ≠ lt2pat a b u v (lt2oth a b c)) :
    (merge {a, b} (lt2pat a b u v) base, lt2col a b c) ∈ lt2Priv s w := by
  classical
  have h := (lt2_mem_PB_merge (t := lt2pat a b u v) (r := base) (lt2_orient ha hb c)).2 hne
  rw [lt2_pair_set] at h
  unfold lt2Priv
  rcases hbase with hH | rfl
  · exact mem_union_left _ (mem_biUnion.2 ⟨base, hH, h⟩)
  · exact mem_union_right _ h

/-- **The events after resampling the private entries.** -/
theorem lt2X_replE (s : State N) (w η : Param N) {a b : Fin N} (ha : a ∈ lt2D1 N) (hb : b ∈ lt2D2 N)
    (x ρ : ℝ) (κ : Bool × Bool × Bool × Bool) :
    replE (lt2Priv s w) w η ∈ lt2X s (replE (lt2Priv s w) w η) a b x ρ κ ↔ η ∈ lt2X s w a b x ρ κ := by
  classical
  set A := lt2Priv s w
  set w' := replE A w η
  have hagree : ∀ q ∉ lt2Priv s w, w q.1 q.2 = w' q.1 q.2 := fun q hq => by
    simp only [w', replE]; rw [if_neg (show (q.1, q.2) ∉ A from hq)]
  have hpriv : ∀ q ∈ lt2Priv s w, w' q.1 q.2 = η q.1 q.2 := fun q hq => by
    simp only [w', replE]; rw [if_pos (show (q.1, q.2) ∈ A from hq)]
  have hH : lt2H s w' = lt2H s w := lt2H_stop hagree
  have hrow : ∀ r ∈ lt2H s w, w' r = w r := fun r hr => funext fun j =>
    (hagree (r, j) (lt2_row_not_Priv (lt2_heavy_not_light ((mem_filter.1 hr).2).1)
      (by have := ((mem_filter.1 hr).2).2.2; omega) j)).symm
  have hs : w' s = w s := funext fun j => by
    refine (hagree (s, j) fun hq => ?_).symm
    rcases lt2_mem_Priv hq with ⟨r, hr, h1, h2⟩ | h
    · have := ((mem_filter.1 hr).2).2.2; rw [b1_ham_comm] at h2; simp only at h2; omega
    · unfold lt2Priv at hq
      rcases mem_union.1 hq with h' | h'
      · obtain ⟨r, hr, hq'⟩ := mem_biUnion.1 h'
        have := lt2_mem_PB hq'
        have := ((mem_filter.1 hr).2).2.2; rw [b1_ham_comm] at this; simp only at *; omega
      · have := (lt2_mem_PB h').1; simp only [b1_ham_self] at this; omega
  have hHf : ∀ c u v, lt2Hf s w' a b c u v = lt2Hf s w a b c u v := fun c u v => by
    unfold lt2Hf; rw [hH]
  have hsd : ∀ c u v, lt2sd s w' a b c u v = lt2sd s w a b c u v := fun c u v => by
    unfold lt2sd; rw [hHf]
    congr 1; exact Finset.sum_congr rfl fun r hr => by rw [hrow r (mem_filter.1 hr).1]
  have hS : ∀ c u v, lt2Sres s w' a b c u v w' = lt2Sres s w a b c u v η := fun c u v => by
    unfold lt2Sres; rw [hHf]
    refine Finset.sum_congr rfl fun r hr => ?_
    obtain ⟨hrH, hro⟩ := mem_filter.1 hr
    rw [hrow r hrH, hpriv _ (lt2_priv_entry ha hb c u v (Or.inl hrH) hro)]
  obtain ⟨e, c, u, v⟩ := κ
  cases e
  · simp only [lt2X, Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · simp only [Set.mem_setOf_eq]; rw [hsd, hS]
    · simp only [Set.mem_setOf_eq]; rw [hsd, hS]
  · simp only [lt2X, ↓reduceIte]
    rw [hs]
    split_ifs with hE
    · have hent := hpriv _ (lt2_priv_entry ha hb c u v (Or.inr rfl) (by
        cases c <;> simp only [lt2isEff, Bool.false_eq_true, ↓reduceIte] at hE <;>
          simp only [lt2oth, lt2pat, Bool.false_eq_true, ↓reduceIte, if_neg (Ne.symm (lt2_D1_ne_D2 ha hb))] <;>
          exact Ne.symm hE))
      simp only [Set.mem_setOf_eq, lt2rowE]; simp only at hent; rw [hent]
    · have hent := hpriv _ (lt2_priv_entry ha hb c u v (Or.inr rfl) (by
        cases c <;> simp only [lt2isEff, Bool.false_eq_true, ↓reduceIte] at hE <;>
          simp only [lt2oth, lt2pat, Bool.false_eq_true, ↓reduceIte, if_neg (Ne.symm (lt2_D1_ne_D2 ha hb))] <;>
          exact Ne.symm hE))
      simp only [Set.mem_setOf_eq, lt2rowE]; simp only at hent; rw [hent]
    · exact Iff.rfl

end Census
end IIT
