/-
Census, B1 lemma LT2, module M4 part 1: heavy rows, the private positions, and the stopping property.

Final M4 design (LT2-PLAN.md): `C₀ = {j < N - 2m}` (`m = N/20`), `D₁ = [N-2m, N-m)`, `D₂ = [N-m, N)`.
* `Light q ⇔ X_{C₀}(q) > (7/10)N` (reads only `C₀` entries, never private).
* `Heavy r ⇔ x₁N < X(r) ≤ (38/100)N`; heavy rows are never light.
* `Iso r ⇔` every row at Hamming distance `1..4` from `r` is light; `H(s) = {r : Heavy ∧ Iso ∧ ham(r,s) > 6}`.
* `Priv(s,w) = ⋃_{r∈H} PB(r) ∪ PB(s)`, `PB(r) = {(r^b,a),(r^{ab},a),(r^a,b),(r^{ab},b) : a ∈ D₁, b ∈ D₂}`.
* `lt2Priv_stop`: `Priv` is a stopping set (determined by the entries outside it).
-/
import IIT.Census.B1LT2Decomp

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- `m = N/20`, the size of each of `D₁`, `D₂`. -/
def lt2m (N : ℕ) : ℕ := N / 20

def lt2C0 (N : ℕ) : Finset (Fin N) := univ.filter fun j => j.val < N - 2 * lt2m N
def lt2D1 (N : ℕ) : Finset (Fin N) := univ.filter fun j => N - 2 * lt2m N ≤ j.val ∧ j.val < N - lt2m N
def lt2D2 (N : ℕ) : Finset (Fin N) := univ.filter fun j => N - lt2m N ≤ j.val

lemma lt2_not_C0_of_D1 {j : Fin N} (h : j ∈ lt2D1 N) : j ∉ lt2C0 N := by
  simp only [lt2D1, lt2C0, mem_filter, mem_univ, true_and] at h ⊢; omega

lemma lt2_not_C0_of_D2 {j : Fin N} (h : j ∈ lt2D2 N) : j ∉ lt2C0 N := by
  simp only [lt2D2, lt2C0, mem_filter, mem_univ, true_and] at h ⊢; omega

lemma lt2_D1_ne_D2 {a b : Fin N} (ha : a ∈ lt2D1 N) (hb : b ∈ lt2D2 N) : a ≠ b := by
  simp only [lt2D1, lt2D2, mem_filter, mem_univ, true_and] at ha hb
  intro h; subst h; omega

/-- Light rows (read on `C₀` only). -/
def lt2Light (w : Param N) (q : State N) : Prop := 7 / 10 * (N : ℝ) < XMW w (lt2C0 N) q

/-- Heavy rows. -/
def lt2Heavy (w : Param N) (r : State N) : Prop := lt2x1 * N < XW w r ∧ XW w r ≤ 38 / 100 * (N : ℝ)

/-- Isolation: every row at distance `1..4` is light. -/
def lt2Iso (w : Param N) (r : State N) : Prop := ∀ q, 1 ≤ ham q r → ham q r ≤ 4 → lt2Light w q

/-- The heavy isolated rows far from `s`. -/
noncomputable def lt2H (s : State N) (w : Param N) : Finset (State N) := by
  classical exact univ.filter fun r => lt2Heavy w r ∧ lt2Iso w r ∧ 6 < ham r s

/-- The private block of a row. -/
noncomputable def lt2PB (r : State N) : Finset (State N × Fin N) := by
  classical exact (lt2D1 N ×ˢ lt2D2 N).biUnion fun p =>
    {(flip r p.2, p.1), (flip (flip r p.1) p.2, p.1), (flip r p.1, p.2), (flip (flip r p.1) p.2, p.2)}

/-- The private positions. -/
noncomputable def lt2Priv (s : State N) (w : Param N) : Finset (State N × Fin N) := by
  classical exact (lt2H s w).biUnion lt2PB ∪ lt2PB s

lemma lt2_heavy_not_light {w : Param N} {r : State N} (h : lt2Heavy w r) : ¬ lt2Light w r := by
  intro hl
  have h1 := XMW_le_XW w (lt2C0 N) r
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  unfold lt2Light at hl
  linarith [h.2]

lemma lt2_ham_flip (r : State N) (j : Fin N) : ham (flip r j) r = 1 := by
  unfold ham flip
  rw [Finset.card_eq_one]
  refine ⟨j, ?_⟩
  ext k
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  by_cases hk : k = j
  · subst hk; simp
  · simp [Function.update_of_ne hk, hk]

lemma lt2_ham_flip2 (r : State N) {a b : Fin N} (hab : a ≠ b) : ham (flip (flip r a) b) r = 2 := by
  unfold ham flip
  rw [Finset.card_eq_two]
  refine ⟨a, b, hab, ?_⟩
  ext k
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  by_cases hka : k = a
  · subst hka; simp [Function.update_of_ne hab]
  · by_cases hkb : k = b
    · subst hkb; simp [Function.update_of_ne hka]
    · simp [Function.update_of_ne hka, Function.update_of_ne hkb, hka, hkb]

/-- Positions of a private block: rows at distance `1` or `2`, columns outside `C₀`. -/
lemma lt2_mem_PB {r : State N} {q : State N × Fin N} (hq : q ∈ lt2PB r) :
    1 ≤ ham q.1 r ∧ ham q.1 r ≤ 2 ∧ q.2 ∉ lt2C0 N := by
  classical
  simp only [lt2PB, mem_biUnion, mem_product, mem_insert, mem_singleton] at hq
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hq⟩ := hq
  have hab := lt2_D1_ne_D2 ha hb
  rcases hq with rfl | rfl | rfl | rfl
  · simp [lt2_ham_flip, lt2_not_C0_of_D1 ha]
  · simp [lt2_ham_flip2 r hab, lt2_not_C0_of_D1 ha]
  · simp [lt2_ham_flip, lt2_not_C0_of_D2 hb]
  · simp [lt2_ham_flip2 r hab, lt2_not_C0_of_D2 hb]

lemma lt2_mem_Priv {s : State N} {w : Param N} {q : State N × Fin N} (hq : q ∈ lt2Priv s w) :
    (∃ r ∈ lt2H s w, 1 ≤ ham q.1 r ∧ ham q.1 r ≤ 2) ∨ ham q.1 s ≤ 2 := by
  classical
  simp only [lt2Priv, mem_union, mem_biUnion] at hq
  rcases hq with ⟨r, hr, hq⟩ | hq
  · exact Or.inl ⟨r, hr, (lt2_mem_PB hq).1, (lt2_mem_PB hq).2.1⟩
  · exact Or.inr (lt2_mem_PB hq).2.1

lemma lt2_Priv_col {s : State N} {w : Param N} {q : State N × Fin N} (hq : q ∈ lt2Priv s w) :
    q.2 ∉ lt2C0 N := by
  classical
  simp only [lt2Priv, mem_union, mem_biUnion] at hq
  rcases hq with ⟨r, -, hq⟩ | hq
  · exact (lt2_mem_PB hq).2.2
  · exact (lt2_mem_PB hq).2.2

/-- Entries of rows that are heavy (at `w`) or far from `H ∪ {s}` are never private. -/
lemma lt2_row_not_Priv {s : State N} {w : Param N} {r : State N} (hr : ¬ lt2Light w r) (hs : 2 < ham r s)
    (j : Fin N) : (r, j) ∉ lt2Priv s w := by
  classical
  intro hq
  rcases lt2_mem_Priv hq with ⟨r', hr', h1, h2⟩ | h
  · have hiso := ((mem_filter.1 hr').2).2.1
    exact hr (hiso r h1 (by simpa using h2.trans (by norm_num : 2 ≤ 4)))
  · simp at h; omega

/-- Agreement off `Priv` gives the same lightness everywhere. -/
lemma lt2_light_congr {s : State N} {w w' : Param N}
    (h : ∀ q ∉ lt2Priv s w, w q.1 q.2 = w' q.1 q.2) (q : State N) : lt2Light w q ↔ lt2Light w' q := by
  have : XMW w (lt2C0 N) q = XMW w' (lt2C0 N) q := by
    unfold XMW
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [h (q, j) fun hq => lt2_Priv_col hq hj]
  unfold lt2Light; rw [this]

/-- **The stopping property of the private positions.** -/
theorem lt2H_stop {s : State N} {w w' : Param N} (h : ∀ q ∉ lt2Priv s w, w q.1 q.2 = w' q.1 q.2) :
    lt2H s w' = lt2H s w := by
  classical
  have hL := lt2_light_congr h
  have hIso : ∀ r, lt2Iso w r ↔ lt2Iso w' r := fun r =>
    forall_congr' fun q => imp_congr_right fun _ => imp_congr_right fun _ => hL q
  have hrow : ∀ r, ¬ lt2Light w r → 2 < ham r s → ∀ j, w r j = w' r j := fun r hr hs j =>
    h (r, j) (lt2_row_not_Priv hr hs j)
  have hX : ∀ r, ¬ lt2Light w r → 2 < ham r s → XW w r = XW w' r := fun r hr hs => by
    unfold XW; exact Finset.sum_congr rfl fun j _ => by rw [hrow r hr hs j]
  ext r
  simp only [lt2H, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hH, hI, hd⟩
    have hnl : ¬ lt2Light w r := fun hl => lt2_heavy_not_light hH ((hL r).1 hl)
    refine ⟨?_, (hIso r).2 hI, hd⟩
    unfold lt2Heavy at hH ⊢; rw [hX r hnl (by omega)]; exact hH
  · rintro ⟨hH, hI, hd⟩
    have hnl : ¬ lt2Light w r := lt2_heavy_not_light hH
    refine ⟨?_, (hIso r).1 hI, hd⟩
    unfold lt2Heavy at hH ⊢; rw [← hX r hnl (by omega)]; exact hH

theorem lt2Priv_stop {s : State N} {w w' : Param N} (h : ∀ q ∉ lt2Priv s w, w q.1 q.2 = w' q.1 q.2) :
    lt2Priv s w' = lt2Priv s w := by
  unfold lt2Priv; rw [lt2H_stop h]

/-- `{Priv = A}` is determined by the entries outside `A`. -/
lemma lt2Priv_detOn (s : State N) (A : Finset (State N × Fin N)) : DetOnE Aᶜ {w | lt2Priv s w = A} := by
  intro w w' hw
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hA
    rw [lt2Priv_stop (w := w) (w' := w') fun q hq => hw q (mem_compl.2 (hA ▸ hq)), hA]
  · intro hA
    rw [lt2Priv_stop (w := w') (w' := w) fun q hq => (hw q (mem_compl.2 (hA ▸ hq))).symm, hA]

lemma lt2_mset_memH (s r : State N) : MeasurableSet {w : Param N | r ∈ lt2H s w} := by
  classical
  have e : {w : Param N | r ∈ lt2H s w} = ({w | lt2x1 * N < XW w r} ∩ {w | XW w r ≤ 38 / 100 * (N : ℝ)}) ∩
      ((⋂ q, {w : Param N | 1 ≤ ham q r → ham q r ≤ 4 → lt2Light w q}) ∩ {_w | 6 < ham r s}) := by
    ext w; unfold lt2H; simp [lt2Heavy, lt2Iso, and_assoc]
  rw [e]
  refine ((measurableSet_lt measurable_const (b1m_XW r)).inter (measurableSet_le (b1m_XW r) measurable_const)).inter
    ((MeasurableSet.iInter fun q => ?_).inter (MeasurableSet.const _))
  by_cases h : 1 ≤ ham q r ∧ ham q r ≤ 4
  · have e2 : {w : Param N | 1 ≤ ham q r → ham q r ≤ 4 → lt2Light w q} = {w | lt2Light w q} := by
      ext w; simp only [Set.mem_setOf_eq]; exact ⟨fun hw => hw h.1 h.2, fun hw _ _ => hw⟩
    rw [e2]; exact measurableSet_lt measurable_const (b1m_XMW _ q)
  · have e2 : {w : Param N | 1 ≤ ham q r → ham q r ≤ 4 → lt2Light w q} = Set.univ := by
      ext w; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact fun h1 h2 => absurd ⟨h1, h2⟩ h
    rw [e2]; exact MeasurableSet.univ

lemma lt2_mset_H (s : State N) (K : Finset (State N)) : MeasurableSet {w : Param N | lt2H s w = K} := by
  have e : {w : Param N | lt2H s w = K} = ⋂ r, {w : Param N | r ∈ lt2H s w ↔ r ∈ K} := by
    ext w; simp only [Set.mem_setOf_eq, Set.mem_iInter]; exact Finset.ext_iff
  rw [e]
  refine MeasurableSet.iInter fun r => ?_
  by_cases hr : r ∈ K
  · have e2 : {w : Param N | r ∈ lt2H s w ↔ r ∈ K} = {w | r ∈ lt2H s w} := by
      ext w; simp [hr]
    rw [e2]; exact lt2_mset_memH s r
  · have e2 : {w : Param N | r ∈ lt2H s w ↔ r ∈ K} = {w | r ∈ lt2H s w}ᶜ := by
      ext w; simp [hr]
    rw [e2]; exact (lt2_mset_memH s r).compl

lemma lt2_mset_Priv (s : State N) (A : Finset (State N × Fin N)) :
    MeasurableSet {w : Param N | lt2Priv s w = A} := by
  classical
  have e : {w : Param N | lt2Priv s w = A} =
      ⋃ K : Finset (State N), ({w | lt2H s w = K} ∩ {_w | K.biUnion lt2PB ∪ lt2PB s = A}) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨lt2H s w, rfl, by rw [← h]; unfold lt2Priv; congr⟩
    · rintro ⟨K, hK, h⟩; rw [← h, ← hK]; unfold lt2Priv; congr
  rw [e]
  exact MeasurableSet.iUnion fun K => (lt2_mset_H s K).inter (MeasurableSet.const _)

end Census
end IIT
