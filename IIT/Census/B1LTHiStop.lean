/-
Census, B1 LTBetaHi, module T2 tool: **the abstract stopping-set lemma** (pattern of `lt2H_stop`, for triples).

Data: columns `C₀(w)` (for triples `Top(tc)ᶜ`, itself a stopping choice); a lightness predicate `Light w q` read on `C₀` only; a selection `Sel w : Finset κ` that only
reads `C₀` entries and the entries of non-light rows; blocks `PB k` with columns outside `C₀` whose rows are light
whenever `k ∈ Sel w`. Then `Priv w = ⋃_{k ∈ Sel w} PB k` is a stopping set: it is determined by the entries outside
it, and `{Priv = A}` is `Aᶜ`-determined.
-/
import IIT.Census.B1LT2Heavy

namespace IIT
namespace Census

open Finset

variable {N : ℕ} {κ : Type*}

/-- The private positions of a selection. -/
def stPriv (Sel : Param N → Finset κ) (PB : κ → Finset (State N × Fin N)) (w : Param N) :
    Finset (State N × Fin N) :=
  (Sel w).biUnion PB

/-- **The abstract stopping property.** -/
theorem stPriv_stop (C0 : Param N → Finset (Fin N)) (Light : Param N → State N → Prop)
    (Sel : Param N → Finset κ)
    (hSel : ∀ w w' : Param N, (∀ q, ∀ j ∈ C0 w, w q j = w' q j) → (∀ r, ¬ Light w r → ∀ j, w r j = w' r j) →
      Sel w' = Sel w)
    (PB : κ → Finset (State N × Fin N)) (hcol : ∀ w, ∀ k ∈ Sel w, ∀ q ∈ PB k, q.2 ∉ C0 w)
    (hrow : ∀ w, ∀ k ∈ Sel w, ∀ q ∈ PB k, Light w q.1)
    {w w' : Param N} (h : ∀ q ∉ stPriv Sel PB w, w q.1 q.2 = w' q.1 q.2) :
    stPriv Sel PB w' = stPriv Sel PB w := by
  have hC : ∀ q, ∀ j ∈ C0 w, w q j = w' q j := fun q j hj => h (q, j) fun hq => by
    obtain ⟨k, hk', hk⟩ := mem_biUnion.1 hq
    exact hcol w k hk' _ hk hj
  have hN : ∀ r, ¬ Light w r → ∀ j, w r j = w' r j := fun r hr j => h (r, j) fun hq => by
    obtain ⟨k, hk, hq⟩ := mem_biUnion.1 hq
    exact hr (hrow w k hk _ hq)
  unfold stPriv; rw [hSel w w' hC hN]

/-- `{Priv = A}` is determined by the entries outside `A`. -/
theorem stPriv_detOn (C0 : Param N → Finset (Fin N)) (Light : Param N → State N → Prop)
    (Sel : Param N → Finset κ)
    (hSel : ∀ w w' : Param N, (∀ q, ∀ j ∈ C0 w, w q j = w' q j) → (∀ r, ¬ Light w r → ∀ j, w r j = w' r j) →
      Sel w' = Sel w)
    (PB : κ → Finset (State N × Fin N)) (hcol : ∀ w, ∀ k ∈ Sel w, ∀ q ∈ PB k, q.2 ∉ C0 w)
    (hrow : ∀ w, ∀ k ∈ Sel w, ∀ q ∈ PB k, Light w q.1) (A : Finset (State N × Fin N)) :
    DetOnE Aᶜ {w | stPriv Sel PB w = A} := by
  intro w w' hw
  show stPriv Sel PB w = A ↔ stPriv Sel PB w' = A
  constructor
  · intro hA
    rw [stPriv_stop C0 Light Sel hSel PB hcol hrow (w := w) (w' := w')
      fun q hq => hw q (mem_compl.2 (hA ▸ hq)), hA]
  · intro hA
    rw [stPriv_stop C0 Light Sel hSel PB hcol hrow (w := w') (w' := w)
      fun q hq => (hw q (mem_compl.2 (hA ▸ hq))).symm, hA]

/-- Lightness read on `C₀`: the `X_{C₀} > c N` form is unchanged by agreement on `C₀` (the instance side of `hSel`). -/
lemma stLight_congr (C0 : Finset (Fin N)) (c : ℝ) {w w' : Param N} (h : ∀ q, ∀ j ∈ C0, w q j = w' q j)
    (q : State N) : (c * N < XMW w C0 q ↔ c * N < XMW w' C0 q) := by
  have : XMW w C0 q = XMW w' C0 q := by
    unfold XMW; exact Finset.sum_congr rfl fun j hj => by rw [h q j hj]
  rw [this]

/-- `P(r) ≤ e^{-X_{C₀}(r)}`. -/
lemma st_Pw_le_exp (C0 : Finset (Fin N)) (w : Param N) (r : State N) :
    Pw w r ≤ Real.exp (-XMW w C0 r) := by
  have h2 : Pw w r ≤ ∏ j ∈ C0, clamp01 (w r j) := by
    unfold Pw
    rw [← Finset.prod_mul_prod_compl C0 (fun j => clamp01 (w r j))]
    exact mul_le_of_le_one_right (Finset.prod_nonneg fun j _ => clamp01_nonneg _)
      (Finset.prod_le_one (fun j _ => clamp01_nonneg _) fun j _ => clamp01_le_one _)
  refine h2.trans ?_
  by_cases hpos : ∀ j ∈ C0, 0 < clamp01 (w r j)
  · apply le_of_eq
    unfold XMW
    rw [Finset.sum_neg_distrib, neg_neg, Real.exp_sum]
    exact Finset.prod_congr rfl fun j hj => (Real.exp_log (hpos j hj)).symm
  · push Not at hpos
    obtain ⟨j, hj, h0⟩ := hpos
    rw [Finset.prod_eq_zero hj (le_antisymm h0 (clamp01_nonneg _))]
    exact (Real.exp_pos _).le

/-- **`tc` is a stopping choice**: if `P(tc) > e^{-cN}`, changing only `C₀`-agreeing entries of light rows
(`X_{C₀} > cN`) keeps `tc` and `P(tc)`. -/
theorem st_tcRow_stable (C0 : Finset (Fin N)) (c : ℝ) {w w' : Param N}
    (hP : Real.exp (-(c * N)) < Pw w (tcRow w))
    (hC : ∀ q, ∀ j ∈ C0, w q j = w' q j) (hN : ∀ r, ¬ c * N < XMW w C0 r → ∀ j, w r j = w' r j) :
    tcRow w' = tcRow w ∧ Pw w' (tcRow w) = Pw w (tcRow w) := by
  set t := tcRow w
  have hlight : ∀ r, c * N < XMW w C0 r → Pw w' r < Pw w t := fun r hr => by
    have hX : XMW w' C0 r = XMW w C0 r := by
      unfold XMW; exact Finset.sum_congr rfl fun j hj => by rw [hC r j hj]
    calc Pw w' r ≤ Real.exp (-XMW w' C0 r) := st_Pw_le_exp C0 w' r
      _ < Real.exp (-(c * N)) := Real.exp_lt_exp.2 (by rw [hX]; linarith)
      _ < Pw w t := hP
  have hrow : ∀ r, ¬ c * N < XMW w C0 r → Pw w' r = Pw w r := fun r hr => by
    unfold Pw; exact Finset.prod_congr rfl fun j _ => by rw [hN r hr j]
  have htl : ¬ c * N < XMW w C0 t := fun h => by
    have := (st_Pw_le_exp C0 w t).trans_lt (Real.exp_lt_exp.2 (by linarith : -XMW w C0 t < -(c * N)))
    linarith
  have ht : Pw w' t = Pw w t := hrow t htl
  refine ⟨?_, ht⟩
  have hspec := (tcRow_eq_iff w t).1 rfl
  refine (tcRow_eq_iff w' t).2 ⟨fun r => ?_, fun r hr => ?_⟩
  · by_cases hl : c * N < XMW w C0 r
    · rw [ht]; exact (hlight r hl).le
    · rw [hrow r hl, ht]; exact hspec.1 r
  · by_cases hl : c * N < XMW w C0 r
    · rw [ht]; exact hlight r hl
    · rw [hrow r hl, ht]; exact hspec.2 r hr

/-- The surrogate parameter: private entries set to `1/2`. -/
noncomputable def stHalf (P : Finset (State N × Fin N)) (w : Param N) : Param N := by
  classical exact fun r j => if (r, j) ∈ P then 1 / 2 else w r j

/-- A weight bounded by the row product is at most `e^{-X_{C₀}}`. -/
lemma st_g_le_exp (C0 : Finset (Fin N)) (g : (Fin N → ℝ) → ℝ) (hgP : ∀ x, g x ≤ ∏ j, clamp01 (x j))
    (w : Param N) (v : State N) : g (w v) ≤ Real.exp (-XMW w C0 v) :=
  (hgP (w v)).trans (st_Pw_le_exp C0 w v)

/-- **The deterministic perturbation bound (W2 (6.1)), abstract form.** -/
theorem st_pert (P : Finset (State N × Fin N)) (w : Param N) (V : Finset (State N)) (σ : State N → State N)
    (i : Fin N) (g : (Fin N → ℝ) → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgP : ∀ x, g x ≤ ∏ j, clamp01 (x j))
    (C0 : Finset (Fin N)) (c θ : ℝ) (hθ : 0 ≤ θ) (hcol : ∀ q ∈ P, q.2 ∉ C0)
    (hrowL : ∀ v ∈ V, (∃ j, (v, j) ∈ P) → c * N < XMW w C0 v)
    (hshL : ∀ v ∈ V, (σ v, i) ∈ P → c * N < XMW w C0 v ∨ g (w v) ≤ θ)
    (nσ : ℕ) (hfib : ∀ q, (V.filter fun v => σ v = q).card ≤ nσ) :
    |∑ v ∈ V, clamp01 (w (σ v) i) * g (w v) - ∑ v ∈ V, clamp01 (stHalf P w (σ v) i) * g (stHalf P w v)| ≤
      (P.card * (1 + nσ) : ℕ) * (Real.exp (-(c * N)) + θ) := by
  classical
  set w2 := stHalf P w
  set E := Real.exp (-(c * N))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hagree : ∀ r j, (r, j) ∉ P → w2 r j = w r j := fun r j h => by
    simp only [w2, stHalf]; rw [if_neg h]
  have hX : ∀ v, XMW w2 C0 v = XMW w C0 v := fun v => by
    unfold XMW; exact Finset.sum_congr rfl fun j hj => by rw [hagree v j fun h => hcol _ h hj]
  let touch : State N → Prop := fun v => (∃ j, (v, j) ∈ P) ∨ (σ v, i) ∈ P
  -- termwise bound
  have hterm : ∀ v ∈ V, |clamp01 (w (σ v) i) * g (w v) - clamp01 (w2 (σ v) i) * g (w2 v)| ≤
      if touch v then E + θ else 0 := by
    intro v hv
    have hy1 := clamp01_nonneg (w (σ v) i); have hy1' := clamp01_le_one (w (σ v) i)
    have hy2 := clamp01_nonneg (w2 (σ v) i); have hy2' := clamp01_le_one (w2 (σ v) i)
    have hg1 := hg0 (w v); have hg2 := hg0 (w2 v)
    by_cases hrow : ∃ j, (v, j) ∈ P
    · rw [if_pos (Or.inl hrow)]
      have hl := hrowL v hv hrow
      have b1 : g (w v) ≤ E := (st_g_le_exp C0 g hgP w v).trans (Real.exp_le_exp.2 (by linarith))
      have b2 : g (w2 v) ≤ E := (st_g_le_exp C0 g hgP w2 v).trans (Real.exp_le_exp.2 (by rw [hX]; linarith))
      rw [abs_le]; constructor <;> nlinarith
    · push Not at hrow
      have hr : w2 v = w v := funext fun j => hagree v j (hrow j)
      rw [hr]
      by_cases hsh : (σ v, i) ∈ P
      · rw [if_pos (Or.inr hsh)]
        have hb : g (w v) ≤ E + θ := by
          rcases hshL v hv hsh with hl | hθ'
          · have := (st_g_le_exp C0 g hgP w v).trans (Real.exp_le_exp.2 (by linarith : -XMW w C0 v ≤ -(c * N)))
            linarith
          · linarith
        rw [abs_le]; constructor <;> nlinarith
      · have hnt : ¬ touch v := by
          rintro (⟨j, hj⟩ | h)
          · exact hrow j hj
          · exact hsh h
        rw [if_neg hnt, hagree _ _ hsh, sub_self, abs_zero]
  -- counting the touching rows
  have hsub : V.filter touch ⊆ P.image Prod.fst ∪ P.biUnion fun q => V.filter fun v => σ v = q.1 := by
    intro v hv
    obtain ⟨hvV, ht⟩ := mem_filter.1 hv
    rcases ht with ⟨j, hj⟩ | h
    · exact mem_union_left _ (mem_image.2 ⟨(v, j), hj, rfl⟩)
    · exact mem_union_right _ (mem_biUnion.2 ⟨(σ v, i), h, mem_filter.2 ⟨hvV, rfl⟩⟩)
  have hcard : (V.filter touch).card ≤ P.card * (1 + nσ) := by
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    have h1 := card_image_le (s := P) (f := Prod.fst)
    have h2 : (P.biUnion fun q => V.filter fun v => σ v = q.1).card ≤ P.card * nσ :=
      (card_biUnion_le).trans (by
        calc ∑ q ∈ P, (V.filter fun v => σ v = q.1).card ≤ ∑ _q ∈ P, nσ := sum_le_sum fun q _ => hfib q.1
          _ = P.card * nσ := by rw [sum_const, smul_eq_mul])
    nlinarith
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by linarith)

end Census
end IIT
