/-
**Tie theorem**: for every `N` and every current state `s`, exact
ties at a positive value between the `φ_s` of two distinct candidates form a Lebesgue-null
set of parameters.

Assembly (L7).  By L0 (`sysPhi_cases`) the tie set, inside the open cube, lies in a
finite union of pieces `{β = β' ∧ 0 < β}` with `β` a branch of `S` and `β'` a branch of
`S' ≠ S`.  Each piece is null: either `β - β'` is not identically zero on the open cube and
Mityagin's theorem (`volume_zero_set_analytic`) applies (analyticity: L2), or
`β ≡ β'` there and then `β ≡ 0` (L6, `br_dichotomy`), so the piece is empty.  The boundary
`cube \ openCube` is null (`volume_cube_diff_openCube`).

The only non-standard axiom is `volume_zero_set_analytic` (Mityagin).
-/
import IIT.Census.TieAnalytic
import IIT.Census.TieCases
import IIT.Census.UnivZero

namespace IIT
namespace Census

open MeasureTheory Finset

variable {N : ℕ}

/-- One piece of the tie set: branch `a` of `S` equals branch `a'` of `S'` at a positive
value, inside the open cube. -/
def tiePiece (s : State N) (S S' : Finset (Fin N)) (a : BrIdx N S) (a' : BrIdx N S') :
    Set (Param N) :=
  {z | S ≠ S' ∧ z ∈ openCube N ∧ br s S a z = br s S' a' z ∧ 0 < br s S a z}

lemma an_br (s : State N) (S : Finset (Fin N)) (a : BrIdx N S) :
    AnalyticOnNhd ℝ (br s S a) (openCube N) := by
  intro z hz
  obtain ⟨b, θ, t⟩ := a
  cases b
  · exact an_BE hz s S θ t
  · exact an_BC hz s S θ t

lemma volume_tiePiece (s : State N) (S S' : Finset (Fin N)) (a : BrIdx N S)
    (a' : BrIdx N S') : volume (tiePiece s S S' a a') = 0 := by
  by_cases hne : S = S'
  · have : tiePiece s S S' a a' = ∅ := by
      ext z; simp [tiePiece, hne]
    rw [this, measure_empty]
  by_cases h : ∀ z ∈ openCube N, br s S a z = br s S' a' z
  · have h0 := br_dichotomy s hne a a' h
    have : tiePiece s S S' a a' = ∅ := by
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, hz, -, hpos⟩
      rw [h0 z hz] at hpos
      exact lt_irrefl _ hpos
    rw [this, measure_empty]
  · push Not at h
    obtain ⟨z0, hz0, hne0⟩ := h
    refine measure_mono_null ?_ (volume_zero_set_analytic volume (isOpen_openCube N)
      (convex_openCube N).isPreconnected
      (f := fun z => br s S a z - br s S' a' z)
      (fun z hz => (an_br s S a z hz).fun_sub (an_br s S' a' z hz))
      ⟨z0, hz0, sub_ne_zero.2 hne0⟩)
    rintro z ⟨-, hz, he, -⟩
    exact ⟨hz, sub_eq_zero.2 he⟩

lemma phi_eq_br (z : Param N) (s : State N) (R : Finset (Fin N)) (h : 0 < phi z s R) :
    ∃ a : BrIdx N R, phi z s R = br s R a z := by
  rcases sysPhi_cases (tpmOf z) R s with h0 | ⟨θ, t, h1 | h1⟩
  · exact absurd h0 h.ne'
  · exact ⟨(true, θ, t), h1⟩
  · exact ⟨(false, θ, t), h1⟩

/-- **Tie theorem.** Positive ties between the `φ_s` of two distinct candidates are null.
This is the set `ties N s` of `IIT/Census/B2Limit.lean`. -/
theorem volume_ties_null (s : State N) :
    volume {z : Param N | z ∈ cube N ∧ ∃ S S' : Finset (Fin N), S ≠ S' ∧ 0 < phi z s S ∧
      phi z s S = phi z s S'} = 0 := by
  have hsub : {z : Param N | z ∈ cube N ∧ ∃ S S' : Finset (Fin N), S ≠ S' ∧ 0 < phi z s S ∧
      phi z s S = phi z s S'} ⊆ (cube N \ openCube N) ∪
      ⋃ S : Finset (Fin N), ⋃ S' : Finset (Fin N), ⋃ a : BrIdx N S, ⋃ a' : BrIdx N S',
        tiePiece s S S' a a' := by
    rintro z ⟨hz, S, S', hne, hpos, heq⟩
    by_cases ho : z ∈ openCube N
    · right
      obtain ⟨a, ha⟩ := phi_eq_br z s S hpos
      obtain ⟨a', ha'⟩ := phi_eq_br z s S' (heq ▸ hpos)
      simp only [Set.mem_iUnion]
      exact ⟨S, S', a, a', hne, ho, by rw [← ha, ← ha', heq], by rw [← ha]; exact hpos⟩
    · exact Or.inl ⟨hz, ho⟩
  refine measure_mono_null hsub (measure_union_null (volume_cube_diff_openCube N) ?_)
  exact measure_iUnion_null fun S => measure_iUnion_null fun S' =>
    measure_iUnion_null fun a => measure_iUnion_null fun a' => volume_tiePiece s S S' a a'

end Census
end IIT

