/-
Census of IIT 2.0, deterministic layer: Lemmas 3 and 4 of the note `pc2-limit.tex`
and the reduction of `WholeIsMainComplex` to bounds on `ei` and on the cross terms `D_M`.
-/
import IIT2.Bounds

namespace IIT2

open Finset Real

variable {N : ℕ}

lemma avg_sum {ι : Type*} (s : Finset ι) (f : ι → State N → ℝ) :
    avg (fun x => ∑ M ∈ s, f M x) = ∑ M ∈ s, avg (f M) := by
  unfold avg; rw [Finset.sum_comm, Finset.sum_div]

/-- Lemma 3 of the note: `φ(R) ≤ ei(R)`. -/
theorem phi_le_ei (sys : UnitTPM N) (S : Finset (Fin N)) (x₁ : State N) :
    phi sys S x₁ ≤ ei sys S x₁ := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS; rw [phi_empty]; exact ei_nonneg _ _ _
  obtain ⟨P, hMIP, hP⟩ := exists_isMIP sys S x₁
  let T := Finpartition.indiscrete (a := S) (by simpa [Finset.bot_eq_empty] using hS.ne_empty)
  have hT : T.parts.card = 1 := by simp [T, Finpartition.indiscrete]
  have hle := hMIP T
  unfold mipKey at hle
  rw [Prod.Lex.toLex_le_toLex'] at hle
  have h1 : eiAcross sys P x₁ / normP P ≤ eiAcross sys T x₁ / normP T := hle.1
  have hTa : eiAcross sys T x₁ = ei sys S x₁ := by simp [eiAcross, hT]
  have hTn : normP T = S.card := by simp [normP, hT]
  rw [hTa, hTn] at h1
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hNP := normP_pos hS P
  have hNle := normP_le_card P
  have hei := ei_nonneg sys S x₁
  rw [div_le_div_iff₀ hNP hcard] at h1
  rw [hP]
  nlinarith

/-- The cross term `D_M = 2^{-n} ∑_x f(x) log g_M(x_M)` of the note, with `f = post X`. -/
noncomputable def Dterm (sys : UnitTPM N) (M : Finset (Fin N)) (x₁ : State N) : ℝ :=
  avg (fun x => post sys Finset.univ x₁ x * logb 2 (post sys M x₁ x))

/-- Lemma 4 of the note: `e_P = ei(X) - ∑_{M ∈ P} D_M` for every partition `P ≠ {X}`. -/
theorem eiAcross_eq_sub (sys : UnitTPM N) (P : Finpartition (Finset.univ : Finset (Fin N)))
    (x₁ : State N) (hP : P.parts.card ≠ 1) :
    eiAcross sys P x₁ = ei sys Finset.univ x₁ - ∑ M ∈ P.parts, Dterm sys M x₁ := by
  unfold eiAcross
  rw [if_neg hP]
  unfold eiRel ei kl Dterm pmax
  rw [← avg_sum, ← avg_sub]
  refine avg_congr fun x => ?_
  set f := post sys Finset.univ x₁ x
  rcases (post_nonneg sys Finset.univ x₁ x).lt_or_eq with hf | hf
  · have hg : ∀ M ∈ P.parts, post sys M x₁ x ≠ 0 := fun M hM =>
      (post_pos_of_subset sys (P.le hM) x₁ x hf).ne'
    unfold partsPost
    rw [div_one, Real.logb_div hf.ne' (Finset.prod_ne_zero_iff.mpr hg),
      Real.logb_prod _ _ hg, mul_sub, Finset.mul_sum]
  · have h0 : f = 0 := hf.symm
    rw [h0]; simp

/-- Reduction: lower bound `lo > 0` on `ei(X)` and on every `ei(X) - ∑_{M∈P} D_M`, and strict
upper bound `lo` on `ei(R)` for every nonempty proper `R`, imply that the whole system is the
main complex. -/
theorem wholeIsMainComplex_of_bounds (sys : UnitTPM N) (x₁ : State N) (lo : ℝ) (hlo : 0 < lo)
    (hX : lo ≤ ei sys Finset.univ x₁)
    (hP : ∀ P : Finpartition (Finset.univ : Finset (Fin N)), P.parts.card ≠ 1 →
      lo ≤ ei sys Finset.univ x₁ - ∑ M ∈ P.parts, Dterm sys M x₁)
    (hR : ∀ R : Finset (Fin N), R ⊂ Finset.univ → R.Nonempty → ei sys R x₁ < lo) :
    WholeIsMainComplex sys x₁ := by
  have hphi : lo ≤ phi sys Finset.univ x₁ := by
    obtain ⟨P, -, hPe⟩ := exists_isMIP sys Finset.univ x₁
    rw [hPe]
    by_cases h1 : P.parts.card = 1
    · unfold eiAcross; rw [if_pos h1]; exact hX
    · rw [eiAcross_eq_sub sys P x₁ h1]; exact hP P h1
  refine ⟨(isComplex_univ_iff sys x₁).mpr (lt_of_lt_of_le hlo hphi), fun R hRs => ?_⟩
  rcases R.eq_empty_or_nonempty with hRe | hRne
  · subst hRe; rw [phi_empty]; linarith
  · exact lt_of_le_of_lt (phi_le_ei sys R x₁) (lt_of_lt_of_le (hR R hRs hRne) hphi)

end IIT2
