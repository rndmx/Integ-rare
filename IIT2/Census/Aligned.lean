/-
Census of IIT 2.0: the quantities of the note expressed through the aligned transition
probabilities `q l c = prob l c (x₁ l)`, and the deterministic event `GoodA` which implies
`WholeIsMainComplex`.
-/
import IIT2.Census.Deterministic

namespace IIT2

open Finset Real

variable {N : ℕ}

/-- Aligned transition probabilities `q_l(c)` of the note. -/
def qOf (sys : UnitTPM N) (x₁ : State N) : Fin N → State N → ℝ := fun l c => sys.prob l c (x₁ l)

/-- `a^M_l(x)`: the probability of the current output of unit `l`, extrinsic inputs averaged. -/
noncomputable def aA (q : Fin N → State N → ℝ) (M : Finset (Fin N)) (l : Fin N) (x : State N) :
    ℝ := avg (fun e => q l (mix M x e))

/-- `W_M(x) = ∏_{l∈M} 2 a^M_l(x)`. -/
noncomputable def WA (q : Fin N → State N → ℝ) (M : Finset (Fin N)) (x : State N) : ℝ :=
  ∏ l ∈ M, 2 * aA q M l x

noncomputable def ZA (q : Fin N → State N → ℝ) (M : Finset (Fin N)) : ℝ := avg (WA q M)

noncomputable def YA (q : Fin N → State N → ℝ) (M : Finset (Fin N)) : ℝ :=
  avg (fun x => WA q M x * logb 2 (WA q M x))

noncomputable def TA (q : Fin N → State N → ℝ) (M : Finset (Fin N)) : ℝ :=
  avg (fun x => WA q Finset.univ x * logb 2 (WA q M x))

lemma cond_eq_WA (sys : UnitTPM N) (M : Finset (Fin N)) (x₁ x : State N) :
    cond sys M x₁ x = WA (qOf sys x₁) M x / 2 ^ M.card := by
  unfold WA cond aA qOf
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  field_simp

lemma post_eq_WA (sys : UnitTPM N) (M : Finset (Fin N)) (x₁ x : State N) :
    post sys M x₁ x = WA (qOf sys x₁) M x / ZA (qOf sys x₁) M := by
  unfold post ZA
  rw [cond_eq_WA, avg_congr (cond_eq_WA sys M x₁), avg_div_const]
  have : (2 : ℝ) ^ M.card ≠ 0 := by positivity
  field_simp

lemma avg_eq_zero_iff_of_nonneg {f : State N → ℝ} (hf : ∀ x, 0 ≤ f x) (h : avg f = 0) (x : State N) :
    f x = 0 := by
  rcases (hf x).lt_or_eq with h' | h'
  · exact absurd h (avg_pos hf h').ne'
  · exact h'.symm

section q

variable (q : Fin N → State N → ℝ)

lemma aA_nonneg (hq : ∀ l c, 0 ≤ q l c) (M : Finset (Fin N)) (l : Fin N) (x : State N) :
    0 ≤ aA q M l x := avg_nonneg fun _ => hq _ _

lemma WA_nonneg (hq : ∀ l c, 0 ≤ q l c) (M : Finset (Fin N)) (x : State N) : 0 ≤ WA q M x :=
  Finset.prod_nonneg fun l _ => by have := aA_nonneg q hq M l x; positivity

lemma aA_univ (l : Fin N) (x : State N) : aA q Finset.univ l x = q l x := by
  unfold aA
  have : ∀ e, mix Finset.univ x e = x := fun e => by funext j; simp [mix]
  simp_rw [this]; exact avg_const _

lemma WA_univ_eq_zero (hq : ∀ l c, 0 ≤ q l c) (M : Finset (Fin N)) (x : State N)
    (h : WA q M x = 0) : WA q Finset.univ x = 0 := by
  obtain ⟨l, hl, h0⟩ := Finset.prod_eq_zero_iff.mp h
  have ha : aA q M l x = 0 := by linarith
  have := avg_eq_zero_iff_of_nonneg (fun e => hq l (mix M x e)) ha x
  have hmix : mix M x x = x := by funext j; by_cases hj : j ∈ M <;> simp [mix, hj]
  rw [hmix] at this
  exact Finset.prod_eq_zero (Finset.mem_univ l) (by rw [aA_univ, this]; ring)

lemma ei_eq_YZ (sys : UnitTPM N) (M : Finset (Fin N)) (x₁ : State N)
    (hZ : 0 < ZA (qOf sys x₁) M) :
    ei sys M x₁ = YA (qOf sys x₁) M / ZA (qOf sys x₁) M - logb 2 (ZA (qOf sys x₁) M) := by
  have hq : ∀ l c, 0 ≤ qOf sys x₁ l c := fun l c => sys.nonneg _ _ _
  unfold ei kl pmax YA
  set Z := ZA (qOf sys x₁) M
  have hpt : ∀ x, post sys M x₁ x * logb 2 (post sys M x₁ x / 1) =
      WA (qOf sys x₁) M x * logb 2 (WA (qOf sys x₁) M x) / Z - WA (qOf sys x₁) M x / Z * logb 2 Z := by
    intro x
    rw [div_one, post_eq_WA]
    rcases (WA_nonneg _ hq M x).lt_or_eq with hW | hW
    · rw [Real.logb_div hW.ne' hZ.ne']; ring
    · rw [← hW]; simp
  rw [avg_congr hpt, avg_sub, avg_div_const]
  have : avg (fun x => WA (qOf sys x₁) M x / Z * logb 2 Z) = logb 2 Z := by
    have h2 : ∀ x, WA (qOf sys x₁) M x / Z * logb 2 Z = WA (qOf sys x₁) M x * (logb 2 Z / Z) :=
      fun x => by ring
    rw [avg_congr h2]
    unfold avg
    rw [← Finset.sum_mul, mul_div_right_comm]
    change avg (WA (qOf sys x₁) M) * (logb 2 Z / Z) = _
    change Z * (logb 2 Z / Z) = _
    field_simp
  rw [this]

lemma Dterm_eq_TZ (sys : UnitTPM N) (M : Finset (Fin N)) (x₁ : State N)
    (hZX : 0 < ZA (qOf sys x₁) Finset.univ) (hZ : 0 < ZA (qOf sys x₁) M) :
    Dterm sys M x₁ = TA (qOf sys x₁) M / ZA (qOf sys x₁) Finset.univ
      - logb 2 (ZA (qOf sys x₁) M) := by
  have hq : ∀ l c, 0 ≤ qOf sys x₁ l c := fun l c => sys.nonneg _ _ _
  unfold Dterm TA
  set Z := ZA (qOf sys x₁) M
  set ZX := ZA (qOf sys x₁) Finset.univ
  have hpt : ∀ x, post sys Finset.univ x₁ x * logb 2 (post sys M x₁ x) =
      WA (qOf sys x₁) Finset.univ x * logb 2 (WA (qOf sys x₁) M x) / ZX
        - WA (qOf sys x₁) Finset.univ x * (logb 2 Z / ZX) := by
    intro x
    rw [post_eq_WA, post_eq_WA]
    rcases (WA_nonneg _ hq M x).lt_or_eq with hW | hW
    · rw [Real.logb_div hW.ne' hZ.ne']; ring
    · rw [WA_univ_eq_zero _ hq M x hW.symm]; simp
  rw [avg_congr hpt, avg_sub, avg_div_const]
  congr 1
  unfold avg
  rw [← Finset.sum_mul, mul_div_right_comm]
  change ZX * (logb 2 Z / ZX) = _
  field_simp

end q

end IIT2
