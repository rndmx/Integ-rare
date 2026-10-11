/-
Census pair step, part 2: moments of the superblock statistics.

On one superblock (`Loc L n`, iid uniform coordinates) the statistic `Tst z a`,
`a = (k, ε, c)`, is `∑_π P(π) φ_a(π)` with `P(π)` the row product and `φ_a(π)` a
character contrast (`chi c`) of the unit-`(k,ε)` column over the four pair-`k` states of the
row.  We compute: `E T_a = 0`, `E T_a T_b = 3^{-R} 4^L dd a b + Off`, with `dd` diagonal
(`33/40`, `23/40`) and `|Off| ≤ 64 · 16^L · 4^{-R}`, and moment bounds for `Sm = ∑_π P(π)`.
-/
import IIT.Census.PairIndep

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

noncomputable section

variable {L n : ℕ}

/-! ### Clamped coordinates -/

lemma continuous_clamp01 : Continuous clamp01 := by unfold clamp01; fun_prop

@[fun_prop]
lemma measurable_clamp01 : Measurable clamp01 := continuous_clamp01.measurable

lemma abs_clamp01_le (x : ℝ) : |clamp01 x| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [clamp01_nonneg x, clamp01_le_one x]

/-! ### Rows and monomials of a superblock -/

/-- Row product of the superblock row `π`. -/
def rowP (z : Loc L n) (π : Pb L) : ℝ := ∏ c : Col L n, clamp01 (z (π, c))

/-- Monomial with exponents `E` in the clamped coordinates. -/
def mono (z : Loc L n) (E : LI L n → ℕ) : ℝ := ∏ i, clamp01 (z i) ^ E i

/-- Exponent `a` on every coordinate of row `π`. -/
def rowE (π : Pb L) (a : ℕ) : LI L n → ℕ := fun i => if i.1 = π then a else 0

/-- Exponent one on the coordinate `p`. -/
def δE (p : LI L n) : LI L n → ℕ := fun i => if i = p then 1 else 0

lemma rowP_nonneg (z : Loc L n) (π : Pb L) : 0 ≤ rowP z π :=
  Finset.prod_nonneg fun _ _ => clamp01_nonneg _

lemma rowP_le_one (z : Loc L n) (π : Pb L) : rowP z π ≤ 1 :=
  Finset.prod_le_one (fun _ _ => clamp01_nonneg _) fun _ _ => clamp01_le_one _

lemma mono_nonneg (z : Loc L n) (E : LI L n → ℕ) : 0 ≤ mono z E :=
  Finset.prod_nonneg fun _ _ => pow_nonneg (clamp01_nonneg _) _

lemma mono_le_one (z : Loc L n) (E : LI L n → ℕ) : mono z E ≤ 1 :=
  Finset.prod_le_one (fun _ _ => pow_nonneg (clamp01_nonneg _) _)
    fun _ _ => pow_le_one₀ (clamp01_nonneg _) (clamp01_le_one _)

lemma mono_add (z : Loc L n) (E F : LI L n → ℕ) : mono z (E + F) = mono z E * mono z F := by
  simp [mono, pow_add, Finset.prod_mul_distrib]

lemma mono_rowE (z : Loc L n) (π : Pb L) (a : ℕ) : mono z (rowE π a) = rowP z π ^ a := by
  simp only [mono, rowE, rowP, Fintype.prod_prod_type, ← Finset.prod_pow]
  rw [Fintype.prod_eq_single π]
  · simp
  · intro ρ hρ; simp [hρ]

lemma mono_δE (z : Loc L n) (p : LI L n) : mono z (δE p) = clamp01 (z p) := by
  simp only [mono, δE]
  rw [Fintype.prod_eq_single p]
  · simp
  · intro i hi; simp [hi]

@[fun_prop]
lemma measurable_coord_cl (i : LI L n) : Measurable fun z : Loc L n => clamp01 (z i) :=
  measurable_clamp01.comp (measurable_pi_apply i)

@[fun_prop]
lemma measurable_mono (E : LI L n → ℕ) : Measurable fun z : Loc L n => mono z E :=
  Finset.measurable_prod _ fun i _ => (measurable_coord_cl i).pow_const _

@[fun_prop]
lemma measurable_rowP (π : Pb L) : Measurable fun z : Loc L n => rowP z π :=
  Finset.measurable_prod _ fun c _ => measurable_coord_cl (π, c)

lemma integrable_of_bdd {f : Loc L n → ℝ} (hf : Measurable f) (C : ℝ) (h : ∀ z, |f z| ≤ C) :
    Integrable f (locM L n) :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact h z)

lemma integrable_mono (E : LI L n → ℕ) : Integrable (fun z => mono z E) (locM L n) :=
  integrable_of_bdd (measurable_mono E) 1 fun z => by
    rw [abs_of_nonneg (mono_nonneg z E)]; exact mono_le_one z E

lemma integral_mono_loc (E : LI L n → ℕ) :
    ∫ z, mono z E ∂locM L n = ∏ i, 1 / ((E i : ℝ) + 1) := integral_monomial E

/-! ### Evaluating `∏ 1/(E+1)` -/

/-- Number of columns. -/
abbrev R (L n : ℕ) : ℕ := Fintype.card (Col L n)

lemma R_eq (L n : ℕ) : R L n = 2 * L + n := by
  simp [R, Fintype.card_sum, Fintype.card_prod]; ring

lemma prod_rowE (π : Pb L) (a : ℕ) :
    ∏ i : LI L n, 1 / ((rowE π a i : ℝ) + 1) = (1 / ((a : ℝ) + 1)) ^ R L n := by
  simp only [rowE, Fintype.prod_prod_type]
  rw [Fintype.prod_eq_single π]
  · simp [Finset.prod_const, R]
  · intro ρ hρ; simp [hρ]

lemma prod_upd (B : LI L n → ℕ) (p : LI L n) :
    ∏ i, 1 / (((B + δE p) i : ℕ) + (1 : ℝ)) =
      (∏ i, 1 / ((B i : ℝ) + 1)) * (((B p : ℝ) + 1) / ((B p : ℝ) + 2)) := by
  have h : ∀ i, 1 / (((B + δE p) i : ℕ) + (1 : ℝ)) =
      1 / ((B i : ℝ) + 1) * (if i = p then ((B p : ℝ) + 1) / ((B p : ℝ) + 2) else 1) := by
    intro i
    by_cases hi : i = p
    · subst hi
      simp only [Pi.add_apply, δE, ite_true, Nat.cast_add, Nat.cast_one]
      have : (0 : ℝ) < B i + 1 := by positivity
      field_simp
      ring
    · simp [δE, hi]
  simp_rw [h, Finset.prod_mul_distrib, Fintype.prod_ite_eq']

/-- The value of `E[P(π)² x_p x_q]` in units of `3^{-R}`. -/
def m2val (π : Pb L) (p q : LI L n) : ℝ :=
  if p = q then (if p.1 = π then 3 / 5 else 1 / 3)
  else (if p.1 = π then 3 / 4 else 1 / 2) * (if q.1 = π then 3 / 4 else 1 / 2)

lemma integral_m2 (π : Pb L) (p q : LI L n) :
    ∫ z, mono z (rowE π 2 + δE p + δE q) ∂locM L n = (1 / 3) ^ R L n * m2val π p q := by
  rw [integral_mono_loc, prod_upd, prod_upd, prod_rowE]
  have e3 : (1 : ℝ) / ((2 : ℕ) + 1) = 1 / 3 := by norm_num
  rw [e3, mul_assoc]
  congr 1
  unfold m2val
  by_cases hpq : p = q
  · subst hpq
    by_cases hp : p.1 = π <;> simp [rowE, δE, hp] <;> norm_num
  · have hqp : ¬ q = p := fun h => hpq h.symm
    by_cases hp : p.1 = π <;> by_cases hq : q.1 = π <;> simp [rowE, δE, hp, hq, hpq, hqp] <;>
      norm_num

/-- The value of `E[P(π) x_p]` in units of `2^{-R}`. -/
lemma integral_m1 (π : Pb L) (p : LI L n) :
    ∫ z, mono z (rowE π 1 + δE p) ∂locM L n =
      (1 / 2) ^ R L n * (if p.1 = π then 2 / 3 else 1 / 2) := by
  rw [integral_mono_loc, prod_upd, prod_rowE]
  have e2 : (1 : ℝ) / ((1 : ℕ) + 1) = 1 / 2 := by norm_num
  rw [e2]
  congr 1
  by_cases hp : p.1 = π <;> simp [rowE, hp] <;> norm_num

lemma integral_rowP_pow (π : Pb L) (a : ℕ) :
    ∫ z, rowP z π ^ a ∂locM L n = (1 / ((a : ℝ) + 1)) ^ R L n := by
  simp_rw [← mono_rowE, integral_mono_loc, prod_rowE]

lemma integral_rowP_mul {π π' : Pb L} (h : π ≠ π') :
    ∫ z, rowP z π * rowP z π' ∂locM L n = (1 / 4) ^ R L n := by
  have : ∀ z : Loc L n, rowP z π * rowP z π' = mono z (rowE π 1 + rowE π' 1) := by
    intro z; rw [mono_add, mono_rowE, mono_rowE, pow_one, pow_one]
  simp_rw [this, integral_mono_loc]
  simp only [Pi.add_apply, rowE, Fintype.prod_prod_type]
  have hf : ∀ ρ : Pb L, ∏ c : Col L n, 1 / ((((if ρ = π then 1 else 0) + (if ρ = π' then 1 else 0)
      : ℕ) : ℝ) + 1) = (if ρ = π then (1 / 2 : ℝ) ^ R L n else 1) *
        (if ρ = π' then (1 / 2 : ℝ) ^ R L n else 1) := by
    intro ρ
    by_cases h1 : ρ = π
    · subst h1; simp [h, Finset.prod_const, R]; norm_num
    · by_cases h2 : ρ = π'
      · subst h2; simp [h1, Finset.prod_const, R]; norm_num
      · simp [h1, h2]
  simp_rw [hf, Finset.prod_mul_distrib, Fintype.prod_ite_eq', ← mul_pow]
  norm_num

/-! ### Characters of the pair states -/

/-- `±1` sign of a bit. -/
def sg (b : Bool) : ℝ := if b then -1 else 1

/-- The three nontrivial characters of the pair states. -/
def chi (c : Fin 3) (u : PS) : ℝ := ![sg (u 0), sg (u 1), sg (u 0) * sg (u 1)] c

/-- Column weights: `(1, 1)` for `ε = 0` and `(1, -1)` for `ε = 1`. -/
def sgn (ε e : Fin 2) : ℝ := if e = 0 then 1 else if ε = 0 then 1 else -1

lemma sum_PS (f : PS → ℝ) :
    ∑ u, f u = f ![false, false] + f ![false, true] + f ![true, false] + f ![true, true] := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp]
  simp [Fintype.sum_prod_type, Fintype.sum_bool, finTwoArrowEquiv]
  ring

lemma sum_chi (c : Fin 3) : ∑ u, chi c u = 0 := by
  rw [sum_PS]; fin_cases c <;> simp [chi, sg] <;> norm_num

lemma sum_chi_mul (c c' : Fin 3) : ∑ u, chi c u * chi c' u = if c = c' then 4 else 0 := by
  rw [sum_PS]; fin_cases c <;> fin_cases c' <;> simp [chi, sg] <;> norm_num

lemma chi_mul_self (c : Fin 3) (u : PS) : chi c u * chi c u = 1 := by
  fin_cases c <;> simp [chi, sg] <;> split_ifs <;> norm_num

lemma abs_chi (c : Fin 3) (u : PS) : |chi c u| = 1 := by
  have h := chi_mul_self c u
  rw [← abs_mul_self, abs_mul] at h
  nlinarith [abs_nonneg (chi c u)]

lemma abs_sgn (ε e : Fin 2) : |sgn ε e| = 1 := by
  unfold sgn; split_ifs <;> simp

lemma sum_sgn (ε : Fin 2) : ∑ e, sgn ε e = if ε = 0 then 2 else 0 := by
  fin_cases ε <;> simp [sgn, Fin.sum_univ_two] <;> norm_num

lemma sum_sgn_mul (ε ε' : Fin 2) : ∑ e, sgn ε e * sgn ε' e = if ε = ε' then 2 else 0 := by
  fin_cases ε <;> fin_cases ε' <;> simp [sgn, Fin.sum_univ_two] <;> norm_num

lemma sum_mul_ite_eq {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ) (v : α) (x y : ℝ) :
    ∑ u, f u * (if u = v then x else y) = y * ∑ u, f u + (x - y) * f v := by
  have : ∀ u, f u * (if u = v then x else y) = y * f u + (if u = v then (x - y) * f u else 0) := by
    intro u; split_ifs <;> ring
  simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, Fintype.sum_ite_eq']

/-- Diagonal/off-diagonal splitting of a double sum. -/
lemma sum_sum_ite_diag {α : Type*} [Fintype α] [DecidableEq α] (x y D G : α → ℝ) :
    ∑ q, ∑ q', x q * y q' * (if q = q' then D q else G q * G q') =
      (∑ q, x q * G q) * (∑ q, y q * G q) + ∑ q, x q * y q * (D q - G q * G q) := by
  have : ∀ q q', x q * y q' * (if q = q' then D q else G q * G q') =
      x q * G q * (y q' * G q') + (if q' = q then x q * y q * (D q - G q * G q) else 0) := by
    intro q q'
    by_cases h : q = q'
    · subst h; simp; ring
    · simp [h, Ne.symm h]; ring
  simp_rw [this, Finset.sum_add_distrib, Fintype.sum_ite_eq', Finset.sum_mul_sum]

/-! ### Sums over the pair bits of a superblock row -/

lemma card_Pb (L : ℕ) : Fintype.card (Pb L) = 4 ^ L := by simp

lemma sum_pi_eval (k : Fin L) (f : PS → ℝ) :
    ∑ π : Pb L, f (π k) = 4 ^ (L - 1) * ∑ u, f u := by
  rw [Fintype.sum_equiv (Equiv.piSplitAt k (fun _ => PS)) (fun π => f (π k)) (fun p => f p.1)
    (fun _ => rfl), Fintype.sum_prod_type]
  simp [Finset.sum_const, Finset.mul_sum, Fintype.card_subtype_compl]

lemma sum_pi_eval2 {k l : Fin L} (hkl : k ≠ l) (f g : PS → ℝ) (hg : ∑ u, g u = 0) :
    ∑ π : Pb L, f (π k) * g (π l) = 0 := by
  rw [Fintype.sum_equiv (Equiv.piSplitAt l (fun _ => PS)) (fun π => f (π k) * g (π l))
    (fun p => f (p.2 ⟨k, hkl⟩) * g p.1) (fun _ => rfl), Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp [hg]

/-! ### The superblock statistics -/

/-- Index of a statistic: pair `k`, column weight `ε`, character `c`. -/
abbrev Ix (L : ℕ) := Fin L × Fin 2 × Fin 3

/-- Pair state and column. -/
abbrev Qt := PS × Fin 2

/-- The coordinate of row `π` with pair `k` set to `q.1`, column `(k, q.2)`. -/
def cpt (π : Pb L) (k : Fin L) (q : Qt) : LI L n := (Function.update π k q.1, Sum.inl (k, q.2))

/-- Coefficient of the contrast. -/
def coef (a : Ix L) (q : Qt) : ℝ := chi a.2.2 q.1 * sgn a.2.1 q.2

/-- The contrast of row `π`. -/
def ctr (z : Loc L n) (a : Ix L) (π : Pb L) : ℝ :=
  ∑ q : Qt, coef a q * clamp01 (z (cpt π a.1 q))

/-- The superblock statistic. -/
def Tst (z : Loc L n) (a : Ix L) : ℝ := ∑ π, rowP z π * ctr z a π

/-- Total row mass of a superblock. -/
def Sm (z : Loc L n) : ℝ := ∑ π, rowP z π

lemma abs_coef (a : Ix L) (q : Qt) : |coef a q| = 1 := by
  simp [coef, abs_mul, abs_chi, abs_sgn]

lemma sum_coef_mul (a : Ix L) (h : PS → ℝ) :
    ∑ q : Qt, coef a q * h q.1 = (∑ u, chi a.2.2 u * h u) * ∑ e, sgn a.2.1 e := by
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun e _ => ?_
  simp [coef]; ring

lemma sum_coef_coef_mul (a b : Ix L) (h : PS → ℝ) :
    ∑ q : Qt, coef a q * coef b q * h q.1 =
      (∑ u, chi a.2.2 u * chi b.2.2 u * h u) * ∑ e, sgn a.2.1 e * sgn b.2.1 e := by
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun e _ => ?_
  simp [coef]; ring

lemma abs_phi_le (z : Loc L n) (a : Ix L) (π : Pb L) : |ctr z a π| ≤ 8 := by
  unfold ctr
  calc |∑ q : Qt, coef a q * clamp01 (z (cpt π a.1 q))|
      ≤ ∑ q : Qt, |coef a q * clamp01 (z (cpt π a.1 q))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q : Qt, (1 : ℝ) := Finset.sum_le_sum fun _ _ => by
        rw [abs_mul, abs_coef, one_mul]; exact abs_clamp01_le _
    _ = 8 := by simp

lemma Sm_nonneg (z : Loc L n) : 0 ≤ Sm z := Finset.sum_nonneg fun π _ => rowP_nonneg z π

lemma abs_Tst_le (z : Loc L n) (a : Ix L) : |Tst z a| ≤ 8 * Sm z := by
  unfold Tst Sm
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun π _ => ?_)
  rw [abs_mul, abs_of_nonneg (rowP_nonneg z π), mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_phi_le z a π) (rowP_nonneg z π)

@[fun_prop]
lemma measurable_phi (a : Ix L) (π : Pb L) : Measurable fun z : Loc L n => ctr z a π :=
  Finset.measurable_sum _ fun q _ => (measurable_coord_cl _).const_mul _

@[fun_prop]
lemma measurable_Tst (a : Ix L) : Measurable fun z : Loc L n => Tst z a :=
  Finset.measurable_sum _ fun π _ => (measurable_rowP π).mul (measurable_phi a π)

@[fun_prop]
lemma measurable_Sm : Measurable fun z : Loc L n => Sm z :=
  Finset.measurable_sum _ fun π _ => measurable_rowP π

lemma update_eq_self_iff' (π : Pb L) (k : Fin L) (u : PS) :
    Function.update π k u = π ↔ u = π k := Function.update_eq_self_iff

/-! ### Mean zero -/

lemma rowP_mul_phi (z : Loc L n) (a : Ix L) (π : Pb L) :
    rowP z π * ctr z a π = ∑ q : Qt, coef a q * mono z (rowE π 1 + δE (cpt π a.1 q)) := by
  simp only [ctr, Finset.mul_sum, mono_add, mono_rowE, mono_δE, pow_one]
  refine Finset.sum_congr rfl fun q _ => by ring

lemma integral_Tst (a : Ix L) : ∫ z, Tst z a ∂locM L n = 0 := by
  have hint : ∀ π (q : Qt), Integrable (fun z => coef a q * mono z (rowE π 1 + δE (cpt π a.1 q)))
      (locM L n) := fun π q => (integrable_mono _).const_mul _
  simp_rw [Tst, rowP_mul_phi]
  rw [integral_finsetSum _ fun π _ => integrable_finsetSum _ fun q _ => hint π q]
  simp_rw [integral_finsetSum _ fun q _ => hint _ q, integral_const_mul, integral_m1]
  simp only [cpt, update_eq_self_iff']
  have : ∀ π : Pb L, ∑ q : Qt, coef a q * ((1 / 2) ^ R L n *
      (if q.1 = π a.1 then (2 : ℝ) / 3 else 1 / 2)) =
      (1 / 2) ^ R L n * ((1 / 6) * chi a.2.2 (π a.1)) * ∑ e, sgn a.2.1 e := by
    intro π
    simp_rw [mul_left_comm (coef a _)]
    rw [← Finset.mul_sum, sum_coef_mul a (fun u => if u = π a.1 then (2 : ℝ) / 3 else 1 / 2),
      sum_mul_ite_eq, sum_chi]
    ring
  simp_rw [this, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [sum_pi_eval a.1 (fun u => chi a.2.2 u), sum_chi]
  ring

/-! ### Covariance -/

/-- Limiting variances: `33/40` for `ε = 0`, `23/40` for `ε = 1`. -/
def ddv (ε : Fin 2) : ℝ := if ε = 0 then 33 / 40 else 23 / 40

/-- The limiting (diagonal) covariance. -/
def dd (a b : Ix L) : ℝ := if a = b then ddv a.2.1 else 0

lemma ddv_pos (ε : Fin 2) : 0 < ddv ε := by unfold ddv; split_ifs <;> norm_num

lemma cpt_eq_iff (π : Pb L) (k l : Fin L) (q q' : Qt) :
    cpt (n := n) π k q = cpt π l q' ↔ k = l ∧ q = q' := by
  constructor
  · intro h
    simp only [cpt, Prod.mk.injEq, Sum.inl.injEq] at h
    obtain ⟨h1, rfl, h3⟩ := h
    refine ⟨rfl, Prod.ext ?_ h3⟩
    exact Function.update_injective π k h1
  · rintro ⟨rfl, rfl⟩; rfl

lemma cpt_fst_eq (π : Pb L) (k : Fin L) (q : Qt) : (cpt (n := n) π k q).1 = π ↔ q.1 = π k :=
  update_eq_self_iff' π k q.1

lemma m2val_ne {π : Pb L} {k l : Fin L} (hkl : k ≠ l) (q q' : Qt) :
    m2val (n := n) π (cpt π k q) (cpt π l q') =
      (if q.1 = π k then 3 / 4 else 1 / 2) * (if q'.1 = π l then 3 / 4 else 1 / 2) := by
  unfold m2val
  rw [if_neg (fun h => hkl ((cpt_eq_iff π k l q q').mp h).1)]
  simp only [cpt_fst_eq]

lemma m2val_eq (π : Pb L) (k : Fin L) (q q' : Qt) :
    m2val (n := n) π (cpt π k q) (cpt π k q') =
      if q = q' then (if q.1 = π k then 3 / 5 else 1 / 3)
      else (if q.1 = π k then 3 / 4 else 1 / 2) * (if q'.1 = π k then 3 / 4 else 1 / 2) := by
  unfold m2val
  simp only [cpt_eq_iff, true_and, cpt_fst_eq]

/-- The diagonal sum, in units of `3^{-R}`. -/
def Wsum (a b : Ix L) : ℝ :=
  ∑ π : Pb L, ∑ q : Qt, ∑ q' : Qt, coef a q * coef b q' * m2val (n := n) π (cpt π a.1 q) (cpt π b.1 q')

lemma sum_chi_ite (c : Fin 3) (v : PS) (x y : ℝ) :
    ∑ u, chi c u * (if u = v then x else y) = (x - y) * chi c v := by
  rw [sum_mul_ite_eq, sum_chi]; ring

lemma Wsum_ne {a b : Ix L} (hab : a.1 ≠ b.1) : Wsum (n := n) a b = 0 := by
  unfold Wsum
  have h : ∀ π : Pb L, ∑ q : Qt, ∑ q' : Qt, coef a q * coef b q' *
      m2val (n := n) π (cpt π a.1 q) (cpt π b.1 q') =
      ((∑ e, sgn a.2.1 e) * (∑ e, sgn b.2.1 e) / 16) *
        (chi a.2.2 (π a.1) * chi b.2.2 (π b.1)) := by
    intro π
    simp_rw [m2val_ne hab]
    have : ∀ q q' : Qt, coef a q * coef b q' *
        ((if q.1 = π a.1 then (3 : ℝ) / 4 else 1 / 2) * (if q'.1 = π b.1 then 3 / 4 else 1 / 2)) =
        (coef a q * (if q.1 = π a.1 then (3 : ℝ) / 4 else 1 / 2)) *
          (coef b q' * (if q'.1 = π b.1 then 3 / 4 else 1 / 2)) := fun q q' => by ring
    simp_rw [this, ← Finset.sum_mul_sum]
    rw [sum_coef_mul a (fun u => if u = π a.1 then (3 : ℝ) / 4 else 1 / 2),
      sum_coef_mul b (fun u => if u = π b.1 then (3 : ℝ) / 4 else 1 / 2), sum_chi_ite, sum_chi_ite]
    ring
  simp_rw [h, ← Finset.mul_sum]
  rw [sum_pi_eval2 hab (fun u => chi a.2.2 u) (fun u => chi b.2.2 u) (sum_chi _), mul_zero]

lemma L_pos_of (k : Fin L) : 0 < L := Nat.pos_of_ne_zero fun h => by subst h; exact k.elim0

lemma Wsum_eq {a b : Ix L} (hab : a.1 = b.1) : Wsum (n := n) a b = 4 ^ L * dd a b := by
  obtain ⟨k, ε, c⟩ := a
  obtain ⟨l, ε', c'⟩ := b
  simp only at hab
  subst hab
  unfold Wsum
  have h : ∀ π : Pb L, ∑ q : Qt, ∑ q' : Qt, coef (k, ε, c) q * coef (k, ε', c') q' *
      m2val (n := n) π (cpt π k q) (cpt π k q') =
      ((∑ e, sgn ε e) * (∑ e, sgn ε' e) / 16 + (∑ e, sgn ε e * sgn ε' e) * (3 / 80 - 1 / 12)) *
        (chi c (π k) * chi c' (π k)) +
        (∑ e, sgn ε e * sgn ε' e) * ((1 / 12) * ∑ u, chi c u * chi c' u) := by
    intro π
    simp_rw [m2val_eq]
    rw [sum_sum_ite_diag (fun q => coef (k, ε, c) q) (fun q => coef (k, ε', c') q)
      (fun q => if q.1 = π k then 3 / 5 else 1 / 3) (fun q => if q.1 = π k then 3 / 4 else 1 / 2)]
    have hD : ∀ q : Qt, coef (k, ε, c) q * coef (k, ε', c') q *
        ((if q.1 = π k then (3 : ℝ) / 5 else 1 / 3) -
          (if q.1 = π k then (3 : ℝ) / 4 else 1 / 2) * (if q.1 = π k then (3 : ℝ) / 4 else 1 / 2)) =
        coef (k, ε, c) q * coef (k, ε', c') q * (if q.1 = π k then (3 : ℝ) / 80 else 1 / 12) := by
      intro q; split_ifs <;> norm_num
    simp_rw [hD]
    rw [sum_coef_mul (k, ε, c) (fun u => if u = π k then (3 : ℝ) / 4 else 1 / 2),
      sum_coef_mul (k, ε', c') (fun u => if u = π k then (3 : ℝ) / 4 else 1 / 2),
      sum_coef_coef_mul (k, ε, c) (k, ε', c') (fun u => if u = π k then (3 : ℝ) / 80 else 1 / 12)]
    simp only
    rw [sum_chi_ite, sum_chi_ite]
    have : ∑ u, chi c u * chi c' u * (if u = π k then (3 : ℝ) / 80 else 1 / 12) =
        1 / 12 * ∑ u, chi c u * chi c' u + (3 / 80 - 1 / 12) * (chi c (π k) * chi c' (π k)) := by
      rw [sum_mul_ite_eq (fun u => chi c u * chi c' u)]
    rw [this]
    ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_pi_eval k (fun u => chi c u * chi c' u), sum_chi_mul, sum_sgn, sum_sgn, sum_sgn_mul]
  simp only [Finset.sum_const, Finset.card_univ, card_Pb, nsmul_eq_mul]
  have hL : (4 : ℝ) ^ L = 4 ^ (L - 1) * 4 := by
    rw [← pow_succ, Nat.sub_add_cancel (L_pos_of k)]
  unfold dd ddv
  simp only [Prod.mk.injEq, true_and]
  rw [hL]
  by_cases hc : c = c' <;> by_cases he : ε = ε' <;> simp [hc, he]
  · subst he; by_cases h0 : ε = 0 <;> simp [h0] <;> rw [← hL] <;> ring
  · intro h1 h0; exact he (h0.trans h1.symm)

lemma Wsum_val (a b : Ix L) : Wsum (n := n) a b = 4 ^ L * dd a b := by
  by_cases hab : a.1 = b.1
  · exact Wsum_eq hab
  · rw [Wsum_ne hab]
    unfold dd
    rw [if_neg (fun h => hab (by rw [h])), mul_zero]

lemma abs_rowP_le (z : Loc L n) (π : Pb L) : |rowP z π| ≤ 1 := by
  rw [abs_of_nonneg (rowP_nonneg z π)]; exact rowP_le_one z π

lemma abs_pp_le (z : Loc L n) (a b : Ix L) (π π' : Pb L) :
    |rowP z π * ctr z a π * (rowP z π' * ctr z b π')| ≤ 64 * (rowP z π * rowP z π') := by
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (rowP_nonneg z π),
    abs_of_nonneg (rowP_nonneg z π')]
  have h1 := abs_phi_le z a π
  have h2 := abs_phi_le z b π'
  have r1 := rowP_nonneg z π
  have r2 := rowP_nonneg z π'
  have : rowP z π * |ctr z a π| * (rowP z π' * |ctr z b π'|) =
      (rowP z π * rowP z π') * (|ctr z a π| * |ctr z b π'|) := by ring
  rw [this, mul_comm 64]
  exact mul_le_mul_of_nonneg_left (by nlinarith [abs_nonneg (ctr z a π), abs_nonneg (ctr z b π')])
    (mul_nonneg r1 r2)

lemma integrable_pp (a b : Ix L) (π π' : Pb L) :
    Integrable (fun z => rowP z π * ctr z a π * (rowP z π' * ctr z b π')) (locM L n) :=
  integrable_of_bdd (by fun_prop) 64 fun z => (abs_pp_le z a b π π').trans (by
    have := mul_le_one₀ (rowP_le_one z π) (rowP_nonneg z π') (rowP_le_one z π')
    linarith)

lemma integrable_rowP_mul (π π' : Pb L) :
    Integrable (fun z => rowP z π * rowP z π') (locM L n) :=
  integrable_of_bdd (by fun_prop) 1 fun z => by
    rw [abs_mul]
    exact mul_le_one₀ (abs_rowP_le z π) (abs_nonneg _) (abs_rowP_le z π')

/-- The off-diagonal (distinct rows) part of `E T_a T_b`. -/
def Off (a b : Ix L) : ℝ :=
  ∑ π : Pb L, ∑ π' ∈ univ.erase π, ∫ z, rowP z π * ctr z a π * (rowP z π' * ctr z b π') ∂locM L n

lemma pp_diag_eq (z : Loc L n) (a b : Ix L) (π : Pb L) :
    rowP z π * ctr z a π * (rowP z π * ctr z b π) = ∑ q : Qt, ∑ q' : Qt,
      coef a q * coef b q' * mono z (rowE π 2 + δE (cpt π a.1 q) + δE (cpt π b.1 q')) := by
  simp only [mono_add, mono_rowE, mono_δE, ctr, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => by ring

lemma integral_diag (a b : Ix L) (π : Pb L) :
    ∫ z, rowP z π * ctr z a π * (rowP z π * ctr z b π) ∂locM L n = (1 / 3) ^ R L n *
      ∑ q : Qt, ∑ q' : Qt, coef a q * coef b q' * m2val (n := n) π (cpt π a.1 q) (cpt π b.1 q') := by
  have hint : ∀ q q' : Qt, Integrable (fun z => coef a q * coef b q' *
      mono z (rowE π 2 + δE (cpt π a.1 q) + δE (cpt π b.1 q'))) (locM L n) :=
    fun q q' => (integrable_mono _).const_mul _
  simp_rw [pp_diag_eq]
  rw [integral_finsetSum _ fun q _ => integrable_finsetSum _ fun q' _ => hint q q']
  simp_rw [integral_finsetSum _ fun q' _ => hint _ q', integral_const_mul, integral_m2,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => by ring

lemma integral_TT (a b : Ix L) :
    ∫ z, Tst z a * Tst z b ∂locM L n = (1 / 3) ^ R L n * 4 ^ L * dd a b + Off (n := n) a b := by
  have h : ∀ z : Loc L n, Tst z a * Tst z b =
      ∑ π, ∑ π', rowP z π * ctr z a π * (rowP z π' * ctr z b π') := by
    intro z; unfold Tst; rw [Finset.sum_mul_sum]
  simp_rw [h]
  rw [integral_finsetSum _ fun π _ => integrable_finsetSum _ fun π' _ => integrable_pp a b π π']
  simp_rw [integral_finsetSum _ fun π' _ => integrable_pp a b _ π']
  rw [Finset.sum_congr rfl fun π _ => (Finset.add_sum_erase _ _ (mem_univ π)).symm,
    Finset.sum_add_distrib]
  simp_rw [integral_diag]
  rw [← Finset.mul_sum]
  change (1 / 3) ^ R L n * Wsum (n := n) a b + Off a b = _
  rw [Wsum_val]; ring

lemma abs_integral_pp_le (a b : Ix L) {π π' : Pb L} (h : π ≠ π') :
    |∫ z, rowP z π * ctr z a π * (rowP z π' * ctr z b π') ∂locM L n| ≤ 64 * (1 / 4) ^ R L n := by
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ z, |rowP z π * ctr z a π * (rowP z π' * ctr z b π')| ∂locM L n
      ≤ ∫ z, 64 * (rowP z π * rowP z π') ∂locM L n :=
        integral_mono (integrable_pp a b π π').abs ((integrable_rowP_mul π π').const_mul _)
          fun z => abs_pp_le z a b π π'
    _ = 64 * (1 / 4) ^ R L n := by rw [integral_const_mul, integral_rowP_mul h]

lemma abs_Off_le (a b : Ix L) : |Off (n := n) a b| ≤ 16 ^ L * (64 * (1 / 4) ^ R L n) := by
  unfold Off
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ π : Pb L, |∑ π' ∈ univ.erase π,
        ∫ z, rowP z π * ctr z a π * (rowP z π' * ctr z b π') ∂locM L n|
      ≤ ∑ _π : Pb L, ∑ _π' : Pb L, 64 * (1 / 4 : ℝ) ^ R L n := by
        refine Finset.sum_le_sum fun π _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun π' hπ' => abs_integral_pp_le a b
          (Finset.ne_of_mem_erase hπ').symm).trans ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          fun _ _ _ => by positivity
    _ = 16 ^ L * (64 * (1 / 4) ^ R L n) := by
        simp only [Finset.sum_const, Finset.card_univ, card_Pb, nsmul_eq_mul]
        push_cast
        rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num

/-! ### Moments of the row mass -/

lemma integral_rowP_sq (π : Pb L) : ∫ z, rowP z π ^ 2 ∂locM L n = (1 / 3) ^ R L n := by
  rw [integral_rowP_pow]; norm_num

lemma integrable_rowP_pow (π : Pb L) (a : ℕ) :
    Integrable (fun z => rowP z π ^ a) (locM L n) :=
  integrable_of_bdd (by fun_prop) 1 fun z => by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (abs_rowP_le z π)

lemma integrable_Sm_pow (a : ℕ) : Integrable (fun z => Sm z ^ a) (locM L n) :=
  integrable_of_bdd (by fun_prop) ((4 ^ L : ℝ) ^ a) fun z => by
    rw [abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ a
    rw [abs_of_nonneg (Sm_nonneg z)]
    calc Sm z ≤ ∑ _π : Pb L, (1 : ℝ) := Finset.sum_le_sum fun π _ => rowP_le_one z π
      _ = 4 ^ L := by simp

lemma integral_Sm_sq_le : ∫ z, Sm z ^ 2 ∂locM L n ≤ (4 ^ L) ^ 2 * (1 / 3) ^ R L n := by
  calc ∫ z, Sm z ^ 2 ∂locM L n ≤ ∫ z, (4 ^ L : ℝ) * ∑ π, rowP z π ^ 2 ∂locM L n := by
        refine integral_mono (integrable_Sm_pow 2)
          ((integrable_finsetSum _ fun π _ => integrable_rowP_pow π 2).const_mul _) fun z => ?_
        have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Pb L))) (f := fun π => rowP z π)
        simpa [Sm] using this
    _ = (4 ^ L) ^ 2 * (1 / 3) ^ R L n := by
        rw [integral_const_mul, integral_finsetSum _ fun π _ => integrable_rowP_pow π 2]
        simp_rw [integral_rowP_sq]
        simp [Finset.sum_const]; ring

lemma integral_Sm_pow4_le : ∫ z, Sm z ^ 4 ∂locM L n ≤ (4 ^ L) ^ 4 * (1 / 5) ^ R L n := by
  calc ∫ z, Sm z ^ 4 ∂locM L n ≤ ∫ z, ((4 ^ L : ℝ) ^ 3) * ∑ π, rowP z π ^ 4 ∂locM L n := by
        refine integral_mono (integrable_Sm_pow 4)
          ((integrable_finsetSum _ fun π _ => integrable_rowP_pow π 4).const_mul _) fun z => ?_
        have := pow_sum_le_card_mul_sum_pow (s := (univ : Finset (Pb L)))
          (f := fun π => rowP z π) (fun π _ => rowP_nonneg z π) 3
        simpa [Sm] using this
    _ = (4 ^ L) ^ 4 * (1 / 5) ^ R L n := by
        rw [integral_const_mul, integral_finsetSum _ fun π _ => integrable_rowP_pow π 4]
        simp_rw [integral_rowP_pow]
        simp [Finset.sum_const]; norm_num; ring

end

end Census
end IIT
