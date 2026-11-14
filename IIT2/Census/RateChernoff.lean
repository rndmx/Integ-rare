/-
Census of IIT 2.0, rate (Proposition `prop:rate` of the note `pc2-limit.tex`):
a one-sided Chernoff bound for sums of independent bounded-above summands
(`exp u ≤ 1 + u + u²` for `u ≤ 1`), and its block version for averages over `State N`.
-/
import IIT2.Census.Main

namespace IIT2

open MeasureTheory ProbabilityTheory Finset Real

variable {N : ℕ}

lemma exp_le_quad {u : ℝ} (hu : u ≤ 1) : Real.exp u ≤ 1 + u + u ^ 2 := by
  rcases le_or_gt (-1) u with h | h
  · have := Real.abs_exp_sub_one_sub_id_le (abs_le.mpr ⟨h, hu⟩)
    have := (abs_le.mp this).2; linarith
  · have h1 : Real.exp u ≤ Real.exp (-1) := Real.exp_le_exp.mpr h.le
    have h2 : Real.exp (-1) < 1 :=
      (Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num)).trans_eq Real.exp_zero
    nlinarith

lemma DepC.comp' {A : Finset (Fin N × State N)} {f : Ωf N → ℝ} (hf : DepC A f) (φ : ℝ → ℝ) :
    DepC A (fun ω => φ (f ω)) := fun ω ω' h => by show φ (f ω) = φ (f ω'); rw [hf ω ω' h]

/-- Expectations of products of functions of pairwise disjoint coordinate sets factorize. -/
theorem integral_prod_disj {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (A : ι → Finset (Fin N × State N)) (hA : (s : Set ι).PairwiseDisjoint A)
    (F : ι → Ωf N → ℝ) (hm : ∀ i, Measurable (F i)) (hd : ∀ i, DepC (A i) (F i)) :
    ∫ ω, (∏ i ∈ s, F i ω) ∂(μP N) = ∏ i ∈ s, ∫ ω, F i ω ∂(μP N) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    have hA' : (s : Set ι).PairwiseDisjoint A :=
      hA.subset (by simp only [Finset.coe_insert]; exact Set.subset_insert _ _)
    have hdis : Disjoint (A a) (s.biUnion A) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hA (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))
    have hdep : DepC (s.biUnion A) (fun ω => ∏ i ∈ s, F i ω) := fun ω ω' hw =>
      Finset.prod_congr rfl fun i hi => hd i ω ω' fun p hp =>
        hw p (Finset.mem_biUnion.mpr ⟨i, hi, hp⟩)
    rw [integral_mul_of_depC hdis (hm a) (Finset.measurable_prod _ fun i _ => hm i) (hd a) hdep,
      ih hA']

/-- One-sided Chernoff bound: independent (disjoint coordinates) bounded summands with
`λ F_i ≤ 1`. -/
theorem chernoff_family {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (A : ι → Finset (Fin N × State N)) (hA : (s : Set ι).PairwiseDisjoint A)
    (F : ι → Ωf N → ℝ) (hm : ∀ i, Measurable (F i)) (hd : ∀ i, DepC (A i) (F i))
    (C : ℝ) (hb : ∀ i ω, |F i ω| ≤ C) (lam : ℝ) (hl : 0 < lam) (hF : ∀ i ω, lam * F i ω ≤ 1)
    (t : ℝ) :
    (μP N).real {ω | (∑ i ∈ s, ∫ ω', F i ω' ∂(μP N)) + t ≤ ∑ i ∈ s, F i ω} ≤
      Real.exp (-lam * t + lam ^ 2 * ∑ i ∈ s, ∫ ω, F i ω ^ 2 ∂(μP N)) := by
  set X : Ωf N → ℝ := fun ω => ∑ i ∈ s, F i ω
  have hX : Measurable X := Finset.measurable_sum _ fun i _ => hm i
  have hXle : ∀ ω, X ω ≤ s.card * C := fun ω => by
    have : X ω ≤ ∑ _i ∈ s, C := Finset.sum_le_sum fun i _ => (abs_le.mp (hb i ω)).2
    rw [Finset.sum_const, nsmul_eq_mul] at this; exact this
  have hexpint : Integrable (fun ω => Real.exp (lam * X ω)) (μP N) :=
    integrable_of_bdd (Real.measurable_exp.comp (hX.const_mul lam)) (Real.exp (lam * (s.card * C)))
      fun ω => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hXle ω) hl.le)
  have h1 := measure_ge_le_exp_mul_mgf (μ := μP N) (X := X)
    ((∑ i ∈ s, ∫ ω', F i ω' ∂(μP N)) + t) hl.le hexpint
  have hmgf : mgf X (μP N) lam = ∏ i ∈ s, ∫ ω, Real.exp (lam * F i ω) ∂(μP N) := by
    unfold mgf
    have : ∀ ω, Real.exp (lam * X ω) = ∏ i ∈ s, Real.exp (lam * F i ω) := fun ω => by
      simp only [X]; rw [Finset.mul_sum, Real.exp_sum]
    simp_rw [this]
    exact integral_prod_disj s A hA (fun i ω => Real.exp (lam * F i ω))
      (fun i => Real.measurable_exp.comp ((hm i).const_mul lam))
      (fun i => (hd i).comp' (fun u => Real.exp (lam * u)))
  have hone : ∀ i, ∫ ω, Real.exp (lam * F i ω) ∂(μP N) ≤
      Real.exp (lam * ∫ ω, F i ω ∂(μP N) + lam ^ 2 * ∫ ω, F i ω ^ 2 ∂(μP N)) := by
    intro i
    have hFi : Integrable (F i) (μP N) := integrable_of_bdd (hm i) C (hb i)
    have hF2 : Integrable (fun ω => F i ω ^ 2) (μP N) :=
      integrable_of_bdd ((hm i).pow_const 2) (C ^ 2) fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb i ω) 2
    have hE : Integrable (fun ω => Real.exp (lam * F i ω)) (μP N) :=
      integrable_of_bdd (Real.measurable_exp.comp ((hm i).const_mul lam)) (Real.exp 1) fun ω => by
        rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (hF i ω)
    have hle : ∫ ω, Real.exp (lam * F i ω) ∂(μP N) ≤
        ∫ ω, (1 + lam * F i ω + lam ^ 2 * F i ω ^ 2) ∂(μP N) :=
      integral_mono hE (((integrable_const _).add (hFi.const_mul lam)).add (hF2.const_mul _))
        fun ω => by
          have := exp_le_quad (hF i ω)
          simp only; nlinarith
    have hcomp : ∫ ω, (1 + lam * F i ω + lam ^ 2 * F i ω ^ 2) ∂(μP N) =
        1 + lam * ∫ ω, F i ω ∂(μP N) + lam ^ 2 * ∫ ω, F i ω ^ 2 ∂(μP N) := by
      rw [integral_add (f := fun ω => 1 + lam * F i ω) (g := fun ω => lam ^ 2 * F i ω ^ 2)
        ((integrable_const _).add (hFi.const_mul lam)) (hF2.const_mul _),
        integral_add (f := fun _ => (1 : ℝ)) (g := fun ω => lam * F i ω)
        (integrable_const _) (hFi.const_mul lam), integral_const_mul, integral_const_mul]
      simp
    rw [hcomp] at hle
    refine hle.trans ?_
    have := Real.add_one_le_exp (lam * ∫ ω, F i ω ∂(μP N) + lam ^ 2 * ∫ ω, F i ω ^ 2 ∂(μP N))
    linarith
  have hprod : ∏ i ∈ s, ∫ ω, Real.exp (lam * F i ω) ∂(μP N) ≤
      ∏ i ∈ s, Real.exp (lam * ∫ ω, F i ω ∂(μP N) + lam ^ 2 * ∫ ω, F i ω ^ 2 ∂(μP N)) :=
    Finset.prod_le_prod (fun i _ => integral_nonneg fun ω => (Real.exp_pos _).le)
      (fun i _ => hone i)
  rw [← Real.exp_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hprod
  rw [hmgf] at h1
  refine h1.trans ?_
  calc Real.exp (-lam * ((∑ i ∈ s, ∫ ω', F i ω' ∂(μP N)) + t)) *
        ∏ i ∈ s, ∫ ω, Real.exp (lam * F i ω) ∂(μP N)
      ≤ Real.exp (-lam * ((∑ i ∈ s, ∫ ω', F i ω' ∂(μP N)) + t)) *
        Real.exp (lam * (∑ i ∈ s, ∫ ω, F i ω ∂(μP N)) +
          lam ^ 2 * ∑ i ∈ s, ∫ ω, F i ω ^ 2 ∂(μP N)) :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-! ## Blocks of `State N` indexed by representatives -/

/-- The representative of the block of `x`: `x` on `M`, `false` outside. -/
def rep (M : Finset (Fin N)) (x : State N) : State N := fun i => if i ∈ M then x i else false

lemma rep_rep (M : Finset (Fin N)) (x : State N) : rep M (rep M x) = rep M x := by
  funext i; unfold rep; split_ifs <;> rfl

def reps (M : Finset (Fin N)) : Finset (State N) := Finset.univ.filter (fun r => rep M r = r)

def fib (M : Finset (Fin N)) (r : State N) : Finset (State N) :=
  Finset.univ.filter (fun x => rep M x = r)

lemma fib_sub_blk (M : Finset (Fin N)) (r : State N) : fib M r ⊆ blk M r := by
  intro x hx
  simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  rw [mem_blk]
  intro i hi
  rw [← hx]; unfold rep; simp [hi]

lemma card_fib_le (M : Finset (Fin N)) (r : State N) :
    ((fib M r).card : ℝ) ≤ 2 ^ (N - M.card) := by
  have := Finset.card_le_card (fib_sub_blk M r)
  rw [card_blk] at this
  exact_mod_cast this

lemma bset_eq_of_mem_blk {M : Finset (Fin N)} {x r : State N} (h : x ∈ blk M r) :
    bset M x = bset M r := by
  unfold bset
  congr 1
  ext c
  rw [mem_blk, mem_blk]
  rw [mem_blk] at h
  constructor
  · intro hc i hi; rw [hc i hi, h i hi]
  · intro hc i hi; rw [hc i hi, h i hi]

lemma reps_pairwiseDisjoint (M : Finset (Fin N)) :
    ((reps M : Finset (State N)) : Set (State N)).PairwiseDisjoint (bset M) := by
  intro r hr r' hr' hne
  simp only [reps, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hr hr'
  refine Finset.disjoint_product.mpr (Or.inr (blk_disjoint ?_))
  intro h
  apply hne
  rw [← hr, ← hr']
  funext i
  unfold rep
  split_ifs with hi
  · exact ((mem_blk.mp h) i hi).symm
  · rfl

lemma sum_reps (M : Finset (Fin N)) (f : State N → ℝ) :
    ∑ x, f x = ∑ r ∈ reps M, ∑ x ∈ fib M r, f x := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := reps M) (g := rep M)
    (fun x _ => by simp [reps, rep_rep])]
  rfl

/-- Chernoff bound for a block-dependent average, upper tail. -/
theorem chernoff_avg (M : Finset (Fin N)) (G : State N → Ωf N → ℝ)
    (hm : ∀ x, Measurable (G x)) (C : ℝ) (hb : ∀ x ω, |G x ω| ≤ C)
    (hd : ∀ x, DepC (bset M x) (G x)) (c : ℝ) (hc : 0 ≤ c) (hGc : ∀ x ω, G x ω ≤ c)
    (lam : ℝ) (hl : 0 < lam) (hlc : lam * 2 ^ (N - M.card) * c ≤ 1)
    (σ2 : ℝ) (hσ : ∀ x, ∫ ω, (G x ω) ^ 2 ∂(μP N) ≤ σ2) (t : ℝ) :
    (μP N).real {ω | t ≤ avg (fun x => G x ω) - avg (fun x => ∫ ω', G x ω' ∂(μP N))} ≤
      Real.exp (-lam * 2 ^ N * t + lam ^ 2 * 2 ^ (N - M.card) * 2 ^ N * σ2) := by
  set F : State N → Ωf N → ℝ := fun r ω => ∑ x ∈ fib M r, G x ω
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hb (fun _ => false) 0)
  have hFm : ∀ r, Measurable (F r) := fun r => Finset.measurable_sum _ fun x _ => hm x
  have hFd : ∀ r, DepC (bset M r) (F r) := by
    intro r ω ω' h
    refine Finset.sum_congr rfl fun x hx => hd x ω ω' ?_
    rw [bset_eq_of_mem_blk (fib_sub_blk M r hx)]; exact h
  have hFb : ∀ r ω, |F r ω| ≤ ∑ _x : State N, C := fun r ω =>
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun x _ => hb x ω).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => hC0))
  have hFc : ∀ r ω, lam * F r ω ≤ 1 := by
    intro r ω
    have h1 : F r ω ≤ (fib M r).card * c := by
      have : F r ω ≤ ∑ _x ∈ fib M r, c := Finset.sum_le_sum fun x _ => hGc x ω
      rw [Finset.sum_const, nsmul_eq_mul] at this; exact this
    have h2 : (fib M r).card * c ≤ 2 ^ (N - M.card) * c :=
      mul_le_mul_of_nonneg_right (card_fib_le M r) hc
    nlinarith
  have hch := chernoff_family (reps M) (bset M) (reps_pairwiseDisjoint M) F hFm hFd _ hFb lam hl
    hFc (2 ^ N * t)
  have hGi : ∀ x, Integrable (G x) (μP N) := fun x => integrable_of_bdd (hm x) C (hb x)
  have hsumF : ∀ ω, ∑ r ∈ reps M, F r ω = ∑ x, G x ω := fun ω => (sum_reps M _).symm
  have hsumEF : ∑ r ∈ reps M, ∫ ω', F r ω' ∂(μP N) = ∑ x, ∫ ω', G x ω' ∂(μP N) := by
    rw [sum_reps M]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact integral_finsetSum _ fun x _ => hGi x
  have hK : (Fintype.card (State N) : ℝ) = 2 ^ N := by simp
  have hsub : {ω | t ≤ avg (fun x => G x ω) - avg (fun x => ∫ ω', G x ω' ∂(μP N))} ⊆
      {ω | (∑ r ∈ reps M, ∫ ω', F r ω' ∂(μP N)) + 2 ^ N * t ≤ ∑ r ∈ reps M, F r ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hsumF, hsumEF]
    unfold avg at hω
    rw [hK, ← sub_div, le_div_iff₀ (by positivity)] at hω
    linarith
  refine (measureReal_mono hsub).trans (hch.trans (Real.exp_le_exp.mpr ?_))
  -- second moments
  have hF2 : ∑ r ∈ reps M, ∫ ω, F r ω ^ 2 ∂(μP N) ≤ 2 ^ (N - M.card) * 2 ^ N * σ2 := by
    have hG2 : ∀ x, Integrable (fun ω => G x ω ^ 2) (μP N) := fun x =>
      integrable_of_bdd ((hm x).pow_const 2) (C ^ 2) fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb x ω) 2
    have hσ0 : 0 ≤ σ2 := (integral_nonneg fun ω => sq_nonneg (G (fun _ => false) ω)).trans
      (hσ _)
    have hr : ∀ r, ∫ ω, F r ω ^ 2 ∂(μP N) ≤ 2 ^ (N - M.card) * ∑ x ∈ fib M r, σ2 := by
      intro r
      have hpt : ∀ ω, F r ω ^ 2 ≤ (fib M r).card * ∑ x ∈ fib M r, G x ω ^ 2 := fun ω =>
        sq_sum_le_card_mul_sum_sq
      have hint : Integrable (fun ω => F r ω ^ 2) (μP N) :=
        integrable_of_bdd ((hFm r).pow_const 2) ((∑ _x : State N, C) ^ 2) fun ω => by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hFb r ω) 2
      refine (integral_mono hint ((integrable_finsetSum _ fun x _ => hG2 x).const_mul _) hpt).trans ?_
      rw [integral_const_mul, integral_finsetSum _ fun x _ => hG2 x]
      have h1 : ∑ x ∈ fib M r, ∫ ω, G x ω ^ 2 ∂(μP N) ≤ ∑ x ∈ fib M r, σ2 :=
        Finset.sum_le_sum fun x _ => hσ x
      have h2 : (0 : ℝ) ≤ ∑ x ∈ fib M r, σ2 := Finset.sum_nonneg fun _ _ => hσ0
      have h3 := card_fib_le M r
      have h4 : (0 : ℝ) ≤ ∑ x ∈ fib M r, ∫ ω, G x ω ^ 2 ∂(μP N) :=
        Finset.sum_nonneg fun x _ => integral_nonneg fun ω => sq_nonneg _
      calc ((fib M r).card : ℝ) * ∑ x ∈ fib M r, ∫ ω, G x ω ^ 2 ∂(μP N)
          ≤ 2 ^ (N - M.card) * ∑ x ∈ fib M r, ∫ ω, G x ω ^ 2 ∂(μP N) :=
            mul_le_mul_of_nonneg_right h3 h4
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    refine (Finset.sum_le_sum fun r _ => hr r).trans (le_of_eq ?_)
    rw [← Finset.mul_sum, ← sum_reps M (fun _ => σ2), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hK]
    ring
  have := mul_le_mul_of_nonneg_left hF2 (sq_nonneg lam)
  nlinarith

end IIT2
