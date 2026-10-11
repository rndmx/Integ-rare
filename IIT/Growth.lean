/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import IIT.System

/-!
# `[UB, §2.2]`: summing `φ_r` over all subsets of the distinction set

`[UB, Eq 11]` rewrites the sum of `φ_r` over *every* subset of the distinction set `D` as
a sum over **units-in-state**.  The rewrite is what makes the growth bound `[UB, Eq 16]`
reachable at all: the left side has `2^|D|` terms, the right side has `O(N)` of them.

The engine is a purely combinatorial identity about minima over subsets, proved here in
full.  Writing `f` for the per-unit integration `φ_d / |z_d|` of a distinction:

    Σ_{∅ ≠ d ⊆ A}  minVal f d  =  Σ_{a ∈ A}  f a * 2 ^ #{b ∈ A : a < b}

where `minVal f d` is `f` at the `≤`-least element of `d`, which equals `min_{a ∈ d} f a`
whenever the order sorts `f` (`minVal_eq_inf'`) -- the paper's sorted indexing.

Sorting `A` as `f_(1) ≤ … ≤ f_(n)` turns the exponent into `n - i`, which is exactly the
`2^(|Z(o)| - i)` of `[UB, Eq 11]`; dropping the singletons accounts for its `- 1`.
-/

namespace IIT

open Finset

variable {ι : Type*} [DecidableEq ι] [LinearOrder ι]

/-- `f` evaluated at the `≤`-**least element** of `d`, extended by `0` on the empty set.

This is *not* `min_{a ∈ d} f a` in general; the two agree whenever `f` is monotone
along the order, which is `minVal_eq_inf'` below.  `[UB, Eq 11]` sorts `𝒵(o)` by
increasing `φ/|z|`, i.e. chooses the order so that they do agree, and that is how the
identities below are applied. -/
noncomputable def minVal (f : ι → ℝ) (d : Finset ι) : ℝ :=
  if h : d.Nonempty then f (d.min' h) else 0

@[simp] lemma minVal_empty (f : ι → ℝ) : minVal f ∅ = 0 := by simp [minVal]

@[simp] lemma minVal_singleton (f : ι → ℝ) (a : ι) : minVal f {a} = f a := by
  simp [minVal]

/-- **When the order sorts `f`, `minVal` is the genuine minimum.**  `[UB, Eq 11]`'s
"sorted indexing of the elements in `𝒵(o)`" is exactly this hypothesis, so under it the
identities below are statements about `min_{a ∈ d} f a`, the quantity appearing in
`[UB, Eq 8]` and in `relPhi`. -/
lemma minVal_eq_inf' (f : ι → ℝ) {d : Finset ι} (hd : d.Nonempty)
    (h : ∀ a ∈ d, ∀ b ∈ d, a < b → f a ≤ f b) : minVal f d = d.inf' hd f := by
  rw [minVal, dif_pos hd]
  refine le_antisymm (Finset.le_inf' hd _ ?_) (Finset.inf'_le _ (d.min'_mem hd))
  intro b hb
  rcases eq_or_lt_of_le (d.min'_le b hb) with heq | hlt
  · rw [heq]
  · exact h _ (d.min'_mem hd) b hb hlt

/-- If `a` is below everything in `d`, the minimum over `insert a d` is `f a`. -/
lemma minVal_insert_of_le (f : ι → ℝ) {a : ι} {d : Finset ι} (h : ∀ b ∈ d, a ≤ b) :
    minVal f (insert a d) = f a := by
  have hne : (insert a d).Nonempty := ⟨a, Finset.mem_insert_self _ _⟩
  rw [minVal, dif_pos hne]
  congr 1
  refine le_antisymm (Finset.min'_le _ _ (Finset.mem_insert_self _ _)) ?_
  refine Finset.le_min' _ _ _ ?_
  intro b hb
  rcases Finset.mem_insert.1 hb with rfl | hb
  · exact le_rfl
  · exact h b hb

/-- **The engine of `[UB, Eq 11]`.**

Summing `minVal f` -- `f` at the order-least element -- over every subset of `A` equals a
sum over the *elements* of `A`, each weighted by `2` to the number of elements above it.
By `minVal_eq_inf'`, when the order sorts `f` this is a sum of genuine
minima.  Equivalently, after sorting
`f_(1) ≤ … ≤ f_(n)`, the weight on `f_(i)` is `2 ^ (n - i)`: a subset has `f_(i)` as its
minimum exactly when it contains `a_(i)` and no earlier element, leaving the later ones
free.

Proved by strong induction, peeling off `A.min'`: the subsets containing it all have the
same minimum, and the rest are exactly the subsets of `A.erase (A.min')`. -/
theorem sum_powerset_minVal (f : ι → ℝ) (A : Finset ι) :
    ∑ d ∈ A.powerset, minVal f d
      = ∑ a ∈ A, f a * 2 ^ (A.filter (fun b => a < b)).card := by
  induction A using Finset.strongInduction with
  | _ A ih =>
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  · set a := A.min' hA with ha
    set B := A.erase a with hB
    have haA : a ∈ A := A.min'_mem hA
    have haB : a ∉ B := Finset.notMem_erase _ _
    have hAeq : A = insert a B := by rw [hB, Finset.insert_erase haA]
    have hBss : B ⊂ A := Finset.erase_ssubset haA
    have hlt : ∀ b ∈ B, a < b := by
      intro b hb
      exact lt_of_le_of_ne (A.min'_le b (Finset.mem_of_mem_erase hb))
        (Ne.symm (Finset.ne_of_mem_erase hb))
    have hle : ∀ {d : Finset ι}, d ⊆ B → ∀ b ∈ d, a ≤ b :=
      fun hd b hb => (hlt b (hd hb)).le
    have hdisj : Disjoint B.powerset (B.powerset.image (insert a)) := by
      rw [Finset.disjoint_right]
      intro d hd hd2
      obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 hd
      exact haB (Finset.mem_powerset.1 hd2 (Finset.mem_insert_self _ _))
    have hinj : ∀ d ∈ B.powerset, ∀ e ∈ B.powerset,
        insert a d = insert a e → d = e := by
      intro d hd e he h
      have hd' := Finset.mem_powerset.1 hd
      have he' := Finset.mem_powerset.1 he
      have h1 : d = (insert a d).erase a :=
        (Finset.erase_insert (fun hc => haB (hd' hc))).symm
      rw [h1, h, Finset.erase_insert (fun hc => haB (he' hc))]
    have hLHS : ∑ d ∈ A.powerset, minVal f d
        = (∑ d ∈ B.powerset, minVal f d) + f a * 2 ^ B.card := by
      have h2 : ∑ x ∈ B.powerset, minVal f (insert a x) = f a * 2 ^ B.card := by
        rw [Finset.sum_congr rfl (fun d hd =>
          minVal_insert_of_le f (hle (Finset.mem_powerset.1 hd))),
          Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
        push_cast
        ring
      conv_lhs => rw [hAeq]
      rw [Finset.powerset_insert, Finset.sum_union hdisj, Finset.sum_image hinj, h2]
    have hfa : (A.filter (fun b => a < b)) = B := by
      ext b
      simp only [Finset.mem_filter, hB, Finset.mem_erase]
      constructor
      · rintro ⟨hb, hab⟩; exact ⟨Ne.symm (ne_of_lt hab), hb⟩
      · rintro ⟨hne, hb⟩; exact ⟨hb, hlt b (Finset.mem_erase.2 ⟨hne, hb⟩)⟩
    have hfx : ∀ x ∈ B, (A.filter (fun b => x < b)) = (B.filter (fun b => x < b)) := by
      intro x hx
      ext b
      simp only [Finset.mem_filter, hB, Finset.mem_erase]
      constructor
      · rintro ⟨hb, hxb⟩
        refine ⟨⟨?_, hb⟩, hxb⟩
        rintro rfl
        exact absurd (hlt x hx) (not_lt.2 hxb.le)
      · rintro ⟨⟨-, hb⟩, hxb⟩; exact ⟨hb, hxb⟩
    have hRHS : ∑ x ∈ A, f x * 2 ^ (A.filter (fun b => x < b)).card
        = (∑ x ∈ B, f x * 2 ^ (B.filter (fun b => x < b)).card) + f a * 2 ^ B.card := by
      conv_lhs => rw [hAeq]
      rw [Finset.sum_insert haB, add_comm]
      congr 1
      · refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [show (insert a B).filter (fun b => x < b) = A.filter (fun b => x < b) by
          rw [hAeq], hfx x hx]
      · rw [show (insert a B).filter (fun b => a < b) = A.filter (fun b => a < b) by
          rw [hAeq], hfa]
    rw [hLHS, hRHS, ih B hBss]

/-- The identity in the form `[UB, Eq 11]` uses it: `φ_r` is defined only on nonempty
subsets, and the empty set contributes nothing anyway. -/
theorem sum_powerset_minVal_nonempty (f : ι → ℝ) (A : Finset ι) :
    ∑ d ∈ A.powerset.filter (fun d => d.Nonempty), minVal f d
      = ∑ a ∈ A, f a * 2 ^ (A.filter (fun b => a < b)).card := by
  rw [← sum_powerset_minVal f A]
  refine (Finset.sum_subset (f := minVal f)
    (Finset.filter_subset (fun d => d.Nonempty) A.powerset) ?_)
  intro d hd hnd
  have hne : ¬ d.Nonempty := by
    intro hc
    exact hnd (Finset.mem_filter.2 ⟨hd, hc⟩)
  rw [Finset.not_nonempty_iff_eq_empty.1 hne, minVal_empty]

/-- The singleton subsets contribute exactly `Σ_{a ∈ A} f a`. -/
lemma sum_powerset_minVal_card_one (f : ι → ℝ) (A : Finset ι) :
    ∑ d ∈ A.powerset.filter (fun d => d.card = 1), minVal f d = ∑ a ∈ A, f a := by
  have himg : A.powerset.filter (fun d => d.card = 1) = A.image (fun a => ({a} : Finset ι)) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hsub, hcard⟩
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 hcard
      exact ⟨x, hsub (Finset.mem_singleton_self x), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Finset.singleton_subset_iff.2 hx, Finset.card_singleton x⟩
  rw [himg, Finset.sum_image (fun x _ y _ h => Finset.singleton_injective h)]
  exact Finset.sum_congr rfl (fun a _ => minVal_singleton f a)

/-- **`[UB, Eq 11]`.**  Summing `φ_r` over subsets of size `≥ 2` — the relations proper,
singletons being self-relations rather than relations — replaces the weight
`2 ^ #{b : a < b}` by `2 ^ #{b : a < b} - 1`.  Under the paper's sorting this is exactly
its `2 ^ (|Z(o)| - i) - 1`. -/
theorem sum_powerset_minVal_ge_two (f : ι → ℝ) (A : Finset ι) :
    ∑ d ∈ A.powerset.filter (fun d => 2 ≤ d.card), minVal f d
      = ∑ a ∈ A, f a * (2 ^ (A.filter (fun b => a < b)).card - 1) := by
  have hsplit : A.powerset.filter (fun d => d.Nonempty)
      = A.powerset.filter (fun d => 2 ≤ d.card)
        ∪ A.powerset.filter (fun d => d.card = 1) := by
    ext d
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hd, hne⟩
      have h1 : 1 ≤ d.card := Finset.card_pos.2 hne
      rcases Nat.lt_or_ge d.card 2 with h | h
      · exact Or.inr ⟨hd, by omega⟩
      · exact Or.inl ⟨hd, h⟩
    · rintro (⟨hd, h⟩ | ⟨hd, h⟩)
      · exact ⟨hd, Finset.card_pos.1 (by omega)⟩
      · exact ⟨hd, Finset.card_pos.1 (by omega)⟩
  have hdisj : Disjoint (A.powerset.filter (fun d => 2 ≤ d.card))
      (A.powerset.filter (fun d => d.card = 1)) := by
    rw [Finset.disjoint_left]
    intro d hd hd2
    have h1 := (Finset.mem_filter.1 hd).2
    have h2 := (Finset.mem_filter.1 hd2).2
    omega
  have key := sum_powerset_minVal_nonempty f A
  rw [hsplit, Finset.sum_union hdisj, sum_powerset_minVal_card_one] at key
  have : ∑ a ∈ A, f a * (2 ^ (A.filter (fun b => a < b)).card - 1)
      = (∑ a ∈ A, f a * 2 ^ (A.filter (fun b => a < b)).card) - ∑ a ∈ A, f a := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  rw [this, ← key]
  ring

/-! ## `[UB, Eq 13]`: the linear program, and its optimum

`[UB, S3 §4]` maximises the `[UB, Eq 11]` objective under a budget on the total per-unit
integration:

    max  Σ_i (φ_(i)/|z_(i)|) (2^(|𝒵(o)| - i) - 1)   s.t.  Σ_i φ_(i)/|z_(i)| ≤ S(o)

and solves it by enumerating the `|𝒵(o)| + 1` vertices of the feasible polytope, finding
the optimum at the vertex where every distinction carries the *same* ratio `S(o)/|𝒵(o)|`,
with value `S(o) (2^|𝒵(o)|/|𝒵(o)| (1 - 2^-|𝒵(o)|) - 1)`.

That value is `(S(o)/n)(2^n - 1 - n)` for `n = |𝒵(o)|`, and the bound is exactly
**Chebyshev's sum inequality**: the weights `2^(n-i) - 1` *decrease* in `i` while the
ratios `φ_(i)/|z_(i)|` *increase*, so the two antivary and the sum of their product is at
most `1/n` times the product of their sums.  We take that route rather than the vertex
enumeration -- it needs no case analysis and gives the same constant. -/

/-- `minVal` of the constant function `1` is the indicator of nonemptiness. -/
lemma minVal_one_of_ne_empty {d : Finset ι} (hd : d ≠ ∅) :
    minVal (fun _ => (1 : ℝ)) d = 1 := by
  rw [minVal, dif_pos (Finset.nonempty_iff_ne_empty.2 hd)]

/-- Every nonempty subset of `A` has a unique minimum, so the ranks `#{b ∈ A : a < b}`
run over `0, …, |A| - 1`, and the weights sum to `2^|A| - 1`.  This is the `f ≡ 1` case
of `sum_powerset_minVal`. -/
lemma sum_two_pow_rank (A : Finset ι) :
    ∑ a ∈ A, (2 : ℝ) ^ (A.filter (fun b => a < b)).card = 2 ^ A.card - 1 := by
  have key := sum_powerset_minVal (fun _ => (1 : ℝ)) A
  simp only [one_mul] at key
  rw [← key]
  have hmem : (∅ : Finset ι) ∈ A.powerset := Finset.empty_mem_powerset A
  rw [← Finset.add_sum_erase _ _ hmem, minVal_empty, zero_add,
    Finset.sum_congr rfl (fun d hd => minVal_one_of_ne_empty (Finset.ne_of_mem_erase hd)),
    Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_erase_of_mem hmem,
    Finset.card_powerset]
  have h1 : 1 ≤ 2 ^ A.card := Nat.one_le_two_pow
  push_cast [h1]
  ring

/-- The total weight appearing in `[UB, Eq 11]`. -/
lemma sum_weight (A : Finset ι) :
    ∑ a ∈ A, ((2 : ℝ) ^ (A.filter (fun b => a < b)).card - 1) = 2 ^ A.card - 1 - A.card := by
  rw [Finset.sum_sub_distrib, sum_two_pow_rank, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **`[UB, Eq 13]`, solved.**  If the per-unit integrations `f` increase along the order
(the paper's sorting of `𝒵(o)`), then the `[UB, Eq 11]` objective is at most `1/|A|` times
the product of the total integration and the total weight:

    |A| * Σ_{|d| ≥ 2} φ_r(d)  ≤  (Σ_a f a) * (2^|A| - 1 - |A|)

which is the paper's LP optimum `S(o) (2^n/n (1 - 2^-n) - 1)` with `n = |A| = |𝒵(o)|` and
`S(o) = Σ_a f a`.  Proved by Chebyshev's sum inequality rather than vertex enumeration. -/
theorem sum_powerset_minVal_ge_two_le (f : ι → ℝ) (A : Finset ι)
    (hmono : ∀ a ∈ A, ∀ b ∈ A, a < b → f a ≤ f b) :
    (A.card : ℝ) * ∑ d ∈ A.powerset.filter (fun d => 2 ≤ d.card), minVal f d
      ≤ (∑ a ∈ A, f a) * (2 ^ A.card - 1 - A.card) := by
  rw [sum_powerset_minVal_ge_two]
  have hanti : AntivaryOn f
      (fun a => (2 : ℝ) ^ (A.filter (fun b => a < b)).card - 1) (A : Set ι) := by
    intro i hi j hj hij
    simp only [Finset.mem_coe] at hi hj
    -- `hij` says rank i < rank j, and the rank is antitone, so `j < i`
    have hcard : (A.filter (fun b => i < b)).card < (A.filter (fun b => j < b)).card := by
      have h2 : (2 : ℝ) ^ (A.filter (fun b => i < b)).card
          < 2 ^ (A.filter (fun b => j < b)).card := by linarith
      exact_mod_cast (pow_lt_pow_iff_right₀ (by norm_num : (1:ℝ) < 2)).1 h2
    have hji : j < i := by
      rcases lt_trichotomy j i with h | h | h
      · exact h
      · exact absurd (h ▸ rfl : (A.filter (fun b => i < b)).card
          = (A.filter (fun b => j < b)).card) (Nat.ne_of_lt hcard)
      · exact absurd (Finset.card_le_card (fun b hb => by
          have := Finset.mem_filter.1 hb
          exact Finset.mem_filter.2 ⟨this.1, lt_trans h this.2⟩)) (not_le.2 hcard)
    exact hmono j hj i hi hji
  have cheb := hanti.card_mul_sum_le_sum_mul_sum
  rw [sum_weight] at cheb
  exact cheb

/-! ## `[UB, Eq 16]`: the growth bound

`[UB, §2.2, Step 3]` plugs two estimates into the `[UB, Eq 15]` bound
`Σ φ_d + Σ_o S(o) (2^|𝒵(o)|/|𝒵(o)| (1 - 2^-|𝒵(o)|) - 1)`:

* `|𝒵(o)| ≤ 2^N - 1` (a distinction set has at most `2^N - 1` nonempty mechanisms), and
* `S(o) ≤ (N/2) 2^N`, from `φ ≤ φ_e ≤ |M||z_e*| ≤ |M|N`, so `φ/|z*| ≤ |M|`, and
  `Σ_{|M|=1}^N |M| C(N,|M|) = (N/2)2^N`.

Together with `2N` values of `o` (`N` units, each in one of two states, as
`[UB, Eq 11]`'s outer sum "sums over all the units `o` in all their possible states")
and `[UB, Eq 6]`'s
`Σ φ_d ≤ (N²/2)2^N`, this gives the paper's numeric bound.  We isolate the *arithmetic*
step — everything past "plugging in the two estimates" — since that step alone is what
produces the `𝒪(N² 2^(2^N))` growth rate; it does not depend on how `|𝒵(o)|` or `S(o)`
were bounded. -/

/-- The `[UB, Eq 14]` bracket `2^n/n (1 - 2^-n) - 1` is nonnegative for every `n ≥ 1`
(it is `0` at `n = 1` and increasing after). -/
lemma eq14_bracket_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (2:ℝ) ^ n / (n:ℝ) * (1 - 1 / 2 ^ n) - 1 := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; norm_num
    · have hprev := ih hkpos
      have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hkpos
      have hkpow : (0:ℝ) < 2 ^ k := by positivity
      have hcast : ((k:ℝ) + 1) ≠ 0 := by positivity
      have goal_eq : (2:ℝ) ^ (k + 1) / (↑k + 1) * (1 - 1 / 2 ^ (k + 1)) - 1
          - ((2:ℝ) ^ k / k * (1 - 1 / 2 ^ k) - 1)
          = (2 ^ (k+1) - 1) / (k+1) - (2 ^ k - 1) / k := by
        push_cast
        field_simp
        ring
      have step : ((2:ℝ) ^ k - 1) / (k:ℝ) ≤ ((2:ℝ) ^ (k+1) - 1) / ((k:ℝ) + 1) := by
        rw [div_le_div_iff₀ (by exact_mod_cast hkpos) (by linarith)]
        have h2k : (2:ℝ) ≤ 2 ^ k := by
          calc (2:ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hkpos
        have hpow2 : (2:ℝ) ^ (k+1) = 2 ^ k * 2 := by ring
        nlinarith [hkpow]
      have hfin : 0 ≤ ((2:ℝ) ^ (k+1) - 1) / ((k:ℝ)+1) - ((2:ℝ) ^ k - 1) / (k:ℝ) := by linarith
      have hcast2 : ((k:ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast2] at goal_eq hfin
      linarith [goal_eq, hfin]

/-- The `[UB, Eq 14]` bracket taken one step further: `bracket(k+1) ≥ bracket(k)` for
`k ≥ 1`.  Isolated from the computation in `eq14_bracket_nonneg`, whose inductive step
already establishes exactly this. -/
lemma eq14_bracket_step {k : ℕ} (hk : 1 ≤ k) :
    (2:ℝ) ^ k / (k:ℝ) * (1 - 1 / 2 ^ k) - 1
      ≤ (2:ℝ) ^ (k+1) / ((k:ℝ)+1) * (1 - 1 / 2 ^ (k+1)) - 1 := by
  have hkpow : (0:ℝ) < 2 ^ k := by positivity
  have goal_eq : (2:ℝ) ^ (k + 1) / ((k:ℝ) + 1) * (1 - 1 / 2 ^ (k + 1)) - 1
      - ((2:ℝ) ^ k / k * (1 - 1 / 2 ^ k) - 1)
      = ((2:ℝ) ^ (k+1) - 1) / ((k:ℝ)+1) - ((2:ℝ) ^ k - 1) / (k:ℝ) := by
    have hcast : ((k:ℝ) + 1) ≠ 0 := by positivity
    have hk0 : (k:ℝ) ≠ 0 := by
      have : 1 ≤ k := hk
      positivity
    field_simp
    ring
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have step : ((2:ℝ) ^ k - 1) / (k:ℝ) ≤ ((2:ℝ) ^ (k+1) - 1) / ((k:ℝ) + 1) := by
    rw [div_le_div_iff₀ (by exact_mod_cast hk) (by linarith)]
    have h2k : (2:ℝ) ≤ 2 ^ k := by
      calc (2:ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
    have hpow2 : (2:ℝ) ^ (k+1) = 2 ^ k * 2 := by ring
    nlinarith [hkpow, hk1, mul_nonneg (le_of_lt hkpow) (by linarith : (0:ℝ) ≤ (k:ℝ) - 1)]
  linarith [goal_eq, step]

/-- **The `[UB, Eq 14]` bracket is monotone in `n`**, for `n ≥ 1`.  `[UB, §2.2]` remarks
in words that "the bound increases almost exponentially in `|𝒵(o)|`"; this is that
statement, by `Nat.le_induction` on `eq14_bracket_step`. -/
lemma eq14_bracket_mono {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (2:ℝ) ^ m / (m:ℝ) * (1 - 1 / 2 ^ m) - 1 ≤ (2:ℝ) ^ n / (n:ℝ) * (1 - 1 / 2 ^ n) - 1 := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_refl _
  | succ k hk ih =>
    have hcast2 : ((k:ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    have hstep := eq14_bracket_step (hm.trans hk)
    rw [hcast2] at hstep
    exact ih.trans hstep

/-- **`[UB, Eq 16]`, the arithmetic step.**  Every term of the `[UB, Eq 15]` sum is
bounded by the single worst case `B (2^n/n(1-2^-n) - 1)`: monotone in `S(o) ≤ B` because
the bracket is nonnegative (`eq14_bracket_nonneg`), and monotone in `|𝒵(o)| ≤ n` by
`eq14_bracket_mono` — exactly `[UB, §2.2]`'s remark that the bound "increases almost
exponentially" in `|𝒵(o)|`.  This gives the growth bound as a clean product over
`o.card` copies. -/
theorem sum_phiR_le {ι : Type*} (o : Finset ι) {D : ℝ}
    (Zo : ι → ℕ) (So : ι → ℝ) {n : ℕ} (hn : 1 ≤ n) {B : ℝ} (hB0 : 0 ≤ B)
    (hZ : ∀ x ∈ o, Zo x ≤ n) (hzero : ∀ x ∈ o, Zo x = 0 → So x = 0)
    (hS : ∀ x ∈ o, So x ≤ B) :
    D + ∑ x ∈ o, So x * (2 ^ (Zo x) / (Zo x : ℝ) * (1 - 1 / 2 ^ (Zo x)) - 1)
      ≤ D + (o.card : ℝ) * (B * (2 ^ n / (n : ℝ) * (1 - 1 / 2 ^ n) - 1)) := by
  have hmono_n : ∀ x ∈ o, So x * (2 ^ (Zo x) / (Zo x : ℝ) * (1 - 1 / 2 ^ (Zo x)) - 1)
      ≤ B * (2 ^ n / (n : ℝ) * (1 - 1 / 2 ^ n) - 1) := by
    intro x hx
    rcases Nat.eq_zero_or_pos (Zo x) with hz | hZ1
    · rw [hzero x hx hz, zero_mul]
      exact mul_nonneg hB0 (eq14_bracket_nonneg hn)
    calc So x * (2 ^ (Zo x) / (Zo x : ℝ) * (1 - 1 / 2 ^ (Zo x)) - 1)
        ≤ B * (2 ^ (Zo x) / (Zo x : ℝ) * (1 - 1 / 2 ^ (Zo x)) - 1) :=
          mul_le_mul_of_nonneg_right (hS x hx) (eq14_bracket_nonneg hZ1)
      _ ≤ B * (2 ^ n / (n : ℝ) * (1 - 1 / 2 ^ n) - 1) :=
          mul_le_mul_of_nonneg_left (eq14_bracket_mono hZ1 (hZ x hx)) hB0
  have h1 : ∑ x ∈ o, So x * (2 ^ (Zo x) / (Zo x : ℝ) * (1 - 1 / 2 ^ (Zo x)) - 1)
      ≤ ∑ _x ∈ o, B * (2 ^ n / (n : ℝ) * (1 - 1 / 2 ^ n) - 1) :=
    Finset.sum_le_sum hmono_n
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  linarith

/-- **`[UB, Eq 16]`**, instantiated at the paper's own numbers: `N` units each in `2`
states give `k = 2N` values of `o` (`"o is an arbitrary unit in a
arbitrary state"` [sic], and
`Σ_o` in `[UB, Eq 11]` "sums over all the units `o` in all their possible states"), with
`|𝒵(o)| ≤ n = 2^N - 1`, `S(o) ≤ B = (N/2)2^N`, `Σ φ_d ≤ D = (N²/2)2^N`.  This is exactly
the printed right-hand side of `[UB, Eq 16]`, and the growth rate `𝒪(N² 2^(2^N))` follows
since `2^n = 2^(2^N - 1)` dominates every polynomial factor. -/
theorem eq16_paper_numbers (N : ℕ) (hN : 0 < N) :
    (N : ℝ) ^ 2 / 2 * 2 ^ N
      + (2 * N : ℝ) * ((N / 2 : ℝ) * 2 ^ N * (2 ^ (2 ^ N - 1) / ((2 : ℝ) ^ N - 1)
        * (1 - 1 / 2 ^ (2 ^ N - 1)) - 1))
      = (N : ℝ) ^ 2 / 2 * 2 ^ N
        + (N : ℝ) ^ 2 * 2 ^ N * (2 ^ (2 ^ N - 1) / ((2 : ℝ) ^ N - 1)
          * (1 - 1 / 2 ^ (2 ^ N - 1)) - 1) := by
  ring

/-! ## `[UB, Eq 10]`: the distinctions through a unit-in-state -/

open scoped Classical in
/-- **`[UB, Eq 10]`**: `𝒵(o) = {(z, φ) : z = z*_c ∪ z*_e, ((z*_c, z*_e), φ) ∈ D,
o ∈ z*_c ∪ z*_e}` -- the sub-family of the distinction set whose purview-union contains
the unit-in-state `o`.  A `Distinction` already carries the tuple `((z*_c, z*_e), φ)` and
`Distinction.support` is `z*_c ∪ z*_e`, so the filter is the whole content of the
equation. -/
noncomputable def Zset {N : ℕ} (D : Finset (Distinction N)) (o : Fin N × Bool) :
    Finset (Distinction N) :=
  D.filter fun d => o ∈ d.support

lemma mem_Zset {N : ℕ} {D : Finset (Distinction N)} {o : Fin N × Bool}
    {d : Distinction N} : d ∈ Zset D o ↔ d ∈ D ∧ o ∈ d.support := by
  classical
  simp [Zset]

/-- **`[UB, Eq 11]` with genuine minima.**  `sum_powerset_minVal_ge_two` restated through
`minVal_eq_inf'`: when the order sorts `f` -- the paper's sorted indexing -- the sum of
the true minima `min_{a ∈ d} f a` over all subsets of size at least two is the
`2^(|𝒵(o)|-i) - 1` weighted sum. -/
theorem sum_powerset_inf'_ge_two (f : ι → ℝ) (A : Finset ι)
    (hmono : ∀ a ∈ A, ∀ b ∈ A, a < b → f a ≤ f b) :
    ∑ d ∈ A.powerset.filter (fun d => 2 ≤ d.card),
        (if hd : d.Nonempty then d.inf' hd f else 0)
      = ∑ a ∈ A, f a * (2 ^ (A.filter (fun b => a < b)).card - 1) := by
  rw [← sum_powerset_minVal_ge_two]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdP, hcard⟩ := Finset.mem_filter.1 hd
  have hne : d.Nonempty := Finset.card_pos.1 (by omega)
  have heq := minVal_eq_inf' f hne (fun a ha b hb hab =>
    hmono a (Finset.mem_powerset.1 hdP ha) b (Finset.mem_powerset.1 hdP hb) hab)
  rw [dif_pos hne, heq]

open scoped Classical in
/-- **The `[UB, Eq 11]` summation exchange, for the development's own `φ_r`.**  The
overlap factor `|⋂_{D ∈ d} supp D|` of `[UB, Eq 8]` counts units-in-state, so summing
`φ_r` over every subset of the distinction set **of size at least two** and
exchanging the order of summation
turns the total into a sum over units-in-state `o` of sums over subsets of `𝒵(o)`
(`Zset`), whose inner sums `sum_powerset_inf'_ge_two` then evaluates.  This is the step
`[UB]` quotes from `[IIT4, S3 Text]`. -/
theorem sum_relPhiOrZero_eq_sum_units {N : ℕ} (D : Finset (Distinction N)) :
    ∑ d ∈ D.powerset.filter (fun d => 2 ≤ d.card), relPhiOrZero d
      = ∑ o : Fin N × Bool,
          ∑ d ∈ (Zset D o).powerset.filter (fun d => 2 ≤ d.card),
            (if hd : d.Nonempty then d.inf' hd Distinction.phiPerUnit else 0) := by
  have h1 : ∀ d ∈ D.powerset.filter (fun d => 2 ≤ d.card),
      relPhiOrZero d = ∑ o : Fin N × Bool,
        (if o ∈ d.inf Distinction.support then
          (if hd : d.Nonempty then d.inf' hd Distinction.phiPerUnit else 0) else 0) := by
    intro d hd
    obtain ⟨-, hcard⟩ := Finset.mem_filter.1 hd
    have hne : d.Nonempty := Finset.card_pos.1 (by omega)
    simp only [dif_pos hne]
    rw [relPhiOrZero, dif_pos hne, relPhi, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [← Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨hdD, hcard⟩, hmem⟩
    refine ⟨fun x hx => ?_, hcard⟩
    rw [mem_Zset]
    exact ⟨hdD hx, mem_finset_inf.1 hmem x hx⟩
  · rintro ⟨hdZ, hcard⟩
    have hdD : d ⊆ D := fun x hx => (mem_Zset.1 (hdZ hx)).1
    exact ⟨⟨hdD, hcard⟩, mem_finset_inf.2 fun x hx => (mem_Zset.1 (hdZ hx)).2⟩

open scoped Classical in
/-- **`[UB, Eq 12]`**: "we can simplify the objective function by finding the maximum of
each term in the sum separately".  `sum_relPhiOrZero_eq_sum_units` supplies the exchange
as an *equality*, so bounding each unit-in-state's inner sum by any `B o` bounds the
relations proper.  This is the second of `[UB, Eq 12]`'s two maximised terms; its first
term, the self-relations, is `step2_self_relations_le` below. -/
theorem eq12_relations_le {N : ℕ} (D : Finset (Distinction N)) (B : Fin N × Bool → ℝ)
    (hB : ∀ o : Fin N × Bool,
      ∑ d ∈ (Zset D o).powerset.filter (fun d => 2 ≤ d.card),
        (if hd : d.Nonempty then d.inf' hd Distinction.phiPerUnit else 0) ≤ B o) :
    ∑ d ∈ D.powerset.filter (fun d => 2 ≤ d.card), relPhiOrZero d
      ≤ ∑ o : Fin N × Bool, B o := by
  rw [sum_relPhiOrZero_eq_sum_units]
  exact Finset.sum_le_sum fun o _ => hB o

/-- **`[UB, §2.2, Step 2]`**: "the first term is bounded by
`Σ_{d ⊆ D, |d| = 1} φ_r(d) ≤ Σ_{d ∈ D} φ_d`, because the integrated information of a
self-relation is less than its distinction integrated information".  Summed form of
`selfRelPhi_le_phi`. -/
theorem step2_self_relations_le {N : ℕ} (D : Finset (Distinction N)) :
    ∑ d ∈ D, selfRelPhi d ≤ ∑ d ∈ D, d.phi :=
  Finset.sum_le_sum fun d _ => selfRelPhi_le_phi d

/-- **`[UB, Eq 14]`, attainment.**  The Chebyshev bound of
`sum_powerset_minVal_ge_two_le` is the exact optimum of the `[UB, Eq 13]` program: the
constant profile -- every element carrying the same ratio, the paper's
`φ_(i)/|z_(i)| = S(o)/|𝒵(o)|`, its optimal vertex `x_1 = S(o)/|𝒵(o)|` -- attains it with
equality. -/
theorem eq14_attained (A : Finset ι) (c : ℝ) :
    ∑ d ∈ A.powerset.filter (fun d => 2 ≤ d.card), minVal (fun _ => c) d
      = c * (2 ^ A.card - 1 - A.card) := by
  rw [sum_powerset_minVal_ge_two, ← Finset.mul_sum, sum_weight]

/-- **The sorted indexing of `[UB, Eq 11]` always exists.**

`[UB, Eq 11]` posits a "sorted indexing of the elements in `𝒵(o)`, such that
`(z_(1), φ_(1))` has the smallest `φ/|z|` ratio", without constructing one.  It always
exists: order by the ratio, breaking ties by any well-order of the ambient type.  So the
`LinearOrder` parameter of `eq11_sum_over_units` below is a construction, not an assumption. -/
noncomputable def sortedBy {α : Type*} (f : α → ℝ) : LinearOrder α := by
  classical
  let r : α → α → Prop := fun a b => f a < f b ∨ (f a = f b ∧ WellOrderingRel a b)
  haveI htri : Std.Trichotomous r := trichotomous_def.mpr (by
    intro a b h1 h2
    have hab : ¬ (f a < f b) := fun h => h1 (Or.inl h)
    have hba : ¬ (f b < f a) := fun h => h2 (Or.inl h)
    have hfe : f a = f b := le_antisymm (not_lt.1 hba) (not_lt.1 hab)
    have hw1 : ¬ WellOrderingRel a b := fun h => h1 (Or.inr ⟨hfe, h⟩)
    have hw2 : ¬ WellOrderingRel b a := fun h => h2 (Or.inr ⟨hfe.symm, h⟩)
    rcases trichotomous_of WellOrderingRel a b with h | h | h
    · exact absurd h hw1
    · exact h
    · exact absurd h hw2)
  haveI hirr : Std.Irrefl r := by
    refine ⟨fun {a} ha => ?_⟩
    rcases ha with h | ⟨-, h⟩
    · exact lt_irrefl _ h
    · exact (irrefl_of WellOrderingRel a) h
  haveI htr : IsTrans α r := by
    refine ⟨fun a b c hab hbc => ?_⟩
    rcases hab with h1 | ⟨he1, hw1⟩ <;> rcases hbc with h2 | ⟨he2, hw2⟩
    · exact Or.inl (h1.trans h2)
    · exact Or.inl (he2 ▸ h1)
    · exact Or.inl (he1 ▸ h2)
    · exact Or.inr ⟨he1.trans he2, trans_of WellOrderingRel hw1 hw2⟩
  haveI : IsStrictOrder α r := {}
  haveI : IsStrictTotalOrder α r := {}
  exact linearOrderOfSTO r

/-- The order built by `sortedBy` does sort `f`, which is `eq11_sum_over_units`'s `hmono`. -/
lemma sortedBy_mono {α : Type*} (f : α → ℝ) {a b : α}
    (h : (sortedBy f).lt a b) : f a ≤ f b := by
  classical
  have h' : f a < f b ∨ (f a = f b ∧ WellOrderingRel a b) := h
  rcases h' with h1 | ⟨he, -⟩
  · exact h1.le
  · exact he.le

/-- **`[UB, Eq 11]`, end to end for the development's own `φ_r`.**

Composing `sum_relPhiOrZero_eq_sum_units` (the summation exchange) with
`sum_powerset_inf'_ge_two` (the weighted evaluation of each inner sum) gives the paper's
identity for the actual relation integrated information: summing `φ_r` over every subset
of the distinction set of size at least two equals, per unit-in-state `o`, the
`2^(|𝒵(o)|-i) - 1` weighted sum of the per-unit integrations `φ_d/|z*_c ∪ z*_e|`.

`hmono` is `[UB, Eq 11]`'s own hypothesis -- its "sorted indexing of the elements in
`𝒵(o)`, such that `(z_(1), φ_(1))` has the smallest `φ/|z|` ratio".  It is not an extra
assumption: `sortedBy` builds such an order for any `f`, and `eq11_sum_over_units'` below instantiates
this theorem at it. -/
theorem eq11_sum_over_units {N : ℕ} [LinearOrder (Distinction N)] (D : Finset (Distinction N))
    (hmono : ∀ o : Fin N × Bool, ∀ a ∈ Zset D o, ∀ b ∈ Zset D o,
      a < b → a.phiPerUnit ≤ b.phiPerUnit) :
    ∑ d ∈ D.powerset.filter (fun d => 2 ≤ d.card), relPhiOrZero d
      = ∑ o : Fin N × Bool, ∑ a ∈ Zset D o,
          a.phiPerUnit * (2 ^ ((Zset D o).filter (fun b => a < b)).card - 1) := by
  rw [sum_relPhiOrZero_eq_sum_units]
  exact Finset.sum_congr rfl fun o _ =>
    sum_powerset_inf'_ge_two Distinction.phiPerUnit (Zset D o) (hmono o)

/-- **`[UB, Eq 11]` with no hypotheses at all**, by instantiating `eq11_sum_over_units` at the order
`sortedBy` constructs.  The paper's sorted indexing is therefore a construction of this
development, not something it assumes. -/
theorem eq11_sum_over_units' {N : ℕ} (D : Finset (Distinction N)) :
    letI := sortedBy (Distinction.phiPerUnit (N := N))
    ∑ d ∈ D.powerset.filter (fun d => 2 ≤ d.card), relPhiOrZero d
      = ∑ o : Fin N × Bool, ∑ a ∈ Zset D o,
          a.phiPerUnit * (2 ^ ((Zset D o).filter (fun b => a < b)).card - 1) := by
  letI := sortedBy (Distinction.phiPerUnit (N := N))
  exact eq11_sum_over_units D fun _ a _ b _ hab => sortedBy_mono _ hab

/-- **`[UB, Eq 15]`**: plugging the `[UB, Eq 13]` optimum back into `[UB, Eq 12]`.

The total over *all* subsets of the distinction set splits into the self-relations
(`|d| = 1`, whose value is `[UB, Eq 9]`'s `selfRelPhi`, bounded by `Σ φ_d` through
`step2_self_relations_le` -- this is `[UB]`'s Step 2) and the relations proper (`|d| ≥ 2`, bounded per
unit-in-state by `eq12_relations_le`).  `B o` is the paper's
`S(o) (2^|𝒵(o)|/|𝒵(o)| (1 - 2^-|𝒵(o)|) - 1)`. -/
theorem eq15 {N : ℕ} (D : Finset (Distinction N)) (B : Fin N × Bool → ℝ)
    (hB : ∀ o : Fin N × Bool,
      ∑ d ∈ (Zset D o).powerset.filter (fun d => 2 ≤ d.card),
        (if hd : d.Nonempty then d.inf' hd Distinction.phiPerUnit else 0) ≤ B o) :
    ∑ d ∈ D, selfRelPhi d
        + ∑ d ∈ D.powerset.filter (fun d => 2 ≤ d.card), relPhiOrZero d
      ≤ (∑ d ∈ D, d.phi) + ∑ o : Fin N × Bool, B o :=
  add_le_add (step2_self_relations_le D) (eq12_relations_le D B hB)

/-- `[UB, Eq 14]`'s bracket in closed form. -/
lemma bracket_eq {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℝ) ^ n / (n : ℝ) * (1 - 1 / 2 ^ n) - 1 = ((2 : ℝ) ^ n - 1 - n) / n := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : 0 < n := hn
    positivity
  have h2 : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  field_simp

/-- The `[UB, Eq 13]` bound in the bracket form `[UB, Eq 14]` prints, for a nonempty
`A`; `chebyshev_bracket'` removes that hypothesis. -/
lemma chebyshev_bracket (f : ι → ℝ) (A : Finset ι) (hA : A.Nonempty)
    (hmono : ∀ a ∈ A, ∀ b ∈ A, a < b → f a ≤ f b) :
    ∑ d ∈ A.powerset.filter (fun d => 2 ≤ d.card), minVal f d
      ≤ (∑ a ∈ A, f a) * (2 ^ A.card / (A.card : ℝ) * (1 - 1 / 2 ^ A.card) - 1) := by
  have hcard : 1 ≤ A.card := Finset.card_pos.2 hA
  have hc : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hA
  rw [bracket_eq hcard, ← mul_div_assoc, le_div_iff₀ hc]
  have h := sum_powerset_minVal_ge_two_le f A hmono
  linarith

/-- **`[UB, Eq 13]` with no hypothesis on `A`.**  At `A = ∅` both sides are `0`: the
filtered powerset is `{∅}` on which `minVal` is `0`, and the right-hand side carries the
empty sum `∑ a ∈ ∅, f a` as a factor.  `chebyshev_bracket` needs `A.Nonempty` only to
divide by `|A|`, so the hypothesis was an artifact of the proof and not of the
statement. -/
lemma chebyshev_bracket' (f : ι → ℝ) (A : Finset ι)
    (hmono : ∀ a ∈ A, ∀ b ∈ A, a < b → f a ≤ f b) :
    ∑ d ∈ A.powerset.filter (fun d => 2 ≤ d.card), minVal f d
      ≤ (∑ a ∈ A, f a) * (2 ^ A.card / (A.card : ℝ) * (1 - 1 / 2 ^ A.card) - 1) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp [Finset.filter_singleton]
  · exact chebyshev_bracket f A hA hmono

/-- **`[UB, Eq 16]`**, as an inequality.

`[UB, §2.2, Step 3]` instantiates `[UB, Eq 15]` with `|𝒵(o)| ≤ 2^N - 1`,
`S(o) ≤ (N/2)2^N`, and `2N` values of `o` (`N` units, each in one of two states), giving
the printed right-hand side

    D + N² 2^N (2^(2^N-1)/(2^N-1) (1 - 2^-(2^N-1)) - 1),

with `D = Σ φ_d ≤ (N²/2)2^N` supplied by `[UB, Eq 6]`.  Unlike `eq16_paper_numbers`,
which only reconciles the printed constants, this is an inequality.

Its left side is `[UB, Eq 15]`'s right side, and `hZ`, `hS` are `[UB, Step 3]`'s estimates
taken as hypotheses: their derivations from the transition probabilities
(`φ ≤ φ_e ≤ |M||z*_e|`, hence `φ/|z*_c ∪ z*_e| ≤ |M|`, hence
`S(o) ≤ Σ_{|M|=1}^N |M| C(N,|M|) = (N/2)2^N`) are not needed at this level of generality.
They are formalized below, as `card_distinctions_le` and `sum_phiPerUnit_Zset_le`, and
`eq16_distinctions` discharges both.  Taking them here as named hypotheses, `eq16_chain` below chains `eq15` and this bound, and `eq16_chain'`
puts the result in the single-sum form `Σ_{d ⊆ D} φ_r(d) ≤ (N²/2)2^N + N²2^N(…)`. -/
theorem eq16 {ι : Type*} (o : Finset ι) (Zo : ι → ℕ) (So : ι → ℝ) {D : ℝ}
    {N : ℕ} (hN : 1 ≤ N) (hcard : o.card = 2 * N)
    (hZ : ∀ x ∈ o, Zo x ≤ 2 ^ N - 1) (hzero : ∀ x ∈ o, Zo x = 0 → So x = 0)
    (hS : ∀ x ∈ o, So x ≤ (N / 2 : ℝ) * 2 ^ N) :
    D + ∑ x ∈ o, So x * (2 ^ (Zo x) / (Zo x : ℝ) * (1 - 1 / 2 ^ (Zo x)) - 1)
      ≤ D + (N : ℝ) ^ 2 * 2 ^ N
          * (2 ^ (2 ^ N - 1) / ((2 : ℝ) ^ N - 1) * (1 - 1 / 2 ^ (2 ^ N - 1)) - 1) := by
  have h2N : 2 ≤ 2 ^ N := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  have hn : 1 ≤ 2 ^ N - 1 := by omega
  have hB0 : (0 : ℝ) ≤ (N / 2 : ℝ) * 2 ^ N := by positivity
  have key := sum_phiR_le (D := D) o Zo So hn hB0 hZ hzero hS
  -- the cast `((2^N - 1 : ℕ) : ℝ) = (2:ℝ)^N - 1`
  have hcast : (((2 ^ N - 1 : ℕ)) : ℝ) = (2 : ℝ) ^ N - 1 := by
    have h1 : (1 : ℕ) ≤ 2 ^ N := by omega
    push_cast [h1]
    ring
  rw [hcast] at key
  refine key.trans (le_of_eq ?_)
  rw [hcard]
  push_cast
  ring

/-- `φ_r` on *every* subset of the distinction set: `[UB, Eq 8]` at degree `≥ 2` and
`[UB, Eq 9]`'s self-relation at degree `1`.  `[IIT4, Eq 49]` admits both, so the sums
`[UB, Eq 11]` and `[UB, Eq 15]` write as `Σ_{d ⊆ D}` range over this. -/
noncomputable def phiR {N : ℕ} (d : Finset (Distinction N)) : ℝ :=
  if 2 ≤ d.card then relPhiOrZero d else ∑ D ∈ d, selfRelPhi D

/-- The splitting that `[UB, Eq 11]` performs on its left-hand side: degree `1` gives the
self-relations, degree `≥ 2` the relations proper. -/
lemma sum_phiR_split {N : ℕ} (D : Finset (Distinction N)) :
    ∑ d ∈ D.powerset, phiR d
      = ∑ d ∈ D, selfRelPhi d
        + ∑ d ∈ D.powerset.filter (fun d => 2 ≤ d.card), relPhiOrZero d := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not D.powerset (fun d => 2 ≤ d.card) phiR,
    add_comm]
  congr 1
  · -- the degree ≤ 1 part is the sum of the self-relations
    have himg : D.powerset.filter (fun d => ¬ 2 ≤ d.card)
        = insert ∅ (D.image fun a => ({a} : Finset (Distinction N))) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_image,
        not_le]
      constructor
      · rintro ⟨hsub, hlt⟩
        interval_cases h : d.card
        · exact Or.inl (Finset.card_eq_zero.1 h)
        · obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 h
          exact Or.inr ⟨x, hsub (Finset.mem_singleton_self x), rfl⟩
      · rintro (rfl | ⟨x, hx, rfl⟩)
        · exact ⟨Finset.empty_subset _, by simp⟩
        · exact ⟨Finset.singleton_subset_iff.2 hx, by simp⟩
    have hnotmem : (∅ : Finset (Distinction N))
        ∉ D.image fun a => ({a} : Finset (Distinction N)) := by
      simp only [Finset.mem_image, not_exists]
      intro a
      simp only [not_and]
      intro _
      exact fun h => absurd h (Finset.singleton_ne_empty a)
    rw [himg, Finset.sum_insert hnotmem,
      Finset.sum_image (fun x _ y _ h => Finset.singleton_injective h)]
    simp [phiR]
  · exact Finset.sum_congr rfl fun d hd => by
      rw [phiR, if_pos (Finset.mem_filter.1 hd).2]

/-- **`[UB, Eqs 15, 16] chained`**: a single bound on the development's own `φ_r`.

Composing `eq15` (the split into self-relations and relations proper) with `eq16` (the
`[UB, §2.2, Step 3]` arithmetic), instantiated at the actual `𝒵(o)` and per-unit
integrations, gives the printed right-hand side of `[UB, Eq 16]` as a bound on
the two summands of `Σ_{d ⊆ D} φ_r(d)`; `eq16_chain'` recombines them via
`sum_phiR_split`.  `[UB, Step 3]`'s two estimates enter as the
named hypotheses `hZcard` and `hSo`, and `[UB, Eq 6]` as `hD`.  Nothing else is assumed:
an earlier version also required every `𝒵(o)` to be nonempty, which is a strong condition
on the distinction set and was an artifact of dividing by `|𝒵(o)|`; `chebyshev_bracket'`
and the `Zo x = 0` case of `sum_phiR_le` remove it. -/
theorem eq16_chain {N : ℕ} [LinearOrder (Distinction N)] (D : Finset (Distinction N))
    (hN : 1 ≤ N)
    (hmono : ∀ o : Fin N × Bool, ∀ a ∈ Zset D o, ∀ b ∈ Zset D o,
      a < b → a.phiPerUnit ≤ b.phiPerUnit)
    (hZcard : ∀ o : Fin N × Bool, (Zset D o).card ≤ 2 ^ N - 1)
    (hSo : ∀ o : Fin N × Bool,
      ∑ a ∈ Zset D o, a.phiPerUnit ≤ (N / 2 : ℝ) * 2 ^ N)
    (hD : ∑ d ∈ D, d.phi ≤ (N : ℝ) ^ 2 / 2 * 2 ^ N) :
    ∑ d ∈ D, selfRelPhi d
        + ∑ d ∈ D.powerset.filter (fun d => 2 ≤ d.card), relPhiOrZero d
      ≤ (N : ℝ) ^ 2 / 2 * 2 ^ N
          + (N : ℝ) ^ 2 * 2 ^ N
            * (2 ^ (2 ^ N - 1) / ((2 : ℝ) ^ N - 1) * (1 - 1 / 2 ^ (2 ^ N - 1)) - 1) := by
  classical
  set Zo : Fin N × Bool → ℕ := fun o => (Zset D o).card with hZo
  set So : Fin N × Bool → ℝ := fun o => ∑ a ∈ Zset D o, a.phiPerUnit with hSodef
  set B : Fin N × Bool → ℝ :=
    fun o => So o * (2 ^ (Zo o) / (Zo o : ℝ) * (1 - 1 / 2 ^ (Zo o)) - 1) with hB
  -- each unit-in-state's inner sum is bounded by the Chebyshev optimum
  have hBound : ∀ o : Fin N × Bool,
      ∑ d ∈ (Zset D o).powerset.filter (fun d => 2 ≤ d.card),
        (if hd : d.Nonempty then d.inf' hd Distinction.phiPerUnit else 0) ≤ B o := by
    intro o
    have hconv : ∑ d ∈ (Zset D o).powerset.filter (fun d => 2 ≤ d.card),
        (if hd : d.Nonempty then d.inf' hd Distinction.phiPerUnit else 0)
        = ∑ d ∈ (Zset D o).powerset.filter (fun d => 2 ≤ d.card),
            minVal Distinction.phiPerUnit d := by
      refine Finset.sum_congr rfl fun d hd => ?_
      obtain ⟨hdP, hcard⟩ := Finset.mem_filter.1 hd
      have hne : d.Nonempty := Finset.card_pos.1 (by omega)
      rw [dif_pos hne, minVal_eq_inf' _ hne (fun a ha b hb hab =>
        hmono o a (Finset.mem_powerset.1 hdP ha) b (Finset.mem_powerset.1 hdP hb) hab)]
    rw [hconv]
    exact chebyshev_bracket' Distinction.phiPerUnit (Zset D o) (hmono o)
  refine (eq15 D B hBound).trans ?_
  have hstep := eq16 (Finset.univ : Finset (Fin N × Bool)) Zo So
    (D := ∑ d ∈ D, d.phi) hN
    (by simp [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm])
    (fun o _ => hZcard o)
    (fun o _ ho => by
      have : Zset D o = ∅ := Finset.card_eq_zero.1 ho
      simp [hSodef, this])
    (fun o _ => hSo o)
  simp only [hB]
  refine hstep.trans ?_
  linarith [hD]

/-- **`[UB, Eq 16]` for `Σ_{d ⊆ D} φ_r(d)`, with no hypothesis about the order.**
`sortedBy` supplies `eq16_chain`'s ordering hypothesis, and `sum_phiR_split` puts the
left-hand side in the paper's own form. -/
theorem eq16_chain' {N : ℕ} (D : Finset (Distinction N)) (hN : 1 ≤ N)
    (hZcard : ∀ o : Fin N × Bool, (Zset D o).card ≤ 2 ^ N - 1)
    (hSo : ∀ o : Fin N × Bool, ∑ a ∈ Zset D o, a.phiPerUnit ≤ (N / 2 : ℝ) * 2 ^ N)
    (hD : ∑ d ∈ D, d.phi ≤ (N : ℝ) ^ 2 / 2 * 2 ^ N) :
    ∑ d ∈ D.powerset, phiR d
      ≤ (N : ℝ) ^ 2 / 2 * 2 ^ N
          + (N : ℝ) ^ 2 * 2 ^ N
            * (2 ^ (2 ^ N - 1) / ((2 : ℝ) ^ N - 1) * (1 - 1 / 2 ^ (2 ^ N - 1)) - 1) := by
  letI := sortedBy (Distinction.phiPerUnit (N := N))
  rw [sum_phiR_split]
  exact eq16_chain D hN (fun _ _ _ _ _ h => sortedBy_mono _ h) hZcard hSo hD

/-- `[UB, §2.2, Step 3]`'s `S(o)` estimate, restricted from the whole distinction set to
the distinctions that specify one unit-in-state. -/
lemma sum_phiPerUnit_Zset_le {N : ℕ} (T : UnitTPM N) (u s : State N)
    (σ : Selector T Finset.univ u s) (o : Fin N × Bool) :
    ∑ a ∈ Zset (distinctions T Finset.univ u s σ) o, a.phiPerUnit
      ≤ (N / 2 : ℝ) * 2 ^ N := by
  classical
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
    (fun a _ _ => a.phiPerUnit_nonneg)) (sum_phiPerUnit_le T u s σ)
  rw [Zset]
  exact Finset.filter_subset _ _

/-- **`[UB, Eq 16]` instantiated at the development's own distinction set.**

`eq16_chain'` is stated for an arbitrary `D : Finset (Distinction N)`; this is the same
bound for the `D` that `[IIT4, Eq 48]` actually produces.  All three of its substantive
hypotheses are discharged rather than assumed: `hD` is `PhiDistinctions_le`, `[UB, Eq 6]`
for the true distinction sum; `hZcard` is `card_distinctions_le`, since a distinction
mechanism is a nonempty subset of the substrate; and `hSo` is `sum_phiPerUnit_Zset_le`,
which derives `[UB, §2.2, Step 3]`'s estimate on `S(o)` from `[UB, Theorem 1]` and
`sum_card_powerset_real` instead of assuming it.  The only hypothesis left is `1 ≤ N`. -/
theorem eq16_distinctions {N : ℕ} (T : UnitTPM N) (u s : State N)
    (σ : Selector T Finset.univ u s) (hN : 1 ≤ N) :
    ∑ d ∈ (distinctions T Finset.univ u s σ).powerset, phiR d
      ≤ (N : ℝ) ^ 2 / 2 * 2 ^ N
          + (N : ℝ) ^ 2 * 2 ^ N
            * (2 ^ (2 ^ N - 1) / ((2 : ℝ) ^ N - 1) * (1 - 1 / 2 ^ (2 ^ N - 1)) - 1) := by
  classical
  refine eq16_chain' _ hN (fun o => ?_) (sum_phiPerUnit_Zset_le T u s σ) ?_
  · calc (Zset (distinctions T Finset.univ u s σ) o).card
        ≤ (distinctions T Finset.univ u s σ).card := by
          rw [Zset]; exact Finset.card_filter_le _ _
    _ ≤ 2 ^ N - 1 := card_distinctions_le T u s σ
  · rw [sum_distinctions_phi]
    exact PhiDistinctions_le T u s

/-- **A bound on `Φ` itself.**

`[UB]` bounds the two halves of `[IIT4, Eq 59]` separately -- `[UB, Eq 6]` the distinction
sum and `[UB, Eq 16]` the relation sum -- and never adds them.  This does.  `[IIT4, Eq 56]`
keeps only the subsets of `D` of size at least two with `φ_r > 0`, and `[UB, Eq 9]` only
the distinctions with a self-relation, so both sums in `Φ` are over *subsets* of what
`eq16_chain'` sums over, and every summand is nonnegative.

Nothing is assumed beyond `1 ≤ N`: every hypothesis of `eq16_chain'` is discharged, as in
`eq16_distinctions`. -/
theorem PhiOf_le {N : ℕ} (T : UnitTPM N) (u s : State N)
    (σ : Selector T Finset.univ u s) (hN : 1 ≤ N) :
    PhiOf T Finset.univ u s σ
      ≤ (N : ℝ) ^ 2 / 2 * 2 ^ N
        + ((N : ℝ) ^ 2 / 2 * 2 ^ N
            + (N : ℝ) ^ 2 * 2 ^ N
              * (2 ^ (2 ^ N - 1) / ((2 : ℝ) ^ N - 1) * (1 - 1 / 2 ^ (2 ^ N - 1)) - 1)) := by
  classical
  set D := distinctions T Finset.univ u s σ with hD
  -- the distinction half, by [UB, Eq 6]
  have h1 : (∑ d ∈ D, d.phi) ≤ (N : ℝ) ^ 2 / 2 * 2 ^ N := by
    rw [hD, sum_distinctions_phi]
    exact PhiDistinctions_le T u s
  -- the relation half sits inside the sum eq16_chain' bounds
  have hrel : ∑ d ∈ relationSets T Finset.univ u s σ, relPhiOrZero d
      ≤ ∑ d ∈ D.powerset.filter (fun d => 2 ≤ d.card), relPhiOrZero d := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ => relPhiOrZero_nonneg d
    intro d hd
    obtain ⟨hdP, hspec⟩ := Finset.mem_filter.1 hd
    obtain ⟨-, hcard, -⟩ := hspec
    exact Finset.mem_filter.2 ⟨hdP, hcard⟩
  have hself : ∑ d ∈ selfRelationDistinctions T Finset.univ u s σ, selfRelPhi d
      ≤ ∑ d ∈ D, selfRelPhi d := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun d hd _ => ?_
    exact mul_nonneg (Nat.cast_nonneg _) d.phiPerUnit_nonneg
  have h2 : ∑ d ∈ D.powerset, phiR d
      ≤ (N : ℝ) ^ 2 / 2 * 2 ^ N
          + (N : ℝ) ^ 2 * 2 ^ N
            * (2 ^ (2 ^ N - 1) / ((2 : ℝ) ^ N - 1) * (1 - 1 / 2 ^ (2 ^ N - 1)) - 1) := by
    refine eq16_chain' D hN (fun o => ?_) (sum_phiPerUnit_Zset_le T u s σ) ?_
    · calc (Zset D o).card ≤ D.card := by rw [Zset]; exact Finset.card_filter_le _ _
        _ ≤ 2 ^ N - 1 := card_distinctions_le T u s σ
    · rw [hD, sum_distinctions_phi]
      exact PhiDistinctions_le T u s
  rw [sum_phiR_split] at h2
  rw [PhiOf]
  linarith [h1, hrel, hself, h2]

/-- **The same bound for the maximizing reading of the tie-break.**  Since the bound holds
for every admissible selector, it holds for `PhiMax`. -/
theorem PhiMax_le {N : ℕ} (T : UnitTPM N) (u s : State N) (hN : 1 ≤ N) :
    PhiMax T Finset.univ u s
      ≤ (N : ℝ) ^ 2 / 2 * 2 ^ N
        + ((N : ℝ) ^ 2 / 2 * 2 ^ N
            + (N : ℝ) ^ 2 * 2 ^ N
              * (2 ^ (2 ^ N - 1) / ((2 : ℝ) ^ N - 1) * (1 - 1 / 2 ^ (2 ^ N - 1)) - 1)) := by
  refine PhiMax_le_of_forall T Finset.univ u s ?_ fun σ => PhiOf_le T u s σ hN
  have h2 := PhiOf_nonneg T Finset.univ u s (Classical.arbitrary (Selector T Finset.univ u s))
  linarith [PhiOf_le T u s (Classical.arbitrary (Selector T Finset.univ u s)) hN]

end IIT
