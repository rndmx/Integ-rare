/-
Census, B1, W14 work package WP6 (part 2): near pairs of the core family (`near_pairs3`).
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §11, finding F3.

Route (elementary, no convex order): with `K = L ∪ K₀`, `|K₀| = n = d - ℓ`, pool `P` of size `p`,
* `#{K₀' : |K₀ ∩ K₀'| = i} ≤ C(n,i) C(p-n, n-i)` and the sequential-draw bound
  `C(p-n, c) ≤ C(p,n) (n/p)^i e^{-c²/p}` (`c = n - i`, falling factorials);
* tangent `-c² ≤ x0² - 2 x0 c` at `x0 = 0.0221 N`, Chernoff weight `e^{σ(c0 - c)}` (`σ = 1.08`,
  `3c ≤ 2d - 1` on near pairs), binomial theorem: the near sum is `≤ e^{x0²/p + σ c0} (n/p + e^{-σ-2x0/p})^n`;
* `n/p + e^{-σ-2x0/p} ≤ e^{-κ (d - N/1000)/n}` (`κ = 0.88`) uniformly in `ℓ ≤ N/1000`, `p ≥ N/4 - ℓ`;
* exponent `0.0019615 + 0.024 - 0.88·0.032333 = -0.0024918 < -1/420`.
No `sorry`.
-/
import IIT.Census.B1CntCovFam

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### Falling factorials and the sequential-draw bound -/

lemma descF_ratio (a b k : ℕ) (hab : a ≤ b) :
    (a.descFactorial k : ℝ) * (b : ℝ) ^ k ≤ (b.descFactorial k : ℝ) * (a : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul]
    have hs : ((a - k : ℕ) : ℝ) * b ≤ ((b - k : ℕ) : ℝ) * a := by
      rcases le_or_gt k a with hka | hka
      · rw [Nat.cast_sub hka, Nat.cast_sub (hka.trans hab)]
        have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      · rw [Nat.sub_eq_zero_of_le hka.le, Nat.cast_zero, zero_mul]; positivity
    have h1 : (0 : ℝ) ≤ (a.descFactorial k : ℝ) * (b : ℝ) ^ k := by positivity
    calc ((a - k : ℕ) : ℝ) * (a.descFactorial k : ℝ) * (b : ℝ) ^ (k + 1)
        = (((a - k : ℕ) : ℝ) * b) * ((a.descFactorial k : ℝ) * (b : ℝ) ^ k) := by ring
      _ ≤ (((b - k : ℕ) : ℝ) * a) * ((b.descFactorial k : ℝ) * (a : ℝ) ^ k) :=
          mul_le_mul hs ih h1 (by positivity)
      _ = ((b - k : ℕ) : ℝ) * (b.descFactorial k : ℝ) * (a : ℝ) ^ (k + 1) := by ring

lemma descF_add (p i c : ℕ) :
    p.descFactorial (i + c) = p.descFactorial i * (p - i).descFactorial c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [← add_assoc, Nat.descFactorial_succ, ih, Nat.descFactorial_succ, Nat.sub_sub]
    ring

/-- `C(p-n, c) p^i (p-i)^c ≤ C(p, n) n^i (p-n)^c` for `i + c = n ≤ p`. -/
lemma hyp_core (p d' i c : ℕ) (hic : i + c = d') (hd : d' ≤ p) :
    ((p - d').choose c : ℝ) * (p : ℝ) ^ i * ((p - i : ℕ) : ℝ) ^ c ≤
      (p.choose d' : ℝ) * (d' : ℝ) ^ i * ((p - d' : ℕ) : ℝ) ^ c := by
  have hA : ((p - d').descFactorial c : ℝ) = c.factorial * ((p - d').choose c : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose _ _
  have hB : (p.descFactorial i : ℝ) * ((p - i).descFactorial c : ℝ) =
      d'.factorial * (p.choose d' : ℝ) := by
    rw [← hic]
    exact_mod_cast (descF_add p i c).symm.trans (Nat.descFactorial_eq_factorial_mul_choose _ _)
  have hC : (d'.factorial : ℝ) = (d'.descFactorial i : ℝ) * c.factorial := by
    have h := Nat.factorial_mul_descFactorial (show i ≤ d' by omega)
    have hc : d' - i = c := by omega
    rw [hc] at h
    rw [← h]; push_cast; ring
  have hD := descF_ratio d' p i hd
  have hE := descF_ratio (p - d') (p - i) c (by omega)
  have hf : (0 : ℝ) < d'.factorial := by exact_mod_cast Nat.factorial_pos _
  refine le_of_mul_le_mul_right ?_ hf
  calc ((p - d').choose c : ℝ) * (p : ℝ) ^ i * ((p - i : ℕ) : ℝ) ^ c * d'.factorial
      = (c.factorial * ((p - d').choose c : ℝ)) * ((p - i : ℕ) : ℝ) ^ c *
          ((d'.descFactorial i : ℝ) * (p : ℝ) ^ i) := by rw [hC]; ring
    _ = ((p - d').descFactorial c : ℝ) * ((p - i : ℕ) : ℝ) ^ c *
          ((d'.descFactorial i : ℝ) * (p : ℝ) ^ i) := by rw [hA]
    _ ≤ ((p - i).descFactorial c : ℝ) * ((p - d' : ℕ) : ℝ) ^ c *
          ((p.descFactorial i : ℝ) * (d' : ℝ) ^ i) :=
        mul_le_mul hE hD (by positivity) (by positivity)
    _ = (p.descFactorial i : ℝ) * ((p - i).descFactorial c : ℝ) * (d' : ℝ) ^ i *
          ((p - d' : ℕ) : ℝ) ^ c := by ring
    _ = (p.choose d' : ℝ) * (d' : ℝ) ^ i * ((p - d' : ℕ) : ℝ) ^ c * d'.factorial := by
        rw [hB]; ring

/-- **Sequential-draw bound** `C(p-n, c) ≤ C(p, n) (n/p)^i e^{-c²/p}` (`i + c = n ≤ p`). -/
lemma hyp_term (p d' i c : ℕ) (hic : i + c = d') (hd : d' ≤ p) (hp : 0 < p) :
    ((p - d').choose c : ℝ) ≤
      (p.choose d' : ℝ) * ((d' : ℝ) / p) ^ i * Real.exp (-((c : ℝ) ^ 2 / p)) := by
  have hcore := hyp_core p d' i c hic hd
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hpi : ((p - i : ℕ) : ℝ) = p - i := Nat.cast_sub (by omega)
  have hpd : ((p - d' : ℕ) : ℝ) = p - i - c := by
    rw [Nat.cast_sub hd, ← hic]; push_cast; ring
  have hlin : ((p - d' : ℕ) : ℝ) ≤ ((p - i : ℕ) : ℝ) * Real.exp (-((c : ℝ) / p)) := by
    have h1 := Real.add_one_le_exp (-((c : ℝ) / p))
    have hpi0 : (0 : ℝ) ≤ (p : ℝ) - i := by rw [← hpi]; positivity
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have h3 : ((p : ℝ) - i) * ((c : ℝ) / p) ≤ c := by
      rw [mul_div_assoc', div_le_iff₀ hpr]; nlinarith
    rw [hpd, hpi]
    nlinarith [mul_le_mul_of_nonneg_left h1 hpi0]
  have hpow : ((p - d' : ℕ) : ℝ) ^ c ≤ ((p - i : ℕ) : ℝ) ^ c * Real.exp (-((c : ℝ) ^ 2 / p)) := by
    calc ((p - d' : ℕ) : ℝ) ^ c ≤ (((p - i : ℕ) : ℝ) * Real.exp (-((c : ℝ) / p))) ^ c :=
          pow_le_pow_left₀ (by positivity) hlin c
      _ = _ := by
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 2
          ring
  have hpos : (0 : ℝ) < ((p - i : ℕ) : ℝ) ^ c * (p : ℝ) ^ i := by
    rcases Nat.eq_zero_or_pos c with hc | hc
    · rw [hc, pow_zero, one_mul]; positivity
    · have : 0 < p - i := by omega
      positivity
  have hdp : ((d' : ℝ) / p) ^ i * (p : ℝ) ^ i = (d' : ℝ) ^ i := by
    rw [div_pow, div_mul_cancel₀ _ (by positivity)]
  refine le_of_mul_le_mul_right ?_ hpos
  calc ((p - d').choose c : ℝ) * (((p - i : ℕ) : ℝ) ^ c * (p : ℝ) ^ i)
      = ((p - d').choose c : ℝ) * (p : ℝ) ^ i * ((p - i : ℕ) : ℝ) ^ c := by ring
    _ ≤ (p.choose d' : ℝ) * (d' : ℝ) ^ i * ((p - d' : ℕ) : ℝ) ^ c := hcore
    _ ≤ (p.choose d' : ℝ) * (d' : ℝ) ^ i *
          (((p - i : ℕ) : ℝ) ^ c * Real.exp (-((c : ℝ) ^ 2 / p))) := by gcongr
    _ = (p.choose d' : ℝ) * (((d' : ℝ) / p) ^ i * (p : ℝ) ^ i) *
          (((p - i : ℕ) : ℝ) ^ c * Real.exp (-((c : ℝ) ^ 2 / p))) := by rw [hdp]
    _ = _ := by ring

/-! ### Counting by overlap -/

lemma count_inter (P K₀ : Finset (Fin N)) (hK₀ : K₀ ⊆ P) (d' i : ℕ) :
    ((P.powersetCard d').filter fun K₀' => (K₀ ∩ K₀').card = i).card ≤
      K₀.card.choose i * (P.card - K₀.card).choose (d' - i) := by
  have hmaps : Set.MapsTo (fun K₀' => (K₀ ∩ K₀', K₀' \ K₀))
      ↑((P.powersetCard d').filter fun K₀' => (K₀ ∩ K₀').card = i)
      ↑(K₀.powersetCard i ×ˢ (P \ K₀).powersetCard (d' - i)) := by
    intro K₀' h
    simp only [mem_coe, mem_filter, mem_powersetCard] at h
    simp only [mem_coe, mem_product, mem_powersetCard]
    refine ⟨⟨inter_subset_left, h.2⟩, sdiff_subset_sdiff h.1.1 subset_rfl, ?_⟩
    rw [card_sdiff, h.1.2, h.2]
  have hinj : Set.InjOn (fun K₀' => (K₀ ∩ K₀', K₀' \ K₀))
      ↑((P.powersetCard d').filter fun K₀' => (K₀ ∩ K₀').card = i) := by
    intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    have ea : a = (K₀ ∩ a) ∪ (a \ K₀) := by ext; simp only [mem_union, mem_inter, Finset.mem_sdiff]; tauto
    have eb : b = (K₀ ∩ b) ∪ (b \ K₀) := by ext; simp only [mem_union, mem_inter, Finset.mem_sdiff]; tauto
    rw [ea, eb, hab.1, hab.2]
  refine (card_le_card_of_injOn _ hmaps hinj).trans ?_
  rw [card_product, card_powersetCard, card_powersetCard, card_sdiff_of_subset hK₀]

/-- The near pairs of a core family, counted by the overlap of the free parts. -/
theorem near_count_le (P L K : Finset (Fin N)) (d : ℕ)
    (hK : K ∈ ((P ∪ L).powersetCard d).filter fun K => L ⊆ K) :
    (((((P ∪ L).powersetCard d).filter fun K' => L ⊆ K').filter
        fun K' => d < 3 * (K ∩ K').card).card : ℝ) ≤
      ∑ i ∈ (range (d - L.card + 1)).filter (fun i => d < 3 * (L.card + i)),
        ((d - L.card).choose i : ℝ) * ((P.card - (d - L.card)).choose (d - L.card - i) : ℝ) := by
  set ℓ := L.card with hℓ
  rw [mem_filter, mem_powersetCard] at hK
  set K₀ := K \ L with hK₀
  have hK₀P : K₀ ⊆ P := sdiff_le_iff.2 (le_of_le_of_eq hK.1.1 (union_comm P L))
  have hK₀c : K₀.card = d - ℓ := by rw [hK₀, card_sdiff_of_subset hK.2, hK.1.2]
  have hcnt : ∀ K' ∈ ((P ∪ L).powersetCard d).filter (fun K' => L ⊆ K'),
      K' \ L ∈ P.powersetCard (d - ℓ) ∧ (K ∩ K').card = ℓ + (K₀ ∩ (K' \ L)).card := by
    intro K' hK'
    rw [mem_filter, mem_powersetCard] at hK'
    refine ⟨?_, ?_⟩
    · rw [mem_powersetCard]
      exact ⟨sdiff_le_iff.2 (le_of_le_of_eq hK'.1.1 (union_comm P L)),
        by rw [card_sdiff_of_subset hK'.2, hK'.1.2]⟩
    · have e : K₀ ∩ (K' \ L) = (K ∩ K') \ L := by
        ext; simp only [hK₀, mem_inter, Finset.mem_sdiff]; tauto
      have hsub : L ⊆ K ∩ K' := subset_inter hK.2 hK'.2
      rw [e, card_sdiff_of_subset hsub]
      have := card_le_card hsub
      omega
  set G := (P.powersetCard (d - ℓ)).filter fun K₀' => d < 3 * (ℓ + (K₀ ∩ K₀').card) with hG
  have h1 : ((((P ∪ L).powersetCard d).filter fun K' => L ⊆ K').filter
        fun K' => d < 3 * (K ∩ K').card).card ≤ G.card := by
    refine card_le_card_of_injOn (fun K' => K' \ L) ?_ ?_
    · intro K' hK'
      rw [mem_coe, mem_filter] at hK'
      obtain ⟨hm, he⟩ := hcnt K' hK'.1
      rw [mem_coe, hG, mem_filter]
      exact ⟨hm, by rw [← he]; exact hK'.2⟩
    · intro a ha b hb hab
      rw [mem_coe, mem_filter, mem_filter] at ha hb
      have ea : a = (a \ L) ∪ L := (sdiff_union_of_subset ha.1.2).symm
      have eb : b = (b \ L) ∪ L := (sdiff_union_of_subset hb.1.2).symm
      have hab' : a \ L = b \ L := hab
      rw [ea, eb, hab']
  have h2 : G ⊆ ((range (d - ℓ + 1)).filter (fun i => d < 3 * (ℓ + i))).biUnion
      (fun i => (P.powersetCard (d - ℓ)).filter fun K₀' => (K₀ ∩ K₀').card = i) := by
    intro K₀' hGm
    rw [hG, mem_filter] at hGm
    rw [mem_biUnion]
    refine ⟨(K₀ ∩ K₀').card, ?_, mem_filter.2 ⟨hGm.1, rfl⟩⟩
    rw [mem_filter, mem_range]
    refine ⟨?_, hGm.2⟩
    have := card_le_card (inter_subset_left : K₀ ∩ K₀' ⊆ K₀)
    omega
  have h3 : G.card ≤ ∑ i ∈ (range (d - ℓ + 1)).filter (fun i => d < 3 * (ℓ + i)),
      (d - ℓ).choose i * (P.card - (d - ℓ)).choose (d - ℓ - i) := by
    refine (card_le_card h2).trans (card_biUnion_le.trans (sum_le_sum fun i _ => ?_))
    have := count_inter P K₀ hK₀P (d - ℓ) i
    rw [hK₀c] at this
    exact this
  have h4 := h1.trans h3
  exact_mod_cast h4

/-! ### The analytic bound -/

lemma exp_sub_le_of_nonpos {u v : ℝ} (hu : u ≤ 0) (hvu : v ≤ u) :
    Real.exp u - Real.exp v ≤ u - v := by
  have h1 : Real.exp v = Real.exp u * Real.exp (v - u) := by rw [← Real.exp_add]; ring_nf
  have h2 := Real.add_one_le_exp (v - u)
  have h3 : Real.exp u ≤ 1 := Real.exp_le_one_iff.2 hu
  have h4 : 0 < Real.exp u := Real.exp_pos u
  rw [h1]
  nlinarith [mul_le_mul_of_nonneg_left h2 h4.le, mul_le_mul_of_nonneg_right h3 (sub_nonneg.2 hvu)]

lemma near_exp1 : Real.exp (-(1571 / 1250 : ℝ)) ≤ 2846 / 10000 := by
  have h := Real.sum_le_exp_of_nonneg (x := (1571 / 1250 : ℝ)) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  norm_num
  linarith

lemma near_exp2 : (4146 / 10000 : ℝ) ≤ Real.exp (-(22 / 25 : ℝ)) := by
  have h := Real.exp_bound' (x := (22 / 25 : ℝ)) (by norm_num) (by norm_num) (n := 10) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  norm_num
  linarith

set_option maxHeartbeats 1000000 in
/-- **The tangent–Chernoff bound** for the near sum (all real parameters). -/
lemma near_sum_bound (Nr dr ℓr pr : ℝ) (n : ℕ) (hN : 100000 ≤ Nr) (hd1 : Nr / 30 ≤ dr)
    (hd2 : dr ≤ Nr / 30 + 1) (hℓ0 : 0 ≤ ℓr) (hℓ : ℓr ≤ Nr / 1000) (hn : (n : ℝ) = dr - ℓr)
    (hp : Nr / 4 - ℓr ≤ pr) (S : Finset ℕ) (hS : S ⊆ range (n + 1))
    (hSc : ∀ i ∈ S, 3 * ((n : ℝ) - i) ≤ 2 * dr - 1) :
    ∑ i ∈ S, (n.choose i : ℝ) * ((n : ℝ) / pr) ^ i *
        Real.exp (-(((n - i : ℕ) : ℝ) ^ 2 / pr)) ≤ Real.exp (-(Nr / 420)) := by
  set ξ : ℝ := 221 / 10000 with hξ
  set σ : ℝ := 27 / 25 with hσ
  set κ : ℝ := 22 / 25 with hκ
  set x0 : ℝ := ξ * Nr with hx0
  set p0 : ℝ := Nr / 4 - ℓr with hp0
  have hp0pos : 249 / 1000 * Nr ≤ p0 := by rw [hp0]; linarith
  have hprpos : 0 < pr := by linarith
  have hp0pos' : 0 < p0 := by linarith
  have hnpos : 0 < (n : ℝ) := by rw [hn]; linarith
  set a : ℝ := (n : ℝ) / pr with ha
  set β : ℝ := Real.exp (-σ - 2 * x0 / pr) with hβ
  set E0 : ℝ := Real.exp (x0 ^ 2 / pr + σ * ((2 * dr - 1) / 3)) with hE0
  -- Step 1: termwise
  have hterm : ∀ i ∈ S, (n.choose i : ℝ) * a ^ i * Real.exp (-(((n - i : ℕ) : ℝ) ^ 2 / pr)) ≤
      E0 * ((n.choose i : ℝ) * a ^ i * β ^ (n - i)) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.1 (mem_range.1 (hS hi))
    have hc := hSc i hi
    obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ((n - i : ℕ) : ℝ) := ⟨_, rfl⟩
    have hcr : c = (n : ℝ) - i := by rw [hcdef]; exact Nat.cast_sub hin
    rw [← hcdef]
    have hexp : Real.exp (-(c ^ 2 / pr)) ≤ E0 * β ^ (n - i) := by
      rw [hE0, hβ, ← Real.exp_nat_mul, ← Real.exp_add, ← hcdef]
      apply Real.exp_le_exp.2
      have hsq : -(c ^ 2 / pr) ≤ x0 ^ 2 / pr - 2 * x0 * c / pr := by
        rw [show x0 ^ 2 / pr - 2 * x0 * c / pr = (x0 ^ 2 - 2 * x0 * c) / pr by ring,
          neg_div', div_le_div_iff_of_pos_right hprpos]
        nlinarith [sq_nonneg (x0 - c)]
      have hsc : 0 ≤ σ * ((2 * dr - 1) / 3 - c) := by
        rw [hcr]; apply mul_nonneg (by rw [hσ]; norm_num); linarith
      have e : x0 ^ 2 / pr + σ * ((2 * dr - 1) / 3) + c * (-σ - 2 * x0 / pr) =
          (x0 ^ 2 / pr - 2 * x0 * c / pr) + σ * ((2 * dr - 1) / 3 - c) := by ring
      rw [e]; linarith
    calc (n.choose i : ℝ) * a ^ i * Real.exp (-(c ^ 2 / pr))
        ≤ (n.choose i : ℝ) * a ^ i * (E0 * β ^ (n - i)) := by gcongr
      _ = _ := by ring
  -- Step 2: binomial theorem
  have hsum : ∑ i ∈ S, (n.choose i : ℝ) * a ^ i * Real.exp (-(((n - i : ℕ) : ℝ) ^ 2 / pr)) ≤
      E0 * (a + β) ^ n := by
    calc _ ≤ ∑ i ∈ S, E0 * ((n.choose i : ℝ) * a ^ i * β ^ (n - i)) := sum_le_sum hterm
      _ ≤ ∑ i ∈ range (n + 1), E0 * ((n.choose i : ℝ) * a ^ i * β ^ (n - i)) :=
          sum_le_sum_of_subset_of_nonneg hS fun i _ _ => by positivity
      _ = E0 * (a + β) ^ n := by
          rw [← mul_sum, add_pow]
          congr 1
          exact sum_congr rfl fun i _ => by ring
  -- Step 3: `a + β ≤ e^{-κ (d - N/1000)/n}`
  have hx0n : x0 ≤ n := by rw [hn, hx0, hξ]; linarith
  have hsig : Real.exp (-σ) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have := Real.add_one_le_exp σ
    rw [hσ] at this ⊢; norm_num; linarith
  have h3a : a + β ≤ (n : ℝ) / p0 + Real.exp (-σ) * Real.exp (-(2 * x0 / p0)) := by
    have hlip := exp_sub_le_of_nonpos (u := -(2 * x0 / pr)) (v := -(2 * x0 / p0))
      (by rw [neg_nonpos]; positivity)
      (by rw [neg_le_neg_iff]; exact div_le_div_of_nonneg_left (by positivity) hp0pos' hp)
    have hβ' : β = Real.exp (-σ) * Real.exp (-(2 * x0 / pr)) := by
      rw [hβ, ← Real.exp_add]; ring_nf
    have hinv : 0 ≤ 1 / p0 - 1 / pr := by
      rw [sub_nonneg]; exact one_div_le_one_div_of_le hp0pos' hp
    have hes : 0 ≤ Real.exp (-σ) := (Real.exp_pos _).le
    have k1 : Real.exp (-σ) * (Real.exp (-(2 * x0 / pr)) - Real.exp (-(2 * x0 / p0))) ≤
        1 / 2 * (2 * x0 * (1 / p0 - 1 / pr)) := by
      have e : -(2 * x0 / pr) - -(2 * x0 / p0) = 2 * x0 * (1 / p0 - 1 / pr) := by ring
      rw [e] at hlip
      have hx0' : 0 ≤ 2 * x0 * (1 / p0 - 1 / pr) := by
        apply mul_nonneg (by rw [hx0, hξ]; linarith) hinv
      calc Real.exp (-σ) * (Real.exp (-(2 * x0 / pr)) - Real.exp (-(2 * x0 / p0)))
          ≤ Real.exp (-σ) * (2 * x0 * (1 / p0 - 1 / pr)) := by gcongr
        _ ≤ 1 / 2 * (2 * x0 * (1 / p0 - 1 / pr)) := by gcongr
    have k2 : 1 / 2 * (2 * x0 * (1 / p0 - 1 / pr)) ≤ (n : ℝ) * (1 / p0 - 1 / pr) := by
      have := mul_le_mul_of_nonneg_right hx0n hinv; linarith
    have e2 : (n : ℝ) * (1 / p0 - 1 / pr) = (n : ℝ) / p0 - a := by rw [ha]; ring
    rw [hβ']
    linarith
  have h3b : Real.exp (-σ) * Real.exp (-(2 * x0 / p0)) ≤ 2846 / 10000 := by
    rw [← Real.exp_add]
    refine le_trans (Real.exp_le_exp.2 ?_) near_exp1
    have : 8 * ξ ≤ 2 * x0 / p0 := by
      rw [le_div_iff₀ hp0pos', hx0, hp0]; rw [hξ]; nlinarith
    rw [hσ] at *; rw [hξ] at this; linarith
  set ℓm : ℝ := Nr / 1000 with hℓm
  set t : ℝ := ℓm - ℓr with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  set B : ℝ := Nr / 4 - ℓm with hB
  have hBpos : 249 / 1000 * Nr ≤ B := by rw [hB, hℓm]; linarith
  have h3c : (n : ℝ) / p0 ≤ 13 / 100 + 3648 / 10000 * t / n := by
    have hBp : B ≤ p0 := by rw [hB, hp0]; linarith
    have hB0 : 0 < B := by linarith
    have s1 : (n : ℝ) / p0 ≤ (n : ℝ) / B := div_le_div_of_nonneg_left hnpos.le hB0 hBp
    have s2 : (n : ℝ) / B = (dr - ℓm) / B + t / B := by rw [hn, ht]; ring
    have s3 : (dr - ℓm) / B ≤ 13 / 100 := by
      rw [div_le_iff₀ hB0, hB, hℓm]; linarith
    have s4 : t / B ≤ 3648 / 10000 * t / n := by
      rw [mul_div_assoc]
      have : 1 / B ≤ 3648 / 10000 / n := by
        rw [div_le_div_iff₀ hB0 hnpos]; rw [hn]; linarith
      calc t / B = t * (1 / B) := by ring
        _ ≤ t * (3648 / 10000 / n) := by gcongr
        _ = 3648 / 10000 * (t / n) := by ring
    linarith
  have hk := near_exp2
  have h3d : a + β ≤ Real.exp (-(κ * (dr - ℓm) / n)) := by
    have e : -(κ * (dr - ℓm) / n) = -κ + κ * t / n := by
      rw [ht]; field_simp; rw [hn]; ring
    rw [e, Real.exp_add]
    have h5 := Real.add_one_le_exp (κ * t / n)
    have htn : 0 ≤ t / n := div_nonneg ht0 hnpos.le
    have h6 : Real.exp (-κ) * (1 + κ * t / n) ≤ Real.exp (-κ) * Real.exp (κ * t / n) := by
      gcongr; linarith
    have h7 : 4146 / 10000 + 3648 / 10000 * t / n ≤ Real.exp (-κ) * (1 + κ * t / n) := by
      rw [hκ]
      have e1 : 3648 / 10000 * t / n = 3648 / 10000 * (t / n) := by ring
      have e2 : Real.exp (-(22 / 25)) * (1 + 22 / 25 * t / n) =
          Real.exp (-(22 / 25)) + Real.exp (-(22 / 25)) * (22 / 25) * (t / n) := by ring
      rw [e1, e2]
      nlinarith
    linarith
  -- Step 4
  have h4 : (a + β) ^ n ≤ Real.exp (-(κ * (dr - ℓm))) := by
    have hab0 : 0 ≤ a + β := by positivity
    calc (a + β) ^ n ≤ Real.exp (-(κ * (dr - ℓm) / n)) ^ n := pow_le_pow_left₀ hab0 h3d n
      _ = Real.exp (-(κ * (dr - ℓm))) := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
  have hx2 : x0 ^ 2 / pr ≤ ξ ^ 2 * Nr / (249 / 1000) := by
    rw [div_le_div_iff₀ hprpos (by norm_num), hx0]
    have : 249 / 1000 * Nr ≤ pr := by linarith
    have hN0 : 0 ≤ Nr := by linarith
    have h := mul_le_mul_of_nonneg_left this (mul_nonneg (sq_nonneg ξ) hN0)
    calc (ξ * Nr) ^ 2 * (249 / 1000) = ξ ^ 2 * Nr * (249 / 1000 * Nr) := by ring
      _ ≤ ξ ^ 2 * Nr * pr := h
  calc _ ≤ E0 * (a + β) ^ n := hsum
    _ ≤ E0 * Real.exp (-(κ * (dr - ℓm))) := by gcongr
    _ = Real.exp (x0 ^ 2 / pr + σ * ((2 * dr - 1) / 3) + -(κ * (dr - ℓm))) := by
        rw [hE0, ← Real.exp_add]
    _ ≤ Real.exp (-(Nr / 420)) := by
        apply Real.exp_le_exp.2
        rw [hσ, hκ, hℓm]
        rw [hξ] at hx2
        linarith

/-- **Near pairs** (W9 5.7, W13-effect G2, F3): in a core family with core `L` (`1000|L| ≤ N`) and
pool `P` (`N ≤ 4(|P| + |L|)`), at most a fraction `e^{-N/420}` of the members are near a given one. -/
theorem near_pairs3 : ∀ᶠ N in atTop, ∀ (P L : Finset (Fin N)), Disjoint P L →
    N ≤ 4 * (P.card + L.card) → 1000 * L.card ≤ N →
    ∀ K ∈ ((P ∪ L).powersetCard (dX N)).filter (fun K => L ⊆ K),
      (((((P ∪ L).powersetCard (dX N)).filter fun K' => L ⊆ K').filter
          fun K' => dX N < 3 * (K ∩ K').card).card : ℝ) ≤
        ((((P ∪ L).powersetCard (dX N)).filter fun K' => L ⊆ K').card : ℝ) *
          Real.exp (-((N : ℝ) / 420)) := by
  filter_upwards [eventually_ge_atTop 100000] with N hN P L hPL hN4 hL K hK
  set d := dX N with hd
  have hdN : d = (N + 29) / 30 := rfl
  set ℓ := L.card with hℓ
  have hℓd : ℓ ≤ d := by omega
  set n := d - ℓ with hn
  have hcnt := near_count_le P L K d hK
  -- `n ≤ |P|`, `0 < |P|`
  have hK' := hK
  rw [mem_filter, mem_powersetCard] at hK'
  have hK₀P : K \ L ⊆ P := sdiff_le_iff.2 (le_of_le_of_eq hK'.1.1 (union_comm P L))
  have hnP : n ≤ P.card := by
    have := card_le_card hK₀P
    rw [card_sdiff_of_subset hK'.2, hK'.1.2] at this
    exact this
  have hP0 : 0 < P.card := by omega
  rw [card_core_fam P L hPL d hℓd]
  set S := (range (n + 1)).filter (fun i => d < 3 * (ℓ + i)) with hS
  have hterm : ∀ i ∈ S, (n.choose i : ℝ) * ((P.card - n).choose (n - i) : ℝ) ≤
      (P.card.choose n : ℝ) * ((n.choose i : ℝ) * ((n : ℝ) / P.card) ^ i *
        Real.exp (-(((n - i : ℕ) : ℝ) ^ 2 / P.card))) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.1 (mem_range.1 (mem_filter.1 hi).1)
    have h := hyp_term P.card n i (n - i) (by omega) hnP hP0
    calc (n.choose i : ℝ) * ((P.card - n).choose (n - i) : ℝ)
        ≤ (n.choose i : ℝ) * ((P.card.choose n : ℝ) * ((n : ℝ) / P.card) ^ i *
            Real.exp (-(((n - i : ℕ) : ℝ) ^ 2 / P.card))) := by gcongr
      _ = _ := by ring
  have hNr : (100000 : ℝ) ≤ N := by exact_mod_cast hN
  have hd1 : (N : ℝ) / 30 ≤ d := by
    have : N ≤ 30 * d := by omega
    have : (N : ℝ) ≤ 30 * d := by exact_mod_cast this
    linarith
  have hd2 : (d : ℝ) ≤ N / 30 + 1 := by
    have : 30 * d ≤ N + 30 := by omega
    have : (30 : ℝ) * d ≤ N + 30 := by exact_mod_cast this
    linarith
  have hℓr : (ℓ : ℝ) ≤ N / 1000 := by
    have : (1000 : ℝ) * ℓ ≤ N := by exact_mod_cast hL
    linarith
  have hnr : (n : ℝ) = d - ℓ := Nat.cast_sub hℓd
  have hpr : (N : ℝ) / 4 - ℓ ≤ P.card := by
    have : (N : ℝ) ≤ 4 * (P.card + ℓ) := by exact_mod_cast hN4
    linarith
  have hSsub : S ⊆ range (n + 1) := filter_subset _ _
  have hSc : ∀ i ∈ S, 3 * ((n : ℝ) - i) ≤ 2 * d - 1 := by
    intro i hi
    have h3 := (mem_filter.1 hi).2
    have : d + 1 ≤ 3 * (ℓ + i) := h3
    have : ((d : ℝ) + 1) ≤ 3 * (ℓ + i) := by exact_mod_cast this
    rw [hnr]; linarith
  have hbound := near_sum_bound N d ℓ P.card n hNr hd1 hd2 (Nat.cast_nonneg _) hℓr hnr hpr S
    hSsub hSc
  have hC0 : (0 : ℝ) ≤ P.card.choose n := Nat.cast_nonneg _
  calc _ ≤ ∑ i ∈ S, (n.choose i : ℝ) * ((P.card - n).choose (n - i) : ℝ) := hcnt
    _ ≤ ∑ i ∈ S, (P.card.choose n : ℝ) * ((n.choose i : ℝ) * ((n : ℝ) / P.card) ^ i *
          Real.exp (-(((n - i : ℕ) : ℝ) ^ 2 / P.card))) := sum_le_sum hterm
    _ = (P.card.choose n : ℝ) * ∑ i ∈ S, (n.choose i : ℝ) * ((n : ℝ) / P.card) ^ i *
          Real.exp (-(((n - i : ℕ) : ℝ) ^ 2 / P.card)) := by rw [mul_sum]
    _ ≤ (P.card.choose n : ℝ) * Real.exp (-((N : ℝ) / 420)) := by gcongr

end Census
end IIT

#print axioms IIT.Census.near_pairs3
