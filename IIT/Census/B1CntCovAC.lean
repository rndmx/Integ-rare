/-
Census, B1, W14 work package WP6 (part 5): anti-concentration of the atoms of `Y_K` (W9 Lemma COV',
"GC gives P(|Φ_c - θ_c| ≤ ρ*) ≤ …").  Each atom is affine in the fresh entries of one subcube in one
column (the block `E`), with slope `1/|Q|`; conditioning on the other entries (`replE`), the law of
the block sum is that of `∑ (U_l - 1/2)` (`EntrySumLawStmt`), and `gc_interval` bounds the window.
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §11.  No `sorry`.
-/
import IIT.Census.B1CntCovRows
import IIT.Census.B1CntTool3

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### A generic window bound -/

/-- A signed centred entry, as in `EntrySumLawStmt`. -/
noncomputable def sgnT (ε : State N × Fin N → Bool) (w : Param N) (e : State N × Fin N) : ℝ :=
  if ε e then clamp01 (w e.1 e.2) - 1 / 2 else 1 / 2 - clamp01 (w e.1 e.2)

/-- **Window bound for a statistic affine in a block of entries.** -/
theorem ac_atom (hGC : GCStmt) (hESL : EntrySumLawStmt) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (E : Finset (State N × Fin N)) (ε : State N × Fin N → Bool)
      (α : ℝ) (L R : Param N → ℝ) (c η V0 n0 : ℝ),
      0 < α → 0 < η → 0 < V0 → V0 ≤ α * Real.sqrt ((E.card : ℝ) / 12) → 0 < n0 →
      n0 ≤ E.card → Measurable L →
      (∀ w ξ, R (replE E w ξ) = R w) → (∀ w, L w = α * ∑ e ∈ E, sgnT ε w e + R w) →
      cubeM N {w | |L w - c| ≤ η} ≤
        ENNReal.ofReal (4 * η / V0 + 2 * C * n0 ^ (-(1 / 8 : ℝ))) := by
  obtain ⟨C, hC, hgc⟩ := gc_interval hGC
  refine ⟨C, hC, fun N E ε α L R c η V0 n0 hα hη hV0 hV hn0 hnE hLm hR hL => ?_⟩
  have hnr : (0 : ℝ) < E.card := lt_of_lt_of_le hn0 hnE
  have hn : 0 < E.card := by exact_mod_cast hnr
  set σn := Real.sqrt ((E.card : ℝ) / 12) with hσn
  have hσ : 0 < σn := Real.sqrt_pos.2 (by positivity)
  have hY : MeasurableSet {w : Param N | |L w - c| ≤ η} :=
    measurableSet_le (continuous_abs.measurable.comp (hLm.sub_const c)) measurable_const
  have key := cubeM_inter_le_of_sectionE E (X := Set.univ) MeasurableSet.univ hY
    (fun _ _ _ => Iff.rfl) (p := ENNReal.ofReal (4 * η / V0 + 2 * C * n0 ^ (-(1 / 8 : ℝ)))) ?_
  · rw [Set.univ_inter, measure_univ, mul_one] at key; exact key
  intro w _
  set a := (c - η - R w) / α with ha
  set b := (c + η - R w) / α with hb
  have hab : a < b := by
    rw [ha, hb]; exact div_lt_div_of_pos_right (by linarith) hα
  have hset : {ξ : Param N | replE E w ξ ∈ {w : Param N | |L w - c| ≤ η}} =
      {ξ | ∑ e ∈ E, (if ε e then clamp01 (ξ e.1 e.2) - 1 / 2 else 1 / 2 - clamp01 (ξ e.1 e.2)) ∈
        Set.Icc a b} := by
    ext ξ
    simp only [Set.mem_ofPred_eq, Set.mem_Icc]
    rw [hL, hR]
    have hs : ∑ e ∈ E, sgnT ε (replE E w ξ) e = ∑ e ∈ E,
        (if ε e then clamp01 (ξ e.1 e.2) - 1 / 2 else 1 / 2 - clamp01 (ξ e.1 e.2)) := by
      refine sum_congr rfl fun e he => ?_
      have : replE E w ξ e.1 e.2 = ξ e.1 e.2 := by simp [replE, he]
      simp only [sgnT, this]
    rw [hs]
    rw [abs_le, ha, hb, le_div_iff₀ hα, div_le_iff₀ hα]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  rw [hset, hESL N E ε _ measurableSet_Icc]
  have hsub : {u : Fin E.card → ℝ | ∑ l, (u l - 1 / 2) ∈ Set.Icc a b} ⊆
      {u | (2 * a - b) / σn * σn < ∑ l, (u l - 1 / 2) ∧ ∑ l, (u l - 1 / 2) ≤ b / σn * σn} := by
    intro u hu
    simp only [Set.mem_ofPred_eq, Set.mem_Icc] at hu ⊢
    rw [div_mul_cancel₀ _ hσ.ne', div_mul_cancel₀ _ hσ.ne']
    constructor <;> linarith [hu.1, hu.2]
  have hle : (2 * a - b) / σn ≤ b / σn := div_le_div_of_nonneg_right (by linarith) hσ.le
  refine (measure_mono hsub).trans ((hgc E.card hn _ _ hle).trans (ENNReal.ofReal_le_ofReal ?_))
  have e1 : b / σn - (2 * a - b) / σn = 4 * η / (α * σn) := by
    rw [ha, hb]; field_simp; ring
  rw [e1]
  have hpi : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have h1 : 4 * η / (α * σn) / Real.sqrt (2 * Real.pi) ≤ 4 * η / V0 := by
    calc 4 * η / (α * σn) / Real.sqrt (2 * Real.pi) ≤ 4 * η / (α * σn) :=
          div_le_self (by positivity) hpi
      _ ≤ 4 * η / V0 := div_le_div_of_nonneg_left (by positivity) hV0 hV
  have h2 : (E.card : ℝ) ^ (-(1 / 8 : ℝ)) ≤ n0 ^ (-(1 / 8 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hn0 hnE (by norm_num)
  have h3 : 2 * C * (E.card : ℝ) ^ (-(1 / 8 : ℝ)) ≤ 2 * C * n0 ^ (-(1 / 8 : ℝ)) := by gcongr
  linarith

/-! ### The glued parameter and row sums -/

/-- The parameter glued from the sensitive data `f` and the entries of `w` outside `Sens`. -/
noncomputable def gluW (s r0 : State N) (f : sensRows s r0 → Fin N → ℝ) (w : Param N) : Param N :=
  glueRows (sensRows s r0) f (restrOut (sensRows s r0) w)

lemma gluW_of_mem {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (w : Param N) {r : State N}
    (hr : r ∈ sensRows s r0) : gluW s r0 f w r = b1Ext f r := by
  unfold gluW; exact glue_eq_b1Ext f _ r hr

lemma gluW_of_not_mem {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (w : Param N) {r : State N}
    (hr : r ∉ sensRows s r0) : gluW s r0 f w r = w r := by
  unfold gluW; rw [glueRows_of_not_mem _ f _ hr]; rfl

lemma measurable_gluW (s r0 : State N) (f : sensRows s r0 → Fin N → ℝ) :
    Measurable (gluW s r0 f) :=
  (measurable_glueRows_right _ f).comp (measurable_restrOut _)

/-- The orientation of column `i` (read on row `s`, which is sensitive). -/
noncomputable def epsF {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (e : State N × Fin N) : Bool :=
  decide (1 / 2 < clamp01 (b1Ext f s e.2))

/-- The row sum `∑_{r ∈ Q} (pTe u s r k - 1/2)`. -/
noncomputable def rsum (u : Param N) (s : State N) (Q : Finset (State N)) (k : Fin N) : ℝ :=
  ∑ r ∈ Q, (pTe u s r k - 1 / 2)

lemma effDevA_eq_rsum (u : Param N) (s : State N) (A : Finset (Fin N)) (t : State N) (k : Fin N) :
    effDevA u s A t k = rsum u s (agree A t) k / (agree A t).card := rfl

/-- The fresh block of a row set `Q` in column `k`. -/
noncomputable def fblk (s r0 : State N) (Q : Finset (State N)) (k : Fin N) : Finset (State N × Fin N) :=
  (Q.filter fun r => r ∉ sensRows s r0) ×ˢ {k}

lemma card_blk (s r0 : State N) (Q : Finset (State N)) (k : Fin N) :
    (fblk s r0 Q k).card = (Q.filter fun r => r ∉ sensRows s r0).card := by
  simp [fblk]

/-- The fixed part of a row sum is constant: `rsum (gluW w) Q - ∑_{fblk Q} sgnT w` does not depend on `w`. -/
lemma rsum_fixed {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (Q : Finset (State N)) (k : Fin N)
    (w w' : Param N) :
    rsum (gluW s r0 f w) s Q k - ∑ e ∈ fblk s r0 Q k, sgnT (epsF f) w e =
      rsum (gluW s r0 f w') s Q k - ∑ e ∈ fblk s r0 Q k, sgnT (epsF f) w' e := by
  have hs : ∀ w : Param N, gluW s r0 f w s = b1Ext f s :=
    fun w => gluW_of_mem f w (mem_sensRows_s s r0)
  have hfr : ∀ w : Param N, ∑ e ∈ fblk s r0 Q k, sgnT (epsF f) w e =
      ∑ r ∈ Q.filter (fun r => r ∉ sensRows s r0), (pTe (gluW s r0 f w) s r k - 1 / 2) := by
    intro w
    rw [fblk, sum_product]
    refine sum_congr rfl fun r hr => ?_
    rw [sum_singleton]
    have hr' : r ∉ sensRows s r0 := (mem_filter.1 hr).2
    unfold sgnT pTe epsF
    rw [hs w, gluW_of_not_mem f w hr']
    by_cases h : 1 / 2 < clamp01 (b1Ext f s k)
    · rw [if_pos (by simpa using h), if_pos h]
    · rw [if_neg (by simpa using h), if_neg h]; ring
  have hsens : ∀ w : Param N, ∑ r ∈ Q.filter (fun r => r ∈ sensRows s r0),
      (pTe (gluW s r0 f w) s r k - 1 / 2) =
      ∑ r ∈ Q.filter (fun r => r ∈ sensRows s r0), (pTe (b1Ext f) s r k - 1 / 2) := by
    intro w
    refine sum_congr rfl fun r hr => ?_
    unfold pTe
    rw [hs w, gluW_of_mem f w (mem_filter.1 hr).2]
  have hsplit : ∀ w : Param N, rsum (gluW s r0 f w) s Q k =
      ∑ r ∈ Q.filter (fun r => r ∈ sensRows s r0), (pTe (gluW s r0 f w) s r k - 1 / 2) +
      ∑ r ∈ Q.filter (fun r => r ∉ sensRows s r0), (pTe (gluW s r0 f w) s r k - 1 / 2) :=
    fun w => (sum_filter_add_sum_filter_not Q _ _).symm
  rw [hsplit w, hsplit w', hfr w, hfr w', hsens w, hsens w']
  ring

lemma gluW_repl_row {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (Q : Finset (State N))
    (k : Fin N) (w ξ : Param N) {r : State N} (hr : r ∉ Q.filter fun r => r ∉ sensRows s r0) :
    gluW s r0 f (replE (fblk s r0 Q k) w ξ) r = gluW s r0 f w r := by
  by_cases hF : r ∈ sensRows s r0
  · rw [gluW_of_mem f _ hF, gluW_of_mem f _ hF]
  · rw [gluW_of_not_mem f _ hF, gluW_of_not_mem f _ hF]
    funext i
    have : (r, i) ∉ fblk s r0 Q k := by
      simp only [fblk, mem_product]
      exact fun h => hr h.1
    simp [replE, this]

/-- A row sum over rows outside the block is unchanged by the replacement. -/
lemma rsum_repl {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (Q Q' : Finset (State N))
    (k k' : Fin N) (w ξ : Param N) (hQ : ∀ r ∈ Q', r ∉ Q) :
    rsum (gluW s r0 f (replE (fblk s r0 Q k) w ξ)) s Q' k' = rsum (gluW s r0 f w) s Q' k' := by
  have hs : gluW s r0 f (replE (fblk s r0 Q k) w ξ) s = gluW s r0 f w s := by
    rw [gluW_of_mem f _ (mem_sensRows_s s r0), gluW_of_mem f _ (mem_sensRows_s s r0)]
  unfold rsum
  refine sum_congr rfl fun r hr => ?_
  have hrow := gluW_repl_row f Q k w ξ (r := r) (fun h => hQ r hr (mem_filter.1 h).1)
  unfold pTe
  rw [hs, hrow]

/-! ### The three atom bounds -/

/-- `√(1/(12·2^M)) ≤ α √(n/12)` when `α = 2^{-a}`, `n ≥ 2^{a-1}`, `a + 1 ≤ M`. -/
lemma V0_le (a M : ℕ) (ha : 1 ≤ a) (haM : a + 1 ≤ M) (n : ℝ) (hn : (2 : ℝ) ^ (a - 1) ≤ n) :
    Real.sqrt (1 / (12 * 2 ^ M)) ≤ 1 / 2 ^ a * Real.sqrt (n / 12) := by
  have h2a : (0 : ℝ) < 2 ^ a := by positivity
  have hrw : 1 / (2 : ℝ) ^ a * Real.sqrt (n / 12) = Real.sqrt (n / (12 * (2 ^ a) ^ 2)) := by
    rw [show n / (12 * (2 ^ a) ^ 2) = (1 / (2 : ℝ) ^ a) ^ 2 * (n / 12) by field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hrw]
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e1 : ((2 : ℝ) ^ a) ^ 2 = 2 ^ (a - 1) * 2 ^ (a + 1) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  have e2 : (2 : ℝ) ^ (a + 1) ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) haM
  rw [e1]
  have hn0 : (0 : ℝ) ≤ n := le_trans (by positivity) hn
  have h1 : (2 : ℝ) ^ (a - 1) * 2 ^ (a + 1) ≤ n * 2 ^ (a + 1) :=
    mul_le_mul_of_nonneg_right hn (by positivity)
  have h2 : n * (2 : ℝ) ^ (a + 1) ≤ n * 2 ^ M := mul_le_mul_of_nonneg_left e2 hn0
  linarith

/-- Fresh rows of a row set: `|Q.filter fresh| ≥ |Q| - |Sens|`. -/
lemma card_fresh_ge (s r0 : State N) (Q : Finset (State N)) :
    Q.card ≤ (Q.filter fun r => r ∉ sensRows s r0).card + (sensRows s r0).card := by
  have h := card_filter_add_card_filter_not (s := Q) (fun r => r ∈ sensRows s r0)
  have h2 : (Q.filter fun r => r ∈ sensRows s r0).card ≤ (sensRows s r0).card :=
    card_le_card fun r hr => (mem_filter.1 hr).2
  omega

/-- The common per-atom bound. -/
noncomputable def patB (C : ℝ) (d M : ℕ) (η : ℝ) : ℝ :=
  4 * η / Real.sqrt (1 / (12 * 2 ^ M)) + 2 * C * ((2 : ℝ) ^ (d - 1)) ^ (-(1 / 8 : ℝ))

section Atoms

variable {C : ℝ}
  (hac : ∀ (N : ℕ) (E : Finset (State N × Fin N)) (ε : State N × Fin N → Bool)
      (α : ℝ) (L R : Param N → ℝ) (c η V0 n0 : ℝ),
      0 < α → 0 < η → 0 < V0 → V0 ≤ α * Real.sqrt ((E.card : ℝ) / 12) → 0 < n0 →
      n0 ≤ E.card → Measurable L →
      (∀ w ξ, R (replE E w ξ) = R w) → (∀ w, L w = α * ∑ e ∈ E, sgnT ε w e + R w) →
      cubeM N {w | |L w - c| ≤ η} ≤
        ENNReal.ofReal (4 * η / V0 + 2 * C * n0 ^ (-(1 / 8 : ℝ))))
include hac

omit hac in
lemma card_agree_C0 (s : State N) (K : Finset (Fin N)) :
    (agree (univ \ K) s).card = 2 ^ K.card := by
  rw [card_agree, card_sdiff_of_subset (subset_univ K), card_univ, Fintype.card_fin]
  congr 1
  have := card_le_univ K
  rw [Fintype.card_fin] at this
  omega

omit hac in
lemma card_agree_Cj (s : State N) (K : Finset (Fin N)) (j : Fin N) :
    (agree (univ \ K) (flipAt j s)).card = 2 ^ K.card := by
  rw [card_agree, card_sdiff_of_subset (subset_univ K), card_univ, Fintype.card_fin]
  congr 1
  have := card_le_univ K
  rw [Fintype.card_fin] at this
  omega

omit hac in
lemma two_pow_sub_le (d : ℕ) (hd : 1 ≤ d) (x : ℕ) (hx : 2 * x ≤ 2 ^ d) :
    (2 : ℝ) ^ (d - 1) ≤ ((2 ^ d - x : ℕ) : ℝ) := by
  have h1 : 2 ^ d = 2 * 2 ^ (d - 1) := by
    rw [← pow_succ']; congr 1; omega
  have : 2 ^ (d - 1) ≤ 2 ^ d - x := by omega
  exact_mod_cast this

/-- **`fK`-atoms.** -/
theorem atom_f (N : ℕ) (s r0 : State N) (f : sensRows s r0 → Fin N → ℝ) (K : Finset (Fin N))
    (hd : 1 ≤ K.card) (hF : 2 * (sensRows s r0).card ≤ 2 ^ K.card) (M : ℕ) (hM : K.card + 1 ≤ M)
    (k' : Fin N) (c η : ℝ) (hη : 0 < η) :
    cubeM N {w | |fK (gluW s r0 f w) s K k' - c| ≤ η} ≤ ENNReal.ofReal (patB C K.card M η) := by
  set Q := agree (univ \ K) s with hQ
  set E := fblk s r0 Q k' with hE
  have hQc : Q.card = 2 ^ K.card := card_agree_C0 s K
  have hEc : (2 : ℝ) ^ (K.card - 1) ≤ E.card := by
    rw [hE, card_blk]
    have h1 := card_fresh_ge s r0 Q
    have h2 : (2 : ℝ) ^ (K.card - 1) ≤ ((2 ^ K.card - (sensRows s r0).card : ℕ) : ℝ) :=
      two_pow_sub_le _ hd _ hF
    refine h2.trans ?_
    exact_mod_cast (by omega : 2 ^ K.card - (sensRows s r0).card ≤
      (Q.filter fun r => r ∉ sensRows s r0).card)
  set α : ℝ := 1 / 2 ^ K.card with hα
  have hαQ : (Q.card : ℝ) = 2 ^ K.card := by rw [hQc]; push_cast; rfl
  have hfr : ∀ w, fK (gluW s r0 f w) s K k' = rsum (gluW s r0 f w) s Q k' * α := by
    intro w; unfold fK; rw [effDevA_eq_rsum, ← hQ, hαQ, hα]; ring
  set L : Param N → ℝ := fun w => fK (gluW s r0 f w) s K k'
  set R : Param N → ℝ := fun w => L w - α * ∑ e ∈ E, sgnT (epsF f) w e
  have hLm : Measurable L := (measurable_effDevA s _ s k').comp (measurable_gluW s r0 f)
  refine hac N E (epsF f) α L R c η _ _ (by positivity) hη (by positivity)
    (V0_le K.card M hd hM _ hEc) (by positivity) hEc hLm ?_ (fun w => by simp only [R]; ring)
  intro w ξ
  simp only [R, L, hfr]
  have := rsum_fixed f Q k' (replE E w ξ) w
  rw [← hE] at this
  linear_combination α * this

/-- **`(N)`-atoms.** -/
theorem atom_n (N : ℕ) (s r0 : State N) (f : sensRows s r0 → Fin N → ℝ) (K : Finset (Fin N))
    (hd : 1 ≤ K.card) (hF : 2 * (sensRows s r0).card ≤ 2 ^ K.card) (M : ℕ) (hM : K.card + 1 ≤ M)
    (k j : Fin N) (hj : j ∈ univ \ K) (c η : ℝ) (hη : 0 < η) :
    cubeM N {w | |nAt N s K k j (gluW s r0 f w) - c| ≤ η} ≤ ENNReal.ofReal (patB C K.card M η) := by
  set Q := agree (univ \ K) (flipAt j s) with hQ
  set Q0 := agree (univ \ K) s with hQ0
  set E := fblk s r0 Q k with hE
  have hQc : Q.card = 2 ^ K.card := card_agree_Cj s K j
  have hQ0c : Q0.card = 2 ^ K.card := card_agree_C0 s K
  have hEc : (2 : ℝ) ^ (K.card - 1) ≤ E.card := by
    rw [hE, card_blk]
    have h1 := card_fresh_ge s r0 Q
    have h2 : (2 : ℝ) ^ (K.card - 1) ≤ ((2 ^ K.card - (sensRows s r0).card : ℕ) : ℝ) :=
      two_pow_sub_le _ hd _ hF
    refine h2.trans ?_
    exact_mod_cast (by omega : 2 ^ K.card - (sensRows s r0).card ≤
      (Q.filter fun r => r ∉ sensRows s r0).card)
  set α : ℝ := 1 / 2 ^ K.card with hα
  have hαQ : (Q.card : ℝ) = 2 ^ K.card := by rw [hQc]; push_cast; rfl
  have hαQ0 : (Q0.card : ℝ) = 2 ^ K.card := by rw [hQ0c]; push_cast; rfl
  have hdisj : ∀ r ∈ Q0, r ∉ Q := by
    intro r hr hr'
    have hjM : j ∈ univ \ K := hj
    have h1 := mem_agree.1 hr j hjM
    have h2 := mem_agree.1 hr' j hjM
    rw [h1] at h2
    unfold flipAt at h2
    simp at h2
  have hL : ∀ w, nAt N s K k j (gluW s r0 f w) =
      rsum (gluW s r0 f w) s Q k * α - (1 - 2 / mX N) * (rsum (gluW s r0 f w) s Q0 k * α) +
        kapN N := by
    intro w; unfold nAt hK fK; rw [effDevA_eq_rsum, effDevA_eq_rsum, ← hQ, ← hQ0, hαQ, hαQ0, hα]
    ring
  set L : Param N → ℝ := fun w => nAt N s K k j (gluW s r0 f w)
  set R : Param N → ℝ := fun w => L w - α * ∑ e ∈ E, sgnT (epsF f) w e
  have hLm : Measurable L := by
    have h1 := (measurable_effDevA s (univ \ K) (flipAt j s) k).comp (measurable_gluW s r0 f)
    have h2 := (measurable_effDevA s (univ \ K) s k).comp (measurable_gluW s r0 f)
    exact ((h1.sub (h2.const_mul _)).add_const _)
  refine hac N E (epsF f) α L R c η _ _ (by positivity) hη (by positivity)
    (V0_le K.card M hd hM _ hEc) (by positivity) hEc hLm ?_ (fun w => by simp only [R]; ring)
  intro w ξ
  simp only [R, L, hL]
  have h1 := rsum_fixed f Q k (replE E w ξ) w
  have h2 := rsum_repl f Q Q0 k k w ξ hdisj
  rw [← hE] at h1 h2
  rw [h2]
  linear_combination α * h1

/-- **`(D)`-atoms.** -/
theorem atom_d (N : ℕ) (s r0 : State N) (f : sensRows s r0 → Fin N → ℝ) (K : Finset (Fin N))
    (hd : 1 ≤ K.card) (hF : 2 * (sensRows s r0).card ≤ 2 ^ K.card) (M : ℕ)
    (k : Fin N) (A : Finset (Fin N)) (hA : A ∈ Aset N K) (hM : K.card + rD N + 1 ≤ M)
    (c η : ℝ) (hη : 0 < η) :
    cubeM N {w | |dAt N s K k A (gluW s r0 f w) - c| ≤ η} ≤ ENNReal.ofReal (patB C K.card M η) := by
  simp only [Aset, mem_filter, mem_powerset] at hA
  obtain ⟨hAM, _, hr2, hrD⟩ := hA
  set r := ((univ \ K) \ A).card with hr
  set Q := agree A s with hQ
  set Q0 := agree (univ \ K) s with hQ0
  set Q1 := Q \ Q0 with hQ1
  set E := fblk s r0 Q1 k with hE
  have hKN : K.card ≤ N := by have := card_le_univ K; rwa [Fintype.card_fin] at this
  have hAc : A.card + r + K.card = N := by
    have h1 := card_sdiff_of_subset hAM
    rw [card_sdiff_of_subset (subset_univ K), card_univ, Fintype.card_fin] at h1
    have h2 := card_le_card hAM
    rw [card_sdiff_of_subset (subset_univ K), card_univ, Fintype.card_fin] at h2
    rw [hr, h1]; omega
  have hQc : Q.card = 2 ^ (K.card + r) := by
    rw [hQ, card_agree]; congr 1; omega
  have hQ0c : Q0.card = 2 ^ K.card := card_agree_C0 s K
  have hsub : Q0 ⊆ Q := by
    intro t ht
    rw [mem_agree] at ht ⊢
    exact fun i hi => ht i (hAM hi)
  have hQ1c : Q1.card = 2 ^ (K.card + r) - 2 ^ K.card := by
    rw [hQ1, card_sdiff_of_subset hsub, hQc, hQ0c]
  have hEc' : (2 : ℝ) ^ (K.card + r - 1) ≤ E.card := by
    rw [hE, card_blk]
    have h1 := card_fresh_ge s r0 Q1
    have hp : 4 * 2 ^ K.card ≤ 2 ^ (K.card + r) := by
      rw [pow_add]
      have : 4 ≤ 2 ^ r := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr2
      nlinarith [Nat.one_le_two_pow (n := K.card)]
    have hp2 : 2 ^ (K.card + r) = 2 * 2 ^ (K.card + r - 1) := by
      rw [← pow_succ']; congr 1; omega
    have : 2 ^ (K.card + r - 1) ≤ (Q1.filter fun r => r ∉ sensRows s r0).card := by
      rw [hQ1c] at h1; omega
    exact_mod_cast this
  have hEc : (2 : ℝ) ^ (K.card - 1) ≤ E.card :=
    le_trans (pow_le_pow_right₀ (by norm_num) (by omega)) hEc'
  set α : ℝ := 1 / 2 ^ (K.card + r) with hα
  set α0 : ℝ := 1 / 2 ^ K.card with hα0
  have hαQ : (Q.card : ℝ) = 2 ^ (K.card + r) := by rw [hQc]; push_cast; rfl
  have hαQ0 : (Q0.card : ℝ) = 2 ^ K.card := by rw [hQ0c]; push_cast; rfl
  have hdisj : ∀ t ∈ Q0, t ∉ Q1 := by
    intro t ht ht1
    rw [hQ1, Finset.mem_sdiff] at ht1
    exact ht1.2 ht
  have hsplit : ∀ u : Param N, rsum u s Q k = rsum u s Q1 k + rsum u s Q0 k := by
    intro u; unfold rsum
    rw [hQ1, sum_sdiff hsub]
  have hL : ∀ w, dAt N s K k A (gluW s r0 f w) =
      (rsum (gluW s r0 f w) s Q1 k + rsum (gluW s r0 f w) s Q0 k) * α -
        (1 - (r : ℝ) / mX N) * (rsum (gluW s r0 f w) s Q0 k * α0) + kapN N / 2 := by
    intro w; unfold dAt fK; rw [effDevA_eq_rsum, effDevA_eq_rsum, ← hQ, ← hQ0, hαQ, hαQ0, hα, hα0,
      hsplit]
    ring
  set L : Param N → ℝ := fun w => dAt N s K k A (gluW s r0 f w)
  set R : Param N → ℝ := fun w => L w - α * ∑ e ∈ E, sgnT (epsF f) w e
  have hLm : Measurable L := by
    have h1 := (measurable_effDevA s A s k).comp (measurable_gluW s r0 f)
    have h2 := (measurable_effDevA s (univ \ K) s k).comp (measurable_gluW s r0 f)
    exact ((h1.sub (h2.const_mul _)).add_const _)
  have hV : Real.sqrt (1 / (12 * 2 ^ M)) ≤ α * Real.sqrt ((E.card : ℝ) / 12) :=
    V0_le (K.card + r) M (by omega) (by omega) _ hEc'
  refine hac N E (epsF f) α L R c η _ _ (by positivity) hη (by positivity) hV (by positivity) hEc
    hLm ?_ (fun w => by simp only [R]; ring)
  intro w ξ
  simp only [R, L, hL]
  have h1 := rsum_fixed f Q1 k (replE E w ξ) w
  have h2 := rsum_repl f Q1 Q0 k k w ξ hdisj
  rw [← hE] at h1 h2
  rw [h2]
  linear_combination α * h1

end Atoms

end Census
end IIT

#print axioms IIT.Census.ac_atom
#print axioms IIT.Census.atom_f
#print axioms IIT.Census.atom_n
#print axioms IIT.Census.atom_d
