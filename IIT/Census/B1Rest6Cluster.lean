/-
Census, B1 `NatTier3Rest6Stmt` (W12 §1.2): **the cluster events** (count and spread fields).

* `clr_window` (deterministic): with `F_j = log₂(y_j / A_j)`, `|A_j - 1/2| ≤ δ`, `j₀` the argmin of `F`, every unit with
  `F_j - F_{j₀} ≤ τ` has `y_j ∈ [y_{j₀} - 5δ, y_{j₀} - 5δ + (2τ + 15δ)]`.
* `clr_grid`, `clr_gridE`: one row; `≥ m` entries (resp. `xE`-values) in some window of width `h` has probability
  `≤ (⌈1/h⌉ + 1) C(N,m) (2h)^m` (resp. `(4h)^m`).
-/
import IIT.Census.B1Tier3NoLow
import IIT.Census.B1LTHiSolid

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-! ### The deterministic window -/

/-- **Near-minimal full-cut values force a cluster of the row entries.** -/
theorem clr_window {y A F : Fin N → ℝ} {δ τ : ℝ} (hy : ∀ j, 0 < y j) (hy1 : ∀ j, y j ≤ 1)
    (hA : ∀ j, |A j - 1 / 2| ≤ δ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 100) (hF : ∀ j, F j = Real.logb 2 (y j / A j))
    {j0 : Fin N} (hj0 : ∀ j, F j0 ≤ F j) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 4) {j : Fin N} (hj : F j - F j0 ≤ τ) :
    y j0 - 5 * δ ≤ y j ∧ y j ≤ y j0 - 5 * δ + (2 * τ + 15 * δ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hAl : ∀ i, 1 / 2 - δ ≤ A i := fun i => by have := (abs_le.1 (hA i)).1; linarith
  have hAu : ∀ i, A i ≤ 1 / 2 + δ := fun i => by have := (abs_le.1 (hA i)).2; linarith
  have hA0 : ∀ i, 0 < A i := fun i => by have := hAl i; linarith
  -- in nats: `F_i ln 2 = ln y_i - ln A_i`
  have hFl : ∀ i, F i * Real.log 2 = Real.log (y i) - Real.log (A i) := fun i => by
    rw [hF i, Real.logb, div_mul_cancel₀ _ hl2.ne', Real.log_div (hy i).ne' (hA0 i).ne']
  -- `|ln A_i - ln A_k| ≤ 5δ`
  have hAd : ∀ i k, Real.log (A i) - Real.log (A k) ≤ 5 * δ := by
    intro i k
    rw [← Real.log_div (hA0 i).ne' (hA0 k).ne']
    refine (Real.log_le_sub_one_of_pos (div_pos (hA0 i) (hA0 k))).trans ?_
    rw [div_sub_one (hA0 k).ne', div_le_iff₀ (hA0 k)]
    have := hAl k; have := hAu i
    nlinarith
  have h1 : Real.log (y j) - Real.log (y j0) ≤ τ + 5 * δ := by
    have e1 := hFl j; have e2 := hFl j0
    have := hAd j j0
    have hτl : (F j - F j0) * Real.log 2 ≤ τ := by
      calc (F j - F j0) * Real.log 2 ≤ τ * Real.log 2 := mul_le_mul_of_nonneg_right hj hl2.le
        _ ≤ τ := by nlinarith
    nlinarith
  have h2 : -(5 * δ) ≤ Real.log (y j) - Real.log (y j0) := by
    have e1 := hFl j; have e2 := hFl j0
    have := hAd j0 j
    have : 0 ≤ (F j - F j0) * Real.log 2 := mul_nonneg (by linarith [hj0 j]) hl2.le
    nlinarith
  have hratio : y j = y j0 * Real.exp (Real.log (y j) - Real.log (y j0)) := by
    rw [Real.exp_sub, Real.exp_log (hy j), Real.exp_log (hy j0)]; field_simp [(hy j0).ne']
  set u := Real.log (y j) - Real.log (y j0) with hu
  have hy0 := hy j0
  have hy01 := hy1 j0
  constructor
  · -- `e^u ≥ 1 + u ≥ 1 - 5δ`
    have := Real.add_one_le_exp u
    rw [hratio]
    nlinarith
  · -- `e^u ≤ 1 + u + u² ≤ 1 + 2(τ + 5δ)` for `|u| ≤ 1/2`
    have hu1 : |u| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have hb := Real.abs_exp_sub_one_sub_id_le hu1
    have hb' := (abs_le.1 hb).2
    have hsq : u ^ 2 ≤ τ + 5 * δ := by
      have : u ^ 2 ≤ |u| := by
        rw [← sq_abs]; nlinarith [abs_nonneg u]
      have : |u| ≤ τ + 5 * δ := by rw [abs_le]; constructor <;> linarith
      linarith
    rw [hratio]
    have he : Real.exp u ≤ 1 + 2 * (τ + 5 * δ) := by nlinarith
    have hE0 : 0 ≤ Real.exp u - 1 + 5 * δ := by have := Real.add_one_le_exp u; linarith
    nlinarith

/-! ### One row: a window of width `h` containing `m` entries -/

lemma clr_unif_Icc (a b : ℝ) (hab : a ≤ b) : unif (Set.Icc a b) ≤ ENNReal.ofReal (b - a) := by
  rw [unif_eq_Ioc]
  exact (Measure.restrict_le_self _).trans (by rw [Real.volume_Icc])

/-- The grid index of a window. -/
lemma clr_index {h a v : ℝ} (hh : 0 < h) (hv0 : 0 ≤ v) (hva : a ≤ v) (hvb : v ≤ a + h) :
    (⌊max a 0 / h⌋₊ : ℝ) * h ≤ v ∧ v ≤ (⌊max a 0 / h⌋₊ : ℝ) * h + 2 * h := by
  set a' := max a 0 with ha'
  have ha'0 : 0 ≤ a' := le_max_right _ _
  have h1 : (⌊a' / h⌋₊ : ℝ) ≤ a' / h := Nat.floor_le (div_nonneg ha'0 hh.le)
  have h2 : a' / h < (⌊a' / h⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h1' : (⌊a' / h⌋₊ : ℝ) * h ≤ a' := by rwa [le_div_iff₀ hh] at h1
  have h2' : a' < ((⌊a' / h⌋₊ : ℝ) + 1) * h := by rwa [div_lt_iff₀ hh] at h2
  have hva' : a' ≤ v := max_le hva hv0
  have : a ≤ a' := le_max_left _ _
  constructor <;> nlinarith

/-- **Cluster of row entries.** -/
theorem clr_grid (r : State N) {h : ℝ} (hh : 0 < h) (m : ℕ) (hm : 1 ≤ m) :
    cubeM N {w | w ∈ openCube N ∧ ∃ a : ℝ,
      m ≤ (univ.filter fun j : Fin N => clamp01 (w r j) ∈ Set.Icc a (a + h)).card} ≤
      ENNReal.ofReal ((⌈1 / h⌉₊ + 1) * (N.choose m * (2 * h) ^ m)) := by
  classical
  set G := ⌈1 / h⌉₊ with hG
  have hsub : {w : Param N | w ∈ openCube N ∧ ∃ a : ℝ,
      m ≤ (univ.filter fun j : Fin N => clamp01 (w r j) ∈ Set.Icc a (a + h)).card} ⊆
      ⋃ i ∈ Finset.range (G + 1), {w | m ≤ (univ.filter fun j : Fin N =>
        w r j ∈ Set.Icc ((i : ℝ) * h) ((i : ℝ) * h + 2 * h)).card} := by
    rintro w ⟨ho, a, ha⟩
    have hval : ∀ j, clamp01 (w r j) = w r j := fun j => b1_clamp01_of_mem_Ioo (ho r j)
    obtain ⟨j1, hj1⟩ : (univ.filter fun j : Fin N => clamp01 (w r j) ∈ Set.Icc a (a + h)).Nonempty := by
      rw [← card_pos]; omega
    have hj1' := (mem_filter.1 hj1).2
    rw [hval] at hj1'
    set i := ⌊max a 0 / h⌋₊ with hi
    have hiG : i < G + 1 := by
      have hv1 := (ho r j1).2.le
      have hix := (clr_index hh (ho r j1).1.le hj1'.1 hj1'.2).1
      have : (i : ℝ) ≤ 1 / h := by rw [le_div_iff₀ hh]; linarith
      have : (i : ℝ) ≤ G := this.trans (Nat.le_ceil _)
      have : i ≤ G := by exact_mod_cast this
      omega
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, Finset.mem_range]
    refine ⟨i, hiG, ha.trans (card_le_card fun j hj => ?_)⟩
    have hj' := (mem_filter.1 hj).2
    rw [hval] at hj'
    exact mem_filter.2 ⟨mem_univ _, clr_index hh (ho r j).1.le hj'.1 hj'.2⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hone : ∀ i ∈ Finset.range (G + 1), cubeM N {w : Param N | m ≤ (univ.filter fun j : Fin N =>
      w r j ∈ Set.Icc ((i : ℝ) * h) ((i : ℝ) * h + 2 * h)).card} ≤
      ENNReal.ofReal (N.choose m * (2 * h) ^ m) := by
    intro i _
    refine cubeM_card_entries_ge r measurableSet_Icc m (by positivity) ?_
    refine (clr_unif_Icc _ _ (by linarith)).trans (le_of_eq ?_)
    congr 1; ring
  refine (Finset.sum_le_sum hone).trans (le_of_eq ?_)
  rw [sum_const, card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  push_cast; ring_nf

/-- **Cluster of the `xE`-values of row `s`** (`xE = max(y, 1-y)`). -/
theorem clr_gridE (s : State N) {h : ℝ} (hh : 0 < h) (m : ℕ) (hm : 1 ≤ m) :
    cubeM N {w | w ∈ openCube N ∧ ∃ a : ℝ,
      m ≤ (univ.filter fun j : Fin N => xE w s j ∈ Set.Icc a (a + h)).card} ≤
      ENNReal.ofReal ((⌈1 / h⌉₊ + 1) * (N.choose m * (4 * h) ^ m)) := by
  classical
  set G := ⌈1 / h⌉₊ with hG
  set I : ℕ → Set ℝ := fun i => Set.Icc ((i : ℝ) * h) ((i : ℝ) * h + 2 * h) ∪
    Set.Icc (1 - ((i : ℝ) * h + 2 * h)) (1 - (i : ℝ) * h) with hI
  have hxE : ∀ (w : Param N) j, w ∈ openCube N → ∀ lo hi, xE w s j ∈ Set.Icc lo hi →
      w s j ∈ Set.Icc lo hi ∪ Set.Icc (1 - hi) (1 - lo) := by
    intro w j ho lo hi hx
    have hval : clamp01 (w s j) = w s j := b1_clamp01_of_mem_Ioo (ho s j)
    unfold xE at hx
    rw [hval] at hx
    rcases le_total (1 - w s j) (w s j) with h1 | h1
    · rw [max_eq_left h1] at hx; exact Or.inl hx
    · rw [max_eq_right h1] at hx
      exact Or.inr ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hsub : {w : Param N | w ∈ openCube N ∧ ∃ a : ℝ,
      m ≤ (univ.filter fun j : Fin N => xE w s j ∈ Set.Icc a (a + h)).card} ⊆
      ⋃ i ∈ Finset.range (G + 1), {w | m ≤ (univ.filter fun j : Fin N => w s j ∈ I i).card} := by
    rintro w ⟨ho, a, ha⟩
    obtain ⟨j1, hj1⟩ : (univ.filter fun j : Fin N => xE w s j ∈ Set.Icc a (a + h)).Nonempty := by
      rw [← card_pos]; omega
    have hj1' := (mem_filter.1 hj1).2
    set i := ⌊max a 0 / h⌋₊ with hi
    have hx0 : ∀ j, 0 ≤ xE w s j := fun j => (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (xE_ge_half w s j)
    have hiG : i < G + 1 := by
      have hv1 := xE_le_one w s j1
      have hix := (clr_index hh (hx0 j1) hj1'.1 hj1'.2).1
      have : (i : ℝ) ≤ 1 / h := by rw [le_div_iff₀ hh]; linarith
      have : (i : ℝ) ≤ G := this.trans (Nat.le_ceil _)
      have : i ≤ G := by exact_mod_cast this
      omega
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, Finset.mem_range]
    refine ⟨i, hiG, ha.trans (card_le_card fun j hj => ?_)⟩
    have hj' := (mem_filter.1 hj).2
    exact mem_filter.2 ⟨mem_univ _, hxE w j ho _ _ (clr_index hh (hx0 j) hj'.1 hj'.2)⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hone : ∀ i ∈ Finset.range (G + 1), cubeM N {w : Param N | m ≤ (univ.filter fun j : Fin N =>
      w s j ∈ I i).card} ≤ ENNReal.ofReal (N.choose m * (4 * h) ^ m) := by
    intro i _
    refine cubeM_card_entries_ge s (measurableSet_Icc.union measurableSet_Icc) m (by positivity) ?_
    refine (measure_union_le _ _).trans ((add_le_add (clr_unif_Icc _ _ (by linarith))
      (clr_unif_Icc _ _ (by linarith))).trans (le_of_eq ?_))
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1; ring
  refine (Finset.sum_le_sum hone).trans (le_of_eq ?_)
  rw [sum_const, card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  push_cast; ring_nf

/-! ### Count and spread failures are clusters (abstract) -/

section Abstract

variable {y A F : Fin N → ℝ} {δ : ℝ} {j0 : Fin N}

/-- **Count failure ⇒ cluster** (`≥ N/5` entries in a window of width `3/N`). -/
theorem clr_count_abs (hy : ∀ j, 0 < y j) (hy1 : ∀ j, y j ≤ 1) (hA : ∀ j, |A j - 1 / 2| ≤ δ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 100) (hF : ∀ j, F j = Real.logb 2 (y j / A j)) (hj0 : ∀ j, F j0 ≤ F j) (hN : 4 ≤ N)
    (hδN : 15 * δ ≤ 1 / (N : ℝ))
    (hfail : N ≤ 5 * (univ.filter fun j => F j - F j0 ≤ 1 / (N : ℝ)).card) :
    ∃ a : ℝ, N / 5 ≤ (univ.filter fun j => y j ∈ Set.Icc a (a + 3 / (N : ℝ))).card := by
  classical
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨y j0 - 5 * δ, ?_⟩
  have hsub : (univ.filter fun j => F j - F j0 ≤ 1 / (N : ℝ)) ⊆
      univ.filter fun j => y j ∈ Set.Icc (y j0 - 5 * δ) (y j0 - 5 * δ + 3 / (N : ℝ)) := by
    intro j hj
    have hj' := (mem_filter.1 hj).2
    have hτ : 1 / (N : ℝ) ≤ 1 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    obtain ⟨h1, h2⟩ := clr_window hy hy1 hA hδ0 hδ hF hj0 (by positivity) hτ hj'
    refine mem_filter.2 ⟨mem_univ _, h1, h2.trans ?_⟩
    have : 2 * (1 / (N : ℝ)) + 15 * δ ≤ 3 / N := by
      have e : (3 : ℝ) / N = 2 * (1 / N) + 1 / N := by ring
      linarith
    linarith
  have := card_le_card hsub
  omega

/-- **Spread failure ⇒ cluster** (`≥ N/2` entries in a window of width `3τ`, `τ = 50D/N`). -/
theorem clr_spread_abs (hy : ∀ j, 0 < y j) (hy1 : ∀ j, y j ≤ 1) (hA : ∀ j, |A j - 1 / 2| ≤ δ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 100) (hF : ∀ j, F j = Real.logb 2 (y j / A j)) (hj0 : ∀ j, F j0 ≤ F j) {D : ℕ} (hD : 1 ≤ D)
    (hN : 10 * D ≤ N) (hτ : 50 * (D : ℝ) / N ≤ 1 / 4) (hδτ : 15 * δ ≤ 50 * (D : ℝ) / N)
    {A' : Finset (Fin N)} (hA' : A'.card < 2 * D) (hsum : ∑ j ∈ A'ᶜ, (F j - F j0) ≤ 5 * D) :
    ∃ a : ℝ, N / 2 ≤ (univ.filter fun j => y j ∈ Set.Icc a (a + 3 * (50 * (D : ℝ) / N))).card := by
  classical
  set τ : ℝ := 50 * (D : ℝ) / N with hτdef
  have hN10 : (10 : ℝ) ≤ N := by exact_mod_cast (show 10 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hτ0 : 0 < τ := by rw [hτdef]; positivity
  -- the units of `A'ᶜ` with a large gap
  set Bg := A'ᶜ.filter fun j => τ < F j - F j0 with hBg
  have hgap : ∀ j, 0 ≤ F j - F j0 := fun j => sub_nonneg.2 (hj0 j)
  have hBg_sum : (Bg.card : ℝ) * τ ≤ 5 * D := by
    have h1 : ∑ j ∈ Bg, τ ≤ ∑ j ∈ Bg, (F j - F j0) := sum_le_sum fun j hj => (mem_filter.1 hj).2.le
    have h2 : ∑ j ∈ Bg, (F j - F j0) ≤ ∑ j ∈ A'ᶜ, (F j - F j0) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ => hgap j
    rw [sum_const, nsmul_eq_mul] at h1
    linarith
  have hBg_card : 10 * Bg.card ≤ N := by
    have e : (Bg.card : ℝ) * τ * N = Bg.card * (50 * D) := by rw [hτdef]; field_simp
    have h1 := mul_le_mul_of_nonneg_right hBg_sum hN0.le
    have h2 : (Bg.card : ℝ) * (50 * D) ≤ 5 * D * N := by linarith
    have hDp : (0 : ℝ) < D := by linarith
    have h3 : (Bg.card : ℝ) * 10 ≤ N := by nlinarith
    have : ((10 * Bg.card : ℕ) : ℝ) ≤ N := by push_cast; linarith
    exact_mod_cast this
  -- the small-gap units
  have hsub : (A'ᶜ \ Bg) ⊆ univ.filter fun j => y j ∈ Set.Icc (y j0 - 5 * δ) (y j0 - 5 * δ + 3 * τ) := by
    intro j hj
    obtain ⟨hjA, hjB⟩ := mem_sdiff.1 hj
    have hj' : F j - F j0 ≤ τ := by
      by_contra hc; push Not at hc; exact hjB (mem_filter.2 ⟨hjA, hc⟩)
    obtain ⟨h1, h2⟩ := clr_window hy hy1 hA hδ0 hδ hF hj0 hτ0.le hτ hj'
    exact mem_filter.2 ⟨mem_univ _, h1, by linarith⟩
  refine ⟨y j0 - 5 * δ, ?_⟩
  have h1 := card_le_card hsub
  have h2 : (A'ᶜ \ Bg).card = A'ᶜ.card - Bg.card := card_sdiff_of_subset (filter_subset _ _)
  have h3 : A'ᶜ.card = N - A'.card := by rw [card_compl, Fintype.card_fin]
  have h4 : A'.card ≤ N := by have := card_le_univ A'; simpa using this
  omega

end Abstract

/-! ### Superexponential numerics -/

/-- `(N+2) 4^N q^m ≤ e^{-CN}` once `q ≤ e^{-k(C+2)}` and `N ≤ k(m+1)`. -/
theorem clr_num (C : ℝ) {k : ℕ} (hk : 1 ≤ k) : ∀ᶠ N : ℕ in atTop, ∀ (q : ℝ) (m : ℕ), 0 ≤ q →
    q ≤ Real.exp (-(k * (|C| + 2))) → N ≤ k * (m + 1) →
    ((N : ℝ) + 2) * ((2 : ℝ) ^ N * ((2 : ℝ) ^ N * q ^ m)) ≤ Real.exp (-(C * N)) := by
  set K : ℝ := k * (|C| + 2) with hK
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK0 : 0 ≤ K := by positivity
  -- `(N+2) e^{K} e^{-N/2} → 0`
  have ht : Tendsto (fun N : ℕ => ((N : ℝ) + 2) * Real.exp (-((N : ℝ) / 2))) atTop (𝓝 0) := by
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (by norm_num : (0 : ℝ) < 2))
    have h2 : Tendsto (fun N : ℕ => Real.exp (-((N : ℝ) / 2))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (by norm_num)))
    have := (h1.const_mul 2).add (h2.const_mul 2)
    simp only [mul_zero, add_zero] at this
    refine this.congr fun N => ?_
    simp only [Function.comp, pow_one]; ring
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < Real.exp (-K) by positivity))] with N hN
  intro q m hq0 hq hNm
  have hNr : (N : ℝ) ≤ k * ((m : ℝ) + 1) := by exact_mod_cast hNm
  have hqm : q ^ m ≤ Real.exp (-(|C| + 2) * (N - k)) := by
    calc q ^ m ≤ Real.exp (-K) ^ m := pow_le_pow_left₀ hq0 hq m
      _ = Real.exp (-K * m) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-(|C| + 2) * (N - k)) := Real.exp_le_exp.2 (by rw [hK]; nlinarith [abs_nonneg C])
  have h4 : (2 : ℝ) ^ N * (2 : ℝ) ^ N = Real.exp (Real.log 4 * N) := by
    rw [← mul_pow, show (2 : ℝ) * 2 = 4 by norm_num, Real.exp_mul, Real.exp_log (by norm_num), Real.rpow_natCast]
  have hl4 : Real.log 4 < 3 / 2 := by
    have := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hpos := Real.exp_pos (-((N : ℝ) / 2))
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc ((N : ℝ) + 2) * ((2 : ℝ) ^ N * ((2 : ℝ) ^ N * q ^ m))
      = ((N : ℝ) + 2) * (Real.exp (Real.log 4 * N) * q ^ m) := by rw [← h4]; ring
    _ ≤ ((N : ℝ) + 2) * (Real.exp (Real.log 4 * N) * Real.exp (-(|C| + 2) * (N - k))) := by
        gcongr
    _ = ((N : ℝ) + 2) * Real.exp (-((N : ℝ) / 2)) * Real.exp K *
          Real.exp ((Real.log 4 - 3 / 2) * N - |C| * N) := by
        rw [hK, mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add, ← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp (-K) * Real.exp K * Real.exp (-(C * N)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hN.le (Real.exp_pos _).le) (Real.exp_le_exp.2 ?_)
          (Real.exp_pos _).le (by positivity)
        have := le_abs_self C
        nlinarith
    _ = Real.exp (-(C * N)) := by rw [← Real.exp_add]; simp

/-- `DU/N → 0`. -/
lemma DU_div_tendsto : Tendsto (fun N : ℕ => (DU N : ℝ) / N) atTop (𝓝 0) := by
  have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h20 : Tendsto (fun N : ℕ => (20 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hup : Tendsto (fun N : ℕ => 6 * (Real.log N ^ 1 / (1 * (N : ℝ) + 0)) + (20 : ℝ) / N) atTop (𝓝 0) := by
    simpa using (ht.const_mul 6).add h20
  refine squeeze_zero (fun N => by positivity) (fun N => ?_) hup
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · have hN : (0 : ℝ) < N := by exact_mod_cast h
    simp only [pow_one, one_mul, add_zero]
    rw [div_le_iff₀ hN]
    have := DU_le_log N
    have e : (6 * (Real.log N / N) + 20 / N) * N = 6 * Real.log N + 20 := by field_simp
    linarith

/-- Eventual numerics of the cluster events. -/
lemma clr_ev (C : ℝ) : ∀ᶠ N : ℕ in atTop, 64 ≤ N ∧ 15 * dU N (N - 1) ≤ 1 / (N : ℝ) ∧
    dU N (N - 1) ≤ 1 / 100 ∧ 10 * DU N ≤ N ∧ 50 * (DU N : ℝ) / N ≤ 1 / 4 ∧
    6 / (N : ℝ) ≤ Real.exp (-(5 * (|C| + 2))) ∧ 12 / (N : ℝ) ≤ Real.exp (-(5 * (|C| + 2))) ∧
    300 * (DU N : ℝ) / N ≤ Real.exp (-(2 * (|C| + 2))) ∧ 600 * (DU N : ℝ) / N ≤ Real.exp (-(2 * (|C| + 2))) := by
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have e5 : (0 : ℝ) < Real.exp (-(5 * (|C| + 2))) / 12 := by positivity
  have e2 : (0 : ℝ) < Real.exp (-(2 * (|C| + 2))) / 600 := by positivity
  filter_upwards [eventually_ge_atTop 64, ev_N_dU_top, ev_lin_C, hinv.eventually (gt_mem_nhds e5),
    DU_div_tendsto.eventually (gt_mem_nhds e2)] with N hN htop hlin h1 h2
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hD0 : (0 : ℝ) ≤ DU N := Nat.cast_nonneg _
  have hδ0 := dU_nonneg N (N - 1)
  have hlinD : 10 * (DU N : ℝ) ≤ N / 50 := by nlinarith
  refine ⟨hN, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hN0]; nlinarith
  · have : dU N (N - 1) ≤ N * dU N (N - 1) := le_mul_of_one_le_left hδ0 (by linarith)
    linarith
  · have : ((10 * DU N : ℕ) : ℝ) ≤ N := by push_cast; linarith
    exact_mod_cast this
  · rw [div_le_iff₀ hN0]; linarith
  · have : 6 / (N : ℝ) = 6 * (1 / N) := by ring
    rw [this]; linarith
  · have : 12 / (N : ℝ) = 12 * (1 / N) := by ring
    rw [this]; linarith
  · have : 300 * (DU N : ℝ) / N = 300 * (DU N / N) := by ring
    rw [this]; linarith
  · have : 600 * (DU N : ℝ) / N = 600 * (DU N / N) := by ring
    rw [this]; linarith

/-! ### The cause-side cluster event -/

/-- Count or spread fails at tc (on the concentration event). -/
def clrBadC (N : ℕ) (s : State N) : Set (Param N) :=
  {w | w ∈ openCube N ∧ concCAt N w (tcRow w) ∧
    ¬ ((∀ A' : Finset (Fin N), A'.card < 2 * DU N →
        5 * (DU N : ℝ) < ∑ j ∈ A'ᶜ, (kF (lamCz (flipP s w) s (tcRow w)) j - lcMin s w)) ∧
      5 * (univ.filter fun j => kF (lamCz (flipP s w) s (tcRow w)) j - lcMin s w ≤ 1 / (N : ℝ)).card < N)}

/-- **The cause-side cluster event is superexponentially rare.** -/
theorem clrBadC_rare (C : ℝ) : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (clrBadC N s) ≤ ENNReal.ofReal (2 * Real.exp (-(C * N))) := by
  filter_upwards [clr_ev C, clr_num C (k := 5) (by norm_num), clr_num C (k := 2) (by norm_num)]
    with N hev hn5 hn2 s
  obtain ⟨hN64, hδN, hδ, hD10, hτ, hq1, -, hq2, -⟩ := hev
  classical
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hN0 : (0 : ℝ) < N := by linarith
  have hDN : DU N ≤ N - 1 := DU_le hN64
  have hD1 : 1 ≤ DU N := by unfold DU; omega
  have hD1r : (1 : ℝ) ≤ DU N := by exact_mod_cast hD1
  set h1 : ℝ := 3 / N with hh1
  set h2 : ℝ := 3 * (50 * (DU N : ℝ) / N) with hh2
  set E1 : State N → Set (Param N) := fun r => {w | w ∈ openCube N ∧ ∃ a : ℝ,
    N / 5 ≤ (univ.filter fun j : Fin N => clamp01 (w r j) ∈ Set.Icc a (a + h1)).card} with hE1
  set E2 : State N → Set (Param N) := fun r => {w | w ∈ openCube N ∧ ∃ a : ℝ,
    N / 2 ≤ (univ.filter fun j : Fin N => clamp01 (w r j) ∈ Set.Icc a (a + h2)).card} with hE2
  have hsub : clrBadC N s ⊆ ⋃ r : State N, (E1 r ∪ E2 r) := by
    rintro w ⟨ho, hcC, hfail⟩
    refine Set.mem_iUnion.2 ⟨tcRow w, ?_⟩
    have hz : flipP s w ∈ openCube N := flipP_mem_openCube ho
    obtain ⟨mc1, -, mc3, -, -⟩ := lamCz_means hz s (tcRow w)
    rw [flipP_invol s w] at mc1 mc3
    set F := kF (lamCz (flipP s w) s (tcRow w)) with hFdef
    set y : Fin N → ℝ := fun j => clamp01 (w (tcRow w) j) with hy
    set A : Fin N → ℝ := fun j => cmean w (univ \ univ.erase j) (tcRow w) j with hA
    have hFy : ∀ j, F j = Real.logb 2 (y j / A j) := fun j => mc1 j (univ.erase j)
    have hcard : ∀ j : Fin N, (univ.erase j).card = N - 1 := fun j => by
      rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
    have hAc : ∀ j, |A j - 1 / 2| ≤ dU N (N - 1) := fun j => by
      have := hcC j (univ.erase j) (notMem_erase j univ) (by rw [hcard j]; exact hDN)
      rwa [hcard j] at this
    obtain ⟨j0, hj0e⟩ := g_ciInf_attained (by omega) F
    have hbdd : BddBelow (Set.range F) := (Set.finite_range F).bddBelow
    have hj0 : ∀ j, F j0 ≤ F j := fun j => hj0e ▸ ciInf_le hbdd j
    have hlc : lcMin s w = F j0 := hj0e.symm
    have hyp : ∀ j, 0 < y j := mc3
    have hy1 : ∀ j, y j ≤ 1 := fun j => clamp01_le_one _
    have hδ0 := dU_nonneg N (N - 1)
    rw [not_and_or] at hfail
    rcases hfail with hsp | hct
    · right
      push Not at hsp
      obtain ⟨A', hA'c, hsum⟩ := hsp
      rw [hlc] at hsum
      have hδτ : 15 * dU N (N - 1) ≤ 50 * (DU N : ℝ) / N := by
        have : 1 / (N : ℝ) ≤ 50 * (DU N : ℝ) / N := by
          rw [div_le_div_iff_of_pos_right hN0]; linarith
        linarith
      obtain ⟨a, ha⟩ := clr_spread_abs hyp hy1 hAc hδ0 hδ hFy hj0 hD1 hD10 hτ hδτ hA'c hsum
      exact ⟨ho, a, ha⟩
    · left
      push Not at hct
      rw [hlc] at hct
      obtain ⟨a, ha⟩ := clr_count_abs hyp hy1 hAc hδ0 hδ hFy hj0 (by omega) hδN hct
      exact ⟨ho, a, ha⟩
  -- the measure
  have hm1 : 1 ≤ N / 5 := by omega
  have hm2 : 1 ≤ N / 2 := by omega
  have hh1p : 0 < h1 := by positivity
  have hh2p : 0 < h2 := by positivity
  have hc1 : (⌈1 / h1⌉₊ : ℝ) + 1 ≤ N + 2 := by
    have : 1 / h1 ≤ N := by rw [hh1, one_div_div, div_le_iff₀ (by norm_num)]; linarith
    have := (Nat.ceil_le.2 (show 1 / h1 ≤ ((N : ℕ) : ℝ) by exact_mod_cast this))
    have : (⌈1 / h1⌉₊ : ℝ) ≤ N := by exact_mod_cast this
    linarith
  have hc2 : (⌈1 / h2⌉₊ : ℝ) + 1 ≤ N + 2 := by
    have : 1 / h2 ≤ N := by
      rw [div_le_iff₀ hh2p, hh2]
      have : (N : ℝ) * (3 * (50 * (DU N : ℝ) / N)) = 150 * DU N := by field_simp; ring
      rw [this]; linarith
    have := (Nat.ceil_le.2 (show 1 / h2 ≤ ((N : ℕ) : ℝ) by exact_mod_cast this))
    have : (⌈1 / h2⌉₊ : ℝ) ≤ N := by exact_mod_cast this
    linarith
  have hch : ∀ m, (N.choose m : ℝ) ≤ 2 ^ N := fun m => by exact_mod_cast Nat.choose_le_two_pow N m
  have hb1 : ∀ r, cubeM N (E1 r) ≤ ENNReal.ofReal (((N : ℝ) + 2) * ((2 : ℝ) ^ N * (2 * h1) ^ (N / 5))) := by
    intro r
    refine (clr_grid r hh1p (N / 5) hm1).trans (ENNReal.ofReal_le_ofReal ?_)
    have := hch (N / 5)
    gcongr
  have hb2 : ∀ r, cubeM N (E2 r) ≤ ENNReal.ofReal (((N : ℝ) + 2) * ((2 : ℝ) ^ N * (2 * h2) ^ (N / 2))) := by
    intro r
    refine (clr_grid r hh2p (N / 2) hm2).trans (ENNReal.ofReal_le_ofReal ?_)
    have := hch (N / 2)
    gcongr
  have hq1' : 2 * h1 ≤ Real.exp (-((5 : ℕ) * (|C| + 2))) := by
    rw [hh1]; push_cast; have : 2 * (3 / (N : ℝ)) = 6 / N := by ring
    rw [this]; exact hq1
  have hq2' : 2 * h2 ≤ Real.exp (-((2 : ℕ) * (|C| + 2))) := by
    rw [hh2]; push_cast; have : 2 * (3 * (50 * (DU N : ℝ) / N)) = 300 * DU N / N := by ring
    rw [this]; exact hq2
  have hr1 := hn5 (2 * h1) (N / 5) (by positivity) hq1' (by omega)
  have hr2 := hn2 (2 * h2) (N / 2) (by positivity) hq2' (by omega)
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
  refine (Finset.sum_le_sum fun r _ => (measure_union_le _ _).trans (add_le_add (hb1 r) (hb2 r))).trans ?_
  rw [sum_const, card_univ, nsmul_eq_mul]
  have hcs : ((Fintype.card (State N) : ℕ) : ENNReal) = ENNReal.ofReal ((2 : ℝ) ^ N) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  rw [hcs, ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith

/-! ### The effect-side cluster event (row `s` at `teW`) -/

/-- Count or spread fails at `teW` (on the concentration event). -/
def clrBadE (N : ℕ) (s : State N) : Set (Param N) :=
  {w | w ∈ openCube N ∧ concEAll N s w ∧
    ¬ ((∀ A' : Finset (Fin N), A'.card < 2 * DU N →
        5 * (DU N : ℝ) < ∑ j ∈ A'ᶜ, (kF (lamEz (flipP s w) s (teW w s)) j - leMinAt s w (teW w s))) ∧
      5 * (univ.filter fun j => kF (lamEz (flipP s w) s (teW w s)) j - leMinAt s w (teW w s) ≤ 1 / (N : ℝ)).card < N)}

/-- **The effect-side cluster event is superexponentially rare.** -/
theorem clrBadE_rare (C : ℝ) : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (clrBadE N s) ≤ ENNReal.ofReal (2 * Real.exp (-(C * N))) := by
  filter_upwards [clr_ev C, clr_num C (k := 5) (by norm_num), clr_num C (k := 2) (by norm_num)]
    with N hev hn5 hn2 s
  obtain ⟨hN64, hδN, hδ, hD10, hτ, -, hq1, -, hq2⟩ := hev
  classical
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hN0 : (0 : ℝ) < N := by linarith
  have hDN : DU N ≤ N - 1 := DU_le hN64
  have hD1 : 1 ≤ DU N := by unfold DU; omega
  have hD1r : (1 : ℝ) ≤ DU N := by exact_mod_cast hD1
  set h1 : ℝ := 3 / N with hh1
  set h2 : ℝ := 3 * (50 * (DU N : ℝ) / N) with hh2
  set E1 : Set (Param N) := {w | w ∈ openCube N ∧ ∃ a : ℝ,
    N / 5 ≤ (univ.filter fun j : Fin N => xE w s j ∈ Set.Icc a (a + h1)).card} with hE1
  set E2 : Set (Param N) := {w | w ∈ openCube N ∧ ∃ a : ℝ,
    N / 2 ≤ (univ.filter fun j : Fin N => xE w s j ∈ Set.Icc a (a + h2)).card} with hE2
  have hsub : clrBadE N s ⊆ E1 ∪ E2 := by
    rintro w ⟨ho, hcE, hfail⟩
    have hz : flipP s w ∈ openCube N := flipP_mem_openCube ho
    obtain ⟨me1, -, -, me4, -⟩ := lamEz_means hz s (teW w s)
    set F := kF (lamEz (flipP s w) s (teW w s)) with hFdef
    set y : Fin N → ℝ := fun j => xE w s j with hy
    set A : Fin N → ℝ := fun j => effUnit (tpmOf (flipP s w)) (univ.erase j)ᶜ s j (teW w s j) with hA
    have hpr : ∀ j, (tpmOf (flipP s w)).prob j s (teW w s j) = xE w s j := by
      intro j
      have h := prob_teW_row (flipP s w) s s j
      rw [flipP_invol s w] at h
      rw [h, ← xE_eq_pTe]
    have hFy : ∀ j, F j = Real.logb 2 (y j / A j) := fun j => by
      rw [hFdef]; show lamEz (flipP s w) s (teW w s) j (univ.erase j) = _
      rw [me1, hpr]
    have hcard : ∀ j : Fin N, (univ.erase j).card = N - 1 := fun j => by
      rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
    have hAc : ∀ j, |A j - 1 / 2| ≤ dU N (N - 1) := fun j => by
      have := hcE (teW w s) j (univ.erase j) (notMem_erase j univ) (by rw [hcard j]; exact hDN)
      rwa [hcard j] at this
    obtain ⟨j0, hj0e⟩ := g_ciInf_attained (by omega) F
    have hbdd : BddBelow (Set.range F) := (Set.finite_range F).bddBelow
    have hj0 : ∀ j, F j0 ≤ F j := fun j => hj0e ▸ ciInf_le hbdd j
    have hlc : leMinAt s w (teW w s) = F j0 := hj0e.symm
    have hyp : ∀ j, 0 < y j := fun j => xE_pos w s j
    have hy1 : ∀ j, y j ≤ 1 := fun j => xE_le_one w s j
    have hδ0 := dU_nonneg N (N - 1)
    rw [not_and_or] at hfail
    rcases hfail with hsp | hct
    · right
      push Not at hsp
      obtain ⟨A', hA'c, hsum⟩ := hsp
      rw [hlc] at hsum
      have hδτ : 15 * dU N (N - 1) ≤ 50 * (DU N : ℝ) / N := by
        have : 1 / (N : ℝ) ≤ 50 * (DU N : ℝ) / N := by
          rw [div_le_div_iff_of_pos_right hN0]; linarith
        linarith
      obtain ⟨a, ha⟩ := clr_spread_abs hyp hy1 hAc hδ0 hδ hFy hj0 hD1 hD10 hτ hδτ hA'c hsum
      exact ⟨ho, a, ha⟩
    · left
      push Not at hct
      rw [hlc] at hct
      obtain ⟨a, ha⟩ := clr_count_abs hyp hy1 hAc hδ0 hδ hFy hj0 (by omega) hδN hct
      exact ⟨ho, a, ha⟩
  -- the measure
  have hm1 : 1 ≤ N / 5 := by omega
  have hm2 : 1 ≤ N / 2 := by omega
  have hh1p : 0 < h1 := by positivity
  have hh2p : 0 < h2 := by positivity
  have hc1 : (⌈1 / h1⌉₊ : ℝ) + 1 ≤ N + 2 := by
    have : 1 / h1 ≤ N := by rw [hh1, one_div_div, div_le_iff₀ (by norm_num)]; linarith
    have := (Nat.ceil_le.2 (show 1 / h1 ≤ ((N : ℕ) : ℝ) by exact_mod_cast this))
    have : (⌈1 / h1⌉₊ : ℝ) ≤ N := by exact_mod_cast this
    linarith
  have hc2 : (⌈1 / h2⌉₊ : ℝ) + 1 ≤ N + 2 := by
    have : 1 / h2 ≤ N := by
      rw [div_le_iff₀ hh2p, hh2]
      have : (N : ℝ) * (3 * (50 * (DU N : ℝ) / N)) = 150 * DU N := by field_simp; ring
      rw [this]; linarith
    have := (Nat.ceil_le.2 (show 1 / h2 ≤ ((N : ℕ) : ℝ) by exact_mod_cast this))
    have : (⌈1 / h2⌉₊ : ℝ) ≤ N := by exact_mod_cast this
    linarith
  have hch : ∀ m, (N.choose m : ℝ) ≤ 2 ^ N := fun m => by exact_mod_cast Nat.choose_le_two_pow N m
  have h2N : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  have hb1 : cubeM N E1 ≤ ENNReal.ofReal (((N : ℝ) + 2) * ((2 : ℝ) ^ N * ((2 : ℝ) ^ N * (4 * h1) ^ (N / 5)))) := by
    refine (clr_gridE s hh1p (N / 5) hm1).trans (ENNReal.ofReal_le_ofReal ?_)
    have := hch (N / 5)
    have h0 : (0 : ℝ) ≤ (4 * h1) ^ (N / 5) := by positivity
    have : (N.choose (N / 5) : ℝ) * (4 * h1) ^ (N / 5) ≤ 2 ^ N * (2 ^ N * (4 * h1) ^ (N / 5)) := by
      have k1 := mul_le_mul_of_nonneg_right this h0
      have k2 : (2 : ℝ) ^ N * (4 * h1) ^ (N / 5) ≤ 2 ^ N * (2 ^ N * (4 * h1) ^ (N / 5)) := by
        have := mul_le_mul_of_nonneg_right h2N (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ N) h0)
        nlinarith
      linarith
    gcongr
  have hb2 : cubeM N E2 ≤ ENNReal.ofReal (((N : ℝ) + 2) * ((2 : ℝ) ^ N * ((2 : ℝ) ^ N * (4 * h2) ^ (N / 2)))) := by
    refine (clr_gridE s hh2p (N / 2) hm2).trans (ENNReal.ofReal_le_ofReal ?_)
    have := hch (N / 2)
    have h0 : (0 : ℝ) ≤ (4 * h2) ^ (N / 2) := by positivity
    have : (N.choose (N / 2) : ℝ) * (4 * h2) ^ (N / 2) ≤ 2 ^ N * (2 ^ N * (4 * h2) ^ (N / 2)) := by
      have k1 := mul_le_mul_of_nonneg_right this h0
      have k2 : (2 : ℝ) ^ N * (4 * h2) ^ (N / 2) ≤ 2 ^ N * (2 ^ N * (4 * h2) ^ (N / 2)) := by
        have := mul_le_mul_of_nonneg_right h2N (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ N) h0)
        nlinarith
      linarith
    gcongr
  have hq1' : 4 * h1 ≤ Real.exp (-((5 : ℕ) * (|C| + 2))) := by
    rw [hh1]; push_cast; have : 4 * (3 / (N : ℝ)) = 12 / N := by ring
    rw [this]; exact hq1
  have hq2' : 4 * h2 ≤ Real.exp (-((2 : ℕ) * (|C| + 2))) := by
    rw [hh2]; push_cast; have : 4 * (3 * (50 * (DU N : ℝ) / N)) = 600 * DU N / N := by ring
    rw [this]; exact hq2
  have hr1 := hn5 (4 * h1) (N / 5) (by positivity) hq1' (by omega)
  have hr2 := hn2 (4 * h2) (N / 2) (by positivity) hq2' (by omega)
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ((add_le_add hb1 hb2).trans ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith

end Census
end IIT
