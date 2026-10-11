/-
Census, B1 forced leaves 4 (`bTilt`) and 5 (`bLink`) of `B1ForcedSkel`, agent "forcedD".

Both are deduced, WITHOUT `GoodW` (false in regime X), from a pair/triple competitor lower bound:

* leaf 4: on B1 (`U` beats every pair), with all half-means regular and `Z ≥ 1/2`, the single-cut cause bound
  (`phi_le_cause`) gives `φ_s(U) ≤ 2 N β`; if the tilt fails, `β < 2 σ_N e^{-slT}`, so `β < σ_N` and every pair
  has `φ_s < 3 σ_N`. That is the event of **Lemma LT2** (W2 §9, `LT2Stmt 1 C`), excluded at any rate.
* leaf 5: the single-cut effect bound (`phi_le_eff`) gives `φ_s(U) ≤ 2 N e`; if the link fails, `e < β/(8 N)` (with
  `Z ≤ 13`), so every pair and triple has `φ_s < β/4`. That is the event of the **pair/triple level bound**
  (`LTBetaStmt (1/4) C`, W6 §2.3 "B1 ⇒ φ_s(U) > max triples ≥ cβ (LT)").

PROVED here (sorry-free): `dt_half_all`, `dt_Zs_bad`, the deterministic deductions `dt_tilt_det`, `dt_link_det`,
and `leaf4_of_LT2`, `leaf5_of_LTBeta` (the leaves at rate `RfF`, and the strong forms at rate `102/100` used
by leaf 7). The two statements `LT2Stmt`, `LTBetaStmt` are NOT proved here (they are the content of W2 §9 and
W2 §8 + W8/W11).
-/
import IIT.Census.B1ForcedA
import IIT.Census.BigPhiSys
import IIT.Census.B1UnivFacts

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-! ### The competitor statements (hypotheses of this file) -/

/-- **Lemma LT2** (W2 §9, Lean form given there): below the tilt some pair reaches `3 L σ_N`. No `GoodW`. -/
def LT2Stmt (L C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N {w | betaW w < L * sigN N ∧
      ∀ S : Finset (Fin N), S.card = 2 → phi (flipP s w) s S < 3 * L * sigN N} ≤
      ENNReal.ofReal (Real.exp (-(C * N)))

/-- **The pair/triple level bound on B1** (W6 §2.3, W2 §8-9, W8, W11): on B1, some pair or triple reaches `c β`. -/
def LTBetaStmt (c C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (B1w N s ∩ openCube N ∩ {w | ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 →
      phi (flipP s w) s S < c * betaW w}) ≤ ENNReal.ofReal (Real.exp (-(C * N)))

/-- The strong rate used by the D-leaves. -/
noncomputable def RfD : ℝ := 102 / 100

/-! ### Superexponential events: half-means, `Z` -/

/-- The half-mean event (all rows `t`, all columns `j`). -/
def dtHalfBad (N : ℕ) : Set (Param N) := {w | ∃ t j, (1 / ((N : ℝ) + 1)) < |faColMean w t j - 1 / 2|}

lemma dt_cube_bound : ∀ᶠ N : ℕ in atTop, 4 * (N : ℝ) * ((N : ℝ) + 1) ^ 2 ≤ 2 ^ N := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt 3 (by norm_num : (1 : ℝ) < 2))
  filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)), eventually_ge_atTop 1]
    with N hN h1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h1
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  rw [div_lt_iff₀ h2] at hN
  have hsq : ((N : ℝ) + 1) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith
  have : 4 * (N : ℝ) * ((N : ℝ) + 1) ^ 2 ≤ 16 * (N : ℝ) ^ 3 := by nlinarith
  nlinarith

theorem dt_half_all : ∀ᶠ N : ℕ in atTop, cubeM N (dtHalfBad N) ≤ ENNReal.ofReal (Real.exp (-(2 * N))) := by
  filter_upwards [dt_cube_bound, eventually_ge_atTop 1] with N hb h1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h1
  have hset : dtHalfBad N =
      ⋃ p : State N × Fin N, {w | (1 / ((N : ℝ) + 1)) < |faColMean w p.1 p.2 - 1 / 2|} := by
    ext w; simp only [dtHalfBad, Set.mem_setOf_eq, Set.mem_iUnion, Prod.exists]
  rw [hset]
  have hc : ((Fintype.card (State N × Fin N) : ℕ) : ℝ) = (2 : ℝ) ^ N * N := by
    rw [Fintype.card_prod, Fintype.card_fin, show Fintype.card (State N) = 2 ^ N by simp]
    push_cast; ring
  have hδ : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  have hU := cubeM_iUnion_le (fun p : State N × Fin N =>
    {w : Param N | (1 / ((N : ℝ) + 1)) < |faColMean w p.1 p.2 - 1 / 2|})
    (fun p => fa_col_dev h1 p.1 p.2 hδ)
  refine hU.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hc]
  have hp1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hk : 4 * (N : ℝ) ≤ 2 ^ N * (1 / ((N : ℝ) + 1)) ^ 2 := by
    rw [div_pow, one_pow, mul_one_div, le_div_iff₀ (by positivity)]; linarith
  have hE : Real.exp (-(2 ^ N * (1 / ((N : ℝ) + 1)) ^ 2)) ≤ Real.exp (-(4 * N)) :=
    Real.exp_le_exp.2 (by linarith)
  have h2e : (2 : ℝ) ^ N ≤ Real.exp N := by
    have : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    calc (2 : ℝ) ^ N ≤ Real.exp 1 ^ N := pow_le_pow_left₀ (by norm_num) this N
      _ = Real.exp N := by rw [← Real.exp_nat_mul]; ring_nf
  have hq : 2 * (N : ℝ) ≤ Real.exp N := by
    have := Real.quadratic_le_exp_of_nonneg (x := (N : ℝ)) (by positivity)
    nlinarith
  calc (2 : ℝ) ^ N * N * (2 * Real.exp (-(2 ^ N * (1 / ((N : ℝ) + 1)) ^ 2)))
      = (2 : ℝ) ^ N * (2 * N) * Real.exp (-(2 ^ N * (1 / ((N : ℝ) + 1)) ^ 2)) := by ring
    _ ≤ Real.exp N * Real.exp N * Real.exp (-(4 * N)) := by gcongr
    _ = Real.exp (-(2 * N)) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- The `Z` event. -/
def dtZBad (N : ℕ) : Set (Param N) := {w | ¬ (1 / 2 < Zs w ∧ Zs w < 13)}

theorem dt_Zs_bad : ∀ᶠ N : ℕ in atTop, cubeM N (dtZBad N) ≤ ENNReal.ofReal (Real.exp (-(14 / 10 * N))) := by
  have hlim : Tendsto (fun N : ℕ => 2 * Real.exp (1 - (N : ℝ) / 20)) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => (1 : ℝ) - (N : ℝ) / 20) atTop atBot := by
      have h := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (by norm_num : (0 : ℝ) < 20)
      exact tendsto_atBot_add_const_left _ 1 (tendsto_neg_atTop_atBot.comp h) |>.congr
        (fun N => by simp; ring)
    simpa using (Real.tendsto_exp_atBot.comp this).const_mul 2
  filter_upwards [fa_small_lo, fa_small_hi,
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N h1 h2 h3
  have hsub : dtZBad N ⊆ {w | Zs w ≤ 1 / 2} ∪ {w | 13 ≤ Zs w} := by
    intro w hw
    simp only [dtZBad, Set.mem_setOf_eq, not_and_or, not_lt] at hw
    rcases hw with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have b1 := cubeM_Zs_le_half (N := N) (t := 3 * N) (by positivity)
  have b2 := cubeM_Zs_ge_13 (N := N) (t := N / 4) (by positivity)
  calc cubeM N (dtZBad N)
      ≤ cubeM N {w | Zs w ≤ 1 / 2} + cubeM N {w | 13 ≤ Zs w} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (Real.exp (1 - 3 * N / 2)) + ENNReal.ofReal (Real.exp (1 - 3 * N / 2)) := by
        gcongr
        · refine b1.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
          linarith
        · refine b2.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
          linarith
    _ = ENNReal.ofReal (2 * Real.exp (1 - 3 * N / 2)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]; congr 1; ring
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have e : Real.exp (1 - 3 * N / 2) = Real.exp (1 - (N : ℝ) / 20) * Real.exp (-(14 / 10 * N)) *
            Real.exp (-(1 / 20 * (N : ℝ))) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        rw [e]
        have hx := Real.exp_pos (-(14 / 10 * (N : ℝ)))
        have hy : Real.exp (-(1 / 20 * (N : ℝ))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        have hz := Real.exp_pos (1 - (N : ℝ) / 20)
        have hy0 := Real.exp_pos (-(1 / 20 * (N : ℝ)))
        nlinarith [mul_le_mul_of_nonneg_left hy (mul_nonneg hz.le hx.le)]

/-! ### The deterministic single-cut bounds for `univ` -/

lemma dt_ratio_le {y q δ : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1) (hq : |q - 1 / 2| ≤ δ) (hδ : δ ≤ 1 / 4) :
    pos (Real.logb 2 (y / q)) ≤ 2 := by
  have hq0 : 1 / 4 ≤ q := by have := (abs_le.1 hq).1; linarith
  have hqp : 0 < q := by linarith
  refine max_le (by norm_num) ?_
  refine logb_two_le_two_of_le_four (div_nonneg hy0 hqp.le) ?_
  rw [div_le_iff₀ hqp]; linarith

/-- **Cause side**: with all half-means regular, `φ_s(U) ≤ 2 N β`. -/
theorem dt_phi_univ_le_beta (hN : 3 ≤ N) {s : State N} {w : Param N} (hw : w ∈ openCube N)
    (hhalf : w ∉ dtHalfBad N) :
    phi (flipP s w) s univ ≤ N * (betaW w * 2) := by
  have hz : flipP s w ∈ openCube N := flipP_mem_openCube hw
  have hzw : flipP s (flipP s w) = w := flipP_invol s w
  have hS : 2 ≤ (univ : Finset (Fin N)).card := by rw [card_univ, Fintype.card_fin]; omega
  have j : Fin N := ⟨0, by omega⟩
  have hβ0 : 0 ≤ betaW w := betaW_nonneg w
  have hδ : 1 / ((N : ℝ) + 1) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have h := phi_le_cause hz (S := univ) (s := s) hS (mem_univ j) (B := betaW w * 2) (by positivity) ?_
  · simpa [card_univ, Fintype.card_fin] using h
  intro tc
  rw [sysBackCause_univ_eq hz, hzw, Num_univ_eq, Num_univ_eq, cmean_univ, cmean_single_eq,
    mul_div_mul_right _ _ (b1_Zs_pos hw).ne']
  have hb : Pw w tc / Zs w ≤ betaW w :=
    div_le_div_of_nonneg_right (Pw_le_tcRow w tc) (b1_Zs_pos hw).le
  have hq : |faColMean w tc j - 1 / 2| ≤ 1 / ((N : ℝ) + 1) := by
    by_contra hc; exact hhalf ⟨tc, j, not_le.1 hc⟩
  have hr := dt_ratio_le (y := clamp01 (w tc j)) (clamp01_nonneg _) (clamp01_le_one _) hq hδ
  have hpos : 0 ≤ pos (Real.logb 2 (clamp01 (w tc j) / faColMean w tc j)) := le_max_left _ _
  calc Pw w tc / Zs w * pos (Real.logb 2 (clamp01 (w tc j) / faColMean w tc j))
      ≤ betaW w * pos (Real.logb 2 (clamp01 (w tc j) / faColMean w tc j)) :=
        mul_le_mul_of_nonneg_right hb hpos
    _ ≤ betaW w * 2 := mul_le_mul_of_nonneg_left hr hβ0

/-- `qW` at `S = univ` is a column half-mean or its complement. -/
lemma dt_qW_univ (hN : 1 ≤ N) (w : Param N) (s : State N) (j : Fin N) (b : Bool) :
    |qW w s univ j b - 1 / 2| = |faColMean w s j - 1 / 2| := by
  have hM : (univ.erase j)ᶜ = ({j} : Finset (Fin N)) := by ext i; simp
  have hc : (((agree {j} s).card : ℕ) : ℝ) = (2 : ℝ) ^ (N - 1) := by
    rw [card_agree, card_singleton]; push_cast; ring
  unfold qW
  rw [hM, card_univ, Fintype.card_fin]
  split_ifs
  · rfl
  · rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, hc]
    unfold faColMean
    have h2 : (0 : ℝ) < 2 ^ (N - 1) := by positivity
    rw [show ((2 : ℝ) ^ (N - 1) - ∑ r ∈ agree {j} s, clamp01 (w r j)) / 2 ^ (N - 1) - 1 / 2 =
        -((∑ r ∈ agree {j} s, clamp01 (w r j)) / 2 ^ (N - 1) - 1 / 2) by field_simp; ring, abs_neg]

/-- **Effect side**: with all half-means regular, `φ_s(U) ≤ 2 N e`. -/
theorem dt_phi_univ_le_e (hN : 3 ≤ N) {s : State N} {w : Param N} (hw : w ∈ openCube N)
    (hhalf : w ∉ dtHalfBad N) :
    phi (flipP s w) s univ ≤ 2 * N * eE w s := by
  have hz : flipP s w ∈ openCube N := flipP_mem_openCube hw
  have hzw : flipP s (flipP s w) = w := flipP_invol s w
  have hS : 2 ≤ (univ : Finset (Fin N)).card := by rw [card_univ, Fintype.card_fin]; omega
  have j : Fin N := ⟨0, by omega⟩
  have hδ : 1 / ((N : ℝ) + 1) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hq : ∀ b, 1 / 4 ≤ qW (flipP s (flipP s w)) s univ j b := by
    intro b
    rw [hzw]
    have h1 := dt_qW_univ (by omega) w s j b
    have h2 : |faColMean w s j - 1 / 2| ≤ 1 / ((N : ℝ) + 1) := by
      by_contra hc; exact hhalf ⟨s, j, not_le.1 hc⟩
    have := (abs_le.1 (h1 ▸ h2.trans hδ)).1
    linarith
  have h := phi_le_eff hz hS (mem_univ j) hq
  rw [hzw, card_univ, Fintype.card_fin, Nat.sub_self, pow_zero, one_mul, ← eE_eq_Mrow] at h
  linarith

/-! ### The B1 competitor inequality -/

/-- On B1 every proper nonempty candidate has `φ_s` below `φ_s(U)`. -/
lemma dt_B1_lt {s : State N} {w : Param N} (hB : w ∈ B1w N s) {S : Finset (Fin N)} (hS : S.Nonempty)
    (hne : S ≠ univ) : phi (flipP s w) s S < phi (flipP s w) s univ := by
  obtain ⟨-, hC⟩ := hB
  exact hC.2 S (subset_univ _) hne (by simpa using hS)

lemma dt_card_ne_univ {S : Finset (Fin N)} {k : ℕ} (hS : S.card ≤ k) (hk : k < N) : S ≠ univ := by
  intro h; rw [h, card_univ, Fintype.card_fin] at hS; omega

/-! ### Leaf 4: tilt -/

lemma dt_slT_exp (hN : 1 ≤ N) : Real.exp (-slT N) = 1 / ((N : ℝ) ^ 2 * Real.exp 20) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold slT
  rw [Real.exp_neg, Real.exp_add, show 2 * Real.log N = Real.log ((N : ℝ) ^ 2) by
    rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity), one_div]

/-- **Leaf 4, deterministic part**: off the half-mean and `Z` events, a tilt failure on B1 is an LT2 event. -/
theorem dt_tilt_det (hN : 3 ≤ N) {s : State N} {w : Param N} (hw : w ∈ bTilt N s)
    (hhalf : w ∉ dtHalfBad N) (hZ : w ∉ dtZBad N) :
    betaW w < 1 * sigN N ∧ ∀ S : Finset (Fin N), S.card = 2 → phi (flipP s w) s S < 3 * 1 * sigN N := by
  obtain ⟨⟨hB, ho⟩, hT⟩ := hw
  simp only [Set.mem_setOf_eq, not_le] at hT
  have hZ' : 1 / 2 < Zs w ∧ Zs w < 13 := by by_contra h; exact hZ h
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : ∀ i, 0 < clamp01 (w (tcRow w) i) := fun i => by
    rw [b1_clamp01_of_mem_Ioo (ho _ i)]; exact (ho _ i).1
  have hP : Pw w (tcRow w) < sigN N / ((N : ℝ) ^ 2 * Real.exp 20) := by
    rw [Pw_eq_exp_neg_XW hpos, sigN_eq_exp, div_eq_mul_one_div, ← dt_slT_exp (by omega), ← Real.exp_add]
    exact Real.exp_lt_exp.2 (by linarith)
  have hσ : 0 < sigN N := by rw [sigN_eq_exp]; exact Real.exp_pos _
  have hden : (1 : ℝ) ≤ (N : ℝ) ^ 2 * Real.exp 20 := by
    have : (1 : ℝ) ≤ Real.exp 20 := Real.one_le_exp (by norm_num)
    nlinarith
  have hβ : betaW w ≤ 2 * Pw w (tcRow w) := by
    unfold betaW
    rw [div_le_iff₀ (b1_Zs_pos ho)]
    have := Pw_nonneg w (tcRow w)
    nlinarith
  -- `2 N β < σ_N`
  have h2Nβ : (N : ℝ) * (betaW w * 2) < sigN N := by
    have h1 : (N : ℝ) * (betaW w * 2) ≤ 4 * N * Pw w (tcRow w) := by nlinarith [betaW_nonneg w]
    have h2 : 4 * (N : ℝ) * Pw w (tcRow w) < 4 * N * (sigN N / ((N : ℝ) ^ 2 * Real.exp 20)) := by
      have : (0 : ℝ) < 4 * N := by positivity
      exact mul_lt_mul_of_pos_left hP this
    have h3 : 4 * (N : ℝ) * (sigN N / ((N : ℝ) ^ 2 * Real.exp 20)) ≤ sigN N := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      have he : (4 : ℝ) ≤ N * Real.exp 20 := by
        have : (21 : ℝ) ≤ Real.exp 20 := by have := Real.add_one_le_exp (20 : ℝ); linarith
        nlinarith
      have hNσ : (0 : ℝ) ≤ N * sigN N := by positivity
      nlinarith [mul_le_mul_of_nonneg_left he hNσ]
    linarith
  refine ⟨?_, fun S hS => ?_⟩
  · have : betaW w * 2 ≤ (N : ℝ) * (betaW w * 2) := by
      have := betaW_nonneg w; nlinarith
    linarith
  · have hne : S.Nonempty := by rw [← card_pos]; omega
    have hlt := dt_B1_lt hB hne (dt_card_ne_univ (le_of_eq hS) (by omega))
    have hU := dt_phi_univ_le_beta (s := s) (by omega) ho hhalf
    linarith

/-- **Leaf 4, strong form** (rate `RfD = 1.02`), from LT2 at `L = 1`, `C = RfD`. -/
theorem leaf4_strong (hLT : LT2Stmt 1 RfD) : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bTilt N s) ≤ ENNReal.ofReal (3 * Real.exp (-(RfD * N))) := by
  filter_upwards [hLT, dt_half_all, dt_Zs_bad, eventually_ge_atTop 3] with N hL hH hZ hN s
  have hsub : bTilt N s ⊆ dtHalfBad N ∪ dtZBad N ∪
      {w | betaW w < 1 * sigN N ∧ ∀ S : Finset (Fin N), S.card = 2 → phi (flipP s w) s S < 3 * 1 * sigN N} := by
    intro w hw
    by_cases h1 : w ∈ dtHalfBad N
    · exact Or.inl (Or.inl h1)
    by_cases h2 : w ∈ dtZBad N
    · exact Or.inl (Or.inr h2)
    exact Or.inr (dt_tilt_det hN hw h1 h2)
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have he : Real.exp (-(2 * N)) ≤ Real.exp (-(RfD * N)) := Real.exp_le_exp.2 (by unfold RfD; nlinarith)
  have he' : Real.exp (-(14 / 10 * N)) ≤ Real.exp (-(RfD * N)) := Real.exp_le_exp.2 (by unfold RfD; nlinarith)
  calc cubeM N (bTilt N s)
      ≤ cubeM N (dtHalfBad N) + cubeM N (dtZBad N) + cubeM N {w | betaW w < 1 * sigN N ∧
          ∀ S : Finset (Fin N), S.card = 2 → phi (flipP s w) s S < 3 * 1 * sigN N} :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
    _ ≤ ENNReal.ofReal (Real.exp (-(RfD * N))) + ENNReal.ofReal (Real.exp (-(RfD * N))) +
          ENNReal.ofReal (Real.exp (-(RfD * N))) := by
        gcongr
        · exact hH.trans (ENNReal.ofReal_le_ofReal he)
        · exact hZ.trans (ENNReal.ofReal_le_ofReal he')
        · exact hL s
    _ = ENNReal.ofReal (3 * Real.exp (-(RfD * N))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
          ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
        ring_nf

/-- `3 e^{-1.02 N} ≤ e^{-RfF N}` eventually (any constant). -/
lemma dt_absorb (K : ℝ) : ∀ᶠ N : ℕ in atTop, K * Real.exp (-(RfD * N)) ≤ Real.exp (-(RfF * N)) := by
  have ht : Tendsto (fun N : ℕ => Real.exp (-((RfD - RfF) * N))) atTop (𝓝 0) := by
    have hpos : 0 < RfD - RfF := by unfold RfD RfF; norm_num
    apply Real.tendsto_exp_atBot.comp
    apply tendsto_neg_atTop_atBot.comp
    exact (tendsto_natCast_atTop_atTop).const_mul_atTop hpos
  filter_upwards [(ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (|K| + 1))))] with N hN
  have e : Real.exp (-(RfD * N)) = Real.exp (-((RfD - RfF) * N)) * Real.exp (-(RfF * N)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  have h1 := Real.exp_pos (-(RfF * N))
  have h2 := Real.exp_pos (-((RfD - RfF) * N))
  have hK : K ≤ |K| := le_abs_self K
  have : (|K| + 1) * Real.exp (-((RfD - RfF) * N)) < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hN; linarith
  nlinarith [abs_nonneg K, mul_le_mul_of_nonneg_right hK (mul_nonneg h2.le h1.le)]

/-- **Leaf 4 (`bTilt`)**, from Lemma LT2 (`L = 1`, `C = 1.02`). -/
theorem leaf4_of_LT2 (hLT : LT2Stmt 1 RfD) : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (forcedBad N s 4) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [leaf4_strong hLT, dt_absorb 3] with N h ha s
  exact (h s).trans (ENNReal.ofReal_le_ofReal ha)

/-! ### Leaf 5: link -/

/-- **Leaf 5, deterministic part**: off the half-mean and `Z` events, a link failure on B1 makes every pair and
triple fall below `β/4`. -/
theorem dt_link_det (hN : 4 ≤ N) {s : State N} {w : Param N} (hw : w ∈ bLink N s)
    (hhalf : w ∉ dtHalfBad N) (hZ : w ∉ dtZBad N) :
    w ∈ B1w N s ∩ openCube N ∩ {w | ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 →
      phi (flipP s w) s S < 1 / 4 * betaW w} := by
  obtain ⟨⟨hB, ho⟩, hL⟩ := hw
  refine ⟨⟨hB, ho⟩, fun S hS2 hS3 => ?_⟩
  simp only [Set.mem_setOf_eq, not_le] at hL
  have hZ' : 1 / 2 < Zs w ∧ Zs w < 13 := by by_contra h; exact hZ h
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : ∀ i, 0 < clamp01 (w (tcRow w) i) := fun i => by
    rw [b1_clamp01_of_mem_Ioo (ho _ i)]; exact (ho _ i).1
  have hxE : ∀ k, 0 < xE w s k := xE_pos w s
  -- `log e = -Σ -log x_k`
  have hlogE : Real.log (eE w s) = -∑ k, -Real.log (xE w s k) := by
    unfold eE; rw [Real.log_prod (fun k _ => (hxE k).ne')]; simp
  have hβ : betaW w = Real.exp (-XW w (tcRow w)) / Zs w := by
    unfold betaW; rw [Pw_eq_exp_neg_XW hpos]
  -- `e < β/(8N)`
  have he : eE w s < betaW w / (8 * N) := by
    have hlt : Real.log (eE w s) < -XW w (tcRow w) - slT N := by rw [hlogE]; linarith
    have h1 : eE w s < Real.exp (-XW w (tcRow w) - slT N) := by
      rw [← Real.exp_log (eE_pos w s)]; exact Real.exp_lt_exp.2 hlt
    refine h1.trans_le ?_
    rw [hβ, sub_eq_add_neg, Real.exp_add, dt_slT_exp (by omega), div_div]
    have hE := Real.exp_pos (-XW w (tcRow w))
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (mul_pos (b1_Zs_pos ho) (by positivity))]
    have h20 : (104 : ℝ) ≤ Real.exp 20 := by
      have := Real.add_one_le_exp 20
      have h4 : (21 : ℝ) ^ 2 / 2 ≤ Real.exp 20 - 21 + 1 + 20 := by
        have := Real.quadratic_le_exp_of_nonneg (x := (20 : ℝ)) (by norm_num); linarith
      linarith
    have : Zs w * (8 * N) ≤ (N : ℝ) ^ 2 * Real.exp 20 := by nlinarith
    exact mul_le_mul_of_nonneg_left this hE.le
  have hne : S.Nonempty := by rw [← card_pos]; omega
  have hlt := dt_B1_lt hB hne (dt_card_ne_univ hS3 (by omega))
  have hU := dt_phi_univ_le_e (s := s) (by omega) ho hhalf
  have : 2 * (N : ℝ) * eE w s < 2 * N * (betaW w / (8 * N)) := by
    have : (0 : ℝ) < 2 * N := by positivity
    exact mul_lt_mul_of_pos_left he this
  have e2 : 2 * (N : ℝ) * (betaW w / (8 * N)) = 1 / 4 * betaW w := by field_simp; ring
  linarith

/-- **Leaf 5, strong form** (rate `RfD = 1.02`), from the pair/triple level bound at `c = 1/4`. -/
theorem leaf5_strong (hLT : LTBetaStmt (1 / 4) RfD) : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bLink N s) ≤ ENNReal.ofReal (3 * Real.exp (-(RfD * N))) := by
  filter_upwards [hLT, dt_half_all, dt_Zs_bad, eventually_ge_atTop 4] with N hL hH hZ hN s
  set Ev := B1w N s ∩ openCube N ∩ {w | ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 →
      phi (flipP s w) s S < 1 / 4 * betaW w}
  have hsub : bLink N s ⊆ dtHalfBad N ∪ dtZBad N ∪ Ev := by
    intro w hw
    by_cases h1 : w ∈ dtHalfBad N
    · exact Or.inl (Or.inl h1)
    by_cases h2 : w ∈ dtZBad N
    · exact Or.inl (Or.inr h2)
    exact Or.inr (dt_link_det hN hw h1 h2)
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have he : Real.exp (-(2 * N)) ≤ Real.exp (-(RfD * N)) := Real.exp_le_exp.2 (by unfold RfD; nlinarith)
  have he' : Real.exp (-(14 / 10 * N)) ≤ Real.exp (-(RfD * N)) := Real.exp_le_exp.2 (by unfold RfD; nlinarith)
  calc cubeM N (bLink N s)
      ≤ cubeM N (dtHalfBad N) + cubeM N (dtZBad N) + cubeM N Ev :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
    _ ≤ ENNReal.ofReal (Real.exp (-(RfD * N))) + ENNReal.ofReal (Real.exp (-(RfD * N))) +
          ENNReal.ofReal (Real.exp (-(RfD * N))) := by
        gcongr
        · exact hH.trans (ENNReal.ofReal_le_ofReal he)
        · exact hZ.trans (ENNReal.ofReal_le_ofReal he')
        · exact hL s
    _ = ENNReal.ofReal (3 * Real.exp (-(RfD * N))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
          ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
        ring_nf

/-- **Leaf 5 (`bLink`)**, from the pair/triple level bound (`c = 1/4`, `C = 1.02`). -/
theorem leaf5_of_LTBeta (hLT : LTBetaStmt (1 / 4) RfD) : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (forcedBad N s 5) ≤ ENNReal.ofReal (Real.exp (-(RfF * N))) := by
  filter_upwards [leaf5_strong hLT, dt_absorb 3] with N h ha s
  exact (h s).trans (ENNReal.ofReal_le_ofReal ha)

end Census
end IIT
