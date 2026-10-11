/-
Census, B1 LTBetaHi, gap G4: the `4/5` floor on `Top` (`rl_sym_full` needs `G1 ≥ 4/5`, RL-tc needs `x ≥ 4/5`,
`lt3WQ_floor` needs `b1YTopR w tc ε ≥ 4/5`).

The floor is DETERMINISTIC once `Zs ≥ 1/2` (any fixed `L > 0`, `N` large; B1 and `openCube` are not used):
if fewer than `⌈N/21⌉₊` entries of `tc` were `≥ 4/5`, then `P(tc) ≤ (4/5)^{N+1-⌈N/21⌉₊} ≤ e^{-(20/21)·0.2218·N}`,
while `P(tc) = β·Zs ≥ Lσ_N/2 = (L/2) e^{-x0 N}`, `x0 < 0.2029`. The margin is `0.0083 N`.
The exception `Zs ≤ 1/2` has probability `≤ e^{1 - 3N/2} ≤ e^{-1.4N}` (`cubeM_Zs_le_half`, `t = 3N`).
Margin of the constants: at `ε = 1/21` a floor `c` is reachable iff `(20/21) log(1/c) > x0`, i.e. `c < 0.808`.

* generic core: `flr_Pw_le` (any row, `ε`, floor `c ∈ [0,1]`), `flr_of_beta` (any `z0 ≤ Zs`, any `L`);
* `flr_floor` (deterministic, eventually), `flr_floor_bad` (probability `≤ e^{-1.4N}` on the LT3 band);
* `LT3HiFlStmt` (the LT3 band with `Zs ≥ 1/2` and the floor added) and `lt3Hi_of_floor`, `ltBetaHi_of_LT3Fl`;
* for T7: `flr_Pw_gt` (`P(tc) > e^{-3N/10}`), `lt3WQ_floor_ev`, `lt3WSel_of_floor` (`Sel = WF × Base`).
-/
import IIT.Census.B1LTHiSplit
import IIT.Census.B1LTHiWin2
import IIT.Census.B1ForcedAZs

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-! ### The deterministic core (generic in `ε`, the floor `c` and the row) -/

/-- **Few entries above the floor force a small row product**: if the `⌈εN⌉₊`-th largest entry of row `r` is
`< c` (`0 ≤ c ≤ 1`), at least `N + 1 - ⌈εN⌉₊` entries are `< c`, so `P(r) ≤ c^{N + 1 - ⌈εN⌉₊}`. -/
lemma flr_Pw_le (w : Param N) (r : State N) {ε c : ℝ} (hk : 1 ≤ ⌈ε * N⌉₊) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (h : b1YTopR w r ε < c) : Pw w r ≤ c ^ (N + 1 - ⌈ε * N⌉₊) := by
  set f : Fin N → ℝ := fun i => clamp01 (w r i) with hf
  have hlt := b1Kth_lt_count (f := f) hk
  have hY : b1Kth f ⌈ε * N⌉₊ < c := h
  have hsub : (univ.filter fun j => ¬ f j < c) ⊆ univ.filter fun j => b1Kth f ⌈ε * N⌉₊ < f j := by
    intro j hj
    simp only [mem_filter, mem_univ, true_and, not_lt] at hj ⊢
    linarith
  have hsplit : (univ.filter fun j => f j < c).card + (univ.filter fun j => ¬ f j < c).card =
      (univ : Finset (Fin N)).card := card_filter_add_card_filter_not _
  rw [card_univ, Fintype.card_fin] at hsplit
  have hcard : N + 1 - ⌈ε * N⌉₊ ≤ (univ.filter fun j => f j < c).card := by
    have := card_le_card hsub
    omega
  have hprod : Pw w r = (∏ j ∈ univ.filter fun j => f j < c, f j) * ∏ j ∈ univ.filter fun j => ¬ f j < c, f j :=
    (prod_filter_mul_prod_filter_not univ (fun j => f j < c) f).symm
  have h1 : ∏ j ∈ univ.filter fun j => ¬ f j < c, f j ≤ 1 :=
    prod_le_one (fun j _ => clamp01_nonneg _) fun j _ => clamp01_le_one _
  have h2 : ∏ j ∈ univ.filter fun j => f j < c, f j ≤ c ^ (univ.filter fun j => f j < c).card := by
    rw [← prod_const]
    exact prod_le_prod (fun j _ => clamp01_nonneg _) fun j hj => (mem_filter.1 hj).2.le
  have h0 : 0 ≤ ∏ j ∈ univ.filter fun j => f j < c, f j := prod_nonneg fun j _ => clamp01_nonneg _
  have h3 : c ^ (univ.filter fun j => f j < c).card ≤ c ^ (N + 1 - ⌈ε * N⌉₊) :=
    pow_le_pow_of_le_one hc0 hc1 hcard
  rw [hprod]
  calc _ ≤ (∏ j ∈ univ.filter fun j => f j < c, f j) * 1 := mul_le_mul_of_nonneg_left h1 h0
    _ ≤ _ := by rw [mul_one]; exact h2.trans h3

/-- **The floor from the tilt** (deterministic, generic): if `z0 ≤ Zs`, `Lσ_N ≤ β` and
`c^{N + 1 - ⌈εN⌉₊} < L z0 σ_N`, then `y_top(tc, ε) ≥ c`. -/
theorem flr_of_beta {w : Param N} {ε c L z0 : ℝ} (hk : 1 ≤ ⌈ε * N⌉₊) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hz0 : 0 < z0) (hZ : z0 ≤ Zs w) (hβ : L * sigN N ≤ betaW w)
    (hnum : c ^ (N + 1 - ⌈ε * N⌉₊) < L * z0 * sigN N) : c ≤ b1YTopR w (tcRow w) ε := by
  by_contra h
  push Not at h
  have hP := flr_Pw_le w (tcRow w) hk hc0 hc1 h
  have hZpos : 0 < Zs w := lt_of_lt_of_le hz0 hZ
  have hβZ : betaW w * Zs w = Pw w (tcRow w) := by unfold betaW; exact div_mul_cancel₀ _ hZpos.ne'
  have e1 : L * sigN N * z0 ≤ betaW w * z0 := mul_le_mul_of_nonneg_right hβ hz0.le
  have e2 : betaW w * z0 ≤ betaW w * Zs w := mul_le_mul_of_nonneg_left hZ (betaW_nonneg w)
  linarith

/-! ### The numeric step at `ε = 1/21`, `c = 4/5`, `z0 = 1/2` -/

/-- `log (4/5) < -(8/25) log 2` (`(4/5)^25 < 2^{-8}`). -/
lemma flr_log_four_fifths : Real.log (4 / 5) < -(8 / 25 * Real.log 2) := by
  have h1 : ((4 : ℝ) / 5) ^ 25 < (1 / 2) ^ 8 := by norm_num
  have h2 := Real.log_lt_log (by positivity) h1
  rw [Real.log_pow, Real.log_pow, one_div, Real.log_inv] at h2
  push_cast at h2
  linarith

/-- `L σ_N / 2 = e^{log L - log 2 - x0 N}`. -/
lemma flr_sig_eq {L : ℝ} (hL : 0 < L) (N : ℕ) :
    L * (1 / 2) * sigN N = Real.exp (Real.log L - Real.log 2 - x0 * N) := by
  rw [sigN_eq_exp, Real.exp_sub, Real.exp_sub, Real.exp_log hL, Real.exp_log (by norm_num : (0 : ℝ) < 2),
    Real.exp_neg]
  ring

/-- **The numeric step**: for any `L > 0`, eventually `1 ≤ ⌈N/21⌉₊` and `(4/5)^{N + 1 - ⌈N/21⌉₊} < (L/2) σ_N`
(`(20/21)(8/25) log 2 ≥ 0.2112 > x0 + 0.008`). -/
lemma flr_num {L : ℝ} (hL : 0 < L) : ∀ᶠ N : ℕ in atTop,
    1 ≤ ⌈(1 / 21 : ℝ) * N⌉₊ ∧ ((4 : ℝ) / 5) ^ (N + 1 - ⌈(1 / 21 : ℝ) * N⌉₊) < L * (1 / 2) * sigN N := by
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈200 * (Real.log 2 - Real.log L)⌉₊]
    with N h1 hNL
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast h1
  have hNL' : 200 * (Real.log 2 - Real.log L) ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNL)
  have hk1 : 1 ≤ ⌈(1 / 21 : ℝ) * N⌉₊ :=
    Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (mul_pos (by norm_num) (by linarith))).ne'
  refine ⟨hk1, ?_⟩
  set k := ⌈(1 / 21 : ℝ) * N⌉₊ with hk
  have hkr : (k : ℝ) < 1 / 21 * N + 1 := Nat.ceil_lt_add_one (by positivity)
  have hkN : k ≤ N + 1 := by
    have : (k : ℝ) < ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact (Nat.cast_lt.1 this).le
  have hmr : ((N + 1 - k : ℕ) : ℝ) = N + 1 - k := by rw [Nat.cast_sub hkN]; push_cast; ring
  have hm20 : 20 / 21 * (N : ℝ) ≤ ((N + 1 - k : ℕ) : ℝ) := by rw [hmr]; linarith
  have e1 : ((4 : ℝ) / 5) ^ (N + 1 - k) = Real.exp (((N + 1 - k : ℕ) : ℝ) * Real.log (4 / 5)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [e1, flr_sig_eq hL N]
  refine Real.exp_lt_exp.2 ?_
  have hl := flr_log_four_fifths
  have hl0 : Real.log (4 / 5) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have p1 : ((N + 1 - k : ℕ) : ℝ) * Real.log (4 / 5) ≤ 20 / 21 * (N : ℝ) * Real.log (4 / 5) :=
    mul_le_mul_of_nonpos_right hm20 hl0.le
  have p2 : 20 / 21 * (N : ℝ) * Real.log (4 / 5) ≤ 20 / 21 * (N : ℝ) * (-(8 / 25 * Real.log 2)) :=
    mul_le_mul_of_nonneg_left hl.le (by positivity)
  have hl2 := Real.log_two_gt_d9
  norm_num at hl2
  have p3 : 6931471803 / 10000000000 * (N : ℝ) ≤ Real.log 2 * N :=
    mul_le_mul_of_nonneg_right hl2.le (by positivity)
  have p4 : x0 * N ≤ 2029 / 10000 * N := mul_le_mul_of_nonneg_right x0_lt.le (by positivity)
  linarith

/-! ### The floor: deterministic and probability forms -/

/-- **G4, deterministic form**: for any `L > 0`, eventually, `Zs ≥ 1/2` and `Lσ_N ≤ β` force
`b1YTopR w tc (1/21) ≥ 4/5` (no B1, no open cube needed). -/
theorem flr_floor {L : ℝ} (hL : 0 < L) : ∀ᶠ N : ℕ in atTop, ∀ w : Param N,
    1 / 2 ≤ Zs w → L * sigN N ≤ betaW w → 4 / 5 ≤ b1YTopR w (tcRow w) (1 / 21) := by
  filter_upwards [flr_num hL] with N hN w hZ hβ
  exact flr_of_beta hN.1 (by norm_num) (by norm_num) (by norm_num) hZ hβ hN.2

/-- `P(Zs ≤ 1/2) ≤ e^{-1.4N}` eventually (`cubeM_Zs_le_half` at `t = 3N`). -/
lemma flr_Zs_low : ∀ᶠ N : ℕ in atTop,
    cubeM N {w : Param N | Zs w ≤ 1 / 2} ≤ ENNReal.ofReal (Real.exp (-(14 / 10 * N))) := by
  filter_upwards [fa_small_lo, eventually_ge_atTop 10] with N h1 h10
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN10 : (10 : ℝ) ≤ N := by exact_mod_cast h10
  refine (cubeM_Zs_le_half (N := N) (t := 3 * N) (by positivity)).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  linarith

/-- **G4, probability form**: for any `L > 0`, eventually, for every `s`, the floor `b1YTopR w tc (1/21) ≥ 4/5`
fails on `B1 ∩ openCube ∩ {Lσ_N ≤ β}` with probability `≤ e^{-1.4N}`. -/
theorem flr_floor_bad {L : ℝ} (hL : 0 < L) : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (B1w N s ∩ openCube N ∩ {w | L * sigN N ≤ betaW w ∧ b1YTopR w (tcRow w) (1 / 21) < 4 / 5}) ≤
      ENNReal.ofReal (Real.exp (-(14 / 10 * N))) := by
  filter_upwards [flr_floor hL, flr_Zs_low] with N hF hZ s
  refine (measure_mono ?_).trans hZ
  rintro w ⟨-, hβ, hlt⟩
  show Zs w ≤ 1 / 2
  by_contra hZw
  exact absurd (hF w (not_le.1 hZw).le hβ) (not_le.2 hlt)

/-! ### The LT3 band with the floor -/

/-- **The LT3 band with `Zs ≥ 1/2` and the floor** (what T7 has to prove). -/
def LT3HiFlStmt (L C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (B1w N s ∩ openCube N ∩ {w | L * sigN N ≤ betaW w ∧ 1 / 2 ≤ Zs w ∧
      4 / 5 ≤ b1YTopR w (tcRow w) (1 / 21) ∧
      ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 1 / 4 * betaW w}) ≤
      ENNReal.ofReal (Real.exp (-(C * N)))

/-- **`Zs ≥ 1/2` and the floor may be assumed**: `LT3HiFlStmt L C₁ → LT3HiStmt L C` (`C < C₁`, `C < 1.4`). -/
theorem lt3Hi_of_floor {L C C₁ : ℝ} (hL : 0 < L) (h1 : C < C₁) (h2 : C < 14 / 10)
    (hFl : LT3HiFlStmt L C₁) : LT3HiStmt L C := by
  filter_upwards [hFl, flr_Zs_low, flr_floor hL, g_union_rate h1 h2] with N hA hB hF hU s
  refine (measure_mono ?_).trans (hU _ _ (hA s) hB)
  rintro w ⟨⟨hw, hcube⟩, hβ, hall⟩
  by_cases hZ : 1 / 2 ≤ Zs w
  · exact Or.inl ⟨⟨hw, hcube⟩, hβ, hZ, hF w hZ hβ, hall⟩
  · exact Or.inr (not_le.1 hZ).le

/-- **LTBetaHi from the floored LT3 band.** -/
theorem ltBetaHi_of_LT3Fl {L C₂ : ℝ} (hL : 1 ≤ L) (h2 : 104 / 100 < C₂) (hFl : LT3HiFlStmt L C₂) :
    LTBetaHiStmt (1 / 4) (104 / 100) := by
  set C := (104 / 100 + min C₂ (14 / 10)) / 2 with hC
  have hm := lt_min h2 (by norm_num : (104 / 100 : ℝ) < 14 / 10)
  have hC1 : C < C₂ := by have := min_le_left C₂ (14 / 10); linarith
  have hC2 : C < 14 / 10 := by have := min_le_right C₂ (14 / 10); linarith
  exact ltBetaHi_of_LT3 hL (by linarith) (lt3Hi_of_floor (by linarith) hC1 hC2 hFl)

/-! ### For T7: the selection is non-trivial on the floored band -/

/-- **`P(tc) > e^{-3N/10}`** eventually on `{Zs ≥ 1/2, Lσ_N ≤ β}` (first clause of `lt3WSel`). -/
theorem flr_Pw_gt {L : ℝ} (hL : 0 < L) : ∀ᶠ N : ℕ in atTop, ∀ w : Param N,
    1 / 2 ≤ Zs w → L * sigN N ≤ betaW w → Real.exp (-(3 / 10 * (N : ℝ))) < Pw w (tcRow w) := by
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈20 * (Real.log 2 - Real.log L)⌉₊]
    with N h1 hNL w hZ hβ
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast h1
  have hNL' : 20 * (Real.log 2 - Real.log L) ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNL)
  have hZpos : 0 < Zs w := lt_of_lt_of_le (by norm_num) hZ
  have hβZ : betaW w * Zs w = Pw w (tcRow w) := by unfold betaW; exact div_mul_cancel₀ _ hZpos.ne'
  have e1 : L * sigN N * (1 / 2) ≤ betaW w * (1 / 2) := mul_le_mul_of_nonneg_right hβ (by norm_num)
  have e2 : betaW w * (1 / 2) ≤ betaW w * Zs w := mul_le_mul_of_nonneg_left hZ (betaW_nonneg w)
  have hlow : L * (1 / 2) * sigN N ≤ Pw w (tcRow w) := by linarith
  refine lt_of_lt_of_le ?_ hlow
  rw [flr_sig_eq hL N]
  refine Real.exp_lt_exp.2 ?_
  have hl2 := Real.log_two_gt_d9
  norm_num at hl2
  have p4 : x0 * N ≤ 2029 / 10000 * N := mul_le_mul_of_nonneg_right x0_lt.le (by positivity)
  linarith

/-- **The floor on the windowed class**, eventually on `{Zs ≥ 1/2, Lσ_N ≤ β}` (`rl_sym_full`'s `hG1`). -/
theorem lt3WQ_floor_ev {L : ℝ} (hL : 0 < L) : ∀ᶠ N : ℕ in atTop, ∀ (s : State N) (γ : ℝ) (n : ℕ) (w : Param N),
    1 / 2 ≤ Zs w → L * sigN N ≤ betaW w → ∀ j ∈ lt3WQ s (1 / 21) γ n w, 4 / 5 ≤ clamp01 (w (tcRow w) j) := by
  filter_upwards [flr_floor hL] with N hF s γ n w hZ hβ
  exact lt3WQ_floor s (1 / 21) γ n w (Or.inr (hF w hZ hβ))

/-- **The selection is `WF × Base`** once its three clauses hold. -/
lemma lt3WSel_of_floor (s : State N) (ε γ : ℝ) (n : ℕ) {w : Param N}
    (hP : Real.exp (-(3 / 10 * (N : ℝ))) < Pw w (tcRow w)) (h7 : 7 ≤ (lt3WQ s ε γ n w).card)
    (hfl : ∀ j ∈ lt3WQ s ε γ n w, 4 / 5 ≤ clamp01 (w (tcRow w) j)) :
    lt3WSel s ε γ n w = lt3WF s ε γ n w ×ˢ lt3Base s w := by
  unfold lt3WSel
  exact ite_eq_left ⟨hP, h7, hfl⟩

/-- **The selection is `WF × Base` on the floored band** (`ε = 1/21`, eventually, given `|WQ| ≥ 7`). -/
theorem lt3WSel_of_floor_ev {L : ℝ} (hL : 0 < L) : ∀ᶠ N : ℕ in atTop,
    ∀ (s : State N) (γ : ℝ) (n : ℕ) (w : Param N), 1 / 2 ≤ Zs w → L * sigN N ≤ betaW w →
      7 ≤ (lt3WQ s (1 / 21) γ n w).card → lt3WSel s (1 / 21) γ n w = lt3WF s (1 / 21) γ n w ×ˢ lt3Base s w := by
  filter_upwards [flr_Pw_gt hL, lt3WQ_floor_ev hL] with N hP hF s γ n w hZ hβ h7
  exact lt3WSel_of_floor s (1 / 21) γ n (hP w hZ hβ) h7 (hF s γ n w hZ hβ)

end Census
end IIT
