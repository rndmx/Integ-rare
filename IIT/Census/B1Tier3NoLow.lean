/-
Census, B1 forced leaf 7: **Tier 3 without the field `lowE`** (W7 §1.1).

`lowE` (`λ^e_min ≥ 1/N²` at every maximal effect state) fails with polynomial probability, so it cannot be a rate
event. It is not needed for the bound `φ_s(U) ≤ β Fᶜ_j` (`NatTier3Stmt`): at a maximal effect state `te`
* either `N λ^e_min⁺ ≤ β λ^c_min`, and the single-cut competitor gives `φ(tc, te) ≤ N e λ^e_min⁺ ≤ β Fᶜ_j`;
* or `λ^e_min > β/(4N²)`, and Lemma G' holds with `d* = ⌊3N/5⌋`: the far deficit `(N-1)·3(δ_d + δ_{N-1})`,
  `d ≥ 3N/5`, is `O(N² 2^{-0.3N})`, below `β/(4N²)` because the tilt gives `β ≥ e^{-x₀N - slT}/13` and
  `0.3 ln 2 - x₀ ≥ 0.005`.

* `phiAt_le_N_kFE`  : the effect-side single-cut competitor bound at one pair `(tc, te)`.
* `t3n_far_num`     : the numerics (`2D ≤ ⌊3N/5⌋`, the far deficit against `e^{-x₀N - slT}/(52 N²)`).
* **`tier3_bound_noLow`** : deterministic, eventually in `N`: B1, open cube, `stateC`, `Tier3Rest6` (= `Tier3Rest4`
  without `lowE`), concentration, no exact tie, the tilt, `Zs < 13` and a pair/triple at `β/4` give
  `φ_s(U) ≤ β Fᶜ_j` for every `j`.
-/
import IIT.Census.B1ForcedGGlue
import IIT.Census.B1ForcedGLow
import IIT.Census.B1ForcedGNull
import IIT.Census.B1UnivSmallC2

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-! ### The residual event without `lowE` -/

/-- The effect fields of `EffRest4` without `lowE`. -/
structure EffRest6 (N : ℕ) (s : State N) (w : Param N) (te : State N) : Prop where
  spreadE : ∀ A' : Finset (Fin N), A'.card < 2 * DU N →
    5 * (DU N : ℝ) < ∑ j ∈ A'ᶜ, (kF (lamEz (flipP s w) s te) j - leMinAt s w te)
  smallE : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N →
    7 * (DU N : ℝ) < kM (lamEz (flipP s w) s te) (leMinAt s w te) K
  countE : 5 * (univ.filter fun j => kF (lamEz (flipP s w) s te) j - leMinAt s w te ≤ 1 / (N : ℝ)).card < N

/-- `Tier3Rest4` without `lowE`. -/
structure Tier3Rest6 (N : ℕ) (s : State N) (w : Param N) : Prop where
  mem_open : w ∈ openCube N
  spreadC : ∀ A' : Finset (Fin N), A'.card < 2 * DU N →
    5 * (DU N : ℝ) < ∑ j ∈ A'ᶜ, (kF (lamCz (flipP s w) s (tcRow w)) j - lcMin s w)
  smallC : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N →
    7 * (DU N : ℝ) < kM (lamCz (flipP s w) s (tcRow w)) (lcMin s w) K
  countC : 5 * (univ.filter fun j => kF (lamCz (flipP s w) s (tcRow w)) j - lcMin s w ≤ 1 / (N : ℝ)).card < N
  effW : EffRest6 N s w (teW w s)

/-- The residual statement without `lowE`. -/
def NatTier3Rest6Stmt (C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bNat N s ∩ {w | ¬ Tier3Rest6 N s w}) ≤ ENNReal.ofReal (Real.exp (-(C * N)))

/-! ### The effect-side single-cut competitor -/

lemma lamEz_empty {z : Param N} (hz : z ∈ openCube N) (s te : State N) (i : Fin N) :
    lamEz z s te i ∅ = 0 := by
  obtain ⟨m1, m2, m3, -, -⟩ := lamEz_means hz s te
  rw [m1, m2, div_self (m3 i).ne', Real.logb_one]

/-- **The effect single-cut bound at one pair**: `φ(tc, te) ≤ N e (Fᵉ_j)⁺`. -/
theorem phiAt_le_N_kFE (hN : 2 ≤ N) {z : Param N} (hz : z ∈ openCube N) (s tc te : State N) (j : Fin N) :
    sysPhiOfState (tpmOf z) univ s s tc te ≤
      N * (sysEffProb (tpmOf z) univ s s te * pos (kF (lamEz z s te) j)) := by
  have hr := hrest_of_two_le hN j
  refine (sysPhiOfState_le_card_mul _ univ s s _ _ (mem_univ j) hr).trans ?_
  rw [card_univ, Fintype.card_fin]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [univ_sysPhiAt_eq hz]
  refine (min_le_right _ _).trans (le_of_eq ?_)
  congr 2
  exact sum_profile_splitAt (lamEz z s te) (lamEz_empty hz s te) j hr

/-! ### Numerics -/

lemma t3n_gap : (1 / 200 : ℝ) ≤ 3 / 10 * Real.log 2 - x0 := by
  unfold x0
  have h1 : Real.log (256 / 243) = 3 * Real.log 2 - 5 * Real.log (3 / 2) := by
    rw [show (256 / 243 : ℝ) = 2 ^ 8 / 3 ^ 5 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_div (by norm_num) (by norm_num)]
    push_cast; ring
  have h2 : 1 - 1 / (256 / 243 : ℝ) ≤ Real.log (256 / 243) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 256 / 243 by norm_num)
    simpa [one_div] using this
  norm_num at h2
  linarith

/-- The far deficit at `d* = ⌊3N/5⌋`. -/
noncomputable def t3nQ (N : ℕ) : ℝ := ((N : ℝ) - 1) * (6 * dU N (3 * N / 5))

lemma t3n_far_num : ∀ᶠ N : ℕ in atTop, 64 ≤ N ∧ 2 * DU N ≤ 3 * N / 5 ∧ 3 * N / 5 ≤ N - 1 ∧
    t3nQ N * (52 * (N : ℝ) ^ 2 * Real.exp (x0 * N + slT N)) < 1 := by
  -- `N^6 e^{-N/200} → 0`
  have ht : Tendsto (fun N : ℕ => ((N : ℝ) / 200) ^ 6 * Real.exp (-((N : ℝ) / 200))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 6).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (by norm_num))
  have hK : (0 : ℝ) < 1 / (200 ^ 6 * (1248 * Real.exp 20 * 4)) := by positivity
  filter_upwards [ht.eventually (gt_mem_nhds hK), ev_lin_C, eventually_ge_atTop 64] with N h1 h2 hN
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  refine ⟨hN, ?_, by omega, ?_⟩
  · -- `2 D ≤ ⌊3N/5⌋`
    have hD : (2 * DU N : ℝ) ≤ 3 * N / 5 - 1 := by nlinarith
    have hfl : (3 * N / 5 : ℕ) * 5 + 4 ≥ 3 * N := by omega
    have h3 : ((3 * N / 5 : ℕ) : ℝ) ≥ 3 * N / 5 - 1 := by
      have : ((3 * N / 5 : ℕ) : ℝ) * 5 + 4 ≥ 3 * N := by exact_mod_cast hfl
      linarith
    have : ((2 * DU N : ℕ) : ℝ) ≤ ((3 * N / 5 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · -- the far deficit
    set n := 3 * N / 5 / 2 with hn
    have hnr : (3 : ℝ) * N / 10 - 2 ≤ n := by
      have : n * 10 + 18 ≥ 3 * N := by omega
      have : (n : ℝ) * 10 + 18 ≥ 3 * N := by exact_mod_cast this
      linarith
    have hdU : dU N (3 * N / 5) = N * Real.exp (-(n * Real.log 2)) := by
      unfold dU
      rw [← hn, one_div, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num),
        Real.rpow_def_of_pos (by norm_num)]
      ring_nf
    have hexp : Real.exp (-(n * Real.log 2)) ≤ 4 * Real.exp (-(3 / 10 * Real.log 2 * N)) := by
      have hl2 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; linarith
      have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have : -(n * Real.log 2) ≤ Real.log 4 + -(3 / 10 * Real.log 2 * N) := by
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
        rw [h4]; nlinarith
      calc Real.exp (-(n * Real.log 2)) ≤ Real.exp (Real.log 4 + -(3 / 10 * Real.log 2 * N)) :=
            Real.exp_le_exp.2 this
        _ = 4 * Real.exp (-(3 / 10 * Real.log 2 * N)) := by
            rw [Real.exp_add, Real.exp_log (by norm_num)]
    have hslT : Real.exp (slT N) = (N : ℝ) ^ 2 * Real.exp 20 := by
      unfold slT
      rw [Real.exp_add, show 2 * Real.log N = Real.log ((N : ℝ) ^ 2) by
        rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
    have hgap := t3n_gap
    have hcomb : Real.exp (-(3 / 10 * Real.log 2 * N)) * Real.exp (x0 * N) ≤ Real.exp (-((N : ℝ) / 200)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
    have hQ : t3nQ N ≤ 24 * (N : ℝ) ^ 2 * Real.exp (-(3 / 10 * Real.log 2 * N)) := by
      unfold t3nQ
      rw [hdU]
      have h0 := Real.exp_pos (-(n * Real.log 2))
      nlinarith
    have hE1 := Real.exp_pos (-(3 / 10 * Real.log 2 * N))
    have hE2 := Real.exp_pos (x0 * N)
    have hE3 := Real.exp_pos (-((N : ℝ) / 200))
    have hQ0 : 0 ≤ t3nQ N := by
      unfold t3nQ; have := dU_nonneg N (3 * N / 5); nlinarith
    rw [Real.exp_add, hslT]
    have hR : 0 ≤ 52 * (N : ℝ) ^ 2 * (Real.exp (x0 * N) * ((N : ℝ) ^ 2 * Real.exp 20)) := by positivity
    calc t3nQ N * (52 * (N : ℝ) ^ 2 * (Real.exp (x0 * N) * ((N : ℝ) ^ 2 * Real.exp 20)))
        ≤ 24 * (N : ℝ) ^ 2 * Real.exp (-(3 / 10 * Real.log 2 * N)) *
            (52 * (N : ℝ) ^ 2 * (Real.exp (x0 * N) * ((N : ℝ) ^ 2 * Real.exp 20))) :=
          mul_le_mul_of_nonneg_right hQ hR
      _ = 1248 * Real.exp 20 * (N : ℝ) ^ 6 *
            (Real.exp (-(3 / 10 * Real.log 2 * N)) * Real.exp (x0 * N)) := by ring
      _ ≤ 1248 * Real.exp 20 * (N : ℝ) ^ 6 * Real.exp (-((N : ℝ) / 200)) :=
          mul_le_mul_of_nonneg_left hcomb (by positivity)
      _ = 200 ^ 6 * (1248 * Real.exp 20) * (((N : ℝ) / 200) ^ 6 * Real.exp (-((N : ℝ) / 200))) := by ring
      _ < 200 ^ 6 * (1248 * Real.exp 20) * (1 / (200 ^ 6 * (1248 * Real.exp 20 * 4))) :=
          mul_lt_mul_of_pos_left h1 (by positivity)
      _ ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]
          have := Real.exp_pos 20
          nlinarith

/-! ### Maximal effect states other than `teW` -/

/-- **Off `teW`, the effect minimum is tiny**: some unit has `p ≤ 1/2`, so `λ^e_min ≤ 6 δ_{N-1}`. -/
lemma leMinAt_le_of_ne_teW {s : State N} {w : Param N} (ho : w ∈ openCube N) (hDN : DU N ≤ N - 1)
    (hcE : concEAll N s w) (hδs : dU N (N - 1) ≤ 1 / 100) {te : State N} (hne : te ≠ teW w s) :
    leMinAt s w te ≤ 6 * dU N (N - 1) := by
  have hz : flipP s w ∈ openCube N := flipP_mem_openCube ho
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  have hbdd : BddBelow (Set.range (kF (lamEz (flipP s w) s te))) := (Set.finite_range _).bddBelow
  refine (ciInf_le hbdd j).trans ?_
  obtain ⟨me1, -, me3, me4, -⟩ := lamEz_means hz s te
  have hk : kF (lamEz (flipP s w) s te) j = Real.logb 2 ((tpmOf (flipP s w)).prob j s (te j) /
      effUnit (tpmOf (flipP s w)) (univ.erase j)ᶜ s j (te j)) := me1 j (univ.erase j)
  rw [hk]
  -- `p ≤ 1/2`
  have hp : (tpmOf (flipP s w)).prob j s (te j) ≤ 1 / 2 := by
    rw [g_prob_te]
    unfold teW at hj
    by_cases hy : 1 / 2 < clamp01 (w s j)
    · rw [if_pos hy] at hj
      rw [if_neg hj]; linarith
    · rw [if_neg hy] at hj
      have : te j = s j := by cases h1 : te j <;> cases h2 : s j <;> simp_all
      rw [if_pos this]; linarith
  -- `A ≥ 1/2 - δ`
  have hcard : (univ.erase j).card = N - 1 := by
    rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
  have hA := hcE te j (univ.erase j) (notMem_erase j univ) (by rw [hcard]; exact hDN)
  rw [hcard] at hA
  have hAlo : 1 / 2 - dU N (N - 1) ≤ effUnit (tpmOf (flipP s w)) (univ.erase j)ᶜ s j (te j) := by
    have := (abs_le.1 hA).1; linarith
  have hp0 := me3 j
  have hA0 := me4 j (univ.erase j)
  have hδ0 := dU_nonneg N (N - 1)
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hratio : (tpmOf (flipP s w)).prob j s (te j) / effUnit (tpmOf (flipP s w)) (univ.erase j)ᶜ s j (te j) ≤
      1 + 3 * dU N (N - 1) := by
    rw [div_le_iff₀ hA0]; nlinarith
  have hpos : 0 < (tpmOf (flipP s w)).prob j s (te j) / effUnit (tpmOf (flipP s w)) (univ.erase j)ᶜ s j (te j) :=
    div_pos hp0 hA0
  unfold Real.logb
  rw [div_le_iff₀ (Real.log_pos (by norm_num))]
  have := Real.log_le_sub_one_of_pos hpos
  nlinarith

/-! ### Tier 3 without `lowE` -/

set_option maxHeartbeats 1000000 in
/-- **Tier 3 bound without `lowE`** (deterministic, `N` large). -/
theorem tier3_bound_noLow : ∀ᶠ N : ℕ in atTop, ∀ (s : State N) (w : Param N),
    w ∈ B1w N s → w ∈ openCube N →
    sysMaxCauseStates (tpmOf (flipP s w)) univ s s = {tcRow w} →
    Tier3Rest6 N s w → concCAt N w (tcRow w) → concEAll N s w → w ∉ gTieEv N s →
    XW w (tcRow w) ≤ x0 * N + slT N → Zs w < 13 →
    (∃ S : Finset (Fin N), 2 ≤ S.card ∧ S.card ≤ 3 ∧ 1 / 4 * betaW w ≤ phi (flipP s w) s S) →
    ∀ j, phi (flipP s w) s univ ≤ betaW w * kF (lamCz (flipP s w) s (tcRow w)) j := by
  filter_upwards [t3n_far_num, ev_N_dU_top] with N ⟨hN64, hDd, hdsN, hQ⟩ htop
  intro s w hB ho hst hr hcC hcE hnt hT hZ ⟨S, h2, h3, hS⟩ j
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hN0 : (0 : ℝ) < N := by linarith
  have hz : flipP s w ∈ openCube N := flipP_mem_openCube ho
  have hinv : flipP s (flipP s w) = w := flipP_invol s w
  have hDN : DU N ≤ N - 1 := DU_le hN64
  set ds := 3 * N / 5 with hdsdef
  have hd5 : 5 * ds ≤ 3 * N := Nat.mul_div_le (3 * N) 5
  have hD1 : 1 ≤ DU N := by unfold DU; omega
  have hδ0 : ∀ d, 0 ≤ dU N d := dU_nonneg N
  have hδtop0 := hδ0 (N - 1)
  have hδs : dU N (N - 1) ≤ 1 / 100 := by
    have : dU N (N - 1) ≤ N * dU N (N - 1) := le_mul_of_one_le_left hδtop0 (by linarith)
    linarith
  have hDU := N_dU_DU hN1
  have hDNr : (DU N : ℝ) ≤ N := by exact_mod_cast (show DU N ≤ N by omega)
  have hDr : (1 : ℝ) ≤ DU N := by exact_mod_cast hD1
  have hδc : 12 * DU N * dU N (N - 1) + 3 * N * (dU N (DU N) + dU N (N - 1)) < DU N := by
    have : (DU N : ℝ) * dU N (N - 1) ≤ N * dU N (N - 1) := mul_le_mul_of_nonneg_right hDNr hδtop0
    nlinarith
  have h2D : 2 * DU N ≤ N - 1 := hDd.trans hdsN
  have hη : 6 * (dU N (2 * DU N) + dU N (N - 1)) < 1 / (N : ℝ) := by
    have h1 := g_N_dU_2DU hN1 (le_refl (2 * DU N))
    have h2 := g_N_dU_2DU hN1 h2D
    have hinvN : 1 / (N : ℝ) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    have hN2' : 1 / (N : ℝ) ^ 2 / 1000 ≤ 1 / 1000 := by linarith
    have : (N : ℝ) * (6 * (dU N (2 * DU N) + dU N (N - 1))) < 1 := by nlinarith
    rw [lt_div_iff₀ hN0]; linarith
  have hj0 : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hbdd : ∀ f : Fin N → ℝ, BddBelow (Set.range f) := fun f => (Set.finite_range f).bddBelow
  -- `β`
  have hβ0 := betaW_pos ho
  have hP0 : ∀ i, 0 < clamp01 (w (tcRow w) i) := fun i => by
    rw [b1_clamp01_of_mem_Ioo (ho _ i)]; exact (ho _ i).1
  have hβlow : Real.exp (-(x0 * N + slT N)) / 13 ≤ betaW w := by
    unfold betaW
    rw [Pw_eq_exp_neg_XW hP0]
    have hZ0 := b1_Zs_pos ho
    calc Real.exp (-(x0 * N + slT N)) / 13 ≤ Real.exp (-XW w (tcRow w)) / 13 :=
          div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) (by norm_num)
      _ ≤ Real.exp (-XW w (tcRow w)) / Zs w :=
          div_le_div_of_nonneg_left (Real.exp_pos _).le hZ0 hZ.le
  have hβ1 : betaW w ≤ 1 := by
    unfold betaW
    rw [div_le_one (b1_Zs_pos ho)]
    exact single_le_sum (f := fun r => Pw w r) (fun r _ => Pw_nonneg w r) (mem_univ _)
  -- the far deficit
  have hfar : ∀ L0 : ℝ, betaW w / (4 * (N : ℝ) ^ 2) ≤ L0 → ∀ d, ds ≤ d → d + 2 ≤ N →
      ((N : ℝ) - 1) * (3 * (dU N d + dU N (N - 1))) < L0 := by
    intro L0 hL0 d hd _
    have ha : dU N d ≤ dU N ds := dU_anti N hd
    have hb : dU N (N - 1) ≤ dU N ds := dU_anti N hdsN
    have hle : ((N : ℝ) - 1) * (3 * (dU N d + dU N (N - 1))) ≤ t3nQ N := by
      unfold t3nQ
      have : (0 : ℝ) ≤ (N : ℝ) - 1 := by linarith
      have := hδ0 d
      nlinarith
    have hE := Real.exp_pos (x0 * N + slT N)
    have hpos : 0 < 52 * (N : ℝ) ^ 2 * Real.exp (x0 * N + slT N) := by positivity
    have hQ' : t3nQ N < 1 / (52 * (N : ℝ) ^ 2 * Real.exp (x0 * N + slT N)) := by
      rw [lt_div_iff₀ hpos]; linarith
    have heq : 1 / (52 * (N : ℝ) ^ 2 * Real.exp (x0 * N + slT N)) =
        Real.exp (-(x0 * N + slT N)) / 13 / (4 * (N : ℝ) ^ 2) := by
      rw [Real.exp_neg]; field_simp; ring
    have hβ4 : Real.exp (-(x0 * N + slT N)) / 13 / (4 * (N : ℝ) ^ 2) ≤ betaW w / (4 * (N : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right hβlow (by positivity)
    linarith
  -- `lowC`
  have hlowC := lowC_det (by omega) hB ho hst h2 h3 hS
  have hlc0 : 0 < lcMin s w := lt_trans (by positivity) hlowC
  have hβN : betaW w / (4 * (N : ℝ) ^ 2) ≤ lcMin s w := by
    have : betaW w / (4 * (N : ℝ) ^ 2) ≤ 1 / (4 * (N : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have hFc : lcMin s w ≤ kF (lamCz (flipP s w) s (tcRow w)) j := ciInf_le (hbdd _) j
  have hX0 : 0 ≤ betaW w * kF (lamCz (flipP s w) s (tcRow w)) j :=
    mul_nonneg hβ0.le (hlc0.le.trans hFc)
  have hβ : sysBackCause (tpmOf (flipP s w)) univ s s (tcRow w) = betaW w := by
    rw [sysBackCause_univ_eq hz, flipP_invol s w]; rfl
  -- the cause side
  obtain ⟨mc1, mc2, mc3, mc4, mc5⟩ := lamCz_means hz s (tcRow w)
  rw [hinv] at mc1 mc2 mc3 mc4 mc5
  have kc := keyHyp_of_events (lam := lamCz (flipP s w) s (tcRow w)) (x := fun j => clamp01 (w (tcRow w) j))
    (A := fun j C => cmean w (univ \ C) (tcRow w) j) (δ := dU N) (lmin := lcMin s w) (η := 1 / (N : ℝ))
    (D := DU N) (dstar := ds) mc1 mc2 mc3 (fun j => clamp01_le_one _) mc4 mc5
    (fun j C hj hC => hcC j C hj hC) hδ0 hδs (fun d d' _ h => dU_anti N h) hD1 hDN hDd hd5
    hlc0 (fun j => ciInf_le (hbdd _) j) hj0 hδc (hfar _ hβN) hr.spreadC hr.smallC hr.countC hη
  -- every maximal pair
  unfold phi sysPhi
  refine sup'OrZero_le hX0 fun q hq => ?_
  rw [hst, mem_product, mem_singleton] at hq
  obtain ⟨q1, te⟩ := q
  obtain ⟨rfl, hte⟩ := hq
  simp only
  obtain ⟨j1, hj1⟩ := g_ciInf_attained hN1 (kF (lamEz (flipP s w) s te))
  have hsing := phiAt_le_N_kFE hN2 hz s (tcRow w) te j1
  have hj1' : kF (lamEz (flipP s w) s te) j1 = leMinAt s w te := hj1
  rw [hj1'] at hsing
  have he1 := sysEffProb_le_one (tpmOf (flipP s w)) univ s s te
  have he0 := sysEffProb_nonneg (tpmOf (flipP s w)) univ s s te
  have hp0 : 0 ≤ pos (leMinAt s w te) := le_max_left _ _
  by_cases hA : (N : ℝ) * pos (leMinAt s w te) ≤ betaW w * lcMin s w
  · calc sysPhiOfState (tpmOf (flipP s w)) univ s s (tcRow w) te
        ≤ N * (sysEffProb (tpmOf (flipP s w)) univ s s te * pos (leMinAt s w te)) := hsing
      _ ≤ N * pos (leMinAt s w te) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          nlinarith
      _ ≤ betaW w * lcMin s w := hA
      _ ≤ betaW w * kF (lamCz (flipP s w) s (tcRow w)) j := mul_le_mul_of_nonneg_left hFc hβ0.le
  · push Not at hA
    have hteW : te = teW w s := by
      by_contra hne
      have hsm := leMinAt_le_of_ne_teW ho hDN hcE hδs hne
      have hp6 : pos (leMinAt s w te) ≤ 6 * dU N (N - 1) := max_le (by positivity) hsm
      have hb4 : Real.exp (-(x0 * N + slT N)) / 13 / (4 * (N : ℝ)) ≤ betaW w * lcMin s w := by
        have h1 : betaW w * (1 / (4 * (N : ℝ))) ≤ betaW w * lcMin s w :=
          mul_le_mul_of_nonneg_left hlowC.le hβ0.le
        have h2 : Real.exp (-(x0 * N + slT N)) / 13 / (4 * (N : ℝ)) ≤ betaW w * (1 / (4 * (N : ℝ))) := by
          rw [mul_one_div]; exact div_le_div_of_nonneg_right hβlow (by positivity)
        linarith
      have hdd : dU N (N - 1) ≤ dU N ds := dU_anti N hdsN
      have hE := Real.exp_pos (x0 * N + slT N)
      have hkey : (N : ℝ) * (6 * dU N (N - 1)) < Real.exp (-(x0 * N + slT N)) / 13 / (4 * (N : ℝ)) := by
        have hQ2 : (N : ℝ) * (6 * dU N ds) * (52 * (N : ℝ) * Real.exp (x0 * N + slT N)) ≤
            t3nQ N * (52 * (N : ℝ) ^ 2 * Real.exp (x0 * N + slT N)) := by
          unfold t3nQ
          have := dU_nonneg N ds
          have : (1 : ℝ) ≤ (N : ℝ) - 1 := by linarith
          nlinarith [mul_nonneg (mul_nonneg (dU_nonneg N ds) (sq_nonneg (N : ℝ))) hE.le]
        have heq : Real.exp (-(x0 * N + slT N)) / 13 / (4 * (N : ℝ)) =
            1 / (52 * (N : ℝ) * Real.exp (x0 * N + slT N)) := by
          rw [Real.exp_neg]; field_simp; ring
        rw [heq, lt_div_iff₀ (by positivity)]
        have h6 : (N : ℝ) * (6 * dU N (N - 1)) ≤ (N : ℝ) * (6 * dU N ds) := by nlinarith
        have h7 := mul_le_mul_of_nonneg_right h6 (by positivity : (0 : ℝ) ≤ 52 * (N : ℝ) * Real.exp (x0 * N + slT N))
        linarith
      have : (N : ℝ) * pos (leMinAt s w te) ≤ (N : ℝ) * (6 * dU N (N - 1)) :=
        mul_le_mul_of_nonneg_left hp6 (Nat.cast_nonneg _)
      linarith
    have he : EffRest6 N s w te := hteW ▸ hr.effW
    have hbl : betaW w / (4 * (N : ℝ) ^ 2) < pos (leMinAt s w te) := by
      have h1 : betaW w * (1 / (4 * (N : ℝ))) < betaW w * lcMin s w := mul_lt_mul_of_pos_left hlowC hβ0
      have k1 : betaW w / (4 * (N : ℝ)) < N * pos (leMinAt s w te) := by
        rw [mul_one_div] at h1; linarith
      rw [div_lt_iff₀ (by positivity)]
      calc betaW w = 4 * (N : ℝ) * (betaW w / (4 * (N : ℝ))) := by field_simp
        _ < 4 * (N : ℝ) * (N * pos (leMinAt s w te)) := mul_lt_mul_of_pos_left k1 (by positivity)
        _ = pos (leMinAt s w te) * (4 * (N : ℝ) ^ 2) := by ring
    have hle0 : 0 < leMinAt s w te := by
      have hb0 : 0 < betaW w / (4 * (N : ℝ) ^ 2) := by positivity
      by_contra hc
      push Not at hc
      have : pos (leMinAt s w te) = 0 := max_eq_left hc
      linarith
    have hposE : pos (leMinAt s w te) = leMinAt s w te := max_eq_right hle0.le
    rw [hposE] at hbl
    obtain ⟨me1, me2, me3, me4, me5⟩ := lamEz_means hz s te
    have ke := keyHyp_of_events (lam := lamEz (flipP s w) s te)
      (x := fun j => (tpmOf (flipP s w)).prob j s (te j))
      (A := fun j C => effUnit (tpmOf (flipP s w)) Cᶜ s j (te j)) (δ := dU N) (lmin := leMinAt s w te)
      (η := 1 / (N : ℝ)) (D := DU N) (dstar := ds) me1 me2 me3
      (fun j => (tpmOf (flipP s w)).le_one j s _) me4 me5
      (fun j C hj hC => hcE te j C hj hC) hδ0 hδs (fun d d' _ h => dU_anti N h) hD1 hDN hDd hd5
      hle0 (fun j => ciInf_le (hbdd _) j) hj0 hδc (hfar _ hbl.le) he.spreadE he.smallE he.countE hη
    have hnoTie : ∀ j j', j ≠ j' → phTAt s w te j ≠ phTAt s w te j' := by
      intro a b hab heq
      exact hnt ⟨te, hte, a, b, hab, heq⟩
    obtain ⟨jst, -, hjst⟩ := exists_min_image (univ : Finset (Fin N)) (phTAt s w te)
      ⟨⟨0, by omega⟩, mem_univ _⟩
    have h3' := univ_tier3 hz hN2 s (tcRow w) te kc ke
      (g_ciInf_attained hN1 _) (g_ciInf_attained hN1 _) hnoTie jst (fun j' => hjst j' (mem_univ j'))
    rw [h3']
    calc phTAt s w te jst ≤ phTAt s w te j := hjst j (mem_univ j)
      _ ≤ sysBackCause (tpmOf (flipP s w)) univ s s (tcRow w) * kF (lamCz (flipP s w) s (tcRow w)) j :=
          min_le_left _ _
      _ = betaW w * kF (lamCz (flipP s w) s (tcRow w)) j := by rw [hβ]

/-! ### The probabilistic reduction -/

/-- **The tilt leaf at any rate `C ≤ 1.4`** (as `leaf4_strong`). -/
theorem tilt_bound {C : ℝ} (hC : C ≤ 14 / 10) (hLT : LT2Stmt 1 C) : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bTilt N s) ≤ ENNReal.ofReal (3 * Real.exp (-(C * N))) := by
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
  have he : Real.exp (-(2 * N)) ≤ Real.exp (-(C * N)) := Real.exp_le_exp.2 (by nlinarith)
  have he' : Real.exp (-(14 / 10 * N)) ≤ Real.exp (-(C * N)) := Real.exp_le_exp.2 (by nlinarith)
  calc cubeM N (bTilt N s)
      ≤ cubeM N (dtHalfBad N) + cubeM N (dtZBad N) + cubeM N {w | betaW w < 1 * sigN N ∧
          ∀ S : Finset (Fin N), S.card = 2 → phi (flipP s w) s S < 3 * 1 * sigN N} :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
    _ ≤ ENNReal.ofReal (Real.exp (-(C * N))) + ENNReal.ofReal (Real.exp (-(C * N))) +
          ENNReal.ofReal (Real.exp (-(C * N))) := by
        gcongr
        · exact hH.trans (ENNReal.ofReal_le_ofReal he)
        · exact hZ.trans (ENNReal.ofReal_le_ofReal he')
        · exact hL s
    _ = ENNReal.ofReal (3 * Real.exp (-(C * N))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
          ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
        ring_nf

/-- **`NatTier3Stmt` from the residual event without `lowE`.** -/
theorem natTier3_of_rest6 {C C' : ℝ} (hC : C < C') (hC' : C' ≤ 14 / 10) (h : NatTier3Rest6Stmt C')
    (hLT2 : LT2Stmt 1 C') (hLT : LTBetaStmt (1 / 4) C') : NatTier3Stmt C := by
  have hm : C < (C + C') / 2 := by linarith
  filter_upwards [h, hLT, tilt_bound hC' hLT2, dt_Zs_bad, tier3_bound_noLow, g_superexp ((C + C') / 2),
    g_absorb 7 hm, eventually_ge_atTop 3] with N hR hL hTl hZb hDet hS hA hN3 s
  have hN1 : 1 ≤ N := by omega
  set c := 2 ^ N * (N * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2))) with hc
  have hsub : bNat N s ∩ {w | ¬ ∀ j, phi (flipP s w) s univ ≤
        betaW w * kF (lamCz (flipP s w) s (tcRow w)) j} ⊆
      ((((bNat N s ∩ {w | ¬ Tier3Rest6 N s w}) ∪
        {w | sysMaxCauseStates (tpmOf (flipP s w)) univ s s ≠ {tcRow w}}) ∪
        ({w | ¬ concCAt N w (tcRow w)} ∪ {w | ¬ concEAll N s w})) ∪ (gTieEv N s ∪ bTilt N s)) ∪
      (dtZBad N ∪ (B1w N s ∩ openCube N ∩ {w | ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 →
        phi (flipP s w) s S < 1 / 4 * betaW w})) := by
    rintro w ⟨hw, hn⟩
    obtain ⟨⟨hB, ho⟩, hNat⟩ := hw
    by_contra hall
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, not_or, not_and, not_not] at hall
    obtain ⟨⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩, h7, h8⟩ := hall
    apply hn
    have hT6 : Tier3Rest6 N s w := h1 ⟨⟨hB, ho⟩, hNat⟩
    have hTilt : XW w (tcRow w) ≤ x0 * N + slT N := by
      by_contra ht
      exact h6 ⟨⟨hB, ho⟩, ht⟩
    have hZ : Zs w < 13 := by
      by_contra hz; exact h7 fun hh => hz hh.2
    obtain ⟨S, hS2, hS3, hSβ⟩ : ∃ S : Finset (Fin N), 2 ≤ S.card ∧ S.card ≤ 3 ∧
        1 / 4 * betaW w ≤ phi (flipP s w) s S := by
      by_contra hno
      push Not at hno
      exact h8 ⟨hB, ho⟩ hno
    exact hDet s w hB ho h2 hT6 h3 h4 h5 hTilt hZ ⟨S, hS2, hS3, hSβ⟩
  have hc0 : 0 ≤ c := by positivity
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hZ' : Real.exp (-(14 / 10 * N)) ≤ Real.exp (-(C' * N)) := Real.exp_le_exp.2 (by nlinarith)
  have hR' : Real.exp (-(C' * N)) ≤ Real.exp (-((C + C') / 2 * N)) := Real.exp_le_exp.2 (by nlinarith)
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add ((measure_union_le _ _).trans (add_le_add (hR s) (stateC_null hN1 s).le))
      ((measure_union_le _ _).trans (add_le_add (concTc_rare hN3 s) (concEAll_rare hN3 s)))))
    ((measure_union_le _ _).trans (add_le_add (noTie_null s).le (hTl s)))))
    ((measure_union_le _ _).trans (add_le_add (hZb.trans (ENNReal.ofReal_le_ofReal hZ')) (hL s)))).trans ?_
  simp only [add_zero, zero_add]
  have ha0 := (Real.exp_pos (-(C' * N))).le
  rw [← ENNReal.ofReal_add hc0 hc0, ← ENNReal.ofReal_add ha0 (add_nonneg hc0 hc0),
    ← ENNReal.ofReal_add (add_nonneg ha0 (add_nonneg hc0 hc0)) (by positivity : (0 : ℝ) ≤ 3 * Real.exp (-(C' * N))),
    ← ENNReal.ofReal_add ha0 ha0, ← ENNReal.ofReal_add (by positivity) (add_nonneg ha0 ha0)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hS' : 2 * c ≤ Real.exp (-((C + C') / 2 * N)) := hS
  have hA' : 7 * Real.exp (-((C + C') / 2 * N)) ≤ Real.exp (-(C * N)) := hA
  linarith

end Census
end IIT
