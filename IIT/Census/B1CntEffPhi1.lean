/-
Census, B1, W14 work package WP3 (effect side), part 5: the value of `φ_e` at the one-unit
purview `{k1}` (W5 Lemma E3'(i)).
* `effC_facts`: the size relations between `σ, ε_N, κ_N, A_0, x_2` used throughout;
* `ratio_key`, `norm_compare`: the real inequalities behind "the total cut is the unique MIP";
* `eff_maxStates_single`, `eff_phi_single`, `eff_phi_single_ge` (blueprint statements).
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §8.  No `sorry`.
-/
import IIT.Census.B1CntEffSingle

namespace IIT
namespace Census

/-! Helpers live in `IIT.Census.WP3` (avoids name clashes with the other work packages);
the blueprint names are re-exported to `IIT.Census` by `alias` at the end of the file. -/
namespace WP3

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### Size relations -/

lemma x2C_le (hC : EffC N) : x2C N ≤ N * sigC N := by
  have hN := hC.hN
  have hL := log_le_N N
  have hN6 : (90000 : ℝ) ≤ N := by exact_mod_cast hN
  unfold x2C
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (sigC_pos N).le
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith

/-- All the size relations of the constants. -/
structure EffF (N : ℕ) : Prop where
  ε0 : 0 ≤ epsN N
  εσ : epsN N ≤ sigC N / 100
  σ0 : 0 < sigC N
  σ1 : sigC N ≤ 1 / 100
  σA : sigC N ≤ A0C N
  x2N : (N : ℝ) * x2C N ≤ 1 / 100
  x21 : x2C N ≤ 1 / 100
  κx : 12 * x2C N ^ 2 + 8 * epsN N ≤ kapN N
  κ0 : 0 ≤ kapN N
  L1 : 1 ≤ Real.log N
  N1 : (1 : ℝ) ≤ N

theorem effC_facts (hC : EffC N) : EffF N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by have := hC.hN; omega)
  have hσ0 := sigC_pos N
  have hN3 : sigC N ≤ (N : ℝ) ^ 3 * sigC N := le_mul_of_one_le_left hσ0.le (one_le_pow₀ hN1)
  have hσ1 : sigC N ≤ 1 / 100 := hN3.trans hC.hσ
  have hL0 : 0 ≤ Real.log N := by linarith [hC.hL1]
  have hx := x2C_le hC
  have hx0 := x2C_nonneg N
  have hNx : (N : ℝ) * x2C N ≤ 1 / 100 := by
    have h1 : (N : ℝ) * x2C N ≤ (N : ℝ) * (N * sigC N) := mul_le_mul_of_nonneg_left hx (by linarith)
    have h2 : (N : ℝ) * (N * sigC N) ≤ (N : ℝ) ^ 3 * sigC N := by
      have : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := pow_le_pow_right₀ hN1 (by norm_num)
      nlinarith
    linarith [hC.hσ]
  refine ⟨epsN_nonneg N, ?_, hσ0, hσ1, A0C_ge hC.hL1, hNx, ?_, ?_, kapN_nonneg hL0, hC.hL1, hN1⟩
  · have := hC.hεσ; nlinarith
  · nlinarith
  · rw [kapN_eq, x2C_sq hL0]
    have : 0 ≤ (dX N : ℝ) ^ 2 * sigC N ^ 2 := by positivity
    nlinarith

/-- From `Core_K(0)` at `k`: `σ ≤ f`, `f < x_2`, and the others are `κ_N` below `f`. -/
lemma core_bounds (hF : EffF N) {s : State N} {K : Finset (Fin N)} {k : Fin N} {w : Param N}
    (hcore : CoreAt N s K k 0 w) :
    sigC N < |fK w s K k| ∧ |fK w s K k| < x2C N ∧
      ∀ k', k' ≠ k → |fK w s K k'| + kapN N < |fK w s K k| := by
  obtain ⟨h1, h2, h3, -⟩ := hcore
  refine ⟨by linarith [hF.σA, hF.κ0], by linarith, fun k' hk' => ?_⟩
  have := h3 k' hk'
  linarith

/-! ### The real inequalities -/

lemma ratio_key {f ab ε dev r m : ℝ} (hf : 0 < f) (hf8 : f ≤ 1 / 8) (hab : |ab| ≤ ε)
    (hε8 : ε ≤ 1 / 8) (hr : 0 < r) (hrm : r ≤ m)
    (hdev : dev < f * (1 - r / m) - 2 * f ^ 2 - 2 * ε) (hq : 0 < 1 / 2 + dev) :
    Real.log ((1 / 2 + f) / (1 / 2 + ab)) * r < Real.log ((1 / 2 + f) / (1 / 2 + dev)) * m := by
  have hm : 0 < m := lt_of_lt_of_le hr hrm
  obtain ⟨hab1, hab2⟩ := abs_le.1 hab
  have hε0 : 0 ≤ ε := (abs_nonneg ab).trans hab
  have hc : 0 < 1 / 2 + ab := by linarith
  -- upper bound on the total-cut log ratio
  have hL1 : Real.log ((1 / 2 + f) / (1 / 2 + ab)) ≤ 2 * f + 4 * ε := by
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one hc.ne', div_le_iff₀ hc]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ab + ε) (by linarith : (0 : ℝ) ≤ 1 + 2 * f + 4 * ε)]
  -- lower bound on the partial-cut log ratio
  have hL2 : 2 * f - 4 * f ^ 2 - 2 * dev ≤ Real.log ((1 / 2 + f) / (1 / 2 + dev)) := by
    have e : (1 / 2 + f) / (1 / 2 + dev) = (1 + 2 * f) / (1 + 2 * dev) := by
      rw [div_eq_div_iff hq.ne' (by linarith)]; ring
    rw [e, Real.log_div (by linarith) (by linarith)]
    have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + 2 * f by linarith)
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 2 * dev by linarith)
    have h3 : (1 + 2 * f)⁻¹ ≤ 1 - 2 * f + 4 * f ^ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hdm : dev * m < f * (m - r) - 2 * f ^ 2 * m - 2 * ε * m := by
    have := mul_lt_mul_of_pos_right hdev hm
    have e : (f * (1 - r / m) - 2 * f ^ 2 - 2 * ε) * m = f * (m - r) - 2 * f ^ 2 * m - 2 * ε * m := by
      field_simp
    linarith
  have hlogpos : 0 ≤ Real.log ((1 / 2 + f) / (1 / 2 + dev)) * m := by
    nlinarith
  calc Real.log ((1 / 2 + f) / (1 / 2 + ab)) * r ≤ (2 * f + 4 * ε) * r :=
        mul_le_mul_of_nonneg_right hL1 hr.le
    _ ≤ 2 * f * r + 4 * ε * m := by nlinarith
    _ < (2 * f - 4 * f ^ 2 - 2 * dev) * m := by nlinarith
    _ ≤ Real.log ((1 / 2 + f) / (1 / 2 + dev)) * m := mul_le_mul_of_nonneg_right hL2 hm.le

lemma norm_compare {p c q m r : ℝ} (hp : 0 < p) (hm : 0 < m) (hr : 0 < r)
    (hpc : 0 < Real.log (p / c)) (hkey : Real.log (p / c) * r < Real.log (p / q) * m) :
    p * pos (Real.logb 2 (p / c)) / m < p * pos (Real.logb 2 (p / q)) / r := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpq : 0 < Real.log (p / q) := by
    have : 0 < Real.log (p / q) * m := lt_trans (mul_pos hpc hr) hkey
    exact pos_of_mul_pos_left this hm.le
  have e1 : pos (Real.logb 2 (p / c)) = Real.log (p / c) / Real.log 2 :=
    max_eq_right (div_nonneg hpc.le hl2.le)
  have e2 : pos (Real.logb 2 (p / q)) = Real.log (p / q) / Real.log 2 :=
    max_eq_right (div_nonneg hpq.le hl2.le)
  rw [e1, e2, div_lt_div_iff₀ hm hr]
  have := mul_lt_mul_of_pos_left hkey (div_pos hp hl2)
  calc p * (Real.log (p / c) / Real.log 2) * r = p / Real.log 2 * (Real.log (p / c) * r) := by ring
    _ < p / Real.log 2 * (Real.log (p / q) * m) := this
    _ = p * (Real.log (p / q) / Real.log 2) * m := by ring

/-! ### The one-unit purview -/

section Single

variable {s : State N} {K : Finset (Fin N)} {k : Fin N} {w : Param N}

lemma effRep_single (T : UnitTPM N) (M : Finset (Fin N)) (m z : State N) (k : Fin N) :
    effRep T M m {k} z = effUnit T M m k (z k) := by
  simp only [effRep, prod_singleton]

lemma partEffRep_single (T : UnitTPM N) (M : Finset (Fin N)) (m z : State N) (k : Fin N)
    (θ : Partition N M {k}) : partEffRep T M m {k} z θ = effUnit T (θ.effPart k) m k (z k) := by
  simp only [partEffRep, prod_singleton]

lemma cutCount_single (M : Finset (Fin N)) (k : Fin N) (θ : Partition N M {k}) :
    cutCount M {k} θ = M.card - (θ.effPart k).card := by
  simp only [cutCount, sum_singleton]

/-- **E3'(i): the value of `φ_e` at `({k}, z)` with `z k = te k`.** -/
theorem phi_single_val (hC : EffC N) (hz : flipP s w ∈ openCube N) (hc : CoinAt N s K k w)
    (hD : DleAt N s K k w)
    (hsub : ∀ A : Finset (Fin N), A.card + D0C N ≤ N →
      |effDevA w s A s k| ≤ 2 * Real.sqrt ((N : ℝ) / 2 ^ (N - A.card)) +
        2 * ((N - A.card + 1 : ℕ) : ℝ) ^ 4 / 2 ^ (N - A.card))
    (hcol : |effDevA w s ∅ s k| ≤ epsN N) (z : State N) (hzk : z k = teW w s k) :
    phiEat (tpmOf (flipP s w)) (univ \ K) s {k} z =
      (1 / 2 + fK w s K k) * Real.logb 2 ((1 / 2 + fK w s K k) / (1 / 2 + effDevA w s ∅ s k)) := by
  have hF := effC_facts hC
  set T := tpmOf (flipP s w) with hT
  set M := univ \ K with hMdef
  set f := fK w s K k with hfdef
  set ab := effDevA w s ∅ s k with habdef
  have hf := hc.posf
  obtain ⟨hσf, hfx, -⟩ := core_bounds hF hc.core
  rw [abs_of_pos hf] at hσf hfx
  have hMne : M.Nonempty := by
    rw [nonempty_iff_ne_empty]; intro h
    have hc' : M.card = N - dX N := by rw [hMdef, card_univ_sdiff, Fintype.card_fin, hc.card]
    rw [h, card_empty] at hc'
    have := hC.hD0; have := hC.hN; unfold D0C at *; have := dX_le_N (show 1 ≤ N by omega)
    have : dX N < N := by have := dX_ge N; omega
    omega
  have hp : effUnit T M s k (z k) = 1 / 2 + f := by rw [hzk, hT, effUnit_te]; rfl
  have hab1 := (abs_le.1 hcol).1
  have hab2 := (abs_le.1 hcol).2
  have hεσ := hF.εσ
  have hσ1 := hF.σ1
  have hσ0 := hF.σ0
  have hc0 : effUnit T ∅ s k (z k) = 1 / 2 + ab := by rw [hzk, hT, effUnit_te]
  have hm := mX_eq_card hc.card
  rw [← hMdef] at hm
  rw [phiEat_single_of_gt T M hMne s k z]
  · unfold phiEofPartition
    rw [effRep_single, partEffRep_total, prod_singleton, hp, hc0]
    have hpos : 0 < Real.logb 2 ((1 / 2 + f) / (1 / 2 + ab)) := by
      refine Real.logb_pos one_lt_two ?_
      rw [one_lt_div (by linarith)]
      linarith
    rw [show pos (Real.logb 2 ((1 / 2 + f) / (1 / 2 + ab))) =
      Real.logb 2 ((1 / 2 + f) / (1 / 2 + ab)) from max_eq_right hpos.le]
  · intro θ hθ
    set A := θ.effPart k with hAdef
    have hAM : A ⊆ M := θ.effPart_subset k
    have hAne' : A ≠ M := θ.effPart_ne (mem_singleton_self k)
    have hAne : A.Nonempty := nonempty_iff_ne_empty.2 hθ
    have hdev := dev_all hC hc hD hsub A hAM hAne hAne'
    have hq : effUnit T A s k (z k) = 1 / 2 + effDevA w s A s k := by rw [hzk, hT, effUnit_te]
    have hqpos : 0 < 1 / 2 + effDevA w s A s k := by
      rw [← hq]; exact effUnit_pos_flip hz A s k (z k)
    unfold normalizedPhi phiEofPartition
    rw [effRep_single, partEffRep_total, prod_singleton, partEffRep_single, cutCount_total,
      cutCount_single, hp, hc0, hq, card_singleton, mul_one]
    have hsd : (M \ A).card = M.card - A.card := card_sdiff_of_subset hAM
    have hr1 : 1 ≤ (M \ A).card := by
      rcases Nat.eq_zero_or_pos (M \ A).card with h | h
      · exfalso; apply hAne'
        exact Subset.antisymm hAM (fun i hi => by
          by_contra hiA
          have : i ∈ M \ A := mem_sdiff.2 ⟨hi, hiA⟩
          rw [card_eq_zero.1 h] at this; exact absurd this (notMem_empty i))
      · exact h
    have hrm : (M \ A).card ≤ M.card := card_le_card sdiff_subset
    rw [← hsd]
    have hmpos : (0 : ℝ) < M.card := by exact_mod_cast (show 0 < M.card by omega)
    refine norm_compare (by linarith) hmpos (by exact_mod_cast hr1) ?_ ?_
    · refine Real.log_pos ?_
      rw [one_lt_div (by linarith)]
      linarith
    · rw [← hm] at hmpos
      have hκ : 2 * f ^ 2 + 2 * epsN N ≤ kapN N / 2 := by
        have : f ^ 2 ≤ x2C N ^ 2 := pow_le_pow_left₀ hf.le hfx.le 2
        linarith [hF.κx, hF.ε0, sq_nonneg (x2C N)]
      rw [← hm]
      refine ratio_key hf (by linarith [hF.x21]) hcol (by linarith [hF.εσ, hF.σ1])
        (by exact_mod_cast hr1) (by rw [hm]; exact_mod_cast hrm) ?_ hqpos
      linarith

/-- The two values of `ii_e` at the one-unit purview `{k}`. -/
lemma iiE_single (T : UnitTPM N) (M : Finset (Fin N)) (m z : State N) (k : Fin N) :
    iiE T M m {k} z = effUnit T M m k (z k) *
      Real.logb 2 (effUnit T M m k (z k) / effUnit T ∅ m k (z k)) := by
  unfold iiE; rw [effRep_single, uncEffRep_single T M k z m]

theorem maxStates_single_iff (hC : EffC N) (hc : CoinAt N s K k w)
    (hcol : |effDevA w s ∅ s k| ≤ epsN N) (z : State N) :
    z ∈ maxEffStates (tpmOf (flipP s w)) (univ \ K) s {k} ↔ z k = teW w s k := by
  have hF := effC_facts hC
  set T := tpmOf (flipP s w) with hT
  set M := univ \ K with hMdef
  set f := fK w s K k with hfdef
  set ab := effDevA w s ∅ s k with habdef
  have hf := hc.posf
  obtain ⟨hσf, hfx, -⟩ := core_bounds hF hc.core
  rw [abs_of_pos hf] at hσf hfx
  have hab1 := (abs_le.1 hcol).1
  have hab2 := (abs_le.1 hcol).2
  have hεσ := hF.εσ
  have hσ1 := hF.σ1
  have hσ0 := hF.σ0
  have hx1 := hF.x21
  set g : Bool → ℝ := fun b => effUnit T M s k b * Real.logb 2 (effUnit T M s k b / effUnit T ∅ s k b)
    with hg
  have hii : ∀ z' : State N, iiE T M s {k} z' = g (z' k) := fun z' => iiE_single T M s z' k
  have hte : g (teW w s k) = (1 / 2 + f) * Real.logb 2 ((1 / 2 + f) / (1 / 2 + ab)) := by
    simp only [hg, hT, effUnit_te]; rfl
  have hnte : g (!teW w s k) = (1 / 2 - f) * Real.logb 2 ((1 / 2 - f) / (1 / 2 - ab)) := by
    simp only [hg, hT, effUnit_nte]; rfl
  have hgt : 0 < g (teW w s k) := by
    rw [hte]
    refine mul_pos (by linarith) (Real.logb_pos one_lt_two ?_)
    rw [one_lt_div (by linarith)]; linarith
  have hgn : g (!teW w s k) < 0 := by
    rw [hnte]
    refine mul_neg_of_pos_of_neg (by linarith) (Real.logb_neg one_lt_two ?_ ?_)
    · exact div_pos (by linarith) (by linarith)
    · rw [div_lt_one (by linarith)]; linarith
  have hb : ∀ b : Bool, b ≠ teW w s k → b = !teW w s k := fun b hb => by
    cases b <;> cases h : teW w s k <;> simp_all
  unfold maxEffStates
  rw [mem_argmaxSet]
  constructor
  · intro h
    by_contra hne
    have h1 := h (teW w s)
    rw [hii, hii, hb _ hne] at h1
    linarith
  · intro hzk z'
    rw [hii, hii, hzk]
    by_cases h' : z' k = teW w s k
    · rw [h']
    · rw [hb _ h']; linarith

end Single

/-! ### Blueprint statements -/

theorem eff_maxStates_single : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide)
    (w : Param N), GoodW3 N s r0 x σ w → CountFreshX N s r0 w → ∀ K ∈ famX3 N s r0 x σ w,
      ∀ k ∈ K, CoreAt N s K k 0 w → 0 < fK w s K k → ∀ z : State N,
        z ∈ maxEffStatesAt (tpmOf (flipP s w)) univ s (univ \ K) s {k} ↔ z k = teW w s k := by
  filter_upwards [ev_effC, eff_colDev] with N hC hcol s r0 x σ w hg hfr K hK k hk hcore hf z
  rw [maxEffStatesAt_univ]
  exact maxStates_single_iff hC ⟨famX3_card hK, hk, hcore, hf⟩ (hcol s r0 x σ w hg hfr s k) z

theorem eff_phi_single : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N),
    GoodW3 N s r0 x σ w → CountFreshX N s r0 w → ∀ K ∈ famX3 N s r0 x σ w, ∀ k ∈ K,
      CoreAt N s K k 0 w → 0 < fK w s K k → DleAt N s K k w → ∀ z : State N, z k = teW w s k →
        phiEatAt (tpmOf (flipP s w)) univ s (univ \ K) s {k} z =
          (1 / 2 + fK w s K k) *
            Real.logb 2 ((1 / 2 + fK w s K k) / (1 / 2 + effDevA w s ∅ s k)) := by
  filter_upwards [ev_effC, eff_subDev, eff_colDev] with N hC hsub hcol s r0 x σ w hg hfr K hK k hk
    hcore hf hD z hzk
  rw [phiEatAt_univ]
  exact phi_single_val hC (cnt_flipP_open hg hfr) ⟨famX3_card hK, hk, hcore, hf⟩ hD
    (fun A hA => hsub s r0 x σ w hg hfr A s k hA) (hcol s r0 x σ w hg hfr s k) z hzk

lemma phi1_ge (hF : EffF N) {f ab : ℝ} (hf : sigC N < f) (hfx : f ≤ 1 / 100)
    (hcol : |ab| ≤ epsN N) :
    f / (2 * Real.log 2) ≤ (1 / 2 + f) * Real.logb 2 ((1 / 2 + f) / (1 / 2 + ab)) := by
  have hab1 := (abs_le.1 hcol).1
  have hab2 := (abs_le.1 hcol).2
  have hεσ := hF.εσ
  have hσ1 := hF.σ1
  have hσ0 := hF.σ0
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc : 0 < 1 / 2 + ab := by linarith
  have hp : 0 < 1 / 2 + f := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hp hc)
  rw [inv_div] at h1
  have e : (1 / 2 + f) * (1 - (1 / 2 + ab) / (1 / 2 + f)) = f - ab := by
    rw [mul_sub, mul_one, mul_div_cancel₀ _ hp.ne']; ring
  have hl : f / 2 ≤ (1 / 2 + f) * Real.log ((1 / 2 + f) / (1 / 2 + ab)) := by
    have := mul_le_mul_of_nonneg_left h1 hp.le
    rw [e] at this; linarith
  calc f / (2 * Real.log 2) = (f / 2) / Real.log 2 := by ring
    _ ≤ ((1 / 2 + f) * Real.log ((1 / 2 + f) / (1 / 2 + ab))) / Real.log 2 :=
        div_le_div_of_nonneg_right hl hl2.le
    _ = (1 / 2 + f) * Real.logb 2 ((1 / 2 + f) / (1 / 2 + ab)) := by rw [Real.logb]; ring

theorem eff_phi_single_ge : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide)
    (w : Param N), GoodW3 N s r0 x σ w → CountFreshX N s r0 w → ∀ K ∈ famX3 N s r0 x σ w,
      ∀ k ∈ K, CoreAt N s K k 0 w → 0 < fK w s K k →
        fK w s K k / (2 * Real.log 2) ≤
          (1 / 2 + fK w s K k) *
            Real.logb 2 ((1 / 2 + fK w s K k) / (1 / 2 + effDevA w s ∅ s k)) := by
  filter_upwards [ev_effC, eff_colDev] with N hC hcol s r0 x σ w hg hfr K hK k hk hcore hf
  have hF := effC_facts hC
  obtain ⟨hσf, hfx, -⟩ := core_bounds hF hcore
  rw [abs_of_pos hf] at hσf hfx
  exact phi1_ge hF hσf (hfx.le.trans hF.x21) (hcol s r0 x σ w hg hfr s k)


end WP3

alias eff_maxStates_single := WP3.eff_maxStates_single
alias eff_phi_single := WP3.eff_phi_single
alias eff_phi_single_ge := WP3.eff_phi_single_ge

end Census
end IIT

#print axioms IIT.Census.WP3.phi_single_val
#print axioms IIT.Census.eff_maxStates_single
#print axioms IIT.Census.eff_phi_single
#print axioms IIT.Census.eff_phi_single_ge
