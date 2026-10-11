/-
Census of complexes, B1 development, module B4 (`B1-W4-B5.md`, which supersedes blueprint B4):
every candidate of size `≥ 5` is below `(12/25) β` on the lower-bound event.

Notation as in `B1Couple` (flipped coordinates `w = flipP s z`, `y_{r,i} = clamp01 (w r i)`); the
two fixed rows are `tc` and `s` (the current state as a row), `H = Pw w tc + Pw w s`.

Contents.
0. Definitions of W4 2 and 4.3: `D1`, `etaB`, `deltaH`, the events `G2` (= g2), `EH`, `EW`, `ECr`,
   `ECh`, `EF a`, and `E5 N s tc = G2 ∩ EH ∩ EW ∩ ECr ∩ ECh ∩ EF tc ∩ EF s`; `measurableSet_E5`.
1. Helpers: `ev_D1_pow` (`(cN)^{D1 N} ≤ e^{εN}` eventually), `tendsto_D1_geom`, and the count
   `card_bigM_le`: `#{M : K2N N < |M|} ≤ e N^{D1 N}`.
2. Failure probabilities (certificate C17): P-EH `cubeM_not_EH` (Hoeffding, local copy of B3's EH),
   P-EW `cubeM_G2_not_EW` (Bernstein with the full row product truncated at `τ`), P-ECr
   `cubeM_not_ECr` (Lemma JP + Chernoff with `θ = 5`), P-EF `cubeM_not_EF` (JP + Markov, `θ = 1`),
   P-ECh `cubeM_not_ECh` (Chebyshev on the pattern sum), and the total
   `cubeM_not_E5_le : 1 ≤ N → EWnum N → cubeM N (E5 N s tc)ᶜ ≤ ofReal (fB5 N)`, `tendsto_fB5`.
3. Proposition M (`propM1`, `propM2`, `propM3`), Corollary Mid (`corMid`), Proposition KT
   (`propKT`), Corollary KT-LB (`corKTLB`), with `ε_k, δ_k, L_k, ρ_k, fl_k` = `epsK, deltaK, LK,
   rhoK, flK`.
4. Theorem B5 (`thmB5_det`, deterministic; `thmB5`, `∀ᶠ` form): `φ_s(S) ≤ e^{-N/4}` for
   `K2N N < |S| < N`.
5. The eventual inequalities of W4 4.7 (and the EW budget), collected in `W4Num N`; `ev_W4Num`.
6. Theorem W4: `thmW4_det` (deterministic core), `thmW4` (the CPL bound
   `≤ cubeM {¬ GoodW} + cubeM E5ᶜ`), `thmW4_bound` (`≤ fGood N + fB5 N`) and
   `tendsto_fGood_add_fB5`; the `∀ᶠ` forms `corMid_ev`, `corKTLB_ev`.

Deviations from W4 (all minimal; no W4 statement was found false):
* EH (B3 is not available): a local copy, for every subcube (no `D0` restriction), with
  `deltaH N d = 2 √(N / 2^d)`; failure `≤ 2 N (4 e^{-8})^N` (`fEH`).
* P-ECr: the fifth moment is bounded by `E max(2A,1)^5 ≤ 1 + E(U+U')^5 = 4` (Jensen pairing in
  power-mean form, `pow_sum_div_card_le_sum_pow`) instead of `47/14`; the rate
  `5·21/50 - ln 4 - ln 2 ≈ 0.0206 > 0` suffices for a `∀ᶠ` statement, so (C17a) is not needed.
  The level `21/50` of ECr is unchanged.
* P-EF: `E max(2A⁺,1) ≤ 3/2` is proved through `max(u+v,1) ≤ 1 + uv ≤ 1 + (one entry)`
  (no `7/6` moment needed); (C17b) is `three_halves_lt_exp`.
* P-EW needs the eventual budget `EWnum N` (`16 N 2^{D1}(σ_N + τ) + (2/3)^N/τ ≤ etaB N`), so the
  bound on `cubeM (E5 N s tc)ᶜ` is stated for `N ≥ 1` with `EWnum N` (true eventually, `ev_EWnum`).
* `fB5` has the form proved here: `fg2 + 2(4e^{-6})^N + fEH + e (N/a)^{D1}(2a)^N
  + 16 e (12N/7)^{D1}(7/12)^N + 2 e (N/b)^{D1} b^N` with `a = 4e^{-21/10}`, `b = (3/2)e^{-43/100}`.
* Prop M / KT are stated with the explicit `L_k` and the hypothesis `0 < L_k` (in place of
  "`N ≥ N0`"), for general fixed rows `{tc, u}` and `GoodW N s0 w̃` with any `s0`.
* Cor Mid (deterministic) assumes the level facts `L_k ≥ 6/25`, `ρ_k ≤ 1/2`, `Zs w ≤ 201/100`
  (W4: `0.235`, `1.149`, `2.001`); `corMid_ev` derives them from `H ≤ N^{-3}` for
  `2 ≤ |S| ≤ K2N N`. The proof gives `8 k 2^{-k}`.
* Cor KT-LB (deterministic) takes the EV1/EV5 levels at `ε = 10^{-4}` as hypotheses and
  `P_s ≤ 10^{-4} P_tc` (from `P_s ≤ 2^{-N/3}`, `P_tc ≥ N^9 σ_N`). EV5 is used as
  `k 2^{-k} fl_k ≤ 458 N^2 σ_N` (`flK_bound`); the constant chain is `e^{ρ_k} ≤ e^{0.108} ≤ 1.1141`,
  `k 2^{-k}(1 - 2^{1-k}) ≤ 75/512` (the `k = 5` value), `ln 2 > 0.6931`, total `≈ 0.4726 ≤ 12/25`.
* Theorem B5: the log-ratio is bounded through `colMean ≥ 1/4` (`pos log₂ ≤ 2`, W4: `1/2 - 1/400`,
  `≤ 1.01`), the normaliser uses `ρ0^{10} ≤ 1/8` (`k ≥ 10`), and the back probability is
  `≤ 4 ρ0^k` with `ρ0 = e^{43/100}/2`, `ρ0 e^{1/4} < 1` (`e^{0.68} < 2`, (C17c)). The
  conclusion `e^{-N/4}` is unchanged. `tc ≠ s` is not assumed (implied by `N ≤ 3 ham tc s`).
* Theorem W4 is stated for the row values `f : {tc, s} → Fin N → ℝ`, with the row weights of the
  glued parameter written `∏ j, clamp01 (f ⟨tc, _⟩ j)`; `2^{-N/3}` is the real power
  `(2 : ℝ) ^ (-(N : ℝ) / 3)`. The null set "`v ∉ openCube`" is absorbed by taking
  `E = {GoodW} ∩ E5 ∩ openCube` in CPL (`cubeM (openCube N)ᶜ = 0`), so the bound is exactly
  `cubeM {¬ GoodW N s} + cubeM (E5 N s tc)ᶜ`.
-/
import IIT.Census.B1Couple
import IIT.Census.B1Chernoff
import IIT.Census.BigPhiGood
import IIT.Census.UnivZero

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

noncomputable section

variable {N : ℕ}

/-! ## 0. Definitions (W4, Sections 2 and 4.3) -/

/-- `K2N N = N - D1 N`: near-universe candidates have `N - |S| < D1 N`. -/
def D1 (N : ℕ) : ℕ := 4 * Nat.log 2 N + 16

/-- The relative precision of the block masses. -/
def etaB (N : ℕ) : ℝ := Real.exp (-(N : ℝ) / 10)

/-- The Hoeffding radius of a subcube mean of dimension `d`. -/
def deltaH (N d : ℕ) : ℝ := 2 * Real.sqrt ((N : ℝ) / 2 ^ d)

lemma K2N_eq_sub_D1 (N : ℕ) : K2N N = N - D1 N := rfl

lemma sub_card_lt_D1 {M : Finset (Fin N)} (h : K2N N < M.card) : N - M.card < D1 N := by
  have := card_le_N M
  rw [K2N_eq_sub_D1] at h
  omega

/-- The event `g2` as a set. -/
def G2 (N : ℕ) : Set (Param N) := {w | ∀ i r, Qw w i r ≤ tauN N}

/-- **EH** (Hoeffding for every subcube mean, `C = 1`). -/
def EH (N : ℕ) : Set (Param N) :=
  {w | ∀ (M : Finset (Fin N)) (m : State N) (i : Fin N),
    |colMean w M m i - 1 / 2| ≤ deltaH N (N - M.card)}

/-- **EW** (block masses of the near-universe candidates). -/
def EW (N : ℕ) : Set (Param N) :=
  {w | ∀ (S : Finset (Fin N)) (r : State N), K2N N < S.card → S.card < N →
    |blockP w S r - (1 / 2 : ℝ) ^ (N - S.card)| ≤ etaB N * (1 / 2 : ℝ) ^ (N - S.card)}

/-- **ECr** (generic Cramér event, level `21/50`). -/
def ECr (N : ℕ) : Set (Param N) :=
  {w | ∀ (M : Finset (Fin N)) (m : State N), K2N N < M.card → M.card < N →
    ∑ i ∈ M, Real.log (max (2 * colMean w M m i) 1) ≤ 21 / 50 * M.card}

/-- **ECh** (normaliser). -/
def ECh (N : ℕ) : Set (Param N) :=
  {w | ∀ S : Finset (Fin N), K2N N < S.card → S.card < N →
    3 / 4 * (2 : ℝ) ^ (N - S.card) ≤ ∑ t : State N, ∏ i ∈ S, colMean w S t i}

/-- **EF(a)** (heavy pattern through the fixed row `a`, level `43/100`; it does not read row `a`). -/
def EF (N : ℕ) (a : State N) : Set (Param N) :=
  {w | ∀ M : Finset (Fin N), K2N N < M.card → M.card < N →
    ∑ i ∈ M, Real.log (max (2 * colMeanPlus w M a i) 1) ≤ 43 / 100 * M.card}

/-- **E5** `= g2 ∩ EH ∩ EW ∩ ECr ∩ ECh ∩ EF tc ∩ EF s`. -/
def E5 (N : ℕ) (s tc : State N) : Set (Param N) :=
  G2 N ∩ EH N ∩ EW N ∩ ECr N ∩ ECh N ∩ EF N tc ∩ EF N s

/-! ### Measurability of `E5` -/

section Meas

lemma measurable_log_max_two_mul {f : Param N → ℝ} (hf : Measurable f) :
    Measurable fun w => Real.log (max (2 * f w) 1) :=
  Real.measurable_log.comp ((hf.const_mul 2).max measurable_const)

lemma measurableSet_G2 : MeasurableSet (G2 N) := by
  rw [G2, measurableSet_setOfPred]
  exact Measurable.forall fun i => Measurable.forall fun r =>
    b1c_measurable_le (measurable_Qw i r) measurable_const

lemma measurableSet_EH : MeasurableSet (EH N) := by
  rw [EH, measurableSet_setOfPred]
  exact Measurable.forall fun M => Measurable.forall fun m => Measurable.forall fun i =>
    b1c_measurable_le (measurable_abs_comp ((measurable_colMean M m i).sub_const _))
      measurable_const

lemma measurableSet_EW : MeasurableSet (EW N) := by
  rw [EW, measurableSet_setOfPred]
  exact Measurable.forall fun S => Measurable.forall fun r => measurable_const.imp
    (measurable_const.imp (b1c_measurable_le
      (measurable_abs_comp ((measurable_blockP S r).sub_const _)) measurable_const))

lemma measurableSet_ECr : MeasurableSet (ECr N) := by
  rw [ECr, measurableSet_setOfPred]
  exact Measurable.forall fun M => Measurable.forall fun m => measurable_const.imp
    (measurable_const.imp (b1c_measurable_le (Finset.measurable_sum _ fun i _ =>
      measurable_log_max_two_mul (measurable_colMean M m i)) measurable_const))

lemma measurableSet_ECh : MeasurableSet (ECh N) := by
  rw [ECh, measurableSet_setOfPred]
  exact Measurable.forall fun S => measurable_const.imp (measurable_const.imp
    (b1c_measurable_le measurable_const (Finset.measurable_sum _ fun t _ =>
      Finset.measurable_prod _ fun i _ => measurable_colMean S t i)))

lemma measurableSet_EF (a : State N) : MeasurableSet (EF N a) := by
  rw [EF, measurableSet_setOfPred]
  exact Measurable.forall fun M => measurable_const.imp
    (measurable_const.imp (b1c_measurable_le (Finset.measurable_sum _ fun i _ =>
      measurable_log_max_two_mul (measurable_colMeanPlus M a i)) measurable_const))

theorem measurableSet_E5 (s tc : State N) : MeasurableSet (E5 N s tc) :=
  ((((((measurableSet_G2.inter measurableSet_EH).inter measurableSet_EW).inter
    measurableSet_ECr).inter measurableSet_ECh).inter (measurableSet_EF tc)).inter
    (measurableSet_EF s))

end Meas

/-! ## 1. Asymptotic and counting helpers -/

section Helpers

/-- `(c N)^{D1 N} ≤ e^{ε N}` eventually (`D1 N = O(log N)`). -/
lemma ev_D1_pow {c : ℝ} (hc : 1 ≤ c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (c * N) ^ D1 N ≤ Real.exp (ε * N) := by
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  filter_upwards [eventually_ge_atTop 1,
    ev_quad_half_comp tendsto_natLog2 4 (20 + 4 * Real.log c) (16 + 16 * Real.log c) hε]
    with N hN hq
  set ℓ := Nat.log 2 N with hℓ
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hcN : 0 < c * N := by positivity
  have hlogN := log_le_natLog hN
  rw [← hℓ] at hlogN
  have h2ℓ : (2 : ℝ) ^ ℓ ≤ N := by exact_mod_cast two_pow_natLog_le hN
  have hp : (0 : ℝ) < (1 / 2) ^ ℓ := by positivity
  have hpq : (2 : ℝ) ^ ℓ * (1 / 2) ^ ℓ = 1 := by rw [← mul_pow]; norm_num
  have key : (4 * (ℓ : ℝ) + 16) * (Real.log c + ℓ + 1) ≤ ε * N := by
    have e : (4 * (ℓ : ℝ) + 16) * (Real.log c + ℓ + 1) =
        (4 * (ℓ : ℝ) ^ 2 + (20 + 4 * Real.log c) * ℓ + (16 + 16 * Real.log c)) := by ring
    rw [e]
    have hq' : (4 * (ℓ : ℝ) ^ 2 + (20 + 4 * Real.log c) * ℓ + (16 + 16 * Real.log c)) * (1 / 2) ^ ℓ
        * 2 ^ ℓ ≤ ε * 2 ^ ℓ := by
      have := mul_le_mul_of_nonneg_right hq.le (by positivity : (0 : ℝ) ≤ 2 ^ ℓ)
      linarith
    rw [mul_assoc, mul_comm ((1 / 2 : ℝ) ^ ℓ), hpq, mul_one] at hq'
    nlinarith
  calc (c * N) ^ D1 N = Real.exp (D1 N * Real.log (c * N)) := by
        rw [← Real.log_pow, Real.exp_log (pow_pos hcN _)]
    _ ≤ Real.exp (ε * N) := by
        refine Real.exp_le_exp.2 ?_
        rw [Real.log_mul (by positivity) (by positivity)]
        have hD : ((D1 N : ℕ) : ℝ) = 4 * (ℓ : ℝ) + 16 := by
          unfold D1; push_cast; rfl
        rw [hD]
        have : Real.log c + Real.log N ≤ Real.log c + ℓ + 1 := by linarith
        nlinarith

/-- `C (c N)^{D1 N} q^N → 0` for `0 < q < 1`. -/
lemma tendsto_D1_geom {c q : ℝ} (hc : 1 ≤ c) (hq0 : 0 < q) (hq1 : q < 1) {C : ℝ} (hC : 0 ≤ C) :
    Tendsto (fun N : ℕ => C * (c * N) ^ D1 N * q ^ N) atTop (𝓝 0) := by
  set q' := (q + 1) / 2 with hq'
  have hqq : q < q' := by rw [hq']; linarith
  have hq'1 : q' < 1 := by rw [hq']; linarith
  have hε : 0 < Real.log (q' / q) := Real.log_pos (by rw [lt_div_iff₀ hq0]; linarith)
  have hlim : Tendsto (fun N : ℕ => C * q' ^ N) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) hq'1).const_mul C
    rwa [mul_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards with N
    have : (0 : ℝ) ≤ c * N := by positivity
    positivity
  · filter_upwards [ev_D1_pow hc hε] with N hN
    have hexp : Real.exp (Real.log (q' / q) * N) = (q' / q) ^ N := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log (div_pos (by linarith) hq0)]
    rw [hexp] at hN
    calc C * (c * N) ^ D1 N * q ^ N ≤ C * (q' / q) ^ N * q ^ N := by gcongr
      _ = C * q' ^ N := by
          rw [mul_assoc, ← mul_pow, div_mul_cancel₀ _ hq0.ne']

/-- The number of large candidates: `#{M : K2N N < |M|} ≤ e N^{D1 N}`. -/
lemma card_bigM_le (hN : 1 ≤ N) :
    ((univ.filter fun M : Finset (Fin N) => K2N N < M.card).card : ℝ) ≤
      Real.exp 1 * (N : ℝ) ^ D1 N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hpt : ∀ M : Finset (Fin N), (if K2N N < M.card then (1 : ℝ) else 0) ≤
      (N : ℝ) ^ D1 N * (1 / (N : ℝ)) ^ (N - M.card) := by
    intro M
    split_ifs with h
    · have hlt := sub_card_lt_D1 h
      have e : (N : ℝ) ^ D1 N = (N : ℝ) ^ (N - M.card) * (N : ℝ) ^ (D1 N - (N - M.card)) := by
        rw [← pow_add]; congr 1; omega
      rw [e, mul_comm ((N : ℝ) ^ (N - M.card)), mul_assoc, ← mul_pow, mul_one_div_cancel hN0.ne',
        one_pow, mul_one]
      exact one_le_pow₀ hN'
    · positivity
  calc ((univ.filter fun M : Finset (Fin N) => K2N N < M.card).card : ℝ)
      = ∑ M : Finset (Fin N), (if K2N N < M.card then (1 : ℝ) else 0) := by
        rw [Finset.natCast_card_filter]
    _ ≤ ∑ M : Finset (Fin N), (N : ℝ) ^ D1 N * (1 / (N : ℝ)) ^ (N - M.card) :=
        sum_le_sum fun M _ => hpt M
    _ = (N : ℝ) ^ D1 N * (1 + 1 / (N : ℝ)) ^ N := by
        rw [← mul_sum]
        congr 1
        have h := Finset.sum_pow_mul_eq_add_pow (1 : ℝ) (1 / (N : ℝ)) (univ : Finset (Fin N))
        rw [Finset.powerset_univ, card_univ, Fintype.card_fin] at h
        simpa using h
    _ ≤ (N : ℝ) ^ D1 N * Real.exp 1 := by
        gcongr
        calc (1 + 1 / (N : ℝ)) ^ N ≤ Real.exp (1 / N) ^ N := by
              gcongr
              linarith [Real.add_one_le_exp (1 / (N : ℝ))]
          _ = Real.exp 1 := by
              rw [← Real.exp_nat_mul, mul_one_div_cancel hN0.ne']
    _ = _ := mul_comm _ _

/-- Union over the large candidates. -/
lemma cubeM_iUnion_bigM_le (hN : 1 ≤ N) (X : Finset (Fin N) → Set (Param N)) {b : ℝ}
    (hb : 0 ≤ b) (h : ∀ M, K2N N < M.card → cubeM N (X M) ≤ ENNReal.ofReal b)
    (h0 : ∀ M, ¬ K2N N < M.card → X M = ∅) :
    cubeM N (⋃ M, X M) ≤ ENNReal.ofReal (Real.exp 1 * (N : ℝ) ^ D1 N * b) := by
  calc cubeM N (⋃ M, X M) ≤ ∑ M, cubeM N (X M) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ M : Finset (Fin N), ENNReal.ofReal (if K2N N < M.card then b else 0) := by
        refine sum_le_sum fun M _ => ?_
        split_ifs with hM
        · exact h M hM
        · rw [h0 M hM, measure_empty]; exact zero_le
    _ = ENNReal.ofReal (∑ M : Finset (Fin N), if K2N N < M.card then b else 0) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun M _ => by split_ifs <;> simp [hb]]
    _ ≤ ENNReal.ofReal (Real.exp 1 * (N : ℝ) ^ D1 N * b) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (card_bigM_le hN) hb

/-- `C N^p e^{-cN} < ε` eventually. -/
lemma ev_poly_exp (p : ℕ) (C : ℝ) {c : ℝ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ p * Real.exp (-(c * N)) < ε := by
  filter_upwards [ev_poly_geom p (r := Real.exp (-c)) (Real.exp_pos _).le
    (Real.exp_lt_one_iff.2 (by linarith)) C hε] with N hN
  rwa [show -(c * (N : ℝ)) = N * (-c) by ring, Real.exp_nat_mul]

end Helpers

/-! ## 2. The failure probabilities of the uniform-law events (certificate C17) -/

section Prob

/-- `E clamp01 (w r i) = 1/2`. -/
lemma integral_clamp_entry (r : State N) (i : Fin N) :
    ∫ w, clamp01 (w r i) ∂cubeM N = 1 / 2 := by
  rw [integral_row_eval (g := fun v => clamp01 (v i))
    (clamp01_measurable.comp (measurable_pi_apply i)).aestronglyMeasurable r]
  unfold rowM
  rw [integral_pi_eval unif clamp01_measurable.aestronglyMeasurable i]
  have := integral_cl_pow 1
  simp only [pow_one] at this
  rw [this]; norm_num

/-! ### P-EH -/

/-- One subcube mean: `|colMean - 1/2| > deltaH` has probability at most `2 e^{-8N}`. -/
lemma cubeM_colMean_dev (M : Finset (Fin N)) (m : State N) (i : Fin N) :
    cubeM N {w | ¬ |colMean w M m i - 1 / 2| ≤ deltaH N (N - M.card)} ≤
      ENNReal.ofReal (2 * Real.exp (-8 * N)) := by
  set C := agree M m with hC
  set n : ℝ := (2 : ℝ) ^ (N - M.card) with hn
  have hcard : (C.card : ℝ) = n := by rw [hC, card_agree]; push_cast; rfl
  have hnpos : 0 < n := by positivity
  have hmf : ∀ _r : State N, Measurable fun v : Fin N → ℝ => clamp01 (v i) :=
    fun _ => clamp01_measurable.comp (measurable_pi_apply i)
  have hind := iIndepFun_rows (fun _ v => clamp01 (v i)) hmf
  have hmeas : ∀ r, AEMeasurable (fun w : Param N => clamp01 (w r i)) (cubeM N) :=
    fun r => ((hmf r).comp (measurable_pi_apply r)).aemeasurable
  have hb : ∀ r ∈ C, ∀ᵐ w ∂cubeM N, clamp01 (w r i) ∈ Set.Icc 0 ((fun _ => (1 : ℝ)) r) :=
    fun r _ => ae_of_all _ fun w => ⟨clamp01_nonneg _, clamp01_le_one _⟩
  set δ := deltaH N (N - M.card) with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ, deltaH]; positivity
  have hε : 0 ≤ n * δ := by positivity
  have h := hoeffding_abs (μ := cubeM N) (X := fun r (w : Param N) => clamp01 (w r i)) C hind hmeas
    hb hε
  simp only [integral_clamp_entry, one_pow, sum_const, nsmul_eq_mul, mul_one, hcard] at h
  have hsub : {w : Param N | ¬ |colMean w M m i - 1 / 2| ≤ δ} ⊆
      {w | n * δ ≤ |∑ r ∈ C, (clamp01 (w r i) - 1 / 2)|} := by
    intro w hw
    simp only [Set.mem_ofPred_eq, not_le] at hw ⊢
    have e : ∑ r ∈ C, (clamp01 (w r i) - 1 / 2) = n * (colMean w M m i - 1 / 2) := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcard, colMean, ← hC, ← hn]
      field_simp
    rw [e, abs_mul, abs_of_pos hnpos]
    exact (mul_lt_mul_of_pos_left hw hnpos).le
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
  congr 2
  have hsq : δ ^ 2 = 4 * ((N : ℝ) / n) := by
    rw [hδ, deltaH, mul_pow, Real.sq_sqrt (by positivity), ← hn]
    norm_num
  rw [mul_pow, hsq]
  field_simp
  ring

/-- The failure probability of `EH`. -/
def fEH (N : ℕ) : ℝ := 2 * N * (4 * Real.exp (-8)) ^ N

/-- **P-EH.** -/
theorem cubeM_not_EH : cubeM N (EH N)ᶜ ≤ ENNReal.ofReal (fEH N) := by
  have hset : (EH N)ᶜ = ⋃ M : Finset (Fin N), ⋃ m : State N, ⋃ i : Fin N,
      {w | ¬ |colMean w M m i - 1 / 2| ≤ deltaH N (N - M.card)} := by
    ext w; simp [EH]
  rw [hset]
  refine (cubeM_iUnion_le _ fun M => cubeM_iUnion_le _ fun m =>
    cubeM_iUnion_le _ fun i => cubeM_colMean_dev M m i).trans (ENNReal.ofReal_le_ofReal ?_)
  simp only [Fintype.card_finset, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool,
    Nat.cast_pow, Nat.cast_ofNat]
  apply le_of_eq
  unfold fEH
  rw [mul_pow, show -8 * (N : ℝ) = N * (-8) by ring, Real.exp_nat_mul,
    show (4 : ℝ) ^ N = 2 ^ N * 2 ^ N by rw [← mul_pow]; norm_num]
  ring

theorem tendsto_fEH : Tendsto fEH atTop (𝓝 0) := by
  have h4 : 4 * Real.exp (-8) < 1 := by
    have h := Real.add_one_le_exp 8
    rw [Real.exp_neg]
    have hp := Real.exp_pos 8
    rw [← div_eq_mul_inv, div_lt_one hp]
    linarith
  have h := (tendsto_self_mul_const_pow_of_lt_one (r := 4 * Real.exp (-8)) (by positivity)
    h4).const_mul 2
  rw [mul_zero] at h
  refine h.congr fun N => ?_
  unfold fEH; ring

/-! ### P-EW: Bernstein for the truncated full row product -/

/-- The full row product, truncated at `tauN N`. -/
def rowTP (N : ℕ) (v : Fin N → ℝ) : ℝ := min (∏ j, clamp01 (v j)) (tauN N)

/-- Its mean. -/
def muTP (N : ℕ) : ℝ := ∫ v, rowTP N v ∂rowM N

lemma measurable_rowTP : Measurable (rowTP N) := measurable_rowPw.min measurable_const

lemma rowTP_nonneg (v : Fin N → ℝ) : 0 ≤ rowTP N v :=
  le_min (prod_nonneg fun _ _ => clamp01_nonneg _) (tauN_pos N).le

lemma rowTP_le_tau (v : Fin N → ℝ) : rowTP N v ≤ tauN N := min_le_right _ _

lemma rowTP_le_P (v : Fin N → ℝ) : rowTP N v ≤ ∏ j, clamp01 (v j) := min_le_left _ _

lemma integrable_rowTP : Integrable (rowTP N) (rowM N) :=
  integrable_rowM measurable_rowTP (tauN N) fun v => by
    rw [abs_of_nonneg (rowTP_nonneg v)]; exact rowTP_le_tau v

lemma abs_rowP_pow_le (p : ℕ) (v : Fin N → ℝ) : |(∏ j, clamp01 (v j)) ^ p| ≤ 1 := by
  have h0 : 0 ≤ ∏ j, clamp01 (v j) := prod_nonneg fun _ _ => clamp01_nonneg _
  rw [abs_of_nonneg (pow_nonneg h0 p)]
  exact pow_le_one₀ h0 (prod_le_one (fun _ _ => clamp01_nonneg _) fun _ _ => clamp01_le_one _)

lemma integrable_rowPp (p : ℕ) :
    Integrable (fun v : Fin N → ℝ => (∏ j, clamp01 (v j)) ^ p) (rowM N) :=
  integrable_rowM (measurable_rowPw.pow_const p) 1 fun v => abs_rowP_pow_le p v

lemma muTP_nonneg : 0 ≤ muTP N := integral_nonneg fun v => rowTP_nonneg v

lemma muTP_le_tau : muTP N ≤ tauN N := by
  have h := integral_mono (integrable_rowTP (N := N)) (integrable_const (tauN N)) fun v =>
    rowTP_le_tau v
  unfold muTP
  simpa using h

lemma muTP_le_half : muTP N ≤ (1 / 2 : ℝ) ^ N := by
  have h := integral_mono (integrable_rowTP (N := N)) (integrable_rowPp (N := N) 1) fun v => by
    simp only [pow_one]; exact rowTP_le_P v
  rw [integral_rowP_pow'] at h
  norm_num at h
  unfold muTP
  norm_num
  exact h

/-- `E min(P, τ) ≥ E P - E P²/τ`. -/
lemma half_sub_le_muTP : (1 / 2 : ℝ) ^ N - (1 / 3 : ℝ) ^ N / tauN N ≤ muTP N := by
  have hτ := tauN_pos N
  have hpt : ∀ v : Fin N → ℝ, (∏ j, clamp01 (v j)) - (∏ j, clamp01 (v j)) ^ 2 / tauN N ≤
      rowTP N v := by
    intro v
    set P := ∏ j, clamp01 (v j)
    have hP0 : 0 ≤ P := prod_nonneg fun _ _ => clamp01_nonneg _
    unfold rowTP
    rcases le_total P (tauN N) with h | h
    · rw [min_eq_left h]
      have : 0 ≤ P ^ 2 / tauN N := by positivity
      linarith
    · rw [min_eq_right h]
      have : P ≤ P ^ 2 / tauN N := by
        rw [le_div_iff₀ hτ, sq]; exact mul_le_mul_of_nonneg_left h hP0
      linarith
  have hint : Integrable (fun v : Fin N → ℝ =>
      (∏ j, clamp01 (v j)) - (∏ j, clamp01 (v j)) ^ 2 / tauN N) (rowM N) := by
    have h1 := integrable_rowPp (N := N) 1
    simp only [pow_one] at h1
    exact h1.sub ((integrable_rowPp 2).div_const _)
  have h := integral_mono hint integrable_rowTP hpt
  rw [integral_sub _ ((integrable_rowPp 2).div_const _), integral_div] at h
  · have e1 := integral_rowP_pow' (N := N) 1
    have e2 := integral_rowP_pow' (N := N) 2
    simp only [pow_one] at e1
    rw [e1, e2] at h
    unfold muTP
    norm_num at h ⊢
    exact h
  · have h1 := integrable_rowPp (N := N) 1
    simp only [pow_one] at h1
    exact h1

lemma integral_sq_rowTP_sub : ∫ v, (rowTP N v - muTP N) ^ 2 ∂rowM N ≤ (1 / 3 : ℝ) ^ N := by
  have h1 := variance_eq_integral (μ := rowM N) (measurable_rowTP (N := N)).aemeasurable
  have h2 := variance_le_expectation_sq (μ := rowM N) (measurable_rowTP (N := N)).aestronglyMeasurable
  rw [h1] at h2
  refine h2.trans ?_
  have h3 : ∫ v, (rowTP N ^ 2) v ∂rowM N ≤ ∫ v, (∏ j, clamp01 (v j)) ^ 2 ∂rowM N :=
    integral_mono (integrable_rowM (measurable_rowTP.pow_const 2) (tauN N ^ 2) fun v => by
        simp only [Pi.pow_apply]
        rw [abs_of_nonneg (pow_nonneg (rowTP_nonneg v) 2)]
        exact pow_le_pow_left₀ (rowTP_nonneg v) (rowTP_le_tau v) 2)
      (integrable_rowPp 2) (fun v => by
        simp only [Pi.pow_apply]
        exact pow_le_pow_left₀ (rowTP_nonneg v) (rowTP_le_P v) 2)
  rw [integral_rowP_pow'] at h3
  norm_num at h3 ⊢
  exact h3

lemma abs_rowTP_sub_le (v : Fin N → ℝ) : |rowTP N v - muTP N| ≤ tauN N :=
  abs_sub_le_iff.2 ⟨by linarith [rowTP_le_tau v, muTP_nonneg (N := N)],
    by linarith [rowTP_nonneg v, muTP_le_tau (N := N)]⟩

/-- **Bernstein over the rows** for the truncated full row products of a row set. -/
theorem cubeM_truncP_dev (s : Finset (State N)) {L V : ℝ} (hL : 1 ≤ L)
    (hV : (s.card : ℝ) * (1 / 3 : ℝ) ^ N ≤ V) :
    cubeM N {w | 16 * L * max (Real.sqrt V) (tauN N) ≤
      |∑ r ∈ s, (rowTP N (w r) - muTP N)|} ≤ ENNReal.ofReal (2 * Real.exp (-6 * L)) := by
  have hmf : ∀ _r : State N, Measurable fun v : Fin N → ℝ => rowTP N v - muTP N :=
    fun _ => measurable_rowTP.sub_const _
  have hind := iIndepFun_rows (fun _ v => rowTP N v - muTP N) hmf
  have hmeas : ∀ r, AEMeasurable (fun w : Param N => rowTP N (w r) - muTP N) (cubeM N) :=
    fun r => ((hmf r).comp (measurable_pi_apply r)).aemeasurable
  have hb : ∀ r ∈ s, ∀ᵐ w ∂cubeM N, |rowTP N (w r) - muTP N| ≤ tauN N :=
    fun r _ => ae_of_all _ fun w => abs_rowTP_sub_le _
  have h0 : ∀ r ∈ s, ∫ w, (rowTP N (w r) - muTP N) ∂cubeM N = 0 := by
    intro r _
    rw [integral_row_eval (g := fun v => rowTP N v - muTP N) (hmf r).aestronglyMeasurable r,
      integral_sub integrable_rowTP (integrable_const _), integral_const]
    simp [muTP]
  have hV' : ∑ r ∈ s, ∫ w, (rowTP N (w r) - muTP N) ^ 2 ∂cubeM N ≤ V := by
    calc ∑ r ∈ s, ∫ w, (rowTP N (w r) - muTP N) ^ 2 ∂cubeM N
        ≤ ∑ _r ∈ s, (1 / 3 : ℝ) ^ N := by
          refine sum_le_sum fun r _ => ?_
          rw [integral_row_eval (g := fun v => (rowTP N v - muTP N) ^ 2)
            ((hmf r).pow_const 2).aestronglyMeasurable r]
          exact integral_sq_rowTP_sub
      _ = s.card * (1 / 3 : ℝ) ^ N := by rw [sum_const, nsmul_eq_mul]
      _ ≤ V := hV
  have hpos : 0 < max (Real.sqrt V) (tauN N) := lt_max_of_lt_right (tauN_pos N)
  have h := bernstein_L (X := fun r (w : Param N) => rowTP N (w r) - muTP N)
    s hind hmeas hL hpos hb h0 hV'
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal h

/-- The eventual inequality behind P-EW (`EV2`-type). -/
def EWnum (N : ℕ) : Prop :=
  16 * N * (2 : ℝ) ^ D1 N * (sigN N + tauN N) + (2 / 3 : ℝ) ^ N / tauN N ≤ etaB N

/-- One block: on `g2`, `|blockP - 2^{-d}| > η 2^{-d}` has probability at most `2 e^{-6N}`. -/
lemma cubeM_blockP_bad (hN : 1 ≤ N) (hnum : EWnum N) (S : Finset (Fin N)) (r0 : State N)
    (hk : K2N N < S.card) :
    cubeM N {w | w ∈ G2 N ∧ ¬ |blockP w S r0 - (1 / 2 : ℝ) ^ (N - S.card)| ≤
      etaB N * (1 / 2 : ℝ) ^ (N - S.card)} ≤ ENNReal.ofReal (2 * Real.exp (-6 * N)) := by
  set s := agree Sᶜ r0 with hs
  set k := S.card with hkdef
  have hkN : k ≤ N := card_le_N S
  have hd := sub_card_lt_D1 hk
  have hcard : (s.card : ℝ) = (2 : ℝ) ^ k := by
    rw [hs, card_agree, card_compl, Fintype.card_fin, Nat.sub_sub_self hkN]; push_cast; rfl
  set V : ℝ := (2 : ℝ) ^ k * (1 / 3 : ℝ) ^ N with hV
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine (measure_mono ?_).trans (cubeM_truncP_dev s hN' (V := V) (by rw [hcard]))
  rintro w ⟨hg2, hbad⟩
  simp only [Set.mem_ofPred_eq]
  have hτ := tauN_pos N
  set u : ℝ := (1 / 2 : ℝ) ^ (N - k) with hu
  have hu0 : 0 < u := by positivity
  have h2u : (2 : ℝ) ^ (N - k) * u = 1 := by rw [hu, ← mul_pow]; norm_num
  have hku : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ N = u := by
    rw [hu, show N = (N - k) + k by omega, pow_add, show N - k + k - k = N - k by omega]
    rw [← mul_assoc, mul_comm ((2 : ℝ) ^ k), mul_assoc, ← mul_pow]; norm_num
  have hsum : ∑ r ∈ s, (rowTP N (w r) - muTP N) = blockP w S r0 - (2 : ℝ) ^ k * muTP N := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcard, blockP]
    congr 1
    refine sum_congr rfl fun r _ => ?_
    unfold rowTP
    exact min_eq_left (Pw_le_tauN_of_g2 hg2 r)
  rw [hsum]
  -- the mean of the truncated block sum
  have hmu1 := muTP_le_half (N := N)
  have hmu2 := half_sub_le_muTP (N := N)
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hB1 : (2 : ℝ) ^ k * muTP N ≤ u := by
    rw [← hku]; exact mul_le_mul_of_nonneg_left hmu1 h2k.le
  have hB2 : u - (2 : ℝ) ^ k * (1 / 3 : ℝ) ^ N / tauN N ≤ (2 : ℝ) ^ k * muTP N := by
    rw [← hku]
    have := mul_le_mul_of_nonneg_left hmu2 h2k.le
    rw [mul_sub] at this
    rw [mul_div_assoc]
    linarith
  -- the deterministic budget
  have hsqrt : Real.sqrt V ≤ sigN N := by
    rw [hV, sigN]
    refine Real.sqrt_le_sqrt ?_
    have : (2 : ℝ) ^ k ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hkN
    calc (2 : ℝ) ^ k * (1 / 3 : ℝ) ^ N ≤ 2 ^ N * (1 / 3) ^ N := by gcongr
      _ = (2 / 3 : ℝ) ^ N := by rw [← mul_pow]; norm_num
  have hmax : max (Real.sqrt V) (tauN N) ≤ sigN N + tauN N :=
    max_le (by linarith) (by linarith [sigN_pos N])
  have h2d : (2 : ℝ) ^ (N - k) ≤ 2 ^ D1 N := pow_le_pow_right₀ (by norm_num) hd.le
  have hbudget : 16 * N * max (Real.sqrt V) (tauN N) + (2 : ℝ) ^ k * (1 / 3 : ℝ) ^ N / tauN N
      ≤ etaB N * u := by
    have hmul : (2 : ℝ) ^ (N - k) * (16 * N * max (Real.sqrt V) (tauN N)
        + (2 : ℝ) ^ k * (1 / 3 : ℝ) ^ N / tauN N) ≤ etaB N := by
      have e : (2 : ℝ) ^ (N - k) * ((2 : ℝ) ^ k * (1 / 3 : ℝ) ^ N / tauN N)
          = (2 / 3 : ℝ) ^ N / tauN N := by
        rw [← mul_div_assoc, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hkN, ← mul_pow]
        norm_num
      rw [mul_add, e]
      have hm0 : 0 ≤ max (Real.sqrt V) (tauN N) := le_max_of_le_right hτ.le
      have : (2 : ℝ) ^ (N - k) * (16 * N * max (Real.sqrt V) (tauN N)) ≤
          16 * N * (2 : ℝ) ^ D1 N * (sigN N + tauN N) := by
        calc (2 : ℝ) ^ (N - k) * (16 * N * max (Real.sqrt V) (tauN N))
            = 16 * N * ((2 : ℝ) ^ (N - k) * max (Real.sqrt V) (tauN N)) := by ring
          _ ≤ 16 * N * ((2 : ℝ) ^ D1 N * (sigN N + tauN N)) := by gcongr
          _ = _ := by ring
      unfold EWnum at hnum
      linarith
    have := mul_le_mul_of_nonneg_left hmul hu0.le
    rw [← mul_assoc, mul_comm u, h2u, one_mul] at this
    linarith
  by_contra hlt
  push Not at hlt
  apply hbad
  have hBu : |(2 : ℝ) ^ k * muTP N - u| ≤ (2 : ℝ) ^ k * (1 / 3 : ℝ) ^ N / tauN N := by
    rw [abs_le]; constructor <;> linarith
  calc |blockP w S r0 - u| ≤ |blockP w S r0 - 2 ^ k * muTP N| + |2 ^ k * muTP N - u| :=
        abs_sub_le _ _ _
    _ ≤ 16 * N * max (Real.sqrt V) (tauN N) + 2 ^ k * (1 / 3 : ℝ) ^ N / tauN N := by
        linarith [hlt.le]
    _ ≤ etaB N * u := hbudget

/-- **P-EW** (on `g2`). -/
theorem cubeM_G2_not_EW (hN : 1 ≤ N) (hnum : EWnum N) :
    cubeM N (G2 N ∩ (EW N)ᶜ) ≤ ENNReal.ofReal (2 * (4 * Real.exp (-6)) ^ N) := by
  have hsub : G2 N ∩ (EW N)ᶜ ⊆ ⋃ S : Finset (Fin N), ⋃ r : State N,
      {w | w ∈ G2 N ∧ K2N N < S.card ∧ S.card < N ∧
        ¬ |blockP w S r - (1 / 2 : ℝ) ^ (N - S.card)| ≤ etaB N * (1 / 2 : ℝ) ^ (N - S.card)} := by
    rintro w ⟨hg, hw⟩
    simp only [EW, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hw
    obtain ⟨S, r, hk, hk', h⟩ := hw
    exact Set.mem_iUnion.2 ⟨S, Set.mem_iUnion.2 ⟨r, hg, hk, hk', h⟩⟩
  refine (measure_mono hsub).trans ((cubeM_iUnion_le _ fun S =>
    cubeM_iUnion_le (b := 2 * Real.exp (-6 * N)) _ fun r => ?_).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  · by_cases hc : K2N N < S.card
    · refine le_trans (measure_mono ?_) (cubeM_blockP_bad hN hnum S r hc)
      intro w hw
      exact ⟨hw.1, hw.2.2.2⟩
    · have : {w : Param N | w ∈ G2 N ∧ K2N N < S.card ∧ S.card < N ∧
          ¬ |blockP w S r - (1 / 2 : ℝ) ^ (N - S.card)| ≤ etaB N * (1 / 2 : ℝ) ^ (N - S.card)}
          = ∅ := by
        ext w; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hc h.2.1
      rw [this, measure_empty]; exact zero_le
  · simp only [Fintype.card_finset, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool,
      Nat.cast_pow, Nat.cast_ofNat]
    rw [mul_pow, show -6 * (N : ℝ) = N * (-6) by ring, Real.exp_nat_mul,
      show (4 : ℝ) ^ N = 2 ^ N * 2 ^ N by rw [← mul_pow]; norm_num]
    ring

/-! ### Column-level statistics -/

/-- The subcube mean of a column: `colMean w M m i = cmCol M m (colsOf w i)`. -/
def cmCol (M : Finset (Fin N)) (m : State N) (c : State N → ℝ) : ℝ :=
  (∑ r ∈ agree M m, clamp01 (c r)) / (2 : ℝ) ^ (N - M.card)

/-- The same with the entry of row `a` replaced by `1`. -/
def cmPlusCol (M : Finset (Fin N)) (a : State N) (c : State N → ℝ) : ℝ :=
  (1 + ∑ r ∈ (agree M a).erase a, clamp01 (c r)) / (2 : ℝ) ^ (N - M.card)

lemma colMean_eq_cmCol (w : Param N) (M : Finset (Fin N)) (m : State N) (i : Fin N) :
    colMean w M m i = cmCol M m (colsOf w i) := rfl

lemma colMeanPlus_eq_cmPlusCol (w : Param N) (M : Finset (Fin N)) (a : State N) (i : Fin N) :
    colMeanPlus w M a i = cmPlusCol M a (colsOf w i) := rfl

lemma measurable_cmCol (M : Finset (Fin N)) (m : State N) : Measurable (cmCol M m) :=
  (Finset.measurable_sum _ fun r _ => clamp01_measurable.comp (measurable_pi_apply r)).div_const _

lemma measurable_cmPlusCol (M : Finset (Fin N)) (a : State N) : Measurable (cmPlusCol M a) :=
  (measurable_const.add (Finset.measurable_sum _ fun r _ =>
    clamp01_measurable.comp (measurable_pi_apply r))).div_const _

lemma measurable_colOf (i : Fin N) : Measurable fun w : Param N => colsOf w i :=
  (measurable_pi_apply i).comp measurable_colsOf

lemma cmCol_nonneg (M : Finset (Fin N)) (m : State N) (c : State N → ℝ) : 0 ≤ cmCol M m c :=
  div_nonneg (sum_nonneg fun _ _ => clamp01_nonneg _) (by positivity)

lemma cmCol_le_one (M : Finset (Fin N)) (m : State N) (c : State N → ℝ) : cmCol M m c ≤ 1 := by
  unfold cmCol
  rw [div_le_one (by positivity)]
  calc ∑ r ∈ agree M m, clamp01 (c r) ≤ ∑ r ∈ agree M m, (1 : ℝ) :=
        sum_le_sum fun r _ => clamp01_le_one _
    _ = (2 : ℝ) ^ (N - M.card) := by
        rw [sum_const, card_agree, nsmul_eq_mul, mul_one]; push_cast; rfl

/-- The flip of coordinate `j0` (the Jensen pairing of W4 4.2). -/
def flipAt (j0 : Fin N) (r : State N) : State N := Function.update r j0 (!r j0)

lemma flipAt_flipAt (j0 : Fin N) (r : State N) : flipAt j0 (flipAt j0 r) = r := by
  funext j
  by_cases h : j = j0
  · subst h; simp [flipAt]
  · simp [flipAt, Function.update_of_ne h]

lemma flipAt_ne (j0 : Fin N) (r : State N) : flipAt j0 r ≠ r := fun h => by
  have := congrFun h j0
  simp [flipAt] at this

lemma flipAt_mem_agree {M : Finset (Fin N)} {j0 : Fin N} (hj0 : j0 ∉ M) {m r : State N}
    (hr : r ∈ agree M m) : flipAt j0 r ∈ agree M m := by
  rw [mem_agree] at hr ⊢
  intro j hj
  have hne : j ≠ j0 := fun h => hj0 (h ▸ hj)
  rw [flipAt, Function.update_of_ne hne]
  exact hr j hj

lemma sum_agree_flipAt {M : Finset (Fin N)} {j0 : Fin N} (hj0 : j0 ∉ M) (m : State N)
    (g : State N → ℝ) : ∑ r ∈ agree M m, g (flipAt j0 r) = ∑ r ∈ agree M m, g r :=
  Finset.sum_nbij' (flipAt j0) (flipAt j0) (fun _ hr => flipAt_mem_agree hj0 hr)
    (fun _ hr => flipAt_mem_agree hj0 hr) (fun r _ => flipAt_flipAt j0 r)
    (fun r _ => flipAt_flipAt j0 r) (fun _ _ => rfl)

lemma exists_not_mem_of_card_lt {M : Finset (Fin N)} (h : M.card < N) : ∃ j0, j0 ∉ M := by
  by_contra hne
  push Not at hne
  have : M = univ := eq_univ_of_forall hne
  rw [this, card_univ, Fintype.card_fin] at h
  exact lt_irrefl _ h

lemma mul_le_one_of_le {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  (mul_le_mul ha hb hb0 zero_le_one).trans_eq (one_mul 1)

/-- **Lemma JP**, fifth-power form: `max(2A, 1)^5 ≤ 1 + 2^{-d} Σ_{r ∈ C} (x_r + x_{r ⊕ j0})^5`. -/
lemma jp_pow5 {M : Finset (Fin N)} {j0 : Fin N} (hj0 : j0 ∉ M) (m : State N)
    (c : State N → ℝ) :
    max (2 * cmCol M m c) 1 ^ 5 ≤
      1 + (∑ r ∈ agree M m, (clamp01 (c r) + clamp01 (c (flipAt j0 r))) ^ 5) /
        (2 : ℝ) ^ (N - M.card) := by
  set C := agree M m with hC
  set n : ℝ := (2 : ℝ) ^ (N - M.card) with hn
  have hcard : (C.card : ℝ) = n := by rw [hC, card_agree]; push_cast; rfl
  have hnpos : 0 < n := by positivity
  set a : State N → ℝ := fun r => clamp01 (c r) + clamp01 (c (flipAt j0 r)) with ha
  have ha0 : ∀ r ∈ C, 0 ≤ a r := fun r _ => add_nonneg (clamp01_nonneg _) (clamp01_nonneg _)
  have hsum : ∑ r ∈ C, a r = 2 * ∑ r ∈ C, clamp01 (c r) := by
    simp only [ha, sum_add_distrib]
    rw [hC, sum_agree_flipAt hj0 m (fun r => clamp01 (c r))]
    ring
  have h2 : 2 * cmCol M m c = (∑ r ∈ C, a r) / n := by
    rw [hsum, cmCol, ← hC, ← hn]; ring
  have hJ := pow_sum_div_card_le_sum_pow ha0 4
  rw [hcard] at hJ
  have hpow : ((∑ r ∈ C, a r) / n) ^ 5 ≤ (∑ r ∈ C, a r ^ 5) / n := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hnpos]
    have h1 := (div_le_iff₀ (by positivity : (0 : ℝ) < n ^ 4)).1 hJ
    calc (∑ r ∈ C, a r) ^ 5 * n ≤ ((∑ r ∈ C, a r ^ (4 + 1)) * n ^ 4) * n :=
          mul_le_mul_of_nonneg_right h1 hnpos.le
      _ = (∑ r ∈ C, a r ^ 5) * n ^ 5 := by ring
  rw [h2]
  have h50 : 0 ≤ (∑ r ∈ C, a r ^ 5) / n :=
    div_nonneg (sum_nonneg fun r hr => pow_nonneg (ha0 r hr) 5) hnpos.le
  rcases le_total ((∑ r ∈ C, a r) / n) 1 with hle | hle
  · rw [max_eq_right hle, one_pow]; linarith
  · rw [max_eq_left hle]; linarith

/-- `E (x_r + x_{r'})^5 = 3` for distinct rows. -/
lemma integral_col_pair_pow5 {r r' : State N} (hrr : r ≠ r') :
    ∫ c, (clamp01 (c r) + clamp01 (c r')) ^ 5 ∂colLaw N = 3 := by
  have hexp : ∀ c : State N → ℝ, (clamp01 (c r) + clamp01 (c r')) ^ 5 =
      ∑ k ∈ range 6, clamp01 (c r) ^ k * clamp01 (c r') ^ (5 - k) * (Nat.choose 5 k : ℝ) :=
    fun c => add_pow _ _ _
  simp_rw [hexp]
  have hk : ∀ k ∈ range 6, ∫ c, clamp01 (c r) ^ k * clamp01 (c r') ^ (5 - k) *
      (Nat.choose 5 k : ℝ) ∂colLaw N =
        1 / ((k : ℝ) + 1) * (1 / (((5 - k : ℕ) : ℝ) + 1)) * (Nat.choose 5 k : ℝ) := by
    intro k _
    rw [integral_mul_const]
    congr 1
    have h := integral_pi_mul_of_ne (I := State N) unif hrr
      (g := fun y => clamp01 y ^ k) (h := fun y => clamp01 y ^ (5 - k))
      (clamp01_measurable.pow_const k) (clamp01_measurable.pow_const (5 - k))
    rw [colLaw, h, integral_cl_pow, integral_cl_pow]
  rw [integral_finsetSum _ fun k _ => ?_, sum_congr rfl hk]
  · simp [Finset.sum_range_succ]
    rw [show Nat.choose 5 2 = 10 from rfl, show Nat.choose 5 3 = 10 from rfl]
    norm_num
  · refine integrable_of_bdd_col ?_ (Nat.choose 5 k) fun c => ?_
    · exact (((clamp01_measurable.comp (measurable_pi_apply r)).pow_const k).mul
        ((clamp01_measurable.comp (measurable_pi_apply r')).pow_const (5 - k))).mul_const _
    · have h1 := clamp01_nonneg (c r)
      have h2 := clamp01_nonneg (c r')
      have h3 : clamp01 (c r) ^ k ≤ 1 := pow_le_one₀ h1 (clamp01_le_one _)
      have h4 : clamp01 (c r') ^ (5 - k) ≤ 1 := pow_le_one₀ h2 (clamp01_le_one _)
      rw [abs_of_nonneg (by positivity)]
      have : clamp01 (c r) ^ k * clamp01 (c r') ^ (5 - k) ≤ 1 :=
        mul_le_one_of_le h3 (by positivity) h4
      have hc : (0 : ℝ) ≤ Nat.choose 5 k := Nat.cast_nonneg _
      nlinarith

/-- **P-ECr, one moment.** `E max(2 colMean, 1)^5 ≤ 4` for every subcube of dimension `≥ 1`
(W4 has `47/14` by the exact pair moment; `1 + E(U+U')^5 = 4` suffices). -/
lemma lintegral_max_pow5_le {M : Finset (Fin N)} (hM : M.card < N) (m : State N) :
    ∫⁻ c, ENNReal.ofReal (max (2 * cmCol M m c) 1 ^ 5) ∂colLaw N ≤ ENNReal.ofReal 4 := by
  obtain ⟨j0, hj0⟩ := exists_not_mem_of_card_lt hM
  set n : ℝ := (2 : ℝ) ^ (N - M.card) with hn
  have hnpos : 0 < n := by positivity
  set g : (State N → ℝ) → ℝ := fun c => 1 + (∑ r ∈ agree M m,
    (clamp01 (c r) + clamp01 (c (flipAt j0 r))) ^ 5) / n with hg
  have hmp : ∀ r : State N, Measurable fun c : State N → ℝ =>
      (clamp01 (c r) + clamp01 (c (flipAt j0 r))) ^ 5 := fun r =>
    ((clamp01_measurable.comp (measurable_pi_apply r)).add
      (clamp01_measurable.comp (measurable_pi_apply _))).pow_const 5
  have hint1 : ∀ r : State N, Integrable (fun c : State N → ℝ =>
      (clamp01 (c r) + clamp01 (c (flipAt j0 r))) ^ 5) (colLaw N) := fun r =>
    integrable_of_bdd_col (hmp r) 32 fun c => by
      have h1 := clamp01_nonneg (c r)
      have h2 := clamp01_nonneg (c (flipAt j0 r))
      have h3 := clamp01_le_one (c r)
      have h4 := clamp01_le_one (c (flipAt j0 r))
      rw [abs_of_nonneg (by positivity)]
      have : clamp01 (c r) + clamp01 (c (flipAt j0 r)) ≤ 2 := by linarith
      calc (clamp01 (c r) + clamp01 (c (flipAt j0 r))) ^ 5 ≤ 2 ^ 5 :=
            pow_le_pow_left₀ (by positivity) this 5
        _ = 32 := by norm_num
  have hint : Integrable g (colLaw N) :=
    (integrable_const 1).add ((integrable_finsetSum _ fun r _ => hint1 r).div_const n)
  have hg0 : ∀ c, 0 ≤ g c := fun c => by
    have : 0 ≤ (∑ r ∈ agree M m, (clamp01 (c r) + clamp01 (c (flipAt j0 r))) ^ 5) / n :=
      div_nonneg (sum_nonneg fun r _ => pow_nonneg (add_nonneg (clamp01_nonneg _)
        (clamp01_nonneg _)) 5) hnpos.le
    simp only [hg]; linarith
  have hval : ∫ c, g c ∂colLaw N = 4 := by
    simp only [hg]
    rw [integral_add (integrable_const 1) ((integrable_finsetSum _ fun r _ => hint1 r).div_const n),
      integral_div, integral_finsetSum _ fun r _ => hint1 r,
      sum_congr rfl fun r _ => integral_col_pair_pow5 (flipAt_ne j0 r).symm]
    rw [sum_const, card_agree, nsmul_eq_mul, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have : ((2 ^ (N - M.card) : ℕ) : ℝ) = n := by rw [hn]; push_cast; rfl
    rw [this]
    field_simp
    norm_num
  calc ∫⁻ c, ENNReal.ofReal (max (2 * cmCol M m c) 1 ^ 5) ∂colLaw N
      ≤ ∫⁻ c, ENNReal.ofReal (g c) ∂colLaw N :=
        lintegral_mono fun c => ENNReal.ofReal_le_ofReal (jp_pow5 hj0 m c)
    _ = ENNReal.ofReal (∫ c, g c ∂colLaw N) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hg0)).symm
    _ = ENNReal.ofReal 4 := by rw [hval]

/-- **P-ECr, one subcube.** -/
lemma cubeM_ECr_bad {M : Finset (Fin N)} (hM : M.card < N) (m : State N) :
    cubeM N {w | ¬ ∑ i ∈ M, Real.log (max (2 * colMean w M m i) 1) ≤ 21 / 50 * M.card} ≤
      ENNReal.ofReal ((4 * Real.exp (-(21 / 10))) ^ M.card) := by
  set F : (State N → ℝ) → ℝ := fun c => Real.log (max (2 * cmCol M m c) 1) with hF
  have hFm : Measurable F := Real.measurable_log.comp
    (((measurable_cmCol M m).const_mul 2).max measurable_const)
  set X : Fin N → Param N → ℝ := fun i w => F (colsOf w i) with hX
  have hind : iIndepFun X (cubeM N) := iIndepFun_cols.comp (fun _ => F) (fun _ => hFm)
  have hmeas : ∀ i, Measurable (X i) := fun i => hFm.comp (measurable_colOf i)
  have h := chernoff_indep_ge (μ := cubeM N) M hind hmeas (a := 21 / 50 * M.card) (t := 5)
    (by norm_num)
  have hsub : {w : Param N | ¬ ∑ i ∈ M, Real.log (max (2 * colMean w M m i) 1) ≤
      21 / 50 * M.card} ⊆ {w | 21 / 50 * M.card ≤ ∑ i ∈ M, X i w} := fun w hw =>
    le_of_lt (not_le.1 hw)
  refine (measure_mono hsub).trans (h.trans ?_)
  have hI : ∀ i, ∫⁻ w, ENNReal.ofReal (Real.exp (5 * X i w)) ∂cubeM N ≤ ENNReal.ofReal 4 := by
    intro i
    have hg : Measurable fun c : State N → ℝ => ENNReal.ofReal (Real.exp (5 * F c)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hFm.const_mul 5))
    refine le_trans (le_of_eq ((mp_colOf i).lintegral_comp hg)) ?_
    refine le_trans (le_of_eq (lintegral_congr fun c => ?_)) (lintegral_max_pow5_le hM m)
    congr 1
    simp only [hF]
    have hpos : 0 < max (2 * cmCol M m c) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hpos]
  calc ENNReal.ofReal (Real.exp (-5 * (21 / 50 * M.card))) *
        ∏ i ∈ M, ∫⁻ w, ENNReal.ofReal (Real.exp (5 * X i w)) ∂cubeM N
      ≤ ENNReal.ofReal (Real.exp (-5 * (21 / 50 * M.card))) * ∏ _i ∈ M, ENNReal.ofReal 4 := by
        gcongr with i hi
        exact hI i
    _ = ENNReal.ofReal ((4 * Real.exp (-(21 / 10))) ^ M.card) := by
        rw [prod_const, ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity),
          mul_pow, ← Real.exp_nat_mul]
        congr 1
        rw [mul_comm]
        congr 1
        ring_nf

/-- **Lemma JP**, `colMeanPlus` form: `max(2A⁺, 1) ≤ 2^{-d} Σ_{r ∈ C} (1 + z_r)` with `z_r` one
entry of a row `≠ a`. -/
lemma jp_plus {M : Finset (Fin N)} {j0 : Fin N} (hj0 : j0 ∉ M) (a : State N)
    (c : State N → ℝ) :
    max (2 * cmPlusCol M a c) 1 ≤
      (∑ r ∈ agree M a, (1 + clamp01 (c (if flipAt j0 r = a then r else flipAt j0 r)))) /
        (2 : ℝ) ^ (N - M.card) := by
  set C := agree M a with hC
  set n : ℝ := (2 : ℝ) ^ (N - M.card) with hn
  have hcard : (C.card : ℝ) = n := by rw [hC, card_agree]; push_cast; rfl
  have hnpos : 0 < n := by positivity
  set xp : State N → ℝ := fun r => if r = a then 1 else clamp01 (c r) with hxp
  have hxp0 : ∀ r, 0 ≤ xp r := fun r => by
    simp only [hxp]; split_ifs
    · norm_num
    · exact clamp01_nonneg _
  have hxp1 : ∀ r, xp r ≤ 1 := fun r => by
    simp only [hxp]; split_ifs
    · norm_num
    · exact clamp01_le_one _
  have haC : a ∈ C := self_mem_agree M a
  have hsumxp : ∑ r ∈ C, xp r = 1 + ∑ r ∈ C.erase a, clamp01 (c r) := by
    rw [← add_sum_erase C xp haC]
    congr 1
    · simp [hxp]
    · refine sum_congr rfl fun r hr => ?_
      simp [hxp, ne_of_mem_erase hr]
  set b : State N → ℝ := fun r => xp r + xp (flipAt j0 r) with hb
  have hsumb : ∑ r ∈ C, b r = 2 * ∑ r ∈ C, xp r := by
    simp only [hb, sum_add_distrib]
    rw [hC, sum_agree_flipAt hj0 a xp]; ring
  have h2 : 2 * cmPlusCol M a c = (∑ r ∈ C, b r) / n := by
    rw [hsumb, hsumxp, cmPlusCol, ← hC, ← hn]; ring
  have hpt : ∀ r ∈ C, max (b r) 1 ≤
      1 + clamp01 (c (if flipAt j0 r = a then r else flipAt j0 r)) := by
    intro r _
    have hu0 := hxp0 r
    have hu1 := hxp1 r
    have hv0 := hxp0 (flipAt j0 r)
    have hv1 := hxp1 (flipAt j0 r)
    have hmax : max (b r) 1 ≤ 1 + xp r * xp (flipAt j0 r) := by
      refine max_le ?_ (by nlinarith)
      simp only [hb]; nlinarith
    refine hmax.trans ?_
    have hz : xp r * xp (flipAt j0 r) ≤
        clamp01 (c (if flipAt j0 r = a then r else flipAt j0 r)) := by
      by_cases hfa : flipAt j0 r = a
      · have hra : r ≠ a := by
          intro hra; rw [hra] at hfa; exact flipAt_ne j0 a hfa
        simp only [hxp, hra, hfa, ite_true, ite_false, mul_one, le_refl]
      · simp only [hfa, ite_false]
        have : xp (flipAt j0 r) = clamp01 (c (flipAt j0 r)) := by simp [hxp, hfa]
        rw [this]
        have := clamp01_nonneg (c (flipAt j0 r))
        nlinarith
    linarith
  rw [h2]
  have hsum_le : ∑ r ∈ C, max (b r) 1 ≤
      ∑ r ∈ C, (1 + clamp01 (c (if flipAt j0 r = a then r else flipAt j0 r))) := sum_le_sum hpt
  refine max_le ?_ ?_
  · rw [div_le_div_iff_of_pos_right hnpos]
    exact (sum_le_sum fun r _ => le_max_left _ _).trans hsum_le
  · rw [le_div_iff₀ hnpos, one_mul, ← hcard]
    calc (C.card : ℝ) = ∑ _r ∈ C, (1 : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ r ∈ C, max (b r) 1 := sum_le_sum fun r _ => le_max_right _ _
      _ ≤ _ := hsum_le

/-- **P-EF, one moment.** `E max(2 colMeanPlus, 1) ≤ 3/2`. -/
lemma lintegral_max_plus_le {M : Finset (Fin N)} (hM : M.card < N) (a : State N) :
    ∫⁻ c, ENNReal.ofReal (max (2 * cmPlusCol M a c) 1) ∂colLaw N ≤ ENNReal.ofReal (3 / 2) := by
  obtain ⟨j0, hj0⟩ := exists_not_mem_of_card_lt hM
  set n : ℝ := (2 : ℝ) ^ (N - M.card) with hn
  have hnpos : 0 < n := by positivity
  set q : State N → State N := fun r => if flipAt j0 r = a then r else flipAt j0 r with hq
  set g : (State N → ℝ) → ℝ := fun c => (∑ r ∈ agree M a, (1 + clamp01 (c (q r)))) / n with hg
  have hint1 : ∀ r : State N, Integrable (fun c : State N → ℝ => 1 + clamp01 (c (q r)))
      (colLaw N) := fun r => (integrable_const 1).add (integrable_col_cl (q r))
  have hint : Integrable g (colLaw N) :=
    (integrable_finsetSum _ fun r _ => hint1 r).div_const n
  have hg0 : ∀ c, 0 ≤ g c := fun c =>
    div_nonneg (sum_nonneg fun r _ => add_nonneg zero_le_one (clamp01_nonneg _)) hnpos.le
  have hval : ∫ c, g c ∂colLaw N = 3 / 2 := by
    simp only [hg]
    rw [integral_div, integral_finsetSum _ fun r _ => hint1 r]
    have : ∀ r ∈ agree M a, ∫ c, (1 + clamp01 (c (q r))) ∂colLaw N = 3 / 2 := by
      intro r _
      rw [integral_add (integrable_const 1) (integrable_col_cl (q r)), integral_col,
        integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      norm_num
    rw [sum_congr rfl this, sum_const, card_agree, nsmul_eq_mul]
    have e : ((2 ^ (N - M.card) : ℕ) : ℝ) = n := by rw [hn]; push_cast; rfl
    rw [e]
    field_simp
  calc ∫⁻ c, ENNReal.ofReal (max (2 * cmPlusCol M a c) 1) ∂colLaw N
      ≤ ∫⁻ c, ENNReal.ofReal (g c) ∂colLaw N :=
        lintegral_mono fun c => ENNReal.ofReal_le_ofReal (jp_plus hj0 a c)
    _ = ENNReal.ofReal (∫ c, g c ∂colLaw N) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hg0)).symm
    _ = ENNReal.ofReal (3 / 2) := by rw [hval]

/-- **P-EF, one set.** -/
lemma cubeM_EF_bad {M : Finset (Fin N)} (hM : M.card < N) (a : State N) :
    cubeM N {w | ¬ ∑ i ∈ M, Real.log (max (2 * colMeanPlus w M a i) 1) ≤ 43 / 100 * M.card} ≤
      ENNReal.ofReal ((3 / 2 * Real.exp (-(43 / 100))) ^ M.card) := by
  set F : (State N → ℝ) → ℝ := fun c => Real.log (max (2 * cmPlusCol M a c) 1) with hF
  have hFm : Measurable F := Real.measurable_log.comp
    (((measurable_cmPlusCol M a).const_mul 2).max measurable_const)
  set X : Fin N → Param N → ℝ := fun i w => F (colsOf w i) with hX
  have hind : iIndepFun X (cubeM N) := iIndepFun_cols.comp (fun _ => F) (fun _ => hFm)
  have hmeas : ∀ i, Measurable (X i) := fun i => hFm.comp (measurable_colOf i)
  have h := chernoff_indep_ge (μ := cubeM N) M hind hmeas (a := 43 / 100 * M.card) (t := 1)
    (by norm_num)
  have hsub : {w : Param N | ¬ ∑ i ∈ M, Real.log (max (2 * colMeanPlus w M a i) 1) ≤
      43 / 100 * M.card} ⊆ {w | 43 / 100 * M.card ≤ ∑ i ∈ M, X i w} := fun w hw =>
    le_of_lt (not_le.1 hw)
  refine (measure_mono hsub).trans (h.trans ?_)
  have hI : ∀ i, ∫⁻ w, ENNReal.ofReal (Real.exp (1 * X i w)) ∂cubeM N ≤
      ENNReal.ofReal (3 / 2) := by
    intro i
    have hg : Measurable fun c : State N → ℝ => ENNReal.ofReal (Real.exp (1 * F c)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hFm.const_mul 1))
    refine le_trans (le_of_eq ((mp_colOf i).lintegral_comp hg)) ?_
    refine le_trans (le_of_eq (lintegral_congr fun c => ?_)) (lintegral_max_plus_le hM a)
    congr 1
    simp only [hF, one_mul]
    exact Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))
  calc ENNReal.ofReal (Real.exp (-1 * (43 / 100 * M.card))) *
        ∏ i ∈ M, ∫⁻ w, ENNReal.ofReal (Real.exp (1 * X i w)) ∂cubeM N
      ≤ ENNReal.ofReal (Real.exp (-1 * (43 / 100 * M.card))) *
          ∏ _i ∈ M, ENNReal.ofReal (3 / 2) := by
        gcongr with i hi
        exact hI i
    _ = ENNReal.ofReal ((3 / 2 * Real.exp (-(43 / 100))) ^ M.card) := by
        rw [prod_const, ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity),
          mul_pow, ← Real.exp_nat_mul]
        congr 1
        rw [mul_comm]
        congr 1
        ring_nf

/-! ### P-ECh: Chebyshev for the normaliser -/

/-- Products over the columns of `S` of functions of the columns factor (IND). -/
lemma integral_prod_cols (S : Finset (Fin N)) (F : Fin N → (State N → ℝ) → ℝ)
    (hF : ∀ i, Measurable (F i)) :
    ∫ w, ∏ i ∈ S, F i (colsOf w i) ∂cubeM N = ∏ i ∈ S, ∫ c, F i c ∂colLaw N := by
  have hmp := mp_colsOf (N := N)
  have hG : Measurable fun x : Fin N → State N → ℝ => ∏ i ∈ S, F i (x i) :=
    Finset.measurable_prod _ fun i _ => (hF i).comp (measurable_pi_apply i)
  have h1 : ∫ w, ∏ i ∈ S, F i (colsOf w i) ∂cubeM N =
      ∫ x, ∏ i ∈ S, F i (x i) ∂(Measure.pi fun _ : Fin N => colLaw N) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hG.aestronglyMeasurable]
  rw [h1]
  have h2 : ∀ x : Fin N → State N → ℝ, ∏ i ∈ S, F i (x i) =
      ∏ i, (fun i c => if i ∈ S then F i c else 1) i (x i) := by
    intro x
    simp only
    rw [prod_ite_mem univ S, univ_inter]
  simp_rw [h2]
  have h4 : ∫ x : Fin N → State N → ℝ, ∏ i, (if i ∈ S then F i (x i) else 1)
      ∂(Measure.pi fun _ : Fin N => colLaw N) =
        ∏ i, ∫ c, (if i ∈ S then F i c else 1) ∂colLaw N :=
    integral_fintype_prod_eq_prod (fun i c => if i ∈ S then F i c else 1)
  rw [h4]
  have h3 : ∀ i, ∫ c, (if i ∈ S then F i c else 1) ∂colLaw N =
      if i ∈ S then ∫ c, F i c ∂colLaw N else 1 := by
    intro i
    split_ifs <;> simp
  simp_rw [h3]
  rw [prod_ite_mem univ S, univ_inter]

lemma integral_cmCol (M : Finset (Fin N)) (m : State N) :
    ∫ c, cmCol M m c ∂colLaw N = 1 / 2 := by
  unfold cmCol
  rw [integral_div]
  have := integral_col_linear (N := N) (agree M m) (fun _ => 1)
  simp only [one_mul, sum_const, nsmul_eq_mul, mul_one] at this
  rw [this, card_agree]
  push_cast
  field_simp

lemma sum_sum_ite_eq_third (A B : Finset (State N)) :
    ∑ r ∈ A, ∑ r' ∈ B, (if r = r' then (1 / 3 : ℝ) else 1 / 4) =
      (A.card : ℝ) * B.card / 4 + ((A ∩ B).card : ℝ) / 12 := by
  have h : ∀ r r' : State N, (if r = r' then (1 / 3 : ℝ) else 1 / 4) =
      1 / 4 + if r = r' then 1 / 12 else 0 := by
    intro r r'; split_ifs <;> norm_num
  simp_rw [h, sum_add_distrib, sum_const, nsmul_eq_mul, Finset.sum_ite_eq]
  rw [Finset.sum_ite_mem, sum_const, nsmul_eq_mul]
  ring

/-- `E[cm_t cm_{t'}]` for two subcubes of the same dimension. -/
lemma integral_cmCol_mul (M : Finset (Fin N)) (m m' : State N) :
    ∫ c, cmCol M m c * cmCol M m' c ∂colLaw N =
      (((agree M m).card : ℝ) * (agree M m').card / 4 + ((agree M m ∩ agree M m').card : ℝ) / 12)
        / ((2 : ℝ) ^ (N - M.card)) ^ 2 := by
  set A := agree M m with hA
  set B := agree M m' with hB
  set n : ℝ := (2 : ℝ) ^ (N - M.card) with hn
  have e : ∀ c : State N → ℝ, cmCol M m c * cmCol M m' c =
      (∑ r ∈ A, ∑ r' ∈ B, clamp01 (c r) * clamp01 (c r')) / n ^ 2 := by
    intro c; unfold cmCol; rw [← hA, ← hB, ← hn, div_mul_div_comm, sum_mul_sum, sq]
  simp_rw [e]
  have hint : ∀ r r' : State N, Integrable (fun c : State N → ℝ => clamp01 (c r) * clamp01 (c r'))
      (colLaw N) := fun r r' =>
    integrable_of_bdd_col ((clamp01_measurable.comp (measurable_pi_apply r)).mul
      (clamp01_measurable.comp (measurable_pi_apply r'))) 1 fun c => by
        rw [abs_of_nonneg (mul_nonneg (clamp01_nonneg _) (clamp01_nonneg _))]
        exact mul_le_one_of_le (clamp01_le_one _) (clamp01_nonneg _) (clamp01_le_one _)
  rw [integral_div, integral_finsetSum _ fun r _ => integrable_finsetSum _ fun r' _ => hint r r']
  rw [sum_congr rfl fun r _ => integral_finsetSum _ fun r' _ => hint r r']
  simp_rw [integral_col_mul]
  rw [sum_sum_ite_eq_third]

lemma agree_eq_of_forall {M : Finset (Fin N)} {t t' : State N} (h : ∀ j ∈ M, t j = t' j) :
    agree M t = agree M t' := by
  ext r; simp only [mem_agree]
  exact ⟨fun H j hj => (H j hj).trans (h j hj), fun H j hj => (H j hj).trans (h j hj).symm⟩

lemma agree_inter_eq_empty {M : Finset (Fin N)} {t t' : State N} (h : ¬ ∀ j ∈ M, t j = t' j) :
    agree M t ∩ agree M t' = ∅ := by
  ext r
  simp only [mem_inter, mem_agree, Finset.notMem_empty, iff_false, not_and]
  intro h1 h2
  exact h fun j hj => (h1 j hj).symm.trans (h2 j hj)

/-- The two cases of `E[cm_t cm_{t'}]` (dimension `≥ 1`). -/
lemma integral_cmCol_mul_le {M : Finset (Fin N)} (hM : M.card < N) (t t' : State N) :
    ∫ c, cmCol M t c * cmCol M t' c ∂colLaw N ≤
      if (∀ j ∈ M, t j = t' j) then 7 / 24 else 1 / 4 := by
  rw [integral_cmCol_mul]
  have hcA : ((agree M t).card : ℝ) = (2 : ℝ) ^ (N - M.card) := by rw [card_agree]; push_cast; rfl
  have hcB : ((agree M t').card : ℝ) = (2 : ℝ) ^ (N - M.card) := by rw [card_agree]; push_cast; rfl
  set n : ℝ := (2 : ℝ) ^ (N - M.card) with hn
  have hn2 : 2 ≤ n := by
    rw [hn]
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (N - M.card) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hnpos : 0 < n := by linarith
  rw [hcA, hcB]
  split_ifs with h
  · rw [agree_eq_of_forall h, inter_self, hcB]
    rw [div_le_iff₀ (by positivity)]
    have : n / 12 ≤ n ^ 2 / 24 := by nlinarith
    nlinarith
  · rw [agree_inter_eq_empty h, card_empty, Nat.cast_zero, zero_div, add_zero]
    rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- **P-ECh, one candidate.** `P(Σ_t Π_{i∈S} colMean < (3/4) 2^d) ≤ 16 (7/12)^k`. -/
lemma cubeM_ECh_bad {S : Finset (Fin N)} (hS : S.card < N) :
    cubeM N {w | ¬ 3 / 4 * (2 : ℝ) ^ (N - S.card) ≤ ∑ t : State N, ∏ i ∈ S, colMean w S t i} ≤
      ENNReal.ofReal (16 * (7 / 12 : ℝ) ^ S.card) := by
  set k := S.card with hk
  set n : ℝ := (2 : ℝ) ^ (N - k) with hn
  set K : ℝ := (2 : ℝ) ^ k with hK
  have hnK : n * K = 2 ^ N := by rw [hn, hK, ← pow_add, Nat.sub_add_cancel hS.le]
  have hnpos : 0 < n := by positivity
  have hKpos : 0 < K := by positivity
  set Yt : State N → Param N → ℝ := fun t w => ∏ i ∈ S, colMean w S t i with hYt
  set Y : Param N → ℝ := fun w => ∑ t : State N, Yt t w with hY
  have hYtm : ∀ t, Measurable (Yt t) := fun t =>
    Finset.measurable_prod _ fun i _ => measurable_colMean S t i
  have hYm : Measurable Y := Finset.measurable_sum _ fun t _ => hYtm t
  have hYt0 : ∀ t w, 0 ≤ Yt t w := fun t w => prod_nonneg fun i _ => colMean_nonneg _ _ _ _
  have hYt1 : ∀ t w, Yt t w ≤ 1 := fun t w =>
    prod_le_one (fun i _ => colMean_nonneg _ _ _ _) fun i _ => colMean_le_one _ _ _ _
  have hYtint : ∀ t, Integrable (Yt t) (cubeM N) := fun t =>
    integrable_of_bdd_cubeM (hYtm t) 1 fun w => by rw [abs_of_nonneg (hYt0 t w)]; exact hYt1 t w
  have hYtt : ∀ t t', Integrable (fun w => Yt t w * Yt t' w) (cubeM N) := fun t t' =>
    integrable_of_bdd_cubeM ((hYtm t).mul (hYtm t')) 1 fun w => by
      rw [abs_of_nonneg (mul_nonneg (hYt0 t w) (hYt0 t' w))]
      exact mul_le_one_of_le (hYt1 t w) (hYt0 t' w) (hYt1 t' w)
  have hYint : Integrable Y (cubeM N) := integrable_finsetSum _ fun t _ => hYtint t
  have hY2eq : ∀ w, Y w ^ 2 = ∑ t : State N, ∑ t' : State N, Yt t w * Yt t' w := by
    intro w; simp only [hY]; rw [sq, sum_mul_sum]
  have hY2int : Integrable (fun w => Y w ^ 2) (cubeM N) := by
    simp_rw [hY2eq]
    exact integrable_finsetSum _ fun t _ => integrable_finsetSum _ fun t' _ => hYtt t t'
  -- the first moment
  have hEYt : ∀ t, ∫ w, Yt t w ∂cubeM N = (1 / 2 : ℝ) ^ k := by
    intro t
    have := integral_prod_cols S (fun _ c => cmCol S t c) (fun _ => measurable_cmCol S t)
    simp only [integral_cmCol, prod_const] at this
    exact this
  have hEY : ∫ w, Y w ∂cubeM N = n := by
    simp only [hY]
    rw [integral_finsetSum _ fun t _ => hYtint t, sum_congr rfl fun t _ => hEYt t, sum_const,
      card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [← hnK, hK, one_div_pow, ← hK]
    field_simp
  -- the second moment
  have hEYtt : ∀ t t', ∫ w, Yt t w * Yt t' w ∂cubeM N ≤
      (1 / 4 : ℝ) ^ k + if (∀ j ∈ S, t j = t' j) then (7 / 24 : ℝ) ^ k else 0 := by
    intro t t'
    have e : ∀ w, Yt t w * Yt t' w = ∏ i ∈ S, (fun c => cmCol S t c * cmCol S t' c) (colsOf w i) :=
      fun w => by simp only [hYt]; rw [← prod_mul_distrib]; rfl
    simp_rw [e]
    rw [integral_prod_cols S (fun _ c => cmCol S t c * cmCol S t' c)
      (fun _ => (measurable_cmCol S t).mul (measurable_cmCol S t'))]
    have hle : ∏ _i ∈ S, ∫ c, cmCol S t c * cmCol S t' c ∂colLaw N ≤
        ∏ _i ∈ S, (if (∀ j ∈ S, t j = t' j) then (7 / 24 : ℝ) else 1 / 4) :=
      prod_le_prod (fun i _ => integral_nonneg fun c =>
        mul_nonneg (cmCol_nonneg _ _ _) (cmCol_nonneg _ _ _))
        (fun i _ => integral_cmCol_mul_le hS t t')
    refine hle.trans ?_
    rw [prod_const]
    split_ifs
    · have : (0 : ℝ) ≤ (1 / 4) ^ k := by positivity
      linarith
    · linarith
  have hcount : ∀ t : State N, ∑ t' : State N,
      (if (∀ j ∈ S, t j = t' j) then (7 / 24 : ℝ) ^ k else 0) = n * (7 / 24 : ℝ) ^ k := by
    intro t
    rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
    congr 1
    have : (univ.filter fun t' : State N => ∀ j ∈ S, t j = t' j) = agree S t := by
      ext t'; simp only [mem_filter, mem_univ, true_and, mem_agree]
      exact ⟨fun H j hj => (H j hj).symm, fun H j hj => (H j hj).symm⟩
    rw [this, card_agree]; push_cast; rfl
  have hEY2 : ∫ w, Y w ^ 2 ∂cubeM N ≤ n ^ 2 + 2 ^ N * n * (7 / 24 : ℝ) ^ k := by
    simp_rw [hY2eq]
    rw [integral_finsetSum _ fun t _ => integrable_finsetSum _ fun t' _ => hYtt t t']
    rw [sum_congr rfl fun t _ => integral_finsetSum _ fun t' _ => hYtt t t']
    calc ∑ t : State N, ∑ t' : State N, ∫ w, Yt t w * Yt t' w ∂cubeM N
        ≤ ∑ t : State N, ∑ t' : State N, ((1 / 4 : ℝ) ^ k +
            if (∀ j ∈ S, t j = t' j) then (7 / 24 : ℝ) ^ k else 0) :=
          sum_le_sum fun t _ => sum_le_sum fun t' _ => hEYtt t t'
      _ = ∑ _t : State N, ((2 : ℝ) ^ N * (1 / 4 : ℝ) ^ k + n * (7 / 24 : ℝ) ^ k) := by
          refine sum_congr rfl fun t _ => ?_
          rw [sum_add_distrib, hcount t, sum_const, card_univ, Fintype.card_fun,
            Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
      _ = n ^ 2 + 2 ^ N * n * (7 / 24 : ℝ) ^ k := by
          rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          rw [← hnK, show (1 / 4 : ℝ) ^ k = 1 / K ^ 2 by
            rw [hK, ← pow_mul, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, ← pow_mul,
              one_div_pow, mul_comm]]
          field_simp
  -- Markov on `(Y - n)^2`
  set f : Param N → ℝ := fun w => (Y w - n) ^ 2 with hf
  have hf0 : ∀ w, 0 ≤ f w := fun w => sq_nonneg _
  have hfint : Integrable f (cubeM N) := by
    have e : f = fun w => Y w ^ 2 - 2 * n * Y w + n ^ 2 := by funext w; simp only [hf]; ring
    rw [e]
    exact (hY2int.sub (hYint.const_mul _)).add (integrable_const _)
  have hEf : ∫ w, f w ∂cubeM N ≤ 2 ^ N * n * (7 / 24 : ℝ) ^ k := by
    have e : ∀ w, f w = Y w ^ 2 - 2 * n * Y w + n ^ 2 := fun w => by simp only [hf]; ring
    simp_rw [e]
    have i1 : Integrable (fun w => Y w ^ 2 - 2 * n * Y w) (cubeM N) :=
      hY2int.sub (hYint.const_mul _)
    have i2 : Integrable (fun w => 2 * n * Y w) (cubeM N) := hYint.const_mul _
    rw [integral_add i1 (integrable_const _), integral_sub hY2int i2, integral_const_mul, hEY,
      integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    linarith
  have hε : (0 : ℝ) < n ^ 2 / 16 := by positivity
  have hsub : {w : Param N | ¬ 3 / 4 * (2 : ℝ) ^ (N - k) ≤ ∑ t : State N, ∏ i ∈ S, colMean w S t i}
      ⊆ {w | n ^ 2 / 16 ≤ f w} := by
    intro w hw
    simp only [Set.mem_ofPred_eq, not_le] at hw ⊢
    have hlt : Y w < 3 / 4 * n := hw
    have h1 : n / 4 ≤ n - Y w := by linarith
    have h2 : 0 ≤ n / 4 := by positivity
    simp only [hf]
    nlinarith
  refine (measure_mono hsub).trans ((markov_cubeM hf0 hfint hε).trans
    (ENNReal.ofReal_le_ofReal ?_))
  rw [div_le_iff₀ hε]
  have e2 : (2 : ℝ) ^ N * n * (7 / 24 : ℝ) ^ k = 16 * (7 / 12 : ℝ) ^ k * (n ^ 2 / 16) := by
    rw [← hnK, show (7 / 12 : ℝ) ^ k = K * (7 / 24) ^ k by
      rw [hK, ← mul_pow]; norm_num]
    field_simp
  linarith

/-! ### The total failure probability of `E5` -/

lemma pow_le_of_big {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) {j : ℕ} (hj : K2N N < j) (hjN : j ≤ N) :
    q ^ j ≤ (1 / q) ^ D1 N * q ^ N := by
  have hd : N - j < D1 N := by rw [K2N_eq_sub_D1] at hj; omega
  have e : q ^ N = q ^ j * q ^ (N - j) := by rw [← pow_add, Nat.add_sub_cancel' hjN]
  rw [e, one_div_pow]
  have h1 : q ^ D1 N ≤ q ^ (N - j) := pow_le_pow_of_le_one hq0.le hq1 hd.le
  have hqD : 0 < q ^ D1 N := by positivity
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hqD]
  calc q ^ j * q ^ D1 N ≤ q ^ j * q ^ (N - j) := by gcongr
    _ = q ^ j * q ^ (N - j) := rfl

/-- The constant `a = 4 e^{-21/10}` of P-ECr. -/
def aCr : ℝ := 4 * Real.exp (-(21 / 10))
/-- The constant `b = (3/2) e^{-43/100}` of P-EF. -/
def bEF : ℝ := 3 / 2 * Real.exp (-(43 / 100))

lemma aCr_pos : 0 < aCr := by unfold aCr; positivity
lemma bEF_pos : 0 < bEF := by unfold bEF; positivity

/-- `8 < e^{21/10}` (so `2 aCr < 1`). -/
lemma eight_lt_exp : (8 : ℝ) < Real.exp (21 / 10) := by
  have h := rat_le_exp (q := 21 / 10) (r := 81 / 10) 10 3 (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  have e : (((21 / 10 : ℚ)) : ℝ) = 21 / 10 := by norm_num
  have e' : (((81 / 10 : ℚ)) : ℝ) = 81 / 10 := by norm_num
  rw [e, e'] at h
  linarith

/-- `3/2 < e^{43/100}` (C17b, so `bEF < 1`). -/
lemma three_halves_lt_exp : (3 / 2 : ℝ) < Real.exp (43 / 100) := by
  have h := rat_le_exp (q := 43 / 100) (r := 1537 / 1000) 10 1 (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  have e : (((43 / 100 : ℚ)) : ℝ) = 43 / 100 := by norm_num
  have e' : (((1537 / 1000 : ℚ)) : ℝ) = 1537 / 1000 := by norm_num
  rw [e, e'] at h
  linarith

lemma two_aCr_lt_one : 2 * aCr < 1 := by
  unfold aCr
  rw [Real.exp_neg]
  have := eight_lt_exp
  have hp := Real.exp_pos (21 / 10)
  rw [← mul_assoc, ← div_eq_mul_inv, div_lt_one hp]
  linarith

lemma aCr_le_one : aCr ≤ 1 := by linarith [two_aCr_lt_one, aCr_pos]

lemma bEF_lt_one : bEF < 1 := by
  unfold bEF
  rw [Real.exp_neg]
  have := three_halves_lt_exp
  have hp := Real.exp_pos (43 / 100)
  rw [← div_eq_mul_inv, div_lt_one hp]
  linarith

/-- **P-ECr.** -/
theorem cubeM_not_ECr (hN : 1 ≤ N) :
    cubeM N (ECr N)ᶜ ≤ ENNReal.ofReal (Real.exp 1 * ((1 / aCr) * N) ^ D1 N * (2 * aCr) ^ N) := by
  set X : Finset (Fin N) → Set (Param N) := fun M => ⋃ m : State N,
    {w | K2N N < M.card ∧ M.card < N ∧
      ¬ ∑ i ∈ M, Real.log (max (2 * colMean w M m i) 1) ≤ 21 / 50 * M.card} with hX
  have hsub : (ECr N)ᶜ ⊆ ⋃ M, X M := by
    intro w hw
    simp only [ECr, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hw
    obtain ⟨M, m, hk, hk', h⟩ := hw
    exact Set.mem_iUnion.2 ⟨M, Set.mem_iUnion.2 ⟨m, hk, hk', h⟩⟩
  have hb0 : 0 ≤ (2 : ℝ) ^ N * ((1 / aCr) ^ D1 N * aCr ^ N) := by
    have := aCr_pos; positivity
  refine (measure_mono hsub).trans ((cubeM_iUnion_bigM_le hN X hb0 (fun M hM => ?_)
    (fun M hM => ?_)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  · refine (cubeM_iUnion_le (b := (1 / aCr) ^ D1 N * aCr ^ N) _ fun m => ?_).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    · by_cases hMN : M.card < N
      · refine le_trans (measure_mono fun w hw => hw.2.2) ((cubeM_ECr_bad hMN m).trans
          (ENNReal.ofReal_le_ofReal ?_))
        exact pow_le_of_big aCr_pos aCr_le_one hM hMN.le
      · have : {w : Param N | K2N N < M.card ∧ M.card < N ∧
            ¬ ∑ i ∈ M, Real.log (max (2 * colMean w M m i) 1) ≤ 21 / 50 * M.card} = ∅ := by
          ext w; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h => hMN h.2.1
        rw [this, measure_empty]; exact zero_le
    · simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; ring
  · simp only [hX]
    ext w
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    exact fun m h => hM h.1
  · rw [mul_pow]; ring

/-- **P-EF** (one fixed row). -/
theorem cubeM_not_EF (hN : 1 ≤ N) (a : State N) :
    cubeM N (EF N a)ᶜ ≤ ENNReal.ofReal (Real.exp 1 * ((1 / bEF) * N) ^ D1 N * bEF ^ N) := by
  set X : Finset (Fin N) → Set (Param N) := fun M =>
    {w | K2N N < M.card ∧ M.card < N ∧
      ¬ ∑ i ∈ M, Real.log (max (2 * colMeanPlus w M a i) 1) ≤ 43 / 100 * M.card} with hX
  have hsub : (EF N a)ᶜ ⊆ ⋃ M, X M := by
    intro w hw
    simp only [EF, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hw
    obtain ⟨M, hk, hk', h⟩ := hw
    exact Set.mem_iUnion.2 ⟨M, hk, hk', h⟩
  have hb0 : 0 ≤ (1 / bEF) ^ D1 N * bEF ^ N := by have := bEF_pos; positivity
  refine (measure_mono hsub).trans ((cubeM_iUnion_bigM_le hN X hb0 (fun M hM => ?_)
    (fun M hM => ?_)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  · by_cases hMN : M.card < N
    · refine le_trans (measure_mono fun w hw => hw.2.2) ((cubeM_EF_bad hMN a).trans
        (ENNReal.ofReal_le_ofReal ?_))
      exact pow_le_of_big bEF_pos bEF_lt_one.le hM hMN.le
    · have : X M = ∅ := by
        ext w; simp only [hX, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hMN h.2.1
      rw [this, measure_empty]; exact zero_le
  · ext w
    simp only [hX, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => hM h.1
  · rw [mul_pow]; ring

/-- **P-ECh.** -/
theorem cubeM_not_ECh (hN : 1 ≤ N) :
    cubeM N (ECh N)ᶜ ≤
      ENNReal.ofReal (Real.exp 1 * 16 * ((12 / 7) * N) ^ D1 N * (7 / 12 : ℝ) ^ N) := by
  set X : Finset (Fin N) → Set (Param N) := fun S =>
    {w | K2N N < S.card ∧ S.card < N ∧
      ¬ 3 / 4 * (2 : ℝ) ^ (N - S.card) ≤ ∑ t : State N, ∏ i ∈ S, colMean w S t i} with hX
  have hsub : (ECh N)ᶜ ⊆ ⋃ S, X S := by
    intro w hw
    simp only [ECh, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hw
    obtain ⟨S, hk, hk', h⟩ := hw
    exact Set.mem_iUnion.2 ⟨S, hk, hk', h⟩
  have hb0 : 0 ≤ 16 * ((1 / (7 / 12 : ℝ)) ^ D1 N * (7 / 12 : ℝ) ^ N) := by positivity
  refine (measure_mono hsub).trans ((cubeM_iUnion_bigM_le hN X hb0 (fun S hS => ?_)
    (fun S hS => ?_)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  · by_cases hSN : S.card < N
    · refine le_trans (measure_mono fun w hw => hw.2.2) ((cubeM_ECh_bad hSN).trans
        (ENNReal.ofReal_le_ofReal ?_))
      have := pow_le_of_big (q := 7 / 12) (by norm_num) (by norm_num) hS hSN.le
      linarith
    · have : X S = ∅ := by
        ext w; simp only [hX, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hSN h.2.1
      rw [this, measure_empty]; exact zero_le
  · ext w
    simp only [hX, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => hS h.1
  · rw [mul_pow, show (1 / (7 / 12 : ℝ)) = 12 / 7 by norm_num]; ring

/-- The total failure probability of `E5` (W4 4.4 "Total", in the form proved here). -/
def fB5 (N : ℕ) : ℝ :=
  fg2 N + 2 * (4 * Real.exp (-6)) ^ N + fEH N
    + Real.exp 1 * ((1 / aCr) * N) ^ D1 N * (2 * aCr) ^ N
    + Real.exp 1 * 16 * ((12 / 7) * N) ^ D1 N * (7 / 12 : ℝ) ^ N
    + 2 * (Real.exp 1 * ((1 / bEF) * N) ^ D1 N * bEF ^ N)

/-- **The failure probability of `E5`**, for every `N ≥ 1` with the eventual inequality `EWnum`. -/
theorem cubeM_not_E5_le (hN : 1 ≤ N) (hnum : EWnum N) (s tc : State N) :
    cubeM N (E5 N s tc)ᶜ ≤ ENNReal.ofReal (fB5 N) := by
  have hsub : (E5 N s tc)ᶜ ⊆ (G2 N)ᶜ ∪ (G2 N ∩ (EW N)ᶜ) ∪ (EH N)ᶜ ∪ (ECr N)ᶜ ∪ (ECh N)ᶜ
      ∪ (EF N tc)ᶜ ∪ (EF N s)ᶜ := by
    intro w hw
    simp only [E5, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union, not_and_or] at hw ⊢
    tauto
  have hG2 : cubeM N (G2 N)ᶜ ≤ ENNReal.ofReal (fg2 N) := by
    have : (G2 N)ᶜ = {w | ¬ ∀ i r, Qw w i r ≤ tauN N} := by ext w; simp [G2]
    rw [this]; exact cubeM_not_g2
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add ((measure_union_le _ _).trans (add_le_add hG2 (cubeM_G2_not_EW hN hnum)))
    cubeM_not_EH)) (cubeM_not_ECr hN))) (cubeM_not_ECh hN))) (cubeM_not_EF hN tc)))
    (cubeM_not_EF hN s)).trans ?_
  have h0 : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≠ ⊤ := fun _ _ => ENNReal.ofReal_ne_top
  have hn1 : 0 ≤ fg2 N := by unfold fg2; positivity
  have hn2 : 0 ≤ 2 * (4 * Real.exp (-6)) ^ N := by positivity
  have hn3 : 0 ≤ fEH N := by unfold fEH; positivity
  have ha := aCr_pos
  have hb := bEF_pos
  have hn4 : 0 ≤ Real.exp 1 * ((1 / aCr) * N) ^ D1 N * (2 * aCr) ^ N := by positivity
  have hn5 : 0 ≤ Real.exp 1 * 16 * ((12 / 7) * N) ^ D1 N * (7 / 12 : ℝ) ^ N := by positivity
  have hn6 : 0 ≤ Real.exp 1 * ((1 / bEF) * N) ^ D1 N * bEF ^ N := by positivity
  rw [← ENNReal.ofReal_add hn1 hn2, ← ENNReal.ofReal_add (by positivity) hn3,
    ← ENNReal.ofReal_add (by positivity) hn4, ← ENNReal.ofReal_add (by positivity) hn5,
    ← ENNReal.ofReal_add (by positivity) hn6, ← ENNReal.ofReal_add (by positivity) hn6]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold fB5; ring

/-- `fB5 N → 0`. -/
theorem tendsto_fB5 : Tendsto fB5 atTop (𝓝 0) := by
  have ha := aCr_pos
  have hb := bEF_pos
  have h1 : Tendsto (fun N : ℕ => 2 * (4 * Real.exp (-6)) ^ N) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      four_exp_neg_six_lt_one).const_mul 2
    rwa [mul_zero] at this
  have hA : Tendsto (fun N : ℕ => Real.exp 1 * ((1 / aCr) * N) ^ D1 N * (2 * aCr) ^ N) atTop
      (𝓝 0) :=
    tendsto_D1_geom (by rw [le_div_iff₀ ha, one_mul]; exact aCr_le_one) (by positivity)
      two_aCr_lt_one (by positivity)
  have hC : Tendsto (fun N : ℕ => Real.exp 1 * 16 * ((12 / 7) * N) ^ D1 N * (7 / 12 : ℝ) ^ N)
      atTop (𝓝 0) :=
    tendsto_D1_geom (by norm_num) (by norm_num) (by norm_num) (by positivity)
  have hF : Tendsto (fun N : ℕ => Real.exp 1 * ((1 / bEF) * N) ^ D1 N * bEF ^ N) atTop (𝓝 0) :=
    tendsto_D1_geom (by rw [le_div_iff₀ hb, one_mul]; exact bEF_lt_one.le) hb bEF_lt_one
      (by positivity)
  have hF2 := hF.const_mul 2
  rw [mul_zero] at hF2
  have := (((((tendsto_fg2.add h1).add tendsto_fEH).add hA).add hC).add hF2)
  simp only [add_zero] at this
  exact this.congr fun N => by unfold fB5; ring

end Prob

/-! ## 3. Candidates with `2 ≤ |S| ≤ K2N N`: Proposition M, Corollary Mid, Proposition KT -/

section MidSizes

variable {tc u s0 : State N} {w' : Param N}

/-- `ε_k := H + 2τ + 2 Mk N k`. -/
def epsK (N k : ℕ) (H : ℝ) : ℝ := H + 2 * tauN N + 2 * Mk N k

/-- `δ_k := ((1/2)^{k-1} + E6 N k)/12 + 2 dlev N k`. -/
def deltaK (N k : ℕ) : ℝ := ((1 / 2 : ℝ) ^ (k - 1) + E6 N k) / 12 + 2 * dlev N k

/-- `L_k := Zs w̃ / 2 - 8 N σ_N - dlev N k - ε_k`. -/
def LK (N k : ℕ) (Z H : ℝ) : ℝ := Z / 2 - 8 * N * sigN N - dlev N k - epsK N k H

/-- `ρ_k := k (δ_k + 2 ε_k) / L_k`. -/
def rhoK (N k : ℕ) (Z H : ℝ) : ℝ := k * (deltaK N k + 2 * epsK N k H) / LK N k Z H

/-- `fl_k := Dev N k + 2τ + 2 (1 + 2^{2-k}) Mk N k`. -/
def flK (N k : ℕ) : ℝ := Dev N k + 2 * tauN N + 2 * (1 + 4 / (2 : ℝ) ^ k) * Mk N k

lemma epsK_nonneg (N k : ℕ) {H : ℝ} (hH : 0 ≤ H) : 0 ≤ epsK N k H := by
  unfold epsK; have := tauN_pos N; have := Mk_nonneg N k; positivity

lemma flK_nonneg {N : ℕ} (hN : 1 ≤ N) (k : ℕ) : 0 ≤ flK N k := by
  unfold flK; have := tauN_pos N; have := Mk_nonneg N k; have := Dev_nonneg (N := N) k hN
  positivity

/-- **Proposition M (M1).** `Num w S Y t i ≥ L_k`. -/
theorem propM1 {w : Param N} (hN : 1 ≤ N) (hA : AgreeOff {tc, u} w w') (hG : GoodW N s0 w')
    {S Y : Finset (Fin N)} {i : Fin N} (hi : i ∈ S) (hY : Y ⊆ S) (t : State N) :
    LK N S.card (Zs w') (Pw w tc + Pw w u) ≤ Num w S Y t i := by
  have h1 := tr2_goodW hA hG hY t i
  have h2 := dev_le_dlev hG hN hi hY t
  have h3 := hG.g11 i
  have hsub : 0 ≤ subSum w' i Y t / (12 * (2 : ℝ) ^ (S.card - Y.card)) :=
    div_nonneg (subSum_nonneg _ _ _ _) (by positivity)
  unfold LK epsK
  unfold cNum at h2
  rw [abs_le] at h1 h2 h3
  linarith [h1.1, h2.1, h3.2]

/-- **Proposition M (M2).** `|Num w S S t i - Num w S S t' i| ≤ δ_k + 2 ε_k`. -/
theorem propM2 {w : Param N} (hN : 1 ≤ N) (hA : AgreeOff {tc, u} w w') (hG : GoodW N s0 w')
    {S : Finset (Fin N)} (hS : 1 ≤ S.card) {i : Fin N} (hi : i ∈ S) (t t' : State N) :
    |Num w S S t i - Num w S S t' i| ≤
      deltaK N S.card + 2 * epsK N S.card (Pw w tc + Pw w u) := by
  have hdiff : |Num w' S S t i - Num w' S S t' i| ≤ deltaK N S.card := by
    rw [Num_S_sub t t']
    have h1 := dev_le_dlev hG hN hi (subset_refl S) t
    have h2 := dev_le_dlev hG hN hi (subset_refl S) t'
    have hs1 := subSum_S_le hG i hS t
    have hs2 := subSum_S_le hG i hS t'
    have hn1 := subSum_nonneg w' i S t
    have hn2 := subSum_nonneg w' i S t'
    unfold deltaK
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith
  have e1 := tr2_goodW hA hG (subset_refl S) t i
  have e2 := tr2_goodW hA hG (subset_refl S) t' i
  unfold epsK
  rw [abs_le] at e1 e2 hdiff ⊢
  constructor <;> linarith

/-- Product comparison with a positive lower bound `L` (variant of `prod_le_exp_mul_prod`). -/
lemma prod_le_exp_mul_prod_L {ι : Type*} (S : Finset ι) (a b : ι → ℝ) {L δ : ℝ} (hL : 0 < L)
    (hδ : 0 ≤ δ) (hb : ∀ i ∈ S, L ≤ b i) (hd : ∀ i ∈ S, a i - b i ≤ δ) (ha0 : ∀ i ∈ S, 0 ≤ a i) :
    ∏ i ∈ S, a i ≤ Real.exp (S.card * δ / L) * ∏ i ∈ S, b i := by
  have hstep : ∀ i ∈ S, a i ≤ b i * Real.exp (δ / L) := by
    intro i hi
    have hbi := hb i hi
    have hbpos : 0 < b i := lt_of_lt_of_le hL hbi
    have h1 : a i ≤ b i + δ := by linarith [hd i hi]
    have h2 : b i + δ ≤ b i * (1 + δ / L) := by
      have : δ ≤ b i * (δ / L) := by
        rw [mul_div_assoc', le_div_iff₀ hL]
        nlinarith
      linarith
    have h3 : 1 + δ / L ≤ Real.exp (δ / L) := by linarith [Real.add_one_le_exp (δ / L)]
    calc a i ≤ b i * (1 + δ / L) := h1.trans h2
      _ ≤ b i * Real.exp (δ / L) := mul_le_mul_of_nonneg_left h3 hbpos.le
  calc ∏ i ∈ S, a i ≤ ∏ i ∈ S, (b i * Real.exp (δ / L)) := prod_le_prod ha0 hstep
    _ = (∏ i ∈ S, b i) * Real.exp (δ / L) ^ S.card := by rw [prod_mul_distrib, prod_const]
    _ = Real.exp (S.card * δ / L) * ∏ i ∈ S, b i := by
        rw [← Real.exp_nat_mul, mul_comm]
        congr 2
        ring

/-- **Proposition M (M3).** `sysBackCause (tpmOf z) S s s t ≤ e^{ρ_k} / 2^k`. -/
theorem propM3 (hN : 1 ≤ N) {z : Param N} (hz : z ∈ openCube N) {s : State N}
    (hA : AgreeOff {tc, u} (flipP s z) w') (hG : GoodW N s0 w') {S : Finset (Fin N)}
    (hS : 1 ≤ S.card)
    (hL : 0 < LK N S.card (Zs w') (Pw (flipP s z) tc + Pw (flipP s z) u)) (t : State N) :
    sysBackCause (tpmOf z) S s s t ≤
      Real.exp (rhoK N S.card (Zs w') (Pw (flipP s z) tc + Pw (flipP s z) u)) / 2 ^ S.card := by
  set w := flipP s z with hw
  have hZpos : 0 < Zs w := Zs_pos hz s
  have hratio : ∀ t t', sysCauseProb (tpmOf z) S s s t ≤
      Real.exp (rhoK N S.card (Zs w') (Pw w tc + Pw w u)) * sysCauseProb (tpmOf z) S s s t' := by
    intro t t'
    rw [sysCauseProb_eq_Num, sysCauseProb_eq_Num, ← hw, prod_div_distrib, prod_div_distrib,
      ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ (prod_nonneg fun _ _ => hZpos.le)
    have hδ : 0 ≤ deltaK N S.card + 2 * epsK N S.card (Pw w tc + Pw w u) := by
      have := epsK_nonneg N S.card (add_nonneg (Pw_nonneg w tc) (Pw_nonneg w u))
      have := dlev_nonneg N S.card
      have := E6_nonneg N S.card
      unfold deltaK; positivity
    exact prod_le_exp_mul_prod_L S (fun i => Num w S S t i) (fun i => Num w S S t' i) hL hδ
      (fun i hi => propM1 hN hA hG hi subset_rfl t')
      (fun i hi => (abs_le.1 (propM2 hN hA hG hS hi t t')).2)
      (fun i _ => Num_nonneg _ _ _ _ _)
  have hpos : ∀ t, 0 < sysCauseProb (tpmOf z) S s s t := by
    intro t
    rw [sysCauseProb_eq_Num]
    exact prod_pos fun i _ => div_pos (Num_pos hz s S S t i) (Zs_pos hz s)
  exact sysBackCause_le_of_ratio (tpmOf z) S s s (Real.exp_pos _) hpos hratio t

lemma Num_le_Zs (w : Param N) {S Y : Finset (Fin N)} (hY : Y ⊆ S) (t : State N) (i : Fin N) :
    Num w S Y t i ≤ Zs w := by
  unfold Num Zs
  exact sum_le_sum fun v _ => mul_le_of_le_one_left (Pw_nonneg w v) (meanW_le_one w hY t i v)

lemma exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

lemma logb_two_four : Real.logb 2 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow]; simp

lemma logb_two_sixteen : Real.logb 2 16 = 4 := by
  rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.logb_pow]; simp

/-- **Corollary Mid.** Under (HM) with the levels `L_k ≥ 6/25`, `ρ_k ≤ 1/2` and `Zs w ≤ 201/100`:
`φ_s(S) ≤ 10 k 2^{-k}`. -/
theorem corMid (hN : 1 ≤ N) {z : Param N} (hz : z ∈ openCube N) {s : State N}
    (hA : AgreeOff {tc, u} (flipP s z) w') (hG : GoodW N s0 w') {S : Finset (Fin N)}
    (hk2 : 2 ≤ S.card)
    (hL : 6 / 25 ≤ LK N S.card (Zs w') (Pw (flipP s z) tc + Pw (flipP s z) u))
    (hρ : rhoK N S.card (Zs w') (Pw (flipP s z) tc + Pw (flipP s z) u) ≤ 1 / 2)
    (hZ : Zs (flipP s z) ≤ 201 / 100) :
    phi z s S ≤ 10 * S.card / 2 ^ S.card := by
  set w := flipP s z with hw
  obtain ⟨j, hj⟩ : S.Nonempty := card_pos.1 (by omega)
  have hjS : ({j} : Finset (Fin N)) ⊆ S := singleton_subset_iff.2 hj
  have hLpos : 0 < LK N S.card (Zs w') (Pw w tc + Pw w u) := by linarith
  have hB0 : (0 : ℝ) ≤ 2 / 2 ^ S.card * 4 := by positivity
  have h := phi_le_cause hz hk2 hj hB0 fun t => by
    have hback := propM3 hN hz hA hG (by omega) hLpos t
    have hback' : sysBackCause (tpmOf z) S s s t ≤ 2 / 2 ^ S.card := by
      refine hback.trans ?_
      gcongr
      exact (Real.exp_le_exp.2 hρ).trans exp_half_le_two
    have hlog : pos (Real.logb 2 (Num w S S t j / Num w S {j} t j)) ≤ 4 := by
      have hb := propM1 hN hA hG hj hjS t
      rw [← logb_two_sixteen]
      refine pos_logb_div_le_logb (Num_pos hz s S S t j) (Num_pos hz s S {j} t j)
        (by norm_num) ?_
      have := Num_le_Zs w (subset_refl S) t j
      linarith
    exact mul_le_mul hback' hlog (pos_nonneg _) (by positivity)
  calc phi z s S ≤ S.card * (2 / 2 ^ S.card * 4) := h
    _ ≤ 10 * S.card / 2 ^ S.card := by
        rw [mul_div_assoc]
        have : (0 : ℝ) ≤ S.card / 2 ^ S.card := by positivity
        have e : (S.card : ℝ) * (2 / 2 ^ S.card * 4) = 8 * (S.card / 2 ^ S.card) := by ring
        rw [e]; linarith

/-- **Proposition KT** (tilted `k`-sets, the corrected A8 `k_upper_tilt`). -/
theorem propKT (hN : 1 ≤ N) {z : Param N} (hz : z ∈ openCube N) {s : State N}
    (hA : AgreeOff {tc, u} (flipP s z) w') (hG : GoodW N s0 w') {S : Finset (Fin N)}
    (hk2 : 2 ≤ S.card)
    (hL : 0 < LK N S.card (Zs w') (Pw (flipP s z) tc + Pw (flipP s z) u)) :
    phi z s S ≤ S.card *
      (Real.exp (rhoK N S.card (Zs w') (Pw (flipP s z) tc + Pw (flipP s z) u)) / 2 ^ S.card *
        (((1 - 2 / (2 : ℝ) ^ S.card) * (Pw (flipP s z) tc + Pw (flipP s z) u) + flK N S.card) /
          (LK N S.card (Zs w') (Pw (flipP s z) tc + Pw (flipP s z) u) * Real.log 2))) := by
  set w := flipP s z with hw
  set H := Pw w tc + Pw w u with hH
  set L := LK N S.card (Zs w') H with hLdef
  obtain ⟨j, hj⟩ : S.Nonempty := card_pos.1 (by omega)
  have hjS : ({j} : Finset (Fin N)) ⊆ S := singleton_subset_iff.2 hj
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hH0 : 0 ≤ H := add_nonneg (Pw_nonneg _ _) (Pw_nonneg _ _)
  have hc : 0 ≤ 1 - 2 / (2 : ℝ) ^ S.card := by
    have : (2 : ℝ) ≤ 2 ^ S.card := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ S.card := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [sub_nonneg, div_le_one (by positivity)]; exact this
  have hnum0 : 0 ≤ (1 - 2 / (2 : ℝ) ^ S.card) * H + flK N S.card :=
    add_nonneg (mul_nonneg hc hH0) (flK_nonneg hN _)
  have hB0 : (0 : ℝ) ≤ Real.exp (rhoK N S.card (Zs w') H) / 2 ^ S.card *
      (((1 - 2 / (2 : ℝ) ^ S.card) * H + flK N S.card) / (L * Real.log 2)) := by
    have := hL; positivity
  refine phi_le_cause hz hk2 hj hB0 fun t => ?_
  have hback := propM3 hN hz hA hG (by omega) hL t
  have hb := propM1 hN hA hG hj hjS t
  have hbpos : 0 < Num w S {j} t j := Num_pos hz s S {j} t j
  have hlog : pos (Real.logb 2 (Num w S S t j / Num w S {j} t j)) ≤
      ((1 - 2 / (2 : ℝ) ^ S.card) * H + flK N S.card) / (L * Real.log 2) := by
    refine (pos_logb_div_le_pos (Num_pos hz s S S t j) hbpos).trans ?_
    have h3 := tr3_goodW hA hG hj t
    have h4 := Num_diff_le hG hN hj (subset_refl S) hjS t
    have hdiff : Num w S S t j - Num w S {j} t j ≤
        (1 - 2 / (2 : ℝ) ^ S.card) * H + flK N S.card := by
      unfold flK
      rw [abs_le] at h4
      linarith [h4.2]
    have hmax : max (Num w S S t j - Num w S {j} t j) 0 ≤
        (1 - 2 / (2 : ℝ) ^ S.card) * H + flK N S.card := max_le hdiff hnum0
    exact div_le_div₀ hnum0 hmax (mul_pos hL hl2) (mul_le_mul_of_nonneg_right hb hl2.le)
  exact mul_le_mul hback hlog (pos_nonneg _) (by positivity)

/-! ### Corollary KT-LB -/

lemma nat_mul_32_le {k : ℕ} (hk : 6 ≤ k) : 32 * k ≤ 3 * 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

/-- `k 2^{-k} ≤ 5/32` for `k ≥ 5`. -/
lemma kdiv_le {k : ℕ} (hk : 5 ≤ k) : (k : ℝ) / 2 ^ k ≤ 5 / 32 := by
  rcases Nat.eq_or_lt_of_le hk with h | h
  · subst h; norm_num
  · have h6 := nat_mul_32_le (k := k) (by omega)
    rw [div_le_iff₀ (by positivity)]
    have : (32 * k : ℝ) ≤ 3 * 2 ^ k := by exact_mod_cast h6
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]

/-- `k 2^{-k} (1 - 2^{1-k}) ≤ 75/512` for `k ≥ 5` (the `k = 5` value). -/
lemma kdiv_mul_le {k : ℕ} (hk : 5 ≤ k) : (k : ℝ) / 2 ^ k * (1 - 2 / 2 ^ k) ≤ 75 / 512 := by
  rcases Nat.eq_or_lt_of_le hk with h | h
  · subst h; norm_num
  · have h6 := nat_mul_32_le (k := k) (by omega)
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    have hx : (k : ℝ) / 2 ^ k ≤ 3 / 32 := by
      rw [div_le_iff₀ hp]
      have : (32 * k : ℝ) ≤ 3 * 2 ^ k := by exact_mod_cast h6
      linarith
    have hx0 : 0 ≤ (k : ℝ) / 2 ^ k := by positivity
    have h1 : 1 - 2 / (2 : ℝ) ^ k ≤ 1 := by
      have : 0 ≤ 2 / (2 : ℝ) ^ k := by positivity
      linarith
    have h0 : 0 ≤ 1 - 2 / (2 : ℝ) ^ k := by
      have : (2 : ℝ) ≤ 2 ^ k := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
      rw [sub_nonneg, div_le_one hp]; exact this
    nlinarith

lemma one_div_two_pow_pred {k : ℕ} (hk : 1 ≤ k) : (k : ℝ) * (1 / 2 : ℝ) ^ (k - 1) = 2 * (k / 2 ^ k) := by
  have e : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  rw [e, one_div_pow]
  field_simp

/-- The numerical constant of KT-LB: `e^{108/1000} ≤ 11141/10000`. -/
lemma exp_108_le : Real.exp (108 / 1000) ≤ 11141 / 10000 := by
  have h := exp_le_rat (q := 108 / 1000) (r := 11141 / 10000) 10 1 (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  have e : (((108 / 1000 : ℚ)) : ℝ) = 108 / 1000 := by norm_num
  have e' : (((11141 / 10000 : ℚ)) : ℝ) = 11141 / 10000 := by norm_num
  rwa [e, e'] at h

/-- The final arithmetic of KT-LB, on plain real numbers. -/
lemma ktlb_final {φ e X L l2 P Zw : ℝ} (hphi : φ ≤ e * X / (L * l2)) (he : e ≤ 11141 / 10000)
    (hX : X ≤ 1466 / 10000 * P) (hX0 : 0 ≤ X) (hL : Zw / 2 - 5 / 10000 ≤ L)
    (hLpos : 0 < L) (hl2 : 6931 / 10000 ≤ l2) (hZw : 1 / 2 - 2 / 10000 ≤ Zw) (hP : 0 ≤ P) :
    φ ≤ 12 / 25 * (P / Zw) := by
  have hl2pos : 0 < l2 := by linarith
  have hZwpos : 0 < Zw := by linarith
  refine hphi.trans ?_
  rw [div_le_iff₀ (mul_pos hLpos hl2pos)]
  have h1 : e * X ≤ 11141 / 10000 * (1466 / 10000 * P) := mul_le_mul he hX hX0 (by norm_num)
  have h2 : 12 / 25 * (P / Zw) * ((Zw / 2 - 5 / 10000) * (6931 / 10000)) ≤
      12 / 25 * (P / Zw) * (L * l2) := by
    have hPZ : 0 ≤ 12 / 25 * (P / Zw) := mul_nonneg (by norm_num) (div_nonneg hP hZwpos.le)
    refine mul_le_mul_of_nonneg_left ?_ hPZ
    exact mul_le_mul hL hl2 (by norm_num) hLpos.le
  have h3 : 11141 / 10000 * (1466 / 10000 * P) ≤
      12 / 25 * (P / Zw) * ((Zw / 2 - 5 / 10000) * (6931 / 10000)) := by
    have e1 : 12 / 25 * (P / Zw) * ((Zw / 2 - 5 / 10000) * (6931 / 10000)) =
        P * (12 / 25 * (6931 / 10000) * (1 / 2 - 5 / 10000 / Zw)) := by
      field_simp
    rw [e1]
    have hq : 5 / 10000 / Zw ≤ 5 / 10000 / (1 / 2 - 2 / 10000) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hZw
    have h4 : 11141 / 10000 * (1466 / 10000) ≤
        12 / 25 * (6931 / 10000) * (1 / 2 - 5 / 10000 / Zw) := by
      have : (1 / 2 : ℝ) - 5 / 10000 / (1 / 2 - 2 / 10000) ≤ 1 / 2 - 5 / 10000 / Zw := by linarith
      nlinarith
    nlinarith
  linarith

/-- **Corollary KT-LB** (deterministic form). With `ε = 10^{-4}`: if the eventual levels of EV1/EV5
hold at `N` (hypotheses `n1`-`n6`), `N H ≤ ε`, `N^9 σ_N ≤ P_tc`, `P_s ≤ ε P_tc` and
`5 ≤ |S| ≤ K2N N`, then `φ_s(S) ≤ (12/25) β` with `β = P_tc / Zs w`. -/
theorem corKTLB (hN : 1 ≤ N) {z : Param N} (hz : z ∈ openCube N) {s tc : State N}
    (hA : AgreeOff {tc, s} (flipP s z) w') (hG : GoodW N s0 w') {S : Finset (Fin N)}
    (hk5 : 5 ≤ S.card)
    (n1 : 8 * N * sigN N ≤ 1 / 10000)
    (n2 : (N : ℝ) * dlev N S.card ≤ 1 / 10000)
    (n3 : (N : ℝ) * (2 * tauN N + 2 * Mk N S.card) ≤ 1 / 10000)
    (n4 : 64 * (N : ℝ) ^ 2 * sigN N ≤ 1 / 10000)
    (n5 : (S.card : ℝ) / 2 ^ S.card * flK N S.card ≤ 1 / 10000 * ((N : ℝ) ^ 9 * sigN N))
    (hNH : (N : ℝ) * (Pw (flipP s z) tc + Pw (flipP s z) s) ≤ 1 / 10000)
    (hP : (N : ℝ) ^ 9 * sigN N ≤ Pw (flipP s z) tc)
    (hPs : Pw (flipP s z) s ≤ 1 / 10000 * Pw (flipP s z) tc) :
    phi z s S ≤ 12 / 25 * (Pw (flipP s z) tc / Zs (flipP s z)) := by
  set w := flipP s z with hw
  set k := S.card with hkdef
  set H := Pw w tc + Pw w s with hHdef
  set P := Pw w tc with hPdef
  set Z' := Zs w' with hZ'
  set Zw := Zs w with hZw
  set L := LK N k Z' H with hLdef
  set ρ := rhoK N k Z' H with hρdef
  set x : ℝ := (k : ℝ) / 2 ^ k with hx
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hσ := sigN_pos N
  have hτ := tauN_pos N
  have hP0 : 0 ≤ P := Pw_nonneg _ _
  have hH0 : 0 ≤ H := add_nonneg (Pw_nonneg _ _) (Pw_nonneg _ _)
  have hdl0 := dlev_nonneg N k
  have hMk0 := Mk_nonneg N k
  have hE60 := E6_nonneg N k
  have hZ'1 := hG.g3.1
  have hZ'2 := hG.g3.2.1
  obtain ⟨htr1a, htr1b⟩ := tr1 hA hG.g2
  have hHle : H ≤ 1 / 10000 := by
    have : H ≤ (N : ℝ) * H := le_mul_of_one_le_left hH0 hN'
    linarith
  have hdl : dlev N k ≤ 1 / 10000 := by
    have : dlev N k ≤ (N : ℝ) * dlev N k := le_mul_of_one_le_left hdl0 hN'
    linarith
  have htm : 2 * tauN N + 2 * Mk N k ≤ 1 / 10000 := by
    have h0 : 0 ≤ 2 * tauN N + 2 * Mk N k := by positivity
    have : 2 * tauN N + 2 * Mk N k ≤ (N : ℝ) * (2 * tauN N + 2 * Mk N k) :=
      le_mul_of_one_le_left h0 hN'
    linarith
  -- the levels
  have hL1 : 1 / 4 - 4 / 10000 ≤ L := by
    simp only [hLdef, LK, epsK]; linarith
  have hL2 : Zw / 2 - 5 / 10000 ≤ L := by
    simp only [hLdef, LK, epsK]; linarith
  have hLpos : 0 < L := by linarith
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast card_le_N S
  have hk1 : 1 ≤ k := by omega
  have hnum : (k : ℝ) * (deltaK N k + 2 * epsK N k H) ≤ x / 6 + 7 / 10000 := by
    have e1 : (k : ℝ) * (deltaK N k + 2 * epsK N k H) =
        ((k : ℝ) * (1 / 2 : ℝ) ^ (k - 1)) / 12 + (k : ℝ) * E6 N k / 12 + 2 * ((k : ℝ) * dlev N k)
          + 2 * ((k : ℝ) * H) + 2 * ((k : ℝ) * (2 * tauN N + 2 * Mk N k)) := by
      unfold deltaK epsK; ring
    rw [e1, one_div_two_pow_pred hk1]
    have a1 : (k : ℝ) * E6 N k ≤ 1 / 10000 := by
      calc (k : ℝ) * E6 N k ≤ N * (64 * N * sigN N) :=
            mul_le_mul hkN (E6_le k hN) hE60 (by positivity)
        _ = 64 * (N : ℝ) ^ 2 * sigN N := by ring
        _ ≤ 1 / 10000 := n4
    have a2 : (k : ℝ) * dlev N k ≤ 1 / 10000 := (mul_le_mul_of_nonneg_right hkN hdl0).trans n2
    have a3 : (k : ℝ) * H ≤ 1 / 10000 := (mul_le_mul_of_nonneg_right hkN hH0).trans hNH
    have a4 : (k : ℝ) * (2 * tauN N + 2 * Mk N k) ≤ 1 / 10000 :=
      (mul_le_mul_of_nonneg_right hkN (by positivity)).trans n3
    linarith
  have hxle := kdiv_le hk5
  have hρle : ρ ≤ 108 / 1000 := by
    simp only [hρdef, rhoK]
    rw [div_le_iff₀ hLpos]
    nlinarith
  have hexp : Real.exp ρ ≤ 11141 / 10000 := (Real.exp_le_exp.2 hρle).trans exp_108_le
  -- Proposition KT
  have hKT : phi z s S ≤ (k : ℝ) * (Real.exp ρ / 2 ^ k *
      (((1 - 2 / (2 : ℝ) ^ k) * H + flK N k) / (L * Real.log 2))) :=
    propKT hN hz hA hG (by omega) hLpos
  have hX := kdiv_mul_le hk5
  have hfl := n5
  have hHP : H ≤ (1 + 1 / 10000) * P := by simp only [hHdef]; linarith
  have hflP : x * flK N k ≤ 1 / 10000 * P := hfl.trans (by linarith)
  -- `(k/2^k) ((1 - 2/2^k) H + fl) ≤ c P`
  have hc0 : 0 ≤ 1 - 2 / (2 : ℝ) ^ k := by
    have : (2 : ℝ) ≤ 2 ^ k := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [sub_nonneg, div_le_one (by positivity)]; exact this
  have hx0 : 0 ≤ x := by positivity
  have hcP : x * ((1 - 2 / (2 : ℝ) ^ k) * H + flK N k) ≤ 1466 / 10000 * P := by
    have e : x * ((1 - 2 / (2 : ℝ) ^ k) * H + flK N k) =
        (x * (1 - 2 / (2 : ℝ) ^ k)) * H + x * flK N k := by ring
    rw [e]
    have hXx : x * (1 - 2 / (2 : ℝ) ^ k) ≤ 75 / 512 := hX
    have hX0 : 0 ≤ x * (1 - 2 / (2 : ℝ) ^ k) := mul_nonneg hx0 hc0
    have : x * (1 - 2 / (2 : ℝ) ^ k) * H ≤ 75 / 512 * ((1 + 1 / 10000) * P) :=
      mul_le_mul hXx hHP hH0 (by norm_num)
    nlinarith
  have hl2 := Real.log_two_gt_d9
  have hl2pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hZwpos : 0 < Zw := by linarith
  have hRHS : (k : ℝ) * (Real.exp ρ / 2 ^ k *
      (((1 - 2 / (2 : ℝ) ^ k) * H + flK N k) / (L * Real.log 2))) =
      Real.exp ρ * (x * ((1 - 2 / (2 : ℝ) ^ k) * H + flK N k)) / (L * Real.log 2) := by
    simp only [hx]; field_simp
  rw [hRHS] at hKT
  have hX0' : 0 ≤ x * ((1 - 2 / (2 : ℝ) ^ k) * H + flK N k) := by
    have := flK_nonneg hN k
    exact mul_nonneg hx0 (add_nonneg (mul_nonneg hc0 hH0) this)
  exact ktlb_final hKT hexp hcP hX0' hL2 hLpos (by linarith)
    (by linarith) hP0

end MidSizes

/-! ## 4. Theorem B5: near-universe candidates `K2N N < |S| < N` -/

section B5

/-- `ρ0 = e^{43/100} / 2`, the per-unit factor of the heavy-pattern bound. -/
def rho0 : ℝ := Real.exp (43 / 100) / 2

lemma rho0_pos : 0 < rho0 := by unfold rho0; positivity

/-- (C17c) `e^{68/100} < 2`, i.e. `ρ0 e^{1/4} < 1`. -/
lemma rho0_mul_exp_lt_one : rho0 * Real.exp (1 / 4) < 1 := by
  have h := exp_le_rat (q := 68 / 100) (r := 198 / 100) 10 1 (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel)
  have e : (((68 / 100 : ℚ)) : ℝ) = 68 / 100 := by norm_num
  have e' : (((198 / 100 : ℚ)) : ℝ) = 198 / 100 := by norm_num
  rw [e, e'] at h
  unfold rho0
  rw [div_mul_eq_mul_div, ← Real.exp_add, div_lt_one two_pos]
  have : (43 / 100 : ℝ) + 1 / 4 = 68 / 100 := by norm_num
  rw [this]; linarith

lemma rho0_lt_one : rho0 < 1 := by
  have h := rho0_mul_exp_lt_one
  have h1 : 1 ≤ Real.exp (1 / 4) := Real.one_le_exp (by norm_num)
  nlinarith [rho0_pos]

lemma rho0_pow (k : ℕ) : rho0 ^ k = (1 / 2 : ℝ) ^ k * Real.exp (43 / 100 * k) := by
  unfold rho0
  rw [div_pow, ← Real.exp_nat_mul, one_div_pow]
  field_simp

/-- `ρ0^{10} ≤ 1/8`. -/
lemma rho0_pow_ten : rho0 ^ 10 ≤ 1 / 8 := by
  have h := rho0_mul_exp_lt_one
  have h8 := rat_le_exp (q := 5 / 2) (r := 8) 10 3 (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
  have e : (((5 / 2 : ℚ)) : ℝ) = 5 / 2 := by norm_num
  rw [e] at h8
  have h0 := rho0_pos
  have hlt : rho0 < Real.exp (-(1 / 4)) := by
    rw [Real.exp_neg, lt_inv_comm₀ h0 (Real.exp_pos _)] at *
    rw [inv_eq_one_div, lt_div_iff₀ h0]
    linarith
  have hp : rho0 ^ 10 ≤ Real.exp (-(1 / 4)) ^ 10 := pow_le_pow_left₀ h0.le hlt.le 10
  rw [← Real.exp_nat_mul] at hp
  have : Real.exp (((10 : ℕ) : ℝ) * -(1 / 4)) = 1 / Real.exp (5 / 2) := by
    rw [eq_div_iff (Real.exp_pos _).ne', ← Real.exp_add]; norm_num
  rw [this] at hp
  refine hp.trans ?_
  rw [div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  push_cast at h8
  linarith

lemma sum_union_le_of_nonneg {α : Type*} [DecidableEq α] (A B : Finset α) {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : ∑ x ∈ A ∪ B, f x ≤ ∑ x ∈ A, f x + ∑ x ∈ B, f x := by
  have := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f)
  have h0 : 0 ≤ ∑ x ∈ A ∩ B, f x := sum_nonneg fun x _ => hf x
  linarith

/-- **Theorem B5** (deterministic form): given the eventual inequalities of W4 4.7 at `N`,
`N ≤ 3 ham(tc, s)`, `w̃ ∈ E5 N s tc` agreeing with `w = flipP s z` off `{tc, s}` and
`H = Pw tc + Pw s ≤ N^{-3}`, every candidate with `K2N N < |S| < N` has `φ_s(S) ≤ e^{-N/4}`. -/
theorem thmB5_det (hN : 1 ≤ N) (hbig : 10 ≤ K2N N) (h3D : 3 * D1 N ≤ N)
    (hη' : etaB N + 2 ^ (D1 N + 1) * tauN N ≤ 1 / 2)
    (hratio : (1 + etaB N + 2 / (N : ℝ) ^ 3) ^ N ≤
      2 * (1 - (etaB N + 2 ^ (D1 N + 1) * tauN N)) ^ N)
    (hhoeff : ∀ k, K2N N < k → k ≤ N → deltaH N (k - 1) + 2 / (2 : ℝ) ^ (k - 1) ≤ 1 / 4)
    (hrate : ∀ k, K2N N < k → k ≤ N → 8 * (k : ℝ) * rho0 ^ k ≤ Real.exp (-(N : ℝ) / 4))
    {s tc : State N} (hham : N ≤ 3 * ham tc s) {z : Param N} (hz : z ∈ openCube N)
    {w' : Param N} (hA : AgreeOff {tc, s} (flipP s z) w') (hE : w' ∈ E5 N s tc)
    (hH : Pw (flipP s z) tc + Pw (flipP s z) s ≤ 1 / (N : ℝ) ^ 3)
    {S : Finset (Fin N)} (hk : K2N N < S.card) (hk' : S.card < N) :
    phi z s S ≤ Real.exp (-(N : ℝ) / 4) := by
  set w := flipP s z with hw
  set k := S.card with hkdef
  have hkN : k ≤ N := card_le_N S
  have hdD : N - k < D1 N := sub_card_lt_D1 hk
  have hk10 : 10 ≤ k := by omega
  obtain ⟨⟨⟨⟨⟨⟨hg2, hEH⟩, hEW⟩, hECr⟩, hECh⟩, hEFtc⟩, hEFs⟩ := hE
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set H := Pw w tc + Pw w s with hHdef
  have hH0 : 0 ≤ H := add_nonneg (Pw_nonneg _ _) (Pw_nonneg _ _)
  /- (G) the two fixed rows never share a pattern on `S` -/
  have hGeo : ∀ a ∈ ({tc, s} : Finset (State N)), ∀ b ∈ ({tc, s} : Finset (State N)),
      (∀ j ∈ S, a j = b j) → a = b := by
    have key : ¬ ∀ j ∈ S, tc j = s j := by
      intro h
      have hsub : (univ.filter fun j => tc j ≠ s j) ⊆ Sᶜ := by
        intro j hj; rw [mem_compl]; intro hjS; exact (mem_filter.1 hj).2 (h j hjS)
      have hc := card_le_card hsub
      rw [card_compl, Fintype.card_fin] at hc
      unfold ham at hham
      omega
    intro a ha b hb hab
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact absurd hab key
    · exact absurd (fun j hj => (hab j hj).symm) key
    · rfl
  have hGplus : ∀ a ∈ ({tc, s} : Finset (State N)), ∀ r ∈ (agree S a).erase a,
      r ∉ ({tc, s} : Finset (State N)) := by
    intro a ha r hr hrA
    exact ne_of_mem_erase hr (hGeo r hrA a ha (mem_agree.1 (mem_of_mem_erase hr)))
  /- generic patterns see only the fresh rows -/
  have hgen : ∀ t, ¬ ((∀ j ∈ S, t j = tc j) ∨ (∀ j ∈ S, t j = s j)) →
      ∀ i, colMean w S t i = colMean w' S t i := by
    intro t ht i
    refine tr4_eq hA (fun a ha hat => ht ?_) i
    rw [mem_agree] at hat
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Or.inl fun j hj => (hat j hj).symm
    · exact Or.inr fun j hj => (hat j hj).symm
  /- (B5-b) the level `43/100` for every pattern -/
  have hheavy : ∀ a ∈ ({tc, s} : Finset (State N)), w' ∈ EF N a → ∀ t, (∀ j ∈ S, t j = a j) →
      ∑ i ∈ S, Real.log (max (2 * colMean w S t i) 1) ≤ 43 / 100 * k := by
    intro a ha hEF t hta
    refine le_trans (sum_le_sum fun i _ => ?_) (hEF S hk hk')
    rw [colMean_congr_agree w hta i]
    have h1 := colMean_le_colMeanPlus w S a i
    rw [colMeanPlus_congr hA (hGplus a ha) i] at h1
    apply Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _))
    exact max_le_max (by linarith) le_rfl
  have hlogsum : ∀ t, ∑ i ∈ S, Real.log (max (2 * colMean w S t i) 1) ≤ 43 / 100 * k := by
    intro t
    by_cases ht : (∀ j ∈ S, t j = tc j) ∨ (∀ j ∈ S, t j = s j)
    · rcases ht with ht | ht
      · exact hheavy tc (mem_insert_self _ _) hEFtc t ht
      · exact hheavy s (by simp) hEFs t ht
    · rw [sum_congr rfl fun i _ => by rw [hgen t ht i]]
      have := hECr S t hk hk'
      rw [← hkdef] at this
      linarith
  have hprodmax : ∀ t, ∏ i ∈ S, max (2 * colMean w S t i) 1 ≤ Real.exp (43 / 100 * k) := by
    intro t
    have hpos : ∀ i ∈ S, 0 < max (2 * colMean w S t i) 1 :=
      fun i _ => lt_of_lt_of_le one_pos (le_max_right _ _)
    rw [← Real.exp_log (prod_pos hpos), Real.log_prod (fun i hi => (hpos i hi).ne')]
    exact Real.exp_le_exp.2 (hlogsum t)
  /- (B5-a) block masses -/
  set η := etaB N with hη
  set η' := etaB N + 2 ^ (D1 N + 1) * tauN N with hη'def
  have hη0 : 0 ≤ η := (Real.exp_pos _).le
  have hη'0 : 0 ≤ η' := by have := tauN_pos N; positivity
  set u : ℝ := (1 / 2 : ℝ) ^ (N - k) with hu
  have hu0 : 0 < u := by positivity
  have h2du : (1 : ℝ) ≤ 2 ^ D1 N * u := by
    have e : (2 : ℝ) ^ D1 N = 2 ^ (N - k) * 2 ^ (D1 N - (N - k)) := by
      rw [← pow_add]; congr 1; omega
    rw [e, hu, mul_comm ((2 : ℝ) ^ (N - k)), mul_assoc, ← mul_pow]
    norm_num
    exact one_le_pow₀ (by norm_num)
  have hbo : ∀ r, (1 - η') * u ≤ blockPo {tc, s} w' S r ∧
      blockPo {tc, s} w' S r ≤ (1 + η) * u := by
    intro r
    obtain ⟨h1, h2, -⟩ := tr5 hA hg2 S r
    have h3 := hEW S r hk hk'
    rw [← hkdef, ← hu, abs_le] at h3
    have hτ := tauN_pos N
    have h4 : 2 * tauN N ≤ 2 ^ (D1 N + 1) * tauN N * u := by
      rw [pow_succ]; nlinarith
    constructor
    · simp only [hη'def]; nlinarith
    · linarith
  have hcm : ∀ t i, colMean w S t i = u * ∑ r ∈ agree S t, clamp01 (w r i) := by
    intro t i
    rw [colMean, ← hkdef, hu, one_div_pow]; ring
  have hNumUp : ∀ t i, Num w S S t i ≤ (1 + η) * colMean w S t i + H := by
    intro t i
    rw [Num_S_eq_blockPo hA S t i]
    have hA2 : ∑ a ∈ ({tc, s} : Finset (State N)), clamp01 (w (merge S t a) i) * Pw w a ≤ H :=
      (sum_le_sum fun a _ => mul_le_of_le_one_left (Pw_nonneg w a) (clamp01_le_one _)).trans
        (sum_pair_le (Pw_nonneg w) tc s)
    have hA1 : ∑ r ∈ agree S t, clamp01 (w r i) * blockPo {tc, s} w' S r ≤
        (1 + η) * colMean w S t i := by
      rw [hcm t i, ← mul_assoc, mul_comm ((1 + η) * u), sum_mul]
      refine sum_le_sum fun r _ => ?_
      exact mul_le_mul_of_nonneg_left (hbo r).2 (clamp01_nonneg _)
    linarith
  have hNumLo : ∀ t i, (1 - η') * colMean w S t i ≤ Num w S S t i := by
    intro t i
    rw [Num_S_eq_blockPo hA S t i]
    have hB0 : 0 ≤ ∑ a ∈ ({tc, s} : Finset (State N)), clamp01 (w (merge S t a) i) * Pw w a :=
      sum_nonneg fun a _ => mul_nonneg (clamp01_nonneg _) (Pw_nonneg _ _)
    have hA1 : (1 - η') * colMean w S t i ≤
        ∑ r ∈ agree S t, clamp01 (w r i) * blockPo {tc, s} w' S r := by
      rw [hcm t i, ← mul_assoc, mul_comm ((1 - η') * u), sum_mul]
      refine sum_le_sum fun r _ => ?_
      exact mul_le_mul_of_nonneg_left (hbo r).1 (clamp01_nonneg _)
    linarith
  /- (★) and the numerator -/
  have hstar : ∀ G : ℝ, 0 ≤ G → (1 + η) * G + H ≤ 1 / 2 * ((1 + η + 2 * H) * max (2 * G) 1) := by
    intro G hG
    rcases le_total 1 (2 * G) with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]; nlinarith
  have hprodUp : ∀ t, ∏ i ∈ S, Num w S S t i ≤
      (1 / 2) ^ k * (1 + η + 2 * H) ^ k * Real.exp (43 / 100 * k) := by
    intro t
    calc ∏ i ∈ S, Num w S S t i
        ≤ ∏ i ∈ S, (1 / 2 * ((1 + η + 2 * H) * max (2 * colMean w S t i) 1)) :=
          prod_le_prod (fun i _ => Num_nonneg _ _ _ _ _)
            (fun i _ => (hNumUp t i).trans (hstar _ (colMean_nonneg _ _ _ _)))
      _ = (1 / 2) ^ k * (1 + η + 2 * H) ^ k * ∏ i ∈ S, max (2 * colMean w S t i) 1 := by
          rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_const]; ring
      _ ≤ _ := by
          have : (0 : ℝ) ≤ (1 / 2) ^ k * (1 + η + 2 * H) ^ k := by positivity
          exact mul_le_mul_of_nonneg_left (hprodmax t) this
  /- (B5-c) the normaliser -/
  have hPa : ∀ a, ∏ i ∈ S, colMean w' S a i ≤ 1 / 8 := by
    intro a
    have hpos : ∀ i ∈ S, 0 < max (2 * colMean w' S a i) 1 :=
      fun i _ => lt_of_lt_of_le one_pos (le_max_right _ _)
    have h1 : ∏ i ∈ S, colMean w' S a i ≤ (1 / 2) ^ k * ∏ i ∈ S, max (2 * colMean w' S a i) 1 := by
      calc ∏ i ∈ S, colMean w' S a i ≤ ∏ i ∈ S, (1 / 2 * max (2 * colMean w' S a i) 1) :=
            prod_le_prod (fun i _ => colMean_nonneg _ _ _ _) fun i _ => by
              have := le_max_left (2 * colMean w' S a i) 1; linarith
        _ = (1 / 2) ^ k * ∏ i ∈ S, max (2 * colMean w' S a i) 1 := by
            rw [prod_mul_distrib, prod_const]
    have h2 : ∏ i ∈ S, max (2 * colMean w' S a i) 1 ≤ Real.exp (43 / 100 * k) := by
      rw [← Real.exp_log (prod_pos hpos), Real.log_prod (fun i hi => (hpos i hi).ne')]
      refine Real.exp_le_exp.2 ?_
      have := hECr S a hk hk'
      rw [← hkdef] at this
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      linarith
    have h3 : (1 / 2 : ℝ) ^ k * Real.exp (43 / 100 * k) ≤ 1 / 8 := by
      rw [← rho0_pow]
      exact (pow_le_pow_of_le_one rho0_pos.le rho0_lt_one.le hk10).trans rho0_pow_ten
    calc ∏ i ∈ S, colMean w' S a i ≤ (1 / 2) ^ k * ∏ i ∈ S, max (2 * colMean w' S a i) 1 := h1
      _ ≤ (1 / 2) ^ k * Real.exp (43 / 100 * k) := by gcongr
      _ ≤ 1 / 8 := h3
  have hsumA : ∀ a, ∑ t ∈ agree S a, ∏ i ∈ S, colMean w' S t i ≤ 2 ^ (N - k) / 8 := by
    intro a
    have e : ∀ t ∈ agree S a, ∏ i ∈ S, colMean w' S t i = ∏ i ∈ S, colMean w' S a i :=
      fun t ht => prod_congr rfl fun i _ => colMean_congr_agree w' (mem_agree.1 ht) i
    rw [sum_congr rfl e, sum_const, card_agree, nsmul_eq_mul, ← hkdef]
    push_cast
    have := hPa a
    have h2 : (0 : ℝ) < 2 ^ (N - k) := by positivity
    nlinarith
  have hnorm : (1 - η') ^ k * (2 ^ (N - k) / 2) ≤ ∑ t : State N, ∏ i ∈ S, Num w S S t i := by
    classical
    set hv : State N → Prop := fun t => (∀ j ∈ S, t j = tc j) ∨ (∀ j ∈ S, t j = s j) with hhv
    have hP0 : ∀ t, 0 ≤ ∏ i ∈ S, colMean w' S t i := fun t =>
      prod_nonneg fun i _ => colMean_nonneg _ _ _ _
    have hsplit := sum_filter_add_sum_filter_not (univ : Finset (State N)) hv
      (fun t => ∏ i ∈ S, colMean w' S t i)
    have hheavysum : ∑ t ∈ univ.filter hv, ∏ i ∈ S, colMean w' S t i ≤ 2 ^ (N - k) / 4 := by
      have hsub : univ.filter hv ⊆ agree S tc ∪ agree S s := by
        intro t ht
        rcases (mem_filter.1 ht).2 with h | h
        · exact mem_union_left _ (mem_agree.2 h)
        · exact mem_union_right _ (mem_agree.2 h)
      calc ∑ t ∈ univ.filter hv, ∏ i ∈ S, colMean w' S t i
          ≤ ∑ t ∈ agree S tc ∪ agree S s, ∏ i ∈ S, colMean w' S t i :=
            sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => hP0 t
        _ ≤ ∑ t ∈ agree S tc, ∏ i ∈ S, colMean w' S t i +
            ∑ t ∈ agree S s, ∏ i ∈ S, colMean w' S t i := sum_union_le_of_nonneg _ _ hP0
        _ ≤ 2 ^ (N - k) / 8 + 2 ^ (N - k) / 8 := add_le_add (hsumA tc) (hsumA s)
        _ = 2 ^ (N - k) / 4 := by ring
    have hall := hECh S hk hk'
    rw [← hkdef] at hall
    have hgeneric : (1 - η') ^ k * ∑ t ∈ univ.filter (fun t => ¬ hv t),
        ∏ i ∈ S, colMean w' S t i ≤ ∑ t : State N, ∏ i ∈ S, Num w S S t i := by
      rw [mul_sum]
      refine le_trans (sum_le_sum fun t ht => ?_)
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun t _ _ =>
          prod_nonneg fun i _ => Num_nonneg _ _ _ _ _)
      have hgt := hgen t (mem_filter.1 ht).2
      calc (1 - η') ^ k * ∏ i ∈ S, colMean w' S t i
          = ∏ i ∈ S, ((1 - η') * colMean w S t i) := by
            rw [prod_mul_distrib, prod_const]
            exact congrArg _ (prod_congr rfl fun i _ => (hgt i).symm)
        _ ≤ ∏ i ∈ S, Num w S S t i :=
            prod_le_prod (fun i _ => mul_nonneg (by linarith) (colMean_nonneg _ _ _ _))
              fun i _ => hNumLo t i
    have hpowpos : 0 ≤ (1 - η') ^ k := pow_nonneg (by linarith) k
    have h2 : (0 : ℝ) < 2 ^ (N - k) := by positivity
    have hge : 2 ^ (N - k) / 2 ≤ ∑ t ∈ univ.filter (fun t => ¬ hv t),
        ∏ i ∈ S, colMean w' S t i := by linarith
    calc (1 - η') ^ k * (2 ^ (N - k) / 2)
        ≤ (1 - η') ^ k * ∑ t ∈ univ.filter (fun t => ¬ hv t), ∏ i ∈ S, colMean w' S t i :=
          mul_le_mul_of_nonneg_left hge hpowpos
      _ ≤ _ := hgeneric
  /- (B5-d) the backward cause probability -/
  have hrat : (1 + η + 2 * H) ^ k ≤ 2 * (1 - η') ^ k := by
    have hb1 : 1 + η + 2 * H ≤ 1 + η + 2 / (N : ℝ) ^ 3 := by
      have : 2 * H ≤ 2 * (1 / (N : ℝ) ^ 3) := by linarith
      have e : 2 * (1 / (N : ℝ) ^ 3) = 2 / (N : ℝ) ^ 3 := by ring
      linarith
    have hb0 : 0 ≤ 1 + η + 2 * H := by positivity
    have hge1 : 1 ≤ 1 + η + 2 / (N : ℝ) ^ 3 := by
      have : (0 : ℝ) ≤ 2 / (N : ℝ) ^ 3 := by positivity
      linarith
    calc (1 + η + 2 * H) ^ k ≤ (1 + η + 2 / (N : ℝ) ^ 3) ^ k := pow_le_pow_left₀ hb0 hb1 k
      _ ≤ (1 + η + 2 / (N : ℝ) ^ 3) ^ N := pow_le_pow_right₀ hge1 hkN
      _ ≤ 2 * (1 - η') ^ N := hratio
      _ ≤ 2 * (1 - η') ^ k := by
          have : (1 - η') ^ N ≤ (1 - η') ^ k :=
            pow_le_pow_of_le_one (by linarith) (by linarith) hkN
          linarith
  have hback : ∀ t, sysBackCause (tpmOf z) S s s t ≤ 4 * rho0 ^ k := by
    intro t
    rw [sysBackCause_eq_Num hz s t S, ← hw, ← hkdef]
    have hY : 0 < (1 - η') ^ k := pow_pos (by linarith) k
    have h2 : (0 : ℝ) < 2 ^ (N - k) := by positivity
    have hden : 0 < ∑ t' : State N, ∏ i ∈ S, Num w S S t' i :=
      lt_of_lt_of_le (by positivity) hnorm
    rw [div_le_iff₀ hden]
    have hnum := hprodUp t
    have hE0 : 0 ≤ Real.exp (43 / 100 * k) := (Real.exp_pos _).le
    calc (2 : ℝ) ^ (N - k) * ∏ i ∈ S, Num w S S t i
        ≤ 2 ^ (N - k) * ((1 / 2) ^ k * (1 + η + 2 * H) ^ k * Real.exp (43 / 100 * k)) :=
          mul_le_mul_of_nonneg_left hnum h2.le
      _ ≤ 2 ^ (N - k) * ((1 / 2) ^ k * (2 * (1 - η') ^ k) * Real.exp (43 / 100 * k)) := by
          gcongr
      _ = 4 * rho0 ^ k * ((1 - η') ^ k * (2 ^ (N - k) / 2)) := by rw [rho0_pow]; ring
      _ ≤ 4 * rho0 ^ k * ∑ t' : State N, ∏ i ∈ S, Num w S S t' i := by
          have : 0 ≤ 4 * rho0 ^ k := by have := rho0_pos; positivity
          exact mul_le_mul_of_nonneg_left hnorm this
  /- (B5-e) the log-ratio -/
  have hlog2 : ∀ t, ∀ j ∈ S, pos (Real.logb 2 (Num w S S t j / Num w S {j} t j)) ≤ 2 := by
    intro t j hj
    have hjS : ({j} : Finset (Fin N)) ⊆ S := singleton_subset_iff.2 hj
    have hlow : Zs w / 4 ≤ Num w S {j} t j := by
      have hpt : ∀ v, 1 / 4 * Pw w v ≤ meanW w S {j} t j v * Pw w v := by
        intro v
        refine mul_le_mul_of_nonneg_right ?_ (Pw_nonneg w v)
        rw [meanW_eq_colMean w hjS t j v]
        have hM : N - ({j} ∪ Sᶜ).card = k - 1 := by
          rw [card_union_compl hjS, card_singleton]; omega
        have h1 := tr4_pair hA ({j} ∪ Sᶜ) (merge S t v) j
        have h2 := hEH ({j} ∪ Sᶜ) (merge S t v) j
        rw [hM] at h1 h2
        have h3 := hhoeff k hk hkN
        rw [abs_le] at h1 h2
        linarith [h1.1, h2.1]
      calc Zs w / 4 = ∑ v, 1 / 4 * Pw w v := by rw [Zs, ← mul_sum]; ring
        _ ≤ ∑ v, meanW w S {j} t j v * Pw w v := sum_le_sum fun v _ => hpt v
        _ = Num w S {j} t j := rfl
    have hup := Num_le_Zs w (subset_refl S) t j
    refine (pos_logb_div_le_logb (c := 4) (Num_pos hz s S S t j) (Num_pos hz s S {j} t j)
      (by norm_num) (by linarith)).trans (le_of_eq logb_two_four)
  /- (B5-f) conclusion -/
  obtain ⟨j, hj⟩ : S.Nonempty := card_pos.1 (by omega)
  have hB0 : (0 : ℝ) ≤ 4 * rho0 ^ k * 2 := by have := rho0_pos; positivity
  have h := phi_le_cause hz (by omega : 2 ≤ S.card) hj hB0 fun t =>
    mul_le_mul (hback t) (hlog2 t j hj) (pos_nonneg _) (by have := rho0_pos; positivity)
  calc phi z s S ≤ k * (4 * rho0 ^ k * 2) := h
    _ = 8 * k * rho0 ^ k := by ring
    _ ≤ Real.exp (-(N : ℝ) / 4) := hrate k hk hkN

end B5

/-! ## 5. The eventual numeric inequalities (W4 4.7, EV1-EV5, and the EW budget) -/

section Eventual

lemma two_pow_D1_le (hN : 1 ≤ N) : (2 : ℝ) ^ D1 N ≤ 2 ^ 16 * (N : ℝ) ^ 4 := by
  have h' : ((2 : ℝ) ^ Nat.log 2 N) ≤ N := by exact_mod_cast two_pow_natLog_le hN
  have e : (2 : ℝ) ^ D1 N = 2 ^ 16 * ((2 : ℝ) ^ Nat.log 2 N) ^ 4 := by
    unfold D1
    rw [show 4 * Nat.log 2 N + 16 = Nat.log 2 N * 4 + 16 by ring, pow_add, pow_mul]; ring
  rw [e]; gcongr

lemma half_pow_le_sigN (N : ℕ) : (1 / 2 : ℝ) ^ N ≤ sigN N := by
  rw [sigN]
  refine Real.le_sqrt_of_sq_le ?_
  rw [← pow_mul, mul_comm, pow_mul]
  gcongr
  norm_num

lemma tauN_eq (N : ℕ) : tauN N = Real.exp (2 / 9) * Real.exp (-(2 / 9 * N)) := by
  unfold tauN; rw [← Real.exp_add]; congr 1; ring

lemma two_thirds_pow_eq (N : ℕ) : (2 / 3 : ℝ) ^ N = Real.exp (-(2 * x0 * N)) := by
  rw [← sigN_sq, sigN_eq_exp, sq, ← Real.exp_add]; congr 1; ring

lemma etaB_eq (N : ℕ) : etaB N = Real.exp (-(1 / 10 * N)) := by
  unfold etaB; congr 1; ring

lemma two_rpow_eq (N : ℕ) : (2 : ℝ) ^ (-(N : ℝ) / 3) = Real.exp (-(Real.log 2 / 3 * N)) := by
  rw [Real.rpow_def_of_pos two_pos]; congr 1; ring

/-- The EW budget holds eventually. -/
lemma ev_EWnum : ∀ᶠ N : ℕ in atTop, EWnum N := by
  have hx0 := x0_gt
  filter_upwards [eventually_ge_atTop 1,
    ev_poly_exp 5 (3 * 2 ^ 20) (c := 1027 / 10000) (by norm_num) (by norm_num : (0 : ℝ) < 1),
    ev_poly_exp 5 (3 * 2 ^ 20 * Real.exp (2 / 9)) (c := 2 / 9 - 1 / 10) (by norm_num)
      (by norm_num : (0 : ℝ) < 1),
    ev_poly_exp 0 (3 * Real.exp (-(2 / 9))) (c := 8 / 100) (by norm_num)
      (by norm_num : (0 : ℝ) < 1)] with N hN h1 h2 h3
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hD := two_pow_D1_le hN
  have hE := Real.exp_pos (-(1 / 10 * (N : ℝ)))
  have ha : 16 * N * (2 : ℝ) ^ D1 N * sigN N ≤ etaB N / 3 := by
    have e1 : Real.exp (-(x0 * N)) ≤ Real.exp (-(1027 / 10000 * N)) * Real.exp (-(1 / 10 * N)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
    calc 16 * N * (2 : ℝ) ^ D1 N * sigN N ≤ 16 * N * (2 ^ 16 * (N : ℝ) ^ 4) * sigN N := by
          have := sigN_pos N; gcongr
      _ = 2 ^ 20 * (N : ℝ) ^ 5 * Real.exp (-(x0 * N)) := by rw [sigN_eq_exp]; ring
      _ ≤ 2 ^ 20 * (N : ℝ) ^ 5 * (Real.exp (-(1027 / 10000 * N)) * Real.exp (-(1 / 10 * N))) := by
          gcongr
      _ = (3 * 2 ^ 20 * (N : ℝ) ^ 5 * Real.exp (-(1027 / 10000 * N))) *
            (Real.exp (-(1 / 10 * N)) / 3) := by ring
      _ ≤ 1 * (Real.exp (-(1 / 10 * N)) / 3) := by
          exact mul_le_mul_of_nonneg_right h1.le (by positivity)
      _ = etaB N / 3 := by rw [etaB_eq]; ring
  have hb : 16 * N * (2 : ℝ) ^ D1 N * tauN N ≤ etaB N / 3 := by
    calc 16 * N * (2 : ℝ) ^ D1 N * tauN N ≤ 16 * N * (2 ^ 16 * (N : ℝ) ^ 4) * tauN N := by
          have := tauN_pos N; gcongr
      _ = (3 * 2 ^ 20 * Real.exp (2 / 9) * (N : ℝ) ^ 5 * Real.exp (-((2 / 9 - 1 / 10) * N))) *
            (Real.exp (-(1 / 10 * N)) / 3) := by
          rw [tauN_eq, show -(2 / 9 * (N : ℝ)) = -((2 / 9 - 1 / 10) * N) + -(1 / 10 * N) by ring,
            Real.exp_add]
          ring
      _ ≤ 1 * (Real.exp (-(1 / 10 * N)) / 3) := mul_le_mul_of_nonneg_right h2.le (by positivity)
      _ = etaB N / 3 := by rw [etaB_eq]; ring
  have hc : (2 / 3 : ℝ) ^ N / tauN N ≤ etaB N / 3 := by
    rw [two_thirds_pow_eq, tauN_eq, div_le_iff₀ (by positivity)]
    have e1 : Real.exp (-(2 * x0 * N)) ≤
        Real.exp (-(8 / 100 * N)) * Real.exp (-(1 / 10 * N)) * Real.exp (-(2 / 9 * N)) := by
      rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
    have h3' : 3 * Real.exp (-(2 / 9)) * Real.exp (-(8 / 100 * N)) < 1 := by
      simpa using h3
    have e2 : Real.exp (-(2 / 9)) * Real.exp (2 / 9) = 1 := by
      rw [← Real.exp_add]; simp
    rw [etaB_eq]
    have hp1 := Real.exp_pos (-(2 / 9 * (N : ℝ)))
    have hp2 := Real.exp_pos (2 / 9 : ℝ)
    have hp3 := Real.exp_pos (-(8 / 100 * (N : ℝ)))
    have key : Real.exp (-(8 / 100 * N)) ≤ Real.exp (2 / 9) / 3 := by
      have := mul_lt_mul_of_pos_right h3' hp2
      rw [one_mul] at this
      nlinarith
    calc Real.exp (-(2 * x0 * N)) ≤
          Real.exp (-(8 / 100 * N)) * Real.exp (-(1 / 10 * N)) * Real.exp (-(2 / 9 * N)) := e1
      _ ≤ Real.exp (2 / 9) / 3 * Real.exp (-(1 / 10 * N)) * Real.exp (-(2 / 9 * N)) := by gcongr
      _ = Real.exp (-(1 / 10 * N)) / 3 * (Real.exp (2 / 9) * Real.exp (-(2 / 9 * N))) := by ring
  unfold EWnum
  have : 16 * N * (2 : ℝ) ^ D1 N * (sigN N + tauN N) =
      16 * N * (2 : ℝ) ^ D1 N * sigN N + 16 * N * (2 : ℝ) ^ D1 N * tauN N := by ring
  rw [this]
  linarith

/-- `3 D1 N ≤ N` eventually. -/
lemma ev_3D1 : ∀ᶠ N : ℕ in atTop, 3 * D1 N ≤ N := by
  filter_upwards [eventually_ge_atTop 1,
    ev_quad_half_comp tendsto_natLog2 0 12 48 (by norm_num : (0 : ℝ) < 1)] with N hN h
  set ℓ := Nat.log 2 N with hℓ
  have h2 : ((2 : ℝ) ^ ℓ) ≤ N := by exact_mod_cast two_pow_natLog_le hN
  have hp : (2 : ℝ) ^ ℓ * (1 / 2) ^ ℓ = 1 := by rw [← mul_pow]; norm_num
  have h' : (12 * (ℓ : ℝ) + 48) < 2 ^ ℓ := by
    have hpos : (0 : ℝ) < (1 / 2) ^ ℓ := by positivity
    have : (0 * (ℓ : ℝ) ^ 2 + 12 * ℓ + 48) * (1 / 2) ^ ℓ * 2 ^ ℓ < 1 * 2 ^ ℓ :=
      mul_lt_mul_of_pos_right h (by positivity)
    rw [mul_assoc, mul_comm ((1 / 2 : ℝ) ^ ℓ), hp] at this
    linarith
  have : ((3 * D1 N : ℕ) : ℝ) ≤ N := by
    unfold D1; push_cast; linarith
  exact_mod_cast this

lemma ev_big : ∀ᶠ N : ℕ in atTop, 10 ≤ K2N N := by
  filter_upwards [ev_3D1, eventually_ge_atTop 30] with N h1 h2
  rw [K2N_eq_sub_D1]; omega

/-- `N η' ≤ 1/10` eventually (`η' = etaB N + 2^{D1+1} τ`). -/
lemma ev_eta' : ∀ᶠ N : ℕ in atTop,
    (N : ℝ) * (etaB N + 2 ^ (D1 N + 1) * tauN N) ≤ 1 / 10 := by
  filter_upwards [eventually_ge_atTop 1,
    ev_poly_exp 1 20 (c := 1 / 10) (by norm_num) (by norm_num : (0 : ℝ) < 1),
    ev_poly_exp 5 (20 * 2 ^ 17 * Real.exp (2 / 9)) (c := 2 / 9) (by norm_num)
      (by norm_num : (0 : ℝ) < 1)] with N hN h1 h2
  have hD := two_pow_D1_le hN
  have a1 : (N : ℝ) * etaB N ≤ 1 / 20 := by
    rw [etaB_eq]; simp only [pow_one] at h1; linarith
  have a2 : (N : ℝ) * (2 ^ (D1 N + 1) * tauN N) ≤ 1 / 20 := by
    have hτ := tauN_pos N
    have h2D : (2 : ℝ) ^ (D1 N + 1) ≤ 2 * (2 ^ 16 * (N : ℝ) ^ 4) := by
      rw [pow_succ, mul_comm]; linarith
    calc (N : ℝ) * (2 ^ (D1 N + 1) * tauN N) ≤ N * (2 * (2 ^ 16 * (N : ℝ) ^ 4) * tauN N) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2D hτ.le) (by positivity)
      _ = (20 * 2 ^ 17 * Real.exp (2 / 9) * (N : ℝ) ^ 5 * Real.exp (-(2 / 9 * N))) / 20 := by
          rw [tauN_eq]; ring
      _ ≤ 1 / 20 := by linarith
  rw [mul_add]; linarith

/-- The ratio condition of (B5-d) holds eventually. -/
lemma ev_ratio : ∀ᶠ N : ℕ in atTop, (1 + etaB N + 2 / (N : ℝ) ^ 3) ^ N ≤
    2 * (1 - (etaB N + 2 ^ (D1 N + 1) * tauN N)) ^ N := by
  have hexp : Real.exp (1 / 5) ≤ 5 / 4 := by
    have h := exp_le_rat (q := 1 / 5) (r := 5 / 4) 10 1 (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)
    have e : (((1 / 5 : ℚ)) : ℝ) = 1 / 5 := by norm_num
    have e' : (((5 / 4 : ℚ)) : ℝ) = 5 / 4 := by norm_num
    rwa [e, e'] at h
  filter_upwards [eventually_ge_atTop 7, ev_eta'] with N hN h1
  have hN' : (7 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set η' := etaB N + 2 ^ (D1 N + 1) * tauN N with hη'
  have hη'0 : 0 ≤ η' := by have := tauN_pos N; have := Real.exp_pos (-(N : ℝ) / 10); positivity
  have hη0 : 0 ≤ etaB N := (Real.exp_pos _).le
  have hNη : (N : ℝ) * etaB N ≤ 1 / 10 := by
    have : (N : ℝ) * etaB N ≤ (N : ℝ) * η' := by
      have := tauN_pos N; gcongr; simp only [hη']; have : (0 : ℝ) ≤ 2 ^ (D1 N + 1) * tauN N := by
        positivity
      linarith
    linarith
  have hlow : 1 - N * η' ≤ (1 - η') ^ N := by
    have := one_add_mul_le_pow (a := -η') (by nlinarith) N
    rw [← sub_eq_add_neg] at this
    linarith
  have hup : (1 + etaB N + 2 / (N : ℝ) ^ 3) ^ N ≤ Real.exp (1 / 5) := by
    have ha0 : 0 ≤ etaB N + 2 / (N : ℝ) ^ 3 := by positivity
    calc (1 + etaB N + 2 / (N : ℝ) ^ 3) ^ N ≤ Real.exp (etaB N + 2 / (N : ℝ) ^ 3) ^ N := by
          apply pow_le_pow_left₀ (by positivity)
          linarith [Real.add_one_le_exp (etaB N + 2 / (N : ℝ) ^ 3)]
      _ = Real.exp (N * (etaB N + 2 / (N : ℝ) ^ 3)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (1 / 5) := by
          apply Real.exp_le_exp.2
          have : (N : ℝ) * (2 / (N : ℝ) ^ 3) = 2 / (N : ℝ) ^ 2 := by field_simp
          have h2 : 2 / (N : ℝ) ^ 2 ≤ 2 / 49 := by
            apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); nlinarith
          nlinarith
  linarith

/-- (EV3-type) `deltaH N (k-1) + 2^{2-k} ≤ 1/4` for `K2N N < k ≤ N`, eventually. -/
lemma ev_hoeff : ∀ᶠ N : ℕ in atTop, ∀ k, K2N N < k → k ≤ N →
    deltaH N (k - 1) + 2 / (2 : ℝ) ^ (k - 1) ≤ 1 / 4 := by
  filter_upwards [eventually_ge_atTop 1, ev_3D1,
    ev_poly_geom 5 (r := 1 / 2) (by norm_num) (by norm_num) (2 ^ 24) (by norm_num : (0 : ℝ) < 1)]
    with N hN h3 hg
  intro k hk hkN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hkk : N ≤ (k - 1) + D1 N := by rw [K2N_eq_sub_D1] at hk; omega
  have hD := two_pow_D1_le hN
  have hinv : 1 / (2 : ℝ) ^ (k - 1) ≤ 2 ^ 16 * (N : ℝ) ^ 4 * (1 / 2) ^ N := by
    have h1 : (2 : ℝ) ^ N ≤ 2 ^ (k - 1) * 2 ^ D1 N := by
      rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) hkk
    have hk1 : (0 : ℝ) < 2 ^ (k - 1) := by positivity
    have h2 : (0 : ℝ) < 2 ^ N := by positivity
    rw [one_div_pow, div_le_iff₀ hk1]
    rw [show 2 ^ 16 * (N : ℝ) ^ 4 * (1 / 2 ^ N) * 2 ^ (k - 1) =
      (2 ^ 16 * (N : ℝ) ^ 4 * 2 ^ (k - 1)) / 2 ^ N by ring, le_div_iff₀ h2, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hD hk1.le]
  have hy : (N : ℝ) / 2 ^ (k - 1) ≤ 1 / 256 := by
    rw [div_eq_mul_one_div]
    calc (N : ℝ) * (1 / 2 ^ (k - 1)) ≤ N * (2 ^ 16 * (N : ℝ) ^ 4 * (1 / 2) ^ N) := by gcongr
      _ = 2 ^ 24 * (N : ℝ) ^ 5 * (1 / 2) ^ N / 256 := by ring
      _ ≤ 1 / 256 := by linarith
  have hδ : deltaH N (k - 1) ≤ 1 / 8 := by
    unfold deltaH
    have : Real.sqrt ((N : ℝ) / 2 ^ (k - 1)) ≤ 1 / 16 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num; linarith
    linarith
  have h2k : 2 / (2 : ℝ) ^ (k - 1) ≤ 1 / 8 := by
    rw [show 2 / (2 : ℝ) ^ (k - 1) = 2 * (1 / 2 ^ (k - 1)) by ring]
    have hp : (0 : ℝ) ≤ (1 / 2) ^ N := by positivity
    have hc : (2 : ℝ) ^ 16 * (N : ℝ) ^ 4 ≤ 2 ^ 24 * (N : ℝ) ^ 5 / 16 := by
      have : (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 5 := pow_le_pow_right₀ hN' (by norm_num)
      have h4 : (0 : ℝ) ≤ (N : ℝ) ^ 4 := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_right hc hp
    have e : 2 ^ 24 * (N : ℝ) ^ 5 / 16 * (1 / 2) ^ N = 2 ^ 24 * (N : ℝ) ^ 5 * (1 / 2) ^ N / 16 := by
      ring
    linarith
  linarith

/-- (EV4) `8 k ρ0^k ≤ e^{-N/4}` for `K2N N < k ≤ N`, eventually. -/
lemma ev_rate : ∀ᶠ N : ℕ in atTop, ∀ k, K2N N < k → k ≤ N →
    8 * (k : ℝ) * rho0 ^ k ≤ Real.exp (-(N : ℝ) / 4) := by
  have h0 := rho0_pos
  have hq := rho0_mul_exp_lt_one
  have hc : 1 ≤ 1 / rho0 := by rw [le_div_iff₀ h0, one_mul]; exact rho0_lt_one.le
  have hlim := tendsto_D1_geom (C := 8) hc (by positivity) hq (by norm_num)
  filter_upwards [eventually_ge_atTop 1, (tendsto_order.1 hlim).2 1 one_pos] with N hN hlt
  intro k hk hkN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hpk := pow_le_of_big h0 rho0_lt_one.le hk hkN
  have hD1 : 1 ≤ D1 N := by unfold D1; omega
  have hND : (N : ℝ) * (1 / rho0) ^ D1 N ≤ ((1 / rho0) * N) ^ D1 N := by
    rw [mul_pow, mul_comm]
    gcongr
    calc (N : ℝ) = N ^ 1 := (pow_one _).symm
      _ ≤ N ^ D1 N := pow_le_pow_right₀ hN' hD1
  have hexpN : (rho0 * Real.exp (1 / 4)) ^ N * Real.exp (-(N : ℝ) / 4) = rho0 ^ N := by
    rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    have : (N : ℝ) * (1 / 4) + -(N : ℝ) / 4 = 0 := by ring
    rw [this, Real.exp_zero, mul_one]
  calc 8 * (k : ℝ) * rho0 ^ k ≤ 8 * N * ((1 / rho0) ^ D1 N * rho0 ^ N) := by
        have := rho0_pos; gcongr
    _ = 8 * ((N : ℝ) * (1 / rho0) ^ D1 N) * rho0 ^ N := by ring
    _ ≤ 8 * ((1 / rho0) * N) ^ D1 N * rho0 ^ N := by
        have := rho0_pos; gcongr
    _ = (8 * ((1 / rho0) * N) ^ D1 N * (rho0 * Real.exp (1 / 4)) ^ N) *
          Real.exp (-(N : ℝ) / 4) := by rw [mul_assoc _ _ (Real.exp _), hexpN]
    _ ≤ 1 * Real.exp (-(N : ℝ) / 4) := mul_le_mul_of_nonneg_right hlt.le (Real.exp_pos _).le
    _ = _ := one_mul _

/-- (EV1) `N dlev N k ≤ 10^{-4}` for `1 ≤ k ≤ K2N N`, eventually (the local bound of
`eventually_levels`, at a general level). -/
lemma ev_N_dlev : ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ K2N N →
    (N : ℝ) * dlev N k ≤ 1 / 10000 := by
  filter_upwards [eventually_ge_atTop 1,
    ev_quad_half_comp tendsto_natLog2 0 1 6 (by norm_num : (0 : ℝ) < 1e-6),
    ev_pow_mul_sigN 5 (C := 5376) (by norm_num) (by norm_num : (0 : ℝ) < 5e-9)]
    with N hN hℓ h5
  intro k hk1 hkK
  set ℓ := Nat.log 2 N with hℓdef
  have hℓ' : ((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ ℓ < 1e-6 := by
    have : ((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ ℓ = (0 * (ℓ : ℝ) ^ 2 + 1 * ℓ + 6) * (1 / 2 : ℝ) ^ ℓ := by
      ring
    rw [this]; exact hℓ
  have hkN : k + (4 * ℓ + 16) ≤ N := by unfold K2N at hkK; omega
  have hkN' : k ≤ N := by omega
  have hσ := sigN_pos N
  have e : (N : ℝ) * dlev N k = (2 * N) * Real.sqrt (LkN N k * (3 * Mk N k)) := by
    rw [dlev]; ring
  rw [e]
  apply mul_sqrt_le_of_sq (by positivity) (by norm_num)
  have hL := LkN_le_levels hN hkN'
  have hL0 := LkN_nonneg' k hN
  have hM := Mk_le hN hkN
  set Mb : ℝ := (1 / 2 : ℝ) ^ (4 * ℓ + 15) + 64 * N * sigN N with hMb
  have hMb0 : 0 ≤ Mb := by positivity
  have s1 : (2 * (N : ℝ)) ^ 2 * (LkN N k * (3 * Mk N k)) ≤
      (2 * (N : ℝ)) ^ 2 * ((N * ((ℓ : ℝ) + 6)) * (3 * Mb)) := by
    have : LkN N k * (3 * Mk N k) ≤ (N * ((ℓ : ℝ) + 6)) * (3 * Mb) := by
      calc LkN N k * (3 * Mk N k) ≤ LkN N k * (3 * Mb) := by gcongr
        _ ≤ _ := by gcongr
    exact mul_le_mul_of_nonneg_left this (by positivity)
  set u : ℝ := (N : ℝ) * (1 / 2 : ℝ) ^ ℓ with hu
  have hu0 : 0 ≤ u := by positivity
  have hu2 : u ≤ 2 := by
    have hlt : (N : ℝ) < 2 * 2 ^ ℓ := by exact_mod_cast lt_two_mul_two_pow_natLog N
    have hh : (2 : ℝ) ^ ℓ * (1 / 2 : ℝ) ^ ℓ = 1 := by rw [← mul_pow]; norm_num
    have : 0 < (1 / 2 : ℝ) ^ ℓ := by positivity
    rw [hu]; nlinarith
  have hu3 : u ^ 3 ≤ 8 := by
    have := pow_le_pow_left₀ hu0 hu2 3; norm_num at this; linarith
  have hpow : (1 / 2 : ℝ) ^ (4 * ℓ + 15) =
      ((1 / 2 : ℝ) ^ ℓ) ^ 3 * (1 / 2 : ℝ) ^ ℓ * (1 / 2) ^ 15 := by
    rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
  have p1 : 12 * (N : ℝ) ^ 3 * ((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ (4 * ℓ + 15) ≤ 3e-9 := by
    have e1 : 12 * (N : ℝ) ^ 3 * ((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ (4 * ℓ + 15) =
        12 * u ^ 3 * (1 / 2) ^ 15 * (((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ ℓ) := by
      rw [hpow, hu]; ring
    rw [e1]
    have : 0 ≤ ((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ ℓ := by positivity
    have : 12 * u ^ 3 * (1 / 2 : ℝ) ^ 15 ≤ 12 * 8 * (1 / 2) ^ 15 := by gcongr
    nlinarith
  have p2 : 768 * (N : ℝ) ^ 4 * ((ℓ : ℝ) + 6) * sigN N ≤ 5e-9 := by
    have hℓN : ((ℓ : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast natLog_succ_le_self hN
    have : 768 * (N : ℝ) ^ 4 * ((ℓ : ℝ) + 6) * sigN N ≤ 768 * (N : ℝ) ^ 4 * (7 * N) * sigN N := by
      gcongr; linarith
    have e : 768 * (N : ℝ) ^ 4 * (7 * N) * sigN N = 5376 * (N : ℝ) ^ 5 * sigN N := by ring
    linarith
  have e2 : (2 * (N : ℝ)) ^ 2 * ((N * ((ℓ : ℝ) + 6)) * (3 * Mb)) =
      12 * (N : ℝ) ^ 3 * ((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ (4 * ℓ + 15)
        + 768 * (N : ℝ) ^ 4 * ((ℓ : ℝ) + 6) * sigN N := by
    rw [hMb]; ring
  rw [e2] at s1
  nlinarith

/-- (EV1) `N (2τ + 2 Mk N k) ≤ 10^{-4}` for `1 ≤ k ≤ K2N N`, eventually. -/
lemma ev_N_tau_Mk : ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ K2N N →
    (N : ℝ) * (2 * tauN N + 2 * Mk N k) ≤ 1 / 10000 := by
  filter_upwards [eventually_ge_atTop 1,
    ev_quad_half_comp tendsto_natLog2 0 0 1 (by norm_num : (0 : ℝ) < 2 / 5),
    ev_pow_mul_sigN 2 (C := 132) (by norm_num) (by norm_num : (0 : ℝ) < 5e-5)]
    with N hN hℓ h2
  intro k hk1 hkK
  set ℓ := Nat.log 2 N with hℓdef
  have hℓ' : (1 / 2 : ℝ) ^ ℓ < 2 / 5 := by
    have : (1 / 2 : ℝ) ^ ℓ = (0 * (ℓ : ℝ) ^ 2 + 0 * ℓ + 1) * (1 / 2 : ℝ) ^ ℓ := by ring
    rw [this]; exact hℓ
  have hkN : k + (4 * ℓ + 16) ≤ N := by unfold K2N at hkK; omega
  have hσ := sigN_pos N
  have hM := Mk_le hN hkN
  rw [← hℓdef] at hM
  have hτ := tauN_le_two_sigN N
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set u : ℝ := (N : ℝ) * (1 / 2 : ℝ) ^ ℓ with hu
  have hu2 : u ≤ 2 := by
    have hlt : (N : ℝ) < 2 * 2 ^ ℓ := by exact_mod_cast lt_two_mul_two_pow_natLog N
    have hh : (2 : ℝ) ^ ℓ * (1 / 2 : ℝ) ^ ℓ = 1 := by rw [← mul_pow]; norm_num
    have : 0 < (1 / 2 : ℝ) ^ ℓ := by positivity
    rw [hu]; nlinarith
  have hp : (N : ℝ) * (1 / 2 : ℝ) ^ (4 * ℓ + 15) ≤ 2 * (2 / 5) * (1 / 2) ^ 15 := by
    have e : (N : ℝ) * (1 / 2 : ℝ) ^ (4 * ℓ + 15) =
        u * ((1 / 2 : ℝ) ^ (3 * ℓ) * (1 / 2) ^ 15) := by
      rw [hu, show 4 * ℓ + 15 = ℓ + 3 * ℓ + 15 by ring, pow_add, pow_add]; ring
    rw [e]
    have h3 : (1 / 2 : ℝ) ^ (3 * ℓ) ≤ (1 / 2 : ℝ) ^ ℓ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h0 : 0 ≤ (1 / 2 : ℝ) ^ (3 * ℓ) := by positivity
    have hu0 : 0 ≤ u := by positivity
    have : (1 / 2 : ℝ) ^ (3 * ℓ) * (1 / 2) ^ 15 ≤ 2 / 5 * (1 / 2) ^ 15 := by
      have : (0 : ℝ) ≤ (1 / 2) ^ 15 := by positivity
      nlinarith
    calc u * ((1 / 2 : ℝ) ^ (3 * ℓ) * (1 / 2) ^ 15) ≤ 2 * (2 / 5 * (1 / 2) ^ 15) :=
          mul_le_mul hu2 this (by positivity) (by norm_num)
      _ = _ := by ring
  have hNM : (N : ℝ) * Mk N k ≤ 2 * (2 / 5) * (1 / 2) ^ 15 + 64 * (N : ℝ) ^ 2 * sigN N := by
    have := mul_le_mul_of_nonneg_left hM (by positivity : (0 : ℝ) ≤ N)
    nlinarith
  have hNτ : (N : ℝ) * tauN N ≤ 2 * (N : ℝ) ^ 2 * sigN N := by
    have := mul_le_mul_of_nonneg_left hτ (by positivity : (0 : ℝ) ≤ N)
    have : (N : ℝ) * sigN N ≤ (N : ℝ) ^ 2 * sigN N := by
      have : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this hσ.le
    nlinarith
  have e : (N : ℝ) * (2 * tauN N + 2 * Mk N k) =
      2 * ((N : ℝ) * tauN N) + 2 * ((N : ℝ) * Mk N k) := by ring
  rw [e]
  have : 132 * (N : ℝ) ^ 2 * sigN N ≤ 5e-5 := h2
  norm_num at this ⊢
  nlinarith

/-- (EV5) `k 2^{-k} fl_k ≤ 458 N^2 σ_N` for `1 ≤ k ≤ N`, when `4 N^5 vkRate^N ≤ 1`. -/
lemma flK_bound (hN : 1 ≤ N) (hv : 4 * (N : ℝ) ^ 5 * vkRate ^ N ≤ 1) {k : ℕ} (hk1 : 1 ≤ k)
    (hkN : k ≤ N) : (k : ℝ) / 2 ^ k * flK N k ≤ 458 * (N : ℝ) ^ 2 * sigN N := by
  set x : ℝ := (k : ℝ) / 2 ^ k with hx
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one hp]; exact_mod_cast (Nat.lt_two_pow_self).le
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hkN' : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hσ := sigN_pos N
  have hτ0 := tauN_pos N
  have hτ2 := tauN_le_two_sigN N
  have hL := LkN_le_six_sq hN hkN
  have hL0 := LkN_nonneg' k hN
  have hV := Vbd_le N k
  have hV0 := Vbd_nonneg N k
  have hvk0 : 0 ≤ vkRate ^ N := (pow_pos vkRate_pos N).le
  have hNσ : sigN N ≤ (N : ℝ) ^ 2 * sigN N := by
    have : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hN1σ : (N : ℝ) * sigN N ≤ (N : ℝ) ^ 2 * sigN N := by
    have : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hσ.le
  -- piece A
  have hA : x * (4 * Real.sqrt (LkN N k * Vbd N k)) ≤ 26 * N * sigN N := by
    rw [← mul_assoc, mul_comm x 4]
    apply mul_sqrt_le_of_sq (by positivity) (by positivity)
    have hx2 : x ^ 2 * 4 ^ k = (k : ℝ) ^ 2 := by
      rw [hx, div_pow, show (4 : ℝ) ^ k = (2 ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      field_simp
    have hxx : x ^ 2 ≤ 1 := by nlinarith
    have hk2 : (k : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by gcongr
    have hLV : LkN N k * Vbd N k ≤ 6 * (N : ℝ) ^ 2 *
        ((6 + 4 * (N : ℝ) ^ 3 * vkRate ^ N * 4 ^ k) * sigN N ^ 2) :=
      mul_le_mul hL hV hV0 (by positivity)
    have e : (4 * x) ^ 2 * (6 * (N : ℝ) ^ 2 * ((6 + 4 * (N : ℝ) ^ 3 * vkRate ^ N * 4 ^ k)
        * sigN N ^ 2)) = 96 * (N : ℝ) ^ 2 * sigN N ^ 2 *
          (6 * x ^ 2 + 4 * (N : ℝ) ^ 3 * vkRate ^ N * (x ^ 2 * 4 ^ k)) := by ring
    have h1 : (4 * x) ^ 2 * (LkN N k * Vbd N k) ≤ 96 * (N : ℝ) ^ 2 * sigN N ^ 2 *
        (6 * x ^ 2 + 4 * (N : ℝ) ^ 3 * vkRate ^ N * (x ^ 2 * 4 ^ k)) := by
      rw [← e]; exact mul_le_mul_of_nonneg_left hLV (by positivity)
    rw [hx2] at h1
    have h2 : 6 * x ^ 2 + 4 * (N : ℝ) ^ 3 * vkRate ^ N * (k : ℝ) ^ 2 ≤ 7 := by
      have : 4 * (N : ℝ) ^ 3 * vkRate ^ N * (k : ℝ) ^ 2 ≤ 4 * (N : ℝ) ^ 3 * vkRate ^ N * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hk2 (by positivity)
      have e' : 4 * (N : ℝ) ^ 3 * vkRate ^ N * (N : ℝ) ^ 2 = 4 * (N : ℝ) ^ 5 * vkRate ^ N := by ring
      linarith
    have h3 : 96 * (N : ℝ) ^ 2 * sigN N ^ 2 *
        (6 * x ^ 2 + 4 * (N : ℝ) ^ 3 * vkRate ^ N * (k : ℝ) ^ 2) ≤ 96 * (N : ℝ) ^ 2 * sigN N ^ 2 * 7 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : 96 * (N : ℝ) ^ 2 * sigN N ^ 2 * 7 ≤ (26 * N * sigN N) ^ 2 := by
      have : 0 ≤ (N : ℝ) ^ 2 * sigN N ^ 2 := by positivity
      nlinarith
    linarith
  -- piece B
  have hB : x * ((4 / 3) * LkN N k * (Real.sqrt 3 * sigN N + tauN N)) ≤ 32 * (N : ℝ) ^ 2 * sigN N := by
    have hs3 := sqrt_three_le_two
    have h1 : Real.sqrt 3 * sigN N + tauN N ≤ 4 * sigN N := by nlinarith
    have h0 : 0 ≤ (4 / 3) * LkN N k * (Real.sqrt 3 * sigN N + tauN N) := by positivity
    calc x * ((4 / 3) * LkN N k * (Real.sqrt 3 * sigN N + tauN N))
        ≤ 1 * ((4 / 3) * LkN N k * (Real.sqrt 3 * sigN N + tauN N)) :=
          mul_le_mul_of_nonneg_right hx1 h0
      _ ≤ 1 * ((4 / 3) * (6 * (N : ℝ) ^ 2) * (4 * sigN N)) := by gcongr
      _ = 32 * (N : ℝ) ^ 2 * sigN N := by ring
  -- piece C
  have hC : x * (2 * tauN N) ≤ 4 * (N : ℝ) ^ 2 * sigN N := by
    have : x * (2 * tauN N) ≤ 1 * (2 * (2 * sigN N)) := by
      apply mul_le_mul hx1 (by linarith) (by positivity) (by norm_num)
    nlinarith
  -- piece D
  have hMk : x * Mk N k ≤ 66 * N * sigN N := by
    have hs := sqrt_two_pow_third_le hN (a := k) hkN
    have hh := half_pow_le_sigN N
    have e1 : x * ((2 : ℝ) ^ k * (1 / 2) ^ (N - 1)) = 2 * k * (1 / 2) ^ N := by
      have : (1 / 2 : ℝ) ^ (N - 1) = 2 * (1 / 2) ^ N := by
        obtain ⟨j, rfl⟩ : ∃ j, N = j + 1 := ⟨N - 1, by omega⟩
        rw [Nat.add_sub_cancel, pow_succ]; ring
      rw [this, hx]; field_simp
    have hmk : Mk N k ≤ (2 : ℝ) ^ k * (1 / 2) ^ (N - 1) + 16 * N * (2 * sigN N + 2 * sigN N) := by
      unfold Mk; gcongr
    calc x * Mk N k ≤ x * ((2 : ℝ) ^ k * (1 / 2) ^ (N - 1) + 16 * N * (2 * sigN N + 2 * sigN N)) :=
          mul_le_mul_of_nonneg_left hmk hx0
      _ = 2 * k * (1 / 2) ^ N + x * (64 * N * sigN N) := by rw [mul_add, e1]; ring
      _ ≤ 2 * N * sigN N + 1 * (64 * N * sigN N) := by
          gcongr
      _ = 66 * N * sigN N := by ring
  have hD : x * (2 * (1 + 4 / (2 : ℝ) ^ k) * Mk N k) ≤ 396 * (N : ℝ) ^ 2 * sigN N := by
    have h4 : 4 / (2 : ℝ) ^ k ≤ 2 := by
      rw [div_le_iff₀ hp]
      have : (2 : ℝ) ≤ 2 ^ k := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk1
      linarith
    have hMk0 := Mk_nonneg N k
    have e : x * (2 * (1 + 4 / (2 : ℝ) ^ k) * Mk N k) = 2 * (1 + 4 / (2 : ℝ) ^ k) * (x * Mk N k) := by
      ring
    rw [e]
    have hxM0 : 0 ≤ x * Mk N k := mul_nonneg hx0 hMk0
    calc 2 * (1 + 4 / (2 : ℝ) ^ k) * (x * Mk N k) ≤ 2 * 3 * (66 * N * sigN N) := by
          apply mul_le_mul (by linarith) hMk hxM0 (by norm_num)
      _ = 396 * (N * sigN N) := by ring
      _ ≤ 396 * ((N : ℝ) ^ 2 * sigN N) := by gcongr
      _ = _ := by ring
  have e : x * flK N k = x * (4 * Real.sqrt (LkN N k * Vbd N k))
      + x * ((4 / 3) * LkN N k * (Real.sqrt 3 * sigN N + tauN N)) + x * (2 * tauN N)
      + x * (2 * (1 + 4 / (2 : ℝ) ^ k) * Mk N k) := by
    unfold flK Dev; ring
  rw [e]
  have : 26 * (N : ℝ) * sigN N ≤ 26 * ((N : ℝ) ^ 2 * sigN N) := by linarith [hN1σ]
  nlinarith

/-- The eventual inequalities used by B5, KT-LB and W4 at a fixed `N`. -/
structure W4Num (N : ℕ) : Prop where
  one_le : 1 ≤ N
  big : 10 ≤ K2N N
  d1 : 3 * D1 N ≤ N
  ew : EWnum N
  eta' : etaB N + 2 ^ (D1 N + 1) * tauN N ≤ 1 / 2
  ratio : (1 + etaB N + 2 / (N : ℝ) ^ 3) ^ N ≤ 2 * (1 - (etaB N + 2 ^ (D1 N + 1) * tauN N)) ^ N
  hoeff : ∀ k, K2N N < k → k ≤ N → deltaH N (k - 1) + 2 / (2 : ℝ) ^ (k - 1) ≤ 1 / 4
  rate : ∀ k, K2N N < k → k ≤ N → 8 * (k : ℝ) * rho0 ^ k ≤ Real.exp (-(N : ℝ) / 4)
  sig8 : 8 * N * sigN N ≤ 1 / 10000
  sig64 : 64 * (N : ℝ) ^ 2 * sigN N ≤ 1 / 10000
  dl : ∀ k, 1 ≤ k → k ≤ K2N N → (N : ℝ) * dlev N k ≤ 1 / 10000
  tm : ∀ k, 1 ≤ k → k ≤ K2N N → (N : ℝ) * (2 * tauN N + 2 * Mk N k) ≤ 1 / 10000
  fl : ∀ k, 1 ≤ k → k ≤ N → (k : ℝ) / 2 ^ k * flK N k ≤ 1 / 10000 * ((N : ℝ) ^ 9 * sigN N)
  srow : (2 : ℝ) ^ (-(N : ℝ) / 3) ≤ 1 / 10000 * ((N : ℝ) ^ 9 * sigN N)
  hsum : Real.exp (-(N : ℝ) / 16) + (2 : ℝ) ^ (-(N : ℝ) / 3) ≤ 1 / (N : ℝ) ^ 3
  n2 : 1 / (N : ℝ) ^ 2 ≤ 1 / 10000
  lb : Real.exp (-(N : ℝ) / 4) ≤ 4 / 25 * ((N : ℝ) ^ 9 * sigN N)

/-- **All the eventual inequalities hold for large `N`.** -/
theorem ev_W4Num : ∀ᶠ N : ℕ in atTop, W4Num N := by
  have hx0 := x0_gt
  have hx0' := x0_lt
  have hl2 := Real.log_two_gt_d9
  filter_upwards [eventually_ge_atTop 100, ev_big, ev_3D1, ev_EWnum, ev_eta', ev_ratio, ev_hoeff,
    ev_rate, ev_pow_mul_sigN 1 (C := 8) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10000),
    ev_pow_mul_sigN 2 (C := 64) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10000),
    ev_N_dlev, ev_N_tau_Mk,
    ev_poly_geom 5 (r := vkRate) vkRate_pos.le vkRate_lt_one 4 (by norm_num : (0 : ℝ) < 1),
    ev_poly_exp 0 10000 (c := 28 / 1000) (by norm_num) (by norm_num : (0 : ℝ) < 1),
    ev_poly_exp 3 2 (c := 1 / 16) (by norm_num) (by norm_num : (0 : ℝ) < 1),
    ev_poly_exp 3 2 (c := 23 / 100) (by norm_num) (by norm_num : (0 : ℝ) < 1),
    ev_poly_exp 0 (25 / 4) (c := 47 / 1000) (by norm_num) (by norm_num : (0 : ℝ) < 1)]
    with N h100 hbig h3D hEW hη' hratio hhoeff hrate h8 h64 hdl htm hvk hsr h16 h3 hlb
  have hN : 1 ≤ N := by omega
  have hN' : (100 : ℝ) ≤ N := by exact_mod_cast h100
  have hNpos : (0 : ℝ) < N := by linarith
  have hσ := sigN_pos N
  have hN9 : (1 : ℝ) ≤ (N : ℝ) ^ 9 := one_le_pow₀ (by linarith)
  have hsig : sigN N = Real.exp (-(x0 * N)) := sigN_eq_exp N
  have h2r := two_rpow_eq N
  refine ⟨hN, hbig, h3D, hEW, ?_, hratio, hhoeff, hrate, ?_, ?_, hdl, htm, ?_, ?_, ?_, ?_, ?_⟩
  · have : etaB N + 2 ^ (D1 N + 1) * tauN N ≤ (N : ℝ) * (etaB N + 2 ^ (D1 N + 1) * tauN N) := by
      have : 0 ≤ etaB N + 2 ^ (D1 N + 1) * tauN N := by
        have := tauN_pos N; have := Real.exp_pos (-(N : ℝ) / 10); unfold etaB; positivity
      nlinarith
    linarith
  · simpa using h8
  · exact h64
  · intro k hk1 hkN
    refine (flK_bound hN hvk.le hk1 hkN).trans ?_
    have h7 : (4580000 : ℝ) ≤ (N : ℝ) ^ 7 := by
      calc (4580000 : ℝ) ≤ 100 ^ 7 := by norm_num
        _ ≤ (N : ℝ) ^ 7 := by gcongr
    have e : 1 / 10000 * ((N : ℝ) ^ 9 * sigN N) = (N : ℝ) ^ 7 / 10000 * ((N : ℝ) ^ 2 * sigN N) := by
      ring
    rw [e]
    have : 0 ≤ (N : ℝ) ^ 2 * sigN N := by positivity
    nlinarith
  · -- `2^{-N/3} ≤ 10^{-4} N^9 σ`
    rw [h2r, hsig]
    have hsr' : 10000 * Real.exp (-(28 / 1000 * N)) < 1 := by simpa using hsr
    have e1 : Real.exp (-(Real.log 2 / 3 * N)) ≤
        Real.exp (-(28 / 1000 * N)) * Real.exp (-(x0 * N)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
    have hE := Real.exp_pos (-(x0 * (N : ℝ)))
    calc Real.exp (-(Real.log 2 / 3 * N)) ≤ Real.exp (-(28 / 1000 * N)) * Real.exp (-(x0 * N)) := e1
      _ ≤ 1 / 10000 * Real.exp (-(x0 * N)) := by
          apply mul_le_mul_of_nonneg_right _ hE.le; linarith
      _ ≤ 1 / 10000 * ((N : ℝ) ^ 9 * Real.exp (-(x0 * N))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num); nlinarith
  · -- `e^{-N/16} + 2^{-N/3} ≤ N^{-3}`
    rw [h2r]
    have e1 : Real.exp (-(Real.log 2 / 3 * N)) ≤ Real.exp (-(23 / 100 * N)) := by
      apply Real.exp_le_exp.2; nlinarith
    have e2 : Real.exp (-(N : ℝ) / 16) = Real.exp (-(1 / 16 * N)) := by congr 1; ring
    rw [e2, le_div_iff₀ (by positivity)]
    have hN3 : (0 : ℝ) < (N : ℝ) ^ 3 := by positivity
    have := mul_le_mul_of_nonneg_right e1 hN3.le
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  · -- `e^{-N/4} ≤ (4/25) N^9 σ`
    rw [hsig]
    have hlb' : 25 / 4 * Real.exp (-(47 / 1000 * N)) < 1 := by simpa using hlb
    have e1 : Real.exp (-(N : ℝ) / 4) ≤ Real.exp (-(47 / 1000 * N)) * Real.exp (-(x0 * N)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
    have hE := Real.exp_pos (-(x0 * (N : ℝ)))
    calc Real.exp (-(N : ℝ) / 4) ≤ Real.exp (-(47 / 1000 * N)) * Real.exp (-(x0 * N)) := e1
      _ ≤ 4 / 25 * Real.exp (-(x0 * N)) := by
          apply mul_le_mul_of_nonneg_right _ hE.le; linarith
      _ ≤ 4 / 25 * ((N : ℝ) ^ 9 * Real.exp (-(x0 * N))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num); nlinarith

end Eventual

/-! ## 6. Theorem W4 -/

section W4

/-- The failure probability of `GoodW` (the ten parts of `cubeM_notGood_le`). -/
def fGood (N : ℕ) : ℝ :=
  fg2 N + fg3 N + fg4 N + fg6 N + fg11 N + fg12 N + fg13a N + fg13b N + fg16 N + (71 / 72 : ℝ) ^ N

lemma fg_nonneg (N : ℕ) : 0 ≤ fg2 N ∧ 0 ≤ fg3 N ∧ 0 ≤ fg4 N ∧ 0 ≤ fg6 N ∧ 0 ≤ fg11 N ∧
    0 ≤ fg12 N ∧ 0 ≤ fg13a N ∧ 0 ≤ fg13b N ∧ 0 ≤ fg16 N := by
  have h2 : 0 ≤ fg2 N := by unfold fg2; positivity
  have h4 : 0 ≤ fg4 N := by unfold fg4; positivity
  refine ⟨h2, by unfold fg3; positivity, h4, by unfold fg6; positivity,
    by unfold fg11; positivity, by unfold fg12; positivity, by unfold fg13a; positivity,
    by unfold fg13b; positivity, by unfold fg16; positivity⟩

/-- `cubeM {¬ GoodW} ≤ fGood N`, uniformly in the current state. -/
theorem cubeM_notGood_le_fGood (s : State N) :
    cubeM N {w | ¬ GoodW N s w} ≤ ENNReal.ofReal (fGood N) := by
  obtain ⟨h2, h3, h4, h6, h11, h12, h13a, h13b, h16⟩ := fg_nonneg N
  have hU : (0 : ℝ) ≤ (71 / 72 : ℝ) ^ N := by positivity
  refine (cubeM_notGood_le s).trans ?_
  refine (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add (cubeM_not_g2 (N := N)) cubeM_not_g3) cubeM_not_g4) cubeM_not_g6)
    cubeM_not_g11) cubeM_not_g12) cubeM_not_g13a) cubeM_not_g13b) (cubeM_not_g16 s))
    (cubeM_not_gU s)).trans (le_of_eq ?_)
  unfold fGood
  rw [ENNReal.ofReal_add (by positivity) hU, ENNReal.ofReal_add (by positivity) h16,
    ENNReal.ofReal_add (by positivity) h13b, ENNReal.ofReal_add (by positivity) h13a,
    ENNReal.ofReal_add (by positivity) h12, ENNReal.ofReal_add (by positivity) h11,
    ENNReal.ofReal_add (by positivity) h6, ENNReal.ofReal_add (by positivity) h4,
    ENNReal.ofReal_add h2 h3]

theorem tendsto_fGood : Tendsto fGood atTop (𝓝 0) := by
  have := (((((((((tendsto_fg2.add tendsto_fg3).add tendsto_fg4).add tendsto_fg6).add
    tendsto_fg11).add tendsto_fg12).add tendsto_fg13a).add tendsto_fg13b).add tendsto_fg16).add
    tendsto_fgU)
  simp only [add_zero] at this
  exact this.congr fun N => by unfold fGood; ring

lemma flipC_mem_Ioo {b : Bool} {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    flipC b x ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hx
  cases b
  · simp only [flipC, Bool.false_eq_true, ↓reduceIte, Set.mem_Ioo]; constructor <;> linarith
  · simpa [flipC] using And.intro h0 h1

lemma flipP_mem_openCube {s : State N} {w : Param N} (hw : w ∈ openCube N) :
    flipP s w ∈ openCube N := fun r i => flipC_mem_Ioo (hw r i)

lemma cubeM_compl_openCube : cubeM N (openCube N)ᶜ = 0 := by
  rw [← restrict_cube, Measure.restrict_apply b1_measurableSet_openCube.compl, Set.inter_comm,
    ← Set.sdiff_eq]
  exact volume_cube_diff_openCube N

/-- **Theorem W4, deterministic core.** At an `N` where the eventual inequalities hold: if the rows
`tc, s` of `w` have entries in `(0,1)`, `Pw tc ≥ N^9 σ_N`, `Pw tc ≤ e^{-N/16}`, `Pw s ≤ 2^{-N/3}`,
`N ≤ 3 ham(tc, s)`, and `w` agrees off `{tc, s}` with some `w̃ ∈ GoodW ∩ E5 ∩ openCube`, then every
candidate with `5 ≤ |S| < N` has `φ_s(S) ≤ (12/25) β`, `β = Pw tc / Zs w`. -/
theorem thmW4_det (hnum : W4Num N) {s tc : State N} (hham : N ≤ 3 * ham tc s)
    {w w' : Param N} (hA : AgreeOff {tc, s} w w') (hG : GoodW N s w') (hE : w' ∈ E5 N s tc)
    (hw' : w' ∈ openCube N)
    (hrow : ∀ i, w tc i ∈ Set.Ioo (0 : ℝ) 1 ∧ w s i ∈ Set.Ioo (0 : ℝ) 1)
    (hP1 : (N : ℝ) ^ 9 * sigN N ≤ Pw w tc) (hP2 : Pw w tc ≤ Real.exp (-(N : ℝ) / 16))
    (hPs : Pw w s ≤ (2 : ℝ) ^ (-(N : ℝ) / 3))
    {S : Finset (Fin N)} (hk5 : 5 ≤ S.card) (hkN : S.card < N) :
    phi (flipP s w) s S ≤ 12 / 25 * (Pw w tc / Zs w) := by
  have hN := hnum.one_le
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hwo : w ∈ openCube N := by
    intro r i
    by_cases hr : r ∈ ({tc, s} : Finset (State N))
    · simp only [mem_insert, mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact (hrow i).1
      · exact (hrow i).2
    · rw [hA r hr]; exact hw' r i
  obtain ⟨z, hz, rfl⟩ : ∃ z, z ∈ openCube N ∧ flipP s z = w :=
    ⟨flipP s w, flipP_mem_openCube hwo, flipP_invol s w⟩
  rw [flipP_invol s z]
  have hH : Pw (flipP s z) tc + Pw (flipP s z) s ≤ 1 / (N : ℝ) ^ 3 := by
    have := hnum.hsum; linarith
  by_cases hkK : S.card ≤ K2N N
  · have hNH : (N : ℝ) * (Pw (flipP s z) tc + Pw (flipP s z) s) ≤ 1 / 10000 := by
      have h1 : (N : ℝ) * (Pw (flipP s z) tc + Pw (flipP s z) s) ≤ N * (1 / (N : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hH (by positivity)
      have e : (N : ℝ) * (1 / (N : ℝ) ^ 3) = 1 / (N : ℝ) ^ 2 := by field_simp
      linarith [hnum.n2]
    have hPs' : Pw (flipP s z) s ≤ 1 / 10000 * Pw (flipP s z) tc := by
      have := hnum.srow; linarith
    exact corKTLB hN hz hA hG hk5 hnum.sig8 (hnum.dl _ (by omega) hkK)
      (hnum.tm _ (by omega) hkK) hnum.sig64 (hnum.fl _ (by omega) hkN.le) hNH hP1 hPs'
  · push Not at hkK
    have hB5 := thmB5_det hN hnum.big hnum.d1 hnum.eta' hnum.ratio hnum.hoeff hnum.rate hham hz
      hA hE hH hkK hkN
    refine hB5.trans (hnum.lb.trans ?_)
    have hH1 : Pw (flipP s z) tc + Pw (flipP s z) s ≤ 1 := by
      have : 1 / (N : ℝ) ^ 3 ≤ 1 := by
        rw [div_le_one (by positivity)]; exact one_le_pow₀ hN'
      linarith
    have hZw : Zs (flipP s z) ≤ 3 := by
      have h1 := (tr1 hA hG.g2).2
      have h2 := hG.g3.2.1
      linarith
    have hZpos : 0 < Zs (flipP s z) := Zs_pos hz s
    rw [mul_div_assoc', le_div_iff₀ hZpos]
    have h0 : 0 ≤ (N : ℝ) ^ 9 * sigN N := by have := sigN_pos N; positivity
    nlinarith

/-- **Theorem W4.** Eventually in `N`: for all `s, tc` with `N ≤ 3 ham(tc, s)` and all values `f` of
the rows `tc, s` with entries in `(0,1)`, `Pw tc ≥ N^9 σ_N`, `Pw tc ≤ e^{-N/16}`, `Pw s ≤ 2^{-N/3}`,
the probability over the other rows that some `S` with `5 ≤ |S| < N` has
`φ_s(S) > (12/25) β` is at most `cubeM {¬ GoodW} + cubeM E5ᶜ` (the open-cube exception is null). -/
theorem thmW4 : ∀ᶠ N : ℕ in atTop, ∀ (s tc : State N), N ≤ 3 * ham tc s →
    ∀ f : ({tc, s} : Finset (State N)) → Fin N → ℝ, (∀ a i, f a i ∈ Set.Ioo (0 : ℝ) 1) →
      (N : ℝ) ^ 9 * sigN N ≤ ∏ j, clamp01 (f ⟨tc, mem_insert_self tc {s}⟩ j) →
      ∏ j, clamp01 (f ⟨tc, mem_insert_self tc {s}⟩ j) ≤ Real.exp (-(N : ℝ) / 16) →
      ∏ j, clamp01 (f ⟨s, mem_insert_of_mem (mem_singleton_self s)⟩ j) ≤
        (2 : ℝ) ^ (-(N : ℝ) / 3) →
      rowsOutM {tc, s} {v | ¬ ∀ S : Finset (Fin N), 5 ≤ S.card → S.card < N →
          phi (flipP s (glueRows {tc, s} f v)) s S ≤
            12 / 25 * (Pw (glueRows {tc, s} f v) tc / Zs (glueRows {tc, s} f v))} ≤
        cubeM N {w | ¬ GoodW N s w} + cubeM N (E5 N s tc)ᶜ := by
  filter_upwards [ev_W4Num] with N hnum
  intro s tc hham f hf hP1 hP2 hPs
  have htcA : tc ∈ ({tc, s} : Finset (State N)) := mem_insert_self tc {s}
  have hsA : s ∈ ({tc, s} : Finset (State N)) := mem_insert_of_mem (mem_singleton_self s)
  set E : Set (Param N) := {w | GoodW N s w} ∩ E5 N s tc ∩ openCube N with hE
  have hEm : MeasurableSet E :=
    ((measurableSet_goodW s).inter (measurableSet_E5 s tc)).inter b1_measurableSet_openCube
  have hΦ : ∀ w w', AgreeOff {tc, s} w w' → w' ∈ E →
      ((∀ i, w tc i ∈ Set.Ioo (0 : ℝ) 1 ∧ w s i ∈ Set.Ioo (0 : ℝ) 1) →
        (N : ℝ) ^ 9 * sigN N ≤ Pw w tc → Pw w tc ≤ Real.exp (-(N : ℝ) / 16) →
        Pw w s ≤ (2 : ℝ) ^ (-(N : ℝ) / 3) →
        ∀ S : Finset (Fin N), 5 ≤ S.card → S.card < N →
          phi (flipP s w) s S ≤ 12 / 25 * (Pw w tc / Zs w)) := by
    intro w w' hA hw' hrow hP1 hP2 hPs S hk5 hkN
    exact thmW4_det hnum hham hA hw'.1.1 hw'.1.2 hw'.2 hrow hP1 hP2 hPs hk5 hkN
  have htrans := cpl_transfer {tc, s} f hEm hΦ
  have hgt : ∀ v i, glueRows {tc, s} f v tc i = f ⟨tc, htcA⟩ i := fun v i => by
    rw [glueRows_of_mem {tc, s} f v htcA]
  have hgs : ∀ v i, glueRows {tc, s} f v s i = f ⟨s, hsA⟩ i := fun v i => by
    rw [glueRows_of_mem {tc, s} f v hsA]
  have hPt : ∀ v, Pw (glueRows {tc, s} f v) tc = ∏ j, clamp01 (f ⟨tc, htcA⟩ j) := fun v => by
    unfold Pw; simp_rw [hgt v]
  have hPsv : ∀ v, Pw (glueRows {tc, s} f v) s = ∏ j, clamp01 (f ⟨s, hsA⟩ j) := fun v => by
    unfold Pw; simp_rw [hgs v]
  refine le_trans (measure_mono ?_) (htrans.trans ?_)
  · intro v hv hΦv
    apply hv
    refine hΦv (fun i => ⟨?_, ?_⟩) ?_ ?_ ?_
    · rw [hgt]; exact hf _ i
    · rw [hgs]; exact hf _ i
    · rw [hPt]; exact hP1
    · rw [hPt]; exact hP2
    · rw [hPsv]; exact hPs
  · have hEc : Eᶜ ⊆ {w | ¬ GoodW N s w} ∪ (E5 N s tc)ᶜ ∪ (openCube N)ᶜ := by
      intro w hw
      simp only [hE, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq,
        not_and_or] at hw ⊢
      tauto
    calc cubeM N Eᶜ ≤ cubeM N ({w | ¬ GoodW N s w} ∪ (E5 N s tc)ᶜ ∪ (openCube N)ᶜ) :=
          measure_mono hEc
      _ ≤ cubeM N ({w | ¬ GoodW N s w} ∪ (E5 N s tc)ᶜ) + cubeM N (openCube N)ᶜ :=
          measure_union_le _ _
      _ ≤ cubeM N {w | ¬ GoodW N s w} + cubeM N (E5 N s tc)ᶜ + 0 := by
          rw [cubeM_compl_openCube]; exact add_le_add (measure_union_le _ _) le_rfl
      _ = _ := add_zero _

/-- **Theorem W4, explicit bound.** Eventually, the same probability is at most
`fGood N + fB5 N`, and `fGood N + fB5 N → 0` (`tendsto_fGood_add_fB5`). -/
theorem thmW4_bound : ∀ᶠ N : ℕ in atTop, ∀ (s tc : State N), N ≤ 3 * ham tc s →
    ∀ f : ({tc, s} : Finset (State N)) → Fin N → ℝ, (∀ a i, f a i ∈ Set.Ioo (0 : ℝ) 1) →
      (N : ℝ) ^ 9 * sigN N ≤ ∏ j, clamp01 (f ⟨tc, mem_insert_self tc {s}⟩ j) →
      ∏ j, clamp01 (f ⟨tc, mem_insert_self tc {s}⟩ j) ≤ Real.exp (-(N : ℝ) / 16) →
      ∏ j, clamp01 (f ⟨s, mem_insert_of_mem (mem_singleton_self s)⟩ j) ≤
        (2 : ℝ) ^ (-(N : ℝ) / 3) →
      rowsOutM {tc, s} {v | ¬ ∀ S : Finset (Fin N), 5 ≤ S.card → S.card < N →
          phi (flipP s (glueRows {tc, s} f v)) s S ≤
            12 / 25 * (Pw (glueRows {tc, s} f v) tc / Zs (glueRows {tc, s} f v))} ≤
        ENNReal.ofReal (fGood N + fB5 N) := by
  filter_upwards [thmW4, eventually_ge_atTop 1, ev_EWnum] with N hW hN hnum
  intro s tc hham f hf hP1 hP2 hPs
  have hG0 : 0 ≤ fGood N := by
    obtain ⟨h2, h3, h4, h6, h11, h12, h13a, h13b, h16⟩ := fg_nonneg N
    unfold fGood; positivity
  have hB0 : 0 ≤ fB5 N := by
    have := aCr_pos; have := bEF_pos
    obtain ⟨h2, -⟩ := fg_nonneg N
    unfold fB5 fEH; positivity
  refine (hW s tc hham f hf hP1 hP2 hPs).trans ?_
  rw [ENNReal.ofReal_add hG0 hB0]
  exact add_le_add (cubeM_notGood_le_fGood s) (cubeM_not_E5_le hN hnum s tc)

theorem tendsto_fGood_add_fB5 : Tendsto (fun N => fGood N + fB5 N) atTop (𝓝 0) := by
  have := tendsto_fGood.add tendsto_fB5
  rwa [add_zero] at this

/-! ### Eventual forms of Theorem B5, Corollary Mid and Corollary KT-LB -/

/-- **Theorem B5** (W4 Section 6, `∀ᶠ` form). -/
theorem thmB5 : ∀ᶠ N : ℕ in atTop, ∀ (s tc : State N), N ≤ 3 * ham tc s →
    ∀ z : Param N, z ∈ openCube N → ∀ w' : Param N, AgreeOff {tc, s} (flipP s z) w' →
      w' ∈ E5 N s tc → Pw (flipP s z) tc + Pw (flipP s z) s ≤ 1 / (N : ℝ) ^ 3 →
      ∀ S : Finset (Fin N), K2N N < S.card → S.card < N → phi z s S ≤ Real.exp (-(N : ℝ) / 4) := by
  filter_upwards [ev_W4Num] with N hnum
  intro s tc hham z hz w' hA hE hH S hk hk'
  exact thmB5_det hnum.one_le hnum.big hnum.d1 hnum.eta' hnum.ratio hnum.hoeff hnum.rate hham hz
    hA hE hH hk hk'

/-- The levels of Proposition M at an `N` where the eventual inequalities hold. -/
lemma levels_of_num (hnum : W4Num N) {H Z' : ℝ} (hH0 : 0 ≤ H) (hNH : (N : ℝ) * H ≤ 1 / 10000)
    (hZ' : 1 / 2 ≤ Z') {k : ℕ} (hk1 : 1 ≤ k) (hkK : k ≤ K2N N) :
    1 / 4 - 4 / 10000 ≤ LK N k Z' H ∧
      (k : ℝ) * (deltaK N k + 2 * epsK N k H) ≤ (k : ℝ) / 2 ^ k / 6 + 7 / 10000 := by
  have hN := hnum.one_le
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hdl0 := dlev_nonneg N k
  have hE60 := E6_nonneg N k
  have n2 := hnum.dl k hk1 hkK
  have n3 := hnum.tm k hk1 hkK
  have hHle : H ≤ 1 / 10000 := by
    have : H ≤ (N : ℝ) * H := le_mul_of_one_le_left hH0 hN'
    linarith
  have hdl : dlev N k ≤ 1 / 10000 := by
    have : dlev N k ≤ (N : ℝ) * dlev N k := le_mul_of_one_le_left hdl0 hN'
    linarith
  have htm : 2 * tauN N + 2 * Mk N k ≤ 1 / 10000 := by
    have h0 : 0 ≤ 2 * tauN N + 2 * Mk N k := by
      have := tauN_pos N; have := Mk_nonneg N k; positivity
    have : 2 * tauN N + 2 * Mk N k ≤ (N : ℝ) * (2 * tauN N + 2 * Mk N k) :=
      le_mul_of_one_le_left h0 hN'
    linarith
  have hkN : (k : ℝ) ≤ N := by
    have : k ≤ N := by unfold K2N at hkK; omega
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · unfold LK epsK; have := hnum.sig8; linarith
  · have e1 : (k : ℝ) * (deltaK N k + 2 * epsK N k H) =
        ((k : ℝ) * (1 / 2 : ℝ) ^ (k - 1)) / 12 + (k : ℝ) * E6 N k / 12 + 2 * ((k : ℝ) * dlev N k)
          + 2 * ((k : ℝ) * H) + 2 * ((k : ℝ) * (2 * tauN N + 2 * Mk N k)) := by
      unfold deltaK epsK; ring
    rw [e1, one_div_two_pow_pred hk1]
    have a1 : (k : ℝ) * E6 N k ≤ 1 / 10000 := by
      calc (k : ℝ) * E6 N k ≤ N * (64 * N * sigN N) :=
            mul_le_mul hkN (E6_le k hN) hE60 (by positivity)
        _ = 64 * (N : ℝ) ^ 2 * sigN N := by ring
        _ ≤ 1 / 10000 := hnum.sig64
    have a2 : (k : ℝ) * dlev N k ≤ 1 / 10000 := (mul_le_mul_of_nonneg_right hkN hdl0).trans n2
    have a3 : (k : ℝ) * H ≤ 1 / 10000 := (mul_le_mul_of_nonneg_right hkN hH0).trans hNH
    have a4 : (k : ℝ) * (2 * tauN N + 2 * Mk N k) ≤ 1 / 10000 :=
      (mul_le_mul_of_nonneg_right hkN (by have := tauN_pos N; have := Mk_nonneg N k; positivity)).trans n3
    linarith

/-- **Corollary Mid** (`∀ᶠ` form): under (HM), `φ_s(S) ≤ 10 k 2^{-k}` for `2 ≤ |S| ≤ K2N N`. -/
theorem corMid_ev : ∀ᶠ N : ℕ in atTop, ∀ (s tc u s0 : State N) (z : Param N), z ∈ openCube N →
    ∀ w' : Param N, AgreeOff {tc, u} (flipP s z) w' → GoodW N s0 w' →
      Pw (flipP s z) tc + Pw (flipP s z) u ≤ 1 / (N : ℝ) ^ 3 →
      ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ K2N N → phi z s S ≤ 10 * S.card / 2 ^ S.card := by
  filter_upwards [ev_W4Num] with N hnum
  intro s tc u s0 z hz w' hA hG hH S hk2 hkK
  have hN := hnum.one_le
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hH0 : 0 ≤ Pw (flipP s z) tc + Pw (flipP s z) u := add_nonneg (Pw_nonneg _ _) (Pw_nonneg _ _)
  have hNH : (N : ℝ) * (Pw (flipP s z) tc + Pw (flipP s z) u) ≤ 1 / 10000 := by
    have h1 : (N : ℝ) * (Pw (flipP s z) tc + Pw (flipP s z) u) ≤ N * (1 / (N : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left hH (by positivity)
    have e : (N : ℝ) * (1 / (N : ℝ) ^ 3) = 1 / (N : ℝ) ^ 2 := by field_simp
    linarith [hnum.n2]
  obtain ⟨hL, hnm⟩ := levels_of_num hnum hH0 hNH hG.g3.1 (by omega) hkK
  have hx : (S.card : ℝ) / 2 ^ S.card ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : 2 * S.card ≤ 2 ^ S.card := by
      have := Nat.lt_two_pow_self (n := S.card - 1)
      have e : 2 ^ S.card = 2 * 2 ^ (S.card - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    have : (2 * S.card : ℝ) ≤ 2 ^ S.card := by exact_mod_cast this
    linarith
  have hLpos : 0 < LK N S.card (Zs w') (Pw (flipP s z) tc + Pw (flipP s z) u) := by linarith
  refine corMid hN hz hA hG hk2 (by linarith) ?_ ?_
  · unfold rhoK
    rw [div_le_iff₀ hLpos]
    linarith
  · have h1 := (tr1 hA hG.g2).2
    have h2 := hG.g3.2.1
    have : Pw (flipP s z) tc + Pw (flipP s z) u ≤ 1 / 10000 := by
      have : Pw (flipP s z) tc + Pw (flipP s z) u ≤
          (N : ℝ) * (Pw (flipP s z) tc + Pw (flipP s z) u) := le_mul_of_one_le_left hH0 hN'
      linarith
    linarith

/-- **Corollary KT-LB** (`∀ᶠ` form): with `P_tc ≥ N^9 σ_N`, `P_tc ≤ e^{-N/16}`, `P_s ≤ 2^{-N/3}`,
every `S` with `5 ≤ |S| ≤ K2N N` has `φ_s(S) ≤ (12/25) β`. -/
theorem corKTLB_ev : ∀ᶠ N : ℕ in atTop, ∀ (s tc : State N) (z : Param N), z ∈ openCube N →
    ∀ w' : Param N, AgreeOff {tc, s} (flipP s z) w' → GoodW N s w' →
      (N : ℝ) ^ 9 * sigN N ≤ Pw (flipP s z) tc → Pw (flipP s z) tc ≤ Real.exp (-(N : ℝ) / 16) →
      Pw (flipP s z) s ≤ (2 : ℝ) ^ (-(N : ℝ) / 3) →
      ∀ S : Finset (Fin N), 5 ≤ S.card → S.card ≤ K2N N →
        phi z s S ≤ 12 / 25 * (Pw (flipP s z) tc / Zs (flipP s z)) := by
  filter_upwards [ev_W4Num] with N hnum
  intro s tc z hz w' hA hG hP1 hP2 hPs S hk5 hkK
  have hN := hnum.one_le
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hH : Pw (flipP s z) tc + Pw (flipP s z) s ≤ 1 / (N : ℝ) ^ 3 := by
    have := hnum.hsum; linarith
  have hNH : (N : ℝ) * (Pw (flipP s z) tc + Pw (flipP s z) s) ≤ 1 / 10000 := by
    have h1 : (N : ℝ) * (Pw (flipP s z) tc + Pw (flipP s z) s) ≤ N * (1 / (N : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left hH (by positivity)
    have e : (N : ℝ) * (1 / (N : ℝ) ^ 3) = 1 / (N : ℝ) ^ 2 := by field_simp
    linarith [hnum.n2]
  have hPs' : Pw (flipP s z) s ≤ 1 / 10000 * Pw (flipP s z) tc := by
    have := hnum.srow; linarith
  have hkN : S.card ≤ N := card_le_N S
  exact corKTLB hN hz hA hG hk5 hnum.sig8 (hnum.dl _ (by omega) hkK)
    (hnum.tm _ (by omega) hkK) hnum.sig64 (hnum.fl _ (by omega) hkN) hNH hP1 hPs'

end W4

end

end Census
end IIT

