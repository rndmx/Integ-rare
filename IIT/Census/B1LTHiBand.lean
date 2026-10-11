/-
Census, B1 LTBetaHi, round-2 open items (a) and (d): **the level band** and **the lower bound on `P(tc)`**.

(d) `bd_Ptc_ge`: on `{Lσ_N ≤ β, Zs ≥ 1/2}`, eventually `P(tc) ≥ e^{-(x₁ - 1/800)N}` (any `L > 0`); `bd_tc_Sp_ev`:
    then `tc ∈ Sp` (so the heavy set `lt3H = {tc} ∪ Sp` is `Sp`).
(a) The band `|Num(S, Y, t, i) - a₃ Zs| ≤ η` for every triple `S` (W2 G3 + heavy rows), with
    `η := 11 P(tc) + 8 e^{-N/7}` (`bdEta`) and `η² ≤ (t/10^6) P(tc) a₃ Zs` (the `hlev`/`hηs` inputs of `lt3_TCprime`):
  * G2' (`bd_heavy_rows`): no row has `X ≤ e^{-3} N` off probability `e^{-(2 - log 2)N}`; then `P ≤ e^{-e^{-3}N}`;
  * the light level event `bdLev λ` (`λ = e^{-N/7}`): `|G_{i,R}(T) - c(R,T) Z_ns| ≤ λ` for every `(i, R, T)` with
    `|{i} ∪ R ∪ T| ≤ 3`, where `c(∅,∅) = 2/3`, `c(R,∅) = 1/2` (`R ≠ ∅`), `c(R,T) = 0` (`T ≠ ∅`).
    Each failure is `≤ 40 e^{-4N}`: the `T ≠ ∅` / `R ≠ ∅` statistics by the LT2 count lemmas at one statistic
    (`m_T`, `Õ`, `Ñ⁰/Ñ¹` with the class `{min R}`), the level statistic `Σ_v P_ns(v)(y_{v,i} - 2/3)` by Bernstein
    around its mean (`bd_rowsum_tail`) with the truncation bias `|2^N E| ≤ e^{x₁N}(2/3)^N` (`bd_bias`);
  * deterministic: `bd_light_level` (`|NumNs - a₃ Z_ns| ≤ 8λ`, Lemma D1), `bd_band_det` (heavy rows add
    `≤ |Sp| P(tc)`), `bd_hlev` (all `Y ⊆ S` via `pk_hlev_of_full`), `bd_eta_sq`;
  * `bd_not_good_ev`: `P(¬ bdGood) ≤ e^{-1.2N}` (`bdGood` = G2' ∧ `bdLev (e^{-N/7})`); `bd_band` (assembly).
-/
import IIT.Census.B1LTHiT6d
import IIT.Census.B1LTHiFloor

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-! ### Small asymptotic helpers -/

/-- `e^{-cN} ≤ δ` eventually (`c, δ > 0`). -/
lemma bd_exp_ev {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) : ∀ᶠ N : ℕ in atTop, Real.exp (-(c * N)) ≤ δ := by
  filter_upwards [eventually_ge_atTop ⌈-Real.log δ / c⌉₊] with N hN
  have h1 : -Real.log δ / c ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have h2 : -Real.log δ ≤ c * N := by rw [div_le_iff₀ hc] at h1; linarith
  calc Real.exp (-(c * N)) ≤ Real.exp (Real.log δ) := Real.exp_le_exp.2 (by linarith)
    _ = δ := Real.exp_log hδ

/-- `(2 : ℝ)^N = e^{N log 2}`. -/
lemma bd_two_pow (N : ℕ) : (2 : ℝ) ^ N = Real.exp (N * Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- A bound on `μ.real` gives a bound on the measure. -/
lemma bd_real_le {s : Set (Param N)} {b : ℝ} (h : (cubeM N).real s ≤ b) : cubeM N s ≤ ENNReal.ofReal b := by
  haveI : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  rw [← ENNReal.ofReal_toReal (measure_ne_top (cubeM N) s)]
  exact ENNReal.ofReal_le_ofReal h

/-- Union of two events with real bounds. -/
lemma bd_union2 {A B : Set (Param N)} {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : cubeM N A ≤ ENNReal.ofReal a) (hB : cubeM N B ≤ ENNReal.ofReal b) (hd : a + b ≤ d) :
    cubeM N (A ∪ B) ≤ ENNReal.ofReal d := by
  refine (measure_union_le A B).trans ((add_le_add hA hB).trans ?_)
  rw [← ENNReal.ofReal_add ha hb]
  exact ENNReal.ofReal_le_ofReal hd

/-! ### (d) The lower bound on `P(tc)` -/

/-- **(d)** For any `L > 0`, eventually: `Zs ≥ 1/2` and `Lσ_N ≤ β` give `P(tc) ≥ e^{-(x₁ - 1/800)N}`. -/
theorem bd_Ptc_ge {L : ℝ} (hL : 0 < L) : ∀ᶠ N : ℕ in atTop, ∀ w : Param N,
    1 / 2 ≤ Zs w → L * sigN N ≤ betaW w → Real.exp (-((lt2x1 - 1 / 800) * N)) ≤ Pw w (tcRow w) := by
  filter_upwards [eventually_ge_atTop ⌈800 * (Real.log 2 - Real.log L)⌉₊] with N hNL w hZ hβ
  have hNL' : 800 * (Real.log 2 - Real.log L) ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNL)
  have hZpos : 0 < Zs w := lt_of_lt_of_le (by norm_num) hZ
  have hβZ : betaW w * Zs w = Pw w (tcRow w) := by unfold betaW; exact div_mul_cancel₀ _ hZpos.ne'
  have e1 : L * sigN N * (1 / 2) ≤ betaW w * (1 / 2) := mul_le_mul_of_nonneg_right hβ (by norm_num)
  have e2 : betaW w * (1 / 2) ≤ betaW w * Zs w := mul_le_mul_of_nonneg_left hZ (betaW_nonneg w)
  have hlow : L * (1 / 2) * sigN N ≤ Pw w (tcRow w) := by linarith
  refine le_trans ?_ hlow
  rw [flr_sig_eq hL N]
  refine Real.exp_le_exp.2 ?_
  have e3 : (lt2x1 - 1 / 800) * (N : ℝ) = x0 * N + (N : ℝ) / 800 := by unfold lt2x1; ring
  rw [e3]
  linarith

/-- **`tc` is special** as soon as `P(tc) ≥ e^{-x₁ N}` (open cube). -/
lemma bd_tc_Sp {w : Param N} (hw : w ∈ openCube N) (h : Real.exp (-(lt2x1 * N)) ≤ Pw w (tcRow w)) :
    tcRow w ∈ lt2Sp w := by
  simp only [lt2Sp, mem_filter, mem_univ, true_and]
  have hP : Pw w (tcRow w) = Real.exp (-XW w (tcRow w)) := by
    unfold Pw XW
    rw [Finset.sum_neg_distrib, neg_neg, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi := hw (tcRow w) i
    rw [b1_clamp01_of_mem_Ioo hi, Real.exp_log hi.1]
  rw [hP] at h
  have := Real.exp_le_exp.1 h
  linarith

/-- **(d), with `tc ∈ Sp`**: eventually on `{Zs ≥ 1/2, Lσ_N ≤ β}` (open cube), `tc ∈ Sp`. -/
theorem bd_tc_Sp_ev {L : ℝ} (hL : 0 < L) : ∀ᶠ N : ℕ in atTop, ∀ w : Param N, w ∈ openCube N →
    1 / 2 ≤ Zs w → L * sigN N ≤ betaW w → tcRow w ∈ lt2Sp w := by
  filter_upwards [bd_Ptc_ge hL] with N hN w hw hZ hβ
  refine bd_tc_Sp hw ((Real.exp_le_exp.2 ?_).trans (hN w hZ hβ))
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-! ### G2': no row is very heavy -/

/-- **No row has `X ≤ e^{-3} N`**, off probability `≤ e^{-(2 - log 2) N}`. -/
theorem bd_heavy_rows (hN : 0 < N) :
    cubeM N {w : Param N | ∃ r, XW w r ≤ Real.exp (-3) * N} ≤
      ENNReal.ofReal (Real.exp (-((2 - Real.log 2) * N))) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have he3 : 0 < Real.exp (-3) := Real.exp_pos _
  have he1 : Real.exp (-3) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have h := min_rows_tail (N := N) ∅ (x := Real.exp (-3) * N) (by positivity) (by nlinarith)
  have e1 : Real.exp (-3) * (N : ℝ) / N = Real.exp (-3) := by field_simp
  rw [e1, Real.log_exp] at h
  refine (measure_mono ?_).trans (h.trans (ENNReal.ofReal_le_ofReal ?_))
  · rintro w ⟨r, hr⟩
    exact ⟨r, Finset.notMem_empty r, hr⟩
  · rw [bd_two_pow, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith

/-- No very heavy row: every row product is `≤ e^{-e^{-3} N}`. -/
lemma bd_Pw_le_of_light {w : Param N} (h : ∀ r, Real.exp (-3) * N < XW w r) (r : State N) :
    Pw w r ≤ Real.exp (-(Real.exp (-3) * N)) := by
  have h1 := st_Pw_le_exp univ w r
  have h2 : XMW w univ r = XW w r := rfl
  rw [h2] at h1
  exact h1.trans (Real.exp_le_exp.2 (by linarith [h r]))

/-! ### The light level statistics -/

/-- The non-special mass `Z_ns = Σ_v P_ns(v)`. -/
noncomputable def bdZns (w : Param N) : ℝ := ∑ v, lt2gNs (w v)

/-- The level centring of `G_{i,R}(T)`: `2/3` (`R = T = ∅`), `1/2` (`R ≠ ∅ = T`), `0` (`T ≠ ∅`). -/
noncomputable def bdC (R T : Finset (Fin N)) : ℝ := if T = ∅ then (if R = ∅ then 2 / 3 else 1 / 2) else 0

/-- The index set: `(i, R, T)` with `|{i} ∪ R ∪ T| ≤ 3`. -/
def bdIdx (N : ℕ) : Finset (Fin N × Finset (Fin N) × Finset (Fin N)) :=
  univ.filter fun α => (insert α.1 (α.2.1 ∪ α.2.2)).card ≤ 3

/-- **The light level event** at tolerance `λ`. -/
def bdLev (lam : ℝ) (w : Param N) : Prop :=
  ∀ α ∈ bdIdx N, |lt2G w α.1 α.2.1 α.2.2 - bdC α.2.1 α.2.2 * bdZns w| ≤ lam

lemma bdIdx_card : (bdIdx N).card ≤ (N + 1) ^ 7 := by
  classical
  set sm := (univ : Finset (Finset (Fin N))).filter fun B => B.card ≤ 3 with hsm
  have hsub : bdIdx N ⊆ univ ×ˢ (sm ×ˢ sm) := by
    intro α hα
    have h := (mem_filter.1 hα).2
    have hR : α.2.1.card ≤ 3 :=
      (card_le_card (subset_union_left.trans (subset_insert _ _))).trans h
    have hT : α.2.2.card ≤ 3 :=
      (card_le_card (subset_union_right.trans (subset_insert _ _))).trans h
    exact mem_product.2 ⟨mem_univ _, mem_product.2 ⟨mem_filter.2 ⟨mem_univ _, hR⟩, mem_filter.2 ⟨mem_univ _, hT⟩⟩⟩
  have hc := card_small_sets_le (α := Fin N) 3
  rw [Fintype.card_fin] at hc
  calc (bdIdx N).card ≤ (univ ×ˢ (sm ×ˢ sm)).card := card_le_card hsub
    _ = N * (sm.card * sm.card) := by rw [card_product, card_product, card_univ, Fintype.card_fin]
    _ ≤ (N + 1) * ((N + 1) ^ 3 * (N + 1) ^ 3) :=
        Nat.mul_le_mul (Nat.le_succ N) (Nat.mul_le_mul hc hc)
    _ = (N + 1) ^ 7 := by ring

/-! ### The level statistic `Σ_v P_ns(v)(y_{v,i} - 2/3)`: mean and Bernstein -/

/-- The row function of the level statistic. -/
noncomputable def bdg (i : Fin N) (x : Fin N → ℝ) : ℝ := lt2gNs x * (clamp01 (x i) - 2 / 3)

lemma bdg_measurable (i : Fin N) : Measurable (bdg i) :=
  lt2gNs_measurable.mul ((clamp01_measurable.comp (measurable_pi_apply i)).sub measurable_const)

lemma bdg_abs_le (i : Fin N) (x : Fin N → ℝ) : |bdg i x| ≤ lt2θ N := by
  unfold bdg
  rw [abs_mul, abs_of_nonneg (lt2gNs_nonneg x)]
  have h1 : |clamp01 (x i) - 2 / 3| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [clamp01_nonneg (x i), clamp01_le_one (x i)]
  calc lt2gNs x * |clamp01 (x i) - 2 / 3| ≤ lt2gNs x * 1 :=
        mul_le_mul_of_nonneg_left h1 (lt2gNs_nonneg x)
    _ ≤ lt2θ N := by rw [mul_one]; exact lt2gNs_le x

lemma lt2gNs_le_one (x : Fin N → ℝ) : lt2gNs x ≤ 1 := by
  unfold lt2gNs; split_ifs
  · exact prod_le_one (fun j _ => clamp01_nonneg _) fun j _ => clamp01_le_one _
  · exact zero_le_one

lemma bdg_sq_int (i : Fin N) : ∫ x, bdg i x ^ 2 ∂rowM N ≤ (1 / 3 : ℝ) ^ N := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  have hle : ∀ x, bdg i x ^ 2 ≤ lt2gNs x ^ 2 := fun x => by
    unfold bdg
    rw [mul_pow]
    have h1 : (clamp01 (x i) - 2 / 3) ^ 2 ≤ 1 := by
      nlinarith [clamp01_nonneg (x i), clamp01_le_one (x i)]
    calc lt2gNs x ^ 2 * (clamp01 (x i) - 2 / 3) ^ 2 ≤ lt2gNs x ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = lt2gNs x ^ 2 := mul_one _
  have hi : Integrable (fun x => lt2gNs x ^ 2) (rowM N) :=
    integrable_rowM (lt2gNs_measurable.pow_const 2) 1 fun x => by
      rw [abs_of_nonneg (sq_nonneg _)]
      have h0 := lt2gNs_nonneg x
      have h1 := lt2gNs_le_one x
      nlinarith
  exact (integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) hi (ae_of_all _ hle)).trans
    lt2gNs_sq_int

/-- `P(x) - P_ns(x) ≤ e^{x₁N} P(x)²` (the truncated part only sees rows with `P ≥ e^{-x₁N}`). -/
lemma bd_trunc_le (x : Fin N → ℝ) :
    (∏ j, clamp01 (x j)) - lt2gNs x ≤ Real.exp (lt2x1 * N) * (∏ j, clamp01 (x j)) ^ 2 := by
  have hP0 : 0 ≤ ∏ j, clamp01 (x j) := prod_nonneg fun j _ => clamp01_nonneg _
  unfold lt2gNs
  split_ifs with h
  · rw [sub_self]; positivity
  · rw [sub_zero]
    push Not at h
    by_cases hpos : ∀ j, 0 < clamp01 (x j)
    · have e : ∏ j, clamp01 (x j) = Real.exp (-∑ j, -Real.log (clamp01 (x j))) := by
        rw [Finset.sum_neg_distrib, neg_neg, Real.exp_sum]
        exact Finset.prod_congr rfl fun j _ => (Real.exp_log (hpos j)).symm
      have hge : Real.exp (-(lt2x1 * N)) ≤ ∏ j, clamp01 (x j) := by
        rw [e]; exact Real.exp_le_exp.2 (by linarith)
      have hone : 1 ≤ Real.exp (lt2x1 * N) * ∏ j, clamp01 (x j) := by
        have := mul_le_mul_of_nonneg_left hge (Real.exp_pos (lt2x1 * N)).le
        rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
      calc ∏ j, clamp01 (x j) = 1 * ∏ j, clamp01 (x j) := (one_mul _).symm
        _ ≤ (Real.exp (lt2x1 * N) * ∏ j, clamp01 (x j)) * ∏ j, clamp01 (x j) :=
            mul_le_mul_of_nonneg_right hone hP0
        _ = Real.exp (lt2x1 * N) * (∏ j, clamp01 (x j)) ^ 2 := by ring
    · push Not at hpos
      obtain ⟨j, hj⟩ := hpos
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (le_antisymm hj (clamp01_nonneg _))]
      simp

/-- `E[P (y_i - 2/3)] = 0`. -/
lemma bd_int_P_center (i : Fin N) :
    ∫ x, (∏ j, clamp01 (x j)) * (clamp01 (x i) - 2 / 3) ∂rowM N = 0 := by
  have : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  set E : Fin N → ℕ := fun j => if j = i then 2 else 1 with hE
  have hEi : E i = 2 := by simp [hE]
  have hEj : ∀ j ∈ univ.erase i, E j = 1 := fun j hj => by simp [hE, Finset.ne_of_mem_erase hj]
  have hmono : ∀ x : Fin N → ℝ, (∏ j, clamp01 (x j)) * clamp01 (x i) = ∏ j, clamp01 (x j) ^ E j := by
    intro x
    rw [← Finset.mul_prod_erase univ (fun j => clamp01 (x j)) (mem_univ i),
      ← Finset.mul_prod_erase univ (fun j => clamp01 (x j) ^ E j) (mem_univ i)]
    have hrest : ∏ j ∈ univ.erase i, clamp01 (x j) ^ E j = ∏ j ∈ univ.erase i, clamp01 (x j) :=
      Finset.prod_congr rfl fun j hj => by rw [hEj j hj, pow_one]
    rw [hrest, hEi]; ring
  have hint1 : Integrable (fun x : Fin N → ℝ => (∏ j, clamp01 (x j)) * clamp01 (x i)) (rowM N) :=
    integrable_rowM (measurable_rowPw.mul (clamp01_measurable.comp (measurable_pi_apply i))) 1 fun x => by
      rw [abs_mul, abs_of_nonneg (prod_nonneg fun j _ => clamp01_nonneg _), abs_of_nonneg (clamp01_nonneg _)]
      exact mul_le_one₀ (prod_le_one (fun j _ => clamp01_nonneg _) fun j _ => clamp01_le_one _)
        (clamp01_nonneg _) (clamp01_le_one _)
  have hint2 : Integrable (fun x : Fin N → ℝ => (∏ j, clamp01 (x j))) (rowM N) :=
    integrable_rowM measurable_rowPw 1 fun x => abs_rowPw_le x
  have hsplit : ∀ x : Fin N → ℝ, (∏ j, clamp01 (x j)) * (clamp01 (x i) - 2 / 3) =
      (∏ j, clamp01 (x j)) * clamp01 (x i) - 2 / 3 * ∏ j, clamp01 (x j) := fun x => by ring
  simp_rw [hsplit]
  rw [integral_sub hint1 (hint2.const_mul _), integral_const_mul]
  simp_rw [hmono]
  rw [integral_rowM_monomial]
  have h1 : ∫ v, ∏ j, clamp01 (v j) ∂rowM N = (1 / 2 : ℝ) ^ N := by
    have := integral_rowP_pow' (N := N) 1
    simp only [pow_one] at this
    rw [this]; norm_num
  rw [h1]
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (fun h => by subst h; exact i.elim0)
  rw [← Finset.mul_prod_erase univ (fun j => 1 / ((E j : ℝ) + 1)) (mem_univ i)]
  have hrest : ∏ j ∈ univ.erase i, 1 / ((E j : ℝ) + 1) = (1 / 2 : ℝ) ^ (N - 1) := by
    have hc : ∀ j ∈ univ.erase i, 1 / ((E j : ℝ) + 1) = 1 / 2 := fun j hj => by
      rw [hEj j hj]; norm_num
    rw [Finset.prod_congr rfl hc, prod_const, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  rw [hrest, hEi]
  have e2 : (1 / 2 : ℝ) ^ N = 1 / 2 * (1 / 2 : ℝ) ^ (N - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hN]
  rw [e2]; push_cast; ring

/-- **The truncation bias**: `|E[P_ns (y_i - 2/3)]| ≤ e^{x₁N} 3^{-N}`. -/
lemma bd_bias (i : Fin N) : |∫ x, bdg i x ∂rowM N| ≤ Real.exp (lt2x1 * N) * (1 / 3 : ℝ) ^ N := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  set P : (Fin N → ℝ) → ℝ := fun x => ∏ j, clamp01 (x j) with hPdef
  have hPm : Measurable P := measurable_rowPw
  have hgNs : ∀ x, lt2gNs x ≤ P x := fun x => by
    unfold lt2gNs; split_ifs
    · exact le_rfl
    · exact prod_nonneg fun j _ => clamp01_nonneg _
  have hcm : Measurable fun x : Fin N → ℝ => clamp01 (x i) - 2 / 3 :=
    (clamp01_measurable.comp (measurable_pi_apply i)).sub measurable_const
  have hc1 : ∀ x : Fin N → ℝ, |clamp01 (x i) - 2 / 3| ≤ 1 := fun x => by
    rw [abs_le]; constructor <;> linarith [clamp01_nonneg (x i), clamp01_le_one (x i)]
  have hP1 : ∀ x, |P x| ≤ 1 := fun x => abs_rowPw_le x
  have hiA : Integrable (fun x => P x * (clamp01 (x i) - 2 / 3)) (rowM N) :=
    integrable_rowM (hPm.mul hcm) 1 fun x => by
      rw [abs_mul]; exact mul_le_one₀ (hP1 x) (abs_nonneg _) (hc1 x)
  have hiB : Integrable (fun x => (P x - lt2gNs x) * (clamp01 (x i) - 2 / 3)) (rowM N) :=
    integrable_rowM ((hPm.sub lt2gNs_measurable).mul hcm) 1 fun x => by
      rw [abs_mul]
      have h0 := lt2gNs_nonneg x
      have hd : |P x - lt2gNs x| ≤ 1 := by
        have := hP1 x
        rw [abs_le] at this ⊢
        constructor <;> linarith [hgNs x]
      exact mul_le_one₀ hd (abs_nonneg _) (hc1 x)
  have hsplit : ∀ x, bdg i x = P x * (clamp01 (x i) - 2 / 3) - (P x - lt2gNs x) * (clamp01 (x i) - 2 / 3) :=
    fun x => by unfold bdg; ring
  simp_rw [hsplit]
  rw [integral_sub hiA hiB]
  have h0 : ∫ x, P x * (clamp01 (x i) - 2 / 3) ∂rowM N = 0 := bd_int_P_center i
  rw [h0, zero_sub, abs_neg]
  have hiC : Integrable (fun x => Real.exp (lt2x1 * N) * P x ^ 2) (rowM N) :=
    (integrable_rowPp 2).const_mul _
  calc |∫ x, (P x - lt2gNs x) * (clamp01 (x i) - 2 / 3) ∂rowM N|
      ≤ ∫ x, |(P x - lt2gNs x) * (clamp01 (x i) - 2 / 3)| ∂rowM N := abs_integral_le_integral_abs
    _ ≤ ∫ x, Real.exp (lt2x1 * N) * P x ^ 2 ∂rowM N := by
        refine integral_mono hiB.abs hiC fun x => ?_
        simp only
        rw [abs_mul]
        have hd0 : 0 ≤ P x - lt2gNs x := by linarith [hgNs x]
        rw [abs_of_nonneg hd0]
        calc (P x - lt2gNs x) * |clamp01 (x i) - 2 / 3| ≤ (P x - lt2gNs x) * 1 :=
              mul_le_mul_of_nonneg_left (hc1 x) hd0
          _ ≤ Real.exp (lt2x1 * N) * P x ^ 2 := by rw [mul_one]; exact bd_trunc_le x
    _ = Real.exp (lt2x1 * N) * (1 / 3 : ℝ) ^ N := by
        rw [integral_const_mul, integral_rowP_pow' 2]; norm_num

/-- **Bernstein for a row-local sum around its mean.** -/
theorem bd_rowsum_tail (g : (Fin N → ℝ) → ℝ) (hg : Measurable g) {G : ℝ} (hG : ∀ x, |g x| ≤ G) {V ε : ℝ}
    (hε : 0 ≤ ε) (hV : (2 : ℝ) ^ N * ∫ x, g x ^ 2 ∂rowM N ≤ V) :
    (cubeM N).real {w | ε ≤ ∑ v, g (w v) - (2 : ℝ) ^ N * ∫ x, g x ∂rowM N} ≤
      Real.exp (-min (ε ^ 2 / (4 * V)) (ε / (2 * (2 * G)))) := by
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  haveI : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG 0)
  have hgi : Integrable g (rowM N) := Integrable.of_bound hg.aestronglyMeasurable G (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]; exact hG x)
  set Eg := ∫ x, g x ∂rowM N with hEgdef
  have hEg : |Eg| ≤ G := by
    calc |Eg| ≤ ∫ x, |g x| ∂rowM N := abs_integral_le_integral_abs
      _ ≤ ∫ _x, G ∂rowM N := integral_mono hgi.abs (integrable_const G) hG
      _ = G := by simp
  set X : State N → Param N → ℝ := fun v w => g (w v) - Eg with hX
  have hind : iIndepFun X (cubeM N) :=
    iIndepFun_rows (N := N) (fun _ x => g x - Eg) (fun _ => hg.sub measurable_const)
  have hmeas : ∀ v, AEMeasurable (X v) (cubeM N) := fun v =>
    ((hg.comp (measurable_pi_apply v)).sub measurable_const).aemeasurable
  have hcard : ((univ : Finset (State N)).card : ℝ) = 2 ^ N := by simp
  have hsum : ∀ w : Param N, ∑ v, g (w v) - (2 : ℝ) ^ N * Eg = ∑ v, X v w := by
    intro w
    simp only [hX, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
  simp_rw [hsum]
  refine bernstein_upper univ hind hmeas (by positivity) hε (fun v _ => ae_of_all _ fun w => ?_)
    (fun v _ => ?_) ?_
  · simp only [hX]
    exact (abs_sub _ _).trans (by linarith [hG (w v), hEg])
  · simp only [hX]
    rw [lt2_int_row (fun x => g x - Eg) (hg.sub measurable_const) v,
      integral_sub hgi (integrable_const _), integral_const]
    simp [Eg]
  · have hgi2 : Integrable (fun x => g x ^ 2) (rowM N) :=
      Integrable.of_bound (hg.pow_const 2).aestronglyMeasurable (G ^ 2) (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have := hG x
        nlinarith [abs_nonneg (g x), sq_abs (g x)])
    have e : ∫ x, (g x - Eg) ^ 2 ∂rowM N = ∫ x, g x ^ 2 ∂rowM N - Eg ^ 2 := by
      have : (fun x => (g x - Eg) ^ 2) = fun x => g x ^ 2 - 2 * Eg * g x + Eg ^ 2 := by
        funext x; ring
      rw [this, integral_add (f := fun x => g x ^ 2 - 2 * Eg * g x) (g := fun _ => Eg ^ 2)
        (hgi2.sub (hgi.const_mul _)) (integrable_const _),
        integral_sub (f := fun x => g x ^ 2) (g := fun x => 2 * Eg * g x) hgi2 (hgi.const_mul _),
        integral_const_mul, integral_const]
      simp [Eg]; ring
    calc ∑ v ∈ univ, ∫ w, X v w ^ 2 ∂cubeM N = ∑ _v : State N, ∫ x, (g x - Eg) ^ 2 ∂rowM N := by
          refine Finset.sum_congr rfl fun v _ => ?_
          simp only [hX]
          rw [lt2_int_row (fun x => (g x - Eg) ^ 2) ((hg.sub measurable_const).pow_const 2) v]
      _ ≤ ∑ _v : State N, ∫ x, g x ^ 2 ∂rowM N :=
          Finset.sum_le_sum fun v _ => by rw [e]; nlinarith [sq_nonneg Eg]
      _ = (2 : ℝ) ^ N * ∫ x, g x ^ 2 ∂rowM N := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
      _ ≤ V := hV

/-- **Two-sided tail of the level statistic** (centred at `0`, the bias absorbed in `ε`). -/
theorem bd_level_tail (i : Fin N) {ε : ℝ} (hε : 0 ≤ ε)
    (hbias : Real.exp (lt2x1 * N) * (2 / 3 : ℝ) ^ N ≤ ε) :
    cubeM N {w | 2 * ε ≤ |∑ v, bdg i (w v)|} ≤
      ENNReal.ofReal (2 * Real.exp (-min (ε ^ 2 / (4 * (2 / 3 : ℝ) ^ N)) (ε / (2 * (2 * lt2θ N))))) := by
  set Eg := ∫ x, bdg i x ∂rowM N with hEg
  have hB : |(2 : ℝ) ^ N * Eg| ≤ ε := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ N)]
    calc (2 : ℝ) ^ N * |Eg| ≤ 2 ^ N * (Real.exp (lt2x1 * N) * (1 / 3 : ℝ) ^ N) :=
          mul_le_mul_of_nonneg_left (bd_bias i) (by positivity)
      _ = Real.exp (lt2x1 * N) * (2 / 3 : ℝ) ^ N := by
          rw [show (2 / 3 : ℝ) ^ N = 2 ^ N * (1 / 3) ^ N by rw [← mul_pow]; norm_num]; ring
      _ ≤ ε := hbias
  have hV : (2 : ℝ) ^ N * ∫ x, bdg i x ^ 2 ∂rowM N ≤ (2 / 3 : ℝ) ^ N := by
    calc (2 : ℝ) ^ N * ∫ x, bdg i x ^ 2 ∂rowM N ≤ 2 ^ N * (1 / 3 : ℝ) ^ N :=
          mul_le_mul_of_nonneg_left (bdg_sq_int i) (by positivity)
      _ = (2 / 3 : ℝ) ^ N := by rw [← mul_pow]; norm_num
  have hV' : (2 : ℝ) ^ N * ∫ x, (fun x => -bdg i x) x ^ 2 ∂rowM N ≤ (2 / 3 : ℝ) ^ N := by
    simp only [neg_sq]; exact hV
  have h1 := bd_rowsum_tail (bdg i) (bdg_measurable i) (G := lt2θ N) (bdg_abs_le i) hε hV
  have h2 := bd_rowsum_tail (fun x => -bdg i x) (bdg_measurable i).neg (G := lt2θ N)
    (fun x => by rw [abs_neg]; exact bdg_abs_le i x) hε hV'
  have hneg : ∫ x, (fun x => -bdg i x) x ∂rowM N = -Eg := by simp only; rw [integral_neg]
  rw [hneg] at h2
  have hsub : {w : Param N | 2 * ε ≤ |∑ v, bdg i (w v)|} ⊆
      {w | ε ≤ ∑ v, bdg i (w v) - (2 : ℝ) ^ N * Eg} ∪
        {w | ε ≤ ∑ v, (fun x => -bdg i x) (w v) - (2 : ℝ) ^ N * -Eg} := by
    intro w hw
    simp only [Set.mem_setOf_eq] at hw
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.sum_neg_distrib]
    have hb := abs_le.1 hB
    rcases le_abs'.1 hw with h | h
    · right; linarith
    · left; linarith
  refine (measure_mono hsub).trans (bd_union2 (Real.exp_pos _).le (Real.exp_pos _).le
    (bd_real_le h1) (bd_real_le h2) (by linarith))

/-! ### One statistic: the tail of each kind -/

/-- The class functional of a nonempty shift: `{min R}`. -/
noncomputable def bdLam (R : Finset (Fin N)) : Finset (Fin N) :=
  if h : R.Nonempty then {R.min' h} else univ

lemma bdLam_odd {R : Finset (Fin N)} (hR : R.Nonempty) : (R ∩ bdLam R).card % 2 = 1 := by
  unfold bdLam
  rw [dif_pos hR]
  have : R ∩ {R.min' hR} = {R.min' hR} := by
    ext j; simp only [mem_inter, mem_singleton]
    constructor
    · exact fun h => h.2
    · intro h; subst h; exact ⟨R.min'_mem hR, rfl⟩
  rw [this, card_singleton]

lemma bdLam_ne_bot {R : Finset (Fin N)} (hR : R.Nonempty) (T : Finset (Fin N)) :
    symmDiff T T ≠ bdLam R := by
  rw [symmDiff_self]
  unfold bdLam; rw [dif_pos hR]
  exact (singleton_ne_empty _).symm

/-- `m_∅ = Z_ns`. -/
lemma lt2mT_empty (w : Param N) : lt2mT w ∅ = bdZns w := by
  unfold lt2mT bdZns
  exact Finset.sum_congr rfl fun v _ => by rw [lt2Chi_empty, mul_one]

/-- `G_{i,∅}(∅) - (2/3) Z_ns` is the level statistic. -/
lemma bd_G_empty_empty (w : Param N) (i : Fin N) :
    lt2G w i ∅ ∅ - 2 / 3 * bdZns w = ∑ v, bdg i (w v) := by
  unfold lt2G bdZns bdg
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun v _ => by rw [lt2Xor_empty, lt2Chi_empty]; ring

/-- A single statistic: `P(K ≤ |X_a|)` from a count lemma at `m = 1`. -/
lemma bd_single {α : Type*} [DecidableEq α] (a : α) (X : α → Param N → ℝ) (K : ℝ) {B : ℝ}
    (h : cubeM N {w | 1 ≤ (({a} : Finset α).filter fun b => K ≤ |X b w|).card} ≤ ENNReal.ofReal B) :
    cubeM N {w | K ≤ |X a w|} ≤ ENNReal.ofReal B := by
  refine (measure_mono fun w hw => ?_).trans h
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Finset.filter_singleton, if_pos hw, card_singleton]

/-- The two exponents of the single-statistic bounds at tolerance `λ = e^{-N/7}`. -/
noncomputable def bdκ (N : ℕ) : ℝ := Real.exp (-(N : ℝ) / 7) / (4 * sigN N)
noncomputable def bdA (N : ℕ) : ℝ := bdκ N ^ 2 / 4
noncomputable def bdB (N : ℕ) : ℝ := bdκ N * sigN N / (4 * lt2θ N)

lemma bdκ_pos : 0 < bdκ N := by unfold bdκ sigN; positivity

lemma bdκ_sig : bdκ N * sigN N = Real.exp (-(N : ℝ) / 7) / 4 := by
  have hσ : 0 < sigN N := by unfold sigN; positivity
  unfold bdκ; field_simp

/-- Both exponents are eventually `≥ 4N`. -/
lemma bd_AB_ev : ∀ᶠ N : ℕ in atTop, 4 * (N : ℝ) ≤ bdA N ∧ 4 * (N : ℝ) ≤ bdB N := by
  have hx0 := x0_gt
  have hx1 := lt2x1_bounds
  filter_upwards [cr_ev_poly_exp 1 (Real.log 256) (δ := 1 / 10) (by norm_num),
    cr_ev_poly_exp 1 (Real.log 64) (δ := 1 / 20) (by norm_num), eventually_ge_atTop 1] with N h1 h2 h3
  rw [Real.exp_log (by norm_num)] at h1 h2
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast h3
  constructor
  · -- `bdA = e^{2(x0 - 1/7)N}/64`
    have e : bdA N = Real.exp ((2 * x0 - 2 / 7) * N) / 64 := by
      unfold bdA bdκ
      rw [sigN_eq_exp, div_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      rw [show (Real.exp (((2 : ℕ) : ℝ) * (-(N : ℝ) / 7)) /
          ((4 : ℝ) ^ 2 * Real.exp (((2 : ℕ) : ℝ) * -(x0 * N))) / 4) =
        Real.exp (((2 : ℕ) : ℝ) * (-(N : ℝ) / 7)) / Real.exp (((2 : ℕ) : ℝ) * -(x0 * N)) / 64 by ring,
        ← Real.exp_sub]
      congr 2; push_cast; ring
    rw [e]
    have hle : Real.exp (1 / 10 * N) ≤ Real.exp ((2 * x0 - 2 / 7) * N) :=
      Real.exp_le_exp.2 (by nlinarith)
    have : ((N : ℝ) + 1) ^ 1 * 256 ≤ Real.exp ((2 * x0 - 2 / 7) * N) := h1.trans hle
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  · -- `bdB = e^{(x1 - 1/7)N}/16`
    have e : bdB N = Real.exp ((lt2x1 - 1 / 7) * N) / 16 := by
      unfold bdB
      rw [bdκ_sig]
      unfold lt2θ
      rw [show Real.exp (-(N : ℝ) / 7) / 4 / (4 * Real.exp (-(lt2x1 * N))) =
        Real.exp (-(N : ℝ) / 7) / Real.exp (-(lt2x1 * N)) / 16 by ring, ← Real.exp_sub]
      congr 2; ring
    rw [e]
    have hle : Real.exp (1 / 20 * N) ≤ Real.exp ((lt2x1 - 1 / 7) * N) :=
      Real.exp_le_exp.2 (by nlinarith)
    have : ((N : ℝ) + 1) ^ 1 * 64 ≤ Real.exp ((lt2x1 - 1 / 7) * N) := h2.trans hle
    rw [le_div_iff₀ (by norm_num)]; nlinarith

/-- `e^{-x} ≤ e^{-4N}` for `x ≥ min (bdA N) (bdB N)`. -/
lemma bd_exp_min_le {N : ℕ} (hAB : 4 * (N : ℝ) ≤ bdA N ∧ 4 * (N : ℝ) ≤ bdB N) {x : ℝ}
    (hx : min (bdA N) (bdB N) ≤ x) : Real.exp (-x) ≤ Real.exp (-(4 * N)) :=
  Real.exp_le_exp.2 (by have := le_min hAB.1 hAB.2; linarith)

section Tails

variable (hAB : 4 * (N : ℝ) ≤ bdA N ∧ 4 * (N : ℝ) ≤ bdB N)
include hAB

/-- Tail of one weight statistic `m_T` (`T ≠ ∅`), at level `κσ = e^{-N/7}/4`. -/
lemma bd_mT_tail {T : Finset (Fin N)} (hT : T.Nonempty) :
    cubeM N {w | bdκ N * sigN N ≤ |lt2mT w T|} ≤ ENNReal.ofReal (2 * Real.exp (-(4 * N))) := by
  have h := lt2_mT_count {T} (fun T' hT' => by rw [mem_singleton.1 hT']; exact hT) (bdκ_pos (N := N)) 1 le_rfl
  refine (bd_single T (fun T w => lt2mT w T) _ h).trans (ENNReal.ofReal_le_ofReal ?_)
  have hx : Real.exp (-min (bdκ N ^ 2 / 4) (bdκ N * sigN N / (4 * lt2θ N))) ≤ Real.exp (-(4 * N)) :=
    bd_exp_min_le hAB le_rfl
  simp only [card_singleton, Nat.choose_one_right, Nat.cast_one, pow_one, one_mul]
  linarith

/-- Tail of one own-entry statistic `Õ_i(T)` (`T ≠ ∅`). -/
lemma bd_Ot_tail (i : Fin N) {T : Finset (Fin N)} (hT : T.Nonempty) :
    cubeM N {w | bdκ N * sigN N ≤ |lt2Ot w (i, T)|} ≤ ENNReal.ofReal (2 * Real.exp (-(4 * N))) := by
  have h := lt2_Ot_count {(i, T)} (fun p hp => by rw [mem_singleton.1 hp]; exact hT) (bdκ_pos (N := N)) 1 le_rfl
  refine (bd_single (i, T) (fun p w => lt2Ot w p) _ h).trans (ENNReal.ofReal_le_ofReal ?_)
  have hθ : 0 < lt2θ N := Real.exp_pos _
  have hσ : 0 < sigN N := by unfold sigN; positivity
  have hκ := bdκ_pos (N := N)
  have hx : Real.exp (-min (20 * bdκ N ^ 2 / 3) (bdκ N * sigN N / (3 * lt2θ N))) ≤ Real.exp (-(4 * N)) := by
    refine bd_exp_min_le hAB (min_le_min ?_ ?_)
    · unfold bdA; nlinarith [sq_nonneg (bdκ N)]
    · unfold bdB
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  simp only [card_singleton, Nat.choose_one_right, Nat.cast_one, pow_one, one_mul, mul_one]
  linarith

/-- Tail of one shifted-entry statistic `Ñ^b_{i,R}(T)` (`R ≠ ∅`, class `{min R}`). -/
lemma bd_N0_tail (hN8 : 8 * (1 / 2 : ℝ) ^ N ≤ lt2tG N) (hN2 : 2 ≤ N)
    (hBs : lt2B2 N ≤ Real.exp (-((N : ℝ) ^ 3)) ∧ lt2Bpair N ≤ 6 * Real.exp (-((N : ℝ) ^ 3)))
    (b : Bool) (i : Fin N) {R : Finset (Fin N)} (hR : R.Nonempty) (T : Finset (Fin N)) :
    cubeM N {w | bdκ N * sigN N ≤ |lt2N0 (bdLam R) b w (i, R, T)|} ≤
      ENNReal.ofReal (16 * Real.exp (-(4 * N))) := by
  have hNne : N ≠ 0 := by omega
  have h := lt2_N0_count (b := b) (bdLam R) {(i, R, T)} (fun α hα => by rw [mem_singleton.1 hα]; exact bdLam_odd hR)
    (fun α hα α' hα' _ => by rw [mem_singleton.1 hα, mem_singleton.1 hα']; exact bdLam_ne_bot hR T)
    hN8 hNne (bdκ_pos (N := N)) 1 le_rfl
  refine (bd_single (i, R, T) (fun α w => lt2N0 (bdLam R) b w α) _ h).trans (ENNReal.ofReal_le_ofReal ?_)
  have hθ : 0 < lt2θ N := Real.exp_pos _
  have hσ : 0 < sigN N := by unfold sigN; positivity
  have hκ := bdκ_pos (N := N)
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN4' : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ (by linarith)
  have hN4 : (1 : ℝ) / (N : ℝ) ^ 4 ≤ 1 := by rw [div_le_one (by positivity)]; exact hN4'
  have hx : Real.exp (-min (3 * 1 * bdκ N ^ 2 / (2 + 1 / (N : ℝ) ^ 4)) (bdκ N * sigN N / lt2θ N)) ≤
      Real.exp (-(4 * N)) := by
    refine bd_exp_min_le hAB (min_le_min ?_ ?_)
    · unfold bdA
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (bdκ N)]
    · unfold bdB
      exact div_le_div_of_nonneg_left (by positivity) hθ (by linarith)
  have h4N : (4 : ℝ) * N ≤ (N : ℝ) ^ 3 := by
    have h4 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hcube : Real.exp (-((N : ℝ) ^ 3)) ≤ Real.exp (-(4 * N)) := Real.exp_le_exp.2 (by linarith)
  simp only [card_singleton, Nat.choose_one_right, Nat.cast_one, pow_one, one_mul, one_pow]
  linarith [hBs.1, hBs.2]

/-- Tail of the level statistic `Σ_v P_ns(v)(y_{v,i} - 2/3)`. -/
lemma bd_lev0_tail (hbias : Real.exp (lt2x1 * N) * (2 / 3 : ℝ) ^ N ≤ Real.exp (-(N : ℝ) / 7) / 2) (i : Fin N) :
    cubeM N {w | Real.exp (-(N : ℝ) / 7) ≤ |∑ v, bdg i (w v)|} ≤ ENNReal.ofReal (2 * Real.exp (-(4 * N))) := by
  have hθ : 0 < lt2θ N := Real.exp_pos _
  have hσ : 0 < sigN N := by unfold sigN; positivity
  set lam := Real.exp (-(N : ℝ) / 7) with hlam
  have hlam0 : 0 < lam := Real.exp_pos _
  have h := bd_level_tail i (ε := lam / 2) (by positivity) hbias
  rw [show 2 * (lam / 2) = lam by ring] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hx : Real.exp (-min ((lam / 2) ^ 2 / (4 * (2 / 3 : ℝ) ^ N)) (lam / 2 / (2 * (2 * lt2θ N)))) ≤
      Real.exp (-(4 * N)) := by
    refine bd_exp_min_le hAB (min_le_min ?_ ?_)
    · have e1 : bdA N = lam ^ 2 / (64 * sigN N ^ 2) := by
        unfold bdA bdκ; rw [← hlam]; field_simp; ring
      have e2 : (lam / 2) ^ 2 / (4 * (2 / 3 : ℝ) ^ N) = lam ^ 2 / (16 * sigN N ^ 2) := by
        rw [← lt2_sigN_sq]; field_simp; ring
      rw [e1, e2]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith [sq_nonneg (sigN N)])
    · unfold bdB
      rw [bdκ_sig, ← hlam]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  linarith

end Tails

/-! ### The probability of the light level event -/

/-- **Each level statistic fails with probability `≤ 40 e^{-4N}`**, eventually, uniformly in `(i, R, T)`. -/
theorem bd_stat_ev : ∀ᶠ N : ℕ in atTop, ∀ α : Fin N × Finset (Fin N) × Finset (Fin N),
    cubeM N {w | Real.exp (-(N : ℝ) / 7) < |lt2G w α.1 α.2.1 α.2.2 - bdC α.2.1 α.2.2 * bdZns w|} ≤
      ENNReal.ofReal (40 * Real.exp (-(4 * N))) := by
  have hx0 := x0_gt
  filter_upwards [bd_AB_ev, lt2_ev_kind, lt2_B_small, eventually_ge_atTop 2,
    bd_exp_ev (c := x0 - 1 / 400 - 1 / 7) (δ := 1 / 2) (by linarith) (by norm_num)]
    with N hAB hev hBs hN2 hbias' α
  obtain ⟨-, hN8, -⟩ := hev
  obtain ⟨i, R, T⟩ := α
  simp only
  set lam := Real.exp (-(N : ℝ) / 7) with hlam
  have hq : bdκ N * sigN N = lam / 4 := bdκ_sig
  have hlam0 : 0 < lam := Real.exp_pos _
  have hE := Real.exp_pos (-(4 * (N : ℝ)))
  have hmT : ∀ {T : Finset (Fin N)}, T.Nonempty →
      cubeM N {w | lam / 4 ≤ |lt2mT w T|} ≤ ENNReal.ofReal (2 * Real.exp (-(4 * N))) := fun hT => by
    have := bd_mT_tail hAB hT; rwa [hq] at this
  have hOt : ∀ {T : Finset (Fin N)}, T.Nonempty →
      cubeM N {w | lam / 4 ≤ |lt2Ot w (i, T)|} ≤ ENNReal.ofReal (2 * Real.exp (-(4 * N))) := fun hT => by
    have := bd_Ot_tail hAB i hT; rwa [hq] at this
  have hbias : Real.exp (lt2x1 * N) * (2 / 3 : ℝ) ^ N ≤ lam / 2 := by
    have e1 : (2 / 3 : ℝ) ^ N = Real.exp (-(2 * x0 * N)) := by
      rw [← lt2_sigN_sq, sigN_eq_exp, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [e1, ← Real.exp_add]
    have e2 : lt2x1 * (N : ℝ) + -(2 * x0 * N) = -((x0 - 1 / 400 - 1 / 7) * N) + -(N : ℝ) / 7 := by
      unfold lt2x1; ring
    rw [e2, Real.exp_add]
    have := mul_le_mul_of_nonneg_right hbias' (Real.exp_pos (-(N : ℝ) / 7)).le
    linarith
  by_cases hR : R = ∅
  · subst hR
    by_cases hT : T = ∅
    · -- the level statistic
      subst hT
      have hc : bdC (∅ : Finset (Fin N)) ∅ = 2 / 3 := by unfold bdC; simp
      rw [hc]
      refine (measure_mono fun w hw => ?_).trans ((bd_lev0_tail hAB hbias i).trans
        (ENNReal.ofReal_le_ofReal (by linarith)))
      simp only [Set.mem_setOf_eq] at hw ⊢
      rw [← bd_G_empty_empty]; exact hw.le
    · -- `G = (3/4) m_T + Õ`
      have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.2 hT
      have hc : bdC (∅ : Finset (Fin N)) T = 0 := by unfold bdC; rw [if_neg hT]
      rw [hc]
      have hsub : {w : Param N | lam < |lt2G w i ∅ T - 0 * bdZns w|} ⊆
          {w | lam / 4 ≤ |lt2mT w T|} ∪ {w | lam / 4 ≤ |lt2Ot w (i, T)|} := by
        intro w hw
        simp only [Set.mem_setOf_eq, zero_mul, sub_zero, lt2G_empty] at hw
        by_contra hcon
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
        obtain ⟨hc1, hc2⟩ := hcon
        have h1 : |3 / 4 * lt2mT w T + lt2Ot w (i, T)| ≤ 3 / 4 * |lt2mT w T| + |lt2Ot w (i, T)| := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
        linarith
      exact (measure_mono hsub).trans (bd_union2 (by positivity) (by positivity) (hmT hTne)
        (hOt hTne) (by linarith))
  · -- `R ≠ ∅`: `G = (1/2) m_T + Ñ⁰ + Ñ¹` with the class `{min R}`
    have hRne : R.Nonempty := Finset.nonempty_iff_ne_empty.2 hR
    have hshift := fun w : Param N => lt2G_shift w (bdLam R) i R T
    have hN0t := bd_N0_tail hAB hN8 hN2 hBs true i hRne T
    have hN0f := bd_N0_tail hAB hN8 hN2 hBs false i hRne T
    rw [hq] at hN0t hN0f
    by_cases hT : T = ∅
    · subst hT
      have hc : bdC R (∅ : Finset (Fin N)) = 1 / 2 := by unfold bdC; simp [hR]
      rw [hc]
      have hsub : {w : Param N | lam < |lt2G w i R ∅ - 1 / 2 * bdZns w|} ⊆
          {w | lam / 4 ≤ |lt2N0 (bdLam R) true w (i, R, ∅)|} ∪
            {w | lam / 4 ≤ |lt2N0 (bdLam R) false w (i, R, ∅)|} := by
        intro w hw
        simp only [Set.mem_setOf_eq] at hw
        rw [hshift w, lt2mT_empty] at hw
        by_contra hcon
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
        have h1 : |1 / 2 * bdZns w + lt2N0 (bdLam R) true w (i, R, ∅) + lt2N0 (bdLam R) false w (i, R, ∅) -
            1 / 2 * bdZns w| ≤ |lt2N0 (bdLam R) true w (i, R, ∅)| + |lt2N0 (bdLam R) false w (i, R, ∅)| := by
          rw [show 1 / 2 * bdZns w + lt2N0 (bdLam R) true w (i, R, ∅) + lt2N0 (bdLam R) false w (i, R, ∅) -
            1 / 2 * bdZns w = lt2N0 (bdLam R) true w (i, R, ∅) + lt2N0 (bdLam R) false w (i, R, ∅) by ring]
          exact abs_add_le _ _
        obtain ⟨hc1, hc2⟩ := hcon
        linarith
      exact (measure_mono hsub).trans (bd_union2 (by positivity) (by positivity) hN0t hN0f (by linarith))
    · have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.2 hT
      have hc : bdC R T = 0 := by unfold bdC; rw [if_neg hT]
      rw [hc]
      have hsub : {w : Param N | lam < |lt2G w i R T - 0 * bdZns w|} ⊆
          ({w | lam / 4 ≤ |lt2mT w T|} ∪ {w | lam / 4 ≤ |lt2N0 (bdLam R) true w (i, R, T)|}) ∪
            {w | lam / 4 ≤ |lt2N0 (bdLam R) false w (i, R, T)|} := by
        intro w hw
        simp only [Set.mem_setOf_eq, zero_mul, sub_zero] at hw
        rw [hshift w] at hw
        by_contra hcon
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
        have h1 : |1 / 2 * lt2mT w T + lt2N0 (bdLam R) true w (i, R, T) + lt2N0 (bdLam R) false w (i, R, T)| ≤
            1 / 2 * |lt2mT w T| + |lt2N0 (bdLam R) true w (i, R, T)| +
              |lt2N0 (bdLam R) false w (i, R, T)| := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (le_of_eq ?_) le_rfl)) le_rfl)
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hcon
        linarith
      refine (measure_mono hsub).trans (bd_union2 (by positivity) (by positivity)
        (bd_union2 (by positivity) (by positivity) (hmT hTne) hN0t le_rfl) hN0f ?_)
      linarith

/-- **The light level event holds off probability `e^{-3N}`.** -/
theorem bd_lev_ev : ∀ᶠ N : ℕ in atTop,
    cubeM N {w : Param N | ¬ bdLev (Real.exp (-(N : ℝ) / 7)) w} ≤ ENNReal.ofReal (Real.exp (-(3 * N))) := by
  filter_upwards [bd_stat_ev, cr_ev_poly_exp 7 (Real.log 40) (δ := 1) (by norm_num)] with N hS hpoly
  rw [Real.exp_log (by norm_num)] at hpoly
  have hsub : {w : Param N | ¬ bdLev (Real.exp (-(N : ℝ) / 7)) w} ⊆ ⋃ α ∈ bdIdx N,
      {w | Real.exp (-(N : ℝ) / 7) < |lt2G w α.1 α.2.1 α.2.2 - bdC α.2.1 α.2.2 * bdZns w|} := by
    intro w hw
    simp only [bdLev, Set.mem_setOf_eq, not_forall, not_le, exists_prop] at hw
    obtain ⟨α, hα, h⟩ := hw
    exact Set.mem_biUnion hα h
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ α ∈ bdIdx N, cubeM N {w | Real.exp (-(N : ℝ) / 7) <
        |lt2G w α.1 α.2.1 α.2.2 - bdC α.2.1 α.2.2 * bdZns w|}
      ≤ ∑ _α ∈ bdIdx N, ENNReal.ofReal (40 * Real.exp (-(4 * N))) := Finset.sum_le_sum fun α _ => hS α
    _ = ENNReal.ofReal ((bdIdx N).card * (40 * Real.exp (-(4 * N)))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (Real.exp (-(3 * N))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hc : ((bdIdx N).card : ℝ) ≤ ((N : ℝ) + 1) ^ 7 := by exact_mod_cast bdIdx_card
        have hE := Real.exp_pos (-(4 * (N : ℝ)))
        have h1 : ((bdIdx N).card : ℝ) * (40 * Real.exp (-(4 * N))) ≤
            ((N : ℝ) + 1) ^ 7 * 40 * Real.exp (-(4 * N)) := by nlinarith
        have h2 : ((N : ℝ) + 1) ^ 7 * 40 * Real.exp (-(4 * N)) ≤ Real.exp (1 * N) * Real.exp (-(4 * N)) :=
          mul_le_mul_of_nonneg_right hpoly hE.le
        have h3 : Real.exp (1 * N) * Real.exp (-(4 * N)) = Real.exp (-(3 * N)) := by
          rw [← Real.exp_add]; ring_nf
        linarith

/-! ### The deterministic band -/

lemma bd_sum_bdC {S : Finset (Fin N)} (hS : S.card = 3) :
    ∑ R ∈ S.powerset, bdC R (∅ : Finset (Fin N)) = 25 / 6 := by
  have h : ∀ R : Finset (Fin N), bdC R ∅ = 1 / 2 + (if R = ∅ then 1 / 6 else 0) := fun R => by
    unfold bdC; rw [if_pos rfl]; split_ifs <;> norm_num
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_powerset, hS, Finset.sum_ite_eq',
    if_pos (Finset.empty_mem_powerset S)]
  norm_num

/-- Indices inside a set of size `≤ 3` belong to `bdIdx`. -/
lemma bd_mem_idx {S : Finset (Fin N)} (hS : S.card ≤ 3) {i : Fin N} {R T : Finset (Fin N)} (hi : i ∈ S)
    (hR : R ⊆ S) (hT : T ⊆ S) : (i, R, T) ∈ bdIdx N := by
  unfold bdIdx
  rw [mem_filter]
  exact ⟨mem_univ _, (card_le_card (insert_subset hi (union_subset hR hT))).trans hS⟩

/-- Reading the level event at an index inside a set of size `≤ 3`. -/
lemma bd_lev_apply {lam : ℝ} {w : Param N} (hlev : bdLev lam w) {S : Finset (Fin N)} (hS : S.card ≤ 3)
    {i : Fin N} {R T : Finset (Fin N)} (hi : i ∈ S) (hR : R ⊆ S) (hT : T ⊆ S) :
    |lt2G w i R T - bdC R T * bdZns w| ≤ lam :=
  hlev (i, R, T) (bd_mem_idx hS hi hR hT)

/-- **Lemma D1 at the level**: `|NumNs(S, t, i) - a₃ Z_ns| ≤ 8λ` on `bdLev λ` (`|S| = 3`, `i ∈ S`). -/
theorem bd_light_level (w : Param N) {S : Finset (Fin N)} (hS : S.card = 3) {lam : ℝ} (hlev : bdLev lam w)
    (t : State N) {i : Fin N} (hi : i ∈ S) : |lt2NumNs w S t i - lvK 3 * bdZns w| ≤ 8 * lam := by
  have h2 : (2 : ℝ) ^ S.card = 8 := by rw [hS]; norm_num
  have hlvK : lvK 3 = 25 / 48 := by unfold lvK; norm_num
  have hkey : lvK 3 * bdZns w = (∑ R ∈ S.powerset, ∑ T ∈ S.powerset,
      lt2Chi T (lt2Xor t R) * (bdC R T * bdZns w)) / 2 ^ S.card := by
    have hin : ∀ R ∈ S.powerset, ∑ T ∈ S.powerset, lt2Chi T (lt2Xor t R) * (bdC R T * bdZns w) =
        bdC R ∅ * bdZns w := by
      intro R _
      rw [Finset.sum_eq_single_of_mem ∅ (empty_mem_powerset S) fun T _ hT => by
        unfold bdC; rw [if_neg hT]; ring]
      rw [lt2Chi_empty, one_mul]
    rw [Finset.sum_congr rfl hin, ← Finset.sum_mul, bd_sum_bdC hS, h2, hlvK]; ring
  rw [lt2_D1, hkey, ← sub_div, ← Finset.sum_sub_distrib, h2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8),
    div_le_iff₀ (by norm_num : (0 : ℝ) < 8)]
  have hS8 : (S.powerset.card : ℝ) = 8 := by rw [Finset.card_powerset, hS]; norm_num
  calc |∑ R ∈ S.powerset, (∑ T ∈ S.powerset, lt2Chi T (lt2Xor t R) * lt2G w i R T -
        ∑ T ∈ S.powerset, lt2Chi T (lt2Xor t R) * (bdC R T * bdZns w))|
      ≤ ∑ R ∈ S.powerset, |∑ T ∈ S.powerset, lt2Chi T (lt2Xor t R) * lt2G w i R T -
        ∑ T ∈ S.powerset, lt2Chi T (lt2Xor t R) * (bdC R T * bdZns w)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _R ∈ S.powerset, ∑ _T ∈ S.powerset, lam := by
        refine Finset.sum_le_sum fun R hR => ?_
        rw [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun T hT => ?_)
        rw [← mul_sub, abs_mul, lt2Chi_abs, one_mul]
        exact bd_lev_apply hlev hS.le hi (mem_powerset.1 hR) (mem_powerset.1 hT)
    _ = lam * 8 * 8 := by rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hS8]; ring
    _ = 8 * lam * 8 := by ring

/-- `P(v) = P_ns(v) + P(v) 1{v ∈ Sp}`. -/
lemma bd_Pw_split (w : Param N) (v : State N) :
    Pw w v = lt2gNs (w v) + (if v ∈ lt2Sp w then Pw w v else 0) := by
  have hSp : v ∈ lt2Sp w ↔ ¬ lt2x1 * N < ∑ j, -Real.log (clamp01 (w v j)) := by
    simp only [lt2Sp, mem_filter, mem_univ, true_and, not_lt]; rfl
  unfold lt2gNs
  by_cases h : lt2x1 * N < ∑ j, -Real.log (clamp01 (w v j))
  · rw [if_pos h, if_neg (fun h' => (hSp.1 h') h), add_zero]; rfl
  · rw [if_neg h, if_pos (hSp.2 h), zero_add]

/-- **The deterministic band** for one numerator: the light part is within `8λ` of `a₃ Z_ns`, the special rows add
at most `|Sp| P(tc)`. -/
theorem bd_band_det (w : Param N) {S : Finset (Fin N)} (hS : S.card = 3) {lam : ℝ}
    (hlev : bdLev lam w) (t : State N) {i : Fin N} (hi : i ∈ S) :
    |Num w S S t i - lvK 3 * Zs w| ≤ (lt2Sp w).card * Pw w (tcRow w) + 8 * lam := by
  have hsplit : ∀ f : State N → ℝ, ∑ v, f v * Pw w v = ∑ v, f v * lt2gNs (w v) + ∑ v ∈ lt2Sp w, f v * Pw w v := by
    intro f
    have e : ∀ v, f v * Pw w v = f v * lt2gNs (w v) + (if v ∈ lt2Sp w then f v * Pw w v else 0) := by
      intro v
      conv_lhs => rw [bd_Pw_split w v]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun v _ => e v, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter]
  have hNum : Num w S S t i = lt2NumNs w S t i + ∑ v ∈ lt2Sp w, clamp01 (w (merge S t v) i) * Pw w v := by
    rw [prof_Num_full, hsplit (fun v => clamp01 (w (merge S t v) i))]
    rfl
  have hZ : Zs w = bdZns w + ∑ v ∈ lt2Sp w, Pw w v := by
    have := hsplit (fun _ => 1)
    simp only [one_mul] at this
    exact this
  have hlvK : lvK 3 = 25 / 48 := by unfold lvK; norm_num
  have hL := bd_light_level w hS hlev t hi
  have hH : |∑ v ∈ lt2Sp w, clamp01 (w (merge S t v) i) * Pw w v - lvK 3 * ∑ v ∈ lt2Sp w, Pw w v| ≤
      (lt2Sp w).card * Pw w (tcRow w) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ v ∈ lt2Sp w, |clamp01 (w (merge S t v) i) * Pw w v - lvK 3 * Pw w v|
        ≤ ∑ _v ∈ lt2Sp w, Pw w (tcRow w) := Finset.sum_le_sum fun v _ => by
          rw [← sub_mul, abs_mul, abs_of_nonneg (Pw_nonneg w v)]
          have h1 : |clamp01 (w (merge S t v) i) - lvK 3| ≤ 1 := by
            rw [hlvK, abs_le]
            constructor <;> linarith [clamp01_nonneg (w (merge S t v) i), clamp01_le_one (w (merge S t v) i)]
          calc |clamp01 (w (merge S t v) i) - lvK 3| * Pw w v ≤ 1 * Pw w v :=
                mul_le_mul_of_nonneg_right h1 (Pw_nonneg w v)
            _ ≤ Pw w (tcRow w) := by rw [one_mul]; exact Pw_le_tcRow w v
      _ = (lt2Sp w).card * Pw w (tcRow w) := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [hNum, hZ]
  calc |lt2NumNs w S t i + ∑ v ∈ lt2Sp w, clamp01 (w (merge S t v) i) * Pw w v -
        lvK 3 * (bdZns w + ∑ v ∈ lt2Sp w, Pw w v)|
      = |(lt2NumNs w S t i - lvK 3 * bdZns w) + (∑ v ∈ lt2Sp w, clamp01 (w (merge S t v) i) * Pw w v -
          lvK 3 * ∑ v ∈ lt2Sp w, Pw w v)| := by ring_nf
    _ ≤ |lt2NumNs w S t i - lvK 3 * bdZns w| + |∑ v ∈ lt2Sp w, clamp01 (w (merge S t v) i) * Pw w v -
          lvK 3 * ∑ v ∈ lt2Sp w, Pw w v| := abs_add_le _ _
    _ ≤ (lt2Sp w).card * Pw w (tcRow w) + 8 * lam := by linarith

/-- The band width `η = 11 P(tc) + 8 e^{-N/7}`. -/
noncomputable def bdEta (w : Param N) : ℝ := 11 * Pw w (tcRow w) + 8 * Real.exp (-(N : ℝ) / 7)

lemma bdEta_nonneg (w : Param N) : 0 ≤ bdEta w := by
  unfold bdEta; have := Pw_nonneg w (tcRow w); positivity

/-- **The band, all `Y ⊆ S`** (`|Sp| < 12`, on `bdLev (e^{-N/7})`): the `hlev` input of `lt3_TCprime`. -/
theorem bd_hlev (w : Param N) (hlev : bdLev (Real.exp (-(N : ℝ) / 7)) w) (hSp : (lt2Sp w).card < 12)
    {a b c : Fin N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ Y ⊆ ({a, b, c} : Finset (Fin N)), ∀ t', ∀ i ∈ ({a, b, c} : Finset (Fin N)),
      |Num w {a, b, c} Y t' i - lvK 3 * Zs w| ≤ bdEta w := by
  refine pk_hlev_of_full fun t i hi => ?_
  have hS : ({a, b, c} : Finset (Fin N)).card = 3 := by
    rw [card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]
  refine (bd_band_det w hS hlev t hi).trans ?_
  unfold bdEta
  have h11 : ((lt2Sp w).card : ℝ) ≤ 11 := by exact_mod_cast Nat.lt_succ_iff.1 hSp
  have hP := Pw_nonneg w (tcRow w)
  nlinarith

/-- **`η² ≤ (t/10^6) P(tc) a₃ Zs`** eventually, on `{Zs ≥ 1/2, Lσ_N ≤ β, P(tc) ≤ e^{-e^{-3}N}}`. -/
theorem bd_eta_sq {t L : ℝ} (ht : 0 < t) (hL : 0 < L) : ∀ᶠ N : ℕ in atTop, ∀ w : Param N,
    1 / 2 ≤ Zs w → L * sigN N ≤ betaW w → Pw w (tcRow w) ≤ Real.exp (-(Real.exp (-3) * N)) →
    bdEta w ^ 2 ≤ t / 10 ^ 6 * Pw w (tcRow w) * (lvK 3 * Zs w) := by
  have hx0 := x0_lt
  filter_upwards [bd_exp_ev (c := Real.exp (-3)) (δ := t * 25 / (192 * 10 ^ 6 * 242)) (Real.exp_pos _)
      (by positivity),
    bd_exp_ev (c := 2 / 7 - x0) (δ := t * L * 25 / (192 * 2 * 10 ^ 6 * 128)) (by linarith) (by positivity)]
    with N h1 h2 w hZ hβ hP
  set σ := Pw w (tcRow w) with hσdef
  set Z := Zs w with hZdef
  have hσ0 : 0 ≤ σ := Pw_nonneg w _
  have hZpos : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hlvK : lvK 3 = 25 / 48 := by unfold lvK; norm_num
  set e := Real.exp (-(N : ℝ) / 7) with he
  have hsig : sigN N = Real.exp (-(x0 * N)) := sigN_eq_exp N
  have hσβ : betaW w * Z = σ := by unfold betaW; exact div_mul_cancel₀ _ hZpos.ne'
  have hσlow : L * sigN N * Z ≤ σ := by
    rw [← hσβ]; exact mul_le_mul_of_nonneg_right hβ hZpos.le
  -- `η² ≤ 242 σ² + 128 e²`
  have hsq : bdEta w ^ 2 ≤ 242 * σ ^ 2 + 128 * e ^ 2 := by
    unfold bdEta; rw [← hσdef, ← he]; nlinarith [sq_nonneg (11 * σ - 8 * e)]
  -- the heavy part
  have hA : 242 * σ ^ 2 ≤ t / (2 * 10 ^ 6) * σ * (lvK 3 * Z) := by
    rw [hlvK]
    have hσs : σ ≤ t * 25 / (192 * 10 ^ 6 * 242) := hP.trans h1
    have k : 242 * σ ≤ t / (2 * 10 ^ 6) * (25 / 48 * Z) := by
      have : t * 25 / (192 * 10 ^ 6 * 242) * 242 ≤ t / (2 * 10 ^ 6) * (25 / 48 * Z) := by
        rw [show t * 25 / (192 * 10 ^ 6 * 242) * 242 = t / (2 * 10 ^ 6) * (25 / 48 * (1 / 2)) by ring]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have := mul_le_mul_of_nonneg_left k hσ0
    nlinarith
  -- the light part
  have hB : 128 * e ^ 2 ≤ t / (2 * 10 ^ 6) * σ * (lvK 3 * Z) := by
    rw [hlvK]
    have he2 : e ^ 2 = Real.exp (-((2 / 7 - x0) * N)) * Real.exp (-(x0 * N)) := by
      rw [he, sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hlow : L * Real.exp (-(x0 * N)) * (1 / 2) * (25 / 96) ≤ σ * (25 / 48 * Z) := by
      have k1 : L * Real.exp (-(x0 * N)) * (1 / 2) ≤ σ := by
        rw [← hsig]
        calc L * sigN N * (1 / 2) ≤ L * sigN N * Z :=
              mul_le_mul_of_nonneg_left hZ (by unfold sigN; positivity)
          _ ≤ σ := hσlow
      have k2 : (25 / 96 : ℝ) ≤ 25 / 48 * Z := by linarith
      exact mul_le_mul k1 k2 (by norm_num) hσ0
    have hE := Real.exp_pos (-(x0 * N))
    have k3 : 128 * e ^ 2 ≤ 128 * (t * L * 25 / (192 * 2 * 10 ^ 6 * 128)) * Real.exp (-(x0 * N)) := by
      rw [he2]
      have := mul_le_mul_of_nonneg_right h2 hE.le
      nlinarith
    have k4 : 128 * (t * L * 25 / (192 * 2 * 10 ^ 6 * 128)) * Real.exp (-(x0 * N)) =
        t / (2 * 10 ^ 6) * (L * Real.exp (-(x0 * N)) * (1 / 2) * (25 / 96)) := by ring
    have k5 : t / (2 * 10 ^ 6) * (L * Real.exp (-(x0 * N)) * (1 / 2) * (25 / 96)) ≤
        t / (2 * 10 ^ 6) * (σ * (25 / 48 * Z)) := mul_le_mul_of_nonneg_left hlow (by positivity)
    nlinarith
  have hsum : t / (2 * 10 ^ 6) * σ * (lvK 3 * Z) + t / (2 * 10 ^ 6) * σ * (lvK 3 * Z) =
      t / 10 ^ 6 * σ * (lvK 3 * Z) := by ring
  linarith

/-! ### The good event and its probability -/

/-- **The band event**: no very heavy row, and the light level event at `λ = e^{-N/7}`. -/
def bdGood (w : Param N) : Prop := (∀ r, Real.exp (-3) * N < XW w r) ∧ bdLev (Real.exp (-(N : ℝ) / 7)) w

/-- **The band event fails with probability `≤ e^{-1.2N}`.** -/
theorem bd_not_good_ev : ∀ᶠ N : ℕ in atTop,
    cubeM N {w : Param N | ¬ bdGood w} ≤ ENNReal.ofReal (Real.exp (-(6 / 5 * N))) := by
  filter_upwards [bd_lev_ev, eventually_ge_atTop 1, bd_exp_ev (c := 1 / 10) (δ := 1 / 2) (by norm_num) (by norm_num)]
    with N hL hN1 h10
  have hN : 0 < N := hN1
  have hsub : {w : Param N | ¬ bdGood w} ⊆ {w | ∃ r, XW w r ≤ Real.exp (-3) * N} ∪
      {w | ¬ bdLev (Real.exp (-(N : ℝ) / 7)) w} := by
    intro w hw
    simp only [bdGood, Set.mem_setOf_eq, not_and_or, not_forall, not_lt] at hw
    rcases hw with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine (measure_mono hsub).trans (bd_union2 (Real.exp_pos _).le (Real.exp_pos _).le (bd_heavy_rows hN) hL ?_)
  have hl2 := Real.log_two_lt_d9
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have e1 : Real.exp (-((2 - Real.log 2) * N)) ≤ Real.exp (-(13 / 10 * N)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have e2 : Real.exp (-(3 * (N : ℝ))) ≤ Real.exp (-(13 / 10 * N)) := Real.exp_le_exp.2 (by nlinarith)
  have e3 : Real.exp (-(13 / 10 * (N : ℝ))) = Real.exp (-(1 / 10 * N)) * Real.exp (-(6 / 5 * N)) := by
    rw [← Real.exp_add]; ring_nf
  have e4 := Real.exp_pos (-(6 / 5 * (N : ℝ)))
  have e5 : Real.exp (-(1 / 10 * (N : ℝ))) * Real.exp (-(6 / 5 * N)) ≤ 1 / 2 * Real.exp (-(6 / 5 * N)) :=
    mul_le_mul_of_nonneg_right h10 e4.le
  linarith

/-- **The band (items (a) and (d) assembled)**: for `t, L > 0`, eventually, on `bdGood ∩ {Zs ≥ 1/2, Lσ_N ≤ β,
|Sp| < 12}`, every triple has the band `|Num - a₃ Zs| ≤ η` (all `Y ⊆ S`), `0 ≤ η`, `η² ≤ (t/10^6) P(tc) a₃ Zs`,
and `P(tc) ≥ e^{-(x₁ - 1/800)N}`. -/
theorem bd_band {t L : ℝ} (ht : 0 < t) (hL : 0 < L) : ∀ᶠ N : ℕ in atTop, ∀ w : Param N, bdGood w →
    1 / 2 ≤ Zs w → L * sigN N ≤ betaW w → (lt2Sp w).card < 12 →
    Real.exp (-((lt2x1 - 1 / 800) * N)) ≤ Pw w (tcRow w) ∧ 0 ≤ bdEta w ∧
      bdEta w ^ 2 ≤ t / 10 ^ 6 * Pw w (tcRow w) * (lvK 3 * Zs w) ∧
      ∀ a b c : Fin N, a ≠ b → a ≠ c → b ≠ c →
        ∀ Y ⊆ ({a, b, c} : Finset (Fin N)), ∀ t', ∀ i ∈ ({a, b, c} : Finset (Fin N)),
          |Num w {a, b, c} Y t' i - lvK 3 * Zs w| ≤ bdEta w := by
  filter_upwards [bd_Ptc_ge hL, bd_eta_sq ht hL] with N hP hE w hG hZ hβ hSp
  exact ⟨hP w hZ hβ, bdEta_nonneg w, hE w hZ hβ (bd_Pw_le_of_light hG.1 _),
    fun a b c hab hac hbc => bd_hlev w hG.2 hSp hab hac hbc⟩

end Census
end IIT
