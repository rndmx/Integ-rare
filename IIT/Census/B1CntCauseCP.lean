/-
Census, B1, W14 work package WP2 (cause side), part 3 (sub-package 2A): positivity at `(univ, r0)`.

* bridges of `causeFwd`, `partCauseFwd`, `causeRep` at `T = tpmOf (flipP s w)` to subcube means;
* `cs_cp_ratio` (W5 Lemma CP + PS, W13-cause G5: the three partition types; G1: the floor from
  `lowU ⊆ K`): every partition of `(M, univ)` has `LR/cc ≥ e^{-N/200}/m`;
* `cs_normC` (FE4b + the Sens rows), `cs_causeRep_univ_r0_ge`, `cs_phiCat_univ_r0_ge`.
Numeric inputs are explicit hypotheses (discharged eventually in `B1CntCauseFin.lean`).
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §7.  No `sorry`.
-/
import IIT.Census.B1CntCauseCut

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### Bridges -/

lemma cs_causeFwd_eq (s : State N) (w : Param N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) : causeFwd (tpmOf (flipP s w)) Z z M s = ∏ i ∈ M, subMean w Z z i := by
  unfold causeFwd effRep
  exact prod_congr rfl fun i _ => effUnit_flipP_self s w Z z i

lemma cs_partCauseFwd_eq (s : State N) (w : Param N) (Z : Finset (Fin N)) (z : State N)
    (M : Finset (Fin N)) (θ : Partition N M Z) :
    partCauseFwd (tpmOf (flipP s w)) Z z M s θ = ∏ i ∈ M, subMean w (θ.causePart i) z i := by
  unfold partCauseFwd
  exact prod_congr rfl fun i _ => effUnit_flipP_self s w _ z i

lemma cs_causeFwd_univ_eq (s : State N) (w : Param N) (z : State N) (M : Finset (Fin N)) :
    causeFwd (tpmOf (flipP s w)) univ z M s = ∏ i ∈ M, clamp01 (w z i) := by
  rw [cs_causeFwd_eq]; exact prod_congr rfl fun i _ => cs_subMean_univ w z i

lemma cs_causeRep_univ_eq (T : UnitTPM N) (z : State N) (M : Finset (Fin N)) (m : State N) :
    causeRep T univ z M m = causeFwd T univ z M m / ∑ t, causeFwd T univ t M m := by
  unfold causeRep uncCauseFwd avgOverStates
  rw [card_univ, Fintype.card_fin, mul_div_cancel₀ _ (by positivity)]

lemma cs_logb_ratio {w : Param N} (hw : w ∈ openCube N) (M : Finset (Fin N))
    (P : Fin N → Finset (Fin N)) (z : State N) :
    Real.logb 2 ((∏ i ∈ M, clamp01 (w z i)) / ∏ i ∈ M, subMean w (P i) z i) =
      (∑ i ∈ M, Real.log (clamp01 (w z i) / subMean w (P i) z i)) / Real.log 2 := by
  rw [← prod_div_distrib, Real.logb, Real.log_prod]
  intro i _
  exact (div_pos (cs_clamp_pos hw z i) (cs_subMean_pos hw _ z i)).ne'

/-! ### The ratio at `(univ, r0)` -/

lemma cs_card_M {K : Finset (Fin N)} (hK : K.card = dX N) : (univ \ K).card = N - dX N := by
  rw [card_univ_sdiff, Fintype.card_fin, hK]

lemma cs_mX_ge (hN : 10000 ≤ N) : (N : ℝ) / 2 ≤ mX N := by
  have h1 : 1 ≤ N := by omega
  rw [cs_mX_eq h1]
  have := cs_dX_le N
  have hN' : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

/-- **`cp_ratio`** (Phi level): every partition of `(univ \ K, univ)` at `r0` has
`LR/cc ≥ e^{-N/200}/m`. -/
theorem cs_cp_ratio {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    (hg : GoodW3 N s r0 x σ w) (hfr : CountFreshX N s r0 w) (hw : w ∈ openCube N)
    {K : Finset (Fin N)} (hK : K ∈ famX3 N s r0 x σ w)
    (hN : 10000 ≤ N) (hslT : slT N ≤ N / 1000) (ha : Real.exp (-((N : ℝ) / 200)) ≤ 1 / 2000)
    (heps : epsN N ≤ Real.exp (-((N : ℝ) / 200)) / 100)
    (hJ3 : 3 * JC N + 3 < N) (hD2 : 2 * D0C N ≤ N)
    (hbig : ∀ (A : Finset (Fin N)) (t : State N) (i : Fin N), A.card + D0C N ≤ N →
      subMean w A t i ≤ cX)
    (hcol : ∀ (t : State N) (i : Fin N), |subMean w ∅ t i - 1 / 2| ≤ epsN N)
    (θ : Partition N (univ \ K) univ) :
    Real.exp (-((N : ℝ) / 200)) / mX N ≤
      Real.logb 2 (causeFwd (tpmOf (flipP s w)) univ r0 (univ \ K) s /
        partCauseFwd (tpmOf (flipP s w)) univ r0 (univ \ K) s θ) /
        (cutCount (univ \ K) univ θ : ℝ) := by
  revert θ
  set M := univ \ K with hMdef
  intro θ
  set a := Real.exp (-((N : ℝ) / 200)) with hadef
  have hapos : 0 < a := Real.exp_pos _
  have hNr : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < N := by omega
  have hU : (univ : Finset (Fin N)).Nonempty := ⟨⟨0, hNpos⟩, mem_univ _⟩
  have hKc := famX3_card hK
  have hMc : M.card = N - dX N := cs_card_M hKc
  have hm := cs_mX_ge hN
  have hmpos : 0 < mX N := by linarith
  have hl2 := cs_log_two_lt
  have hl2' := cs_log_two_gt
  have hl2pos : 0 < Real.log 2 := by linarith
  -- the log-ratio and the cut count through the cause parts
  set P : Fin N → Finset (Fin N) := fun i => θ.causePart i with hP
  set t : Fin N → ℝ := fun i => Real.log (clamp01 (w r0 i) / subMean w (P i) r0 i) with ht
  have hLR : Real.logb 2 (causeFwd (tpmOf (flipP s w)) univ r0 M s /
      partCauseFwd (tpmOf (flipP s w)) univ r0 M s θ) = (∑ i ∈ M, t i) / Real.log 2 := by
    rw [cs_causeFwd_univ_eq, cs_partCauseFwd_eq, cs_logb_ratio hw]
  have hcc : (cutCount M univ θ : ℝ) = ∑ i ∈ M, ((N : ℝ) - (P i).card) := by
    rw [cutCount_eq_causeSum, card_univ, Fintype.card_fin]
    push_cast
    refine sum_congr rfl fun i _ => ?_
    rw [Nat.cast_sub (by simpa using card_le_univ (P i))]
  have hccpos : (0 : ℝ) < cutCount M univ θ := Nat.cast_pos.2 (cutCount_pos hU θ)
  have hccle : (cutCount M univ θ : ℝ) ≤ mX N * N := by
    rw [hcc]
    calc ∑ i ∈ M, ((N : ℝ) - (P i).card) ≤ ∑ _i ∈ M, (N : ℝ) :=
          sum_le_sum fun i _ => by have := Nat.cast_nonneg (α := ℝ) (P i).card; linarith
      _ = mX N * N := by rw [sum_const, nsmul_eq_mul, hMc]; rfl
  rw [hLR, div_div]
  -- the floor on `M`
  have hfloor : ∀ i ∈ M, 1 / 2 + a ≤ clamp01 (w r0 i) := fun i hi =>
    mem_famX3_floor hK (mem_sdiff.1 hi).2
  by_cases hB : ∃ i0 ∈ M, P i0 = univ
  · -- type B: a block keeps the whole purview
    obtain ⟨i0, hi0, h0⟩ := hB
    set ε := epsN N with hεdef
    set ℓ := (a - ε) / (1 / 2 + a) with hℓ
    have hε0 : 0 ≤ ε := by rw [hεdef]; unfold epsN; positivity
    have hℓpos : 19 / 10 * a ≤ ℓ := by
      rw [hℓ, le_div_iff₀ (by linarith)]; nlinarith
    have hℓ1 : 1 - (1 / 2 + ε) / (1 / 2 + a) = ℓ := by
      rw [hℓ]; field_simp; ring
    have hterm : ∀ i ∈ M, ℓ / N * ((N : ℝ) - (P i).card) ≤ t i := by
      intro i hi
      rcases cs_causePart_univ_or_empty θ hi0 h0 hi with hPi | hPi
      · simp only [ht]
        rw [show P i = univ from hPi, card_univ, Fintype.card_fin, sub_self, mul_zero]
        rw [cs_subMean_univ, div_self (cs_clamp_pos hw r0 i).ne', Real.log_one]
      · simp only [ht]
        rw [show P i = ∅ from hPi, card_empty, Nat.cast_zero, sub_zero]
        rw [div_mul_cancel₀ _ (by positivity : (N : ℝ) ≠ 0)]
        have hy := hfloor i hi
        have hA := (abs_le.1 (hcol r0 i)).2
        have hApos := cs_subMean_pos hw ∅ r0 i
        have hypos : 0 < clamp01 (w r0 i) := by linarith
        have hyA : 0 < clamp01 (w r0 i) / subMean w ∅ r0 i := div_pos hypos hApos
        have hlow : 1 - (subMean w ∅ r0 i) / clamp01 (w r0 i) ≤
            Real.log (clamp01 (w r0 i) / subMean w ∅ r0 i) := by
          have := Real.log_le_sub_one_of_pos (inv_pos.2 hyA)
          rw [Real.log_inv, inv_div] at this; linarith
        have hq : (subMean w ∅ r0 i) / clamp01 (w r0 i) ≤ (1 / 2 + ε) / (1 / 2 + a) :=
          div_le_div₀ (by linarith) (by linarith) (by linarith) hy
        linarith
    have hS : ℓ / N * (cutCount M univ θ : ℝ) ≤ ∑ i ∈ M, t i := by
      rw [hcc, mul_sum]; exact sum_le_sum hterm
    rw [div_le_div_iff₀ hmpos (mul_pos hl2pos hccpos)]
    have hkey : a * Real.log 2 ≤ mX N * (ℓ / N) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      have haN : 0 ≤ a * N := mul_nonneg hapos.le (Nat.cast_nonneg _)
      have hl := mul_le_mul_of_nonneg_left hl2.le haN
      calc a * Real.log 2 * N ≤ (N / 2) * (19 / 10 * a) := by linarith
        _ ≤ mX N * ℓ := by nlinarith
    calc a * (Real.log 2 * (cutCount M univ θ : ℝ))
        = (a * Real.log 2) * (cutCount M univ θ : ℝ) := by ring
      _ ≤ (mX N * (ℓ / N)) * (cutCount M univ θ : ℝ) :=
          mul_le_mul_of_nonneg_right hkey hccpos.le
      _ = mX N * (ℓ / N * (cutCount M univ θ : ℝ)) := by ring
      _ ≤ mX N * (∑ i ∈ M, t i) := mul_le_mul_of_nonneg_left hS hmpos.le
      _ = (∑ i ∈ M, t i) * mX N := by ring
  · -- types A and C
    push Not at hB
    have hS : (N : ℝ) / 2000 ≤ ∑ i ∈ M, t i := by
      by_cases hA : ∃ i0 ∈ M, N < (P i0).card + D0C N
      · obtain ⟨i0, hi0, hbig0⟩ := hA
        set K' := univ \ P i0 with hK'
        have hK'c : K'ᶜ = P i0 := by rw [hK', ← compl_eq_univ_sdiff, compl_compl]
        have hK'card : K'.card = N - (P i0).card := by rw [hK', card_univ_sdiff, Fintype.card_fin]
        have hK'ne : K'.Nonempty := by
          rw [hK', sdiff_nonempty]; intro h; exact hB i0 hi0 (Finset.univ_subset_iff.1 h)
        have hPle : (P i0).card ≤ N := by simpa using card_le_univ (P i0)
        have hJ : K'.card ≤ JC N := by
          rw [hK'card]; unfold D0C JC at *; omega
        have hfar : 3 * K'.card + 3 < N := by
          rw [hK'card]; unfold D0C JC at *; omega
        have hsc := (cs_smallCut hg hfr hw hK hN hslT (ha.trans (by norm_num)) hK'ne hJ hfar).1
        refine hsc.trans (sum_le_sum fun i hi => ?_)
        rcases cs_causePart_eq_or_disjoint θ hi hi0 with he | hd
        · simp only [ht]
          have : P i = K'ᶜ := by rw [hK'c]; exact he
          rw [this]; exact min_le_left _ _
        · have hPi : (P i).card + D0C N ≤ N := by
            have hd' : Disjoint (P i) (P i0) := hd
            have := card_union_of_disjoint hd'
            have h2 : (P i ∪ P i0).card ≤ N := by simpa using card_le_univ (P i ∪ P i0)
            unfold D0C at *; omega
          have hle := hbig (P i) r0 i hPi
          have hy := cs_clamp_pos hw r0 i
          refine (min_le_right _ _).trans ?_
          exact Real.log_le_log (div_pos hy cs_cX_pos)
            (div_le_div_of_nonneg_left hy.le (cs_subMean_pos hw _ r0 i) hle)
      · push Not at hA
        -- type C: every unit is a big cut
        have hterm : ∀ i ∈ M, Real.log (clamp01 (w r0 i)) + 249 / 500 ≤ t i := by
          intro i hi
          have hle := hbig (P i) r0 i (by have := hA i hi; omega)
          have hy := cs_clamp_pos hw r0 i
          have hApos := cs_subMean_pos hw (P i) r0 i
          simp only [ht]
          rw [Real.log_div hy.ne' hApos.ne']
          have h1 : Real.log (subMean w (P i) r0 i) ≤ subMean w (P i) r0 i - 1 :=
            Real.log_le_sub_one_of_pos hApos
          unfold cX at hle; linarith
        have hsumy : -XW w r0 ≤ ∑ i ∈ M, Real.log (clamp01 (w r0 i)) := by
          have h := XMW_le_XW w M r0
          have e : ∑ i ∈ M, Real.log (clamp01 (w r0 i)) = -XMW w M r0 := by
            unfold XMW; rw [sum_neg_distrib, neg_neg]
          linarith
        have htilt := cnt_tilt hg
        have hx0 := x0_lt
        have hx0N : x0 * N ≤ 2029 / 10000 * N := mul_le_mul_of_nonneg_right hx0.le (by positivity)
        have hsum2 : ∑ i ∈ M, (Real.log (clamp01 (w r0 i)) + 249 / 500) ≤ ∑ i ∈ M, t i :=
          sum_le_sum hterm
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, hMc] at hsum2
        have hm' : (((N - dX N : ℕ)) : ℝ) = mX N := rfl
        rw [hm'] at hsum2
        nlinarith
    rw [div_le_div_iff₀ hmpos (mul_pos hl2pos hccpos)]
    have h1 : a * Real.log 2 ≤ 1 / 2000 := by nlinarith
    calc a * (Real.log 2 * (cutCount M univ θ : ℝ))
        ≤ a * (Real.log 2 * (mX N * N)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hccle hl2pos.le) hapos.le
      _ = (a * Real.log 2) * N * mX N := by ring
      _ ≤ (1 / 2000) * N * mX N := by gcongr
      _ ≤ (∑ i ∈ M, t i) * mX N := by
          refine mul_le_mul_of_nonneg_right ?_ hmpos.le; linarith

/-! ### Normaliser and selectivity at `(univ, r0)` -/

/-- **`cnt_normC`** (deterministic form): FE4b plus the Sens rows (each `≤ 1`). -/
theorem cs_normC {s r0 : State N} (w : Param N) (hfr : CountFreshX N s r0 w)
    (hsens : 2 * ((N : ℝ) + 1) ^ 4 ≤ 2 ^ (dX N + 1))
    {K : Finset (Fin N)} (hK : K.card = dX N) :
    ∑ t : State N, ∏ i ∈ univ \ K, clamp01 (w t i) ≤ 2 ^ (dX N + 2) := by
  have h1 := hfr.fe4b K hK
  rw [← sum_filter_add_sum_filter_not univ (fun t => t ∈ sensRows s r0)]
  have hS : ∑ t ∈ univ.filter (fun t => t ∈ sensRows s r0), ∏ i ∈ univ \ K, clamp01 (w t i) ≤
      2 * ((N : ℝ) + 1) ^ 4 := by
    calc _ ≤ ∑ _t ∈ univ.filter (fun t => t ∈ sensRows s r0), (1 : ℝ) :=
          sum_le_sum fun t _ => prod_le_one (fun i _ => clamp01_nonneg _)
            (fun i _ => clamp01_le_one _)
      _ = ((univ.filter (fun t => t ∈ sensRows s r0)).card : ℝ) := by simp
      _ ≤ 2 * ((N : ℝ) + 1) ^ 4 := by
          have : (univ.filter (fun t => t ∈ sensRows s r0)) = sensRows s r0 := by ext; simp
          rw [this]
          exact_mod_cast card_sensRows_le s r0
  have hF : ∑ t ∈ univ.filter (fun t => t ∉ sensRows s r0), ∏ i ∈ univ \ K, clamp01 (w t i) =
      ∑ r ∈ freshRows s r0, ∏ i ∈ univ \ K, clamp01 (w r i) := rfl
  rw [hF, pow_succ]
  linarith

theorem cs_causeRep_univ_r0_ge {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    (hg : GoodW3 N s r0 x σ w) (hfr : CountFreshX N s r0 w) (hw : w ∈ openCube N)
    (hsens : 2 * ((N : ℝ) + 1) ^ 4 ≤ 2 ^ (dX N + 1)) {K : Finset (Fin N)} (hK : K.card = dX N) :
    Real.exp (-(x0 * N + slT N)) / 2 ^ (dX N + 2) ≤
      causeRep (tpmOf (flipP s w)) univ r0 (univ \ K) s := by
  rw [cs_causeRep_univ_eq, cs_causeFwd_univ_eq]
  simp only [cs_causeFwd_univ_eq]
  have hnorm := cs_normC w hfr hsens hK
  have hpos : 0 < ∑ t : State N, ∏ i ∈ univ \ K, clamp01 (w t i) :=
    sum_pos (fun t _ => prod_pos fun i _ => cs_clamp_pos hw t i) ⟨r0, mem_univ _⟩
  have hP : Real.exp (-(x0 * N + slT N)) ≤ ∏ i ∈ univ \ K, clamp01 (w r0 i) := by
    have h1 : Real.exp (-(x0 * N + slT N)) ≤ Real.exp (-XW w r0) :=
      Real.exp_le_exp.2 (by linarith [cnt_tilt hg])
    have h2 : Real.exp (-XW w r0) = ∏ i, clamp01 (w r0 i) := by
      rw [← Pw_eq_exp_neg_XW (fun i => cs_clamp_pos hw r0 i)]; rfl
    have h3 : ∏ i, clamp01 (w r0 i) ≤ ∏ i ∈ univ \ K, clamp01 (w r0 i) :=
      prod_le_prod_of_subset_of_le_one (subset_univ _) (fun i _ => clamp01_nonneg _)
        (fun i _ _ => clamp01_le_one _)
    linarith
  calc Real.exp (-(x0 * N + slT N)) / 2 ^ (dX N + 2)
      ≤ (∏ i ∈ univ \ K, clamp01 (w r0 i)) / 2 ^ (dX N + 2) :=
        div_le_div_of_nonneg_right hP (by positivity)
    _ ≤ (∏ i ∈ univ \ K, clamp01 (w r0 i)) / ∑ t : State N, ∏ i ∈ univ \ K, clamp01 (w t i) :=
        div_le_div_of_nonneg_left (prod_nonneg fun i _ => clamp01_nonneg _) hpos hnorm

/-- **`phiCatAt_univ_r0_ge`** (Phi level). -/
theorem cs_phiCat_univ_r0_ge {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    (hg : GoodW3 N s r0 x σ w) (hfr : CountFreshX N s r0 w) (hw : w ∈ openCube N)
    {K : Finset (Fin N)} (hK : K ∈ famX3 N s r0 x σ w)
    (hN : 10000 ≤ N) (hslT : slT N ≤ N / 1000) (ha : Real.exp (-((N : ℝ) / 200)) ≤ 1 / 2000)
    (heps : epsN N ≤ Real.exp (-((N : ℝ) / 200)) / 100)
    (hJ3 : 3 * JC N + 3 < N) (hD2 : 2 * D0C N ≤ N)
    (hbig : ∀ (A : Finset (Fin N)) (t : State N) (i : Fin N), A.card + D0C N ≤ N →
      subMean w A t i ≤ cX)
    (hcol : ∀ (t : State N) (i : Fin N), |subMean w ∅ t i - 1 / 2| ≤ epsN N) :
    causeRep (tpmOf (flipP s w)) univ r0 (univ \ K) s * Real.exp (-((N : ℝ) / 200)) ≤
      phiCat (tpmOf (flipP s w)) univ r0 (univ \ K) s := by
  have hNpos : 0 < N := by omega
  have hm := cs_mX_ge hN
  have hNr : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have hmpos : 0 < mX N := by linarith
  have hMne : (univ \ K).Nonempty := by
    rw [← card_pos, cs_card_M (famX3_card hK)]
    have := cs_dX_le N
    have h1 : dX N < N := by
      have : (dX N : ℝ) < N := by linarith
      exact_mod_cast this
    omega
  have key := cs_phiCat_ge_of_ratio (tpmOf (flipP s w)) univ r0 (univ \ K) s hMne
    (L := mX N) (c := Real.exp (-((N : ℝ) / 200)) / mX N) hmpos.le
    (div_nonneg (Real.exp_pos _).le hmpos.le)
    (fun θ => by
      have := cutCount_univ_ge (univ \ K) θ
      rw [cs_card_M (famX3_card hK)] at this
      unfold mX; exact_mod_cast this)
    (cs_cp_ratio hg hfr hw hK hN hslT ha heps hJ3 hD2 hbig hcol)
  rwa [mul_div_cancel₀ _ hmpos.ne'] at key

end Census
end IIT
