/-
Census, B1, W14 work package WP2 (cause side), part 7 (sub-package 2C): the states and the assembly.

* `cs_XW_lt` / `cnt_XW_lt` (W5 CS(i), W13 step table): `r0` is the strict maximiser of `P`;
  `sysCause_proved : SysCauseStmt`;
* `cs_XMW_lt` / `cnt_XMW_lt` (W5 CS(ii), W7 4.3, W13 F2: AM-GM `ln(y/U) ≥ 2 λ` on the cause side,
  `posNear({x})` on the effect side);
* `cs_maxCauseStates_univ` (the `h`-monotonicity of W5 CS(ii));
* `causeDet_proved : CauseDetStmt` (W5 CS(v)).
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §7.  No `sorry`.
-/
import IIT.Census.B1CntCauseH4
import IIT.Census.B1CntCauseNum

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### Small facts -/

theorem cs_cellsX_cause_mlo : ∀ c ∈ cellsX .cause, ((499999 / 1000000 : ℚ) : ℝ) ≤ (c.1 : ℝ) := by
  intro c hc
  have h : ∀ c ∈ cellsXCauseData, (499999 / 1000000 : ℚ) ≤ c.1 := by
    simp only [cellsXCauseData, List.forall_mem_cons]
    norm_num
  exact_mod_cast h c (List.mem_toFinset.1 hc)

lemma cs_XMW_sub {w : Param N} (hw : w ∈ openCube N) (M : Finset (Fin N)) (r t : State N) :
    XMW w M t - XMW w M r = ∑ i ∈ M, Real.log (clamp01 (w r i) / clamp01 (w t i)) := by
  unfold XMW
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [Real.log_div (cs_clamp_pos hw r i).ne' (cs_clamp_pos hw t i).ne']
  ring

/-- AM-GM: `ln(y/U) ≥ 2 ln(2y/(y+U))`. -/
lemma cs_amgm {y U : ℝ} (hy : 0 < y) (hU : 0 < U) :
    2 * Real.log (2 * y / (y + U)) ≤ Real.log (y / U) := by
  have e : 2 * Real.log (2 * y / (y + U)) = Real.log ((2 * y / (y + U)) ^ 2) := by
    rw [Real.log_pow]; norm_num
  rw [e]
  refine Real.log_le_log (by positivity) ?_
  rw [div_pow, div_le_div_iff₀ (by positivity) hU]
  nlinarith [sq_nonneg (y - U), mul_pos hy hU]

lemma cs_meanPlus_single_ge {w : Param N} (r : State N) (x i : Fin N) :
    (1 + clamp01 (w (flipAt x r) i)) / 2 ≤ b1CutMeanPlus w r {x} i := by
  unfold b1CutMeanPlus
  rw [card_singleton, pow_one]
  refine div_le_div_of_nonneg_right ?_ (by norm_num)
  have hmem : flipAt x r ∈ (agree ({x} : Finset (Fin N))ᶜ r).erase r :=
    mem_erase.2 ⟨flipAt_ne x r, cs_mem_agree_compl_single.2 (Or.inr rfl)⟩
  have := single_le_sum (f := fun v => clamp01 (w v i)) (fun v _ => clamp01_nonneg _) hmem
  linarith

/-- `b1CutGX(r0, {x}) ≤ ln(y/U)` (W13-effect G3). -/
lemma cs_b1CutGX_single_le {w : Param N} (hw : w ∈ openCube N) (r0 : State N) (x i : Fin N) :
    b1CutGX w r0 {x} i ≤ Real.log (clamp01 (w r0 i) / clamp01 (w (flipAt x r0) i)) := by
  have hy := cs_clamp_pos hw r0 i
  have hU := cs_clamp_pos hw (flipAt x r0) i
  have hU1 := clamp01_le_one (w (flipAt x r0) i)
  have hmP := cs_meanPlus_single_ge (w := w) r0 x i
  refine (min_le_left _ _).trans (Real.log_le_log (div_pos hy (by linarith)) ?_)
  exact div_le_div_of_nonneg_left hy.le hU (by linarith)

lemma cs_b1CutGX_le_log2 (w : Param N) (t : State N) (K' : Finset (Fin N)) (i : Fin N) :
    b1CutGX w t K' i ≤ Real.log 2 := by
  refine (min_le_right _ _).trans ?_
  rcases eq_or_lt_of_le (clamp01_nonneg (w t i)) with h0 | hpos
  · rw [← h0, zero_div, Real.log_zero]; exact (Real.log_pos (by norm_num)).le
  · refine Real.log_le_log (div_pos hpos cs_b1Cap_pos) ?_
    rw [div_le_iff₀ cs_b1Cap_pos]; unfold b1Cap; linarith [clamp01_le_one (w t i)]

/-! ### The system cause state -/

theorem cs_XW_lt {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    (hg : GoodW3 N s r0 x σ w) (hfr : CountFreshX N s r0 w) (hw : w ∈ openCube N)
    (hN : 1000 ≤ N) : ∀ r, r ≠ r0 → XW w r0 < XW w r := by
  intro r hr
  have hNr : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have htilt := cnt_tilt hg
  have hη : (0 : ℝ) < b1Eta * N := by unfold b1Eta; positivity
  by_cases hS : r ∈ sensRows s r0
  · by_cases hr1 : r = flipAt x r0
    · subst hr1
      have hsub := cs_XMW_sub hw univ r0 (flipAt x r0)
      simp only [XMW] at hsub
      change XW w (flipAt x r0) - XW w r0 = _ at hsub
      cases σ with
      | cause =>
        have hR := hg.1.retR1 rfl
        obtain ⟨c, hc, hcell⟩ := hg.1.regEv
        have hyx : (499999 / 1000000 : ℝ) ≤ clamp01 (w r0 x) := by
          have := cs_cellsX_cause_mlo c hc
          have h2 := hcell.1 x
          simp only [baseE] at h2
          push_cast at this; linarith
        have hy := cs_clamp_pos hw r0 x
        have hU := cs_clamp_pos hw (flipAt x r0) x
        have hxterm : -2 ≤ Real.log (clamp01 (w r0 x) / clamp01 (w (flipAt x r0) x)) := by
          have h1 : clamp01 (w r0 x) ≤ clamp01 (w r0 x) / clamp01 (w (flipAt x r0) x) := by
            rw [le_div_iff₀ hU]
            nlinarith [clamp01_le_one (w (flipAt x r0) x)]
          have h2 := Real.log_le_log hy h1
          have h3 : 1 - 1 / clamp01 (w r0 x) ≤ Real.log (clamp01 (w r0 x)) := by
            have := Real.log_le_sub_one_of_pos (inv_pos.2 hy)
            rw [Real.log_inv] at this; rw [one_div]; linarith
          have h4 : 1 / clamp01 (w r0 x) ≤ 3 := by
            rw [div_le_iff₀ hy]; linarith
          linarith
        have := add_sum_erase univ (fun i => Real.log (clamp01 (w r0 i) /
          clamp01 (w (flipAt x r0) i))) (mem_univ x)
        linarith
      | effect =>
        have hp := hg.1.posNear {x} (singleton_nonempty x) (by simp) (fun h => by cases h)
        have : ∑ i, b1CutGX w r0 {x} i ≤
            ∑ i, Real.log (clamp01 (w r0 i) / clamp01 (w (flipAt x r0) i)) :=
          sum_le_sum fun i _ => cs_b1CutGX_single_le hw r0 x i
        linarith
    · have h := hg.1.ret r hS hr hr1 ∅ (by simp)
      simp only [sdiff_empty] at h
      have e : XMW w univ r = XW w r := rfl
      linarith
  · have h := hfr.fe6 r hS
    linarith

theorem cnt_XW_lt : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N),
    GoodW3 N s r0 x σ w → CountFreshX N s r0 w → ∀ r, r ≠ r0 → XW w r0 < XW w r := by
  filter_upwards [eventually_ge_atTop 1000] with N hN s r0 x σ w hg hfr
  exact cs_XW_lt hg hfr (cnt_mem_openCube hg hfr) hN

/-- **WP2 deliverable: `SysCauseStmt`** (W5 CS(i)). -/
theorem sysCause_proved : SysCauseStmt := by
  filter_upwards [cnt_XW_lt] with N hXW s r0 x σ w hg hfr
  have hw := cnt_mem_openCube hg hfr
  have hz := cnt_flipP_open hg hfr
  refine sysMaxCauseStates_univ_eq hz s r0 fun r hr => ?_
  rw [rowProd_eq_Pw, rowProd_eq_Pw, flipP_invol s w, Pw_eq_exp_neg_XW (fun i => cs_clamp_pos hw r i),
    Pw_eq_exp_neg_XW (fun i => cs_clamp_pos hw r0 i)]
  exact Real.exp_lt_exp.2 (neg_lt_neg (hXW s r0 x σ w hg hfr r hr))

/-! ### The cause state of `M = univ \ K` at the purview `univ` -/

theorem cs_XMW_lt {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    (hg : GoodW3 N s r0 x σ w) (hfr : CountFreshX N s r0 w) (hw : w ∈ openCube N)
    {K : Finset (Fin N)} (hK : K ∈ famX3 N s r0 x σ w) (hRet : RetK N s r0 K w)
    (hN : 10000 ≤ N) (hslT : slT N ≤ N / 1000) (ha : Real.exp (-((N : ℝ) / 200)) ≤ 1 / 1000) :
    ∀ t, t ≠ r0 → XMW w (univ \ K) r0 < XMW w (univ \ K) t := by
  intro t ht
  have hNr : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have htilt := cnt_tilt hg
  have hle := XMW_le_XW w (univ \ K) r0
  have hη : (0 : ℝ) < b1Eta * N := by unfold b1Eta; positivity
  have hKc := famX3_card hK
  by_cases hS : t ∈ sensRows s r0
  · by_cases ht1 : t = flipAt x r0
    · subst ht1
      rw [← sub_pos, cs_XMW_sub hw]
      cases σ with
      | cause =>
        have hsc := (cs_smallCut hg hfr hw hK hN hslT ha (singleton_nonempty x)
          (by simp; unfold JC; omega) (by simp; omega)).1
        have hterm : ∀ i ∈ univ \ K, 2 * csG w r0 {x} i ≤
            Real.log (clamp01 (w r0 i) / clamp01 (w (flipAt x r0) i)) := by
          intro i _
          rw [cs_csG_single_eq w s r0 x i]
          refine le_trans ?_ (cs_amgm (cs_clamp_pos hw r0 i) (cs_clamp_pos hw (flipAt x r0) i))
          have := min_le_left (lamX w s r0 x .cause i) (Real.log (clamp01 (w r0 i) / cX))
          have e : lamX w s r0 x .cause i = Real.log (2 * clamp01 (w r0 i) /
              (clamp01 (w r0 i) + clamp01 (w (flipAt x r0) i))) := rfl
          linarith
        have := sum_le_sum hterm
        rw [← mul_sum] at this
        linarith
      | effect =>
        have hp := hg.1.posNear {x} (singleton_nonempty x) (by simp) (fun h => by cases h)
        have h2 := cs_sum_sdiff_ge K (b1CutGX w r0 {x}) (fun i _ => cs_b1CutGX_le_log2 w r0 {x} i)
        have h3 : ∑ i ∈ univ \ K, b1CutGX w r0 {x} i ≤
            ∑ i ∈ univ \ K, Real.log (clamp01 (w r0 i) / clamp01 (w (flipAt x r0) i)) :=
          sum_le_sum fun i _ => cs_b1CutGX_single_le hw r0 x i
        have hd := cs_dX_le N
        have hl2 := cs_log_two_lt
        rw [hKc] at h2
        nlinarith
    · have h := hg.1.ret t hS ht ht1 K (by rw [hKc])
      linarith
  · have h := hRet t hS
    linarith

theorem cnt_XMW_lt : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N),
    GoodW3 N s r0 x σ w → CountFreshX N s r0 w → ∀ K ∈ famX3 N s r0 x σ w, RetK N s r0 K w →
      ∀ t, t ≠ r0 → XMW w (univ \ K) r0 < XMW w (univ \ K) t := by
  filter_upwards [eventually_ge_atTop 10000, cs_ev_slT, cs_ev_a] with N hN hslT ha
    s r0 x σ w hg hfr K hK hRet
  exact cs_XMW_lt hg hfr (cnt_mem_openCube hg hfr) hK hRet hN hslT (ha.trans (by norm_num))

/-- The `h`-monotonicity of W5 CS(ii): `p ↦ p log₂(2^N p)` is strictly increasing past `2^{-N}`. -/
lemma cs_h_lt {p q : ℝ} (hp : 0 ≤ p) (hpq : p < q) (hq : 1 < 2 ^ N * q) :
    p * Real.logb 2 (2 ^ N * p) < q * Real.logb 2 (2 ^ N * q) := by
  have hqpos : 0 < q := lt_of_le_of_lt hp hpq
  have hLq : 0 < Real.logb 2 (2 ^ N * q) := Real.logb_pos (by norm_num) hq
  by_cases h1 : 2 ^ N * p ≤ 1
  · have : Real.logb 2 (2 ^ N * p) ≤ 0 := Real.logb_nonpos (by norm_num) (by positivity) h1
    nlinarith [mul_pos hqpos hLq]
  · push Not at h1
    have hLp : 0 < Real.logb 2 (2 ^ N * p) := Real.logb_pos (by norm_num) h1
    have hmono : Real.logb 2 (2 ^ N * p) ≤ Real.logb 2 (2 ^ N * q) :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) (by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) N])
    nlinarith

theorem cs_maxCauseStates_univ {s r0 : State N} {w : Param N} (hw : w ∈ openCube N)
    (M : Finset (Fin N)) (hlt : ∀ t, t ≠ r0 → XMW w M r0 < XMW w M t)
    (hp : 1 / (2 : ℝ) ^ N < causeRep (tpmOf (flipP s w)) univ r0 M s) :
    maxCauseStates (tpmOf (flipP s w)) M s univ = {r0} := by
  set T := tpmOf (flipP s w)
  set S := ∑ t : State N, causeFwd T univ t M s with hS
  have hcf : ∀ t, causeFwd T univ t M s = Real.exp (-XMW w M t) := by
    intro t
    rw [cs_causeFwd_univ_eq]
    unfold XMW
    rw [← sum_neg_distrib, Real.exp_sum]
    exact prod_congr rfl fun i _ => by rw [neg_neg, Real.exp_log (cs_clamp_pos hw t i)]
  have hSpos : 0 < S := sum_pos (fun t _ => by rw [hcf]; exact Real.exp_pos _) ⟨r0, mem_univ _⟩
  have hrep : ∀ t, causeRep T univ t M s = causeFwd T univ t M s / S := fun t =>
    cs_causeRep_univ_eq T t M s
  have hii : ∀ t, iiC T M s univ t =
      causeRep T univ t M s * Real.logb 2 (2 ^ N * causeRep T univ t M s) := by
    intro t
    unfold iiC
    congr 2
    rw [hrep, uncCauseFwd, avgOverStates, ← hS]
    field_simp
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hq : 1 < 2 ^ N * causeRep T univ r0 M s := by
    rw [div_lt_iff₀ h2N] at hp; linarith
  have hstrict : ∀ t, t ≠ r0 → iiC T M s univ t < iiC T M s univ r0 := by
    intro t ht
    rw [hii, hii]
    refine cs_h_lt (causeRep_nonneg _ _ _ _ _) ?_ hq
    rw [hrep, hrep, hcf, hcf]
    exact div_lt_div_of_pos_right (Real.exp_lt_exp.2 (neg_lt_neg (hlt t ht))) hSpos
  ext t
  rw [mem_singleton]
  unfold maxCauseStates
  rw [mem_argmaxSet]
  constructor
  · intro h; by_contra hne; exact absurd (h r0) (not_le.2 (hstrict t hne))
  · rintro rfl b
    by_cases hb : b = t
    · rw [hb]
    · exact (hstrict b hb).le

/-! ### Assembly -/

/-- **WP2 deliverable: `CauseDetStmt`** (W5 Theorem CS (ii)-(v), W7 Theorem CS_X). -/
theorem causeDet_proved : CauseDetStmt := by
  filter_upwards [eventually_ge_atTop 400000, cs_ev_slT, cs_ev_a, cs_ev_eps, cs_ev_JC, cs_ev_sens,
    cs_ev_dev, cs_ev_H3, cs_ev_H4, cs_ev_H2, cs_ev_floor, cnt_subDev, cnt_colDev]
    with N hN hslT ha heps hJ hsens hdev hH3 hH4 hH2 hfl hsubD hcolD
  intro s r0 x σ w hg hfr K hK hRet
  have hN' : 10000 ≤ N := by omega
  have hNr : (400000 : ℝ) ≤ N := by exact_mod_cast hN
  set T := tpmOf (flipP s w) with hT
  set M := univ \ K with hM
  set a := Real.exp (-((N : ℝ) / 200)) with hadef
  have hw := cnt_mem_openCube hg hfr
  have hu := cnt_reach hg hfr
  have hKc := famX3_card hK
  have hcol : ∀ (t : State N) (i : Fin N), |subMean w ∅ t i - 1 / 2| ≤ epsN N :=
    hcolD s r0 x σ w hg hfr
  have hbig : ∀ (A : Finset (Fin N)) (t : State N) (i : Fin N), A.card + D0C N ≤ N →
      subMean w A t i ≤ cX := by
    intro A t i hA
    have h1 := hsubD s r0 x σ w hg hfr A t i hA
    have h2 := hdev (N - A.card) (by omega) (by omega)
    have := (abs_le.1 (h1.trans h2)).2
    unfold cX; linarith
  -- the value at `(univ, r0)`
  have hR := cs_phiCat_univ_r0_ge hg hfr hw hK hN' hslT ha heps.1 hJ.1 hJ.2 hbig hcol
  have hRrep := cs_causeRep_univ_r0_ge hg hfr hw hsens hKc
  have hrhs := cs_rhs_ge hslT
  have hRlow : Real.exp (-(csA * N)) / 8 ≤ causeRep T univ r0 M s * a := by
    refine hrhs.trans (mul_le_mul_of_nonneg_right hRrep (Real.exp_pos _).le)
  have hRpos : 0 < causeRep T univ r0 M s * a := lt_of_lt_of_le (by positivity) hRlow
  -- the cause state at `univ`
  have hXMW := cs_XMW_lt hg hfr hw hK hRet hN' hslT (ha.trans (by norm_num))
  have hp : 1 / (2 : ℝ) ^ N < causeRep T univ r0 M s := by
    refine lt_of_lt_of_le hfl.2 (hrhs.trans ?_)
    have : Real.exp (-(x0 * N + slT N)) / 2 ^ (dX N + 2) * a ≤
        Real.exp (-(x0 * N + slT N)) / 2 ^ (dX N + 2) := by
      refine mul_le_of_le_one_right (by positivity) ?_
      rw [hadef]; exact Real.exp_le_one_iff.2 (by have : (0:ℝ) ≤ N := Nat.cast_nonneg N; linarith)
    exact this.trans hRrep
  have hstates : maxCauseStates T M s univ = {r0} := cs_maxCauseStates_univ hw M hXMW hp
  -- every other candidate is smaller
  have hcomp : ∀ (Z : Finset (Fin N)) (z : State N), z ∈ maxCauseStates T M s Z →
      (Z, z) ≠ (univ, r0) → phiCat T Z z M s < causeRep T univ r0 M s * a := by
    intro Z z hz hne
    by_cases hZu : Z = univ
    · subst hZu
      rw [hstates, mem_singleton] at hz
      exact absurd (by rw [hz]) hne
    rcases Z.eq_empty_or_nonempty with hZ0 | hZne
    · subst hZ0; rw [phiCat_empty_purview]; exact hRpos
    by_cases hZJ : Z.card + JC N < N
    · -- (h2)
      have hD0J : D0C N ≤ JC N := by unfold D0C JC; omega
      have hsubZ := fun t i => hsubD s r0 x σ w hg hfr Z t i (by omega)
      have hδ := cs_delta_le_inv_sq (N := N) (by omega) (D := N - Z.card) (by omega) (by omega)
      have hδZ := cs_delta_scaled N Z.card (by simpa using card_le_univ Z)
      have hε : epsN N ≤ 1 / 4 := by linarith [heps.1]
      have hMne : M.Nonempty := by
        rw [← card_pos, hM, cs_card_M hKc]
        have := cs_dX_le N
        have h1 : dX N < N := by
          have : (dX N : ℝ) < N := by linarith
          exact_mod_cast this
        omega
      have h2 := cs_phiCat_h2 (s := s) hw K hMne (by omega) z hZne hZJ hsubZ hδ hδZ hcol hε
      linarith
    · push Not at hZJ
      by_cases hzr : ∀ i ∈ Z, z i = r0 i
      · exact cs_phiCat_h3 hg hfr hw hK hN' hslT ha heps.2 hJ.1 hsens hcol hH3 z hZu hZJ hzr
      · push Not at hzr
        exact cs_phiCat_h4 hg hfr hw hK hN' hJ.1 hsens (lt_of_lt_of_le hH4 hrhs) z hZu hZJ hzr
  -- the purview candidates, through the collapse at `S = univ`
  have hstatesAt : ∀ Z, maxCauseStatesAt T univ s M s Z = maxCauseStates T M s Z :=
    fun Z => maxCauseStatesAt_univ T s M s Z hu
  have hphiAt : ∀ Z z, phiCatAt T univ s Z z M s = phiCat T Z z M s :=
    fun Z z => phiCatAt_univ T s Z z M s hu
  have hmemC : (univ, r0) ∈ causeCandidatesAt T univ s M s := by
    rw [causeCandidatesAt, mem_biUnion]
    exact ⟨univ, mem_powerset.2 (subset_refl _),
      mem_image.2 ⟨r0, by rw [hstatesAt, hstates, mem_singleton], rfl⟩⟩
  have hcandlt : ∀ q ∈ causeCandidatesAt T univ s M s, q ≠ (univ, r0) →
      phiCatAt T univ s q.1 q.2 M s < phiCatAt T univ s univ r0 M s := by
    intro q hq hne
    obtain ⟨Z, _, hz⟩ := mem_biUnion.1 hq
    obtain ⟨z, hzmem, rfl⟩ := mem_image.1 hz
    rw [hphiAt, hphiAt]
    rw [hstatesAt] at hzmem
    exact (hcomp Z z hzmem hne).trans_le hR
  have hmax : maxCausePurviewsAt T univ s M s = {(univ, r0)} := by
    ext p
    rw [mem_singleton]
    constructor
    · intro hp'
      obtain ⟨hpC, hpmax⟩ := mem_filter.1 hp'
      by_contra hne
      exact absurd (hpmax _ hmemC) (not_le.2 (hcandlt p hpC hne))
    · rintro rfl
      refine mem_filter.2 ⟨hmemC, fun q hq => ?_⟩
      by_cases hqe : q = (univ, r0)
      · rw [hqe]
      · exact (hcandlt q hq hqe).le
  refine ⟨hmax, ?_⟩
  have hval := phiCatAt_of_mem_maxCausePurviewsAt T univ s M s (p := (univ, r0))
    (by rw [hmax]; exact mem_singleton_self _)
  rw [← hval, hphiAt]
  exact hfl.1.trans (hRlow.trans hR)

end Census
end IIT

#print axioms IIT.Census.causeDet_proved
#print axioms IIT.Census.sysCause_proved
