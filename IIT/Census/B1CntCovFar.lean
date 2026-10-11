/-
Census, B1, W14 work package WP6 (part 6): far pairs (`cov_far`, W9 Lemma COV').

Coupling: `Ỹ_K` = `Y_K` with the shared entries `C_K ∩ C_{K'}` (`C_K = (RDrows K ∪ {s}) × U`)
replaced by `1/2`.  `Ỹ_K` is independent of `Y_{K'}` (disjoint entries), so
`|Cov(Y_K, Y_{K'})| ≤ 2 P(Y_K ≠ Ỹ_K)`; every statistic of `Y_K` moves by `≤ δ = 2^j (d+1)^{r_D} 2^{r_D}/2^d`
(Lemma SH'), so `Y_K ≠ Ỹ_K` forces a `2δ`-degenerate atom (`YK_stable`); each atom has probability
`≤ patB` (`atom_f/n/d`), and there are `≤ 7N(N+1)^{r_D}` atoms.  Exponent `ln 2/240 > 1/420`.
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §11.  No `sorry`.
-/
import IIT.Census.B1CntCovAC
import IIT.Census.B1CntCovFam

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### Generic pieces -/

lemma cov_coupling {X X' Xt Bad : Set (Param N)}
    (hind : cubeM N (Xt ∩ X') = cubeM N Xt * cubeM N X')
    (hBad : ∀ w, w ∉ Bad → (w ∈ X ↔ w ∈ Xt)) :
    |(cubeM N (X ∩ X')).toReal - (cubeM N X).toReal * (cubeM N X').toReal| ≤
      2 * (cubeM N Bad).toReal := by
  simp only [← measureReal_def]
  have h1 : X ∩ X' ⊆ (Xt ∩ X') ∪ Bad := by
    intro w hw
    by_cases hb : w ∈ Bad
    · exact Or.inr hb
    · exact Or.inl ⟨(hBad w hb).1 hw.1, hw.2⟩
  have h2 : Xt ∩ X' ⊆ (X ∩ X') ∪ Bad := by
    intro w hw
    by_cases hb : w ∈ Bad
    · exact Or.inr hb
    · exact Or.inl ⟨(hBad w hb).2 hw.1, hw.2⟩
  have h3 : X ⊆ Xt ∪ Bad := by
    intro w hw
    by_cases hb : w ∈ Bad
    · exact Or.inr hb
    · exact Or.inl ((hBad w hb).1 hw)
  have h4 : Xt ⊆ X ∪ Bad := by
    intro w hw
    by_cases hb : w ∈ Bad
    · exact Or.inr hb
    · exact Or.inl ((hBad w hb).2 hw)
  have k1 := (measureReal_mono (μ := cubeM N) h1).trans (measureReal_union_le (μ := cubeM N) _ _)
  have k2 := (measureReal_mono (μ := cubeM N) h2).trans (measureReal_union_le (μ := cubeM N) _ _)
  have k3 := (measureReal_mono (μ := cubeM N) h3).trans (measureReal_union_le (μ := cubeM N) _ _)
  have k4 := (measureReal_mono (μ := cubeM N) h4).trans (measureReal_union_le (μ := cubeM N) _ _)
  have hind' : (cubeM N).real (Xt ∩ X') = (cubeM N).real Xt * (cubeM N).real X' := by
    simp only [measureReal_def, hind, ENNReal.toReal_mul]
  have hc0 : 0 ≤ (cubeM N).real X' := measureReal_nonneg
  have hc1 : (cubeM N).real X' ≤ 1 := measureReal_le_one
  have hβ : 0 ≤ (cubeM N).real Bad := measureReal_nonneg
  have m1 : (cubeM N).real Xt * (cubeM N).real X' ≤
      ((cubeM N).real X + (cubeM N).real Bad) * (cubeM N).real X' :=
    mul_le_mul_of_nonneg_right k4 hc0
  have m2 : (cubeM N).real X * (cubeM N).real X' ≤
      ((cubeM N).real Xt + (cubeM N).real Bad) * (cubeM N).real X' :=
    mul_le_mul_of_nonneg_right k3 hc0
  have m3 : (cubeM N).real Bad * (cubeM N).real X' ≤ (cubeM N).real Bad :=
    mul_le_of_le_one_right hβ hc1
  rw [abs_le]
  constructor <;> nlinarith

lemma detOnE_gluW {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) {C : Finset (State N × Fin N)}
    {X : Set (Param N)} (h : DetOnE C X) : DetOnE C {w | gluW s r0 f w ∈ X} := by
  intro w w' hw
  apply h
  intro q hq
  by_cases hF : q.1 ∈ sensRows s r0
  · rw [gluW_of_mem f w hF, gluW_of_mem f w' hF]
  · rw [gluW_of_not_mem f w hF, gluW_of_not_mem f w' hF]; exact hw q hq

lemma meas_biUnion2_le {ι κ : Type*} (I : Finset ι) (J : ι → Finset κ) (S : ι → κ → Set (Param N))
    (P : ℝ) (hP0 : 0 ≤ P) (h : ∀ i ∈ I, ∀ j ∈ J i, cubeM N (S i j) ≤ ENNReal.ofReal P) (n : ℕ)
    (hn : ∀ i ∈ I, (J i).card ≤ n) :
    cubeM N (⋃ i ∈ I, ⋃ j ∈ J i, S i j) ≤ ENNReal.ofReal (I.card * n * P) := by
  calc cubeM N (⋃ i ∈ I, ⋃ j ∈ J i, S i j) ≤ ∑ i ∈ I, cubeM N (⋃ j ∈ J i, S i j) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ I, ∑ j ∈ J i, cubeM N (S i j) := sum_le_sum fun i _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ I, ∑ j ∈ J i, ENNReal.ofReal P := sum_le_sum fun i hi => sum_le_sum fun j hj => h i hi j hj
    _ = ENNReal.ofReal (∑ i ∈ I, ∑ j ∈ J i, P) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => sum_nonneg fun j _ => hP0]
        exact sum_congr rfl fun i _ => (ENNReal.ofReal_sum_of_nonneg fun j _ => hP0).symm
    _ ≤ ENNReal.ofReal (I.card * n * P) := by
        apply ENNReal.ofReal_le_ofReal
        calc ∑ i ∈ I, ∑ j ∈ J i, P = ∑ i ∈ I, ((J i).card : ℝ) * P := by
              simp only [sum_const, nsmul_eq_mul]
          _ ≤ ∑ i ∈ I, (n : ℝ) * P := sum_le_sum fun i hi => by
              gcongr; exact_mod_cast hn i hi
          _ = I.card * n * P := by rw [sum_const, nsmul_eq_mul]; ring

lemma card_Aset_le (K : Finset (Fin N)) : (Aset N K).card ≤ (N + 1) ^ rD N := by
  have hmaps : Set.MapsTo (fun A => (univ \ K) \ A) ↑(Aset N K)
      ↑((univ \ K).powerset.filter fun T => T.card ≤ rD N) := by
    intro A hA
    simp only [Aset, mem_coe, mem_filter, mem_powerset] at hA ⊢
    exact ⟨sdiff_subset, hA.2.2.2⟩
  have hinj : Set.InjOn (fun A => (univ \ K) \ A) ↑(Aset N K) := by
    intro A hA B hB h
    simp only [Aset, mem_coe, mem_filter, mem_powerset] at hA hB
    have h' : (univ \ K) \ A = (univ \ K) \ B := h
    rw [← Finset.sdiff_sdiff_eq_self hA.1, ← Finset.sdiff_sdiff_eq_self hB.1, h']
  refine (card_le_card_of_injOn _ hmaps hinj).trans ((card_powerset_filter_le _ _).trans ?_)
  apply Nat.pow_le_pow_left
  have := card_le_card (sdiff_subset : univ \ K ⊆ univ)
  rw [card_univ, Fintype.card_fin] at this
  omega

/-! ### The asymptotic bound -/

lemma pow_eq_exp_log {x : ℝ} (hx : 0 < x) (n : ℕ) : x ^ n = Real.exp (n * Real.log x) := by
  rw [Real.exp_nat_mul, Real.exp_log hx]

lemma rD_le_log (hN : 1 ≤ N) : (rD N : ℝ) ≤ 433 / 100 * Real.log N + 13 ∧
    (rD N : ℝ) * Real.log 2 ≤ 3 * Real.log N + 13 * Real.log 2 := by
  have hp : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hp' : (2 : ℝ) ^ Nat.log 2 N ≤ N := by exact_mod_cast hp
  have hl : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hp'
  have hl2 := Real.log_two_gt_d9
  have hL0 : (0 : ℝ) ≤ Nat.log 2 N := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hrd : (rD N : ℝ) = 3 * (Nat.log 2 N : ℝ) + 13 := by unfold rD; push_cast; ring
  constructor
  · have : (Nat.log 2 N : ℝ) * 0.6931471803 ≤ Real.log N := by
      have := mul_le_mul_of_nonneg_left hl2.le hL0; linarith
    rw [hrd]; nlinarith
  · rw [hrd]; nlinarith

lemma covfar_large : ∀ᶠ N : ℕ in atTop, 4 * (N + 1) ^ 4 ≤ 2 ^ dX N ∧ 1 ≤ dX N ∧
    (2 : ℝ) ≤ mX N ∧ (rD N : ℝ) ≤ mX N := by
  have hl2 : 0 < Real.log 2 / 30 := by have := Real.log_pos (by norm_num : (1:ℝ) < 2); positivity
  filter_upwards [cov_ev_logsq 4 (8 + Real.log 4) (Real.log 2 / 30) hl2,
    cov_ev_logsq 5 18 (1 / 2) (by norm_num), eventually_ge_atTop 100] with N h1 h2 hN
  have hNr : (100 : ℝ) ≤ N := by exact_mod_cast hN
  have hdN : dX N = (N + 29) / 30 := rfl
  have hd30 : N ≤ 30 * dX N := by omega
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hsq := cov_log_le_sq N
  have hm : (mX N : ℝ) ≥ N / 2 := by
    unfold mX
    have : 2 * (N - dX N) ≥ N := by omega
    have : (2 : ℝ) * ((N - dX N : ℕ) : ℝ) ≥ N := by exact_mod_cast this
    linarith
  refine ⟨?_, by omega, by linarith, ?_⟩
  · have hLN : Real.log ((N : ℝ) + 1) ≤ Real.log N + 1 := by
      have : (N : ℝ) + 1 ≤ Real.exp 1 * N := by
        have := Real.exp_one_gt_d9; nlinarith
      calc Real.log ((N : ℝ) + 1) ≤ Real.log (Real.exp 1 * N) := Real.log_le_log (by positivity) this
        _ = Real.log N + 1 := by rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]; ring
    have hd : (N : ℝ) / 30 ≤ dX N := by
      have : (N : ℝ) ≤ 30 * dX N := by exact_mod_cast hd30
      linarith
    have key : Real.log (4 * ((N : ℝ) + 1) ^ 4) ≤ Real.log ((2 : ℝ) ^ dX N) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
      have := Real.log_pos (by norm_num : (1:ℝ) < 2)
      have h5 : Real.log 2 / 30 * N ≤ (dX N : ℝ) * Real.log 2 := by nlinarith
      push_cast
      nlinarith
    have := (Real.log_le_log_iff (by positivity) (by positivity)).1 key
    exact_mod_cast this
  · have := (rD_le_log (N := N) (by omega)).1
    nlinarith

lemma covfar_final (C : ℝ) (hC : 0 < C) : ∀ᶠ N : ℕ in atTop, ∀ j : ℕ, 3 * j ≤ dX N →
    2 * ((7 * (N : ℝ) * ((N : ℝ) + 1) ^ rD N) * patB C (dX N) (dX N + rD N + 1)
      (2 * ((2 : ℝ) ^ j * ((dX N : ℝ) + 1) ^ rD N * 2 ^ rD N / 2 ^ dX N))) ≤
        Real.exp (-((N : ℝ) / 420)) := by
  set K0 : ℝ := 14 * (32 + 2 * C) with hK0
  have hK0pos : 0 < K0 := by positivity
  filter_upwards [cov_ev_logsq 51 (87 + Real.log K0) (1 / 2000) (by norm_num),
    eventually_ge_atTop 100] with N hev hN j hj
  set d := dX N with hd
  set R := rD N with hR
  set ℓ2 := Real.log 2 with hℓ2
  set LN := Real.log ((N : ℝ) + 1) with hLN
  set lnN := Real.log (N : ℝ) with hlnN
  have hNr : (100 : ℝ) ≤ N := by exact_mod_cast hN
  have hdN : dX N = (N + 29) / 30 := rfl
  have hd1 : 1 ≤ d := by omega
  have hdr : (N : ℝ) / 30 ≤ d := by
    have : N ≤ 30 * d := by omega
    have : (N : ℝ) ≤ 30 * d := by exact_mod_cast this
    linarith
  have hdN' : (d : ℝ) ≤ N := by exact_mod_cast (by omega : d ≤ N)
  have hjr : (j : ℝ) * 3 ≤ d := by exact_mod_cast (by omega : j * 3 ≤ d)
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hlnN0 : 0 ≤ lnN := Real.log_natCast_nonneg N
  have hLN0 : 0 ≤ LN := Real.log_nonneg (by linarith)
  have hLNle : LN ≤ lnN + 1 := by
    have : (N : ℝ) + 1 ≤ Real.exp 1 * N := by
      have := Real.exp_one_gt_d9; nlinarith
    calc LN ≤ Real.log (Real.exp 1 * N) := Real.log_le_log (by positivity) this
      _ = lnN + 1 := by rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]; ring
  obtain ⟨hR1, hR2⟩ := rD_le_log (N := N) (by omega)
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hsq := cov_log_le_sq N
  -- pieces as exponentials
  set G : ℝ := R * LN + 2 * R * ℓ2 + ℓ2 with hG
  have hδ : (2 : ℝ) ^ j * ((d : ℝ) + 1) ^ R * 2 ^ R / 2 ^ d ≤
      Real.exp (j * ℓ2 + R * LN + R * ℓ2 - d * ℓ2) := by
    have e1 : (2 : ℝ) ^ j = Real.exp (j * ℓ2) := pow_eq_exp_log (by norm_num) j
    have e2 : (2 : ℝ) ^ R = Real.exp (R * ℓ2) := pow_eq_exp_log (by norm_num) R
    have e3 : (2 : ℝ) ^ d = Real.exp (d * ℓ2) := pow_eq_exp_log (by norm_num) d
    have e4 : ((d : ℝ) + 1) ^ R ≤ Real.exp (R * LN) := by
      rw [← pow_eq_exp_log (by positivity) R]
      exact pow_le_pow_left₀ (by positivity) (by linarith) R
    rw [e1, e2, e3, div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
    have : j * ℓ2 + R * LN + R * ℓ2 - d * ℓ2 + d * ℓ2 = j * ℓ2 + R * LN + R * ℓ2 := by ring
    rw [this, Real.exp_add, Real.exp_add]
    gcongr
  have hsqrt : Real.sqrt (12 * 2 ^ (d + R + 1)) ≤ 4 * Real.exp ((d + R + 1 : ℕ) * ℓ2 / 2) := by
    rw [Real.sqrt_mul (by norm_num), pow_eq_exp_log (by norm_num), ← Real.exp_half]
    gcongr
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hT1 : 4 * (2 * ((2 : ℝ) ^ j * ((d : ℝ) + 1) ^ R * 2 ^ R / 2 ^ d)) /
      Real.sqrt (1 / (12 * 2 ^ (d + R + 1))) ≤ 32 * Real.exp (-(d * ℓ2 / 8) + G) := by
    rw [one_div, Real.sqrt_inv, div_inv_eq_mul]
    have hpos : 0 ≤ (2 : ℝ) ^ j * ((d : ℝ) + 1) ^ R * 2 ^ R / 2 ^ d := by positivity
    calc 4 * (2 * ((2 : ℝ) ^ j * ((d : ℝ) + 1) ^ R * 2 ^ R / 2 ^ d)) *
          Real.sqrt (12 * 2 ^ (d + R + 1))
        ≤ 4 * (2 * Real.exp (j * ℓ2 + R * LN + R * ℓ2 - d * ℓ2)) *
          (4 * Real.exp ((d + R + 1 : ℕ) * ℓ2 / 2)) := by gcongr
      _ = 32 * Real.exp (j * ℓ2 + R * LN + R * ℓ2 - d * ℓ2 + (d + R + 1 : ℕ) * ℓ2 / 2) := by
          rw [Real.exp_add]; ring
      _ ≤ 32 * Real.exp (-(d * ℓ2 / 8) + G) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.exp_le_exp.2
          rw [hG]; push_cast
          nlinarith [mul_nonneg hR0 hLN0]
  have hT2 : 2 * C * ((2 : ℝ) ^ (d - 1)) ^ (-(1 / 8 : ℝ)) ≤ 2 * C * Real.exp (-(d * ℓ2 / 8) + G) := by
    gcongr
    rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
    apply Real.exp_le_exp.2
    have : ((d - 1 : ℕ) : ℝ) = d - 1 := by rw [Nat.cast_sub hd1, Nat.cast_one]
    rw [this, hG]
    nlinarith [mul_nonneg hR0 hLN0]
  have hpat : patB C d (d + R + 1) (2 * ((2 : ℝ) ^ j * ((d : ℝ) + 1) ^ R * 2 ^ R / 2 ^ d)) ≤
      (32 + 2 * C) * Real.exp (-(d * ℓ2 / 8) + G) := by
    unfold patB; linarith
  have hpre : 2 * (7 * (N : ℝ) * ((N : ℝ) + 1) ^ R) ≤ 14 * Real.exp (lnN + R * LN) := by
    rw [Real.exp_add, Real.exp_log (by positivity), ← pow_eq_exp_log (by positivity)]
    linarith
  have hpat0 : 0 ≤ patB C d (d + R + 1) (2 * ((2 : ℝ) ^ j * ((d : ℝ) + 1) ^ R * 2 ^ R / 2 ^ d)) := by
    unfold patB; positivity
  calc 2 * ((7 * (N : ℝ) * ((N : ℝ) + 1) ^ R) *
        patB C d (d + R + 1) (2 * ((2 : ℝ) ^ j * ((d : ℝ) + 1) ^ R * 2 ^ R / 2 ^ d)))
      = (2 * (7 * (N : ℝ) * ((N : ℝ) + 1) ^ R)) *
        patB C d (d + R + 1) (2 * ((2 : ℝ) ^ j * ((d : ℝ) + 1) ^ R * 2 ^ R / 2 ^ d)) := by ring
    _ ≤ (14 * Real.exp (lnN + R * LN)) * ((32 + 2 * C) * Real.exp (-(d * ℓ2 / 8) + G)) :=
        mul_le_mul hpre hpat hpat0 (by positivity)
    _ = Real.exp (Real.log K0 + (lnN + R * LN) + (-(d * ℓ2 / 8) + G)) := by
        rw [Real.exp_add (Real.log K0 + (lnN + R * LN)) (-(d * ℓ2 / 8) + G),
          Real.exp_add (Real.log K0) (lnN + R * LN), Real.exp_log hK0pos, hK0]; ring
    _ ≤ Real.exp (-((N : ℝ) / 420)) := by
        apply Real.exp_le_exp.2
        have hRLN : (R : ℝ) * LN ≤ (433 / 100 * lnN + 13) * (lnN + 1) :=
          mul_le_mul hR1 hLNle hLN0 (by positivity)
        have hdl : (N : ℝ) / 30 * 0.6931471803 ≤ d * ℓ2 := by
          have := mul_le_mul hdr hl2a.le (by norm_num) (by positivity); linarith
        rw [hG]
        nlinarith

/-! ### `cov_far` -/

/-- **Lemma COV' (far pairs)**: `|Cov(Y_K, Y_{K'})| ≤ e^{-N/420}` when `3|K ∩ K'| ≤ d`. -/
theorem cov_far (hGC : GCStmt) (hESL : EntrySumLawStmt) :
    ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide), ∀ f ∈ GoodX3 N s r0 x σ,
      ∀ K ∈ famX3 N s r0 x σ (b1Ext f), ∀ K' ∈ famX3 N s r0 x σ (b1Ext f),
        3 * (K ∩ K').card ≤ dX N →
        |(rowsOutM (sensRows s r0) {g | YK N s K (glueRows (sensRows s r0) f g) ∧
              YK N s K' (glueRows (sensRows s r0) f g)}).toReal -
            (rowsOutM (sensRows s r0) {g | YK N s K (glueRows (sensRows s r0) f g)}).toReal *
              (rowsOutM (sensRows s r0) {g | YK N s K' (glueRows (sensRows s r0) f g)}).toReal| ≤
          Real.exp (-((N : ℝ) / 420)) := by
  obtain ⟨C, hC, hac⟩ := ac_atom hGC hESL
  filter_upwards [covfar_final C hC, covfar_large] with N hfin hlarge s r0 x σ f _ K hKm K' hK'm hj
  obtain ⟨hFsz, hd1, hm2, hrm⟩ := hlarge
  set d := dX N with hd
  set R := rD N with hR
  have hKc : K.card = d := famX3_card hKm
  set j := (K ∩ K').card with hjdef
  set G := gluW s r0 f with hGdef
  set X : Set (Param N) := {w | YK N s K (G w)} with hX
  set X' : Set (Param N) := {w | YK N s K' (G w)} with hX'
  set CK : Finset (State N × Fin N) := (RDrows N s K ∪ {s}) ×ˢ univ with hCK
  set CK' : Finset (State N × Fin N) := (RDrows N s K' ∪ {s}) ×ˢ univ with hCK'
  set Csh := CK ∩ CK' with hCsh
  set c0 : Param N := fun _ _ => 1 / 2 with hc0
  set Xt : Set (Param N) := {w | YK N s K (G (replE Csh w c0))} with hXt
  set δ : ℝ := (2 : ℝ) ^ j * ((d : ℝ) + 1) ^ R * 2 ^ R / 2 ^ d with hδ
  set Bad : Set (Param N) := {w | ¬ NDeg N s K (2 * δ) (G w)} with hBad
  -- to the cube
  have e1 : rowsOutM (sensRows s r0) {g | YK N s K (glueRows (sensRows s r0) f g) ∧ YK N s K' (glueRows (sensRows s r0) f g)} =
      cubeM N (X ∩ X') := rowsOutM_glue_eq_cubeM (sensRows s r0) f {w | YK N s K w ∧ YK N s K' w}
  have e2 : rowsOutM (sensRows s r0) {g | YK N s K (glueRows (sensRows s r0) f g)} = cubeM N X :=
    rowsOutM_glue_eq_cubeM (sensRows s r0) f {w | YK N s K w}
  have e3 : rowsOutM (sensRows s r0) {g | YK N s K' (glueRows (sensRows s r0) f g)} = cubeM N X' :=
    rowsOutM_glue_eq_cubeM (sensRows s r0) f {w | YK N s K' w}
  rw [e1, e2, e3]
  -- independence
  have hGm := measurable_gluW s r0 f
  have hrm' : Measurable fun w : Param N => replE Csh w c0 := by
    refine Measurable.of_eval fun r => Measurable.of_eval fun i => ?_
    by_cases h : (r, i) ∈ Csh
    · simp only [replE, h, if_true]; exact measurable_const
    · simp only [replE, h, if_false]; exact (measurable_pi_apply i).comp (measurable_pi_apply r)
  have hXm' : MeasurableSet X' := hGm (measurableSet_YK s K')
  have hXtm : MeasurableSet Xt := (hGm.comp hrm') (measurableSet_YK s K)
  have hX'd : DetOnE CK' X' := detOnE_gluW f (YK_detOn s K')
  have hXtd : DetOnE (CK \ CK') Xt := by
    intro w w' hw
    have h := detOnE_gluW f (YK_detOn s K) (replE Csh w c0) (replE Csh w' c0)
    refine h fun q hq => ?_
    by_cases hqs : q ∈ Csh
    · have : (q.1, q.2) ∈ Csh := hqs
      simp only [replE, this, if_true]
    · have : (q.1, q.2) ∉ Csh := hqs
      simp only [replE, this, if_false]
      apply hw
      rw [Finset.mem_sdiff]
      exact ⟨hq, fun h' => hqs (mem_inter.2 ⟨hq, h'⟩)⟩
  have hind : cubeM N (Xt ∩ X') = cubeM N Xt * cubeM N X' :=
    cubeM_inter_eq_mul_of_detOnE sdiff_disjoint hXtm hXm' hXtd hX'd
  -- the moves of the statistics
  have hmove : ∀ w : Param N,
      (∀ k, |fK (G w) s K k - fK (G (replE Csh w c0)) s K k| ≤ δ) ∧
      (∀ jj ∈ univ \ K, ∀ k, |hK (G w) s K jj k - hK (G (replE Csh w c0)) s K jj k| ≤ δ) ∧
      (∀ A, A ⊆ univ \ K → ((univ \ K) \ A).card ≤ rD N → ∀ k,
        |effDevA (G w) s A s k - effDevA (G (replE Csh w c0)) s A s k| ≤ δ) := by
    intro w
    have hs : G w s = G (replE Csh w c0) s := by
      rw [hGdef, gluW_of_mem f _ (mem_sensRows_s s r0), gluW_of_mem f _ (mem_sensRows_s s r0)]
    have hRr : ∀ r, r ∉ RDrows N s K' → G w r = G (replE Csh w c0) r := by
      intro r hr
      by_cases hF : r ∈ (sensRows s r0)
      · rw [hGdef, gluW_of_mem f _ hF, gluW_of_mem f _ hF]
      · rw [hGdef, gluW_of_not_mem f _ hF, gluW_of_not_mem f _ hF]
        funext i
        have hrs : r ≠ s := fun h => hF (h ▸ mem_sensRows_s s r0)
        have : (r, i) ∉ Csh := by
          intro h
          have h2 := (mem_inter.1 h).2
          rw [hCK', mem_product, mem_union, mem_singleton] at h2
          rcases h2.1 with h3 | h3
          · exact hr h3
          · exact hrs h3
        simp only [replE, this, if_false]
    have hdiff := fun A t k => effDevA_diff_le (G w) (G (replE Csh w c0)) s A t k (RDrows N s K') hs hRr
    have hsh : ∀ E : Finset (Fin N), Disjoint E K → E.card ≤ rD N →
        (((agree (univ \ (K ∪ E)) s) ∩ RDrows N s K').card : ℝ) ≤ 2 ^ j * ((d : ℝ) + 1) ^ R * 2 ^ R := by
      intro E hEK hE
      have := sh_rows s K K' E hEK hE
      rw [hKc] at this
      exact_mod_cast this
    have hX0 : (0 : ℝ) ≤ 2 ^ j * ((d : ℝ) + 1) ^ R * 2 ^ R := by positivity
    have h2d : (0 : ℝ) < 2 ^ d := by positivity
    refine ⟨fun k => ?_, fun jj hjj k => ?_, fun A hA hr k => ?_⟩
    · refine (hdiff _ _ k).trans ?_
      rw [card_agree_C0 s K, hKc]
      have := hsh ∅ (disjoint_empty_left _) (by simp)
      rw [union_empty] at this
      push_cast
      exact div_le_div_of_nonneg_right this h2d.le
    · refine (hdiff _ _ k).trans ?_
      rw [card_agree_Cj s K jj, hKc]
      have hsub : agree (univ \ K) (flipAt jj s) ∩ RDrows N s K' ⊆
          agree (univ \ (K ∪ {jj})) s ∩ RDrows N s K' := by
        intro r hr
        rw [mem_inter] at hr ⊢
        refine ⟨?_, hr.2⟩
        rw [mem_agree]
        intro i hi
        by_contra hne
        rcases Cj_diff hr.1 i hne with h1 | h1
        · simp only [Finset.mem_sdiff, mem_univ, true_and, mem_union] at hi; exact hi (Or.inl h1)
        · simp only [Finset.mem_sdiff, mem_univ, true_and, mem_union] at hi; exact hi (Or.inr h1)
      have hjK : Disjoint {jj} K := by
        rw [disjoint_singleton_left]; exact (Finset.mem_sdiff.1 hjj).2
      have := hsh {jj} hjK (by rw [card_singleton]; exact one_le_rD N)
      have hc : ((agree (univ \ K) (flipAt jj s) ∩ RDrows N s K').card : ℝ) ≤
          ((agree (univ \ (K ∪ {jj})) s ∩ RDrows N s K').card : ℝ) := by
        exact_mod_cast card_le_card hsub
      push_cast
      exact div_le_div_of_nonneg_right (hc.trans this) h2d.le
    · refine (hdiff _ _ k).trans ?_
      set E := (univ \ K) \ A with hE
      have hEK : Disjoint E K := by
        rw [hE]; exact disjoint_of_subset_left sdiff_subset sdiff_disjoint
      have hAeq : A = univ \ (K ∪ E) := by
        ext i
        simp only [hE, Finset.mem_sdiff, mem_univ, true_and, mem_union]
        constructor
        · intro hi
          have := hA hi
          simp only [Finset.mem_sdiff, mem_univ, true_and] at this
          tauto
        · intro hi; push_neg at hi; exact hi.2 hi.1
      have h1 := hsh E hEK hr
      rw [← hAeq] at h1
      have hcard : (2 : ℝ) ^ d ≤ (agree A s).card := by
        rw [card_agree]
        have hAc : A.card ≤ N - d := by
          have := card_le_card hA
          rw [card_sdiff_of_subset (subset_univ K), card_univ, Fintype.card_fin, hKc] at this
          exact this
        have : d ≤ N - A.card := by
          have := card_le_univ K; rw [Fintype.card_fin, hKc] at this; omega
        push_cast
        exact pow_le_pow_right₀ (by norm_num) this
      calc ((agree A s ∩ RDrows N s K').card : ℝ) / (agree A s).card
          ≤ (2 ^ j * ((d : ℝ) + 1) ^ R * 2 ^ R) / (agree A s).card :=
            div_le_div_of_nonneg_right h1 (Nat.cast_nonneg _)
        _ ≤ δ := div_le_div_of_nonneg_left hX0 h2d hcard
  -- the coupling
  have hcoup : ∀ w, w ∉ Bad → (w ∈ X ↔ w ∈ Xt) := by
    intro w hw
    have hnd : NDeg N s K (2 * δ) (G w) := by
      by_contra h; exact hw h
    obtain ⟨hf1, hh1, he1⟩ := hmove w
    exact YK_stable hm2 hrm hf1 hh1 he1 hnd
  have hcov := cov_coupling hind hcoup
  -- the bad set
  have hd1' : 1 ≤ K.card := by rw [hKc]; exact hd1
  have hF : 2 * (sensRows s r0).card ≤ 2 ^ K.card := by
    rw [hKc]
    have := card_sensRows_le s r0
    calc 2 * (sensRows s r0).card ≤ 2 * (2 * (N + 1) ^ 4) := by omega
      _ = 4 * (N + 1) ^ 4 := by ring
      _ ≤ 2 ^ d := hFsz
  set M := d + R + 1 with hM
  set P := patB C d M (2 * δ) with hP
  have hηpos : 0 < 2 * δ := by positivity
  have hP0 : 0 ≤ P := by rw [hP]; unfold patB; positivity
  have hsub : Bad ⊆ ((⋃ k' ∈ (univ : Finset (Fin N)), ⋃ c ∈ (univ : Finset (Fin 5)),
      {w | |fK (G w) s K k' - thrF N c| ≤ 2 * δ}) ∪
      (⋃ k ∈ K, ⋃ jj ∈ univ \ K, {w | |nAt N s K k jj (G w) - 0| ≤ 2 * δ})) ∪
      (⋃ k ∈ K, ⋃ A ∈ Aset N K, {w | |dAt N s K k A (G w) - 0| ≤ 2 * δ}) := by
    intro w hw
    simp only [hBad, Set.mem_ofPred_eq, NDeg, not_and_or, not_forall, not_lt] at hw
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, mem_univ, exists_true_left,
      sub_zero]
    rcases hw with h | h | h
    · obtain ⟨k', c, h⟩ := h; exact Or.inl (Or.inl ⟨k', c, h⟩)
    · obtain ⟨k, hk, jj, hjj, h⟩ := h; exact Or.inl (Or.inr ⟨k, hk, jj, hjj, h⟩)
    · obtain ⟨k, hk, A, hA, h⟩ := h; exact Or.inr ⟨k, hk, A, hA, h⟩
  have hB1 := meas_biUnion2_le (N := N) (univ : Finset (Fin N)) (fun _ => (univ : Finset (Fin 5)))
    (fun k' c => {w | |fK (G w) s K k' - thrF N c| ≤ 2 * δ}) P hP0
    (fun k' _ c _ => by
      have := atom_f hac N s r0 f K hd1' hF M (by rw [hKc]; omega) k' (thrF N c) (2 * δ) hηpos
      rw [hKc] at this; exact this) 5 (fun _ _ => by simp)
  have hB2 := meas_biUnion2_le (N := N) K (fun _ => univ \ K)
    (fun k jj => {w | |nAt N s K k jj (G w) - 0| ≤ 2 * δ}) P hP0
    (fun k _ jj hjj => by
      have := atom_n hac N s r0 f K hd1' hF M (by rw [hKc]; omega) k jj hjj 0 (2 * δ) hηpos
      rw [hKc] at this; exact this) N
    (fun _ _ => by
      have := card_le_card (sdiff_subset : univ \ K ⊆ univ)
      rwa [card_univ, Fintype.card_fin] at this)
  have hB3 := meas_biUnion2_le (N := N) K (fun _ => Aset N K)
    (fun k A => {w | |dAt N s K k A (G w) - 0| ≤ 2 * δ}) P hP0
    (fun k _ A hA => by
      have := atom_d hac N s r0 f K hd1' hF M k A hA (by rw [hKc]) 0 (2 * δ) hηpos
      rw [hKc] at this; exact this) ((N + 1) ^ rD N) (fun _ _ => card_Aset_le K)
  have hKN : (K.card : ℝ) ≤ N := by
    have := card_le_univ K; rw [Fintype.card_fin] at this; exact_mod_cast this
  have hBadle : cubeM N Bad ≤ ENNReal.ofReal (7 * (N : ℝ) * ((N : ℝ) + 1) ^ R * P) := by
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    refine (add_le_add ((measure_union_le _ _).trans (add_le_add hB1 hB2)) hB3).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    simp only [card_univ, Fintype.card_fin]
    push_cast
    have hN1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ R := one_le_pow₀ (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
    have hNN : (N : ℝ) ≤ ((N : ℝ) + 1) ^ R := by
      have : (N : ℝ) + 1 ≤ ((N : ℝ) + 1) ^ R := by
        calc (N : ℝ) + 1 = ((N : ℝ) + 1) ^ 1 := (pow_one _).symm
          _ ≤ ((N : ℝ) + 1) ^ R := pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
              (one_le_rD N)
      linarith
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hK0 : (0 : ℝ) ≤ K.card := Nat.cast_nonneg _
    have t1 : (K.card : ℝ) * N * P ≤ N * ((N : ℝ) + 1) ^ R * P := by
      apply mul_le_mul_of_nonneg_right _ hP0
      exact mul_le_mul hKN hNN hN0 hN0
    have t2 : (K.card : ℝ) * ((N : ℝ) + 1) ^ R * P ≤ N * ((N : ℝ) + 1) ^ R * P := by
      apply mul_le_mul_of_nonneg_right _ hP0
      exact mul_le_mul_of_nonneg_right hKN (by positivity)
    have t3 : (N : ℝ) * 5 * P ≤ 5 * (N * ((N : ℝ) + 1) ^ R * P) := by
      have : (N : ℝ) * P ≤ N * ((N : ℝ) + 1) ^ R * P := by
        have := mul_le_mul_of_nonneg_left hN1 (mul_nonneg hN0 hP0); nlinarith
      nlinarith
    nlinarith
  have hBadr : (cubeM N Bad).toReal ≤ 7 * (N : ℝ) * ((N : ℝ) + 1) ^ R * P :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hBadle
  have hfin' := hfin j hj
  calc _ ≤ 2 * (cubeM N Bad).toReal := hcov
    _ ≤ 2 * (7 * (N : ℝ) * ((N : ℝ) + 1) ^ R * P) := by linarith
    _ ≤ Real.exp (-((N : ℝ) / 420)) := hfin'

end Census
end IIT

#print axioms IIT.Census.cov_far
