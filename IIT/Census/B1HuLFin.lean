/-
Census, B1 forced leaf 7: **`NatLT3HuStmt λ_u (103/100)` proved, for every `λ_u`** (W12 §3, §7, §8).

`bNat ∩ {∀ triples, φ < (1 - dnEps) levTrip y_top(dnEps) β}` is split by the current row `s`:
* `s = tc`: `natTc_rareX` (copy of `natTc_rare` at rate `1.031`, B1HuTc);
* `s ∈ Sp \ {tc}`: `natSp_rareX` (copy of `natSp_rare` at rate `1.031`, B1HuSp);
* `s ∉ lt3H w` (light) and `β ≥ L σ_N` (`L = lt3LcE5`): `lt3HuL_final` (B1HuLSect, rate `1.046`);
* light and `β < L σ_N` (W12 §3.1): off LT2(L) (`lt2_provedL`, rate `1.045`) some pair has `φ ≥ 3Lσ_N > 3β`;
  B1 (`dt_B1_lt`) and Tier 3 (`NatTier3Stmt 1.035`) give `β Fᶜ_j > 3β`, i.e. `Fᶜ_j > 3`, impossible on `concC`
  (`hlb_F_le`: `Fᶜ_j ≤ 3` since `y ≤ 1` and the complement mean is `≥ 1/2 - 10⁻⁴`).
`H_u` is not used, so the statement holds for every `λ_u`.

* `natTc_rareX`, `natSp_rareX`, `hlb_F_le`, **`natLT3Hu_proved`**.
-/
import IIT.Census.B1HuLSect
import IIT.Census.B1HuSp
import IIT.Census.B1LT2LFinal

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- **`s = tc` is rare in the natural regime** (rate `1.031`). -/
theorem natTc_rareX : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bNat N s ∩ {w | s = tcRow w}) ≤ ENNReal.ofReal (Real.exp (-(1031 / 1000 * N))) := by
  set Cm : ℝ := 1035 / 1000 with hCm
  have hT3 : NatTier3Stmt Cm :=
    natTier3_of_rest6 (by norm_num) (by norm_num) natTier3Rest6_proved (lt2_at (by norm_num))
      (ltBeta_at (by norm_num))
  filter_upwards [hT3, ltBeta920_at (C := Cm) (by norm_num), ev_N_dU_top, eventually_ge_atTop 64, g_superexp Cm,
    g_absorb 7 (show (1031 / 1000 : ℝ) < Cm by norm_num)] with N hT hLb htop hN64 hS hA s
  classical
  have hN3 : 3 ≤ N := by omega
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hDN : DU N ≤ N - 1 := DU_le hN64
  have hδ : dU N (N - 1) ≤ 1 / 10000 := by
    have : dU N (N - 1) ≤ N * dU N (N - 1) := le_mul_of_one_le_left (dU_nonneg N _) (by linarith)
    linarith
  set M : Set (Param N) := {w | ∀ i, 2 / 3 ≤ clamp01 (w s i)} with hM
  set c := 2 ^ N * (N * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2))) with hc
  have hsub : bNat N s ∩ {w | s = tcRow w} ⊆
      (((bNat N s ∩ {w | ¬ ∀ j, phi (flipP s w) s univ ≤ betaW w * kF (lamCz (flipP s w) s (tcRow w)) j}) ∪
        {w | ¬ concCAt N w (tcRow w)}) ∪ (B1w N s ∩ openCube N ∩
          {w | ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 9 / 20 * betaW w})) ∪ M := by
    rintro w ⟨⟨⟨hBw, ho⟩, hNat⟩, htc⟩
    by_contra hall
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, not_or, not_and, not_not, not_forall,
      not_lt] at hall
    obtain ⟨⟨⟨h1, h2⟩, h4⟩, h5⟩ := hall
    have hT3w : ∀ j, phi (flipP s w) s univ ≤ betaW w * kF (lamCz (flipP s w) s (tcRow w)) j := by
      intro j; by_contra hc'; exact h1 ⟨⟨hBw, ho⟩, hNat⟩ ⟨j, by simpa using hc'⟩
    obtain ⟨S, hS2, hS3, hSβ⟩ := h4 ⟨hBw, ho⟩
    have hβ0 := betaW_pos ho
    have hlt := dt_B1_lt hBw (by rw [← card_pos]; omega) (dt_card_ne_univ hS3 (by omega))
    have hF : ∀ j, 9 / 20 < kF (lamCz (flipP s w) s (tcRow w)) j := by
      intro j
      have h := hT3w j
      by_contra hc'
      push Not at hc'
      have : betaW w * kF (lamCz (flipP s w) s (tcRow w)) j ≤ betaW w * (9 / 20) :=
        mul_le_mul_of_nonneg_left hc' hβ0.le
      linarith
    apply h5
    intro i
    have := htc_floor ho hDN h2 hδ (hF i)
    rwa [← htc] at this
  have hMb : cubeM N M ≤ ENNReal.ofReal (Real.exp (-(Cm * N))) := by
    refine (htc_row_bound s).trans (ENNReal.ofReal_le_ofReal ?_)
    calc (1 / 3 : ℝ) ^ N ≤ Real.exp (-(105 / 100)) ^ N := pow_le_pow_left₀ (by norm_num) htc_num N
      _ = Real.exp (-(105 / 100 * N)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-(Cm * N)) := Real.exp_le_exp.2 (by rw [hCm]; nlinarith)
  have hc0 : 0 ≤ c := by positivity
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add (hT s) (concTc_rare hN3 s))) (hLb s))) hMb).trans ?_
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le hc0, ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le,
    ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have hS' : 2 * c ≤ Real.exp (-(Cm * N)) := hS
  have hA' : 7 * Real.exp (-(Cm * N)) ≤ Real.exp (-(1031 / 1000 * N)) := hA
  have := Real.exp_pos (-(Cm * N))
  clear_value Cm c
  linarith

/-- **A special current row `s ≠ tc` is rare in the natural regime** (rate `1.031`). -/
theorem natSp_rareX : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bNat N s ∩ {w | s ≠ tcRow w ∧ s ∈ lt2Sp w}) ≤ ENNReal.ofReal (Real.exp (-(1031 / 1000 * N))) := by
  set Cm : ℝ := 1035 / 1000 with hCm
  have hT3 : NatTier3Stmt Cm :=
    natTier3_of_rest6 (by norm_num) (by norm_num) natTier3Rest6_proved (lt2_at (by norm_num))
      (ltBeta_at (by norm_num))
  filter_upwards [hT3, ltBeta920_at (C := Cm) (by norm_num), ev_N_dU_top, eventually_ge_atTop 64, g_superexp Cm,
    g_absorb 7 (show (1031 / 1000 : ℝ) < Cm by norm_num)] with N hT hLb htop hN64 hS hA s
  classical
  have hN3 : 3 ≤ N := by omega
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hDN : DU N ≤ N - 1 := DU_le hN64
  have hδ : dU N (N - 1) ≤ 1 / 10000 := by
    have : dU N (N - 1) ≤ N * dU N (N - 1) := le_mul_of_one_le_left (dU_nonneg N _) (by linarith)
    linarith
  set M : Set (Param N) := ⋃ r0 : State N, if r0 = s then ∅ else
    {w | (∀ i, 2 / 3 ≤ clamp01 (w r0 i)) ∧ XW w s ≤ lt2x1 * N} with hM
  set c := 2 ^ N * (N * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2))) with hc
  have hsub : bNat N s ∩ {w | s ≠ tcRow w ∧ s ∈ lt2Sp w} ⊆
      (((bNat N s ∩ {w | ¬ ∀ j, phi (flipP s w) s univ ≤ betaW w * kF (lamCz (flipP s w) s (tcRow w)) j}) ∪
        {w | ¬ concCAt N w (tcRow w)}) ∪ (B1w N s ∩ openCube N ∩
          {w | ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 9 / 20 * betaW w})) ∪ M := by
    rintro w ⟨⟨⟨hBw, ho⟩, hNat⟩, hne, hsp⟩
    by_contra hall
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, not_or, not_and, not_not, not_forall,
      not_lt] at hall
    obtain ⟨⟨⟨h1, h2⟩, h4⟩, h5⟩ := hall
    have hT3w : ∀ j, phi (flipP s w) s univ ≤ betaW w * kF (lamCz (flipP s w) s (tcRow w)) j := by
      intro j; by_contra hc'; exact h1 ⟨⟨hBw, ho⟩, hNat⟩ ⟨j, by simpa using hc'⟩
    obtain ⟨S, hS2, hS3, hSβ⟩ := h4 ⟨hBw, ho⟩
    have hβ0 := betaW_pos ho
    have hlt := dt_B1_lt hBw (by rw [← card_pos]; omega) (dt_card_ne_univ hS3 (by omega))
    have hF : ∀ j, 9 / 20 < kF (lamCz (flipP s w) s (tcRow w)) j := by
      intro j
      have h := hT3w j
      by_contra hc'
      push Not at hc'
      have : betaW w * kF (lamCz (flipP s w) s (tcRow w)) j ≤ betaW w * (9 / 20) :=
        mul_le_mul_of_nonneg_left hc' hβ0.le
      linarith
    apply h5
    refine Set.mem_iUnion.2 ⟨tcRow w, ?_⟩
    rw [if_neg (fun h => hne h.symm)]
    exact ⟨fun i => htc_floor ho hDN h2 hδ (hF i), (mem_filter.1 hsp).2⟩
  have hMb : cubeM N M ≤ ENNReal.ofReal (Real.exp (-(Cm * N))) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    have hone : ∀ r0 : State N, cubeM N (if r0 = s then ∅ else
        {w | (∀ i, 2 / 3 ≤ clamp01 (w r0 i)) ∧ XW w s ≤ lt2x1 * N}) ≤
        ENNReal.ofReal ((1 / 3 : ℝ) ^ N * Real.exp (-(N * (lt2x1 - 1 - Real.log lt2x1)))) := by
      intro r0
      split_ifs with h
      · simp
      · exact hsp_pair_bound (by omega) h
    refine (Finset.sum_le_sum fun r0 _ => hone r0).trans ?_
    rw [sum_const, card_state, nsmul_eq_mul]
    have h2 : ((2 ^ N : ℕ) : ENNReal) = ENNReal.ofReal ((2 : ℝ) ^ N) := by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp
    rw [h2, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hr0 : 0 ≤ 2 * (1 / 3 : ℝ) * Real.exp (-(lt2x1 - 1 - Real.log lt2x1)) := by positivity
    have key : (2 : ℝ) ^ N * ((1 / 3 : ℝ) ^ N * Real.exp (-(N * (lt2x1 - 1 - Real.log lt2x1)))) =
        (2 * (1 / 3 : ℝ) * Real.exp (-(lt2x1 - 1 - Real.log lt2x1))) ^ N := by
      rw [mul_pow, mul_pow, ← Real.exp_nat_mul]; ring_nf
    rw [key]
    calc (2 * (1 / 3 : ℝ) * Real.exp (-(lt2x1 - 1 - Real.log lt2x1))) ^ N
        ≤ Real.exp (-(1035 / 1000)) ^ N := pow_le_pow_left₀ hr0 hsp_num N
      _ = Real.exp (-(Cm * N)) := by rw [← Real.exp_nat_mul, hCm]; ring_nf
  have hc0 : 0 ≤ c := by positivity
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add (hT s) (concTc_rare hN3 s))) (hLb s))) hMb).trans ?_
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le hc0, ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le,
    ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have hS' : 2 * c ≤ Real.exp (-(Cm * N)) := hS
  have hA' : 7 * Real.exp (-(Cm * N)) ≤ Real.exp (-(1031 / 1000 * N)) := hA
  have := Real.exp_pos (-(Cm * N))
  clear_value Cm c
  linarith

/-- **Low `β` is impossible on `concC`**: `Fᶜ_j ≤ 3` (`y ≤ 1`, complement mean `≥ 1/2 - 10⁻⁴`). -/
theorem hlb_F_le {s : State N} {w : Param N} (ho : w ∈ openCube N) (hDN : DU N ≤ N - 1)
    (hcC : concCAt N w (tcRow w)) (hδ : dU N (N - 1) ≤ 1 / 10000) (j : Fin N) :
    kF (lamCz (flipP s w) s (tcRow w)) j ≤ 3 := by
  by_contra hF
  push Not at hF
  have hz : flipP s w ∈ openCube N := flipP_mem_openCube ho
  obtain ⟨mc1, -, mc3, -, mc5⟩ := lamCz_means hz s (tcRow w)
  rw [flipP_invol s w] at mc1 mc3 mc5
  have hk : kF (lamCz (flipP s w) s (tcRow w)) j =
      Real.logb 2 (clamp01 (w (tcRow w) j) / cmean w (univ \ univ.erase j) (tcRow w) j) := mc1 j (univ.erase j)
  rw [hk] at hF
  have hcard : (univ.erase j).card = N - 1 := by
    rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
  have hA := hcC j (univ.erase j) (notMem_erase j univ) (by rw [hcard]; exact hDN)
  rw [hcard] at hA
  have hAlo : 1 / 2 - 1 / 10000 ≤ cmean w (univ \ univ.erase j) (tcRow w) j := by
    have := (abs_le.1 hA).1; linarith
  have hA0 : 0 < cmean w (univ \ univ.erase j) (tcRow w) j := by linarith
  have hy0 := mc3 j
  have hpos : 0 < clamp01 (w (tcRow w) j) / cmean w (univ \ univ.erase j) (tcRow w) j := div_pos hy0 hA0
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) hpos, lt_div_iff₀ hA0] at hF
  have h8 : (2 : ℝ) ^ (3 : ℝ) = 8 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  rw [h8] at hF
  have := clamp01_le_one (w (tcRow w) j)
  linarith

/-- **Low `β`, deterministic**: on B1, the open cube and `concC`, with Tier 3 at `w`, no pair reaches `3Lσ_N` when
`β < Lσ_N` (`N ≥ 64`). -/
theorem hlb_no_pair {s : State N} {w : Param N} {L : ℝ} (hBw : w ∈ B1w N s) (ho : w ∈ openCube N)
    (hN : 3 ≤ N) (hDN : DU N ≤ N - 1) (hcC : concCAt N w (tcRow w)) (hδ : dU N (N - 1) ≤ 1 / 10000)
    (hT3w : ∀ j, phi (flipP s w) s univ ≤ betaW w * kF (lamCz (flipP s w) s (tcRow w)) j)
    (hβ : betaW w < L * sigN N) {S : Finset (Fin N)} (hS2 : S.card = 2)
    (hSφ : 3 * L * sigN N ≤ phi (flipP s w) s S) : False := by
  have hβ0 := betaW_pos ho
  have hlt := dt_B1_lt hBw (by rw [← card_pos]; omega) (dt_card_ne_univ (k := 2) hS2.le (by omega))
  set j0 : Fin N := ⟨0, by omega⟩
  have h1 := hT3w j0
  have h2 := hlb_F_le (s := s) ho hDN hcC hδ j0
  have h3 : betaW w * kF (lamCz (flipP s w) s (tcRow w)) j0 ≤ betaW w * 3 :=
    mul_le_mul_of_nonneg_left h2 hβ0.le
  linarith

/-- **`NatLT3HuStmt λ_u (103/100)`, proved** (any `λ_u`). -/
theorem natLT3Hu_proved (lamU : ℝ) : NatLT3HuStmt lamU (103 / 100) := by
  have hT3 : NatTier3Stmt (1035 / 1000) :=
    natTier3_of_rest6 (by norm_num) (by norm_num) natTier3Rest6_proved (lt2_at (by norm_num))
      (ltBeta_at (by norm_num))
  have hLT2 : LT2Stmt lt3LcE5 (1045 / 1000) := lt2_provedL lt3LcE5 lt3LcE5_one
  filter_upwards [hT3, hLT2, lt3HuL_final (L := lt3LcE5) le_rfl, natTc_rareX, natSp_rareX, ev_N_dU_top,
    eventually_ge_atTop 64, g_superexp (1035 / 1000),
    g_absorb 7 (show (103 / 100 : ℝ) < 1031 / 1000 by norm_num)] with N hT hL2 hL3 hTc hSp htop hN64 hS hA s
  classical
  have hN3 : 3 ≤ N := by omega
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hDN : DU N ≤ N - 1 := DU_le hN64
  have hδ : dU N (N - 1) ≤ 1 / 10000 := by
    have : dU N (N - 1) ≤ N * dU N (N - 1) := le_mul_of_one_le_left (dU_nonneg N _) (by linarith)
    linarith
  set c := 2 ^ N * (N * 2 ^ N * (2 * Real.exp (-((N : ℝ) ^ 2) / 2))) with hc
  have hsub : bNat N s ∩ {w | HuW s w lamU ∧ ∀ S : Finset (Fin N), S.card = 3 →
      phi (flipP s w) s S < (1 - dnEps) * levTrip * yTopW w dnEps * betaW w} ⊆
      (((((bNat N s ∩ {w | s = tcRow w}) ∪ (bNat N s ∩ {w | s ≠ tcRow w ∧ s ∈ lt2Sp w})) ∪
        (bNat N s ∩ {w | ¬ ∀ j, phi (flipP s w) s univ ≤ betaW w * kF (lamCz (flipP s w) s (tcRow w)) j})) ∪
        {w | ¬ concCAt N w (tcRow w)}) ∪
        {w | betaW w < lt3LcE5 * sigN N ∧
          ∀ S : Finset (Fin N), S.card = 2 → phi (flipP s w) s S < 3 * lt3LcE5 * sigN N}) ∪
      (openCube N ∩ {w | lt3LcE5 * sigN N ≤ betaW w ∧ s ∉ lt3H w ∧
        ∀ S : Finset (Fin N), S.card = 3 →
          phi (flipP s w) s S < (1 - dnEps) * levTrip * yTopW w dnEps * betaW w}) := by
    rintro w ⟨hb, -, hall⟩
    obtain ⟨⟨hBw, ho⟩, hNat⟩ := id hb
    by_cases htc : s = tcRow w
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨hb, htc⟩))))
    by_cases hsp : s ∈ lt2Sp w
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hb, htc, hsp⟩))))
    have hsH : s ∉ lt3H w := fun h => (mem_insert.1 h).elim htc hsp
    by_cases hβ : lt3LcE5 * sigN N ≤ betaW w
    · exact Or.inr ⟨ho, hβ, hsH, hall⟩
    by_cases hT3w : ∀ j, phi (flipP s w) s univ ≤ betaW w * kF (lamCz (flipP s w) s (tcRow w)) j
    swap
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hb, hT3w⟩)))
    by_cases hcC : concCAt N w (tcRow w)
    swap
    · exact Or.inl (Or.inl (Or.inr hcC))
    by_cases hpair : ∀ S : Finset (Fin N), S.card = 2 → phi (flipP s w) s S < 3 * lt3LcE5 * sigN N
    · exact Or.inl (Or.inr ⟨not_le.1 hβ, hpair⟩)
    exfalso
    push Not at hpair
    obtain ⟨S, hS2, hSφ⟩ := hpair
    exact hlb_no_pair hBw ho hN3 hDN hcC hδ hT3w (not_le.1 hβ) hS2 hSφ
  have hc0 : 0 ≤ c := by positivity
  refine (measure_mono hsub).trans ?_
  refine ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add
    ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add
      ((measure_union_le _ _).trans (add_le_add (hTc s) (hSp s))) (hT s))) (concTc_rare hN3 s))) (hL2 s)))
    (hL3 s))).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have e1 : Real.exp (-(1035 / 1000 * (N : ℝ))) ≤ Real.exp (-(1031 / 1000 * (N : ℝ))) :=
    Real.exp_le_exp.2 (by linarith)
  have e2 : Real.exp (-(1045 / 1000 * (N : ℝ))) ≤ Real.exp (-(1031 / 1000 * (N : ℝ))) :=
    Real.exp_le_exp.2 (by linarith)
  have e3 : Real.exp (-(1046 / 1000 * (N : ℝ))) ≤ Real.exp (-(1031 / 1000 * (N : ℝ))) :=
    Real.exp_le_exp.2 (by linarith)
  have hS' : 2 * c ≤ Real.exp (-(1035 / 1000 * (N : ℝ))) := hS
  have hA' : 7 * Real.exp (-(1031 / 1000 * (N : ℝ))) ≤ Real.exp (-(103 / 100 * (N : ℝ))) := hA
  have := Real.exp_pos (-(1035 / 1000 * (N : ℝ)))
  clear_value c
  linarith

end Census
end IIT
