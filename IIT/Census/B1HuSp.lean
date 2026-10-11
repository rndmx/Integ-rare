/-
Census, B1 forced leaf 7, `NatLT3Hu` part (b), `s ∈ Sp \ {tc}` (W12 §7): on `bNat`, off the proved rare events,
row `tc` is `≥ 2/3` everywhere (`htc_floor`) and row `s` is special (`X(s) ≤ x₁N`). The two rows are independent:
`P ≤ 2^N (1/3)^N e^{-N I(x₁)}`, rate `ln(3/2) + I(x₁) ≥ 1.13`.

* `two_rows_eq`, `one_row_eq`, `hsp_pair_bound`, `hsp_num`, **`natSp_rare`**.
-/
import IIT.Census.B1HuTc

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- Two distinct rows are independent. -/
lemma two_rows_eq {r0 s : State N} (hne : r0 ≠ s) (A B : Set (Fin N → ℝ)) :
    cubeM N {w | w r0 ∈ A ∧ w s ∈ B} = rowM N A * rowM N B := by
  classical
  have hset : {w : Param N | w r0 ∈ A ∧ w s ∈ B} =
      Set.pi Set.univ fun r => if r = r0 then A else if r = s then B else Set.univ := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ r
      split_ifs with h h'
      · subst h; exact h1
      · subst h'; exact h2
      · trivial
    · intro h
      refine ⟨by simpa using h r0, ?_⟩
      have := h s
      rwa [if_neg (Ne.symm hne), if_pos rfl] at this
  rw [hset]
  unfold cubeM
  rw [Measure.pi_pi]
  rw [show (fun r => rowM N (if r = r0 then A else if r = s then B else Set.univ)) =
      fun r => (if r = r0 then rowM N A else 1) * (if r = s then rowM N B else 1) by
    funext r
    by_cases h : r = r0
    · subst h; simp [hne]
    · by_cases h' : r = s
      · subst h'; simp [h]
      · simp [h, h']]
  rw [prod_mul_distrib, prod_ite_eq' univ r0, prod_ite_eq' univ s]
  simp

/-- One row. -/
lemma one_row_eq (r0 : State N) (A : Set (Fin N → ℝ)) : cubeM N {w | w r0 ∈ A} = rowM N A := by
  classical
  have hset : {w : Param N | w r0 ∈ A} = Set.pi Set.univ fun r => if r = r0 then A else Set.univ := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h r; split_ifs with h'
      · subst h'; exact h
      · trivial
    · intro h; simpa using h r0
  rw [hset]
  unfold cubeM
  rw [Measure.pi_pi]
  rw [show (fun r => rowM N (if r = r0 then A else Set.univ)) = fun r => if r = r0 then rowM N A else 1 by
    funext r; split_ifs <;> simp]
  rw [prod_ite_eq' univ r0]
  simp

/-- **One pair of rows**: `tc`-candidate `r0` above `2/3`, row `s` special. -/
theorem hsp_pair_bound (hN : 0 < N) {r0 s : State N} (hne : r0 ≠ s) :
    cubeM N {w | (∀ i, 2 / 3 ≤ clamp01 (w r0 i)) ∧ XW w s ≤ lt2x1 * N} ≤
      ENNReal.ofReal ((1 / 3 : ℝ) ^ N * Real.exp (-(N * (lt2x1 - 1 - Real.log lt2x1)))) := by
  have hx := lt2x1_bounds
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have e : {w : Param N | (∀ i, 2 / 3 ≤ clamp01 (w r0 i)) ∧ XW w s ≤ lt2x1 * N} =
      {w | w r0 ∈ {v : Fin N → ℝ | ∀ i, 2 / 3 ≤ clamp01 (v i)} ∧
        w s ∈ {v : Fin N → ℝ | ∑ i, -Real.log (clamp01 (v i)) ≤ lt2x1 * N}} := rfl
  rw [e, two_rows_eq hne]
  have hA : rowM N {v : Fin N → ℝ | ∀ i, 2 / 3 ≤ clamp01 (v i)} ≤ ENNReal.ofReal ((1 / 3 : ℝ) ^ N) := by
    rw [← one_row_eq r0]; exact htc_row_bound r0
  have hB : rowM N {v : Fin N → ℝ | ∑ i, -Real.log (clamp01 (v i)) ≤ lt2x1 * N} ≤
      ENNReal.ofReal (Real.exp (-(N * (lt2x1 - 1 - Real.log lt2x1)))) := by
    have h := rowM_negLog_sum_le (N := N) univ (x := lt2x1 * N) (by nlinarith) (by
      simp only [card_univ, Fintype.card_fin]; nlinarith)
    simp only [card_univ, Fintype.card_fin] at h
    rw [show lt2x1 * N / N = lt2x1 by field_simp] at h
    exact h
  rw [ENNReal.ofReal_mul (by positivity)]
  exact mul_le_mul' hA hB

/-- `2 · (1/3) · e^{-I(x₁)} ≤ e^{-1.035}`. -/
lemma hsp_num : 2 * (1 / 3 : ℝ) * Real.exp (-(lt2x1 - 1 - Real.log lt2x1)) ≤ Real.exp (-(1035 / 1000)) := by
  have hr := lt2_rate
  have hI : Real.log 2 + 105 / 1200 ≤ lt2x1 - 1 - Real.log lt2x1 := by linarith
  have h3 := htc_num
  have hE : Real.exp (-(lt2x1 - 1 - Real.log lt2x1)) ≤ Real.exp (-(Real.log 2 + 105 / 1200)) :=
    Real.exp_le_exp.2 (by linarith)
  rw [show -(Real.log 2 + 105 / 1200) = -Real.log 2 + -(105 / 1200) by ring, Real.exp_add,
    show Real.exp (-Real.log 2) = 2⁻¹ by rw [Real.exp_neg, Real.exp_log (by norm_num)]] at hE
  have hp := Real.exp_pos (-(105 / 1200 : ℝ))
  have hp2 := Real.exp_pos (-(lt2x1 - 1 - Real.log lt2x1))
  calc 2 * (1 / 3 : ℝ) * Real.exp (-(lt2x1 - 1 - Real.log lt2x1))
      ≤ 2 * (1 / 3) * (2⁻¹ * Real.exp (-(105 / 1200))) := by gcongr
    _ = (1 / 3) * Real.exp (-(105 / 1200)) := by ring
    _ ≤ Real.exp (-(105 / 100)) * Real.exp (-(105 / 1200)) := by gcongr
    _ = Real.exp (-(105 / 100 + 105 / 1200)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(1035 / 1000)) := Real.exp_le_exp.2 (by norm_num)

/-- **A special current row `s ≠ tc` is rare in the natural regime** (rate `1.03`). -/
theorem natSp_rare : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bNat N s ∩ {w | s ≠ tcRow w ∧ s ∈ lt2Sp w}) ≤ ENNReal.ofReal (Real.exp (-(103 / 100 * N))) := by
  set Cm : ℝ := 1035 / 1000 with hCm
  have hT3 : NatTier3Stmt Cm :=
    natTier3_of_rest6 (by norm_num) (by norm_num) natTier3Rest6_proved (lt2_at (by norm_num))
      (ltBeta_at (by norm_num))
  filter_upwards [hT3, ltBeta920_at (C := Cm) (by norm_num), ev_N_dU_top, eventually_ge_atTop 64, g_superexp Cm,
    g_absorb 7 (show (103 / 100 : ℝ) < Cm by norm_num)] with N hT hLb htop hN64 hS hA s
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
  have hA' : 7 * Real.exp (-(Cm * N)) ≤ Real.exp (-(103 / 100 * N)) := hA
  have := Real.exp_pos (-(Cm * N))
  clear_value Cm c
  linarith

end Census
end IIT
