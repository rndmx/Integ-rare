/-
Census, B1 lemma LT2, module M4 part 5d: **the variance floor**.

Eventually, for every `s`, off probability `e^{-2N}`: for all columns `j` and `β`,
`Σ_{r ∈ H, r_j = β} P_ns(r)² ≥ σ_N²/16`.
Events: `A(j,β)` (lower tail of the heavy-window mass, `2N` events) and `B(D)` (non-isolated mass along a shift
`D`, `|D| ∈ [1,4]`, `≤ (N+1)⁴` events), each of probability `≤ e^{-3N}`.
-/
import IIT.Census.B1LT2Floor3

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

lemma lt2_log109 : (105 / 1000 : ℝ) ≤ Real.log (10 / 9) := by
  have hq : (((105 / 1000 : ℚ)) : ℝ) ≤ Real.log (((10 / 9 : ℚ)) : ℝ) := crLog_ge 0 40 (by decide +kernel)
  push_cast at hq; exact hq

lemma lt2_exp_le_109 (N : ℕ) : Real.exp (105 / 1000 * N) ≤ (10 / 9 : ℝ) ^ N := by
  rw [← Real.exp_log (show (0 : ℝ) < 10 / 9 by norm_num), ← Real.exp_nat_mul, Real.exp_le_exp]
  have := lt2_log109; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; nlinarith

lemma lt2_sig4_ratio (N : ℕ) : (sigN N ^ 2) ^ 2 / (2 / 5 : ℝ) ^ N = (10 / 9 : ℝ) ^ N := by
  rw [lt2_sigN_sq, ← pow_mul, mul_comm, pow_mul, ← div_pow]; norm_num

lemma lt2_sig_theta (N : ℕ) : sigN N ^ 2 / lt2θ N ^ 2 = Real.exp ((N : ℝ) / 200) := by
  have hσ : 0 < sigN N ^ 2 := by unfold sigN; positivity
  rw [lt2θ_sq, div_mul_eq_div_div, div_self hσ.ne', one_div, ← Real.exp_neg]; ring_nf

lemma lt2_meas_le_of_real {X : Set (Param N)} {b : ℝ} (h : (cubeM N).real X ≤ b) : cubeM N X ≤ ENNReal.ofReal b := by
  haveI : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  rw [← ofReal_measureReal (measure_ne_top _ _)]; exact ENNReal.ofReal_le_ofReal h

lemma lt2_two_third_q (q : ℝ) : (2 : ℝ) ^ N * ((1 / 3 : ℝ) ^ N * q) = sigN N ^ 2 * q := by
  rw [lt2_sigN_sq, ← mul_assoc, ← mul_pow]; norm_num

lemma lt2_q_small {q : ℝ} (hq : q ≤ Real.exp (-(257 / 10000 * (N : ℝ))))
    (e5 : ((N : ℝ) + 1) ^ 4 * 128 ≤ Real.exp (257 / 10000 * N)) : ((N : ℝ) + 1) ^ 4 * q ≤ 1 / 128 := by
  have h1 : ((N : ℝ) + 1) ^ 4 * q ≤ ((N : ℝ) + 1) ^ 4 * Real.exp (-(257 / 10000 * (N : ℝ))) :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  have h2 : Real.exp (257 / 10000 * (N : ℝ)) * Real.exp (-(257 / 10000 * (N : ℝ))) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have h3 := Real.exp_pos (-(257 / 10000 * (N : ℝ)))
  have h4 : ((N : ℝ) + 1) ^ 4 * 128 * Real.exp (-(257 / 10000 * (N : ℝ))) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right e5 h3.le; rw [h2] at this; exact this
  linarith

lemma lt2_ball_small (e6 : ((N : ℝ) + 1) ^ 6 * 32 ≤ Real.exp ((N : ℝ) / 200)) :
    ((N : ℝ) + 1) ^ 6 * lt2θ N ^ 2 ≤ sigN N ^ 2 / 32 := by
  rw [lt2θ_sq]
  have hσ : 0 < sigN N ^ 2 := by unfold sigN; positivity
  have h2 : Real.exp ((N : ℝ) / 200) * Real.exp (-(N : ℝ) / 200) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have h3 := Real.exp_pos (-(N : ℝ) / 200)
  have h4 : ((N : ℝ) + 1) ^ 6 * 32 * Real.exp (-(N : ℝ) / 200) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right e6 h3.le; rw [h2] at this; exact this
  have h5 : ((N : ℝ) + 1) ^ 6 * Real.exp (-(N : ℝ) / 200) ≤ 1 / 32 := by linarith
  calc ((N : ℝ) + 1) ^ 6 * (sigN N ^ 2 * Real.exp (-(N : ℝ) / 200))
      = sigN N ^ 2 * (((N : ℝ) + 1) ^ 6 * Real.exp (-(N : ℝ) / 200)) := by ring
    _ ≤ sigN N ^ 2 * (1 / 32) := mul_le_mul_of_nonneg_left h5 hσ.le
    _ = sigN N ^ 2 / 32 := by ring

/-- The deterministic core of the floor. -/
lemma lt2_floor_incl (s : State N) (w : Param N) (j : Fin N) (β : Bool) {m q : ℝ}
    (hEf : (1 / 3 : ℝ) ^ N / 2 ≤ m) (hN1 : 1 ≤ N)
    (hA : (agree {j} (fun _ => β)).card * m - ∑ r ∈ agree {j} (fun _ => β), lt2fH (w r) < sigN N ^ 2 / 8)
    (hB : ∀ D ∈ lt2Dset N, ∑ r : State N, lt2gNs (w r) ^ 2 * lt2hL (w (lt2Xor r D)) ≤
      sigN N ^ 2 / (64 * ((N : ℝ) + 1) ^ 4) + 2 * (sigN N ^ 2 * q))
    (hq0 : 0 ≤ q) (hq' : ((N : ℝ) + 1) ^ 4 * q ≤ 1 / 128)
    (hb6 : ((N : ℝ) + 1) ^ 6 * lt2θ N ^ 2 ≤ sigN N ^ 2 / 32) :
    sigN N ^ 2 / 16 ≤ ∑ r ∈ (lt2H s w).filter (fun r => r ∈ agree {j} (fun _ => β)), lt2gNs (w r) ^ 2 := by
  set σ2 := sigN N ^ 2 with hσ2def
  have hσ : 0 < σ2 := by unfold sigN at hσ2def; rw [hσ2def]; positivity
  have hdet := lt2_floor_det s w j (fun _ => β)
  have hcard : ((agree ({j} : Finset (Fin N)) (fun _ => β)).card : ℝ) = (2 : ℝ) ^ (N - 1) := by
    rw [card_agree, card_singleton]; push_cast; rfl
  have h2N : (2 : ℝ) ^ (N - 1) * 2 = 2 ^ N := by rw [← pow_succ]; congr 1; omega
  have hhalf : σ2 / 4 ≤ (agree {j} (fun _ => β)).card * m := by
    rw [hcard]
    have e : σ2 / 4 = 2 ^ (N - 1) * ((1 / 3 : ℝ) ^ N / 2) := by
      rw [hσ2def, lt2_sigN_sq, show (2 / 3 : ℝ) ^ N = 2 ^ N * (1 / 3) ^ N by rw [← mul_pow]; norm_num,
        ← h2N]; ring
    rw [e]; exact mul_le_mul_of_nonneg_left hEf (by positivity)
  have hcD := lt2_card_Dset (N := N)
  have hBsum : ∑ D ∈ lt2Dset N, ∑ r : State N, lt2gNs (w r) ^ 2 * lt2hL (w (lt2Xor r D)) ≤ σ2 / 32 := by
    calc ∑ D ∈ lt2Dset N, ∑ r : State N, lt2gNs (w r) ^ 2 * lt2hL (w (lt2Xor r D))
        ≤ ∑ _D ∈ lt2Dset N, (σ2 / (64 * ((N : ℝ) + 1) ^ 4) + 2 * (σ2 * q)) := Finset.sum_le_sum hB
      _ = (lt2Dset N).card * (σ2 / (64 * ((N : ℝ) + 1) ^ 4) + 2 * (σ2 * q)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((N : ℝ) + 1) ^ 4 * (σ2 / (64 * ((N : ℝ) + 1) ^ 4) + 2 * (σ2 * q)) :=
          mul_le_mul_of_nonneg_right hcD (by positivity)
      _ = σ2 / 64 + 2 * σ2 * (((N : ℝ) + 1) ^ 4 * q) := by
          have : ((N : ℝ) + 1) ^ 4 ≠ 0 := by positivity
          field_simp
      _ ≤ σ2 / 32 := by nlinarith
  have hball : ∑ r ∈ ballR s 6, lt2gNs (w r) ^ 2 ≤ σ2 / 32 := by
    calc ∑ r ∈ ballR s 6, lt2gNs (w r) ^ 2 ≤ ∑ _r ∈ ballR s 6, lt2θ N ^ 2 :=
          Finset.sum_le_sum fun r _ => pow_le_pow_left₀ (lt2gNs_nonneg _) (lt2gNs_le _) 2
      _ = (ballR s 6).card * lt2θ N ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((N : ℝ) + 1) ^ 6 * lt2θ N ^ 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_ballR_le s 6) (sq_nonneg _)
      _ ≤ σ2 / 32 := hb6
  linarith

/-- **The variance floor.** -/
theorem lt2_varfloor : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N {w | ∃ j : Fin N, ∃ β : Bool,
      ∑ r ∈ (lt2H s w).filter (fun r => r ∈ agree {j} (fun _ => β)), lt2gNs (w r) ^ 2 < sigN N ^ 2 / 16} ≤
      ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
  filter_upwards [lt2_Ef_half, eventually_ge_atTop 1,
    cr_ev_poly_exp 1 (Real.log 768) (δ := 105 / 1000) (by norm_num),
    cr_ev_poly_exp 1 (Real.log 96) (δ := 1 / 200) (by norm_num),
    cr_ev_poly_exp 9 (Real.log 196608) (δ := 105 / 1000) (by norm_num),
    cr_ev_poly_exp 5 (Real.log 1536) (δ := 1 / 200) (by norm_num),
    cr_ev_poly_exp 4 (Real.log 128) (δ := 257 / 10000) (by norm_num),
    cr_ev_poly_exp 6 (Real.log 32) (δ := 1 / 200) (by norm_num),
    cr_ev_poly_exp 4 (Real.log 3) (δ := 1) (by norm_num)] with N hEf hN1 e1 e2 e3 e4 e5 e6 e7 s
  haveI : IsProbabilityMeasure (rowM N) := by unfold rowM; infer_instance
  haveI : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  rw [Real.exp_log (by norm_num)] at e1 e2 e3 e4 e5 e6 e7
  rw [pow_one] at e1 e2
  have r200 : (1 / 200 : ℝ) * N = (N : ℝ) / 200 := by ring
  rw [r200] at e2 e4 e6
  have hθpos : 0 < lt2θ N ^ 2 := by unfold lt2θ; positivity
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hP : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith
  set σ2 := sigN N ^ 2 with hσ2def
  have hσ2 : 0 < σ2 := by unfold sigN at hσ2def; rw [hσ2def]; positivity
  have hθ2 : lt2θ N ^ 2 = σ2 * Real.exp (-(N : ℝ) / 200) := lt2θ_sq N
  have hE200 : Real.exp ((N : ℝ) / 200) * Real.exp (-(N : ℝ) / 200) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  set m := ∫ x, lt2fH x ∂rowM N
  set q := ∫ x, lt2hL x ∂rowM N
  have hq := lt2_q_le (N := N)
  have hq0 : 0 ≤ q := integral_nonneg lt2hL_nonneg
  set εA := σ2 / 8
  set εB := σ2 / (64 * ((N : ℝ) + 1) ^ 4)
  set BadA : Fin N → Bool → Set (Param N) := fun j β =>
    {w | εA ≤ (agree {j} (fun _ => β)).card * m - ∑ r ∈ agree {j} (fun _ => β), lt2fH (w r)}
  set BadB : Finset (Fin N) → Set (Param N) := fun D =>
    {w | εB + 2 * (2 ^ N * ((1 / 3 : ℝ) ^ N * q)) ≤ ∑ r : State N, lt2gNs (w r) ^ 2 * lt2hL (w (lt2Xor r D))}
  -- probability of each event
  have p3 : ∀ X Y : ℝ, 3 * N ≤ X → 3 * N ≤ Y → Real.exp (-min X Y) ≤ Real.exp (-(3 * N)) :=
    fun X Y hX hY => Real.exp_le_exp.2 (neg_le_neg (le_min hX hY))
  have pA : ∀ j β, cubeM N (BadA j β) ≤ ENNReal.ofReal (Real.exp (-(3 * N))) := by
    intro j β
    refine lt2_meas_le_of_real ((lt2_A_tail j (fun _ => β) (ε := εA) (by positivity)).trans (p3 _ _ ?_ ?_))
    · have h := lt2_sig4_ratio N
      have hr : εA ^ 2 / (4 * (2 / 5 : ℝ) ^ N) = (10 / 9 : ℝ) ^ N / 256 := by
        rw [← h]; simp only [εA]; field_simp; ring
      rw [hr]; have := lt2_exp_le_109 N; linarith
    · have hr : εA / (2 * (2 * lt2θ N ^ 2)) = (sigN N ^ 2 / lt2θ N ^ 2) / 32 := by
        simp only [εA]; field_simp; ring
      rw [hr, lt2_sig_theta]; linarith
  have pB : ∀ D ∈ lt2Dset N, cubeM N (BadB D) ≤ ENNReal.ofReal (Real.exp (-(3 * N))) := by
    intro D hD
    obtain ⟨d, hd⟩ := Finset.card_pos.1 (by have := (mem_filter.1 hD).2.1; omega : 0 < D.card)
    refine lt2_meas_le_of_real ((lt2_B_tail hd (ε := εB) (by positivity)).trans (p3 _ _ ?_ ?_))
    · have h := lt2_sig4_ratio N
      have hr : εB ^ 2 / (4 * (4 * (2 / 5 : ℝ) ^ N)) = (10 / 9 : ℝ) ^ N / (65536 * ((N : ℝ) + 1) ^ 8) := by
        rw [← h]; simp only [εB]; field_simp; ring
      rw [hr, le_div_iff₀ (by positivity)]
      have := lt2_exp_le_109 N
      have hp9 : ((N : ℝ) + 1) ^ 9 = ((N : ℝ) + 1) ^ 8 * ((N : ℝ) + 1) := by ring
      have hp8 := pow_pos (show (0 : ℝ) < (N : ℝ) + 1 by linarith) 8
      have : 3 * (N : ℝ) * (65536 * ((N : ℝ) + 1) ^ 8) ≤ ((N : ℝ) + 1) ^ 9 * 196608 := by
        rw [hp9]; nlinarith
      linarith
    · have hr : εB / (2 * (2 * (2 * lt2θ N ^ 2))) = (sigN N ^ 2 / lt2θ N ^ 2) / (512 * ((N : ℝ) + 1) ^ 4) := by
        simp only [εB]; field_simp; ring
      rw [hr, lt2_sig_theta, le_div_iff₀ (by positivity)]
      have hp5 : ((N : ℝ) + 1) ^ 5 = ((N : ℝ) + 1) ^ 4 * ((N : ℝ) + 1) := by ring
      have hp4 := pow_pos (show (0 : ℝ) < (N : ℝ) + 1 by linarith) 4
      have : 3 * (N : ℝ) * (512 * ((N : ℝ) + 1) ^ 4) ≤ ((N : ℝ) + 1) ^ 5 * 1536 := by
        rw [hp5]; nlinarith
      linarith
  -- the inclusion
  have hq' : ((N : ℝ) + 1) ^ 4 * q ≤ 1 / 128 := lt2_q_small hq e5
  have hb6 : ((N : ℝ) + 1) ^ 6 * lt2θ N ^ 2 ≤ σ2 / 32 := lt2_ball_small e6
  have hsub : {w | ∃ j : Fin N, ∃ β : Bool,
      ∑ r ∈ (lt2H s w).filter (fun r => r ∈ agree {j} (fun _ => β)), lt2gNs (w r) ^ 2 < σ2 / 16} ⊆
      (⋃ j : Fin N, ⋃ β : Bool, BadA j β) ∪ ⋃ D ∈ lt2Dset N, BadB D := by
    intro w hw
    obtain ⟨j, β, hlt⟩ := hw
    by_contra hnot
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hnot
    obtain ⟨hA, hB⟩ := hnot
    have hA' := hA j β
    simp only [BadA, Set.mem_setOf_eq, not_le] at hA'
    have hB' : ∀ D ∈ lt2Dset N, ∑ r : State N, lt2gNs (w r) ^ 2 * lt2hL (w (lt2Xor r D)) ≤
        σ2 / (64 * ((N : ℝ) + 1) ^ 4) + 2 * (σ2 * q) := fun D hD => by
      have := hB D hD; simp only [BadB, Set.mem_setOf_eq, not_le] at this
      rw [lt2_two_third_q] at this; exact this.le
    exact absurd (lt2_floor_incl s w j β hEf hN1 hA' hB' hq0 hq' hb6) (not_le.2 hlt)
  -- the sum
  have hcD := lt2_card_Dset (N := N)
  calc cubeM N {w | ∃ j : Fin N, ∃ β : Bool,
        ∑ r ∈ (lt2H s w).filter (fun r => r ∈ agree {j} (fun _ => β)), lt2gNs (w r) ^ 2 < sigN N ^ 2 / 16}
      ≤ cubeM N (⋃ j : Fin N, ⋃ β : Bool, BadA j β) + cubeM N (⋃ D ∈ lt2Dset N, BadB D) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ∑ _j : Fin N, ∑ _β : Bool, ENNReal.ofReal (Real.exp (-(3 * N))) +
          ∑ _D ∈ lt2Dset N, ENNReal.ofReal (Real.exp (-(3 * N))) := by
        refine add_le_add ((measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun j _ =>
          (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun β _ => pA j β))) ?_
        exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun D hD => pB D hD)
    _ = ENNReal.ofReal ((2 * N + (lt2Dset N).card) * Real.exp (-(3 * N))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
        rw [add_mul, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
        push_cast; ring
    _ ≤ ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : 2 * (N : ℝ) + (lt2Dset N).card ≤ Real.exp (N : ℝ) := by
          have h4 : (N : ℝ) + 1 ≤ ((N : ℝ) + 1) ^ 4 := le_self_pow₀ hP (by norm_num)
          rw [one_mul] at e7
          linarith
        have h2 : Real.exp (N : ℝ) * Real.exp (-(3 * N)) = Real.exp (-(2 * (N : ℝ))) := by
          rw [← Real.exp_add]; ring_nf
        rw [← h2]
        exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

end Census
end IIT
