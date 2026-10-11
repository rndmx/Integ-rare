/-
Census, B1 lemma LT2 at every level `L ≥ 1`: `LT2Stmt L (104/100)` (W2 Thm LT2 for every L').
-/
import IIT.Census.B1LT2L2

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

lemma lt2_union' (X Y : Set (Param N)) {a b : ENNReal} (hX : cubeM N X ≤ a) (hY : cubeM N Y ≤ b) :
    cubeM N (X ∪ Y) ≤ a + b := (measure_union_le X Y).trans (add_le_add hX hY)

/-- The `L`-dependent numerical facts. -/
theorem lt2_final_evL (L x : ℝ) (hL : 1 ≤ L) (hx1 : 1 ≤ x) : ∀ᶠ N : ℕ in atTop,
    3 * L * sigN N ≤ 1 / 5 ∧ lt2θ N ≤ sigN N / (14 * 16 * x) ∧
    Real.exp (-(lt2p2X x * (((lt2m N : ℝ)) ^ 2 / 4))) ≤ Real.exp (-(11 / 10 * (N : ℝ))) ∧
    Real.exp (-(105 / 100 * (N : ℝ))) + 7 * Real.exp (-(11 / 10 * (N : ℝ))) ≤
      Real.exp (-(1045 / 1000 * (N : ℝ))) := by
  have hp2 := lt2p2X_pos x
  filter_upwards [eventually_ge_atTop (⌈100 * L + 400 * 224 * x + 7040 / lt2p2X x⌉₊ + 1000)] with N hN
  have hNc : 100 * L + 400 * 224 * x + 7040 / lt2p2X x ≤ N := by
    have h1 : (⌈100 * L + 400 * 224 * x + 7040 / lt2p2X x⌉₊ : ℝ) ≤ N := by
      exact_mod_cast le_trans (Nat.le_add_right _ _) hN
    exact (Nat.le_ceil _).trans h1
  have hN100 : (1000 : ℝ) ≤ N := by
    have : 1000 ≤ N := le_trans (Nat.le_add_left _ _) hN
    exact_mod_cast this
  have hpos : 0 ≤ 7040 / lt2p2X x := by positivity
  have hx0 := cr_x0_bounds
  have hlo : ((crX0lo : ℚ) : ℝ) ≥ 2027 / 10000 := by unfold crX0lo; push_cast; norm_num
  have hσ : sigN N = Real.exp (-(x0 * N)) := sigN_eq_exp N
  have hexp_big : ∀ y : ℝ, 1 + y ≤ Real.exp y := fun y => by linarith [Real.add_one_le_exp y]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hσ, Real.exp_neg]
    have := hexp_big (x0 * N)
    have hpos2 := Real.exp_pos (x0 * N)
    rw [mul_inv_le_iff₀' hpos2] <;> try skip
    nlinarith
  · have h1 : lt2θ N = sigN N * Real.exp (-(N : ℝ) / 400) := by
      rw [hσ, lt2θ, lt2x1, ← Real.exp_add]; congr 1; ring
    rw [h1, le_div_iff₀ (by positivity)]
    have h2 : 14 * 16 * x * Real.exp (-(N : ℝ) / 400) ≤ 1 := by
      have := hexp_big ((N : ℝ) / 400)
      have h3 : Real.exp (-(N : ℝ) / 400) = (Real.exp ((N : ℝ) / 400))⁻¹ := by rw [← Real.exp_neg]; ring_nf
      rw [h3, mul_inv_le_iff₀ (Real.exp_pos _)]; nlinarith
    have hσp : 0 < sigN N := by rw [hσ]; exact Real.exp_pos _
    nlinarith
  · refine Real.exp_le_exp.2 (neg_le_neg ?_)
    set m := lt2m N with hmdef
    have hmn : N < 20 * m + 20 := by rw [hmdef]; unfold lt2m; omega
    have hmr : (N : ℝ) / 40 ≤ m := by
      have : (N : ℝ) < 20 * m + 20 := by exact_mod_cast hmn
      linarith
    have hm2 : ((N : ℝ) / 40) ^ 2 ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hmr 2
    have hNp : 7040 / lt2p2X x ≤ N := by linarith
    have : 7040 ≤ lt2p2X x * N := by rwa [div_le_iff₀ hp2, mul_comm] at hNp
    nlinarith
  · have h1 : Real.exp (-(11 / 10 * (N : ℝ))) = Real.exp (-(105 / 100 * (N : ℝ))) * Real.exp (-(5 / 100 * N)) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-(1045 / 1000 * (N : ℝ))) = Real.exp (-(105 / 100 * (N : ℝ))) * Real.exp (5 / 1000 * N) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-(5 / 100 * (N : ℝ))) ≤ 1 / 7 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have := hexp_big (5 / 100 * N); linarith
    have h4 : (2 : ℝ) ≤ Real.exp (5 / 1000 * N) := by have := hexp_big (5 / 1000 * N); linarith
    rw [h1, h2]
    have := Real.exp_pos (-(105 / 100 * (N : ℝ)))
    nlinarith

/-- **Lemma LT2 at every level `L ≥ 1`.** -/
theorem lt2_provedL (L : ℝ) (hL : 1 ≤ L) : LT2Stmt L (1045 / 1000) := by
  classical
  unfold LT2Stmt
  set x : ℝ := 7 * (40004 + 468 * L) with hxdef
  have hx1 : 1 ≤ x := by rw [hxdef]; nlinarith
  filter_upwards [lt2_final_ev, lt2_Sp_ev, lt2_eps_small, lt2_varfloor, lt2_Z_count, fa_small_hi,
    lt2_final_evL L x hL hx1] with N hev hSpE hEpsS hVFE hZc hfa hevL s
  obtain ⟨-, -, hHv, hWk, -, hZ13, h16, hsum, hN1, hm16⟩ := hev
  obtain ⟨h3σ, hθ, hYs, hsum'⟩ := hevL
  haveI : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  have hσ : 0 < sigN N := by unfold sigN; positivity
  set m := lt2m N with hmdef
  set γ := lt2γ
  -- the sets
  set B0 : Set (Param N) := (openCube N)ᶜ
  set B1 : Set (Param N) := {w | 13 ≤ Zs w}
  set B2 : Set (Param N) := {w | 12 ≤ (lt2Sp w).card}
  set B3 : Set (Param N) := {w | 2 * (2 ^ N * lt2pH N) < ((univ.filter fun r : State N => w r ∈ lt2HvSet N).card : ℝ)}
  set B4 : Set (Param N) := {w | ∃ j : Fin N, ∃ β : Bool,
      ∑ r ∈ (lt2H s w).filter (fun r => r ∈ agree {j} (fun _ => β)), lt2gNs (w r) ^ 2 < sigN N ^ 2 / 16}
  set B5 : Set (Param N) := {w | m / 8 ≤ ((lt2D1 N).filter fun a => |clamp01 (w s a) - 1 / 2| < γ).card}
  set B6 : Set (Param N) := {w | m / 8 ≤ ((lt2D2 N).filter fun a => |clamp01 (w s a) - 1 / 2| < γ).card}
  set B7 : Set (Param N) := {w | m ^ 2 / 4 + 1 ≤ (lt2Z s w).card}
  -- the inclusion
  have hsub : {w : Param N | betaW w < L * sigN N ∧
      ∀ S : Finset (Fin N), S.card = 2 → phi (flipP s w) s S < 3 * L * sigN N} ⊆
      B0 ∪ B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6 ∪ B7 ∪ lt2YstarX s x := by
    rintro w ⟨hβ, hphi⟩
    by_contra hno
    simp only [Set.mem_union, not_or] at hno
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, hY⟩ := hno
    simp only [B0, Set.mem_compl_iff, not_not] at h0
    simp only [B1, B2, B3, B4, B5, B6, B7, Set.mem_setOf_eq, not_le, not_lt, not_exists] at h1 h2 h3 h4 h5 h6 h7
    -- the hypotheses of the pair bound
    have hZ0 : 0 < Zs w := by
      have := Zs_pos (flipP_mem_openCube (s := s) h0) s; rwa [flipP_invol] at this
    have hPw : ∀ v, Pw w v < 13 * L * sigN N := lt2_Pw_ltL (by linarith) hβ hZ0 h1.le
    have hSp : ∑ v ∈ lt2Sp w, Pw w v < 156 * L * sigN N := by
      calc ∑ v ∈ lt2Sp w, Pw w v ≤ ∑ _v ∈ lt2Sp w, 13 * L * sigN N := Finset.sum_le_sum fun v _ => (hPw v).le
        _ = (lt2Sp w).card * (13 * L * sigN N) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 11 * (13 * L * sigN N) := by
            have : ((lt2Sp w).card : ℝ) ≤ 11 := by exact_mod_cast (by omega : (lt2Sp w).card ≤ 11)
            have hLσ : 0 ≤ 13 * L * sigN N := by positivity
            exact mul_le_mul_of_nonneg_right this hLσ
        _ < 156 * L * sigN N := by
            have : 0 < L * sigN N := by positivity
            linarith
    have hEps : lt2Eps s w ≤ sigN N := by
      have h := hEpsS s w ((lt2H_card_le s w).trans h3)
      have : Real.exp (-(N : ℝ) / 1000) ≤ 1 := Real.exp_le_one_iff.2 (by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith)
      nlinarith
    have hVF : lt2VF s w := fun j β => h4 j β
    -- many good pairs
    have hGood : ((lt2m N : ℝ)) ^ 2 / 4 ≤ ((lt2Good s w).card : ℝ) := by
      set W1 := (lt2D1 N).filter fun a => |clamp01 (w s a) - 1 / 2| < γ
      set W2 := (lt2D2 N).filter fun a => |clamp01 (w s a) - 1 / 2| < γ
      have hcov : lt2D1 N ×ˢ lt2D2 N ⊆ lt2Good s w ∪ lt2Z s w ∪ (W1 ×ˢ lt2D2 N) ∪ (lt2D1 N ×ˢ W2) := by
        intro p hp
        obtain ⟨ha, hb⟩ := mem_product.1 hp
        by_cases hz : lt2ZP s w p
        · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hp, hz⟩)))
        · by_cases hwa : lt2Weak s w p.1
          · exact mem_union_left _ (mem_union_right _ (mem_product.2 ⟨mem_filter.2 ⟨ha, hwa⟩, hb⟩))
          · by_cases hwb : lt2Weak s w p.2
            · exact mem_union_right _ (mem_product.2 ⟨ha, mem_filter.2 ⟨hb, hwb⟩⟩)
            · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (by
                unfold lt2Good; exact mem_filter.2 ⟨hp, hz, hwa, hwb⟩)))
      have hc := Finset.card_le_card hcov
      have u1 := Finset.card_union_le (lt2Good s w ∪ lt2Z s w ∪ W1 ×ˢ lt2D2 N) (lt2D1 N ×ˢ W2)
      have u2 := Finset.card_union_le (lt2Good s w ∪ lt2Z s w) (W1 ×ˢ lt2D2 N)
      have u3 := Finset.card_union_le (lt2Good s w) (lt2Z s w)
      rw [card_product, lt2_card_D1, lt2_card_D2] at hc
      rw [card_product, lt2_card_D1] at u1
      rw [card_product, lt2_card_D2] at u2
      have hall : m * m ≤ (lt2Good s w).card + (lt2Z s w).card + W1.card * m + m * W2.card := by
        rw [hmdef]; linarith
      have hW1 : W1.card ≤ m / 8 := by have := h5; omega
      have hW2 : W2.card ≤ m / 8 := by have := h6; omega
      have hZ : (lt2Z s w).card ≤ m ^ 2 / 4 := by have := h7; omega
      have r1 : ((m * m : ℕ) : ℝ) ≤ (lt2Good s w).card + (lt2Z s w).card + W1.card * m + m * W2.card := by
        exact_mod_cast hall
      have r2 : ((lt2Z s w).card : ℝ) ≤ (m : ℝ) ^ 2 / 4 := by
        have : 4 * (lt2Z s w).card ≤ m ^ 2 := by omega
        have : (4 : ℝ) * (lt2Z s w).card ≤ (m : ℝ) ^ 2 := by exact_mod_cast this
        linarith
      have r3 : (W1.card : ℝ) ≤ m / 8 := by
        have : 8 * W1.card ≤ m := by omega
        have : (8 : ℝ) * W1.card ≤ m := by exact_mod_cast this
        linarith
      have r4 : (W2.card : ℝ) ≤ m / 8 := by
        have : 8 * W2.card ≤ m := by omega
        have : (8 : ℝ) * W2.card ≤ m := by exact_mod_cast this
        linarith
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      push_cast at r1
      nlinarith [mul_le_mul_of_nonneg_right r3 hm0, mul_le_mul_of_nonneg_left r4 hm0]
    -- no good pair succeeds
    have hnot : ∀ p ∈ lt2Good s w, ¬ lt2Succ s w p.1 p.2 x lt2ρ := by
      intro p hp hsucc
      unfold lt2Good at hp
      obtain ⟨hpD, hz, hwa, hwb⟩ := mem_filter.1 hp
      obtain ⟨ha, hb⟩ := mem_product.1 hpD
      have hF : ∀ (c u v : Bool), (u, v) ≠ (false, false) →
          |lt2NumNs (lt2Half s w) {p.1, p.2} (lt2pat p.1 p.2 false false) (lt2col p.1 p.2 c) -
            lt2NumNs (lt2Half s w) {p.1, p.2} (lt2pat p.1 p.2 u v) (lt2col p.1 p.2 c)| <
            16 * lt2κ * sigN N + 2 * lt2Eps s w := by
        intro c u v huv
        by_contra hge
        exact hz ⟨c, u, v, huv, not_lt.1 hge⟩
      have hphi2 := hphi {p.1, p.2} (card_pair (lt2_D1_ne_D2 ha hb))
      have hge := lt2_pair_good_phiL s w h0 ha hb lt2γ_pos (by have := lt2γ_le; linarith) lt2ρ_nonneg
        (by unfold lt2ρ; linarith) lt2ρ_le (le_of_eq hxdef.symm) hL h3σ h1.le hSp hEps hVF hF (not_lt.1 hwa)
        (not_lt.1 hwb) hsucc
      linarith
    exact hY ⟨hVF, hGood, hnot⟩
  -- the bounds
  have b0 : cubeM N B0 ≤ 0 := le_of_eq cubeM_compl_openCube
  have b1 : cubeM N B1 ≤ ENNReal.ofReal (Real.exp (-(11 / 10 * (N : ℝ)))) := by
    refine (cubeM_Zs_ge_13 (t := (N : ℝ) / 4) (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
    refine le_trans (Real.exp_le_exp.2 ?_) hZ13
    linarith
  have b2 : cubeM N B2 ≤ ENNReal.ofReal (Real.exp (-(105 / 100 * (N : ℝ)))) := hSpE
  have b3 : cubeM N B3 ≤ ENNReal.ofReal (Real.exp (-(11 / 10 * (N : ℝ)))) :=
    lt2_meas_le_of_real ((lt2_heavy_count (by omega)).trans hHv)
  have hsmall : ENNReal.ofReal (16 * Real.exp (-(2 * (N : ℝ)))) ≤ ENNReal.ofReal (Real.exp (-(11 / 10 * (N : ℝ)))) :=
    ENNReal.ofReal_le_ofReal h16
  have b4 : cubeM N B4 ≤ ENNReal.ofReal (Real.exp (-(11 / 10 * (N : ℝ)))) :=
    (hVFE s).trans ((ENNReal.ofReal_le_ofReal (by linarith [Real.exp_pos (-(2 * (N : ℝ)))])).trans hsmall)
  have hweak : ∀ D : Finset (Fin N), D.card = m →
      cubeM N {w | m / 8 ≤ (D.filter fun a => |clamp01 (w s a) - 1 / 2| < γ).card} ≤
        ENNReal.ofReal (Real.exp (-(11 / 10 * (N : ℝ)))) := fun D hD => by
    refine (lt2_eff_count s D lt2γ_pos.le (m / 8)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hD]; exact hWk
  have b5 : cubeM N B5 ≤ ENNReal.ofReal (Real.exp (-(11 / 10 * (N : ℝ)))) := hweak _ lt2_card_D1
  have b6 : cubeM N B6 ≤ ENNReal.ofReal (Real.exp (-(11 / 10 * (N : ℝ)))) := hweak _ lt2_card_D2
  have b7 : cubeM N B7 ≤ ENNReal.ofReal (Real.exp (-(11 / 10 * (N : ℝ)))) := (hZc s).trans hsmall
  have b8 : cubeM N (lt2YstarX s x) ≤ ENNReal.ofReal (Real.exp (-(11 / 10 * (N : ℝ)))) :=
    (lt2_Ystar_probX s hx1 hθ).trans (ENNReal.ofReal_le_ofReal hYs)
  set E := ENNReal.ofReal (Real.exp (-(11 / 10 * (N : ℝ))))
  have htot := lt2_union' _ _ (lt2_union' _ _ (lt2_union' _ _ (lt2_union' _ _ (lt2_union' _ _ (lt2_union' _ _
    (lt2_union' _ _ (lt2_union' _ _ b0 b1) b2) b3) b4) b5) b6) b7) b8
  refine (measure_mono hsub).trans (htot.trans ?_)
  have e7 : 0 + E + ENNReal.ofReal (Real.exp (-(105 / 100 * (N : ℝ)))) + E + E + E + E + E + E =
      ENNReal.ofReal (Real.exp (-(105 / 100 * (N : ℝ))) + 7 * Real.exp (-(11 / 10 * (N : ℝ)))) := by
    rw [ENNReal.ofReal_add (Real.exp_pos _).le (by positivity), ENNReal.ofReal_mul (by norm_num)]
    simp only [E, zero_add, ENNReal.ofReal_ofNat]
    ring
  rw [e7]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa using hsum'

end Census
end IIT
