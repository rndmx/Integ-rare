/-
Census, B1 lemma LT2: **the proof of `LT2Stmt 1 (104/100)`**.

Below the tilt, off a union of rare events (non-open cube, `Z ≥ 13`, `|Sp| ≥ 12`, many heavy rows, variance floor
failure, many weak effect units, many pairs with a large shared difference) there are `≥ m²/4` good pairs; if no
pair reaches `3σ`, none of them succeeds, which has conditional probability `≤ e^{-p₂ m²/4}`.
-/
import IIT.Census.B1LT2Final2
import IIT.Census.B1ForcedDTilt
import IIT.Census.B1ForcedAZs

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

lemma lt2_union (X Y : Set (Param N)) {a b : ENNReal} (hX : cubeM N X ≤ a) (hY : cubeM N Y ≤ b) :
    cubeM N (X ∪ Y) ≤ a + b := (measure_union_le X Y).trans (add_le_add hX hY)

/-- **Lemma LT2.** -/
theorem lt2_proved : LT2Stmt 1 (104 / 100) := by
  classical
  unfold LT2Stmt
  filter_upwards [lt2_final_ev, lt2_Sp_ev, lt2_eps_small, lt2_varfloor, lt2_Z_count, fa_small_hi]
    with N hev hSpE hEpsS hVFE hZc hfa s
  obtain ⟨hσ15, hθ, hHv, hWk, hYs, hZ13, h16, hsum, hN1, hm16⟩ := hev
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
  have hsub : {w : Param N | betaW w < 1 * sigN N ∧
      ∀ S : Finset (Fin N), S.card = 2 → phi (flipP s w) s S < 3 * 1 * sigN N} ⊆
      B0 ∪ B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6 ∪ B7 ∪ lt2Ystar s := by
    rintro w ⟨hβ, hphi⟩
    by_contra hno
    simp only [Set.mem_union, not_or] at hno
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, hY⟩ := hno
    simp only [B0, Set.mem_compl_iff, not_not] at h0
    simp only [B1, B2, B3, B4, B5, B6, B7, Set.mem_setOf_eq, not_le, not_lt, not_exists] at h1 h2 h3 h4 h5 h6 h7
    rw [one_mul] at hβ
    -- the hypotheses of the pair bound
    have hZ0 : 0 < Zs w := by
      have := Zs_pos (flipP_mem_openCube (s := s) h0) s; rwa [flipP_invol] at this
    have hPw : ∀ v, Pw w v < 13 * sigN N := lt2_Pw_lt hβ hZ0 h1.le
    have hSp : ∑ v ∈ lt2Sp w, Pw w v < 156 * sigN N := by
      calc ∑ v ∈ lt2Sp w, Pw w v ≤ ∑ _v ∈ lt2Sp w, 13 * sigN N := Finset.sum_le_sum fun v _ => (hPw v).le
        _ = (lt2Sp w).card * (13 * sigN N) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 11 * (13 * sigN N) := by
            have : ((lt2Sp w).card : ℝ) ≤ 11 := by exact_mod_cast (by omega : (lt2Sp w).card ≤ 11)
            nlinarith
        _ < 156 * sigN N := by linarith
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
    have hnot : ∀ p ∈ lt2Good s w, ¬ lt2Succ s w p.1 p.2 lt2x lt2ρ := by
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
      have hge := lt2_pair_good_phi s w h0 ha hb lt2γ_pos (by have := lt2γ_le; linarith) lt2ρ_nonneg
        (by unfold lt2ρ; linarith) lt2ρ_le hσ15 h1.le hSp hEps hVF hF (not_lt.1 hwa) (not_lt.1 hwb)
        (by unfold lt2x at hsucc; exact hsucc)
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
  have b8 : cubeM N (lt2Ystar s) ≤ ENNReal.ofReal (Real.exp (-(11 / 10 * (N : ℝ)))) :=
    (lt2_Ystar_prob s hθ).trans (ENNReal.ofReal_le_ofReal hYs)
  set E := ENNReal.ofReal (Real.exp (-(11 / 10 * (N : ℝ))))
  have htot := lt2_union _ _ (lt2_union _ _ (lt2_union _ _ (lt2_union _ _ (lt2_union _ _ (lt2_union _ _
    (lt2_union _ _ (lt2_union _ _ b0 b1) b2) b3) b4) b5) b6) b7) b8
  refine (measure_mono hsub).trans (htot.trans ?_)
  have e7 : 0 + E + ENNReal.ofReal (Real.exp (-(105 / 100 * (N : ℝ)))) + E + E + E + E + E + E =
      ENNReal.ofReal (Real.exp (-(105 / 100 * (N : ℝ))) + 7 * Real.exp (-(11 / 10 * (N : ℝ)))) := by
    rw [ENNReal.ofReal_add (Real.exp_pos _).le (by positivity), ENNReal.ofReal_mul (by norm_num)]
    simp only [E, zero_add, ENNReal.ofReal_ofNat]
    ring
  rw [e7]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa using hsum

end Census
end IIT
