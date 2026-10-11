/-
Census, B1 forced leaf 7: the field `lowC` of `Tier3Rest` from LTβ, agent "forcedG".

PROVED here (sorry-free):
* `phiU_le_N_beta_kF` : with `tcRow` the unique maximal cause state (any effect state), `φ_s(U) ≤ N β (Fᶜ_j)⁺` for every `j` (single-cut
                        competitor bound `sysPhiOfState_le_card_mul`, Lemma V).
* `lowC_det`          : on B1 with those states, a pair/triple with `φ_s ≥ β/4` forces `λᶜ_min > 1/(4N)`.
* `natTier3_of_rest2` : `NatTier3Stmt C` from `NatTier3Rest2Stmt C'` (`Tier3Rest` without `lowC`) and
                        `LTBetaStmt (1/4) C'` (`C < C'`).
-/
import IIT.Census.B1ForcedGTier3

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

lemma lamCz_empty {z : Param N} (hz : z ∈ openCube N) (s tc : State N) (i : Fin N) :
    lamCz z s tc i ∅ = 0 := by
  obtain ⟨m1, m2, m3, -, -⟩ := lamCz_means hz s tc
  rw [m1, m2, div_self (m3 i).ne', Real.logb_one]

/-- **Single-cut competitor bound at the maximal states.** -/
theorem phiU_le_N_beta_kF (hN : 2 ≤ N) {s : State N} {w : Param N} (ho : w ∈ openCube N)
    (hst : sysMaxCauseStates (tpmOf (flipP s w)) univ s s = {tcRow w}) (j : Fin N) :
    phi (flipP s w) s univ ≤ N * (betaW w * pos (kF (lamCz (flipP s w) s (tcRow w)) j)) := by
  have hz : flipP s w ∈ openCube N := flipP_mem_openCube ho
  have hr := hrest_of_two_le hN j
  have hβ : sysBackCause (tpmOf (flipP s w)) univ s s (tcRow w) = betaW w := by
    rw [sysBackCause_univ_eq hz, flipP_invol s w]; rfl
  have h0 : 0 ≤ (N : ℝ) * (betaW w * pos (kF (lamCz (flipP s w) s (tcRow w)) j)) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (betaW_nonneg w) (le_max_left _ _))
  unfold phi sysPhi
  refine sup'OrZero_le h0 fun q hq => ?_
  rw [hst, mem_product, mem_singleton] at hq
  obtain ⟨q1, q2⟩ := q
  obtain ⟨rfl, -⟩ := hq
  refine (sysPhiOfState_le_card_mul _ univ s s _ _ (mem_univ j) hr).trans ?_
  rw [card_univ, Fintype.card_fin]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [univ_sysPhiAt_eq hz]
  refine (min_le_left _ _).trans (le_of_eq ?_)
  rw [hβ]
  congr 2
  exact sum_profile_splitAt (lamCz (flipP s w) s (tcRow w)) (lamCz_empty hz s (tcRow w)) j hr

/-- **`lowC` from a pair/triple at level `β/4`.** -/
theorem lowC_det (hN : 4 ≤ N) {s : State N} {w : Param N} (hB : w ∈ B1w N s) (ho : w ∈ openCube N)
    (hst : sysMaxCauseStates (tpmOf (flipP s w)) univ s s = {tcRow w})
    {S : Finset (Fin N)} (h2 : 2 ≤ S.card) (h3 : S.card ≤ 3) (hS : 1 / 4 * betaW w ≤ phi (flipP s w) s S) :
    1 / (4 * (N : ℝ)) < lcMin s w := by
  obtain ⟨j, hj⟩ := g_ciInf_attained (by omega) (kF (lamCz (flipP s w) s (tcRow w)))
  have hU := phiU_le_N_beta_kF (by omega) ho hst j
  have hne : S.Nonempty := by rw [← card_pos]; omega
  have hlt := dt_B1_lt hB hne (dt_card_ne_univ h3 (by omega))
  have hβ := betaW_pos ho
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hj' : kF (lamCz (flipP s w) s (tcRow w)) j = lcMin s w := hj
  rw [hj'] at hU
  have key : 1 / (4 * (N : ℝ)) < pos (lcMin s w) := by
    rw [div_lt_iff₀ (by positivity)]
    have : betaW w * 1 < betaW w * (pos (lcMin s w) * (4 * N)) := by nlinarith
    exact lt_of_mul_lt_mul_left this hβ.le
  unfold pos at key
  rcases le_total (lcMin s w) 0 with h | h
  · rw [max_eq_left h] at key
    have : (0 : ℝ) < 1 / (4 * (N : ℝ)) := by positivity
    linarith
  · rwa [max_eq_right h] at key

/-- `Tier3Rest` without the field `lowC`. -/
structure Tier3Rest2 (N : ℕ) (s : State N) (w : Param N) : Prop where
  mem_open : w ∈ openCube N
  stateC : sysMaxCauseStates (tpmOf (flipP s w)) univ s s = {tcRow w}
  spreadC : ∀ A' : Finset (Fin N), A'.card < 2 * DU N →
    5 * (DU N : ℝ) < ∑ j ∈ A'ᶜ, (kF (lamCz (flipP s w) s (tcRow w)) j - lcMin s w)
  smallC : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N →
    7 * (DU N : ℝ) < kM (lamCz (flipP s w) s (tcRow w)) (lcMin s w) K
  countC : 5 * (univ.filter fun j => kF (lamCz (flipP s w) s (tcRow w)) j - lcMin s w ≤ 1 / (N : ℝ)).card < N
  eff : ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) univ s s, EffRest N s w te

/-- The residual statement without `lowC`. -/
def NatTier3Rest2Stmt (C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bNat N s ∩ {w | ¬ Tier3Rest2 N s w}) ≤ ENNReal.ofReal (Real.exp (-(C * N)))

/-- **NatTier3 from `Tier3Rest2` and LTβ.** -/
theorem natTier3_of_rest2 {C C' : ℝ} (hC : C < C') (h : NatTier3Rest2Stmt C')
    (hLT : LTBetaStmt (1 / 4) C') : NatTier3Stmt C := by
  have hm : C < (C + C') / 2 := by linarith
  have hm' : (C + C') / 2 < C' := by linarith
  refine natTier3_of_rest hm ?_
  filter_upwards [h, hLT, g_union_rate hm' hm', eventually_ge_atTop 4] with N hR hL hU hN4 s
  refine (measure_mono ?_).trans (hU _ _ (hR s) (hL s))
  rintro w ⟨hw, hnot⟩
  by_cases h2 : Tier3Rest2 N s w
  · right
    obtain ⟨⟨hB, ho⟩, -⟩ := hw
    refine ⟨⟨hB, ho⟩, fun S hS2 hS3 => ?_⟩
    by_contra hge
    push Not at hge
    apply hnot
    have hl := lowC_det hN4 hB ho h2.stateC hS2 hS3 hge
    have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN4
    have hle : 1 / (N : ℝ) ^ 2 ≤ 1 / (4 * N) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    exact ⟨h2.mem_open, h2.stateC, hle.trans hl.le, h2.spreadC, h2.smallC, h2.countC, h2.eff⟩
  · exact Or.inl ⟨hw, h2⟩

end Census
end IIT
