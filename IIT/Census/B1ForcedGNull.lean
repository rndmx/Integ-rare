/-
Census, B1 forced leaf 7: the field `stateC` of `Tier3Rest` holds almost surely, agent "forcedG".

PROVED here (sorry-free):
* `rowTie_null`  : for rows `r ≠ r'`, `{z ∈ openCube | P_z(r) = P_z(r')}` is Lebesgue-null (Mityagin, the analytic
                   zero-set theorem `volume_zero_set_analytic`, with an explicit witness point).
* `stateC_null`  : `cubeM {w | sysMaxCauseStates (tpmOf (flipP s w)) univ s s ≠ {tcRow w}} = 0` (`N ≥ 1`).
-/
import IIT.Census.B1ForcedGLow
import IIT.Census.Ties

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- The witness point: row `r` reads `3/4` on its current bits, every other row `1/2`. -/
noncomputable def gWit (s r : State N) : Param N :=
  fun v j => if v = r then (if s j then 3 / 4 else 1 / 4) else 1 / 2

lemma gWit_mem (s r : State N) : gWit s r ∈ openCube N := by
  intro v j
  unfold gWit
  split_ifs <;> constructor <;> norm_num

lemma gWit_fullProb (s r v : State N) :
    fullProb (tpmOf (gWit s r)) v s = if v = r then (3 / 4 : ℝ) ^ N else (1 / 2 : ℝ) ^ N := by
  unfold fullProb
  split_ifs with hv
  · have h : ∀ j, (tpmOf (gWit s r)).prob j v (s j) = 3 / 4 := fun j => by
      show (if s j then clamp01 (gWit s r v j) else 1 - clamp01 (gWit s r v j)) = 3 / 4
      unfold gWit
      rw [if_pos hv]
      cases s j <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
        rw [clamp01_eq (by constructor <;> norm_num)] <;> norm_num
    rw [prod_congr rfl fun j _ => h j, prod_const, card_univ, Fintype.card_fin]
  · have h : ∀ j, (tpmOf (gWit s r)).prob j v (s j) = 1 / 2 := fun j => by
      show (if s j then clamp01 (gWit s r v j) else 1 - clamp01 (gWit s r v j)) = 1 / 2
      unfold gWit
      rw [if_neg hv]
      cases s j <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
        rw [clamp01_eq (by constructor <;> norm_num)] <;> norm_num
    rw [prod_congr rfl fun j _ => h j, prod_const, card_univ, Fintype.card_fin]

/-- **Row ties are null.** -/
theorem rowTie_null (hN : 1 ≤ N) (s : State N) {r r' : State N} (hr : r ≠ r') :
    volume {z : Param N | z ∈ openCube N ∧ fullProb (tpmOf z) r s = fullProb (tpmOf z) r' s} = 0 := by
  have h := volume_zero_set_analytic volume (isOpen_openCube N) (convex_openCube N).isPreconnected
    (f := fun z => fullProb (tpmOf z) r s - fullProb (tpmOf z) r' s)
    (fun z hz => (an_fullProb hz r s).fun_sub (an_fullProb hz r' s))
    ⟨gWit s r, gWit_mem s r, by
      rw [gWit_fullProb, gWit_fullProb, if_pos rfl, if_neg (Ne.symm hr)]
      have : (1 / 2 : ℝ) ^ N < (3 / 4 : ℝ) ^ N :=
        pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
      linarith⟩
  refine measure_mono_null (fun z hz => ?_) h
  exact ⟨hz.1, sub_eq_zero.2 hz.2⟩

lemma g_rowProd_flip (s : State N) (w : Param N) (r : State N) :
    fullProb (tpmOf (flipP s w)) r s = Pw w r := by
  have h := rowProd_eq_Pw (flipP s w) s r
  rw [flipP_invol s w] at h
  rw [← h]
  rfl

/-- **`tcRow` is the unique maximal cause state of `U`, almost surely.** -/
theorem stateC_null (hN : 1 ≤ N) (s : State N) :
    cubeM N {w | sysMaxCauseStates (tpmOf (flipP s w)) univ s s ≠ {tcRow w}} = 0 := by
  classical
  set T : Set (Param N) := ⋃ r : State N, ⋃ r' : State N, if r = r' then ∅ else
    {z : Param N | z ∈ openCube N ∧ fullProb (tpmOf z) r s = fullProb (tpmOf z) r' s} with hT
  have hTnull : volume T = 0 := by
    refine measure_iUnion_null fun r => measure_iUnion_null fun r' => ?_
    split_ifs with h
    · exact measure_empty
    · exact rowTie_null hN s h
  have hsub : {w : Param N | sysMaxCauseStates (tpmOf (flipP s w)) univ s s ≠ {tcRow w}} ⊆
      (openCube N)ᶜ ∪ flipE s ⁻¹' T := by
    intro w hw
    rw [Set.mem_ofPred_eq] at hw
    by_cases ho : w ∈ openCube N
    · right
      have hz : flipP s w ∈ openCube N := flipP_mem_openCube ho
      by_contra hno
      apply hw
      refine sysMaxCauseStates_univ_eq hz s (tcRow w) fun r hr => ?_
      have hle : rowProd (flipP s w) s r ≤ rowProd (flipP s w) s (tcRow w) := by
        rw [rowProd_eq_Pw, rowProd_eq_Pw, flipP_invol s w]; exact Pw_le_tcRow w r
      refine lt_of_le_of_ne hle fun heq => hno ?_
      rw [Set.mem_preimage]
      refine Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨tcRow w, ?_⟩⟩
      rw [if_neg hr]
      exact ⟨hz, heq⟩
    · exact Or.inl ho
  refine measure_mono_null hsub (measure_union_null cubeM_compl_openCube ?_)
  rw [← volume_cube_inter]
  refine measure_mono_null Set.inter_subset_right ?_
  rw [(mp_flipE s).measure_preimage_equiv]
  exact hTnull

end Census
end IIT

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- `Tier3Rest2` without the a.s. field `stateC`. -/
structure Tier3Rest3 (N : ℕ) (s : State N) (w : Param N) : Prop where
  mem_open : w ∈ openCube N
  spreadC : ∀ A' : Finset (Fin N), A'.card < 2 * DU N →
    5 * (DU N : ℝ) < ∑ j ∈ A'ᶜ, (kF (lamCz (flipP s w) s (tcRow w)) j - lcMin s w)
  smallC : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N →
    7 * (DU N : ℝ) < kM (lamCz (flipP s w) s (tcRow w)) (lcMin s w) K
  countC : 5 * (univ.filter fun j => kF (lamCz (flipP s w) s (tcRow w)) j - lcMin s w ≤ 1 / (N : ℝ)).card < N
  eff : ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) univ s s, EffRest N s w te

/-- The residual statement for Tier 3 after the concentration, `lowC` and `stateC` reductions. -/
def NatTier3Rest3Stmt (C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bNat N s ∩ {w | ¬ Tier3Rest3 N s w}) ≤ ENNReal.ofReal (Real.exp (-(C * N)))

/-- **NatTier3 from `Tier3Rest3` and LTβ.** -/
theorem natTier3_of_rest3 {C C' : ℝ} (hC : C < C') (h : NatTier3Rest3Stmt C')
    (hLT : LTBetaStmt (1 / 4) C') : NatTier3Stmt C := by
  refine natTier3_of_rest2 hC ?_ hLT
  filter_upwards [h, eventually_ge_atTop 1] with N hR hN1 s
  have hsub : bNat N s ∩ {w | ¬ Tier3Rest2 N s w} ⊆ (bNat N s ∩ {w | ¬ Tier3Rest3 N s w}) ∪
      {w | sysMaxCauseStates (tpmOf (flipP s w)) univ s s ≠ {tcRow w}} := by
    rintro w ⟨hw, hn⟩
    by_cases h3 : Tier3Rest3 N s w
    · by_cases hs : sysMaxCauseStates (tpmOf (flipP s w)) univ s s = {tcRow w}
      · exact absurd ⟨h3.mem_open, hs, h3.spreadC, h3.smallC, h3.countC, h3.eff⟩ hn
      · exact Or.inr hs
    · exact Or.inl ⟨hw, h3⟩
  calc cubeM N (bNat N s ∩ {w | ¬ Tier3Rest2 N s w})
      ≤ cubeM N (bNat N s ∩ {w | ¬ Tier3Rest3 N s w}) +
          cubeM N {w | sysMaxCauseStates (tpmOf (flipP s w)) univ s s ≠ {tcRow w}} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (Real.exp (-(C' * N))) + 0 := add_le_add (hR s) (stateC_null hN1 s).le
    _ = ENNReal.ofReal (Real.exp (-(C' * N))) := add_zero _

end Census
end IIT
