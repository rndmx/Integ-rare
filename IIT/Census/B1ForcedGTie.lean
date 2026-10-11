/-
Census, B1 forced leaf 7: the field `noTie` of `EffRest` holds almost surely, agent "forcedG".

For fixed `tc, te` and `j ≠ j'`, a tie `min(β Fᶜ_j, e Fᵉ_j) = min(β Fᶜ_j', e Fᵉ_j')` forces one of four analytic
equalities; each difference is analytic on the open cube and nonzero at an explicit point (all entries `1/2` except one
entry of column `j`, at the row `tc^{j'}` or `s^{j'}`), so its zero set is null (Mityagin, `volume_zero_set_analytic`).

PROVED here (sorry-free):
* `an_FC`, `an_FE`      : the full-cut values are analytic on the open cube.
* `noTie_null`          : `cubeM {w | ∃ te ∈ maxEff, ∃ j ≠ j', phTAt s w te j = phTAt s w te j'} = 0`.
* `natTier3_of_rest4`   : `NatTier3Stmt C` from `NatTier3Rest4Stmt C'` (no `noTie`) and `LTBetaStmt (1/4) C'`.
-/
import IIT.Census.B1ForcedGNull

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

lemma g_sdiff_erase (j : Fin N) : (univ : Finset (Fin N)) \ univ.erase j = {j} := by
  ext i; by_cases h : i = j <;> simp [h]

lemma g_compl_erase (j : Fin N) : (univ.erase j : Finset (Fin N))ᶜ = {j} := by
  ext i; by_cases h : i = j <;> simp [h]

/-- The cause full-cut value through transition probabilities. -/
noncomputable def gFCf (s tc : State N) (j : Fin N) (z : Param N) : ℝ :=
  Real.logb 2 ((tpmOf z).prob j tc (s j) /
    ((∑ r ∈ agree {j} tc, (tpmOf z).prob j r (s j)) / (2 : ℝ) ^ (N - 1)))

lemma kF_lamCz_eq {z : Param N} (hz : z ∈ openCube N) (s tc : State N) (j : Fin N) :
    kF (lamCz z s tc) j = gFCf s tc j z := by
  unfold kF
  rw [(lamCz_means hz s tc).1, g_sdiff_erase, gFCf]
  unfold cmean
  rw [card_singleton, prob_eq_clamp]
  congr 3
  refine sum_congr rfl fun r _ => (prob_eq_clamp z s r j).symm

lemma an_FC {z0 : Param N} (hz : z0 ∈ openCube N) (s tc : State N) (j : Fin N) :
    AnalyticAt ℝ (fun z => kF (lamCz z s tc) j) z0 := by
  have hev : (fun z => gFCf s tc j z) =ᶠ[𝓝 z0] fun z => kF (lamCz z s tc) j := by
    filter_upwards [(isOpen_openCube N).mem_nhds hz] with z hz'
    exact (kF_lamCz_eq hz' s tc j).symm
  refine AnalyticAt.congr ?_ hev
  unfold gFCf
  refine an_logb_div (an_prob hz j tc (s j))
    ((Finset.analyticAt_fun_sum _ fun r _ => an_prob hz j r (s j)).fun_div analyticAt_const
      (by positivity)) (prob_pos hz j tc (s j)) ?_
  refine div_pos (sum_pos (fun r _ => prob_pos hz j r (s j)) ⟨tc, mem_agree.2 fun _ _ => rfl⟩)
    (by positivity)

lemma an_FE {z0 : Param N} (hz : z0 ∈ openCube N) (s te : State N) (j : Fin N) :
    AnalyticAt ℝ (fun z => kF (lamEz z s te) j) z0 :=
  an_logb_div (an_prob hz j s (te j)) (an_effUnit hz _ s j (te j)) (prob_pos hz j s (te j))
    (effUnit_pos hz _ s j (te j))

lemma g_logb_ne_zero {x : ℝ} (hx : 0 < x) (h1 : x ≠ 1) : Real.logb 2 x ≠ 0 := by
  intro h
  rw [Real.logb, div_eq_zero_iff] at h
  rcases h with h | h
  · rcases Real.log_eq_zero.1 h with h | h | h
    · linarith
    · exact h1 h
    · linarith
  · have := Real.log_pos one_lt_two; linarith

lemma g_half_ratio {M : ℝ} (hM : 0 < M) : Real.logb 2 ((1 / 2 : ℝ) / ((M / 2) / M)) = 0 := by
  have : (1 / 2 : ℝ) / ((M / 2) / M) = 1 := by field_simp
  rw [this, Real.logb_one]

/-! ### The witness points (flipped coordinates) -/

/-- All entries `1/2` except entry `(r*, j)`, which is `1/4`. -/
noncomputable def gW1 (rs : State N) (j : Fin N) : Param N :=
  fun r i => if r = rs ∧ i = j then 1 / 4 else 1 / 2

lemma gW1_mem (rs : State N) (j : Fin N) : gW1 rs j ∈ openCube N := by
  intro r i; unfold gW1; split_ifs <;> constructor <;> norm_num

lemma gW1_clamp (rs : State N) (j : Fin N) (r : State N) (i : Fin N) :
    clamp01 (gW1 rs j r i) = if r = rs ∧ i = j then 1 / 4 else 1 / 2 := by
  unfold gW1; split_ifs <;> rw [clamp01_eq (by constructor <;> norm_num)]

lemma g_sum_half (A : Finset (State N)) : ∑ _r ∈ A, (1 / 2 : ℝ) = A.card / 2 := by
  rw [sum_const, nsmul_eq_mul]; ring

/-- Column `i ≠ j` of the witness is constant `1/2`: both full-cut values of `i` vanish. -/
lemma gW1_FC_zero (s tc rs : State N) {i j : Fin N} (hij : i ≠ j) :
    kF (lamCz (flipP s (gW1 rs j)) s tc) i = 0 := by
  have hz := flipP_mem_openCube (s := s) (gW1_mem rs j)
  have h := (lamCz_means hz s tc).1 i (univ.erase i)
  unfold kF; rw [h, flipP_invol s (gW1 rs j), g_sdiff_erase]
  unfold cmean
  have hc : ∀ r, clamp01 (gW1 rs j r i) = 1 / 2 := fun r => by
    rw [gW1_clamp, if_neg (fun h => hij h.2)]
  simp_rw [hc]
  rw [g_sum_half, card_agree, card_singleton]
  have : ((2 ^ (N - 1) : ℕ) : ℝ) = (2 : ℝ) ^ (N - 1) := by push_cast; rfl
  rw [this]
  exact g_half_ratio (by positivity)

lemma gW1_FE_zero (s te rs : State N) {i j : Fin N} (hij : i ≠ j) :
    kF (lamEz (flipP s (gW1 rs j)) s te) i = 0 := by
  unfold kF lamEz lamEU effUnit
  have hp : ∀ r, (tpmOf (flipP s (gW1 rs j))).prob i r (te i) = 1 / 2 := fun r => by
    have hc : clamp01 (gW1 rs j r i) = 1 / 2 := by rw [gW1_clamp, if_neg (fun h => hij h.2)]
    rw [g_prob_te, hc]; split_ifs <;> norm_num
  simp_rw [hp]
  rw [g_sum_half]
  exact g_half_ratio (by exact_mod_cast card_agree_pos _ _)

/-- At the witness `(tc^{j'}, j)` the cause value of `j` is nonzero. -/
lemma gW1_FC_ne (s tc : State N) {j j' : Fin N} (hjj : j ≠ j') :
    kF (lamCz (flipP s (gW1 (flipAt j' tc) j)) s tc) j ≠ 0 := by
  set rs := flipAt j' tc
  have hz := flipP_mem_openCube (s := s) (gW1_mem rs j)
  have h := (lamCz_means hz s tc).1 j (univ.erase j)
  unfold kF; rw [h, flipP_invol s (gW1 rs j), g_sdiff_erase]
  have hrs : rs ≠ tc := fun h => by
    have := congrFun h j'
    exact flipAt_ne j' tc h
  have hmem : rs ∈ agree {j} tc := mem_agree.2 fun i hi => by
    rw [mem_singleton.1 hi]; exact Function.update_of_ne hjj _ _
  have hy : clamp01 (gW1 rs j tc j) = 1 / 2 := by rw [gW1_clamp, if_neg (fun h => hrs h.1.symm)]
  have hsum : ∑ r ∈ agree {j} tc, clamp01 (gW1 rs j r j) = (agree {j} tc).card / 2 - 1 / 4 := by
    have e : ∀ r, clamp01 (gW1 rs j r j) = 1 / 2 + (if rs = r then (-1 / 4 : ℝ) else 0) := fun r => by
      rw [gW1_clamp]
      by_cases hr : r = rs
      · rw [if_pos ⟨hr, rfl⟩, if_pos hr.symm]; norm_num
      · rw [if_neg (fun h => hr h.1), if_neg (fun h => hr h.symm)]; norm_num
    simp_rw [e]
    rw [sum_add_distrib, g_sum_half, sum_ite_eq, if_pos hmem]; ring
  unfold cmean
  rw [hy, hsum, card_agree, card_singleton]
  set M : ℝ := (2 : ℝ) ^ (N - 1) with hM
  have hcast : ((2 ^ (N - 1) : ℕ) : ℝ) = M := by rw [hM]; push_cast; rfl
  rw [hcast]
  have hM1 : (1 : ℝ) ≤ M := one_le_pow₀ (by norm_num)
  have hden : 0 < (M / 2 - 1 / 4) / M := div_pos (by linarith) (by linarith)
  have hq : (1 / 2 : ℝ) / ((M / 2 - 1 / 4) / M) ≠ 1 := by
    rw [ne_eq, div_eq_one_iff_eq hden.ne']
    intro h
    rw [eq_div_iff (by linarith)] at h
    linarith
  exact g_logb_ne_zero (div_pos (by norm_num) hden) hq

/-- At the witness `(s^{j'}, j)` the effect value of `j` is nonzero. -/
lemma gW1_FE_ne (s te : State N) {j j' : Fin N} (hjj : j ≠ j') :
    kF (lamEz (flipP s (gW1 (flipAt j' s) j)) s te) j ≠ 0 := by
  set rs := flipAt j' s
  have hrs : rs ≠ s := fun h => by
    have := congrFun h j'
    exact flipAt_ne j' s h
  have hmem : rs ∈ agree ({j} : Finset (Fin N)) s := mem_agree.2 fun i hi => by
    rw [mem_singleton.1 hi]; exact Function.update_of_ne hjj _ _
  set c : ℝ := if te j = s j then 1 / 4 else 3 / 4 with hc
  have hp : ∀ r, (tpmOf (flipP s (gW1 rs j))).prob j r (te j) =
      1 / 2 + (if rs = r then c - 1 / 2 else 0) := fun r => by
    by_cases hr : r = rs
    · have hcl : clamp01 (gW1 rs j r j) = 1 / 4 := by rw [gW1_clamp, if_pos ⟨hr, rfl⟩]
      rw [g_prob_te, hcl, if_pos hr.symm, hc]; split_ifs <;> norm_num
    · have hcl : clamp01 (gW1 rs j r j) = 1 / 2 := by rw [gW1_clamp, if_neg (fun h => hr h.1)]
      have hne : ¬ rs = r := fun h => hr h.symm
      rw [g_prob_te, hcl, if_neg hne]; split_ifs <;> norm_num
  have hc0 : c - 1 / 2 ≠ 0 := by rw [hc]; split_ifs <;> norm_num
  unfold kF lamEz lamEU effUnit
  rw [g_compl_erase]
  simp_rw [hp]
  rw [sum_add_distrib, g_sum_half, sum_ite_eq, if_pos hmem, if_neg hrs, add_zero]
  set M : ℝ := ((agree ({j} : Finset (Fin N)) s).card : ℝ) with hM
  have hM1 : (1 : ℝ) ≤ M := by rw [hM]; exact_mod_cast card_agree_pos _ _
  have hcb : c ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) := by rw [hc]; split_ifs <;> constructor <;> norm_num
  have hden : 0 < (M / 2 + (c - 1 / 2)) / M := div_pos (by linarith [hcb.1]) (by linarith)
  have hq : (1 / 2 : ℝ) / ((M / 2 + (c - 1 / 2)) / M) ≠ 1 := by
    rw [ne_eq, div_eq_one_iff_eq hden.ne']
    intro h
    rw [eq_div_iff (by linarith)] at h
    exact hc0 (by linarith)
  exact g_logb_ne_zero (div_pos (by norm_num) hden) hq

/-! ### The tie set is null -/

lemma g_min_eq_cases {a b c d : ℝ} (h : min a b = min c d) : a = c ∨ a = d ∨ b = c ∨ b = d := by
  rcases min_choice a b with h1 | h1 <;> rcases min_choice c d with h2 | h2 <;> rw [h1, h2] at h <;> tauto

/-- One analytic zero set, null when the function is nonzero at a point of the open cube. -/
lemma g_zero_null {f : Param N → ℝ} (hf : ∀ z ∈ openCube N, AnalyticAt ℝ f z) {z1 : Param N}
    (hz1 : z1 ∈ openCube N) (h1 : f z1 ≠ 0) : volume {z | z ∈ openCube N ∧ f z = 0} = 0 :=
  volume_zero_set_analytic volume (isOpen_openCube N) (convex_openCube N).isPreconnected
    (fun z hz => hf z hz) ⟨z1, hz1, h1⟩

/-- The four tie pieces at fixed `(tc, te, j, j')`. -/
def gTiePiece (s tc te : State N) (j j' : Fin N) : Set (Param N) :=
  {z | z ∈ openCube N ∧
    (sysBackCause (tpmOf z) univ s s tc * kF (lamCz z s tc) j -
      sysBackCause (tpmOf z) univ s s tc * kF (lamCz z s tc) j' = 0)} ∪
  {z | z ∈ openCube N ∧
    (sysBackCause (tpmOf z) univ s s tc * kF (lamCz z s tc) j -
      sysEffProb (tpmOf z) univ s s te * kF (lamEz z s te) j' = 0)} ∪
  {z | z ∈ openCube N ∧
    (sysEffProb (tpmOf z) univ s s te * kF (lamEz z s te) j -
      sysBackCause (tpmOf z) univ s s tc * kF (lamCz z s tc) j' = 0)} ∪
  {z | z ∈ openCube N ∧
    (sysEffProb (tpmOf z) univ s s te * kF (lamEz z s te) j -
      sysEffProb (tpmOf z) univ s s te * kF (lamEz z s te) j' = 0)}

theorem gTiePiece_null (s tc te : State N) {j j' : Fin N} (hjj : j ≠ j') :
    volume (gTiePiece s tc te j j') = 0 := by
  have hBB : ∀ z ∈ openCube N, AnalyticAt ℝ (fun z => sysBackCause (tpmOf z) univ s s tc) z :=
    fun z hz => an_sysBackCause hz s univ tc
  have hEE : ∀ z ∈ openCube N, AnalyticAt ℝ (fun z => sysEffProb (tpmOf z) univ s s te) z :=
    fun z hz => an_sysEffProb hz s univ te
  have hj'j : j' ≠ j := hjj.symm
  -- witness 1: column `j` perturbed at `tc^{j'}`
  set z1 := flipP s (gW1 (flipAt j' tc) j)
  have hz1 : z1 ∈ openCube N := flipP_mem_openCube (gW1_mem _ _)
  have hFC1 : kF (lamCz z1 s tc) j ≠ 0 := gW1_FC_ne s tc hjj
  have hFC1' : kF (lamCz z1 s tc) j' = 0 := gW1_FC_zero s tc _ hj'j
  have hFE1' : kF (lamEz z1 s te) j' = 0 := gW1_FE_zero s te _ hj'j
  have hB1 := sysBackCause_pos hz1 s univ tc
  -- witness 2: column `j` perturbed at `s^{j'}`
  set z2 := flipP s (gW1 (flipAt j' s) j)
  have hz2 : z2 ∈ openCube N := flipP_mem_openCube (gW1_mem _ _)
  have hFE2 : kF (lamEz z2 s te) j ≠ 0 := gW1_FE_ne s te hjj
  have hFC2' : kF (lamCz z2 s tc) j' = 0 := gW1_FC_zero s tc _ hj'j
  have hFE2' : kF (lamEz z2 s te) j' = 0 := gW1_FE_zero s te _ hj'j
  have hE2 := sysEffProb_pos hz2 s univ te
  unfold gTiePiece
  refine measure_union_null (measure_union_null (measure_union_null ?_ ?_) ?_) ?_
  · refine g_zero_null (fun z hz => ((hBB z hz).fun_mul (an_FC hz s tc j)).fun_sub
      ((hBB z hz).fun_mul (an_FC hz s tc j'))) hz1 ?_
    simp only [hFC1', mul_zero, sub_zero]; exact mul_ne_zero hB1.ne' hFC1
  · refine g_zero_null (fun z hz => ((hBB z hz).fun_mul (an_FC hz s tc j)).fun_sub
      ((hEE z hz).fun_mul (an_FE hz s te j'))) hz1 ?_
    simp only [hFE1', mul_zero, sub_zero]; exact mul_ne_zero hB1.ne' hFC1
  · refine g_zero_null (fun z hz => ((hEE z hz).fun_mul (an_FE hz s te j)).fun_sub
      ((hBB z hz).fun_mul (an_FC hz s tc j'))) hz2 ?_
    simp only [hFC2', mul_zero, sub_zero]; exact mul_ne_zero hE2.ne' hFE2
  · refine g_zero_null (fun z hz => ((hEE z hz).fun_mul (an_FE hz s te j)).fun_sub
      ((hEE z hz).fun_mul (an_FE hz s te j'))) hz2 ?_
    simp only [hFE2', mul_zero, sub_zero]; exact mul_ne_zero hE2.ne' hFE2

/-- The tie event of `EffRest.noTie`. -/
def gTieEv (N : ℕ) (s : State N) : Set (Param N) :=
  {w | ∃ te ∈ sysMaxEffStates (tpmOf (flipP s w)) univ s s, ∃ j j', j ≠ j' ∧ phTAt s w te j = phTAt s w te j'}

/-- **No exact tie among the single-cut values, almost surely.** -/
theorem noTie_null (s : State N) : cubeM N (gTieEv N s) = 0 := by
  classical
  set T : Set (Param N) := ⋃ tc : State N, ⋃ te : State N, ⋃ j : Fin N, ⋃ j' : Fin N,
    if j = j' then ∅ else gTiePiece s tc te j j' with hT
  have hTnull : volume T = 0 := by
    refine measure_iUnion_null fun tc => measure_iUnion_null fun te => measure_iUnion_null fun j =>
      measure_iUnion_null fun j' => ?_
    split_ifs with h
    · exact measure_empty
    · exact gTiePiece_null s tc te h
  have hsub : gTieEv N s ⊆ (openCube N)ᶜ ∪ flipE s ⁻¹' T := by
    intro w hw
    by_cases ho : w ∈ openCube N
    · right
      obtain ⟨te, -, j, j', hjj, heq⟩ := hw
      have hz : flipP s w ∈ openCube N := flipP_mem_openCube ho
      rw [Set.mem_preimage]
      refine Set.mem_iUnion.2 ⟨tcRow w, Set.mem_iUnion.2 ⟨te, Set.mem_iUnion.2 ⟨j,
        Set.mem_iUnion.2 ⟨j', ?_⟩⟩⟩⟩
      rw [if_neg hjj]
      unfold phTAt phT at heq
      have hfe : flipE s w = flipP s w := rfl
      rw [hfe]
      unfold gTiePiece
      rcases g_min_eq_cases heq with h | h | h | h
      · exact Or.inl (Or.inl (Or.inl ⟨hz, sub_eq_zero.2 h⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨hz, sub_eq_zero.2 h⟩))
      · exact Or.inl (Or.inr ⟨hz, sub_eq_zero.2 h⟩)
      · exact Or.inr ⟨hz, sub_eq_zero.2 h⟩
    · exact Or.inl ho
  refine measure_mono_null hsub (measure_union_null cubeM_compl_openCube ?_)
  rw [← volume_cube_inter]
  refine measure_mono_null Set.inter_subset_right ?_
  rw [(mp_flipE s).measure_preimage_equiv]
  exact hTnull

/-! ### Glue: `EffRest` without `noTie` -/

/-- `EffRest` without the a.s. field `noTie`. -/
structure EffRest4 (N : ℕ) (s : State N) (w : Param N) (te : State N) : Prop where
  lowE : 1 / (N : ℝ) ^ 2 ≤ leMinAt s w te
  spreadE : ∀ A' : Finset (Fin N), A'.card < 2 * DU N →
    5 * (DU N : ℝ) < ∑ j ∈ A'ᶜ, (kF (lamEz (flipP s w) s te) j - leMinAt s w te)
  smallE : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N →
    7 * (DU N : ℝ) < kM (lamEz (flipP s w) s te) (leMinAt s w te) K
  countE : 5 * (univ.filter fun j => kF (lamEz (flipP s w) s te) j - leMinAt s w te ≤ 1 / (N : ℝ)).card < N

/-- **The final residual Tier 3 event.** -/
structure Tier3Rest4 (N : ℕ) (s : State N) (w : Param N) : Prop where
  mem_open : w ∈ openCube N
  spreadC : ∀ A' : Finset (Fin N), A'.card < 2 * DU N →
    5 * (DU N : ℝ) < ∑ j ∈ A'ᶜ, (kF (lamCz (flipP s w) s (tcRow w)) j - lcMin s w)
  smallC : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N →
    7 * (DU N : ℝ) < kM (lamCz (flipP s w) s (tcRow w)) (lcMin s w) K
  countC : 5 * (univ.filter fun j => kF (lamCz (flipP s w) s (tcRow w)) j - lcMin s w ≤ 1 / (N : ℝ)).card < N
  eff : ∀ te ∈ sysMaxEffStates (tpmOf (flipP s w)) univ s s, EffRest4 N s w te

/-- The final residual statement for Tier 3. -/
def NatTier3Rest4Stmt (C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (bNat N s ∩ {w | ¬ Tier3Rest4 N s w}) ≤ ENNReal.ofReal (Real.exp (-(C * N)))

/-- **NatTier3 from `Tier3Rest4` and LTβ.** -/
theorem natTier3_of_rest4 {C C' : ℝ} (hC : C < C') (h : NatTier3Rest4Stmt C')
    (hLT : LTBetaStmt (1 / 4) C') : NatTier3Stmt C := by
  refine natTier3_of_rest3 hC ?_ hLT
  filter_upwards [h] with N hR s
  have hsub : bNat N s ∩ {w | ¬ Tier3Rest3 N s w} ⊆ (bNat N s ∩ {w | ¬ Tier3Rest4 N s w}) ∪ gTieEv N s := by
    rintro w ⟨hw, hn⟩
    by_cases h4 : Tier3Rest4 N s w
    · by_cases ht : w ∈ gTieEv N s
      · exact Or.inr ht
      · refine absurd ⟨h4.mem_open, h4.spreadC, h4.smallC, h4.countC, fun te hte => ?_⟩ hn
        have e := h4.eff te hte
        exact ⟨fun j j' hjj heq => ht ⟨te, hte, j, j', hjj, heq⟩, e.lowE, e.spreadE, e.smallE, e.countE⟩
    · exact Or.inl ⟨hw, h4⟩
  calc cubeM N (bNat N s ∩ {w | ¬ Tier3Rest3 N s w})
      ≤ cubeM N (bNat N s ∩ {w | ¬ Tier3Rest4 N s w}) + cubeM N (gTieEv N s) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (Real.exp (-(C' * N))) + 0 := add_le_add (hR s) (noTie_null s).le
    _ = ENNReal.ofReal (Real.exp (-(C' * N))) := add_zero _

end Census
end IIT
