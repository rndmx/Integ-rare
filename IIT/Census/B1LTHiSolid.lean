/-
Census, B1 LTBetaHi, module T2: **solid lightness fails with probability `≤ e^{-0.44N}`** (W2 6.2).

A row with iid uniform entries has `X_M = Σ_{j ∈ M} -ln y_j ≤ 3N/10` with probability `≤ e^{-0.44 N}` as soon as
`|M| ≥ 19N/20` (`M = Top^c`, `ε ≤ 1/20`): rate `m (x/m - 1 - ln(x/m)) = x - m + m ln(m/x) ≥ x + 0.15 m ≥ 0.4425 N`
since `ln(m/x) ≥ ln(19/6) ≥ 1.15`.
-/
import IIT.Census.B1LTHiStop
import IIT.Census.B1Ties
import IIT.Census.B1LT2Kinds
import IIT.Census.B1ArgmaxUnion
import IIT.Census.B1LTHiDisj

namespace IIT
namespace Census

open MeasureTheory Finset

variable {N : ℕ}

lemma st_log_19_6 : ((115 / 100 : ℚ) : ℝ) ≤ Real.log ((19 / 6 : ℚ) : ℝ) :=
  log_ge_rat (by norm_num) 12 2 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- **Solid-lightness failure of one row.** -/
theorem st_solid_fail (M : Finset (Fin N)) (hN : 0 < N) (hM : 19 * N ≤ 20 * M.card) :
    rowM N {v | ∑ i ∈ M, -Real.log (clamp01 (v i)) ≤ 3 / 10 * (N : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(44 / 100 * (N : ℝ)))) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : 19 * (N : ℝ) ≤ 20 * M.card := by exact_mod_cast hM
  set m : ℝ := ((M.card : ℕ) : ℝ)
  set x : ℝ := 3 / 10 * (N : ℝ) with hxd
  have hx : 0 < x := by positivity
  have hxm : x ≤ m := by rw [hxd]; linarith
  have hm : 0 < m := by linarith
  refine (rowM_negLog_sum_le M hx hxm).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  have hq : ((19 / 6 : ℚ) : ℝ) ≤ m / x := by
    rw [le_div_iff₀ hx, hxd]; push_cast; linarith
  have hlog : (115 / 100 : ℝ) ≤ Real.log (m / x) := by
    have := st_log_19_6
    push_cast at this hq
    exact this.trans (Real.log_le_log (by norm_num) hq)
  have e : Real.log (x / m) = -Real.log (m / x) := by
    rw [← Real.log_inv, inv_div]
  have e2 : m * (x / m - 1 - Real.log (x / m)) = x - m + m * Real.log (m / x) := by
    rw [e]; field_simp; ring
  rw [e2]
  have := mul_le_mul_of_nonneg_left hlog hm.le
  rw [hxd] at this ⊢; linarith

/-- **At least `K` rows of a prescribed set `A` in an event**: `≤ C(|A|, K) p^K`. -/
theorem cubeM_card_rowsA_ge (A : Finset (State N)) {E : Set (Fin N → ℝ)} [DecidablePred (· ∈ E)]
    (hE : MeasurableSet E) (K : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp : rowM N E ≤ ENNReal.ofReal p) :
    cubeM N {w | K ≤ (A.filter fun r : State N => w r ∈ E).card} ≤
      ENNReal.ofReal (A.card.choose K * p ^ K) := by
  have hsub : {w : Param N | K ≤ (A.filter fun r : State N => w r ∈ E).card} ⊆
      ⋃ S ∈ Finset.powersetCard K A, ⋂ r ∈ S, (fun w : Param N => w r) ⁻¹' E := by
    intro w hw
    obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq (show K ≤ _ from hw)
    simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_preimage, exists_prop]
    exact ⟨S, Finset.mem_powersetCard.2 ⟨fun r hr => (Finset.mem_filter.1 (hS hr)).1, hSc⟩,
      fun r hr => (Finset.mem_filter.1 (hS hr)).2⟩
  have hind := iIndepFun_rows (N := N) (fun _ v => v) fun _ => measurable_id
  have hmp : ∀ r, MeasurePreserving (fun w : Param N => w r) (cubeM N) (rowM N) := fun r =>
    measurePreserving_eval (fun _ : State N => rowM N) r
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ S ∈ Finset.powersetCard K A, cubeM N (⋂ r ∈ S, (fun w : Param N => w r) ⁻¹' E)
      ≤ ∑ _S ∈ Finset.powersetCard K A, ENNReal.ofReal (p ^ K) := by
        refine Finset.sum_le_sum fun S hS => ?_
        rw [hind.measure_inter_preimage_eq_mul S (sets := fun _ => E) fun _ _ => hE]
        calc ∏ r ∈ S, cubeM N ((fun w : Param N => w r) ⁻¹' E)
            = ∏ _r ∈ S, rowM N E :=
              Finset.prod_congr rfl fun r _ => (hmp r).measure_preimage hE.nullMeasurableSet
          _ ≤ ∏ _r ∈ S, ENNReal.ofReal p := Finset.prod_le_prod' fun _ _ => hp
          _ = ENNReal.ofReal (p ^ K) := by
              rw [Finset.prod_const, (Finset.mem_powersetCard.1 hS).2, ENNReal.ofReal_pow hp0]
    _ = ENNReal.ofReal (A.card.choose K * p ^ K) := by
        rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

/-- **Many units with a bad row** (W2 6.2): if every bad unit `j ∈ J` has a bad row `ρ j ∈ A` (rows of distinct units
distinct), then `#bad units ≥ K` has probability `≤ C(|A|, K) p^K`. -/
theorem cubeM_card_units_ge {ι : Type*} [DecidableEq ι] (J : Finset ι) (A : Finset (State N))
    (bad : Param N → ι → Prop) [∀ w, DecidablePred (bad w)] {E : Set (Fin N → ℝ)} [DecidablePred (· ∈ E)]
    (hE : MeasurableSet E) (ρ : Param N → ι → State N)
    (hρA : ∀ w, ∀ j ∈ J, bad w j → ρ w j ∈ A) (hρE : ∀ w, ∀ j ∈ J, bad w j → w (ρ w j) ∈ E)
    (hρinj : ∀ w, ∀ j ∈ J, ∀ j' ∈ J, bad w j → bad w j' → ρ w j = ρ w j' → j = j')
    (K : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp : rowM N E ≤ ENNReal.ofReal p) :
    cubeM N {w | K ≤ (J.filter (bad w)).card} ≤ ENNReal.ofReal (A.card.choose K * p ^ K) := by
  refine (measure_mono fun w hw => ?_).trans (cubeM_card_rowsA_ge A hE K hp0 hp)
  simp only [Set.mem_setOf_eq] at hw ⊢
  refine hw.trans (Finset.card_le_card_of_injOn (ρ w) (fun j hj => ?_) fun j hj j' hj' h => ?_)
  · obtain ⟨hjJ, hb⟩ := Finset.mem_filter.1 hj
    exact Finset.mem_filter.2 ⟨hρA w j hjJ hb, hρE w j hjJ hb⟩
  · obtain ⟨hjJ, hb⟩ := Finset.mem_filter.1 hj
    obtain ⟨hjJ', hb'⟩ := Finset.mem_filter.1 hj'
    exact hρinj w j hjJ j' hjJ' hb hb' h

/-- A row light on `C₀` at level `c ≥ x₁` is never special. -/
lemma st_light_not_Sp (C0 : Finset (Fin N)) {c : ℝ} (hc : lt2x1 ≤ c) {w : Param N} {r : State N}
    (h : c * N < XMW w C0 r) : r ∉ lt2Sp w := by
  intro hr
  have h1 := (mem_filter.1 hr).2
  have h2 := XMW_le_XW w C0 r
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-- **`Sp` is a stopping choice**: changing only `C₀`-agreeing entries of light rows keeps `Sp`. -/
theorem st_Sp_stable (C0 : Finset (Fin N)) {c : ℝ} (hc : lt2x1 ≤ c) {w w' : Param N}
    (hC : ∀ q, ∀ j ∈ C0, w q j = w' q j) (hN : ∀ r, ¬ c * N < XMW w C0 r → ∀ j, w r j = w' r j) :
    lt2Sp w' = lt2Sp w := by
  ext r
  by_cases hl : c * N < XMW w C0 r
  · have hl' : c * N < XMW w' C0 r := (stLight_congr C0 c hC r).1 hl
    simp only [st_light_not_Sp C0 hc hl, st_light_not_Sp C0 hc hl']
  · have hX : XW w' r = XW w r := by
      unfold XW; exact Finset.sum_congr rfl fun j _ => by rw [hN r hl j]
    simp only [lt2Sp, mem_filter, mem_univ, true_and, hX]

/-- The global `Top`: the units where `tc` is at least its `⌈εN⌉`-th largest entry. -/
noncomputable def lt3TopG (w : Param N) (ε : ℝ) : Finset (Fin N) := by
  classical exact univ.filter fun j => b1YTopR w (tcRow w) ε ≤ clamp01 (w (tcRow w) j)

/-- The good units for `Top'` (W11 §2): `y_{tc,j} ≥ 17/20` and `y_{s,j} ≥ 7/8`. -/
noncomputable def lt3GoodU (s : State N) (w : Param N) : Finset (Fin N) := by
  classical exact univ.filter fun j => 17 / 20 ≤ clamp01 (w (tcRow w) j) ∧ 7 / 8 ≤ clamp01 (w s j)

/-- `Top'`: the first `⌈εN⌉` good units (by index). -/
noncomputable def lt3TopP (s : State N) (w : Param N) (ε : ℝ) : Finset (Fin N) :=
  (((lt3GoodU s w).sort (· ≤ ·)).take ⌈ε * N⌉₊).toFinset

/-- The special-current-row case `s ∈ Sp \ {tc}`. -/
def lt3SpC (s : State N) (w : Param N) : Prop := s ∈ lt2Sp w ∧ s ≠ tcRow w

/-- **`Top`**: `Top'` in the special-current-row case, the global `Top` otherwise. -/
noncomputable def lt3Top (s : State N) (w : Param N) (ε : ℝ) : Finset (Fin N) := by
  classical exact if lt3SpC s w then lt3TopP s w ε else lt3TopG w ε

lemma lt3TopP_sub (s : State N) (w : Param N) (ε : ℝ) : lt3TopP s w ε ⊆ lt3GoodU s w := by
  intro j hj
  simp only [lt3TopP, List.mem_toFinset] at hj
  exact (Finset.mem_sort _).1 (List.mem_of_mem_take hj)

lemma lt3TopP_card (s : State N) (w : Param N) (ε : ℝ) :
    (lt3TopP s w ε).card = min ⌈ε * N⌉₊ (lt3GoodU s w).card := by
  unfold lt3TopP
  rw [List.toFinset_card_of_nodup ((Finset.sort_nodup _ _).sublist (List.take_sublist _ _)),
    List.length_take, Finset.length_sort]

/-- In the special case every unit of `Top` has `y_{tc,j} ≥ 17/20`. -/
lemma lt3Top_floorP {s : State N} {w : Param N} {ε : ℝ} (h : lt3SpC s w) {j : Fin N} (hj : j ∈ lt3Top s w ε) :
    17 / 20 ≤ clamp01 (w (tcRow w) j) := by
  classical
  simp only [lt3Top, if_pos h] at hj
  have := lt3TopP_sub s w ε hj
  simp only [lt3GoodU, Finset.mem_filter] at this
  exact this.2.1

lemma lt3Top_congr {s : State N} {w w' : Param N} (ε : ℝ) (ht : tcRow w' = tcRow w)
    (hrow : w' (tcRow w) = w (tcRow w)) (hSp : lt2Sp w' = lt2Sp w) (hs : w' s = w s) :
    lt3Top s w' ε = lt3Top s w ε := by
  classical
  have hC : lt3SpC s w' ↔ lt3SpC s w := by unfold lt3SpC; rw [hSp, ht]
  have hG : lt3TopG w' ε = lt3TopG w ε := by
    have hY : b1YTopR w' (tcRow w') ε = b1YTopR w (tcRow w) ε := by
      rw [ht]; unfold b1YTopR; rw [hrow]
    unfold lt3TopG; rw [hY, ht, hrow]
  have hU : lt3GoodU s w' = lt3GoodU s w := by unfold lt3GoodU; rw [ht, hrow, hs]
  have hP : lt3TopP s w' ε = lt3TopP s w ε := by unfold lt3TopP; rw [hU]
  unfold lt3Top
  by_cases h : lt3SpC s w
  · rw [if_pos (hC.2 h), if_pos h, hP]
  · rw [if_neg (fun h' => h (hC.1 h')), if_neg h, hG]

/-- **The frame of Lemma SS** (W2 6.1(a)(b)): if `P(tc) > e^{-cN}` (`c ≥ x₁`) and `w'` differs from `w` only in
`Top`-column entries of rows that are solidly light (`X_{Top^c} > cN`), and not in the row `s`, then `tc`, its
row, `P(tc)`, `Top` and `Sp` are unchanged. -/
theorem lt3_frame_stable {s : State N} (ε : ℝ) {c : ℝ} (hc : lt2x1 ≤ c) {w w' : Param N}
    (hP : Real.exp (-(c * N)) < Pw w (tcRow w))
    (hC : ∀ q, ∀ j ∈ (lt3Top s w ε)ᶜ, w q j = w' q j)
    (hN : ∀ r, ¬ c * N < XMW w (lt3Top s w ε)ᶜ r → ∀ j, w r j = w' r j) (hs : w' s = w s) :
    tcRow w' = tcRow w ∧ w' (tcRow w) = w (tcRow w) ∧ Pw w' (tcRow w') = Pw w (tcRow w) ∧
      lt3Top s w' ε = lt3Top s w ε ∧ lt2Sp w' = lt2Sp w := by
  obtain ⟨ht, hPt⟩ := st_tcRow_stable _ c hP hC hN
  have htl : ¬ c * N < XMW w (lt3Top s w ε)ᶜ (tcRow w) := fun h =>
    absurd ((st_Pw_le_exp _ w _).trans_lt
      (Real.exp_lt_exp.2 (by linarith : -XMW w (lt3Top s w ε)ᶜ (tcRow w) < -(c * N)))) (not_lt.2 hP.le)
  have hrow : w' (tcRow w) = w (tcRow w) := funext fun j => (hN _ htl j).symm
  have hSp := st_Sp_stable _ hc hC hN
  exact ⟨ht, hrow, by rw [ht, hPt], lt3Top_congr ε ht hrow hSp hs, hSp⟩

/-- **No tie inside a row, `cubeM`-a.e.** -/
theorem null_entry_tie :
    cubeM N {w : Param N | ∃ r : State N, ∃ i j : Fin N, i ≠ j ∧ clamp01 (w r i) = clamp01 (w r j)} = 0 := by
  have an : ∀ (r : State N) (i : Fin N), AnalyticOnNhd ℝ (fun w : Param N => w r i) (openCube N) :=
    fun r i w _ => by
      have := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : State N => Fin N → ℝ) r)).analyticAt w
      exact this
  have hpair : ∀ (r : State N) (i j : Fin N), i ≠ j →
      volume {w : Param N | w ∈ openCube N ∧ w r i = w r j} = 0 := by
    intro r i j hij
    refine null_of_analytic_ne (an r i) (an r j) (zSpike_open r i) ?_
    simp [zSpike, Ne.symm hij]; norm_num
  have hsub : {w : Param N | ∃ r : State N, ∃ i j : Fin N, i ≠ j ∧ clamp01 (w r i) = clamp01 (w r j)} ⊆
      (openCube N)ᶜ ∪ ⋃ r : State N, ⋃ i : Fin N, ⋃ j : Fin N,
        (if i = j then ∅ else {w : Param N | w ∈ openCube N ∧ w r i = w r j}) := by
    rintro w ⟨r, i, j, hne, he⟩
    by_cases hw : w ∈ openCube N
    · right; simp only [Set.mem_iUnion]
      have he' : w r i = w r j := by
        rwa [clamp01_of_mem ⟨(hw r i).1.le, (hw r i).2.le⟩, clamp01_of_mem ⟨(hw r j).1.le, (hw r j).2.le⟩] at he
      exact ⟨r, i, j, by rw [if_neg hne]; exact ⟨hw, he'⟩⟩
    · exact Or.inl hw
  refine measure_mono_null hsub (measure_union_null cubeM_compl_openCube
    (measure_iUnion_null fun r => measure_iUnion_null fun i => measure_iUnion_null fun j => ?_))
  split_ifs with h
  · exact measure_empty
  · rw [← restrict_cube]
    exact le_antisymm ((Measure.restrict_le_self _).trans (hpair r i j h).le) zero_le

/-- Off row ties, `|Top_G| ≤ ⌈εN⌉` (and always `≥ ⌈εN⌉`). -/
lemma lt3TopG_card_le {w : Param N} {ε : ℝ} (hk : 1 ≤ ⌈ε * N⌉₊)
    (hnt : ∀ i j : Fin N, i ≠ j → clamp01 (w (tcRow w) i) ≠ clamp01 (w (tcRow w) j)) :
    (lt3TopG w ε).card ≤ ⌈ε * N⌉₊ := by
  classical
  have hlt := card_gt_yTopW_lt w hk
  -- at most one unit attains `y_top` exactly
  have hsub : lt3TopG w ε ⊆ (univ.filter fun i => yTopW w ε < clamp01 (w (tcRow w) i)) ∪
      univ.filter fun i => clamp01 (w (tcRow w) i) = yTopW w ε := by
    intro i hi
    have := (mem_filter.1 hi).2
    rcases this.lt_or_eq with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, h⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, h.symm⟩)
  have hone : (univ.filter fun i => clamp01 (w (tcRow w) i) = yTopW w ε).card ≤ 1 := by
    refine Finset.card_le_one.2 fun i hi j hj => ?_
    by_contra hij
    exact hnt i j hij ((mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm)
  have := (card_le_card hsub).trans (card_union_le _ _)
  omega

/-- `|Top| ≤ ⌈εN⌉` off row ties of `tc`. -/
lemma lt3Top_card_le {s : State N} {w : Param N} {ε : ℝ} (hk : 1 ≤ ⌈ε * N⌉₊)
    (hnt : ∀ i j : Fin N, i ≠ j → clamp01 (w (tcRow w) i) ≠ clamp01 (w (tcRow w) j)) :
    (lt3Top s w ε).card ≤ ⌈ε * N⌉₊ := by
  classical
  unfold lt3Top
  split_ifs
  · rw [lt3TopP_card]; exact min_le_left _ _
  · exact lt3TopG_card_le hk hnt

/-- **Many entries of one row in a set** (W2 6.2, row-`u` exclusion): `P(#{j : y_{s,j} ∈ I} ≥ K) ≤ C(N,K) p^K`
when `unif I ≤ p`. (Counting over all units removes any dependence on `Top`/`tc`.) -/
theorem cubeM_card_entries_ge (s : State N) {I : Set ℝ} [DecidablePred (· ∈ I)] (hI : MeasurableSet I) (K : ℕ) {p : ℝ} (hp0 : 0 ≤ p)
    (hp : unif I ≤ ENNReal.ofReal p) :
    cubeM N {w | K ≤ (univ.filter fun j : Fin N => w s j ∈ I).card} ≤ ENNReal.ofReal (N.choose K * p ^ K) := by
  classical
  have hsub : {w : Param N | K ≤ (univ.filter fun j : Fin N => w s j ∈ I).card} ⊆
      ⋃ T ∈ Finset.powersetCard K (univ : Finset (Fin N)),
        (fun w : Param N => w s) ⁻¹' Set.pi Set.univ (fun j => if j ∈ T then I else Set.univ) := by
    intro w hw
    obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq (show K ≤ _ from hw)
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, exists_prop]
    refine ⟨T, Finset.mem_powersetCard.2 ⟨subset_univ _, hTc⟩, fun j => ?_⟩
    split_ifs with hj
    · exact (mem_filter.1 (hT hj)).2
    · trivial
  have hmp : MeasurePreserving (fun w : Param N => w s) (cubeM N) (rowM N) :=
    measurePreserving_eval (fun _ : State N => rowM N) s
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ T ∈ Finset.powersetCard K (univ : Finset (Fin N)), cubeM N ((fun w : Param N => w s) ⁻¹'
        Set.pi Set.univ (fun j => if j ∈ T then I else Set.univ))
      ≤ ∑ _T ∈ Finset.powersetCard K (univ : Finset (Fin N)), ENNReal.ofReal (p ^ K) := by
        refine Finset.sum_le_sum fun T hT => ?_
        rw [hmp.measure_preimage (MeasurableSet.univ_pi fun j => by
          split_ifs
          · exact hI
          · exact MeasurableSet.univ).nullMeasurableSet]
        unfold rowM
        rw [Measure.pi_pi]
        rw [show (fun j => unif (if j ∈ T then I else Set.univ)) = fun j => if j ∈ T then unif I else 1 by
          funext j; split_ifs <;> simp]
        rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, Finset.filter_mem_eq_inter,
          Finset.univ_inter, (Finset.mem_powersetCard.1 hT).2, ENNReal.ofReal_pow hp0]
        exact pow_le_pow_left₀ zero_le hp K
    _ = ENNReal.ofReal (N.choose K * p ^ K) := by
        rw [Finset.sum_const, Finset.card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

/-- The rate of `cubeM_card_entries_ge`: `C(N,K) q^K ≤ e^{(ln 2 - λ/160) N}` for `q ≤ e^{-λ}`, `K ≥ N/160`. -/
lemma st_entries_rate {N K : ℕ} {q lam : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ Real.exp (-lam)) (hlam : 0 ≤ lam)
    (hK : N ≤ 160 * K) :
    (N.choose K : ℝ) * q ^ K ≤ Real.exp ((Real.log 2 - lam / 160) * N) := by
  have h1 : (N.choose K : ℝ) ≤ Real.exp (Real.log 2 * N) := by
    rw [Real.exp_mul, Real.exp_log (by norm_num), Real.rpow_natCast]
    exact_mod_cast Nat.choose_le_two_pow N K
  have h2 : q ^ K ≤ Real.exp (-(lam / 160) * N) := by
    calc q ^ K ≤ Real.exp (-lam) ^ K := pow_le_pow_left₀ hq0 hq K
      _ = Real.exp (-lam * K) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-(lam / 160) * N) := Real.exp_le_exp.2 (by
          have : (N : ℝ) ≤ 160 * K := by exact_mod_cast hK
          nlinarith)
  calc (N.choose K : ℝ) * q ^ K ≤ Real.exp (Real.log 2 * N) * Real.exp (-(lam / 160) * N) :=
        mul_le_mul h1 h2 (pow_nonneg hq0 K) (Real.exp_pos _).le
    _ = Real.exp ((Real.log 2 - lam / 160) * N) := by rw [← Real.exp_add]; ring_nf

/-- Robust solid lightness of a row vector: `X_{Tᶜ} > 3N/10` for every `|T| ≤ k`. -/
def stRobust (N k : ℕ) (v : Fin N → ℝ) : Prop :=
  ∀ T : Finset (Fin N), T.card ≤ k → 3 / 10 * (N : ℝ) < ∑ i ∈ Tᶜ, -Real.log (clamp01 (v i))

/-- **Robust solid lightness fails with probability `≤ C(N,k) e^{-0.44N}`** (`20k ≤ N`). -/
theorem st_robust_fail {k : ℕ} (hN : 0 < N) (hk : 20 * k ≤ N) :
    rowM N {v | ¬ stRobust N k v} ≤ ENNReal.ofReal (N.choose k * Real.exp (-(44 / 100 * (N : ℝ)))) := by
  classical
  have hsub : {v : Fin N → ℝ | ¬ stRobust N k v} ⊆
      ⋃ T ∈ Finset.powersetCard k (univ : Finset (Fin N)),
        {v | ∑ i ∈ Tᶜ, -Real.log (clamp01 (v i)) ≤ 3 / 10 * (N : ℝ)} := by
    intro v hv
    simp only [stRobust, not_forall, not_lt, Set.mem_setOf_eq] at hv
    obtain ⟨T, hT, hle⟩ := hv
    -- enlarge `T` to exactly `k` elements: the complement sum only decreases
    obtain ⟨T', hTT', hT'⟩ := Finset.exists_superset_card_eq hT (by simpa using hk.trans' (by omega))
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    refine ⟨T', Finset.mem_powersetCard.2 ⟨subset_univ _, hT'⟩, le_trans ?_ hle⟩
    exact Finset.sum_le_sum_of_subset_of_nonneg (compl_subset_compl.2 hTT')
      fun i _ _ => b1_neg_log_clamp_nonneg _
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ T ∈ Finset.powersetCard k (univ : Finset (Fin N)),
        rowM N {v | ∑ i ∈ Tᶜ, -Real.log (clamp01 (v i)) ≤ 3 / 10 * (N : ℝ)}
      ≤ ∑ _T ∈ Finset.powersetCard k (univ : Finset (Fin N)),
          ENNReal.ofReal (Real.exp (-(44 / 100 * (N : ℝ)))) := by
        refine Finset.sum_le_sum fun T hT => st_solid_fail Tᶜ hN ?_
        rw [card_compl, Fintype.card_fin, (Finset.mem_powersetCard.1 hT).2]
        omega
    _ = ENNReal.ofReal (N.choose k * Real.exp (-(44 / 100 * (N : ℝ)))) := by
        rw [Finset.sum_const, Finset.card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

/-- A robustly solidly light row is solidly light for `Top` (when `|Top| ≤ k`). -/
lemma stRobust_top {k : ℕ} {w : Param N} {q : State N} (h : stRobust N k (w q)) {T : Finset (Fin N)}
    (hT : T.card ≤ k) : 3 / 10 * (N : ℝ) < XMW w Tᶜ q := h T hT

lemma st_log21 : Real.log ((21 : ℚ) : ℝ) ≤ ((305 / 100 : ℚ) : ℝ) :=
  log_le_rat (by norm_num) 12 4 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

/-- **Rate of robust solid-lightness failure**: `C(N,k) e^{-0.44N} ≤ e^{-0.23N}` for `N/21 ≤ k ≤ N/20`. -/
lemma st_robust_rate {k : ℕ} (hk2 : N ≤ 21 * k) (hk1 : 20 * k ≤ N) :
    (N.choose k : ℝ) * Real.exp (-(44 / 100 * (N : ℝ))) ≤ Real.exp (-(23 / 100 * (N : ℝ))) := by
  have hc := lt2_choose_le (d := N) (m := k) (D := 21) (by norm_num) (by exact_mod_cast hk2)
  have hl := st_log21
  push_cast at hl
  have hk : (20 : ℝ) * k ≤ N := by exact_mod_cast hk1
  have e : (Real.exp 1 * 21) ^ k = Real.exp ((1 + Real.log 21) * k) := by
    rw [← Real.exp_log (show (0 : ℝ) < 21 by norm_num), ← Real.exp_add, ← Real.exp_nat_mul,
      Real.exp_log (by norm_num)]; ring_nf
  calc (N.choose k : ℝ) * Real.exp (-(44 / 100 * (N : ℝ)))
      ≤ Real.exp ((1 + Real.log 21) * k) * Real.exp (-(44 / 100 * (N : ℝ))) := by
        rw [← e]; exact mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ = Real.exp ((1 + Real.log 21) * k - 44 / 100 * (N : ℝ)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(23 / 100 * (N : ℝ))) := Real.exp_le_exp.2 (by
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith)

lemma st_mset_robust (N k : ℕ) : MeasurableSet {v : Fin N → ℝ | ¬ stRobust N k v} := by
  suffices hm : MeasurableSet {v : Fin N → ℝ | stRobust N k v} from hm.compl
  have e : {v : Fin N → ℝ | stRobust N k v} = ⋂ T : Finset (Fin N),
      {v | T.card ≤ k → 3 / 10 * (N : ℝ) < ∑ i ∈ Tᶜ, -Real.log (clamp01 (v i))} := by
    ext v; simp [stRobust]
  rw [e]
  refine MeasurableSet.iInter fun T => ?_
  by_cases hT : T.card ≤ k
  · have e2 : {v : Fin N → ℝ | T.card ≤ k → 3 / 10 * (N : ℝ) < ∑ i ∈ Tᶜ, -Real.log (clamp01 (v i))} =
        {v | 3 / 10 * (N : ℝ) < ∑ i ∈ Tᶜ, -Real.log (clamp01 (v i))} := by
      ext v; simp [hT]
    rw [e2]
    exact measurableSet_lt measurable_const
      (Finset.measurable_sum _ fun i _ => (measurable_negLogClamp.comp (measurable_pi_apply i)))
  · have e2 : {v : Fin N → ℝ | T.card ≤ k → 3 / 10 * (N : ℝ) < ∑ i ∈ Tᶜ, -Real.log (clamp01 (v i))} =
        Set.univ := by
      ext v; simp [hT]
    rw [e2]; exact MeasurableSet.univ

lemma st_flip_inj (s : State N) : Function.Injective (flip s) := by
  intro j j' h
  by_contra hne
  have := congrFun h j
  simp [flip, Function.update_of_ne hne, Function.update_self] at this

open Classical in
/-- **Unit exclusion by the current row** (W2 6.1(c), rows `u^j`, `u = s` fixed): at least `K` units `j` with
`s^j` not robustly solidly light has probability `≤ C(N, K) (C(N,k) e^{-0.44N})^K`. -/
theorem lt3_unit_flip_excl (s : State N) {k : ℕ} (hN : 0 < N) (hk : 20 * k ≤ N) (K : ℕ) :
    cubeM N {w | K ≤ (univ.filter fun j : Fin N => ¬ stRobust N k (w (flip s j))).card} ≤
      ENNReal.ofReal (N.choose K * (N.choose k * Real.exp (-(44 / 100 * (N : ℝ)))) ^ K) := by
  have h := cubeM_card_units_ge (univ : Finset (Fin N)) ((univ : Finset (Fin N)).image (flip s))
    (fun w j => ¬ stRobust N k (w (flip s j))) (st_mset_robust N k) (fun _ j => flip s j)
    (fun _ j _ _ => mem_image.2 ⟨j, mem_univ _, rfl⟩) (fun _ _ _ hb => hb)
    (fun _ _ _ _ _ _ _ h => st_flip_inj s h) K (by positivity) (st_robust_fail hN hk)
  rw [card_image_of_injective _ (st_flip_inj s), card_univ, Fintype.card_fin] at h
  exact h

open Classical in
lemma st_mset_card_ge (B : Fin N → Set (Param N)) (hB : ∀ j, MeasurableSet (B j)) (K : ℕ) :
    MeasurableSet {w : Param N | K ≤ (univ.filter fun j => w ∈ B j).card} := by
  classical
  have e : {w : Param N | K ≤ (univ.filter fun j => w ∈ B j).card} =
      ⋃ T ∈ Finset.powersetCard K (univ : Finset (Fin N)), ⋂ j ∈ T, B j := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, exists_prop, Finset.mem_powersetCard]
    constructor
    · intro hw
      obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hw
      exact ⟨T, ⟨subset_univ _, hTc⟩, fun j hj => (mem_filter.1 (hT hj)).2⟩
    · rintro ⟨T, ⟨-, hTc⟩, hT⟩
      rw [← hTc]
      exact card_le_card fun j hj => mem_filter.2 ⟨mem_univ _, hT j hj⟩
  rw [e]
  exact Finset.measurableSet_biUnion _ fun T _ => Finset.measurableSet_biInter _ fun j _ => hB j

open Classical in
/-- **Unit exclusion by the rows `tc^j`** (W2 6.1(c)): via the argmax-union lemma with `ρ = 1`. -/
theorem lt3_unit_tc_excl {k : ℕ} (hN : 0 < N) (hk : 20 * k ≤ N) (K : ℕ) :
    cubeM N {w | K ≤ (univ.filter fun j : Fin N => ¬ stRobust N k (w (flip (tcRow w) j))).card} ≤
      ((N + 1) ^ 1 : ℕ) * ENNReal.ofReal (N.choose K * (N.choose k * Real.exp (-(44 / 100 * (N : ℝ)))) ^ K) := by
  let E : State N → Set (Param N) := fun r0 =>
    {w | K ≤ (univ.filter fun j : Fin N => ¬ stRobust N k (w (flip r0 j))).card}
  have hE : ∀ r0, MeasurableSet (E r0) := fun r0 => by
    have := st_mset_card_ge (fun j => (fun w : Param N => w (flip r0 j)) ⁻¹' {v | ¬ stRobust N k v})
      (fun j => (st_mset_robust N k).preimage (measurable_pi_apply _)) K
    convert this using 1
    ext w; simp only [E, Set.mem_setOf_eq, Set.mem_preimage]
  have hq : ∀ r0 w, cubeM N {η | replE (amC 1 r0) w η ∈ E r0} ≤
      ENNReal.ofReal (N.choose K * (N.choose k * Real.exp (-(44 / 100 * (N : ℝ)))) ^ K) := by
    intro r0 w
    have hrow : ∀ (η : Param N) (j : Fin N), replE (amC 1 r0) w η (flip r0 j) = η (flip r0 j) := by
      intro η j; funext i
      have hm : (flip r0 j, i) ∈ amC 1 r0 := by
        simp only [amC, mem_product, mem_erase, mem_univ, and_true]
        refine ⟨fun h => ?_, ?_⟩
        · have := lt2_ham_flip r0 j; rw [h, b1_ham_self] at this; omega
        · rw [mem_ballR]; have := lt2_ham_flip r0 j; rw [b1_ham_comm] at this; omega
      simp only [replE, if_pos hm]
    have e : {η | replE (amC 1 r0) w η ∈ E r0} =
        {η : Param N | K ≤ (univ.filter fun j : Fin N => ¬ stRobust N k (η (flip r0 j))).card} := by
      ext η; simp only [E, Set.mem_setOf_eq, hrow]
    rw [e]; exact lt3_unit_flip_excl r0 hN hk K
  exact cubeM_argmax_union 1 E hE hq

open Classical in
/-- **Unit exclusion for every row at once**: some row `h` has `≥ K` units `j` with `h^j` not robustly solidly
light with probability `≤ 2^N C(N,K) (C(N,k) e^{-0.44N})^K` (superexponentially small for `K ≍ N`; covers `tc`, `u`
and all special rows without conditioning). -/
theorem lt3_unit_all_excl {k : ℕ} (hN : 0 < N) (hk : 20 * k ≤ N) (K : ℕ) :
    cubeM N {w | ∃ h : State N, K ≤ (univ.filter fun j : Fin N => ¬ stRobust N k (w (flip h j))).card} ≤
      (2 ^ N : ℕ) * ENNReal.ofReal (N.choose K * (N.choose k * Real.exp (-(44 / 100 * (N : ℝ)))) ^ K) := by
  have e : {w : Param N | ∃ h : State N, K ≤ (univ.filter fun j : Fin N => ¬ stRobust N k (w (flip h j))).card} =
      ⋃ h : State N, {w | K ≤ (univ.filter fun j : Fin N => ¬ stRobust N k (w (flip h j))).card} := by
    ext w; simp
  rw [e]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  refine (Finset.sum_le_sum fun h _ => lt3_unit_flip_excl h hN hk K).trans ?_
  rw [Finset.sum_const, card_univ]; simp [nsmul_eq_mul]

open Classical in
/-- **The solid-lightness unit exclusion is `≤ e^{-2N}`** for `N/21 ≤ k ≤ N/20` and `K ≥ 15`. -/
theorem lt3_unit_all_excl_le {k K : ℕ} (hN : 0 < N) (hk2 : N ≤ 21 * k) (hk1 : 20 * k ≤ N)
    (hK : 15 ≤ K) :
    cubeM N {w | ∃ h : State N, K ≤ (univ.filter fun j : Fin N => ¬ stRobust N k (w (flip h j))).card} ≤
      ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
  refine (lt3_unit_all_excl hN hk1 K).trans ?_
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hKr : (15 : ℝ) ≤ K := by exact_mod_cast hK
  have hNK := mul_le_mul_of_nonneg_left hKr hNr
  set p := (N.choose k : ℝ) * Real.exp (-(44 / 100 * (N : ℝ)))
  have hp0 : 0 ≤ p := by positivity
  have hp : p ≤ Real.exp (-(23 / 100 * (N : ℝ))) := st_robust_rate hk2 hk1
  have hpK : p ^ K ≤ Real.exp (-(23 / 100 * (N : ℝ)) * K) := by
    rw [Real.exp_mul]; rw [Real.rpow_natCast]; exact pow_le_pow_left₀ hp0 hp K
  have hc : (N.choose K : ℝ) ≤ Real.exp (Real.log 2 * N) := by
    rw [Real.exp_mul, Real.exp_log (by norm_num), Real.rpow_natCast]
    exact_mod_cast Nat.choose_le_two_pow N K
  have h2 : ((2 ^ N : ℕ) : ℝ) = Real.exp (Real.log 2 * N) := by
    rw [Real.exp_mul, Real.exp_log (by norm_num), Real.rpow_natCast]; push_cast; rfl
  have hl2 := Real.log_two_lt_d9
  have hbound : ((2 ^ N : ℕ) : ℝ) * ((N.choose K : ℝ) * p ^ K) ≤ Real.exp (-(2 * (N : ℝ))) := by
    rw [h2]
    calc Real.exp (Real.log 2 * N) * ((N.choose K : ℝ) * p ^ K)
        ≤ Real.exp (Real.log 2 * N) * (Real.exp (Real.log 2 * N) * Real.exp (-(23 / 100 * (N : ℝ)) * K)) := by
          gcongr
      _ = Real.exp (2 * Real.log 2 * N - 23 / 100 * (N : ℝ) * K) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(2 * (N : ℝ))) := Real.exp_le_exp.2 (by nlinarith)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hbound

open Classical in
/-- **Row-`u` exclusion** (W2 6.2): `#{j : |y_{s,j} - 1/2| < γ} ≥ K` has probability `≤ e^{(ln 2 - λ/160) N}` when
`2γ ≤ e^{-λ}` and `K ≥ N/160`. -/
theorem lt3_u_excl_le (s : State N) {γ lam : ℝ} (hγ : 0 ≤ γ) (hγl : 2 * γ ≤ Real.exp (-lam)) (hlam : 0 ≤ lam)
    {K : ℕ} (hK : N ≤ 160 * K) :
    cubeM N {w | K ≤ (univ.filter fun j : Fin N => w s j ∈ Set.Ioo (1 / 2 - γ) (1 / 2 + γ)).card} ≤
      ENNReal.ofReal (Real.exp ((Real.log 2 - lam / 160) * N)) := by
  have hI : unif (Set.Ioo (1 / 2 - γ) (1 / 2 + γ)) ≤ ENNReal.ofReal (2 * γ) := by
    refine (Measure.restrict_le_self _).trans ?_
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_le_ofReal (by linarith)
  refine (cubeM_card_entries_ge s measurableSet_Ioo K (by linarith) hI).trans
    (ENNReal.ofReal_le_ofReal (st_entries_rate (by linarith) hγl hlam hK))

open Classical in
/-- **Member exclusion** (W2 6.2(e)), for fixed base rows `B` (pairwise agreeing-or-differing on `Q`) and a fixed
family `F` inside `Q` (members of size `≤ 3` sharing `≤ 1` unit): at least `M` members with a non-robust row `r^R`
(`r ∈ B`, `R ⊆ S`, `|R| ≥ 2`) has probability `≤ C(8|B||F|, M) p^M`, `p = C(N,k)e^{-0.44N}`. -/
theorem lt3_member_excl {k : ℕ} (hN : 0 < N) (hk : 20 * k ≤ N) (Q : Finset (Fin N)) (hQ : 7 ≤ Q.card)
    (B : Finset (State N)) (hB : ∀ r ∈ B, ∀ r' ∈ B, (∀ j ∈ Q, r j = r' j) ∨ (∀ j ∈ Q, r j ≠ r' j))
    (F : Finset (Finset (Fin N))) (hFQ : ∀ S ∈ F, S ⊆ Q) (hF3 : ∀ S ∈ F, S.card ≤ 3)
    (hF : ∀ S ∈ F, ∀ S' ∈ F, S ≠ S' → (S ∩ S').card ≤ 1) (M : ℕ) :
    cubeM N {w | M ≤ (F.filter fun S => ∃ r ∈ B, ∃ R ⊆ S, 2 ≤ R.card ∧ ¬ stRobust N k (w (flipS r R))).card} ≤
      ENNReal.ofReal (((B ×ˢ F.biUnion Finset.powerset).card.choose M) *
        (N.choose k * Real.exp (-(44 / 100 * (N : ℝ)))) ^ M) := by
  let bad : Param N → Finset (Fin N) → Prop := fun w S =>
    ∃ r ∈ B, ∃ R ⊆ S, 2 ≤ R.card ∧ ¬ stRobust N k (w (flipS r R))
  let pick : Param N → Finset (Fin N) → State N × Finset (Fin N) := fun w S =>
    if h : bad w S then (h.choose, h.choose_spec.2.choose) else (fun _ => false, ∅)
  have hpick : ∀ w S, bad w S → (pick w S).1 ∈ B ∧ (pick w S).2 ⊆ S ∧ 2 ≤ (pick w S).2.card ∧
      ¬ stRobust N k (w (flipS (pick w S).1 (pick w S).2)) := by
    intro w S h
    simp only [pick, dif_pos h]
    exact ⟨h.choose_spec.1, h.choose_spec.2.choose_spec.1, h.choose_spec.2.choose_spec.2⟩
  let A : Finset (State N) := (B ×ˢ F.biUnion Finset.powerset).image fun p => flipS p.1 p.2
  have h := cubeM_card_units_ge F A bad (st_mset_robust N k) (fun w S => flipS (pick w S).1 (pick w S).2)
    (fun w S hS hb => by
      obtain ⟨h1, h2, -, -⟩ := hpick w S hb
      exact mem_image.2 ⟨_, mem_product.2 ⟨h1, mem_biUnion.2 ⟨S, hS, mem_powerset.2 h2⟩⟩, rfl⟩)
    (fun w S _ hb => (hpick w S hb).2.2.2)
    (fun w S hS S' hS' hb hb' he => by
      obtain ⟨h1, h2, h3, -⟩ := hpick w S hb
      obtain ⟨h1', h2', -, -⟩ := hpick w S' hb'
      exact (flipS_member_inj hQ (hFQ S hS) (hFQ S' hS') (hF3 S hS) (hF3 S' hS') (hF S hS S' hS') h2 h2' h3
        (hB _ h1 _ h1') he).1)
    M (by positivity) (st_robust_fail hN hk)
  refine h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity)))
  exact_mod_cast Nat.choose_le_choose M
    (card_image_le (s := B ×ˢ F.biUnion Finset.powerset) (f := fun p : State N × Finset (Fin N) => flipS p.1 p.2))

/-- Admissible member-exclusion data `(Q, B, F)`. -/
def lt3Adm (d : Finset (Fin N) × Finset (State N) × Finset (Finset (Fin N))) : Prop :=
  7 ≤ d.1.card ∧ (∀ r ∈ d.2.1, ∀ r' ∈ d.2.1, (∀ j ∈ d.1, r j = r' j) ∨ (∀ j ∈ d.1, r j ≠ r' j)) ∧
    (∀ S ∈ d.2.2, S ⊆ d.1) ∧ (∀ S ∈ d.2.2, S.card ≤ 3) ∧
    (∀ S ∈ d.2.2, ∀ S' ∈ d.2.2, S ≠ S' → (S ∩ S').card ≤ 1)

open Classical in
/-- **Member exclusion, union over random data**: over a finite set `𝒟` of admissible data with `|B| ≤ b`,
`|F| ≤ f`, some datum has `≥ M` bad members with probability `≤ |𝒟| C(8bf, M) p^M`. -/
theorem lt3_member_excl_union {k : ℕ} (hN : 0 < N) (hk : 20 * k ≤ N)
    (𝒟 : Finset (Finset (Fin N) × Finset (State N) × Finset (Finset (Fin N)))) (h𝒟 : ∀ d ∈ 𝒟, lt3Adm d)
    {b f : ℕ} (hb : ∀ d ∈ 𝒟, d.2.1.card ≤ b) (hf : ∀ d ∈ 𝒟, d.2.2.card ≤ f) (M : ℕ) :
    cubeM N {w | ∃ d ∈ 𝒟, M ≤ (d.2.2.filter fun S => ∃ r ∈ d.2.1, ∃ R ⊆ S, 2 ≤ R.card ∧
        ¬ stRobust N k (w (flipS r R))).card} ≤
      𝒟.card * ENNReal.ofReal (((8 * b * f).choose M) * (N.choose k * Real.exp (-(44 / 100 * (N : ℝ)))) ^ M) := by
  have e : {w : Param N | ∃ d ∈ 𝒟, M ≤ (d.2.2.filter fun S => ∃ r ∈ d.2.1, ∃ R ⊆ S, 2 ≤ R.card ∧
        ¬ stRobust N k (w (flipS r R))).card} = ⋃ d ∈ 𝒟, {w : Param N | M ≤ (d.2.2.filter fun S =>
        ∃ r ∈ d.2.1, ∃ R ⊆ S, 2 ≤ R.card ∧ ¬ stRobust N k (w (flipS r R))).card} := by
    ext w; simp
  rw [e]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ d ∈ 𝒟, cubeM N {w : Param N | M ≤ (d.2.2.filter fun S =>
        ∃ r ∈ d.2.1, ∃ R ⊆ S, 2 ≤ R.card ∧ ¬ stRobust N k (w (flipS r R))).card}
      ≤ ∑ _d ∈ 𝒟, ENNReal.ofReal (((8 * b * f).choose M) *
          (N.choose k * Real.exp (-(44 / 100 * (N : ℝ)))) ^ M) := by
        refine Finset.sum_le_sum fun d hd => ?_
        obtain ⟨hQ, hB, hFQ, hF3, hF⟩ := h𝒟 d hd
        refine (lt3_member_excl hN hk d.1 hQ d.2.1 hB d.2.2 hFQ hF3 hF M).trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity)))
        have hc : (d.2.1 ×ˢ d.2.2.biUnion Finset.powerset).card ≤ 8 * b * f := by
          rw [card_product]
          have h1 : (d.2.2.biUnion Finset.powerset).card ≤ 8 * f := by
            refine card_biUnion_le.trans ?_
            calc ∑ S ∈ d.2.2, S.powerset.card ≤ ∑ _S ∈ d.2.2, 8 := sum_le_sum fun S hS => by
                  rw [card_powerset]
                  calc 2 ^ S.card ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (hF3 S hS)
                    _ = 8 := by norm_num
              _ = d.2.2.card * 8 := by rw [sum_const, smul_eq_mul]
              _ ≤ 8 * f := by have := hf d hd; omega
          calc d.2.1.card * (d.2.2.biUnion Finset.powerset).card ≤ b * (8 * f) :=
                Nat.mul_le_mul (hb d hd) h1
            _ = 8 * b * f := by ring
        exact_mod_cast Nat.choose_le_choose M hc
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Rate of the member exclusion**: `D · C(8bf, M) p^M ≤ e^{-2N}` for `D ≤ e^{aN}`, `p ≤ e^{-0.23N}`,
`8bf ≤ c M` (`c ≥ 1`; e.g. `M = f/8`, `c = 64 b`), `1 + log c + 100 ≤ 0.23 N`, `(a+2)N ≤ 100M`. -/
lemma lt3_member_rate {b f M : ℕ} {a c D p : ℝ} (hc1 : 1 ≤ c) (hD : D ≤ Real.exp (a * N)) (hp0 : 0 ≤ p)
    (hp : p ≤ Real.exp (-(23 / 100 * (N : ℝ)))) (hbf : ((8 * b * f : ℕ) : ℝ) ≤ c * M)
    (hN : 1 + Real.log c + 100 ≤ 23 / 100 * (N : ℝ)) (hM : (a + 2) * N ≤ 100 * M) :
    D * (((8 * b * f).choose M : ℕ) * p ^ M) ≤ Real.exp (-(2 * (N : ℝ))) := by
  have hMr : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hc : (((8 * b * f).choose M : ℕ) : ℝ) ≤ Real.exp ((1 + Real.log c) * M) := by
    refine (lt2_choose_le (by linarith) hbf).trans (le_of_eq ?_)
    rw [← Real.exp_log (show (0 : ℝ) < c by linarith), ← Real.exp_add, ← Real.exp_nat_mul,
      Real.exp_log (by linarith)]; ring_nf
  have hpM : p ^ M ≤ Real.exp (-(23 / 100 * (N : ℝ)) * M) := by
    rw [Real.exp_mul, Real.rpow_natCast]; exact pow_le_pow_left₀ hp0 hp M
  calc D * (((8 * b * f).choose M : ℕ) * p ^ M)
      ≤ Real.exp (a * N) * (Real.exp ((1 + Real.log c) * M) * Real.exp (-(23 / 100 * (N : ℝ)) * M)) := by
        gcongr
    _ = Real.exp (a * N + (1 + Real.log c) * M - 23 / 100 * (N : ℝ) * M) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(2 * (N : ℝ))) := Real.exp_le_exp.2 (by nlinarith)

/-- `st_entries_rate` with a general ratio `D`: `C(N,K) q^K ≤ e^{(ln 2 - λ/D) N}` for `K ≥ N/D`. -/
lemma st_entries_rateD {N K : ℕ} {q lam D : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ Real.exp (-lam)) (hlam : 0 ≤ lam)
    (hD : 0 < D) (hK : (N : ℝ) ≤ D * K) :
    (N.choose K : ℝ) * q ^ K ≤ Real.exp ((Real.log 2 - lam / D) * N) := by
  have h1 : (N.choose K : ℝ) ≤ Real.exp (Real.log 2 * N) := by
    rw [Real.exp_mul, Real.exp_log (by norm_num), Real.rpow_natCast]
    exact_mod_cast Nat.choose_le_two_pow N K
  have h2 : q ^ K ≤ Real.exp (-(lam / D) * N) := by
    calc q ^ K ≤ Real.exp (-lam) ^ K := pow_le_pow_left₀ hq0 hq K
      _ = Real.exp (-lam * K) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-(lam / D) * N) := Real.exp_le_exp.2 (by
          rw [neg_mul, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, div_le_iff₀ hD]
          nlinarith)
  calc (N.choose K : ℝ) * q ^ K ≤ Real.exp (Real.log 2 * N) * Real.exp (-(lam / D) * N) :=
        mul_le_mul h1 h2 (pow_nonneg hq0 K) (Real.exp_pos _).le
    _ = Real.exp ((Real.log 2 - lam / D) * N) := by rw [← Real.exp_add]; ring_nf

open Classical in
/-- **Row-`u` exclusion with general ratio**: `≤ e^{(ln 2 - λ/D) N}` when `2γ ≤ e^{-λ}`, `K ≥ N/D`. -/
theorem lt3_u_excl_leD (s : State N) {γ lam D : ℝ} (hγ : 0 ≤ γ) (hγl : 2 * γ ≤ Real.exp (-lam)) (hlam : 0 ≤ lam)
    (hD : 0 < D) {K : ℕ} (hK : (N : ℝ) ≤ D * K) :
    cubeM N {w | K ≤ (univ.filter fun j : Fin N => w s j ∈ Set.Ioo (1 / 2 - γ) (1 / 2 + γ)).card} ≤
      ENNReal.ofReal (Real.exp ((Real.log 2 - lam / D) * N)) := by
  have hI : unif (Set.Ioo (1 / 2 - γ) (1 / 2 + γ)) ≤ ENNReal.ofReal (2 * γ) := by
    refine (Measure.restrict_le_self _).trans ?_
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_le_ofReal (by linarith)
  refine (cubeM_card_entries_ge s measurableSet_Ioo K (by linarith) hI).trans
    (ENNReal.ofReal_le_ofReal (st_entries_rateD (by linarith) hγl hlam hD hK))

end Census
end IIT
