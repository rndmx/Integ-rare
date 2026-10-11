/-
Census, B1 new leaf `pairLow`, part 2: the per-cell bound and **`joint_pairLow : JointBound P0PairLow`**.
-/
import IIT.Census.B1NewLeafPair

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-! ### 1. Chernoff with a window on the column triple -/

/-- **Joint Chernoff for three rows with a window on the triple of entries.** -/
theorem cubeM_chernoff_three_win {κ : Type*} (ra rb rc : Fin N → State N)
    (hab : ∀ i, ra i ≠ rb i) (hac : ∀ i, ra i ≠ rc i) (hbc : ∀ i, rb i ≠ rc i)
    (K : Finset κ) (f : κ → Fin N → ℝ × ℝ × ℝ → ℝ) (hf : ∀ k i, Measurable (f k i))
    (a t : κ → ℝ) (ht : ∀ k ∈ K, 0 ≤ t k) (W : Fin N → Set (ℝ × ℝ × ℝ)) (hW : ∀ i, MeasurableSet (W i)) :
    cubeM N {w | (∀ i, (w (ra i) i, w (rb i) i, w (rc i) i) ∈ W i) ∧
        ∀ k ∈ K, ∑ i, f k i (w (ra i) i, w (rb i) i, w (rc i) i) ≤ a k} ≤
      ENNReal.ofReal (Real.exp (∑ k ∈ K, t k * a k)) *
        ∏ i, ∫⁻ y, ∫⁻ u, ∫⁻ x, (W i).indicator
          (fun p => ENNReal.ofReal (Real.exp (-∑ k ∈ K, t k * f k i p))) (y, u, x) ∂unif ∂unif ∂unif := by
  have hWc : ∀ i, MeasurableSet {c : State N → ℝ | (c (ra i), c (rb i), c (rc i)) ∈ W i} :=
    fun i => (hW i).preimage (by fun_prop)
  have h := cubeM_chernoff_cols K (fun k i c => f k i (c (ra i), c (rb i), c (rc i)))
    (fun k i => (hf k i).comp (by fun_prop)) a t ht
    (fun i => {c | (c (ra i), c (rb i), c (rc i)) ∈ W i}) hWc
  refine h.trans_eq ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  set H : ℝ × ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (Real.exp (-∑ k ∈ K, t k * f k i p)) with hH
  have hHm : Measurable H := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (Finset.measurable_sum _ fun k _ => (hf k i).const_mul (t k)).neg)
  rw [← lintegral_indicator (hWc i)]
  have e1 : ∀ c : State N → ℝ, ({c : State N → ℝ | (c (ra i), c (rb i), c (rc i)) ∈ W i}).indicator
      (fun c => H (c (ra i), c (rb i), c (rc i))) c = (W i).indicator H (c (ra i), c (rb i), c (rc i)) :=
    fun c => by
      by_cases hc : (c (ra i), c (rb i), c (rc i)) ∈ W i
      · rw [Set.indicator_of_mem (show c ∈ {c : State N → ℝ | (c (ra i), c (rb i), c (rc i)) ∈ W i} from hc),
          Set.indicator_of_mem hc]
      · rw [Set.indicator_of_notMem
          (show c ∉ {c : State N → ℝ | (c (ra i), c (rb i), c (rc i)) ∈ W i} from hc),
          Set.indicator_of_notMem hc]
  refine (lintegral_congr e1).trans ?_
  exact lintegral_colLaw_triple (hab i) (hac i) (hbc i) (hHm.indicator (hW i))

/-- Splitting a triple `unif`-integral of a product. -/
lemma pl_lint3 (F1 : ℝ → ENNReal) (F2 : ℝ → ℝ → ENNReal) (F3 : ℝ → ENNReal)
    (h1 : Measurable F1) (h2 : Measurable fun p : ℝ × ℝ => F2 p.1 p.2) (h3 : Measurable F3) :
    ∫⁻ y, ∫⁻ u, ∫⁻ z, F1 y * F2 y u * F3 z ∂unif ∂unif ∂unif =
      (∫⁻ y, F1 y * ∫⁻ u, F2 y u ∂unif ∂unif) * ∫⁻ z, F3 z ∂unif := by
  have hIB : Measurable fun y => ∫⁻ u, F2 y u ∂unif := h2.lintegral_prod_right'
  have hm : Measurable fun y => F1 y * ∫⁻ u, F2 y u ∂unif := h1.mul hIB
  rw [← lintegral_mul_const _ hm]
  refine lintegral_congr fun y => ?_
  have hBy : Measurable fun u => F2 y u := h2.comp (measurable_const.prodMk measurable_id)
  simp_rw [lintegral_const_mul _ h3]
  rw [lintegral_mul_const _ (hBy.const_mul _), lintegral_const_mul _ hBy]

/-! ### 2. One cause cell with the pair window -/

/-- The `pairLow` failure set (cause side). -/
def plFail (N : ℕ) (r0 : State N) (x : Fin N) : Set (Param N) :=
  {w | ∀ j, j ≠ x → 1 - 1 / (N : ℝ) < clamp01 (w r0 j) + clamp01 (w (flipAt x r0) j)}

set_option maxHeartbeats 2000000 in
/-- **One cause cell jointly with the `pairLow` failure.** -/
theorem pl_cause_cell (hN : 1 ≤ N) (s r0 : State N) (x : Fin N) {c : ℚ × ℚ}
    (hc : c ∈ cellsXCauseData) (h1 : r0 ≠ s) (h3 : flipAt x r0 ≠ s) :
    cubeM N ({w | CellEvX N s r0 x .cause c w} ∩ plFail N r0 x) ≤
      ENNReal.ofReal (Real.exp (-((plR : ℝ) * N)) * Real.exp (14 * slT N + 17 * (8 + slV N) + 210) / 2 ^ N) := by
  have hN0 : 0 < N := by omega
  obtain ⟨C, hC, hok, hlam, hlu, hP, hmono1, hcm1, hm0, hm1⟩ := fs_cause_partner hN0 hc
  have hpl : plOK C = true := (List.all_eq_true.1 plCells_ok) C hC
  obtain ⟨hBcorr, hB2, hB203, hBrate⟩ := pl_unit C hok hpl
  have hIle := pl_int_le hN0 C hok
  set c1 : ℚ × ℚ := (C.v ^ 4, C.w ^ 4) with hc1
  have hsubC := cellEvX_sub_template hN0 s r0 x c1 hcm1
  set lu : ℝ := (C.lu : ℝ) with hludef
  set t : ℝ := (C.P : ℝ) / 4 + lu with ht
  have hlu0 : 0 ≤ lu := Nat.cast_nonneg _
  have htlu : lu ≤ t := by rw [ht]; have : (0 : ℝ) ≤ (C.P : ℝ) / 4 := by positivity
                           linarith
  set Wa : Set ℝ := {y : ℝ | (c1.1 : ℝ) ≤ clamp01 y} with hWa
  have hWam : MeasurableSet Wa := measurableSet_le measurable_const clamp01_measurable
  set W : Fin N → Set (ℝ × ℝ × ℝ) := fun i =>
    {p | (c1.1 : ℝ) ≤ clamp01 p.1 ∧ (i ≠ x → 1 - 1 / (N : ℝ) < clamp01 p.1 + clamp01 p.2.1)} with hW
  have hWm : ∀ i, MeasurableSet (W i) := fun i =>
    b1_mset_and (measurableSet_le measurable_const (clamp01_measurable.comp measurable_fst))
      (b1_mset_imp (MeasurableSet.const _) (measurableSet_lt measurable_const
        ((clamp01_measurable.comp measurable_fst).add
          (clamp01_measurable.comp (measurable_fst.comp measurable_snd)))))
  have hell : Measurable fun y : ℝ => -Real.log (clamp01 y) :=
    (Real.measurable_log.comp clamp01_measurable).neg
  have hellU : Measurable (ellUX N) := by
    unfold ellUX
    exact ((Real.measurable_log.comp (clamp01_measurable.max
      (measurable_const.sub clamp01_measurable))).neg).sub_const _
  set f : Fin 3 → Fin N → ℝ × ℝ × ℝ → ℝ :=
    ![fun _ p => -Real.log (clamp01 p.1), fun _ p => ellUX N p.2.2 - -Real.log (clamp01 p.1),
      fun _ p => gXev N c1 p.1 p.2.1] with hf
  have hfm : ∀ k i, Measurable (f k i) := by
    intro k i
    fin_cases k
    · exact hell.comp measurable_fst
    · exact (hellU.comp (measurable_snd.comp measurable_snd)).sub (hell.comp measurable_fst)
    · exact (fs_gXev_meas c1).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  set a : Fin 3 → ℝ := ![x0 * N + slT N, 0, 0] with ha
  set tt : Fin 3 → ℝ := ![t, lu, (C.lam : ℝ)] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 3)), 0 ≤ tt k := by
    intro k _; fin_cases k
    · simp only [htt]; simp; positivity
    · simpa [htt] using hlu0
    · simp [htt]
  have hmain := cubeM_chernoff_three_win (fun _ => r0) (fun _ => flipAt x r0) (fun _ => s)
    (fun _ => (flipAt_ne x r0).symm) (fun _ => h1) (fun _ => h3) univ f hfm a tt htt0 W hWm
  have hsub : ({w | CellEvX N s r0 x .cause c w} ∩ plFail N r0 x : Set (Param N)) ⊆
      {w | (∀ i, (w ((fun _ : Fin N => r0) i) i, w ((fun _ : Fin N => flipAt x r0) i) i,
          w ((fun _ : Fin N => s) i) i) ∈ W i) ∧
        ∀ k ∈ (univ : Finset (Fin 3)), ∑ i, f k i (w ((fun _ : Fin N => r0) i) i,
          w ((fun _ : Fin N => flipAt x r0) i) i, w ((fun _ : Fin N => s) i) i) ≤ a k} := by
    rintro w ⟨hw1, hw2⟩
    obtain ⟨hW1, hT, hL, hV⟩ := hsubC (hmono1 s r0 x hw1)
    refine ⟨fun i => ⟨hW1 i, fun hi => hw2 i hi⟩, fun k _ => ?_⟩
    fin_cases k
    · simpa [hf, ha] using hT
    · simp only [hf, ha, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [sum_sub_distrib]; linarith
    · simpa [hf, ha] using hV
  -- the column constants
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = fsK N := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (lu * (slT N / N)) := ⟨_, rfl⟩
  obtain ⟨Ex, hExd⟩ : ∃ Ex : ℝ, Ex = 2 * (1 - (1 / 2 : ℝ) ^ (C.lu + 1)) / (C.lu + 1) := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, B = plB C := ⟨_, rfl⟩
  rw [← hBd] at hBcorr hB2 hB203 hBrate
  have hEx2 : (rsEx C.lu : ℝ) = Ex := by rw [hExd, rsEx_cast]
  rw [hEx2] at hBrate
  have hEx0 : 0 < Ex := by
    rw [hExd]
    have : (1 / 2 : ℝ) ^ (C.lu + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    apply div_pos (by linarith) (by positivity)
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB203
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = Real.exp ((C.lam : ℝ) * K) * (E * Ex) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ, hE]; positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hJ1 : 0 ≤ Q * (2 * B) := by positivity
  have hJ2 : 0 ≤ Q * (B + 1 / N) := by positivity
  -- the column bound
  have hcol : ∀ i : Fin N, ∫⁻ y, ∫⁻ u, ∫⁻ z, (W i).indicator
      (fun p => ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 3)), tt k * f k i p))) (y, u, z)
        ∂unif ∂unif ∂unif ≤ ENNReal.ofReal (if i = x then Q * (2 * B) else Q * (B + 1 / N)) := by
    intro i
    set A : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 y))) with hA
    set G0 : ℝ → ℝ → ENNReal := fun y u => ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXev N c1 y u)) with hG0
    set F2 : ℝ → ℝ → ENNReal := fun y u => if i = x then G0 y u else
      ({u : ℝ | 1 - 1 / (N : ℝ) < clamp01 y + clamp01 u}).indicator (fun u => G0 y u) u with hF2
    set F3 : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp (-lu * ellUX N z)) with hF3
    have hAm : Measurable A := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hell.const_mul _))
    have hG0m : Measurable fun p : ℝ × ℝ => G0 p.1 p.2 :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((fs_gXev_meas c1).const_mul _))
    have hF2m : Measurable fun p : ℝ × ℝ => F2 p.1 p.2 := by
      by_cases hix : i = x
      · simp only [hF2, hix, if_true]; exact hG0m
      · have e : (fun p : ℝ × ℝ => F2 p.1 p.2) =
            ({q : ℝ × ℝ | 1 - 1 / (N : ℝ) < clamp01 q.1 + clamp01 q.2}).indicator (fun q => G0 q.1 q.2) := by
          funext q; simp only [hF2, hix, if_false, Set.indicator, Set.mem_setOf_eq]
        rw [e]
        exact hG0m.indicator (measurableSet_lt measurable_const
          ((clamp01_measurable.comp measurable_fst).add (clamp01_measurable.comp measurable_snd)))
    have hF3m : Measurable F3 := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hellU.const_mul _))
    have hpt : ∀ y u z, (W i).indicator
        (fun p => ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 3)), tt k * f k i p))) (y, u, z) ≤
        Wa.indicator A y * F2 y u * F3 z := by
      intro y u z
      by_cases hp : (y, u, z) ∈ W i
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show y ∈ Wa from hp.1)]
        have hF2e : F2 y u = G0 y u := by
          by_cases hix : i = x
          · simp only [hF2, hix, if_true]
          · simp only [hF2, hix, if_false]
            exact Set.indicator_of_mem (show u ∈ {u : ℝ | 1 - 1 / (N : ℝ) < clamp01 y + clamp01 u} from
              hp.2 hix) _
        rw [hF2e]
        simp only [hA, hG0, hF3]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
          ← Real.exp_add, ← Real.exp_add]
        apply le_of_eq
        congr 2
        simp only [Fin.sum_univ_three, hf, htt, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        ring
      · rw [Set.indicator_of_notMem hp]; exact bot_le
    have hstep : ∫⁻ y, ∫⁻ u, ∫⁻ z, (W i).indicator
        (fun p => ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 3)), tt k * f k i p))) (y, u, z)
          ∂unif ∂unif ∂unif ≤ (∫⁻ y in Wa, A y * ∫⁻ u, F2 y u ∂unif ∂unif) * ∫⁻ z, F3 z ∂unif := by
      calc _ ≤ ∫⁻ y, ∫⁻ u, ∫⁻ z, Wa.indicator A y * F2 y u * F3 z ∂unif ∂unif ∂unif :=
            lintegral_mono fun y => lintegral_mono fun u => lintegral_mono fun z => hpt y u z
        _ = (∫⁻ y, Wa.indicator A y * ∫⁻ u, F2 y u ∂unif ∂unif) * ∫⁻ z, F3 z ∂unif :=
            pl_lint3 _ F2 F3 (hAm.indicator hWam) hF2m hF3m
        _ = _ := by
            congr 1
            rw [← lintegral_indicator hWam]
            refine lintegral_congr fun y => ?_
            by_cases hy : y ∈ Wa
            · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
            · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
    have hF3v : ∫⁻ z, F3 z ∂unif = ENNReal.ofReal (E * Ex) := by
      have := lintegral_ellUX (N := N) C.lu
      rw [show -(C.lu : ℝ) = -lu from rfl] at this
      rw [hE, hExd]; exact this
    refine hstep.trans ?_
    rw [hF3v]
    have hpow : t - lu = (C.P : ℝ) / 4 := by rw [ht]; ring
    by_cases hix : i = x
    · rw [if_pos hix]
      have hF2x : ∀ y u, F2 y u = G0 y u := fun y u => by simp only [hF2, hix, if_true]
      simp_rw [hF2x]
      have hJ := cell_J_le (N := N) C.lam c1 hcm1 hm0 hm1 (t := t) (lamU := lu) htlu
      have e1 : (∫ y in (c1.1 : ℝ)..1, y ^ (t - lu) * gX C.lam (c1.2 : ℝ) y) = fsI C := by
        rw [hpow]; simp only [hc1, fsI]; push_cast; rfl
      rw [e1] at hJ
      calc (∫⁻ y in Wa, A y * ∫⁻ u, G0 y u ∂unif ∂unif) * ENNReal.ofReal (E * Ex)
          ≤ ENNReal.ofReal (Real.exp ((C.lam : ℝ) * K) * (2 * B)) * ENNReal.ofReal (E * Ex) := by
            gcongr
            refine hJ.trans (ENNReal.ofReal_le_ofReal ?_)
            rw [hK]
            exact mul_le_mul_of_nonneg_left hB2 (Real.exp_pos _).le
        _ = ENNReal.ofReal (Q * (2 * B)) := by
            rw [← ENNReal.ofReal_mul (by positivity), hQ]; ring_nf
    · rw [if_neg hix]
      have hF2x : ∀ y u, F2 y u = ({u : ℝ | 1 - 1 / (N : ℝ) < clamp01 y + clamp01 u}).indicator
          (fun u => G0 y u) u := fun y u => by simp only [hF2, hix, if_false]
      simp_rw [hF2x]
      have hJ := pl_J_le hN0 C.lam c1 hcm1 hm0 hm1 (t := t) (lamU := lu) htlu
      have e1 : (∫ y in (c1.1 : ℝ)..1, y ^ (t - lu) * plG N C.lam (c1.2 : ℝ) y) =
          ∫ y in ((C.v : ℝ) ^ 4)..1, y ^ ((C.P : ℝ) / 4) * plG N C.lam ((C.w : ℝ) ^ 4) y := by
        rw [hpow]; simp only [hc1]; push_cast; rfl
      rw [e1] at hJ
      calc (∫⁻ y in Wa, A y * ∫⁻ u, ({u : ℝ | 1 - 1 / (N : ℝ) < clamp01 y + clamp01 u}).indicator
              (fun u => G0 y u) u ∂unif ∂unif) * ENNReal.ofReal (E * Ex)
          ≤ ENNReal.ofReal (Real.exp ((C.lam : ℝ) * K) * (B + 1 / N)) * ENNReal.ofReal (E * Ex) := by
            gcongr
            refine hJ.trans (ENNReal.ofReal_le_ofReal ?_)
            rw [hK]
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            linarith
        _ = ENNReal.ofReal (Q * (B + 1 / N)) := by
            rw [← ENNReal.ofReal_mul (by positivity), hQ]; ring_nf
  refine (measure_mono hsub).trans (hmain.trans ?_)
  have hsum : ∑ k ∈ (univ : Finset (Fin 3)), tt k * a k = t * (x0 * N + slT N) := by
    simp [Fin.sum_univ_three, htt, ha]
  rw [hsum]
  calc ENNReal.ofReal (Real.exp (t * (x0 * N + slT N))) * ∏ i : Fin N, ∫⁻ y, ∫⁻ u, ∫⁻ z, (W i).indicator
        (fun p => ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 3)), tt k * f k i p))) (y, u, z)
          ∂unif ∂unif ∂unif
      ≤ ENNReal.ofReal (Real.exp (t * (x0 * N + slT N))) *
          ∏ i : Fin N, ENNReal.ofReal (if i = x then Q * (2 * B) else Q * (B + 1 / N)) := by
        gcongr with i; exact hcol i
    _ = ENNReal.ofReal (Real.exp (t * (x0 * N + slT N)) * (Q * (2 * B) * (Q * (B + 1 / N)) ^ (N - 1))) := by
        rw [show (fun i : Fin N => ENNReal.ofReal (if i = x then Q * (2 * B) else Q * (B + 1 / N))) =
          fun i => if i = x then ENNReal.ofReal (Q * (2 * B)) else ENNReal.ofReal (Q * (B + 1 / N)) from
            funext fun i => by split_ifs <;> rfl, prod_ite_one, ← ENNReal.ofReal_pow hJ2,
          ← ENNReal.ofReal_mul hJ1, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        -- (1) J1 J2^{N-1} ≤ 2 (Q (B + 1/N))^N
        have hstep1 : Q * (2 * B) * (Q * (B + 1 / N)) ^ (N - 1) ≤ 2 * (Q * (B + 1 / N)) ^ N := by
          have hpow : (Q * (B + 1 / N)) ^ N = Q * (B + 1 / N) * (Q * (B + 1 / N)) ^ (N - 1) := by
            rw [← pow_succ']; congr 1; omega
          rw [hpow]
          have : Q * (2 * B) ≤ 2 * (Q * (B + 1 / N)) := by
            have : (0 : ℝ) ≤ 1 / N := by positivity
            nlinarith
          nlinarith [pow_nonneg hJ2 (N - 1)]
        -- (2) (B + 1/N)^N ≤ B^N e^{203}
        have hstep2 : (B + 1 / N) ^ N ≤ B ^ N * Real.exp 203 := by
          have h1 : B + 1 / N ≤ B * Real.exp (1 / (N * B)) := by
            have := Real.add_one_le_exp (1 / (N * B))
            have e : B + 1 / N = B * (1 / (N * B) + 1) := by field_simp; ring
            rw [e]; exact mul_le_mul_of_nonneg_left this hB0.le
          have h2 := pow_le_pow_left₀ (by positivity) h1 N
          rw [mul_pow, ← Real.exp_nat_mul] at h2
          have e2 : (N : ℝ) * (1 / (N * B)) = 1 / B := by field_simp
          rw [e2] at h2
          have h3 : 1 / B ≤ 203 := by rw [div_le_iff₀ hB0]; linarith
          exact h2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h3) (by positivity))
        -- (3) the rate
        have hrate := rate_of_log_le hB0 hEx0 hBrate N
        have h2N : (0 : ℝ) < 2 ^ N := by positivity
        have hslT : 0 ≤ slT N := by
          unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
          linarith
        have hslV : 0 ≤ slV N := by unfold slV; positivity
        have hKN := fsK_mul_le (N := N) hN
        have hKN0 := fsK_mul_nonneg (N := N)
        have hlamR : (C.lam : ℝ) ≤ 17 := by exact_mod_cast hlam
        have hluR : lu ≤ 3 := by rw [hludef]; exact_mod_cast hlu
        have htR : t ≤ 11 := by
          have : (C.P : ℝ) ≤ 30 := by exact_mod_cast hP
          rw [ht]; linarith
        have hQN : (Q * (B + 1 / N)) ^ N =
            Real.exp ((C.lam : ℝ) * (K * N)) * Real.exp (lu * slT N) * (Ex * (B + 1 / N)) ^ N := by
          rw [hQ, hE, mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
          rw [show (N : ℝ) * ((C.lam : ℝ) * K) = (C.lam : ℝ) * (K * N) by ring,
            show (N : ℝ) * (lu * (slT N / N)) = lu * slT N by field_simp]
          rw [mul_pow]; ring
        have hE1 : Real.exp (t * slT N) * (Real.exp ((C.lam : ℝ) * (K * N)) * Real.exp (lu * slT N)) ≤
            Real.exp (14 * slT N + 17 * (8 + slV N)) := by
          rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.2
          rw [hK]
          have a1 := mul_le_mul_of_nonneg_right htR hslT
          have a2 := mul_le_mul_of_nonneg_right hluR hslT
          have a3 := mul_le_mul hlamR hKN hKN0 (by norm_num : (0 : ℝ) ≤ 17)
          linarith
        have hrate' : Real.exp (t * (x0 * N)) * (B * Ex) ^ N ≤ Real.exp (-((plR : ℝ) * N)) / 2 ^ N := by
          rw [le_div_iff₀ h2N]; linarith [hrate]
        have hEB : (Ex * (B + 1 / N)) ^ N ≤ (B * Ex) ^ N * Real.exp 203 := by
          rw [mul_pow, mul_pow, mul_comm (B ^ N) (Ex ^ N), mul_assoc]
          exact mul_le_mul_of_nonneg_left hstep2 (by positivity)
        have h207 : 2 * Real.exp 203 ≤ Real.exp 210 := by
          have : (2 : ℝ) ≤ Real.exp 7 := by
            have := Real.add_one_le_exp (7 : ℝ); linarith
          calc 2 * Real.exp 203 ≤ Real.exp 7 * Real.exp 203 := by gcongr
            _ = Real.exp 210 := by rw [← Real.exp_add]; norm_num
        calc Real.exp (t * (x0 * N + slT N)) * (Q * (2 * B) * (Q * (B + 1 / N)) ^ (N - 1))
            ≤ Real.exp (t * (x0 * N + slT N)) * (2 * (Q * (B + 1 / N)) ^ N) :=
              mul_le_mul_of_nonneg_left hstep1 (Real.exp_pos _).le
          _ = 2 * (Real.exp (t * slT N) * (Real.exp ((C.lam : ℝ) * (K * N)) * Real.exp (lu * slT N))) *
                (Real.exp (t * (x0 * N)) * (Ex * (B + 1 / N)) ^ N) := by
              rw [hQN, mul_add, Real.exp_add]; ring
          _ ≤ 2 * Real.exp (14 * slT N + 17 * (8 + slV N)) *
                (Real.exp (t * (x0 * N)) * ((B * Ex) ^ N * Real.exp 203)) := by
              gcongr
          _ = (2 * Real.exp 203) * Real.exp (14 * slT N + 17 * (8 + slV N)) *
                (Real.exp (t * (x0 * N)) * (B * Ex) ^ N) := by ring
          _ ≤ Real.exp 210 * Real.exp (14 * slT N + 17 * (8 + slV N)) *
                (Real.exp (-((plR : ℝ) * N)) / 2 ^ N) := by
              gcongr
          _ = _ := by
              rw [show Real.exp (14 * slT N + 17 * (8 + slV N) + 210) =
                Real.exp 210 * Real.exp (14 * slT N + 17 * (8 + slV N)) by rw [← Real.exp_add]; ring_nf]
              ring

/-! ### 3. The joint bound -/

/-- The `pairLow` field with an explicit anchor row (cause side only). -/
def P0PairLow (N : ℕ) (_s : State N) : State N → Param N → Fin N → XSide → Prop := fun r0 w x σ =>
  σ = .cause → ∃ j, j ≠ x ∧ clamp01 (w r0 j) + clamp01 (w (flipAt x r0) j) ≤ 1 - 1 / (N : ℝ)

/-- **Joint bound for `pairLow`, PROVED** (rate `plR = 1.0202 > RJ`). -/
theorem joint_pairLow : JointBound P0PairLow := by
  have hab := poly_absorb (61 * Real.exp 210) 0 (δ := (plR : ℝ) - RJ) (by unfold plR RJ rsR0; norm_num)
  filter_upwards [hab, eventually_ge_atTop 15] with N hab hN s r0 x σ hfar
  cases σ with
  | effect =>
    have : {w : Param N | RegEvX N s r0 x .effect w ∧ ¬ P0PairLow N s r0 w x .effect} = ∅ := by
      ext w; simp [P0PairLow]
    rw [this, measure_empty]; exact bot_le
  | cause =>
    set SB := Real.exp (-((plR : ℝ) * N)) * Real.exp (14 * slT N + 17 * (8 + slV N) + 210) / 2 ^ N with hSB
    have hSB0 : 0 ≤ SB := by positivity
    have hsub : {w : Param N | RegEvX N s r0 x .cause w ∧ ¬ P0PairLow N s r0 w x .cause} ⊆
        ⋃ c ∈ cellsX .cause, ({w | CellEvX N s r0 x .cause c w} ∩ plFail N r0 x) := by
      rintro w ⟨⟨c, hc, hcw⟩, hn⟩
      simp only [P0PairLow, forall_const, not_exists, not_and, not_le] at hn
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
      exact ⟨c, hc, hcw, fun j hj => hn j hj⟩
    refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
    calc ∑ c ∈ cellsX .cause, cubeM N ({w | CellEvX N s r0 x .cause c w} ∩ plFail N r0 x)
        ≤ ∑ _c ∈ cellsX .cause, ENNReal.ofReal SB := sum_le_sum fun c hc =>
          pl_cause_cell (by omega) s r0 x (List.mem_toFinset.1 hc) (tf_far_ne2 (by omega) hfar)
            (tf_far_ne1 (by omega) hfar x)
      _ ≤ (61 : ENNReal) * ENNReal.ofReal SB := by
          rw [sum_const, nsmul_eq_mul]; gcongr; exact_mod_cast tf_cells_card .cause
      _ = ENNReal.ofReal (61 * SB) := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hsl := rs_slack_le N
          have hslT : 0 ≤ slT N := by
            unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
            linarith
          have h2N : (0 : ℝ) < 2 ^ N := by positivity
          have hk : 61 * Real.exp 210 * Real.exp (14 * slT N + 17 * (8 + slV N)) ≤
              Real.exp (((plR : ℝ) - RJ) * N) := by
            refine le_trans ?_ hab
            simp only [pow_zero, mul_one]
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)
          have e : 61 * SB = (61 * Real.exp 210 * Real.exp (14 * slT N + 17 * (8 + slV N))) *
              (Real.exp (-(((plR : ℝ) - RJ) * N)) * Real.exp (-(RJ * N))) / 2 ^ N := by
            rw [hSB, show Real.exp (14 * slT N + 17 * (8 + slV N) + 210) =
              Real.exp 210 * Real.exp (14 * slT N + 17 * (8 + slV N)) by rw [← Real.exp_add]; ring_nf,
              show Real.exp (-((plR : ℝ) * N)) = Real.exp (-(((plR : ℝ) - RJ) * N)) * Real.exp (-(RJ * N)) by
                rw [← Real.exp_add]; ring_nf]
            ring
          rw [e, div_le_div_iff_of_pos_right h2N]
          have hy : Real.exp (((plR : ℝ) - RJ) * N) * Real.exp (-(((plR : ℝ) - RJ) * N)) = 1 := by
            rw [← Real.exp_add]; simp
          calc (61 * Real.exp 210 * Real.exp (14 * slT N + 17 * (8 + slV N))) *
                (Real.exp (-(((plR : ℝ) - RJ) * N)) * Real.exp (-(RJ * N)))
              ≤ Real.exp (((plR : ℝ) - RJ) * N) * (Real.exp (-(((plR : ℝ) - RJ) * N)) * Real.exp (-(RJ * N))) := by
                gcongr
            _ = Real.exp (-(RJ * N)) := by rw [← mul_assoc, hy, one_mul]

end Census
end IIT

#print axioms IIT.Census.pl_cause_cell
#print axioms IIT.Census.joint_pairLow
