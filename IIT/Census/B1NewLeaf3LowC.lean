/-
Census, B1 GoodX3 leaf `lowFew`, cause side: `lc_cause_cell` (cause cell 0 jointly with `|lowU| > N/1000`, rate
`1.012`) and `lc_cause_joint` (all cause cells; the other cells have no low unit).
-/
import IIT.Census.B1NewLeaf3LowCert

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- The `lowFew` failure set. -/
def lowFail (N : ℕ) (r0 : State N) : Set (Param N) := {w | N < 1000 * (lowU N w r0).card}

/-- The number of low units as a sum of indicators. -/
lemma lowU_card_eq (w : Param N) (r0 : State N) :
    ∑ i, {y : ℝ | clamp01 y < 1 / 2 + Real.exp (-((N : ℝ) / 200))}.indicator (fun _ => (1 : ℝ)) (w r0 i) =
      ((lowU N w r0).card : ℝ) := by
  classical
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [Finset.sum_boole]
  unfold lowU
  congr 2

set_option maxHeartbeats 2000000 in
/-- **Cause cell 0 jointly with the `lowFew` failure.** -/
theorem lc_cause_cell (hN : 1 ≤ N) (s r0 : State N) (x : Fin N) (h1 : r0 ≠ s) (h3 : flipAt x r0 ≠ s)
    (hε : Real.exp (-((N : ℝ) / 200)) ≤ 1 / 10 ^ 7) :
    cubeM N ({w | CellEvX N s r0 x .cause lcc0 w} ∩ lowFail N r0) ≤
      ENNReal.ofReal (Real.exp (-((1012 / 1000 : ℝ) * N)) * Real.exp (14 * slT N + 17 * (8 + slV N)) / 2 ^ N) := by
  have hN0 : 0 < N := by omega
  have hok : rsCellOK lcC0 = true := lc_C0_ok
  have hunit := lc_unit
  have hz := lc_z
  have hlink := lc_link
  have hbd : lcC0.lam ≤ 17 ∧ lcC0.lu ≤ 3 ∧ lcC0.P ≤ 30 := by decide
  have hcapL : lcc0.2 ≤ lcC0.w ^ 4 := by decide +kernel
  set C := lcC0 with hCdef
  obtain ⟨hlam, hlu, hP⟩ := hbd
  obtain ⟨hJpos, hJrate⟩ := hunit
  have h' := hok
  simp only [rsCellOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hvw⟩, hw1⟩, hv1⟩, hw2⟩, hk⟩, hp⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
  obtain ⟨⟨⟨hz4, hzw⟩, hvz⟩, hL0⟩ := hz
  simp only [rsLink, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hlink
  obtain ⟨⟨hv4, -⟩, hc2⟩ := hlink
  set c1 : ℚ × ℚ := (C.v ^ 4, C.w ^ 4) with hc1
  have hv' : (0 : ℝ) < C.v := by exact_mod_cast hv
  have hmono1 : {w : Param N | CellEvX N s r0 x .cause lcc0 w} ⊆ {w | CellEvX N s r0 x .cause c1 w} :=
    cellEvX_mono hN0 s r0 x (by simp only [hc1]; exact_mod_cast hv4)
      (by left; simp only [hc1]; exact_mod_cast hcapL)
      (by exact_mod_cast hc2) (by simp only [hc1]; push_cast; exact pow_pos (by exact_mod_cast (lt_of_lt_of_le hv hvw)) 4)
  have hcm1 : (1 : ℝ) / 2 ≤ (c1.2 : ℝ) := by
    simp only [hc1]; have := (Rat.cast_le (K := ℝ)).2 hw2; push_cast at this ⊢; exact this
  have hm0 : (0 : ℝ) < (c1.1 : ℝ) := by simp only [hc1]; push_cast; positivity
  have hm1 : (c1.1 : ℝ) ≤ 1 := by
    simp only [hc1]; push_cast; exact pow_le_one₀ hv'.le (by exact_mod_cast hv1.le)
  have hsubC := cellEvX_sub_template hN0 s r0 x c1 hcm1
  set lu : ℝ := (C.lu : ℝ) with hludef
  set t : ℝ := (C.P : ℝ) / 4 + lu with ht
  have hlu0 : 0 ≤ lu := Nat.cast_nonneg _
  have htlu : lu ≤ t := by rw [ht]; have : (0 : ℝ) ≤ (C.P : ℝ) / 4 := by positivity
                           linarith
  set bb : ℝ := 1 / 2 + Real.exp (-((N : ℝ) / 200)) with hbb
  set zb : ℝ := (lcZ : ℝ) ^ 4 with hzb
  have hbz : bb ≤ zb := by
    have := (Rat.cast_le (K := ℝ)).2 hz4; push_cast at this; rw [hbb, hzb]; linarith
  have hz0 : (0 : ℝ) < lcZ := by have := lt_of_lt_of_le hv hvz; exact_mod_cast this
  have hzc : (c1.1 : ℝ) ≤ zb := by
    simp only [hc1, hzb]; push_cast; exact pow_le_pow_left₀ hv'.le (by exact_mod_cast hvz) 4
  have hz1 : zb ≤ 1 := by
    rw [hzb]; exact pow_le_one₀ hz0.le (by have := hzw.trans hw1; exact_mod_cast this)
  set Wa : Set ℝ := {y : ℝ | (c1.1 : ℝ) ≤ clamp01 y} with hWa
  have hWam : MeasurableSet Wa := measurableSet_le measurable_const clamp01_measurable
  set W : Fin N → Set (ℝ × ℝ × ℝ) := fun _ => {p | (c1.1 : ℝ) ≤ clamp01 p.1} with hW
  have hWm : ∀ i, MeasurableSet (W i) := fun _ =>
    measurableSet_le measurable_const (clamp01_measurable.comp measurable_fst)
  have hell : Measurable fun y : ℝ => -Real.log (clamp01 y) :=
    (Real.measurable_log.comp clamp01_measurable).neg
  have hellU : Measurable (ellUX N) := by
    unfold ellUX
    exact ((Real.measurable_log.comp (clamp01_measurable.max
      (measurable_const.sub clamp01_measurable))).neg).sub_const _
  set ind : ℝ → ℝ := fun y => {y : ℝ | clamp01 y < bb}.indicator (fun _ => (1 : ℝ)) y with hind
  have hindm : Measurable ind := measurable_const.indicator (measurableSet_lt clamp01_measurable measurable_const)
  set f : Fin 4 → Fin N → ℝ × ℝ × ℝ → ℝ :=
    ![fun _ p => -Real.log (clamp01 p.1), fun _ p => ellUX N p.2.2 - -Real.log (clamp01 p.1),
      fun _ p => gXev N c1 p.1 p.2.1, fun _ p => -ind p.1] with hf
  have hfm : ∀ k i, Measurable (f k i) := by
    intro k i
    fin_cases k
    · exact hell.comp measurable_fst
    · exact (hellU.comp (measurable_snd.comp measurable_snd)).sub (hell.comp measurable_fst)
    · exact (fs_gXev_meas c1).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    · exact (hindm.comp measurable_fst).neg
  set a : Fin 4 → ℝ := ![x0 * N + slT N, 0, 0, -((N : ℝ) / 1000)] with ha
  set tt : Fin 4 → ℝ := ![t, lu, (C.lam : ℝ), 6] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 4)), 0 ≤ tt k := by
    intro k _; fin_cases k
    · simp only [htt]; simp; positivity
    · simpa [htt] using hlu0
    · simp [htt]
    · simp [htt]
  have hmain := cubeM_chernoff_three_win (fun _ => r0) (fun _ => flipAt x r0) (fun _ => s)
    (fun _ => (flipAt_ne x r0).symm) (fun _ => h1) (fun _ => h3) univ f hfm a tt htt0 W hWm
  have hsub : ({w | CellEvX N s r0 x .cause lcc0 w} ∩ lowFail N r0 : Set (Param N)) ⊆
      {w | (∀ i, (w ((fun _ : Fin N => r0) i) i, w ((fun _ : Fin N => flipAt x r0) i) i,
          w ((fun _ : Fin N => s) i) i) ∈ W i) ∧
        ∀ k ∈ (univ : Finset (Fin 4)), ∑ i, f k i (w ((fun _ : Fin N => r0) i) i,
          w ((fun _ : Fin N => flipAt x r0) i) i, w ((fun _ : Fin N => s) i) i) ≤ a k} := by
    rintro w ⟨hw1, hw2⟩
    obtain ⟨hW1, hT, hL, hV⟩ := hsubC (hmono1 hw1)
    refine ⟨fun i => hW1 i, fun k _ => ?_⟩
    fin_cases k
    · simpa [hf, ha] using hT
    · simp only [hf, ha, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [sum_sub_distrib]; linarith
    · simpa [hf, ha] using hV
    · have hc := lowU_card_eq w r0
      have hlt : (N : ℝ) < 1000 * ((lowU N w r0).card : ℝ) := by exact_mod_cast hw2
      show ∑ i, -ind (w r0 i) ≤ -((N : ℝ) / 1000)
      rw [sum_neg_distrib]
      have : ∑ i, ind (w r0 i) = ((lowU N w r0).card : ℝ) := hc
      rw [this]; linarith
  -- the column constants
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = fsK N := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (lu * (slT N / N)) := ⟨_, rfl⟩
  obtain ⟨Ex, hExd⟩ : ∃ Ex : ℝ, Ex = 2 * (1 - (1 / 2 : ℝ) ^ (C.lu + 1)) / (C.lu + 1) := ⟨_, rfl⟩
  have hEx2 : (rsEx C.lu : ℝ) = Ex := by rw [hExd, rsEx_cast]
  rw [hEx2] at hJrate
  have hEx0 : 0 < Ex := by
    rw [hExd]
    have : (1 / 2 : ℝ) ^ (C.lu + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    apply div_pos (by linarith) (by positivity)
  obtain ⟨Jp, hJp⟩ : ∃ Jp : ℝ, Jp = fsI C + (Real.exp 6 - 1) *
      ∫ y in ((C.v : ℝ) ^ 4)..((lcZ : ℝ) ^ 4), y ^ ((C.P : ℝ) / 4) * gX C.lam ((C.w : ℝ) ^ 4) y := ⟨_, rfl⟩
  rw [← hJp] at hJpos hJrate
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = Real.exp ((C.lam : ℝ) * K) * (E * Ex) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ, hE]; positivity
  have hLw : 0 ≤ ∫ y in ((C.v : ℝ) ^ 4)..((lcZ : ℝ) ^ 4), y ^ ((C.P : ℝ) / 4) * gX C.lam ((C.w : ℝ) ^ 4) y := by
    rw [lowQ_eq C.v lcZ C.w hv hvz hzw C.lam C.P (fun k hkm => hk k (Finset.mem_range.1 hkm)) hp]
    exact_mod_cast hL0
  have he1 : 0 ≤ Real.exp 6 - 1 := by have := Real.add_one_le_exp (6 : ℝ); linarith
  -- the column bound
  have hcol : ∀ i : Fin N, ∫⁻ y, ∫⁻ u, ∫⁻ z, (W i).indicator
      (fun p => ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)), tt k * f k i p))) (y, u, z)
        ∂unif ∂unif ∂unif ≤ ENNReal.ofReal (Q * Jp) := by
    intro i
    set F1 : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 y)) *
      Real.exp (6 * ind y)) with hF1
    set G0 : ℝ → ℝ → ENNReal := fun y u => ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXev N c1 y u)) with hG0
    set F3 : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp (-lu * ellUX N z)) with hF3
    have hF1m : Measurable F1 := ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp (hell.const_mul _)).mul (Real.measurable_exp.comp (hindm.const_mul _)))
    have hG0m : Measurable fun p : ℝ × ℝ => G0 p.1 p.2 :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((fs_gXev_meas c1).const_mul _))
    have hF3m : Measurable F3 := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hellU.const_mul _))
    have hpt : ∀ y u z, (W i).indicator
        (fun p => ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)), tt k * f k i p))) (y, u, z) ≤
        Wa.indicator F1 y * G0 y u * F3 z := by
      intro y u z
      by_cases hp' : (y, u, z) ∈ W i
      · rw [Set.indicator_of_mem hp', Set.indicator_of_mem (show y ∈ Wa from hp')]
        simp only [hF1, hG0, hF3]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        apply le_of_eq
        congr 2
        simp only [Fin.sum_univ_four, hf, htt, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
        ring
      · rw [Set.indicator_of_notMem hp']; exact bot_le
    have hstep : ∫⁻ y, ∫⁻ u, ∫⁻ z, (W i).indicator
        (fun p => ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)), tt k * f k i p))) (y, u, z)
          ∂unif ∂unif ∂unif ≤ (∫⁻ y in Wa, F1 y * ∫⁻ u, G0 y u ∂unif ∂unif) * ∫⁻ z, F3 z ∂unif := by
      calc _ ≤ ∫⁻ y, ∫⁻ u, ∫⁻ z, Wa.indicator F1 y * G0 y u * F3 z ∂unif ∂unif ∂unif :=
            lintegral_mono fun y => lintegral_mono fun u => lintegral_mono fun z => hpt y u z
        _ = (∫⁻ y, Wa.indicator F1 y * ∫⁻ u, G0 y u ∂unif ∂unif) * ∫⁻ z, F3 z ∂unif :=
            pl_lint3 _ G0 F3 (hF1m.indicator hWam) hG0m hF3m
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
    have hY := lc_ypart (N := N) C.lam c1 hcm1 hm0 hm1 (t := t) (lamU := lu) htlu hbz hzc hz1
      (θ := 6) (by norm_num)
    have e1 : (∫ y in (c1.1 : ℝ)..1, y ^ (t - lu) * gX C.lam (c1.2 : ℝ) y) = fsI C := by
      rw [hpow]; simp only [hc1, fsI]; push_cast; rfl
    have e2 : (∫ y in (c1.1 : ℝ)..zb, y ^ (t - lu) * gX C.lam (c1.2 : ℝ) y) =
        ∫ y in ((C.v : ℝ) ^ 4)..((lcZ : ℝ) ^ 4), y ^ ((C.P : ℝ) / 4) * gX C.lam ((C.w : ℝ) ^ 4) y := by
      rw [hpow, hzb]; simp only [hc1]; push_cast; rfl
    rw [e1, e2] at hY
    have hIpos := fs_cell_pos C hok
    calc (∫⁻ y in Wa, F1 y * ∫⁻ u, G0 y u ∂unif ∂unif) * ENNReal.ofReal (E * Ex)
        ≤ (ENNReal.ofReal (Real.exp ((C.lam : ℝ) * K) * fsI C) + ENNReal.ofReal (Real.exp 6 - 1) *
            ENNReal.ofReal (Real.exp ((C.lam : ℝ) * K) *
              ∫ y in ((C.v : ℝ) ^ 4)..((lcZ : ℝ) ^ 4), y ^ ((C.P : ℝ) / 4) * gX C.lam ((C.w : ℝ) ^ 4) y)) *
            ENNReal.ofReal (E * Ex) := by
          gcongr
          rw [hK]; exact hY
      _ = ENNReal.ofReal (Q * Jp) := by
          rw [← ENNReal.ofReal_mul he1, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by positivity), hQ, hJp]
          congr 1; ring
  refine (measure_mono hsub).trans (hmain.trans ?_)
  have hsum : ∑ k ∈ (univ : Finset (Fin 4)), tt k * a k = t * (x0 * N + slT N) - 6 * ((N : ℝ) / 1000) := by
    simp [Fin.sum_univ_four, htt, ha]; ring
  rw [hsum]
  have hJ0 : 0 ≤ Q * Jp := by positivity
  calc ENNReal.ofReal (Real.exp (t * (x0 * N + slT N) - 6 * ((N : ℝ) / 1000))) * ∏ i : Fin N, ∫⁻ y, ∫⁻ u, ∫⁻ z,
        (W i).indicator (fun p => ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 4)), tt k * f k i p)))
          (y, u, z) ∂unif ∂unif ∂unif
      ≤ ENNReal.ofReal (Real.exp (t * (x0 * N + slT N) - 6 * ((N : ℝ) / 1000))) *
          ∏ _i : Fin N, ENNReal.ofReal (Q * Jp) := by
        gcongr with i; exact hcol i
    _ = ENNReal.ofReal (Real.exp (t * (x0 * N + slT N) - 6 * ((N : ℝ) / 1000)) * (Q * Jp) ^ N) := by
        rw [prod_const, card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow hJ0,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hrate := rate_of_log_le hJpos hEx0 hJrate N
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
        have hQN : (Q * Jp) ^ N = Real.exp ((C.lam : ℝ) * (K * N)) * Real.exp (lu * slT N) * (Jp * Ex) ^ N := by
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
        have hrate' : Real.exp (t * (x0 * N)) * (Jp * Ex) ^ N ≤ Real.exp (-((1006 / 1000 : ℝ) * N)) / 2 ^ N := by
          rw [le_div_iff₀ h2N]; linarith [hrate]
        have hR : Real.exp (-((1006 / 1000 : ℝ) * N)) * Real.exp (-(6 * ((N : ℝ) / 1000))) =
            Real.exp (-((1012 / 1000 : ℝ) * N)) := by rw [← Real.exp_add]; ring_nf
        calc Real.exp (t * (x0 * N + slT N) - 6 * ((N : ℝ) / 1000)) * (Q * Jp) ^ N
            = (Real.exp (t * slT N) * (Real.exp ((C.lam : ℝ) * (K * N)) * Real.exp (lu * slT N))) *
                (Real.exp (t * (x0 * N)) * (Jp * Ex) ^ N) * Real.exp (-(6 * ((N : ℝ) / 1000))) := by
              rw [hQN, sub_eq_add_neg, mul_add, Real.exp_add, Real.exp_add]; ring
          _ ≤ Real.exp (14 * slT N + 17 * (8 + slV N)) *
                (Real.exp (-((1006 / 1000 : ℝ) * N)) / 2 ^ N) * Real.exp (-(6 * ((N : ℝ) / 1000))) := by
              gcongr
          _ = _ := by rw [← hR]; ring

/-- **The cause side of `lowFew`**: only cell 0 meets the low window. -/
theorem lc_cause_joint (hN : 15 ≤ N) (hε : Real.exp (-((N : ℝ) / 200)) ≤ 1 / 10 ^ 7) (s r0 : State N) (x : Fin N)
    (hfar : N ≤ 3 * ham r0 s) :
    cubeM N {w | RegEvX N s r0 x .cause w ∧ N < 1000 * (lowU N w r0).card} ≤
      ENNReal.ofReal (Real.exp (-((1012 / 1000 : ℝ) * N)) * Real.exp (14 * slT N + 17 * (8 + slV N)) / 2 ^ N) := by
  refine (measure_mono ?_).trans (lc_cause_cell (by omega) s r0 x (tf_far_ne2 (by omega) hfar)
    (tf_far_ne1 (by omega) hfar x) hε)
  rintro w ⟨⟨c, hc, hcw⟩, hlow⟩
  have hcl := List.all_eq_true.1 lc_cells c (List.mem_toFinset.1 hc)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hcl
  rcases hcl with hc1 | hc0
  · exfalso
    have hcard : (lowU N w r0).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro j hj
      have hj' : clamp01 (w r0 j) < 1 / 2 + Real.exp (-((N : ℝ) / 200)) := by
        unfold lowU at hj; simpa using hj
      have h1 := hcw.1 j
      simp only [baseE] at h1
      have : ((5001 / 10000 : ℚ) : ℝ) ≤ (c.1 : ℝ) := by exact_mod_cast hc1
      push_cast at this
      linarith
    rw [hcard] at hlow; omega
  · subst hc0
    exact ⟨hcw, hlow⟩

end Census
end IIT

#print axioms IIT.Census.lc_cause_cell
#print axioms IIT.Census.lc_cause_joint
