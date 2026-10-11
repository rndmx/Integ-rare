/-
Census, B1 forced leaf 19 (`sRowMu`, agent "forcedF"): one entry of row `s` in the window `[1/2, 1/2 + ε)`.

Per `(r0, x, σ)`, `k` and cell: the regime template with column `k` of row `s` restricted to the window.
* cause side (row `s` is the link row): the column-`k` link factor `≤ 2ε e^{l_u slT/N}` instead of
  `rsEx(l_u) e^{l_u slT/N}`, so the cell bound gains `2ε/rsEx(l_u) ≤ (64/15) ε`;
* effect side (row `s` is the base row): the column-`k` factor is `≤ 2ε e^{l_u slT/N} e^{λK} (3/2)^λ (H + δ)`.
With `ε = e^{N/100} σ_N = e^{-(x0 - 1/100) N}` the rate is `R0 + x0 - 1/100 > RJ`.
-/
import IIT.Census.B1ForcedFTwoLeaf
import IIT.Census.B1ForcedF0

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- The window set of one row entry. -/
def srWin (ε : ℝ) : Set ℝ := {z | max (clamp01 z) (1 - clamp01 z) < 1 / 2 + ε}

lemma srWin_meas (ε : ℝ) : MeasurableSet (srWin ε) :=
  measurableSet_lt (clamp01_measurable.max (measurable_const.sub clamp01_measurable)) measurable_const

lemma unif_srWin_le {ε : ℝ} (hε : 0 ≤ ε) {S : Set ℝ} (hS : S ⊆ srWin ε) : unif S ≤ ENNReal.ofReal (2 * ε) := by
  unfold unif
  rw [Measure.restrict_apply' measurableSet_Icc]
  calc volume (S ∩ Set.Icc 0 1) ≤ volume (Set.Icc (1 / 2 - ε) (1 / 2 + ε)) := by
        refine measure_mono fun z hz => ?_
        have hw := hS hz.1
        simp only [srWin, Set.mem_setOf_eq] at hw
        rw [fs_clamp_of_mem hz.2] at hw
        have h1 := le_max_left z (1 - z); have h2 := le_max_right z (1 - z)
        exact ⟨by linarith, by linarith⟩
    _ = ENNReal.ofReal (2 * ε) := by rw [Real.volume_Icc]; congr 1; ring

/-- `∏_i (if i = k then a else b) = a b^{N-1}`. -/
lemma prod_ite_one (k : Fin N) (a b : ENNReal) :
    ∏ i : Fin N, (if i = k then a else b) = a * b ^ (N - 1) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ k), if_pos rfl]
  congr 1
  rw [Finset.prod_congr rfl fun i hi => if_neg (ne_of_mem_erase hi), prod_const, card_erase_of_mem (mem_univ k),
    card_univ, Fintype.card_fin]

set_option maxHeartbeats 1000000 in
/-- **Cause cell with one window entry of row `s`.** -/
theorem sr_cause_cell (hN : 2 ≤ N) (s r0 : State N) (x x' : Fin N) (hxx : x' ≠ x) (k : Fin N) {c : ℚ × ℚ}
    (hc : c ∈ cellsXCauseData) (h1 : r0 ≠ s) (h3 : flipAt x r0 ≠ s) (hd : flipAt x' r0 ≠ s) {ε : ℝ}
    (hε : 0 ≤ ε) :
    cubeM N ({w | CellEvX N s r0 x .cause c w} ∩ {w | w s k ∈ srWin ε}) ≤
      ENNReal.ofReal (Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (14 * slT N + 17 * (8 + slV N)) / 2 ^ N *
        (5 * ε)) := by
  have hN0 : 0 < N := by omega
  obtain ⟨C, hC, hok, hlam, hlu, hP, hmono1, hcm1, hm0, hm1⟩ := fs_cause_partner hN0 hc
  set c1 : ℚ × ℚ := (C.v ^ 4, C.w ^ 4) with hc1
  have hsubC := cellEvX_sub_template hN0 s r0 x c1 hcm1
  set lu : ℝ := (C.lu : ℝ) with hludef
  set t : ℝ := (C.P : ℝ) / 4 + lu with ht
  have hlu0 : 0 ≤ lu := Nat.cast_nonneg _
  set Wa : Set ℝ := {y : ℝ | (c1.1 : ℝ) ≤ clamp01 y} with hWa
  have hWam : MeasurableSet Wa := measurableSet_le measurable_const clamp01_measurable
  set Wc : Fin N → Set ℝ := fun i => if i = k then srWin ε else Set.univ with hWc
  have hWcm : ∀ i, MeasurableSet (Wc i) := fun i => by
    simp only [hWc]; split_ifs
    · exact srWin_meas ε
    · exact MeasurableSet.univ
  set f : Fin 3 → Fin N → (ℝ × ℝ) × (ℝ × ℝ) → ℝ :=
    ![fun _ p => -Real.log (clamp01 p.1.1), fun _ p => ellSX N p.2.1 - -Real.log (clamp01 p.1.1),
      fun _ p => gXev N c1 p.1.1 p.1.2] with hf
  have hell : Measurable fun y : ℝ => -Real.log (clamp01 y) :=
    (Real.measurable_log.comp clamp01_measurable).neg
  have hfm : ∀ k i, Measurable (f k i) := by
    intro k i
    fin_cases k
    · exact hell.comp (measurable_fst.comp measurable_fst)
    · exact (fs_ellSX_meas.comp (measurable_fst.comp measurable_snd)).sub (hell.comp (measurable_fst.comp measurable_fst))
    · exact (fs_gXev_meas c1).comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst))
  set a : Fin 3 → ℝ := ![x0 * N + slT N, 0, 0] with ha
  set tt : Fin 3 → ℝ := ![t, lu, (C.lam : ℝ)] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 3)), 0 ≤ tt k := by
    intro k _; fin_cases k
    · simp only [htt]; simp; positivity
    · simpa [htt] using hlu0
    · simp [htt]
  have hmain := cubeM_chernoff_four (fun _ => r0) (fun _ => flipAt x r0) (fun _ => s) (fun _ => flipAt x' r0)
    (fun _ => (flipAt_ne x r0).symm) (fun _ => h1) (fun _ => (flipAt_ne x' r0).symm) (fun _ => h3)
    (fun _ => fs_flip_ne hxx r0) (fun _ => Ne.symm hd) univ f hfm a tt htt0 (fun _ => Wa) Wc (fun _ => hWam) hWcm
  have hsub : ({w | CellEvX N s r0 x .cause c w} ∩ {w | w s k ∈ srWin ε} : Set (Param N)) ⊆
      {w | (∀ i, w ((fun _ : Fin N => r0) i) i ∈ (fun _ : Fin N => Wa) i ∧ w ((fun _ : Fin N => s) i) i ∈ Wc i) ∧
        ∀ j ∈ (univ : Finset (Fin 3)), ∑ i, f j i ((w ((fun _ : Fin N => r0) i) i,
          w ((fun _ : Fin N => flipAt x r0) i) i), (w ((fun _ : Fin N => s) i) i,
            w ((fun _ : Fin N => flipAt x' r0) i) i)) ≤ a j} := by
    rintro w ⟨hw1, hw2⟩
    obtain ⟨hW1, hT, hL, hV⟩ := hsubC (hmono1 s r0 x hw1)
    refine ⟨fun i => ⟨hW1 i, ?_⟩, fun j _ => ?_⟩
    · simp only [hWc]; split_ifs with h
      · subst h; exact hw2
      · exact Set.mem_univ _
    fin_cases j
    · simpa [hf, ha] using hT
    · simp only [hf, ha]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [sum_sub_distrib]
      have : ∑ i, ellSX N (w s i) = ∑ i, ellUX N (w s i) := rfl
      rw [this]; linarith
    · simpa [hf, ha] using hV
  -- the column factors
  set I1 := fsI C with hI1
  have hI10 := fs_cell_pos C hok
  set Ex : ℝ := 2 * (1 - (1 / 2 : ℝ) ^ (C.lu + 1)) / (C.lu + 1) with hEx
  have hEx0 : 15 / 32 ≤ Ex := by
    have key : ∀ n : ℕ, n ≤ 3 → (15 : ℝ) / 32 ≤ 2 * (1 - (1 / 2 : ℝ) ^ (n + 1)) / (n + 1) := by
      intro n hn; interval_cases n <;> norm_num
    exact key C.lu hlu
  set J1 : ℝ := Real.exp ((C.lam : ℝ) * fsK N) * I1 with hJ1
  set E : ℝ := Real.exp (lu * (slT N / N)) with hE
  set J : ℝ := J1 * (E * Ex) with hJ
  set Jk : ℝ := J1 * (E * (2 * ε)) with hJk
  have hJ0 : 0 ≤ J := by have : 0 ≤ Ex := by linarith
                         positivity
  have hJk0 : 0 ≤ Jk := by positivity
  have hcol : ∀ i : Fin N, ∫⁻ y in (fun _ : Fin N => Wa) i, ∫⁻ u, ∫⁻ z in Wc i, ∫⁻ v,
      ENNReal.ofReal (Real.exp (-∑ j ∈ (univ : Finset (Fin 3)), tt j * f j i ((y, u), (z, v))))
        ∂unif ∂unif ∂unif ∂unif ≤ ENNReal.ofReal (if i = k then Jk else J) := by
    intro i
    have hpt : ∀ y u z v, ENNReal.ofReal (Real.exp (-∑ j ∈ (univ : Finset (Fin 3)), tt j * f j i ((y, u), (z, v)))) =
        ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 y))) *
          ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXev N c1 y u)) *
          (ENNReal.ofReal (Real.exp (-lu * ellSX N z)) * ENNReal.ofReal (Real.exp 0)) := by
      intro y u z v
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 2
      simp [Fin.sum_univ_three, hf, htt]
      ring
    simp_rw [hpt]
    have m1 : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 y))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hell.const_mul _))
    have m2 : Measurable fun z : ℝ => ENNReal.ofReal (Real.exp (-lu * ellSX N z)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (fs_ellSX_meas.const_mul _))
    have m3 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXev N c1 p.1 p.2)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((fs_gXev_meas c1).const_mul _))
    rw [lint4_split Wa (Wc i) (fun y => ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 y))))
      (fun z => ENNReal.ofReal (Real.exp (-lu * ellSX N z)))
      (fun y u => ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXev N c1 y u)))
      (fun _ _ => ENNReal.ofReal (Real.exp 0)) m1 m2 m3 measurable_const]
    have hJ1b := cell_J_le (N := N) C.lam c1 hcm1 hm0 hm1 (t := t) (lamU := lu) (by
      rw [ht]; have : (0 : ℝ) ≤ (C.P : ℝ) / 4 := by positivity
      linarith)
    have e1 : (∫ y in (c1.1 : ℝ)..1, y ^ (t - lu) * gX C.lam (c1.2 : ℝ) y) = I1 := by
      simp only [hc1, ht, add_sub_cancel_right, hI1, fsI]; push_cast; rfl
    rw [e1] at hJ1b
    have hone : ∫⁻ _v : ℝ, ENNReal.ofReal (Real.exp 0) ∂unif = 1 := by
      rw [Real.exp_zero, ENNReal.ofReal_one, lintegral_const, unif_univ, mul_one]
    simp_rw [hone, mul_one]
    have hF2 : ∫⁻ z in Wc i, ENNReal.ofReal (Real.exp (-lu * ellSX N z)) ∂unif ≤
        ENNReal.ofReal (if i = k then E * (2 * ε) else E * Ex) := by
      by_cases hik : i = k
      · rw [if_pos hik]
        have hWk : Wc i = srWin ε := by simp only [hWc, if_pos hik]
        rw [hWk]
        calc ∫⁻ z in srWin ε, ENNReal.ofReal (Real.exp (-lu * ellSX N z)) ∂unif
            ≤ ∫⁻ _z in srWin ε, ENNReal.ofReal E ∂unif := by
              refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
              obtain ⟨hX1, hX2⟩ := fs_X_bounds z
              have hX0 : 0 < max (clamp01 z) (1 - clamp01 z) := by linarith
              have e : Real.exp (-lu * ellSX N z) = E * (max (clamp01 z) (1 - clamp01 z)) ^ lu := by
                unfold ellSX; rw [hE, Real.rpow_def_of_pos hX0, ← Real.exp_add]; congr 1; ring
              rw [e]
              have := Real.rpow_le_one hX0.le hX2 hlu0
              have := Real.exp_pos (lu * (slT N / N))
              nlinarith
          _ = ENNReal.ofReal E * unif (srWin ε) := by rw [setLIntegral_const]
          _ ≤ ENNReal.ofReal E * ENNReal.ofReal (2 * ε) := by gcongr; exact unif_srWin_le hε le_rfl
          _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
      · rw [if_neg hik]
        have hWk : Wc i = Set.univ := by simp only [hWc, if_neg hik]
        rw [hWk, Measure.restrict_univ]
        have := lintegral_ellUX (N := N) C.lu
        rw [show -(C.lu : ℝ) = -lu from rfl] at this
        exact le_of_eq this
    calc _ ≤ ENNReal.ofReal J1 * ENNReal.ofReal (if i = k then E * (2 * ε) else E * Ex) := by
          refine mul_le_mul' (le_trans ?_ (le_of_eq rfl)) hF2
          simpa [hJ1, fsK] using hJ1b
      _ = ENNReal.ofReal (if i = k then Jk else J) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          split_ifs <;> rfl
  refine (measure_mono hsub).trans (hmain.trans ?_)
  have hsum : ∑ j ∈ (univ : Finset (Fin 3)), tt j * a j = t * (x0 * N + slT N) := by
    simp [Fin.sum_univ_three, htt, ha]
  rw [hsum]
  calc ENNReal.ofReal (Real.exp (t * (x0 * N + slT N))) * ∏ i : Fin N, ∫⁻ y in (fun _ : Fin N => Wa) i,
        ∫⁻ u, ∫⁻ z in Wc i, ∫⁻ v,
          ENNReal.ofReal (Real.exp (-∑ j ∈ (univ : Finset (Fin 3)), tt j * f j i ((y, u), (z, v))))
            ∂unif ∂unif ∂unif ∂unif
      ≤ ENNReal.ofReal (Real.exp (t * (x0 * N + slT N))) *
          ∏ i : Fin N, ENNReal.ofReal (if i = k then Jk else J) := by
        gcongr with i; exact hcol i
    _ = ENNReal.ofReal (Real.exp (t * (x0 * N + slT N)) * (Jk * J ^ (N - 1))) := by
        rw [show (fun i : Fin N => ENNReal.ofReal (if i = k then Jk else J)) =
          fun i => if i = k then ENNReal.ofReal Jk else ENNReal.ofReal J from
            funext fun i => by split_ifs <;> rfl, prod_ite_one, ← ENNReal.ofReal_pow hJ0,
          ← ENNReal.ofReal_mul hJk0, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        -- `Jk J^{N-1} = J^N · (2ε/Ex)`
        have hEx' : 0 < Ex := by linarith
        have hJN : Jk * J ^ (N - 1) = J ^ N * (2 * ε / Ex) := by
          have : J ^ N = J * J ^ (N - 1) := by rw [← pow_succ']; congr 1; omega
          rw [this, hJk, hJ]; field_simp
        rw [hJN]
        -- the regime rate (as in `causeCell_prob`)
        have hsound := rsCell_sound C hok
        have hEx2 : (rsEx C.lu : ℝ) = Ex := by rw [hEx, rsEx_cast]
        have hEx'' : (0 : ℝ) < rsEx C.lu := by rw [hEx2]; exact hEx'
        have hrate := rate_of_log_le hI10 hEx'' hsound N
        rw [hEx2] at hrate
        have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
        have h2N : (0 : ℝ) < 2 ^ N := by positivity
        have hslT : 0 ≤ slT N := by
          unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
          linarith
        have hslV : 0 ≤ slV N := by unfold slV; positivity
        have hKN := fsK_mul_le (N := N) (by omega)
        have hKN0 := fsK_mul_nonneg (N := N)
        have hlamR : (C.lam : ℝ) ≤ 17 := by exact_mod_cast hlam
        have hluR : lu ≤ 3 := by rw [hludef]; exact_mod_cast hlu
        have htR : t ≤ 11 := by
          have : (C.P : ℝ) ≤ 30 := by exact_mod_cast hP
          rw [ht]; linarith
        have e1 : J ^ N = Real.exp ((C.lam : ℝ) * (fsK N * N)) * Real.exp (lu * slT N) * (I1 * Ex) ^ N := by
          rw [hJ, hJ1, hE, mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
          rw [show (N : ℝ) * ((C.lam : ℝ) * fsK N) = (C.lam : ℝ) * (fsK N * N) by ring,
            show (N : ℝ) * (lu * (slT N / N)) = lu * slT N by field_simp]
          ring
        rw [e1]
        have hE1 : Real.exp (t * slT N) * (Real.exp ((C.lam : ℝ) * (fsK N * N)) * Real.exp (lu * slT N)) ≤
            Real.exp (14 * slT N + 17 * (8 + slV N)) := by
          rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.2
          have a1 := mul_le_mul_of_nonneg_right htR hslT
          have a2 := mul_le_mul_of_nonneg_right hluR hslT
          have a3 := mul_le_mul hlamR hKN hKN0 (by norm_num : (0 : ℝ) ≤ 17)
          linarith
        have hrate' : Real.exp (t * (x0 * N)) * (I1 * Ex) ^ N ≤ Real.exp (-((rsR0 : ℝ) * N)) / 2 ^ N := by
          rw [le_div_iff₀ h2N]; linarith [hrate]
        have h5 : 2 * ε / Ex ≤ 5 * ε := by
          have h := mul_le_mul_of_nonneg_left hEx0 (show (0 : ℝ) ≤ 5 * ε by positivity)
          rw [div_le_iff₀ hEx']; linarith
        calc Real.exp (t * (x0 * N + slT N)) *
              (Real.exp ((C.lam : ℝ) * (fsK N * N)) * Real.exp (lu * slT N) * (I1 * Ex) ^ N * (2 * ε / Ex))
            = (Real.exp (t * (x0 * N)) * (I1 * Ex) ^ N) *
                (Real.exp (t * slT N) * (Real.exp ((C.lam : ℝ) * (fsK N * N)) * Real.exp (lu * slT N))) *
                  (2 * ε / Ex) := by rw [mul_add, Real.exp_add]; ring
          _ ≤ (Real.exp (-((rsR0 : ℝ) * N)) / 2 ^ N) * Real.exp (14 * slT N + 17 * (8 + slV N)) * (5 * ε) := by
              gcongr
          _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- **Effect cell with one window entry of row `s`.** -/
theorem sr_eff_cell (hN : 2 ≤ N) (hδ : deltaU N < 1 / 2) (s r0 : State N) (x x' : Fin N) (hxx : x' ≠ x)
    (k : Fin N) {c : ℚ × ℚ} (hc : c ∈ cellsXEffectData) (h1 : r0 ≠ s) (h2 : r0 ≠ flipAt x s)
    (hd : r0 ≠ flipAt x' s) {ε : ℝ} (hε : 0 ≤ ε) :
    cubeM N ({w | CellEvX N s r0 x .effect c w} ∩ {w | w s k ∈ srWin ε}) ≤
      ENNReal.ofReal (Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (19 * slT N + 17 * (8 + slV N) + 20) / 2 ^ N *
        (5 * ε)) := by
  have hN0 : 0 < N := by omega
  have hδ0 : 0 < deltaU N := by unfold deltaU; positivity
  obtain ⟨C, hC, hok, hlam, hlu, hP, hv, hv1, hw4, hb, hcap, hc2⟩ := fs_eff_partner hc
  set c1 : ℚ × ℚ := (c.1, C.w ^ 4) with hc1
  have hc12 : (c1.2 : ℝ) = (C.w : ℝ) ^ 4 := by simp only [hc1]; push_cast; rfl
  have hcm1 : (1 : ℝ) / 2 ≤ (c1.2 : ℝ) := by rw [hc12]; exact hw4
  have hmono := cellEvX_mono_eff s r0 x (c := c) (c' := c1) (by simp only [hc1])
    (by rw [hc12]; exact hcap) (by linarith) (by linarith)
  have hsubE := cellEvX_eff_sub_template hN0 s r0 x c1 hcm1 hδ
  set lu : ℝ := (C.P : ℝ) / 4 with hludef
  set t : ℝ := lu + C.lu with ht
  have hlu0 : 0 ≤ lu := by positivity
  set Wx : Set ℝ := {y : ℝ | (c1.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} with hWx
  have hWxm : MeasurableSet Wx :=
    measurableSet_le measurable_const (clamp01_measurable.max (measurable_const.sub clamp01_measurable))
  set Wa : Fin N → Set ℝ := fun i => if i = k then Wx ∩ srWin ε else Wx with hWa
  have hWam : ∀ i, MeasurableSet (Wa i) := fun i => by
    simp only [hWa]; split_ifs
    · exact hWxm.inter (srWin_meas ε)
    · exact hWxm
  set Wc : Set ℝ := {y : ℝ | 1 / 2 - deltaU N ≤ y} with hWc
  have hWcm : MeasurableSet Wc := measurableSet_le measurable_const measurable_id
  set f : Fin 3 → Fin N → (ℝ × ℝ) × (ℝ × ℝ) → ℝ :=
    ![fun _ p => -Real.log (clamp01 p.2.1), fun _ p => ellSX N p.1.1 - -Real.log (clamp01 p.2.1),
      fun _ p => gXevE N c1 p.1.1 p.1.2] with hf
  have hell : Measurable fun y : ℝ => -Real.log (clamp01 y) :=
    (Real.measurable_log.comp clamp01_measurable).neg
  have hfm : ∀ k i, Measurable (f k i) := by
    intro k i
    fin_cases k
    · exact hell.comp (measurable_fst.comp measurable_snd)
    · exact (fs_ellSX_meas.comp (measurable_fst.comp measurable_fst)).sub (hell.comp (measurable_fst.comp measurable_snd))
    · exact (fs_gE_meas c1).comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst))
  set a : Fin 3 → ℝ := ![x0 * N + slT N, 0, 0] with ha
  set tt : Fin 3 → ℝ := ![t, lu, (C.lam : ℝ)] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 3)), 0 ≤ tt k := by
    intro k _; fin_cases k
    · simp only [htt]; simp; positivity
    · simpa [htt] using hlu0
    · simp [htt]
  have hmain := cubeM_chernoff_four (fun _ => s) (fun _ => flipAt x s) (fun _ => r0) (fun _ => flipAt x' s)
    (fun _ => (flipAt_ne x s).symm) (fun _ => Ne.symm h1) (fun _ => (flipAt_ne x' s).symm) (fun _ => Ne.symm h2)
    (fun _ => fs_flip_ne hxx s) (fun _ => hd) univ f hfm a tt htt0 Wa (fun _ => Wc) hWam (fun _ => hWcm)
  have hsub : ({w | CellEvX N s r0 x .effect c w} ∩ {w | w s k ∈ srWin ε} : Set (Param N)) ⊆
      {w | (∀ i, w ((fun _ : Fin N => s) i) i ∈ Wa i ∧ w ((fun _ : Fin N => r0) i) i ∈ (fun _ : Fin N => Wc) i) ∧
        ∀ j ∈ (univ : Finset (Fin 3)), ∑ i, f j i ((w ((fun _ : Fin N => s) i) i,
          w ((fun _ : Fin N => flipAt x s) i) i), (w ((fun _ : Fin N => r0) i) i,
            w ((fun _ : Fin N => flipAt x' s) i) i)) ≤ a j} := by
    rintro w ⟨hw1, hw2⟩
    obtain ⟨hW1, hT, hL, hV, hF⟩ := hsubE (hmono hw1)
    refine ⟨fun i => ⟨?_, hF i⟩, fun j _ => ?_⟩
    · simp only [hWa]; split_ifs with h
      · subst h; exact ⟨hW1 i, hw2⟩
      · exact hW1 i
    fin_cases j
    · simpa [hf, ha] using hT
    · simp only [hf, ha]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [sum_sub_distrib]; linarith
    · simpa [hf, ha] using hV
  -- the column factors
  set I1 := fsI C with hI1
  have hI10 := fs_cell_pos C hok
  set H : ℝ := (1 - (1 / 2 : ℝ) ^ (C.lu + 1)) / (C.lu + 1) with hH
  have hH15 : (15 : ℝ) / 64 ≤ H := by
    have key : ∀ n : ℕ, n ≤ 3 → (15 : ℝ) / 64 ≤ (1 - (1 / 2 : ℝ) ^ (n + 1)) / (n + 1) := by
      intro n hn; interval_cases n <;> norm_num
    exact key C.lu hlu
  have hH1 : H ≤ 1 := by
    rw [hH, div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (C.lu + 1) := by positivity
    have : (0 : ℝ) ≤ C.lu := Nat.cast_nonneg _
    linarith
  set E : ℝ := Real.exp (lu * (slT N / N)) * Real.exp ((C.lam : ℝ) * fsK N) with hE
  set J : ℝ := E * (2 * I1) * (H + deltaU N) with hJ
  set Jk : ℝ := E * ((3 / 2 : ℝ) ^ C.lam * (2 * ε)) * (H + deltaU N) with hJk
  have hJ0 : 0 ≤ J := by positivity
  have hJk0 : 0 ≤ Jk := by positivity
  have hcol : ∀ i : Fin N, ∫⁻ y in Wa i, ∫⁻ u, ∫⁻ z in (fun _ : Fin N => Wc) i, ∫⁻ v,
      ENNReal.ofReal (Real.exp (-∑ j ∈ (univ : Finset (Fin 3)), tt j * f j i ((y, u), (z, v))))
        ∂unif ∂unif ∂unif ∂unif ≤ ENNReal.ofReal (if i = k then Jk else J) := by
    intro i
    have hpt : ∀ y u z v, ENNReal.ofReal (Real.exp (-∑ j ∈ (univ : Finset (Fin 3)), tt j * f j i ((y, u), (z, v)))) =
        ENNReal.ofReal (Real.exp (-lu * ellSX N y)) *
          ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXevE N c1 y u)) *
          (ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 z))) * ENNReal.ofReal (Real.exp 0)) := by
      intro y u z v
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 2
      simp [Fin.sum_univ_three, hf, htt]
      ring
    simp_rw [hpt]
    have m1 : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (-lu * ellSX N y)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (fs_ellSX_meas.const_mul _))
    have m2 : Measurable fun z : ℝ => ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 z))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hell.const_mul _))
    have m3 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXevE N c1 p.1 p.2)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((fs_gE_meas c1).const_mul _))
    rw [lint4_split (Wa i) Wc (fun y => ENNReal.ofReal (Real.exp (-lu * ellSX N y)))
      (fun z => ENNReal.ofReal (Real.exp ((lu - t) * -Real.log (clamp01 z))))
      (fun y u => ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXevE N c1 y u)))
      (fun _ _ => ENNReal.ofReal (Real.exp 0)) m1 m2 m3 measurable_const]
    have hone : ∫⁻ _v : ℝ, ENNReal.ofReal (Real.exp 0) ∂unif = 1 := by
      rw [Real.exp_zero, ENNReal.ofReal_one, lintegral_const, unif_univ, mul_one]
    simp_rw [hone, mul_one]
    have hF := tf_floor_factor (N := N) C.lu (t := t) (lu := lu) (by rw [ht]; ring) hδ
    have hS : ∫⁻ y in Wa i, ENNReal.ofReal (Real.exp (-lu * ellSX N y)) *
        ∫⁻ u, ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXevE N c1 y u)) ∂unif ∂unif ≤
        ENNReal.ofReal (if i = k then E * ((3 / 2 : ℝ) ^ C.lam * (2 * ε)) else E * (2 * I1)) := by
      by_cases hik : i = k
      · rw [if_pos hik]
        have hWk : Wa i = Wx ∩ srWin ε := by simp only [hWa, if_pos hik]
        rw [hWk]
        calc ∫⁻ y in Wx ∩ srWin ε, ENNReal.ofReal (Real.exp (-lu * ellSX N y)) *
              ∫⁻ u, ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXevE N c1 y u)) ∂unif ∂unif
            ≤ ∫⁻ _y in Wx ∩ srWin ε, ENNReal.ofReal (E * (3 / 2 : ℝ) ^ C.lam) ∂unif := by
              refine lintegral_mono fun y => ?_
              obtain ⟨hX1, hX2⟩ := fs_X_bounds y
              have hX0 : 0 < max (clamp01 y) (1 - clamp01 y) := by linarith
              have e : Real.exp (-lu * ellSX N y) =
                  Real.exp (lu * (slT N / N)) * (max (clamp01 y) (1 - clamp01 y)) ^ lu := by
                unfold ellSX; rw [Real.rpow_def_of_pos hX0, ← Real.exp_add]; congr 1; ring
              have hpw := Real.rpow_le_one hX0.le hX2 hlu0
              have hin := fs_inner_le_H (N := N) C.lam c1 y
              calc ENNReal.ofReal (Real.exp (-lu * ellSX N y)) *
                    ∫⁻ u, ENNReal.ofReal (Real.exp (-(C.lam : ℝ) * gXevE N c1 y u)) ∂unif
                  ≤ ENNReal.ofReal (Real.exp (lu * (slT N / N))) *
                      ENNReal.ofReal ((3 / 2 : ℝ) ^ C.lam * Real.exp (C.lam * fsK N)) := by
                    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) hin
                    rw [e]; have := Real.exp_pos (lu * (slT N / N)); nlinarith
                _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), hE]; congr 1; ring
          _ = ENNReal.ofReal (E * (3 / 2 : ℝ) ^ C.lam) * unif (Wx ∩ srWin ε) := by rw [setLIntegral_const]
          _ ≤ ENNReal.ofReal (E * (3 / 2 : ℝ) ^ C.lam) * ENNReal.ofReal (2 * ε) := by
              gcongr; exact unif_srWin_le hε Set.inter_subset_right
          _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
      · rw [if_neg hik]
        have hWk : Wa i = Wx := by simp only [hWa, if_neg hik]
        rw [hWk]
        have hb0 : (0 : ℝ) < (C.v : ℝ) ^ 4 := by positivity
        have hb1 : (C.v : ℝ) ^ 4 ≤ 1 := pow_le_one₀ hv.le hv1.le
        have := s_factor_le (N := N) C.lam c1 hcm1 hlu0 hb0 (by simpa [hc1] using hb) hb1
        have e2 : (∫ X in (C.v : ℝ) ^ 4..1, X ^ lu * gX C.lam (c1.2 : ℝ) X) = I1 := by
          rw [hc12]; simp only [hI1, fsI, hludef]
        rw [e2] at this
        refine this.trans (le_of_eq ?_)
        congr 1
    calc _ ≤ ENNReal.ofReal (if i = k then E * ((3 / 2 : ℝ) ^ C.lam * (2 * ε)) else E * (2 * I1)) *
          ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ (C.lu + 1)) / (C.lu + 1) + deltaU N) := mul_le_mul' hS hF
      _ = ENNReal.ofReal (if i = k then Jk else J) := by
          rw [← ENNReal.ofReal_mul (by split_ifs <;> positivity)]
          split_ifs <;> rfl
  refine (measure_mono hsub).trans (hmain.trans ?_)
  have hsum : ∑ j ∈ (univ : Finset (Fin 3)), tt j * a j = t * (x0 * N + slT N) := by
    simp [Fin.sum_univ_three, htt, ha]
  rw [hsum]
  calc ENNReal.ofReal (Real.exp (t * (x0 * N + slT N))) * ∏ i : Fin N, ∫⁻ y in Wa i,
        ∫⁻ u, ∫⁻ z in (fun _ : Fin N => Wc) i, ∫⁻ v,
          ENNReal.ofReal (Real.exp (-∑ j ∈ (univ : Finset (Fin 3)), tt j * f j i ((y, u), (z, v))))
            ∂unif ∂unif ∂unif ∂unif
      ≤ ENNReal.ofReal (Real.exp (t * (x0 * N + slT N))) *
          ∏ i : Fin N, ENNReal.ofReal (if i = k then Jk else J) := by
        gcongr with i; exact hcol i
    _ = ENNReal.ofReal (Real.exp (t * (x0 * N + slT N)) * (Jk * J ^ (N - 1))) := by
        rw [show (fun i : Fin N => ENNReal.ofReal (if i = k then Jk else J)) =
          fun i => if i = k then ENNReal.ofReal Jk else ENNReal.ofReal J from
            funext fun i => by split_ifs <;> rfl, prod_ite_one, ← ENNReal.ofReal_pow hJ0,
          ← ENNReal.ofReal_mul hJk0, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        -- the per-unit rate: e^{t x0} I1 rsEx ≤ e^{-R0}/2
        have hsound := rsCell_sound C hok
        have hEx2 : (rsEx C.lu : ℝ) = 2 * H := by rw [rsEx_cast, hH]; ring
        have hEx0 : (0 : ℝ) < rsEx C.lu := by rw [hEx2]; linarith
        have hs' : Real.log 2 + Real.log I1 + Real.log (rsEx C.lu : ℝ) + ((C.P : ℝ) / 4 + C.lu) * x0 ≤
            -(rsR0 : ℝ) := hsound
        have hunit : Real.exp (t * x0) * (2 * I1 * H) ≤ Real.exp (-(rsR0 : ℝ)) / 2 := by
          have hl : Real.exp (t * x0) * (2 * I1 * H) * 2 =
              Real.exp (Real.log 2 + Real.log I1 + Real.log (rsEx C.lu : ℝ) + t * x0) := by
            rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), Real.exp_log hI10,
              Real.exp_log hEx0, hEx2]; ring
          rw [le_div_iff₀ (by norm_num), hl]
          apply Real.exp_le_exp.2
          rw [ht, hludef]; linarith
        -- J = E (1 + δ/H) · (2 I1 H)
        have hHpos : 0 < H := by linarith
        have hJe : J = E * (1 + deltaU N / H) * (2 * I1 * H) := by rw [hJ]; field_simp
        have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN0
        have hδN : deltaU N * N ≤ 1 := by
          unfold deltaU; rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
        have hslT : 0 ≤ slT N := by
          unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
          linarith
        have hslV : 0 ≤ slV N := by unfold slV; positivity
        have hKN := fsK_mul_le (N := N) (by omega)
        have hKN0 := fsK_mul_nonneg (N := N)
        have hlamR : (C.lam : ℝ) ≤ 17 := by exact_mod_cast hlam
        have hluR : lu ≤ 15 / 2 := by
          have : (C.P : ℝ) ≤ 30 := by exact_mod_cast hP
          rw [hludef]; linarith
        have hpR : (C.lu : ℝ) ≤ 3 := by exact_mod_cast hlu
        have htR : t ≤ 21 / 2 := by rw [ht]; linarith
        have hx0 := x0_lt
        -- E^N and (1 + δ/H)^N
        have hEN : E ^ N = Real.exp (lu * slT N) * Real.exp ((C.lam : ℝ) * (fsK N * N)) := by
          rw [hE, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
          congr 1 <;> congr 1
          · field_simp
          · ring
        have hcorr : (1 + deltaU N / H) ^ N ≤ Real.exp 5 := by
          calc (1 + deltaU N / H) ^ N ≤ Real.exp (deltaU N / H) ^ N := by
                gcongr; linarith [Real.add_one_le_exp (deltaU N / H)]
            _ = Real.exp (deltaU N * N / H) := by rw [← Real.exp_nat_mul]; congr 1; ring
            _ ≤ Real.exp 5 := Real.exp_le_exp.2 (by rw [div_le_iff₀ hHpos]; nlinarith)
        -- assemble: e^{tB} J^{N-1} Jk ≤ ...
        have hJk : Jk = E * (1 + deltaU N / H) * ((3 / 2 : ℝ) ^ C.lam * (2 * ε) * H) := by
          rw [hJk]; field_simp
        have hE0 : 0 < E := by positivity
        have hc0 : 0 ≤ 1 + deltaU N / H := by positivity
        have hpowN1 : (Real.exp (t * x0) * J) ^ (N - 1) ≤ (E * (1 + deltaU N / H)) ^ (N - 1) *
            (Real.exp (-(rsR0 : ℝ)) / 2) ^ (N - 1) := by
          rw [← mul_pow]
          apply pow_le_pow_left₀ (by positivity)
          rw [hJe]
          calc Real.exp (t * x0) * (E * (1 + deltaU N / H) * (2 * I1 * H))
              = E * (1 + deltaU N / H) * (Real.exp (t * x0) * (2 * I1 * H)) := by ring
            _ ≤ E * (1 + deltaU N / H) * (Real.exp (-(rsR0 : ℝ)) / 2) :=
                mul_le_mul_of_nonneg_left hunit (by positivity)
        have hsplit : Real.exp (t * (x0 * N + slT N)) * (Jk * J ^ (N - 1)) =
            Real.exp (t * slT N) * (Real.exp (t * x0) * J) ^ (N - 1) * (Real.exp (t * x0) * Jk) := by
          have : Real.exp (t * (x0 * N)) = Real.exp (t * x0) ^ (N - 1) * Real.exp (t * x0) := by
            rw [← pow_succ, ← Real.exp_nat_mul]; congr 1; rw [Nat.sub_add_cancel (by omega)]; ring
          rw [mul_add, Real.exp_add, this]; ring
        rw [hsplit]
        -- the bound for `(E (1+δ/H))^{N-1} · E (1+δ/H)` and the constants
        have hEc : (E * (1 + deltaU N / H)) ^ (N - 1) * (E * (1 + deltaU N / H)) ≤
            Real.exp (lu * slT N) * Real.exp ((C.lam : ℝ) * (fsK N * N)) * Real.exp 5 := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega), mul_pow, hEN]
          exact mul_le_mul_of_nonneg_left hcorr (by positivity)
        have hR2 : (Real.exp (-(rsR0 : ℝ)) / 2) ^ (N - 1) = Real.exp (-((rsR0 : ℝ) * N)) / 2 ^ N *
            (2 * Real.exp (rsR0 : ℝ)) := by
          have h2 : (2 : ℝ) ^ N = 2 ^ (N - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
          have he : Real.exp (-((rsR0 : ℝ) * N)) = Real.exp (-(rsR0 : ℝ)) ^ (N - 1) * Real.exp (-(rsR0 : ℝ)) := by
            rw [← pow_succ, Nat.sub_add_cancel (by omega), ← Real.exp_nat_mul]; ring_nf
          have hx : Real.exp (-(rsR0 : ℝ)) * Real.exp (rsR0 : ℝ) = 1 := by rw [← Real.exp_add]; simp
          calc (Real.exp (-(rsR0 : ℝ)) / 2) ^ (N - 1)
              = Real.exp (-(rsR0 : ℝ)) ^ (N - 1) / 2 ^ (N - 1) * (Real.exp (-(rsR0 : ℝ)) * Real.exp (rsR0 : ℝ)) := by
                rw [hx, mul_one, div_pow]
            _ = (Real.exp (-(rsR0 : ℝ)) ^ (N - 1) * Real.exp (-(rsR0 : ℝ))) / (2 ^ (N - 1) * 2) *
                (2 * Real.exp (rsR0 : ℝ)) := by field_simp
            _ = _ := by rw [← he, ← h2]
        have hlog32 : Real.log (3 / 2) ≤ 2 * x0 := by rw [log_three_halves_eq]
        have h32 : (3 / 2 : ℝ) ^ C.lam ≤ Real.exp 7 := by
          rw [← Real.exp_log (show (0 : ℝ) < (3 / 2) ^ C.lam by positivity), Real.log_pow]
          apply Real.exp_le_exp.2; nlinarith
        have hex : Real.exp (t * x0) ≤ Real.exp 3 := Real.exp_le_exp.2 (by nlinarith [x0_pos])
        have h2R : 2 * Real.exp (rsR0 : ℝ) ≤ Real.exp 2 := by
          have hl2 := Real.log_two_lt_d9
          have e : 2 * Real.exp (rsR0 : ℝ) = Real.exp (Real.log 2 + rsR0) := by
            rw [Real.exp_add, Real.exp_log (by norm_num)]
          rw [e]; apply Real.exp_le_exp.2; unfold rsR0; push_cast; norm_num at hl2; linarith
        have hconst : Real.exp (t * x0) * ((3 / 2 : ℝ) ^ C.lam * (2 * ε) * H) * (2 * Real.exp (rsR0 : ℝ)) ≤
            Real.exp 12 * (2 * ε) := by
          have e12 : Real.exp 12 = Real.exp 3 * Real.exp 7 * Real.exp 2 := by
            rw [← Real.exp_add, ← Real.exp_add]; norm_num
          rw [e12]
          have hH0 : 0 ≤ H := by linarith
          calc Real.exp (t * x0) * ((3 / 2 : ℝ) ^ C.lam * (2 * ε) * H) * (2 * Real.exp (rsR0 : ℝ))
              = Real.exp (t * x0) * (3 / 2 : ℝ) ^ C.lam * (2 * Real.exp (rsR0 : ℝ)) * H * (2 * ε) := by ring
            _ ≤ Real.exp 3 * Real.exp 7 * Real.exp 2 * 1 * (2 * ε) := by gcongr
            _ = _ := by ring
        have hJkx : Real.exp (t * x0) * Jk =
            (E * (1 + deltaU N / H)) * (Real.exp (t * x0) * ((3 / 2 : ℝ) ^ C.lam * (2 * ε) * H)) := by
          rw [hJk]; ring
        rw [hJkx]
        have hP1 : 0 ≤ (E * (1 + deltaU N / H)) ^ (N - 1) := by positivity
        have hexpo : Real.exp (t * slT N) * (Real.exp (lu * slT N) * Real.exp ((C.lam : ℝ) * (fsK N * N)) *
            Real.exp 5) * Real.exp 12 ≤ Real.exp (19 * slT N + 17 * (8 + slV N) + 20) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.2
          have a1 := mul_le_mul_of_nonneg_right htR hslT
          have a2 := mul_le_mul_of_nonneg_right hluR hslT
          have a3 := mul_le_mul hlamR hKN hKN0 (by norm_num : (0 : ℝ) ≤ 17)
          linarith
        calc Real.exp (t * slT N) * (Real.exp (t * x0) * J) ^ (N - 1) *
              ((E * (1 + deltaU N / H)) * (Real.exp (t * x0) * ((3 / 2 : ℝ) ^ C.lam * (2 * ε) * H)))
            ≤ Real.exp (t * slT N) * ((E * (1 + deltaU N / H)) ^ (N - 1) * (Real.exp (-(rsR0 : ℝ)) / 2) ^ (N - 1)) *
              ((E * (1 + deltaU N / H)) * (Real.exp (t * x0) * ((3 / 2 : ℝ) ^ C.lam * (2 * ε) * H))) := by
              gcongr
          _ = Real.exp (t * slT N) * ((E * (1 + deltaU N / H)) ^ (N - 1) * (E * (1 + deltaU N / H))) *
              (Real.exp (-((rsR0 : ℝ) * N)) / 2 ^ N) *
              (Real.exp (t * x0) * ((3 / 2 : ℝ) ^ C.lam * (2 * ε) * H) * (2 * Real.exp (rsR0 : ℝ))) := by
              rw [hR2]; ring
          _ ≤ Real.exp (t * slT N) * (Real.exp (lu * slT N) * Real.exp ((C.lam : ℝ) * (fsK N * N)) * Real.exp 5) *
              (Real.exp (-((rsR0 : ℝ) * N)) / 2 ^ N) * (Real.exp 12 * (2 * ε)) := by
              gcongr
          _ = (Real.exp (t * slT N) * (Real.exp (lu * slT N) * Real.exp ((C.lam : ℝ) * (fsK N * N)) *
              Real.exp 5) * Real.exp 12) * (Real.exp (-((rsR0 : ℝ) * N)) / 2 ^ N) * (2 * ε) := by ring
          _ ≤ Real.exp (19 * slT N + 17 * (8 + slV N) + 20) * (Real.exp (-((rsR0 : ℝ) * N)) / 2 ^ N) * (5 * ε) :=
              mul_le_mul (mul_le_mul_of_nonneg_right hexpo (by positivity)) (by linarith) (by positivity)
                (by positivity)
          _ = _ := by ring

lemma sigN_eq (N : ℕ) : sigN N = Real.exp (-(x0 * N)) := by
  unfold sigN
  rw [show ((2 / 3 : ℝ)) ^ N = Real.exp (-(x0 * N)) ^ 2 by
    rw [← Real.exp_nat_mul, ← Real.exp_log (show (0 : ℝ) < 2 / 3 by norm_num), ← Real.exp_nat_mul]
    congr 1
    have : Real.log (2 / 3) = -(2 * x0) := by
      rw [← log_three_halves_eq, ← Real.log_inv]; norm_num
    rw [this]; push_cast; ring]
  exact Real.sqrt_sq (Real.exp_pos _).le

/-- **`joint_sRowMu`, PROVED** (one entry of row `s` in a window of width `e^{N/100} σ_N`). -/
theorem joint_sRowMuF : JointBound P0SRowMu := by
  have hab := poly_absorb (61 * 5 * Real.exp 11) 1 (δ := (rsR0 : ℝ) + x0 - 1 / 100 - RJ)
    (by have := x0_gt; unfold RJ rsR0; push_cast; linarith)
  filter_upwards [hab, eventually_ge_atTop 15] with N hab hN s r0 x σ hfar
  have hN2 : 2 ≤ N := by omega
  have hδ : deltaU N < 1 / 2 := by
    unfold deltaU; rw [div_lt_iff₀ (by positivity)]; have : (15 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set ε := Real.exp ((N : ℝ) / 100) * sigN N with hε
  have hε0 : 0 ≤ ε := by rw [hε]; unfold sigN; positivity
  obtain ⟨x', hx'⟩ := fs_dummy hN2 x
  set SB := Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (19 * slT N + 17 * (8 + slV N) + 20) / 2 ^ N * (5 * ε) with hSB
  have hSB0 : 0 ≤ SB := by positivity
  have hcell : ∀ k : Fin N, ∀ c ∈ cellsX σ,
      cubeM N ({w | CellEvX N s r0 x σ c w} ∩ {w | w s k ∈ srWin ε}) ≤ ENNReal.ofReal SB := by
    intro k c hc
    have h0 := tf_far_ne2 (by omega) hfar
    cases σ with
    | cause =>
      refine (sr_cause_cell hN2 s r0 x x' hx' k (List.mem_toFinset.1 hc) h0 (tf_far_ne1 (by omega) hfar x)
        (tf_far_ne1 (by omega) hfar x') hε0).trans (ENNReal.ofReal_le_ofReal ?_)
      have hslT : 0 ≤ slT N := by
        unfold slT; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
        linarith
      have : Real.exp (14 * slT N + 17 * (8 + slV N)) ≤ Real.exp (19 * slT N + 17 * (8 + slV N) + 20) :=
        Real.exp_le_exp.2 (by linarith)
      rw [hSB]; gcongr
    | effect =>
      exact sr_eff_cell hN2 hδ s r0 x x' hx' k (List.mem_toFinset.1 hc) h0 (tf_far_ne0 (by omega) hfar x)
        (tf_far_ne0 (by omega) hfar x') hε0
  have hsub : {w : Param N | RegEvX N s r0 x σ w ∧ ¬ P0SRowMu N s r0 w x σ} ⊆
      ⋃ k : Fin N, ⋃ c ∈ cellsX σ, ({w | CellEvX N s r0 x σ c w} ∩ {w | w s k ∈ srWin ε}) := by
    rintro w ⟨⟨c, hc, hcw⟩, hn⟩
    simp only [P0SRowMu, not_forall, not_le] at hn
    obtain ⟨h, hlt⟩ := hn
    obtain ⟨k, -, hk⟩ := (Finset.inf'_lt_iff h).1 hlt
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
    refine ⟨k, c, hc, hcw, ?_⟩
    simp only [srWin, Set.mem_setOf_eq]
    have : xE w s k = max (clamp01 (w s k)) (1 - clamp01 (w s k)) := rfl
    rw [hε]; linarith
  refine (measure_mono hsub).trans ?_
  calc cubeM N (⋃ k : Fin N, ⋃ c ∈ cellsX σ, ({w | CellEvX N s r0 x σ c w} ∩ {w | w s k ∈ srWin ε}))
      ≤ ∑ k : Fin N, ∑ c ∈ cellsX σ, cubeM N ({w | CellEvX N s r0 x σ c w} ∩ {w | w s k ∈ srWin ε}) :=
        (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun k _ => measure_biUnion_finset_le _ _)
    _ ≤ ∑ _k : Fin N, ∑ _c ∈ cellsX σ, ENNReal.ofReal SB := sum_le_sum fun k _ => sum_le_sum fun c hc => hcell k c hc
    _ ≤ ∑ _k : Fin N, (61 : ENNReal) * ENNReal.ofReal SB := by
        refine sum_le_sum fun k _ => ?_
        rw [sum_const, nsmul_eq_mul]; gcongr; exact_mod_cast tf_cells_card σ
    _ = ENNReal.ofReal (N * (61 * SB)) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (p := (N : ℝ)) (q := 61 * SB) (Nat.cast_nonneg _),
          ENNReal.ofReal_mul (p := 61) (q := SB) (by norm_num), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hsl := rs_slack_le N
        have h2N : (0 : ℝ) < 2 ^ N := by positivity
        have hεe : ε = Real.exp (-((x0 - 1 / 100) * N)) := by
          rw [hε, sigN_eq, ← Real.exp_add]; congr 1; ring
        have e1 : (N : ℝ) * (61 * SB) = (61 * 5 * Real.exp 11 * N * Real.exp (19 * slT N + 17 * (8 + slV N) + 9)) *
            (Real.exp (-((((rsR0 : ℝ) + x0 - 1 / 100 - RJ)) * N)) * Real.exp (-(RJ * N))) / 2 ^ N := by
          rw [hSB, hεe]
          have : Real.exp (19 * slT N + 17 * (8 + slV N) + 20) =
              Real.exp 11 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [this]
          have : Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (-((x0 - 1 / 100) * N)) =
              Real.exp (-((((rsR0 : ℝ) + x0 - 1 / 100 - RJ)) * N)) * Real.exp (-(RJ * N)) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          rw [← this]; ring
        rw [e1, div_le_div_iff_of_pos_right h2N]
        have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        have hk : 61 * 5 * Real.exp 11 * N * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) ≤
            Real.exp ((((rsR0 : ℝ) + x0 - 1 / 100 - RJ)) * N) := by
          refine le_trans ?_ hab
          simp only [pow_one]
          have : (N : ℝ) ≤ N + 1 := by linarith
          calc 61 * 5 * Real.exp 11 * N * Real.exp (19 * slT N + 17 * (8 + slV N) + 9)
              ≤ 61 * 5 * Real.exp 11 * ((N : ℝ) + 1) * Real.exp (4000 + 1400 * Real.log N) := by gcongr
            _ = _ := by ring
        have hy : Real.exp ((((rsR0 : ℝ) + x0 - 1 / 100 - RJ)) * N) *
            Real.exp (-((((rsR0 : ℝ) + x0 - 1 / 100 - RJ)) * N)) = 1 := by rw [← Real.exp_add]; simp
        calc (61 * 5 * Real.exp 11 * N * Real.exp (19 * slT N + 17 * (8 + slV N) + 9)) *
              (Real.exp (-((((rsR0 : ℝ) + x0 - 1 / 100 - RJ)) * N)) * Real.exp (-(RJ * N)))
            ≤ Real.exp ((((rsR0 : ℝ) + x0 - 1 / 100 - RJ)) * N) *
              (Real.exp (-((((rsR0 : ℝ) + x0 - 1 / 100 - RJ)) * N)) * Real.exp (-(RJ * N))) := by gcongr
          _ = Real.exp (-(RJ * N)) := by rw [← mul_assoc, hy, one_mul]

end Census
end IIT

#print axioms IIT.Census.joint_sRowMuF
