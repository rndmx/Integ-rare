/-
Census, B1 forced leaf: the nuS sub-leaf `NuSxStmt` (effect side, subcube `K' = {x}` through `s`).

Since `clamp01 (w s i) ≤ 1`, `log max(y_s + y_{s^x}, 1) ≤ log(1 + y_{s^x})`, so the failure event lies in
`RegEvX effect ∩ {Σ_i log(1 + y_{s^x,i}) ≥ 0.46 N}`.  Row `s^x` is the competitor row of the effect template, so
the extra constraint enters the Chernoff bound as a weight `(1 + u)` in the competitor integral.  The `s`-factor
is symmetric under `y ↦ 1 - y`, which maps the competitor `u` to `1 - u`; averaging the two orientations the
weight becomes `((1 + u) + (2 - u))/2 = 3/2`, a constant (`s_weight_le`).  Each certified effect cell bound is
therefore multiplied by exactly `e^{-0.46 N} (3/2)^N ≤ e^{-N/32}`, with no new numerics:
rate `≥ rsR0 + 1/32 = 1.0384 > 1.0109`.
-/
import IIT.Census.CertRSXESound
import IIT.Census.B1ForcedFJoint
import IIT.Census.BigPhiBridge

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-! ### 1. The effect template with the competitor weight -/

theorem joint_template_eff_floor_nu (ra rb rc : Fin N → State N)
    (hab : ∀ i, ra i ≠ rb i) (hac : ∀ i, ra i ≠ rc i) (hbc : ∀ i, rb i ≠ rc i)
    (ellT ellS : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (hellT : Measurable ellT) (hellS : Measurable ellS)
    (hg : Measurable fun p : ℝ × ℝ => g p.1 p.2) (W : Set ℝ) (hW : MeasurableSet W)
    (B t lamU lam : ℝ) (ht : 0 ≤ t) (hlamU : 0 ≤ lamU) (hlam : 0 ≤ lam) (a : ℝ) (mu : ℝ) (hmu : 0 ≤ mu)
    (L : ℝ) :
    cubeM N {w | (∀ i, w (ra i) i ∈ W) ∧ ∑ i, ellT (w (rc i) i) ≤ B ∧
        ∑ i, ellS (w (ra i) i) ≤ ∑ i, ellT (w (rc i) i) ∧ ∑ i, g (w (ra i) i) (w (rb i) i) ≤ 0 ∧
        (∀ i, a ≤ w (rc i) i) ∧ L ≤ ∑ i, Real.log (1 + clamp01 (w (rb i) i))} ≤
      ENNReal.ofReal (Real.exp (t * B - L)) *
        ((∫⁻ x in W, ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
            ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g x u + Real.log (1 + clamp01 u))) ∂unif ∂unif) *
          ∫⁻ y, ENNReal.ofReal (Real.exp ((lamU - t) * ellT y - mu * Set.indicator (Set.Iio a) 1 y))
            ∂unif) ^ N := by
  have hlog1 : Measurable fun u : ℝ => Real.log (1 + clamp01 u) :=
    Real.measurable_log.comp (measurable_const.add clamp01_measurable)
  set f : Fin 5 → Fin N → ℝ × ℝ × ℝ → ℝ :=
    ![fun _ p => ellT p.2.2, fun _ p => ellS p.1 - ellT p.2.2, fun _ p => g p.1 p.2.1,
      fun _ p => Set.indicator (Set.Iio a) 1 p.2.2, fun _ p => -Real.log (1 + clamp01 p.2.1)] with hf
  have hfm : ∀ k i, Measurable (f k i) := by
    intro k i
    fin_cases k
    · exact hellT.comp (measurable_snd.comp measurable_snd)
    · exact (hellS.comp measurable_fst).sub (hellT.comp (measurable_snd.comp measurable_snd))
    · exact hg.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    · exact (measurable_one.indicator measurableSet_Iio).comp (measurable_snd.comp measurable_snd)
    · exact (hlog1.comp (measurable_fst.comp measurable_snd)).neg
  set aa : Fin 5 → ℝ := ![B, 0, 0, 0, -L] with ha
  set tt : Fin 5 → ℝ := ![t, lamU, lam, mu, 1] with htt
  have htt0 : ∀ k ∈ (univ : Finset (Fin 5)), 0 ≤ tt k := by
    intro k _; fin_cases k <;> simp [htt, ht, hlamU, hlam, hmu]
  have hmain := cubeM_chernoff_three ra rb rc hab hac hbc univ f hfm aa tt htt0 (fun _ => W)
    (fun _ => hW)
  refine (measure_mono ?_).trans (hmain.trans_eq ?_)
  · rintro w ⟨hW', hB, hU, hG, hF, hL⟩
    refine ⟨hW', fun k _ => ?_⟩
    fin_cases k
    · simpa [hf, ha] using hB
    · simp only [hf, ha, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [Finset.sum_sub_distrib]; linarith
    · simpa [hf, ha] using hG
    · simp only [hf, ha]
      refine le_of_eq (Finset.sum_eq_zero fun i _ => ?_)
      simp [Set.indicator_of_notMem (show w (rc i) i ∉ Set.Iio a from not_lt.2 (hF i))]
    · show ∑ i, -Real.log (1 + clamp01 (w (rb i) i)) ≤ -L
      rw [Finset.sum_neg_distrib]; linarith
  · have hsum : ∑ k ∈ (univ : Finset (Fin 5)), tt k * aa k = t * B - L := by
      simp [htt, ha, Fin.sum_univ_five]; ring
    rw [hsum]
    congr 1
    have hexp : ∀ i x u y, ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 5)),
        tt k * f k i (x, u, y))) = ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
          ENNReal.ofReal (Real.exp (-lam * g x u + Real.log (1 + clamp01 u))) *
            ENNReal.ofReal (Real.exp ((lamU - t) * ellT y - mu * Set.indicator (Set.Iio a) 1 y)) := by
      intro i x u y
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
        ← Real.exp_add, ← Real.exp_add]
      congr 2
      simp only [Fin.sum_univ_five, hf, htt, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
        Matrix.head_cons]
      ring
    have hA : Measurable fun x => ENNReal.ofReal (Real.exp (-lamU * ellS x)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hellS.const_mul _))
    have hBm : Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal (Real.exp (-lam * g p.1 p.2 + Real.log (1 + clamp01 p.2))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hg.const_mul _).add
        (hlog1.comp measurable_snd)))
    have hC : Measurable fun y => ENNReal.ofReal (Real.exp ((lamU - t) * ellT y -
        mu * Set.indicator (Set.Iio a) 1 y)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hellT.const_mul _).sub
        ((measurable_one.indicator measurableSet_Iio).const_mul _)))
    have hIB : Measurable fun x =>
        ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g x u + Real.log (1 + clamp01 u))) ∂unif :=
      hBm.lintegral_prod_right'
    have hfac : ∀ i : Fin N, ∫⁻ x in W, ∫⁻ u, ∫⁻ y, ENNReal.ofReal (Real.exp
        (-∑ k ∈ (univ : Finset (Fin 5)), tt k * f k i (x, u, y))) ∂unif ∂unif ∂unif =
        (∫⁻ x in W, ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
            ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g x u + Real.log (1 + clamp01 u))) ∂unif ∂unif) *
          ∫⁻ y, ENNReal.ofReal (Real.exp ((lamU - t) * ellT y - mu * Set.indicator (Set.Iio a) 1 y))
            ∂unif := by
      intro i
      have hAB : Measurable fun x => ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * g x u + Real.log (1 + clamp01 u))) ∂unif := hA.mul hIB
      simp_rw [hexp i]
      rw [← lintegral_mul_const _ hAB]
      refine lintegral_congr fun x => ?_
      have hBx : Measurable fun u =>
          ENNReal.ofReal (Real.exp (-lam * g x u + Real.log (1 + clamp01 u))) :=
        hBm.comp (measurable_const.prodMk measurable_id)
      have hABx : Measurable fun u => ENNReal.ofReal (Real.exp (-lamU * ellS x)) *
          ENNReal.ofReal (Real.exp (-lam * g x u + Real.log (1 + clamp01 u))) := hBx.const_mul _
      simp_rw [lintegral_const_mul _ hC]
      rw [lintegral_mul_const _ hABx, lintegral_const_mul _ hBx]
    rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]

/-! ### 2. The weight averages to `3/2` -/

lemma nsx_xmax_one_sub (y : ℝ) :
    max (clamp01 (1 - y)) (1 - clamp01 (1 - y)) = max (clamp01 y) (1 - clamp01 y) := by
  rw [clamp01_one_sub, sub_sub_cancel, max_comm]

lemma nsx_ellSX_one_sub (y : ℝ) : ellSX N (1 - y) = ellSX N y := by
  unfold ellSX; rw [nsx_xmax_one_sub]

/-- Reflecting the row-`s` entry flips the orientation of the competitor (off `y = 1/2`). -/
lemma gXevE_one_sub (c : ℚ × ℚ) {y : ℝ} (hy : y ≠ 1 / 2) (u : ℝ) :
    gXevE N c (1 - y) u = gXevE N c y (1 - u) := by
  have hcy : clamp01 y ≠ 1 / 2 := by
    intro h
    apply hy
    unfold clamp01 at h
    rcases le_total y 0 with h0 | h0
    · rw [min_eq_right (by linarith : y ≤ 1), max_eq_left h0] at h; norm_num at h
    · rcases le_total y 1 with h1 | h1
      · rw [min_eq_right h1, max_eq_right h0] at h; exact h
      · rw [min_eq_left h1, max_eq_right zero_le_one] at h; norm_num at h
  unfold gXevE
  rw [nsx_xmax_one_sub, clamp01_one_sub, clamp01_one_sub]
  congr 3
  rcases lt_or_gt_of_ne hcy with h | h
  · rw [if_pos (by linarith), if_neg (by linarith)]; ring
  · rw [if_neg (by linarith), if_pos h]

/-- The row-`s` window. -/
def nsxW (c : ℚ × ℚ) : Set ℝ := {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)}
/-- The row-`s` link weight. -/
noncomputable def nsxA (N : ℕ) (lamU y : ℝ) : ENNReal := ENNReal.ofReal (Real.exp (-lamU * ellSX N y))
/-- The competitor kernel. -/
noncomputable def nsxE (N : ℕ) (c : ℚ × ℚ) (lam y u : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.exp (-lam * gXevE N c y u))
/-- Unweighted and `u`-weighted competitor integrals. -/
noncomputable def nsxPhi (N : ℕ) (c : ℚ × ℚ) (lam y : ℝ) : ENNReal := ∫⁻ u, nsxE N c lam y u ∂unif
noncomputable def nsxPsi (N : ℕ) (c : ℚ × ℚ) (lam y : ℝ) : ENNReal :=
  ∫⁻ u, nsxE N c lam y u * ENNReal.ofReal (clamp01 u) ∂unif

lemma nsx_measurable_xmax : Measurable fun y : ℝ => max (clamp01 y) (1 - clamp01 y) :=
  clamp01_measurable.max (measurable_const.sub clamp01_measurable)

lemma measurableSet_nsxW (c : ℚ × ℚ) : MeasurableSet (nsxW c) :=
  measurableSet_le measurable_const nsx_measurable_xmax

lemma nsx_measurable_gXevE (c : ℚ × ℚ) : Measurable fun p : ℝ × ℝ => gXevE N c p.1 p.2 := by
  unfold gXevE
  have hy : Measurable fun p : ℝ × ℝ => clamp01 p.1 := clamp01_measurable.comp measurable_fst
  have hu : Measurable fun p : ℝ × ℝ => clamp01 p.2 := clamp01_measurable.comp measurable_snd
  have hX : Measurable fun p : ℝ × ℝ => max (clamp01 p.1) (1 - clamp01 p.1) :=
    hy.max (measurable_const.sub hy)
  have hU : Measurable fun p : ℝ × ℝ => if 1 / 2 < clamp01 p.1 then clamp01 p.2 else 1 - clamp01 p.2 :=
    Measurable.ite (measurableSet_lt measurable_const hy) hu (measurable_const.sub hu)
  refine (Measurable.min ?_ ?_).sub_const _
  · exact Real.measurable_log.comp ((measurable_const.mul hX).div (hX.add hU))
  · exact (measurable_const.max (Real.measurable_log.comp (hX.div_const _))).sub_const _

lemma measurable_nsxA (lamU : ℝ) : Measurable (nsxA N lamU) := by
  have hellS : Measurable (ellSX N) := by
    unfold ellSX
    exact ((Real.measurable_log.comp nsx_measurable_xmax).neg).sub_const _
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hellS.const_mul _))

lemma measurable_nsxE (c : ℚ × ℚ) (lam : ℝ) : Measurable fun p : ℝ × ℝ => nsxE N c lam p.1 p.2 :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((nsx_measurable_gXevE c).const_mul _))

lemma measurable_nsxE_right (c : ℚ × ℚ) (lam y : ℝ) : Measurable fun u => nsxE N c lam y u :=
  Measurable.of_uncurry_left (f := nsxE N c lam) (measurable_nsxE c lam)

lemma measurable_nsxPsi (c : ℚ × ℚ) (lam : ℝ) : Measurable (nsxPsi N c lam) :=
  ((measurable_nsxE c lam).mul (ENNReal.measurable_ofReal.comp
    (clamp01_measurable.comp measurable_snd))).lintegral_prod_right'

lemma measurable_nsxPhi (c : ℚ × ℚ) (lam : ℝ) : Measurable (nsxPhi N c lam) :=
  (measurable_nsxE c lam).lintegral_prod_right'

/-- The weighted inner integral is `Phi + Psi`. -/
lemma nsx_inner (c : ℚ × ℚ) (lam y : ℝ) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * gXevE N c y u + Real.log (1 + clamp01 u))) ∂unif =
      nsxPhi N c lam y + nsxPsi N c lam y := by
  have hpt : ∀ u, ENNReal.ofReal (Real.exp (-lam * gXevE N c y u + Real.log (1 + clamp01 u))) =
      nsxE N c lam y u + nsxE N c lam y u * ENNReal.ofReal (clamp01 u) := by
    intro u
    have h1 : 0 < 1 + clamp01 u := by linarith [clamp01_nonneg u]
    unfold nsxE
    rw [Real.exp_add, Real.exp_log h1, mul_add, mul_one, ENNReal.ofReal_add (Real.exp_pos _).le
      (mul_nonneg (Real.exp_pos _).le (clamp01_nonneg u)), ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [hpt]
  exact lintegral_add_left (measurable_nsxE_right c lam y) _

/-- Reflection of the competitor: `Psi y + Psi (1 - y) = Phi y` off `y = 1/2`. -/
lemma nsx_refl (c : ℚ × ℚ) (lam : ℝ) {y : ℝ} (hy : y ≠ 1 / 2) :
    nsxPsi N c lam y + nsxPsi N c lam (1 - y) = nsxPhi N c lam y := by
  have hEy := measurable_nsxE_right (N := N) c lam y
  have hf : Measurable fun u => nsxE N c lam y u * ENNReal.ofReal (clamp01 (1 - u)) :=
    hEy.mul (ENNReal.measurable_ofReal.comp (clamp01_measurable.comp (measurable_const.sub measurable_id)))
  have h1 : nsxPsi N c lam (1 - y) = ∫⁻ u, nsxE N c lam y u * ENNReal.ofReal (1 - clamp01 u) ∂unif := by
    have e : ∀ u, nsxE N c lam (1 - y) u * ENNReal.ofReal (clamp01 u) =
        (fun u => nsxE N c lam y u * ENNReal.ofReal (clamp01 (1 - u))) (1 - u) := by
      intro u; simp only [nsxE, gXevE_one_sub c hy, sub_sub_cancel]
    unfold nsxPsi
    simp_rw [e]
    rw [lintegral_unif_reflect _ hf]
    simp only [clamp01_one_sub]
  rw [h1]
  unfold nsxPsi nsxPhi
  rw [← lintegral_add_left (f := fun u => nsxE N c lam y u * ENNReal.ofReal (clamp01 u))
    (hEy.mul (ENNReal.measurable_ofReal.comp clamp01_measurable))]
  refine lintegral_congr fun u => ?_
  rw [← mul_add, ← ENNReal.ofReal_add (clamp01_nonneg u) (by linarith [clamp01_le_one u])]
  simp

/-- Reflection of the row-`s` entry. -/
lemma nsx_reflW (c : ℚ × ℚ) (lam lamU : ℝ) :
    ∫⁻ y in nsxW c, nsxA N lamU y * nsxPsi N c lam (1 - y) ∂unif =
      ∫⁻ y in nsxW c, nsxA N lamU y * nsxPsi N c lam y ∂unif := by
  have hsymW : ∀ y, y ∈ nsxW c ↔ 1 - y ∈ nsxW c := by
    intro y; simp only [nsxW, Set.mem_setOf_eq, nsx_xmax_one_sub]
  have hKm : Measurable ((nsxW c).indicator fun z => nsxA N lamU z * nsxPsi N c lam z) :=
    ((measurable_nsxA lamU).mul (measurable_nsxPsi c lam)).indicator (measurableSet_nsxW c)
  have hpt : ∀ y, (nsxW c).indicator (fun z => nsxA N lamU z * nsxPsi N c lam (1 - z)) y =
      (nsxW c).indicator (fun z => nsxA N lamU z * nsxPsi N c lam z) (1 - y) := by
    intro y
    by_cases h : y ∈ nsxW c
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hsymW y).1 h)]
      simp only [nsxA, nsx_ellSX_one_sub]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hsymW y).2 h'))]
  rw [← lintegral_indicator (measurableSet_nsxW c), ← lintegral_indicator (measurableSet_nsxW c)]
  simp_rw [hpt]
  exact lintegral_unif_reflect _ hKm

lemma nsx_key (c : ℚ × ℚ) (lam lamU : ℝ) :
    (∫⁻ y in nsxW c, nsxA N lamU y * nsxPsi N c lam y ∂unif) +
        (∫⁻ y in nsxW c, nsxA N lamU y * nsxPsi N c lam y ∂unif) =
      ∫⁻ y in nsxW c, nsxA N lamU y * nsxPhi N c lam y ∂unif := by
  have hae : ∀ᵐ y ∂(unif.restrict (nsxW c)), y ≠ 1 / 2 := by
    refine ae_restrict_of_ae ?_
    unfold unif
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    simp
  conv_lhs => arg 2; rw [← nsx_reflW c lam lamU]
  rw [← lintegral_add_left (f := fun y => nsxA N lamU y * nsxPsi N c lam y)
    ((measurable_nsxA lamU).mul (measurable_nsxPsi c lam))]
  refine lintegral_congr_ae (hae.mono fun y hy => ?_)
  simp only []
  rw [← mul_add, nsx_refl c lam hy]

/-- **The weighted row-`s` factor is `3/2` times the unweighted one.** -/
theorem s_weight_le (c : ℚ × ℚ) (lam lamU : ℝ) :
    ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)},
        ENNReal.ofReal (Real.exp (-lamU * ellSX N y)) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * gXevE N c y u + Real.log (1 + clamp01 u))) ∂unif ∂unif ≤
      ENNReal.ofReal (3 / 2) *
        ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)},
          ENNReal.ofReal (Real.exp (-lamU * ellSX N y)) *
            ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * gXevE N c y u)) ∂unif ∂unif := by
  change ∫⁻ y in nsxW c, nsxA N lamU y * ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * gXevE N c y u +
      Real.log (1 + clamp01 u))) ∂unif ∂unif ≤
    ENNReal.ofReal (3 / 2) * ∫⁻ y in nsxW c, nsxA N lamU y * nsxPhi N c lam y ∂unif
  simp_rw [nsx_inner c lam, mul_add]
  rw [lintegral_add_left (f := fun y => nsxA N lamU y * nsxPhi N c lam y)
    ((measurable_nsxA lamU).mul (measurable_nsxPhi c lam)), ← nsx_key c lam lamU]
  generalize (∫⁻ y in nsxW c, nsxA N lamU y * nsxPsi N c lam y ∂unif) = a
  have h32 : ENNReal.ofReal (3 / 2) * 2 = 3 := by
    rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  calc a + a + a = 3 * a := by ring
    _ = ENNReal.ofReal (3 / 2) * (a + a) := by rw [← two_mul, ← mul_assoc, h32]
    _ ≤ _ := le_rfl

/-! ### 3. One effect cell with the competitor constraint -/

/-- **One effect cell intersected with `Σ log(1 + y_{s^x}) ≥ L`.** -/
theorem cellEvX_eff_prob_nu (hN : 0 < N) (s r0 : State N) (x : Fin N) (c : ℚ × ℚ) (hcm : (1 : ℝ) / 2 ≤ c.2)
    (hδ : deltaU N < 1 / 2) (hsr : s ≠ r0) (hfr : flipAt x s ≠ r0) (t lamU lam mu : ℝ) (ht : 0 ≤ t)
    (hlamU : 0 ≤ lamU) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) {Js Jt : ℝ} (hJs0 : 0 ≤ Js) (hJt0 : 0 ≤ Jt)
    (hJs : ∫⁻ y in {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)},
        ENNReal.ofReal (Real.exp (-lamU * ellSX N y)) *
          ∫⁻ u, ENNReal.ofReal (Real.exp (-lam * gXevE N c y u)) ∂unif ∂unif ≤ ENNReal.ofReal Js)
    (hJt : ∫⁻ y, ENNReal.ofReal (Real.exp ((lamU - t) * -Real.log (clamp01 y) -
        mu * Set.indicator (Set.Iio (1 / 2 - deltaU N)) 1 y)) ∂unif ≤ ENNReal.ofReal Jt) (L : ℝ) :
    cubeM N {w : Param N | CellEvX N s r0 x .effect c w ∧
        L ≤ ∑ i, Real.log (1 + clamp01 (w (flipAt x s) i))} ≤
      ENNReal.ofReal (Real.exp (-L) * (3 / 2) ^ N) *
        ENNReal.ofReal (Real.exp (t * (x0 * N + slT N)) * (Js * Jt) ^ N) := by
  have hellT : Measurable fun y : ℝ => -Real.log (clamp01 y) :=
    (Real.measurable_log.comp clamp01_measurable).neg
  have hellS : Measurable (ellSX N) := by
    unfold ellSX
    exact ((Real.measurable_log.comp (clamp01_measurable.max
      (measurable_const.sub clamp01_measurable))).neg).sub_const _
  have hg : Measurable fun p : ℝ × ℝ => gXevE N c p.1 p.2 := by
    unfold gXevE
    have hy : Measurable fun p : ℝ × ℝ => clamp01 p.1 := clamp01_measurable.comp measurable_fst
    have hu : Measurable fun p : ℝ × ℝ => clamp01 p.2 := clamp01_measurable.comp measurable_snd
    have hX : Measurable fun p : ℝ × ℝ => max (clamp01 p.1) (1 - clamp01 p.1) :=
      hy.max (measurable_const.sub hy)
    have hU : Measurable fun p : ℝ × ℝ => if 1 / 2 < clamp01 p.1 then clamp01 p.2 else 1 - clamp01 p.2 :=
      Measurable.ite (measurableSet_lt measurable_const hy) hu (measurable_const.sub hu)
    refine (Measurable.min ?_ ?_).sub_const _
    · exact Real.measurable_log.comp ((measurable_const.mul hX).div (hX.add hU))
    · exact (measurable_const.max (Real.measurable_log.comp (hX.div_const _))).sub_const _
  have hW : MeasurableSet {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)} :=
    measurableSet_le measurable_const (clamp01_measurable.max (measurable_const.sub clamp01_measurable))
  have hsub : {w : Param N | CellEvX N s r0 x .effect c w ∧
      L ≤ ∑ i, Real.log (1 + clamp01 (w (flipAt x s) i))} ⊆
      {w | (∀ i, w ((fun _ : Fin N => s) i) i ∈ {y : ℝ | (c.1 : ℝ) ≤ max (clamp01 y) (1 - clamp01 y)}) ∧
        ∑ i, (fun y => -Real.log (clamp01 y)) (w ((fun _ : Fin N => r0) i) i) ≤ x0 * N + slT N ∧
        ∑ i, ellSX N (w ((fun _ : Fin N => s) i) i) ≤
          ∑ i, (fun y => -Real.log (clamp01 y)) (w ((fun _ : Fin N => r0) i) i) ∧
        ∑ i, gXevE N c (w ((fun _ : Fin N => s) i) i) (w ((fun _ : Fin N => flipAt x s) i) i) ≤ 0 ∧
        (∀ i, 1 / 2 - deltaU N ≤ w ((fun _ : Fin N => r0) i) i) ∧
        L ≤ ∑ i, Real.log (1 + clamp01 (w ((fun _ : Fin N => flipAt x s) i) i))} := by
    rintro w ⟨hc, hL⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := cellEvX_eff_sub_template hN s r0 x c hcm hδ hc
    exact ⟨h1, h2, h3, h4, h5, hL⟩
  refine (measure_mono hsub).trans ?_
  refine (joint_template_eff_floor_nu (fun _ => s) (fun _ => flipAt x s) (fun _ => r0)
    (fun _ => (flipAt_ne x s).symm) (fun _ => hsr) (fun _ => hfr)
    (fun y => -Real.log (clamp01 y)) (ellSX N) (gXevE N c) hellT hellS hg _ hW
    (x0 * N + slT N) t lamU lam ht hlamU hlam (1 / 2 - deltaU N) mu hmu L).trans ?_
  have hJs' := (s_weight_le (N := N) c lam lamU).trans (mul_le_mul_of_nonneg_left hJs zero_le)
  rw [← ENNReal.ofReal_mul (by norm_num)] at hJs'
  have hrw : Real.exp (-L) * (3 / 2) ^ N * (Real.exp (t * (x0 * N + slT N)) * (Js * Jt) ^ N) =
      Real.exp (t * (x0 * N + slT N) - L) * (3 / 2 * Js * Jt) ^ N := by
    rw [sub_eq_add_neg, Real.exp_add, mul_pow, mul_pow, mul_pow]; ring
  have hk0 : (0 : ℝ) ≤ Real.exp (-L) * (3 / 2) ^ N := by positivity
  have hJ0 : (0 : ℝ) ≤ 3 / 2 * Js := by positivity
  rw [← ENNReal.ofReal_mul hk0, hrw, ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_pow (mul_nonneg hJ0 hJt0), ENNReal.ofReal_mul hJ0]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zero_le (mul_le_mul' hJs' hJt) N) zero_le

/-! ### 4. The certified effect cells with the competitor constraint -/

/-- **One original effect cell with `Σ log(1 + y_{s^x}) ≥ L`**: the certified cell bound times
`e^{-L} (3/2)^N`. -/
theorem effectCell_prob_nu (hN : 0 < N) (s r0 : State N) (x : Fin N) {c : ℚ × ℚ}
    (hc : c ∈ cellsXEffectData) (hδ : deltaU N < 1 / 2) (hsr : s ≠ r0) (hfr : flipAt x s ≠ r0) (L : ℝ) :
    cubeM N {w : Param N | CellEvX N s r0 x .effect c w ∧
        L ≤ ∑ i, Real.log (1 + clamp01 (w (flipAt x s) i))} ≤
      ENNReal.ofReal (Real.exp (-L) * (3 / 2) ^ N) *
        ENNReal.ofReal (Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N) := by
  have hall := rsLinkE_all
  rw [List.all_eq_true] at hall
  obtain ⟨C, hC, hlink⟩ := List.any_eq_true.1 (hall c hc)
  have hok : rsCellOK C = true := (List.all_eq_true.1 rsCellsE_ok) C hC
  have hb := (List.all_eq_true.1 rsBoundsE) C hC
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨hlam, hlu⟩, hP⟩ := hb
  simp only [rsLinkE, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hlink
  obtain ⟨⟨hv4, hcap⟩, hc2⟩ := hlink
  have hok' := hok
  simp only [rsCellOK, Bool.and_eq_true, decide_eq_true_eq] at hok'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hvw⟩, hw1⟩, hv1⟩, hw2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok'
  set c' : ℚ × ℚ := (c.1, C.w ^ 4) with hc'
  have hc2R : (1 : ℝ) / 2 ≤ c.2 := by
    have := (Rat.cast_le (K := ℝ)).2 hc2; push_cast at this ⊢; exact this
  have hw4 : (1 : ℝ) / 2 ≤ (C.w : ℝ) ^ 4 := by
    have := (Rat.cast_le (K := ℝ)).2 hw2; push_cast at this ⊢; exact this
  have hmono := cellEvX_mono_eff s r0 x (c := c) (c' := c') (by simp only [hc'])
    (by
      simp only [hc']
      rcases hcap with h | h
      · left; exact_mod_cast h
      · right; rw [h]; norm_num)
    (by linarith) (by simp only [hc']; push_cast; linarith)
  have hmono' : {w : Param N | CellEvX N s r0 x .effect c w ∧
      L ≤ ∑ i, Real.log (1 + clamp01 (w (flipAt x s) i))} ⊆
      {w | CellEvX N s r0 x .effect c' w ∧ L ≤ ∑ i, Real.log (1 + clamp01 (w (flipAt x s) i))} :=
    fun w hw => ⟨hmono hw.1, hw.2⟩
  refine (measure_mono hmono').trans ?_
  have hδ0 : 0 < deltaU N := by unfold deltaU; positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcm' : (1 : ℝ) / 2 ≤ (c'.2 : ℝ) := by simp only [hc']; push_cast; exact hw4
  set lu : ℝ := (C.P : ℝ) / 4 with hludef
  set t : ℝ := lu + C.lu with htdef
  set K : ℝ := 7 * deltaU N + (slV N + Real.log 2) / N with hK
  set I := ∫ y in ((C.v : ℝ) ^ 4)..1, y ^ ((C.P : ℝ) / 4) * gX C.lam ((C.w : ℝ) ^ 4) y with hIdef
  set H : ℝ := (1 - (1 / 2 : ℝ) ^ (C.lu + 1)) / (C.lu + 1) with hH
  have hv' : (0 : ℝ) < C.v := by exact_mod_cast hv
  have hv0 : (0 : ℝ) < (C.v : ℝ) ^ 4 := by positivity
  have hb : (C.v : ℝ) ^ 4 ≤ max (1 / 2) (c'.1 : ℝ) := by
    simp only [hc']; have := (Rat.cast_le (K := ℝ)).2 hv4; push_cast at this; exact this
  have hb1 : (C.v : ℝ) ^ 4 ≤ 1 := pow_le_one₀ hv'.le (by exact_mod_cast hv1.le)
  have hIpos : 0 < I := cellI_pos C hv hvw hv1 hw2
  have hH15 : (15 : ℝ) / 64 ≤ H := by
    have key : ∀ n : ℕ, n ≤ 3 → (15 : ℝ) / 64 ≤ (1 - (1 / 2 : ℝ) ^ (n + 1)) / (n + 1) := by
      intro n hn; interval_cases n <;> norm_num
    exact key C.lu hlu
  have hH0 : 0 < H := lt_of_lt_of_le (by norm_num) hH15
  have hlu0 : 0 ≤ lu := by positivity
  have hJs := s_factor_le (N := N) C.lam c' hcm' hlu0 hv0 hb hb1
  have hI' : (∫ X in ((C.v : ℝ) ^ 4)..1, X ^ lu * gX C.lam (c'.2 : ℝ) X) = I := by
    simp only [hc', hludef]; push_cast; rfl
  rw [hI'] at hJs
  have hJt := tcJ_le (N := N) C.lu (t := t) (lu := lu) (by simp only [htdef]; ring) hδ
  set C1 : ℝ := Real.exp (lu * (slT N / N)) * Real.exp ((C.lam : ℝ) * K) with hC1
  have hlog1 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  refine (cellEvX_eff_prob_nu hN s r0 x c' hcm' hδ hsr hfr t lu C.lam (Real.log (N + 1))
    (by positivity) hlu0 (Nat.cast_nonneg _) hlog1 (Js := C1 * (2 * I)) (Jt := H + 2 * deltaU N)
    (by positivity) (by positivity) hJs hJt L).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  -- the rate
  have hEx : (rsEx C.lu : ℝ) = 2 * H := by unfold rsEx; push_cast; simp only [hH]; ring
  have hsound := rsCell_sound C hok
  have hEx0 : (0 : ℝ) < rsEx C.lu := by rw [hEx]; positivity
  have hrate := rate_of_log_le hIpos hEx0 hsound N
  have hfac : C1 * (2 * I) * (H + 2 * deltaU N) = C1 * (I * (rsEx C.lu : ℝ)) * (1 + 2 * deltaU N / H) := by
    rw [hEx]; field_simp
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have e1 : C1 ^ N = Real.exp (lu * slT N + (C.lam : ℝ) * (K * N)) := by
    simp only [hC1]
    rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; field_simp
  have hsplitB : Real.exp (t * (x0 * N + slT N)) * (C1 * (2 * I) * (H + 2 * deltaU N)) ^ N =
      ((2 : ℝ) ^ N * (Real.exp (t * (x0 * N)) * (I * (rsEx C.lu : ℝ)) ^ N)) *
        (Real.exp (t * slT N + (lu * slT N + (C.lam : ℝ) * (K * N))) * (1 + 2 * deltaU N / H) ^ N) / 2 ^ N := by
    rw [hfac, mul_pow, mul_pow, e1, mul_add t, Real.exp_add, Real.exp_add]
    field_simp
    rw [Real.exp_add, Real.exp_add]
    ring
  rw [hsplitB]
  -- the correction factor `(1 + 2δ/H)^N ≤ e^9`
  have hδN : deltaU N * N ≤ 1 := by
    unfold deltaU; rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  have hcorr : (1 + 2 * deltaU N / H) ^ N ≤ Real.exp 9 := by
    calc (1 + 2 * deltaU N / H) ^ N ≤ (Real.exp (2 * deltaU N / H)) ^ N := by
          gcongr
          linarith [Real.add_one_le_exp (2 * deltaU N / H)]
      _ = Real.exp (2 * (deltaU N * N) / H) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ Real.exp 9 := by
          apply Real.exp_le_exp.2
          rw [div_le_iff₀ hH0]; nlinarith
  -- the lower-order exponent
  have hslT : 0 ≤ slT N := by
    unfold slT
    have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    linarith
  have hslV : 0 ≤ slV N := by unfold slV; positivity
  have hKN : K * N ≤ 7 + slV N + 1 := by
    simp only [hK, add_mul, div_mul_cancel₀ _ hNr.ne']
    have := Real.log_two_lt_d9
    nlinarith
  have hKN0 : 0 ≤ K * N := by
    simp only [hK]; unfold deltaU; have := Real.log_pos one_lt_two; positivity
  have hlamR : (C.lam : ℝ) ≤ 17 := by exact_mod_cast hlam
  have hluR : lu ≤ 8 := by
    have : (C.P : ℝ) ≤ 30 := by exact_mod_cast hP
    simp only [hludef]; linarith
  have htR : t ≤ 11 := by
    have : (C.lu : ℝ) ≤ 3 := by exact_mod_cast hlu
    simp only [htdef]; linarith
  have hE : t * slT N + (lu * slT N + (C.lam : ℝ) * (K * N)) ≤ 19 * slT N + 17 * (8 + slV N) := by
    have hl0 : (0 : ℝ) ≤ C.lam := Nat.cast_nonneg _
    have a1 := mul_le_mul_of_nonneg_right htR hslT
    have a2 := mul_le_mul_of_nonneg_right hluR hslT
    have a3 := mul_le_mul hlamR hKN hKN0 (by norm_num : (0 : ℝ) ≤ 17)
    linarith
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff_of_pos_right h2N, Real.exp_add (19 * slT N + 17 * (8 + slV N)) 9]
  refine mul_le_mul hrate (mul_le_mul (Real.exp_le_exp.2 hE) hcorr (by positivity) (Real.exp_pos _).le)
    (by positivity) (Real.exp_pos _).le
/-- **The effect regime event with the competitor constraint**: at most 61 cells. -/
theorem regEvX_effect_prob_nu (hN : 0 < N) (s r0 : State N) (x : Fin N) (hδ : deltaU N < 1 / 2)
    (hsr : s ≠ r0) (hfr : flipAt x s ≠ r0) (L : ℝ) :
    cubeM N {w : Param N | RegEvX N s r0 x .effect w ∧
        L ≤ ∑ i, Real.log (1 + clamp01 (w (flipAt x s) i))} ≤
      ENNReal.ofReal (61 * (Real.exp (-L) * (3 / 2) ^ N *
        (Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N))) := by
  have hk0 : (0 : ℝ) ≤ Real.exp (-L) * (3 / 2) ^ N := by positivity
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = Real.exp (-L) * (3 / 2) ^ N *
      (Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N) := ⟨_, rfl⟩
  rw [← hBdef]
  have hset : {w : Param N | RegEvX N s r0 x .effect w ∧
      L ≤ ∑ i, Real.log (1 + clamp01 (w (flipAt x s) i))} =
      ⋃ c ∈ cellsXEffectData.toFinset, {w : Param N | CellEvX N s r0 x .effect c w ∧
        L ≤ ∑ i, Real.log (1 + clamp01 (w (flipAt x s) i))} := by
    ext w
    simp only [RegEvX, cellsX, Set.mem_setOf_eq, Set.mem_iUnion, List.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨⟨c, hc, h⟩, hL⟩; exact ⟨c, hc, h, hL⟩
    · rintro ⟨c, hc, h, hL⟩; exact ⟨⟨c, hc, h⟩, hL⟩
  rw [hset]
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hcell : ∀ c ∈ cellsXEffectData.toFinset, cubeM N {w : Param N | CellEvX N s r0 x .effect c w ∧
      L ≤ ∑ i, Real.log (1 + clamp01 (w (flipAt x s) i))} ≤ ENNReal.ofReal B := by
    intro c hc
    refine (effectCell_prob_nu hN s r0 x (List.mem_toFinset.1 hc) hδ hsr hfr L).trans (le_of_eq ?_)
    rw [hBdef, ENNReal.ofReal_mul hk0]
  calc ∑ c ∈ cellsXEffectData.toFinset, cubeM N {w : Param N | CellEvX N s r0 x .effect c w ∧
        L ≤ ∑ i, Real.log (1 + clamp01 (w (flipAt x s) i))}
      ≤ ∑ _c ∈ cellsXEffectData.toFinset, ENNReal.ofReal B := Finset.sum_le_sum hcell
    _ = (cellsXEffectData.toFinset.card : ENNReal) * ENNReal.ofReal B := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (61 : ENNReal) * ENNReal.ofReal B := by
        gcongr
        have : cellsXEffectData.toFinset.card ≤ cellsXEffectData.length := List.toFinset_card_le _
        have hlen : cellsXEffectData.length = 61 := by decide
        exact_mod_cast hlen ▸ this
    _ = ENNReal.ofReal (61 * B) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 61)]; norm_num

/-! ### 5. `NuSxStmt` -/

lemma nsx_absorb : ∀ᶠ N : ℕ in atTop, 61 * (Real.exp (-((rsR0 : ℝ) * N)) *
    Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N) * Real.exp (-(N : ℝ) / 32) ≤
      Real.exp (-((10109 / 10000 : ℝ) * N)) / 2 ^ N := by
  set R : ℝ := 10109 / 10000 with hR
  have hab := poly_absorb 61 0 (δ := (rsR0 : ℝ) + 1 / 32 - R) (by rw [hR]; unfold rsR0; norm_num)
  filter_upwards [hab] with N hab
  have hsl := rs_slack_le N
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hexp : Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (-(N : ℝ) / 32) =
      Real.exp (-((((rsR0 : ℝ) + 1 / 32 - R)) * N)) * Real.exp (-(R * N)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have e : 61 * (Real.exp (-((rsR0 : ℝ) * N)) *
      Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N) * Real.exp (-(N : ℝ) / 32) =
      (61 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9)) *
        (Real.exp (-((((rsR0 : ℝ) + 1 / 32 - R)) * N)) * Real.exp (-(R * N))) / 2 ^ N := by
    rw [← hexp]; ring
  rw [e, div_le_div_iff_of_pos_right h2N]
  have hk : 61 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) ≤
      Real.exp ((((rsR0 : ℝ) + 1 / 32 - R)) * N) := by
    refine le_trans ?_ hab
    simp only [pow_zero, mul_one]
    gcongr
  have hy : Real.exp ((((rsR0 : ℝ) + 1 / 32 - R)) * N) *
      Real.exp (-((((rsR0 : ℝ) + 1 / 32 - R)) * N)) = 1 := by rw [← Real.exp_add]; simp
  calc (61 * Real.exp (19 * slT N + 17 * (8 + slV N) + 9)) *
        (Real.exp (-((((rsR0 : ℝ) + 1 / 32 - R)) * N)) * Real.exp (-(R * N)))
      ≤ Real.exp ((((rsR0 : ℝ) + 1 / 32 - R)) * N) *
          (Real.exp (-((((rsR0 : ℝ) + 1 / 32 - R)) * N)) * Real.exp (-(R * N))) := by gcongr
    _ = Real.exp (-(R * N)) := by rw [← mul_assoc, hy, one_mul]

/-- `e^{-0.46 N} (3/2)^N ≤ e^{-N/32}`. -/
lemma nsx_kappa_le (N : ℕ) : Real.exp (-((23 / 50 : ℝ) * N)) * (3 / 2) ^ N ≤ Real.exp (-(N : ℝ) / 32) := by
  have hr := exp_rate_ge
  calc Real.exp (-((23 / 50 : ℝ) * N)) * (3 / 2) ^ N
      ≤ Real.exp (-((23 / 50 : ℝ) * N)) * Real.exp (23 / 50 - 1 / 32) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by linarith) N) (Real.exp_pos _).le
    _ = Real.exp (-(N : ℝ) / 32) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

/-- **`NuSxStmt`, PROVED.** -/
theorem nuSx_proved : NuSxStmt := by
  filter_upwards [nsx_absorb, eventually_ge_atTop 7] with N hab hN7 s r0 x hfar
  have hN : 0 < N := by omega
  have hδ : deltaU N < 1 / 2 := by
    unfold deltaU; rw [div_lt_iff₀ (by positivity)]; have : (7 : ℝ) ≤ N := by exact_mod_cast hN7
    linarith
  have hh1 := ham_flipAt_le_one x s
  have hsr : s ≠ r0 := by
    intro h; rw [h, ham_self] at hfar; omega
  have hfr : flipAt x s ≠ r0 := by
    intro h; rw [← h] at hfar; omega
  set L : ℝ := (23 / 50 : ℝ) * N with hL
  have hsub : {w : Param N | RegEvX N s r0 x .effect w ∧
      (23 / 50 : ℝ) * N < ∑ i, Real.log (max (clamp01 (w s i) + clamp01 (w (flipAt x s) i)) 1)} ⊆
      {w | RegEvX N s r0 x .effect w ∧ L ≤ ∑ i, Real.log (1 + clamp01 (w (flipAt x s) i))} := by
    rintro w ⟨hreg, hlt⟩
    refine ⟨hreg, le_of_lt (lt_of_lt_of_le hlt (Finset.sum_le_sum fun i _ => ?_))⟩
    have h1 := clamp01_le_one (w s i)
    have h0 := clamp01_nonneg (w (flipAt x s) i)
    exact Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _))
      (max_le (by linarith) (by linarith))
  refine (measure_mono hsub).trans ((regEvX_effect_prob_nu hN s r0 x hδ hsr hfr L).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  refine le_trans ?_ hab
  have hk := nsx_kappa_le N
  set B0 := Real.exp (-((rsR0 : ℝ) * N)) * Real.exp (19 * slT N + 17 * (8 + slV N) + 9) / 2 ^ N
  have hB0 : 0 ≤ B0 := by positivity
  calc 61 * (Real.exp (-L) * (3 / 2) ^ N * B0) = 61 * B0 * (Real.exp (-L) * (3 / 2) ^ N) := by ring
    _ ≤ 61 * B0 * Real.exp (-(N : ℝ) / 32) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa [hL] using hk

end Census
end IIT

#print axioms IIT.Census.nuSx_proved
