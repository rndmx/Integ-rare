import Mathlib

/-!
# Erlang lower bound for the volume of a product super-level set

`volume {v ∈ [0,1]^N | e^{-x} ≤ ∏ v i} ≥ e^{-x} x^N / N!`, proved by induction on `N`,
splitting off the first coordinate (Tonelli) and evaluating the resulting one-dimensional
integral by the fundamental theorem of calculus.
-/

open MeasureTheory Set

namespace IIT.Census

private lemma erlang_measS (N : ℕ) (c : ℝ) :
    MeasurableSet {v : Fin N → ℝ | (∀ i, v i ∈ Icc (0:ℝ) 1) ∧ c ≤ ∏ i, v i} := by
  have h1 : MeasurableSet {v : Fin N → ℝ | ∀ i, v i ∈ Icc (0:ℝ) 1} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun i => measurable_pi_apply i measurableSet_Icc
  have h2 : MeasurableSet {v : Fin N → ℝ | c ≤ ∏ i, v i} :=
    measurableSet_le measurable_const (Finset.measurable_prod _ fun i _ => measurable_pi_apply i)
  exact h1.inter h2

private lemma erlang_cont (N : ℕ) (c : ℝ) (hc : 0 < c) :
    ContinuousOn (fun u : ℝ => c / u * (Real.log u - Real.log c) ^ N / N.factorial)
      (Icc c 1) := by
  have hne : ∀ u ∈ Icc c 1, u ≠ 0 := fun u hu => (hc.trans_le hu.1).ne'
  exact ((continuousOn_const.div continuousOn_id hne).mul
    (((Real.continuousOn_log.mono fun u hu => hne u hu).sub continuousOn_const).pow N)).div_const _

private lemma erlang_integral (N : ℕ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∫ u in c..1, c / u * (Real.log u - Real.log c) ^ N / N.factorial =
      c * (-Real.log c) ^ (N + 1) / (N + 1).factorial := by
  have hderiv : ∀ u ∈ uIcc c 1,
      HasDerivAt (fun u => c * (Real.log u - Real.log c) ^ (N + 1) / (N + 1).factorial)
        (c / u * (Real.log u - Real.log c) ^ N / N.factorial) u := by
    intro u hu
    rw [uIcc_of_le hc1] at hu
    have hu0 : u ≠ 0 := (hc.trans_le hu.1).ne'
    have := ((((Real.hasDerivAt_log hu0).sub_const (Real.log c)).pow (N + 1)).const_mul c).div_const
      ((N + 1).factorial : ℝ)
    have h2 : c / u * (Real.log u - Real.log c) ^ N / N.factorial =
        c * (((N + 1 : ℕ) : ℝ) * (Real.log u - Real.log c) ^ (N + 1 - 1) * u⁻¹) /
          ((N + 1).factorial : ℝ) := by
      rw [Nat.add_sub_cancel, Nat.factorial_succ]; push_cast
      have : (N.factorial : ℝ) ≠ 0 := by positivity
      field_simp
    rw [h2]; exact this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((erlang_cont N c hc).mono (by rw [uIcc_of_le hc1])).intervalIntegrable]
  simp

private lemma erlang_aux (N : ℕ) : ∀ c : ℝ, 0 < c → c ≤ 1 →
    ENNReal.ofReal (c * (-Real.log c) ^ N / N.factorial) ≤
      volume {v : Fin N → ℝ | (∀ i, v i ∈ Icc (0:ℝ) 1) ∧ c ≤ ∏ i, v i} := by
  induction N with
  | zero =>
    intro c hc hc1
    have : {v : Fin 0 → ℝ | (∀ i, v i ∈ Icc (0:ℝ) 1) ∧ c ≤ ∏ i, v i} = univ := by
      ext v; simp [hc1]
    rw [this, volume_pi, Measure.pi_univ]
    simp [hc1]
  | succ N ih =>
    intro c hc hc1
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) 0
    set S := {v : Fin (N + 1) → ℝ | (∀ i, v i ∈ Icc (0:ℝ) 1) ∧ c ≤ ∏ i, v i} with hS
    have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) 0).symm
    rw [← hmp.measure_preimage_equiv S]
    have hT : MeasurableSet (e.symm ⁻¹' S) := e.symm.measurable (erlang_measS (N + 1) c)
    rw [Measure.volume_eq_prod, Measure.prod_apply hT]
    set f := fun u : ℝ => c / u * (Real.log u - Real.log c) ^ N / N.factorial
    calc ENNReal.ofReal (c * (-Real.log c) ^ (N + 1) / (N + 1).factorial)
        = ENNReal.ofReal (∫ u in c..1, f u) := by rw [erlang_integral N c hc hc1]
      _ = ∫⁻ u in Ioc c 1, ENNReal.ofReal (f u) := by
          rw [intervalIntegral.integral_of_le hc1, ofReal_integral_eq_lintegral_ofReal]
          · exact ((erlang_cont N c hc).integrableOn_Icc).mono_set Ioc_subset_Icc_self
          · refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun u hu => ?_)
            have hu0 : 0 < u := hc.trans hu.1
            have : 0 ≤ Real.log u - Real.log c :=
              sub_nonneg.2 (Real.log_le_log hc hu.1.le)
            positivity
      _ ≤ ∫⁻ u in Ioc c 1, volume (Prod.mk u ⁻¹' (e.symm ⁻¹' S)) :=
          setLIntegral_mono' measurableSet_Ioc fun u hu => ?_
      _ ≤ ∫⁻ u, volume (Prod.mk u ⁻¹' (e.symm ⁻¹' S)) := setLIntegral_le_lintegral _ _
    have hu0 : 0 < u := hc.trans hu.1
    have hslice : Prod.mk u ⁻¹' (e.symm ⁻¹' S) =
        {v : Fin N → ℝ | (∀ i, v i ∈ Icc (0:ℝ) 1) ∧ c / u ≤ ∏ i, v i} := by
      ext w
      simp [e, hS, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.forall_fin_succ, Fin.prod_univ_succ, div_le_iff₀ hu0]
      rw [mul_comm u]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨⟨hu0.le, hu.2⟩, h.1⟩, h.2⟩⟩
    rw [hslice]
    have hf : f u = c / u * (-Real.log (c / u)) ^ N / N.factorial := by
      simp only [f, Real.log_div hc.ne' hu0.ne', neg_sub]
    rw [hf]
    exact ih (c / u) (div_pos hc hu0) ((div_le_one hu0).2 hu.1.le)

theorem erlang_lower_thm (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal (Real.exp (-x) * x ^ N / N.factorial) ≤
      MeasureTheory.volume {v : Fin N → ℝ | (∀ i, v i ∈ Set.Icc (0:ℝ) 1) ∧
        Real.exp (-x) ≤ ∏ i, v i} := by
  have h := erlang_aux N (Real.exp (-x)) (Real.exp_pos _)
    (Real.exp_le_one_iff.2 (by linarith))
  rwa [Real.log_exp, neg_neg] at h

end IIT.Census
