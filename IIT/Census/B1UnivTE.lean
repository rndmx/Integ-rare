/-
Census, B1 lower bound, leaf `phi_univ_ge_EX` (W7 §3 item 5): the maximal effect state of `univ`.

Copy of `B1UnivSys.te_key` / `sysMaxEffStates_univ_eq_of` with the bound `R(te) ≤ 3` instead of `≤ 2`
(only used through `e + R(te) ≤ 4`), so that the two fixed rows `r0, r0^x` (each contributing `≤ 1`)
fit next to the generic mass `≤ 3/2`.
-/
import IIT.Census.B1UnivSys

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

section TE3

variable (T : UnitTPM N) (s : State N)

/-- The real inequality behind Lemma TE. -/
lemma te_key3 {e et Rte Rt μ ν : ℝ} (he0 : 0 < e) (het0 : 0 < et) (he1 : e ≤ 1)
    (hetle : et ≤ e * (1 - 2 * μ)) (hlog : -((N : ℝ) / 2) ≤ Real.logb 2 e) (hRt : 1 / 2 ≤ Rt)
    (hRte0 : 0 ≤ Rte) (hRte : Rte ≤ 3) (hRR : Rte ≤ Rt + ν) (hμ : 0 < μ) (hν : 0 ≤ ν)
    (hμν : 3 * ν < μ * ((N : ℝ) - 10)) :
    et * Real.logb 2 ((2 : ℝ) ^ N * et / (et + Rt)) <
      e * Real.logb 2 ((2 : ℝ) ^ N * e / (e + Rte)) := by
  have hb : 0 < et + Rt := by linarith
  have ha : 0 < e + Rte := by linarith
  rw [te_logb_split het0 hb, te_logb_split he0 ha]
  set A := Real.logb 2 e
  set B := Real.logb 2 et
  set C := Real.logb 2 (e + Rte)
  set D := Real.logb 2 (et + Rt)
  have hete : et ≤ e := by nlinarith
  have hAB : B ≤ A := Real.logb_le_logb_of_le one_lt_two het0 hete
  have hC : C ≤ 2 := by
    have h4 : Real.logb 2 (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one one_lt_two]
      norm_num
    rw [← h4]
    exact Real.logb_le_logb_of_le one_lt_two ha (by linarith)
  set u := e - et + ν with hu
  have hu0 : 0 ≤ u := by linarith
  have hCD : C - D ≤ 3 * u := by
    have hl2 : (2 : ℝ) / 3 < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hlogq : Real.log ((e + Rte) / (et + Rt)) ≤ 2 * u := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
      have h2 : (e + Rte) / (et + Rt) - 1 ≤ 2 * u := by
        rw [div_sub_one hb.ne', div_le_iff₀ hb]
        nlinarith
      linarith
    have hCD' : C - D = Real.log ((e + Rte) / (et + Rt)) / Real.log 2 := by
      simp only [C, D, Real.logb]
      rw [Real.log_div ha.ne' hb.ne']
      ring
    rw [hCD', div_le_iff₀ (by linarith)]
    nlinarith
  have hN10 : (10 : ℝ) < N := by
    by_contra h
    push Not at h
    nlinarith
  have key : e * (N + A - C) - et * (N + B - D) =
      (e - et) * (N + A - C) + et * (A - B) - et * (C - D) := by ring
  have h1 : (e - et) * ((N : ℝ) / 2 - 2) ≤ (e - et) * (N + A - C) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : 0 ≤ et * (A - B) := mul_nonneg het0.le (by linarith)
  have h3 : et * (C - D) ≤ et * (3 * u) := mul_le_mul_of_nonneg_left hCD het0.le
  have h4 : et * (3 * u) ≤ 3 * (e - et) + 3 * e * ν := by
    have : et * (e - et) ≤ e - et := by nlinarith
    have : et * ν ≤ e * ν := mul_le_mul_of_nonneg_right hete hν
    rw [hu]; nlinarith
  have h5 : 2 * μ * e * ((N : ℝ) / 2 - 5) ≤ (e - et) * ((N : ℝ) / 2 - 5) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h6 : 0 < e * (μ * ((N : ℝ) - 10) - 3 * ν) := mul_pos he0 (by linarith)
  nlinarith

/-- **Lemma TE.** Under the W5 hypotheses (i)-(iv) (with `ν ≤ 1` not needed), the maximal effect
state of `univ` is the pattern `te` of the more likely bits. -/
theorem sysMaxEffStates_univ_eq_of3 (hpos : ∀ i r b, 0 < T.prob i r b) (te : State N) {μ ν : ℝ}
    (hμ : 0 < μ) (hx : ∀ k, 1 / 2 + μ ≤ T.prob k s (te k))
    (he : (2 : ℝ) ^ (-((N : ℝ) / 2)) ≤ fullProb T s te)
    (hRt : ∀ t, 1 / 2 ≤ effRest T s t) (hRte : effRest T s te ≤ 3)
    (hRR : ∀ t, effRest T s te ≤ effRest T s t + ν) (hν : 0 ≤ ν)
    (hμν : 3 * ν < μ * ((N : ℝ) - 10)) :
    sysMaxEffStates T univ s s = {te} := by
  have hfe : 0 < fullProb T s te := prod_pos fun i _ => hpos i s (te i)
  have hlt : ∀ t, t ≠ te → sysIiE T univ s s t < sysIiE T univ s s te := by
    intro t ht
    rw [sysIiE_univ_eq T s hpos, sysIiE_univ_eq T s hpos]
    refine te_key3 (prod_pos fun i _ => hpos i s (te i)) (prod_pos fun i _ => hpos i s (t i))
      (prod_le_one (fun i _ => T.nonneg i s _) fun i _ => T.le_one i s _)
      (te_fullProb_le T s te hμ.le hx ht) ?_ (hRt t)
      (sum_nonneg fun r _ => prod_nonneg fun i _ => T.nonneg i r _) hRte (hRR t) hμ hν hμν
    have := Real.logb_le_logb_of_le one_lt_two (by positivity) he
    rwa [Real.logb_rpow two_pos (by norm_num)] at this
  ext t
  rw [mem_singleton]
  unfold sysMaxEffStates
  rw [mem_argmaxSet]
  constructor
  · intro h
    by_contra hne
    exact absurd (h te) (not_le.2 (hlt t hne))
  · rintro rfl t'
    by_cases h : t' = t
    · rw [h]
    · exact (hlt t' h).le

end TE3

end Census
end IIT
