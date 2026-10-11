/-
Census, module A7 (B1-BLUEPRINT-v2 §5.2): the whole-substrate system quantities through the
profile.

Lemma V (W3 §2): for `z` in the open cube and every system partition `θ` of `univ`, the two
directional integrated informations are additive over units through the profile:

  `sysPhiC = β · pos (∑ⱼ λᶜⱼ(Cⱼ))`,   `sysPhiE = e · pos (∑ⱼ λᵉⱼ(Cⱼ))`,

with `λᶜⱼ(C) = log₂ (Num w U U t j / Num w U (U \ C) t j)` and
`λᵉⱼ(C) = log₂ (p_j(s → t_j) / effUnit Cᶜ s j t_j)`.  The cause side is `UpperReduce.ur_logb_eq`
specialised to `S = univ`; the effect side uses `merge univ s s = s`.
-/
import IIT.Census.UpperReduce
import IIT.Census.TieBranches
import IIT.Census.UnivDet
import IIT.Census.BigPhiSys

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- Cause-side per-unit term of Lemma V: unit `j` cut from `C`. -/
noncomputable def lamCU (w : Param N) (t : State N) (C : Finset (Fin N)) (j : Fin N) : ℝ :=
  Real.logb 2 (Num w univ univ t j / Num w univ (univ \ C) t j)

/-- Effect-side per-unit term of Lemma V: unit `j` cut from `C`. -/
noncomputable def lamEU (z : Param N) (s t : State N) (C : Finset (Fin N)) (j : Fin N) : ℝ :=
  Real.logb 2 ((tpmOf z).prob j s (t j) / effUnit (tpmOf z) Cᶜ s j (t j))

/-- **Lemma V, cause side.** -/
theorem univ_sysPhiC_eq {z : Param N} (hz : z ∈ openCube N) (s t : State N)
    (θ : SysPartition N univ) :
    sysPhiC (tpmOf z) univ s θ s t =
      sysBackCause (tpmOf z) univ s s t * pos (∑ j, lamCU (flipP s z) t (profile θ j) j) := by
  unfold sysPhiC
  congr 2
  rw [ur_logb_eq s hz t θ, ur_G, Finset.sum_div]
  rfl

/-- **Lemma V, effect side.** -/
theorem univ_sysPhiE_eq {z : Param N} (hz : z ∈ openCube N) (s t : State N)
    (θ : SysPartition N univ) :
    sysPhiE (tpmOf z) univ s θ s t =
      sysEffProb (tpmOf z) univ s s t * pos (∑ j, lamEU z s t (profile θ j) j) := by
  unfold sysPhiE
  congr 2
  rw [sysEffProb, sysPartEffProb, merge_univ, ← prod_div_distrib, Real.logb, Real.log_prod]
  · rw [Finset.sum_div]
    rfl
  · intro j _
    exact (div_pos (prob_pos hz j s (t j)) (effUnit_pos hz _ s j (t j))).ne'

/-- **Lemma V.** `φ_s` of a partition of `univ` at a fixed pair, through the profile. -/
theorem univ_sysPhiAt_eq {z : Param N} (hz : z ∈ openCube N) (s tc te : State N)
    (θ : SysPartition N univ) :
    sysPhiAt (tpmOf z) univ s θ s tc te =
      min (sysBackCause (tpmOf z) univ s s tc * pos (∑ j, lamCU (flipP s z) tc (profile θ j) j))
          (sysEffProb (tpmOf z) univ s s te * pos (∑ j, lamEU z s te (profile θ j) j)) := by
  rw [sysPhiAt, univ_sysPhiC_eq hz, univ_sysPhiE_eq hz]

/-- The normaliser through the profile (re-export at `S = univ`). -/
theorem univ_sysCutCount_eq (θ : SysPartition N univ) :
    sysCutCount θ = ∑ j, (profile θ j).card :=
  sysCutCount_eq_sum_profile θ

/-- An empty cut contributes nothing (cause side). -/
lemma lamCU_empty (w : Param N) (t : State N) (j : Fin N) (hpos : 0 < Num w univ univ t j) :
    lamCU w t ∅ j = 0 := by
  unfold lamCU
  rw [sdiff_empty, div_self hpos.ne', Real.logb_one]

/-- An empty cut contributes nothing (effect side). -/
lemma lamEU_empty {z : Param N} (hz : z ∈ openCube N) (s t : State N) (j : Fin N) :
    lamEU z s t ∅ j = 0 := by
  unfold lamEU
  rw [compl_empty, effUnit_univ_prob, div_self (prob_pos hz j s (t j)).ne', Real.logb_one]

/-- **The maximal cause state of `univ` is the strict maximiser of the row product.** -/
theorem sysMaxCauseStates_univ_eq {z : Param N} (hz : z ∈ openCube N) (s tc : State N)
    (h : ∀ r, r ≠ tc → rowProd z s r < rowProd z s tc) :
    sysMaxCauseStates (tpmOf z) univ s s = {tc} := by
  have key : ∀ t ∈ sysMaxCauseStates (tpmOf z) univ s s, t = tc := by
    intro t ht
    by_contra hne
    exact absurd (rowProd_max_of_mem hz s t ht tc) (not_le.2 (h t hne))
  obtain ⟨m, hm⟩ := sysMaxCauseStates_nonempty (tpmOf z) univ s s
  ext t
  rw [mem_singleton]
  refine ⟨key t, fun ht => ?_⟩
  rw [ht, ← key m hm]
  exact hm

/-- **Competitor bound at a fixed pair.** `φ_s` at `(tc, te)` is at most `|S|` times the value of
the single-unit split at that pair. -/
theorem sysPhiOfState_le_card_mul (T : UnitTPM N) (S : Finset (Fin N)) (u s tc te : State N)
    {j : Fin N} (hj : j ∈ S) (hrest : (S.erase j).Nonempty) :
    sysPhiOfState T S u s tc te ≤ S.card * sysPhiAt T S u (splitAt hj hrest) s tc te := by
  classical
  have hk : 2 ≤ S.card := by
    have h1 := card_erase_of_mem hj
    have h2 : 0 < (S.erase j).card := card_pos.2 hrest
    omega
  set θ₀ := splitAt hj hrest with hθ₀
  set B := sysPhiAt T S u θ₀ s tc te with hBdef
  have hB0 : 0 ≤ B := sysPhiAt_nonneg _ _ _ _ _ _ _
  have hcc₀ : (sysCutCount θ₀ : ℝ) = (S.card : ℝ) - 1 := by
    rw [hθ₀, sysCutCount_splitAt hj hrest, Nat.cast_sub (by omega : 1 ≤ S.card)]
    simp
  have hk1 : (0 : ℝ) < (S.card : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hk
    linarith
  have hnn : (0 : ℝ) ≤ (S.card : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) hB0
  unfold sysPhiOfState sysMipSetAt
  refine sup'OrZero_le hnn fun θ hθ => ?_
  have hmin := (mem_argminSet.1 hθ) θ₀
  have hccθ : (0 : ℝ) < (sysCutCount θ : ℝ) := by exact_mod_cast sysCutCount_pos θ
  rw [normalizedSysPhiAt, normalizedSysPhiAt, hcc₀] at hmin
  rw [div_le_div_iff₀ hccθ hk1] at hmin
  have hccle : (sysCutCount θ : ℝ) ≤ (S.card : ℝ) * ((S.card : ℝ) - 1) := by
    have h := sysCutCount_le' θ
    have h' : ((sysCutCount θ : ℕ) : ℝ) ≤ ((S.card * (S.card - 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ S.card)] at h'
    simpa using h'
  have h2 : sysPhiAt T S u θ s tc te * ((S.card : ℝ) - 1)
      ≤ (S.card * B) * ((S.card : ℝ) - 1) := by
    calc sysPhiAt T S u θ s tc te * ((S.card : ℝ) - 1)
        ≤ B * (sysCutCount θ : ℝ) := hmin
      _ ≤ B * ((S.card : ℝ) * ((S.card : ℝ) - 1)) := by gcongr
      _ = (S.card * B) * ((S.card : ℝ) - 1) := by ring
  exact le_of_mul_le_mul_right h2 hk1

/-- **Step 1 of the forcing chain** (blueprint `sysPhiOfState_univ_le`): at a fixed pair,
`φ_s(univ) ≤ N · minⱼ φ(θⱼ)`. -/
theorem sysPhiOfState_univ_le (T : UnitTPM N) (hN : 2 ≤ N) (u s tc te : State N)
    (hU : (univ : Finset (Fin N)).Nonempty) :
    sysPhiOfState T univ u s tc te ≤ N * univ.inf' hU (fun j =>
      sysPhiAt T univ u (splitAt (mem_univ j) (hrest_of_two_le hN j)) s tc te) := by
  obtain ⟨j, -, hj⟩ := exists_mem_eq_inf' hU (fun j =>
      sysPhiAt T univ u (splitAt (mem_univ j) (hrest_of_two_le hN j)) s tc te)
  rw [hj]
  have h := sysPhiOfState_le_card_mul T univ u s tc te (mem_univ j) (hrest_of_two_le hN j)
  simpa [card_univ, Fintype.card_fin] using h

/-- **Lemma J, algebraic core**: the min of sums dominates the sum of mins. -/
lemma sum_min_le_min_sum {ι : Type*} (J : Finset ι) (f g : ι → ℝ) :
    ∑ j ∈ J, min (f j) (g j) ≤ min (∑ j ∈ J, f j) (∑ j ∈ J, g j) :=
  le_min (sum_le_sum fun _ _ => min_le_left _ _) (sum_le_sum fun _ _ => min_le_right _ _)

/-! ### Lemma TE: the maximal effect state of `univ` (W5 §7.2, W9 §5.2)

The proof is W5's, simplified: `h(e) - h(eₜ) ≥ (e - eₜ)·N/2` follows from `log₂ eₜ ≤ log₂ e` and
`log₂ e ≥ -N/2` directly, so no case split on `eₜ ≥ e/2` and no calculus is needed. -/

section TE

variable (T : UnitTPM N) (s : State N)

/-- `R(t)`: the mass of the unconstrained effect repertoire coming from rows other than `s`. -/
noncomputable def effRest (t : State N) : ℝ :=
  ∑ r ∈ univ.erase s, fullProb T r t

lemma sysUncEff_univ_eq (t : State N) :
    sysUncEff T univ s t = (fullProb T s t + effRest T s t) / 2 ^ N := by
  unfold sysUncEff avgOverStates effRest
  simp only [sysEffProb_univ]
  rw [← add_sum_erase _ _ (mem_univ s)]

lemma te_logb_split {x R : ℝ} (hx : 0 < x) (hxR : 0 < x + R) :
    Real.logb 2 ((2 : ℝ) ^ N * x / (x + R)) = N + Real.logb 2 x - Real.logb 2 (x + R) := by
  rw [Real.logb_div (by positivity) hxR.ne', Real.logb_mul (by positivity) hx.ne', Real.logb_pow,
    Real.logb_self_eq_one one_lt_two]
  ring

lemma sysIiE_univ_eq (hpos : ∀ i r b, 0 < T.prob i r b) (t : State N) :
    sysIiE T univ s s t = fullProb T s t * Real.logb 2 ((2 : ℝ) ^ N * fullProb T s t /
      (fullProb T s t + effRest T s t)) := by
  have hf : 0 < fullProb T s t := prod_pos fun i _ => hpos i s (t i)
  have hR : 0 ≤ effRest T s t :=
    sum_nonneg fun r _ => prod_nonneg fun i _ => (hpos i r (t i)).le
  unfold sysIiE
  rw [sysEffProb_univ, sysUncEff_univ_eq]
  congr 2
  field_simp

/-- The real inequality behind Lemma TE. -/
lemma te_key {e et Rte Rt μ ν : ℝ} (he0 : 0 < e) (het0 : 0 < et) (he1 : e ≤ 1)
    (hetle : et ≤ e * (1 - 2 * μ)) (hlog : -((N : ℝ) / 2) ≤ Real.logb 2 e) (hRt : 1 / 2 ≤ Rt)
    (hRte0 : 0 ≤ Rte) (hRte : Rte ≤ 2) (hRR : Rte ≤ Rt + ν) (hμ : 0 < μ) (hν : 0 ≤ ν)
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

lemma te_prob_other {i : Fin N} {r : State N} {b c : Bool} (h : b ≠ c) :
    T.prob i r b = 1 - T.prob i r c := by
  have := T.normalized i r
  cases b <;> cases c <;> simp_all <;> linarith

/-- Off the maximal pattern, the effect probability drops by the factor `1 - 2μ`. -/
lemma te_fullProb_le (te : State N) {μ : ℝ} (hμ : 0 ≤ μ) (hx : ∀ k, 1 / 2 + μ ≤ T.prob k s (te k))
    {t : State N} (ht : t ≠ te) : fullProb T s t ≤ fullProb T s te * (1 - 2 * μ) := by
  obtain ⟨k0, hk0⟩ : ∃ k, t k ≠ te k := by
    by_contra h; push Not at h; exact ht (funext h)
  have hμ1 : 1 - 2 * μ ≥ 0 := by
    have := hx k0; have := T.le_one k0 s (te k0); linarith
  have hle : ∀ k, T.prob k s (t k) ≤ (if k = k0 then 1 - 2 * μ else 1) * T.prob k s (te k) := by
    intro k
    by_cases hk : t k = te k
    · have hkk : k ≠ k0 := fun h => hk0 (h ▸ hk)
      simp [hkk, hk]
    · rw [te_prob_other T hk]
      have hxk := hx k
      split_ifs
      · nlinarith [mul_nonneg (sub_nonneg.2 hxk) (by linarith : (0 : ℝ) ≤ 2 - 2 * μ),
          mul_nonneg hμ hμ1]
      · linarith
  calc fullProb T s t = ∏ k, T.prob k s (t k) := rfl
    _ ≤ ∏ k, (if k = k0 then 1 - 2 * μ else 1) * T.prob k s (te k) :=
        prod_le_prod (fun k _ => T.nonneg k s (t k)) fun k _ => hle k
    _ = fullProb T s te * (1 - 2 * μ) := by
        rw [prod_mul_distrib, prod_ite_eq' univ k0, if_pos (mem_univ _), mul_comm]
        rfl

/-- **Lemma TE.** Under the W5 hypotheses (i)-(iv) (with `ν ≤ 1` not needed), the maximal effect
state of `univ` is the pattern `te` of the more likely bits. -/
theorem sysMaxEffStates_univ_eq_of (hpos : ∀ i r b, 0 < T.prob i r b) (te : State N) {μ ν : ℝ}
    (hμ : 0 < μ) (hx : ∀ k, 1 / 2 + μ ≤ T.prob k s (te k))
    (he : (2 : ℝ) ^ (-((N : ℝ) / 2)) ≤ fullProb T s te)
    (hRt : ∀ t, 1 / 2 ≤ effRest T s t) (hRte : effRest T s te ≤ 2)
    (hRR : ∀ t, effRest T s te ≤ effRest T s t + ν) (hν : 0 ≤ ν)
    (hμν : 3 * ν < μ * ((N : ℝ) - 10)) :
    sysMaxEffStates T univ s s = {te} := by
  have hfe : 0 < fullProb T s te := prod_pos fun i _ => hpos i s (te i)
  have hlt : ∀ t, t ≠ te → sysIiE T univ s s t < sysIiE T univ s s te := by
    intro t ht
    rw [sysIiE_univ_eq T s hpos, sysIiE_univ_eq T s hpos]
    refine te_key (prod_pos fun i _ => hpos i s (te i)) (prod_pos fun i _ => hpos i s (t i))
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

end TE

end Census
end IIT
