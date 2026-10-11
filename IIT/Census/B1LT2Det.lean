/-
Census, B1 lemma LT2 (pairs below the tilt), module M1: the deterministic pair lower bound
(`iit-census/lean/LT2-PLAN.md`).

Effect side without `effBox`: the majority values `oa, ob` of the units at the current state `s` have
probability `≥ 1/2 + γ`, and the four pair-private entries (rows `s^b`, `s^{ab}` at `a`; `s^a`, `s^{ab}` at `b`) give the
majority value probability `≤ ρ ≤ γ/10`.  The unit-level entries (rows `s`, `s^a` at `a`; `s`, `s^b` at `b`) are free.
Then every maximal effect state takes the majority values (`effPair_te`) and every cut lowers the effect probability by
a factor `≤ (1 + 2ρ)/2`, so `φ_e ≥ 1/5` (`effPair_phiE`).  Cause side: `sysPhiC_pair_ge` with block sums `≤ 4Z`.
-/
import IIT.Census.PairQuant

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-! ### The maximal effect state -/

lemma lt2_logb_le_two {x : ℝ} (hx : 0 < x) (h : x ≤ 4) : Real.logb 2 x ≤ 2 := by
  have : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
  calc Real.logb 2 x ≤ Real.logb 2 4 := Real.logb_le_logb_of_le (b := 2) (by norm_num) hx h
    _ = 2 := this

/-- `log₂ (4/(1+u)) ≥ 2 - 3u/2` for `0 ≤ u`. -/
lemma lt2_logb_four_div {u : ℝ} (hu : 0 ≤ u) : 2 - 3 / 2 * u ≤ Real.logb 2 (4 / (1 + u)) := by
  have hl2 := Real.log_two_gt_d9
  have hl2' : 0 < Real.log 2 := by linarith
  rw [Real.logb, Real.log_div (by norm_num) (by linarith), show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.log_pow, le_div_iff₀ hl2']
  have hlu : Real.log (1 + u) ≤ u := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + u by linarith); linarith
  push_cast
  nlinarith

lemma lt2_ii_formula (T : UnitTPM N) (s : State N) {a b : Fin N} (hab : a ≠ b) (t : State N) :
    sysIiE T {a, b} s s t = T.prob a s (t a) * T.prob b s (t b) *
      Real.logb 2 (T.prob a s (t a) * T.prob b s (t b) / sysUncEff T {a, b} s t) := by
  rw [sysIiE, eff_pair _ hab]

/-- The majority state has `ii_e ≥ PA PB (2 - 18ρ)`. -/
lemma lt2_ii_star (T : UnitTPM N) (s : State N) {a b : Fin N}
    (hab : a ≠ b) (oa ob : Bool) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hsa : 1 / 2 ≤ T.prob a s oa) (hsb : 1 / 2 ≤ T.prob b s ob)
    (p1 : T.prob a (flip s b) oa ≤ ρ) (p2 : T.prob a (flip (flip s a) b) oa ≤ ρ)
    (p3 : T.prob b (flip s a) ob ≤ ρ)
    (ts : State N) (hta : ts a = oa) (htb : ts b = ob) :
    T.prob a s oa * T.prob b s ob * (2 - 18 * ρ) ≤ sysIiE T {a, b} s s ts := by
  have hu := unc_pair T hab s ts
  rw [hta, htb] at hu
  have e1 : T.prob a (flip s a) oa * T.prob b (flip s a) ob ≤ ρ :=
    (mul_le_mul (T.le_one _ _ _) p3 (T.nonneg _ _ _) zero_le_one).trans_eq (one_mul ρ)
  have e2 : T.prob a (flip s b) oa * T.prob b (flip s b) ob ≤ ρ :=
    (mul_le_mul p1 (T.le_one _ _ _) (T.nonneg _ _ _) hρ0).trans_eq (mul_one ρ)
  have e3 : T.prob a (flip (flip s a) b) oa * T.prob b (flip (flip s a) b) ob ≤ ρ :=
    (mul_le_mul p2 (T.le_one _ _ _) (T.nonneg _ _ _) hρ0).trans_eq (mul_one ρ)
  set PP := T.prob a s oa * T.prob b s ob with hPPdef
  have hP4 : (1 : ℝ) / 4 ≤ PP := by
    have := mul_le_mul hsa hsb (by norm_num) (by linarith); rw [hPPdef]; linarith
  have hunc : 4 * sysUncEff T {a, b} s ts ≤ PP + 3 * ρ := by rw [hu]; linarith
  have hu0 : 0 < sysUncEff T {a, b} s ts := by
    have := mul_nonneg (T.nonneg a (flip s a) oa) (T.nonneg b (flip s a) ob)
    have := mul_nonneg (T.nonneg a (flip s b) oa) (T.nonneg b (flip s b) ob)
    have := mul_nonneg (T.nonneg a (flip (flip s a) b) oa) (T.nonneg b (flip (flip s a) b) ob)
    linarith
  have hratio : 4 / (1 + 12 * ρ) ≤ PP / sysUncEff T {a, b} s ts := by
    rw [div_le_div_iff₀ (by positivity) hu0]
    have : 4 * sysUncEff T {a, b} s ts * (1 + 12 * ρ) ≤ (PP + 3 * ρ) * (1 + 12 * ρ) :=
      mul_le_mul_of_nonneg_right hunc (by positivity)
    nlinarith
  rw [lt2_ii_formula T s hab, hta, htb]
  have hlog := (lt2_logb_four_div (u := 12 * ρ) (by positivity)).trans
    (Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hratio)
  have hPP0 : 0 ≤ PP := by linarith
  calc PP * (2 - 18 * ρ) = PP * (2 - 3 / 2 * (12 * ρ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog hPP0

/-- A non-majority state has `ii_e (1/2 + γ) ≤ 2 (1/2 - γ) PA PB`. -/
lemma lt2_ii_other (T : UnitTPM N) (hT : ∀ i r x, 0 < T.prob i r x) (s : State N) {a b : Fin N}
    (hab : a ≠ b) (oa ob : Bool) {γ : ℝ} (hγ0 : 0 < γ)
    (hsa : 1 / 2 + γ ≤ T.prob a s oa) (hsb : 1 / 2 + γ ≤ T.prob b s ob)
    (t : State N) (ht : ¬ (t a = oa ∧ t b = ob)) :
    sysIiE T {a, b} s s t * (1 / 2 + γ) ≤ 2 * ((1 / 2 - γ) * (T.prob a s oa * T.prob b s ob)) := by
  have hp0 : 0 < T.prob a s (t a) * T.prob b s (t b) := mul_pos (hT _ _ _) (hT _ _ _)
  have hu := unc_pair T hab s t
  have hu0 : T.prob a s (t a) * T.prob b s (t b) ≤ 4 * sysUncEff T {a, b} s t := by
    rw [hu]
    have := mul_nonneg (T.nonneg a (flip s a) (t a)) (T.nonneg b (flip s a) (t b))
    have := mul_nonneg (T.nonneg a (flip s b) (t a)) (T.nonneg b (flip s b) (t b))
    have := mul_nonneg (T.nonneg a (flip (flip s a) b) (t a)) (T.nonneg b (flip (flip s a) b) (t b))
    linarith
  have hu0' : 0 < sysUncEff T {a, b} s t := by linarith
  have hlog : Real.logb 2 (T.prob a s (t a) * T.prob b s (t b) / sysUncEff T {a, b} s t) ≤ 2 :=
    lt2_logb_le_two (div_pos hp0 hu0') (by rw [div_le_iff₀ hu0']; linarith)
  have hii : sysIiE T {a, b} s s t ≤ 2 * (T.prob a s (t a) * T.prob b s (t b)) := by
    rw [lt2_ii_formula T s hab]
    calc _ ≤ T.prob a s (t a) * T.prob b s (t b) * 2 := mul_le_mul_of_nonneg_left hlog hp0.le
      _ = _ := by ring
  have hnot : ∀ (i : Fin N) (o x : Bool), x ≠ o → 1 / 2 + γ ≤ T.prob i s o →
      T.prob i s x ≤ 1 / 2 - γ := by
    intro i o x hx hpo
    have hn := T.normalized i s
    cases o <;> cases x
    · exact absurd rfl hx
    · linarith
    · linarith
    · exact absurd rfl hx
  have hge : ∀ (i : Fin N) (o x : Bool), 1 / 2 + γ ≤ T.prob i s o → T.prob i s x ≤ T.prob i s o := by
    intro i o x hpo
    by_cases hx : x = o
    · rw [hx]
    · have := hnot i o x hx hpo; linarith
  have hPA0 : 0 ≤ T.prob a s oa := T.nonneg _ _ _
  have hPB0 : 0 ≤ T.prob b s ob := T.nonneg _ _ _
  have nb := T.nonneg b s (t b)
  have hkey : T.prob a s (t a) * T.prob b s (t b) * (1 / 2 + γ) ≤
      (1 / 2 - γ) * (T.prob a s oa * T.prob b s ob) := by
    by_cases ha : t a = oa
    · have hb : t b ≠ ob := fun h => ht ⟨ha, h⟩
      have h1 := hnot b ob (t b) hb hsb
      have h2 : T.prob a s (t a) ≤ T.prob a s oa := hge a oa (t a) hsa
      calc T.prob a s (t a) * T.prob b s (t b) * (1 / 2 + γ)
          ≤ T.prob a s oa * (1 / 2 - γ) * T.prob b s ob :=
            mul_le_mul (mul_le_mul h2 h1 nb hPA0) hsb (by linarith) (mul_nonneg hPA0 (by linarith [h1, nb]))
        _ = _ := by ring
    · have h1 := hnot a oa (t a) ha hsa
      have h2 : T.prob b s (t b) ≤ T.prob b s ob := hge b ob (t b) hsb
      calc T.prob a s (t a) * T.prob b s (t b) * (1 / 2 + γ)
          ≤ (1 / 2 - γ) * T.prob b s ob * T.prob a s oa :=
            mul_le_mul (mul_le_mul h1 h2 nb (by linarith [h1, T.nonneg a s (t a)])) hsa (by linarith)
              (mul_nonneg (by linarith [h1, T.nonneg a s (t a)]) hPB0)
        _ = _ := by ring
  calc sysIiE T {a, b} s s t * (1 / 2 + γ) ≤ 2 * (T.prob a s (t a) * T.prob b s (t b)) * (1 / 2 + γ) :=
        mul_le_mul_of_nonneg_right hii (by linarith)
    _ = 2 * (T.prob a s (t a) * T.prob b s (t b) * (1 / 2 + γ)) := by ring
    _ ≤ _ := by linarith

/-- **The maximal effect state takes the majority values.** -/
theorem effPair_te (T : UnitTPM N) (hT : ∀ i r x, 0 < T.prob i r x) (s : State N) {a b : Fin N}
    (hab : a ≠ b) (oa ob : Bool) {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hρ0 : 0 ≤ ρ) (hργ : 10 * ρ ≤ γ)
    (hsa : 1 / 2 + γ ≤ T.prob a s oa) (hsb : 1 / 2 + γ ≤ T.prob b s ob)
    (p1 : T.prob a (flip s b) oa ≤ ρ) (p2 : T.prob a (flip (flip s a) b) oa ≤ ρ)
    (p3 : T.prob b (flip s a) ob ≤ ρ) (p4 : T.prob b (flip (flip s a) b) ob ≤ ρ) :
    ∀ te ∈ sysMaxEffStates T {a, b} s s, te a = oa ∧ te b = ob := by
  intro te hte
  set ts : State N := Function.update (Function.update s a oa) b ob with hts
  have htsa : ts a = oa := by simp [hts, Function.update_of_ne hab]
  have htsb : ts b = ob := by simp [hts]
  have hstar := lt2_ii_star T s hab oa ob hρ0 (by linarith) (by linarith) p1 p2 p3 ts htsa htsb
  have hmax := (mem_argmaxSet.1 hte) ts
  by_contra hne
  have hoth := lt2_ii_other T hT s hab oa ob hγ0 hsa hsb te hne
  set PP := T.prob a s oa * T.prob b s ob with hPPdef
  have hPP : (1 / 4 : ℝ) ≤ PP := by
    have := mul_le_mul hsa hsb (by linarith) (by linarith); rw [hPPdef]; nlinarith
  have hc : 2 * (1 / 2 - γ) < (2 - 18 * ρ) * (1 / 2 + γ) := by
    have : 18 * ρ * γ ≤ 18 * ρ * (1 / 2) := mul_le_mul_of_nonneg_left hγ2 (by positivity)
    nlinarith
  have h1 : 2 * ((1 / 2 - γ) * PP) < PP * (2 - 18 * ρ) * (1 / 2 + γ) := by
    have := mul_lt_mul_of_pos_left hc (show 0 < PP by linarith)
    calc 2 * ((1 / 2 - γ) * PP) = PP * (2 * (1 / 2 - γ)) := by ring
      _ < PP * ((2 - 18 * ρ) * (1 / 2 + γ)) := this
      _ = _ := by ring
  have h2 : sysIiE T {a, b} s s ts * (1 / 2 + γ) ≤ sysIiE T {a, b} s s te * (1 / 2 + γ) :=
    mul_le_mul_of_nonneg_right hmax (by linarith)
  have h3 := mul_le_mul_of_nonneg_right hstar (show (0 : ℝ) ≤ 1 / 2 + γ by linarith)
  linarith

/-! ### `φ_e ≥ 1/5` -/

lemma lt2_effFactor (T : UnitTPM N) (hT : ∀ i r x, 0 < T.prob i r x) (s : State N) (M : Finset (Fin N))
    {i k : Fin N} (o : Bool) {ρ : ℝ} (hρ1 : ρ ≤ 1 / 2) (hM : M = ∅ ∨ M = {k}) (h1 : 1 / 2 ≤ T.prob i s o)
    (h2 : T.prob i (flip s k) o ≤ ρ) :
    0 < effUnit T Mᶜ s i o ∧ effUnit T Mᶜ s i o ≤ T.prob i s o ∧
      (M.Nonempty → effUnit T Mᶜ s i o ≤ (1 + 2 * ρ) / 2 * T.prob i s o) := by
  have hp := hT i s o
  have hq := hT i (flip s k) o
  rcases hM with rfl | rfl
  · rw [compl_empty, effUnit_univ_prob]
    exact ⟨hp, le_rfl, fun h => absurd h (by simp)⟩
  · rw [effUnit_compl_single]
    have hρ : 0 ≤ ρ := hq.le.trans h2
    refine ⟨by positivity, ?_, fun _ => ?_⟩
    · have : T.prob i (flip s k) o ≤ T.prob i s o := by linarith
      linarith
    · nlinarith

/-- **`φ_e ≥ 1/5` at every partition** (majority values, private entries `≤ ρ ≤ min(γ/10, 1/100)`). -/
theorem effPair_phiE (T : UnitTPM N) (hT : ∀ i r x, 0 < T.prob i r x) (s : State N) {a b : Fin N}
    (hab : a ≠ b) (oa ob : Bool) {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hρ0 : 0 ≤ ρ) (hργ : 10 * ρ ≤ γ)
    (hρ1 : ρ ≤ 1 / 100)
    (hsa : 1 / 2 + γ ≤ T.prob a s oa) (hsb : 1 / 2 + γ ≤ T.prob b s ob)
    (p1 : T.prob a (flip s b) oa ≤ ρ) (p2 : T.prob a (flip (flip s a) b) oa ≤ ρ)
    (p3 : T.prob b (flip s a) ob ≤ ρ) (p4 : T.prob b (flip (flip s a) b) ob ≤ ρ) :
    ∀ te ∈ sysMaxEffStates T {a, b} s s, ∀ θ : SysPartition N {a, b},
      1 / 5 ≤ sysPhiE T {a, b} s θ s te := by
  intro te hte θ
  obtain ⟨hta, htb⟩ := effPair_te T hT s hab oa ob hγ0 hγ2 hρ0 hργ hsa hsb p1 p2 p3 p4 te hte
  have hγ : 0 ≤ γ := by linarith
  have haS : a ∈ ({a, b} : Finset (Fin N)) := mem_insert_self _ _
  have hbS : b ∈ ({a, b} : Finset (Fin N)) := mem_insert_of_mem (mem_singleton_self _)
  have hea : ({a, b} : Finset (Fin N)).erase a ⊆ {b} := by
    intro x hx; simp only [mem_erase, mem_insert, mem_singleton] at hx ⊢; tauto
  have heb : ({a, b} : Finset (Fin N)).erase b ⊆ {a} := by
    intro x hx; simp only [mem_erase, mem_insert, mem_singleton] at hx ⊢; tauto
  -- the private entry of row `s^a` at `b` is the one of `flip s a`
  obtain ⟨pa, la, sa⟩ := lt2_effFactor T hT s _ oa (by linarith) (cut_cases_pair θ hea haS) (by linarith) p1
  obtain ⟨pb, lb, sb⟩ := lt2_effFactor T hT s _ ob (by linarith) (cut_cases_pair θ heb hbS) (by linarith) p3
  set PA := T.prob a s oa
  set PB := T.prob b s ob
  have hE : sysEffProb T {a, b} s s te = PA * PB := by rw [eff_pair _ hab, hta, htb]
  have hP : sysPartEffProb T {a, b} s θ s te =
      effUnit T (θ.cutSet (θ.partOf a))ᶜ s a oa * effUnit T (θ.cutSet (θ.partOf b))ᶜ s b ob := by
    rw [sysPartEffProb, merge_self, prod_pair hab, hta, htb]
  have hle : sysPartEffProb T {a, b} s θ s te ≤ (1 + 2 * ρ) / 2 * sysEffProb T {a, b} s s te := by
    rw [hE, hP]
    rcases exists_cut_pair θ with hc | hc
    · calc _ ≤ (1 + 2 * ρ) / 2 * PA * _ := mul_le_mul_of_nonneg_right (sa hc) pb.le
        _ ≤ (1 + 2 * ρ) / 2 * PA * PB := mul_le_mul_of_nonneg_left lb (by nlinarith)
        _ = _ := by ring
    · calc _ ≤ _ * ((1 + 2 * ρ) / 2 * PB) := mul_le_mul_of_nonneg_left (sb hc) pa.le
        _ ≤ PA * ((1 + 2 * ρ) / 2 * PB) := mul_le_mul_of_nonneg_right la (by nlinarith)
        _ = _ := by ring
  have hP0 : 0 < sysPartEffProb T {a, b} s θ s te := by rw [hP]; exact mul_pos pa pb
  have hE0 : 1 / 4 ≤ sysEffProb T {a, b} s s te := by rw [hE]; nlinarith
  have hratio : 2 / (1 + 2 * ρ) ≤ sysEffProb T {a, b} s s te / sysPartEffProb T {a, b} s θ s te := by
    rw [div_le_div_iff₀ (by positivity) hP0]; nlinarith
  have hlog : 9 / 10 ≤ Real.logb 2 (sysEffProb T {a, b} s s te / sysPartEffProb T {a, b} s θ s te) := by
    have h2 : 2 - 3 / 2 * (2 * ρ) ≤ Real.logb 2 (4 / (1 + 2 * ρ)) := lt2_logb_four_div (by positivity)
    have h3 : Real.logb 2 (4 / (1 + 2 * ρ)) = 1 + Real.logb 2 (2 / (1 + 2 * ρ)) := by
      rw [show (4 : ℝ) / (1 + 2 * ρ) = 2 * (2 / (1 + 2 * ρ)) by ring,
        Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]
    have h4 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hratio
    linarith
  unfold sysPhiE
  calc (1 / 5 : ℝ) ≤ 1 / 4 * (9 / 10) := by norm_num
    _ ≤ _ := mul_le_mul hE0 (le_max_of_le_right hlog) (by norm_num) (by linarith)

/-! ### The pair -/

/-- **The deterministic pair lower bound of LT2.** Open cube, `Z ≤ 13`, a pattern winning by `Δ` in both block sums,
and the weakened effect box: `φ_s ≥ min (1/5) (Δ / 416)`. -/
theorem lt2_pair_phi {z : Param N} (hz : z ∈ openCube N) (s : State N) {a b : Fin N} (hab : a ≠ b)
    {Δ : ℝ} (hΔ : 0 < Δ) (hsame : sameArgQ z s a b Δ) (hZ : ∑ v : State N, rowProd z s v ≤ 13)
    (oa ob : Bool) {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hρ0 : 0 ≤ ρ) (hργ : 10 * ρ ≤ γ) (hρ1 : ρ ≤ 1 / 100)
    (hsa : 1 / 2 + γ ≤ (tpmOf z).prob a s oa) (hsb : 1 / 2 + γ ≤ (tpmOf z).prob b s ob)
    (p1 : (tpmOf z).prob a (flip s b) oa ≤ ρ) (p2 : (tpmOf z).prob a (flip (flip s a) b) oa ≤ ρ)
    (p3 : (tpmOf z).prob b (flip s a) ob ≤ ρ) (p4 : (tpmOf z).prob b (flip (flip s a) b) ob ≤ ρ) :
    min (1 / 5) (Δ / 416) ≤ phi z s {a, b} := by
  have hT : ∀ i r x, 0 < (tpmOf z).prob i r x := by
    intro i r x
    rw [prob_of_mem hz]
    have h := hz r i
    cases x <;> simp <;> linarith [h.1, h.2]
  obtain ⟨tc, htc⟩ := sysMaxCauseStates_nonempty (tpmOf z) {a, b} s s
  obtain ⟨te, hte⟩ := sysMaxEffStates_nonempty (tpmOf z) {a, b} s s
  have hB : ∀ i t, U z s {a, b} i t ≤ 52 := by
    intro i t
    have := U_le_Zsum z s {a, b} i t
    rw [card_pair hab] at this
    norm_num at this
    linarith
  refine le_phi_pair_of s hab htc hte fun θ => le_min ?_ ?_
  · have h := sysPhiC_pair_ge hz s hab hΔ hB (hUQ_of_sameArgQ hz s hab hΔ hsame) tc htc θ
    rw [show Δ / (8 * 52) = Δ / 416 by norm_num] at h
    exact (min_le_right _ _).trans h
  · exact (min_le_left _ _).trans
      (effPair_phiE (tpmOf z) hT s hab oa ob hγ0 hγ2 hρ0 hργ hρ1 hsa hsb p1 p2 p3 p4 te hte θ)

end Census
end IIT

#print axioms IIT.Census.lt2_pair_phi
