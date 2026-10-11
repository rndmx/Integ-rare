/-
Census, B1, W14 work package WP2 (cause side), part 5 (sub-package 2B, second half): the competitor
`(h4)` (near-full purviews at a pattern `z ≠ r0` on `Z`).

* `cs_W_le`: `Σ_i ln max(2 Ā_i(C), 1) ≤ 23N/50` for every subcube `C = agree Z z` of dimension
  `1 … J` not containing `r0` (W5 (h4), W13-cause table rows (h4), G3, G4): `nuS` (`s ∈ C`,
  `d' ≤ 2`), `x5` (`r0^x ∈ C`, cause, `d' ≤ 3`), `x5e1` (`s^x ∈ C`, effect, `d' = 1`), FE3
  (`C ∩ Sens = ∅`), else the Jensen bound `logW_le_jensen` with `ρ = 137/500` (`rowExc`, FE2);
* `cs_phiCat_h4`: `φ_c(Z, z) < causeRep(univ, r0) e^{-N/200}`.
Numeric inputs are explicit hypotheses.  Blueprint: `iit-census/lean/B1-W14-count-lean.md` §7.
No `sorry`.
-/
import IIT.Census.B1CntCauseH

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

lemma cs_logmax_mono {a b : ℝ} (hab : a ≤ b) :
    Real.log (max (2 * a) 1) ≤ Real.log (max (2 * b) 1) :=
  Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _)) (max_le_max (by linarith) le_rfl)

lemma cs_log_W_level : Real.log (2 * (b1Cap + 137 / 500)) ≤ 23 / 50 := by
  rw [Real.log_le_iff_le_exp (by unfold b1Cap; norm_num)]
  have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 23 / 50)
  unfold b1Cap; linarith

/-- Rows of a subcube meeting `Sens`, other than `s` and the special row, have excess `≤ N/5`. -/
lemma cs_exc_cubeZ {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    (hg : GoodW3 N s r0 x σ w) (hfr : CountFreshX N s r0 w)
    {Z : Finset (Fin N)} {z : State N} (hZJ : N ≤ Z.card + JC N) (hr0 : r0 ∉ agree Z z)
    {r' : State N} (hr' : r' ∈ agree Z z) (hr'S : r' ∈ sensRows s r0)
    {r : State N} (hr : r ∈ agree Z z) (hrs : r ≠ s) (hrsp : r ≠ spRow s r0 x σ) :
    csExc w r ≤ N / 5 := by
  by_cases hS : r ∈ sensRows s r0
  · exact hg.1.rowExc r hS (fun e => hr0 (e ▸ hr)) hrs hrsp
  · refine hfr.fe2 r hS ⟨r', hr'S, ?_⟩
    have := ham_le_of_mem_agree hr hr'
    omega

/-- The Jensen case of `(h4)`: at most `q` special rows, `4q ≤ |C|`. -/
lemma cs_W_jensen {w : Param N} (Z : Finset (Fin N)) (z : State N) (Sp : Finset (State N)) {q : ℕ}
    (hq : Sp.card ≤ q) (h4q : 4 * q ≤ 2 ^ (N - Z.card))
    (hrows : ∀ r ∈ agree Z z, r ∉ Sp → csExc w r ≤ N / 5) :
    ∑ i, Real.log (max (2 * subMean w Z z i) 1) ≤ 23 / 50 * N := by
  have hex := cs_sum_exc_le w (agree Z z) Sp hq hrows
  have hC : ((agree Z z).card : ℝ) = 2 ^ (N - Z.card) := by rw [card_agree]; push_cast; rfl
  have h4qR : 4 * (q : ℝ) ≤ (agree Z z).card := by rw [hC]; exact_mod_cast h4q
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hρ : ∑ r ∈ agree Z z, ∑ i, pos (clamp01 (w r i) - b1Cap) ≤
      (137 / 500) * N * (agree Z z).card := by
    change ∑ r ∈ agree Z z, csExc w r ≤ _
    refine hex.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left h4qR hN]
  refine (logW_le_jensen w Z z hρ).trans ?_
  have := cs_log_W_level
  nlinarith

/-- **The level `23N/50` for every near-full subcube avoiding `r0`.** -/
theorem cs_W_le {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    (hg : GoodW3 N s r0 x σ w) (hfr : CountFreshX N s r0 w) (_hw : w ∈ openCube N)
    (hJ3 : 3 * JC N + 3 < N)
    {Z : Finset (Fin N)} (z : State N) (hZJ : N ≤ Z.card + JC N) (hZc : Z.card < N)
    (hr0 : r0 ∉ agree Z z) :
    ∑ i, Real.log (max (2 * subMean w Z z i) 1) ≤ 23 / 50 * N := by
  set C := agree Z z with hCdef
  set K' := Zᶜ with hK'
  have hK'c : K'ᶜ = Z := by rw [hK', compl_compl]
  have hK'card : K'.card = N - Z.card := by rw [hK', card_compl, Fintype.card_fin]
  have hK'ne : K'.Nonempty := by rw [← card_pos, hK'card]; omega
  have hfar := hg.1.far
  -- subcube means through any row of `C`
  have hmean : ∀ t ∈ C, ∀ i, subMean w Z z i = subMean w K'ᶜ t i := by
    intro t ht i; rw [hK'c]; unfold subMean; rw [agree_eq_of_mem ht]
  -- `s` and `r0^x` are far apart
  have hsr1 : ¬ (s ∈ C ∧ flipAt x r0 ∈ C) := by
    rintro ⟨h1, h2⟩
    have h3 := ham_le_of_mem_agree h1 h2
    have h4 := ham_triangle r0 (flipAt x r0) s
    have h5 : ham r0 (flipAt x r0) ≤ 1 := by rw [ham_comm]; exact ham_flipAt_le_one x r0
    have h6 := ham_comm s (flipAt x r0)
    unfold JC at hJ3 hZJ; omega
  by_cases c1 : s ∈ C ∧ N - Z.card ≤ 2
  · -- `nuS`
    have h := hg.1.nuS K' hK'ne (by omega)
    refine le_trans (le_of_eq ?_) h
    refine sum_congr rfl fun i _ => ?_
    rw [hmean s c1.1 i]
    unfold b1CutMeanS subMean
    rw [cs_card_agree_compl]
  by_cases c2 : σ = .cause ∧ flipAt x r0 ∈ C ∧ N - Z.card ≤ 3
  · -- `x5`
    obtain ⟨hσ, h1, h3⟩ := c2
    have hxZ : x ∈ Z := by
      by_contra hxZ
      apply hr0
      rw [hCdef, ← agree_eq_of_mem h1, mem_agree]
      intro j hj
      have hjx : j ≠ x := fun e => hxZ (e ▸ hj)
      rw [flipAt, Function.update_of_ne hjx]
    have hxK' : x ∉ K' := by rw [hK', mem_compl, not_not]; exact hxZ
    have h := hg.1.x5 hσ K' hK'ne (by omega) hxK'
    refine le_trans (sum_le_sum fun i _ => ?_) h
    rw [hmean _ h1 i]
    exact cs_logmax_mono (cs_subMean_le_meanPlus w _ K' i)
  by_cases c3 : σ = .effect ∧ flipAt x s ∈ C ∧ N - Z.card = 1
  · -- `x5e1`
    obtain ⟨hσ, h1, h3⟩ := c3
    obtain ⟨j, hj⟩ := card_eq_one.1 (hK'card.trans h3)
    have hsC : s ∉ C := fun hs => c1 ⟨hs, by omega⟩
    have hjx : j ≠ x := by
      rintro rfl
      apply hsC
      rw [hCdef, ← agree_eq_of_mem h1, ← hK'c, hj, cs_mem_agree_compl_single]
      right; rw [flipAt_flipAt]
    have h := hg.2.x5e1 hσ j hjx
    refine le_trans (sum_le_sum fun i _ => ?_) h
    rw [hmean _ h1 i, hj]
    exact cs_logmax_mono (cs_subMean_le_meanPlus w _ {j} i)
  by_cases c4 : ∀ r ∈ C, r ∉ sensRows s r0
  · -- FE3
    exact hfr.fe3 z Z hZJ hZc c4
  -- the Jensen case
  push Not at c4
  obtain ⟨r', hr', hr'S⟩ := c4
  have hrow := fun r hr hrs hrsp => cs_exc_cubeZ hg hfr hZJ hr0 hr' hr'S (r := r) hr hrs hrsp
  have hpow : ∀ k : ℕ, k ≤ N - Z.card → (2 : ℕ) ^ k ≤ 2 ^ (N - Z.card) := fun k hk =>
    Nat.pow_le_pow_right (by norm_num) hk
  by_cases hs : s ∈ C
  · refine cs_W_jensen Z z {s, spRow s r0 x σ} (q := 2) card_le_two ?_ ?_
    · have : 3 ≤ N - Z.card := by by_contra h; exact c1 ⟨hs, by omega⟩
      have := hpow 3 this; norm_num at this ⊢; omega
    · intro r hr hsp
      simp only [mem_insert, mem_singleton, not_or] at hsp
      exact hrow r hr hsp.1 hsp.2
  by_cases hsp : spRow s r0 x σ ∈ C
  · refine cs_W_jensen Z z {spRow s r0 x σ} (q := 1) (by simp) ?_ ?_
    · cases σ with
      | cause =>
        have : 4 ≤ N - Z.card := by
          by_contra h; exact c2 ⟨rfl, hsp, by omega⟩
        have := hpow 2 (by omega); norm_num at this ⊢; omega
      | effect =>
        have : 2 ≤ N - Z.card := by
          by_contra h
          exact c3 ⟨rfl, hsp, by omega⟩
        have := hpow 2 this; norm_num at this ⊢; omega
    · intro r hr hsp'
      rw [mem_singleton] at hsp'
      exact hrow r hr (fun e => hs (e ▸ hr)) hsp'
  · refine cs_W_jensen Z z ∅ (q := 0) (by simp) (by simp) ?_
    intro r hr _
    exact hrow r hr (fun e => hs (e ▸ hr)) (fun e => hsp (e ▸ hr))

/-- **`(h4)`** (Phi level). -/
theorem cs_phiCat_h4 {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    (hg : GoodW3 N s r0 x σ w) (hfr : CountFreshX N s r0 w) (hw : w ∈ openCube N)
    {K : Finset (Fin N)} (hK : K ∈ famX3 N s r0 x σ w)
    (hN : 10000 ≤ N) (hJ3 : 3 * JC N + 3 < N)
    (hsens : 2 * ((N : ℝ) + 1) ^ 4 ≤ 2 ^ (dX N + 1))
    (hH4 : 4 * (N : ℝ) ^ 2 * Real.exp (23 / 50 * N) * 2 ^ JC N / 2 ^ N <
      Real.exp (-(x0 * N + slT N)) / 2 ^ (dX N + 2) * Real.exp (-((N : ℝ) / 200)))
    {Z : Finset (Fin N)} (z : State N) (hZu : Z ≠ univ) (hZJ : N ≤ Z.card + JC N)
    (hzr : ∃ i ∈ Z, z i ≠ r0 i) :
    phiCat (tpmOf (flipP s w)) Z z (univ \ K) s <
      causeRep (tpmOf (flipP s w)) univ r0 (univ \ K) s * Real.exp (-((N : ℝ) / 200)) := by
  set a := Real.exp (-((N : ℝ) / 200)) with hadef
  have hapos : 0 < a := Real.exp_pos _
  have hKc := famX3_card hK
  have hNr : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have hdN : dX N ≤ N := cs_dX_le_N (by omega)
  have hMne : (univ \ K).Nonempty := by
    rw [← card_pos, cs_card_M hKc]
    have := cs_dX_le N
    have h1 : dX N < N := by
      have : (dX N : ℝ) < N := by linarith
      exact_mod_cast this
    omega
  have hZc : Z.card < N := by
    have := card_lt_card ((subset_univ Z).ssubset_of_ne hZu); simpa using this
  have hZne : Z.Nonempty := by
    rw [← card_pos]; unfold JC at hJ3 hZJ; omega
  have hr0 : r0 ∉ agree Z z := by
    obtain ⟨i, hi, hne⟩ := hzr
    intro h; exact hne ((mem_agree.1 h i hi).symm)
  have hW := cs_W_le hg hfr hw hJ3 z hZJ hZc hr0
  -- the forward term
  set E := Real.exp (23 / 50 * N) with hE
  have hcf : causeFwd (tpmOf (flipP s w)) Z z (univ \ K) s ≤ (1 / 2) ^ (N - dX N) * E := by
    rw [cs_causeFwd_eq]
    have h1 : ∀ i ∈ univ \ K, subMean w Z z i ≤ 1 / 2 * max (2 * subMean w Z z i) 1 :=
      fun i _ => by have := le_max_left (2 * subMean w Z z i) 1; linarith
    have hprod : ∏ i ∈ univ \ K, (1 / 2 * max (2 * subMean w Z z i) 1) =
        (1 / 2) ^ (N - dX N) * Real.exp (∑ i ∈ univ \ K, Real.log (max (2 * subMean w Z z i) 1)) := by
      rw [prod_mul_distrib, prod_const, cs_card_M hKc, Real.exp_sum]
      congr 1
      exact prod_congr rfl fun i _ => (Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))).symm
    have hsub : ∑ i ∈ univ \ K, Real.log (max (2 * subMean w Z z i) 1) ≤
        ∑ i, Real.log (max (2 * subMean w Z z i) 1) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ =>
        Real.log_nonneg (le_max_right _ _)
    calc ∏ i ∈ univ \ K, subMean w Z z i ≤ ∏ i ∈ univ \ K, (1 / 2 * max (2 * subMean w Z z i) 1) :=
          prod_le_prod (fun i _ => (cs_subMean_pos hw Z z i).le) h1
      _ = _ := hprod
      _ ≤ (1 / 2) ^ (N - dX N) * E := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hsub.trans hW)) (by positivity)
  -- FE5 and the total cut
  have hB : (0 : ℝ) < 1 / 2 ^ (N - dX N + 2) := by positivity
  have hunc := hfr.fe5 K hKc Z hZJ hZc
  have hrep := cs_causeRep_le s w Z z (univ \ K) hB hunc
  rw [← cs_causeFwd_eq] at hrep
  have hle := cs_phiCat_le_rep (tpmOf (flipP s w)) Z z (univ \ K) s hMne hZne
    (cs_partCauseFwd_total_pos hw s Z z _ hMne)
  have hMZ : ((univ \ K).card : ℝ) * Z.card ≤ (N : ℝ) ^ 2 := by
    have h1 : ((univ \ K).card : ℝ) ≤ N := by exact_mod_cast (card_le_univ _).trans (by simp)
    have h2 : (Z.card : ℝ) ≤ N := by exact_mod_cast hZc.le
    nlinarith [Nat.cast_nonneg (α := ℝ) Z.card]
  have hrep0 := causeRep_nonneg (tpmOf (flipP s w)) Z z (univ \ K) s
  have hpowZ : (2 : ℝ) ^ N ≤ 2 ^ Z.card * 2 ^ JC N := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) hZJ
  have hhalf : (1 / 2 : ℝ) ^ (N - dX N) * 2 ^ (N - dX N + 2) = 4 := by
    rw [pow_add, ← mul_assoc, ← mul_pow]; norm_num
  have hstep : phiCat (tpmOf (flipP s w)) Z z (univ \ K) s ≤
      4 * (N : ℝ) ^ 2 * E * 2 ^ JC N / 2 ^ N := by
    refine hle.trans ((mul_le_mul_of_nonneg_left hMZ hrep0).trans ?_)
    have hZ2 : (0 : ℝ) < 2 ^ Z.card := by positivity
    calc causeRep (tpmOf (flipP s w)) Z z (univ \ K) s * (N : ℝ) ^ 2
        ≤ (causeFwd (tpmOf (flipP s w)) Z z (univ \ K) s /
            (2 ^ Z.card * (1 / 2 ^ (N - dX N + 2)))) * (N : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hrep (by positivity)
      _ ≤ ((1 / 2) ^ (N - dX N) * E / (2 ^ Z.card * (1 / 2 ^ (N - dX N + 2)))) * (N : ℝ) ^ 2 := by
          gcongr
      _ = 4 * (N : ℝ) ^ 2 * E / 2 ^ Z.card := by
          rw [← hhalf]; field_simp
      _ ≤ 4 * (N : ℝ) ^ 2 * E * 2 ^ JC N / 2 ^ N := by
          rw [div_le_div_iff₀ hZ2 (by positivity)]
          have : 0 ≤ 4 * (N : ℝ) ^ 2 * E := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hpowZ this]
  refine lt_of_le_of_lt hstep (lt_of_lt_of_le hH4 ?_)
  exact mul_le_mul_of_nonneg_right (cs_causeRep_univ_r0_ge hg hfr hw hsens hKc) hapos.le

end Census
end IIT
