/-
Census pair step with margins, part 2: some pair reaches `φ_s ≥ σ_N / 128`.

If a pair `{a, b}` sits in the effect box (`effBox`), one pair state beats all others by `Δ` in
both block sums (`sameArgQ`), and the Bayes normaliser `Z = ∑ᵥ P(v)` is at most `2`, then
`φ_s({a, b}) ≥ min (1/5) (Δ/64)` (`phi_pair_ge`): on the cause side every block sum is at most
`4Z ≤ 8`, the selectivity of the maximal cause state is at least `1/4`, and a cut lowers the cause
probability by the factor `1 - Δ/16`; on the effect side a cut lowers the effect probability by the
factor `0.78`.  With `Δ = σ_N / 2` (`limsup_allBadQ`) and `Z ≤ 2` with probability tending to one
(Chebyshev in flipped coordinates), no pair reaching `σ_N / 128` has probability tending to zero
(`tendsto_noGoodPair`).
-/
import IIT.Census.PairQuant2
import IIT.Census.BigPhiBridge
import IIT.Census.UnivZero

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

variable {N : ℕ}

/-! ### A lower bound for `log₂` -/

private lemma le_logb_of_le_mul {p q x : ℝ} (hp : 0 < p) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (h : p ≤ (1 - x) * q) : x ≤ Real.logb 2 (q / p) := by
  have h1x : 0 < 1 - x := by linarith
  have hy : 1 / (1 - x) ≤ q / p := by
    rw [div_le_div_iff₀ h1x hp]; nlinarith
  have hl1 : x ≤ Real.log (1 / (1 - x)) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_sub_one_of_pos h1x
    linarith
  have hl2 : Real.log (1 / (1 - x)) ≤ Real.log (q / p) :=
    Real.log_le_log (by positivity) hy
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; norm_num at this; linarith
  rw [Real.logb, le_div_iff₀ hlog2]
  nlinarith

/-! ### The cause side with a margin -/

private lemma partFactor_boundQ {z : Param N} (hz : z ∈ openCube N) (s t : State N)
    {S : Finset (Fin N)} (M : Finset (Fin N)) {j k : Fin N} (hk : k ∈ S)
    (hM : M = ∅ ∨ M = {k}) {Δ B : ℝ} (hΔ : 0 < Δ)
    (hle : U z s S j (flip t k) + Δ ≤ U z s S j t) (hB : U z s S j t ≤ B) :
    let F := (∑ w : State N, effUnit (tpmOf z) Mᶜ (merge S t w) j (s j)
        * bgWeight (tpmOf z) S s w) / (2 : ℝ) ^ S.card
    let C := U z s S j t / (∑ v : State N, fullProb (tpmOf z) v s) / (2 : ℝ) ^ S.card
    0 < F ∧ F ≤ C ∧ (M.Nonempty → F ≤ (1 - Δ / (2 * B)) * C) := by
  intro F C
  have hlt : U z s S j (flip t k) < U z s S j t := by linarith
  obtain ⟨h0, h1, -⟩ := partFactor_bound hz s t M hk hM hlt
  refine ⟨h0, h1, fun hne => ?_⟩
  rcases hM with rfl | rfl
  · simp at hne
  · have hF : F = (U z s S j t + U z s S j (flip t k)) / 2 / (∑ v : State N,
        fullProb (tpmOf z) v s) / (2 : ℝ) ^ S.card := partFactor_single z s t S j k hk
    have hZ := sum_fullProb_pos hz s
    have hU1 := U_pos hz s S j t
    have hB0 : 0 < B := hU1.trans_le hB
    have key : (U z s S j t + U z s S j (flip t k)) / 2 ≤ (1 - Δ / (2 * B)) * U z s S j t := by
      have h2 : Δ / (2 * B) * U z s S j t ≤ Δ / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      nlinarith
    have hD : 0 < (∑ v : State N, fullProb (tpmOf z) v s) * (2 : ℝ) ^ S.card := by positivity
    rw [hF]
    calc (U z s S j t + U z s S j (flip t k)) / 2 / (∑ v : State N, fullProb (tpmOf z) v s)
          / (2 : ℝ) ^ S.card
        = ((U z s S j t + U z s S j (flip t k)) / 2) /
            ((∑ v : State N, fullProb (tpmOf z) v s) * (2 : ℝ) ^ S.card) := by ring
      _ ≤ ((1 - Δ / (2 * B)) * U z s S j t) /
            ((∑ v : State N, fullProb (tpmOf z) v s) * (2 : ℝ) ^ S.card) :=
          div_le_div_of_nonneg_right key hD.le
      _ = (1 - Δ / (2 * B)) * C := by simp only [C]; ring

private lemma sysPartCauseProb_le_pair {z : Param N} (hz : z ∈ openCube N) (s tc : State N)
    {a b : Fin N} (hab : a ≠ b) (θ : SysPartition N {a, b}) {Δ B : ℝ} (hΔ : 0 < Δ)
    (ha : U z s {a, b} a (flip tc b) + Δ ≤ U z s {a, b} a tc)
    (hb : U z s {a, b} b (flip tc a) + Δ ≤ U z s {a, b} b tc)
    (hBa : U z s {a, b} a tc ≤ B) (hBb : U z s {a, b} b tc ≤ B) :
    0 < sysPartCauseProb (tpmOf z) {a, b} s θ s tc ∧
      sysPartCauseProb (tpmOf z) {a, b} s θ s tc ≤
        (1 - Δ / (2 * B)) * sysCauseProb (tpmOf z) {a, b} s s tc := by
  have haS : a ∈ ({a, b} : Finset (Fin N)) := mem_insert_self _ _
  have hbS : b ∈ ({a, b} : Finset (Fin N)) := mem_insert_of_mem (mem_singleton_self _)
  have hea : ({a, b} : Finset (Fin N)).erase a ⊆ {b} := by
    intro x hx; simp only [mem_erase, mem_insert, mem_singleton] at hx ⊢; tauto
  have heb : ({a, b} : Finset (Fin N)).erase b ⊆ {a} := by
    intro x hx; simp only [mem_erase, mem_insert, mem_singleton] at hx ⊢; tauto
  have hB0 : 0 < B := (U_pos hz s _ a tc).trans_le hBa
  have hΔB : Δ < B := by linarith [U_pos hz s {a, b} a (flip tc b)]
  have hx : 0 ≤ 1 - Δ / (2 * B) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  obtain ⟨pa, la, sa⟩ := partFactor_boundQ hz s tc _ hbS (cut_cases_pair θ hea haS) hΔ ha hBa
  obtain ⟨pb, lb, sb⟩ := partFactor_boundQ hz s tc _ haS (cut_cases_pair θ heb hbS) hΔ hb hBb
  unfold sysPartCauseProb
  rw [sysCauseProb_eq, prod_pair hab, prod_pair hab]
  refine ⟨mul_pos pa pb, ?_⟩
  rcases exists_cut_pair θ with hc | hc
  · calc _ ≤ _ := mul_le_mul_of_nonneg_right (sa hc) pb.le
      _ ≤ _ := mul_le_mul_of_nonneg_left lb (mul_nonneg hx (pa.le.trans la))
      _ = _ := by ring
  · calc _ ≤ _ := mul_le_mul_of_nonneg_left (sb hc) pa.le
      _ ≤ _ := mul_le_mul_of_nonneg_right la (mul_nonneg hx (pb.le.trans lb))
      _ = _ := by ring

/-- The maximal cause state of a pair has selectivity at least `1/4`. -/
lemma sysBackCause_pair_ge {z : Param N} (hz : z ∈ openCube N) (s tc : State N) {a b : Fin N}
    (hab : a ≠ b) (htc : tc ∈ sysMaxCauseStates (tpmOf z) {a, b} s s) :
    1 / 4 ≤ sysBackCause (tpmOf z) {a, b} s s tc := by
  have hmax := U_prod_max_of_mem hz s tc hab htc
  have hZ := sum_fullProb_pos hz s
  have hcp : ∀ t, 0 < sysCauseProb (tpmOf z) {a, b} s s t := by
    intro t
    rw [sysCauseProb_pair_eq z s t hab]
    have := U_pos hz s {a, b} a t
    have := U_pos hz s {a, b} b t
    positivity
  have hle : ∀ t, sysCauseProb (tpmOf z) {a, b} s s t ≤ sysCauseProb (tpmOf z) {a, b} s s tc := by
    intro t
    rw [sysCauseProb_pair_eq z s t hab, sysCauseProb_pair_eq z s tc hab]
    exact mul_le_mul_of_nonneg_left (hmax t) (by positivity)
  have havg : sysUncCause (tpmOf z) {a, b} s s ≤ sysCauseProb (tpmOf z) {a, b} s s tc := by
    unfold sysUncCause avgOverStates
    rw [div_le_iff₀ (by positivity)]
    calc ∑ t, sysCauseProb (tpmOf z) {a, b} s s t
        ≤ ∑ _t : State N, sysCauseProb (tpmOf z) {a, b} s s tc := sum_le_sum fun t _ => hle t
      _ = _ := by rw [sum_const, card_state, nsmul_eq_mul]; push_cast; ring
  have hunc : 0 < sysUncCause (tpmOf z) {a, b} s s := avg_pos _ hcp
  unfold sysBackCause
  rw [card_pair hab, le_div_iff₀ (by positivity)]
  norm_num
  linarith

/-- **Cause side with a margin.** If every maximiser of `U a · U b` beats its two flips by `Δ`
and all block sums are at most `B`, then `φ_c ≥ Δ / (8B)` at every partition. -/
theorem sysPhiC_pair_ge {z : Param N} (hz : z ∈ openCube N) (s : State N) {a b : Fin N}
    (hab : a ≠ b) {Δ B : ℝ} (hΔ : 0 < Δ) (hB : ∀ i t, U z s {a, b} i t ≤ B)
    (hU : ∀ tc : State N, (∀ t, U z s {a, b} a t * U z s {a, b} b t ≤
        U z s {a, b} a tc * U z s {a, b} b tc) →
      U z s {a, b} a (flip tc b) + Δ ≤ U z s {a, b} a tc ∧
        U z s {a, b} b (flip tc a) + Δ ≤ U z s {a, b} b tc) :
    ∀ tc ∈ sysMaxCauseStates (tpmOf z) {a, b} s s, ∀ θ : SysPartition N {a, b},
      Δ / (8 * B) ≤ sysPhiC (tpmOf z) {a, b} s θ s tc := by
  intro tc htc θ
  obtain ⟨ha, hb⟩ := hU tc (U_prod_max_of_mem hz s tc hab htc)
  obtain ⟨hP, hle⟩ := sysPartCauseProb_le_pair hz s tc hab θ hΔ ha hb (hB a tc) (hB b tc)
  have hB0 : 0 < B := (U_pos hz s {a, b} a tc).trans_le (hB a tc)
  have hΔB : Δ < B := by linarith [hB a tc, U_pos hz s {a, b} a (flip tc b)]
  have hx0 : 0 ≤ Δ / (2 * B) := by positivity
  have hx1 : Δ / (2 * B) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hlog := le_logb_of_le_mul hP hx0 hx1 hle
  have hback := sysBackCause_pair_ge hz s tc hab htc
  have hpos : Δ / (2 * B) ≤ pos (Real.logb 2 (sysCauseProb (tpmOf z) {a, b} s s tc /
      sysPartCauseProb (tpmOf z) {a, b} s θ s tc)) := by
    unfold pos; exact le_max_of_le_right hlog
  unfold sysPhiC
  calc Δ / (8 * B) = 1 / 4 * (Δ / (2 * B)) := by ring
    _ ≤ _ := mul_le_mul hback hpos hx0 (by linarith)

/-! ### The effect side with a margin -/

private lemma effFactor_boundQ {z : Param N} (hz : z ∈ openCube N) (s : State N)
    (M : Finset (Fin N)) {i k : Fin N} (hM : M = ∅ ∨ M = {k}) (h1 : 99 / 100 < z s i)
    (h2 : z (flip s k) i < 11 / 20) :
    0 < effUnit (tpmOf z) Mᶜ s i true ∧ effUnit (tpmOf z) Mᶜ s i true ≤ z s i ∧
      (M.Nonempty → effUnit (tpmOf z) Mᶜ s i true ≤ (1 - 22 / 100) * z s i) := by
  have hlt : z (flip s k) i < z s i := by linarith
  obtain ⟨p0, p1, -⟩ := effFactor_bound hz s M hM hlt
  refine ⟨p0, p1, fun hne => ?_⟩
  rcases hM with rfl | rfl
  · simp at hne
  · rw [effUnit_compl_single, prob_of_mem hz, prob_of_mem hz]
    simp only [↓reduceIte]
    linarith

/-- **Effect side with a margin.** In the effect box, `φ_e ≥ 1/5` at every partition. -/
theorem sysPhiE_pair_ge {z : Param N} (hz : z ∈ openCube N) (s : State N) {a b : Fin N}
    (hab : a ≠ b) (hbox : effBox z s a b) :
    ∀ te ∈ sysMaxEffStates (tpmOf z) {a, b} s s, ∀ θ : SysPartition N {a, b},
      1 / 5 ≤ sysPhiE (tpmOf z) {a, b} s θ s te := by
  intro te hte θ
  obtain ⟨hta, htb⟩ := te_true z hz s hab hbox te hte
  obtain ⟨⟨hsa, -⟩, ⟨hsb, -⟩, hr⟩ := hbox
  have ra := (hr (flip s b) (by simp)).1
  have rb := (hr (flip s a) (by simp)).2
  have haS : a ∈ ({a, b} : Finset (Fin N)) := mem_insert_self _ _
  have hbS : b ∈ ({a, b} : Finset (Fin N)) := mem_insert_of_mem (mem_singleton_self _)
  have hea : ({a, b} : Finset (Fin N)).erase a ⊆ {b} := by
    intro x hx; simp only [mem_erase, mem_insert, mem_singleton] at hx ⊢; tauto
  have heb : ({a, b} : Finset (Fin N)).erase b ⊆ {a} := by
    intro x hx; simp only [mem_erase, mem_insert, mem_singleton] at hx ⊢; tauto
  obtain ⟨pa, la, sa⟩ := effFactor_boundQ hz s _ (cut_cases_pair θ hea haS) hsa ra.2
  obtain ⟨pb, lb, sb⟩ := effFactor_boundQ hz s _ (cut_cases_pair θ heb hbS) hsb rb.2
  have hE : sysEffProb (tpmOf z) {a, b} s s te = z s a * z s b := by
    rw [eff_pair _ hab, hta, htb, prob_of_mem hz, prob_of_mem hz]; simp
  have hP : sysPartEffProb (tpmOf z) {a, b} s θ s te =
      effUnit (tpmOf z) (θ.cutSet (θ.partOf a))ᶜ s a true *
        effUnit (tpmOf z) (θ.cutSet (θ.partOf b))ᶜ s b true := by
    rw [sysPartEffProb, merge_self, prod_pair hab, hta, htb]
  have hle : sysPartEffProb (tpmOf z) {a, b} s θ s te ≤
      (1 - 22 / 100) * sysEffProb (tpmOf z) {a, b} s s te := by
    rw [hE, hP]
    rcases exists_cut_pair θ with hc | hc
    · calc _ ≤ _ := mul_le_mul_of_nonneg_right (sa hc) pb.le
        _ ≤ _ := mul_le_mul_of_nonneg_left lb (by linarith)
        _ = _ := by ring
    · calc _ ≤ _ := mul_le_mul_of_nonneg_left (sb hc) pa.le
        _ ≤ _ := mul_le_mul_of_nonneg_right la (by linarith)
        _ = _ := by ring
  have hP0 : 0 < sysPartEffProb (tpmOf z) {a, b} s θ s te := by rw [hP]; exact mul_pos pa pb
  have hlog := le_logb_of_le_mul hP0 (by norm_num) (by norm_num) hle
  have hE0 : 9801 / 10000 ≤ sysEffProb (tpmOf z) {a, b} s s te := by rw [hE]; nlinarith
  have hpos : 22 / 100 ≤ pos (Real.logb 2 (sysEffProb (tpmOf z) {a, b} s s te /
      sysPartEffProb (tpmOf z) {a, b} s θ s te)) := by
    unfold pos; exact le_max_of_le_right hlog
  unfold sysPhiE
  calc (1 / 5 : ℝ) ≤ 9801 / 10000 * (22 / 100) := by norm_num
    _ ≤ _ := mul_le_mul hE0 hpos (by norm_num) (by linarith)

/-! ### From every partition to `φ_s` -/

/-- A bound at every partition, at one maximal cause state and one maximal effect state,
bounds `φ_s` of the pair from below. -/
lemma le_phi_pair_of {z : Param N} (s : State N) {a b : Fin N} (hab : a ≠ b) {c : ℝ}
    {tc te : State N} (htc : tc ∈ sysMaxCauseStates (tpmOf z) {a, b} s s)
    (hte : te ∈ sysMaxEffStates (tpmOf z) {a, b} s s)
    (h : ∀ θ, c ≤ sysPhiAt (tpmOf z) {a, b} s θ s tc te) : c ≤ phi z s {a, b} := by
  have hS : (({a, b} : Finset (Fin N)).erase a).Nonempty :=
    ⟨b, mem_erase.2 ⟨hab.symm, by simp⟩⟩
  have : Nonempty (SysPartition N {a, b}) := ⟨splitAt (mem_insert_self a {b}) hS⟩
  obtain ⟨θ, hθ⟩ :=
    argminSet_nonempty (fun θ => normalizedSysPhiAt (tpmOf z) {a, b} s θ s tc te)
  have h1 : c ≤ sysPhiOfState (tpmOf z) {a, b} s s tc te := by
    unfold sysPhiOfState sysMipSetAt
    exact (h θ).trans (le_sup'OrZero (f := fun θ => sysPhiAt (tpmOf z) {a, b} s θ s tc te) hθ)
  unfold phi
  exact h1.trans (sysPhiOfState_le_sysPhi _ _ _ _ htc hte)

/-! ### Margins at every maximiser -/

/-- A pair state winning by `Δ` is the restriction of every maximiser of `U a · U b`, and each
flip of a maximiser loses at least `Δ`. -/
lemma hUQ_of_sameArgQ {z : Param N} (hz : z ∈ openCube N) (s : State N) {a b : Fin N}
    (hab : a ≠ b) {Δ : ℝ} (hΔ : 0 < Δ) (h : sameArgQ z s a b Δ) :
    ∀ tc : State N, (∀ t, U z s {a, b} a t * U z s {a, b} b t ≤
        U z s {a, b} a tc * U z s {a, b} b tc) →
      U z s {a, b} a (flip tc b) + Δ ≤ U z s {a, b} a tc ∧
        U z s {a, b} b (flip tc a) + Δ ≤ U z s {a, b} b tc := by
  obtain ⟨t₀, ht₀⟩ := h
  intro tc hmax
  have hpos : ∀ i t, 0 < U z s {a, b} i t := fun i t => U_pos hz s _ i t
  have hagree : tc a = t₀ a ∧ tc b = t₀ b := by
    by_contra hne
    have hne' : tc a ≠ t₀ a ∨ tc b ≠ t₀ b := by tauto
    obtain ⟨h1, h2⟩ := ht₀ tc hne'
    have h1' : U z s {a, b} a tc < U z s {a, b} a t₀ := by linarith
    have h2' : U z s {a, b} b tc < U z s {a, b} b t₀ := by linarith
    have := hmax t₀
    nlinarith [hpos a tc, hpos b tc, hpos a t₀, hpos b t₀, mul_lt_mul'' h1' h2' (hpos a tc).le
      (hpos b tc).le]
  have heq : ∀ i, U z s {a, b} i tc = U z s {a, b} i t₀ := fun i =>
    U_congr z s _ i fun j hj => by
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hagree.1
      · rw [Finset.mem_singleton.mp hj]; exact hagree.2
  refine ⟨?_, ?_⟩
  · rw [heq a]
    refine (ht₀ (flip tc b) (Or.inr ?_)).1
    simp [flip, hagree.2]
  · rw [heq b]
    refine (ht₀ (flip tc a) (Or.inl ?_)).2
    simp [flip, hagree.1]

/-! ### Block sums are at most `2^|S| Z` -/

lemma U_le_Zsum (z : Param N) (s : State N) (S : Finset (Fin N)) (i : Fin N) (t : State N) :
    U z s S i t ≤ 2 ^ S.card * ∑ v : State N, rowProd z s v := by
  rw [U_eq_sum]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun v _ => ?_) (by positivity)
  have h0 : 0 ≤ rowProd z s v := prod_nonneg fun j _ => (tpmOf z).nonneg _ _ _
  have h1 : y z s (merge S t v) i ≤ 1 := (tpmOf z).le_one _ _ _
  nlinarith

/-! ### A good pair has `φ_s ≥ min (1/5) (Δ/64)` -/

/-- **Quantitative good pair.** In the effect box, with a margin `Δ > 0` for the block sums and
`Z ≤ 2`, the pair has `φ_s ≥ min (1/5) (Δ/64)`. -/
theorem phi_pair_ge {z : Param N} (hz : z ∈ openCube N) (s : State N) {a b : Fin N}
    (hab : a ≠ b) (hbox : effBox z s a b) {Δ : ℝ} (hΔ : 0 < Δ) (hsame : sameArgQ z s a b Δ)
    (hZ : ∑ v : State N, rowProd z s v ≤ 2) : min (1 / 5) (Δ / 64) ≤ phi z s {a, b} := by
  obtain ⟨tc, htc⟩ := sysMaxCauseStates_nonempty (tpmOf z) {a, b} s s
  obtain ⟨te, hte⟩ := sysMaxEffStates_nonempty (tpmOf z) {a, b} s s
  have hB : ∀ i t, U z s {a, b} i t ≤ 8 := by
    intro i t
    have := U_le_Zsum z s {a, b} i t
    rw [card_pair hab] at this
    norm_num at this
    linarith
  refine le_phi_pair_of s hab htc hte fun θ => le_min ?_ ?_
  · have h := sysPhiC_pair_ge hz s hab hΔ hB (hUQ_of_sameArgQ hz s hab hΔ hsame) tc htc θ
    rw [show Δ / (8 * 8) = Δ / 64 by norm_num] at h
    exact (min_le_right _ _).trans h
  · exact (min_le_left _ _).trans (sysPhiE_pair_ge hz s hab hbox te hte θ)

/-! ### Reduction -/

/-- No pair reaches `η σ_N`. -/
def noGoodPair (N : ℕ) (s : State N) (η : ℝ) : Set (Param N) :=
  {z | z ∈ cube N ∧ ∀ a b : Fin N, a ≠ b → phi z s {a, b} < η * sigN N}

/-- The Bayes normaliser exceeds `2`. -/
def Zbad (N : ℕ) (s : State N) : Set (Param N) :=
  {z | z ∈ cube N ∧ 2 < ∑ v : State N, rowProd z s v}

private lemma sigN_pos' (N : ℕ) : 0 < sigN N := Real.sqrt_pos.mpr (by positivity)

private lemma sigN_le_one' (N : ℕ) : sigN N ≤ 1 :=
  Real.sqrt_le_one.mpr (pow_le_one₀ (by norm_num) (by norm_num))

/-- **Reduction.** "No pair reaches `σ_N / 128`" is contained in the null boundary of the cube,
"all of the first `L` pairs are bad at the margin `σ_N / 2`", and "`Z > 2`". -/
lemma noGoodPair_subset (L : ℕ) (s : State N) :
    noGoodPair N s (1 / 128) ⊆ (cube N \ openCube N) ∪ allBadQ N L s ∪ Zbad N s := by
  rintro z ⟨hz, hlt⟩
  by_cases ho : z ∈ openCube N
  swap
  · exact Or.inl (Or.inl ⟨hz, ho⟩)
  by_cases hZ : 2 < ∑ v : State N, rowProd z s v
  · exact Or.inr ⟨hz, hZ⟩
  refine Or.inl (Or.inr ⟨hz, fun k hk _ hgood => ?_⟩)
  have hab : pa N k hk ≠ pb N k hk := by simp [pa, pb, Fin.ext_iff]
  have hσ := sigN_pos' N
  have hσ1 := sigN_le_one' N
  have hge := phi_pair_ge ho s hab hgood.1 (by positivity) hgood.2 (not_lt.mp hZ)
  have h1 := hlt _ _ hab
  have : sigN N / 128 ≤ min (1 / 5) (sigN N / 2 / 64) := le_min (by linarith) (by linarith)
  linarith

/-! ### `Z ≤ 2` with probability tending to one (Chebyshev) -/

section Cheb

private lemma integral_pi_eval' {I E : Type*} [Fintype I] [MeasurableSpace E] (μ0 : Measure E)
    [IsProbabilityMeasure μ0] {g : E → ℝ} (hg : AEStronglyMeasurable g μ0) (a : I) :
    ∫ x, g (x a) ∂(Measure.pi fun _ : I => μ0) = ∫ y, g y ∂μ0 := by
  have hmp := measurePreserving_eval (fun _ : I => μ0) a
  have hg' : AEStronglyMeasurable g ((Measure.pi fun _ : I => μ0).map (Function.eval a)) := by
    rw [hmp.map_eq]; exact hg
  rw [← integral_map hmp.measurable.aemeasurable hg', hmp.map_eq]

private lemma memLp_row' {g : (Fin N → ℝ) → ℝ} (hg : Measurable g) (hb : ∀ v, |g v| ≤ 1)
    (r : State N) : MemLp (fun w : Param N => g (w r)) 2 (cubeM N) :=
  MemLp.of_bound (hg.comp (measurable_pi_apply r)).aestronglyMeasurable 1
    (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hb (w r))

private lemma cheb_rows' {g : (Fin N → ℝ) → ℝ} (hg : Measurable g) (hb : ∀ v, |g v| ≤ 1)
    {c : ℝ} (hc : 0 < c) :
    cubeM N {w | c ≤ |∑ r, g (w r) - 2 ^ N * ∫ v, g v ∂rowM N|} ≤
      ENNReal.ofReal (2 ^ N * (∫ v, g v ^ 2 ∂rowM N) / c ^ 2) := by
  have hmem : MemLp (fun w : Param N => ∑ r, g (w r)) 2 (cubeM N) :=
    memLp_finsetSum _ fun r _ => memLp_row' hg hb r
  have h := meas_ge_le_variance_div_sq hmem hc
  have hE : (∫ w, (fun w : Param N => ∑ r, g (w r)) w ∂cubeM N) = 2 ^ N * ∫ v, g v ∂rowM N := by
    have hrow : ∀ r : State N, ∫ w, g (w r) ∂cubeM N = ∫ v, g v ∂rowM N := fun r =>
      integral_pi_eval' (rowM N) hg.aestronglyMeasurable r
    rw [integral_finsetSum _ fun r _ => (memLp_row' hg hb r).integrable one_le_two,
      sum_congr rfl fun r _ => hrow r, sum_const,
      card_state, nsmul_eq_mul]
    push_cast; ring
  rw [hE] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  gcongr
  have hind : iIndepFun (fun r (w : Param N) => g (w r)) (cubeM N) := by
    unfold cubeM
    exact iIndepFun_pi (X := fun _ => g) fun r => hg.aemeasurable
  have hsum : (fun w : Param N => ∑ r, g (w r)) = ∑ r, fun w : Param N => g (w r) := by
    funext w; simp [Finset.sum_apply]
  rw [hsum, IndepFun.variance_sum (fun r _ => memLp_row' hg hb r)
    (fun r _ r' _ hrr => hind.indepFun hrr)]
  calc ∑ r, variance (fun w : Param N => g (w r)) (cubeM N)
      ≤ ∑ _r : State N, ∫ v, g v ^ 2 ∂rowM N := by
        refine sum_le_sum fun r _ => ?_
        refine (variance_le_expectation_sq (memLp_row' hg hb r).aestronglyMeasurable).trans_eq ?_
        exact integral_pi_eval' (rowM N) (g := fun v => g v ^ 2)
          (hg.pow_const 2).aestronglyMeasurable r
    _ = _ := by rw [sum_const, card_state, nsmul_eq_mul]; push_cast; ring

/-- In flipped coordinates, `Z > 2` has probability at most `(2/3)^N`. -/
lemma cubeM_Zs_gt : cubeM N {w | 2 < Zs w} ≤ ENNReal.ofReal ((2 / 3 : ℝ) ^ N) := by
  have hmeas : Measurable fun v : Fin N → ℝ => ∏ j, clamp01 (v j) :=
    Finset.measurable_prod _ fun j _ => measurable_clamp01.comp (measurable_pi_apply j)
  have hb : ∀ v : Fin N → ℝ, |∏ j, clamp01 (v j)| ≤ 1 := fun v => by
    rw [abs_of_nonneg (prod_nonneg fun _ _ => clamp01_nonneg _)]
    exact prod_le_one (fun _ _ => clamp01_nonneg _) fun _ _ => clamp01_le_one _
  have hpow : ∀ p : ℕ, ∫ v, (∏ j, clamp01 (v j)) ^ p ∂rowM N = (1 / ((p : ℝ) + 1)) ^ N := by
    intro p
    simp_rw [← prod_pow]
    rw [rowM, integral_monomial (fun _ : Fin N => p), prod_const, card_univ, Fintype.card_fin]
  have hmean : (2 : ℝ) ^ N * ∫ v, ∏ j, clamp01 (v j) ∂rowM N = 1 := by
    have := hpow 1
    simp only [pow_one] at this
    rw [this, ← mul_pow]; norm_num
  have hsub : {w : Param N | 2 < Zs w} ⊆
      {w | 1 ≤ |∑ r, (fun v : Fin N → ℝ => ∏ j, clamp01 (v j)) (w r) -
        2 ^ N * ∫ v, ∏ j, clamp01 (v j) ∂rowM N|} := by
    intro w hw
    simp only [Set.mem_setOf_eq] at hw ⊢
    rw [hmean]
    change 1 ≤ |Zs w - 1|
    rw [abs_of_pos (by linarith)]; linarith
  refine (measure_mono hsub).trans ((cheb_rows' hmeas hb one_pos).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  rw [hpow 2, ← mul_pow]; norm_num

end Cheb

lemma volume_Zbad_le (s : State N) : volume (Zbad N s) ≤ ENNReal.ofReal ((2 / 3 : ℝ) ^ N) := by
  have hsub : Zbad N s ⊆ flipE s ⁻¹' (cube N ∩ {w | 2 < Zs w}) := by
    rintro z ⟨hz, hZ⟩
    refine ⟨flipP_cube hz s, ?_⟩
    show 2 < Zs (flipP s z)
    have : ∑ v : State N, rowProd z s v = Zs (flipP s z) := by
      unfold Zs; exact sum_congr rfl fun v _ => rowProd_eq_Pw z s v
    rwa [← this]
  calc volume (Zbad N s) ≤ volume (flipE s ⁻¹' (cube N ∩ {w | 2 < Zs w})) := measure_mono hsub
    _ = cubeM N {w | 2 < Zs w} := by
        rw [(mp_flipE s).measure_preimage_equiv, volume_cube_inter]
    _ ≤ _ := cubeM_Zs_gt

/-! ### The limit -/

/-- **Quantitative pair step.** With probability tending to one, some pair has
`φ_s ≥ σ_N / 128`, for any choice of current state `s N`. -/
theorem tendsto_noGoodPair (s : ∀ N, State N) :
    Tendsto (fun N => volume (noGoodPair N (s N) (1 / 128))) atTop (𝓝 0) := by
  obtain ⟨p, hp0, hp1, hlim⟩ := PQ.limsup_allBadQ s
  have hZ : Tendsto (fun N => volume (Zbad N (s N))) atTop (𝓝 0) := by
    have h : Tendsto (fun N : ℕ => ENNReal.ofReal ((2 / 3 : ℝ) ^ N)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
      fun N => volume_Zbad_le (s N)
  have hsub : ∀ L N, volume (noGoodPair N (s N) (1 / 128)) ≤
      volume (allBadQ N L (s N)) + volume (Zbad N (s N)) := by
    intro L N
    calc volume (noGoodPair N (s N) (1 / 128))
        ≤ volume ((cube N \ openCube N) ∪ allBadQ N L (s N) ∪ Zbad N (s N)) :=
          measure_mono (noGoodPair_subset L (s N))
      _ ≤ volume (cube N \ openCube N) + volume (allBadQ N L (s N)) + volume (Zbad N (s N)) :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ = _ := by rw [volume_cube_diff_openCube, zero_add]
  have hbound : ∀ L, limsup (fun N => volume (noGoodPair N (s N) (1 / 128))) atTop ≤
      ENNReal.ofReal ((1 - p) ^ L) := by
    intro L
    calc limsup (fun N => volume (noGoodPair N (s N) (1 / 128))) atTop
        ≤ limsup ((fun N => volume (allBadQ N L (s N))) + fun N => volume (Zbad N (s N)))
            atTop := limsup_le_limsup (Eventually.of_forall fun N => hsub L N)
      _ ≤ limsup (fun N => volume (allBadQ N L (s N))) atTop +
            limsup (fun N => volume (Zbad N (s N))) atTop := PQ.limsup_add_le_nat _ _
      _ ≤ ENNReal.ofReal ((1 - p) ^ L) + 0 := add_le_add (hlim L) hZ.limsup_eq.le
      _ = _ := add_zero _
  have hgeom : Tendsto (fun L : ℕ => ENNReal.ofReal ((1 - p) ^ L)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith))
  have hls : limsup (fun N => volume (noGoodPair N (s N) (1 / 128))) atTop ≤ 0 :=
    ge_of_tendsto' hgeom hbound
  exact tendsto_of_le_liminf_of_limsup_le (zero_le.trans (le_liminf_of_le (by isBoundedDefault)
    (Eventually.of_forall fun _ => zero_le))) hls

end Census
end IIT
