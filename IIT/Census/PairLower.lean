/-
Census of complexes: the winning pair has `φ_s ≥ cstar · sqrt (log N) · σ_N`.

Let `S = {a, b}` and `w = flipP s z`.  The block sums of the pair are `U_i(t) = 4 Num_i(t)`.  If the
pattern `(false, false)` beats every other pattern of the pair by `2 y σ_N` in both numerators
(`inA`), every maximal cause state agrees with that pattern on the pair and each flip of it lowers
the block sum by `Δ = 8 y σ_N`.  On the good event every numerator of a pair is at most
`aPair + 1/100`, so a cut lowers the cause probability by the factor `1 - x` with
`x ≥ y σ_N / (aPair + 1/100)`, and `log₂ (1 / (1 - x)) ≥ x / ln 2`.  With the selectivity bound
`1/4`, the cause side is at least `y σ_N / (4 (aPair + 1/100) ln 2) ≥ cstar sqrt (log N) σ_N`; the
effect side is at least `1/5` in the effect box.
-/
import IIT.Census.PairQuant
import IIT.Census.BigPhiDet
import IIT.Census.TightStats

namespace IIT
namespace Census

open Finset Filter Topology

variable {N : ℕ}

/-! ### A sharp lower bound for `log₂` -/

private lemma pl_div_log_le_logb {p q x : ℝ} (hp : 0 < p) (hx1 : x < 1)
    (h : p ≤ (1 - x) * q) : x / Real.log 2 ≤ Real.logb 2 (q / p) := by
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
  rw [Real.logb]
  exact div_le_div_of_nonneg_right (hl1.trans hl2) hlog2.le

/-! ### The cause side of a pair with the sharp logarithm -/

private lemma pl_partFactor_boundQ {z : Param N} (hz : z ∈ openCube N) (s t : State N)
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
    have hU1 := U_pos hz s S j t
    have hB0 : 0 < B := hU1.trans_le hB
    have key : (U z s S j t + U z s S j (flip t k)) / 2 ≤ (1 - Δ / (2 * B)) * U z s S j t := by
      have h2 : Δ / (2 * B) * U z s S j t ≤ Δ / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      nlinarith
    have hD : 0 < (∑ v : State N, fullProb (tpmOf z) v s) * (2 : ℝ) ^ S.card := by
      have := sum_fullProb_pos hz s
      positivity
    rw [hF]
    calc (U z s S j t + U z s S j (flip t k)) / 2 / (∑ v : State N, fullProb (tpmOf z) v s)
          / (2 : ℝ) ^ S.card
        = ((U z s S j t + U z s S j (flip t k)) / 2) /
            ((∑ v : State N, fullProb (tpmOf z) v s) * (2 : ℝ) ^ S.card) := by ring
      _ ≤ ((1 - Δ / (2 * B)) * U z s S j t) /
            ((∑ v : State N, fullProb (tpmOf z) v s) * (2 : ℝ) ^ S.card) :=
          div_le_div_of_nonneg_right key hD.le
      _ = (1 - Δ / (2 * B)) * C := by simp only [C]; ring

private lemma pl_sysPartCauseProb_le_pair {z : Param N} (hz : z ∈ openCube N) (s tc : State N)
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
  obtain ⟨pa, la, sa⟩ :=
    pl_partFactor_boundQ hz s tc _ hbS (cut_cases_pair θ hea haS) hΔ ha hBa
  obtain ⟨pb, lb, sb⟩ :=
    pl_partFactor_boundQ hz s tc _ haS (cut_cases_pair θ heb hbS) hΔ hb hBb
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

/-- **Sharp cause side of a pair.** If every maximiser of `U a · U b` beats its two flips by `Δ`
and the block sums of `a` and `b` are at most `B`, then `φ_c ≥ Δ / (8 B ln 2)` at every
partition. -/
theorem sysPhiC_pair_ge_log {z : Param N} (hz : z ∈ openCube N) (s : State N) {a b : Fin N}
    (hab : a ≠ b) {Δ B : ℝ} (hΔ : 0 < Δ) (hBa : ∀ t, U z s {a, b} a t ≤ B)
    (hBb : ∀ t, U z s {a, b} b t ≤ B)
    (hU : ∀ tc : State N, (∀ t, U z s {a, b} a t * U z s {a, b} b t ≤
        U z s {a, b} a tc * U z s {a, b} b tc) →
      U z s {a, b} a (flip tc b) + Δ ≤ U z s {a, b} a tc ∧
        U z s {a, b} b (flip tc a) + Δ ≤ U z s {a, b} b tc) :
    ∀ tc ∈ sysMaxCauseStates (tpmOf z) {a, b} s s, ∀ θ : SysPartition N {a, b},
      Δ / (8 * B * Real.log 2) ≤ sysPhiC (tpmOf z) {a, b} s θ s tc := by
  intro tc htc θ
  obtain ⟨ha, hb⟩ := hU tc (U_prod_max_of_mem hz s tc hab htc)
  obtain ⟨hP, hle⟩ := pl_sysPartCauseProb_le_pair hz s tc hab θ hΔ ha hb (hBa tc) (hBb tc)
  have hB0 : 0 < B := (U_pos hz s {a, b} a tc).trans_le (hBa tc)
  have hΔB : Δ < B := by linarith [hBa tc, U_pos hz s {a, b} a (flip tc b)]
  have hx0 : 0 ≤ Δ / (2 * B) := by positivity
  have hx1 : Δ / (2 * B) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hlog := pl_div_log_le_logb hP hx1 hle
  have hback := sysBackCause_pair_ge hz s tc hab htc
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpos : Δ / (2 * B) / Real.log 2 ≤ pos (Real.logb 2 (sysCauseProb (tpmOf z) {a, b} s s tc /
      sysPartCauseProb (tpmOf z) {a, b} s θ s tc)) := by
    unfold pos; exact le_max_of_le_right hlog
  unfold sysPhiC
  calc Δ / (8 * B * Real.log 2) = 1 / 4 * (Δ / (2 * B) / Real.log 2) := by
        field_simp; ring
    _ ≤ _ := mul_le_mul hback hpos (by positivity) (by linarith)

/-! ### Block sums and numerators -/

/-- The block sum of a unit is `2^|S|` times its conditioned cause numerator with the full purview. -/
lemma U_eq_two_pow_mul_Num {z : Param N} (hz : z ∈ openCube N) (s : State N)
    (S : Finset (Fin N)) (i : Fin N) (t : State N) :
    U z s S i t = 2 ^ S.card * Num (flipP s z) S S t i := by
  have h1 := partFactor_univ z s t S i
  have h2 := condFactor_eq z s (subset_refl S) t i
  simp only [condSet, condState, union_compl] at h2
  rw [h2, sum_fullProb_eq_Zs] at h1
  have hZ := Zs_pos hz s
  have h2p : (0 : ℝ) < 2 ^ S.card := by positivity
  field_simp at h1
  linarith

/-- On the good event, every conditioned cause numerator of a pair is at most
`13/24 + 22 N σ_N + dsmall N 2`. -/
lemma Num_pair_le {s : State N} {w : Param N} (hG : GoodW N s w) (hZ : gZ N w) (hN : 1 ≤ N)
    {S : Finset (Fin N)} (hS : S.card = 2) {i : Fin N} (hi : i ∈ S) (t : State N) :
    Num w S S t i ≤ 13 / 24 + 22 * N * sigN N + dsmall N 2 := by
  have h1 := dev_le_dsmall hG hN hi (subset_refl S) t
  rw [hS] at h1
  have h2 := hG.g11 i
  have h3 : |Zs w - 1| ≤ 16 * N * sigN N := hZ
  have h4 := subSum_S_le hG i (S := S) (by omega) t
  rw [hS] at h4
  norm_num at h4
  have h5 := E6_le 2 hN
  have hc : cNum w S S t i = ZQ w i / 4 + subSum w i S t / 12 := by
    unfold cNum; simp
  have hσ : 0 ≤ (N : ℝ) * sigN N := mul_nonneg (Nat.cast_nonneg _) (sigN_pos N).le
  rw [abs_le] at h1 h2 h3
  rw [hc] at h1
  nlinarith

/-! ### Eventual smallness -/

lemma ev_pair_level : ∀ᶠ N : ℕ in atTop, 22 * (N : ℝ) * sigN N + dsmall N 2 ≤ 1 / 100 := by
  filter_upwards [eventually_ge_atTop 1,
    ev_poly_geom 7 vkRate_pos.le vkRate_lt_one 1024 one_pos,
    ev_poly_geom 2 (r := 2 / 3) (by norm_num) (by norm_num) 400 (by norm_num : (0 : ℝ) < 2.5e-5),
    ev_pow_mul_sigN 1 (C := 22) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 200)]
    with N hN hρ h400 h22
  have hk : 2 ≤ KN N := by unfold KN; omega
  have hV := Vbd_le_seven hN hk hρ
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg hN'
  have hl1 : Real.log N ≤ N := Real.log_le_self (by positivity)
  have hL0 := LkN_nonneg' 2 hN
  have hL : LkN N 2 ≤ 10 * (N : ℝ) ^ 2 := by
    unfold LkN; push_cast; nlinarith
  have hds : dsmall N 2 ≤ 1 / 200 := by
    unfold dsmall
    apply mul_sqrt_le_of_sq (by norm_num) (by norm_num)
    have hs : 0 ≤ sigN N ^ 2 := by positivity
    have := Vbd_nonneg N 2
    calc (2 : ℝ) ^ 2 * (LkN N 2 * Vbd N 2) ≤ 4 * (10 * (N : ℝ) ^ 2 * (7 * sigN N ^ 2)) := by
          norm_num; gcongr
      _ = 280 * (N : ℝ) ^ 2 * (2 / 3 : ℝ) ^ N := by rw [sigN_sq]; ring
      _ ≤ (1 / 200) ^ 2 := by
          have : 0 ≤ (N : ℝ) ^ 2 * (2 / 3 : ℝ) ^ N := by positivity
          nlinarith
  have : 22 * (N : ℝ) * sigN N = 22 * (N : ℝ) ^ 1 * sigN N := by ring
  rw [this]; linarith

lemma ev_target_le_fifth : ∀ᶠ N : ℕ in atTop, cstar * Real.sqrt (Real.log N) * sigN N ≤ 1 / 5 := by
  filter_upwards [eventually_ge_atTop 1,
    ev_pow_mul_sigN 1 (C := 1) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 5)] with N hN h1
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl1 : Real.log N ≤ (N : ℝ) ^ 2 := by
    nlinarith [Real.log_le_self (by positivity : (0 : ℝ) ≤ N)]
  have hsq : Real.sqrt (Real.log N) ≤ N := by
    calc Real.sqrt (Real.log N) ≤ Real.sqrt ((N : ℝ) ^ 2) := Real.sqrt_le_sqrt hl1
      _ = N := Real.sqrt_sq (by positivity)
  have hσ := (sigN_pos N).le
  have hs0 := Real.sqrt_nonneg (Real.log N)
  simp only [one_mul, pow_one] at h1
  have : cstar * Real.sqrt (Real.log N) * sigN N ≤ (N : ℝ) * sigN N := by
    unfold cstar
    have : Real.sqrt (Real.log N) * sigN N ≤ (N : ℝ) * sigN N :=
      mul_le_mul_of_nonneg_right hsq hσ
    nlinarith [mul_nonneg hs0 hσ]
  linarith

/-- The constant comparison `gamT / (4 (aPair + 1/100) ln 2) ≥ cstar`. -/
lemma cstar_le_pair_const : cstar * (4 * (aPair + 1 / 100) * Real.log 2) ≤ gamT := by
  have := Real.log_two_lt_d9
  unfold cstar aPair gamT
  norm_num at this ⊢
  linarith

/-! ### The winning pair -/

/-- **The winning pair.** Eventually, on the good event, in the effect box and in the orthant
`inA` at level `yN N`, the pair has `φ_s ≥ cstar · sqrt (log N) · σ_N`. -/
theorem eventually_pair_lower : ∀ᶠ N in atTop, ∀ (s : State N) (z : Param N) (a b : Fin N),
    z ∈ openCube N → GoodW N s (flipP s z) → gZ N (flipP s z) → a ≠ b → effBox z s a b →
    inA (flipP s z) a b (yN N) → cstar * Real.sqrt (Real.log N) * sigN N ≤ phi z s {a, b} := by
  filter_upwards [eventually_ge_atTop 2, ev_pair_level, ev_target_le_fifth]
    with N hN hlev hfifth
  intro s z a b hz hG hZ hab hbox hA
  have hN1 : 1 ≤ N := by omega
  have hσ := sigN_pos N
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hy : 0 < yN N := mul_pos gamT_pos (Real.sqrt_pos.mpr hlogN)
  have hΔ : 0 < 8 * yN N * sigN N := by positivity
  have hS2 : ({a, b} : Finset (Fin N)).card = 2 := card_pair hab
  have hUN : ∀ i t, U z s {a, b} i t = 4 * Num (flipP s z) {a, b} {a, b} t i := by
    intro i t; rw [U_eq_two_pow_mul_Num hz, hS2]; norm_num
  have hB : ∀ i ∈ ({a, b} : Finset (Fin N)), ∀ t,
      U z s {a, b} i t ≤ 4 * (aPair + 1 / 100) := by
    intro i hi t
    rw [hUN]
    have := Num_pair_le hG hZ hN1 hS2 hi t
    unfold aPair
    linarith
  have haS : a ∈ ({a, b} : Finset (Fin N)) := mem_insert_self _ _
  have hbS : b ∈ ({a, b} : Finset (Fin N)) := mem_insert_of_mem (mem_singleton_self _)
  have hsame : sameArgQ z s a b (8 * yN N * sigN N) := by
    refine ⟨pat a b false false, fun t ht => ?_⟩
    have hne : (t a, t b) ≠ (false, false) := by
      intro h
      simp only [Prod.mk.injEq] at h
      rcases ht with h1 | h1
      · exact h1 (by simp [pat, h.1])
      · exact h1 (by simp [pat, h.2])
    have key : ∀ i ∈ ({a, b} : Finset (Fin N)),
        U z s {a, b} i t + 8 * yN N * sigN N ≤ U z s {a, b} i (pat a b false false) := by
      intro i hi
      have he := hA i hi (t a) (t b) hne
      unfold etaP at he
      rw [div_le_iff₀ hσ] at he
      have hc : U z s {a, b} i t = U z s {a, b} i (pat a b (t a) (t b)) :=
        U_congr z s _ i fun j hj => by
          rcases mem_insert.mp hj with h | h
          · rw [h]; simp [pat]
          · rw [mem_singleton.mp h]; simp [pat, hab.symm]
      rw [hc, hUN, hUN]
      linarith
    exact ⟨key a haS, key b hbS⟩
  obtain ⟨tc, htc⟩ := sysMaxCauseStates_nonempty (tpmOf z) {a, b} s s
  obtain ⟨te, hte⟩ := sysMaxEffStates_nonempty (tpmOf z) {a, b} s s
  have hC := sysPhiC_pair_ge_log hz s hab hΔ (hB a haS) (hB b hbS)
    (hUQ_of_sameArgQ hz s hab hΔ hsame) tc htc
  have harith : cstar * Real.sqrt (Real.log N) * sigN N ≤
      8 * yN N * sigN N / (8 * (4 * (aPair + 1 / 100)) * Real.log 2) := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hK : 0 < 4 * (aPair + 1 / 100) * Real.log 2 := by
      unfold aPair; positivity
    rw [le_div_iff₀ (by unfold aPair; positivity)]
    have hc := cstar_le_pair_const
    have hs0 : 0 ≤ Real.sqrt (Real.log N) * sigN N := by positivity
    unfold yN
    nlinarith [mul_le_mul_of_nonneg_right hc hs0]
  refine le_phi_pair_of s hab htc hte fun θ => le_min ?_ ?_
  · exact harith.trans (hC θ)
  · exact hfifth.trans (sysPhiE_pair_ge hz s hab hbox te hte θ)

end Census
end IIT
