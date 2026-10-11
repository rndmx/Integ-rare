/-
Census, B1 lower bound, leaf `phi_univ_ge_EX` (W7 §3 items 2, 3, 5): the DETERMINISTIC part.

`univ_lower_det`: on a configuration `w` where
* the fixed rows satisfy the facts read off `EX`/`EXFacts` (row `r0 ≥ f`, row `s` away from `1/2`,
  checks L, V, M0),
* `r0` is the strict row-product maximiser,
* `Z ≥ 1/2`, `te = teW w s` is a maximal effect state of `univ`,
* subcube concentration holds on both sides for cuts of size `≥ D`, and
* the truncated small-cut sums exceed `8 D` (cause side for `K ≠ {x}`, effect side for all `K`),
we have `P(r0)/Z · N / 10⁶ ≤ φ_s(univ)`.

Route: `phi_lower_fail` (W3 Thm 6.1 / Lemma G') with the comparison partition `uxTheta` (check V puts
the MIP in `𝓕_x`), the cause value from check M0, the effect value from the small-cut sum at `{x}`
and the link `e ≥ N³ P(r0)` (check L).
-/
import IIT.Census.B1UnivAux

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-! ### Small tools -/

/-- The smallest entry of a row (`1` for `N = 0`). -/
noncomputable def rowMinU (v : Fin N → ℝ) : ℝ :=
  if h : (univ : Finset (Fin N)).Nonempty then univ.inf' h v else 1

lemma rowMinU_le (v : Fin N → ℝ) (j : Fin N) : rowMinU v ≤ v j := by
  unfold rowMinU
  rw [dif_pos ⟨j, mem_univ j⟩]
  exact inf'_le _ (mem_univ j)

lemma exists_le_rowMinU (v : Fin N → ℝ) (hN : 0 < N) : ∃ k, v k ≤ rowMinU v := by
  have hne : (univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, mem_univ _⟩
  obtain ⟨k, -, hk⟩ := exists_mem_eq_inf' hne v
  refine ⟨k, ?_⟩
  unfold rowMinU
  rw [dif_pos hne, hk]

lemma le_rowMinU {v : Fin N → ℝ} {a : ℝ} (h : ∀ j, a ≤ v j) (hN : 0 < N) : a ≤ rowMinU v := by
  obtain ⟨k, hk⟩ := exists_le_rowMinU v hN
  exact (h k).trans hk

lemma two_mul_le_cube {n : ℝ} (h : 2 ≤ n) : 2 * n ≤ n ^ 3 := by
  have h1 : 4 ≤ n * n := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ n)
  have h3 : n ^ 3 = n * (n * n) := by ring
  linarith

lemma logb_mul_log2 (t : ℝ) : Real.logb 2 t * Real.log 2 = Real.log t := by
  rw [Real.logb, div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne']

/-- A full-cut value with top entry `≥ 1/2 + 10⁻⁵` and half-mean `≤ 1/2 + 10⁻⁷` is `≥ 10⁻⁵`. -/
lemma logb_lb_e5 {a b : ℝ} (ha : 1 / 2 + 1 / 10 ^ 5 ≤ a) (hb0 : 0 < b) (hb : b ≤ 1 / 2 + 1 / 10 ^ 7) :
    1 / 10 ^ 5 ≤ Real.logb 2 (a / b) := by
  have ha0 : 0 < a := by linarith
  have ht : 0 < a / b := div_pos ha0 hb0
  have h1 := Real.one_sub_inv_le_log_of_pos ht
  rw [inv_div] at h1
  have h2 : b / a ≤ (1 / 2 + 1 / 10 ^ 7) / (1 / 2 + 1 / 10 ^ 5) :=
    div_le_div₀ (by norm_num) hb (by norm_num) ha
  have hlog : (19 / 10 ^ 6 : ℝ) ≤ Real.log (a / b) := by
    have : (1 / 2 + 1 / 10 ^ 7 : ℝ) / (1 / 2 + 1 / 10 ^ 5) ≤ 1 - 19 / 10 ^ 6 := by norm_num
    linarith
  have hl2 := Real.log_pos one_lt_two
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  rw [Real.logb, le_div_iff₀ hl2]
  nlinarith

/-- `ln (2y/(y+U)) ≥ -1/2` for `y ≥ 1/2`, `U ≤ 1`. -/
lemma lam_lb {y U : ℝ} (hy : 1 / 2 ≤ y) (hU0 : 0 ≤ U) (hU : U ≤ 1) :
    -(1 / 2 : ℝ) ≤ Real.log (2 * y / (y + U)) := by
  have hyU : 0 < y + U := by linarith
  have ht : 0 < 2 * y / (y + U) := div_pos (by linarith) hyU
  have h1 := Real.one_sub_inv_le_log_of_pos ht
  rw [inv_div] at h1
  have : (y + U) / (2 * y) ≤ 3 / 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-- The full-cut gap: `ln (y/A) - ln (y_k/A_k) ≤ ln (y/f) + 5δ`. -/
lemma log_gap_le {y yk A Ak δ f : ℝ} (hf : 0 < f) (hfy : f ≤ yk) (hy0 : 0 < y) (hδ : 0 ≤ δ)
    (hδs : δ ≤ 1 / 100) (hA : 1 / 2 - δ ≤ A) (hAk0 : 0 < Ak) (hAk : Ak ≤ 1 / 2 + δ) :
    Real.log (y / A) - Real.log (yk / Ak) ≤ Real.log (y / f) + 5 * δ := by
  have hA0 : 0 < A := by linarith
  have hyk0 : 0 < yk := by linarith
  have a1 : Real.log (y / A) ≤ Real.log (y / (1 / 2 - δ)) :=
    Real.log_le_log (div_pos hy0 hA0) (div_le_div_of_nonneg_left hy0.le (by linarith) hA)
  have a2 : Real.log (f / (1 / 2 + δ)) ≤ Real.log (yk / Ak) :=
    Real.log_le_log (div_pos hf (by linarith)) (div_le_div₀ hyk0.le hfy hAk0 hAk)
  have a3 : Real.log (y / (1 / 2 - δ)) - Real.log (f / (1 / 2 + δ)) =
      Real.log (y / f) + Real.log ((1 / 2 + δ) / (1 / 2 - δ)) := by
    have h1 : (1 / 2 - δ) ≠ 0 := by linarith
    have h2 : (1 / 2 + δ) ≠ 0 := by linarith
    rw [← Real.log_div (by positivity) (by positivity), ← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have a4 : Real.log ((1 / 2 + δ) / (1 / 2 - δ)) ≤ 5 * δ := by
    refine (Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))).trans ?_
    rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- `ln (y/A) ≥ ln (2y) - 2δ` when `A ≤ 1/2 + δ`. -/
lemma log_kF_ge {y A δ : ℝ} (hy0 : 0 < y) (hA0 : 0 < A) (hA : A ≤ 1 / 2 + δ) (hδ : 0 ≤ δ) :
    Real.log (2 * y) - 2 * δ ≤ Real.log (y / A) := by
  have h1 : Real.log (y / (1 / 2 + δ)) ≤ Real.log (y / A) :=
    Real.log_le_log (div_pos hy0 (by linarith)) (div_le_div_of_nonneg_left hy0.le hA0 hA)
  have h2 : Real.log (y / (1 / 2 + δ)) = Real.log (2 * y) - Real.log (1 + 2 * δ) := by
    have h3 : (1 / 2 + δ) ≠ 0 := by linarith
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1; field_simp
  have h3 : Real.log (1 + 2 * δ) ≤ 2 * δ := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 2 * δ by linarith); linarith
  linarith

lemma sysPhiOfState_le_phi {z : Param N} {s tc te : State N}
    (hc : tc ∈ sysMaxCauseStates (tpmOf z) univ s s) (he : te ∈ sysMaxEffStates (tpmOf z) univ s s) :
    sysPhiOfState (tpmOf z) univ s s tc te ≤ phi z s univ := by
  unfold phi sysPhi
  exact le_sup'OrZero (b := (tc, te)) (f := fun p : State N × State N => sysPhiOfState (tpmOf z) univ s s p.1 p.2)
    (mem_product.2 ⟨hc, he⟩)

/-! ### The deterministic lower bound -/

/-- **`φ_s(univ) ≥ β N / 10⁶` from the deterministic facts.** -/
theorem univ_lower_det {s r0 : State N} {x : Fin N} {w : Param N} {δ : ℕ → ℝ} {D dstar : ℕ}
    (hw : w ∈ openCube N) (hN2 : 2 ≤ N) (hNbig : (10 : ℝ) ^ 7 ≤ N)
    (hδ0 : ∀ d, 0 ≤ δ d) (hδs : δ (N - 1) ≤ 1 / 10 ^ 8)
    (hδanti : ∀ d d', D ≤ d → d ≤ d' → δ d' ≤ δ d)
    (hD : 2 ≤ D) (hDN : D ≤ N - 1) (hDd : 2 * D ≤ dstar) (hdD : dstar ≤ 7 * D)
    (hNδD : (N : ℝ) * δ D ≤ 1 / 100) (hNδ : (N : ℝ) * δ (N - 1) ≤ 1 / 100)
    (hBfar : ∀ d, dstar ≤ d → d + 2 ≤ N → (N : ℝ) * (δ d + δ (N - 1)) ≤ 1 / 10 ^ 6)
    (hy : ∀ j, (1001 / 2000 : ℝ) ≤ clamp01 (w r0 j))
    (hxs : ∀ k, (1 / 2 + 1 / 100000 : ℝ) ≤ xE w s k)
    (hstrict : ∀ r, r ≠ r0 → Pw w r < Pw w r0)
    (hL : ∑ k, -Real.log (xE w s k) ≤ XW w r0 - 3 * Real.log N)
    (hV : ∑ j, min (lamEX w r0 x j) (Real.log (clamp01 (w r0 j) / (1001 / 2000))) ≤
      -((N : ℝ) / (2 * 10 ^ 6)))
    (hM0 : (N : ℝ) / 10 ^ 5 ≤ ∑ j, min (lamEX w r0 x j) (Real.log (2 * clamp01 (w r0 j))))
    (hZ : 1 / 2 ≤ Zs w)
    (hte : teW w s ∈ sysMaxEffStates (tpmOf (flipP s w)) univ s s)
    (hconcC : ∀ j C, j ∉ C → D ≤ C.card → |cmean w (univ \ C) r0 j - 1 / 2| ≤ δ C.card)
    (hconcE : ∀ j C, j ∉ C → D ≤ C.card →
      |effUnit (tpmOf (flipP s w)) Cᶜ s j (teW w s j) - 1 / 2| ≤ δ C.card)
    (hsmallC : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < D → K ≠ {x} →
      8 * (D : ℝ) < ∑ j ∈ Kᶜ, min (Real.logb 2 (clamp01 (w r0 j) / cmean w (univ \ K) r0 j))
        (cpx (fun j => clamp01 (w r0 j)) (rowMinU fun j => clamp01 (w r0 j)) (δ (N - 1)) j))
    (hsmallE : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < D →
      8 * (D : ℝ) < ∑ j ∈ Kᶜ,
        min (Real.logb 2 (xE w s j / effUnit (tpmOf (flipP s w)) Kᶜ s j (teW w s j)))
          (cpx (xE w s) (rowMinU (xE w s)) (δ (N - 1)) j)) :
    Pw w r0 / Zs w * N / 10 ^ 6 ≤ phi (flipP s w) s univ := by
  classical
  have hN0 : 0 < N := by omega
  have : Nonempty (Fin N) := ⟨⟨0, hN0⟩⟩
  set z := flipP s w with hzdef
  have hz : z ∈ openCube N := flipP_mem_openCube hw
  have hzw : flipP s z = w := flipP_invol s w
  set te := teW w s with htedef
  have hte' : teW (flipP s z) s = te := by rw [hzw]
  have hl2 := Real.log_pos one_lt_two
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hδN0 := hδ0 (N - 1)
  have hδD0 := hδ0 D
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hDr : (2 : ℝ) ≤ D := by exact_mod_cast hD
  -- clamp on the open cube
  have hcl : ∀ r i, clamp01 (w r i) = w r i := fun r i => by
    have h := hw r i; unfold clamp01; rw [min_eq_right h.2.le, max_eq_right h.1.le]
  -- the states
  have hcause : sysMaxCauseStates (tpmOf z) univ s s = {r0} :=
    sysMaxCauseStates_univ_eq hz s r0 fun r hr => by
      rw [rowProd_eq_Pw, rowProd_eq_Pw, hzw]; exact hstrict r hr
  have hphi : sysPhiOfState (tpmOf z) univ s s r0 te ≤ phi z s univ := by
    exact sysPhiOfState_le_phi (by rw [hcause]; exact mem_singleton_self _) hte
  -- β and e
  set β := sysBackCause (tpmOf z) univ s s r0 with hβdef
  have hβ : β = Pw w r0 / Zs w := by rw [hβdef, sysBackCause_univ_eq hz s r0, hzw]
  set e := sysEffProb (tpmOf z) univ s s te with hedef
  have he : e = eE w s := by rw [hedef, ← hte', sysEffProb_univ_teW z s, hzw]
  have hPw : 0 < Pw w r0 := b1_Pw_pos hw r0
  have hZ0 : 0 < Zs w := by linarith
  have hβ0 : 0 < β := by rw [hβ]; exact div_pos hPw hZ0
  have hβle : β ≤ 2 * Pw w r0 := by
    rw [hβ, div_le_iff₀ hZ0]; nlinarith
  -- the link: `e ≥ N³ P(r0)`
  have hxE0 : ∀ k, 0 < xE w s k := fun k => xE_pos w s k
  have heN : (N : ℝ) ^ 3 * Pw w r0 ≤ e := by
    rw [he, Pw_eq_exp hw r0]
    have h1 : eE w s = Real.exp (∑ k, Real.log (xE w s k)) := by
      rw [Real.exp_sum, eE]; exact prod_congr rfl fun k _ => (Real.exp_log (hxE0 k)).symm
    have h2 : (N : ℝ) ^ 3 = Real.exp (3 * Real.log N) := by
      rw [← Real.log_rpow (by positivity), Real.exp_log (by positivity)]; norm_cast
    rw [h1, h2, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : ∑ k, -Real.log (xE w s k) = -∑ k, Real.log (xE w s k) := sum_neg_distrib _
    linarith
  have he0 : 0 < e := by rw [he]; exact eE_pos w s
  /- ### The cause side -/
  set lc := lamCz z s r0 with hlcdef
  obtain ⟨hlC0, hAeC0, hx0C0, hA0C0, hA1C0⟩ := lamCz_means hz s r0
  rw [hzw] at hlC0 hAeC0 hx0C0 hA0C0 hA1C0
  set yC : Fin N → ℝ := fun j => clamp01 (w r0 j) with hyCdef
  set AC : Fin N → Finset (Fin N) → ℝ := fun j C => cmean w (univ \ C) r0 j with hACdef
  have hlC : ∀ j C, lc j C = Real.logb 2 (yC j / AC j C) := hlC0
  have hfullcard : ∀ j : Fin N, (univ.erase j).card = N - 1 := fun j => by
    rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
  have hqC : ∀ j, |AC j (univ.erase j) - 1 / 2| ≤ δ (N - 1) := fun j => by
    have := hconcC j (univ.erase j) (notMem_erase j univ) (by rw [hfullcard]; omega)
    rwa [hfullcard] at this
  set lc0 := univ.inf' univ_nonempty (kF lc) with hlc0def
  have hminC : ∀ j, lc0 ≤ kF lc j := fun j => inf'_le _ (mem_univ j)
  have hcminC : ∃ j, kF lc j = lc0 := by
    obtain ⟨j, -, hj⟩ := exists_mem_eq_inf' univ_nonempty (kF lc); exact ⟨j, hj.symm⟩
  have hkFC : ∀ j, kF lc j = Real.logb 2 (yC j / AC j (univ.erase j)) := fun j => hlC j _
  have hPC : 1 / 10 ^ 5 ≤ lc0 := by
    refine le_inf' _ _ fun j _ => ?_
    rw [hkFC]
    have := (abs_le.1 (hqC j)).2
    exact logb_lb_e5 (by have h : (1001 / 2000 : ℝ) ≤ yC j := hy j; linarith) (hA0C0 j _) (by linarith)
  obtain ⟨xk, hxk⟩ : ∃ k : Fin N, k ≠ x := by
    by_cases h : x.1 = 0
    · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
    · exact ⟨⟨0, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
  have hsideC := side_keyHyp (lam := lc) (x := yC) (A := AC) (δ := δ) (lmin := lc0)
    (cm := rowMinU yC) (D := D) (dstar := dstar) hlC hAeC0 hx0C0
    (fun j => clamp01_le_one _) hA0C0 hA1C0 (fun j C hj hC => hconcC j C hj hC) hδ0
    (by linarith) hδanti hD hDN hDd hdD hNδD hNδ hBfar hPC hminC (exists_le_rowMinU yC hN0)
    (le_rowMinU (fun j => by have h : (1001 / 2000 : ℝ) ≤ yC j := hy j; linarith) hN0)
    (fun K => K ≠ {x}) xk (fun e => hxk (singleton_injective e))
    (fun K hK1 hKD hKx => by
      have := hsmallC K hK1 hKD hKx
      refine this.trans_le (le_of_eq (sum_congr rfl fun j _ => ?_))
      rw [hlC])
  obtain ⟨hKC0, hHC⟩ := hsideC
  /- ### The effect side -/
  set le := lamEz z s te with hledef
  obtain ⟨hlE0, hAeE0, hx0E0, hA0E0, hA1E0⟩ := lamEz_means hz s te
  have hprob : ∀ j, (tpmOf z).prob j s (te j) = xE w s j := fun j => by
    have := prob_teW z s j; rw [hte', hzw] at this; exact this
  set AE : Fin N → Finset (Fin N) → ℝ := fun j C => effUnit (tpmOf z) Cᶜ s j (te j) with hAEdef
  have hlE : ∀ j C, le j C = Real.logb 2 (xE w s j / AE j C) := fun j C => by
    rw [hledef, hlE0, hprob]
  have hAeE : ∀ j, AE j ∅ = xE w s j := fun j => by rw [← hprob]; exact hAeE0 j
  have hqE : ∀ j, |AE j (univ.erase j) - 1 / 2| ≤ δ (N - 1) := fun j => by
    have := hconcE j (univ.erase j) (notMem_erase j univ) (by rw [hfullcard]; omega)
    rwa [hfullcard] at this
  set le0 := univ.inf' univ_nonempty (kF le) with hle0def
  have hminE : ∀ j, le0 ≤ kF le j := fun j => inf'_le _ (mem_univ j)
  have hcminE : ∃ j, kF le j = le0 := by
    obtain ⟨j, -, hj⟩ := exists_mem_eq_inf' univ_nonempty (kF le); exact ⟨j, hj.symm⟩
  have hkFE : ∀ j, kF le j = Real.logb 2 (xE w s j / AE j (univ.erase j)) := fun j => hlE j _
  have hPE : 1 / 10 ^ 5 ≤ le0 := by
    refine le_inf' _ _ fun j _ => ?_
    rw [hkFE]
    have := (abs_le.1 (hqE j)).2
    exact logb_lb_e5 (by have := hxs j; linarith) (hA0E0 j _) (by linarith)
  have hsideE := side_keyHyp (lam := le) (x := xE w s) (A := AE) (δ := δ) (lmin := le0)
    (cm := rowMinU (xE w s)) (D := D) (dstar := dstar) hlE hAeE hxE0
    (fun j => xE_le_one w s j) hA0E0 hA1E0 (fun j C hj hC => hconcE j C hj hC) hδ0
    (by linarith) hδanti hD hDN hDd hdD hNδD hNδ hBfar hPE hminE (exists_le_rowMinU _ hN0)
    (le_rowMinU (fun j => xE_ge_half w s j) hN0)
    (fun _ => True) x trivial
    (fun K hK1 hKD _ => by
      have := hsmallE K hK1 hKD
      refine this.trans_le (le_of_eq (sum_congr rfl fun j _ => ?_))
      rw [hlE])
  obtain ⟨hKE0, hHE⟩ := hsideE
  have hKE : KeyHyp le le0 (1 + 3 * δ (N - 1)) (fun d => 3 * (δ d + δ (N - 1))) D dstar :=
    { toKeyHyp0 := hKE0, hH := fun K hK1 hKD => hHE K hK1 hKD trivial }
  /- ### Lemma V, the best single cut -/
  have hval : ∀ θ : SysPartition N univ, sysPhiAt (tpmOf z) univ s θ s r0 te =
      min (β * pos (∑ j, lc j (profile θ j))) (e * pos (∑ j, le j (profile θ j))) :=
    fun θ => univ_sysPhiAt_eq hz s r0 te θ
  obtain ⟨jst, -, hjst⟩ := exists_min_image univ (phT lc le β e) univ_nonempty
  have hlcmax : lc0 ≤ 2 := by
    obtain ⟨k, hk⟩ := hcminC
    rw [← hk]
    have := kF_le_of_means hlC hx0C0 (fun j => clamp01_le_one _) hA0C0 hqC hδN0 (by linarith) k
    linarith
  have hphT : β * lc0 ≤ phT lc le β e jst := by
    unfold phT
    refine le_min (mul_le_mul_of_nonneg_left (hminC jst) hβ0.le) ?_
    have h1 : e * le0 ≤ e * kF le jst := mul_le_mul_of_nonneg_left (hminE jst) he0.le
    have hN3 : (10 : ℝ) ^ 21 ≤ (N : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) hNbig 3; norm_num at this ⊢; linarith
    have h2 : β * lc0 ≤ 4 * Pw w r0 := by nlinarith
    have h3 : 4 * Pw w r0 ≤ e * le0 := by nlinarith
    linarith
  /- ### Check V: the comparison partition -/
  have hδ1 : δ (N - 1) ≤ 1 / 100 := by linarith
  have hcj : ∀ j, (kF lc j - lc0) * Real.log 2 ≤
      Real.log (yC j / (1001 / 2000)) + 5 * δ (N - 1) := by
    intro j
    obtain ⟨k, hk⟩ := hcminC
    rw [← hk, sub_mul, hkFC, hkFC, logb_mul_log2, logb_mul_log2]
    exact log_gap_le (by norm_num) (hy k) (hx0C0 j) hδN0 hδ1
      (by have := (abs_le.1 (hqC j)).1; linarith) (hA0C0 k _) (by have := (abs_le.1 (hqC k)).2; linarith)
  have hlamx : ∀ j, lc j {x} * Real.log 2 = lamEX w r0 x j := fun j => by
    have := lamCz_single_eq hz s r0 x j
    rw [hzw] at this
    rw [this]; rfl
  have hlamlb : ∀ j, -(1 / 2 : ℝ) ≤ lamEX w r0 x j := fun j =>
    lam_lb (by have h : (1001 / 2000 : ℝ) ≤ yC j := hy j; linarith) (clamp01_nonneg _) (clamp01_le_one _)
  have hVsum : (kF lc x - lc0) + kM lc lc0 {x} < 0 :=
    vsum_neg (y := yC) hNbig hδN0 hNδ hcj hlamx hlamlb hy (fun j => clamp01_le_one _) hV
  set P := (univ.erase x).filter fun j => lc j {x} ≤ kF lc j - lc0 with hPdef
  have hxP : x ∉ P := fun h => by simp [hPdef] at h
  have hPmem : ∀ j, j ∈ P ↔ (j ≠ x ∧ lc j {x} ≤ kF lc j - lc0) := fun j => by
    rw [hPdef, mem_filter, mem_erase]; simp
  set θm := uxTheta x P hxP hN2 with hθmdef
  have hE := uxTheta_excess (lam := lc) (lmin := lc0) (by linarith) hxP hN2 hPmem
  set Λc := ∑ j, lc j (profile θm j) with hΛc
  set cc : ℝ := ∑ j, ((profile θm j).card : ℝ) with hccdef
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hccθ : (sysCutCount θm : ℝ) = cc := by
    rw [univ_sysCutCount_eq]; push_cast; rfl
  have hccpos : (0 : ℝ) < cc := by
    have := sysCutCount_pos θm
    rw [← hccθ]; exact_mod_cast this
  have hlt : ((N : ℝ) - 1) * Λc < lc0 * cc := by
    have := mul_neg_of_pos_of_neg hN1 hVsum
    linarith
  have hphTpos : 0 < phT lc le β e jst := lt_of_lt_of_le (by positivity) hphT
  have hVpart : ∃ θ' : SysPartition N univ, sysPhiAt (tpmOf z) univ s θ' s r0 te / (sysCutCount θ' : ℝ) <
      phT lc le β e jst / ((N : ℝ) - 1) := by
    refine ⟨θm, ?_⟩
    rw [hccθ]
    have hle1 : sysPhiAt (tpmOf z) univ s θm s r0 te ≤ β * pos Λc := by
      rw [hval]; exact min_le_left _ _
    have hrhs : 0 < phT lc le β e jst / ((N : ℝ) - 1) := div_pos hphTpos hN1
    rcases le_or_gt Λc 0 with hneg | hpos'
    · have : pos Λc = 0 := by unfold pos; exact max_eq_left hneg
      rw [this, mul_zero] at hle1
      have : sysPhiAt (tpmOf z) univ s θm s r0 te / cc ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hle1 hccpos.le
      linarith
    · have hp : pos Λc = Λc := by unfold pos; exact max_eq_right hpos'.le
      rw [hp] at hle1
      calc sysPhiAt (tpmOf z) univ s θm s r0 te / cc ≤ β * Λc / cc :=
            div_le_div_of_nonneg_right hle1 hccpos.le
        _ < β * lc0 / ((N : ℝ) - 1) := by
            rw [div_lt_div_iff₀ hccpos hN1]
            have h := mul_lt_mul_of_pos_left hlt hβ0
            have e1 : β * Λc * ((N : ℝ) - 1) = β * (((N : ℝ) - 1) * Λc) := by ring
            have e2 : β * lc0 * cc = β * (lc0 * cc) := by ring
            rw [e1, e2]; exact h
        _ ≤ phT lc le β e jst / ((N : ℝ) - 1) := div_le_div_of_nonneg_right hphT hN1.le
  /- ### `phi_lower_fail` -/
  have hmain := phi_lower_fail (tpmOf z) s s r0 te hN2 hβ0 he0 hval hKC0 x
    (fun K hK1 hKD hKx => hHC K hK1 hKD hKx) hKE hcminC hcminE jst (fun j => hjst j (mem_univ j))
    hVpart
  refine le_trans ?_ (hmain.trans hphi)
  /- ### The two values -/
  clear_value Λc cc θm P β e
  have hδD3 : ((N : ℝ) - 1) * (3 * (δ D + δ (N - 1))) ≤ 6 / 100 := by
    have h1 : ((N : ℝ) - 1) * (3 * (δ D + δ (N - 1))) ≤ (N : ℝ) * (3 * (δ D + δ (N - 1))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : (N : ℝ) * (3 * (δ D + δ (N - 1))) = 3 * ((N : ℝ) * δ D) + 3 * ((N : ℝ) * δ (N - 1)) := by ring
    linarith
  have hkM0C : (N : ℝ) / 10 ^ 5 - 102 / 100 ≤ kM0 lc x := by
    refine kM0_ge (y := yC) hNbig hδN0 hNδ (fun j => ?_) hlamx (fun j => hx0C0 j)
      (fun j => clamp01_le_one _) hM0
    rw [hkFC, logb_mul_log2]
    exact log_kF_ge (hx0C0 j) (hA0C0 j _) (by have := (abs_le.1 (hqC j)).2; linarith) hδN0
  have hcomplx : ({x}ᶜ : Finset (Fin N)) = univ.erase x := by ext; simp
  have hkM0E : 8 * (D : ℝ) ≤ kM0 le x := by
    have h := hsmallE {x} (by simp) (by rw [card_singleton]; omega)
    rw [kM0, ← hcomplx]
    obtain ⟨kE, hkE⟩ := exists_le_rowMinU (xE w s) hN0
    refine h.le.trans (sum_le_sum fun j _ => min_le_min (le_of_eq (hlE j {x}).symm) ?_)
    have := cpx_le_kF hlE hxE0 hA0E0 hqE (by linarith) hminE hkE j
    linarith [hPE]
  have hval_c : Pw w r0 / Zs w * N / 10 ^ 6 ≤
      β * (kM0 lc x - ((N : ℝ) - 1) * (3 * (δ D + δ (N - 1))) - (1 + 3 * δ (N - 1))) := by
    rw [← hβ, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hβ0.le
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have hval_e : Pw w r0 / Zs w * N / 10 ^ 6 ≤
      e * (kM0 le x - ((N : ℝ) - 1) * (3 * (δ D + δ (N - 1))) - (1 + 3 * δ (N - 1))) := by
    rw [← hβ]
    have h1 : 1 ≤ kM0 le x - ((N : ℝ) - 1) * (3 * (δ D + δ (N - 1))) - (1 + 3 * δ (N - 1)) := by
      linarith
    have a1 : β * N ≤ 2 * Pw w r0 * N := mul_le_mul_of_nonneg_right hβle (Nat.cast_nonneg _)
    have a2 : 2 * Pw w r0 * N ≤ (N : ℝ) ^ 3 * Pw w r0 := by
      have := mul_le_mul_of_nonneg_right (two_mul_le_cube hNr) hPw.le
      linarith
    have a3 : β * N / 10 ^ 6 ≤ β * N := by
      have : 0 ≤ β * N := mul_nonneg hβ0.le (Nat.cast_nonneg _)
      linarith
    have a4 : e ≤ e * (kM0 le x - ((N : ℝ) - 1) * (3 * (δ D + δ (N - 1))) - (1 + 3 * δ (N - 1))) :=
      le_mul_of_one_le_right he0.le h1
    linarith
  exact le_min hval_c hval_e

end Census
end IIT
