/-
Census, B1 LTBetaHi, round-2 open item (c), deterministic part: **the light statistic at `w½` is small on
non-adverse members**.

`w½ = lt3Hf s ε γ n w` is `stHalf` of the windowed private set (the configuration `lt3W_TCprime` reads its light
part from). We show:
* `lt3Hf_gNs`: at `w½` the non-special weight of a row is `0` on `Sp(w)` and its full product elsewhere (private rows
  are solidly light: `Top`-columns of `lt3L` rows); hence `lt3Light_half`: when `tc ∈ Sp`, the light part
  `lt3Light w½ S (lt3H w)` is the non-special numerator `lt2NumNs w½ S`;
* `lt3_pat_le` (Lemma D2 at `|S| = 3`): pattern differences of `lt2NumNs` are `≤ 16 g` when every `|G_{i,R}(T)|`
  (`R, T ⊆ S`, `T ≠ ∅`) is `≤ g`;
* `lt3G_pert` (W2 (6.1)): `|G(w) - G(w½)| ≤ 2 E`, `E = |Priv| · 2 · (e^{-3N/10} + e^{-x₁N})` (`lt3PE`);
* `lt3Adv κ w`: members of `lt3WF` with some `|G_{i,R}(T)(w½)| > 3κσ_N`; `lt3_hHalf_of_not_adv`: on a
  non-adverse member the `hHalf` input of `lt3W_TCprime_ev` holds with `φH = 48 κ σ_N`, and `lt3_phiH_le`:
  `48 κ σ_N ≤ t P(tc)/8000` once `L ≥ 768000 κ/t` (band `Lσ_N ≤ β`, `Zs ≥ 1/2`).
The count of adverse members is in `B1LTHiLight2`.
-/
import IIT.Census.B1LTHiBand

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-! ### Non-special weights -/

/-- `P_ns(v) = 0` on `Sp`, `P(v)` elsewhere. -/
lemma lt2gNs_split (w : Param N) (v : State N) : lt2gNs (w v) = if v ∈ lt2Sp w then 0 else Pw w v := by
  by_cases hs : v ∈ lt2Sp w
  · rw [if_pos hs]; have := bd_Pw_split w v; rw [if_pos hs] at this; linarith
  · rw [if_neg hs]; have := bd_Pw_split w v; rw [if_neg hs] at this; linarith

/-! ### The half-replaced configuration -/

section Half

variable (s : State N) (ε γ : ℝ) (n : ℕ)

/-- `w½`: the private entries of the windowed selection replaced by `1/2`. -/
noncomputable def lt3Hf (w : Param N) : Param N := stHalf (stPriv (lt3WSel s ε γ n) lt3PB w) w

lemma lt3Hf_def (w : Param N) : lt3Hf s ε γ n w = stHalf (stPriv (lt3WSel s ε γ n) lt3PB w) w := rfl

/-- Private positions sit in `Top` columns of light rows. -/
lemma lt3W_priv_light {w : Param N} {q : State N × Fin N} (hq : q ∈ stPriv (lt3WSel s ε γ n) lt3PB w) :
    q.2 ∈ lt3Top s w ε ∧ lt3L s ε w q.1 := by
  obtain ⟨k, hk, hqk⟩ := mem_biUnion.1 hq
  have hns := lt3WPB_not_safe w k hk q hqk
  have h1 : q ∉ lt3Safe s ε w := fun h => hns (Or.inl h)
  simp only [lt3Safe, Set.mem_setOf_eq, not_or, not_not] at h1
  exact ⟨h1.1, h1.2.1⟩

lemma lt3Hf_row {w : Param N} {v : State N} (h : ∀ j, (v, j) ∉ stPriv (lt3WSel s ε γ n) lt3PB w) :
    lt3Hf s ε γ n w v = w v := by
  funext j
  simp only [lt3Hf, stHalf]
  rw [if_neg (h j)]

lemma lt3Hf_XM (w : Param N) (v : State N) :
    XMW (lt3Hf s ε γ n w) (lt3Top s w ε)ᶜ v = XMW w (lt3Top s w ε)ᶜ v := by
  unfold XMW
  refine Finset.sum_congr rfl fun j hj => ?_
  have hnp : (v, j) ∉ stPriv (lt3WSel s ε γ n) lt3PB w := fun hq =>
    (mem_compl.1 hj) (lt3W_priv_light s ε γ n hq).1
  simp only [lt3Hf, stHalf]
  rw [if_neg hnp]

/-- **Non-special weights at `w½`**: `0` on `Sp(w)`, the full product elsewhere. -/
lemma lt3Hf_gNs (w : Param N) (v : State N) :
    lt2gNs (lt3Hf s ε γ n w v) = if v ∈ lt2Sp w then 0 else Pw (lt3Hf s ε γ n w) v := by
  have hx1 := lt2x1_bounds
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hx1N : lt2x1 * N ≤ 3 / 10 * N := mul_le_mul_of_nonneg_right (by linarith) hN0
  by_cases hp : ∃ j, (v, j) ∈ stPriv (lt3WSel s ε γ n) lt3PB w
  · obtain ⟨j, hj⟩ := hp
    have hL := (lt3W_priv_light s ε γ n hj).2
    unfold lt3L at hL
    have hnS : v ∉ lt2Sp w := by
      simp only [lt2Sp, mem_filter, mem_univ, true_and, not_le]
      have := XMW_le_XW w (lt3Top s w ε)ᶜ v
      linarith
    rw [if_neg hnS]
    unfold lt2gNs
    rw [if_pos]
    · rfl
    · have h1 := XMW_le_XW (lt3Hf s ε γ n w) (lt3Top s w ε)ᶜ v
      rw [lt3Hf_XM] at h1
      have h2 : XW (lt3Hf s ε γ n w) v = ∑ j, -Real.log (clamp01 (lt3Hf s ε γ n w v j)) := rfl
      linarith
  · push Not at hp
    have hPv : Pw (lt3Hf s ε γ n w) v = Pw w v := by unfold Pw; rw [lt3Hf_row s ε γ n hp]
    rw [hPv, lt3Hf_row s ε γ n hp]
    exact lt2gNs_split w v

/-- **The light part at `w½` is the non-special numerator** (when `tc` is special, `lt3H w = Sp`). -/
lemma lt3Light_half (w : Param N) (htc : tcRow w ∈ lt2Sp w) (S : Finset (Fin N)) (t : State N) (j : Fin N) :
    lt3Light (lt3Hf s ε γ n w) S (lt3H w) t j = lt2NumNs (lt3Hf s ε γ n w) S t j := by
  have hH : lt3H w = lt2Sp w := insert_eq_of_mem htc
  unfold lt3Light lt2NumNs
  rw [hH, ← Finset.sum_compl_add_sum (lt2Sp w)]
  have h0 : ∑ v ∈ lt2Sp w, clamp01 (lt3Hf s ε γ n w (merge S t v) j) * lt2gNs (lt3Hf s ε γ n w v) = 0 :=
    Finset.sum_eq_zero fun v hv => by rw [lt3Hf_gNs, if_pos hv, mul_zero]
  rw [h0, add_zero]
  exact Finset.sum_congr rfl fun v hv => by rw [lt3Hf_gNs, if_neg (mem_compl.1 hv)]

end Half

/-! ### Pattern differences from bounded `G`'s -/

/-- **Lemma D2 at `|S| = 3`**: if every `|G_{i,R}(T)|` (`R, T ⊆ S`, `T ≠ ∅`) is `≤ g`, the pattern differences of
the non-special numerator are `≤ 16 g`. -/
lemma lt3_pat_le (w : Param N) {S : Finset (Fin N)} (hS : S.card = 3) {g : ℝ} (hg : 0 ≤ g) {i : Fin N}
    (hG : ∀ R ⊆ S, ∀ T ⊆ S, T.Nonempty → |lt2G w i R T| ≤ g) (t0 t : State N) :
    |lt2NumNs w S t0 i - lt2NumNs w S t i| ≤ 16 * g := by
  refine (lt2_D2 w S t0 t i).trans ?_
  have hsum : ∑ R ∈ S.powerset, ∑ T ∈ S.powerset.filter (fun T => T.Nonempty), |lt2G w i R T| ≤
      ∑ _R ∈ S.powerset, ∑ _T ∈ S.powerset, g := by
    refine Finset.sum_le_sum fun R hR => ?_
    calc ∑ T ∈ S.powerset.filter (fun T => T.Nonempty), |lt2G w i R T|
        ≤ ∑ _T ∈ S.powerset.filter (fun T => T.Nonempty), g :=
          Finset.sum_le_sum fun T hT =>
            hG R (mem_powerset.1 hR) T (mem_powerset.1 (mem_filter.1 hT).1) (mem_filter.1 hT).2
      _ ≤ ∑ _T ∈ S.powerset, g := Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => hg
  have h8 : (S.powerset.card : ℝ) = 8 := by rw [card_powerset, hS]; norm_num
  rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, h8] at hsum
  have h23 : (2 : ℝ) ^ S.card = 8 := by rw [hS]; norm_num
  rw [h23]
  linarith

/-! ### The perturbation of `G` -/

/-- `G` as a signed sum over the rows outside `Sp(w)`, for any `w'` whose non-special weights vanish on `Sp(w)`. -/
lemma lt3G_signed (w w' : Param N) (hg : ∀ v, lt2gNs (w' v) = if v ∈ lt2Sp w then 0 else Pw w' v)
    (i : Fin N) (R T : Finset (Fin N)) :
    lt2G w' i R T = ∑ v ∈ (lt2Sp w)ᶜ.filter (fun v => lt2Chi T v = 1), clamp01 (w' (lt2Xor v R) i) * Pw w' v -
      ∑ v ∈ (lt2Sp w)ᶜ.filter (fun v => lt2Chi T v ≠ 1), clamp01 (w' (lt2Xor v R) i) * Pw w' v := by
  have hchi : ∀ v, lt2Chi T v = 1 ∨ lt2Chi T v = -1 := fun v => (abs_eq zero_le_one).1 (lt2Chi_abs T v)
  have h0 : ∑ v ∈ lt2Sp w, lt2gNs (w' v) * clamp01 (w' (lt2Xor v R) i) * lt2Chi T v = 0 :=
    Finset.sum_eq_zero fun v hv => by rw [hg, if_pos hv]; ring
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  unfold lt2G
  rw [← Finset.sum_compl_add_sum (lt2Sp w), h0, add_zero]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [hg, if_neg (mem_compl.1 hv)]
  rcases hchi v with h | h
  · rw [if_pos h, if_neg (not_not.2 h), h]; ring
  · have h' : lt2Chi T v ≠ 1 := by rw [h]; norm_num
    rw [if_neg h', if_pos h', h]; ring

section Pert

variable (s : State N) (ε γ : ℝ) (n : ℕ)

/-- The perturbation error at `nσ = 1`. -/
noncomputable def lt3PE (w : Param N) : ℝ :=
  (((stPriv (lt3WSel s ε γ n) lt3PB w).card * (1 + 1) : ℕ) : ℝ) *
    (Real.exp (-(3 / 10 * (N : ℝ))) + Real.exp (-(lt2x1 * N)))

/-- **The perturbation of `G` between `w` and `w½`** (W2 (6.1)): `≤ 2 E`. -/
theorem lt3G_pert (w : Param N) (i : Fin N) (R T : Finset (Fin N)) :
    |lt2G w i R T - lt2G (lt3Hf s ε γ n w) i R T| ≤ 2 * lt3PE s ε γ n w := by
  rw [lt3G_signed w w (lt2gNs_split w), lt3G_signed w (lt3Hf s ε γ n w) (lt3Hf_gNs s ε γ n w)]
  set Vp := (lt2Sp w)ᶜ.filter (fun v => lt2Chi T v = 1) with hVp
  set Vm := (lt2Sp w)ᶜ.filter (fun v => lt2Chi T v ≠ 1) with hVm
  have hfib : ∀ (V : Finset (State N)) (q : State N), (V.filter fun v => lt2Xor v R = q).card ≤ 1 := by
    intro V q
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    have h1 := (mem_filter.1 ha).2
    have h2 := (mem_filter.1 hb).2
    rw [← lt2Xor_xor a R, ← lt2Xor_xor b R, h1, h2]
  have hp : |∑ v ∈ Vp, clamp01 (w (lt2Xor v R) i) * Pw w v -
      ∑ v ∈ Vp, clamp01 (lt3Hf s ε γ n w (lt2Xor v R) i) * Pw (lt3Hf s ε γ n w) v| ≤ lt3PE s ε γ n w :=
    lt3W_pert s ε γ n w Vp (fun v hv => mem_compl.1 (mem_filter.1 hv).1) (fun v => lt2Xor v R) i
      (fun x => ∏ j, clamp01 (x j)) (fun x => prod_nonneg fun j _ => clamp01_nonneg _) (fun x => le_rfl) 1
      (hfib Vp)
  have hm : |∑ v ∈ Vm, clamp01 (w (lt2Xor v R) i) * Pw w v -
      ∑ v ∈ Vm, clamp01 (lt3Hf s ε γ n w (lt2Xor v R) i) * Pw (lt3Hf s ε γ n w) v| ≤ lt3PE s ε γ n w :=
    lt3W_pert s ε γ n w Vm (fun v hv => mem_compl.1 (mem_filter.1 hv).1) (fun v => lt2Xor v R) i
      (fun x => ∏ j, clamp01 (x j)) (fun x => prod_nonneg fun j _ => clamp01_nonneg _) (fun x => le_rfl) 1
      (hfib Vm)
  set A := ∑ v ∈ Vp, clamp01 (w (lt2Xor v R) i) * Pw w v
  set A' := ∑ v ∈ Vp, clamp01 (lt3Hf s ε γ n w (lt2Xor v R) i) * Pw (lt3Hf s ε γ n w) v
  set B := ∑ v ∈ Vm, clamp01 (w (lt2Xor v R) i) * Pw w v
  set B' := ∑ v ∈ Vm, clamp01 (lt3Hf s ε γ n w (lt2Xor v R) i) * Pw (lt3Hf s ε γ n w) v
  calc |A - B - (A' - B')| = |(A - A') - (B - B')| := by ring_nf
    _ ≤ |A - A'| + |B - B'| := abs_sub _ _
    _ ≤ lt3PE s ε γ n w + lt3PE s ε γ n w := add_le_add hp hm
    _ = 2 * lt3PE s ε γ n w := by ring

/-- **The perturbation is negligible** for `N` large: `2 E ≤ κ σ_N / 2` whenever `|Priv| ≤ 24 · 13 N²`. -/
theorem lt3PE_small {κ : ℝ} (hκ : 0 < κ) : ∀ᶠ N : ℕ in atTop, ∀ P : ℕ, P ≤ 24 * (13 * (N * N)) →
    2 * (((P * (1 + 1) : ℕ) : ℝ) * (Real.exp (-(3 / 10 * (N : ℝ))) + Real.exp (-(lt2x1 * N)))) ≤
      κ * sigN N / 2 := by
  filter_upwards [cr_ev_poly_exp 2 (Real.log (2496 * 8 / κ)) (δ := 1 / 400) (by norm_num)] with N hN P hP
  rw [Real.exp_log (by positivity)] at hN
  have hx1 := lt2x1_bounds
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have he1 : Real.exp (-(3 / 10 * (N : ℝ))) ≤ Real.exp (-(lt2x1 * N)) := Real.exp_le_exp.2 (by nlinarith)
  have hP' : ((P * (1 + 1) : ℕ) : ℝ) ≤ 624 * ((N : ℝ) + 1) ^ 2 := by
    have h9 : P * (1 + 1) ≤ 624 * (N * N) := by omega
    calc ((P * (1 + 1) : ℕ) : ℝ) ≤ ((624 * (N * N) : ℕ) : ℝ) := by exact_mod_cast h9
      _ = 624 * ((N : ℝ) * N) := by push_cast; ring
      _ ≤ 624 * ((N : ℝ) + 1) ^ 2 := by nlinarith
  set E := Real.exp (-(lt2x1 * N)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hsplit : sigN N = E * Real.exp (1 / 400 * N) := by
    rw [sigN_eq_exp, hE, ← Real.exp_add]; unfold lt2x1; ring_nf
  have k1 : ((P * (1 + 1) : ℕ) : ℝ) * (Real.exp (-(3 / 10 * (N : ℝ))) + E) ≤
      (624 * ((N : ℝ) + 1) ^ 2) * (2 * E) :=
    mul_le_mul hP' (by linarith) (by positivity) (by positivity)
  have k2 : (κ / 2 * E) * (((N : ℝ) + 1) ^ 2 * (2496 * 8 / κ)) ≤ (κ / 2 * E) * Real.exp (1 / 400 * N) :=
    mul_le_mul_of_nonneg_left hN (by positivity)
  have k3 : (κ / 2 * E) * (((N : ℝ) + 1) ^ 2 * (2496 * 8 / κ)) = 8 * ((624 * ((N : ℝ) + 1) ^ 2) * (2 * E)) := by
    field_simp; ring
  rw [hsplit]
  nlinarith

end Pert

/-! ### Adverse members and the light statistic -/

section Adv

variable (s : State N) (ε γ : ℝ) (n : ℕ)

/-- **Adverse members** of the windowed family (at `w½`, level `3κσ_N`). -/
noncomputable def lt3Adv (κ : ℝ) (w : Param N) : Finset (Finset (Fin N)) := by
  classical exact (lt3WF s ε γ n w).filter fun S => ∃ i ∈ S, ∃ R ⊆ S, ∃ T ⊆ S, T.Nonempty ∧
    3 * κ * sigN N < |lt2G (lt3Hf s ε γ n w) i R T|

/-- **On a non-adverse member the light statistic at `w½` is `≤ 48 κ σ_N`** (the `hHalf` input of
`lt3W_TCprime_ev`, with `φH = 48 κ σ_N`), when `tc` is special. -/
theorem lt3_hHalf_of_not_adv {κ : ℝ} (hκ : 0 ≤ κ) {w : Param N} (htc : tcRow w ∈ lt2Sp w) {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hS : ({a, b, c} : Finset (Fin N)) ∈ lt3WF s ε γ n w)
    (hnot : ({a, b, c} : Finset (Fin N)) ∉ lt3Adv s ε γ n κ w) :
    ∀ (t0 : State N) (u : Fin (2 ^ 3)) (i : Fin 3),
      |lt3Light (stHalf (stPriv (lt3WSel s ε γ n) lt3PB w) w) {a, b, c} (lt3H w)
          (pkFlip (pkE3 hab hac hbc) t0 u) (pkE3 hab hac hbc i) -
        lt3Light (stHalf (stPriv (lt3WSel s ε γ n) lt3PB w) w) {a, b, c} (lt3H w) t0 (pkE3 hab hac hbc i)| ≤
      48 * κ * sigN N := by
  classical
  intro t0 u i
  rw [← lt3Hf_def, lt3Light_half s ε γ n w htc, lt3Light_half s ε γ n w htc]
  have hS3 : ({a, b, c} : Finset (Fin N)).card = 3 := by
    rw [card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]
  have hσ : 0 ≤ sigN N := by unfold sigN; positivity
  have hiS : pkE3 hab hac hbc i ∈ ({a, b, c} : Finset (Fin N)) := (pkE3_S hab hac hbc _).2 ⟨i, rfl⟩
  have hG : ∀ R ⊆ ({a, b, c} : Finset (Fin N)), ∀ T ⊆ ({a, b, c} : Finset (Fin N)), T.Nonempty →
      |lt2G (lt3Hf s ε γ n w) (pkE3 hab hac hbc i) R T| ≤ 3 * κ * sigN N := by
    intro R hR T hT hTne
    by_contra hcon
    push Not at hcon
    exact hnot (mem_filter.2 ⟨hS, pkE3 hab hac hbc i, hiS, R, hR, T, hT, hTne, hcon⟩)
  have h := lt3_pat_le (lt3Hf s ε γ n w) hS3 (by positivity) hG (pkFlip (pkE3 hab hac hbc) t0 u) t0
  linarith

end Adv

/-- **`φH = 48 κ σ_N ≤ t P(tc)/8000`** on the band `Lσ_N ≤ β`, `Zs ≥ 1/2`, once `768000 κ ≤ t L`. -/
lemma lt3_phiH_le {κ t L : ℝ} (hκ : 0 ≤ κ) (ht : 0 < t) (hL : 768000 * κ ≤ t * L) {w : Param N}
    (hZ : 1 / 2 ≤ Zs w) (hβ : L * sigN N ≤ betaW w) : 48 * κ * sigN N ≤ t / 8000 * Pw w (tcRow w) := by
  have hZpos : 0 < Zs w := lt_of_lt_of_le (by norm_num) hZ
  have hβZ : betaW w * Zs w = Pw w (tcRow w) := by unfold betaW; exact div_mul_cancel₀ _ hZpos.ne'
  have hσ : 0 ≤ sigN N := by unfold sigN; positivity
  have e1 : L * sigN N * (1 / 2) ≤ betaW w * (1 / 2) := mul_le_mul_of_nonneg_right hβ (by norm_num)
  have e2 : betaW w * (1 / 2) ≤ betaW w * Zs w := mul_le_mul_of_nonneg_left hZ (betaW_nonneg w)
  have hlow : L * sigN N / 2 ≤ Pw w (tcRow w) := by linarith
  have k1 : t / 8000 * (L * sigN N / 2) ≤ t / 8000 * Pw w (tcRow w) :=
    mul_le_mul_of_nonneg_left hlow (by positivity)
  have k2 : 48 * κ * sigN N ≤ t / 8000 * (L * sigN N / 2) := by
    have := mul_le_mul_of_nonneg_right hL hσ
    nlinarith
  linarith

end Census
end IIT
