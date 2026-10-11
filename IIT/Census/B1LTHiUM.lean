/-
Census, B1 LTBetaHi, RL-u part 2d: **the success region of a member when `s ∈ Sp \ {tc}`**.

* The member's RL-u data: the rest `H \ {s}` (which contains `tc`) at the scale `σ = λ P(tc)`, where
  `λ = max(1, max_i G1_i)` brings the rest `A`-level into `[4/5, 1]` (`lt3URestD`); `s`'s weight `wu = P(s)/σ`,
  its shared entries `lt3UX`, `lt3UF`, its offset `lt3Uds` (`D_u = ∅` if `s` agrees with `tc` on `S`, else `S`),
  and the Hilbert-chosen table `lt3UTab` (a function of these data only).
  **`lt3UTab_spec`**: for a member of `lt3WSel` with `s ∈ Sp \ {tc}` and `|H \ {s}| ≤ 2`, the table satisfies
  `RLUWin` with window loss `1/320000` (`rlu_real_window`); the units of `S` are good (`Top'`).
* `lt3UData_replE`: resampling `Priv` keeps the data and the table.
* **`lt3_u_quarter`**: `β/4 ≤ φ_s(S)` (cause `lt3_TCprime_u` at scale `σ`, effect `lt3_heff_u` at `a = 1/2`).
* **`lt3_u_member_ev`** (`L ≥ lt3Lc`): every non-adverse member with `s ∈ Sp \ {tc}`, `|H \ {s}| ≤ 2` has a success
  region of probability `≥ lt3pT` (rest box `∩` `s`'s box, disjoint blocks).
-/
import IIT.Census.B1LTHiUC
import IIT.Census.B1LTHiTcM

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-! ### The member's RL-u data and table -/

/-- The unscaled rest data of an `s`-member (rows `H \ {s}`, weights `P(r)/P(tc)`). -/
noncomputable def lt3URest0 (w : Param N) (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) (s : State N) : RLDR :=
  lt3RealData w e S (tcRow w) ((lt3H w).erase s) (Pw w (tcRow w))

/-- The scale `λ = max(1, max_i G1_i)`. -/
noncomputable def lt3Ulam (w : Param N) (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) (s : State N) : ℝ :=
  max 1 (max ((lt3URest0 w e S s).G1 0) (max ((lt3URest0 w e S s).G1 1) ((lt3URest0 w e S s).G1 2)))

/-- The cause scale `σ = λ P(tc)`. -/
noncomputable def lt3Usig (w : Param N) (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) (s : State N) : ℝ :=
  lt3Ulam w e S s * Pw w (tcRow w)

/-- The scaled rest data. -/
noncomputable def lt3URestD (w : Param N) (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) (s : State N) : RLDR :=
  lt3RealData w e S (tcRow w) ((lt3H w).erase s) (lt3Usig w e S s)

/-- `s`'s own entries on the units. -/
noncomputable def lt3UX (w : Param N) (e : Fin 3 ↪ Fin N) (s : State N) : Fin 3 → ℝ := fun i => clamp01 (w s (e i))

/-- `s`'s own-flip entries on the units. -/
noncomputable def lt3UF (w : Param N) (e : Fin 3 ↪ Fin N) (s : State N) : Fin 3 → ℝ :=
  fun i => clamp01 (w (flip s (e i)) (e i))

/-- `s`'s offset: `false` (`D_u = ∅`) if `s` agrees with `tc` on `S`. -/
noncomputable def lt3Uds (w : Param N) (S : Finset (Fin N)) (s : State N) : Bool := by
  classical exact if ∀ j ∈ S, s j = tcRow w j then false else true

/-- `s`'s weight. -/
noncomputable def lt3Uwu (w : Param N) (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) (s : State N) : ℝ :=
  Pw w s / lt3Usig w e S s

/-- The threshold of the offset. -/
noncomputable def lt3Uthr (ds : Bool) : ℝ := if ds then 7 / 8 else 9 / 16

/-- **The chosen RL-u table** (with its level `x0`) of an `s`-member. -/
noncomputable def lt3UTab (w : Param N) (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) (s : State N) : TcTab × ℝ :=
  Classical.epsilon fun p : TcTab × ℝ => lt3Uthr (lt3Uds w S s) - 1 / 1000 ≤ p.2 ∧
    RLUWin (lt3Uds w S s) (lt3URestD w e S s) (lt3Uwu w e S s) (lt3UX w e s) (lt3UF w e s) (1 / 320000) p.2 p.1

lemma lt3Uds_spec {w : Param N} {S : Finset (Fin N)} {s : State N}
    (h : (∀ j ∈ S, s j = tcRow w j) ∨ (∀ j ∈ S, s j ≠ tcRow w j)) :
    (lt3Uds w S s = false ∧ ∀ j ∈ S, s j = tcRow w j) ∨ (lt3Uds w S s = true ∧ ∀ j ∈ S, s j ≠ tcRow w j) := by
  classical
  unfold lt3Uds
  split_ifs with hc
  · exact Or.inl ⟨rfl, hc⟩
  · rcases h with h | h
    · exact absurd h hc
    · exact Or.inr ⟨rfl, h⟩

lemma lt3RD_scale (w : Param N) (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) (tc : State N) (H : Finset (State N))
    {σ l : ℝ} (hσ : σ ≠ 0) (hl : l ≠ 0) :
    (∀ i, (lt3RealData w e S tc H (l * σ)).G1 i = (lt3RealData w e S tc H σ).G1 i / l) ∧
    (∀ i, (lt3RealData w e S tc H (l * σ)).F1 i = (lt3RealData w e S tc H σ).F1 i / l) ∧
    (lt3RealData w e S tc H (l * σ)).V1 = (lt3RealData w e S tc H σ).V1 / l ∧
    (lt3RealData w e S tc H (l * σ)).V2 = (lt3RealData w e S tc H σ).V2 / l := by
  refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩ <;> simp only [lt3RealData] <;> rw [sum_div] <;>
    refine sum_congr rfl fun r _ => ?_ <;> field_simp

/-- `1 ≤ λ ≤ 2` when `|H \ {s}| ≤ 2`; `λ` dominates the unscaled `G1`. -/
lemma lt3Ulam_bounds {w : Param N} (hw : w ∈ openCube N) (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) (s : State N) :
    1 ≤ lt3Ulam w e S s ∧ (∀ i, (lt3URest0 w e S s).G1 i ≤ lt3Ulam w e S s) ∧
      lt3Ulam w e S s ≤ max 1 (lt3URest0 w e S s).V1 := by
  have hσ := b1_Pw_pos hw (tcRow w)
  obtain ⟨-, -, -, -, hG1V, -, -, -, -, -, -⟩ :=
    lt3RD_bounds w e S (tcRow w) ((lt3H w).erase s) hσ (fun r => Pw_le_tcRow w r)
  refine ⟨le_max_left _ _, fun i => ?_, max_le_max le_rfl (max_le (hG1V 0) (max_le (hG1V 1) (hG1V 2)))⟩
  unfold lt3Ulam
  fin_cases i
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  · exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)

lemma lt3Usig_ge {w : Param N} (hw : w ∈ openCube N) (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) (s : State N) :
    Pw w (tcRow w) ≤ lt3Usig w e S s := by
  unfold lt3Usig
  have := (lt3Ulam_bounds hw e S s).1
  have h0 := Pw_nonneg w (tcRow w)
  nlinarith

/-- The rest `V`'s under `|H \ {s}| ≤ 2`: `V1 ≤ 2`, `V2 ≤ 1` (at any scale `σ ≥ P(r)`). -/
lemma lt3U_V_bounds {w : Param N} (e : Fin 3 ↪ Fin N) {S : Finset (Fin N)} (hS0 : S.Nonempty) {s : State N}
    (htc : tcRow w ∈ (lt3H w).erase s) (hH2 : ((lt3H w).erase s).card ≤ 2) {σ : ℝ} (hσ : 0 < σ)
    (hPw : ∀ r, Pw w r ≤ σ) :
    (lt3RealData w e S (tcRow w) ((lt3H w).erase s) σ).V1 ≤ 2 ∧
      (lt3RealData w e S (tcRow w) ((lt3H w).erase s) σ).V2 ≤ 1 := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, hV2n, hVH⟩ := lt3RD_bounds w e S (tcRow w) ((lt3H w).erase s) hσ hPw
  have hw1 : ∀ r, Pw w r / σ ≤ 1 := fun r => (div_le_one hσ).2 (hPw r)
  have hB : lt3HB S (tcRow w) ((lt3H w).erase s) ⊆ ((lt3H w).erase s).erase (tcRow w) := by
    intro r hr
    obtain ⟨hrH, hne⟩ := mem_filter.1 hr
    exact mem_erase.2 ⟨fun h => hne (fun j _ => by rw [h]), hrH⟩
  have hBc : (lt3HB S (tcRow w) ((lt3H w).erase s)).card ≤ 1 := by
    have := card_le_card hB
    rw [card_erase_of_mem htc] at this
    omega
  have hV2 : (lt3RealData w e S (tcRow w) ((lt3H w).erase s) σ).V2 ≤ 1 := by
    show ∑ r ∈ lt3HB S (tcRow w) ((lt3H w).erase s), Pw w r / σ ≤ 1
    refine (sum_le_card_nsmul _ _ 1 fun r _ => hw1 r).trans ?_
    rw [nsmul_eq_mul, mul_one]
    exact_mod_cast hBc
  refine ⟨?_, hV2⟩
  have : ((((lt3H w).erase s).card : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hH2
  linarith

/-- **The chosen table satisfies the windowed RL-u conclusion** for a member of `lt3WSel` with `s ∈ Sp \ {tc}`
and `|H \ {s}| ≤ 2`. -/
theorem lt3UTab_spec {s : State N} {ε γ : ℝ} {w : Param N} (hw : w ∈ openCube N) {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {r0 : State N}
    (hk : (({a, b, c} : Finset (Fin N)), r0) ∈ lt3WSel s ε γ 8319999 w)
    (hsH : s ∈ lt3H w) (hstc : s ≠ tcRow w) (hH2 : ((lt3H w).erase s).card ≤ 2) :
    lt3Uthr (lt3Uds w {a, b, c} s) - 1 / 1000 ≤ (lt3UTab w (pkE3 hab hac hbc) {a, b, c} s).2 ∧
      RLUWin (lt3Uds w {a, b, c} s) (lt3URestD w (pkE3 hab hac hbc) {a, b, c} s)
        (lt3Uwu w (pkE3 hab hac hbc) {a, b, c} s) (lt3UX w (pkE3 hab hac hbc) s) (lt3UF w (pkE3 hab hac hbc) s)
        (1 / 320000) (lt3UTab w (pkE3 hab hac hbc) {a, b, c} s).2 (lt3UTab w (pkE3 hab hac hbc) {a, b, c} s).1 := by
  classical
  obtain ⟨-, -, -, -, -, hSWQ, -⟩ := lt3W_mem hk
  set e := pkE3 hab hac hbc with he
  have hS := pkE3_S hab hac hbc
  set S : Finset (Fin N) := {a, b, c} with hSdef
  have heS : ∀ i, e i ∈ S := fun i => (hS _).2 ⟨i, rfl⟩
  have hS0 : S.Nonempty := ⟨e 0, heS 0⟩
  set tc := tcRow w with htc
  have hσ0 := b1_Pw_pos hw tc
  set H' := (lt3H w).erase s with hH'
  have htcH' : tc ∈ H' := mem_erase.2 ⟨fun h => hstc h.symm, mem_insert_self _ _⟩
  -- the good units
  have hSpC : lt3SpC s w := ⟨(mem_insert.1 hsH).resolve_left hstc, hstc⟩
  have hGU : ∀ i, 17 / 20 ≤ clamp01 (w tc (e i)) ∧ 7 / 8 ≤ clamp01 (w s (e i)) := by
    intro i
    have h1 : e i ∈ lt3Q s ε γ w := lt3WQ_sub _ _ _ _ _ (hSWQ (heS i))
    have h2 : e i ∈ lt3Top s w ε := (mem_sdiff.1 ((lt3QOf_spec _ _ _).1 h1)).1
    have h3 : lt3Top s w ε = lt3TopP s w ε := by simp [lt3Top, hSpC]
    rw [h3] at h2
    have h4 := lt3TopP_sub s w ε h2
    simp only [lt3GoodU, mem_filter] at h4
    exact h4.2
  -- the unscaled data
  set d0 := lt3URest0 w e S s with hd0
  have hd0e : lt3RealData w e S (tcRow w) ((lt3H w).erase s) (Pw w tc) = d0 := rfl
  have hd0e' : lt3RealData w e S tc H' (Pw w tc) = d0 := rfl
  have hPw0 : ∀ r, Pw w r ≤ Pw w tc := fun r => Pw_le_tcRow w r
  obtain ⟨hG1n0, hF1n0, -, -, hG1V0, hF1V0, -, -, hV1n0, hV2n0, -⟩ := lt3RD_bounds w e S tc H' hσ0 hPw0
  have hw0' : ∀ r, 0 ≤ Pw w r / Pw w tc := fun r => div_nonneg (Pw_nonneg w r) hσ0.le
  have htcA : tc ∈ lt3HA S tc H' := mem_filter.2 ⟨htcH', fun _ _ => rfl⟩
  have hone : Pw w tc / Pw w tc = 1 := div_self hσ0.ne'
  have hG1lo : ∀ i, 17 / 20 ≤ d0.G1 i := by
    intro i
    have h := single_le_sum (f := fun r => Pw w r / Pw w tc * clamp01 (w r (e i)))
      (fun r _ => mul_nonneg (hw0' r) (clamp01_nonneg _)) htcA
    simp only [hone, one_mul] at h
    exact (hGU i).1.trans h
  have hV1lo : 1 ≤ d0.V1 := by
    have h := single_le_sum (f := fun r => Pw w r / Pw w tc) (fun r _ => hw0' r) htcA
    simp only [hone] at h
    exact h
  obtain ⟨hV1_0, hV2_0⟩ := lt3U_V_bounds e hS0 htcH' hH2 hσ0 hPw0
  rw [hd0e] at hV1_0 hV2_0
  -- the window
  set wb : ℝ := 1 / ((8319999 + 1 : ℕ) : ℝ) with hwb
  have hwb0 : 0 ≤ wb := by positivity
  have hwin : ∀ r ∈ H', ∀ i i' : Fin 3,
      |clamp01 (w r (e i)) - clamp01 (w r (e i'))| ≤ wb ∧
      |clamp01 (w (flip r (e i)) (e i)) - clamp01 (w (flip r (e i')) (e i'))| ≤ wb :=
    fun r hr i i' => lt3WQ_window s ε γ 8319999 w (hSWQ (heS i)) (hSWQ (heS i'))
      (lt3H_sub_base s w (mem_of_mem_erase hr))
  have hH'c : (H'.card : ℝ) ≤ 13 := by exact_mod_cast hH2.trans (by norm_num)
  have hd0w : d0.win (13 * wb) :=
    RLDR.win_mono (lt3RD_win w e S tc H' hσ0 hPw0 hwb0 hwin) (mul_le_mul_of_nonneg_right hH'c hwb0)
  -- the scale
  obtain ⟨hl1, hlG, hlV⟩ := lt3Ulam_bounds hw e S s
  set l := lt3Ulam w e S s with hl
  have hl2 : l ≤ 2 := hlV.trans (max_le (by norm_num) hV1_0)
  have hlV1 : l ≤ d0.V1 := hlV.trans (max_le hV1lo le_rfl)
  have hlwin : ∀ i, 4 / 5 * l ≤ d0.G1 i := by
    intro i
    have hmax : ∀ j, d0.G1 j ≤ d0.G1 i + 13 * wb := fun j => by
      have h1 := (hd0w j).1
      have h2 := rlMin3R_le d0.G1 i
      linarith
    have hl' : l ≤ max 1 (d0.G1 i + 13 * wb) := by
      rw [hl]; unfold lt3Ulam
      refine max_le_max le_rfl (max_le ?_ (max_le ?_ ?_)) <;> exact hmax _
    have hwbs : 13 * wb ≤ 1 / 100 := by rw [hwb]; norm_num
    have := hG1lo i
    clear_value l wb d0
    rcases le_total 1 (d0.G1 i + 13 * wb) with h | h
    · rw [max_eq_right h] at hl'; linarith
    · rw [max_eq_left h] at hl'; linarith
  set σ := lt3Usig w e S s with hσdef
  have hσe : σ = l * Pw w tc := rfl
  have hσ1 : Pw w tc ≤ σ := lt3Usig_ge hw e S s
  have hσ : 0 < σ := hσ0.trans_le hσ1
  have hPw : ∀ r, Pw w r ≤ σ := fun r => (hPw0 r).trans hσ1
  set dR := lt3URestD w e S s with hdR
  have hdRe : dR = lt3RealData w e S tc H' (l * Pw w tc) := rfl
  obtain ⟨sG1, sF1, sV1, sV2⟩ := lt3RD_scale w e S tc H' hσ0.ne' (by linarith : l ≠ 0)
  simp only [hd0e'] at sG1 sF1 sV1 sV2
  have hl0 : 0 < l := by linarith
  obtain ⟨hG1n, hF1n, hG2n, hF2n, hG1V, hF1V, hG2V, hF2V, hV1n, hV2n, -⟩ := lt3RD_bounds w e S tc H' hσ hPw
  have hdw : dR.win (13 * wb) :=
    RLDR.win_mono (lt3RD_win w e S tc H' hσ hPw hwb0 hwin) (mul_le_mul_of_nonneg_right hH'c hwb0)
  have qG1 : ∀ i, 4 / 5 ≤ dR.G1 i := fun i => by
    rw [hdRe, sG1 i, le_div_iff₀ hl0]; linarith [hlwin i]
  have qG11 : ∀ i, dR.G1 i ≤ 1 := fun i => by
    rw [hdRe, sG1 i, div_le_one hl0]; exact hlG i
  have qF12 : ∀ i, dR.F1 i ≤ 2 := fun i => by
    rw [hdRe, sF1 i]
    exact (div_le_self (hF1n0 i) hl1).trans ((hF1V0 i).trans hV1_0)
  have qV1 : 1 ≤ dR.V1 := by rw [hdRe, sV1, le_div_iff₀ hl0]; linarith
  have qV21 : dR.V2 ≤ 1 := by rw [hdRe, sV2]; exact (div_le_self hV2n0 hl1).trans hV2_0
  -- s's entries
  have hsB : s ∈ lt3Base s w := lt3H_sub_base s w hsH
  have hsw : ∀ i i' : Fin 3, |clamp01 (w s (e i)) - clamp01 (w s (e i'))| ≤ wb ∧
      |clamp01 (w (flip s (e i)) (e i)) - clamp01 (w (flip s (e i')) (e i'))| ≤ wb :=
    fun i i' => lt3WQ_window s ε γ 8319999 w (hSWQ (heS i)) (hSWQ (heS i')) hsB
  have hwb13 : wb ≤ 13 * wb := by linarith
  have hxw : ∀ i, lt3UX w e s i - rlMin3R (lt3UX w e s) ≤ 13 * wb :=
    sub_rlMin3R_le fun i i' => ((abs_le.1 (hsw i i').1).2).trans hwb13
  have hfw : ∀ i, lt3UF w e s i - rlMin3R (lt3UF w e s) ≤ 13 * wb :=
    sub_rlMin3R_le fun i i' => ((abs_le.1 (hsw i i').2).2).trans hwb13
  have hwu0 : 0 ≤ lt3Uwu w e S s := div_nonneg (Pw_nonneg w s) hσ.le
  have hwu1 : lt3Uwu w e S s ≤ 1 := (div_le_one hσ).2 (hPw s)
  have hx0 : ∀ i, (if lt3Uds w S s then 7 / 8 else 9 / 16 : ℝ) ≤ lt3UX w e s i := fun i => by
    have := (hGU i).2
    show _ ≤ clamp01 (w s (e i))
    split_ifs <;> linarith
  have hn : ((13 * wb) + 1 / ((640000 : ℕ) : ℝ)) = 1 / 320000 := by rw [hwb]; push_cast; norm_num
  obtain ⟨T, x0, hx0T, hT⟩ := rlu_real_window (lt3Uds w S s) dR (lt3Uwu w e S s) (lt3UX w e s) (lt3UF w e s)
    (n := 640000) (by norm_num) (by norm_num) (by positivity) hdw hxw hfw (by rw [hn]; norm_num)
    qG1 qG11 hF1n qF12 qV1 hF1V hG2n hF2n hG2V hF2V qV21 hwu0 hwu1 hx0 (fun i => clamp01_le_one _)
    (fun i => clamp01_nonneg _) (fun i => clamp01_le_one _)
  rw [hn] at hT
  have hex : ∃ p : TcTab × ℝ, lt3Uthr (lt3Uds w S s) - 1 / 1000 ≤ p.2 ∧
      RLUWin (lt3Uds w S s) dR (lt3Uwu w e S s) (lt3UX w e s) (lt3UF w e s) (1 / 320000) p.2 p.1 :=
    ⟨(T, x0), by unfold lt3Uthr; exact hx0T, hT⟩
  exact Classical.epsilon_spec hex

/-! ### Resampling the private entries keeps the member's data -/

/-- **The member's RL-u data, hence its table, are unchanged by resampling `Priv`.** -/
theorem lt3UData_replE {s : State N} {ε γ : ℝ} {nb : ℕ} {w : Param N} {a b c : Fin N} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) {r0 : State N} (hk : (({a, b, c} : Finset (Fin N)), r0) ∈ lt3WSel s ε γ nb w)
    (hsH : s ∈ lt3H w) (η : Param N) :
    lt3URestD (replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η) (pkE3 hab hac hbc) {a, b, c} s =
        lt3URestD w (pkE3 hab hac hbc) {a, b, c} s ∧
      lt3Uds (replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η) {a, b, c} s = lt3Uds w {a, b, c} s ∧
      lt3Uwu (replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η) (pkE3 hab hac hbc) {a, b, c} s =
        lt3Uwu w (pkE3 hab hac hbc) {a, b, c} s ∧
      lt3UTab (replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η) (pkE3 hab hac hbc) {a, b, c} s =
        lt3UTab w (pkE3 hab hac hbc) {a, b, c} s := by
  classical
  obtain ⟨ht, hH, hrow, hflip, hPt, hPw⟩ := lt3W_replE_frame hab hac hbc hk η
  set w' := replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η with hw'
  have hRD : ∀ σ : ℝ, lt3RealData w' (pkE3 hab hac hbc) {a, b, c} (tcRow w') ((lt3H w').erase s) σ =
      lt3RealData w (pkE3 hab hac hbc) {a, b, c} (tcRow w) ((lt3H w).erase s) σ := by
    intro σ
    rw [ht, hH]
    unfold lt3RealData
    congr 1 <;> (try funext i) <;> refine sum_congr rfl fun r hr => ?_ <;>
      simp only [hPw r (mem_of_mem_erase (mem_filter.1 hr).1), hrow r (mem_of_mem_erase (mem_filter.1 hr).1),
        hflip r (mem_of_mem_erase (mem_filter.1 hr).1)]
  have h0 : lt3URest0 w' (pkE3 hab hac hbc) {a, b, c} s = lt3URest0 w (pkE3 hab hac hbc) {a, b, c} s := by
    unfold lt3URest0; rw [hRD, ht, hPt]
  have hσ : lt3Usig w' (pkE3 hab hac hbc) {a, b, c} s = lt3Usig w (pkE3 hab hac hbc) {a, b, c} s := by
    unfold lt3Usig lt3Ulam; rw [h0, ht, hPt]
  have hD : lt3URestD w' (pkE3 hab hac hbc) {a, b, c} s = lt3URestD w (pkE3 hab hac hbc) {a, b, c} s := by
    unfold lt3URestD; rw [hσ, hRD]
  have hds : lt3Uds w' {a, b, c} s = lt3Uds w {a, b, c} s := by unfold lt3Uds; rw [ht]
  have hwu : lt3Uwu w' (pkE3 hab hac hbc) {a, b, c} s = lt3Uwu w (pkE3 hab hac hbc) {a, b, c} s := by
    unfold lt3Uwu; rw [hσ, hPw s hsH]
  have hX : lt3UX w' (pkE3 hab hac hbc) s = lt3UX w (pkE3 hab hac hbc) s := by
    funext i; unfold lt3UX; rw [hrow s hsH]
  have hF : lt3UF w' (pkE3 hab hac hbc) s = lt3UF w (pkE3 hab hac hbc) s := by
    funext i; unfold lt3UF; rw [hflip s hsH]
  refine ⟨hD, hds, hwu, ?_⟩
  unfold lt3UTab
  rw [hD, hds, hwu, hX, hF]

/-! ### The success region -/

/-- The two boxes of an `s`-member: the rest box and `s`'s box (targets read from `w`). -/
def lt3URegion (w : Param N) (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) (s : State N) (ρ : ℝ) : Set (Param N) :=
  lt3Box e S (tcRow w) ((lt3H w).erase s)
      (lt3Tgt (lt3URestD w e S s)
        (lt3URest w e s (lt3Uds w S s) (lt3Uwu w e S s) (lt3UTab w e S s).1)) ρ ∩
    lt3Box e S s {s} (fun u i => clamp01 ((lt3UTab w e S s).1.Y u i)) ρ

/-- **Lemma TC' for `s ∈ Sp \ {tc}`, packaged at a member** (deterministic, `t = 1/80`): `φ_s(S) ≥ β/4`. -/
theorem lt3_u_quarter {w : Param N} (hw : w ∈ openCube N) (s : State N) (hsH : s ∈ lt3H w) (hstc : s ≠ tcRow w)
    (hH2 : ((lt3H w).erase s).card ≤ 2) {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hSp : (lt2Sp w).card < 12)
    (hH : ∀ r ∈ lt3H w, (∀ j ∈ ({a, b, c} : Finset (Fin N)), r j = tcRow w j) ∨
      (∀ j ∈ ({a, b, c} : Finset (Fin N)), r j ≠ tcRow w j))
    (hT : lt3Uthr (lt3Uds w {a, b, c} s) - 1 / 1000 ≤ (lt3UTab w (pkE3 hab hac hbc) {a, b, c} s).2 ∧
      RLUWin (lt3Uds w {a, b, c} s) (lt3URestD w (pkE3 hab hac hbc) {a, b, c} s)
        (lt3Uwu w (pkE3 hab hac hbc) {a, b, c} s) (lt3UX w (pkE3 hab hac hbc) s) (lt3UF w (pkE3 hab hac hbc) s)
        (1 / 320000) (lt3UTab w (pkE3 hab hac hbc) {a, b, c} s).2 (lt3UTab w (pkE3 hab hac hbc) {a, b, c} s).1)
    (hreg : w ∈ lt3URegion w (pkE3 hab hac hbc) {a, b, c} s (1 / 4160000))
    {φL η : ℝ}
    (hlight : ∀ (t0 : State N) (u : Fin (2 ^ 3)) (i : Fin 3),
      |lt3Light w {a, b, c} (lt3H w) (pkFlip (pkE3 hab hac hbc) t0 u) (pkE3 hab hac hbc i) -
        lt3Light w {a, b, c} (lt3H w) t0 (pkE3 hab hac hbc i)| ≤ φL)
    (hφL : φL ≤ Pw w (tcRow w) / 320000) (hη0 : 0 ≤ η)
    (hlev : ∀ Y ⊆ ({a, b, c} : Finset (Fin N)), ∀ t', ∀ i ∈ ({a, b, c} : Finset (Fin N)),
      |Num w {a, b, c} Y t' i - lvK 3 * Zs w| ≤ η)
    (hηs : η ^ 2 ≤ Pw w (tcRow w) * (lvK 3 * Zs w) / (8 * 10 ^ 7))
    (hE0 : 6 * η / ((lvK 3 * Zs w - η) * Real.log 2) ≤ lt3E0u (1 / 2)) :
    1 / 4 * betaW w ≤ phi (flipP s w) s {a, b, c} := by
  classical
  set e := pkE3 hab hac hbc with he
  have hS := pkE3_S hab hac hbc
  set T := (lt3UTab w e {a, b, c} s).1 with hTdef
  set x0 := (lt3UTab w e {a, b, c} s).2 with hx0def
  obtain ⟨hx0, hTw⟩ := hT
  obtain ⟨hregR, hregT⟩ := hreg
  have hY01 := hTw.2.2.2.2.2.1
  have hc45 := hTw.2.1
  -- `s`'s box with the raw targets
  have hboxT : w ∈ lt3Box e {a, b, c} s {s} (fun u i => T.Y u i) (1 / 4160000) := by
    intro x hx
    have h := hregT x hx
    obtain ⟨hx1, hv⟩ := mem_lt3BoxIdx.1 hx
    have hx1' : x.1 = s := mem_singleton.1 hx1
    have hag : ∀ j ∈ ({a, b, c} : Finset (Fin N)), x.1 j = s j := fun j _ => by rw [hx1']
    simp only [lt3BoxTgt, if_pos hag] at h ⊢
    have hcl : clamp01 (T.Y x.2.1 x.2.2) = T.Y x.2.1 x.2.2 :=
      clamp01_of_mem ⟨(hY01 x.2.1 x.2.2 hv).1, (hY01 x.2.1 x.2.2 hv).2⟩
    rwa [hcl] at h
  -- the effect side
  have hρY : ∀ (u : Fin (2 ^ 3)) (i : Fin 3), ¬((u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ)) →
      |clamp01 (w (pkFlip e s u) (e i)) - T.Y u i| ≤ 1 / 4160000 := by
    intro u i hv
    have h := hboxT (s, u, i) (mem_lt3BoxIdx.2 ⟨mem_singleton_self _, hv⟩)
    simp only [lt3BoxE, lt3BoxTgt] at h
    rwa [if_pos (fun _ _ => trivial)] at h
  have hax : (1 / 2 : ℝ) ≤ x0 := by
    unfold lt3Uthr at hx0; split_ifs at hx0 <;> linarith
  have heff := lt3_heff_u hw s e hS hTw (a := 1 / 2) (by norm_num) hax (by norm_num) (by norm_num) (by norm_num) hρY
  -- the scale
  have hsag := lt3Uds_spec (hH s hsH)
  have hσ1 := lt3Usig_ge hw e {a, b, c} s
  have hσ0 := b1_Pw_pos hw (tcRow w)
  have hσ2 : lt3Usig w e {a, b, c} s ≤ 2 * Zs w := by
    have hS0 : ({a, b, c} : Finset (Fin N)).Nonempty := ⟨a, by simp⟩
    have htcH' : tcRow w ∈ (lt3H w).erase s := mem_erase.2 ⟨fun h => hstc h.symm, mem_insert_self _ _⟩
    obtain ⟨hV1, -⟩ := lt3U_V_bounds e hS0 htcH' hH2 hσ0 (fun r => Pw_le_tcRow w r)
    obtain ⟨hl1, -, hlV⟩ := lt3Ulam_bounds hw e {a, b, c} s
    have hl2 : lt3Ulam w e {a, b, c} s ≤ 2 := hlV.trans (max_le (by norm_num) hV1)
    have hZ : Pw w (tcRow w) ≤ Zs w :=
      single_le_sum (f := fun r => Pw w r) (fun r _ => Pw_nonneg w r) (mem_univ _)
    unfold lt3Usig
    nlinarith
  have hA0 : 0 ≤ lvK 3 * Zs w := mul_nonneg (lvK_pos 3).le (b1_Zs_pos hw).le
  have hφL' : φL ≤ lt3Usig w e {a, b, c} s / 320000 := hφL.trans (div_le_div_of_nonneg_right hσ1 (by norm_num))
  have hηs' : η ^ 2 ≤ lt3Usig w e {a, b, c} s * (lvK 3 * Zs w) / (8 * 10 ^ 7) :=
    hηs.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hσ1 hA0) (by norm_num))
  have hmain := lt3_TCprime_u hw s hab hac hbc (lt3H w) (lt3H_card hSp) hsH (lt3Uds w {a, b, c} s) hsag hH
    hσ1 hσ2 T hTw (by norm_num) (by norm_num) (by norm_num) hregR hboxT hlight hφL' hη0 hlev hηs' hE0 heff
  have hβ : 0 ≤ betaW w := div_nonneg (Pw_nonneg w _) (b1_Zs_pos hw).le
  have hlt := levTrip_gt
  have k1 : (577 / 1000 : ℝ) * (4 / 5) ≤ levTrip * T.c0 := mul_le_mul hlt.le hc45 (by norm_num) levTrip_pos.le
  have k2 : (1 : ℝ) / 4 ≤ levTrip * T.c0 * (79 / 80) := by nlinarith
  calc 1 / 4 * betaW w ≤ levTrip * T.c0 * (79 / 80) * betaW w := mul_le_mul_of_nonneg_right k2 hβ
    _ ≤ phi (flipP s w) s {a, b, c} := hmain

/-- **A non-adverse member with `s ∈ Sp \ {tc}` and `|H \ {s}| ≤ 2` has a success region of probability
`≥ lt3pT`** (`N` large, any band level `L ≥ lt3Lc`). -/
theorem lt3_u_member_ev {L : ℝ} (hL : lt3Lc ≤ L) : ∀ᶠ N : ℕ in atTop,
    ∀ (s : State N) (w : Param N) (S : Finset (Fin N)),
    w ∈ openCube N → (lt2Sp w).card < 12 → (S, s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w →
    S ∉ lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w → s ∈ lt3H w → s ≠ tcRow w → ((lt3H w).erase s).card ≤ 2 →
    LT3MemberOK L lt3pT s w S := by
  have hL0 : 0 < L := lt3Lc_pos.trans_le hL
  have hLκ : 768000 * lt3κ ≤ (1 / 80 : ℝ) * L := by have := lt3Lc_κ; linarith
  filter_upwards [bd_band (t := 1 / 80) (L := L) (by norm_num) hL0, bd_E0_ev (lt3E0u_pos (a := 1 / 2) (by norm_num)),
    bd_tc_Sp_ev hL0, lt3_pert_ev (t := 1 / 80) (by norm_num)] with N hBand hE0 hTc hPert
  intro s w S hw hSp hk hnadv hsH hstc hH2
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hS⟩ := lt3WSel_three hk
  have hS' : S = {a, b, c} := hS
  subst hS'
  set A := stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w with hA
  set e := pkE3 hab hac hbc with he
  have hSe := pkE3_S hab hac hbc
  obtain ⟨-, h7, -, -, -, hSWQ, hag⟩ := lt3W_mem hk
  set tc := tcRow w with htc
  set H' := (lt3H w).erase s with hH'
  set T := (lt3UTab w e {a, b, c} s).1 with hTdef
  have hT := lt3UTab_spec hw hab hac hbc hk hsH hstc hH2
  set ρ : ℝ := 1 / 4160000 with hρ
  set ds := lt3Uds w {a, b, c} s with hds
  set wu := lt3Uwu w e {a, b, c} s with hwu
  set Ur := lt3Box e {a, b, c} tc H' (lt3Tgt (lt3URestD w e {a, b, c} s) (lt3URest w e s ds wu T)) ρ with hUr
  set Ut := lt3Box e {a, b, c} s {s} (fun u i => clamp01 (T.Y u i)) ρ with hUt
  -- blocks
  have hsubR : H'.biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)) ⊆
      (lt3Base s w).biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)) :=
    biUnion_subset_biUnion_of_subset_left _ ((erase_subset _ _).trans (lt3H_sub_base s w))
  have hsubT : ({s} : Finset (State N)).biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)) ⊆
      (lt3Base s w).biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)) :=
    biUnion_subset_biUnion_of_subset_left _ (singleton_subset_iff.2 (lt3H_sub_base s w hsH))
  have hdisj : Disjoint (H'.biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)))
      (({s} : Finset (State N)).biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r))) := by
    rw [Finset.disjoint_biUnion_left]
    intro r hr
    rw [singleton_biUnion]
    have hrH := mem_of_mem_erase hr
    refine lt3WPB_disjoint w (lt3W_mem_base hk (lt3H_sub_base s w hrH)) (lt3W_mem_base hk (lt3H_sub_base s w hsH)) ?_
    intro h
    exact (ne_of_mem_erase hr) (Prod.ext_iff.1 h).2
  have hUrm : MeasurableSet Ur := lt3Box_mset _ _ _ _ _ _
  have hUtm : MeasurableSet Ut := lt3Box_mset _ _ _ _ _ _
  have hUrd := lt3Box_detOn hSe tc H' (lt3Tgt (lt3URestD w e {a, b, c} s) (lt3URest w e s ds wu T)) ρ
  have hUtd := lt3Box_detOn hSe s {s} (fun u i => clamp01 (T.Y u i)) ρ
  refine ⟨Ur ∩ Ut, hUrm.inter hUtm, (hUrd.mono hsubR).inter (hUtd.mono hsubT), ?_, ?_⟩
  · -- probability
    rw [cubeM_inter_eq_mul_of_detOnE hdisj hUrm hUtm hUrd hUtd]
    have hSQ : ({a, b, c} : Finset (Fin N)) ⊆ lt3Q s (1 / 21) lt3γ w := hSWQ.trans (lt3WQ_sub _ _ _ _ _)
    have hQ7 : 7 ≤ (lt3Q s (1 / 21) lt3γ w).card := h7.trans (card_le_card (lt3WQ_sub _ _ _ _ _))
    have hσ1 := lt3Usig_ge hw e {a, b, c} s
    have hσ : 0 < lt3Usig w e {a, b, c} s := (b1_Pw_pos hw tc).trans_le hσ1
    obtain ⟨hG1n, hF1n, hG2n, hF2n, hG1V, hF1V, hG2V, hF2V, hV1n, hV2n, -⟩ :=
      lt3RD_bounds w e {a, b, c} tc H' hσ (fun r => (Pw_le_tcRow w r).trans hσ1)
    have hlw := rlLoR_wd_bounds _ hG1n hF1n hG2n hF2n hG1V hF1V hG2V hF2V hV1n hV2n
    have hTg := lt3Tgt_spec (lt3URestD w e {a, b, c} s) (lt3URest w e s ds wu T) (fun u i => hT.2.2.2.2.2.1 u i)
      (fun u i => (hlw u i).2.1)
    have hρ0 : (0 : ℝ) ≤ ρ := by rw [hρ]; norm_num
    have hρ1 : ρ ≤ 1 := by rw [hρ]; norm_num
    have hpR := lt3Box_prob hSe hSQ hQ7 (H := H') (tc := tc)
      (fun r hr => hag r (lt3H_sub_base s w (mem_of_mem_erase hr))) (fun u i => (hTg u i).2) hρ0 hρ1
    have hpT := lt3Box_prob hSe hSQ hQ7 (H := {s}) (tc := s)
      (fun r hr => by rw [mem_singleton.1 hr]; exact Or.inl fun j _ => rfl)
      (τ := fun u i => clamp01 (T.Y u i)) (fun u i => ⟨clamp01_nonneg _, clamp01_le_one _⟩) hρ0 hρ1
    rw [card_singleton] at hpT
    have hH'c : H'.card ≤ 2 := hH2
    have hpow : ρ ^ 234 ≤ ρ ^ (18 * H'.card) * ρ ^ (18 * 1) := by
      rw [← pow_add]
      exact pow_le_pow_of_le_one hρ0 hρ1 (by omega)
    unfold lt3pT
    rw [← hρ]
    calc ENNReal.ofReal (ρ ^ 234) ≤ ENNReal.ofReal (ρ ^ (18 * H'.card) * ρ ^ (18 * 1)) :=
          ENNReal.ofReal_le_ofReal hpow
      _ = ENNReal.ofReal (ρ ^ (18 * H'.card)) * ENNReal.ofReal (ρ ^ (18 * 1)) :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ cubeM N Ur * cubeM N Ut := mul_le_mul' hpR hpT
  · -- the conclusion
    rintro η ⟨hηr, hηt⟩ hw' hZ' hβ' hbd' hSp'
    set w' := replE A w η with hw'def
    obtain ⟨ht, hHw, hrow, hflip, hPt, hPw⟩ := lt3W_replE_frame hab hac hbc hk η
    obtain ⟨hD, hds', hwu', hTab⟩ := lt3UData_replE hab hac hbc hk hsH η
    have hk' : (({a, b, c} : Finset (Fin N)), s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w' := by
      rw [hw'def, hA, lt3W_replE_sel]; exact hk
    have hF' := (lt3W_mem hk').2.2.2.1
    have hAdv' : ({a, b, c} : Finset (Fin N)) ∉ lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w' := by
      rw [hw'def, hA, lt3Adv_replE]; exact hnadv
    have hsH' : s ∈ lt3H w' := by rw [hHw]; exact hsH
    have hstc' : s ≠ tcRow w' := by rw [ht]; exact hstc
    have hH2' : ((lt3H w').erase s).card ≤ 2 := by rw [hHw]; exact hH2
    -- the region at `w'`
    have hreg' : w' ∈ lt3URegion w' e {a, b, c} s ρ := by
      have hU' : lt3URest w' e s ds wu T = lt3URest w e s ds wu T := by
        funext u i
        unfold lt3URest
        have hrow' : w' s = w s := hrow _ hsH
        have hflip' : ∀ i : Fin 3, w' (flip s (e i)) (e i) = w (flip s (e i)) (e i) := hflip _ hsH
        simp only [hrow', hflip']
      unfold lt3URegion
      rw [hds', hwu', hTab, hD, ← hds, ← hwu, ← hTdef, hU', ht, hHw]
      have hdet : ∀ q ∈ (lt3H w).biUnion (fun r => lt3PB (({a, b, c} : Finset (Fin N)), r)),
          η q.1 q.2 = w' q.1 q.2 := by
        rintro ⟨q1, q2⟩ hq
        obtain ⟨r, hr, hq'⟩ := mem_biUnion.1 hq
        have hqA : (q1, q2) ∈ A := mem_biUnion.2 ⟨(({a, b, c} : Finset (Fin N)), r),
          lt3W_mem_base hk (lt3H_sub_base s w hr), hq'⟩
        show η q1 q2 = (if (q1, q2) ∈ A then η q1 q2 else w q1 q2)
        rw [if_pos hqA]
      refine ⟨(hUrd η w' fun q hq => hdet q ?_).1 hηr, (hUtd η w' fun q hq => hdet q ?_).1 hηt⟩
      · exact (biUnion_subset_biUnion_of_subset_left _ (erase_subset _ _)) hq
      · exact (biUnion_subset_biUnion_of_subset_left _ (singleton_subset_iff.2 hsH)) hq
    -- the table at `w'`
    have hT' := lt3UTab_spec hw' hab hac hbc hk' hsH' hstc' hH2'
    -- agreement classes at `w'`
    obtain ⟨-, -, -, -, -, hSWQ', hag'⟩ := lt3W_mem hk'
    have hSQ' : ({a, b, c} : Finset (Fin N)) ⊆ lt3Q s (1 / 21) lt3γ w' := hSWQ'.trans (lt3WQ_sub _ _ _ _ _)
    have hHag : ∀ r ∈ lt3H w', (∀ j ∈ ({a, b, c} : Finset (Fin N)), r j = tcRow w' j) ∨
        (∀ j ∈ ({a, b, c} : Finset (Fin N)), r j ≠ tcRow w' j) := fun r hr => by
      rcases hag' r (lt3H_sub_base s w' hr) with h | h
      · exact Or.inl fun j hj => h j (hSQ' hj)
      · exact Or.inr fun j hj => h j (hSQ' hj)
    -- the light part
    have htc' : tcRow w' ∈ lt2Sp w' := hTc w' hw' hZ' hβ'
    have hHalf := lt3_hHalf_of_not_adv s (1 / 21) lt3γ 8319999 lt3κ_pos.le htc' hab hac hbc hF' hAdv'
    have hφH : 48 * lt3κ * sigN N ≤ (1 / 80) / 8000 * Pw w' (tcRow w') :=
      lt3_phiH_le (κ := lt3κ) (t := 1 / 80) (L := L) lt3κ_pos.le (by norm_num) hLκ hZ' hβ'
    obtain ⟨hP', hη0, hηs, hlev⟩ := hBand w' hbd' hZ' hβ' hSp'
    obtain ⟨-, hE0'⟩ := hE0 w' hbd' hZ'
    set Ep := ((((stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w').card * (1 + 8) : ℕ) : ℝ) *
      (Real.exp (-(3 / 10 * (N : ℝ))) + Real.exp (-(lt2x1 * N)))) with hEp
    have hPcard := (lt3W_Priv_card s (1 / 21) lt3γ 8319999 w').trans
      (Nat.mul_le_mul_left 24 (lt3WSel_card s (1 / 21) lt3γ 8319999 hSp'))
    have hEp2 : 2 * Ep ≤ (1 / 80) / 8000 * Pw w' (tcRow w') := by
      have h1 := hPert _ hPcard
      have h2 : (1 / 80 : ℝ) / 8000 * Real.exp (-((lt2x1 - 1 / 800) * N)) ≤ (1 / 80) / 8000 * Pw w' (tcRow w') :=
        mul_le_mul_of_nonneg_left hP' (by norm_num)
      rw [hEp]; linarith
    have hS3 : ({a, b, c} : Finset (Fin N)).card ≤ 3 := card_le_three
    have hlight : ∀ (t0 : State N) (u : Fin (2 ^ 3)) (i : Fin 3),
        |lt3Light w' {a, b, c} (lt3H w') (pkFlip e t0 u) (e i) - lt3Light w' {a, b, c} (lt3H w') t0 (e i)| ≤
          48 * lt3κ * sigN N + 2 * Ep := by
      intro t0 u i
      have h1 := abs_le.1 (lt3Light_pert s (1 / 21) lt3γ 8319999 w' hS3 (H := lt3H w') (subset_insert _ _)
        (pkFlip e t0 u) (e i))
      have h2 := abs_le.1 (lt3Light_pert s (1 / 21) lt3γ 8319999 w' hS3 (H := lt3H w') (subset_insert _ _) t0 (e i))
      have h3 := abs_le.1 (hHalf t0 u i)
      rw [← hEp] at h1 h2
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
    have hφL : 48 * lt3κ * sigN N + 2 * Ep ≤ Pw w' (tcRow w') / 320000 := by
      have e1 : (1 / 80 : ℝ) / 8000 * Pw w' (tcRow w') = Pw w' (tcRow w') / 640000 := by ring
      rw [e1] at hφH hEp2
      linarith
    have hηs' : bdEta w' ^ 2 ≤ Pw w' (tcRow w') * (lvK 3 * Zs w') / (8 * 10 ^ 7) := by
      have e1 : (1 / 80 : ℝ) / 10 ^ 6 * Pw w' (tcRow w') * (lvK 3 * Zs w') =
          Pw w' (tcRow w') * (lvK 3 * Zs w') / (8 * 10 ^ 7) := by ring
      linarith
    exact lt3_u_quarter hw' s hsH' hstc' hH2' hab hac hbc hSp' hHag hT' hreg' hlight hφL hη0
      (hlev a b c hab hac hbc) hηs' hE0'

end Census
end IIT
