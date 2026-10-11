/-
Census, B1 LTBetaHi, RL-u part 2c: **the cause side for a heavy current state `s ≠ tc`** (two targets).

In the RL-u configuration `s`'s private entries are pinned to the table `Y` of the certificate (they are also effect
entries), with weight `wu = P(s)/σ` and pattern index `uIdx ds v` (`D_u = ∅` or `S`), while the other heavy rows
(`H \ {s}`, INCLUDING `tc`) realise the rest `M - wu · uEnt(x, f, Y)` through the single-target box of Lemma M.

* `lt3_hdec_u` (two-target L6): `|Num(t0 ⊕ u, e i) - (σ M(Ts ⊕ u, i) + light)| ≤ σ ((V1r + V2r) ρ + wu ρ) + φL`.
-/
import IIT.Census.B1LTHiUE
import IIT.Census.B1LTHiTcC

namespace IIT
namespace Census

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-- `s`'s merged row at pattern `v`. -/
lemma lt3_u_merge (e : Fin 3 ↪ Fin N) {S : Finset (Fin N)} (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) {tc s : State N}
    {ds : Bool} (hsag : (ds = false ∧ ∀ j ∈ S, s j = tc j) ∨ (ds = true ∧ ∀ j ∈ S, s j ≠ tc j))
    (v : Fin (2 ^ 3)) : merge S (pkFlip e tc v) s = pkFlip e s (uIdx ds v) := by
  rcases hsag with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · rw [(merge_pkFlip_class e hS (tc := tc) (r := s) v).1 h]
    congr 1; apply Fin.ext; simp [uIdx, uOff]
  · rw [(merge_pkFlip_class e hS (tc := tc) (r := s) v).2 h]
    congr 1; apply Fin.ext; simp [uIdx, uOff, pkCo, Nat.xor_comm]

/-- **(L6, two targets, `s ≠ tc`)** The decomposition of the numerators at `t0 ⊕ u`, `t0 = tc ⊕ Ts`. -/
theorem lt3_hdec_u (w : Param N) (e : Fin 3 ↪ Fin N) {S : Finset (Fin N)} (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
    (tc s : State N) (H : Finset (State N)) {σ ρ φL wu : ℝ} (hσ : 0 < σ) (hσs : Pw w s = wu * σ) (hsH : s ∈ H)
    (hρ : 0 ≤ ρ) (ds : Bool)
    (hsag : (ds = false ∧ ∀ j ∈ S, s j = tc j) ∨ (ds = true ∧ ∀ j ∈ S, s j ≠ tc j))
    (hH : ∀ r ∈ H.erase s, (∀ j ∈ S, r j = tc j) ∨ (∀ j ∈ S, r j ≠ tc j))
    (φ : Fin (2 ^ 3) → Fin 3 → ℝ)
    (hA : ∀ r ∈ lt3HA S tc (H.erase s), ∀ (u : Fin (2 ^ 3)) (i : Fin 3), ¬((u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ)) →
      |clamp01 (w (pkFlip e r u) (e i)) - φ u i| ≤ ρ)
    (hB : ∀ r ∈ lt3HB S tc (H.erase s), ∀ (u : Fin (2 ^ 3)) (i : Fin 3),
      ¬((u : ℕ) = 7 ∨ (u : ℕ) = 7 - 2 ^ (i : ℕ)) → |clamp01 (w (pkFlip e r (pkCo u)) (e i)) - φ u i| ≤ ρ)
    (Y : Fin 8 → Fin 3 → ℝ)
    (hY : ∀ (u : Fin (2 ^ 3)) (i : Fin 3), ¬((u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ)) →
      |clamp01 (w (pkFlip e s u) (e i)) - Y u i| ≤ ρ)
    (M : Fin 8 → Fin 3 → ℝ) (Ts : Fin (2 ^ 3))
    (hbox : ∀ (v : Fin (2 ^ 3)) (i : Fin 3),
      rlLoR (lt3RealData w e S tc (H.erase s) σ) v i + rlWdR (lt3RealData w e S tc (H.erase s) σ) v i * φ v i +
        wu * tcEntR (fun i => clamp01 (w s (e i))) (fun i => clamp01 (w (flip s (e i)) (e i))) Y (uIdx ds v) i =
          rlMR M v i)
    (hlight : ∀ (u : Fin (2 ^ 3)) (i : Fin 3),
      |lt3Light w S H (pkFlip e (pkFlip e tc Ts) u) (e i) - lt3Light w S H (pkFlip e tc Ts) (e i)| ≤ φL)
    (i : Fin 3) (u : Fin (2 ^ 3)) :
    |Num w S S (pkFlip e (pkFlip e tc Ts) u) (e i) -
        (σ * rlMR M ((Ts : ℕ) ^^^ (u : ℕ)) i + lt3Light w S H (pkFlip e tc Ts) (e i))| ≤
      σ * (((lt3RealData w e S tc (H.erase s) σ).V1 + (lt3RealData w e S tc (H.erase s) σ).V2) * ρ + wu * ρ) +
        φL := by
  set v := pkXor Ts u with hv
  set H' := H.erase s with hH'
  have hwu : 0 ≤ wu := by
    have h := Pw_nonneg w s
    rw [hσs] at h
    exact nonneg_of_mul_nonneg_left h hσ
  have hM := lemmaM_blocks w e hS tc H' hσ hρ hH φ hA hB v i
  have hT := lt3_tc_entry w e s hρ Y hY (uIdx ds v) i
  have hb := hbox v i
  have hMv : rlMR M (v : ℕ) i = rlMR M ((Ts : ℕ) ^^^ (u : ℕ)) i := rfl
  rw [hMv] at hb
  rw [num_split_heavy w S H _ (e i), pkFlip_pkFlip, ← add_sum_erase H _ hsH]
  rw [lt3_u_merge e hS hsag v, hσs]
  set X := ((lt3RealData w e S tc H' σ).V1 + (lt3RealData w e S tc H' σ).V2) * ρ with hX
  set h := ∑ r ∈ H', clamp01 (w (merge S (pkFlip e tc v) r) (e i)) * Pw w r with hh
  set ent := tcEntR (fun i => clamp01 (w s (e i))) (fun i => clamp01 (w (flip s (e i)) (e i))) Y (uIdx ds v) i
    with hent
  have hσM : |h - σ * (rlLoR (lt3RealData w e S tc H' σ) v i + rlWdR (lt3RealData w e S tc H' σ) v i * φ v i)| ≤
      σ * X := by
    have e1 : h - σ * (rlLoR (lt3RealData w e S tc H' σ) v i + rlWdR (lt3RealData w e S tc H' σ) v i * φ v i) =
        σ * (h / σ - (rlLoR (lt3RealData w e S tc H' σ) v i +
          rlWdR (lt3RealData w e S tc H' σ) v i * φ v i)) := by
      field_simp
    rw [e1, abs_mul, abs_of_pos hσ]
    exact mul_le_mul_of_nonneg_left hM hσ.le
  have hTσ : |clamp01 (w (pkFlip e s (uIdx ds v)) (e i)) * (wu * σ) - wu * σ * ent| ≤ wu * σ * ρ := by
    have e1 : clamp01 (w (pkFlip e s (uIdx ds v)) (e i)) * (wu * σ) - wu * σ * ent =
        wu * σ * (clamp01 (w (pkFlip e s (uIdx ds v)) (e i)) - ent) := by ring
    rw [e1, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hT (by positivity)
  have hL := hlight u i
  rw [pkFlip_pkFlip] at hL
  have a1 := abs_le.1 hσM
  have a2 := abs_le.1 hL
  have a3 := abs_le.1 hTσ
  have hL' : ∑ x ∈ Hᶜ, clamp01 (w (merge S (pkFlip e tc v) x) (e i)) * Pw w x =
      lt3Light w S H (pkFlip e tc v) (e i) := rfl
  rw [hL', abs_le]
  have hbM : σ * rlMR M ((Ts : ℕ) ^^^ (u : ℕ)) i = σ * (rlLoR (lt3RealData w e S tc H' σ) v i +
      rlWdR (lt3RealData w e S tc H' σ) v i * φ v i) + wu * σ * ent := by
    rw [← hb]; ring
  constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]

/-- The rest table `M - wu · uEnt(x, f, Y)` of an RL-u table at `w`'s shared entries of `s`. -/
noncomputable def lt3URest (w : Param N) (e : Fin 3 ↪ Fin N) (s : State N) (ds : Bool) (wu : ℝ) (T : TcTab) :
    Fin 8 → Fin 3 → ℝ :=
  fun u i => T.M u i - wu * tcEntR (fun i => clamp01 (w s (e i))) (fun i => clamp01 (w (flip s (e i)) (e i))) T.Y
    (uIdx ds u) i

set_option maxHeartbeats 1000000 in
/-- **Lemma TC' for a heavy current state `s ≠ tc`** (deterministic, `t = 1/80`, two targets). -/
theorem lt3_TCprime_u {w : Param N} (hw : w ∈ openCube N) (s : State N) {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (H : Finset (State N)) (hHc : H.card ≤ 13) (hsH : s ∈ H)
    (ds : Bool) (hsag : (ds = false ∧ ∀ j ∈ ({a, b, c} : Finset (Fin N)), s j = tcRow w j) ∨
      (ds = true ∧ ∀ j ∈ ({a, b, c} : Finset (Fin N)), s j ≠ tcRow w j))
    (hH : ∀ r ∈ H, (∀ j ∈ ({a, b, c} : Finset (Fin N)), r j = tcRow w j) ∨
      (∀ j ∈ ({a, b, c} : Finset (Fin N)), r j ≠ tcRow w j))
    {σ ω' ρ φL η E0 x0 : ℝ} (hσ1 : Pw w (tcRow w) ≤ σ) (hσ2 : σ ≤ 2 * Zs w) (T : TcTab)
    (hT : RLUWin ds (lt3RealData w (pkE3 hab hac hbc) {a, b, c} (tcRow w) (H.erase s) σ)
      (Pw w s / σ) (fun i => clamp01 (w s (pkE3 hab hac hbc i)))
      (fun i => clamp01 (w (flip s (pkE3 hab hac hbc i)) (pkE3 hab hac hbc i))) ω' x0 T)
    (hωt : ω' ≤ 1 / 320000) (hρ0 : 0 ≤ ρ) (hρt : 13 * ρ ≤ 1 / 320000)
    (hboxR : w ∈ lt3Box (pkE3 hab hac hbc) {a, b, c} (tcRow w) (H.erase s)
      (lt3Tgt (lt3RealData w (pkE3 hab hac hbc) {a, b, c} (tcRow w) (H.erase s) σ)
        (lt3URest w (pkE3 hab hac hbc) s ds (Pw w s / σ) T)) ρ)
    (hboxT : w ∈ lt3Box (pkE3 hab hac hbc) {a, b, c} s {s} (fun u i => T.Y u i) ρ)
    (hlight : ∀ (t0 : State N) (u : Fin (2 ^ 3)) (i : Fin 3),
      |lt3Light w {a, b, c} H (pkFlip (pkE3 hab hac hbc) t0 u) (pkE3 hab hac hbc i) -
        lt3Light w {a, b, c} H t0 (pkE3 hab hac hbc i)| ≤ φL)
    (hφL : φL ≤ σ / 320000) (hη0 : 0 ≤ η)
    (hlev : ∀ Y ⊆ ({a, b, c} : Finset (Fin N)), ∀ t', ∀ i ∈ ({a, b, c} : Finset (Fin N)),
      |Num w {a, b, c} Y t' i - lvK 3 * Zs w| ≤ η)
    (hηs : η ^ 2 ≤ σ * (lvK 3 * Zs w) / (8 * 10 ^ 7))
    (hE0 : 6 * η / ((lvK 3 * Zs w - η) * Real.log 2) ≤ E0)
    (heff : ∃ te ∈ sysMaxEffStates (tpmOf (flipP s w)) {a, b, c} s s,
      ∀ θ : SysPartition N {a, b, c}, E0 ≤ sysPhiE (tpmOf (flipP s w)) {a, b, c} s θ s te) :
    levTrip * T.c0 * (79 / 80) * betaW w ≤ phi (flipP s w) s {a, b, c} := by
  classical
  set e := pkE3 hab hac hbc with he
  have hS := pkE3_S hab hac hbc
  set S : Finset (Fin N) := {a, b, c} with hSdef
  set tc := tcRow w with htc
  have hσ : 0 < σ := (b1_Pw_pos hw tc).trans_le hσ1
  have hPw : ∀ r, Pw w r ≤ σ := fun r => (Pw_le_tcRow w r).trans hσ1
  set H' := H.erase s with hH'
  have hH'c : H'.card ≤ 12 := by rw [hH', card_erase_of_mem hsH]; omega
  set wu := Pw w s / σ with hwudef
  have hσs : Pw w s = wu * σ := by rw [hwudef]; field_simp
  have hwu0 : 0 ≤ wu := div_nonneg (Pw_nonneg w s) hσ.le
  have hwu1 : wu ≤ 1 := (div_le_one hσ).2 (hPw s)
  set d := lt3RealData w e S tc H' σ with hd
  obtain ⟨hG1n, hF1n, hG2n, hF2n, hG1V, hF1V, hG2V, hF2V, hV1n, hV2n, hVH⟩ := lt3RD_bounds w e S tc H' hσ hPw
  have hV12 : d.V1 + d.V2 ≤ 12 := hVH.trans (by exact_mod_cast hH'c)
  obtain ⟨hTs, hc45, -, -, hTbox, hY01, hV, hG, hP, -, -, -, -, -, -⟩ := hT
  set x : Fin 3 → ℝ := fun i => clamp01 (w s (e i)) with hxdef
  set f : Fin 3 → ℝ := fun i => clamp01 (w (flip s (e i)) (e i)) with hfdef
  set Mr := lt3URest w e s ds wu T with hMr
  have hlw := rlLoR_wd_bounds d hG1n hF1n hG2n hF2n hG1V hF1V hG2V hF2V hV1n hV2n
  have hMrbox : ∀ (u : Fin 8) (i : Fin 3), rlLoR d u i ≤ Mr u i ∧ Mr u i ≤ rlLoR d u i + rlWdR d u i :=
    fun u i => hTbox u i
  have hTg := lt3Tgt_spec d Mr hMrbox (fun u i => (hlw u i).2.1)
  -- the private hypotheses
  have hA : ∀ r ∈ lt3HA S tc H', ∀ (u : Fin (2 ^ 3)) (i : Fin 3), ¬((u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ)) →
      |clamp01 (w (pkFlip e r u) (e i)) - lt3Tgt d Mr u i| ≤ ρ := by
    intro r hr u i hv
    obtain ⟨hrH, hag⟩ := mem_filter.1 hr
    have h := hboxR (r, u, i) (mem_lt3BoxIdx.2 ⟨hrH, hv⟩)
    simp only [lt3BoxE, lt3BoxTgt] at h
    rwa [if_pos hag] at h
  have hB : ∀ r ∈ lt3HB S tc H', ∀ (u : Fin (2 ^ 3)) (i : Fin 3), ¬((u : ℕ) = 7 ∨ (u : ℕ) = 7 - 2 ^ (i : ℕ)) →
      |clamp01 (w (pkFlip e r (pkCo u)) (e i)) - lt3Tgt d Mr u i| ≤ ρ := by
    intro r hr u i hv
    obtain ⟨hrH, hag⟩ := mem_filter.1 hr
    have h := hboxR (r, pkCo u, i) (mem_lt3BoxIdx.2 ⟨hrH, pkCo_valid u i hv⟩)
    simp only [lt3BoxE, lt3BoxTgt] at h
    rwa [if_neg hag, pkCo_pkCo] at h
  have hY : ∀ (u : Fin (2 ^ 3)) (i : Fin 3), ¬((u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ)) →
      |clamp01 (w (pkFlip e s u) (e i)) - T.Y u i| ≤ ρ := by
    intro u i hv
    have h := hboxT (s, u, i) (mem_lt3BoxIdx.2 ⟨mem_singleton_self _, hv⟩)
    simp only [lt3BoxE, lt3BoxTgt] at h
    rwa [if_pos (fun _ _ => trivial)] at h
  have hHe : ∀ r ∈ H', (∀ j ∈ S, r j = tc j) ∨ (∀ j ∈ S, r j ≠ tc j) := fun r hr => hH r (mem_of_mem_erase hr)
  have hbox : ∀ (v : Fin (2 ^ 3)) (i : Fin 3),
      rlLoR d v i + rlWdR d v i * lt3Tgt d Mr v i + wu * tcEntR x f T.Y (uIdx ds v) i = rlMR T.M v i := by
    intro v i
    rw [(hTg v i).1, rlMR_coe, rlMR_coe]
    simp only [hMr, lt3URest]
    ring
  set Ts' : Fin (2 ^ 3) := ⟨T.Ts, by simpa using hTs⟩ with hTs'
  set t0 := pkFlip e tc Ts' with ht0def
  have hφL0 : 0 ≤ φL := (abs_nonneg _).trans (hlight tc 0 0)
  set φ := σ * (13 * ρ) + φL with hφdef
  have hdec0 := lt3_hdec_u w e hS tc s H hσ hσs hsH hρ0 ds hsag hHe (lt3Tgt d Mr) hA hB T.Y hY T.M Ts' hbox
    (fun u i => hlight t0 u i)
  have hinv : flipP s (flipP s w) = w := flipP_invol s w
  have hz : flipP s w ∈ openCube N := flipP_mem_openCube hw
  have hdec : ∀ (i : Fin 3) (u : Fin 8), |Num (flipP s (flipP s w)) S S (pkFlip e t0 u) (e i) -
      (σ * rlMR T.M (T.Ts ^^^ (u : ℕ)) i + lt3Light w S H t0 (e i))| ≤ φ := by
    intro i u
    rw [hinv]
    refine (hdec0 i u).trans ?_
    have k : (d.V1 + d.V2) * ρ ≤ 12 * ρ := mul_le_mul_of_nonneg_right hV12 hρ0
    have k2 : wu * ρ ≤ ρ := mul_le_of_le_one_left hρ0 hwu1
    have : σ * ((d.V1 + d.V2) * ρ + wu * ρ) ≤ σ * (13 * ρ) :=
      mul_le_mul_of_nonneg_left (by linarith) hσ.le
    linarith
  -- the scales
  set A := lvK 3 * Zs w with hAdef
  have hηsA : η ^ 2 ≤ σ * A / (8 * 10 ^ 7) := hηs
  have hZ : 0 < Zs w := b1_Zs_pos hw
  have hA0 : 0 < A := mul_pos (lvK_pos 3) hZ
  have hσA : σ ≤ 4 * A := by rw [hAdef, lvK_three]; linarith
  have hηA3 : 3 * η ≤ A := by
    by_contra hcon
    push Not at hcon
    have h1 : A * A < (3 * η) * (3 * η) := mul_self_lt_mul_self hA0.le hcon
    have h2 : σ * A / (8 * 10 ^ 7) ≤ (4 * A) * A / (8 * 10 ^ 7) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hσA hA0.le) (by norm_num)
    have e2 : (3 * η) * (3 * η) = 9 * η ^ 2 := by ring
    have hAA : 0 < A * A := by positivity
    have e3 : σ * A = σ * (lvK 3 * Zs w) := rfl
    linarith
  have hAη : 2 * A / 3 ≤ A - η := by linarith
  have hAη0 : 0 < A - η := by linarith
  -- the error terms
  have hφLσ : φL / σ ≤ 1 / 320000 := by rw [div_le_iff₀ hσ]; linarith
  have hE : 6 * φ / σ = 78 * ρ + 6 * (φL / σ) := by rw [hφdef]; field_simp; ring
  have hEt : 6 * φ / σ ≤ 12 / 320000 := by rw [hE]; linarith
  have hE0' : 0 ≤ 6 * φ / σ := by rw [hE]; have := div_nonneg hφL0 hσ.le; positivity
  set y := T.c0 * (5 / 3 - 1 / 80) - 36 * (3 * ω') / 8 - 6 * φ / σ with hydef
  have hy1 : 1 ≤ y := by rw [hydef]; linarith
  have hy0 : 0 < y := by linarith
  have hyV : y ≤ (T.c0 * (5 / 3 - 1 / 80) - 36 * (3 * ω') / 8) - 6 * φ / σ := by rw [hydef]
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / 800000 := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδdef]; norm_num
  have hV' : T.c0 * (5 / 3 - 1 / 80) - 36 * (3 * ω') / 8 ≤ rlV8R lp3CStar T.Ts T.M / 8 := by linarith
  have hstar : lp3CStar ∈ lp3Profiles := by decide +kernel
  have hFmax : rlV8R lp3CStar T.Ts T.M / 8 ≤ 59 := by
    have hM13 : ∀ (u : Fin 8) (i : Fin 3), |T.M u i - (fun _ _ => (0 : ℝ)) u i| ≤ 13 := by
      intro u i
      have hb := hMrbox u i
      have hl := hlw u i
      have hent : 0 ≤ tcEntR x f T.Y (uIdx ds u) i ∧ tcEntR x f T.Y (uIdx ds u) i ≤ 1 := by
        unfold tcEntR
        split_ifs with h0 h1
        · exact ⟨clamp01_nonneg _, clamp01_le_one _⟩
        · exact ⟨clamp01_nonneg _, clamp01_le_one _⟩
        · exact hY01 (uIdx ds u) i (by rintro (h | h); exact h0 h; exact h1 h)
      have hMv : T.M u i = Mr u i + wu * tcEntR x f T.Y (uIdx ds u) i := by simp only [hMr, lt3URest]; ring
      have hw1 : 0 ≤ wu * tcEntR x f T.Y (uIdx ds u) i := mul_nonneg hwu0 hent.1
      have hw2 : wu * tcEntR x f T.Y (uIdx ds u) i ≤ 1 := by nlinarith [hent.2]
      simp only [sub_zero]
      rw [abs_le, hMv]; constructor <;> linarith [hb.1, hb.2, hl.1, hl.2.2]
    have h := rlV8R_pert hstar T.Ts hM13
    have h0 : rlV8R lp3CStar T.Ts (fun _ _ => (0 : ℝ)) = 0 := by simp [rlV8R, rlMR]
    rw [h0, sub_zero] at h
    have := (abs_le.1 h).2
    linarith
  have hδG : δ * (59 + 6 * φ / σ) / 5 + 6 * (6 * φ / σ) / 5 ≤ T.c0 * (1 / 80) / 20 - 6 * (3 * ω') := by
    have k1 : δ * (59 + 6 * φ / σ) ≤ δ * 60 := mul_le_mul_of_nonneg_left (by linarith) hδ0
    rw [hδdef] at k1 ⊢
    linarith
  have hsmall : 36 * η ^ 2 < δ * y * σ * (A - η) := by
    have k2 : δ * σ * (2 * A / 3) ≤ δ * σ * (A - η) := mul_le_mul_of_nonneg_left hAη (by positivity)
    have k3 : δ * σ * (A - η) ≤ δ * y * σ * (A - η) := by
      have hX : 0 ≤ δ * σ * (A - η) := by positivity
      have := mul_le_mul_of_nonneg_right hy1 hX
      have e1 : y * (δ * σ * (A - η)) = δ * y * σ * (A - η) := by ring
      linarith
    have hσA' : 0 < σ * A := by positivity
    have l1 : 36 * η ^ 2 ≤ 36 * (σ * A / (8 * 10 ^ 7)) := by linarith
    have l2 : 36 * (σ * A / (8 * 10 ^ 7)) < δ * σ * (2 * A / 3) := by
      have e1 : 36 * (σ * A / (8 * 10 ^ 7)) = (σ * A) * (36 / (8 * 10 ^ 7)) := by ring
      have e2 : δ * σ * (2 * A / 3) = (σ * A) * (1 / 1200000) := by rw [hδdef]; ring
      rw [e1, e2]
      exact mul_lt_mul_of_pos_left (by norm_num) hσA'
    linarith
  have hmsmall : 24 * A * η ^ 2 < (A - η) ^ 2 * (σ * (1 / 20 - 6 * (3 * ω')) - 6 * φ) := by
    have hσP : σ * (1 / 20 - 6 * (3 * ω')) - 6 * φ = σ * ((1 / 20 - 6 * (3 * ω')) - 6 * φ / σ) := by
      field_simp
    have hPE : (1 : ℝ) / 25 ≤ (1 / 20 - 6 * (3 * ω')) - 6 * φ / σ := by linarith
    have hsq : 4 * A ^ 2 / 9 ≤ (A - η) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hAη 2
      have e : (2 * A / 3) ^ 2 = 4 * A ^ 2 / 9 := by ring
      linarith
    have r1 : (4 * A ^ 2 / 9) * (σ * (1 / 25)) ≤ (A - η) ^ 2 * (σ * ((1 / 20 - 6 * (3 * ω')) - 6 * φ / σ)) :=
      mul_le_mul hsq (mul_le_mul_of_nonneg_left hPE hσ.le) (by positivity) (by positivity)
    have e3 : σ * (lvK 3 * Zs w) = σ * A := rfl
    rw [e3] at hηs
    have l1 : 24 * A * η ^ 2 ≤ 24 * A * (σ * A / (8 * 10 ^ 7)) :=
      mul_le_mul_of_nonneg_left hηs (by positivity)
    have l2 : 24 * A * (σ * A / (8 * 10 ^ 7)) = (σ * A ^ 2) * (3 / 10 ^ 7) := by ring
    have r2 : (4 * A ^ 2 / 9) * (σ * (1 / 25)) = (σ * A ^ 2) * (4 / 225) := by ring
    have hσA2 : 0 < σ * A ^ 2 := by positivity
    rw [hσP]
    have r3 : (σ * A ^ 2) * (3 / 10 ^ 7) < (σ * A ^ 2) * (4 / 225) := mul_lt_mul_of_pos_left (by norm_num) hσA2
    linarith
  have hlev' : ∀ Y ⊆ S, ∀ t', ∀ i ∈ S, |Num (flipP s (flipP s w)) S Y t' i - A| ≤ η := by
    rw [hinv]; exact hlev
  have hmain := triple_lower_rl (z := flipP s w) hz s hab hac hbc t0 hTs T.M (fun j => lt3Light w S H t0 j)
    (A := A) (η := η) (δ := δ) (σ := σ) (φ := φ) (y := y) (Fm := 59) (E0 := E0)
    hη0 hηA3 hA0 hδ0 hσ hlev' hdec hV' hG hP hFmax hy0 hyV hδG hsmall hmsmall hE0 heff
  -- the level
  set q := 6 * η ^ 2 / ((A - η) * σ) with hqdef
  have hq : q ≤ 9 / (8 * 10 ^ 7) := by
    rw [hqdef, div_le_iff₀ (mul_pos hAη0 hσ)]
    have k : 9 / (8 * 10 ^ 7) * ((2 * A / 3) * σ) ≤ 9 / (8 * 10 ^ 7) * ((A - η) * σ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAη hσ.le) (by positivity)
    have e3 : 9 / (8 * 10 ^ 7) * ((2 * A / 3) * σ) = 6 * (σ * A / (8 * 10 ^ 7)) := by ring
    have e4 : σ * (lvK 3 * Zs w) = σ * A := rfl
    rw [e4] at hηs
    linarith
  have hyq : T.c0 * (5 / 3 * (79 / 80)) ≤ y - q := by
    rw [hydef]
    linarith
  have hβ : 0 ≤ betaW w := div_nonneg (Pw_nonneg w _) hZ.le
  have hlt := levTrip_pos
  calc levTrip * T.c0 * (79 / 80) * betaW w
      = 3 / 5 * levTrip * betaW w * (T.c0 * (5 / 3 * (79 / 80))) := by ring
    _ ≤ 3 / 5 * levTrip * betaW w * (y - q) := mul_le_mul_of_nonneg_left hyq (by positivity)
    _ = Pw w tc * (y - q) / (8 * A * Real.log 2) := (lt3_level_eq w hZ (y - q)).symm
    _ ≤ σ * (y - q) / (8 * A * Real.log 2) := by
        have hyq0 : 0 ≤ y - q := by nlinarith
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hσ1 hyq0)
          (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity)
    _ ≤ phi (flipP s w) s {a, b, c} := hmain

end Census
end IIT
