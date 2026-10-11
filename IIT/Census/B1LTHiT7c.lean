/-
Census, B1 LTBetaHi, T7 part C: **the assembly of the LT3 band**.

* `LT3HeavyHyp L p` — **open item (b) as a named hypothesis**: for `s ∈ lt3H w = {tc} ∪ Sp`, every non-adverse member
  has a success region of probability `≥ p` (`LT3MemberOK`). `lt3MemberOK_of_box` turns a target table on the
  member's private blocks plus the deterministic implication into such a region (probability `ρ^312`), which is
  the form the RL-tc certificate delivers.
* `lt3_nosucc_prod`: success regions of distinct members are determined by disjoint private blocks
  (`lt3WPB_disjoint`), so no member succeeding has probability `≤ e^{-p |G|}`.
* Item (f) (measurability): the conditioning (`lt3W_cond_priv`) is applied to the MEASURABLE event
  `lt3T7Y L s = lt3T7Tm L s ∩ (toMeasurable {¬ good})ᶜ`, where `lt3T7Tm` is the target (`φ` is measurable,
  `b1m_phi_flip`) and the good event (`lt3WGood`, `bdGood`, no excess of adverse members) enters only through a
  measurable subset of it. Inside a section the success regions are the `η`-boxes of `lt3WSucc_prob` (never the
  set `{w | lt3WSucc ..}` itself, which uses the Hilbert choice `lt3Tab`).
* `lt3_T7_sect`: a nonempty section at `w0 ∈ lt3T7Y L s` has measure `≤ e^{-2N}`: on the good event
  `m ≥ N/(2300000 C)`, `m² ≤ 2|WF|`, `4|Adv| ≤ m²`, so `G = WF \ Adv` has `m² ≤ 4|G|` members, each with a success
  region (light: `lt3_light_member_ev`; heavy: `LT3HeavyHyp`), and `e^{-p m²/4} ≤ e^{-2N}`.
* **`lt3HiFl_of_heavy`** (`lt3Lc ≤ L`): `LT3HeavyHyp L p → LT3HiFlStmt L (1047/1000)` (bad events: `2e^{-1.05N}` windowed good
  event, `e^{-1.2N}` band, `e^{-2N}` adverse count, `e^{-2N}` conditional product); **`ltBetaHi_of_heavy`**:
  `LT3HeavyHyp L p → LTBetaHiStmt (1/4) (104/100)` (via `ltBetaHi_of_LT3Fl`).
-/
import IIT.Census.B1LTHiT7b
import IIT.Census.B1LTHiSpGU

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-! ### Open item (b): the heavy current state -/

/-- **Open item (b), as a hypothesis.** For a heavy current state (`s ∈ lt3H w = {tc} ∪ Sp`), `s`'s private block is
a cause block, so the effect side must come from the RL-tc certificate, whose box pins `tc`'s private entries
(`Y`) separately from the other heavy rows (`M - Y`): the cause box of `lt3WSucc` (one target `lt3Tgt` for all rows
of a class) does not cover it. `LT3HeavyHyp L p` asks exactly what that box delivers: every non-adverse member of
a heavy `s` has a success region of probability `≥ p` (band level `L`). The windowed good event `lt3WGood` at the
conditioning point is available (checker, 2026-10-08); the floor `4/5 ≤ y_top(tc)` follows from `Zs ≥ 1/2`,
`Lσ_N ≤ β` by `flr_floor`. -/
def LT3HeavyHyp (L p : ℝ) : Prop :=
  0 < p ∧ ∀ᶠ N : ℕ in atTop, ∀ (s : State N) (w : Param N) (S : Finset (Fin N)),
    w ∈ openCube N → 1 / 2 ≤ Zs w → L * sigN N ≤ betaW w → bdGood w → (lt2Sp w).card < 12 →
    lt3WGood s (1 / 21) lt3γ 8319999 (N / 20) (N / 600) 14 (N * N / (10 ^ 14 * lt3Cn * lt3Cn)) w →
    (S, s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w → S ∉ lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w →
    s ∈ lt3H w → LT3MemberOK L p s w S

/-- **A box gives a success region**: targets `τ ∈ [0, 1]` on the member's private blocks and the deterministic
implication give `LT3MemberOK` with probability `ρ^312` (`|Base| ≤ 13`, `|lt3PB| ≤ 24`). -/
theorem lt3MemberOK_of_box {L ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {s : State N} {w : Param N}
    {S : Finset (Fin N)} (hS : S.card ≤ 3) (hSp : (lt2Sp w).card < 12) (τ : State N × Fin N → ℝ)
    (hτ : ∀ q, 0 ≤ τ q ∧ τ q ≤ 1)
    (himp : ∀ η : Param N, (∀ q ∈ (lt3Base s w).biUnion (fun r => lt3PB (S, r)), |clamp01 (η q.1 q.2) - τ q| ≤ ρ) →
      LT3Concl L s (replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w) w η) S) :
    LT3MemberOK L (ρ ^ 312) s w S := by
  classical
  set B := (lt3Base s w).biUnion (fun r => lt3PB (S, r)) with hB
  refine ⟨{η | ∀ q ∈ B, |clamp01 (η q.1 q.2) - τ q| ≤ ρ}, ?_, ?_, ?_, fun η hη => himp η hη⟩
  · have e1 : {η : Param N | ∀ q ∈ B, |clamp01 (η q.1 q.2) - τ q| ≤ ρ} =
        ⋂ q ∈ B, {η : Param N | |clamp01 (η q.1 q.2) - τ q| ≤ ρ} := by
      ext η; simp
    rw [e1]
    exact MeasurableSet.biInter (Set.to_countable _) fun q _ =>
      measurableSet_le (continuous_abs.measurable.comp ((b1m_clamp _ _).sub measurable_const)) measurable_const
  · intro η η' h
    simp only [Set.mem_setOf_eq]
    exact forall₂_congr fun q hq => by rw [h q hq]
  · have hE : Function.Injective fun b : {q // q ∈ B} => (b.1 : State N × Fin N) := Subtype.val_injective
    have h := cubeM_box_ge (B := {q // q ∈ B}) (fun b => b.1) hE (fun b => τ b.1) (fun b => hτ b.1) hρ0 hρ1
    rw [Fintype.card_coe] at h
    have hBase : (lt3Base s w).card ≤ 13 :=
      (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans (by omega)))
    have hc : B.card ≤ 312 := by
      refine card_biUnion_le.trans ?_
      calc ∑ r ∈ lt3Base s w, (lt3PB (S, r)).card ≤ ∑ _r ∈ lt3Base s w, 24 :=
            sum_le_sum fun r _ => lt3PB_card_le (S, r) hS
        _ = 24 * (lt3Base s w).card := by rw [sum_const, smul_eq_mul, mul_comm]
        _ ≤ 312 := by omega
    refine le_trans (ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hρ0 hρ1 hc))
      (h.trans (le_of_eq (congrArg _ ?_)))
    ext η
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h q hq => h ⟨q, hq⟩, fun h b => h b.1 b.2⟩

/-! ### The conditional product -/

/-- **No member succeeds**: success regions on disjoint private blocks, `P ≤ e^{-p |G|}`. -/
theorem lt3_nosucc_prod {L p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : State N) (w : Param N)
    (G : Finset (Finset (Fin N))) (hG : ∀ S ∈ G, (S, s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w)
    (hOK : ∀ S ∈ G, LT3MemberOK L p s w S) :
    cubeM N {η | ∀ S ∈ G, ¬ LT3Concl L s (replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w) w η) S} ≤
      ENNReal.ofReal (Real.exp (-(p * G.card))) := by
  classical
  have : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  set A := stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w with hA
  set C : Finset (Fin N) → Finset (State N × Fin N) := fun S => (lt3Base s w).biUnion fun r => lt3PB (S, r)
    with hC
  have hOK' : ∀ S : Finset (Fin N), ∃ U : Set (Param N), S ∈ G → (MeasurableSet U ∧ DetOnE (C S) U ∧
      ENNReal.ofReal p ≤ cubeM N U ∧ ∀ η ∈ U, LT3Concl L s (replE A w η) S) := by
    intro S
    by_cases hS : S ∈ G
    · obtain ⟨U, hU⟩ := hOK S hS
      exact ⟨U, fun _ => hU⟩
    · exact ⟨∅, fun h => absurd h hS⟩
  choose U hU using hOK'
  have hsub : {η | ∀ S ∈ G, ¬ LT3Concl L s (replE A w η) S} ⊆ ⋂ S ∈ G, (U S)ᶜ := by
    intro η hη
    simp only [Set.mem_iInter, Set.mem_compl_iff]
    intro S hS hηU
    exact hη S hS ((hU S hS).2.2.2 η hηU)
  have hdisj : ∀ j ∈ G, ∀ k ∈ G, j ≠ k → Disjoint (C j) (C k) := by
    intro j hj k hk hjk
    simp only [hC]
    rw [Finset.disjoint_biUnion_left]
    intro r hr
    rw [Finset.disjoint_biUnion_right]
    intro r' hr'
    exact lt3WPB_disjoint w (lt3W_mem_base (hG j hj) hr) (lt3W_mem_base (hG k hk) hr')
      (fun h => hjk (Prod.ext_iff.1 h).1)
  refine (measure_mono hsub).trans ?_
  rw [cubeM_iInter_eq_prod_of_detOnE G C hdisj (fun S hS => (hU S hS).1.compl)
    (fun S hS => (hU S hS).2.1.compl)]
  have hone : ∀ S ∈ G, cubeM N (U S)ᶜ ≤ ENNReal.ofReal (1 - p) := fun S hS => by
    rw [measure_compl (hU S hS).1 (measure_ne_top _ _), measure_univ, ENNReal.ofReal_sub _ hp0,
      ENNReal.ofReal_one]
    exact tsub_le_tsub_left (hU S hS).2.2.1 1
  calc ∏ S ∈ G, cubeM N (U S)ᶜ ≤ ∏ _S ∈ G, ENNReal.ofReal (1 - p) := Finset.prod_le_prod' hone
    _ = ENNReal.ofReal ((1 - p) ^ G.card) := by
        rw [Finset.prod_const, ENNReal.ofReal_pow (by linarith)]
    _ ≤ ENNReal.ofReal (Real.exp (-(p * G.card))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc (1 - p) ^ G.card ≤ Real.exp (-p) ^ G.card :=
              pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-p)]) _
          _ = Real.exp (-(p * G.card)) := by rw [← Real.exp_nat_mul]; ring_nf

/-! ### The events -/

/-- The good event of T7: the windowed good event, the band event, and no excess of adverse members. -/
def lt3T7Good (s : State N) (w : Param N) : Prop :=
  lt3WGood s (1 / 21) lt3γ 8319999 (N / 20) (N / 600) 14 (N * N / (10 ^ 14 * lt3Cn * lt3Cn)) w ∧ bdGood w ∧
  ¬ ((lt2Sp w).card < 12 ∧ 7 ≤ qM (lt3WQ s (1 / 21) lt3γ 8319999 w) ∧
      N ≤ lt3D0 * qM (lt3WQ s (1 / 21) lt3γ 8319999 w) ∧
      qM (lt3WQ s (1 / 21) lt3γ 8319999 w) * qM (lt3WQ s (1 / 21) lt3γ 8319999 w) <
        4 * (lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w).card)

/-- The measurable target: no pair or triple reaches `β/4` on `{Lσ_N ≤ β, Zs ≥ 1/2}` (open cube). -/
def lt3T7Tm (L : ℝ) (s : State N) : Set (Param N) :=
  {w | w ∈ openCube N ∧ L * sigN N ≤ betaW w ∧ 1 / 2 ≤ Zs w ∧
    (lt3SpC s w → ⌈(1 / 21 : ℝ) * N⌉₊ ≤ (lt3GoodU s w).card) ∧
    ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 1 / 4 * betaW w}

/-- The conditioned event: the target intersected with a measurable subset of the good event. -/
def lt3T7Y (L : ℝ) (s : State N) : Set (Param N) :=
  lt3T7Tm L s ∩ (toMeasurable (cubeM N) {w | ¬ lt3T7Good s w})ᶜ

lemma lt3T7Tm_mset (L : ℝ) (s : State N) : MeasurableSet (lt3T7Tm L s) := by
  classical
  have e : lt3T7Tm L s = openCube N ∩ ({w | L * sigN N ≤ betaW w} ∩ ({w | 1 / 2 ≤ Zs w} ∩
      ({w | lt3SpC s w → ⌈(1 / 21 : ℝ) * N⌉₊ ≤ (lt3GoodU s w).card} ∩
      ⋂ S : Finset (Fin N), {w | 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 1 / 4 * betaW w}))) := by
    ext w
    simp only [lt3T7Tm, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  have hGU : MeasurableSet {w : Param N | lt3SpC s w → ⌈(1 / 21 : ℝ) * N⌉₊ ≤ (lt3GoodU s w).card} := by
    have h := fibM_comp (f := fun w : Param N => ((lt2Sp w, tcRow w), lt3GoodU s w))
      (fibM_pair fibM_SpTc (fibM_GoodU s))
      (fun d => decide (s ∈ d.1.1 ∧ s ≠ d.1.2 → ⌈(1 / 21 : ℝ) * N⌉₊ ≤ d.2.card)) true
    convert h using 1
    ext w
    simp only [Set.mem_setOf_eq, decide_eq_true_eq]
    rfl
  refine b1_measurableSet_openCube.inter ((measurableSet_le measurable_const b1m_betaW).inter
    ((measurableSet_le measurable_const b1m_Zs).inter (hGU.inter (MeasurableSet.iInter fun S => ?_))))
  by_cases h : 2 ≤ S.card ∧ S.card ≤ 3
  · have e2 : {w : Param N | 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 1 / 4 * betaW w} =
        {w | phi (flipP s w) s S < 1 / 4 * betaW w} := by
      ext w
      simp only [Set.mem_setOf_eq]
      exact ⟨fun hw => hw h.1 h.2, fun hw _ _ => hw⟩
    rw [e2]
    exact measurableSet_lt (b1m_phi_flip s S) (b1m_betaW.const_mul _)
  · have e2 : {w : Param N | 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 1 / 4 * betaW w} = Set.univ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ h
    rw [e2]
    exact MeasurableSet.univ

lemma lt3T7Y_mset (L : ℝ) (s : State N) : MeasurableSet (lt3T7Y L s) :=
  (lt3T7Tm_mset L s).inter (measurableSet_toMeasurable _ _).compl

lemma lt3T7Y_good {L : ℝ} {s : State N} {w : Param N} (h : w ∈ lt3T7Y L s) : lt3T7Good s w := by
  by_contra hc
  exact h.2 (subset_toMeasurable _ _ hc)

/-! ### Numerics -/

/-- **The conditional product is `≤ e^{-2N}`**: `m ≥ N/K` (`K = 2300000 C`), `m² ≤ 4g` give `2N ≤ p g`. -/
lemma lt3_prod_num {p : ℝ} (hp : 0 < p) : ∀ᶠ N : ℕ in atTop, ∀ m g : ℕ, N / (2300000 * lt3Cn) ≤ m →
    m * m ≤ 4 * g → 2 * (N : ℝ) ≤ p * g := by
  set K : ℕ := 2300000 * lt3Cn with hK
  have hK0 : 0 < K := by have := lt3Cn_pos; positivity
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  filter_upwards [eventually_ge_atTop (2 * K), eventually_ge_atTop ⌈32 * (K : ℝ) ^ 2 / p⌉₊] with N h1 h2 m g hm hg
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1r : 2 * (K : ℝ) ≤ N := by exact_mod_cast h1
  have h2r : 32 * (K : ℝ) ^ 2 / p ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast h2)
  have hlt := Nat.lt_div_mul_add (a := N) hK0
  have hlt' : (N : ℝ) < (N / K : ℕ) * K + K := by exact_mod_cast hlt
  have hmr : ((N / K : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
  -- `N/(2K) ≤ m`
  have hq : (N : ℝ) ≤ 2 * K * m := by nlinarith
  have hgr : ((m : ℝ)) * m ≤ 4 * g := by exact_mod_cast hg
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- `N² ≤ 4K² m² ≤ 16 K² g`
  have hN2 : (N : ℝ) * N ≤ 16 * (K : ℝ) ^ 2 * g := by nlinarith
  have h32 : 32 * (K : ℝ) ^ 2 ≤ p * N := by
    rw [div_le_iff₀ hp] at h2r; linarith
  -- `2N · 16K² ≤ p N · 16 K² g / N`, i.e. `2N ≤ p g`
  by_cases hNz : (N : ℝ) = 0
  · rw [hNz]; have : (0 : ℝ) ≤ p * g := by positivity
    linarith
  · have hNpos : 0 < (N : ℝ) := lt_of_le_of_ne hN0 (Ne.symm hNz)
    have hK2 : 0 < (K : ℝ) ^ 2 := by positivity
    have key : 2 * (N : ℝ) * (16 * (K : ℝ) ^ 2) ≤ p * g * (16 * (K : ℝ) ^ 2) := by
      have e1 : 2 * (N : ℝ) * (16 * (K : ℝ) ^ 2) = N * (32 * (K : ℝ) ^ 2) := by ring
      have e2 : (N : ℝ) * (32 * (K : ℝ) ^ 2) ≤ N * (p * N) := mul_le_mul_of_nonneg_left h32 hN0
      have e3 : (N : ℝ) * (p * N) ≤ p * (16 * (K : ℝ) ^ 2 * g) := by
        have := mul_le_mul_of_nonneg_left hN2 hp.le
        nlinarith
      nlinarith
    exact le_of_mul_le_mul_right key (by positivity)

/-- `2 e^{-1.05N} + e^{-1.2N} + 2 e^{-2N} + 2 e^{-1.1N} ≤ e^{-1.047N}` for `N` large. -/
lemma lt3_rate_num : ∀ᶠ N : ℕ in atTop, Real.exp (-(2 * (N : ℝ))) +
    (2 * Real.exp (-((105 / 100 : ℝ) * N)) + Real.exp (-(6 / 5 * (N : ℝ))) + Real.exp (-(2 * (N : ℝ)))) +
      2 * Real.exp (-((11 / 10 : ℝ) * N)) ≤ Real.exp (-(1047 / 1000 * (N : ℝ))) := by
  filter_upwards [eventually_ge_atTop 2000] with N hN
  have hNr : (2000 : ℝ) ≤ N := by exact_mod_cast hN
  set E := Real.exp (-((105 / 100 : ℝ) * N)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have e1 : Real.exp (-(2 * (N : ℝ))) ≤ E := Real.exp_le_exp.2 (by linarith)
  have e2 : Real.exp (-(6 / 5 * (N : ℝ))) ≤ E := Real.exp_le_exp.2 (by linarith)
  have hsplit : Real.exp (-(1047 / 1000 * (N : ℝ))) = E * Real.exp (3 / 1000 * N) := by
    rw [hE, ← Real.exp_add]; ring_nf
  have e3 : Real.exp (-((11 / 10 : ℝ) * N)) ≤ E := Real.exp_le_exp.2 (by linarith)
  have h5 : (7 : ℝ) ≤ Real.exp (3 / 1000 * N) := by
    have := Real.add_one_le_exp (3 / 1000 * (N : ℝ)); linarith
  rw [hsplit]
  nlinarith

/-! ### One section -/

/-- **A nonempty section of the conditioned event is `≤ e^{-2N}`** (`N` large, uniformly in `s`). -/
theorem lt3_T7_sect {L p : ℝ} (hL : lt3Lc ≤ L) (hH : LT3HeavyHyp L p) : ∀ᶠ N : ℕ in atTop,
    ∀ (s : State N) (w0 : Param N), w0 ∈ lt3T7Y L s →
    cubeM N {η | replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w0) w0 η ∈ lt3T7Y L s} ≤
      ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
  obtain ⟨hp, hHv⟩ := hH
  set p0 := min (min p lt3pL) 1 with hp0def
  have hp0 : 0 < p0 := lt_min (lt_min hp lt3pL_pos) one_pos
  have hp01 : p0 ≤ 1 := min_le_right _ _
  have hp0p : p0 ≤ p := (min_le_left _ _).trans (min_le_left _ _)
  have hp0L : p0 ≤ lt3pL := (min_le_left _ _).trans (min_le_right _ _)
  filter_upwards [hHv, lt3_light_member_ev hL, lt3WSel_of_floor_ev (lt3Lc_pos.trans_le hL), eventually_ge_atTop (10 ^ 8 * lt3Cn),
    eventually_ge_atTop (7 * (2300000 * lt3Cn)), lt3_prod_num hp0] with N hHN hLN hSelF hN8 hN7 hnum
  intro s w0 hw0
  classical
  have hgood := lt3T7Y_good hw0
  obtain ⟨⟨hcube, hβ, hZ, hGU, -⟩, -⟩ := hw0
  obtain ⟨hWG, hbd, hnadv⟩ := hgood
  obtain ⟨hm, h7, hm2⟩ := lt3W_good_F s 8319999 lt3Cn_ge hN8 hWG hGU
  have hSp : (lt2Sp w0).card < 12 := hWG.1.2.2.2.1
  have hSel := hSelF s lt3γ 8319999 w0 hZ hβ h7
  set m := qM (lt3WQ s (1 / 21) lt3γ 8319999 w0) with hmdef
  set K := 2300000 * lt3Cn with hK
  have hK0 : 0 < K := by have := lt3Cn_pos; positivity
  have h7K : 7 ≤ N / K := by rw [Nat.le_div_iff_mul_le hK0]; linarith
  have hm7 : 7 ≤ m := h7K.trans hm
  have hND : N ≤ lt3D0 * m := by
    have hlt := Nat.lt_div_mul_add (a := N) hK0
    have h1 : N / K * K ≤ m * K := Nat.mul_le_mul_right K hm
    have h2 : K ≤ m * K := Nat.le_mul_of_pos_left K (by omega)
    have e : lt3D0 * m = 2 * (m * K) := by simp only [lt3D0, hK]; ring
    rw [e]; omega
  have hAdv : 4 * (lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w0).card ≤ m * m := by
    by_contra hc
    exact hnadv ⟨hSp, hm7, hND, not_le.1 hc⟩
  set G := lt3WF s (1 / 21) lt3γ 8319999 w0 \ lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w0 with hGdef
  have hGc : m * m ≤ 4 * G.card := by
    have h1 : (lt3WF s (1 / 21) lt3γ 8319999 w0).card - (lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w0).card ≤
        G.card := Finset.le_card_sdiff _ _
    have h2 : m * m ≤ 2 * (lt3WF s (1 / 21) lt3γ 8319999 w0).card := hm2
    omega
  have hsB : s ∈ lt3Base s w0 := mem_insert_of_mem (mem_insert_self _ _)
  have hGk : ∀ S ∈ G, (S, s) ∈ lt3WSel s (1 / 21) lt3γ 8319999 w0 := fun S hS => by
    rw [hSel]; exact mem_product.2 ⟨(mem_sdiff.1 hS).1, hsB⟩
  have hOK : ∀ S ∈ G, LT3MemberOK L p0 s w0 S := by
    intro S hS
    have hnS := (mem_sdiff.1 hS).2
    by_cases hsH : s ∈ lt3H w0
    · exact (hHN s w0 S hcube hZ hβ hbd hSp hWG (hGk S hS) hnS hsH).mono hp0p
    · exact (hLN s w0 S hcube hSp (hGk S hS) hnS hsH).mono hp0L
  have hsub : {η | replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w0) w0 η ∈ lt3T7Y L s} ⊆
      {η | ∀ S ∈ G, ¬ LT3Concl L s (replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB w0) w0 η) S} := by
    intro η hη S hS hconc
    have hg' := lt3T7Y_good hη
    obtain ⟨⟨hc', hβ', hZ', -, hφ'⟩, -⟩ := hη
    obtain ⟨a, b, c, hab, hac, hbc, hS3⟩ := lt3WSel_three (hGk S hS)
    have hS3' : S = {a, b, c} := hS3
    have hcard : S.card = 3 := by
      rw [hS3', card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]
    have h1 := hconc hc' hZ' hβ' hg'.2.1 hg'.1.1.2.2.2.1
    have h2 := hφ' S (by omega) (by omega)
    linarith
  refine (measure_mono hsub).trans ((lt3_nosucc_prod hp0.le hp01 s w0 G hGk hOK).trans ?_)
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have := hnum m G.card hm hGc
  linarith

/-! ### The assembly -/

/-- Uniformity in the current state: a bound along every sequence of states holds uniformly. -/
lemma ev_forall_state {P : ∀ N : ℕ, State N → Prop} (h : ∀ sq : ∀ N, State N, ∀ᶠ N in atTop, P N (sq N)) :
    ∀ᶠ N in atTop, ∀ s : State N, P N s := by
  classical
  by_contra hc
  have hfr : ∃ᶠ N in atTop, ∃ s : State N, ¬ P N s := by
    rw [Filter.not_eventually] at hc
    exact hc.mono fun N hN => not_forall.1 hN
  let sq : ∀ N, State N := fun N => if h : ∃ s : State N, ¬ P N s then h.choose else fun _ => false
  have h2 : ∃ᶠ N in atTop, ¬ P N (sq N) := hfr.mono fun N hN => by
    show ¬ P N (if h : ∃ s : State N, ¬ P N s then h.choose else fun _ => false)
    rw [dif_pos hN]
    exact hN.choose_spec
  exact h2 ((h sq).mono fun N hN hN' => hN' hN)

/-- **The floored LT3 band, from the heavy hypothesis** (open item (b)). -/
theorem lt3HiFl_of_heavy {L p : ℝ} (hL : lt3Lc ≤ L) (hH : LT3HeavyHyp L p) : LT3HiFlStmt L (1047 / 1000) := by
  unfold LT3HiFlStmt
  refine ev_forall_state (P := fun N s => cubeM N (B1w N s ∩ openCube N ∩ {w | L * sigN N ≤ betaW w ∧
      1 / 2 ≤ Zs w ∧ 4 / 5 ≤ b1YTopR w (tcRow w) (1 / 21) ∧
      ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 1 / 4 * betaW w}) ≤
      ENNReal.ofReal (Real.exp (-(1047 / 1000 * (N : ℝ))))) fun sq => ?_
  have hD1 : 1 ≤ 10 ^ 14 * lt3Cn * lt3Cn := Nat.succ_le_of_lt (by have := lt3Cn_pos; positivity)
  filter_upwards [lt3_T7_sect hL hH, lt3W_not_good_ev2 sq (1 / 21) 8319999 hD1, bd_not_good_ev,
    lt3_adv_ev lt3D0_pos lt3κ_ge lt3κ_sq, lt3_rate_num, spgu_ev (lt3Lc_pos.trans_le hL)]
    with N hsect hWG hbd hadv hrate hgu
  set s := sq N with hs
  have : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  -- the conditioned event
  have hY : cubeM N (lt3T7Y L s) ≤ ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
    refine lt3W_cond_priv s (1 / 21) lt3γ 8319999 (lt3T7Y_mset L s) fun A w hA => ?_
    by_cases hne : ∃ η0, replE A w η0 ∈ lt3T7Y L s
    · obtain ⟨η0, hη0⟩ := hne
      have hP0 : stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB (replE A w η0) = A :=
        ((lt3WPriv_detOn (s := s) (ε := 1 / 21) (γ := lt3γ) (n := 8319999) A).replE_out w η0).2 hA
      have e : {η | replE A w η ∈ lt3T7Y L s} =
          {η | replE (stPriv (lt3WSel s (1 / 21) lt3γ 8319999) lt3PB (replE A w η0)) (replE A w η0) η ∈
            lt3T7Y L s} := by
        ext η
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hP0, replE_replE]
      rw [e]
      exact hsect s _ hη0
    · push Not at hne
      have e : {η | replE A w η ∈ lt3T7Y L s} = ∅ := by
        ext η
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact hne η
      rw [e, measure_empty]
      exact zero_le
  -- the bad event
  have hbad : {w | ¬ lt3T7Good s w} ⊆
      ({w | ¬ lt3WGood s (1 / 21) lt3γ 8319999 (N / 20) (N / 600) 14 (N * N / (10 ^ 14 * lt3Cn * lt3Cn)) w} ∪
        {w | ¬ bdGood w}) ∪
      {w | (lt2Sp w).card < 12 ∧ 7 ≤ qM (lt3WQ s (1 / 21) lt3γ 8319999 w) ∧
        N ≤ lt3D0 * qM (lt3WQ s (1 / 21) lt3γ 8319999 w) ∧
        qM (lt3WQ s (1 / 21) lt3γ 8319999 w) * qM (lt3WQ s (1 / 21) lt3γ 8319999 w) <
          4 * (lt3Adv s (1 / 21) lt3γ 8319999 lt3κ w).card} := by
    intro w hw
    by_cases h1 : lt3WGood s (1 / 21) lt3γ 8319999 (N / 20) (N / 600) 14 (N * N / (10 ^ 14 * lt3Cn * lt3Cn)) w
    · by_cases h2 : bdGood w
      · exact Or.inr (not_not.1 fun h3 => hw ⟨h1, h2, h3⟩)
      · exact Or.inl (Or.inr h2)
    · exact Or.inl (Or.inl h1)
  have hbadM : cubeM N {w | ¬ lt3T7Good s w} ≤ ENNReal.ofReal (2 * Real.exp (-((105 / 100 : ℝ) * N)) +
      Real.exp (-(6 / 5 * (N : ℝ))) + Real.exp (-(2 * (N : ℝ)))) := by
    refine (measure_mono hbad).trans ((measure_union_le _ _).trans ?_)
    refine (add_le_add ((measure_union_le _ _).trans (add_le_add hWG hbd)) (hadv s (1 / 21) lt3γ 8319999)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  -- the target
  have hT : B1w N s ∩ openCube N ∩ {w | L * sigN N ≤ betaW w ∧ 1 / 2 ≤ Zs w ∧
      4 / 5 ≤ b1YTopR w (tcRow w) (1 / 21) ∧
      ∀ S : Finset (Fin N), 2 ≤ S.card → S.card ≤ 3 → phi (flipP s w) s S < 1 / 4 * betaW w} ⊆
      (lt3T7Y L s ∪ toMeasurable (cubeM N) {w | ¬ lt3T7Good s w}) ∪
        {w | w ∈ B1w N s ∧ w ∈ openCube N ∧ L * sigN N ≤ betaW w ∧ 1 / 2 ≤ Zs w ∧ lt3SpC s w ∧
          (lt3GoodU s w).card < ⌈(1 / 21 : ℝ) * N⌉₊} := by
    rintro w ⟨⟨hB, hc⟩, hβ, hZ, -, hall⟩
    by_cases hgw : lt3SpC s w → ⌈(1 / 21 : ℝ) * N⌉₊ ≤ (lt3GoodU s w).card
    · by_cases h : w ∈ toMeasurable (cubeM N) {w | ¬ lt3T7Good s w}
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl ⟨⟨hc, hβ, hZ, hgw, hall⟩, h⟩)
    · push Not at hgw
      exact Or.inr ⟨hB, hc, hβ, hZ, hgw.1, hgw.2⟩
  refine (measure_mono hT).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add le_rfl (le_of_eq (measure_toMeasurable _))))
    (hgu s)).trans ?_
  refine (add_le_add (add_le_add hY hbadM) le_rfl).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hrate

/-- **The LT3 band (`LT3HiStmt`, B1LTHiSplit) from the heavy hypothesis**, at any `L ≥ lt3Lc`, rate `1.046`. -/
theorem lt3Hi_of_heavy {L p : ℝ} (hL : lt3Lc ≤ L) (hH : LT3HeavyHyp L p) : LT3HiStmt L (1046 / 1000) :=
  lt3Hi_of_floor (lt3Lc_pos.trans_le hL) (by norm_num) (by norm_num) (lt3HiFl_of_heavy hL hH)

/-- **LTBetaHi from the heavy hypothesis**: `LT3HeavyHyp L p → LTBetaHiStmt (1/4) (104/100)` (`L ≥ lt3Lc`). -/
theorem ltBetaHi_of_heavy {L p : ℝ} (hL : lt3Lc ≤ L) (hH : LT3HeavyHyp L p) : LTBetaHiStmt (1 / 4) (104 / 100) :=
  ltBetaHi_of_LT3Fl (lt3Lc_one.trans hL) (by norm_num) (lt3HiFl_of_heavy hL hH)

end Census
end IIT
