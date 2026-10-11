/-
Census, B1 LTBetaHi, module T6 (part D): packaging of Lemma TC' (scope L8) and the light-part budget.

* The per-member box `lt3Box e S tc H τ ρ`: every private entry `(r ⊕ u, e i)` (`r ∈ H`, `u ∉ {0, 2^i}`) lies within
  `ρ` of its target (`τ u i` for rows agreeing with `tc` on `S`, `τ (7 ⊕ u) i` for the others). Its entries lie in
  the private blocks `lt3PB (S, r)` (`lt3Box_entry_PB`) and are pairwise distinct (`lt3Box_injOn`), so the box is
  measurable (`lt3Box_mset`), determined by `⋃_{r ∈ H} lt3PB (S, r)` (`lt3Box_detOn`) and has probability
  `≥ ρ^{18|H|}` (`lt3Box_prob`, a product of uniforms via `lt2_mp_inj`).
* The RL table: `RLWin` (the conclusion of `rl_real_window`), the Hilbert choice `lt3Tab`, the targets `lt3Tgt`
  (`(M - lo)/wd`), the heavy set `lt3H = {tc} ∪ Sp`, the member data `lt3WData`, and the **per-member success event**
  `lt3WSucc` (the box of the member's private entries around the targets of the chosen table).
* `lt3_TCprime` (deterministic, generic heavy set, generic level `t ∈ (0, 1/80]`): on the box, with window
  `ω' ≤ t/4000`, `13ρ ≤ t/4000`, light part `≤ t σ/4000` and level band `η² ≤ t σ A/10^6` (`A = a₃ Z`):
  `levTrip · c0 · (1 - 483 t/800) · β ≤ φ_s(S)`; `hsmall`, `hmsmall`, `hy`, `hδG` are discharged inside.
* `lt3W_TCprime`: a member `S` of `lt3WSel` with `|Sp| < 12`, light part via `lt3W_pert` (stHalf statistic `φH` plus
  `2 |Priv| · 9 (e^{-3N/10} + e^{-x₁N})`); `lt3W_TCprime_ev`: for `N` large the perturbation error is absorbed when
  `P(tc) ≥ e^{-(x₁ - 1/800)N}`; `lt3W_TCprime_quarter`: explicit `n`, `ρ` at `t = 1/80` give `φ_s(S) ≥ β/4`.
-/
import IIT.Census.B1LTHiT6c
import IIT.Census.B1LTHiWin3

namespace IIT
namespace Census

open MeasureTheory Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-! ### Masks as sets of units -/

/-- The units flipped by a mask. -/
def pkSet (e : Fin 3 ↪ Fin N) (u : Fin (2 ^ 3)) : Finset (Fin N) :=
  (univ.filter fun q : Fin 3 => (u : ℕ).testBit q = true).map e

lemma mem_pkSet (e : Fin 3 ↪ Fin N) (u : Fin (2 ^ 3)) (q : Fin 3) :
    e q ∈ pkSet e u ↔ (u : ℕ).testBit q = true := by
  simp [pkSet]

lemma pkSet_sub {e : Fin 3 ↪ Fin N} {S : Finset (Fin N)} (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) (u : Fin (2 ^ 3)) :
    pkSet e u ⊆ S := by
  intro j hj
  obtain ⟨q, -, rfl⟩ := mem_map.1 hj
  exact (hS _).2 ⟨q, rfl⟩

lemma pkSet_card (e : Fin 3 ↪ Fin N) (u : Fin (2 ^ 3)) : (pkSet e u).card ≤ 3 := by
  unfold pkSet
  rw [card_map]
  exact (card_filter_le _ _).trans (by simp)

lemma pkFlip_eq_flipS (e : Fin 3 ↪ Fin N) (r : State N) (u : Fin (2 ^ 3)) :
    pkFlip e r u = flipS r (pkSet e u) := by
  funext j
  have hiff : (∃ q : Fin 3, e q = j ∧ (u : ℕ).testBit q = true) ↔ j ∈ pkSet e u := by
    simp only [pkSet, mem_map, mem_filter, mem_univ, true_and]
    exact ⟨fun ⟨q, h1, h2⟩ => ⟨q, h2, h1⟩, fun ⟨q, h1, h2⟩ => ⟨q, h2, h1⟩⟩
  show (if ∃ q : Fin 3, e q = j ∧ (u : ℕ).testBit q = true then !r j else r j) =
    (if j ∈ pkSet e u then !r j else r j)
  by_cases h : j ∈ pkSet e u
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

lemma pk_valid_iff (u : Fin (2 ^ 3)) (i : Fin 3) :
    (∀ q : Fin 3, (u : ℕ).testBit q = true → q = i) ↔ ((u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ)) := by
  revert u i; decide

lemma pkSet_sub_single (e : Fin 3 ↪ Fin N) (u : Fin (2 ^ 3)) (i : Fin 3) :
    pkSet e u ⊆ {e i} ↔ ((u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ)) := by
  rw [← pk_valid_iff]
  constructor
  · intro h q hq
    exact e.injective (mem_singleton.1 (h ((mem_pkSet e u q).2 hq)))
  · intro h j hj
    obtain ⟨q, hq, rfl⟩ := mem_map.1 hj
    rw [h q (mem_filter.1 hq).2]
    exact mem_singleton_self _

lemma pk_mask_ext : ∀ u u' : Fin (2 ^ 3), (∀ q : Fin 3, (u : ℕ).testBit q = (u' : ℕ).testBit q) → u = u' := by
  decide

lemma pkCo_pkCo : ∀ u : Fin (2 ^ 3), pkCo (pkCo u) = u := by decide

lemma pkCo_valid : ∀ (u : Fin (2 ^ 3)) (i : Fin 3), ¬((u : ℕ) = 7 ∨ (u : ℕ) = 7 - 2 ^ (i : ℕ)) →
    ¬(((pkCo u : Fin (2 ^ 3)) : ℕ) = 0 ∨ ((pkCo u : Fin (2 ^ 3)) : ℕ) = 2 ^ (i : ℕ)) := by
  decide

/-! ### The per-member box -/

/-- The target of the private entry `(r ⊕ u, e i)`: `τ u i` if `r` agrees with `tc` on `S`, else `τ (7 ⊕ u) i`. -/
noncomputable def lt3BoxTgt (S : Finset (Fin N)) (tc r : State N) (τ : Fin (2 ^ 3) → Fin 3 → ℝ)
    (u : Fin (2 ^ 3)) (i : Fin 3) : ℝ := by
  classical exact if ∀ j ∈ S, r j = tc j then τ u i else τ (pkCo u) i

/-- The valid pairs `(u, i)`, `u ∉ {0, 2^i}` (the private positions of a block). -/
def lt3VPairs : Finset (Fin (2 ^ 3) × Fin 3) :=
  univ.filter fun x => ¬((x.1 : ℕ) = 0 ∨ (x.1 : ℕ) = 2 ^ (x.2 : ℕ))

lemma lt3VPairs_card : lt3VPairs.card = 18 := by decide

/-- The index set of the box. -/
def lt3BoxIdx (H : Finset (State N)) : Finset (State N × (Fin (2 ^ 3) × Fin 3)) := H ×ˢ lt3VPairs

lemma lt3BoxIdx_card (H : Finset (State N)) : (lt3BoxIdx H).card = 18 * H.card := by
  unfold lt3BoxIdx; rw [card_product, lt3VPairs_card, mul_comm]

lemma mem_lt3BoxIdx {H : Finset (State N)} {x : State N × (Fin (2 ^ 3) × Fin 3)} :
    x ∈ lt3BoxIdx H ↔ x.1 ∈ H ∧ ¬((x.2.1 : ℕ) = 0 ∨ (x.2.1 : ℕ) = 2 ^ (x.2.2 : ℕ)) := by
  simp [lt3BoxIdx, lt3VPairs]

/-- The entry of an index. -/
def lt3BoxE (e : Fin 3 ↪ Fin N) (x : State N × (Fin (2 ^ 3) × Fin 3)) : State N × Fin N :=
  (pkFlip e x.1 x.2.1, e x.2.2)

/-- **The per-member box event.** -/
def lt3Box (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) (tc : State N) (H : Finset (State N))
    (τ : Fin (2 ^ 3) → Fin 3 → ℝ) (ρ : ℝ) : Set (Param N) :=
  {w | ∀ x ∈ lt3BoxIdx H, |clamp01 (w (lt3BoxE e x).1 (lt3BoxE e x).2) - lt3BoxTgt S tc x.1 τ x.2.1 x.2.2| ≤ ρ}

/-- **The box entries are private**: `(r ⊕ u, e i) ∈ lt3PB (S, r)`. -/
lemma lt3Box_entry_PB {e : Fin 3 ↪ Fin N} {S : Finset (Fin N)} (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
    {H : Finset (State N)} {x : State N × (Fin (2 ^ 3) × Fin 3)} (hx : x ∈ lt3BoxIdx H) :
    lt3BoxE e x ∈ lt3PB (S, x.1) := by
  have hv := (mem_lt3BoxIdx.1 hx).2
  unfold lt3PB lt3BoxE
  rw [pkFlip_eq_flipS]
  refine mem_image.2 ⟨(pkSet e x.2.1, e x.2.2), mem_filter.2 ⟨mem_product.2 ⟨mem_powerset.2 (pkSet_sub hS _),
    (hS _).2 ⟨_, rfl⟩⟩, ?_⟩, rfl⟩
  rw [pkSet_sub_single]; exact hv

/-- **The box entries are distinct** (blocks of rows agreeing pairwise on `Q ⊇ S`, `|Q| ≥ 7`). -/
lemma lt3Box_injOn {e : Fin 3 ↪ Fin N} {S Q : Finset (Fin N)} (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) (hSQ : S ⊆ Q)
    (hQ : 7 ≤ Q.card) {tc : State N} {H : Finset (State N)}
    (hag : ∀ r ∈ H, (∀ j ∈ Q, r j = tc j) ∨ (∀ j ∈ Q, r j ≠ tc j)) :
    Set.InjOn (lt3BoxE e) (lt3BoxIdx H : Set (State N × (Fin (2 ^ 3) × Fin 3))) := by
  rintro ⟨r, u, i⟩ hx ⟨r', u', i'⟩ hx' h
  simp only [lt3BoxE, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hi : i = i' := e.injective h2
  rw [pkFlip_eq_flipS, pkFlip_eq_flipS] at h1
  have hr := (mem_lt3BoxIdx.1 hx).1
  have hr' := (mem_lt3BoxIdx.1 hx').1
  obtain ⟨hrr, hR⟩ := flipS_inj_agree hQ ((pkSet_sub hS u).trans hSQ) ((pkSet_sub hS u').trans hSQ)
    (pkSet_card e u) (pkSet_card e u') (agree_pair_tc (hag r hr) (hag r' hr')) h1
  have hu : u = u' := pk_mask_ext u u' fun q => by
    have a := mem_pkSet e u q
    have b := mem_pkSet e u' q
    rw [hR] at a
    exact Bool.eq_iff_iff.2 (a.symm.trans b)
  subst hrr hu hi
  rfl

/-- **The box is measurable.** -/
lemma lt3Box_mset (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) (tc : State N) (H : Finset (State N))
    (τ : Fin (2 ^ 3) → Fin 3 → ℝ) (ρ : ℝ) : MeasurableSet (lt3Box e S tc H τ ρ) := by
  have e1 : lt3Box e S tc H τ ρ = ⋂ x ∈ lt3BoxIdx H,
      {w : Param N | |clamp01 (w (lt3BoxE e x).1 (lt3BoxE e x).2) - lt3BoxTgt S tc x.1 τ x.2.1 x.2.2| ≤ ρ} := by
    ext w; simp [lt3Box]
  rw [e1]
  exact MeasurableSet.biInter (Set.to_countable _) fun x _ =>
    measurableSet_le (continuous_abs.measurable.comp ((b1m_clamp _ _).sub measurable_const)) measurable_const

/-- **The box is determined by the private blocks of its rows.** -/
lemma lt3Box_detOn {e : Fin 3 ↪ Fin N} {S : Finset (Fin N)} (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) (tc : State N)
    (H : Finset (State N)) (τ : Fin (2 ^ 3) → Fin 3 → ℝ) (ρ : ℝ) :
    DetOnE (H.biUnion fun r => lt3PB (S, r)) (lt3Box e S tc H τ ρ) := by
  intro w w' h
  have hx : ∀ x ∈ lt3BoxIdx H, w (lt3BoxE e x).1 (lt3BoxE e x).2 = w' (lt3BoxE e x).1 (lt3BoxE e x).2 :=
    fun x hx => h _ (mem_biUnion.2 ⟨x.1, (mem_lt3BoxIdx.1 hx).1, lt3Box_entry_PB hS hx⟩)
  simp only [lt3Box, Set.mem_setOf_eq]
  exact forall₂_congr fun x hx' => by rw [hx x hx']

/-- One uniform entry lands in the `ρ`-ball of a target in `[0, 1]` with probability `≥ ρ`. -/
lemma unif_ball_ge {τ ρ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ENNReal.ofReal ρ ≤ unif {x | |clamp01 x - τ| ≤ ρ} := by
  set a := min τ (1 - ρ) with ha
  have ha0 : 0 ≤ a := le_min hτ0 (by linarith)
  have ha1 : a + ρ ≤ 1 := by have := min_le_right τ (1 - ρ); linarith
  have haτ : τ - ρ ≤ a := le_min (by linarith) (by linarith)
  have haτ' : a ≤ τ := min_le_left τ (1 - ρ)
  unfold unif
  rw [Measure.restrict_apply' measurableSet_Icc]
  calc ENNReal.ofReal ρ = volume (Set.Icc a (a + ρ)) := by rw [Real.volume_Icc]; congr 1; ring
    _ ≤ volume ({x | |clamp01 x - τ| ≤ ρ} ∩ Set.Icc (0 : ℝ) 1) := measure_mono fun x hx => by
        have hx0 : 0 ≤ x := ha0.trans hx.1
        have hx1 : x ≤ 1 := hx.2.trans ha1
        refine ⟨?_, hx0, hx1⟩
        simp only [Set.mem_setOf_eq]
        rw [clamp01_of_mem ⟨hx0, hx1⟩, abs_le]
        constructor <;> linarith [hx.1, hx.2]

/-- **A box of distinct entries around targets in `[0, 1]` has probability `≥ ρ^{#entries}`.** -/
theorem cubeM_box_ge {B : Type*} [Fintype B] [DecidableEq B] (E : B → State N × Fin N)
    (hE : Function.Injective E) (τ : B → ℝ) (hτ : ∀ b, 0 ≤ τ b ∧ τ b ≤ 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ENNReal.ofReal (ρ ^ Fintype.card B) ≤
      cubeM N {η | ∀ b, |clamp01 (η (E b).1 (E b).2) - τ b| ≤ ρ} := by
  have mp := lt2_mp_inj E hE
  set T : Set (B → ℝ) := Set.univ.pi fun b => {x : ℝ | |clamp01 x - τ b| ≤ ρ} with hTdef
  have hT : MeasurableSet T := MeasurableSet.univ_pi fun b =>
    measurableSet_le (continuous_abs.measurable.comp (measurable_clamp01.sub measurable_const)) measurable_const
  have hpre : {η : Param N | ∀ b, |clamp01 (η (E b).1 (E b).2) - τ b| ≤ ρ} =
      (fun (η : Param N) (b : B) => η (E b).1 (E b).2) ⁻¹' T := by
    ext η; simp [hTdef]
  rw [hpre, mp.measure_preimage hT.nullMeasurableSet, hTdef, Measure.pi_pi]
  calc ENNReal.ofReal (ρ ^ Fintype.card B) = ∏ _b : B, ENNReal.ofReal ρ := by
        rw [Finset.prod_const, Finset.card_univ, ENNReal.ofReal_pow hρ0]
    _ ≤ ∏ b : B, unif {x : ℝ | |clamp01 x - τ b| ≤ ρ} :=
        Finset.prod_le_prod' fun b _ => unif_ball_ge (hτ b).1 (hτ b).2 hρ0 hρ1

/-- **The per-member box has probability `≥ ρ^{18|H|}`** (targets in `[0, 1]`). -/
theorem lt3Box_prob {e : Fin 3 ↪ Fin N} {S Q : Finset (Fin N)} (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) (hSQ : S ⊆ Q)
    (hQ : 7 ≤ Q.card) {tc : State N} {H : Finset (State N)}
    (hag : ∀ r ∈ H, (∀ j ∈ Q, r j = tc j) ∨ (∀ j ∈ Q, r j ≠ tc j)) {τ : Fin (2 ^ 3) → Fin 3 → ℝ}
    (hτ : ∀ u i, 0 ≤ τ u i ∧ τ u i ≤ 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ENNReal.ofReal (ρ ^ (18 * H.card)) ≤ cubeM N (lt3Box e S tc H τ ρ) := by
  classical
  have hinj := lt3Box_injOn hS hSQ hQ hag
  set B := {x // x ∈ lt3BoxIdx H}
  have hE : Function.Injective fun b : B => lt3BoxE e b.1 := fun b b' h =>
    Subtype.ext (hinj b.2 b'.2 h)
  have h := cubeM_box_ge (B := B) (fun b => lt3BoxE e b.1) hE (fun b => lt3BoxTgt S tc b.1.1 τ b.1.2.1 b.1.2.2)
    (fun b => by unfold lt3BoxTgt; split_ifs <;> exact hτ _ _) hρ0 hρ1
  rw [Fintype.card_coe, lt3BoxIdx_card] at h
  refine h.trans (le_of_eq (congrArg _ ?_))
  ext w
  simp only [lt3Box, Set.mem_setOf_eq]
  exact ⟨fun h x hx => h ⟨x, hx⟩, fun h b => h b.1 b.2⟩

/-! ### The RL table of a member -/

/-- The conclusion of `rl_real_window` for `p = (Ts, M, c0)` with window loss `ω'`. -/
def RLWin (d : RLDR) (t : ℚ) (ω' : ℝ) (p : ℕ × (Fin 8 → Fin 3 → ℝ) × ℝ) : Prop :=
  p.1 < 8 ∧ 4 / 5 ≤ p.2.2 ∧ (∀ i, p.2.2 ≤ d.G1 i) ∧ (∀ i, d.G1 i ≤ p.2.2 + ω') ∧
    (∀ (u : Fin 8) (i : Fin 3), rlLoR d u i ≤ p.2.1 u i ∧ p.2.1 u i ≤ rlLoR d u i + rlWdR d u i) ∧
    8 * p.2.2 * (5 / 3 - (t : ℝ)) - 36 * ω' ≤ rlV8R lp3CStar p.1 p.2.1 ∧
    (∀ C ∈ lp3Profiles, C ≠ lp3CStar →
      p.2.2 * (t : ℝ) / 20 - 6 * ω' ≤ rlV8R C p.1 p.2.1 / (8 * (cd_cc 3 C : ℝ)) - rlV8R lp3CStar p.1 p.2.1 / 40) ∧
    (∀ u < 8, u ≠ p.1 → 1 / 20 - 6 * ω' ≤ rlPSR p.2.1 p.1 - rlPSR p.2.1 u)

/-- **The chosen RL table** of real data (Hilbert choice of `RLWin`): a function of the data only. -/
noncomputable def lt3Tab (d : RLDR) (t : ℚ) (ω' : ℝ) : ℕ × (Fin 8 → Fin 3 → ℝ) × ℝ :=
  Classical.epsilon (RLWin d t ω')

lemma lt3Tab_spec {d : RLDR} {t : ℚ} {ω' : ℝ} (h : ∃ p, RLWin d t ω' p) : RLWin d t ω' (lt3Tab d t ω') :=
  Classical.epsilon_spec h

/-- `rl_real_window` in the `RLWin` form. -/
lemma rlWin_exists (dR : RLDR) {n : ℕ} (hn : 0 < n) (h5 : 5 ∣ n) {ω : ℝ} (hω : 0 ≤ ω) (hw : dR.win ω)
    (hG1 : ∀ i, 4 / 5 ≤ dR.G1 i) (hGV : ∀ i, dR.G1 i ≤ dR.V1) (hF1 : ∀ i, 0 ≤ dR.F1 i)
    (hF1V : ∀ i, dR.F1 i ≤ dR.V1) (hV1 : 1 ≤ dR.V1) (hG2 : ∀ i, 0 ≤ dR.G2 i) (hF2 : ∀ i, 0 ≤ dR.F2 i)
    (hG2V : ∀ i, dR.G2 i ≤ dR.V2) (hF2V : ∀ i, dR.F2 i ≤ dR.V2) {t : ℚ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 80) :
    ∃ p, RLWin dR t (ω + 1 / n) p := by
  obtain ⟨Ts, hTs, M, c0, h1, h2, h3, h4, h5', h6, h7⟩ :=
    rl_real_window dR hn h5 hω hw hG1 hGV hF1 hF1V hV1 hG2 hF2 hG2V hF2V ht0 ht
  exact ⟨(Ts, M, c0), hTs, h1, h2, h3, h4, h5', h6, h7⟩

lemma rlMR_coe (M : Fin 8 → Fin 3 → ℝ) (u : Fin 8) (i : Fin 3) : rlMR M u i = M u i := by
  unfold rlMR
  congr 1
  · exact Fin.ext (Nat.mod_eq_of_lt u.2)
  · exact Fin.ext (Nat.mod_eq_of_lt i.2)

/-- **The private targets** `φ = (M - lo)/wd` of a table (`0` on degenerate intervals). -/
noncomputable def lt3Tgt (d : RLDR) (M : Fin 8 → Fin 3 → ℝ) (u : Fin (2 ^ 3)) (i : Fin 3) : ℝ :=
  if rlWdR d u i = 0 then 0 else (rlMR M u i - rlLoR d u i) / rlWdR d u i

/-- The targets realise the table exactly and lie in `[0, 1]`. -/
lemma lt3Tgt_spec (d : RLDR) (M : Fin 8 → Fin 3 → ℝ)
    (hbox : ∀ (u : Fin 8) (i : Fin 3), rlLoR d u i ≤ M u i ∧ M u i ≤ rlLoR d u i + rlWdR d u i)
    (hwd : ∀ (u : Fin (2 ^ 3)) (i : Fin 3), 0 ≤ rlWdR d u i) (v : Fin (2 ^ 3)) (i : Fin 3) :
    rlLoR d v i + rlWdR d v i * lt3Tgt d M v i = rlMR M v i ∧ 0 ≤ lt3Tgt d M v i ∧ lt3Tgt d M v i ≤ 1 := by
  have hb := hbox v i
  have hM : rlMR M v i = M v i := rlMR_coe M v i
  unfold lt3Tgt
  rw [hM]
  split_ifs with h0
  · rw [h0] at hb
    refine ⟨by rw [h0]; linarith [hb.1, hb.2], le_refl _, zero_le_one⟩
  · have hpos : 0 < rlWdR d v i := lt_of_le_of_ne (hwd v i) (Ne.symm h0)
    refine ⟨by field_simp; ring, div_nonneg (by linarith [hb.1]) hpos.le, ?_⟩
    rw [div_le_one hpos]; linarith [hb.2]

/-! ### The real data of a heavy set -/

lemma sub_rlMin3R_le {f : Fin 3 → ℝ} {ω : ℝ} (h : ∀ i i', f i - f i' ≤ ω) (i : Fin 3) :
    f i - rlMin3R f ≤ ω := by
  have : rlMin3R f = f 0 ∨ rlMin3R f = f 1 ∨ rlMin3R f = f 2 := by
    unfold rlMin3R
    rcases min_choice (f 0) (min (f 1) (f 2)) with h0 | h0
    · exact Or.inl h0
    · rw [h0]
      rcases min_choice (f 1) (f 2) with h1 | h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
  rcases this with h' | h' | h' <;> rw [h'] <;> exact h i _

lemma lt3_wsum_spread (T : Finset (State N)) (c x x' : State N → ℝ) (hc0 : ∀ r ∈ T, 0 ≤ c r)
    (hc1 : ∀ r ∈ T, c r ≤ 1) {wb : ℝ} (hwb : 0 ≤ wb) (hx : ∀ r ∈ T, |x r - x' r| ≤ wb) :
    ∑ r ∈ T, c r * x r - ∑ r ∈ T, c r * x' r ≤ T.card * wb := by
  rw [← sum_sub_distrib]
  calc ∑ r ∈ T, (c r * x r - c r * x' r) ≤ ∑ _r ∈ T, wb := sum_le_sum fun r hr => by
        have h1 := (abs_le.1 (hx r hr)).2
        nlinarith [mul_nonneg (hc0 r hr) (sub_nonneg.2 h1), mul_nonneg hwb (sub_nonneg.2 (hc1 r hr))]
    _ = T.card * wb := by rw [sum_const, nsmul_eq_mul]

section RD

variable (w : Param N) (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) (tc : State N) (H : Finset (State N)) {σ : ℝ}

/-- Bounds on the real data of a heavy set (weights `Pw w r / σ ∈ [0, 1]`). -/
lemma lt3RD_bounds (hσ : 0 < σ) (hPw : ∀ r, Pw w r ≤ σ) :
    (∀ i, 0 ≤ (lt3RealData w e S tc H σ).G1 i) ∧ (∀ i, 0 ≤ (lt3RealData w e S tc H σ).F1 i) ∧
      (∀ i, 0 ≤ (lt3RealData w e S tc H σ).G2 i) ∧ (∀ i, 0 ≤ (lt3RealData w e S tc H σ).F2 i) ∧
      (∀ i, (lt3RealData w e S tc H σ).G1 i ≤ (lt3RealData w e S tc H σ).V1) ∧
      (∀ i, (lt3RealData w e S tc H σ).F1 i ≤ (lt3RealData w e S tc H σ).V1) ∧
      (∀ i, (lt3RealData w e S tc H σ).G2 i ≤ (lt3RealData w e S tc H σ).V2) ∧
      (∀ i, (lt3RealData w e S tc H σ).F2 i ≤ (lt3RealData w e S tc H σ).V2) ∧
      0 ≤ (lt3RealData w e S tc H σ).V1 ∧ 0 ≤ (lt3RealData w e S tc H σ).V2 ∧
      (lt3RealData w e S tc H σ).V1 + (lt3RealData w e S tc H σ).V2 ≤ H.card := by
  have hw0 : ∀ r, 0 ≤ Pw w r / σ := fun r => div_nonneg (Pw_nonneg w r) hσ.le
  have hw1 : ∀ r, Pw w r / σ ≤ 1 := fun r => (div_le_one hσ).2 (hPw r)
  have hn : ∀ (T : Finset (State N)) (x : State N → ℝ), 0 ≤ ∑ r ∈ T, Pw w r / σ * clamp01 (x r) :=
    fun T x => sum_nonneg fun r _ => mul_nonneg (hw0 r) (clamp01_nonneg _)
  have hle : ∀ (T : Finset (State N)) (x : State N → ℝ),
      ∑ r ∈ T, Pw w r / σ * clamp01 (x r) ≤ ∑ r ∈ T, Pw w r / σ :=
    fun T x => sum_le_sum fun r _ => mul_le_of_le_one_right (hw0 r) (clamp01_le_one _)
  refine ⟨fun i => hn _ _, fun i => hn _ _, fun i => hn _ _, fun i => hn _ _, fun i => hle _ _, fun i => hle _ _,
    fun i => hle _ _, fun i => hle _ _, sum_nonneg fun r _ => hw0 r, sum_nonneg fun r _ => hw0 r, ?_⟩
  have e1 : (lt3RealData w e S tc H σ).V1 + (lt3RealData w e S tc H σ).V2 = ∑ r ∈ H, Pw w r / σ := by
    simp only [lt3RealData, lt3HA, lt3HB]
    exact sum_filter_add_sum_filter_not H _ _
  rw [e1]
  calc ∑ r ∈ H, Pw w r / σ ≤ ∑ _r ∈ H, (1 : ℝ) := sum_le_sum fun r _ => hw1 r
    _ = H.card := by rw [sum_const, nsmul_eq_mul, mul_one]

/-- `V1 ≥ 1` and `G1 ≥ y_{tc}` when `tc ∈ H` carries the scale `σ = P(tc)`. -/
lemma lt3RD_tc (hσ : 0 < σ) (htcH : tc ∈ H) (hσtc : Pw w tc = σ) :
    1 ≤ (lt3RealData w e S tc H σ).V1 ∧ ∀ i, clamp01 (w tc (e i)) ≤ (lt3RealData w e S tc H σ).G1 i := by
  have hw0 : ∀ r, 0 ≤ Pw w r / σ := fun r => div_nonneg (Pw_nonneg w r) hσ.le
  have htcA : tc ∈ lt3HA S tc H := mem_filter.2 ⟨htcH, fun j _ => rfl⟩
  have h1 : Pw w tc / σ = 1 := by rw [hσtc]; exact div_self hσ.ne'
  refine ⟨?_, fun i => ?_⟩
  · have := single_le_sum (f := fun r => Pw w r / σ) (fun r _ => hw0 r) htcA
    simp only [h1] at this
    exact this
  · have := single_le_sum (f := fun r => Pw w r / σ * clamp01 (w r (e i)))
      (fun r _ => mul_nonneg (hw0 r) (clamp01_nonneg _)) htcA
    simp only [h1, one_mul] at this
    exact this

/-- **The window of the real data**: per-row spread `wb` on the units gives `d.win (|H| wb)`. -/
lemma lt3RD_win (hσ : 0 < σ) (hPw : ∀ r, Pw w r ≤ σ) {wb : ℝ} (hwb : 0 ≤ wb)
    (hwin : ∀ r ∈ H, ∀ i i' : Fin 3, |clamp01 (w r (e i)) - clamp01 (w r (e i'))| ≤ wb ∧
      |clamp01 (w (flip r (e i)) (e i)) - clamp01 (w (flip r (e i')) (e i'))| ≤ wb) :
    (lt3RealData w e S tc H σ).win (H.card * wb) := by
  have hw0 : ∀ r, 0 ≤ Pw w r / σ := fun r => div_nonneg (Pw_nonneg w r) hσ.le
  have hw1 : ∀ r, Pw w r / σ ≤ 1 := fun r => (div_le_one hσ).2 (hPw r)
  have hHA : (lt3HA S tc H).card ≤ H.card := card_filter_le _ _
  have hHB : (lt3HB S tc H).card ≤ H.card := card_filter_le _ _
  have hA : (lt3HA S tc H : Finset (State N)) ⊆ H := filter_subset _ _
  have hB : (lt3HB S tc H : Finset (State N)) ⊆ H := filter_subset _ _
  have key : ∀ (T : Finset (State N)), T.card ≤ H.card → ∀ (x : Fin 3 → State N → ℝ),
      (∀ r ∈ T, ∀ i i', |x i r - x i' r| ≤ wb) →
      ∀ i, (∑ r ∈ T, Pw w r / σ * x i r) - rlMin3R (fun i => ∑ r ∈ T, Pw w r / σ * x i r) ≤ H.card * wb := by
    intro T hTc x hx i
    refine sub_rlMin3R_le (f := fun i => ∑ r ∈ T, Pw w r / σ * x i r) (fun i i' => ?_) i
    refine (lt3_wsum_spread T _ _ _ (fun r _ => hw0 r) (fun r _ => hw1 r) hwb fun r hr => hx r hr i i').trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hTc) hwb
  intro i
  exact ⟨key _ hHA (fun i r => clamp01 (w r (e i))) (fun r hr i i' => (hwin r (hA hr) i i').1) i,
    key _ hHA (fun i r => clamp01 (w (flip r (e i)) (e i))) (fun r hr i i' => (hwin r (hA hr) i i').2) i,
    key _ hHB (fun i r => clamp01 (w r (e i))) (fun r hr i i' => (hwin r (hB hr) i i').1) i,
    key _ hHB (fun i r => clamp01 (w (flip r (e i)) (e i))) (fun r hr i i' => (hwin r (hB hr) i i').2) i⟩

end RD

/-- Interval ends of the real data: `0 ≤ lo`, `0 ≤ wd`, `lo + wd ≤ V1 + V2`. -/
lemma rlLoR_wd_bounds (d : RLDR) (hG1 : ∀ i, 0 ≤ d.G1 i) (hF1 : ∀ i, 0 ≤ d.F1 i) (hG2 : ∀ i, 0 ≤ d.G2 i)
    (hF2 : ∀ i, 0 ≤ d.F2 i) (hG1V : ∀ i, d.G1 i ≤ d.V1) (hF1V : ∀ i, d.F1 i ≤ d.V1) (hG2V : ∀ i, d.G2 i ≤ d.V2)
    (hF2V : ∀ i, d.F2 i ≤ d.V2) (hV1 : 0 ≤ d.V1) (hV2 : 0 ≤ d.V2) (u : Fin (2 ^ 3)) (i : Fin 3) :
    0 ≤ rlLoR d u i ∧ 0 ≤ rlWdR d u i ∧ rlLoR d u i + rlWdR d u i ≤ d.V1 + d.V2 := by
  obtain ⟨hlo, hwd⟩ := rlLoR_split d u i
  rw [hlo, hwd]
  have a1 : 0 ≤ (if (u : ℕ) = 0 then d.G1 i else if (u : ℕ) = 2 ^ (i : ℕ) then d.F1 i else 0) := by
    split_ifs <;> linarith [hG1 i, hF1 i]
  have a2 : 0 ≤ (if (u : ℕ) = 7 then d.G2 i else if (u : ℕ) = 7 - 2 ^ (i : ℕ) then d.F2 i else 0) := by
    split_ifs <;> linarith [hG2 i, hF2 i]
  have b1 : 0 ≤ (if (u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ) then 0 else d.V1) := by split_ifs <;> linarith
  have b2 : 0 ≤ (if (u : ℕ) = 7 ∨ (u : ℕ) = 7 - 2 ^ (i : ℕ) then 0 else d.V2) := by split_ifs <;> linarith
  have c1 : (if (u : ℕ) = 0 then d.G1 i else if (u : ℕ) = 2 ^ (i : ℕ) then d.F1 i else 0) +
      (if (u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ) then 0 else d.V1) ≤ d.V1 := by
    split_ifs <;> first | linarith [hG1V i, hF1V i] | (exfalso; tauto)
  have c2 : (if (u : ℕ) = 7 then d.G2 i else if (u : ℕ) = 7 - 2 ^ (i : ℕ) then d.F2 i else 0) +
      (if (u : ℕ) = 7 ∨ (u : ℕ) = 7 - 2 ^ (i : ℕ) then 0 else d.V2) ≤ d.V2 := by
    split_ifs <;> first | linarith [hG2V i, hF2V i] | (exfalso; tauto)
  exact ⟨by linarith, by linarith, by linarith⟩

/-! ### Lemma TC', packaged -/

/-- The level factor: `P(tc) x / (8 a₃ Z ln 2) = (3/5) levTrip β x`. -/
lemma lt3_level_eq (w : Param N) (hZ : 0 < Zs w) (x : ℝ) :
    Pw w (tcRow w) * x / (8 * (lvK 3 * Zs w) * Real.log 2) = 3 / 5 * levTrip * betaW w * x := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hk := lvK_pos 3
  unfold levTrip betaW
  field_simp
  ring

/-- **Lemma TC' (packaged, deterministic, generic in the level `t ∈ (0, 1/80]`).** For a heavy set `H`
(`|H| ≤ 13`, rows agreeing or disagreeing with `tc` on `S = {a, b, c}`), a table `p = (Ts, M, c0)` satisfying the
windowed RL conclusion `RLWin` of the member's real data with loss `ω' ≤ t/4000`, the private entries in the box of
half-width `ρ` (`13ρ ≤ t/4000`) around the targets `lt3Tgt`, a light part varying by `φL ≤ t σ/4000`, the level band
`|Num - a₃Z| ≤ η` with `η² ≤ t σ a₃Z/10^6`, and the effect side `≥ E0`:
`levTrip · c0 · (1 - 483 t/800) · β ≤ φ_s(S)`. -/
theorem lt3_TCprime {w : Param N} (hw : w ∈ openCube N) (s : State N) {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (H : Finset (State N)) (hHc : H.card ≤ 13)
    (hH : ∀ r ∈ H, (∀ j ∈ ({a, b, c} : Finset (Fin N)), r j = tcRow w j) ∨
      (∀ j ∈ ({a, b, c} : Finset (Fin N)), r j ≠ tcRow w j))
    {t : ℚ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 80) {ω' ρ φL η E0 : ℝ} (p : ℕ × (Fin 8 → Fin 3 → ℝ) × ℝ)
    (hp : RLWin (lt3RealData w (pkE3 hab hac hbc) {a, b, c} (tcRow w) H (Pw w (tcRow w))) t ω' p)
    (hωt : ω' ≤ (t : ℝ) / 4000) (hρ0 : 0 ≤ ρ) (hρt : 13 * ρ ≤ (t : ℝ) / 4000)
    (hbox : w ∈ lt3Box (pkE3 hab hac hbc) {a, b, c} (tcRow w) H
      (lt3Tgt (lt3RealData w (pkE3 hab hac hbc) {a, b, c} (tcRow w) H (Pw w (tcRow w))) p.2.1) ρ)
    (hlight : ∀ (t0 : State N) (u : Fin (2 ^ 3)) (i : Fin 3),
      |lt3Light w {a, b, c} H (pkFlip (pkE3 hab hac hbc) t0 u) (pkE3 hab hac hbc i) -
        lt3Light w {a, b, c} H t0 (pkE3 hab hac hbc i)| ≤ φL)
    (hφL : φL ≤ (t : ℝ) / 4000 * Pw w (tcRow w)) (hη0 : 0 ≤ η)
    (hlev : ∀ Y ⊆ ({a, b, c} : Finset (Fin N)), ∀ t', ∀ i ∈ ({a, b, c} : Finset (Fin N)),
      |Num w {a, b, c} Y t' i - lvK 3 * Zs w| ≤ η)
    (hηs : η ^ 2 ≤ (t : ℝ) / 10 ^ 6 * Pw w (tcRow w) * (lvK 3 * Zs w))
    (hE0 : 6 * η / ((lvK 3 * Zs w - η) * Real.log 2) ≤ E0)
    (heff : ∃ te ∈ sysMaxEffStates (tpmOf (flipP s w)) {a, b, c} s s,
      ∀ θ : SysPartition N {a, b, c}, E0 ≤ sysPhiE (tpmOf (flipP s w)) {a, b, c} s θ s te) :
    levTrip * p.2.2 * (1 - 483 * (t : ℝ) / 800) * betaW w ≤ phi (flipP s w) s {a, b, c} := by
  classical
  set e := pkE3 hab hac hbc with he
  have hS := pkE3_S hab hac hbc
  set S : Finset (Fin N) := {a, b, c} with hSdef
  set tc := tcRow w with htc
  set σ := Pw w tc with hσdef
  have hσ : 0 < σ := b1_Pw_pos hw tc
  have hPw : ∀ r, Pw w r ≤ σ := fun r => Pw_le_tcRow w r
  set d := lt3RealData w e S tc H σ with hd
  obtain ⟨hG1n, hF1n, hG2n, hF2n, hG1V, hF1V, hG2V, hF2V, hV1n, hV2n, hVH⟩ := lt3RD_bounds w e S tc H hσ hPw
  have hV13 : d.V1 + d.V2 ≤ 13 := hVH.trans (by exact_mod_cast hHc)
  obtain ⟨hTs, hc45, -, -, hMbox, hV, hG, hP⟩ := hp
  set Ts := p.1 with hTsdef
  set M := p.2.1 with hMdef
  set c0 := p.2.2 with hc0def
  have hlw := rlLoR_wd_bounds d hG1n hF1n hG2n hF2n hG1V hF1V hG2V hF2V hV1n hV2n
  have hT := lt3Tgt_spec d M hMbox (fun u i => (hlw u i).2.1)
  -- the private hypotheses of Lemma M, from the box
  have hA : ∀ r ∈ lt3HA S tc H, ∀ (u : Fin (2 ^ 3)) (i : Fin 3), ¬((u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ)) →
      |clamp01 (w (pkFlip e r u) (e i)) - lt3Tgt d M u i| ≤ ρ := by
    intro r hr u i hv
    obtain ⟨hrH, hag⟩ := mem_filter.1 hr
    have h := hbox (r, u, i) (mem_lt3BoxIdx.2 ⟨hrH, hv⟩)
    simp only [lt3BoxE, lt3BoxTgt] at h
    rwa [if_pos hag] at h
  have hB : ∀ r ∈ lt3HB S tc H, ∀ (u : Fin (2 ^ 3)) (i : Fin 3), ¬((u : ℕ) = 7 ∨ (u : ℕ) = 7 - 2 ^ (i : ℕ)) →
      |clamp01 (w (pkFlip e r (pkCo u)) (e i)) - lt3Tgt d M u i| ≤ ρ := by
    intro r hr u i hv
    obtain ⟨hrH, hag⟩ := mem_filter.1 hr
    have h := hbox (r, pkCo u, i) (mem_lt3BoxIdx.2 ⟨hrH, pkCo_valid u i hv⟩)
    simp only [lt3BoxE, lt3BoxTgt] at h
    rwa [if_neg hag, pkCo_pkCo] at h
  set Ts' : Fin (2 ^ 3) := ⟨Ts, by simpa using hTs⟩ with hTs'
  set t0 := pkFlip e tc Ts' with ht0def
  have hφL0 : 0 ≤ φL := (abs_nonneg _).trans (hlight tc 0 0)
  set φ := σ * (13 * ρ) + φL with hφdef
  have hdec0 := lt3_hdec w e hS tc H hσ hρ0 hH (lt3Tgt d M) hA hB M Ts' (fun v i => (hT v i).1)
    (fun u i => hlight t0 u i)
  have hinv : flipP s (flipP s w) = w := flipP_invol s w
  have hz : flipP s w ∈ openCube N := flipP_mem_openCube hw
  have hdec : ∀ (i : Fin 3) (u : Fin 8), |Num (flipP s (flipP s w)) S S (pkFlip e t0 u) (e i) -
      (σ * rlMR M (Ts ^^^ (u : ℕ)) i + lt3Light w S H t0 (e i))| ≤ φ := by
    intro i u
    rw [hinv]
    refine (hdec0 i u).trans ?_
    have : σ * ((d.V1 + d.V2) * ρ) ≤ σ * (13 * ρ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hV13 hρ0) hσ.le
    linarith
  -- the scales
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  have htR1 : (t : ℝ) ≤ 1 / 80 := by
    have h := (Rat.cast_le (K := ℝ)).2 ht1
    norm_num at h
    exact h
  set A := lvK 3 * Zs w with hAdef
  have hZ : 0 < Zs w := b1_Zs_pos hw
  have hA : 0 < A := mul_pos (lvK_pos 3) hZ
  have hσZ : σ ≤ Zs w := single_le_sum (f := fun r => Pw w r) (fun r _ => Pw_nonneg w r) (mem_univ tc)
  have hσA : σ ≤ 2 * A := by rw [hAdef, lvK_three]; linarith
  have hηA3 : 3 * η ≤ A := by
    by_contra hcon
    push Not at hcon
    have h1 : A * A < (3 * η) * (3 * η) := mul_self_lt_mul_self hA.le hcon
    have h2 : (t : ℝ) / 10 ^ 6 * σ * A ≤ (t : ℝ) / 10 ^ 6 * (2 * A) * A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hσA (by positivity)) hA.le
    have h3 : (t : ℝ) / 10 ^ 6 * (2 * A) * A ≤ 1 / 10 ^ 6 * (A * A) := by
      have e1 : (t : ℝ) / 10 ^ 6 * (2 * A) * A = 2 * t / 10 ^ 6 * (A * A) := by ring
      rw [e1]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e2 : (3 * η) * (3 * η) = 9 * η ^ 2 := by ring
    have hAA : 0 < A * A := by positivity
    linarith
  have hAη : 2 * A / 3 ≤ A - η := by linarith
  have hAη0 : 0 < A - η := by linarith
  -- the error terms
  have hφLσ : φL / σ ≤ (t : ℝ) / 4000 := by rw [div_le_iff₀ hσ]; linarith
  have hE : 6 * φ / σ = 78 * ρ + 6 * (φL / σ) := by rw [hφdef]; field_simp; ring
  have hEt : 6 * φ / σ ≤ 3 * (t : ℝ) / 1000 := by rw [hE]; linarith
  have hE0' : 0 ≤ 6 * φ / σ := by rw [hE]; have := div_nonneg hφL0 hσ.le; positivity
  have hc0t : (4 : ℝ) / 5 * t ≤ c0 * t := mul_le_mul_of_nonneg_right hc45 htR.le
  have h53 : (4 : ℝ) / 5 * (5 / 3 - t) ≤ c0 * (5 / 3 - t) := mul_le_mul_of_nonneg_right hc45 (by linarith)
  set y := c0 * (5 / 3 - (t : ℝ)) - 36 * ω' / 8 - 78 * ρ - 6 * ((t : ℝ) / 4000) with hydef
  have hy1 : 1 ≤ y := by rw [hydef]; linarith
  have hy0 : 0 < y := by linarith
  have hyV : y ≤ (c0 * (5 / 3 - (t : ℝ)) - 36 * ω' / 8) - 6 * φ / σ := by rw [hE, hydef]; linarith
  set δ := (t : ℝ) / 10 ^ 4 with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  -- (V), (G), (P) and the bound `Fm`
  have hV' : c0 * (5 / 3 - (t : ℝ)) - 36 * ω' / 8 ≤ rlV8R lp3CStar Ts M / 8 := by linarith
  have hstar : lp3CStar ∈ lp3Profiles := by decide +kernel
  have hFmax : rlV8R lp3CStar Ts M / 8 ≤ 59 := by
    have hM13 : ∀ (u : Fin 8) (i : Fin 3), |M u i - (fun _ _ => (0 : ℝ)) u i| ≤ 13 := by
      intro u i
      have hb := hMbox u i
      have hl := hlw u i
      simp only [sub_zero]
      rw [abs_le]; constructor <;> linarith [hb.1, hb.2, hl.1, hl.2.2]
    have h := rlV8R_pert hstar Ts hM13
    have h0 : rlV8R lp3CStar Ts (fun _ _ => (0 : ℝ)) = 0 := by simp [rlV8R, rlMR]
    rw [h0, sub_zero] at h
    have := (abs_le.1 h).2
    linarith
  have hδG : δ * (59 + 6 * φ / σ) / 5 + 6 * (6 * φ / σ) / 5 ≤ c0 * (t : ℝ) / 20 - 6 * ω' := by
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
    have htσA : 0 < (t : ℝ) * σ * A := by positivity
    have e1 : δ * σ * (2 * A / 3) = ((t : ℝ) * σ * A) * (2 / 30000) := by rw [hδdef]; ring
    have e2 : 36 * ((t : ℝ) / 10 ^ 6 * σ * A) = ((t : ℝ) * σ * A) * (36 / 10 ^ 6) := by ring
    linarith
  have hmsmall : 24 * A * η ^ 2 < (A - η) ^ 2 * (σ * (1 / 20 - 6 * ω') - 6 * φ) := by
    have hσP : σ * (1 / 20 - 6 * ω') - 6 * φ = σ * ((1 / 20 - 6 * ω') - 6 * φ / σ) := by
      field_simp
    have hPE : (1 : ℝ) / 25 ≤ (1 / 20 - 6 * ω') - 6 * φ / σ := by linarith
    have hsq : 4 * A ^ 2 / 9 ≤ (A - η) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hAη 2
      have e : (2 * A / 3) ^ 2 = 4 * A ^ 2 / 9 := by ring
      linarith
    have r1 : (4 * A ^ 2 / 9) * (σ * (1 / 25)) ≤ (A - η) ^ 2 * (σ * ((1 / 20 - 6 * ω') - 6 * φ / σ)) :=
      mul_le_mul hsq (mul_le_mul_of_nonneg_left hPE hσ.le) (by positivity) (by positivity)
    have l1 : 24 * A * η ^ 2 ≤ 24 * A * ((t : ℝ) / 10 ^ 6 * σ * A) :=
      mul_le_mul_of_nonneg_left hηs (by positivity)
    have l2 : 24 * A * ((t : ℝ) / 10 ^ 6 * σ * A) = (σ * A ^ 2) * (24 * t / 10 ^ 6) := by ring
    have l3 : (σ * A ^ 2) * (24 * (t : ℝ) / 10 ^ 6) ≤ (σ * A ^ 2) * (3 / 10 ^ 7) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have r2 : (4 * A ^ 2 / 9) * (σ * (1 / 25)) = (σ * A ^ 2) * (4 / 225) := by ring
    have hσA2 : 0 < σ * A ^ 2 := by positivity
    rw [hσP]
    linarith
  have hlev' : ∀ Y ⊆ S, ∀ t', ∀ i ∈ S, |Num (flipP s (flipP s w)) S Y t' i - A| ≤ η := by
    rw [hinv]; exact hlev
  have hmain := triple_lower_rl (z := flipP s w) hz s hab hac hbc t0 hTs M (fun j => lt3Light w S H t0 j)
    (A := A) (η := η) (δ := δ) (σ := σ) (φ := φ) (y := y) (Fm := 59) (E0 := E0)
    hη0 hηA3 hA hδ0 hσ hlev' hdec hV' hG hP hFmax hy0 hyV hδG hsmall hmsmall hE0 heff
  -- the level
  set q := 6 * η ^ 2 / ((A - η) * σ) with hqdef
  have hq : q ≤ 9 * (t : ℝ) / 10 ^ 6 := by
    rw [hqdef, div_le_iff₀ (mul_pos hAη0 hσ)]
    have k : 9 * (t : ℝ) / 10 ^ 6 * ((2 * A / 3) * σ) ≤ 9 * (t : ℝ) / 10 ^ 6 * ((A - η) * σ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAη hσ.le) (by positivity)
    have e3 : 9 * (t : ℝ) / 10 ^ 6 * ((2 * A / 3) * σ) = 6 * ((t : ℝ) / 10 ^ 6 * σ * A) := by ring
    linarith
  have hyq : c0 * (5 / 3 - 161 * (t : ℝ) / 160) ≤ y - q := by
    have e4 : c0 * (5 / 3 - 161 * (t : ℝ) / 160) = c0 * (5 / 3 - t) - c0 * t / 160 := by ring
    rw [e4, hydef]
    linarith
  have hβ : 0 ≤ betaW w := div_nonneg (Pw_nonneg w _) hZ.le
  have hlt := levTrip_pos
  calc levTrip * c0 * (1 - 483 * (t : ℝ) / 800) * betaW w
      = 3 / 5 * levTrip * betaW w * (c0 * (5 / 3 - 161 * (t : ℝ) / 160)) := by ring
    _ ≤ 3 / 5 * levTrip * betaW w * (y - q) := mul_le_mul_of_nonneg_left hyq (by positivity)
    _ = σ * (y - q) / (8 * A * Real.log 2) := (lt3_level_eq w hZ (y - q)).symm
    _ ≤ phi (flipP s w) s {a, b, c} := hmain

/-! ### The windowed instance: members of `lt3WSel` -/

/-- The heavy set of the windowed configuration: `tc` and the special rows. -/
noncomputable def lt3H (w : Param N) : Finset (State N) := insert (tcRow w) (lt2Sp w)

/-- The real data of member `S` (units ordered by `e`). -/
noncomputable def lt3WData (w : Param N) (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) : RLDR :=
  lt3RealData w e S (tcRow w) (lt3H w) (Pw w (tcRow w))

/-- **The per-member success event** (level `t`, window loss `ω'`, box half-width `ρ`): every private entry of the
blocks of `tc` and of the special rows lies within `ρ` of its target for the RL table `lt3Tab` chosen from the
member's data. -/
def lt3WSucc (t : ℚ) (ω' ρ : ℝ) (e : Fin 3 ↪ Fin N) (S : Finset (Fin N)) (w : Param N) : Prop :=
  w ∈ lt3Box e S (tcRow w) (lt3H w) (lt3Tgt (lt3WData w e S) (lt3Tab (lt3WData w e S) t ω').2.1) ρ

lemma RLDR.win_mono {d : RLDR} {ω ω' : ℝ} (h : d.win ω) (hle : ω ≤ ω') : d.win ω' := fun i =>
  ⟨(h i).1.trans hle, (h i).2.1.trans hle, (h i).2.2.1.trans hle, (h i).2.2.2.trans hle⟩

lemma RLWin_mono {d : RLDR} {t : ℚ} {ω₁ ω₂ : ℝ} {p : ℕ × (Fin 8 → Fin 3 → ℝ) × ℝ} (hle : ω₁ ≤ ω₂)
    (h : RLWin d t ω₁ p) : RLWin d t ω₂ p := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, fun i => (h4 i).trans (by linarith), h5, by linarith, fun C hC hne => ?_,
    fun u hu hne => ?_⟩
  · have := h7 C hC hne; linarith
  · have := h8 u hu hne; linarith

/-- Unpacking a member of the windowed selection. -/
lemma lt3W_mem {s : State N} {ε γ : ℝ} {nb : ℕ} {w : Param N} {k : Finset (Fin N) × State N}
    (hk : k ∈ lt3WSel s ε γ nb w) :
    Real.exp (-(3 / 10 * (N : ℝ))) < Pw w (tcRow w) ∧ 7 ≤ (lt3WQ s ε γ nb w).card ∧
      (∀ j ∈ lt3WQ s ε γ nb w, 4 / 5 ≤ clamp01 (w (tcRow w) j)) ∧ k.1 ∈ lt3WF s ε γ nb w ∧
      k.2 ∈ lt3Base s w ∧ k.1 ⊆ lt3WQ s ε γ nb w ∧
      ∀ r ∈ lt3Base s w, (∀ j ∈ lt3Q s ε γ w, r j = tcRow w j) ∨ (∀ j ∈ lt3Q s ε γ w, r j ≠ tcRow w j) := by
  classical
  have hspec := (lt3QOf_spec (lt3Base s w) (lt3Top s w ε \ lt3Ex s ε γ w) (tcRow w)).2.2
  unfold lt3WSel at hk
  split_ifs at hk with hc
  · obtain ⟨hS, hr⟩ := mem_product.1 hk
    exact ⟨hc.1, hc.2.1, hc.2.2, hS, hr, qFam_sub (mem_filter.1 hS).1, hspec⟩
  · simp at hk

lemma lt3H_sub_base (s : State N) (w : Param N) : lt3H w ⊆ lt3Base s w :=
  insert_subset_insert _ (subset_insert _ _)

lemma lt3H_card {w : Param N} (hSp : (lt2Sp w).card < 12) : (lt3H w).card ≤ 13 :=
  (card_insert_le _ _).trans (by omega)

/-- **The chosen table satisfies the windowed RL conclusion** for a member of `lt3WSel` (`|Sp| < 12`,
window loss `ω' ≥ 13/(n_b + 1) + 1/n_g`, `5 ∣ n_g`). -/
theorem lt3W_tab_spec {s : State N} {ε γ : ℝ} {nb : ℕ} {w : Param N} (hw : w ∈ openCube N) {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {r0 : State N}
    (hk : (({a, b, c} : Finset (Fin N)), r0) ∈ lt3WSel s ε γ nb w) (hSp : (lt2Sp w).card < 12)
    {ng : ℕ} (hng : 0 < ng) (h5 : 5 ∣ ng) {t : ℚ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 80) {ω' : ℝ}
    (hω' : 13 * (1 / ((nb + 1 : ℕ) : ℝ)) + 1 / (ng : ℝ) ≤ ω') :
    RLWin (lt3WData w (pkE3 hab hac hbc) {a, b, c}) t ω'
      (lt3Tab (lt3WData w (pkE3 hab hac hbc) {a, b, c}) t ω') := by
  obtain ⟨-, -, hfl, -, -, hSWQ, -⟩ := lt3W_mem hk
  set e := pkE3 hab hac hbc
  have hS := pkE3_S hab hac hbc
  have heS : ∀ i, e i ∈ ({a, b, c} : Finset (Fin N)) := fun i => (hS _).2 ⟨i, rfl⟩
  have hσ := b1_Pw_pos hw (tcRow w)
  have hPw : ∀ r, Pw w r ≤ Pw w (tcRow w) := fun r => Pw_le_tcRow w r
  have hwin : ∀ r ∈ lt3H w, ∀ i i' : Fin 3,
      |clamp01 (w r (e i)) - clamp01 (w r (e i'))| ≤ 1 / ((nb + 1 : ℕ) : ℝ) ∧
      |clamp01 (w (flip r (e i)) (e i)) - clamp01 (w (flip r (e i')) (e i'))| ≤ 1 / ((nb + 1 : ℕ) : ℝ) :=
    fun r hr i i' => lt3WQ_window s ε γ nb w (hSWQ (heS i)) (hSWQ (heS i')) (lt3H_sub_base s w hr)
  have hd := lt3RD_win w e {a, b, c} (tcRow w) (lt3H w) hσ hPw (by positivity) hwin
  have hd' : (lt3WData w e {a, b, c}).win (13 * (1 / ((nb + 1 : ℕ) : ℝ))) :=
    RLDR.win_mono hd (mul_le_mul_of_nonneg_right (by exact_mod_cast lt3H_card hSp) (by positivity))
  obtain ⟨hG1n, hF1n, hG2n, hF2n, hG1V, hF1V, hG2V, hF2V, -, -, -⟩ :=
    lt3RD_bounds w e {a, b, c} (tcRow w) (lt3H w) hσ hPw
  obtain ⟨hV1, hG1tc⟩ := lt3RD_tc w e {a, b, c} (tcRow w) (lt3H w) hσ (mem_insert_self _ _) rfl
  have hG1 : ∀ i, 4 / 5 ≤ (lt3WData w e {a, b, c}).G1 i := fun i => (hfl _ (hSWQ (heS i))).trans (hG1tc i)
  obtain ⟨p, hp⟩ := rlWin_exists (lt3WData w e {a, b, c}) hng h5 (by positivity) hd' hG1 hG1V hF1n hF1V hV1
    hG2n hF2n hG2V hF2V ht0 ht1
  exact lt3Tab_spec ⟨p, RLWin_mono hω' hp⟩

/-- The fibres of `v ↦ merge S t v` have at most `2^{|S|} ≤ 8` elements. -/
lemma merge_fib_card {S : Finset (Fin N)} (hS : S.card ≤ 3) (t q : State N) (V : Finset (State N)) :
    (V.filter fun v => merge S t v = q).card ≤ 8 := by
  classical
  calc (V.filter fun v => merge S t v = q).card ≤ (univ : Finset (S → Bool)).card := by
        refine card_le_card_of_injOn (fun v (j : S) => v j) (fun _ _ => by simp) ?_
        intro v hv v' hv' h
        have hv1 := (mem_filter.1 (mem_coe.1 hv)).2
        have hv2 := (mem_filter.1 (mem_coe.1 hv')).2
        funext j
        by_cases hj : j ∈ S
        · exact congrFun h ⟨j, hj⟩
        · have a1 := congrFun hv1 j
          have a2 := congrFun hv2 j
          rw [merge_not_mem hj] at a1 a2
          rw [a1, a2]
    _ = 2 ^ S.card := by simp
    _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hS
    _ = 8 := by norm_num

/-- **The light part moves by at most the perturbation error** between `w` and `w½` (`lt3W_pert`, `V = Hᶜ`,
`Sp ⊆ H`). -/
theorem lt3Light_pert (s : State N) (ε γ : ℝ) (nb : ℕ) (w : Param N) {S : Finset (Fin N)} (hS3 : S.card ≤ 3)
    {H : Finset (State N)} (hSpH : lt2Sp w ⊆ H) (t : State N) (j : Fin N) :
    |lt3Light w S H t j - lt3Light (stHalf (stPriv (lt3WSel s ε γ nb) lt3PB w) w) S H t j| ≤
      ((stPriv (lt3WSel s ε γ nb) lt3PB w).card * (1 + 8) : ℕ) *
        (Real.exp (-(3 / 10 * (N : ℝ))) + Real.exp (-(lt2x1 * N))) :=
  lt3W_pert s ε γ nb w Hᶜ (fun _ hv hsp => (mem_compl.1 hv) (hSpH hsp)) (fun v => merge S t v) j
    (fun x => ∏ i, clamp01 (x i)) (fun _ => prod_nonneg fun _ _ => clamp01_nonneg _) (fun _ => le_refl _) 8
    (fun q => merge_fib_card hS3 t q Hᶜ)

/-- **Lemma TC' for a member of the windowed selection** (generic level `t ∈ (0, 1/80]`). The light part is the
`stHalf` statistic `φH` plus twice the perturbation error of `lt3W_pert`; the success event is `lt3WSucc`. -/
theorem lt3W_TCprime {w : Param N} (hw : w ∈ openCube N) (s : State N) (ε γ : ℝ) (nb : ℕ) {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {r0 : State N}
    (hk : (({a, b, c} : Finset (Fin N)), r0) ∈ lt3WSel s ε γ nb w) (hSp : (lt2Sp w).card < 12)
    {ng : ℕ} (hng : 0 < ng) (h5 : 5 ∣ ng) {t : ℚ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 80) {ω' ρ φH η E0 : ℝ}
    (hω' : 13 * (1 / ((nb + 1 : ℕ) : ℝ)) + 1 / (ng : ℝ) ≤ ω') (hωt : ω' ≤ (t : ℝ) / 4000)
    (hρ0 : 0 ≤ ρ) (hρt : 13 * ρ ≤ (t : ℝ) / 4000)
    (hsucc : lt3WSucc t ω' ρ (pkE3 hab hac hbc) {a, b, c} w)
    (hHalf : ∀ (t0 : State N) (u : Fin (2 ^ 3)) (i : Fin 3),
      |lt3Light (stHalf (stPriv (lt3WSel s ε γ nb) lt3PB w) w) {a, b, c} (lt3H w)
          (pkFlip (pkE3 hab hac hbc) t0 u) (pkE3 hab hac hbc i) -
        lt3Light (stHalf (stPriv (lt3WSel s ε γ nb) lt3PB w) w) {a, b, c} (lt3H w) t0 (pkE3 hab hac hbc i)| ≤ φH)
    (hbud : φH + 2 * ((((stPriv (lt3WSel s ε γ nb) lt3PB w).card * (1 + 8) : ℕ) : ℝ) *
        (Real.exp (-(3 / 10 * (N : ℝ))) + Real.exp (-(lt2x1 * N)))) ≤ (t : ℝ) / 4000 * Pw w (tcRow w))
    (hη0 : 0 ≤ η)
    (hlev : ∀ Y ⊆ ({a, b, c} : Finset (Fin N)), ∀ t', ∀ i ∈ ({a, b, c} : Finset (Fin N)),
      |Num w {a, b, c} Y t' i - lvK 3 * Zs w| ≤ η)
    (hηs : η ^ 2 ≤ (t : ℝ) / 10 ^ 6 * Pw w (tcRow w) * (lvK 3 * Zs w))
    (hE0 : 6 * η / ((lvK 3 * Zs w - η) * Real.log 2) ≤ E0)
    (heff : ∃ te ∈ sysMaxEffStates (tpmOf (flipP s w)) {a, b, c} s s,
      ∀ θ : SysPartition N {a, b, c}, E0 ≤ sysPhiE (tpmOf (flipP s w)) {a, b, c} s θ s te) :
    ∃ c0 : ℝ, 4 / 5 ≤ c0 ∧ (∀ j ∈ ({a, b, c} : Finset (Fin N)), clamp01 (w (tcRow w) j) - ω' ≤ c0) ∧
      levTrip * c0 * (1 - 483 * (t : ℝ) / 800) * betaW w ≤ phi (flipP s w) s {a, b, c} := by
  classical
  obtain ⟨-, h7, -, -, -, hSWQ, hag⟩ := lt3W_mem hk
  set e := pkE3 hab hac hbc with he
  have hS := pkE3_S hab hac hbc
  have hp := lt3W_tab_spec hw hab hac hbc hk hSp hng h5 ht0.le ht1 hω'
  set p := lt3Tab (lt3WData w e {a, b, c}) t ω' with hpdef
  have hσ := b1_Pw_pos hw (tcRow w)
  obtain ⟨-, hG1tc⟩ := lt3RD_tc w e {a, b, c} (tcRow w) (lt3H w) hσ (mem_insert_self _ _) rfl
  have hSQ : ({a, b, c} : Finset (Fin N)) ⊆ lt3Q s ε γ w := hSWQ.trans (lt3WQ_sub s ε γ nb w)
  have hH : ∀ r ∈ lt3H w, (∀ j ∈ ({a, b, c} : Finset (Fin N)), r j = tcRow w j) ∨
      (∀ j ∈ ({a, b, c} : Finset (Fin N)), r j ≠ tcRow w j) := fun r hr => by
    rcases hag r (lt3H_sub_base s w hr) with h | h
    · exact Or.inl fun j hj => h j (hSQ hj)
    · exact Or.inr fun j hj => h j (hSQ hj)
  have hS3 : ({a, b, c} : Finset (Fin N)).card ≤ 3 := card_le_three
  set Ep := ((((stPriv (lt3WSel s ε γ nb) lt3PB w).card * (1 + 8) : ℕ) : ℝ) *
    (Real.exp (-(3 / 10 * (N : ℝ))) + Real.exp (-(lt2x1 * N)))) with hEp
  have hlight : ∀ (t0 : State N) (u : Fin (2 ^ 3)) (i : Fin 3),
      |lt3Light w {a, b, c} (lt3H w) (pkFlip e t0 u) (e i) - lt3Light w {a, b, c} (lt3H w) t0 (e i)| ≤
        φH + 2 * Ep := by
    intro t0 u i
    have h1 := abs_le.1 (lt3Light_pert s ε γ nb w hS3 (H := lt3H w) (subset_insert _ _) (pkFlip e t0 u) (e i))
    have h2 := abs_le.1 (lt3Light_pert s ε γ nb w hS3 (H := lt3H w) (subset_insert _ _) t0 (e i))
    have h3 := abs_le.1 (hHalf t0 u i)
    rw [← hEp] at h1 h2
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  refine ⟨p.2.2, hp.2.1, fun j hj => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := (hS j).1 hj
    have h1 := hp.2.2.2.1 i
    have h2 := hG1tc i
    simp only [lt3WData] at h1
    linarith
  · exact lt3_TCprime hw s hab hac hbc (lt3H w) (lt3H_card hSp) hH ht0 ht1 p hp hωt hρ0 hρt hsucc hlight
      hbud hη0 hlev hηs hE0 heff

/-! ### The perturbation budget for `N` large -/

/-- `|lt3WSel| ≤ 13 N²` when `|Sp| < 12`. -/
lemma lt3WSel_card (s : State N) (ε γ : ℝ) (nb : ℕ) {w : Param N} (hSp : (lt2Sp w).card < 12) :
    (lt3WSel s ε γ nb w).card ≤ 13 * (N * N) := by
  classical
  unfold lt3WSel
  split_ifs
  · rw [card_product]
    have h1 : (lt3WF s ε γ nb w).card ≤ N * N := by
      unfold lt3WF; exact (card_filter_le _ _).trans (qFam_card_le_sq _)
    have h2 : (lt3Base s w).card ≤ 13 :=
      (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans (by omega)))
    calc (lt3WF s ε γ nb w).card * (lt3Base s w).card ≤ (N * N) * 13 := Nat.mul_le_mul h1 h2
      _ = 13 * (N * N) := by ring
  · simp

/-- **The perturbation error is absorbed for `N` large**: `2 · 9|Priv| (e^{-3N/10} + e^{-x₁N}) ≤ t e^{-(x₁-1/800)N}/8000`
whenever `|Priv| ≤ 24 · 13 N²`. -/
theorem lt3_pert_ev {t : ℝ} (ht : 0 < t) : ∀ᶠ N : ℕ in Filter.atTop, ∀ P : ℕ, P ≤ 24 * (13 * (N * N)) →
    2 * (((P * (1 + 8) : ℕ) : ℝ) * (Real.exp (-(3 / 10 * (N : ℝ))) + Real.exp (-(lt2x1 * N)))) ≤
      t / 8000 * Real.exp (-((lt2x1 - 1 / 800) * N)) := by
  filter_upwards [cr_ev_poly_exp 2 (Real.log (11232 * 8000 / t)) (δ := 1 / 800) (by norm_num)] with N hN P hP
  rw [Real.exp_log (by positivity)] at hN
  have hx1 := lt2x1_bounds
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have he1 : Real.exp (-(3 / 10 * (N : ℝ))) ≤ Real.exp (-(lt2x1 * N)) := Real.exp_le_exp.2 (by nlinarith)
  have hP' : ((P * (1 + 8) : ℕ) : ℝ) ≤ 2808 * ((N : ℝ) + 1) ^ 2 := by
    have h9 : P * (1 + 8) ≤ 2808 * (N * N) := by omega
    calc ((P * (1 + 8) : ℕ) : ℝ) ≤ ((2808 * (N * N) : ℕ) : ℝ) := by exact_mod_cast h9
      _ = 2808 * ((N : ℝ) * N) := by push_cast; ring
      _ ≤ 2808 * ((N : ℝ) + 1) ^ 2 := by nlinarith
  set E := Real.exp (-(lt2x1 * N)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hsplit : Real.exp (-((lt2x1 - 1 / 800) * N)) = E * Real.exp (1 / 800 * N) := by
    rw [hE, ← Real.exp_add]; ring_nf
  have k1 : ((P * (1 + 8) : ℕ) : ℝ) * (Real.exp (-(3 / 10 * (N : ℝ))) + E) ≤
      (2808 * ((N : ℝ) + 1) ^ 2) * (2 * E) :=
    mul_le_mul hP' (by linarith) (by positivity) (by positivity)
  have k2 : (t / 8000 * E) * (((N : ℝ) + 1) ^ 2 * (11232 * 8000 / t)) ≤ (t / 8000 * E) * Real.exp (1 / 800 * N) :=
    mul_le_mul_of_nonneg_left hN (by positivity)
  have k3 : (t / 8000 * E) * (((N : ℝ) + 1) ^ 2 * (11232 * 8000 / t)) = 2 * ((2808 * ((N : ℝ) + 1) ^ 2) * (2 * E)) := by
    field_simp; ring
  rw [hsplit]
  nlinarith

/-- **Lemma TC' for members of `lt3WSel`, `N` large** (generic level `t ∈ (0, 1/80]`): the perturbation error is
absorbed when `P(tc) ≥ e^{-(x₁ - 1/800)N}`; the remaining inputs are the `stHalf` light statistic `≤ t σ/8000`,
the level band, the effect side and the success event. -/
theorem lt3W_TCprime_ev {t : ℚ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 80) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (w : Param N) (s : State N) (ε γ : ℝ) (nb : ℕ) (a b c : Fin N) (hab : a ≠ b)
      (hac : a ≠ c) (hbc : b ≠ c) (r0 : State N) (ng : ℕ) (ω' ρ φH η E0 : ℝ), w ∈ openCube N →
      (({a, b, c} : Finset (Fin N)), r0) ∈ lt3WSel s ε γ nb w → (lt2Sp w).card < 12 → 0 < ng → 5 ∣ ng →
      13 * (1 / ((nb + 1 : ℕ) : ℝ)) + 1 / (ng : ℝ) ≤ ω' → ω' ≤ (t : ℝ) / 4000 → 0 ≤ ρ →
      13 * ρ ≤ (t : ℝ) / 4000 → lt3WSucc t ω' ρ (pkE3 hab hac hbc) {a, b, c} w →
      (∀ (t0 : State N) (u : Fin (2 ^ 3)) (i : Fin 3),
        |lt3Light (stHalf (stPriv (lt3WSel s ε γ nb) lt3PB w) w) {a, b, c} (lt3H w)
            (pkFlip (pkE3 hab hac hbc) t0 u) (pkE3 hab hac hbc i) -
          lt3Light (stHalf (stPriv (lt3WSel s ε γ nb) lt3PB w) w) {a, b, c} (lt3H w) t0
            (pkE3 hab hac hbc i)| ≤ φH) →
      φH ≤ (t : ℝ) / 8000 * Pw w (tcRow w) →
      Real.exp (-((lt2x1 - 1 / 800) * N)) ≤ Pw w (tcRow w) → 0 ≤ η →
      (∀ Y ⊆ ({a, b, c} : Finset (Fin N)), ∀ t', ∀ i ∈ ({a, b, c} : Finset (Fin N)),
        |Num w {a, b, c} Y t' i - lvK 3 * Zs w| ≤ η) →
      η ^ 2 ≤ (t : ℝ) / 10 ^ 6 * Pw w (tcRow w) * (lvK 3 * Zs w) →
      6 * η / ((lvK 3 * Zs w - η) * Real.log 2) ≤ E0 →
      (∃ te ∈ sysMaxEffStates (tpmOf (flipP s w)) {a, b, c} s s,
        ∀ θ : SysPartition N {a, b, c}, E0 ≤ sysPhiE (tpmOf (flipP s w)) {a, b, c} s θ s te) →
      ∃ c0 : ℝ, 4 / 5 ≤ c0 ∧ (∀ j ∈ ({a, b, c} : Finset (Fin N)), clamp01 (w (tcRow w) j) - ω' ≤ c0) ∧
        levTrip * c0 * (1 - 483 * (t : ℝ) / 800) * betaW w ≤ phi (flipP s w) s {a, b, c} := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  filter_upwards [lt3_pert_ev htR] with N hN w s ε γ nb a b c hab hac hbc r0 ng ω' ρ φH η E0 hw hk hSp hng h5 hω'
    hωt hρ0 hρt hsucc hHalf hφH hσN hη0 hlev hηs hE0 heff
  have hP := (lt3W_Priv_card s ε γ nb w).trans (Nat.mul_le_mul_left 24 (lt3WSel_card s ε γ nb hSp))
  have h2 := hN _ hP
  refine lt3W_TCprime hw s ε γ nb hab hac hbc hk hSp hng h5 ht0 ht1 hω' hωt hρ0 hρt hsucc hHalf ?_ hη0 hlev hηs
    hE0 heff
  have k : (t : ℝ) / 8000 * Real.exp (-((lt2x1 - 1 / 800) * N)) ≤ (t : ℝ) / 8000 * Pw w (tcRow w) :=
    mul_le_mul_of_nonneg_left hσN (by positivity)
  linarith

/-- **`φ_s(S) ≥ β/4` for a successful member, `N` large** (`t = 1/80`, bins `n_b = 8319999`, grid `n_g = 640000`,
box `ρ = 1/4160000`, window loss `ω' = 1/320000`; light statistic `≤ σ/640000`, band `η² ≤ σ a₃Z/(8·10^7)`). -/
theorem lt3W_TCprime_quarter :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (w : Param N) (s : State N) (ε γ : ℝ) (a b c : Fin N) (hab : a ≠ b)
      (hac : a ≠ c) (hbc : b ≠ c) (r0 : State N) (φH η E0 : ℝ), w ∈ openCube N →
      (({a, b, c} : Finset (Fin N)), r0) ∈ lt3WSel s ε γ 8319999 w → (lt2Sp w).card < 12 →
      lt3WSucc (1 / 80) (1 / 320000) (1 / 4160000) (pkE3 hab hac hbc) {a, b, c} w →
      (∀ (t0 : State N) (u : Fin (2 ^ 3)) (i : Fin 3),
        |lt3Light (stHalf (stPriv (lt3WSel s ε γ 8319999) lt3PB w) w) {a, b, c} (lt3H w)
            (pkFlip (pkE3 hab hac hbc) t0 u) (pkE3 hab hac hbc i) -
          lt3Light (stHalf (stPriv (lt3WSel s ε γ 8319999) lt3PB w) w) {a, b, c} (lt3H w) t0
            (pkE3 hab hac hbc i)| ≤ φH) →
      φH ≤ Pw w (tcRow w) / 640000 →
      Real.exp (-((lt2x1 - 1 / 800) * N)) ≤ Pw w (tcRow w) → 0 ≤ η →
      (∀ Y ⊆ ({a, b, c} : Finset (Fin N)), ∀ t', ∀ i ∈ ({a, b, c} : Finset (Fin N)),
        |Num w {a, b, c} Y t' i - lvK 3 * Zs w| ≤ η) →
      η ^ 2 ≤ Pw w (tcRow w) * (lvK 3 * Zs w) / (8 * 10 ^ 7) →
      6 * η / ((lvK 3 * Zs w - η) * Real.log 2) ≤ E0 →
      (∃ te ∈ sysMaxEffStates (tpmOf (flipP s w)) {a, b, c} s s,
        ∀ θ : SysPartition N {a, b, c}, E0 ≤ sysPhiE (tpmOf (flipP s w)) {a, b, c} s θ s te) →
      1 / 4 * betaW w ≤ phi (flipP s w) s {a, b, c} := by
  filter_upwards [lt3W_TCprime_ev (t := 1 / 80) (by norm_num) le_rfl] with N hN w s ε γ a b c hab hac hbc r0 φH η
    E0 hw hk hSp hsucc hHalf hφH hσN hη0 hlev hηs hE0 heff
  have hc : ((1 / 80 : ℚ) : ℝ) = 1 / 80 := by push_cast; ring
  obtain ⟨c0, hc0, -, hphi⟩ := hN w s ε γ 8319999 a b c hab hac hbc r0 640000 (1 / 320000) (1 / 4160000) φH η E0
    hw hk hSp (by norm_num) (by norm_num) (by push_cast; norm_num) (by rw [hc]; norm_num) (by norm_num)
    (by rw [hc]; norm_num) hsucc hHalf (by rw [hc]; linarith) hσN hη0 hlev (by rw [hc]; linarith) hE0 heff
  rw [hc] at hphi
  have hβ : 0 ≤ betaW w := div_nonneg (Pw_nonneg w _) (b1_Zs_pos hw).le
  have hlt := levTrip_gt
  have k1 : (577 / 1000 : ℝ) * (4 / 5) ≤ levTrip * c0 := mul_le_mul hlt.le hc0 (by norm_num) levTrip_pos.le
  have k2 : (1 : ℝ) / 4 ≤ levTrip * c0 * (1 - 483 * (1 / 80) / 800) := by nlinarith
  calc 1 / 4 * betaW w ≤ levTrip * c0 * (1 - 483 * (1 / 80) / 800) * betaW w :=
        mul_le_mul_of_nonneg_right k2 hβ
    _ ≤ phi (flipP s w) s {a, b, c} := hphi

/-! ### The success event under resampling of the private entries (input to T7) -/

/-- Every member of the family is a triple of distinct units. -/
lemma qFam_three {Q S : Finset (Fin N)} (hS : S ∈ qFam Q) :
    ∃ a b c : Fin N, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ S = {a, b, c} := by
  obtain ⟨p, -, rfl⟩ := mem_image.1 hS
  refine ⟨_, _, _, fun h => ?_, fun h => ?_, fun h => ?_, rfl⟩
  · exact Finset.disjoint_left.1 (qPart_disj Q (by decide : (0 : Fin 3) ≠ 1)) (orderEmbOfFin_mem _ _ _)
      (by rw [h]; exact orderEmbOfFin_mem _ _ _)
  · exact Finset.disjoint_left.1 (qPart_disj Q (by decide : (0 : Fin 3) ≠ 2)) (orderEmbOfFin_mem _ _ _)
      (by rw [h]; exact orderEmbOfFin_mem _ _ _)
  · exact Finset.disjoint_left.1 (qPart_disj Q (by decide : (1 : Fin 3) ≠ 2)) (orderEmbOfFin_mem _ _ _)
      (by rw [h]; exact orderEmbOfFin_mem _ _ _)

/-- Every member of the windowed selection is `({a, b, c}, r)` with distinct units. -/
lemma lt3WSel_three {s : State N} {ε γ : ℝ} {nb : ℕ} {w : Param N} {k : Finset (Fin N) × State N}
    (hk : k ∈ lt3WSel s ε γ nb w) : ∃ a b c : Fin N, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ k.1 = {a, b, c} := by
  classical
  obtain ⟨-, -, -, hF, -⟩ := lt3W_mem hk
  unfold lt3WF at hF
  exact qFam_three (mem_filter.1 hF).1

lemma lt3W_mem_base {s : State N} {ε γ : ℝ} {nb : ℕ} {w : Param N} {S : Finset (Fin N)} {r0 r : State N}
    (hk : (S, r0) ∈ lt3WSel s ε γ nb w) (hr : r ∈ lt3Base s w) : (S, r) ∈ lt3WSel s ε γ nb w := by
  classical
  unfold lt3WSel at hk ⊢
  split_ifs at hk ⊢ with hc
  · exact mem_product.2 ⟨(mem_product.1 hk).1, hr⟩
  · simp at hk

/-- **Success only reads the member's private entries**: resampling the private entries `A = Priv(w)` keeps `tc`,
the heavy set and the real data (they read safe entries only), so success at `replE A w η` is the box with the
targets of `w`, evaluated at `η`. -/
theorem lt3WSucc_replE {s : State N} {ε γ : ℝ} {nb : ℕ} {w : Param N} {a b c : Fin N} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) {r0 : State N} (hk : (({a, b, c} : Finset (Fin N)), r0) ∈ lt3WSel s ε γ nb w)
    (t : ℚ) (ω' ρ : ℝ) (η : Param N) :
    lt3WSucc t ω' ρ (pkE3 hab hac hbc) {a, b, c} (replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η) ↔
      η ∈ lt3Box (pkE3 hab hac hbc) {a, b, c} (tcRow w) (lt3H w)
        (lt3Tgt (lt3WData w (pkE3 hab hac hbc) {a, b, c})
          (lt3Tab (lt3WData w (pkE3 hab hac hbc) {a, b, c}) t ω').2.1) ρ := by
  classical
  obtain ⟨hP, -, -, -, -, hSWQ, -⟩ := lt3W_mem hk
  set e := pkE3 hab hac hbc with he
  have hS := pkE3_S hab hac hbc
  set S : Finset (Fin N) := {a, b, c} with hSdef
  set A := stPriv (lt3WSel s ε γ nb) lt3PB w with hA
  set w' := replE A w η with hw'
  have hSQ : S ⊆ lt3Q s ε γ w := hSWQ.trans (lt3WQ_sub s ε γ nb w)
  have hnA : ∀ q ∈ lt3WSafe s ε γ w, q ∉ A := fun q hq hqA => by
    obtain ⟨k, hk', hq'⟩ := mem_biUnion.1 hqA
    exact lt3WPB_not_safe w k hk' q hq' hq
  have hsafe : ∀ q ∈ lt3WSafe s ε γ w, w q.1 q.2 = w' q.1 q.2 := by
    rintro ⟨q1, q2⟩ hq
    show w q1 q2 = (if (q1, q2) ∈ A then η q1 q2 else w q1 q2)
    rw [if_neg (hnA _ hq)]
  have hC : ∀ q, ∀ j ∈ (lt3Top s w ε)ᶜ, w q j = w' q j := fun q j hj =>
    hsafe (q, j) (Or.inl (Or.inl (mem_compl.1 hj)))
  have hN : ∀ r, ¬ 3 / 10 * (N : ℝ) < XMW w (lt3Top s w ε)ᶜ r → ∀ j, w r j = w' r j := fun r hr j =>
    hsafe (r, j) (Or.inl (Or.inr (Or.inl hr)))
  have hs' : w' s = w s := funext fun j => (hsafe (s, j) (Or.inl (Or.inr (Or.inr rfl)))).symm
  obtain ⟨ht, -, hPt, -, hSp⟩ := lt3_frame_stable ε (le_trans lt2x1_bounds.2 (by norm_num)) hP hC hN hs'
  have hH : lt3H w' = lt3H w := by unfold lt3H; rw [ht, hSp]
  have hrow : ∀ r ∈ lt3H w, w' r = w r := by
    intro r hr
    have hnl : ¬ 3 / 10 * (N : ℝ) < XMW w (lt3Top s w ε)ᶜ r := by
      intro hl
      rcases mem_insert.1 hr with rfl | hsp
      · have := (st_Pw_le_exp _ w (tcRow w)).trans_lt
          (Real.exp_lt_exp.2 (by linarith : -XMW w (lt3Top s w ε)ᶜ (tcRow w) < -(3 / 10 * (N : ℝ))))
        linarith
      · have hx : XW w r ≤ lt2x1 * N := by
          simpa [lt2Sp] using hsp
        have h1 := XMW_le_XW w (lt3Top s w ε)ᶜ r
        have h2 := lt2x1_bounds
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith
    funext j
    exact (hN r hnl j).symm
  have hflip : ∀ r ∈ lt3H w, ∀ i : Fin 3, w' (flip r (e i)) (e i) = w (flip r (e i)) (e i) := fun r hr i =>
    (hsafe (flip r (e i), e i) (Or.inr ⟨hSQ ((hS _).2 ⟨i, rfl⟩), r, lt3H_sub_base s w hr, Or.inr rfl⟩)).symm
  have hPw : ∀ r ∈ lt3H w, Pw w' r = Pw w r := fun r hr => by unfold Pw; rw [hrow r hr]
  have hD : lt3WData w' e S = lt3WData w e S := by
    unfold lt3WData
    rw [hPt, ht, hH]
    unfold lt3RealData
    congr 1 <;> (try funext i) <;> refine sum_congr rfl fun r hr => ?_ <;>
      simp only [hPw r (mem_filter.1 hr).1, hrow r (mem_filter.1 hr).1, hflip r (mem_filter.1 hr).1]
  unfold lt3WSucc
  rw [ht, hH, hD]
  refine lt3Box_detOn hS (tcRow w) (lt3H w) _ ρ w' η ?_
  rintro ⟨q1, q2⟩ hq
  obtain ⟨r, hr, hq'⟩ := mem_biUnion.1 hq
  have hqA : (q1, q2) ∈ A := mem_biUnion.2 ⟨(S, r), lt3W_mem_base hk (lt3H_sub_base s w hr), hq'⟩
  show (if (q1, q2) ∈ A then η q1 q2 else w q1 q2) = η q1 q2
  rw [if_pos hqA]

/-- **The success event of a member, conditionally on `Priv`, is a measurable box** on the member's private entries
(`⋃_{r ∈ {tc} ∪ Sp} lt3PB (S, r)`) **of probability `≥ ρ^{18|H|} ≥ ρ^{234}`** (product of uniforms). -/
theorem lt3WSucc_prob {s : State N} {ε γ : ℝ} {nb : ℕ} {w : Param N} (hw : w ∈ openCube N) {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {r0 : State N}
    (hk : (({a, b, c} : Finset (Fin N)), r0) ∈ lt3WSel s ε γ nb w) (hSp : (lt2Sp w).card < 12)
    {ng : ℕ} (hng : 0 < ng) (h5 : 5 ∣ ng) {t : ℚ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 80) {ω' ρ : ℝ}
    (hω' : 13 * (1 / ((nb + 1 : ℕ) : ℝ)) + 1 / (ng : ℝ) ≤ ω') (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    {η | lt3WSucc t ω' ρ (pkE3 hab hac hbc) {a, b, c} (replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η)} =
        lt3Box (pkE3 hab hac hbc) {a, b, c} (tcRow w) (lt3H w)
          (lt3Tgt (lt3WData w (pkE3 hab hac hbc) {a, b, c})
            (lt3Tab (lt3WData w (pkE3 hab hac hbc) {a, b, c}) t ω').2.1) ρ ∧
      MeasurableSet
        {η | lt3WSucc t ω' ρ (pkE3 hab hac hbc) {a, b, c} (replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η)} ∧
      DetOnE ((lt3H w).biUnion fun r => lt3PB (({a, b, c} : Finset (Fin N)), r))
        {η | lt3WSucc t ω' ρ (pkE3 hab hac hbc) {a, b, c} (replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η)} ∧
      ENNReal.ofReal (ρ ^ 234) ≤
        cubeM N {η | lt3WSucc t ω' ρ (pkE3 hab hac hbc) {a, b, c}
          (replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η)} := by
  classical
  have heq : {η | lt3WSucc t ω' ρ (pkE3 hab hac hbc) {a, b, c}
      (replE (stPriv (lt3WSel s ε γ nb) lt3PB w) w η)} =
      lt3Box (pkE3 hab hac hbc) {a, b, c} (tcRow w) (lt3H w)
        (lt3Tgt (lt3WData w (pkE3 hab hac hbc) {a, b, c})
          (lt3Tab (lt3WData w (pkE3 hab hac hbc) {a, b, c}) t ω').2.1) ρ := by
    ext η; exact lt3WSucc_replE hab hac hbc hk t ω' ρ η
  have hS := pkE3_S hab hac hbc
  refine ⟨heq, by rw [heq]; exact lt3Box_mset _ _ _ _ _ _, by rw [heq]; exact lt3Box_detOn hS _ _ _ _, ?_⟩
  rw [heq]
  obtain ⟨-, h7, -, -, -, hSWQ, hag⟩ := lt3W_mem hk
  have hσ := b1_Pw_pos hw (tcRow w)
  have hp := lt3W_tab_spec hw hab hac hbc hk hSp hng h5 ht0 ht1 hω'
  obtain ⟨hG1n, hF1n, hG2n, hF2n, hG1V, hF1V, hG2V, hF2V, hV1n, hV2n, -⟩ :=
    lt3RD_bounds w (pkE3 hab hac hbc) {a, b, c} (tcRow w) (lt3H w) hσ (fun r => Pw_le_tcRow w r)
  have hlw := rlLoR_wd_bounds _ hG1n hF1n hG2n hF2n hG1V hF1V hG2V hF2V hV1n hV2n
  have hT := lt3Tgt_spec _ _ hp.2.2.2.2.1 (fun u i => (hlw u i).2.1)
  have hQ7 : 7 ≤ (lt3Q s ε γ w).card := h7.trans (card_le_card (lt3WQ_sub s ε γ nb w))
  have h := lt3Box_prob hS (hSWQ.trans (lt3WQ_sub s ε γ nb w)) hQ7
    (fun r hr => hag r (lt3H_sub_base s w hr)) (fun u i => (hT u i).2) hρ0 hρ1 (tc := tcRow w)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) h
  exact pow_le_pow_of_le_one hρ0 hρ1 (by have := lt3H_card hSp; omega)

end Census
end IIT
