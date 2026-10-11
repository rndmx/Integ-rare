/-
Census of complexes: definitions for the "regime X" forcing of B1 (the whole substrate is a
complex because U's minimum information partition sits in the family F_x — some neighbour
row of the top row, or of the current-state row, nearly copies it). See
`results/theory/iit-census/lean/B1-BLUEPRINT-v2.md` Section 5.1 for the informal specification
this file follows (write-ups W7, W9, W5, W3).

DEVIATIONS FROM THE BLUEPRINT (written by hand, single low-effort pass, time-boxed):
* `SingleNotFail`, `deltaU`, `D0U`, `hU`, `lamC/lamE/FC/FE/MsumC/MsumE` are meant to be shared with
  the not-yet-written `B1UnivMIP.lean`. Per the blueprint's own note, minimal placeholder
  definitions are given here so this file has no forward dependency; `B1UnivMIP` should import
  them from here once written, and may need to strengthen them.
* `cellsX` now reads the real 61-per-side certified data (`w7_certX_cause.json` /
  `w7_certX_effect.json` under `results/theory/b1cert/`), via the companion file
  `CertRatesDataX.lean`; `RegEvX` is therefore non-vacuous. The `lam`/`mult` fields of the JSON
  (used only to *certify* each cell's rate, not to *state* the event) are not carried over; only
  the `(mlo, cm)` pair each cell contributes to `CellEvX` is kept.
* Every field of `B1FGoodX` is copied close to the blueprint's literal text; several needed
  `Finset.sum`/`Finset.inf'` nonempty-witnesses spelled out, and are given explicitly.
* `b1CutMeanS`, `b1CutMeanPlus`, `b1CutGX` are new helpers (W5 §11 / W7 §4.3), modelled directly
  on `B1Defs.b1CutMean` / `b1CutG`, generalised to an arbitrary anchor row instead of always `tc`.
* Proofs of `B1FGoodX.congr`, `forcedX_restr`, the four `measurableSet_*`/`mem_famX_measurable`
  theorems are NOT attempted in this pass (time-boxed); they are left as clearly marked `sorry`s.
  Every definition above them typechecks and is `sorry`-free.
-/
import IIT.Census.B1Defs
import IIT.Census.B1Prod
import IIT.Census.B1NearUniv
import IIT.Census.CertRatesDataX

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- Which side of the current mechanism the regime-X neighbour row lives on: the cause side
(a neighbour of the top row `tcRow w`) or the effect side (a neighbour of the current-state
row `s`). -/
inductive XSide | cause | effect
  deriving DecidableEq

instance : Fintype XSide where
  elems := {XSide.cause, XSide.effect}
  complete := by intro x; cases x <;> simp

/-- The family size used by regime X: `⌈N/30⌉`. -/
def dX (N : ℕ) : ℕ := (N + 29) / 30

noncomputable def cCnt : ℝ := 1 / 500
noncomputable def RXf : ℝ := 1007 / 1000
noncomputable def Rcnt : ℝ := 1009 / 1000
noncomputable def RLBX : ℝ := 10085 / 10000
noncomputable def RbadX : ℝ := 101 / 100
noncomputable def cX : ℝ := 1 / 2 + 1 / 500

/-- The special (near-copying) row of the regime: `tcRow` flipped at `x` on the cause side,
`s` flipped at `x` on the effect side. -/
def spRow (s r0 : State N) (x : Fin N) : XSide → State N
  | .cause => flipAt x r0
  | .effect => flipAt x s

/-- The probability that row `r` sends unit `j` to the same value as the maximal effect state
`teW w s j`, i.e. the flipped-coordinates reading of row `r`'s column `j`. -/
noncomputable def pTe (w : Param N) (s r : State N) (j : Fin N) : ℝ :=
  if 1 / 2 < clamp01 (w s j) then clamp01 (w r j) else 1 - clamp01 (w r j)

/-- The "base" entries of the regime: the top row's own entries on the cause side, the current
row's flipped-coordinate entries (`xE`) on the effect side. -/
noncomputable def baseE (w : Param N) (s r0 : State N) (x : Fin N) : XSide → Fin N → ℝ
  | .cause, j => clamp01 (w r0 j)
  | .effect, j => xE w s j

/-- The "competitor" entries of the regime: the near-copying neighbour row's entries. -/
noncomputable def compE (w : Param N) (s r0 : State N) (x : Fin N) : XSide → Fin N → ℝ
  | .cause, j => clamp01 (w (flipAt x r0) j)
  | .effect, j => pTe w s (flipAt x s) j

/-- The per-unit log-ratio comparing the base entry to the competitor entry. -/
noncomputable def lamX (w : Param N) (s r0 : State N) (x : Fin N) (σ : XSide) (j : Fin N) : ℝ :=
  Real.log (2 * baseE w s r0 x σ j / (baseE w s r0 x σ j + compE w s r0 x σ j))

/-- The units where the neighbour row `tc^x` is at least `27/25` times heavier than `tc` itself
(excluding `x`): the family the cause-side count is drawn from. -/
noncomputable def NegX (w : Param N) (r0 : State N) (x : Fin N) : Finset (Fin N) :=
  (univ.erase x).filter fun j => 27 / 25 * clamp01 (w r0 j) ≤ clamp01 (w (flipAt x r0) j)

/-- The family of `d`-sets the counting argument runs over: `d`-subsets of `NegX` on the cause
side, all `d`-subsets on the effect side. -/
noncomputable def famX (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N) :
    Finset (Finset (Fin N)) :=
  match σ with
  | .cause => (NegX w r0 x).powersetCard (dX N)
  | .effect => (univ : Finset (Fin N)).powersetCard (dX N)

/-- Slack sequences of the regime event, `o(N)`. -/
noncomputable def slT (N : ℕ) : ℝ := 2 * Real.log N + 20

/-- `deltaU`: the half-mean deviation bound of `HalfMeanGood` (W3 §7.1's `δ_{N-1}`); any `o(1)` value
whose half-mean event has doubly exponentially small failure works, `1/(N+1)` is such a value. -/
noncomputable def deltaU (N : ℕ) : ℝ := 1 / (N + 1 : ℝ)

/-- `D0U = 5 log₂ N + C0` (blueprint §1, W3 §9.4), with `C0 = 20`.  Distinct from the count's
`D0C = 2 log₂ N + 14` (gap G9). -/
def D0U (N : ℕ) : ℕ := 5 * Nat.log 2 N + 20

/-- The V-sum slack of the regime event: `8·D0U + 20 ≥ 7·D0U·ln 2 +` the proxy error (gap G2(a)). -/
noncomputable def slV (N : ℕ) : ℝ := 8 * (D0U N : ℝ) + 20


/-!
### The regime-X cell table

`cellsX` is the 61-per-side table of rational cells certified in
`results/theory/b1cert/w7_certX_cause.json` / `w7_certX_effect.json` (imported via
`CertRatesDataX.cellsXCauseData` / `cellsXEffectData`), converted from a `List` to a `Finset`.
-/

/-- The certified cell table for the regime event, per side. -/
noncomputable def cellsX (σ : XSide) : Finset (ℚ × ℚ) :=
  match σ with
  | .cause => cellsXCauseData.toFinset
  | .effect => cellsXEffectData.toFinset

/-- The cell event: on cell `c = (mlo, cm)`, every base entry is at least `mlo`, some base entry
is at most `cm`, and the tilt/link/V-sum conditions of W7 §2.1 hold. -/
def CellEvX (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) (c : ℚ × ℚ) (w : Param N) : Prop :=
  (∀ j, (c.1 : ℝ) ≤ baseE w s r0 x σ j) ∧ (∃ j, baseE w s r0 x σ j ≤ (c.2 : ℝ)) ∧
    XW w r0 ≤ x0 * N + slT N ∧
    ∑ k, -Real.log (xE w s k) ≤ XW w r0 + slT N ∧
    ∑ j ∈ univ.erase x, min (lamX w s r0 x σ j)
        (max 0 (Real.log (baseE w s r0 x σ j / (c.2 : ℝ))) - 7 * deltaU N)
      ≤ slV N ∧
    (σ = .effect → ∀ j, 1 / 2 - deltaU N ≤ clamp01 (w r0 j))

/-- The regime event: some cell of `cellsX σ` is satisfied. -/
def RegEvX (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N) : Prop :=
  ∃ c ∈ cellsX σ, CellEvX N s r0 x σ c w

/-- Mean of column `i` over the `K'`-subcube through the anchor row `s0` (W5 A3 / W7 §4.4: the rows
around the current state `s`). The argument `t` is unused (kept for signature stability). -/
noncomputable def b1CutMeanS (w : Param N) (s0 t : State N) (K' : Finset (Fin N)) (i : Fin N) :
    ℝ :=
  (∑ r ∈ agree K'ᶜ s0, clamp01 (w r i)) / (2 : ℝ) ^ K'.card

/-- The `plus` variant used when the anchor row itself is excluded from the average and replaced
by the value `1` at the anchor (W5 §11's `colMeanPlus` idea, ported to a general row `t`). -/
noncomputable def b1CutMeanPlus (w : Param N) (t : State N) (K' : Finset (Fin N)) (i : Fin N) :
    ℝ :=
  (1 + ∑ r ∈ (agree K'ᶜ t).erase t, clamp01 (w r i)) / (2 : ℝ) ^ K'.card

/-- The regime-X truncated small-cut term, built from `b1CutMeanPlus`. -/
noncomputable def b1CutGX (w : Param N) (t : State N) (K' : Finset (Fin N)) (i : Fin N) : ℝ :=
  min (Real.log (clamp01 (w t i) / b1CutMeanPlus w t K' i)) (Real.log (clamp01 (w t i) / b1Cap))

/-! ### Copies of the shared `B1UnivMIP` definitions (see header note) -/

/-- Placeholder for `B1UnivMIP`'s cause-side single-unit-cut log-ratio at unit `x`
(minimal stand-in; `B1UnivMIP` should refine/replace this). -/
noncomputable def lamC (w : Param N) (r0 : State N) (x : Fin N) : ℝ :=
  Real.log (2 * clamp01 (w r0 x) / (clamp01 (w r0 x) + clamp01 (w (flipAt x r0) x)))

/-- Placeholder for `B1UnivMIP`'s effect-side single-unit-cut log-ratio at unit `x`. -/
noncomputable def lamE (w : Param N) (s : State N) (x : Fin N) : ℝ :=
  Real.log (2 * xE w s x / (xE w s x + pTe w s (flipAt x s) x))

/-- Placeholder cause-side full-cut sum used by `SingleNotFail`. -/
noncomputable def FC (w : Param N) (r0 : State N) (x : Fin N) : ℝ :=
  ∑ j ∈ univ.erase x, lamC w r0 j

/-- Placeholder effect-side full-cut sum used by `SingleNotFail`. -/
noncomputable def FE (w : Param N) (s : State N) (x : Fin N) : ℝ :=
  ∑ j ∈ univ.erase x, lamE w s j

/-- Placeholder `min`-form sum over a `K` of size `2..4` (cause side), used by `SingleNotFail`. -/
noncomputable def MsumC (w : Param N) (r0 : State N) (x : Fin N) (K : Finset (Fin N)) : ℝ :=
  ∑ j ∈ K.erase x, lamC w r0 j

/-- Placeholder `min`-form sum over a `K` of size `2..4` (effect side). -/
noncomputable def MsumE (w : Param N) (s : State N) (x : Fin N) (K : Finset (Fin N)) : ℝ :=
  ∑ j ∈ K.erase x, lamE w s j


/-- Placeholder nonempty witness needed by `phUMin`-style `inf'` calls below. -/
theorem hU : (univ : Finset (Fin N)).Nonempty ↔ 0 < N := by
  simp [Finset.univ_nonempty_iff, Fin.pos_iff_nonempty]

/-- `SingleNotFail w s r0 x'`: unit `x'` is not itself a failing (near-copy) unit, in the local
proxy form of W7 §4.4 ("Fail = {x}"): the regime event at `x'` holds on neither side. By the proxy
lemmas (`regEv_of_fail_cause/effect`), a failing `x'` (SmallCutGood violated at `x'`) forces
`RegEvX` at `x'`, so this field excludes a second failing unit; its failure jointly with the
regime event at `x` is W7's "two failing units" (rate ≥ 1.661931) or "both sides" event. -/
def SingleNotFail (w : Param N) (s r0 : State N) (x' : Fin N) : Prop :=
  ¬ RegEvX N s r0 x' .cause w ∧ ¬ RegEvX N s r0 x' .effect w

/-! ### The regime-X good-configuration structure -/

structure B1FGoodX (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N) : Prop where
  regEv : RegEvX N s r0 x σ w
  openRows : ∀ r ∈ sensRows s r0, ∀ i, w r i ∈ Set.Ioo (0 : ℝ) 1
  far : N ≤ 3 * ham r0 s
  ret : ∀ r ∈ sensRows s r0, r ≠ r0 → r ≠ spRow s r0 x .cause → ∀ K : Finset (Fin N),
      K.card ≤ dX N → XW w r0 + b1Eta * N < XMW w (univ \ K) r
  retR1 : σ = .cause → (N : ℝ) / 400 ≤
      ∑ j ∈ univ.erase x, Real.log (clamp01 (w r0 j) / clamp01 (w (flipAt x r0) j))
  rowExc : ∀ r ∈ sensRows s r0, r ≠ r0 → r ≠ s → r ≠ spRow s r0 x σ →
      ∑ i, pos (clamp01 (w r i) - b1Cap) ≤ (N : ℝ) / 5
  nuS : ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 2 →
      ∑ i, Real.log (max (2 * b1CutMeanS w s r0 K' i) 1) ≤ 23 / 50 * (N : ℝ)
  nuTc : σ = .effect → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 3 →
      ∑ i, Real.log (max (2 * b1CutMeanPlus w r0 K' i) 1) ≤ 23 / 50 * (N : ℝ)
  x5 : σ = .cause → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 3 → x ∉ K' →
      ∑ i, Real.log (max (2 * b1CutMeanPlus w (flipAt x r0) K' i) 1) ≤ 23 / 50 * (N : ℝ)
  posNear : ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 4 → (σ = .cause → K' ≠ {x}) →
      (N : ℝ) / 25 ≤ ∑ i, b1CutGX w r0 K' i
  x1 : σ = .cause → -((N : ℝ) / 2000) ≤
      ∑ j ∈ univ.erase x, min (lamX w s r0 x .cause j) (Real.log (clamp01 (w r0 j) / cX))
  x2 : σ = .cause → N ≤ 4 * (NegX w r0 x).card
  failOnly : ∀ x' : Fin N, x' ≠ x → SingleNotFail w s r0 x'
  sRowMu' : ∀ h : (univ : Finset (Fin N)).Nonempty,
      Real.exp ((N : ℝ) / 100) * sigN N ≤ univ.inf' h (fun k => xE w s k - 1 / 2)
  sRowE : (2 : ℝ) ^ (-(N : ℝ) / 2) ≤ eE w s
  sRowR : ∑ r ∈ (sensRows s r0).erase s, ∏ k, pTe w s r k ≤ sigN N

/-- The good-configuration set on the sensitive-row projection. -/
def GoodFX (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) : Set (sensRows s r0 → Fin N → ℝ) :=
  {f | B1FGoodX N s r0 x σ (b1Ext f)}

/-- The forced event: the whole substrate is well-formed and some regime-X window is good. -/
structure ForcedX (N : ℕ) (s : State N) (w : Param N) : Prop where
  mem_open : w ∈ openCube N
  zs : 1 / 2 ≤ Zs w ∧ Zs w ≤ b1ZMax
  regime : ∃ x σ, B1FGoodX N s (tcRow w) x σ w

/-! ### Congruence and measurability (TODO, time-boxed: left as `sorry`) -/

/-! ### Hamming-distance and subcube lemmas feeding `B1FGoodX.congr` -/

theorem ham_triangle {N : ℕ} (r r' r'' : State N) : ham r r'' ≤ ham r r' + ham r' r'' := by
  unfold ham
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases eq_or_ne (r j) (r' j) with h1 | h1
  · exact Or.inr (h1 ▸ hj)
  · exact Or.inl h1

theorem ham_comm {N : ℕ} (r r' : State N) : ham r r' = ham r' r := by
  unfold ham; congr 1; ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ne_comm

theorem ham_flipAt_le_one {N : ℕ} (x : Fin N) (r : State N) : ham (flipAt x r) r ≤ 1 := by
  unfold ham flipAt
  refine le_trans (Finset.card_le_card ?_) (Finset.card_singleton x).le
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  simp only [Finset.mem_singleton]
  by_contra hne
  exact hj (Function.update_of_ne hne _ _)

theorem ham_le_card_of_mem_agree {N : ℕ} {K : Finset (Fin N)} {t r : State N}
    (hr : r ∈ agree Kᶜ t) : ham r t ≤ K.card := by
  rw [mem_agree] at hr
  unfold ham
  refine Finset.card_le_card fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  by_contra hjK
  exact hj (hr j (by simpa using hjK))

theorem agree_subset_ballR {N : ℕ} {K : Finset (Fin N)} {t r0 : State N} {d ρ : ℕ}
    (hdist : ham t r0 ≤ d) (hcard : K.card ≤ ρ - d) (hd : d ≤ ρ) :
    agree Kᶜ t ⊆ ballR r0 ρ := by
  intro r hr
  simp only [ballR, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [ham_comm]
  calc ham r r0 ≤ ham r t + ham t r0 := ham_triangle r t r0
    _ ≤ K.card + d := Nat.add_le_add (ham_le_card_of_mem_agree hr) hdist
    _ ≤ (ρ - d) + d := Nat.add_le_add hcard le_rfl
    _ = ρ := Nat.sub_add_cancel hd

theorem agree_subset_sensRows_of_r0 {N : ℕ} {s r0 : State N} {K : Finset (Fin N)}
    (hcard : K.card ≤ 4) : agree Kᶜ r0 ⊆ sensRows s r0 := by
  refine Finset.Subset.trans ?_ Finset.subset_union_left
  exact agree_subset_ballR (d := 0) (ham_self r0).le (by simpa using hcard) (by norm_num)

theorem agree_subset_sensRows_of_flip {N : ℕ} {s r0 : State N} {x : Fin N} {K : Finset (Fin N)}
    (hcard : K.card ≤ 3) : agree Kᶜ (flipAt x r0) ⊆ sensRows s r0 := by
  refine Finset.Subset.trans ?_ Finset.subset_union_left
  refine agree_subset_ballR (d := 1) (ham_flipAt_le_one x r0) (by omega) (by norm_num)

theorem agree_subset_sensRows_of_s {N : ℕ} {s r0 : State N} {K : Finset (Fin N)}
    (hcard : K.card ≤ 2) : agree Kᶜ s ⊆ sensRows s r0 := by
  refine Finset.Subset.trans ?_ Finset.subset_union_right
  exact agree_subset_ballR (d := 0) (ham_self s).le (by simpa using hcard) (by norm_num)

/-! ### Congruence of the building-block functions -/

theorem XW_congr {N : ℕ} {w w' : Param N} {r : State N} (h : w' r = w r) :
    XW w' r = XW w r := by unfold XW; rw [h]

theorem XMW_congr {N : ℕ} {w w' : Param N} {M : Finset (Fin N)} {r : State N} (h : w' r = w r) :
    XMW w' M r = XMW w M r := by unfold XMW; rw [h]

theorem xE_congr {N : ℕ} {w w' : Param N} {s : State N} (h : w' s = w s) (k : Fin N) :
    xE w' s k = xE w s k := by unfold xE; rw [h]

theorem eE_congr {N : ℕ} {w w' : Param N} {s : State N} (h : w' s = w s) :
    eE w' s = eE w s := by unfold eE; exact Finset.prod_congr rfl fun k _ => xE_congr h k

theorem pTe_congr {N : ℕ} {w w' : Param N} {s r : State N} (hs : w' s = w s) (hr : w' r = w r)
    (j : Fin N) : pTe w' s r j = pTe w s r j := by unfold pTe; rw [hs, hr]

theorem NegX_congr {N : ℕ} {w w' : Param N} {r0 : State N} {x : Fin N}
    (h0 : w' r0 = w r0) (h1 : w' (flipAt x r0) = w (flipAt x r0)) :
    NegX w' r0 x = NegX w r0 x := by
  unfold NegX; rw [h0, h1]

theorem baseE_congr {N : ℕ} {w w' : Param N} {s r0 : State N} {x : Fin N} {σ : XSide}
    (hr0 : w' r0 = w r0) (hs : w' s = w s) (j : Fin N) :
    baseE w' s r0 x σ j = baseE w s r0 x σ j := by
  cases σ <;> simp only [baseE] <;> [rw [hr0]; exact xE_congr hs j]

theorem compE_congr {N : ℕ} {w w' : Param N} {s r0 : State N} {x : Fin N} {σ : XSide}
    (hf0 : w' (flipAt x r0) = w (flipAt x r0)) (hs : w' s = w s)
    (hfs : w' (flipAt x s) = w (flipAt x s)) (j : Fin N) :
    compE w' s r0 x σ j = compE w s r0 x σ j := by
  cases σ <;> simp only [compE] <;> [rw [hf0]; exact pTe_congr hs hfs j]

theorem lamX_congr {N : ℕ} {w w' : Param N} {s r0 : State N} {x : Fin N} {σ : XSide}
    (hr0 : w' r0 = w r0) (hf0 : w' (flipAt x r0) = w (flipAt x r0)) (hs : w' s = w s)
    (hfs : w' (flipAt x s) = w (flipAt x s)) (j : Fin N) :
    lamX w' s r0 x σ j = lamX w s r0 x σ j := by
  unfold lamX; rw [baseE_congr hr0 hs j, compE_congr hf0 hs hfs j]

theorem b1CutMeanS_congr {N : ℕ} {w w' : Param N} {s0 t : State N} {K' : Finset (Fin N)}
    (h : ∀ r ∈ agree K'ᶜ s0, w' r = w r) (i : Fin N) :
    b1CutMeanS w' s0 t K' i = b1CutMeanS w s0 t K' i := by
  unfold b1CutMeanS
  refine congrArg (· / _) (Finset.sum_congr rfl fun r hr => ?_)
  rw [h r hr]

theorem b1CutMeanPlus_congr {N : ℕ} {w w' : Param N} {t : State N} {K' : Finset (Fin N)}
    (h : ∀ r ∈ agree K'ᶜ t, w' r = w r) (i : Fin N) :
    b1CutMeanPlus w' t K' i = b1CutMeanPlus w t K' i := by
  unfold b1CutMeanPlus
  refine congrArg (fun v => (1 + v) / _) (Finset.sum_congr rfl fun r hr => ?_)
  rw [h r (Finset.mem_of_mem_erase hr)]

theorem b1CutGX_congr {N : ℕ} {w w' : Param N} {t : State N} {K' : Finset (Fin N)}
    (h : ∀ r ∈ agree K'ᶜ t, w' r = w r) (i : Fin N) :
    b1CutGX w' t K' i = b1CutGX w t K' i := by
  unfold b1CutGX
  rw [h t (self_mem_agree _ _), b1CutMeanPlus_congr h i]

theorem lamC_congr {N : ℕ} {w w' : Param N} {r0 : State N} {x : Fin N}
    (h0 : w' r0 = w r0) (hf : w' (flipAt x r0) = w (flipAt x r0)) :
    lamC w' r0 x = lamC w r0 x := by unfold lamC; rw [h0, hf]

theorem lamE_congr {N : ℕ} {w w' : Param N} {s : State N} {x : Fin N}
    (hs : w' s = w s) (hf : w' (flipAt x s) = w (flipAt x s)) :
    lamE w' s x = lamE w s x := by unfold lamE; rw [xE_congr hs x, pTe_congr hs hf x]

theorem CellEvX_congr {N : ℕ} {w w' : Param N} {s r0 : State N} {x : Fin N} {σ : XSide}
    (hr0 : w' r0 = w r0) (hf0 : w' (flipAt x r0) = w (flipAt x r0)) (hs : w' s = w s)
    (hfs : w' (flipAt x s) = w (flipAt x s)) (c : ℚ × ℚ) :
    CellEvX N s r0 x σ c w' ↔ CellEvX N s r0 x σ c w := by
  unfold CellEvX
  have hV : ∑ j ∈ univ.erase x, min (lamX w' s r0 x σ j)
        (max 0 (Real.log (baseE w' s r0 x σ j / (c.2 : ℝ))) - 7 * deltaU N)
      = ∑ j ∈ univ.erase x, min (lamX w s r0 x σ j)
        (max 0 (Real.log (baseE w s r0 x σ j / (c.2 : ℝ))) - 7 * deltaU N) :=
    Finset.sum_congr rfl fun j _ => by
      rw [lamX_congr hr0 hf0 hs hfs j, baseE_congr hr0 hs j]
  rw [XW_congr hr0, hV,
    show (∑ k, -Real.log (xE w' s k)) = ∑ k, -Real.log (xE w s k) from
      Finset.sum_congr rfl fun k _ => by rw [xE_congr hs k],
    show (∀ j, (c.1 : ℝ) ≤ baseE w' s r0 x σ j) ↔ (∀ j, (c.1 : ℝ) ≤ baseE w s r0 x σ j) from
      forall_congr' fun j => by rw [baseE_congr hr0 hs j],
    show (∃ j, baseE w' s r0 x σ j ≤ (c.2 : ℝ)) ↔ (∃ j, baseE w s r0 x σ j ≤ (c.2 : ℝ)) from
      exists_congr fun j => by rw [baseE_congr hr0 hs j]]
  simp only [hr0]

theorem RegEvX_congr {N : ℕ} {w w' : Param N} {s r0 : State N} {x : Fin N} {σ : XSide}
    (hr0 : w' r0 = w r0) (hf0 : w' (flipAt x r0) = w (flipAt x r0)) (hs : w' s = w s)
    (hfs : w' (flipAt x s) = w (flipAt x s)) :
    RegEvX N s r0 x σ w' ↔ RegEvX N s r0 x σ w := by
  unfold RegEvX
  exact exists_congr fun c => and_congr_right fun _ => CellEvX_congr hr0 hf0 hs hfs c

theorem SingleNotFail_congr {N : ℕ} {w w' : Param N} {s r0 : State N} {x' : Fin N}
    (h0 : w' r0 = w r0) (hf0 : w' (flipAt x' r0) = w (flipAt x' r0)) (hs : w' s = w s)
    (hfs : w' (flipAt x' s) = w (flipAt x' s)) :
    SingleNotFail w' s r0 x' ↔ SingleNotFail w s r0 x' := by
  unfold SingleNotFail; rw [RegEvX_congr h0 hf0 hs hfs, RegEvX_congr h0 hf0 hs hfs]

theorem B1FGoodX.congr {N : ℕ} {s r0 : State N} {x : Fin N} {σ : XSide} {w w' : Param N}
    (h : ∀ r ∈ sensRows s r0, w' r = w r) : B1FGoodX N s r0 x σ w ↔ B1FGoodX N s r0 x σ w' := by
  have hr0 : w' r0 = w r0 :=
    h r0 (Finset.mem_union_left _ (by simp [ballR, ham_self]))
  have hf0 : w' (flipAt x r0) = w (flipAt x r0) := by
    refine h _ (Finset.mem_union_left _ ?_)
    simp only [ballR, Finset.mem_filter, Finset.mem_univ, true_and]
    have := ham_flipAt_le_one x r0; rw [ham_comm] at this; omega
  have hs : w' s = w s := h s (Finset.mem_union_right _ (by simp [ballR, ham_self]))
  have hfs : w' (flipAt x s) = w (flipAt x s) := by
    refine h _ (Finset.mem_union_right _ ?_)
    simp only [ballR, Finset.mem_filter, Finset.mem_univ, true_and]
    have := ham_flipAt_le_one x s; rw [ham_comm] at this; omega
  have hOpen : (∀ r ∈ sensRows s r0, ∀ i, w' r i ∈ Set.Ioo (0 : ℝ) 1) ↔
      (∀ r ∈ sensRows s r0, ∀ i, w r i ∈ Set.Ioo (0 : ℝ) 1) :=
    forall₂_congr fun r hr => by rw [h r hr]
  have hRet : (∀ r ∈ sensRows s r0, r ≠ r0 → r ≠ spRow s r0 x .cause → ∀ K : Finset (Fin N),
        K.card ≤ dX N → XW w' r0 + b1Eta * N < XMW w' (univ \ K) r) ↔
      (∀ r ∈ sensRows s r0, r ≠ r0 → r ≠ spRow s r0 x .cause → ∀ K : Finset (Fin N),
        K.card ≤ dX N → XW w r0 + b1Eta * N < XMW w (univ \ K) r) := by
    refine forall₂_congr fun r hr => forall_congr' fun _ => forall_congr' fun _ =>
      forall_congr' fun K => forall_congr' fun _ => ?_
    rw [XW_congr hr0, XMW_congr (h r hr)]
  have hRowExc : (∀ r ∈ sensRows s r0, r ≠ r0 → r ≠ s → r ≠ spRow s r0 x σ →
        ∑ i, pos (clamp01 (w' r i) - b1Cap) ≤ (N : ℝ) / 5) ↔
      (∀ r ∈ sensRows s r0, r ≠ r0 → r ≠ s → r ≠ spRow s r0 x σ →
        ∑ i, pos (clamp01 (w r i) - b1Cap) ≤ (N : ℝ) / 5) := by
    refine forall₂_congr fun r hr => forall_congr' fun _ => forall_congr' fun _ =>
      forall_congr' fun _ => ?_
    rw [h r hr]
  have hNuS : (∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 2 →
        ∑ i, Real.log (max (2 * b1CutMeanS w' s r0 K' i) 1) ≤ 23 / 50 * (N : ℝ)) ↔
      (∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 2 →
        ∑ i, Real.log (max (2 * b1CutMeanS w s r0 K' i) 1) ≤ 23 / 50 * (N : ℝ)) := by
    refine forall_congr' fun K' => forall_congr' fun _ => forall_congr' fun hK' => ?_
    have hsub : agree K'ᶜ s ⊆ sensRows s r0 := agree_subset_sensRows_of_s hK'
    have : ∀ i, b1CutMeanS w' s r0 K' i = b1CutMeanS w s r0 K' i :=
      fun i => b1CutMeanS_congr (fun r hr => h r (hsub hr)) i
    simp only [this]
  have hNuTc : (σ = .effect → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 3 →
        ∑ i, Real.log (max (2 * b1CutMeanPlus w' r0 K' i) 1) ≤ 23 / 50 * (N : ℝ)) ↔
      (σ = .effect → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 3 →
        ∑ i, Real.log (max (2 * b1CutMeanPlus w r0 K' i) 1) ≤ 23 / 50 * (N : ℝ)) := by
    refine forall_congr' fun _ => forall_congr' fun K' => forall_congr' fun _ =>
      forall_congr' fun hK' => ?_
    have hsub : agree K'ᶜ r0 ⊆ sensRows s r0 := agree_subset_sensRows_of_r0 (hK'.trans (by norm_num))
    have : ∀ i, b1CutMeanPlus w' r0 K' i = b1CutMeanPlus w r0 K' i :=
      fun i => b1CutMeanPlus_congr (fun r hr => h r (hsub hr)) i
    simp only [this]
  have hX5 : (σ = .cause → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 3 → x ∉ K' →
        ∑ i, Real.log (max (2 * b1CutMeanPlus w' (flipAt x r0) K' i) 1) ≤ 23 / 50 * (N : ℝ)) ↔
      (σ = .cause → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 3 → x ∉ K' →
        ∑ i, Real.log (max (2 * b1CutMeanPlus w (flipAt x r0) K' i) 1) ≤ 23 / 50 * (N : ℝ)) := by
    refine forall_congr' fun _ => forall_congr' fun K' => forall_congr' fun _ =>
      forall_congr' fun hK' => forall_congr' fun _ => ?_
    have hsub : agree K'ᶜ (flipAt x r0) ⊆ sensRows s r0 := agree_subset_sensRows_of_flip hK'
    have : ∀ i, b1CutMeanPlus w' (flipAt x r0) K' i = b1CutMeanPlus w (flipAt x r0) K' i :=
      fun i => b1CutMeanPlus_congr (fun r hr => h r (hsub hr)) i
    simp only [this]
  have hPosNear : (∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 4 → (σ = .cause → K' ≠ {x}) →
        (N : ℝ) / 25 ≤ ∑ i, b1CutGX w' r0 K' i) ↔
      (∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 4 → (σ = .cause → K' ≠ {x}) →
        (N : ℝ) / 25 ≤ ∑ i, b1CutGX w r0 K' i) := by
    refine forall_congr' fun K' => forall_congr' fun _ => forall_congr' fun hK' =>
      forall_congr' fun _ => ?_
    have hsub : agree K'ᶜ r0 ⊆ sensRows s r0 := agree_subset_sensRows_of_r0 hK'
    have : ∀ i, b1CutGX w' r0 K' i = b1CutGX w r0 K' i :=
      fun i => b1CutGX_congr (fun r hr => h r (hsub hr)) i
    simp only [this]
  have hX1 : (σ = .cause → -((N : ℝ) / 2000) ≤
        ∑ j ∈ univ.erase x, min (lamX w' s r0 x .cause j)
          (Real.log (clamp01 (w' r0 j) / cX))) ↔
      (σ = .cause → -((N : ℝ) / 2000) ≤
        ∑ j ∈ univ.erase x, min (lamX w s r0 x .cause j)
          (Real.log (clamp01 (w r0 j) / cX))) := by
    refine forall_congr' fun _ => ?_
    have heq : (∑ j ∈ univ.erase x, min (lamX w' s r0 x .cause j)
          (Real.log (clamp01 (w' r0 j) / cX))) =
        ∑ j ∈ univ.erase x, min (lamX w s r0 x .cause j)
          (Real.log (clamp01 (w r0 j) / cX)) :=
      Finset.sum_congr rfl fun j _ => by
        rw [lamX_congr hr0 hf0 hs hfs j, hr0]
    rw [heq]
  have hX2 : (σ = .cause → N ≤ 4 * (NegX w' r0 x).card) ↔
      (σ = .cause → N ≤ 4 * (NegX w r0 x).card) := by
    refine forall_congr' fun _ => ?_
    rw [NegX_congr hr0 hf0]
  have hFailOnly : (∀ x' : Fin N, x' ≠ x → SingleNotFail w' s r0 x') ↔
      (∀ x' : Fin N, x' ≠ x → SingleNotFail w s r0 x') := by
    refine forall_congr' fun x' => forall_congr' fun _ => ?_
    have h0' : w' r0 = w r0 := hr0
    have hf' : w' (flipAt x' r0) = w (flipAt x' r0) :=
      h _ (Finset.mem_union_left _ (by
        simp only [ballR, Finset.mem_filter, Finset.mem_univ, true_and]
        have := ham_flipAt_le_one x' r0; rw [ham_comm] at this; omega))
    have hs' : w' s = w s := hs
    have hfs' : w' (flipAt x' s) = w (flipAt x' s) :=
      h _ (Finset.mem_union_right _ (by
        simp only [ballR, Finset.mem_filter, Finset.mem_univ, true_and]
        have := ham_flipAt_le_one x' s; rw [ham_comm] at this; omega))
    exact SingleNotFail_congr h0' hf' hs' hfs'
  have hSRowMu : (∀ hne : (univ : Finset (Fin N)).Nonempty,
        Real.exp ((N : ℝ) / 100) * sigN N ≤ univ.inf' hne (fun k => xE w' s k - 1 / 2)) ↔
      (∀ hne : (univ : Finset (Fin N)).Nonempty,
        Real.exp ((N : ℝ) / 100) * sigN N ≤ univ.inf' hne (fun k => xE w s k - 1 / 2)) := by
    refine forall_congr' fun hne => ?_
    rw [show (fun k => xE w' s k - 1 / 2) = (fun k => xE w s k - 1 / 2) from
      funext fun k => by rw [xE_congr hs k]]
  have hSRowE : (2 : ℝ) ^ (-(N : ℝ) / 2) ≤ eE w' s ↔ (2 : ℝ) ^ (-(N : ℝ) / 2) ≤ eE w s := by
    rw [eE_congr hs]
  have hSRowR : (∑ r ∈ (sensRows s r0).erase s, ∏ k, pTe w' s r k ≤ sigN N) ↔
      (∑ r ∈ (sensRows s r0).erase s, ∏ k, pTe w s r k ≤ sigN N) := by
    have heq : (∑ r ∈ (sensRows s r0).erase s, ∏ k, pTe w' s r k) =
        ∑ r ∈ (sensRows s r0).erase s, ∏ k, pTe w s r k :=
      Finset.sum_congr rfl fun r hr => Finset.prod_congr rfl fun k _ =>
        pTe_congr hs (h r (Finset.mem_of_mem_erase hr)) k
    rw [heq]
  constructor
  · intro hg
    exact
      { regEv := (RegEvX_congr hr0 hf0 hs hfs).2 hg.regEv
        openRows := hOpen.2 hg.openRows
        far := hg.far
        ret := hRet.2 hg.ret
        retR1 := fun hc => by
          have heq : (∑ j ∈ univ.erase x,
                Real.log (clamp01 (w' r0 j) / clamp01 (w' (flipAt x r0) j))) =
              ∑ j ∈ univ.erase x, Real.log (clamp01 (w r0 j) / clamp01 (w (flipAt x r0) j)) :=
            Finset.sum_congr rfl fun j _ => by rw [hr0, hf0]
          rw [heq]; exact hg.retR1 hc
        rowExc := hRowExc.2 hg.rowExc
        nuS := hNuS.2 hg.nuS
        nuTc := hNuTc.2 hg.nuTc
        x5 := hX5.2 hg.x5
        posNear := hPosNear.2 hg.posNear
        x1 := hX1.2 hg.x1
        x2 := hX2.2 hg.x2
        failOnly := hFailOnly.2 hg.failOnly
        sRowMu' := hSRowMu.2 hg.sRowMu'
        sRowE := hSRowE.2 hg.sRowE
        sRowR := hSRowR.2 hg.sRowR }
  · intro hg
    exact
      { regEv := (RegEvX_congr hr0 hf0 hs hfs).1 hg.regEv
        openRows := hOpen.1 hg.openRows
        far := hg.far
        ret := hRet.1 hg.ret
        retR1 := fun hc => by
          have heq : (∑ j ∈ univ.erase x,
                Real.log (clamp01 (w r0 j) / clamp01 (w (flipAt x r0) j))) =
              ∑ j ∈ univ.erase x,
                Real.log (clamp01 (w' r0 j) / clamp01 (w' (flipAt x r0) j)) :=
            Finset.sum_congr rfl fun j _ => by rw [hr0, hf0]
          rw [heq]; exact hg.retR1 hc
        rowExc := hRowExc.1 hg.rowExc
        nuS := hNuS.1 hg.nuS
        nuTc := hNuTc.1 hg.nuTc
        x5 := hX5.1 hg.x5
        posNear := hPosNear.1 hg.posNear
        x1 := hX1.1 hg.x1
        x2 := hX2.1 hg.x2
        failOnly := hFailOnly.1 hg.failOnly
        sRowMu' := hSRowMu.1 hg.sRowMu'
        sRowE := hSRowE.1 hg.sRowE
        sRowR := hSRowR.1 hg.sRowR }

theorem forcedX_restr {N : ℕ} {s : State N} {w : Param N} (h : ForcedX N s w) :
    ∃ x σ, restrIn (sensRows s (tcRow w)) w ∈ GoodFX N s (tcRow w) x σ := by
  obtain ⟨x, σ, hg⟩ := h.regime
  refine ⟨x, σ, ?_⟩
  show B1FGoodX N s (tcRow w) x σ (b1Ext (restrIn (sensRows s (tcRow w)) w))
  rw [← b1Restr_eq_restrIn]
  exact (B1FGoodX.congr (b1_Ext_Restr s (tcRow w) w)).1 hg

/-! ### Measurability of the building-block functions on `Param N` -/

lemma b1mx_pTe (s r : State N) (j : Fin N) : Measurable fun w : Param N => pTe w s r j := by
  unfold pTe
  exact Measurable.ite (measurableSet_lt measurable_const (b1m_clamp s j)) (b1m_clamp r j)
    ((b1m_clamp r j).const_sub 1)

lemma b1mx_baseE (s r0 : State N) (x : Fin N) (σ : XSide) (j : Fin N) :
    Measurable fun w : Param N => baseE w s r0 x σ j := by
  cases σ
  · exact b1m_clamp r0 j
  · exact b1m_xE s j

lemma b1mx_compE (s r0 : State N) (x : Fin N) (σ : XSide) (j : Fin N) :
    Measurable fun w : Param N => compE w s r0 x σ j := by
  cases σ
  · exact b1m_clamp (flipAt x r0) j
  · exact b1mx_pTe s (flipAt x s) j

lemma b1mx_lamX (s r0 : State N) (x : Fin N) (σ : XSide) (j : Fin N) :
    Measurable fun w : Param N => lamX w s r0 x σ j := by
  unfold lamX
  exact ((measurable_const.mul (b1mx_baseE s r0 x σ j)).div
    ((b1mx_baseE s r0 x σ j).add (b1mx_compE s r0 x σ j))).log

lemma b1mx_CutMeanS (s0 t : State N) (K' : Finset (Fin N)) (i : Fin N) :
    Measurable fun w : Param N => b1CutMeanS w s0 t K' i :=
  (Finset.measurable_sum _ fun r _ => b1m_clamp r i).div_const _

lemma b1mx_CutMeanPlus (t : State N) (K' : Finset (Fin N)) (i : Fin N) :
    Measurable fun w : Param N => b1CutMeanPlus w t K' i :=
  ((Finset.measurable_sum _ fun r _ => b1m_clamp r i).const_add 1).div_const _

lemma b1mx_CutGX (t : State N) (K' : Finset (Fin N)) (i : Fin N) :
    Measurable fun w : Param N => b1CutGX w t K' i :=
  ((b1m_clamp t i).div (b1mx_CutMeanPlus t K' i)).log.min ((b1m_clamp t i).div_const b1Cap).log

lemma b1mx_lamC (r0 : State N) (x : Fin N) : Measurable fun w : Param N => lamC w r0 x := by
  unfold lamC
  exact ((measurable_const.mul (b1m_clamp r0 x)).div
    ((b1m_clamp r0 x).add (b1m_clamp (flipAt x r0) x))).log

lemma b1mx_lamE (s : State N) (x : Fin N) : Measurable fun w : Param N => lamE w s x := by
  unfold lamE
  exact ((measurable_const.mul (b1m_xE s x)).div
    ((b1m_xE s x).add (b1mx_pTe s (flipAt x s) x))).log

lemma b1mx_measurableSet_mem_NegX (r0 : State N) (x : Fin N) (j : Fin N) :
    MeasurableSet {w : Param N | j ∈ NegX w r0 x} := by
  unfold NegX
  by_cases hjx : j = x
  · subst hjx; simpa using MeasurableSet.empty
  · have heq : {w : Param N | j ∈ (univ.erase x).filter
        (fun k => 27 / 25 * clamp01 (w r0 k) ≤ clamp01 (w (flipAt x r0) k))} =
        {w : Param N | 27 / 25 * clamp01 (w r0 j) ≤ clamp01 (w (flipAt x r0) j)} := by
      ext w; simp [Finset.mem_filter, hjx]
    rw [heq]
    exact measurableSet_le (measurable_const.mul (b1m_clamp r0 j)) (b1m_clamp (flipAt x r0) j)

lemma b1mx_measurableSet_NegX_eq (r0 : State N) (x : Fin N) (A : Finset (Fin N)) :
    MeasurableSet {w : Param N | NegX w r0 x = A} := by
  have h : {w : Param N | NegX w r0 x = A} = ⋂ j, {w | (j ∈ NegX w r0 x ↔ j ∈ A)} := by
    ext w; simp [Finset.ext_iff]
  rw [h]
  refine MeasurableSet.iInter fun j => ?_
  by_cases hj : j ∈ A
  · convert b1mx_measurableSet_mem_NegX r0 x j using 1; ext w; simp [hj]
  · convert (b1mx_measurableSet_mem_NegX r0 x j).compl using 1; ext w; simp [hj]

lemma b1mx_measurableSet_NegX_card_ge (r0 : State N) (x : Fin N) (k : ℕ) :
    MeasurableSet {w : Param N | k ≤ (NegX w r0 x).card} := by
  have h : {w : Param N | k ≤ (NegX w r0 x).card} =
      ⋃ A : Finset (Fin N), (if k ≤ A.card then {w | NegX w r0 x = A} else ∅) := by
    ext w
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro hx; refine ⟨NegX w r0 x, ?_⟩; rw [if_pos hx]; rfl
    · rintro ⟨A, hA⟩
      split_ifs at hA with hk
      · show k ≤ (NegX w r0 x).card; rw [hA]; exact hk
      · exact absurd hA (Set.notMem_empty w)
  rw [h]
  refine MeasurableSet.iUnion fun A => ?_
  split_ifs
  · exact b1mx_measurableSet_NegX_eq r0 x A
  · exact MeasurableSet.empty

lemma b1mx_CellEvX (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) (c : ℚ × ℚ) :
    MeasurableSet {w : Param N | CellEvX N s r0 x σ c w} := by
  unfold CellEvX
  refine b1_mset_and (b1_mset_forall fun j =>
    measurableSet_le measurable_const (b1mx_baseE s r0 x σ j)) (b1_mset_and
    (b1_mset_exists fun j => measurableSet_le (b1mx_baseE s r0 x σ j) measurable_const)
    (b1_mset_and (measurableSet_le (b1m_XW r0) measurable_const) (b1_mset_and
      (measurableSet_le (Finset.measurable_sum _ fun k _ => (b1m_xE s k).log.neg)
        ((b1m_XW r0).add_const _))
      (b1_mset_and (measurableSet_le (Finset.measurable_sum _ fun j _ =>
          (b1mx_lamX s r0 x σ j).min ((measurable_const.max
            ((b1mx_baseE s r0 x σ j).div_const _).log).sub_const _))
        measurable_const)
        (b1_mset_imp (MeasurableSet.const _) (b1_mset_forall fun j =>
          measurableSet_le measurable_const (b1m_clamp r0 j)))))))

lemma b1mx_RegEvX (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) :
    MeasurableSet {w : Param N | RegEvX N s r0 x σ w} := by
  unfold RegEvX
  have h : {w : Param N | ∃ c ∈ cellsX σ, CellEvX N s r0 x σ c w} =
      ⋃ c ∈ cellsX σ, {w : Param N | CellEvX N s r0 x σ c w} := by
    ext w; simp
  rw [h]
  exact MeasurableSet.biUnion (cellsX σ).countable_toSet fun c _ => b1mx_CellEvX N s r0 x σ c

lemma b1mx_SingleNotFail (s r0 : State N) (x' : Fin N) :
    MeasurableSet {w : Param N | SingleNotFail w s r0 x'} := by
  unfold SingleNotFail
  exact b1_mset_and (b1mx_RegEvX N s r0 x' .cause).compl (b1mx_RegEvX N s r0 x' .effect).compl

theorem measurableSet_B1FGoodX (s r0 : State N) (x : Fin N) (σ : XSide) :
    MeasurableSet {w : Param N | B1FGoodX N s r0 x σ w} := by
  have hstruct : {w : Param N | B1FGoodX N s r0 x σ w} = {w |
      RegEvX N s r0 x σ w ∧ (∀ r ∈ sensRows s r0, ∀ i, w r i ∈ Set.Ioo (0 : ℝ) 1) ∧
      N ≤ 3 * ham r0 s ∧
      (∀ r ∈ sensRows s r0, r ≠ r0 → r ≠ spRow s r0 x .cause → ∀ K : Finset (Fin N),
        K.card ≤ dX N → XW w r0 + b1Eta * N < XMW w (univ \ K) r) ∧
      (σ = .cause → (N : ℝ) / 400 ≤
        ∑ j ∈ univ.erase x, Real.log (clamp01 (w r0 j) / clamp01 (w (flipAt x r0) j))) ∧
      (∀ r ∈ sensRows s r0, r ≠ r0 → r ≠ s → r ≠ spRow s r0 x σ →
        ∑ i, pos (clamp01 (w r i) - b1Cap) ≤ (N : ℝ) / 5) ∧
      (∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 2 →
        ∑ i, Real.log (max (2 * b1CutMeanS w s r0 K' i) 1) ≤ 23 / 50 * (N : ℝ)) ∧
      (σ = .effect → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 3 →
        ∑ i, Real.log (max (2 * b1CutMeanPlus w r0 K' i) 1) ≤ 23 / 50 * (N : ℝ)) ∧
      (σ = .cause → ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 3 → x ∉ K' →
        ∑ i, Real.log (max (2 * b1CutMeanPlus w (flipAt x r0) K' i) 1) ≤ 23 / 50 * (N : ℝ)) ∧
      (∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 4 → (σ = .cause → K' ≠ {x}) →
        (N : ℝ) / 25 ≤ ∑ i, b1CutGX w r0 K' i) ∧
      (σ = .cause → -((N : ℝ) / 2000) ≤
        ∑ j ∈ univ.erase x, min (lamX w s r0 x .cause j) (Real.log (clamp01 (w r0 j) / cX))) ∧
      (σ = .cause → N ≤ 4 * (NegX w r0 x).card) ∧
      (∀ x' : Fin N, x' ≠ x → SingleNotFail w s r0 x') ∧
      (∀ hne : (univ : Finset (Fin N)).Nonempty,
        Real.exp ((N : ℝ) / 100) * sigN N ≤ univ.inf' hne (fun k => xE w s k - 1 / 2)) ∧
      (2 : ℝ) ^ (-(N : ℝ) / 2) ≤ eE w s ∧
      ∑ r ∈ (sensRows s r0).erase s, ∏ k, pTe w s r k ≤ sigN N} := by
    ext w
    exact ⟨fun h => ⟨h.regEv, h.openRows, h.far, h.ret, h.retR1, h.rowExc, h.nuS, h.nuTc, h.x5,
        h.posNear, h.x1, h.x2, h.failOnly, h.sRowMu', h.sRowE, h.sRowR⟩,
      fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ =>
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩⟩
  rw [hstruct]
  have h1 : MeasurableSet {w : Param N | RegEvX N s r0 x σ w} := b1mx_RegEvX N s r0 x σ
  have h2 : MeasurableSet {w : Param N |
      ∀ r ∈ sensRows s r0, ∀ i, w r i ∈ Set.Ioo (0 : ℝ) 1} :=
    b1_mset_forall fun r => b1_mset_imp (MeasurableSet.const _) (b1_mset_forall fun i =>
      b1m_coord r i measurableSet_Ioo)
  have h3 : MeasurableSet {_w : Param N | N ≤ 3 * ham r0 s} := MeasurableSet.const _
  have h4 : MeasurableSet {w : Param N |
      ∀ r ∈ sensRows s r0, r ≠ r0 → r ≠ spRow s r0 x .cause → ∀ K : Finset (Fin N),
        K.card ≤ dX N → XW w r0 + b1Eta * N < XMW w (univ \ K) r} :=
    b1_mset_forall fun r => b1_mset_imp (MeasurableSet.const _) (b1_mset_imp
      (MeasurableSet.const _) (b1_mset_imp (MeasurableSet.const _)
        (b1_mset_forall fun K => b1_mset_imp (MeasurableSet.const _)
          (measurableSet_lt ((b1m_XW r0).add_const _) (b1m_XMW _ r)))))
  have h5 : MeasurableSet {w : Param N | σ = .cause → (N : ℝ) / 400 ≤
      ∑ j ∈ univ.erase x, Real.log (clamp01 (w r0 j) / clamp01 (w (flipAt x r0) j))} :=
    b1_mset_imp (MeasurableSet.const _) (measurableSet_le measurable_const
      (Finset.measurable_sum _ fun j _ => ((b1m_clamp r0 j).div (b1m_clamp (flipAt x r0) j)).log))
  have h6 : MeasurableSet {w : Param N |
      ∀ r ∈ sensRows s r0, r ≠ r0 → r ≠ s → r ≠ spRow s r0 x σ →
        ∑ i, pos (clamp01 (w r i) - b1Cap) ≤ (N : ℝ) / 5} :=
    b1_mset_forall fun r => b1_mset_imp (MeasurableSet.const _) (b1_mset_imp
      (MeasurableSet.const _) (b1_mset_imp (MeasurableSet.const _) (b1_mset_imp
        (MeasurableSet.const _) (measurableSet_le (Finset.measurable_sum _ fun i _ =>
          b1_measurable_pos ((b1m_clamp r i).sub_const _)) measurable_const))))
  have h7 : MeasurableSet {w : Param N |
      ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 2 →
        ∑ i, Real.log (max (2 * b1CutMeanS w s r0 K' i) 1) ≤ 23 / 50 * (N : ℝ)} :=
    b1_mset_forall fun K' => b1_mset_imp (MeasurableSet.const _) (b1_mset_imp
      (MeasurableSet.const _) (measurableSet_le
        (Finset.measurable_sum _ fun i _ =>
          (((b1mx_CutMeanS s r0 K' i).const_mul 2).max measurable_const).log)
        measurable_const))
  have h8 : MeasurableSet {w : Param N | σ = .effect → ∀ K' : Finset (Fin N),
      K'.Nonempty → K'.card ≤ 3 →
        ∑ i, Real.log (max (2 * b1CutMeanPlus w r0 K' i) 1) ≤ 23 / 50 * (N : ℝ)} :=
    b1_mset_imp (MeasurableSet.const _) (b1_mset_forall fun K' => b1_mset_imp
      (MeasurableSet.const _) (b1_mset_imp (MeasurableSet.const _) (measurableSet_le
        (Finset.measurable_sum _ fun i _ =>
          (((b1mx_CutMeanPlus r0 K' i).const_mul 2).max measurable_const).log)
        measurable_const)))
  have h9 : MeasurableSet {w : Param N | σ = .cause → ∀ K' : Finset (Fin N),
      K'.Nonempty → K'.card ≤ 3 → x ∉ K' →
        ∑ i, Real.log (max (2 * b1CutMeanPlus w (flipAt x r0) K' i) 1) ≤ 23 / 50 * (N : ℝ)} :=
    b1_mset_imp (MeasurableSet.const _) (b1_mset_forall fun K' => b1_mset_imp
      (MeasurableSet.const _) (b1_mset_imp (MeasurableSet.const _) (b1_mset_imp (MeasurableSet.const _) (measurableSet_le
        (Finset.measurable_sum _ fun i _ =>
          (((b1mx_CutMeanPlus (flipAt x r0) K' i).const_mul 2).max measurable_const).log)
        measurable_const))))
  have h10 : MeasurableSet {w : Param N |
      ∀ K' : Finset (Fin N), K'.Nonempty → K'.card ≤ 4 → (σ = .cause → K' ≠ {x}) →
        (N : ℝ) / 25 ≤ ∑ i, b1CutGX w r0 K' i} :=
    b1_mset_forall fun K' => b1_mset_imp (MeasurableSet.const _) (b1_mset_imp
      (MeasurableSet.const _) (b1_mset_imp (MeasurableSet.const _) (measurableSet_le
        measurable_const (Finset.measurable_sum _ fun i _ => b1mx_CutGX r0 K' i))))
  have h11 : MeasurableSet {w : Param N | σ = .cause → -((N : ℝ) / 2000) ≤
      ∑ j ∈ univ.erase x, min (lamX w s r0 x .cause j) (Real.log (clamp01 (w r0 j) / cX))} :=
    b1_mset_imp (MeasurableSet.const _) (measurableSet_le measurable_const
      (Finset.measurable_sum _ fun j _ =>
        (b1mx_lamX s r0 x .cause j).min ((b1m_clamp r0 j).div_const _).log))
  have h12 : MeasurableSet {w : Param N | σ = .cause → N ≤ 4 * (NegX w r0 x).card} := by
    refine b1_mset_imp (MeasurableSet.const _) ?_
    have heq : {w : Param N | N ≤ 4 * (NegX w r0 x).card} =
        {w : Param N | (N + 3) / 4 ≤ (NegX w r0 x).card} := by
      ext w; simp only [Set.mem_setOf_eq]; omega
    rw [heq]; exact b1mx_measurableSet_NegX_card_ge r0 x _
  have h13 : MeasurableSet {w : Param N | ∀ x' : Fin N, x' ≠ x → SingleNotFail w s r0 x'} :=
    b1_mset_forall fun x' => b1_mset_imp (MeasurableSet.const _)
      (b1mx_SingleNotFail s r0 x')
  have h14 : MeasurableSet {w : Param N | ∀ hne : (univ : Finset (Fin N)).Nonempty,
      Real.exp ((N : ℝ) / 100) * sigN N ≤ univ.inf' hne (fun k => xE w s k - 1 / 2)} := by
    by_cases hU : (univ : Finset (Fin N)).Nonempty
    · have heq : {w : Param N | ∀ hne : (univ : Finset (Fin N)).Nonempty,
          Real.exp ((N : ℝ) / 100) * sigN N ≤ univ.inf' hne (fun k => xE w s k - 1 / 2)} =
          {w : Param N | Real.exp ((N : ℝ) / 100) * sigN N ≤
            univ.inf' hU (fun k => xE w s k - 1 / 2)} := by
        ext w; exact ⟨fun h => h hU, fun h _ => h⟩
      rw [heq]
      exact measurableSet_le measurable_const
        (b1_measurable_inf' hU fun k _ => (b1m_xE s k).sub_const _)
    · have heq : {w : Param N | ∀ hne : (univ : Finset (Fin N)).Nonempty,
          Real.exp ((N : ℝ) / 100) * sigN N ≤ univ.inf' hne (fun k => xE w s k - 1 / 2)} =
          Set.univ := by
        ext w; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro hne; exact absurd hne hU
      rw [heq]; exact MeasurableSet.univ
  have h15 : MeasurableSet {w : Param N | (2 : ℝ) ^ (-(N : ℝ) / 2) ≤ eE w s} :=
    measurableSet_le measurable_const (b1m_eE s)
  have h16 : MeasurableSet {w : Param N |
      ∑ r ∈ (sensRows s r0).erase s, ∏ k, pTe w s r k ≤ sigN N} :=
    measurableSet_le
      (Finset.measurable_sum _ fun r _ => Finset.measurable_prod _ fun k _ => b1mx_pTe s r k)
      measurable_const
  exact h1.inter (h2.inter (h3.inter (h4.inter (h5.inter (h6.inter (h7.inter (h8.inter
    (h9.inter (h10.inter (h11.inter (h12.inter (h13.inter (h14.inter (h15.inter h16))))))))))))))

theorem measurableSet_goodFX {N : ℕ} {s r0 : State N} {x : Fin N} {σ : XSide} :
    MeasurableSet (GoodFX N s r0 x σ) :=
  b1_measurable_Ext s r0 (measurableSet_B1FGoodX s r0 x σ)

theorem measurableSet_forcedX {N : ℕ} {s : State N} : MeasurableSet {w : Param N | ForcedX N s w} := by
  have hstruct : {w : Param N | ForcedX N s w} = {w | w ∈ openCube N ∧
      (1 / 2 ≤ Zs w ∧ Zs w ≤ b1ZMax) ∧ ∃ x σ, B1FGoodX N s (tcRow w) x σ w} := by
    ext w
    exact ⟨fun h => ⟨h.mem_open, h.zs, h.regime⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩
  rw [hstruct]
  refine b1_mset_and b1_measurableSet_openCube (b1_mset_and (b1_mset_and
    (measurableSet_le measurable_const b1m_Zs) (measurableSet_le b1m_Zs measurable_const)) ?_)
  refine b1_mset_exists fun x => b1_mset_exists fun σ => ?_
  exact b1_measurableSet_at_tcRow (P := fun w r0 => B1FGoodX N s r0 x σ w)
    fun r0 => measurableSet_B1FGoodX s r0 x σ

theorem mem_famX_measurable {N : ℕ} {s r0 : State N} {x : Fin N} {σ : XSide} (K : Finset (Fin N)) :
    MeasurableSet {w : Param N | K ∈ famX N s r0 x σ w} := by
  cases σ with
  | effect =>
      by_cases hK : K ∈ (univ : Finset (Fin N)).powersetCard (dX N)
      · simpa [famX, hK] using MeasurableSet.univ
      · simpa [famX, hK] using MeasurableSet.empty
  | cause =>
      have hset : {w : Param N | K ∈ famX N s r0 x .cause w} =
          if K.card = dX N then {w : Param N | K ⊆ NegX w r0 x} else ∅ := by
        unfold famX
        split_ifs with h <;>
          simp [Finset.mem_powersetCard, h, Set.eq_empty_iff_forall_notMem]
      rw [hset]
      split_ifs with h
      · have hset2 : {w : Param N | K ⊆ NegX w r0 x} =
            ⋂ j ∈ K, {w : Param N | j ∈ NegX w r0 x} := by
          ext w; simp [Finset.subset_iff]
        rw [hset2]
        refine MeasurableSet.biInter K.countable_toSet fun j _ => ?_
        show MeasurableSet {w : Param N | j ∈ NegX w r0 x}
        unfold NegX
        by_cases hjx : j = x
        · subst hjx
          simpa [Set.eq_empty_iff_forall_notMem] using MeasurableSet.empty
        · have heq : {w : Param N | j ∈ (univ.erase x).filter
                (fun k => 27 / 25 * clamp01 (w r0 k) ≤ clamp01 (w (flipAt x r0) k))} =
              {w : Param N | 27 / 25 * clamp01 (w r0 j) ≤ clamp01 (w (flipAt x r0) j)} := by
            ext w; simp [Finset.mem_filter, hjx]
          rw [heq]
          exact measurableSet_le
            (measurable_const.mul
              (clamp01_measurable.comp ((measurable_pi_apply j).comp (measurable_pi_apply r0))))
            (clamp01_measurable.comp
              ((measurable_pi_apply j).comp (measurable_pi_apply (flipAt x r0))))
      · exact MeasurableSet.empty

end Census
end IIT
