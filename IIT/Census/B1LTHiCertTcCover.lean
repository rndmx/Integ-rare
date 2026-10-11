/-
Census, B1 LTBetaHi, RL-tc certificate (W8 §8.2), part 1d: the 518 cells cover the RL-tc domain.

Domain (W8 §8.2, mode tcB): `G1, F1 ∈ [0, 22]` (A-rest, without `tc`), `G2, F2 ≥ 0`, `x ∈ [4/5, 1]`, `f ∈ [0, 1]`
(`V1 ≥ max(G1, F1)`, `V2 ≥ max(G2, F2)` are handled by the vertex/ray decomposition, not by the cover).
The cover is a guillotine tree (`tcTree`, reconstructed from the cells by `rltc_cover.py`): a node splits one
coordinate at a cut, a leaf `(j, i)` names cell `i` of data file `j`, whose box must EQUAL the region of the
leaf. `tcCoverB` checks this by `decide +kernel`; `tc_cover` is the consequence.
-/
import IIT.Census.B1LTHiCertTcAll

namespace IIT
namespace Census

/-- A point of the RL-tc domain: rest data `G1, F1, G2, F2` and tc's shared entries `x, f`. -/
structure TcPt where
  G1 : ℚ
  F1 : ℚ
  G2 : ℚ
  F2 : ℚ
  x : ℚ
  f : ℚ

/-- Coordinate `c` of a point. -/
def TcPt.get (p : TcPt) : ℕ → ℚ
  | 0 => p.G1
  | 1 => p.F1
  | 2 => p.G2
  | 3 => p.F2
  | 4 => p.x
  | _ => p.f

/-- A region: lower ends and optional upper ends of the six coordinates. -/
structure TcReg where
  l0 : ℚ
  h0 : Option ℚ
  l1 : ℚ
  h1 : Option ℚ
  l2 : ℚ
  h2 : Option ℚ
  l3 : ℚ
  h3 : Option ℚ
  l4 : ℚ
  h4 : Option ℚ
  l5 : ℚ
  h5 : Option ℚ
  deriving DecidableEq

def TcReg.lo (R : TcReg) : ℕ → ℚ
  | 0 => R.l0
  | 1 => R.l1
  | 2 => R.l2
  | 3 => R.l3
  | 4 => R.l4
  | _ => R.l5

def TcReg.hi (R : TcReg) : ℕ → Option ℚ
  | 0 => R.h0
  | 1 => R.h1
  | 2 => R.h2
  | 3 => R.h3
  | 4 => R.h4
  | _ => R.h5

def TcReg.setLo (R : TcReg) (c : ℕ) (v : ℚ) : TcReg :=
  match c with
  | 0 => { R with l0 := v }
  | 1 => { R with l1 := v }
  | 2 => { R with l2 := v }
  | 3 => { R with l3 := v }
  | 4 => { R with l4 := v }
  | _ => { R with l5 := v }

def TcReg.setHi (R : TcReg) (c : ℕ) (v : ℚ) : TcReg :=
  match c with
  | 0 => { R with h0 := some v }
  | 1 => { R with h1 := some v }
  | 2 => { R with h2 := some v }
  | 3 => { R with h3 := some v }
  | 4 => { R with h4 := some v }
  | _ => { R with h5 := some v }

/-- Membership in a region. -/
def TcReg.mem (R : TcReg) (p : TcPt) : Prop :=
  ∀ c < 6, R.lo c ≤ p.get c ∧ ∀ h, R.hi c = some h → p.get c ≤ h

/-- The region of a box (over its denominator `Q`). -/
def TcBox.reg (b : TcBox) : TcReg :=
  ⟨(b.g1lo : ℚ) / b.Q, some ((b.g1hi : ℚ) / b.Q), (b.f1lo : ℚ) / b.Q, some ((b.f1hi : ℚ) / b.Q),
    (b.g2lo : ℚ) / b.Q, b.g2hi.map fun h => (h : ℚ) / b.Q, (b.f2lo : ℚ) / b.Q, b.f2hi.map fun h => (h : ℚ) / b.Q,
    (b.xlo : ℚ) / b.Q, some ((b.xhi : ℚ) / b.Q), (b.flo : ℚ) / b.Q, some ((b.fhi : ℚ) / b.Q)⟩

/-- The RL-tc domain. -/
def tcDom : TcReg := ⟨0, some 22, 0, some 22, 0, none, 0, none, 4 / 5, some 1, 0, some 1⟩

/-- A guillotine tree; a leaf `(j, i)` is cell `i` of data file `j`. -/
inductive TcTree
  | leaf (j i : ℕ)
  | node (c : ℕ) (cut : ℚ) (l r : TcTree)

/-- The data files. -/
def tcFileList : ℕ → List TcCell
  | 0 => tcCellsD00
  | 1 => tcCellsD01
  | 2 => tcCellsD02
  | 3 => tcCellsD03
  | 4 => tcCellsD04
  | 5 => tcCellsD05
  | 6 => tcCellsD06
  | 7 => tcCellsD07
  | 8 => tcCellsD08
  | 9 => tcCellsD09
  | 10 => tcCellsD10
  | 11 => tcCellsD11
  | 12 => tcCellsD12
  | 13 => tcCellsD13
  | _ => []

/-- A default cell (never used: leaves are checked to be in range). -/
def tcCellDflt : TcCell := ⟨⟨0, 0, 0, 0, 0, none, 0, none, 0, 0, 0, 0, 1⟩, 0, 0, 1, 0, [], []⟩

/-- **The cover checker.** -/
def tcCoverB : TcTree → TcReg → Bool
  | .leaf j i, R => decide (i < (tcFileList j).length) && decide (((tcFileList j).getD i tcCellDflt).box.reg = R)
  | .node c cut l r, R => decide (c < 6) && tcCoverB l (R.setHi c cut) && tcCoverB r (R.setLo c cut)

lemma TcReg.setHi_lo (R : TcReg) (c : ℕ) (v : ℚ) (c' : ℕ) : (R.setHi c v).lo c' = R.lo c' := by
  rcases c with _ | _ | _ | _ | _ | c <;> rcases c' with _ | _ | _ | _ | _ | c' <;> rfl

lemma TcReg.setLo_hi (R : TcReg) (c : ℕ) (v : ℚ) (c' : ℕ) : (R.setLo c v).hi c' = R.hi c' := by
  rcases c with _ | _ | _ | _ | _ | c <;> rcases c' with _ | _ | _ | _ | _ | c' <;> rfl

lemma TcReg.setHi_hi (R : TcReg) {c : ℕ} (hc : c < 6) (v : ℚ) {c' : ℕ} (hc' : c' < 6) :
    (R.setHi c v).hi c' = if c' = c then some v else R.hi c' := by
  interval_cases c <;> interval_cases c' <;> rfl

lemma TcReg.setLo_lo (R : TcReg) {c : ℕ} (hc : c < 6) (v : ℚ) {c' : ℕ} (hc' : c' < 6) :
    (R.setLo c v).lo c' = if c' = c then v else R.lo c' := by
  interval_cases c <;> interval_cases c' <;> rfl

lemma TcReg.mem_split {R : TcReg} {p : TcPt} (h : R.mem p) {c : ℕ} (hc : c < 6) (cut : ℚ) :
    (R.setHi c cut).mem p ∨ (R.setLo c cut).mem p := by
  rcases le_total (p.get c) cut with h1 | h1
  · left
    intro c' hc'
    obtain ⟨hl, hh⟩ := h c' hc'
    refine ⟨by rw [TcReg.setHi_lo]; exact hl, fun h0 hh0 => ?_⟩
    rw [TcReg.setHi_hi R hc cut hc'] at hh0
    split_ifs at hh0 with hcc
    · subst hcc; cases hh0; exact h1
    · exact hh h0 hh0
  · right
    intro c' hc'
    obtain ⟨hl, hh⟩ := h c' hc'
    refine ⟨?_, fun h0 hh0 => ?_⟩
    · rw [TcReg.setLo_lo R hc cut hc']
      split_ifs with hcc
      · subst hcc; exact h1
      · exact hl
    · rw [TcReg.setLo_hi] at hh0; exact hh h0 hh0

/-- **Soundness of the cover checker.** -/
theorem tcCoverB_sound : ∀ (t : TcTree) (R : TcReg), tcCoverB t R = true → ∀ p, R.mem p →
    ∃ j i, i < (tcFileList j).length ∧ ((tcFileList j).getD i tcCellDflt).box.reg.mem p
  | .leaf j i, R, h, p, hp => by
    simp only [tcCoverB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨j, i, h.1, h.2 ▸ hp⟩
  | .node c cut l r, R, h, p, hp => by
    simp only [tcCoverB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases TcReg.mem_split hp h.1.1 cut with h' | h'
    · exact tcCoverB_sound l _ h.1.2 p h'
    · exact tcCoverB_sound r _ h.2 p h'

lemma tcFileList_sub {j : ℕ} {C : TcCell} (hC : C ∈ tcFileList j) : C ∈ tcCellsAll := by
  unfold tcFileList at hC
  split at hC <;> simp_all [tcCellsAll]

/-- The guillotine tree of the 518 cells (generated by `rltc_cover.py`). -/
def tcTree : TcTree :=
  (.node 0 (11 / 2 : ℚ) (.node 1 (11 / 2 : ℚ) (.node 0 (11 / 4 : ℚ) (.node 1 (11 / 4 : ℚ) (.node 4 (17 / 20 : ℚ) (.node 2 (2 : ℚ) (.node 3 (2 : ℚ) (.node 0 (11 / 8 : ℚ) (.node 1 (11 / 8 : ℚ) (.node 5 (1 / 4 : ℚ) (.node 2 (1 : ℚ) (.node 3 (1 : ℚ) (.leaf 7 4) (.leaf 7 5)) (.node 3 (1 : ℚ) (.leaf 7 6) (.leaf 7 7))) (.node 5 (1 / 2 : ℚ) (.leaf 5 0) (.node 2 (1 : ℚ) (.node 3 (1 : ℚ) (.node 0 (11 / 16 : ℚ) (.node 5 (3 / 4 : ℚ) (.node 1 (11 / 16 : ℚ) (.leaf 8 23) (.node 2 (1 / 2 : ℚ) (.node 3 (1 / 2 : ℚ) (.node 5 (5 / 8 : ℚ) (.leaf 9 21) (.node 0 (11 / 32 : ℚ) (.node 2 (1 / 4 : ℚ) (.node 3 (1 / 4 : ℚ) (.node 1 (33 / 32 : ℚ) (.leaf 11 7) (.leaf 11 8)) (.leaf 11 4)) (.leaf 10 24)) (.node 1 (33 / 32 : ℚ) (.node 2 (1 / 4 : ℚ) (.node 0 (33 / 64 : ℚ) (.node 1 (55 / 64 : ℚ) (.node 3 (1 / 4 : ℚ) (.leaf 11 20) (.leaf 11 22)) (.node 3 (1 / 4 : ℚ) (.leaf 11 21) (.leaf 11 23))) (.node 1 (55 / 64 : ℚ) (.node 3 (1 / 8 : ℚ) (.node 2 (1 / 8 : ℚ) (.node 4 (33 / 40 : ℚ) (.node 5 (11 / 16 : ℚ) (.leaf 12 15) (.leaf 12 16)) (.node 5 (11 / 16 : ℚ) (.node 0 (77 / 128 : ℚ) (.node 1 (99 / 128 : ℚ) (.node 2 (1 / 16 : ℚ) (.node 3 (1 / 16 : ℚ) (.leaf 13 4) (.leaf 13 5)) (.leaf 13 2)) (.node 2 (1 / 16 : ℚ) (.node 3 (1 / 16 : ℚ) (.leaf 13 6) (.leaf 13 7)) (.leaf 13 3))) (.node 1 (99 / 128 : ℚ) (.leaf 13 0) (.leaf 13 1))) (.leaf 12 17))) (.node 4 (33 / 40 : ℚ) (.node 5 (11 / 16 : ℚ) (.leaf 12 18) (.leaf 12 20)) (.node 5 (11 / 16 : ℚ) (.leaf 12 19) (.leaf 12 21)))) (.node 3 (1 / 4 : ℚ) (.node 2 (1 / 8 : ℚ) (.leaf 12 3) (.leaf 12 4)) (.leaf 11 24))) (.node 2 (1 / 8 : ℚ) (.node 3 (1 / 8 : ℚ) (.leaf 12 5) (.node 3 (1 / 4 : ℚ) (.leaf 12 6) (.node 3 (3 / 8 : ℚ) (.leaf 12 7) (.leaf 12 8)))) (.node 3 (1 / 4 : ℚ) (.leaf 11 27) (.node 3 (3 / 8 : ℚ) (.leaf 12 9) (.leaf 12 10)))))) (.leaf 11 5)) (.leaf 10 25)))) (.node 5 (5 / 8 : ℚ) (.leaf 9 22) (.leaf 9 25))) (.node 5 (5 / 8 : ℚ) (.node 3 (1 / 2 : ℚ) (.leaf 9 23) (.leaf 9 24)) (.leaf 9 8)))) (.node 2 (1 / 2 : ℚ) (.node 3 (1 / 2 : ℚ) (.node 0 (11 / 32 : ℚ) (.node 1 (11 / 16 : ℚ) (.leaf 10 7) (.node 2 (1 / 4 : ℚ) (.node 1 (33 / 32 : ℚ) (.leaf 10 26) (.leaf 10 27)) (.leaf 10 17))) (.node 1 (11 / 16 : ℚ) (.leaf 10 8) (.node 1 (33 / 32 : ℚ) (.node 2 (1 / 4 : ℚ) (.node 3 (1 / 4 : ℚ) (.leaf 11 6) (.node 5 (7 / 8 : ℚ) (.leaf 11 9) (.node 0 (33 / 64 : ℚ) (.leaf 11 15) (.leaf 11 16)))) (.leaf 10 28)) (.leaf 10 18)))) (.leaf 9 0)) (.node 1 (11 / 16 : ℚ) (.leaf 9 1) (.leaf 9 2)))) (.node 5 (5 / 8 : ℚ) (.node 1 (11 / 16 : ℚ) (.node 2 (1 / 2 : ℚ) (.node 3 (1 / 2 : ℚ) (.node 5 (9 / 16 : ℚ) (.leaf 10 13) (.leaf 10 14)) (.leaf 9 26)) (.node 3 (1 / 2 : ℚ) (.leaf 9 27) (.leaf 9 28))) (.node 2 (1 / 2 : ℚ) (.node 3 (1 / 2 : ℚ) (.node 5 (9 / 16 : ℚ) (.leaf 10 15) (.leaf 10 16)) (.leaf 10 2)) (.node 3 (1 / 2 : ℚ) (.leaf 10 3) (.leaf 10 4)))) (.node 5 (3 / 4 : ℚ) (.node 1 (11 / 16 : ℚ) (.node 2 (1 / 2 : ℚ) (.node 3 (1 / 2 : ℚ) (.leaf 10 0) (.leaf 10 1)) (.leaf 9 9)) (.node 2 (1 / 2 : ℚ) (.node 3 (1 / 2 : ℚ) (.leaf 10 5) (.leaf 10 6)) (.leaf 9 10))) (.leaf 8 4)))) (.node 5 (3 / 4 : ℚ) (.leaf 7 13) (.leaf 7 14))) (.node 5 (3 / 4 : ℚ) (.leaf 6 2) (.leaf 6 3))))) (.node 2 (1 : ℚ) (.node 3 (1 : ℚ) (.node 0 (11 / 16 : ℚ) (.node 5 (1 / 4 : ℚ) (.leaf 8 1) (.node 5 (1 / 2 : ℚ) (.leaf 8 2) (.node 5 (3 / 4 : ℚ) (.leaf 8 5) (.leaf 8 6)))) (.node 5 (1 / 4 : ℚ) (.node 1 (33 / 16 : ℚ) (.node 2 (1 / 2 : ℚ) (.node 3 (1 / 2 : ℚ) (.node 0 (33 / 32 : ℚ) (.node 1 (55 / 32 : ℚ) (.leaf 10 11) (.leaf 10 12)) (.leaf 9 20)) (.leaf 9 7)) (.leaf 8 27)) (.leaf 8 19)) (.node 5 (3 / 8 : ℚ) (.leaf 8 20) (.node 5 (1 / 2 : ℚ) (.node 1 (33 / 16 : ℚ) (.leaf 8 28) (.leaf 8 29)) (.node 5 (3 / 4 : ℚ) (.node 1 (33 / 16 : ℚ) (.node 5 (5 / 8 : ℚ) (.node 2 (1 / 2 : ℚ) (.node 3 (1 / 2 : ℚ) (.node 5 (9 / 16 : ℚ) (.node 0 (33 / 32 : ℚ) (.leaf 11 0) (.node 1 (55 / 32 : ℚ) (.node 2 (1 / 4 : ℚ) (.node 0 (77 / 64 : ℚ) (.node 3 (1 / 4 : ℚ) (.node 5 (17 / 32 : ℚ) (.node 1 (99 / 64 : ℚ) (.leaf 12 11) (.leaf 12 12)) (.leaf 11 29)) (.node 5 (17 / 32 : ℚ) (.leaf 12 1) (.leaf 12 2))) (.node 3 (1 / 4 : ℚ) (.node 5 (17 / 32 : ℚ) (.leaf 11 28) (.leaf 12 0)) (.node 1 (99 / 64 : ℚ) (.node 2 (1 / 8 : ℚ) (.node 3 (3 / 8 : ℚ) (.node 5 (17 / 32 : ℚ) (.node 4 (33 / 40 : ℚ) (.leaf 12 28) (.leaf 12 29)) (.leaf 12 24)) (.node 5 (17 / 32 : ℚ) (.leaf 12 22) (.leaf 12 25))) (.node 3 (3 / 8 : ℚ) (.node 5 (17 / 32 : ℚ) (.node 4 (33 / 40 : ℚ) (.leaf 12 30) (.leaf 12 31)) (.leaf 12 26)) (.node 5 (17 / 32 : ℚ) (.leaf 12 23) (.leaf 12 27)))) (.node 5 (17 / 32 : ℚ) (.leaf 12 13) (.leaf 12 14))))) (.leaf 11 10)) (.node 2 (1 / 4 : ℚ) (.node 3 (1 / 4 : ℚ) (.leaf 11 17) (.leaf 11 18)) (.leaf 11 11)))) (.leaf 10 19)) (.leaf 10 9)) (.leaf 9 11)) (.leaf 9 3)) (.leaf 8 24)) (.leaf 8 7)))))) (.node 5 (1 / 4 : ℚ) (.leaf 7 8) (.node 5 (1 / 2 : ℚ) (.leaf 7 9) (.node 5 (3 / 4 : ℚ) (.leaf 7 15) (.leaf 7 16))))) (.node 5 (1 / 4 : ℚ) (.leaf 5 28) (.node 5 (1 / 2 : ℚ) (.leaf 5 29) (.node 5 (3 / 4 : ℚ) (.leaf 6 4) (.leaf 6 5)))))) (.node 5 (1 / 2 : ℚ) (.leaf 3 18) (.leaf 3 26))) (.node 5 (1 / 2 : ℚ) (.leaf 2 30) (.leaf 2 35))) (.node 5 (1 / 2 : ℚ) (.leaf 1 39) (.leaf 1 41))) (.node 4 (9 / 10 : ℚ) (.node 5 (1 / 2 : ℚ) (.node 2 (2 : ℚ) (.node 3 (2 : ℚ) (.node 0 (11 / 8 : ℚ) (.node 1 (11 / 8 : ℚ) (.node 5 (1 / 4 : ℚ) (.node 2 (1 : ℚ) (.node 3 (1 : ℚ) (.leaf 7 17) (.leaf 7 18)) (.leaf 6 20)) (.leaf 5 10)) (.node 2 (1 : ℚ) (.node 3 (1 : ℚ) (.node 0 (11 / 16 : ℚ) (.node 5 (1 / 4 : ℚ) (.leaf 8 8) (.leaf 8 10)) (.node 5 (1 / 4 : ℚ) (.leaf 8 9) (.leaf 8 11))) (.node 5 (1 / 4 : ℚ) (.leaf 7 19) (.leaf 7 20))) (.node 5 (1 / 4 : ℚ) (.leaf 6 21) (.leaf 6 22)))) (.leaf 3 35)) (.leaf 3 0)) (.leaf 2 2)) (.node 0 (11 / 8 : ℚ) (.node 1 (11 / 8 : ℚ) (.node 2 (1 : ℚ) (.node 3 (1 : ℚ) (.node 0 (11 / 16 : ℚ) (.node 1 (11 / 16 : ℚ) (.leaf 8 12) (.node 2 (1 / 2 : ℚ) (.node 3 (1 / 2 : ℚ) (.node 5 (3 / 4 : ℚ) (.leaf 9 12) (.node 0 (11 / 32 : ℚ) (.node 1 (33 / 32 : ℚ) (.leaf 10 20) (.leaf 10 21)) (.leaf 10 10))) (.leaf 9 4)) (.leaf 8 25))) (.leaf 7 21)) (.node 3 (2 : ℚ) (.leaf 6 23) (.leaf 5 15))) (.node 2 (2 : ℚ) (.leaf 4 26) (.leaf 3 37))) (.node 2 (1 : ℚ) (.node 3 (1 : ℚ) (.node 0 (11 / 16 : ℚ) (.leaf 7 22) (.leaf 7 23)) (.node 3 (2 : ℚ) (.leaf 6 24) (.leaf 5 16))) (.node 2 (2 : ℚ) (.leaf 4 27) (.leaf 3 38)))) (.leaf 2 4))) (.node 4 (19 / 20 : ℚ) (.node 2 (2 : ℚ) (.node 3 (2 : ℚ) (.node 0 (11 / 8 : ℚ) (.node 1 (11 / 8 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 4 28) (.node 5 (3 / 4 : ℚ) (.leaf 5 18) (.node 2 (1 : ℚ) (.node 3 (1 : ℚ) (.node 0 (11 / 16 : ℚ) (.node 2 (1 / 2 : ℚ) (.node 3 (1 / 2 : ℚ) (.node 0 (11 / 32 : ℚ) (.node 2 (1 / 4 : ℚ) (.node 3 (1 / 4 : ℚ) (.node 1 (11 / 16 : ℚ) (.leaf 11 1) (.node 0 (11 / 64 : ℚ) (.node 2 (1 / 8 : ℚ) (.node 3 (1 / 8 : ℚ) (.node 1 (33 / 32 : ℚ) (.leaf 11 25) (.leaf 11 26)) (.leaf 11 19)) (.leaf 11 12)) (.node 1 (33 / 32 : ℚ) (.leaf 11 13) (.leaf 11 14)))) (.leaf 10 22)) (.node 1 (11 / 32 : ℚ) (.leaf 11 2) (.node 1 (11 / 16 : ℚ) (.leaf 11 3) (.leaf 10 23)))) (.leaf 9 13)) (.node 1 (11 / 16 : ℚ) (.leaf 9 14) (.leaf 9 15))) (.leaf 8 26)) (.node 1 (11 / 16 : ℚ) (.node 2 (1 / 2 : ℚ) (.node 3 (1 / 2 : ℚ) (.leaf 9 16) (.leaf 9 17)) (.leaf 9 5)) (.node 2 (1 / 2 : ℚ) (.node 3 (1 / 2 : ℚ) (.leaf 9 18) (.leaf 9 19)) (.leaf 9 6)))) (.leaf 7 25)) (.leaf 6 26)))) (.node 5 (1 / 4 : ℚ) (.leaf 5 17) (.node 2 (1 : ℚ) (.node 3 (1 : ℚ) (.node 0 (11 / 16 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 8 13) (.node 5 (3 / 4 : ℚ) (.leaf 8 15) (.leaf 8 17))) (.node 5 (1 / 2 : ℚ) (.leaf 8 14) (.node 5 (3 / 4 : ℚ) (.leaf 8 16) (.leaf 8 18)))) (.node 5 (1 / 2 : ℚ) (.leaf 7 24) (.node 5 (3 / 4 : ℚ) (.leaf 7 26) (.leaf 7 27)))) (.node 5 (1 / 2 : ℚ) (.leaf 6 25) (.node 5 (3 / 4 : ℚ) (.leaf 6 27) (.leaf 6 28)))))) (.node 5 (1 / 2 : ℚ) (.leaf 3 39) (.leaf 4 0))) (.node 5 (1 / 2 : ℚ) (.leaf 3 4) (.leaf 3 6))) (.node 5 (1 / 2 : ℚ) (.leaf 2 6) (.leaf 2 20))) (.node 0 (11 / 8 : ℚ) (.node 1 (11 / 8 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 3 14) (.leaf 3 15)) (.node 2 (1 : ℚ) (.node 3 (1 : ℚ) (.node 0 (11 / 16 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 7 28) (.leaf 7 30)) (.node 5 (1 / 2 : ℚ) (.leaf 7 29) (.leaf 8 0))) (.node 3 (2 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 7 2) (.leaf 7 3)) (.node 5 (1 / 2 : ℚ) (.leaf 5 26) (.leaf 5 27)))) (.node 2 (2 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 4 33) (.leaf 4 34)) (.node 5 (1 / 2 : ℚ) (.leaf 4 7) (.leaf 4 8))))) (.node 5 (1 / 2 : ℚ) (.leaf 2 25) (.leaf 2 28)))))) (.node 4 (17 / 20 : ℚ) (.node 2 (2 : ℚ) (.node 5 (1 / 2 : ℚ) (.node 3 (2 : ℚ) (.node 0 (11 / 8 : ℚ) (.leaf 3 19) (.node 1 (33 / 8 : ℚ) (.node 2 (1 : ℚ) (.node 3 (1 : ℚ) (.node 5 (1 / 4 : ℚ) (.node 0 (33 / 16 : ℚ) (.leaf 8 3) (.node 1 (55 / 16 : ℚ) (.leaf 8 21) (.leaf 8 22))) (.leaf 7 11)) (.node 5 (1 / 4 : ℚ) (.leaf 7 10) (.leaf 7 12))) (.node 5 (1 / 4 : ℚ) (.leaf 6 0) (.leaf 6 1))) (.node 5 (1 / 4 : ℚ) (.leaf 5 1) (.leaf 5 2)))) (.leaf 2 31)) (.node 0 (11 / 8 : ℚ) (.leaf 2 36) (.node 3 (2 : ℚ) (.node 1 (33 / 8 : ℚ) (.leaf 4 17) (.leaf 4 18)) (.leaf 3 27)))) (.node 5 (1 / 2 : ℚ) (.leaf 1 40) (.leaf 1 42))) (.node 4 (9 / 10 : ℚ) (.node 5 (1 / 2 : ℚ) (.node 2 (2 : ℚ) (.node 3 (2 : ℚ) (.node 0 (11 / 8 : ℚ) (.leaf 3 36) (.node 1 (33 / 8 : ℚ) (.node 5 (1 / 4 : ℚ) (.leaf 5 11) (.leaf 5 13)) (.node 5 (1 / 4 : ℚ) (.leaf 5 12) (.leaf 5 14)))) (.leaf 3 1)) (.leaf 2 3)) (.node 0 (11 / 8 : ℚ) (.leaf 2 5) (.node 1 (33 / 8 : ℚ) (.leaf 3 2) (.leaf 3 3)))) (.node 4 (19 / 20 : ℚ) (.node 2 (2 : ℚ) (.node 3 (2 : ℚ) (.node 0 (11 / 8 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 3 40) (.leaf 4 1)) (.node 5 (1 / 2 : ℚ) (.leaf 3 41) (.node 1 (33 / 8 : ℚ) (.leaf 4 29) (.leaf 4 30)))) (.node 5 (1 / 2 : ℚ) (.leaf 3 5) (.leaf 3 7))) (.node 5 (1 / 2 : ℚ) (.leaf 2 7) (.leaf 2 21))) (.node 0 (11 / 8 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 2 26) (.leaf 2 29)) (.node 5 (1 / 2 : ℚ) (.leaf 2 27) (.node 1 (33 / 8 : ℚ) (.leaf 3 16) (.leaf 3 17)))))))) (.node 4 (17 / 20 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 36) (.leaf 0 41)) (.node 4 (9 / 10 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 49) (.leaf 0 52)) (.node 4 (19 / 20 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 56) (.leaf 0 70)) (.node 5 (1 / 2 : ℚ) (.leaf 0 73) (.leaf 0 75)))))) (.node 1 (11 : ℚ) (.node 0 (11 / 4 : ℚ) (.node 4 (17 / 20 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 37) (.leaf 0 42)) (.node 4 (9 / 10 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 50) (.leaf 0 53)) (.node 4 (19 / 20 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 57) (.leaf 0 71)) (.node 5 (1 / 2 : ℚ) (.leaf 0 74) (.leaf 0 76))))) (.node 1 (33 / 4 : ℚ) (.node 4 (17 / 20 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 78) (.leaf 0 84)) (.node 4 (9 / 10 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 88) (.leaf 0 92)) (.node 4 (19 / 20 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 1 1) (.leaf 1 17)) (.node 5 (1 / 2 : ℚ) (.leaf 1 33) (.leaf 1 35))))) (.node 4 (17 / 20 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 79) (.leaf 0 85)) (.node 4 (9 / 10 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 89) (.leaf 1 0)) (.node 4 (19 / 20 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 1 2) (.leaf 1 18)) (.node 5 (1 / 2 : ℚ) (.leaf 1 34) (.leaf 1 36))))))) (.node 4 (17 / 20 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 4) (.leaf 0 9)) (.node 4 (9 / 10 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 12) (.leaf 0 14)) (.node 4 (19 / 20 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 15) (.leaf 0 17)) (.node 5 (1 / 2 : ℚ) (.leaf 0 21) (.leaf 0 23))))))) (.node 0 (11 : ℚ) (.node 1 (11 : ℚ) (.node 4 (17 / 20 : ℚ) (.node 5 (1 / 2 : ℚ) (.node 1 (11 / 2 : ℚ) (.node 2 (2 : ℚ) (.node 0 (33 / 4 : ℚ) (.leaf 0 80) (.node 1 (11 / 4 : ℚ) (.node 2 (1 : ℚ) (.node 3 (2 : ℚ) (.node 5 (1 / 4 : ℚ) (.leaf 4 9) (.leaf 4 10)) (.leaf 3 20)) (.leaf 2 32)) (.node 2 (1 : ℚ) (.node 3 (2 : ℚ) (.node 5 (1 / 4 : ℚ) (.leaf 4 11) (.leaf 4 12)) (.leaf 3 21)) (.leaf 2 33)))) (.leaf 0 38)) (.node 2 (2 : ℚ) (.node 0 (33 / 4 : ℚ) (.leaf 0 81) (.node 1 (33 / 4 : ℚ) (.node 2 (1 : ℚ) (.node 3 (2 : ℚ) (.node 5 (1 / 4 : ℚ) (.leaf 4 13) (.leaf 4 14)) (.leaf 3 22)) (.leaf 2 34)) (.node 2 (1 : ℚ) (.node 3 (2 : ℚ) (.node 5 (1 / 4 : ℚ) (.leaf 4 15) (.leaf 4 16)) (.leaf 3 23)) (.node 5 (1 / 4 : ℚ) (.leaf 3 24) (.leaf 3 25))))) (.leaf 0 39))) (.leaf 0 8)) (.node 4 (9 / 10 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 11) (.leaf 0 13)) (.node 4 (19 / 20 : ℚ) (.node 5 (1 / 2 : ℚ) (.node 1 (11 / 2 : ℚ) (.node 2 (2 : ℚ) (.leaf 0 58) (.leaf 0 59)) (.node 2 (2 : ℚ) (.node 0 (33 / 4 : ℚ) (.leaf 1 3) (.leaf 1 4)) (.leaf 0 60))) (.leaf 0 16)) (.node 5 (1 / 2 : ℚ) (.leaf 0 20) (.leaf 0 22))))) (.node 1 (33 / 2 : ℚ) (.node 4 (17 / 20 : ℚ) (.node 5 (1 / 2 : ℚ) (.node 2 (2 : ℚ) (.node 0 (33 / 4 : ℚ) (.leaf 0 82) (.leaf 0 83)) (.leaf 0 40)) (.node 0 (33 / 4 : ℚ) (.leaf 0 43) (.node 2 (2 : ℚ) (.node 1 (55 / 4 : ℚ) (.leaf 1 43) (.leaf 1 44)) (.leaf 0 86)))) (.node 4 (9 / 10 : ℚ) (.node 5 (1 / 2 : ℚ) (.node 2 (2 : ℚ) (.node 0 (33 / 4 : ℚ) (.leaf 0 90) (.leaf 0 91)) (.leaf 0 51)) (.node 0 (33 / 4 : ℚ) (.leaf 0 54) (.leaf 0 55))) (.node 4 (19 / 20 : ℚ) (.node 5 (1 / 2 : ℚ) (.node 2 (2 : ℚ) (.node 0 (33 / 4 : ℚ) (.leaf 1 5) (.leaf 1 6)) (.leaf 0 61)) (.node 0 (33 / 4 : ℚ) (.leaf 0 72) (.node 2 (2 : ℚ) (.node 1 (55 / 4 : ℚ) (.node 2 (1 : ℚ) (.node 3 (2 : ℚ) (.node 5 (3 / 4 : ℚ) (.node 3 (1 : ℚ) (.leaf 5 19) (.leaf 5 20)) (.node 0 (77 / 8 : ℚ) (.leaf 5 21) (.leaf 5 22))) (.leaf 4 2)) (.leaf 3 8)) (.leaf 2 22)) (.leaf 1 19)))) (.node 5 (1 / 2 : ℚ) (.leaf 0 33) (.node 0 (33 / 4 : ℚ) (.leaf 0 77) (.node 1 (55 / 4 : ℚ) (.leaf 1 37) (.leaf 1 38))))))) (.node 4 (17 / 20 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 24) (.leaf 0 27)) (.node 4 (9 / 10 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 29) (.leaf 0 30)) (.node 4 (19 / 20 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 31) (.leaf 0 32)) (.node 5 (1 / 2 : ℚ) (.leaf 0 34) (.leaf 0 35))))))) (.node 4 (17 / 20 : ℚ) (.node 0 (33 / 2 : ℚ) (.node 1 (11 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 5) (.leaf 0 10)) (.node 1 (33 / 2 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 25) (.leaf 0 28)) (.node 5 (1 / 2 : ℚ) (.leaf 0 26) (.node 1 (77 / 4 : ℚ) (.leaf 0 46) (.leaf 0 47))))) (.node 1 (11 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 6) (.node 0 (77 / 4 : ℚ) (.node 1 (11 / 2 : ℚ) (.leaf 0 44) (.leaf 0 45)) (.node 1 (11 / 2 : ℚ) (.node 2 (2 : ℚ) (.node 0 (165 / 8 : ℚ) (.node 1 (11 / 4 : ℚ) (.node 2 (1 : ℚ) (.node 3 (2 : ℚ) (.node 5 (3 / 4 : ℚ) (.node 3 (1 : ℚ) (.leaf 6 6) (.leaf 6 7)) (.leaf 5 3)) (.leaf 4 19)) (.leaf 3 28)) (.node 2 (1 : ℚ) (.node 3 (2 : ℚ) (.node 5 (3 / 4 : ℚ) (.node 3 (1 : ℚ) (.leaf 6 8) (.leaf 6 9)) (.leaf 5 4)) (.leaf 4 20)) (.leaf 3 29))) (.node 1 (11 / 4 : ℚ) (.leaf 2 37) (.leaf 2 38))) (.node 2 (4 : ℚ) (.leaf 1 45) (.leaf 1 46))) (.node 2 (2 : ℚ) (.node 0 (165 / 8 : ℚ) (.node 1 (33 / 4 : ℚ) (.node 2 (1 : ℚ) (.node 3 (2 : ℚ) (.node 5 (3 / 4 : ℚ) (.node 3 (1 : ℚ) (.leaf 6 10) (.leaf 6 11)) (.leaf 5 5)) (.leaf 4 21)) (.leaf 3 30)) (.node 2 (1 : ℚ) (.node 3 (2 : ℚ) (.node 5 (3 / 4 : ℚ) (.node 3 (1 : ℚ) (.leaf 6 12) (.leaf 6 13)) (.leaf 5 6)) (.leaf 4 22)) (.leaf 3 31))) (.node 1 (33 / 4 : ℚ) (.leaf 2 39) (.leaf 2 40))) (.node 2 (4 : ℚ) (.leaf 1 47) (.leaf 1 48)))))) (.node 5 (1 / 2 : ℚ) (.leaf 0 7) (.node 0 (77 / 4 : ℚ) (.node 1 (33 / 2 : ℚ) (.leaf 0 48) (.node 1 (77 / 4 : ℚ) (.leaf 0 87) (.node 2 (2 : ℚ) (.node 1 (165 / 8 : ℚ) (.leaf 2 43) (.leaf 2 44)) (.leaf 1 51)))) (.node 1 (33 / 2 : ℚ) (.node 2 (2 : ℚ) (.node 0 (165 / 8 : ℚ) (.node 1 (55 / 4 : ℚ) (.node 2 (1 : ℚ) (.node 3 (2 : ℚ) (.node 5 (3 / 4 : ℚ) (.node 3 (1 : ℚ) (.leaf 6 14) (.leaf 6 15)) (.leaf 5 7)) (.leaf 4 23)) (.leaf 3 32)) (.node 2 (1 : ℚ) (.node 3 (2 : ℚ) (.node 5 (3 / 4 : ℚ) (.node 3 (1 : ℚ) (.leaf 6 16) (.leaf 6 17)) (.leaf 5 8)) (.leaf 4 24)) (.leaf 3 33))) (.node 1 (55 / 4 : ℚ) (.leaf 2 41) (.leaf 2 42))) (.node 2 (4 : ℚ) (.leaf 1 49) (.leaf 1 50))) (.node 2 (2 : ℚ) (.node 0 (165 / 8 : ℚ) (.node 1 (77 / 4 : ℚ) (.node 2 (1 : ℚ) (.node 3 (2 : ℚ) (.node 5 (3 / 4 : ℚ) (.node 3 (1 : ℚ) (.leaf 6 18) (.leaf 6 19)) (.leaf 5 9)) (.leaf 4 25)) (.leaf 3 34)) (.leaf 2 46)) (.node 1 (77 / 4 : ℚ) (.leaf 2 45) (.leaf 2 47))) (.node 2 (4 : ℚ) (.leaf 2 0) (.leaf 2 1)))))))) (.node 4 (9 / 10 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 0) (.leaf 0 1)) (.node 4 (19 / 20 : ℚ) (.node 0 (33 / 2 : ℚ) (.node 1 (11 : ℚ) (.node 5 (1 / 2 : ℚ) (.node 1 (11 / 2 : ℚ) (.node 2 (2 : ℚ) (.leaf 0 62) (.node 2 (4 : ℚ) (.leaf 1 7) (.node 2 (8 : ℚ) (.leaf 2 8) (.leaf 2 9)))) (.node 2 (2 : ℚ) (.leaf 0 63) (.node 2 (4 : ℚ) (.leaf 1 8) (.node 2 (8 : ℚ) (.leaf 2 10) (.leaf 2 11))))) (.leaf 0 18)) (.node 5 (1 / 2 : ℚ) (.node 1 (33 / 2 : ℚ) (.node 2 (2 : ℚ) (.node 0 (55 / 4 : ℚ) (.leaf 1 11) (.leaf 1 12)) (.node 2 (4 : ℚ) (.leaf 1 13) (.leaf 1 14))) (.node 1 (77 / 4 : ℚ) (.leaf 0 66) (.leaf 0 67))) (.leaf 0 19))) (.node 0 (77 / 4 : ℚ) (.node 1 (11 / 2 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 64) (.node 2 (2 : ℚ) (.leaf 1 20) (.leaf 1 21))) (.node 1 (11 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 65) (.node 2 (2 : ℚ) (.leaf 1 24) (.leaf 1 25))) (.node 1 (33 / 2 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 0 68) (.node 2 (2 : ℚ) (.node 1 (55 / 4 : ℚ) (.leaf 2 23) (.node 2 (1 : ℚ) (.node 3 (2 : ℚ) (.leaf 4 3) (.leaf 4 4)) (.leaf 3 9))) (.leaf 1 28))) (.node 5 (1 / 2 : ℚ) (.leaf 0 69) (.node 1 (77 / 4 : ℚ) (.node 2 (1 : ℚ) (.node 3 (2 : ℚ) (.node 5 (3 / 4 : ℚ) (.leaf 4 31) (.node 0 (143 / 8 : ℚ) (.leaf 5 23) (.leaf 5 24))) (.leaf 4 5)) (.node 2 (2 : ℚ) (.leaf 3 10) (.leaf 2 24))) (.leaf 1 31)))))) (.node 1 (11 / 2 : ℚ) (.node 2 (2 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 1 9) (.leaf 1 22)) (.node 5 (1 / 2 : ℚ) (.node 2 (4 : ℚ) (.leaf 2 12) (.leaf 2 13)) (.leaf 1 23))) (.node 1 (11 : ℚ) (.node 2 (2 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 1 10) (.leaf 1 26)) (.node 5 (1 / 2 : ℚ) (.node 2 (4 : ℚ) (.leaf 2 14) (.leaf 2 15)) (.leaf 1 27))) (.node 1 (33 / 2 : ℚ) (.node 2 (2 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 1 15) (.leaf 1 29)) (.node 5 (1 / 2 : ℚ) (.node 2 (4 : ℚ) (.leaf 2 16) (.leaf 2 17)) (.leaf 1 30))) (.node 2 (2 : ℚ) (.node 5 (1 / 2 : ℚ) (.leaf 1 16) (.node 0 (165 / 8 : ℚ) (.node 1 (77 / 4 : ℚ) (.leaf 3 11) (.leaf 3 13)) (.node 1 (77 / 4 : ℚ) (.leaf 3 12) (.node 2 (1 : ℚ) (.node 3 (2 : ℚ) (.node 5 (3 / 4 : ℚ) (.node 3 (1 : ℚ) (.leaf 7 0) (.leaf 7 1)) (.leaf 5 25)) (.leaf 4 32)) (.leaf 4 6))))) (.node 5 (1 / 2 : ℚ) (.node 2 (4 : ℚ) (.leaf 2 18) (.leaf 2 19)) (.leaf 1 32)))))))) (.node 5 (1 / 2 : ℚ) (.leaf 0 2) (.leaf 0 3)))))))

theorem tcTree_ok : tcCoverB tcTree tcDom = true := by decide +kernel

/-- **The RL-tc cells cover the domain**: every point with `G1, F1 ∈ [0, 22]`, `G2, F2 ≥ 0`, `x ∈ [4/5, 1]`,
`f ∈ [0, 1]` lies in the box of a certified cell. -/
theorem tc_cover (p : TcPt) (hp : tcDom.mem p) : ∃ C ∈ tcCellsAll, C.box.reg.mem p := by
  obtain ⟨j, i, hi, hm⟩ := tcCoverB_sound tcTree tcDom tcTree_ok p hp
  refine ⟨_, tcFileList_sub (j := j) ?_, hm⟩
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

end Census
end IIT
