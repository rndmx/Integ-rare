/-
Census, B1 LTBetaHi, RL-u certificate, part 2: cells, their vertices, the cell checker and its soundness.

A cell is a box `G1 ∈ [g1lo, g1hi] ⊆ [0, Q]`, `F1`, `G2`, `F2`, `w`, `x`, `f` (all over `Q`), with `V1 ≥ max(1, G1, F1)`
and `V2 ≥ max(G2, F2)`. Since `G1 ≤ 1`, the lower envelope of the first factor is `V1 = max(1, F1)`: its points are
the corners and, when `F1` crosses `1`, the points `F1 = 1`. Admissibility is monotone in `V1, V2`, so only the lower
envelope is checked.
-/
import IIT.Census.B1LTHiCertU

namespace IIT
namespace Census

/-- A cell box of the RL-u domain (all values over `Q`). -/
structure UBox where
  g1lo : ℕ
  g1hi : ℕ
  f1lo : ℕ
  f1hi : ℕ
  g2lo : ℕ
  g2hi : ℕ
  f2lo : ℕ
  f2hi : ℕ
  wlo : ℕ
  whi : ℕ
  xlo : ℕ
  xhi : ℕ
  flo : ℕ
  fhi : ℕ
  Q : ℕ

/-- A certified RL-u cell. -/
structure UCell where
  box : UBox
  ds : Bool
  Ts : ℕ
  Bn : ℕ
  Bd : ℕ
  dg : ℕ
  wits : List UWit

/-- The `F1` values of the first factor's envelope points. -/
def uF1Pts (f0 f1 Q : ℕ) : List ℕ := if f0 < Q ∧ Q < f1 then [f0, Q, f1] else [f0, f1]

/-- The vertices of a cell (integer coordinates over `Q`). -/
def uVertsN (b : UBox) : List RLUN :=
  [b.g1lo, b.g1hi].flatMap fun g1 =>
  (uF1Pts b.f1lo b.f1hi b.Q).flatMap fun f1 =>
  (tcFacPts b.g2lo (some b.g2hi) b.f2lo (some b.f2hi)).flatMap fun p2 =>
  [b.wlo, b.whi].flatMap fun w => [b.xlo, b.xhi].flatMap fun x => [b.flo, b.fhi].map fun f =>
    (⟨g1, f1, p2.1, p2.2, max b.Q f1, max p2.1 p2.2, w, x, f⟩ : RLUN)

/-- The rational vertices. -/
def uVerts (b : UBox) : List RLUD := (uVertsN b).map fun v => v.toQ b.Q

/-- The budget box (only the `x` range and `Q` matter for `tcBudB`). -/
def UBox.tcb (b : UBox) : TcBox := ⟨0, 0, 0, 0, 0, none, 0, none, b.xlo, b.xhi, b.flo, b.fhi, b.Q⟩

/-- **The RL-u cell checker** at `t = tn/td`. -/
def uCellOK (tn td : ℕ) (C : UCell) : Bool :=
  Nat.blt C.Ts 8 && Nat.blt 0 C.box.Q && Nat.blt 0 C.Bd && tcDesigB C.dg &&
  Nat.ble C.box.g1lo C.box.g1hi && Nat.ble C.box.g1hi C.box.Q && Nat.ble C.box.f1lo C.box.f1hi &&
  Nat.ble C.box.g2lo C.box.g2hi && Nat.ble C.box.f2lo C.box.f2hi && Nat.ble C.box.wlo C.box.whi &&
  Nat.ble C.box.xlo C.box.xhi && Nat.ble C.box.flo C.box.fhi &&
  tcBudB C.box.tcb ((C.Bn : ℚ) / C.Bd) &&
  tcAllZip (uVertB C.ds tn td C.Ts C.Bn C.Bd C.dg C.box.Q) (uVertsN C.box) C.wits

/-- **Soundness of the RL-u cell checker.** -/
theorem uCellOK_sound {tn td : ℕ} (htd : 0 < td) {C : UCell} (h : uCellOK tn td C = true) :
    (∀ v ∈ uVerts C.box, ∃ M Y : Fin 8 → Fin 3 → ℚ,
      rlUAdm C.ds v ((tn : ℚ) / td) C.Ts M Y ∧
        rlUEff v ((tn : ℚ) / td) ((C.Bn : ℚ) / C.Bd) (tcDesig C.dg) Y) ∧
    C.Ts < 8 ∧ 0 < C.box.Q ∧ C.box.g1lo ≤ C.box.g1hi ∧ C.box.g1hi ≤ C.box.Q ∧ C.box.f1lo ≤ C.box.f1hi ∧
    C.box.g2lo ≤ C.box.g2hi ∧ C.box.f2lo ≤ C.box.f2hi ∧ C.box.wlo ≤ C.box.whi ∧ C.box.xlo ≤ C.box.xhi ∧
    C.box.flo ≤ C.box.fhi ∧ TcBudget C.box.tcb ((C.Bn : ℚ) / C.Bd) := by
  simp only [uCellOK, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hTs, hQ⟩, hBd⟩, hdes⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, hbud⟩, hv⟩ := h
  have hdes' : ∀ R < 8, R ≠ 0 → tcDesig C.dg R < 3 := by
    intro R hR hR0
    have := nAll8_sound hdes R hR
    simp only [Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at this
    exact this.resolve_left hR0
  refine ⟨fun v hv' => ?_, hTs, hQ, h1, h2, h3, h4, h5, h6, h7, h8, tcBudB_sound hbud⟩
  obtain ⟨vn, hvn, rfl⟩ := List.mem_map.1 hv'
  obtain ⟨w, -, hw⟩ := tcAllZip_sound hv vn hvn
  exact ⟨_, _, uVertB_sound htd hTs hQ hBd hdes' hw⟩

end Census
end IIT
