/-
Census, B1 LTBetaHi, RL-tc certificate (W8 §8.2), part 1c: all 518 cells of `w8_ucells_tcB.json`.

The cells are kernel-checked in the data files `B1LTHiCertTcD00` … `B1LTHiCertTcD13` (26 940 vertex witnesses,
537 ray witnesses, single level `t = 1/80`). `tcCellsAll_sound` is the per-cell certificate: at every vertex of
the cell's box (lower envelope `V = max(G, F)`, corners in `x`, `f`) an RL-tc table with the effect conditions,
at every ray a homogeneous table, and the real budget `TcBudget`.
-/
import IIT.Census.B1LTHiCertTcD00
import IIT.Census.B1LTHiCertTcD01
import IIT.Census.B1LTHiCertTcD02
import IIT.Census.B1LTHiCertTcD03
import IIT.Census.B1LTHiCertTcD04
import IIT.Census.B1LTHiCertTcD05
import IIT.Census.B1LTHiCertTcD06
import IIT.Census.B1LTHiCertTcD07
import IIT.Census.B1LTHiCertTcD08
import IIT.Census.B1LTHiCertTcD09
import IIT.Census.B1LTHiCertTcD10
import IIT.Census.B1LTHiCertTcD11
import IIT.Census.B1LTHiCertTcD12
import IIT.Census.B1LTHiCertTcD13

namespace IIT
namespace Census

/-- All 518 certified RL-tc cells. -/
def tcCellsAll : List TcCell :=
  tcCellsD00 ++ tcCellsD01 ++ tcCellsD02 ++ tcCellsD03 ++ tcCellsD04 ++ tcCellsD05 ++ tcCellsD06 ++
    tcCellsD07 ++ tcCellsD08 ++ tcCellsD09 ++ tcCellsD10 ++ tcCellsD11 ++ tcCellsD12 ++ tcCellsD13

theorem tcCellsAll_ok : tcCellsAll.all (tcCellOK 1 80) = true := by
  simp only [tcCellsAll, List.all_append, tcCellsD00_ok, tcCellsD01_ok, tcCellsD02_ok, tcCellsD03_ok,
    tcCellsD04_ok, tcCellsD05_ok, tcCellsD06_ok, tcCellsD07_ok, tcCellsD08_ok, tcCellsD09_ok, tcCellsD10_ok,
    tcCellsD11_ok, tcCellsD12_ok, tcCellsD13_ok, Bool.and_self]

/-- **The RL-tc cell certificate** (W8 §8.2, at `t = 1/80`): for every certified cell, every vertex of its box
carries an RL-tc table `(M, Y)` that is cause-admissible (`rlTcAdm`, value `c(5/3 - t)`, gap `c t/20`,
pattern margin `1/20`, `c = x`) and satisfies the effect conditions of Lemma EFG (`rlTcEff`: (E2) with slack
`t/100`, designated budget `≤ B - 1/500`); every ray carries a homogeneous table; and the budget `B` satisfies
the real bound `B ≤ 3 log 2 (e_lo - e_hi(c))` for all seven competitors (`TcBudget`). -/
theorem tcCellsAll_sound {C : TcCell} (hC : C ∈ tcCellsAll) :
    (∀ v ∈ tcVerts C.box, ∃ M Y : Fin 8 → Fin 3 → ℚ,
      rlTcAdm v (1 / 80) C.Ts M Y ∧ rlTcEff v (1 / 80) ((C.Bn : ℚ) / C.Bd) (tcDesig C.dg) Y) ∧
    (∀ r ∈ tcRays C.box, ∃ M, rlRay r C.Ts M) ∧ C.Ts < 8 ∧ 0 < C.box.Q ∧
      TcBudget C.box ((C.Bn : ℚ) / C.Bd) := by
  have h := tcCellsAll_ok
  rw [List.all_eq_true] at h
  have hs := tcCellOK_sound (tn := 1) (td := 80) (by norm_num) (h C hC)
  have e : ((1 : ℕ) : ℚ) / ((80 : ℕ) : ℚ) = 1 / 80 := by norm_num
  rw [e] at hs
  exact hs

theorem tcCellsAll_length : tcCellsAll.length = 518 := by
  simp only [tcCellsAll, List.length_append, tcCellsD00, tcCellsD01, tcCellsD02, tcCellsD03, tcCellsD04,
    tcCellsD05, tcCellsD06, tcCellsD07, tcCellsD08, tcCellsD09, tcCellsD10, tcCellsD11, tcCellsD12, tcCellsD13,
    List.length_cons, List.length_nil]

end Census
end IIT
