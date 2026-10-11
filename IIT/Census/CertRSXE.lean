/-
Census, Lemma RS: the kernel-checked certificate of the 61 regime-X EFFECT cells (data `CertRSDataXE`).

Same check `rsCellOK` as the cause cells, read with `lu` := the row-`tc` multiplier `p` (`rsEx p = 2 ∫_{1/2}^1 y^p`)
and `P` := `4 l_u` (row `s`).  The effect rate is `-log(2 · Js · Jt) - (p + l_u) x0`, `Js = 2 cellIq`.
-/
import IIT.Census.CertRSX
import IIT.Census.CertRSDataXE

namespace IIT
namespace Census

/-- **The effect certificate**: every effect cell passes. -/
theorem rsCellsE_ok : rsCellsE.all rsCellOK = true := by decide +kernel

/-- A certified effect cell covers an original effect cell: `v⁴ ≤ max(1/2, m_lo)`, larger or inactive cap. -/
def rsLinkE (C : RSCell) (c : ℚ × ℚ) : Bool :=
  decide (C.v ^ 4 ≤ max (1 / 2) c.1) && (decide (c.2 ≤ C.w ^ 4) || decide (C.w = 1)) &&
    decide ((1 : ℚ) / 2 ≤ c.2)

/-- **Every original effect cell is covered by a certified effect cell.** -/
theorem rsLinkE_all : cellsXEffectData.all (fun c => rsCellsE.any (fun C => rsLinkE C c)) = true := by
  decide +kernel

/-- Multiplier ranges of the certified effect cells. -/
theorem rsBoundsE : rsCellsE.all (fun C => decide (C.lam ≤ 17) && decide (C.lu ≤ 3) && decide (C.P ≤ 30)) = true := by
  decide +kernel

end Census
end IIT
