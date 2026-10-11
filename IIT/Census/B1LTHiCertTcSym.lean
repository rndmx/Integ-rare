/-
Census, B1 LTBetaHi, RL-tc certificate (W8 §7.2, §8.2), part 1f: **Theorem RL-tc (symmetric data, `t = 1/80`)**.

For every symmetric RL-tc datum with A-rest weight `≤ 22` (`G1, F1 ∈ [0, 22]`), any B-block (`G2, F2 ≥ 0`), tc's
entries `x ∈ [4/5, 1]`, `f ∈ [0, 1]`, and `V1 ≥ max(G1, F1)`, `V2 ≥ max(G2, F2)`, some certified cell `C` contains
it and supplies a target `Ts`, an RL-tc table `(M, Y)` (cause: value `x(5/3 - t)`, gap `x t/20`, pattern margin
`1/20`, profile `lp3CStar`; effect: (E2) slack `t/100`, designated budget `≤ B - 1/500`) and a budget `B` with
`B ≤ 3 log 2 (e_lo - e_hi(c))` for every competitor `c` (`TcBudget`, over the cell's `x`-range widened by `1/1000`).
Cover (`tc_cover`) + per-cell decomposition (`tcCell_good`) + the kernel-checked cells (`tcCellsAll_ok`).
-/
import IIT.Census.B1LTHiCertTcCover
import IIT.Census.B1LTHiCertTcDecomp

namespace IIT
namespace Census

/-- **Theorem RL-tc** (W8 §8.2, `t = 1/80`, symmetric data). -/
theorem rltc_sym (d : RLTcD) (hG1 : 0 ≤ d.G1) (hG1' : d.G1 ≤ 22) (hF1 : 0 ≤ d.F1) (hF1' : d.F1 ≤ 22)
    (hG2 : 0 ≤ d.G2) (hF2 : 0 ≤ d.F2) (hx : 4 / 5 ≤ d.x) (hx' : d.x ≤ 1) (hf : 0 ≤ d.f) (hf' : d.f ≤ 1)
    (hV1 : max d.G1 d.F1 ≤ d.V1) (hV2 : max d.G2 d.F2 ≤ d.V2) :
    ∃ C ∈ tcCellsAll, C.box.reg.mem ⟨d.G1, d.F1, d.G2, d.F2, d.x, d.f⟩ ∧
      TcGood (1 / 80) ((C.Bn : ℚ) / C.Bd) C.Ts (tcDesig C.dg) d ∧ C.Ts < 8 ∧
      TcBudget C.box ((C.Bn : ℚ) / C.Bd) := by
  have hdom : tcDom.mem ⟨d.G1, d.F1, d.G2, d.F2, d.x, d.f⟩ := by
    intro c hc
    interval_cases c <;> simp only [tcDom, TcReg.lo, TcReg.hi, TcPt.get] <;>
      refine ⟨by assumption, fun h hh => ?_⟩ <;> simp only [Option.some.injEq, reduceCtorEq] at hh <;>
      subst hh <;> assumption
  obtain ⟨C, hC, hm⟩ := tc_cover _ hdom
  have hok : tcCellOK 1 80 C = true := (List.all_eq_true.1 tcCellsAll_ok) C hC
  obtain ⟨-, -, hTs, -, hb⟩ := tcCellOK_sound (by norm_num) hok
  refine ⟨C, hC, hm, ?_, hTs, hb⟩
  have m0 := hm 0 (by norm_num)
  have m1 := hm 1 (by norm_num)
  have m2 := hm 2 (by norm_num)
  have m3 := hm 3 (by norm_num)
  have m4 := hm 4 (by norm_num)
  have m5 := hm 5 (by norm_num)
  simp only [TcBox.reg, TcReg.lo, TcReg.hi, TcPt.get] at m0 m1 m2 m3 m4 m5
  have := tcCell_good (tn := 1) (td := 80) (by norm_num) hok d
    ⟨m0.1, m0.2 _ rfl⟩ ⟨m1.1, m1.2 _ rfl⟩
    ⟨m2.1, fun h hh => m2.2 _ (by rw [hh]; rfl)⟩ ⟨m3.1, fun h hh => m3.2 _ (by rw [hh]; rfl)⟩
    ⟨m4.1, m4.2 _ rfl⟩ ⟨m5.1, m5.2 _ rfl⟩ hV1 hV2
  have e : ((1 : ℕ) : ℚ) / ((80 : ℕ) : ℚ) = 1 / 80 := by norm_num
  rwa [e] at this

end Census
end IIT
