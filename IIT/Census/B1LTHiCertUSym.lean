/-
Census, B1 LTBetaHi, RL-u certificate, part 6: **`rlu_sym`** (W8 §8.3 restricted to the W11 sub-domains).

Every RL-u datum with `D_u = ∅` and `x ≥ 9/16`, or `D_u = S` and `x ≥ 7/8`, over the bounded domain
(`G1 ∈ [4/5, 1]`, `F1 ∈ [0, 2]`, `G2, F2, w, f ∈ [0, 1]`, `V1 ≥ max(1, F1)`, `V2 ≥ max(G2, F2)`) lies in a certified
cell, which supplies a target `Ts < 8`, an RL-u table at `t = 1/80` (cause admissible at level `c = G1`, effect
conditions of Lemma EFG with slack `t/100`, designated budget `≤ B - 1/500`), and the real budget bound.
-/
import IIT.Census.B1LTHiCertUAll
import IIT.Census.B1LTHiCertUDecomp

namespace IIT
namespace Census

/-- **RL-u on the W11 sub-domains.** -/
theorem rlu_sym (ds : Bool) (d : RLUD) (hG1 : 4 / 5 ≤ d.G1) (hG1' : d.G1 ≤ 1) (hF1 : 0 ≤ d.F1)
    (hF1' : d.F1 ≤ 2) (hG2 : 0 ≤ d.G2) (hG2' : d.G2 ≤ 1) (hF2 : 0 ≤ d.F2) (hF2' : d.F2 ≤ 1)
    (hw : 0 ≤ d.w) (hw' : d.w ≤ 1) (hx : (if ds then 7 / 8 else 9 / 16) ≤ d.x) (hx' : d.x ≤ 1) (hf : 0 ≤ d.f)
    (hf' : d.f ≤ 1) (hV1 : max 1 d.F1 ≤ d.V1) (hV2 : max d.G2 d.F2 ≤ d.V2) :
    ∃ C ∈ uCellsAll, C.ds = ds ∧ C.Ts < 8 ∧
      UGood ds (1 / 80) ((C.Bn : ℚ) / C.Bd) C.Ts (tcDesig C.dg) d ∧
      TcBudget C.box.tcb ((C.Bn : ℚ) / C.Bd) ∧
      (C.box.xlo : ℚ) / C.box.Q ≤ d.x ∧ d.x ≤ (C.box.xhi : ℚ) / C.box.Q := by
  have hp : (uDom ds).mem ⟨d.G1, d.F1, d.G2, d.F2, d.w, d.x, d.f⟩ := by
    intro c hc
    interval_cases c <;> simp [uDom, UPt.get] <;> cases ds <;> simp_all <;> constructor <;> linarith
  obtain ⟨C, hC, hm, hds⟩ := u_cover ds _ hp
  have hs := uCellsAll_sound hC
  have hok : uCellOK 1 80 C = true := by
    have h := uCellsAll_ok; rw [List.all_eq_true] at h; exact h C hC
  have g := fun c (hc : c < 7) => hm c hc
  simp only [UBox.reg, UPt.get] at g
  have g0 := g 0 (by norm_num); have g1 := g 1 (by norm_num); have g2 := g 2 (by norm_num)
  have g3 := g 3 (by norm_num); have g4 := g 4 (by norm_num); have g5 := g 5 (by norm_num)
  have g6 := g 6 (by norm_num)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at g0 g1 g2 g3 g4 g5 g6
  have hgood := uCell_good (tn := 1) (td := 80) (by norm_num) hok d g0 g1 g2 g3 g4 g5 g6 hV1 hV2
  have e : ((1 : ℕ) : ℚ) / ((80 : ℕ) : ℚ) = 1 / 80 := by norm_num
  rw [e, hds] at hgood
  exact ⟨C, hC, hds, hs.2.1, hgood, hs.2.2.2.2.2.2.2.2.2.2.2, g5⟩

end Census
end IIT
