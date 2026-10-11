/-
Census, B1 LTBetaHi, RL-tc part 2a: **the real windowed RL-tc table** (W8 §8.1, §9; analogue of `rl_real_window`).

Real per-unit data: the rest blocks `dR : RLDR` (the heavy rows other than `tc`, weights `P(r)/P(tc)`), tc's shared
entries `x i = y_{tc, e i}` and `f i = y_{tc^i, e i}`, each with spread `≤ ω` over the three units. The datum is
floored to the grid `ℤ/n` (`5 ∣ n`) and the componentwise minimum is fed to `rltc_sym` (`t = 1/80`). The certified
rational table `(M0, Y0)` is moved to the real data by `M := tcEnt(x, f, Y) + max(M0 - tcEnt0, lo)`, `Y := Y0`
(`|M - M0| ≤ 2ω'`, `ω' = ω + 1/n`).

* `TcTab`, `tcEntR` (tc's real entry), `tcEhiR` (competitor bound), `RLTcWin` (the conclusion: the cause box of the
  rest, `Y ∈ [0, 1]`, (V), (G), (P) weakened by `36·2ω'`, `6·2ω'`, `6·2ω'`, (E2) `Y R i ≤ c0 - 1/8000`, the designated
  budget `≤ B - 1/500 + 7ω'`, and the budget `B ≤ 3 log 2 (Lx³ - e_hi(c))` with `Lx ≤ x i ≤ Hx`).
* **`rltc_real_window`**: every admissible real datum (rest A-weight `≤ 22`, `x i ∈ [4/5, 1]`, `f i ∈ [0, 1]`,
  `ω + 1/n ≤ 1/1000`) has a table with `RLTcWin`.
-/
import IIT.Census.B1LTHiCertTcSym
import IIT.Census.B1LTHiT6b

namespace IIT
namespace Census

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- An RL-tc table on real data: target, merged table, tc's private entries, level `c0`, budget `B`, designations,
and the `x`-range `[Lx, Hx]` of the budget. -/
structure TcTab where
  Ts : ℕ
  M : Fin 8 → Fin 3 → ℝ
  Y : Fin 8 → Fin 3 → ℝ
  c0 : ℝ
  B : ℝ
  dg : Fin 8 → Fin 3
  Lx : ℝ
  Hx : ℝ

instance : Nonempty TcTab := ⟨⟨0, 0, 0, 0, 0, fun _ => 0, 0, 0⟩⟩

/-- tc's real entry at pattern `u`, column `i`: `x i` (shared), `f i` (own flip, shared), `Y u i` (private). -/
noncomputable def tcEntR (x f : Fin 3 → ℝ) (Y : Fin 8 → Fin 3 → ℝ) (u : Fin 8) (i : Fin 3) : ℝ :=
  if (u : ℕ) = 0 then x i else if (u : ℕ) = rlBit i then f i else Y u i

/-- Upper bound of a competitor's effect probability (bit `i` of `c` set = unit `i` OFF). -/
noncomputable def tcEhiR (Lx Hx : ℝ) (c : ℕ) : ℝ :=
  (if c.testBit 0 then 1 - Lx else Hx) * (if c.testBit 1 then 1 - Lx else Hx) *
    (if c.testBit 2 then 1 - Lx else Hx)

/-- **The windowed RL-tc conclusion** (`t = 1/80`) for real data `(dR, x, f)` with window loss `ω'`. -/
def RLTcWin (dR : RLDR) (x f : Fin 3 → ℝ) (ω' : ℝ) (T : TcTab) : Prop :=
  T.Ts < 8 ∧ 4 / 5 ≤ T.c0 ∧ (∀ i, T.c0 ≤ x i) ∧ (∀ i, x i ≤ T.c0 + ω') ∧
  (∀ (u : Fin 8) (i : Fin 3), rlLoR dR u i ≤ T.M u i - tcEntR x f T.Y u i ∧
    T.M u i - tcEntR x f T.Y u i ≤ rlLoR dR u i + rlWdR dR u i) ∧
  (∀ (u : Fin 8) (i : Fin 3), ¬((u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ)) → 0 ≤ T.Y u i ∧ T.Y u i ≤ 1) ∧
  8 * T.c0 * (5 / 3 - 1 / 80) - 36 * (2 * ω') ≤ rlV8R lp3CStar T.Ts T.M ∧
  (∀ C ∈ lp3Profiles, C ≠ lp3CStar →
    T.c0 * (1 / 80) / 20 - 6 * (2 * ω') ≤
      rlV8R C T.Ts T.M / (8 * (cd_cc 3 C : ℝ)) - rlV8R lp3CStar T.Ts T.M / 40) ∧
  (∀ u < 8, u ≠ T.Ts → 1 / 20 - 6 * (2 * ω') ≤ rlPSR T.M T.Ts - rlPSR T.M u) ∧
  (∀ (R : Fin 8) (i : Fin 3), (R : ℕ) ≠ 0 → (R : ℕ).testBit i = false → T.Y R i ≤ T.c0 - 1 / 8000) ∧
  ∑ R ∈ (univ : Finset (Fin 8)).erase 0, tcEntR x f T.Y R (T.dg R) ≤ T.B - 1 / 500 + 7 * ω' ∧
  0 ≤ T.Lx ∧ T.Hx ≤ 1 ∧ (∀ i, T.Lx ≤ x i ∧ x i ≤ T.Hx) ∧
  ∀ c : ℕ, 0 < c → c < 8 → T.B ≤ 3 * Real.log 2 * (T.Lx ^ 3 - tcEhiR T.Lx T.Hx c)

lemma tcEhi_cast (b : TcBox) (c : ℕ) :
    ((tcEhi b c : ℚ) : ℝ) = tcEhiR ((tcLx b : ℚ) : ℝ) ((tcHx b : ℚ) : ℝ) c := by
  unfold tcEhi tcEhiR
  push_cast
  split_ifs <;> push_cast <;> ring

/-- The floored symmetric RL-tc datum of real windowed data. -/
noncomputable def rlTcFlD (n : ℕ) (dR : RLDR) (x f : Fin 3 → ℝ) : RLTcD :=
  ⟨rlFl n (rlMin3R dR.G1), rlFl n (rlMin3R dR.F1), rlFl n (rlMin3R dR.G2), rlFl n (rlMin3R dR.F2),
    rlFl n dR.V1, rlFl n dR.V2, rlFl n (rlMin3R x), rlFl n (rlMin3R f)⟩

lemma rlTcFlD_rest (n : ℕ) (dR : RLDR) (x f : Fin 3 → ℝ) : (rlTcFlD n dR x f).rest = rlFlD n dR := rfl

lemma rlFl_nonneg {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) : (0 : ℚ) ≤ rlFl n x := by
  have := rlFl_ge_int hn 0 (x := x) (by simpa using hx); simpa using this

lemma rlFl_le_of {n : ℕ} (hn : 0 < n) {x : ℝ} {q : ℚ} (h : x ≤ (q : ℝ)) : rlFl n x ≤ q := by
  have h1 := rlFl_le hn x
  have : ((rlFl n x : ℚ) : ℝ) ≤ (q : ℝ) := h1.trans h
  exact_mod_cast this

/-- `4/5 ≤ ⌊4/5⌋_n` when `5 ∣ n`. -/
lemma rlFl_45 {n : ℕ} (hn : 0 < n) (h5 : 5 ∣ n) {x : ℝ} (hx : 4 / 5 ≤ x) : (4 : ℚ) / 5 ≤ rlFl n x := by
  obtain ⟨m, hm⟩ := h5
  have hm0 : 0 < m := by omega
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hmQ : (m : ℚ) ≠ 0 := by positivity
  have e1 : ((4 * m : ℤ) : ℝ) / n = 4 / 5 := by
    rw [hm]; push_cast; field_simp
  have e2 : ((4 * m : ℤ) : ℚ) / n = 4 / 5 := by
    rw [hm]; push_cast; field_simp
  have := rlFl_ge_int hn (4 * m) (x := x) (by rw [e1]; exact hx)
  rw [e2] at this; exact this

lemma tcEntR_close {x f : Fin 3 → ℝ} {Y : Fin 8 → Fin 3 → ℝ} {x0 f0 : ℝ} {ω : ℝ} (hω : 0 ≤ ω)
    (hx : ∀ i, x0 ≤ x i ∧ x i - x0 ≤ ω) (hf : ∀ i, f0 ≤ f i ∧ f i - f0 ≤ ω) (u : Fin 8) (i : Fin 3) :
    0 ≤ tcEntR x f Y u i - tcEntR (fun _ => x0) (fun _ => f0) Y u i ∧
      tcEntR x f Y u i - tcEntR (fun _ => x0) (fun _ => f0) Y u i ≤ ω := by
  unfold tcEntR
  split_ifs
  · exact ⟨by linarith [(hx i).1], (hx i).2⟩
  · exact ⟨by linarith [(hf i).1], (hf i).2⟩
  · exact ⟨by simp, by simpa using hω⟩

/-- The rational tc entry, cast. -/
lemma rlTcEnt_cast (d : RLTcD) (Y : Fin 8 → Fin 3 → ℚ) (u : Fin 8) (i : Fin 3) :
    ((rlTcEnt d Y u i : ℚ) : ℝ) = tcEntR (fun _ => (d.x : ℝ)) (fun _ => (d.f : ℝ)) (fun u i => (Y u i : ℝ)) u i := by
  unfold rlTcEnt tcEntR
  have hM : rlM Y u i = Y u i := by simp [rlM, Nat.mod_eq_of_lt u.2, Nat.mod_eq_of_lt i.2]
  split_ifs <;> simp [hM]

/-- Sums over the nonzero patterns. -/
lemma sum_erase0_fin8 (g : Fin 8 → ℝ) :
    ∑ R ∈ (univ : Finset (Fin 8)).erase 0, g R = g 1 + g 2 + g 3 + g 4 + g 5 + g 6 + g 7 := by
  rw [Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_eight]
  ring

/-- **RL-tc on real windowed data** (`t = 1/80`). -/
theorem rltc_real_window (dR : RLDR) (x f : Fin 3 → ℝ) {n : ℕ} (hn : 0 < n) (h5 : 5 ∣ n) {ω : ℝ} (hω : 0 ≤ ω)
    (hw : dR.win ω) (hxw : ∀ i, x i - rlMin3R x ≤ ω) (hfw : ∀ i, f i - rlMin3R f ≤ ω)
    (hω1 : ω + 1 / n ≤ 1 / 1000)
    (hG1 : ∀ i, 0 ≤ dR.G1 i) (hG1V : ∀ i, dR.G1 i ≤ dR.V1) (hF1 : ∀ i, 0 ≤ dR.F1 i)
    (hF1V : ∀ i, dR.F1 i ≤ dR.V1) (hV22 : dR.V1 ≤ 22) (hG2 : ∀ i, 0 ≤ dR.G2 i) (hF2 : ∀ i, 0 ≤ dR.F2 i)
    (hG2V : ∀ i, dR.G2 i ≤ dR.V2) (hF2V : ∀ i, dR.F2 i ≤ dR.V2)
    (hx0 : ∀ i, 4 / 5 ≤ x i) (hx1 : ∀ i, x i ≤ 1) (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) :
    ∃ T : TcTab, RLTcWin dR x f (ω + 1 / n) T := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) ≤ 1 / n := by positivity
  set ω' := ω + 1 / n with hω'
  have hω'0 : 0 ≤ ω' := by positivity
  set d0 := rlTcFlD n dR x f with hd0
  -- the hypotheses of `rltc_sym`
  have hmin0 : ∀ g : Fin 3 → ℝ, (∀ i, 0 ≤ g i) → 0 ≤ rlMin3R g := fun g h => le_rlMin3R h
  have q1 : 0 ≤ d0.G1 := rlFl_nonneg hn (hmin0 _ hG1)
  have q2 : d0.G1 ≤ 22 := rlFl_le_of hn (by push_cast; linarith [rlMin3R_le dR.G1 0, hG1V 0])
  have q3 : 0 ≤ d0.F1 := rlFl_nonneg hn (hmin0 _ hF1)
  have q4 : d0.F1 ≤ 22 := rlFl_le_of hn (by push_cast; linarith [rlMin3R_le dR.F1 0, hF1V 0])
  have q5 : 0 ≤ d0.G2 := rlFl_nonneg hn (hmin0 _ hG2)
  have q6 : 0 ≤ d0.F2 := rlFl_nonneg hn (hmin0 _ hF2)
  have q7 : 4 / 5 ≤ d0.x := rlFl_45 hn h5 (le_rlMin3R hx0)
  have q8 : d0.x ≤ 1 := rlFl_le_of hn (by push_cast; linarith [rlMin3R_le x 0, hx1 0])
  have q9 : 0 ≤ d0.f := rlFl_nonneg hn (hmin0 _ hf0)
  have q10 : d0.f ≤ 1 := rlFl_le_of hn (by push_cast; linarith [rlMin3R_le f 0, hf1 0])
  have q11 : max d0.G1 d0.F1 ≤ d0.V1 :=
    max_le (rlFl_mono ((rlMin3R_le _ 0).trans (hG1V 0))) (rlFl_mono ((rlMin3R_le _ 0).trans (hF1V 0)))
  have q12 : max d0.G2 d0.F2 ≤ d0.V2 :=
    max_le (rlFl_mono ((rlMin3R_le _ 0).trans (hG2V 0))) (rlFl_mono ((rlMin3R_le _ 0).trans (hF2V 0)))
  obtain ⟨C, -, hm, ⟨M0, Y0, hadm, heff⟩, hTs, hbud⟩ :=
    rltc_sym d0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  -- window facts
  set x0 : ℝ := ((d0.x : ℚ) : ℝ) with hx0def
  set f0 : ℝ := ((d0.f : ℚ) : ℝ) with hf0def
  have hxc : ∀ i, x0 ≤ x i ∧ x i - x0 ≤ ω' := fun i => rlFl_min_close hn hxw i
  have hfc : ∀ i, f0 ≤ f i ∧ f i - f0 ≤ ω' := fun i => rlFl_min_close hn hfw i
  have hc45 : (4 : ℝ) / 5 ≤ x0 := by
    have h : (((4 : ℚ) / 5 : ℚ) : ℝ) ≤ x0 := by rw [hx0def]; exact_mod_cast q7
    norm_num at h; exact h
  -- the real table
  set Y : Fin 8 → Fin 3 → ℝ := fun u i => (Y0 u i : ℝ) with hYdef
  set E0 : Fin 8 → Fin 3 → ℝ := fun u i => tcEntR (fun _ => x0) (fun _ => f0) Y u i with hE0def
  have hE0c : ∀ u i, E0 u i = ((rlTcEnt d0 Y0 u i : ℚ) : ℝ) := fun u i => (rlTcEnt_cast d0 Y0 u i).symm
  set M : Fin 8 → Fin 3 → ℝ := fun u i => tcEntR x f Y u i + max ((M0 u i : ℝ) - E0 u i) (rlLoR dR u i)
    with hMdef
  have hM0v : ∀ (u : Fin 8) (i : Fin 3), rlM M0 u i = M0 u i := by
    intro u i; simp [rlM, Nat.mod_eq_of_lt u.2, Nat.mod_eq_of_lt i.2]
  have hbox0 : ∀ (u : Fin 8) (i : Fin 3),
      ((rlLo d0.rest u i : ℚ) : ℝ) ≤ (M0 u i : ℝ) - E0 u i ∧
        (M0 u i : ℝ) - E0 u i ≤ ((rlLo d0.rest u i : ℚ) : ℝ) + ((rlWd d0.rest u i : ℚ) : ℝ) := by
    intro u i
    have h := hadm.1 u u.2 i i.2
    rw [hM0v] at h
    rw [hE0c]
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  have hwdR : ∀ u i, 0 ≤ rlWdR dR u i := by
    intro u i; unfold rlWdR; split_ifs <;> linarith [(hG2 0).trans (hG2V 0), (hG1 0).trans (hG1V 0)]
  have hclose : ∀ u i, |M u i - (fun u i => (M0 u i : ℝ)) u i| ≤ 2 * ω' := by
    intro u i
    simp only [hMdef]
    have hb := hbox0 u i
    have hl := rlLo_flD_le hn dR hω hw u i
    rw [rlTcFlD_rest] at hb
    have he := tcEntR_close (Y := Y) hω'0 hxc hfc u i
    have hm1 := le_max_left ((M0 u i : ℝ) - E0 u i) (rlLoR dR u i)
    have hm2 : max ((M0 u i : ℝ) - E0 u i) (rlLoR dR u i) ≤ (M0 u i : ℝ) - E0 u i + ω' :=
      max_le (by linarith) (by linarith [hb.1, hl.2])
    have hE : E0 u i = tcEntR (fun _ => x0) (fun _ => f0) Y u i := rfl
    rw [abs_le]; constructor <;> linarith [he.1, he.2]
  have hstar : lp3CStar ∈ lp3Profiles := by decide +kernel
  have ht : ((1 : ℚ) / 80 : ℚ) = 1 / 80 := rfl
  -- the budget range
  set b := C.box with hb
  have m4 := hm 4 (by norm_num)
  simp only [TcBox.reg, TcReg.lo, TcReg.hi, TcPt.get] at m4
  have hxlo : ((b.xlo : ℚ) / b.Q : ℚ) ≤ d0.x := m4.1
  have hxhi : d0.x ≤ ((b.xhi : ℚ) / b.Q : ℚ) := m4.2 _ rfl
  set Lx : ℝ := ((tcLx b : ℚ) : ℝ) with hLx
  set Hx : ℝ := ((tcHx b : ℚ) : ℝ) with hHx
  have hLx0 : 0 ≤ Lx := by rw [hLx]; exact_mod_cast le_max_left _ _
  have hHx1 : Hx ≤ 1 := by rw [hHx]; exact_mod_cast min_le_left _ _
  have hxr : ∀ i, Lx ≤ x i ∧ x i ≤ Hx := by
    intro i
    have h1 := hxc i
    constructor
    · rw [hLx]
      unfold tcLx
      push_cast
      refine max_le (by linarith [hx0 i]) ?_
      have : (((b.xlo : ℚ) / b.Q : ℚ) : ℝ) ≤ x0 := by rw [hx0def]; exact_mod_cast hxlo
      push_cast at this
      linarith
    · rw [hHx]
      unfold tcHx
      push_cast
      refine le_min (hx1 i) ?_
      have : x0 ≤ (((b.xhi : ℚ) / b.Q : ℚ) : ℝ) := by rw [hx0def]; exact_mod_cast hxhi
      push_cast at this
      linarith
  -- the designations
  have hdes := heff.2.1
  set dg : Fin 8 → Fin 3 := fun R => ⟨tcDesig C.dg R % 3, Nat.mod_lt _ (by norm_num)⟩ with hdg
  set B : ℝ := (((C.Bn : ℚ) / C.Bd : ℚ) : ℝ) with hBdef
  refine ⟨⟨C.Ts, M, Y, x0, B, dg, Lx, Hx⟩, hTs, hc45, fun i => (hxc i).1, fun i => by linarith [(hxc i).2],
    fun u i => ?_, fun u i hv => ?_, ?_, fun C' hC' hne => ?_, fun u hu hne => ?_, fun R i hR hbit => ?_, ?_,
    hLx0, hHx1, hxr, fun c hc0 hc8 => ?_⟩
  · -- the box
    simp only
    have hb := hbox0 u i
    have hl := rlLo_flD_le hn dR hω hw u i
    have hwd := rlWd_flD_le hn dR u i
    rw [rlTcFlD_rest] at hb
    have e1 : M u i - tcEntR x f Y u i = max ((M0 u i : ℝ) - E0 u i) (rlLoR dR u i) := by
      simp only [hMdef]; ring
    rw [e1]
    exact ⟨le_max_right _ _, max_le (by linarith [hb.2, hl.1]) (by linarith [hwdR u i])⟩
  · -- `Y ∈ [0, 1]`
    simp only [hYdef]
    have h := hadm.2.1 u u.2 i i.2 (fun h => hv (Or.inl h)) (fun h => hv (Or.inr (by simpa [rlBit] using h)))
    have e : rlM Y0 u i = Y0 u i := by simp [rlM, Nat.mod_eq_of_lt u.2, Nat.mod_eq_of_lt i.2]
    rw [e] at h
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  · -- (V)
    simp only
    have hp := abs_le.1 (rlV8R_pert hstar C.Ts hclose)
    rw [rlV8R_cast] at hp
    have hv : 8 * x0 * (5 / 3 - 1 / 80) ≤ ((rlV8 lp3CStar C.Ts M0 : ℚ) : ℝ) := by
      have h : ((8 * d0.x * (5 / 3 - 1 / 80) : ℚ) : ℝ) ≤ ((rlV8 lp3CStar C.Ts M0 : ℚ) : ℝ) := by
        exact_mod_cast hadm.2.2.1
      push_cast at h; rw [hx0def]; linarith
    linarith [hp.1]
  · -- (G)
    simp only
    have hcc : (1 : ℝ) ≤ (cd_cc 3 C' : ℝ) := by
      have := profiles3_cc_pos C' (by simpa [profiles3] using hC'); exact_mod_cast this
    have hg : 1 / 20 * x0 * (1 / 80) ≤ ((rlV8 C' C.Ts M0 : ℚ) : ℝ) / (8 * (cd_cc 3 C' : ℝ)) -
        ((rlV8 lp3CStar C.Ts M0 : ℚ) : ℝ) / 40 := by
      have h : ((1 / 20 * d0.x * (1 / 80) : ℚ) : ℝ) ≤
          ((rlV8 C' C.Ts M0 / (8 * (cd_cc 3 C' : ℚ)) - rlV8 lp3CStar C.Ts M0 / 40 : ℚ) : ℝ) := by
        exact_mod_cast hadm.2.2.2.1 C' hC' hne
      push_cast at h; rw [hx0def]; linarith
    have pc := rlV8R_pert hC' C.Ts hclose
    rw [rlV8R_cast] at pc
    have ps := rlV8R_pert hstar C.Ts hclose
    rw [rlV8R_cast] at ps
    have e1 : |rlV8R C' C.Ts M / (8 * (cd_cc 3 C' : ℝ)) - ((rlV8 C' C.Ts M0 : ℚ) : ℝ) / (8 * (cd_cc 3 C' : ℝ))| ≤
        36 * (2 * ω') / 8 := by
      have hc8 : (0 : ℝ) < 8 * (cd_cc 3 C' : ℝ) := by linarith
      rw [← sub_div, abs_div, abs_of_pos hc8, div_le_iff₀ hc8]
      nlinarith
    have e2 : |rlV8R lp3CStar C.Ts M / 40 - ((rlV8 lp3CStar C.Ts M0 : ℚ) : ℝ) / 40| ≤ 36 * (2 * ω') / 40 := by
      rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 40)]
      linarith
    have e1' := abs_le.1 e1
    have e2' := abs_le.1 e2
    linarith [e1'.1, e2'.2]
  · -- (P)
    simp only at hne ⊢
    have a1 := abs_le.1 (rlPSR_pert hclose C.Ts)
    have a2 := abs_le.1 (rlPSR_pert hclose u)
    rw [rlPSR_cast] at a1 a2
    have hp : (1 : ℝ) / 20 ≤ ((rlPS M0 C.Ts : ℚ) : ℝ) - ((rlPS M0 u : ℚ) : ℝ) := by
      have h : ((1 / 20 : ℚ) : ℝ) ≤ ((rlPS M0 C.Ts - rlPS M0 u : ℚ) : ℝ) := by
        exact_mod_cast hadm.2.2.2.2 u hu hne
      push_cast at h; linarith
    linarith [a1.1, a2.2]
  · -- (E2)
    simp only [hYdef]
    have h := heff.1 R R.2 hR i i.2 hbit
    have e : rlM Y0 R i = Y0 R i := by simp [rlM, Nat.mod_eq_of_lt R.2, Nat.mod_eq_of_lt i.2]
    rw [e] at h
    have h' : ((Y0 R i : ℚ) : ℝ) ≤ ((d0.x - 1 / 80 / 100 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    rw [hx0def]; linarith
  · -- the designated budget
    simp only
    have hsum := heff.2.2
    have hdgv : ∀ R : Fin 8, (R : ℕ) ≠ 0 → ((dg R : Fin 3) : ℕ) = tcDesig C.dg R := by
      intro R hR
      simp only [hdg]
      exact Nat.mod_eq_of_lt (hdes R R.2 hR)
    -- per-term comparison with the rational entries
    have hterm : ∀ R : Fin 8, (R : ℕ) ≠ 0 →
        tcEntR x f Y R (dg R) ≤ ((rlTcEnt d0 Y0 R (tcDesig C.dg R) : ℚ) : ℝ) + ω' := by
      intro R hR
      have he := tcEntR_close (Y := Y) hω'0 hxc hfc R (dg R)
      have h1 := hE0c R (dg R)
      rw [hdgv R hR] at h1
      have : E0 R (dg R) = tcEntR (fun _ => x0) (fun _ => f0) Y R (dg R) := rfl
      linarith [he.2]
    rw [sum_erase0_fin8]
    have hs' : (((∑ R ∈ Finset.range 7, rlTcEnt d0 Y0 (R + 1) (tcDesig C.dg (R + 1)) : ℚ)) : ℝ) ≤
        B - 1 / 500 := by
      have h : (((∑ R ∈ Finset.range 7, rlTcEnt d0 Y0 (R + 1) (tcDesig C.dg (R + 1)) : ℚ)) : ℝ) ≤
          ((((C.Bn : ℚ) / C.Bd - 1 / 500 : ℚ)) : ℝ) := by exact_mod_cast hsum
      rw [hBdef]; push_cast at h ⊢; linarith
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hs'
    push_cast at hs'
    have t1 : tcEntR x f Y 1 (dg 1) ≤ ((rlTcEnt d0 Y0 1 (tcDesig C.dg 1) : ℚ) : ℝ) + ω' :=
      hterm 1 (by decide)
    have t2 : tcEntR x f Y 2 (dg 2) ≤ ((rlTcEnt d0 Y0 2 (tcDesig C.dg 2) : ℚ) : ℝ) + ω' :=
      hterm 2 (by decide)
    have t3 : tcEntR x f Y 3 (dg 3) ≤ ((rlTcEnt d0 Y0 3 (tcDesig C.dg 3) : ℚ) : ℝ) + ω' :=
      hterm 3 (by decide)
    have t4 : tcEntR x f Y 4 (dg 4) ≤ ((rlTcEnt d0 Y0 4 (tcDesig C.dg 4) : ℚ) : ℝ) + ω' :=
      hterm 4 (by decide)
    have t5 : tcEntR x f Y 5 (dg 5) ≤ ((rlTcEnt d0 Y0 5 (tcDesig C.dg 5) : ℚ) : ℝ) + ω' :=
      hterm 5 (by decide)
    have t6 : tcEntR x f Y 6 (dg 6) ≤ ((rlTcEnt d0 Y0 6 (tcDesig C.dg 6) : ℚ) : ℝ) + ω' :=
      hterm 6 (by decide)
    have t7 : tcEntR x f Y 7 (dg 7) ≤ ((rlTcEnt d0 Y0 7 (tcDesig C.dg 7) : ℚ) : ℝ) + ω' :=
      hterm 7 (by decide)
    norm_num at hs'
    linarith
  · -- the budget
    obtain ⟨-, h2⟩ := hbud c hc0 hc8
    rw [tcEhi_cast] at h2
    exact h2

end Census
end IIT
