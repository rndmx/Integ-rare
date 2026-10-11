/-
Census, B1 LTBetaHi, RL-tc certificate (W8 §7.2, §8.2), part 1a: the data model, the fast cell checker and
its soundness.

Model (W8 §7.2, symmetric merged two-block model with `u = tc`). Data `RLTcD`: the A-rest block (`G1, F1, V1`,
the A-rows WITHOUT `tc`), the B block (`G2, F2, V2`) and tc's two shared entries `x = y_{tc,i}`,
`f = y_{tc^i,i}`. A merged table `M u i` (pattern mask `u : Fin 8` relative to `tc`, column `i : Fin 3`) and tc's
private entries `Y u i` (`u ∉ {0, 2^i}`) are admissible (`rlTcAdm`) if `M - (tc entry)` lies in the rest interval
of (2.1), `Y ∈ [0, 1]`, and (V), (G), (P) hold with `c = x` and target profile `lp3CStar` (every cc-5 profile is
`lp3CStar` up to renaming the units; the emitter renames). The effect conditions `rlTcEff` are those of Lemma EFG
with `te` = all ON: (E2) `Y R i ≤ x - t/100` for `i ∉ R`, and the designated budget
`Σ_{R ≠ 0} T(R, desig R) ≤ B - 1/500` (`T` = tc's entry). Suppressor rows are not needed: in all 518 cells of
`w8_ucells_tcB.json` the budget `B` satisfies the plain bound `B ≤ 3 log 2 (e_lo - e_hi(c))` for every competitor
`c` (`TcBudget`), so (E1) follows from `efg_E1_of_eff_le` (B1LTHiEff).

Checker (kernel cost is the design constraint: list lookups by structural recursion cost ~1 ms each in the
kernel, GMP-accelerated `Nat` primitives ~30 µs). A witness stores its table as ONE natural (`bw` bits per entry,
read by `Nat.shiftRight` / `Nat.mod`), all inequalities are `Nat.ble` of `Nat.add` / `Nat.mul` terms (negative
parts moved across), and the value form of a profile is computed from its unit cut masks (`TcProf`:
`8 v_C = 8 PS(Ts) - Σ_i c_i Σ_{u ⊆ X_i} M(Ts ⊕ u, i)`), matched against `cd_fz` once by `decide +kernel`
(`tcProfL_ok`, `tcProfStar_ok`). Vertices (`tcVertsN`) are the lower-envelope points `V = max(G, F)` of the two
`(G, F, V)` factors (admissibility is monotone in `V1, V2`), in integer coordinates over the box denominator `Q`.

Soundness: **`tcCellOK_sound`** (vertices: `rlTcAdm ∧ rlTcEff` at `t = tn/td`; rays: `rlRay`; `Ts < 8`;
budget: `TcBudget`, the real form with `Real.log 2`).
-/
import IIT.Census.B1LTHiCertRL2
import IIT.Census.CertRatesCore

namespace IIT
namespace Census

/-! ### The RL-tc data model (ℚ) -/

/-- RL-tc data: A-rest block `(G1, F1, V1)` (without `tc`), B block `(G2, F2, V2)`, tc's shared entries `x, f`. -/
structure RLTcD where
  G1 : ℚ
  F1 : ℚ
  G2 : ℚ
  F2 : ℚ
  V1 : ℚ
  V2 : ℚ
  x : ℚ
  f : ℚ

/-- The rest blocks as two-block data. -/
def RLTcD.rest (d : RLTcD) : RLD := ⟨d.G1, d.F1, d.G2, d.F2, d.V1, d.V2⟩

/-- tc's entry at pattern `u`, column `i` (shared `x`, `f`; private `Y`). -/
def rlTcEnt (d : RLTcD) (Y : Fin 8 → Fin 3 → ℚ) (u i : ℕ) : ℚ :=
  if u = 0 then d.x else if u = rlBit i then d.f else rlM Y u i

/-- **Cause admissibility** of `(M, Y)` for RL-tc at level `t`, target `Ts` (`c = x`). -/
def rlTcAdm (d : RLTcD) (t : ℚ) (Ts : ℕ) (M Y : Fin 8 → Fin 3 → ℚ) : Prop :=
  (∀ u < 8, ∀ i < 3, rlLo d.rest u i ≤ rlM M u i - rlTcEnt d Y u i ∧
      rlM M u i - rlTcEnt d Y u i ≤ rlLo d.rest u i + rlWd d.rest u i) ∧
  (∀ u < 8, ∀ i < 3, u ≠ 0 → u ≠ rlBit i → 0 ≤ rlM Y u i ∧ rlM Y u i ≤ 1) ∧
  8 * d.x * (5 / 3 - t) ≤ rlV8 lp3CStar Ts M ∧
  (∀ C ∈ lp3Profiles, C ≠ lp3CStar →
    1 / 20 * d.x * t ≤ rlV8 C Ts M / (8 * (cd_cc 3 C : ℚ)) - rlV8 lp3CStar Ts M / 40) ∧
  (∀ u < 8, u ≠ Ts → 1 / 20 ≤ rlPS M Ts - rlPS M u)

/-- **Effect conditions** (Lemma EFG, `te` = all ON, frame of row `tc`): (E2) with slack `t/100`, valid
designations, and the designated budget with slack `1/500`. -/
def rlTcEff (d : RLTcD) (t B : ℚ) (desig : ℕ → ℕ) (Y : Fin 8 → Fin 3 → ℚ) : Prop :=
  (∀ R < 8, R ≠ 0 → ∀ i < 3, R.testBit i = false → rlM Y R i ≤ d.x - t / 100) ∧
  (∀ R < 8, R ≠ 0 → desig R < 3) ∧
  ∑ R ∈ Finset.range 7, rlTcEnt d Y (R + 1) (desig (R + 1)) ≤ B - 1 / 500

/-! ### Kernel primitives -/

/-- Field `k` of a packed natural (`bw` bits per field, modulus `md`). -/
def tcGet (bw md P k : ℕ) : ℕ := Nat.mod (Nat.shiftRight P (Nat.mul bw k)) md

/-- Entry `(u, i)` of a packed table (field `3u + i`). -/
def tcAt (bw md P u i : ℕ) : ℕ := tcGet bw md P (Nat.add (Nat.mul 3 u) i)

/-- The rational table of a packed witness with denominator `D`. -/
def tcTab (bw md P D : ℕ) : Fin 8 → Fin 3 → ℚ := fun u i => (tcAt bw md P u i : ℚ) / D

def nAll3 (p : ℕ → Bool) : Bool := p 0 && p 1 && p 2
def nAll8 (p : ℕ → Bool) : Bool := p 0 && p 1 && p 2 && p 3 && p 4 && p 5 && p 6 && p 7
def nSum3 (f : ℕ → ℕ) : ℕ := Nat.add (Nat.add (f 0) (f 1)) (f 2)
def nSum7 (f : ℕ → ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (f 0) (f 1)) (f 2)) (f 3)) (f 4)) (f 5)) (f 6)
def nSum8 (f : ℕ → ℕ) : ℕ := Nat.add (nSum7 f) (f 7)

/-! ### Profiles by unit cut masks -/

/-- A profile as unit cut masks `X_i` (`bit q` = unit `q` cut from unit `i`) with weights `c_i = 2^{3-|X_i|}`. -/
structure TcProf where
  cc : ℕ
  X0 : ℕ
  c0 : ℕ
  X1 : ℕ
  c1 : ℕ
  X2 : ℕ
  c2 : ℕ

/-- `Σ_{u ⊆ X} M(Ts ⊕ u, i)` (packed table). -/
def tcSubSum (bw md P Ts X i : ℕ) : ℕ :=
  nSum8 fun u => cond (Nat.beq (Nat.land u X) u) (tcAt bw md P (Ts ^^^ u) i) 0

/-- `Σ_i c_i Σ_{u ⊆ X_i} M(Ts ⊕ u, i)`, so that `8 v_C = 8 PS(Ts) - tcNeg`. -/
def tcNeg (bw md P Ts : ℕ) (p : TcProf) : ℕ :=
  Nat.add (Nat.add (Nat.mul p.c0 (tcSubSum bw md P Ts p.X0 0)) (Nat.mul p.c1 (tcSubSum bw md P Ts p.X1 1)))
    (Nat.mul p.c2 (tcSubSum bw md P Ts p.X2 2))

/-- `tcNeg` from cached unit subsums (field `8 i + X`). -/
def tcNegS (sw smd S : ℕ) (p : TcProf) : ℕ :=
  Nat.add (Nat.add (Nat.mul p.c0 (tcGet sw smd S p.X0)) (Nat.mul p.c1 (tcGet sw smd S (Nat.add 8 p.X1))))
    (Nat.mul p.c2 (tcGet sw smd S (Nat.add 16 p.X2)))

/-- The cached unit subsums are correct (for the masks `X ∌ i`). -/
def tcSubB (bw md W Ts sw smd S : ℕ) : Bool :=
  nAll3 fun i => nAll8 fun X => Nat.testBit X i ||
    Nat.beq (tcGet sw smd S (Nat.add (Nat.mul 8 i) X)) (tcSubSum bw md W Ts X i)

/-- Pattern sum of a packed table. -/
def tcPSN (bw md P u : ℕ) : ℕ := nSum3 fun i => tcAt bw md P u i

/-- The target profile `lp3CStar` (`C_0 = {2}`, `C_1 = {0,2}`, `C_2 = {0,1}`). -/
def tcProfStar : TcProf := ⟨5, 4, 4, 5, 2, 3, 2⟩

/-- The 21 other profiles, in the order of `lp3Profiles`. -/
def tcProfL : List TcProf :=
  [⟨4, 4, 4, 4, 4, 3, 2⟩, ⟨2, 4, 4, 4, 4, 0, 8⟩, ⟨2, 0, 8, 0, 8, 3, 2⟩, ⟨4, 2, 4, 5, 2, 2, 4⟩,
   ⟨2, 2, 4, 0, 8, 2, 4⟩, ⟨2, 0, 8, 5, 2, 0, 8⟩, ⟨4, 6, 2, 1, 4, 1, 4⟩, ⟨2, 6, 2, 0, 8, 0, 8⟩,
   ⟨2, 0, 8, 1, 4, 1, 4⟩, ⟨6, 6, 2, 5, 2, 3, 2⟩, ⟨4, 6, 2, 5, 2, 0, 8⟩, ⟨4, 6, 2, 0, 8, 3, 2⟩,
   ⟨4, 6, 2, 4, 4, 2, 4⟩, ⟨5, 6, 2, 4, 4, 3, 2⟩, ⟨5, 6, 2, 5, 2, 2, 4⟩, ⟨4, 0, 8, 5, 2, 3, 2⟩,
   ⟨4, 4, 4, 5, 2, 1, 4⟩, ⟨4, 2, 4, 1, 4, 3, 2⟩, ⟨5, 2, 4, 5, 2, 3, 2⟩, ⟨5, 6, 2, 5, 2, 1, 4⟩,
   ⟨5, 6, 2, 1, 4, 3, 2⟩]

/-- The `cd_fz` coefficients of `C` are those of the unit cut masks of `p`, and `p.cc = cd_cc 3 C > 0`. -/
def tcCoefOK (C : List (List Bool)) (p : TcProf) : Bool :=
  Nat.beq p.cc (cd_cc 3 C) && Nat.blt 0 p.cc &&
  !Nat.testBit p.X0 0 && !Nat.testBit p.X1 1 && !Nat.testBit p.X2 2 &&
  Nat.blt p.X0 8 && Nat.blt p.X1 8 && Nat.blt p.X2 8 &&
  (List.range 8).all fun u =>
    decide (cd_fz 3 C 0 (u + 8 * 0) =
      (if u = 0 then 8 else 0) - (if Nat.land u p.X0 = u then (p.c0 : ℤ) else 0)) &&
    decide (cd_fz 3 C 0 (u + 8 * 1) =
      (if u = 0 then 8 else 0) - (if Nat.land u p.X1 = u then (p.c1 : ℤ) else 0)) &&
    decide (cd_fz 3 C 0 (u + 8 * 2) =
      (if u = 0 then 8 else 0) - (if Nat.land u p.X2 = u then (p.c2 : ℤ) else 0))

theorem tcProfStar_ok : tcCoefOK lp3CStar tcProfStar = true := by decide +kernel

theorem tcProfL_ok : lp3Profiles.all (fun C => C == lp3CStar || tcProfL.any (tcCoefOK C)) = true := by
  decide +kernel

/-! ### Witnesses and their checks -/

/-- A vertex witness, scaled by `D`: the vertex data times `D`, the value `vs = 8 v_{C*}` (times `D`), the
packed merged table `W` and tc's private entries `Y` (`bw` bits per entry, modulus `md`), and the cached unit
subsums `S(i, X) = Σ_{u ⊆ X} W(Ts ⊕ u, i)` (field `8 i + X`, `sw` bits, modulus `smd`; checked once). -/
structure TcWit where
  D : ℕ
  G1 : ℕ
  F1 : ℕ
  G2 : ℕ
  F2 : ℕ
  V1 : ℕ
  V2 : ℕ
  x : ℕ
  f : ℕ
  vs : ℕ
  bw : ℕ
  md : ℕ
  W : ℕ
  Y : ℕ
  sw : ℕ
  smd : ℕ
  S : ℕ

/-- Integer ray data (increments of the rest data). -/
structure RLTcR where
  G1 : ℕ
  F1 : ℕ
  G2 : ℕ
  F2 : ℕ
  V1 : ℕ
  V2 : ℕ

/-- The rational ray. -/
def RLTcR.toRLD (r : RLTcR) : RLD := ⟨r.G1, r.F1, r.G2, r.F2, r.V1, r.V2⟩

/-- A ray witness (homogeneous, `Y = 0`), scaled by `D`, packed. -/
structure TcRayWit where
  D : ℕ
  bw : ℕ
  md : ℕ
  W : ℕ

/-- Lower end of the rest interval from the four shared values (scaled). -/
def tcLo5 (G1 F1 G2 F2 u i : ℕ) : ℕ :=
  cond (Nat.beq u 0) G1 (cond (Nat.beq u (Nat.pow 2 i)) F1 (cond (Nat.beq u 7) G2
    (cond (Nat.beq u (Nat.sub 7 (Nat.pow 2 i))) F2 0)))

/-- Width of the rest interval from the two weights (scaled). -/
def tcWd2 (V1 V2 u i : ℕ) : ℕ :=
  cond (Nat.beq u 0 || Nat.beq u (Nat.pow 2 i)) V2
    (cond (Nat.beq u 7 || Nat.beq u (Nat.sub 7 (Nat.pow 2 i))) V1 (Nat.add V1 V2))

/-- Scaled lower end of the rest interval. -/
def tcLoN (w : TcWit) (u i : ℕ) : ℕ := tcLo5 w.G1 w.F1 w.G2 w.F2 u i

/-- Scaled width of the rest interval. -/
def tcWdN (w : TcWit) (u i : ℕ) : ℕ := tcWd2 w.V1 w.V2 u i

/-- Scaled tc entry. -/
def tcEntN (w : TcWit) (u i : ℕ) : ℕ :=
  cond (Nat.beq u 0) w.x (cond (Nat.beq u (Nat.pow 2 i)) w.f (tcAt w.bw w.md w.Y u i))

/-- Box and `Y ≤ 1` (scaled) at every position. -/
def tcBoxB (w : TcWit) : Bool :=
  nAll8 fun u => nAll3 fun i =>
    Nat.ble (Nat.add (tcLoN w u i) (tcEntN w u i)) (tcAt w.bw w.md w.W u i) &&
    Nat.ble (tcAt w.bw w.md w.W u i) (Nat.add (Nat.add (tcLoN w u i) (tcWdN w u i)) (tcEntN w u i)) &&
    (Nat.beq u 0 || Nat.beq u (Nat.pow 2 i) || Nat.ble (tcAt w.bw w.md w.Y u i) w.D)

/-- Integer vertex data (over the box denominator `Q`). -/
structure RLTcN where
  G1 : ℕ
  F1 : ℕ
  G2 : ℕ
  F2 : ℕ
  V1 : ℕ
  V2 : ℕ
  x : ℕ
  f : ℕ

/-- The rational vertex `v / Q`. -/
def RLTcN.toQ (v : RLTcN) (Q : ℕ) : RLTcD :=
  ⟨(v.G1 : ℚ) / Q, (v.F1 : ℚ) / Q, (v.G2 : ℚ) / Q, (v.F2 : ℚ) / Q, (v.V1 : ℚ) / Q, (v.V2 : ℚ) / Q,
    (v.x : ℚ) / Q, (v.f : ℚ) / Q⟩

/-- The scaled data of a witness are those of the vertex: `w.G1 / D = v.G1 / Q`, etc. -/
def tcDataB (Q : ℕ) (v : RLTcN) (w : TcWit) : Bool :=
  Nat.beq (Nat.mul w.G1 Q) (Nat.mul v.G1 w.D) && Nat.beq (Nat.mul w.F1 Q) (Nat.mul v.F1 w.D) &&
  Nat.beq (Nat.mul w.G2 Q) (Nat.mul v.G2 w.D) && Nat.beq (Nat.mul w.F2 Q) (Nat.mul v.F2 w.D) &&
  Nat.beq (Nat.mul w.V1 Q) (Nat.mul v.V1 w.D) && Nat.beq (Nat.mul w.V2 Q) (Nat.mul v.V2 w.D) &&
  Nat.beq (Nat.mul w.x Q) (Nat.mul v.x w.D) && Nat.beq (Nat.mul w.f Q) (Nat.mul v.f w.D)

/-- Designated column of row `R` (2 bits per row). -/
def tcDesig (dg R : ℕ) : ℕ := Nat.mod (Nat.shiftRight dg (Nat.mul 2 R)) 4

/-- **The vertex checker** at `t = tn/td`, target `Ts`, budget `B = Bn/Bd`, designations `dg`. -/
def tcVertB (tn td Ts Bn Bd dg Q : ℕ) (v : RLTcN) (w : TcWit) : Bool :=
  Nat.blt 0 w.D && tcDataB Q v w && tcBoxB w && tcSubB w.bw w.md w.W Ts w.sw w.smd w.S &&
  Nat.beq (Nat.add w.vs (tcNegS w.sw w.smd w.S tcProfStar)) (Nat.mul 8 (tcPSN w.bw w.md w.W Ts)) &&
  Nat.ble (Nat.mul (Nat.mul 40 w.x) td) (Nat.add (Nat.mul (Nat.mul 3 td) w.vs) (Nat.mul (Nat.mul 24 w.x) tn)) &&
  tcProfL.all (fun p => Nat.ble
    (Nat.add (Nat.add (Nat.mul (Nat.mul (Nat.mul 2 p.cc) w.x) tn) (Nat.mul (Nat.mul p.cc td) w.vs))
      (Nat.mul (Nat.mul 5 td) (tcNegS w.sw w.smd w.S p)))
    (Nat.mul (Nat.mul 40 td) (tcPSN w.bw w.md w.W Ts))) &&
  nAll8 (fun u => Nat.beq u Ts ||
    Nat.ble (Nat.add w.D (Nat.mul 20 (tcPSN w.bw w.md w.W u))) (Nat.mul 20 (tcPSN w.bw w.md w.W Ts))) &&
  nAll8 (fun R => Nat.beq R 0 || nAll3 fun i => Nat.testBit R i ||
    Nat.ble (Nat.add (Nat.mul (Nat.mul 100 td) (tcAt w.bw w.md w.Y R i)) (Nat.mul w.D tn))
      (Nat.mul (Nat.mul 100 td) w.x)) &&
  Nat.ble (Nat.add (Nat.mul (Nat.mul 500 Bd) (nSum7 fun R => tcEntN w (R + 1) (tcDesig dg (R + 1))))
      (Nat.mul Bd w.D)) (Nat.mul (Nat.mul 500 Bn) w.D)

/-- **The ray checker** (homogeneous). -/
def tcRayB (Ts : ℕ) (r : RLTcR) (w : TcRayWit) : Bool :=
  Nat.blt 0 w.D &&
  (nAll8 fun u => nAll3 fun i =>
    Nat.ble (Nat.mul (tcLo5 r.G1 r.F1 r.G2 r.F2 u i) w.D) (tcAt w.bw w.md w.W u i) &&
    Nat.ble (tcAt w.bw w.md w.W u i)
      (Nat.mul (Nat.add (tcLo5 r.G1 r.F1 r.G2 r.F2 u i) (tcWd2 r.V1 r.V2 u i)) w.D)) &&
  Nat.ble (tcNeg w.bw w.md w.W Ts tcProfStar) (Nat.mul 8 (tcPSN w.bw w.md w.W Ts)) &&
  tcProfL.all (fun p => Nat.ble
    (Nat.add (Nat.mul 5 (tcNeg w.bw w.md w.W Ts p)) (Nat.mul (Nat.mul 8 p.cc) (tcPSN w.bw w.md w.W Ts)))
    (Nat.add (Nat.mul 40 (tcPSN w.bw w.md w.W Ts)) (Nat.mul p.cc (tcNeg w.bw w.md w.W Ts tcProfStar)))) &&
  nAll8 fun u => Nat.ble (tcPSN w.bw w.md w.W u) (tcPSN w.bw w.md w.W Ts)

/-! ### Cells -/

/-- A box of data over the denominator `Q`: `G1 ∈ [g1lo, g1hi]/Q`, `F1 ∈ [f1lo, f1hi]/Q`,
`G2 ∈ [g2lo, g2hi]/Q`, `F2 ∈ [f2lo, f2hi]/Q` (`none` = unbounded), `x ∈ [xlo, xhi]/Q`, `f ∈ [flo, fhi]/Q`;
`V1 ≥ max(G1, F1)`, `V2 ≥ max(G2, F2)`. -/
structure TcBox where
  g1lo : ℕ
  g1hi : ℕ
  f1lo : ℕ
  f1hi : ℕ
  g2lo : ℕ
  g2hi : Option ℕ
  f2lo : ℕ
  f2hi : Option ℕ
  xlo : ℕ
  xhi : ℕ
  flo : ℕ
  fhi : ℕ
  Q : ℕ

/-- A certified cell: box, target `Ts`, budget `B = Bn/Bd`, designations `dg` (2 bits per row), witnesses. -/
structure TcCell where
  box : TcBox
  Ts : ℕ
  Bn : ℕ
  Bd : ℕ
  dg : ℕ
  wits : List TcWit
  rays : List TcRayWit

/-- Append `p` unless present. -/
def tcAddNew (p : ℕ × ℕ) (L : List (ℕ × ℕ)) : List (ℕ × ℕ) := if p ∈ L then L else L ++ [p]

/-- Lower-envelope points of one factor `(G, F)`: the corners, then the two ends of the diagonal segment. -/
def tcFacPts (g0 : ℕ) (g1 : Option ℕ) (f0 : ℕ) (f1 : Option ℕ) : List (ℕ × ℕ) :=
  let L2 := match g1 with | none => [(g0, f0)] | some g => tcAddNew (g, f0) [(g0, f0)]
  let L3 := match f1 with | none => L2 | some f => tcAddNew (g0, f) L2
  let L4 := match g1, f1 with | some g, some f => tcAddNew (g, f) L3 | _, _ => L3
  let a := max g0 f0
  let okA : Bool := (match g1 with | none => true | some g => decide (a ≤ g)) &&
    (match f1 with | none => true | some f => decide (a ≤ f))
  let L5 := if okA then tcAddNew (a, a) L4 else L4
  match g1, f1 with
  | some g, some f => if a ≤ min g f then tcAddNew (min g f, min g f) L5 else L5
  | some g, none => if a ≤ g then tcAddNew (g, g) L5 else L5
  | none, some f => if a ≤ f then tcAddNew (f, f) L5 else L5
  | none, none => L5

/-- The vertices of a cell (integer coordinates over `Q`): lower-envelope points of both factors times the
corners in `x`, `f`. -/
def tcVertsN (b : TcBox) : List RLTcN :=
  (tcFacPts b.g1lo (some b.g1hi) b.f1lo (some b.f1hi)).flatMap fun p1 =>
  (tcFacPts b.g2lo b.g2hi b.f2lo b.f2hi).flatMap fun p2 =>
  [b.xlo, b.xhi].flatMap fun x => [b.flo, b.fhi].map fun f =>
    (⟨p1.1, p1.2, p2.1, p2.2, max p1.1 p1.2, max p2.1 p2.2, x, f⟩ : RLTcN)

/-- The rational vertices of a cell. -/
def tcVerts (b : TcBox) : List RLTcD := (tcVertsN b).map fun v => v.toQ b.Q

/-- The rays of a cell (increments of the rest data; only the B factor can be unbounded). -/
def tcRaysN (b : TcBox) : List RLTcR :=
  (match b.g2hi with | none => [(⟨0, 0, 1, 0, 0, 1⟩ : RLTcR)] | some _ => []) ++
  (match b.f2hi with | none => [(⟨0, 0, 0, 1, 0, 1⟩ : RLTcR)] | some _ => []) ++
  (match b.g2hi, b.f2hi with | none, none => [(⟨0, 0, 1, 1, 0, 1⟩ : RLTcR)] | _, _ => [])

/-- The rational rays of a cell. -/
def tcRays (b : TcBox) : List RLD := (tcRaysN b).map RLTcR.toRLD

/-- `x` range widened by the window `1/1000` (lower / upper). -/
def tcLx (b : TcBox) : ℚ := max 0 ((b.xlo : ℚ) / b.Q - 1 / 1000)
def tcHx (b : TcBox) : ℚ := min 1 ((b.xhi : ℚ) / b.Q + 1 / 1000)

/-- Upper bound of the effect probability of competitor `c` (bit `i` set = unit `i` OFF). -/
def tcEhi (b : TcBox) (c : ℕ) : ℚ :=
  (if c.testBit 0 then 1 - tcLx b else tcHx b) * (if c.testBit 1 then 1 - tcLx b else tcHx b) *
    (if c.testBit 2 then 1 - tcLx b else tcHx b)

/-- The rational budget check (plain bound `U_t = 3 e_hi(t)` for every competitor). -/
def tcBudB (b : TcBox) (B : ℚ) : Bool :=
  (List.range 7).all fun c => decide (tcEhi b (c + 1) ≤ tcLx b ^ 3) &&
    decide (B ≤ 3 * crL2lo * (tcLx b ^ 3 - tcEhi b (c + 1)))

/-- Designations are columns. -/
def tcDesigB (dg : ℕ) : Bool := nAll8 fun R => Nat.beq R 0 || Nat.blt (tcDesig dg R) 3

/-- `f a b` along two lists of equal length. -/
def tcAllZip {α β : Type} (f : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: l, b :: m => f a b && tcAllZip f l m
  | [], _ :: _ => false
  | _ :: _, [] => false

/-- **The cell checker** at `t = tn/td`. -/
def tcCellOK (tn td : ℕ) (C : TcCell) : Bool :=
  Nat.blt C.Ts 8 && Nat.blt 0 C.box.Q && Nat.blt 0 C.Bd && tcDesigB C.dg &&
  tcBudB C.box ((C.Bn : ℚ) / C.Bd) &&
  tcAllZip (tcVertB tn td C.Ts C.Bn C.Bd C.dg C.box.Q) (tcVertsN C.box) C.wits &&
  tcAllZip (tcRayB C.Ts) (tcRaysN C.box) C.rays

/-! ### Soundness -/

lemma nAll3_sound {p : ℕ → Bool} (h : nAll3 p = true) : ∀ i < 3, p i = true := by
  simp only [nAll3, Bool.and_eq_true] at h
  intro i hi; interval_cases i <;> simp_all

lemma nAll8_sound {p : ℕ → Bool} (h : nAll8 p = true) : ∀ i < 8, p i = true := by
  simp only [nAll8, Bool.and_eq_true] at h
  intro i hi; interval_cases i <;> simp_all

lemma tcAllZip_sound {α β : Type} {f : α → β → Bool} :
    ∀ {l : List α} {m : List β}, tcAllZip f l m = true → ∀ a ∈ l, ∃ b ∈ m, f a b = true
  | [], [], _, a, ha => by simp at ha
  | a' :: l, b' :: m, h, a, ha => by
    simp only [tcAllZip, Bool.and_eq_true] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b', List.mem_cons_self, h.1⟩
    · obtain ⟨b, hb, hfb⟩ := tcAllZip_sound h.2 a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hfb⟩
  | [], _ :: _, h, _, _ => by simp [tcAllZip] at h
  | _ :: _, [], h, _, _ => by simp [tcAllZip] at h

lemma rlM_tcTab (bw md P D : ℕ) {u i : ℕ} (hu : u < 8) (hi : i < 3) :
    rlM (tcTab bw md P D) u i = (tcAt bw md P u i : ℚ) / D := by
  simp [rlM, tcTab, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hi]

lemma rlS8_congr' {f g : ℕ → ℚ} (h : ∀ u < 8, f u = g u) : rlS8 f = rlS8 g := by
  unfold rlS8
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num),
    h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num)]

lemma tc_xor_lt {Ts u : ℕ} (hTs : Ts < 8) (hu : u < 8) : Ts ^^^ u < 8 :=
  Nat.xor_lt_two_pow (n := 3) hTs hu

lemma tcSubSum_cast (bw md P Ts X i : ℕ) :
    ((tcSubSum bw md P Ts X i : ℕ) : ℚ) =
      rlS8 (fun u => if Nat.land u X = u then (tcAt bw md P (Ts ^^^ u) i : ℚ) else 0) := by
  simp only [tcSubSum, nSum8, nSum7, rlS8, Nat.add_eq, Nat.cast_add, cond_eq_ite, Nat.beq_eq, Nat.cast_ite,
    Nat.cast_zero]

lemma tcNeg_cast (bw md P Ts : ℕ) (p : TcProf) :
    ((tcNeg bw md P Ts p : ℕ) : ℚ) = p.c0 * (tcSubSum bw md P Ts p.X0 0 : ℚ) +
      p.c1 * (tcSubSum bw md P Ts p.X1 1 : ℚ) + p.c2 * (tcSubSum bw md P Ts p.X2 2 : ℚ) := by
  simp only [tcNeg, Nat.add_eq, Nat.mul_eq]; push_cast; ring

lemma tcPSN_cast (bw md P u : ℕ) :
    ((tcPSN bw md P u : ℕ) : ℚ) = tcAt bw md P u 0 + tcAt bw md P u 1 + tcAt bw md P u 2 := by
  simp only [tcPSN, nSum3, Nat.add_eq]; push_cast; ring

lemma rlPS_tcTab (bw md P D : ℕ) {u : ℕ} (hu : u < 8) :
    rlPS (tcTab bw md P D) u = (tcPSN bw md P u : ℚ) / D := by
  rw [tcPSN_cast]
  simp only [rlPS, rlS3, rlM_tcTab bw md P D hu (by norm_num : (0 : ℕ) < 3),
    rlM_tcTab bw md P D hu (by norm_num : (1 : ℕ) < 3), rlM_tcTab bw md P D hu (by norm_num : (2 : ℕ) < 3)]
  ring

/-- One unit of the value form, from its cut mask. -/
lemma tc_unit {C : List (List Bool)} {i X c : ℕ} (hi : i < 3)
    (ha : ∀ u < 8, cd_fz 3 C 0 (u + 8 * i) =
      (if u = 0 then 8 else 0) - (if Nat.land u X = u then (c : ℤ) else 0))
    {Ts : ℕ} (hTs : Ts < 8) (bw md P D : ℕ) :
    rlS8 (fun u => (cd_fz 3 C 0 (u + 8 * i) : ℚ) * rlM (tcTab bw md P D) (Ts ^^^ u) i) =
      (8 * (tcAt bw md P Ts i : ℚ) - c * (tcSubSum bw md P Ts X i : ℚ)) / D := by
  rw [tcSubSum_cast]
  have key : ∀ u < 8, (cd_fz 3 C 0 (u + 8 * i) : ℚ) * rlM (tcTab bw md P D) (Ts ^^^ u) i =
      (8 * (if u = 0 then (tcAt bw md P (Ts ^^^ u) i : ℚ) else 0) -
        c * (if Nat.land u X = u then (tcAt bw md P (Ts ^^^ u) i : ℚ) else 0)) / D := by
    intro u hu
    rw [ha u hu, rlM_tcTab bw md P D (tc_xor_lt hTs hu) hi]
    push_cast
    split_ifs <;> ring
  rw [rlS8_congr' key]
  simp (config := { decide := true }) only [rlS8, Nat.xor_zero, ↓reduceIte]
  ring

/-- **The value form of a profile**, computed from its unit cut masks. -/
lemma rlV8_tc {C : List (List Bool)} {p : TcProf} (hp : tcCoefOK C p = true) {Ts : ℕ} (hTs : Ts < 8)
    (bw md P D : ℕ) :
    rlV8 C Ts (tcTab bw md P D) = (8 * (tcPSN bw md P Ts : ℚ) - (tcNeg bw md P Ts p : ℚ)) / D := by
  simp only [tcCoefOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hp
  have h0 : ∀ u < 8, cd_fz 3 C 0 (u + 8 * 0) =
      (if u = 0 then 8 else 0) - (if Nat.land u p.X0 = u then (p.c0 : ℤ) else 0) :=
    fun u hu => (hp.2 u hu).1.1
  have h1 : ∀ u < 8, cd_fz 3 C 0 (u + 8 * 1) =
      (if u = 0 then 8 else 0) - (if Nat.land u p.X1 = u then (p.c1 : ℤ) else 0) :=
    fun u hu => (hp.2 u hu).1.2
  have h2 : ∀ u < 8, cd_fz 3 C 0 (u + 8 * 2) =
      (if u = 0 then 8 else 0) - (if Nat.land u p.X2 = u then (p.c2 : ℤ) else 0) :=
    fun u hu => (hp.2 u hu).2
  simp only [rlV8, rlS3]
  rw [tc_unit (by norm_num) h0 hTs, tc_unit (by norm_num) h1 hTs, tc_unit (by norm_num) h2 hTs, tcNeg_cast,
    tcPSN_cast]
  ring

/-- The cached subsums give `tcNeg`. -/
lemma tcNegS_eq {bw md W Ts sw smd S : ℕ} (h : tcSubB bw md W Ts sw smd S = true) {p : TcProf}
    (hp0 : Nat.testBit p.X0 0 = false) (hp1 : Nat.testBit p.X1 1 = false) (hp2 : Nat.testBit p.X2 2 = false)
    (hq0 : p.X0 < 8) (hq1 : p.X1 < 8) (hq2 : p.X2 < 8) :
    tcNegS sw smd S p = tcNeg bw md W Ts p := by
  have h' := nAll3_sound h
  have e : ∀ i < 3, ∀ X < 8, Nat.testBit X i = false →
      tcGet sw smd S (Nat.add (Nat.mul 8 i) X) = tcSubSum bw md W Ts X i := by
    intro i hi X hX hb
    have := nAll8_sound (h' i hi) X hX
    simpa [hb] using this
  have e0 := e 0 (by norm_num) p.X0 hq0 hp0
  have e1 := e 1 (by norm_num) p.X1 hq1 hp1
  have e2 := e 2 (by norm_num) p.X2 hq2 hp2
  simp only [Nat.mul_eq, Nat.add_eq, mul_zero, zero_add, mul_one] at e0 e1 e2
  simp only [tcNegS, tcNeg, Nat.add_eq, Nat.mul_eq]
  rw [e0, e1, e2]

lemma tcCoefOK_masks {C : List (List Bool)} {p : TcProf} (hp : tcCoefOK C p = true) :
    p.cc = cd_cc 3 C ∧ 0 < p.cc ∧ Nat.testBit p.X0 0 = false ∧ Nat.testBit p.X1 1 = false ∧
      Nat.testBit p.X2 2 = false ∧ p.X0 < 8 ∧ p.X1 < 8 ∧ p.X2 < 8 := by
  simp only [tcCoefOK, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Bool.not_eq_true'] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, -⟩ := hp
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- The row of a non-star profile. -/
lemma tcProfL_mem {C : List (List Bool)} (hC : C ∈ lp3Profiles) (hne : C ≠ lp3CStar) :
    ∃ p ∈ tcProfL, tcCoefOK C p = true := by
  have h := tcProfL_ok
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
  rcases h C hC with h | h
  · exact absurd h hne
  · exact h

lemma tc_lo5 (d : RLD) {G1 F1 G2 F2 : ℕ} {s : ℚ} (h1 : d.G1 = G1 * s) (h2 : d.F1 = F1 * s)
    (h3 : d.G2 = G2 * s) (h4 : d.F2 = F2 * s) (u i : ℕ) :
    rlLo d u i = (tcLo5 G1 F1 G2 F2 u i : ℚ) * s := by
  unfold rlLo tcLo5 rlBit
  simp only [cond_eq_ite, Nat.beq_eq, Nat.pow_eq, Nat.sub_eq]
  split_ifs <;> simp [h1, h2, h3, h4]

lemma tc_wd2 (d : RLD) {V1 V2 : ℕ} {s : ℚ} (h5 : d.V1 = V1 * s) (h6 : d.V2 = V2 * s) (u i : ℕ) :
    rlWd d u i = (tcWd2 V1 V2 u i : ℚ) * s := by
  unfold rlWd tcWd2 rlBit
  simp only [cond_eq_ite, Nat.beq_eq, Nat.pow_eq, Nat.sub_eq, Bool.or_eq_true, Nat.add_eq]
  split_ifs <;> simp_all [add_mul]

section Vert

variable {w : TcWit} {v : RLTcN} {Q : ℕ}

lemma tcDataB_sound (hQ : 0 < Q) (hD : 0 < w.D) (h : tcDataB Q v w = true) :
    (v.toQ Q).G1 = w.G1 / w.D ∧ (v.toQ Q).F1 = w.F1 / w.D ∧ (v.toQ Q).G2 = w.G2 / w.D ∧
      (v.toQ Q).F2 = w.F2 / w.D ∧ (v.toQ Q).V1 = w.V1 / w.D ∧ (v.toQ Q).V2 = w.V2 / w.D ∧
      (v.toQ Q).x = w.x / w.D ∧ (v.toQ Q).f = w.f / w.D := by
  have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hD' : (w.D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  simp only [tcDataB, Bool.and_eq_true, Nat.beq_eq, Nat.mul_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  simp only [RLTcN.toQ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [div_eq_div_iff hQ' hD'] <;> exact_mod_cast (by omega)

lemma tcEntN_eq {d : RLTcD} (hx : d.x = w.x / w.D) (hf : d.f = w.f / w.D) {u i : ℕ} (hu : u < 8)
    (hi : i < 3) : rlTcEnt d (tcTab w.bw w.md w.Y w.D) u i = (tcEntN w u i : ℚ) / w.D := by
  unfold rlTcEnt tcEntN rlBit
  simp only [cond_eq_ite, Nat.beq_eq, Nat.pow_eq]
  split_ifs <;> simp [hx, hf, rlM_tcTab _ _ _ _ hu hi]

/-- **Soundness of the vertex checker.** -/
theorem tcVertB_sound {tn td Ts Bn Bd dg : ℕ} (htd : 0 < td) (hTs : Ts < 8) (hQ : 0 < Q) (hBd : 0 < Bd)
    (hdes : ∀ R < 8, R ≠ 0 → tcDesig dg R < 3) (h : tcVertB tn td Ts Bn Bd dg Q v w = true) :
    rlTcAdm (v.toQ Q) ((tn : ℚ) / td) Ts (tcTab w.bw w.md w.W w.D) (tcTab w.bw w.md w.Y w.D) ∧
      rlTcEff (v.toQ Q) ((tn : ℚ) / td) ((Bn : ℚ) / Bd) (tcDesig dg) (tcTab w.bw w.md w.Y w.D) := by
  simp only [tcVertB, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hd⟩, hbox⟩, hsub⟩, hvs⟩, hV⟩, hG⟩, hP⟩, hE2⟩, hbud⟩ := h
  have hDq : (0 : ℚ) < w.D := by exact_mod_cast hD
  have htdq : (0 : ℚ) < td := by exact_mod_cast htd
  obtain ⟨e1, e2, e3, e4, e5, e6, hx, hf⟩ := tcDataB_sound hQ hD hd
  have hs : ∀ n : ℕ, (n : ℚ) / w.D = n * (1 / w.D) := fun n => by ring
  have hlo : ∀ u i, rlLo (v.toQ Q).rest u i = (tcLoN w u i : ℚ) / w.D := fun u i => by
    rw [hs]
    exact tc_lo5 (v.toQ Q).rest (by simp only [RLTcD.rest]; rw [e1]; ring)
      (by simp only [RLTcD.rest]; rw [e2]; ring) (by simp only [RLTcD.rest]; rw [e3]; ring)
      (by simp only [RLTcD.rest]; rw [e4]; ring) u i
  have hwd : ∀ u i, rlWd (v.toQ Q).rest u i = (tcWdN w u i : ℚ) / w.D := fun u i => by
    rw [hs]
    exact tc_wd2 (v.toQ Q).rest (by simp only [RLTcD.rest]; rw [e5]; ring)
      (by simp only [RLTcD.rest]; rw [e6]; ring) u i
  have hstarM := tcCoefOK_masks tcProfStar_ok
  have hstar : rlV8 lp3CStar Ts (tcTab w.bw w.md w.W w.D) = (w.vs : ℚ) / w.D := by
    rw [rlV8_tc tcProfStar_ok hTs, ← tcNegS_eq hsub hstarM.2.2.1 hstarM.2.2.2.1 hstarM.2.2.2.2.1
      hstarM.2.2.2.2.2.1 hstarM.2.2.2.2.2.2.1 hstarM.2.2.2.2.2.2.2]
    congr 1
    have : ((w.vs + tcNegS w.sw w.smd w.S tcProfStar : ℕ) : ℚ) = ((8 * tcPSN w.bw w.md w.W Ts : ℕ) : ℚ) := by
      simp only [Nat.add_eq, Nat.mul_eq] at hvs; rw [hvs]
    push_cast at this; linarith
  refine ⟨⟨fun u hu i hi => ?_, fun u hu i hi hu0 hub => ?_, ?_, fun C hC hne => ?_, fun u hu hne => ?_⟩,
    fun R hR hR0 i hi hb => ?_, hdes, ?_⟩
  · -- box
    have hb := nAll3_sound (nAll8_sound hbox u hu) i hi
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at hb
    obtain ⟨⟨b1, b2⟩, -⟩ := hb
    rw [hlo, hwd, tcEntN_eq hx hf hu hi, rlM_tcTab _ _ _ _ hu hi, ← sub_div, ← add_div]
    constructor
    · rw [div_le_div_iff_of_pos_right hDq, le_sub_iff_add_le]; exact_mod_cast b1
    · rw [div_le_div_iff_of_pos_right hDq, sub_le_iff_le_add]; exact_mod_cast b2
  · -- Y range
    have hb := nAll3_sound (nAll8_sound hbox u hu) i hi
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.pow_eq] at hb
    obtain ⟨-, (h0 | h0) | h3⟩ := hb
    · exact absurd h0 hu0
    · exact absurd h0 (by simpa [rlBit] using hub)
    · rw [rlM_tcTab _ _ _ _ hu hi]
      exact ⟨by positivity, (div_le_one hDq).2 (by exact_mod_cast h3)⟩
  · -- (V)
    rw [hstar, hx]
    have h' : (40 * (w.x : ℚ) * td) ≤ 3 * td * w.vs + 24 * w.x * tn := by
      simp only [Nat.add_eq, Nat.mul_eq] at hV; exact_mod_cast hV
    have e : 8 * ((w.x : ℚ) / w.D) * (5 / 3 - (tn : ℚ) / td) =
        (8 * (w.x : ℚ) * (5 * td - 3 * tn)) / (3 * td * w.D) := by
      field_simp
    have e' : (w.vs : ℚ) / w.D = (3 * td * (w.vs : ℚ)) / (3 * td * w.D) := by
      field_simp
    rw [e, e']
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · -- (G)
    obtain ⟨p, hp, hpC⟩ := tcProfL_mem hC hne
    have hpm := tcCoefOK_masks hpC
    simp only [List.all_eq_true, Nat.ble_eq] at hG
    have hg := hG p hp
    rw [tcNegS_eq hsub hpm.2.2.1 hpm.2.2.2.1 hpm.2.2.2.2.1 hpm.2.2.2.2.2.1 hpm.2.2.2.2.2.2.1
      hpm.2.2.2.2.2.2.2] at hg
    rw [rlV8_tc hpC hTs, hstar, hx, ← hpm.1]
    have hcc : (0 : ℚ) < p.cc := by exact_mod_cast hpm.2.1
    have h' : 2 * (p.cc : ℚ) * w.x * tn + p.cc * td * w.vs + 5 * td * (tcNeg w.bw w.md w.W Ts p : ℚ) ≤
        40 * td * (tcPSN w.bw w.md w.W Ts : ℚ) := by
      simp only [Nat.add_eq, Nat.mul_eq] at hg; exact_mod_cast hg
    have e1 : 1 / 20 * ((w.x : ℚ) / w.D) * ((tn : ℚ) / td) =
        (2 * (p.cc : ℚ) * w.x * tn) / (40 * p.cc * td * w.D) := by
      field_simp; ring
    have e2 : (8 * (tcPSN w.bw w.md w.W Ts : ℚ) - (tcNeg w.bw w.md w.W Ts p : ℚ)) / w.D / (8 * (p.cc : ℚ)) -
        (w.vs : ℚ) / w.D / 40 = (5 * td * (8 * (tcPSN w.bw w.md w.W Ts : ℚ) - (tcNeg w.bw w.md w.W Ts p : ℚ)) -
          p.cc * td * w.vs) / (40 * p.cc * td * w.D) := by
      field_simp; ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · -- (P)
    have hp := nAll8_sound hP u hu
    simp only [Bool.or_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq] at hp
    have hp' := hp.resolve_left hne
    rw [rlPS_tcTab _ _ _ _ hTs, rlPS_tcTab _ _ _ _ hu, ← sub_div, le_div_iff₀ hDq]
    have : (w.D : ℚ) + 20 * (tcPSN w.bw w.md w.W u : ℚ) ≤ 20 * (tcPSN w.bw w.md w.W Ts : ℚ) := by
      exact_mod_cast hp'
    linarith
  · -- (E2)
    have he := nAll8_sound hE2 R hR
    simp only [Bool.or_eq_true, Nat.beq_eq] at he
    have he' := nAll3_sound (he.resolve_left hR0) i hi
    simp only [Bool.or_eq_true, hb, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, false_or, Bool.false_eq_true] at he'
    rw [rlM_tcTab _ _ _ _ hR hi, hx]
    have h' : 100 * (td : ℚ) * (tcAt w.bw w.md w.Y R i : ℚ) + w.D * tn ≤ 100 * td * w.x := by
      exact_mod_cast he'
    have e : (w.x : ℚ) / w.D - (tn : ℚ) / td / 100 = (100 * td * w.x - w.D * tn) / (100 * td * w.D) := by
      field_simp
    have e' : (tcAt w.bw w.md w.Y R i : ℚ) / w.D =
        (100 * td * (tcAt w.bw w.md w.Y R i : ℚ)) / (100 * td * w.D) := by
      field_simp
    rw [e, e']
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · -- budget
    have hsum : ∑ R ∈ Finset.range 7, rlTcEnt (v.toQ Q) (tcTab w.bw w.md w.Y w.D) (R + 1) (tcDesig dg (R + 1)) =
        ((nSum7 fun R => tcEntN w (R + 1) (tcDesig dg (R + 1)) : ℕ) : ℚ) / w.D := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, nSum7, Nat.add_eq]
      rw [tcEntN_eq hx hf (by norm_num) (hdes 1 (by norm_num) (by norm_num)),
        tcEntN_eq hx hf (by norm_num) (hdes 2 (by norm_num) (by norm_num)),
        tcEntN_eq hx hf (by norm_num) (hdes 3 (by norm_num) (by norm_num)),
        tcEntN_eq hx hf (by norm_num) (hdes 4 (by norm_num) (by norm_num)),
        tcEntN_eq hx hf (by norm_num) (hdes 5 (by norm_num) (by norm_num)),
        tcEntN_eq hx hf (by norm_num) (hdes 6 (by norm_num) (by norm_num)),
        tcEntN_eq hx hf (by norm_num) (hdes 7 (by norm_num) (by norm_num))]
      push_cast; ring
    rw [hsum, div_le_iff₀ hDq]
    have hBdq : (0 : ℚ) < Bd := by exact_mod_cast hBd
    have h' : 500 * (Bd : ℚ) * ((nSum7 fun R => tcEntN w (R + 1) (tcDesig dg (R + 1)) : ℕ) : ℚ) +
        Bd * w.D ≤ 500 * Bn * w.D := by
      simp only [Nat.add_eq, Nat.mul_eq] at hbud; exact_mod_cast hbud
    have e : ((Bn : ℚ) / Bd - 1 / 500) * w.D = (500 * Bn * w.D - Bd * w.D) / (500 * Bd) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith

end Vert

/-- **Soundness of the ray checker.** -/
theorem tcRayB_sound {Ts : ℕ} (hTs : Ts < 8) {r : RLTcR} {w : TcRayWit} (h : tcRayB Ts r w = true) :
    rlRay r.toRLD Ts (tcTab w.bw w.md w.W w.D) := by
  simp only [tcRayB, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨hD, hbox⟩, hV⟩, hG⟩, hP⟩ := h
  have hDq : (0 : ℚ) < w.D := by exact_mod_cast hD
  have hstar : rlV8 lp3CStar Ts (tcTab w.bw w.md w.W w.D) =
      (8 * (tcPSN w.bw w.md w.W Ts : ℚ) - (tcNeg w.bw w.md w.W Ts tcProfStar : ℚ)) / w.D :=
    rlV8_tc tcProfStar_ok hTs _ _ _ _
  refine ⟨fun u hu i hi => ?_, ?_, fun C hC hne => ?_, fun u hu hne => ?_⟩
  · have hb := nAll3_sound (nAll8_sound hbox u hu) i hi
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.mul_eq, Nat.add_eq] at hb
    have hl := tc_lo5 r.toRLD (G1 := r.G1) (F1 := r.F1) (G2 := r.G2) (F2 := r.F2) (s := 1)
      (by simp [RLTcR.toRLD]) (by simp [RLTcR.toRLD]) (by simp [RLTcR.toRLD]) (by simp [RLTcR.toRLD]) u i
    have hw := tc_wd2 r.toRLD (V1 := r.V1) (V2 := r.V2) (s := 1)
      (by simp [RLTcR.toRLD]) (by simp [RLTcR.toRLD]) u i
    rw [mul_one] at hl hw
    rw [rlM_tcTab _ _ _ _ hu hi, hl, hw]
    constructor
    · rw [le_div_iff₀ hDq]; exact_mod_cast hb.1
    · rw [div_le_iff₀ hDq]; exact_mod_cast hb.2
  · rw [hstar]
    have : (tcNeg w.bw w.md w.W Ts tcProfStar : ℚ) ≤ 8 * (tcPSN w.bw w.md w.W Ts : ℚ) := by
      simp only [Nat.ble_eq, Nat.mul_eq] at hV; exact_mod_cast hV
    exact div_nonneg (by linarith) hDq.le
  · obtain ⟨p, hp, hpC⟩ := tcProfL_mem hC hne
    have hpm := tcCoefOK_masks hpC
    simp only [List.all_eq_true, Nat.ble_eq] at hG
    have hg := hG p hp
    rw [rlV8_tc hpC hTs, hstar, ← hpm.1]
    have hcc : (0 : ℚ) < p.cc := by exact_mod_cast hpm.2.1
    have h' : 5 * (tcNeg w.bw w.md w.W Ts p : ℚ) + 8 * p.cc * (tcPSN w.bw w.md w.W Ts : ℚ) ≤
        40 * (tcPSN w.bw w.md w.W Ts : ℚ) + p.cc * (tcNeg w.bw w.md w.W Ts tcProfStar : ℚ) := by
      simp only [Nat.add_eq, Nat.mul_eq] at hg; exact_mod_cast hg
    have e : (8 * (tcPSN w.bw w.md w.W Ts : ℚ) - (tcNeg w.bw w.md w.W Ts p : ℚ)) / w.D / (8 * (p.cc : ℚ)) -
        (8 * (tcPSN w.bw w.md w.W Ts : ℚ) - (tcNeg w.bw w.md w.W Ts tcProfStar : ℚ)) / w.D / 40 =
        (5 * (8 * (tcPSN w.bw w.md w.W Ts : ℚ) - (tcNeg w.bw w.md w.W Ts p : ℚ)) -
          p.cc * (8 * (tcPSN w.bw w.md w.W Ts : ℚ) - (tcNeg w.bw w.md w.W Ts tcProfStar : ℚ))) /
          (40 * p.cc * w.D) := by
      field_simp; ring
    rw [e]
    exact div_nonneg (by nlinarith) (by positivity)
  · have hp := nAll8_sound hP u hu
    simp only [Nat.ble_eq] at hp
    rw [rlPS_tcTab _ _ _ _ hTs, rlPS_tcTab _ _ _ _ hu, ← sub_div]
    have : (tcPSN w.bw w.md w.W u : ℚ) ≤ tcPSN w.bw w.md w.W Ts := by exact_mod_cast hp
    exact div_nonneg (by linarith) hDq.le

/-- **The real budget** of a cell: every competitor `c ≠ 0` (bit `i` = unit `i` OFF) has `e_hi(c) ≤ e_lo`
and `B ≤ 3 log 2 (e_lo - e_hi(c))`, where `e_lo = (x_lo - 1/1000)³` and `e_hi(c)` is the product bound over
`x_i ∈ [x_lo - 1/1000, x_hi + 1/1000]`. -/
def TcBudget (b : TcBox) (B : ℚ) : Prop :=
  ∀ c, 0 < c → c < 8 → tcEhi b c ≤ tcLx b ^ 3 ∧
    (B : ℝ) ≤ 3 * Real.log 2 * (((tcLx b : ℚ) : ℝ) ^ 3 - ((tcEhi b c : ℚ) : ℝ))

theorem tcBudB_sound {b : TcBox} {B : ℚ} (h : tcBudB b B = true) : TcBudget b B := by
  intro c hc0 hc8
  simp only [tcBudB, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h (c - 1) (by omega)
  rw [Nat.sub_add_cancel hc0] at h1 h2
  refine ⟨h1, ?_⟩
  have hl := crL2lo_lt
  have h2' : (B : ℝ) ≤ 3 * (crL2lo : ℝ) * (((tcLx b : ℚ) : ℝ) ^ 3 - ((tcEhi b c : ℚ) : ℝ)) := by
    exact_mod_cast h2
  have hnn : (0 : ℝ) ≤ ((tcLx b : ℚ) : ℝ) ^ 3 - ((tcEhi b c : ℚ) : ℝ) := by
    have : ((tcEhi b c : ℚ) : ℝ) ≤ ((tcLx b ^ 3 : ℚ) : ℝ) := by exact_mod_cast h1
    push_cast at this; linarith
  nlinarith

/-- **Soundness of the cell checker**: at every vertex of the cell an admissible table with the effect
conditions, at every ray a homogeneous table, `Ts < 8`, `Q > 0`, and the real budget. -/
theorem tcCellOK_sound {tn td : ℕ} (htd : 0 < td) {C : TcCell} (h : tcCellOK tn td C = true) :
    (∀ v ∈ tcVerts C.box, ∃ M Y : Fin 8 → Fin 3 → ℚ,
      rlTcAdm v ((tn : ℚ) / td) C.Ts M Y ∧
        rlTcEff v ((tn : ℚ) / td) ((C.Bn : ℚ) / C.Bd) (tcDesig C.dg) Y) ∧
    (∀ r ∈ tcRays C.box, ∃ M, rlRay r C.Ts M) ∧ C.Ts < 8 ∧ 0 < C.box.Q ∧
      TcBudget C.box ((C.Bn : ℚ) / C.Bd) := by
  simp only [tcCellOK, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hTs, hQ⟩, hBd⟩, hdes⟩, hbud⟩, hv⟩, hr⟩ := h
  have hdes' : ∀ R < 8, R ≠ 0 → tcDesig C.dg R < 3 := by
    intro R hR hR0
    have := nAll8_sound hdes R hR
    simp only [Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at this
    exact this.resolve_left hR0
  refine ⟨fun v hv' => ?_, fun r hr' => ?_, hTs, hQ, tcBudB_sound hbud⟩
  · obtain ⟨vn, hvn, rfl⟩ := List.mem_map.1 hv'
    obtain ⟨w, -, hw⟩ := tcAllZip_sound hv vn hvn
    exact ⟨_, _, tcVertB_sound htd hTs hQ hBd hdes' hw⟩
  · obtain ⟨rn, hrn, rfl⟩ := List.mem_map.1 hr'
    obtain ⟨w, -, hw⟩ := tcAllZip_sound hr rn hrn
    exact ⟨_, tcRayB_sound hTs hw⟩

end Census
end IIT
