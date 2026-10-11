/-
Census, B1 LTBetaHi, RL-u certificate (W8 §7.1', §8.3, W11 §0), part 1: the data model, the cell checker and its
vertex soundness.

Model (u := s, a special row `≠ tc`, bounded domain `D_u^b`): rest data `(G1, F1, V1)` (block 1, INCLUDING tc),
`(G2, F2, V2)` (block 2), and u's weight `w = P(u)/P(tc)`, offset `D_u ∈ {∅, S}` (`ds`), shared entries `x = y_{u,i}`,
`f = y_{u^i,i}` and private entries `Y R i` (pattern `R` relative to `u`). The merged table `M u i` minus `w` times
u's entry at `R = u ⊕ D_u` lies in the rest interval; (V), (G), (P) at level `c = G1`; the effect conditions are
those of RL-tc in the frame of row `u`. Primitives (packed tables, profiles by cut masks, budget) are those of
`B1LTHiCertTc`.
-/
import IIT.Census.B1LTHiCertTc

namespace IIT
namespace Census

/-! ### The RL-u data model (ℚ) -/

/-- RL-u data. -/
structure RLUD where
  G1 : ℚ
  F1 : ℚ
  G2 : ℚ
  F2 : ℚ
  V1 : ℚ
  V2 : ℚ
  w : ℚ
  x : ℚ
  f : ℚ

/-- The rest blocks as two-block data. -/
def RLUD.rest (d : RLUD) : RLD := ⟨d.G1, d.F1, d.G2, d.F2, d.V1, d.V2⟩

/-- The offset mask of u (`0` for `D_u = ∅`, `7` for `D_u = S`). -/
def uOff (ds : Bool) : ℕ := if ds then 7 else 0

/-- u's entry at its own pattern `R`, column `i` (shared `x`, `f`; private `Y`). -/
def rlUEnt (d : RLUD) (Y : Fin 8 → Fin 3 → ℚ) (R i : ℕ) : ℚ :=
  if R = 0 then d.x else if R = rlBit i then d.f else rlM Y R i

/-- **Cause admissibility** of `(M, Y)` for RL-u at level `t`, target `Ts` (`c = G1`). -/
def rlUAdm (ds : Bool) (d : RLUD) (t : ℚ) (Ts : ℕ) (M Y : Fin 8 → Fin 3 → ℚ) : Prop :=
  (∀ u < 8, ∀ i < 3, rlLo d.rest u i ≤ rlM M u i - d.w * rlUEnt d Y (u ^^^ uOff ds) i ∧
      rlM M u i - d.w * rlUEnt d Y (u ^^^ uOff ds) i ≤ rlLo d.rest u i + rlWd d.rest u i) ∧
  (∀ R < 8, ∀ i < 3, R ≠ 0 → R ≠ rlBit i → 0 ≤ rlM Y R i ∧ rlM Y R i ≤ 1) ∧
  8 * d.G1 * (5 / 3 - t) ≤ rlV8 lp3CStar Ts M ∧
  (∀ C ∈ lp3Profiles, C ≠ lp3CStar →
    1 / 20 * d.G1 * t ≤ rlV8 C Ts M / (8 * (cd_cc 3 C : ℚ)) - rlV8 lp3CStar Ts M / 40) ∧
  (∀ u < 8, u ≠ Ts → 1 / 20 ≤ rlPS M Ts - rlPS M u)

/-- **Effect conditions** (Lemma EFG, `te` = all ON, frame of row `u`). -/
def rlUEff (d : RLUD) (t B : ℚ) (desig : ℕ → ℕ) (Y : Fin 8 → Fin 3 → ℚ) : Prop :=
  (∀ R < 8, R ≠ 0 → ∀ i < 3, R.testBit i = false → rlM Y R i ≤ d.x - t / 100) ∧
  (∀ R < 8, R ≠ 0 → desig R < 3) ∧
  ∑ R ∈ Finset.range 7, rlUEnt d Y (R + 1) (desig (R + 1)) ≤ B - 1 / 500

/-! ### Witnesses and the vertex checker -/

/-- A vertex witness, scaled by `D` (as `TcWit`, plus u's weight `w`). -/
structure UWit where
  D : ℕ
  G1 : ℕ
  F1 : ℕ
  G2 : ℕ
  F2 : ℕ
  V1 : ℕ
  V2 : ℕ
  w : ℕ
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

/-- Scaled u entry at its own pattern `R`. -/
def uEntN (w : UWit) (R i : ℕ) : ℕ :=
  cond (Nat.beq R 0) w.x (cond (Nat.beq R (Nat.pow 2 i)) w.f (tcAt w.bw w.md w.Y R i))

/-- Box (times `D`: `D lo + w ent ≤ D M ≤ D (lo + wd) + w ent`) and `Y ≤ 1` at the private positions. -/
def uBoxB (ds : Bool) (w : UWit) : Bool :=
  nAll8 fun u => nAll3 fun i =>
    Nat.ble (Nat.add (Nat.mul w.D (tcLo5 w.G1 w.F1 w.G2 w.F2 u i)) (Nat.mul w.w (uEntN w (u ^^^ uOff ds) i)))
      (Nat.mul w.D (tcAt w.bw w.md w.W u i)) &&
    Nat.ble (Nat.mul w.D (tcAt w.bw w.md w.W u i))
      (Nat.add (Nat.mul w.D (Nat.add (tcLo5 w.G1 w.F1 w.G2 w.F2 u i) (tcWd2 w.V1 w.V2 u i)))
        (Nat.mul w.w (uEntN w (u ^^^ uOff ds) i))) &&
    (Nat.beq u 0 || Nat.beq u (Nat.pow 2 i) || Nat.ble (tcAt w.bw w.md w.Y u i) w.D)

/-- Integer vertex data (over the box denominator `Q`). -/
structure RLUN where
  G1 : ℕ
  F1 : ℕ
  G2 : ℕ
  F2 : ℕ
  V1 : ℕ
  V2 : ℕ
  w : ℕ
  x : ℕ
  f : ℕ

/-- The rational vertex `v / Q`. -/
def RLUN.toQ (v : RLUN) (Q : ℕ) : RLUD :=
  ⟨(v.G1 : ℚ) / Q, (v.F1 : ℚ) / Q, (v.G2 : ℚ) / Q, (v.F2 : ℚ) / Q, (v.V1 : ℚ) / Q, (v.V2 : ℚ) / Q,
    (v.w : ℚ) / Q, (v.x : ℚ) / Q, (v.f : ℚ) / Q⟩

/-- The scaled data of a witness are those of the vertex. -/
def uDataB (Q : ℕ) (v : RLUN) (w : UWit) : Bool :=
  Nat.beq (Nat.mul w.G1 Q) (Nat.mul v.G1 w.D) && Nat.beq (Nat.mul w.F1 Q) (Nat.mul v.F1 w.D) &&
  Nat.beq (Nat.mul w.G2 Q) (Nat.mul v.G2 w.D) && Nat.beq (Nat.mul w.F2 Q) (Nat.mul v.F2 w.D) &&
  Nat.beq (Nat.mul w.V1 Q) (Nat.mul v.V1 w.D) && Nat.beq (Nat.mul w.V2 Q) (Nat.mul v.V2 w.D) &&
  Nat.beq (Nat.mul w.w Q) (Nat.mul v.w w.D) &&
  Nat.beq (Nat.mul w.x Q) (Nat.mul v.x w.D) && Nat.beq (Nat.mul w.f Q) (Nat.mul v.f w.D)

/-- **The vertex checker** at `t = tn/td` (level `c = G1`). -/
def uVertB (ds : Bool) (tn td Ts Bn Bd dg Q : ℕ) (v : RLUN) (w : UWit) : Bool :=
  Nat.blt 0 w.D && uDataB Q v w && uBoxB ds w && tcSubB w.bw w.md w.W Ts w.sw w.smd w.S &&
  Nat.beq (Nat.add w.vs (tcNegS w.sw w.smd w.S tcProfStar)) (Nat.mul 8 (tcPSN w.bw w.md w.W Ts)) &&
  Nat.ble (Nat.mul (Nat.mul 40 w.G1) td) (Nat.add (Nat.mul (Nat.mul 3 td) w.vs) (Nat.mul (Nat.mul 24 w.G1) tn)) &&
  tcProfL.all (fun p => Nat.ble
    (Nat.add (Nat.add (Nat.mul (Nat.mul (Nat.mul 2 p.cc) w.G1) tn) (Nat.mul (Nat.mul p.cc td) w.vs))
      (Nat.mul (Nat.mul 5 td) (tcNegS w.sw w.smd w.S p)))
    (Nat.mul (Nat.mul 40 td) (tcPSN w.bw w.md w.W Ts))) &&
  nAll8 (fun u => Nat.beq u Ts ||
    Nat.ble (Nat.add w.D (Nat.mul 20 (tcPSN w.bw w.md w.W u))) (Nat.mul 20 (tcPSN w.bw w.md w.W Ts))) &&
  nAll8 (fun R => Nat.beq R 0 || nAll3 fun i => Nat.testBit R i ||
    Nat.ble (Nat.add (Nat.mul (Nat.mul 100 td) (tcAt w.bw w.md w.Y R i)) (Nat.mul w.D tn))
      (Nat.mul (Nat.mul 100 td) w.x)) &&
  Nat.ble (Nat.add (Nat.mul (Nat.mul 500 Bd) (nSum7 fun R => uEntN w (R + 1) (tcDesig dg (R + 1))))
      (Nat.mul Bd w.D)) (Nat.mul (Nat.mul 500 Bn) w.D)

/-! ### Soundness of the vertex checker -/

section Vert

variable {w : UWit} {v : RLUN} {Q : ℕ}

lemma uDataB_sound (hQ : 0 < Q) (hD : 0 < w.D) (h : uDataB Q v w = true) :
    (v.toQ Q).G1 = w.G1 / w.D ∧ (v.toQ Q).F1 = w.F1 / w.D ∧ (v.toQ Q).G2 = w.G2 / w.D ∧
      (v.toQ Q).F2 = w.F2 / w.D ∧ (v.toQ Q).V1 = w.V1 / w.D ∧ (v.toQ Q).V2 = w.V2 / w.D ∧
      (v.toQ Q).w = w.w / w.D ∧ (v.toQ Q).x = w.x / w.D ∧ (v.toQ Q).f = w.f / w.D := by
  have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hD' : (w.D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  simp only [uDataB, Bool.and_eq_true, Nat.beq_eq, Nat.mul_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  simp only [RLUN.toQ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [div_eq_div_iff hQ' hD'] <;> exact_mod_cast (by omega)

lemma uEntN_eq {d : RLUD} (hx : d.x = w.x / w.D) (hf : d.f = w.f / w.D) {R i : ℕ} (hR : R < 8)
    (hi : i < 3) : rlUEnt d (tcTab w.bw w.md w.Y w.D) R i = (uEntN w R i : ℚ) / w.D := by
  unfold rlUEnt uEntN rlBit
  simp only [cond_eq_ite, Nat.beq_eq, Nat.pow_eq]
  split_ifs <;> simp [hx, hf, rlM_tcTab _ _ _ _ hR hi]

lemma uOff_lt (ds : Bool) : uOff ds < 8 := by unfold uOff; split_ifs <;> norm_num

/-- **Soundness of the RL-u vertex checker.** -/
theorem uVertB_sound {ds : Bool} {tn td Ts Bn Bd dg : ℕ} (htd : 0 < td) (hTs : Ts < 8) (hQ : 0 < Q)
    (hBd : 0 < Bd) (hdes : ∀ R < 8, R ≠ 0 → tcDesig dg R < 3)
    (h : uVertB ds tn td Ts Bn Bd dg Q v w = true) :
    rlUAdm ds (v.toQ Q) ((tn : ℚ) / td) Ts (tcTab w.bw w.md w.W w.D) (tcTab w.bw w.md w.Y w.D) ∧
      rlUEff (v.toQ Q) ((tn : ℚ) / td) ((Bn : ℚ) / Bd) (tcDesig dg) (tcTab w.bw w.md w.Y w.D) := by
  simp only [uVertB, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hd⟩, hbox⟩, hsub⟩, hvs⟩, hV⟩, hG⟩, hP⟩, hE2⟩, hbud⟩ := h
  have hDq : (0 : ℚ) < w.D := by exact_mod_cast hD
  have htdq : (0 : ℚ) < td := by exact_mod_cast htd
  obtain ⟨e1, e2, e3, e4, e5, e6, ew, hx, hf⟩ := uDataB_sound hQ hD hd
  have hs : ∀ n : ℕ, (n : ℚ) / w.D = n * (1 / w.D) := fun n => by ring
  have hlo : ∀ u i, rlLo (v.toQ Q).rest u i = (tcLo5 w.G1 w.F1 w.G2 w.F2 u i : ℚ) / w.D := fun u i => by
    rw [hs]
    exact tc_lo5 (v.toQ Q).rest (by simp only [RLUD.rest]; rw [e1]; ring)
      (by simp only [RLUD.rest]; rw [e2]; ring) (by simp only [RLUD.rest]; rw [e3]; ring)
      (by simp only [RLUD.rest]; rw [e4]; ring) u i
  have hwd : ∀ u i, rlWd (v.toQ Q).rest u i = (tcWd2 w.V1 w.V2 u i : ℚ) / w.D := fun u i => by
    rw [hs]
    exact tc_wd2 (v.toQ Q).rest (by simp only [RLUD.rest]; rw [e5]; ring)
      (by simp only [RLUD.rest]; rw [e6]; ring) u i
  have hstarM := tcCoefOK_masks tcProfStar_ok
  have hstar : rlV8 lp3CStar Ts (tcTab w.bw w.md w.W w.D) = (w.vs : ℚ) / w.D := by
    rw [rlV8_tc tcProfStar_ok hTs, ← tcNegS_eq hsub hstarM.2.2.1 hstarM.2.2.2.1 hstarM.2.2.2.2.1
      hstarM.2.2.2.2.2.1 hstarM.2.2.2.2.2.2.1 hstarM.2.2.2.2.2.2.2]
    congr 1
    have : ((w.vs + tcNegS w.sw w.smd w.S tcProfStar : ℕ) : ℚ) = ((8 * tcPSN w.bw w.md w.W Ts : ℕ) : ℚ) := by
      simp only [Nat.add_eq, Nat.mul_eq] at hvs; rw [hvs]
    push_cast at this; linarith
  refine ⟨⟨fun u hu i hi => ?_, fun R hR i hi hR0 hRb => ?_, ?_, fun C hC hne => ?_, fun u hu hne => ?_⟩,
    fun R hR hR0 i hi hb => ?_, hdes, ?_⟩
  · -- box
    have hb := nAll3_sound (nAll8_sound hbox u hu) i hi
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.mul_eq] at hb
    obtain ⟨⟨b1, b2⟩, -⟩ := hb
    have hR := tc_xor_lt hu (uOff_lt ds)
    rw [hlo, hwd, uEntN_eq hx hf hR hi, rlM_tcTab _ _ _ _ hu hi, ew]
    have b1' : (w.D : ℚ) * (tcLo5 w.G1 w.F1 w.G2 w.F2 u i : ℚ) + (w.w : ℚ) * (uEntN w (u ^^^ uOff ds) i : ℚ) ≤
        (w.D : ℚ) * (tcAt w.bw w.md w.W u i : ℚ) := by exact_mod_cast b1
    have b2' : (w.D : ℚ) * (tcAt w.bw w.md w.W u i : ℚ) ≤ (w.D : ℚ) * ((tcLo5 w.G1 w.F1 w.G2 w.F2 u i : ℚ) +
        (tcWd2 w.V1 w.V2 u i : ℚ)) + (w.w : ℚ) * (uEntN w (u ^^^ uOff ds) i : ℚ) := by exact_mod_cast b2
    have hD2 : (0 : ℚ) < w.D * w.D := by positivity
    constructor
    · rw [show (tcLo5 w.G1 w.F1 w.G2 w.F2 u i : ℚ) / w.D = (w.D * (tcLo5 w.G1 w.F1 w.G2 w.F2 u i : ℚ)) / (w.D * w.D) by
          field_simp,
        show (tcAt w.bw w.md w.W u i : ℚ) / w.D - (w.w : ℚ) / w.D * ((uEntN w (u ^^^ uOff ds) i : ℚ) / w.D) =
          (w.D * (tcAt w.bw w.md w.W u i : ℚ) - w.w * (uEntN w (u ^^^ uOff ds) i : ℚ)) / (w.D * w.D) by
          field_simp]
      exact div_le_div_of_nonneg_right (by linarith) hD2.le
    · rw [show (tcAt w.bw w.md w.W u i : ℚ) / w.D - (w.w : ℚ) / w.D * ((uEntN w (u ^^^ uOff ds) i : ℚ) / w.D) =
          (w.D * (tcAt w.bw w.md w.W u i : ℚ) - w.w * (uEntN w (u ^^^ uOff ds) i : ℚ)) / (w.D * w.D) by
          field_simp,
        show (tcLo5 w.G1 w.F1 w.G2 w.F2 u i : ℚ) / w.D + (tcWd2 w.V1 w.V2 u i : ℚ) / w.D =
          (w.D * ((tcLo5 w.G1 w.F1 w.G2 w.F2 u i : ℚ) + (tcWd2 w.V1 w.V2 u i : ℚ))) / (w.D * w.D) by
          field_simp]
      exact div_le_div_of_nonneg_right (by linarith) hD2.le
  · -- Y range
    have hb := nAll3_sound (nAll8_sound hbox R hR) i hi
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.pow_eq] at hb
    obtain ⟨-, (h0 | h0) | h3⟩ := hb
    · exact absurd h0 hR0
    · exact absurd h0 (by simpa [rlBit] using hRb)
    · rw [rlM_tcTab _ _ _ _ hR hi]
      exact ⟨by positivity, (div_le_one hDq).2 (by exact_mod_cast h3)⟩
  · -- (V)
    rw [hstar, e1]
    have h' : (40 * (w.G1 : ℚ) * td) ≤ 3 * td * w.vs + 24 * w.G1 * tn := by
      simp only [Nat.add_eq, Nat.mul_eq] at hV; exact_mod_cast hV
    have e : 8 * ((w.G1 : ℚ) / w.D) * (5 / 3 - (tn : ℚ) / td) =
        (8 * (w.G1 : ℚ) * (5 * td - 3 * tn)) / (3 * td * w.D) := by
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
    rw [rlV8_tc hpC hTs, hstar, e1, ← hpm.1]
    have hcc : (0 : ℚ) < p.cc := by exact_mod_cast hpm.2.1
    have h' : 2 * (p.cc : ℚ) * w.G1 * tn + p.cc * td * w.vs + 5 * td * (tcNeg w.bw w.md w.W Ts p : ℚ) ≤
        40 * td * (tcPSN w.bw w.md w.W Ts : ℚ) := by
      simp only [Nat.add_eq, Nat.mul_eq] at hg; exact_mod_cast hg
    have e1' : 1 / 20 * ((w.G1 : ℚ) / w.D) * ((tn : ℚ) / td) =
        (2 * (p.cc : ℚ) * w.G1 * tn) / (40 * p.cc * td * w.D) := by
      field_simp; ring
    have e2' : (8 * (tcPSN w.bw w.md w.W Ts : ℚ) - (tcNeg w.bw w.md w.W Ts p : ℚ)) / w.D / (8 * (p.cc : ℚ)) -
        (w.vs : ℚ) / w.D / 40 = (5 * td * (8 * (tcPSN w.bw w.md w.W Ts : ℚ) - (tcNeg w.bw w.md w.W Ts p : ℚ)) -
          p.cc * td * w.vs) / (40 * p.cc * td * w.D) := by
      field_simp; ring
    rw [e1', e2']
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
    have hsum : ∑ R ∈ Finset.range 7, rlUEnt (v.toQ Q) (tcTab w.bw w.md w.Y w.D) (R + 1) (tcDesig dg (R + 1)) =
        ((nSum7 fun R => uEntN w (R + 1) (tcDesig dg (R + 1)) : ℕ) : ℚ) / w.D := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, nSum7, Nat.add_eq]
      rw [uEntN_eq hx hf (by norm_num) (hdes 1 (by norm_num) (by norm_num)),
        uEntN_eq hx hf (by norm_num) (hdes 2 (by norm_num) (by norm_num)),
        uEntN_eq hx hf (by norm_num) (hdes 3 (by norm_num) (by norm_num)),
        uEntN_eq hx hf (by norm_num) (hdes 4 (by norm_num) (by norm_num)),
        uEntN_eq hx hf (by norm_num) (hdes 5 (by norm_num) (by norm_num)),
        uEntN_eq hx hf (by norm_num) (hdes 6 (by norm_num) (by norm_num)),
        uEntN_eq hx hf (by norm_num) (hdes 7 (by norm_num) (by norm_num))]
      push_cast; ring
    rw [hsum, div_le_iff₀ hDq]
    have hBdq : (0 : ℚ) < Bd := by exact_mod_cast hBd
    have h' : 500 * (Bd : ℚ) * ((nSum7 fun R => uEntN w (R + 1) (tcDesig dg (R + 1)) : ℕ) : ℚ) +
        Bd * w.D ≤ 500 * Bn * w.D := by
      simp only [Nat.add_eq, Nat.mul_eq] at hbud; exact_mod_cast hbud
    have e : ((Bn : ℚ) / Bd - 1 / 500) * w.D = (500 * Bn * w.D - Bd * w.D) / (500 * Bd) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith

end Vert

end Census
end IIT
