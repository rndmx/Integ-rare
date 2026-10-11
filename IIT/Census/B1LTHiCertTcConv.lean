/-
Census, B1 LTBetaHi, RL-tc certificate (W8 §8.1, (R1)), part 1b: the linear structure of the RL-tc conditions.

For a fixed level `t`, target `Ts`, budget `B` and designations, the RL-tc conditions are linear in
`(d, M, Y)`: a convex combination of two admissible configurations is admissible (`rlTcAdm_conv`,
`rlTcEff_conv`); adding a non-negative multiple of a homogeneous ray table (`rlRay`, increments of the rest data
only, `Y` unchanged) keeps admissibility (`rlTcAdm_ray`; the effect conditions only read `x, f, Y`:
`rlTcEff_rest`); and admissibility is monotone in the rest weights `V1, V2` (`rlTcAdm_monoV`). These are the
steps that turn the vertex/ray witnesses of a cell (`tcCellsAll_sound`) into a witness at every point of it.
-/
import IIT.Census.B1LTHiCertTc

namespace IIT
namespace Census

/-- Linear combination of RL-tc data. -/
def RLTcD.lc (a b : ℚ) (d e : RLTcD) : RLTcD :=
  ⟨a * d.G1 + b * e.G1, a * d.F1 + b * e.F1, a * d.G2 + b * e.G2, a * d.F2 + b * e.F2,
    a * d.V1 + b * e.V1, a * d.V2 + b * e.V2, a * d.x + b * e.x, a * d.f + b * e.f⟩

/-- Adding `μ` times a ray of the rest data (tc's entries unchanged). -/
def RLTcD.addRay (d : RLTcD) (μ : ℚ) (r : RLD) : RLTcD :=
  ⟨d.G1 + μ * r.G1, d.F1 + μ * r.F1, d.G2 + μ * r.G2, d.F2 + μ * r.F2, d.V1 + μ * r.V1, d.V2 + μ * r.V2,
    d.x, d.f⟩

lemma RLTcD.lc_rest (a b : ℚ) (d e : RLTcD) : (d.lc a b e).rest = RLD.lc a b d.rest e.rest := rfl

lemma RLTcD.addRay_rest (d : RLTcD) (μ : ℚ) (r : RLD) : (d.addRay μ r).rest = RLD.lc 1 μ d.rest r := by
  simp [RLTcD.addRay, RLTcD.rest, RLD.lc]

lemma rlTcEnt_lc (a b : ℚ) (d e : RLTcD) (Y Y' : Fin 8 → Fin 3 → ℚ) (u i : ℕ) :
    rlTcEnt (d.lc a b e) (rlLC a b Y Y') u i = a * rlTcEnt d Y u i + b * rlTcEnt e Y' u i := by
  unfold rlTcEnt RLTcD.lc
  split_ifs <;> simp [rlM_lc]

/-- **Convex combination** of two cause-admissible configurations (same `t`, same target). -/
theorem rlTcAdm_conv {d e : RLTcD} {t : ℚ} {Ts : ℕ} {M M' Y Y' : Fin 8 → Fin 3 → ℚ}
    (hd : rlTcAdm d t Ts M Y) (he : rlTcAdm e t Ts M' Y') {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : rlTcAdm (d.lc a b e) t Ts (rlLC a b M M') (rlLC a b Y Y') := by
  obtain ⟨b1, y1, v1, g1, p1⟩ := hd
  obtain ⟨b2, y2, v2, g2, p2⟩ := he
  refine ⟨fun u hu i hi => ?_, fun u hu i hi h0 h1 => ?_, ?_, fun C hC hne => ?_, fun u hu hne => ?_⟩
  · rw [RLTcD.lc_rest, rlLo_lc, rlWd_lc, rlM_lc, rlTcEnt_lc]
    obtain ⟨l1, u1⟩ := b1 u hu i hi; obtain ⟨l2, u2⟩ := b2 u hu i hi
    constructor <;> nlinarith
  · rw [rlM_lc]
    obtain ⟨l1, u1⟩ := y1 u hu i hi h0 h1; obtain ⟨l2, u2⟩ := y2 u hu i hi h0 h1
    constructor <;> nlinarith
  · rw [rlV8_lc]; simp only [RLTcD.lc]; nlinarith
  · rw [rlV8_lc, rlV8_lc]; simp only [RLTcD.lc]
    have := g1 C hC hne; have := g2 C hC hne
    rw [add_div, mul_div_assoc, mul_div_assoc]
    nlinarith
  · rw [rlPS_lc, rlPS_lc]
    have := p1 u hu hne; have := p2 u hu hne
    nlinarith

/-- **Convex combination** of the effect conditions (same `t`, `B`, designations). -/
theorem rlTcEff_conv {d e : RLTcD} {t B : ℚ} {desig : ℕ → ℕ} {Y Y' : Fin 8 → Fin 3 → ℚ}
    (hd : rlTcEff d t B desig Y) (he : rlTcEff e t B desig Y') {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : rlTcEff (d.lc a b e) t B desig (rlLC a b Y Y') := by
  obtain ⟨e1, d1, s1⟩ := hd
  obtain ⟨e2, -, s2⟩ := he
  refine ⟨fun R hR hR0 i hi hbit => ?_, d1, ?_⟩
  · rw [rlM_lc]; simp only [RLTcD.lc]
    have h1 := mul_le_mul_of_nonneg_left (e1 R hR hR0 i hi hbit) ha
    have h2 := mul_le_mul_of_nonneg_left (e2 R hR hR0 i hi hbit) hb
    have h3 : a * t + b * t = t := by rw [← add_mul, hab, one_mul]
    linarith
  · simp only [rlTcEnt_lc]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left s1 ha
    have h2 := mul_le_mul_of_nonneg_left s2 hb
    have h3 : a * B + b * B = B := by rw [← add_mul, hab, one_mul]
    linarith

/-- **Adding a ray** (increments of the rest data, homogeneous table, `Y` unchanged). -/
theorem rlTcAdm_ray {d : RLTcD} {t : ℚ} {Ts : ℕ} {M Y R : Fin 8 → Fin 3 → ℚ} {r : RLD}
    (hd : rlTcAdm d t Ts M Y) (hr : rlRay r Ts R) {μ : ℚ} (hμ : 0 ≤ μ) :
    rlTcAdm (d.addRay μ r) t Ts (rlLC 1 μ M R) Y := by
  obtain ⟨b1, y1, v1, g1, p1⟩ := hd
  obtain ⟨b2, v2, g2, p2⟩ := hr
  have hent : ∀ u i, rlTcEnt (d.addRay μ r) Y u i = rlTcEnt d Y u i := fun u i => by
    simp [rlTcEnt, RLTcD.addRay]
  refine ⟨fun u hu i hi => ?_, y1, ?_, fun C hC hne => ?_, fun u hu hne => ?_⟩
  · rw [RLTcD.addRay_rest, rlLo_lc, rlWd_lc, rlM_lc, hent]
    obtain ⟨l1, u1⟩ := b1 u hu i hi; obtain ⟨l2, u2⟩ := b2 u hu i hi
    constructor <;> nlinarith
  · rw [rlV8_lc]; simp only [RLTcD.addRay]; nlinarith
  · rw [rlV8_lc, rlV8_lc]; simp only [RLTcD.addRay]
    have := g1 C hC hne; have := g2 C hC hne
    rw [add_div, mul_div_assoc, mul_div_assoc]
    nlinarith
  · rw [rlPS_lc, rlPS_lc]
    have := p1 u hu hne; have := p2 u hu hne
    nlinarith

/-- The effect conditions only read tc's entries: adding a ray keeps them. -/
theorem rlTcEff_rest {d : RLTcD} {t B : ℚ} {desig : ℕ → ℕ} {Y : Fin 8 → Fin 3 → ℚ}
    (hd : rlTcEff d t B desig Y) (μ : ℚ) (r : RLD) : rlTcEff (d.addRay μ r) t B desig Y := by
  have hent : ∀ u i, rlTcEnt (d.addRay μ r) Y u i = rlTcEnt d Y u i := fun u i => by
    simp [rlTcEnt, RLTcD.addRay]
  obtain ⟨e1, d1, s1⟩ := hd
  exact ⟨fun R hR hR0 i hi hb => by simpa [RLTcD.addRay] using e1 R hR hR0 i hi hb, d1,
    by simpa only [hent] using s1⟩

/-- **Monotonicity in the rest weights** `V1, V2`. -/
theorem rlTcAdm_monoV {d : RLTcD} {t : ℚ} {Ts : ℕ} {M Y : Fin 8 → Fin 3 → ℚ} (hd : rlTcAdm d t Ts M Y)
    {V1 V2 : ℚ} (h1 : d.V1 ≤ V1) (h2 : d.V2 ≤ V2) :
    rlTcAdm ⟨d.G1, d.F1, d.G2, d.F2, V1, V2, d.x, d.f⟩ t Ts M Y := by
  obtain ⟨b1, y1, v1, g1, p1⟩ := hd
  refine ⟨fun u hu i hi => ?_, y1, v1, g1, p1⟩
  obtain ⟨l1, u1⟩ := b1 u hu i hi
  have hent : rlTcEnt ⟨d.G1, d.F1, d.G2, d.F2, V1, V2, d.x, d.f⟩ Y u i = rlTcEnt d Y u i := by
    simp [rlTcEnt]
  have hwd : rlWd d.rest u i ≤ rlWd (⟨d.G1, d.F1, d.G2, d.F2, V1, V2, d.x, d.f⟩ : RLTcD).rest u i := by
    unfold rlWd RLTcD.rest; dsimp only; split_ifs <;> linarith
  have hlo : rlLo (⟨d.G1, d.F1, d.G2, d.F2, V1, V2, d.x, d.f⟩ : RLTcD).rest u i = rlLo d.rest u i := rfl
  rw [hent, hlo]
  exact ⟨l1, by linarith⟩

/-- The effect conditions do not read `V1, V2`. -/
theorem rlTcEff_monoV {d : RLTcD} {t B : ℚ} {desig : ℕ → ℕ} {Y : Fin 8 → Fin 3 → ℚ}
    (hd : rlTcEff d t B desig Y) (V1 V2 : ℚ) :
    rlTcEff ⟨d.G1, d.F1, d.G2, d.F2, V1, V2, d.x, d.f⟩ t B desig Y := by
  have hent : ∀ u i, rlTcEnt ⟨d.G1, d.F1, d.G2, d.F2, V1, V2, d.x, d.f⟩ Y u i = rlTcEnt d Y u i :=
    fun u i => by simp [rlTcEnt]
  obtain ⟨e1, d1, s1⟩ := hd
  exact ⟨e1, d1, by simpa only [hent] using s1⟩

end Census
end IIT
