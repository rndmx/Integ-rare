/-
Census, B1 LTBetaHi, module T3 (part 2): soundness of the RL checker and the linear combination lemmas
(W8 §4 (R1) convexity / rays, (R2) interpolation in `t`).
-/
import IIT.Census.B1LTHiCertRL

namespace IIT
namespace Census

/-- Linear combination of data. -/
def RLD.lc (a b : ℚ) (d e : RLD) : RLD :=
  ⟨a * d.G1 + b * e.G1, a * d.F1 + b * e.F1, a * d.G2 + b * e.G2, a * d.F2 + b * e.F2,
    a * d.V1 + b * e.V1, a * d.V2 + b * e.V2⟩

/-- Linear combination of tables. -/
def rlLC (a b : ℚ) (M M' : Fin 8 → Fin 3 → ℚ) : Fin 8 → Fin 3 → ℚ := fun u i => a * M u i + b * M' u i

/-- **Admissibility** (with `c = G1`, i.e. `G1 ≤ 1`). -/
def rlAdm (d : RLD) (t : ℚ) (Ts : ℕ) (M : Fin 8 → Fin 3 → ℚ) : Prop :=
  (∀ u < 8, ∀ i < 3, rlLo d u i ≤ rlM M u i ∧ rlM M u i ≤ rlLo d u i + rlWd d u i) ∧
  8 * d.G1 * (5 / 3 - t) ≤ rlV8 lp3CStar Ts M ∧
  (∀ C ∈ lp3Profiles, C ≠ lp3CStar →
    1 / 20 * d.G1 * t ≤ rlV8 C Ts M / (8 * (cd_cc 3 C : ℚ)) - rlV8 lp3CStar Ts M / 40) ∧
  (∀ u < 8, u ≠ Ts → 1 / 20 ≤ rlPS M Ts - rlPS M u)

/-- **Ray admissibility** (homogeneous). -/
def rlRay (d : RLD) (Ts : ℕ) (M : Fin 8 → Fin 3 → ℚ) : Prop :=
  (∀ u < 8, ∀ i < 3, rlLo d u i ≤ rlM M u i ∧ rlM M u i ≤ rlLo d u i + rlWd d u i) ∧
  0 ≤ rlV8 lp3CStar Ts M ∧
  (∀ C ∈ lp3Profiles, C ≠ lp3CStar → 0 ≤ rlV8 C Ts M / (8 * (cd_cc 3 C : ℚ)) - rlV8 lp3CStar Ts M / 40) ∧
  (∀ u < 8, u ≠ Ts → 0 ≤ rlPS M Ts - rlPS M u)

lemma rlBox_sound {d : RLD} {M : Fin 8 → Fin 3 → ℚ} (h : rlBox d M = true) :
    ∀ u < 8, ∀ i < 3, rlLo d u i ≤ rlM M u i ∧ rlM M u i ≤ rlLo d u i + rlWd d u i := by
  intro u hu i hi
  simp only [rlBox, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h u hu i hi

/-- **Soundness of the vertex checker.** -/
theorem rlAdmB_sound {d : RLD} {t : ℚ} {Ts : ℕ} {M : Fin 8 → Fin 3 → ℚ} (hG : d.G1 ≤ 1)
    (h : rlAdmB d t Ts M = true) : rlAdm d t Ts M := by
  have hc : min 1 d.G1 = d.G1 := min_eq_right hG
  simp only [rlAdmB, hc, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hbox, hV⟩, hG'⟩, hP⟩ := h
  refine ⟨rlBox_sound hbox, hV, fun C hC hne => ?_, fun u hu hne => ?_⟩
  · simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hG'
    exact (hG' C hC).resolve_left hne
  · simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hP
    exact (hP u hu).resolve_left hne

/-- **Soundness of the ray checker.** -/
theorem rlRayB_sound {d : RLD} {Ts : ℕ} {M : Fin 8 → Fin 3 → ℚ} (h : rlRayB d Ts M = true) : rlRay d Ts M := by
  simp only [rlRayB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hbox, hV⟩, hG'⟩, hP⟩ := h
  refine ⟨rlBox_sound hbox, hV, fun C hC hne => ?_, fun u hu hne => ?_⟩
  · simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hG'
    exact (hG' C hC).resolve_left hne
  · simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hP
    exact (hP u hu).resolve_left hne

/-! ### Linearity -/

lemma rlLo_lc (a b : ℚ) (d e : RLD) (u i : ℕ) : rlLo (RLD.lc a b d e) u i = a * rlLo d u i + b * rlLo e u i := by
  unfold rlLo RLD.lc; split_ifs <;> simp

lemma rlWd_lc (a b : ℚ) (d e : RLD) (u i : ℕ) : rlWd (RLD.lc a b d e) u i = a * rlWd d u i + b * rlWd e u i := by
  unfold rlWd RLD.lc; split_ifs <;> simp <;> ring

lemma rlM_lc (a b : ℚ) (M M' : Fin 8 → Fin 3 → ℚ) (u i : ℕ) :
    rlM (rlLC a b M M') u i = a * rlM M u i + b * rlM M' u i := rfl

lemma rlV8_lc (C : List (List Bool)) (Ts : ℕ) (a b : ℚ) (M M' : Fin 8 → Fin 3 → ℚ) :
    rlV8 C Ts (rlLC a b M M') = a * rlV8 C Ts M + b * rlV8 C Ts M' := by
  simp only [rlV8, rlS3, rlS8, rlM_lc]; ring

lemma rlPS_lc (a b : ℚ) (M M' : Fin 8 → Fin 3 → ℚ) (u : ℕ) :
    rlPS (rlLC a b M M') u = a * rlPS M u + b * rlPS M' u := by
  simp only [rlPS, rlS3, rlM_lc]; ring

/-- **(R1) Convex combination** of two admissible configurations (same `t`, same target). -/
theorem rlAdm_conv {d e : RLD} {t : ℚ} {Ts : ℕ} {M M' : Fin 8 → Fin 3 → ℚ} (hd : rlAdm d t Ts M)
    (he : rlAdm e t Ts M') {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    rlAdm (RLD.lc a b d e) t Ts (rlLC a b M M') := by
  obtain ⟨b1, v1, g1, p1⟩ := hd
  obtain ⟨b2, v2, g2, p2⟩ := he
  refine ⟨fun u hu i hi => ?_, ?_, fun C hC hne => ?_, fun u hu hne => ?_⟩
  · rw [rlLo_lc, rlWd_lc, rlM_lc]
    obtain ⟨l1, h1⟩ := b1 u hu i hi; obtain ⟨l2, h2⟩ := b2 u hu i hi
    constructor <;> nlinarith
  · rw [rlV8_lc]; simp only [RLD.lc]; nlinarith
  · rw [rlV8_lc, rlV8_lc]; simp only [RLD.lc]
    have := g1 C hC hne; have := g2 C hC hne
    have hcc : (0 : ℚ) < 8 * (cd_cc 3 C : ℚ) := by
      have := profiles3_cc_pos C (by simpa [profiles3] using hC); positivity
    rw [add_div, mul_div_assoc, mul_div_assoc]
    nlinarith
  · rw [rlPS_lc, rlPS_lc]
    have := p1 u hu hne; have := p2 u hu hne
    nlinarith

/-- **(R1) Adding a ray** (with `dG1 = 0`). -/
theorem rlAdm_ray {d r : RLD} {t : ℚ} {Ts : ℕ} {M R : Fin 8 → Fin 3 → ℚ} (hd : rlAdm d t Ts M)
    (hr : rlRay r Ts R) (hr0 : r.G1 = 0) {μ : ℚ} (hμ : 0 ≤ μ) :
    rlAdm (RLD.lc 1 μ d r) t Ts (rlLC 1 μ M R) := by
  obtain ⟨b1, v1, g1, p1⟩ := hd
  obtain ⟨b2, v2, g2, p2⟩ := hr
  refine ⟨fun u hu i hi => ?_, ?_, fun C hC hne => ?_, fun u hu hne => ?_⟩
  · rw [rlLo_lc, rlWd_lc, rlM_lc]
    obtain ⟨l1, h1⟩ := b1 u hu i hi; obtain ⟨l2, h2⟩ := b2 u hu i hi
    constructor <;> nlinarith
  · rw [rlV8_lc]; simp only [RLD.lc, hr0]; nlinarith
  · rw [rlV8_lc, rlV8_lc]; simp only [RLD.lc, hr0]
    have := g1 C hC hne; have := g2 C hC hne
    rw [add_div, mul_div_assoc, mul_div_assoc]
    nlinarith
  · rw [rlPS_lc, rlPS_lc]
    have := p1 u hu hne; have := p2 u hu hne
    nlinarith

/-- **(R2) Interpolation in `t`** (same data, same target). -/
theorem rlAdm_interp {d : RLD} {T : ℚ} {Ts : ℕ} {M0 MT : Fin 8 → Fin 3 → ℚ} (h0 : rlAdm d 0 Ts M0)
    (hT : rlAdm d T Ts MT) (hG : 0 ≤ d.G1) {l : ℚ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    rlAdm d (l * T) Ts (rlLC (1 - l) l M0 MT) := by
  obtain ⟨b1, v1, g1, p1⟩ := h0
  obtain ⟨b2, v2, g2, p2⟩ := hT
  refine ⟨fun u hu i hi => ?_, ?_, fun C hC hne => ?_, fun u hu hne => ?_⟩
  · rw [rlM_lc]
    obtain ⟨l1, h1⟩ := b1 u hu i hi; obtain ⟨l2, h2⟩ := b2 u hu i hi
    constructor <;> nlinarith
  · rw [rlV8_lc]; nlinarith
  · rw [rlV8_lc, rlV8_lc]
    have := g1 C hC hne; have := g2 C hC hne
    rw [add_div, mul_div_assoc, mul_div_assoc]
    nlinarith
  · rw [rlPS_lc, rlPS_lc]
    have := p1 u hu hne; have := p2 u hu hne
    nlinarith

end Census
end IIT
