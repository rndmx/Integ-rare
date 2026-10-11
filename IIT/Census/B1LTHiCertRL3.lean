/-
Census, B1 LTBetaHi, module T3 (part 3): **Theorem RL_sym** (W8 §5) on the reduced domain `D_red`.

For `G1 ∈ [4/5, 1]`, `F1 ≥ 0`, `V1 ≥ max(1, F1)`, `G2, F2 ≥ 0`, `V2 ≥ max(G2, F2)` and `t ∈ [0, 1/80]` there is an
admissible table: cell 1 (`F1 ≤ 2`, target `Ts = ∅`) and cell 2 (`F1 ≥ 2`, `Ts = {2}`), each a combination of the
kernel-checked vertex witnesses (interpolated in `t`) plus non-negative multiples of the ray witnesses.
-/
import IIT.Census.B1LTHiCertRL2

namespace IIT
namespace Census

lemma RLD.ext' {d e : RLD} (h1 : d.G1 = e.G1) (h2 : d.F1 = e.F1) (h3 : d.G2 = e.G2) (h4 : d.F2 = e.F2)
    (h5 : d.V1 = e.V1) (h6 : d.V2 = e.V2) : d = e := by
  cases d; cases e; simp_all

lemma rlAdm_congr {d e : RLD} {t : ℚ} {Ts : ℕ} {M : Fin 8 → Fin 3 → ℚ} (h : rlAdm d t Ts M) (he : d = e) :
    rlAdm e t Ts M := he ▸ h

/-- A vertex witness at every `t ∈ [0, 1/80]`. -/
lemma rl_vertex_t {dv : RLD} {Ts : ℕ} {M0 MT : Fin 8 → Fin 3 → ℚ} (h0 : rlAdm dv 0 Ts M0)
    (hT : rlAdm dv (1 / 80) Ts MT) (hG : 0 ≤ dv.G1) {t : ℚ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 80) :
    rlAdm dv t Ts (rlLC (1 - 80 * t) (80 * t) M0 MT) := by
  have h := rlAdm_interp h0 hT hG (l := 80 * t) (by linarith) (by linarith)
  rwa [show 80 * t * (1 / 80) = t by ring] at h

/-- The zero witness of the rays `e_V1`, `e_V2`. -/
def rlZ : Fin 8 → Fin 3 → ℚ := fun _ _ => 0
def rlEV1 : RLD := ⟨0, 0, 0, 0, 1, 0⟩
def rlEV2 : RLD := ⟨0, 0, 0, 0, 0, 1⟩
theorem rl_eV1_0 : rlRayB rlEV1 0 rlZ = true := by decide +kernel
theorem rl_eV2_0 : rlRayB rlEV2 0 rlZ = true := by decide +kernel
theorem rl_eV1_4 : rlRayB rlEV1 4 rlZ = true := by decide +kernel
theorem rl_eV2_4 : rlRayB rlEV2 4 rlZ = true := by decide +kernel

/-- The `(G2, F2, V2)` part: add the three rays and `e_V2`. -/
lemma rl_add_GF {d : RLD} {t : ℚ} {Ts : ℕ} {M : Fin 8 → Fin 3 → ℚ} (h : rlAdm d t Ts M)
    (hd2 : d.G2 = 0 ∧ d.F2 = 0 ∧ d.V2 = 0)
    {rG rF rGF : RLD} {MG MF MGF : Fin 8 → Fin 3 → ℚ}
    (hrG : rlRay rG Ts MG) (hrF : rlRay rF Ts MF) (hrGF : rlRay rGF Ts MGF) (hrV : rlRay rlEV2 Ts rlZ)
    (eG : rG = ⟨0, 0, 1, 0, 0, 1⟩) (eF : rF = ⟨0, 0, 0, 1, 0, 1⟩) (eGF : rGF = ⟨0, 0, 1, 1, 0, 1⟩)
    {G2 F2 V2 : ℚ} (hG2 : 0 ≤ G2) (hF2 : 0 ≤ F2) (hV2G : G2 ≤ V2) (hV2F : F2 ≤ V2) :
    ∃ M', rlAdm ⟨d.G1, d.F1, G2, F2, d.V1, V2⟩ t Ts M' := by
  set g := min G2 F2 with hgdef
  have hg1 : g ≤ G2 := min_le_left _ _
  have hg2 : g ≤ F2 := min_le_right _ _
  have hg0 : 0 ≤ g := le_min hG2 hF2
  have hgv : G2 + F2 - g ≤ V2 := by
    rcases le_total G2 F2 with h' | h'
    · rw [hgdef, min_eq_left h']; linarith
    · rw [hgdef, min_eq_right h']; linarith
  have s1 := rlAdm_ray h hrGF (by rw [eGF]) hg0
  have s2 := rlAdm_ray s1 hrG (by rw [eG]) (show 0 ≤ G2 - g by linarith)
  have s3 := rlAdm_ray s2 hrF (by rw [eF]) (show 0 ≤ F2 - g by linarith)
  have s4 := rlAdm_ray s3 hrV rfl (show 0 ≤ V2 - (G2 + F2 - g) by linarith)
  refine ⟨_, rlAdm_congr s4 (RLD.ext' ?_ ?_ ?_ ?_ ?_ ?_)⟩ <;>
    simp only [RLD.lc, eG, eF, eGF, rlEV2, hd2.1, hd2.2.1, hd2.2.2] <;> ring

/-- **Theorem RL_sym** on the reduced domain. -/
theorem rl_sym (d : RLD) (hG1 : 4 / 5 ≤ d.G1) (hG1' : d.G1 ≤ 1) (hF1 : 0 ≤ d.F1) (hV1 : 1 ≤ d.V1)
    (hV1F : d.F1 ≤ d.V1) (hG2 : 0 ≤ d.G2) (hF2 : 0 ≤ d.F2) (hV2G : d.G2 ≤ d.V2) (hV2F : d.F2 ≤ d.V2)
    {t : ℚ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 80) : ∃ Ts M, rlAdm d t Ts M := by
  set lamG := 5 * d.G1 - 4
  have hlam0 : 0 ≤ lamG := by simp only [lamG]; linarith
  have hlam1 : lamG ≤ 1 := by simp only [lamG]; linarith
  -- vertex witnesses at `t`
  have W : ∀ (k0 k1 : ℕ) (dv : RLD) (Ts : ℕ) (M0 MT : Fin 8 → Fin 3 → ℚ), 4 / 5 ≤ dv.G1 → dv.G1 ≤ 1 →
      rlAdmB dv 0 Ts M0 = true → rlAdmB dv (1 / 80) Ts MT = true →
      rlAdm dv t Ts (rlLC (1 - 80 * t) (80 * t) M0 MT) := fun _ _ dv Ts M0 MT h1 h2 h0 hT =>
    rl_vertex_t (rlAdmB_sound h2 h0) (rlAdmB_sound h2 hT) (by linarith) ht0 ht
  rcases le_total d.F1 2 with hc | hc
  · -- cell 1
    have A1 := W 0 1 rlD0 0 rlM0 rlM1 (by norm_num [rlD0]) (by norm_num [rlD0]) rl_w0 rl_w1
    have A2 := W 2 3 rlD2 0 rlM2 rlM3 (by norm_num [rlD2]) (by norm_num [rlD2]) rl_w2 rl_w3
    have A3 := W 4 5 rlD4 0 rlM4 rlM5 (by norm_num [rlD4]) (by norm_num [rlD4]) rl_w4 rl_w5
    have B1 := W 6 7 rlD6 0 rlM6 rlM7 (by norm_num [rlD6]) (by norm_num [rlD6]) rl_w6 rl_w7
    have B2 := W 8 9 rlD8 0 rlM8 rlM9 (by norm_num [rlD8]) (by norm_num [rlD8]) rl_w8 rl_w9
    have B3 := W 10 11 rlD10 0 rlM10 rlM11 (by norm_num [rlD10]) (by norm_num [rlD10]) rl_w10 rl_w11
    have C1 := rlAdm_conv A1 B1 (a := 1 - lamG) (b := lamG) (by linarith) hlam0 (by ring)
    have C2 := rlAdm_conv A2 B2 (a := 1 - lamG) (b := lamG) (by linarith) hlam0 (by ring)
    have C3 := rlAdm_conv A3 B3 (a := 1 - lamG) (b := lamG) (by linarith) hlam0 (by ring)
    -- the `(F1, V1)` part
    have hF : ∃ M, ∃ V1v : ℚ, max 1 d.F1 = V1v ∧ rlAdm ⟨d.G1, d.F1, 0, 0, V1v, 0⟩ t 0 M := by
      rcases le_total d.F1 1 with h1 | h1
      · have D := rlAdm_conv C1 C2 (a := 1 - d.F1) (b := d.F1) (by linarith) hF1 (by ring)
        refine ⟨_, 1, max_eq_left h1, rlAdm_congr D (RLD.ext' ?_ ?_ ?_ ?_ ?_ ?_)⟩ <;>
          simp only [RLD.lc, rlD0, rlD2, rlD4, rlD6, rlD8, rlD10, lamG] <;> ring
      · have D := rlAdm_conv C2 C3 (a := 2 - d.F1) (b := d.F1 - 1) (by linarith) (by linarith) (by ring)
        refine ⟨_, d.F1, max_eq_right h1, rlAdm_congr D (RLD.ext' ?_ ?_ ?_ ?_ ?_ ?_)⟩ <;>
          simp only [RLD.lc, rlD0, rlD2, rlD4, rlD6, rlD8, rlD10, lamG] <;> ring
    obtain ⟨M1, V1v, hV1v, hM1⟩ := hF
    have hμ : 0 ≤ d.V1 - V1v := by rw [← hV1v]; exact sub_nonneg.2 (max_le hV1 hV1F)
    have E := rlAdm_ray hM1 (rlRayB_sound rl_eV1_0) rfl hμ
    have E' : rlAdm ⟨d.G1, d.F1, 0, 0, d.V1, 0⟩ t 0 (rlLC 1 (d.V1 - V1v) M1 rlZ) :=
      rlAdm_congr E (RLD.ext' (by simp [RLD.lc, rlEV1]) (by simp [RLD.lc, rlEV1]) (by simp [RLD.lc, rlEV1])
        (by simp [RLD.lc, rlEV1]) (by simp [RLD.lc, rlEV1]) (by simp [RLD.lc, rlEV1]))
    obtain ⟨M', hM'⟩ := rl_add_GF E' ⟨rfl, rfl, rfl⟩ (rlRayB_sound rl_w12) (rlRayB_sound rl_w13)
      (rlRayB_sound rl_w14) (rlRayB_sound rl_eV2_0) (by simp [rlD12]) (by simp [rlD13]) (by simp [rlD14])
      hG2 hF2 hV2G hV2F
    exact ⟨0, M', rlAdm_congr hM' (by cases d; rfl)⟩
  · -- cell 2
    have A := W 15 16 rlD15 4 rlM15 rlM16 (by norm_num [rlD15]) (by norm_num [rlD15]) rl_w15 rl_w16
    have B := W 17 18 rlD17 4 rlM17 rlM18 (by norm_num [rlD17]) (by norm_num [rlD17]) rl_w17 rl_w18
    have C := rlAdm_conv A B (a := 1 - lamG) (b := lamG) (by linarith) hlam0 (by ring)
    have hrF1 : rlD19 = ⟨0, 1, 0, 0, 1, 0⟩ := by simp [rlD19]
    have D := rlAdm_ray C (rlRayB_sound rl_w19) (by rw [hrF1]) (show 0 ≤ d.F1 - 2 by linarith)
    have E := rlAdm_ray D (rlRayB_sound rl_eV1_4) rfl (show 0 ≤ d.V1 - d.F1 by linarith)
    have E' : rlAdm ⟨d.G1, d.F1, 0, 0, d.V1, 0⟩ t 4
        (rlLC 1 (d.V1 - d.F1) (rlLC 1 (d.F1 - 2) (rlLC (1 - lamG) lamG
          (rlLC (1 - 80 * t) (80 * t) rlM15 rlM16) (rlLC (1 - 80 * t) (80 * t) rlM17 rlM18)) rlM19) rlZ) :=
      by
        refine rlAdm_congr E (RLD.ext' ?_ ?_ ?_ ?_ ?_ ?_) <;>
          first
            | (simp only [RLD.lc, rlD15, rlD17, hrF1, rlEV1, lamG]; ring)
            | simp only [RLD.lc, rlD15, rlD17, hrF1, rlEV1, lamG]
            | ring
    obtain ⟨M', hM'⟩ := rl_add_GF E' ⟨rfl, rfl, rfl⟩ (rlRayB_sound rl_w20) (rlRayB_sound rl_w21)
      (rlRayB_sound rl_w22) (rlRayB_sound rl_eV2_4) (by simp [rlD20]) (by simp [rlD21]) (by simp [rlD22])
      hG2 hF2 hV2G hV2F
    exact ⟨4, M', rlAdm_congr hM' (by cases d; rfl)⟩

/-- **(R4) Scaling** by `λ ≥ 1`. -/
theorem rlAdm_scale {d : RLD} {t : ℚ} {Ts : ℕ} {M : Fin 8 → Fin 3 → ℚ} (h : rlAdm d t Ts M) {l : ℚ} (hl : 1 ≤ l) :
    rlAdm (RLD.lc l 0 d d) t Ts (rlLC l 0 M M) := by
  obtain ⟨b1, v1, g1, p1⟩ := h
  have hl0 : 0 ≤ l := by linarith
  refine ⟨fun u hu i hi => ?_, ?_, fun C hC hne => ?_, fun u hu hne => ?_⟩
  · rw [rlLo_lc, rlWd_lc, rlM_lc]
    obtain ⟨l1, h1⟩ := b1 u hu i hi
    constructor <;> nlinarith
  · rw [rlV8_lc]; simp only [RLD.lc]; nlinarith
  · rw [rlV8_lc, rlV8_lc]; simp only [RLD.lc]
    have := g1 C hC hne
    rw [add_div, mul_div_assoc, mul_div_assoc]
    nlinarith
  · rw [rlPS_lc, rlPS_lc]
    have := p1 u hu hne
    nlinarith

/-- **Theorem RL_sym, full symmetric domain** (`G1 ≥ 4/5`, `G1 ≤ V1`). -/
theorem rl_sym_full (d : RLD) (hG1 : 4 / 5 ≤ d.G1) (hGV : d.G1 ≤ d.V1) (hF1 : 0 ≤ d.F1)
    (hV1F : d.F1 ≤ d.V1) (hV1 : 1 ≤ d.V1) (hG2 : 0 ≤ d.G2) (hF2 : 0 ≤ d.F2) (hV2G : d.G2 ≤ d.V2)
    (hV2F : d.F2 ≤ d.V2) {t : ℚ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 80) : ∃ Ts M, rlAdm d t Ts M := by
  rcases le_total d.G1 1 with h1 | h1
  · exact rl_sym d hG1 h1 hF1 hV1 hV1F hG2 hF2 hV2G hV2F ht0 ht
  · set l := d.G1
    have hl : 0 < l := by linarith
    set d' : RLD := ⟨1, d.F1 / l, d.G2 / l, d.F2 / l, d.V1 / l, d.V2 / l⟩
    obtain ⟨Ts, M, hM⟩ := rl_sym d' (by norm_num [d']) (by norm_num [d']) (by simp only [d']; positivity)
      (by simp only [d']; rw [le_div_iff₀ hl]; linarith) (by simp only [d']; gcongr)
      (by simp only [d']; positivity) (by simp only [d']; positivity) (by simp only [d']; gcongr)
      (by simp only [d']; gcongr) ht0 ht
    have hne : d.G1 ≠ 0 := ne_of_gt (by linarith)
    refine ⟨Ts, _, rlAdm_congr (rlAdm_scale hM h1) (RLD.ext' ?_ ?_ ?_ ?_ ?_ ?_)⟩ <;>
      simp only [RLD.lc, d', l] <;> field_simp <;> ring

end Census
end IIT
