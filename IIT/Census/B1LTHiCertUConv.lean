/-
Census, B1 LTBetaHi, RL-u certificate, part 4: the linear structure of the RL-u conditions.

* `rlUAdm_conv` / `rlUEff_conv`: convex combinations at a FIXED weight `w` (everything is then linear in
  `(d, M, Y)`; u's contribution `w · ent` is linear in `x, f, Y`);
* `rlU_wseg`: along a segment in `w` alone, the private entries are mixed with the weights `a w / w''`,
  `b w' / w''` (`w'' = a w + b w'`), so that `w'' · ent'' = a w ent + b w' ent'`;
* `rlUAdm_monoV`: admissibility is monotone in the rest weights `V1, V2`.
-/
import IIT.Census.B1LTHiCertU2
import IIT.Census.B1LTHiCertTcConv

namespace IIT
namespace Census

/-- Linear combination of RL-u data. -/
def RLUD.lc (a b : ℚ) (d e : RLUD) : RLUD :=
  ⟨a * d.G1 + b * e.G1, a * d.F1 + b * e.F1, a * d.G2 + b * e.G2, a * d.F2 + b * e.F2,
    a * d.V1 + b * e.V1, a * d.V2 + b * e.V2, a * d.w + b * e.w, a * d.x + b * e.x, a * d.f + b * e.f⟩

lemma RLUD.lc_rest (a b : ℚ) (d e : RLUD) : (d.lc a b e).rest = RLD.lc a b d.rest e.rest := rfl

lemma RLUD.ext' {d e : RLUD} (h1 : d.G1 = e.G1) (h2 : d.F1 = e.F1) (h3 : d.G2 = e.G2) (h4 : d.F2 = e.F2)
    (h5 : d.V1 = e.V1) (h6 : d.V2 = e.V2) (h7 : d.w = e.w) (h8 : d.x = e.x) (h9 : d.f = e.f) : d = e := by
  cases d; cases e; simp_all

lemma rlUEnt_lc (a b : ℚ) (d e : RLUD) (Y Y' : Fin 8 → Fin 3 → ℚ) (R i : ℕ) :
    rlUEnt (d.lc a b e) (rlLC a b Y Y') R i = a * rlUEnt d Y R i + b * rlUEnt e Y' R i := by
  unfold rlUEnt RLUD.lc
  split_ifs <;> simp [rlM_lc]

/-- **Convex combination at a fixed weight.** -/
theorem rlUAdm_conv {ds : Bool} {d e : RLUD} {t : ℚ} {Ts : ℕ} {M M' Y Y' : Fin 8 → Fin 3 → ℚ}
    (hd : rlUAdm ds d t Ts M Y) (he : rlUAdm ds e t Ts M' Y') (hw : d.w = e.w) {a b : ℚ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) : rlUAdm ds (d.lc a b e) t Ts (rlLC a b M M') (rlLC a b Y Y') := by
  obtain ⟨b1, y1, v1, g1, p1⟩ := hd
  obtain ⟨b2, y2, v2, g2, p2⟩ := he
  have hw'' : (d.lc a b e).w = d.w := by simp only [RLUD.lc]; rw [← hw, ← add_mul, hab, one_mul]
  refine ⟨fun u hu i hi => ?_, fun R hR i hi h0 h1 => ?_, ?_, fun C hC hne => ?_, fun u hu hne => ?_⟩
  · rw [RLUD.lc_rest, rlLo_lc, rlWd_lc, rlM_lc, rlUEnt_lc, hw'']
    obtain ⟨l1, u1⟩ := b1 u hu i hi; obtain ⟨l2, u2⟩ := b2 u hu i hi
    rw [← hw] at l2 u2
    constructor <;> nlinarith
  · rw [rlM_lc]
    obtain ⟨l1, u1⟩ := y1 R hR i hi h0 h1; obtain ⟨l2, u2⟩ := y2 R hR i hi h0 h1
    constructor <;> nlinarith
  · rw [rlV8_lc]; simp only [RLUD.lc]; nlinarith
  · rw [rlV8_lc, rlV8_lc]; simp only [RLUD.lc]
    have := g1 C hC hne; have := g2 C hC hne
    rw [add_div, mul_div_assoc, mul_div_assoc]
    nlinarith
  · rw [rlPS_lc, rlPS_lc]
    have := p1 u hu hne; have := p2 u hu hne
    nlinarith

theorem rlUEff_conv {d e : RLUD} {t B : ℚ} {desig : ℕ → ℕ} {Y Y' : Fin 8 → Fin 3 → ℚ}
    (hd : rlUEff d t B desig Y) (he : rlUEff e t B desig Y') {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : rlUEff (d.lc a b e) t B desig (rlLC a b Y Y') := by
  obtain ⟨e1, d1, s1⟩ := hd
  obtain ⟨e2, -, s2⟩ := he
  refine ⟨fun R hR hR0 i hi hbit => ?_, d1, ?_⟩
  · rw [rlM_lc]; simp only [RLUD.lc]
    have h1 := mul_le_mul_of_nonneg_left (e1 R hR hR0 i hi hbit) ha
    have h2 := mul_le_mul_of_nonneg_left (e2 R hR hR0 i hi hbit) hb
    have h3 : a * t + b * t = t := by rw [← add_mul, hab, one_mul]
    linarith
  · simp only [rlUEnt_lc]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left s1 ha
    have h2 := mul_le_mul_of_nonneg_left s2 hb
    have h3 : a * B + b * B = B := by rw [← add_mul, hab, one_mul]
    linarith

/-- **Monotonicity in the rest weights.** -/
theorem rlUAdm_monoV {ds : Bool} {d : RLUD} {t : ℚ} {Ts : ℕ} {M Y : Fin 8 → Fin 3 → ℚ}
    (hd : rlUAdm ds d t Ts M Y) {V1 V2 : ℚ} (h1 : d.V1 ≤ V1) (h2 : d.V2 ≤ V2) :
    rlUAdm ds ⟨d.G1, d.F1, d.G2, d.F2, V1, V2, d.w, d.x, d.f⟩ t Ts M Y := by
  obtain ⟨b1, y1, v1, g1, p1⟩ := hd
  refine ⟨fun u hu i hi => ?_, y1, v1, g1, p1⟩
  obtain ⟨l1, u1⟩ := b1 u hu i hi
  have hw : rlWd d.rest u i ≤ rlWd (⟨d.G1, d.F1, d.G2, d.F2, V1, V2, d.w, d.x, d.f⟩ : RLUD).rest u i := by
    unfold rlWd RLUD.rest; simp only; split_ifs <;> linarith
  have hl : rlLo (⟨d.G1, d.F1, d.G2, d.F2, V1, V2, d.w, d.x, d.f⟩ : RLUD).rest u i = rlLo d.rest u i := by
    unfold rlLo RLUD.rest; rfl
  have he : rlUEnt (⟨d.G1, d.F1, d.G2, d.F2, V1, V2, d.w, d.x, d.f⟩ : RLUD) Y (u ^^^ uOff ds) i =
      rlUEnt d Y (u ^^^ uOff ds) i := by unfold rlUEnt; rfl
  simp only at he ⊢
  rw [hl, he]
  exact ⟨l1, by linarith⟩

theorem rlUEff_monoV {d : RLUD} {t B : ℚ} {desig : ℕ → ℕ} {Y : Fin 8 → Fin 3 → ℚ}
    (hd : rlUEff d t B desig Y) (V1 V2 : ℚ) :
    rlUEff ⟨d.G1, d.F1, d.G2, d.F2, V1, V2, d.w, d.x, d.f⟩ t B desig Y := hd

/-! ### The `w`-segment -/

/-- The data `d` with weight `w`. -/
def RLUD.setW (d : RLUD) (w : ℚ) : RLUD := ⟨d.G1, d.F1, d.G2, d.F2, d.V1, d.V2, w, d.x, d.f⟩

lemma rlUEnt_setW (d : RLUD) (w : ℚ) (Y : Fin 8 → Fin 3 → ℚ) (R i : ℕ) :
    rlUEnt (d.setW w) Y R i = rlUEnt d Y R i := by unfold rlUEnt RLUD.setW; rfl

lemma rlUEnt_mix (d : RLUD) (α β : ℚ) (hab : α + β = 1) (Y Y' : Fin 8 → Fin 3 → ℚ) (R i : ℕ) :
    rlUEnt d (rlLC α β Y Y') R i = α * rlUEnt d Y R i + β * rlUEnt d Y' R i := by
  unfold rlUEnt
  split_ifs
  · rw [← add_mul, hab, one_mul]
  · rw [← add_mul, hab, one_mul]
  · simp [rlM_lc]

/-- **The `w`-segment**: admissible tables at weights `w` and `w'` give one at `a w + b w'`. -/
theorem rlU_wseg {ds : Bool} {d : RLUD} {t B : ℚ} {Ts : ℕ} {desig : ℕ → ℕ} {w w' : ℚ} (hw : 0 ≤ w)
    (hw' : 0 ≤ w') {M M' Y Y' : Fin 8 → Fin 3 → ℚ}
    (hd : rlUAdm ds (d.setW w) t Ts M Y ∧ rlUEff (d.setW w) t B desig Y)
    (he : rlUAdm ds (d.setW w') t Ts M' Y' ∧ rlUEff (d.setW w') t B desig Y') {a b : ℚ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) :
    ∃ M'' Y'', rlUAdm ds (d.setW (a * w + b * w')) t Ts M'' Y'' ∧
      rlUEff (d.setW (a * w + b * w')) t B desig Y'' := by
  obtain ⟨⟨b1, y1, v1, g1, p1⟩, e1⟩ := hd
  obtain ⟨⟨b2, y2, v2, g2, p2⟩, e2⟩ := he
  set W := a * w + b * w'
  have hW : 0 ≤ W := by positivity
  -- mixing weights for the private entries
  obtain ⟨α, β, hα, hβ, hαβ, hmix⟩ : ∃ α β : ℚ, 0 ≤ α ∧ 0 ≤ β ∧ α + β = 1 ∧ W * α = a * w ∧ W * β = b * w' := by
    rcases eq_or_lt_of_le hW with h0 | hpos
    · have h1 : a * w = 0 := by nlinarith [mul_nonneg ha hw, mul_nonneg hb hw']
      have h2 : b * w' = 0 := by nlinarith [mul_nonneg ha hw, mul_nonneg hb hw']
      exact ⟨1, 0, zero_le_one, le_rfl, by ring, by rw [← h0, h1]; ring, by rw [← h0, h2]; ring⟩
    · refine ⟨a * w / W, b * w' / W, by positivity, by positivity, ?_, ?_, ?_⟩
      · rw [← add_div]; exact div_self hpos.ne'
      · field_simp
      · field_simp
  refine ⟨rlLC a b M M', rlLC α β Y Y', ⟨fun u hu i hi => ?_, fun R hR i hi h0 h1 => ?_, ?_,
    fun C hC hne => ?_, fun u hu hne => ?_⟩, ⟨fun R hR hR0 i hi hbit => ?_, e1.2.1, ?_⟩⟩
  · obtain ⟨l1, u1⟩ := b1 u hu i hi; obtain ⟨l2, u2⟩ := b2 u hu i hi
    have hr : ∀ v, (d.setW v).rest = d.rest := fun v => rfl
    have hwv : ∀ v, (d.setW v).w = v := fun v => rfl
    have hent : rlUEnt (d.setW W) (rlLC α β Y Y') (u ^^^ uOff ds) i =
        α * rlUEnt d Y (u ^^^ uOff ds) i + β * rlUEnt d Y' (u ^^^ uOff ds) i := by
      rw [rlUEnt_setW, rlUEnt_mix d α β hαβ]
    rw [rlUEnt_setW, hr, hwv] at l1 u1 l2 u2
    rw [hr, hwv, hent, rlM_lc]
    have key : W * (α * rlUEnt d Y (u ^^^ uOff ds) i + β * rlUEnt d Y' (u ^^^ uOff ds) i) =
        a * (w * rlUEnt d Y (u ^^^ uOff ds) i) + b * (w' * rlUEnt d Y' (u ^^^ uOff ds) i) := by
      rw [mul_add, ← mul_assoc, ← mul_assoc, hmix.1, hmix.2]; ring
    rw [key]
    have hl : rlLo d.rest u i = a * rlLo d.rest u i + b * rlLo d.rest u i := by rw [← add_mul, hab, one_mul]
    have hwd : rlWd d.rest u i = a * rlWd d.rest u i + b * rlWd d.rest u i := by rw [← add_mul, hab, one_mul]
    constructor <;> nlinarith
  · rw [rlM_lc]
    obtain ⟨l1, u1⟩ := y1 R hR i hi h0 h1; obtain ⟨l2, u2⟩ := y2 R hR i hi h0 h1
    constructor <;> nlinarith
  · rw [rlV8_lc]; simp only [RLUD.setW] at v1 v2 ⊢
    have h1 := mul_le_mul_of_nonneg_left v1 ha; have h2 := mul_le_mul_of_nonneg_left v2 hb
    have h3 : a * (8 * d.G1 * (5 / 3 - t)) + b * (8 * d.G1 * (5 / 3 - t)) = 8 * d.G1 * (5 / 3 - t) := by
      rw [← add_mul, hab, one_mul]
    linarith
  · rw [rlV8_lc, rlV8_lc]; simp only [RLUD.setW] at g1 g2 ⊢
    have h1 := mul_le_mul_of_nonneg_left (g1 C hC hne) ha
    have h2 := mul_le_mul_of_nonneg_left (g2 C hC hne) hb
    have h3 : a * (1 / 20 * d.G1 * t) + b * (1 / 20 * d.G1 * t) = 1 / 20 * d.G1 * t := by
      rw [← add_mul, hab, one_mul]
    have e : (a * rlV8 C Ts M + b * rlV8 C Ts M') / (8 * (cd_cc 3 C : ℚ)) -
        (a * rlV8 lp3CStar Ts M + b * rlV8 lp3CStar Ts M') / 40 =
        a * (rlV8 C Ts M / (8 * (cd_cc 3 C : ℚ)) - rlV8 lp3CStar Ts M / 40) +
          b * (rlV8 C Ts M' / (8 * (cd_cc 3 C : ℚ)) - rlV8 lp3CStar Ts M' / 40) := by ring
    rw [e]; linarith
  · rw [rlPS_lc, rlPS_lc]
    have h1 := mul_le_mul_of_nonneg_left (p1 u hu hne) ha
    have h2 := mul_le_mul_of_nonneg_left (p2 u hu hne) hb
    have h3 : a * (1 / 20) + b * (1 / 20) = (1 / 20 : ℚ) := by rw [← add_mul, hab, one_mul]
    have e : a * rlPS M Ts + b * rlPS M' Ts - (a * rlPS M u + b * rlPS M' u) =
        a * (rlPS M Ts - rlPS M u) + b * (rlPS M' Ts - rlPS M' u) := by ring
    rw [e]; linarith
  · rw [rlM_lc]
    have h1 := mul_le_mul_of_nonneg_left (e1.1 R hR hR0 i hi hbit) hα
    have h2 := mul_le_mul_of_nonneg_left (e2.1 R hR hR0 i hi hbit) hβ
    simp only [RLUD.setW] at h1 h2 ⊢
    have h3 : α * (d.x - t / 100) + β * (d.x - t / 100) = d.x - t / 100 := by rw [← add_mul, hαβ, one_mul]
    linarith
  · have s1 := e1.2.2; have s2 := e2.2.2
    simp only [rlUEnt_setW] at s1 s2 ⊢
    simp only [rlUEnt_mix d α β hαβ]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left s1 hα
    have h2 := mul_le_mul_of_nonneg_left s2 hβ
    have h3 : α * (B - 1 / 500) + β * (B - 1 / 500) = B - 1 / 500 := by rw [← add_mul, hαβ, one_mul]
    linarith

end Census
end IIT
