/-
Census, B1 LTBetaHi, RL-u part 2b: **the effect side for a heavy current state `s ≠ tc`** (analogue of
`lt3_heff_tc`, with the floor `a` of `s`'s entries in place of `4/5`): Lemma EFG at the maximal effect state with
`e0 = a³`, from the windowed RL-u table (`RLUWin`).
-/
import IIT.Census.B1LTHiUW
import IIT.Census.B1LTHiTcE

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- The effect level for floor `a`. -/
noncomputable def lt3E0u (a : ℝ) : ℝ := a ^ 3 * Real.logb 2 (1 / (1 - (1 / 16000) / 2))

lemma lt3E0u_pos {a : ℝ} (ha : 0 < a) : 0 < lt3E0u a := by
  unfold lt3E0u
  have : 0 < Real.logb 2 (1 / (1 - (1 / 16000 : ℝ) / 2)) :=
    Real.logb_pos (by norm_num) (by norm_num)
  positivity

/-! ### The effect side for a heavy `s ≠ tc` -/

/-- **Lemma EFG for a heavy current state `s ≠ tc`**, from a windowed RL-u table of `s`'s shared entries and `s`'s
private entries within `ρ` of the table; `a ≤ x0` is the floor of `s`'s entries. -/
theorem lt3_heff_u {w : Param N} (hw : w ∈ openCube N) (s : State N) {S : Finset (Fin N)}
    (e : Fin 3 ↪ Fin N) (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) {ds : Bool} {dR : RLDR} {wu ω' ρ x0 a : ℝ} {T : TcTab}
    (hT : RLUWin ds dR wu (fun i => clamp01 (w s (e i))) (fun i => clamp01 (w (flip s (e i)) (e i))) ω' x0 T)
    (ha : 0 ≤ a) (hax : a ≤ x0)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 16000) (hsl : 7 * ω' + 7 * ρ ≤ 1 / 500)
    (hbox : ∀ (u : Fin (2 ^ 3)) (i : Fin 3), ¬((u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ)) →
      |clamp01 (w (pkFlip e s u) (e i)) - T.Y u i| ≤ ρ) :
    ∃ te ∈ sysMaxEffStates (tpmOf (flipP s w)) S s s, ∀ θ : SysPartition N S,
      lt3E0u a ≤ sysPhiE (tpmOf (flipP s w)) S s θ s te := by
  classical
  obtain ⟨-, -, -, hxw, -, -, -, -, -, hE2, hSig, hLx0, hHx1, hxr, hbud⟩ := hT
  have hc0x : ∀ i, x0 ≤ clamp01 (w s (e i)) := fun i => (hxw i).1
  set x : Fin 3 → ℝ := fun i => clamp01 (w s (e i)) with hxdef
  set f : Fin 3 → ℝ := fun i => clamp01 (w (flip s (e i)) (e i)) with hfdef
  have hc : ∀ r j, clamp01 (w r j) = w r j := fun r j => clamp01_of_mem ⟨(hw r j).1.le, (hw r j).2.le⟩
  have hS3 : S.card = 3 := pk_card_S e hS
  -- the frame `z' = w`
  set z' : Param N := fun r j => flipC ((fun _ => true) j) (w r j) with hz'def
  have hz'w : ∀ r j, z' r j = w r j := fun r j => by simp [hz'def, flipC]
  have hz' : z' ∈ openCube N := fun r j => by rw [hz'w]; exact hw r j
  set desig : State N → Fin N := fun r => e (T.dg (pkCode e s r)) with hdesig
  -- (E2)
  have hE2' : ∀ r ∈ agree Sᶜ s, r ≠ s → ∀ j ∈ S, r j = s j → z' r j ≤ z' s j - 1 / 16000 := by
    intro r hr hrs j hj hrj
    obtain ⟨i, rfl⟩ := (hS j).1 hj
    set R := pkCode e s r with hR
    have hrR : pkFlip e s R = r := pkFlip_code e hS hr
    have hR0 : (R : ℕ) ≠ 0 := fun h0 => hrs (by rw [← hrR, pkFlip_zero e s R h0])
    have hbit : (R : ℕ).testBit i = false := by
      have h1 : pkFlip e s R (e i) = s (e i) := by rw [hrR]; exact hrj
      rw [pkFlip_e] at h1
      by_contra hb
      rw [Bool.not_eq_false] at hb
      rw [if_pos hb] at h1
      cases h' : s (e i) <;> simp [h'] at h1
    have hpriv : ¬((R : ℕ) = 0 ∨ (R : ℕ) = 2 ^ (i : ℕ)) := by
      rintro (h | h)
      · exact hR0 h
      · rw [h, Nat.testBit_two_pow_self] at hbit; exact Bool.noConfusion hbit
    have hb := abs_le.1 (hbox R i hpriv)
    rw [hrR, hc] at hb
    have he2 := hE2 R i hR0 hbit
    have hx := hc0x i
    simp only [hxdef, hc] at hx
    rw [hz'w, hz'w]
    linarith [hb.2]
  -- (Σ)
  have hSig' : ∑ r ∈ (agree Sᶜ s).erase s, z' r (desig r) ≤ T.B := by
    rw [block_sum_pk e hS s (fun r => z' r (desig r))]
    simp only [hdesig, pkCode_flip, hz'w]
    have hterm : ∀ R ∈ (univ : Finset (Fin (2 ^ 3))).erase 0,
        w (pkFlip e s R) (e (T.dg R)) ≤ tcEntR x f T.Y R (T.dg R) + ρ := by
      intro R hR
      have hR0 : (R : ℕ) ≠ 0 := fun h => (mem_erase.1 hR).1 (Fin.ext h)
      set i := T.dg R
      unfold tcEntR
      rw [if_neg hR0]
      by_cases hbi : (R : ℕ) = rlBit i
      · rw [if_pos hbi]
        have hfl : pkFlip e s R = flip s (e i) := pkFlip_bit e s R i hbi
        rw [hfl]
        simp only [hfdef, hc]
        linarith
      · rw [if_neg hbi]
        have hpriv : ¬((R : ℕ) = 0 ∨ (R : ℕ) = 2 ^ (i : ℕ)) := by
          rintro (h | h)
          · exact hR0 h
          · exact hbi h
        have hb := abs_le.1 (hbox R i hpriv)
        rw [hc] at hb
        linarith [hb.2]
    calc ∑ R ∈ (univ : Finset (Fin (2 ^ 3))).erase 0, w (pkFlip e s R) (e (T.dg R))
        ≤ ∑ R ∈ (univ : Finset (Fin (2 ^ 3))).erase 0, (tcEntR x f T.Y R (T.dg R) + ρ) := sum_le_sum hterm
      _ = ∑ R ∈ (univ : Finset (Fin 8)).erase 0, tcEntR x f T.Y R (T.dg R) + 7 * ρ := by
          rw [sum_add_distrib, sum_const, card_erase_of_mem (mem_univ _)]
          simp
      _ ≤ T.B := by linarith
  -- the product of own entries
  have hprod : ∏ j ∈ S, z' s j = x 0 * x 1 * x 2 := by
    rw [prod_S_e e hS]; simp only [hz'w, hxdef, hc]
  have hx0 : ∀ i, 0 ≤ x i := fun i => le_trans (by linarith) ((hxr i).1)
  have hx1 : ∀ i, x i ≤ 1 := fun i => (hxr i).2.trans hHx1
  have hLx3 : T.Lx ^ 3 ≤ ∏ j ∈ S, z' s j := by
    rw [hprod]
    have h01 := mul_le_mul (hxr 0).1 (hxr 1).1 hLx0 (hx0 0)
    have := mul_le_mul h01 (hxr 2).1 hLx0 (mul_nonneg (hx0 0) (hx0 1))
    nlinarith
  -- (E1)
  have hE1 : ∀ t : State N, (∃ j ∈ S, t j = false) →
      Real.log 2 * sysIiE (tpmOf z') S s s t ≤ Real.log 2 * (3 * ∏ j ∈ S, z' s j) - T.B := by
    refine efg_E1_pointwise s hS3 fun t ht => ?_
    set c : Fin (2 ^ 3) := pkEnc 3 (fun q => !t (e q)) with hcdef
    have hbits : ∀ q : Fin 3, (c : ℕ).testBit q = !t (e q) := fun q => pk_testBit_enc _ q
    have hc0 : 0 < (c : ℕ) := by
      obtain ⟨j, hj, hf⟩ := ht
      obtain ⟨q, rfl⟩ := (hS j).1 hj
      have := hbits q
      rw [hf] at this
      rcases Nat.eq_zero_or_pos (c : ℕ) with h | h
      · rw [h, Nat.zero_testBit] at this; exact absurd this (by decide)
      · exact h
    have hc8 : (c : ℕ) < 8 := c.2
    refine ⟨tcEhiR T.Lx T.Hx c, ?_, ?_⟩
    · rw [tp_eff_eq, prod_S_e e hS]
      have hfac : ∀ q : Fin 3, 0 ≤ (tpmOf z').prob (e q) s (t (e q)) ∧
          (tpmOf z').prob (e q) s (t (e q)) ≤ (if (c : ℕ).testBit q then 1 - T.Lx else T.Hx) := by
        intro q
        rw [prob_of_mem hz', hz'w, hbits q]
        have hxq : w s (e q) = x q := by simp only [hxdef, hc]
        rw [hxq]
        cases t (e q)
        · simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
          constructor <;> linarith [hx1 q, (hxr q).1]
        · simp only [Bool.not_true, ite_true, Bool.false_eq_true, ite_false]
          exact ⟨hx0 q, (hxr q).2⟩
      have f0 := hfac 0
      have f1 := hfac 1
      have f2 := hfac 2
      unfold tcEhiR
      have k1 := mul_le_mul f0.2 f1.2 f1.1 (f0.1.trans f0.2)
      exact mul_le_mul k1 f2.2 f2.1 (mul_nonneg (f0.1.trans f0.2) (f1.1.trans f1.2))
    · have := hbud c hc0 hc8
      have hl2 : 0 ≤ 3 * Real.log 2 := by positivity
      nlinarith
  -- `e0 = a³`
  have he0 : a ^ 3 ≤ ∏ j ∈ S, z' s j := by
    rw [hprod]
    have hxa : ∀ i, a ≤ x i := fun i => hax.trans (hc0x i)
    have h01 := mul_le_mul (hxa 0) (hxa 1) ha (hx0 0)
    have := mul_le_mul h01 (hxa 2) ha (mul_nonneg (hx0 0) (hx0 1))
    nlinarith
  have hH : EFGHyp z' s S (1 / 16000) T.B (a ^ 3) desig :=
    ⟨by norm_num, by norm_num, hE2', fun r _ => (hS _).2 ⟨_, rfl⟩, hSig', hE1, he0⟩
  obtain ⟨te, hte, hphi⟩ := efg_of_hyp hz' s hS3 hH
  -- transport to `flipP s w`
  have hTr : ∀ i r b, (tpmOf z').prob i r b =
      (tpmOf (flipP s w)).prob i r (xor b ((fun i => xor ((fun _ => true) i) (s i)) i)) := by
    intro i r b
    have e1 := tpmOf_flipCol (fun _ => true) w i r b
    have e2 := tpmOf_flipCol s w i r (xor b (xor ((fun _ => true) i) (s i)))
    have e3 : (tpmOf (flipP s w)).prob i r (xor b (xor ((fun _ => true) i) (s i))) =
        (tpmOf (fun r j => flipC (s j) (w r j))).prob i r (xor b (xor ((fun _ => true) i) (s i))) := rfl
    rw [e3, e2]
    rw [hz'def, e1]
    congr 1
    cases b <;> cases s i <;> rfl
  refine ⟨tXor (fun i => xor ((fun _ => true) i) (s i)) te, (maxEff_tXor hTr S s s te).1 hte, fun θ => ?_⟩
  rw [← phiE_tXor hTr]
  exact hphi θ

end Census
end IIT
