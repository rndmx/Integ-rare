/-
Census, B1 forced leaf 7 (natural regime): the Chernoff bounds behind the natural-cell certificate.

The certified natural event at a cell `C` and an anchor row `r0` (W7 §2.1, natural form):
  floor  `∀ j, v⁴ ≤ y_{r0,j}`,   count  `#{j : w⁴ < y_{r0,j}} ≤ Kc`,
  tilt   `X(r0) ≤ B`,             link   `Σ_k -ln x_k ≤ X(r0) + Lk`   (`r0 ≠ s`; dropped when `r0 = s`).
* `dn_two_row`  : `P ≤ e^{t B + l_u Lk + μ Kc} (I · E_x)^N` (rows `r0 ≠ s` independent, multipliers `t, l_u, μ`);
* `dn_self_row` : the case `r0 = s` (one row, no link);
* `dnNatEv_le`  : the union over the 118 cells and all `r0`, at `B = x0 N + S`, `Lk = S`, `Kc = N/10⁵`:
  `P ≤ 236 e^{32 S} e^{-1.0106 N}`.
Nothing here reads `B1DefsX`.
-/
import IIT.Census.B1ForcedDNatInt

namespace IIT
namespace Census

open MeasureTheory Finset

noncomputable section

variable {N : ℕ}

/-- Factorisation of a column integral with a window on the first entry. -/
lemma dn_triple_fact (W : Set ℝ) (A B C : ℝ → ℝ) (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) :
    ∫⁻ y in W, ∫⁻ u, ∫⁻ x, ENNReal.ofReal (Real.exp (A y + B u + C x)) ∂unif ∂unif ∂unif =
      (∫⁻ y in W, ENNReal.ofReal (Real.exp (A y)) ∂unif) * (∫⁻ u, ENNReal.ofReal (Real.exp (B u)) ∂unif) *
        ∫⁻ x, ENNReal.ofReal (Real.exp (C x)) ∂unif := by
  have mA : Measurable fun y => ENNReal.ofReal (Real.exp (A y)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hA)
  have mB : Measurable fun y => ENNReal.ofReal (Real.exp (B y)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hB)
  have mC : Measurable fun y => ENNReal.ofReal (Real.exp (C y)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hC)
  have e : ∀ y u x, ENNReal.ofReal (Real.exp (A y + B u + C x)) =
      ENNReal.ofReal (Real.exp (A y)) * ENNReal.ofReal (Real.exp (B u)) *
        ENNReal.ofReal (Real.exp (C x)) := by
    intro y u x
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
      ← Real.exp_add, ← Real.exp_add]
  simp_rw [e]
  simp_rw [lintegral_const_mul _ mC]
  simp_rw [lintegral_mul_const _ (mB.const_mul _), lintegral_const_mul _ mB]
  rw [lintegral_mul_const _ (mA.mul_const _), lintegral_mul_const _ mA]

lemma dn_lint_one : ∫⁻ _u : ℝ, ENNReal.ofReal (Real.exp 0) ∂unif = 1 := by simp

/-- The three constraint functions (tilt, link, count at cap `c`). -/
def dnF (c : ℝ) : Fin 3 → Fin N → ℝ × ℝ × ℝ → ℝ :=
  ![fun _ p => -Real.log (clamp01 p.1),
    fun _ p => -Real.log (max (clamp01 p.2.2) (1 - clamp01 p.2.2)) + Real.log (clamp01 p.1),
    fun _ p => if c < clamp01 p.1 then 1 else 0]

lemma dnF_meas (c : ℝ) (k : Fin 3) (i : Fin N) : Measurable (dnF c k i) := by
  have hl : Measurable fun v : ℝ => Real.log (clamp01 v) := Real.measurable_log.comp clamp01_measurable
  have hf : Measurable fun v : ℝ => Real.log (max (clamp01 v) (1 - clamp01 v)) :=
    Real.measurable_log.comp (clamp01_measurable.max (measurable_const.sub clamp01_measurable))
  fin_cases k
  · exact (hl.comp measurable_fst).neg
  · exact (hf.comp (measurable_snd.comp measurable_snd)).neg.add (hl.comp measurable_fst)
  · show Measurable fun p : ℝ × ℝ × ℝ => if c < clamp01 p.1 then (1 : ℝ) else 0
    exact Measurable.ite (measurableSet_lt measurable_const (clamp01_measurable.comp measurable_fst))
      measurable_const measurable_const

lemma dn_count_eq (c : ℝ) (f : Fin N → ℝ) :
    ∑ i, (if c < clamp01 (f i) then (1 : ℝ) else 0) = ((univ.filter fun j => c < clamp01 (f j)).card : ℝ) := by
  rw [Finset.sum_boole]

/-- A third row distinct from two given ones. -/
lemma dn_exists_third (hN : 2 ≤ N) (a b : State N) : ∃ r : State N, r ≠ a ∧ r ≠ b := by
  have hc : 2 < (univ : Finset (State N)).card := by
    rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  have : ((univ.erase a).erase b).Nonempty := by
    rw [← card_pos]
    have h1 := pred_card_le_card_erase (s := univ.erase a) (a := b)
    have h2 := pred_card_le_card_erase (s := (univ : Finset (State N))) (a := a)
    omega
  obtain ⟨r, hr⟩ := this
  exact ⟨r, ne_of_mem_erase (mem_of_mem_erase hr), ne_of_mem_erase hr⟩

/-- The two-row natural cell event. -/
def DNCellEv (s r0 : State N) (v4 c B Lk Kc : ℝ) : Set (Param N) :=
  {w | (∀ j, v4 ≤ clamp01 (w r0 j)) ∧ ((univ.filter fun j => c < clamp01 (w r0 j)).card : ℝ) ≤ Kc ∧
    XW w r0 ≤ B ∧ ∑ k, -Real.log (xE w s k) ≤ XW w r0 + Lk}

/-- The one-row (self) natural cell event. -/
def DNSelfEv (s : State N) (v4 c B Kc : ℝ) : Set (Param N) :=
  {w | (∀ j, v4 ≤ clamp01 (w s j)) ∧ ((univ.filter fun j => c < clamp01 (w s j)).card : ℝ) ≤ Kc ∧
    XW w s ≤ B}

/-- The cell integral `I(v⁴, c, p, μ)`. -/
def dnIy (v4 c p μ : ℝ) : ℝ :=
  (c ^ (p + 1) - v4 ^ (p + 1)) / (p + 1) + Real.exp (-μ) * ((1 - c ^ (p + 1)) / (p + 1))

/-- The row-`s` factor `E[x^{l}]`. -/
def dnExR (l : ℝ) : ℝ := 2 * (1 - (1 / 2 : ℝ) ^ (l + 1)) / (l + 1)

lemma dnIy_nonneg {v4 c p μ : ℝ} (hv : 0 < v4) (hvc : v4 ≤ c) (hc1 : c ≤ 1) (hp : p ≠ -1) :
    0 ≤ dnIy v4 c p μ := by
  unfold dnIy
  have hc0 : 0 < c := lt_of_lt_of_le hv hvc
  exact add_nonneg (dn_div_rpow_nonneg hv hvc hp)
    (mul_nonneg (Real.exp_pos _).le (by simpa [Real.one_rpow] using dn_div_rpow_nonneg hc0 hc1 hp))

lemma dnExR_nonneg {l : ℝ} (hl : 0 ≤ l) : 0 ≤ dnExR l := by
  unfold dnExR
  have : (1 / 2 : ℝ) ^ (l + 1) ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)
  exact div_nonneg (by linarith) (by linarith)

/-- **Two-row Chernoff** (`r0 ≠ s`): `P(DNCellEv) ≤ e^{t B + l Lk + μ Kc} (I E_x)^N`, `t = p + l`. -/
theorem dn_two_row (hN : 2 ≤ N) {s r0 : State N} (hr : r0 ≠ s) {v4 c p l μ B Lk Kc : ℝ}
    (hv : 0 < v4) (hvc : v4 ≤ c) (hc1 : c ≤ 1) (hp : p ≠ -1) (hl : 0 ≤ l) (ht : 0 ≤ p + l) (hμ : 0 ≤ μ) :
    cubeM N (DNCellEv s r0 v4 c B Lk Kc) ≤
      ENNReal.ofReal (Real.exp ((p + l) * B + l * Lk + μ * Kc) * (dnIy v4 c p μ * dnExR l) ^ N) := by
  obtain ⟨rb, hb0, hbs⟩ := dn_exists_third hN r0 s
  have h := cubeM_chernoff_three (fun _ => r0) (fun _ => rb) (fun _ => s)
    (fun _ => hb0.symm) (fun _ => hr) (fun _ => hbs) univ (dnF c) (dnF_meas c)
    ![B, Lk, Kc] ![p + l, l, μ] (fun k _ => by fin_cases k <;> simp [ht, hl, hμ])
    (fun _ => {y : ℝ | v4 ≤ clamp01 y}) (fun _ => measurableSet_le measurable_const clamp01_measurable)
  refine (measure_mono ?_).trans (h.trans ?_)
  · rintro w ⟨hF, hC, hT, hL⟩
    refine ⟨fun i => hF i, fun k _ => ?_⟩
    fin_cases k
    · simpa [dnF, XW] using hT
    · simp only [dnF, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [sum_add_distrib]
      have : ∑ i, Real.log (clamp01 (w r0 i)) = -XW w r0 := by unfold XW; simp
      rw [this]; unfold xE at hL; linarith
    · simp only [dnF, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [dn_count_eq c (fun i => w r0 i)]; exact hC
  · have hsum : ∑ k ∈ (univ : Finset (Fin 3)), (![p + l, l, μ] : Fin 3 → ℝ) k * ![B, Lk, Kc] k =
        (p + l) * B + l * Lk + μ * Kc := by
      simp [Fin.sum_univ_three]
    rw [hsum, ENNReal.ofReal_mul (Real.exp_pos _).le]
    gcongr
    have hlg : Measurable fun v : ℝ => Real.log (clamp01 v) := Real.measurable_log.comp clamp01_measurable
    have hf : Measurable fun v : ℝ => Real.log (max (clamp01 v) (1 - clamp01 v)) :=
      Real.measurable_log.comp (clamp01_measurable.max (measurable_const.sub clamp01_measurable))
    have hind : Measurable fun v : ℝ => if c < clamp01 v then (1 : ℝ) else 0 :=
      Measurable.ite (measurableSet_lt measurable_const clamp01_measurable) measurable_const measurable_const
    have hcol : ∀ i : Fin N, ∫⁻ y in {y : ℝ | v4 ≤ clamp01 y}, ∫⁻ u, ∫⁻ x,
        ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 3)), (![p + l, l, μ] : Fin 3 → ℝ) k *
          dnF c k i (y, u, x))) ∂unif ∂unif ∂unif ≤ ENNReal.ofReal (dnIy v4 c p μ * dnExR l) := by
      intro i
      have e : ∀ y u x, -∑ k ∈ (univ : Finset (Fin 3)), (![p + l, l, μ] : Fin 3 → ℝ) k * dnF c k i (y, u, x) =
          (p * Real.log (clamp01 y) - μ * (if c < clamp01 y then 1 else 0)) + 0 +
            l * Real.log (max (clamp01 x) (1 - clamp01 x)) := by
        intro y u x
        simp only [Fin.sum_univ_three, dnF, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        ring
      simp_rw [e]
      rw [dn_triple_fact _ (fun y => p * Real.log (clamp01 y) - μ * (if c < clamp01 y then 1 else 0))
        (fun _ => (0 : ℝ)) (fun x => l * Real.log (max (clamp01 x) (1 - clamp01 x)))
        ((hlg.const_mul _).sub (hind.const_mul _)) measurable_const
        (hf.const_mul _), dn_lint_one, mul_one, dn_fold_factor hl]
      calc (∫⁻ y in {y : ℝ | v4 ≤ clamp01 y},
            ENNReal.ofReal (Real.exp (p * Real.log (clamp01 y) - μ * (if c < clamp01 y then 1 else 0))) ∂unif) *
            ENNReal.ofReal (2 * (1 - (1 / 2 : ℝ) ^ (l + 1)) / (l + 1))
          ≤ ENNReal.ofReal (dnIy v4 c p μ) * ENNReal.ofReal (dnExR l) :=
            mul_le_mul_left (dn_y_factor hv hvc hc1 hp) _
        _ = ENNReal.ofReal (dnIy v4 c p μ * dnExR l) := (ENNReal.ofReal_mul (dnIy_nonneg hv hvc hc1 hp)).symm
    calc ∏ i : Fin N, ∫⁻ y in {y : ℝ | v4 ≤ clamp01 y}, ∫⁻ u, ∫⁻ x,
          ENNReal.ofReal (Real.exp (-∑ k ∈ (univ : Finset (Fin 3)), (![p + l, l, μ] : Fin 3 → ℝ) k *
            dnF c k i (y, u, x))) ∂unif ∂unif ∂unif
        ≤ ∏ _i : Fin N, ENNReal.ofReal (dnIy v4 c p μ * dnExR l) := Finset.prod_le_prod' fun i _ => hcol i
      _ = _ := by
        rw [prod_const, card_univ, Fintype.card_fin,
          ENNReal.ofReal_pow (mul_nonneg (dnIy_nonneg hv hvc hc1 hp) (dnExR_nonneg hl))]

/-- **One-row Chernoff** (the self case `r0 = s`): `P(DNSelfEv) ≤ e^{t B + μ Kc} I^N`. -/
theorem dn_self_row (hN : 2 ≤ N) (s : State N) {v4 c t μ B Kc : ℝ}
    (hv : 0 < v4) (hvc : v4 ≤ c) (hc1 : c ≤ 1) (ht : 0 ≤ t) (hμ : 0 ≤ μ) :
    cubeM N (DNSelfEv s v4 c B Kc) ≤
      ENNReal.ofReal (Real.exp (t * B + μ * Kc) * (dnIy v4 c t μ) ^ N) := by
  have htp : t ≠ -1 := by intro h; linarith
  obtain ⟨rb, hbs, -⟩ := dn_exists_third hN s s
  obtain ⟨rc, hcs, hcb⟩ := dn_exists_third hN s rb
  have h := cubeM_chernoff_three (fun _ => s) (fun _ => rb) (fun _ => rc)
    (fun _ => hbs.symm) (fun _ => hcs.symm) (fun _ => hcb.symm) ({0, 2} : Finset (Fin 3)) (dnF c) (dnF_meas c)
    ![B, 0, Kc] ![t, 0, μ] (fun k _ => by fin_cases k <;> simp [ht, hμ])
    (fun _ => {y : ℝ | v4 ≤ clamp01 y}) (fun _ => measurableSet_le measurable_const clamp01_measurable)
  refine (measure_mono ?_).trans (h.trans ?_)
  · rintro w ⟨hF, hC, hT⟩
    refine ⟨fun i => hF i, fun k hk => ?_⟩
    simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl
    · simpa [dnF, XW] using hT
    · simp only [dnF, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [dn_count_eq c (fun i => w s i)]; exact hC
  · have hsum : ∑ k ∈ ({0, 2} : Finset (Fin 3)), (![t, 0, μ] : Fin 3 → ℝ) k * ![B, 0, Kc] k =
        t * B + μ * Kc := by
      rw [sum_pair (by decide)]; simp
    rw [hsum, ENNReal.ofReal_mul (Real.exp_pos _).le]
    gcongr
    have hlg : Measurable fun v : ℝ => Real.log (clamp01 v) := Real.measurable_log.comp clamp01_measurable
    have hind : Measurable fun v : ℝ => if c < clamp01 v then (1 : ℝ) else 0 :=
      Measurable.ite (measurableSet_lt measurable_const clamp01_measurable) measurable_const measurable_const
    have hcol : ∀ i : Fin N, ∫⁻ y in {y : ℝ | v4 ≤ clamp01 y}, ∫⁻ u, ∫⁻ x,
        ENNReal.ofReal (Real.exp (-∑ k ∈ ({0, 2} : Finset (Fin 3)), (![t, 0, μ] : Fin 3 → ℝ) k *
          dnF c k i (y, u, x))) ∂unif ∂unif ∂unif ≤ ENNReal.ofReal (dnIy v4 c t μ) := by
      intro i
      have e : ∀ y u x, -∑ k ∈ ({0, 2} : Finset (Fin 3)), (![t, 0, μ] : Fin 3 → ℝ) k * dnF c k i (y, u, x) =
          (t * Real.log (clamp01 y) - μ * (if c < clamp01 y then 1 else 0)) + 0 + 0 := by
        intro y u x
        rw [sum_pair (by decide)]
        simp only [dnF, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        ring
      simp_rw [e]
      rw [dn_triple_fact _ (fun y => t * Real.log (clamp01 y) - μ * (if c < clamp01 y then 1 else 0))
        (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) ((hlg.const_mul _).sub (hind.const_mul _)) measurable_const
        measurable_const, dn_lint_one, mul_one, mul_one]
      exact dn_y_factor hv hvc hc1 htp
    calc ∏ i : Fin N, ∫⁻ y in {y : ℝ | v4 ≤ clamp01 y}, ∫⁻ u, ∫⁻ x,
          ENNReal.ofReal (Real.exp (-∑ k ∈ ({0, 2} : Finset (Fin 3)), (![t, 0, μ] : Fin 3 → ℝ) k *
            dnF c k i (y, u, x))) ∂unif ∂unif ∂unif
        ≤ ∏ _i : Fin N, ENNReal.ofReal (dnIy v4 c t μ) := Finset.prod_le_prod' fun i _ => hcol i
      _ = _ := by
        rw [prod_const, card_univ, Fintype.card_fin, ENNReal.ofReal_pow (dnIy_nonneg hv hvc hc1 htp)]

/-! ### The certified cells -/

/-- Multiplier ranges and strict cells. -/
theorem dnCells_bounds : dnCells.all (fun C => decide (C.P + 2 * C.L ≤ 128) && decide (C.Ps ≤ 128) &&
    decide (C.v < C.w)) = true := by decide +kernel

/-- The facts of a certified cell, unpacked. -/
lemma dnCellOK_spec {C : DNCell} (h : dnCellOK C = true) :
    0 < C.v ∧ C.v ≤ C.w ∧ C.w ≤ 1 ∧ 0 ≤ C.tlo ∧
    C.v ^ 4 ≤ (1 / 2 - 1 / 10 ^ 6) * dnExpLo (2 / 5 * (1 - 1 / 10 ^ 5) * C.tlo) 12 ∧
    C.thi ≤ C.w ^ 4 ∧ 0 ≤ C.P + C.L ∧ C.P + 4 ≠ 0 ∧
    dnIq C.v C.w C.P C.a ≤ C.ub ∧ 0 ≤ C.e2 ∧ C.e2 ^ 4 * 2 ^ (C.L + 4) ≤ 1 ∧
    0 < 2 * C.ub * dnEx C ∧ |1 - crRed (2 * C.ub * dnEx C) C.k| < 1 ∧
    crLnHi (2 * C.ub * dnEx C) C.k C.n ≤ C.r ∧
    C.r + ((C.P : ℚ) + C.L) / 4 * crX0hi + 1 / 10 ^ 5 * C.a * crL2hi ≤ -dnR ∧
    dnIq C.v C.w C.Ps C.As ≤ C.ubs ∧ 0 < C.ubs ∧
    |1 - crRed C.ubs C.ks| < 1 ∧ crLnHi C.ubs C.ks C.n ≤ C.rs ∧
    C.rs + (C.Ps : ℚ) / 4 * crX0hi + 1 / 10 ^ 5 * C.As * crL2hi ≤ -dnR := by
  simp only [dnCellOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩

/-- `dnIy` at the cell parameters is the rational `dnIq`. -/
lemma dnIy_cell {v w : ℚ} (hv : 0 < v) (hw : 0 < w) (P : ℤ) (a : ℕ) :
    dnIy ((v : ℝ) ^ 4) ((w : ℝ) ^ 4) ((P : ℝ) / 4) (a * Real.log 2) = ((dnIq v w P a : ℚ) : ℝ) := by
  rw [← dn_Iq_eq hv hw P a]; rfl

/-- **One certified cell, two rows**: `P(DNCellEv) ≤ e^{-1.0106 N} e^{32 S} / 2^N` at `B = x0 N + S`,
`Lk = S`, `Kc = N/10⁵`. -/
theorem dn_cell_two_le (hN : 2 ≤ N) {C : DNCell} (hC : C ∈ dnCells) {s r0 : State N} (hr : r0 ≠ s)
    {S : ℝ} (hS : 0 ≤ S) :
    cubeM N (DNCellEv s r0 ((C.v : ℝ) ^ 4) ((C.w : ℝ) ^ 4) (x0 * N + S) S ((N : ℝ) / 10 ^ 5)) ≤
      ENNReal.ofReal (Real.exp (-((dnR : ℝ) * N)) * Real.exp (32 * S) / 2 ^ N) := by
  obtain ⟨h1, h2, h3, -, -, -, h7, h8, h9, h10, h11, h12, h13, h14, h15, -⟩ :=
    dnCellOK_spec ((List.all_eq_true.1 dnCells_ok) C hC)
  have hb := (List.all_eq_true.1 dnCells_bounds) C hC
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨hb1, -⟩, -⟩ := hb
  have hv : (0 : ℝ) < C.v := by exact_mod_cast h1
  have hw : (0 : ℝ) < C.w := by exact_mod_cast (lt_of_lt_of_le h1 h2)
  have hv4 : (0 : ℝ) < (C.v : ℝ) ^ 4 := by positivity
  have hvc : (C.v : ℝ) ^ 4 ≤ (C.w : ℝ) ^ 4 := pow_le_pow_left₀ hv.le (by exact_mod_cast h2) 4
  have hc1 : (C.w : ℝ) ^ 4 ≤ 1 := pow_le_one₀ hw.le (by exact_mod_cast h3)
  have hp : (C.P : ℝ) / 4 ≠ -1 := by
    intro h; apply h8
    have : ((C.P + 4 : ℤ) : ℝ) = 0 := by push_cast; linarith
    exact_mod_cast this
  have hl : (0 : ℝ) ≤ (C.L : ℝ) / 4 := by positivity
  have ht : (0 : ℝ) ≤ (C.P : ℝ) / 4 + (C.L : ℝ) / 4 := by
    have : ((0 : ℤ) : ℝ) ≤ ((C.P + C.L : ℤ) : ℝ) := by exact_mod_cast h7
    push_cast at this; linarith
  have hμ : (0 : ℝ) ≤ C.a * Real.log 2 := by positivity
  refine (dn_two_row hN hr hv4 hvc hc1 hp hl ht hμ).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [dnIy_cell h1 (lt_of_lt_of_le h1 h2)]
  have hI : ((dnIq C.v C.w C.P C.a : ℚ) : ℝ) ≤ C.ub := by exact_mod_cast h9
  have hI0 : (0 : ℝ) ≤ ((dnIq C.v C.w C.P C.a : ℚ) : ℝ) := by
    rw [← dnIy_cell h1 (lt_of_lt_of_le h1 h2)]; exact dnIy_nonneg hv4 hvc hc1 hp
  have he2 := dn_e2_le h10 h11
  have hEx : dnExR ((C.L : ℝ) / 4) ≤ ((dnEx C : ℚ) : ℝ) := by
    unfold dnExR dnEx
    push_cast
    have hq : (C.L : ℝ) / 4 + 1 = ((C.L : ℝ) + 4) / 4 := by ring
    rw [hq]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [← hq]
    linarith
  have hEx0 : 0 ≤ dnExR ((C.L : ℝ) / 4) := dnExR_nonneg hl
  have hq0 : (0 : ℝ) < ((2 * C.ub * dnEx C : ℚ) : ℝ) := by exact_mod_cast h12
  have hlog : Real.log (((2 * C.ub * dnEx C : ℚ) : ℝ)) ≤ C.r :=
    crLog_le (q := 2 * C.ub * dnEx C) (r := C.r) C.k C.n (by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨h12, h13⟩, h14⟩)
  have hqexp : ((2 * C.ub * dnEx C : ℚ) : ℝ) ≤ Real.exp C.r := by
    rw [← Real.log_le_iff_le_exp hq0]; exact hlog
  have hprod : 2 * (((dnIq C.v C.w C.P C.a : ℚ) : ℝ) * dnExR ((C.L : ℝ) / 4)) ≤ Real.exp C.r := by
    refine le_trans ?_ hqexp
    push_cast
    have := mul_le_mul hI hEx hEx0 (le_trans hI0 hI)
    nlinarith
  have hpow : (2 : ℝ) ^ N * (((dnIq C.v C.w C.P C.a : ℚ) : ℝ) * dnExR ((C.L : ℝ) / 4)) ^ N ≤
      Real.exp (C.r * N) := by
    rw [← mul_pow, mul_comm (C.r : ℝ), Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hprod N
  have hrate : ((C.r : ℚ) : ℝ) + ((C.P : ℝ) + C.L) / 4 * x0 + 1 / 10 ^ 5 * C.a * Real.log 2 ≤ -(dnR : ℝ) := by
    have hR := (Rat.cast_le (K := ℝ)).2 h15
    push_cast at hR
    have hx0 := cr_x0_bounds.2
    have hl2 := (cr_log2_bounds).2.le
    have hPL : (0 : ℝ) ≤ ((C.P : ℝ) + C.L) / 4 := by linarith
    have ha : (0 : ℝ) ≤ 1 / 10 ^ 5 * C.a := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hx0 hPL, mul_le_mul_of_nonneg_left hl2 ha]
  have hPL32 : (C.P : ℝ) / 4 + (C.L : ℝ) / 4 + (C.L : ℝ) / 4 ≤ 32 := by
    have : ((C.P + 2 * C.L : ℤ) : ℝ) ≤ 128 := by exact_mod_cast hb1
    push_cast at this; linarith
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  rw [le_div_iff₀ h2N]
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc Real.exp (((C.P : ℝ) / 4 + (C.L : ℝ) / 4) * (x0 * N + S) + (C.L : ℝ) / 4 * S +
        C.a * Real.log 2 * ((N : ℝ) / 10 ^ 5)) *
        (((dnIq C.v C.w C.P C.a : ℚ) : ℝ) * dnExR ((C.L : ℝ) / 4)) ^ N * 2 ^ N
      = Real.exp (((C.P : ℝ) / 4 + (C.L : ℝ) / 4) * (x0 * N + S) + (C.L : ℝ) / 4 * S +
          C.a * Real.log 2 * ((N : ℝ) / 10 ^ 5)) *
          ((2 : ℝ) ^ N * (((dnIq C.v C.w C.P C.a : ℚ) : ℝ) * dnExR ((C.L : ℝ) / 4)) ^ N) := by ring
    _ ≤ Real.exp (((C.P : ℝ) / 4 + (C.L : ℝ) / 4) * (x0 * N + S) + (C.L : ℝ) / 4 * S +
          C.a * Real.log 2 * ((N : ℝ) / 10 ^ 5)) * Real.exp (C.r * N) := by gcongr
    _ = Real.exp (N * ((C.r : ℝ) + ((C.P : ℝ) + C.L) / 4 * x0 + 1 / 10 ^ 5 * C.a * Real.log 2) +
          ((C.P : ℝ) / 4 + (C.L : ℝ) / 4 + (C.L : ℝ) / 4) * S) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-((dnR : ℝ) * N)) * Real.exp (32 * S) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        nlinarith [mul_le_mul_of_nonneg_left hrate hNr, mul_le_mul_of_nonneg_right hPL32 hS]

/-- **One certified cell, the self case**: `P(DNSelfEv) ≤ e^{-1.0106 N} e^{32 S}`. -/
theorem dn_cell_self_le (hN : 2 ≤ N) {C : DNCell} (hC : C ∈ dnCells) (s : State N) {S : ℝ} (hS : 0 ≤ S) :
    cubeM N (DNSelfEv s ((C.v : ℝ) ^ 4) ((C.w : ℝ) ^ 4) (x0 * N + S) ((N : ℝ) / 10 ^ 5)) ≤
      ENNReal.ofReal (Real.exp (-((dnR : ℝ) * N)) * Real.exp (32 * S)) := by
  obtain ⟨h1, h2, h3, -, -, -, -, -, -, -, -, -, -, -, -, h16, h17, h18, h19, h20⟩ :=
    dnCellOK_spec ((List.all_eq_true.1 dnCells_ok) C hC)
  have hb := (List.all_eq_true.1 dnCells_bounds) C hC
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨-, hb2⟩, -⟩ := hb
  have hv : (0 : ℝ) < C.v := by exact_mod_cast h1
  have hw : (0 : ℝ) < C.w := by exact_mod_cast (lt_of_lt_of_le h1 h2)
  have hv4 : (0 : ℝ) < (C.v : ℝ) ^ 4 := by positivity
  have hvc : (C.v : ℝ) ^ 4 ≤ (C.w : ℝ) ^ 4 := pow_le_pow_left₀ hv.le (by exact_mod_cast h2) 4
  have hc1 : (C.w : ℝ) ^ 4 ≤ 1 := pow_le_one₀ hw.le (by exact_mod_cast h3)
  have hcast : (((C.Ps : ℤ) : ℝ)) / 4 = (C.Ps : ℝ) / 4 := by push_cast; rfl
  have ht : (0 : ℝ) ≤ ((C.Ps : ℤ) : ℝ) / 4 := by rw [hcast]; positivity
  have hμ : (0 : ℝ) ≤ C.As * Real.log 2 := by positivity
  refine (dn_self_row hN s hv4 hvc hc1 ht hμ).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [dnIy_cell h1 (lt_of_lt_of_le h1 h2)]
  have hI : ((dnIq C.v C.w C.Ps C.As : ℚ) : ℝ) ≤ C.ubs := by exact_mod_cast h16
  have hI0 : (0 : ℝ) ≤ ((dnIq C.v C.w C.Ps C.As : ℚ) : ℝ) := by
    rw [← dnIy_cell h1 (lt_of_lt_of_le h1 h2)]
    exact dnIy_nonneg hv4 hvc hc1 (by intro h; linarith)
  have hq0 : (0 : ℝ) < ((C.ubs : ℚ) : ℝ) := by exact_mod_cast h17
  have hlog : Real.log ((C.ubs : ℚ) : ℝ) ≤ C.rs :=
    crLog_le (q := C.ubs) (r := C.rs) C.ks C.n (by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨h17, h18⟩, h19⟩)
  have hqexp : ((C.ubs : ℚ) : ℝ) ≤ Real.exp C.rs := by
    rw [← Real.log_le_iff_le_exp hq0]; exact hlog
  have hpow : (((dnIq C.v C.w C.Ps C.As : ℚ) : ℝ)) ^ N ≤ Real.exp (C.rs * N) := by
    rw [mul_comm (C.rs : ℝ), Real.exp_nat_mul]
    exact pow_le_pow_left₀ hI0 (hI.trans hqexp) N
  have ht' : (0 : ℝ) ≤ (C.Ps : ℝ) / 4 := by positivity
  have hrate : ((C.rs : ℚ) : ℝ) + (C.Ps : ℝ) / 4 * x0 + 1 / 10 ^ 5 * C.As * Real.log 2 ≤ -(dnR : ℝ) := by
    have hR := (Rat.cast_le (K := ℝ)).2 h20
    push_cast at hR
    have hx0 := cr_x0_bounds.2
    have hl2 := (cr_log2_bounds).2.le
    have ha : (0 : ℝ) ≤ 1 / 10 ^ 5 * C.As := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hx0 ht', mul_le_mul_of_nonneg_left hl2 ha]
  have hP32 : (C.Ps : ℝ) / 4 ≤ 32 := by
    have : (C.Ps : ℝ) ≤ 128 := by exact_mod_cast hb2
    linarith
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [hcast]
  calc Real.exp ((C.Ps : ℝ) / 4 * (x0 * N + S) + C.As * Real.log 2 * ((N : ℝ) / 10 ^ 5)) *
        (((dnIq C.v C.w C.Ps C.As : ℚ) : ℝ)) ^ N
      ≤ Real.exp ((C.Ps : ℝ) / 4 * (x0 * N + S) + C.As * Real.log 2 * ((N : ℝ) / 10 ^ 5)) *
          Real.exp (C.rs * N) := by gcongr
    _ = Real.exp (N * ((C.rs : ℝ) + (C.Ps : ℝ) / 4 * x0 + 1 / 10 ^ 5 * C.As * Real.log 2) +
          (C.Ps : ℝ) / 4 * S) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-((dnR : ℝ) * N)) * Real.exp (32 * S) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        nlinarith [mul_le_mul_of_nonneg_left hrate hNr, mul_le_mul_of_nonneg_right hP32 hS]

/-! ### The union over cells and anchor rows -/

/-- The certified natural event: some cell and some anchor row `r0` (the self event when `r0 = s`). -/
def DNEv (N : ℕ) (s : State N) (S : ℝ) : Set (Param N) :=
  {w | ∃ C ∈ dnCells, ∃ r0 : State N,
    (r0 = s ∧ w ∈ DNSelfEv s ((C.v : ℝ) ^ 4) ((C.w : ℝ) ^ 4) (x0 * N + S) ((N : ℝ) / 10 ^ 5)) ∨
    (r0 ≠ s ∧ w ∈ DNCellEv s r0 ((C.v : ℝ) ^ 4) ((C.w : ℝ) ^ 4) (x0 * N + S) S ((N : ℝ) / 10 ^ 5))}

deriving instance DecidableEq for DNCell

lemma dnCells_length : dnCells.length = 118 := by decide +kernel

/-- **The natural certificate, probability form**: `P(DNEv) ≤ 236 e^{32 S} e^{-1.0106 N}`. -/
theorem dnNatEv_le (hN : 2 ≤ N) (s : State N) {S : ℝ} (hS : 0 ≤ S) :
    cubeM N (DNEv N s S) ≤ ENNReal.ofReal (236 * (Real.exp (-((dnR : ℝ) * N)) * Real.exp (32 * S))) := by
  set E := Real.exp (-((dnR : ℝ) * N)) * Real.exp (32 * S) with hE
  have hE0 : 0 ≤ E := by positivity
  set T : DNCell → Set (Param N) := fun C =>
    DNSelfEv s ((C.v : ℝ) ^ 4) ((C.w : ℝ) ^ 4) (x0 * N + S) ((N : ℝ) / 10 ^ 5) ∪
      ⋃ r0 ∈ (univ.erase s : Finset (State N)),
        DNCellEv s r0 ((C.v : ℝ) ^ 4) ((C.w : ℝ) ^ 4) (x0 * N + S) S ((N : ℝ) / 10 ^ 5) with hT
  have hsub : DNEv N s S ⊆ ⋃ C ∈ dnCells.toFinset, T C := by
    rintro w ⟨C, hC, r0, h⟩
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨C, List.mem_toFinset.2 hC, ?_⟩
    rcases h with ⟨-, h⟩ | ⟨hr, h⟩
    · exact Or.inl h
    · refine Or.inr ?_
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨r0, mem_erase.2 ⟨hr, mem_univ _⟩, h⟩
  have hTC : ∀ C ∈ dnCells.toFinset, cubeM N (T C) ≤ ENNReal.ofReal (2 * E) := by
    intro C hC
    have hC' := List.mem_toFinset.1 hC
    calc cubeM N (T C) ≤ cubeM N (DNSelfEv s ((C.v : ℝ) ^ 4) ((C.w : ℝ) ^ 4) (x0 * N + S) ((N : ℝ) / 10 ^ 5)) +
          cubeM N (⋃ r0 ∈ (univ.erase s : Finset (State N)),
            DNCellEv s r0 ((C.v : ℝ) ^ 4) ((C.w : ℝ) ^ 4) (x0 * N + S) S ((N : ℝ) / 10 ^ 5)) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal E + ∑ r0 ∈ (univ.erase s : Finset (State N)),
            cubeM N (DNCellEv s r0 ((C.v : ℝ) ^ 4) ((C.w : ℝ) ^ 4) (x0 * N + S) S ((N : ℝ) / 10 ^ 5)) :=
          add_le_add (dn_cell_self_le hN hC' s hS) (measure_biUnion_finset_le _ _)
      _ ≤ ENNReal.ofReal E + ∑ _r0 ∈ (univ : Finset (State N)), ENNReal.ofReal (E / 2 ^ N) := by
          refine add_le_add le_rfl ((sum_le_sum fun r0 hr0 => dn_cell_two_le hN hC' (ne_of_mem_erase hr0) hS).trans
            (sum_le_sum_of_subset (erase_subset _ _)))
      _ = ENNReal.ofReal (2 * E) := by
          rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hE0 (by positivity)]
          congr 1
          push_cast
          field_simp
          ring
  calc cubeM N (DNEv N s S) ≤ cubeM N (⋃ C ∈ dnCells.toFinset, T C) := measure_mono hsub
    _ ≤ ∑ C ∈ dnCells.toFinset, cubeM N (T C) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _C ∈ dnCells.toFinset, ENNReal.ofReal (2 * E) := sum_le_sum hTC
    _ ≤ (118 : ENNReal) * ENNReal.ofReal (2 * E) := by
        rw [sum_const, nsmul_eq_mul]
        gcongr
        have := List.toFinset_card_le dnCells
        rw [dnCells_length] at this
        exact_mod_cast this
    _ = ENNReal.ofReal (236 * E) := by
        rw [show (118 : ENNReal) = ENNReal.ofReal 118 by simp, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring

end

end Census
end IIT
