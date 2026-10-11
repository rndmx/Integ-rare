/-
Census, B1 LTBetaHi, round-2 open item (c), probability part: **`P(many adverse members) ≤ e^{-2N}`**.

* `lt3_mem_prob`: for a fixed class `Q` (`7 ≤ m = qM Q`, `N ≤ D0 m`, `352 D0² ≤ N`), the 44 member-specific
  families exceed `m²/352` adverse indices with probability `≤ 86 e^{-3N}` (`lt2_kind_mT/Ot/N0`, level `lt2κ`);
* `lt3_unit_prob`: the four unit-level families exceed `m₃ - 1` adverse units with probability `≤ 6 e^{-3N}`
  (count lemmas at level `κ`, binomial bound `lt3_unit_binom`);
* **`lt3_adv_ev`**: eventually, for all `s, ε, γ, n`,
  `P(|Sp| < 12 ∧ 7 ≤ m ∧ N ≤ D0 m ∧ m² < 4 |lt3Adv κ|) ≤ e^{-2N}` (`m = qM (lt3WQ ..)`; union over the `≤ 2^N`
  classes `Q`; the deterministic step is `lt3_bad_quarter` + `lt3_adv_card`).
-/
import IIT.Census.B1LTHiLight2

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

lemma lt3bits_pos : ∀ u : Fin (2 ^ 3), u ≠ 0 → 0 < (lt3bits u).card := by decide

/-! ### The member-specific families of a fixed class -/

/-- **The 44 member-specific families of a fixed class are rarely large.** -/
theorem lt3_mem_prob (Q : Finset (Fin N)) (h7 : 7 ≤ qM Q) (hN7 : 7 ≤ N) {D0 : ℕ}
    (hQ : N ≤ D0 * qM Q) (hND : 352 * D0 * D0 ≤ N)
    (hev : 3 * (N : ℝ) + (N : ℝ) ^ 2 * 12 ≤ lt2κ * sigN N / (4 * lt2θ N)) (hN8 : 8 * (1 / 2 : ℝ) ^ N ≤ lt2tG N)
    (hextra : ∀ d m : ℕ, d ≤ N ^ 2 →
      ((d.choose m : ℕ) : ℝ) * 2 ^ m * (lt2B2 N + (d : ℝ) ^ 2 * lt2Bpair N) ≤ Real.exp (-(3 * (N : ℝ)))) :
    cubeM N {w | ¬ lt3MemGood Q w} ≤ ENNReal.ofReal (86 * Real.exp (-(3 * N))) := by
  classical
  set m := qM Q with hm
  set m' := m * m / 352 + 1 with hm'
  have hm1 : 1 ≤ m' := by omega
  have hlt : m * m < 352 * m' := Nat.lt_mul_div_succ (m * m) (by norm_num)
  have hQc : Q.card ≤ N := (card_le_univ Q).trans (by simp)
  have h3m : 3 * m ≤ N := (Nat.mul_div_le Q.card 3).trans hQc
  have h9 : 9 * (m * m) ≤ N * N := by nlinarith
  have hD0 : 1 ≤ D0 := by
    rcases Nat.eq_zero_or_pos D0 with h | h
    · rw [h, zero_mul] at hQ; omega
    · exact h
  -- `N < m'`
  have hNm' : N < m' := by
    have k1 : N * N ≤ D0 * D0 * (m * m) := by
      calc N * N ≤ (D0 * m) * (D0 * m) := Nat.mul_le_mul hQ hQ
        _ = D0 * D0 * (m * m) := by ring
    have k2 : D0 * D0 * (m * m) < D0 * D0 * (352 * m') :=
      Nat.mul_lt_mul_of_pos_left hlt (Nat.mul_pos hD0 hD0)
    have k3 : D0 * D0 * (352 * m') ≤ N * m' := by
      calc D0 * D0 * (352 * m') = (352 * D0 * D0) * m' := by ring
        _ ≤ N * m' := Nat.mul_le_mul_right _ hND
    exact Nat.lt_of_mul_lt_mul_left (k1.trans_lt (k2.trans_le k3))
  have hmN : (N : ℝ) / 491520 ≤ m' := by
    have : (N : ℝ) ≤ m' := by exact_mod_cast hNm'.le
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith [div_le_self hN0 (by norm_num : (1 : ℝ) ≤ 491520)]
  have hmN2 : (m' : ℝ) ≤ (N : ℝ) ^ 2 := by
    have : m' ≤ N * N := by
      have := Nat.div_le_self (m * m) 352
      omega
    exact_mod_cast (show m' ≤ N ^ 2 by rw [sq]; exact this)
  have hP8 : ∀ P : ℕ, P ≤ 8 * (m * m) → (P : ℝ) ≤ 12288 * m' := fun P hP => by
    have : P ≤ 12288 * m' := by omega
    exact_mod_cast this
  have hP24 : ∀ P : ℕ, P ≤ 24 * (m * m) → (P : ℝ) ≤ 12288 * m' := fun P hP => by
    have : P ≤ 12288 * m' := by omega
    exact_mod_cast this
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  -- the three kinds of families
  have hM : cubeM N {w | m' ≤ (lt3AdvM Q w).card} ≤ ENNReal.ofReal (Real.exp (-(3 * N))) :=
    (measure_mono fun w hw => hw).trans (lt2_kind_mT hev (lt3Pm Q) _ (lt3Pm_inj Q)
      (fun x hx => Finset.card_pos.1 (by rw [pkSet_card_eq]; have := (mem_filter.1 hx).2; omega))
      hm1 (hP8 _ (lt3Pm_card Q)) hmN hmN2)
  have hO : cubeM N {w | m' ≤ (lt3AdvO Q w).card} ≤ ENNReal.ofReal (Real.exp (-(3 * N))) :=
    (measure_mono fun w hw => hw).trans (lt2_kind_Ot hev (lt3Po Q) _ (lt3Po_inj Q)
      (fun x hx => Finset.card_pos.1 (by rw [pkSet_card_eq]; exact lt3bits_pos _ (mem_filter.1 hx).2.1))
      hm1 (hP24 _ (lt3Po_card Q)) hmN hmN2)
  have hNfam : ∀ ci rb β, rb ≠ 0 →
      cubeM N {w | m' ≤ (lt3AdvN Q ci rb β w).card} ≤ ENNReal.ofReal (2 * Real.exp (-(3 * N))) := by
    intro ci rb β hrb
    refine (measure_mono fun w hw => hw).trans (lt2_kind_N0 (b := β) hev hN8 hN1 hextra
      (lt3LamOf Q (lt3LamT rb)) (lt3Pn Q ci rb) _ (lt3Pn_inj Q ci rb)
      (fun x _ => lt3_odd_Lam Q (lt3uE Q x.1) (lt3uE_part_iff Q x.1) hrb)
      (fun x _ x' _ _ => lt3_symmDiff_ne (by rw [pkSet_card_eq]; exact lt3bits_card_le _)
        (by rw [pkSet_card_eq]; exact lt3bits_card_le _) (lt3LamOf_card h7 hN7 _))
      hm1 (hP8 _ (lt3Pn_card Q ci rb)) hmN hmN2 ?_)
    have := lt3Pn_card Q ci rb
    have h9' : 9 * (qM Q * qM Q) ≤ N * N := h9
    rw [sq]; omega
  -- the union
  set K := (univ : Finset (Fin 3)) ×ˢ ((univ.filter fun rb : Fin (2 ^ 3) => rb ≠ 0) ×ˢ (univ : Finset Bool))
    with hK
  have hKc : K.card = 42 := by rw [hK]; decide
  have hsub : {w : Param N | ¬ lt3MemGood Q w} ⊆ ({w | m' ≤ (lt3AdvM Q w).card} ∪
      {w | m' ≤ (lt3AdvO Q w).card}) ∪ ⋃ k ∈ K, {w | m' ≤ (lt3AdvN Q k.1 k.2.1 k.2.2 w).card} := by
    intro w hw
    simp only [lt3MemGood, Set.mem_setOf_eq, not_and_or, not_forall, not_lt] at hw
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    rcases hw with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · obtain ⟨ci, rb, hrb, β, h⟩ := h
      exact Or.inr ⟨(ci, rb, β), mem_product.2 ⟨mem_univ _, mem_product.2 ⟨mem_filter.2 ⟨mem_univ _, hrb⟩,
        mem_univ _⟩⟩, h⟩
  have hE := Real.exp_pos (-(3 * (N : ℝ)))
  have hU : cubeM N (⋃ k ∈ K, {w | m' ≤ (lt3AdvN Q k.1 k.2.1 k.2.2 w).card}) ≤
      ENNReal.ofReal (84 * Real.exp (-(3 * N))) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ k ∈ K, cubeM N {w | m' ≤ (lt3AdvN Q k.1 k.2.1 k.2.2 w).card}
        ≤ ∑ _k ∈ K, ENNReal.ofReal (2 * Real.exp (-(3 * N))) := Finset.sum_le_sum fun k hk =>
          hNfam _ _ _ (mem_filter.1 (mem_product.1 (mem_product.1 hk).2).1).2
      _ = ENNReal.ofReal (84 * Real.exp (-(3 * N))) := by
          rw [Finset.sum_const, hKc, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1; push_cast; ring
  refine (measure_mono hsub).trans (bd_union2 (by positivity) (by positivity)
    (bd_union2 hE.le hE.le hM hO le_rfl) hU ?_)
  linarith

/-! ### The unit-level families -/

/-- The binomial step for the unit families: `C(N, m₃) 2^{m₃} e^{-X} ≤ e^{-3N}`. -/
lemma lt3_unit_binom {m3 : ℕ} {D κ : ℝ} (hD : 1 ≤ D) (hd : (N : ℝ) ≤ D * m3) (hm3N : m3 ≤ N)
    (hκ : 4 * (3 * D + Real.log (2 * Real.exp 1 * D)) ≤ κ ^ 2)
    (hB : 3 * (N : ℝ) + N * Real.log (2 * Real.exp 1 * D) ≤ κ * sigN N / (4 * lt2θ N))
    {X : ℝ} (hX : min (m3 * κ ^ 2 / 4) (κ * sigN N / (4 * lt2θ N)) ≤ X) :
    ((N.choose m3 : ℕ) : ℝ) * 2 ^ m3 * Real.exp (-X) ≤ Real.exp (-(3 * N)) := by
  have hlog : 0 ≤ Real.log (2 * Real.exp 1 * D) := Real.log_nonneg (by
    have := Real.add_one_le_exp 1; nlinarith)
  have hm0 : (0 : ℝ) ≤ m3 := Nat.cast_nonneg _
  have hmN : (m3 : ℝ) ≤ N := by exact_mod_cast hm3N
  refine lt2_binom_le hD hd (le_trans (le_min ?_ ?_) hX)
  · have k1 : (m3 : ℝ) * (4 * (3 * D + Real.log (2 * Real.exp 1 * D))) ≤ m3 * κ ^ 2 :=
      mul_le_mul_of_nonneg_left hκ hm0
    nlinarith
  · have k2 : (m3 : ℝ) * Real.log (2 * Real.exp 1 * D) ≤ N * Real.log (2 * Real.exp 1 * D) :=
      mul_le_mul_of_nonneg_right hmN hlog
    linarith

/-- **The unit-level families are rarely large** (level `κσ_N`, threshold `m₃`). -/
theorem lt3_unit_prob {κ D : ℝ} (hκ0 : 0 < κ) (hD : 1 ≤ D) {m3 : ℕ} (hm3 : 1 ≤ m3) (hm3N : m3 ≤ N)
    (hd : (N : ℝ) ≤ D * m3) (hκ : 4 * (3 * D + Real.log (2 * Real.exp 1 * D)) ≤ κ ^ 2)
    (hB : 3 * (N : ℝ) + N * Real.log (2 * Real.exp 1 * D) ≤ κ * sigN N / (4 * lt2θ N))
    (hN8 : 8 * (1 / 2 : ℝ) ^ N ≤ lt2tG N) (hN1 : 1 ≤ N)
    (hextra : ∀ d m : ℕ, d ≤ N ^ 2 →
      ((d.choose m : ℕ) : ℝ) * 2 ^ m * (lt2B2 N + (d : ℝ) ^ 2 * lt2Bpair N) ≤ Real.exp (-(3 * (N : ℝ)))) :
    cubeM N {w | ¬ lt3UnitGood κ m3 w} ≤ ENNReal.ofReal (6 * Real.exp (-(3 * N))) := by
  classical
  have hσ : 0 < sigN N := by unfold sigN; positivity
  have hθ : 0 < lt2θ N := Real.exp_pos _
  have hE := Real.exp_pos (-(3 * (N : ℝ)))
  have hNne : N ≠ 0 := by omega
  have hcard : (univ : Finset (Fin N)).card = N := by simp
  -- `m_{x}`
  have h1 : cubeM N {w | m3 ≤ (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2mT w {x}|).card} ≤
      ENNReal.ofReal (Real.exp (-(3 * N))) := by
    refine (lt2_mT_count_img univ (fun x : Fin N => ({x} : Finset (Fin N)))
      (fun x _ y _ h => singleton_injective h) (fun x _ => singleton_nonempty x) hκ0 m3 hm3).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [hcard]
    exact lt3_unit_binom hD hd hm3N hκ hB le_rfl
  -- `Õ_x({x})`
  have h2 : cubeM N {w | m3 ≤ (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2Ot w (x, {x})|).card} ≤
      ENNReal.ofReal (Real.exp (-(3 * N))) := by
    refine (lt2_Ot_count_img univ (fun x : Fin N => (x, ({x} : Finset (Fin N))))
      (fun x _ y _ h => (Prod.mk.inj h).1) (fun x _ => singleton_nonempty x) hκ0 m3 hm3).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [hcard]
    refine lt3_unit_binom hD hd hm3N hκ hB (min_le_min ?_ ?_)
    · have := sq_nonneg κ; have hm0 : (0 : ℝ) ≤ m3 := Nat.cast_nonneg _; nlinarith
    · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  -- `Ñ^β_{x,{x}}({x})`, class `univ`
  have h3 : ∀ β : Bool, cubeM N {w | m3 ≤ (univ.filter fun x : Fin N =>
      κ * sigN N ≤ |lt2N0 univ β w (x, {x}, {x})|).card} ≤ ENNReal.ofReal (2 * Real.exp (-(3 * N))) := by
    intro β
    have hodd : ∀ x ∈ (univ : Finset (Fin N)),
        (((fun x : Fin N => ((x, {x}, {x}) : LT2Idx N)) x).2.1 ∩ univ).card % 2 = 1 := fun x _ => by
      simp
    have hT : ∀ x ∈ (univ : Finset (Fin N)), ∀ x' ∈ (univ : Finset (Fin N)),
        ((fun x : Fin N => ((x, {x}, {x}) : LT2Idx N)) x).2.1 =
          ((fun x : Fin N => ((x, {x}, {x}) : LT2Idx N)) x').2.1 →
        symmDiff ((fun x : Fin N => ((x, {x}, {x}) : LT2Idx N)) x).2.2
          ((fun x : Fin N => ((x, {x}, {x}) : LT2Idx N)) x').2.2 ≠ univ := by
      intro x _ x' _ h
      simp only at h ⊢
      rw [h, symmDiff_self]
      intro he
      have : x' ∈ (univ : Finset (Fin N)) := mem_univ _
      rw [← he] at this
      exact Finset.notMem_empty _ this
    refine (lt2_N0_count_img (b := β) univ univ (fun x : Fin N => ((x, {x}, {x}) : LT2Idx N))
      (fun x _ y _ h => (Prod.mk.inj h).1) hodd hT hN8 hNne hκ0 m3 hm3).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hcard, mul_add]
    have hN4 : (m3 : ℝ) / (N : ℝ) ^ 4 ≤ 1 := by
      have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      rw [div_le_one (by positivity)]
      calc (m3 : ℝ) ≤ N := by exact_mod_cast hm3N
        _ ≤ (N : ℝ) ^ 4 := by
            calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
              _ ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ hNr (by norm_num)
    have k1 : ((N.choose m3 : ℕ) : ℝ) * 2 ^ m3 *
        Real.exp (-min (3 * m3 * κ ^ 2 / (2 + m3 / (N : ℝ) ^ 4)) (κ * sigN N / lt2θ N)) ≤
        Real.exp (-(3 * N)) := by
      refine lt3_unit_binom hD hd hm3N hκ hB (min_le_min ?_ ?_)
      · have hm0 : (0 : ℝ) ≤ m3 := Nat.cast_nonneg _
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg κ, mul_nonneg hm0 (sq_nonneg κ)]
      · exact div_le_div_of_nonneg_left (by positivity) hθ (by linarith)
    have k2 := hextra N m3 (by rw [sq]; exact Nat.le_mul_self N)
    have hc2 : ((univ : Finset (Fin N)).card : ℝ) = N := by exact_mod_cast hcard
    rw [hc2] at *
    linarith
  -- the union
  have hsub : {w : Param N | ¬ lt3UnitGood κ m3 w} ⊆
      ({w | m3 ≤ (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2mT w {x}|).card} ∪
        {w | m3 ≤ (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2Ot w (x, {x})|).card}) ∪
      ({w | m3 ≤ (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2N0 univ true w (x, {x}, {x})|).card} ∪
        {w | m3 ≤ (univ.filter fun x : Fin N => κ * sigN N ≤ |lt2N0 univ false w (x, {x}, {x})|).card}) := by
    intro w hw
    simp only [lt3UnitGood, Set.mem_setOf_eq, not_and_or, not_lt] at hw
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases hw with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine (measure_mono hsub).trans (bd_union2 (by positivity) (by positivity)
    (bd_union2 hE.le hE.le h1 h2 le_rfl) (bd_union2 (by positivity) (by positivity) (h3 true) (h3 false) le_rfl) ?_)
  linarith

/-- The unit exponent condition holds eventually. -/
lemma lt3_unit_hB {κ D : ℝ} (hκ0 : 0 < κ) (hD : 1 ≤ D) : ∀ᶠ N : ℕ in atTop,
    3 * (N : ℝ) + N * Real.log (2 * Real.exp 1 * D) ≤ κ * sigN N / (4 * lt2θ N) := by
  have hlog : 0 ≤ Real.log (2 * Real.exp 1 * D) := Real.log_nonneg (by
    have := Real.add_one_le_exp 1; nlinarith)
  set c := 4 * (3 + Real.log (2 * Real.exp 1 * D)) / κ with hc
  have hc0 : 0 < c := by positivity
  filter_upwards [cr_ev_poly_exp 1 (Real.log c) (δ := 1 / 400) (by norm_num)] with N hN
  rw [Real.exp_log hc0, pow_one] at hN
  have hθ : 0 < lt2θ N := Real.exp_pos _
  have hratio : κ * sigN N / (4 * lt2θ N) = κ / 4 * Real.exp ((N : ℝ) / 400) := by
    rw [← lt2_sig_div_theta]; field_simp
  rw [hratio, show (N : ℝ) / 400 = 1 / 400 * N by ring]
  have k1 : κ / 4 * (((N : ℝ) + 1) * c) ≤ κ / 4 * Real.exp (1 / 400 * N) :=
    mul_le_mul_of_nonneg_left hN (by positivity)
  have k2 : κ / 4 * (((N : ℝ) + 1) * c) = ((N : ℝ) + 1) * (3 + Real.log (2 * Real.exp 1 * D)) := by
    rw [hc]; field_simp
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-! ### Assembly -/

/-- **Few adverse members.** For `D0 ≥ 1` and `κ ≥ lt2κ` with `κ² ≥ 4(3 · 96 D0 + log(2e · 96 D0))`, eventually,
for all `s, ε, γ, n`: with `m = qM (lt3WQ s ε γ n w)`,
`P(|Sp| < 12 ∧ 7 ≤ m ∧ N ≤ D0 m ∧ m² < 4 |lt3Adv κ w|) ≤ e^{-2N}`. -/
theorem lt3_adv_ev {D0 : ℕ} (hD0 : 1 ≤ D0) {κ : ℝ} (hκ1 : lt2κ ≤ κ)
    (hκ : 4 * (3 * (96 * (D0 : ℝ)) + Real.log (2 * Real.exp 1 * (96 * D0))) ≤ κ ^ 2) :
    ∀ᶠ N : ℕ in atTop, ∀ (s : State N) (ε γ : ℝ) (n : ℕ),
      cubeM N {w | (lt2Sp w).card < 12 ∧ 7 ≤ qM (lt3WQ s ε γ n w) ∧ N ≤ D0 * qM (lt3WQ s ε γ n w) ∧
        qM (lt3WQ s ε γ n w) * qM (lt3WQ s ε γ n w) < 4 * (lt3Adv s ε γ n κ w).card} ≤
      ENNReal.ofReal (Real.exp (-(2 * N))) := by
  classical
  have hκ0 : 0 < κ := lt_of_lt_of_le (by unfold lt2κ; norm_num) hκ1
  have hD : (1 : ℝ) ≤ 96 * (D0 : ℝ) := by
    have : (1 : ℝ) ≤ D0 := by exact_mod_cast hD0
    linarith
  filter_upwards [lt2_ev_kind, lt2_extra_small, lt3PE_small hκ0, eventually_ge_atTop (352 * D0 * D0),
    eventually_ge_atTop (96 * D0), eventually_ge_atTop 7, lt3_unit_hB hκ0 hD,
    bd_exp_ev (c := 3 / 10) (δ := 1 / 92) (by norm_num) (by norm_num)]
    with N hev hextra hpe hN352 hN96 hN7 hB h92 s ε γ n
  obtain ⟨hev1, hN8, hN1r⟩ := hev
  set m3 := N / (D0 * 96) + 1 with hm3def
  have hm3 : 1 ≤ m3 := Nat.le_add_left 1 _
  have hm3N : m3 ≤ N := by
    have : N / (D0 * 96) ≤ N / 2 := Nat.div_le_div_left (by nlinarith) (by norm_num)
    show N / (D0 * 96) + 1 ≤ N
    omega
  have hd : (N : ℝ) ≤ 96 * (D0 : ℝ) * m3 := by
    have h := Nat.lt_mul_div_succ N (show 0 < D0 * 96 by positivity)
    have : N ≤ 96 * D0 * m3 := by rw [hm3def]; nlinarith
    exact_mod_cast this
  set Qset := (univ : Finset (Finset (Fin N))).filter fun Q => 7 ≤ qM Q ∧ N ≤ D0 * qM Q with hQset
  have hsub : {w : Param N | (lt2Sp w).card < 12 ∧ 7 ≤ qM (lt3WQ s ε γ n w) ∧ N ≤ D0 * qM (lt3WQ s ε γ n w) ∧
      qM (lt3WQ s ε γ n w) * qM (lt3WQ s ε γ n w) < 4 * (lt3Adv s ε γ n κ w).card} ⊆
      (⋃ Q ∈ Qset, {w | ¬ lt3MemGood Q w}) ∪ {w | ¬ lt3UnitGood κ m3 w} := by
    intro w hw
    obtain ⟨hSp, h7, hQ, hbig⟩ := hw
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists, not_not] at hcon
    obtain ⟨hM, hU⟩ := hcon
    have hMQ := hM (lt3WQ s ε γ n w) (mem_filter.2 ⟨mem_univ _, h7, hQ⟩)
    have hm3Q : 96 * (m3 - 1) ≤ qM (lt3WQ s ε γ n w) := by
      have e1 : m3 - 1 = N / D0 / 96 := by rw [hm3def, Nat.div_div_eq_div_mul]; omega
      rw [e1]
      exact (Nat.mul_div_le (N / D0) 96).trans (Nat.div_le_of_le_mul hQ)
    have hq := lt3_bad_quarter (lt3WQ s ε γ n w) w hκ1 hm3Q hMQ hU
    have hP : (stPriv (lt3WSel s ε γ n) lt3PB w).card ≤ 24 * (13 * (N * N)) :=
      (lt3W_Priv_card s ε γ n w).trans (Nat.mul_le_mul_left 24 (lt3WSel_card s ε γ n hSp))
    have hpert : 2 * lt3PE s ε γ n w ≤ κ * sigN N / 2 := hpe _ hP
    have ha := lt3_adv_card s ε γ n w hpert
    omega
  have hE := Real.exp_pos (-(3 * (N : ℝ)))
  have hQc : (Qset.card : ℝ) ≤ 2 ^ N := by
    have : Qset.card ≤ 2 ^ N := (card_le_univ _).trans (by simp)
    exact_mod_cast this
  have hMem : cubeM N (⋃ Q ∈ Qset, {w | ¬ lt3MemGood Q w}) ≤
      ENNReal.ofReal (2 ^ N * (86 * Real.exp (-(3 * N)))) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ Q ∈ Qset, cubeM N {w | ¬ lt3MemGood Q w} ≤ ∑ _Q ∈ Qset, ENNReal.ofReal (86 * Real.exp (-(3 * N))) :=
          Finset.sum_le_sum fun Q hQ => by
            obtain ⟨h7, hQN⟩ := (mem_filter.1 hQ).2
            exact lt3_mem_prob Q h7 hN7 hQN hN352 hev1 hN8 hextra
      _ = ENNReal.ofReal (Qset.card * (86 * Real.exp (-(3 * N)))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hQc (by positivity))
  have hUnit := lt3_unit_prob hκ0 hD hm3 hm3N hd hκ hB hN8 (by omega) hextra
  refine (measure_mono hsub).trans (bd_union2 (by positivity) (by positivity) hMem hUnit ?_)
  -- `86 · 2^N e^{-3N} + 6 e^{-3N} ≤ e^{-2N}`
  have hl2 := Real.log_two_lt_d9
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h2N : (2 : ℝ) ^ N ≤ Real.exp (7 / 10 * N) := by
    rw [bd_two_pow]; exact Real.exp_le_exp.2 (by nlinarith)
  have e1 : Real.exp (7 / 10 * (N : ℝ)) * Real.exp (-(3 * N)) = Real.exp (-(3 / 10 * N)) * Real.exp (-(2 * N)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(3 * (N : ℝ))) ≤ Real.exp (-(3 / 10 * N)) * Real.exp (-(2 * N)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
  have hE2 := Real.exp_pos (-(2 * (N : ℝ)))
  have k1 : 2 ^ N * (86 * Real.exp (-(3 * (N : ℝ)))) ≤ 86 * (Real.exp (-(3 / 10 * N)) * Real.exp (-(2 * N))) := by
    have := mul_le_mul_of_nonneg_right h2N hE.le
    nlinarith
  have k2 : Real.exp (-(3 / 10 * (N : ℝ))) * Real.exp (-(2 * N)) ≤ 1 / 92 * Real.exp (-(2 * N)) :=
    mul_le_mul_of_nonneg_right h92 hE2.le
  nlinarith

end Census
end IIT
