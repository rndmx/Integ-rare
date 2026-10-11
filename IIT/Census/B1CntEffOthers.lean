/-
Census, B1, W14 work package WP3 (effect side), part 6: every other purview is strictly below
`({k1}, te)` (W5 Lemma E3'(ii)), and the assembly `effDet_proved : EffDetStmt` (E3'(iii)).
* `log_ratio_le`, `phiEat_le_B`: Fact E0(a) gives `φ_e(Z, z) ln 2 ≤ ∏_Z (1/2 + a_j) · Σ_Z (2 a_j + 3 ε_N)`;
* `others_real`: that bound is `< a - ε_N` for `Z ≠ {k1}` (cases `|Z| = 1, 2, ≥ 3`);
* `eff_others_lt`, `effDet_proved`.
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §8.  No `sorry`.
-/
import IIT.Census.B1CntEffPhi1

namespace IIT
namespace Census

/-! Helpers live in `IIT.Census.WP3` (avoids name clashes with the other work packages);
the blueprint names are re-exported to `IIT.Census` by `alias` at the end of the file. -/
namespace WP3

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### Real inequalities -/

lemma l_half_pow_le (l : ℕ) (hl : 3 ≤ l) : (l : ℝ) * (1 / 2) ^ l ≤ 3 / 8 := by
  have key : 8 * l ≤ 3 * 2 ^ l := by
    induction l, hl using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [pow_succ]
      have : 8 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
      omega
  have h : (8 : ℝ) * l ≤ 3 * 2 ^ l := by exact_mod_cast key
  rw [one_div_pow, mul_one_div, div_le_iff₀ (by positivity)]
  linarith

lemma log_ratio_le {f ab ε c : ℝ} (hc : c = 1 ∨ c = -1) (hab : |ab| ≤ ε) (hf16 : |f| ≤ 1 / 16)
    (hε16 : ε ≤ 1 / 16) (hp : 0 < 1 / 2 + c * f) :
    Real.log ((1 / 2 + c * f) / (1 / 2 + c * ab)) ≤ 2 * |f| + 3 * ε := by
  obtain ⟨hab1, hab2⟩ := abs_le.1 hab
  have hε0 : 0 ≤ ε := (abs_nonneg ab).trans hab
  have hf1 := neg_abs_le f
  have hf2 := le_abs_self f
  have hcf : c * f ≤ |f| ∧ -ε ≤ c * ab ∧ c * ab ≤ ε := by
    rcases hc with rfl | rfl
    · simp only [one_mul]; exact ⟨hf2, hab1, hab2⟩
    · simp only [neg_one_mul]; exact ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨h1, h2, h3⟩ := hcf
  have hq : 0 < 1 / 2 + c * ab := by linarith
  refine (Real.log_le_sub_one_of_pos (div_pos hp hq)).trans ?_
  rw [div_sub_one hq.ne', div_le_iff₀ hq]
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * |f| + 3 * ε) (by linarith : 0 ≤ c * ab + ε),
    mul_nonneg (abs_nonneg f) hε0, mul_nonneg hε0 hε0]

/-- **Case analysis of E3'(ii)** on the size of the purview. -/
lemma others_real {ι : Type*} (Z : Finset ι) (a : ι → ℝ) (k1 : ι) {f κ x ε : ℝ} (n : ℕ)
    (ha0 : ∀ j, 0 ≤ a j) (hax : ∀ j, a j ≤ x) (hk1 : a k1 = f)
    (hother : ∀ j, j ≠ k1 → a j + κ < f) (hκ : 12 * x ^ 2 + 8 * ε ≤ κ) (hε0 : 0 ≤ ε)
    (hfε : 100 * ε ≤ f) (hx : x ≤ 1 / 100) (hnx : (n : ℝ) * x ≤ 1 / 100) (hZn : Z.card ≤ n)
    (hZ : Z.Nonempty) (hZk : Z ≠ {k1}) :
    (∏ j ∈ Z, (1 / 2 + a j)) * ∑ j ∈ Z, (2 * a j + 3 * ε) < f - ε := by
  have hκ0 : 0 ≤ κ := by nlinarith [sq_nonneg x]
  have hx0 : 0 ≤ x := (ha0 k1).trans (hax k1)
  have hle : ∀ j, a j ≤ f := fun j => by
    by_cases hj : j = k1
    · rw [hj, hk1]
    · linarith [hother j hj]
  obtain ⟨j0, hj0, hj0k⟩ : ∃ j ∈ Z, j ≠ k1 := by
    by_contra h
    push Not at h
    apply hZk
    obtain ⟨i, hi⟩ := hZ
    have hik := h i hi
    ext j
    simp only [mem_singleton]
    exact ⟨fun hj => h j hj, fun hj => hj ▸ hik ▸ hi⟩
  have hfpos : 0 < f := by linarith [hother j0 hj0k, ha0 j0]
  have hεf : ε ≤ f / 100 := by linarith
  rcases Nat.lt_or_ge Z.card 3 with hlt | hge
  · rcases (show Z.card = 1 ∨ Z.card = 2 by have := card_pos.2 hZ; omega) with h1 | h2
    · -- one unit, not `k1`
      obtain ⟨j, rfl⟩ := card_eq_one.1 h1
      have hj : j ≠ k1 := fun h => hZk (by rw [h])
      rw [prod_singleton, sum_singleton]
      have hoj := hother j hj
      have hsq : a j ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (ha0 j) (hax j) 2
      have hae : a j * ε ≤ x * ε := mul_le_mul_of_nonneg_right (hax j) hε0
      have hxε : x * ε ≤ ε / 100 := by nlinarith
      nlinarith
    · -- two units
      obtain ⟨i, j, hij, rfl⟩ := card_eq_two.1 h2
      rw [prod_pair hij, sum_pair hij]
      have hS : a i + a j + κ < 2 * f := by
        by_cases hi : i = k1
        · have hj : j ≠ k1 := fun h => hij (hi.trans h.symm)
          rw [hi, hk1]; linarith [hother j hj]
        · by_cases hj : j = k1
          · rw [hj, hk1]; linarith [hother i hi]
          · linarith [hother i hi, hother j hj]
      set p := a i
      set q := a j
      have hp0 := ha0 i
      have hq0 := ha0 j
      have hpx := hax i
      have hqx := hax j
      have e : (1 / 2 + p) * (1 / 2 + q) * (2 * p + 3 * ε + (2 * q + 3 * ε)) =
          (p + q) / 2 + 3 / 2 * ε + (p + q) ^ 2 + 3 * ε * (p + q) + 2 * (p * q) * (p + q) +
            6 * (p * q) * ε := by ring
      rw [e]
      have hpq : p * q ≤ x ^ 2 := by nlinarith
      have hsq : (p + q) ^ 2 ≤ 4 * x ^ 2 := by nlinarith
      have h3 : ε * (p + q) ≤ ε / 50 := by nlinarith
      have h4 : (p * q) * (p + q) ≤ x ^ 2 / 50 := by
        have : p * q * (p + q) ≤ x ^ 2 * (2 * x) :=
          mul_le_mul hpq (by linarith) (by positivity) (by positivity)
        nlinarith
      have h5 : (p * q) * ε ≤ x ^ 2 / 100 := by
        have hfx : f ≤ x := hk1 ▸ hax k1
        have hε1 : ε ≤ 1 / 100 := by linarith
        have : p * q * ε ≤ x ^ 2 * ε := mul_le_mul_of_nonneg_right hpq hε0
        nlinarith
      nlinarith
  · -- at least three units
    set l := Z.card with hl
    have hprod : ∏ j ∈ Z, (1 / 2 + a j) ≤ (1 / 2) ^ l * Real.exp (∑ j ∈ Z, 2 * a j) := by
      have e : ∏ j ∈ Z, (1 / 2 + a j) = (1 / 2) ^ l * ∏ j ∈ Z, (2 * a j + 1) := by
        rw [← prod_const, ← prod_mul_distrib]
        exact prod_congr rfl fun j _ => by ring
      rw [e, Real.exp_sum]
      gcongr with j hj
      · exact fun j _ => by linarith [ha0 j]
      · exact Real.add_one_le_exp _
    have hsa : ∑ j ∈ Z, 2 * a j ≤ 1 / 50 := by
      have : ∑ j ∈ Z, 2 * a j ≤ ∑ _j ∈ Z, 2 * x := sum_le_sum fun j _ => by linarith [hax j]
      rw [sum_const, nsmul_eq_mul] at this
      have hln : (l : ℝ) ≤ n := by exact_mod_cast hZn
      nlinarith
    have hsa0 : 0 ≤ ∑ j ∈ Z, 2 * a j := sum_nonneg fun j _ => by linarith [ha0 j]
    have hexp : Real.exp (∑ j ∈ Z, 2 * a j) ≤ 103 / 100 := by
      have h1 : Real.exp (∑ j ∈ Z, 2 * a j) ≤ Real.exp (1 / 50) := Real.exp_le_exp.2 hsa
      have h2 := Real.abs_exp_sub_one_sub_id_le (x := 1 / 50) (by norm_num [abs_of_pos])
      have h3 := (abs_le.1 h2).2
      linarith
    have hsum : ∑ j ∈ Z, (2 * a j + 3 * ε) ≤ l * (2 * f + 3 * ε) := by
      have : ∑ j ∈ Z, (2 * a j + 3 * ε) ≤ ∑ _j ∈ Z, (2 * f + 3 * ε) :=
        sum_le_sum fun j _ => by linarith [hle j]
      rwa [sum_const, nsmul_eq_mul] at this
    have hP0 : 0 ≤ ∏ j ∈ Z, (1 / 2 + a j) := prod_nonneg fun j _ => by linarith [ha0 j]
    have hhalf := l_half_pow_le l hge
    have hpow0 : (0 : ℝ) ≤ (1 / 2) ^ l := by positivity
    calc (∏ j ∈ Z, (1 / 2 + a j)) * ∑ j ∈ Z, (2 * a j + 3 * ε)
        ≤ ((1 / 2) ^ l * (103 / 100)) * (l * (2 * f + 3 * ε)) := by
          apply mul_le_mul _ hsum (sum_nonneg fun j _ => by linarith [ha0 j]) (by positivity)
          exact hprod.trans (mul_le_mul_of_nonneg_left hexp hpow0)
      _ = (103 / 100) * ((l : ℝ) * (1 / 2) ^ l) * (2 * f + 3 * ε) := by ring
      _ ≤ (103 / 100) * (3 / 8) * (2 * f + 3 * ε) := by gcongr
      _ < f - ε := by nlinarith

/-! ### The bound through the total cut (Fact E0(a)) -/

section Upper

variable {s : State N} {K : Finset (Fin N)} {w : Param N}

theorem phiEat_le_B (hz : flipP s w ∈ openCube N) (hMne : (univ \ K).Nonempty)
    (hcol : ∀ j, |effDevA w s ∅ s j| ≤ epsN N) (hε16 : epsN N ≤ 1 / 16)
    (ha : ∀ j, |fK w s K j| ≤ 1 / 16) (Z : Finset (Fin N)) (hZ : Z.Nonempty) (z : State N) :
    phiEat (tpmOf (flipP s w)) (univ \ K) s Z z * Real.log 2 ≤
      (∏ j ∈ Z, (1 / 2 + |fK w s K j|)) * ∑ j ∈ Z, (2 * |fK w s K j| + 3 * epsN N) := by
  set T := tpmOf (flipP s w) with hT
  set M := univ \ K with hMdef
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h1 : phiEat T M s Z z ≤ phiEofPartition T M s Z z (Partition.total hMne Z) := by
    have := phiEatAt_le_total T univ s M s Z z hMne hZ
    rwa [phiEatAt_univ, phiEofPartitionAt_univ] at this
  -- per-unit facts
  have hunit : ∀ j, 0 < effUnit T M s j (z j) ∧ 0 < effUnit T ∅ s j (z j) ∧
      effUnit T M s j (z j) ≤ 1 / 2 + |fK w s K j| ∧
      Real.log (effUnit T M s j (z j) / effUnit T ∅ s j (z j)) ≤
        2 * |fK w s K j| + 3 * epsN N := by
    intro j
    obtain ⟨c, hc, hcA⟩ := effUnit_sign s w j (z j)
    have hp := hcA M s
    have hq := hcA ∅ s
    have hpp := effUnit_pos_flip hz M s j (z j)
    have hqp := effUnit_pos_flip hz ∅ s j (z j)
    have hfM : effDevA w s M s j = fK w s K j := rfl
    rw [hfM] at hp
    refine ⟨hpp, hqp, ?_, ?_⟩
    · rw [hp]
      rcases hc with rfl | rfl
      · linarith [le_abs_self (fK w s K j)]
      · linarith [neg_abs_le (fK w s K j)]
    · rw [hp, hq]
      rw [hp] at hpp
      exact log_ratio_le hc (hcol j) (ha j) hε16 hpp
  have hB0 : 0 ≤ ∑ j ∈ Z, (2 * |fK w s K j| + 3 * epsN N) :=
    sum_nonneg fun j _ => by have := (abs_nonneg ((effDevA w s ∅ s j))).trans (hcol j); positivity
  have hlog : Real.logb 2 (effRep T M s Z z / partEffRep T M s Z z (Partition.total hMne Z)) ≤
      (∑ j ∈ Z, (2 * |fK w s K j| + 3 * epsN N)) / Real.log 2 := by
    rw [partEffRep_total, effRep, ← prod_div_distrib, Real.logb,
      Real.log_prod (fun j _ => (div_pos (hunit j).1 (hunit j).2.1).ne')]
    exact div_le_div_of_nonneg_right (sum_le_sum fun j _ => (hunit j).2.2.2) hl2.le
  have hpos : pos (Real.logb 2 (effRep T M s Z z / partEffRep T M s Z z (Partition.total hMne Z))) ≤
      (∑ j ∈ Z, (2 * |fK w s K j| + 3 * epsN N)) / Real.log 2 :=
    pos_le (div_nonneg hB0 hl2.le) hlog
  have hE : effRep T M s Z z ≤ ∏ j ∈ Z, (1 / 2 + |fK w s K j|) :=
    prod_le_prod (fun j _ => (hunit j).1.le) fun j _ => (hunit j).2.2.1
  have hE0 : 0 ≤ effRep T M s Z z := effRep_nonneg T M s Z z
  calc phiEat T M s Z z * Real.log 2
      ≤ phiEofPartition T M s Z z (Partition.total hMne Z) * Real.log 2 :=
        mul_le_mul_of_nonneg_right h1 hl2.le
    _ ≤ (∏ j ∈ Z, (1 / 2 + |fK w s K j|)) *
          ((∑ j ∈ Z, (2 * |fK w s K j| + 3 * epsN N)) / Real.log 2) * Real.log 2 := by
        unfold phiEofPartition
        exact mul_le_mul_of_nonneg_right (mul_le_mul hE hpos (pos_nonneg _)
          (prod_nonneg fun j _ => by positivity)) hl2.le
    _ = (∏ j ∈ Z, (1 / 2 + |fK w s K j|)) * ∑ j ∈ Z, (2 * |fK w s K j| + 3 * epsN N) := by
        field_simp

end Upper

/-! ### E3'(ii) and the assembly -/

lemma M_nonempty (hC : EffC N) {K : Finset (Fin N)} (hK : K.card = dX N) : (univ \ K).Nonempty := by
  rw [nonempty_iff_ne_empty]; intro h
  have hc' : (univ \ K).card = N - dX N := by rw [card_univ_sdiff, Fintype.card_fin, hK]
  rw [h, card_empty] at hc'
  have := hC.hN
  have := dX_ge N
  omega

/-- The core of E3'(ii), deterministic. -/
theorem others_lt_core (hC : EffC N) {s : State N} {K : Finset (Fin N)} {k : Fin N} {w : Param N}
    (hz : flipP s w ∈ openCube N) (hc : CoinAt N s K k w)
    (hcol : ∀ j, |effDevA w s ∅ s j| ≤ epsN N) (Z : Finset (Fin N)) (z : State N) (hZk : Z ≠ {k}) :
    phiEat (tpmOf (flipP s w)) (univ \ K) s Z z * Real.log 2 < fK w s K k - epsN N := by
  have hF := effC_facts hC
  obtain ⟨hσf, hfx, hoth⟩ := core_bounds hF hc.core
  have hf := hc.posf
  have habs : |fK w s K k| = fK w s K k := abs_of_pos hf
  rw [habs] at hσf hfx
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hfε : 100 * epsN N ≤ fK w s K k := by linarith [hF.εσ]
  rcases Z.eq_empty_or_nonempty with h0 | hZ
  · subst h0
    have := phiEat_empty_purview (tpmOf (flipP s w)) (univ \ K) s z
    rw [this, zero_mul]
    linarith [hF.ε0]
  · have hax : ∀ j, |fK w s K j| ≤ x2C N := fun j => by
      by_cases hj : j = k
      · rw [hj, habs]; exact hfx.le
      · have := hoth j hj; rw [habs] at this; linarith [hF.κ0]
    have hB := phiEat_le_B hz (M_nonempty hC hc.card) hcol (by linarith [hF.εσ, hF.σ1])
      (fun j => (hax j).trans (by linarith [hF.x21])) Z hZ z
    refine lt_of_le_of_lt hB ?_
    refine others_real Z (fun j => |fK w s K j|) k N (fun j => abs_nonneg _) hax habs
      (fun j hj => by have := hoth j hj; rwa [habs] at this) hF.κx hF.ε0 hfε hF.x21 hF.x2N
      (by simpa using card_le_univ Z) hZ hZk

theorem eff_others_lt : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N),
    GoodW3 N s r0 x σ w → CountFreshX N s r0 w → ∀ K ∈ famX3 N s r0 x σ w, ∀ k ∈ K,
      CoreAt N s K k 0 w → 0 < fK w s K k → DleAt N s K k w →
        ∀ (Z : Finset (Fin N)) (z : State N), Z ≠ {k} →
          phiEatAt (tpmOf (flipP s w)) univ s (univ \ K) s Z z <
            phiEatAt (tpmOf (flipP s w)) univ s (univ \ K) s {k} (teW w s) := by
  filter_upwards [ev_effC, eff_subDev, eff_colDev] with N hC hsub hcol s r0 x σ w hg hfr K hK k hk
    hcore hf hD Z z hZk
  have hz := cnt_flipP_open hg hfr
  have hc : CoinAt N s K k w := ⟨famX3_card hK, hk, hcore, hf⟩
  have hF := effC_facts hC
  have hcol' : ∀ j, |effDevA w s ∅ s j| ≤ epsN N := fun j => hcol s r0 x σ w hg hfr s j
  rw [phiEatAt_univ, phiEatAt_univ,
    phi_single_val hC hz hc hD (fun A hA => hsub s r0 x σ w hg hfr A s k hA) (hcol' k) _ rfl]
  have hlt := others_lt_core hC hz hc hcol' Z z hZk
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- `Φ_1 ln 2 ≥ f - ε`
  obtain ⟨hσf, hfx, -⟩ := core_bounds hF hcore
  rw [abs_of_pos hf] at hσf hfx
  set f := fK w s K k
  set ab := effDevA w s ∅ s k
  have hab1 := (abs_le.1 (hcol' k)).1
  have hab2 := (abs_le.1 (hcol' k)).2
  have hεσ := hF.εσ
  have hσ1 := hF.σ1
  have hσ0 := hF.σ0
  have hc0 : 0 < 1 / 2 + ab := by linarith
  have hp : 0 < 1 / 2 + f := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hp hc0)
  rw [inv_div] at h1
  have e : (1 / 2 + f) * (1 - (1 / 2 + ab) / (1 / 2 + f)) = f - ab := by
    rw [mul_sub, mul_one, mul_div_cancel₀ _ hp.ne']; ring
  have hl : f - epsN N ≤ (1 / 2 + f) * Real.log ((1 / 2 + f) / (1 / 2 + ab)) := by
    have := mul_le_mul_of_nonneg_left h1 hp.le
    rw [e] at this; linarith
  have e2 : (1 / 2 + f) * Real.logb 2 ((1 / 2 + f) / (1 / 2 + ab)) * Real.log 2 =
      (1 / 2 + f) * Real.log ((1 / 2 + f) / (1 / 2 + ab)) := by
    rw [Real.logb]; field_simp
  have : phiEat (tpmOf (flipP s w)) (univ \ K) s Z z * Real.log 2 <
      (1 / 2 + f) * Real.logb 2 ((1 / 2 + f) / (1 / 2 + ab)) * Real.log 2 := by
    rw [e2]; linarith
  exact lt_of_mul_lt_mul_right this hl2.le

/-- `phiFloor N ≤ σ/2`, eventually. -/
lemma ev_phiFloor : ∀ᶠ N in atTop, phiFloor N ≤ sigC N / 2 := by
  filter_upwards [ev_poly_geom 2 (r := 1 / 2) (by norm_num) (by norm_num) 192 (ε := 1) one_pos,
    eventually_ge_atTop 1] with N hN hN1
  have hσ0 := sigC_pos N
  have hd : dX N ≤ N := dX_le_N hN1
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hfl : phiFloor N = 2 * (N : ℝ) / 2 ^ N := by
    unfold phiFloor; rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
  have h0 : 0 ≤ phiFloor N := by rw [hfl]; positivity
  have hk' : 192 * (N : ℝ) ^ 2 < 2 ^ N := by
    have := hN
    rwa [one_div_pow, mul_one_div, div_lt_one h2N] at this
  have h2d : (2 : ℝ) ^ dX N ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hd
  have key : 192 * (N : ℝ) ^ 2 * 2 ^ dX N ≤ 2 ^ N * 2 ^ N :=
    mul_le_mul hk'.le h2d (by positivity) h2N.le
  have e1 : (2 * (N : ℝ) / 2 ^ N) ^ 2 = 4 * (N : ℝ) ^ 2 / (2 ^ N * 2 ^ N) := by ring
  have e2 : (sigC N / 2) ^ 2 = 1 / (48 * 2 ^ dX N) := by
    rw [div_pow, sigC_sq, div_div]; congr 1; ring
  have hsq : phiFloor N ^ 2 ≤ (sigC N / 2) ^ 2 := by
    rw [hfl, e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [key]
  by_contra hc
  push Not at hc
  have : (sigC N / 2) ^ 2 < phiFloor N ^ 2 := by nlinarith
  linarith

/-- **WP3 main: E3'(iii) + the DistOK floor.** -/
theorem effDet_proved : EffDetStmt := by
  filter_upwards [ev_effC, eff_others_lt, eff_maxStates_single, eff_phi_single, eff_phi_single_ge,
    ev_phiFloor] with N hC hO hS hP hG hfl s r0 x σ w hg hfr K hK hY
  obtain ⟨k, hk, hcore, hf, hD⟩ := hY
  set T := tpmOf (flipP s w) with hT
  set M := univ \ K with hMdef
  set te := teW w s with hte
  have hcand : ({k}, te) ∈ effCandidatesAt T univ s M s := by
    rw [effCandidatesAt, mem_biUnion]
    exact ⟨{k}, mem_powerset.2 (subset_univ _),
      mem_image.2 ⟨te, (hS s r0 x σ w hg hfr K hK k hk hcore hf te).2 rfl, rfl⟩⟩
  obtain ⟨pe, hpe⟩ := maxEffPurviewsAt_nonempty T univ s M s
  have hpe' := mem_filter.1 hpe
  obtain ⟨Z, -, hz⟩ := mem_biUnion.1 hpe'.1
  obtain ⟨z, hzmem, hzeq⟩ := mem_image.1 hz
  have hmax := hpe'.2 ({k}, te) hcand
  rw [← hzeq] at hmax
  simp only at hmax
  have hZk : Z = {k} := by
    by_contra hne
    have h1 := hO s r0 x σ w hg hfr K hK k hk hcore hf hD Z z hne
    linarith
  subst hZk
  have hzk : z k = te k := (hS s r0 x σ w hg hfr K hK k hk hcore hf z).1 hzmem
  refine ⟨⟨pe, hpe, ?_⟩, ?_⟩
  · rw [← hzeq]
    intro p hp
    rw [mem_stated] at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    rw [mem_singleton] at h1
    refine ⟨mem_univ _, ?_⟩
    rw [h2, h1]; exact hzk
  · rw [← phiEatAt_of_mem_maxEffPurviewsAt T univ s M s hpe, ← hzeq]
    simp only
    have hv := hP s r0 x σ w hg hfr K hK k hk hcore hf hD te rfl
    have hge := hG s r0 x σ w hg hfr K hK k hk hcore hf
    have hF := effC_facts hC
    obtain ⟨hσf, -, -⟩ := core_bounds hF hcore
    rw [abs_of_pos hf] at hσf
    have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have hl20 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have h3 : sigC N / 2 ≤ fK w s K k / (2 * Real.log 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [hF.σ0]
    have hfl' := hfl
    linarith

end WP3

alias eff_others_lt := WP3.eff_others_lt
alias effDet_proved := WP3.effDet_proved

end Census
end IIT

#print axioms IIT.Census.eff_others_lt
#print axioms IIT.Census.effDet_proved
