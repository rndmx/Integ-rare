/-
Census, B1 small cuts (W12 §6): **the cause side** (`smallC` for `2 ≤ |K| < D`).

* `sc_incl` (deterministic): on the concentration event, with the floor `y ≥ 0.49` and the tilt, a small-cut failure
  `kM(K) ≤ T` at `tc` lies in `scE tc K m_i m'_i T B` for the cell `i` of `y_min` (`m'_i = m_i + 0.012` absorbs
  the concentration error, `δ ≤ 1/2500`).
* **`scBadC_rare`**: the failure event has probability `≤ e^{-1.1 N}` (per unit `2 (3/2)^{μ/2} R ≤ 0.95/3`,
  union over the centre row, the `≤ (N+1)^D` cuts and the 51 cells).
-/
import IIT.Census.B1SmallCutChern

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

variable {N : ℕ}

/-- `cmean` over the complement of `K` is the subcube mean of the column. -/
lemma cmean_eq_scX (w : Param N) (K : Finset (Fin N)) (tc : State N) (j : Fin N) :
    cmean w (univ \ K) tc j = scX tc K (fun r => w r j) := by
  unfold cmean scX
  congr 1
  rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
  have := card_le_univ K; rw [Fintype.card_fin] at this
  rw [show N - (N - K.card) = K.card by omega]

/-- **The deterministic inclusion.** -/
theorem sc_incl {s : State N} {w : Param N} (ho : w ∈ openCube N) (hcC : concCAt N w (tcRow w))
    (hDN : DU N ≤ N - 1) (hδ : dU N (N - 1) ≤ 1 / 2500) (hfl : ∀ j, 49 / 100 ≤ clamp01 (w (tcRow w) j))
    (hN : 1 ≤ N) {K : Finset (Fin N)} {T : ℝ}
    (hkM : kM (lamCz (flipP s w) s (tcRow w)) (lcMin s w) K ≤ T) {B : ℝ} (hX : XW w (tcRow w) ≤ B) :
    ∃ i < 51, w ∈ scE (tcRow w) K (scM i) (scMp i) T B := by
  classical
  have hz : flipP s w ∈ openCube N := flipP_mem_openCube ho
  obtain ⟨mc1, -, mc3, mc4, -⟩ := lamCz_means hz s (tcRow w)
  rw [flipP_invol s w] at mc1 mc3 mc4
  set tc := tcRow w with htc
  set y : Fin N → ℝ := fun j => clamp01 (w tc j) with hy
  set A : Fin N → ℝ := fun j => cmean w (univ \ univ.erase j) tc j with hA
  have hFy : ∀ j, kF (lamCz (flipP s w) s tc) j = Real.logb 2 (y j / A j) := fun j => mc1 j (univ.erase j)
  have hcard : ∀ j : Fin N, (univ.erase j).card = N - 1 := fun j => by
    rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
  have hAc : ∀ j, |A j - 1 / 2| ≤ dU N (N - 1) := fun j => by
    have := hcC j (univ.erase j) (notMem_erase j univ) (by rw [hcard j]; exact hDN)
    rwa [hcard j] at this
  have hAl : ∀ j, 1 / 2 - 1 / 2500 ≤ A j := fun j => by have := (abs_le.1 (hAc j)).1; linarith
  have hAu : ∀ j, A j ≤ 1 / 2 + 1 / 2500 := fun j => by have := (abs_le.1 (hAc j)).2; linarith
  have hA0 : ∀ j, 0 < A j := fun j => by have := hAl j; linarith
  have hy0 : ∀ j, 0 < y j := mc3
  have hy1 : ∀ j, y j < 1 := fun j => by
    show clamp01 (w tc j) < 1
    rw [b1_clamp01_of_mem_Ioo (ho tc j)]; exact (ho tc j).2
  -- the minimal entry and its cell
  have hne : (univ : Finset (Fin N)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  obtain ⟨jm, -, hjm⟩ := exists_min_image univ y hne
  set ym := y jm with hym
  set i := ⌊(ym - 49 / 100) * 100⌋₊ with hi
  have hym0 : 49 / 100 ≤ ym := hfl jm
  have hym1 := hy1 jm
  have hx0 : 0 ≤ (ym - 49 / 100) * 100 := by nlinarith
  have hfl1 : (i : ℝ) ≤ (ym - 49 / 100) * 100 := Nat.floor_le hx0
  have hfl2 : (ym - 49 / 100) * 100 < i + 1 := Nat.lt_floor_add_one _
  have hi51 : i < 51 := by
    have : (i : ℝ) < 51 := by linarith
    exact_mod_cast this
  have hsc : ((scM i : ℚ) : ℝ) = 49 / 100 + i / 100 := by unfold scM; push_cast; ring
  have hscp : ((scMp i : ℚ) : ℝ) = 49 / 100 + i / 100 + 12 / 1000 := by unfold scMp scM; push_cast; ring
  have hlo : ((scM i : ℚ) : ℝ) ≤ ym := by rw [hsc]; linarith
  have hhi : ym + 2 / 1000 ≤ ((scMp i : ℚ) : ℝ) := by rw [hscp]; linarith
  refine ⟨i, hi51, fun j => hlo.trans (hjm j (mem_univ j)), hX, ?_⟩
  -- the small-cut terms
  have hbdd : BddBelow (Set.range (kF (lamCz (flipP s w) s tc))) := (Set.finite_range _).bddBelow
  have hlc : lcMin s w ≤ kF (lamCz (flipP s w) s tc) jm := ciInf_le hbdd jm
  refine le_trans (sum_le_sum fun j _ => ?_) hkM
  unfold scV
  have hl : Real.logb 2 (clamp01 (w tc j) / scX tc K (fun r => w r j)) = lamCz (flipP s w) s tc j K := by
    rw [mc1 j K, cmean_eq_scX]
  rw [hl]
  refine min_le_min le_rfl ?_
  -- `log₂(y_j / m') ≤ F_j - λ_min`
  have hmp0 : (0 : ℝ) < ((scMp i : ℚ) : ℝ) := by linarith
  have key : Real.logb 2 (y j / ((scMp i : ℚ) : ℝ)) ≤
      kF (lamCz (flipP s w) s tc) j - kF (lamCz (flipP s w) s tc) jm := by
    rw [hFy, hFy, ← Real.logb_div (div_pos (hy0 j) (hA0 j)).ne' (div_pos (hy0 jm) (hA0 jm)).ne']
    refine Real.logb_le_logb_of_le (by norm_num) (div_pos (hy0 j) hmp0) ?_
    rw [div_div_div_eq, div_le_div_iff₀ hmp0 (mul_pos (hA0 j) (hy0 jm))]
    have hymle : ym ≤ 1 := hym1.le
    have hym0' : 0 ≤ ym := by linarith
    have k1 := mul_le_mul_of_nonneg_left hhi (hA0 jm).le
    have k2 : (1 / 2 - 1 / 2500) * (ym + 2 / 1000) ≤ A jm * (ym + 2 / 1000) :=
      mul_le_mul_of_nonneg_right (hAl jm) (by linarith)
    have k3 : A j * ym ≤ (1 / 2 + 1 / 2500) * ym := mul_le_mul_of_nonneg_right (hAu j) hym0'
    have h1 : A j * ym ≤ A jm * ((scMp i : ℚ) : ℝ) := by nlinarith
    have := mul_le_mul_of_nonneg_left h1 (hy0 j).le
    nlinarith
  linarith

/-! ### Numerics -/

lemma sc_logsq (c : ℝ) : ∀ᶠ N : ℕ in atTop, c * (Real.log ((N : ℝ) + 1) + c) ^ 2 ≤ (N : ℝ) / 100 := by
  have hx : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have t2 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hx
  have t1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hx
  have t0 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hx
  have ht : Tendsto (fun N : ℕ => |c| * ((Real.log ((N : ℝ) + 1)) ^ 2 / ((N : ℝ) + 1) +
      2 * |c| * (Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1)) + c ^ 2 * (1 / ((N : ℝ) + 1)))) atTop (𝓝 0) := by
    have := ((t2.add ((t1.const_mul (2 * |c|)))).add (t0.const_mul (c ^ 2))).const_mul |c|
    simp only [mul_zero, add_zero] at this
    refine this.congr fun N => ?_
    simp only [Function.comp, one_mul, add_zero, pow_one]
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 200 by norm_num)), eventually_ge_atTop 1]
    with N h hN
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  have e : |c| * ((Real.log ((N : ℝ) + 1)) ^ 2 / ((N : ℝ) + 1) +
      2 * |c| * (Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1)) + c ^ 2 * (1 / ((N : ℝ) + 1))) =
      |c| * ((Real.log ((N : ℝ) + 1)) ^ 2 + 2 * |c| * Real.log ((N : ℝ) + 1) + c ^ 2) / ((N : ℝ) + 1) := by
    field_simp
  rw [e, div_lt_iff₀ hN1] at h
  have hc : c * (Real.log ((N : ℝ) + 1) + c) ^ 2 ≤
      |c| * ((Real.log ((N : ℝ) + 1)) ^ 2 + 2 * |c| * Real.log ((N : ℝ) + 1) + c ^ 2) := by
    have h1 : c ≤ |c| := le_abs_self c
    have h2 : (Real.log ((N : ℝ) + 1) + c) ^ 2 ≤ (Real.log ((N : ℝ) + 1)) ^ 2 + 2 * |c| * Real.log ((N : ℝ) + 1) + c ^ 2 := by
      have := le_abs_self c; nlinarith [abs_nonneg c, sq_abs c]
    have h3 : 0 ≤ (Real.log ((N : ℝ) + 1) + c) ^ 2 := sq_nonneg _
    nlinarith [abs_nonneg c]
  linarith

/-- The subexponential factor of the union. -/
lemma sc_rate_num : ∀ᶠ N : ℕ in atTop, Real.log 51 + Real.log (DU N) + (DU N : ℝ) * Real.log ((N : ℝ) + 1) +
    (DU N : ℝ) * (82 * Real.log 2) + 8 * slT N ≤ (N : ℝ) / 25 := by
  filter_upwards [sc_logsq 60, eventually_ge_atTop 2] with N h hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set L := Real.log ((N : ℝ) + 1) with hLdef
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hlogN : Real.log N ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hD := DU_le_log N
  have hD0 : (1 : ℝ) ≤ DU N := by have : 1 ≤ DU N := by unfold DU; omega
                                  exact_mod_cast this
  have hlD : Real.log (DU N) ≤ DU N := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hl51 : Real.log 51 ≤ 50 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have hl2 : Real.log 2 < 7 / 10 := by have := Real.log_two_lt_d9; linarith
  have hDL : (DU N : ℝ) ≤ 6 * L + 20 := by linarith
  unfold slT
  have k1 : (DU N : ℝ) * L ≤ (6 * L + 20) * L := mul_le_mul_of_nonneg_right hDL hL
  have k2 : (DU N : ℝ) * (82 * Real.log 2) ≤ (6 * L + 20) * 58 := by
    have : 82 * Real.log 2 ≤ 58 := by linarith
    nlinarith
  nlinarith

/-! ### The cause-side small-cut failure -/

/-- The cause-side small-cut failure (`2 ≤ |K| < D`) on the concentration, floor and tilt events. -/
def scBadCEv (N : ℕ) (s : State N) : Set (Param N) :=
  {w | w ∈ openCube N ∧ concCAt N w (tcRow w) ∧ (∀ j, 49 / 100 ≤ clamp01 (w (tcRow w) j)) ∧
    XW w (tcRow w) ≤ x0 * N + slT N ∧ ∃ K : Finset (Fin N), 2 ≤ K.card ∧ K.card < DU N ∧
      kM (lamCz (flipP s w) s (tcRow w)) (lcMin s w) K ≤ 7 * DU N}

/-- The number of small cuts. -/
lemma sc_cuts_card (D : ℕ) :
    ((univ : Finset (Finset (Fin N))).filter fun K => 2 ≤ K.card ∧ K.card < D).card ≤ D * (N + 1) ^ D := by
  classical
  have hsub : ((univ : Finset (Finset (Fin N))).filter fun K => 2 ≤ K.card ∧ K.card < D) ⊆
      (range D).biUnion fun k => powersetCard k (univ : Finset (Fin N)) := by
    intro K hK
    obtain ⟨-, -, h⟩ := mem_filter.1 hK
    exact mem_biUnion.2 ⟨K.card, mem_range.2 h, mem_powersetCard.2 ⟨subset_univ _, rfl⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ k ∈ range D, (powersetCard k (univ : Finset (Fin N))).card
      ≤ ∑ _k ∈ range D, (N + 1) ^ D := sum_le_sum fun k hk => by
        rw [card_powersetCard, card_univ, Fintype.card_fin]
        exact (Nat.choose_le_pow N k).trans ((Nat.pow_le_pow_left (Nat.le_succ N) k).trans
          (Nat.pow_le_pow_right (Nat.succ_pos N) (mem_range.1 hk).le))
    _ = D * (N + 1) ^ D := by rw [sum_const, card_range, smul_eq_mul]

/-- `e^{μ x₀ N} = ((3/2)^{μ/2})^N` for even `μ`. -/
lemma sc_exp_tilt {μ : ℕ} (hμe : μ % 2 = 0) (N : ℕ) :
    Real.exp ((μ : ℝ) * (x0 * N)) = ((3 / 2 : ℝ) ^ (μ / 2)) ^ N := by
  unfold x0
  have hμ : (μ : ℝ) = 2 * ((μ / 2 : ℕ) : ℝ) := by
    have := Nat.div_add_mod μ 2; rw [hμe] at this; exact_mod_cast (by omega : μ = 2 * (μ / 2))
  rw [hμ, show 2 * ((μ / 2 : ℕ) : ℝ) * (Real.log (3 / 2) / 2 * N) = ((N * (μ / 2) : ℕ) : ℝ) * Real.log (3 / 2) by
    push_cast; ring, Real.exp_nat_mul, Real.exp_log (by norm_num), ← pow_mul, mul_comm N]

/-- **One term of the union.** -/
theorem sc_term_bound (hN : 1 ≤ N) (r0 : State N) {K : Finset (Fin N)} (hK2 : 2 ≤ K.card) (hKD : K.card ≤ DU N)
    {i : ℕ} (hi : i < 51) :
    cubeM N (scE r0 K ((scM i : ℚ) : ℝ) ((scMp i : ℚ) : ℝ) (7 * DU N) (x0 * N + slT N)) ≤
      ENNReal.ofReal (Real.exp ((77 * Real.log 2) * DU N + 8 * slT N) * (32 : ℝ) ^ DU N * (95 / 600) ^ N) := by
  classical
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hslT : 0 ≤ slT N := by
    unfold slT; have := Real.log_nonneg hNr; linarith
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < K.card)
  have habK : ({a, b} : Finset (Fin N)) ⊆ K := by
    intro x hx; rcases mem_insert.1 hx with rfl | hx; exact ha; rw [mem_singleton.1 hx]; exact hb
  obtain ⟨n, μ, R, hR0, hR1, hRc, hμe, hn11, hμ8, hRint⟩ := sc_cell_bound i hi
  have hm0 : (0 : ℝ) < ((scM i : ℚ) : ℝ) := by unfold scM; push_cast; positivity
  have hmp0 : (0 : ℝ) < ((scMp i : ℚ) : ℝ) := by unfold scMp scM; push_cast; positivity
  refine (sc_chernoff r0 K habK hab hm0 hmp0 n μ hR0 hRint _ _).trans (ENNReal.ofReal_le_ofReal ?_)
  set q : ℝ := (3 / 2 : ℝ) ^ (μ / 2) with hq
  have hq1 : 1 ≤ q := one_le_pow₀ (by norm_num)
  have hq8 : q ≤ 81 / 16 := by
    calc q ≤ (3 / 2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 81 / 16 := by norm_num
  have hexpB : Real.exp ((μ : ℝ) * (x0 * N + slT N)) = q ^ N * Real.exp (μ * slT N) := by
    rw [mul_add, Real.exp_add, sc_exp_tilt hμe N]
  have hqR : q * R ≤ 95 / 600 := by
    have : 6 * (q * R) ≤ 95 / 100 := by rw [← mul_assoc]; exact hRc
    linarith
  set k := K.card with hk
  have hkN : k ≤ N := by have := card_le_univ K; rwa [Fintype.card_fin] at this
  have hqRpow : q ^ N * R ^ (N - k) ≤ (81 / 16 : ℝ) ^ DU N * (600 / 95 : ℝ) ^ DU N * (95 / 600) ^ N := by
    have e1 : q ^ N * R ^ (N - k) = q ^ k * (q * R) ^ (N - k) := by
      rw [mul_pow, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hkN]
    rw [e1]
    have h1 : q ^ k ≤ (81 / 16 : ℝ) ^ DU N :=
      (pow_le_pow_left₀ (by linarith) hq8 k).trans (pow_le_pow_right₀ (by norm_num) hKD)
    have h2 : (q * R) ^ (N - k) ≤ (95 / 600 : ℝ) ^ (N - k) :=
      pow_le_pow_left₀ (mul_nonneg (by linarith) hR0) hqR _
    have h3 : (95 / 600 : ℝ) ^ (N - k) ≤ (600 / 95 : ℝ) ^ DU N * (95 / 600) ^ N := by
      have e2 : (95 / 600 : ℝ) ^ N = (95 / 600) ^ (N - k) * (95 / 600) ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hkN]
      have h4 : 1 ≤ (600 / 95 : ℝ) ^ DU N * (95 / 600) ^ k := by
        have e3 : (600 / 95 : ℝ) ^ k * (95 / 600) ^ k = 1 := by rw [← mul_pow]; norm_num
        have h5 : (600 / 95 : ℝ) ^ k ≤ (600 / 95 : ℝ) ^ DU N := pow_le_pow_right₀ (by norm_num) hKD
        have h6 : (0 : ℝ) < (95 / 600) ^ k := by positivity
        nlinarith
      rw [e2]
      have h7 : (0 : ℝ) < (95 / 600) ^ (N - k) := by positivity
      nlinarith
    calc q ^ k * (q * R) ^ (N - k) ≤ (81 / 16 : ℝ) ^ DU N * ((600 / 95 : ℝ) ^ DU N * (95 / 600) ^ N) :=
          mul_le_mul h1 (h2.trans h3) (by positivity) (by positivity)
      _ = _ := by ring
  have hexpT : Real.exp ((n : ℝ) * Real.log 2 * (7 * DU N)) ≤ Real.exp ((77 * Real.log 2) * DU N) := by
    refine Real.exp_le_exp.2 ?_
    have hn : (n : ℝ) ≤ 11 := by exact_mod_cast hn11
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hD : (0 : ℝ) ≤ DU N := Nat.cast_nonneg _
    have e1 : (n : ℝ) * Real.log 2 * (7 * DU N) = (7 * n) * (Real.log 2 * DU N) := by ring
    have e2 : (77 * Real.log 2) * DU N = 77 * (Real.log 2 * DU N) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hl2.le hD)
  have hexpS : Real.exp (μ * slT N) ≤ Real.exp (8 * slT N) := by
    refine Real.exp_le_exp.2 ?_
    have : (μ : ℝ) ≤ 8 := by exact_mod_cast hμ8
    nlinarith
  have h32 : (81 / 16 : ℝ) ^ DU N * (600 / 95 : ℝ) ^ DU N ≤ 32 ^ DU N := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  rw [Real.exp_add, hexpB]
  calc Real.exp ((n : ℝ) * Real.log 2 * (7 * DU N)) * (q ^ N * Real.exp (μ * slT N)) * R ^ (N - k)
      = Real.exp ((n : ℝ) * Real.log 2 * (7 * DU N)) * Real.exp (μ * slT N) * (q ^ N * R ^ (N - k)) := by ring
    _ ≤ Real.exp ((77 * Real.log 2) * DU N) * Real.exp (8 * slT N) *
        ((81 / 16 : ℝ) ^ DU N * (600 / 95 : ℝ) ^ DU N * (95 / 600) ^ N) :=
        mul_le_mul (mul_le_mul hexpT hexpS (Real.exp_pos _).le (Real.exp_pos _).le) hqRpow
          (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg hR0 _)) (by positivity)
    _ ≤ Real.exp ((77 * Real.log 2) * DU N) * Real.exp (8 * slT N) * (32 ^ DU N * (95 / 600) ^ N) := by
        gcongr
    _ = Real.exp ((77 * Real.log 2) * DU N + 8 * slT N) * (32 : ℝ) ^ DU N * (95 / 600) ^ N := by
        rw [Real.exp_add]; ring

/-- `2 · 95/600 ≤ e^{-1.14}`. -/
lemma sc_base_num : (2 : ℝ) * (95 / 600) ≤ Real.exp (-(114 / 100)) := by
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (14 / 100) ≤ 1 + 14 / 100 + (14 / 100) ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (show |(14 / 100 : ℝ)| ≤ 1 by norm_num)
    have := (abs_le.1 this).2
    linarith
  have e : Real.exp (114 / 100) = Real.exp 1 * Real.exp (14 / 100) := by rw [← Real.exp_add]; norm_num
  rw [e]
  calc Real.exp 1 * Real.exp (14 / 100) ≤ 2.7182818286 * (1 + 14 / 100 + (14 / 100) ^ 2) :=
        mul_le_mul h1.le h2 (Real.exp_pos _).le (by norm_num)
    _ ≤ (2 * (95 / 600))⁻¹ := by norm_num

/-- The final numerics of the union. -/
lemma sc_union_num : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ N * ((DU N * ((N : ℝ) + 1) ^ DU N) * (51 *
    (Real.exp ((77 * Real.log 2) * DU N + 8 * slT N) * (32 : ℝ) ^ DU N * (95 / 600) ^ N))) ≤
    Real.exp (-(11 / 10 * (N : ℝ))) := by
  filter_upwards [sc_rate_num, eventually_ge_atTop 1] with N hnum hN
  have hD0 : (0 : ℝ) < DU N := by
    have : 1 ≤ DU N := by unfold DU; omega
    exact_mod_cast this
  have h95 : (2 : ℝ) ^ N * (95 / 600) ^ N ≤ Real.exp (-(114 / 100 * (N : ℝ))) := by
    rw [← mul_pow]
    calc ((2 : ℝ) * (95 / 600)) ^ N ≤ Real.exp (-(114 / 100)) ^ N := pow_le_pow_left₀ (by norm_num) sc_base_num N
      _ = Real.exp (-(114 / 100 * (N : ℝ))) := by rw [← Real.exp_nat_mul]; ring_nf
  have hfac : (51 : ℝ) * (DU N * ((N : ℝ) + 1) ^ DU N) * (Real.exp ((77 * Real.log 2) * DU N + 8 * slT N) *
      (32 : ℝ) ^ DU N) ≤ Real.exp ((N : ℝ) / 25) := by
    have e3 : Real.exp ((DU N : ℝ) * Real.log ((N : ℝ) + 1)) = ((N : ℝ) + 1) ^ DU N := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    have e4 : Real.exp ((DU N : ℝ) * (5 * Real.log 2)) = (32 : ℝ) ^ DU N := by
      rw [show (DU N : ℝ) * (5 * Real.log 2) = ((5 * DU N : ℕ) : ℝ) * Real.log 2 by push_cast; ring,
        Real.exp_nat_mul, Real.exp_log (by norm_num), pow_mul]; norm_num
    have hrepr : (51 : ℝ) * (DU N * ((N : ℝ) + 1) ^ DU N) * (Real.exp ((77 * Real.log 2) * DU N + 8 * slT N) *
        (32 : ℝ) ^ DU N) = Real.exp (Real.log 51 + Real.log (DU N) + (DU N : ℝ) * Real.log ((N : ℝ) + 1) +
          ((77 * Real.log 2) * DU N + 8 * slT N) + (DU N : ℝ) * (5 * Real.log 2)) := by
      simp only [Real.exp_add, Real.exp_log (show (0 : ℝ) < 51 by norm_num), Real.exp_log hD0, e3, e4]
      ring
    rw [hrepr]
    refine Real.exp_le_exp.2 ?_
    have e5 : (77 * Real.log 2) * DU N + (DU N : ℝ) * (5 * Real.log 2) = (DU N : ℝ) * (82 * Real.log 2) := by ring
    linarith
  calc (2 : ℝ) ^ N * ((DU N * ((N : ℝ) + 1) ^ DU N) * (51 *
        (Real.exp ((77 * Real.log 2) * DU N + 8 * slT N) * (32 : ℝ) ^ DU N * (95 / 600) ^ N)))
      = (51 : ℝ) * (DU N * ((N : ℝ) + 1) ^ DU N) *
          (Real.exp ((77 * Real.log 2) * DU N + 8 * slT N) * (32 : ℝ) ^ DU N) *
          ((2 : ℝ) ^ N * (95 / 600) ^ N) := by ring
    _ ≤ Real.exp ((N : ℝ) / 25) * Real.exp (-(114 / 100 * (N : ℝ))) :=
        mul_le_mul hfac h95 (by positivity) (Real.exp_pos _).le
    _ = Real.exp (-(11 / 10 * (N : ℝ))) := by rw [← Real.exp_add]; ring_nf

/-- **The cause-side small-cut failure is rare** (rate `1.1`). -/
theorem scBadC_rare : ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (scBadCEv N s) ≤ ENNReal.ofReal (Real.exp (-(11 / 10 * (N : ℝ)))) := by
  filter_upwards [eventually_ge_atTop 64, ev_N_dU_top, sc_union_num] with N hN64 htop hnum s
  classical
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hDN : DU N ≤ N - 1 := DU_le hN64
  have hδ : dU N (N - 1) ≤ 1 / 2500 := by
    have : dU N (N - 1) ≤ N * dU N (N - 1) := le_mul_of_one_le_left (dU_nonneg N _) (by linarith)
    linarith
  set S := (univ : Finset (Finset (Fin N))).filter fun K => 2 ≤ K.card ∧ K.card < DU N with hS
  set q0 : ℝ := Real.exp ((77 * Real.log 2) * DU N + 8 * slT N) * (32 : ℝ) ^ DU N * (95 / 600) ^ N with hq0
  have hsub : scBadCEv N s ⊆ ⋃ r0 : State N, ⋃ K ∈ S, ⋃ i ∈ range 51,
      scE r0 K ((scM i : ℚ) : ℝ) ((scMp i : ℚ) : ℝ) (7 * DU N) (x0 * N + slT N) := by
    rintro w ⟨ho, hcC, hfl, hX, K, hK2, hKD, hkM⟩
    obtain ⟨i, hi, hw⟩ := sc_incl ho hcC hDN hδ hfl (by omega) hkM hX
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨tcRow w, K, mem_filter.2 ⟨mem_univ _, hK2, hKD⟩, i, mem_range.2 hi, hw⟩
  have hq00 : 0 ≤ q0 := by positivity
  have hrow : ∀ r0 : State N, cubeM N (⋃ K ∈ S, ⋃ i ∈ range 51,
      scE r0 K ((scM i : ℚ) : ℝ) ((scMp i : ℚ) : ℝ) (7 * DU N) (x0 * N + slT N)) ≤
        ENNReal.ofReal ((S.card : ℝ) * (51 * q0)) := by
    intro r0
    refine (measure_biUnion_finset_le _ _).trans ?_
    have hK : ∀ K ∈ S, cubeM N (⋃ i ∈ range 51,
        scE r0 K ((scM i : ℚ) : ℝ) ((scMp i : ℚ) : ℝ) (7 * DU N) (x0 * N + slT N)) ≤ ENNReal.ofReal (51 * q0) := by
      intro K hK
      obtain ⟨-, hK2, hKD⟩ := mem_filter.1 hK
      refine (measure_biUnion_finset_le _ _).trans ?_
      refine (Finset.sum_le_sum fun i hi => sc_term_bound (by omega) r0 hK2 hKD.le (mem_range.1 hi)).trans
        (le_of_eq ?_)
      rw [sum_const, card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num), hq0]
      push_cast; ring_nf
    refine (Finset.sum_le_sum hK).trans ?_
    rw [sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
  refine (Finset.sum_le_sum fun r0 _ => hrow r0).trans ?_
  rw [sum_const, card_univ, nsmul_eq_mul]
  have hcs : ((Fintype.card (State N) : ℕ) : ENNReal) = ENNReal.ofReal ((2 : ℝ) ^ N) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  rw [hcs, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hSc : (S.card : ℝ) ≤ DU N * ((N : ℝ) + 1) ^ DU N := by
    have := sc_cuts_card (N := N) (DU N)
    exact_mod_cast this
  refine le_trans ?_ hnum
  gcongr

end Census
end IIT
