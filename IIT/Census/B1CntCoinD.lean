/-
Census, B1, W14 work package WP5 (part 5): Lemma D' (W5 6.6, W9 5.5, W13-effect G1).

`dprime`: for `f ∈ GoodX3` and `K ∈ famX3`, `P(∃ k ∈ K, Core^{(k)}_K(0) ∧ ¬ D≤_K(k)) ≤ 1/N`.

Proof.  On `Core^{(k)}_K(0)`, a failing `(D_A)` (`A = M \ B`, `r = |B| ∈ [2, rD]`) forces, for one orientation
`b`, both `S_0 := ±(fresh sum of column k over C_0) ≥ a A0` and `T_A := ±(fresh sum of column k over
agree A s \ C_0) ≥ w5tr N r` (`w5_dle_alg`; the fixed rows are `≤ d²/2`, `≤ (d+r+1)²/2`).  The two sums read
disjoint entries (independence), and the sharp sub-Gaussian tail `exp(-6t²/n)` (`SubGaussStmt`, law by
`EntrySumLawStmt`) gives `P(S_0 ≥ a A0) ≤ e^{-ln N} = 1/N` and `P(T_A ≥ w5tr) ≤ N^{-(2^r-1)(1-2γ)}`; the
union over `k`, `r`, `B`, `b` is `≤ (1/N) · 2 d Σ_r C(m, r) N^{-(2^r-1)(1-2γ)} ≤ 1/N` (`w5_dnum`).

No `sorry`.
-/
import IIT.Census.B1CntCoinDNum

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### Tails of signed fresh sums -/

lemma w5_subG_le (hSG : SubGaussStmt) (n : ℕ) {t n' : ℝ} (ht : 0 < t) (hn : (n : ℝ) ≤ n')
    (hn' : 0 < n') :
    (Measure.pi fun _ : Fin n => unif) {u | ∑ l, (u l - 1 / 2) ∈ Set.Ici t} ≤
      ENNReal.ofReal (Real.exp (-(6 * t ^ 2 / n'))) := by
  by_cases hn0 : n = 0
  · subst hn0
    have : {u : Fin 0 → ℝ | ∑ l, (u l - 1 / 2) ∈ Set.Ici t} = ∅ := by
      ext u; simp only [univ_eq_empty, sum_empty, Set.mem_Ici, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false, not_le]; exact ht
    rw [this, measure_empty]; exact bot_le
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    refine (hSG n t ht.le).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    have : 6 * t ^ 2 / n' ≤ 6 * t ^ 2 / n :=
      div_le_div_of_nonneg_left (by positivity) hnpos hn
    linarith

lemma w5S_tail (hSG : SubGaussStmt) (hESL : EntrySumLawStmt) (F R : Finset (State N)) (k : Fin N)
    (b : Bool) {t n' : ℝ} (ht : 0 < t) (hn : (R.card : ℝ) ≤ n') (hn' : 0 < n') :
    cubeM N {w | t ≤ w5S F R k b w} ≤ ENNReal.ofReal (Real.exp (-(6 * t ^ 2 / n'))) := by
  have e : {w : Param N | t ≤ w5S F R k b w} = {w | w5S F R k b w ∈ Set.Ici t} := rfl
  rw [e, w5S_law hESL F R k b measurableSet_Ici]
  refine w5_subG_le hSG _ ht ?_ hn'
  rw [w5E_card]
  have : ((R.filter fun r => r ∉ F).card : ℝ) ≤ R.card := by exact_mod_cast card_filter_le _ _
  linarith

lemma measurableSet_w5S_ge (F R : Finset (State N)) (k : Fin N) (b : Bool) (t : ℝ) :
    MeasurableSet {w : Param N | t ≤ w5S F R k b w} :=
  measurableSet_le measurable_const (measurable_w5S F R k b)

/-! ### The deterministic step -/

/-- A failing `(D_A)` on `Core^{(k)}_K(0)`: both fresh sums are large, for one orientation. -/
lemma w5_dle_alg {a ρ m f E ψ T φ0 S0 A0 κN dd Q r : ℝ} (ha : 0 < a) (hρ : 0 < ρ)
    (hE : E * (a * ρ) = a * f + ψ + T) (hf0 : a * f = φ0 + S0) (hφ : |φ0| ≤ dd) (hψ : |ψ| ≤ Q)
    (hdd : dd ≤ 2 * a * κN) (hA0 : 0 ≤ A0) (hκN : 0 ≤ κN) (hc : 0 ≤ ρ * (1 - r / m) - 1)
    (hcore : A0 + 2 * κN < |f|) (hfail : |f| * (1 - r / m) - κN / 2 ≤ sgnMul f E) :
    (a * A0 ≤ S0 ∧ a * A0 * (ρ * (1 - r / m) - 1) - a * ρ * κN / 2 - Q ≤ T) ∨
      (a * A0 ≤ -S0 ∧ a * A0 * (ρ * (1 - r / m) - 1) - a * ρ * κN / 2 - Q ≤ -T) := by
  have hφ' := abs_le.1 hφ
  have hψ' := abs_le.1 hψ
  have haρ : 0 ≤ a * ρ := (mul_pos ha hρ).le
  rcases lt_or_ge 0 f with hpos | hneg
  · left
    rw [abs_of_pos hpos] at hcore hfail
    unfold sgnMul at hfail
    rw [if_pos hpos] at hfail
    have h1 : a * (A0 + 2 * κN) ≤ a * f := mul_le_mul_of_nonneg_left hcore.le ha.le
    have h2 := mul_le_mul_of_nonneg_right hfail haρ
    have h3 : a * A0 * (ρ * (1 - r / m) - 1) ≤ a * f * (ρ * (1 - r / m) - 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) ha.le) hc
    have e : (f * (1 - r / m) - κN / 2) * (a * ρ) - a * f =
        a * f * (ρ * (1 - r / m) - 1) - a * ρ * κN / 2 := by ring
    constructor <;> nlinarith
  · right
    have hf0' : f ≠ 0 := by
      rintro rfl; rw [abs_zero] at hcore; linarith
    have hneg' : f < 0 := lt_of_le_of_ne hneg hf0'
    rw [abs_of_neg hneg'] at hcore hfail
    unfold sgnMul at hfail
    rw [if_neg (not_lt.2 hneg)] at hfail
    have h1 : a * (A0 + 2 * κN) ≤ a * (-f) := mul_le_mul_of_nonneg_left hcore.le ha.le
    have h2 := mul_le_mul_of_nonneg_right hfail haρ
    have h3 : a * A0 * (ρ * (1 - r / m) - 1) ≤ a * (-f) * (ρ * (1 - r / m) - 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) ha.le) hc
    have e : (-f * (1 - r / m) - κN / 2) * (a * ρ) + a * f =
        a * (-f) * (ρ * (1 - r / m) - 1) - a * ρ * κN / 2 := by ring
    have e2 : -E * (a * ρ) = -(E * (a * ρ)) := by ring
    constructor <;> nlinarith

lemma w5_sum_agree (w : Param N) (s : State N) (A : Finset (Fin N)) (t : State N) (k : Fin N) :
    ∑ r ∈ agree A t, (pTe w s r k - 1 / 2) = effDevA w s A t k * 2 ^ (N - A.card) := by
  have hc : ((agree A t).card : ℝ) = 2 ^ (N - A.card) := by rw [card_agree]; push_cast; rfl
  unfold effDevA
  rw [hc, div_mul_cancel₀ _ (by positivity)]

/-- **The cover** of `Core^{(k)}_K(0) ∩ ¬D≤_K(k)`. -/
lemma w5_dle_cover {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ) (K : Finset (Fin N))
    (k : Fin N) (w : Param N) (hfar : N ≤ 3 * ham r0 s) (hKc : K.card = dX N) (hdN : dX N ≤ N)
    (hd2 : 2 ≤ dX N) (h319 : 3 * (dX N + rD N) + 19 ≤ N) (h4rD : 4 * (rD N : ℝ) ≤ mX N)
    (hcore : CoreAt N s K k 0 (w5G f w)) (hnot : ¬ DleAt N s K k (w5G f w)) :
    ∃ r ∈ Icc 2 (rD N), ∃ B ∈ (univ \ K).powersetCard r, ∃ b : Bool,
      2 ^ dX N * A0C N ≤ w5S (sensRows s r0) (agree (univ \ K) s) k b w ∧
      w5tr N r ≤ w5S (sensRows s r0) (agree ((univ \ K) \ B) s \ agree (univ \ K) s) k b w := by
  unfold DleAt at hnot
  push_neg at hnot
  obtain ⟨A, hAM, _hAne, h2, hrD, hfail⟩ := hnot
  set M := univ \ K with hMdef
  set B := M \ A with hBdef
  set r := B.card with hrdef
  have hAB : M \ B = A := Finset.sdiff_sdiff_eq_self hAM
  refine ⟨r, mem_Icc.2 ⟨h2, hrD⟩, B, mem_powersetCard.2 ⟨sdiff_subset, rfl⟩, ?_⟩
  rw [hAB]
  -- sizes
  have hMc : M.card = N - dX N := by rw [hMdef, card_univ_sdiff, Fintype.card_fin, hKc]
  have hdM : N - M.card = dX N := by rw [hMc]; omega
  have hBc : B.card = M.card - A.card := card_sdiff_of_subset hAM
  have hAle : A.card ≤ M.card := card_le_card hAM
  have hrle : r ≤ rD N := hrD
  have hdA : N - A.card = dX N + r := by rw [hrdef, hBc, hMc] at *; omega
  set d := dX N with hd
  set a : ℝ := 2 ^ d with ha_def
  have ha : 0 < a := by positivity
  set ρ : ℝ := 2 ^ r with hρ
  have hρ4 : 4 ≤ ρ := by
    rw [hρ]; calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) h2
  have hC0A : agree M s ⊆ agree A s := agree_subset_agree hAM s
  set D := agree A s \ agree M s with hDdef
  -- the decomposition of `effDevA` at `A`
  have hsplit : ∑ r' ∈ agree A s, (pTe (w5G f w) s r' k - 1 / 2) =
      (w5fix f D k + w5S (sensRows s r0) D k (w5or f k) w) + fK (w5G f w) s K k * a := by
    rw [← sum_sdiff hC0A, sum_pTe_w5G f D k w]
    congr 1
    unfold fK
    rw [w5_sum_agree, hdM]
  have hE : effDevA (w5G f w) s A s k * (a * ρ) =
      a * fK (w5G f w) s K k + w5fix f D k + w5S (sensRows s r0) D k (w5or f k) w := by
    rw [w5_sum_agree] at hsplit
    have : (2 : ℝ) ^ (N - A.card) = a * ρ := by rw [hdA, pow_add]
    rw [this] at hsplit
    linarith
  have hf0 : a * fK (w5G f w) s K k = w5fix f (agree M s) k + w5S (sensRows s r0) (agree M s) k (w5or f k) w := by
    rw [mul_comm]; exact w5_fK_w5G f K k w hdM
  -- the fixed parts
  have hφ : |w5fix f (agree M s) k| ≤ (d : ℝ) ^ 2 / 2 := by
    have h1 := abs_w5fix_le f (agree M s) k
    have h2 := w5_sens_card_le (r0 := r0) hfar M s (by simp [ham_self]) hdM hd2 (by omega)
    have h3 : (((agree M s).filter fun r => r ∈ sensRows s r0).card : ℝ) ≤ (d : ℝ) ^ 2 := by
      exact_mod_cast h2
    linarith
  have hψ : |w5fix f D k| ≤ ((dX N + r + 1 : ℕ) : ℝ) ^ 2 / 2 := by
    have h1 := abs_w5fix_le f D k
    have h2 : (D.filter fun r => r ∈ sensRows s r0) ⊆ (agree A s).filter fun r => r ∈ sensRows s r0 :=
      filter_subset_filter _ sdiff_subset
    have h3 := w5_sens_card_le' (r0 := r0) hfar A s (by simp [ham_self]) (by omega)
    rw [hdA] at h3
    have h4 : ((D.filter fun r => r ∈ sensRows s r0).card : ℝ) ≤ ((dX N + r + 1 : ℕ) : ℝ) ^ 2 := by
      have := (card_le_card h2).trans h3
      exact_mod_cast this
    linarith
  have hκN := w5_kapN_nonneg N
  have hdd : (d : ℝ) ^ 2 / 2 ≤ 2 * a * kapN N := by
    have : 4 * kap0 N ≤ kapN N := by
      unfold kapN
      have := Real.log_natCast_nonneg N
      have := w5_epsN_nonneg N
      have : 0 ≤ 6 * Real.log N / 2 ^ dX N := by positivity
      linarith
    have hk0 : a * kap0 N = (d : ℝ) ^ 2 := by unfold kap0; rw [← hd, ← ha_def]; field_simp
    nlinarith
  have hmpos : 0 < mX N := by
    have : (0 : ℝ) < rD N := by unfold rD; positivity
    linarith
  have hc : 0 ≤ ρ * (1 - r / mX N) - 1 := by
    have hr' : (r : ℝ) ≤ rD N := by exact_mod_cast hrle
    have : (r : ℝ) / mX N ≤ 1 / 4 := by rw [div_le_iff₀ hmpos]; linarith
    nlinarith
  have hcore' : A0C N + 2 * kapN N < |fK (w5G f w) s K k| := by
    have := hcore.1; linarith
  have hfail' : |fK (w5G f w) s K k| * (1 - (r : ℝ) / mX N) - kapN N / 2 ≤
      sgnMul (fK (w5G f w) s K k) (effDevA (w5G f w) s A s k) := by
    exact hfail
  have halg := w5_dle_alg ha (by positivity) hE hf0 hφ hψ hdd (w5_A0C_nonneg N) hκN hc hcore' hfail'
  have htr : w5tr N r = a * A0C N * (ρ * (1 - r / mX N) - 1) - a * ρ * kapN N / 2 -
      ((dX N + r + 1 : ℕ) : ℝ) ^ 2 / 2 := by unfold w5tr; rw [← hd, ← ha_def, ← hρ]
  rcases halg with ⟨hS, hT⟩ | ⟨hS, hT⟩
  · exact ⟨w5or f k, hS, by rw [htr]; exact hT⟩
  · refine ⟨!w5or f k, ?_, ?_⟩
    · rw [w5S_not]; exact hS
    · rw [w5S_not, htr]; exact hT

/-! ### Summation -/

lemma w5_sum4 {α β γ δ : Type*} (s1 : Finset α) (s2 : Finset β) (s3 : β → Finset γ)
    (s4 : Finset δ) (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) :
    ∑ _i ∈ s1, ∑ r ∈ s2, ∑ _B ∈ s3 r, ∑ _b ∈ s4, ENNReal.ofReal (g r) =
      ENNReal.ofReal (s1.card * ∑ r ∈ s2, ((s3 r).card * (s4.card * g r))) := by
  have h1 : ∀ r, ∑ _B ∈ s3 r, ∑ _b ∈ s4, ENNReal.ofReal (g r) =
      ENNReal.ofReal ((s3 r).card * (s4.card * g r)) := by
    intro r
    rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, ← ENNReal.ofReal_natCast (s3 r).card,
      ← ENNReal.ofReal_natCast s4.card, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
  simp_rw [h1]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => by have := hg r; positivity), sum_const,
    nsmul_eq_mul, ← ENNReal.ofReal_natCast s1.card, ← ENNReal.ofReal_mul (by positivity)]

/-! ### Lemma D' -/

theorem dprime (hSG : SubGaussStmt) (hESL : EntrySumLawStmt) :
    ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide), ∀ f ∈ GoodX3 N s r0 x σ,
      ∀ K ∈ famX3 N s r0 x σ (b1Ext f),
        rowsOutM (sensRows s r0) {g | ∃ k ∈ K, CoreAt N s K k 0 (glueRows (sensRows s r0) f g) ∧
            ¬ DleAt N s K k (glueRows (sensRows s r0) f g)} ≤ ENNReal.ofReal (1 / (N : ℝ)) := by
  filter_upwards [w5_dnum] with N hnum s r0 x σ f hf K hK
  obtain ⟨hA0, hL1, h4rD, h319, hd2, hdN, hγ0, hγ20, hthr, hsum⟩ := hnum
  have hfar : N ≤ 3 * ham r0 s := hf.1.far
  have hKc : K.card = dX N := famX3_card hK
  rw [rowsOut_eq_w5G f (fun w => ∃ k ∈ K, CoreAt N s K k 0 w ∧ ¬ DleAt N s K k w)]
  set M := univ \ K with hMdef
  set d := dX N with hd
  set a : ℝ := 2 ^ d with ha_def
  have ha : 0 < a := by positivity
  set L := Real.log N with hLdef
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set e : ℕ → ℝ := fun r => Real.exp (-(L * (2 ^ r - 1) * (1 - 2 * w5gam N))) with he
  set Z : Fin N → Bool → Set (Param N) :=
    fun k b => {w | a * A0C N ≤ w5S (sensRows s r0) (agree M s) k b w} with hZ
  set T : Fin N → ℕ → Finset (Fin N) → Bool → Set (Param N) :=
    fun k r B b => {w | w5tr N r ≤ w5S (sensRows s r0) (agree (M \ B) s \ agree M s) k b w} with hT
  have hcover : {w : Param N | ∃ k ∈ K, CoreAt N s K k 0 (w5G f w) ∧ ¬ DleAt N s K k (w5G f w)} ⊆
      ⋃ k ∈ K, ⋃ r ∈ Icc 2 (rD N), ⋃ B ∈ M.powersetCard r, ⋃ b ∈ (univ : Finset Bool),
        Z k b ∩ T k r B b := by
    rintro w ⟨k, hk, hc, hn⟩
    obtain ⟨r, hr, B, hB, b, h1, h2⟩ := w5_dle_cover f K k w hfar hKc hdN hd2 h319 h4rD hc hn
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨k, hk, r, hr, B, hB, b, mem_univ _, h1, h2⟩
  -- each piece
  have hpiece : ∀ k ∈ K, ∀ r ∈ Icc 2 (rD N), ∀ B ∈ M.powersetCard r, ∀ b ∈ (univ : Finset Bool),
      cubeM N (Z k b ∩ T k r B b) ≤ ENNReal.ofReal (1 / N * e r) := by
    intro k _ r hr B hB b _
    rw [mem_Icc] at hr
    have hBM : B ⊆ M := (mem_powersetCard.1 hB).1
    have hBc : B.card = r := (mem_powersetCard.1 hB).2
    have hdisj : Disjoint (agree M s) (agree (M \ B) s \ agree M s) := disjoint_sdiff
    rw [cubeM_inter_eq_mul_of_detOnE (w5E_disj_row (sensRows s r0) hdisj k k)
      (measurableSet_w5S_ge (sensRows s r0) _ k b _) (measurableSet_w5S_ge (sensRows s r0) _ k b _)
      (w5S_detOn (sensRows s r0) (agree M s) k b (Set.Ici _)) (w5S_detOn (sensRows s r0) _ k b (Set.Ici _))]
    have hMc : M.card = N - d := by rw [hMdef, card_univ_sdiff, Fintype.card_fin, hKc]
    have hdM : N - M.card = d := by rw [hMc]; omega
    -- the `C_0` factor
    have hZb : cubeM N (Z k b) ≤ ENNReal.ofReal (1 / N) := by
      have hc0 : ((agree M s).card : ℝ) ≤ a := by
        rw [card_agree, hdM]; push_cast; rfl
      have hpos : 0 < a * A0C N := mul_pos ha hA0
      refine (w5S_tail hSG hESL (sensRows s r0) (agree M s) k b hpos hc0 ha).trans (ENNReal.ofReal_le_ofReal ?_)
      have hsq := w5_A0C_sq N
      rw [← hd, ← ha_def] at hsq
      have : 6 * (a * A0C N) ^ 2 / a = L := by rw [hLdef, ← hsq]; field_simp
      rw [this, Real.exp_neg, Real.exp_log hN0, one_div]
    -- the `D` factor
    have hTb : cubeM N (T k r B b) ≤ ENNReal.ofReal (e r) := by
      obtain ⟨htpos, hthr'⟩ := hthr r hr.1 hr.2
      have hsub : agree M s ⊆ agree (M \ B) s := agree_subset_agree sdiff_subset s
      have hAc : (M \ B).card = M.card - r := by rw [card_sdiff_of_subset hBM, hBc]
      have hBle : r ≤ M.card := hBc ▸ card_le_card hBM
      have hrd : r ≤ rD N := hr.2
      have hNA : N - (M \ B).card = d + r := by rw [hAc, hMc]; omega
      have hDc : ((agree (M \ B) s \ agree M s).card : ℝ) ≤ a * (2 ^ r - 1) := by
        rw [card_sdiff_of_subset hsub, card_agree, card_agree, hNA, hdM, Nat.cast_sub
          (Nat.pow_le_pow_right (by norm_num) (by omega))]
        push_cast
        rw [pow_add]
        ring_nf
        rfl
      have hρ1 : 0 < (2 : ℝ) ^ r - 1 := by
        have : (2 : ℝ) ≤ 2 ^ r := by
          calc (2 : ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
      refine (w5S_tail hSG hESL (sensRows s r0) _ k b htpos hDc (by positivity)).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
      linarith [hthr']
    calc cubeM N (Z k b) * cubeM N (T k r B b)
        ≤ ENNReal.ofReal (1 / N) * ENNReal.ofReal (e r) := mul_le_mul' hZb hTb
      _ = ENNReal.ofReal (1 / N * e r) := (ENNReal.ofReal_mul (by positivity)).symm
  have he0 : ∀ r, 0 ≤ 1 / (N : ℝ) * e r := fun r => by rw [he]; positivity
  calc cubeM N {w : Param N | ∃ k ∈ K, CoreAt N s K k 0 (w5G f w) ∧ ¬ DleAt N s K k (w5G f w)}
      ≤ cubeM N (⋃ k ∈ K, ⋃ r ∈ Icc 2 (rD N), ⋃ B ∈ M.powersetCard r, ⋃ b ∈ (univ : Finset Bool),
          Z k b ∩ T k r B b) := measure_mono hcover
    _ ≤ ∑ k ∈ K, ∑ r ∈ Icc 2 (rD N), ∑ B ∈ M.powersetCard r, ∑ b ∈ (univ : Finset Bool),
          cubeM N (Z k b ∩ T k r B b) := by
        refine (measure_biUnion_finset_le _ _).trans (sum_le_sum fun k _ => ?_)
        refine (measure_biUnion_finset_le _ _).trans (sum_le_sum fun r _ => ?_)
        refine (measure_biUnion_finset_le _ _).trans (sum_le_sum fun B _ => ?_)
        exact measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ K, ∑ r ∈ Icc 2 (rD N), ∑ _B ∈ M.powersetCard r, ∑ _b ∈ (univ : Finset Bool),
          ENNReal.ofReal (1 / N * e r) :=
        sum_le_sum fun k hk => sum_le_sum fun r hr => sum_le_sum fun B hB => sum_le_sum fun b hb =>
          hpiece k hk r hr B hB b hb
    _ = ENNReal.ofReal (K.card * ∑ r ∈ Icc 2 (rD N),
          ((M.powersetCard r).card * ((univ : Finset Bool).card * (1 / N * e r)))) :=
        w5_sum4 K (Icc 2 (rD N)) (fun r => M.powersetCard r) univ (fun r => 1 / N * e r) he0
    _ ≤ ENNReal.ofReal (1 / (N : ℝ)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hMc : M.card = N - d := by rw [hMdef, card_univ_sdiff, Fintype.card_fin, hKc]
        simp only [card_powersetCard, hMc, card_univ, Fintype.card_bool, hKc]
        have : (d : ℝ) * ∑ r ∈ Icc 2 (rD N), (((N - d).choose r : ℕ) : ℝ) * ((2 : ℕ) * (1 / N * e r)) =
            1 / N * (2 * (d : ℝ) * ∑ r ∈ Icc 2 (rD N), ((N - d).choose r : ℝ) * e r) := by
          rw [mul_sum, mul_sum, mul_sum]
          refine sum_congr rfl fun r _ => ?_
          push_cast; ring
        rw [this]
        calc 1 / (N : ℝ) * (2 * (d : ℝ) * ∑ r ∈ Icc 2 (rD N), ((N - d).choose r : ℝ) * e r)
            ≤ 1 / N * 1 := mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = 1 / N := mul_one _

end Census
end IIT

#print axioms IIT.Census.dprime
