/-
B1 lower bound, leaf `phi_S_le_EX` (W7 §3 item 4), the candidate `S = U \ {x}`.
Its `r0`-pattern is the 2-row subcube `{r0, r0^x}`; its tilt is `∏_{i ≠ x} (y_i + U_i)/2
= ∏_{i≠x} y_i e^{-λ_i} ≤ 4 P(r0) e^{-N/400}` (check S), all other patterns are as in B5.
-/
import IIT.Census.B1SubB5

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace IIT
namespace Census

open MeasureTheory Filter Finset

noncomputable section

variable {N : ℕ}

/-- **`S = U \ {x}`, three fixed rows** (deterministic). -/
theorem thmCoX_det (hN : 1 ≤ N) (hbig : 20 ≤ K2N N) (h3D : 3 * D1 N + 3 ≤ N)
    (hη' : N * etaX N ≤ 1 / 10)
    (hratio : (1 + etaB N + 8 / (N : ℝ) ^ 3) ^ N ≤ 2 * (1 - etaX N) ^ N)
    (hhoeff : ∀ k, K2N N < k → k ≤ N → deltaH N (k - 1) + 3 / (2 : ℝ) ^ (k - 1) ≤ 1 / 4)
    (hrate : ∀ k, K2N N < k → k ≤ N → 8 * (k : ℝ) * rho0 ^ k ≤ Real.exp (-(N : ℝ) / 4))
    {s r0 : State N} {x : Fin N} (hham : N ≤ 3 * ham r0 s) {z : Param N} (hz : z ∈ openCube N)
    {w' : Param N} (hA : AgreeOff (rowsA s r0 x) (flipP s z) w') (hE : w' ∈ E5X N s r0 x)
    (hH : ∑ a ∈ rowsA s r0 x, Pw (flipP s z) a ≤ 2 / (N : ℝ) ^ 3)
    (hy : ∀ i, 1 / 2 ≤ clamp01 (flipP s z r0 i))
    (hlam : (N : ℝ) / 400 ≤ ∑ j, lamEX (flipP s z) r0 x j) :
    phi z s (univ.erase x) ≤
      max (Real.exp (-(N : ℝ) / 4)) (32 * N * Pw (flipP s z) r0 * Real.exp (-(N : ℝ) / 400)) := by
  classical
  set w := flipP s z with hw
  set S := univ.erase x with hSdef
  have hxS : x ∉ S := by simp [hSdef]
  have hmemS : ∀ j, j ∈ S ↔ j ≠ x := fun j => by simp [hSdef]
  have hS1 : S.card + 1 = N := by
    rw [hSdef, card_erase_of_mem (mem_univ x), card_univ, Fintype.card_fin]
    have : 1 ≤ N := hN; omega
  set k := S.card with hkdef
  set r1 := flipAt x r0 with hr1
  set A := rowsA s r0 x with hAdef
  have hkN : k ≤ N := card_le_N S
  have hk' : S.card < N := by omega
  have hk : K2N N < S.card := by
    rw [K2N_eq_sub_D1]; unfold D1 at h3D ⊢; omega
  have hdD : N - k < D1 N := sub_card_lt_D1 hk
  have hk20 : 20 ≤ k := by omega
  have hk10 : 10 ≤ k := by omega
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hg2, hEH⟩, hEW⟩, hECr⟩, hECh⟩, -⟩, hEFs⟩, -⟩, -⟩ := hE
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set H := ∑ a ∈ A, Pw w a with hHdef
  have hH0 : 0 ≤ H := sum_nonneg fun a _ => Pw_nonneg _ _
  have hAcard : A.card ≤ 3 := by
    simp only [hAdef, rowsA]
    exact (card_insert_le _ _).trans (Nat.succ_le_succ (card_insert_le _ _))
  /- (G) the three fixed rows never share a pattern on `S` -/
  have hfar : ∀ b : State N, (∀ j ∈ S, j ≠ x → b j = r0 j) → ¬ ∀ j ∈ S, b j = s j := by
    intro b hb h
    have hsub : (univ.filter fun j => r0 j ≠ s j) ⊆ insert x Sᶜ := by
      intro j hj
      rw [mem_insert, mem_compl]
      by_cases hjx : j = x
      · exact Or.inl hjx
      · right; intro hjS
        exact (mem_filter.1 hj).2 ((hb j hjS hjx).symm.trans (h j hjS))
    have hc := (card_le_card hsub).trans (card_insert_le _ _)
    rw [card_compl, Fintype.card_fin] at hc
    unfold ham at hham
    omega
  have hr1x : ∀ j ∈ S, j ≠ x → r1 j = r0 j := by
    intro j _ hjx; simp only [hr1, flipAt]; rw [Function.update_of_ne hjx]
  have hr1S : ∀ j ∈ S, r1 j = r0 j := fun j hj => hr1x j hj (fun h => hxS (h ▸ hj))
  have k1 : ¬ ∀ j ∈ S, r0 j = s j := hfar r0 (fun _ _ _ => rfl)
  have k2 : ¬ ∀ j ∈ S, r1 j = s j := hfar r1 hr1x
  set F : Finset (State N) := {r0, r1} with hFdef
  /- generic patterns see only the fresh rows -/
  have hgen : ∀ t, ¬ ((∀ j ∈ S, t j = r0 j) ∨ (∀ j ∈ S, t j = s j)) →
      ∀ i, colMean w S t i = colMean w' S t i := by
    intro t ht i
    refine tr4_eq hA (fun a ha hat => ht ?_) i
    rw [mem_agree] at hat
    simp only [hAdef, rowsA, mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact Or.inl fun j hj => (hat j hj).symm
    · exact Or.inl fun j hj => ((hat j hj).symm.trans (hr1S j hj))
    · exact Or.inr fun j hj => (hat j hj).symm
  /- (B5-b) the level `43/100` for every pattern -/
  have hheavys : ∀ t, (∀ j ∈ S, t j = s j) →
      ∑ i ∈ S, Real.log (max (2 * colMean w S t i) 1) ≤ 43 / 100 * k := by
    intro t hta
    have hGs : ∀ r ∈ (agree S s).erase s, r ∉ A := by
      intro r hr hrA
      have hra := mem_agree.1 (mem_of_mem_erase hr)
      simp only [hAdef, rowsA, mem_insert, mem_singleton] at hrA
      rcases hrA with rfl | rfl | rfl
      · exact k1 hra
      · exact k2 hra
      · exact ne_of_mem_erase hr rfl
    refine le_trans (sum_le_sum fun i _ => ?_) (hEFs S hk hk')
    rw [colMean_congr_agree w hta i]
    have h1 := colMean_le_colMeanPlus w S s i
    rw [colMeanPlus_congr hA hGs i] at h1
    apply Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _))
    exact max_le_max (by linarith) le_rfl
  have hlogsum : ∀ t, ¬ (∀ j ∈ S, t j = r0 j) →
      ∑ i ∈ S, Real.log (max (2 * colMean w S t i) 1) ≤ 43 / 100 * k := by
    intro t ht0
    by_cases hts : ∀ j ∈ S, t j = s j
    · exact hheavys t hts
    · have ht : ¬ ((∀ j ∈ S, t j = r0 j) ∨ (∀ j ∈ S, t j = s j)) := by tauto
      rw [sum_congr rfl fun i _ => by rw [hgen t ht i]]
      have := hECr S t hk hk'
      rw [← hkdef] at this
      linarith
  have hprodmax : ∀ t, ¬ (∀ j ∈ S, t j = r0 j) →
      ∏ i ∈ S, max (2 * colMean w S t i) 1 ≤ Real.exp (43 / 100 * k) := by
    intro t ht0
    have hpos : ∀ i ∈ S, 0 < max (2 * colMean w S t i) 1 :=
      fun i _ => lt_of_lt_of_le one_pos (le_max_right _ _)
    rw [← Real.exp_log (prod_pos hpos), Real.log_prod (fun i hi => (hpos i hi).ne')]
    exact Real.exp_le_exp.2 (hlogsum t ht0)
  /- (B5-a) block masses -/
  set η := etaB N with hη
  set η' := etaX N with hη'def
  have hη0 : 0 ≤ η := (Real.exp_pos _).le
  have hη'0 : 0 ≤ η' := etaX_nonneg N
  have hη'1 : η' ≤ 1 / 10 := by
    have : η' ≤ N * η' := le_mul_of_one_le_left hη'0 hN'
    linarith
  set u : ℝ := (1 / 2 : ℝ) ^ (N - k) with hu
  have hu0 : 0 < u := by positivity
  have h2du : (1 : ℝ) ≤ 2 ^ D1 N * u := by
    have e : (2 : ℝ) ^ D1 N = 2 ^ (N - k) * 2 ^ (D1 N - (N - k)) := by
      rw [← pow_add]; congr 1; omega
    rw [e, hu, mul_comm ((2 : ℝ) ^ (N - k)), mul_assoc, ← mul_pow]
    norm_num
    exact one_le_pow₀ (by norm_num)
  have hA3 : ∑ a ∈ A, Pw w' a ≤ 3 * tauN N := by
    calc ∑ a ∈ A, Pw w' a ≤ ∑ _a ∈ A, tauN N := sum_le_sum fun a _ => Pw_le_tauN_of_g2 hg2 a
      _ = A.card * tauN N := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 3 * tauN N := by
          have := tauN_pos N
          have : (A.card : ℝ) ≤ 3 := by exact_mod_cast hAcard
          nlinarith
  have hbo : ∀ r, (1 - η') * u ≤ blockPo A w' S r ∧ blockPo A w' S r ≤ (1 + η) * u := by
    intro r
    have h1 := blockP_sub_le_blockPo A w' S r
    have h2 := blockPo_le_blockP A w' S r
    have h3 := hEW S r hk hk'
    rw [← hkdef, ← hu, abs_le] at h3
    have hτ := tauN_pos N
    have h4 : 3 * tauN N ≤ 2 ^ (D1 N + 2) * tauN N * u := by
      rw [pow_add]; nlinarith
    constructor
    · simp only [hη'def, etaX]; nlinarith
    · linarith
  have hcm : ∀ t i, colMean w S t i = u * ∑ r ∈ agree S t, clamp01 (w r i) := by
    intro t i
    rw [colMean, ← hkdef, hu, one_div_pow]; ring
  have hNumUp : ∀ t i, Num w S S t i ≤ (1 + η) * colMean w S t i + H := by
    intro t i
    rw [Num_S_eq_blockPo hA S t i]
    have hA2 : ∑ a ∈ A, clamp01 (w (merge S t a) i) * Pw w a ≤ H :=
      sum_le_sum fun a _ => mul_le_of_le_one_left (Pw_nonneg w a) (clamp01_le_one _)
    have hA1 : ∑ r ∈ agree S t, clamp01 (w r i) * blockPo A w' S r ≤
        (1 + η) * colMean w S t i := by
      rw [hcm t i, ← mul_assoc, mul_comm ((1 + η) * u), sum_mul]
      refine sum_le_sum fun r _ => ?_
      exact mul_le_mul_of_nonneg_left (hbo r).2 (clamp01_nonneg _)
    linarith
  have hNumLo : ∀ t i, (1 - η') * colMean w S t i ≤ Num w S S t i := by
    intro t i
    rw [Num_S_eq_blockPo hA S t i]
    have hB0 : 0 ≤ ∑ a ∈ A, clamp01 (w (merge S t a) i) * Pw w a :=
      sum_nonneg fun a _ => mul_nonneg (clamp01_nonneg _) (Pw_nonneg _ _)
    have hA1 : (1 - η') * colMean w S t i ≤
        ∑ r ∈ agree S t, clamp01 (w r i) * blockPo A w' S r := by
      rw [hcm t i, ← mul_assoc, mul_comm ((1 - η') * u), sum_mul]
      refine sum_le_sum fun r _ => ?_
      exact mul_le_mul_of_nonneg_left (hbo r).1 (clamp01_nonneg _)
    linarith
  /- (★) and the numerator -/
  have hstar : ∀ G : ℝ, 0 ≤ G → (1 + η) * G + H ≤ 1 / 2 * ((1 + η + 2 * H) * max (2 * G) 1) := by
    intro G hG
    rcases le_total 1 (2 * G) with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]; nlinarith
  have hprodUp : ∀ t, ¬ (∀ j ∈ S, t j = r0 j) → ∏ i ∈ S, Num w S S t i ≤
      (1 / 2) ^ k * (1 + η + 2 * H) ^ k * Real.exp (43 / 100 * k) := by
    intro t ht0
    calc ∏ i ∈ S, Num w S S t i
        ≤ ∏ i ∈ S, (1 / 2 * ((1 + η + 2 * H) * max (2 * colMean w S t i) 1)) :=
          prod_le_prod (fun i _ => Num_nonneg _ _ _ _ _)
            (fun i _ => (hNumUp t i).trans (hstar _ (colMean_nonneg _ _ _ _)))
      _ = (1 / 2) ^ k * (1 + η + 2 * H) ^ k * ∏ i ∈ S, max (2 * colMean w S t i) 1 := by
          rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_const]; ring
      _ ≤ _ := by
          have : (0 : ℝ) ≤ (1 / 2) ^ k * (1 + η + 2 * H) ^ k := by positivity
          exact mul_le_mul_of_nonneg_left (hprodmax t ht0) this
  /- (B5-c) the normaliser -/
  have hPa : ∀ a, ∏ i ∈ S, colMean w' S a i ≤ 1 / 64 := by
    intro a
    have hpos : ∀ i ∈ S, 0 < max (2 * colMean w' S a i) 1 :=
      fun i _ => lt_of_lt_of_le one_pos (le_max_right _ _)
    have h1 : ∏ i ∈ S, colMean w' S a i ≤ (1 / 2) ^ k * ∏ i ∈ S, max (2 * colMean w' S a i) 1 := by
      calc ∏ i ∈ S, colMean w' S a i ≤ ∏ i ∈ S, (1 / 2 * max (2 * colMean w' S a i) 1) :=
            prod_le_prod (fun i _ => colMean_nonneg _ _ _ _) fun i _ => by
              have := le_max_left (2 * colMean w' S a i) 1; linarith
        _ = (1 / 2) ^ k * ∏ i ∈ S, max (2 * colMean w' S a i) 1 := by
            rw [prod_mul_distrib, prod_const]
    have h2 : ∏ i ∈ S, max (2 * colMean w' S a i) 1 ≤ Real.exp (43 / 100 * k) := by
      rw [← Real.exp_log (prod_pos hpos), Real.log_prod (fun i hi => (hpos i hi).ne')]
      refine Real.exp_le_exp.2 ?_
      have := hECr S a hk hk'
      rw [← hkdef] at this
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      linarith
    have h3 : (1 / 2 : ℝ) ^ k * Real.exp (43 / 100 * k) ≤ 1 / 64 := by
      rw [← rho0_pow]
      exact (pow_le_pow_of_le_one rho0_pos.le rho0_lt_one.le hk20).trans rho0_pow_twenty
    calc ∏ i ∈ S, colMean w' S a i ≤ (1 / 2) ^ k * ∏ i ∈ S, max (2 * colMean w' S a i) 1 := h1
      _ ≤ (1 / 2) ^ k * Real.exp (43 / 100 * k) := by gcongr
      _ ≤ 1 / 64 := h3
  have hsumA : ∀ a, ∑ t ∈ agree S a, ∏ i ∈ S, colMean w' S t i ≤ 2 ^ (N - k) / 64 := by
    intro a
    have e : ∀ t ∈ agree S a, ∏ i ∈ S, colMean w' S t i = ∏ i ∈ S, colMean w' S a i :=
      fun t ht => prod_congr rfl fun i _ => colMean_congr_agree w' (mem_agree.1 ht) i
    rw [sum_congr rfl e, sum_const, card_agree, nsmul_eq_mul, ← hkdef]
    push_cast
    have := hPa a
    have h2 : (0 : ℝ) < 2 ^ (N - k) := by positivity
    nlinarith
  have hnorm : (1 - η') ^ k * (2 ^ (N - k) / 2) ≤ ∑ t : State N, ∏ i ∈ S, Num w S S t i := by
    set hv : State N → Prop := fun t => (∀ j ∈ S, t j = r0 j) ∨ (∀ j ∈ S, t j = s j) with hhv
    have hP0 : ∀ t, 0 ≤ ∏ i ∈ S, colMean w' S t i := fun t =>
      prod_nonneg fun i _ => colMean_nonneg _ _ _ _
    have hsplit := sum_filter_add_sum_filter_not (univ : Finset (State N)) hv
      (fun t => ∏ i ∈ S, colMean w' S t i)
    have hheavysum : ∑ t ∈ univ.filter hv, ∏ i ∈ S, colMean w' S t i ≤ 2 ^ (N - k) / 4 := by
      have hsub : univ.filter hv ⊆ agree S r0 ∪ agree S s := by
        intro t ht
        rcases (mem_filter.1 ht).2 with h | h
        · exact mem_union_left _ (mem_agree.2 h)
        · exact mem_union_right _ (mem_agree.2 h)
      calc ∑ t ∈ univ.filter hv, ∏ i ∈ S, colMean w' S t i
          ≤ ∑ t ∈ agree S r0 ∪ agree S s, ∏ i ∈ S, colMean w' S t i :=
            sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => hP0 t
        _ ≤ ∑ t ∈ agree S r0, ∏ i ∈ S, colMean w' S t i +
            ∑ t ∈ agree S s, ∏ i ∈ S, colMean w' S t i := sum_union_le_of_nonneg _ _ hP0
        _ ≤ 2 ^ (N - k) / 64 + 2 ^ (N - k) / 64 := add_le_add (hsumA r0) (hsumA s)
        _ ≤ 2 ^ (N - k) / 4 := by
            have h2 : (0 : ℝ) < 2 ^ (N - k) := by positivity
            linarith
    have hall := hECh S hk hk'
    rw [← hkdef] at hall
    have hgeneric : (1 - η') ^ k * ∑ t ∈ univ.filter (fun t => ¬ hv t),
        ∏ i ∈ S, colMean w' S t i ≤ ∑ t : State N, ∏ i ∈ S, Num w S S t i := by
      rw [mul_sum]
      refine le_trans (sum_le_sum fun t ht => ?_)
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun t _ _ =>
          prod_nonneg fun i _ => Num_nonneg _ _ _ _ _)
      have hgt := hgen t (mem_filter.1 ht).2
      calc (1 - η') ^ k * ∏ i ∈ S, colMean w' S t i
          = ∏ i ∈ S, ((1 - η') * colMean w S t i) := by
            rw [prod_mul_distrib, prod_const]
            exact congrArg _ (prod_congr rfl fun i _ => (hgt i).symm)
        _ ≤ ∏ i ∈ S, Num w S S t i :=
            prod_le_prod (fun i _ => mul_nonneg (by linarith) (colMean_nonneg _ _ _ _))
              fun i _ => hNumLo t i
    have hpowpos : 0 ≤ (1 - η') ^ k := pow_nonneg (by linarith) k
    have h2 : (0 : ℝ) < 2 ^ (N - k) := by positivity
    have hge : 2 ^ (N - k) / 2 ≤ ∑ t ∈ univ.filter (fun t => ¬ hv t),
        ∏ i ∈ S, colMean w' S t i := by linarith
    calc (1 - η') ^ k * (2 ^ (N - k) / 2)
        ≤ (1 - η') ^ k * ∑ t ∈ univ.filter (fun t => ¬ hv t), ∏ i ∈ S, colMean w' S t i :=
          mul_le_mul_of_nonneg_left hge hpowpos
      _ ≤ _ := hgeneric
  /- (B5-d) the backward cause probability -/
  have hrat : (1 + η + 4 * H) ^ k ≤ 2 * (1 - η') ^ k := by
    have hb1 : 1 + η + 4 * H ≤ 1 + η + 8 / (N : ℝ) ^ 3 := by
      have : 4 * H ≤ 4 * (2 / (N : ℝ) ^ 3) := by linarith
      have e : 4 * (2 / (N : ℝ) ^ 3) = 8 / (N : ℝ) ^ 3 := by ring
      linarith
    have hb0 : 0 ≤ 1 + η + 4 * H := by positivity
    have hge1 : 1 ≤ 1 + η + 8 / (N : ℝ) ^ 3 := by
      have : (0 : ℝ) ≤ 8 / (N : ℝ) ^ 3 := by positivity
      linarith
    calc (1 + η + 4 * H) ^ k ≤ (1 + η + 8 / (N : ℝ) ^ 3) ^ k := pow_le_pow_left₀ hb0 hb1 k
      _ ≤ (1 + η + 8 / (N : ℝ) ^ 3) ^ N := pow_le_pow_right₀ hge1 hkN
      _ ≤ 2 * (1 - η') ^ N := hratio
      _ ≤ 2 * (1 - η') ^ k := by
          have : (1 - η') ^ N ≤ (1 - η') ^ k :=
            pow_le_pow_of_le_one (by linarith) (by linarith) hkN
          linarith
  have hrat2 : (1 + η + 2 * H) ^ k ≤ 2 * (1 - η') ^ k :=
    (pow_le_pow_left₀ (by positivity) (by linarith) k).trans hrat
  have hY : 0 < (1 - η') ^ k := pow_pos (by linarith) k
  have h2Nk : (0 : ℝ) < 2 ^ (N - k) := by positivity
  have hden : 0 < ∑ t' : State N, ∏ i ∈ S, Num w S S t' i :=
    lt_of_lt_of_le (by positivity) hnorm
  have hback : ∀ t, ¬ (∀ j ∈ S, t j = r0 j) → sysBackCause (tpmOf z) S s s t ≤ 4 * rho0 ^ k := by
    intro t ht0
    rw [sysBackCause_eq_Num hz s t S, ← hw, ← hkdef]
    rw [div_le_iff₀ hden]
    have hnum := hprodUp t ht0
    have hE0 : 0 ≤ Real.exp (43 / 100 * k) := (Real.exp_pos _).le
    calc (2 : ℝ) ^ (N - k) * ∏ i ∈ S, Num w S S t i
        ≤ 2 ^ (N - k) * ((1 / 2) ^ k * (1 + η + 2 * H) ^ k * Real.exp (43 / 100 * k)) :=
          mul_le_mul_of_nonneg_left hnum h2Nk.le
      _ ≤ 2 ^ (N - k) * ((1 / 2) ^ k * (2 * (1 - η') ^ k) * Real.exp (43 / 100 * k)) := by
          gcongr
      _ = 4 * rho0 ^ k * ((1 - η') ^ k * (2 ^ (N - k) / 2)) := by rw [rho0_pow]; ring
      _ ≤ 4 * rho0 ^ k * ∑ t' : State N, ∏ i ∈ S, Num w S S t' i := by
          have : 0 ≤ 4 * rho0 ^ k := by have := rho0_pos; positivity
          exact mul_le_mul_of_nonneg_left hnorm this
  /- the pattern of `r0` (two fixed rows): the tilt `∏ (y + U)/2 ≤ 4 P(r0) e^{-N/400}` -/
  have hNk : N - k = 1 := by omega
  have hagree : agree S r0 = {r0, r1} := by
    ext r
    simp only [mem_agree, mem_insert, mem_singleton]
    constructor
    · intro h
      by_cases hx : r x = r0 x
      · left; funext j
        by_cases hj : j = x
        · rw [hj]; exact hx
        · exact h j ((hmemS j).2 hj)
      · right; funext j
        by_cases hj : j = x
        · subst hj
          simp only [hr1, flipAt, Function.update_self]
          cases h1 : r j <;> cases h2 : r0 j <;> simp_all
        · rw [hr1x j ((hmemS j).2 hj) hj]; exact h j ((hmemS j).2 hj)
    · rintro (rfl | rfl)
      · exact fun _ _ => rfl
      · exact hr1S
  have hr01 : r0 ≠ r1 := (flipAt_ne x r0).symm
  have hm : ∀ i, colMean w S r0 i = (clamp01 (w r0 i) + clamp01 (w r1 i)) / 2 := by
    intro i
    rw [colMean, hagree, sum_pair hr01, ← hkdef, hNk]; norm_num <;> rfl
  have hy' : ∀ i, 1 / 2 ≤ clamp01 (w r0 i) := hy
  have hU0 : ∀ i, 0 ≤ clamp01 (w r1 i) := fun i => clamp01_nonneg _
  have htilt : ∏ i ∈ S, colMean w S r0 i ≤ 4 * Pw w r0 * Real.exp (-(N : ℝ) / 400) := by
    have hfac : ∀ i, colMean w S r0 i = clamp01 (w r0 i) * Real.exp (-lamEX w r0 x i) := by
      intro i
      have a1 := hy' i; have a2 := hU0 i
      rw [hm, lamEX, Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
      rfl
    rw [prod_congr rfl fun i _ => hfac i, prod_mul_distrib, ← Real.exp_sum]
    have hPx : Pw w r0 = clamp01 (w r0 x) * ∏ i ∈ S, clamp01 (w r0 i) := by
      rw [Pw, hSdef]; exact (mul_prod_erase _ (fun i => clamp01 (w r0 i)) (mem_univ x)).symm
    have hyx := hy' x
    have hyx1 : clamp01 (w r0 x) ≤ 1 := clamp01_le_one _
    have h0 : 0 ≤ ∏ i ∈ S, clamp01 (w r0 i) := prod_nonneg fun i _ => clamp01_nonneg _
    have hprodS : ∏ i ∈ S, clamp01 (w r0 i) ≤ 2 * Pw w r0 := by
      rw [hPx]; nlinarith
    have hlx : lamEX w r0 x x ≤ Real.log 2 := by
      unfold lamEX
      have a2 := hU0 x
      have h0 : 0 < 2 * clamp01 (w r0 x) / (clamp01 (w r0 x) + clamp01 (w r1 x)) := by
        positivity
      refine Real.log_le_log h0 ?_
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hsumS : ∑ i ∈ S, lamEX w r0 x i = ∑ j, lamEX w r0 x j - lamEX w r0 x x := by
      rw [hSdef, ← add_sum_erase _ _ (mem_univ x)]; ring
    have hexp : Real.exp (-∑ i ∈ S, lamEX w r0 x i) ≤ 2 * Real.exp (-(N : ℝ) / 400) := by
      rw [show (2 : ℝ) * Real.exp (-(N : ℝ) / 400) = Real.exp (Real.log 2 + -(N : ℝ) / 400) by
        rw [Real.exp_add, Real.exp_log (by norm_num)]]
      apply Real.exp_le_exp.2
      have := hlam
      rw [hsumS]
      linarith
    calc (∏ i ∈ S, clamp01 (w r0 i)) * Real.exp (∑ i ∈ S, -lamEX w r0 x i)
        = (∏ i ∈ S, clamp01 (w r0 i)) * Real.exp (-∑ i ∈ S, lamEX w r0 x i) := by
          rw [sum_neg_distrib]
      _ ≤ (2 * Pw w r0) * (2 * Real.exp (-(N : ℝ) / 400)) :=
          mul_le_mul hprodS hexp (Real.exp_pos _).le (by have := Pw_nonneg w r0; positivity)
      _ = 4 * Pw w r0 * Real.exp (-(N : ℝ) / 400) := by ring
  have hback0 : ∀ t, (∀ j ∈ S, t j = r0 j) →
      sysBackCause (tpmOf z) S s s t ≤ 16 * Pw w r0 * Real.exp (-(N : ℝ) / 400) := by
    intro t ht0
    rw [sysBackCause_eq_Num hz s t S, ← hw, ← hkdef]
    rw [div_le_iff₀ hden]
    have hmt : ∀ i, colMean w S t i = colMean w S r0 i := fun i => colMean_congr_agree w ht0 i
    have hm4 : ∀ i, 1 / 4 ≤ colMean w S r0 i := fun i => by
      rw [hm]; have := hy' i; have := hU0 i; linarith
    have hnum : ∏ i ∈ S, Num w S S t i ≤ (1 + η + 4 * H) ^ k * ∏ i ∈ S, colMean w S r0 i := by
      calc ∏ i ∈ S, Num w S S t i ≤ ∏ i ∈ S, ((1 + η + 4 * H) * colMean w S r0 i) :=
            prod_le_prod (fun i _ => Num_nonneg _ _ _ _ _) fun i _ => by
              have h1 := hNumUp t i
              rw [hmt] at h1
              have := hm4 i
              nlinarith
        _ = _ := by rw [prod_mul_distrib, prod_const]
    have hP0 := Pw_nonneg w r0
    calc (2 : ℝ) ^ (N - k) * ∏ i ∈ S, Num w S S t i
        ≤ 2 * ((2 * (1 - η') ^ k) * (4 * Pw w r0 * Real.exp (-(N : ℝ) / 400))) := by
          rw [hNk, pow_one]
          refine mul_le_mul_of_nonneg_left (hnum.trans ?_) (by norm_num)
          exact mul_le_mul hrat htilt (prod_nonneg fun i _ => colMean_nonneg _ _ _ _)
            (by positivity)
      _ = 16 * Pw w r0 * Real.exp (-(N : ℝ) / 400) * ((1 - η') ^ k * (2 ^ (N - k) / 2)) := by
          rw [hNk]; ring
      _ ≤ 16 * Pw w r0 * Real.exp (-(N : ℝ) / 400) * ∑ t' : State N, ∏ i ∈ S, Num w S S t' i := by
          have : 0 ≤ 16 * Pw w r0 * Real.exp (-(N : ℝ) / 400) := by positivity
          exact mul_le_mul_of_nonneg_left hnorm this
  /- (B5-e) the log-ratio -/
  have hlog2 : ∀ t, ∀ j ∈ S, pos (Real.logb 2 (Num w S S t j / Num w S {j} t j)) ≤ 2 := by
    intro t j hj
    have hjS : ({j} : Finset (Fin N)) ⊆ S := singleton_subset_iff.2 hj
    have hlow : Zs w / 4 ≤ Num w S {j} t j := by
      have hpt : ∀ v, 1 / 4 * Pw w v ≤ meanW w S {j} t j v * Pw w v := by
        intro v
        refine mul_le_mul_of_nonneg_right ?_ (Pw_nonneg w v)
        rw [meanW_eq_colMean w hjS t j v]
        have hM : N - ({j} ∪ Sᶜ).card = k - 1 := by
          rw [card_union_compl hjS, card_singleton]; omega
        have h1 := tr4 hA ({j} ∪ Sᶜ) (merge S t v) j
        have hc3 : (((agree ({j} ∪ Sᶜ) (merge S t v)).filter (· ∈ A)).card : ℝ) ≤ 3 := by
          have : ((agree ({j} ∪ Sᶜ) (merge S t v)).filter (· ∈ A)).card ≤ 3 :=
            (card_le_card fun r hr => (mem_filter.1 hr).2).trans hAcard
          exact_mod_cast this
        have h2 := hEH ({j} ∪ Sᶜ) (merge S t v) j
        rw [hM] at h1 h2
        have h1' : |colMean w ({j} ∪ Sᶜ) (merge S t v) j - colMean w' ({j} ∪ Sᶜ) (merge S t v) j| ≤
            3 / (2 : ℝ) ^ (k - 1) := h1.trans (by gcongr)
        have h3 := hhoeff k hk hkN
        rw [abs_le] at h1' h2
        linarith [h1'.1, h2.1]
      calc Zs w / 4 = ∑ v, 1 / 4 * Pw w v := by rw [Zs, ← mul_sum]; ring
        _ ≤ ∑ v, meanW w S {j} t j v * Pw w v := sum_le_sum fun v _ => hpt v
        _ = Num w S {j} t j := rfl
    have hup := Num_le_Zs w (subset_refl S) t j
    refine (pos_logb_div_le_logb (c := 4) (Num_pos hz s S S t j) (Num_pos hz s S {j} t j)
      (by norm_num) (by linarith)).trans (le_of_eq logb_two_four)
  /- (B5-f) conclusion -/
  obtain ⟨j, hj⟩ : S.Nonempty := card_pos.1 (by omega)
  set B := max (4 * rho0 ^ k) (16 * Pw w r0 * Real.exp (-(N : ℝ) / 400)) with hBdef
  have hB0 : (0 : ℝ) ≤ B * 2 := by have := rho0_pos; positivity
  have h := phi_le_cause hz (by omega : 2 ≤ S.card) hj hB0 fun t => by
    have hbt : sysBackCause (tpmOf z) S s s t ≤ B := by
      by_cases ht0 : ∀ j ∈ S, t j = r0 j
      · exact (hback0 t ht0).trans (le_max_right _ _)
      · exact (hback t ht0).trans (le_max_left _ _)
    exact mul_le_mul hbt (hlog2 t j hj) (pos_nonneg _) (by have := rho0_pos; positivity)
  have hkr : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hP0 := Pw_nonneg w r0
  refine h.trans ?_
  rcases le_total (4 * rho0 ^ k) (16 * Pw w r0 * Real.exp (-(N : ℝ) / 400)) with hab | hab
  · rw [hBdef, max_eq_right hab]
    refine le_trans ?_ (le_max_right _ _)
    have : 0 ≤ Pw w r0 * Real.exp (-(N : ℝ) / 400) := by positivity
    nlinarith
  · rw [hBdef, max_eq_left hab]
    refine le_trans ?_ (le_max_left _ _)
    have := hrate k hk hkN
    linarith

lemma ev_ratioX8 : ∀ᶠ N : ℕ in atTop, (1 + etaB N + 8 / (N : ℝ) ^ 3) ^ N ≤ 2 * (1 - etaX N) ^ N := by
  have hexp : Real.exp (1 / 5) ≤ 5 / 4 := by
    have h := exp_le_rat (q := 1 / 5) (r := 5 / 4) 10 1 (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)
    have e : (((1 / 5 : ℚ)) : ℝ) = 1 / 5 := by norm_num
    have e' : (((5 / 4 : ℚ)) : ℝ) = 5 / 4 := by norm_num
    rwa [e, e'] at h
  filter_upwards [eventually_ge_atTop 9, ev_etaX] with N hN h1
  have hN' : (9 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set η' := etaX N with hη'
  have hη'0 : 0 ≤ η' := etaX_nonneg N
  have hη0 : 0 ≤ etaB N := (Real.exp_pos _).le
  have hNη : (N : ℝ) * etaB N ≤ 1 / 10 := by
    have : (N : ℝ) * etaB N ≤ (N : ℝ) * η' := by
      have := tauN_pos N; gcongr; simp only [hη', etaX]; have : (0 : ℝ) ≤ 2 ^ (D1 N + 2) * tauN N := by
        positivity
      linarith
    linarith
  have hlow : 1 - N * η' ≤ (1 - η') ^ N := by
    have := one_add_mul_le_pow (a := -η') (by nlinarith) N
    rw [← sub_eq_add_neg] at this
    linarith
  have hup : (1 + etaB N + 8 / (N : ℝ) ^ 3) ^ N ≤ Real.exp (1 / 5) := by
    have ha0 : 0 ≤ etaB N + 8 / (N : ℝ) ^ 3 := by positivity
    calc (1 + etaB N + 8 / (N : ℝ) ^ 3) ^ N ≤ Real.exp (etaB N + 8 / (N : ℝ) ^ 3) ^ N := by
          apply pow_le_pow_left₀ (by positivity)
          linarith [Real.add_one_le_exp (etaB N + 8 / (N : ℝ) ^ 3)]
      _ = Real.exp (N * (etaB N + 8 / (N : ℝ) ^ 3)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (1 / 5) := by
          apply Real.exp_le_exp.2
          have : (N : ℝ) * (8 / (N : ℝ) ^ 3) = 8 / (N : ℝ) ^ 2 := by field_simp
          have h2 : 8 / (N : ℝ) ^ 2 ≤ 8 / 81 := by
            apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); nlinarith
          nlinarith
  linarith


/-- Every unit of row `r0` lies in some pair cell (own copy). -/
lemma sub_EX_pair_cover {s r0 : State N} {x : Fin N} {w : Param N} (hw : w ∈ EX N s r0 x) (j : Fin N) :
    ∃ i : Fin KP, (w r0 j, w (flipAt x r0) j) ∈ exIP (cP i) := by
  classical
  by_contra hno
  push Not at hno
  set F : Fin KP → Finset (Fin N) := fun i => univ.filter fun j => (w r0 j, w (flipAt x r0) j) ∈ exIP (cP i)
  have hdisj : ((univ : Finset (Fin KP)) : Set (Fin KP)).PairwiseDisjoint F := by
    intro i _ i' _ hii'
    refine Finset.disjoint_filter.2 fun j _ h1 h2 => ?_
    exact Set.disjoint_left.1 (exIP_disjoint hii') h1 h2
  have hcard : (univ.biUnion F).card = N := by
    rw [card_biUnion hdisj]
    refine Eq.trans ?_ (nP_sum N)
    exact sum_congr rfl fun i _ => hw.1 i
  have hsub : univ.biUnion F ⊆ univ.erase j := by
    intro j' hj'
    obtain ⟨i, -, hi⟩ := mem_biUnion.1 hj'
    refine mem_erase.2 ⟨fun e => ?_, mem_univ _⟩
    rw [e] at hi
    exact hno i (mem_filter.1 hi).2
  have := card_le_card hsub
  rw [hcard, card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin] at this
  have hN : 0 < N := Fin.pos j
  omega

/-- On `EX`, every entry of row `r0` is `≥ 1/2`. -/
lemma sub_EX_y_half {s r0 : State N} {x : Fin N} {w : Param N} (hw : w ∈ EX N s r0 x) (j : Fin N) :
    (1 / 2 : ℝ) ≤ clamp01 (w r0 j) := by
  obtain ⟨i, hi⟩ := sub_EX_pair_cover hw j
  have hm := cell_mem (cP_mem i) hi
  rw [hm.2.2.2.2.2.2.2.1]
  exact hm.2.2.1

/-- **Leaf `phi_S_le_EX`, case `S = U \ {x}`.** -/
theorem phi_S_le_EX_coX : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    ∀ w ∈ openCube N, w ∈ EX N s r0 x → EXFacts N s r0 x w → RestGood N s r0 x w →
      SubGood N s r0 x w → phi (flipP s w) s (univ.erase x) < betaW w * N / 10 ^ 6 := by
  have hxhi : x0 ≤ 2027325541 / 10000000000 := by
    have := cr_x0_bounds.2; unfold crX0hi at this; push_cast at this; exact this
  have hc : (0 : ℝ) < 1 / 4 - 2027325541 / 10000000000 := by norm_num
  filter_upwards [ev_B5XNum, ev_ratioX8, tc_of_EX, sumA_le, eventually_ge_atTop 2,
    ev_poly_exp 0 (3 * 10 ^ 6) hc (by norm_num : (0 : ℝ) < 1),
    ev_poly_exp 0 (96 * 10 ^ 6) (c := 1 / 400) (by norm_num) (by norm_num : (0 : ℝ) < 1)]
    with N hnum hrat8 htc hsum hN2 hev hev2
  intro s r0 x hham w ho hw hF hR hSG
  obtain ⟨w', hA, hE, hG, -⟩ := hSG.cmp
  have hN : 1 ≤ N := hnum.one_le
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set z := flipP s w with hz
  have hzo : z ∈ openCube N := flipP_mem_openCube ho
  have hzw : flipP s z = w := flipP_invol s w
  have hH := hsum s r0 x hham w ho hw hF
  have hphi := thmCoX_det hN hnum.big hnum.d1 hnum.eta hrat8 hnum.hoeff hnum.rate hham hzo
      (by rw [hzw]; exact hA) hE (by rw [hzw]; exact hH)
      (by rw [hzw]; exact fun i => sub_EX_y_half hw i) (by rw [hzw]; exact hF.S)
  rw [hzw] at hphi
  have htc := htc s r0 x hham w ho hw hF hR
  have hZ : Zs w ≤ 3 := by
    have h1 := Zs_le_add hA
    have h2 := hG.g3.2.1
    have h3 : 2 / (N : ℝ) ^ 3 ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
      have : (2 : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) this 3
      linarith
    linarith
  have hZpos : 0 < Zs w := b1_Zs_pos ho
  have hPpos : 0 < Pw w r0 := b1_Pw_pos ho r0
  have hP : Real.exp (-(2027325541 / 10000000000 * N)) ≤ Pw w r0 := by
    rw [Pw_eq_exp ho]; apply Real.exp_le_exp.2
    have := hF.T
    have := Real.log_natCast_nonneg N
    nlinarith
  have hev' : 3 * 10 ^ 6 * Real.exp (-(N : ℝ) / 4) < Real.exp (-(2027325541 / 10000000000 * N)) := by
    have e : Real.exp (-(N : ℝ) / 4) = Real.exp (-((1 / 4 - 2027325541 / 10000000000) * N)) *
        Real.exp (-(2027325541 / 10000000000 * N)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    simp only [pow_zero, mul_one] at hev
    have := Real.exp_pos (-(2027325541 / 10000000000 * (N : ℝ)))
    nlinarith
  have hβ : Pw w r0 / (3 * 10 ^ 6) ≤ Pw w r0 / Zs w / 10 ^ 6 := by
    rw [div_div]; apply div_le_div_of_nonneg_left (Pw_nonneg _ _) (by positivity); nlinarith
  have hβN : Pw w r0 / Zs w / 10 ^ 6 ≤ Pw w r0 / Zs w * N / 10 ^ 6 := by
    have : 0 ≤ Pw w r0 / Zs w := div_nonneg (Pw_nonneg _ _) hZpos.le
    gcongr; nlinarith
  unfold betaW; rw [htc]
  refine lt_of_le_of_lt hphi (max_lt ?_ ?_)
  · calc Real.exp (-(N : ℝ) / 4) < Pw w r0 / (3 * 10 ^ 6) := by
          rw [lt_div_iff₀ (by norm_num)]; linarith
      _ ≤ _ := hβ.trans hβN
  · have hev2' : 96 * 10 ^ 6 * Real.exp (-(N : ℝ) / 400) < 1 := by
      simp only [pow_zero, mul_one] at hev2
      have e : -(N : ℝ) / 400 = -(1 / 400 * N) := by ring
      rw [e]; exact hev2
    have hNpos : (0 : ℝ) < N := by linarith
    calc 32 * N * Pw w r0 * Real.exp (-(N : ℝ) / 400)
        < Pw w r0 * N / (3 * 10 ^ 6) := by
          rw [lt_div_iff₀ (by norm_num)]
          have : 0 < Pw w r0 * N := by positivity
          nlinarith
      _ ≤ Pw w r0 / Zs w * N / 10 ^ 6 := by
          rw [show Pw w r0 * N / (3 * 10 ^ 6) = Pw w r0 / (3 * 10 ^ 6) * N by ring,
            show Pw w r0 / Zs w * N / 10 ^ 6 = Pw w r0 / Zs w / 10 ^ 6 * N by ring]
          exact mul_le_mul_of_nonneg_right hβ hNpos.le

end

end Census
end IIT
