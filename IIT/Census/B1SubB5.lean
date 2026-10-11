/-
B1 lower bound, leaf `phi_S_le_EX` (W7 §3 item 4), the near-universe candidates `S ∋ x`, `K2N < |S| < N`:
Theorem B5 of W4 re-proved for THREE fixed rows `A = {r0, r0^x, s}` (each heavy pattern of `S` contains
exactly one fixed row because `x ∈ S` separates `r0` from `r0^x`, and `ham(r0, s) > N - |S| + 1`).
-/
import IIT.Census.B1SubEF2

set_option maxHeartbeats 1000000

namespace IIT
namespace Census

open MeasureTheory Filter Finset

noncomputable section

variable {N : ℕ}

/-- `E5` for the three fixed rows `{r0, r0^x, s}`. -/
def E5X (N : ℕ) (s r0 : State N) (x : Fin N) : Set (Param N) :=
  E5 N s r0 ∩ EF N (flipAt x r0) ∩ EF2 N r0 x

/-- `η''` : the block-mass error with three removed rows. -/
def etaX (N : ℕ) : ℝ := etaB N + 2 ^ (D1 N + 2) * tauN N

lemma etaX_nonneg (N : ℕ) : 0 ≤ etaX N := by
  unfold etaX etaB; have := tauN_pos N; positivity

lemma rho0_pow_twenty : rho0 ^ 20 ≤ 1 / 64 := by
  have h := rho0_pow_ten
  have h0 : 0 ≤ rho0 ^ 10 := pow_nonneg rho0_pos.le _
  have e : rho0 ^ 20 = rho0 ^ 10 * rho0 ^ 10 := by rw [← pow_add]
  rw [e]; nlinarith

/-- **Theorem B5, three fixed rows** (deterministic). -/
theorem thmB5X_det (hN : 1 ≤ N) (hbig : 20 ≤ K2N N) (h3D : 3 * D1 N + 3 ≤ N)
    (hη' : N * etaX N ≤ 1 / 10)
    (hratio : (1 + etaB N + 4 / (N : ℝ) ^ 3) ^ N ≤ 2 * (1 - etaX N) ^ N)
    (hhoeff : ∀ k, K2N N < k → k ≤ N → deltaH N (k - 1) + 3 / (2 : ℝ) ^ (k - 1) ≤ 1 / 4)
    (hrate : ∀ k, K2N N < k → k ≤ N → 8 * (k : ℝ) * rho0 ^ k ≤ Real.exp (-(N : ℝ) / 4))
    {s r0 : State N} {x : Fin N} (hham : N ≤ 3 * ham r0 s) {z : Param N} (hz : z ∈ openCube N)
    {w' : Param N} (hA : AgreeOff (rowsA s r0 x) (flipP s z) w') (hE : w' ∈ E5X N s r0 x)
    (hH : ∑ a ∈ rowsA s r0 x, Pw (flipP s z) a ≤ 2 / (N : ℝ) ^ 3)
    {S : Finset (Fin N)} (hxS : x ∈ S) (hk : K2N N < S.card) (hk' : S.card < N) :
    phi z s S ≤ Real.exp (-(N : ℝ) / 4) := by
  classical
  set w := flipP s z with hw
  set k := S.card with hkdef
  set r1 := flipAt x r0 with hr1
  set A := rowsA s r0 x with hAdef
  have hkN : k ≤ N := card_le_N S
  have hdD : N - k < D1 N := sub_card_lt_D1 hk
  have hk20 : 20 ≤ k := by omega
  have hk10 : 10 ≤ k := by omega
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hg2, hEH⟩, hEW⟩, hECr⟩, hECh⟩, hEFtc⟩, hEFs⟩, hEFr1⟩, -⟩ := hE
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
  have hr0r1 : ¬ ∀ j ∈ S, r0 j = r1 j := by
    intro h
    have := h x hxS
    simp only [hr1, flipAt, Function.update_self] at this
    cases hh : r0 x <;> simp [hh] at this
  have hr1x : ∀ j ∈ S, j ≠ x → r1 j = r0 j := by
    intro j _ hjx; simp only [hr1, flipAt]; rw [Function.update_of_ne hjx]
  have hGeo : ∀ a ∈ A, ∀ b ∈ A, (∀ j ∈ S, a j = b j) → a = b := by
    have k1 : ¬ ∀ j ∈ S, r0 j = s j := hfar r0 (fun _ _ _ => rfl)
    have k2 : ¬ ∀ j ∈ S, r1 j = s j := hfar r1 hr1x
    intro a ha b hb hab
    simp only [hAdef, rowsA, mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · rfl
    · exact absurd hab hr0r1
    · exact absurd hab k1
    · exact absurd (fun j hj => (hab j hj).symm) hr0r1
    · rfl
    · exact absurd hab k2
    · exact absurd (fun j hj => (hab j hj).symm) k1
    · exact absurd (fun j hj => (hab j hj).symm) k2
    · rfl
  have hGplus : ∀ a ∈ A, ∀ r ∈ (agree S a).erase a, r ∉ A := by
    intro a ha r hr hrA
    exact ne_of_mem_erase hr (hGeo r hrA a ha (mem_agree.1 (mem_of_mem_erase hr)))
  /- generic patterns see only the fresh rows -/
  have hgen : ∀ t, ¬ (∃ a ∈ A, ∀ j ∈ S, t j = a j) → ∀ i, colMean w S t i = colMean w' S t i := by
    intro t ht i
    refine tr4_eq hA (fun a ha hat => ht ⟨a, ha, ?_⟩) i
    rw [mem_agree] at hat
    exact fun j hj => (hat j hj).symm
  have hEFall : ∀ a ∈ A, w' ∈ EF N a := by
    intro a ha
    simp only [hAdef, rowsA, mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hEFtc
    · exact hEFr1
    · exact hEFs
  /- (B5-b) the level `43/100` for every pattern -/
  have hheavy : ∀ a ∈ A, ∀ t, (∀ j ∈ S, t j = a j) →
      ∑ i ∈ S, Real.log (max (2 * colMean w S t i) 1) ≤ 43 / 100 * k := by
    intro a ha t hta
    refine le_trans (sum_le_sum fun i _ => ?_) (hEFall a ha S hk hk')
    rw [colMean_congr_agree w hta i]
    have h1 := colMean_le_colMeanPlus w S a i
    rw [colMeanPlus_congr hA (hGplus a ha) i] at h1
    apply Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _))
    exact max_le_max (by linarith) le_rfl
  have hlogsum : ∀ t, ∑ i ∈ S, Real.log (max (2 * colMean w S t i) 1) ≤ 43 / 100 * k := by
    intro t
    by_cases ht : ∃ a ∈ A, ∀ j ∈ S, t j = a j
    · obtain ⟨a, ha, hta⟩ := ht
      exact hheavy a ha t hta
    · rw [sum_congr rfl fun i _ => by rw [hgen t ht i]]
      have := hECr S t hk hk'
      rw [← hkdef] at this
      linarith
  have hprodmax : ∀ t, ∏ i ∈ S, max (2 * colMean w S t i) 1 ≤ Real.exp (43 / 100 * k) := by
    intro t
    have hpos : ∀ i ∈ S, 0 < max (2 * colMean w S t i) 1 :=
      fun i _ => lt_of_lt_of_le one_pos (le_max_right _ _)
    rw [← Real.exp_log (prod_pos hpos), Real.log_prod (fun i hi => (hpos i hi).ne')]
    exact Real.exp_le_exp.2 (hlogsum t)
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
  have hprodUp : ∀ t, ∏ i ∈ S, Num w S S t i ≤
      (1 / 2) ^ k * (1 + η + 2 * H) ^ k * Real.exp (43 / 100 * k) := by
    intro t
    calc ∏ i ∈ S, Num w S S t i
        ≤ ∏ i ∈ S, (1 / 2 * ((1 + η + 2 * H) * max (2 * colMean w S t i) 1)) :=
          prod_le_prod (fun i _ => Num_nonneg _ _ _ _ _)
            (fun i _ => (hNumUp t i).trans (hstar _ (colMean_nonneg _ _ _ _)))
      _ = (1 / 2) ^ k * (1 + η + 2 * H) ^ k * ∏ i ∈ S, max (2 * colMean w S t i) 1 := by
          rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_const]; ring
      _ ≤ _ := by
          have : (0 : ℝ) ≤ (1 / 2) ^ k * (1 + η + 2 * H) ^ k := by positivity
          exact mul_le_mul_of_nonneg_left (hprodmax t) this
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
    set hv : State N → Prop := fun t => ∃ a ∈ A, ∀ j ∈ S, t j = a j with hhv
    have hP0 : ∀ t, 0 ≤ ∏ i ∈ S, colMean w' S t i := fun t =>
      prod_nonneg fun i _ => colMean_nonneg _ _ _ _
    have hsplit := sum_filter_add_sum_filter_not (univ : Finset (State N)) hv
      (fun t => ∏ i ∈ S, colMean w' S t i)
    have hheavysum : ∑ t ∈ univ.filter hv, ∏ i ∈ S, colMean w' S t i ≤ 2 ^ (N - k) / 4 := by
      have hsub : univ.filter hv ⊆ agree S r0 ∪ agree S r1 ∪ agree S s := by
        intro t ht
        obtain ⟨a, ha, hta⟩ := (mem_filter.1 ht).2
        simp only [hAdef, rowsA, mem_insert, mem_singleton] at ha
        rcases ha with rfl | rfl | rfl
        · exact mem_union_left _ (mem_union_left _ (mem_agree.2 hta))
        · exact mem_union_left _ (mem_union_right _ (mem_agree.2 hta))
        · exact mem_union_right _ (mem_agree.2 hta)
      calc ∑ t ∈ univ.filter hv, ∏ i ∈ S, colMean w' S t i
          ≤ ∑ t ∈ agree S r0 ∪ agree S r1 ∪ agree S s, ∏ i ∈ S, colMean w' S t i :=
            sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => hP0 t
        _ ≤ ∑ t ∈ agree S r0 ∪ agree S r1, ∏ i ∈ S, colMean w' S t i +
            ∑ t ∈ agree S s, ∏ i ∈ S, colMean w' S t i := sum_union_le_of_nonneg _ _ hP0
        _ ≤ (∑ t ∈ agree S r0, ∏ i ∈ S, colMean w' S t i +
            ∑ t ∈ agree S r1, ∏ i ∈ S, colMean w' S t i) +
            ∑ t ∈ agree S s, ∏ i ∈ S, colMean w' S t i :=
            add_le_add (sum_union_le_of_nonneg _ _ hP0) le_rfl
        _ ≤ (2 ^ (N - k) / 64 + 2 ^ (N - k) / 64) + 2 ^ (N - k) / 64 :=
            add_le_add (add_le_add (hsumA r0) (hsumA r1)) (hsumA s)
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
  have hrat : (1 + η + 2 * H) ^ k ≤ 2 * (1 - η') ^ k := by
    have hb1 : 1 + η + 2 * H ≤ 1 + η + 4 / (N : ℝ) ^ 3 := by
      have : 2 * H ≤ 2 * (2 / (N : ℝ) ^ 3) := by linarith
      have e : 2 * (2 / (N : ℝ) ^ 3) = 4 / (N : ℝ) ^ 3 := by ring
      linarith
    have hb0 : 0 ≤ 1 + η + 2 * H := by positivity
    have hge1 : 1 ≤ 1 + η + 4 / (N : ℝ) ^ 3 := by
      have : (0 : ℝ) ≤ 4 / (N : ℝ) ^ 3 := by positivity
      linarith
    calc (1 + η + 2 * H) ^ k ≤ (1 + η + 4 / (N : ℝ) ^ 3) ^ k := pow_le_pow_left₀ hb0 hb1 k
      _ ≤ (1 + η + 4 / (N : ℝ) ^ 3) ^ N := pow_le_pow_right₀ hge1 hkN
      _ ≤ 2 * (1 - η') ^ N := hratio
      _ ≤ 2 * (1 - η') ^ k := by
          have : (1 - η') ^ N ≤ (1 - η') ^ k :=
            pow_le_pow_of_le_one (by linarith) (by linarith) hkN
          linarith
  have hback : ∀ t, sysBackCause (tpmOf z) S s s t ≤ 4 * rho0 ^ k := by
    intro t
    rw [sysBackCause_eq_Num hz s t S, ← hw, ← hkdef]
    have hY : 0 < (1 - η') ^ k := pow_pos (by linarith) k
    have h2 : (0 : ℝ) < 2 ^ (N - k) := by positivity
    have hden : 0 < ∑ t' : State N, ∏ i ∈ S, Num w S S t' i :=
      lt_of_lt_of_le (by positivity) hnorm
    rw [div_le_iff₀ hden]
    have hnum := hprodUp t
    have hE0 : 0 ≤ Real.exp (43 / 100 * k) := (Real.exp_pos _).le
    calc (2 : ℝ) ^ (N - k) * ∏ i ∈ S, Num w S S t i
        ≤ 2 ^ (N - k) * ((1 / 2) ^ k * (1 + η + 2 * H) ^ k * Real.exp (43 / 100 * k)) :=
          mul_le_mul_of_nonneg_left hnum h2.le
      _ ≤ 2 ^ (N - k) * ((1 / 2) ^ k * (2 * (1 - η') ^ k) * Real.exp (43 / 100 * k)) := by
          gcongr
      _ = 4 * rho0 ^ k * ((1 - η') ^ k * (2 ^ (N - k) / 2)) := by rw [rho0_pow]; ring
      _ ≤ 4 * rho0 ^ k * ∑ t' : State N, ∏ i ∈ S, Num w S S t' i := by
          have : 0 ≤ 4 * rho0 ^ k := by have := rho0_pos; positivity
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
  have hB0 : (0 : ℝ) ≤ 4 * rho0 ^ k * 2 := by have := rho0_pos; positivity
  have h := phi_le_cause hz (by omega : 2 ≤ S.card) hxS hB0 fun t =>
    mul_le_mul (hback t) (hlog2 t x hxS) (pos_nonneg _) (by have := rho0_pos; positivity)
  calc phi z s S ≤ k * (4 * rho0 ^ k * 2) := h
    _ = 8 * k * rho0 ^ k := by ring
    _ ≤ Real.exp (-(N : ℝ) / 4) := hrate k hk hkN

/-- **Theorem B5, three fixed rows, `x ∉ S`** (deterministic; the `r0`-pattern holds `r0` and `r0^x`). -/
theorem thmB5Xn_det (hN : 1 ≤ N) (hbig : 20 ≤ K2N N) (h3D : 3 * D1 N + 3 ≤ N)
    (hη' : N * etaX N ≤ 1 / 10)
    (hratio : (1 + etaB N + 4 / (N : ℝ) ^ 3) ^ N ≤ 2 * (1 - etaX N) ^ N)
    (hhoeff : ∀ k, K2N N < k → k ≤ N → deltaH N (k - 1) + 3 / (2 : ℝ) ^ (k - 1) ≤ 1 / 4)
    (hrate : ∀ k, K2N N < k → k ≤ N → 8 * (k : ℝ) * rho0 ^ k ≤ Real.exp (-(N : ℝ) / 4))
    {s r0 : State N} {x : Fin N} (hham : N ≤ 3 * ham r0 s) {z : Param N} (hz : z ∈ openCube N)
    {w' : Param N} (hA : AgreeOff (rowsA s r0 x) (flipP s z) w') (hE : w' ∈ E5X N s r0 x)
    (hH : ∑ a ∈ rowsA s r0 x, Pw (flipP s z) a ≤ 2 / (N : ℝ) ^ 3)
    {S : Finset (Fin N)} (hxS : x ∉ S) (hk : K2N N < S.card) (hk2 : S.card + 2 ≤ N) :
    phi z s S ≤ Real.exp (-(N : ℝ) / 4) := by
  classical
  set w := flipP s z with hw
  set k := S.card with hkdef
  set r1 := flipAt x r0 with hr1
  set A := rowsA s r0 x with hAdef
  have hkN : k ≤ N := card_le_N S
  have hk' : S.card < N := by omega
  have hdD : N - k < D1 N := sub_card_lt_D1 hk
  have hk20 : 20 ≤ k := by omega
  have hk10 : 10 ≤ k := by omega
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hg2, hEH⟩, hEW⟩, hECr⟩, hECh⟩, -⟩, hEFs⟩, -⟩, hEF2⟩ := hE
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
  have hheavy0 : ∀ t, (∀ j ∈ S, t j = r0 j) →
      ∑ i ∈ S, Real.log (max (2 * colMean w S t i) 1) ≤ 43 / 100 * k := by
    intro t hta
    refine le_trans (sum_le_sum fun i _ => ?_) (hEF2 S hk hk2 hxS)
    rw [colMean_congr_agree w hta i]
    have h1 : colMean w S r0 i ≤ colMeanSet w S r0 F i := by
      unfold colMean colMeanSet cmSetCol colsOf
      gcongr with r _
      split_ifs
      · exact clamp01_le_one _
      · exact le_rfl
    have h2 : colMeanSet w S r0 F i = colMeanSet w' S r0 F i := by
      unfold colMeanSet cmSetCol colsOf
      congr 1
      refine sum_congr rfl fun r hr => ?_
      split_ifs with hrF
      · rfl
      · have hne0 : r ≠ r0 := fun h => hrF (by rw [h, hFdef]; exact mem_insert_self _ _)
        have hne1 : r ≠ r1 := fun h => hrF (by
          rw [h, hFdef]; exact mem_insert_of_mem (mem_singleton_self _))
        have hrA : r ∉ A := by
          intro hrA
          simp only [hAdef, rowsA, mem_insert, mem_singleton] at hrA
          rcases hrA with h | h | h
          · exact hne0 h
          · exact hne1 h
          · subst h; exact k1 fun j hj => ((mem_agree.1 hr) j hj).symm
        rw [hA r hrA]
    rw [h2] at h1
    apply Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _))
    exact max_le_max (by linarith) le_rfl
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
  have hlogsum : ∀ t, ∑ i ∈ S, Real.log (max (2 * colMean w S t i) 1) ≤ 43 / 100 * k := by
    intro t
    by_cases ht : (∀ j ∈ S, t j = r0 j) ∨ (∀ j ∈ S, t j = s j)
    · rcases ht with ht | ht
      · exact hheavy0 t ht
      · exact hheavys t ht
    · rw [sum_congr rfl fun i _ => by rw [hgen t ht i]]
      have := hECr S t hk hk'
      rw [← hkdef] at this
      linarith
  have hprodmax : ∀ t, ∏ i ∈ S, max (2 * colMean w S t i) 1 ≤ Real.exp (43 / 100 * k) := by
    intro t
    have hpos : ∀ i ∈ S, 0 < max (2 * colMean w S t i) 1 :=
      fun i _ => lt_of_lt_of_le one_pos (le_max_right _ _)
    rw [← Real.exp_log (prod_pos hpos), Real.log_prod (fun i hi => (hpos i hi).ne')]
    exact Real.exp_le_exp.2 (hlogsum t)
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
  have hprodUp : ∀ t, ∏ i ∈ S, Num w S S t i ≤
      (1 / 2) ^ k * (1 + η + 2 * H) ^ k * Real.exp (43 / 100 * k) := by
    intro t
    calc ∏ i ∈ S, Num w S S t i
        ≤ ∏ i ∈ S, (1 / 2 * ((1 + η + 2 * H) * max (2 * colMean w S t i) 1)) :=
          prod_le_prod (fun i _ => Num_nonneg _ _ _ _ _)
            (fun i _ => (hNumUp t i).trans (hstar _ (colMean_nonneg _ _ _ _)))
      _ = (1 / 2) ^ k * (1 + η + 2 * H) ^ k * ∏ i ∈ S, max (2 * colMean w S t i) 1 := by
          rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_const]; ring
      _ ≤ _ := by
          have : (0 : ℝ) ≤ (1 / 2) ^ k * (1 + η + 2 * H) ^ k := by positivity
          exact mul_le_mul_of_nonneg_left (hprodmax t) this
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
  have hrat : (1 + η + 2 * H) ^ k ≤ 2 * (1 - η') ^ k := by
    have hb1 : 1 + η + 2 * H ≤ 1 + η + 4 / (N : ℝ) ^ 3 := by
      have : 2 * H ≤ 2 * (2 / (N : ℝ) ^ 3) := by linarith
      have e : 2 * (2 / (N : ℝ) ^ 3) = 4 / (N : ℝ) ^ 3 := by ring
      linarith
    have hb0 : 0 ≤ 1 + η + 2 * H := by positivity
    have hge1 : 1 ≤ 1 + η + 4 / (N : ℝ) ^ 3 := by
      have : (0 : ℝ) ≤ 4 / (N : ℝ) ^ 3 := by positivity
      linarith
    calc (1 + η + 2 * H) ^ k ≤ (1 + η + 4 / (N : ℝ) ^ 3) ^ k := pow_le_pow_left₀ hb0 hb1 k
      _ ≤ (1 + η + 4 / (N : ℝ) ^ 3) ^ N := pow_le_pow_right₀ hge1 hkN
      _ ≤ 2 * (1 - η') ^ N := hratio
      _ ≤ 2 * (1 - η') ^ k := by
          have : (1 - η') ^ N ≤ (1 - η') ^ k :=
            pow_le_pow_of_le_one (by linarith) (by linarith) hkN
          linarith
  have hback : ∀ t, sysBackCause (tpmOf z) S s s t ≤ 4 * rho0 ^ k := by
    intro t
    rw [sysBackCause_eq_Num hz s t S, ← hw, ← hkdef]
    have hY : 0 < (1 - η') ^ k := pow_pos (by linarith) k
    have h2 : (0 : ℝ) < 2 ^ (N - k) := by positivity
    have hden : 0 < ∑ t' : State N, ∏ i ∈ S, Num w S S t' i :=
      lt_of_lt_of_le (by positivity) hnorm
    rw [div_le_iff₀ hden]
    have hnum := hprodUp t
    have hE0 : 0 ≤ Real.exp (43 / 100 * k) := (Real.exp_pos _).le
    calc (2 : ℝ) ^ (N - k) * ∏ i ∈ S, Num w S S t i
        ≤ 2 ^ (N - k) * ((1 / 2) ^ k * (1 + η + 2 * H) ^ k * Real.exp (43 / 100 * k)) :=
          mul_le_mul_of_nonneg_left hnum h2.le
      _ ≤ 2 ^ (N - k) * ((1 / 2) ^ k * (2 * (1 - η') ^ k) * Real.exp (43 / 100 * k)) := by
          gcongr
      _ = 4 * rho0 ^ k * ((1 - η') ^ k * (2 ^ (N - k) / 2)) := by rw [rho0_pow]; ring
      _ ≤ 4 * rho0 ^ k * ∑ t' : State N, ∏ i ∈ S, Num w S S t' i := by
          have : 0 ≤ 4 * rho0 ^ k := by have := rho0_pos; positivity
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
  have hB0 : (0 : ℝ) ≤ 4 * rho0 ^ k * 2 := by have := rho0_pos; positivity
  have h := phi_le_cause hz (by omega : 2 ≤ S.card) hj hB0 fun t =>
    mul_le_mul (hback t) (hlog2 t j hj) (pos_nonneg _) (by have := rho0_pos; positivity)
  calc phi z s S ≤ k * (4 * rho0 ^ k * 2) := h
    _ = 8 * k * rho0 ^ k := by ring
    _ ≤ Real.exp (-(N : ℝ) / 4) := hrate k hk hkN

/-! ### The eventual numeric inequalities of `thmB5X_det` -/

lemma ev_3D1X : ∀ᶠ N : ℕ in atTop, 3 * D1 N + 3 ≤ N := by
  filter_upwards [eventually_ge_atTop 1,
    ev_quad_half_comp tendsto_natLog2 0 12 51 (by norm_num : (0 : ℝ) < 1)] with N hN h
  set ℓ := Nat.log 2 N with hℓ
  have h2 : ((2 : ℝ) ^ ℓ) ≤ N := by exact_mod_cast two_pow_natLog_le hN
  have hp : (2 : ℝ) ^ ℓ * (1 / 2) ^ ℓ = 1 := by rw [← mul_pow]; norm_num
  have h' : (12 * (ℓ : ℝ) + 51) < 2 ^ ℓ := by
    have hpos : (0 : ℝ) < (1 / 2) ^ ℓ := by positivity
    have : (0 * (ℓ : ℝ) ^ 2 + 12 * ℓ + 51) * (1 / 2) ^ ℓ * 2 ^ ℓ < 1 * 2 ^ ℓ :=
      mul_lt_mul_of_pos_right h (by positivity)
    rw [mul_assoc, mul_comm ((1 / 2 : ℝ) ^ ℓ), hp] at this
    linarith
  have : ((3 * D1 N + 3 : ℕ) : ℝ) ≤ N := by
    unfold D1; push_cast; linarith
  exact_mod_cast this

lemma ev_big20 : ∀ᶠ N : ℕ in atTop, 20 ≤ K2N N := by
  filter_upwards [ev_3D1, eventually_ge_atTop 60] with N h1 h2
  rw [K2N_eq_sub_D1]; omega

lemma ev_etaX : ∀ᶠ N : ℕ in atTop, (N : ℝ) * etaX N ≤ 1 / 10 := by
  filter_upwards [eventually_ge_atTop 1,
    ev_poly_exp 1 20 (c := 1 / 10) (by norm_num) (by norm_num : (0 : ℝ) < 1),
    ev_poly_exp 5 (20 * 2 ^ 18 * Real.exp (2 / 9)) (c := 2 / 9) (by norm_num)
      (by norm_num : (0 : ℝ) < 1)] with N hN h1 h2
  have hD := two_pow_D1_le hN
  have a1 : (N : ℝ) * etaB N ≤ 1 / 20 := by
    rw [etaB_eq]; simp only [pow_one] at h1; linarith
  have a2 : (N : ℝ) * (2 ^ (D1 N + 2) * tauN N) ≤ 1 / 20 := by
    have hτ := tauN_pos N
    have h2D : (2 : ℝ) ^ (D1 N + 2) ≤ 4 * (2 ^ 16 * (N : ℝ) ^ 4) := by
      rw [pow_add]; norm_num; linarith
    calc (N : ℝ) * (2 ^ (D1 N + 2) * tauN N) ≤ N * (4 * (2 ^ 16 * (N : ℝ) ^ 4) * tauN N) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2D hτ.le) (by positivity)
      _ = (20 * 2 ^ 18 * Real.exp (2 / 9) * (N : ℝ) ^ 5 * Real.exp (-(2 / 9 * N))) / 20 := by
          rw [tauN_eq]; ring
      _ ≤ 1 / 20 := by linarith
  unfold etaX; rw [mul_add]; linarith

lemma ev_ratioX : ∀ᶠ N : ℕ in atTop, (1 + etaB N + 4 / (N : ℝ) ^ 3) ^ N ≤ 2 * (1 - etaX N) ^ N := by
  have hexp : Real.exp (1 / 5) ≤ 5 / 4 := by
    have h := exp_le_rat (q := 1 / 5) (r := 5 / 4) 10 1 (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)
    have e : (((1 / 5 : ℚ)) : ℝ) = 1 / 5 := by norm_num
    have e' : (((5 / 4 : ℚ)) : ℝ) = 5 / 4 := by norm_num
    rwa [e, e'] at h
  filter_upwards [eventually_ge_atTop 7, ev_etaX] with N hN h1
  have hN' : (7 : ℝ) ≤ N := by exact_mod_cast hN
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
  have hup : (1 + etaB N + 4 / (N : ℝ) ^ 3) ^ N ≤ Real.exp (1 / 5) := by
    have ha0 : 0 ≤ etaB N + 4 / (N : ℝ) ^ 3 := by positivity
    calc (1 + etaB N + 4 / (N : ℝ) ^ 3) ^ N ≤ Real.exp (etaB N + 4 / (N : ℝ) ^ 3) ^ N := by
          apply pow_le_pow_left₀ (by positivity)
          linarith [Real.add_one_le_exp (etaB N + 4 / (N : ℝ) ^ 3)]
      _ = Real.exp (N * (etaB N + 4 / (N : ℝ) ^ 3)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (1 / 5) := by
          apply Real.exp_le_exp.2
          have : (N : ℝ) * (4 / (N : ℝ) ^ 3) = 4 / (N : ℝ) ^ 2 := by field_simp
          have h2 : 4 / (N : ℝ) ^ 2 ≤ 4 / 49 := by
            apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); nlinarith
          nlinarith
  linarith

lemma ev_hoeffX : ∀ᶠ N : ℕ in atTop, ∀ k, K2N N < k → k ≤ N →
    deltaH N (k - 1) + 3 / (2 : ℝ) ^ (k - 1) ≤ 1 / 4 := by
  filter_upwards [eventually_ge_atTop 1, ev_3D1,
    ev_poly_geom 5 (r := 1 / 2) (by norm_num) (by norm_num) (2 ^ 24) (by norm_num : (0 : ℝ) < 1)]
    with N hN h3 hg
  intro k hk hkN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hkk : N ≤ (k - 1) + D1 N := by rw [K2N_eq_sub_D1] at hk; omega
  have hD := two_pow_D1_le hN
  have hinv : 1 / (2 : ℝ) ^ (k - 1) ≤ 2 ^ 16 * (N : ℝ) ^ 4 * (1 / 2) ^ N := by
    have h1 : (2 : ℝ) ^ N ≤ 2 ^ (k - 1) * 2 ^ D1 N := by
      rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) hkk
    have hk1 : (0 : ℝ) < 2 ^ (k - 1) := by positivity
    have h2 : (0 : ℝ) < 2 ^ N := by positivity
    rw [one_div_pow, div_le_iff₀ hk1]
    rw [show 2 ^ 16 * (N : ℝ) ^ 4 * (1 / 2 ^ N) * 2 ^ (k - 1) =
      (2 ^ 16 * (N : ℝ) ^ 4 * 2 ^ (k - 1)) / 2 ^ N by ring, le_div_iff₀ h2, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hD hk1.le]
  have hy : (N : ℝ) / 2 ^ (k - 1) ≤ 1 / 256 := by
    rw [div_eq_mul_one_div]
    calc (N : ℝ) * (1 / 2 ^ (k - 1)) ≤ N * (2 ^ 16 * (N : ℝ) ^ 4 * (1 / 2) ^ N) := by gcongr
      _ = 2 ^ 24 * (N : ℝ) ^ 5 * (1 / 2) ^ N / 256 := by ring
      _ ≤ 1 / 256 := by linarith
  have hδ : deltaH N (k - 1) ≤ 1 / 8 := by
    unfold deltaH
    have : Real.sqrt ((N : ℝ) / 2 ^ (k - 1)) ≤ 1 / 16 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num; linarith
    linarith
  have h2k : 3 / (2 : ℝ) ^ (k - 1) ≤ 1 / 8 := by
    rw [show 3 / (2 : ℝ) ^ (k - 1) = 3 * (1 / 2 ^ (k - 1)) by ring]
    have hp : (0 : ℝ) ≤ (1 / 2) ^ N := by positivity
    have hc : 3 * ((2 : ℝ) ^ 16 * (N : ℝ) ^ 4) ≤ 2 ^ 24 * (N : ℝ) ^ 5 / 8 := by
      have : (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 5 := pow_le_pow_right₀ hN' (by norm_num)
      have h4 : (0 : ℝ) ≤ (N : ℝ) ^ 4 := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_right hc hp
    have e : 2 ^ 24 * (N : ℝ) ^ 5 / 8 * (1 / 2) ^ N = 2 ^ 24 * (N : ℝ) ^ 5 * (1 / 2) ^ N / 8 := by
      ring
    nlinarith
  linarith

/-- The numeric conditions of `thmB5X_det`. -/
structure B5XNum (N : ℕ) : Prop where
  one_le : 1 ≤ N
  big : 20 ≤ K2N N
  d1 : 3 * D1 N + 3 ≤ N
  eta : (N : ℝ) * etaX N ≤ 1 / 10
  ratio : (1 + etaB N + 4 / (N : ℝ) ^ 3) ^ N ≤ 2 * (1 - etaX N) ^ N
  hoeff : ∀ k, K2N N < k → k ≤ N → deltaH N (k - 1) + 3 / (2 : ℝ) ^ (k - 1) ≤ 1 / 4
  rate : ∀ k, K2N N < k → k ≤ N → 8 * (k : ℝ) * rho0 ^ k ≤ Real.exp (-(N : ℝ) / 4)

theorem ev_B5XNum : ∀ᶠ N : ℕ in atTop, B5XNum N := by
  filter_upwards [eventually_ge_atTop 1, ev_big20, ev_3D1X, ev_etaX, ev_ratioX, ev_hoeffX, ev_rate]
    with N h1 h2 h3 h4 h5 h6 h7
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-! ### The good event on the rows outside `rowsA`, and its conditional probability -/

/-- **Own good event** (rows outside `rowsA` only): some parameter agreeing with `w` off the three fixed rows
lies in `E5X ∩ GoodW ∩ openCube`. It reads `w` only off `rowsA` (`AgreeOff`). -/
structure SubGood (N : ℕ) (s r0 : State N) (x : Fin N) (w : Param N) : Prop where
  cmp : ∃ w', AgreeOff (rowsA s r0 x) w w' ∧ w' ∈ E5X N s r0 x ∧ GoodW N s w' ∧ w' ∈ openCube N

/-- The failure bound of `SubGood`. -/
def fSub (N : ℕ) : ℝ := fGood N + fB5 N + 2 * (Real.exp 1 * ((1 / bEF) * N) ^ D1 N * bEF ^ N)

theorem cubeM_not_E5X_good (hN : 1 ≤ N) (hnum : EWnum N) (s r0 : State N) (x : Fin N) :
    cubeM N (E5X N s r0 x ∩ {w | GoodW N s w} ∩ openCube N)ᶜ ≤ ENNReal.ofReal (fSub N) := by
  have hsub : (E5X N s r0 x ∩ {w | GoodW N s w} ∩ openCube N)ᶜ ⊆
      {w | ¬ GoodW N s w} ∪ (E5 N s r0)ᶜ ∪ (EF N (flipAt x r0))ᶜ ∪ (EF2 N r0 x)ᶜ ∪ (openCube N)ᶜ := by
    intro w hw
    simp only [E5X, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
      not_and_or] at hw ⊢
    tauto
  have h1 : 0 ≤ fGood N := by
    obtain ⟨h2, h3, h4, h6, h11, h12, h13a, h13b, h16⟩ := fg_nonneg N
    unfold fGood; positivity
  have h2 : 0 ≤ fB5 N := by
    have := aCr_pos; have := bEF_pos
    obtain ⟨h2, -⟩ := fg_nonneg N
    unfold fB5 fEH; positivity
  have h3 : 0 ≤ Real.exp 1 * ((1 / bEF) * N) ^ D1 N * bEF ^ N := by have := bEF_pos; positivity
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  rw [cubeM_compl_openCube, add_zero]
  refine ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add
    ((measure_union_le _ _).trans
    (add_le_add (cubeM_notGood_le_fGood s) (cubeM_not_E5_le hN hnum s r0)))
    (cubeM_not_EF hN (flipAt x r0)))) (cubeM_not_EF2 hN r0 x))).trans ?_
  rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (by positivity) h3,
    ← ENNReal.ofReal_add (by positivity) h3]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold fSub; ring

/-- **Conditional bound of `SubGood`** given ANY values of the fixed rows. -/
theorem SubGood_cond_le (hN : 1 ≤ N) (hnum : EWnum N) (s r0 : State N) (x : Fin N)
    (f : rowsA s r0 x → Fin N → ℝ) :
    rowsOutM (rowsA s r0 x) {g | ¬ SubGood N s r0 x (glueRows (rowsA s r0 x) f g)} ≤
      ENNReal.ofReal (fSub N) := by
  have hEm : MeasurableSet (E5X N s r0 x ∩ {w | GoodW N s w} ∩ openCube N) :=
    ((((measurableSet_E5 s r0).inter (measurableSet_EF _)).inter (measurableSet_EF2 r0 x)).inter
      (measurableSet_goodW s)).inter
      b1_measurableSet_openCube
  refine (cpl_transfer (rowsA s r0 x) f hEm (Φ := SubGood N s r0 x) ?_).trans
    (cubeM_not_E5X_good hN hnum s r0 x)
  rintro w w' hA ⟨⟨hE, hG⟩, ho⟩
  exact ⟨⟨w', hA, hE, hG, ho⟩⟩

theorem tendsto_fSub : Tendsto fSub atTop (nhds 0) := by
  have hb := bEF_pos
  have hF : Tendsto (fun N : ℕ => Real.exp 1 * ((1 / bEF) * N) ^ D1 N * bEF ^ N) atTop (nhds 0) :=
    tendsto_D1_geom (by rw [le_div_iff₀ hb, one_mul]; exact bEF_lt_one.le) hb bEF_lt_one
      (by positivity)
  have hF2 := hF.const_mul 2
  rw [mul_zero] at hF2
  have := (tendsto_fGood.add tendsto_fB5).add hF2
  simp only [add_zero] at this
  exact this.congr fun N => by unfold fSub; ring

/-- **`SubGood_cond`**: eventually, given any fixed rows, `SubGood` fails with probability `≤ ε`. -/
theorem SubGood_cond {ε : ℝ} (hε : 0 < ε) : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N),
    ∀ f : rowsA s r0 x → Fin N → ℝ,
      rowsOutM (rowsA s r0 x) {g | ¬ SubGood N s r0 x (glueRows (rowsA s r0 x) f g)} ≤
        ENNReal.ofReal ε := by
  filter_upwards [eventually_ge_atTop 1, ev_EWnum, (tendsto_order.1 tendsto_fSub).2 ε hε]
    with N hN hnum hlt
  intro s r0 x f
  exact (SubGood_cond_le hN hnum s r0 x f).trans (ENNReal.ofReal_le_ofReal hlt.le)

/-! ### Application to the leaf: near-universe candidates through `x` -/

/-- On the open cube, `P(r) ≤ N^{-3}` when `X(r) ≥ 3 ln N`. -/
lemma Pw_le_inv_cube {w : Param N} (ho : w ∈ openCube N) (hN : 1 ≤ N) {r : State N}
    (h : 3 * Real.log N ≤ XW w r) : Pw w r ≤ 1 / (N : ℝ) ^ 3 := by
  rw [Pw_eq_exp ho]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have e : 1 / (N : ℝ) ^ 3 = Real.exp (-(3 * Real.log N)) := by
    rw [Real.exp_neg, show 3 * Real.log N = Real.log ((N : ℝ) ^ 3) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity), one_div]
  rw [e]; exact Real.exp_le_exp.2 (by linarith)

/-- The three fixed rows carry mass `≤ 2/N³` on the good event. -/
theorem sumA_le : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    ∀ w ∈ openCube N, w ∈ EX N s r0 x → EXFacts N s r0 x w →
      ∑ a ∈ rowsA s r0 x, Pw w a ≤ 2 / (N : ℝ) ^ 3 := by
  have hl2 : 0 < Real.log 2 / 2 := by have := Real.log_pos one_lt_two; linarith
  filter_upwards [eventually_ge_atTop 30,
    ev_poly_exp 3 (2 * Real.exp ((KS : ℝ) ^ 2 * Real.log 2)) hl2 (by norm_num : (0 : ℝ) < 1)]
    with N hN30 hev
  intro s r0 x hham w ho hw hF
  have hN : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN3 : (0 : ℝ) < (N : ℝ) ^ 3 := by positivity
  have h0 : r0 ≠ s := fun h => by rw [h, ham_self] at hham; omega
  have h1 : flipAt x r0 ≠ s := fun h => by
    have := ham_flipAt_le_one x r0; rw [h, ham_comm] at this; omega
  have h01 : r0 ≠ flipAt x r0 := (flipAt_ne x r0).symm
  -- row r0
  have hxE : 0 ≤ ∑ k, -Real.log (xE w s k) := sum_nonneg fun k _ => by
    have a1 : 0 ≤ xE w s k := le_max_of_le_left (clamp01_nonneg _)
    have a2 : xE w s k ≤ 1 := max_le (clamp01_le_one _) (by linarith [clamp01_nonneg (w s k)])
    linarith [Real.log_nonpos a1 a2]
  have hP0 : Pw w r0 ≤ 1 / (N : ℝ) ^ 3 := Pw_le_inv_cube ho hN (by have := hF.L; linarith)
  -- row r0^x
  have hP1 : Pw w (flipAt x r0) ≤ 1 / (N : ℝ) ^ 3 / 2 := by
    have hD := hF.D
    rw [← XW_flip_sub ho] at hD
    rw [Pw_eq_exp ho] at hP0 ⊢
    have e : Real.exp (-XW w (flipAt x r0)) ≤ Real.exp (-XW w r0) * Real.exp (-1) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2
      have : (1 : ℝ) ≤ N / 30 := by
        rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (by omega : 30 ≤ N)
      linarith
    have he : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith [Real.add_one_le_exp (1 : ℝ)]
    have := Real.exp_pos (-XW w r0)
    nlinarith
  -- row s
  have hPs : Pw w s ≤ 1 / (N : ℝ) ^ 3 / 2 := by
    refine (Pw_s_le ho s).trans ?_
    have hL := EX_s_lower (s := s) (r0 := r0) (x := x) hw
    set c := (univ.filter fun k => w s k ∈ Set.Iio (1 / 2 : ℝ)).card
    have hpow : (1 / 2 : ℝ) ^ c = Real.exp (-(c * Real.log 2)) := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num), one_div, inv_pow]
    rw [hpow]
    have hl := Real.log_pos one_lt_two
    have hb : Real.exp (-(c * Real.log 2)) ≤
        Real.exp ((KS : ℝ) ^ 2 * Real.log 2) * Real.exp (-(Real.log 2 / 2 * N)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
    have hev' : 2 * Real.exp ((KS : ℝ) ^ 2 * Real.log 2) * (N : ℝ) ^ 3 *
        Real.exp (-(Real.log 2 / 2 * N)) ≤ 1 := hev.le
    rw [div_div, le_div_iff₀ (by positivity)]
    have hpos := Real.exp_pos (-(c * Real.log 2))
    nlinarith
  have e : ∑ a ∈ rowsA s r0 x, Pw w a = Pw w r0 + Pw w (flipAt x r0) + Pw w s := by
    simp only [rowsA]
    rw [sum_insert (by simp [h01, h0]), sum_insert (by simp [h1]), sum_singleton, add_assoc]
  rw [e]
  have : 2 / (N : ℝ) ^ 3 = 1 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 3 / 2 + 1 / (N : ℝ) ^ 3 / 2 := by ring
  linarith

/-- **Leaf `phi_S_le_EX`, case `x ∈ S`, `K2N < |S| < N`** (three-row B5). -/
theorem phi_S_le_EX_nearX : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    ∀ w ∈ openCube N, w ∈ EX N s r0 x → EXFacts N s r0 x w → RestGood N s r0 x w →
      SubGood N s r0 x w →
      ∀ S : Finset (Fin N), x ∈ S → K2N N < S.card → S.card < N →
        phi (flipP s w) s S < betaW w * N / 10 ^ 6 := by
  have hxhi : x0 ≤ 2027325541 / 10000000000 := by
    have := cr_x0_bounds.2; unfold crX0hi at this; push_cast at this; exact this
  have hc : (0 : ℝ) < 1 / 4 - 2027325541 / 10000000000 := by norm_num
  filter_upwards [ev_B5XNum, tc_of_EX, sumA_le, eventually_ge_atTop 2,
    ev_poly_exp 0 (3 * 10 ^ 6) hc (by norm_num : (0 : ℝ) < 1)] with N hnum htc hsum hN2 hev
  intro s r0 x hham w ho hw hF hR hSG S hxS hk hk'
  obtain ⟨w', hA, hE, hG, -⟩ := hSG.cmp
  have hN : 1 ≤ N := hnum.one_le
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set z := flipP s w with hz
  have hzo : z ∈ openCube N := flipP_mem_openCube ho
  have hzw : flipP s z = w := flipP_invol s w
  have hH := hsum s r0 x hham w ho hw hF
  have hphi : phi z s S ≤ Real.exp (-(N : ℝ) / 4) :=
    thmB5X_det hN hnum.big hnum.d1 hnum.eta hnum.ratio hnum.hoeff hnum.rate hham hzo
      (by rw [hzw]; exact hA) hE (by rw [hzw]; exact hH) hxS hk hk'
  -- the level `β`
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
  unfold betaW; rw [htc]
  calc phi z s S ≤ Real.exp (-(N : ℝ) / 4) := hphi
    _ < Pw w r0 / (3 * 10 ^ 6) := by rw [lt_div_iff₀ (by norm_num)]; linarith
    _ ≤ Pw w r0 / Zs w / 10 ^ 6 := by
        rw [div_div]; apply div_le_div_of_nonneg_left (Pw_nonneg _ _) (by positivity); nlinarith
    _ ≤ Pw w r0 / Zs w * N / 10 ^ 6 := by
        have : 0 ≤ Pw w r0 / Zs w := div_nonneg (Pw_nonneg _ _) hZpos.le
        gcongr; nlinarith

/-- **Leaf `phi_S_le_EX`, case `x ∉ S`, `K2N < |S| ≤ N - 2`** (three-row B5 with `EF2`). -/
theorem phi_S_le_EX_nearNotX : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    ∀ w ∈ openCube N, w ∈ EX N s r0 x → EXFacts N s r0 x w → RestGood N s r0 x w →
      SubGood N s r0 x w →
      ∀ S : Finset (Fin N), x ∉ S → K2N N < S.card → S.card + 2 ≤ N →
        phi (flipP s w) s S < betaW w * N / 10 ^ 6 := by
  have hxhi : x0 ≤ 2027325541 / 10000000000 := by
    have := cr_x0_bounds.2; unfold crX0hi at this; push_cast at this; exact this
  have hc : (0 : ℝ) < 1 / 4 - 2027325541 / 10000000000 := by norm_num
  filter_upwards [ev_B5XNum, tc_of_EX, sumA_le, eventually_ge_atTop 2,
    ev_poly_exp 0 (3 * 10 ^ 6) hc (by norm_num : (0 : ℝ) < 1)] with N hnum htc hsum hN2 hev
  intro s r0 x hham w ho hw hF hR hSG S hxS hk hk'
  obtain ⟨w', hA, hE, hG, -⟩ := hSG.cmp
  have hN : 1 ≤ N := hnum.one_le
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set z := flipP s w with hz
  have hzo : z ∈ openCube N := flipP_mem_openCube ho
  have hzw : flipP s z = w := flipP_invol s w
  have hH := hsum s r0 x hham w ho hw hF
  have hphi : phi z s S ≤ Real.exp (-(N : ℝ) / 4) :=
    thmB5Xn_det hN hnum.big hnum.d1 hnum.eta hnum.ratio hnum.hoeff hnum.rate hham hzo
      (by rw [hzw]; exact hA) hE (by rw [hzw]; exact hH) hxS hk hk'
  -- the level `β`
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
  unfold betaW; rw [htc]
  calc phi z s S ≤ Real.exp (-(N : ℝ) / 4) := hphi
    _ < Pw w r0 / (3 * 10 ^ 6) := by rw [lt_div_iff₀ (by norm_num)]; linarith
    _ ≤ Pw w r0 / Zs w / 10 ^ 6 := by
        rw [div_div]; apply div_le_div_of_nonneg_left (Pw_nonneg _ _) (by positivity); nlinarith
    _ ≤ Pw w r0 / Zs w * N / 10 ^ 6 := by
        have : 0 ≤ Pw w r0 / Zs w := div_nonneg (Pw_nonneg _ _) hZpos.le
        gcongr; nlinarith

end

end Census
end IIT
