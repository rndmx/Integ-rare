/-
Census, B1 LTBetaHi, module T2: **the good event of the triple stopping set**.

`lt3Good`: no tie in the row `tc`; every row has `< K` units with a non-robust flip; `< K` units of `s` near `1/2`;
`|Sp| < 12`; and not (`|Q| ≥ 7`, `|Base| ≤ b`, `≥ M` robust-bad members). Its complement is bounded by the sum of the
five exclusion probabilities; on it, `|Ex| ≤ (|Base|+1)K`, `|Top| - |Ex| ≤ 2^{|Base|}|Q|`, `|qFam| ≤ |F| + M`.
-/
import IIT.Census.B1LTHiMeas

namespace IIT
namespace Census

open MeasureTheory Finset

variable {N : ℕ}

open Classical in
/-- The good event. -/
def lt3Good (s : State N) (ε γ : ℝ) (k K b M : ℕ) (w : Param N) : Prop :=
  (∀ i j : Fin N, i ≠ j → clamp01 (w (tcRow w) i) ≠ clamp01 (w (tcRow w) j)) ∧
  (∀ h : State N, (univ.filter fun j : Fin N => ¬ stRobust N k (w (flip h j))).card < K) ∧
  (univ.filter fun j : Fin N => w s j ∈ Set.Ioo (1 / 2 - γ) (1 / 2 + γ)).card < K ∧
  (lt2Sp w).card < 12 ∧
  ¬ (7 ≤ (lt3Q s ε γ w).card ∧ (lt3Base s w).card ≤ b ∧
      M ≤ ((qFam (lt3Q s ε γ w)).filter fun S => ∃ r ∈ lt3Base s w, ∃ R ⊆ S, 2 ≤ R.card ∧
        ¬ stRobust N k (w (flipS r R))).card)

open Classical in
/-- **The complement of the good event**: union bound. -/
theorem lt3_not_good_le (s : State N) (ε γ : ℝ) (k K b M : ℕ) :
    cubeM N {w | ¬ lt3Good s ε γ k K b M w} ≤
      cubeM N {w | ∃ h : State N, K ≤ (univ.filter fun j : Fin N => ¬ stRobust N k (w (flip h j))).card} +
      cubeM N {w | K ≤ (univ.filter fun j : Fin N => w s j ∈ Set.Ioo (1 / 2 - γ) (1 / 2 + γ)).card} +
      cubeM N {w | 12 ≤ (lt2Sp (N := N) w).card} +
      cubeM N {w | 7 ≤ (lt3Q s ε γ w).card ∧ (lt3Base s w).card ≤ b ∧
        M ≤ ((qFam (lt3Q s ε γ w)).filter fun S => ∃ r ∈ lt3Base s w, ∃ R ⊆ S, 2 ≤ R.card ∧
          ¬ stRobust N k (w (flipS r R))).card} := by
  have htie : cubeM N {w : Param N | ∃ i j : Fin N, i ≠ j ∧
      clamp01 (w (tcRow w) i) = clamp01 (w (tcRow w) j)} = 0 :=
    measure_mono_null (fun w hw => by obtain ⟨i, j, h, e⟩ := hw; exact ⟨tcRow w, i, j, h, e⟩) null_entry_tie
  have hsub : {w | ¬ lt3Good s ε γ k K b M w} ⊆
      {w : Param N | ∃ i j : Fin N, i ≠ j ∧ clamp01 (w (tcRow w) i) = clamp01 (w (tcRow w) j)} ∪
      ({w | ∃ h : State N, K ≤ (univ.filter fun j : Fin N => ¬ stRobust N k (w (flip h j))).card} ∪
      {w | K ≤ (univ.filter fun j : Fin N => w s j ∈ Set.Ioo (1 / 2 - γ) (1 / 2 + γ)).card} ∪
      {w | 12 ≤ (lt2Sp (N := N) w).card} ∪
      {w | 7 ≤ (lt3Q s ε γ w).card ∧ (lt3Base s w).card ≤ b ∧
        M ≤ ((qFam (lt3Q s ε γ w)).filter fun S => ∃ r ∈ lt3Base s w, ∃ R ⊆ S, 2 ≤ R.card ∧
          ¬ stRobust N k (w (flipS r R))).card}) := by
    intro w hw
    unfold lt3Good at hw
    by_cases h1 : ∀ i j : Fin N, i ≠ j → clamp01 (w (tcRow w) i) ≠ clamp01 (w (tcRow w) j)
    · by_cases h2 : ∀ h : State N, (univ.filter fun j : Fin N => ¬ stRobust N k (w (flip h j))).card < K
      · by_cases h3 : (univ.filter fun j : Fin N => w s j ∈ Set.Ioo (1 / 2 - γ) (1 / 2 + γ)).card < K
        · by_cases h4 : (lt2Sp w).card < 12
          · have h5 : 7 ≤ (lt3Q s ε γ w).card ∧ (lt3Base s w).card ≤ b ∧
                M ≤ ((qFam (lt3Q s ε γ w)).filter fun S => ∃ r ∈ lt3Base s w, ∃ R ⊆ S, 2 ≤ R.card ∧
                  ¬ stRobust N k (w (flipS r R))).card := by
              by_contra h5; exact hw ⟨h1, h2, h3, h4, h5⟩
            exact Or.inr (Or.inr h5)
          · exact Or.inr (Or.inl (Or.inr (not_lt.1 h4)))
        · exact Or.inr (Or.inl (Or.inl (Or.inr (not_lt.1 h3))))
      · push Not at h2
        exact Or.inr (Or.inl (Or.inl (Or.inl h2)))
    · push Not at h1
      obtain ⟨i, j, h, e⟩ := h1
      exact Or.inl ⟨i, j, h, e⟩
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [htie, zero_add]
  refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add
    ((measure_union_le _ _).trans le_rfl) le_rfl)) le_rfl)

/-- **Deterministic consequences of the good event.** -/
theorem lt3_good_sizes (s : State N) (ε γ : ℝ) (hγ : γ < 1 / 2) {k K b M : ℕ} {w : Param N}
    (hb : 14 ≤ b) (hg : lt3Good s ε γ k K b M w) (hTop : (lt3Top s w ε).card ≤ k) :
    (lt3Base s w).card ≤ 14 ∧ (lt3Ex s ε γ w).card ≤ ((lt3Base s w).card + 1) * K ∧
      (lt3Top s w ε).card - (lt3Ex s ε γ w).card ≤ 2 ^ (lt3Base s w).card * (lt3Q s ε γ w).card ∧
      (7 ≤ (lt3Q s ε γ w).card → (qFam (lt3Q s ε γ w)).card < (lt3F s ε γ w).card + M) := by
  classical
  obtain ⟨-, hrob, hhalf, hSp, hmem⟩ := hg
  have hB : (lt3Base s w).card ≤ 14 := by
    unfold lt3Base
    exact (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans (by omega)))
  refine ⟨hB, lt3_Ex_card s ε γ hγ w hTop hrob hhalf, lt3_Q_card s ε γ w, fun h7 => ?_⟩
  have hbad : ((qFam (lt3Q s ε γ w)).filter fun S => ∃ r ∈ lt3Base s w, ∃ R ⊆ S, 2 ≤ R.card ∧
      ¬ stRobust N k (w (flipS r R))).card < M := by
    by_contra hc; exact hmem ⟨h7, by omega, not_lt.1 hc⟩
  have := lt3_F_card s ε γ w hTop
  omega

/-- The near-half width `γ₀ = e^{-3600}/2`. -/
noncomputable def lt3γ : ℝ := Real.exp (-3600) / 2

lemma lt3γ_pos : 0 < lt3γ := by unfold lt3γ; positivity

lemma lt3γ_lt : lt3γ < 1 / 2 := by
  unfold lt3γ
  have : Real.exp (-3600) < Real.exp 0 := Real.exp_lt_exp.2 (by norm_num)
  rw [Real.exp_zero] at this
  linarith

/-- **The good event has probability `≥ 1 - 2e^{-1.05N}`** (concrete parameters `k = N/20`, `K = N/600`, `b = 14`,
`γ = γ₀`, `M = N²/D`). -/
theorem lt3_not_good_ev (s : ∀ N, State N) (ε : ℝ) {D : ℕ} (hD : 1 ≤ D) :
    ∀ᶠ N : ℕ in Filter.atTop, cubeM N {w | ¬ lt3Good (s N) ε lt3γ (N / 20) (N / 600) 14 (N * N / D) w} ≤
      ENNReal.ofReal (2 * Real.exp (-((105 / 100 : ℝ) * N))) := by
  filter_upwards [lt2_Sp_ev, Filter.eventually_ge_atTop (10 ^ 6 * D)] with N hSp hN
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hNbig : 10 ^ 6 ≤ N := le_trans (Nat.le_mul_of_pos_right _ hD) hN
  have hNr : (10 : ℝ) ^ 6 * D ≤ N := by exact_mod_cast hN
  have hN0 : 0 < N := by omega
  -- the four pieces
  have h1 := lt3_unit_all_excl_le (N := N) (k := N / 20) (K := N / 600) hN0 (by omega) (by omega) (by omega)
  have h2 := lt3_u_excl_leD (N := N) (s N) (γ := lt3γ) (lam := 3600) (D := 1200) lt3γ_pos.le
    (by unfold lt3γ; linarith) (by norm_num) (by norm_num) (K := N / 600) (by
      have : N ≤ 1200 * (N / 600) := by omega
      exact_mod_cast this)
  have hMfl : N * N ≤ 2 * D * (N * N / D) := by
    have h := Nat.div_add_mod (N * N) D
    have hm := Nat.mod_lt (N * N) (show 0 < D by omega)
    have : 2 * D ≤ N * N := by nlinarith
    nlinarith
  have hMr : (N : ℝ) * N ≤ 2 * D * (N * N / D : ℕ) := by exact_mod_cast hMfl
  have hl3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have h4 := lt3_member_ev_le (N := N) (s N) ε lt3γ (k := N / 20) (b := 14) (M := N * N / D) (D := 2 * D)
    (by omega) (by norm_num) (by omega) (by omega) hMfl (by
      have hlog : Real.log (8 * 14 * ((2 * D : ℕ) : ℝ)) ≤ 8 * 14 * ((2 * D : ℕ) : ℝ) :=
        (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
      push_cast at hlog ⊢
      norm_num at hNr hlog ⊢
      linarith) (by
      push_cast
      have hNN : (N : ℝ) * (10 ^ 6 * D) ≤ N * N := mul_le_mul_of_nonneg_left hNr (Nat.cast_nonneg N)
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
      nlinarith)
  refine (lt3_not_good_le (s N) ε lt3γ (N / 20) (N / 600) 14 (N * N / D)).trans ?_
  have e2 : Real.exp ((Real.log 2 - 3600 / 1200) * N) ≤ Real.exp (-(2 * (N : ℝ))) := Real.exp_le_exp.2 (by
    have := Real.log_two_lt_d9; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; nlinarith)
  have e3 : 3 * Real.exp (-(2 * (N : ℝ))) ≤ Real.exp (-((105 / 100 : ℝ) * N)) := by
    have e : Real.exp (-((105 / 100 : ℝ) * N)) = Real.exp (-(2 * (N : ℝ))) * Real.exp (95 / 100 * N) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have h1 := Real.add_one_le_exp (95 / 100 * (N : ℝ))
    have h2 : (10 : ℝ) ^ 6 ≤ N := by exact_mod_cast hNbig
    nlinarith [Real.exp_pos (-(2 * (N : ℝ)))]
  have hE := Real.exp_pos (-((105 / 100 : ℝ) * N))
  calc _ ≤ ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) + ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) +
        ENNReal.ofReal (Real.exp (-((105 / 100 : ℝ) * N))) + ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) :=
        add_le_add (add_le_add (add_le_add h1 (h2.trans (ENNReal.ofReal_le_ofReal e2))) hSp) h4
    _ = ENNReal.ofReal (3 * Real.exp (-(2 * (N : ℝ))) + Real.exp (-((105 / 100 : ℝ) * N))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

lemma lt3_ceil_bounds (hN : 420 ≤ N) : N / 21 ≤ ⌈(1 / 21 : ℝ) * N⌉₊ ∧ ⌈(1 / 21 : ℝ) * N⌉₊ ≤ N / 20 := by
  have hNr : (420 : ℝ) ≤ N := by exact_mod_cast hN
  constructor
  · have : ((N / 21 : ℕ) : ℝ) ≤ (1 / 21 : ℝ) * N := by
      have := Nat.cast_div_le (m := N) (n := 21) (α := ℝ); push_cast at this ⊢; linarith
    exact Nat.cast_le.1 (this.trans (Nat.le_ceil _))
  · rw [Nat.ceil_le]
    have h20 : (N : ℝ) / 20 - 1 < ((N / 20 : ℕ) : ℝ) := by
      have := Nat.lt_div_mul_add (a := N) (b := 20) (by norm_num)
      have : (N : ℝ) < ((N / 20 : ℕ) : ℝ) * 20 + 20 := by exact_mod_cast (by omega : N < N / 20 * 20 + 20)
      linarith
    linarith

/-- **`Top` and `Q` sizes on the good event** (`ε = 1/21`, `N ≥ 420`). -/
theorem lt3_good_Q (s : State N) {M : ℕ} (hN : 420 ≤ N) {w : Param N}
    (hg : lt3Good s (1 / 21) lt3γ (N / 20) (N / 600) 14 M w)
    (hGU : lt3SpC s w → ⌈(1 / 21 : ℝ) * N⌉₊ ≤ (lt3GoodU s w).card) :
    (lt3Top s w (1 / 21)).card ≤ N / 20 ∧ N / 21 ≤ (lt3Top s w (1 / 21)).card ∧
      N / 21 - 15 * (N / 600) ≤ 2 ^ 14 * (lt3Q s (1 / 21) lt3γ w).card := by
  obtain ⟨hc1, hc2⟩ := lt3_ceil_bounds hN
  have hk1 : 1 ≤ ⌈(1 / 21 : ℝ) * N⌉₊ := le_trans (by omega) hc1
  have hTle : (lt3Top s w (1 / 21)).card ≤ N / 20 :=
    (lt3Top_card_le hk1 hg.1).trans hc2
  have hTge : N / 21 ≤ (lt3Top s w (1 / 21)).card := by
    refine hc1.trans ?_
    classical
    unfold lt3Top
    split_ifs with hc
    · rw [lt3TopP_card]; exact le_min le_rfl (hGU hc)
    · have := card_ge_yTopW w (ε := 1 / 21) (hc2.trans (Nat.div_le_self _ _))
      unfold lt3TopG; exact this
  obtain ⟨hB, hEx, hQ, -⟩ := lt3_good_sizes s (1 / 21) lt3γ lt3γ_lt (le_refl 14) hg hTle
  refine ⟨hTle, hTge, ?_⟩
  have h2 : 2 ^ (lt3Base s w).card ≤ 2 ^ 14 := Nat.pow_le_pow_right (by norm_num) hB
  have := Nat.mul_le_mul_right (lt3Q s (1 / 21) lt3γ w).card h2
  have : ((lt3Base s w).card + 1) * (N / 600) ≤ 15 * (N / 600) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **The kept family is large on the good event** (`ε = 1/21`, `M = N²/10^14`, `N ≥ 10^8`):
`m ≥ N/2300000` and `m² ≤ 2|F|`. -/
theorem lt3_good_F (s : State N) (hN : 10 ^ 8 ≤ N) {w : Param N}
    (hg : lt3Good s (1 / 21) lt3γ (N / 20) (N / 600) 14 (N * N / 10 ^ 14) w)
    (hGU : lt3SpC s w → ⌈(1 / 21 : ℝ) * N⌉₊ ≤ (lt3GoodU s w).card) :
    N / 2300000 ≤ qM (lt3Q s (1 / 21) lt3γ w) ∧ 7 ≤ (lt3Q s (1 / 21) lt3γ w).card ∧
      qM (lt3Q s (1 / 21) lt3γ w) * qM (lt3Q s (1 / 21) lt3γ w) ≤ 2 * (lt3F s (1 / 21) lt3γ w).card := by
  obtain ⟨hTle, -, hQ⟩ := lt3_good_Q s (by omega) hg hGU
  set Q := lt3Q s (1 / 21) lt3γ w
  have hm : N / 2300000 ≤ qM Q := by unfold qM; omega
  have h7 : 7 ≤ Q.card := by unfold qM at hm; omega
  refine ⟨hm, h7, ?_⟩
  obtain ⟨-, -, -, hF⟩ := lt3_good_sizes s (1 / 21) lt3γ lt3γ_lt (le_refl 14) hg hTle
  have hF := hF h7
  have hm3 : 3 ≤ qM Q := by omega
  rw [qFam_card hm3] at hF
  -- `N²/10^14 ≤ m²/2`
  set a := N / 2300000
  have ha : 43 ≤ a := by omega
  have hNa : N < 2300000 * (a + 1) := by omega
  have hM : N * N / 10 ^ 14 ≤ a * a / 2 := by
    have h1 : N * N ≤ (2300000 * (a + 1)) * (2300000 * (a + 1)) := Nat.mul_le_mul hNa.le hNa.le
    have h2 : (2300000 * (a + 1)) * (2300000 * (a + 1)) ≤ 10 ^ 14 * (a * a / 2) := by
      have : 4 * (a + 1) * (a + 1) ≤ 7 * (a * a) := by nlinarith
      have h3 : a * a ≤ 2 * (a * a / 2) + 1 := by omega
      nlinarith
    exact Nat.div_le_of_le_mul (h1.trans h2)
  have hmm : a * a ≤ qM Q * qM Q := Nat.mul_le_mul hm hm
  omega

/-- **Private blocks of different selected pairs are disjoint** (W2 5.3). -/
theorem lt3PB_disjoint (s : State N) (ε γ : ℝ) (w : Param N) {k k' : Finset (Fin N) × State N}
    (hk : k ∈ lt3Sel s ε γ w) (hk' : k' ∈ lt3Sel s ε γ w) (hne : k ≠ k') : Disjoint (lt3PB k) (lt3PB k') := by
  classical
  unfold lt3Sel at hk hk'
  split_ifs at hk hk' with hc
  swap
  · simp at hk
  obtain ⟨hS, hr⟩ := mem_product.1 hk
  obtain ⟨hS', hr'⟩ := mem_product.1 hk'
  have hSQ := qFam_sub (mem_filter.1 hS).1
  have hS'Q := qFam_sub (mem_filter.1 hS').1
  have hspec := lt3QOf_spec (lt3Base s w) (lt3Top s w ε \ lt3Ex s ε γ w) (tcRow w)
  rw [Finset.disjoint_left]
  intro q hq hq'
  unfold lt3PB at hq hq'
  obtain ⟨⟨R, i⟩, hp, rfl⟩ := mem_image.1 hq
  obtain ⟨⟨R', i'⟩, hp', he⟩ := mem_image.1 hq'
  obtain ⟨hRi, hnot⟩ := mem_filter.1 hp
  obtain ⟨hR'i, -⟩ := mem_filter.1 hp'
  obtain ⟨hR, hi⟩ := mem_product.1 hRi
  obtain ⟨hR', hi'⟩ := mem_product.1 hR'i
  have hR := mem_powerset.1 hR
  have hR' := mem_powerset.1 hR'
  simp only [Prod.mk.injEq] at he
  obtain ⟨hfl, rfl⟩ := he
  obtain ⟨hrr, hRR⟩ := flipS_inj_agree hc.2 (hR'.trans hS'Q) (hR.trans hSQ)
    ((card_le_card hR').trans (qFam_card_le (mem_filter.1 hS').1))
    ((card_le_card hR).trans (qFam_card_le (mem_filter.1 hS).1))
    (agree_pair_tc (hspec.2.2 _ hr') (hspec.2.2 _ hr)) hfl
  subst hRR
  by_cases hSS : k.1 = k'.1
  · exact hne (Prod.ext hSS hrr.symm)
  · exact hnot (shared_pos_sub (qFam_inter (mem_filter.1 hS).1 (mem_filter.1 hS').1 hSS) hR hR' hi hi')

end Census
end IIT
