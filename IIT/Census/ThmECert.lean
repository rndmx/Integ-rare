/-
Census, Theorem E for the sizes with certified regions (`k = 2, 4, 5`).

Off the null boundary, the field event and the effect event, a `k`-set with
`φ_s > c √(ln N) σ_N` puts the translated field of one of its orderings into the region
`cd_region k C e_N y_N` of an orbit representative `C` (`te_mem_regBad`).  A covered region lies in
a half-space `⟨v, ξ⟩ ≥ h y - Λ e` with `(L_n/L_d) vᵀ C_k v ≤ h²`, or in a slab `|⟨r, ξ⟩| ≤ Λ e`
with `r ≠ 0`; the Gaussian comparison of `ThmELind` bounds its probability by
`N^{-L l²/2} + err` resp. `O(e_N + ε_N) + err`, uniformly in the ordering and the translation
(`te_region_prob`).  With `y_N ≥ l √(ln N) + 1` and `L l²/2 > k`, the union over the `≤ N^k`
orderings, the representatives and the `2^k` translations tends to `0`
(`te_thmE_cert`).  The instances are `te_thmE_k2`, `te_thmE_k4`, `te_thmE_k5`.
-/
import IIT.Census.ThmEReduce
import IIT.Census.CertDataOrbit

namespace IIT
namespace Census

open MeasureTheory Finset Filter Topology ENNReal

noncomputable section

variable {N k : ℕ}

/-! ### The region event -/

/-- Some ordering, representative and translation put the field in the region. -/
def te_regBad (k N : ℕ) (c : ℝ) (reps : List (List (List Bool))) : Set (Param N) :=
  {w | ∃ e : Fin k ↪ Fin N, ∃ C ∈ reps, ∃ u0 : Fin (2 ^ k),
    cd_region k C (te_e k N) (te_y k c N) (te_sh u0 (te_xi e.injective w))}

theorem te_region_S (e : Fin k ↪ Fin N) {S : Finset (Fin N)} (hS : bg_U e = S) (w : Param N)
    (θ : SysPartition N S) (t : State N) (C : List (List Bool))
    (hC : ∀ i j : Fin k, e j ∈ profile θ (e i) ↔ cd_at C i j = true) {ε y : ℝ}
    (hmax : ∀ t', ur_xi w S (bg_ak k) (sigN N) t' ≤ ur_xi w S (bg_ak k) (sigN N) t + ε)
    (hmin : ∀ θ' : SysPartition N S, ur_F w θ t (sigN N) / (sysCutCount θ : ℝ) ≤
      ur_F w θ' t (sigN N) / (sysCutCount θ' : ℝ) + ε)
    (hy : y ≤ ur_F w θ t (sigN N)) :
    cd_region k C ε y (te_sh (te_pat e.injective t) (te_xi e.injective w)) := by
  subst hS
  exact te_region e w θ t C hC hmax hmin hy

/-- **Deterministic step.** -/
theorem te_mem_regBad {reps : List (List (List Bool))} {W : List (List ℕ × ℕ)}
    (hc : cd_orbitCheck k reps W = true) {s : State N} {z : Param N} (hz : z ∈ openCube N)
    {S : Finset (Fin N)} (hSk : S.card = k) {c : ℝ} (hc0 : 0 ≤ c)
    (h3 : 3 * te_eta N ≤ bg_ak k) (hfield : flipP s z ∉ te_fieldBad k N)
    (heff : z ∉ te_effBad k N s) (hphi : c * Real.sqrt (Real.log N) * sigN N < phi z s S) :
    flipP s z ∈ te_regBad k N c reps := by
  obtain ⟨e, hSe, θ, t, hmax, hmin, hy⟩ := te_reduce hz hSk hc0 h3 hfield heff hphi
  obtain ⟨σ, C, hCm, hprof⟩ := cd_classify_rep k e (by rw [hSe.symm]; exact te_hS e) θ reps W hc
  set e' : Fin k ↪ Fin N := σ.toEmbedding.trans e with he'
  have hU : bg_U e' = S := by
    rw [← hSe, bg_U, bg_U]
    ext x
    simp only [mem_image, mem_univ, true_and, he', Function.Embedding.trans_apply,
      Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨σ i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨σ.symm i, by simp⟩
  have hC : ∀ i j : Fin k, e' j ∈ profile θ (e' i) ↔ cd_at C i j = true := by
    intro i j
    simp only [he', Function.Embedding.trans_apply, Equiv.toEmbedding_apply]
    exact hprof i j
  exact ⟨e', C, hCm, te_pat e'.injective t,
    te_region_S e' hU (flipP s z) θ t C hC hmax hmin hy⟩

/-! ### Probability of one region -/

/-- **One covered region.** For `y_N ≥ l √(ln N) + 1` and `L l²/2 > k`, the probability that
the translated field of an ordering lies in the region is at most `g N` with `N^k g N → 0`. -/
theorem te_region_prob {Ln Ld : ℕ} (hLd : 0 < Ld) {C : List (List Bool)}
    (hcov : cd_Covered k Ln Ld C) {c l : ℝ} (hl : 0 < l)
    (hy : ∀ᶠ N : ℕ in atTop, l * Real.sqrt (Real.log N) + 1 ≤ te_y k c N)
    (hK : (k : ℝ) < Ln / Ld * l ^ 2 / 2) :
    ∃ g : ℕ → ℝ, (∀ N, 0 ≤ g N) ∧ Tendsto (fun N : ℕ => (N : ℝ) ^ k * g N) atTop (𝓝 0) ∧
      ∀ᶠ N : ℕ in atTop, ∀ (e : Fin k ↪ Fin N) (u0 : Fin (2 ^ k)),
        cubeM N {w | cd_region k C (te_e k N) (te_y k c N) (te_sh u0 (te_xi e.injective w))} ≤
          ENNReal.ofReal (g N) := by
  have hLdr : (0 : ℝ) < Ld := by exact_mod_cast hLd
  have he0 : Tendsto (fun N => te_e k N) atTop (𝓝 0) := by
    have h := te_tendsto_e k 0
    simpa using h
  have hε0 : Tendsto (fun N : ℕ => ps_eps N) atTop (𝓝 0) := by
    have h := te_tendsto_geom 0 (q := 99 / 100) (by norm_num) (by norm_num) 1
    simpa [ps_eps] using h
  rcases cd_covered_sound hLd hcov with ⟨v, hh, Λ, hh0, hΛ, hq, hsound⟩ |
    ⟨r, Λ, hr, hΛ, hsound⟩
  · by_cases hv0 : v = 0
    · -- the region is eventually empty
      refine ⟨fun _ => 0, fun _ => le_rfl, by simp, ?_⟩
      have hsmall : ∀ᶠ N : ℕ in atTop, Λ * te_e k N < hh := by
        have h := (he0.const_mul Λ)
        rw [mul_zero] at h
        exact (tendsto_order.1 h).2 hh hh0
      filter_upwards [hy, hsmall, te_e_nonneg k] with N hyN hsN hE0 e u0
      have hempty : {w : Param N | cd_region k C (te_e k N) (te_y k c N)
          (te_sh u0 (te_xi e.injective w))} = ∅ := by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hR
        have h1 := hsound _ _ _ hE0 hR
        simp only [hv0, Pi.zero_apply, zero_mul, sum_const_zero] at h1
        have hs0 : 0 ≤ l * Real.sqrt (Real.log N) := by positivity
        nlinarith
      rw [hempty, measure_empty]; exact bot_le
    · have hq0 : 0 < gg_quad (gg_C k) v := te_quad_pos hv0
      have hLn : (0 : ℝ) < Ln / Ld := by
        by_contra hle; push Not at hle
        have : Ln / Ld * l ^ 2 / 2 ≤ 0 := by
          have : 0 ≤ l ^ 2 := sq_nonneg l
          nlinarith
        linarith [Nat.cast_nonneg (α := ℝ) k]
      set K := Ln / Ld * l ^ 2 / 2 with hKdef
      set A := ∑ p, |v p| with hA
      refine ⟨fun N => Real.exp (-(K * Real.log N)) + ps_err (te_C2 k A) (te_C3 k A) N,
        fun N => ?_, ?_, ?_⟩
      · have := ps_err_nonneg (C2 := te_C2 k A) (C3 := te_C3 k A)
          (by unfold te_C2; positivity)
          (by unfold te_C3; have := te_C3G_nonneg k; positivity) N
        positivity
      · have h := (te_tendsto_exp_log k hK).add (te_tendsto_err k (te_C2 k A) (te_C3 k A))
        rw [add_zero] at h
        exact h.congr fun N => by ring
      · have hsmall : ∀ᶠ N : ℕ in atTop, Λ * te_e k N + ps_eps N < hh := by
          have h := (he0.const_mul Λ).add hε0
          rw [mul_zero, add_zero] at h
          exact (tendsto_order.1 h).2 hh hh0
        filter_upwards [hy, hsmall, te_e_nonneg k, eventually_ge_atTop 1] with N hyN hsN heN hN
          e u0
        set v' : Fin (k * 2 ^ k) → ℝ := fun q => v ((te_pi k u0).symm q) with hv'
        set h := hh * (l * Real.sqrt (Real.log N) + 1) - Λ * te_e k N with hhdef
        have hsub : {w : Param N | cd_region k C (te_e k N) (te_y k c N)
            (te_sh u0 (te_xi e.injective w))} ⊆
            {w | h ≤ ∑ p, v' p * te_xi e.injective w p} := by
          intro w hR
          have h1 := hsound _ _ _ heN hR
          rw [te_sum_sh] at h1
          simp only [Set.mem_setOf_eq]
          have : hh * (l * Real.sqrt (Real.log N) + 1) ≤ hh * te_y k c N :=
            mul_le_mul_of_nonneg_left hyN hh0.le
          linarith
        have hs0 : 0 ≤ l * Real.sqrt (Real.log N) := by positivity
        have hεh : ps_eps N < h := by
          rw [hhdef]; nlinarith [mul_nonneg hh0.le hs0]
        have hlin := te_halfspace_le e.injective v' hεh
        rw [te_quad_relabel, hv', te_sumabs_relabel] at hlin
        refine (measure_mono hsub).trans (te_le_ofReal (hlin.trans (add_le_add ?_ le_rfl)))
        -- the Gaussian exponent
        apply Real.exp_le_exp.2
        have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
        have hsq : Real.sqrt (Real.log N) ^ 2 = Real.log N := Real.sq_sqrt hlogN
        have hd : hh * (l * Real.sqrt (Real.log N)) ≤ h - ps_eps N := by
          rw [hhdef]; nlinarith
        have hd0 : 0 ≤ hh * (l * Real.sqrt (Real.log N)) := by positivity
        have hsq2 : hh ^ 2 * (l ^ 2 * Real.log N) ≤ (h - ps_eps N) ^ 2 := by
          have := pow_le_pow_left₀ hd0 hd 2
          rw [← hsq]; nlinarith
        have hqv : gg_quad (gg_C k) v ≤ hh ^ 2 / (Ln / Ld) := by
          rw [le_div_iff₀ hLn]; linarith
        rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
        calc K * Real.log N * (2 * gg_quad (gg_C k) v)
            ≤ K * Real.log N * (2 * (hh ^ 2 / (Ln / Ld))) := by
              have : 0 ≤ K * Real.log N := by rw [hKdef]; positivity
              gcongr
          _ = hh ^ 2 * (l ^ 2 * Real.log N) := by
              have hLn0 : (Ln : ℝ) ≠ 0 := by
                intro h0; rw [h0, zero_div] at hLn; exact lt_irrefl _ hLn
              rw [hKdef]; field_simp
          _ ≤ (h - ps_eps N) ^ 2 := hsq2
  · have hq0 : 0 < gg_quad (gg_C k) r := te_quad_pos hr
    set D := Real.sqrt (2 * Real.pi * gg_quad (gg_C k) r) with hD
    have hD0 : 0 < D := Real.sqrt_pos.2 (by positivity)
    set A := 2 * ∑ p, |r p| with hA
    refine ⟨fun N => 2 * (Λ * |te_e k N| + ps_eps N) / D + ps_err (te_C2 k A) (te_C3 k A) N,
      fun N => ?_, ?_, ?_⟩
    · have := ps_err_nonneg (C2 := te_C2 k A) (C3 := te_C3 k A)
        (by unfold te_C2; positivity)
        (by unfold te_C3; have := te_C3G_nonneg k; positivity) N
      have := ps_eps_pos N
      positivity
    · have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ k * |te_e k N|) atTop (𝓝 0) := by
        have h := (te_tendsto_e k k).abs
        rw [abs_zero] at h
        refine h.congr fun N => ?_
        rw [abs_mul, abs_of_nonneg (by positivity)]
      have h2 : Tendsto (fun N : ℕ => (N : ℝ) ^ k * ps_eps N) atTop (𝓝 0) := by
        have h := te_tendsto_geom k (q := 99 / 100) (by norm_num) (by norm_num) 1
        simpa [ps_eps] using h
      have h := ((h1.const_mul (2 * Λ / D)).add (h2.const_mul (2 / D))).add
        (te_tendsto_err k (te_C2 k A) (te_C3 k A))
      rw [mul_zero, mul_zero, add_zero, add_zero] at h
      refine h.congr fun N => ?_
      field_simp
    · filter_upwards [te_e_nonneg k] with N heN e u0
      set r' : Fin (k * 2 ^ k) → ℝ := fun q => r ((te_pi k u0).symm q) with hr'
      have hsub : {w : Param N | cd_region k C (te_e k N) (te_y k c N)
          (te_sh u0 (te_xi e.injective w))} ⊆
          {w | |∑ p, r' p * te_xi e.injective w p| ≤ Λ * te_e k N} := by
        intro w hR
        have h1 := hsound _ _ _ heN hR
        rw [te_sum_sh] at h1
        exact h1
      have hq' : 0 < gg_quad (gg_C k) r' := by rw [hr', te_quad_relabel]; exact hq0
      have hlin := te_slab_le e.injective r' hq' (Λ * te_e k N)
      rw [hr', te_quad_relabel, te_sumabs_relabel] at hlin
      refine (measure_mono hsub).trans (te_le_ofReal (hlin.trans (le_of_eq ?_)))
      rw [abs_mul, abs_of_nonneg hΛ, ← hD, ← hA]

/-! ### The theorem for certified sizes -/

/-- **Theorem E for a certified size.** If the orbit representatives `reps` are all covered at rate
`L = L_n / L_d`, `l < c κ_k` and `L l²/2 > k`, then with probability tending to one no `k`-set has
`φ_s > c √(ln N) σ_N`. -/
theorem te_thmE_cert {Ln Ld : ℕ} (hLd : 0 < Ld) {reps : List (List (List Bool))}
    {W : List (List ℕ × ℕ)} (hc : cd_orbitCheck k reps W = true)
    (hcov : ∀ C ∈ reps, cd_Covered k Ln Ld C) (hk : 1 ≤ k) {c l : ℝ} (hc0 : 0 ≤ c) (hl : 0 < l)
    (hlc : l < c * te_kap k) (hK : (k : ℝ) < Ln / Ld * l ^ 2 / 2) (s : ∀ N, State N) :
    Tendsto (fun N => volume {z | z ∈ cube N ∧ ∃ S : Finset (Fin N), S.card = k ∧
      c * Real.sqrt (Real.log N) * sigN N < phi z (s N) S}) atTop (𝓝 0) := by
  have hy := te_ev_y k hlc
  -- the functions `g_C`
  have hex : ∀ C : List (List Bool), ∃ g : ℕ → ℝ, C ∈ reps → ((∀ N, 0 ≤ g N) ∧
      Tendsto (fun N : ℕ => (N : ℝ) ^ k * g N) atTop (𝓝 0) ∧
      ∀ᶠ N : ℕ in atTop, ∀ (e : Fin k ↪ Fin N) (u0 : Fin (2 ^ k)),
        cubeM N {w | cd_region k C (te_e k N) (te_y k c N) (te_sh u0 (te_xi e.injective w))} ≤
          ENNReal.ofReal (g N)) := by
    intro C
    by_cases hC : C ∈ reps
    · obtain ⟨g, hg⟩ := te_region_prob hLd (hcov C hC) hl hy hK
      exact ⟨g, fun _ => hg⟩
    · exact ⟨fun _ => 0, fun h => absurd h hC⟩
  choose g hg using hex
  set R := reps.toFinset with hR
  set T : ℕ → ℝ := fun N => ∑ C ∈ R, (2 : ℝ) ^ k * ((N : ℝ) ^ k * g C N) with hT
  have hT0 : Tendsto T atTop (𝓝 0) := by
    have h := tendsto_finsetSum R fun C hC =>
      ((hg C (List.mem_toFinset.1 hC)).2.1.const_mul ((2 : ℝ) ^ k))
    simpa [mul_zero, sum_const_zero] using h
  have hreg : Tendsto (fun N => cubeM N (te_regBad k N c reps)) atTop (𝓝 0) := by
    have hlim' : Tendsto (fun N => ENNReal.ofReal (T N)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]; exact ENNReal.tendsto_ofReal hT0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
      (Eventually.of_forall fun _ => bot_le) ?_
    have hall : ∀ᶠ N : ℕ in atTop, ∀ C ∈ R, ∀ (e : Fin k ↪ Fin N) (u0 : Fin (2 ^ k)),
        cubeM N {w | cd_region k C (te_e k N) (te_y k c N) (te_sh u0 (te_xi e.injective w))} ≤
          ENNReal.ofReal (g C N) :=
      (Filter.eventually_all_finset R).2 fun C hC => (hg C (List.mem_toFinset.1 hC)).2.2
    filter_upwards [hall] with N hN
    have hsub : te_regBad k N c reps ⊆ ⋃ e : Fin k ↪ Fin N, ⋃ C ∈ R, ⋃ u0 : Fin (2 ^ k),
        {w | cd_region k C (te_e k N) (te_y k c N) (te_sh u0 (te_xi e.injective w))} := by
      rintro w ⟨e, C, hC, u0, hreg⟩
      simp only [Set.mem_iUnion]
      exact ⟨e, C, List.mem_toFinset.2 hC, u0, hreg⟩
    have hgnn : ∀ C ∈ R, 0 ≤ g C N := fun C hC => (hg C (List.mem_toFinset.1 hC)).1 N
    calc cubeM N (te_regBad k N c reps)
        ≤ ∑ e : Fin k ↪ Fin N, ∑ C ∈ R, ∑ u0 : Fin (2 ^ k),
            cubeM N {w | cd_region k C (te_e k N) (te_y k c N)
              (te_sh u0 (te_xi e.injective w))} := by
          refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans
            (Finset.sum_le_sum fun e _ => ?_))
          exact (measure_biUnion_finset_le _ _).trans
            (Finset.sum_le_sum fun C _ => measure_iUnion_fintype_le _ _)
      _ ≤ ∑ _e : Fin k ↪ Fin N, ∑ C ∈ R, ∑ _u0 : Fin (2 ^ k), ENNReal.ofReal (g C N) :=
          Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun C hC => Finset.sum_le_sum
            fun u0 _ => hN C hC e u0
      _ = ∑ _e : Fin k ↪ Fin N, ENNReal.ofReal (∑ C ∈ R, (2 : ℝ) ^ k * g C N) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg fun C hC => by have := hgnn C hC; positivity]
          refine Finset.sum_congr rfl fun C hC => ?_
          have h2k : ((Fintype.card (Fin (2 ^ k)) : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ k) := by
            rw [Fintype.card_fin, ← ENNReal.ofReal_natCast]; push_cast; rfl
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h2k,
            ← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal ((Fintype.card (Fin k ↪ Fin N) : ℝ) *
            ∑ C ∈ R, (2 : ℝ) ^ k * g C N) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (T N) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hT]
          simp only
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun C hC => ?_
          have := te_card_emb k N
          have : 0 ≤ (2 : ℝ) ^ k * g C N := by have := hgnn C hC; positivity
          nlinarith
  -- the inclusion
  have hflip_field : Tendsto (fun N => volume {z | z ∈ cube N ∧
      flipP (s N) z ∈ te_fieldBad k N}) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (te_tendsto_fieldBad k)
      (fun _ => bot_le) fun N => te_volume_flip_le (s N) (fun w => w ∈ te_fieldBad k N)
  have hflip_reg : Tendsto (fun N => volume {z | z ∈ cube N ∧
      flipP (s N) z ∈ te_regBad k N c reps}) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hreg
      (fun _ => bot_le) fun N => te_volume_flip_le (s N) (fun w => w ∈ te_regBad k N c reps)
  have heffv : Tendsto (fun N => volume (te_effBad k N (s N))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (te_tendsto_effBad k hk s) (fun _ => bot_le) fun N => ?_
    have hsub : te_effBad k N (s N) ⊆ cube N ∩ te_effBad k N (s N) := fun z hz =>
      ⟨fun r j => Set.Ioo_subset_Icc_self (hz.1 r j), hz⟩
    exact (measure_mono hsub).trans (volume_cube_inter _).le
  have hsum := ((hflip_field.add heffv).add hflip_reg)
  rw [add_zero, add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [te_ev_three_eta k] with N h3
  have hsub : {z | z ∈ cube N ∧ ∃ S : Finset (Fin N), S.card = k ∧
      c * Real.sqrt (Real.log N) * sigN N < phi z (s N) S} ⊆
      (cube N \ openCube N) ∪ {z | z ∈ cube N ∧ flipP (s N) z ∈ te_fieldBad k N} ∪
        te_effBad k N (s N) ∪ {z | z ∈ cube N ∧ flipP (s N) z ∈ te_regBad k N c reps} := by
    rintro z ⟨hz, S, hSk, hphi⟩
    by_cases ho : z ∈ openCube N
    · by_cases hf : flipP (s N) z ∈ te_fieldBad k N
      · exact Or.inl (Or.inl (Or.inr ⟨hz, hf⟩))
      · by_cases he : z ∈ te_effBad k N (s N)
        · exact Or.inl (Or.inr he)
        · exact Or.inr ⟨hz, te_mem_regBad hc ho hSk hc0 h3 hf he hphi⟩
    · exact Or.inl (Or.inl (Or.inl ⟨hz, ho⟩))
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  refine (measure_union_le _ _).trans ?_
  rw [volume_cube_diff_openCube, zero_add]

end

end Census
end IIT
