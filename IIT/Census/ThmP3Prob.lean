/-
Census: the events of the second moment method for triples and their probabilities at fixed `N`.

For a 3-set `S` with increasing ordering `e`, the event `tp_A s y S` is: the difference field of
`e` lies within `1` (sup norm) of `y Δz`, and the effect box of `S` holds.
* `tp_A_low`: removing the block of `s` (independence, Lindeberg, `ThmP3Diff`) its probability is at
  least `p_E (G₁(B(yΔz, 1 - 16τ/σ - ε)) - err) - P(¬g2)`;
* `tp_AA0_up`: for disjoint `S, S'` the probability of both is at most
  `p_E² (G₁(B(yΔz, 1 + 128τ/σ + ε))² + err) + P(¬g2)` (independent differences, `tp_G2_zero_ball`);
* `tp_AA_up`: for `S, S'` sharing `m = 1, 2` units the probability of both field events is at most
  `exp(-J (y - 3(1 + ε))² / 2) + err` with `J = 13, 11` (half-space certificates).
-/
import IIT.Census.ThmP3Box2

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

noncomputable section

variable {N : ℕ}

/-- The centre `y Δz`. -/
def tp_cen (y : ℝ) : Fin (3 * 2 ^ 3) → ℝ := fun p => y * tp_Dz p

/-- The field event of a triple. -/
def tp_E (y : ℝ) (S : Finset (Fin N)) (hS : S.card = 3) : Set (Param N) :=
  {w | tp_dfld (tp_ord S hS) w ∈ tp_ball (tp_cen y) 1}

/-- The event of a triple: field event and effect box. -/
def tp_A (s : State N) (y : ℝ) (S : Finset (Fin N)) (hS : S.card = 3) : Set (Param N) :=
  tp_E y S hS ∩ tp_boxW s S

lemma tp_measurable_fld {e : Fin 3 → Fin N} (he : Function.Injective e) :
    Measurable (tp_fld e) := by
  have : tp_fld e = fun w => ∑ β, bg_sX he β w := funext fun w => (tp_fld_sum he w).symm
  rw [this]
  exact Finset.measurable_sum _ fun β _ => bg_measurable_X _ _ _ _ β

lemma tp_measurable_dfld {e : Fin 3 → Fin N} (he : Function.Injective e) :
    Measurable (tp_dfld e) :=
  (measurable_tp_Dif _).comp (tp_measurable_fld he)

lemma tp_measurableSet_E (y : ℝ) (S : Finset (Fin N)) (hS : S.card = 3) :
    MeasurableSet (tp_E y S hS) :=
  tp_measurable_dfld (tp_ord_inj S hS) (tp_measurableSet_ball _ _)

lemma tp_measurableSet_A (s : State N) (y : ℝ) (S : Finset (Fin N)) (hS : S.card = 3) :
    MeasurableSet (tp_A s y S hS) :=
  (tp_measurableSet_E y S hS).inter (tp_measurableSet_boxW s S)

lemma tp_real_not_g2 : (cubeM N).real {w : Param N | ¬ ∀ i r, Qw w i r ≤ tauN N} ≤ fg2 N :=
  ps_real_not_g2

/-! ### One triple -/

lemma tp_abs_Dif_sub {d : ℕ} (b : Fin d → Fin d) {x x' : Fin d → ℝ} {c : ℝ}
    (h : ∀ p, |x p - x' p| ≤ c) (p : Fin d) : |tp_Dif b x p - tp_Dif b x' p| ≤ 2 * c := by
  have h1 := h p
  have h2 := h (b p)
  rw [abs_le] at h1 h2 ⊢
  simp only [tp_Dif]
  constructor <;> linarith

/-- **Lower bound for one triple.** -/
theorem tp_A_low (s : State N) (S : Finset (Fin N)) (hS : S.card = 3)
    (hB : 2 ≤ bg_sB (tp_ord S hS)) (y : ℝ) :
    tp_pE * ((tp_G1 3).real (tp_ball (tp_cen y) (1 - 16 * tauN N / sigN N - ps_eps N)) -
      tp_err (tp_E2s 3) (tp_E3s 3) N) - fg2 N ≤ (cubeM N).real (tp_A s y S hS) := by
  set e := tp_ord S hS
  have he : Function.Injective e := tp_ord_inj S hS
  have hU : bg_U e = S := tp_U_ord S hS
  set sh := 16 * tauN N / sigN N with hsh
  set R := {w : Param N | tp_restD 3 he s w ∈ tp_ball (tp_cen y) (1 - sh)} with hR
  have hε := ps_eps_pos N
  -- Lindeberg
  have hlow : (tp_G1 3).real (tp_ball (tp_cen y) (1 - sh - ps_eps N)) -
      tp_err (tp_E2s 3) (tp_E3s 3) N ≤ (cubeM N).real R := by
    have h1 := tp_boxF1_le_real (μ := cubeM N) (measurable_tp_restD 3 he s) (tp_cen y) (1 - sh) hε
    have h2 := tp_real_le_boxF1 (μ := tp_G1 3) measurable_id (tp_cen y) (1 - sh) hε
    have h3 := tp_compare_single 3 he s hB (tp_cen y) (1 - sh) 1
    rw [abs_le] at h3
    simp only [Set.preimage_id] at h2
    have h1' : ∫ w, tp_boxF (tp_cen y) (1 - sh) (ps_eps N) 1 (tp_restD 3 he s w) ∂cubeM N ≤
        (cubeM N).real R := h1
    have h2' : (tp_G1 3).real (tp_ball (tp_cen y) (1 - sh - ps_eps N)) ≤
        ∫ x, tp_boxF (tp_cen y) (1 - sh) (ps_eps N) 1 x ∂(tp_G1 3) := h2
    linarith [h3.1]
  -- independence of the box and the remaining blocks
  have hbox_eq := tp_box_rows he (bg_bits_inj 3) (Fintype.card_fin _) s (tp_T s S)
    (fun r j hr => tp_T_univ (hU ▸ subset_refl S) r j hr)
  have hY : MeasurableSet {y' : Fin (2 ^ 3) → Fin N → ℝ | ∀ u j, y' u j ∈
      tp_T s S (bg_eqv (bg_bits 3) he (bg_bits_inj 3) (Fintype.card_fin _)
        (((bg_eqv (bg_bits 3) he (bg_bits_inj 3) (Fintype.card_fin _)).symm s).1, u)) j} :=
    ps_measurableSet_rows _ fun u j => tp_measurableSet_T s S _ j
  have hO : MeasurableSet {x : Fin (bg_sB e - 1) → Fin (3 * 2 ^ 3) → ℝ |
      tp_Dif (tp_base 3) (∑ b, x b) ∈ tp_ball (tp_cen y) (1 - sh)} :=
    ((measurable_tp_Dif _).comp (Finset.measurable_sum _ fun b _ => measurable_pi_apply b))
      (tp_measurableSet_ball _ _)
  have hind := (bg_s_indep_rest he s).measure_inter_preimage_eq_mul _ _ hY hO
  have eR : R = bg_sXr he s ⁻¹' {x | tp_Dif (tp_base 3) (∑ b, x b) ∈ tp_ball (tp_cen y) (1 - sh)} :=
    rfl
  have hmul : (cubeM N).real (tp_boxW s S ∩ R) = tp_pE * (cubeM N).real R := by
    rw [measureReal_def, measureReal_def, eR, tp_boxW, hbox_eq]
    erw [hind]
    rw [ENNReal.toReal_mul]
    congr 1
    have := tp_real_boxW s hS
    rw [measureReal_def, tp_boxW, hbox_eq] at this
    exact this
  -- the box and the rest event give the event, on `g2`
  have hsub : tp_boxW s S ∩ R ⊆ tp_A s y S hS ∪ {w : Param N | ¬ ∀ i r, Qw w i r ≤ tauN N} := by
    rintro w ⟨hb, hRw⟩
    by_cases hg : ∀ i r, Qw w i r ≤ tauN N
    · refine Or.inl ⟨fun p => ?_, hb⟩
      have hclose : ∀ q, |tp_fld e w q - (∑ b, bg_sXr he s w b) q| ≤ 8 * tauN N / sigN N := by
        intro q
        have := bg_s_abs_sub_rest_le he s hg q
        rw [tp_fld_sum he w] at this
        norm_num at this ⊢
        exact this
      have h1 := tp_abs_Dif_sub (tp_base 3) hclose p
      have h2 := hRw p
      show |tp_Dif (tp_base 3) (tp_fld e w) p - tp_cen y p| ≤ 1
      have hsh2 : sh = 2 * (8 * tauN N / sigN N) := by rw [hsh]; ring
      rw [abs_le] at h1 h2 ⊢
      simp only [tp_restD] at h2
      constructor <;> linarith
    · exact Or.inr hg
  have h1 : (cubeM N).real (tp_boxW s S ∩ R) ≤ (cubeM N).real (tp_A s y S hS) + fg2 N :=
    (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
      (add_le_add le_rfl tp_real_not_g2))
  have hp := tp_pE_pos
  rw [hmul] at h1
  nlinarith [mul_le_mul_of_nonneg_left hlow hp.le]

/-! ### Two disjoint triples -/

lemma tp_join_ball {c c' x x' : Fin (3 * 2 ^ 3) → ℝ} {r : ℝ} (hx : x ∈ tp_ball c r)
    (hx' : x' ∈ tp_ball c' r) : tp_join 3 x x' ∈ tp_ball (tp_join 3 c c') r := by
  intro P
  simp only [tp_join]
  split_ifs
  · exact hx _
  · exact hx' _

/-- **Upper bound for two disjoint triples.** -/
theorem tp_AA0_up (s : State N) {S S' : Finset (Fin N)} (hS : S.card = 3) (hS' : S'.card = 3)
    (hd : Disjoint S S') (hB : 2 ≤ bg_jB (tp_ord S hS) (tp_ord S' hS') 0) (y : ℝ) :
    (cubeM N).real (tp_A s y S hS ∩ tp_A s y S' hS') ≤
      tp_pE ^ 2 * ((tp_G1 3).real (tp_ball (tp_cen y) (1 + 128 * tauN N / sigN N + ps_eps N)) ^ 2
        + tp_err (tp_E2j 3 0) (tp_E3j 3 0) N) + fg2 N := by
  set e0 := tp_ord S hS
  set e1 := tp_ord S' hS'
  have h : bg_JPair 3 0 e0 e1 := tp_jpair0 hS hS' hd
  set sh := 128 * tauN N / sigN N with hsh
  set c2 := tp_join 3 (tp_cen y) (tp_cen y)
  set R := {w : Param N | tp_restDJ 3 h s w ∈ tp_ball c2 (1 + sh)} with hR
  have hε := ps_eps_pos N
  -- Lindeberg
  have hup : (cubeM N).real R ≤
      (tp_G1 3).real (tp_ball (tp_cen y) (1 + sh + ps_eps N)) ^ 2 +
        tp_err (tp_E2j 3 0) (tp_E3j 3 0) N := by
    have h1 := tp_real_le_boxF0 (μ := cubeM N) (measurable_tp_restDJ 3 h s) c2 (1 + sh) hε
    have h2 := tp_boxF0_le_real (μ := tp_G2 3 0) measurable_id c2 (1 + sh) hε
    have h3 := tp_compare_rest 3 h s hB c2 (1 + sh) 0
    have h4 := tp_G2_zero_ball 3 (tp_cen y) (tp_cen y) (1 + sh + ps_eps N)
    simp only [Set.preimage_id, id] at h2
    rw [abs_le] at h3
    have h1' : (cubeM N).real R ≤
        ∫ w, tp_boxF c2 (1 + sh) (ps_eps N) 0 (tp_restDJ 3 h s w) ∂cubeM N := h1
    rw [h4, ← sq] at h2
    linarith [h3.2]
  -- the boxes as events of the superblock rows
  have hU0 : bg_U e0 = S := tp_U_ord S hS
  have hU1 : bg_U e1 = S' := tp_U_ord S' hS'
  have hSU : S ⊆ bg_U (bg_eU e0 e1 0) := hU0 ▸ bg_U0_sub h
  have hS'U : S' ⊆ bg_U (bg_eU e0 e1 0) := hU1 ▸ bg_U1_sub h
  have hbox_eq := tp_box_rows (bg_eU_inj h) (bg_jbits_inj h.1) (bg_card_ρ h.1) s
    (fun r j => tp_T s S r j ∩ tp_T s S' r j)
    (fun r j hr => by rw [tp_T_univ hSU r j hr, tp_T_univ hS'U r j hr, Set.univ_inter])
  have hinter : tp_boxW s S ∩ tp_boxW s S' =
      {w : Param N | ∀ r j, w r j ∈ tp_T s S r j ∩ tp_T s S' r j} := by
    ext w
    simp only [tp_boxW, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h r j => ⟨h.1 r j, h.2 r j⟩, fun h => ⟨fun r j => (h r j).1, fun r j => (h r j).2⟩⟩
  have hY : MeasurableSet {y' : gg_ρ 3 0 → Fin N → ℝ | ∀ u j, y' u j ∈
      tp_T s S (bg_eqv (bg_jbits 3 0) (bg_eU_inj h) (bg_jbits_inj h.1) (bg_card_ρ h.1)
        (((bg_eqv (bg_jbits 3 0) (bg_eU_inj h) (bg_jbits_inj h.1) (bg_card_ρ h.1)).symm s).1, u)) j ∩
      tp_T s S' (bg_eqv (bg_jbits 3 0) (bg_eU_inj h) (bg_jbits_inj h.1) (bg_card_ρ h.1)
        (((bg_eqv (bg_jbits 3 0) (bg_eU_inj h) (bg_jbits_inj h.1) (bg_card_ρ h.1)).symm s).1, u)) j} :=
    ps_measurableSet_rows _ fun u j =>
      (tp_measurableSet_T s S _ j).inter (tp_measurableSet_T s S' _ j)
  have hO : MeasurableSet {x : Fin (bg_jB e0 e1 0 - 1) → Fin (2 * (3 * 2 ^ 3)) → ℝ |
      tp_Dif (tp_baseJ 3) (∑ b, x b) ∈ tp_ball c2 (1 + sh)} :=
    ((measurable_tp_Dif _).comp (Finset.measurable_sum _ fun b _ => measurable_pi_apply b))
      (tp_measurableSet_ball _ _)
  have hind := (bg_j_indep_rest h s).measure_inter_preimage_eq_mul _ _ hY hO
  have eR : R = bg_jXr h s ⁻¹' {x | tp_Dif (tp_baseJ 3) (∑ b, x b) ∈ tp_ball c2 (1 + sh)} := rfl
  have hmul : (cubeM N).real ((tp_boxW s S ∩ tp_boxW s S') ∩ R) =
      tp_pE ^ 2 * (cubeM N).real R := by
    rw [measureReal_def, measureReal_def, eR, hinter, hbox_eq]
    erw [hind]
    rw [ENNReal.toReal_mul]
    congr 1
    have := tp_real_boxW_inter s hS hS' hd
    rw [measureReal_def, hinter, hbox_eq] at this
    exact this
  -- on `g2` the two events give the rest event
  have hsub : tp_A s y S hS ∩ tp_A s y S' hS' ⊆
      ((tp_boxW s S ∩ tp_boxW s S') ∩ R) ∪ {w : Param N | ¬ ∀ i r, Qw w i r ≤ tauN N} := by
    rintro w ⟨⟨hE, hb⟩, ⟨hE', hb'⟩⟩
    by_cases hg : ∀ i r, Qw w i r ≤ tauN N
    · refine Or.inl ⟨⟨hb, hb'⟩, fun P => ?_⟩
      have hclose : ∀ Q, |(∑ b, bg_jXs h w b) Q - (∑ b, bg_jXr h s w b) Q| ≤
          64 * tauN N / sigN N := by
        intro Q
        have := bg_j_abs_sub_rest_le h s hg Q
        rw [← bg_j_sum_Xs h w] at this
        norm_num at this ⊢
        exact this
      have h1 := tp_abs_Dif_sub (tp_baseJ 3) hclose P
      have hfull : tp_fullDJ 3 h w ∈ tp_ball c2 1 := by
        rw [tp_fullDJ_eq]
        exact tp_join_ball hE hE'
      have h2 := hfull P
      have hsh2 : sh = 2 * (64 * tauN N / sigN N) := by rw [hsh]; ring
      show |tp_Dif (tp_baseJ 3) (∑ b, bg_jXr h s w b) P - c2 P| ≤ 1 + sh
      simp only [tp_fullDJ] at h2
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith
    · exact Or.inr hg
  have h1 : (cubeM N).real (tp_A s y S hS ∩ tp_A s y S' hS') ≤
      tp_pE ^ 2 * (cubeM N).real R + fg2 N := by
    rw [← hmul]
    exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
      (add_le_add le_rfl tp_real_not_g2))
  have hp : 0 ≤ tp_pE ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hup hp]

/-! ### Two triples sharing units -/

/-- Half-space tail with a certified rate, including the degenerate case. -/
lemma tp_tail {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Fin d → ι → ℝ)
    (v : Fin d → ℝ) {Sr y' J : ℝ} (hSr : 0 < Sr) (hy' : 0 < y') (_hJ0 : 0 ≤ J)
    (hJ : J * gg_quad (gg_cov A) v ≤ Sr ^ 2) :
    (gg_law A).real {x | Sr * y' ≤ ∑ p, v p * x p} ≤ Real.exp (-(J * y' ^ 2) / 2) := by
  have hh : 0 < Sr * y' := mul_pos hSr hy'
  rcases (gg_quad_nonneg A v).eq_or_lt with hq | hq
  · have hmeas : Measurable (fun x : Fin d → ℝ => ∑ p, v p * x p) := by fun_prop
    have hset : {x : Fin d → ℝ | Sr * y' ≤ ∑ p, v p * x p}
        = (fun x : Fin d → ℝ => ∑ p, v p * x p) ⁻¹' Set.Ici (Sr * y') := rfl
    rw [hset, ← map_measureReal_apply hmeas measurableSet_Ici, gg_law_functional, ← hq]
    simp only [Real.toNNReal_zero, gaussianReal_zero_var]
    rw [measureReal_def, Measure.dirac_apply' _ measurableSet_Ici]
    simp only [Set.indicator, Set.mem_Ici]
    rw [ite_eq_right (not_le.2 hh)]
    simp only [ENNReal.toReal_zero]
    positivity
  · refine (gg_law_halfspace_le A v hh).trans (Real.exp_le_exp.2 ?_)
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have : J * y' ^ 2 * gg_quad (gg_cov A) v ≤ Sr ^ 2 * y' ^ 2 := by
      have := mul_le_mul_of_nonneg_right hJ (sq_nonneg y')
      linarith
    nlinarith

/-- **Upper bound for two triples sharing units**, through a half-space certificate. -/
theorem tp_AA_up {m J : ℕ} (hm : m ≤ 3) {S S' : Finset (Fin N)} (hS : S.card = 3)
    (hS' : S'.card = 3) {σ0 σ1 : Equiv.Perm (Fin 3)}
    (h : bg_JPair 3 m (tp_ord S hS ∘ σ0) (tp_ord S' hS' ∘ σ1))
    (hB : 2 ≤ bg_jB (tp_ord S hS ∘ σ0) (tp_ord S' hS' ∘ σ1) m) {v : List ℤ}
    (hv : tp_hcheck m J 1 3 (tp_pl σ0) (tp_pl σ1) v = true) {y : ℝ}
    (hy : 3 * (1 + ps_eps N) < y) :
    (cubeM N).real (tp_E y S hS ∩ tp_E y S' hS') ≤
      Real.exp (-(J * (y - 3 * (1 + ps_eps N)) ^ 2) / 2) + tp_err (tp_E2j 3 m) (tp_E3j 3 m) N := by
  set o := tp_ord S hS
  set o' := tp_ord S' hS'
  have ho := tp_ord_inj S hS
  have ho' := tp_ord_inj S' hS'
  set c2 := tp_join 3 (fun p => y * tp_Dz (tp_rel σ0 p)) (fun p => y * tp_Dz (tp_rel σ1 p))
  have hε := ps_eps_pos N
  have hsub : tp_E y S hS ∩ tp_E y S' hS' ⊆ {w | tp_fullDJ 3 h w ∈ tp_ball c2 1} := by
    rintro w ⟨hE, hE'⟩
    simp only [Set.mem_ofPred_eq]
    rw [tp_fullDJ_eq]
    refine tp_join_ball (fun p => ?_) (fun p => ?_)
    · rw [tp_dfld_comp ho σ0]; exact hE _
    · rw [tp_dfld_comp ho' σ1]; exact hE' _
  have h1 := tp_real_le_boxF0 (μ := cubeM N) (measurable_tp_fullDJ 3 h) c2 1 hε
  have h2 := tp_boxF0_le_real (μ := tp_G2 3 m) measurable_id c2 1 hε
  have h3 := tp_compare_full 3 h hB c2 1 0
  simp only [Set.preimage_id, id] at h2
  rw [abs_le] at h3
  obtain ⟨hS0, hq, hlin⟩ := tp_hcheck_sound hm hv
  set Sr := (tp_Sv (tp_pl σ0) (tp_pl σ1) v : ℝ) / 2 ^ 24
  have hy' : 0 < y - 3 * (1 + ps_eps N) := by linarith
  have hball : tp_ball c2 (1 + ps_eps N) ⊆
      {x | Sr * (y - 3 * (1 + ps_eps N)) ≤ ∑ P, cd_vec (2 * (3 * 2 ^ 3)) v P * x P} := by
    intro x hx
    refine hlin x y (1 + ps_eps N) (by linarith) fun P => ?_
    have := hx P
    rwa [show c2 P = _ from tp_join_rel σ0 σ1 y P] at this
  have hJq : (J : ℝ) * gg_quad (gg_cov (tp_DA (tp_baseJ 3) (gg_AJ 3 m)))
      (cd_vec (2 * (3 * 2 ^ 3)) v) ≤ Sr ^ 2 := by
    rw [tp_quad_DA]
    have e : gg_cov (gg_AJ 3 m) = gg_CJ 3 m :=
      funext fun P => funext fun Q => gg_cov_AJ 3 m hm P Q
    rw [e]
    exact hq
  have htail := tp_tail (tp_DA (tp_baseJ 3) (gg_AJ 3 m)) (cd_vec (2 * (3 * 2 ^ 3)) v) hS0 hy'
    (Nat.cast_nonneg J) hJq
  have h4 : (tp_G2 3 m).real (tp_ball c2 (1 + ps_eps N)) ≤
      Real.exp (-(J * (y - 3 * (1 + ps_eps N)) ^ 2) / 2) :=
    (measureReal_mono hball).trans htail
  have h1' : (cubeM N).real {w | tp_fullDJ 3 h w ∈ tp_ball c2 1} ≤
      ∫ w, tp_boxF c2 1 (ps_eps N) 0 (tp_fullDJ 3 h w) ∂cubeM N := h1
  calc (cubeM N).real (tp_E y S hS ∩ tp_E y S' hS')
      ≤ (cubeM N).real {w | tp_fullDJ 3 h w ∈ tp_ball c2 1} := measureReal_mono hsub
    _ ≤ _ := by linarith [h3.2]

end

end Census
end IIT
