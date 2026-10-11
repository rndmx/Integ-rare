/-
Census, Theorem E: the two exceptional events.

* `te_fieldBad k N`: some ordered `k`-set has a field coordinate of modulus above `N`.  By the
  half-space bound for the coordinate functionals and a union over the at most `N^k` orderings,
  its probability tends to `0` (`te_tendsto_fieldBad`).
* `te_effBad k N s`: inside the open cube, some `k`-set has an effect side of some partition and
  some effect state in `(0, δ_N)`.  The effect side depends on the partition only through its
  profile (one of the finitely many admissible pairs of `CertDataEnum`) and on the effect state
  only through its pattern on the set, so the event is a union of at most
  `N^k · |cd_gen k| · 2^k` events, each of probability at most `k a_N + ρ_N + 4^k b_N / ρ_N`
  (`te_eff_le`), and its probability tends to `0` (`te_tendsto_effBad`).
-/
import IIT.Census.ThmEAsymp
import IIT.Census.ThmEEff
import IIT.Census.CertDataEnum

namespace IIT
namespace Census

open MeasureTheory Finset Filter Topology ENNReal

noncomputable section

variable {N k : ℕ}

/-! ### Generalities -/

lemma te_card_emb (k N : ℕ) : (Fintype.card (Fin k ↪ Fin N) : ℝ) ≤ (N : ℝ) ^ k := by
  rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
  exact_mod_cast Nat.descFactorial_le_pow N k

lemma te_le_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {A : Set α} {x : ℝ} (h : μ.real A ≤ x) : μ A ≤ ENNReal.ofReal x := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ A)]
  exact ENNReal.ofReal_le_ofReal h

lemma te_sum_ofReal {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, ENNReal.ofReal (f i) = ENNReal.ofReal (∑ i ∈ s, f i) :=
  (ENNReal.ofReal_sum_of_nonneg hf).symm

lemma te_quad_single (p : Fin (k * 2 ^ k)) :
    gg_quad (gg_C k) (fun q => if q = p then 1 else 0) = gg_C k p p := by
  simp [gg_quad]

lemma te_quad_neg (v : Fin (k * 2 ^ k) → ℝ) :
    gg_quad (gg_C k) (fun q => -v q) = gg_quad (gg_C k) v := by
  simp [gg_quad]

lemma te_C_diag_pos (p : Fin (k * 2 ^ k)) : 0 < gg_C k p p := by
  simp only [gg_C, ite_true, mul_one]
  have := gg_c0_pos k; have := gg_c1_pos k; have := gg_c2_pos k
  linarith

lemma te_C_diag_le (p : Fin (k * 2 ^ k)) : gg_C k p p ≤ 1 := by
  simp only [gg_C, ite_true, mul_one, gg_c0, gg_c1, gg_c2]
  have h := gg_inv_pow_le k
  have h0 : (0 : ℝ) ≤ ((2 : ℝ) ^ k)⁻¹ := by positivity
  linarith

/-! ### The field event -/

/-- Some ordered `k`-set has a field coordinate of modulus above `N`. -/
def te_fieldBad (k N : ℕ) : Set (Param N) :=
  {w | ∃ e : Fin k ↪ Fin N, ∃ p, (N : ℝ) < |te_xi e.injective w p|}

/-- One coordinate exceeds `N` with probability at most `2 (exp(-(N-1)²/2) + err)`. -/
lemma te_coord_le (e : Fin k ↪ Fin N) (p : Fin (k * 2 ^ k)) (hN : 1 ≤ N) :
    cubeM N {w | (N : ℝ) < |te_xi e.injective w p|} ≤
      ENNReal.ofReal (2 * (Real.exp (-((N : ℝ) - 1) ^ 2 / 2) +
        ps_err (te_C2 k 1) (te_C3 k 1) N)) := by
  set v : Fin (k * 2 ^ k) → ℝ := fun q => if q = p then 1 else 0 with hv
  set v' : Fin (k * 2 ^ k) → ℝ := fun q => -v q with hv'
  have hav : ∀ q, |v q| = if q = p then 1 else 0 := fun q => by
    by_cases h : q = p
    · simp [hv, h]
    · simp [hv, h]
  have hsv : ∑ q, |v q| = 1 := by simp [hav]
  have hsv' : ∑ q, |v' q| = 1 := by simp only [hv', abs_neg]; exact hsv
  have hdot : ∀ w, ∑ q, v q * te_xi e.injective w q = te_xi e.injective w p := by
    intro w; simp [hv]
  have hdot' : ∀ w, ∑ q, v' q * te_xi e.injective w q = -te_xi e.injective w p := by
    intro w; simp [hv', hv]
  have hε := ps_eps_pos N
  have hε1 : ps_eps N ≤ 1 := by unfold ps_eps; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hεN : ps_eps N < N := by
    rcases eq_or_lt_of_le hε1 with h | h
    · rw [h]
      unfold ps_eps at h
      have : (99 / 100 : ℝ) ^ N < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      linarith
    · linarith
  have hq : gg_quad (gg_C k) v = gg_C k p p := te_quad_single p
  have hq' : gg_quad (gg_C k) v' = gg_C k p p := by rw [hv', te_quad_neg, hq]
  have hC0 := te_C_diag_pos (k := k) p
  have hC1 := te_C_diag_le (k := k) p
  have hexp : ∀ V, 0 < V → V ≤ 1 → Real.exp (-((N : ℝ) - ps_eps N) ^ 2 / (2 * V)) ≤
      Real.exp (-((N : ℝ) - 1) ^ 2 / 2) := by
    intro V hV0 hV1
    apply Real.exp_le_exp.2
    have h1 : ((N : ℝ) - 1) ^ 2 ≤ ((N : ℝ) - ps_eps N) ^ 2 := by
      apply pow_le_pow_left₀ (by linarith) (by linarith)
    rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have h1 := te_halfspace_le e.injective v hεN
  have h2 := te_halfspace_le e.injective v' hεN
  rw [hsv, hq] at h1
  rw [hsv', hq'] at h2
  simp_rw [hdot] at h1
  simp_rw [hdot'] at h2
  have hsub : {w | (N : ℝ) < |te_xi e.injective w p|} ⊆
      {w | (N : ℝ) ≤ te_xi e.injective w p} ∪ {w | (N : ℝ) ≤ -te_xi e.injective w p} := by
    intro w hw
    simp only [Set.mem_setOf_eq, lt_abs] at hw
    rcases hw with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hA := te_le_ofReal (μ := cubeM N) (h1.trans (add_le_add (hexp _ hC0 hC1) le_rfl))
  have hB := te_le_ofReal (μ := cubeM N) (h2.trans (add_le_add (hexp _ hC0 hC1) le_rfl))
  refine (add_le_add hA hB).trans ?_
  have hnn : 0 ≤ Real.exp (-((N : ℝ) - 1) ^ 2 / 2) + ps_err (te_C2 k 1) (te_C3 k 1) N := by
    have := ps_err_nonneg (C2 := te_C2 k 1) (C3 := te_C3 k 1) (by unfold te_C2; positivity)
      (by unfold te_C3; have := te_C3G_nonneg k; positivity) N
    positivity
  rw [← ENNReal.ofReal_add hnn hnn]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **The field event is rare.** -/
theorem te_tendsto_fieldBad (k : ℕ) :
    Tendsto (fun N => cubeM N (te_fieldBad k N)) atTop (𝓝 0) := by
  set F : ℕ → ℝ := fun N => (N : ℝ) ^ k * ((k * 2 ^ k : ℕ) *
    (2 * (Real.exp (-((N : ℝ) - 1) ^ 2 / 2) + ps_err (te_C2 k 1) (te_C3 k 1) N))) with hF
  have hlim : Tendsto F atTop (𝓝 0) := by
    have he : Tendsto (fun N : ℕ => (N : ℝ) ^ k * Real.exp (-((N : ℝ) - 1) ^ 2 / 2)) atTop
        (𝓝 0) := by
      have h := te_tendsto_geom k (q := Real.exp (-(1 / 2))) (Real.exp_pos _).le
        (by have := Real.exp_lt_exp.2 (show -(1 / 2 : ℝ) < 0 by norm_num); rwa [Real.exp_zero] at this)
        (Real.exp (1 / 2))
      refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ h
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith
    have hr := te_tendsto_err k (te_C2 k 1) (te_C3 k 1)
    have hsum := (he.add hr).const_mul ((k * 2 ^ k : ℕ) * 2 : ℝ)
    rw [add_zero, mul_zero] at hsum
    exact hsum.congr fun N => by rw [hF]; ring
  have hlim' : Tendsto (fun N => ENNReal.ofReal (F N)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]; exact ENNReal.tendsto_ofReal hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hsub : te_fieldBad k N ⊆ ⋃ e : Fin k ↪ Fin N, ⋃ p : Fin (k * 2 ^ k),
      {w | (N : ℝ) < |te_xi e.injective w p|} := by
    rintro w ⟨e, p, h⟩
    exact Set.mem_iUnion.2 ⟨e, Set.mem_iUnion.2 ⟨p, h⟩⟩
  set G := 2 * (Real.exp (-((N : ℝ) - 1) ^ 2 / 2) + ps_err (te_C2 k 1) (te_C3 k 1) N) with hG
  have hG0 : 0 ≤ G := by
    have := ps_err_nonneg (C2 := te_C2 k 1) (C3 := te_C3 k 1) (by unfold te_C2; positivity)
      (by unfold te_C3; have := te_C3G_nonneg k; positivity) N
    rw [hG]; positivity
  calc cubeM N (te_fieldBad k N)
      ≤ ∑ e : Fin k ↪ Fin N, ∑ p : Fin (k * 2 ^ k),
          cubeM N {w | (N : ℝ) < |te_xi e.injective w p|} :=
        (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans
          (Finset.sum_le_sum fun e _ => measure_iUnion_fintype_le _ _))
    _ ≤ ∑ _e : Fin k ↪ Fin N, ∑ _p : Fin (k * 2 ^ k), ENNReal.ofReal G :=
        Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun p _ => te_coord_le e p hN
    _ = ENNReal.ofReal ((Fintype.card (Fin k ↪ Fin N) : ℝ) * ((k * 2 ^ k : ℕ) * G)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h1 : ((Fintype.card (Fin k ↪ Fin N) : ℕ) : ℝ≥0∞) =
            ENNReal.ofReal (Fintype.card (Fin k ↪ Fin N) : ℝ) := (ENNReal.ofReal_natCast _).symm
        have h2 : ((k * 2 ^ k : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((k * 2 ^ k : ℕ) : ℝ) :=
          (ENNReal.ofReal_natCast _).symm
        rw [h1, h2, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (F N) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hF]
        exact mul_le_mul_of_nonneg_right (te_card_emb k N) (by positivity)

/-! ### The effect event -/

/-- Inside the open cube, some `k`-set has an effect side in `(0, δ_N)`. -/
def te_effBad (k N : ℕ) (s : State N) : Set (Param N) :=
  {z | z ∈ openCube N ∧ ∃ S : Finset (Fin N), S.card = k ∧ ∃ θ : SysPartition N S, ∃ te : State N,
    0 < sysPhiE (tpmOf z) S s θ s te ∧ sysPhiE (tpmOf z) S s θ s te < te_del k N}

lemma te_hS (e : Fin k ↪ Fin N) : ∀ x, x ∈ bg_U e ↔ ∃ i, e i = x := by
  intro x
  simp only [bg_U, mem_image, mem_univ, true_and]

/-- The realisation of an admissible pair along `e`. -/
def te_realize (e : Fin k ↪ Fin N) (g δ : List ℕ) (hv : cd_valid k g δ = true) :
    SysPartition N (bg_U e) :=
  Classical.choose (cd_realize e g δ (te_hS e) hv)

lemma te_realize_spec (e : Fin k ↪ Fin N) (g δ : List ℕ) (hv : cd_valid k g δ = true)
    (i j : Fin k) :
    e j ∈ profile (te_realize e g δ hv) (e i) ↔ cd_at (cd_profOf k g δ) i j = true :=
  Classical.choose_spec (cd_realize e g δ (te_hS e) hv) i j

/-- Two partitions with the same profile table along `e` have the same profiles. -/
lemma te_profile_eq (e : Fin k ↪ Fin N) {θ θ' : SysPartition N (bg_U e)}
    (h : ∀ i j : Fin k, e j ∈ profile θ (e i) ↔ e j ∈ profile θ' (e i)) :
    ∀ x ∈ bg_U e, profile θ x = profile θ' x := by
  intro x hx
  obtain ⟨i, rfl⟩ := (te_hS e x).1 hx
  ext y
  constructor
  · intro hy
    obtain ⟨j, rfl⟩ := (te_hS e y).1 (prof_profile_subset θ _ hy)
    exact (h i j).1 hy
  · intro hy
    obtain ⟨j, rfl⟩ := (te_hS e y).1 (prof_profile_subset θ' _ hy)
    exact (h i j).2 hy

/-- One piece of the effect event. -/
def te_effPiece (s : State N) (δ : ℝ) (e : Fin k ↪ Fin N) (x : List ℕ × List ℕ) (te : State N) :
    Set (Param N) :=
  {z | ∃ hv : cd_valid k x.1 x.2 = true, z ∈ openCube N ∧
    0 < sysPhiE (tpmOf z) (bg_U e) s (te_realize e x.1 x.2 hv) s te ∧
    sysPhiE (tpmOf z) (bg_U e) s (te_realize e x.1 x.2 hv) s te < δ}

lemma te_effBad_sub (s : State N) :
    te_effBad k N s ⊆ ⋃ e : Fin k ↪ Fin N, ⋃ x ∈ (cd_gen k).toFinset,
      ⋃ te ∈ agree (bg_U e)ᶜ s, te_effPiece s (te_del k N) e x te := by
  rintro z ⟨hz, S, hSk, θ, te, h0, h1⟩
  obtain ⟨e, hSe⟩ : ∃ e : Fin k ↪ Fin N, bg_U e = S :=
    ⟨(S.orderEmbOfFin hSk).toEmbedding, by rw [bg_U]; exact image_orderEmbOfFin_univ S hSk⟩
  subst hSe
  obtain ⟨g, δ, hv, hgδ⟩ := cd_classify e (te_hS e) θ
  set θ' := te_realize e g δ hv
  have hprof := te_profile_eq e (θ := θ) (θ' := θ') fun i j =>
    (hgδ i j).trans (te_realize_spec e g δ hv i j).symm
  have hθ : ∀ te, sysPhiE (tpmOf z) (bg_U e) s θ s te = sysPhiE (tpmOf z) (bg_U e) s θ' s te :=
    fun te => prof_sysPhiE_congr _ _ hprof s te
  set te' := merge (bg_U e) te s with hte'
  have hte : ∀ i ∈ bg_U e, te i = te' i := fun i hi => by rw [hte', merge_mem hi]
  have hte'm : te' ∈ agree (bg_U e)ᶜ s := by
    rw [mem_agree]
    intro j hj
    rw [hte', merge_not_mem (mem_compl.1 hj)]
  simp only [Set.mem_iUnion]
  refine ⟨e, (g, δ), List.mem_toFinset.2 (cd_mem_gen hv), te', hte'm, hv, hz, ?_, ?_⟩
  · rw [← sysPhiE_congr hte, ← hθ]; exact h0
  · rw [← sysPhiE_congr hte, ← hθ]; exact h1

lemma te_effPiece_le (s : State N) {δ a b ρ : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b)
    (hρ : 0 < ρ) (hδ : δ ≤ a ^ k * b) (e : Fin k ↪ Fin N) (x : List ℕ × List ℕ)
    (te : State N) :
    cubeM N (te_effPiece s δ e x te) ≤ ENNReal.ofReal (k * a + ρ + 4 ^ k * b / ρ) := by
  by_cases hv : cd_valid k x.1 x.2 = true
  · have hc : (bg_U e).card = k := bg_card_U e.injective
    have h := te_eff_le s (te_realize e x.1 x.2 hv) te ha ha1 hb hρ (δ := δ) (by rw [hc]; exact hδ)
    rw [hc] at h
    refine le_trans (measure_mono ?_) h
    rintro z ⟨hv', hz, h0, h1⟩
    exact ⟨hz, h0, h1⟩
  · have : te_effPiece s δ e x te = ∅ := by
      ext z; simp only [te_effPiece, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hv', _⟩; exact hv hv'
    rw [this, measure_empty]
    exact bot_le

/-- **The effect event is rare.** -/
theorem te_tendsto_effBad (k : ℕ) (hk : 1 ≤ k) (s : ∀ N, State N) :
    Tendsto (fun N => cubeM N (te_effBad k N (s N))) atTop (𝓝 0) := by
  set L : ℝ := ((cd_gen k).toFinset.card : ℝ)
  set a : ℕ → ℝ := fun N => (1 - 1 / (20 * k : ℝ)) ^ N with ha
  set b : ℕ → ℝ := fun N => (9 / 10 : ℝ) ^ N with hb
  set ρ : ℕ → ℝ := fun N => (19 / 20 : ℝ) ^ N with hρ
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq0 : (0 : ℝ) ≤ 1 - 1 / (20 * k : ℝ) := by
    have : 1 / (20 * k : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have hq1 : 1 - 1 / (20 * k : ℝ) < 1 := by
    have : 0 < 1 / (20 * k : ℝ) := by positivity
    linarith
  set F : ℕ → ℝ := fun N => (N : ℝ) ^ k * (L * 2 ^ k * (k * a N + ρ N + 4 ^ k * b N / ρ N))
    with hF
  have hbr : ∀ N : ℕ, b N / ρ N = (18 / 19 : ℝ) ^ N := by
    intro N; rw [hb, hρ, ← div_pow]; norm_num
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h1 := te_tendsto_geom k hq0 hq1 (L * 2 ^ k * k)
    have h2 := te_tendsto_geom k (q := 19 / 20) (by norm_num) (by norm_num) (L * 2 ^ k)
    have h3 := te_tendsto_geom k (q := 18 / 19) (by norm_num) (by norm_num) (L * 2 ^ k * 4 ^ k)
    have hs := (h1.add h2).add h3
    rw [add_zero, add_zero] at hs
    refine hs.congr fun N => ?_
    rw [hF]; simp only
    rw [mul_div_assoc, hbr]
    ring
  have hlim' : Tendsto (fun N => ENNReal.ofReal (F N)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]; exact ENNReal.tendsto_ofReal hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [te_ev_del k hk] with N hδ
  have hpiece : ∀ e x te, cubeM N (te_effPiece (s N) (te_del k N) e x te) ≤
      ENNReal.ofReal (k * a N + ρ N + 4 ^ k * b N / ρ N) :=
    fun e x te => te_effPiece_le (s N) (by positivity) (pow_le_one₀ hq0 hq1.le) (by positivity)
      (by positivity) hδ e x te
  set G := k * a N + ρ N + 4 ^ k * b N / ρ N with hG
  have hG0 : 0 ≤ G := by positivity
  have hagree : ∀ e : Fin k ↪ Fin N, ((agree (bg_U e)ᶜ (s N)).card : ℝ) = 2 ^ k := by
    intro e
    rw [card_agree, card_compl, Fintype.card_fin, bg_card_U e.injective]
    have := bg_le_of_inj e.injective
    rw [show N - (N - k) = k by omega]
    push_cast; ring
  calc cubeM N (te_effBad k N (s N))
      ≤ ∑ e : Fin k ↪ Fin N, ∑ x ∈ (cd_gen k).toFinset, ∑ te ∈ agree (bg_U e)ᶜ (s N),
          cubeM N (te_effPiece (s N) (te_del k N) e x te) := by
        refine (measure_mono (te_effBad_sub (s N))).trans ((measure_iUnion_fintype_le _ _).trans
          (Finset.sum_le_sum fun e _ => ?_))
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
        exact measure_biUnion_finset_le _ _
    _ ≤ ∑ e : Fin k ↪ Fin N, ∑ _x ∈ (cd_gen k).toFinset, ∑ _te ∈ agree (bg_U e)ᶜ (s N),
          ENNReal.ofReal G :=
        Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun x _ => Finset.sum_le_sum
          fun te _ => hpiece e x te
    _ = ∑ _e : Fin k ↪ Fin N, ENNReal.ofReal (L * (2 ^ k * G)) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        have h1 : ((agree (bg_U e)ᶜ (s N)).card : ℝ≥0∞) = ENNReal.ofReal (2 ^ k) := by
          rw [← hagree e, ENNReal.ofReal_natCast]
        have h2 : (((cd_gen k).toFinset.card : ℕ) : ℝ≥0∞) = ENNReal.ofReal L := by
          rw [ENNReal.ofReal_natCast]
        simp only [Finset.sum_const, nsmul_eq_mul, h1, h2]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal ((Fintype.card (Fin k ↪ Fin N) : ℝ) * (L * (2 ^ k * G))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (F N) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hF]
        simp only
        rw [← hG]
        have := te_card_emb k N
        have hL : 0 ≤ L := Nat.cast_nonneg _
        nlinarith [mul_le_mul_of_nonneg_right this (show 0 ≤ L * (2 ^ k * G) by positivity)]

end

end Census
end IIT
