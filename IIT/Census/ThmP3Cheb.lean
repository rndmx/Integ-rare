/-
Census: the second moment bound over all triples at fixed `N`.

`X = ∑_S 1{A_S}` over all 3-sets `S`.  The first moment is at least `M a` (`tp_A_low`), and the
second moment splits by the overlap of the two triples: disjoint pairs (`tp_AA0_up`), pairs sharing
one unit (at most `3 N²` per triple, certificate rate `13`) and pairs sharing two units (at most
`9 N` per triple, rate `11`), `tp_AA_up`.  Chebyshev's inequality gives `tp_bound`.
-/
import IIT.Census.ThmP3Asym

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

noncomputable section

variable {N : ℕ}

/-! ### Chebyshev's inequality for finitely many events -/

/-- **Second moment bound** for a finite family of events. -/
theorem tp_cheb {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) {e0 U : ℝ} (he0 : 0 < e0)
    (he : e0 ≤ ∑ i, μ.real (A i)) (hU : ∑ i, ∑ j ∈ univ.erase i, μ.real (A i ∩ A j) ≤ U) :
    μ.real {ω | ∀ i, ω ∉ A i} ≤ 1 / e0 + U / e0 ^ 2 - 1 := by
  set e := ∑ i, μ.real (A i) with he_def
  have hepos : 0 < e := he0.trans_le he
  set f : ι → Ω → ℝ := fun i => (A i).indicator 1 with hf
  have hfi : ∀ i, Integrable (f i) μ := fun i => (integrable_const (1 : ℝ)).indicator (hA i)
  have hff : ∀ i j, (fun ω => f i ω * f j ω) = (A i ∩ A j).indicator 1 := fun i j => by
    funext ω
    simp only [hf, Set.inter_indicator_one, Pi.mul_apply]
  have hgi : ∀ i j, Integrable (fun ω => f i ω * f j ω) μ := fun i j => by
    rw [hff]
    exact (integrable_const (1 : ℝ)).indicator ((hA i).inter (hA j))
  set X : Ω → ℝ := fun ω => ∑ i, f i ω with hX
  have hXi : Integrable X μ := integrable_finsetSum _ fun i _ => hfi i
  have hX2 : ∀ ω, X ω ^ 2 = ∑ i, ∑ j, f i ω * f j ω := fun ω => by
    simp only [hX, sq, Finset.sum_mul_sum]
  have hX2i : Integrable (fun ω => X ω ^ 2) μ := by
    simp_rw [hX2]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hgi i j
  have hIX : ∫ ω, X ω ∂μ = e := by
    simp only [hX]
    rw [integral_finsetSum _ fun i _ => hfi i]
    exact Finset.sum_congr rfl fun i _ => integral_indicator_one (hA i)
  have hrow : ∀ i, ∫ ω, ∑ j, f i ω * f j ω ∂μ = ∑ j, μ.real (A i ∩ A j) := fun i => by
    rw [integral_finsetSum _ fun j _ => hgi i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hff, integral_indicator_one ((hA i).inter (hA j))]
  have hIX2 : ∫ ω, X ω ^ 2 ∂μ ≤ e + U := by
    simp_rw [hX2]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hgi i j]
    simp_rw [hrow]
    have hsplit : ∀ i, ∑ j, μ.real (A i ∩ A j) =
        μ.real (A i) + ∑ j ∈ univ.erase i, μ.real (A i ∩ A j) := fun i => by
      rw [← Finset.add_sum_erase _ _ (mem_univ i), Set.inter_self]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    linarith
  set Z := {ω | ∀ i, ω ∉ A i} with hZdef
  have hZ : MeasurableSet Z := by
    have : Z = ⋂ i, (A i)ᶜ := by ext; simp [hZdef]
    rw [this]
    exact MeasurableSet.iInter fun i => (hA i).compl
  have hpt : ∀ ω, Z.indicator (1 : Ω → ℝ) ω ≤ (X ω - e) ^ 2 / e ^ 2 := fun ω => by
    by_cases hω : ω ∈ Z
    · rw [Set.indicator_of_mem hω]
      have : X ω = 0 := Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (hω i) _
      rw [this, Pi.one_apply, zero_sub, neg_sq, div_self (by positivity)]
    · rw [Set.indicator_of_notMem hω]
      positivity
  have hexp : (fun ω => (X ω - e) ^ 2 / e ^ 2) =
      fun ω => (X ω ^ 2 - 2 * e * X ω + e ^ 2) / e ^ 2 := by
    funext ω; ring
  have hint : Integrable (fun ω => (X ω - e) ^ 2 / e ^ 2) μ := by
    rw [hexp]
    exact ((hX2i.sub (hXi.const_mul _)).add (integrable_const _)).div_const _
  have hbound : μ.real Z ≤ ∫ ω, (X ω - e) ^ 2 / e ^ 2 ∂μ := by
    rw [← integral_indicator_one hZ]
    exact integral_mono ((integrable_const 1).indicator hZ) hint hpt
  have hi1 : Integrable (fun ω => X ω ^ 2 - 2 * e * X ω) μ := hX2i.sub (hXi.const_mul _)
  have hi2 : Integrable (fun ω => 2 * e * X ω) μ := hXi.const_mul _
  have hcalc : ∫ ω, (X ω - e) ^ 2 / e ^ 2 ∂μ = (∫ ω, X ω ^ 2 ∂μ - e ^ 2) / e ^ 2 := by
    rw [hexp, integral_div, integral_add hi1 (integrable_const _),
      integral_sub hX2i hi2, integral_const_mul, hIX, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    ring
  have hU0 : 0 ≤ U := le_trans (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    measureReal_nonneg) hU
  calc μ.real Z ≤ (∫ ω, X ω ^ 2 ∂μ - e ^ 2) / e ^ 2 := hbound.trans hcalc.le
    _ ≤ (e + U - e ^ 2) / e ^ 2 := by gcongr
    _ = 1 / e + U / e ^ 2 - 1 := by field_simp
    _ ≤ 1 / e0 + U / e0 ^ 2 - 1 := by gcongr

/-! ### Counting triples by overlap -/

/-- The 3-sets. -/
abbrev tp_Tri (N : ℕ) := {T : Finset (Fin N) // T.card = 3}

lemma tp_card_Tri (N : ℕ) : Fintype.card (tp_Tri N) = N.choose 3 := by
  rw [Fintype.card_finset_len, Fintype.card_fin]

lemma tp_choose_ge {N : ℕ} (hN : 6 ≤ N) : (N : ℝ) ^ 3 / 12 ≤ N.choose 3 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose N 3
  have hd : N.descFactorial 3 = N * (N - 1) * (N - 2) := by
    simp [Nat.descFactorial]; ring
  rw [hd] at h
  have h' : ((N * (N - 1) * (N - 2) : ℕ) : ℝ) = 6 * (N.choose 3 : ℝ) := by
    rw [h]; simp [Nat.factorial]
  have e1 : ((N * (N - 1) * (N - 2) : ℕ) : ℝ) = (N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_sub (by omega : 2 ≤ N)]
    ring
  rw [e1] at h'
  have hN' : (6 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

lemma tp_count1 (S : Finset (Fin N)) (hS : S.card = 3) :
    ((univ : Finset (tp_Tri N)).filter fun T => (S ∩ T.1).card = 1).card ≤ 3 * N ^ 2 := by
  set F := (univ : Finset (tp_Tri N)).filter fun T => (S ∩ T.1).card = 1
  have h1 : F.card = (F.image Subtype.val).card :=
    (card_image_of_injective _ Subtype.val_injective).symm
  have hsub : F.image Subtype.val ⊆
      (S ×ˢ (univ : Finset (Fin N)) ×ˢ (univ : Finset (Fin N))).image
        fun q => ({q.1, q.2.1, q.2.2} : Finset (Fin N)) := by
    intro T hT
    simp only [mem_image, F, mem_filter, mem_univ, true_and] at hT
    obtain ⟨⟨T, hT3⟩, h1, rfl⟩ := hT
    obtain ⟨x, hx⟩ := card_eq_one.1 h1
    have hxT : x ∈ S ∩ T := by rw [hx]; exact mem_singleton_self x
    have hc : (T.erase x).card = 2 := by rw [card_erase_of_mem (mem_inter.1 hxT).2, hT3]
    obtain ⟨y, z, _, hyz⟩ := card_eq_two.1 hc
    simp only [mem_image, mem_product, mem_univ, and_true, Prod.exists]
    refine ⟨x, y, z, (mem_inter.1 hxT).1, ?_⟩
    rw [← hyz, insert_erase (mem_inter.1 hxT).2]
  calc F.card = (F.image Subtype.val).card := h1
    _ ≤ _ := card_le_card hsub
    _ ≤ (S ×ˢ (univ : Finset (Fin N)) ×ˢ (univ : Finset (Fin N))).card := card_image_le
    _ = 3 * N ^ 2 := by simp [card_product, hS]; ring

lemma tp_count2 (S : Finset (Fin N)) (hS : S.card = 3) :
    ((univ : Finset (tp_Tri N)).filter fun T => (S ∩ T.1).card = 2).card ≤ 9 * N := by
  set F := (univ : Finset (tp_Tri N)).filter fun T => (S ∩ T.1).card = 2
  have h1 : F.card = (F.image Subtype.val).card :=
    (card_image_of_injective _ Subtype.val_injective).symm
  have hsub : F.image Subtype.val ⊆
      (S ×ˢ S ×ˢ (univ : Finset (Fin N))).image
        fun q => ({q.1, q.2.1, q.2.2} : Finset (Fin N)) := by
    intro T hT
    simp only [mem_image, F, mem_filter, mem_univ, true_and] at hT
    obtain ⟨⟨T, hT3⟩, h2, rfl⟩ := hT
    obtain ⟨x, y, _, hxy⟩ := card_eq_two.1 h2
    have hx : x ∈ S ∩ T := by rw [hxy]; simp
    have hy : y ∈ S ∩ T := by rw [hxy]; simp
    have hc : (T \ (S ∩ T)).card = 1 := by
      rw [card_sdiff_of_subset inter_subset_right, hT3, h2]
    obtain ⟨z, hz⟩ := card_eq_one.1 hc
    simp only [mem_image, mem_product, mem_univ, and_true, Prod.exists]
    refine ⟨x, y, z, ⟨(mem_inter.1 hx).1, (mem_inter.1 hy).1⟩, ?_⟩
    have : T = (S ∩ T) ∪ (T \ (S ∩ T)) := (union_sdiff_of_subset inter_subset_right).symm
    rw [this, hz, hxy]
    ext v; simp
  calc F.card = (F.image Subtype.val).card := h1
    _ ≤ _ := card_le_card hsub
    _ ≤ (S ×ˢ S ×ˢ (univ : Finset (Fin N))).card := card_image_le
    _ = 9 * N := by simp [card_product, hS]; ring

/-! ### The bound at fixed `N` -/

/-- The first-moment constant. -/
def tp_a (N : ℕ) (y : ℝ) : ℝ :=
  tp_pE * ((tp_G1 3).real (tp_ball (tp_cen y) (1 - 16 * tauN N / sigN N - ps_eps N)) -
    tp_err (tp_E2s 3) (tp_E3s 3) N) - fg2 N

/-- The bound for two disjoint triples. -/
def tp_b0 (N : ℕ) (y : ℝ) : ℝ :=
  tp_pE ^ 2 * ((tp_G1 3).real (tp_ball (tp_cen y) (1 + 128 * tauN N / sigN N + ps_eps N)) ^ 2
    + tp_err (tp_E2j 3 0) (tp_E3j 3 0) N) + fg2 N

/-- The bound for two triples sharing one unit. -/
def tp_b1 (N : ℕ) (y : ℝ) : ℝ :=
  Real.exp (-(13 * (y - 3 * (1 + ps_eps N)) ^ 2) / 2) + tp_err (tp_E2j 3 1) (tp_E3j 3 1) N

/-- The bound for two triples sharing two units. -/
def tp_b2 (N : ℕ) (y : ℝ) : ℝ :=
  Real.exp (-(11 * (y - 3 * (1 + ps_eps N)) ^ 2) / 2) + tp_err (tp_E2j 3 2) (tp_E3j 3 2) N

/-- No triple has its event. -/
def tp_Z (N : ℕ) (s : State N) (y : ℝ) : Set (Param N) :=
  {w | ∀ T : tp_Tri N, w ∉ tp_A s y T.1 T.2}

lemma tp_E2j_nonneg (m : ℕ) : 0 ≤ tp_E2j 3 m := by unfold tp_E2j; positivity

lemma tp_E3j_nonneg (m : ℕ) : 0 ≤ tp_E3j 3 m := by
  have := tp_C3G2_nonneg 3 m; unfold tp_E3j; positivity

lemma tp_E2s_nonneg : 0 ≤ tp_E2s 3 := by unfold tp_E2s; positivity

lemma tp_E3s_nonneg : 0 ≤ tp_E3s 3 := by
  have := tp_C3G1_nonneg 3; unfold tp_E3s; positivity

lemma tp_errj_nonneg (m N : ℕ) : 0 ≤ tp_err (tp_E2j 3 m) (tp_E3j 3 m) N :=
  tp_err_nonneg (tp_E2j_nonneg m) (tp_E3j_nonneg m) N

lemma tp_errs_nonneg (N : ℕ) : 0 ≤ tp_err (tp_E2s 3) (tp_E3s 3) N :=
  tp_err_nonneg tp_E2s_nonneg tp_E3s_nonneg N

lemma tp_b0_nonneg (N : ℕ) (y : ℝ) : 0 ≤ tp_b0 N y := by
  have := tp_errj_nonneg 0 N
  have := ps_fg2_nonneg N
  unfold tp_b0; positivity

lemma tp_b1_nonneg (N : ℕ) (y : ℝ) : 0 ≤ tp_b1 N y := by
  have := tp_errj_nonneg 1 N
  unfold tp_b1; positivity

lemma tp_b2_nonneg (N : ℕ) (y : ℝ) : 0 ≤ tp_b2 N y := by
  have := tp_errj_nonneg 2 N
  unfold tp_b2; positivity

lemma tp_two_le_pow {N a : ℕ} (h : a + 1 ≤ N) : 2 ≤ 2 ^ (N - a) := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (N - a) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Pairs of distinct triples.** -/
theorem tp_pair_le (hN : 7 ≤ N) (s : State N) {y : ℝ} (hy : 3 * (1 + ps_eps N) < y)
    (T T' : tp_Tri N) (hne : T ≠ T') :
    (cubeM N).real (tp_A s y T.1 T.2 ∩ tp_A s y T'.1 T'.2) ≤
      tp_b0 N y + (if (T.1 ∩ T'.1).card = 1 then tp_b1 N y else 0) +
        (if (T.1 ∩ T'.1).card = 2 then tp_b2 N y else 0) := by
  obtain ⟨S, hS⟩ := T
  obtain ⟨S', hS'⟩ := T'
  simp only
  have hb0 := tp_b0_nonneg N y
  have hb1 := tp_b1_nonneg N y
  have hb2 := tp_b2_nonneg N y
  have hsubE : tp_A s y S hS ∩ tp_A s y S' hS' ⊆ tp_E y S hS ∩ tp_E y S' hS' :=
    Set.inter_subset_inter Set.inter_subset_left Set.inter_subset_left
  have hc3 : (S ∩ S').card ≤ 3 := hS ▸ card_le_card inter_subset_left
  have hne' : S ≠ S' := fun h => hne (Subtype.ext h)
  have hc : (S ∩ S').card = 0 ∨ (S ∩ S').card = 1 ∨ (S ∩ S').card = 2 := by
    rcases Nat.lt_or_ge (S ∩ S').card 3 with h | h
    · omega
    · exfalso
      have h3 : (S ∩ S').card = 3 := le_antisymm hc3 h
      have e1 : S ∩ S' = S := eq_of_subset_of_card_le inter_subset_left (by rw [h3, hS])
      have e2 : S ∩ S' = S' := eq_of_subset_of_card_le inter_subset_right (by rw [h3, hS'])
      exact hne' (e1.symm.trans e2)
  rcases hc with h0 | h1 | h2
  · have hd : Disjoint S S' := disjoint_iff_inter_eq_empty.2 (card_eq_zero.1 h0)
    have hj := tp_jpair0 hS hS' hd
    have hB : 2 ≤ bg_jB (tp_ord S hS) (tp_ord S' hS') 0 := by
      rw [bg_jB_eq hj]; exact tp_two_le_pow (by omega)
    have := tp_AA0_up s hS hS' hd hB y
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    unfold tp_b0
    linarith
  · obtain ⟨σ0, σ1, hj⟩ := tp_jpair1 hS hS' h1
    have hB : 2 ≤ bg_jB (tp_ord S hS ∘ σ0) (tp_ord S' hS' ∘ σ1) 1 := by
      rw [bg_jB_eq hj]; exact tp_two_le_pow (by omega)
    have hv := tp_tab1_all _ (tp_pl_mem σ0) _ (tp_pl_mem σ1)
    have := tp_AA_up (by norm_num) hS hS' hj hB hv hy
    rw [ite_eq_left h1, ite_eq_right (by omega)]
    have h' := (measureReal_mono hsubE).trans this
    unfold tp_b1
    push_cast at h'
    linarith
  · obtain ⟨σ0, σ1, hj⟩ := tp_jpair2 hS hS' h2
    have hB : 2 ≤ bg_jB (tp_ord S hS ∘ σ0) (tp_ord S' hS' ∘ σ1) 2 := by
      rw [bg_jB_eq hj]; exact tp_two_le_pow (by omega)
    have hv := tp_tab2_all _ (tp_pl_mem σ0) _ (tp_pl_mem σ1)
    have := tp_AA_up (by norm_num) hS hS' hj hB hv hy
    rw [ite_eq_right (by omega), ite_eq_left h2]
    have h' := (measureReal_mono hsubE).trans this
    unfold tp_b2
    push_cast at h'
    linarith

/-- **The second moment bound at fixed `N`.** -/
theorem tp_bound (hN : 7 ≤ N) (s : State N) {y : ℝ} (hy : 3 * (1 + ps_eps N) < y)
    (ha : 0 < tp_a N y) :
    (cubeM N).real (tp_Z N s y) ≤ 1 / ((N.choose 3 : ℝ) * tp_a N y) +
      ((N.choose 3 : ℝ) * tp_b0 N y + 3 * N ^ 2 * tp_b1 N y + 9 * N * tp_b2 N y) /
        ((N.choose 3 : ℝ) * tp_a N y ^ 2) - 1 := by
  set M : ℝ := (N.choose 3 : ℝ) with hM
  have hM0 : 0 < M := by
    have := tp_choose_ge (N := N) (by omega)
    have : (0 : ℝ) < (N : ℝ) ^ 3 / 12 := by
      have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      positivity
    linarith
  have hcard : (Fintype.card (tp_Tri N) : ℝ) = M := by rw [tp_card_Tri]
  set a := tp_a N y
  set B := M * tp_b0 N y + 3 * N ^ 2 * tp_b1 N y + 9 * N * tp_b2 N y with hBdef
  have hlow : ∀ T : tp_Tri N, a ≤ (cubeM N).real (tp_A s y T.1 T.2) := by
    intro T
    have hB : 2 ≤ bg_sB (tp_ord T.1 T.2) := by
      rw [bg_sB_eq (tp_ord_inj T.1 T.2)]; exact tp_two_le_pow (by omega)
    exact tp_A_low s T.1 T.2 hB y
  have h := tp_cheb (cubeM N) (fun T : tp_Tri N => tp_A s y T.1 T.2)
    (fun T => tp_measurableSet_A s y T.1 T.2) (e0 := M * a) (U := M * B) (by positivity) ?_ ?_
  · have e : 1 / (M * a) + M * B / (M * a) ^ 2 - 1 = 1 / (M * a) + B / (M * a ^ 2) - 1 := by
      field_simp
    rw [e] at h
    exact h
  · calc M * a = ∑ _T : tp_Tri N, a := by rw [sum_const, card_univ, nsmul_eq_mul, hcard]
      _ ≤ _ := sum_le_sum fun T _ => hlow T
  · have hrow : ∀ T : tp_Tri N, ∑ T' ∈ univ.erase T,
        (cubeM N).real (tp_A s y T.1 T.2 ∩ tp_A s y T'.1 T'.2) ≤ B := by
      intro T
      have hb0 := tp_b0_nonneg N y
      have hb1 := tp_b1_nonneg N y
      have hb2 := tp_b2_nonneg N y
      calc ∑ T' ∈ univ.erase T, (cubeM N).real (tp_A s y T.1 T.2 ∩ tp_A s y T'.1 T'.2)
          ≤ ∑ T' ∈ univ.erase T, (tp_b0 N y + (if (T.1 ∩ T'.1).card = 1 then tp_b1 N y else 0) +
              (if (T.1 ∩ T'.1).card = 2 then tp_b2 N y else 0)) :=
            sum_le_sum fun T' hT' => tp_pair_le hN s hy T T' (ne_of_mem_erase hT').symm
        _ ≤ ∑ T' : tp_Tri N, (tp_b0 N y + (if (T.1 ∩ T'.1).card = 1 then tp_b1 N y else 0) +
              (if (T.1 ∩ T'.1).card = 2 then tp_b2 N y else 0)) :=
            sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun T' _ _ => by
              split_ifs <;> positivity
        _ = M * tp_b0 N y +
              ((univ : Finset (tp_Tri N)).filter fun T' => (T.1 ∩ T'.1).card = 1).card *
                tp_b1 N y +
              ((univ : Finset (tp_Tri N)).filter fun T' => (T.1 ∩ T'.1).card = 2).card *
                tp_b2 N y := by
            rw [sum_add_distrib, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, hcard,
              ← sum_filter, ← sum_filter, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
        _ ≤ B := by
            have c1 := tp_count1 T.1 T.2
            have c2 := tp_count2 T.1 T.2
            have c1' : (((univ : Finset (tp_Tri N)).filter
                fun T' => (T.1 ∩ T'.1).card = 1).card : ℝ) ≤ 3 * N ^ 2 := by exact_mod_cast c1
            have c2' : (((univ : Finset (tp_Tri N)).filter
                fun T' => (T.1 ∩ T'.1).card = 2).card : ℝ) ≤ 9 * N := by exact_mod_cast c2
            rw [hBdef]
            nlinarith [mul_le_mul_of_nonneg_right c1' hb1, mul_le_mul_of_nonneg_right c2' hb2]
    calc ∑ T : tp_Tri N, ∑ T' ∈ univ.erase T,
          (cubeM N).real (tp_A s y T.1 T.2 ∩ tp_A s y T'.1 T'.2)
        ≤ ∑ _T : tp_Tri N, B := sum_le_sum fun T _ => hrow T
      _ = M * B := by rw [sum_const, card_univ, nsmul_eq_mul, hcard]

end

end Census
end IIT
