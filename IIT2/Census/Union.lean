/-
Census of IIT 2.0: Proposition 5 for fixed `N` and threshold `L` — union bound on the
complement of the good event.
-/
import IIT2.Census.Averages

namespace IIT2

open MeasureTheory ProbabilityTheory Finset Real

variable {N : ℕ}

lemma meanW (M : Finset (Fin N)) : avg (fun x => ∫ ω, Wω M x ω ∂(μP N)) = 1 := by
  rw [avg_congr (integral_Wω M)]; exact avg_const 1

/-- Hoeffding events (large `m`). -/
def hset (t : Finset (Fin N) × Fin N × State N) : Set (Ωf N) :=
  {ω | 1 / 2000 ≤ |2 * aω t.1 t.2.1 t.2.2 ω - 1|}

/-- Chebyshev events (small `m`). -/
def cset (M : Finset (Fin N)) : Set (Ωf N) :=
  {ω | 1 / 1000 ≤ |avg (fun x => Wω M x ω) - avg (fun x => ∫ ω', Wω M x ω' ∂(μP N))|} ∪
  {ω | (N : ℝ) / 1000 ≤ |avg (fun x => GY M x ω) - avg (fun x => ∫ ω', GY M x ω' ∂(μP N))|} ∪
  {ω | (N : ℝ) / 1000 ≤ |avg (fun x => GT M x ω) - avg (fun x => ∫ ω', GT M x ω' ∂(μP N))|}

def largeT (N L : ℕ) : Finset (Finset (Fin N) × Fin N × State N) :=
  (Finset.univ.filter (fun M : Finset (Fin N) => L ≤ N - M.card)) ×ˢ (Finset.univ ×ˢ Finset.univ)

def smallF (N L : ℕ) : Finset (Finset (Fin N)) :=
  Finset.univ.filter (fun M : Finset (Fin N) => N - M.card < L)

lemma good_of_not_bad (L : ℕ) (hL : 1 ≤ L) (ω : Ωf N)
    (hH : ω ∉ ⋃ t ∈ largeT N L, hset t) (hS : ω ∉ ⋃ M ∈ smallF N L, cset M) :
    GoodA (qω ω) L := by
  have hH' : ∀ t ∈ largeT N L, ω ∉ hset t := fun t ht h =>
    hH (Set.mem_biUnion (x := t) ht h)
  have hS' : ∀ M ∈ smallF N L, ω ∉ cset M := fun M hM h =>
    hS (Set.mem_biUnion (x := M) hM h)
  have hcs : ∀ M ∈ smallF N L,
      |avg (fun x => Wω M x ω) - 1| < 1 / 1000 ∧
      |avg (fun x => GY M x ω) - avg (fun x => ∫ ω', GY M x ω' ∂(μP N))| < (N : ℝ) / 1000 ∧
      |avg (fun x => GT M x ω) - avg (fun x => ∫ ω', GT M x ω' ∂(μP N))| < (N : ℝ) / 1000 := by
    intro M hM
    have h := hS' M hM
    simp only [cset, Set.mem_union, Set.mem_setOf_eq, not_or, not_le, meanW] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  refine ⟨fun l c => ⟨clamp_nonneg _, clamp_le_one _⟩, ?_, ?_, ?_⟩
  · intro M hM l _ x
    have h := hH' (M, l, x) (by simp [largeT, hM])
    simp only [hset, Set.mem_setOf_eq, not_le] at h
    exact h.le
  · have hu : (Finset.univ : Finset (Fin N)) ∈ smallF N L := by simp [smallF]; omega
    obtain ⟨hZ, hY, -⟩ := hcs _ hu
    refine ⟨hZ.le, ?_⟩
    have hm : avg (fun x => ∫ ω', GY Finset.univ x ω' ∂(μP N)) =
        N * ((Real.log 2 - 1 / 2) / Real.log 2) := by rw [meanY_eq, mean_univ]
    rw [hm] at hY
    have hd := d0_gt
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have := (abs_lt.mp hY).1
    change 2776 / 10000 * (N : ℝ) ≤ avg (fun x => GY Finset.univ x ω)
    nlinarith
  · intro M hMu _ hm
    have hM : M ∈ smallF N L := by simp [smallF, hm]
    obtain ⟨hZ, hY, hT⟩ := hcs M hM
    refine ⟨hZ.le, ?_, ?_⟩
    · have h1 := (abs_lt.mp hY).2
      have h2 := mean_le M hMu
      rw [← meanY_eq] at h2
      change avg (fun x => GY M x ω) ≤ 1321 / 10000 * (N : ℝ)
      linarith
    · have h1 := (abs_lt.mp hT).2
      have h2 := mean_le M hMu
      rw [← meanT_eq] at h2
      change avg (fun x => GT M x ω) ≤ 1321 / 10000 * (N : ℝ)
      linarith

/-! ## Arithmetic of the Chebyshev bounds -/

lemma two_thirds_pow_le (k m : ℕ) : ((2 : ℝ) / 3) ^ k ≤ 8 ^ m * (2 / 3) ^ (k + m) := by
  rw [pow_add]
  have : (1 : ℝ) ≤ 8 ^ m * (2 / 3) ^ m := by
    rw [← mul_pow]; exact one_le_pow₀ (by norm_num)
  have h0 : (0 : ℝ) ≤ (2 / 3) ^ k := by positivity
  nlinarith

lemma boundZ (k m : ℕ) :
    ((4 : ℝ) / 3) ^ k / 2 ^ k / (1 / 1000) ^ 2 ≤ 10 ^ 6 * (8 ^ m * (2 / 3) ^ (k + m)) := by
  have : ((4 : ℝ) / 3) ^ k / 2 ^ k = (2 / 3) ^ k := by rw [← div_pow]; norm_num
  rw [this]
  have := two_thirds_pow_le k m
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

lemma boundY (k m : ℕ) (hN : 1 ≤ k + m) :
    (k : ℝ) * (k * (3 * (4 / 3) ^ k)) / 2 ^ k / ((↑(k + m) : ℝ) / 1000) ^ 2 ≤
      3 * 10 ^ 6 * (8 ^ m * (2 / 3) ^ (k + m)) := by
  have hNr : (1 : ℝ) ≤ (↑(k + m) : ℝ) := by exact_mod_cast hN
  have hk : (k : ℝ) ≤ (↑(k + m) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have e : (k : ℝ) * (k * (3 * (4 / 3) ^ k)) / 2 ^ k = 3 * k ^ 2 * (2 / 3) ^ k := by
    rw [show ((2 : ℝ) / 3) ^ k = (4 / 3) ^ k / 2 ^ k by rw [← div_pow]; norm_num]
    ring
  rw [e]
  have h23 := two_thirds_pow_le k m
  have hp : (0 : ℝ) ≤ (2 / 3) ^ k := by positivity
  rw [div_le_iff₀ (by positivity)]
  have hk2 : (k : ℝ) ^ 2 ≤ (↑(k + m) : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg k) hk 2
  have : 3 * (k : ℝ) ^ 2 * (2 / 3) ^ k ≤ 3 * (↑(k + m) : ℝ) ^ 2 * (8 ^ m * (2 / 3) ^ (k + m)) := by
    have h1 : 3 * (k : ℝ) ^ 2 * (2 / 3) ^ k ≤ 3 * (↑(k + m) : ℝ) ^ 2 * (2 / 3) ^ k := by
      nlinarith
    have h2 : 3 * (↑(k + m) : ℝ) ^ 2 * (2 / 3) ^ k ≤
        3 * (↑(k + m) : ℝ) ^ 2 * (8 ^ m * (2 / 3) ^ (k + m)) :=
      mul_le_mul_of_nonneg_left h23 (by positivity)
    linarith
  nlinarith

lemma boundT (k m : ℕ) (hN : 1 ≤ k + m) :
    (k : ℝ) * (k * (3 * 4 ^ m * (4 / 3) ^ (k + m))) / 2 ^ k / ((↑(k + m) : ℝ) / 1000) ^ 2 ≤
      3 * 10 ^ 6 * (8 ^ m * (2 / 3) ^ (k + m)) := by
  have hNr : (1 : ℝ) ≤ (↑(k + m) : ℝ) := by exact_mod_cast hN
  have hk : (k : ℝ) ≤ (↑(k + m) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have e : (4 : ℝ) ^ m * (4 / 3) ^ (k + m) / 2 ^ k = 8 ^ m * (2 / 3) ^ (k + m) := by
    rw [show ((2 : ℝ) / 3) ^ (k + m) = (4 / 3) ^ (k + m) / 2 ^ (k + m) by rw [← div_pow]; norm_num]
    rw [pow_add (2 : ℝ) k m, show (8 : ℝ) ^ m = 4 ^ m * 2 ^ m by rw [← mul_pow]; norm_num]
    field_simp
  have e2 : (k : ℝ) * (k * (3 * 4 ^ m * (4 / 3) ^ (k + m))) / 2 ^ k =
      3 * k ^ 2 * (4 ^ m * (4 / 3) ^ (k + m) / 2 ^ k) := by ring
  rw [e2, e, div_le_iff₀ (by positivity)]
  have hk2 : (k : ℝ) ^ 2 ≤ (↑(k + m) : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg k) hk 2
  have hp : (0 : ℝ) ≤ 8 ^ m * (2 / 3) ^ (k + m) := by positivity
  nlinarith

/-- Chebyshev bound for one small set. -/
lemma cset_bound (M : Finset (Fin N)) (hN : 1 ≤ N) :
    (μP N).real (cset M) ≤ 7 * 10 ^ 6 * (8 ^ (N - M.card) * (2 / 3) ^ N) := by
  have hkm : M.card + (N - M.card) = N := by
    have := Finset.card_le_univ M; simp only [Fintype.card_fin] at this; omega
  have hNpos : (0 : ℝ) < (N : ℝ) / 1000 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    positivity
  have hZ := cheb_avg M (Wω M) (measurable_Wω M) (2 ^ M.card)
    (fun x ω => by rw [abs_of_nonneg (Wω_nonneg M x ω)]; exact Wω_le M x ω)
    (Wω_depC M) _ (integral_Wω_sq M) (1 / 1000) (by norm_num)
  have hY := cheb_avg M (GY M) (measurable_GY M) _ (abs_GY_le M) (GY_depC M) _
    (integral_GY_sq M) ((N : ℝ) / 1000) hNpos
  have hT := cheb_avg M (GT M) (measurable_GT M) _ (abs_GT_le M) (GT_depC M) _
    (integral_GT_sq M) ((N : ℝ) / 1000) hNpos
  have bZ := boundZ M.card (N - M.card)
  have bY := boundY M.card (N - M.card) (by omega)
  have bT := boundT M.card (N - M.card) (by omega)
  rw [hkm] at bZ bY bT
  unfold cset
  calc (μP N).real (_ ∪ _ ∪ _) ≤ (μP N).real (_ ∪ _) + (μP N).real _ := measureReal_union_le _ _
    _ ≤ (μP N).real _ + (μP N).real _ + (μP N).real _ := by
        gcongr; exact measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- Hoeffding bound for one large triple. -/
lemma hset_bound (L : ℕ) (t : Finset (Fin N) × Fin N × State N) (ht : t ∈ largeT N L) :
    (μP N).real (hset t) ≤ 2 * Real.exp (-(1 / 2000) ^ 2 * 2 ^ L / 2) := by
  have hm : L ≤ N - t.1.card := by
    simp only [largeT, Finset.mem_product, Finset.mem_filter] at ht; exact ht.1.2
  refine (hoeffding_window t.1 t.2.1 t.2.2 (1 / 2000) (by norm_num)).trans ?_
  have h1 : (2 : ℝ) ^ L ≤ 2 ^ (N - t.1.card) := pow_le_pow_right₀ (by norm_num) hm
  have h2 : -(1 / 2000 : ℝ) ^ 2 * 2 ^ (N - t.1.card) / 2 ≤ -(1 / 2000) ^ 2 * 2 ^ L / 2 := by
    nlinarith
  have := Real.exp_le_exp.mpr h2
  linarith

lemma card_largeT (L : ℕ) : ((largeT N L).card : ℝ) ≤ 2 ^ N * N * 2 ^ N := by
  have : (largeT N L).card ≤ 2 ^ N * (N * 2 ^ N) := by
    unfold largeT
    rw [Finset.card_product, Finset.card_product]
    refine Nat.mul_le_mul ?_ ?_
    · refine (Finset.card_filter_le _ _).trans ?_
      simp
    · simp
  have : ((largeT N L).card : ℝ) ≤ ((2 ^ N * (N * 2 ^ N) : ℕ) : ℝ) := by exact_mod_cast this
  push_cast at this; linarith

lemma card_smallF (L : ℕ) (hN : 1 ≤ N) : ((smallF N L).card : ℝ) ≤ L * (N : ℝ) ^ L := by
  classical
  have hsub : smallF N L ⊆ (Finset.range L).biUnion
      (fun j => (Finset.powersetCard j (Finset.univ : Finset (Fin N))).image compl) := by
    intro M hM
    simp only [smallF, Finset.mem_filter, Finset.mem_univ, true_and] at hM
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_powersetCard]
    refine ⟨Mᶜ.card, ?_, Mᶜ, ⟨Finset.subset_univ _, rfl⟩, compl_compl M⟩
    rw [Finset.card_compl, Fintype.card_fin]; omega
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∀ j ∈ Finset.range L,
      ((Finset.powersetCard j (Finset.univ : Finset (Fin N))).image compl).card ≤ N ^ L := by
    intro j hj
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    exact (Nat.choose_le_pow N j).trans (Nat.pow_le_pow_right hN (Finset.mem_range.mp hj).le)
  have h3 := h1.trans (Finset.sum_le_sum h2)
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at h3
  exact_mod_cast h3

/-- Proposition 5 for fixed `N` and `L`. -/
theorem bad_bound (L : ℕ) (hL : 1 ≤ L) (hN : 1 ≤ N) :
    (μP N).real {ω | ¬ GoodA (qω ω) L} ≤
      2 ^ N * N * 2 ^ N * (2 * Real.exp (-(1 / 2000) ^ 2 * 2 ^ L / 2)) +
        L * (N : ℝ) ^ L * (7 * 10 ^ 6 * (8 ^ L * (2 / 3) ^ N)) := by
  have hsub : {ω | ¬ GoodA (qω ω) L} ⊆ (⋃ t ∈ largeT N L, hset t) ∪ ⋃ M ∈ smallF N L, cset M := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    exact hω (good_of_not_bad L hL ω hc.1 hc.2)
  have hH : (μP N).real (⋃ t ∈ largeT N L, hset t) ≤
      2 ^ N * N * 2 ^ N * (2 * Real.exp (-(1 / 2000) ^ 2 * 2 ^ L / 2)) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun t ht => hset_bound L t ht).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (card_largeT L) (by positivity)
  have hS : (μP N).real (⋃ M ∈ smallF N L, cset M) ≤
      L * (N : ℝ) ^ L * (7 * 10 ^ 6 * (8 ^ L * (2 / 3) ^ N)) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    have : ∀ M ∈ smallF N L, (μP N).real (cset M) ≤ 7 * 10 ^ 6 * (8 ^ L * (2 / 3) ^ N) := by
      intro M hM
      refine (cset_bound M hN).trans ?_
      have hm : N - M.card < L := by simpa [smallF] using hM
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) hm.le) (by positivity)) (by norm_num)
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (card_smallF L hN) (by positivity)
  calc (μP N).real {ω | ¬ GoodA (qω ω) L}
      ≤ (μP N).real ((⋃ t ∈ largeT N L, hset t) ∪ ⋃ M ∈ smallF N L, cset M) :=
        measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := add_le_add hH hS

end IIT2
