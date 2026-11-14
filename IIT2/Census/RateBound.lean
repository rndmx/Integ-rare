/-
Census of IIT 2.0, rate: for fixed `N` and threshold `L`, the complement of the good event has
probability at most `rateB N L` (Hoeffding for large `m`; truncation + Chernoff for small `m`).
-/
import IIT2.Census.RateTrunc

namespace IIT2

open MeasureTheory ProbabilityTheory Finset Real

variable {N : ℕ}

/-! ## The events -/

/-- Truncation event: some `W_M(x)` with small `m` exceeds `2^{|M|} / N^4`. -/
def TB (N L : ℕ) : Set (Ωf N) :=
  ⋃ M ∈ smallF N L, ⋃ x ∈ (Finset.univ : Finset (State N)),
    {ω | (2 : ℝ) ^ M.card / (N : ℝ) ^ 4 < Wω M x ω}

/-- Deviation events for one small set (one-sided for `T`). -/
def rset (M : Finset (Fin N)) : Set (Ωf N) :=
  {ω | 1 / 1000 ≤ |avg (fun x => Wω M x ω) - avg (fun x => ∫ ω', Wω M x ω' ∂(μP N))|} ∪
  {ω | (N : ℝ) / 1000 ≤ |avg (fun x => GY M x ω) - avg (fun x => ∫ ω', GY M x ω' ∂(μP N))|} ∪
  {ω | (N : ℝ) / 1000 ≤ avg (fun x => GT M x ω) - avg (fun x => ∫ ω', GT M x ω' ∂(μP N))}

lemma good_of_not_bad' (L : ℕ) (hL : 1 ≤ L) (ω : Ωf N)
    (hH : ω ∉ ⋃ t ∈ largeT N L, hset t) (hS : ω ∉ ⋃ M ∈ smallF N L, rset M) :
    GoodA (qω ω) L := by
  have hH' : ∀ t ∈ largeT N L, ω ∉ hset t := fun t ht h =>
    hH (Set.mem_biUnion (x := t) ht h)
  have hS' : ∀ M ∈ smallF N L, ω ∉ rset M := fun M hM h =>
    hS (Set.mem_biUnion (x := M) hM h)
  have hcs : ∀ M ∈ smallF N L,
      |avg (fun x => Wω M x ω) - 1| < 1 / 1000 ∧
      |avg (fun x => GY M x ω) - avg (fun x => ∫ ω', GY M x ω' ∂(μP N))| < (N : ℝ) / 1000 ∧
      avg (fun x => GT M x ω) - avg (fun x => ∫ ω', GT M x ω' ∂(μP N)) < (N : ℝ) / 1000 := by
    intro M hM
    have h := hS' M hM
    simp only [rset, Set.mem_union, Set.mem_setOf_eq, not_or, not_le, meanW] at h
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
    · have h2 := mean_le M hMu
      rw [← meanT_eq] at h2
      change avg (fun x => GT M x ω) ≤ 1321 / 10000 * (N : ℝ)
      linarith

/-! ## Pointwise bounds -/

lemma logb_W_le (M : Finset (Fin N)) (x : State N) (ω : Ωf N) :
    logb 2 (Wω M x ω) ≤ M.card := by
  rcases (Wω_nonneg M x ω).lt_or_eq with h | h
  · calc logb 2 (Wω M x ω) ≤ logb 2 ((2 : ℝ) ^ M.card) :=
          Real.logb_le_logb_of_le (by norm_num) h (Wω_le M x ω)
      _ = M.card := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; ring
  · rw [← h]; simp

lemma GY_le (M : Finset (Fin N)) (x : State N) (ω : Ωf N) :
    GY M x ω ≤ M.card * Wω M x ω := by
  unfold GY
  have := mul_le_mul_of_nonneg_left (logb_W_le M x ω) (Wω_nonneg M x ω)
  linarith

lemma GT_le (M : Finset (Fin N)) (x : State N) (ω : Ωf N) :
    GT M x ω ≤ M.card * Wω Finset.univ x ω := by
  unfold GT
  have := mul_le_mul_of_nonneg_left (logb_W_le M x ω) (Wω_nonneg Finset.univ x ω)
  linarith

lemma GY_ge (M : Finset (Fin N)) (x : State N) (ω : Ωf N) : -2 ≤ GY M x ω := by
  unfold GY
  have h0 := Wω_nonneg M x ω
  rcases le_or_gt (Wω M x ω) 2 with h | h
  · exact (abs_le.mp (abs_psi_le_two h0 h)).1
  · have : 0 ≤ logb 2 (Wω M x ω) := Real.logb_nonneg (by norm_num) (by linarith)
    nlinarith

/-! ## Arithmetic of the parameters -/

/-- The common Chernoff parameter. -/
noncomputable def lamR (N L : ℕ) : ℝ := (N : ℝ) ^ 3 / (2 ^ L * 2 ^ N)

/-- The common second-moment bound. -/
noncomputable def sigR (N L : ℕ) : ℝ := 3 * (N : ℝ) ^ 2 * 4 ^ L * (4 / 3) ^ N

/-- The common Chernoff bound. -/
noncomputable def eB (N L : ℕ) : ℝ :=
  Real.exp (-((N : ℝ) ^ 3 / (2000 * 2 ^ L)) + 3 * (N : ℝ) ^ 8 * 2 ^ L * (2 / 3) ^ N)

lemma lamR_pos (N L : ℕ) (hN : 1 ≤ N) : 0 < lamR N L := by
  unfold lamR; have : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

lemma expo_le (N L m : ℕ) (hN : 1 ≤ N) (hm : m ≤ L) (t : ℝ) (ht : 1 / 2000 ≤ t) :
    Real.exp (-lamR N L * 2 ^ N * t + lamR N L ^ 2 * 2 ^ m * 2 ^ N * sigR N L) ≤ eB N L := by
  unfold eB
  apply Real.exp_le_exp.mpr
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : lamR N L * 2 ^ N * t = (N : ℝ) ^ 3 * t / 2 ^ L := by
    unfold lamR; field_simp
  have h2 : lamR N L ^ 2 * 2 ^ m * 2 ^ N * sigR N L = 3 * (N : ℝ) ^ 8 * 2 ^ m * (2 / 3) ^ N := by
    unfold lamR sigR
    rw [show (4 : ℝ) ^ L = 2 ^ L * 2 ^ L by rw [← mul_pow]; norm_num,
      show ((4 : ℝ) / 3) ^ N = 2 ^ N * (2 / 3) ^ N by rw [← mul_pow]; norm_num]
    field_simp
  have h3 : (2 : ℝ) ^ m ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hm
  have h4 : (N : ℝ) ^ 3 / (2000 * 2 ^ L) ≤ (N : ℝ) ^ 3 * t / 2 ^ L := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) < N ^ 3 * 2 ^ L := by positivity
    nlinarith
  have h5 : 3 * (N : ℝ) ^ 8 * 2 ^ m * (2 / 3) ^ N ≤ 3 * (N : ℝ) ^ 8 * 2 ^ L * (2 / 3) ^ N := by
    gcongr
  rw [neg_mul, neg_mul, h1, h2]
  linarith

lemma lam_mul_le (N L k m : ℕ) (hkm : k + m = N) (hm : m ≤ L) (hN : 1 ≤ N) (c : ℝ)
    (hc : (N : ℝ) ^ 3 * 2 ^ m * c ≤ 2 ^ L * 2 ^ N) :
    lamR N L * 2 ^ m * c ≤ 1 := by
  unfold lamR
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_one (by positivity)]
  exact hc

lemma two_pow_kN (k m N : ℕ) (hkm : k + m = N) : (2 : ℝ) ^ N = 2 ^ k * 2 ^ m := by
  rw [← hkm, pow_add]

lemma sig_Z (N k : ℕ) (hk : k ≤ N) (hN : 1 ≤ N) (L : ℕ) : ((4 : ℝ) / 3) ^ k ≤ sigR N L := by
  unfold sigR
  have h1 : ((4 : ℝ) / 3) ^ k ≤ (4 / 3) ^ N := pow_le_pow_right₀ (by norm_num) hk
  have h2 : (1 : ℝ) ≤ 3 * (N : ℝ) ^ 2 * 4 ^ L := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have : (1 : ℝ) ≤ 4 ^ L := one_le_pow₀ (by norm_num)
    nlinarith
  have : (0 : ℝ) ≤ (4 / 3) ^ N := by positivity
  nlinarith

lemma sig_Y (N k : ℕ) (hk : k ≤ N) (L : ℕ) :
    (k : ℝ) * (k * (3 * (4 / 3) ^ k)) ≤ sigR N L := by
  unfold sigR
  have h1 : ((4 : ℝ) / 3) ^ k ≤ (4 / 3) ^ N := pow_le_pow_right₀ (by norm_num) hk
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
  have h4 : (1 : ℝ) ≤ 4 ^ L := one_le_pow₀ (by norm_num)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkk : (k : ℝ) * k ≤ N ^ 2 := by nlinarith
  have hp : (0 : ℝ) ≤ (4 / 3) ^ k := by positivity
  have h5 : 3 * (k * k) * ((4 : ℝ) / 3) ^ k ≤ 3 * (N : ℝ) ^ 2 * (4 / 3) ^ N := by
    have := mul_le_mul hkk h1 hp (by positivity)
    nlinarith
  have h6 := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 3 * (N : ℝ) ^ 2 * (4 / 3) ^ N)
  nlinarith

lemma sig_T (N k m : ℕ) (hk : k ≤ N) (L : ℕ) (hm : m ≤ L) :
    (k : ℝ) * (k * (3 * 4 ^ m * (4 / 3) ^ N)) ≤ sigR N L := by
  unfold sigR
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkk : (k : ℝ) * k ≤ N ^ 2 := by nlinarith
  have h4 : (4 : ℝ) ^ m ≤ 4 ^ L := pow_le_pow_right₀ (by norm_num) hm
  calc (k : ℝ) * (k * (3 * 4 ^ m * (4 / 3) ^ N)) = 3 * (k * k) * 4 ^ m * (4 / 3) ^ N := by ring
    _ ≤ _ := by gcongr

/-! ## One small set -/

lemma dev_split {a : ℝ} {δ : ℝ} (h : δ ≤ |a|) : δ ≤ a ∨ δ ≤ -a := by
  rcases le_total 0 a with h0 | h0
  · left; rwa [abs_of_nonneg h0] at h
  · right; rwa [abs_of_nonpos h0] at h

theorem rset_bound (L : ℕ) (M : Finset (Fin N)) (hM : M ∈ smallF N L) (hN : 1 ≤ N)
    (hN3 : 2 * (N : ℝ) ^ 3 ≤ 2 ^ N) :
    (μP N).real (rset M) ≤ 3 * (μP N).real (TB N L) + 10 * eB N L := by
  set k := M.card
  set m := N - M.card
  have hkN : k ≤ N := by have := Finset.card_le_univ M; simpa using this
  have hkm : k + m = N := by omega
  have hmL : m ≤ L := by have := (Finset.mem_filter.mp hM).2; omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hsplit := two_pow_kN k m N hkm
  have hl := lamR_pos N L hN
  have h2m : (2 : ℝ) ^ m ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hmL
  have hkr : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hTB : ∀ (G : State N → Ωf N → ℝ) (c : ℝ),
      (∀ x ω, c < G x ω → ω ∈ TB N L) → (μP N).real {ω | ∃ x, c < G x ω} ≤ (μP N).real (TB N L) :=
    fun G c h => measureReal_mono fun ω ⟨x, hx⟩ => h x ω hx
  have hLpos : 0 < L := by have := (Finset.mem_filter.mp hM).2; omega
  have huniv : (Finset.univ : Finset (Fin N)) ∈ smallF N L := by simp [smallF]; omega
  have memTB : ∀ (M' : Finset (Fin N)), M' ∈ smallF N L → ∀ x ω,
      (2 : ℝ) ^ M'.card / (N : ℝ) ^ 4 < Wω M' x ω → ω ∈ TB N L := fun M' hM' x ω h => by
    simp only [TB, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨M', hM', x, Finset.mem_univ _, h⟩
  -- the five tail bounds
  have hZu := upper_tail M (Wω M) (measurable_Wω M) _ (fun x ω => by
      rw [abs_of_nonneg (Wω_nonneg M x ω)]; exact Wω_le M x ω) (Wω_depC M) (sigR N L)
    (fun x => (integral_Wω_sq M x).trans (sig_Z N k hkN hN L)) ((2 : ℝ) ^ k / (N : ℝ) ^ 4)
    (by positivity) (lamR N L) (lamR N L) hl
    (lam_mul_le N L k m hkm hmL hN _ (by
      have e : (N : ℝ) ^ 3 * 2 ^ m * (2 ^ k / N ^ 4) = 2 ^ N / N := by
        rw [hsplit]; field_simp <;> ring_nf
      rw [e, div_le_iff₀ hN0]
      have h1 : (1 : ℝ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
      have hp : (0 : ℝ) < 2 ^ N := by positivity
      nlinarith [mul_le_mul h1 hNr zero_le_one (by positivity : (0:ℝ) ≤ 2 ^ L)])) hl (1 / 2000)
  have hZl := lower_tail M (Wω M) (measurable_Wω M) _ (fun x ω => by
      rw [abs_of_nonneg (Wω_nonneg M x ω)]; exact Wω_le M x ω) (Wω_depC M) (sigR N L)
    (fun x => (integral_Wω_sq M x).trans (sig_Z N k hkN hN L)) 0 le_rfl
    (fun x ω => by linarith [Wω_nonneg M x ω]) (lamR N L) (lamR N L) hl hl (by simp) (1 / 2000)
  have hYu := upper_tail M (GY M) (measurable_GY M) _ (abs_GY_le M) (GY_depC M) (sigR N L)
    (fun x => (integral_GY_sq M x).trans (sig_Y N k hkN L)) ((k : ℝ) * 2 ^ k / (N : ℝ) ^ 4)
    (by positivity) (lamR N L) (lamR N L) hl
    (lam_mul_le N L k m hkm hmL hN _ (by
      have e : (N : ℝ) ^ 3 * 2 ^ m * (k * 2 ^ k / N ^ 4) = k * 2 ^ N / N := by
        rw [hsplit]; field_simp <;> ring_nf
      rw [e, div_le_iff₀ hN0]
      have h1 : (1 : ℝ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
      have hp : (0 : ℝ) < 2 ^ N := by positivity
      have h2 : (k : ℝ) ≤ 2 ^ L * N := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h2 hp.le])) hl ((N : ℝ) / 2000)
  have hYl := lower_tail M (GY M) (measurable_GY M) _ (abs_GY_le M) (GY_depC M) (sigR N L)
    (fun x => (integral_GY_sq M x).trans (sig_Y N k hkN L)) 2 (by norm_num)
    (fun x ω => GY_ge M x ω) (lamR N L) (lamR N L) hl hl
    (lam_mul_le N L k m hkm hmL hN _ (by
      nlinarith [mul_le_mul hN3 h2m (by positivity) (by positivity)])) ((N : ℝ) / 2000)
  have hTu := upper_tail M (GT M) (measurable_GT M) _ (abs_GT_le M) (GT_depC M) (sigR N L)
    (fun x => (integral_GT_sq M x).trans (sig_T N k m hkN L hmL)) ((k : ℝ) * 2 ^ N / (N : ℝ) ^ 4)
    (by positivity) (lamR N L) (lamR N L) hl
    (lam_mul_le N L k m hkm hmL hN _ (by
      have e : (N : ℝ) ^ 3 * 2 ^ m * (k * 2 ^ N / N ^ 4) = k * 2 ^ m * 2 ^ N / N := by
        field_simp <;> ring_nf
      rw [e, div_le_iff₀ hN0]
      have hp : (0 : ℝ) < 2 ^ N := by positivity
      have h2 : (k : ℝ) * 2 ^ m ≤ N * 2 ^ L := mul_le_mul hkr h2m (by positivity) hN0.le
      nlinarith [mul_le_mul_of_nonneg_left h2 hp.le])) hl ((N : ℝ) / 2000)
  -- truncation events inside TB
  have tZ := hTB (Wω M) _ (fun x ω h => memTB M hM x ω h)
  have tY := hTB (GY M) ((k : ℝ) * 2 ^ k / (N : ℝ) ^ 4) (fun x ω h => by
    refine memTB M hM x ω ?_
    by_contra hc
    push_neg at hc
    have := GY_le M x ω
    have : (k : ℝ) * Wω M x ω ≤ k * (2 ^ k / N ^ 4) := mul_le_mul_of_nonneg_left hc hk0
    have : (k : ℝ) * 2 ^ k / N ^ 4 = k * (2 ^ k / N ^ 4) := by ring
    linarith)
  have tT := hTB (GT M) ((k : ℝ) * 2 ^ N / (N : ℝ) ^ 4) (fun x ω h => by
    refine memTB Finset.univ huniv x ω ?_
    by_contra hc
    push_neg at hc
    rw [Finset.card_univ, Fintype.card_fin] at hc
    have := GT_le M x ω
    have : (k : ℝ) * Wω Finset.univ x ω ≤ k * (2 ^ N / N ^ 4) := mul_le_mul_of_nonneg_left hc hk0
    have : (k : ℝ) * 2 ^ N / N ^ 4 = k * (2 ^ N / N ^ 4) := by ring
    linarith)
  -- exponent bounds
  have hN2000 : (1 : ℝ) / 2000 ≤ N / 2000 := by linarith
  have e1 := expo_le N L m hN hmL (1 / 2000) le_rfl
  have e2 := expo_le N L m hN hmL ((N : ℝ) / 2000) hN2000
  -- the union
  have hsub : rset M ⊆
      ({ω | 2 * (1 / 2000) ≤ avg (fun x => Wω M x ω) - avg (fun x => ∫ ω', Wω M x ω' ∂(μP N))} ∪
       {ω | 2 * (1 / 2000) ≤ avg (fun x => ∫ ω', Wω M x ω' ∂(μP N)) - avg (fun x => Wω M x ω)}) ∪
      ({ω | 2 * ((N : ℝ) / 2000) ≤ avg (fun x => GY M x ω) - avg (fun x => ∫ ω', GY M x ω' ∂(μP N))} ∪
       {ω | 2 * ((N : ℝ) / 2000) ≤ avg (fun x => ∫ ω', GY M x ω' ∂(μP N)) - avg (fun x => GY M x ω)}) ∪
      {ω | 2 * ((N : ℝ) / 2000) ≤ avg (fun x => GT M x ω) - avg (fun x => ∫ ω', GT M x ω' ∂(μP N))} := by
    intro ω hω
    simp only [rset, Set.mem_union, Set.mem_setOf_eq] at hω ⊢
    rcases hω with (h | h) | h
    · rcases dev_split h with h' | h'
      · left; left; left; linarith
      · left; left; right; linarith
    · rcases dev_split h with h' | h'
      · left; right; left; linarith
      · left; right; right; linarith
    · right; linarith
  refine (measureReal_mono hsub).trans ?_
  refine (measureReal_union_le _ _).trans ?_
  have u1 := measureReal_union_le (μ := μP N)
    ({ω | 2 * (1 / 2000) ≤ avg (fun x => Wω M x ω) - avg (fun x => ∫ ω', Wω M x ω' ∂(μP N))} ∪
       {ω | 2 * (1 / 2000) ≤ avg (fun x => ∫ ω', Wω M x ω' ∂(μP N)) - avg (fun x => Wω M x ω)})
    ({ω | 2 * ((N : ℝ) / 2000) ≤ avg (fun x => GY M x ω) - avg (fun x => ∫ ω', GY M x ω' ∂(μP N))} ∪
       {ω | 2 * ((N : ℝ) / 2000) ≤ avg (fun x => ∫ ω', GY M x ω' ∂(μP N)) - avg (fun x => GY M x ω)})
  have u2 := measureReal_union_le (μ := μP N)
    {ω | 2 * (1 / 2000) ≤ avg (fun x => Wω M x ω) - avg (fun x => ∫ ω', Wω M x ω' ∂(μP N))}
    {ω | 2 * (1 / 2000) ≤ avg (fun x => ∫ ω', Wω M x ω' ∂(μP N)) - avg (fun x => Wω M x ω)}
  have u3 := measureReal_union_le (μ := μP N)
    {ω | 2 * ((N : ℝ) / 2000) ≤ avg (fun x => GY M x ω) - avg (fun x => ∫ ω', GY M x ω' ∂(μP N))}
    {ω | 2 * ((N : ℝ) / 2000) ≤ avg (fun x => ∫ ω', GY M x ω' ∂(μP N)) - avg (fun x => GY M x ω)}
  linarith

/-! ## The bound for fixed `N`, `L` -/

/-- The bound. -/
noncomputable def rateB (N L : ℕ) : ℝ :=
  2 ^ N * N * 2 ^ N * (2 * Real.exp (-(1 / 2000) ^ 2 * 2 ^ L / 2)) +
    L * (N : ℝ) ^ L * (3 * (L * (N : ℝ) ^ L * 2 ^ N * ((N : ℝ) ^ 252 / 64 ^ (N - L))) +
      10 * eB N L)

theorem TB_bound (L : ℕ) (hN : 1 ≤ N) :
    (μP N).real (TB N L) ≤ L * (N : ℝ) ^ L * 2 ^ N * ((N : ℝ) ^ 252 / 64 ^ (N - L)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hone : ∀ M ∈ smallF N L, ∀ x : State N,
      (μP N).real {ω | (2 : ℝ) ^ M.card / (N : ℝ) ^ 4 < Wω M x ω} ≤
        (N : ℝ) ^ 252 / 64 ^ (N - L) := by
    intro M hM x
    have hmL : N - M.card < L := by simpa [smallF] using hM
    refine (trunc_prob M x 63 _ (by positivity)).trans ?_
    have e : ((2 : ℝ) ^ 63 / (63 + 1)) ^ M.card / (2 ^ M.card / (N : ℝ) ^ 4) ^ 63 =
        (N : ℝ) ^ 252 / 64 ^ M.card := by
      rw [div_pow, div_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm 63 M.card]
      norm_num
      field_simp
    push_cast
    rw [e]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  unfold TB
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  have : ∀ M ∈ smallF N L, (μP N).real (⋃ x ∈ (Finset.univ : Finset (State N)),
      {ω | (2 : ℝ) ^ M.card / (N : ℝ) ^ 4 < Wω M x ω}) ≤ 2 ^ N * ((N : ℝ) ^ 252 / 64 ^ (N - L)) := by
    intro M hM
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun x _ => hone M hM x).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; simp
  refine (Finset.sum_le_sum this).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have := card_smallF L hN
  have h0 : (0 : ℝ) ≤ 2 ^ N * ((N : ℝ) ^ 252 / 64 ^ (N - L)) := by positivity
  nlinarith

theorem rate_bad_bound (L : ℕ) (hL : 1 ≤ L) (hN : 1 ≤ N) (hN3 : 2 * (N : ℝ) ^ 3 ≤ 2 ^ N) :
    (μP N).real {ω | ¬ GoodA (qω ω) L} ≤ rateB N L := by
  have hsub : {ω | ¬ GoodA (qω ω) L} ⊆ (⋃ t ∈ largeT N L, hset t) ∪ ⋃ M ∈ smallF N L, rset M := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    exact hω (good_of_not_bad' L hL ω hc.1 hc.2)
  have hH : (μP N).real (⋃ t ∈ largeT N L, hset t) ≤
      2 ^ N * N * 2 ^ N * (2 * Real.exp (-(1 / 2000) ^ 2 * 2 ^ L / 2)) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun t ht => hset_bound L t ht).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (card_largeT L) (by positivity)
  have hS : (μP N).real (⋃ M ∈ smallF N L, rset M) ≤
      L * (N : ℝ) ^ L * (3 * (L * (N : ℝ) ^ L * 2 ^ N * ((N : ℝ) ^ 252 / 64 ^ (N - L))) +
        10 * eB N L) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    have hTB := TB_bound (N := N) L hN
    have : ∀ M ∈ smallF N L, (μP N).real (rset M) ≤
        3 * (L * (N : ℝ) ^ L * 2 ^ N * ((N : ℝ) ^ 252 / 64 ^ (N - L))) + 10 * eB N L := by
      intro M hM
      have := rset_bound L M hM hN hN3
      linarith
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (card_smallF L hN) (by unfold eB; positivity)
  unfold rateB
  calc (μP N).real {ω | ¬ GoodA (qω ω) L}
      ≤ (μP N).real ((⋃ t ∈ largeT N L, hset t) ∪ ⋃ M ∈ smallF N L, rset M) :=
        measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := add_le_add hH hS

end IIT2
