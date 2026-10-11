/-
Census of complexes: some disjoint pair wins the cause-side competition (second moment method).

For the pairs `{2m, 2m+1}`, `m < N/2`, consider in flipped coordinates `w = flipP s z`
* the effect box `ps_box s a b` (a product box on the rows of the block of `s`, which implies
  `effBox` for `z`), of probability `ps_pB = (1/100)^2 (1/10)^6`;
* the orthant event `ps_E a b y`: all six cause-side differences `pb_eta` are at most `-2y`
  (which implies `inA`).
Their intersections `ps_A` have probability at least `ps_pB (G⁻ - err) - P(¬g2)` (removal of the block
of `s`, independence, Lindeberg, `ps_rest_low`), and two of them intersect with probability at most
`ps_pB² ((G⁺)² + err) + P(¬g2)` (`ps_rest_up`).  The Gaussian orthants `G⁻ ≤ G⁺` differ by an
exponentially small slab, and `G⁻ ≥ N^{-17/20}`, so Chebyshev's inequality for the number of
successful pairs gives `tendsto_noPairOrthant`.
-/
import IIT.Census.PairSecond
import IIT.Census.BigPhiProbBasic
import IIT.Census.PairBridge

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

noncomputable section

variable {N : ℕ}

/-! ### The effect box in flipped coordinates -/

/-- The constraint on the entry `(r, j)`: rows of the block of `s`, columns `a` and `b`. -/
def ps_S (s : State N) (a b : Fin N) (r : State N) (j : Fin N) : Set ℝ :=
  if pb_blk a b r = pb_blk a b s ∧ (j = a ∨ j = b) then
    (if r = s then Jb (s j) else Set.Ioo (9 / 20) (11 / 20)) else Set.univ

/-- The effect box of the pair `{a, b}` in flipped coordinates. -/
def ps_box (s : State N) (a b : Fin N) : Set (Param N) := {w | ∀ r j, w r j ∈ ps_S s a b r j}

/-- The probability of the effect box. -/
def ps_pB : ℝ := (1 / 100) ^ 2 * (1 / 10) ^ 6

lemma ps_pB_pos : 0 < ps_pB := by norm_num [ps_pB]

lemma ps_pB_le_one : ps_pB ≤ 1 := by norm_num [ps_pB]

lemma ps_blk_flip {a b k : Fin N} (hk : k = a ∨ k = b) (r : State N) :
    pb_blk a b (flip r k) = pb_blk a b r := by
  funext ⟨j, hj⟩
  have hjk : j ≠ k := by
    rintro rfl
    rcases hk with rfl | rfl <;> simp at hj
  exact flip_ne_apply r hjk

lemma ps_flip_ne (r : State N) (k : Fin N) : flip r k ≠ r := fun h => by
  have := congrFun h k
  rw [flip_self] at this
  simp at this

lemma ps_flip2_ne {a b : Fin N} (hab : a ≠ b) (r : State N) : flip (flip r a) b ≠ r := fun h => by
  have := congrFun h a
  rw [flip_ne_apply _ hab, flip_self] at this
  simp at this

/-- The box implies `effBox` for the unflipped parameters. -/
theorem ps_box_effBox {s : State N} {a b : Fin N} (hab : a ≠ b) {w : Param N}
    (hw : w ∈ ps_box s a b) : effBox (flipP s w) s a b := by
  have hS : ∀ j, j = a ∨ j = b → flipP s w s j ∈ Set.Ioo (99 / 100 : ℝ) 1 := by
    intro j hj
    have := hw s j
    rw [ps_S, ite_eq_left ⟨rfl, hj⟩, ite_eq_left rfl] at this
    exact flipC_Jb _ this
  have hM : ∀ r, pb_blk a b r = pb_blk a b s → r ≠ s → ∀ j, j = a ∨ j = b →
      flipP s w r j ∈ Set.Ioo (9 / 20 : ℝ) (11 / 20) := by
    intro r hr hrs j hj
    have := hw r j
    rw [ps_S, ite_eq_left ⟨hr, hj⟩, ite_eq_right hrs] at this
    exact flipC_mid _ this
  refine ⟨hS a (Or.inl rfl), hS b (Or.inr rfl), fun r hr => ?_⟩
  have hr' : pb_blk a b r = pb_blk a b s ∧ r ≠ s := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ps_blk_flip (Or.inl rfl) s, ps_flip_ne s a⟩
    · exact ⟨ps_blk_flip (Or.inr rfl) s, ps_flip_ne s b⟩
    · exact ⟨by rw [ps_blk_flip (Or.inr rfl), ps_blk_flip (Or.inl rfl)], ps_flip2_ne hab s⟩
  exact ⟨hM r hr'.1 hr'.2 a (Or.inl rfl), hM r hr'.1 hr'.2 b (Or.inr rfl)⟩

/-! ### The orthant event -/

/-- All six cause-side differences of the pair are at most `-2y`. -/
def ps_E (a b : Fin N) (y : ℝ) : Set (Param N) := {w | ∀ p, pb_eta w a b p ≤ -2 * y}

/-- The orthant event implies `inA`. -/
theorem ps_E_inA {a b : Fin N} {y : ℝ} {w : Param N} (hw : w ∈ ps_E a b y) : inA w a b y := by
  have key : ∀ p : Fin 6, pb_eta w a b p ≤ -2 * y := hw
  have e0 : pb_eta w a b 0 = etaP w a b a true false := rfl
  have e1 : pb_eta w a b 1 = etaP w a b a false true := rfl
  have e2 : pb_eta w a b 2 = etaP w a b a true true := rfl
  have e3 : pb_eta w a b 3 = etaP w a b b true false := rfl
  have e4 : pb_eta w a b 4 = etaP w a b b false true := rfl
  have e5 : pb_eta w a b 5 = etaP w a b b true true := rfl
  intro i hi ta tb hne
  rcases Finset.mem_insert.1 hi with rfl | hi
  · cases ta <;> cases tb
    · exact absurd rfl hne
    · rw [← e1]; exact key 1
    · rw [← e0]; exact key 0
    · rw [← e2]; exact key 2
  · rw [Finset.mem_singleton.1 hi]
    cases ta <;> cases tb
    · exact absurd rfl hne
    · rw [← e4]; exact key 4
    · rw [← e3]; exact key 3
    · rw [← e5]; exact key 5

/-- The event used for the pair `{a, b}`. -/
def ps_A (s : State N) (a b : Fin N) (y : ℝ) : Set (Param N) := ps_E a b y ∩ ps_box s a b

/-! ### Measurability -/

lemma ps_measurableSet_rows {ι : Type*} [Countable ι] (T : ι → Fin N → Set ℝ)
    (hT : ∀ t j, MeasurableSet (T t j)) :
    MeasurableSet {y : ι → Fin N → ℝ | ∀ t j, y t j ∈ T t j} := by
  have e : {y : ι → Fin N → ℝ | ∀ t j, y t j ∈ T t j} =
      ⋂ t, ⋂ j, (fun y : ι → Fin N → ℝ => y t j) ⁻¹' T t j := by
    ext y; simp
  rw [e]
  exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun j =>
    ((measurable_pi_apply j).comp (measurable_pi_apply t)) (hT t j)

lemma ps_measurableSet_S (s : State N) (a b : Fin N) (r : State N) (j : Fin N) :
    MeasurableSet (ps_S s a b r j) := by
  unfold ps_S Jb
  split_ifs <;> first | exact measurableSet_Ioo | exact MeasurableSet.univ

lemma ps_measurableSet_box (s : State N) (a b : Fin N) : MeasurableSet (ps_box s a b) :=
  ps_measurableSet_rows _ fun r j => ps_measurableSet_S s a b r j

lemma ps_measurableSet_E {a b : Fin N} (hab : a ≠ b) (y : ℝ) : MeasurableSet (ps_E a b y) := by
  have e : ps_E a b y = {w | ∀ p, (∑ k, pb_Xs a b w k) p ≤ (fun _ : Fin 6 => -2 * y) p} := by
    ext w
    simp only [ps_E, Set.mem_ofPred_eq, pb_eta_eq_sum hab]
  rw [e]
  exact lind_measurableSet_orth (Finset.measurable_sum _ fun k _ =>
    (measurable_pi_apply k).comp (pb_measurable_Xs a b)) _

lemma ps_measurableSet_A (s : State N) {a b : Fin N} (hab : a ≠ b) (y : ℝ) :
    MeasurableSet (ps_A s a b y) :=
  (ps_measurableSet_E hab y).inter (ps_measurableSet_box s a b)

/-! ### The probability of the effect boxes -/

lemma ps_cubeM_rows (S : State N → Fin N → Set ℝ) :
    cubeM N {w | ∀ r j, w r j ∈ S r j} = ∏ r, ∏ j, unif (S r j) := by
  have e : {w : Param N | ∀ r j, w r j ∈ S r j} =
      Set.univ.pi fun r => Set.univ.pi fun j => S r j := by
    ext w; simp [Set.mem_pi]
  rw [e, cubeM, Measure.pi_pi]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [rowM, Measure.pi_pi]

lemma ps_unif_Ioo {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ 1) :
    unif (Set.Ioo x y) = ENNReal.ofReal (y - x) := by
  unfold unif
  rw [Measure.restrict_apply measurableSet_Ioo,
    Set.inter_eq_left.mpr (Set.Ioo_subset_Icc_self.trans (Set.Icc_subset_Icc hx hy)),
    Real.volume_Ioo]

lemma ps_unif_Jb (x : Bool) : unif (Jb x) = ENNReal.ofReal (1 / 100) := by
  cases x
  · simp only [Jb, Bool.false_eq_true, ite_false]
    rw [ps_unif_Ioo (by norm_num) (by norm_num)]; norm_num
  · simp only [Jb, ite_true]
    rw [ps_unif_Ioo (by norm_num) (by norm_num)]; norm_num

lemma ps_unif_mid : unif (Set.Ioo (9 / 20 : ℝ) (11 / 20)) = ENNReal.ofReal (1 / 10) := by
  rw [ps_unif_Ioo (by norm_num) (by norm_num)]; norm_num

lemma ps_S_univ_of {s : State N} {a b j : Fin N} (hj : j ≠ a ∧ j ≠ b) (r : State N) :
    ps_S s a b r j = Set.univ := by
  rw [ps_S, ite_eq_right]
  tauto

lemma ps_S_pos {s r : State N} {a b j : Fin N} (hr : pb_blk a b r = pb_blk a b s)
    (hj : j = a ∨ j = b) :
    ps_S s a b r j = if r = s then Jb (s j) else Set.Ioo (9 / 20) (11 / 20) := by
  rw [ps_S, ite_eq_left (And.intro hr hj)]

lemma ps_prod_row {s : State N} {a b : Fin N} (hab : a ≠ b) (r : State N) :
    ∏ j, unif (ps_S s a b r j) = if pb_blk a b r = pb_blk a b s then
      (if r = s then ENNReal.ofReal (1 / 100) ^ 2 else ENNReal.ofReal (1 / 10) ^ 2) else 1 := by
  by_cases hr : pb_blk a b r = pb_blk a b s
  · rw [ite_eq_left hr, Finset.prod_eq_mul a b hab (fun c _ hc => ?_)
      (fun h => absurd (mem_univ a) h) (fun h => absurd (mem_univ b) h)]
    · rw [ps_S_pos hr (Or.inl rfl), ps_S_pos hr (Or.inr rfl)]
      by_cases hrs : r = s
      · rw [ite_eq_left hrs, ite_eq_left hrs, ite_eq_left hrs, ps_unif_Jb, ps_unif_Jb, sq]
      · rw [ite_eq_right hrs, ite_eq_right hrs, ite_eq_right hrs, ps_unif_mid, sq]
    · rw [ps_S_univ_of hc, measure_univ]
  · rw [ite_eq_right hr]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [ps_S, ite_eq_right (by tauto), measure_univ]

lemma ps_filter_blk {a b : Fin N} (s : State N) :
    (univ.filter fun r : State N => pb_blk a b r = pb_blk a b s) =
      univ.image (pb_row a b (pb_blk a b s)) := by
  ext r
  simp only [mem_filter, mem_univ, true_and, mem_image]
  constructor
  · intro h
    exact ⟨(r a, r b), by rw [← h]; exact pb_row_blk r⟩
  · rintro ⟨t, rfl⟩
    exact pb_blk_row _ _

lemma ps_card_filter {a b : Fin N} (hab : a ≠ b) (s : State N) :
    (univ.filter fun r : State N => pb_blk a b r = pb_blk a b s).card = 4 := by
  rw [ps_filter_blk, card_image_of_injective]
  · simp
  · intro t t' h
    have h1 := congrFun h a
    have h2 := congrFun h b
    simp only [pb_row_a, pb_row_b hab] at h1 h2
    exact Prod.ext h1 h2

/-- The effect box has probability `ps_pB`. -/
theorem ps_cubeM_box {s : State N} {a b : Fin N} (hab : a ≠ b) :
    cubeM N (ps_box s a b) = ENNReal.ofReal ps_pB := by
  rw [ps_box, ps_cubeM_rows]
  simp_rw [ps_prod_row hab]
  have hs : s ∈ univ.filter (fun r : State N => pb_blk a b r = pb_blk a b s) := by simp
  rw [← Finset.prod_filter, ← Finset.mul_prod_erase _ _ hs, ite_eq_left rfl,
    Finset.prod_congr rfl (fun r hr => ite_eq_right (Finset.ne_of_mem_erase hr)), Finset.prod_const,
    Finset.card_erase_of_mem hs, ps_card_filter hab, ps_pB, ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_pow (by norm_num), ← pow_mul]

lemma ps_real_box {s : State N} {a b : Fin N} (hab : a ≠ b) :
    (cubeM N).real (ps_box s a b) = ps_pB := by
  rw [measureReal_def, ps_cubeM_box hab, ENNReal.toReal_ofReal ps_pB_pos.le]

/-- Effect boxes of disjoint pairs are independent. -/
theorem ps_cubeM_box_inter {s : State N} {a b c d : Fin N} (h : pb_dist4 a b c d) :
    cubeM N (ps_box s a b ∩ ps_box s c d) = cubeM N (ps_box s a b) * cubeM N (ps_box s c d) := by
  have e : ps_box s a b ∩ ps_box s c d =
      {w | ∀ r j, w r j ∈ ps_S s a b r j ∩ ps_S s c d r j} := by
    ext w
    simp only [ps_box, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h r j => ⟨h.1 r j, h.2 r j⟩, fun h => ⟨fun r j => (h r j).1, fun r j => (h r j).2⟩⟩
  rw [e, ps_box, ps_box, ps_cubeM_rows, ps_cubeM_rows, ps_cubeM_rows, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := h
  by_cases hj : j = a ∨ j = b
  · have hj' : j ≠ c ∧ j ≠ d := by
      rcases hj with rfl | rfl
      · exact ⟨hac, had⟩
      · exact ⟨hbc, hbd⟩
    rw [ps_S_univ_of (a := c) (b := d) hj' r, Set.inter_univ, measure_univ, mul_one]
  · rw [ps_S_univ_of (a := a) (b := b) (by tauto) r, Set.univ_inter, measure_univ, one_mul]

/-! ### The boxes as events of the block rows -/

lemma ps_box_eq {s : State N} {a b : Fin N} :
    ps_box s a b = pb_blockRows a b s ⁻¹'
      {y | ∀ t j, y t j ∈ ps_S s a b (pb_row a b (pb_blk a b s) t) j} := by
  ext w
  simp only [ps_box, Set.mem_preimage, Set.mem_ofPred_eq, pb_blockRows]
  constructor
  · intro h t j
    exact h _ j
  · intro h r j
    by_cases hr : pb_blk a b r = pb_blk a b s
    · have := h (r a, r b) j
      rwa [← hr, pb_row_blk] at this
    · rw [ps_S, ite_eq_right (by tauto)]
      trivial

lemma ps_row2_of_ab {a b c d : Fin N} {r s : State N} (hr : pb_blk a b r = pb_blk a b s) :
    r = pb_row2 a b c d (pb_blk2 a b c d s) ((r a, r b), (r c, r d)) :=
  pb_row2_of_agree fun j hj => congrFun hr ⟨j, by simp at hj ⊢; tauto⟩

lemma ps_row2_of_cd {a b c d : Fin N} {r s : State N} (hr : pb_blk c d r = pb_blk c d s) :
    r = pb_row2 a b c d (pb_blk2 a b c d s) ((r a, r b), (r c, r d)) :=
  pb_row2_of_agree fun j hj => congrFun hr ⟨j, by simp at hj ⊢; tauto⟩

lemma ps_box_inter_eq {s : State N} {a b c d : Fin N} :
    ps_box s a b ∩ ps_box s c d = pb_blockRows2 a b c d s ⁻¹'
      {z | ∀ τ j, z τ j ∈ ps_S s a b (pb_row2 a b c d (pb_blk2 a b c d s) τ) j ∩
        ps_S s c d (pb_row2 a b c d (pb_blk2 a b c d s) τ) j} := by
  ext w
  simp only [ps_box, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, pb_blockRows2]
  constructor
  · rintro ⟨h1, h2⟩ τ j
    exact ⟨h1 _ j, h2 _ j⟩
  · intro h
    have key : ∀ r, (pb_blk a b r = pb_blk a b s ∨ pb_blk c d r = pb_blk c d s) → ∀ j,
        w r j ∈ ps_S s a b r j ∧ w r j ∈ ps_S s c d r j := by
      intro r hr j
      have hr' : r = pb_row2 a b c d (pb_blk2 a b c d s) ((r a, r b), (r c, r d)) := by
        rcases hr with hr | hr
        · exact ps_row2_of_ab hr
        · exact ps_row2_of_cd hr
      have := h ((r a, r b), (r c, r d)) j
      rw [← hr'] at this
      exact this
    refine ⟨fun r j => ?_, fun r j => ?_⟩
    · by_cases hr : pb_blk a b r = pb_blk a b s
      · exact (key r (Or.inl hr) j).1
      · rw [ps_S, ite_eq_right (by tauto)]
        trivial
    · by_cases hr : pb_blk c d r = pb_blk c d s
      · exact (key r (Or.inr hr) j).2
      · rw [ps_S, ite_eq_right (by tauto)]
        trivial

/-! ### One pair: lower bound; two pairs: upper bound -/

lemma ps_fg2_nonneg (N : ℕ) : 0 ≤ fg2 N := by unfold fg2; positivity

lemma ps_real_not_g2 :
    (cubeM N).real {w : Param N | ¬ ∀ i r, Qw w i r ≤ tauN N} ≤ fg2 N :=
  ENNReal.toReal_le_of_le_ofReal (ps_fg2_nonneg N) cubeM_not_g2

/-- **Lower bound** for one pair. -/
theorem ps_A_low {s : State N} {a b : Fin N} (hab : a ≠ b) (hB : 2 ≤ pb_B a b) (y : ℝ) :
    ps_pB * (gbox_G6.real {x | ∀ p, x p ≤ (-2 * y - 4 * tauN N / sigN N) - ps_eps N} -
      ps_err6 N) - fg2 N ≤ (cubeM N).real (ps_A s a b y) := by
  set c := -2 * y - 4 * tauN N / sigN N with hc
  set R := {w : Param N | ∀ p, (∑ k, pb_Xr a b s w k) p ≤ c} with hR
  have hlow := ps_rest_low hab s hB c
  have hO : MeasurableSet {x : Fin (pb_B a b - 1) → Fin 6 → ℝ | ∀ p, (∑ k, x k) p ≤ c} :=
    lind_measurableSet_orth ps_measurable_sum (fun _ => c)
  have hBs : MeasurableSet {y' : PbPat → Fin N → ℝ |
      ∀ t j, y' t j ∈ ps_S s a b (pb_row a b (pb_blk a b s) t) j} :=
    ps_measurableSet_rows _ fun t j => ps_measurableSet_S s a b _ j
  have hind := (pb_indep_rest a b s).measure_inter_preimage_eq_mul _ _ hBs hO
  have eR : R = pb_Xr a b s ⁻¹' {x | ∀ p, (∑ k, x k) p ≤ c} := rfl
  have hmul : (cubeM N).real (ps_box s a b ∩ R) = ps_pB * (cubeM N).real R := by
    rw [measureReal_def, measureReal_def, eR, ps_box_eq, hind, ENNReal.toReal_mul, ← ps_box_eq,
      ps_cubeM_box hab, ENNReal.toReal_ofReal ps_pB_pos.le]
  have hsub : ps_box s a b ∩ R ⊆ ps_A s a b y ∪ {w : Param N | ¬ ∀ i r, Qw w i r ≤ tauN N} := by
    rintro w ⟨hb, hRw⟩
    by_cases hg : ∀ i r, Qw w i r ≤ tauN N
    · refine Or.inl ⟨fun p => ?_, hb⟩
      have h1 := pb_abs_eta_sub_le hab s hg p
      have h2 : (∑ k, pb_Xr a b s w k) p ≤ c := hRw p
      rw [abs_le] at h1
      linarith [h1.2]
    · exact Or.inr hg
  have h1 : (cubeM N).real (ps_box s a b ∩ R) ≤ (cubeM N).real (ps_A s a b y) + fg2 N :=
    (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
      (add_le_add le_rfl ps_real_not_g2))
  have hp := ps_pB_pos
  rw [hmul] at h1
  nlinarith [mul_le_mul_of_nonneg_left hlow hp.le]

/-- **Upper bound** for two disjoint pairs. -/
theorem ps_AA_up {s : State N} {a b c d : Fin N} (h : pb_dist4 a b c d) (hB : 2 ≤ pb_B2 a b c d)
    (y : ℝ) :
    (cubeM N).real (ps_A s a b y ∩ ps_A s c d y) ≤
      ps_pB ^ 2 * ((gbox_G6.real {x | ∀ p, x p ≤ (-2 * y + 16 * tauN N / sigN N) +
        ps_eps N}) ^ 2 + ps_err12 N) + fg2 N := by
  set c0 := -2 * y + 16 * tauN N / sigN N with hc0
  set R := {w : Param N | ∀ q, (∑ k, pb_Yr a b c d s w k) q ≤ c0} with hR
  have hup := ps_rest_up h s hB c0
  have hO : MeasurableSet {x : Fin (pb_B2 a b c d - 1) → Fin 12 → ℝ | ∀ q, (∑ k, x k) q ≤ c0} :=
    lind_measurableSet_orth ps_measurable_sum (fun _ => c0)
  have hBs : MeasurableSet {z : PbPat × PbPat → Fin N → ℝ |
      ∀ τ j, z τ j ∈ ps_S s a b (pb_row2 a b c d (pb_blk2 a b c d s) τ) j ∩
        ps_S s c d (pb_row2 a b c d (pb_blk2 a b c d s) τ) j} :=
    ps_measurableSet_rows _ fun τ j =>
      (ps_measurableSet_S s a b _ j).inter (ps_measurableSet_S s c d _ j)
  have hind := (pb_indep_rest2 a b c d s).measure_inter_preimage_eq_mul _ _ hBs hO
  have eR : R = pb_Yr a b c d s ⁻¹' {x | ∀ q, (∑ k, x k) q ≤ c0} := rfl
  have hmul : (cubeM N).real ((ps_box s a b ∩ ps_box s c d) ∩ R) =
      ps_pB ^ 2 * (cubeM N).real R := by
    rw [measureReal_def, measureReal_def, eR, ps_box_inter_eq, hind, ENNReal.toReal_mul,
      ← ps_box_inter_eq, ps_cubeM_box_inter h, ps_cubeM_box h.1,
      ps_cubeM_box h.2.2.2.2.2, ← sq, ENNReal.toReal_pow, ENNReal.toReal_ofReal ps_pB_pos.le]
  have hsub : ps_A s a b y ∩ ps_A s c d y ⊆
      ((ps_box s a b ∩ ps_box s c d) ∩ R) ∪ {w : Param N | ¬ ∀ i r, Qw w i r ≤ tauN N} := by
    rintro w ⟨⟨hE, hb⟩, ⟨hE', hb'⟩⟩
    by_cases hg : ∀ i r, Qw w i r ≤ tauN N
    · refine Or.inl ⟨⟨hb, hb'⟩, fun q => ?_⟩
      have h2 : pb_eta2 w a b c d q ≤ -2 * y := by
        refine pb_fin12_cases (P := fun q => pb_eta2 w a b c d q ≤ -2 * y) (fun p => ?_)
          (fun p => ?_) q
        · simp only [pb_eta2, Fin.append_left]; exact hE p
        · simp only [pb_eta2, Fin.append_right]; exact hE' p
      have h3 := pb_abs_eta2_sub_le h s hg q
      rw [abs_le] at h3
      show (∑ k, pb_Yr a b c d s w k) q ≤ c0
      linarith [h3.1]
    · exact Or.inr hg
  have h1 : (cubeM N).real (ps_A s a b y ∩ ps_A s c d y) ≤
      ps_pB ^ 2 * (cubeM N).real R + fg2 N := by
    rw [← hmul]
    exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
      (add_le_add le_rfl ps_real_not_g2))
  have hp : 0 ≤ ps_pB ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hup hp]

/-! ### Chebyshev's inequality for a number of events -/

/-- **Second moment bound**: if the expected number of events is at least `e0 > 0` and the sum of
the probabilities of the pairwise intersections is at most `U`, the probability that none of the
events occurs is at most `1/e0 + U/e0² - 1`. -/
theorem ps_cheb {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {M : ℕ}
    (A : Fin M → Set Ω) (hA : ∀ i, MeasurableSet (A i)) {e0 U : ℝ} (he0 : 0 < e0)
    (he : e0 ≤ ∑ i, μ.real (A i)) (hU : ∑ i, ∑ j ∈ univ.erase i, μ.real (A i ∩ A j) ≤ U) :
    μ.real {ω | ∀ i, ω ∉ A i} ≤ 1 / e0 + U / e0 ^ 2 - 1 := by
  set e := ∑ i, μ.real (A i) with he_def
  have hepos : 0 < e := he0.trans_le he
  set f : Fin M → Ω → ℝ := fun i => (A i).indicator 1 with hf
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

/-! ### The disjoint pairs -/

/-- First unit of the `m`-th pair. -/
def ps_a (N : ℕ) (m : Fin (N / 2)) : Fin N := ⟨2 * m.val, by have := m.isLt; omega⟩

/-- Second unit of the `m`-th pair. -/
def ps_b (N : ℕ) (m : Fin (N / 2)) : Fin N := ⟨2 * m.val + 1, by have := m.isLt; omega⟩

lemma ps_ab_ne (m : Fin (N / 2)) : ps_a N m ≠ ps_b N m := by
  simp only [ps_a, ps_b, ne_eq, Fin.mk.injEq]
  omega

lemma ps_dist4 {m m' : Fin (N / 2)} (h : m ≠ m') :
    pb_dist4 (ps_a N m) (ps_b N m) (ps_a N m') (ps_b N m') := by
  have h' : m.val ≠ m'.val := fun e => h (Fin.ext e)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [ps_a, ps_b, ne_eq, Fin.mk.injEq] <;> omega

/-! ### The bound for fixed `N` -/

/-- The lower Gaussian orthant. -/
def ps_Glo (N : ℕ) : ℝ :=
  gbox_G6.real {x | ∀ p, x p ≤ (-2 * yN N - 4 * tauN N / sigN N) - ps_eps N}

/-- The upper Gaussian orthant. -/
def ps_Ghi (N : ℕ) : ℝ :=
  gbox_G6.real {x | ∀ p, x p ≤ (-2 * yN N + 16 * tauN N / sigN N) + ps_eps N}

/-- Lower bound on the probability of one pair event. -/
def ps_la (N : ℕ) : ℝ := ps_pB * (ps_Glo N - ps_err6 N) - fg2 N

/-- Upper bound on the probability of two pair events. -/
def ps_lb (N : ℕ) : ℝ := ps_pB ^ 2 * (ps_Ghi N ^ 2 + ps_err12 N) + fg2 N

/-- No pair `m < N/2` has its event. -/
def ps_Z (N : ℕ) (s : State N) : Set (Param N) :=
  {w | ∀ m : Fin (N / 2), w ∉ ps_A s (ps_a N m) (ps_b N m) (yN N)}

/-- **Second moment bound** for fixed `N`. -/
theorem ps_bound (hN : 5 ≤ N) (s : State N) (ha : 0 < ps_la N) :
    (cubeM N).real (ps_Z N s) ≤ 1 / ((N / 2 : ℕ) * ps_la N) + ps_lb N / ps_la N ^ 2 - 1 := by
  have hM : (0 : ℝ) < (N / 2 : ℕ) := by exact_mod_cast (by omega : 0 < N / 2)
  have hB : ∀ m : Fin (N / 2), 2 ≤ pb_B (ps_a N m) (ps_b N m) := fun m => by
    rw [pb_B_eq (ps_ab_ne m)]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (N - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hB2 : ∀ m m' : Fin (N / 2), m ≠ m' →
      2 ≤ pb_B2 (ps_a N m) (ps_b N m) (ps_a N m') (ps_b N m') := fun m m' h => by
    rw [pb_B2_eq (ps_dist4 h)]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (N - 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlb : 0 ≤ ps_lb N := by
    have := ps_fg2_nonneg N
    unfold ps_lb
    have : 0 ≤ ps_err12 N := ps_err_nonneg (by norm_num)
      (by have := gbox_C3_nonneg gbox_T12; positivity) N
    positivity
  have h := ps_cheb (cubeM N) (fun m => ps_A s (ps_a N m) (ps_b N m) (yN N))
    (fun m => ps_measurableSet_A s (ps_ab_ne m) _) (e0 := (N / 2 : ℕ) * ps_la N)
    (U := ((N / 2 : ℕ) : ℝ) ^ 2 * ps_lb N) (by positivity) ?_ ?_
  · have e : ((N / 2 : ℕ) : ℝ) ^ 2 * ps_lb N / (((N / 2 : ℕ) : ℝ) * ps_la N) ^ 2 =
        ps_lb N / ps_la N ^ 2 := by
      rw [mul_pow, mul_div_mul_left _ _ (pow_ne_zero 2 hM.ne')]
    rw [e] at h
    exact h
  · calc ((N / 2 : ℕ) : ℝ) * ps_la N = ∑ _m : Fin (N / 2), ps_la N := by simp
      _ ≤ ∑ m, (cubeM N).real (ps_A s (ps_a N m) (ps_b N m) (yN N)) :=
          Finset.sum_le_sum fun m _ => ps_A_low (ps_ab_ne m) (hB m) (yN N)
  · calc ∑ m, ∑ m' ∈ univ.erase m, (cubeM N).real (ps_A s (ps_a N m) (ps_b N m) (yN N) ∩
          ps_A s (ps_a N m') (ps_b N m') (yN N))
        ≤ ∑ m : Fin (N / 2), ∑ m' ∈ univ.erase m, ps_lb N := by
          refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun m' hm' => ?_
          exact ps_AA_up (ps_dist4 (Finset.ne_of_mem_erase hm').symm)
            (hB2 m m' (Finset.ne_of_mem_erase hm').symm) (yN N)
      _ ≤ ∑ _m : Fin (N / 2), ∑ _m' : Fin (N / 2), ps_lb N :=
          Finset.sum_le_sum fun m _ => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) fun _ _ _ => hlb
      _ = ((N / 2 : ℕ) : ℝ) ^ 2 * ps_lb N := by simp; ring

/-! ### Asymptotics -/

/-- The Gaussian mass of the slab between the two orthants. -/
def ps_D (N : ℕ) : ℝ :=
  6 * ((4 * tauN N / sigN N + 16 * tauN N / sigN N + 2 * ps_eps N) /
    (Real.sqrt gbox_c2 * Real.sqrt (2 * Real.pi)))

lemma ps_D_nonneg (N : ℕ) : 0 ≤ ps_D N := by
  have := tauN_pos N; have := sigN_pos N; have := ps_eps_pos N
  unfold ps_D; positivity

/-- **Slab bound**: the upper orthant exceeds the lower one by at most `ps_D N`. -/
lemma ps_Ghi_le (N : ℕ) : ps_Ghi N ≤ ps_Glo N + ps_D N := by
  set lo := (-2 * yN N - 4 * tauN N / sigN N) - ps_eps N with hlo
  set w := 4 * tauN N / sigN N + 16 * tauN N / sigN N + 2 * ps_eps N with hw
  have hw0 : 0 ≤ w := by
    have := tauN_pos N; have := sigN_pos N; have := ps_eps_pos N; positivity
  have hhi : (-2 * yN N + 16 * tauN N / sigN N) + ps_eps N = lo + w := by rw [hlo, hw]; ring
  have hsub : {x : Fin 6 → ℝ | ∀ p, x p ≤ (-2 * yN N + 16 * tauN N / sigN N) + ps_eps N} ⊆
      {x | ∀ p, x p ≤ lo} ∪ ⋃ p, {x : Fin 6 → ℝ | x p ∈ Set.Icc lo (lo + w)} := by
    intro x hx
    by_cases h : ∀ p, x p ≤ lo
    · exact Or.inl h
    · push Not at h
      obtain ⟨p, hp⟩ := h
      have := hx p
      rw [hhi] at this
      exact Or.inr (Set.mem_iUnion.2 ⟨p, hp.le, this⟩)
  calc ps_Ghi N ≤ gbox_G6.real ({x | ∀ p, x p ≤ lo} ∪
        ⋃ p, {x : Fin 6 → ℝ | x p ∈ Set.Icc lo (lo + w)}) := measureReal_mono hsub
    _ ≤ ps_Glo N + ∑ p, gbox_G6.real {x : Fin 6 → ℝ | x p ∈ Set.Icc lo (lo + w)} :=
        (measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_iUnion_fintype_le _))
    _ ≤ ps_Glo N + ∑ _p : Fin 6, w / (Real.sqrt gbox_c2 * Real.sqrt (2 * Real.pi)) := by
        gcongr with p
        exact gbox_G6_slab_le p lo w hw0
    _ = ps_Glo N + ps_D N := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ps_D, hw]
        ring

lemma ps_tau_sig (N : ℕ) : tauN N / sigN N =
    Real.exp (2 / 9) * (Real.exp (-(2 / 9)) / Real.sqrt (2 / 3)) ^ N := by
  have hs : sigN N = Real.sqrt (2 / 3) ^ N := by
    rw [sigN]
    rw [show ((2 / 3 : ℝ)) ^ N = (Real.sqrt (2 / 3) ^ N) ^ 2 by
      rw [← pow_mul, mul_comm N 2, pow_mul, Real.sq_sqrt (by norm_num)]]
    exact Real.sqrt_sq (by positivity)
  have ht : tauN N = Real.exp (2 / 9) * Real.exp (-(2 / 9)) ^ N := by
    rw [tauN, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hs, ht, div_pow]
  ring

lemma ps_r_nonneg : 0 ≤ Real.exp (-(2 / 9)) / Real.sqrt (2 / 3) :=
  div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)

lemma ps_r_lt : Real.exp (-(2 / 9)) / Real.sqrt (2 / 3) < 1 := by
  rw [div_lt_one (Real.sqrt_pos.2 (by norm_num)), Real.lt_sqrt (Real.exp_pos _).le]
  have h1 : (1 / 9 : ℝ) + 1 ≤ Real.exp (1 / 9) := Real.add_one_le_exp _
  have h4 : Real.exp (4 / 9) = Real.exp (1 / 9) ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp (-(2 / 9)) ^ 2 * Real.exp (4 / 9) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h5 : (3 / 2 : ℝ) < Real.exp (4 / 9) := by
    rw [h4]
    have := pow_le_pow_left₀ (by norm_num) h1 4
    nlinarith
  nlinarith [mul_lt_mul_of_pos_left h5 (pow_pos (Real.exp_pos (-(2 / 9))) 2)]

lemma ps_tendsto_tau2 : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * (tauN N / sigN N)) atTop (𝓝 0) := by
  simp_rw [ps_tau_sig]
  exact ps_tendsto_sq_mul_pow ps_r_nonneg ps_r_lt _

lemma ps_tendsto_eps2 : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * ps_eps N) atTop (𝓝 0) :=
  (ps_tendsto_sq_mul_pow (r := 99 / 100) (by norm_num) (by norm_num) 1).congr fun N => by
    simp [ps_eps]

lemma ps_tendsto_fg2 : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * fg2 N) atTop (𝓝 0) := by
  have hr : |Real.exp (2 / 3) / 2| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by norm_num)]
    exact exp_two_thirds_lt_two
  have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 3 hr).const_mul 4
  rw [mul_zero] at h
  refine h.congr fun N => ?_
  rw [fg2]
  ring

lemma ps_tendsto_D2 : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * ps_D N) atTop (𝓝 0) := by
  set K0 := Real.sqrt gbox_c2 * Real.sqrt (2 * Real.pi)
  have h := (ps_tendsto_tau2.const_mul (120 / K0)).add (ps_tendsto_eps2.const_mul (12 / K0))
  rw [mul_zero, mul_zero, add_zero] at h
  refine h.congr fun N => ?_
  rw [ps_D]
  ring

lemma ps_tendsto_D : Tendsto ps_D atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall ps_D_nonneg) ?_ ps_tendsto_D2
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hN)
  exact le_mul_of_one_le_left (ps_D_nonneg N) hN1

/-- The quantity controlling the variance term. -/
def ps_V (N : ℕ) : ℝ :=
  ps_pB ^ 2 * (2 * ps_D N + ps_D N ^ 2 + ps_err12 N) + fg2 N + 2 * (ps_pB * ps_err6 N + fg2 N)

/-- The final bound. -/
def ps_T (N : ℕ) : ℝ :=
  8 / ps_pB * (N : ℝ) ^ (-(3 / 20 : ℝ)) + 4 / ps_pB ^ 2 * ((N : ℝ) ^ 2 * ps_V N)

lemma ps_tendsto_T : Tendsto ps_T atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(3 / 20 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 20)).comp tendsto_natCast_atTop_atTop
  have h6 : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * ps_err6 N) atTop (𝓝 0) := ps_tendsto_err _ _
  have h12 : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * ps_err12 N) atTop (𝓝 0) := ps_tendsto_err _ _
  have hDD : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * ps_D N * ps_D N) atTop (𝓝 0) := by
    have := ps_tendsto_D2.mul ps_tendsto_D
    rwa [mul_zero] at this
  have hV : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * ps_V N) atTop (𝓝 0) := by
    have h := ((((ps_tendsto_D2.const_mul 2).add hDD).add h12).const_mul (ps_pB ^ 2)).add
      (ps_tendsto_fg2.add (((h6.const_mul ps_pB).add ps_tendsto_fg2).const_mul 2))
    simp only [mul_zero, add_zero] at h
    refine h.congr fun N => ?_
    rw [ps_V]
    ring
  have h := (h1.const_mul (8 / ps_pB)).add (hV.const_mul (4 / ps_pB ^ 2))
  simp only [mul_zero, add_zero] at h
  exact h

/-- Elementary form of the second moment bound. -/
lemma ps_final_alg {pB G ℓ u v a b M : ℝ} (hpB : 0 < pB) (hpB1 : pB ≤ 1) (hG1 : G ≤ 1) (hℓ : 0 < ℓ) (hℓG : ℓ ≤ G) (hu0 : 0 ≤ u) (hu : u ≤ pB * ℓ / 2) (hv : 0 ≤ v)
    (ha : a = pB * G - u) (hb : b ≤ pB ^ 2 * G ^ 2 + v) (hM : 0 < M) :
    0 < a ∧ 1 / (M * a) + b / a ^ 2 - 1 ≤ 2 / (M * (pB * ℓ)) + 4 * (v + 2 * u) / (pB * ℓ) ^ 2 := by
  have hpl : 0 < pB * ℓ := mul_pos hpB hℓ
  have ha' : pB * ℓ / 2 ≤ a := by
    rw [ha]; nlinarith [mul_le_mul_of_nonneg_left hℓG hpB.le]
  have ha0 : 0 < a := by linarith
  refine ⟨ha0, ?_⟩
  have h1 : 1 / (M * a) ≤ 2 / (M * (pB * ℓ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left ha' hM.le]
  have hpG : pB * G ≤ 1 := by nlinarith
  have h2 : b - a ^ 2 ≤ v + 2 * u := by
    rw [ha]; nlinarith [mul_le_mul_of_nonneg_right hpG hu0]
  have h3 : b / a ^ 2 - 1 = (b - a ^ 2) / a ^ 2 := by field_simp
  have h4 : (b - a ^ 2) / a ^ 2 ≤ (v + 2 * u) / a ^ 2 :=
    div_le_div_of_nonneg_right h2 (by positivity)
  have h5 : (v + 2 * u) / a ^ 2 ≤ 4 * (v + 2 * u) / (pB * ℓ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (pB * ℓ) ^ 2 ≤ 4 * a ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (by linarith : 0 ≤ v + 2 * u)]
  linarith

/-- **No pair `m < N/2` has its event** with probability tending to `0`, for every `s`. -/
theorem ps_tendsto_Z (s : ∀ N, State N) :
    Tendsto (fun N => (cubeM N).real (ps_Z N (s N))) atTop (𝓝 0) := by
  have hu : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * (ps_pB * ps_err6 N + fg2 N)) atTop (𝓝 0) := by
    have h := ((ps_tendsto_err 180 (3456 + 3 * gbox_C3 gbox_T6)).const_mul ps_pB).add
      ps_tendsto_fg2
    simp only [mul_zero, add_zero] at h
    refine h.congr fun N => ?_
    rw [ps_err6]
    ring
  have hsm : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * (4 * tauN N / sigN N + ps_eps N)) atTop
      (𝓝 0) := by
    have h := (ps_tendsto_tau2.const_mul 4).add ps_tendsto_eps2
    simp only [mul_zero, add_zero] at h
    refine h.congr fun N => ?_
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ps_tendsto_T
    (Eventually.of_forall fun N => measureReal_nonneg) ?_
  filter_upwards [eventually_ge_atTop 5, gbox_eventually_G6_box,
    hu.eventually (ge_mem_nhds (half_pos ps_pB_pos)),
    hsm.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 7 / 8))] with N hN hbox huN hsN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hN1
  have hpB := ps_pB_pos
  set ℓ := (N : ℝ) ^ (-(17 / 20 : ℝ)) with hℓdef
  have hℓpos : 0 < ℓ := Real.rpow_pos_of_pos hN0 _
  have hℓN : 1 / (N : ℝ) ≤ ℓ := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hτ : 0 ≤ 4 * tauN N / sigN N + ps_eps N := by
    have := tauN_pos N; have := sigN_pos N; have := ps_eps_pos N; positivity
  have hδ : 4 * tauN N / sigN N + ps_eps N ≤ 7 / 8 :=
    (le_mul_of_one_le_left hτ hN2).trans hsN
  have hG : ℓ ≤ ps_Glo N := by
    have h := hbox (4 * tauN N / sigN N + ps_eps N) hδ
    have e : ps_Glo N =
        gbox_G6.real {x | ∀ p, x p ≤ -2 * yN N - (4 * tauN N / sigN N + ps_eps N)} := by
      unfold ps_Glo
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor <;> intro h p <;> linarith [h p]
    rw [e]
    exact h
  set u := ps_pB * ps_err6 N + fg2 N with hudef
  have hu0 : 0 ≤ u := by
    have := ps_err_nonneg (C2 := 180) (C3 := 3456 + 3 * gbox_C3 gbox_T6) (by norm_num)
      (by have := gbox_C3_nonneg gbox_T6; positivity) N
    have := ps_fg2_nonneg N
    rw [hudef]; unfold ps_err6; positivity
  have huℓ : u ≤ ps_pB * ℓ / 2 := by
    have h1 : u ≤ ps_pB / 2 / (N : ℝ) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h2 : ps_pB / 2 / (N : ℝ) ^ 2 ≤ ps_pB / 2 / N :=
      div_le_div_of_nonneg_left (by positivity) hN0 (by nlinarith)
    have h3 : ps_pB / 2 / (N : ℝ) ≤ ps_pB * ℓ / 2 := by
      have := mul_le_mul_of_nonneg_left hℓN (by positivity : (0 : ℝ) ≤ ps_pB / 2)
      calc ps_pB / 2 / (N : ℝ) = ps_pB / 2 * (1 / N) := by ring
        _ ≤ ps_pB / 2 * ℓ := this
        _ = ps_pB * ℓ / 2 := by ring
    linarith
  set v := ps_pB ^ 2 * (2 * ps_D N + ps_D N ^ 2 + ps_err12 N) + fg2 N with hvdef
  have hD := ps_D_nonneg N
  have he12 : 0 ≤ ps_err12 N := ps_err_nonneg (by norm_num)
    (by have := gbox_C3_nonneg gbox_T12; positivity) N
  have hv0 : 0 ≤ v := by have := ps_fg2_nonneg N; rw [hvdef]; positivity
  have hG0 : 0 ≤ ps_Glo N := measureReal_nonneg
  have hG1 : ps_Glo N ≤ 1 := measureReal_le_one
  have hb : ps_lb N ≤ ps_pB ^ 2 * ps_Glo N ^ 2 + v := by
    have hH0 : 0 ≤ ps_Ghi N := measureReal_nonneg
    have hH : ps_Ghi N ^ 2 ≤ (ps_Glo N + ps_D N) ^ 2 :=
      pow_le_pow_left₀ hH0 (ps_Ghi_le N) 2
    have hH' : (ps_Glo N + ps_D N) ^ 2 ≤ ps_Glo N ^ 2 + 2 * ps_D N + ps_D N ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hG1 hD]
    unfold ps_lb
    rw [hvdef]
    nlinarith [mul_le_mul_of_nonneg_left (hH.trans hH') (sq_nonneg ps_pB)]
  have ha_eq : ps_la N = ps_pB * ps_Glo N - u := by rw [ps_la, hudef]; ring
  have hM : (0 : ℝ) < (N / 2 : ℕ) := by exact_mod_cast (by omega : 0 < N / 2)
  obtain ⟨ha, hfin⟩ := ps_final_alg hpB ps_pB_le_one hG1 hℓpos hG hu0 huℓ hv0 ha_eq hb hM
  have hZ := ps_bound hN (s N) ha
  refine hZ.trans (hfin.trans ?_)
  have hM4 : (N : ℝ) ≤ 4 * ((N / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : N ≤ 4 * (N / 2))
  have hNℓ : (N : ℝ) * ℓ = (N : ℝ) ^ (3 / 20 : ℝ) := by
    rw [hℓdef, ← Real.rpow_one_add' hN0.le (by norm_num)]
    norm_num
  have hNℓ1 : 1 ≤ (N : ℝ) * ℓ := by
    have := mul_le_mul_of_nonneg_left hℓN hN0.le
    rwa [mul_one_div_cancel hN0.ne'] at this
  have hT1 : 2 / (((N / 2 : ℕ) : ℝ) * (ps_pB * ℓ)) ≤ 8 / ps_pB * (N : ℝ) ^ (-(3 / 20 : ℝ)) := by
    rw [Real.rpow_neg hN0.le, ← hNℓ, div_le_iff₀ (by positivity)]
    have hpos : 0 < (N : ℝ) * ℓ := by positivity
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hM4 (by positivity : (0 : ℝ) ≤ ps_pB * ℓ)]
  have hT2 : 4 * (v + 2 * u) / (ps_pB * ℓ) ^ 2 ≤ 4 / ps_pB ^ 2 * ((N : ℝ) ^ 2 * ps_V N) := by
    have hVe : ps_V N = v + 2 * u := by rw [ps_V, hvdef, hudef]
    rw [hVe, div_le_iff₀ (by positivity)]
    have h1 : 1 ≤ ((N : ℝ) * ℓ) ^ 2 := one_le_pow₀ hNℓ1
    have e : 4 / ps_pB ^ 2 * ((N : ℝ) ^ 2 * (v + 2 * u)) * (ps_pB * ℓ) ^ 2 =
        4 * (v + 2 * u) * ((N : ℝ) * ℓ) ^ 2 := by
      field_simp
    rw [e]
    exact le_mul_of_one_le_right (by linarith) h1
  rw [ps_T]
  linarith

/-! ### The main theorem -/

/-- **Some pair wins the cause-side competition**: with probability tending to one, some pair
`{a, b}` has its effect box and the cause-side orthant event `inA` at level `yN N`. -/
theorem tendsto_noPairOrthant (s : ∀ N, State N) :
    Tendsto (fun N => volume {z | z ∈ cube N ∧ ¬ ∃ a b : Fin N, a ≠ b ∧
      effBox z (s N) a b ∧ inA (flipP (s N) z) a b (yN N)}) atTop (𝓝 0) := by
  have hR : Tendsto (fun N => ENNReal.ofReal ((cubeM N).real (ps_Z N (s N)))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (ps_tendsto_Z s)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hR (fun _ => zero_le)
    fun N => ?_
  have hsub : {z | z ∈ cube N ∧ ¬ ∃ a b : Fin N, a ≠ b ∧
      effBox z (s N) a b ∧ inA (flipP (s N) z) a b (yN N)} ⊆
      flipE (s N) ⁻¹' (cube N ∩ ps_Z N (s N)) := by
    rintro z ⟨hz, hno⟩
    refine ⟨flipP_cube hz (s N), fun m hm => hno ⟨ps_a N m, ps_b N m, ps_ab_ne m, ?_,
      ps_E_inA hm.1⟩⟩
    have h := ps_box_effBox (ps_ab_ne m) hm.2
    have e : flipP (s N) (flipE (s N) z) = z := flipP_invol (s N) z
    rwa [e] at h
  calc volume {z | z ∈ cube N ∧ ¬ ∃ a b : Fin N, a ≠ b ∧
        effBox z (s N) a b ∧ inA (flipP (s N) z) a b (yN N)}
      ≤ volume (flipE (s N) ⁻¹' (cube N ∩ ps_Z N (s N))) := measure_mono hsub
    _ = cubeM N (ps_Z N (s N)) := by
        rw [(mp_flipE (s N)).measure_preimage_equiv, volume_cube_inter]
    _ = ENNReal.ofReal ((cubeM N).real (ps_Z N (s N))) := (ofReal_measureReal).symm

end

end Census
end IIT
