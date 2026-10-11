/-
Census of complexes: probability bounds for the parts of the good event that condition on all
columns but one.

Under `cubeM N`, each of the following fails with probability at most an explicit function of `N`
tending to `0`:
* `g11`: `|Zs - ZQ i / 2| ≤ 16 N σ_N` for every `i` (Hoeffding over the entries of column `i`
  given the other columns, with variance proxy `SQ2 w i`, combined with `g4`);
* `g13a`: `|Num - cNum| ≤ 2 √(L Vp)` with `L = LkN N |S|` (Hoeffding over the `S`-blocks of
  column `i` given the other columns, union over `S`, `i`, `Y` and the patterns on `S`);
* `g16`: every effect-side cut mean `qW w s S j b` with `|S| > K2N N` is at least `1/4`
  (Hoeffding over the `2^{|S|-1}` independent entries, union over `S`, `j`, `b`), uniformly in `s`.
-/
import IIT.Census.Bernstein
import IIT.Census.ColSplit
import IIT.Census.BigPhiProbBasic
import IIT.Census.BigPhiProbSub

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

noncomputable section

variable {N : ℕ}

lemma measurable_abs_comp {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f) :
    Measurable fun a => |f a| :=
  continuous_abs.measurable.comp hf

/-! ### `g11`: the normalisation against the half-sum without one column -/

/-- The failure probability of `g11`. -/
def fg11 (N : ℕ) : ℝ := fg4 N + 2 * N * Real.exp (-1) ^ N

lemma cubeM_g11_inter (i : Fin N) :
    cubeM N ({w | ¬ |Zs w - ZQ w i / 2| ≤ 16 * N * sigN N} ∩
      {w | SQ2 w i ≤ 6 * (2 / 3 : ℝ) ^ N}) ≤ ENNReal.ofReal (2 * Real.exp (-1) ^ N) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast i.pos
  have hmX : MeasurableSet {w : Param N | ¬ |Zs w - ZQ w i / 2| ≤ 16 * N * sigN N} :=
    (measurableSet_le (measurable_abs_comp (measurable_Zs.sub ((measurable_ZQ i).div_const 2)))
      measurable_const).compl
  have hmG : MeasurableSet {w : Param N | SQ2 w i ≤ 6 * (2 / 3 : ℝ) ^ N} :=
    measurableSet_le (measurable_SQ2 i) measurable_const
  refine cubeM_inter_le_of_fiber i hmX hmG fun ρ c hc => ?_
  simp only [Set.mem_ofPred_eq] at hc
  set Q : State N → ℝ := fun r => Qw (glue i c ρ) i r with hQ
  have hQ0 : ∀ r, 0 ≤ Q r := fun r => Qw_nonneg _ i r
  have hZs : ∀ c', Zs (glue i c' ρ) - ZQ (glue i c' ρ) i / 2 =
      ∑ r, (clamp01 (c' r) * Q r - Q r / 2) := by
    intro c'
    rw [Zs_glue i c' c, ZQ_glue i c' c, ZQ, sum_sub_distrib, sum_div]
  have hSQ : SQ2 (glue i c ρ) i = ∑ r, Q r ^ 2 := rfl
  by_cases h0 : SQ2 (glue i c ρ) i = 0
  · -- all row products vanish: the fibre is empty
    have hQz : ∀ r, Q r = 0 := by
      intro r
      rw [hSQ] at h0
      have := (sum_eq_zero_iff_of_nonneg fun r _ => sq_nonneg (Q r)).1 h0 r (mem_univ r)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    have hE : {c' | glue i c' ρ ∈ {w : Param N | ¬ |Zs w - ZQ w i / 2| ≤ 16 * N * sigN N}} = ∅ := by
      ext c'
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      rw [hZs c']
      simp only [hQz, mul_zero, zero_div, sub_zero, sum_const_zero, abs_zero]
      have := sigN_pos N
      positivity
    rw [hE, measure_empty]
    exact zero_le
  have hpos : 0 < SQ2 (glue i c ρ) i :=
    lt_of_le_of_ne (sum_nonneg fun r _ => sq_nonneg _) (Ne.symm h0)
  set ε : ℝ := 16 * N * sigN N with hε
  have hε0 : 0 ≤ ε := by have := sigN_pos N; positivity
  have hind := iIndepFun_col (N := N) (fun r x => clamp01 x * Q r)
    (fun r => clamp01_measurable.mul_const _)
  have hmeas : ∀ r, AEMeasurable (fun c' : State N → ℝ => clamp01 (c' r) * Q r) (colLaw N) :=
    fun r => ((clamp01_measurable.comp (measurable_pi_apply r)).mul_const _).aemeasurable
  have hb : ∀ r ∈ (univ : Finset (State N)), ∀ᵐ c' ∂colLaw N,
      clamp01 (c' r) * Q r ∈ Set.Icc 0 (Q r) := fun r _ => ae_of_all _ fun c' =>
    ⟨mul_nonneg (clamp01_nonneg _) (hQ0 r),
      mul_le_of_le_one_left (hQ0 r) (clamp01_le_one _)⟩
  have h := hoeffding_abs (μ := colLaw N) (X := fun r (c' : State N → ℝ) => clamp01 (c' r) * Q r)
    univ hind hmeas hb hε0
  have hmean : ∀ r, ∫ c', clamp01 (c' r) * Q r ∂colLaw N = Q r / 2 := by
    intro r
    rw [integral_mul_const, integral_col]; ring
  simp only [hmean] at h
  have hsub : {c' | glue i c' ρ ∈ {w : Param N | ¬ |Zs w - ZQ w i / 2| ≤ 16 * N * sigN N}} ⊆
      {c' | ε ≤ |∑ r, (clamp01 (c' r) * Q r - Q r / 2)|} := by
    intro c' hc'
    simp only [Set.mem_ofPred_eq, not_le] at hc' ⊢
    rw [← hZs c']
    exact hc'.le
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (h.trans ?_)
  rw [← hSQ]
  have hsig : sigN N ^ 2 = (2 / 3 : ℝ) ^ N := Real.sq_sqrt (by positivity)
  have hε2 : ε ^ 2 = 256 * (N : ℝ) ^ 2 * (2 / 3 : ℝ) ^ N := by
    rw [hε, mul_pow, mul_pow, hsig]; ring
  have hkey : -2 * ε ^ 2 / SQ2 (glue i c ρ) i ≤ -(N : ℝ) := by
    rw [div_le_iff₀ hpos, hε2]
    have ha : (0 : ℝ) < (2 / 3 : ℝ) ^ N := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ N)]
  have := Real.exp_le_exp.2 hkey
  rw [show -(N : ℝ) = N * (-1) by ring, Real.exp_nat_mul] at this
  linarith

/-- **`g11` fails with probability at most `fg11 N`.** -/
theorem cubeM_not_g11 :
    cubeM N {w | ¬ ∀ i, |Zs w - ZQ w i / 2| ≤ 16 * N * sigN N} ≤ ENNReal.ofReal (fg11 N) := by
  have hsub : {w : Param N | ¬ ∀ i, |Zs w - ZQ w i / 2| ≤ 16 * N * sigN N} ⊆
      {w | ¬ ∀ i, SQ2 w i ≤ 6 * (2 / 3 : ℝ) ^ N} ∪
        ⋃ i, ({w | ¬ |Zs w - ZQ w i / 2| ≤ 16 * N * sigN N} ∩
          {w | SQ2 w i ≤ 6 * (2 / 3 : ℝ) ^ N}) := by
    intro w hw
    by_cases h4 : ∀ i, SQ2 w i ≤ 6 * (2 / 3 : ℝ) ^ N
    · right
      simp only [Set.mem_ofPred_eq, not_forall] at hw
      obtain ⟨i, hi⟩ := hw
      exact Set.mem_iUnion.2 ⟨i, hi, h4 i⟩
    · exact Or.inl h4
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hU := cubeM_iUnion_le _ fun i => cubeM_g11_inter (N := N) i
  rw [Fintype.card_fin] at hU
  refine (add_le_add cubeM_not_g4 hU).trans ?_
  rw [← ENNReal.ofReal_add (by unfold fg4; positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  unfold fg11; ring_nf; rfl

theorem tendsto_fg11 : Tendsto fg11 atTop (𝓝 0) := by
  have h := (tendsto_self_mul_const_pow_of_lt_one (r := Real.exp (-1)) (by positivity)
    (Real.exp_lt_one_iff.2 (by norm_num))).const_mul 2
  rw [mul_zero] at h
  have h2 := tendsto_fg4.add h
  rw [add_zero] at h2
  refine h2.congr fun N => ?_
  unfold fg11; ring

/-! ### `g13a`: the conditioned cause numerators -/

section G13a

/-- The `S`-block label of a row: the row with its bits in `S` cleared. -/
def blk (S : Finset (Fin N)) (r : State N) : State N := merge S (fun _ => false) r

lemma blk_eq_iff {S : Finset (Fin N)} {r r' : State N} :
    blk S r' = blk S r ↔ r' ∈ agree Sᶜ r := by
  rw [mem_agree]
  constructor
  · intro h j hj
    have := congrFun h j
    simpa [blk, merge_not_mem (mem_compl.1 hj)] using this
  · intro h
    funext j
    by_cases hj : j ∈ S
    · simp [blk, merge_mem hj]
    · simp [blk, merge_not_mem hj, h j (mem_compl.2 hj)]

lemma filter_blk_eq (S : Finset (Fin N)) (v : State N) :
    univ.filter (fun r => blk S r = blk S v) = agree Sᶜ v := by
  ext r
  simp only [mem_filter, mem_univ, true_and]
  exact blk_eq_iff

variable {S Y : Finset (Fin N)} {t : State N}

lemma blk_of_mem_cond {v r : State N} (hr : r ∈ agree (Y ∪ Sᶜ) (merge S t v)) :
    blk S r = blk S v := by
  rw [blk_eq_iff, mem_agree]
  intro j hj
  have := (mem_agree.1 hr) j (mem_union_right _ hj)
  rwa [merge_not_mem (mem_compl.1 hj)] at this

lemma card_cond (hY : Y ⊆ S) (t v : State N) :
    (agree (Y ∪ Sᶜ) (merge S t v)).card = 2 ^ (S.card - Y.card) := by
  rw [card_agree]
  congr 1
  have hd : Disjoint Y Sᶜ := disjoint_left.2 fun a ha hb => (mem_compl.1 hb) (hY ha)
  have hc : (Y ∪ Sᶜ).card = Y.card + (N - S.card) := by
    rw [card_union_of_disjoint hd, card_compl, Fintype.card_fin]
  have h1 : Y.card ≤ S.card := card_le_card hY
  have h2 : S.card ≤ N := by simpa [Fintype.card_fin] using card_le_univ S
  omega

lemma self_mem_cond_iff (hY : Y ⊆ S) (v : State N) :
    v ∈ agree (Y ∪ Sᶜ) (merge S t v) ↔ v ∈ agree Y t := by
  simp only [mem_agree, mem_union, mem_compl]
  constructor
  · intro h j hj
    have := h j (Or.inl hj)
    rwa [merge_mem (hY hj)] at this
  · rintro h j (hj | hj)
    · rw [merge_mem (hY hj)]; exact h j hj
    · rw [merge_not_mem hj]

lemma agree_cond_congr {t t' : State N} (h : ∀ j ∈ Y, t j = t' j) (v : State N) :
    agree (Y ∪ Sᶜ) (merge S t v) = agree (Y ∪ Sᶜ) (merge S t' v) := by
  ext r
  simp only [mem_agree, mem_union, mem_compl]
  refine forall₂_congr fun j hj => ?_
  by_cases hjS : j ∈ S
  · have hjY : j ∈ Y := hj.resolve_right (not_not.2 hjS)
    rw [merge_mem hjS, merge_mem hjS, h j hjY]
  · rw [merge_not_mem hjS, merge_not_mem hjS]

variable (S Y t)

/-- `Num` on a fibre, as a function of the column: `Q` are the row products without the column. -/
def Fnum (Q : State N → ℝ) (c : State N → ℝ) : ℝ :=
  ∑ v, (∑ r ∈ agree (Y ∪ Sᶜ) (merge S t v), clamp01 (c r)) / 2 ^ (S.card - Y.card) *
    (clamp01 (c v) * Q v)

/-- The conditional mean of `Fnum`. -/
def Cm (Q : State N → ℝ) : ℝ :=
  (∑ v, Q v) / 4 + (∑ v ∈ agree Y t, Q v) / (12 * (2 : ℝ) ^ (S.card - Y.card))

/-- The variance proxy of `Fnum`. -/
def Vq (Q : State N → ℝ) : ℝ := ∑ v, Q v * ∑ r ∈ agree Sᶜ v, Q r

/-- The contribution of the `S`-block with label `β` to `Fnum`. -/
def Hb (Q : State N → ℝ) (β : State N) (c : State N → ℝ) : ℝ :=
  ∑ v ∈ univ.filter (fun v => blk S v = β),
    (∑ r ∈ agree (Y ∪ Sᶜ) (merge S t v), clamp01 (c r)) / 2 ^ (S.card - Y.card) *
      (clamp01 (c v) * Q v)

/-- The `Q`-mass of the `S`-block with label `β`. -/
def cb (Q : State N → ℝ) (β : State N) : ℝ := ∑ v ∈ univ.filter (fun v => blk S v = β), Q v

lemma sum_Hb (Q : State N → ℝ) (c : State N → ℝ) : ∑ β, Hb S Y t Q β c = Fnum S Y t Q c :=
  sum_fiberwise univ (blk S) _

lemma Hb_congr (Q : State N → ℝ) (β : State N) {c c' : State N → ℝ}
    (h : ∀ r, blk S r = β → c r = c' r) : Hb S Y t Q β c = Hb S Y t Q β c' := by
  unfold Hb
  refine sum_congr rfl fun v hv => ?_
  have hvb : blk S v = β := (mem_filter.1 hv).2
  rw [h v hvb, sum_congr rfl fun r hr => by rw [h r ((blk_of_mem_cond hr).trans hvb)]]

lemma measurable_Hb (Q : State N → ℝ) (β : State N) : Measurable (Hb S Y t Q β) :=
  Finset.measurable_sum _ fun v _ =>
    ((Finset.measurable_sum _ fun r _ => clamp01_measurable.comp (measurable_pi_apply r)).div_const
      _).mul ((clamp01_measurable.comp (measurable_pi_apply v)).mul_const _)

/-- Extension by zero of a function on one block. -/
def extB (β : State N) (y : {r // blk S r = β} → ℝ) : State N → ℝ :=
  fun r => if h : blk S r = β then y ⟨r, h⟩ else 0

lemma measurable_extB (β : State N) : Measurable (extB S β) := by
  refine Measurable.of_eval fun r => ?_
  by_cases h : blk S r = β
  · simp only [extB, h, ↓reduceDIte]; exact measurable_pi_apply _
  · simp only [extB, h, ↓reduceDIte]; exact measurable_const

/-- The block terms are independent under the column law. -/
lemma iIndepFun_Hb (Q : State N → ℝ) :
    iIndepFun (fun β (c : State N → ℝ) => Hb S Y t Q β c) (colLaw N) := by
  have h := (iIndepFun_fib (blk S) unif).comp (fun β y => Hb S Y t Q β (extB S β y))
    (fun β => (measurable_Hb S Y t Q β).comp (measurable_extB S β))
  unfold colLaw
  convert h using 1
  funext β c
  simp only [Function.comp]
  refine Hb_congr S Y t Q β fun r hr => ?_
  simp [extB, fib, hr]

lemma Hb_mem (hY : Y ⊆ S) {Q : State N → ℝ} (hQ : ∀ r, 0 ≤ Q r) (β : State N)
    (c : State N → ℝ) : Hb S Y t Q β c ∈ Set.Icc 0 (cb S Q β) := by
  have hm : ∀ v, 0 ≤ (∑ r ∈ agree (Y ∪ Sᶜ) (merge S t v), clamp01 (c r)) /
      (2 : ℝ) ^ (S.card - Y.card) ∧
      (∑ r ∈ agree (Y ∪ Sᶜ) (merge S t v), clamp01 (c r)) / (2 : ℝ) ^ (S.card - Y.card) ≤ 1 := by
    intro v
    refine ⟨div_nonneg (sum_nonneg fun r _ => clamp01_nonneg _) (by positivity), ?_⟩
    rw [div_le_one (by positivity)]
    calc ∑ r ∈ agree (Y ∪ Sᶜ) (merge S t v), clamp01 (c r)
        ≤ ∑ _r ∈ agree (Y ∪ Sᶜ) (merge S t v), (1 : ℝ) := sum_le_sum fun r _ => clamp01_le_one _
      _ = (2 : ℝ) ^ (S.card - Y.card) := by
          rw [sum_const, card_cond hY, nsmul_one]; push_cast; rfl
  constructor
  · exact sum_nonneg fun v _ => mul_nonneg (hm v).1 (mul_nonneg (clamp01_nonneg _) (hQ v))
  · refine sum_le_sum fun v _ => ?_
    calc _ ≤ 1 * (1 * Q v) :=
          mul_le_mul (hm v).2 (mul_le_mul_of_nonneg_right (clamp01_le_one _) (hQ v))
            (mul_nonneg (clamp01_nonneg _) (hQ v)) zero_le_one
      _ = Q v := by ring

lemma integrable_Hb (Q : State N → ℝ) (β : State N) : Integrable (Hb S Y t Q β) (colLaw N) := by
  refine integrable_of_bdd_col (measurable_Hb S Y t Q β)
    (∑ v ∈ univ.filter (fun v => blk S v = β),
      ((agree (Y ∪ Sᶜ) (merge S t v)).card / 2 ^ (S.card - Y.card) * |Q v|)) fun c => ?_
  unfold Hb
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v _ => ?_)
  rw [abs_mul, abs_mul, abs_div, abs_of_nonneg (clamp01_nonneg _),
    abs_of_nonneg (sum_nonneg fun r _ => clamp01_nonneg _), abs_of_pos (by positivity)]
  have h1 : ∑ r ∈ agree (Y ∪ Sᶜ) (merge S t v), clamp01 (c r) ≤
      (agree (Y ∪ Sᶜ) (merge S t v)).card := by
    calc _ ≤ ∑ _r ∈ agree (Y ∪ Sᶜ) (merge S t v), (1 : ℝ) := sum_le_sum fun r _ => clamp01_le_one _
      _ = _ := by rw [sum_const, nsmul_one]
  have h2 := clamp01_le_one (c v)
  have h3 := clamp01_nonneg (c v)
  have h4 : 0 ≤ ∑ r ∈ agree (Y ∪ Sᶜ) (merge S t v), clamp01 (c r) :=
    sum_nonneg fun r _ => clamp01_nonneg _
  have h5 : (0 : ℝ) < 2 ^ (S.card - Y.card) := by positivity
  have h6 := abs_nonneg (Q v)
  gcongr
  calc clamp01 (c v) * |Q v| ≤ 1 * |Q v| := mul_le_mul_of_nonneg_right h2 h6
    _ = |Q v| := one_mul _

/-- The exact mean of `Fnum` under the column law. -/
lemma integral_Fnum (hY : Y ⊆ S) (Q : State N → ℝ) :
    ∫ c, Fnum S Y t Q c ∂colLaw N = Cm S Y t Q := by
  have hrw : ∀ c, Fnum S Y t Q c = ∑ v, ∑ r ∈ agree (Y ∪ Sᶜ) (merge S t v),
      Q v / 2 ^ (S.card - Y.card) * (clamp01 (c r) * clamp01 (c v)) := by
    intro c
    unfold Fnum
    refine sum_congr rfl fun v _ => ?_
    rw [sum_div, sum_mul]
    refine sum_congr rfl fun r _ => ?_
    ring
  have hint : ∀ r v : State N, Integrable (fun c : State N → ℝ =>
      Q v / 2 ^ (S.card - Y.card) * (clamp01 (c r) * clamp01 (c v))) (colLaw N) := by
    intro r v
    refine Integrable.const_mul ?_ _
    refine integrable_of_bdd_col ((clamp01_measurable.comp (measurable_pi_apply r)).mul
      (clamp01_measurable.comp (measurable_pi_apply v))) 1 fun c => ?_
    rw [abs_of_nonneg (mul_nonneg (clamp01_nonneg _) (clamp01_nonneg _))]
    exact (mul_le_mul_of_nonneg_right (clamp01_le_one _) (clamp01_nonneg _)).trans
      (by rw [one_mul]; exact clamp01_le_one _)
  simp_rw [hrw]
  rw [integral_finsetSum _ fun v _ => integrable_finsetSum _ fun r _ => hint r v]
  simp_rw [integral_finsetSum _ fun r _ => hint r _, integral_const_mul, integral_col_mul]
  have hin : ∀ v, ∑ r ∈ agree (Y ∪ Sᶜ) (merge S t v),
      Q v / 2 ^ (S.card - Y.card) * (if r = v then (1 / 3 : ℝ) else 1 / 4) =
      Q v / 4 + (if v ∈ agree Y t then Q v / (12 * 2 ^ (S.card - Y.card)) else 0) := by
    intro v
    have e : ∀ r, (if r = v then (1 / 3 : ℝ) else 1 / 4) = 1 / 4 + if r = v then 1 / 12 else 0 := by
      intro r; split_ifs <;> norm_num
    simp_rw [e, mul_add, sum_add_distrib, sum_const, card_cond hY, mul_ite, mul_zero,
      sum_ite_eq', self_mem_cond_iff hY]
    have h5 : (0 : ℝ) < 2 ^ (S.card - Y.card) := by positivity
    congr 1
    · rw [nsmul_eq_mul]; push_cast; field_simp
    · split_ifs <;> [field_simp; rfl]
  simp_rw [hin]
  rw [sum_add_distrib, ← sum_div, Fintype.sum_ite_mem, ← sum_div]
  rfl

lemma sum_cb_sq (Q : State N → ℝ) : ∑ β, cb S Q β ^ 2 = Vq S Q := by
  have h : ∀ β, cb S Q β ^ 2 = ∑ v ∈ univ.filter (fun v => blk S v = β), Q v * cb S Q (blk S v) := by
    intro β
    rw [sq, cb, sum_mul]
    refine sum_congr rfl fun v hv => ?_
    rw [(mem_filter.1 hv).2]
    rfl
  simp_rw [h]
  rw [sum_fiberwise univ (blk S) (fun v => Q v * cb S Q (blk S v))]
  refine sum_congr rfl fun v _ => ?_
  rw [cb, filter_blk_eq]

lemma Vq_nonneg {Q : State N → ℝ} (hQ : ∀ r, 0 ≤ Q r) : 0 ≤ Vq S Q :=
  sum_nonneg fun v _ => mul_nonneg (hQ v) (sum_nonneg fun r _ => hQ r)

/-- **Hoeffding over the blocks of one column.** -/
theorem colLaw_Fnum_dev (hY : Y ⊆ S) {Q : State N → ℝ} (hQ : ∀ r, 0 ≤ Q r) {L : ℝ} (hL : 0 ≤ L) :
    colLaw N {c | ¬ |Fnum S Y t Q c - Cm S Y t Q| ≤ 2 * Real.sqrt (L * Vq S Q)} ≤
      ENNReal.ofReal (2 * Real.exp (-8 * L)) := by
  have hmean : ∑ β, ∫ c, Hb S Y t Q β c ∂colLaw N = Cm S Y t Q := by
    rw [← integral_finsetSum _ fun β _ => integrable_Hb S Y t Q β, ← integral_Fnum S Y t hY Q]
    exact integral_congr_ae (ae_of_all _ fun c => sum_Hb S Y t Q c)
  have hD : ∀ c, Fnum S Y t Q c - Cm S Y t Q =
      ∑ β, (Hb S Y t Q β c - ∫ c', Hb S Y t Q β c' ∂colLaw N) := by
    intro c
    rw [sum_sub_distrib, sum_Hb, hmean]
  by_cases hV0 : Vq S Q = 0
  · have hcb : ∀ β, cb S Q β = 0 := by
      intro β
      rw [← sum_cb_sq] at hV0
      have := (sum_eq_zero_iff_of_nonneg fun β _ => sq_nonneg (cb S Q β)).1 hV0 β (mem_univ β)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    have hH : ∀ β c, Hb S Y t Q β c = 0 := by
      intro β c
      have := Hb_mem S Y t hY hQ β c
      rw [hcb] at this
      exact le_antisymm this.2 this.1
    have hE : {c | ¬ |Fnum S Y t Q c - Cm S Y t Q| ≤ 2 * Real.sqrt (L * Vq S Q)} = ∅ := by
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      rw [hD c]
      simp only [hH, integral_zero, sub_zero, sum_const_zero, abs_zero]
      positivity
    rw [hE, measure_empty]
    exact zero_le
  have hVpos : 0 < Vq S Q := lt_of_le_of_ne (Vq_nonneg S hQ) (Ne.symm hV0)
  set ε := 2 * Real.sqrt (L * Vq S Q) with hε
  have hε0 : 0 ≤ ε := by positivity
  have h := hoeffding_abs (μ := colLaw N) (X := fun β (c : State N → ℝ) => Hb S Y t Q β c)
    (c := cb S Q) univ (iIndepFun_Hb S Y t Q)
    (fun β => (measurable_Hb S Y t Q β).aemeasurable)
    (fun β _ => ae_of_all _ fun c => Hb_mem S Y t hY hQ β c) hε0
  have hsub : {c | ¬ |Fnum S Y t Q c - Cm S Y t Q| ≤ ε} ⊆
      {c | ε ≤ |∑ β, (Hb S Y t Q β c - ∫ c', Hb S Y t Q β c' ∂colLaw N)|} := by
    intro c hc
    simp only [Set.mem_ofPred_eq, not_le] at hc ⊢
    rw [← hD c]
    exact hc.le
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
  rw [sum_cb_sq, hε, mul_pow, Real.sq_sqrt (mul_nonneg hL hVpos.le)]
  congr 2
  field_simp
  ring

/-- `Num` on the fibre of column `i`. -/
lemma Num_glue (i : Fin N) (c : State N → ℝ) (ρ : Rest N i) :
    Num (glue i c ρ) S Y t i = Fnum S Y t (fun r => Qw (glue i (fun _ => 0) ρ) i r) c := by
  unfold Num meanW Fnum
  refine sum_congr rfl fun v _ => ?_
  rw [Pw_glue i c (fun _ => 0) ρ v]
  simp only [glue_self]

lemma measurable_Num (i : Fin N) : Measurable fun w : Param N => Num w S Y t i :=
  Finset.measurable_sum _ fun v _ =>
    ((Finset.measurable_sum _ fun r _ => clamp01_measurable.comp
      ((measurable_pi_apply i).comp (measurable_pi_apply r))).div_const _).mul (measurable_Pw v)

lemma measurable_cNum (i : Fin N) : Measurable fun w : Param N => cNum w S Y t i :=
  ((measurable_ZQ i).div_const 4).add ((measurable_subSum i Y t).div_const _)

lemma measurable_Vp (i : Fin N) : Measurable fun w : Param N => Vp w i S :=
  Finset.measurable_sum _ fun r _ => (measurable_Qw i r).mul (measurable_subSum i Sᶜ r)

/-- The bad event of `g13a` for one pattern. -/
def badNum (S : Finset (Fin N)) (i : Fin N) (Y : Finset (Fin N)) (t : State N) : Set (Param N) :=
  {w | ¬ |Num w S Y t i - cNum w S Y t i| ≤ 2 * Real.sqrt (LkN N S.card * Vp w i S)}

/-- **Deviation of `Num` from its conditional mean**, for one pattern. -/
lemma cubeM_badNum (i : Fin N) (hY : Y ⊆ S) :
    cubeM N (badNum S i Y t) ≤ ENNReal.ofReal (2 * Real.exp (-8 * LkN N S.card)) := by
  have hL : 0 ≤ LkN N S.card := by
    unfold LkN
    have := Real.log_natCast_nonneg N
    positivity
  have hm : MeasurableSet (badNum S i Y t) :=
    (measurableSet_le (measurable_abs_comp ((measurable_Num S Y t i).sub (measurable_cNum S Y t i)))
      (measurable_const.mul (Real.continuous_sqrt.measurable.comp
        (measurable_const.mul (measurable_Vp S i))))).compl
  refine cubeM_le_of_fiber i hm fun ρ => ?_
  have hQ : ∀ r, 0 ≤ Qw (glue i (fun _ => 0) ρ) i r := fun r => Qw_nonneg _ i r
  refine le_of_eq_of_le ?_ (colLaw_Fnum_dev S Y t hY hQ hL)
  congr 1
  ext c
  simp only [badNum, Set.mem_ofPred_eq]
  rw [Num_glue, cNum_glue i c (fun _ => 0), Vp_glue i c (fun _ => 0)]
  rfl

end G13a

lemma Num_congr {S Y : Finset (Fin N)} {t t' : State N} (h : ∀ j ∈ Y, t j = t' j)
    (w : Param N) (i : Fin N) : Num w S Y t i = Num w S Y t' i := by
  unfold Num meanW
  simp_rw [agree_cond_congr h]

lemma cNum_indS (w : Param N) {S Y : Finset (Fin N)} (hY : Y ⊆ S) (t : State N) (i : Fin N) :
    cNum w S Y t i = cNum w S Y (indS (S.filter fun j => t j = true)) i := by
  unfold cNum subSum
  rw [agree_indS hY t]

lemma indS_eq_on {S Y : Finset (Fin N)} (hY : Y ⊆ S) (t : State N) :
    ∀ j ∈ Y, t j = indS (S.filter fun j => t j = true) j := by
  intro j hj
  simp [indS, hY hj]

/-- All bad patterns of `g13a` for one candidate `S`. -/
def badNumS (S : Finset (Fin N)) : Set (Param N) :=
  ⋃ i ∈ S, ⋃ Y ∈ S.powerset, ⋃ T ∈ S.powerset, badNum S i Y (indS T)

lemma cubeM_badNumS (S : Finset (Fin N)) : cubeM N (badNumS S) ≤ ENNReal.ofReal (bS N S.card) := by
  have h : cubeM N (badNumS S) ≤ ENNReal.ofReal (S.card * (S.powerset.card *
      (S.powerset.card * (2 * Real.exp (-8 * LkN N S.card))))) := by
    unfold badNumS
    refine cubeM_biUnion_le _ _ fun i _ => ?_
    refine cubeM_biUnion_le _ _ fun Y hY => ?_
    refine cubeM_biUnion_le _ _ fun T _ => ?_
    exact cubeM_badNum S Y (indS T) i (mem_powerset.1 hY)
  rw [card_powerset] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  unfold bS
  have hL : 0 ≤ LkN N S.card := by
    unfold LkN
    have := Real.log_natCast_nonneg N
    positivity
  have h1 : (1 : ℝ) ≤ 2 ^ S.card := one_le_pow₀ (by norm_num)
  have h2 : Real.exp (-8 * LkN N S.card) ≤ Real.exp (-6 * LkN N S.card) :=
    Real.exp_le_exp.2 (by linarith)
  have h3 : 2 * Real.exp (-8 * LkN N S.card) ≤ 2 ^ S.card * (2 * Real.exp (-6 * LkN N S.card)) := by
    have := Real.exp_pos (-6 * LkN N S.card)
    nlinarith
  push_cast
  gcongr

/-- The failure probability of `g13a`. -/
def fg13a (N : ℕ) : ℝ := 2 * Real.exp 1 * (1 / (N : ℝ)) ^ 11

/-- **`g13a` fails with probability at most `fg13a N`.** -/
theorem cubeM_not_g13a :
    cubeM N {w | ¬ ∀ (S : Finset (Fin N)) i (Y : Finset (Fin N)) t, i ∈ S → Y ⊆ S →
      |Num w S Y t i - cNum w S Y t i| ≤ 2 * Real.sqrt (LkN N S.card * Vp w i S)} ≤
      ENNReal.ofReal (fg13a N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hE : {w : Param 0 | ¬ ∀ (S : Finset (Fin 0)) i (Y : Finset (Fin 0)) t, i ∈ S → Y ⊆ S →
        |Num w S Y t i - cNum w S Y t i| ≤ 2 * Real.sqrt (LkN 0 S.card * Vp w i S)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun w hw => hw fun S i => i.elim0
    rw [hE, measure_empty]
    exact bot_le
  have hsub : {w : Param N | ¬ ∀ (S : Finset (Fin N)) i (Y : Finset (Fin N)) t, i ∈ S → Y ⊆ S →
      |Num w S Y t i - cNum w S Y t i| ≤ 2 * Real.sqrt (LkN N S.card * Vp w i S)} ⊆
      ⋃ S : Finset (Fin N), badNumS S := by
    intro w hw
    simp only [Set.mem_ofPred_eq, not_forall] at hw
    obtain ⟨S, i, Y, t, hi, hY, h⟩ := hw
    simp only [Set.mem_iUnion, badNumS, mem_powerset, exists_prop]
    refine ⟨S, i, hi, Y, hY, S.filter fun j => t j = true, filter_subset _ _, ?_⟩
    simp only [badNum, Set.mem_ofPred_eq]
    rwa [← Num_congr (indS_eq_on hY t), ← cNum_indS w hY t i]
  refine (measure_mono hsub).trans ?_
  have hU : cubeM N (⋃ S : Finset (Fin N), badNumS S) ≤
      ENNReal.ofReal (∑ S : Finset (Fin N), bS N S.card) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun S _ => bS_nonneg N S.card]
    exact (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun S _ => cubeM_badNumS S)
  exact hU.trans (ENNReal.ofReal_le_ofReal (sum_bS_le hN))

theorem tendsto_fg13a : Tendsto fg13a atTop (𝓝 0) := by
  have h := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 11).const_mul (2 * Real.exp 1)
  rw [zero_pow (by norm_num), mul_zero] at h
  exact h

/-! ### `g16`: the effect-side cut means near the whole substrate -/

/-- The probability that an entry produces the bit `b` against the current bit `a`. -/
def gq (a b : Bool) (x : ℝ) : ℝ := if b = a then clamp01 x else 1 - clamp01 x

lemma measurable_gq (a b : Bool) : Measurable (gq a b) := by
  unfold gq
  by_cases h : b = a
  · simp only [h, ite_true]; exact clamp01_measurable
  · simp only [h, ite_false]; exact measurable_const.sub clamp01_measurable

lemma gq_mem (a b : Bool) (x : ℝ) : gq a b x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold gq
  have h0 := clamp01_nonneg x
  have h1 := clamp01_le_one x
  split_ifs
  · exact ⟨h0, h1⟩
  · exact ⟨by linarith, by linarith⟩

lemma integral_gq (a b : Bool) : ∫ x, gq a b x ∂unif = 1 / 2 := by
  have h1 := integral_cl_pow 1
  simp only [pow_one] at h1
  unfold gq
  by_cases h : b = a
  · simp only [h, ite_true]; rw [h1]; norm_num
  · simp only [h, ite_false]
    have hc : Integrable (fun x => clamp01 x) unif :=
      Integrable.of_bound clamp01_measurable.aestronglyMeasurable 1 (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (clamp01_nonneg x)]; exact clamp01_le_one x)
    rw [integral_sub (integrable_const _) hc, h1]
    simp
    norm_num

lemma card_agree_erase_compl {S : Finset (Fin N)} {j : Fin N} (hj : j ∈ S) (s : State N) :
    (agree (S.erase j)ᶜ s).card = 2 ^ (S.card - 1) := by
  rw [card_agree, card_compl, Fintype.card_fin, card_erase_of_mem hj]
  congr 1
  have h2 : S.card ≤ N := by simpa [Fintype.card_fin] using card_le_univ S
  have h1 : 1 ≤ S.card := card_pos.2 ⟨j, hj⟩
  omega

/-- **One cut mean**: `qW < 1/4` has probability at most `2 exp (-2^{|S|-1}/8)`. -/
lemma cubeM_qW_lt (s : State N) {S : Finset (Fin N)} {j : Fin N} (hj : j ∈ S) (b : Bool) :
    cubeM N {w | qW w s S j b < 1 / 4} ≤
      ENNReal.ofReal (2 * Real.exp (-(2 : ℝ) ^ (S.card - 1) / 8)) := by
  set A := agree (S.erase j)ᶜ s with hA
  set n : ℝ := (2 : ℝ) ^ (S.card - 1) with hn
  have hcard : (A.card : ℝ) = n := by rw [hA, card_agree_erase_compl hj]; push_cast; rfl
  have hnpos : 0 < n := by positivity
  have hmf : ∀ r : State N, Measurable fun v : Fin N → ℝ => gq (s j) b (v j) :=
    fun _ => (measurable_gq _ _).comp (measurable_pi_apply j)
  have hind := iIndepFun_rows (fun _ v => gq (s j) b (v j)) hmf
  have hmeas : ∀ r, AEMeasurable (fun w : Param N => gq (s j) b (w r j)) (cubeM N) :=
    fun r => ((hmf r).comp (measurable_pi_apply r)).aemeasurable
  have hb : ∀ r ∈ A, ∀ᵐ w ∂cubeM N, gq (s j) b (w r j) ∈ Set.Icc 0 ((fun _ => (1 : ℝ)) r) :=
    fun r _ => ae_of_all _ fun w => gq_mem _ _ _
  have hε : (0 : ℝ) ≤ n / 4 := by positivity
  have h := hoeffding_abs (μ := cubeM N) (X := fun r (w : Param N) => gq (s j) b (w r j))
    A hind hmeas hb hε
  have hmean : ∀ r, ∫ w, gq (s j) b (w r j) ∂cubeM N = 1 / 2 := by
    intro r
    rw [integral_row_eval (g := fun v => gq (s j) b (v j)) (hmf r).aestronglyMeasurable r]
    unfold rowM
    rw [integral_pi_eval unif (measurable_gq _ _).aestronglyMeasurable j, integral_gq]
  simp only [hmean, one_pow, sum_const, nsmul_one, hcard] at h
  have hsub : {w : Param N | qW w s S j b < 1 / 4} ⊆
      {w | n / 4 ≤ |∑ r ∈ A, (gq (s j) b (w r j) - 1 / 2)|} := by
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    have hq : qW w s S j b = (∑ r ∈ A, gq (s j) b (w r j)) / n := rfl
    rw [hq, div_lt_iff₀ hnpos] at hw
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcard]
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
  congr 2
  field_simp
  ring

/-- The failure probability of `g16`. -/
def fg16 (N : ℕ) : ℝ := 4 * N * 2 ^ N * Real.exp (-(2 : ℝ) ^ K2N N / 8)

/-- **`g16` fails with probability at most `fg16 N`, uniformly in the current state.** -/
theorem cubeM_not_g16 (s : State N) :
    cubeM N {w | ¬ ∀ (S : Finset (Fin N)) j b, j ∈ S → K2N N < S.card → 1 / 4 ≤ qW w s S j b} ≤
      ENNReal.ofReal (fg16 N) := by
  set E : Finset (Fin N) → Fin N → Bool → Set (Param N) := fun S j b =>
    {w | j ∈ S ∧ K2N N < S.card ∧ qW w s S j b < 1 / 4} with hE
  have hsub : {w : Param N | ¬ ∀ (S : Finset (Fin N)) j b, j ∈ S → K2N N < S.card →
      1 / 4 ≤ qW w s S j b} ⊆ ⋃ S, ⋃ j, ⋃ b, E S j b := by
    intro w hw
    simp only [Set.mem_ofPred_eq, not_forall, not_le] at hw
    obtain ⟨S, j, b, hj, hk, h⟩ := hw
    exact Set.mem_iUnion.2 ⟨S, Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨b, hj, hk, h⟩⟩⟩
  have hone : ∀ S j b, cubeM N (E S j b) ≤
      ENNReal.ofReal (2 * Real.exp (-(2 : ℝ) ^ K2N N / 8)) := by
    intro S j b
    by_cases hc : j ∈ S ∧ K2N N < S.card
    · refine (measure_mono fun w hw => hw.2.2).trans ((cubeM_qW_lt s hc.1 b).trans
        (ENNReal.ofReal_le_ofReal ?_))
      have hk : K2N N ≤ S.card - 1 := by omega
      have : (2 : ℝ) ^ K2N N ≤ 2 ^ (S.card - 1) := pow_le_pow_right₀ (by norm_num) hk
      gcongr
    · have : E S j b = ∅ := by
        ext w; simp only [hE, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hc ⟨h.1, h.2.1⟩
      rw [this, measure_empty]
      exact zero_le
  refine (measure_mono hsub).trans ((cubeM_iUnion_le _ fun S => cubeM_iUnion_le _ fun j =>
    cubeM_iUnion_le _ fun b => hone S j b).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  simp only [Fintype.card_finset, Fintype.card_fin, Fintype.card_bool]
  unfold fg16
  push_cast
  ring

lemma two_pow_le_K2N {N : ℕ} (hN : 0 < N) : 2 ^ N ≤ 2 ^ K2N N * (2 ^ 16 * N ^ 4) := by
  have hlog : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN.ne'
  have h1 : 2 ^ (4 * Nat.log 2 N + 16) ≤ 2 ^ 16 * N ^ 4 := by
    rw [pow_add, mul_comm 4, pow_mul]
    calc (2 ^ Nat.log 2 N) ^ 4 * 2 ^ 16 ≤ N ^ 4 * 2 ^ 16 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hlog 4)
      _ = 2 ^ 16 * N ^ 4 := mul_comm _ _
  calc 2 ^ N ≤ 2 ^ (K2N N + (4 * Nat.log 2 N + 16)) :=
        Nat.pow_le_pow_right (by norm_num) (by unfold K2N; omega)
    _ = 2 ^ K2N N * 2 ^ (4 * Nat.log 2 N + 16) := pow_add _ _ _
    _ ≤ _ := Nat.mul_le_mul_left _ h1

lemma eventually_K2N_large : ∀ᶠ N : ℕ in atTop, 16 * N ≤ 2 ^ K2N N := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 5 (r := 2) (by norm_num)
  have hev := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 ^ 20 by positivity))).and
    (eventually_ge_atTop 1)
  filter_upwards [hev] with N ⟨hN, h1⟩
  have hpow : (0 : ℝ) < 2 ^ N := by positivity
  rw [div_lt_iff₀ hpow] at hN
  have hreal : (2 : ℝ) ^ 20 * (N : ℝ) ^ 5 ≤ 2 ^ N := by
    have := mul_lt_mul_of_pos_left hN (show (0 : ℝ) < 2 ^ 20 by positivity)
    rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
    exact this.le
  have hnat : 2 ^ 20 * N ^ 5 ≤ 2 ^ N := by exact_mod_cast hreal
  have h2 := hnat.trans (two_pow_le_K2N h1)
  have hN4 : 0 < 2 ^ 16 * N ^ 4 := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hN4
  calc 16 * N * (2 ^ 16 * N ^ 4) = 2 ^ 20 * N ^ 5 := by ring
    _ ≤ _ := h2

theorem tendsto_fg16 : Tendsto fg16 atTop (𝓝 0) := by
  have hr : 2 * Real.exp (-2) < 1 := by
    have h := Real.add_one_le_exp 2
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos 2)]
    linarith
  have h := (tendsto_self_mul_const_pow_of_lt_one (r := 2 * Real.exp (-2)) (by positivity)
    hr).const_mul 4
  rw [mul_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun N => by unfold fg16; positivity) ?_
  filter_upwards [eventually_K2N_large] with N hN
  have hNr : (16 : ℝ) * N ≤ 2 ^ K2N N := by exact_mod_cast hN
  have he : Real.exp (-(2 : ℝ) ^ K2N N / 8) ≤ Real.exp (-2) ^ N := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by linarith)
  unfold fg16
  rw [mul_pow]
  have : (0 : ℝ) ≤ 4 * N * 2 ^ N := by positivity
  calc 4 * (N : ℝ) * 2 ^ N * Real.exp (-(2 : ℝ) ^ K2N N / 8)
      ≤ 4 * N * 2 ^ N * Real.exp (-2) ^ N := mul_le_mul_of_nonneg_left he this
    _ = 4 * (N * (2 ^ N * Real.exp (-2) ^ N)) := by ring

end

end Census
end IIT
