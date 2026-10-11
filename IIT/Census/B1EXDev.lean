/-
Census, B1 lower bound part (b): per-unit sums on `E_X` concentrate (the deviation step of `EXFacts_whp`).

* `pair_s_law`: the joint law of the pair vector `(w r0 j, w r1 j)_j` and the row `w s` (three distinct rows) is
  `(unif ⊗ unif)^N ⊗ rowM`.
* `EX_pair_dev`: for `g : ℝ² → ℝ` bounded on the pair cells with per-cell average bounds `avg_j ≤ B_j` and
  `Σ_j a_j B_j ≤ E`, `P(E_X ∩ {Σ_j g(y_j, U_j) ≥ N(E + η)}) ≤ P(E_X) e^{-N η² / (2 (b - a)²)}` eventually.
* `EX_s_dev`: the same for functions of the row-`s` entries.
-/
import IIT.Census.B1LowerEX
import IIT.Census.B1TypeMGF

namespace IIT
namespace Census

open MeasureTheory Filter Finset

variable {N : ℕ}

/-- The pair vector of rows `r0`, `r1`. -/
def pairVec (w : Param N) (r0 r1 : State N) : Fin N → ℝ × ℝ := fun j => (w r0 j, w r1 j)

lemma measurable_pairVec (r0 r1 : State N) : Measurable fun w : Param N => pairVec w r0 r1 :=
  measurable_pi_iff.2 fun j => ((measurable_pi_apply j).comp (measurable_pi_apply r0)).prodMk
    ((measurable_pi_apply j).comp (measurable_pi_apply r1))

/-- **Joint law of a pair of rows and a third row.** -/
theorem pair_s_law {r0 r1 s : State N} (h01 : r0 ≠ r1) (h0 : r0 ≠ s) (h1 : r1 ≠ s)
    {S : Set (Fin N → ℝ × ℝ)} (hS : MeasurableSet S) {B : Set (Fin N → ℝ)} (hB : MeasurableSet B) :
    cubeM N {w | pairVec w r0 r1 ∈ S ∧ w s ∈ B} =
      Measure.pi (fun _ : Fin N => unif.prod unif) S * rowM N B := by
  set A : Set ((Fin N → ℝ) × (Fin N → ℝ)) := {ab | (fun j => (ab.1 j, ab.2 j)) ∈ S} with hA
  have hAm : MeasurableSet A :=
    hS.preimage (measurable_pi_iff.2 fun j => ((measurable_pi_apply j).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd))
  have hind := (iIndepFun_rows (N := N) (fun _ v => v) fun _ => measurable_id).indepFun_prodMk
    (fun _ => measurable_pi_apply _) r0 r1 s h0 h1
  have hsplit := hind.measure_inter_preimage_eq_mul A B hAm hB
  have hset : {w : Param N | pairVec w r0 r1 ∈ S ∧ w s ∈ B} =
      (fun w : Param N => (w r0, w r1)) ⁻¹' A ∩ (fun w : Param N => w s) ⁻¹' B := by
    ext w; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, A]; rfl
  rw [hset, hsplit]
  have hmp : MeasurePreserving (fun w : Param N => w s) (cubeM N) (rowM N) :=
    measurePreserving_eval (fun _ : State N => rowM N) s
  rw [hmp.measure_preimage hB.nullMeasurableSet]
  congr 1
  have hm : Measurable (fun w : Param N => (w r0, w r1)) :=
    (measurable_pi_apply r0).prodMk (measurable_pi_apply r1)
  rw [← Measure.map_apply hm hAm, map_two_rows h01]
  have hmp2 := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin N) (fun _ => unif) (fun _ => unif)
  unfold rowM
  rw [← hmp2.measure_preimage_equiv]
  rfl

open Classical in
/-- The pair-type set and the row-`s` type set of `E_X`. -/
noncomputable def PTset (N : ℕ) : Set (Fin N → ℝ × ℝ) :=
  {v | ∀ i : Fin KP, (univ.filter fun j => v j ∈ exIP (cP i)).card = nP N i}

open Classical in
noncomputable def STset (N : ℕ) : Set (Fin N → ℝ) :=
  {v | ∀ i : Fin KS, (univ.filter fun k => v k ∈ exIS (cS i)).card = nS N i}

lemma EX_eq (s r0 : State N) (x : Fin N) :
    EX N s r0 x = {w | pairVec w r0 (flipAt x r0) ∈ PTset N ∧ w s ∈ STset N} := by
  classical
  ext w; simp only [EX, PTset, STset, pairVec, Set.mem_setOf_eq]
  constructor <;> rintro ⟨a, b⟩ <;> exact ⟨fun i => (congrArg Finset.card (Finset.filter_congr fun _ _ => Iff.rfl)).trans (a i),
    fun i => (congrArg Finset.card (Finset.filter_congr fun _ _ => Iff.rfl)).trans (b i)⟩

lemma measurableSet_PTset : MeasurableSet (PTset N) := by
  classical
  have : PTset N = ⋂ i : Fin KP, {v : Fin N → ℝ × ℝ | (univ.filter fun j => v j ∈ exIP (cP i)).card = nP N i} := by
    ext v; simp [PTset]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_card_filter (fun (j : Fin N) (v : Fin N → ℝ × ℝ) =>
    v j ∈ exIP (cP i)) (fun j => (measurable_pi_apply j) (measurableSet_Ico.prod measurableSet_Ico)) _

lemma measurableSet_STset : MeasurableSet (STset N) := by
  classical
  have : STset N = ⋂ i : Fin KS, {v : Fin N → ℝ | (univ.filter fun k => v k ∈ exIS (cS i)).card = nS N i} := by
    ext v; simp [STset]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_card_filter (fun (k : Fin N) (v : Fin N → ℝ) =>
    v k ∈ exIS (cS i)) (fun k => (measurable_pi_apply k) measurableSet_Ico) _

lemma exP_real (i : Fin KP) : (unif.prod unif).real (exIP (cP i)) = ellP i := by
  have := ellP_pos i; unfold ellP at this
  rw [Measure.real, exP_measure (cP_mem i), ENNReal.toReal_ofReal this.le]; rfl

lemma exS_real (i : Fin KS) : unif.real (exIS (cS i)) = ellS i := by
  have := ellS_pos i; unfold ellS at this
  rw [Measure.real, exS_measure (cS_mem i), ENNReal.toReal_ofReal this.le]; rfl

/-- Rounding of a weighted count: `Σ_j n_j B_j ≤ N Σ_j a_j B_j + K Σ_j |B_j|`. -/
lemma nP_wsum_le (N : ℕ) (B : Fin KP → ℝ) :
    ∑ i, (nP N i : ℝ) * B i ≤ N * ∑ i, ((cP i).a : ℝ) * B i + KP * ∑ i, |B i| := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := nP_err N i
  have : ((nP N i : ℝ) - (cP i).a * N) * B i ≤ KP * |B i| := by
    calc ((nP N i : ℝ) - (cP i).a * N) * B i ≤ |((nP N i : ℝ) - (cP i).a * N) * B i| := le_abs_self _
      _ = |(nP N i : ℝ) - (cP i).a * N| * |B i| := abs_mul _ _
      _ ≤ KP * |B i| := mul_le_mul_of_nonneg_right h (abs_nonneg _)
  nlinarith

lemma nS_wsum_le (N : ℕ) (B : Fin KS → ℝ) :
    ∑ i, (nS N i : ℝ) * B i ≤ N * ∑ i, ((cS i).a : ℝ) * B i + KS * ∑ i, |B i| := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := nS_err N i
  have : ((nS N i : ℝ) - (cS i).a * N) * B i ≤ KS * |B i| := by
    calc ((nS N i : ℝ) - (cS i).a * N) * B i ≤ |((nS N i : ℝ) - (cS i).a * N) * B i| := le_abs_self _
      _ = |(nS N i : ℝ) - (cS i).a * N| * |B i| := abs_mul _ _
      _ ≤ KS * |B i| := mul_le_mul_of_nonneg_right h (abs_nonneg _)
  nlinarith

/-- **Deviation of a pair sum on `E_X`** (upper tail). -/
theorem EX_pair_dev (g : ℝ × ℝ → ℝ) (hgm : Measurable g) {a b : ℝ} (hab : a < b)
    (hg : ∀ i, ∀ p ∈ exIP (cP i), g p ∈ Set.Icc a b) (B : Fin KP → ℝ)
    (hB : ∀ i, (∫ p in exIP (cP i), g p ∂(unif.prod unif)) / ellP i ≤ B i)
    {E : ℝ} (hE : ∑ i, ((cP i).a : ℝ) * B i ≤ E) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N), r0 ≠ s → flipAt x r0 ≠ s →
      cubeM N (EX N s r0 x ∩ {w | N * (E + η) ≤ ∑ j, g (w r0 j, w (flipAt x r0) j)}) ≤
        cubeM N (EX N s r0 x) * ENNReal.ofReal (Real.exp (-(2 * N * (η / 2) ^ 2 / (b - a) ^ 2))) := by
  classical
  set C := (KP : ℝ) * ∑ i, |B i|
  have hev : ∀ᶠ N : ℕ in atTop, C ≤ N * (η / 2) := by
    have := tendsto_natCast_atTop_atTop.eventually_ge_atTop (C / (η / 2))
    filter_upwards [this] with N hN
    rwa [div_le_iff₀ (by positivity)] at hN
  filter_upwards [hev] with N hN s r0 x h0 h1
  set r1 := flipAt x r0
  set D : Set (Fin N → ℝ × ℝ) := {v | ∑ i, (nP N i : ℝ) * ((∫ p in exIP (cP i), g p ∂(unif.prod unif)) /
      (unif.prod unif).real (exIP (cP i))) + N * (η / 2) ≤ ∑ j, g (v j)}
  have hDm : MeasurableSet D :=
    measurableSet_le measurable_const (Finset.measurable_sum _ fun j _ => hgm.comp (measurable_pi_apply j))
  -- the threshold is above the conditional mean plus `N η / 2`
  have hthr : ∀ v : Fin N → ℝ × ℝ, N * (E + η) ≤ ∑ j, g (v j) → v ∈ D := by
    intro v hv
    have h1' : ∑ i, (nP N i : ℝ) * ((∫ p in exIP (cP i), g p ∂(unif.prod unif)) /
        (unif.prod unif).real (exIP (cP i))) ≤ ∑ i, (nP N i : ℝ) * B i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by rw [exP_real]; exact hB i)
        (Nat.cast_nonneg _)
    have h2' := nP_wsum_le N B
    have h3 : (N : ℝ) * ∑ i, ((cP i).a : ℝ) * B i ≤ N * E :=
      mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)
    simp only [D, Set.mem_setOf_eq]
    nlinarith
  have hsub : EX N s r0 x ∩ {w | N * (E + η) ≤ ∑ j, g (w r0 j, w r1 j)} ⊆
      {w | pairVec w r0 r1 ∈ PTset N ∩ D ∧ w s ∈ STset N} := by
    rintro w ⟨hw, hd⟩
    rw [EX_eq] at hw
    exact ⟨⟨hw.1, hthr _ hd⟩, hw.2⟩
  have h01 : r0 ≠ r1 := (flipAt_ne x r0).symm
  refine (measure_mono hsub).trans ?_
  rw [pair_s_law h01 h0 h1 (measurableSet_PTset.inter hDm) measurableSet_STset, EX_eq,
    pair_s_law h01 h0 h1 measurableSet_PTset measurableSet_STset, mul_right_comm]
  gcongr
  -- the Hoeffding step
  have hH := type_event_hoeffding (unif.prod unif) (fun i => exIP (cP i))
    (fun i => measurableSet_Ico.prod measurableSet_Ico) exIP_disjoint (nP_sum N)
    (fun i => by rw [exP_real]; exact ellP_pos i) g hgm hab hg (η := η / 2) (by positivity)
  have hfin : ∀ X, Measure.pi (fun _ : Fin N => unif.prod unif) X ≠ ⊤ := fun X => measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal (hfin _), ← ENNReal.ofReal_toReal (hfin (PTset N)),
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal hH

/-- **Deviation of a pair sum on `E_X`** (lower tail). -/
theorem EX_pair_dev_lo (g : ℝ × ℝ → ℝ) (hgm : Measurable g) {a b : ℝ} (hab : a < b)
    (hg : ∀ i, ∀ p ∈ exIP (cP i), g p ∈ Set.Icc a b) (B : Fin KP → ℝ)
    (hB : ∀ i, B i ≤ (∫ p in exIP (cP i), g p ∂(unif.prod unif)) / ellP i)
    {E : ℝ} (hE : E ≤ ∑ i, ((cP i).a : ℝ) * B i) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N), r0 ≠ s → flipAt x r0 ≠ s →
      cubeM N (EX N s r0 x ∩ {w | ∑ j, g (w r0 j, w (flipAt x r0) j) ≤ N * (E - η)}) ≤
        cubeM N (EX N s r0 x) * ENNReal.ofReal (Real.exp (-(2 * N * (η / 2) ^ 2 / (b - a) ^ 2))) := by
  have h := EX_pair_dev (fun p => -g p) hgm.neg (a := -b) (b := -a) (by linarith)
    (fun i p hp => ⟨by linarith [(hg i p hp).2], by linarith [(hg i p hp).1]⟩) (fun i => -B i)
    (fun i => by rw [integral_neg, neg_div]; exact neg_le_neg (hB i)) (E := -E)
    (by simp only [mul_neg, Finset.sum_neg_distrib]; linarith) hη
  filter_upwards [h] with N hN s r0 x h0 h1
  have hb : (-a - -b) ^ 2 = (b - a) ^ 2 := by ring
  rw [hb] at hN
  refine le_trans (measure_mono (s := EX N s r0 x ∩ {w | ∑ j, g (w r0 j, w (flipAt x r0) j) ≤ N * (E - η)})
    (t := EX N s r0 x ∩ {w | N * (-E + η) ≤ ∑ j, -g (w r0 j, w (flipAt x r0) j)}) ?_) (hN s r0 x h0 h1)
  intro w hw
  refine ⟨hw.1, ?_⟩
  have := hw.2
  simp only [Set.mem_setOf_eq, Finset.sum_neg_distrib] at this ⊢
  linarith

/-- The row-`s` vector. -/
lemma EX_s_aux (s r0 : State N) (x : Fin N) (h0 : r0 ≠ s) (h1 : flipAt x r0 ≠ s)
    {D : Set (Fin N → ℝ)} (hD : MeasurableSet D) :
    cubeM N {w | pairVec w r0 (flipAt x r0) ∈ PTset N ∧ w s ∈ STset N ∩ D} =
      cubeM N (EX N s r0 x) * (rowM N (STset N ∩ D) / rowM N (STset N)) := by
  have h01 : r0 ≠ flipAt x r0 := (flipAt_ne x r0).symm
  rw [pair_s_law h01 h0 h1 measurableSet_PTset (measurableSet_STset.inter hD), EX_eq,
    pair_s_law h01 h0 h1 measurableSet_PTset measurableSet_STset]
  by_cases hz : rowM N (STset N) = 0
  · have : rowM N (STset N ∩ D) = 0 := measure_mono_null Set.inter_subset_left hz
    rw [this, hz]; simp
  · rw [mul_assoc, ENNReal.mul_div_cancel hz (measure_ne_top _ _)]

/-- **Deviation of a row-`s` sum on `E_X`** (upper tail). -/
theorem EX_s_dev (g : ℝ → ℝ) (hgm : Measurable g) {a b : ℝ} (hab : a < b)
    (hg : ∀ i, ∀ p ∈ exIS (cS i), g p ∈ Set.Icc a b) (B : Fin KS → ℝ)
    (hB : ∀ i, (∫ p in exIS (cS i), g p ∂unif) / ellS i ≤ B i)
    {E : ℝ} (hE : ∑ i, ((cS i).a : ℝ) * B i ≤ E) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N), r0 ≠ s → flipAt x r0 ≠ s →
      cubeM N (EX N s r0 x ∩ {w | N * (E + η) ≤ ∑ k, g (w s k)}) ≤
        cubeM N (EX N s r0 x) * ENNReal.ofReal (Real.exp (-(2 * N * (η / 2) ^ 2 / (b - a) ^ 2))) := by
  classical
  set C := (KS : ℝ) * ∑ i, |B i|
  have hev : ∀ᶠ N : ℕ in atTop, C ≤ N * (η / 2) := by
    have := tendsto_natCast_atTop_atTop.eventually_ge_atTop (C / (η / 2))
    filter_upwards [this] with N hN
    rwa [div_le_iff₀ (by positivity)] at hN
  filter_upwards [hev] with N hN s r0 x h0 h1
  set D : Set (Fin N → ℝ) := {v | ∑ i, (nS N i : ℝ) * ((∫ p in exIS (cS i), g p ∂unif) /
      unif.real (exIS (cS i))) + N * (η / 2) ≤ ∑ k, g (v k)}
  have hDm : MeasurableSet D :=
    measurableSet_le measurable_const (Finset.measurable_sum _ fun j _ => hgm.comp (measurable_pi_apply j))
  have hthr : ∀ v : Fin N → ℝ, N * (E + η) ≤ ∑ k, g (v k) → v ∈ D := by
    intro v hv
    have h1' : ∑ i, (nS N i : ℝ) * ((∫ p in exIS (cS i), g p ∂unif) / unif.real (exIS (cS i))) ≤
        ∑ i, (nS N i : ℝ) * B i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by rw [exS_real]; exact hB i)
        (Nat.cast_nonneg _)
    have h2' := nS_wsum_le N B
    have h3 : (N : ℝ) * ∑ i, ((cS i).a : ℝ) * B i ≤ N * E :=
      mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)
    simp only [D, Set.mem_setOf_eq]
    nlinarith
  have hsub : EX N s r0 x ∩ {w | N * (E + η) ≤ ∑ k, g (w s k)} ⊆
      {w | pairVec w r0 (flipAt x r0) ∈ PTset N ∧ w s ∈ STset N ∩ D} := by
    rintro w ⟨hw, hd⟩
    rw [EX_eq] at hw
    exact ⟨hw.1, hw.2, hthr _ hd⟩
  refine (measure_mono hsub).trans ?_
  rw [EX_s_aux s r0 x h0 h1 hDm]
  gcongr
  have hH := type_event_hoeffding unif (fun i => exIS (cS i)) (fun i => measurableSet_Ico) exIS_disjoint
    (nS_sum N) (fun i => by rw [exS_real]; exact ellS_pos i) g hgm hab hg (η := η / 2) (by positivity)
  have hfin : ∀ X, rowM N X ≠ ⊤ := fun X => measure_ne_top _ _
  by_cases hz : rowM N (STset N) = 0
  · have : rowM N (STset N ∩ D) = 0 := measure_mono_null Set.inter_subset_left hz
    rw [this, ENNReal.zero_div]; exact bot_le
  rw [ENNReal.div_le_iff hz (hfin _), mul_comm]
  rw [← ENNReal.ofReal_toReal (hfin _), ← ENNReal.ofReal_toReal (hfin (STset N)),
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal hH

/-- **Deviation of a row-`s` sum on `E_X`** (lower tail). -/
theorem EX_s_dev_lo (g : ℝ → ℝ) (hgm : Measurable g) {a b : ℝ} (hab : a < b)
    (hg : ∀ i, ∀ p ∈ exIS (cS i), g p ∈ Set.Icc a b) (B : Fin KS → ℝ)
    (hB : ∀ i, B i ≤ (∫ p in exIS (cS i), g p ∂unif) / ellS i)
    {E : ℝ} (hE : E ≤ ∑ i, ((cS i).a : ℝ) * B i) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ (s r0 : State N) (x : Fin N), r0 ≠ s → flipAt x r0 ≠ s →
      cubeM N (EX N s r0 x ∩ {w | ∑ k, g (w s k) ≤ N * (E - η)}) ≤
        cubeM N (EX N s r0 x) * ENNReal.ofReal (Real.exp (-(2 * N * (η / 2) ^ 2 / (b - a) ^ 2))) := by
  have h := EX_s_dev (fun p => -g p) hgm.neg (a := -b) (b := -a) (by linarith)
    (fun i p hp => ⟨by linarith [(hg i p hp).2], by linarith [(hg i p hp).1]⟩) (fun i => -B i)
    (fun i => by rw [integral_neg, neg_div]; exact neg_le_neg (hB i)) (E := -E)
    (by simp only [mul_neg, Finset.sum_neg_distrib]; linarith) hη
  filter_upwards [h] with N hN s r0 x h0 h1
  have hb : (-a - -b) ^ 2 = (b - a) ^ 2 := by ring
  rw [hb] at hN
  refine le_trans (measure_mono (s := EX N s r0 x ∩ {w | ∑ k, g (w s k) ≤ N * (E - η)})
    (t := EX N s r0 x ∩ {w | N * (-E + η) ≤ ∑ k, -g (w s k)}) ?_) (hN s r0 x h0 h1)
  intro w hw
  refine ⟨hw.1, ?_⟩
  have := hw.2
  simp only [Set.mem_setOf_eq, Finset.sum_neg_distrib] at this ⊢
  linarith

end Census
end IIT
