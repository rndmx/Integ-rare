/-
Census, Theorem E: small positive effect sides are rare.

For a candidate `S`, a system partition `θ` and an effect state `te`, the effect side
`sysPhiE(θ; te) = e · |log₂ (e / pe)|₊` of `φ_s` is a function of the column entries of `S` in the
rows of the `S`-block of the current state.  If `0 < sysPhiE < δ ≤ a^|S| b` then either some
`e`-factor is below `a`, or a row entry `y'` of a cut unit `i` in another row of the block is below
`ρ`, or `0 < ln (e / pe) < b` while `y' ≥ ρ`.  In the last case, as a function of the single entry
`z s i`, `ln (e / pe)` moves by at least `ρ 4^{-|S|}` times the increment, so the slice of the
event along that coordinate has length at most `4^|S| b / ρ`.  Integrating the slices
(`te_cube_slice`) gives (`te_eff_le`)
`P(0 < sysPhiE < δ) ≤ |S| a + ρ + 4^|S| b / ρ`.
-/
import IIT.Census.Profile
import IIT.Census.TieBranches
import IIT.Census.PairMoments
import IIT.Census.UnivProb
import IIT.Census.CertDataClass

namespace IIT
namespace Census

open MeasureTheory Finset ENNReal

noncomputable section

variable {N : ℕ}

/-! ### Slicing a product measure along one coordinate -/

/-- If every slice of `F` along the coordinate `i` has `μ i`-measure at most `c`, then `F` has
product measure at most `c`. -/
lemma te_pi_slice {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {F : Set (∀ i, X i)} (hF : MeasurableSet F) (i : ι) (x0 : ∀ i, X i) {c : ℝ≥0∞}
    (h : ∀ x, μ i {t | Function.update x i t ∈ F} ≤ c) : Measure.pi μ F ≤ c := by
  have hf : Measurable (F.indicator (1 : (∀ i, X i) → ℝ≥0∞)) :=
    measurable_one.indicator hF
  rw [← lintegral_indicator_one hF, lintegral_eq_lmarginal_univ x0,
    lmarginal_erase' _ hf (mem_univ i)]
  have hin : (fun x => ∫⁻ t, F.indicator 1 (Function.update x i t) ∂μ i) ≤ fun _ => c := by
    intro x
    have e1 : (fun t => F.indicator (1 : (∀ i, X i) → ℝ≥0∞) (Function.update x i t)) =
        ((fun t => Function.update x i t) ⁻¹' F).indicator 1 := by
      funext t; rfl
    simp only
    rw [e1, lintegral_indicator_one (measurable_update x hF)]
    exact h x
  refine (lmarginal_mono (s := univ.erase i) (μ := μ) hin x0).trans ?_
  simp [lmarginal]

/-- A subset of `[0,1]` whose points are pairwise within `D` has `unif`-measure at most `D`. -/
lemma te_unif_le {A : Set ℝ} {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ t1 ∈ A, ∀ t2 ∈ A, t1 ∈ Set.Icc (0 : ℝ) 1 → t2 ∈ Set.Icc (0 : ℝ) 1 → |t1 - t2| ≤ D) :
    unif A ≤ ENNReal.ofReal D := by
  unfold unif
  rw [Measure.restrict_apply' measurableSet_Icc]
  refine (Real.volume_le_diam _).trans ?_
  refine Metric.ediam_le fun t1 ht1 t2 ht2 => ?_
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal (h t1 ht1.1 t2 ht2.1 ht1.2 ht2.2)

/-- **Slicing the cube** along the entry `(r, j)`: if the points of a measurable set that differ
only in that entry are within `D` of each other, the set has measure at most `D`. -/
lemma te_cube_slice {E : Set (Param N)} (hE : MeasurableSet E) (r : State N) (j : Fin N)
    {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ (x : Param N) (row : Fin N → ℝ) (t1 t2 : ℝ), t1 ∈ Set.Icc (0 : ℝ) 1 →
      t2 ∈ Set.Icc (0 : ℝ) 1 → Function.update x r (Function.update row j t1) ∈ E →
      Function.update x r (Function.update row j t2) ∈ E → |t1 - t2| ≤ D) :
    cubeM N E ≤ ENNReal.ofReal D := by
  unfold cubeM
  refine te_pi_slice _ hE r (fun _ _ => 0) fun x => ?_
  have hEx : MeasurableSet {row : Fin N → ℝ | Function.update x r row ∈ E} :=
    measurable_update x hE
  unfold rowM
  refine te_pi_slice _ hEx j (fun _ => 0) fun row => ?_
  exact te_unif_le hD fun t1 h1 t2 h2 i1 i2 => h x row t1 t2 i1 i2 h1 h2

/-! ### Coordinate events -/

lemma te_unif_lt (a : ℝ) (hb : Bool) :
    unif {x | (if hb then clamp01 x else 1 - clamp01 x) < a} ≤ ENNReal.ofReal a := by
  unfold unif
  rw [Measure.restrict_apply' measurableSet_Icc]
  cases hb
  · have hs : {x : ℝ | (if false = true then clamp01 x else 1 - clamp01 x) < a} ∩ Set.Icc 0 1 ⊆
        Set.Icc (1 - a) 1 := by
      rintro x ⟨hx, hx01⟩
      simp only [Set.mem_setOf_eq, Bool.false_eq_true, ↓reduceIte, clamp01_of_mem hx01] at hx
      exact ⟨by linarith, hx01.2⟩
    refine (measure_mono hs).trans ?_
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · have hs : {x : ℝ | (if true = true then clamp01 x else 1 - clamp01 x) < a} ∩ Set.Icc 0 1 ⊆
        Set.Icc 0 a := by
      rintro x ⟨hx, hx01⟩
      simp only [Set.mem_setOf_eq, ↓reduceIte, clamp01_of_mem hx01] at hx
      exact ⟨hx01.1, hx.le⟩
    refine (measure_mono hs).trans ?_
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal (by linarith)

lemma te_prob_eq (z : Param N) (j : Fin N) (r : State N) (b : Bool) :
    (tpmOf z).prob j r b = if b then clamp01 (z r j) else 1 - clamp01 (z r j) := rfl

lemma te_measurable_prob (j : Fin N) (r : State N) (b : Bool) :
    Measurable fun z : Param N => (tpmOf z).prob j r b := by
  simp only [te_prob_eq]
  have hc : Measurable fun z : Param N => clamp01 (z r j) :=
    measurable_clamp01.comp ((measurable_pi_apply j).comp (measurable_pi_apply r))
  cases b
  · exact measurable_const.sub hc
  · exact hc

/-- An entry of a fixed row is below `a` with probability at most `a`. -/
lemma te_cubeM_prob_lt (j : Fin N) (r : State N) (b : Bool) (a : ℝ) :
    cubeM N {z | (tpmOf z).prob j r b < a} ≤ ENNReal.ofReal a := by
  have hm : MeasurableSet {x : ℝ | (if b then clamp01 x else 1 - clamp01 x) < a} := by
    cases b
    · exact measurableSet_lt (measurable_const.sub measurable_clamp01) measurable_const
    · exact measurableSet_lt measurable_clamp01 measurable_const
  have e : {z : Param N | (tpmOf z).prob j r b < a} =
      (fun w : Param N => w r j) ⁻¹' {x | (if b then clamp01 x else 1 - clamp01 x) < a} := by
    ext z; simp [te_prob_eq]
  rw [e, (mp_coord r j).measure_preimage hm.nullMeasurableSet]
  exact te_unif_lt a b

lemma te_measurableSet_openCube : MeasurableSet (openCube N) := by
  have e : openCube N = ⋂ r : State N, ⋂ j : Fin N,
      (fun z : Param N => z r j) ⁻¹' Set.Ioo (0 : ℝ) 1 := by
    ext z; simp [openCube]
  rw [e]
  exact MeasurableSet.iInter fun r => MeasurableSet.iInter fun j =>
    ((measurable_pi_apply j).comp (measurable_pi_apply r)) measurableSet_Ioo

/-! ### The effect side as a product over units -/

section Effect

variable (s : State N) {S : Finset (Fin N)} (θ : SysPartition N S) (te : State N)

/-- The partial effect factor of unit `j`. -/
def te_U (z : Param N) (j : Fin N) : ℝ := effUnit (tpmOf z) (profile θ j)ᶜ s j (te j)

lemma te_eP_eq (z : Param N) :
    sysEffProb (tpmOf z) S s s te = ∏ j ∈ S, (tpmOf z).prob j s (te j) := by
  unfold sysEffProb
  rw [merge_self]

lemma te_pP_eq (z : Param N) : sysPartEffProb (tpmOf z) S s θ s te = ∏ j ∈ S, te_U s θ te z j := by
  unfold sysPartEffProb te_U profile
  rw [merge_self]

lemma te_measurable_U (j : Fin N) : Measurable fun z => te_U s θ te z j := by
  unfold te_U effUnit
  exact (Finset.measurable_sum _ fun r _ => te_measurable_prob j r _).div_const _

lemma te_measurable_eP : Measurable fun z : Param N => sysEffProb (tpmOf z) S s s te := by
  simp_rw [te_eP_eq]
  exact Finset.measurable_prod _ fun j _ => te_measurable_prob j s _

lemma te_measurable_pP : Measurable fun z : Param N => sysPartEffProb (tpmOf z) S s θ s te := by
  simp_rw [te_pP_eq]
  exact Finset.measurable_prod _ fun j _ => te_measurable_U s θ te j

/-- The log-ratio `ln (e / pe)`. -/
def te_Phi (z : Param N) : ℝ :=
  Real.log (sysEffProb (tpmOf z) S s s te / sysPartEffProb (tpmOf z) S s θ s te)

lemma te_measurable_Phi : Measurable (te_Phi s θ te) :=
  Real.measurable_log.comp ((te_measurable_eP s te).div (te_measurable_pP s θ te))

/-- The partial effect factor as an average over the `2^|C|` rows of the block. -/
lemma te_U_eq (z : Param N) {j : Fin N} :
    te_U s θ te z j = (∑ r ∈ agree (profile θ j)ᶜ s, (tpmOf z).prob j r (te j)) /
      2 ^ (profile θ j).card := by
  unfold te_U effUnit
  rw [card_agree, card_compl, Fintype.card_fin]
  have hc : (profile θ j).card ≤ N := by simpa using card_le_univ (profile θ j)
  rw [show N - (N - (profile θ j).card) = (profile θ j).card by omega]
  push_cast
  rfl

end Effect

/-! ### The slice estimate -/

lemma te_log_sub_ge {h1 h2 : ℝ} (h1p : 0 < h1) (h2p : 0 < h2) (h1l : h1 ≤ 1) (h2l : h2 ≤ 1) :
    |h1 - h2| ≤ |Real.log h1 - Real.log h2| := by
  rcases le_total h1 h2 with h | h
  · have hl := Real.log_le_sub_one_of_pos (div_pos h1p h2p)
    rw [Real.log_div h1p.ne' h2p.ne'] at hl
    have hq : h1 / h2 - 1 ≤ h1 - h2 := by
      rw [div_sub_one h2p.ne', div_le_iff₀ h2p]; nlinarith
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h), abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 (Real.log_le_log h1p h))]
    linarith
  · have hl := Real.log_le_sub_one_of_pos (div_pos h2p h1p)
    rw [Real.log_div h2p.ne' h1p.ne'] at hl
    have hq : h2 / h1 - 1 ≤ h2 - h1 := by
      rw [div_sub_one h1p.ne', div_le_iff₀ h1p]; nlinarith
    rw [abs_of_nonneg (sub_nonneg.2 h), abs_of_nonneg (sub_nonneg.2 (Real.log_le_log h2p h))]
    linarith

/-- `|y₁/(y₁+R) - y₂/(y₂+R)| ≥ R |y₁ - y₂| / L²` when `0 < yᵢ + R ≤ L`. -/
lemma te_frac_sub_ge {y1 y2 R L : ℝ} (hR : 0 ≤ R) (h1 : 0 < y1 + R) (h2 : 0 < y2 + R)
    (h1L : y1 + R ≤ L) (h2L : y2 + R ≤ L) :
    R * |y1 - y2| / L ^ 2 ≤ |y1 / (y1 + R) - y2 / (y2 + R)| := by
  have e : y1 / (y1 + R) - y2 / (y2 + R) = R * (y1 - y2) / ((y1 + R) * (y2 + R)) := by
    field_simp; ring
  rw [e, abs_div, abs_mul, abs_of_nonneg hR, abs_of_pos (mul_pos h1 h2)]
  have hL : 0 < L := lt_of_lt_of_le h1 h1L
  apply div_le_div_of_nonneg_left (by positivity) (mul_pos h1 h2)
  calc (y1 + R) * (y2 + R) ≤ L * L := mul_le_mul h1L h2L h2.le hL.le
    _ = L ^ 2 := by ring

section Slice

variable {s : State N} {S : Finset (Fin N)} {θ : SysPartition N S} {te : State N}

lemma te_mem_agree_self (P : Finset (Fin N)) (s : State N) : s ∈ agree Pᶜ s := self_mem_agree _ _

lemma te_prob_le_one (z : Param N) (j : Fin N) (r : State N) (b : Bool) :
    (tpmOf z).prob j r b ≤ 1 := (tpmOf z).le_one j r b

/-- Changing the single entry `z s i` of a cut unit `i`: the log-ratio moves by at least
`y' 4^{-|S|}` times the change, `y'` the entry of `i` in another row `s'` of its block. -/
lemma te_Phi_sep {i : Fin N} (hi : i ∈ S) {s' : State N} (hs' : s' ∈ agree (profile θ i)ᶜ s)
    (hss : s' ≠ s) {z1 z2 : Param N} (hz1 : z1 ∈ openCube N) (hz2 : z2 ∈ openCube N)
    (hdiff : ∀ r j, (r, j) ≠ (s, i) → z1 r j = z2 r j) :
    (tpmOf z1).prob i s' (te i) * |z1 s i - z2 s i| / (4 : ℝ) ^ S.card ≤
      |te_Phi s θ te z1 - te_Phi s θ te z2| := by
  set P := profile θ i with hPdef
  have hPS : P ⊆ S := prof_profile_subset θ i
  set y1 := (tpmOf z1).prob i s (te i) with hy1
  set y2 := (tpmOf z2).prob i s (te i) with hy2
  set R := ∑ r ∈ (agree Pᶜ s).erase s, (tpmOf z1).prob i r (te i) with hRdef
  have hR2 : R = ∑ r ∈ (agree Pᶜ s).erase s, (tpmOf z2).prob i r (te i) := by
    refine sum_congr rfl fun r hr => ?_
    have hrs : r ≠ s := ne_of_mem_erase hr
    simp only [te_prob_eq, hdiff r i (fun h => hrs (Prod.mk.inj h).1)]
  have hsplit : ∀ z : Param N, ∑ r ∈ agree Pᶜ s, (tpmOf z).prob i r (te i) =
      (tpmOf z).prob i s (te i) + ∑ r ∈ (agree Pᶜ s).erase s, (tpmOf z).prob i r (te i) :=
    fun z => (add_sum_erase _ _ (te_mem_agree_self P s)).symm
  have hU1 : te_U s θ te z1 i = (y1 + R) / 2 ^ P.card := by rw [te_U_eq, hsplit]
  have hU2 : te_U s θ te z2 i = (y2 + R) / 2 ^ P.card := by rw [te_U_eq, hsplit, ← hR2]
  -- the other units do not change
  have hj : ∀ j ∈ S.erase i, (tpmOf z1).prob j s (te j) / te_U s θ te z1 j =
      (tpmOf z2).prob j s (te j) / te_U s θ te z2 j := by
    intro j hj
    have hji : j ≠ i := ne_of_mem_erase hj
    have hc : ∀ r, (tpmOf z1).prob j r (te j) = (tpmOf z2).prob j r (te j) := by
      intro r
      simp only [te_prob_eq, hdiff r j (fun h => hji (Prod.mk.inj h).2)]
    unfold te_U effUnit
    simp_rw [hc]
  -- positivity
  have hy1p : 0 < y1 := prob_pos hz1 _ _ _
  have hy2p : 0 < y2 := prob_pos hz2 _ _ _
  have hy'p : 0 < (tpmOf z1).prob i s' (te i) := prob_pos hz1 _ _ _
  have hs'mem : s' ∈ (agree Pᶜ s).erase s := mem_erase.2 ⟨hss, hs'⟩
  have hRge : (tpmOf z1).prob i s' (te i) ≤ R :=
    single_le_sum (fun r _ => (tpmOf z1).nonneg i r _) hs'mem
  have hR0 : 0 ≤ R := hy'p.le.trans hRge
  have hcard : ((agree Pᶜ s).card : ℝ) = 2 ^ P.card := by
    rw [card_agree, card_compl, Fintype.card_fin]
    have hc : P.card ≤ N := by simpa using card_le_univ P
    rw [show N - (N - P.card) = P.card by omega]
    push_cast; ring
  have hsumle : ∀ z : Param N, ∑ r ∈ agree Pᶜ s, (tpmOf z).prob i r (te i) ≤ 2 ^ P.card := by
    intro z
    rw [← hcard]
    exact (sum_le_card_nsmul _ _ 1 fun r _ => te_prob_le_one z i r _).trans (by simp)
  have hL1 : y1 + R ≤ 2 ^ P.card := by have := hsumle z1; rw [hsplit] at this; exact this
  have hL2 : y2 + R ≤ 2 ^ P.card := by have := hsumle z2; rw [hsplit, ← hR2] at this; exact this
  have hPk : (2 : ℝ) ^ P.card ≤ 2 ^ S.card :=
    pow_le_pow_right₀ (by norm_num) (card_le_card hPS)
  -- the log-ratio splits off unit `i`
  have hQ : ∀ z : Param N, z ∈ openCube N →
      sysEffProb (tpmOf z) S s s te / sysPartEffProb (tpmOf z) S s θ s te =
        ((tpmOf z).prob i s (te i) / te_U s θ te z i) *
          ∏ j ∈ S.erase i, (tpmOf z).prob j s (te j) / te_U s θ te z j := by
    intro z _
    rw [te_eP_eq, te_pP_eq, ← Finset.prod_div_distrib]
    exact (mul_prod_erase S (fun j => (tpmOf z).prob j s (te j) / te_U s θ te z j) hi).symm
  have hrest_pos : 0 < ∏ j ∈ S.erase i, (tpmOf z1).prob j s (te j) / te_U s θ te z1 j :=
    prod_pos fun j _ => div_pos (prob_pos hz1 _ _ _) (effUnit_pos hz1 _ _ _ _)
  have hrest : ∏ j ∈ S.erase i, (tpmOf z1).prob j s (te j) / te_U s θ te z1 j =
      ∏ j ∈ S.erase i, (tpmOf z2).prob j s (te j) / te_U s θ te z2 j := prod_congr rfl hj
  have h2P : (0 : ℝ) < 2 ^ P.card := by positivity
  have hq1 : (tpmOf z1).prob i s (te i) / te_U s θ te z1 i = 2 ^ P.card * (y1 / (y1 + R)) := by
    rw [hU1, div_div_eq_mul_div]; ring
  have hq2 : (tpmOf z2).prob i s (te i) / te_U s θ te z2 i = 2 ^ P.card * (y2 / (y2 + R)) := by
    rw [hU2, div_div_eq_mul_div]; ring
  have hh1p : 0 < y1 / (y1 + R) := div_pos hy1p (by linarith)
  have hh2p : 0 < y2 / (y2 + R) := div_pos hy2p (by linarith)
  have hh1l : y1 / (y1 + R) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  have hh2l : y2 / (y2 + R) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  have hPhi : te_Phi s θ te z1 - te_Phi s θ te z2 =
      Real.log (y1 / (y1 + R)) - Real.log (y2 / (y2 + R)) := by
    unfold te_Phi
    rw [hQ z1 hz1, hQ z2 hz2, hq1, hq2, ← hrest]
    rw [Real.log_mul (by positivity) hrest_pos.ne', Real.log_mul (by positivity) hrest_pos.ne',
      Real.log_mul h2P.ne' hh1p.ne', Real.log_mul h2P.ne' hh2p.ne']
    ring
  rw [hPhi]
  refine le_trans ?_ (te_log_sub_ge hh1p hh2p hh1l hh2l)
  have hyy : |y1 - y2| = |z1 s i - z2 s i| := by
    rw [hy1, hy2, te_prob_eq, te_prob_eq,
      clamp01_of_mem (Set.Ioo_subset_Icc_self (hz1 s i)),
      clamp01_of_mem (Set.Ioo_subset_Icc_self (hz2 s i))]
    cases te i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show 1 - z1 s i - (1 - z2 s i) = -(z1 s i - z2 s i) by ring, abs_neg]
    · simp
  have hfrac := te_frac_sub_ge hR0 (by linarith) (by linarith) hL1 hL2
  rw [hyy] at hfrac
  refine le_trans ?_ hfrac
  have h4 : ((2 : ℝ) ^ P.card) ^ 2 ≤ (4 : ℝ) ^ S.card := by
    calc ((2 : ℝ) ^ P.card) ^ 2 ≤ ((2 : ℝ) ^ S.card) ^ 2 := pow_le_pow_left₀ h2P.le hPk 2
      _ = (4 : ℝ) ^ S.card := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hn : 0 ≤ (tpmOf z1).prob i s' (te i) * |z1 s i - z2 s i| := by positivity
  calc (tpmOf z1).prob i s' (te i) * |z1 s i - z2 s i| / (4 : ℝ) ^ S.card
      ≤ (tpmOf z1).prob i s' (te i) * |z1 s i - z2 s i| / ((2 : ℝ) ^ P.card) ^ 2 :=
        div_le_div_of_nonneg_left hn (by positivity) h4
    _ ≤ R * |z1 s i - z2 s i| / ((2 : ℝ) ^ P.card) ^ 2 := by gcongr

end Slice

/-! ### The effect event -/

/-- A unit with a nonempty profile. -/
lemma te_exists_cut {S : Finset (Fin N)} (θ : SysPartition N S) :
    ∃ i ∈ S, (profile θ i).Nonempty := by
  have h := sysCutCount_pos θ
  rw [sysCutCount_eq_sum_profile] at h
  obtain ⟨i, hi, hpos⟩ := exists_pos_of_sum_pos h
  exact ⟨i, hi, card_pos.1 hpos⟩
where
  exists_pos_of_sum_pos {s : Finset (Fin N)} {f : Fin N → ℕ} (h : 0 < ∑ i ∈ s, f i) :
      ∃ i ∈ s, 0 < f i := by
    by_contra hne
    push Not at hne
    have : ∑ i ∈ s, f i = 0 := sum_eq_zero fun i hi => Nat.le_zero.1 (hne i hi)
    omega

/-- **Small positive effect sides are rare**: for `0 ≤ a ≤ 1`, `0 ≤ b`, `0 < ρ` and
`δ ≤ a^|S| b`, `P(0 < sysPhiE(θ; te) < δ) ≤ |S| a + ρ + 4^|S| b / ρ`. -/
theorem te_eff_le (s : State N) {S : Finset (Fin N)} (θ : SysPartition N S) (te : State N)
    {a b ρ δ : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hρ : 0 < ρ)
    (hδ : δ ≤ a ^ S.card * b) :
    cubeM N {z | z ∈ openCube N ∧ 0 < sysPhiE (tpmOf z) S s θ s te ∧
      sysPhiE (tpmOf z) S s θ s te < δ} ≤
      ENNReal.ofReal (S.card * a + ρ + 4 ^ S.card * b / ρ) := by
  obtain ⟨i, hi, i', hi'⟩ : ∃ i ∈ S, ∃ i', i' ∈ profile θ i := by
    obtain ⟨i, hi, hne⟩ := te_exists_cut θ
    exact ⟨i, hi, hne⟩
  have hi'S : i' ∈ S := prof_profile_subset θ i hi'
  have hii : i' ≠ i := by
    intro h
    rw [h] at hi'
    have hm := (prof_partOf_mem θ hi)
    unfold profile at hi'
    rw [cd_mem_cutSet θ hm.1 hi] at hi'
    exact hi'.1 hm.2
  set s' : State N := Function.update s i' (!s i') with hs'def
  have hs' : s' ∈ agree (profile θ i)ᶜ s := by
    rw [mem_agree]
    intro j hj
    have hji : j ≠ i' := fun h => (mem_compl.1 hj) (h ▸ hi')
    simp [hs'def, hji]
  have hss : s' ≠ s := by
    intro h
    have := congrFun h i'
    simp [hs'def] at this
  -- the three events
  set A : Set (Param N) := ⋃ j ∈ S, {z | (tpmOf z).prob j s (te j) < a} with hA
  set B : Set (Param N) := {z | (tpmOf z).prob i s' (te i) < ρ} with hB
  set E : Set (Param N) := {z | z ∈ openCube N ∧ 0 < te_Phi s θ te z ∧ te_Phi s θ te z < b ∧
    ρ ≤ (tpmOf z).prob i s' (te i)} with hE
  have hsub : {z | z ∈ openCube N ∧ 0 < sysPhiE (tpmOf z) S s θ s te ∧
      sysPhiE (tpmOf z) S s θ s te < δ} ⊆ A ∪ B ∪ E := by
    rintro z ⟨hz, h0, hδz⟩
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    obtain ⟨⟨hAn', hBn'⟩, hEn⟩ := hnot
    have hAn : ∀ j ∈ S, a ≤ (tpmOf z).prob j s (te j) := fun j hj =>
      not_lt.1 fun h => hAn' (Set.mem_biUnion hj h)
    have hBn : ρ ≤ (tpmOf z).prob i s' (te i) := not_lt.1 hBn'
    have heP := sysEffProb_pos hz s S te
    have hpP := sysPartEffProb_pos hz s S θ te
    have hlogpos : 0 < Real.logb 2 (sysEffProb (tpmOf z) S s s te /
        sysPartEffProb (tpmOf z) S s θ s te) := by
      by_contra hle
      push Not at hle
      have : sysPhiE (tpmOf z) S s θ s te = 0 := by
        unfold sysPhiE pos; rw [max_eq_left hle, mul_zero]
      linarith
    have hPhi_pos : 0 < te_Phi s θ te z :=
      Real.log_pos ((Real.logb_pos_iff one_lt_two (div_pos heP hpP)).1 hlogpos)
    have hlogb_ge : b ≤ Real.logb 2 (sysEffProb (tpmOf z) S s s te /
        sysPartEffProb (tpmOf z) S s θ s te) := by
      by_contra hlt
      push Not at hlt
      have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      have hPhi_lt : te_Phi s θ te z < b := by
        have e1 : te_Phi s θ te z = Real.logb 2 (sysEffProb (tpmOf z) S s s te /
            sysPartEffProb (tpmOf z) S s θ s te) * Real.log 2 := by
          unfold te_Phi Real.logb; field_simp
        rw [e1]
        have hl2' : Real.log 2 < 1 := by
          have := Real.log_two_lt_d9; linarith
        nlinarith
      exact hEn ⟨hz, hPhi_pos, hPhi_lt, hBn⟩
    have heP_ge : a ^ S.card ≤ sysEffProb (tpmOf z) S s s te := by
      rw [te_eP_eq, ← prod_const]
      exact prod_le_prod (fun _ _ => ha) fun j hj => hAn j hj
    have : δ ≤ sysPhiE (tpmOf z) S s θ s te := by
      unfold sysPhiE pos
      rw [max_eq_right hlogpos.le]
      calc δ ≤ a ^ S.card * b := hδ
        _ ≤ sysEffProb (tpmOf z) S s s te * Real.logb 2 (sysEffProb (tpmOf z) S s s te /
            sysPartEffProb (tpmOf z) S s θ s te) :=
          mul_le_mul heP_ge hlogb_ge hb heP.le
    linarith
  -- measures
  have hmA : cubeM N A ≤ ENNReal.ofReal (S.card * a) := by
    refine (measure_biUnion_finset_le S _).trans ?_
    calc ∑ j ∈ S, cubeM N {z | (tpmOf z).prob j s (te j) < a}
        ≤ ∑ _j ∈ S, ENNReal.ofReal a := sum_le_sum fun j _ => te_cubeM_prob_lt j s _ a
      _ = ENNReal.ofReal (S.card * a) := by
          rw [sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
  have hmB : cubeM N B ≤ ENNReal.ofReal ρ := te_cubeM_prob_lt i s' _ ρ
  have hEm : MeasurableSet E := by
    refine te_measurableSet_openCube.inter ?_
    refine (measurableSet_lt measurable_const (te_measurable_Phi s θ te)).inter
      ((measurableSet_lt (te_measurable_Phi s θ te) measurable_const).inter
        (measurableSet_le measurable_const (te_measurable_prob i s' _)))
  have hD : 0 ≤ 4 ^ S.card * b / ρ := by positivity
  have hmE : cubeM N E ≤ ENNReal.ofReal (4 ^ S.card * b / ρ) := by
    refine te_cube_slice hEm s i hD fun x row t1 t2 _ _ h1 h2 => ?_
    set z1 := Function.update x s (Function.update row i t1)
    set z2 := Function.update x s (Function.update row i t2)
    obtain ⟨hz1, hp1, hl1, hr1⟩ := h1
    obtain ⟨hz2, hp2, hl2, _⟩ := h2
    have hdiff : ∀ r j, (r, j) ≠ (s, i) → z1 r j = z2 r j := by
      intro r j hrj
      by_cases hr : r = s
      · subst hr
        have hj : j ≠ i := fun h => hrj (by rw [h])
        simp [z1, z2, hj]
      · simp [z1, z2, hr]
    have hsep := te_Phi_sep (te := te) hi hs' hss hz1 hz2 hdiff
    have h1v : z1 s i = t1 := by simp [z1]
    have h2v : z2 s i = t2 := by simp [z2]
    rw [h1v, h2v] at hsep
    have hdist : |te_Phi s θ te z1 - te_Phi s θ te z2| ≤ b := by
      rw [abs_le]; constructor <;> linarith
    have h4 : (0 : ℝ) < 4 ^ S.card := by positivity
    rw [le_div_iff₀ hρ]
    have hsep' := hsep.trans hdist
    rw [div_le_iff₀ h4] at hsep'
    have : ρ * |t1 - t2| ≤ (tpmOf z1).prob i s' (te i) * |t1 - t2| :=
      mul_le_mul_of_nonneg_right hr1 (abs_nonneg _)
    nlinarith
  calc cubeM N {z | z ∈ openCube N ∧ 0 < sysPhiE (tpmOf z) S s θ s te ∧
        sysPhiE (tpmOf z) S s θ s te < δ}
      ≤ cubeM N (A ∪ B ∪ E) := measure_mono hsub
    _ ≤ cubeM N A + cubeM N B + cubeM N E := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (S.card * a) + ENNReal.ofReal ρ + ENNReal.ofReal (4 ^ S.card * b / ρ) :=
        add_le_add (add_le_add hmA hmB) hmE
    _ = ENNReal.ofReal (S.card * a + ρ + 4 ^ S.card * b / ρ) := by
        rw [ENNReal.ofReal_add (by positivity) hD, ENNReal.ofReal_add (by positivity) hρ.le]

end

end Census
end IIT
