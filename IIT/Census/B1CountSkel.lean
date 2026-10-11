/-
Census, B1: the count package (D3', W9 Theorem CE + Lemma DET) as a SKELETON.

`count_package` of `B1Skeleton.lean` asks for a measurable bad set per `(r0, x, σ)` such that
(DET) good F-data outside `Bad` are not in `SmallW`, and (CE) the fresh-row probability of `Bad`
is `≤ e^{-cCnt N}` uniformly over `GoodFX`.

Choice of the bad set.  Instead of W9's `BadCount` (a Boolean combination of row statistics,
whose DET needs W5's whole Lemma DIST), we take the bad set to be the *conclusion* of DIST:

    BadMech N s := {w | ∀ t, #{M | DistOK s t w M} < 2^(N/8) + 2N},

where `DistOK s t w M` says, for `T := tpmOf (flipP s w)`: `M` is a conditioned distinction
mechanism of `U` at `s`, its maximal cause purview is exactly `(univ, t)`, and
`φ_d ≥ 2N·2^{-N}` (exactly the three hypotheses of A2, `PhiOfAt_ge_of_mechs`).

* `measurableSet_BadMech`  — PROVED (via `B1CountMeas.lean`).
* `notSmall_of_not_badMech` (Lemma DET) — PROVED, for every `N ≥ 1`, without using `GoodFX`
  (A2 + `two_pow_two_pow_le`).
* `count_package_X` — the exact statement of `B1Skeleton.count_package`, PROVED from the single
  open leaf `count_exp_famX` below (through `badMech_subset_badFam`, PROVED).

The open leaf `count_exp_famX` is W9 Theorem CE composed with W5 Lemma DIST: given `f ∈ GoodFX`,
with fresh-row probability `≥ 1 - e^{-cCnt N}` at least `2^(N/8) + 2N` sets `K ∈ famX` make
`U \ K` a certified distinction with cause purview `(univ, r0)`.  (W9 §4.2: on `BadCountᶜ`,
`L ≥ |famX|/(720 ln N) ≥ 2^(N/8) + 2N` such `K`; W9 §5: `freshM(BadCount) ≤ e^{-N/500}`.)
-/
import IIT.Census.B1CountMeas
import IIT.Census.B1Family

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### Definitions -/

/-- `M` is a certified distinction mechanism of `U` at `s` (in flipped coordinates `w`), with
unique maximal cause purview `(univ, t)` and `φ_d ≥ 2N·2^{-N}`: the hypotheses of A2. -/
def DistOK (s t : State N) (w : Param N) (M : Finset (Fin N)) : Prop :=
  M ∈ distinctionMechsAt (tpmOf (flipP s w)) univ s s ∧
    maxCausePurviewsAt (tpmOf (flipP s w)) univ s M s = {(univ, t)} ∧
    2 * (N : ℝ) * (2 : ℝ) ^ (-(N : ℤ)) ≤ phiDAt (tpmOf (flipP s w)) univ s M s

/-- The number of certified mechanisms the count must produce. -/
def LCnt (N : ℕ) : ℕ := 2 ^ (N / 8) + 2 * N

/-- **The bad set of the count**: for no cause state `t` are there `LCnt N` certified mechanisms. -/
def BadMech (N : ℕ) (s : State N) : Set (Param N) :=
  {w | ∀ t : State N, (univ.filter (DistOK s t w)).card < LCnt N}

/-- The family-restricted bad set used by the open leaf: fewer than `LCnt N` sets `K ∈ famX`
make `U \ K` certified with cause purview `(univ, r0)`. -/
def BadFam (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) : Set (Param N) :=
  {w | ((famX N s r0 x σ w).filter fun K => DistOK s r0 w (univ \ K)).card < LCnt N}

/-! ### Measurability (proved) -/

theorem measurableSet_DistOK (s t : State N) (M : Finset (Fin N)) :
    MeasurableSet {w : Param N | DistOK s t w M} := by
  have h : {w : Param N | DistOK s t w M} = flipP s ⁻¹'
      ({p | M ∈ distinctionMechsAt (tpmOf p) univ s s} ∩
        {p | maxCausePurviewsAt (tpmOf p) univ s M s = {(univ, t)}} ∩
        {p | 2 * (N : ℝ) * (2 : ℝ) ^ (-(N : ℤ)) ≤ phiDAt (tpmOf p) univ s M s}) := by
    ext w; simp only [DistOK, Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]
  rw [h]
  exact (mp_flipP s).measurable
    (((b1c_mem_distinctionMechsAt univ s s M).inter (b1c_maxCausePurviewsAt_eq univ s M s _)).inter
      (measurableSet_le measurable_const (b1c_phiDAt univ s M s)))

theorem measurableSet_BadMech (s : State N) : MeasurableSet (BadMech N s) := by
  have h : BadMech N s = ⋂ t : State N, {w | LCnt N ≤ (univ.filter (DistOK s t w)).card}ᶜ := by
    ext w; simp [BadMech]
  rw [h]
  exact MeasurableSet.iInter fun t =>
    (b1_measurableSet_card_filter_ge (fun M => measurableSet_DistOK s t M) (LCnt N)).compl

/-! ### Lemma DET (proved) -/

/-- **Lemma DET.** Outside `BadMech`, every selector gives `Φ(U) ≥ 2 ^ 2 ^ (N / 8)`, so `w ∉ SmallW`. -/
theorem notSmall_of_not_badMech (hN : 1 ≤ N) {s : State N} {w : Param N}
    (h : w ∉ BadMech N s) : w ∉ SmallW N s := by
  simp only [BadMech, Set.mem_setOf_eq, not_forall, not_lt] at h
  obtain ⟨t, ht⟩ := h
  rintro ⟨-, σ, hσ⟩
  set Ms := univ.filter (DistOK s t w) with hMs
  have hc : (0 : ℝ) < (2 : ℝ) ^ (-(N : ℤ)) := by positivity
  have hge := PhiOfAt_ge_of_mechs_of_le_card (tpmOf (flipP s w)) s s σ Ms t hc
    (fun M hM => (mem_filter.1 hM).2.1) (fun M hM => (mem_filter.1 hM).2.2.1)
    (fun M hM => (mem_filter.1 hM).2.2.2) (le_refl Ms.card)
  have harith := two_pow_two_pow_le hN (L := Ms.card) ht (le_refl ((2 : ℝ) ^ (-(N : ℤ))))
  linarith

/-! ### From the family count to `BadMech` (proved) -/

theorem badMech_subset_badFam (s r0 : State N) (x : Fin N) (σ : XSide) :
    BadMech N s ⊆ BadFam N s r0 x σ := by
  intro w hw
  have h1 := hw r0
  show ((famX N s r0 x σ w).filter fun K => DistOK s r0 w (univ \ K)).card < LCnt N
  refine lt_of_le_of_lt ?_ h1
  have hinj : Function.Injective fun K : Finset (Fin N) => univ \ K := by
    intro K K' hKK'
    have := congrArg (fun A : Finset (Fin N) => univ \ A) hKK'
    simpa [Finset.sdiff_sdiff_eq_self (subset_univ _)] using this
  rw [← card_image_of_injective _ hinj]
  refine card_le_card fun M hM => ?_
  obtain ⟨K, hK, rfl⟩ := mem_image.1 hM
  exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hK).2⟩

/-! ### The open leaf -/


/-! ### Assembly (proved from `count_exp_famX`) -/

theorem count_exp_mech_of
    (hfam : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide),
      ∀ f ∈ GoodFX N s r0 x σ,
        rowsOutM (sensRows s r0) {g | glueRows (sensRows s r0) f g ∈ BadFam N s r0 x σ}
          ≤ ENNReal.ofReal (Real.exp (-(cCnt * N)))) :
    ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide),
      ∀ f ∈ GoodFX N s r0 x σ,
        rowsOutM (sensRows s r0) {g | glueRows (sensRows s r0) f g ∈ BadMech N s}
          ≤ ENNReal.ofReal (Real.exp (-(cCnt * N))) := by
  filter_upwards [hfam] with N h s r0 x σ f hf
  exact le_trans (measure_mono fun g hg => badMech_subset_badFam s r0 x σ hg) (h s r0 x σ f hf)

/-- **`count_package`, exactly as stated in `B1Skeleton.lean`**, from the mechanism count. -/
theorem count_package_of
    (hmech : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide),
      ∀ f ∈ GoodFX N s r0 x σ,
        rowsOutM (sensRows s r0) {g | glueRows (sensRows s r0) f g ∈ BadMech N s}
          ≤ ENNReal.ofReal (Real.exp (-(cCnt * N)))) :
    ∀ᶠ N in atTop, ∀ s : State N,
      ∃ Bad : State N → Fin N → XSide → Set (Param N),
        (∀ r0 x σ, MeasurableSet (Bad r0 x σ)) ∧
        (∀ r0 x σ (w : Param N), restrIn (sensRows s r0) w ∈ GoodFX N s r0 x σ →
          w ∉ Bad r0 x σ → w ∉ SmallW N s) ∧
        (∀ r0 x σ, ∀ f ∈ GoodFX N s r0 x σ,
          rowsOutM (sensRows s r0) {g | glueRows (sensRows s r0) f g ∈ Bad r0 x σ}
            ≤ ENNReal.ofReal (Real.exp (-(cCnt * N)))) := by
  filter_upwards [hmech, eventually_ge_atTop 1] with N h hN s
  exact ⟨fun _ _ _ => BadMech N s, fun _ _ _ => measurableSet_BadMech s,
    fun _ _ _ _ _ hw => notSmall_of_not_badMech hN hw, fun r0 x σ f hf => h s r0 x σ f hf⟩


end Census
end IIT

#print axioms IIT.Census.measurableSet_BadMech
#print axioms IIT.Census.notSmall_of_not_badMech
#print axioms IIT.Census.badMech_subset_badFam
#print axioms IIT.Census.count_exp_mech_of
#print axioms IIT.Census.count_package_of
