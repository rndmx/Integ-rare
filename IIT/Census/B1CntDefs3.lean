/-
Census, B1: the definitions of the count over `GoodX3` (`CountX3Stmt`, `B1GoodX3.lean`), with FIXED interfaces.
(Supersedes the GoodX2 version `B1CntDefs.lean`; uses only `B1GoodX3` objects: `lowU`, `NewX3`, `famX3`, `GoodX3`.)

Blueprint: `iit-census/lean/B1-W14-count-lean.md` (W14).  Mathematics: W5 §§2-8, W7 §§4-5, W9 §5,
the two W13 audits (their fixes are built in: lowU-in-K floor/pairLow/x5e from `NewX3`, threshold `x0 N + slT`
in FE6/Ret, FE4/FE5 at `d = dX`, `D≤` over `2 ≤ r ≤ rD`, null sets in `fe0`).

Contents.
* §1 constants (`D0C`, `JC`, `rD`, `mX`, `kap0`, `epsN`, `kapN`, `sigC`, `A0C`, `x2C`, `pY`);
* §2 statistics in flipped coordinates (`subMean`, `effDevA`, `fK`, `hK`, `rowTX`, `freshRows`) and
  their bridges to the IIT definitions (`effUnit`, `fullProb`, `prob … (teW …)`), PROVED;
* §3 the K-free fresh event `CountFreshX` (FE0-FE7(b)');
* §4 the per-K events `RetK`, `CoreAt`/`CoreK`, `SignK`, `DleAt`, `YK`;
* §5 the counts `WCnt`, `RFCnt`, the bad sets `RetBad`, `WBad`, `BadCountX`;
* §6 `GoodW3` (the `Param`-level form of `GoodX3`) and the transfer `goodW3_glue`, PROVED;
* §7 the work-package interfaces (`…Stmt : Prop`), assembled in `B1CntGlue3.lean`.
No `sorry`, no axioms.
-/
import IIT.Census.B1GoodX3

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ## 1. Constants -/

/-- Big-cut dimension threshold `D0 = 2 log₂ N + 14` (W5 §2). -/
def D0C (N : ℕ) : ℕ := 2 * Nat.log 2 N + 14

/-- Near-full purview threshold `J = 6 log₂ N + 16` (W5 §2). -/
def JC (N : ℕ) : ℕ := 6 * Nat.log 2 N + 16

/-- Range of the probabilistic `(D)` conditions, `r_D ≥ 3 log₂ N + 10` (W9 §2). -/
def rD (N : ℕ) : ℕ := 3 * Nat.log 2 N + 13

/-- `m = N - d`, the mechanism size, as a real. -/
noncomputable def mX (N : ℕ) : ℝ := ((N - dX N : ℕ) : ℝ)

/-- `κ0 = d² 2^{-d}`: the shift of a coin variable by the fixed rows of `Ball(s, 2)` (W5 6.1). -/
noncomputable def kap0 (N : ℕ) : ℝ := (dX N : ℝ) ^ 2 / 2 ^ dX N

/-- `ε_N = 2 √N 2^{-N/2} + 2 N⁴ 2^{-N}`: column-mean deviation (W5 FE1'). -/
noncomputable def epsN (N : ℕ) : ℝ := 2 * Real.sqrt ((N : ℝ) / 2 ^ N) + 2 * (N : ℝ) ^ 4 / 2 ^ N

/-- `κ_N = 6 ln N 2^{-d} + 4 κ0 + 8 ε_N` (W5 1.4(c)). -/
noncomputable def kapN (N : ℕ) : ℝ := 6 * Real.log N / 2 ^ dX N + 4 * kap0 N + 8 * epsN N

/-- `σ = 2^{-d/2}/√12`, the scale of a coin variable. -/
noncomputable def sigC (N : ℕ) : ℝ := Real.sqrt (1 / (12 * 2 ^ dX N))

/-- The coin threshold `A_0 = σ √(2 ln N)` (explicit; replaces W5's Gaussian quantile). -/
noncomputable def A0C (N : ℕ) : ℝ := sigC N * Real.sqrt (2 * Real.log N)

/-- The coin ceiling `x_2 = σ √(6 ln N)`. -/
noncomputable def x2C (N : ℕ) : ℝ := sigC N * Real.sqrt (6 * Real.log N)

/-- The guaranteed mean of a counted indicator, `E Y_K ≥ pY N` (true value `≍ 1/√(ln N)`). -/
noncomputable def pY (N : ℕ) : ℝ := 1 / (1000 * Real.log N)

/-! ## 2. Statistics in flipped coordinates, and their IIT meaning -/

/-- The rows outside `Sens = sensRows s r0` (the fresh rows). -/
noncomputable def freshRows (s r0 : State N) : Finset (State N) :=
  univ.filter fun r => r ∉ sensRows s r0

/-- Mean of `y_{·,i}` over the subcube `agree A t` (`= effUnit … A t i (s i)`). -/
noncomputable def subMean (w : Param N) (A : Finset (Fin N)) (t : State N) (i : Fin N) : ℝ :=
  (∑ r ∈ agree A t, clamp01 (w r i)) / ((agree A t).card : ℝ)

/-- Deviation `eU(A, k, te_k) - 1/2` of the te-oriented column `k` on the subcube `agree A t`. -/
noncomputable def effDevA (w : Param N) (s : State N) (A : Finset (Fin N)) (t : State N)
    (k : Fin N) : ℝ :=
  (∑ r ∈ agree A t, (pTe w s r k - 1 / 2)) / ((agree A t).card : ℝ)

/-- `f_k` of W5 6.1 for `M = U \ K`: the deviation on `C_0 = agree (U \ K) s`. -/
noncomputable def fK (w : Param N) (s : State N) (K : Finset (Fin N)) (k : Fin N) : ℝ :=
  effDevA w s (univ \ K) s k

/-- `h_j(k)` of W5 6.1: the deviation on `C_j = agree (U \ K) (s^j)`. -/
noncomputable def hK (w : Param N) (s : State N) (K : Finset (Fin N)) (j k : Fin N) : ℝ :=
  effDevA w s (univ \ K) (flipAt j s) k

/-- `sign(a) · b` (the value at `a = 0` is irrelevant: every use has `|a| > 0`). -/
noncomputable def sgnMul (a b : ℝ) : ℝ := if 0 < a then b else -b

/-- `Π_k T_k(r, t_k)` in flipped coordinates (`= fullProb (tpmOf (flipP s w)) r t`). -/
noncomputable def rowTX (w : Param N) (s r t : State N) : ℝ :=
  ∏ k, (if t k = s k then clamp01 (w r k) else 1 - clamp01 (w r k))

/-! ### Bridges (proved) -/

lemma prob_flipP_self (s : State N) (w : Param N) (r : State N) (i : Fin N) :
    (tpmOf (flipP s w)).prob i r (s i) = clamp01 (w r i) := by
  simp only [tpmOf, flipP, flipC]
  cases h : s i <;> simp [clamp01_one_sub]

lemma prob_flipP_teW (s : State N) (w : Param N) (r : State N) (k : Fin N) :
    (tpmOf (flipP s w)).prob k r (teW w s k) = pTe w s r k := by
  have h := prob_teW_row (flipP s w) s r k
  rwa [flipP_invol s w] at h

lemma effUnit_flipP_self (s : State N) (w : Param N) (A : Finset (Fin N)) (t : State N)
    (i : Fin N) : effUnit (tpmOf (flipP s w)) A t i (s i) = subMean w A t i := by
  unfold effUnit subMean
  congr 1
  exact sum_congr rfl fun r _ => prob_flipP_self s w r i

lemma effUnit_flipP_teW (s : State N) (w : Param N) (A : Finset (Fin N)) (t : State N)
    (k : Fin N) : effUnit (tpmOf (flipP s w)) A t k (teW w s k) - 1 / 2 = effDevA w s A t k := by
  have hc : ((agree A t).card : ℝ) ≠ 0 := (Nat.cast_pos.2 (card_agree_pos A t)).ne'
  unfold effUnit effDevA
  rw [sum_congr rfl fun r _ => prob_flipP_teW s w r k, sum_sub_distrib, sum_const, nsmul_eq_mul,
    eq_div_iff hc, sub_mul, div_mul_cancel₀ _ hc]
  ring

lemma fullProb_flipP (s : State N) (w : Param N) (r t : State N) :
    fullProb (tpmOf (flipP s w)) r t = rowTX w s r t := by
  unfold fullProb rowTX
  refine prod_congr rfl fun k _ => ?_
  simp only [tpmOf, flipP, flipC]
  cases h1 : t k <;> cases h2 : s k <;> simp [clamp01_one_sub]

/-- `rowsOutM`-probabilities of glued events are `cubeM`-probabilities (so the entry-level tools of
`B1Prod` §5 apply: `mp_uncurryE`, `mp_replE`, `cubeM_inter_eq_mul_of_detOnE`, …). -/
theorem rowsOutM_glue_eq_cubeM (F : Finset (State N)) (f : F → Fin N → ℝ) (X : Set (Param N)) :
    rowsOutM F {g | glueRows F f g ∈ X} = cubeM N {w | glueRows F f (restrOut F w) ∈ X} :=
  (cubeM_restrOut_preimage F _).symm

/-! ## 3. The K-free fresh event (W5 §4, W9 §5.1, W13 G5) -/

/-- FE0: the fresh entries are in `(0,1)` (the complement is null; W13-effect G5). -/
def FE0X (N : ℕ) (s r0 : State N) (w : Param N) : Prop :=
  ∀ r, r ∉ sensRows s r0 → ∀ i, w r i ∈ Set.Ioo (0 : ℝ) 1

/-- FE1: fresh part of every subcube sum of dimension `≥ D0` (Hoeffding scale `2 √(N 2^D)`). -/
def FE1X (N : ℕ) (s r0 : State N) (w : Param N) : Prop :=
  ∀ (t : State N) (A : Finset (Fin N)), A.card + D0C N ≤ N → ∀ i,
    |∑ r ∈ (agree A t).filter (fun r => r ∉ sensRows s r0), (clamp01 (w r i) - 1 / 2)| ≤
      2 * Real.sqrt ((N : ℝ) * 2 ^ (N - A.card))

/-- FE2: row excess `≤ N/5` for fresh rows within distance `J` of `Sens`. -/
def FE2X (N : ℕ) (s r0 : State N) (w : Param N) : Prop :=
  ∀ r, r ∉ sensRows s r0 → (∃ r' ∈ sensRows s r0, ham r r' ≤ JC N) →
    ∑ i, pos (clamp01 (w r i) - b1Cap) ≤ (N : ℝ) / 5

/-- FE3: Cramér level `23/50` for fresh subcubes of dimension `1 … J`. -/
def FE3X (N : ℕ) (s r0 : State N) (w : Param N) : Prop :=
  ∀ (t : State N) (A : Finset (Fin N)), N ≤ A.card + JC N → A.card < N →
    (∀ r ∈ agree A t, r ∉ sensRows s r0) →
    ∑ i, Real.log (max (2 * subMean w A t i) 1) ≤ 23 / 50 * (N : ℝ)

/-- FE4(a): the fresh row products sum to `≤ 2`. -/
def FE4aX (N : ℕ) (s r0 : State N) (w : Param N) : Prop :=
  ∑ r ∈ freshRows s r0, Pw w r ≤ 2

/-- FE4(b): the fresh `M`-row products sum to `≤ 2^{d+1}`, every `|K| = dX` (W13 G5). -/
def FE4bX (N : ℕ) (s r0 : State N) (w : Param N) : Prop :=
  ∀ K : Finset (Fin N), K.card = dX N →
    ∑ r ∈ freshRows s r0, ∏ i ∈ univ \ K, clamp01 (w r i) ≤ 2 ^ (dX N + 1)

/-- FE5: near-full normalisers, `avg_z ∏_{i ∈ M} Ā_i(agree Z z) ≥ 2^{-(m+2)}`. -/
def FE5X (N : ℕ) (_s _r0 : State N) (w : Param N) : Prop :=
  ∀ K : Finset (Fin N), K.card = dX N → ∀ Z : Finset (Fin N), N ≤ Z.card + JC N → Z.card < N →
    1 / (2 : ℝ) ^ (N - dX N + 2) ≤ (∑ z : State N, ∏ i ∈ univ \ K, subMean w Z z i) / 2 ^ N

/-- FE6: no heavy fresh row (threshold from the tilt of `CellEvX`, W13 G5). -/
def FE6X (N : ℕ) (s r0 : State N) (w : Param N) : Prop :=
  ∀ r, r ∉ sensRows s r0 → x0 * N + slT N + b1Eta * N < XW w r

/-- FE7(a): the fresh effect mass at every `t` is `≥ 1 - 2N⁴2^{-N} - 2√N σ_N`. -/
def FE7aX (N : ℕ) (s r0 : State N) (w : Param N) : Prop :=
  ∀ t : State N, 1 - 2 * (N : ℝ) ^ 4 / 2 ^ N - 2 * Real.sqrt N * sigN N ≤
    ∑ r ∈ freshRows s r0, rowTX w s r t

/-- FE7(b)': the fresh effect mass at `te` is `≤ 1 + e^{N/100} σ_N` (W9 5.1). -/
def FE7bX (N : ℕ) (s r0 : State N) (w : Param N) : Prop :=
  ∑ r ∈ freshRows s r0, rowTX w s r (teW w s) ≤ 1 + Real.exp ((N : ℝ) / 100) * sigN N

/-- **`CountFreshX`** = FE0 ∧ … ∧ FE7(b)' (W5 §4, W9 §5.1, W13 G5). -/
structure CountFreshX (N : ℕ) (s r0 : State N) (w : Param N) : Prop where
  fe0 : FE0X N s r0 w
  fe1 : FE1X N s r0 w
  fe2 : FE2X N s r0 w
  fe3 : FE3X N s r0 w
  fe4a : FE4aX N s r0 w
  fe4b : FE4bX N s r0 w
  fe5 : FE5X N s r0 w
  fe6 : FE6X N s r0 w
  fe7a : FE7aX N s r0 w
  fe7b : FE7bX N s r0 w

/-! ## 4. The per-K events (W5 §§5.1, 6.2, W9 §5.5) -/

/-- **Retention** (profile-free, W5 5.1 / W13 G5): every fresh row is lighter on `M = U \ K` than the
level `x0 N + slT + 1 ≥ X(r0) + 1`. -/
def RetK (N : ℕ) (s r0 : State N) (K : Finset (Fin N)) (w : Param N) : Prop :=
  ∀ r, r ∉ sensRows s r0 → x0 * N + slT N + 1 < XMW w (univ \ K) r

/-- The conditions (L), (S), (N) of `Core_K(κ)` at the unit `k` (W5 6.2). -/
def CoreAt (N : ℕ) (s : State N) (K : Finset (Fin N)) (k : Fin N) (κ : ℝ) (w : Param N) : Prop :=
  A0C N + 2 * kapN N + κ < |fK w s K k| ∧ |fK w s K k| < x2C N - κ ∧
    (∀ k' : Fin N, k' ≠ k → |fK w s K k'| < A0C N + kapN N - κ) ∧
    ∀ j ∈ univ \ K, sgnMul (fK w s K k) (hK w s K j k) < (1 - 2 / mX N) * |fK w s K k| - kapN N - κ

/-- `Core_K(κ)`: some `k ∈ K` satisfies (L), (S), (N). -/
def CoreK (N : ℕ) (s : State N) (K : Finset (Fin N)) (κ : ℝ) (w : Param N) : Prop :=
  ∃ k ∈ K, CoreAt N s K k κ w

/-- `Sign_K = Core_K(0) ∩ {s_{k1} = +1}`. -/
def SignK (N : ℕ) (s : State N) (K : Finset (Fin N)) (w : Param N) : Prop :=
  ∃ k ∈ K, CoreAt N s K k 0 w ∧ 0 < fK w s K k

/-- `(D_A)` for every nonempty `A ⊆ M` with `2 ≤ r = |M \ A| ≤ r_D` (W5 6.2, W9 5.5). -/
def DleAt (N : ℕ) (s : State N) (K : Finset (Fin N)) (k : Fin N) (w : Param N) : Prop :=
  ∀ A : Finset (Fin N), A ⊆ univ \ K → A.Nonempty → 2 ≤ ((univ \ K) \ A).card →
    ((univ \ K) \ A).card ≤ rD N →
    sgnMul (fK w s K k) (effDevA w s A s k) <
      |fK w s K k| * (1 - (((univ \ K) \ A).card : ℝ) / mX N) - kapN N / 2

/-- **The counted indicator** `Y_K = 1[Sign_K ∩ D≤_K]` (W9 5.5). -/
def YK (N : ℕ) (s : State N) (K : Finset (Fin N)) (w : Param N) : Prop :=
  ∃ k ∈ K, CoreAt N s K k 0 w ∧ 0 < fK w s K k ∧ DleAt N s K k w

/-! ## 5. Counts and bad sets (W9 §3.1) -/

/-- `W = #{K ∈ famX3 : Y_K}`. -/
noncomputable def WCnt (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N) : ℕ :=
  ((famX3 N s r0 x σ w).filter fun K => YK N s K w).card

/-- `RF = #{K ∈ famX3 : ¬ Ret_K}`. -/
noncomputable def RFCnt (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N) : ℕ :=
  ((famX3 N s r0 x σ w).filter fun K => ¬ RetK N s r0 K w).card

/-- Too many non-retaining `K`. -/
def RetBad (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) : Set (Param N) :=
  {w | ((famX3 N s r0 x σ w).card : ℝ) * pY N / 4 < (RFCnt N s r0 x σ w : ℝ)}

/-- Too few counted indicators. -/
def WBad (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) : Set (Param N) :=
  {w | (WCnt N s r0 x σ w : ℝ) < ((famX3 N s r0 x σ w).card : ℝ) * pY N / 2}

/-- **`BadCountX`** (W9 3.1 with the constants of this file). -/
def BadCountX (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) : Set (Param N) :=
  {w | ¬ CountFreshX N s r0 w} ∪ RetBad N s r0 x σ ∪ WBad N s r0 x σ

/-! ## 6. `GoodX3` at the level of `Param N` -/

/-- The new fields `NewX3`, read on the true parameter (`x5e` only at `K' = {j}`: rows of `Ball(s, 2)`;
this is all the count uses, W13-effect G4). There is no pointwise floor: units outside `lowU` are above it,
and `lowU ⊆ K` for every counted `K` (`mem_famX3_floor`). -/
structure NewX3W (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N) : Prop where
  lowFew : 1000 * (lowU N w r0).card ≤ N
  pairLow : σ = .cause → ∃ j, j ≠ x ∧ 1 / 2 + Real.exp (-((N : ℝ) / 200)) ≤ clamp01 (w r0 j) ∧
      clamp01 (w r0 j) + clamp01 (w (flipAt x r0) j) ≤ 1 - 1 / (N : ℝ)
  x5e1 : σ = .effect → ∀ j, j ≠ x →
      ∑ i, Real.log (max (2 * b1CutMeanPlus w (flipAt x s) {j} i) 1) ≤ 23 / 50 * (N : ℝ)

/-- **`GoodW3`**: the hypotheses every deterministic lemma takes. -/
def GoodW3 (N : ℕ) (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N) : Prop :=
  B1FGoodX N s r0 x σ w ∧ NewX3W N s r0 x σ w

lemma mem_sensRows_r0 (s r0 : State N) : r0 ∈ sensRows s r0 :=
  Finset.mem_union_left _ (by simp [ballR, ham_self])

lemma mem_sensRows_s (s r0 : State N) : s ∈ sensRows s r0 :=
  Finset.mem_union_right _ (by simp [ballR, ham_self])

lemma mem_sensRows_flip_r0 (s r0 : State N) (x : Fin N) : flipAt x r0 ∈ sensRows s r0 := by
  refine Finset.mem_union_left _ ?_
  simp only [ballR, Finset.mem_filter, Finset.mem_univ, true_and]
  have := ham_flipAt_le_one x r0; rw [ham_comm] at this; omega

lemma agree_single_flip_s_subset (s r0 : State N) (x j : Fin N) :
    agree ({j} : Finset (Fin N))ᶜ (flipAt x s) ⊆ sensRows s r0 := by
  refine Finset.Subset.trans ?_ Finset.subset_union_right
  exact agree_subset_ballR (d := 1) (ham_flipAt_le_one x s) (by simp) (by norm_num)

lemma glue_eq_b1Ext {s r0 : State N} (f : sensRows s r0 → Fin N → ℝ)
    (g : {r // r ∉ sensRows s r0} → Fin N → ℝ) :
    ∀ r ∈ sensRows s r0, glueRows (sensRows s r0) f g r = b1Ext f r := by
  intro r hr
  rw [glueRows_of_mem _ f g hr]
  simp [b1Ext, hr]

lemma lowU_congr {w w' : Param N} {r0 : State N} (h : w' r0 = w r0) : lowU N w' r0 = lowU N w r0 := by
  unfold lowU; rw [h]

/-- `famX3` reads rows `r0`, `r0^x` only: it is the same for `glue f g` and `b1Ext f`. -/
theorem famX3_glue {s r0 : State N} {x : Fin N} {σ : XSide} (f : sensRows s r0 → Fin N → ℝ)
    (g : {r // r ∉ sensRows s r0} → Fin N → ℝ) :
    famX3 N s r0 x σ (glueRows (sensRows s r0) f g) = famX3 N s r0 x σ (b1Ext f) := by
  have h := glue_eq_b1Ext f g
  have h0 := h r0 (mem_sensRows_r0 s r0)
  cases σ with
  | cause =>
    simp only [famX3]
    rw [NegX_congr h0 (h _ (mem_sensRows_flip_r0 s r0 x)), lowU_congr h0]
  | effect =>
    simp only [famX3]
    rw [lowU_congr h0]

lemma famX3_card {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N} {K : Finset (Fin N)}
    (hK : K ∈ famX3 N s r0 x σ w) : K.card = dX N := by
  cases σ <;> simp only [famX3, mem_filter, mem_powersetCard] at hK <;> exact hK.1.2

lemma lowU_sub_of_mem_famX3 {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    {K : Finset (Fin N)} (hK : K ∈ famX3 N s r0 x σ w) : lowU N w r0 ⊆ K := by
  cases σ <;> simp only [famX3, mem_filter] at hK <;> exact hK.2

/-- **The floor on `M = U \ K`**: every unit outside a counted `K` is not low. -/
theorem mem_famX3_floor {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    {K : Finset (Fin N)} (hK : K ∈ famX3 N s r0 x σ w) {j : Fin N} (hj : j ∉ K) :
    1 / 2 + Real.exp (-((N : ℝ) / 200)) ≤ clamp01 (w r0 j) := by
  by_contra hlt
  have hl : j ∈ lowU N w r0 := by
    simp only [lowU, mem_filter, mem_univ, true_and]
    exact not_le.1 hlt
  exact hj (lowU_sub_of_mem_famX3 hK hl)

lemma famX3_cause_sub {s r0 : State N} {x : Fin N} {w : Param N} {K : Finset (Fin N)}
    (hK : K ∈ famX3 N s r0 x .cause w) : K ⊆ NegX w r0 x ∪ lowU N w r0 := by
  simp only [famX3, mem_filter, mem_powersetCard] at hK
  exact hK.1.1

/-- **Transfer** `GoodX3 → GoodW3` for every gluing (proved). -/
theorem goodW3_glue {s r0 : State N} {x : Fin N} {σ : XSide} {f : sensRows s r0 → Fin N → ℝ}
    (hf : f ∈ GoodX3 N s r0 x σ) (g : {r // r ∉ sensRows s r0} → Fin N → ℝ) :
    GoodW3 N s r0 x σ (glueRows (sensRows s r0) f g) := by
  have h := glue_eq_b1Ext f g
  have h0 := h r0 (mem_sensRows_r0 s r0)
  have h1 := h _ (mem_sensRows_flip_r0 s r0 x)
  refine ⟨(B1FGoodX.congr h).1 hf.1, ?_, ?_, ?_⟩
  · rw [lowU_congr h0]; exact hf.2.lowFew
  · intro hσ
    obtain ⟨j, hj, hfl, hle⟩ := hf.2.pairLow hσ
    exact ⟨j, hj, by rw [h0]; exact hfl, by rw [h0, h1]; exact hle⟩
  · intro hσ j hj
    have hsub := agree_single_flip_s_subset s r0 x j
    have hm : ∀ i, b1CutMeanPlus (glueRows (sensRows s r0) f g) (flipAt x s) {j} i =
        b1CutMeanPlus (b1Ext f) (flipAt x s) {j} i :=
      fun i => b1CutMeanPlus_congr (fun r hr => h r (hsub hr)) i
    simp only [hm]
    exact hf.2.x5e hσ {j} (singleton_nonempty j) (by simp)
      (by rw [mem_singleton]; exact fun e => hj e.symm)

/-- On good data and the fresh event, every entry is in `(0,1)`. -/
theorem cnt_mem_openCube {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    (hg : GoodW3 N s r0 x σ w) (hfr : CountFreshX N s r0 w) : w ∈ openCube N := by
  intro r i
  by_cases hr : r ∈ sensRows s r0
  · exact hg.1.openRows r hr i
  · exact hfr.fe0 r hr i

/-- The tilt `X(r0) ≤ x0 N + slT` (from the regime cell). -/
theorem cnt_tilt {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    (hg : GoodW3 N s r0 x σ w) : XW w r0 ≤ x0 * N + slT N := by
  obtain ⟨c, -, hc⟩ := hg.1.regEv
  exact hc.2.2.1

/-! ## 7. Work-package interfaces

Each `…Stmt` below is the main statement of one work package of W14.  `B1CntGlue.lean` proves
`CountX3Stmt` from them.  Generic toolkit statements (WP1) are stated as `Prop`s too, so that the
packages using them can be written before WP1 is done. -/

/-- The DistOK lower bound on `φ_d`. -/
noncomputable def phiFloor (N : ℕ) : ℝ := 2 * (N : ℝ) * (2 : ℝ) ^ (-(N : ℤ))

/-- **WP2 main (Theorem CS / CS_X (ii)-(v)).** -/
def CauseDetStmt : Prop :=
  ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N),
    GoodW3 N s r0 x σ w → CountFreshX N s r0 w → ∀ K ∈ famX3 N s r0 x σ w, RetK N s r0 K w →
      maxCausePurviewsAt (tpmOf (flipP s w)) univ s (univ \ K) s = {(univ, r0)} ∧
      phiFloor N ≤ phiCmechAt (tpmOf (flipP s w)) univ s (univ \ K) s

/-- **WP2 (Theorem CS (i)): the system cause state.** -/
def SysCauseStmt : Prop :=
  ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N),
    GoodW3 N s r0 x σ w → CountFreshX N s r0 w →
      sysMaxCauseStates (tpmOf (flipP s w)) univ s s = {r0}

/-- **WP3 main (Lemma E3' + Glob from FE1 for `r > r_D`).** -/
def EffDetStmt : Prop :=
  ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N),
    GoodW3 N s r0 x σ w → CountFreshX N s r0 w → ∀ K ∈ famX3 N s r0 x σ w, YK N s K w →
      (∃ pe ∈ maxEffPurviewsAt (tpmOf (flipP s w)) univ s (univ \ K) s,
          stated pe.1 pe.2 ⊆ stated univ (teW w s)) ∧
      phiFloor N ≤ phiEmechAt (tpmOf (flipP s w)) univ s (univ \ K) s

/-- **WP3 (Lemma TE'): the system effect state.** -/
def SysEffStmt : Prop :=
  ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N),
    GoodW3 N s r0 x σ w → CountFreshX N s r0 w →
      sysMaxEffStates (tpmOf (flipP s w)) univ s s = {teW w s}

/-- **WP6 (family size, W9 4.2).** -/
def FamBigStmt : Prop :=
  ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N),
    GoodW3 N s r0 x σ w → (LCnt N : ℝ) ≤ ((famX3 N s r0 x σ w).card : ℝ) * pY N / 4

/-- **WP4 main: the fresh event fails with probability `≤ e^{-N/200}`** (assembled in
`B1CntGlue.freshProb_of_fields` from the ten `FreshFieldProb` statements). -/
def FreshProbStmt : Prop :=
  ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide), ∀ f ∈ GoodX3 N s r0 x σ,
    rowsOutM (sensRows s r0) {g | ¬ CountFreshX N s r0 (glueRows (sensRows s r0) f g)}
      ≤ ENNReal.ofReal (Real.exp (-((N : ℝ) / 200)))

/-- **WP4, one field**: the fresh event `P` fails with probability `≤ e^{-cN}`, for EVERY `f`. -/
def FreshFieldProb (P : ∀ N : ℕ, State N → State N → Param N → Prop) (c : ℝ) : Prop :=
  ∀ᶠ N in atTop, ∀ (s r0 : State N) (f : sensRows s r0 → Fin N → ℝ),
    rowsOutM (sensRows s r0) {g | ¬ P N s r0 (glueRows (sensRows s r0) f g)}
      ≤ ENNReal.ofReal (Real.exp (-(c * N)))

/-- **WP5 (retention C3a + Markov).** -/
def RetMarkovStmt : Prop :=
  ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide), ∀ f ∈ GoodX3 N s r0 x σ,
    rowsOutM (sensRows s r0) {g | glueRows (sensRows s r0) f g ∈ RetBad N s r0 x σ}
      ≤ ENNReal.ofReal (Real.exp (-((N : ℝ) / 40)))

/-- **WP5 main (E2' coin + E4'' sign + D'): the mean of a counted indicator.** -/
def MeanYStmt : Prop :=
  ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide), ∀ f ∈ GoodX3 N s r0 x σ,
    ∀ K ∈ famX3 N s r0 x σ (b1Ext f),
      ENNReal.ofReal (pY N) ≤
        rowsOutM (sensRows s r0) {g | YK N s K (glueRows (sensRows s r0) f g)}

/-- **WP6 main (SH', COV', near pairs, Chebyshev).** -/
def ChebStmt : Prop :=
  ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide), ∀ f ∈ GoodX3 N s r0 x σ,
    rowsOutM (sensRows s r0) {g | glueRows (sensRows s r0) f g ∈ WBad N s r0 x σ}
      ≤ ENNReal.ofReal (Real.exp (-((N : ℝ) / 450)))

/-! ### WP1 toolkit interfaces (generic, no IIT) -/

/-- **WP1a: sharp sub-Gaussian tail of centred uniforms** (from `sbM l ≤ exp (l²/24)`). -/
def SubGaussStmt : Prop :=
  ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
    (Measure.pi fun _ : Fin n => unif) {u | t ≤ ∑ l, (u l - 1 / 2)} ≤
      ENNReal.ofReal (Real.exp (-(6 * t ^ 2 / n)))

/-- **WP1b: one-dimensional Gaussian comparison** (W5 Lemma GC, from `Lindeberg.lean`). -/
def GCStmt : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ x : ℝ,
    |((Measure.pi fun _ : Fin n => unif) {u | ∑ l, (u l - 1 / 2) ≤ x * Real.sqrt ((n : ℝ) / 12)}).toReal
        - (ProbabilityTheory.gaussianReal 0 1 (Set.Iic x)).toReal| ≤ C * (n : ℝ) ^ (-(1 / 8 : ℝ))

/-- **WP1c: Mills-ratio bounds for the Gaussian tail.** -/
def MillsStmt : Prop :=
  ∀ z : ℝ, 0 < z →
    Real.exp (-(z ^ 2 / 2)) / Real.sqrt (2 * Real.pi) * (z / (1 + z ^ 2)) ≤
        (ProbabilityTheory.gaussianReal 0 1 (Set.Ioi z)).toReal ∧
      (ProbabilityTheory.gaussianReal 0 1 (Set.Ioi z)).toReal ≤
        Real.exp (-(z ^ 2 / 2)) / Real.sqrt (2 * Real.pi) / z

/-- **WP1d: law of a signed entry sum.** Under `cubeM`, a sum of `±(y - 1/2)` over a finite set `E` of
entries has the law of `∑_{l < |E|} (U_l - 1/2)` (entries iid uniform, `U ↦ 1 - U`, `clamp01 = id`
a.e.).  With `rowsOutM_glue_eq_cubeM` this transports every fresh-row sum. -/
def EntrySumLawStmt : Prop :=
  ∀ (N : ℕ) (E : Finset (State N × Fin N)) (ε : State N × Fin N → Bool) (S : Set ℝ),
    MeasurableSet S →
    cubeM N {w | ∑ e ∈ E, (if ε e then clamp01 (w e.1 e.2) - 1 / 2 else 1 / 2 - clamp01 (w e.1 e.2))
        ∈ S} =
      (Measure.pi fun _ : Fin E.card => unif) {u | ∑ l, (u l - 1 / 2) ∈ S}

end Census
end IIT
