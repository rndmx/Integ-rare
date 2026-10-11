/-
Census, B1 forced leaf 7, `NatLT3Hu` part (c) (light `s`), stage **Section**: the T7 conditioning/section argument
and its assembly for LIGHT `s` only, at the `ε = dnEps = 10⁻⁵` constants of `B1HuLGood` / `B1HuLMember`.

* `flr_numE5`, `flr_floorE5`: the floor `4/5 ≤ y_top(tc, dnEps)` from `Zs ≥ 1/2`, `Lσ_N ≤ β` (deterministic,
  `(4/5)^{(1-10⁻⁵)N} ≈ e^{-0.2218N}` against `(L/2) e^{-x0 N}`, `x0 < 0.2029`); `lt3WSel_of_floor_evE5`
  (`Sel = WF × Base` at `ε = dnEps`).
* `lt3T7GoodE5`, `lt3T7TmE5` (target: `s ∉ lt3H w` and no triple at the natural level), `lt3T7YE5` (measurable).
* **`lt3_T7_sectE5`**: a nonempty section of the conditioned event is `≤ e^{-2N}` (light members only:
  `lt3_light_member_evE5`, product `lt3_nosucc_prodE5`, `m ≥ N/(10^10 C)`, `m² ≤ 4|G|`).
* **`lt3HuLFl_final`**: `LT3HuLFlStmt L (1047/1000)` (with `Zs ≥ 1/2`), `L ≥ lt3LcE5`.
* **`lt3HuL_final`**: `LT3HuLStmt L (1046/1000)`: on `openCube ∩ {Lσ_N ≤ β, s ∉ lt3H w}`, no triple reaches the
  natural level `(1 - dnEps) levTrip y_top(dnEps) β`, except with probability `≤ e^{-1.046N}`.
-/
import IIT.Census.B1HuLMember

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {N : ℕ}

/-! ### The floor at `ε = dnEps` -/

lemma dnEps_eq : dnEps = 1 / 100000 := by unfold dnEps; norm_num

/-- **The numeric step at `ε = dnEps`**: for any `L > 0`, eventually `1 ≤ ⌈dnEps N⌉₊` and
`(4/5)^{N + 1 - ⌈dnEps N⌉₊} < (L/2) σ_N`. -/
lemma flr_numE5 {L : ℝ} (hL : 0 < L) : ∀ᶠ N : ℕ in atTop,
    1 ≤ ⌈dnEps * N⌉₊ ∧ ((4 : ℝ) / 5) ^ (N + 1 - ⌈dnEps * N⌉₊) < L * (1 / 2) * sigN N := by
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈200 * (Real.log 2 - Real.log L)⌉₊]
    with N h1 hNL
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast h1
  have hNL' : 200 * (Real.log 2 - Real.log L) ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNL)
  have hk1 : 1 ≤ ⌈dnEps * N⌉₊ :=
    Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (mul_pos (by rw [dnEps_eq]; norm_num) (by linarith))).ne'
  refine ⟨hk1, ?_⟩
  set k := ⌈dnEps * N⌉₊ with hk
  have hkr : (k : ℝ) < dnEps * N + 1 := Nat.ceil_lt_add_one (by rw [dnEps_eq]; positivity)
  rw [dnEps_eq] at hkr
  have hkN : k ≤ N + 1 := by
    have : (k : ℝ) < ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact (Nat.cast_lt.1 this).le
  have hmr : ((N + 1 - k : ℕ) : ℝ) = N + 1 - k := by rw [Nat.cast_sub hkN]; push_cast; ring
  have hm20 : 99999 / 100000 * (N : ℝ) ≤ ((N + 1 - k : ℕ) : ℝ) := by rw [hmr]; linarith
  have e1 : ((4 : ℝ) / 5) ^ (N + 1 - k) = Real.exp (((N + 1 - k : ℕ) : ℝ) * Real.log (4 / 5)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [e1, flr_sig_eq hL N]
  refine Real.exp_lt_exp.2 ?_
  have hl := flr_log_four_fifths
  have hl0 : Real.log (4 / 5) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have p1 : ((N + 1 - k : ℕ) : ℝ) * Real.log (4 / 5) ≤ 99999 / 100000 * (N : ℝ) * Real.log (4 / 5) :=
    mul_le_mul_of_nonpos_right hm20 hl0.le
  have p2 : 99999 / 100000 * (N : ℝ) * Real.log (4 / 5) ≤ 99999 / 100000 * (N : ℝ) * (-(8 / 25 * Real.log 2)) :=
    mul_le_mul_of_nonneg_left hl.le (by positivity)
  have hl2 := Real.log_two_gt_d9
  norm_num at hl2
  have p3 : 6931471803 / 10000000000 * (N : ℝ) ≤ Real.log 2 * N :=
    mul_le_mul_of_nonneg_right hl2.le (by positivity)
  have p4 : x0 * N ≤ 2029 / 10000 * N := mul_le_mul_of_nonneg_right x0_lt.le (by positivity)
  linarith

/-- **The floor at `ε = dnEps`, deterministic form**: for any `L > 0`, eventually, `Zs ≥ 1/2` and `Lσ_N ≤ β` force
`b1YTopR w tc dnEps ≥ 4/5`. -/
theorem flr_floorE5 {L : ℝ} (hL : 0 < L) : ∀ᶠ N : ℕ in atTop, ∀ w : Param N,
    1 / 2 ≤ Zs w → L * sigN N ≤ betaW w → 4 / 5 ≤ b1YTopR w (tcRow w) dnEps := by
  filter_upwards [flr_numE5 hL] with N hN w hZ hβ
  exact flr_of_beta hN.1 (by norm_num) (by norm_num) (by norm_num) hZ hβ hN.2

/-- **The selection is `WF × Base` on the floored band** (`ε = dnEps`, eventually, given `|WQ| ≥ 7`). -/
theorem lt3WSel_of_floor_evE5 {L : ℝ} (hL : 0 < L) : ∀ᶠ N : ℕ in atTop,
    ∀ (s : State N) (γ : ℝ) (n : ℕ) (w : Param N), 1 / 2 ≤ Zs w → L * sigN N ≤ betaW w →
      7 ≤ (lt3WQ s dnEps γ n w).card → lt3WSel s dnEps γ n w = lt3WF s dnEps γ n w ×ˢ lt3Base s w := by
  filter_upwards [flr_Pw_gt hL, flr_floorE5 hL] with N hP hF s γ n w hZ hβ h7
  exact lt3WSel_of_floor s dnEps γ n (hP w hZ hβ) h7 (lt3WQ_floor s dnEps γ n w (Or.inr (hF w hZ hβ)))

/-! ### The events -/

/-- The good event of T7 at the `ε = 10⁻⁵` constants. -/
def lt3T7GoodE5 (s : State N) (w : Param N) : Prop :=
  lt3WGood s dnEps lt3γE5 lt3nbE5 (N / 20) (N / 3000000) 14 (N * N / (10 ^ 21 * lt3CnE5 * lt3CnE5)) w ∧
  bdGood w ∧
  ¬ ((lt2Sp w).card < 12 ∧ 7 ≤ qM (lt3WQ s dnEps lt3γE5 lt3nbE5 w) ∧
      N ≤ lt3D0E5 * qM (lt3WQ s dnEps lt3γE5 lt3nbE5 w) ∧
      qM (lt3WQ s dnEps lt3γE5 lt3nbE5 w) * qM (lt3WQ s dnEps lt3γE5 lt3nbE5 w) <
        4 * (lt3Adv s dnEps lt3γE5 lt3nbE5 lt3κE5 w).card)

/-- The measurable target: light `s`, and no triple reaches the natural level, on `{Lσ_N ≤ β, Zs ≥ 1/2}`. -/
def lt3T7TmE5 (L : ℝ) (s : State N) : Set (Param N) :=
  {w | w ∈ openCube N ∧ L * sigN N ≤ betaW w ∧ 1 / 2 ≤ Zs w ∧ s ∉ lt3H w ∧
    ∀ S : Finset (Fin N), S.card = 3 →
      phi (flipP s w) s S < (1 - dnEps) * levTrip * yTopW w dnEps * betaW w}

/-- The conditioned event. -/
def lt3T7YE5 (L : ℝ) (s : State N) : Set (Param N) :=
  lt3T7TmE5 L s ∩ (toMeasurable (cubeM N) {w | ¬ lt3T7GoodE5 s w})ᶜ

lemma lt3_light_mset (s : State N) : MeasurableSet {w : Param N | s ∉ lt3H w} := by
  classical
  have h := fibM_comp (f := fun w : Param N => (lt2Sp w, tcRow w)) fibM_SpTc
    (fun d => decide (s ∉ insert d.2 d.1)) true
  convert h using 1
  ext w
  simp only [Set.mem_setOf_eq, decide_eq_true_eq]
  rfl

lemma lt3T7TmE5_mset (L : ℝ) (s : State N) : MeasurableSet (lt3T7TmE5 L s) := by
  classical
  have e : lt3T7TmE5 L s = openCube N ∩ ({w | L * sigN N ≤ betaW w} ∩ ({w | 1 / 2 ≤ Zs w} ∩
      ({w | s ∉ lt3H w} ∩
      ⋂ S : Finset (Fin N), {w | S.card = 3 →
        phi (flipP s w) s S < (1 - dnEps) * levTrip * yTopW w dnEps * betaW w}))) := by
    ext w
    simp only [lt3T7TmE5, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine b1_measurableSet_openCube.inter ((measurableSet_le measurable_const b1m_betaW).inter
    ((measurableSet_le measurable_const b1m_Zs).inter ((lt3_light_mset s).inter
      (MeasurableSet.iInter fun S => ?_))))
  by_cases h : S.card = 3
  · have e2 : {w : Param N | S.card = 3 →
        phi (flipP s w) s S < (1 - dnEps) * levTrip * yTopW w dnEps * betaW w} =
        {w | phi (flipP s w) s S < (1 - dnEps) * levTrip * yTopW w dnEps * betaW w} := by
      ext w
      simp only [Set.mem_setOf_eq]
      exact ⟨fun hw => hw h, fun hw _ => hw⟩
    rw [e2]
    exact measurableSet_lt (b1m_phi_flip s S) ((measurable_const.mul (b1m_yTopW dnEps)).mul b1m_betaW)
  · have e2 : {w : Param N | S.card = 3 →
        phi (flipP s w) s S < (1 - dnEps) * levTrip * yTopW w dnEps * betaW w} = Set.univ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro h1
      exact absurd h1 h
    rw [e2]
    exact MeasurableSet.univ

lemma lt3T7YE5_mset (L : ℝ) (s : State N) : MeasurableSet (lt3T7YE5 L s) :=
  (lt3T7TmE5_mset L s).inter (measurableSet_toMeasurable _ _).compl

lemma lt3T7YE5_good {L : ℝ} {s : State N} {w : Param N} (h : w ∈ lt3T7YE5 L s) : lt3T7GoodE5 s w := by
  by_contra hc
  exact h.2 (subset_toMeasurable _ _ hc)

/-! ### Numerics -/

/-- **The conditional product is `≤ e^{-2N}`**: `m ≥ N/K` (any `K > 0`), `m² ≤ 4g` give `2N ≤ p g`. -/
lemma lt3_prod_numK {p : ℝ} (hp : 0 < p) (K : ℕ) (hK0 : 0 < K) : ∀ᶠ N : ℕ in atTop, ∀ m g : ℕ, N / K ≤ m →
    m * m ≤ 4 * g → 2 * (N : ℝ) ≤ p * g := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  filter_upwards [eventually_ge_atTop (2 * K), eventually_ge_atTop ⌈32 * (K : ℝ) ^ 2 / p⌉₊] with N h1 h2 m g hm hg
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1r : 2 * (K : ℝ) ≤ N := by exact_mod_cast h1
  have h2r : 32 * (K : ℝ) ^ 2 / p ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast h2)
  have hlt := Nat.lt_div_mul_add (a := N) hK0
  have hlt' : (N : ℝ) < (N / K : ℕ) * K + K := by exact_mod_cast hlt
  have hmr : ((N / K : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
  have hq : (N : ℝ) ≤ 2 * K * m := by nlinarith
  have hgr : ((m : ℝ)) * m ≤ 4 * g := by exact_mod_cast hg
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hN2 : (N : ℝ) * N ≤ 16 * (K : ℝ) ^ 2 * g := by nlinarith
  have h32 : 32 * (K : ℝ) ^ 2 ≤ p * N := by
    rw [div_le_iff₀ hp] at h2r; linarith
  by_cases hNz : (N : ℝ) = 0
  · rw [hNz]; have : (0 : ℝ) ≤ p * g := by positivity
    linarith
  · have hNpos : 0 < (N : ℝ) := lt_of_le_of_ne hN0 (Ne.symm hNz)
    have hK2 : 0 < (K : ℝ) ^ 2 := by positivity
    have key : 2 * (N : ℝ) * (16 * (K : ℝ) ^ 2) ≤ p * g * (16 * (K : ℝ) ^ 2) := by
      have e1 : 2 * (N : ℝ) * (16 * (K : ℝ) ^ 2) = N * (32 * (K : ℝ) ^ 2) := by ring
      have e2 : (N : ℝ) * (32 * (K : ℝ) ^ 2) ≤ N * (p * N) := mul_le_mul_of_nonneg_left h32 hN0
      have e3 : (N : ℝ) * (p * N) ≤ p * (16 * (K : ℝ) ^ 2 * g) := by
        have := mul_le_mul_of_nonneg_left hN2 hp.le
        nlinarith
      nlinarith
    exact le_of_mul_le_mul_right key (by positivity)

/-- `lt3_prod_numK` at `K = 10^10 C`. -/
lemma lt3_prod_numE5 {p : ℝ} (hp : 0 < p) : ∀ᶠ N : ℕ in atTop, ∀ m g : ℕ, N / (10 ^ 10 * lt3CnE5) ≤ m →
    m * m ≤ 4 * g → 2 * (N : ℝ) ≤ p * g :=
  lt3_prod_numK hp _ (by have := lt3CnE5_pos; positivity)

/-- `e^{-2N} + (2e^{-1.05N} + e^{-1.2N} + e^{-2N}) ≤ e^{-1.047N}` for `N` large. -/
lemma lt3_rate_numE5 : ∀ᶠ N : ℕ in atTop, Real.exp (-(2 * (N : ℝ))) +
    (2 * Real.exp (-((105 / 100 : ℝ) * N)) + Real.exp (-(6 / 5 * (N : ℝ))) + Real.exp (-(2 * (N : ℝ)))) ≤
      Real.exp (-(1047 / 1000 * (N : ℝ))) := by
  filter_upwards [lt3_rate_num] with N h
  have : 0 ≤ 2 * Real.exp (-((11 / 10 : ℝ) * N)) := by positivity
  linarith

/-! ### One section -/

/-- **A nonempty section of the conditioned event is `≤ e^{-2N}`** (`N` large, uniformly in `s`; light `s` only). -/
theorem lt3_T7_sectE5 {L : ℝ} (hL : lt3LcE5 ≤ L) : ∀ᶠ N : ℕ in atTop,
    ∀ (s : State N) (w0 : Param N), w0 ∈ lt3T7YE5 L s →
    cubeM N {η | replE (stPriv (lt3WSel s dnEps lt3γE5 lt3nbE5) lt3PB w0) w0 η ∈ lt3T7YE5 L s} ≤
      ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
  have hL0 : 0 < L := lt3LcE5_pos.trans_le hL
  filter_upwards [lt3_light_member_evE5 hL, lt3WSel_of_floor_evE5 hL0, eventually_ge_atTop (10 ^ 12 * lt3CnE5),
    eventually_ge_atTop (7 * (10 ^ 10 * lt3CnE5)), lt3_prod_numE5 lt3pLE5_pos] with N hLN hSelF hN12 hN7 hnum
  intro s w0 hw0
  classical
  have hgood := lt3T7YE5_good hw0
  obtain ⟨⟨hcube, hβ, hZ, hsH, -⟩, -⟩ := hw0
  obtain ⟨hWG, hbd, hnadv⟩ := hgood
  obtain ⟨hm, h7, hm2⟩ := lt3W_good_F_lightE5 s hsH hN12 hWG
  have hSp : (lt2Sp w0).card < 12 := hWG.1.2.2.2.1
  have hSel := hSelF s lt3γE5 lt3nbE5 w0 hZ hβ h7
  set m := qM (lt3WQ s dnEps lt3γE5 lt3nbE5 w0) with hmdef
  obtain ⟨hm7, hND⟩ := lt3_ND0E5 hN7 hm
  have hAdv : 4 * (lt3Adv s dnEps lt3γE5 lt3nbE5 lt3κE5 w0).card ≤ m * m := by
    by_contra hc
    exact hnadv ⟨hSp, hm7, hND, not_le.1 hc⟩
  set G := lt3WF s dnEps lt3γE5 lt3nbE5 w0 \ lt3Adv s dnEps lt3γE5 lt3nbE5 lt3κE5 w0 with hGdef
  have hGc : m * m ≤ 4 * G.card := by
    have h1 : (lt3WF s dnEps lt3γE5 lt3nbE5 w0).card - (lt3Adv s dnEps lt3γE5 lt3nbE5 lt3κE5 w0).card ≤
        G.card := Finset.le_card_sdiff _ _
    have h2 : m * m ≤ 2 * (lt3WF s dnEps lt3γE5 lt3nbE5 w0).card := hm2
    omega
  have hsB : s ∈ lt3Base s w0 := mem_insert_of_mem (mem_insert_self _ _)
  have hGk : ∀ S ∈ G, (S, s) ∈ lt3WSel s dnEps lt3γE5 lt3nbE5 w0 := fun S hS => by
    rw [hSel]; exact mem_product.2 ⟨(mem_sdiff.1 hS).1, hsB⟩
  have hOK : ∀ S ∈ G, LT3MemberOKE5 L lt3pLE5 s w0 S := fun S hS =>
    hLN s w0 S hcube hSp (hGk S hS) (mem_sdiff.1 hS).2 hsH
  have hsub : {η | replE (stPriv (lt3WSel s dnEps lt3γE5 lt3nbE5) lt3PB w0) w0 η ∈ lt3T7YE5 L s} ⊆
      {η | ∀ S ∈ G, ¬ LT3ConclE5 L s (replE (stPriv (lt3WSel s dnEps lt3γE5 lt3nbE5) lt3PB w0) w0 η) S} := by
    intro η hη S hS hconc
    have hg' := lt3T7YE5_good hη
    obtain ⟨⟨hc', hβ', hZ', -, hφ'⟩, -⟩ := hη
    obtain ⟨a, b, c, hab, hac, hbc, hS3⟩ := lt3WSel_three (hGk S hS)
    have hS3' : S = {a, b, c} := hS3
    have hcard : S.card = 3 := by
      rw [hS3', card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]
    have h1 := hconc hc' hZ' hβ' hg'.2.1 hg'.1.1.2.2.2.1
    have h2 := hφ' S hcard
    linarith
  refine (measure_mono hsub).trans ((lt3_nosucc_prodE5 lt3pLE5_pos.le lt3pLE5_le s w0 G hGk hOK).trans ?_)
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have := hnum m G.card hm hGc
  linarith

/-! ### The assembly -/

/-- **The light LT3 band at the natural level, with `Zs ≥ 1/2`.** -/
def LT3HuLFlStmt (L C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (openCube N ∩ {w | L * sigN N ≤ betaW w ∧ 1 / 2 ≤ Zs w ∧ s ∉ lt3H w ∧
      ∀ S : Finset (Fin N), S.card = 3 →
        phi (flipP s w) s S < (1 - dnEps) * levTrip * yTopW w dnEps * betaW w}) ≤
      ENNReal.ofReal (Real.exp (-(C * N)))

/-- **The light LT3 band at the natural level**: only `Lσ_N ≤ β` (and the open cube) is assumed. -/
def LT3HuLStmt (L C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ s : State N,
    cubeM N (openCube N ∩ {w | L * sigN N ≤ betaW w ∧ s ∉ lt3H w ∧
      ∀ S : Finset (Fin N), S.card = 3 →
        phi (flipP s w) s S < (1 - dnEps) * levTrip * yTopW w dnEps * betaW w}) ≤
      ENNReal.ofReal (Real.exp (-(C * N)))

/-- **The floored light band** (`L ≥ lt3LcE5`), rate `1.047`. -/
theorem lt3HuLFl_final {L : ℝ} (hL : lt3LcE5 ≤ L) : LT3HuLFlStmt L (1047 / 1000) := by
  unfold LT3HuLFlStmt
  refine ev_forall_state (P := fun N s => cubeM N (openCube N ∩ {w | L * sigN N ≤ betaW w ∧ 1 / 2 ≤ Zs w ∧
      s ∉ lt3H w ∧ ∀ S : Finset (Fin N), S.card = 3 →
        phi (flipP s w) s S < (1 - dnEps) * levTrip * yTopW w dnEps * betaW w}) ≤
      ENNReal.ofReal (Real.exp (-(1047 / 1000 * (N : ℝ))))) fun sq => ?_
  have hD1 : 1 ≤ 10 ^ 21 * lt3CnE5 * lt3CnE5 := Nat.succ_le_of_lt (by have := lt3CnE5_pos; positivity)
  filter_upwards [lt3_T7_sectE5 hL, lt3W_not_good_ev2E5 sq dnEps lt3nbE5 hD1, bd_not_good_ev,
    lt3_adv_evE5, lt3_rate_numE5] with N hsect hWG hbd hadv hrate
  set s := sq N with hs
  have : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  -- the conditioned event
  have hY : cubeM N (lt3T7YE5 L s) ≤ ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
    refine lt3W_cond_priv s dnEps lt3γE5 lt3nbE5 (lt3T7YE5_mset L s) fun A w hA => ?_
    by_cases hne : ∃ η0, replE A w η0 ∈ lt3T7YE5 L s
    · obtain ⟨η0, hη0⟩ := hne
      have hP0 : stPriv (lt3WSel s dnEps lt3γE5 lt3nbE5) lt3PB (replE A w η0) = A :=
        ((lt3WPriv_detOn (s := s) (ε := dnEps) (γ := lt3γE5) (n := lt3nbE5) A).replE_out w η0).2 hA
      have e : {η | replE A w η ∈ lt3T7YE5 L s} =
          {η | replE (stPriv (lt3WSel s dnEps lt3γE5 lt3nbE5) lt3PB (replE A w η0)) (replE A w η0) η ∈
            lt3T7YE5 L s} := by
        ext η
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hP0, replE_replE]
      rw [e]
      exact hsect s _ hη0
    · push Not at hne
      have e : {η | replE A w η ∈ lt3T7YE5 L s} = ∅ := by
        ext η
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact hne η
      rw [e, measure_empty]
      exact zero_le
  -- the bad event
  have hbad : {w | ¬ lt3T7GoodE5 s w} ⊆
      ({w | ¬ lt3WGood s dnEps lt3γE5 lt3nbE5 (N / 20) (N / 3000000) 14
          (N * N / (10 ^ 21 * lt3CnE5 * lt3CnE5)) w} ∪ {w | ¬ bdGood w}) ∪
      {w | (lt2Sp w).card < 12 ∧ 7 ≤ qM (lt3WQ s dnEps lt3γE5 lt3nbE5 w) ∧
        N ≤ lt3D0E5 * qM (lt3WQ s dnEps lt3γE5 lt3nbE5 w) ∧
        qM (lt3WQ s dnEps lt3γE5 lt3nbE5 w) * qM (lt3WQ s dnEps lt3γE5 lt3nbE5 w) <
          4 * (lt3Adv s dnEps lt3γE5 lt3nbE5 lt3κE5 w).card} := by
    intro w hw
    by_cases h1 : lt3WGood s dnEps lt3γE5 lt3nbE5 (N / 20) (N / 3000000) 14
        (N * N / (10 ^ 21 * lt3CnE5 * lt3CnE5)) w
    · by_cases h2 : bdGood w
      · exact Or.inr (not_not.1 fun h3 => hw ⟨h1, h2, h3⟩)
      · exact Or.inl (Or.inr h2)
    · exact Or.inl (Or.inl h1)
  have hbadM : cubeM N {w | ¬ lt3T7GoodE5 s w} ≤ ENNReal.ofReal (2 * Real.exp (-((105 / 100 : ℝ) * N)) +
      Real.exp (-(6 / 5 * (N : ℝ))) + Real.exp (-(2 * (N : ℝ)))) := by
    refine (measure_mono hbad).trans ((measure_union_le _ _).trans ?_)
    refine (add_le_add ((measure_union_le _ _).trans (add_le_add hWG hbd))
      (hadv s dnEps lt3γE5 lt3nbE5)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  -- the target
  have hT : openCube N ∩ {w | L * sigN N ≤ betaW w ∧ 1 / 2 ≤ Zs w ∧ s ∉ lt3H w ∧
      ∀ S : Finset (Fin N), S.card = 3 →
        phi (flipP s w) s S < (1 - dnEps) * levTrip * yTopW w dnEps * betaW w} ⊆
      lt3T7YE5 L s ∪ toMeasurable (cubeM N) {w | ¬ lt3T7GoodE5 s w} := by
    rintro w ⟨hc, hβ, hZ, hsH, hall⟩
    by_cases h : w ∈ toMeasurable (cubeM N) {w | ¬ lt3T7GoodE5 s w}
    · exact Or.inr h
    · exact Or.inl ⟨⟨hc, hβ, hZ, hsH, hall⟩, h⟩
  refine (measure_mono hT).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add hY ((le_of_eq (measure_toMeasurable _)).trans hbadM)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hrate

/-- **`Zs ≥ 1/2` may be assumed**: `LT3HuLFlStmt L C₁ → LT3HuLStmt L C` (`C < C₁`, `C < 1.4`). -/
theorem lt3HuL_of_floor {L C C₁ : ℝ} (h1 : C < C₁) (h2 : C < 14 / 10) (hFl : LT3HuLFlStmt L C₁) :
    LT3HuLStmt L C := by
  filter_upwards [hFl, flr_Zs_low, g_union_rate h1 h2] with N hA hB hU s
  refine (measure_mono ?_).trans (hU _ _ (hA s) hB)
  rintro w ⟨hcube, hβ, hsH, hall⟩
  by_cases hZ : 1 / 2 ≤ Zs w
  · exact Or.inl ⟨hcube, hβ, hZ, hsH, hall⟩
  · exact Or.inr (not_le.1 hZ).le

/-- **The light LT3 band at the natural level** (`L ≥ lt3LcE5`), rate `1.046`. -/
theorem lt3HuL_final {L : ℝ} (hL : lt3LcE5 ≤ L) : LT3HuLStmt L (1046 / 1000) :=
  lt3HuL_of_floor (by norm_num) (by norm_num) (lt3HuLFl_final hL)

end Census
end IIT
