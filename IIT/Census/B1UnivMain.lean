/-
Census, B1 lower bound, leaf `phi_univ_ge_EX` of `B1LowerB` (W7 §3 items 2, 3, 5).

`phi_univ_ge_EX_univ` has the SAME conclusion as `B1LowerB.phi_univ_ge_EX`, with `RestGood` replaced by
`RestGood ∧ UnivGood`.  `UnivGood N s r0 x w` collects the extra conditions; all of them are statements
about the GENERIC rows (rows outside `rowsA s r0 x`) given the fixed rows:
* `low`    : every effect pattern `t` gets generic mass `Σ_{r ∉ A} p(r → t) ≥ 1/2`
             (gives `Z ≥ 1/2` at `t = s`, and Lemma TE's lower bound on `R(t)`);
* `upTe`   : the generic mass of `te = teW w s` is `≤ 3/2` (Lemma TE's upper bound on `R(te)`);
* `concC`, `concE` : subcube concentration `|A_j(C) - 1/2| ≤ dU N |C|` for `|C| ≥ DU N`, both sides;
* `smallC`, `smallE` : the truncated small-cut sums `> 8 DU N` for `1 ≤ |K| < DU N`
             (cause side `K ≠ {x}`, effect side all `K`).
Parameters: `DU N = 4 log₂ N + 20`, `dsU N = 2 DU N + 40`, `dU N d = N · 2^{-⌊d/2⌋}`.
-/
import IIT.Census.B1UnivDet
import IIT.Census.B1UnivTE

namespace IIT
namespace Census

open Finset Filter Topology

variable {N : ℕ}

/-! ### Parameters -/

/-- Small-cut threshold `D = 4 log₂ N + 20`. -/
def DU (N : ℕ) : ℕ := 4 * Nat.log 2 N + 20

/-- `d* = 2 D + 40`. -/
def dsU (N : ℕ) : ℕ := 2 * DU N + 40

/-- Subcube deviation bound `δ_d = N · 2^{-⌊d/2⌋}`. -/
noncomputable def dU (N d : ℕ) : ℝ := N * (1 / 2 : ℝ) ^ (d / 2)

lemma dU_nonneg (N d : ℕ) : 0 ≤ dU N d := by unfold dU; positivity

lemma dU_anti (N : ℕ) {d d' : ℕ} (h : d ≤ d') : dU N d' ≤ dU N d := by
  unfold dU
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.div_le_div_right h)

/-! ### The extra good event -/

/-- **The extra conditions** (generic rows, given the fixed rows `rowsA s r0 x`). -/
structure UnivGood (N : ℕ) (s r0 : State N) (x : Fin N) (w : Param N) : Prop where
  low : ∀ t : State N, 1 / 2 ≤ ∑ r ∈ (rowsA s r0 x)ᶜ, fullProb (tpmOf (flipP s w)) r t
  upTe : ∑ r ∈ (rowsA s r0 x)ᶜ, fullProb (tpmOf (flipP s w)) r (teW w s) ≤ 3 / 2
  concC : ∀ j C, j ∉ C → DU N ≤ C.card → |cmean w (univ \ C) r0 j - 1 / 2| ≤ dU N C.card
  concE : ∀ j C, j ∉ C → DU N ≤ C.card →
    |effUnit (tpmOf (flipP s w)) Cᶜ s j (teW w s j) - 1 / 2| ≤ dU N C.card
  smallC : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N → K ≠ {x} →
    8 * (DU N : ℝ) < ∑ j ∈ Kᶜ, min (Real.logb 2 (clamp01 (w r0 j) / cmean w (univ \ K) r0 j))
      (cpx (fun j => clamp01 (w r0 j)) (rowMinU fun j => clamp01 (w r0 j)) (dU N (N - 1)) j)
  smallE : ∀ K : Finset (Fin N), 1 ≤ K.card → K.card < DU N →
    8 * (DU N : ℝ) < ∑ j ∈ Kᶜ,
      min (Real.logb 2 (xE w s j / effUnit (tpmOf (flipP s w)) Kᶜ s j (teW w s j)))
        (cpx (xE w s) (rowMinU (xE w s)) (dU N (N - 1)) j)

/-! ### Deterministic consequences of `low` / `upTe` -/

lemma rowsA_mem_r0 {s r0 : State N} {x : Fin N} : r0 ∈ rowsA s r0 x := by simp [rowsA]
lemma rowsA_mem_flip {s r0 : State N} {x : Fin N} : flipAt x r0 ∈ rowsA s r0 x := by simp [rowsA]
lemma rowsA_mem_s {s r0 : State N} {x : Fin N} : s ∈ rowsA s r0 x := by simp [rowsA]

/-- `Z ≥ 1/2`. -/
lemma Zs_ge_of_low {s r0 : State N} {x : Fin N} {w : Param N}
    (hlow : ∀ t : State N, 1 / 2 ≤ ∑ r ∈ (rowsA s r0 x)ᶜ, fullProb (tpmOf (flipP s w)) r t) :
    1 / 2 ≤ Zs w := by
  have h := hlow s
  have e : ∀ r, fullProb (tpmOf (flipP s w)) r s = Pw w r := fun r => by
    rw [← flipP_invol s w, ← rowProd_eq_Pw, flipP_invol s w]; rfl
  simp_rw [e] at h
  refine h.trans ?_
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ => Pw_nonneg w r

/-- **Item 5: `te = teW w s` is a maximal effect state of `univ`.** -/
theorem teW_mem_of_good {s r0 : State N} {x : Fin N} {w : Param N} (hw : w ∈ openCube N)
    (hNbig : (10 : ℝ) ^ 7 ≤ N) (h0 : r0 ≠ s) (h1 : flipAt x r0 ≠ s)
    (hy : ∀ j, (1001 / 2000 : ℝ) ≤ clamp01 (w r0 j))
    (hxs : ∀ k, (1 / 2 + 1 / 100000 : ℝ) ≤ xE w s k)
    (hk : ∃ k, w s k < 1 / 2)
    (hT : XW w r0 ≤ x0 * N)
    (hL : ∑ k, -Real.log (xE w s k) ≤ XW w r0 - 3 * Real.log N)
    (hlow : ∀ t : State N, 1 / 2 ≤ ∑ r ∈ (rowsA s r0 x)ᶜ, fullProb (tpmOf (flipP s w)) r t)
    (hup : ∑ r ∈ (rowsA s r0 x)ᶜ, fullProb (tpmOf (flipP s w)) r (teW w s) ≤ 3 / 2) :
    teW w s ∈ sysMaxEffStates (tpmOf (flipP s w)) univ s s := by
  set z := flipP s w with hzdef
  have hz : z ∈ openCube N := flipP_mem_openCube hw
  have hzw : flipP s z = w := flipP_invol s w
  set T := tpmOf z
  set te := teW w s
  have hte' : teW (flipP s z) s = te := by rw [hzw]
  have hpos : ∀ i r b, 0 < T.prob i r b := fun i r b => prob_pos hz i r b
  set A := rowsA s r0 x
  have hnn : ∀ r t, 0 ≤ fullProb T r t := fun r t => fullProb_nonneg T r t
  -- `R(t) ≥` generic mass
  have hRt : ∀ t, 1 / 2 ≤ effRest T s t := by
    intro t
    refine (hlow t).trans (sum_le_sum_of_subset_of_nonneg ?_ fun r _ _ => hnn r t)
    intro r hr
    exact mem_erase.2 ⟨fun e => (mem_compl.1 hr) (e ▸ rowsA_mem_s), mem_univ r⟩
  -- the fixed row `r0` gives at most `1/2` to `te`
  have hr0 : fullProb T r0 te ≤ 1 / 2 := by
    obtain ⟨k, hk⟩ := hk
    have hfac : ∀ j, T.prob j r0 (te j) = pTe w s r0 j := fun j => by
      have := prob_teW_row z s r0 j; rw [hte', hzw] at this; exact this
    have hcs : clamp01 (w s k) = w s k := by
      have h := hw s k; unfold clamp01; rw [min_eq_right h.2.le, max_eq_right h.1.le]
    have hkv : pTe w s r0 k ≤ 1 / 2 := by
      unfold pTe
      rw [if_neg (by rw [hcs]; linarith)]
      linarith [hy k]
    unfold fullProb
    rw [← mul_prod_erase univ _ (mem_univ k)]
    have hrest : ∏ j ∈ univ.erase k, T.prob j r0 (te j) ≤ 1 :=
      prod_le_one (fun j _ => T.nonneg j r0 _) fun j _ => T.le_one j r0 _
    rw [hfac k]
    have : 0 ≤ pTe w s r0 k := by rw [← hfac k]; exact T.nonneg k r0 _
    nlinarith [prod_nonneg fun j (_ : j ∈ univ.erase k) => T.nonneg j r0 (te j)]
  have hr1 : fullProb T (flipAt x r0) te ≤ 1 := fullProb_le_one T _ _
  have hRte : effRest T s te ≤ 3 := by
    unfold effRest
    have hsub : univ.erase s ⊆ Aᶜ ∪ {r0, flipAt x r0} := by
      intro r hr
      by_cases hA : r ∈ A
      · have : r = r0 ∨ r = flipAt x r0 ∨ r = s := by simpa [A, rowsA] using hA
        rcases this with h | h | h
        · exact mem_union_right _ (by simp [h])
        · exact mem_union_right _ (by simp [h])
        · exact absurd h (ne_of_mem_erase hr)
      · exact mem_union_left _ (mem_compl.2 hA)
    have hdisj : Disjoint Aᶜ ({r0, flipAt x r0} : Finset (State N)) := by
      rw [disjoint_left]
      intro r hr hr'
      have : r = r0 ∨ r = flipAt x r0 := by simpa using hr'
      rcases this with h | h
      · exact (mem_compl.1 hr) (h ▸ rowsA_mem_r0)
      · exact (mem_compl.1 hr) (h ▸ rowsA_mem_flip)
    calc ∑ r ∈ univ.erase s, fullProb T r te ≤ ∑ r ∈ Aᶜ ∪ {r0, flipAt x r0}, fullProb T r te :=
          sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => hnn r te
      _ = ∑ r ∈ Aᶜ, fullProb T r te + (fullProb T r0 te + fullProb T (flipAt x r0) te) := by
          rw [sum_union hdisj, sum_pair (flipAt_ne x r0).symm]
      _ ≤ 3 / 2 + (1 / 2 + 1) := by gcongr
      _ = 3 := by norm_num
  -- `e ≥ 2^{-N/2}`
  have hxE0 : ∀ k, 0 < xE w s k := fun k => xE_pos w s k
  have he : (2 : ℝ) ^ (-((N : ℝ) / 2)) ≤ fullProb T s te := by
    have hfe : fullProb T s te = eE w s := by
      rw [← sysEffProb_univ T s s te, ← hte', sysEffProb_univ_teW z s, hzw]
    rw [hfe]
    have h1 : eE w s = Real.exp (∑ k, Real.log (xE w s k)) := by
      rw [Real.exp_sum, eE]; exact prod_congr rfl fun k _ => (Real.exp_log (hxE0 k)).symm
    have h2 : (2 : ℝ) ^ (-((N : ℝ) / 2)) = Real.exp (-(Real.log 2 / 2 * N)) := by
      rw [Real.rpow_def_of_pos (by norm_num)]; congr 1; ring
    rw [h1, h2]
    apply Real.exp_le_exp.2
    have hsum : ∑ k, -Real.log (xE w s k) = -∑ k, Real.log (xE w s k) := sum_neg_distrib _
    have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have hx0 : x0 ≤ Real.log 2 / 2 := by
      unfold x0
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (3 / 2 : ℝ) ≤ 2)
      linarith
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [mul_le_mul_of_nonneg_right hx0 hN0]
  have hμν : 3 * (3 : ℝ) < 1 / 10 ^ 5 * ((N : ℝ) - 10) := by linarith
  have := sysMaxEffStates_univ_eq_of3 T s hpos te (μ := 1 / 10 ^ 5) (ν := 3) (by norm_num)
    (fun k => by
      have h := prob_teW z s k; rw [hte', hzw] at h; rw [h]; have := hxs k; linarith)
    he hRt hRte (fun t => by have := hRt t; linarith) (by norm_num) hμν
  rw [this]; exact mem_singleton_self _

/-! ### Item 1, strict form -/

/-- `r0` is the STRICT row-product maximiser on the good event (the proof of `tc_of_EX`). -/
theorem tc_strict_of_EX : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    ∀ w ∈ openCube N, w ∈ EX N s r0 x → EXFacts N s r0 x w → RestGood N s r0 x w →
      ∀ r, r ≠ r0 → Pw w r < Pw w r0 := by
  have hx0 := cr_x0_bounds
  have hx0hi : x0 ≤ 2027325541 / 10000000000 := by
    have := hx0.2; unfold crX0hi at this; push_cast at this; exact this
  have hev : ∀ᶠ N : ℕ in atTop, ((KS : ℝ) ^ 2 + 1) * Real.log 2 ≤
      N * (Real.log 2 / 2 - 2027325541 / 10000000000) := by
    have hl : (0 : ℝ) < Real.log 2 / 2 - 2027325541 / 10000000000 := by
      have := Real.log_two_gt_d9; linarith
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop
      (((KS : ℝ) ^ 2 + 1) * Real.log 2 / (Real.log 2 / 2 - 2027325541 / 10000000000))] with N hN
    rwa [div_le_iff₀ hl] at hN
  filter_upwards [hev, eventually_ge_atTop 6] with N hN hN6
  intro s r0 x hham w ho hw hF hR r hr
  have h0 : r0 ≠ s := fun h => by rw [h, ham_self] at hham; omega
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hT : XW w r0 ≤ x0 * N := by have := hF.T; linarith
  rw [Pw_eq_exp ho, Pw_eq_exp ho]
  by_cases hA : r ∈ rowsA s r0 x
  · simp only [rowsA, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with h | h | h
    · exact absurd h hr
    · rw [h]
      apply Real.exp_lt_exp.2
      have hD := hF.D
      rw [← XW_flip_sub ho] at hD
      have : (0 : ℝ) < N / 30 := by
        have : (6 : ℝ) ≤ N := by exact_mod_cast hN6
        linarith
      linarith
    · rw [h, ← Pw_eq_exp ho]
      refine lt_of_le_of_lt (Pw_s_le ho s) ?_
      have hL := EX_s_lower (s := s) (r0 := r0) (x := x) hw
      set c := (univ.filter fun k => w s k ∈ Set.Iio (1 / 2 : ℝ)).card
      have hpow : (1 / 2 : ℝ) ^ c = Real.exp (-(c * Real.log 2)) := by
        rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num), one_div, inv_pow]
      rw [hpow]
      apply Real.exp_lt_exp.2
      have hl2 := Real.log_two_gt_d9
      have hX : XW w r0 ≤ 2027325541 / 10000000000 * N := by
        have := mul_le_mul_of_nonneg_right hx0hi (Nat.cast_nonneg N); linarith
      nlinarith
  · apply Real.exp_lt_exp.2
    have h1 := hR.fe6 r hA
    have : (0 : ℝ) < 9 * Real.log N := by
      have : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
      have := Real.log_pos this; linarith
    have := hF.T
    linarith

/-! ### Numerics of the parameters -/

lemma two_pow_log_gt (N : ℕ) : (N : ℝ) < 2 * 2 ^ Nat.log 2 N := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  rw [pow_succ] at h
  have : (N : ℝ) < ((2 ^ Nat.log 2 N * 2 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at this; linarith

/-- `2^{⌊(4L+20)/2⌋} = 2^{2L+10}`. -/
lemma DU_half (N : ℕ) : DU N / 2 = 2 * Nat.log 2 N + 10 := by unfold DU; omega

lemma N_dU_DU (hN : 1 ≤ N) : (N : ℝ) * dU N (DU N) ≤ 1 / 100 := by
  unfold dU
  rw [DU_half]
  set L := Nat.log 2 N
  have h1 := two_pow_log_gt N
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (1 / 2 : ℝ) ^ (2 * L + 10) = 1 / (2 ^ 10 * (2 ^ L) ^ 2) := by
    rw [one_div_pow, ← pow_mul, ← pow_add]; congr 2; ring
  rw [hp]
  have hL0 : (0 : ℝ) < 2 ^ L := by positivity
  have hsq : (N : ℝ) ^ 2 < 4 * (2 ^ L) ^ 2 := by nlinarith
  rw [← mul_assoc, ← sq, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

lemma N_dU_far (hN : 1 ≤ N) {d : ℕ} (hd : dsU N ≤ d) : (N : ℝ) * dU N d ≤ 1 / (2 * 10 ^ 6) := by
  refine (mul_le_mul_of_nonneg_left (dU_anti N hd) (Nat.cast_nonneg _)).trans ?_
  unfold dU dsU DU
  have hdiv : (2 * (4 * Nat.log 2 N + 20) + 40) / 2 = 4 * Nat.log 2 N + 40 := by omega
  rw [hdiv]
  set L := Nat.log 2 N
  have h1 := two_pow_log_gt N
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (1 / 2 : ℝ) ^ (4 * L + 40) = 1 / (2 ^ 40 * ((2 ^ L) ^ 2) ^ 2) := by
    rw [one_div_pow, ← pow_mul, ← pow_mul, ← pow_add]; congr 2; ring
  rw [hp]
  have hL0 : (0 : ℝ) < 2 ^ L := by positivity
  have hsq : (N : ℝ) ^ 2 < 4 * (2 ^ L) ^ 2 := by nlinarith
  have hX : (1 : ℝ) ≤ (2 ^ L) ^ 2 := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hsq2 : (N : ℝ) ^ 2 * 1 ≤ ((2 ^ L) ^ 2) ^ 2 * 16 := by nlinarith
  rw [← mul_assoc, ← sq, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

lemma ev_N_dU_top : ∀ᶠ N : ℕ in atTop, (N : ℝ) * dU N (N - 1) ≤ 1 / (2 * 10 ^ 6) := by
  have hs1 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 2 hs1
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (8 * 10 ^ 6) by norm_num))
  filter_upwards [hev, eventually_ge_atTop 2] with N hN hN2
  unfold dU
  have hsq2 : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs : (Real.sqrt 2) ^ N ≤ 4 * 2 ^ ((N - 1) / 2) := by
    have h2 : (Real.sqrt 2) ^ N = Real.sqrt 2 ^ (N % 2) * 2 ^ (N / 2) := by
      conv_lhs => rw [← Nat.mod_add_div N 2, pow_add, pow_mul, Real.sq_sqrt (by norm_num)]
    have h3 : N / 2 ≤ (N - 1) / 2 + 1 := by omega
    have h4 : Real.sqrt 2 ^ (N % 2) ≤ 2 := by
      rcases Nat.mod_two_eq_zero_or_one N with h | h <;> rw [h]
      · norm_num
      · rw [pow_one]; exact hsq2
    rw [h2]
    calc Real.sqrt 2 ^ (N % 2) * 2 ^ (N / 2) ≤ 2 * 2 ^ ((N - 1) / 2 + 1) :=
          mul_le_mul h4 (pow_le_pow_right₀ (by norm_num) h3) (by positivity) (by norm_num)
      _ = 4 * 2 ^ ((N - 1) / 2) := by rw [pow_succ]; ring
  have hposs : (0 : ℝ) < Real.sqrt 2 ^ N := by positivity
  have hN' : (N : ℝ) ^ 2 < 1 / (8 * 10 ^ 6) * Real.sqrt 2 ^ N := by
    have := hN; rwa [div_lt_iff₀ hposs] at this
  have hp : (0 : ℝ) < 2 ^ ((N - 1) / 2) := by positivity
  rw [one_div_pow, ← mul_assoc, mul_one_div, div_le_div_iff₀ hp (by norm_num)]
  nlinarith


/-! ### The leaf -/

lemma four_mul_add_le_two_pow : ∀ L : ℕ, 6 ≤ L → 4 * L + 21 ≤ 2 ^ L := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

lemma DU_le (hN : 64 ≤ N) : DU N ≤ N - 1 := by
  unfold DU
  have h6 : 6 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have h1 := four_mul_add_le_two_pow _ h6
  have h2 := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
  omega

/-- **Leaf `phi_univ_ge_EX` with `RestGood` replaced by `RestGood ∧ UnivGood`.** -/
theorem phi_univ_ge_EX_univ : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N), N ≤ 3 * ham r0 s →
    ∀ w ∈ openCube N, w ∈ EX N s r0 x → EXFacts N s r0 x w →
      (RestGood N s r0 x w ∧ UnivGood N s r0 x w) →
      betaW w * N / 10 ^ 6 ≤ phi (flipP s w) s univ := by
  filter_upwards [tc_of_EX, tc_strict_of_EX, ev_N_dU_top, eventually_ge_atTop (10 ^ 7),
    eventually_ge_atTop (2 * KS ^ 2 + 2)] with N htc hst htop hNb hKS
  intro s r0 x hham w ho hw hF ⟨hR, hU⟩
  have htcr := htc s r0 x hham w ho hw hF hR
  rw [betaW, htcr]
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNbig : (10 : ℝ) ^ 7 ≤ N := by exact_mod_cast hNb
  have h0 : r0 ≠ s := fun h => by rw [h, ham_self] at hham; omega
  have h1 : flipAt x r0 ≠ s := fun h => by
    have := ham_flipAt_le_one x r0; rw [h, ham_comm] at this; omega
  have hk : ∃ k, w s k < 1 / 2 := by
    have hL := EX_s_lower (s := s) (r0 := r0) (x := x) hw
    have hc : 0 < (univ.filter fun k => w s k ∈ Set.Iio (1 / 2 : ℝ)).card := by
      have : (1 : ℝ) ≤ (N : ℝ) / 2 - (KS : ℝ) ^ 2 := by
        have : ((2 * KS ^ 2 + 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hKS
        push_cast at this; linarith
      have : (0 : ℝ) < ((univ.filter fun k => w s k ∈ Set.Iio (1 / 2 : ℝ)).card : ℝ) := by linarith
      exact_mod_cast this
    obtain ⟨k, hk⟩ := card_pos.1 hc
    exact ⟨k, (mem_filter.1 hk).2⟩
  have hT : XW w r0 ≤ x0 * N := by
    have := hF.T; have : 0 ≤ Real.log N := Real.log_natCast_nonneg N; linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have htop' : (N : ℝ) * dU N (N - 1) ≤ 1 / (2 * 10 ^ 6) := htop
  have hδs : dU N (N - 1) ≤ 1 / 10 ^ 8 := by
    have h0' := dU_nonneg N (N - 1)
    have := mul_le_mul_of_nonneg_right hNbig h0'
    linarith
  refine univ_lower_det (δ := dU N) (D := DU N) (dstar := dsU N) ho hN2 hNbig (dU_nonneg N) hδs
    (fun d d' _ h => dU_anti N h) (by unfold DU; omega) (DU_le (by omega)) (by unfold dsU; omega)
    (by unfold dsU DU; omega) (N_dU_DU hN1) (by linarith)
    (fun d hd _ => by have := N_dU_far hN1 hd; rw [mul_add]; linarith)
    (EX_y_ge hw) (EX_xE_ge hw) (hst s r0 x hham w ho hw hF hR) hF.L hF.V hF.M0
    (Zs_ge_of_low hU.low)
    (teW_mem_of_good ho hNbig h0 h1 (EX_y_ge hw) (EX_xE_ge hw) hk hT hF.L hU.low hU.upTe)
    hU.concC hU.concE hU.smallC hU.smallE

end Census
end IIT
