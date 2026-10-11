/-
Census of complexes: the real inequalities behind the bound on `Φ` of the maximal complex.

The Hamming-ball size `vk N k` is at most `(e N / k)^k`, which leaves an exponential margin against
`2^N`.  With it, the error terms of the cause-side estimates (`Dev`, `dlev`, `dsmall`) are small for
all candidate sizes simultaneously, eventually in `N`: exponentially small, or of relative size
`(log log N)^2 / log N` just above the size threshold `KN N`.  Finally the rate `rateN N` tends to
zero.
-/
import IIT.Census.BigPhiStats

namespace IIT
namespace Census

open Finset Filter Topology

/-! ## The error terms -/

/-- The variance bound `6 (2/3)^N + 4 N^3 vk (1/2)^N` for candidates of size at most `k`. -/
noncomputable def Vbd (N k : ℕ) : ℝ :=
  6 * (2 / 3 : ℝ) ^ N + 4 * (N : ℝ) ^ 3 * vk N k * (1 / 2 : ℝ) ^ N

/-- The deviation between the conditioned numerators of a candidate of size `k`. -/
noncomputable def Dev (N k : ℕ) : ℝ :=
  4 * Real.sqrt (LkN N k * Vbd N k) + (4 / 3) * LkN N k * (Real.sqrt 3 * sigN N + tauN N)

/-- The bound on the `Qw`-mass of a `k`-dimensional subcube. -/
noncomputable def Mk (N k : ℕ) : ℝ :=
  (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ (N - 1)
    + 16 * N * (Real.sqrt ((2 : ℝ) ^ k * (1 / 3 : ℝ) ^ (N - 1)) + tauN N)

/-- The fluctuation part of the bound on the `Qw`-mass of an `(N - k)`-dimensional subcube. -/
noncomputable def E6 (N k : ℕ) : ℝ :=
  16 * N * (Real.sqrt ((2 : ℝ) ^ (N - k) * (1 / 3 : ℝ) ^ (N - 1)) + tauN N)

/-- The deviation bound for candidates of intermediate size. -/
noncomputable def dlev (N k : ℕ) : ℝ := 2 * Real.sqrt (LkN N k * (3 * Mk N k))

/-- The deviation bound for small candidates. -/
noncomputable def dsmall (N k : ℕ) : ℝ := 2 * Real.sqrt (LkN N k * Vbd N k)

/-! ## Elementary helpers -/

lemma mul_sqrt_le_of_sq {a x b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 * x ≤ b ^ 2) :
    a * Real.sqrt x ≤ b := by
  rcases le_or_gt x 0 with hx | hx
  · rw [Real.sqrt_eq_zero'.2 hx, mul_zero]; exact hb
  · have h1 : a * Real.sqrt x = Real.sqrt (a ^ 2 * x) := by
      rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
    rw [h1, ← Real.sqrt_sq hb]
    exact Real.sqrt_le_sqrt h

lemma sigN_sq (N : ℕ) : sigN N ^ 2 = (2 / 3 : ℝ) ^ N := Real.sq_sqrt (by positivity)

lemma exp_neg_four_ninths_le : Real.exp (-(4 / 9)) ≤ 2 / 3 := by
  rw [Real.exp_neg]
  have h := Real.quadratic_le_exp_of_nonneg (x := 4 / 9) (by norm_num)
  have hpos : (0 : ℝ) < Real.exp (4 / 9) := Real.exp_pos _
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith

lemma tauN_le_two_sigN (N : ℕ) : tauN N ≤ 2 * sigN N := by
  have hsq : tauN N ^ 2 = Real.exp (4 / 9) * Real.exp (-(4 / 9)) ^ N := by
    rw [tauN, sq, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; ring
  have h49 : Real.exp (4 / 9) ≤ 4 := by
    have := Real.exp_one_lt_d9
    have : Real.exp (4 / 9) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
    linarith
  have hp : Real.exp (-(4 / 9)) ^ N ≤ (2 / 3 : ℝ) ^ N :=
    pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_four_ninths_le N
  have h1 : tauN N ^ 2 ≤ (2 * sigN N) ^ 2 := by
    rw [hsq, mul_pow, sigN_sq]
    have : 0 ≤ Real.exp (-(4 / 9)) ^ N := by positivity
    nlinarith [Real.exp_pos (4 / 9)]
  nlinarith [tauN_pos N, sigN_pos N]

/-! ## The Hamming ball -/

/-- The Hamming ball of radius `k ≤ N` has at most `(e N / k)^k` points. -/
theorem vk_le {N k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) : (vk N k : ℝ) ≤ (Real.exp 1 * N / k) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hk hkN)
  set x : ℝ := (k : ℝ) / N with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hNpos]; exact_mod_cast hkN
  have h1 : (vk N k : ℝ) * x ^ k ≤ (x + 1) ^ N := by
    rw [add_pow]
    unfold vk; push_cast
    rw [sum_mul]
    calc ∑ j ∈ Icc 1 k, (N.choose j : ℝ) * x ^ k
        ≤ ∑ j ∈ Icc 1 k, x ^ j * 1 ^ (N - j) * (N.choose j : ℝ) := by
          apply sum_le_sum; intro j hj; rw [mem_Icc] at hj
          rw [one_pow, mul_one, mul_comm]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hx0.le hx1 hj.2) (by positivity)
      _ ≤ ∑ j ∈ range (N + 1), x ^ j * 1 ^ (N - j) * (N.choose j : ℝ) :=
          sum_le_sum_of_subset_of_nonneg
            (by intro j hj; rw [mem_Icc] at hj; rw [mem_range]; omega)
            (fun _ _ _ => by positivity)
  have h2 : (x + 1) ^ N ≤ Real.exp 1 ^ k := by
    calc (x + 1) ^ N ≤ Real.exp x ^ N := pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp x) N
      _ = Real.exp 1 ^ k := by
          rw [← Real.exp_nat_mul, Real.exp_one_pow, hx]; congr 1; field_simp
  have h3 : (Real.exp 1 * N / k) ^ k = Real.exp 1 ^ k / x ^ k := by
    rw [hx, div_pow, div_pow, mul_pow]; field_simp
  rw [h3, le_div_iff₀ (by positivity)]
  linarith

lemma vk_zero_right (N : ℕ) : vk N 0 = 0 := by simp [vk]

lemma vk_eq_of_le {N k : ℕ} (h : N ≤ k) : vk N k = vk N N := by
  unfold vk
  symm
  apply sum_subset
  · intro j hj; rw [mem_Icc] at hj ⊢; omega
  · intro j hj hj'; rw [mem_Icc] at hj hj'
    exact Nat.choose_eq_zero_of_lt (by omega)

/-- `vk N k ≤ e^{N/4} 4^k`, from `ε (1 - log (4 ε)) ≤ 1/4`. -/
lemma vk_le_exp (N k : ℕ) : (vk N k : ℝ) ≤ Real.exp (N / 4) * 4 ^ k := by
  have key : ∀ k : ℕ, 1 ≤ k → k ≤ N → (vk N k : ℝ) ≤ Real.exp (N / 4) * 4 ^ k := by
    intro k hk hkN
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hk hkN)
    set y : ℝ := 4 * k / N with hy
    have hy0 : 0 < y := by positivity
    have hlog := Real.one_sub_inv_le_log_of_pos hy0
    have hinv : (k : ℝ) * y⁻¹ = N / 4 := by rw [hy]; field_simp
    have hexp : Real.exp 1 * N / k = 4 * Real.exp (1 - Real.log y) := by
      rw [Real.exp_sub, Real.exp_log hy0, hy]; field_simp
    refine (vk_le hk hkN).trans ?_
    rw [hexp, mul_pow, ← Real.exp_nat_mul, mul_comm (Real.exp _)]
    gcongr
    nlinarith
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [vk_zero_right]; positivity
  rcases le_or_gt k N with hkN | hkN
  · exact key k hk hkN
  · rw [vk_eq_of_le hkN.le]
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · rw [h0, vk_zero_right]; simp
    · refine (key N hN le_rfl).trans ?_
      gcongr
      · norm_num

/-- The exponential margin of the Hamming ball against the cube:
`vk N k (1/2)^N ≤ e^{-(log (4/3) - 1/4) N} 4^k (2/3)^N`. -/
theorem vk_margin (N k : ℕ) : (vk N k : ℝ) * (1 / 2 : ℝ) ^ N ≤
    Real.exp (-(Real.log (4 / 3) - 1 / 4) * N) * 4 ^ k * (2 / 3 : ℝ) ^ N := by
  have h43 : (4 / 3 : ℝ) ^ N = Real.exp (N * Real.log (4 / 3)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hid : Real.exp (-(Real.log (4 / 3) - 1 / 4) * N) * (2 / 3 : ℝ) ^ N
      = Real.exp (N / 4) * (1 / 2 : ℝ) ^ N := by
    have : (2 / 3 : ℝ) ^ N = (4 / 3 : ℝ) ^ N * (1 / 2 : ℝ) ^ N := by
      rw [← mul_pow]; norm_num
    rw [this, h43, ← mul_assoc, ← Real.exp_add]
    congr 2; ring
  calc (vk N k : ℝ) * (1 / 2 : ℝ) ^ N ≤ Real.exp (N / 4) * 4 ^ k * (1 / 2 : ℝ) ^ N := by
        gcongr; exact vk_le_exp N k
    _ = _ := by rw [mul_right_comm, ← hid]; ring

/-- The per-coordinate rate `e^{-(log (4/3) - 1/4)} < 1` of `vk_margin`. -/
noncomputable def vkRate : ℝ := Real.exp (-(Real.log (4 / 3) - 1 / 4))

lemma log_four_thirds_gt : 1 / 4 < Real.log (4 / 3) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h : Real.exp (1 / 4) ^ 4 < (4 / 3 : ℝ) ^ 4 := by
    rw [← Real.exp_nat_mul]
    have := Real.exp_one_lt_d9
    norm_num
    linarith
  exact lt_of_pow_lt_pow_left₀ 4 (by norm_num) h

lemma vkRate_pos : 0 < vkRate := Real.exp_pos _

lemma vkRate_lt_one : vkRate < 1 := by
  rw [vkRate, Real.exp_lt_one_iff]; linarith [log_four_thirds_gt]

lemma Vbd_le (N k : ℕ) : Vbd N k ≤ (6 + 4 * (N : ℝ) ^ 3 * vkRate ^ N * 4 ^ k) * sigN N ^ 2 := by
  have h := vk_margin N k
  rw [mul_comm (-(Real.log (4 / 3) - 1 / 4)), Real.exp_nat_mul] at h
  rw [sigN_sq, Vbd]
  have hN3 : 0 ≤ 4 * (N : ℝ) ^ 3 := by positivity
  have := mul_le_mul_of_nonneg_left h hN3
  unfold vkRate
  nlinarith

lemma sqrt_three_le_two : Real.sqrt 3 ≤ 2 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)

lemma LkN_nonneg' {N : ℕ} (k : ℕ) (hN : 1 ≤ N) : 0 ≤ LkN N k := by
  have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  unfold LkN; positivity

lemma exp_two_mul_le : Real.exp 2 * (8 / Real.log 2) ≤ 100 := by
  have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have h1 := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have e2' : Real.exp 2 ≤ 7.4 := by rw [e2]; nlinarith
  have l2 := Real.log_two_gt_d9
  have l2' : 8 / Real.log 2 ≤ 12 := by rw [div_le_iff₀ (by linarith)]; linarith
  have : 0 ≤ 8 / Real.log 2 := by positivity
  nlinarith [Real.exp_pos 2]

/-! ## Asymptotic helpers -/

/-- `C N^p r^N` is eventually below any positive level when `0 ≤ r < 1`. -/
lemma ev_poly_geom (p : ℕ) {r : ℝ} (h0 : 0 ≤ r) (hr : r < 1) (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ p * r ^ N < ε := by
  have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one p
    (by rw [abs_of_nonneg h0]; exact hr)).const_mul C
  rw [mul_zero] at h
  filter_upwards [(tendsto_order.1 h).2 ε hε] with N hN
  simpa [mul_assoc] using hN

/-- `C N^p σ_N` is eventually below any positive level. -/
lemma ev_pow_mul_sigN (p : ℕ) {C : ℝ} (hC : 0 ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ p * sigN N ≤ ε := by
  filter_upwards [ev_poly_geom (2 * p) (r := 2 / 3) (by norm_num) (by norm_num) (C ^ 2)
    (pow_pos hε 2)] with N hN
  apply mul_sqrt_le_of_sq (by positivity) hε.le
  have : (C * (N : ℝ) ^ p) ^ 2 * (2 / 3 : ℝ) ^ N = C ^ 2 * (N : ℝ) ^ (2 * p) * (2 / 3 : ℝ) ^ N := by
    ring
  rw [this]; exact hN.le

lemma tendsto_quad_half (a b c : ℝ) :
    Tendsto (fun n : ℕ => (a * n ^ 2 + b * n + c) * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
  have hr : |(1 / 2 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have h2 := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hr).const_mul a
  have h1 := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr).const_mul b
  have h0 := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
    (by norm_num)).const_mul c
  have := (h2.add h1).add h0
  simp only [mul_zero, add_zero] at this
  refine this.congr fun n => ?_
  ring

lemma tendsto_natLog2 : Tendsto (fun N : ℕ => Nat.log 2 N) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨2 ^ b, fun _ ha => Nat.le_log_of_pow_le (by norm_num) ha⟩

lemma ev_quad_half_comp {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) (a b c : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, (a * (f N : ℝ) ^ 2 + b * f N + c) * (1 / 2 : ℝ) ^ f N < ε :=
  ((tendsto_quad_half a b c).comp hf).eventually (gt_mem_nhds hε)

/-! ## Facts on the logarithms -/

lemma log_le_natLog {N : ℕ} (hN : 1 ≤ N) : Real.log N ≤ Nat.log 2 N + 1 := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h' : (N : ℝ) < 2 ^ (Nat.log 2 N + 1) := by exact_mod_cast h
  have hl := Real.log_lt_log hN' h'
  rw [Real.log_pow] at hl
  have l2 := Real.log_two_lt_d9
  have l2' := Real.log_two_gt_d9
  push_cast at hl
  nlinarith

lemma natLog_succ_le (N : ℕ) : Nat.log 2 N + 1 ≤ 2 * 2 ^ Nat.log 2 (Nat.log 2 N) := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Nat.log 2 N)
  rw [pow_succ] at h; omega

lemma two_pow_natLog_le {N : ℕ} (hN : 1 ≤ N) : 2 ^ Nat.log 2 N ≤ N :=
  Nat.pow_log_le_self 2 (by omega)

lemma natLog_succ_le_self {N : ℕ} (hN : 1 ≤ N) : Nat.log 2 N + 1 ≤ N :=
  (Nat.lt_two_pow_self).trans_le (two_pow_natLog_le hN)

lemma two_pow_m_le {N : ℕ} (hN : 1 ≤ N) : 2 ^ Nat.log 2 (Nat.log 2 N) ≤ N := by
  rcases Nat.eq_zero_or_pos (Nat.log 2 N) with h | h
  · rw [h]; simpa using hN
  · exact (Nat.pow_log_le_self 2 h.ne').trans (Nat.log_le_self 2 N)

lemma lt_two_mul_two_pow_natLog (N : ℕ) : N < 2 * 2 ^ Nat.log 2 N := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  rw [pow_succ] at h; omega

lemma sq_mul_two_pow_le {a b : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) : b ^ 2 * 2 ^ a ≤ a ^ 2 * 2 ^ b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    have h1 : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
    calc (n + 1) ^ 2 * 2 ^ a ≤ 2 * n ^ 2 * 2 ^ a := Nat.mul_le_mul_right _ h1
      _ = 2 * (n ^ 2 * 2 ^ a) := by ring
      _ ≤ 2 * (a ^ 2 * 2 ^ n) := Nat.mul_le_mul_left _ ih
      _ = a ^ 2 * 2 ^ (n + 1) := by ring

lemma four_pow_le {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ KN N) : (4 : ℝ) ^ k ≤ 256 * (N : ℝ) ^ 4 := by
  have h1 : 4 ^ k ≤ 4 ^ KN N := Nat.pow_le_pow_right (by norm_num) hk
  have h2 : 4 ^ KN N = 256 * (2 ^ Nat.log 2 (Nat.log 2 N)) ^ 4 := by
    unfold KN
    rw [pow_add, pow_mul, ← pow_mul 2 _ 4, mul_comm _ 4, pow_mul]
    norm_num; ring
  have h3 := Nat.pow_le_pow_left (two_pow_m_le hN) 4
  have : 4 ^ k ≤ 256 * N ^ 4 := by rw [h2] at h1; omega
  exact_mod_cast this


lemma LkN_le_six_sq {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) : LkN N k ≤ 6 * (N : ℝ) ^ 2 := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg hN'
  have hl1 : Real.log N ≤ N := Real.log_le_self (by positivity)
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  unfold LkN
  nlinarith [mul_le_mul hk' hl1 hl0 (by positivity)]

lemma LkN_le_natLog {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) :
    LkN N k ≤ 6 * k * ((Nat.log 2 N : ℝ) + 1) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg hN'
  have hl1 := log_le_natLog hN
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hℓ : (0 : ℝ) ≤ Nat.log 2 N := by positivity
  unfold LkN
  nlinarith [mul_le_mul_of_nonneg_left hl1 (by linarith : (0 : ℝ) ≤ k)]

/-- Just above the threshold `KN N`, `k LkN / 2^k ≤ (3/8)(2m+5)^2 2^{-m}` with
`m = log₂ log₂ N`. -/
lemma kL_div_le {N k : ℕ} (hN : 1 ≤ N) (hk : KN N < k) :
    (k : ℝ) * LkN N k / 2 ^ k ≤
      (3 / 2 * (Nat.log 2 (Nat.log 2 N) : ℝ) ^ 2 + 15 / 2 * Nat.log 2 (Nat.log 2 N) + 75 / 8)
        * (1 / 2 : ℝ) ^ Nat.log 2 (Nat.log 2 N) := by
  set m := Nat.log 2 (Nat.log 2 N) with hm
  have hKN : KN N = 2 * m + 4 := rfl
  have hk1 : 1 ≤ k := by omega
  have hL := LkN_le_natLog hN hk1
  have hℓ : ((Nat.log 2 N : ℕ) : ℝ) + 1 ≤ 2 * 2 ^ m := by
    have := natLog_succ_le N
    rw [← hm] at this
    exact_mod_cast this
  have hsq : k ^ 2 * 2 ^ (2 * m + 5) ≤ (2 * m + 5) ^ 2 * 2 ^ k :=
    sq_mul_two_pow_le (by omega) (by omega)
  have hsq' : (k : ℝ) ^ 2 * 2 ^ (2 * m + 5) ≤ (2 * m + 5) ^ 2 * 2 ^ k := by exact_mod_cast hsq
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hpow : (2 : ℝ) ^ (2 * m + 5) = 32 * 2 ^ m * 2 ^ m := by
    rw [pow_add, mul_comm 2 m, pow_mul]; ring
  have hhalf : (1 / 2 : ℝ) ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
  rw [div_le_iff₀ h2k]
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hLk : (k : ℝ) * LkN N k ≤ 6 * k ^ 2 * (2 * 2 ^ m) := by
    calc (k : ℝ) * LkN N k ≤ k * (6 * k * ((Nat.log 2 N : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hL hk0
      _ ≤ k * (6 * k * (2 * 2 ^ m)) := by gcongr
      _ = 6 * k ^ 2 * (2 * 2 ^ m) := by ring
  rw [hpow] at hsq'
  have hgoal : 6 * (k : ℝ) ^ 2 * (2 * 2 ^ m) * (32 * 2 ^ m) ≤
      (3 / 2 * (m : ℝ) ^ 2 + 15 / 2 * m + 75 / 8) * 2 ^ k * 32 := by
    nlinarith
  have hfin : 6 * (k : ℝ) ^ 2 * (2 * 2 ^ m) ≤
      (3 / 2 * (m : ℝ) ^ 2 + 15 / 2 * m + 75 / 8) * (1 / 2 : ℝ) ^ m * 2 ^ k := by
    have h32 : (0 : ℝ) < 32 * 2 ^ m := by positivity
    rw [← mul_le_mul_iff_left₀ h32]
    calc 6 * (k : ℝ) ^ 2 * (2 * 2 ^ m) * (32 * 2 ^ m)
        ≤ (3 / 2 * (m : ℝ) ^ 2 + 15 / 2 * m + 75 / 8) * 2 ^ k * 32 := hgoal
      _ = (3 / 2 * (m : ℝ) ^ 2 + 15 / 2 * m + 75 / 8) * ((1 / 2 : ℝ) ^ m * 2 ^ m) * 2 ^ k * 32 := by
          rw [hhalf]; ring
      _ = _ := by ring
  linarith

/-- Range I: above the threshold `KN N`, the cause-side bound is below `σ_N / 128`. -/
theorem eventually_rangeI : ∀ᶠ N in atTop, ∀ k, KN N < k → k ≤ N →
    (k : ℝ) * Real.exp 2 / 2 ^ k * (8 / Real.log 2) * Dev N k < sigN N / 128 := by
  have hm : Tendsto (fun N : ℕ => Nat.log 2 (Nat.log 2 N)) atTop atTop :=
    tendsto_natLog2.comp tendsto_natLog2
  filter_upwards [eventually_ge_atTop 1,
    ev_quad_half_comp hm (3 / 2) (15 / 2) (75 / 8) (by norm_num : (0 : ℝ) < 1e-12),
    ev_poly_geom 7 vkRate_pos.le vkRate_lt_one 24 (by norm_num : (0 : ℝ) < 1e-12)]
    with N hN hT hρ
  intro k hk hkN
  have hT' := (kL_div_le hN hk).trans hT.le
  have hσ := sigN_pos N
  have hτ := tauN_le_two_sigN N
  have hL0 := LkN_nonneg' k hN
  have hL6 := LkN_le_six_sq hN hkN
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  set a : ℝ := (k : ℝ) / 2 ^ k with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one h2k]; exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have hT2 : a * LkN N k ≤ 1e-12 := by
    rw [ha, div_mul_eq_mul_div]; exact hT'
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hk0 : (0 : ℝ) ≤ k := by positivity
  -- the square-root part
  have hV := Vbd_le N k
  have ha4 : a ^ 2 * (4 : ℝ) ^ k = (k : ℝ) ^ 2 := by
    rw [ha, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm 2 k, pow_mul]
    field_simp
  have hρN : 0 ≤ vkRate ^ N := by have := vkRate_pos; positivity
  have hA : a * Real.sqrt (LkN N k * Vbd N k) ≤ 3e-6 * sigN N := by
    apply mul_sqrt_le_of_sq ha0 (by positivity)
    have e1 : a ^ 2 * (LkN N k * Vbd N k) ≤
        a ^ 2 * (LkN N k * ((6 + 4 * (N : ℝ) ^ 3 * vkRate ^ N * 4 ^ k) * sigN N ^ 2)) := by
      gcongr
    have e2 : a ^ 2 * (LkN N k * ((6 + 4 * (N : ℝ) ^ 3 * vkRate ^ N * 4 ^ k) * sigN N ^ 2)) =
        (6 * (a * (a * LkN N k)) + 4 * ((k : ℝ) ^ 2 * LkN N k * (N : ℝ) ^ 3 * vkRate ^ N))
          * sigN N ^ 2 := by
      rw [← ha4]; ring
    have e3 : a * (a * LkN N k) ≤ 1e-12 := by
      calc a * (a * LkN N k) ≤ 1 * (a * LkN N k) :=
            mul_le_mul_of_nonneg_right ha1 (by positivity)
        _ ≤ 1e-12 := by linarith
    have e4 : (k : ℝ) ^ 2 * LkN N k * (N : ℝ) ^ 3 * vkRate ^ N ≤
        (N : ℝ) ^ 2 * (6 * (N : ℝ) ^ 2) * (N : ℝ) ^ 3 * vkRate ^ N := by
      gcongr
    have e5 : (N : ℝ) ^ 2 * (6 * (N : ℝ) ^ 2) * (N : ℝ) ^ 3 * vkRate ^ N * 4 < 1e-12 := by
      have : (N : ℝ) ^ 2 * (6 * (N : ℝ) ^ 2) * (N : ℝ) ^ 3 * vkRate ^ N * 4 =
          24 * (N : ℝ) ^ 7 * vkRate ^ N := by ring
      rw [this]; exact hρ
    have hs2 : 0 ≤ sigN N ^ 2 := by positivity
    calc a ^ 2 * (LkN N k * Vbd N k) ≤ _ := e1
      _ = _ := e2
      _ ≤ (6 * 1e-12 + 1e-12) * sigN N ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hs2
          nlinarith
      _ ≤ (3e-6 * sigN N) ^ 2 := by nlinarith
  -- the linear part
  have hB : a * ((4 / 3) * LkN N k * (Real.sqrt 3 * sigN N + tauN N)) ≤
      (16 / 3) * 1e-12 * sigN N := by
    have h3 := sqrt_three_le_two
    have hs : Real.sqrt 3 * sigN N + tauN N ≤ 4 * sigN N := by nlinarith
    have hs0 : 0 ≤ Real.sqrt 3 * sigN N + tauN N := by
      have := tauN_pos N; positivity
    calc a * ((4 / 3) * LkN N k * (Real.sqrt 3 * sigN N + tauN N))
        = (4 / 3) * (a * LkN N k) * (Real.sqrt 3 * sigN N + tauN N) := by ring
      _ ≤ (4 / 3) * 1e-12 * (4 * sigN N) := by gcongr
      _ = _ := by ring
  have hDev : a * Dev N k ≤ (4 * 3e-6 + (16 / 3) * 1e-12) * sigN N := by
    rw [Dev]
    have : a * (4 * Real.sqrt (LkN N k * Vbd N k)
          + 4 / 3 * LkN N k * (Real.sqrt 3 * sigN N + tauN N))
        = 4 * (a * Real.sqrt (LkN N k * Vbd N k))
          + a * ((4 / 3) * LkN N k * (Real.sqrt 3 * sigN N + tauN N)) := by ring
    rw [this]; linarith
  have hC := exp_two_mul_le
  have hC0 : 0 ≤ Real.exp 2 * (8 / Real.log 2) := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have hrw : (k : ℝ) * Real.exp 2 / 2 ^ k * (8 / Real.log 2) * Dev N k
      = (Real.exp 2 * (8 / Real.log 2)) * (a * Dev N k) := by rw [ha]; ring
  rw [hrw]
  have hy0 : 0 ≤ (4 * 3e-6 + (16 / 3) * 1e-12) * sigN N := by positivity
  calc (Real.exp 2 * (8 / Real.log 2)) * (a * Dev N k)
      ≤ (Real.exp 2 * (8 / Real.log 2)) * ((4 * 3e-6 + (16 / 3) * 1e-12) * sigN N) :=
        mul_le_mul_of_nonneg_left hDev hC0
    _ ≤ 100 * ((4 * 3e-6 + (16 / 3) * 1e-12) * sigN N) := mul_le_mul_of_nonneg_right hC hy0
    _ < sigN N / 128 := by nlinarith


/-! ## Intermediate sizes -/

lemma two_pow_third_le {N a : ℕ} (hN : 1 ≤ N) (ha : a ≤ N) :
    (2 : ℝ) ^ a * (1 / 3 : ℝ) ^ (N - 1) ≤ 4 * sigN N ^ 2 := by
  rw [sigN_sq]
  have h1 : (1 / 3 : ℝ) ^ (N - 1) = 3 * (1 / 3) ^ N := by
    obtain ⟨j, rfl⟩ : ∃ j, N = j + 1 := ⟨N - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]; ring
  have h2 : (2 : ℝ) ^ a ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) ha
  have h3 : (2 / 3 : ℝ) ^ N = 2 ^ N * (1 / 3) ^ N := by rw [← mul_pow]; norm_num
  rw [h1, h3]
  have h0 : 0 ≤ (1 / 3 : ℝ) ^ N := by positivity
  have h4 := mul_le_mul_of_nonneg_right h2 h0
  have h5 : 0 ≤ (2 : ℝ) ^ N * (1 / 3) ^ N := by positivity
  nlinarith

lemma sqrt_two_pow_third_le {N a : ℕ} (hN : 1 ≤ N) (ha : a ≤ N) :
    Real.sqrt ((2 : ℝ) ^ a * (1 / 3 : ℝ) ^ (N - 1)) ≤ 2 * sigN N := by
  rw [Real.sqrt_le_left (by have := sigN_pos N; positivity), mul_pow]
  have := two_pow_third_le hN ha
  linarith

lemma Mk_le {N k : ℕ} (hN : 1 ≤ N) (hk : k + (4 * Nat.log 2 N + 16) ≤ N) :
    Mk N k ≤ (1 / 2 : ℝ) ^ (4 * Nat.log 2 N + 15) + 64 * N * sigN N := by
  have h1 : (2 : ℝ) ^ k * (1 / 2) ^ (N - 1) ≤ (1 / 2) ^ (4 * Nat.log 2 N + 15) := by
    obtain ⟨j, hj⟩ : ∃ j, N - 1 = k + j := ⟨N - 1 - k, by omega⟩
    rw [hj, pow_add, ← mul_assoc, ← mul_pow, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow,
      one_mul]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h2 := sqrt_two_pow_third_le hN (a := k) (by omega)
  have h3 := tauN_le_two_sigN N
  unfold Mk
  have : (0 : ℝ) ≤ 16 * N := by positivity
  nlinarith

lemma E6_le {N : ℕ} (k : ℕ) (hN : 1 ≤ N) : E6 N k ≤ 64 * N * sigN N := by
  have h2 := sqrt_two_pow_third_le hN (a := N - k) (by omega)
  have h3 := tauN_le_two_sigN N
  unfold E6
  have : (0 : ℝ) ≤ 16 * N := by positivity
  nlinarith

lemma E6_nonneg (N k : ℕ) : 0 ≤ E6 N k := by
  unfold E6; have := tauN_pos N; positivity

lemma dlev_nonneg (N k : ℕ) : 0 ≤ dlev N k := by unfold dlev; positivity

lemma dsmall_nonneg (N k : ℕ) : 0 ≤ dsmall N k := by unfold dsmall; positivity

lemma LkN_le_levels {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) :
    LkN N k ≤ N * ((Nat.log 2 N : ℝ) + 6) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg hN'
  have hl1 := log_le_natLog hN
  have hℓN : ((Nat.log 2 N : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast natLog_succ_le_self hN
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  unfold LkN
  nlinarith [mul_le_mul hk' hl1 hl0 (by positivity)]

lemma le_two_pow_pred {k : ℕ} (hk : 1 ≤ k) : k ≤ 2 ^ (k - 1) := by
  have := Nat.lt_two_pow_self (n := k - 1); omega

/-- Intermediate sizes `2 ≤ k ≤ K2N N`: the lower bound on the numerators and the budget of the
product comparison. -/
theorem eventually_levels : ∀ᶠ N in atTop, ∀ k, 2 ≤ k → k ≤ K2N N →
    16 * N * sigN N / 2 + dlev N k ≤ 1 / 8 ∧
    (k : ℝ) * 8 * (((1 / 2 : ℝ) ^ (k - 1) + E6 N k) / 12 + 2 * dlev N k) ≤ 2 := by
  filter_upwards [eventually_ge_atTop 1,
    ev_quad_half_comp tendsto_natLog2 0 1 6 (by norm_num : (0 : ℝ) < 1e-3),
    ev_pow_mul_sigN 5 (C := 5376) (by norm_num) (by norm_num : (0 : ℝ) < 5e-5),
    ev_pow_mul_sigN 1 (C := 8) (by norm_num) (by norm_num : (0 : ℝ) < 1e-2),
    ev_pow_mul_sigN 2 (C := 64) (by norm_num) (by norm_num : (0 : ℝ) < 1e-2)]
    with N hN hℓ h5 h1 h2
  intro k hk2 hkK
  set ℓ := Nat.log 2 N with hℓdef
  have hkN : k + (4 * ℓ + 16) ≤ N := by unfold K2N at hkK; omega
  have hkN' : k ≤ N := by omega
  have hσ := sigN_pos N
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hℓ' : ((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ ℓ < 1e-3 := by
    have : ((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ ℓ = (0 * (ℓ : ℝ) ^ 2 + 1 * ℓ + 6) * (1 / 2 : ℝ) ^ ℓ := by
      ring
    rw [this]; exact hℓ
  -- `N dlev ≤ 1/100`
  have hNd : (N : ℝ) * dlev N k ≤ 1 / 100 := by
    have e : (N : ℝ) * dlev N k = (2 * N) * Real.sqrt (LkN N k * (3 * Mk N k)) := by
      rw [dlev]; ring
    rw [e]
    apply mul_sqrt_le_of_sq (by positivity) (by norm_num)
    have hL := LkN_le_levels hN hkN'
    have hL0 := LkN_nonneg' k hN
    have hM := Mk_le hN hkN
    set Mb : ℝ := (1 / 2 : ℝ) ^ (4 * ℓ + 15) + 64 * N * sigN N with hMb
    have hMb0 : 0 ≤ Mb := by positivity
    have s1 : (2 * (N : ℝ)) ^ 2 * (LkN N k * (3 * Mk N k)) ≤
        (2 * (N : ℝ)) ^ 2 * ((N * ((ℓ : ℝ) + 6)) * (3 * Mb)) := by
      have : LkN N k * (3 * Mk N k) ≤ (N * ((ℓ : ℝ) + 6)) * (3 * Mb) := by
        calc LkN N k * (3 * Mk N k) ≤ LkN N k * (3 * Mb) := by gcongr
          _ ≤ _ := by gcongr
      exact mul_le_mul_of_nonneg_left this (by positivity)
    -- the two pieces of `Mb`
    set u : ℝ := (N : ℝ) * (1 / 2 : ℝ) ^ ℓ with hu
    have hu0 : 0 ≤ u := by positivity
    have hu2 : u ≤ 2 := by
      have hlt : (N : ℝ) < 2 * 2 ^ ℓ := by exact_mod_cast lt_two_mul_two_pow_natLog N
      have hh : (2 : ℝ) ^ ℓ * (1 / 2 : ℝ) ^ ℓ = 1 := by rw [← mul_pow]; norm_num
      have : 0 < (1 / 2 : ℝ) ^ ℓ := by positivity
      rw [hu]; nlinarith
    have hu3 : u ^ 3 ≤ 8 := by
      have := pow_le_pow_left₀ hu0 hu2 3; norm_num at this; linarith
    have hpow : (1 / 2 : ℝ) ^ (4 * ℓ + 15) = ((1 / 2 : ℝ) ^ ℓ) ^ 3 * (1 / 2 : ℝ) ^ ℓ * (1 / 2) ^ 15 := by
      rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
    have p1 : 12 * (N : ℝ) ^ 3 * ((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ (4 * ℓ + 15) ≤ 1e-5 := by
      have e1 : 12 * (N : ℝ) ^ 3 * ((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ (4 * ℓ + 15) =
          12 * u ^ 3 * (1 / 2) ^ 15 * (((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ ℓ) := by
        rw [hpow, hu]; ring
      rw [e1]
      have : 0 ≤ ((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ ℓ := by positivity
      have : 12 * u ^ 3 * (1 / 2 : ℝ) ^ 15 ≤ 12 * 8 * (1 / 2) ^ 15 := by gcongr
      nlinarith
    have p2 : 768 * (N : ℝ) ^ 4 * ((ℓ : ℝ) + 6) * sigN N ≤ 5e-5 := by
      have hℓN : ((ℓ : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast natLog_succ_le_self hN
      have : 768 * (N : ℝ) ^ 4 * ((ℓ : ℝ) + 6) * sigN N ≤ 768 * (N : ℝ) ^ 4 * (7 * N) * sigN N := by
        gcongr; linarith
      have e : 768 * (N : ℝ) ^ 4 * (7 * N) * sigN N = 5376 * (N : ℝ) ^ 5 * sigN N := by ring
      linarith
    have e2 : (2 * (N : ℝ)) ^ 2 * ((N * ((ℓ : ℝ) + 6)) * (3 * Mb)) =
        12 * (N : ℝ) ^ 3 * ((ℓ : ℝ) + 6) * (1 / 2 : ℝ) ^ (4 * ℓ + 15)
          + 768 * (N : ℝ) ^ 4 * ((ℓ : ℝ) + 6) * sigN N := by
      rw [hMb]; ring
    rw [e2] at s1
    nlinarith
  have hd0 := dlev_nonneg N k
  have hdl : dlev N k ≤ 1 / 100 := by nlinarith
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hkN'
  have hk0 : (0 : ℝ) ≤ k := by positivity
  constructor
  · have : 16 * (N : ℝ) * sigN N / 2 = 8 * (N : ℝ) ^ 1 * sigN N := by ring
    rw [this]; linarith
  · have hkp : (k : ℝ) * (1 / 2 : ℝ) ^ (k - 1) ≤ 1 := by
      have h1' : (k : ℝ) ≤ 2 ^ (k - 1) := by exact_mod_cast le_two_pow_pred (by omega : 1 ≤ k)
      have hh : (2 : ℝ) ^ (k - 1) * (1 / 2 : ℝ) ^ (k - 1) = 1 := by rw [← mul_pow]; norm_num
      have : 0 ≤ (1 / 2 : ℝ) ^ (k - 1) := by positivity
      nlinarith
    have hE := E6_le k hN
    have hE0 := E6_nonneg N k
    have hkE : (k : ℝ) * E6 N k ≤ 1e-2 := by
      calc (k : ℝ) * E6 N k ≤ N * (64 * N * sigN N) := mul_le_mul hk' hE hE0 (by positivity)
        _ = 64 * (N : ℝ) ^ 2 * sigN N := by ring
        _ ≤ 1e-2 := h2
    have hkd : (k : ℝ) * dlev N k ≤ 1 / 100 :=
      (mul_le_mul_of_nonneg_right hk' hd0).trans hNd
    have e : (k : ℝ) * 8 * (((1 / 2 : ℝ) ^ (k - 1) + E6 N k) / 12 + 2 * dlev N k)
        = (2 / 3) * ((k : ℝ) * (1 / 2 : ℝ) ^ (k - 1)) + (2 / 3) * ((k : ℝ) * E6 N k)
          + 16 * ((k : ℝ) * dlev N k) := by ring
    rw [e]; linarith

/-! ## Small sizes -/

lemma KN_le_six_mul {N : ℕ} (hN : 1 ≤ N) : KN N ≤ 6 * N := by
  have h := two_pow_m_le hN
  have h2 := Nat.lt_two_pow_self (n := Nat.log 2 (Nat.log 2 N))
  unfold KN; omega

lemma Vbd_le_seven {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ KN N)
    (hρ : 1024 * (N : ℝ) ^ 7 * vkRate ^ N < 1) : Vbd N k ≤ 7 * sigN N ^ 2 := by
  have hV := Vbd_le N k
  have h4 := four_pow_le hN hk
  have hρ0 : 0 ≤ vkRate ^ N := by have := vkRate_pos; positivity
  have : 4 * (N : ℝ) ^ 3 * vkRate ^ N * 4 ^ k ≤ 1 := by
    calc 4 * (N : ℝ) ^ 3 * vkRate ^ N * 4 ^ k ≤ 4 * (N : ℝ) ^ 3 * vkRate ^ N * (256 * (N : ℝ) ^ 4) := by
          gcongr
      _ = 1024 * (N : ℝ) ^ 7 * vkRate ^ N := by ring
      _ ≤ 1 := hρ.le
  have hs : 0 ≤ sigN N ^ 2 := by positivity
  nlinarith

lemma Vbd_nonneg (N k : ℕ) : 0 ≤ Vbd N k := by unfold Vbd; positivity

/-- Small sizes `k ≤ KN N`: the lower bound on the numerators. -/
theorem eventually_small : ∀ᶠ N in atTop, ∀ k ≤ KN N, 16 * N * sigN N / 2 + dsmall N k ≤ 1 / 8 := by
  filter_upwards [eventually_ge_atTop 1,
    ev_poly_geom 7 vkRate_pos.le vkRate_lt_one 1024 one_pos,
    ev_poly_geom 2 (r := 2 / 3) (by norm_num) (by norm_num) 728 (by norm_num : (0 : ℝ) < 1e-4),
    ev_pow_mul_sigN 1 (C := 8) (by norm_num) (by norm_num : (0 : ℝ) < 1e-2)]
    with N hN hρ h728 h1
  intro k hk
  have hV := Vbd_le_seven hN hk hρ
  have hL0 := LkN_nonneg' k hN
  have hL : LkN N k ≤ 26 * (N : ℝ) ^ 2 := by
    have hK := KN_le_six_mul hN
    have hk' : (k : ℝ) ≤ 6 * N := by exact_mod_cast hk.trans hK
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hl0 : 0 ≤ Real.log N := Real.log_nonneg hN'
    have hl1 : Real.log N ≤ N := Real.log_le_self (by positivity)
    unfold LkN
    nlinarith [mul_le_mul hk' hl1 hl0 (by positivity)]
  have hds : dsmall N k ≤ 1 / 100 := by
    unfold dsmall
    apply mul_sqrt_le_of_sq (by norm_num) (by norm_num)
    have hs : 0 ≤ sigN N ^ 2 := by positivity
    have := Vbd_nonneg N k
    calc (2 : ℝ) ^ 2 * (LkN N k * Vbd N k) ≤ 4 * (26 * (N : ℝ) ^ 2 * (7 * sigN N ^ 2)) := by
          norm_num; gcongr
      _ = 728 * (N : ℝ) ^ 2 * (2 / 3 : ℝ) ^ N := by rw [sigN_sq]; ring
      _ ≤ (1 / 100) ^ 2 := by linarith
  have : 16 * (N : ℝ) * sigN N / 2 = 8 * (N : ℝ) ^ 1 * sigN N := by ring
  rw [this]; linarith

/-! ## Near-universe sizes and the thresholds -/

/-- Range II: near the whole substrate the effect-side bound is below `σ_N / 128`. -/
theorem eventually_rangeII : ∀ᶠ N in atTop, ∀ k, K2N N < k → k ≤ N →
    (k : ℝ) * ((2 : ℝ) ^ (N - k) * (4 / 5) ^ N) * 2 < sigN N / 128 := by
  filter_upwards [eventually_ge_atTop 1,
    ev_poly_geom 10 (r := 24 / 25) (by norm_num) (by norm_num) ((128 * 131072 : ℝ) ^ 2) one_pos]
    with N hN hev
  intro k hk hkN
  set ℓ := Nat.log 2 N with hℓ
  have hNk : N - k ≤ 4 * ℓ + 16 := by unfold K2N at hk; omega
  have h2 : (2 : ℝ) ^ (N - k) ≤ 65536 * (N : ℝ) ^ 4 := by
    have h1 : (2 : ℝ) ^ (N - k) ≤ 2 ^ (4 * ℓ + 16) := pow_le_pow_right₀ (by norm_num) hNk
    have h3 : (2 : ℝ) ^ (4 * ℓ + 16) = 65536 * ((2 : ℝ) ^ ℓ) ^ 4 := by
      rw [pow_add, mul_comm 4 ℓ, pow_mul]; norm_num; ring
    have h4 : ((2 : ℝ) ^ ℓ) ≤ N := by exact_mod_cast two_pow_natLog_le hN
    have h5 : ((2 : ℝ) ^ ℓ) ^ 4 ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) h4 4
    linarith
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hbound : (k : ℝ) * ((2 : ℝ) ^ (N - k) * (4 / 5) ^ N) * 2 ≤
      131072 * (N : ℝ) ^ 5 * (4 / 5) ^ N := by
    have : (0 : ℝ) ≤ (4 / 5) ^ N := by positivity
    calc (k : ℝ) * ((2 : ℝ) ^ (N - k) * (4 / 5) ^ N) * 2
        ≤ (N : ℝ) * (65536 * (N : ℝ) ^ 4 * (4 / 5) ^ N) * 2 := by gcongr
      _ = _ := by ring
  have hlt : 128 * (131072 * (N : ℝ) ^ 5 * (4 / 5) ^ N) < sigN N := by
    rw [sigN]
    apply Real.lt_sqrt_of_sq_lt
    have hsq : ((4 / 5 : ℝ) ^ N) ^ 2 = (24 / 25 : ℝ) ^ N * (2 / 3) ^ N := by
      rw [← pow_mul, mul_comm N 2, pow_mul, ← mul_pow]; norm_num
    have e : (128 * (131072 * (N : ℝ) ^ 5 * (4 / 5) ^ N)) ^ 2 =
        ((128 * 131072 : ℝ) ^ 2 * (N : ℝ) ^ 10 * (24 / 25) ^ N) * (2 / 3) ^ N := by
      rw [show (128 * (131072 * (N : ℝ) ^ 5 * (4 / 5) ^ N)) ^ 2
          = (128 * 131072 : ℝ) ^ 2 * (N : ℝ) ^ 10 * ((4 / 5 : ℝ) ^ N) ^ 2 by ring, hsq]
      ring
    rw [e]
    have : (0 : ℝ) < (2 / 3) ^ N := by positivity
    calc ((128 * 131072 : ℝ) ^ 2 * (N : ℝ) ^ 10 * (24 / 25) ^ N) * (2 / 3) ^ N
        < 1 * (2 / 3) ^ N := mul_lt_mul_of_pos_right hev this
      _ = _ := one_mul _
  linarith

lemma six_mul_add_le_two_pow {n : ℕ} (hn : 6 ≤ n) : 6 * n + 20 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

/-- The thresholds are ordered. -/
theorem eventually_KN_le_K2N : ∀ᶠ N in atTop, 2 ≤ KN N ∧ KN N ≤ K2N N := by
  filter_upwards [eventually_ge_atTop 64] with N hN
  have hℓ : 6 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (le_trans (by norm_num) hN)
  have hm : Nat.log 2 (Nat.log 2 N) ≤ Nat.log 2 N := Nat.log_le_self 2 _
  have h1 := six_mul_add_le_two_pow hℓ
  have h2 := two_pow_natLog_le (by omega : 1 ≤ N)
  unfold KN K2N
  omega

/-! ## The rate -/

lemma three_pow_ge {n : ℕ} (hn : 16 ≤ n) : 2592 * n ^ 3 ≤ 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : 16 * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right _ hn
    have h2 : (n + 1) ^ 3 ≤ 3 * n ^ 3 := by nlinarith
    calc 2592 * (n + 1) ^ 3 ≤ 3 * (2592 * n ^ 3) := by nlinarith
      _ ≤ 3 * 3 ^ n := Nat.mul_le_mul_left _ ih
      _ = 3 ^ (n + 1) := by ring

lemma Dev_nonneg {N : ℕ} (k : ℕ) (hN : 1 ≤ N) : 0 ≤ Dev N k := by
  have := LkN_nonneg' k hN
  have := tauN_pos N
  have := sigN_pos N
  unfold Dev; positivity

/-- Small sizes: the mechanism-level bound is below the rate `rateN N`. -/
theorem eventually_rateB : ∀ᶠ N in atTop, ∀ k ≤ KN N,
    ((2 : ℝ) ^ (2 ^ k) + 2 ^ (k + 1)) * ((k : ℝ) * (8 / Real.log 2) * Dev N k) ≤ rateN N := by
  filter_upwards [eventually_ge_atTop 2,
    ev_poly_geom 7 vkRate_pos.le vkRate_lt_one 1024 one_pos] with N hN hρ
  intro k hk
  set K := KN N with hKdef
  set X : ℕ := 2 ^ K with hX
  have hN1 : 1 ≤ N := by omega
  have hK4 : 4 ≤ K := by simp only [hKdef, KN]; omega
  have hX16 : 16 ≤ X := by
    calc 16 = 2 ^ 4 := rfl
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK4
  have hKX : K + 1 ≤ X := Nat.lt_two_pow_self
  have hkX : k ≤ X := by omega
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hlogX : Real.log N ≤ X := by
    have h1 := log_le_natLog hN1
    have h2 := natLog_succ_le N
    have h3 : 2 * 2 ^ Nat.log 2 (Nat.log 2 N) ≤ X := by
      rw [hX, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by simp only [hKdef, KN]; omega)
    have : ((Nat.log 2 N : ℕ) : ℝ) + 1 ≤ X := by exact_mod_cast h2.trans h3
    linarith
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hk' : (k : ℝ) ≤ X := by exact_mod_cast hkX
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hL1 : 1 ≤ LkN N k := by
    have h2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN'
    have := Real.log_two_gt_d9
    unfold LkN; nlinarith
  have hL6 : LkN N k ≤ 6 * (X : ℝ) ^ 2 := by
    unfold LkN
    nlinarith [mul_le_mul hk' hlogX hl0 (by positivity)]
  have hσ := sigN_pos N
  have hVb := Vbd_le_seven hN1 (le_of_eq_of_le rfl hk) hρ
  have hDev : Dev N k ≤ 18 * LkN N k * sigN N := by
    have hs : Real.sqrt (LkN N k * Vbd N k) ≤ 3 * LkN N k * sigN N := by
      rw [Real.sqrt_le_left (by positivity)]
      have : LkN N k * Vbd N k ≤ LkN N k * (7 * sigN N ^ 2) :=
        mul_le_mul_of_nonneg_left hVb (by linarith)
      nlinarith
    have h3 := sqrt_three_le_two
    have hτ := tauN_le_two_sigN N
    have hs2 : Real.sqrt 3 * sigN N + tauN N ≤ 4 * sigN N := by nlinarith
    have : (4 / 3) * LkN N k * (Real.sqrt 3 * sigN N + tauN N) ≤ (4 / 3) * LkN N k * (4 * sigN N) := by
      gcongr
    unfold Dev; nlinarith
  have hpre : (2 : ℝ) ^ (2 ^ k) + 2 ^ (k + 1) ≤ 2 * 2 ^ X := by
    have e1 : (2 : ℝ) ^ (2 ^ k) ≤ 2 ^ X :=
      pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
    have e2 : (2 : ℝ) ^ (k + 1) ≤ 2 ^ X := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hk8 : (k : ℝ) * (8 / Real.log 2) ≤ X * 12 := by
    have l2 := Real.log_two_gt_d9
    have l2' : 8 / Real.log 2 ≤ 12 := by rw [div_le_iff₀ (by linarith)]; linarith
    exact mul_le_mul hk' l2' (by positivity) (by positivity)
  have hexp : (2 : ℝ) ^ X * (2592 * (X : ℝ) ^ 3) ≤ Real.exp (2 ^ (K + 1)) := by
    have e1 : (2 : ℝ) ^ (K + 1) = X * 2 := by rw [hX]; push_cast; ring
    rw [e1, Real.exp_nat_mul]
    have e6 : (6 : ℝ) ≤ Real.exp 2 := by
      have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have := Real.exp_one_gt_d9
      rw [e2]; nlinarith
    have h3 : (2592 * (X : ℝ) ^ 3) ≤ 3 ^ X := by exact_mod_cast three_pow_ge hX16
    calc (2 : ℝ) ^ X * (2592 * (X : ℝ) ^ 3) ≤ 2 ^ X * 3 ^ X := by gcongr
      _ = 6 ^ X := by rw [← mul_pow]; norm_num
      _ ≤ Real.exp 2 ^ X := pow_le_pow_left₀ (by norm_num) e6 X
  have hD0 := Dev_nonneg k hN1
  unfold rateN
  calc ((2 : ℝ) ^ (2 ^ k) + 2 ^ (k + 1)) * ((k : ℝ) * (8 / Real.log 2) * Dev N k)
      ≤ (2 * 2 ^ X) * ((X * 12) * (18 * (6 * (X : ℝ) ^ 2) * sigN N)) := by
        apply mul_le_mul hpre _ (by positivity) (by positivity)
        apply mul_le_mul hk8 _ hD0 (by positivity)
        calc Dev N k ≤ 18 * LkN N k * sigN N := hDev
          _ ≤ 18 * (6 * (X : ℝ) ^ 2) * sigN N := by gcongr
    _ = ((2 : ℝ) ^ X * (2592 * (X : ℝ) ^ 3)) * sigN N := by ring
    _ ≤ Real.exp (2 ^ (K + 1)) * sigN N := by gcongr

lemma two_hundred_sq_le {n : ℕ} (hn : 16 ≤ n) : 200 * n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
    have e : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [e]; nlinarith

/-- The rate tends to zero: `e^{2^{KN+1}} = e^{O((log N)^2)}` against `σ_N = (2/3)^{N/2}`. -/
theorem tendsto_rateN : Tendsto rateN atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ Nat.log 2 N) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp tendsto_natLog2
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hlim
  · exact mul_nonneg (Real.exp_pos _).le (sigN_pos N).le
  filter_upwards [eventually_ge_atTop (2 ^ 18)] with N hN
  set ℓ := Nat.log 2 N with hℓ
  set m := Nat.log 2 ℓ with hm
  have hℓ18 : 18 ≤ ℓ := Nat.le_log_of_pow_le (by norm_num) hN
  have hN1 : 1 ≤ N := le_trans Nat.one_le_two_pow hN
  have h2m : 2 ^ m ≤ ℓ := Nat.pow_log_le_self 2 (by omega)
  have hA : (2 : ℝ) ^ (KN N + 1) ≤ 32 * (ℓ : ℝ) ^ 2 := by
    have e : (2 : ℝ) ^ (KN N + 1) = 32 * ((2 : ℝ) ^ m) ^ 2 := by
      show (2 : ℝ) ^ (2 * m + 4 + 1) = _
      rw [pow_add, pow_add, mul_comm 2 m, pow_mul]; ring
    rw [e]
    have : ((2 : ℝ) ^ m) ≤ ℓ := by exact_mod_cast h2m
    have : (0 : ℝ) ≤ 2 ^ m := by positivity
    nlinarith
  have hE : Real.exp (2 ^ (KN N + 1)) ^ 2 ≤ (3 : ℝ) ^ (64 * ℓ ^ 2) := by
    rw [← Real.exp_nat_mul]
    calc Real.exp (((2 : ℕ) : ℝ) * 2 ^ (KN N + 1)) ≤ Real.exp ((64 * ℓ ^ 2 : ℕ) : ℝ) := by
          apply Real.exp_le_exp.2; push_cast; linarith
      _ = Real.exp 1 ^ (64 * ℓ ^ 2) := (Real.exp_one_pow _).symm
      _ ≤ 3 ^ (64 * ℓ ^ 2) :=
          pow_le_pow_left₀ (Real.exp_pos 1).le (by have := Real.exp_one_lt_d9; linarith) _
  have hS : (2 / 3 : ℝ) ^ N ≤ ((2 / 3 : ℝ) ^ 200) ^ (ℓ ^ 2) := by
    rw [← pow_mul]
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    exact (two_hundred_sq_le (by omega)).trans (two_pow_natLog_le hN1)
  unfold rateN sigN
  apply mul_sqrt_le_of_sq (Real.exp_pos _).le (by positivity)
  have hℓsq : ℓ ≤ ℓ ^ 2 := by nlinarith
  calc Real.exp (2 ^ (KN N + 1)) ^ 2 * (2 / 3 : ℝ) ^ N
      ≤ (3 : ℝ) ^ (64 * ℓ ^ 2) * ((2 / 3 : ℝ) ^ 200) ^ (ℓ ^ 2) :=
        mul_le_mul hE hS (by positivity) (by positivity)
    _ = ((3 : ℝ) ^ 64 * (2 / 3 : ℝ) ^ 200) ^ (ℓ ^ 2) := by rw [mul_pow, ← pow_mul, ← pow_mul]
    _ ≤ (1 / 4 : ℝ) ^ (ℓ ^ 2) := pow_le_pow_left₀ (by positivity) (by norm_num) _
    _ ≤ (1 / 4 : ℝ) ^ ℓ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hℓsq
    _ = ((1 / 2 : ℝ) ^ ℓ) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

end Census
end IIT
