/-
Census, Theorem E: the cause side of an ordered `k`-set through its field.

For an injection `e : Fin k → Fin N` with image `S = bg_U e`, every state `x` has a background
`te_bg he x` and a pattern `te_pat he x : Fin (2^k)` (bit `q` is `x (e q)`).  With the field
`ξ = te_xi he w` of `ThmELind`:
* `Num w S S x (e i) = a_k + σ_N ξ(i, te_pat x)` (`te_Num_S`), and every conditioned numerator
  `Num w S (S \ P) x (e i)` is `a_k + σ_N` times the average of `ξ(i, ·)` over the patterns agreeing
  with `te_pat x` off `P` (`te_Num_Y`);
* if `|ξ| ≤ M` then every numerator of `S` is within `σ_N M` of `a_k` (`te_lev`);
* the linear forms of `UpperReduce` are the certificate forms: `ur_xi = ∑_i ξ(i, ·)`
  (`te_urxi`), `ur_F θ x σ_N = cd_F k C (te_pat x) ξ` for the profile table `C` of `θ` along `e`
  (`te_urF`), and `sysCutCount θ = cd_cc k C` (`te_cc`);
* translating patterns by `u₀` (`te_sh`) moves the forms at `u₀` to the forms at `0`;
* the near-argmax and near-minimiser conditions of `ur_upper_reduce` place the shifted field in the
  region `cd_region k C ε y` of `CertDataBase` (`te_region`).
-/
import IIT.Census.ThmELind
import IIT.Census.UpperReduce
import IIT.Census.CertDataClass

namespace IIT
namespace Census

open MeasureTheory Finset

noncomputable section

variable {N k : ℕ}

/-! ### Background and pattern of a state -/

section Pattern

variable {e : Fin k → Fin N} (he : Function.Injective e)

/-- The background of a state (its bits off the image of `e`). -/
def te_bg (x : State N) : bg_Bg e := ((bg_sg he).symm x).1

/-- The pattern of a state (bit `q` is `x (e q)`). -/
def te_pat (x : State N) : Fin (2 ^ k) := ((bg_sg he).symm x).2

lemma te_sg_apply (q : bg_Bg e × Fin (2 ^ k)) : bg_sg he q = bg_row e (bg_bits k) q.1 q.2 := by
  simp [bg_sg]

lemma te_row_self (x : State N) : bg_row e (bg_bits k) (te_bg he x) (te_pat he x) = x := by
  have h := te_sg_apply he ((bg_sg he).symm x)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

lemma te_bit (x : State N) (q : Fin k) : x (e q) = (te_pat he x : ℕ).testBit q := by
  conv_lhs => rw [← te_row_self he x]
  rw [bg_row_E (bg_bits k) he]
  rfl

lemma te_out (x : State N) {j : Fin N} (hj : j ∉ bg_U e) : x j = te_bg he x ⟨j, hj⟩ := by
  conv_lhs => rw [← te_row_self he x]
  simp only [bg_row, dif_neg hj]

lemma te_pat_row (β : bg_Bg e) (u : Fin (2 ^ k)) : te_pat he (bg_row e (bg_bits k) β u) = u := by
  rw [te_pat, ← te_sg_apply he (β, u), Equiv.symm_apply_apply]

lemma te_pat_pst (u : Fin (2 ^ k)) : te_pat he (bg_pst e u) = u := te_pat_row he _ u

lemma te_pst_agree (x : State N) : ∀ j ∈ bg_U e, bg_pst e (te_pat he x) j = x j := by
  intro j hj
  obtain ⟨g, rfl⟩ := bg_mem_U e hj
  rw [bg_pst_E he, te_bit he x g]
  rfl

lemma te_mem_U (i : Fin k) : e i ∈ bg_U e := bg_E_mem e i

end Pattern

/-! ### Numerators through the field -/

lemma te_Num_congr (w : Param N) (S Y : Finset (Fin N)) {t t' : State N}
    (h : ∀ j ∈ S, t j = t' j) (i : Fin N) : Num w S Y t i = Num w S Y t' i := by
  unfold Num meanW
  simp_rw [merge_congr (w := _) h]

section Field

variable {e : Fin k → Fin N} (he : Function.Injective e)

lemma te_Num_S (w : Param N) (x : State N) (i : Fin k) :
    Num w (bg_U e) (bg_U e) x (e i) =
      bg_ak k + sigN N * te_xi he w (cd_idx k i (te_pat he x)) := by
  have h := te_xi_apply he w (cd_idx k i (te_pat he x))
  rw [gg_pat_idx, gg_unit_idx] at h
  rw [h, te_Num_congr w _ _ (te_pst_agree he x)]
  have := sigN_pos N
  field_simp
  ring

/-- Summing over the states agreeing with `t` off `P` is summing over the agreeing patterns. -/
lemma te_sum_agree {P : Finset (Fin N)} (hP : P ⊆ bg_U e) (t : State N) (g : Fin (2 ^ k) → ℝ) :
    ∑ t' ∈ agree ((bg_U e \ P) ∪ (bg_U e)ᶜ) t, g (te_pat he t') =
      ∑ u : Fin (2 ^ k), if (∀ q : Fin k, e q ∉ P → (u : ℕ).testBit q =
        (te_pat he t : ℕ).testBit q) then g u else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (te_pat he) (fun u => bg_row e (bg_bits k) (te_bg he t) u) ?_ ?_ ?_ ?_
    (fun _ _ => rfl)
  · intro t' ht'
    simp only [Finset.mem_coe, mem_agree, mem_union, mem_sdiff, mem_compl] at ht'
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    intro q hq
    rw [← te_bit he t' q, ← te_bit he t q]
    exact ht' (e q) (Or.inl ⟨te_mem_U q, hq⟩)
  · intro u hu
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [Finset.mem_coe, mem_agree, mem_union, mem_sdiff, mem_compl]
    rintro j (⟨hjU, hjP⟩ | hjU)
    · obtain ⟨q, rfl⟩ := bg_mem_U e hjU
      rw [bg_row_E (bg_bits k) he, te_bit he t q]
      exact hu q hjP
    · rw [te_out he t hjU]
      simp only [bg_row, dif_neg hjU]
  · intro t' ht'
    simp only [Finset.mem_coe, mem_agree, mem_union, mem_sdiff, mem_compl] at ht'
    have hbg : te_bg he t = te_bg he t' := by
      funext ⟨j, hj⟩
      rw [← te_out he t hj, ← te_out he t' hj]
      exact (ht' j (Or.inr hj)).symm
    rw [hbg, te_row_self]
  · intro u _
    exact te_pat_row he _ u

lemma te_card_sdiff_union {P : Finset (Fin N)} (hP : P ⊆ bg_U e) :
    ((bg_U e \ P) ∪ (bg_U e)ᶜ).card = N - P.card := by
  rw [card_union_of_disjoint (disjoint_compl_right.mono_left sdiff_subset), card_sdiff_of_subset hP,
    card_compl, Fintype.card_fin]
  have h1 := card_le_card hP
  have h2 : (bg_U e).card ≤ N := by simpa using card_le_univ (bg_U e)
  omega

/-- A conditioned numerator is `a_k + σ_N` times the average of the field over the agreeing
patterns. -/
lemma te_Num_Y (w : Param N) {P : Finset (Fin N)} (hP : P ⊆ bg_U e) (t : State N) (i : Fin k) :
    Num w (bg_U e) (bg_U e \ P) t (e i) = bg_ak k + sigN N *
      ((∑ u : Fin (2 ^ k), if (∀ q : Fin k, e q ∉ P → (u : ℕ).testBit q =
        (te_pat he t : ℕ).testBit q) then te_xi he w (cd_idx k i u) else 0) / 2 ^ P.card) := by
  rw [Num_eq_avg]
  have hU : bg_U e ∪ (bg_U e)ᶜ = univ := union_compl _
  rw [show (bg_U e \ P) ∪ (bg_U e)ᶜ = (bg_U e \ P) ∪ (bg_U e)ᶜ from rfl]
  simp_rw [te_Num_S he w _ i]
  rw [te_sum_agree he hP t (fun u => bg_ak k + sigN N * te_xi he w (cd_idx k i u))]
  have hcnt := te_sum_agree he hP t (fun _ => (1 : ℝ))
  simp only [sum_const, nsmul_eq_mul, mul_one] at hcnt
  rw [card_agree, te_card_sdiff_union hP] at hcnt
  have hNP : N - (N - P.card) = P.card := by
    have : P.card ≤ N := by simpa using card_le_univ P
    omega
  rw [hNP] at hcnt
  have hsplit : ∀ u : Fin (2 ^ k),
      (if (∀ q : Fin k, e q ∉ P → (u : ℕ).testBit q = (te_pat he t : ℕ).testBit q)
        then bg_ak k + sigN N * te_xi he w (cd_idx k i u) else 0) =
      bg_ak k * (if (∀ q : Fin k, e q ∉ P → (u : ℕ).testBit q = (te_pat he t : ℕ).testBit q)
        then 1 else 0) + sigN N * (if (∀ q : Fin k, e q ∉ P → (u : ℕ).testBit q =
          (te_pat he t : ℕ).testBit q) then te_xi he w (cd_idx k i u) else 0) := by
    intro u; split_ifs <;> ring
  rw [sum_congr rfl fun u _ => hsplit u, sum_add_distrib, ← mul_sum, ← mul_sum, ← hcnt,
    card_sdiff_of_subset hP]
  have hPc := card_le_card hP
  rw [show (bg_U e).card - ((bg_U e).card - P.card) = P.card by omega]
  push_cast
  have h2 : (0 : ℝ) < 2 ^ P.card := by positivity
  field_simp

/-- If the field is bounded by `M`, every numerator of `S` is within `σ_N M` of `a_k`. -/
lemma te_lev (w : Param N) {M : ℝ} (hM : ∀ p, |te_xi he w p| ≤ M) :
    ∀ Y ⊆ bg_U e, ∀ t, ∀ j ∈ bg_U e, |Num w (bg_U e) Y t j - bg_ak k| ≤ sigN N * M := by
  intro Y hY t j hj
  obtain ⟨i, rfl⟩ := bg_mem_U e hj
  have hσ := sigN_pos N
  set P := bg_U e \ Y with hPdef
  have hPU : P ⊆ bg_U e := sdiff_subset
  have hYP : Y = bg_U e \ P := by rw [hPdef, Finset.sdiff_sdiff_eq_self hY]
  rw [hYP, te_Num_Y he w hPU t i, add_sub_cancel_left, abs_mul, abs_of_pos hσ]
  refine mul_le_mul_of_nonneg_left ?_ hσ.le
  have hcnt := te_sum_agree he hPU t (fun _ => (1 : ℝ))
  simp only [sum_const, nsmul_eq_mul, mul_one] at hcnt
  rw [card_agree, te_card_sdiff_union hPU] at hcnt
  have hNP : N - (N - P.card) = P.card := by
    have : P.card ≤ N := by simpa using card_le_univ P
    omega
  rw [hNP] at hcnt
  have h2 : (0 : ℝ) < 2 ^ P.card := by positivity
  rw [abs_div, abs_of_pos h2, div_le_iff₀ h2]
  push_cast at hcnt
  rw [hcnt, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun u _ => ?_)
  split_ifs
  · rw [mul_one]; exact hM _
  · simp only [abs_zero, mul_zero, le_refl]

end Field

/-! ### The forms of `UpperReduce` as certificate forms -/

section Forms

variable {e : Fin k → Fin N} (he : Function.Injective e)

lemma te_sum_U {β : Type*} [AddCommMonoid β] (he : Function.Injective e) (f : Fin N → β) :
    ∑ j ∈ bg_U e, f j = ∑ i : Fin k, f (e i) := by
  rw [bg_U, sum_image fun a _ b _ h => he h]

lemma te_card_profile (he : Function.Injective e) {P : Finset (Fin N)} (hP : P ⊆ bg_U e) (C : List (List Bool)) (i : Fin k)
    (hC : ∀ j : Fin k, e j ∈ P ↔ cd_at C i j = true) : cd_card k C i = P.card := by
  rw [cd_card, cd_cnt_eq]
  have hPi : P = (univ.filter fun j : Fin k => cd_at C i j = true).image e := by
    ext x
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · intro hx
      obtain ⟨j, rfl⟩ := bg_mem_U e (hP hx)
      exact ⟨j, (hC j).1 hx, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact (hC j).2 hj
  rw [hPi, card_image_of_injective _ he]

lemma te_agree_iff {P : Finset (Fin N)} (C : List (List Bool)) (i : Fin k)
    (hC : ∀ j : Fin k, e j ∈ P ↔ cd_at C i j = true) (u t : Fin (2 ^ k)) :
    cd_agree k (cd_at C i) u t = true ↔
      ∀ q : Fin k, e q ∉ P → (u : ℕ).testBit q = (t : ℕ).testBit q := by
  rw [cd_agree_iff]
  constructor
  · intro h q hq
    exact h q q.2 (by rw [← Bool.not_eq_true, ← hC q]; exact hq)
  · intro h q hqk hq
    exact h ⟨q, hqk⟩ (by rw [hC ⟨q, hqk⟩, hq]; simp)

lemma te_urxi (w : Param N) (t : State N) :
    ur_xi w (bg_U e) (bg_ak k) (sigN N) t = ∑ i : Fin k, te_xi he w (cd_idx k i (te_pat he t)) := by
  unfold ur_xi
  rw [te_sum_U he (fun j => Num w (bg_U e) (bg_U e) t j - bg_ak k)]
  simp_rw [te_Num_S he w t, add_sub_cancel_left, ← mul_sum]
  have := sigN_pos N
  field_simp

lemma te_urF (w : Param N) (θ : SysPartition N (bg_U e)) (t : State N) (C : List (List Bool))
    (hC : ∀ i j : Fin k, e j ∈ profile θ (e i) ↔ cd_at C i j = true) :
    ur_F w θ t (sigN N) = cd_F k C (te_pat he t) (te_xi he w) := by
  rw [cd_F_eq, ur_F, te_sum_U he (fun j => ur_D w θ t j)]
  have hσ := sigN_pos N
  rw [div_eq_iff hσ.ne', sum_mul]
  refine sum_congr rfl fun i _ => ?_
  have hP : profile θ (e i) ⊆ bg_U e := prof_profile_subset θ (e i)
  rw [ur_D, te_Num_S he w t i, te_Num_Y he w hP t i, te_card_profile he hP C i (hC i)]
  have hsum : (∑ u : Fin (2 ^ k), if (∀ q : Fin k, e q ∉ profile θ (e i) → (u : ℕ).testBit q =
      (te_pat he t : ℕ).testBit q) then te_xi he w (cd_idx k i u) else 0) =
      ∑ u : Fin (2 ^ k), if cd_agree k (cd_at C i) u (te_pat he t) then
        te_xi he w (cd_idx k i u) else 0 := by
    refine sum_congr rfl fun u _ => ?_
    by_cases h : cd_agree k (cd_at C i) u (te_pat he t) = true
    · rw [if_pos h, if_pos ((te_agree_iff C i (hC i) u _).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((te_agree_iff C i (hC i) u _).2 h'))]
  rw [hsum]
  ring

lemma te_cc (he : Function.Injective e) (θ : SysPartition N (bg_U e)) (C : List (List Bool))
    (hC : ∀ i j : Fin k, e j ∈ profile θ (e i) ↔ cd_at C i j = true) :
    sysCutCount θ = cd_cc k C := by
  rw [sysCutCount_eq_sum_profile, te_sum_U he (fun j => (profile θ j).card), cd_cc, cd_nsumN_eq,
    ← Fin.sum_univ_eq_sum_range]
  exact sum_congr rfl fun i _ =>
    (te_card_profile he (prof_profile_subset θ (e i)) C i (hC i)).symm

end Forms

/-! ### Pattern translations -/

section Shift

/-- The zero pattern. -/
def te_z0 (k : ℕ) : Fin (2 ^ k) := ⟨0, by positivity⟩

/-- Translation of the patterns by `u₀`. -/
def te_sh (u0 : Fin (2 ^ k)) (ξ : Fin (k * 2 ^ k) → ℝ) : Fin (k * 2 ^ k) → ℝ :=
  fun p => ξ (gg_relabel k (Equiv.refl _) (gg_xor k u0) p)

lemma te_sh_idx (u0 : Fin (2 ^ k)) (ξ : Fin (k * 2 ^ k) → ℝ) (i : Fin k) (u : Fin (2 ^ k)) :
    te_sh u0 ξ (cd_idx k i u) = ξ (cd_idx k i (gg_xor k u0 u)) := by
  simp [te_sh, gg_relabel, cd_idx]

lemma te_xor_z0 (u0 : Fin (2 ^ k)) : gg_xor k u0 (te_z0 k) = u0 :=
  Fin.ext (by simp [gg_xor_val, te_z0])

lemma te_agree_xor (r : ℕ → Bool) (u0 v : Fin (2 ^ k)) :
    cd_agree k r (gg_xor k u0 v) (te_z0 k) = cd_agree k r v u0 := by
  rw [Bool.eq_iff_iff, cd_agree_iff, cd_agree_iff]
  refine forall_congr' fun q => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [gg_xor_val, Nat.testBit_xor]
  simp only [te_z0, Nat.zero_testBit]
  cases (v : ℕ).testBit q <;> cases (u0 : ℕ).testBit q <;> simp

lemma te_F_sh (C : List (List Bool)) (u0 : Fin (2 ^ k)) (ξ : Fin (k * 2 ^ k) → ℝ) :
    cd_F k C 0 (te_sh u0 ξ) = cd_F k C u0 ξ := by
  have h0 := cd_F_eq k C (te_z0 k) (te_sh u0 ξ)
  rw [show ((te_z0 k : Fin (2 ^ k)) : ℕ) = 0 from rfl] at h0
  rw [h0, cd_F_eq]
  refine sum_congr rfl fun i _ => ?_
  rw [te_sh_idx, te_xor_z0]
  congr 2
  have hf : ∀ u : Fin (2 ^ k), (if cd_agree k (cd_at C i) u 0 then
      te_sh u0 ξ (cd_idx k i u) else 0) =
      (fun v : Fin (2 ^ k) => if cd_agree k (cd_at C i) v u0 then ξ (cd_idx k i v) else 0)
        (gg_xor k u0 u) := by
    intro u
    have hinv : gg_xor k u0 (gg_xor k u0 u) = u :=
      Fin.ext (by simp [gg_xor_val])
    simp only
    rw [te_sh_idx, ← te_agree_xor (cd_at C i) u0 (gg_xor k u0 u), hinv]
    rfl
  rw [Finset.sum_congr rfl fun u _ => hf u]
  exact Equiv.sum_comp (gg_xor k u0)
    (fun v : Fin (2 ^ k) => if cd_agree k (cd_at C i) v u0 then ξ (cd_idx k i v) else 0)

lemma te_argc_sh (u0 t : Fin (2 ^ k)) (ξ : Fin (k * 2 ^ k) → ℝ) :
    cd_lin k (cd_argc k t) (te_sh u0 ξ) =
      ∑ i : Fin k, (ξ (cd_idx k i u0) - ξ (cd_idx k i (gg_xor k u0 t))) := by
  rw [cd_lin_argc]
  refine sum_congr rfl fun i _ => ?_
  have h0 : gg_xor k u0 ⟨0, by positivity⟩ = u0 := te_xor_z0 u0
  rw [te_sh_idx, te_sh_idx, h0]

end Shift

/-! ### The region -/

/-- **Region of the shifted field.** At a near-argmax pattern `t` and a near-minimiser `θ` with
profile table `C` along `e`, the field translated by the pattern of `t` lies in the region of `C`
with slack `ε` at level `y ≤ F_θ(t)`. -/
theorem te_region (e : Fin k ↪ Fin N) (w : Param N) (θ : SysPartition N (bg_U e))
    (t : State N) (C : List (List Bool))
    (hC : ∀ i j : Fin k, e j ∈ profile θ (e i) ↔ cd_at C i j = true) {ε y : ℝ}
    (hmax : ∀ t', ur_xi w (bg_U e) (bg_ak k) (sigN N) t' ≤
      ur_xi w (bg_U e) (bg_ak k) (sigN N) t + ε)
    (hmin : ∀ θ' : SysPartition N (bg_U e), ur_F w θ t (sigN N) / (sysCutCount θ : ℝ) ≤
      ur_F w θ' t (sigN N) / (sysCutCount θ' : ℝ) + ε)
    (hy : y ≤ ur_F w θ t (sigN N)) :
    cd_region k C ε y (te_sh (te_pat e.injective t) (te_xi e.injective w)) := by
  have he := e.injective
  set u0 := te_pat he t with hu0
  set ξ := te_xi he w with hξ
  have hS : ∀ x, x ∈ bg_U e ↔ ∃ i, e i = x := by
    intro x
    simp only [bg_U, mem_image, mem_univ, true_and]
  refine ⟨fun t' ht0 ht1 => ?_, fun g δ hv => ?_, ?_⟩
  · have h := te_argc_sh u0 ⟨t', ht1⟩ ξ
    rw [show ((⟨t', ht1⟩ : Fin (2 ^ k)) : ℕ) = t' from rfl] at h
    rw [h, sum_sub_distrib]
    have hm := hmax (bg_pst e (gg_xor k u0 ⟨t', ht1⟩))
    rw [te_urxi he, te_urxi he, te_pat_pst he] at hm
    linarith
  · obtain ⟨θ', hθ'⟩ := cd_realize e g δ hS hv
    have hm := hmin θ'
    rw [te_urF he w θ t C hC, te_urF he w θ' t _ hθ', te_cc he θ C hC, te_cc he θ' _ hθ'] at hm
    rw [te_F_sh, te_F_sh]
    linarith
  · rw [te_F_sh, ← te_urF he w θ t C hC]
    exact hy

end

end Census
end IIT
