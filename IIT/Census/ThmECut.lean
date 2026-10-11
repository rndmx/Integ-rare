/-
Census, Theorem E for sizes `k ≥ 6` through the single cut.

For a `k`-set `S` and `a ∈ S`, the partition `te_theta0` into `{a}` (inputs severed) and `S \ {a}`
(outputs severed) cuts only the inputs of `a` from the rest: its profile is `S \ {a}` at `a` and
empty elsewhere, and its normaliser is `k - 1`.  Every normaliser is at most `k (k - 1)`.  Hence at a
near-minimiser `θ`, `F_{θ₀}(t) ≥ F_θ(t)/k - (k - 1) e_N ≥ y_N / k - (k - 1) e_N`, and
`F_{θ₀}(t) = ⟨v_u, ξ⟩` for the explicit functional `te_v1 u` (`u` the pattern of `t`), whose
Gaussian variance is `(c₁ + c₂)(1 - 2^{1-k}) ≤ 7/80` (`te_quad_v1`).  With the half-space bound and
a union over the `≤ N^k` orderings and `2^k` patterns: for every `k ≥ 6`, with probability tending
to one no `k`-set has `φ_s > 0.28 √(ln N) σ_N` (`te_thmE_cut`).
-/
import IIT.Census.ThmECert

namespace IIT
namespace Census

open MeasureTheory Finset Filter Topology ENNReal

noncomputable section

variable {N k : ℕ}

/-! ### The single cut -/

section Theta0

variable {S : Finset (Fin N)} {a : Fin N}

lemma te_erase_ne (ha : a ∈ S) : S.erase a ≠ {a} := by
  intro h
  have : a ∈ S.erase a := by rw [h]; exact mem_singleton_self a
  exact (notMem_erase a S) this

/-- The partition `{a} | S \ {a}`, inputs of `a` severed. -/
def te_theta0 (ha : a ∈ S) (h2 : 2 ≤ S.card) : SysPartition N S where
  parts := {{a}, S.erase a}
  dir := fun p => if p = {a} then Dir.inputs else Dir.outputs
  parts_nonempty := by
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact singleton_nonempty a
    · rw [← card_pos, card_erase_of_mem ha]; omega
  parts_subset := by
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact singleton_subset_iff.2 ha
    · exact erase_subset a S
  parts_disjoint := by
    intro p hp q hq hpq
    simp only [mem_insert, mem_singleton] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd rfl hpq
    · rw [disjoint_singleton_left]; exact notMem_erase a S
    · rw [disjoint_singleton_right]; exact notMem_erase a S
    · exact absurd rfl hpq
  parts_cover := by
    intro i hi
    by_cases h : i = a
    · exact ⟨{a}, by simp, by rw [h]; exact mem_singleton_self a⟩
    · exact ⟨S.erase a, by simp, mem_erase.2 ⟨h, hi⟩⟩
  two_le := by
    rw [card_insert_of_notMem (by simp only [mem_singleton]; exact (te_erase_ne ha).symm),
      card_singleton]

lemma te_theta0_mem_a (ha : a ∈ S) (h2 : 2 ≤ S.card) : {a} ∈ (te_theta0 ha h2).parts := by
  simp [te_theta0]

lemma te_theta0_mem_b (ha : a ∈ S) (h2 : 2 ≤ S.card) : S.erase a ∈ (te_theta0 ha h2).parts := by
  simp [te_theta0]

lemma te_theta0_partOf_a (ha : a ∈ S) (h2 : 2 ≤ S.card) : (te_theta0 ha h2).partOf a = {a} :=
  (te_theta0 ha h2).partOf_eq (te_theta0_mem_a ha h2) (mem_singleton_self a)

lemma te_theta0_partOf_b (ha : a ∈ S) (h2 : 2 ≤ S.card) {x : Fin N} (hx : x ∈ S) (hxa : x ≠ a) :
    (te_theta0 ha h2).partOf x = S.erase a :=
  (te_theta0 ha h2).partOf_eq (te_theta0_mem_b ha h2) (mem_erase.2 ⟨hxa, hx⟩)

lemma te_theta0_dir_a (ha : a ∈ S) (h2 : 2 ≤ S.card) : (te_theta0 ha h2).dir {a} = Dir.inputs := by
  simp [te_theta0]

lemma te_theta0_dir_b (ha : a ∈ S) (h2 : 2 ≤ S.card) :
    (te_theta0 ha h2).dir (S.erase a) = Dir.outputs := by
  simp [te_theta0, te_erase_ne ha]

lemma te_theta0_prof_a (ha : a ∈ S) (h2 : 2 ≤ S.card) : profile (te_theta0 ha h2) a = S.erase a := by
  ext x
  constructor
  · intro hx
    have hxS := prof_profile_subset (te_theta0 ha h2) a hx
    unfold profile at hx
    rw [cd_mem_cutSet _ (by rw [te_theta0_partOf_a]; exact te_theta0_mem_a ha h2) hxS,
      te_theta0_partOf_a] at hx
    exact mem_erase.2 ⟨fun h => hx.1 (h ▸ mem_singleton_self a), hxS⟩
  · intro hx
    obtain ⟨hxa, hxS⟩ := mem_erase.1 hx
    unfold profile
    rw [cd_mem_cutSet _ (by rw [te_theta0_partOf_a]; exact te_theta0_mem_a ha h2) hxS,
      te_theta0_partOf_a, te_theta0_dir_a]
    exact ⟨by simp [hxa], Or.inl (by simp)⟩

lemma te_theta0_prof_b (ha : a ∈ S) (h2 : 2 ≤ S.card) {y : Fin N} (hy : y ∈ S) (hya : y ≠ a) :
    profile (te_theta0 ha h2) y = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have hxS := prof_profile_subset (te_theta0 ha h2) y hx
  unfold profile at hx
  rw [cd_mem_cutSet _ (by rw [te_theta0_partOf_b ha h2 hy hya]; exact te_theta0_mem_b ha h2) hxS,
    te_theta0_partOf_b ha h2 hy hya, te_theta0_dir_b] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hxa : x = a := by
    by_contra h; exact hx1 (mem_erase.2 ⟨h, hxS⟩)
  subst hxa
  rw [te_theta0_partOf_a, te_theta0_dir_a] at hx2
  simp at hx2

lemma te_theta0_cc (ha : a ∈ S) (h2 : 2 ≤ S.card) :
    (sysCutCount (te_theta0 ha h2) : ℝ) = S.card - 1 := by
  rw [sysCutCount_eq_sum_profile, ← add_sum_erase S _ ha, te_theta0_prof_a,
    sum_eq_zero fun y hy => by
      rw [te_theta0_prof_b ha h2 (mem_of_mem_erase hy) (ne_of_mem_erase hy), card_empty],
    add_zero, card_erase_of_mem ha]
  have : 1 ≤ S.card := by omega
  push_cast [this]
  ring

end Theta0

/-- Every normaliser is at most `k (k - 1)`. -/
lemma te_cc_le {S : Finset (Fin N)} (θ : SysPartition N S) :
    (sysCutCount θ : ℝ) ≤ S.card * (S.card - 1) := by
  rw [sysCutCount_eq_sum_profile]
  have h : ∀ j ∈ S, (profile θ j).card ≤ S.card - 1 := by
    intro j hj
    have hsub : profile θ j ⊆ S.erase j := by
      intro x hx
      have hxS := prof_profile_subset θ j hx
      have hm := prof_partOf_mem θ hj
      unfold profile at hx
      rw [cd_mem_cutSet θ hm.1 hxS] at hx
      exact mem_erase.2 ⟨fun h => hx.1 (h ▸ hm.2), hxS⟩
    exact (card_le_card hsub).trans (by rw [card_erase_of_mem hj])
  have hS1 : 1 ≤ S.card ∨ S = ∅ := by
    rcases S.eq_empty_or_nonempty with h | h
    · exact Or.inr h
    · exact Or.inl (card_pos.2 h)
  rcases hS1 with h1 | h1
  · have := sum_le_card_nsmul S (fun j => (profile θ j).card) (S.card - 1) h
    rw [smul_eq_mul] at this
    have hc : ((∑ j ∈ S, (profile θ j).card : ℕ) : ℝ) ≤ ((S.card * (S.card - 1) : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast [h1] at hc
    push_cast
    exact hc
  · subst h1; simp

/-! ### The functional of the single cut -/

/-- `h = 2^{-(k-1)}`. -/
def te_h (k : ℕ) : ℝ := ((2 : ℝ) ^ (k - 1))⁻¹

/-- The coefficients of `F_{θ₀}` at the pattern `u`. -/
def te_v1 (k : ℕ) (u : Fin (2 ^ k)) (p : Fin (k * 2 ^ k)) : ℝ :=
  if (gg_unit k p : ℕ) = 0 then
    (if gg_pat k p = u then 1 else 0) -
      (if (gg_pat k p : ℕ).testBit 0 = (u : ℕ).testBit 0 then te_h k else 0)
  else 0

lemma te_sum_idx {β : Type*} [AddCommMonoid β] (f : Fin (k * 2 ^ k) → β) :
    ∑ p, f p = ∑ i : Fin k, ∑ u : Fin (2 ^ k), f (cd_idx k i u) := by
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin k × Fin (2 ^ k) ≃ _), Fintype.sum_prod_type]
  rfl

lemma te_v1_idx (u : Fin (2 ^ k)) (i : Fin k) (t : Fin (2 ^ k)) :
    te_v1 k u (cd_idx k i t) = if (i : ℕ) = 0 then
      (if t = u then 1 else 0) - (if (t : ℕ).testBit 0 = (u : ℕ).testBit 0 then te_h k else 0)
    else 0 := by
  rw [te_v1, gg_unit_idx, gg_pat_idx]

/-- `∑_p v_p f(p)` only sees unit `0`. -/
lemma te_sum_v1 (hk : 1 ≤ k) (u : Fin (2 ^ k)) (f : Fin (k * 2 ^ k) → ℝ) :
    ∑ p, te_v1 k u p * f p = ∑ t : Fin (2 ^ k), ((if t = u then 1 else 0) -
      (if (t : ℕ).testBit 0 = (u : ℕ).testBit 0 then te_h k else 0)) * f (cd_idx k ⟨0, hk⟩ t) := by
  rw [te_sum_idx, sum_eq_single ⟨0, hk⟩]
  · refine sum_congr rfl fun t _ => ?_
    rw [te_v1_idx]; simp
  · intro i _ hi
    refine sum_eq_zero fun t _ => ?_
    rw [te_v1_idx, if_neg (fun h => hi (Fin.ext h)), zero_mul]
  · intro h; exact absurd (mem_univ _) h

/-- Half of the patterns have a given bit `0`. -/
lemma te_count_bit0 (hk : 1 ≤ k) (u : Fin (2 ^ k)) :
    ∑ t : Fin (2 ^ k), (if (t : ℕ).testBit 0 = (u : ℕ).testBit 0 then (1 : ℝ) else 0) =
      2 ^ (k - 1) := by
  have h2 : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
  set one : Fin (2 ^ k) := ⟨1, h2⟩
  set b := (u : ℕ).testBit 0
  have hflip : ∀ t : Fin (2 ^ k), ((gg_xor k one t : ℕ)).testBit 0 = !(t : ℕ).testBit 0 := by
    intro t
    rw [gg_xor_val, Nat.testBit_xor]
    simp [one]
  have hA : ∑ t : Fin (2 ^ k), (if (t : ℕ).testBit 0 = b then (1 : ℝ) else 0) =
      ∑ t : Fin (2 ^ k), (if (t : ℕ).testBit 0 = !b then (1 : ℝ) else 0) := by
    rw [← Equiv.sum_comp (gg_xor k one)]
    refine sum_congr rfl fun t _ => ?_
    rw [hflip]
    cases (t : ℕ).testBit 0 <;> cases b <;> simp
  have hB : ∑ t : Fin (2 ^ k), (if (t : ℕ).testBit 0 = b then (1 : ℝ) else 0) +
      ∑ t : Fin (2 ^ k), (if (t : ℕ).testBit 0 = !b then (1 : ℝ) else 0) = 2 ^ k := by
    rw [← sum_add_distrib]
    have : ∀ t : Fin (2 ^ k), (if (t : ℕ).testBit 0 = b then (1 : ℝ) else 0) +
        (if (t : ℕ).testBit 0 = !b then (1 : ℝ) else 0) = 1 := by
      intro t; cases (t : ℕ).testBit 0 <;> cases b <;> simp
    rw [Finset.sum_congr rfl fun t _ => this t, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast; ring
  have hk2 : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  linarith

lemma te_h_mul (hk : 1 ≤ k) : te_h k * 2 ^ (k - 1) = 1 := by
  unfold te_h; field_simp

lemma te_h_le (hk : 2 ≤ k) : te_h k ≤ 1 / 2 := by
  unfold te_h
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  calc (1 / 2 : ℝ)⁻¹ = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (k - 1) := pow_le_pow_right₀ (by norm_num) (by omega)

/-- **Variance of the single cut**: `vᵀ C_k v = (c₁ + c₂)(1 - 2^{1-k})`. -/
lemma te_quad_v1 (hk : 1 ≤ k) (u : Fin (2 ^ k)) :
    gg_quad (gg_C k) (te_v1 k u) = (gg_c1 k + gg_c2 k) * (1 - te_h k) := by
  have hcnt := te_count_bit0 hk u
  have hh := te_h_mul hk
  set z0 : Fin k := ⟨0, hk⟩
  set w : Fin (2 ^ k) → ℝ := fun t => (if t = u then 1 else 0) -
    (if (t : ℕ).testBit 0 = (u : ℕ).testBit 0 then te_h k else 0) with hw
  have hv : ∀ i t, te_v1 k u (cd_idx k i t) = if i = z0 then w t else 0 := by
    intro i t
    rw [te_v1_idx]
    by_cases hi : i = z0
    · rw [if_pos (by rw [hi]), if_pos hi]
    · rw [if_neg (fun h => hi (Fin.ext h)), if_neg hi]
  have hsum : ∑ p, te_v1 k u p = 0 := by
    rw [te_sum_idx]
    simp_rw [hv]
    rw [sum_eq_single z0 (fun i _ hi => by simp [hi]) (by simp)]
    simp only [ite_true, hw, sum_sub_distrib]
    rw [sum_ite_eq' univ u (fun _ => (1 : ℝ))]
    have : ∑ t : Fin (2 ^ k), (if (t : ℕ).testBit 0 = (u : ℕ).testBit 0 then te_h k else 0) =
        te_h k * 2 ^ (k - 1) := by
      rw [← hcnt, mul_sum]
      exact sum_congr rfl fun t _ => by split_ifs <;> ring
    rw [this, hh]; simp
  have hw2 : ∑ t, w t ^ 2 = 1 - te_h k := by
    have e : ∀ t : Fin (2 ^ k), w t ^ 2 = (if t = u then 1 - 2 * te_h k else 0) +
        te_h k ^ 2 * (if (t : ℕ).testBit 0 = (u : ℕ).testBit 0 then 1 else 0) := by
      intro t
      rw [hw]
      by_cases h1 : t = u
      · subst h1; simp; ring
      · simp only [h1, ite_false]
        split_ifs <;> ring
    simp_rw [e]
    rw [sum_add_distrib, sum_ite_eq' univ u, ← mul_sum, hcnt]
    simp only [mem_univ, ite_true]
    have : te_h k ^ 2 * 2 ^ (k - 1) = te_h k := by rw [sq, mul_assoc, hh, mul_one]
    rw [this]; ring
  have hpat : ∑ t : Fin (2 ^ k), (∑ i : Fin k, te_v1 k u (cd_idx k i t)) ^ 2 = 1 - te_h k := by
    simp_rw [hv]
    simp only [sum_ite_eq', mem_univ, ite_true]
    exact hw2
  have hsq : ∑ p, te_v1 k u p ^ 2 = 1 - te_h k := by
    rw [te_sum_idx (fun p => te_v1 k u p ^ 2)]
    simp_rw [hv]
    rw [sum_eq_single z0 (fun i _ hi => by simp [hi]) (by simp)]
    simp only [ite_true]
    exact hw2
  rw [cd_quad_C, hsum, hpat, hsq]
  ring

lemma te_quad_v1_le (hk : 2 ≤ k) (u : Fin (2 ^ k)) : gg_quad (gg_C k) (te_v1 k u) ≤ 7 / 80 := by
  rw [te_quad_v1 (by omega)]
  have h0 : 0 ≤ te_h k := by unfold te_h; positivity
  have hc : gg_c1 k + gg_c2 k ≤ 7 / 80 := by
    unfold gg_c1 gg_c2
    have h4 : ((2 : ℝ) ^ k)⁻¹ ≤ 1 / 4 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      calc (1 / 4 : ℝ)⁻¹ = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
    have h0' : 0 ≤ ((2 : ℝ) ^ k)⁻¹ := by positivity
    nlinarith
  have hpos : 0 ≤ gg_c1 k + gg_c2 k := by have := gg_c1_pos k; have := gg_c2_pos k; linarith
  nlinarith

lemma te_quad_v1_pos (hk : 2 ≤ k) (u : Fin (2 ^ k)) : 0 < gg_quad (gg_C k) (te_v1 k u) := by
  rw [te_quad_v1 (by omega)]
  have := te_h_le hk
  have := gg_c1_pos k; have := gg_c2_pos k
  have : 0 < 1 - te_h k := by linarith
  positivity

lemma te_sumabs_v1 (hk : 1 ≤ k) (u : Fin (2 ^ k)) : ∑ p, |te_v1 k u p| ≤ 2 := by
  have hcnt := te_count_bit0 hk u
  have hh := te_h_mul hk
  have h0 : 0 ≤ te_h k := by unfold te_h; positivity
  rw [te_sum_idx (fun p => |te_v1 k u p|), sum_eq_single (⟨0, hk⟩ : Fin k)]
  · simp_rw [te_v1_idx]
    simp only [ite_true]
    calc ∑ t : Fin (2 ^ k), |(if t = u then (1 : ℝ) else 0) -
          (if (t : ℕ).testBit 0 = (u : ℕ).testBit 0 then te_h k else 0)|
        ≤ ∑ t : Fin (2 ^ k), ((if t = u then (1 : ℝ) else 0) +
          te_h k * (if (t : ℕ).testBit 0 = (u : ℕ).testBit 0 then 1 else 0)) := by
          refine sum_le_sum fun t _ => ?_
          refine (abs_sub _ _).trans (le_of_eq ?_)
          split_ifs <;> simp [abs_of_nonneg h0]
      _ = 2 := by
          rw [sum_add_distrib, sum_ite_eq' univ u, ← mul_sum, hcnt, hh]
          simp only [mem_univ, ite_true]; norm_num
  · intro i _ hi
    refine sum_eq_zero fun t _ => ?_
    rw [te_v1_idx, if_neg (fun h => hi (Fin.ext h)), abs_zero]
  · intro h; exact absurd (mem_univ _) h

/-- `F_{θ₀}(t) = ⟨v_u, ξ⟩`. -/
lemma te_urF_theta0 (e : Fin k ↪ Fin N) (hk2 : 2 ≤ k) (w : Param N) (t : State N) :
    ur_F w (te_theta0 (te_mem_U (e := e) ⟨0, by omega⟩)
      (by rw [bg_card_U e.injective]; exact hk2)) t (sigN N) =
      ∑ p, te_v1 k (te_pat e.injective t) p * te_xi e.injective w p := by
  have hk : 1 ≤ k := by omega
  set z0 : Fin k := ⟨0, by omega⟩
  set a := e z0
  have ha : a ∈ bg_U e := te_mem_U z0
  have h2 : 2 ≤ (bg_U e).card := by rw [bg_card_U e.injective]; exact hk2
  have he := e.injective
  rw [te_sum_v1 hk]
  rw [ur_F, te_sum_U he (fun j => ur_D w (te_theta0 ha h2) t j), sum_eq_single z0]
  · -- unit `a`
    have hP : profile (te_theta0 ha h2) a ⊆ bg_U e := prof_profile_subset _ a
    rw [ur_D, te_Num_S he w t z0, te_Num_Y he w hP t z0, te_theta0_prof_a,
      card_erase_of_mem ha, bg_card_U he]
    have hσ := sigN_pos N
    have hcond : ∀ u' : Fin (2 ^ k), (∀ q : Fin k, e q ∉ (bg_U e).erase a →
        (u' : ℕ).testBit q = (te_pat he t : ℕ).testBit q) ↔
        (u' : ℕ).testBit 0 = (te_pat he t : ℕ).testBit 0 := by
      intro u'
      constructor
      · intro h
        exact h z0 (notMem_erase a _)
      · intro h q hq
        have hqa : e q = a := by
          by_contra hne; exact hq (mem_erase.2 ⟨hne, te_mem_U q⟩)
        have : q = z0 := he hqa
        subst this
        exact h
    simp_rw [hcond]
    rw [div_eq_iff hσ.ne']
    simp only [sub_mul, ite_mul, one_mul, zero_mul, sum_sub_distrib]
    rw [sum_ite_eq' univ (te_pat he t)]
    simp only [mem_univ, ite_true]
    have : ∑ x : Fin (2 ^ k), (if (x : ℕ).testBit 0 = (te_pat he t : ℕ).testBit 0 then te_h k *
        te_xi he w (cd_idx k z0 x) else 0) = te_h k * ∑ x : Fin (2 ^ k),
        (if (x : ℕ).testBit 0 = (te_pat he t : ℕ).testBit 0 then te_xi he w (cd_idx k z0 x) else 0) := by
      rw [mul_sum]; exact sum_congr rfl fun x _ => by split_ifs <;> ring
    rw [this, te_h]
    field_simp
    ring
  · intro i _ hi
    have hia : e i ≠ a := fun h => hi (he h)
    rw [ur_D, te_theta0_prof_b ha h2 (te_mem_U i) hia, sdiff_empty, sub_self]
  · intro h; exact absurd (mem_univ _) h

/-! ### The cut event -/

/-- Some ordering and pattern give `⟨v_u, ξ⟩ ≥ y_N / k - (k - 1) e_N`. -/
def te_cutBad (k N : ℕ) (c : ℝ) : Set (Param N) :=
  {w | ∃ e : Fin k ↪ Fin N, ∃ u : Fin (2 ^ k),
    te_y k c N / k - (k - 1) * te_e k N ≤ ∑ p, te_v1 k u p * te_xi e.injective w p}

theorem te_mem_cutBad (hk2 : 2 ≤ k) {s : State N} {z : Param N} (hz : z ∈ openCube N)
    {S : Finset (Fin N)} (hSk : S.card = k) {c : ℝ} (hc0 : 0 ≤ c)
    (h3 : 3 * te_eta N ≤ bg_ak k) (hy : 0 < te_y k c N) (hfield : flipP s z ∉ te_fieldBad k N)
    (heff : z ∉ te_effBad k N s) (hphi : c * Real.sqrt (Real.log N) * sigN N < phi z s S) :
    flipP s z ∈ te_cutBad k N c := by
  obtain ⟨e, hSe, θ, t, _, hmin, hyF⟩ := te_reduce hz hSk hc0 h3 hfield heff hphi
  subst hSe
  set z0 : Fin k := ⟨0, by omega⟩
  have ha : e z0 ∈ bg_U e := te_mem_U z0
  have h2 : 2 ≤ (bg_U e).card := by rw [bg_card_U e.injective]; exact hk2
  refine ⟨e, te_pat e.injective t, ?_⟩
  have hm := hmin (te_theta0 ha h2)
  rw [te_theta0_cc, bg_card_U e.injective] at hm
  have hF0 := te_urF_theta0 e hk2 (flipP s z) t
  rw [← hF0]
  set F := ur_F (flipP s z) θ t (sigN N)
  set F0 := ur_F (flipP s z) (te_theta0 ha h2) t (sigN N)
  have hcc := te_cc_le θ
  rw [bg_card_U e.injective] at hcc
  have hccpos : (0 : ℝ) < sysCutCount θ := by exact_mod_cast sysCutCount_pos θ
  have hk1 : (1 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    linarith
  have hkpos : (0 : ℝ) < k := by linarith
  have hFpos : 0 < F := lt_of_lt_of_le hy hyF
  -- `F / cc ≥ y / (k (k - 1))`
  have hratio : te_y k c N / (k * (k - 1)) ≤ F / sysCutCount θ := by
    rw [div_le_div_iff₀ (by positivity) hccpos]
    calc te_y k c N * sysCutCount θ ≤ F * sysCutCount θ :=
          mul_le_mul_of_nonneg_right hyF hccpos.le
      _ ≤ F * (k * (k - 1)) := mul_le_mul_of_nonneg_left hcc hFpos.le
  have h1 : te_y k c N / (k * (k - 1)) - te_e k N ≤ F0 / (k - 1) := by linarith
  have h1' := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ k - 1)
  rw [mul_div_cancel₀ _ (by linarith : (k : ℝ) - 1 ≠ 0)] at h1'
  have e1 : ((k : ℝ) - 1) * (te_y k c N / (k * (k - 1)) - te_e k N) =
      te_y k c N / k - (k - 1) * te_e k N := by
    field_simp
  linarith

/-! ### Probability of the cut event -/

lemma te_ps_err_mono {C2 C2' C3 C3' : ℝ} (h2 : C2 ≤ C2') (h3 : C3 ≤ C3') (N : ℕ) :
    ps_err C2 C3 N ≤ ps_err C2' C3' N := by
  unfold ps_err
  have := ps_eps_pos N
  have := lind_Kpsi_pos
  gcongr

lemma te_C2_mono {Λ Λ' : ℝ} (h0 : 0 ≤ Λ) (h : Λ ≤ Λ') : te_C2 k Λ ≤ te_C2 k Λ' := by
  unfold te_C2; gcongr

lemma te_C3_mono {Λ Λ' : ℝ} (h0 : 0 ≤ Λ) (h : Λ ≤ Λ') : te_C3 k Λ ≤ te_C3 k Λ' := by
  unfold te_C3
  have := te_C3G_nonneg k
  gcongr

/-- The numerical condition for the single cut at level `0.28`. -/
lemma te_cut_num (hk : 6 ≤ k) :
    (k : ℝ) < 40 / 7 * ((999 / 1000 * (28 / 100) * te_kap k) / k) ^ 2 := by
  have hl2 := Real.log_two_gt_d9
  have hA := te_ak_ge k
  -- `k³ ≤ (27/128) 4^{k-1}`
  have hind : ∀ n : ℕ, 6 ≤ n → ((n : ℝ)) ^ 3 ≤ 27 / 128 * 4 ^ (n - 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      have hm' : (6 : ℝ) ≤ m := by exact_mod_cast hm
      rw [show m + 1 - 1 = (m - 1) + 1 by omega,
        show (4 : ℝ) ^ (m - 1 + 1) = 4 ^ (m - 1) * 4 from pow_succ _ _]
      push_cast
      have hd : (0 : ℝ) ≤ m - 6 := by linarith
      have h1 : ((m : ℝ) + 1) ^ 3 ≤ 4 * (m : ℝ) ^ 3 := by
        nlinarith [mul_nonneg hd (sq_nonneg ((m : ℝ) - 6)), sq_nonneg ((m : ℝ) - 6)]
      nlinarith [h1, ih]
  have h3 := hind k hk
  have hkr : (6 : ℝ) ≤ k := by exact_mod_cast hk
  have hkap : (2 : ℝ) ^ (k - 1) * Real.log 2 ≤ te_kap k := by
    unfold te_kap
    have h2k : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    rw [h2k]
    have : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hPL : 0 ≤ (2 : ℝ) ^ (k - 1) * Real.log 2 := by positivity
    nlinarith [mul_nonneg hPL (by linarith : (0 : ℝ) ≤ 2 * bg_ak k - 1)]
  have h4 : (4 : ℝ) ^ (k - 1) = ((2 : ℝ) ^ (k - 1)) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  set P := (2 : ℝ) ^ (k - 1) with hP
  have hP0 : 0 < P := by positivity
  have hq : (999 / 1000 * (28 / 100) * (P * Real.log 2) / k) ^ 2 ≤
      (999 / 1000 * (28 / 100) * te_kap k / k) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    gcongr
  refine lt_of_lt_of_le ?_ (mul_le_mul_of_nonneg_left hq (by norm_num))
  rw [div_pow, mul_div_assoc', lt_div_iff₀ (by positivity)]
  rw [h4] at h3
  have hl : (0.6931471803 : ℝ) ^ 2 ≤ Real.log 2 ^ 2 := pow_le_pow_left₀ (by norm_num) hl2.le 2
  have hkk : (k : ℝ) * (k : ℝ) ^ 2 = (k : ℝ) ^ 3 := by ring
  nlinarith [mul_le_mul_of_nonneg_left hl (sq_nonneg P)]

/-- **Theorem E for `k ≥ 6`**: with probability tending to one, no `k`-set has
`φ_s > 0.28 √(ln N) σ_N`. -/
theorem te_thmE_cut (hk : 6 ≤ k) (s : ∀ N, State N) :
    Tendsto (fun N => volume {z | z ∈ cube N ∧ ∃ S : Finset (Fin N), S.card = k ∧
      28 / 100 * Real.sqrt (Real.log N) * sigN N < phi z (s N) S}) atTop (𝓝 0) := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  have hkr : (6 : ℝ) ≤ k := by exact_mod_cast hk
  set c : ℝ := 28 / 100 with hcdef
  set l : ℝ := 999 / 1000 * c * te_kap k with hldef
  have hkap := te_kap_pos k
  have hlc : l < c * te_kap k := by rw [hldef]; nlinarith
  have hl0 : 0 < l := by rw [hldef]; positivity
  set K : ℝ := 40 / 7 * (l / k) ^ 2 with hKdef
  have hK : (k : ℝ) < K := te_cut_num hk
  have hy := te_ev_y k hlc
  set A : ℝ := 2
  set g : ℕ → ℝ := fun N => Real.exp (-(K * Real.log N)) + ps_err (te_C2 k A) (te_C3 k A) N
    with hg
  have hg0 : ∀ N, 0 ≤ g N := by
    intro N
    have := ps_err_nonneg (C2 := te_C2 k A) (C3 := te_C3 k A) (by unfold te_C2; positivity)
      (by unfold te_C3; have := te_C3G_nonneg k; positivity) N
    positivity
  have hgT : Tendsto (fun N : ℕ => (N : ℝ) ^ k * g N) atTop (𝓝 0) := by
    have h := (te_tendsto_exp_log k hK).add (te_tendsto_err k (te_C2 k A) (te_C3 k A))
    rw [add_zero] at h
    exact h.congr fun N => by rw [hg]; ring
  -- one ordering and pattern
  have he0 : Tendsto (fun N => te_e k N) atTop (𝓝 0) := by
    have h := te_tendsto_e k 0
    simpa using h
  have hε0 : Tendsto (fun N : ℕ => ps_eps N) atTop (𝓝 0) := by
    have h := te_tendsto_geom 0 (q := 99 / 100) (by norm_num) (by norm_num) 1
    simpa [ps_eps] using h
  have hsmall : ∀ᶠ N : ℕ in atTop, (k - 1) * te_e k N + ps_eps N < 1 / k := by
    have h := (he0.const_mul ((k : ℝ) - 1)).add hε0
    rw [mul_zero, add_zero] at h
    exact (tendsto_order.1 h).2 _ (by positivity)
  have hone : ∀ᶠ N : ℕ in atTop, ∀ (e : Fin k ↪ Fin N) (u : Fin (2 ^ k)),
      cubeM N {w | te_y k c N / k - (k - 1) * te_e k N ≤
        ∑ p, te_v1 k u p * te_xi e.injective w p} ≤ ENNReal.ofReal (g N) := by
    filter_upwards [hy, hsmall, eventually_ge_atTop 1] with N hyN hsN hN e u
    set h := te_y k c N / k - (k - 1) * te_e k N with hhdef
    have hs0 : 0 ≤ l * Real.sqrt (Real.log N) := by positivity
    have hkpos : (0 : ℝ) < k := by linarith
    have hyk : (l * Real.sqrt (Real.log N) + 1) / k ≤ te_y k c N / k :=
      div_le_div_of_nonneg_right hyN hkpos.le
    have hd : l / k * Real.sqrt (Real.log N) < h - ps_eps N := by
      have : (l * Real.sqrt (Real.log N) + 1) / k = l / k * Real.sqrt (Real.log N) + 1 / k := by
        field_simp
      have hh' : h = te_y k c N / k - (k - 1) * te_e k N := hhdef
      linarith
    have hεh : ps_eps N < h := by
      have : 0 ≤ l / k * Real.sqrt (Real.log N) := by positivity
      linarith
    have hlin := te_halfspace_le e.injective (te_v1 k u) hεh
    have hq0 := te_quad_v1_pos hk2 u
    have hq1 := te_quad_v1_le hk2 u
    have hA1 := te_sumabs_v1 hk1 u
    have herr : ps_err (te_C2 k (∑ p, |te_v1 k u p|)) (te_C3 k (∑ p, |te_v1 k u p|)) N ≤
        ps_err (te_C2 k A) (te_C3 k A) N :=
      te_ps_err_mono (te_C2_mono (sum_nonneg fun _ _ => abs_nonneg _) hA1)
        (te_C3_mono (sum_nonneg fun _ _ => abs_nonneg _) hA1) N
    refine te_le_ofReal (hlin.trans (add_le_add ?_ herr))
    apply Real.exp_le_exp.2
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    have hsq : Real.sqrt (Real.log N) ^ 2 = Real.log N := Real.sq_sqrt hlogN
    have hd0 : 0 ≤ l / k * Real.sqrt (Real.log N) := by positivity
    have hsq2 : (l / k) ^ 2 * Real.log N ≤ (h - ps_eps N) ^ 2 := by
      have := pow_le_pow_left₀ hd0 hd.le 2
      rw [← hsq]; nlinarith
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    calc K * Real.log N * (2 * gg_quad (gg_C k) (te_v1 k u))
        ≤ K * Real.log N * (2 * (7 / 80)) := by
          have : 0 ≤ K * Real.log N := by rw [hKdef]; positivity
          gcongr
      _ = (l / k) ^ 2 * Real.log N := by rw [hKdef]; ring
      _ ≤ (h - ps_eps N) ^ 2 := hsq2
  -- the union over orderings and patterns
  have hcut : Tendsto (fun N => cubeM N (te_cutBad k N c)) atTop (𝓝 0) := by
    have hT : Tendsto (fun N : ℕ => (2 : ℝ) ^ k * ((N : ℝ) ^ k * g N)) atTop (𝓝 0) := by
      have := hgT.const_mul ((2 : ℝ) ^ k); rwa [mul_zero] at this
    have hlim' : Tendsto (fun N : ℕ => ENNReal.ofReal ((2 : ℝ) ^ k * ((N : ℝ) ^ k * g N))) atTop
        (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]; exact ENNReal.tendsto_ofReal hT
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hone] with N hN
    have hsub : te_cutBad k N c ⊆ ⋃ e : Fin k ↪ Fin N, ⋃ u : Fin (2 ^ k),
        {w | te_y k c N / k - (k - 1) * te_e k N ≤
          ∑ p, te_v1 k u p * te_xi e.injective w p} := by
      rintro w ⟨e, u, h⟩
      exact Set.mem_iUnion.2 ⟨e, Set.mem_iUnion.2 ⟨u, h⟩⟩
    calc cubeM N (te_cutBad k N c)
        ≤ ∑ e : Fin k ↪ Fin N, ∑ u : Fin (2 ^ k), cubeM N {w | te_y k c N / k -
            (k - 1) * te_e k N ≤ ∑ p, te_v1 k u p * te_xi e.injective w p} :=
          (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans
            (Finset.sum_le_sum fun e _ => measure_iUnion_fintype_le _ _))
      _ ≤ ∑ _e : Fin k ↪ Fin N, ∑ _u : Fin (2 ^ k), ENNReal.ofReal (g N) :=
          Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun u _ => hN e u
      _ = ENNReal.ofReal ((Fintype.card (Fin k ↪ Fin N) : ℝ) * ((2 : ℝ) ^ k * g N)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have h1 : ((Fintype.card (Fin k ↪ Fin N) : ℕ) : ℝ≥0∞) =
              ENNReal.ofReal (Fintype.card (Fin k ↪ Fin N) : ℝ) := (ENNReal.ofReal_natCast _).symm
          have h2 : ((2 ^ k : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ k) := by
            rw [← ENNReal.ofReal_natCast]; push_cast; rfl
          rw [h1, h2, ← ENNReal.ofReal_mul (by have := hg0 N; positivity),
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ k * ((N : ℝ) ^ k * g N)) := by
          apply ENNReal.ofReal_le_ofReal
          have := te_card_emb k N
          have : 0 ≤ (2 : ℝ) ^ k * g N := by have := hg0 N; positivity
          nlinarith
  -- assembly
  have hflip_field : Tendsto (fun N => volume {z | z ∈ cube N ∧
      flipP (s N) z ∈ te_fieldBad k N}) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (te_tendsto_fieldBad k)
      (fun _ => bot_le) fun N => te_volume_flip_le (s N) (fun w => w ∈ te_fieldBad k N)
  have hflip_cut : Tendsto (fun N => volume {z | z ∈ cube N ∧
      flipP (s N) z ∈ te_cutBad k N c}) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcut
      (fun _ => bot_le) fun N => te_volume_flip_le (s N) (fun w => w ∈ te_cutBad k N c)
  have heffv : Tendsto (fun N => volume (te_effBad k N (s N))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (te_tendsto_effBad k hk1 s) (fun _ => bot_le) fun N => ?_
    have hsub : te_effBad k N (s N) ⊆ cube N ∩ te_effBad k N (s N) := fun z hz =>
      ⟨fun r j => Set.Ioo_subset_Icc_self (hz.1 r j), hz⟩
    exact (measure_mono hsub).trans (volume_cube_inter _).le
  have hsum := ((hflip_field.add heffv).add hflip_cut)
  rw [add_zero, add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [te_ev_three_eta k, hy] with N h3 hyN
  have hypos : 0 < te_y k c N := by
    have : 0 ≤ l * Real.sqrt (Real.log N) := by positivity
    linarith
  have hsub : {z | z ∈ cube N ∧ ∃ S : Finset (Fin N), S.card = k ∧
      c * Real.sqrt (Real.log N) * sigN N < phi z (s N) S} ⊆
      (cube N \ openCube N) ∪ {z | z ∈ cube N ∧ flipP (s N) z ∈ te_fieldBad k N} ∪
        te_effBad k N (s N) ∪ {z | z ∈ cube N ∧ flipP (s N) z ∈ te_cutBad k N c} := by
    rintro z ⟨hz, S, hSk, hphi⟩
    by_cases ho : z ∈ openCube N
    · by_cases hf : flipP (s N) z ∈ te_fieldBad k N
      · exact Or.inl (Or.inl (Or.inr ⟨hz, hf⟩))
      · by_cases he : z ∈ te_effBad k N (s N)
        · exact Or.inl (Or.inr he)
        · exact Or.inr ⟨hz, te_mem_cutBad hk2 ho hSk (by norm_num) h3 hypos hf he hphi⟩
    · exact Or.inl (Or.inl (Or.inl ⟨hz, ho⟩))
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  refine (measure_union_le _ _).trans ?_
  rw [volume_cube_diff_openCube, zero_add]

end

end Census
end IIT
