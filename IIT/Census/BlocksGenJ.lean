/-
Census of complexes: the joint block decomposition of the fields of two `k`-sets sharing `m` units.

The two ordered `k`-sets are injections `e0 e1 : Fin k → Fin N` with `e0 i = e1 i'` exactly when
`i = i' + (k - m)` (`bg_JPair`): the last `m` units of the first set are the first `m` units of the
second, in the layout of `gg_jidx` in `GaussGen`.  Their union is the injection `bg_eU e0 e1 m` of
`Fin (2k - m)`, and the rows split into `2^(N-(2k-m))` superblocks of `2^(2k-m)` rows, the rows of a
superblock being indexed by the union patterns `(own bits of set 0, shared bits, own bits of set 1)`
of `gg_ρ k m`.  The superblock summand `bg_jX` is a vector indexed by the joint coordinates
`Fin (2 (k 2^k))`; coordinate `gg_jidx k w p` is the sum over the `2^(k-m)` blocks of set `w` inside
the superblock of `(W_β · clamp01 (w (row t of β) (e_w i)) - a_k / 2^(N-k)) / σ_N`, so that
summing over the superblocks gives the centred field of set `w` (`bg_j_sum0`, `bg_j_sum1`).

Under `cubeM N` the superblock summands are iid with law `bg_jnu` (`bg_j_map_Xs`), which has zero
means (`bg_jnu_mean`), second moments `|2^(N-(2k-m)) ∫ x P x Q dν - C_J[P,Q]| ≤ 2^(2k-m) (3/4)^N`
where `C_J = gg_CJ k m` is exactly the joint covariance of `GaussGen` (`bg_jnu_second`, via the
exact identity `bg_j_corr`), and third absolute moments
`2^(N-(2k-m)) ∫ (∑ |x P|)^3 dν ≤ 8 (2 k 2^k)^3 4^(2k-m) (23/25)^N` (`bg_jnu_third`).  Removing the
superblock of a state `s` leaves iid summands (`bg_j_map_Xr`) independent of the rows of that
superblock (`bg_j_indep_rest`) and changes every coordinate by at most `2^(2k-m) τ_N / σ_N` on `g2`
(`bg_j_abs_sub_rest_le`).
-/
import IIT.Census.BlocksGenK

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset

set_option linter.unusedSectionVars false

noncomputable section

variable {N k m : ℕ}

/-- Two ordered `k`-sets sharing their last / first `m` units, and otherwise disjoint. -/
def bg_JPair (k m : ℕ) (e0 e1 : Fin k → Fin N) : Prop :=
  m ≤ k ∧ Function.Injective e0 ∧ Function.Injective e1 ∧
    ∀ i i', e0 i = e1 i' ↔ (i : ℕ) = i' + (k - m)

/-! ### The union of the two sets -/

/-- The union: units `0, …, k-1` are those of the first set, units `k - m + i` those of the
second. -/
def bg_eU (e0 e1 : Fin k → Fin N) (m : ℕ) (g : Fin (2 * k - m)) : Fin N :=
  if h : (g : ℕ) < k then e0 ⟨g, h⟩ else e1 ⟨g - (k - m), by omega⟩

section Union

variable {e0 e1 : Fin k → Fin N}

lemma bg_eU_lt (g : Fin (2 * k - m)) (hg : (g : ℕ) < k) : bg_eU e0 e1 m g = e0 ⟨g, hg⟩ := by
  simp [bg_eU, hg]

lemma bg_eU_ge (g : Fin (2 * k - m)) (hg : ¬ (g : ℕ) < k) :
    bg_eU e0 e1 m g = e1 ⟨g - (k - m), by omega⟩ := by
  simp [bg_eU, hg]

lemma bg_eU_e1 (h : bg_JPair k m e0 e1) (g : Fin (2 * k - m)) (hg : k - m ≤ (g : ℕ)) :
    bg_eU e0 e1 m g = e1 ⟨g - (k - m), by omega⟩ := by
  by_cases hk : (g : ℕ) < k
  · rw [bg_eU_lt g hk]
    exact (h.2.2.2 _ _).2 (by simp; omega)
  · exact bg_eU_ge g hk

lemma bg_eU_inj (h : bg_JPair k m e0 e1) : Function.Injective (bg_eU e0 e1 m) := by
  intro g g' hgg
  by_cases hg : (g : ℕ) < k <;> by_cases hg' : (g' : ℕ) < k
  · rw [bg_eU_lt g hg, bg_eU_lt g' hg'] at hgg
    exact Fin.ext (by simpa using h.2.1 hgg)
  · rw [bg_eU_lt g hg, bg_eU_ge g' hg'] at hgg
    have := (h.2.2.2 _ _).1 hgg
    simp at this; omega
  · rw [bg_eU_ge g hg, bg_eU_lt g' hg'] at hgg
    have := (h.2.2.2 _ _).1 hgg.symm
    simp at this; omega
  · rw [bg_eU_ge g hg, bg_eU_ge g' hg'] at hgg
    have := h.2.2.1 hgg
    simp only [Fin.mk.injEq] at this
    exact Fin.ext (by omega)

lemma bg_eU_mem0 (h : bg_JPair k m e0 e1) (g : Fin (2 * k - m)) :
    bg_eU e0 e1 m g ∈ bg_U e0 ↔ (g : ℕ) < k := by
  constructor
  · intro hmem
    by_contra hg
    obtain ⟨i, hi⟩ := bg_mem_U e0 hmem
    rw [bg_eU_ge g hg] at hi
    have := (h.2.2.2 _ _).1 hi
    simp at this; omega
  · intro hg
    rw [bg_eU_lt g hg]
    exact bg_E_mem e0 _

lemma bg_eU_mem1 (h : bg_JPair k m e0 e1) (g : Fin (2 * k - m)) :
    bg_eU e0 e1 m g ∈ bg_U e1 ↔ k - m ≤ (g : ℕ) := by
  constructor
  · intro hmem
    by_contra hg
    obtain ⟨i, hi⟩ := bg_mem_U e1 hmem
    rw [bg_eU_lt g (by omega)] at hi
    have := (h.2.2.2 _ _).1 hi.symm
    simp at this; omega
  · intro hg
    rw [bg_eU_e1 h g hg]
    exact bg_E_mem e1 _

lemma bg_U0_sub (h : bg_JPair k m e0 e1) : bg_U e0 ⊆ bg_U (bg_eU e0 e1 m) := by
  intro j hj
  obtain ⟨i, rfl⟩ := bg_mem_U e0 hj
  have hi : (i : ℕ) < 2 * k - m := by have := h.1; omega
  rw [show e0 i = bg_eU e0 e1 m ⟨i, hi⟩ by rw [bg_eU_lt _ i.2]]
  exact bg_E_mem _ _

lemma bg_U1_sub (h : bg_JPair k m e0 e1) : bg_U e1 ⊆ bg_U (bg_eU e0 e1 m) := by
  intro j hj
  obtain ⟨i, rfl⟩ := bg_mem_U e1 hj
  have hi : (i : ℕ) + (k - m) < 2 * k - m := by have := h.1; omega
  have e : e1 i = bg_eU e0 e1 m ⟨i + (k - m), hi⟩ := by
    rw [bg_eU_e1 h _ (by simp)]
    congr 1; ext; simp
  rw [e]
  exact bg_E_mem _ _

end Union

/-! ### Bits of union patterns -/

/-- Bit `g` of the union pattern `u = (own bits of set 0, shared bits, own bits of set 1)`. -/
def bg_jbits (k m : ℕ) (u : gg_ρ k m) (g : Fin (2 * k - m)) : Bool :=
  if (g : ℕ) < k - m then (u.1 : ℕ).testBit g
  else if (g : ℕ) < k then (u.2.1 : ℕ).testBit (g - (k - m))
  else (u.2.2 : ℕ).testBit (g - k)

lemma bg_tb_false {n : ℕ} (x : Fin (2 ^ n)) {i : ℕ} (hi : n ≤ i) : (x : ℕ).testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le x.2 (Nat.pow_le_pow_right (by norm_num) hi))

lemma bg_jbits_inj (hm : m ≤ k) : Function.Injective (bg_jbits k m) := by
  rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ h
  have hb := fun g => congrFun h g
  simp only [Prod.mk.injEq]
  refine ⟨Fin.ext (Nat.eq_of_testBit_eq fun i => ?_), Fin.ext (Nat.eq_of_testBit_eq fun i => ?_),
    Fin.ext (Nat.eq_of_testBit_eq fun i => ?_)⟩
  · by_cases hi : i < k - m
    · have := hb ⟨i, by omega⟩
      simpa [bg_jbits, hi] using this
    · rw [bg_tb_false x (by omega), bg_tb_false x' (by omega)]
  · by_cases hi : i < m
    · have := hb ⟨i + (k - m), by omega⟩
      simpa [bg_jbits, show ¬ (i + (k - m) < k - m) by omega, show i + (k - m) < k by omega]
        using this
    · rw [bg_tb_false y (by omega), bg_tb_false y' (by omega)]
  · by_cases hi : i < k - m
    · have := hb ⟨i + k, by omega⟩
      simpa [bg_jbits, show ¬ (i + k < k - m) by omega, show ¬ (i + k < k) by omega] using this
    · rw [bg_tb_false z (by omega), bg_tb_false z' (by omega)]

lemma bg_card_ρ (hm : m ≤ k) : Fintype.card (gg_ρ k m) = 2 ^ (2 * k - m) := by
  simp only [Fintype.card_prod, Fintype.card_fin, ← pow_add]
  congr 1; omega

/-! ### Rows, coordinates and summands -/

section Joint

variable {e0 e1 : Fin k → Fin N}

/-- The rows parametrised by (superblock, union pattern). -/
def bg_jg (h : bg_JPair k m e0 e1) : bg_Bg (bg_eU e0 e1 m) × gg_ρ k m ≃ State N :=
  bg_eqv (bg_jbits k m) (bg_eU_inj h) (bg_jbits_inj h.1) (bg_card_ρ h.1)

/-- The row of a joint coordinate: the bits of its set are replaced by its pattern. -/
def bg_jρ (k m : ℕ) (P : Fin (2 * (k * 2 ^ k))) (u : gg_ρ k m) : gg_ρ k m :=
  if gg_jw k P = 0 then
    (gg_lo0 k m (gg_pat k (gg_jp k P)), gg_hi0 k m (gg_pat k (gg_jp k P)), u.2.2)
  else (u.1, gg_lo1 k m (gg_pat k (gg_jp k P)), gg_hi1 k m (gg_pat k (gg_jp k P)))

/-- The unit of a joint coordinate. -/
def bg_jj (e0 e1 : Fin k → Fin N) (P : Fin (2 * (k * 2 ^ k))) : Fin N :=
  if gg_jw k P = 0 then e0 (gg_unit k (gg_jp k P)) else e1 (gg_unit k (gg_jp k P))

/-- The centring constant `2^(k-m) a_k / 2^(N-k)` (one `a_k / 2^(N-k)` per block). -/
def bg_jc (N k m : ℕ) (_P : Fin (2 * (k * 2 ^ k))) : ℝ := 2 ^ (k - m) * bg_ak k / 2 ^ (N - k)

/-- The summand of superblock `γ`. -/
def bg_jX (h : bg_JPair k m e0 e1) (γ : bg_Bg (bg_eU e0 e1 m)) (w : Param N) :
    Fin (2 * (k * 2 ^ k)) → ℝ :=
  bg_X (bg_jg h) (bg_jρ k m) (bg_jj e0 e1) (bg_jc N k m) γ w

/-- The common law of the superblock summands. -/
def bg_jnu (e0 e1 : Fin k → Fin N) (m : ℕ) : Measure (Fin (2 * (k * 2 ^ k)) → ℝ) :=
  bg_nu (bg_jρ k m) (bg_jj e0 e1) (bg_jc N k m)

instance (e0 e1 : Fin k → Fin N) (m : ℕ) : IsProbabilityMeasure (bg_jnu e0 e1 m) := by
  unfold bg_jnu; infer_instance

/-- The number of superblocks. -/
def bg_jB (e0 e1 : Fin k → Fin N) (m : ℕ) : ℕ := Fintype.card (bg_Bg (bg_eU e0 e1 m))

lemma bg_jB_eq (h : bg_JPair k m e0 e1) : bg_jB e0 e1 m = 2 ^ (N - (2 * k - m)) :=
  bg_card_Bg (bg_eU_inj h)

lemma bg_j_le (h : bg_JPair k m e0 e1) : 2 * k - m ≤ N := bg_le_of_inj (bg_eU_inj h)

lemma bg_jB_mul (h : bg_JPair k m e0 e1) :
    (bg_jB e0 e1 m : ℝ) * Fintype.card (gg_ρ k m) = 2 ^ N := by
  rw [bg_jB_eq h, bg_card_ρ h.1]
  push_cast
  rw [← pow_add, Nat.sub_add_cancel (bg_j_le h)]

/-! ### Indicators of the pattern rows -/

lemma bg_jind (P : Fin (2 * (k * 2 ^ k))) (u : gg_ρ k m) :
    (if bg_jρ k m P u = u then (1 : ℝ) else 0) =
      gg_ind k m (gg_jw k P) (gg_pat k (gg_jp k P)) u := by
  obtain ⟨x, y, z⟩ := u
  unfold bg_jρ gg_ind gg_e1 gg_e2 gg_e3 gg_shb
  rcases gg_fin2 (gg_jw k P) with hw | hw
  · simp only [hw, ite_true, Prod.mk.injEq, and_true, mul_one]
    by_cases h1 : x = gg_lo0 k m (gg_pat k (gg_jp k P)) <;>
      by_cases h2 : y = gg_hi0 k m (gg_pat k (gg_jp k P)) <;> simp [h1, h2, eq_comm]
  · simp only [hw, show (1 : Fin 2) ≠ 0 by decide, ite_false, Prod.mk.injEq, true_and, one_mul]
    by_cases h1 : y = gg_lo1 k m (gg_pat k (gg_jp k P)) <;>
      by_cases h2 : z = gg_hi1 k m (gg_pat k (gg_jp k P)) <;> simp [h1, h2, eq_comm]

lemma bg_ind_sq (w : Fin 2) (t : Fin (2 ^ k)) (u : gg_ρ k m) :
    gg_ind k m w t u * gg_ind k m w t u = gg_ind k m w t u := by
  unfold gg_ind gg_e1 gg_e2 gg_e3; split_ifs <;> norm_num

lemma bg_sum_ind (w : Fin 2) (t : Fin (2 ^ k)) :
    ∑ u : gg_ρ k m, gg_ind k m w t u = 2 ^ (k - m) := by
  have h := gg_sum_ind_mul k m w w t t
  simp only [bg_ind_sq, ite_true, mul_one] at h
  exact h

/-! ### The centring constant is the exact mean -/

lemma bg_j_hc (h : bg_JPair k m e0 e1) (P : Fin (2 * (k * 2 ^ k))) :
    bg_jc N k m P = bg_mean N (bg_jρ k m P) := by
  have e : ∀ u, (if bg_jρ k m P u = u then (2 / 3 : ℝ) else 1 / 2) =
      1 / 2 + gg_ind k m (gg_jw k P) (gg_pat k (gg_jp k P)) u / 6 := by
    intro u; rw [← bg_jind]; split_ifs <;> norm_num
  simp only [bg_jc, bg_mean, e, sum_add_distrib, ← sum_div, bg_sum_ind, sum_const, card_univ,
    bg_card_ρ h.1, nsmul_eq_mul, bg_ak]
  have hm := h.1
  have hN := bg_j_le h
  obtain ⟨n, rfl⟩ : ∃ n, N = n + (2 * k - m) := ⟨N - (2 * k - m), by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, k = a + m := ⟨k - m, by omega⟩
  have e1 : a + m + m - m = a + m := by omega
  have e2 : 2 * (a + m) - m = a + a + m := by omega
  have e3 : n + (a + a + m) - (a + m) = n + a := by omega
  rw [Nat.add_sub_cancel, e2, e3]
  push_cast
  rw [one_div_pow, pow_add, pow_add, pow_add, pow_add]
  field_simp
  ring

/-! ### Merge rules and the block decomposition -/

lemma bg_merge0 (h : bg_JPair k m e0 e1) (t : Fin (2 ^ k)) (γ : bg_Bg (bg_eU e0 e1 m))
    (u : gg_ρ k m) :
    merge (bg_U e0) (bg_pst e0 t) (bg_jg h (γ, u)) =
      bg_jg h (γ, (gg_lo0 k m t, gg_hi0 k m t, u.2.2)) := by
  simp only [bg_jg, bg_eqv_apply]
  refine bg_merge_row (bg_jbits k m) (bg_eU_inj h) (bg_U0_sub h) _
    (fun u => (gg_lo0 k m t, gg_hi0 k m t, u.2.2)) (fun u g => ?_) γ u
  by_cases hg : (g : ℕ) < k
  · simp only [(bg_eU_mem0 h g).2 hg, ↓reduceIte]
    rw [bg_eU_lt g hg, bg_pst_E h.2.1]
    simp only [bg_jbits, bg_bits, gg_lo0, gg_hi0]
    by_cases hg' : (g : ℕ) < k - m
    · simp [hg', Nat.testBit_mod_two_pow]
    · simp only [hg', ite_false, hg, ite_true, Nat.testBit_div_two_pow]
      congr 1; omega
  · have hn : bg_eU e0 e1 m g ∉ bg_U e0 := fun hh => hg ((bg_eU_mem0 h g).1 hh)
    simp only [hn, ↓reduceIte]
    simp [bg_jbits, hg, show ¬ ((g : ℕ) < k - m) by omega]

lemma bg_merge1 (h : bg_JPair k m e0 e1) (t : Fin (2 ^ k)) (γ : bg_Bg (bg_eU e0 e1 m))
    (u : gg_ρ k m) :
    merge (bg_U e1) (bg_pst e1 t) (bg_jg h (γ, u)) =
      bg_jg h (γ, (u.1, gg_lo1 k m t, gg_hi1 k m t)) := by
  simp only [bg_jg, bg_eqv_apply]
  refine bg_merge_row (bg_jbits k m) (bg_eU_inj h) (bg_U1_sub h) _
    (fun u => (u.1, gg_lo1 k m t, gg_hi1 k m t)) (fun u g => ?_) γ u
  have hm := h.1
  by_cases hg : k - m ≤ (g : ℕ)
  · simp only [(bg_eU_mem1 h g).2 hg, ↓reduceIte]
    rw [bg_eU_e1 h g hg, bg_pst_E h.2.2.1]
    simp only [bg_jbits, bg_bits, gg_lo1, gg_hi1, show ¬ ((g : ℕ) < k - m) by omega, ite_false]
    by_cases hk : (g : ℕ) < k
    · simp [hk, Nat.testBit_mod_two_pow, show (g : ℕ) - (k - m) < m by omega]
    · simp only [hk, ite_false, Nat.testBit_div_two_pow]
      congr 1; omega
  · have hn : bg_eU e0 e1 m g ∉ bg_U e1 := fun hh => hg ((bg_eU_mem1 h g).1 hh)
    simp only [hn, ↓reduceIte]
    simp [bg_jbits, show ((g : ℕ) < k - m) by omega]

lemma bg_jρ_jidx0 (p : Fin (k * 2 ^ k)) (u : gg_ρ k m) :
    bg_jρ k m (gg_jidx k 0 p) u = (gg_lo0 k m (gg_pat k p), gg_hi0 k m (gg_pat k p), u.2.2) := by
  simp [bg_jρ]

lemma bg_jρ_jidx1 (p : Fin (k * 2 ^ k)) (u : gg_ρ k m) :
    bg_jρ k m (gg_jidx k 1 p) u = (u.1, gg_lo1 k m (gg_pat k p), gg_hi1 k m (gg_pat k p)) := by
  simp [bg_jρ]

lemma bg_jj_jidx0 (p : Fin (k * 2 ^ k)) : bg_jj e0 e1 (gg_jidx k 0 p) = e0 (gg_unit k p) := by
  simp [bg_jj]

lemma bg_jj_jidx1 (p : Fin (k * 2 ^ k)) : bg_jj e0 e1 (gg_jidx k 1 p) = e1 (gg_unit k p) := by
  simp [bg_jj]

lemma bg_j_count (h : bg_JPair k m e0 e1) (P : Fin (2 * (k * 2 ^ k))) :
    (Fintype.card (bg_Bg (bg_eU e0 e1 m)) : ℝ) * bg_jc N k m P = bg_ak k := by
  rw [show Fintype.card (bg_Bg (bg_eU e0 e1 m)) = bg_jB e0 e1 m from rfl, bg_jB_eq h, bg_jc]
  have hm := h.1
  have hN := bg_j_le h
  obtain ⟨n, rfl⟩ : ∃ n, N = n + (2 * k - m) := ⟨N - (2 * k - m), by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, k = a + m := ⟨k - m, by omega⟩
  have e2 : 2 * (a + m) - m = a + a + m := by omega
  have e3 : n + (a + a + m) - (a + m) = n + a := by omega
  rw [Nat.add_sub_cancel, e2, e3, Nat.add_sub_cancel]
  push_cast
  rw [pow_add]
  field_simp

/-- **Block decomposition** of the field of the first set. -/
theorem bg_j_sum0 (h : bg_JPair k m e0 e1) (w : Param N) (p : Fin (k * 2 ^ k)) :
    (∑ γ, bg_jX h γ w) (gg_jidx k 0 p) =
      (Num w (bg_U e0) (bg_U e0) (bg_pst e0 (gg_pat k p)) (e0 (gg_unit k p)) - bg_ak k) /
        sigN N := by
  have hm : ∀ γ u, merge (bg_U e0) (bg_pst e0 (gg_pat k p)) (bg_jg h (γ, u)) =
      bg_jg h (γ, bg_jρ k m (gg_jidx k 0 p) u) := fun γ u => by
    rw [bg_merge0 h, bg_jρ_jidx0]
  rw [show (∑ γ, bg_jX h γ w) = ∑ γ, bg_X (bg_jg h) (bg_jρ k m) (bg_jj e0 e1) (bg_jc N k m) γ w
    from rfl, bg_sum_X _ _ _ _ _ _ _ hm w, bg_jj_jidx0, bg_j_count h]

/-- **Block decomposition** of the field of the second set. -/
theorem bg_j_sum1 (h : bg_JPair k m e0 e1) (w : Param N) (p : Fin (k * 2 ^ k)) :
    (∑ γ, bg_jX h γ w) (gg_jidx k 1 p) =
      (Num w (bg_U e1) (bg_U e1) (bg_pst e1 (gg_pat k p)) (e1 (gg_unit k p)) - bg_ak k) /
        sigN N := by
  have hm : ∀ γ u, merge (bg_U e1) (bg_pst e1 (gg_pat k p)) (bg_jg h (γ, u)) =
      bg_jg h (γ, bg_jρ k m (gg_jidx k 1 p) u) := fun γ u => by
    rw [bg_merge1 h, bg_jρ_jidx1]
  rw [show (∑ γ, bg_jX h γ w) = ∑ γ, bg_X (bg_jg h) (bg_jρ k m) (bg_jj e0 e1) (bg_jc N k m) γ w
    from rfl, bg_sum_X _ _ _ _ _ _ _ hm w, bg_jj_jidx1, bg_j_count h]

/-! ### The joint covariance -/

lemma bg_corr_split {K : Type*} [DecidableEq K] (ρp ρq : K → K) (jp jq : Fin N) (u : K) :
    bg_corr ρp ρq jp jq u =
      (1 / 2 + (if ρp u = u then (1 : ℝ) else 0) / 4) *
          (1 / 2 + (if ρq u = u then (1 : ℝ) else 0) / 4) +
        (if ρp u = ρq u ∧ jp = jq then 1 / 12 - 11 / 240 * (if ρp u = u then (1 : ℝ) else 0)
          else 0) := by
  unfold bg_corr bg_corr0
  by_cases hs : ρp u = ρq u ∧ jp = jq
  · have h1 := hs.1
    simp only [hs, and_self, ↓reduceIte]
    rw [← h1]
    split_ifs <;> norm_num
  · simp only [hs, ↓reduceIte, add_zero]
    split_ifs <;> norm_num

lemma bg_xtra00 (h : bg_JPair k m e0 e1) (p q : Fin (k * 2 ^ k)) :
    ∑ u : gg_ρ k m, (if bg_jρ k m (gg_jidx k 0 p) u = bg_jρ k m (gg_jidx k 0 q) u ∧
        bg_jj e0 e1 (gg_jidx k 0 p) = bg_jj e0 e1 (gg_jidx k 0 q)
      then 1 / 12 - 11 / 240 * gg_ind k m 0 (gg_pat k p) u else 0) =
      if p = q then (Fintype.card (gg_ρ k m) : ℝ) / 12 - 11 / 240 * 2 ^ (k - m) else 0 := by
  have hc : ∀ u : gg_ρ k m, (bg_jρ k m (gg_jidx k 0 p) u = bg_jρ k m (gg_jidx k 0 q) u ∧
      bg_jj e0 e1 (gg_jidx k 0 p) = bg_jj e0 e1 (gg_jidx k 0 q)) ↔ p = q := by
    intro u
    rw [bg_jρ_jidx0, bg_jρ_jidx0, bg_jj_jidx0, bg_jj_jidx0]
    constructor
    · rintro ⟨h1, h2⟩
      simp only [Prod.mk.injEq] at h1
      exact finProdFinEquiv.symm.injective
        (Prod.ext (h.2.1 h2) (gg_lohi0_inj k m h1.1 h1.2.1))
    · rintro rfl; exact ⟨rfl, rfl⟩
  simp only [hc]
  split_ifs
  · rw [sum_sub_distrib, ← mul_sum, bg_sum_ind]; simp [div_eq_mul_inv]
  · simp

lemma bg_xtra11 (h : bg_JPair k m e0 e1) (p q : Fin (k * 2 ^ k)) :
    ∑ u : gg_ρ k m, (if bg_jρ k m (gg_jidx k 1 p) u = bg_jρ k m (gg_jidx k 1 q) u ∧
        bg_jj e0 e1 (gg_jidx k 1 p) = bg_jj e0 e1 (gg_jidx k 1 q)
      then 1 / 12 - 11 / 240 * gg_ind k m 1 (gg_pat k p) u else 0) =
      if p = q then (Fintype.card (gg_ρ k m) : ℝ) / 12 - 11 / 240 * 2 ^ (k - m) else 0 := by
  have hc : ∀ u : gg_ρ k m, (bg_jρ k m (gg_jidx k 1 p) u = bg_jρ k m (gg_jidx k 1 q) u ∧
      bg_jj e0 e1 (gg_jidx k 1 p) = bg_jj e0 e1 (gg_jidx k 1 q)) ↔ p = q := by
    intro u
    rw [bg_jρ_jidx1, bg_jρ_jidx1, bg_jj_jidx1, bg_jj_jidx1]
    constructor
    · rintro ⟨h1, h2⟩
      simp only [Prod.mk.injEq] at h1
      exact finProdFinEquiv.symm.injective
        (Prod.ext (h.2.2.1 h2) (gg_lohi1_inj k m h1.2.1 h1.2.2))
    · rintro rfl; exact ⟨rfl, rfl⟩
  simp only [hc]
  split_ifs
  · rw [sum_sub_distrib, ← mul_sum, bg_sum_ind]; simp [div_eq_mul_inv]
  · simp

/-- `∑_{x,y,z} [z = c] [x = a] F y = ∑_y F y`. -/
lemma bg_sum_triple {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α]
    [DecidableEq γ] (a : α) (c : γ) (F : β → ℝ) :
    ∑ u : α × β × γ, (if u.2.2 = c then (if u.1 = a then F u.2.1 else 0) else 0) = ∑ y, F y := by
  simp only [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', mem_univ, ↓reduceIte]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', mem_univ, ↓reduceIte]

lemma bg_sum_lin {β : Type*} [Fintype β] [DecidableEq β] (b : β) :
    ∑ y : β, (1 / 12 - 11 / 240 * (if y = b then (1 : ℝ) else 0)) =
      Fintype.card β / 12 - 11 / 240 := by
  rw [sum_sub_distrib, ← mul_sum, Finset.sum_ite_eq']
  simp [div_eq_mul_inv]

/-- The triple sum of `bg_xtra01` and `bg_xtra10`. -/
lemma bg_sum_triple' {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] (a : α) (b : β) (c : γ) :
    ∑ u : α × β × γ, (if u.2.2 = c then (if u.1 = a then
      (1 / 12 - 11 / 240 * if u.2.1 = b then (1 : ℝ) else 0) else 0) else 0) =
      Fintype.card β / 12 - 11 / 240 :=
  (bg_sum_triple a c (fun y => 1 / 12 - 11 / 240 * if y = b then (1 : ℝ) else 0)).trans
    (bg_sum_lin b)

lemma bg_xtra01 (p q : Fin (k * 2 ^ k)) :
    ∑ u : gg_ρ k m, (if bg_jρ k m (gg_jidx k 0 p) u = bg_jρ k m (gg_jidx k 1 q) u ∧
        bg_jj e0 e1 (gg_jidx k 0 p) = bg_jj e0 e1 (gg_jidx k 1 q)
      then 1 / 12 - 11 / 240 * gg_ind k m 0 (gg_pat k p) u else 0) =
      (if e0 (gg_unit k p) = e1 (gg_unit k q) then 1 else 0) *
        (if gg_hi0 k m (gg_pat k p) = gg_lo1 k m (gg_pat k q) then 1 else 0) *
          ((2 : ℝ) ^ m / 12 - 11 / 240) := by
  simp only [bg_jρ_jidx0, bg_jρ_jidx1, bg_jj_jidx0, bg_jj_jidx1]
  set a := gg_lo0 k m (gg_pat k p) with ha
  set b := gg_hi0 k m (gg_pat k p) with hb
  set b' := gg_lo1 k m (gg_pat k q) with hb'
  set c := gg_hi1 k m (gg_pat k q) with hc
  have hpt : ∀ u : gg_ρ k m, (if (a, b, u.2.2) = (u.1, b', c) ∧ e0 (gg_unit k p) = e1 (gg_unit k q)
      then 1 / 12 - 11 / 240 * gg_ind k m 0 (gg_pat k p) u else 0) =
      (if e0 (gg_unit k p) = e1 (gg_unit k q) ∧ b = b' then 1 else 0) *
        (if u.2.2 = c then (if u.1 = a then (1 / 12 - 11 / 240 * if u.2.1 = b then (1 : ℝ) else 0)
          else 0) else 0) := by
    rintro ⟨x, y, z⟩
    simp only [gg_ind, gg_e1, gg_e2, gg_e3, gg_shb, ↓reduceIte, mul_one, Prod.mk.injEq, ← ha, ← hb]
    by_cases hx : x = a <;> by_cases hz : z = c <;>
      by_cases hG : e0 (gg_unit k p) = e1 (gg_unit k q) <;> by_cases hD : b = b' <;>
      simp [hx, hz, hG, hD, eq_comm]
  simp only [hpt]
  rw [← mul_sum, bg_sum_triple', Fintype.card_fin]
  by_cases hG : e0 (gg_unit k p) = e1 (gg_unit k q) <;> by_cases hD : b = b' <;> simp [hG, hD]

lemma bg_xtra10 (p q : Fin (k * 2 ^ k)) :
    ∑ u : gg_ρ k m, (if bg_jρ k m (gg_jidx k 1 p) u = bg_jρ k m (gg_jidx k 0 q) u ∧
        bg_jj e0 e1 (gg_jidx k 1 p) = bg_jj e0 e1 (gg_jidx k 0 q)
      then 1 / 12 - 11 / 240 * gg_ind k m 1 (gg_pat k p) u else 0) =
      (if e1 (gg_unit k p) = e0 (gg_unit k q) then 1 else 0) *
        (if gg_lo1 k m (gg_pat k p) = gg_hi0 k m (gg_pat k q) then 1 else 0) *
          ((2 : ℝ) ^ m / 12 - 11 / 240) := by
  simp only [bg_jρ_jidx0, bg_jρ_jidx1, bg_jj_jidx0, bg_jj_jidx1]
  set a := gg_lo0 k m (gg_pat k q) with ha
  set b := gg_hi0 k m (gg_pat k q) with hb
  set b' := gg_lo1 k m (gg_pat k p) with hb'
  set c := gg_hi1 k m (gg_pat k p) with hc
  have hpt : ∀ u : gg_ρ k m, (if (u.1, b', c) = (a, b, u.2.2) ∧ e1 (gg_unit k p) = e0 (gg_unit k q)
      then 1 / 12 - 11 / 240 * gg_ind k m 1 (gg_pat k p) u else 0) =
      (if e1 (gg_unit k p) = e0 (gg_unit k q) ∧ b' = b then 1 else 0) *
        (if u.2.2 = c then (if u.1 = a then (1 / 12 - 11 / 240 * if u.2.1 = b' then (1 : ℝ) else 0)
          else 0) else 0) := by
    rintro ⟨x, y, z⟩
    simp only [gg_ind, gg_e1, gg_e2, gg_e3, gg_shb, ↓reduceIte, one_mul, Prod.mk.injEq,
      show (1 : Fin 2) ≠ 0 by decide, ← hb', ← hc]
    by_cases hx : x = a <;> by_cases hz : z = c <;>
      by_cases hG : e1 (gg_unit k p) = e0 (gg_unit k q) <;> by_cases hD : b' = b <;>
      simp [hx, hz, hG, hD, eq_comm]
  simp only [hpt]
  rw [← mul_sum, bg_sum_triple', Fintype.card_fin]
  by_cases hG : e1 (gg_unit k p) = e0 (gg_unit k q) <;> by_cases hD : b' = b <;> simp [hG, hD]

lemma bg_sum_A (w w' : Fin 2) (t t' : Fin (2 ^ k)) :
    ∑ u : gg_ρ k m, (1 / 2 + gg_ind k m w t u / 4) * (1 / 2 + gg_ind k m w' t' u / 4) =
      Fintype.card (gg_ρ k m) / 4 + 2 ^ (k - m) / 4 +
        (∑ u, gg_ind k m w t u * gg_ind k m w' t' u) / 16 := by
  have e : ∀ u : gg_ρ k m, (1 / 2 + gg_ind k m w t u / 4) * (1 / 2 + gg_ind k m w' t' u / 4) =
      1 / 4 + gg_ind k m w t u / 8 + gg_ind k m w' t' u / 8 +
        gg_ind k m w t u * gg_ind k m w' t' u / 16 := fun u => by ring
  simp only [e, sum_add_distrib, ← sum_div, bg_sum_ind, sum_const, card_univ, nsmul_eq_mul]
  ring

lemma bg_glob01 (h : bg_JPair k m e0 e1) (p q : Fin (k * 2 ^ k)) :
    e0 (gg_unit k p) = e1 (gg_unit k q) ↔
      gg_glob k m (gg_jidx k 0 p) = gg_glob k m (gg_jidx k 1 q) := by
  rw [h.2.2.2]
  simp only [gg_glob, gg_jw_jidx, gg_jp_jidx, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide, zero_add]
  omega

lemma bg_glob10 (h : bg_JPair k m e0 e1) (p q : Fin (k * 2 ^ k)) :
    e1 (gg_unit k p) = e0 (gg_unit k q) ↔
      gg_glob k m (gg_jidx k 1 p) = gg_glob k m (gg_jidx k 0 q) := by
  rw [eq_comm, h.2.2.2]
  simp only [gg_glob, gg_jw_jidx, gg_jp_jidx, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide, zero_add]
  omega

lemma bg_jidx_eq (w : Fin 2) (p q : Fin (k * 2 ^ k)) :
    gg_jidx k w p = gg_jidx k w q ↔ p = q :=
  ⟨fun e => by simpa using congrArg (gg_jp k) e, fun e => e ▸ rfl⟩

/-- **The limit covariance is `gg_CJ`**: the correlation sum of two joint coordinates, divided by
the number `2^(2k-m)` of rows of a superblock, is exactly the joint covariance of `GaussGen`. -/
theorem bg_j_corr (h : bg_JPair k m e0 e1) (P Q : Fin (2 * (k * 2 ^ k))) :
    ((Fintype.card (gg_ρ k m) : ℝ))⁻¹ *
        ∑ u, bg_corr (bg_jρ k m P) (bg_jρ k m Q) (bg_jj e0 e1 P) (bg_jj e0 e1 Q) u =
      gg_CJ k m P Q := by
  obtain ⟨⟨w, p⟩, rfl⟩ := finProdFinEquiv.surjective P
  obtain ⟨⟨w', q⟩, rfl⟩ := finProdFinEquiv.surjective Q
  change _ * ∑ u, bg_corr (bg_jρ k m (gg_jidx k w p)) (bg_jρ k m (gg_jidx k w' q))
    (bg_jj e0 e1 (gg_jidx k w p)) (bg_jj e0 e1 (gg_jidx k w' q)) u =
      gg_CJ k m (gg_jidx k w p) (gg_jidx k w' q)
  simp only [bg_corr_split, sum_add_distrib, bg_jind, gg_jw_jidx, gg_jp_jidx]
  rw [bg_sum_A, gg_sum_ind_mul]
  have hm := h.1
  have hK : (Fintype.card (gg_ρ k m) : ℝ) = 2 ^ k * 2 ^ (k - m) := by
    rw [bg_card_ρ hm]; push_cast; exact gg_pow_split k m hm
  have hK' : ((2 : ℝ) ^ (2 * k - m)) = 2 ^ k * 2 ^ (k - m) := gg_pow_split k m hm
  have h2m : (2 : ℝ) ^ k = 2 ^ (k - m) * 2 ^ m := by
    rw [← pow_add]; congr 1; omega
  have hp1 : (0 : ℝ) < 2 ^ (k - m) := by positivity
  have hp2 : (0 : ℝ) < 2 ^ m := by positivity
  rcases gg_fin2 w with rfl | rfl <;> rcases gg_fin2 w' with rfl | rfl
  · rw [bg_xtra00 h]
    simp only [gg_CJ, gg_jw_jidx, gg_jp_jidx, ↓reduceIte, bg_jidx_eq, gg_c0, gg_c1, gg_c2, hK]
    split_ifs <;> field_simp <;> ring
  · rw [bg_xtra01]
    simp only [gg_CJ, gg_jw_jidx, gg_jp_jidx, ↓reduceIte, show (0 : Fin 2) ≠ 1 by decide,
      gg_c0, gg_beta, gg_alpha, gg_shb, show (1 : Fin 2) ≠ 0 by decide, ← bg_glob01 h, hK, hK']
    rw [h2m]
    split_ifs <;> field_simp <;> ring
  · rw [bg_xtra10]
    simp only [gg_CJ, gg_jw_jidx, gg_jp_jidx, ↓reduceIte,
      gg_c0, gg_beta, gg_alpha, gg_shb, show (1 : Fin 2) ≠ 0 by decide, ← bg_glob10 h, hK, hK']
    rw [h2m]
    split_ifs <;> field_simp <;> ring
  · rw [bg_xtra11 h]
    simp only [gg_CJ, gg_jw_jidx, gg_jp_jidx, ↓reduceIte, bg_jidx_eq, gg_c0, gg_c1, gg_c2, hK]
    split_ifs <;> field_simp <;> ring

/-! ### Law and moments of the superblock summands -/

/-- The family of superblock summands, indexed by `Fin (bg_jB e0 e1 m)`. -/
def bg_jXs (h : bg_JPair k m e0 e1) (w : Param N) :
    Fin (bg_jB e0 e1 m) → Fin (2 * (k * 2 ^ k)) → ℝ :=
  bg_Xs (bg_jg h) (bg_jρ k m) (bg_jj e0 e1) (bg_jc N k m) w

lemma bg_j_sum_Xs (h : bg_JPair k m e0 e1) (w : Param N) :
    ∑ b, bg_jXs h w b = ∑ γ, bg_jX h γ w :=
  bg_sum_Xs _ _ _ _ w

/-- **Law of the superblock summands**: iid with law `bg_jnu e0 e1 m`. -/
theorem bg_j_map_Xs (h : bg_JPair k m e0 e1) :
    (cubeM N).map (bg_jXs h) = Measure.pi fun _ : Fin (bg_jB e0 e1 m) => bg_jnu e0 e1 m :=
  bg_map_Xs _ _ _ _

/-- **Zero means**. -/
theorem bg_jnu_mean (h : bg_JPair k m e0 e1) (P : Fin (2 * (k * 2 ^ k))) :
    ∫ x, x P ∂bg_jnu e0 e1 m = 0 :=
  bg_nu_mean (bg_j_hc h) P

/-- **Second moments**: `|2^(N-(2k-m)) ∫ x P x Q dν - C_J[P,Q]| ≤ 2^(2k-m) (3/4)^N`. -/
theorem bg_jnu_second (h : bg_JPair k m e0 e1) (P Q : Fin (2 * (k * 2 ^ k))) :
    |(bg_jB e0 e1 m : ℝ) * ∫ x, x P * x Q ∂bg_jnu e0 e1 m - gg_CJ k m P Q| ≤
      2 ^ (2 * k - m) * (3 / 4 : ℝ) ^ N := by
  have hh := bg_nu_second (j := bg_jj e0 e1) (bg_j_hc h) (bg_jB_mul h) P Q
  rw [bg_j_corr h, bg_card_ρ h.1] at hh
  push_cast at hh
  exact hh

/-- **Second moments** with `2^(N-(2k-m)) - 1` summands. -/
theorem bg_jnu_second_pred (h : bg_JPair k m e0 e1) (P Q : Fin (2 * (k * 2 ^ k))) :
    |((bg_jB e0 e1 m - 1 : ℕ) : ℝ) * ∫ x, x P * x Q ∂bg_jnu e0 e1 m - gg_CJ k m P Q| ≤
      3 * ((2 : ℝ) ^ (2 * k - m)) ^ 2 * (3 / 4 : ℝ) ^ N := by
  have hh := bg_nu_second_pred (j := bg_jj e0 e1) (bg_j_hc h) (bg_jB_mul h) P Q
  rw [bg_j_corr h, bg_card_ρ h.1] at hh
  push_cast at hh
  exact hh

/-- Integrability of the third absolute moment. -/
theorem bg_jnu_integrable3 (h : bg_JPair k m e0 e1) :
    Integrable (fun x => (∑ P, |x P|) ^ 3) (bg_jnu e0 e1 m) :=
  bg_nu_integrable3 (bg_j_hc h)

/-- **Third moments**: `2^(N-(2k-m)) ∫ (∑ |x P|)^3 dν ≤ 8 (2 k 2^k)^3 (2^(2k-m))^2 (23/25)^N`. -/
theorem bg_jnu_third (h : bg_JPair k m e0 e1) :
    (bg_jB e0 e1 m : ℝ) * ∫ x, (∑ P, |x P|) ^ 3 ∂bg_jnu e0 e1 m ≤
      8 * (2 * ((k : ℝ) * 2 ^ k)) ^ 3 * ((2 : ℝ) ^ (2 * k - m)) ^ 2 * (23 / 25 : ℝ) ^ N := by
  have hh := bg_nu_third (j := bg_jj e0 e1) (bg_j_hc h) (bg_jB_mul h)
  rw [Fintype.card_fin, bg_card_ρ h.1] at hh
  push_cast at hh
  exact hh

/-! ### Removing the superblock of a state -/

/-- The summands of the superblocks other than the superblock of `s`. -/
def bg_jXr (h : bg_JPair k m e0 e1) (s : State N) (w : Param N) :
    Fin (bg_jB e0 e1 m - 1) → Fin (2 * (k * 2 ^ k)) → ℝ :=
  bg_Xr (bg_jg h) (bg_jρ k m) (bg_jj e0 e1) (bg_jc N k m) s w

/-- **Law of the remaining summands**: iid with law `bg_jnu e0 e1 m`. -/
theorem bg_j_map_Xr (h : bg_JPair k m e0 e1) (s : State N) :
    (cubeM N).map (bg_jXr h s) =
      Measure.pi fun _ : Fin (bg_jB e0 e1 m - 1) => bg_jnu e0 e1 m :=
  bg_map_Xr _ _ _ _ s

/-- The joint field is the sum of the remaining summands plus the summand of the superblock of
`s`. -/
theorem bg_j_sum_eq_rest (h : bg_JPair k m e0 e1) (s : State N) (w : Param N) :
    ∑ γ, bg_jX h γ w = ∑ b, bg_jXr h s w b + bg_jX h ((bg_jg h).symm s).1 w :=
  bg_sum_eq_rest _ _ _ _ s w

/-- **Removing the superblock of `s`** changes every coordinate by at most `2^(2k-m) τ_N / σ_N`
on `g2`. -/
theorem bg_j_abs_sub_rest_le (h : bg_JPair k m e0 e1) (s : State N) {w : Param N}
    (h2 : ∀ i r, Qw w i r ≤ tauN N) (P : Fin (2 * (k * 2 ^ k))) :
    |(∑ γ, bg_jX h γ w) P - (∑ b, bg_jXr h s w b) P| ≤ 2 ^ (2 * k - m) * tauN N / sigN N := by
  have hh := bg_abs_sub_rest_le (bg_jg h) (j := bg_jj e0 e1) (bg_j_hc h) s h2 P
  rw [bg_card_ρ h.1] at hh
  push_cast at hh
  exact hh

/-- The rows of the superblock of `s`. -/
def bg_jblockRows (h : bg_JPair k m e0 e1) (s : State N) (w : Param N) :
    gg_ρ k m → Fin N → ℝ :=
  bg_blockRows (bg_jg h) s w

/-- **Independence**: the remaining summands are independent of the rows of the superblock of
`s`. -/
theorem bg_j_indep_rest (h : bg_JPair k m e0 e1) (s : State N) :
    IndepFun (bg_jblockRows h s) (bg_jXr h s) (cubeM N) :=
  bg_indep_rest _ _ _ _ s

/-- The rows of the superblock of `s` are the rows agreeing with `s` off the union. -/
lemma bg_j_blockRows_eq (h : bg_JPair k m e0 e1) (s : State N) (u : gg_ρ k m) (j : Fin N)
    (hj : j ∉ bg_U (bg_eU e0 e1 m)) : bg_jg h (((bg_jg h).symm s).1, u) j = s j := by
  have h1 : bg_jg h (((bg_jg h).symm s).1, ((bg_jg h).symm s).2) = s :=
    (bg_jg h).apply_symm_apply s
  have h2 := congrFun h1 j
  simp only [bg_jg, bg_eqv_apply] at h2 ⊢
  rw [bg_row_out _ _ _ hj] at h2 ⊢
  exact h2

end Joint

end

end Census
end IIT
