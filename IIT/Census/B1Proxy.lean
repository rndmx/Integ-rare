/-
Census, module B1UnivMIP part 6: the proxy lemma (blueprint v2 §8 G2), cause side.

If unit `x` fails `SmallCutGood` on the cause side (`M^c({x}) ≤ 7·D0U`, in bits) and the half-means
are within `deltaU N` of `1/2`, then the F-data lie in the certified regime event `RegEvX` (the
tilt and link conjuncts are supplied by the forcing).  Three facts:
* `λᶜⱼ({x}) · ln 2 = lamX_j`: the subcube free on `{x}` through `tc` is `{tc, tc^x}`;
* `(Fⱼ - λ_min) · ln 2 ≥ max(0, ln(yⱼ / c_m)) - 7δ` for a cell `(m_lo, c_m)` holding `y_min`;
* the 61 certified cells cover `[0.499999, 1]`.
-/
import IIT.Census.B1DefsX
import IIT.Census.B1UnivMIP
import IIT.Census.PairCause

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-! ### The cell table covers `[0.499999, 1]` -/

lemma chain_cover : ∀ (l : List (ℚ × ℚ)) (c : ℚ × ℚ),
    List.IsChain (fun a b => b.1 ≤ a.2) (c :: l) → ∀ v : ℝ, (c.1 : ℝ) ≤ v →
      v ≤ ((c :: l).getLast (List.cons_ne_nil _ _)).2 → ∃ d ∈ c :: l, (d.1 : ℝ) ≤ v ∧ v ≤ d.2
  | [], c, _, v, h1, h2 => ⟨c, List.mem_singleton_self c, h1, by simpa using h2⟩
  | d :: l, c, hch, v, h1, h2 => by
    by_cases hv : v ≤ c.2
    · exact ⟨c, List.mem_cons_self, h1, hv⟩
    · push Not at hv
      have hcd : d.1 ≤ c.2 := (List.isChain_cons_cons.1 hch).1
      have hd1 : (d.1 : ℝ) ≤ v := le_trans (by exact_mod_cast hcd) hv.le
      obtain ⟨e, he, he1, he2⟩ :=
        chain_cover l d (List.isChain_cons_cons.1 hch).2 v hd1 (by simpa using h2)
      exact ⟨e, List.mem_cons_of_mem _ he, he1, he2⟩

lemma cellsXCause_chain : List.IsChain (fun a b : ℚ × ℚ => b.1 ≤ a.2) cellsXCauseData := by
  unfold cellsXCauseData; norm_num

lemma cellsXCause_cover (v : ℝ) (h1 : 499999 / 1000000 ≤ v) (h2 : v ≤ 1) :
    ∃ c ∈ cellsX .cause, (c.1 : ℝ) ≤ v ∧ v ≤ c.2 := by
  have hch := cellsXCause_chain
  unfold cellsXCauseData at hch
  obtain ⟨c, hc, hc1, hc2⟩ := chain_cover _ _ hch v (by norm_num; linarith)
    (by norm_num; linarith)
  refine ⟨c, ?_, hc1, hc2⟩
  unfold cellsX cellsXCauseData
  exact List.mem_toFinset.2 hc

/-! ### The single cut from `x` -/

lemma cmean_compl_single (w : Param N) (t : State N) (x j : Fin N) :
    cmean w (univ \ {x}) t j = (clamp01 (w t j) + clamp01 (w (flipAt x t) j)) / 2 := by
  unfold cmean
  have h1 : (univ \ {x} : Finset (Fin N)) = {x}ᶜ := by ext; simp
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (by have := x.2; omega)
  rw [h1, agree_compl_single, sum_pair (flip_ne t x), card_compl, card_singleton,
    Fintype.card_fin, show N - (N - 1) = 1 by omega, pow_one]
  rfl

lemma lamCz_single_eq {z : Param N} (hz : z ∈ openCube N) (s tc : State N) (x j : Fin N) :
    lamCz z s tc j {x} * Real.log 2 = lamX (flipP s z) s tc x .cause j := by
  obtain ⟨hl, -, hx0, -, -⟩ := lamCz_means hz s tc
  have hU : 0 < clamp01 (flipP s z (flipAt x tc) j) := by
    rw [← y_eq_clamp]; exact y_pos hz s _ j
  rw [hl, cmean_compl_single, Real.logb, div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne']
  unfold lamX baseE compE
  congr 1
  have := hx0 j
  field_simp

/-! ### The truncation -/

lemma kF_lamCz {z : Param N} (hz : z ∈ openCube N) (s tc : State N) (j : Fin N) :
    kF (lamCz z s tc) j = Real.logb 2 (clamp01 (flipP s z tc j) / cmean (flipP s z) {j} tc j) := by
  obtain ⟨hl, -⟩ := lamCz_means hz s tc
  unfold kF
  rw [hl, show (univ \ univ.erase j : Finset (Fin N)) = {j} by ext; simp]

lemma trunc_le {z : Param N} (hz : z ∈ openCube N) (s tc : State N) {δ lc0 cm : ℝ}
    (hq : ∀ j, |cmean (flipP s z) {j} tc j - 1 / 2| ≤ δ) (hδ : δ ≤ 1 / 100)
    (hmin : ∀ j, lc0 ≤ kF (lamCz z s tc) j) {k : Fin N}
    (hk : clamp01 (flipP s z tc k) ≤ cm) (j : Fin N) :
    max 0 (Real.log (clamp01 (flipP s z tc j) / cm)) - 7 * δ ≤
      (kF (lamCz z s tc) j - lc0) * Real.log 2 := by
  obtain ⟨-, -, hx0, -, -⟩ := lamCz_means hz s tc
  have hl2 := Real.log_pos one_lt_two
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hq j)
  have hq0 : ∀ i, 0 < cmean (flipP s z) {i} tc i := fun i => cmean_pos hz s _ tc i
  have hF0 : 0 ≤ (kF (lamCz z s tc) j - lc0) * Real.log 2 :=
    mul_nonneg (sub_nonneg.2 (hmin j)) hl2.le
  -- `F_j - F_k = log₂(y_j / y_k) + log₂(q_k / q_j)`
  have hsplit : kF (lamCz z s tc) j - kF (lamCz z s tc) k =
      Real.logb 2 (clamp01 (flipP s z tc j) / clamp01 (flipP s z tc k)) +
        Real.logb 2 (cmean (flipP s z) {k} tc k / cmean (flipP s z) {j} tc j) := by
    rw [kF_lamCz hz, kF_lamCz hz, ← Real.logb_div (div_pos (hx0 j) (hq0 j)).ne'
      (div_pos (hx0 k) (hq0 k)).ne', ← Real.logb_mul (div_pos (hx0 j) (hx0 k)).ne'
      (div_pos (hq0 k) (hq0 j)).ne']
    congr 1
    have := hq0 j; have := hq0 k; have := hx0 k
    field_simp
  have hqq := logb_ratio_ge (hq k) (hq j) hδ (hq0 j)
  have hcm0 : 0 < cm := lt_of_lt_of_le (hx0 k) hk
  have hyy : Real.log (clamp01 (flipP s z tc j) / cm) ≤
      Real.log (clamp01 (flipP s z tc j) / clamp01 (flipP s z tc k)) :=
    Real.log_le_log (div_pos (hx0 j) hcm0) (div_le_div_of_nonneg_left (hx0 j).le (hx0 k) hk)
  have hconv : Real.logb 2 (clamp01 (flipP s z tc j) / clamp01 (flipP s z tc k)) * Real.log 2 =
      Real.log (clamp01 (flipP s z tc j) / clamp01 (flipP s z tc k)) := by
    rw [Real.logb, div_mul_cancel₀ _ hl2.ne']
  have hmk := hmin k
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  rcases le_total (Real.log (clamp01 (flipP s z tc j) / cm)) 0 with hneg | hpos
  · rw [max_eq_left hneg]; linarith
  · rw [max_eq_right hpos]
    have : (kF (lamCz z s tc) j - lc0) * Real.log 2 ≥
        (kF (lamCz z s tc) j - kF (lamCz z s tc) k) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hl2.le
    rw [hsplit, add_mul, hconv] at this
    nlinarith [mul_le_mul_of_nonneg_right hqq hl2.le]

/-! ### The proxy lemma -/

/-- **Proxy lemma, cause side** (blueprint v2 §8 G2 (a)-(c)). -/
theorem regEv_of_fail_cause {z : Param N} (hz : z ∈ openCube N) (s tc : State N) (x : Fin N)
    {lc0 : ℝ} (hP : 0 < lc0) (hmin : ∀ j, lc0 ≤ kF (lamCz z s tc) j)
    (hq : ∀ j, |cmean (flipP s z) {j} tc j - 1 / 2| ≤ deltaU N)
    (hδ : deltaU N ≤ 1 / 1000000)
    (hfail : kM (lamCz z s tc) lc0 {x} ≤ 7 * (D0U N : ℝ))
    (hT : XW (flipP s z) tc ≤ x0 * N + slT N)
    (hL : ∑ k, -Real.log (xE (flipP s z) s k) ≤ XW (flipP s z) tc + slT N) :
    RegEvX N s tc x .cause (flipP s z) := by
  obtain ⟨-, -, hx0, -, -⟩ := lamCz_means hz s tc
  set y : Fin N → ℝ := fun j => clamp01 (flipP s z tc j) with hy
  obtain ⟨k, -, hkmin⟩ := exists_min_image univ y ⟨x, mem_univ x⟩
  -- `y_min ≥ 1/2 - δ`: from `F_k > 0`
  have hyk : 499999 / 1000000 ≤ y k := by
    have hF : 0 < kF (lamCz z s tc) k := lt_of_lt_of_le hP (hmin k)
    rw [kF_lamCz hz] at hF
    have hq0 := cmean_pos hz s {k} tc k
    have h1 : cmean (flipP s z) {k} tc k < y k := by
      by_contra h; push Not at h
      exact absurd hF (not_lt.2 (Real.logb_nonpos one_lt_two (div_pos (hx0 k) hq0).le
        ((div_le_one hq0).2 h)))
    have := (abs_le.1 (hq k)).1
    linarith
  obtain ⟨c, hc, hc1, hc2⟩ := cellsXCause_cover (y k) hyk (clamp01_le_one _)
  refine ⟨c, hc, fun j => hc1.trans (hkmin j (mem_univ j)), ⟨k, hc2⟩, hT, hL, ?_, fun h => nomatch h⟩
  -- the V-sum
  have hl2 := Real.log_pos one_lt_two
  have htr := fun j => trunc_le hz s tc hq (by linarith) hmin (k := k) hc2 j
  have hcompl : ({x}ᶜ : Finset (Fin N)) = univ.erase x := by ext; simp
  calc ∑ j ∈ univ.erase x, min (lamX (flipP s z) s tc x .cause j)
        (max 0 (Real.log (baseE (flipP s z) s tc x .cause j / (c.2 : ℝ))) - 7 * deltaU N)
      ≤ ∑ j ∈ univ.erase x, min (lamCz z s tc j {x}) (kF (lamCz z s tc) j - lc0) *
          Real.log 2 := by
        refine sum_le_sum fun j _ => ?_
        rw [min_mul_of_nonneg _ _ hl2.le, lamCz_single_eq hz]
        exact min_le_min le_rfl (htr j)
    _ = Real.log 2 * kM (lamCz z s tc) lc0 {x} := by
        rw [kM, hcompl, mul_sum]; exact sum_congr rfl fun j _ => by ring
    _ ≤ Real.log 2 * (7 * (D0U N : ℝ)) := mul_le_mul_of_nonneg_left hfail hl2.le
    _ ≤ slV N := by
        unfold slV
        have : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
        have hD : (0 : ℝ) ≤ D0U N := Nat.cast_nonneg _
        nlinarith

/-! ### Effect side -/

lemma cellsXEffect_chain : List.IsChain (fun a b : ℚ × ℚ => b.1 ≤ a.2) cellsXEffectData := by
  unfold cellsXEffectData; norm_num

lemma cellsXEffect_cover (v : ℝ) (h1 : 499999 / 1000000 ≤ v) (h2 : v ≤ 1) :
    ∃ c ∈ cellsX .effect, (c.1 : ℝ) ≤ v ∧ v ≤ c.2 := by
  have hch := cellsXEffect_chain
  unfold cellsXEffectData at hch
  obtain ⟨c, hc, hc1, hc2⟩ := chain_cover _ _ hch v (by norm_num; linarith)
    (by norm_num; linarith)
  refine ⟨c, ?_, hc1, hc2⟩
  unfold cellsX cellsXEffectData
  exact List.mem_toFinset.2 hc

/-- The truncation bound for any side of the form `λⱼ(C) = log₂(xⱼ / Aⱼ(C))`. -/
lemma trunc_gen {lam : Fin N → Finset (Fin N) → ℝ} {x : Fin N → ℝ}
    {A : Fin N → Finset (Fin N) → ℝ} {δ lc0 cm : ℝ}
    (hlam : ∀ j C, lam j C = Real.logb 2 (x j / A j C)) (hx0 : ∀ j, 0 < x j)
    (hA0 : ∀ j C, 0 < A j C) (hq : ∀ j, |A j (univ.erase j) - 1 / 2| ≤ δ) (hδ : δ ≤ 1 / 100)
    (hmin : ∀ j, lc0 ≤ kF lam j) {k : Fin N} (hk : x k ≤ cm) (j : Fin N) :
    max 0 (Real.log (x j / cm)) - 7 * δ ≤ (kF lam j - lc0) * Real.log 2 := by
  have hl2 := Real.log_pos one_lt_two
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hq j)
  have hq0 : ∀ i, 0 < A i (univ.erase i) := fun i => hA0 i _
  have hF0 : 0 ≤ (kF lam j - lc0) * Real.log 2 := mul_nonneg (sub_nonneg.2 (hmin j)) hl2.le
  have hsplit : kF lam j - kF lam k = Real.logb 2 (x j / x k) +
      Real.logb 2 (A k (univ.erase k) / A j (univ.erase j)) := by
    unfold kF
    rw [hlam, hlam, ← Real.logb_div (div_pos (hx0 j) (hq0 j)).ne' (div_pos (hx0 k) (hq0 k)).ne',
      ← Real.logb_mul (div_pos (hx0 j) (hx0 k)).ne' (div_pos (hq0 k) (hq0 j)).ne']
    congr 1
    have := hq0 j; have := hq0 k; have := hx0 k
    field_simp
  have hqq := logb_ratio_ge (hq k) (hq j) hδ (hq0 j)
  have hcm0 : 0 < cm := lt_of_lt_of_le (hx0 k) hk
  have hyy : Real.log (x j / cm) ≤ Real.log (x j / x k) :=
    Real.log_le_log (div_pos (hx0 j) hcm0) (div_le_div_of_nonneg_left (hx0 j).le (hx0 k) hk)
  have hconv : Real.logb 2 (x j / x k) * Real.log 2 = Real.log (x j / x k) := by
    rw [Real.logb, div_mul_cancel₀ _ hl2.ne']
  have hmk := hmin k
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  rcases le_total (Real.log (x j / cm)) 0 with hneg | hpos
  · rw [max_eq_left hneg]; linarith
  · rw [max_eq_right hpos]
    have : (kF lam j - lc0) * Real.log 2 ≥ (kF lam j - kF lam k) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hl2.le
    rw [hsplit, add_mul, hconv] at this
    nlinarith [mul_le_mul_of_nonneg_right hqq hl2.le]

lemma prob_teW_row (z : Param N) (s r : State N) (j : Fin N) :
    (tpmOf z).prob j r (teW (flipP s z) s j) = pTe (flipP s z) s r j := by
  unfold teW pTe
  split_ifs with h
  · exact prob_eq_clamp z s r j
  · have h1 := (tpmOf z).normalized j r
    have h2 := prob_eq_clamp z s r j
    cases hs : s j <;> simp_all <;> linarith

lemma xE_eq_pTe (w : Param N) (s : State N) (j : Fin N) : xE w s j = pTe w s s j := by
  unfold xE pTe
  split_ifs with h
  · exact max_eq_left (by linarith)
  · exact max_eq_right (by push Not at h; linarith)

lemma lamEz_single_eq {z : Param N} (hz : z ∈ openCube N) (s : State N) (x j : Fin N) :
    lamEz z s (teW (flipP s z) s) j {x} * Real.log 2 =
      lamX (flipP s z) s (teW (flipP s z) s) x .effect j := by
  obtain ⟨hl, -, hx0, -, -⟩ := lamEz_means hz s (teW (flipP s z) s)
  have hU : 0 < (tpmOf z).prob j (flip s x) (teW (flipP s z) s j) := prob_pos hz j _ _
  rw [hl, effUnit_compl_single, Real.logb, div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne']
  simp only [lamX, baseE, compE]
  rw [xE_eq_pTe, ← prob_teW_row, ← prob_teW_row]
  congr 1
  have := hx0 j
  have : flip s x = flipAt x s := rfl
  rw [this] at hU ⊢
  field_simp

/-- **Proxy lemma, effect side** (blueprint v2 §8 G2). -/
theorem regEv_of_fail_effect {z : Param N} (hz : z ∈ openCube N) (s r0 : State N) (x : Fin N)
    {le0 : ℝ} (hmin : ∀ j, le0 ≤ kF (lamEz z s (teW (flipP s z) s)) j)
    (hq : ∀ j, |effUnit (tpmOf z) (univ.erase j)ᶜ s j (teW (flipP s z) s j) - 1 / 2| ≤ deltaU N)
    (hδ : deltaU N ≤ 1 / 1000000)
    (hfail : kM (lamEz z s (teW (flipP s z) s)) le0 {x} ≤ 7 * (D0U N : ℝ))
    (hT : XW (flipP s z) r0 ≤ x0 * N + slT N)
    (hL : ∑ k, -Real.log (xE (flipP s z) s k) ≤ XW (flipP s z) r0 + slT N)
    (hfloor : ∀ j, 1 / 2 - deltaU N ≤ clamp01 (flipP s z r0 j)) :
    RegEvX N s r0 x .effect (flipP s z) := by
  set te := teW (flipP s z) s
  obtain ⟨hl, -, hx0, hA0, -⟩ := lamEz_means hz s te
  have hxv : ∀ j, (tpmOf z).prob j s (te j) = xE (flipP s z) s j := fun j => by
    exact prob_teW z s j
  set xv : Fin N → ℝ := fun j => (tpmOf z).prob j s (te j)
  obtain ⟨k, -, hkmin⟩ := exists_min_image univ xv ⟨x, mem_univ x⟩
  have hyk : 499999 / 1000000 ≤ xv k := by
    show 499999 / 1000000 ≤ (tpmOf z).prob k s (te k)
    rw [hxv k]
    have : 1 / 2 ≤ xE (flipP s z) s k := by
      unfold xE; rcases le_total (clamp01 (flipP s z s k)) (1 / 2) with h | h
      · exact le_max_of_le_right (by linarith)
      · exact le_max_of_le_left h
    linarith
  obtain ⟨c, hc, hc1, hc2⟩ :=
    cellsXEffect_cover (xv k) hyk ((tpmOf z).le_one k s _)
  refine ⟨c, hc, fun j => ?_, ⟨k, ?_⟩, hT, hL, ?_, fun _ => hfloor⟩
  · show (c.1 : ℝ) ≤ xE (flipP s z) s j
    rw [← hxv]; exact hc1.trans (hkmin j (mem_univ j))
  · show xE (flipP s z) s k ≤ (c.2 : ℝ)
    rw [← hxv]; exact hc2
  have hl2 := Real.log_pos one_lt_two
  have htr := fun j => trunc_gen (lam := lamEz z s te) (x := xv)
    (A := fun j C => effUnit (tpmOf z) Cᶜ s j (te j)) hl hx0 hA0 hq (by linarith) hmin
    (k := k) hc2 j
  have hcompl : ({x}ᶜ : Finset (Fin N)) = univ.erase x := by ext; simp
  calc ∑ j ∈ univ.erase x, min (lamX (flipP s z) s r0 x .effect j)
        (max 0 (Real.log (baseE (flipP s z) s r0 x .effect j / (c.2 : ℝ))) - 7 * deltaU N)
      ≤ ∑ j ∈ univ.erase x, min (lamEz z s te j {x}) (kF (lamEz z s te) j - le0) *
          Real.log 2 := by
        refine sum_le_sum fun j _ => ?_
        rw [min_mul_of_nonneg _ _ hl2.le, lamEz_single_eq hz]
        refine min_le_min (le_of_eq ?_) ?_
        · rfl
        · have := htr j
          simp only [xv, hxv] at this
          simpa only [baseE] using this
    _ = Real.log 2 * kM (lamEz z s te) le0 {x} := by
        rw [kM, hcompl, mul_sum]; exact sum_congr rfl fun j _ => by ring
    _ ≤ Real.log 2 * (7 * (D0U N : ℝ)) := mul_le_mul_of_nonneg_left hfail hl2.le
    _ ≤ slV N := by
        unfold slV
        have : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
        have hD : (0 : ℝ) ≤ D0U N := Nat.cast_nonneg _
        nlinarith

end Census
end IIT
