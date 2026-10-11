/-
Census, B1, W14 work package WP3 (effect side), part 4: the one-unit purview `{k1}` (W5 Lemma E3'(i)).
* the effect repertoires of `T = tpmOf (flipP s w)` in te orientation (`effUnit_te`, `effUnit_nte`);
* the deviation at `M \ {j}` is the mean of `f` and `h_j` (`effDevA_erase`);
* `far_bound` and `dle_far` (W9 4.2: the D-conditions for `r > r_D` from FE1');
* `dev_all`: the D-condition `dev_A < a (1 - r/m) - κ_N/2` for EVERY nonempty `A ⊊ M`;
* `eff_maxStates_single`, `eff_phi_single`, `eff_phi_single_ge`.
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §8.  No `sorry`.
-/
import IIT.Census.B1CntEffGen
import IIT.Census.B1CntEffConst
import IIT.Census.B1CntEffSys

namespace IIT
namespace Census

/-! Helpers live in `IIT.Census.WP3` (avoids name clashes with the other work packages);
the blueprint names are re-exported to `IIT.Census` by `alias` at the end of the file. -/
namespace WP3

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### Effect repertoires in te orientation -/

lemma effUnit_te (s : State N) (w : Param N) (A : Finset (Fin N)) (t : State N) (k : Fin N) :
    effUnit (tpmOf (flipP s w)) A t k (teW w s k) = 1 / 2 + effDevA w s A t k := by
  have := effUnit_flipP_teW s w A t k; linarith

lemma effUnit_nte (s : State N) (w : Param N) (A : Finset (Fin N)) (t : State N) (k : Fin N) :
    effUnit (tpmOf (flipP s w)) A t k (!teW w s k) = 1 / 2 - effDevA w s A t k := by
  have h1 := effUnit_add (tpmOf (flipP s w)) A t k
  have h2 := effUnit_te s w A t k
  cases h : teW w s k <;> simp only [h, Bool.not_false, Bool.not_true] at h2 ⊢ <;> linarith

/-- The sign of a bit relative to `te` is the same for every subcube. -/
lemma effUnit_sign (s : State N) (w : Param N) (k : Fin N) (b : Bool) :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ ∀ (A : Finset (Fin N)) (t : State N),
      effUnit (tpmOf (flipP s w)) A t k b = 1 / 2 + c * effDevA w s A t k := by
  by_cases hb : b = teW w s k
  · refine ⟨1, Or.inl rfl, fun A t => ?_⟩
    rw [hb, effUnit_te]; ring
  · have hb' : b = !teW w s k := by cases b <;> cases h : teW w s k <;> simp_all
    refine ⟨-1, Or.inr rfl, fun A t => ?_⟩
    rw [hb', effUnit_nte]; ring

lemma effUnit_pos_flip {s : State N} {w : Param N} (hz : flipP s w ∈ openCube N)
    (A : Finset (Fin N)) (t : State N) (k : Fin N) (b : Bool) :
    0 < effUnit (tpmOf (flipP s w)) A t k b := by
  unfold effUnit
  exact div_pos (sum_pos (fun r _ => prob_pos hz k r b) (agree_nonempty A t))
    (Nat.cast_pos.2 (card_agree_pos A t))

/-! ### `r = 1`: the subcube `agree (M \ {j}) s` -/

lemma agree_erase_eq {M : Finset (Fin N)} {j : Fin N} (hj : j ∈ M) (t : State N) :
    agree (M.erase j) t = agree M t ∪ agree M (flipAt j t) := by
  ext r
  simp only [mem_union, mem_agree, mem_erase]
  constructor
  · intro h
    by_cases hrj : r j = t j
    · left; intro i hi
      by_cases hij : i = j
      · rw [hij]; exact hrj
      · exact h i ⟨hij, hi⟩
    · right; intro i hi
      unfold flipAt
      by_cases hij : i = j
      · subst hij; rw [Function.update_self]; cases h1 : r i <;> cases h2 : t i <;> simp_all
      · rw [Function.update_of_ne hij]; exact h i ⟨hij, hi⟩
  · rintro (h | h) i ⟨hij, hi⟩
    · exact h i hi
    · have := h i hi; unfold flipAt at this; rwa [Function.update_of_ne hij] at this

lemma agree_flip_disjoint {M : Finset (Fin N)} {j : Fin N} (hj : j ∈ M) (t : State N) :
    Disjoint (agree M t) (agree M (flipAt j t)) := by
  rw [disjoint_left]
  intro r h1 h2
  rw [mem_agree] at h1 h2
  have e1 := h1 j hj
  have e2 := h2 j hj
  unfold flipAt at e2
  rw [Function.update_self] at e2
  rw [e1] at e2
  cases h : t j <;> simp [h] at e2

lemma effDevA_erase (w : Param N) (s : State N) {M : Finset (Fin N)} {j : Fin N} (hj : j ∈ M)
    (t : State N) (k : Fin N) :
    effDevA w s (M.erase j) t k = (effDevA w s M t k + effDevA w s M (flipAt j t) k) / 2 := by
  have hM : M.card ≤ N := by simpa using card_le_univ M
  have hM1 : 1 ≤ M.card := card_pos.2 ⟨j, hj⟩
  have hc1 : ((agree M t).card : ℝ) = 2 ^ (N - M.card) := by rw [card_agree]; push_cast; ring
  have hc2 : ((agree M (flipAt j t)).card : ℝ) = 2 ^ (N - M.card) := by
    rw [card_agree]; push_cast; ring
  have hc3 : ((agree (M.erase j) t).card : ℝ) = 2 * 2 ^ (N - M.card) := by
    rw [card_agree, card_erase_of_mem hj, show N - (M.card - 1) = N - M.card + 1 by omega]
    push_cast; ring
  unfold effDevA
  rw [hc1, hc2, hc3, agree_erase_eq hj, sum_union (agree_flip_disjoint hj t)]
  rw [← add_div, div_div, mul_comm (2 : ℝ)]

/-! ### The far D-conditions (W9 4.2, W5 D' last paragraph) -/

lemma dX_le_N {N : ℕ} (hN : 1 ≤ N) : dX N ≤ N := by unfold dX; omega

lemma log_le_N (N : ℕ) : Real.log N ≤ N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · exact (Real.log_le_sub_one_of_pos (by exact_mod_cast h)).trans (by linarith)

theorem far_bound (hC : EffC N) (D : ℕ) (hD1 : dX N + rD N ≤ D) (hDN : D ≤ N) :
    2 * Real.sqrt ((N : ℝ) / 2 ^ D) + 2 * ((D + 1 : ℕ) : ℝ) ^ 4 / 2 ^ D + kapN N / 2 <
      sigC N / N := by
  have hN := hC.hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  set σ := sigC N with hσdef
  have hσ0 : 0 < σ := sigC_pos N
  set d := dX N with hddef
  have hdN : (d : ℝ) ≤ N := by exact_mod_cast dX_le_N (show 1 ≤ N by omega)
  have hσ2 : 1 / (2 : ℝ) ^ d = 12 * σ ^ 2 := inv_two_pow_dX N
  set P : ℝ := 1024 * ((N : ℝ) + 1) ^ 3 with hP
  have hPpos : 0 < P := by positivity
  have h2D : (2 : ℝ) ^ d * P ≤ 2 ^ D := by
    have h1 : ((1024 * (N + 1) ^ 3 : ℕ) : ℝ) ≤ ((2 ^ rD N : ℕ) : ℝ) := by
      exact_mod_cast rD_pow N (by omega)
    push_cast at h1
    calc (2 : ℝ) ^ d * P ≤ 2 ^ d * 2 ^ rD N := by rw [hP]; gcongr
      _ = 2 ^ (d + rD N) := by rw [pow_add]
      _ ≤ 2 ^ D := pow_le_pow_right₀ (by norm_num) hD1
  have hQ : 0 < (2 : ℝ) ^ D := by positivity
  have hinv : 1 / (2 : ℝ) ^ D ≤ 12 * σ ^ 2 / P := by
    rw [← hσ2, div_div, one_div_le_one_div hQ (by positivity)]; exact h2D
  -- the square-root term
  have hs1 : (N : ℝ) / 2 ^ D ≤ (σ / (8 * N)) ^ 2 := by
    have : (N : ℝ) / 2 ^ D ≤ N * (12 * σ ^ 2 / P) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hinv (by positivity)
    refine this.trans ?_
    rw [div_pow, mul_pow, hP, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : (N : ℝ) ^ 3 ≤ ((N : ℝ) + 1) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    have hσ2' : 0 ≤ σ ^ 2 := sq_nonneg σ
    nlinarith [mul_le_mul_of_nonneg_left h3 hσ2']
  have hs : Real.sqrt ((N : ℝ) / 2 ^ D) ≤ σ / (8 * N) :=
    Real.sqrt_le_iff.2 ⟨by positivity, hs1⟩
  -- the polynomial term
  have hp1 : ((D + 1 : ℕ) : ℝ) ^ 4 / 2 ^ D ≤ ((N : ℝ) + 1) * σ ^ 2 / 80 := by
    have hD' : ((D + 1 : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by
      have : D + 1 ≤ N + 1 := by omega
      exact_mod_cast this
    have h4 : ((D + 1 : ℕ) : ℝ) ^ 4 ≤ ((N : ℝ) + 1) ^ 4 := pow_le_pow_left₀ (by positivity) hD' 4
    calc ((D + 1 : ℕ) : ℝ) ^ 4 / 2 ^ D = ((D + 1 : ℕ) : ℝ) ^ 4 * (1 / 2 ^ D) := by ring
      _ ≤ ((N : ℝ) + 1) ^ 4 * (12 * σ ^ 2 / P) := by gcongr
      _ = 12 * ((N : ℝ) + 1) * σ ^ 2 / 1024 := by rw [hP]; field_simp
      _ ≤ ((N : ℝ) + 1) * σ ^ 2 / 80 := by
          have : 0 ≤ ((N : ℝ) + 1) * σ ^ 2 := by positivity
          linarith
  -- κ_N
  have hk : kapN N ≤ 128 * (N : ℝ) ^ 2 * σ ^ 2 := by
    rw [kapN_eq]
    have hL := log_le_N N
    have hε := hC.hεσ
    have hd2 : (d : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hdN 2
    have hσ2' : 0 ≤ σ ^ 2 := sq_nonneg σ
    nlinarith [mul_le_mul_of_nonneg_right hL hσ2', mul_le_mul_of_nonneg_right hd2 hσ2',
      mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (N : ℝ) ^ 2 by nlinarith) hσ2',
      mul_le_mul_of_nonneg_right (show (N : ℝ) ≤ (N : ℝ) ^ 2 by nlinarith) hσ2']
  have hσN := hC.hσ
  -- assemble
  have e1 : 2 * (σ / (8 * N)) = σ / (4 * N) := by field_simp; ring
  have hfin : σ / (4 * N) + 2 * (((N : ℝ) + 1) * σ ^ 2 / 80) + 64 * (N : ℝ) ^ 2 * σ ^ 2 <
      σ / N := by
    rw [← sub_pos]
    have e2 : σ / N - (σ / (4 * N) + 2 * (((N : ℝ) + 1) * σ ^ 2 / 80) + 64 * (N : ℝ) ^ 2 * σ ^ 2)
        = σ / N * (3 / 4 - (((N : ℝ) + 1) * N * σ / 40 + 64 * (N : ℝ) ^ 3 * σ)) := by
      field_simp; ring
    rw [e2]
    refine mul_pos (by positivity) ?_
    have h1 : ((N : ℝ) + 1) * N * σ ≤ 2 * (N : ℝ) ^ 3 * σ := by
      have : ((N : ℝ) + 1) * N ≤ 2 * (N : ℝ) ^ 3 := by nlinarith
      nlinarith
    nlinarith
  calc 2 * Real.sqrt ((N : ℝ) / 2 ^ D) + 2 * ((D + 1 : ℕ) : ℝ) ^ 4 / 2 ^ D + kapN N / 2
      ≤ 2 * (σ / (8 * N)) + 2 * (((N : ℝ) + 1) * σ ^ 2 / 80) + 64 * (N : ℝ) ^ 2 * σ ^ 2 := by
        have : 2 * ((D + 1 : ℕ) : ℝ) ^ 4 / 2 ^ D = 2 * (((D + 1 : ℕ) : ℝ) ^ 4 / 2 ^ D) := by ring
        rw [this]
        linarith
    _ < σ / N := by rw [e1]; exact hfin

/-! ### Hypotheses shared by the single-purview lemmas -/

/-- The data of a counted `K` at its coin unit `k` (W5 6.2 at `κ = 0`, sign `+`). -/
structure CoinAt (N : ℕ) (s : State N) (K : Finset (Fin N)) (k : Fin N) (w : Param N) : Prop where
  card : K.card = dX N
  mem : k ∈ K
  core : CoreAt N s K k 0 w
  posf : 0 < fK w s K k

lemma mX_eq_card {K : Finset (Fin N)} (hK : K.card = dX N) :
    mX N = ((univ \ K).card : ℝ) := by
  unfold mX; rw [card_univ_sdiff, Fintype.card_fin, hK]

lemma sgnMul_of_pos {a b : ℝ} (ha : 0 < a) : sgnMul a b = b := by unfold sgnMul; rw [if_pos ha]

/-- **The D-condition for every nonempty `A ⊊ M`** (`r = 1` from (N), `2 ≤ r ≤ r_D` from `D≤`,
`r > r_D` from FE1'). -/
theorem dev_all (hC : EffC N) {s : State N} {K : Finset (Fin N)} {k : Fin N} {w : Param N}
    (hc : CoinAt N s K k w) (hD : DleAt N s K k w)
    (hsub : ∀ A : Finset (Fin N), A.card + D0C N ≤ N →
      |effDevA w s A s k| ≤ 2 * Real.sqrt ((N : ℝ) / 2 ^ (N - A.card)) +
        2 * ((N - A.card + 1 : ℕ) : ℝ) ^ 4 / 2 ^ (N - A.card))
    (A : Finset (Fin N)) (hA : A ⊆ univ \ K) (hAne : A.Nonempty) (hAM : A ≠ univ \ K) :
    effDevA w s A s k <
      fK w s K k * (1 - (((univ \ K) \ A).card : ℝ) / mX N) - kapN N / 2 := by
  set M := univ \ K with hMdef
  set f := fK w s K k with hfdef
  have hf := hc.posf
  have habs : |f| = f := abs_of_pos hf
  have hMcard : M.card = N - dX N := by rw [hMdef, card_univ_sdiff, Fintype.card_fin, hc.card]
  have hm := mX_eq_card hc.card
  rw [← hMdef] at hm
  have hr1 : 1 ≤ (M \ A).card := by
    rcases Nat.eq_zero_or_pos (M \ A).card with h | h
    · exfalso; apply hAM
      exact Subset.antisymm hA (fun i hi => by
        by_contra hiA
        have : i ∈ M \ A := mem_sdiff.2 ⟨hi, hiA⟩
        rw [card_eq_zero.1 h] at this; exact absurd this (notMem_empty i))
    · exact h
  have hsd : (M \ A).card = M.card - A.card := card_sdiff_of_subset hA
  have hA1 : 1 ≤ A.card := card_pos.2 hAne
  have hAleM : A.card ≤ M.card := card_le_card hA
  rcases Nat.lt_or_ge 1 (M \ A).card with hr2 | hr2
  · rcases Nat.lt_or_ge (rD N) (M \ A).card with hfar | hnear
    · -- far: FE1'
      have hNA : N - A.card = dX N + (M \ A).card := by omega
      have hb := hsub A (by have := hC.hD0; omega)
      have hfb := far_bound hC (N - A.card) (by omega) (by omega)
      have hdevle : effDevA w s A s k ≤ |effDevA w s A s k| := le_abs_self _
      -- `σ/N ≤ f (1 - r/m)`
      have hkey : sigC N / N ≤ f * (1 - (((M \ A).card : ℝ)) / mX N) := by
        have hmpos : (0 : ℝ) < mX N := by
          rw [hm]; exact_mod_cast (show 0 < M.card by omega)
        have hmN : mX N ≤ N := by
          rw [hm]; exact_mod_cast (show M.card ≤ N by omega)
        have hfac : 1 - (((M \ A).card : ℝ)) / mX N = (A.card : ℝ) / mX N := by
          have hM0 : ((M.card : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
          rw [hm, hsd, Nat.cast_sub hAleM, sub_div, div_self hM0]; ring
        rw [hfac]
        have hA1' : (1 : ℝ) ≤ A.card := by exact_mod_cast hA1
        have hfσ : sigC N ≤ f := by
          have h1 := hc.core.1
          have h2 := A0C_ge hC.hL1
          have h3 := kapN_nonneg (by linarith [hC.hL1] : (0 : ℝ) ≤ Real.log N)
          rw [habs] at h1; linarith
        have hσ0 := sigC_pos N
        calc sigC N / N ≤ sigC N / mX N := div_le_div_of_nonneg_left hσ0.le hmpos hmN
          _ ≤ f * (A.card : ℝ) / mX N := by
              apply div_le_div_of_nonneg_right _ hmpos.le
              nlinarith
          _ = f * ((A.card : ℝ) / mX N) := by ring
      linarith
    · -- `2 ≤ r ≤ r_D`: the event `D≤`
      have h := hD A hA hAne hr2 hnear
      rwa [sgnMul_of_pos hf, habs] at h
  · -- `r = 1`: the condition (N)
    have hr : (M \ A).card = 1 := by omega
    obtain ⟨j, hj⟩ := card_eq_one.1 hr
    have hjM : j ∈ M := (mem_sdiff.1 (hj ▸ mem_singleton_self j)).1
    have hAe : A = M.erase j := by
      ext i
      simp only [mem_erase]
      constructor
      · intro hi
        refine ⟨fun hij => ?_, hA hi⟩
        have : j ∈ M \ A := hj ▸ mem_singleton_self j
        exact (mem_sdiff.1 this).2 (hij ▸ hi)
      · rintro ⟨hij, hiM⟩
        by_contra hiA
        have : i ∈ M \ A := mem_sdiff.2 ⟨hiM, hiA⟩
        rw [hj, mem_singleton] at this; exact hij this
    rw [hr, hAe, effDevA_erase w s hjM]
    have hN' := hc.core.2.2.2 j hjM
    rw [sgnMul_of_pos hf, habs] at hN'
    have e1 : effDevA w s M s k = f := rfl
    have e2 : effDevA w s M (flipAt j s) k = hK w s K j k := rfl
    rw [e1, e2]
    push_cast
    have : (2 : ℝ) / mX N = 2 * (1 / mX N) := by ring
    nlinarith

/-- The blueprint form of the far D-conditions. -/
theorem dle_far : ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N),
    GoodW3 N s r0 x σ w → CountFreshX N s r0 w → ∀ K ∈ famX3 N s r0 x σ w, ∀ k ∈ K,
      CoreAt N s K k 0 w → ∀ A : Finset (Fin N), A ⊆ univ \ K → A.Nonempty →
        rD N < ((univ \ K) \ A).card →
        sgnMul (fK w s K k) (effDevA w s A s k) <
          |fK w s K k| * (1 - (((univ \ K) \ A).card : ℝ) / mX N) - kapN N / 2 := by
  filter_upwards [ev_effC, eff_subDev] with N hC hsub s r0 x σ w hg hfr K hK k hk hcore A hA
    hAne hfar
  -- the bound holds for `|sgnMul f dev| = |dev|`, whatever the sign of `f`
  have hcK := famX3_card hK
  set M := univ \ K with hMdef
  have hMcard : M.card = N - dX N := by rw [hMdef, card_univ_sdiff, Fintype.card_fin, hcK]
  have hm := mX_eq_card hcK
  rw [← hMdef] at hm
  have hsd : (M \ A).card = M.card - A.card := card_sdiff_of_subset hA
  have hAleM : A.card ≤ M.card := card_le_card hA
  have hA1 : 1 ≤ A.card := card_pos.2 hAne
  have hNA : N - A.card = dX N + (M \ A).card := by omega
  have hb := hsub s r0 x σ w hg hfr A s k (by have := hC.hD0; omega)
  have hfb := far_bound hC (N - A.card) (by omega) (by omega)
  have hsg : sgnMul (fK w s K k) (effDevA w s A s k) ≤ |effDevA w s A s k| := by
    unfold sgnMul; split_ifs
    · exact le_abs_self _
    · exact neg_le_abs _
  have hkey : sigC N / N ≤ |fK w s K k| * (1 - (((M \ A).card : ℝ)) / mX N) := by
    have hmpos : (0 : ℝ) < mX N := by
      rw [hm]; exact_mod_cast (show 0 < M.card by omega)
    have hmN : mX N ≤ N := by
      rw [hm]; exact_mod_cast (show M.card ≤ N by omega)
    have hfac : 1 - (((M \ A).card : ℝ)) / mX N = (A.card : ℝ) / mX N := by
      have hM0 : ((M.card : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      rw [hm, hsd, Nat.cast_sub hAleM, sub_div, div_self hM0]; ring
    rw [hfac]
    have hA1' : (1 : ℝ) ≤ A.card := by exact_mod_cast hA1
    have hfσ : sigC N ≤ |fK w s K k| := by
      have h1 := hcore.1
      have h2 := A0C_ge hC.hL1
      have h3 := kapN_nonneg (by linarith [hC.hL1] : (0 : ℝ) ≤ Real.log N)
      linarith
    have hσ0 := sigC_pos N
    calc sigC N / N ≤ sigC N / mX N := div_le_div_of_nonneg_left hσ0.le hmpos hmN
      _ ≤ |fK w s K k| * (A.card : ℝ) / mX N := by
          apply div_le_div_of_nonneg_right _ hmpos.le
          nlinarith
      _ = |fK w s K k| * ((A.card : ℝ) / mX N) := by ring
  linarith

end WP3

alias dle_far := WP3.dle_far

end Census
end IIT

#print axioms IIT.Census.WP3.dev_all
#print axioms IIT.Census.dle_far
