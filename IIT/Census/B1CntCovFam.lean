/-
Census, B1, W14 work package WP6 (part 1): the family `famX3` as a core family, its size
(`FamBigStmt`), and a generic `log²`-absorption lemma.
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §11 (G-W14-2, F3).  No `sorry`.
-/
import IIT.Census.B1CntBasics

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### Absorption of `exp(O(log² N))` factors -/

/-- `A log² N + B ≤ ε N` eventually. -/
lemma cov_ev_logsq (A B ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, A * Real.log N ^ 2 + B ≤ ε * N := by
  have hlo := Real.isLittleO_pow_log_id_atTop (n := 2)
  have hev : ∀ᶠ x : ℝ in atTop, A * Real.log x ^ 2 + B ≤ ε * x := by
    have h1 := hlo.def (c := ε / (2 * (|A| + 1))) (by positivity)
    filter_upwards [h1, eventually_ge_atTop (2 * |B| / ε), eventually_ge_atTop 0] with x hx hx1 hx0
    simp only [Real.norm_eq_abs, id, abs_of_nonneg hx0] at hx
    have hsq : |Real.log x ^ 2| = Real.log x ^ 2 := abs_of_nonneg (sq_nonneg _)
    rw [hsq] at hx
    have h2 : A * Real.log x ^ 2 ≤ (|A| + 1) * Real.log x ^ 2 := by
      have := le_abs_self A; nlinarith [sq_nonneg (Real.log x)]
    have h3 : (|A| + 1) * Real.log x ^ 2 ≤ ε * x / 2 := by
      calc (|A| + 1) * Real.log x ^ 2 ≤ (|A| + 1) * (ε / (2 * (|A| + 1)) * x) := by gcongr
        _ = ε * x / 2 := by field_simp
    have h4 : 2 * |B| ≤ ε * x := by rw [div_le_iff₀ hε] at hx1; linarith
    have := le_abs_self B
    linarith
  exact tendsto_natCast_atTop_atTop.eventually hev

lemma cov_log_le_sq (N : ℕ) : Real.log N ≤ Real.log N ^ 2 + 1 := by
  nlinarith [sq_nonneg (Real.log N - 1 / 2)]

/-! ### The core family -/

/-- The core family `{K ⊆ P ∪ L : |K| = d, L ⊆ K}` has `C(|P|, d - |L|)` members. -/
theorem card_core_fam (P L : Finset (Fin N)) (hPL : Disjoint P L) (d : ℕ) (hLd : L.card ≤ d) :
    (((P ∪ L).powersetCard d).filter fun K => L ⊆ K).card = P.card.choose (d - L.card) := by
  rw [← card_powersetCard (d - L.card) P]
  symm
  refine card_bij (fun K₀ _ => K₀ ∪ L) ?_ ?_ ?_
  · intro K₀ hK₀
    rw [mem_powersetCard] at hK₀
    rw [mem_filter, mem_powersetCard]
    refine ⟨⟨union_subset_union hK₀.1 subset_rfl, ?_⟩, subset_union_right⟩
    rw [card_union_of_disjoint (disjoint_of_subset_left hK₀.1 hPL), hK₀.2]
    omega
  · intro a ha b hb hab
    rw [mem_powersetCard] at ha hb
    have h1 : (a ∪ L) \ L = a := union_sdiff_cancel_right (disjoint_of_subset_left ha.1 hPL)
    have h2 : (b ∪ L) \ L = b := union_sdiff_cancel_right (disjoint_of_subset_left hb.1 hPL)
    rw [← h1, ← h2]
    exact congrArg (· \ L) hab
  · intro K hK
    rw [mem_filter, mem_powersetCard] at hK
    refine ⟨K \ L, ?_, sdiff_union_of_subset hK.2⟩
    rw [mem_powersetCard]
    constructor
    · exact sdiff_le_iff.2 (le_of_le_of_eq hK.1.1 (union_comm P L))
    · rw [card_sdiff_of_subset hK.2, hK.1.2]

/-- **`famX3` is a core family** with core `lowU` and pool `P`. -/
theorem famX3_eq_core (s r0 : State N) (x : Fin N) (σ : XSide) (w : Param N) :
    ∃ P : Finset (Fin N), Disjoint P (lowU N w r0) ∧
      (σ = .cause → NegX w r0 x ⊆ P ∪ lowU N w r0) ∧ (σ = .effect → P ∪ lowU N w r0 = univ) ∧
      famX3 N s r0 x σ w =
        ((P ∪ lowU N w r0).powersetCard (dX N)).filter fun K => lowU N w r0 ⊆ K := by
  cases σ with
  | cause =>
    refine ⟨NegX w r0 x \ lowU N w r0, sdiff_disjoint, fun _ => ?_, fun h => absurd h (by simp), ?_⟩
    · rw [sdiff_union_self_eq_union]; exact subset_union_left
    · rw [sdiff_union_self_eq_union]
      simp only [famX3]
  | effect =>
    refine ⟨univ \ lowU N w r0, sdiff_disjoint, fun h => absurd h (by simp), fun _ => ?_, ?_⟩
    · rw [sdiff_union_self_eq_union]; ext; simp
    · rw [sdiff_union_self_eq_union, show univ ∪ lowU N w r0 = univ by ext; simp]
      simp only [famX3]

/-- The pool and core of `famX3` on good data: `N ≤ 4(|P| + |L|)`, `1000 |L| ≤ N`. -/
theorem famX3_core_good {s r0 : State N} {x : Fin N} {σ : XSide} {w : Param N}
    (hx2 : σ = .cause → N ≤ 4 * (NegX w r0 x).card) :
    ∃ P : Finset (Fin N), Disjoint P (lowU N w r0) ∧ N ≤ 4 * (P.card + (lowU N w r0).card) ∧
      famX3 N s r0 x σ w =
        ((P ∪ lowU N w r0).powersetCard (dX N)).filter fun K => lowU N w r0 ⊆ K := by
  obtain ⟨P, hd, hc, he, hf⟩ := famX3_eq_core s r0 x σ w
  refine ⟨P, hd, ?_, hf⟩
  rw [← card_union_of_disjoint hd]
  cases σ with
  | cause => exact (hx2 rfl).trans (Nat.mul_le_mul_left 4 (card_le_card (hc rfl)))
  | effect => rw [he rfl, card_univ, Fintype.card_fin]; omega

/-! ### Binomial lower bounds -/

lemma choose_le_add_add (n k t : ℕ) (h : k ≤ n) : n.choose k ≤ (n + t).choose (k + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hs : (n + t + 1) * (n + t).choose (k + t) =
        (n + t + 1).choose (k + t + 1) * (k + t + 1) := Nat.add_one_mul_choose_eq _ _
    have h2 : (n + t + 1) * (n + t).choose (k + t) ≤
        (n + t + 1) * (n + t + 1).choose (k + t + 1) := by
      rw [hs]; nlinarith [Nat.zero_le ((n + t + 1).choose (k + t + 1))]
    have h1 := Nat.le_of_mul_le_mul_left h2 (by omega)
    calc n.choose k ≤ (n + t).choose (k + t) := ih
      _ ≤ (n + t + 1).choose (k + t + 1) := h1

/-- `k! ≤ e √k (k/e)^k` (Stirling's sequence is antitone, `stirlingSeq 1 = e/√2`). -/
lemma factorial_le_stirling_up (k : ℕ) (hk : 0 < k) :
    (k.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt k * ((k : ℝ) / Real.exp 1) ^ k := by
  have h : Stirling.stirlingSeq k ≤ Stirling.stirlingSeq 1 := by
    have := Stirling.stirlingSeq'_antitone (Nat.zero_le (k - 1))
    simp only [Function.comp, Nat.succ_eq_add_one, zero_add, Nat.sub_add_cancel hk] at this
    exact this
  rw [Stirling.stirlingSeq_one] at h
  unfold Stirling.stirlingSeq at h
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < Real.sqrt (2 * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k := by positivity
  rw [div_le_iff₀ hpos] at h
  have hs : Real.sqrt (2 * (k : ℝ)) = Real.sqrt 2 * Real.sqrt k := Real.sqrt_mul (by norm_num) _
  rw [hs] at h
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  calc (k.factorial : ℝ) ≤ Real.exp 1 / Real.sqrt 2 *
        (Real.sqrt 2 * Real.sqrt k * ((k : ℝ) / Real.exp 1) ^ k) := h
    _ = Real.exp 1 * Real.sqrt k * ((k : ℝ) / Real.exp 1) ^ k := by field_simp

/-- **`C(n,k) ≥ (n-k)^k/k! ≥ (n-k)^k e^k/(e √k k^k)`** (G-W14-2). -/
theorem choose_ge_stirling (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    ((n - k : ℕ) : ℝ) ^ k * Real.exp k / (Real.exp 1 * Real.sqrt k * (k : ℝ) ^ k) ≤ n.choose k := by
  have hd : ((n - k : ℕ) : ℝ) ^ k ≤ (n.descFactorial k : ℝ) := by
    have h1 := Nat.pow_sub_le_descFactorial n k
    have h2 : (n - k) ^ k ≤ (n + 1 - k) ^ k := Nat.pow_le_pow_left (by omega) k
    exact_mod_cast h2.trans h1
  have hc : (n.descFactorial k : ℝ) = k.factorial * n.choose k := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose n k
  have hf := factorial_le_stirling_up k hk
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have he : ((k : ℝ) / Real.exp 1) ^ k = (k : ℝ) ^ k / Real.exp k := by
    rw [div_pow, ← Real.exp_one_pow]
  rw [he] at hf
  have hE : 0 < Real.exp (k : ℝ) := Real.exp_pos _
  have hC : (0 : ℝ) ≤ n.choose k := by positivity
  rw [div_le_iff₀ (by positivity)]
  have h3 : ((n - k : ℕ) : ℝ) ^ k ≤ (n.choose k : ℝ) *
      (Real.exp 1 * Real.sqrt k * ((k : ℝ) ^ k / Real.exp k)) := by
    calc ((n - k : ℕ) : ℝ) ^ k ≤ k.factorial * n.choose k := hd.trans hc.le
      _ ≤ (Real.exp 1 * Real.sqrt k * ((k : ℝ) ^ k / Real.exp k)) * n.choose k := by gcongr
      _ = _ := by ring
  have h4 : (n.choose k : ℝ) * (Real.exp 1 * Real.sqrt k * ((k : ℝ) ^ k / Real.exp k)) *
      Real.exp k = n.choose k * (Real.exp 1 * Real.sqrt k * (k : ℝ) ^ k) := by
    field_simp
  calc ((n - k : ℕ) : ℝ) ^ k * Real.exp k ≤ (n.choose k : ℝ) *
        (Real.exp 1 * Real.sqrt k * ((k : ℝ) ^ k / Real.exp k)) * Real.exp k := by gcongr
    _ = _ := h4

/-! ### `FamBigStmt` -/

lemma famBig_poly : ∀ᶠ N : ℕ in atTop, 36000 * (N : ℝ) ^ 3 ≤ (2 : ℝ) ^ (N / 250) := by
  filter_upwards [cov_ev_logsq 3 (3 + Real.log 36000) (1 / 500) (by norm_num),
    eventually_ge_atTop 1000] with N hN h1000
  have hNr : (1000 : ℝ) ≤ N := by exact_mod_cast h1000
  have hNpos : (0 : ℝ) < N := by linarith
  have hl2 : (0.6931 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hdiv : ((N / 250 : ℕ) : ℝ) ≥ (N : ℝ) / 250 - 1 := by
    have h := Nat.div_add_mod N 250
    have hm := Nat.mod_lt N (by norm_num : 250 > 0)
    have : (N : ℝ) = 250 * ((N / 250 : ℕ) : ℝ) + ((N % 250 : ℕ) : ℝ) := by exact_mod_cast h.symm
    have hm' : ((N % 250 : ℕ) : ℝ) ≤ 249 := by exact_mod_cast (by omega : N % 250 ≤ 249)
    linarith
  have hlogN := cov_log_le_sq N
  have hkey : Real.log 36000 + 3 * Real.log N ≤ ((N / 250 : ℕ) : ℝ) * Real.log 2 := by
    have h5 : ((N : ℝ) / 250 - 1) * 0.6931 ≤ ((N / 250 : ℕ) : ℝ) * Real.log 2 := by
      have h6 : (0 : ℝ) ≤ (N : ℝ) / 250 - 1 := by linarith
      calc ((N : ℝ) / 250 - 1) * 0.6931 ≤ ((N / 250 : ℕ) : ℝ) * 0.6931 := by gcongr
        _ ≤ ((N / 250 : ℕ) : ℝ) * Real.log 2 := by gcongr
    nlinarith
  have hl : Real.log (36000 * (N : ℝ) ^ 3) ≤ Real.log ((2 : ℝ) ^ (N / 250)) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; linarith
  exact (Real.log_le_log_iff (by positivity) (by positivity)).1 hl

/-- **WP6: the family is big** (G-W14-2, F3): `|famX3| pY/4 ≥ 2^{N/8} + 2N`. -/
theorem famBig_proved : FamBigStmt := by
  filter_upwards [famBig_poly, eventually_ge_atTop 1000] with N hpoly hN s r0 x σ w hg
  obtain ⟨P, hdisj, hn1, hfam⟩ := famX3_core_good (s := s) (σ := σ) hg.1.x2
  have hlow := hg.2.lowFew
  set ℓ := (lowU N w r0).card with hℓ
  set d := dX N with hd
  have hdN : d = (N + 29) / 30 := rfl
  have hℓd : ℓ ≤ d := by omega
  have hcard : (famX3 N s r0 x σ w).card = P.card.choose (d - ℓ) := by
    rw [hfam]; exact card_core_fam P _ hdisj d hℓd
  set ℓm := N / 1000 with hℓm
  set a := P.card + ℓ - ℓm with ha
  set b := d - ℓm with hb
  have hba : b ≤ a := by omega
  have hb0 : 0 < b := by omega
  have hmono : a.choose b ≤ P.card.choose (d - ℓ) := by
    have e1 : P.card = a + (ℓm - ℓ) := by omega
    have e2 : d - ℓ = b + (ℓm - ℓ) := by omega
    rw [e1, e2]; exact choose_le_add_add a b _ hba
  have hst := choose_ge_stirling a b hb0 hba
  -- numerical facts
  have hNr : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hab60 : ((13 * N - 58 : ℕ) : ℝ) ≤ 60 * ((a - b : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 13 * N - 58 ≤ 60 * (a - b))
  have hab60' : (13 : ℝ) * N - 58 ≤ 60 * ((a - b : ℕ) : ℝ) := by
    have : ((13 * N - 58 : ℕ) : ℝ) = 13 * (N : ℝ) - 58 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    linarith
  have hb3000 : 3000 * (b : ℝ) ≤ 97 * N + 5897 := by
    exact_mod_cast (by omega : 3000 * b ≤ 97 * N + 5897)
  have hbN : (b : ℝ) ≤ N := by exact_mod_cast (by omega : b ≤ N)
  have he27 : (2.7 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have he3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9; linarith
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb0
  have hratio : 16 * (b : ℝ) ≤ ((a - b : ℕ) : ℝ) * Real.exp 1 := by
    have h0 : (0 : ℝ) ≤ ((a - b : ℕ) : ℝ) := by positivity
    nlinarith
  -- `C(a,b) ≥ 16^b/(e N)`
  have hpowb : (16 : ℝ) ^ b ≤ (((a - b : ℕ) : ℝ) * Real.exp 1 / b) ^ b := by
    gcongr
    rw [le_div_iff₀ hbpos]; linarith
  have hsq : Real.sqrt b ≤ N := by
    rw [Real.sqrt_le_left (by positivity)]
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb0
    nlinarith
  have hlow2 : (16 : ℝ) ^ b / (3 * N) ≤ (a.choose b : ℝ) := by
    refine le_trans ?_ hst
    have e1 : ((a - b : ℕ) : ℝ) ^ b * Real.exp b / (Real.exp 1 * Real.sqrt b * (b : ℝ) ^ b) =
        (((a - b : ℕ) : ℝ) * Real.exp 1 / b) ^ b / (Real.exp 1 * Real.sqrt b) := by
      rw [div_pow, mul_pow, ← Real.exp_one_pow]
      field_simp
    rw [e1]
    have hden : Real.exp 1 * Real.sqrt b ≤ 3 * N := by
      have : 0 ≤ Real.sqrt b := Real.sqrt_nonneg _
      nlinarith
    have hden0 : 0 < Real.exp 1 * Real.sqrt b := by positivity
    calc (16 : ℝ) ^ b / (3 * N) ≤ (16 : ℝ) ^ b / (Real.exp 1 * Real.sqrt b) := by gcongr
      _ ≤ _ := by gcongr
  -- `16^b ≥ 2^{N/8} 2^{N/250}`
  have h16 : (2 : ℝ) ^ (N / 8) * (2 : ℝ) ^ (N / 250) ≤ (16 : ℝ) ^ b := by
    rw [← pow_add, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  -- assemble
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogN' : Real.log N ≤ N := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hpY : pY N = 1 / (1000 * Real.log N) := rfl
  rw [hcard, hpY]
  have hfam_ge : (2 : ℝ) ^ (N / 8) * (12000 * (N : ℝ) ^ 2) ≤ (P.card.choose (d - ℓ) : ℝ) := by
    have hm : (a.choose b : ℝ) ≤ P.card.choose (d - ℓ) := by exact_mod_cast hmono
    refine le_trans ?_ (hlow2.trans hm)
    rw [le_div_iff₀ (by positivity)]
    have h2p : (0 : ℝ) ≤ (2 : ℝ) ^ (N / 8) := by positivity
    calc (2 : ℝ) ^ (N / 8) * (12000 * (N : ℝ) ^ 2) * (3 * N) =
          (2 : ℝ) ^ (N / 8) * (36000 * (N : ℝ) ^ 3) := by ring
      _ ≤ (2 : ℝ) ^ (N / 8) * (2 : ℝ) ^ (N / 250) := by gcongr
      _ ≤ _ := h16
  have hL : (LCnt N : ℝ) ≤ (2 : ℝ) ^ (N / 8) * (3 * N) := by
    unfold LCnt; push_cast
    have : (1 : ℝ) ≤ (2 : ℝ) ^ (N / 8) := one_le_pow₀ (by norm_num)
    nlinarith
  rw [show (P.card.choose (d - ℓ) : ℝ) * (1 / (1000 * Real.log N)) / 4 =
      (P.card.choose (d - ℓ) : ℝ) / (4000 * Real.log N) by field_simp; ring]
  rw [le_div_iff₀ (by positivity)]
  have h2p : (0 : ℝ) ≤ (2 : ℝ) ^ (N / 8) := by positivity
  calc (LCnt N : ℝ) * (4000 * Real.log N) ≤ (2 : ℝ) ^ (N / 8) * (3 * N) * (4000 * N) := by
        gcongr
    _ = (2 : ℝ) ^ (N / 8) * (12000 * (N : ℝ) ^ 2) := by ring
    _ ≤ _ := hfam_ge

end Census
end IIT

#print axioms IIT.Census.famBig_proved
#print axioms IIT.Census.famX3_eq_core
#print axioms IIT.Census.choose_ge_stirling
