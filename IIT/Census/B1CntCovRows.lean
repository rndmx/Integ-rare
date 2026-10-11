/-
Census, B1, W14 work package WP6 (part 4): the rows read by `Y_K` (`RDrows`, `YK_detOn`), the shared
rows of two counted indicators (`sh_rows`, W9 Lemma SH'), and the deterministic stability of `Y_K`
under a perturbation of the shared rows (the atom argument of W9 Lemma COV').
Blueprint: `iit-census/lean/B1-W14-count-lean.md` §11.  No `sorry`.
-/
import IIT.Census.B1CntCovCheb

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-! ### The rows read by `Y_K` -/

/-- The rows `s ⊕ J` with `|J \ K| ≤ r_D`: every subcube read by `Y_K` lies in them (W9 5.5). -/
noncomputable def RDrows (N : ℕ) (s : State N) (K : Finset (Fin N)) : Finset (State N) :=
  univ.filter fun r => ((univ.filter fun i => r i ≠ s i) \ K).card ≤ rD N

lemma one_le_rD (N : ℕ) : 1 ≤ rD N := by unfold rD; omega

lemma mem_RDrows_of {s r : State N} {K E : Finset (Fin N)} (hE : E.card ≤ rD N)
    (h : ∀ i, r i ≠ s i → i ∈ K ∨ i ∈ E) : r ∈ RDrows N s K := by
  simp only [RDrows, mem_filter, mem_univ, true_and]
  refine le_trans (card_le_card ?_) hE
  intro i hi
  simp only [Finset.mem_sdiff, mem_filter, mem_univ, true_and] at hi
  rcases h i hi.1 with h1 | h1
  · exact absurd h1 hi.2
  · exact h1

lemma flipAt_apply_ne' {j i : Fin N} (s : State N) (h : i ≠ j) : flipAt j s i = s i := by
  unfold flipAt; exact Function.update_of_ne h _ _

lemma C0_mem_RD {s r : State N} {K : Finset (Fin N)} (hr : r ∈ agree (univ \ K) s) :
    r ∈ RDrows N s K :=
  mem_RDrows_of (E := ∅) (by simp) fun i hi => Or.inl (by
    by_contra hiK
    exact hi (mem_agree.1 hr i (by simp only [Finset.mem_sdiff, mem_univ, true_and]; exact hiK)))

lemma Cj_diff {s r : State N} {K : Finset (Fin N)} {j : Fin N}
    (hr : r ∈ agree (univ \ K) (flipAt j s)) : ∀ i, r i ≠ s i → i ∈ K ∨ i ∈ ({j} : Finset (Fin N)) := by
  intro i hi
  by_cases hiK : i ∈ K
  · exact Or.inl hiK
  · refine Or.inr (mem_singleton.2 ?_)
    by_contra hij
    have h1 := mem_agree.1 hr i (by simp only [Finset.mem_sdiff, mem_univ, true_and]; exact hiK)
    rw [flipAt_apply_ne' s hij] at h1
    exact hi h1

lemma Cj_mem_RD {s r : State N} {K : Finset (Fin N)} {j : Fin N}
    (hr : r ∈ agree (univ \ K) (flipAt j s)) : r ∈ RDrows N s K :=
  mem_RDrows_of (E := {j}) (by rw [card_singleton]; exact one_le_rD N) (Cj_diff hr)

lemma CA_diff {s r : State N} {K A : Finset (Fin N)} (hr : r ∈ agree A s) :
    ∀ i, r i ≠ s i → i ∈ K ∨ i ∈ (univ \ K) \ A := by
  intro i hi
  by_cases hiK : i ∈ K
  · exact Or.inl hiK
  · refine Or.inr ?_
    simp only [Finset.mem_sdiff, mem_univ, true_and]
    exact ⟨hiK, fun hiA => hi (mem_agree.1 hr i hiA)⟩

lemma CA_mem_RD {s r : State N} {K A : Finset (Fin N)} (hA : ((univ \ K) \ A).card ≤ rD N)
    (hr : r ∈ agree A s) : r ∈ RDrows N s K :=
  mem_RDrows_of hA (CA_diff hr)

lemma effDevA_congr {w w' : Param N} {s : State N} {A : Finset (Fin N)} {t : State N} (k : Fin N)
    (hs : w s = w' s) (h : ∀ r ∈ agree A t, w r = w' r) :
    effDevA w s A t k = effDevA w' s A t k := by
  unfold effDevA pTe
  congr 1
  refine sum_congr rfl fun r hr => ?_
  rw [hs, h r hr]

/-- `Y_K` is a function of `fK`, `hK` (`j ∈ M`) and the `(D)`-subcube statistics only. -/
lemma YK_congr {w w' : Param N} {s : State N} {K : Finset (Fin N)}
    (hf : ∀ k, fK w s K k = fK w' s K k)
    (hh : ∀ j ∈ univ \ K, ∀ k, hK w s K j k = hK w' s K j k)
    (he : ∀ A, A ⊆ univ \ K → ((univ \ K) \ A).card ≤ rD N → ∀ k,
      effDevA w s A s k = effDevA w' s A s k) :
    YK N s K w ↔ YK N s K w' := by
  unfold YK
  refine exists_congr fun k => and_congr_right fun _ => ?_
  have hC : CoreAt N s K k 0 w ↔ CoreAt N s K k 0 w' := by
    unfold CoreAt
    simp only [hf]
    exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
      (forall₂_congr fun j hj => by rw [hh j hj k])))
  have hD : DleAt N s K k w ↔ DleAt N s K k w' := by
    unfold DleAt
    simp only [hf]
    refine forall_congr' fun A => ?_
    constructor
    · intro h hA hne h2 hr; rw [← he A hA hr k]; exact h hA hne h2 hr
    · intro h hA hne h2 hr; rw [he A hA hr k]; exact h hA hne h2 hr
  rw [hC, hD, hf k]

/-- **`Y_K` reads only `s` and the rows `RDrows K`** (W9 5.5 "Reads"). -/
theorem YK_detOn (s : State N) (K : Finset (Fin N)) :
    DetOnE ((RDrows N s K ∪ {s}) ×ˢ (univ : Finset (Fin N))) {w : Param N | YK N s K w} := by
  refine detOnE_of_rows fun w w' hw => ?_
  have hs : w s = w' s := hw s (mem_union_right _ (mem_singleton_self s))
  have hrow : ∀ (A : Finset (Fin N)) (t : State N), (∀ r ∈ agree A t, r ∈ RDrows N s K) →
      ∀ k, effDevA w s A t k = effDevA w' s A t k :=
    fun A t hA k => effDevA_congr k hs fun r hr => hw r (mem_union_left _ (hA r hr))
  show YK N s K w ↔ YK N s K w'
  exact YK_congr (fun k => hrow _ _ (fun r hr => C0_mem_RD hr) k)
    (fun j _ k => hrow _ _ (fun r hr => Cj_mem_RD hr) k)
    (fun A _ hr k => hrow _ _ (fun r hr' => CA_mem_RD hr hr') k)

/-! ### Shared rows (W9 Lemma SH') -/

lemma card_powerset_filter_le (S : Finset (Fin N)) (ρ : ℕ) :
    (S.powerset.filter fun T => T.card ≤ ρ).card ≤ (S.card + 1) ^ ρ := by
  have hsub : S.powerset.filter (fun T => T.card ≤ ρ) ⊆
      (range (ρ + 1)).biUnion fun m => S.powersetCard m := by
    intro T hT
    rw [mem_filter, mem_powerset] at hT
    rw [mem_biUnion]
    exact ⟨T.card, mem_range.2 (Nat.lt_succ_of_le hT.2), mem_powersetCard.2 ⟨hT.1, rfl⟩⟩
  refine (card_le_card hsub).trans ((card_biUnion_le).trans ?_)
  simp only [card_powersetCard]
  exact sum_choose_le_succ_pow _ _

/-- The set of coordinates where `r` differs from `s`. -/
def covDiff (s r : State N) : Finset (Fin N) := univ.filter fun i => r i ≠ s i

lemma covDiff_inj {s r r' : State N} (h : covDiff s r = covDiff s r') : r = r' := by
  funext i
  have := congrArg (fun S => i ∈ S) h
  simp only [covDiff, mem_filter, mem_univ, true_and, eq_iff_iff] at this
  cases h1 : r i <;> cases h2 : r' i <;> cases h3 : s i <;> simp_all

/-- **Lemma SH'**: a subcube `agree (U \ (K ∪ E)) s` (`E ∩ K = ∅`, `|E| ≤ r_D`) has at most
`2^{|K ∩ K'|} (|K|+1)^{r_D} 2^{r_D}` rows in `RDrows K'`. -/
theorem sh_rows (s : State N) (K K' E : Finset (Fin N)) (_hEK : Disjoint E K)
    (hE : E.card ≤ rD N) :
    ((agree (univ \ (K ∪ E)) s) ∩ RDrows N s K').card ≤
      2 ^ (K ∩ K').card * (K.card + 1) ^ rD N * 2 ^ rD N := by
  set φ : State N → Finset (Fin N) × Finset (Fin N) × Finset (Fin N) := fun r =>
    (covDiff s r ∩ (K ∩ K'), covDiff s r ∩ (K \ K'), covDiff s r ∩ E) with hφ
  set T := (K ∩ K').powerset ×ˢ (((K \ K').powerset.filter fun S => S.card ≤ rD N) ×ˢ E.powerset)
    with hT
  have hJsub : ∀ r ∈ agree (univ \ (K ∪ E)) s, covDiff s r ⊆ K ∪ E := by
    intro r hr i hi
    simp only [covDiff, mem_filter, mem_univ, true_and] at hi
    by_contra h
    exact hi (mem_agree.1 hr i (by simp only [Finset.mem_sdiff, mem_univ, true_and]; exact h))
  have hmaps : Set.MapsTo φ ↑((agree (univ \ (K ∪ E)) s) ∩ RDrows N s K') ↑T := by
    intro r hr
    rw [mem_coe, mem_inter] at hr
    have hRD := hr.2
    simp only [RDrows, mem_filter, mem_univ, true_and] at hRD
    simp only [hφ, hT, mem_coe, mem_product, mem_powerset, mem_filter]
    refine ⟨inter_subset_right, ⟨inter_subset_right, ?_⟩, inter_subset_right⟩
    refine le_trans (card_le_card ?_) hRD
    intro i hi
    simp only [mem_inter, Finset.mem_sdiff, covDiff, mem_filter, mem_univ, true_and] at hi ⊢
    exact ⟨hi.1, hi.2.2⟩
  have hdec : ∀ r ∈ agree (univ \ (K ∪ E)) s,
      covDiff s r = covDiff s r ∩ (K ∩ K') ∪ covDiff s r ∩ (K \ K') ∪ covDiff s r ∩ E := by
    intro r hr
    have hs := hJsub r hr
    ext i
    simp only [mem_union, mem_inter, Finset.mem_sdiff]
    constructor
    · intro hi
      have h2 := hs hi
      rw [mem_union] at h2
      by_cases hk : i ∈ K' <;> tauto
    · tauto
  have hinj : Set.InjOn φ ↑((agree (univ \ (K ∪ E)) s) ∩ RDrows N s K') := by
    intro r hr r' hr' h
    rw [mem_coe, mem_inter] at hr hr'
    simp only [hφ, Prod.mk.injEq] at h
    apply covDiff_inj (s := s)
    rw [hdec r hr.1, hdec r' hr'.1, h.1, h.2.1, h.2.2]
  refine (card_le_card_of_injOn φ hmaps hinj).trans ?_
  rw [hT, card_product, card_product, card_powerset, card_powerset, ← mul_assoc]
  have hfilt : ((K \ K').powerset.filter fun S => S.card ≤ rD N).card ≤ (K.card + 1) ^ rD N := by
    refine (card_powerset_filter_le _ _).trans (Nat.pow_le_pow_left ?_ _)
    have := card_le_card (sdiff_subset : K \ K' ⊆ K)
    omega
  exact Nat.mul_le_mul (Nat.mul_le_mul le_rfl hfilt) (Nat.pow_le_pow_right (by norm_num) hE)

/-! ### Perturbation of subcube statistics -/

lemma pTe_mem (w : Param N) (s r : State N) (k : Fin N) :
    0 ≤ pTe w s r k ∧ pTe w s r k ≤ 1 := by
  have h0 := clamp01_nonneg (w r k)
  have h1 := clamp01_le_one (w r k)
  unfold pTe
  split_ifs <;> constructor <;> linarith

/-- Changing only the rows of `R` (and not row `s`) moves a subcube statistic by at most the
fraction of its rows in `R`. -/
lemma effDevA_diff_le (u v : Param N) (s : State N) (A : Finset (Fin N)) (t : State N) (k : Fin N)
    (R : Finset (State N)) (hs : u s = v s) (hR : ∀ r, r ∉ R → u r = v r) :
    |effDevA u s A t k - effDevA v s A t k| ≤
      ((agree A t ∩ R).card : ℝ) / (agree A t).card := by
  have hcard : (0 : ℝ) < (agree A t).card := Nat.cast_pos.2 (card_agree_pos A t)
  unfold effDevA
  rw [← sub_div, abs_div, abs_of_pos hcard, div_le_div_iff_of_pos_right hcard, ← sum_sub_distrib]
  calc |∑ r ∈ agree A t, ((pTe u s r k - 1 / 2) - (pTe v s r k - 1 / 2))|
      ≤ ∑ r ∈ agree A t, |(pTe u s r k - 1 / 2) - (pTe v s r k - 1 / 2)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ agree A t, (if r ∈ R then (1 : ℝ) else 0) := by
        refine sum_le_sum fun r _ => ?_
        by_cases hr : r ∈ R
        · rw [if_pos hr]
          have h1 := pTe_mem u s r k
          have h2 := pTe_mem v s r k
          rw [abs_le]; constructor <;> linarith
        · rw [if_neg hr]
          have : pTe u s r k = pTe v s r k := by unfold pTe; rw [hs, hR r hr]
          rw [this]; simp
    _ = ((agree A t ∩ R).card : ℝ) := by
        rw [sum_boole, filter_mem_eq_inter]

/-! ### Stability of `Y_K` (the atom argument of W9 Lemma COV') -/

/-- The thresholds of the `fK`-atoms (for `f_k > 0`). -/
noncomputable def thrF (N : ℕ) : Fin 5 → ℝ :=
  ![0, A0C N + 2 * kapN N, x2C N, A0C N + kapN N, -(A0C N + kapN N)]

/-- The `(D)`-index sets `A ⊆ M`, `A ≠ ∅`, `2 ≤ |M \ A| ≤ r_D`. -/
noncomputable def Aset (N : ℕ) (K : Finset (Fin N)) : Finset (Finset (Fin N)) :=
  (univ \ K).powerset.filter fun A =>
    A.Nonempty ∧ 2 ≤ ((univ \ K) \ A).card ∧ ((univ \ K) \ A).card ≤ rD N

/-- The `(N)`-atom linear form. -/
noncomputable def nAt (N : ℕ) (s : State N) (K : Finset (Fin N)) (k j : Fin N) (u : Param N) : ℝ :=
  hK u s K j k - (1 - 2 / mX N) * fK u s K k + kapN N

/-- The `(D)`-atom linear form. -/
noncomputable def dAt (N : ℕ) (s : State N) (K : Finset (Fin N)) (k : Fin N) (A : Finset (Fin N))
    (u : Param N) : ℝ :=
  effDevA u s A s k - (1 - (((univ \ K) \ A).card : ℝ) / mX N) * fK u s K k + kapN N / 2

/-- **Non-degeneracy at margin `η`**: every atom is `η`-far from its threshold. -/
def NDeg (N : ℕ) (s : State N) (K : Finset (Fin N)) (η : ℝ) (u : Param N) : Prop :=
  (∀ k' : Fin N, ∀ c : Fin 5, η < |fK u s K k' - thrF N c|) ∧
  (∀ k ∈ K, ∀ j ∈ univ \ K, η < |nAt N s K k j u|) ∧
  (∀ k ∈ K, ∀ A ∈ Aset N K, η < |dAt N s K k A u|)

lemma cmp_lt_iff {x y c : ℝ} (h : |x - y| < |x - c|) : x < c ↔ y < c := by
  rcases lt_or_ge x c with hx | hx
  · rw [abs_of_neg (by linarith : x - c < 0)] at h
    have h2 := neg_abs_le (x - y)
    constructor <;> intro <;> linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ x - c)] at h
    have h2 := le_abs_self (x - y)
    constructor
    · intro h3; linarith
    · intro h3; linarith

lemma cmp_gt_iff {x y c : ℝ} (h : |x - y| < |x - c|) : c < x ↔ c < y := by
  have h' : |(-x) - (-y)| < |(-x) - (-c)| := by
    rw [show (-x) - (-y) = -(x - y) by ring, show (-x) - (-c) = -(x - c) by ring, abs_neg, abs_neg]
    exact h
  have := cmp_lt_iff h'
  constructor
  · intro h1; have := this.1 (by linarith); linarith
  · intro h1; have := this.2 (by linarith); linarith

/-- **Stability**: if every statistic of `Y_K` moves by `≤ δ` and `u` is `2δ`-non-degenerate, then
`Y_K(u) ↔ Y_K(v)`. -/
theorem YK_stable {u v : Param N} {s : State N} {K : Finset (Fin N)} {δ : ℝ}
    (hm : 2 ≤ mX N) (hrm : (rD N : ℝ) ≤ mX N)
    (hf : ∀ k, |fK u s K k - fK v s K k| ≤ δ)
    (hh : ∀ j ∈ univ \ K, ∀ k, |hK u s K j k - hK v s K j k| ≤ δ)
    (he : ∀ A, A ⊆ univ \ K → ((univ \ K) \ A).card ≤ rD N → ∀ k,
      |effDevA u s A s k - effDevA v s A s k| ≤ δ)
    (hnd : NDeg N s K (2 * δ) u) : YK N s K u ↔ YK N s K v := by
  have hm0 : (0 : ℝ) < mX N := by linarith
  have hfat : ∀ k' (c : Fin 5), |fK u s K k' - fK v s K k'| < |fK u s K k' - thrF N c| :=
    fun k' c => lt_of_le_of_lt ((hf k').trans (by linarith [abs_nonneg (fK u s K k' - fK v s K k'), hf k']))
      (hnd.1 k' c)
  unfold YK
  refine exists_congr fun k => and_congr_right fun hk => ?_
  have hsgn : 0 < fK u s K k ↔ 0 < fK v s K k := cmp_gt_iff (hfat k 0)
  by_cases hpos : 0 < fK u s K k
  swap
  · constructor
    · rintro ⟨_, h, _⟩; exact absurd h hpos
    · rintro ⟨_, h, _⟩; exact absurd (hsgn.2 h) hpos
  have hpos' := hsgn.1 hpos
  have hfk : |fK u s K k - fK v s K k| ≤ δ := hf k
  -- coefficient bound
  have hcoef : ∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ x x' : ℝ, |x - x'| ≤ δ →
      |(x - a * fK u s K k + 0) - (x' - a * fK v s K k + 0)| ≤ 2 * δ := by
    intro a ha0 ha1 x x' hx
    have e : (x - a * fK u s K k + 0) - (x' - a * fK v s K k + 0) =
        (x - x') - a * (fK u s K k - fK v s K k) := by ring
    rw [e]
    have h1 : |a * (fK u s K k - fK v s K k)| ≤ δ := by
      rw [abs_mul, abs_of_nonneg ha0]
      calc a * |fK u s K k - fK v s K k| ≤ 1 * δ := mul_le_mul ha1 hfk (abs_nonneg _) zero_le_one
        _ = δ := one_mul δ
    calc |(x - x') - a * (fK u s K k - fK v s K k)| ≤ |x - x'| + |a * (fK u s K k - fK v s K k)| :=
          abs_sub _ _
      _ ≤ 2 * δ := by linarith
  have hC : CoreAt N s K k 0 u ↔ CoreAt N s K k 0 v := by
    unfold CoreAt sgnMul
    simp only [hpos, hpos', ↓reduceIte, abs_of_pos hpos, abs_of_pos hpos', add_zero, sub_zero]
    refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
    · exact cmp_gt_iff (hfat k 1)
    · exact cmp_lt_iff (hfat k 2)
    · refine forall₂_congr fun k' _ => ?_
      rw [abs_lt, abs_lt]
      refine and_congr ?_ (cmp_lt_iff (hfat k' 3))
      exact cmp_gt_iff (hfat k' 4)
    · refine forall₂_congr fun j hj => ?_
      have hn := hnd.2.1 k hk j hj
      have hmc : 0 ≤ 1 - 2 / mX N ∧ 1 - 2 / mX N ≤ 1 := by
        constructor
        · rw [sub_nonneg, div_le_one hm0]; exact hm
        · have : 0 ≤ 2 / mX N := by positivity
          linarith
      have hd := hcoef _ hmc.1 hmc.2 _ _ (hh j hj k)
      have key : nAt N s K k j u < 0 ↔ nAt N s K k j v < 0 := by
        refine cmp_lt_iff (lt_of_le_of_lt ?_ (by rw [sub_zero]; exact hn))
        unfold nAt
        have e : (hK u s K j k - (1 - 2 / mX N) * fK u s K k + kapN N) -
            (hK v s K j k - (1 - 2 / mX N) * fK v s K k + kapN N) =
            (hK u s K j k - (1 - 2 / mX N) * fK u s K k + 0) -
            (hK v s K j k - (1 - 2 / mX N) * fK v s K k + 0) := by ring
        rw [e]; exact hd
      unfold nAt at key
      constructor
      · intro h1; have := key.1 (by linarith); linarith
      · intro h1; have := key.2 (by linarith); linarith
  have hD : DleAt N s K k u ↔ DleAt N s K k v := by
    unfold DleAt sgnMul
    simp only [hpos, hpos', ↓reduceIte, abs_of_pos hpos, abs_of_pos hpos']
    refine forall_congr' fun A => ?_
    constructor
    · intro h hA hne h2 hr
      have hAs : A ∈ Aset N K := by
        simp only [Aset, mem_filter, mem_powerset]; exact ⟨hA, hne, h2, hr⟩
      have hn := hnd.2.2 k hk A hAs
      have hmc : 0 ≤ 1 - (((univ \ K) \ A).card : ℝ) / mX N ∧
          1 - (((univ \ K) \ A).card : ℝ) / mX N ≤ 1 := by
        have hr' : (((univ \ K) \ A).card : ℝ) ≤ rD N := by exact_mod_cast hr
        constructor
        · rw [sub_nonneg, div_le_one hm0]; linarith
        · have : 0 ≤ (((univ \ K) \ A).card : ℝ) / mX N := by positivity
          linarith
      have hd := hcoef _ hmc.1 hmc.2 _ _ (he A hA hr k)
      have key : dAt N s K k A u < 0 ↔ dAt N s K k A v < 0 := by
        refine cmp_lt_iff (lt_of_le_of_lt ?_ (by rw [sub_zero]; exact hn))
        unfold dAt
        have e : (effDevA u s A s k - (1 - (((univ \ K) \ A).card : ℝ) / mX N) * fK u s K k +
            kapN N / 2) - (effDevA v s A s k - (1 - (((univ \ K) \ A).card : ℝ) / mX N) *
            fK v s K k + kapN N / 2) =
            (effDevA u s A s k - (1 - (((univ \ K) \ A).card : ℝ) / mX N) * fK u s K k + 0) -
            (effDevA v s A s k - (1 - (((univ \ K) \ A).card : ℝ) / mX N) * fK v s K k + 0) := by
          ring
        rw [e]; exact hd
      unfold dAt at key
      have := h hA hne h2 hr
      have := key.1 (by linarith)
      linarith
    · intro h hA hne h2 hr
      have hAs : A ∈ Aset N K := by
        simp only [Aset, mem_filter, mem_powerset]; exact ⟨hA, hne, h2, hr⟩
      have hn := hnd.2.2 k hk A hAs
      have hmc : 0 ≤ 1 - (((univ \ K) \ A).card : ℝ) / mX N ∧
          1 - (((univ \ K) \ A).card : ℝ) / mX N ≤ 1 := by
        have hr' : (((univ \ K) \ A).card : ℝ) ≤ rD N := by exact_mod_cast hr
        constructor
        · rw [sub_nonneg, div_le_one hm0]; linarith
        · have : 0 ≤ (((univ \ K) \ A).card : ℝ) / mX N := by positivity
          linarith
      have hd := hcoef _ hmc.1 hmc.2 _ _ (he A hA hr k)
      have key : dAt N s K k A u < 0 ↔ dAt N s K k A v < 0 := by
        refine cmp_lt_iff (lt_of_le_of_lt ?_ (by rw [sub_zero]; exact hn))
        unfold dAt
        have e : (effDevA u s A s k - (1 - (((univ \ K) \ A).card : ℝ) / mX N) * fK u s K k +
            kapN N / 2) - (effDevA v s A s k - (1 - (((univ \ K) \ A).card : ℝ) / mX N) *
            fK v s K k + kapN N / 2) =
            (effDevA u s A s k - (1 - (((univ \ K) \ A).card : ℝ) / mX N) * fK u s K k + 0) -
            (effDevA v s A s k - (1 - (((univ \ K) \ A).card : ℝ) / mX N) * fK v s K k + 0) := by
          ring
        rw [e]; exact hd
      unfold dAt at key
      have := h hA hne h2 hr
      have := key.2 (by linarith)
      linarith
  rw [hC, hD]
  exact ⟨fun h => ⟨h.1, hpos', h.2.2⟩, fun h => ⟨h.1, hpos, h.2.2⟩⟩

end Census
end IIT

#print axioms IIT.Census.YK_detOn
#print axioms IIT.Census.sh_rows
#print axioms IIT.Census.YK_stable
