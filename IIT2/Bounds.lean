/-
Upper bounds `ei ≤ n` and `φ ≤ n` bits [BT08, p.4 and p.7].
-/
import IIT2.Theorems

namespace IIT2

open Finset Real

variable {N : ℕ}

/-- Indicator that coordinate `i` equals `b`. -/
def ind (i : Fin N) (b : Bool) : State N → ℝ := fun y => if y i = b then 1 else 0

/-- Flip coordinate `i`. -/
def flipEquiv (i : Fin N) : State N ≃ State N where
  toFun y := Function.update y i (!y i)
  invFun y := Function.update y i (!y i)
  left_inv y := by funext j; by_cases h : j = i <;> simp [Function.update, h]
  right_inv y := by funext j; by_cases h : j = i <;> simp [Function.update, h]

lemma avg_ind (i : Fin N) (b : Bool) : avg (ind i b) = 1 / 2 := by
  have hflip : (∑ y, ind i b y) = ∑ y, ind i (!b) y := by
    rw [← (flipEquiv i).sum_comp]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [ind, flipEquiv, Equiv.coe_fn_mk, Function.update_self]
    cases b <;> cases y i <;> simp
  have hsum : (∑ y, ind i b y) + ∑ y, ind i (!b) y = (Fintype.card (State N) : ℝ) := by
    rw [← Finset.sum_add_distrib]
    have : ∀ y : State N, ind i b y + ind i (!b) y = 1 := fun y => by
      simp only [ind]; cases b <;> cases y i <;> simp
    simp [this]
  unfold avg
  have hc := card_pos (N := N)
  field_simp
  linarith

lemma ind_depOn (i : Fin N) (b : Bool) : DepOn {i} (ind i b) := fun x y h => by
  simp [ind, h i (Finset.mem_singleton_self i)]

/-- `avg (∏_{i∈S} h i) = ∏ avg (h i)` when `h i` depends only on coordinate `i`. -/
lemma avg_prod_singletons (S : Finset (Fin N)) (h : Fin N → State N → ℝ)
    (hh : ∀ i ∈ S, DepOn {i} (h i)) :
    avg (fun x => ∏ i ∈ S, h i x) = ∏ i ∈ S, avg (h i) ∧ DepOn S (fun x => ∏ i ∈ S, h i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact ⟨avg_const 1, fun _ _ _ => rfl⟩
  | insert a S ha ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hh i (Finset.mem_insert_of_mem hi))
    have hfa := hh a (Finset.mem_insert_self a S)
    simp only [Finset.prod_insert ha]
    refine ⟨?_, ?_⟩
    · rw [avg_mul_of_disjoint (Finset.disjoint_singleton_left.mpr ha) hfa ih2, ih1]
    · exact (hfa.mono (by simp)).mul (ih2.mono (Finset.subset_insert a S))

/-- The a posteriori density is at most `2^{|S|}` (a probability is at most `1`). -/
lemma post_le (sys : UnitTPM N) (S : Finset (Fin N)) (x₁ x : State N) :
    post sys S x₁ x ≤ 2 ^ S.card := by
  by_cases h : 0 < avg (cond sys S x₁)
  · let g : State N → ℝ := fun y => ∏ i ∈ S, ind i (x i) y
    have hg : avg g = (1 / 2) ^ S.card := by
      rw [(avg_prod_singletons S (fun i => ind i (x i)) (fun i _ => ind_depOn i (x i))).1]
      simp [avg_ind]
    have hpt : ∀ y, cond sys S x₁ x * g y ≤ cond sys S x₁ y := by
      intro y
      by_cases hy : ∀ i ∈ S, y i = x i
      · have : g y = 1 := Finset.prod_eq_one fun i hi => by simp [ind, hy i hi]
        rw [this, mul_one, cond_depOn sys S x₁ x y (fun i hi => (hy i hi).symm)]
      · push Not at hy
        obtain ⟨i, hi, hne⟩ := hy
        have : g y = 0 := Finset.prod_eq_zero hi (by simp [ind, hne])
        rw [this, mul_zero]; exact cond_nonneg _ _ _ _
    have hle := avg_mono hpt
    have hmul : avg (fun y => cond sys S x₁ x * g y) = cond sys S x₁ x * avg g := by
      unfold avg; rw [← Finset.mul_sum, mul_div_assoc]
    rw [hmul, hg] at hle
    unfold post
    rw [div_le_iff₀ h]
    have h2 : (0 : ℝ) < 2 ^ S.card := by positivity
    have : (2 : ℝ) ^ S.card * (1 / 2) ^ S.card = 1 := by
      rw [← mul_pow]; norm_num
    nlinarith [cond_nonneg sys S x₁ x]
  · rw [post_eq_zero sys S x₁ h]; positivity

/-- `ei(S₀ → s₁) ≤ |S|` bits `[BT08, p.4]` ("a system of n binary elements generates at most
n bits of information"). -/
theorem ei_le_card (sys : UnitTPM N) (S : Finset (Fin N)) (x₁ : State N) :
    ei sys S x₁ ≤ S.card := by
  unfold ei kl pmax
  by_cases h : 0 < avg (cond sys S x₁)
  · have hpt : ∀ x, post sys S x₁ x * logb 2 (post sys S x₁ x / 1) ≤
        (S.card : ℝ) * post sys S x₁ x := by
      intro x
      rw [div_one]
      rcases (post_nonneg sys S x₁ x).lt_or_eq with hp | hp
      · have hlog : logb 2 (post sys S x₁ x) ≤ S.card := by
          rw [Real.logb_le_iff_le_rpow (by norm_num) hp, Real.rpow_natCast]
          exact post_le sys S x₁ x
        nlinarith
      · rw [← hp]; simp
    have := avg_mono hpt
    have hm : avg (fun x => (S.card : ℝ) * post sys S x₁ x) = S.card := by
      unfold avg; rw [← Finset.mul_sum, mul_div_assoc]
      have := avg_post sys S x₁ h; unfold avg at this; rw [this, mul_one]
    linarith
  · rw [← avg_const (N := N) (S.card : ℝ)]
    exact avg_mono fun x => by
      rw [post_eq_zero sys S x₁ h x]; simp

lemma normP_le_card {S : Finset (Fin N)} (P : Finpartition S) : normP P ≤ S.card := by
  unfold normP
  split_ifs with h
  · exact le_rfl
  · have hsum : ∑ M ∈ P.parts, M.card = S.card := P.sum_card_parts
    have hmin : P.parts.card * minPartSize P ≤ S.card := by
      rw [← hsum]
      unfold minPartSize
      split_ifs with hn
      · rw [← smul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum fun M hM => Finset.inf'_le _ hM
      · simp
    have : ((P.parts.card : ℝ) - 1) * minPartSize P ≤ (P.parts.card : ℝ) * minPartSize P := by
      nlinarith [(Nat.cast_nonneg (minPartSize P) : (0 : ℝ) ≤ _)]
    have h2 : ((P.parts.card * minPartSize P : ℕ) : ℝ) ≤ S.card := by exact_mod_cast hmin
    push_cast at h2
    linarith

lemma normP_pos {S : Finset (Fin N)} (hS : S.Nonempty) (P : Finpartition S) : 0 < normP P := by
  have hne : P.parts.Nonempty := P.parts_nonempty (by simpa [Finset.bot_eq_empty] using hS.ne_empty)
  unfold normP
  split_ifs with h
  · exact_mod_cast hS.card_pos
  · have h2 : 2 ≤ P.parts.card := by
      have := hne.card_pos; omega
    have hm : 0 < minPartSize P := by
      unfold minPartSize
      rw [dif_pos hne]
      obtain ⟨M, hM, hMeq⟩ := Finset.exists_mem_eq_inf' hne Finset.card
      rw [hMeq]
      exact (Finset.nonempty_of_ne_empty (P.ne_bot hM)).card_pos
    have : (2 : ℝ) ≤ P.parts.card := by exact_mod_cast h2
    have : (0 : ℝ) < minPartSize P := by exact_mod_cast hm
    nlinarith

/-- `φ(s₁) ≤ |S|` bits `[BT08, p.7]` ("For a discrete system composed of n binary elements
φ(x₁) ≤ n bits. This follows since the normalization is largest for the total partition, and
for this partition effective information is [...] ≤ n bits"). -/
theorem phi_le_card (sys : UnitTPM N) (S : Finset (Fin N)) (x₁ : State N) :
    phi sys S x₁ ≤ S.card := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS; rw [phi_empty]; simp
  obtain ⟨P, hMIP, hP⟩ := exists_isMIP sys S x₁
  let T := Finpartition.indiscrete (a := S) (by simpa [Finset.bot_eq_empty] using hS.ne_empty)
  have hT : T.parts.card = 1 := by simp [T, Finpartition.indiscrete]
  have hle := hMIP T
  unfold mipKey at hle
  rw [Prod.Lex.toLex_le_toLex'] at hle
  have h1 : eiAcross sys P x₁ / normP P ≤ eiAcross sys T x₁ / normP T := hle.1
  have hTa : eiAcross sys T x₁ = ei sys S x₁ := by simp [eiAcross, hT]
  have hTn : normP T = S.card := by simp [normP, hT]
  rw [hTa, hTn] at h1
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hr : ei sys S x₁ / S.card ≤ 1 := (div_le_one hcard).mpr (ei_le_card sys S x₁)
  have hNP := normP_pos hS P
  have : eiAcross sys P x₁ ≤ normP P := by
    have := h1.trans hr
    rwa [div_le_one hNP] at this
  rw [hP]
  exact this.trans (normP_le_card P)

end IIT2
