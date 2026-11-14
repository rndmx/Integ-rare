/-
Census of IIT 2.0: blocks `{c : c_M = x_M}` and the combinatorics of `mix`.
-/
import IIT2.Census.Measure

namespace IIT2

open Finset Real

variable {N : ℕ}

/-- The block of states agreeing with `x` on `M`. -/
def blk (M : Finset (Fin N)) (x : State N) : Finset (State N) :=
  Finset.univ.filter (fun c => ∀ i ∈ M, c i = x i)

lemma mem_blk {M : Finset (Fin N)} {x c : State N} : c ∈ blk M x ↔ ∀ i ∈ M, c i = x i := by
  simp [blk]

lemma self_mem_blk (M : Finset (Fin N)) (x : State N) : x ∈ blk M x := mem_blk.mpr fun _ _ => rfl

lemma card_state : Fintype.card (State N) = 2 ^ N := by simp

lemma card_blk (A : Finset (Fin N)) (x : State N) : (blk A x).card = 2 ^ (N - A.card) := by
  classical
  have : blk A x = Fintype.piFinset (fun i => if i ∈ A then {x i} else Finset.univ) := by
    ext c
    simp only [mem_blk, Fintype.mem_piFinset]
    constructor
    · intro h i; by_cases hi : i ∈ A <;> simp [hi, h i]
    · intro h i hi; have := h i; simpa [hi] using this
  rw [this, Fintype.card_piFinset]
  have h2 : ∀ i, (if i ∈ A then ({x i} : Finset Bool) else Finset.univ).card =
      if i ∈ A then 1 else 2 := fun i => by split_ifs <;> simp
  simp_rw [h2]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have : (Finset.univ.filter fun i : Fin N => i ∉ A) = Aᶜ := by ext i; simp
  rw [this, Finset.card_compl, Fintype.card_fin]

lemma mix_eq_iff {M : Finset (Fin N)} {x e c : State N} :
    mix M x e = c ↔ c ∈ blk M x ∧ e ∈ blk Mᶜ c := by
  rw [mem_blk, mem_blk, funext_iff]
  constructor
  · intro h
    exact ⟨fun i hi => by rw [← h i, mix_eq_of_mem hi], fun i hi => by
      rw [Finset.mem_compl] at hi; rw [← h i, mix_eq_of_not_mem hi]⟩
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i ∈ M
    · rw [mix_eq_of_mem hi, h1 i hi]
    · rw [mix_eq_of_not_mem hi, h2 i (Finset.mem_compl.mpr hi)]

/-- `∑_e F(mix M x e) = 2^{|M|} ∑_{c ∈ blk M x} F c`. -/
lemma sum_mix (M : Finset (Fin N)) (x : State N) (F : State N → ℝ) :
    ∑ e, F (mix M x e) = 2 ^ M.card * ∑ c ∈ blk M x, F c := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := blk M x) (g := mix M x)
    (fun e _ => (mix_eq_iff.mp rfl).1)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c hc => ?_
  have : ∀ e ∈ Finset.univ.filter (fun e => mix M x e = c), F (mix M x e) = F c :=
    fun e he => by rw [(Finset.mem_filter.mp he).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  have hf : Finset.univ.filter (fun e => mix M x e = c) = blk Mᶜ c := by
    ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, mix_eq_iff, hc]
  rw [hf, card_blk, Finset.card_compl, Fintype.card_fin]
  have : N - (N - M.card) = M.card := by
    have := Finset.card_le_univ M; simp only [Fintype.card_fin] at this; omega
  rw [this]; push_cast; ring

lemma two_pow_split (M : Finset (Fin N)) :
    (2 : ℝ) ^ N = 2 ^ M.card * 2 ^ (N - M.card) := by
  rw [← pow_add]
  congr 1
  have := Finset.card_le_univ M; simp only [Fintype.card_fin] at this; omega

/-- Block form of `a^M_l(x)`: the average of `q_l` over the block of `x`. -/
lemma aA_eq_blk (q : Fin N → State N → ℝ) (M : Finset (Fin N)) (l : Fin N) (x : State N) :
    aA q M l x = (∑ c ∈ blk M x, q l c) / 2 ^ (N - M.card) := by
  unfold aA avg
  rw [sum_mix M x (fun c => q l c), card_state]
  push_cast
  rw [two_pow_split M]
  have : (2 : ℝ) ^ M.card ≠ 0 := by positivity
  field_simp

/-- Mixing identity: `avg_x q_l(x) h(x) = avg_x a^M_l(x) h(x)` for `h` depending on `M`. -/
lemma avg_q_mul_eq (q : Fin N → State N → ℝ) (M : Finset (Fin N)) (l : Fin N)
    (h : State N → ℝ) (hh : DepOn M h) :
    avg (fun x => aA q M l x * h x) = avg (fun x => q l x * h x) := by
  unfold aA avg
  have hc : (Fintype.card (State N) : ℝ) ≠ 0 := card_pos.ne'
  have key : ∑ x, (∑ e, q l (mix M x e)) * h x =
      (Fintype.card (State N) : ℝ) * ∑ x, q l x * h x := by
    have h1 : ∀ x, (∑ e, q l (mix M x e)) * h x = ∑ e, q l (mix M x e) * h (mix M x e) :=
      fun x => by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hh x (mix M x e) fun i hi => (mix_eq_of_mem hi).symm]
    simp_rw [h1]
    rw [← Fintype.sum_prod_type' (f := fun x e => q l (mix M x e) * h (mix M x e))]
    rw [← (swapEquiv M).sum_comp]
    have h2 : ∀ p : State N × State N, q l (mix M ((swapEquiv M) p).1 ((swapEquiv M) p).2) *
        h (mix M ((swapEquiv M) p).1 ((swapEquiv M) p).2) = q l p.1 * h p.1 := by
      intro p
      have : mix M ((swapEquiv M) p).1 ((swapEquiv M) p).2 = p.1 := by
        funext i; by_cases hi : i ∈ M <;> simp [swapEquiv, mix, hi]
      rw [this]
    simp_rw [h2]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have : ∀ x, (∑ e, q l (mix M x e)) / (Fintype.card (State N) : ℝ) * h x =
      (∑ e, q l (mix M x e)) * h x / (Fintype.card (State N) : ℝ) := fun x => by ring
  simp_rw [this]
  rw [← Finset.sum_div, key]
  field_simp

/-- Disjointness of blocks. -/
lemma blk_disjoint {M : Finset (Fin N)} {x x' : State N} (h : x' ∉ blk M x) :
    Disjoint (blk M x) (blk M x') := by
  rw [Finset.disjoint_left]
  intro c hc hc'
  apply h
  rw [mem_blk] at hc hc' ⊢
  intro i hi; rw [← hc i hi, hc' i hi]

end IIT2
