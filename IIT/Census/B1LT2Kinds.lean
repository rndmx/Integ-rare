/-
Census, B1 lemma LT2, module M6d-1: adverse counts indexed by pairs or units, and the binomial asymptotics.

* `lt2_mT_count_img`, `lt2_Ot_count_img`, `lt2_N0_count_img`: the adverse-count lemmas for a family given as the
  injective image of an index set `P` (pairs or units).
* `lt2_binom_le`: `C(d,m) 2^m e^{-X} ≤ e^{-L}` when `d ≤ D m` and `X ≥ L + m log(2eD)`.
-/
import IIT.Census.B1LT2Reflect

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

lemma lt2_card_filter_image {α β : Type*} [DecidableEq β] (P : Finset α) (g : α → β) (hg : Set.InjOn g P)
    (pr : β → Prop) [DecidablePred pr] :
    (P.filter fun p => pr (g p)).card = ((P.image g).filter pr).card := by
  classical
  rw [Finset.filter_image, Finset.card_image_of_injOn (fun x hx y hy h => hg (mem_filter.1 hx).1
    (mem_filter.1 hy).1 h)]

theorem lt2_mT_count_img {α : Type*} (P : Finset α) (g : α → Finset (Fin N)) (hg : Set.InjOn g P)
    (hne : ∀ p ∈ P, (g p).Nonempty) {κ : ℝ} (hκ : 0 < κ) (m : ℕ) (hm : 1 ≤ m) :
    cubeM N {w | m ≤ (P.filter fun p => κ * sigN N ≤ |lt2mT w (g p)|).card} ≤
      ENNReal.ofReal ((P.card.choose m) * 2 ^ m *
        Real.exp (-min (m * κ ^ 2 / 4) (κ * sigN N / (4 * lt2θ N)))) := by
  classical
  have h := lt2_mT_count (P.image g) (fun T hT => by
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hT; exact hne p hp) hκ m hm
  rw [Finset.card_image_of_injOn hg] at h
  refine le_trans (le_of_eq ?_) h
  congr 1; ext w; simp only [Set.mem_setOf_eq]
  have e : (P.filter fun p => κ * sigN N ≤ |lt2mT w (g p)|).card =
      ((P.image g).filter fun T => κ * sigN N ≤ |lt2mT w T|).card :=
    lt2_card_filter_image P g hg (fun T => κ * sigN N ≤ |lt2mT w T|)
  rw [e]

theorem lt2_Ot_count_img {α : Type*} (P : Finset α) (g : α → Fin N × Finset (Fin N)) (hg : Set.InjOn g P)
    (hne : ∀ p ∈ P, (g p).2.Nonempty) {κ : ℝ} (hκ : 0 < κ) (m : ℕ) (hm : 1 ≤ m) :
    cubeM N {w | m ≤ (P.filter fun p => κ * sigN N ≤ |lt2Ot w (g p)|).card} ≤
      ENNReal.ofReal ((P.card.choose m) * 2 ^ m *
        Real.exp (-min (20 * m * κ ^ 2 / 3) (κ * sigN N / (3 * lt2θ N)))) := by
  classical
  have h := lt2_Ot_count (P.image g) (fun q hq => by
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hq; exact hne p hp) hκ m hm
  rw [Finset.card_image_of_injOn hg] at h
  refine le_trans (le_of_eq ?_) h
  congr 1; ext w; simp only [Set.mem_setOf_eq]
  have e : (P.filter fun p => κ * sigN N ≤ |lt2Ot w (g p)|).card =
      ((P.image g).filter fun q => κ * sigN N ≤ |lt2Ot w q|).card :=
    lt2_card_filter_image P g hg (fun q => κ * sigN N ≤ |lt2Ot w q|)
  rw [e]

theorem lt2_N0_count_img {α : Type*} {b : Bool} (Λ : Finset (Fin N)) (P : Finset α) (g : α → LT2Idx N)
    (hg : Set.InjOn g P) (hodd : ∀ p ∈ P, ((g p).2.1 ∩ Λ).card % 2 = 1)
    (hT : ∀ p ∈ P, ∀ p' ∈ P, (g p).2.1 = (g p').2.1 → symmDiff (g p).2.2 (g p').2.2 ≠ Λ)
    (hN : 8 * (1 / 2 : ℝ) ^ N ≤ lt2tG N) (hN0 : N ≠ 0) {κ : ℝ} (hκ : 0 < κ) (m : ℕ) (hm : 1 ≤ m) :
    cubeM N {w | m ≤ (P.filter fun p => κ * sigN N ≤ |lt2N0 Λ b w (g p)|).card} ≤
      ENNReal.ofReal ((P.card.choose m) * 2 ^ m *
        (Real.exp (-min (3 * m * κ ^ 2 / (2 + m / (N : ℝ) ^ 4)) (κ * sigN N / lt2θ N)) +
          (lt2B2 N + (P.card : ℝ) ^ 2 * lt2Bpair N))) := by
  classical
  have h := lt2_N0_count (b := b) Λ (P.image g)
    (fun α hα => by obtain ⟨p, hp, rfl⟩ := mem_image.1 hα; exact hodd p hp)
    (fun α hα α' hα' h => by
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hα; obtain ⟨p', hp', rfl⟩ := mem_image.1 hα'
      exact hT p hp p' hp' h) hN hN0 hκ m hm
  rw [Finset.card_image_of_injOn hg] at h
  refine le_trans (le_of_eq ?_) h
  congr 1; ext w; simp only [Set.mem_setOf_eq]
  have e : (P.filter fun p => κ * sigN N ≤ |lt2N0 Λ b w (g p)|).card =
      ((P.image g).filter fun q => κ * sigN N ≤ |lt2N0 Λ b w q|).card :=
    lt2_card_filter_image P g hg (fun q => κ * sigN N ≤ |lt2N0 Λ b w q|)
  rw [e]

/-- `C(d,m) ≤ (e d / m)^m`, in the form `C(d,m) ≤ (e D)^m` for `d ≤ D m`. -/
lemma lt2_choose_le {d m : ℕ} {D : ℝ} (hD : 0 ≤ D) (hd : (d : ℝ) ≤ D * m) :
    ((d.choose m : ℕ) : ℝ) ≤ (Real.exp 1 * D) ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : ((d.choose m : ℕ) : ℝ) ≤ (d : ℝ) ^ m / m.factorial := Nat.choose_le_pow_div m d
  have h2 : (m : ℝ) ^ m / m.factorial ≤ Real.exp m := Real.pow_div_factorial_le_exp (m : ℝ) hmr.le m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  calc ((d.choose m : ℕ) : ℝ) ≤ (d : ℝ) ^ m / m.factorial := h1
    _ ≤ (D * m) ^ m / m.factorial := by gcongr
    _ = D ^ m * ((m : ℝ) ^ m / m.factorial) := by rw [mul_pow]; ring
    _ ≤ D ^ m * Real.exp m := by gcongr
    _ = (Real.exp 1 * D) ^ m := by rw [mul_pow, ← Real.exp_nat_mul, mul_one, mul_comm]

/-- **The binomial asymptotics.** -/
lemma lt2_binom_le {d m : ℕ} {D L X : ℝ} (hD : 1 ≤ D) (hd : (d : ℝ) ≤ D * m)
    (hX : L + m * Real.log (2 * Real.exp 1 * D) ≤ X) :
    ((d.choose m : ℕ) : ℝ) * 2 ^ m * Real.exp (-X) ≤ Real.exp (-L) := by
  have hc := lt2_choose_le (by linarith) hd
  have hpos : 0 < 2 * Real.exp 1 * D := by positivity
  calc ((d.choose m : ℕ) : ℝ) * 2 ^ m * Real.exp (-X) ≤ (Real.exp 1 * D) ^ m * 2 ^ m * Real.exp (-X) := by
        gcongr
    _ = Real.exp (m * Real.log (2 * Real.exp 1 * D)) * Real.exp (-X) := by
        rw [Real.exp_nat_mul, Real.exp_log hpos, ← mul_pow]; ring_nf
    _ = Real.exp (m * Real.log (2 * Real.exp 1 * D) - X) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-L) := Real.exp_le_exp.2 (by linarith)

end Census
end IIT
