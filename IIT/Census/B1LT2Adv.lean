/-
Census, B1 lemma LT2, module M6d-2: visible differences come from adverse primitive statistics.

Kinds `k = (st, ci, β, ra, rb, ta, tb)`: `st ∈ {0,1,2}` (weight / own entry / shifted entry), column `a` or `b`
(`ci`), parity class `β`, `R = sub(ra, rb)`, `T = sub(ta, tb)` (subsets of `{a,b}`); the class functional of the
shifted entries is `Λ = D₁` for `R = {a}` and `D₂` otherwise.
`lt2_visible_adv`: if all valid kinds of the pair are `< κσ`, every column difference of `NumNs` is `≤ 15κσ`.
-/
import IIT.Census.B1LT2Kinds

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {N : ℕ}

/-- The subset of `{a,b}` coded by two bits. -/
def lt2sub (a b : Fin N) (x y : Bool) : Finset (Fin N) := (if x then {a} else ∅) ∪ (if y then {b} else ∅)

/-- The class functional for the shift `R = sub(ra, rb)`. -/
def lt2Lam (ra rb : Bool) : Finset (Fin N) := if ra = true ∧ rb = false then lt2D1 N else lt2D2 N

/-- Kinds of primitive statistics. -/
abbrev LT2Kind := Fin 3 × Bool × Bool × Bool × Bool × Bool × Bool

/-- The statistic of kind `k` of the pair `(a,b)`. -/
noncomputable def lt2stat (w : Param N) (a b : Fin N) (k : LT2Kind) : ℝ :=
  if k.1 = 0 then lt2mT w (lt2sub a b k.2.2.2.2.2.1 k.2.2.2.2.2.2)
  else if k.1 = 1 then lt2Ot w (lt2col a b k.2.1, lt2sub a b k.2.2.2.2.2.1 k.2.2.2.2.2.2)
  else lt2N0 (lt2Lam k.2.2.2.1 k.2.2.2.2.1) k.2.2.1 w
    (lt2col a b k.2.1, lt2sub a b k.2.2.2.1 k.2.2.2.2.1, lt2sub a b k.2.2.2.2.2.1 k.2.2.2.2.2.2)

/-- Valid kinds: `T ≠ ∅`, and `R ≠ ∅` for shifted entries. -/
def lt2kValid (k : LT2Kind) : Prop :=
  (k.2.2.2.2.2.1 = true ∨ k.2.2.2.2.2.2 = true) ∧ (k.1 = 2 → (k.2.2.2.1 = true ∨ k.2.2.2.2.1 = true))

lemma lt2_powerset_pair {a b : Fin N} (hab : a ≠ b) :
    ({a, b} : Finset (Fin N)).powerset = (univ : Finset (Bool × Bool)).image fun x => lt2sub a b x.1 x.2 := by
  ext R
  simp only [mem_powerset, mem_image, mem_univ, true_and, Prod.exists]
  constructor
  · intro hR
    refine ⟨decide (a ∈ R), decide (b ∈ R), ?_⟩
    ext j
    simp only [lt2sub, mem_union]
    constructor
    · rintro (h | h) <;> split_ifs at h with hh <;> simp_all
    · intro hj
      have := hR hj
      simp only [mem_insert, mem_singleton] at this
      rcases this with rfl | rfl
      · left; simp [hj]
      · right; simp [hj]
  · rintro ⟨x, y, rfl⟩
    intro j hj
    simp only [lt2sub, mem_union] at hj
    split_ifs at hj <;> simp_all

lemma lt2_sub_nonempty_iff {a b : Fin N} (x y : Bool) : (lt2sub a b x y).Nonempty ↔ (x = true ∨ y = true) := by
  cases x <;> cases y <;> simp [lt2sub]

/-- Sums over subsets of `{a,b}` are bounded by sums over the bit codes. -/
lemma lt2_sum_pow_le {a b : Fin N} (hab : a ≠ b) (f : Finset (Fin N) → ℝ) (hf : ∀ R, 0 ≤ f R)
    (P : Finset (Fin N) → Prop) [DecidablePred P] :
    ∑ R ∈ ({a, b} : Finset (Fin N)).powerset.filter P, f R ≤
      ∑ x : Bool × Bool, (if P (lt2sub a b x.1 x.2) then f (lt2sub a b x.1 x.2) else 0) := by
  classical
  rw [lt2_powerset_pair hab, Finset.filter_image, ← Finset.sum_filter]
  refine Finset.sum_image_le_of_nonneg fun x _ => hf _

/-- **Visible differences come from adverse statistics.** -/
theorem lt2_visible_adv (w : Param N) {a b : Fin N} (ha : a ∈ lt2D1 N) (hb : b ∈ lt2D2 N) (c : Bool)
    (t0 t : State N) {g : ℝ} (hg : 0 ≤ g)
    (hk : ∀ k : LT2Kind, lt2kValid k → k.2.1 = c → |lt2stat w a b k| < g) :
    |lt2NumNs w {a, b} t0 (lt2col a b c) - lt2NumNs w {a, b} t (lt2col a b c)| ≤ 15 * g := by
  classical
  have hab := lt2_D1_ne_D2 ha hb
  set i := lt2col a b c
  -- every `|G| < 5g/2`
  have hG : ∀ x y u v : Bool, (u = true ∨ v = true) → |lt2G w i (lt2sub a b x y) (lt2sub a b u v)| ≤ 5 / 2 * g := by
    intro x y u v huv
    have hm := hk (0, c, false, x, y, u, v) ⟨huv, by simp⟩ rfl
    simp only [lt2stat, ↓reduceIte] at hm
    by_cases hR : x = true ∨ y = true
    · rw [lt2G_shift w (lt2Lam x y)]
      have h0 := hk (2, c, false, x, y, u, v) ⟨huv, fun _ => hR⟩ rfl
      have h1 := hk (2, c, true, x, y, u, v) ⟨huv, fun _ => hR⟩ rfl
      simp only [lt2stat, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte] at h0 h1
      calc |1 / 2 * lt2mT w (lt2sub a b u v) + lt2N0 (lt2Lam x y) true w (i, lt2sub a b x y, lt2sub a b u v) +
            lt2N0 (lt2Lam x y) false w (i, lt2sub a b x y, lt2sub a b u v)|
          ≤ 1 / 2 * |lt2mT w (lt2sub a b u v)| + |lt2N0 (lt2Lam x y) true w (i, lt2sub a b x y, lt2sub a b u v)| +
            |lt2N0 (lt2Lam x y) false w (i, lt2sub a b x y, lt2sub a b u v)| := by
            refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ le_rfl)) le_rfl)
            rw [abs_mul]; norm_num
        _ ≤ 5 / 2 * g := by linarith
    · push_neg at hR
      have hx : x = false := by simpa using hR.1
      have hy : y = false := by simpa using hR.2
      subst hx; subst hy
      have hR0 : lt2sub a b false false = ∅ := by simp [lt2sub]
      rw [hR0, lt2G_empty]
      have h1 := hk (1, c, false, false, false, u, v) ⟨huv, by simp⟩ rfl
      simp only [lt2stat, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte] at h1
      calc |3 / 4 * lt2mT w (lt2sub a b u v) + lt2Ot w (i, lt2sub a b u v)|
          ≤ 3 / 4 * |lt2mT w (lt2sub a b u v)| + |lt2Ot w (i, lt2sub a b u v)| := by
            refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl); rw [abs_mul]; norm_num
        _ ≤ 5 / 2 * g := by linarith
  have hD2 := lt2_D2 w {a, b} t0 t i
  rw [card_pair hab] at hD2
  -- bound the double sum
  have hsum : ∑ R ∈ ({a, b} : Finset (Fin N)).powerset,
      ∑ T ∈ ({a, b} : Finset (Fin N)).powerset.filter (fun T => T.Nonempty), |lt2G w i R T| ≤ 4 * (3 * (5 / 2 * g)) := by
    calc ∑ R ∈ ({a, b} : Finset (Fin N)).powerset,
          ∑ T ∈ ({a, b} : Finset (Fin N)).powerset.filter (fun T => T.Nonempty), |lt2G w i R T|
        ≤ ∑ R ∈ ({a, b} : Finset (Fin N)).powerset, 3 * (5 / 2 * g) := by
          refine Finset.sum_le_sum fun R hR => ?_
          obtain ⟨⟨x, y⟩, -, rfl⟩ := mem_image.1 ((lt2_powerset_pair hab) ▸ hR)
          refine (lt2_sum_pow_le hab (fun T => |lt2G w i (lt2sub a b x y) T|) (fun _ => abs_nonneg _)
            (fun T => T.Nonempty)).trans ?_
          calc ∑ z : Bool × Bool, (if (lt2sub a b z.1 z.2).Nonempty then
                |lt2G w i (lt2sub a b x y) (lt2sub a b z.1 z.2)| else 0)
              ≤ ∑ z : Bool × Bool, (if z = (false, false) then 0 else 5 / 2 * g) := by
                refine Finset.sum_le_sum fun z _ => ?_
                obtain ⟨u, v⟩ := z
                by_cases hz : (u, v) = (false, false)
                · simp only [Prod.mk.injEq] at hz; obtain ⟨rfl, rfl⟩ := hz; simp [lt2sub]
                · rw [if_neg hz]
                  split_ifs with hne
                  · exact hG x y u v ((lt2_sub_nonempty_iff u v).1 hne)
                  · positivity
            _ = 3 * (5 / 2 * g) := by simp [Fintype.sum_prod_type]; ring
      _ ≤ 4 * (3 * (5 / 2 * g)) := by
          rw [Finset.sum_const, Finset.card_powerset, card_pair hab, nsmul_eq_mul]; norm_num
  calc _ ≤ 2 * (∑ R ∈ ({a, b} : Finset (Fin N)).powerset,
        ∑ T ∈ ({a, b} : Finset (Fin N)).powerset.filter (fun T => T.Nonempty), |lt2G w i R T|) / 2 ^ 2 := hD2
    _ ≤ 2 * (4 * (3 * (5 / 2 * g))) / 2 ^ 2 := by gcongr
    _ = 15 * g := by ring

end Census
end IIT
