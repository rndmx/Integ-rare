/-
Reduction of the pair step to an event about `L` fixed disjoint pairs.

A pair `{a,b}` is *good* when its eight block entries lie in `effBox` and one state of the pair
strictly maximises both block sums `U a ·` and `U b ·` (`sameArg`). A good pair has `φ_s > 0`
(`phi_pair_pos`), so "no proper candidate has positive `φ_s`" forces every one of the `L`
pairs `{2k, 2k+1}` to be bad (on the open cube).
-/
import IIT.Census.PairPos

namespace IIT
namespace Census

open MeasureTheory Finset

variable {N : ℕ}

/-- One state of the pair strictly maximises both block sums. -/
def sameArg (z : Param N) (s : State N) (a b : Fin N) : Prop :=
  ∃ t₀ : State N, ∀ t : State N, (t a ≠ t₀ a ∨ t b ≠ t₀ b) →
    U z s {a, b} a t < U z s {a, b} a t₀ ∧ U z s {a, b} b t < U z s {a, b} b t₀

/-- `U` sees a state only through its restriction to `S`. -/
lemma U_congr (z : Param N) (s : State N) (S : Finset (Fin N)) (i : Fin N) {t t' : State N}
    (h : ∀ j ∈ S, t j = t' j) : U z s S i t = U z s S i t' := by
  unfold U
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 2
  funext j
  by_cases hj : j ∈ S
  · simp [merge, hj, h j hj]
  · simp [merge, hj]

lemma hU_of_sameArg {z : Param N} (hz : z ∈ openCube N) (s : State N) {a b : Fin N}
    (hab : a ≠ b) (h : sameArg z s a b) :
    ∀ tc : State N, (∀ t, U z s {a, b} a t * U z s {a, b} b t ≤
        U z s {a, b} a tc * U z s {a, b} b tc) →
      U z s {a, b} a (flip tc b) < U z s {a, b} a tc ∧
        U z s {a, b} b (flip tc a) < U z s {a, b} b tc := by
  obtain ⟨t₀, ht₀⟩ := h
  intro tc hmax
  have hpos : ∀ i t, 0 < U z s {a, b} i t := fun i t => U_pos hz s _ i t
  -- tc agrees with t₀ on the pair
  have hagree : tc a = t₀ a ∧ tc b = t₀ b := by
    by_contra hne
    have hne' : tc a ≠ t₀ a ∨ tc b ≠ t₀ b := by tauto
    obtain ⟨h1, h2⟩ := ht₀ tc hne'
    have := hmax t₀
    nlinarith [hpos a tc, hpos b tc, hpos a t₀, hpos b t₀, mul_lt_mul'' h1 h2 (hpos a tc).le
      (hpos b tc).le]
  have heq : ∀ i, U z s {a, b} i tc = U z s {a, b} i t₀ := fun i =>
    U_congr z s _ i fun j hj => by
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hagree.1
      · rw [Finset.mem_singleton.mp hj]; exact hagree.2
  refine ⟨?_, ?_⟩
  · rw [heq a]
    refine (ht₀ (flip tc b) (Or.inr ?_)).1
    simp [flip, hagree.2]
  · rw [heq b]
    refine (ht₀ (flip tc a) (Or.inl ?_)).2
    simp [flip, hagree.1]

/-- A good pair has positive `φ_s`. -/
lemma phi_pos_of_good {z : Param N} (hz : z ∈ openCube N) (s : State N) {a b : Fin N}
    (hab : a ≠ b) (hbox : effBox z s a b) (hsame : sameArg z s a b) : 0 < phi z s {a, b} :=
  phi_pair_pos z hz s hab hbox (hU_of_sameArg hz s hab hsame)

/-- The `k`-th disjoint pair `{2k, 2k+1}`. -/
def pa (N : ℕ) (k : ℕ) (hk : 2 * k + 1 < N) : Fin N := ⟨2 * k, by omega⟩
def pb (N : ℕ) (k : ℕ) (hk : 2 * k + 1 < N) : Fin N := ⟨2 * k + 1, hk⟩

/-- All of the first `L` pairs are bad. -/
def allBad (N L : ℕ) (s : State N) : Set (Param N) :=
  {z | z ∈ cube N ∧ ∀ k (hk : 2 * k + 1 < N), k < L →
    ¬ (effBox z s (pa N k hk) (pb N k hk) ∧ sameArg z s (pa N k hk) (pb N k hk))}

/-- **Reduction.** With at least three units, "no proper candidate has positive `φ_s`" is
contained in the null boundary of the cube together with "all of the first `L` pairs are bad". -/
lemma noPos_subset (hN : 3 ≤ N) (L : ℕ) (s : State N) :
    {z | z ∈ cube N ∧ ∀ S : Finset (Fin N), S ≠ univ → phi z s S ≤ 0} ⊆
      (cube N \ openCube N) ∪ allBad N L s := by
  rintro z ⟨hz, hno⟩
  by_cases ho : z ∈ openCube N
  · refine Or.inr ⟨hz, fun k hk _ hgood => ?_⟩
    have hab : pa N k hk ≠ pb N k hk := by simp [pa, pb, Fin.ext_iff]
    have hne : ({pa N k hk, pb N k hk} : Finset (Fin N)) ≠ univ := by
      intro h
      have hc := congrArg Finset.card h
      rw [Finset.card_univ, Fintype.card_fin, Finset.card_pair hab] at hc
      omega
    exact absurd (phi_pos_of_good ho s hab hgood.1 hgood.2) (not_lt.mpr (hno _ hne))
  · exact Or.inl ⟨hz, ho⟩

end Census
end IIT
