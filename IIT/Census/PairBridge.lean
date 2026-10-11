/-
Census pair step, part 3: from the cause factors `U` to the superblock statistics.

With `x = flipP s z` (so that `y z s r j = x r j` on the cube) and the superblock coordinates
`Ψ x`, the block sums of pair `k = {2k, 2k+1}` are
`U(i, t) = 4 ∑_w ∑_π P_w(π) x_w(π[k ↦ t_k], i)`; their character contrasts are the statistics
`Tst`, summed over all superblocks.  If the contrasts of both units are positive for all three
characters (`goodT`), the all-`false` pair state strictly maximises both block sums, so
`sameArg` holds; the local box `Ek` on the superblock of `s` gives `effBox`.
-/
import IIT.Census.PairMoments

namespace IIT
namespace Census

open MeasureTheory Finset

noncomputable section

variable {L n : ℕ}

/-! ### Pair bits -/

/-- The bits of pair `k` of a state. -/
def tb (t : State (2 * L + n)) (k : Fin L) : PS := fun e => t (eCol L n (Sum.inl (k, e)))

lemma pa_eq (k : Fin L) (hk : 2 * (k : ℕ) + 1 < 2 * L + n) :
    pa (2 * L + n) k hk = eCol L n (Sum.inl (k, 0)) := by
  ext; simp [pa]

lemma pb_eq (k : Fin L) (hk : 2 * (k : ℕ) + 1 < 2 * L + n) :
    pb (2 * L + n) k hk = eCol L n (Sum.inl (k, 1)) := by
  ext; simp [pb]

/-- The pair `k` as a set of units. -/
abbrev pairS (L n : ℕ) (k : Fin L) : Finset (Fin (2 * L + n)) :=
  {eCol L n (Sum.inl (k, 0)), eCol L n (Sum.inl (k, 1))}

lemma mem_pairS (k : Fin L) (c : Col L n) :
    eCol L n c ∈ pairS L n k ↔ ∃ e, c = Sum.inl (k, e) := by
  simp only [pairS, Finset.mem_insert, Finset.mem_singleton, (eCol L n).injective.eq_iff]
  constructor
  · rintro (h | h) <;> exact ⟨_, h⟩
  · rintro ⟨e, rfl⟩
    fin_cases e <;> simp

lemma card_pairS (k : Fin L) : (pairS L n k).card = 2 := by
  rw [Finset.card_pair]
  intro h
  have := (eCol L n).injective h
  simp at this

lemma merge_eRow (k : Fin L) (t : State (2 * L + n)) (π : Pb L) (w : Outer n) :
    merge (pairS L n k) t (eRow L n (π, w)) = eRow L n (Function.update π k (tb t k), w) := by
  funext j
  obtain ⟨c, rfl⟩ := (eCol L n).surjective j
  rw [eRow_eCol]
  by_cases hc : eCol L n c ∈ pairS L n k
  · rw [merge_mem hc]
    obtain ⟨e, rfl⟩ := (mem_pairS k c).mp hc
    simp [rowFun, tb]
  · rw [merge_not_mem hc, eRow_eCol]
    rcases c with ⟨k', e⟩ | j
    · have hk : k' ≠ k := by
        rintro rfl; exact hc ((mem_pairS k' _).mpr ⟨e, rfl⟩)
      simp [rowFun, Function.update_of_ne hk]
    · rfl

lemma flip_eRow (π : Pb L) (w : Outer n) (k : Fin L) (e : Fin 2) :
    flip (eRow L n (π, w)) (eCol L n (Sum.inl (k, e))) =
      eRow L n (Function.update π k (Function.update (π k) e (!(π k e))), w) := by
  funext j
  obtain ⟨c, rfl⟩ := (eCol L n).surjective j
  rw [eRow_eCol]
  unfold flip
  by_cases hc : c = Sum.inl (k, e)
  · subst hc; simp [rowFun]
  · rw [Function.update_of_ne (fun h => hc ((eCol L n).injective h)), eRow_eCol]
    rcases c with ⟨k', e'⟩ | j
    · by_cases hk : k' = k
      · subst hk
        have he : e' ≠ e := fun h => hc (by rw [h])
        simp [rowFun, Function.update_of_ne he]
      · simp [rowFun, Function.update_of_ne hk]
    · rfl

/-! ### The block sums in superblock coordinates -/

lemma U_eq_sum {N : ℕ} (z : Param N) (s t : State N) (S : Finset (Fin N)) (i : Fin N) :
    U z s S i t = 2 ^ S.card * ∑ v : State N, y z s (merge S t v) i * rowProd z s v := by
  unfold U blockW
  have h1 : ∀ w : State N, y z s (merge S t w) i * ∑ v ∈ agree Sᶜ w, rowProd z s v =
      ∑ v : State N, if w ∈ agree Sᶜ v then y z s (merge S t v) i * rowProd z s v else 0 := by
    intro w
    rw [Finset.mul_sum, ← Finset.sum_filter]
    have hset : agree Sᶜ w = univ.filter (fun v => w ∈ agree Sᶜ v) := by
      ext v; simp only [mem_agree, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h j hj => (h j hj).symm, fun h j hj => (h j hj).symm⟩
    rw [← hset]
    refine Finset.sum_congr rfl fun v hv => ?_
    have : merge S t w = merge S t v := by
      funext j
      by_cases hj : j ∈ S
      · simp [merge, hj]
      · simp [merge, hj, (mem_agree.mp hv) j (Finset.mem_compl.mpr hj)]
    rw [this]
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have : univ.filter (fun w => w ∈ agree Sᶜ v) = agree Sᶜ v := by ext; simp
  rw [this, card_agree, Finset.card_compl, Fintype.card_fin,
    Nat.sub_sub_self ((Finset.card_le_univ S).trans_eq (Fintype.card_fin N))]
  push_cast; ring

/-- Unnormalised block sum of unit `(k, e)` at pair state `u`, over all superblocks. -/
def Ubar (ω : Om L n) (k : Fin L) (e : Fin 2) (u : PS) : ℝ :=
  ∑ w, ∑ π, rowP (ω w) π * clamp01 (ω w (cpt π k (u, e)))

lemma Ψ_mem_Icc {x : Param (2 * L + n)} (hx : x ∈ cube (2 * L + n)) (w : Outer n)
    (i : LI L n) : Ψ L n x w i ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Ψ_apply]; exact hx _ _

lemma rowProd_eRow {z : Param (2 * L + n)} (hz : z ∈ cube (2 * L + n)) (s : State (2 * L + n))
    (π : Pb L) (w : Outer n) :
    rowProd z s (eRow L n (π, w)) = rowP (Ψ L n (flipP s z) w) π := by
  unfold rowProd rowP
  rw [← (eCol L n).prod_comp]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [clamp01_of_mem (Ψ_mem_Icc (flipP_cube hz s) w (π, c)), Ψ_apply, y_eq hz]

lemma U_pair {z : Param (2 * L + n)} (hz : z ∈ cube (2 * L + n)) (s t : State (2 * L + n))
    (k : Fin L) (e : Fin 2) :
    U z s (pairS L n k) (eCol L n (Sum.inl (k, e))) t = 4 * Ubar (Ψ L n (flipP s z)) k e (tb t k) := by
  rw [U_eq_sum, card_pairS, ← (eRow L n).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  unfold Ubar
  norm_num
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun π _ => ?_
  rw [merge_eRow, rowProd_eRow hz, mul_comm, y_eq hz,
    clamp01_of_mem (Ψ_mem_Icc (flipP_cube hz s) w _), Ψ_apply]
  rfl

/-- The statistics summed over all superblocks. -/
def Tfull (ω : Om L n) (a : Ix L) : ℝ := ∑ w, Tst (ω w) a

lemma Tfull_eq (ω : Om L n) (k : Fin L) (ε : Fin 2) (c : Fin 3) :
    Tfull ω (k, ε, c) = ∑ u, chi c u * ∑ e, sgn ε e * Ubar ω k e u := by
  have h1 : ∀ w π, rowP (ω w) π * ctr (ω w) (k, ε, c) π = ∑ u, chi c u * ∑ e, sgn ε e *
      (rowP (ω w) π * clamp01 (ω w (cpt π k (u, e)))) := by
    intro w π
    simp only [ctr, coef, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun e _ => by ring
  unfold Tfull Tst Ubar
  simp_rw [h1]
  calc ∑ w, ∑ π, ∑ u, chi c u * ∑ e, sgn ε e * (rowP (ω w) π * clamp01 (ω w (cpt π k (u, e))))
      = ∑ w, ∑ u, ∑ π, chi c u * ∑ e, sgn ε e *
          (rowP (ω w) π * clamp01 (ω w (cpt π k (u, e)))) :=
        Finset.sum_congr rfl fun w _ => Finset.sum_comm
    _ = ∑ u, ∑ w, ∑ π, chi c u * ∑ e, sgn ε e *
          (rowP (ω w) π * clamp01 (ω w (cpt π k (u, e)))) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun u _ => ?_
        simp only [Finset.mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.sum_comm]

/-! ### Positive contrasts give `sameArg` -/

/-- The all-`false` pair state. -/
def u₀ : PS := fun _ => false

lemma lt_of_contrasts (A : PS → ℝ) (h : ∀ c, 0 < ∑ u, chi c u * A u) (u : PS) (hu : u ≠ u₀) :
    A u < A u₀ := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [sum_PS, chi, sg] at h0 h1 h2
  simp at h0 h1 h2
  have hu₀ : u₀ = ![false, false] := by ext i; fin_cases i <;> rfl
  rw [hu₀] at hu ⊢
  have hu' : u = ![u 0, u 1] := by ext i; fin_cases i <;> rfl
  rw [hu'] at hu ⊢
  cases h0' : u 0 <;> cases h1' : u 1 <;> simp [h0', h1'] at hu ⊢ <;> linarith

/-- Contrast positivity of both units of pair `k`. -/
def goodT (T : Ix L → ℝ) (k : Fin L) : Prop := ∀ c, |T (k, 1, c)| < T (k, 0, c)

lemma sameArg_of_goodT {z : Param (2 * L + n)} (hz : z ∈ cube (2 * L + n))
    (s : State (2 * L + n)) (k : Fin L) (hk : 2 * (k : ℕ) + 1 < 2 * L + n)
    (hg : goodT (Tfull (Ψ L n (flipP s z))) k) :
    sameArg z s (pa (2 * L + n) k hk) (pb (2 * L + n) k hk) := by
  set ω := Ψ L n (flipP s z)
  have hpos : ∀ e : Fin 2, ∀ c, 0 < ∑ u, chi c u * Ubar ω k e u := by
    intro e c
    have hc := hg c
    have e0 : Tfull ω (k, 0, c) = ∑ u, chi c u * Ubar ω k 0 u + ∑ u, chi c u * Ubar ω k 1 u := by
      rw [Tfull_eq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      simp [Fin.sum_univ_two, sgn]; ring
    have e1 : Tfull ω (k, 1, c) = ∑ u, chi c u * Ubar ω k 0 u - ∑ u, chi c u * Ubar ω k 1 u := by
      rw [Tfull_eq, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      simp [Fin.sum_univ_two, sgn]; ring
    rw [e0, e1] at hc
    obtain ⟨hc1, hc2⟩ := abs_lt.mp hc
    fin_cases e
    · simp only [Fin.zero_eta, Fin.isValue]; linarith
    · simp only [Fin.mk_one, Fin.isValue]; linarith
  refine ⟨fun _ => false, fun t ht => ?_⟩
  rw [pa_eq, pb_eq] at ht ⊢
  have htb : tb t k ≠ u₀ := by
    intro h
    rcases ht with ht | ht
    · exact ht (congrFun h 0)
    · exact ht (congrFun h 1)
  have ht₀ : tb (fun _ => false : State (2 * L + n)) k = u₀ := rfl
  rw [U_pair hz, U_pair hz, U_pair hz, U_pair hz, ht₀]
  exact ⟨by linarith [lt_of_contrasts _ (hpos 0) _ htb],
    by linarith [lt_of_contrasts _ (hpos 1) _ htb]⟩

/-! ### The local box gives `effBox` -/

/-- Target interval of the current-state entry. -/
def Jb (b : Bool) : Set ℝ := if b then Set.Ioo (99 / 100) 1 else Set.Ioo 0 (1 / 100)

/-- Target interval of the entry `(cpt π₀ k q)`. -/
def Jt (π₀ : Pb L) (k : Fin L) (q : Qt) : Set ℝ :=
  if q.1 = π₀ k then Jb (π₀ k q.2) else Set.Ioo (9 / 20) (11 / 20)

/-- The local effect-side box of pair `k` on the superblock of `s`. -/
def Ek (π₀ : Pb L) (k : Fin L) (ζ : Loc L n) : Prop := ∀ q : Qt, ζ (cpt π₀ k q) ∈ Jt π₀ k q

lemma flipC_Jb (b : Bool) {x : ℝ} (hx : x ∈ Jb b) : flipC b x ∈ Set.Ioo (99 / 100 : ℝ) 1 := by
  cases b <;> simp [Jb, flipC] at hx ⊢ <;> constructor <;> linarith [hx.1, hx.2]

lemma flipC_mid (b : Bool) {x : ℝ} (hx : x ∈ Set.Ioo (9 / 20 : ℝ) (11 / 20)) :
    flipC b x ∈ Set.Ioo (9 / 20 : ℝ) (11 / 20) := by
  cases b <;> simp [flipC] at hx ⊢ <;> constructor <;> linarith [hx.1, hx.2]

lemma z_eq_flip {z : Param (2 * L + n)} (s : State (2 * L + n)) (r : State (2 * L + n))
    (j : Fin (2 * L + n)) : z r j = flipC (s j) (flipP s z r j) :=
  (congrFun (congrFun (flipP_invol s z) r) j).symm

lemma effBox_of_Ek {z : Param (2 * L + n)} {π₀ : Pb L} {w₀ : Outer n} (k : Fin L)
    (hk : 2 * (k : ℕ) + 1 < 2 * L + n)
    (hE : Ek π₀ k (Ψ L n (flipP (eRow L n (π₀, w₀)) z) w₀)) :
    effBox z (eRow L n (π₀, w₀)) (pa (2 * L + n) k hk) (pb (2 * L + n) k hk) := by
  set s := eRow L n (π₀, w₀)
  rw [pa_eq, pb_eq]
  have hval : ∀ (u : PS) (e : Fin 2), flipP s z (eRow L n (Function.update π₀ k u, w₀))
      (eCol L n (Sum.inl (k, e))) ∈ Jt π₀ k (u, e) := by
    intro u e
    have := hE (u, e)
    rwa [cpt, Ψ_apply] at this
  have hs_bit : ∀ e : Fin 2, s (eCol L n (Sum.inl (k, e))) = π₀ k e := by
    intro e; simp [s, rowFun]
  have hs_row : s = eRow L n (Function.update π₀ k (π₀ k), w₀) := by simp [s]
  have hcur : ∀ e : Fin 2, z s (eCol L n (Sum.inl (k, e))) ∈ Set.Ioo (99 / 100 : ℝ) 1 := by
    intro e
    rw [z_eq_flip (z := z) s, hs_bit]
    have := hval (π₀ k) e
    simp only [Jt, if_true] at this
    rw [← hs_row] at this
    exact flipC_Jb _ this
  have hoth : ∀ u : PS, u ≠ π₀ k → ∀ e : Fin 2,
      z (eRow L n (Function.update π₀ k u, w₀)) (eCol L n (Sum.inl (k, e))) ∈
        Set.Ioo (9 / 20 : ℝ) (11 / 20) := by
    intro u hu e
    rw [z_eq_flip (z := z) s, hs_bit]
    have := hval u e
    simp only [Jt, if_neg hu] at this
    exact flipC_mid _ this
  refine ⟨hcur 0, hcur 1, fun r hr => ?_⟩
  have hf0 : flip s (eCol L n (Sum.inl (k, 0))) =
      eRow L n (Function.update π₀ k (Function.update (π₀ k) 0 (!(π₀ k 0))), w₀) := by
    rw [flip_eRow]
  have hf1 : flip s (eCol L n (Sum.inl (k, 1))) =
      eRow L n (Function.update π₀ k (Function.update (π₀ k) 1 (!(π₀ k 1))), w₀) := by
    rw [flip_eRow]
  have hf01 : flip (flip s (eCol L n (Sum.inl (k, 0)))) (eCol L n (Sum.inl (k, 1))) =
      eRow L n (Function.update π₀ k (Function.update (Function.update (π₀ k) 0 (!(π₀ k 0))) 1
        (!(π₀ k 1))), w₀) := by
    rw [hf0, flip_eRow]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl
  · rw [hf0]
    have hu : Function.update (π₀ k) 0 (!(π₀ k 0)) ≠ π₀ k := by
      intro h; have := congrFun h 0; simp at this
    exact ⟨hoth _ hu 0, hoth _ hu 1⟩
  · rw [hf1]
    have hu : Function.update (π₀ k) 1 (!(π₀ k 1)) ≠ π₀ k := by
      intro h; have := congrFun h 1; simp at this
    exact ⟨hoth _ hu 0, hoth _ hu 1⟩
  · rw [hf01]
    have hu : Function.update (Function.update (π₀ k) 0 (!(π₀ k 0))) 1 (!(π₀ k 1)) ≠ π₀ k := by
      intro h; have := congrFun h 1; simp at this
    exact ⟨hoth _ hu 0, hoth _ hu 1⟩

/-! ### The reduction to superblock coordinates -/

/-- The bad event in superblock coordinates. -/
def BadΩ (π₀ : Pb L) (w₀ : Outer n) : Set (Om L n) :=
  {ω | ∀ k : Fin L, ¬ (Ek π₀ k (ω w₀) ∧ goodT (Tfull ω) k)}

lemma allBad_sub (π₀ : Pb L) (w₀ : Outer n) :
    allBad (2 * L + n) L (eRow L n (π₀, w₀)) ⊆
      flipE (eRow L n (π₀, w₀)) ⁻¹' (cube (2 * L + n) ∩ Ψ L n ⁻¹' BadΩ π₀ w₀) := by
  rintro z ⟨hz, hbad⟩
  refine ⟨flipP_cube hz _, fun k ⟨hE, hg⟩ => ?_⟩
  have hk : 2 * (k : ℕ) + 1 < 2 * L + n := by omega
  exact hbad k hk k.2 ⟨effBox_of_Ek k hk hE, sameArg_of_goodT hz _ k hk hg⟩

lemma volume_allBad_le (π₀ : Pb L) (w₀ : Outer n) :
    volume (allBad (2 * L + n) L (eRow L n (π₀, w₀))) ≤ omM L n (BadΩ π₀ w₀) := by
  calc volume (allBad (2 * L + n) L (eRow L n (π₀, w₀)))
      ≤ volume (flipE (eRow L n (π₀, w₀)) ⁻¹' (cube (2 * L + n) ∩ Ψ L n ⁻¹' BadΩ π₀ w₀)) :=
        measure_mono (allBad_sub π₀ w₀)
    _ = omM L n (BadΩ π₀ w₀) := by
        rw [(mp_flipE _).measure_preimage_equiv, volume_cube_inter,
          (mp_Ψ L n).measure_preimage_equiv]

end

end Census
end IIT
