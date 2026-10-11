/-
Census: the classification bridge between directional system partitions of a concrete `k`-set and
the admissible pairs `(g, δ)` of `CertDataEnum`.

The `k`-set `S` is given with an ordering `e : Fin k ↪ Fin N` onto `S`.  The profile of a partition
`θ` pulled back along `e` is the table `(i, j) ↦ [e j ∈ profile θ (e i)]`.
* `cd_classify`: the pulled-back profile of every `θ` is `cd_profOf k g δ` for an admissible pair
  (`g` sends a unit to the least unit of its block, `δ` records the block directions).
* `cd_realize`: every admissible pair is realized by some `θ`.
* `cd_orbit_sound`: a kernel check over `cd_gen k` with explicit unit permutations shows that every
  admissible profile is a relabelling of one in a given list of representatives; choosing the ordering
  `e ∘ σ` then turns any `θ` into a representative (`cd_classify_rep`).
The argument rests on the membership rule for cut sets (`cd_mem_cutSet`): for `p` a block and
`x ∈ S`, `x ∈ cutSet p ↔ x ∉ p ∧ (dir p ≠ outputs ∨ dir (partOf x) ≠ inputs)`.
-/
import IIT.Census.Profile
import IIT.Census.CertDataEnum

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- The direction code: `0` inputs, `1` outputs, `2` both. -/
def cd_code : Dir → ℕ
  | Dir.inputs => 0
  | Dir.outputs => 1
  | Dir.both => 2

/-- Decoding of direction codes. -/
def cd_decode : ℕ → Dir
  | 0 => Dir.inputs
  | 1 => Dir.outputs
  | _ => Dir.both

lemma cd_code_le (d : Dir) : cd_code d ≤ 2 := by cases d <;> simp [cd_code]

lemma cd_code_ne_one (d : Dir) : cd_code d ≠ 1 ↔ d ≠ Dir.outputs := by
  cases d <;> simp [cd_code]

lemma cd_code_ne_zero (d : Dir) : cd_code d ≠ 0 ↔ d ≠ Dir.inputs := by
  cases d <;> simp [cd_code]

lemma cd_code_ne_one' (d : Dir) : ¬ cd_code d = 1 ↔ d ≠ Dir.outputs := cd_code_ne_one d

lemma cd_code_ne_zero' (d : Dir) : ¬ cd_code d = 0 ↔ d ≠ Dir.inputs := cd_code_ne_zero d

lemma cd_decode_ne_out (x : ℕ) : cd_decode x ≠ Dir.outputs ↔ x ≠ 1 := by
  rcases x with _ | _ | x <;> simp [cd_decode]

lemma cd_decode_ne_in (x : ℕ) : cd_decode x ≠ Dir.inputs ↔ x ≠ 0 := by
  rcases x with _ | _ | x <;> simp [cd_decode]

/-- **Membership in a cut set.** -/
theorem cd_mem_cutSet {S : Finset (Fin N)} (θ : SysPartition N S) {p : Finset (Fin N)}
    (hp : p ∈ θ.parts) {x : Fin N} (hx : x ∈ S) :
    x ∈ θ.cutSet p ↔ x ∉ p ∧ (θ.dir p ≠ Dir.outputs ∨ θ.dir (θ.partOf x) ≠ Dir.inputs) := by
  obtain ⟨hxp, hxx⟩ := prof_partOf_mem θ hx
  unfold SysPartition.cutSet
  cases hd : θ.dir p
  · simp [hx]
  · simp only [ne_eq, not_true_eq_false, false_or]
    rw [Finset.mem_sup]
    constructor
    · rintro ⟨q, hq, hxq⟩
      rw [mem_filter] at hq
      have e := θ.partOf_eq hq.1 hxq
      refine ⟨fun hxp' => hq.2.1 ?_, ?_⟩
      · rw [← e, θ.partOf_eq hp hxp']
      · rw [e]; rcases hq.2.2 with h | h <;> rw [h] <;> simp
    · rintro ⟨hxp', hdx⟩
      refine ⟨θ.partOf x, mem_filter.2 ⟨hxp, fun h => hxp' (h ▸ hxx), ?_⟩, hxx⟩
      cases h : θ.dir (θ.partOf x)
      · exact absurd h hdx
      · exact Or.inl rfl
      · exact Or.inr rfl
  · simp [hx]

lemma cd_getD_ofFn {k : ℕ} (f : Fin k → ℕ) (i : Fin k) : (List.ofFn f).getD i 0 = f i := by
  simp [List.getD_eq_getElem?_getD]

section Classify

variable {k : ℕ} {S : Finset (Fin N)} (e : Fin k ↪ Fin N) (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
  (θ : SysPartition N S)

include hS

/-- The block of unit `i`. -/
noncomputable def cd_blk (i : Fin k) : Finset (Fin N) := θ.partOf (e i)

lemma cd_blk_mem (i : Fin k) : cd_blk e θ i ∈ θ.parts ∧ e i ∈ cd_blk e θ i :=
  prof_partOf_mem θ ((hS _).2 ⟨i, rfl⟩)

lemma cd_mem_blk (i j : Fin k) : e j ∈ cd_blk e θ i ↔ cd_blk e θ j = cd_blk e θ i := by
  constructor
  · intro h; exact θ.partOf_eq (cd_blk_mem e hS θ i).1 h
  · intro h; rw [← h]; exact (cd_blk_mem e hS θ j).2

/-- The least unit of the block of `i`. -/
noncomputable def cd_gmin (i : Fin k) : Fin k :=
  (univ.filter fun j : Fin k => e j ∈ cd_blk e θ i).min' ⟨i, mem_filter.2 ⟨mem_univ _, (cd_blk_mem e hS θ i).2⟩⟩

lemma cd_gmin_mem (i : Fin k) : e (cd_gmin e hS θ i) ∈ cd_blk e θ i := by
  unfold cd_gmin
  exact (mem_filter.1 (min'_mem (univ.filter fun j : Fin k => e j ∈ cd_blk e θ i) _)).2

lemma cd_gmin_le (i j : Fin k) (h : e j ∈ cd_blk e θ i) : cd_gmin e hS θ i ≤ j := by
  unfold cd_gmin
  exact min'_le (univ.filter fun j : Fin k => e j ∈ cd_blk e θ i) j (mem_filter.2 ⟨mem_univ _, h⟩)

lemma cd_gmin_eq_iff (i j : Fin k) : cd_gmin e hS θ i = cd_gmin e hS θ j ↔ cd_blk e θ i = cd_blk e θ j := by
  constructor
  · intro h
    have h1 := (cd_mem_blk e hS θ i _).1 (cd_gmin_mem e hS θ i)
    have h2 := (cd_mem_blk e hS θ j _).1 (cd_gmin_mem e hS θ j)
    rw [h] at h1
    exact h1.symm.trans h2
  · intro h
    refine le_antisymm (cd_gmin_le e hS θ i _ ?_) (cd_gmin_le e hS θ j _ ?_)
    · rw [h]; exact cd_gmin_mem e hS θ j
    · rw [← h]; exact cd_gmin_mem e hS θ i

lemma cd_blk_gmin (i : Fin k) : cd_blk e θ (cd_gmin e hS θ i) = cd_blk e θ i :=
  (cd_mem_blk e hS θ i _).1 (cd_gmin_mem e hS θ i)

lemma cd_gmin_gmin (i : Fin k) : cd_gmin e hS θ (cd_gmin e hS θ i) = cd_gmin e hS θ i :=
  (cd_gmin_eq_iff e hS θ _ _).2 (cd_blk_gmin e hS θ i)

/-- The representative map of `θ` as a list. -/
noncomputable def cd_gL : List ℕ := List.ofFn fun i => (cd_gmin e hS θ i : ℕ)

/-- The direction codes of `θ` as a list (read at representatives). -/
noncomputable def cd_dL : List ℕ :=
  List.ofFn fun i => if cd_gmin e hS θ i = i then cd_code (θ.dir (cd_blk e θ i)) else 0

lemma cd_gL_getD (i : Fin k) : (cd_gL e hS θ).getD i 0 = cd_gmin e hS θ i := cd_getD_ofFn _ i

lemma cd_dL_getD_gmin (i : Fin k) :
    (cd_dL e hS θ).getD (cd_gmin e hS θ i) 0 = cd_code (θ.dir (cd_blk e θ i)) := by
  rw [cd_dL, cd_getD_ofFn, ite_eq_left (cd_gmin_gmin e hS θ i), cd_blk_gmin]

lemma cd_classify_valid : cd_valid k (cd_gL e hS θ) (cd_dL e hS θ) = true := by
  rw [cd_valid_iff]
  refine ⟨by simp [cd_gL], by simp [cd_dL], fun i hi => ?_, ?_⟩
  · have hg := cd_gL_getD e hS θ ⟨i, hi⟩
    simp only at hg
    rw [hg]
    refine ⟨cd_gmin_le e hS θ _ _ (cd_blk_mem e hS θ _).2, ?_, ?_⟩
    · rw [cd_gL_getD e hS θ (cd_gmin e hS θ ⟨i, hi⟩), cd_gmin_gmin]
    · have hd : (cd_dL e hS θ).getD i 0 = if cd_gmin e hS θ ⟨i, hi⟩ = ⟨i, hi⟩
          then cd_code (θ.dir (cd_blk e θ ⟨i, hi⟩)) else 0 := cd_getD_ofFn _ ⟨i, hi⟩
      rw [hd]
      by_cases h : cd_gmin e hS θ ⟨i, hi⟩ = ⟨i, hi⟩
      · rw [ite_eq_left (by rw [h]), ite_eq_left h]; exact cd_code_le _
      · rw [ite_eq_right (fun h' => h (Fin.ext h')), ite_eq_right h]
  · obtain ⟨p, hp⟩ : θ.parts.Nonempty := card_pos.1 (by have := θ.two_le; omega)
    obtain ⟨x, hx⟩ := θ.parts_nonempty p hp
    obtain ⟨i0, rfl⟩ := (hS x).1 (θ.parts_subset p hp hx)
    obtain ⟨q, hq, hqp⟩ : ∃ q ∈ θ.parts, q ≠ cd_blk e θ i0 := by
      by_contra hcon
      push Not at hcon
      have : θ.parts ⊆ {cd_blk e θ i0} := fun q hq => mem_singleton.2 (hcon q hq)
      have := card_le_card this
      have := θ.two_le
      simp at *; omega
    obtain ⟨y, hy⟩ := θ.parts_nonempty q hq
    obtain ⟨i1, rfl⟩ := (hS y).1 (θ.parts_subset q hq hy)
    have hb : cd_blk e θ i1 = q := θ.partOf_eq hq hy
    have hne : cd_gmin e hS θ i1 ≠ cd_gmin e hS θ i0 := fun h =>
      hqp (hb ▸ (cd_gmin_eq_iff e hS θ _ _).1 h)
    by_cases h0 : (cd_gmin e hS θ i1 : ℕ) = 0
    · refine ⟨i0, i0.2, ?_⟩
      rw [cd_gL_getD e hS θ i0]
      intro h
      exact hne (Fin.ext (h0.trans h.symm))
    · exact ⟨i1, i1.2, by rw [cd_gL_getD e hS θ i1]; exact h0⟩

/-- **Classification.** The pulled-back profile of every partition is that of an admissible pair. -/
theorem cd_classify :
    ∃ g δ : List ℕ, cd_valid k g δ = true ∧
      ∀ i j : Fin k, (e j ∈ profile θ (e i) ↔ cd_at (cd_profOf k g δ) i j = true) := by
  refine ⟨cd_gL e hS θ, cd_dL e hS θ, cd_classify_valid e hS θ, fun i j => ?_⟩
  rw [cd_at_profOf k _ _ i.2 j.2, cd_gL_getD e hS θ i, cd_gL_getD e hS θ j,
    cd_dL_getD_gmin e hS θ i, cd_dL_getD_gmin e hS θ j]
  unfold profile
  change e j ∈ θ.cutSet (cd_blk e θ i) ↔ _
  rw [cd_mem_cutSet θ (cd_blk_mem e hS θ i).1 ((hS _).2 ⟨j, rfl⟩)]
  have h1 : (¬ ((cd_gmin e hS θ j : ℕ) = cd_gmin e hS θ i)) ↔ e j ∉ cd_blk e θ i := by
    rw [← Fin.ext_iff, cd_gmin_eq_iff, cd_mem_blk e hS θ i j]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, cd_code_ne_one', cd_code_ne_zero']
  rw [h1]
  rfl

end Classify

section Realize

variable {k : ℕ} {S : Finset (Fin N)} (e : Fin k ↪ Fin N) (g δ : List ℕ)

/-- The block with representative `r`. -/
def cd_B (r : ℕ) : Finset (Fin N) := (univ.filter fun j : Fin k => g.getD j 0 = r).map e

lemma cd_mem_B (r : ℕ) (j : Fin k) : e j ∈ cd_B e g r ↔ g.getD j 0 = r := by
  simp [cd_B]

lemma cd_B_elim {r : ℕ} {x : Fin N} (hx : x ∈ cd_B e g r) : ∃ j, e j = x ∧ g.getD j 0 = r := by
  simp only [cd_B, mem_map, mem_filter, mem_univ, true_and] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  exact ⟨j, rfl, hj⟩

open Classical in
/-- The partition realizing an admissible pair. -/
noncomputable def cd_theta (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) (hv : cd_valid k g δ = true) :
    SysPartition N S where
  parts := (univ.filter fun i : Fin k => g.getD i 0 = i).image fun i : Fin k => cd_B e g (i : ℕ)
  dir := fun p => if h : ∃ i : Fin k, e i ∈ p then cd_decode (δ.getD (g.getD ((Classical.choose h : Fin k) : ℕ) 0) 0)
    else Dir.inputs
  parts_nonempty := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hp
    exact ⟨e i, (cd_mem_B e g _ _).2 (mem_filter.1 hi).2⟩
  parts_subset := by
    intro p hp x hx
    obtain ⟨i, _, rfl⟩ := mem_image.1 hp
    obtain ⟨j, rfl, _⟩ := cd_B_elim e g hx
    exact (hS _).2 ⟨j, rfl⟩
  parts_disjoint := by
    intro p hp q hq hpq
    obtain ⟨i, _, rfl⟩ := mem_image.1 hp
    obtain ⟨i', _, rfl⟩ := mem_image.1 hq
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨j, rfl, hj⟩ := cd_B_elim e g hx
    have hj' := (cd_mem_B e g _ _).1 hx'
    exact hpq (by rw [← hj, hj'])
  parts_cover := by
    intro x hx
    obtain ⟨j, rfl⟩ := (hS x).1 hx
    obtain ⟨_, _, hv3, _⟩ := (cd_valid_iff k g δ).1 hv
    have h1 := hv3 j j.2
    refine ⟨cd_B e g (g.getD j 0), mem_image.2 ⟨⟨g.getD j 0, lt_of_le_of_lt h1.1 j.2⟩,
      mem_filter.2 ⟨mem_univ _, h1.2.1⟩, rfl⟩, (cd_mem_B e g _ _).2 rfl⟩
  two_le := by
    obtain ⟨_, _, hv3, ⟨i, hi, hgi⟩⟩ := (cd_valid_iff k g δ).1 hv
    have hk : 0 < k := by omega
    have h0 : g.getD 0 0 = 0 := by have := (hv3 0 hk).1; omega
    have hgi' := hv3 i hi
    have hA : cd_B e g 0 ∈ (univ.filter fun i : Fin k => g.getD i 0 = i).image
        fun i : Fin k => cd_B e g (i : ℕ) :=
      mem_image.2 ⟨⟨0, hk⟩, mem_filter.2 ⟨mem_univ _, h0⟩, rfl⟩
    have hB : cd_B e g (g.getD i 0) ∈ (univ.filter fun i : Fin k => g.getD i 0 = i).image
        fun i : Fin k => cd_B e g (i : ℕ) :=
      mem_image.2 ⟨⟨g.getD i 0, lt_of_le_of_lt hgi'.1 hi⟩, mem_filter.2 ⟨mem_univ _, hgi'.2.1⟩, rfl⟩
    have hAB : cd_B e g 0 ≠ cd_B e g (g.getD i 0) := by
      intro h
      have : e ⟨0, hk⟩ ∈ cd_B e g 0 := (cd_mem_B e g _ _).2 h0
      rw [h, cd_mem_B] at this
      exact hgi (by rw [← this]; exact h0)
    have := card_le_card (show ({cd_B e g 0, cd_B e g (g.getD i 0)} : Finset (Finset (Fin N)))
      ⊆ _ from insert_subset hA (singleton_subset_iff.2 hB))
    rw [card_pair hAB] at this
    exact this

lemma cd_theta_partOf (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) (hv : cd_valid k g δ = true) (i : Fin k) :
    (cd_theta e g δ hS hv).partOf (e i) = cd_B e g (g.getD i 0) := by
  obtain ⟨_, _, hv3, _⟩ := (cd_valid_iff k g δ).1 hv
  have h1 := hv3 i i.2
  refine SysPartition.partOf_eq _ ?_ ((cd_mem_B e g _ _).2 rfl)
  exact mem_image.2 ⟨⟨g.getD i 0, lt_of_le_of_lt h1.1 i.2⟩, mem_filter.2 ⟨mem_univ _, h1.2.1⟩, rfl⟩

lemma cd_theta_dir (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) (hv : cd_valid k g δ = true) (i : Fin k) :
    (cd_theta e g δ hS hv).dir (cd_B e g (g.getD i 0)) = cd_decode (δ.getD (g.getD i 0) 0) := by
  have h : ∃ j : Fin k, e j ∈ cd_B e g (g.getD i 0) := ⟨i, (cd_mem_B e g _ _).2 rfl⟩
  change (if h : ∃ j : Fin k, e j ∈ cd_B e g (g.getD i 0) then
      cd_decode (δ.getD (g.getD ((Classical.choose h : Fin k) : ℕ) 0) 0) else Dir.inputs) = _
  rw [dite_eq_left h, (cd_mem_B e g _ _).1 (Classical.choose_spec h)]

/-- **Realization.** Every admissible pair is the pulled-back profile of some partition. -/
theorem cd_realize (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x) (hv : cd_valid k g δ = true) :
    ∃ θ : SysPartition N S, ∀ i j : Fin k,
      (e j ∈ profile θ (e i) ↔ cd_at (cd_profOf k g δ) i j = true) := by
  refine ⟨cd_theta e g δ hS hv, fun i j => ?_⟩
  set θ := cd_theta e g δ hS hv
  have hp : θ.partOf (e i) ∈ θ.parts := (prof_partOf_mem θ ((hS _).2 ⟨i, rfl⟩)).1
  unfold profile
  rw [cd_mem_cutSet θ hp ((hS _).2 ⟨j, rfl⟩), cd_theta_partOf e g δ hS hv i,
    cd_theta_partOf e g δ hS hv j, cd_theta_dir e g δ hS hv i, cd_theta_dir e g δ hS hv j,
    cd_mem_B, cd_decode_ne_out, cd_decode_ne_in, cd_at_profOf k _ _ i.2 j.2]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true]

end Realize

/-! ### Orbit reduction -/

section Orbit

variable (k : ℕ)

/-- A unit permutation given as a list, with a check that it is one. -/
def cd_permOK (σ : List ℕ) : Bool :=
  (σ.length == k) && (List.range k).all (fun i => decide (σ.getD i 0 < k)) &&
  (List.range k).all fun i => (List.range k).all fun j => (i == j) || (σ.getD i 0 != σ.getD j 0)

/-- `C` is the relabelling of `C'` by `σ`: `C i j = C' (σ i) (σ j)`. -/
def cd_relab (σ : List ℕ) (C C' : List (List Bool)) : Bool :=
  (List.range k).all fun i => (List.range k).all fun j =>
    cd_at C i j == cd_at C' (σ.getD i 0) (σ.getD j 0)

/-- The orbit check: the `n`-th admissible pair has the witness `(σ, r)`, and its profile is the
relabelling by `σ` of the `r`-th representative. -/
def cd_orbitCheck (reps : List (List (List Bool))) (W : List (List ℕ × ℕ)) : Bool :=
  ((cd_gen k).length == W.length) &&
  ((cd_gen k).zip W).all fun x =>
    cd_permOK k x.2.1 && decide (x.2.2 < reps.length) &&
      cd_relab k x.2.1 (reps.getD x.2.2 []) (cd_profOf k x.1.1 x.1.2)

/-- The permutation of `Fin k` given by a checked list. -/
def cd_permF (σ : List ℕ) (hk : 0 < k) : Fin k → Fin k := fun i => ⟨σ.getD i 0 % k, Nat.mod_lt _ hk⟩

lemma cd_permF_val {σ : List ℕ} (h : cd_permOK k σ = true) (hk : 0 < k) (i : Fin k) :
    (cd_permF k σ hk i : ℕ) = σ.getD i 0 := by
  simp only [cd_permOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact Nat.mod_eq_of_lt (h.1.2 i i.2)

lemma cd_permF_inj {σ : List ℕ} (h : cd_permOK k σ = true) (hk : 0 < k) :
    Function.Injective (cd_permF k σ hk) := by
  intro i j hij
  have h' := h
  simp only [cd_permOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq] at h'
  have hv := congrArg Fin.val hij
  rw [cd_permF_val k h hk, cd_permF_val k h hk] at hv
  rcases h'.2 i i.2 j j.2 with h1 | h1
  · exact Fin.ext h1
  · exact absurd hv h1

/-- **Soundness of the orbit check.** Every admissible profile is a relabelling of a
representative. -/
theorem cd_orbit_sound (reps : List (List (List Bool))) (W : List (List ℕ × ℕ))
    (hc : cd_orbitCheck k reps W = true) (g δ : List ℕ) (hv : cd_valid k g δ = true) :
    ∃ σ : Equiv.Perm (Fin k), ∃ C ∈ reps, ∀ i j : Fin k,
      cd_at C i j = cd_at (cd_profOf k g δ) (σ i) (σ j) := by
  simp only [cd_orbitCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨hlen, hall⟩ := hc
  obtain ⟨n, hn, hgn⟩ := List.getElem_of_mem (cd_mem_gen hv)
  have hmem : ((cd_gen k)[n], W[n]'(hlen ▸ hn)) ∈ (cd_gen k).zip W := by
    rw [List.mem_iff_getElem]
    exact ⟨n, by simp [hlen ▸ hn, hn], by simp⟩
  have hx := hall _ hmem
  simp only [decide_eq_true_eq] at hx
  obtain ⟨⟨hperm, hr⟩, hrel⟩ := hx
  rw [hgn] at hrel
  have hk : 0 < k := by
    obtain ⟨_, _, _, ⟨i, hi, _⟩⟩ := (cd_valid_iff k g δ).1 hv
    omega
  let σ := Equiv.ofBijective (cd_permF k (W[n]'(hlen ▸ hn)).1 hk)
    ((Finite.injective_iff_bijective).1 (cd_permF_inj k hperm hk))
  have hmemr : reps.getD (W[n]'(hlen ▸ hn)).2 [] ∈ reps := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
    exact List.getElem_mem hr
  refine ⟨σ, reps.getD (W[n]'(hlen ▸ hn)).2 [], hmemr, fun i j => ?_⟩
  simp only [cd_relab, List.all_eq_true, List.mem_range, beq_iff_eq] at hrel
  rw [hrel i i.2 j j.2]
  simp only [σ, Equiv.ofBijective_apply, cd_permF_val k hperm hk]

/-- **Reduction to a representative.** For every partition `θ` of `S` there is an ordering
`e ∘ σ` of `S` along which the pulled-back profile of `θ` is a representative. -/
theorem cd_classify_rep {S : Finset (Fin N)} (e : Fin k ↪ Fin N) (hS : ∀ x, x ∈ S ↔ ∃ i, e i = x)
    (θ : SysPartition N S) (reps : List (List (List Bool))) (W : List (List ℕ × ℕ))
    (hc : cd_orbitCheck k reps W = true) :
    ∃ σ : Equiv.Perm (Fin k), ∃ C ∈ reps, ∀ i j : Fin k,
      (e (σ j) ∈ profile θ (e (σ i)) ↔ cd_at C i j = true) := by
  obtain ⟨g, δ, hv, hp⟩ := cd_classify e hS θ
  obtain ⟨σ, C, hC, hrel⟩ := cd_orbit_sound k reps W hc g δ hv
  exact ⟨σ, C, hC, fun i j => by rw [hp, hrel]⟩

end Orbit

end Census
end IIT
