/-
Census: the cause side of a two-unit candidate system `S = {a, b}`.

With `Z = ∑ᵥ P(v)` the Bayes weight of `[IIT4, Eq 4]` is `bgWeight w = blockW w / Z`, where
`blockW w` sums the row products over the `S`-block of `w`.  Every factor of the cause
probability is then `U i t / Z / 2^|S|`, and a cut unit `a` (whose inputs from `b` are
severed) gets the averaged factor `(U a t + U a (flip t b)) / 2 / Z / 2^|S|`.  Every system
partition of a pair cuts at least one unit, so if both flips strictly lower `U` at a
maximiser of `U a · U b` (= the maximal cause state), `φ_c > 0` at every partition.
-/
import IIT.Census.UnivDet

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- Weight of the `S`-block of `w`: the row products summed over states agreeing with `w`
off `S`. -/
noncomputable def blockW (z : Param N) (s : State N) (S : Finset (Fin N)) (w : State N) : ℝ :=
  ∑ v ∈ agree Sᶜ w, rowProd z s v

/-- Unnormalised cause factor of unit `i` at prior system state `t`. -/
noncomputable def U (z : Param N) (s : State N) (S : Finset (Fin N)) (i : Fin N) (t : State N) :
    ℝ :=
  ∑ w : State N, y z s (merge S t w) i * blockW z s S w

/-- Flip bit `k` of `t`. -/
def flip (t : State N) (k : Fin N) : State N := Function.update t k (!t k)

/-! ### Flips and the single-hole fibre -/

lemma flip_ne (t : State N) (k : Fin N) : t ≠ flip t k := by
  intro h
  have := congrFun h k
  cases hk : t k <;> simp [flip, hk] at this

lemma flip_merge {S : Finset (Fin N)} {k : Fin N} (hk : k ∈ S) (t w : State N) :
    flip (merge S t w) k = merge S (flip t k) w := by
  funext j
  by_cases hj : j = k
  · subst hj; simp [flip, hk]
  · by_cases hjS : j ∈ S
    · simp [flip, Function.update_of_ne hj, hjS]
    · simp [flip, Function.update_of_ne hj, hjS]

lemma mem_agree_compl_single {m v : State N} {k : Fin N} :
    v ∈ agree ({k}ᶜ) m ↔ v = m ∨ v = flip m k := by
  rw [mem_agree]
  constructor
  · intro h
    by_cases hk : v k = m k
    · left; funext j
      by_cases hj : j = k
      · subst hj; exact hk
      · exact h j (by simpa using hj)
    · right; funext j
      by_cases hj : j = k
      · subst hj
        simp only [flip, Function.update_self]
        cases h1 : v j <;> cases h2 : m j <;> simp_all
      · rw [flip, Function.update_of_ne hj]; exact h j (by simpa using hj)
  · rintro (rfl | rfl) j hj
    · rfl
    · have : j ≠ k := by simpa using hj
      simp [flip, Function.update_of_ne this]

lemma agree_compl_single (m : State N) (k : Fin N) :
    agree ({k}ᶜ) m = {m, flip m k} := by
  ext v; rw [mem_agree_compl_single]; simp

lemma effUnit_compl_single (T : UnitTPM N) (m : State N) (k i : Fin N) (x : Bool) :
    effUnit T ({k}ᶜ) m i x = (T.prob i m x + T.prob i (flip m k) x) / 2 := by
  rw [effUnit, agree_compl_single, sum_pair (flip_ne m k), card_pair (flip_ne m k)]
  norm_num

/-! ### The Bayes weight as a block weight -/

lemma sum_merge_eq (S : Finset (Fin N)) (w : State N) (f : State N → ℝ) :
    ∑ sv : State N, f (merge S sv w) = (2 : ℝ) ^ (N - S.card) * ∑ v ∈ agree Sᶜ w, f v := by
  have hmaps : ∀ sv ∈ (univ : Finset (State N)), merge S sv w ∈ agree Sᶜ w := fun sv _ =>
    mem_agree.2 fun j hj => merge_not_mem (mem_compl.1 hj)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hfib : univ.filter (fun sv : State N => merge S sv w = v) = agree S v := by
    ext sv
    simp only [mem_filter, mem_univ, true_and, mem_agree]
    constructor
    · rintro rfl j hj; simp [hj]
    · intro h; funext j
      by_cases hj : j ∈ S
      · simp [hj, h j hj]
      · rw [merge_not_mem hj]; exact ((mem_agree.1 hv) j (mem_compl.2 hj)).symm
  rw [Finset.sum_congr rfl fun sv hsv => by rw [(mem_filter.1 hsv).2], sum_const, hfib,
    card_agree, nsmul_eq_mul]
  push_cast; ring

lemma bgWeight_eq (z : Param N) (s : State N) (S : Finset (Fin N)) (w : State N) :
    bgWeight (tpmOf z) S s w = blockW z s S w / ∑ v : State N, fullProb (tpmOf z) v s := by
  rw [bgWeight, sum_merge_eq S w (fun v => fullProb (tpmOf z) v s),
    mul_div_cancel_left₀ _ (by positivity)]
  rfl

lemma sum_mul_bgWeight (z : Param N) (s : State N) (S : Finset (Fin N)) (g : State N → ℝ) :
    ∑ w : State N, g w * bgWeight (tpmOf z) S s w =
      (∑ w : State N, g w * blockW z s S w) / ∑ v : State N, fullProb (tpmOf z) v s := by
  simp only [bgWeight_eq, Finset.sum_div, mul_div_assoc]

/-! ### Positivity -/

lemma blockW_pos {z : Param N} (hz : z ∈ openCube N) (s : State N) (S : Finset (Fin N))
    (w : State N) : 0 < blockW z s S w :=
  Finset.sum_pos (fun v _ => rowProd_pos hz s v) (agree_nonempty _ _)

lemma U_pos {z : Param N} (hz : z ∈ openCube N) (s : State N) (S : Finset (Fin N)) (i : Fin N)
    (t : State N) : 0 < U z s S i t :=
  Finset.sum_pos (fun w _ => mul_pos (y_pos hz s _ i) (blockW_pos hz s S w)) univ_nonempty

/-! ### Factors of the cause probability -/

lemma sysCauseProb_eq (z : Param N) (s t : State N) (S : Finset (Fin N)) :
    sysCauseProb (tpmOf z) S s s t =
      ∏ i ∈ S, (U z s S i t / (∑ v : State N, fullProb (tpmOf z) v s) / (2 : ℝ) ^ S.card) := by
  unfold sysCauseProb
  refine prod_congr rfl fun i _ => ?_
  rw [sum_mul_bgWeight]
  rfl

lemma partFactor_univ (z : Param N) (s t : State N) (S : Finset (Fin N)) (j : Fin N) :
    (∑ w : State N, effUnit (tpmOf z) univ (merge S t w) j (s j) * bgWeight (tpmOf z) S s w)
        / (2 : ℝ) ^ S.card =
      U z s S j t / (∑ v : State N, fullProb (tpmOf z) v s) / (2 : ℝ) ^ S.card := by
  simp only [effUnit_univ_prob]
  rw [sum_mul_bgWeight]
  rfl

lemma partFactor_single (z : Param N) (s t : State N) (S : Finset (Fin N)) (j k : Fin N)
    (hk : k ∈ S) :
    (∑ w : State N, effUnit (tpmOf z) ({k}ᶜ) (merge S t w) j (s j) * bgWeight (tpmOf z) S s w)
        / (2 : ℝ) ^ S.card =
      (U z s S j t + U z s S j (flip t k)) / 2 / (∑ v : State N, fullProb (tpmOf z) v s)
        / (2 : ℝ) ^ S.card := by
  simp only [effUnit_compl_single, flip_merge hk]
  have h : ∀ w : State N,
      ((tpmOf z).prob j (merge S t w) (s j) + (tpmOf z).prob j (merge S (flip t k) w) (s j)) / 2
        * bgWeight (tpmOf z) S s w =
      ((tpmOf z).prob j (merge S t w) (s j) * bgWeight (tpmOf z) S s w
        + (tpmOf z).prob j (merge S (flip t k) w) (s j) * bgWeight (tpmOf z) S s w) / 2 := by
    intro w; ring
  rw [Finset.sum_congr rfl fun w _ => h w, ← Finset.sum_div, Finset.sum_add_distrib,
    sum_mul_bgWeight, sum_mul_bgWeight]
  simp only [U, y]
  ring

/-! ### Cut sets of a partition -/

lemma cutSet_partOf_subset {S : Finset (Fin N)} (θ : SysPartition N S) {j : Fin N}
    (hj : j ∈ S) : θ.cutSet (θ.partOf j) ⊆ S.erase j := by
  obtain ⟨p, hp, hjp⟩ := θ.parts_cover j hj
  rw [θ.partOf_eq hp hjp]
  intro x hx
  unfold SysPartition.cutSet at hx
  cases hd : θ.dir p with
  | inputs =>
      rw [hd] at hx
      obtain ⟨hxS, hxp⟩ := mem_sdiff.1 hx
      exact mem_erase.2 ⟨fun h => hxp (h ▸ hjp), hxS⟩
  | both =>
      rw [hd] at hx
      obtain ⟨hxS, hxp⟩ := mem_sdiff.1 hx
      exact mem_erase.2 ⟨fun h => hxp (h ▸ hjp), hxS⟩
  | outputs =>
      rw [hd] at hx
      obtain ⟨q, hq, hxq⟩ := Finset.mem_sup.1 hx
      obtain ⟨hqP, hqp, -⟩ := mem_filter.1 hq
      refine mem_erase.2 ⟨fun h => ?_, θ.parts_subset q hqP hxq⟩
      subst h
      exact Finset.disjoint_left.1 (θ.parts_disjoint q hqP p hp hqp) hxq hjp

lemma cut_cases_pair {a b : Fin N} (θ : SysPartition N {a, b}) {j k : Fin N}
    (hjk : ({a, b} : Finset (Fin N)).erase j ⊆ {k}) (hj : j ∈ ({a, b} : Finset (Fin N))) :
    θ.cutSet (θ.partOf j) = ∅ ∨ θ.cutSet (θ.partOf j) = {k} :=
  Finset.subset_singleton_iff.1 ((cutSet_partOf_subset θ hj).trans hjk)

lemma exists_cut_pair {a b : Fin N} (θ : SysPartition N {a, b}) :
    (θ.cutSet (θ.partOf a)).Nonempty ∨ (θ.cutSet (θ.partOf b)).Nonempty := by
  obtain ⟨p, hp, hne⟩ := θ.exists_cutSet_nonempty
  obtain ⟨j, hj⟩ := θ.parts_nonempty p hp
  have hjS := θ.parts_subset p hp hj
  rw [← θ.partOf_eq hp hj] at hne
  rcases mem_insert.1 hjS with rfl | h
  · exact Or.inl hne
  · rw [mem_singleton.1 h] at hne; exact Or.inr hne

/-! ### One factor of the partitioned cause probability -/

lemma partFactor_bound {z : Param N} (hz : z ∈ openCube N) (s t : State N)
    {S : Finset (Fin N)} (M : Finset (Fin N)) {j k : Fin N} (hk : k ∈ S)
    (hM : M = ∅ ∨ M = {k}) (hlt : U z s S j (flip t k) < U z s S j t) :
    let F := (∑ w : State N, effUnit (tpmOf z) Mᶜ (merge S t w) j (s j)
        * bgWeight (tpmOf z) S s w) / (2 : ℝ) ^ S.card
    let C := U z s S j t / (∑ v : State N, fullProb (tpmOf z) v s) / (2 : ℝ) ^ S.card
    0 < F ∧ F ≤ C ∧ (M.Nonempty → F < C) := by
  intro F C
  have hZ := sum_fullProb_pos hz s
  have h2 : (0 : ℝ) < 2 ^ S.card := by positivity
  have hU1 := U_pos hz s S j t
  have hU2 := U_pos hz s S j (flip t k)
  rcases hM with rfl | rfl
  · have hF : F = C := by simp only [F, C, compl_empty]; exact partFactor_univ z s t S j
    refine ⟨?_, hF.le, fun h => absurd h (by simp)⟩
    rw [hF]; exact div_pos (div_pos hU1 hZ) h2
  · have hF : F = (U z s S j t + U z s S j (flip t k)) / 2 / (∑ v : State N,
        fullProb (tpmOf z) v s) / (2 : ℝ) ^ S.card := partFactor_single z s t S j k hk
    have hlt' : F < C := by
      rw [hF]
      refine div_lt_div_of_pos_right (div_lt_div_of_pos_right ?_ hZ) h2
      linarith
    refine ⟨?_, hlt'.le, fun _ => hlt'⟩
    rw [hF]; exact div_pos (div_pos (div_pos (by linarith) two_pos) hZ) h2

/-! ### The pair: `φ_c > 0` at every partition when both flips hurt -/

lemma sysPartCauseProb_lt_pair {z : Param N} (hz : z ∈ openCube N) (s tc : State N)
    {a b : Fin N} (hab : a ≠ b) (θ : SysPartition N {a, b})
    (ha : U z s {a, b} a (flip tc b) < U z s {a, b} a tc)
    (hb : U z s {a, b} b (flip tc a) < U z s {a, b} b tc) :
    0 < sysPartCauseProb (tpmOf z) {a, b} s θ s tc ∧
      sysPartCauseProb (tpmOf z) {a, b} s θ s tc < sysCauseProb (tpmOf z) {a, b} s s tc := by
  have haS : a ∈ ({a, b} : Finset (Fin N)) := mem_insert_self _ _
  have hbS : b ∈ ({a, b} : Finset (Fin N)) := mem_insert_of_mem (mem_singleton_self _)
  have hea : ({a, b} : Finset (Fin N)).erase a ⊆ {b} := by
    intro x hx; simp only [mem_erase, mem_insert, mem_singleton] at hx ⊢; tauto
  have heb : ({a, b} : Finset (Fin N)).erase b ⊆ {a} := by
    intro x hx; simp only [mem_erase, mem_insert, mem_singleton] at hx ⊢; tauto
  obtain ⟨pa, la, sa⟩ := partFactor_bound hz s tc _ hbS (cut_cases_pair θ hea haS) ha
  obtain ⟨pb, lb, sb⟩ := partFactor_bound hz s tc _ haS (cut_cases_pair θ heb hbS) hb
  unfold sysPartCauseProb
  rw [sysCauseProb_eq, prod_pair hab, prod_pair hab]
  refine ⟨mul_pos pa pb, ?_⟩
  rcases exists_cut_pair θ with hc | hc
  · have := sa hc
    calc _ ≤ _ := mul_le_mul_of_nonneg_left lb pa.le
      _ < _ := mul_lt_mul_of_pos_right this (pb.trans_le lb)
  · have := sb hc
    calc _ < _ := mul_lt_mul_of_pos_left this pa
      _ ≤ _ := mul_le_mul_of_nonneg_right la ((pb.trans this).le)

/-! ### The maximal cause state maximises `U a · U b` -/

lemma sysCauseProb_pair_eq (z : Param N) (s t : State N) {a b : Fin N} (hab : a ≠ b) :
    sysCauseProb (tpmOf z) {a, b} s s t =
      ((∑ v : State N, fullProb (tpmOf z) v s)⁻¹ * ((2 : ℝ) ^ ({a, b} : Finset (Fin N)).card)⁻¹)
        ^ 2 * (U z s {a, b} a t * U z s {a, b} b t) := by
  rw [sysCauseProb_eq, prod_pair hab]
  ring

lemma avg_scale (κ : ℝ) (f : State N → ℝ) :
    avgOverStates (fun r => κ * f r) = κ * avgOverStates f := by
  unfold avgOverStates
  rw [← Finset.mul_sum, mul_div_assoc]

lemma max_of_argmax_iic_scaled (f : State N → ℝ) (hf : ∀ t, 0 < f t) (κ K : ℝ) (hκ : 0 < κ)
    (hK : 0 < K) (t : State N)
    (ht : ∀ t', κ * f t' / (K * avgOverStates (fun r => κ * f r)) *
        Real.logb 2 (κ * f t' / avgOverStates (fun r => κ * f r)) ≤
      κ * f t / (K * avgOverStates (fun r => κ * f r)) *
        Real.logb 2 (κ * f t / avgOverStates (fun r => κ * f r))) :
    ∀ t', f t' ≤ f t := by
  have e1 : ∀ r, κ * f r / (K * avgOverStates (fun r => κ * f r)) =
      f r / (K * avgOverStates f) := by
    intro r
    rw [avg_scale, mul_left_comm, mul_div_mul_left _ _ hκ.ne']
  have e2 : ∀ r, κ * f r / avgOverStates (fun r => κ * f r) = f r / avgOverStates f := by
    intro r
    rw [avg_scale, mul_div_mul_left _ _ hκ.ne']
  refine max_of_argmax_iic f hf K hK t fun t' => ?_
  have := ht t'
  rw [e1, e1, e2, e2] at this
  exact this

lemma U_prod_max_of_mem {z : Param N} (hz : z ∈ openCube N) (s tc : State N) {a b : Fin N}
    (hab : a ≠ b) (htc : tc ∈ sysMaxCauseStates (tpmOf z) {a, b} s s) :
    ∀ t, U z s {a, b} a t * U z s {a, b} b t ≤ U z s {a, b} a tc * U z s {a, b} b tc := by
  have h := mem_argmaxSet.1 htc
  have hZ := sum_fullProb_pos hz s
  set κ := ((∑ v : State N, fullProb (tpmOf z) v s)⁻¹ *
    ((2 : ℝ) ^ ({a, b} : Finset (Fin N)).card)⁻¹) ^ 2 with hκdef
  have hκ : 0 < κ := by positivity
  have hc : ∀ t, sysCauseProb (tpmOf z) {a, b} s s t =
      κ * (U z s {a, b} a t * U z s {a, b} b t) := fun t => sysCauseProb_pair_eq z s t hab
  refine max_of_argmax_iic_scaled (fun t => U z s {a, b} a t * U z s {a, b} b t)
    (fun t => mul_pos (U_pos hz s _ a t) (U_pos hz s _ b t)) κ
    ((2 : ℝ) ^ ({a, b} : Finset (Fin N)).card) hκ (by positivity) tc fun t' => ?_
  have := h t'
  unfold sysIiC sysBackCause sysUncCause at this
  simp only [hc] at this
  exact this

/-! ### Assembly -/

theorem sysPhiC_pair_pos (z : Param N) (hz : z ∈ openCube N) (s : State N) {a b : Fin N}
    (hab : a ≠ b)
    (hU : ∀ tc : State N, (∀ t, U z s {a, b} a t * U z s {a, b} b t ≤
        U z s {a, b} a tc * U z s {a, b} b tc) →
      U z s {a, b} a (flip tc b) < U z s {a, b} a tc ∧
        U z s {a, b} b (flip tc a) < U z s {a, b} b tc) :
    ∀ tc ∈ sysMaxCauseStates (tpmOf z) {a, b} s s, ∀ θ : SysPartition N {a, b},
      0 < sysPhiC (tpmOf z) {a, b} s θ s tc := by
  intro tc htc θ
  obtain ⟨ha, hb⟩ := hU tc (U_prod_max_of_mem hz s tc hab htc)
  obtain ⟨hP, hlt⟩ := sysPartCauseProb_lt_pair hz s tc hab θ ha hb
  have hZ := sum_fullProb_pos hz s
  have hcp : ∀ t, 0 < sysCauseProb (tpmOf z) {a, b} s s t := by
    intro t
    rw [sysCauseProb_pair_eq z s t hab]
    have := U_pos hz s {a, b} a t
    have := U_pos hz s {a, b} b t
    positivity
  have hback : 0 < sysBackCause (tpmOf z) {a, b} s s tc := by
    unfold sysBackCause sysUncCause
    exact div_pos (hcp tc) (mul_pos (by positivity) (avg_pos _ hcp))
  have hlog : 0 < Real.logb 2 (sysCauseProb (tpmOf z) {a, b} s s tc /
      sysPartCauseProb (tpmOf z) {a, b} s θ s tc) :=
    Real.logb_pos one_lt_two ((one_lt_div hP).2 hlt)
  unfold sysPhiC
  exact mul_pos hback (by rw [pos]; exact lt_max_of_lt_right hlog)

end Census
end IIT
