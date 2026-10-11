/-
Census: the deterministic lower bound for a triple (Lemma T1 for `k = 3`).

For distinct `a b c` and `S = {a, b, c}` the partition `θ*` into the singletons `{a}`, `{b}`,
`{c}` with directions outputs, inputs, both has the cut profile `C_a = {c}`, `C_b = {a, c}`,
`C_c = {a, b}` and normaliser `5`.  Write `w = flipP s z`, `t0` for the all-false state and
`D_i(θ) = Num w S S t0 i - Num w S (S \ C_i) t0 i`, `F_θ = (∑_{i ∈ S} D_i(θ)) / σ`.

If every numerator of `S` is within `η` of a level `A`, the all-false pattern beats every other
pattern of `S` in `∑_i Num_i` by `y σ`, every partition with a different profile has
`F_θ / cc(θ) ≥ (1 + δ) F_θ* / 5`, `F_θ* ≥ y`, some tied effect state has every effect side at least
`E0`, and the errors are small, then `φ_s(S) ≥ σ (y - e) / (8 A ln 2)` with
`e = 6 η² / ((A - η) σ)`.  The proof uses the log sandwich
`(X - Y)/X ≤ ln (X/Y) ≤ (X - Y)/Y`, the minimiser lemma and the selectivity bound `1/8`.
-/
import IIT.Census.Profile
import IIT.Census.PairLower

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-! ### Objects -/

/-- The level of a triple, `a_3 = 1/2 + 1/48`. -/
noncomputable def tl_aTrip : ℝ := 1 / 2 + 1 / 48

/-- The all-false state. -/
def tl_t0 : State N := fun _ => false

/-- The state with bits `ta, tb, tc` on `a, b, c` and `false` elsewhere. -/
def tl_pat3 (a b c : Fin N) (ta tb tc : Bool) : State N :=
  fun j => if j = a then ta else if j = b then tb else if j = c then tc else false

/-- The difference `D_i(θ, t) = Num_i(S, t) - Num_i(S \ C_i, t)`. -/
noncomputable def tl_D (w : Param N) {S : Finset (Fin N)} (θ : SysPartition N S) (t : State N)
    (i : Fin N) : ℝ :=
  Num w S S t i - Num w S (S \ profile θ i) t i

/-- The linear form `F_θ(t) = (∑_{i ∈ S} D_i(θ, t)) / σ`. -/
noncomputable def tl_F (w : Param N) {S : Finset (Fin N)} (θ : SysPartition N S) (t : State N)
    (σ : ℝ) : ℝ :=
  (∑ i ∈ S, tl_D w θ t i) / σ

/-- The partition `θ*` of `{a, b, c}`: singletons, `a` cuts its outputs, `b` its inputs, `c` both. -/
noncomputable def tl_thetaStar (a b c : Fin N) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    SysPartition N {a, b, c} where
  parts := {{a}, {b}, {c}}
  dir := fun p => if p = {a} then Dir.outputs else if p = {b} then Dir.inputs else Dir.both
  parts_nonempty := by
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> simp
  parts_subset := by
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> simp
  parts_disjoint := by
    intro p hp q hq hpq
    simp only [mem_insert, mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      simp_all [eq_comm]
  parts_cover := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨{i}, by simp, mem_singleton_self _⟩
    · exact ⟨{i}, by simp, mem_singleton_self _⟩
    · exact ⟨{i}, by simp, mem_singleton_self _⟩
  two_le := by
    have h1 : ({b} : Finset (Fin N)) ≠ {c} := by simpa using hbc
    have h2 : ({a} : Finset (Fin N)) ∉ ({{b}, {c}} : Finset (Finset (Fin N))) := by
      simp [hab, hac]
    rw [card_insert_of_notMem h2, card_pair h1]
    omega

section Star

variable {a b c : Fin N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)

lemma tl_star_partOf {x : Fin N} (hx : x = a ∨ x = b ∨ x = c) :
    (tl_thetaStar a b c hab hac hbc).partOf x = {x} := by
  refine SysPartition.partOf_eq _ ?_ (mem_singleton_self x)
  change {x} ∈ ({{a}, {b}, {c}} : Finset (Finset (Fin N)))
  rcases hx with rfl | rfl | rfl <;> simp

lemma tl_profile_a : profile (tl_thetaStar a b c hab hac hbc) a = {c} := by
  unfold profile
  rw [tl_star_partOf hab hac hbc (Or.inl rfl)]
  unfold SysPartition.cutSet
  have hd : (tl_thetaStar a b c hab hac hbc).dir {a} = Dir.outputs := by
    simp [tl_thetaStar]
  rw [hd]
  have hparts : (tl_thetaStar a b c hab hac hbc).parts = {{a}, {b}, {c}} := rfl
  have hdir : ∀ q, (tl_thetaStar a b c hab hac hbc).dir q =
      if q = {a} then Dir.outputs else if q = {b} then Dir.inputs else Dir.both := fun _ => rfl
  have hf : ((tl_thetaStar a b c hab hac hbc).parts.filter fun q => q ≠ {a} ∧
      ((tl_thetaStar a b c hab hac hbc).dir q = Dir.outputs ∨
        (tl_thetaStar a b c hab hac hbc).dir q = Dir.both)) = {{c}} := by
    ext q
    rw [mem_filter, hparts, hdir, mem_singleton]
    simp only [mem_insert, mem_singleton]
    constructor
    · rintro ⟨h | h | h, h1, h2⟩
      · exact absurd h h1
      · subst h; simp [hab.symm] at h2
      · exact h
    · rintro rfl
      refine ⟨Or.inr (Or.inr rfl), by simpa using hac.symm, Or.inr ?_⟩
      simp [hac.symm, hbc.symm]
  rw [hf, sup_singleton, id]

lemma tl_profile_b : profile (tl_thetaStar a b c hab hac hbc) b = {a, c} := by
  unfold profile
  rw [tl_star_partOf hab hac hbc (Or.inr (Or.inl rfl))]
  unfold SysPartition.cutSet
  have hd : (tl_thetaStar a b c hab hac hbc).dir {b} = Dir.inputs := by
    simp [tl_thetaStar, hab.symm]
  rw [hd]
  ext x
  simp only [mem_sdiff, mem_insert, mem_singleton]
  constructor
  · rintro ⟨h | h | h, h1⟩
    · exact Or.inl h
    · exact absurd h h1
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, hab⟩
    · exact ⟨Or.inr (Or.inr rfl), hbc.symm⟩

lemma tl_profile_c : profile (tl_thetaStar a b c hab hac hbc) c = {a, b} := by
  unfold profile
  rw [tl_star_partOf hab hac hbc (Or.inr (Or.inr rfl))]
  unfold SysPartition.cutSet
  have hd : (tl_thetaStar a b c hab hac hbc).dir {c} = Dir.both := by
    simp [tl_thetaStar, hac.symm, hbc.symm]
  rw [hd]
  ext x
  simp only [mem_sdiff, mem_insert, mem_singleton]
  constructor
  · rintro ⟨h | h | h, h1⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h h1
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, hac⟩
    · exact ⟨Or.inr (Or.inl rfl), hbc⟩

/-- The normaliser of `θ*` is `5`. -/
lemma tl_cc_star : sysCutCount (tl_thetaStar a b c hab hac hbc) = 5 := by
  rw [sysCutCount_eq_sum_profile, sum_insert (by simp [hab, hac]), sum_pair hbc,
    tl_profile_a, tl_profile_b, tl_profile_c, card_singleton, card_pair hac, card_pair hab]
  norm_num

end Star

/-! ### Triples -/

lemma tl_card3 {a b c : Fin N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset (Fin N)).card = 3 := by
  rw [card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]

lemma tl_sum3 {a b c : Fin N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Fin N → ℝ) :
    ∑ i ∈ ({a, b, c} : Finset (Fin N)), f i = f a + f b + f c := by
  rw [sum_insert (by simp [hab, hac]), sum_pair hbc]; ring

lemma tl_prod3 {a b c : Fin N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Fin N → ℝ) :
    ∏ i ∈ ({a, b, c} : Finset (Fin N)), f i = f a * f b * f c := by
  rw [prod_insert (by simp [hab, hac]), prod_pair hbc]; ring

lemma tl_pat3_eq_t0 (a b c : Fin N) : tl_pat3 a b c false false false = (tl_t0 : State N) := by
  funext j; simp [tl_pat3, tl_t0]

/-! ### Real inequalities -/

/-- A product gap from a sum gap, for numbers within `η` of `A`. -/
lemma tl_prod_gap {A η m x1 x2 x3 y1 y2 y3 : ℝ} (hη : 0 ≤ η) (hηA : η < A)
    (hx1 : |x1 - A| ≤ η) (hx2 : |x2 - A| ≤ η) (hx3 : |x3 - A| ≤ η)
    (hy1 : |y1 - A| ≤ η) (hy2 : |y2 - A| ≤ η) (hy3 : |y3 - A| ≤ η)
    (hm : y1 + y2 + y3 + m ≤ x1 + x2 + x3) (hsm : 24 * A * η ^ 2 < (A - η) ^ 2 * m) :
    y1 * y2 * y3 < x1 * x2 * x3 := by
  rw [abs_le] at hx1 hx2 hx3 hy1 hy2 hy3
  set L := (A - η) * (A - η)
  set U := (A + η) * (A + η)
  have hL0 : 0 ≤ A - η := by linarith
  have hb : ∀ p q : ℝ, |p - A| ≤ η → |q - A| ≤ η → L ≤ p * q ∧ p * q ≤ U := by
    intro p q hp hq
    rw [abs_le] at hp hq
    exact ⟨mul_le_mul (by linarith) (by linarith) hL0 (by linarith),
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)⟩
  have term : ∀ d cc : ℝ, -(2 * η) ≤ d → d ≤ 2 * η → L ≤ cc → cc ≤ U →
      d * L - 2 * η * (U - L) ≤ d * cc := by
    intro d cc h1 h2 h3 h4
    nlinarith [mul_nonneg (by linarith : 0 ≤ d + 2 * η) (by linarith : 0 ≤ cc - L),
      mul_nonneg hη (by linarith : 0 ≤ U - cc)]
  obtain ⟨c1l, c1u⟩ := hb x2 x3 (abs_le.2 hx2) (abs_le.2 hx3)
  obtain ⟨c2l, c2u⟩ := hb y1 x3 (abs_le.2 hy1) (abs_le.2 hx3)
  obtain ⟨c3l, c3u⟩ := hb y1 y2 (abs_le.2 hy1) (abs_le.2 hy2)
  have t1 := term (x1 - y1) (x2 * x3) (by linarith) (by linarith) c1l c1u
  have t2 := term (x2 - y2) (y1 * x3) (by linarith) (by linarith) c2l c2u
  have t3 := term (x3 - y3) (y1 * y2) (by linarith) (by linarith) c3l c3u
  have hid : x1 * x2 * x3 - y1 * y2 * y3 =
      (x1 - y1) * (x2 * x3) + (x2 - y2) * (y1 * x3) + (x3 - y3) * (y1 * y2) := by ring
  have hUL : U - L = 4 * A * η := by simp only [U, L]; ring
  have hLm : L * m = (A - η) ^ 2 * m := by simp only [L]; ring
  have hs : (x1 - y1) * L + (x2 - y2) * L + (x3 - y3) * L ≥ m * L := by
    have : 0 ≤ L := mul_nonneg hL0 hL0
    nlinarith
  nlinarith

/-- `|D/Z - D/A| ≤ 2η²/(A(A-η))` when `|Z - A| ≤ η` and `|D| ≤ 2η`. -/
lemma tl_frac_near {A η Z D : ℝ} (hη : 0 ≤ η) (hηA : η < A) (hZ : |Z - A| ≤ η)
    (hD : |D| ≤ 2 * η) : |D / Z - D / A| ≤ 2 * η ^ 2 / (A * (A - η)) := by
  have hA : 0 < A := by linarith
  have hZl : A - η ≤ Z := by rw [abs_le] at hZ; linarith
  have hZ0 : 0 < Z := by linarith
  have hAη : 0 < A - η := by linarith
  rw [show D / Z - D / A = D * (A - Z) / (Z * A) by field_simp, abs_div, abs_mul,
    abs_of_pos (mul_pos hZ0 hA), div_le_div_iff₀ (mul_pos hZ0 hA) (mul_pos hA hAη)]
  have h1 : |D| * |A - Z| ≤ 2 * η * η :=
    mul_le_mul hD (by rw [abs_sub_comm]; exact hZ) (abs_nonneg _) (by linarith)
  have h2 : 0 ≤ |D| * |A - Z| := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 (mul_pos hA hAη).le,
    mul_le_mul_of_nonneg_left hZl (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (sq_nonneg η)) hA.le)]

/-- **Log sandwich.** For `X, Y` within `η` of `A`, `ln (X/Y)` is within `2η²/(A(A-η))` of
`(X - Y)/A`. -/
lemma tl_log_near {A η X Y : ℝ} (hη : 0 ≤ η) (hηA : η < A) (hX : |X - A| ≤ η)
    (hY : |Y - A| ≤ η) : |Real.log (X / Y) - (X - Y) / A| ≤ 2 * η ^ 2 / (A * (A - η)) := by
  have hXl : A - η ≤ X := by rw [abs_le] at hX; linarith
  have hYl : A - η ≤ Y := by rw [abs_le] at hY; linarith
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hD : |X - Y| ≤ 2 * η := by
    calc |X - Y| = |(X - A) - (Y - A)| := by ring_nf
      _ ≤ |X - A| + |Y - A| := abs_sub _ _
      _ ≤ 2 * η := by linarith
  have e1 := tl_frac_near hη hηA hX hD
  have e2 := tl_frac_near hη hηA hY hD
  have l1 : (X - Y) / X ≤ Real.log (X / Y) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hY0 hX0)
    rw [Real.log_div hY0.ne' hX0.ne'] at h
    rw [Real.log_div hX0.ne' hY0.ne']
    have : Y / X - 1 = -((X - Y) / X) := by field_simp; ring
    linarith
  have l2 : Real.log (X / Y) ≤ (X - Y) / Y := by
    have h := Real.log_le_sub_one_of_pos (div_pos hX0 hY0)
    have : X / Y - 1 = (X - Y) / Y := by field_simp
    linarith
  rw [abs_le] at e1 e2 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

/-! ### The cause side at a state agreeing with `t0` on `S` -/

section Cause

variable {z : Param N} (s : State N) {S : Finset (Fin N)}

/-- The log-ratio sum `G_θ = ∑_{i ∈ S} ln (Num_i(S, t0) / Num_i(S \ C_i, t0))`. -/
noncomputable def tl_G (w : Param N) (θ : SysPartition N S) : ℝ :=
  ∑ i ∈ S, Real.log (Num w S S tl_t0 i / Num w S (S \ profile θ i) tl_t0 i)

lemma tl_logb_eq (hz : z ∈ openCube N) {tc : State N} (htc : ∀ j ∈ S, tc j = false)
    (θ : SysPartition N S) :
    Real.logb 2 (sysCauseProb (tpmOf z) S s s tc / sysPartCauseProb (tpmOf z) S s θ s tc) =
      tl_G (flipP s z) θ / Real.log 2 := by
  have hZ := Zs_pos hz s
  have hc : ∀ Y ⊆ S, ∀ i, Num (flipP s z) S Y tc i = Num (flipP s z) S Y tl_t0 i :=
    fun Y hY i => Num_congr (fun j hj => by rw [htc j (hY hj)]; rfl) _ i
  rw [sysCauseProb_eq_Num, sysPartCauseProb_eq_profile, ← prod_div_distrib]
  have hq : ∀ i ∈ S, Num (flipP s z) S S tc i / Zs (flipP s z) /
      (Num (flipP s z) S (S \ profile θ i) tc i / Zs (flipP s z)) =
      Num (flipP s z) S S tl_t0 i / Num (flipP s z) S (S \ profile θ i) tl_t0 i := by
    intro i _
    rw [hc S (subset_refl _), hc _ sdiff_subset]
    have := Num_pos hz s S (S \ profile θ i) tl_t0 i
    field_simp
  rw [prod_congr rfl hq, Real.logb, Real.log_prod]
  · rfl
  · intro i _
    exact (div_pos (Num_pos hz s S S tl_t0 i) (Num_pos hz s S _ tl_t0 i)).ne'

/-- `G_θ` is within `|S| · 2η²/(A(A-η))` of `(∑_{i ∈ S} D_i(θ, t0)) / A`. -/
lemma tl_G_near {A η : ℝ} (hη : 0 ≤ η) (hηA : η < A) (w : Param N)
    (hlev : ∀ Y ⊆ S, ∀ i ∈ S, |Num w S Y tl_t0 i - A| ≤ η) (θ : SysPartition N S) :
    |tl_G w θ - (∑ i ∈ S, tl_D w θ tl_t0 i) / A| ≤ S.card * (2 * η ^ 2 / (A * (A - η))) := by
  unfold tl_G
  rw [sum_div, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [← nsmul_eq_mul]
  refine sum_le_card_nsmul _ _ _ fun i hi => ?_
  exact tl_log_near hη hηA (hlev S (subset_refl _) i hi) (hlev _ sdiff_subset i hi)

/-- On the band, the selectivity is at most `1` when `3η ≤ A`. -/
lemma tl_backCause_le_one (hz : z ∈ openCube N) {A η : ℝ} (hη : 0 ≤ η) (hηA : 3 * η ≤ A)
    (hlev : ∀ t, ∀ i ∈ S, |Num (flipP s z) S S t i - A| ≤ η) (tc : State N) :
    sysBackCause (tpmOf z) S s s tc ≤ 1 := by
  have hZ := Zs_pos hz s
  set κ := ((Zs (flipP s z)) ^ S.card)⁻¹
  have hκ : 0 < κ := by positivity
  have hAη : 0 ≤ A - η := by linarith
  have hlo : ∀ t, κ * (A - η) ^ S.card ≤ sysCauseProb (tpmOf z) S s s t := by
    intro t
    rw [prof_sysCauseProb_eq]
    refine mul_le_mul_of_nonneg_left ?_ hκ.le
    rw [← prod_const]
    exact prod_le_prod (fun _ _ => hAη) fun i hi => by
      have := hlev t i hi; rw [abs_le] at this; linarith
  have hhi : sysCauseProb (tpmOf z) S s s tc ≤ κ * (A + η) ^ S.card := by
    rw [prof_sysCauseProb_eq]
    refine mul_le_mul_of_nonneg_left ?_ hκ.le
    rw [← prod_const]
    exact prod_le_prod (fun i _ => (Num_pos hz s S S tc i).le) fun i hi => by
      have := hlev tc i hi; rw [abs_le] at this; linarith
  have hunc : κ * (A - η) ^ S.card ≤ sysUncCause (tpmOf z) S s s := by
    unfold sysUncCause avgOverStates
    rw [le_div_iff₀ (by positivity)]
    calc κ * (A - η) ^ S.card * 2 ^ N = ∑ _t : State N, κ * (A - η) ^ S.card := by
          rw [sum_const, card_state, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := sum_le_sum fun t _ => hlo t
  have hpow : (A + η) ^ S.card ≤ 2 ^ S.card * (A - η) ^ S.card := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hcp : 0 < sysCauseProb (tpmOf z) S s s tc := by
    rw [prof_sysCauseProb_eq]
    exact mul_pos hκ (prod_pos fun i _ => Num_pos hz s S S tc i)
  unfold sysBackCause
  have hden : 0 < (2 : ℝ) ^ S.card * sysUncCause (tpmOf z) S s s := by
    have := avg_pos _ fun t => (show 0 < sysCauseProb (tpmOf z) S s s t by
      rw [prof_sysCauseProb_eq]; exact mul_pos hκ (prod_pos fun i _ => Num_pos hz s S S t i))
    unfold sysUncCause; positivity
  rw [div_le_one hden]
  calc sysCauseProb (tpmOf z) S s s tc ≤ κ * (A + η) ^ S.card := hhi
    _ ≤ κ * (2 ^ S.card * (A - η) ^ S.card) := mul_le_mul_of_nonneg_left hpow hκ.le
    _ = 2 ^ S.card * (κ * (A - η) ^ S.card) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hunc (by positivity)

end Cause

/-! ### The tied cause state -/

/-- **Every tied cause state is all-false on the triple.** -/
lemma tl_tc_false {z : Param N} (hz : z ∈ openCube N) (s : State N) {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {A η m : ℝ} (hη : 0 ≤ η) (hηA : η < A)
    (hlev : ∀ t, ∀ i ∈ ({a, b, c} : Finset (Fin N)),
      |Num (flipP s z) {a, b, c} {a, b, c} t i - A| ≤ η)
    (hmarg : ∀ ta tb tc : Bool, (ta || tb || tc) = true →
      ∑ i ∈ ({a, b, c} : Finset (Fin N)), Num (flipP s z) {a, b, c} {a, b, c}
          (tl_pat3 a b c ta tb tc) i + m ≤
        ∑ i ∈ ({a, b, c} : Finset (Fin N)), Num (flipP s z) {a, b, c} {a, b, c} tl_t0 i)
    (hsm : 24 * A * η ^ 2 < (A - η) ^ 2 * m) {tc : State N}
    (htc : tc ∈ sysMaxCauseStates (tpmOf z) {a, b, c} s s) :
    ∀ j ∈ ({a, b, c} : Finset (Fin N)), tc j = false := by
  set w := flipP s z
  set S : Finset (Fin N) := {a, b, c}
  have haS : a ∈ S := by simp [S]
  have hbS : b ∈ S := by simp [S]
  have hcS : c ∈ S := by simp [S]
  have hall : tc a = false ∧ tc b = false ∧ tc c = false := by
    by_contra hne
    have hor : (tc a || tc b || tc c) = true := by
      cases h1 : tc a <;> cases h2 : tc b <;> cases h3 : tc c <;> simp_all
    have hpat : ∀ i, Num w S S tc i = Num w S S (tl_pat3 a b c (tc a) (tc b) (tc c)) i := by
      intro i
      refine Num_congr (fun j hj => ?_) w i
      simp only [S, mem_insert, mem_singleton] at hj
      rcases hj with rfl | rfl | rfl
      · simp [tl_pat3]
      · simp [tl_pat3, hab.symm]
      · simp [tl_pat3, hac.symm, hbc.symm]
    have hm := hmarg _ _ _ hor
    rw [tl_sum3 hab hac hbc, tl_sum3 hab hac hbc, ← hpat a, ← hpat b, ← hpat c] at hm
    have hmax := prod_Num_max_of_mem hz s tc htc tl_t0
    rw [tl_prod3 hab hac hbc, tl_prod3 hab hac hbc] at hmax
    have := tl_prod_gap hη hηA (hlev _ a haS) (hlev _ b hbS) (hlev _ c hcS)
      (hlev tc a haS) (hlev tc b hbS) (hlev tc c hcS) hm hsm
    linarith
  intro j hj
  simp only [S, mem_insert, mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2

/-! ### Lemma T1 for triples -/

lemma tl_arith {k δ R Ls Lθ Gs Gθ : ℝ} (hk : 1 ≤ k) (hR : 0 ≤ R) (hLs : 0 ≤ Ls)
    (hr : k * (1 + δ) * Ls ≤ 5 * Lθ) (hd : 6 * R < δ * Ls) (hGθ : Lθ - R ≤ Gθ)
    (hGs : Gs ≤ Ls + R) : k * Gs < 5 * Gθ ∧ 0 < Gθ := by
  have h1 : k * (6 * R) < k * (δ * Ls) := mul_lt_mul_of_pos_left hd (by linarith)
  have h2 : k * Gs ≤ k * (Ls + R) := mul_le_mul_of_nonneg_left hGs (by linarith)
  have h3 : R ≤ k * R := by nlinarith
  have h4 : 0 ≤ k * Ls := mul_nonneg (by linarith) hLs
  have e : k * (1 + δ) * Ls = k * Ls + k * (δ * Ls) := by ring
  constructor <;> nlinarith

/-- **Lemma T1 for a triple, general level.**  With `w = flipP s z`, `S = {a, b, c}` and `θ*`
the partition of `tl_thetaStar`: if every numerator of `S` is within `η` of `A` (`3η ≤ A`), the
all-false pattern beats every other pattern of `S` in `∑_i Num_i(S, ·)` by `y σ`, every partition
with a different profile on `S` has `F_θ / cc(θ) ≥ (1 + δ) F_θ* / 5`, `F_θ* ≥ y`, a tied effect
state has every effect side at least `E0 ≥ 6η / ((A - η) ln 2)`, and
`36 η² < δ y σ (A - η)`, `24 A η² < (A - η)² y σ`, then
`φ_s(S) ≥ σ (y - 6η² / ((A - η) σ)) / (8 A ln 2)`. -/
theorem tl_triple_lower_gen {z : Param N} (hz : z ∈ openCube N) (s : State N) {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {A η δ y σ E0 : ℝ}
    (hη : 0 ≤ η) (hηA : 3 * η ≤ A) (hA : 0 < A) (hδ : 0 ≤ δ) (hy : 0 < y) (hσ : 0 < σ)
    (hlev : ∀ Y ⊆ ({a, b, c} : Finset (Fin N)), ∀ t, ∀ i ∈ ({a, b, c} : Finset (Fin N)),
      |Num (flipP s z) {a, b, c} Y t i - A| ≤ η)
    (hreg : ∀ θ : SysPartition N {a, b, c},
      (∃ j ∈ ({a, b, c} : Finset (Fin N)), profile θ j ≠
        profile (tl_thetaStar a b c hab hac hbc) j) →
      (1 + δ) * tl_F (flipP s z) (tl_thetaStar a b c hab hac hbc) tl_t0 σ / 5 ≤
        tl_F (flipP s z) θ tl_t0 σ / (sysCutCount θ : ℝ))
    (hFy : y ≤ tl_F (flipP s z) (tl_thetaStar a b c hab hac hbc) tl_t0 σ)
    (hmarg : ∀ ta tb tc : Bool, (ta || tb || tc) = true →
      ∑ i ∈ ({a, b, c} : Finset (Fin N)), Num (flipP s z) {a, b, c} {a, b, c}
          (tl_pat3 a b c ta tb tc) i + y * σ ≤
        ∑ i ∈ ({a, b, c} : Finset (Fin N)), Num (flipP s z) {a, b, c} {a, b, c} tl_t0 i)
    (hsmall : 36 * η ^ 2 < δ * y * σ * (A - η))
    (hmsmall : 24 * A * η ^ 2 < (A - η) ^ 2 * (y * σ))
    (hE0 : 6 * η / ((A - η) * Real.log 2) ≤ E0)
    (heff : ∃ te ∈ sysMaxEffStates (tpmOf z) {a, b, c} s s,
      ∀ θ : SysPartition N {a, b, c}, E0 ≤ sysPhiE (tpmOf z) {a, b, c} s θ s te) :
    σ * (y - 6 * η ^ 2 / ((A - η) * σ)) / (8 * A * Real.log 2) ≤ phi z s {a, b, c} := by
  set S : Finset (Fin N) := {a, b, c} with hSdef
  set w := flipP s z
  set θs := tl_thetaStar a b c hab hac hbc
  have hηA' : η < A := by
    rcases hη.lt_or_eq with h | h
    · linarith
    · rw [← h]; exact hA
  have hAη : 0 < A - η := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcard : S.card = 3 := tl_card3 hab hac hbc
  obtain ⟨te, hte, hE⟩ := heff
  obtain ⟨tc, htc⟩ := sysMaxCauseStates_nonempty (tpmOf z) S s s
  have htc0 := tl_tc_false hz s hab hac hbc hη hηA' (fun t i hi => hlev S (subset_refl _) t i hi)
    hmarg hmsmall htc
  set R := 3 * (2 * η ^ 2 / (A * (A - η))) with hR
  have hR0 : 0 ≤ R := by positivity
  set P : SysPartition N S → ℝ := fun θ => ∑ i ∈ S, tl_D w θ tl_t0 i with hP
  have hnear : ∀ θ : SysPartition N S, |tl_G w θ - P θ / A| ≤ R := by
    intro θ
    have := tl_G_near hη hηA' w (fun Y hY i hi => hlev Y hY tl_t0 i hi) θ
    rw [hcard] at this
    push_cast at this
    exact this
  have hback := sysBackCause_ge_of_mem hz s tc htc
  rw [hcard] at hback
  have hb0 : 0 < sysBackCause (tpmOf z) S s s tc := lt_of_lt_of_le (by norm_num) hback
  have hb1 := tl_backCause_le_one s hz hη hηA (fun t i hi => hlev S (subset_refl _) t i hi) tc
  have hC : ∀ θ : SysPartition N S, sysPhiC (tpmOf z) S s θ s tc =
      sysBackCause (tpmOf z) S s s tc * pos (tl_G w θ / Real.log 2) := by
    intro θ
    unfold sysPhiC
    rw [tl_logb_eq s hz htc0 θ]
  -- every cause side is at most `E0`
  have hDle : ∀ θ : SysPartition N S, tl_G w θ ≤ 6 * η / (A - η) := by
    intro θ
    have h1 := (abs_le.1 (hnear θ)).2
    have h2 : P θ ≤ 3 * (2 * η) := by
      have hs := sum_le_card_nsmul S (fun i => tl_D w θ tl_t0 i) (2 * η) fun i hi => by
        have hx := hlev S (subset_refl _) tl_t0 i hi
        have hy' := hlev _ (sdiff_subset : S \ profile θ i ⊆ S) tl_t0 i hi
        rw [abs_le] at hx hy'
        unfold tl_D; linarith
      rw [hcard, nsmul_eq_mul] at hs
      simp only [hP]
      push_cast at hs
      linarith
    have h3 : P θ / A ≤ 6 * η / A := by
      rw [div_le_div_iff_of_pos_right hA]; linarith
    have h4 : 6 * η / A + R = 6 * η / (A - η) := by
      rw [hR]; field_simp; ring
    linarith
  have hCle : ∀ θ : SysPartition N S, sysPhiC (tpmOf z) S s θ s tc ≤ E0 := by
    intro θ
    rw [hC θ]
    have hp : pos (tl_G w θ / Real.log 2) ≤ 6 * η / ((A - η) * Real.log 2) := by
      unfold pos
      refine max_le (by positivity) ?_
      rw [← div_div]
      exact div_le_div_of_nonneg_right (hDle θ) hlog2.le
    have h0 : 0 ≤ pos (tl_G w θ / Real.log 2) := pos_nonneg _
    calc _ ≤ 1 * pos (tl_G w θ / Real.log 2) := mul_le_mul_of_nonneg_right hb1 h0
      _ ≤ _ := by rw [one_mul]; exact hp.trans hE0
  have hAt : ∀ θ : SysPartition N S, sysPhiAt (tpmOf z) S s θ s tc te =
      sysPhiC (tpmOf z) S s θ s tc := fun θ =>
    min_eq_left ((hCle θ).trans (hE θ))
  -- the region in terms of `P`
  have hFs : tl_F w θs tl_t0 σ = P θs / σ := rfl
  have hPs : y * σ ≤ P θs := by
    rw [hFs, le_div_iff₀ hσ] at hFy; exact hFy
  have hLs : y * σ / A ≤ P θs / A := div_le_div_of_nonneg_right hPs hA.le
  have hsm' : 6 * R < δ * (y * σ / A) := by
    rw [hR]
    have : 36 * η ^ 2 / (A * (A - η)) < δ * y * σ * (A - η) / (A * (A - η)) :=
      div_lt_div_of_pos_right hsmall (mul_pos hA hAη)
    have e1 : δ * y * σ * (A - η) / (A * (A - η)) = δ * (y * σ / A) := by
      field_simp
    have e2 : 6 * (3 * (2 * η ^ 2 / (A * (A - η)))) = 36 * η ^ 2 / (A * (A - η)) := by ring
    linarith
  have hδL : δ * (y * σ / A) ≤ δ * (P θs / A) := mul_le_mul_of_nonneg_left hLs hδ
  have hLs0 : 0 ≤ P θs / A := le_trans (by positivity) hLs
  have hcc5 : (sysCutCount θs : ℝ) = 5 := by
    rw [tl_cc_star hab hac hbc]; norm_num
  -- the minimiser is `θ*`
  have hstrict : ∀ θ : SysPartition N S, (∃ j ∈ S, profile θ j ≠ profile θs j) →
      sysPhiAt (tpmOf z) S s θs s tc te / (sysCutCount θs : ℝ) <
        sysPhiAt (tpmOf z) S s θ s tc te / (sysCutCount θ : ℝ) := by
    intro θ hθ
    have hk1 : (1 : ℝ) ≤ sysCutCount θ := by exact_mod_cast sysCutCount_pos θ
    set k : ℝ := (sysCutCount θ : ℝ) with hk
    have hk0 : 0 < k := by linarith
    have hr := hreg θ hθ
    have hFθ : tl_F w θ tl_t0 σ = P θ / σ := rfl
    rw [hFs, hFθ, div_div, le_div_iff₀ (mul_pos hσ hk0)] at hr
    -- `k (1 + δ) P* ≤ 5 P_θ`
    have hr' : k * (1 + δ) * (P θs / A) ≤ 5 * (P θ / A) := by
      have : (1 + δ) * (P θs / σ) / 5 * (σ * k) = k * (1 + δ) * P θs / 5 := by
        field_simp
      rw [this] at hr
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 5)] at hr
      have : k * (1 + δ) * (P θs / A) = (k * (1 + δ) * P θs) / A := by ring
      rw [this, show 5 * (P θ / A) = (P θ * 5) / A by ring]
      exact div_le_div_of_nonneg_right hr hA.le
    have hGθ := abs_le.1 (hnear θ)
    have hGs := abs_le.1 (hnear θs)
    -- `5 G_θ > k max(G*, 0)`
    obtain ⟨hkey1, hkey0⟩ := tl_arith (Gs := tl_G w θs) (Gθ := tl_G w θ) hk1 hR0 hLs0 hr'
      (lt_of_lt_of_le hsm' hδL)
      (by linarith [hGθ.1]) (by linarith [hGs.2])
    rw [hAt, hAt, hC, hC, hcc5]
    have hpθ : pos (tl_G w θ / Real.log 2) = tl_G w θ / Real.log 2 :=
      max_eq_right (div_pos hkey0 hlog2).le
    rw [hpθ]
    set bb := sysBackCause (tpmOf z) S s s tc
    rcases le_or_gt (tl_G w θs) 0 with hneg | hposs
    · have : pos (tl_G w θs / Real.log 2) = 0 :=
        max_eq_left (div_nonpos_of_nonpos_of_nonneg hneg hlog2.le)
      rw [this, mul_zero, zero_div]
      exact div_pos (mul_pos hb0 (div_pos hkey0 hlog2)) hk0
    · have : pos (tl_G w θs / Real.log 2) = tl_G w θs / Real.log 2 :=
        max_eq_right (div_pos hposs hlog2).le
      rw [this, div_lt_div_iff₀ (by norm_num) hk0]
      have : bb * (tl_G w θs / Real.log 2) * k = bb / Real.log 2 * (k * tl_G w θs) := by ring
      rw [this]
      have : bb * (tl_G w θ / Real.log 2) * 5 = bb / Real.log 2 * (5 * tl_G w θ) := by ring
      rw [this]
      exact mul_lt_mul_of_pos_left hkey1 (div_pos hb0 hlog2)
  have hval := sysPhiOfState_eq_of_strict (tpmOf z) S s θs s tc te hstrict
  have hle := sysPhiOfState_le_sysPhi (tpmOf z) S s s htc hte
  unfold phi
  refine le_trans ?_ hle
  rw [hval, hAt, hC]
  have hGlow : y * σ / A - R ≤ tl_G w θs := by linarith [(abs_le.1 (hnear θs)).1]
  have hp1 : (y * σ / A - R) / Real.log 2 ≤ pos (tl_G w θs / Real.log 2) :=
    le_max_of_le_right (div_le_div_of_nonneg_right hGlow hlog2.le)
  have hp0 : 0 ≤ pos (tl_G w θs / Real.log 2) := pos_nonneg _
  have htarget : σ * (y - 6 * η ^ 2 / ((A - η) * σ)) / (8 * A * Real.log 2) =
      1 / 8 * ((y * σ / A - R) / Real.log 2) := by
    rw [hR]; field_simp; ring
  rw [htarget]
  calc 1 / 8 * ((y * σ / A - R) / Real.log 2) ≤ 1 / 8 * pos (tl_G w θs / Real.log 2) :=
        mul_le_mul_of_nonneg_left hp1 (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by rw [show (1 : ℝ) / 8 = 1 / 2 ^ 3 by norm_num]; exact hback) hp0

/-- **Lemma T1 for a triple** at the level `a_3 = 1/2 + 1/48` (see `tl_triple_lower_gen`). -/
theorem tl_triple_lower {z : Param N} (hz : z ∈ openCube N) (s : State N) {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {η δ y σ E0 : ℝ}
    (hη : 0 ≤ η) (hηA : 3 * η ≤ tl_aTrip) (hδ : 0 ≤ δ) (hy : 0 < y) (hσ : 0 < σ)
    (hlev : ∀ Y ⊆ ({a, b, c} : Finset (Fin N)), ∀ t, ∀ i ∈ ({a, b, c} : Finset (Fin N)),
      |Num (flipP s z) {a, b, c} Y t i - tl_aTrip| ≤ η)
    (hreg : ∀ θ : SysPartition N {a, b, c},
      (∃ j ∈ ({a, b, c} : Finset (Fin N)), profile θ j ≠
        profile (tl_thetaStar a b c hab hac hbc) j) →
      (1 + δ) * tl_F (flipP s z) (tl_thetaStar a b c hab hac hbc) tl_t0 σ / 5 ≤
        tl_F (flipP s z) θ tl_t0 σ / (sysCutCount θ : ℝ))
    (hFy : y ≤ tl_F (flipP s z) (tl_thetaStar a b c hab hac hbc) tl_t0 σ)
    (hmarg : ∀ ta tb tc : Bool, (ta || tb || tc) = true →
      ∑ i ∈ ({a, b, c} : Finset (Fin N)), Num (flipP s z) {a, b, c} {a, b, c}
          (tl_pat3 a b c ta tb tc) i + y * σ ≤
        ∑ i ∈ ({a, b, c} : Finset (Fin N)), Num (flipP s z) {a, b, c} {a, b, c} tl_t0 i)
    (hsmall : 36 * η ^ 2 < δ * y * σ * (tl_aTrip - η))
    (hmsmall : 24 * tl_aTrip * η ^ 2 < (tl_aTrip - η) ^ 2 * (y * σ))
    (hE0 : 6 * η / ((tl_aTrip - η) * Real.log 2) ≤ E0)
    (heff : ∃ te ∈ sysMaxEffStates (tpmOf z) {a, b, c} s s,
      ∀ θ : SysPartition N {a, b, c}, E0 ≤ sysPhiE (tpmOf z) {a, b, c} s θ s te) :
    σ * (y - 6 * η ^ 2 / ((tl_aTrip - η) * σ)) / (8 * tl_aTrip * Real.log 2) ≤
      phi z s {a, b, c} :=
  tl_triple_lower_gen hz s hab hac hbc hη hηA (by unfold tl_aTrip; norm_num) hδ hy hσ hlev hreg
    hFy hmarg hsmall hmsmall hE0 heff

end Census
end IIT
