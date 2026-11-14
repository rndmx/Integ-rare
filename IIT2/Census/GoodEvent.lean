/-
Census of IIT 2.0: the deterministic event `GoodA` (conclusions of Proposition 5 of the note,
with explicit rational constants) implies `WholeIsMainComplex` (proof of Theorem 6).
Constants: `t = 1/2000` (Hoeffding window), `η = 1/1000` (Chebyshev window for `Z`),
`A0 = 0.2776 < d0`, `B1 = 0.1321 > d1`.
-/
import IIT2.Census.Aligned

namespace IIT2

open Finset Real

variable {N : ℕ}

/-- The good event of Proposition 5, for the threshold `L` separating small and large `m = N - |M|`. -/
def GoodA (q : Fin N → State N → ℝ) (L : ℕ) : Prop :=
  (∀ l c, 0 ≤ q l c ∧ q l c ≤ 1) ∧
  (∀ M : Finset (Fin N), L ≤ N - M.card → ∀ l ∈ M, ∀ x, |2 * aA q M l x - 1| ≤ 1 / 2000) ∧
  (|ZA q Finset.univ - 1| ≤ 1 / 1000 ∧ 2776 / 10000 * (N : ℝ) ≤ YA q Finset.univ) ∧
  (∀ M : Finset (Fin N), M ≠ Finset.univ → M.Nonempty → N - M.card < L →
    |ZA q M - 1| ≤ 1 / 1000 ∧ YA q M ≤ 1321 / 10000 * (N : ℝ) ∧ TA q M ≤ 1321 / 10000 * (N : ℝ))

lemma logb_ratio_t_le : logb 2 (1 + 1 / 2000) - logb 2 (1 - 1 / 2000) ≤ 1 / 500 := by
  rw [← Real.logb_div (by norm_num) (by norm_num)]
  have h2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  unfold logb
  rw [div_le_iff₀ (by linarith)]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 + 1 / 2000) / (1 - 1 / 2000) by norm_num)
  nlinarith

lemma logb_eta_lower : -(1 / 500 : ℝ) ≤ logb 2 (1 - 1 / 1000) := by
  have h2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  unfold logb
  rw [le_div_iff₀ (by linarith)]
  have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 - 1 / 1000 by norm_num)
  norm_num at this ⊢
  nlinarith

lemma logb_eta_upper : logb 2 (1 + 1 / 1000) ≤ 1 / 500 := by
  have h2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  unfold logb
  rw [div_le_iff₀ (by linarith)]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / 1000 by norm_num)
  nlinarith

/-- An average against a probability density of a function bounded by `c`. -/
lemma avg_mul_le_of_le {p g : State N → ℝ} (hp : ∀ x, 0 ≤ p x) (hp1 : avg p = 1) {c : ℝ}
    (hg : ∀ x, 0 < p x → g x ≤ c) : avg (fun x => p x * g x) ≤ c := by
  have : ∀ x, p x * g x ≤ c * p x := fun x => by
    rcases (hp x).lt_or_eq with h | h
    · nlinarith [hg x h]
    · rw [← h]; simp
  calc avg (fun x => p x * g x) ≤ avg (fun x => c * p x) := avg_mono this
    _ = c * avg p := by unfold avg; rw [← Finset.mul_sum, mul_div_assoc]
    _ = c := by rw [hp1, mul_one]

section

variable (sys : UnitTPM N) (x₁ : State N)

lemma avg_post_eq_one (M : Finset (Fin N)) (hZ : 0 < ZA (qOf sys x₁) M) :
    avg (post sys M x₁) = 1 := by
  rw [avg_congr (post_eq_WA sys M x₁), avg_div_const]
  exact div_self hZ.ne'

/-- Large `m`: `log₂ g_M ≤ |M| τ` with `τ = 1/500`. -/
lemma logb_post_le_of_window (M : Finset (Fin N))
    (hw : ∀ l ∈ M, ∀ x, |2 * aA (qOf sys x₁) M l x - 1| ≤ 1 / 2000) (x : State N) :
    0 < ZA (qOf sys x₁) M ∧ logb 2 (post sys M x₁ x) ≤ M.card * (1 / 500) := by
  set q := qOf sys x₁
  have hlo : ∀ y, (1 - 1 / 2000 : ℝ) ^ M.card ≤ WA q M y := fun y => by
    unfold WA
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => by norm_num)
      (fun l hl => by have := abs_le.mp (hw l hl y); linarith)
  have hhi : ∀ y, WA q M y ≤ (1 + 1 / 2000 : ℝ) ^ M.card := fun y => by
    unfold WA
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun l hl => by have := abs_le.mp (hw l hl y); linarith)
      (fun l hl => by have := abs_le.mp (hw l hl y); linarith)
  have hp : (0 : ℝ) < (1 - 1 / 2000) ^ M.card := by positivity
  have hZlo : (1 - 1 / 2000 : ℝ) ^ M.card ≤ ZA q M := by
    unfold ZA; rw [← avg_const (N := N) ((1 - 1 / 2000 : ℝ) ^ M.card)]; exact avg_mono hlo
  have hZpos : 0 < ZA q M := lt_of_lt_of_le hp hZlo
  refine ⟨hZpos, ?_⟩
  rw [post_eq_WA]
  have hW := lt_of_lt_of_le hp (hlo x)
  have hle : WA q M x / ZA q M ≤ (1 + 1 / 2000 : ℝ) ^ M.card / (1 - 1 / 2000) ^ M.card :=
    div_le_div₀ (by positivity) (hhi x) hp hZlo
  calc logb 2 (WA q M x / ZA q M)
      ≤ logb 2 ((1 + 1 / 2000 : ℝ) ^ M.card / (1 - 1 / 2000) ^ M.card) :=
        Real.logb_le_logb_of_le (by norm_num) (div_pos hW hZpos) hle
    _ = M.card * (logb 2 (1 + 1 / 2000) - logb 2 (1 - 1 / 2000)) := by
        rw [Real.logb_div (by positivity) (by positivity), Real.logb_pow, Real.logb_pow]; ring
    _ ≤ M.card * (1 / 500) := mul_le_mul_of_nonneg_left logb_ratio_t_le (by positivity)

lemma ei_le_of_window (M : Finset (Fin N))
    (hw : ∀ l ∈ M, ∀ x, |2 * aA (qOf sys x₁) M l x - 1| ≤ 1 / 2000) :
    ei sys M x₁ ≤ M.card * (1 / 500) := by
  have hZ := (logb_post_le_of_window sys x₁ M hw (fun _ => false)).1
  unfold ei kl pmax
  simp_rw [div_one]
  exact avg_mul_le_of_le (post_nonneg _ _ _) (avg_post_eq_one sys x₁ M hZ)
    (fun x _ => (logb_post_le_of_window sys x₁ M hw x).2)

lemma Dterm_le_of_window (M : Finset (Fin N)) (hZX : 0 < ZA (qOf sys x₁) Finset.univ)
    (hw : ∀ l ∈ M, ∀ x, |2 * aA (qOf sys x₁) M l x - 1| ≤ 1 / 2000) :
    Dterm sys M x₁ ≤ M.card * (1 / 500) :=
  avg_mul_le_of_le (post_nonneg _ _ _) (avg_post_eq_one sys x₁ _ hZX)
    (fun x _ => (logb_post_le_of_window sys x₁ M hw x).2)

/-- `B/Z - log₂ Z' ≤ B/(1-η) + 1/500` on the Chebyshev window. -/
lemma small_bound {Y Z Z' B : ℝ} (hB : 0 ≤ B) (hY : Y ≤ B) (hZ : |Z - 1| ≤ 1 / 1000)
    (hZ' : |Z' - 1| ≤ 1 / 1000) :
    Y / Z - logb 2 Z' ≤ B / (1 - 1 / 1000) + 1 / 500 := by
  have hZl : 1 - 1 / 1000 ≤ Z := by have := abs_le.mp hZ; linarith
  have hZ'l : 1 - 1 / 1000 ≤ Z' := by have := abs_le.mp hZ'; linarith
  have h1 : Y / Z ≤ B / Z := div_le_div_of_nonneg_right hY (by linarith)
  have h2 : B / Z ≤ B / (1 - 1 / 1000) := div_le_div_of_nonneg_left hB (by norm_num) hZl
  have h3 : logb 2 (1 - 1 / 1000) ≤ logb 2 Z' :=
    Real.logb_le_logb_of_le (by norm_num) (by norm_num) hZ'l
  have := logb_eta_lower
  linarith

theorem wholeIsMainComplex_of_goodA (L : ℕ) (hL : 1 ≤ L) (hN : 2 * L < N)
    (hG : GoodA (qOf sys x₁) L) : WholeIsMainComplex sys x₁ := by
  obtain ⟨-, hW, ⟨hZX, hYX⟩, hS⟩ := hG
  set q := qOf sys x₁
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast (show 3 ≤ N by omega)
  have hZXpos : 0 < ZA q Finset.univ := by have := abs_le.mp hZX; linarith
  -- ei(X) lower bound
  have heiX : (2776 / 10010 : ℝ) * N - 1 / 500 ≤ ei sys Finset.univ x₁ := by
    rw [ei_eq_YZ sys Finset.univ x₁ hZXpos]
    have hZu : ZA q Finset.univ ≤ 1 + 1 / 1000 := by have := abs_le.mp hZX; linarith
    have h1 : 2776 / 10000 * (N : ℝ) / (1 + 1 / 1000) ≤ 2776 / 10000 * (N : ℝ) / ZA q Finset.univ :=
      div_le_div_of_nonneg_left (by positivity) hZXpos hZu
    have h2 : 2776 / 10000 * (N : ℝ) / ZA q Finset.univ ≤ YA q Finset.univ / ZA q Finset.univ :=
      div_le_div_of_nonneg_right hYX hZXpos.le
    have h3 : logb 2 (ZA q Finset.univ) ≤ logb 2 (1 + 1 / 1000) :=
      Real.logb_le_logb_of_le (by norm_num) hZXpos hZu
    have h4 := logb_eta_upper
    have e : 2776 / 10000 * (N : ℝ) / (1 + 1 / 1000) = 2776 / 10010 * N := by ring
    linarith
  have eb : 1321 / 10000 * (N : ℝ) / (1 - 1 / 1000) + 1 / 500 = 1321 / 9990 * N + 1 / 500 := by
    ring
  -- small proper sets
  have hsmall_ei : ∀ M : Finset (Fin N), M ≠ Finset.univ → M.Nonempty → N - M.card < L →
      ei sys M x₁ ≤ 1321 / 9990 * N + 1 / 500 := by
    intro M hMu hMne hm
    obtain ⟨hZ, hY, -⟩ := hS M hMu hMne hm
    have hZpos : 0 < ZA q M := by have := abs_le.mp hZ; linarith
    rw [ei_eq_YZ sys M x₁ hZpos, ← eb]
    exact small_bound (by positivity) hY hZ hZ
  have hsmall_D : ∀ M : Finset (Fin N), M ≠ Finset.univ → M.Nonempty → N - M.card < L →
      Dterm sys M x₁ ≤ 1321 / 9990 * N + 1 / 500 := by
    intro M hMu hMne hm
    obtain ⟨hZ, -, hT⟩ := hS M hMu hMne hm
    have hZpos : 0 < ZA q M := by have := abs_le.mp hZ; linarith
    rw [Dterm_eq_TZ sys M x₁ hZXpos hZpos, ← eb]
    exact small_bound (by positivity) hT hZX hZ
  have hcard_le : ∀ M : Finset (Fin N), (M.card : ℝ) ≤ N := fun M => by
    have := Finset.card_le_univ M; simp only [Fintype.card_fin] at this; exact_mod_cast this
  refine wholeIsMainComplex_of_bounds sys x₁
    ((2776 / 10010 - 1321 / 9990 - 1 / 500 : ℝ) * N - 2 / 500) ?_ ?_ ?_ ?_
  · norm_num; linarith
  · norm_num; linarith
  · intro P hP
    have hpart : ∀ M ∈ P.parts, M ≠ Finset.univ ∧ M.Nonempty := by
      intro M hM
      refine ⟨fun hMu => hP ?_, Finset.nonempty_iff_ne_empty.mpr (P.ne_bot hM)⟩
      rw [Finset.card_eq_one]
      refine ⟨M, Finset.eq_singleton_iff_unique_mem.mpr ⟨hM, fun M' hM' => ?_⟩⟩
      by_contra hne
      have hd := P.disjoint hM' hM hne
      rw [hMu] at hd
      exact P.ne_bot hM' (by
        rw [Finset.bot_eq_empty]
        exact Finset.eq_empty_of_forall_notMem fun i hi =>
          Finset.disjoint_left.mp hd hi (Finset.mem_univ i))
    set sm := P.parts.filter (fun M => N - M.card < L)
    have hsm : sm.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro M1 h1 M2 h2
      by_contra hne
      have hM1 := Finset.mem_filter.mp h1
      have hM2 := Finset.mem_filter.mp h2
      have e1 : N - M1.card < L := hM1.2
      have e2 : N - M2.card < L := hM2.2
      have hd := P.disjoint hM1.1 hM2.1 hne
      have hu : (M1 ∪ M2).card = M1.card + M2.card := Finset.card_union_of_disjoint hd
      have hle : (M1 ∪ M2).card ≤ N := by
        have := Finset.card_le_univ (M1 ∪ M2); simpa using this
      have c1 := Finset.card_le_univ M1
      have c2 := Finset.card_le_univ M2
      simp only [Fintype.card_fin] at c1 c2
      omega
    have hbound : ∀ M ∈ P.parts, Dterm sys M x₁ ≤
        (if N - M.card < L then (1321 / 9990 * N + 1 / 500 : ℝ) else 0) + M.card * (1 / 500) := by
      intro M hM
      obtain ⟨hMu, hMne⟩ := hpart M hM
      by_cases hm : N - M.card < L
      · rw [if_pos hm]
        have := hsmall_D M hMu hMne hm
        have : (0 : ℝ) ≤ M.card * (1 / 500) := by positivity
        linarith
      · rw [if_neg hm, zero_add]
        exact Dterm_le_of_window sys x₁ M hZXpos (hW M (by omega))
    have hsum := Finset.sum_le_sum hbound
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_filter] at hsum
    have hsc : ∑ M ∈ P.parts, (M.card : ℝ) = N := by
      have := P.sum_card_parts
      simp only [Finset.card_univ, Fintype.card_fin] at this
      exact_mod_cast this
    rw [hsc, Finset.sum_const, nsmul_eq_mul] at hsum
    have hb0 : (0 : ℝ) ≤ 1321 / 9990 * N + 1 / 500 := by positivity
    have : (sm.card : ℝ) * (1321 / 9990 * N + 1 / 500) ≤ 1321 / 9990 * N + 1 / 500 := by
      have : (sm.card : ℝ) ≤ 1 := by exact_mod_cast hsm
      nlinarith
    norm_num at hsum this ⊢
    linarith
  · intro R hR hRne
    by_cases hm : N - R.card < L
    · have := hsmall_ei R hR.ne hRne hm
      norm_num at this ⊢; linarith
    · have h1 := ei_le_of_window sys x₁ R (hW R (by omega))
      have h2 := hcard_le R
      norm_num at h1 ⊢; linarith

end

end IIT2
