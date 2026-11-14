/-
Basic theorems for IIT 2.0 [BT08].
-/
import IIT2.Basic

namespace IIT2

open Finset Real

variable {N : ℕ}

/-! ## Averages -/

lemma card_pos : (0 : ℝ) < (Fintype.card (State N) : ℝ) := by
  exact_mod_cast Fintype.card_pos

lemma avg_nonneg {f : State N → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ avg f :=
  div_nonneg (Finset.sum_nonneg fun x _ => hf x) card_pos.le

lemma avg_pos {f : State N → ℝ} (hf : ∀ x, 0 ≤ f x) {x : State N} (hx : 0 < f x) :
    0 < avg f := by
  unfold avg
  refine div_pos ?_ card_pos
  exact lt_of_lt_of_le hx (Finset.single_le_sum (fun y _ => hf y) (Finset.mem_univ x))

lemma exists_pos_of_avg_pos {f : State N → ℝ} (h : 0 < avg f) : ∃ x, 0 < f x := by
  by_contra hc
  push Not at hc
  have : avg f ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (Finset.sum_nonpos fun x _ => hc x) card_pos.le
  linarith

lemma avg_const (c : ℝ) : avg (fun _ : State N => c) = c := by
  unfold avg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [card_pos.ne']

lemma avg_mono {f g : State N → ℝ} (h : ∀ x, f x ≤ g x) : avg f ≤ avg g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) card_pos.le

lemma avg_sub (f g : State N → ℝ) : avg (fun x => f x - g x) = avg f - avg g := by
  unfold avg; rw [Finset.sum_sub_distrib, sub_div]

lemma avg_div_const (f : State N → ℝ) (c : ℝ) : avg (fun x => f x / c) = avg f / c := by
  unfold avg; rw [← Finset.sum_div, div_div, div_div, mul_comm]

lemma avg_congr {f g : State N → ℝ} (h : ∀ x, f x = g x) : avg f = avg g := by
  have : f = g := funext h
  rw [this]

/-! ## Mixing and independence -/

lemma mix_eq_of_mem {A : Finset (Fin N)} {x e : State N} {i : Fin N} (h : i ∈ A) :
    mix A x e i = x i := by simp [mix, h]

lemma mix_eq_of_not_mem {A : Finset (Fin N)} {x e : State N} {i : Fin N} (h : i ∉ A) :
    mix A x e i = e i := by simp [mix, h]

/-- The swap `(x, y) ↦ (mix A x y, mix A y x)`, an involution of `State N × State N`. -/
def swapEquiv (A : Finset (Fin N)) : State N × State N ≃ State N × State N where
  toFun p := (mix A p.1 p.2, mix A p.2 p.1)
  invFun p := (mix A p.1 p.2, mix A p.2 p.1)
  left_inv p := by
    ext i <;> by_cases h : i ∈ A <;> simp [mix, h]
  right_inv p := by
    ext i <;> by_cases h : i ∈ A <;> simp [mix, h]

/-- Independence under the maximum entropy distribution: functions of disjoint sets of
coordinates are uncorrelated. -/
lemma avg_mul_of_disjoint {A B : Finset (Fin N)} (hAB : Disjoint A B) {f g : State N → ℝ}
    (hf : DepOn A f) (hg : DepOn B g) : avg (fun x => f x * g x) = avg f * avg g := by
  have key : (∑ x, f x) * (∑ y, g y) =
      (Fintype.card (State N) : ℝ) * ∑ x, f x * g x := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    rw [show (∑ p ∈ (Finset.univ : Finset (State N)) ×ˢ Finset.univ, f p.1 * g p.2)
        = ∑ p : State N × State N, f p.1 * g p.2 from rfl]
    rw [← (swapEquiv A).sum_comp]
    have h1 : ∀ p : State N × State N, f ((swapEquiv A) p).1 * g ((swapEquiv A) p).2
        = f p.1 * g p.1 := by
      intro p
      simp only [swapEquiv, Equiv.coe_fn_mk]
      congr 1
      · exact hf _ _ (fun i hi => mix_eq_of_mem hi)
      · exact hg _ _ (fun i hi => mix_eq_of_not_mem (Finset.disjoint_right.mp hAB hi))
    simp_rw [h1]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  unfold avg
  have hc := card_pos (N := N)
  field_simp
  linarith [key]

lemma DepOn.mono {A B : Finset (Fin N)} (h : A ⊆ B) {f : State N → ℝ} (hf : DepOn A f) :
    DepOn B f := fun x y hxy => hf x y (fun i hi => hxy i (h hi))

lemma DepOn.mul {A : Finset (Fin N)} {f g : State N → ℝ} (hf : DepOn A f) (hg : DepOn A g) :
    DepOn A (fun x => f x * g x) := fun x y h => by
  show f x * g x = f y * g y
  rw [hf x y h, hg x y h]

/-- Product over pairwise disjoint coordinate sets: the average factorizes. -/
lemma avg_prod_of_pairwiseDisjoint (F : Finset (Finset (Fin N)))
    (hF : (F : Set (Finset (Fin N))).PairwiseDisjoint id)
    (f : Finset (Fin N) → State N → ℝ) (hf : ∀ M ∈ F, DepOn M (f M)) :
    avg (fun x => ∏ M ∈ F, f M x) = ∏ M ∈ F, avg (f M) ∧
      DepOn (F.sup id) (fun x => ∏ M ∈ F, f M x) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact ⟨avg_const 1, fun _ _ _ => rfl⟩
  | insert a F ha ih =>
    have hF' : (F : Set (Finset (Fin N))).PairwiseDisjoint id :=
      hF.subset (by simp [Finset.coe_insert])
    obtain ⟨ih1, ih2⟩ := ih hF' (fun M hM => hf M (Finset.mem_insert_of_mem hM))
    have hdis : Disjoint a (F.sup id) := by
      rw [Finset.disjoint_sup_right]
      intro M hM
      exact hF (by simp) (by simp [hM]) (fun h => ha (h ▸ hM))
    have hfa := hf a (Finset.mem_insert_self a F)
    simp only [Finset.prod_insert ha]
    refine ⟨?_, ?_⟩
    · rw [avg_mul_of_disjoint hdis hfa ih2, ih1]
    · rw [Finset.sup_insert]
      exact (hfa.mono le_sup_left).mul (ih2.mono le_sup_right)

/-! ## Repertoires -/

lemma cond_nonneg (sys : UnitTPM N) (A : Finset (Fin N)) (x₁ x₀ : State N) :
    0 ≤ cond sys A x₁ x₀ :=
  Finset.prod_nonneg fun i _ => avg_nonneg fun e => sys.nonneg _ _ _

lemma cond_depOn (sys : UnitTPM N) (A : Finset (Fin N)) (x₁ : State N) :
    DepOn A (cond sys A x₁) := by
  intro x y h
  unfold cond
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  funext e
  have : mix A x e = mix A y e := by
    funext j; by_cases hj : j ∈ A <;> simp [mix, hj, h j]
  rw [this]

lemma post_nonneg (sys : UnitTPM N) (A : Finset (Fin N)) (x₁ x₀ : State N) :
    0 ≤ post sys A x₁ x₀ :=
  div_nonneg (cond_nonneg _ _ _ _) (avg_nonneg fun _ => cond_nonneg _ _ _ _)

lemma post_depOn (sys : UnitTPM N) (A : Finset (Fin N)) (x₁ : State N) :
    DepOn A (post sys A x₁) := fun x y h => by
  unfold post; rw [cond_depOn sys A x₁ x y h]

lemma avg_post (sys : UnitTPM N) (A : Finset (Fin N)) (x₁ : State N)
    (h : 0 < avg (cond sys A x₁)) : avg (post sys A x₁) = 1 := by
  unfold post
  rw [avg_div_const, div_self h.ne']

lemma post_eq_zero (sys : UnitTPM N) (A : Finset (Fin N)) (x₁ : State N)
    (h : ¬ 0 < avg (cond sys A x₁)) (x : State N) : post sys A x₁ x = 0 := by
  have h0 : avg (cond sys A x₁) = 0 :=
    le_antisymm (not_lt.mp h) (avg_nonneg fun _ => cond_nonneg _ _ _ _)
  simp [post, h0]

/-- If a perturbation `x₀` of `S` can cause `s₁`, then its restriction to any `M ⊆ S` can
cause `m₁` when `M` is considered on its own. -/
lemma cond_pos_of_subset (sys : UnitTPM N) {M S : Finset (Fin N)} (hMS : M ⊆ S)
    (x₁ x : State N) (h : 0 < cond sys S x₁ x) : 0 < cond sys M x₁ x := by
  have hS : ∀ i ∈ S, 0 < avg (fun e => sys.prob i (mix S x e) (x₁ i)) := by
    intro i hi
    have hne := (Finset.prod_ne_zero_iff.mp h.ne') i hi
    exact lt_of_le_of_ne (avg_nonneg fun _ => sys.nonneg _ _ _) (Ne.symm hne)
  refine Finset.prod_pos fun i hi => ?_
  obtain ⟨e, he⟩ := exists_pos_of_avg_pos (hS i (hMS hi))
  have hmix : mix M x (mix S x e) = mix S x e := by
    funext j
    by_cases hj : j ∈ M
    · simp [mix, hj, hMS hj]
    · simp [mix, hj]
  refine avg_pos (fun _ => sys.nonneg _ _ _) (x := mix S x e) ?_
  rw [hmix]; exact he

lemma post_pos_of_subset (sys : UnitTPM N) {M S : Finset (Fin N)} (hMS : M ⊆ S)
    (x₁ x : State N) (h : 0 < post sys S x₁ x) : 0 < post sys M x₁ x := by
  have hS : 0 < cond sys S x₁ x := by
    rcases (cond_nonneg sys S x₁ x).lt_or_eq with h' | h'
    · exact h'
    · simp [post, ← h'] at h
  have hM := cond_pos_of_subset sys hMS x₁ x hS
  exact div_pos hM (avg_pos (fun _ => cond_nonneg _ _ _ _) hM)

/-! ## Gibbs' inequality -/

lemma mul_log_div_ge {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p → 0 < q) :
    p - q ≤ p * Real.log (p / q) := by
  rcases hp.lt_or_eq with hp' | hp'
  · have hq' := hpq hp'
    have h1 := Real.log_le_sub_one_of_pos (div_pos hq' hp')
    have h2 : Real.log (p / q) = - Real.log (q / p) := by
      rw [← Real.log_inv, inv_div]
    rw [h2]
    have : p * (q / p - 1) = q - p := by field_simp
    nlinarith
  · subst hp'; simp [hq]

/-- Relative entropy is non-negative `[BT08, p.3]` ("It is always non-negative"). -/
theorem kl_nonneg {p q : State N → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hp1 : avg p = 1) (hq1 : avg q ≤ 1) (hpq : ∀ x, 0 < p x → 0 < q x) : 0 ≤ kl p q := by
  unfold kl
  have hl : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have : avg (fun x => p x * logb 2 (p x / q x)) =
      avg (fun x => p x * Real.log (p x / q x)) / Real.log 2 := by
    rw [← avg_div_const]
    exact avg_congr fun x => by unfold logb; ring
  rw [this]
  refine div_nonneg ?_ hl.le
  have := avg_mono (fun x => mul_log_div_ge (hp x) (hq x) (hpq x))
  rw [avg_sub, hp1] at this
  linarith

lemma kl_zero_left (q : State N → ℝ) : kl (fun _ => 0) q = 0 := by
  simp [kl, avg_const]

lemma kl_self (p : State N → ℝ) : kl p p = 0 := by
  unfold kl
  rw [← avg_const (N := N) 0]
  exact avg_congr fun x => by
    by_cases h : p x = 0
    · simp [h]
    · simp [div_self h]

/-! ## Non-negativity of ei and φ -/

/-- `ei(S₀ → s₁) ≥ 0` `[BT08, p.3]`. -/
theorem ei_nonneg (sys : UnitTPM N) (S : Finset (Fin N)) (x₁ : State N) :
    0 ≤ ei sys S x₁ := by
  unfold ei
  by_cases h : 0 < avg (cond sys S x₁)
  · exact kl_nonneg (post_nonneg _ _ _) (fun _ => zero_le_one) (avg_post _ _ _ h)
      (avg_const 1).le (fun _ _ => one_pos)
  · have : post sys S x₁ = fun _ => 0 := funext (post_eq_zero sys S x₁ h)
    rw [this, kl_zero_left]

/-- The combined a posteriori repertoire of the parts has total mass `1` (when `s₁` is
reachable), and is positive wherever the repertoire of `S` is. -/
lemma partsPost_props (sys : UnitTPM N) {S : Finset (Fin N)} (P : Finpartition S)
    (x₁ : State N) (h : 0 < avg (cond sys S x₁)) :
    avg (partsPost sys P x₁) = 1 ∧
      ∀ x, 0 < post sys S x₁ x → 0 < partsPost sys P x₁ x := by
  have hpos : ∀ x, 0 < post sys S x₁ x → 0 < partsPost sys P x₁ x := fun x hx =>
    Finset.prod_pos fun M hM => post_pos_of_subset sys (P.le hM) x₁ x hx
  refine ⟨?_, hpos⟩
  obtain ⟨x, hx⟩ := exists_pos_of_avg_pos (by rw [avg_post _ _ _ h]; exact one_pos)
  have hfac := (avg_prod_of_pairwiseDisjoint P.parts P.disjoint (fun M => post sys M x₁)
    (fun M _ => post_depOn sys M x₁)).1
  unfold partsPost
  rw [hfac]
  refine Finset.prod_eq_one fun M hM => avg_post sys M x₁ ?_
  have hc : 0 < cond sys S x₁ x := by
    rcases (cond_nonneg sys S x₁ x).lt_or_eq with h' | h'
    · exact h'
    · simp [post, ← h'] at hx
  exact avg_pos (fun _ => cond_nonneg _ _ _ _) (cond_pos_of_subset sys (P.le hM) x₁ x hc)

/-- `ei(S₀ → s₁ / P) ≥ 0` for every partition `[BT08, p.5]`. -/
theorem eiRel_nonneg (sys : UnitTPM N) {S : Finset (Fin N)} (P : Finpartition S)
    (x₁ : State N) : 0 ≤ eiRel sys P x₁ := by
  unfold eiRel
  by_cases h : 0 < avg (cond sys S x₁)
  · obtain ⟨h1, h2⟩ := partsPost_props sys P x₁ h
    exact kl_nonneg (post_nonneg _ _ _)
      (fun x => Finset.prod_nonneg fun M _ => post_nonneg _ _ _ _) (avg_post _ _ _ h) h1.le h2
  · have : post sys S x₁ = fun _ => 0 := funext (post_eq_zero sys S x₁ h)
    rw [this, kl_zero_left]

theorem eiAcross_nonneg (sys : UnitTPM N) {S : Finset (Fin N)} (P : Finpartition S)
    (x₁ : State N) : 0 ≤ eiAcross sys P x₁ := by
  unfold eiAcross; split_ifs
  · exact ei_nonneg _ _ _
  · exact eiRel_nonneg _ _ _

lemma normP_nonneg {S : Finset (Fin N)} (P : Finpartition S) : 0 ≤ normP P := by
  unfold normP
  split_ifs with h
  · positivity
  · rcases Nat.lt_or_ge P.parts.card 1 with h' | h'
    · have : P.parts.card = 0 := by omega
      simp [this, minPartSize, Finset.card_eq_zero.mp this]
    · have : (1 : ℝ) ≤ P.parts.card := by exact_mod_cast h'
      exact mul_nonneg (by linarith) (by positivity)

/-- φ is attained by some partition (a minimum information partition). -/
theorem exists_isMIP (sys : UnitTPM N) (S : Finset (Fin N)) (x₁ : State N) :
    ∃ P : Finpartition S, IsMIP sys x₁ P ∧ phi sys S x₁ = eiAcross sys P x₁ := by
  obtain ⟨P, -, hP⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Finpartition S))
    (mipKey sys x₁)
  refine ⟨P, fun Q => ?_, ?_⟩
  · rw [← hP]; exact Finset.inf'_le _ (Finset.mem_univ Q)
  · unfold phi; rw [hP]; rfl

/-- `φ(s₁) ≥ 0` `[BT08, p.4–7]`. -/
theorem phi_nonneg (sys : UnitTPM N) (S : Finset (Fin N)) (x₁ : State N) :
    0 ≤ phi sys S x₁ := by
  obtain ⟨P, -, hP⟩ := exists_isMIP sys S x₁
  rw [hP]; exact eiAcross_nonneg _ _ _

/-- If some partition has zero effective information across it, then `φ = 0`. -/
theorem phi_eq_zero_of_eiAcross_eq_zero (sys : UnitTPM N) {S : Finset (Fin N)}
    (x₁ : State N) (Q : Finpartition S) (hQ : eiAcross sys Q x₁ = 0) : phi sys S x₁ = 0 := by
  obtain ⟨P, hMIP, hP⟩ := exists_isMIP sys S x₁
  have hle := hMIP Q
  unfold mipKey at hle
  rw [hQ, zero_div, Prod.Lex.toLex_le_toLex'] at hle
  have ha : 0 ≤ eiAcross sys P x₁ / normP P :=
    div_nonneg (eiAcross_nonneg _ _ _) (normP_nonneg P)
  have hb : eiAcross sys P x₁ ≤ 0 := hle.2 (le_antisymm hle.1 ha)
  rw [hP]; exact le_antisymm hb (eiAcross_nonneg _ _ _)

/-- An empty set has `φ = 0`, hence is never a complex. -/
theorem phi_empty (sys : UnitTPM N) (x₁ : State N) : phi sys ∅ x₁ = 0 := by
  obtain ⟨P, -, hP⟩ := exists_isMIP sys ∅ x₁
  have hparts : P.parts = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty, Finpartition.parts_nonempty_iff]; simp
  rw [hP]
  unfold eiAcross eiRel partsPost
  rw [hparts]
  simp only [Finset.card_empty, zero_ne_one, if_false, Finset.prod_empty]
  have hc : cond sys ∅ x₁ = fun _ => 1 := funext fun x => by simp [cond, avg_const]
  have : post sys ∅ x₁ = fun _ => 1 := by
    funext x; simp [post, hc, avg_const]
  rw [this]; exact kl_self _

/-! ## Systems that split into independent parts -/

/-- The bipartition `{A, B}` of `A ∪ B`. -/
def pairPartition (A B : Finset (Fin N)) (hAB : Disjoint A B) (hA : A.Nonempty)
    (hB : B.Nonempty) : Finpartition (A ∪ B) where
  parts := {A, B}
  supIndep := by
    have hne : A ≠ B := fun h => by
      subst h; exact (Finset.disjoint_self_iff_empty A).mp hAB ▸ hA |>.ne_empty rfl
    exact (Finset.supIndep_pair hne).mpr hAB
  sup_parts := by simp [Finset.sup_insert]
  bot_notMem := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hA.ne_empty h.symm, fun h => hB.ne_empty h.symm⟩

/-- `φ = 0` for a system that splits into two independent parts `[BT08, p.4]`
("integrated information is zero if [...] the system can be decomposed into a collection of
independent parts"; Fig 3; `[BT08 S1, §4]` "No integrated information is generated by a
disconnected system").  Hypothesis: no element of `A` takes input from `B` and no element of
`B` takes input from `A`.  Inputs from outside `A ∪ B` are arbitrary and may be shared (e.g.
`a' = a ⊕ e`, `b' = b ⊕ e`): each element's extrinsic input is averaged separately
`[BT08 S1, §3]`. -/
theorem phi_eq_zero_of_independent (sys : UnitTPM N) (A B : Finset (Fin N))
    (hA : A.Nonempty) (hB : B.Nonempty) (hAB : Disjoint A B)
    (hinA : ∀ i ∈ A, ∀ s s' : State N, (∀ j, j ∉ B → s j = s' j) → sys.prob i s = sys.prob i s')
    (hinB : ∀ i ∈ B, ∀ s s' : State N, (∀ j, j ∉ A → s j = s' j) → sys.prob i s = sys.prob i s')
    (x₁ : State N) : phi sys (A ∪ B) x₁ = 0 := by
  have hcond : ∀ x, cond sys (A ∪ B) x₁ x = cond sys A x₁ x * cond sys B x₁ x := by
    intro x
    unfold cond
    rw [Finset.prod_union hAB]
    congr 1
    · refine Finset.prod_congr rfl fun i hi => avg_congr fun e => ?_
      rw [hinA i hi (mix (A ∪ B) x e) (mix A x e) fun j hj => ?_]
      by_cases hjA : j ∈ A <;> simp [mix, hjA, hj]
    · refine Finset.prod_congr rfl fun i hi => avg_congr fun e => ?_
      rw [hinB i hi (mix (A ∪ B) x e) (mix B x e) fun j hj => ?_]
      by_cases hjB : j ∈ B <;> simp [mix, hjB, hj]
  have hpost : ∀ x, post sys (A ∪ B) x₁ x = post sys A x₁ x * post sys B x₁ x := by
    intro x
    unfold post
    rw [hcond x, avg_congr hcond,
      avg_mul_of_disjoint hAB (cond_depOn sys A x₁) (cond_depOn sys B x₁), mul_div_mul_comm]
  let Q := pairPartition A B hAB hA hB
  have hne : A ≠ B := fun h => by
    subst h; exact (Finset.disjoint_self_iff_empty A).mp hAB ▸ hA |>.ne_empty rfl
  have hcard : Q.parts.card = 2 := Finset.card_pair hne
  refine phi_eq_zero_of_eiAcross_eq_zero sys x₁ Q ?_
  unfold eiAcross
  rw [hcard, if_neg (by norm_num)]
  unfold eiRel
  have : partsPost sys Q x₁ = post sys (A ∪ B) x₁ := by
    funext x
    unfold partsPost
    show ∏ M ∈ ({A, B} : Finset (Finset (Fin N))), post sys M x₁ x = _
    rw [Finset.prod_pair hne, hpost x]
  rw [this, kl_self]

/-! ## Complexes -/

theorem not_isComplex_of_phi_eq_zero (sys : UnitTPM N) (x₁ : State N) (S : Finset (Fin N))
    (h : phi sys S x₁ = 0) : ¬ IsComplex sys x₁ S := fun hc => by
  have := hc.1; rw [h] at this; exact lt_irrefl 0 this

/-- The whole system is a complex iff `φ(x₁) > 0` (nothing contains `X` strictly). -/
theorem isComplex_univ_iff (sys : UnitTPM N) (x₁ : State N) :
    IsComplex sys x₁ Finset.univ ↔ 0 < phi sys Finset.univ x₁ := by
  refine ⟨fun h => h.1, fun h => ⟨h, fun T hT => ?_⟩⟩
  rw [Finset.univ_subset_iff.mp hT]

/-- Existence of a main complex `[BT08, p.7]` ("the complex in a given system with the
maximum value of φ necessarily forms a main complex"): if some subset has `φ > 0`, then a
subset of maximal `φ` and of minimal size among those is a main complex. -/
theorem exists_isMainComplex (sys : UnitTPM N) (x₁ : State N)
    (h : ∃ S : Finset (Fin N), 0 < phi sys S x₁) :
    ∃ S : Finset (Fin N), IsMainComplex sys x₁ S := by
  classical
  obtain ⟨S₀, hS₀⟩ := h
  set m := (Finset.univ : Finset (Finset (Fin N))).sup' Finset.univ_nonempty
    (fun S => phi sys S x₁) with hm
  have hle : ∀ S, phi sys S x₁ ≤ m := fun S =>
    Finset.le_sup' (fun S => phi sys S x₁) (Finset.mem_univ S)
  obtain ⟨S₁, -, hS₁⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun S : Finset (Fin N) => phi sys S x₁)
  set F := (Finset.univ : Finset (Finset (Fin N))).filter (fun S => phi sys S x₁ = m)
  have hFne : F.Nonempty := ⟨S₁, by simp [F, hm, hS₁]⟩
  obtain ⟨S, hSF, hmin⟩ := Finset.exists_min_image F Finset.card hFne
  have hSm : phi sys S x₁ = m := (Finset.mem_filter.mp hSF).2
  refine ⟨S, ⟨⟨?_, fun T _ => hSm ▸ hle T⟩, fun R hR => ?_⟩⟩
  · rw [hSm]; exact lt_of_lt_of_le hS₀ (hle S₀)
  · rcases (hle R).lt_or_eq with h' | h'
    · rwa [hSm]
    · exfalso
      have := hmin R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩)
      exact absurd (Finset.card_lt_card hR) (not_lt.mpr this)

end IIT2
