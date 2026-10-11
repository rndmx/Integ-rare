/-
Census, B1 LTBetaHi, module T2: **measurability of the triple stopping set** `{Priv = A}`.

Toolkit `FibM f` (every fibre of a finite-valued map is measurable), closed under composition, pairing and dependent
choice; `lt3Sel` is a function of the finite data (tc, the `P(tc)` test, `Top`, `Sp`, the lightness pattern, the
near-half pattern of row `s`), each fibre-measurable.
-/
import IIT.Census.B1LTHiInst

namespace IIT
namespace Census

open MeasureTheory Finset

variable {N : ℕ}

/-- Every fibre of `f` is measurable. -/
def FibM {β : Type*} (f : Param N → β) : Prop := ∀ b, MeasurableSet {w | f w = b}

lemma fibM_comp {β γ : Type*} [Fintype β] {f : Param N → β} (hf : FibM f) (g : β → γ) : FibM (fun w => g (f w)) := by
  classical
  intro c
  have e : {w | g (f w) = c} = ⋃ b ∈ (univ.filter fun b => g b = c), {w | f w = b} := by
    ext w; simp
  rw [e]; exact Finset.measurableSet_biUnion _ fun b _ => hf b

lemma fibM_pair {β γ : Type*} {f : Param N → β} {g : Param N → γ} (hf : FibM f) (hg : FibM g) :
    FibM (fun w => (f w, g w)) := by
  intro p
  have e : {w | (f w, g w) = p} = {w | f w = p.1} ∩ {w | g w = p.2} := by
    ext w; simp [Prod.ext_iff]
  rw [e]; exact (hf _).inter (hg _)

lemma fibM_dep {α β : Type*} [Fintype α] {f : Param N → α} (hf : FibM f) {g : α → Param N → β}
    (hg : ∀ a, FibM (g a)) : FibM (fun w => g (f w) w) := by
  intro c
  have e : {w | g (f w) w = c} = ⋃ a, {w | f w = a} ∩ {w | g a w = c} := by
    ext w; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨f w, rfl, h⟩, fun ⟨a, h1, h2⟩ => h1 ▸ h2⟩
  rw [e]; exact MeasurableSet.iUnion fun a => (hf a).inter (hg a c)

lemma fibM_decide {P : Param N → Prop} [DecidablePred P] (hP : MeasurableSet {w | P w}) :
    FibM (fun w => decide (P w)) := by
  intro b
  cases b
  · have e : {w | decide (P w) = false} = {w | P w}ᶜ := by ext w; simp
    rw [e]; exact hP.compl
  · have e : {w | decide (P w) = true} = {w | P w} := by ext w; simp
    rw [e]; exact hP

lemma fibM_fun {ι β : Type*} [Fintype ι] {f : Param N → ι → β} (hf : ∀ i, FibM fun w => f w i) : FibM f := by
  intro b
  have e : {w | f w = b} = ⋂ i, {w | f w i = b i} := by
    ext w; simp [funext_iff]
  rw [e]; exact MeasurableSet.iInter fun i => hf i (b i)

lemma fibM_const {β : Type*} (b0 : β) : FibM (fun _ : Param N => b0) := fun _ => MeasurableSet.const _

lemma fibM_tcRow : FibM (tcRow (N := N)) := fun r0 => measurableSet_tcRow_eq r0

/-- A finset defined by measurable membership conditions. -/
lemma fibM_filter {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Param N → ι → Prop} [∀ w, DecidablePred (P w)]
    (hP : ∀ i, MeasurableSet {w | P w i}) : FibM (fun w => univ.filter (P w)) := by
  have : (fun w => univ.filter (P w)) = fun w => (fun v : ι → Bool => univ.filter fun i => v i = true)
      (fun i => decide (P w i)) := by
    funext w; ext i; simp
  rw [this]
  exact fibM_comp (f := fun w i => decide (P w i)) (fibM_fun fun i => fibM_decide (hP i))
    (fun v : ι → Bool => univ.filter fun i => v i = true)

/-! ### The data of the selection -/

section Data

variable (s : State N) (ε γ : ℝ)

/-- `Top` for a given candidate row. -/
noncomputable def lt3TopOf (r : State N) (w : Param N) : Finset (Fin N) := by
  classical exact univ.filter fun j => b1YTopR w r ε ≤ clamp01 (w r j)

lemma lt3TopG_eq (w : Param N) : lt3TopG w ε = lt3TopOf ε (tcRow w) w := by
  unfold lt3TopG lt3TopOf; rfl

lemma fibM_TopOf (r : State N) : FibM (lt3TopOf (N := N) ε r) := by
  classical
  unfold lt3TopOf
  exact fibM_filter fun j => measurableSet_le (b1m_YTopR r ε) (b1m_clamp r j)

lemma fibM_TopG : FibM (fun w : Param N => lt3TopG w ε) := by
  have : (fun w : Param N => lt3TopG w ε) = fun w => lt3TopOf ε (tcRow w) w := funext fun w => lt3TopG_eq ε w
  rw [this]; exact fibM_dep fibM_tcRow (fibM_TopOf ε)

/-- The good units for a given candidate `tc` row. -/
noncomputable def lt3GoodUOf (r : State N) (w : Param N) : Finset (Fin N) := by
  classical exact univ.filter fun j => 17 / 20 ≤ clamp01 (w r j) ∧ 7 / 8 ≤ clamp01 (w s j)

lemma fibM_GoodUOf (r : State N) : FibM (lt3GoodUOf (N := N) s r) := by
  classical
  unfold lt3GoodUOf
  exact fibM_filter fun j => (measurableSet_le measurable_const (b1m_clamp r j)).inter
    (measurableSet_le measurable_const (b1m_clamp s j))

lemma fibM_GoodU : FibM (fun w : Param N => lt3GoodU s w) := by
  have : (fun w : Param N => lt3GoodU s w) = fun w => lt3GoodUOf s (tcRow w) w := by
    funext w; unfold lt3GoodU lt3GoodUOf; rfl
  rw [this]; exact fibM_dep fibM_tcRow (fibM_GoodUOf s)

lemma fibM_Sp : FibM (lt2Sp (N := N)) := by
  classical
  unfold lt2Sp
  exact fibM_filter fun r => measurableSet_le (b1m_XW r) measurable_const

lemma fibM_SpTc : FibM (fun w : Param N => (lt2Sp w, tcRow w)) := fibM_pair fibM_Sp fibM_tcRow

open Classical in
lemma fibM_Top : FibM (fun w : Param N => lt3Top s w ε) := by
  set g : (Finset (State N) × State N) × Finset (Fin N) × Finset (Fin N) → Finset (Fin N) := fun p =>
    if s ∈ p.1.1 ∧ s ≠ p.1.2 then (p.2.1.sort (· ≤ ·) |>.take ⌈ε * N⌉₊).toFinset else p.2.2 with hg
  have e : (fun w : Param N => lt3Top s w ε) = fun w => g ((lt2Sp w, tcRow w), lt3GoodU s w, lt3TopG w ε) := by
    funext w; unfold lt3Top lt3TopP lt3SpC; rw [hg]; by_cases h : s ∈ lt2Sp w ∧ s ≠ tcRow w <;> simp [h]
  rw [e]
  exact fibM_comp (f := fun w => ((lt2Sp w, tcRow w), lt3GoodU s w, lt3TopG w ε))
    (fibM_pair fibM_SpTc (fibM_pair (fibM_GoodU s) (fibM_TopG ε))) g

/-- The lightness pattern for a given `Top`. -/
noncomputable def lt3LvOf (T : Finset (Fin N)) (w : Param N) : State N → Bool := by
  classical exact fun q => decide (3 / 10 * (N : ℝ) < XMW w Tᶜ q)

lemma fibM_LvOf (T : Finset (Fin N)) : FibM (lt3LvOf T) := by
  classical
  refine fibM_fun fun q => ?_
  unfold lt3LvOf
  exact fibM_decide (measurableSet_lt measurable_const (b1m_XMW _ q))

lemma lt3L_iff (w : Param N) (q : State N) : lt3L s ε w q ↔ lt3LvOf (lt3Top s w ε) w q = true := by
  unfold lt3L lt3LvOf; simp

lemma fibM_Lv : FibM (fun w : Param N => lt3LvOf (lt3Top s w ε) w) :=
  fibM_dep (fibM_Top s ε) fibM_LvOf

/-- The near-half pattern of row `s`. -/
noncomputable def lt3Hv (w : Param N) : Fin N → Bool := by
  classical exact fun j => decide (clamp01 (w s j) ∈ Set.Ioo (1 / 2 - γ) (1 / 2 + γ))

lemma fibM_Hv : FibM (lt3Hv (N := N) s γ) := by
  classical
  refine fibM_fun fun j => ?_
  unfold lt3Hv
  exact fibM_decide (measurableSet_Ioo.preimage (b1m_clamp s j))

/-- The `P(tc)` test. -/
noncomputable def lt3Pv (w : Param N) : Bool := by
  classical exact decide (Real.exp (-(3 / 10 * (N : ℝ))) < Pw w (tcRow w))

lemma fibM_Pv : FibM (lt3Pv (N := N)) := by
  classical
  unfold lt3Pv
  exact fibM_decide (b1_measurableSet_at_tcRow (P := fun w r => Real.exp (-(3 / 10 * (N : ℝ))) < Pw w r)
    fun r => measurableSet_lt measurable_const (b1m_Pw r))

/-- The selection as a function of the data. -/
noncomputable def lt3SelOf (d : State N × Bool × Finset (Fin N) × Finset (State N) × (State N → Bool) ×
    (Fin N → Bool)) : Finset (Finset (Fin N) × State N) := by
  classical exact
    let t := d.1; let P := d.2.1; let T := d.2.2.1; let Sp := d.2.2.2.1; let Lv := d.2.2.2.2.1
    let Hv := d.2.2.2.2.2
    let B := insert t (insert s Sp)
    let Ex := T.filter fun j => (∃ r ∈ B, Lv (flip r j) = false) ∨ Hv j = true
    let Q := lt3QOf B (T \ Ex) t
    let F := (qFam Q).filter fun S => ∀ r ∈ B, ∀ R ⊆ S, 2 ≤ R.card → Lv (flipS r R) = true
    if P = true ∧ 7 ≤ Q.card then F ×ˢ B else ∅

lemma lt3Sel_eq (w : Param N) :
    lt3Sel s ε γ w = lt3SelOf s (tcRow w, lt3Pv w, lt3Top s w ε, lt2Sp w, lt3LvOf (lt3Top s w ε) w, lt3Hv s γ w) := by
  classical
  have hEx : lt3Ex s ε γ w = (lt3Top s w ε).filter fun j =>
      (∃ r ∈ lt3Base s w, lt3LvOf (lt3Top s w ε) w (flip r j) = false) ∨ lt3Hv s γ w j = true := by
    unfold lt3Ex
    refine Finset.filter_congr fun j _ => ?_
    simp only [lt3L_iff, Bool.not_eq_true, lt3Hv, decide_eq_true_eq]
  have hF : lt3F s ε γ w = (qFam (lt3Q s ε γ w)).filter fun S =>
      ∀ r ∈ lt3Base s w, ∀ R ⊆ S, 2 ≤ R.card → lt3LvOf (lt3Top s w ε) w (flipS r R) = true := by
    unfold lt3F
    exact Finset.filter_congr fun S _ => by simp only [lt3L_iff]
  have hQ : lt3Q s ε γ w = lt3QOf (lt3Base s w) (lt3Top s w ε \ ((lt3Top s w ε).filter fun j =>
      (∃ r ∈ lt3Base s w, lt3LvOf (lt3Top s w ε) w (flip r j) = false) ∨ lt3Hv s γ w j = true)) (tcRow w) := by
    unfold lt3Q; rw [hEx]
  unfold lt3Sel lt3SelOf
  simp only [lt3Pv, decide_eq_true_eq]
  rw [hF, hQ]
  rfl

end Data

/-- **`{Sel = K}` is measurable.** -/
theorem lt3_mset_Sel (s : State N) (ε γ : ℝ) : FibM (lt3Sel s ε γ) := by
  have e : lt3Sel s ε γ = fun w => lt3SelOf s
      (tcRow w, lt3Pv w, lt3Top s w ε, lt2Sp w, lt3LvOf (lt3Top s w ε) w, lt3Hv s γ w) :=
    funext fun w => lt3Sel_eq s ε γ w
  rw [e]
  exact fibM_comp (fibM_pair fibM_tcRow (fibM_pair fibM_Pv (fibM_pair (fibM_Top s ε) (fibM_pair fibM_Sp
    (fibM_pair (fibM_Lv s ε) (fibM_Hv s γ)))))) _

/-- **`{Priv = A}` is measurable.** -/
theorem lt3_mset_Priv (s : State N) (ε γ : ℝ) (A : Finset (State N × Fin N)) :
    MeasurableSet {w : Param N | stPriv (lt3Sel s ε γ) lt3PB w = A} := by
  have := fibM_comp (lt3_mset_Sel s ε γ) (fun K => K.biUnion lt3PB)
  exact this A

/-- **Conditioning on the triple private positions** (W2 Lemma CI, as `lt2_cond_priv`). -/
theorem lt3_cond_priv (s : State N) (ε γ : ℝ) {Y : Set (Param N)} (hY : MeasurableSet Y) {p : ENNReal}
    (h : ∀ A w, stPriv (lt3Sel s ε γ) lt3PB w = A → cubeM N {η | replE A w η ∈ Y} ≤ p) : cubeM N Y ≤ p := by
  have : IsProbabilityMeasure (cubeM N) := by unfold cubeM; infer_instance
  rw [measure_eq_sum_partition (cubeM N) (lt3_mset_Priv s ε γ) Y]
  calc ∑ A, cubeM N (Y ∩ {w | stPriv (lt3Sel s ε γ) lt3PB w = A})
      ≤ ∑ A, p * cubeM N {w | stPriv (lt3Sel s ε γ) lt3PB w = A} :=
        Finset.sum_le_sum fun A _ => by
          rw [Set.inter_comm]
          exact cubeM_inter_le_of_sectionE A (lt3_mset_Priv s ε γ A) hY (lt3Priv_detOn A) fun w hw => h A w hw
    _ = p * ∑ A, cubeM N (Set.univ ∩ {w | stPriv (lt3Sel s ε γ) lt3PB w = A}) := by
        rw [Finset.mul_sum]; simp only [Set.univ_inter]
    _ = p := by
        rw [← measure_eq_sum_partition (cubeM N) (lt3_mset_Priv s ε γ) Set.univ, measure_univ, mul_one]

/-- **The deterministic perturbation bound for triples** (W2 (6.1)): a light statistic summed over non-special rows
moves by at most `|Priv|(1+nσ)(e^{-3N/10} + e^{-x₁N})` when the private entries are set to `1/2`. -/
theorem lt3_pert (s : State N) (ε γ : ℝ) (w : Param N) (V : Finset (State N)) (hV : ∀ v ∈ V, v ∉ lt2Sp w)
    (σ : State N → State N) (i : Fin N) (g : (Fin N → ℝ) → ℝ) (hg0 : ∀ x, 0 ≤ g x)
    (hgP : ∀ x, g x ≤ ∏ j, clamp01 (x j)) (nσ : ℕ) (hfib : ∀ q, (V.filter fun v => σ v = q).card ≤ nσ) :
    |∑ v ∈ V, clamp01 (w (σ v) i) * g (w v) -
        ∑ v ∈ V, clamp01 (stHalf (stPriv (lt3Sel s ε γ) lt3PB w) w (σ v) i) *
          g (stHalf (stPriv (lt3Sel s ε γ) lt3PB w) w v)| ≤
      ((stPriv (lt3Sel s ε γ) lt3PB w).card * (1 + nσ) : ℕ) *
        (Real.exp (-(3 / 10 * (N : ℝ))) + Real.exp (-(lt2x1 * N))) := by
  classical
  have hns : ∀ q ∈ stPriv (lt3Sel s ε γ) lt3PB w, q ∉ lt3Safe s ε w := fun q hq => by
    obtain ⟨k, hk, hq⟩ := mem_biUnion.1 hq
    exact lt3PB_not_safe w k hk q hq
  refine st_pert _ w V σ i g hg0 hgP (lt3Top s w ε)ᶜ (3 / 10) _ (Real.exp_pos _).le
    (fun q hq hc => (hns q hq) (Or.inl (mem_compl.1 hc)))
    (fun v _ ⟨j, hj⟩ => by
      by_contra hl
      exact hns (v, j) hj (Or.inr (Or.inl hl)))
    (fun v hv _ => Or.inr ?_) nσ hfib
  have hX : lt2x1 * N < XW w v := by
    have := hV v hv
    simp only [lt2Sp, mem_filter, mem_univ, true_and, not_le] at this
    exact this
  refine (hgP (w v)).trans ?_
  have := st_Pw_le_exp univ w v
  rw [XMW_univ] at this
  exact this.trans (Real.exp_le_exp.2 (by linarith))

lemma lt3PB_card_le (k : Finset (Fin N) × State N) (hk : k.1.card ≤ 3) : (lt3PB k).card ≤ 24 := by
  classical
  unfold lt3PB
  refine card_image_le.trans ((card_filter_le _ _).trans ?_)
  rw [card_product, card_powerset]
  calc 2 ^ k.1.card * k.1.card ≤ 2 ^ 3 * 3 := Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hk) hk
    _ = 24 := by norm_num

/-- `|Priv| ≤ 24 |Sel| ≤ 24 |qFam Q| |Base|`. -/
theorem lt3_Priv_card (s : State N) (ε γ : ℝ) (w : Param N) :
    (stPriv (lt3Sel s ε γ) lt3PB w).card ≤ 24 * (lt3Sel s ε γ w).card := by
  classical
  unfold stPriv
  refine card_biUnion_le.trans ?_
  calc ∑ k ∈ lt3Sel s ε γ w, (lt3PB k).card ≤ ∑ _k ∈ lt3Sel s ε γ w, 24 := sum_le_sum fun k hk => by
        refine lt3PB_card_le k ?_
        unfold lt3Sel at hk
        split_ifs at hk
        · exact qFam_card_le (mem_filter.1 (mem_product.1 hk).1).1
        · simp at hk
    _ = 24 * (lt3Sel s ε γ w).card := by rw [sum_const, smul_eq_mul, mul_comm]

lemma lt3_Sel_card (s : State N) (ε γ : ℝ) (w : Param N) :
    (lt3Sel s ε γ w).card ≤ (qFam (lt3Q s ε γ w)).card * (lt3Base s w).card := by
  classical
  unfold lt3Sel
  split_ifs
  · rw [card_product]; exact Nat.mul_le_mul_right _ (card_filter_le _ _)
  · simp

open Classical in
/-- **Size of `Ex`** (deterministic): if `|Top| ≤ k`, every row has `< K` units with a non-robust flip, and `< K`
units of `s` are near `1/2`, then `|Ex| ≤ (|Base| + 1) K`. -/
theorem lt3_Ex_card (s : State N) (ε γ : ℝ) (hγ : γ < 1 / 2) (w : Param N) {k K : ℕ} (hTop : (lt3Top s w ε).card ≤ k)
    (hrob : ∀ h : State N, (univ.filter fun j : Fin N => ¬ stRobust N k (w (flip h j))).card < K)
    (hhalf : (univ.filter fun j : Fin N => w s j ∈ Set.Ioo (1 / 2 - γ) (1 / 2 + γ)).card < K) :
    (lt3Ex s ε γ w).card ≤ ((lt3Base s w).card + 1) * K := by
  have hsub : lt3Ex s ε γ w ⊆ (lt3Base s w).biUnion (fun h => univ.filter fun j : Fin N =>
      ¬ stRobust N k (w (flip h j))) ∪ univ.filter fun j : Fin N => w s j ∈ Set.Ioo (1 / 2 - γ) (1 / 2 + γ) := by
    intro j hj
    unfold lt3Ex at hj
    obtain ⟨-, hc⟩ := mem_filter.1 hj
    rcases hc with ⟨r, hr, hl⟩ | hh
    · refine mem_union_left _ (mem_biUnion.2 ⟨r, hr, mem_filter.2 ⟨mem_univ _, fun hro => hl ?_⟩⟩)
      exact stRobust_top hro hTop
    · refine mem_union_right _ (mem_filter.2 ⟨mem_univ _, ?_⟩)
      obtain ⟨h1, h2⟩ := hh
      have e : clamp01 (w s j) = w s j := by
        unfold clamp01 at h1 h2 ⊢
        rcases le_total (w s j) 1 with hx | hx
        · rw [min_eq_right hx] at h1 h2 ⊢
          rcases le_total 0 (w s j) with hy | hy
          · rw [max_eq_right hy]
          · rw [max_eq_left hy] at h1 h2; linarith
        · rw [min_eq_left hx, max_eq_right zero_le_one] at h1 h2; linarith
      rw [← e]; exact ⟨h1, h2⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  have hb : ((lt3Base s w).biUnion fun h => univ.filter fun j : Fin N => ¬ stRobust N k (w (flip h j))).card ≤
      (lt3Base s w).card * K :=
    card_biUnion_le.trans ((sum_le_sum fun h _ => (hrob h).le).trans (by rw [sum_const, smul_eq_mul]))
  have := hhalf.le
  nlinarith

/-- **Size of `Q`**: `|Top| - |Ex| ≤ 2^{|Base|} |Q|`. -/
theorem lt3_Q_card (s : State N) (ε γ : ℝ) (w : Param N) :
    (lt3Top s w ε).card - (lt3Ex s ε γ w).card ≤ 2 ^ (lt3Base s w).card * (lt3Q s ε γ w).card := by
  have h := (lt3QOf_spec (lt3Base s w) (lt3Top s w ε \ lt3Ex s ε γ w) (tcRow w)).2.1
  refine le_trans ?_ h
  exact le_card_sdiff _ _

open Classical in
/-- **Size of the kept family** (deterministic): if `|Top| ≤ k`, the dropped members are members with a non-robust
row `r^R`. -/
theorem lt3_F_card (s : State N) (ε γ : ℝ) (w : Param N) {k : ℕ} (hTop : (lt3Top s w ε).card ≤ k) :
    (qFam (lt3Q s ε γ w)).card ≤ (lt3F s ε γ w).card + ((qFam (lt3Q s ε γ w)).filter fun S =>
      ∃ r ∈ lt3Base s w, ∃ R ⊆ S, 2 ≤ R.card ∧ ¬ stRobust N k (w (flipS r R))).card := by
  have hsub : qFam (lt3Q s ε γ w) ⊆ lt3F s ε γ w ∪ (qFam (lt3Q s ε γ w)).filter fun S =>
      ∃ r ∈ lt3Base s w, ∃ R ⊆ S, 2 ≤ R.card ∧ ¬ stRobust N k (w (flipS r R)) := by
    intro S hS
    by_cases hk : S ∈ lt3F s ε γ w
    · exact mem_union_left _ hk
    · refine mem_union_right _ (mem_filter.2 ⟨hS, ?_⟩)
      unfold lt3F at hk
      simp only [mem_filter, not_and, not_forall] at hk
      obtain ⟨r, hr, R, hR, h2, hl⟩ := hk hS
      exact ⟨r, hr, R, hR, h2, fun hro => hl (stRobust_top hro hTop)⟩
  exact (card_le_card hsub).trans (card_union_le _ _)

lemma qFam_card_le_sq (Q : Finset (Fin N)) : (qFam Q).card ≤ N * N := by
  unfold qFam trFamily
  refine card_image_le.trans ?_
  rw [card_univ, Fintype.card_prod, Fintype.card_fin]
  have : qM Q ≤ N := by
    unfold qM; have := card_le_univ Q; rw [Fintype.card_fin] at this; omega
  exact Nat.mul_le_mul this this

/-- Sets of at most `b` elements: at most `(n+1)^b` of them. -/
lemma card_small_sets_le {α : Type*} [Fintype α] [DecidableEq α] (b : ℕ) :
    ((univ : Finset (Finset α)).filter fun B => B.card ≤ b).card ≤ (Fintype.card α + 1) ^ b := by
  classical
  have hsub : ((univ : Finset (Finset α)).filter fun B => B.card ≤ b) ⊆
      (univ : Finset (Fin b → Option α)).image fun g => (univ.image g).eraseNone := by
    intro B hB
    have hb := (mem_filter.1 hB).2
    let e := B.equivFin.symm
    refine mem_image.2 ⟨fun i => if h : i.val < B.card then some (e ⟨i.val, h⟩).1 else none, mem_univ _, ?_⟩
    ext x
    simp only [Finset.mem_eraseNone, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      split_ifs at hi with h
      · cases hi; exact (e ⟨i.val, h⟩).2
    · intro hx
      refine ⟨⟨(B.equivFin ⟨x, hx⟩).val, by have := (B.equivFin ⟨x, hx⟩).isLt; omega⟩, ?_⟩
      simp only [Fin.is_lt, dif_pos, Fin.eta, e, Equiv.symm_apply_apply]
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  rw [card_univ, Fintype.card_fun, Fintype.card_option, Fintype.card_fin]

/-- All admissible data with at most `b` base rows. -/
noncomputable def lt3Dat (N b : ℕ) : Finset (Finset (Fin N) × Finset (State N) × Finset (Finset (Fin N))) := by
  classical exact
    (((univ : Finset (Finset (Fin N))) ×ˢ ((univ : Finset (Finset (State N))).filter fun B => B.card ≤ b)).image
      fun p => (p.1, p.2, qFam p.1)).filter lt3Adm

lemma lt3Dat_card (b : ℕ) : (lt3Dat N b).card ≤ 2 ^ N * (2 ^ N + 1) ^ b := by
  classical
  unfold lt3Dat
  refine (card_filter_le _ _).trans (card_image_le.trans ?_)
  rw [card_product, card_univ, Fintype.card_finset, Fintype.card_fin]
  refine Nat.mul_le_mul_left _ ((card_small_sets_le b).trans ?_)
  simp

open Classical in
/-- **Member exclusion for the random family** (W2 6.2(e)). -/
theorem lt3_member_ev (s : State N) (ε γ : ℝ) {k : ℕ} (hN : 0 < N) (hk : 20 * k ≤ N) (b M : ℕ) :
    cubeM N {w | 7 ≤ (lt3Q s ε γ w).card ∧ (lt3Base s w).card ≤ b ∧
      M ≤ ((qFam (lt3Q s ε γ w)).filter fun S => ∃ r ∈ lt3Base s w, ∃ R ⊆ S, 2 ≤ R.card ∧
        ¬ stRobust N k (w (flipS r R))).card} ≤
      (lt3Dat N b).card * ENNReal.ofReal (((8 * b * (N * N)).choose M) *
        (N.choose k * Real.exp (-(44 / 100 * (N : ℝ)))) ^ M) := by
  refine (measure_mono fun w hw => ?_).trans (lt3_member_excl_union hN hk (lt3Dat N b)
    (fun d hd => (mem_filter.1 hd).2) (b := b) (f := N * N)
    (fun d hd => by
      obtain ⟨p, hp, rfl⟩ := mem_image.1 (mem_filter.1 hd).1
      exact (mem_filter.1 (mem_product.1 hp).2).2)
    (fun d hd => by
      obtain ⟨p, -, rfl⟩ := mem_image.1 (mem_filter.1 hd).1
      exact qFam_card_le_sq p.1) M)
  obtain ⟨h7, hb, hM⟩ := hw
  set Q := lt3Q s ε γ w
  have hspec := lt3QOf_spec (lt3Base s w) (lt3Top s w ε \ lt3Ex s ε γ w) (tcRow w)
  have hadm : lt3Adm (Q, lt3Base s w, qFam Q) :=
    ⟨h7, fun r hr r' hr' => agree_pair_tc (hspec.2.2 r hr) (hspec.2.2 r' hr'),
      fun S hS => qFam_sub hS, fun S hS => qFam_card_le hS, fun S hS S' hS' hne => qFam_inter hS hS' hne⟩
  refine ⟨(Q, lt3Base s w, qFam Q), mem_filter.2 ⟨mem_image.2 ⟨(Q, lt3Base s w),
    mem_product.2 ⟨mem_univ _, mem_filter.2 ⟨mem_univ _, hb⟩⟩, rfl⟩, hadm⟩, hM⟩

open Classical in
/-- **The member exclusion is `≤ e^{-2N}`** once `N` is large: `M ≥ N²/D`, `N/21 ≤ k ≤ N/20`,
`1 + log(8bD) + 100 ≤ 0.23N`, `((b+1) log 3 + 2) N ≤ 100 M`. -/
theorem lt3_member_ev_le (s : State N) (ε γ : ℝ) {k b M D : ℕ} (hD : 1 ≤ D) (hb : 1 ≤ b)
    (hk2 : N ≤ 21 * k) (hk1 : 20 * k ≤ N) (hM : N * N ≤ D * M)
    (hN1 : 1 + Real.log (8 * b * D) + 100 ≤ 23 / 100 * (N : ℝ))
    (hN2 : (((b : ℝ) + 1) * Real.log 3 + 2) * N ≤ 100 * M) :
    cubeM N {w | 7 ≤ (lt3Q s ε γ w).card ∧ (lt3Base s w).card ≤ b ∧
      M ≤ ((qFam (lt3Q s ε γ w)).filter fun S => ∃ r ∈ lt3Base s w, ∃ R ⊆ S, 2 ≤ R.card ∧
        ¬ stRobust N k (w (flipS r R))).card} ≤ ENNReal.ofReal (Real.exp (-(2 * (N : ℝ)))) := by
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; have := Real.log_nonneg (show (1 : ℝ) ≤ 8 * b * D by
        have : (1 : ℝ) ≤ b := by exact_mod_cast hb
        have : (1 : ℝ) ≤ D := by exact_mod_cast hD
        nlinarith)
      norm_num at hN1; linarith
    · exact h
  refine (lt3_member_ev s ε γ hNpos hk1 b M).trans ?_
  set p := (N.choose k : ℝ) * Real.exp (-(44 / 100 * (N : ℝ)))
  have hp0 : 0 ≤ p := by positivity
  have hp : p ≤ Real.exp (-(23 / 100 * (N : ℝ))) := st_robust_rate hk2 hk1
  have hDat : ((lt3Dat N b).card : ℝ) ≤ Real.exp (((b : ℝ) + 1) * Real.log 3 * N) := by
    have h1 : ((lt3Dat N b).card : ℝ) ≤ ((2 ^ N * (2 ^ N + 1) ^ b : ℕ) : ℝ) := by exact_mod_cast lt3Dat_card b
    have h2 : ((2 ^ N * (2 ^ N + 1) ^ b : ℕ) : ℝ) ≤ ((3 ^ N) ^ (b + 1) : ℕ) := by
      have a1 : 2 ^ N ≤ 3 ^ N := Nat.pow_le_pow_left (by norm_num) N
      have a2 : 2 ^ N + 1 ≤ 3 ^ N := by
        rcases Nat.eq_zero_or_pos N with h | h
        · omega
        · have : 2 ^ N < 3 ^ N := Nat.pow_lt_pow_left (by norm_num) (by omega)
          omega
      have : 2 ^ N * (2 ^ N + 1) ^ b ≤ (3 ^ N) ^ (b + 1) := by
        rw [pow_succ']; exact Nat.mul_le_mul a1 (Nat.pow_le_pow_left a2 b)
      exact_mod_cast this
    refine h1.trans (h2.trans (le_of_eq ?_))
    rw [show ((b : ℝ) + 1) * Real.log 3 * N = ((N * (b + 1) : ℕ) : ℝ) * Real.log 3 by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (by norm_num)]
    push_cast; ring
  have hc : ((8 * b * (N * N) : ℕ) : ℝ) ≤ (8 * b * D : ℝ) * M := by
    have : 8 * b * (N * N) ≤ 8 * b * D * M := by rw [mul_assoc (8 * b) D M]; exact Nat.mul_le_mul_left _ hM
    exact_mod_cast this
  have hrate := lt3_member_rate (b := b) (f := N * N) (M := M) (a := ((b : ℝ) + 1) * Real.log 3)
    (c := 8 * b * D) (by
      have : (1 : ℝ) ≤ b := by exact_mod_cast hb
      have : (1 : ℝ) ≤ D := by exact_mod_cast hD
      nlinarith) hDat hp0 hp (by exact_mod_cast hc) hN1 hN2
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hrate

end Census
end IIT
