/-
Census, B1 LTBetaHi, module T6 (part C, effect side): Lemma EFG and Lemma EF.

Everything is stated for a three-unit system `S` at the current state `s`, in the frame where the
designated effect state is all ON (`efgTop`); in the LTBetaHi application this is `flipP s w`.

* `effOff z s S = ∑_{r ∈ block(s) \ {s}} ∏_{j ∈ S} z r j`, the off-row effect mass.
* (EFG) `sysPhiE_pos_of_EFG`: if every row `r ≠ s` of the `S`-block is lowered by `κ` on the columns where it
  agrees with `s` (E2), the off-row mass is at most `B` (Σ), and every competitor `t` (some unit OFF) has
  `ln 2 · ii_e(t) ≤ ln 2 · 3 e - B` (E1), then `efgTop` is a maximal effect state and
  `φ_e ≥ e0 · log₂(1 / (1 - κ/2))` at every partition (`e0 ≤ e = ∏ z s j`).
  The budget enters through `ii_e(top) ≥ 3e - effOff / ln 2` (`efg_iiE_top_lower`).
* `effOff_le_desig`: (Σ) from one designated column per row (`Σ_r z r (desig r) ≤ B`).
* `efg_E1_of_eff_le`: (E1) without logs from `e(t) ≤ e_hi` and `B ≤ 3 ln 2 (e - e_hi)` (the
  non-suppressor cells of RL-tc).
* (EF) `tp_eff_gamma`: light `u`. Own entries `≥ 1/2 + γ`, private entries (`R ⊄ {i}`) `≤ ρ`, own flips
  `(s^i, i)` unconstrained, `7ρ ≤ 3 ln 2 · 2γ (1/2+γ)²`: `φ_e ≥ (1/2+γ)³ log₂(1/(1 - (1/2+γ-ρ)/2))`.
* `EFGHyp` packages exactly what the RL-tc certificate has to deliver for `u ∈ Sp_sig ∪ {tc}`;
  `efg_of_hyp` turns it into the effect conclusion. No certificate data is used in this file.
-/
import IIT.Census.ThmP3Eff

namespace IIT
namespace Census

open Finset

variable {N : ℕ}

/-- The all-ON state (the designated effect state, in the flipped frame). -/
def efgTop : State N := fun _ => true

/-- The off-row effect mass of the `S`-block of `s`. -/
noncomputable def effOff (z : Param N) (s : State N) (S : Finset (Fin N)) : ℝ :=
  ∑ r ∈ (agree Sᶜ s).erase s, ∏ j ∈ S, z r j

/-- `ii_e` at `t` only depends on `t` on `S`. -/
lemma efg_iiE_congr (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) {t t' : State N}
    (h : ∀ j ∈ S, t j = t' j) : sysIiE T S u s t = sysIiE T S u s t' := by
  have h1 : ∀ v, sysEffProb T S u v t = sysEffProb T S u v t' := fun v =>
    prod_congr rfl fun j hj => by rw [h j hj]
  simp only [sysIiE, sysUncEff, h1]

section EFG

variable {z : Param N} (hz : z ∈ openCube N) (s : State N) {S : Finset (Fin N)}

include hz

lemma efg_prob_top (r : State N) :
    ∏ j ∈ S, (tpmOf z).prob j r (efgTop j) = ∏ j ∈ S, z r j :=
  prod_congr rfl fun j _ => by rw [prob_of_mem hz]; simp [efgTop]

lemma efg_eff_top : sysEffProb (tpmOf z) S s s efgTop = ∏ j ∈ S, z s j := by
  rw [tp_eff_eq]; exact efg_prob_top hz s

lemma efg_unc_top :
    sysUncEff (tpmOf z) S s efgTop = (∏ j ∈ S, z s j + effOff z s S) / 2 ^ S.card := by
  rw [tp_unc_eq, ← sum_erase_add _ _ (tp_mem_block s S)]
  simp only [efg_prob_top hz, effOff]
  ring

lemma efg_e_pos : 0 < ∏ j ∈ S, z s j := prod_pos fun j _ => (hz s j).1

lemma effOff_nonneg : 0 ≤ effOff z s S :=
  sum_nonneg fun r _ => prod_nonneg fun j _ => (hz r j).1.le

/-- **The budget lower bound**: `ii_e(top) ≥ 3 e - effOff / ln 2`. -/
lemma efg_iiE_top_lower (hS : S.card = 3) :
    3 * ∏ j ∈ S, z s j - effOff z s S / Real.log 2 ≤ sysIiE (tpmOf z) S s s efgTop := by
  set e := ∏ j ∈ S, z s j with he
  set O := effOff z s S with hO
  have he0 : 0 < e := efg_e_pos hz s
  have hO0 : 0 ≤ O := effOff_nonneg hz s
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have heO : 0 < (e + O) / e := div_pos (by linarith) he0
  have hq : sysEffProb (tpmOf z) S s s efgTop / sysUncEff (tpmOf z) S s efgTop =
      8 / ((e + O) / e) := by
    rw [efg_eff_top hz, efg_unc_top hz, hS, ← he, ← hO]
    field_simp
    norm_num
  have hl : Real.log (8 / ((e + O) / e)) = 3 * Real.log 2 - Real.log ((e + O) / e) := by
    rw [Real.log_div (by norm_num) heO.ne', show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast; ring
  have hle : Real.log ((e + O) / e) ≤ O / e := by
    have := Real.log_le_sub_one_of_pos heO
    have h2 : (e + O) / e - 1 = O / e := by field_simp; ring
    linarith
  have heL : e * Real.log ((e + O) / e) ≤ O := by
    have := mul_le_mul_of_nonneg_left hle he0.le
    rwa [mul_div_cancel₀ _ he0.ne'] at this
  rw [sysIiE, hq, efg_eff_top hz, ← he, Real.logb, hl]
  have hrw : e * ((3 * Real.log 2 - Real.log ((e + O) / e)) / Real.log 2) =
      3 * e - e * Real.log ((e + O) / e) / Real.log 2 := by
    field_simp
  rw [hrw]
  have := div_le_div_of_nonneg_right heL hl2.le
  linarith

/-- **`efgTop` is a maximal effect state** under (Σ) and (E1). -/
theorem efg_top_mem (hS : S.card = 3) {B : ℝ} (hB : effOff z s S ≤ B)
    (hE1 : ∀ t : State N, (∃ j ∈ S, t j = false) →
      Real.log 2 * sysIiE (tpmOf z) S s s t ≤ Real.log 2 * (3 * ∏ j ∈ S, z s j) - B) :
    efgTop ∈ sysMaxEffStates (tpmOf z) S s s := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine mem_argmaxSet.2 fun t => ?_
  by_cases h : ∃ j ∈ S, t j = false
  · have h1 := hE1 t h
    have hlow := mul_le_mul_of_nonneg_left (efg_iiE_top_lower hz s hS) hl2.le
    have hrw : Real.log 2 * (3 * ∏ j ∈ S, z s j - effOff z s S / Real.log 2) =
        Real.log 2 * (3 * ∏ j ∈ S, z s j) - effOff z s S := by
      field_simp
    rw [hrw] at hlow
    exact le_of_mul_le_mul_left (by linarith) hl2
  · push Not at h
    refine le_of_eq (efg_iiE_congr _ _ _ _ fun j hj => ?_)
    have := h j hj
    simp only [efgTop]
    simpa using this

/-- One factor of the partitioned effect probability at `efgTop`, under (E2). -/
lemma efg_effUnit {κ : ℝ} (hκ : 0 ≤ κ)
    (hE2 : ∀ r ∈ agree Sᶜ s, r ≠ s → ∀ j ∈ S, r j = s j → z r j ≤ z s j - κ)
    {j : Fin N} (hj : j ∈ S) {M : Finset (Fin N)} (hM : M ⊆ S.erase j) :
    0 < effUnit (tpmOf z) Mᶜ s j true ∧ effUnit (tpmOf z) Mᶜ s j true ≤ z s j ∧
      (M.Nonempty → effUnit (tpmOf z) Mᶜ s j true ≤ z s j - κ / 2) := by
  have hP := prob_of_mem hz
  have hMS : M ⊆ S := hM.trans (erase_subset j S)
  have hjM : j ∉ M := fun h => (notMem_erase j S) (hM h)
  have hsub : agree Mᶜ s ⊆ agree Sᶜ s := agree_subset_agree (compl_subset_compl.2 hMS) s
  have hmem : s ∈ agree Mᶜ s := self_mem_agree _ _
  have hcard : (agree Mᶜ s).card = 2 ^ M.card := tp_card_block s M
  have hc0 : (0 : ℝ) < (agree Mᶜ s).card := by rw [hcard]; positivity
  have hc1 : (1 : ℝ) ≤ (agree Mᶜ s).card := by
    rw [hcard]; exact_mod_cast Nat.one_le_two_pow
  have hrow : ∀ r ∈ agree Mᶜ s, r ≠ s → z r j ≤ z s j - κ := fun r hr hrs =>
    hE2 r (hsub hr) hrs j hj ((mem_agree.1 hr) j (mem_compl.2 hjM))
  have hval : effUnit (tpmOf z) Mᶜ s j true = (∑ r ∈ agree Mᶜ s, z r j) / (agree Mᶜ s).card := by
    rw [effUnit]
    congr 1
    exact sum_congr rfl fun r _ => by rw [hP]; simp
  have hsplit := sum_erase_add (agree Mᶜ s) (fun r => z r j) hmem
  have hrest0 : 0 ≤ ∑ r ∈ (agree Mᶜ s).erase s, z r j :=
    sum_nonneg fun r _ => (hz r j).1.le
  have hrest : ∑ r ∈ (agree Mᶜ s).erase s, z r j ≤ ((agree Mᶜ s).card - 1) * (z s j - κ) := by
    calc ∑ r ∈ (agree Mᶜ s).erase s, z r j ≤ ∑ _r ∈ (agree Mᶜ s).erase s, (z s j - κ) :=
          sum_le_sum fun r hr => hrow r (mem_of_mem_erase hr) (ne_of_mem_erase hr)
      _ = ((agree Mᶜ s).card - 1) * (z s j - κ) := by
          rw [sum_const, card_erase_of_mem hmem, nsmul_eq_mul]
          rw [Nat.cast_sub (card_pos.2 ⟨s, hmem⟩)]
          simp
  rw [hval]
  refine ⟨div_pos (by rw [← hsplit]; linarith [(hz s j).1]) hc0, ?_, fun hne => ?_⟩
  · rw [div_le_iff₀ hc0, ← hsplit]
    nlinarith
  · have h2 : (2 : ℝ) ≤ (agree Mᶜ s).card := by
      rw [hcard]
      have : 1 ≤ M.card := card_pos.2 hne
      have : (2 : ℕ) ≤ 2 ^ M.card := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ M.card := Nat.pow_le_pow_right (by norm_num) this
      exact_mod_cast this
    rw [div_le_iff₀ hc0, ← hsplit]
    nlinarith

/-- **`φ_e` at `efgTop`** under (E2): at least `e0 · log₂(1/(1 - κ/2))` at every partition. -/
theorem efg_phiE {κ e0 : ℝ} (hκ : 0 ≤ κ) (hκ2 : κ < 2)
    (hE2 : ∀ r ∈ agree Sᶜ s, r ≠ s → ∀ j ∈ S, r j = s j → z r j ≤ z s j - κ)
    (he0 : e0 ≤ ∏ j ∈ S, z s j) (θ : SysPartition N S) :
    e0 * Real.logb 2 (1 / (1 - κ / 2)) ≤ sysPhiE (tpmOf z) S s θ s efgTop := by
  set T := tpmOf z
  have he : sysEffProb T S s s efgTop = ∏ j ∈ S, z s j := efg_eff_top hz s
  have hpe : sysPartEffProb T S s θ s efgTop =
      ∏ j ∈ S, effUnit T (θ.cutSet (θ.partOf j))ᶜ s j true := by
    rw [sysPartEffProb, merge_self]
    exact prod_congr rfl fun j _ => rfl
  have hfac := fun j (hj : j ∈ S) => efg_effUnit hz s hκ hE2 hj (cutSet_partOf_subset θ hj)
  obtain ⟨p, hp, hne⟩ := θ.exists_cutSet_nonempty
  obtain ⟨j0, hj0p⟩ := θ.parts_nonempty p hp
  have hj0 : j0 ∈ S := θ.parts_subset p hp hj0p
  rw [← θ.partOf_eq hp hj0p] at hne
  have hz0 := hz s j0
  have hrest0 : 0 ≤ ∏ j ∈ S.erase j0, z s j := prod_nonneg fun j _ => (hz s j).1.le
  have hk : 0 < 1 - κ / 2 := by linarith
  have hpe_le : sysPartEffProb T S s θ s efgTop ≤ (1 - κ / 2) * sysEffProb T S s s efgTop := by
    rw [hpe, he, ← mul_prod_erase S _ hj0, ← mul_prod_erase S (fun j => z s j) hj0]
    have hA := (hfac j0 hj0).2.2 hne
    have hB : ∏ j ∈ S.erase j0, effUnit T (θ.cutSet (θ.partOf j))ᶜ s j true ≤
        ∏ j ∈ S.erase j0, z s j :=
      prod_le_prod (fun j hj => (hfac j (mem_of_mem_erase hj)).1.le)
        fun j hj => (hfac j (mem_of_mem_erase hj)).2.1
    have hB0 : 0 ≤ ∏ j ∈ S.erase j0, effUnit T (θ.cutSet (θ.partOf j))ᶜ s j true :=
      prod_nonneg fun j hj => (hfac j (mem_of_mem_erase hj)).1.le
    have hA0 := (hfac j0 hj0).1
    calc effUnit T (θ.cutSet (θ.partOf j0))ᶜ s j0 true *
          ∏ j ∈ S.erase j0, effUnit T (θ.cutSet (θ.partOf j))ᶜ s j true
        ≤ (z s j0 - κ / 2) * ∏ j ∈ S.erase j0, z s j :=
          mul_le_mul hA hB hB0 (by linarith)
      _ ≤ (1 - κ / 2) * (z s j0 * ∏ j ∈ S.erase j0, z s j) := by
          nlinarith [mul_nonneg (mul_nonneg hκ hrest0) (by linarith [hz0.2] : (0 : ℝ) ≤ 1 - z s j0)]
  have hpe0 : 0 < sysPartEffProb T S s θ s efgTop := by
    rw [hpe]; exact prod_pos fun j hj => (hfac j hj).1
  have hratio : 1 / (1 - κ / 2) ≤ sysEffProb T S s s efgTop / sysPartEffProb T S s θ s efgTop := by
    rw [div_le_div_iff₀ hk hpe0]; linarith
  have hL0 : 0 ≤ Real.logb 2 (1 / (1 - κ / 2)) := by
    apply Real.logb_nonneg one_lt_two
    rw [le_div_iff₀ hk]; linarith
  have hL : Real.logb 2 (1 / (1 - κ / 2)) ≤
      pos (Real.logb 2 (sysEffProb T S s s efgTop / sysPartEffProb T S s θ s efgTop)) :=
    le_max_of_le_right (Real.logb_le_logb_of_le one_lt_two (by positivity) hratio)
  unfold sysPhiE
  rw [← he] at he0
  exact mul_le_mul he0 hL hL0 (sysEffProb_nonneg _ _ _ _ _)

/-- **Lemma EFG.** -/
theorem sysPhiE_pos_of_EFG (hS : S.card = 3) {κ B e0 : ℝ} (hκ : 0 ≤ κ) (hκ2 : κ < 2)
    (hE2 : ∀ r ∈ agree Sᶜ s, r ≠ s → ∀ j ∈ S, r j = s j → z r j ≤ z s j - κ)
    (hSig : effOff z s S ≤ B)
    (hE1 : ∀ t : State N, (∃ j ∈ S, t j = false) →
      Real.log 2 * sysIiE (tpmOf z) S s s t ≤ Real.log 2 * (3 * ∏ j ∈ S, z s j) - B)
    (he0 : e0 ≤ ∏ j ∈ S, z s j) :
    efgTop ∈ sysMaxEffStates (tpmOf z) S s s ∧
      ∀ θ : SysPartition N S, e0 * Real.logb 2 (1 / (1 - κ / 2)) ≤
        sysPhiE (tpmOf z) S s θ s efgTop :=
  ⟨efg_top_mem hz s hS hSig hE1, efg_phiE hz s hκ hκ2 hE2 he0⟩

/-- (Σ) from one designated column per off row. -/
lemma effOff_le_desig (desig : State N → Fin N)
    (hd : ∀ r ∈ (agree Sᶜ s).erase s, desig r ∈ S) :
    effOff z s S ≤ ∑ r ∈ (agree Sᶜ s).erase s, z r (desig r) :=
  sum_le_sum fun r hr => tp_prod_le_one_factor (f := fun j => z r j)
    (fun j _ => (hz r j).1.le) (fun j _ => (hz r j).2.le) (hd r hr)

omit hz in
/-- (E1) without logarithms: competitors have `e(t) ≤ e_hi` and `B ≤ 3 ln 2 (e - e_hi)`. -/
lemma efg_E1_of_eff_le (hS : S.card = 3) {B ehi : ℝ}
    (heff : ∀ t : State N, (∃ j ∈ S, t j = false) → sysEffProb (tpmOf z) S s s t ≤ ehi)
    (hB : B ≤ 3 * Real.log 2 * (∏ j ∈ S, z s j - ehi)) :
    ∀ t : State N, (∃ j ∈ S, t j = false) →
      Real.log 2 * sysIiE (tpmOf z) S s s t ≤ Real.log 2 * (3 * ∏ j ∈ S, z s j) - B := by
  intro t ht
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h1 := mul_le_mul_of_nonneg_left (tp_iiE_le (z := z) s hS t) hl2.le
  have h2 := mul_le_mul_of_nonneg_left (heff t ht) (by positivity : (0 : ℝ) ≤ 3 * Real.log 2)
  nlinarith

/-- Competitors lose a factor `(1/2-γ)/(1/2+γ)` when every own entry is `≥ 1/2 + γ`. -/
lemma efg_competitor {γ : ℝ} (hγ : 0 ≤ γ) (hown : ∀ j ∈ S, 1 / 2 + γ ≤ z s j)
    {t : State N} (ht : ∃ j ∈ S, t j = false) :
    (1 / 2 + γ) * sysEffProb (tpmOf z) S s s t ≤ (1 / 2 - γ) * ∏ j ∈ S, z s j := by
  obtain ⟨j0, hj0, hf⟩ := ht
  have hP := prob_of_mem hz
  rw [tp_eff_eq, ← mul_prod_erase S _ hj0, ← mul_prod_erase S (fun j => z s j) hj0, hP, hf]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hle : ∀ j ∈ S.erase j0, (tpmOf z).prob j s (t j) ≤ z s j := fun j hj => by
    have := hown j (mem_of_mem_erase hj)
    rw [hP]; split_ifs <;> linarith
  have hB := prod_le_prod (fun j _ => (tpmOf z).nonneg j s (t j)) hle
  have hB0 : 0 ≤ ∏ j ∈ S.erase j0, (tpmOf z).prob j s (t j) :=
    prod_nonneg fun j _ => (tpmOf z).nonneg j s (t j)
  have hz0 := hown j0 hj0
  have hz1 := (hz s j0).2
  have h1 : 0 ≤ 1 - z s j0 := by linarith
  calc (1 / 2 + γ) * ((1 - z s j0) * ∏ j ∈ S.erase j0, (tpmOf z).prob j s (t j))
      ≤ (1 / 2 + γ) * ((1 - z s j0) * ∏ j ∈ S.erase j0, z s j) := by
        have := mul_le_mul_of_nonneg_left hB h1
        nlinarith
    _ ≤ (1 / 2 - γ) * (z s j0 * ∏ j ∈ S.erase j0, z s j) := by
        have h0 : 0 ≤ ∏ j ∈ S.erase j0, z s j := prod_nonneg fun j _ => (hz s j).1.le
        nlinarith

/-- **Lemma EF (light `u`).** Own entries `≥ 1/2 + γ`; private entries (`(r, j)` with `r` flipped at some
`i ≠ j`, i.e. `R ⊄ {j}`) `≤ ρ`; the own flips `(s^i, i)` are unconstrained. -/
theorem tp_eff_gamma (hS : S.card = 3) {γ ρ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1 / 2) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1 / 2 + γ)
    (hown : ∀ j ∈ S, 1 / 2 + γ ≤ z s j)
    (hpriv : ∀ r ∈ agree Sᶜ s, r ≠ s → ∀ j ∈ S, (∃ i ∈ S, i ≠ j ∧ r i ≠ s i) → z r j ≤ ρ)
    (hB : 7 * ρ ≤ 3 * Real.log 2 * (2 * γ * (1 / 2 + γ) ^ 2)) :
    efgTop ∈ sysMaxEffStates (tpmOf z) S s s ∧
      ∀ θ : SysPartition N S, (1 / 2 + γ) ^ 3 * Real.logb 2 (1 / (1 - (1 / 2 + γ - ρ) / 2)) ≤
        sysPhiE (tpmOf z) S s θ s efgTop := by
  -- an off row differs from `s` somewhere on `S`
  have hdiff : ∀ r ∈ agree Sᶜ s, r ≠ s → ∃ i ∈ S, r i ≠ s i := by
    intro r hr hrs
    by_contra hc
    push Not at hc
    apply hrs
    funext k
    by_cases hk : k ∈ S
    · exact hc k hk
    · exact (mem_agree.1 hr) k (mem_compl.2 hk)
  set e := ∏ j ∈ S, z s j with he
  have he3 : (1 / 2 + γ) ^ 3 ≤ e := by
    have := prod_le_prod (s := S) (f := fun _ => (1 / 2 + γ : ℝ)) (g := fun j => z s j)
      (fun _ _ => by linarith) fun j hj => hown j hj
    rw [prod_const, hS] at this
    exact this
  -- (E2)
  have hE2 : ∀ r ∈ agree Sᶜ s, r ≠ s → ∀ j ∈ S, r j = s j →
      z r j ≤ z s j - (1 / 2 + γ - ρ) := by
    intro r hr hrs j hj hrj
    obtain ⟨i, hi, hri⟩ := hdiff r hr hrs
    have hij : i ≠ j := fun h => hri (h ▸ hrj)
    have := hpriv r hr hrs j hj ⟨i, hi, hij, hri⟩
    linarith [hown j hj]
  -- (Σ)
  have hSig : effOff z s S ≤ 7 * ρ := by
    have hc : ((agree Sᶜ s).erase s).card = 7 := by
      rw [card_erase_of_mem (tp_mem_block s S), tp_card_block, hS]; rfl
    calc effOff z s S ≤ ∑ _r ∈ (agree Sᶜ s).erase s, ρ := by
          refine sum_le_sum fun r hr => ?_
          have hr' := mem_of_mem_erase hr
          have hrs := ne_of_mem_erase hr
          obtain ⟨i, hi, hri⟩ := hdiff r hr' hrs
          have h2 : 1 < S.card := by rw [hS]; norm_num
          obtain ⟨j, hj, hji⟩ := exists_mem_ne h2 i
          have hle := tp_prod_le_one_factor (f := fun k => z r k)
            (fun k _ => (hz r k).1.le) (fun k _ => (hz r k).2.le) hj
          have := hpriv r hr' hrs j hj ⟨i, hi, fun h => hji h.symm, hri⟩
          exact hle.trans this
      _ = 7 * ρ := by rw [sum_const, hc]; simp
  -- (E1)
  have hE1 : ∀ t : State N, (∃ j ∈ S, t j = false) →
      Real.log 2 * sysIiE (tpmOf z) S s s t ≤ Real.log 2 * (3 * e) - 7 * ρ := by
    intro t ht
    have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hc := efg_competitor hz s hγ0 hown ht
    set et := sysEffProb (tpmOf z) S s s t with het
    have hgap : 2 * γ * (1 / 2 + γ) ^ 2 ≤ e - et := by
      have hpos : 0 < 1 / 2 + γ := by linarith
      refine le_of_mul_le_mul_left ?_ hpos
      have h1 := mul_le_mul_of_nonneg_left he3 (by linarith : (0 : ℝ) ≤ 2 * γ)
      nlinarith
    have h1 := mul_le_mul_of_nonneg_left (tp_iiE_le (z := z) s hS t) hl2.le
    have h2 := mul_le_mul_of_nonneg_left hgap (by positivity : (0 : ℝ) ≤ 3 * Real.log 2)
    nlinarith
  refine sysPhiE_pos_of_EFG hz s hS (by linarith) (by linarith) hE2 hSig hE1 he3

end EFG

/-- **What the RL-tc certificate must deliver** (for `u ∈ Sp_sig ∪ {tc}`), in the flipped frame: (E2) with a
slack `κ`, the off-row budget `B` through designated columns, (E1) against every competitor, and the effect
floor `e0`. In the application `κ = t/100` at `t = 1/80`, `e0 = 51/100`, and (E1) comes from
`efg_E1_of_eff_le` (492 cells) or from the suppressor log bounds (26 cells). -/
structure EFGHyp (z : Param N) (s : State N) (S : Finset (Fin N)) (κ B e0 : ℝ)
    (desig : State N → Fin N) : Prop where
  hκ : 0 ≤ κ
  hκ2 : κ < 2
  hE2 : ∀ r ∈ agree Sᶜ s, r ≠ s → ∀ j ∈ S, r j = s j → z r j ≤ z s j - κ
  hdesig : ∀ r ∈ (agree Sᶜ s).erase s, desig r ∈ S
  hSig : ∑ r ∈ (agree Sᶜ s).erase s, z r (desig r) ≤ B
  hE1 : ∀ t : State N, (∃ j ∈ S, t j = false) →
    Real.log 2 * sysIiE (tpmOf z) S s s t ≤ Real.log 2 * (3 * ∏ j ∈ S, z s j) - B
  he0 : e0 ≤ ∏ j ∈ S, z s j

/-- `EFGHyp` gives the effect conclusion needed by `tl_triple_lower_gen_t0`. -/
theorem efg_of_hyp {z : Param N} (hz : z ∈ openCube N) (s : State N) {S : Finset (Fin N)}
    (hS : S.card = 3) {κ B e0 : ℝ} {desig : State N → Fin N}
    (h : EFGHyp z s S κ B e0 desig) :
    ∃ te ∈ sysMaxEffStates (tpmOf z) S s s, ∀ θ : SysPartition N S,
      e0 * Real.logb 2 (1 / (1 - κ / 2)) ≤ sysPhiE (tpmOf z) S s θ s te :=
  let H := sysPhiE_pos_of_EFG hz s hS h.hκ h.hκ2 h.hE2
    ((effOff_le_desig hz s desig h.hdesig).trans h.hSig) h.hE1 h.he0
  ⟨efgTop, H.1, H.2⟩

end Census
end IIT
