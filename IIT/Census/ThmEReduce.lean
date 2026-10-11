/-
Census, Theorem E: the deterministic reduction and the relabelling of functionals.

`te_reduce`: in the open cube, off the field event and the effect event, if a `k`-set `S` has
`φ_s(S) > c √(ln N) σ_N` (and `3 η_N ≤ a_k`), then for some ordering `e` of `S` there are a
pattern `t` and a partition `θ` with the near-argmax and near-minimiser conditions of
`ur_upper_reduce` (shift `e_N`) and `F_θ(t) ≥ y_N`.

Also: a functional of the translated field is a functional of the field with the same quadratic
form (`te_sum_sh`, `te_quad_relabel`), `C_k` is positive definite (`te_quad_pos`), and flipped
events have probability at most that of the event (`te_volume_flip_le`).
-/
import IIT.Census.ThmEBad

namespace IIT
namespace Census

open MeasureTheory Finset Filter Topology

noncomputable section

variable {N k : ℕ}

/-! ### Relabelling functionals -/

/-- The pattern translation as a permutation of the coordinates. -/
def te_pi (k : ℕ) (u0 : Fin (2 ^ k)) : Equiv.Perm (Fin (k * 2 ^ k)) :=
  gg_relabel k (Equiv.refl _) (gg_xor k u0)

lemma te_sum_sh (u0 : Fin (2 ^ k)) (v ξ : Fin (k * 2 ^ k) → ℝ) :
    ∑ p, v p * te_sh u0 ξ p = ∑ q, v ((te_pi k u0).symm q) * ξ q := by
  have h := Equiv.sum_comp (te_pi k u0) (fun q => v ((te_pi k u0).symm q) * ξ q)
  simp only [Equiv.symm_apply_apply] at h
  rw [← h]
  rfl

lemma te_C_relabel (τ : Equiv.Perm (Fin k)) (ψ : Equiv.Perm (Fin (2 ^ k)))
    (p q : Fin (k * 2 ^ k)) :
    gg_C k (gg_relabel k τ ψ p) (gg_relabel k τ ψ q) = gg_C k p q := by
  rw [gg_C, gg_C, gg_pat_relabel, gg_pat_relabel]
  simp only [ψ.injective.eq_iff, (gg_relabel k τ ψ).injective.eq_iff]

lemma te_quad_relabel (u0 : Fin (2 ^ k)) (v : Fin (k * 2 ^ k) → ℝ) :
    gg_quad (gg_C k) (fun q => v ((te_pi k u0).symm q)) = gg_quad (gg_C k) v := by
  unfold gg_quad
  rw [← Equiv.sum_comp (te_pi k u0)]
  refine sum_congr rfl fun p _ => ?_
  rw [← Equiv.sum_comp (te_pi k u0)]
  refine sum_congr rfl fun q _ => ?_
  simp only [Equiv.symm_apply_apply]
  rw [te_pi, te_C_relabel]

lemma te_sumabs_relabel (u0 : Fin (2 ^ k)) (v : Fin (k * 2 ^ k) → ℝ) :
    ∑ q, |v ((te_pi k u0).symm q)| = ∑ p, |v p| :=
  Equiv.sum_comp (te_pi k u0).symm (fun p => |v p|)

/-- `vᵀ C_k v ≥ c₂ ∑ v²`. -/
lemma te_quad_ge (v : Fin (k * 2 ^ k) → ℝ) : gg_c2 k * ∑ p, v p ^ 2 ≤ gg_quad (gg_C k) v := by
  rw [cd_quad_C]
  have h0 := gg_c0_pos k
  have h1 := gg_c1_pos k
  have : 0 ≤ gg_c0 k * (∑ p, v p) ^ 2 := by positivity
  have : 0 ≤ gg_c1 k * ∑ t : Fin (2 ^ k), (∑ i : Fin k, v (cd_idx k i t)) ^ 2 := by
    have : 0 ≤ ∑ t : Fin (2 ^ k), (∑ i : Fin k, v (cd_idx k i t)) ^ 2 :=
      sum_nonneg fun _ _ => sq_nonneg _
    positivity
  linarith

/-- `C_k` is positive definite. -/
lemma te_quad_pos {v : Fin (k * 2 ^ k) → ℝ} (hv : v ≠ 0) : 0 < gg_quad (gg_C k) v := by
  obtain ⟨p, hp⟩ : ∃ p, v p ≠ 0 := by
    by_contra h; push Not at h; exact hv (funext h)
  have hs : 0 < ∑ q, v q ^ 2 :=
    lt_of_lt_of_le (by positivity) (single_le_sum (fun q _ => sq_nonneg (v q)) (mem_univ p))
  exact lt_of_lt_of_le (mul_pos (gg_c2_pos k) hs) (te_quad_ge v)

/-! ### Flipped events -/

lemma te_volume_flip_le (s : State N) (Q : Param N → Prop) :
    volume {z | z ∈ cube N ∧ Q (flipP s z)} ≤ cubeM N {w | Q w} := by
  have hsub : {z | z ∈ cube N ∧ Q (flipP s z)} ⊆ flipE s ⁻¹' (cube N ∩ {w | Q w}) := by
    rintro z ⟨hz, hQ⟩
    exact ⟨flipP_cube hz s, hQ⟩
  calc volume {z | z ∈ cube N ∧ Q (flipP s z)}
      ≤ volume (flipE s ⁻¹' (cube N ∩ {w | Q w})) := measure_mono hsub
    _ = cubeM N {w | Q w} := by
        rw [(mp_flipE s).measure_preimage_equiv, volume_cube_inter]

/-! ### The deterministic reduction -/

/-- **Reduction.** In the open cube, off the field and effect events, a `k`-set with
`φ_s(S) > c √(ln N) σ_N` has an ordering `e` with a near-argmax pattern `t`, a near-minimiser
`θ`, and `F_θ(t) ≥ y_N`. -/
theorem te_reduce {s : State N} {z : Param N} (hz : z ∈ openCube N) {S : Finset (Fin N)}
    (hSk : S.card = k) {c : ℝ} (hc : 0 ≤ c) (h3 : 3 * te_eta N ≤ bg_ak k)
    (hfield : flipP s z ∉ te_fieldBad k N) (heff : z ∉ te_effBad k N s)
    (hphi : c * Real.sqrt (Real.log N) * sigN N < phi z s S) :
    ∃ e : Fin k ↪ Fin N, bg_U e = S ∧ ∃ (θ : SysPartition N S) (t : State N),
      (∀ t', ur_xi (flipP s z) S (bg_ak k) (sigN N) t' ≤
        ur_xi (flipP s z) S (bg_ak k) (sigN N) t + te_e k N) ∧
      (∀ θ' : SysPartition N S, ur_F (flipP s z) θ t (sigN N) / (sysCutCount θ : ℝ) ≤
        ur_F (flipP s z) θ' t (sigN N) / (sysCutCount θ' : ℝ) + te_e k N) ∧
      te_y k c N ≤ ur_F (flipP s z) θ t (sigN N) := by
  obtain ⟨e, hSe⟩ : ∃ e : Fin k ↪ Fin N, bg_U e = S :=
    ⟨(S.orderEmbOfFin hSk).toEmbedding, by rw [bg_U]; exact image_orderEmbOfFin_univ S hSk⟩
  refine ⟨e, hSe, ?_⟩
  subst hSe
  set w := flipP s z with hw
  have hσ := sigN_pos N
  have hA := te_ak_ge k
  have hη0 := te_eta_nonneg N
  have hM : ∀ p, |te_xi e.injective w p| ≤ N := by
    intro p
    by_contra h
    exact hfield ⟨e, p, not_le.1 h⟩
  have hlev : ∀ Y ⊆ bg_U e, ∀ t, ∀ i ∈ bg_U e, |Num w (bg_U e) Y t i - bg_ak k| ≤ te_eta N := by
    intro Y hY t i hi
    have := te_lev e.injective w hM Y hY t i hi
    rw [te_eta]; linarith [mul_comm (sigN N) (N : ℝ)]
  have hX : 0 ≤ c * Real.sqrt (Real.log N) * sigN N := by positivity
  have hcard : (bg_U e).card = k := bg_card_U e.injective
  rcases ur_upper_reduce hz s hη0 h3 (by linarith) hσ hX hlev hphi with
    ⟨t, θ, hmax, hmin, hXF⟩ | ⟨te, _, θ, hX1, hX2⟩
  · refine ⟨θ, t, ?_, ?_, ?_⟩
    · intro t'; have h := hmax t'; rw [hcard] at h; exact h
    · intro θ'; have h := hmin θ'; rw [hcard] at h; exact h
    · rw [hcard] at hXF
      have hρ : 0 < ur_rho k (bg_ak k) (te_eta N) := by
        unfold ur_rho
        have : 0 < bg_ak k - te_eta N := by linarith
        positivity
      have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      have hpre : 0 < ur_rho k (bg_ak k) (te_eta N) / 2 ^ k * (sigN N / (bg_ak k * Real.log 2)) :=
        by positivity
      unfold te_y te_kap te_e te_rho
      set F := ur_F w θ t (sigN N)
      set E := ur_err k (bg_ak k) (te_eta N) (sigN N)
      set R := ur_rho k (bg_ak k) (te_eta N)
      have key : c * Real.sqrt (Real.log N) * (2 ^ k * bg_ak k * Real.log 2) / R < F + E := by
        rw [div_lt_iff₀ hρ]
        have e1 : R / 2 ^ k * (sigN N / (bg_ak k * Real.log 2)) * (F + E) * (2 ^ k * bg_ak k *
            Real.log 2 / sigN N) = (F + E) * R := by
          field_simp
        have h2 : 0 < 2 ^ k * bg_ak k * Real.log 2 / sigN N := by positivity
        have := mul_lt_mul_of_pos_right hXF h2
        rw [e1] at this
        calc c * Real.sqrt (Real.log N) * (2 ^ k * bg_ak k * Real.log 2)
            = c * Real.sqrt (Real.log N) * sigN N * (2 ^ k * bg_ak k * Real.log 2 / sigN N) := by
              field_simp
          _ < (F + E) * R := this
      linarith
  · exfalso
    rw [hcard] at hX1 hX2
    refine heff ⟨hz, bg_U e, hcard, θ, te, ?_, ?_⟩
    · by_contra hle
      push Not at hle
      have : (k : ℝ) ^ 2 * sysPhiE (tpmOf z) (bg_U e) s θ s te ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hle
      linarith
    · unfold te_del te_rho
      exact hX2

end

end Census
end IIT
