/-
Census, Theorem E (upper bounds for the sizes `k ≠ 3`, `2 ≤ k ≤ 21`).

For every sequence of current states, with probability tending to one over the cube, no candidate
of size `k` has `φ_s > c_k √(ln N) σ_N`, where
`c_2 = 0.21`, `c_4 = 0.26`, `c_5 = 0.17` (certified Gaussian rates of `CertData2/4/5`) and
`c_k = 0.28` for every `k ≥ 6` (single cut).  All these constants are at most `0.2896`, so with
probability tending to one no candidate of size in `{2, 4, 5, …, 21}` has
`φ_s > 0.2896 √(ln N) σ_N` (`te_thmE_union`).
-/
import IIT.Census.ThmECut

namespace IIT
namespace Census

open MeasureTheory Finset Filter Topology

noncomputable section

/-- The constants `c_k`. -/
def te_ck (k : ℕ) : ℝ :=
  if k = 2 then 21 / 100 else if k = 4 then 26 / 100 else if k = 5 then 17 / 100 else 28 / 100

lemma te_ck_le (k : ℕ) : te_ck k ≤ 2896 / 10000 := by
  unfold te_ck; split_ifs <;> norm_num

lemma te_ck_nonneg (k : ℕ) : 0 ≤ te_ck k := by
  unfold te_ck; split_ifs <;> norm_num

/-- **Theorem E, `k = 2`** (level `0.2056`, rate `I₂ = 2560/61`). -/
theorem te_thmE_k2 (s : ∀ N, State N) :
    Tendsto (fun N => volume {z | z ∈ cube N ∧ ∃ S : Finset (Fin N), S.card = 2 ∧
      21 / 100 * Real.sqrt (Real.log N) * sigN N < phi z (s N) S}) atTop (𝓝 0) := by
  refine te_thmE_cert (Ln := 7999992) (Ld := 190625) (by norm_num) cd_W2_ok cd_k2_covered
    (by norm_num) (by norm_num) (l := 5 / 16) (by norm_num) ?_ (by norm_num) s
  unfold te_kap bg_ak
  have := Real.log_two_gt_d9
  norm_num
  linarith

/-- **Theorem E, `k = 4`** (level `0.2539`, certified rate `3.8733`). -/
theorem te_thmE_k4 (s : ∀ N, State N) :
    Tendsto (fun N => volume {z | z ∈ cube N ∧ ∃ S : Finset (Fin N), S.card = 4 ∧
      26 / 100 * Real.sqrt (Real.log N) * sigN N < phi z (s N) S}) atTop (𝓝 0) := by
  refine te_thmE_cert (Ln := 38733) (Ld := 10000) (by norm_num) cd_W4_ok cd_k4_covered
    (by norm_num) (by norm_num) (l := 146 / 100) (by norm_num) ?_ (by norm_num) s
  unfold te_kap bg_ak
  have := Real.log_two_gt_d9
  norm_num
  linarith

/-- **Theorem E, `k = 5`** (level `0.1659`, certified rate `2.8923`). -/
theorem te_thmE_k5 (s : ∀ N, State N) :
    Tendsto (fun N => volume {z | z ∈ cube N ∧ ∃ S : Finset (Fin N), S.card = 5 ∧
      17 / 100 * Real.sqrt (Real.log N) * sigN N < phi z (s N) S}) atTop (𝓝 0) := by
  refine te_thmE_cert (Ln := 28923) (Ld := 10000) (by norm_num) cd_W5_ok cd_k5_covered
    (by norm_num) (by norm_num) (l := 19 / 10) (by norm_num) ?_ (by norm_num) s
  unfold te_kap bg_ak
  have := Real.log_two_gt_d9
  norm_num
  linarith

/-- **Theorem E for every size `k ∈ {2, 4, 5, …, 21}`** with the constant `c_k = te_ck k`. -/
theorem te_thmE (s : ∀ N, State N) {k : ℕ} (hk2 : 2 ≤ k) (hk21 : k ≤ 21) (hk3 : k ≠ 3) :
    Tendsto (fun N => volume {z | z ∈ cube N ∧ ∃ S : Finset (Fin N), S.card = k ∧
      te_ck k * Real.sqrt (Real.log N) * sigN N < phi z (s N) S}) atTop (𝓝 0) := by
  have _ := hk21
  by_cases h2 : k = 2
  · subst h2; simpa [te_ck] using te_thmE_k2 s
  by_cases h4 : k = 4
  · subst h4; simpa [te_ck] using te_thmE_k4 s
  by_cases h5 : k = 5
  · subst h5; simpa [te_ck] using te_thmE_k5 s
  have h6 : 6 ≤ k := by omega
  have hc : te_ck k = 28 / 100 := by simp [te_ck, h2, h4, h5]
  rw [hc]
  exact te_thmE_cut h6 s

/-- **Theorem E, combined.** With probability tending to one, no candidate `S` with
`2 ≤ |S| ≤ 21`, `|S| ≠ 3` has `φ_s(S) > 0.2896 √(ln N) σ_N`. -/
theorem te_thmE_union (s : ∀ N, State N) :
    Tendsto (fun N => volume {z | z ∈ cube N ∧ ∃ S : Finset (Fin N), 2 ≤ S.card ∧
      S.card ≤ 21 ∧ S.card ≠ 3 ∧
      2896 / 10000 * Real.sqrt (Real.log N) * sigN N < phi z (s N) S}) atTop (𝓝 0) := by
  set K : Finset ℕ := (Icc 2 21).erase 3 with hK
  have hmem : ∀ k ∈ K, 2 ≤ k ∧ k ≤ 21 ∧ k ≠ 3 := by
    intro k hk
    rw [hK, mem_erase, mem_Icc] at hk
    exact ⟨hk.2.1, hk.2.2, hk.1⟩
  have hsum := tendsto_finsetSum K fun k hk =>
    te_thmE s (hmem k hk).1 (hmem k hk).2.1 (hmem k hk).2.2
  simp only [sum_const_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) fun N => ?_
  have hsub : {z | z ∈ cube N ∧ ∃ S : Finset (Fin N), 2 ≤ S.card ∧ S.card ≤ 21 ∧
      S.card ≠ 3 ∧ 2896 / 10000 * Real.sqrt (Real.log N) * sigN N < phi z (s N) S} ⊆
      ⋃ k ∈ K, {z | z ∈ cube N ∧ ∃ S : Finset (Fin N), S.card = k ∧
        te_ck k * Real.sqrt (Real.log N) * sigN N < phi z (s N) S} := by
    rintro z ⟨hz, S, h2, h21, h3, hphi⟩
    simp only [Set.mem_iUnion]
    refine ⟨S.card, by rw [hK, mem_erase, mem_Icc]; exact ⟨h3, h2, h21⟩, hz, S, rfl, ?_⟩
    have hX : 0 ≤ Real.sqrt (Real.log N) * sigN N := by
      have := sigN_pos N; positivity
    have := te_ck_le S.card
    calc te_ck S.card * Real.sqrt (Real.log N) * sigN N
        = te_ck S.card * (Real.sqrt (Real.log N) * sigN N) := by ring
      _ ≤ 2896 / 10000 * (Real.sqrt (Real.log N) * sigN N) := mul_le_mul_of_nonneg_right this hX
      _ = 2896 / 10000 * Real.sqrt (Real.log N) * sigN N := by ring
      _ < phi z (s N) S := hphi
  exact (measure_mono hsub).trans (measure_biUnion_finset_le _ _)

end

end Census
end IIT
