/-
Census: an interior point of the region of `θ*` for the lower bound on `I_3`.

`θ*` has profile `C_0 = {2}`, `C_1 = {0, 2}`, `C_2 = {0, 1}` (`cd_Cstar`, normaliser `5`).  The
point `z = cd_zi / 2^24` and `u = cd_ui / cd_Du` satisfy `C_3 u = z` exactly and `⟨u, z⟩ ≤ 7.15`
(`cd_point_Cu`, `cd_point_q`), and every `ξ` in the sup-norm ball of radius `y / 20000` around `y z`
lies in the region `y P^δ` with `δ = 1/100`: the argmax rows are `≥ y`, `F_{θ*}(0) ≥ y`, and
`F_C(0)/cc(C) ≥ (1 + 1/100) F_{θ*}(0)/5` for every admissible profile `C ≠ θ*`
(`cd_point_ball`).  All inequalities are checked by the kernel on integers.
-/
import IIT.Census.CertDataEnum

namespace IIT
namespace Census

open Finset

set_option maxRecDepth 100000

/-- The profile of `θ*`. -/
def cd_Cstar : List (List Bool) := [[false, false, true], [true, false, true], [true, true, false]]

/-- Numerators of the point `z` (denominator `cd_Dz = 2^24`). -/
def cd_zi : List ℤ := [6978596, -360598, -3518025, -178744, 599905, -181854, -3339281, 0, 7040380, -2167013, -484166, -178744, -1916767, -1988269, -305422, 0, 6947704, -2136121, -2259689, -1954267, -110351, -181854, -305422, 0]

/-- The denominator of `z`. -/
def cd_Dz : ℕ := 16777216

/-- Numerators of `u = C_3^{-1} z` (denominator `cd_Du`). -/
def cd_ui : List ℤ := [102536821321620, -1950060, -58065238958850, 121695, 13593650472975, -864855, -58065237873645, 1206900, 103719309622500, -34573105084110, 812280, 121695, -34573111102065, -34573103998905, 1897485, 1206900, 101945577171180, -33981860933670, -33981858171330, -33981858861915, 11171055, -864855, 1897485, 1206900]

/-- The denominator of `u`. -/
def cd_Du : ℕ := 24918722084864

/-- The point `z`. -/
noncomputable def cd_z : Fin (3 * 2 ^ 3) → ℝ := fun p => (cd_zi.getD p 0 : ℝ) / cd_Dz

/-- The point `u`. -/
noncomputable def cd_u : Fin (3 * 2 ^ 3) → ℝ := fun p => (cd_ui.getD p 0 : ℝ) / cd_Du

/-- `∑_p c_p zi_p`. -/
def cd_dotz (c : ℕ → ℤ) : ℤ := cd_nsum 24 fun p => c p * cd_zi.getD p 0

/-- `∑_p |c_p|`. -/
def cd_abs (c : ℕ → ℤ) : ℤ := cd_nsum 24 fun p => |c p|

/-- A row `c` with `20000 (⟨c, zi⟩ - a Dz) ≥ Dz ∑|c|` stays `≥ a y` on the ball. -/
def cd_rowMargin (c : ℕ → ℤ) (a : ℤ) : Bool :=
  decide ((cd_Dz : ℤ) * cd_abs c ≤ 20000 * (cd_dotz c - a * cd_Dz))

/-- The scaled ratio row `100 cc(θ*) F_C - 101 cc(C) F_{θ*}` (times `2^3`). -/
def cd_ratioRow (C : List (List Bool)) (p : ℕ) : ℤ :=
  100 * (cd_cc 3 cd_Cstar : ℤ) * cd_fz 3 C 0 p - 101 * (cd_cc 3 C : ℤ) * cd_fz 3 cd_Cstar 0 p

/-- The kernel check of the point. -/
def cd_pointCheck : Bool :=
  (List.range 24).all (fun p => (cd_Dz : ℤ) * cd_nsum 24 (fun q => cd_Cz 3 p q * cd_ui.getD q 0)
      == 1920 * (cd_Du : ℤ) * cd_zi.getD p 0) &&
  decide (100 * cd_nsum 24 (fun p => cd_ui.getD p 0 * cd_zi.getD p 0) ≤ 715 * (cd_Du : ℤ) * cd_Dz) &&
  (List.range 8).all (fun t => t == 0 || cd_rowMargin (cd_argc 3 t) 1) &&
  cd_rowMargin (cd_fz 3 cd_Cstar 0) 8 &&
  (cd_gen 3).all (fun x => cd_profOf 3 x.1 x.2 == cd_Cstar ||
      (decide (0 < cd_cc 3 (cd_profOf 3 x.1 x.2)) && cd_rowMargin (cd_ratioRow (cd_profOf 3 x.1 x.2)) 0))

theorem cd_pointCheck_ok : cd_pointCheck = true := by decide +kernel

lemma cd_Dz_pos : (0 : ℝ) < cd_Dz := by norm_num [cd_Dz]

lemma cd_Du_pos : (0 : ℝ) < cd_Du := by norm_num [cd_Du]

lemma cd_sum24 (f : ℕ → ℝ) : ∑ p : Fin (3 * 2 ^ 3), f p = ∑ p ∈ range 24, f p :=
  Fin.sum_univ_eq_sum_range f 24

/-- `C_3 u = z`. -/
theorem cd_point_Cu : ∀ p, ∑ q, gg_C 3 p q * cd_u q = cd_z p := by
  have h := cd_pointCheck_ok
  simp only [cd_pointCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hC := h.1.1.1.1
  intro p
  have e := hC p p.2
  rw [cd_nsum_eq] at e
  have e' : (cd_Dz : ℝ) * ∑ q ∈ range 24, (cd_Cz 3 p q : ℝ) * (cd_ui.getD q 0 : ℝ)
      = 1920 * cd_Du * (cd_zi.getD p 0 : ℝ) := by exact_mod_cast e
  have hsum : ∑ q : Fin (3 * 2 ^ 3), gg_C 3 p q * cd_u q
      = (∑ q : Fin (3 * 2 ^ 3), (cd_Cz 3 p q : ℝ) * (cd_ui.getD q 0 : ℝ)) / (1920 * cd_Du) := by
    rw [sum_div]
    refine sum_congr rfl fun q _ => ?_
    rw [cd_Cz_cast, cd_u]
    have := cd_Du_pos
    field_simp
    ring
  rw [hsum, cd_sum24 (fun q => (cd_Cz 3 p q : ℝ) * (cd_ui.getD q 0 : ℝ)), cd_z]
  have := cd_Du_pos
  have := cd_Dz_pos
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linarith

/-- `⟨u, z⟩ = zᵀ C_3⁻¹ z ≤ 7.15`. -/
theorem cd_point_q : ∑ p, cd_u p * cd_z p ≤ 715 / 100 := by
  have h := cd_pointCheck_ok
  simp only [cd_pointCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have e := h.1.1.1.2
  rw [cd_nsum_eq] at e
  have e' : 100 * ∑ p ∈ range 24, (cd_ui.getD p 0 : ℝ) * (cd_zi.getD p 0 : ℝ)
      ≤ 715 * (cd_Du : ℝ) * cd_Dz := by exact_mod_cast e
  have hs : ∑ p : Fin (3 * 2 ^ 3), cd_u p * cd_z p
      = (∑ p ∈ range 24, (cd_ui.getD p 0 : ℝ) * (cd_zi.getD p 0 : ℝ)) / (cd_Du * cd_Dz) := by
    rw [← cd_sum24 (fun p => (cd_ui.getD p 0 : ℝ) * (cd_zi.getD p 0 : ℝ)), sum_div]
    refine sum_congr rfl fun p _ => ?_
    simp only [cd_u, cd_z]
    field_simp
  rw [hs, div_le_iff₀ (by have := cd_Du_pos; have := cd_Dz_pos; positivity)]
  linarith

/-- Perturbation of a row on the ball. -/
lemma cd_row_ball (c : ℕ → ℤ) (a : ℤ) (h : cd_rowMargin c a = true) {y : ℝ} (hy : 0 ≤ y)
    (ξ : Fin (3 * 2 ^ 3) → ℝ) (hξ : ∀ p, |ξ p - y * cd_z p| ≤ y / 20000) :
    (a : ℝ) * y ≤ cd_lin 3 c ξ := by
  simp only [cd_rowMargin, decide_eq_true_eq, cd_abs, cd_dotz, cd_nsum_eq] at h
  have h' : (cd_Dz : ℝ) * ∑ p ∈ range 24, |(c p : ℝ)|
      ≤ 20000 * (∑ p ∈ range 24, (c p : ℝ) * (cd_zi.getD p 0 : ℝ) - a * cd_Dz) := by
    have := (Int.cast_le (R := ℝ)).2 h
    push_cast at this
    exact this
  have hz : cd_lin 3 c (fun p => y * cd_z p)
      = y * (∑ p ∈ range 24, (c p : ℝ) * (cd_zi.getD p 0 : ℝ)) / cd_Dz := by
    unfold cd_lin
    simp only [cd_z]
    rw [cd_sum24 (fun p => (c p : ℝ) * (y * ((cd_zi.getD p 0 : ℝ) / cd_Dz))), mul_sum, sum_div]
    refine sum_congr rfl fun p _ => ?_
    field_simp
  have hd : |cd_lin 3 c ξ - cd_lin 3 c (fun p => y * cd_z p)|
      ≤ (∑ p ∈ range 24, |(c p : ℝ)|) * (y / 20000) := by
    unfold cd_lin
    rw [← sum_sub_distrib, ← cd_sum24 (fun p => |(c p : ℝ)|), sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ => ?_)
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (hξ p) (abs_nonneg _)
  have hDz := cd_Dz_pos
  have key : (a : ℝ) * y + (∑ p ∈ range 24, |(c p : ℝ)|) * (y / 20000)
      ≤ cd_lin 3 c (fun p => y * cd_z p) := by
    rw [hz, ← sub_nonneg]
    have e : y * (∑ p ∈ range 24, (c p : ℝ) * (cd_zi.getD p 0 : ℝ)) / cd_Dz
        - ((a : ℝ) * y + (∑ p ∈ range 24, |(c p : ℝ)|) * (y / 20000))
        = y / (20000 * cd_Dz) * (20000 * (∑ p ∈ range 24, (c p : ℝ) * (cd_zi.getD p 0 : ℝ) - a * cd_Dz)
          - cd_Dz * ∑ p ∈ range 24, |(c p : ℝ)|) := by
      field_simp
      ring
    rw [e]
    exact mul_nonneg (div_nonneg hy (by positivity)) (sub_nonneg.2 h')
  have := (abs_le.1 hd).1
  linarith

/-- **The ball around `y z` lies in `y P^δ`** (`δ = 1/100`) for the profile of `θ*`. -/
theorem cd_point_ball {y : ℝ} (hy : 0 ≤ y) (ξ : Fin (3 * 2 ^ 3) → ℝ)
    (hξ : ∀ p, |ξ p - y * cd_z p| ≤ y / 20000) :
    (∀ t : ℕ, 0 < t → t < 2 ^ 3 → y ≤ cd_lin 3 (cd_argc 3 t) ξ) ∧
    y ≤ cd_F 3 cd_Cstar 0 ξ ∧
    ∀ g δ : List ℕ, cd_valid 3 g δ = true → cd_profOf 3 g δ ≠ cd_Cstar →
      (1 + 1 / 100) * (cd_F 3 cd_Cstar 0 ξ / cd_cc 3 cd_Cstar)
        ≤ cd_F 3 (cd_profOf 3 g δ) 0 ξ / cd_cc 3 (cd_profOf 3 g δ) := by
  have h := cd_pointCheck_ok
  simp only [cd_pointCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq] at h
  obtain ⟨⟨⟨_, hargs⟩, hF⟩, hmins⟩ := h
  refine ⟨fun t ht1 ht2 => ?_, ?_, fun g δ hv hne => ?_⟩
  · rcases hargs t ht2 with h0 | ha
    · omega
    · simpa using cd_row_ball _ 1 ha hy ξ hξ
  · have := cd_row_ball _ 8 hF hy ξ hξ
    rw [cd_F, le_div_iff₀ (by positivity)]
    push_cast at this
    linarith
  · rcases hmins _ (cd_mem_gen hv) with h1 | ⟨hcc, h2⟩
    · exact absurd h1 hne
    · simp only [decide_eq_true_eq] at hcc
      have hr := cd_row_ball _ 0 h2 hy ξ hξ
      simp only [Int.cast_zero, zero_mul] at hr
      have er : cd_ratioRow (cd_profOf 3 g δ) = fun p =>
          (100 * (cd_cc 3 cd_Cstar : ℤ)) * cd_fz 3 (cd_profOf 3 g δ) 0 p
          - (101 * (cd_cc 3 (cd_profOf 3 g δ) : ℤ)) * cd_fz 3 cd_Cstar 0 p := rfl
      rw [er, cd_lin_sub, cd_lin_smul, cd_lin_smul] at hr
      have h5 : (cd_cc 3 cd_Cstar : ℝ) = 5 := by
        have : cd_cc 3 cd_Cstar = 5 := by decide
        exact_mod_cast this
      have hc : (0 : ℝ) < cd_cc 3 (cd_profOf 3 g δ) := by exact_mod_cast hcc
      push_cast at hr
      rw [h5] at hr
      simp only [cd_F]
      rw [h5, div_div, div_div, le_div_iff₀ (by positivity)]
      have e : (1 + 1 / 100 : ℝ) * (cd_lin 3 (cd_fz 3 cd_Cstar 0) ξ / (2 ^ 3 * 5))
          * (2 ^ 3 * (cd_cc 3 (cd_profOf 3 g δ) : ℝ))
          = (101 * (cd_cc 3 (cd_profOf 3 g δ) : ℝ) * cd_lin 3 (cd_fz 3 cd_Cstar 0) ξ) / 500 := by
        field_simp
        ring
      rw [e, div_le_iff₀ (by norm_num)]
      nlinarith

end Census
end IIT
