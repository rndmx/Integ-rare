/-
Census: soundness of the half-space certificates of `ThmP3Cert`.

A passing certificate `v` for the relabellings `s0, s1` gives, with `S = ⟨v, Δz⟩ / 2^24 > 0`:
`J vᵀ Δᵀ C_J Δ v ≤ S²`, and `⟨v, x⟩ ≥ S (y - 3 r)` for every `x` within `r` (sup norm) of the
scaled joint relabelled difference `y Δz` (`tp_hcheck_sound`).
-/
import IIT.Census.ThmP3Cert

namespace IIT
namespace Census

open Finset

lemma tp_tab1_all : ∀ s0 ∈ tp_plist, ∀ s1 ∈ tp_plist,
    tp_hcheck 1 13 1 3 s0 s1 (tp_look tp_tab1 s0 s1) = true := by
  intro s0 hs0 s1 hs1
  simp only [tp_plist, List.mem_cons, List.not_mem_nil, or_false] at hs0
  rcases hs0 with rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.1 tp_tab1_ok_0 s1 hs1
  · exact List.all_eq_true.1 tp_tab1_ok_1 s1 hs1
  · exact List.all_eq_true.1 tp_tab1_ok_2 s1 hs1
  · exact List.all_eq_true.1 tp_tab1_ok_3 s1 hs1
  · exact List.all_eq_true.1 tp_tab1_ok_4 s1 hs1
  · exact List.all_eq_true.1 tp_tab1_ok_5 s1 hs1

lemma tp_tab2_all : ∀ s0 ∈ tp_plist, ∀ s1 ∈ tp_plist,
    tp_hcheck 2 11 1 3 s0 s1 (tp_look tp_tab2 s0 s1) = true := by
  intro s0 hs0 s1 hs1
  simp only [tp_plist, List.mem_cons, List.not_mem_nil, or_false] at hs0
  rcases hs0 with rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.1 tp_tab2_ok_0 s1 hs1
  · exact List.all_eq_true.1 tp_tab2_ok_1 s1 hs1
  · exact List.all_eq_true.1 tp_tab2_ok_2 s1 hs1
  · exact List.all_eq_true.1 tp_tab2_ok_3 s1 hs1
  · exact List.all_eq_true.1 tp_tab2_ok_4 s1 hs1
  · exact List.all_eq_true.1 tp_tab2_ok_5 s1 hs1

lemma tp_base_val (p : Fin (3 * 2 ^ 3)) : (tp_base 3 p : ℕ) = 8 * (p / 8) := by
  rw [tp_base, cd_idx_val, gg_unit_val]
  norm_num

lemma tp_baseJ_val (P : Fin (2 * (3 * 2 ^ 3))) : (tp_baseJ 3 P : ℕ) = 8 * (P / 8) := by
  have h1 : (tp_baseJ 3 P : ℕ) = (tp_base 3 (gg_jp 3 P) : ℕ) + (3 * 2 ^ 3) * (gg_jw 3 P : ℕ) := rfl
  rw [h1, tp_base_val, cd_jp_val, cd_jw_val]
  norm_num
  omega

lemma tp_sum48 (f : ℕ → ℝ) : ∑ P : Fin (2 * (3 * 2 ^ 3)), f P = ∑ P ∈ range 48, f P :=
  Fin.sum_univ_eq_sum_range f 48

lemma tp_DT_vec (v : List ℤ) :
    tp_DT (tp_baseJ 3) (cd_vec (2 * (3 * 2 ^ 3)) v) = cd_vec (2 * (3 * 2 ^ 3)) (tp_DTl v) := by
  funext Q
  have hQ : (Q : ℕ) < 48 := Q.2
  have hget : (tp_DTl v).getD Q 0 = v.getD Q 0 - cd_nsum 48 fun P =>
      if 8 * (P / 8) = Q then v.getD P 0 else 0 := by
    simp only [tp_DTl, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hQ,
      Option.map_some, Option.getD_some]
  simp only [tp_DT, cd_vec, hget, cd_nsum_eq]
  push_cast
  congr 1
  rw [sum_filter]
  have e : ∀ P : Fin (2 * (3 * 2 ^ 3)), (if tp_baseJ 3 P = Q then ((v.getD P 0 : ℤ) : ℝ) else 0) =
      (fun n : ℕ => if 8 * (n / 8) = (Q : ℕ) then ((v.getD n 0 : ℤ) : ℝ) else 0) P := by
    intro P
    simp only [Fin.ext_iff, tp_baseJ_val]
  rw [← tp_sum48]
  exact sum_congr rfl fun P _ => e P

/-- **Soundness of a half-space certificate.** -/
theorem tp_hcheck_sound {m Jn Kc : ℕ} (hm : m ≤ 3) {s0 s1 : List ℕ} {v : List ℤ}
    (hc : tp_hcheck m Jn 1 Kc s0 s1 v = true) :
    0 < (tp_Sv s0 s1 v : ℝ) / 2 ^ 24 ∧
    (Jn : ℝ) * gg_quad (gg_CJ 3 m) (tp_DT (tp_baseJ 3) (cd_vec (2 * (3 * 2 ^ 3)) v)) ≤
      ((tp_Sv s0 s1 v : ℝ) / 2 ^ 24) ^ 2 ∧
    ∀ (x : Fin (2 * (3 * 2 ^ 3)) → ℝ) (y r : ℝ), 0 ≤ r →
      (∀ P : Fin (2 * (3 * 2 ^ 3)), |x P - y * ((tp_zc s0 s1 P : ℝ) / 2 ^ 24)| ≤ r) →
      (tp_Sv s0 s1 v : ℝ) / 2 ^ 24 * (y - Kc * r) ≤ ∑ P, cd_vec (2 * (3 * 2 ^ 3)) v P * x P := by
  simp only [tp_hcheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hS, hq⟩, hL⟩ := hc
  have hSr : (0 : ℝ) < tp_Sv s0 s1 v := by exact_mod_cast hS
  refine ⟨by positivity, ?_, fun x y r hr hx => ?_⟩
  · rw [tp_DT_vec]
    have hcast := cd_QJz_cast 3 m hm (tp_DTl v)
    have hq' : (Jn : ℝ) * (cd_QJz 3 m (tp_DTl v) : ℝ) * 2 ^ 48 ≤
        (1 : ℝ) * (240 * 2 ^ (6 - m)) * (tp_Sv s0 s1 v : ℝ) ^ 2 := by exact_mod_cast hq
    rw [hcast] at hq'
    have e6 : (2 : ℝ) ^ (2 * 3 - m) = 2 ^ (6 - m) := by norm_num
    rw [e6] at hq'
    have hp : (0 : ℝ) < 240 * 2 ^ (6 - m) := by positivity
    rw [div_pow]
    rw [le_div_iff₀ (by positivity)]
    have : ((2 : ℝ) ^ 24) ^ 2 = 2 ^ 48 := by norm_num
    nlinarith
  · have hL' : (tp_L1 v : ℝ) * 2 ^ 24 ≤ (Kc : ℝ) * tp_Sv s0 s1 v := by exact_mod_cast hL
    have hSsum : (tp_Sv s0 s1 v : ℝ) =
        ∑ P : Fin (2 * (3 * 2 ^ 3)), cd_vec (2 * (3 * 2 ^ 3)) v P * (tp_zc s0 s1 P : ℝ) := by
      rw [tp_Sv, cd_nsum_eq]
      push_cast
      rw [← tp_sum48 (fun P : ℕ => ((v.getD P 0 : ℤ) : ℝ) * ((tp_zc s0 s1 P : ℤ) : ℝ))]
      rfl
    have hLsum : (tp_L1 v : ℝ) = ∑ P : Fin (2 * (3 * 2 ^ 3)), |cd_vec (2 * (3 * 2 ^ 3)) v P| := by
      rw [tp_L1, cd_nsum_eq]
      push_cast
      rw [← tp_sum48 (fun P : ℕ => |((v.getD P 0 : ℤ) : ℝ)|)]
      rfl
    have hsplit : ∑ P, cd_vec (2 * (3 * 2 ^ 3)) v P * x P =
        y * ((tp_Sv s0 s1 v : ℝ) / 2 ^ 24) +
          ∑ P, cd_vec (2 * (3 * 2 ^ 3)) v P * (x P - y * ((tp_zc s0 s1 P : ℝ) / 2 ^ 24)) := by
      rw [hSsum, sum_div, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun P _ => by ring
    have hdev : -((tp_L1 v : ℝ) * r) ≤
        ∑ P, cd_vec (2 * (3 * 2 ^ 3)) v P * (x P - y * ((tp_zc s0 s1 P : ℝ) / 2 ^ 24)) := by
      rw [hLsum, sum_mul, ← sum_neg_distrib]
      refine sum_le_sum fun P _ => ?_
      have h1 := hx P
      have h2 := neg_abs_le (cd_vec (2 * (3 * 2 ^ 3)) v P * (x P - y * ((tp_zc s0 s1 P : ℝ) / 2 ^ 24)))
      rw [abs_mul] at h2
      have h3 : |cd_vec (2 * (3 * 2 ^ 3)) v P| * |x P - y * ((tp_zc s0 s1 P : ℝ) / 2 ^ 24)|
          ≤ |cd_vec (2 * (3 * 2 ^ 3)) v P| * r := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      linarith
    have hL2 : (tp_L1 v : ℝ) ≤ Kc * ((tp_Sv s0 s1 v : ℝ) / 2 ^ 24) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]; linarith
    rw [hsplit]
    have := mul_le_mul_of_nonneg_right hL2 hr
    nlinarith

end Census
end IIT
