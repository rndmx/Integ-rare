/-
Census of complexes: probability bounds for the sharp deviation event `gSharp` and for `gZ`.

Under `cubeM N`:
* `gSharp` fails with probability at most `fSharp N = fg2 N + 2 e / N`: Bernstein over all rows at the
  level `2 √(2 V L) + 2 τ L` (tail `2 e^{-L}`), with `V = 3 σ_N²`, `L = LkN N |S|`, union over the
  candidates `S`, the units `i ∈ S`, the subsets `Y, Y' ⊆ S` and the patterns on `S`;
* `gZ` fails with probability at most `fZ N = 1 / (256 N²)` (Chebyshev over the rows).
-/
import IIT.Census.BigPhiProbSub
import IIT.Census.TightStats

namespace IIT
namespace Census

open MeasureTheory ProbabilityTheory Finset Filter Topology

noncomputable section

variable {N : ℕ}

/-! ### Bernstein at the sharp level -/

/-- **Bernstein over the rows at the sharp level**: for a weighted sum of centred truncated row
products with weights of absolute value at most one, the deviation `2 √(2 V L) + 2 τ L` has
probability at most `2 e^{-L}`. -/
theorem cubeM_trunc_sharp (i : Fin N) (s : Finset (State N)) (ε : State N → ℝ)
    (hε : ∀ r, |ε r| ≤ 1) {L V : ℝ} (hL : 0 ≤ L) (hVpos : 0 < V)
    (hV : (s.card : ℝ) * (1 / 3 : ℝ) ^ (N - 1) ≤ V) :
    cubeM N {w | 2 * Real.sqrt (2 * V * L) + 2 * tauN N * L ≤
      |∑ r ∈ s, ε r * (rowT i (w r) - muT N i)|} ≤ ENNReal.ofReal (2 * Real.exp (-L)) := by
  have hmf : ∀ r, Measurable fun v : Fin N → ℝ => ε r * (rowT i v - muT N i) :=
    fun r => measurable_const.mul ((measurable_rowT i).sub_const _)
  have hind := iIndepFun_rows (fun r v => ε r * (rowT i v - muT N i)) hmf
  have hmeas : ∀ r, AEMeasurable (fun w : Param N => ε r * (rowT i (w r) - muT N i)) (cubeM N) :=
    fun r => ((hmf r).comp (measurable_pi_apply r)).aemeasurable
  have hb : ∀ r ∈ s, ∀ᵐ w ∂cubeM N, |ε r * (rowT i (w r) - muT N i)| ≤ tauN N := by
    intro r _
    refine ae_of_all _ fun w => ?_
    rw [abs_mul]
    calc |ε r| * |rowT i (w r) - muT N i| ≤ 1 * tauN N :=
          mul_le_mul (hε r) (abs_rowT_sub_le i _) (abs_nonneg _) zero_le_one
      _ = tauN N := one_mul _
  have h0 : ∀ r ∈ s, ∫ w, ε r * (rowT i (w r) - muT N i) ∂cubeM N = 0 := by
    intro r _
    rw [integral_row_eval (g := fun v => ε r * (rowT i v - muT N i)) (hmf r).aestronglyMeasurable r,
      integral_const_mul, integral_sub (integrable_rowT i) (integrable_const _), integral_const]
    simp [muT]
  have hV' : ∑ r ∈ s, ∫ w, (ε r * (rowT i (w r) - muT N i)) ^ 2 ∂cubeM N ≤ V := by
    calc ∑ r ∈ s, ∫ w, (ε r * (rowT i (w r) - muT N i)) ^ 2 ∂cubeM N
        ≤ ∑ _r ∈ s, (1 / 3 : ℝ) ^ (N - 1) := by
          refine sum_le_sum fun r _ => ?_
          rw [integral_row_eval (g := fun v => (ε r * (rowT i v - muT N i)) ^ 2)
            ((hmf r).pow_const 2).aestronglyMeasurable r]
          simp_rw [mul_pow]
          rw [integral_const_mul]
          have hε2 : ε r ^ 2 ≤ 1 := by
            rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (hε r)
          calc ε r ^ 2 * ∫ v, (rowT i v - muT N i) ^ 2 ∂rowM N
              ≤ 1 * ∫ v, (rowT i v - muT N i) ^ 2 ∂rowM N :=
                mul_le_mul_of_nonneg_right hε2 (integral_nonneg fun v => sq_nonneg _)
            _ ≤ _ := by rw [one_mul]; exact integral_sq_rowT_sub i
      _ = s.card * (1 / 3 : ℝ) ^ (N - 1) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ V := hV
  have hτ := tauN_pos N
  set a := Real.sqrt (2 * V * L) with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 2 * V * L := Real.sq_sqrt (by positivity)
  have hE0 : 0 ≤ 2 * a + 2 * tauN N * L := by positivity
  have h := bernstein_abs (X := fun r (w : Param N) => ε r * (rowT i (w r) - muT N i))
    s hind hmeas hτ.le hE0 hb h0 hV'
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (h.trans ?_)
  have h1 : L ≤ (2 * a + 2 * tauN N * L) ^ 2 / (4 * V) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg hτ.le hL, mul_nonneg ha0 (mul_nonneg hτ.le hL)]
  have h2 : L ≤ (2 * a + 2 * tauN N * L) / (2 * tauN N) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h3 := le_min h1 h2
  have := Real.exp_le_exp.mpr (neg_le_neg h3)
  linarith

/-! ### `gSharp` -/

/-- The bad event of `gSharp` for one pattern, on the event `g2`. -/
def badSh (S : Finset (Fin N)) (i : Fin N) (Y Y' : Finset (Fin N)) (t : State N) :
    Set (Param N) :=
  {w | (∀ i r, Qw w i r ≤ tauN N) ∧
    ¬ |DQ w S Y Y' t i| ≤
      2 * Real.sqrt (6 * sigN N ^ 2 * LkN N S.card) + 2 * tauN N * LkN N S.card}

lemma sigN_sq (N : ℕ) : sigN N ^ 2 = (2 / 3 : ℝ) ^ N := Real.sq_sqrt (by positivity)

lemma cubeM_badSh {S : Finset (Fin N)} {i : Fin N} {Y Y' : Finset (Fin N)} (t : State N)
    (hi : i ∈ S) (hY : Y ⊆ S) (hY' : Y' ⊆ S) :
    cubeM N (badSh S i Y Y' t) ≤ ENNReal.ofReal (2 * Real.exp (-LkN N S.card)) := by
  have hN : 1 ≤ N := by have := i.pos; omega
  have hL : 0 ≤ LkN N S.card := zero_le_one.trans (one_le_LkN (card_pos.2 ⟨i, hi⟩))
  have hVpos : (0 : ℝ) < 3 * sigN N ^ 2 := by have := sigN_pos N; positivity
  refine (measure_mono ?_).trans (cubeM_trunc_sharp i univ (epsW S Y Y' t)
    (abs_epsW_le S Y Y' t) hL hVpos (by rw [card_state]; push_cast; rw [V13_eq hN, sigN_sq]))
  rintro w ⟨hg2, hbad⟩
  simp only [Set.mem_ofPred_eq]
  have hsum : ∑ r, epsW S Y Y' t r * (rowT i (w r) - muT N i) = DQ w S Y Y' t i := by
    simp_rw [mul_sub, sum_sub_distrib, ← sum_mul, sum_epsW hY hY', zero_mul, sub_zero,
      DQ_eq_sum, rowT_eq_Qw (hg2 i)]
  rw [hsum, show 2 * (3 * sigN N ^ 2) * LkN N S.card = 6 * sigN N ^ 2 * LkN N S.card by ring]
  push Not at hbad
  exact hbad.le

/-- All bad patterns of one candidate `S`. -/
def badShS (S : Finset (Fin N)) : Set (Param N) :=
  ⋃ i ∈ S, ⋃ Y ∈ S.powerset, ⋃ Y' ∈ S.powerset, ⋃ T ∈ S.powerset, badSh S i Y Y' (indS T)

/-- The per-candidate union bound: `|S| 2^{3|S|}` patterns, each of probability `2 e^{-L}`. -/
def bSh (N k : ℕ) : ℝ := k * (2 ^ k * (2 ^ k * (2 ^ k * (2 * Real.exp (-LkN N k)))))

lemma bSh_nonneg (N k : ℕ) : 0 ≤ bSh N k := by unfold bSh; positivity

lemma cubeM_badShS (S : Finset (Fin N)) : cubeM N (badShS S) ≤ ENNReal.ofReal (bSh N S.card) := by
  have h : cubeM N (badShS S) ≤ ENNReal.ofReal (S.card * (S.powerset.card *
      (S.powerset.card * (S.powerset.card * (2 * Real.exp (-LkN N S.card)))))) := by
    unfold badShS
    refine cubeM_biUnion_le _ _ fun i hi => ?_
    refine cubeM_biUnion_le _ _ fun Y hY => ?_
    refine cubeM_biUnion_le _ _ fun Y2 hY2 => ?_
    refine cubeM_biUnion_le _ _ fun T _ => ?_
    exact cubeM_badSh (indS T) hi (mem_powerset.1 hY) (mem_powerset.1 hY2)
  rw [card_powerset] at h
  refine h.trans_eq ?_
  unfold bSh
  push_cast
  rfl

lemma bSh_le (hN : 1 ≤ N) {k : ℕ} (hk : k ≤ N) :
    bSh N k ≤ 2 * (1 / (N : ℝ)) * (1 / (N : ℝ)) ^ k := by
  have hx : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNx : (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log hNpos).symm
  have h1N : 1 / (N : ℝ) = Real.exp (-Real.log N) := by
    rw [Real.exp_neg, ← hNx, one_div]
  have h2 : (2 : ℝ) ^ k ≤ Real.exp k := by
    calc (2 : ℝ) ^ k ≤ Real.exp 1 ^ k :=
          pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) k
      _ = Real.exp k := by rw [← Real.exp_nat_mul, mul_one]
  have h8 : (2 : ℝ) ^ k * (2 ^ k * 2 ^ k) ≤ Real.exp (k * 3) := by
    calc (2 : ℝ) ^ k * (2 ^ k * 2 ^ k) ≤ Real.exp k * (Real.exp k * Real.exp k) := by
          gcongr
      _ = Real.exp (k * 3) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hk' : (k : ℝ) ≤ Real.exp (Real.log N) := by rw [← hNx]; exact_mod_cast hk
  rw [h1N, ← Real.exp_nat_mul]
  unfold bSh
  calc (k : ℝ) * (2 ^ k * (2 ^ k * (2 ^ k * (2 * Real.exp (-LkN N k)))))
      = (k : ℝ) * (2 ^ k * (2 ^ k * 2 ^ k)) * (2 * Real.exp (-LkN N k)) := by ring
    _ ≤ Real.exp (Real.log N) * Real.exp (k * 3) * (2 * Real.exp (-LkN N k)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hk' h8 (by positivity) (Real.exp_pos _).le)
          (by positivity)
    _ = 2 * Real.exp (Real.log N + k * 3 + -LkN N k) := by
        rw [Real.exp_add, Real.exp_add]; ring
    _ = 2 * Real.exp (-Real.log N + (k : ℝ) * -Real.log N) := by
        congr 2
        unfold LkN
        ring
    _ = 2 * Real.exp (-Real.log N) * Real.exp ((k : ℝ) * -Real.log N) := by
        rw [Real.exp_add]; ring

lemma sum_bSh_le (hN : 1 ≤ N) :
    ∑ S : Finset (Fin N), bSh N S.card ≤ 2 * Real.exp 1 * (1 / (N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hbin := Fin.sum_pow_mul_eq_add_pow (n := N) (1 / (N : ℝ)) 1
  simp only [one_pow, mul_one] at hbin
  have he : (1 / (N : ℝ) + 1) ^ N ≤ Real.exp 1 := by
    calc (1 / (N : ℝ) + 1) ^ N ≤ Real.exp (1 / N) ^ N :=
          pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) N
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul, mul_one_div_cancel hNpos.ne']
  calc ∑ S : Finset (Fin N), bSh N S.card
      ≤ ∑ S : Finset (Fin N), 2 * (1 / (N : ℝ)) * (1 / (N : ℝ)) ^ S.card := by
        refine sum_le_sum fun S _ => bSh_le hN ?_
        simpa using card_le_univ S
    _ = 2 * (1 / (N : ℝ)) * (1 / (N : ℝ) + 1) ^ N := by rw [← mul_sum, hbin]
    _ ≤ 2 * (1 / (N : ℝ)) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

/-- The failure probability of `gSharp`. -/
def fSharp (N : ℕ) : ℝ := fg2 N + 2 * Real.exp 1 * (1 / (N : ℝ))

/-- **`gSharp` fails with probability at most `fSharp N`.** -/
theorem cubeM_not_gSharp : cubeM N {w | ¬ gSharp N w} ≤ ENNReal.ofReal (fSharp N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hE : {w : Param 0 | ¬ gSharp 0 w} = ∅ :=
      Set.eq_empty_of_forall_notMem fun w hw => hw fun S i => i.elim0
    rw [hE, measure_empty]
    exact bot_le
  have hsub : {w : Param N | ¬ gSharp N w} ⊆
      {w | ¬ ∀ i r, Qw w i r ≤ tauN N} ∪ ⋃ S : Finset (Fin N), badShS S := by
    intro w hw
    by_cases hg2 : ∀ i r, Qw w i r ≤ tauN N
    · right
      simp only [Set.mem_ofPred_eq, gSharp, not_forall] at hw
      obtain ⟨S, i, Y, Y', t, hi, hY, hY', h⟩ := hw
      simp only [Set.mem_iUnion, badShS, mem_powerset, exists_prop]
      refine ⟨S, i, hi, Y, hY, Y', hY', S.filter fun j => t j = true, filter_subset _ _, hg2, ?_⟩
      rwa [← DQ_indS w hY hY' t i]
    · exact Or.inl hg2
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hU : cubeM N (⋃ S : Finset (Fin N), badShS S) ≤
      ENNReal.ofReal (∑ S : Finset (Fin N), bSh N S.card) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun S _ => bSh_nonneg N S.card]
    exact (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun S _ => cubeM_badShS S)
  refine (add_le_add cubeM_not_g2 hU).trans ?_
  rw [← ENNReal.ofReal_add (by unfold fg2; positivity)
    (sum_nonneg fun S _ => bSh_nonneg N S.card)]
  apply ENNReal.ofReal_le_ofReal
  unfold fSharp
  linarith [sum_bSh_le hN]

theorem tendsto_fSharp : Tendsto fSharp atTop (𝓝 0) := by
  have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * Real.exp 1)
  rw [mul_zero] at h
  have h2 := tendsto_fg2.add h
  rw [add_zero] at h2
  exact h2

/-! ### `gZ` -/

/-- The failure probability of `gZ`. -/
def fZ (N : ℕ) : ℝ := 1 / (256 * (N : ℝ) ^ 2)

/-- **`gZ` fails with probability at most `fZ N`** (Chebyshev: `E Zs = 1`, `Var Zs ≤ σ_N²`). -/
theorem cubeM_not_gZ : cubeM N {w | ¬ gZ N w} ≤ ENNReal.ofReal (fZ N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hE : {w : Param 0 | ¬ gZ 0 w} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun w hw => hw ?_
      simp [gZ, Zs, Pw]
    rw [hE, measure_empty]
    exact bot_le
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmean : (2 : ℝ) ^ N * ∫ v, ∏ j, clamp01 (v j) ∂rowM N = 1 := by
    have := integral_rowP_pow' (N := N) 1
    simp only [pow_one] at this
    rw [this, ← mul_pow]; norm_num
  have hsq : ∫ v, (∏ j, clamp01 (v j)) ^ 2 ∂rowM N = (1 / 3 : ℝ) ^ N := by
    rw [integral_rowP_pow']; norm_num
  have hc : 0 < 16 * (N : ℝ) * sigN N := by have := sigN_pos N; positivity
  have hsub : {w : Param N | ¬ gZ N w} ⊆
      {w | 16 * (N : ℝ) * sigN N ≤ |∑ r, (fun v : Fin N → ℝ => ∏ j, clamp01 (v j)) (w r) -
        2 ^ N * ∫ v, ∏ j, clamp01 (v j) ∂rowM N|} := by
    intro w hw
    rw [Set.mem_ofPred_eq, hmean]
    change 16 * (N : ℝ) * sigN N ≤ |Zs w - 1|
    simp only [Set.mem_ofPred_eq, gZ, not_le] at hw
    exact hw.le
  refine (measure_mono hsub).trans ((cheb_rows measurable_rowPw abs_rowPw_le hc).trans
    (ENNReal.ofReal_le_ofReal ?_))
  have e1 : (16 * (N : ℝ) * sigN N) ^ 2 = 256 * (N : ℝ) ^ 2 * (2 / 3 : ℝ) ^ N := by
    rw [mul_pow, sigN_sq]; ring
  have e2 : (2 : ℝ) ^ N * (1 / 3 : ℝ) ^ N = (2 / 3 : ℝ) ^ N := by rw [← mul_pow]; norm_num
  rw [hsq, e1, e2]
  apply le_of_eq
  unfold fZ
  have : (0 : ℝ) < (2 / 3 : ℝ) ^ N := by positivity
  field_simp

theorem tendsto_fZ : Tendsto fZ atTop (𝓝 0) := by
  have h := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul (1 / 256)
  rw [zero_pow two_ne_zero, mul_zero] at h
  refine h.congr fun N => ?_
  unfold fZ
  ring

end

end Census
end IIT
