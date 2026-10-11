/-
Census, B1, W14 work package WP5 (part 11): **the coin** (W5 Lemma E2', G-W14-4).

`coin_core (hGC hMills hESL)`: for `f ∈ GoodX3`, `K ∈ famX3`, `P(Core_K(2κ0)) ≥ 1/(100 √(ln N))`.

`P(Core_K(2κ0)) ≥ Σ_{k ∈ K, b} P(E_k^b)` (disjoint, `w5Ev_disj`, `w5Ev_core`), and
`P(E_k^b) ≥ P(B)(1 - Σ_c P(G_c) - Σ_j P(G_j)) ≥ (G1 - G3)(1 - 2N G2 - N G4)` by independence of disjoint entry
sets, the GC tails at the levels `zA + 1/N`, `2√(ln N)`, `zA`, `(1 - 3/m) zA` and Mills; then `w5_cfinal`.

No `sorry`.
-/
import IIT.Census.B1CntCoinCoreB

namespace IIT
namespace Census

open MeasureTheory Filter Topology Finset
open scoped Classical

variable {N : ℕ}

/-- **The probability of one coin event.** -/
lemma w5_Ev_prob (hESL : EntrySumLawStmt) (hMills : MillsStmt) {C : ℝ} (hC : W5GC C)
    (hC0 : 0 ≤ C) {s r0 : State N} (K : Finset (Fin N)) (k : Fin N) (b : Bool)
    (hfar : N ≤ 3 * ham r0 s) (hdM : N - (univ \ K).card = dX N) (hd2 : 2 ≤ dX N)
    (hD : 3 * dX N + 19 ≤ N) (hda : (dX N : ℝ) ^ 2 ≤ 2 ^ dX N / 2) (hN1 : 1 ≤ N)
    (h2d : 2 * dX N ≤ N) (hP : 20000 * (N : ℝ) ^ 5 ≤ Real.sqrt (2 ^ dX N)) (hzA : w5zA N ≤ N)
    (hL1 : 1 ≤ Real.log N) (hm16 : 16 ≤ mX N)
    (hX : 0 ≤ 1 - (2 * N * (w5mup (w5zA N) + w5err C N) +
      N * (w5mup ((1 - 3 / mX N) * w5zA N) + w5err C N))) :
    ((w5mlo (w5zA N + 1 / N) - w5err C N) - (w5mup (2 * Real.sqrt (Real.log N)) + w5err C N)) *
        (1 - (2 * N * (w5mup (w5zA N) + w5err C N) +
          N * (w5mup ((1 - 3 / mX N) * w5zA N) + w5err C N))) ≤
      (cubeM N (w5Ev s r0 K k b)).toReal := by
  set μ := cubeM N with hμ
  set a : ℝ := 2 ^ dX N with ha_def
  have ha : 0 < a := by positivity
  set err := w5err C N with herr
  have herr0 : 0 ≤ err := by rw [herr]; unfold w5err; positivity
  set zA := w5zA N with hzAdef
  have hzA0 : 0 < zA := Real.sqrt_pos.2 (by linarith)
  set ℓ := Real.sqrt (Real.log N) with hℓdef
  have hℓ0 : 0 < ℓ := Real.sqrt_pos.2 (by linarith)
  set y4 := (1 - 3 / mX N) * zA with hy4
  have hm0 : 0 < mX N := by linarith
  have hy40 : 0 < y4 := by
    have : 3 / mX N < 1 := by rw [div_lt_one hm0]; linarith
    rw [hy4]; exact mul_pos (by linarith) hzA0
  set G2u := w5mup zA + err with hG2u
  set G4u := w5mup y4 + err with hG4u
  have hG2u0 : 0 ≤ G2u := by rw [hG2u]; unfold w5mup; positivity
  have hG4u0 : 0 ≤ G4u := by rw [hG4u]; unfold w5mup; positivity
  set F := sensRows s r0 with hF
  set M := univ \ K with hM
  -- fresh counts and the error
  have hcnt : ∀ t : State N, ham s t ≤ 2 → ∀ c : Fin N,
      0 < (w5E F (agree M t) c).card ∧ (w5E F (agree M t) c).card ≤ a ∧
        C * ((w5E F (agree M t) c).card : ℝ) ^ (-(1 / 8 : ℝ)) ≤ err ∧
        a - (dX N : ℝ) ^ 2 ≤ (w5E F (agree M t) c).card := by
    intro t ht c
    obtain ⟨h1, h2⟩ := w5_fresh_card hfar K t ht c hdM hd2 hD
    have h3 : a / 2 ≤ ((w5E F (agree M t) c).card : ℝ) := by linarith
    refine ⟨?_, h2, w5_err_le C hC0 h3, h1⟩
    have : (0 : ℝ) < (w5E F (agree M t) c).card := by linarith
    exact_mod_cast this
  have hs0 : ham s s ≤ 2 := by simp [ham_self]
  -- the `B` factor
  set S1 := {w : Param N | a * w5lam1 N ≤ w5S F (agree M s) k b w} with hS1
  set S3 := {w : Param N | a * w5lam3 N ≤ w5S F (agree M s) k b w} with hS3
  have hBdef : w5Bset s r0 K k b = S1 \ S3 := rfl
  obtain ⟨hn0, hna, hne, hnlo⟩ := hcnt s hs0 k
  have hp1 : w5mlo (zA + 1 / N) - err ≤ (μ S1).toReal := by
    have hx : 0 < zA + 1 / N := by positivity
    have h1 : _ ≤ (μ S1).toReal := w5S_tail_lo hESL hC F (agree M s) k b hn0
      (w5_req1 hN1 h2d hP hzA hda (by linarith))
    have h2 : w5mlo (zA + 1 / N) ≤ w5Q (zA + 1 / N) := (hMills _ hx).1
    linarith
  have hp3 : (μ S3).toReal ≤ w5mup (2 * ℓ) + err := by
    have hy : 0 < 2 * ℓ := by positivity
    have h1 : (μ S3).toReal ≤ _ := w5S_tail_up hESL hC F (agree M s) k b hn0
      (w5_req3 hN1 hL1 hP (by omega) hna)
    have h2 : w5Q (2 * ℓ) ≤ w5mup (2 * ℓ) := (hMills _ hy).2
    linarith
  have hpB : (w5mlo (zA + 1 / N) - err) - (w5mup (2 * ℓ) + err) ≤ (μ (w5Bset s r0 K k b)).toReal := by
    rw [hBdef]; have := w5_toReal_diff μ S1 S3; linarith
  set pB := (μ (w5Bset s r0 K k b)).toReal with hpBdef
  have hpB0 : 0 ≤ pB := ENNReal.toReal_nonneg
  -- the bad events
  have hGc : ∀ c b', (μ (w5Gc s r0 K c b')).toReal ≤ G2u := by
    intro c b'
    obtain ⟨hc0, hca, hce, -⟩ := hcnt s hs0 c
    have h1 : (μ (w5Gc s r0 K c b')).toReal ≤ _ :=
      w5S_tail_up hESL hC F (agree M s) c b' hc0 (w5_req2 (by linarith) hca)
    have h2 : w5Q zA ≤ w5mup zA := (hMills _ hzA0).2
    rw [hG2u]; linarith
  have hGj : ∀ j, ham s (flipAt j s) ≤ 2 → (μ (w5Gj s r0 K j k b)).toReal ≤ G4u := by
    intro j hj
    obtain ⟨hc0, hca, hce, -⟩ := hcnt (flipAt j s) hj k
    have h1 : (μ (w5Gj s r0 K j k b)).toReal ≤ _ := w5S_tail_up hESL hC F (agree M (flipAt j s)) k b hc0
      (w5_req4 (by linarith) (by linarith) hca)
    have h2 : w5Q y4 ≤ w5mup y4 := (hMills _ hy40).2
    rw [hG4u]; linarith
  -- independence
  have hBdet : DetOnE (w5E F (agree M s) k) (w5Bset s r0 K k b) :=
    (w5S_detOn_ge F (agree M s) k b _).inter (w5S_detOn_ge F (agree M s) k b _).compl
  have hindc : ∀ c, c ≠ k → ∀ b', (μ (w5Bset s r0 K k b ∩ w5Gc s r0 K c b')).toReal ≤ pB * G2u := by
    intro c hc b'
    rw [cubeM_inter_eq_mul_of_detOnE (w5E_disj_col F _ _ (Ne.symm hc)) (measurableSet_w5Bset _ _ _ _ _)
      (measurableSet_w5Gc _ _ _ _ _) hBdet (w5S_detOn_ge F (agree M s) c b' _), ENNReal.toReal_mul]
    exact mul_le_mul_of_nonneg_left (hGc c b') hpB0
  have hindj : ∀ j ∈ M, (μ (w5Bset s r0 K k b ∩ w5Gj s r0 K j k b)).toReal ≤ pB * G4u := by
    intro j hj
    have hj2 : ham s (flipAt j s) ≤ 2 := by
      have := ham_flipAt_le_one j s; rw [ham_comm] at this; omega
    rw [cubeM_inter_eq_mul_of_detOnE (w5E_disj_row F (w5_C0_Cj_disj s K hj) k k)
      (measurableSet_w5Bset _ _ _ _ _) (measurableSet_w5Gj _ _ _ _ _ _) hBdet
      (w5S_detOn_ge F _ k b _), ENNReal.toReal_mul]
    exact mul_le_mul_of_nonneg_left (hGj j hj2) hpB0
  -- the union bound on `B ∩ Bad`
  have hsubset : w5Bset s r0 K k b ∩ w5Bad s r0 K k b ⊆
      (⋃ c ∈ univ.erase k, ⋃ b' ∈ (univ : Finset Bool), w5Bset s r0 K k b ∩ w5Gc s r0 K c b') ∪
        ⋃ j ∈ M, w5Bset s r0 K k b ∩ w5Gj s r0 K j k b := by
    rintro w ⟨hB, hbad⟩
    rcases hbad with h | h
    · left
      simp only [Set.mem_iUnion, exists_prop] at h ⊢
      obtain ⟨c, hc, b', hb', hw⟩ := h
      exact ⟨c, hc, b', hb', hB, hw⟩
    · right
      simp only [Set.mem_iUnion, exists_prop] at h ⊢
      obtain ⟨j, hj, hw⟩ := h
      exact ⟨j, hj, hB, hw⟩
  have hbadE : μ (w5Bset s r0 K k b ∩ w5Bad s r0 K k b) ≤
      (∑ c ∈ univ.erase k, ∑ b' ∈ (univ : Finset Bool), μ (w5Bset s r0 K k b ∩ w5Gc s r0 K c b')) +
        ∑ j ∈ M, μ (w5Bset s r0 K k b ∩ w5Gj s r0 K j k b) := by
    refine (measure_mono hsubset).trans ((measure_union_le _ _).trans (add_le_add ?_ ?_))
    · refine (measure_biUnion_finset_le _ _).trans (sum_le_sum fun c _ => ?_)
      exact measure_biUnion_finset_le _ _
    · exact measure_biUnion_finset_le _ _
  have hfin : ∀ {T : Set (Param N)}, μ T ≠ ⊤ := fun {T} => measure_ne_top _ _
  have hbadR : (μ (w5Bset s r0 K k b ∩ w5Bad s r0 K k b)).toReal ≤
      (∑ c ∈ univ.erase k, ∑ b' ∈ (univ : Finset Bool),
        (μ (w5Bset s r0 K k b ∩ w5Gc s r0 K c b')).toReal) +
        ∑ j ∈ M, (μ (w5Bset s r0 K k b ∩ w5Gj s r0 K j k b)).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun c _ =>
      ENNReal.sum_ne_top.2 fun b' _ => hfin, ENNReal.sum_ne_top.2 fun j _ => hfin⟩) hbadE
    rw [ENNReal.toReal_add (ENNReal.sum_ne_top.2 fun c _ => ENNReal.sum_ne_top.2 fun b' _ => hfin)
      (ENNReal.sum_ne_top.2 fun j _ => hfin), ENNReal.toReal_sum (fun c _ =>
      ENNReal.sum_ne_top.2 fun b' _ => hfin), ENNReal.toReal_sum (fun j _ => hfin)] at h
    refine h.trans_eq ?_
    congr 1
    exact sum_congr rfl fun c _ => ENNReal.toReal_sum fun b' _ => hfin
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hsum1 : ∑ c ∈ univ.erase k, ∑ b' ∈ (univ : Finset Bool),
      (μ (w5Bset s r0 K k b ∩ w5Gc s r0 K c b')).toReal ≤ N * (2 * (pB * G2u)) := by
    calc ∑ c ∈ univ.erase k, ∑ b' ∈ (univ : Finset Bool),
          (μ (w5Bset s r0 K k b ∩ w5Gc s r0 K c b')).toReal
        ≤ ∑ _c ∈ univ.erase k, ∑ _b' ∈ (univ : Finset Bool), pB * G2u :=
          sum_le_sum fun c hc => sum_le_sum fun b' _ => hindc c (mem_erase.1 hc).1 b'
      _ = ((univ.erase k).card : ℝ) * (2 * (pB * G2u)) := by
          simp [sum_const, card_univ, Fintype.card_bool]
      _ ≤ N * (2 * (pB * G2u)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have : (univ.erase k).card ≤ N := (card_erase_le).trans (by simp)
          exact_mod_cast this
  have hsum2 : ∑ j ∈ M, (μ (w5Bset s r0 K k b ∩ w5Gj s r0 K j k b)).toReal ≤ N * (pB * G4u) := by
    calc ∑ j ∈ M, (μ (w5Bset s r0 K k b ∩ w5Gj s r0 K j k b)).toReal
        ≤ ∑ _j ∈ M, pB * G4u := sum_le_sum fun j hj => hindj j hj
      _ = (M.card : ℝ) * (pB * G4u) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ N * (pB * G4u) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have : M.card ≤ N := (card_le_univ _).trans (by simp)
          exact_mod_cast this
  -- assemble
  have hE := w5_toReal_sub_inter_le μ (w5Bset s r0 K k b) (w5Bad s r0 K k b)
  have hEv : (μ (w5Ev s r0 K k b)).toReal = (μ (w5Bset s r0 K k b \ w5Bad s r0 K k b)).toReal := rfl
  rw [hEv]
  have hX' : pB * (1 - (2 * N * G2u + N * G4u)) ≤ (μ (w5Bset s r0 K k b \ w5Bad s r0 K k b)).toReal := by
    have : pB * (1 - (2 * N * G2u + N * G4u)) = pB - (N * (2 * (pB * G2u)) + N * (pB * G4u)) := by ring
    rw [this]; linarith
  have hmono : ((w5mlo (zA + 1 / N) - err) - (w5mup (2 * ℓ) + err)) * (1 - (2 * N * G2u + N * G4u)) ≤
      pB * (1 - (2 * N * G2u + N * G4u)) := mul_le_mul_of_nonneg_right hpB hX
  exact hmono.trans hX'

/-- **`coin_core`** (W5 Lemma E2' at the explicit thresholds of G-W14-4). -/
theorem coin_core (hGC : GCStmt) (hMills : MillsStmt) (hESL : EntrySumLawStmt) :
    ∀ᶠ N in atTop, ∀ (s r0 : State N) (x : Fin N) (σ : XSide), ∀ f ∈ GoodX3 N s r0 x σ,
      ∀ K ∈ famX3 N s r0 x σ (b1Ext f),
        ENNReal.ofReal (1 / (100 * Real.sqrt (Real.log N))) ≤
          rowsOutM (sensRows s r0) {g | CoreK N s K (2 * kap0 N) (glueRows (sensRows s r0) f g)} := by
  obtain ⟨C, hCpos, hCC⟩ := hGC
  have hC : W5GC C := hCC
  filter_upwards [w5_cfinal C hCpos.le, w5_ev_exp_poly, w5_ev_log_sq, w5_ev_log100, w5_ev_sizes,
    eventually_ge_atTop 1000] with N hfin hP hLs hL100 hsz hN s r0 x σ f hf K hK
  obtain ⟨hd2, hD, hdN, _⟩ := hsz
  have hfar : N ≤ 3 * ham r0 s := hf.1.far
  have hKc : K.card = dX N := famX3_card hK
  have hdM : N - (univ \ K).card = dX N := by
    rw [card_univ_sdiff, Fintype.card_fin, hKc]; omega
  have hN1 : 1 ≤ N := by omega
  have hNr : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have h2d : 2 * dX N ≤ N := by unfold dX; omega
  set L := Real.log N with hLdef
  have hL1 : 1 ≤ L := by linarith
  have hLN : L ≤ N := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hzA : w5zA N ≤ N := by
    unfold w5zA
    have : 2 * (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have h := Real.sqrt_le_sqrt (show 2 * L ≤ (N : ℝ) ^ 2 by linarith)
    rwa [Real.sqrt_sq (by positivity)] at h
  have hda : (dX N : ℝ) ^ 2 ≤ 2 ^ dX N / 2 := by
    have hsa := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 ^ dX N by positivity)
    have hd : (dX N : ℝ) ≤ N := by exact_mod_cast hdN
    have h5 : (N : ℝ) ≤ (N : ℝ) ^ 5 := by
      calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (N : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have : (N : ℝ) ≤ Real.sqrt (2 ^ dX N) := by linarith
    have hd2' : (dX N : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hd 2
    nlinarith
  have hm16 : 16 ≤ mX N := by
    unfold mX; rw [Nat.cast_sub hdN]
    have : (30 : ℝ) * dX N ≤ N + 29 := by
      have : 30 * dX N ≤ N + 29 := by unfold dX; omega
      exact_mod_cast this
    linarith
  rw [rowsOut_eq_w5G f (fun w => CoreK N s K (2 * kap0 N) w)]
  set μ := cubeM N
  have hcover : (⋃ p ∈ K ×ˢ (univ : Finset Bool), w5Ev s r0 K p.1 p.2) ⊆
      {w | CoreK N s K (2 * kap0 N) (w5G f w)} := by
    intro w hw
    simp only [Set.mem_iUnion, exists_prop, mem_product] at hw
    obtain ⟨⟨k, b⟩, ⟨hk, _⟩, hwE⟩ := hw
    exact ⟨k, hk, w5Ev_core f K k b hfar hdM hd2 (by omega) hm16 hwE⟩
  have hdisj : (↑(K ×ˢ (univ : Finset Bool)) : Set (Fin N × Bool)).PairwiseDisjoint
      (fun p => w5Ev s r0 K p.1 p.2) := by
    intro p _ q _ hpq
    exact w5Ev_disj s r0 K (by omega) hpq
  have hU : μ (⋃ p ∈ K ×ˢ (univ : Finset Bool), w5Ev s r0 K p.1 p.2) =
      ∑ p ∈ K ×ˢ (univ : Finset Bool), μ (w5Ev s r0 K p.1 p.2) :=
    measure_biUnion_finset hdisj fun p _ => measurableSet_w5Ev _ _ _ _ _
  set V := ((w5mlo (w5zA N + 1 / N) - w5err C N) - (w5mup (2 * Real.sqrt L) + w5err C N)) *
    (1 - (2 * N * (w5mup (w5zA N) + w5err C N) + N * (w5mup ((1 - 3 / mX N) * w5zA N) + w5err C N)))
    with hV
  have hpiece : ∀ p ∈ K ×ˢ (univ : Finset Bool), V ≤ (μ (w5Ev s r0 K p.1 p.2)).toReal := fun p _ =>
    w5_Ev_prob hESL hMills hC hCpos.le K p.1 p.2 hfar hdM hd2 (by omega) hda hN1 h2d hP hzA hL1 hm16
      hfin.1
  have hsumV : ((K ×ˢ (univ : Finset Bool)).card : ℝ) * V ≤
      (μ (⋃ p ∈ K ×ˢ (univ : Finset Bool), w5Ev s r0 K p.1 p.2)).toReal := by
    rw [hU, ENNReal.toReal_sum (fun p _ => measure_ne_top _ _), ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hpiece
  have hcard : ((K ×ˢ (univ : Finset Bool)).card : ℝ) = 2 * (dX N : ℝ) := by
    rw [card_product, hKc, card_univ, Fintype.card_bool]; push_cast; ring
  rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  calc 1 / (100 * Real.sqrt L) ≤ 2 * (dX N : ℝ) * V := by rw [hV, ← mul_assoc]; exact hfin.2
    _ = ((K ×ˢ (univ : Finset Bool)).card : ℝ) * V := by rw [hcard]
    _ ≤ (μ (⋃ p ∈ K ×ˢ (univ : Finset Bool), w5Ev s r0 K p.1 p.2)).toReal := hsumV
    _ ≤ (μ {w | CoreK N s K (2 * kap0 N) (w5G f w)}).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hcover)

end Census
end IIT

#print axioms IIT.Census.coin_core
