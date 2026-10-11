/-
Census, B1 LTBetaHi, RL-u part 2a: **the real windowed RL-u table** (analogue of `rltc_real_window`).

Real data: the rest blocks `dR : RLDR` (the heavy rows other than `u = s`, INCLUDING `tc`, weights `P(r)/σ`), u's
weight `w`, offset flag `ds` (`D_u = ∅` or `S`), u's shared entries `x i = y_{u, e i}`, `f i = y_{u^i, e i}`. The datum
is floored to the grid `ℤ/n` (`5 ∣ n`) and fed to `rlu_sym` (`t = 1/80`). The certified table `(M0, Y0)` is moved to
the real data by `M := w · uEnt(x, f, Y) + max(M0 - w0 · uEnt0, lo)` (`|M - M0| ≤ 3ω'`, `ω' = ω + 1/n`).

* `RLUWin` (the conclusion): the cause box of the rest after removing u's contribution, `Y ∈ [0, 1]`, (V), (G), (P)
  at level `c0 = ⌊G1⌋` weakened by `36·3ω'`, `6·3ω'`, `6·3ω'`, (E2) `Y R i ≤ x0 - 1/8000` with `x0 ≤ x i ≤ x0 + ω'`,
  the designated budget `≤ B - 1/500 + 7ω'`, and the budget bound with `Lx ≤ x i ≤ Hx`.
* **`rlu_real_window`**.
-/
import IIT.Census.B1LTHiCertUSym
import IIT.Census.B1LTHiTcW

namespace IIT
namespace Census

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- u's pattern index (`R = u ⊕ D_u`). -/
def uIdx (ds : Bool) (u : Fin 8) : Fin 8 := ⟨(u : ℕ) ^^^ uOff ds, tc_xor_lt u.2 (uOff_lt ds)⟩

/-- **The windowed RL-u conclusion** (`t = 1/80`). -/
def RLUWin (ds : Bool) (dR : RLDR) (w : ℝ) (x f : Fin 3 → ℝ) (ω' x0 : ℝ) (T : TcTab) : Prop :=
  T.Ts < 8 ∧ 4 / 5 ≤ T.c0 ∧ (∀ i, T.c0 ≤ dR.G1 i) ∧ (∀ i, x0 ≤ x i ∧ x i ≤ x0 + ω') ∧
  (∀ (u : Fin 8) (i : Fin 3), rlLoR dR u i ≤ T.M u i - w * tcEntR x f T.Y (uIdx ds u) i ∧
    T.M u i - w * tcEntR x f T.Y (uIdx ds u) i ≤ rlLoR dR u i + rlWdR dR u i) ∧
  (∀ (u : Fin 8) (i : Fin 3), ¬((u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ)) → 0 ≤ T.Y u i ∧ T.Y u i ≤ 1) ∧
  8 * T.c0 * (5 / 3 - 1 / 80) - 36 * (3 * ω') ≤ rlV8R lp3CStar T.Ts T.M ∧
  (∀ C ∈ lp3Profiles, C ≠ lp3CStar →
    T.c0 * (1 / 80) / 20 - 6 * (3 * ω') ≤
      rlV8R C T.Ts T.M / (8 * (cd_cc 3 C : ℝ)) - rlV8R lp3CStar T.Ts T.M / 40) ∧
  (∀ u < 8, u ≠ T.Ts → 1 / 20 - 6 * (3 * ω') ≤ rlPSR T.M T.Ts - rlPSR T.M u) ∧
  (∀ (R : Fin 8) (i : Fin 3), (R : ℕ) ≠ 0 → (R : ℕ).testBit i = false → T.Y R i ≤ x0 - 1 / 8000) ∧
  ∑ R ∈ (univ : Finset (Fin 8)).erase 0, tcEntR x f T.Y R (T.dg R) ≤ T.B - 1 / 500 + 7 * ω' ∧
  0 ≤ T.Lx ∧ T.Hx ≤ 1 ∧ (∀ i, T.Lx ≤ x i ∧ x i ≤ T.Hx) ∧
  ∀ c : ℕ, 0 < c → c < 8 → T.B ≤ 3 * Real.log 2 * (T.Lx ^ 3 - tcEhiR T.Lx T.Hx c)

/-- The floored RL-u datum of real windowed data. -/
noncomputable def rlUFlD (n : ℕ) (dR : RLDR) (w : ℝ) (x f : Fin 3 → ℝ) (thr : ℚ) : RLUD :=
  ⟨rlFl n (rlMin3R dR.G1), rlFl n (rlMin3R dR.F1), rlFl n (rlMin3R dR.G2), rlFl n (rlMin3R dR.F2),
    rlFl n dR.V1, rlFl n dR.V2, rlFl n w, max thr (rlFl n (rlMin3R x)), rlFl n (rlMin3R f)⟩

lemma rlUFlD_rest (n : ℕ) (dR : RLDR) (w : ℝ) (x f : Fin 3 → ℝ) (thr : ℚ) :
    (rlUFlD n dR w x f thr).rest = rlFlD n dR := rfl

/-- The rational u entry, cast. -/
lemma rlUEnt_cast (d : RLUD) (Y : Fin 8 → Fin 3 → ℚ) (u : Fin 8) (i : Fin 3) :
    ((rlUEnt d Y u i : ℚ) : ℝ) = tcEntR (fun _ => (d.x : ℝ)) (fun _ => (d.f : ℝ)) (fun u i => (Y u i : ℝ)) u i := by
  unfold rlUEnt tcEntR
  have hM : rlM Y u i = Y u i := by simp [rlM, Nat.mod_eq_of_lt u.2, Nat.mod_eq_of_lt i.2]
  split_ifs <;> simp [hM]

lemma tcEntR_bounds {x f : Fin 3 → ℝ} {Y : Fin 8 → Fin 3 → ℝ} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hY : ∀ (u : Fin 8) (i : Fin 3), ¬((u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ)) → 0 ≤ Y u i ∧ Y u i ≤ 1)
    (u : Fin 8) (i : Fin 3) : 0 ≤ tcEntR x f Y u i ∧ tcEntR x f Y u i ≤ 1 := by
  unfold tcEntR
  split_ifs with h0 h1
  · exact hx i
  · exact hf i
  · exact hY u i (by rintro (h | h); exact h0 h; exact h1 (by simpa [rlBit] using h))

/-- **RL-u on real windowed data** (`t = 1/80`). -/
theorem rlu_real_window (ds : Bool) (dR : RLDR) (w : ℝ) (x f : Fin 3 → ℝ) {n : ℕ} (hn : 0 < n) (h5 : 5 ∣ n)
    {ω : ℝ} (hω : 0 ≤ ω) (hwin : dR.win ω) (hxw : ∀ i, x i - rlMin3R x ≤ ω) (hfw : ∀ i, f i - rlMin3R f ≤ ω)
    (hω1 : ω + 1 / n ≤ 1 / 1000)
    (hG1 : ∀ i, 4 / 5 ≤ dR.G1 i) (hG11 : ∀ i, dR.G1 i ≤ 1) (hF1 : ∀ i, 0 ≤ dR.F1 i) (hF12 : ∀ i, dR.F1 i ≤ 2)
    (hV1 : 1 ≤ dR.V1) (hF1V : ∀ i, dR.F1 i ≤ dR.V1)
    (hG2 : ∀ i, 0 ≤ dR.G2 i) (hF2 : ∀ i, 0 ≤ dR.F2 i) (hG2V : ∀ i, dR.G2 i ≤ dR.V2) (hF2V : ∀ i, dR.F2 i ≤ dR.V2)
    (hV21 : dR.V2 ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hx0 : ∀ i, (if ds then 7 / 8 else 9 / 16) ≤ x i) (hx1 : ∀ i, x i ≤ 1) (hf0 : ∀ i, 0 ≤ f i)
    (hf1 : ∀ i, f i ≤ 1) :
    ∃ (T : TcTab) (x0 : ℝ), (if ds then 7 / 8 else 9 / 16) - 1 / 1000 ≤ x0 ∧
      RLUWin ds dR w x f (ω + 1 / n) x0 T := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) ≤ 1 / n := by positivity
  set ω' := ω + 1 / n with hω'
  have hω'0 : 0 ≤ ω' := by positivity
  set thr : ℚ := if ds then 7 / 8 else 9 / 16 with hthr
  have hthrR : ((thr : ℚ) : ℝ) = (if ds then 7 / 8 else 9 / 16 : ℝ) := by
    rw [hthr]; split_ifs <;> norm_num
  set d0 := rlUFlD n dR w x f thr with hd0
  have hmin0 : ∀ g : Fin 3 → ℝ, (∀ i, 0 ≤ g i) → 0 ≤ rlMin3R g := fun g h => le_rlMin3R h
  -- the hypotheses of `rlu_sym`
  have q1 : 4 / 5 ≤ d0.G1 := rlFl_45 hn h5 (le_rlMin3R hG1)
  have q2 : d0.G1 ≤ 1 := rlFl_le_of hn (by push_cast; linarith [rlMin3R_le dR.G1 0, hG11 0])
  have q3 : 0 ≤ d0.F1 := rlFl_nonneg hn (hmin0 _ hF1)
  have q4 : d0.F1 ≤ 2 := rlFl_le_of hn (by push_cast; linarith [rlMin3R_le dR.F1 0, hF12 0])
  have q5 : 0 ≤ d0.G2 := rlFl_nonneg hn (hmin0 _ hG2)
  have q6 : d0.G2 ≤ 1 := rlFl_le_of hn (by push_cast; linarith [rlMin3R_le dR.G2 0, hG2V 0])
  have q7 : 0 ≤ d0.F2 := rlFl_nonneg hn (hmin0 _ hF2)
  have q8 : d0.F2 ≤ 1 := rlFl_le_of hn (by push_cast; linarith [rlMin3R_le dR.F2 0, hF2V 0])
  have q9 : 0 ≤ d0.w := rlFl_nonneg hn hw0
  have q10 : d0.w ≤ 1 := rlFl_le_of hn (by push_cast; linarith)
  have hx01 : ∀ i, 0 ≤ x i ∧ x i ≤ 1 := fun i =>
    ⟨le_trans (by split_ifs <;> norm_num) (hx0 i), hx1 i⟩
  have hxmin : ((thr : ℚ) : ℝ) ≤ rlMin3R x := le_rlMin3R fun i => by rw [hthrR]; exact hx0 i
  have q11 : (if ds then 7 / 8 else 9 / 16 : ℚ) ≤ d0.x := le_max_left _ _
  have q12 : d0.x ≤ 1 := by
    refine max_le (by rw [hthr]; split_ifs <;> norm_num) (rlFl_le_of hn ?_)
    push_cast; linarith [rlMin3R_le x 0, hx1 0]
  have q13 : 0 ≤ d0.f := rlFl_nonneg hn (hmin0 _ hf0)
  have q14 : d0.f ≤ 1 := rlFl_le_of hn (by push_cast; linarith [rlMin3R_le f 0, hf1 0])
  have hV1q : (1 : ℚ) ≤ d0.V1 := by
    have h := rlFl_ge_int hn (n : ℤ) (x := dR.V1) (by push_cast; rw [div_self hnR.ne']; exact hV1)
    have e : ((n : ℤ) : ℚ) / n = 1 := by
      push_cast; exact div_self (by exact_mod_cast hn.ne')
    rw [e] at h; exact h
  have q15 : max 1 d0.F1 ≤ d0.V1 :=
    max_le hV1q (rlFl_mono ((rlMin3R_le _ 0).trans (hF1V 0)))
  have q16 : max d0.G2 d0.F2 ≤ d0.V2 :=
    max_le (rlFl_mono ((rlMin3R_le _ 0).trans (hG2V 0))) (rlFl_mono ((rlMin3R_le _ 0).trans (hF2V 0)))
  obtain ⟨C, -, hCds, hTs, ⟨M0, Y0, hadm, heff⟩, hbud, hxlo, hxhi⟩ :=
    rlu_sym ds d0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  -- window facts
  set x0 : ℝ := ((d0.x : ℚ) : ℝ) with hx0def
  set f0 : ℝ := ((d0.f : ℚ) : ℝ) with hf0def
  set w0 : ℝ := ((d0.w : ℚ) : ℝ) with hw0def
  set c0 : ℝ := ((d0.G1 : ℚ) : ℝ) with hc0def
  have hx0max : x0 = max ((thr : ℚ) : ℝ) ((rlFl n (rlMin3R x) : ℚ) : ℝ) := by
    rw [hx0def]; show ((max thr (rlFl n (rlMin3R x)) : ℚ) : ℝ) = _; push_cast; rfl
  have hxc : ∀ i, x0 ≤ x i ∧ x i - x0 ≤ ω' := by
    intro i
    have h := rlFl_min_close hn hxw i
    rw [hx0max]
    refine ⟨max_le (hxmin.trans (rlMin3R_le x i)) h.1, ?_⟩
    have := le_max_right ((thr : ℚ) : ℝ) ((rlFl n (rlMin3R x) : ℚ) : ℝ)
    linarith [h.2]
  have hfc : ∀ i, f0 ≤ f i ∧ f i - f0 ≤ ω' := fun i => rlFl_min_close hn hfw i
  have hwc1 : w0 ≤ w := rlFl_le hn w
  have hwc2 : w - w0 ≤ 1 / n := by
    have h := rlFl_gt hn w
    have e : w0 = ((rlFl n w : ℚ) : ℝ) := rfl
    linarith
  have hw00 : 0 ≤ w0 := by rw [hw0def]; exact_mod_cast q9
  have hw01 : w0 ≤ 1 := by rw [hw0def]; exact_mod_cast q10
  have hc45 : (4 : ℝ) / 5 ≤ c0 := by
    have h : (((4 : ℚ) / 5 : ℚ) : ℝ) ≤ c0 := by rw [hc0def]; exact_mod_cast q1
    norm_num at h; exact h
  have hc0G : ∀ i, c0 ≤ dR.G1 i := fun i => (rlFl_le hn _).trans (rlMin3R_le _ i)
  -- the real table
  set Y : Fin 8 → Fin 3 → ℝ := fun u i => (Y0 u i : ℝ) with hYdef
  have hY01 : ∀ (u : Fin 8) (i : Fin 3), ¬((u : ℕ) = 0 ∨ (u : ℕ) = 2 ^ (i : ℕ)) → 0 ≤ Y u i ∧ Y u i ≤ 1 := by
    intro u i hv
    have h := hadm.2.1 u u.2 i i.2 (fun h => hv (Or.inl h)) (fun h => hv (Or.inr (by simpa [rlBit] using h)))
    have e : rlM Y0 u i = Y0 u i := by simp [rlM, Nat.mod_eq_of_lt u.2, Nat.mod_eq_of_lt i.2]
    rw [e] at h
    simp only [hYdef]
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  set E0 : Fin 8 → Fin 3 → ℝ := fun u i => tcEntR (fun _ => x0) (fun _ => f0) Y (uIdx ds u) i with hE0def
  have hE0c : ∀ u i, E0 u i = ((rlUEnt d0 Y0 ((u : ℕ) ^^^ uOff ds) i : ℚ) : ℝ) := fun u i =>
    (rlUEnt_cast d0 Y0 (uIdx ds u) i).symm
  set M : Fin 8 → Fin 3 → ℝ := fun u i => w * tcEntR x f Y (uIdx ds u) i +
    max ((M0 u i : ℝ) - w0 * E0 u i) (rlLoR dR u i) with hMdef
  have hM0v : ∀ (u : Fin 8) (i : Fin 3), rlM M0 u i = M0 u i := by
    intro u i; simp [rlM, Nat.mod_eq_of_lt u.2, Nat.mod_eq_of_lt i.2]
  have hbox0 : ∀ (u : Fin 8) (i : Fin 3),
      ((rlLo d0.rest u i : ℚ) : ℝ) ≤ (M0 u i : ℝ) - w0 * E0 u i ∧
        (M0 u i : ℝ) - w0 * E0 u i ≤ ((rlLo d0.rest u i : ℚ) : ℝ) + ((rlWd d0.rest u i : ℚ) : ℝ) := by
    intro u i
    have h := hadm.1 u u.2 i i.2
    rw [hM0v] at h
    rw [hE0c, hw0def]
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  have hwdR : ∀ u i, 0 ≤ rlWdR dR u i := by
    intro u i; unfold rlWdR; split_ifs <;> linarith [(hG2 0).trans (hG2V 0), (hF1 0).trans (hF1V 0)]
  have hf01 : ∀ i, 0 ≤ f i ∧ f i ≤ 1 := fun i => ⟨hf0 i, hf1 i⟩
  have hentB : ∀ u i, 0 ≤ tcEntR x f Y (uIdx ds u) i ∧ tcEntR x f Y (uIdx ds u) i ≤ 1 := fun u i =>
    tcEntR_bounds hx01 hf01 hY01 _ i
  have hclose : ∀ u i, |M u i - (fun u i => (M0 u i : ℝ)) u i| ≤ 3 * ω' := by
    intro u i
    simp only [hMdef]
    have hb := hbox0 u i
    have hl := rlLo_flD_le hn dR hω hwin u i
    rw [rlUFlD_rest] at hb
    have he := tcEntR_close (Y := Y) hω'0 hxc hfc (uIdx ds u) i
    have hE : E0 u i = tcEntR (fun _ => x0) (fun _ => f0) Y (uIdx ds u) i := rfl
    have hm1 := le_max_left ((M0 u i : ℝ) - w0 * E0 u i) (rlLoR dR u i)
    have hm2 : max ((M0 u i : ℝ) - w0 * E0 u i) (rlLoR dR u i) ≤ (M0 u i : ℝ) - w0 * E0 u i + ω' :=
      max_le (by linarith) (by linarith [hb.1, hl.2])
    have hb1 := hentB u i
    have k1 : 0 ≤ (w - w0) * tcEntR x f Y (uIdx ds u) i := mul_nonneg (by linarith) hb1.1
    have k2 : (w - w0) * tcEntR x f Y (uIdx ds u) i ≤ ω' := by
      have := mul_le_mul hwc2 hb1.2 hb1.1 hn1; linarith
    have k3 : 0 ≤ w0 * (tcEntR x f Y (uIdx ds u) i - E0 u i) := mul_nonneg hw00 (by rw [hE]; linarith [he.1])
    have k4 : w0 * (tcEntR x f Y (uIdx ds u) i - E0 u i) ≤ ω' := by
      have := mul_le_mul hw01 (show tcEntR x f Y (uIdx ds u) i - E0 u i ≤ ω' by rw [hE]; linarith [he.2])
        (by rw [hE]; linarith [he.1]) zero_le_one
      linarith
    have ka : w * tcEntR x f Y (uIdx ds u) i - w0 * E0 u i =
        (w - w0) * tcEntR x f Y (uIdx ds u) i + w0 * (tcEntR x f Y (uIdx ds u) i - E0 u i) := by ring
    rw [abs_le]; constructor <;> linarith
  have hstar : lp3CStar ∈ lp3Profiles := by decide +kernel
  -- the budget range
  set b := C.box.tcb with hb
  set Lx : ℝ := ((tcLx b : ℚ) : ℝ) with hLx
  set Hx : ℝ := ((tcHx b : ℚ) : ℝ) with hHx
  have hLx0 : 0 ≤ Lx := by rw [hLx]; exact_mod_cast le_max_left _ _
  have hHx1 : Hx ≤ 1 := by rw [hHx]; exact_mod_cast min_le_left _ _
  have hxr : ∀ i, Lx ≤ x i ∧ x i ≤ Hx := by
    intro i
    have h1 := hxc i
    constructor
    · rw [hLx]; unfold tcLx; push_cast
      refine max_le (hx01 i).1 ?_
      have : (((C.box.xlo : ℚ) / C.box.Q : ℚ) : ℝ) ≤ x0 := by rw [hx0def]; exact_mod_cast hxlo
      simp only [hb, UBox.tcb]; push_cast at this ⊢; linarith
    · rw [hHx]; unfold tcHx; push_cast
      refine le_min (hx1 i) ?_
      have : x0 ≤ (((C.box.xhi : ℚ) / C.box.Q : ℚ) : ℝ) := by rw [hx0def]; exact_mod_cast hxhi
      simp only [hb, UBox.tcb]; push_cast at this ⊢; linarith
  have hdes := heff.2.1
  set dg : Fin 8 → Fin 3 := fun R => ⟨tcDesig C.dg R % 3, Nat.mod_lt _ (by norm_num)⟩ with hdg
  set B : ℝ := (((C.Bn : ℚ) / C.Bd : ℚ) : ℝ) with hBdef
  refine ⟨⟨C.Ts, M, Y, c0, B, dg, Lx, Hx⟩, x0, ?_, hTs, hc45, hc0G,
    fun i => ⟨(hxc i).1, by linarith [(hxc i).2]⟩,
    fun u i => ?_, hY01, ?_, fun C' hC' hne => ?_, fun u hu hne => ?_, fun R i hR hbit => ?_, ?_,
    hLx0, hHx1, hxr, fun c hc0 hc8 => ?_⟩
  · have h1 : ((thr : ℚ) : ℝ) ≤ x0 := by rw [hx0max]; exact le_max_left _ _
    rw [hthrR] at h1; linarith
  · -- the box
    simp only
    have hb := hbox0 u i
    have hl := rlLo_flD_le hn dR hω hwin u i
    have hwd := rlWd_flD_le hn dR u i
    rw [rlUFlD_rest] at hb
    have e1 : M u i - w * tcEntR x f Y (uIdx ds u) i = max ((M0 u i : ℝ) - w0 * E0 u i) (rlLoR dR u i) := by
      simp only [hMdef]; ring
    rw [e1]
    exact ⟨le_max_right _ _, max_le (by linarith [hb.2, hl.1]) (by linarith [hwdR u i])⟩
  · -- (V)
    simp only
    have hp := abs_le.1 (rlV8R_pert hstar C.Ts hclose)
    rw [rlV8R_cast] at hp
    have hv : 8 * c0 * (5 / 3 - 1 / 80) ≤ ((rlV8 lp3CStar C.Ts M0 : ℚ) : ℝ) := by
      have h : ((8 * d0.G1 * (5 / 3 - 1 / 80) : ℚ) : ℝ) ≤ ((rlV8 lp3CStar C.Ts M0 : ℚ) : ℝ) := by
        exact_mod_cast hadm.2.2.1
      push_cast at h; rw [hc0def]; linarith
    linarith [hp.1]
  · -- (G)
    simp only
    have hcc : (1 : ℝ) ≤ (cd_cc 3 C' : ℝ) := by
      have := profiles3_cc_pos C' (by simpa [profiles3] using hC'); exact_mod_cast this
    have hg : 1 / 20 * c0 * (1 / 80) ≤ ((rlV8 C' C.Ts M0 : ℚ) : ℝ) / (8 * (cd_cc 3 C' : ℝ)) -
        ((rlV8 lp3CStar C.Ts M0 : ℚ) : ℝ) / 40 := by
      have h : ((1 / 20 * d0.G1 * (1 / 80) : ℚ) : ℝ) ≤
          ((rlV8 C' C.Ts M0 / (8 * (cd_cc 3 C' : ℚ)) - rlV8 lp3CStar C.Ts M0 / 40 : ℚ) : ℝ) := by
        exact_mod_cast hadm.2.2.2.1 C' hC' hne
      push_cast at h; rw [hc0def]; linarith
    have pc := rlV8R_pert hC' C.Ts hclose
    rw [rlV8R_cast] at pc
    have ps := rlV8R_pert hstar C.Ts hclose
    rw [rlV8R_cast] at ps
    have e1 : |rlV8R C' C.Ts M / (8 * (cd_cc 3 C' : ℝ)) - ((rlV8 C' C.Ts M0 : ℚ) : ℝ) / (8 * (cd_cc 3 C' : ℝ))| ≤
        36 * (3 * ω') / 8 := by
      have hc8 : (0 : ℝ) < 8 * (cd_cc 3 C' : ℝ) := by linarith
      rw [← sub_div, abs_div, abs_of_pos hc8, div_le_iff₀ hc8]
      nlinarith
    have e2 : |rlV8R lp3CStar C.Ts M / 40 - ((rlV8 lp3CStar C.Ts M0 : ℚ) : ℝ) / 40| ≤ 36 * (3 * ω') / 40 := by
      rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 40)]
      linarith
    have e1' := abs_le.1 e1
    have e2' := abs_le.1 e2
    linarith [e1'.1, e2'.2]
  · -- (P)
    simp only at hne ⊢
    have a1 := abs_le.1 (rlPSR_pert hclose C.Ts)
    have a2 := abs_le.1 (rlPSR_pert hclose u)
    rw [rlPSR_cast] at a1 a2
    have hp : (1 : ℝ) / 20 ≤ ((rlPS M0 C.Ts : ℚ) : ℝ) - ((rlPS M0 u : ℚ) : ℝ) := by
      have h : ((1 / 20 : ℚ) : ℝ) ≤ ((rlPS M0 C.Ts - rlPS M0 u : ℚ) : ℝ) := by
        exact_mod_cast hadm.2.2.2.2 u hu hne
      push_cast at h; linarith
    linarith [a1.1, a2.2]
  · -- (E2)
    simp only [hYdef]
    have h := heff.1 R R.2 hR i i.2 hbit
    have e : rlM Y0 R i = Y0 R i := by simp [rlM, Nat.mod_eq_of_lt R.2, Nat.mod_eq_of_lt i.2]
    rw [e] at h
    have h' : ((Y0 R i : ℚ) : ℝ) ≤ ((d0.x - 1 / 80 / 100 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    rw [hx0def]; linarith
  · -- the designated budget
    simp only
    have hsum := heff.2.2
    have hdgv : ∀ R : Fin 8, (R : ℕ) ≠ 0 → ((dg R : Fin 3) : ℕ) = tcDesig C.dg R := by
      intro R hR
      simp only [hdg]
      exact Nat.mod_eq_of_lt (hdes R R.2 hR)
    have hterm : ∀ R : Fin 8, (R : ℕ) ≠ 0 →
        tcEntR x f Y R (dg R) ≤ ((rlUEnt d0 Y0 R (tcDesig C.dg R) : ℚ) : ℝ) + ω' := by
      intro R hR
      have he := tcEntR_close (Y := Y) hω'0 hxc hfc R (dg R)
      have h1 := rlUEnt_cast d0 Y0 R (dg R)
      rw [hdgv R hR] at h1
      rw [h1]
      linarith [he.2]
    rw [sum_erase0_fin8]
    have hs' : (((∑ R ∈ Finset.range 7, rlUEnt d0 Y0 (R + 1) (tcDesig C.dg (R + 1)) : ℚ)) : ℝ) ≤
        B - 1 / 500 := by
      have h : (((∑ R ∈ Finset.range 7, rlUEnt d0 Y0 (R + 1) (tcDesig C.dg (R + 1)) : ℚ)) : ℝ) ≤
          ((((C.Bn : ℚ) / C.Bd - 1 / 500 : ℚ)) : ℝ) := by exact_mod_cast hsum
      rw [hBdef]; push_cast at h ⊢; linarith
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hs'
    push_cast at hs'
    have t1 := hterm 1 (by decide)
    have t2 := hterm 2 (by decide)
    have t3 := hterm 3 (by decide)
    have t4 := hterm 4 (by decide)
    have t5 := hterm 5 (by decide)
    have t6 := hterm 6 (by decide)
    have t7 := hterm 7 (by decide)
    norm_num at hs' t1 t2 t3 t4 t5 t6 t7
    linarith
  · -- the budget
    obtain ⟨-, h2⟩ := hbud c hc0 hc8
    rw [tcEhi_cast] at h2
    exact h2

end Census
end IIT
