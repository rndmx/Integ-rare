/-
Census, B1 LTBetaHi, RL-u certificate, part 5: from the vertex witnesses of a cell to a witness at every point.

`UGood ds t B Ts desig d`: some `(M, Y)` is RL-u admissible at `d` with the effect conditions. A point of a cell is
reached from the vertices `uVertsN` by one-dimensional steps: `(x, f)` bilinearly (fixed `w`), then `w`
(`rlU_wseg`), then the second factor `(G2, F2, V2 = max(G2, F2))` by `tc_factor`, then `G1` (fixed `F1`), then `F1`
piecewise linearly (`V1 = max(1, F1)`, break point `F1 = 1`), finally monotonicity in `V1, V2`.
-/
import IIT.Census.B1LTHiCertUConv
import IIT.Census.B1LTHiCertTcDecomp

namespace IIT
namespace Census

/-- Some RL-u table at `d`. -/
def UGood (ds : Bool) (t B : ℚ) (Ts : ℕ) (desig : ℕ → ℕ) (d : RLUD) : Prop :=
  ∃ M Y : Fin 8 → Fin 3 → ℚ, rlUAdm ds d t Ts M Y ∧ rlUEff d t B desig Y

/-- The data of a point on the lower envelope. -/
def uD (G1 F1 G2 F2 w x f : ℚ) : RLUD := ⟨G1, F1, G2, F2, max 1 F1, max G2 F2, w, x, f⟩

section Good

variable {ds : Bool} {t B : ℚ} {Ts : ℕ} {desig : ℕ → ℕ}

lemma UGood.congr {d e : RLUD} (hd : UGood ds t B Ts desig d) (he : d = e) : UGood ds t B Ts desig e := he ▸ hd

lemma UGood.conv {d e : RLUD} (hd : UGood ds t B Ts desig d) (he : UGood ds t B Ts desig e) (hw : d.w = e.w)
    {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : UGood ds t B Ts desig (d.lc a b e) := by
  obtain ⟨M, Y, h1, h2⟩ := hd
  obtain ⟨M', Y', h1', h2'⟩ := he
  exact ⟨_, _, rlUAdm_conv h1 h1' hw ha hb hab, rlUEff_conv h2 h2' ha hb hab⟩

lemma UGood.monoV {d : RLUD} (hd : UGood ds t B Ts desig d) {V1 V2 : ℚ} (h1 : d.V1 ≤ V1) (h2 : d.V2 ≤ V2) :
    UGood ds t B Ts desig ⟨d.G1, d.F1, d.G2, d.F2, V1, V2, d.w, d.x, d.f⟩ := by
  obtain ⟨M, Y, ha, he⟩ := hd
  exact ⟨M, Y, rlUAdm_monoV ha h1 h2, rlUEff_monoV he V1 V2⟩

/-- The bilinear step in `(x, f)` (fixed `w`). -/
lemma u_xf (G1 F1 G2 F2 w : ℚ) {x0 x1 f0 f1 x f : ℚ} (hx0 : x0 ≤ x) (hx1 : x ≤ x1) (hf0 : f0 ≤ f)
    (hf1 : f ≤ f1) (h00 : UGood ds t B Ts desig (uD G1 F1 G2 F2 w x0 f0))
    (h01 : UGood ds t B Ts desig (uD G1 F1 G2 F2 w x0 f1)) (h10 : UGood ds t B Ts desig (uD G1 F1 G2 F2 w x1 f0))
    (h11 : UGood ds t B Ts desig (uD G1 F1 G2 F2 w x1 f1)) : UGood ds t B Ts desig (uD G1 F1 G2 F2 w x f) := by
  have lin : ∀ x x' f f' l, (uD G1 F1 G2 F2 w x f).lc (1 - l) l (uD G1 F1 G2 F2 w x' f') =
      uD G1 F1 G2 F2 w ((1 - l) * x + l * x') ((1 - l) * f + l * f') := by
    intro x x' f f' l
    apply RLUD.ext' <;> simp only [RLUD.lc, uD] <;> ring
  have sx : ∀ fc, UGood ds t B Ts desig (uD G1 F1 G2 F2 w x0 fc) → UGood ds t B Ts desig (uD G1 F1 G2 F2 w x1 fc) →
      UGood ds t B Ts desig (uD G1 F1 G2 F2 w x fc) := by
    intro fc q0 q1
    refine tc_seg (Q := fun z => UGood ds t B Ts desig (uD G1 F1 G2 F2 w z fc)) (fun l hl0 hl1 => ?_) hx0 hx1
    have := (q0.conv q1 rfl (a := 1 - l) (b := l) (by linarith) hl0 (by ring)).congr (lin x0 x1 fc fc l)
    rwa [show (1 - l) * fc + l * fc = fc by ring] at this
  have q0 := sx f0 h00 h10
  have q1 := sx f1 h01 h11
  refine tc_seg (Q := fun z => UGood ds t B Ts desig (uD G1 F1 G2 F2 w x z)) (fun l hl0 hl1 => ?_) hf0 hf1
  have := (q0.conv q1 rfl (a := 1 - l) (b := l) (by linarith) hl0 (by ring)).congr (lin x x f0 f1 l)
  rwa [show (1 - l) * x + l * x = x by ring] at this

/-- The `w` step. -/
lemma u_w (G1 F1 G2 F2 x f : ℚ) {w0 w1 w : ℚ} (hw00 : 0 ≤ w0) (hw0 : w0 ≤ w) (hw1 : w ≤ w1)
    (h0 : UGood ds t B Ts desig (uD G1 F1 G2 F2 w0 x f)) (h1 : UGood ds t B Ts desig (uD G1 F1 G2 F2 w1 x f)) :
    UGood ds t B Ts desig (uD G1 F1 G2 F2 w x f) := by
  refine tc_seg (Q := fun z => UGood ds t B Ts desig (uD G1 F1 G2 F2 z x f)) (fun l hl0 hl1 => ?_) hw0 hw1
  obtain ⟨M, Y, a1, e1⟩ := h0
  obtain ⟨M', Y', a2, e2⟩ := h1
  have := rlU_wseg (d := uD G1 F1 G2 F2 0 x f) (w := w0) (w' := w1) hw00 (hw00.trans (hw0.trans hw1))
    ⟨a1, e1⟩ ⟨a2, e2⟩ (a := 1 - l) (b := l) (by linarith) hl0 (by ring)
  exact this

/-- Convexity of the second factor on each side of the diagonal (fixed `w`). -/
lemma u_conv2 (G1 F1 w x f : ℚ) {G F G' F' l : ℚ} (hs : (F ≤ G ∧ F' ≤ G') ∨ (G ≤ F ∧ G' ≤ F')) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) (q : UGood ds t B Ts desig (uD G1 F1 G F w x f))
    (q' : UGood ds t B Ts desig (uD G1 F1 G' F' w x f)) :
    UGood ds t B Ts desig (uD G1 F1 ((1 - l) * G + l * G') ((1 - l) * F + l * F') w x f) := by
  refine (q.conv q' rfl (a := 1 - l) (b := l) (by linarith) hl0 (by ring)).congr ?_
  apply RLUD.ext' <;> simp only [RLUD.lc, uD] <;> try ring1
  rcases hs with ⟨h, h'⟩ | ⟨h, h'⟩
  · rw [max_eq_left h, max_eq_left h', max_eq_left (by nlinarith)]
  · rw [max_eq_right h, max_eq_right h', max_eq_right (by nlinarith)]

/-- The `G1` step (fixed `F1`, `w`). -/
lemma u_g1 (F1 G2 F2 w x f : ℚ) {g0 g1 G : ℚ} (h0' : g0 ≤ G) (h1' : G ≤ g1)
    (q0 : UGood ds t B Ts desig (uD g0 F1 G2 F2 w x f)) (q1 : UGood ds t B Ts desig (uD g1 F1 G2 F2 w x f)) :
    UGood ds t B Ts desig (uD G F1 G2 F2 w x f) := by
  refine tc_seg (Q := fun z => UGood ds t B Ts desig (uD z F1 G2 F2 w x f)) (fun l hl0 hl1 => ?_) h0' h1'
  refine (q0.conv q1 rfl (a := 1 - l) (b := l) (by linarith) hl0 (by ring)).congr ?_
  apply RLUD.ext' <;> simp only [RLUD.lc, uD] <;> ring

/-- The `F1` step on one linear piece of `max 1 F1` (fixed `w`). -/
lemma u_f1 (G1 G2 F2 w x f : ℚ) {p0 p1 F : ℚ} (hs : (p0 ≤ 1 ∧ p1 ≤ 1) ∨ (1 ≤ p0 ∧ 1 ≤ p1)) (h0' : p0 ≤ F)
    (h1' : F ≤ p1) (q0 : UGood ds t B Ts desig (uD G1 p0 G2 F2 w x f))
    (q1 : UGood ds t B Ts desig (uD G1 p1 G2 F2 w x f)) : UGood ds t B Ts desig (uD G1 F G2 F2 w x f) := by
  refine tc_seg (Q := fun z => UGood ds t B Ts desig (uD G1 z G2 F2 w x f)) (fun l hl0 hl1 => ?_) h0' h1'
  refine (q0.conv q1 rfl (a := 1 - l) (b := l) (by linarith) hl0 (by ring)).congr ?_
  apply RLUD.ext' <;> simp only [RLUD.lc, uD] <;> try ring1
  rcases hs with ⟨h, h'⟩ | ⟨h, h'⟩
  · rw [max_eq_left h, max_eq_left h', max_eq_left (by nlinarith)]; ring
  · rw [max_eq_right h, max_eq_right h', max_eq_right (by nlinarith)]

end Good

lemma uVertsN_mem {b : UBox} {g1 f1 w x f : ℕ} {p2 : ℕ × ℕ} (hg : g1 = b.g1lo ∨ g1 = b.g1hi)
    (hf1 : f1 ∈ uF1Pts b.f1lo b.f1hi b.Q) (h2 : p2 ∈ tcFacPts b.g2lo (some b.g2hi) b.f2lo (some b.f2hi))
    (hw : w = b.wlo ∨ w = b.whi) (hx : x = b.xlo ∨ x = b.xhi) (hf : f = b.flo ∨ f = b.fhi) :
    (⟨g1, f1, p2.1, p2.2, max b.Q f1, max p2.1 p2.2, w, x, f⟩ : RLUN) ∈ uVertsN b := by
  simp only [uVertsN, List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨g1, hg, f1, hf1, p2, h2, w, hw, x, hx, f, hf, rfl⟩

lemma uVtx_toQ {Q : ℕ} (hQ : 0 < Q) (g1 f1 w x f : ℕ) (p2 : ℕ × ℕ) :
    (⟨g1, f1, p2.1, p2.2, max Q f1, max p2.1 p2.2, w, x, f⟩ : RLUN).toQ Q =
      uD ((g1 : ℚ) / Q) ((f1 : ℚ) / Q) ((p2.1 : ℚ) / Q) ((p2.2 : ℚ) / Q) ((w : ℚ) / Q) ((x : ℚ) / Q)
        ((f : ℚ) / Q) := by
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  have e : max (Q : ℚ) (f1 : ℚ) / Q = max 1 ((f1 : ℚ) / Q) := by
    rw [← max_div_div_right hQq.le, div_self hQq.ne']
  simp only [RLUN.toQ, uD, Nat.cast_max, e]
  congr 1
  rw [max_div_div_right hQq.le]

set_option maxHeartbeats 1000000 in
/-- **Every point of a checked RL-u cell is good** (`V1 ≥ max(1, F1)`, `V2 ≥ max(G2, F2)`). -/
theorem uCell_good {tn td : ℕ} (htd : 0 < td) {C : UCell} (hC : uCellOK tn td C = true) (d : RLUD)
    (hG1 : (C.box.g1lo : ℚ) / C.box.Q ≤ d.G1 ∧ d.G1 ≤ (C.box.g1hi : ℚ) / C.box.Q)
    (hF1 : (C.box.f1lo : ℚ) / C.box.Q ≤ d.F1 ∧ d.F1 ≤ (C.box.f1hi : ℚ) / C.box.Q)
    (hG2 : (C.box.g2lo : ℚ) / C.box.Q ≤ d.G2 ∧ d.G2 ≤ (C.box.g2hi : ℚ) / C.box.Q)
    (hF2 : (C.box.f2lo : ℚ) / C.box.Q ≤ d.F2 ∧ d.F2 ≤ (C.box.f2hi : ℚ) / C.box.Q)
    (hw : (C.box.wlo : ℚ) / C.box.Q ≤ d.w ∧ d.w ≤ (C.box.whi : ℚ) / C.box.Q)
    (hx : (C.box.xlo : ℚ) / C.box.Q ≤ d.x ∧ d.x ≤ (C.box.xhi : ℚ) / C.box.Q)
    (hf : (C.box.flo : ℚ) / C.box.Q ≤ d.f ∧ d.f ≤ (C.box.fhi : ℚ) / C.box.Q)
    (hV1 : max 1 d.F1 ≤ d.V1) (hV2 : max d.G2 d.F2 ≤ d.V2) :
    UGood C.ds ((tn : ℚ) / td) ((C.Bn : ℚ) / C.Bd) C.Ts (tcDesig C.dg) d := by
  obtain ⟨hV, -, hQ, -, -, hf1o, -, -, -, -, -, -⟩ := uCellOK_sound htd hC
  set b := C.box with hb
  set P := UGood C.ds ((tn : ℚ) / td) ((C.Bn : ℚ) / C.Bd) C.Ts (tcDesig C.dg) with hP
  have hQq : (0 : ℚ) < b.Q := by exact_mod_cast hQ
  set q : ℕ → ℚ := fun n => (n : ℚ) / b.Q with hq
  have qle : ∀ m n : ℕ, q m ≤ q n ↔ m ≤ n := fun m n => by
    simp only [hq]; rw [div_le_div_iff_of_pos_right hQq]; exact Nat.cast_le
  have qmax : ∀ m n : ℕ, q (max m n) = max (q m) (q n) := fun m n => by
    simp only [hq, Nat.cast_max, max_div_div_right hQq.le]
  have qmin : ∀ m n : ℕ, q (min m n) = min (q m) (q n) := fun m n => by
    simp only [hq, Nat.cast_min, min_div_div_right hQq.le]
  have qQ : q b.Q = 1 := by simp only [hq]; exact div_self hQq.ne'
  have q0 : ∀ n, 0 ≤ q n := fun n => by simp only [hq]; positivity
  -- step 0: vertices
  have hvert : ∀ g1 f1 w x f : ℕ, ∀ p2 ∈ tcFacPts b.g2lo (some b.g2hi) b.f2lo (some b.f2hi),
      (g1 = b.g1lo ∨ g1 = b.g1hi) → f1 ∈ uF1Pts b.f1lo b.f1hi b.Q → (w = b.wlo ∨ w = b.whi) →
      (x = b.xlo ∨ x = b.xhi) → (f = b.flo ∨ f = b.fhi) →
      P (uD (q g1) (q f1) (q p2.1) (q p2.2) (q w) (q x) (q f)) := by
    intro g1 f1 w x f p2 h2 hg hf1 hw' hx' hf'
    have := hV _ (List.mem_map_of_mem (f := fun v => v.toQ b.Q) (uVertsN_mem hg hf1 h2 hw' hx' hf'))
    rw [uVtx_toQ hQ] at this
    exact this
  -- step A: (x, f), then w
  have hA : ∀ g1 f1 : ℕ, ∀ p2 ∈ tcFacPts b.g2lo (some b.g2hi) b.f2lo (some b.f2hi),
      (g1 = b.g1lo ∨ g1 = b.g1hi) → f1 ∈ uF1Pts b.f1lo b.f1hi b.Q →
      P (uD (q g1) (q f1) (q p2.1) (q p2.2) d.w d.x d.f) := by
    intro g1 f1 p2 h2 hg hf1
    have hw' : ∀ w, (w = b.wlo ∨ w = b.whi) → P (uD (q g1) (q f1) (q p2.1) (q p2.2) (q w) d.x d.f) :=
      fun w hw' => u_xf _ _ _ _ _ hx.1 hx.2 hf.1 hf.2
        (hvert g1 f1 w b.xlo b.flo p2 h2 hg hf1 hw' (Or.inl rfl) (Or.inl rfl))
        (hvert g1 f1 w b.xlo b.fhi p2 h2 hg hf1 hw' (Or.inl rfl) (Or.inr rfl))
        (hvert g1 f1 w b.xhi b.flo p2 h2 hg hf1 hw' (Or.inr rfl) (Or.inl rfl))
        (hvert g1 f1 w b.xhi b.fhi p2 h2 hg hf1 hw' (Or.inr rfl) (Or.inr rfl))
    exact u_w _ _ _ _ _ _ (q0 _) hw.1 hw.2 (hw' b.wlo (Or.inl rfl)) (hw' b.whi (Or.inr rfl))
  -- step B: the second factor
  have S2 := tcFacPts_spec b.g2lo b.f2lo (some b.g2hi) (some b.f2hi)
  have hB : ∀ g1 f1 : ℕ, (g1 = b.g1lo ∨ g1 = b.g1hi) → f1 ∈ uF1Pts b.f1lo b.f1hi b.Q →
      P (uD (q g1) (q f1) d.G2 d.F2 d.w d.x d.f) := by
    intro g1 f1 hg hf1
    refine tc_factor (fun G F => P (uD (q g1) (q f1) G F d.w d.x d.f)) (q b.g2lo) (q b.f2lo)
      (some (q b.g2hi)) (some (q b.f2hi))
      (fun G F G' F' l h h' hl0 hl1 qq qq' => u_conv2 _ _ _ _ _ (Or.inl ⟨h, h'⟩) hl0 hl1 qq qq')
      (fun G F G' F' l h h' hl0 hl1 qq qq' => u_conv2 _ _ _ _ _ (Or.inr ⟨h, h'⟩) hl0 hl1 qq qq')
      (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
      (hA g1 f1 (b.g2lo, b.f2lo) S2.1 hg hf1) ?_ ?_ ?_ ?_ ?_ (fun g _ h => by cases h) (fun f h => by cases h)
      hG2.1 hF2.1 ?_ ?_
    · intro g hg'; cases hg'; exact hA g1 f1 (b.g2hi, b.f2lo) (S2.2.1 b.g2hi rfl) hg hf1
    · intro f hf'; cases hf'; exact hA g1 f1 (b.g2lo, b.f2hi) (S2.2.2.1 b.f2hi rfl) hg hf1
    · intro g f hg' hf'; cases hg'; cases hf'
      exact hA g1 f1 (b.g2hi, b.f2hi) (S2.2.2.2.1 b.g2hi b.f2hi rfl rfl) hg hf1
    · intro hg' hf'
      have := hA g1 f1 (max b.g2lo b.f2lo, max b.g2lo b.f2lo) (S2.2.2.2.2.1 (fun g h => by
        cases h; have := hg' (q b.g2hi) rfl; rwa [← qmax, qle] at this)
        (fun f h => by cases h; have := hf' (q b.f2hi) rfl; rwa [← qmax, qle] at this)) hg hf1
      simpa only [qmax] using this
    · intro g f hg' hf' hm
      cases hg'; cases hf'
      have := hA g1 f1 (min b.g2hi b.f2hi, min b.g2hi b.f2hi)
        (S2.2.2.2.2.2.1 b.g2hi b.f2hi rfl rfl (by rwa [← qmax, ← qmin, qle] at hm)) hg hf1
      simpa only [qmin] using this
    · intro g hg'; cases hg'; exact hG2.2
    · intro f hf'; cases hf'; exact hF2.2
  -- step C: G1
  have hC1 : ∀ f1 : ℕ, f1 ∈ uF1Pts b.f1lo b.f1hi b.Q → P (uD d.G1 (q f1) d.G2 d.F2 d.w d.x d.f) :=
    fun f1 hf1 => u_g1 _ _ _ _ _ _ hG1.1 hG1.2 (hB b.g1lo f1 (Or.inl rfl) hf1) (hB b.g1hi f1 (Or.inr rfl) hf1)
  -- step D: F1, piecewise
  have hD : P (uD d.G1 d.F1 d.G2 d.F2 d.w d.x d.f) := by
    by_cases hcr : b.f1lo < b.Q ∧ b.Q < b.f1hi
    · have m0 : b.f1lo ∈ uF1Pts b.f1lo b.f1hi b.Q := by simp [uF1Pts, hcr]
      have m1 : b.Q ∈ uF1Pts b.f1lo b.f1hi b.Q := by simp [uF1Pts, hcr]
      have m2 : b.f1hi ∈ uF1Pts b.f1lo b.f1hi b.Q := by simp [uF1Pts, hcr]
      have l0 : q b.f1lo ≤ 1 := by rw [← qQ, qle]; exact hcr.1.le
      have l2 : 1 ≤ q b.f1hi := by rw [← qQ, qle]; exact hcr.2.le
      rcases le_total d.F1 1 with h1 | h1
      · have := u_f1 d.G1 d.G2 d.F2 d.w d.x d.f (Or.inl ⟨l0, le_of_eq qQ⟩) hF1.1 (qQ ▸ h1)
          (hC1 _ m0) (hC1 _ m1)
        exact this
      · have := u_f1 d.G1 d.G2 d.F2 d.w d.x d.f (Or.inr ⟨le_of_eq qQ.symm, l2⟩) (qQ ▸ h1) hF1.2
          (hC1 _ m1) (hC1 _ m2)
        exact this
    · have m0 : b.f1lo ∈ uF1Pts b.f1lo b.f1hi b.Q := by simp [uF1Pts, hcr]
      have m2 : b.f1hi ∈ uF1Pts b.f1lo b.f1hi b.Q := by simp [uF1Pts, hcr]
      have hs : (q b.f1lo ≤ 1 ∧ q b.f1hi ≤ 1) ∨ (1 ≤ q b.f1lo ∧ 1 ≤ q b.f1hi) := by
        rw [← qQ, qle, qle, qle, qle]
        rw [not_and_or, not_lt, not_lt] at hcr
        rcases hcr with h | h
        · exact Or.inr ⟨h, h.trans hf1o⟩
        · exact Or.inl ⟨hf1o.trans h, h⟩
      exact u_f1 d.G1 d.G2 d.F2 d.w d.x d.f hs hF1.1 hF1.2 (hC1 _ m0) (hC1 _ m2)
  -- step E: monotone in V1, V2
  have := hD.monoV (V1 := d.V1) (V2 := d.V2) hV1 hV2
  exact this.congr (by cases d; rfl)

end Census
end IIT
