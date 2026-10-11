/-
Census, B1 LTBetaHi, RL-tc certificate (W8 §8.1, (R1)), part 1e: from the vertex/ray witnesses of a cell to a
witness at every point of the cell.

`TcGood t B Ts desig d`: some `(M, Y)` is RL-tc admissible at `d` with the effect conditions. It is convex in `d`
(`TcGood.conv`), closed under the rays of the rest data (`TcGood.ray`) and monotone in `V1, V2`
(`TcGood.monoV`). A point of a cell is reached from the vertices of `tcVerts` by 1-D interpolations:
* (x, f) bilinearly from the four corners (`tc_corners`);
* each `(G, F, V = max(G, F))` factor by `tc_factor`: on each side of the diagonal `V` is linear, and the
  half-planes are swept by vertical segments whose ends lie on the box edges or on the diagonal, whose ends in
  turn are the points of `tcFacPts` (corners, the two ends of the diagonal segment); unbounded directions use the
  rays `(1,0,1)`, `(0,1,1)`, `(1,1,1)`.
Result: **`tcCell_good`** (every point of the box of a checked cell, with `V1 ≥ max(G1, F1)`,
`V2 ≥ max(G2, F2)`, is good).
-/
import IIT.Census.B1LTHiCertTcConv

namespace IIT
namespace Census

/-! ### The predicate and its closure properties -/

/-- Some RL-tc table at `d` (cause admissible and effect conditions). -/
def TcGood (t B : ℚ) (Ts : ℕ) (desig : ℕ → ℕ) (d : RLTcD) : Prop :=
  ∃ M Y : Fin 8 → Fin 3 → ℚ, rlTcAdm d t Ts M Y ∧ rlTcEff d t B desig Y

section Good

variable {t B : ℚ} {Ts : ℕ} {desig : ℕ → ℕ}

lemma RLTcD.ext' {d e : RLTcD} (h1 : d.G1 = e.G1) (h2 : d.F1 = e.F1) (h3 : d.G2 = e.G2) (h4 : d.F2 = e.F2)
    (h5 : d.V1 = e.V1) (h6 : d.V2 = e.V2) (h7 : d.x = e.x) (h8 : d.f = e.f) : d = e := by
  cases d; cases e; simp_all

lemma TcGood.conv {d e : RLTcD} (hd : TcGood t B Ts desig d) (he : TcGood t B Ts desig e) {a b : ℚ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : TcGood t B Ts desig (d.lc a b e) := by
  obtain ⟨M, Y, h1, h2⟩ := hd
  obtain ⟨M', Y', h1', h2'⟩ := he
  exact ⟨_, _, rlTcAdm_conv h1 h1' ha hb hab, rlTcEff_conv h2 h2' ha hb hab⟩

lemma TcGood.congr {d e : RLTcD} (hd : TcGood t B Ts desig d) (he : d = e) : TcGood t B Ts desig e :=
  he ▸ hd

lemma TcGood.ray {d : RLTcD} (hd : TcGood t B Ts desig d) {r : RLD} (hr : ∃ R, rlRay r Ts R) {μ : ℚ}
    (hμ : 0 ≤ μ) : TcGood t B Ts desig (d.addRay μ r) := by
  obtain ⟨M, Y, h1, h2⟩ := hd
  obtain ⟨R, hR⟩ := hr
  exact ⟨_, _, rlTcAdm_ray h1 hR hμ, rlTcEff_rest h2 μ r⟩

lemma TcGood.monoV {d : RLTcD} (hd : TcGood t B Ts desig d) {V1 V2 : ℚ} (h1 : d.V1 ≤ V1) (h2 : d.V2 ≤ V2) :
    TcGood t B Ts desig ⟨d.G1, d.F1, d.G2, d.F2, V1, V2, d.x, d.f⟩ := by
  obtain ⟨M, Y, ha, he⟩ := hd
  exact ⟨M, Y, rlTcAdm_monoV ha h1 h2, rlTcEff_monoV he V1 V2⟩

end Good

/-! ### One-dimensional interpolation -/

/-- A predicate that holds at every convex combination of `z0, z1` holds between them. -/
lemma tc_seg {Q : ℚ → Prop} {z0 z1 z : ℚ} (hQ : ∀ l, 0 ≤ l → l ≤ 1 → Q ((1 - l) * z0 + l * z1))
    (h0 : z0 ≤ z) (h1 : z ≤ z1) : Q z := by
  rcases eq_or_lt_of_le (h0.trans h1) with he | hlt
  · have hz : z = (1 - 0) * z0 + 0 * z1 := by
      have : z = z0 := le_antisymm (he ▸ h1) h0
      rw [this]; ring
    rw [hz]; exact hQ 0 le_rfl zero_le_one
  · have hd : 0 < z1 - z0 := by linarith
    have hl0 : 0 ≤ (z - z0) / (z1 - z0) := div_nonneg (by linarith) hd.le
    have hl1 : (z - z0) / (z1 - z0) ≤ 1 := (div_le_one hd).2 (by linarith)
    have hz : (1 - (z - z0) / (z1 - z0)) * z0 + (z - z0) / (z1 - z0) * z1 = z := by
      field_simp; ring
    have := hQ _ hl0 hl1
    rwa [hz] at this

/-! ### The factor lemma (one `(G, F, V = max(G, F))` factor) -/

/-- The half `F ≤ G` of the factor lemma. -/
lemma tc_factor_half (Q : ℚ → ℚ → Prop) (g0 f0 : ℚ) (g1 f1 : Option ℚ)
    (hconv : ∀ G F G' F' l, F ≤ G → F' ≤ G' → 0 ≤ l → l ≤ 1 → Q G F → Q G' F' →
      Q ((1 - l) * G + l * G') ((1 - l) * F + l * F'))
    (hray : g1 = none → ∀ G F μ, F ≤ G → 0 ≤ μ → Q G F → Q (G + μ) F)
    (hray11 : g1 = none → f1 = none → ∀ G F μ, 0 ≤ μ → Q G F → Q (G + μ) (F + μ))
    (H1 : Q g0 f0) (H2 : ∀ g, g1 = some g → Q g f0) (H3 : ∀ f, f1 = some f → Q g0 f)
    (H4 : ∀ g f, g1 = some g → f1 = some f → Q g f)
    (H5 : (∀ g, g1 = some g → max g0 f0 ≤ g) → (∀ f, f1 = some f → max g0 f0 ≤ f) →
      Q (max g0 f0) (max g0 f0))
    (H6 : ∀ g f, g1 = some g → f1 = some f → max g0 f0 ≤ min g f → Q (min g f) (min g f))
    (H7 : ∀ g, g1 = some g → f1 = none → max g0 f0 ≤ g → Q g g)
    (H8 : ∀ f, g1 = none → f1 = some f → max g0 f0 ≤ f → Q f f)
    {G F : ℚ} (hG0 : g0 ≤ G) (hF0 : f0 ≤ F) (hG1 : ∀ g, g1 = some g → G ≤ g)
    (hF1 : ∀ f, f1 = some f → F ≤ f) (hFG : F ≤ G) : Q G F := by
  -- segments with one coordinate fixed
  have segG : ∀ (F0 G0 G1 G : ℚ), F0 ≤ G0 → G0 ≤ G → G ≤ G1 → Q G0 F0 → Q G1 F0 → Q G F0 := by
    intro F0 G0 G1 G hF h1 h2 q0 q1
    refine tc_seg (Q := fun z => Q z F0) (fun l hl0 hl1 => ?_) h1 h2
    have := hconv G0 F0 G1 F0 l hF (hF.trans (h1.trans h2)) hl0 hl1 q0 q1
    rwa [show (1 - l) * F0 + l * F0 = F0 by ring] at this
  have segF : ∀ (G0 F0 F1 F : ℚ), F0 ≤ F → F ≤ F1 → F1 ≤ G0 → Q G0 F0 → Q G0 F1 → Q G0 F := by
    intro G0 F0 F1 F h0 h1 h2 q0 q1
    refine tc_seg (Q := fun z => Q G0 z) (fun l hl0 hl1 => ?_) h0 h1
    have := hconv G0 F0 G0 F1 l ((h0.trans h1).trans h2) h2 hl0 hl1 q0 q1
    rwa [show (1 - l) * G0 + l * G0 = G0 by ring] at this
  have segD : ∀ (a b z : ℚ), a ≤ z → z ≤ b → Q a a → Q b b → Q z z := by
    intro a b z h0 h1 q0 q1
    exact tc_seg (Q := fun z => Q z z) (fun l hl0 hl1 => hconv a a b b l le_rfl le_rfl hl0 hl1 q0 q1) h0 h1
  set a := max g0 f0 with ha
  have hag : g0 ≤ a := le_max_left _ _
  have haf : f0 ≤ a := le_max_right _ _
  have haG : a ≤ G := max_le hG0 (hF0.trans hFG)
  rcases g1 with _ | g
  · -- `G` unbounded: go left to `G' = max(g0, F)` and add the ray `(1, 0, 1)`
    set G' := max g0 F with hG'
    have hG'G : G' ≤ G := max_le hG0 hFG
    have hFG' : F ≤ G' := le_max_right _ _
    have hQ' : Q G' F := by
      rcases le_total F g0 with hF | hF
      · rw [hG', max_eq_left hF]
        -- left edge `(g0, F)`, `F ∈ [f0, min(g0, f1)]`
        have hag0 : a = g0 := max_eq_left (hF0.trans hF)
        rcases f1 with _ | f
        · have q5 : Q g0 g0 := by
            have := H5 (fun g h => by cases h) (fun f h => by cases h); rwa [hag0] at this
          exact segF g0 f0 g0 F hF0 hF le_rfl H1 q5
        · rcases le_total f g0 with hfg | hfg
          · exact segF g0 f0 f F hF0 (hF1 f rfl) hfg H1 (H3 f rfl)
          · have q5 : Q g0 g0 := by
              have := H5 (fun g h => by cases h) (fun f' h => by cases h; rw [hag0]; exact hfg)
              rwa [hag0] at this
            exact segF g0 f0 g0 F hF0 hF le_rfl H1 q5
      · rw [hG', max_eq_right hF]
        -- diagonal `(F, F)`, `F ≥ a`
        have haF : a ≤ F := max_le hF hF0
        rcases f1 with _ | f
        · have q5 := H5 (fun g h => by cases h) (fun f h => by cases h)
          have := hray11 rfl rfl a a (F - a) (by linarith) q5
          rwa [show a + (F - a) = F by ring] at this
        · have q5 := H5 (fun g h => by cases h) (fun f' h => by cases h; exact haF.trans (hF1 f rfl))
          have q8 := H8 f rfl rfl (haF.trans (hF1 f rfl))
          exact segD a f F haF (hF1 f rfl) q5 q8
    have := hray rfl G' F (G - G') hFG' (by linarith) hQ'
    rwa [show G' + (G - G') = G by ring] at this
  · -- `G ≤ g`: vertical segment at `G` from the bottom edge to the top edge or the diagonal
    have hGg : G ≤ g := hG1 g rfl
    -- bottom point `(G, f0)`
    have qbot : Q G f0 := by
      have hl : Q a f0 := by
        rcases le_total f0 g0 with h | h
        · rw [ha, max_eq_left h]; exact H1
        · have q5 := H5 (fun g' h' => by cases h'; exact haG.trans hGg)
            (fun f' h' => max_le (h.trans (hF0.trans (hF1 f' h'))) (hF0.trans (hF1 f' h')))
          have : a = f0 := max_eq_right h
          rw [this] at q5 ⊢; exact q5
      exact segG f0 a g G haf haG hGg hl (H2 g rfl)
    -- top point `(G, Ft)`
    rcases f1 with _ | f
    · -- diagonal point `(G, G)`
      have q5 := H5 (fun g' h' => by cases h'; exact haG.trans hGg) (fun f h => by cases h)
      have q7 := H7 g rfl rfl (haG.trans hGg)
      have qtop := segD a g G haG hGg q5 q7
      exact segF G f0 G F hF0 hFG le_rfl qbot qtop
    · have hFf : F ≤ f := hF1 f rfl
      rcases lt_or_ge f G with hfG | hGf
      · -- top edge `(G, f)`
        have qt : Q G f := by
          rcases le_total f g0 with h | h
          · exact segG f g0 g G h hG0 hGg (H3 f rfl) (H4 g f rfl rfl)
          · have hmin : min g f = f := min_eq_right (hfG.le.trans hGg)
            have haf' : a ≤ min g f := by rw [hmin]; exact max_le h (hF0.trans hFf)
            have q6 := H6 g f rfl rfl haf'
            rw [hmin] at q6
            exact segG f f g G le_rfl hfG.le hGg q6 (H4 g f rfl rfl)
        exact segF G f0 f F hF0 hFf hfG.le qbot qt
      · -- diagonal point `(G, G)`
        have hmin : G ≤ min g f := le_min hGg hGf
        have q5 := H5 (fun g' h' => by cases h'; exact haG.trans hGg) (fun f' h' => by cases h'; exact haG.trans hGf)
        have q6 := H6 g f rfl rfl (haG.trans hmin)
        have qtop := segD a (min g f) G haG hmin q5 q6
        exact segF G f0 G F hF0 hFG le_rfl qbot qtop

/-- **The factor lemma**: a predicate on `(G, F)` that is convex on each side of the diagonal, closed under the
available rays and true at the points of `tcFacPts` holds on the whole factor box. -/
lemma tc_factor (Q : ℚ → ℚ → Prop) (g0 f0 : ℚ) (g1 f1 : Option ℚ)
    (hconvL : ∀ G F G' F' l, F ≤ G → F' ≤ G' → 0 ≤ l → l ≤ 1 → Q G F → Q G' F' →
      Q ((1 - l) * G + l * G') ((1 - l) * F + l * F'))
    (hconvR : ∀ G F G' F' l, G ≤ F → G' ≤ F' → 0 ≤ l → l ≤ 1 → Q G F → Q G' F' →
      Q ((1 - l) * G + l * G') ((1 - l) * F + l * F'))
    (hrayG : g1 = none → ∀ G F μ, F ≤ G → 0 ≤ μ → Q G F → Q (G + μ) F)
    (hrayF : f1 = none → ∀ G F μ, G ≤ F → 0 ≤ μ → Q G F → Q G (F + μ))
    (hray11 : g1 = none → f1 = none → ∀ G F μ, 0 ≤ μ → Q G F → Q (G + μ) (F + μ))
    (H1 : Q g0 f0) (H2 : ∀ g, g1 = some g → Q g f0) (H3 : ∀ f, f1 = some f → Q g0 f)
    (H4 : ∀ g f, g1 = some g → f1 = some f → Q g f)
    (H5 : (∀ g, g1 = some g → max g0 f0 ≤ g) → (∀ f, f1 = some f → max g0 f0 ≤ f) →
      Q (max g0 f0) (max g0 f0))
    (H6 : ∀ g f, g1 = some g → f1 = some f → max g0 f0 ≤ min g f → Q (min g f) (min g f))
    (H7 : ∀ g, g1 = some g → f1 = none → max g0 f0 ≤ g → Q g g)
    (H8 : ∀ f, g1 = none → f1 = some f → max g0 f0 ≤ f → Q f f)
    {G F : ℚ} (hG0 : g0 ≤ G) (hF0 : f0 ≤ F) (hG1 : ∀ g, g1 = some g → G ≤ g)
    (hF1 : ∀ f, f1 = some f → F ≤ f) : Q G F := by
  rcases le_total F G with hFG | hGF
  · exact tc_factor_half Q g0 f0 g1 f1 hconvL hrayG hray11 H1 H2 H3 H4 H5 H6 H7 H8 hG0 hF0 hG1 hF1 hFG
  · -- the mirror image
    refine tc_factor_half (fun F G => Q G F) f0 g0 f1 g1
      (fun F G F' G' l h h' hl0 hl1 q q' => hconvR G F G' F' l h h' hl0 hl1 q q')
      (fun h F G μ hGF hμ q => hrayF h G F μ hGF hμ q)
      (fun h h' F G μ hμ q => hray11 h' h G F μ hμ q)
      H1 H3 H2 (fun f g hf hg => H4 g f hg hf)
      (fun h1 h2 => by
        rw [max_comm]
        exact H5 (fun g h => by rw [max_comm]; exact h2 g h) (fun f h => by rw [max_comm]; exact h1 f h))
      (fun f g hf hg h => by
        rw [max_comm, min_comm] at h; rw [min_comm]; exact H6 g f hg hf h)
      (fun f hf hg h => H8 f hg hf (by rwa [max_comm] at h))
      (fun g hf hg h => H7 g hg hf (by rwa [max_comm] at h))
      hF0 hG0 hF1 hG1 hGF

/-! ### The points of `tcFacPts` -/

lemma mem_tcAddNew {p q : ℕ × ℕ} {L : List (ℕ × ℕ)} : q ∈ tcAddNew p L ↔ q ∈ L ∨ q = p := by
  unfold tcAddNew
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (h' | rfl)
      · exact h'
      · exact h
  · simp

lemma tcFacPts_spec (g0 f0 : ℕ) (g1 f1 : Option ℕ) :
    (g0, f0) ∈ tcFacPts g0 g1 f0 f1 ∧
    (∀ g, g1 = some g → (g, f0) ∈ tcFacPts g0 g1 f0 f1) ∧
    (∀ f, f1 = some f → (g0, f) ∈ tcFacPts g0 g1 f0 f1) ∧
    (∀ g f, g1 = some g → f1 = some f → (g, f) ∈ tcFacPts g0 g1 f0 f1) ∧
    ((∀ g, g1 = some g → max g0 f0 ≤ g) → (∀ f, f1 = some f → max g0 f0 ≤ f) →
      (max g0 f0, max g0 f0) ∈ tcFacPts g0 g1 f0 f1) ∧
    (∀ g f, g1 = some g → f1 = some f → max g0 f0 ≤ min g f →
      (min g f, min g f) ∈ tcFacPts g0 g1 f0 f1) ∧
    (∀ g, g1 = some g → f1 = none → max g0 f0 ≤ g → (g, g) ∈ tcFacPts g0 g1 f0 f1) ∧
    (∀ f, g1 = none → f1 = some f → max g0 f0 ≤ f → (f, f) ∈ tcFacPts g0 g1 f0 f1) := by
  rcases g1 with _ | g <;> rcases f1 with _ | f <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp only [tcFacPts] <;> split_ifs <;>
    simp_all [mem_tcAddNew]

/-! ### Vertices -/

/-- The data of a point with `V = max(G, F)` in both factors. -/
def tcD (G1 F1 G2 F2 x f : ℚ) : RLTcD := ⟨G1, F1, G2, F2, max G1 F1, max G2 F2, x, f⟩

lemma tcVertsN_mem {b : TcBox} {p1 p2 : ℕ × ℕ} (h1 : p1 ∈ tcFacPts b.g1lo (some b.g1hi) b.f1lo (some b.f1hi))
    (h2 : p2 ∈ tcFacPts b.g2lo b.g2hi b.f2lo b.f2hi) {x f : ℕ} (hx : x = b.xlo ∨ x = b.xhi)
    (hf : f = b.flo ∨ f = b.fhi) :
    (⟨p1.1, p1.2, p2.1, p2.2, max p1.1 p1.2, max p2.1 p2.2, x, f⟩ : RLTcN) ∈ tcVertsN b := by
  simp only [tcVertsN, List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨p1, h1, p2, h2, x, hx, f, hf, rfl⟩

lemma tcVtx_toQ {Q : ℕ} (p1 p2 : ℕ × ℕ) (x f : ℕ) :
    (⟨p1.1, p1.2, p2.1, p2.2, max p1.1 p1.2, max p2.1 p2.2, x, f⟩ : RLTcN).toQ Q =
      tcD ((p1.1 : ℚ) / Q) ((p1.2 : ℚ) / Q) ((p2.1 : ℚ) / Q) ((p2.2 : ℚ) / Q) ((x : ℚ) / Q) ((f : ℚ) / Q) := by
  simp only [RLTcN.toQ, tcD, Nat.cast_max, max_div_div_right (Nat.cast_nonneg Q)]

/-! ### The assembly -/

section Assembly

variable {t B : ℚ} {Ts : ℕ} {desig : ℕ → ℕ}

/-- The bilinear step in `(x, f)`. -/
lemma tc_xf (G1 F1 G2 F2 : ℚ) {x0 x1 f0 f1 x f : ℚ} (hx0 : x0 ≤ x) (hx1 : x ≤ x1) (hf0 : f0 ≤ f)
    (hf1 : f ≤ f1) (h00 : TcGood t B Ts desig (tcD G1 F1 G2 F2 x0 f0))
    (h01 : TcGood t B Ts desig (tcD G1 F1 G2 F2 x0 f1)) (h10 : TcGood t B Ts desig (tcD G1 F1 G2 F2 x1 f0))
    (h11 : TcGood t B Ts desig (tcD G1 F1 G2 F2 x1 f1)) : TcGood t B Ts desig (tcD G1 F1 G2 F2 x f) := by
  have lin : ∀ x x' f f' l, (tcD G1 F1 G2 F2 x f).lc (1 - l) l (tcD G1 F1 G2 F2 x' f') =
      tcD G1 F1 G2 F2 ((1 - l) * x + l * x') ((1 - l) * f + l * f') := by
    intro x x' f f' l
    apply RLTcD.ext' <;> simp only [RLTcD.lc, tcD] <;> ring
  have sx : ∀ fc, TcGood t B Ts desig (tcD G1 F1 G2 F2 x0 fc) → TcGood t B Ts desig (tcD G1 F1 G2 F2 x1 fc) →
      TcGood t B Ts desig (tcD G1 F1 G2 F2 x fc) := by
    intro fc q0 q1
    refine tc_seg (Q := fun z => TcGood t B Ts desig (tcD G1 F1 G2 F2 z fc)) (fun l hl0 hl1 => ?_) hx0 hx1
    have := (q0.conv q1 (a := 1 - l) (b := l) (by linarith) hl0 (by ring)).congr (lin x0 x1 fc fc l)
    rwa [show (1 - l) * fc + l * fc = fc by ring] at this
  have q0 := sx f0 h00 h10
  have q1 := sx f1 h01 h11
  refine tc_seg (Q := fun z => TcGood t B Ts desig (tcD G1 F1 G2 F2 x z)) (fun l hl0 hl1 => ?_) hf0 hf1
  have := (q0.conv q1 (a := 1 - l) (b := l) (by linarith) hl0 (by ring)).congr (lin x x f0 f1 l)
  rwa [show (1 - l) * x + l * x = x by ring] at this

/-- Convexity of a factor on each side of the diagonal (second factor). -/
lemma tc_conv2 (G1 F1 x f : ℚ) {G F G' F' l : ℚ} (hs : (F ≤ G ∧ F' ≤ G') ∨ (G ≤ F ∧ G' ≤ F')) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) (q : TcGood t B Ts desig (tcD G1 F1 G F x f))
    (q' : TcGood t B Ts desig (tcD G1 F1 G' F' x f)) :
    TcGood t B Ts desig (tcD G1 F1 ((1 - l) * G + l * G') ((1 - l) * F + l * F') x f) := by
  refine (q.conv q' (a := 1 - l) (b := l) (by linarith) hl0 (by ring)).congr ?_
  apply RLTcD.ext' <;> simp only [RLTcD.lc, tcD] <;> try ring1
  rcases hs with ⟨h, h'⟩ | ⟨h, h'⟩
  · rw [max_eq_left h, max_eq_left h', max_eq_left (by nlinarith)]
  · rw [max_eq_right h, max_eq_right h', max_eq_right (by nlinarith)]

/-- Convexity of a factor on each side of the diagonal (first factor). -/
lemma tc_conv1 (G2 F2 x f : ℚ) {G F G' F' l : ℚ} (hs : (F ≤ G ∧ F' ≤ G') ∨ (G ≤ F ∧ G' ≤ F')) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) (q : TcGood t B Ts desig (tcD G F G2 F2 x f))
    (q' : TcGood t B Ts desig (tcD G' F' G2 F2 x f)) :
    TcGood t B Ts desig (tcD ((1 - l) * G + l * G') ((1 - l) * F + l * F') G2 F2 x f) := by
  refine (q.conv q' (a := 1 - l) (b := l) (by linarith) hl0 (by ring)).congr ?_
  apply RLTcD.ext' <;> simp only [RLTcD.lc, tcD] <;> try ring1
  rcases hs with ⟨h, h'⟩ | ⟨h, h'⟩
  · rw [max_eq_left h, max_eq_left h', max_eq_left (by nlinarith)]
  · rw [max_eq_right h, max_eq_right h', max_eq_right (by nlinarith)]

/-- The ray `(1, 0, 1)` of the second factor (from `F ≤ G`). -/
lemma tc_rayG (G1 F1 x f : ℚ) {G F μ : ℚ} (hμ : 0 ≤ μ) (h : F ≤ G) (q : TcGood t B Ts desig (tcD G1 F1 G F x f))
    (hr : ∃ R, rlRay (⟨0, 0, 1, 0, 0, 1⟩ : RLD) Ts R) : TcGood t B Ts desig (tcD G1 F1 (G + μ) F x f) := by
  refine (q.ray hr hμ).congr ?_
  apply RLTcD.ext' <;> simp only [RLTcD.addRay, tcD] <;> try ring1
  rw [max_eq_left h, max_eq_left (by linarith)]; ring

/-- The ray `(0, 1, 1)` of the second factor (from `G ≤ F`). -/
lemma tc_rayF (G1 F1 x f : ℚ) {G F μ : ℚ} (hμ : 0 ≤ μ) (h : G ≤ F) (q : TcGood t B Ts desig (tcD G1 F1 G F x f))
    (hr : ∃ R, rlRay (⟨0, 0, 0, 1, 0, 1⟩ : RLD) Ts R) : TcGood t B Ts desig (tcD G1 F1 G (F + μ) x f) := by
  refine (q.ray hr hμ).congr ?_
  apply RLTcD.ext' <;> simp only [RLTcD.addRay, tcD] <;> try ring1
  rw [max_eq_right h, max_eq_right (by linarith)]; ring

/-- The ray `(1, 1, 1)` of the second factor. -/
lemma tc_ray11 (G1 F1 x f : ℚ) {G F μ : ℚ} (hμ : 0 ≤ μ) (q : TcGood t B Ts desig (tcD G1 F1 G F x f))
    (hr : ∃ R, rlRay (⟨0, 0, 1, 1, 0, 1⟩ : RLD) Ts R) :
    TcGood t B Ts desig (tcD G1 F1 (G + μ) (F + μ) x f) := by
  refine (q.ray hr hμ).congr ?_
  apply RLTcD.ext' <;> simp only [RLTcD.addRay, tcD] <;> try ring1
  rw [max_add_add_right]; ring

lemma tcRaysN_memG {b : TcBox} (h : b.g2hi = none) : (⟨0, 0, 1, 0, 0, 1⟩ : RLTcR) ∈ tcRaysN b := by
  unfold tcRaysN; rw [h]; simp

lemma tcRaysN_memF {b : TcBox} (h : b.f2hi = none) : (⟨0, 0, 0, 1, 0, 1⟩ : RLTcR) ∈ tcRaysN b := by
  unfold tcRaysN; rw [h]; simp

lemma tcRaysN_mem11 {b : TcBox} (h : b.g2hi = none) (h' : b.f2hi = none) :
    (⟨0, 0, 1, 1, 0, 1⟩ : RLTcR) ∈ tcRaysN b := by
  unfold tcRaysN; rw [h, h']; simp

lemma tcRay_toRLD (a c : ℕ) : (⟨0, 0, a, c, 0, 1⟩ : RLTcR).toRLD = (⟨0, 0, a, c, 0, 1⟩ : RLD) := by
  simp [RLTcR.toRLD]

end Assembly

set_option maxHeartbeats 1000000 in
/-- **Every point of a checked cell is good**: if the cell passes `tcCellOK tn td`, every datum `d` in its box
(`G1, F1, G2, F2, x, f` within the box over `Q`, `V1 ≥ max(G1, F1)`, `V2 ≥ max(G2, F2)`) carries an RL-tc table
with the effect conditions. -/
theorem tcCell_good {tn td : ℕ} (htd : 0 < td) {C : TcCell} (hC : tcCellOK tn td C = true) (d : RLTcD)
    (hG1 : (C.box.g1lo : ℚ) / C.box.Q ≤ d.G1 ∧ d.G1 ≤ (C.box.g1hi : ℚ) / C.box.Q)
    (hF1 : (C.box.f1lo : ℚ) / C.box.Q ≤ d.F1 ∧ d.F1 ≤ (C.box.f1hi : ℚ) / C.box.Q)
    (hG2 : (C.box.g2lo : ℚ) / C.box.Q ≤ d.G2 ∧ ∀ h, C.box.g2hi = some h → d.G2 ≤ (h : ℚ) / C.box.Q)
    (hF2 : (C.box.f2lo : ℚ) / C.box.Q ≤ d.F2 ∧ ∀ h, C.box.f2hi = some h → d.F2 ≤ (h : ℚ) / C.box.Q)
    (hx : (C.box.xlo : ℚ) / C.box.Q ≤ d.x ∧ d.x ≤ (C.box.xhi : ℚ) / C.box.Q)
    (hf : (C.box.flo : ℚ) / C.box.Q ≤ d.f ∧ d.f ≤ (C.box.fhi : ℚ) / C.box.Q)
    (hV1 : max d.G1 d.F1 ≤ d.V1) (hV2 : max d.G2 d.F2 ≤ d.V2) :
    TcGood ((tn : ℚ) / td) ((C.Bn : ℚ) / C.Bd) C.Ts (tcDesig C.dg) d := by
  obtain ⟨hV, hR, -, hQ, -⟩ := tcCellOK_sound htd hC
  set b := C.box with hb
  set P := TcGood ((tn : ℚ) / td) ((C.Bn : ℚ) / C.Bd) C.Ts (tcDesig C.dg) with hP
  have hQq : (0 : ℚ) < b.Q := by exact_mod_cast hQ
  set q : ℕ → ℚ := fun n => (n : ℚ) / b.Q with hq
  have qle : ∀ m n : ℕ, q m ≤ q n ↔ m ≤ n := fun m n => by
    simp only [hq]; rw [div_le_div_iff_of_pos_right hQq]; exact Nat.cast_le
  have qmax : ∀ m n : ℕ, q (max m n) = max (q m) (q n) := fun m n => by
    simp only [hq, Nat.cast_max, max_div_div_right hQq.le]
  have qmin : ∀ m n : ℕ, q (min m n) = min (q m) (q n) := fun m n => by
    simp only [hq, Nat.cast_min, min_div_div_right hQq.le]
  -- step 0: the vertices
  have S1 := tcFacPts_spec b.g1lo b.f1lo (some b.g1hi) (some b.f1hi)
  have S2 := tcFacPts_spec b.g2lo b.f2lo b.g2hi b.f2hi
  have hvert : ∀ p1 ∈ tcFacPts b.g1lo (some b.g1hi) b.f1lo (some b.f1hi),
      ∀ p2 ∈ tcFacPts b.g2lo b.g2hi b.f2lo b.f2hi,
      ∀ x f : ℕ, (x = b.xlo ∨ x = b.xhi) → (f = b.flo ∨ f = b.fhi) →
      P (tcD (q p1.1) (q p1.2) (q p2.1) (q p2.2) (q x) (q f)) := by
    intro p1 h1 p2 h2 x f hx hf
    have := hV _ (List.mem_map_of_mem (f := fun v => v.toQ b.Q) (tcVertsN_mem h1 h2 hx hf))
    rw [tcVtx_toQ] at this
    exact this
  -- step A: (x, f)
  have hA : ∀ p1 ∈ tcFacPts b.g1lo (some b.g1hi) b.f1lo (some b.f1hi),
      ∀ p2 ∈ tcFacPts b.g2lo b.g2hi b.f2lo b.f2hi,
      P (tcD (q p1.1) (q p1.2) (q p2.1) (q p2.2) d.x d.f) := fun p1 h1 p2 h2 =>
    tc_xf _ _ _ _ hx.1 hx.2 hf.1 hf.2 (hvert p1 h1 p2 h2 b.xlo b.flo (Or.inl rfl) (Or.inl rfl))
      (hvert p1 h1 p2 h2 b.xlo b.fhi (Or.inl rfl) (Or.inr rfl))
      (hvert p1 h1 p2 h2 b.xhi b.flo (Or.inr rfl) (Or.inl rfl))
      (hvert p1 h1 p2 h2 b.xhi b.fhi (Or.inr rfl) (Or.inr rfl))
  -- rays of the second factor
  have ray : ∀ a c : ℕ, (⟨0, 0, a, c, 0, 1⟩ : RLTcR) ∈ tcRaysN b →
      ∃ R, rlRay (⟨0, 0, a, c, 0, 1⟩ : RLD) C.Ts R := fun a c h => by
    have := hR _ (List.mem_map_of_mem (f := RLTcR.toRLD) h)
    rwa [tcRay_toRLD] at this
  -- step B: the second factor
  have hB : ∀ p1 ∈ tcFacPts b.g1lo (some b.g1hi) b.f1lo (some b.f1hi),
      P (tcD (q p1.1) (q p1.2) d.G2 d.F2 d.x d.f) := by
    intro p1 h1
    refine tc_factor (fun G F => P (tcD (q p1.1) (q p1.2) G F d.x d.f)) (q b.g2lo) (q b.f2lo)
      (b.g2hi.map q) (b.f2hi.map q)
      (fun G F G' F' l h h' hl0 hl1 qq qq' => tc_conv2 _ _ _ _ (Or.inl ⟨h, h'⟩) hl0 hl1 qq qq')
      (fun G F G' F' l h h' hl0 hl1 qq qq' => tc_conv2 _ _ _ _ (Or.inr ⟨h, h'⟩) hl0 hl1 qq qq')
      (fun hg G F μ hFG hμ qq => ?_) (fun hf G F μ hGF hμ qq => ?_) (fun hg hf G F μ hμ qq => ?_)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hG2.1 hF2.1 ?_ ?_
    · have hg' : b.g2hi = none := Option.map_eq_none_iff.1 hg
      have := ray 1 0 (tcRaysN_memG hg')
      exact tc_rayG _ _ _ _ hμ hFG qq (by simpa using this)
    · have hf' : b.f2hi = none := Option.map_eq_none_iff.1 hf
      have := ray 0 1 (tcRaysN_memF hf')
      exact tc_rayF _ _ _ _ hμ hGF qq (by simpa using this)
    · have hg' : b.g2hi = none := Option.map_eq_none_iff.1 hg
      have hf' : b.f2hi = none := Option.map_eq_none_iff.1 hf
      have := ray 1 1 (tcRaysN_mem11 hg' hf')
      exact tc_ray11 _ _ _ _ hμ qq (by simpa using this)
    · exact hA p1 h1 (b.g2lo, b.f2lo) S2.1
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := Option.map_eq_some_iff.1 hg
      exact hA p1 h1 (g', b.f2lo) (S2.2.1 g' hg')
    · intro f hf
      obtain ⟨f', hf', rfl⟩ := Option.map_eq_some_iff.1 hf
      exact hA p1 h1 (b.g2lo, f') (S2.2.2.1 f' hf')
    · intro g f hg hf
      obtain ⟨g', hg', rfl⟩ := Option.map_eq_some_iff.1 hg
      obtain ⟨f', hf', rfl⟩ := Option.map_eq_some_iff.1 hf
      exact hA p1 h1 (g', f') (S2.2.2.2.1 g' f' hg' hf')
    · intro hg hf
      have := hA p1 h1 (max b.g2lo b.f2lo, max b.g2lo b.f2lo) (S2.2.2.2.2.1 (fun g h => by
        have := hg (q g) (by rw [h]; rfl); rwa [← qmax, qle] at this)
        (fun f h => by have := hf (q f) (by rw [h]; rfl); rwa [← qmax, qle] at this))
      simpa only [qmax] using this
    · intro g f hg hf hm
      obtain ⟨g', hg', rfl⟩ := Option.map_eq_some_iff.1 hg
      obtain ⟨f', hf', rfl⟩ := Option.map_eq_some_iff.1 hf
      have := hA p1 h1 (min g' f', min g' f') (S2.2.2.2.2.2.1 g' f' hg' hf' (by rwa [← qmax, ← qmin, qle] at hm))
      simpa only [qmin] using this
    · intro g hg hf hm
      obtain ⟨g', hg', rfl⟩ := Option.map_eq_some_iff.1 hg
      have hf' : b.f2hi = none := Option.map_eq_none_iff.1 hf
      exact hA p1 h1 (g', g') (S2.2.2.2.2.2.2.1 g' hg' hf' (by rwa [← qmax, qle] at hm))
    · intro f hg hf hm
      obtain ⟨f', hf', rfl⟩ := Option.map_eq_some_iff.1 hf
      have hg' : b.g2hi = none := Option.map_eq_none_iff.1 hg
      exact hA p1 h1 (f', f') (S2.2.2.2.2.2.2.2 f' hg' hf' (by rwa [← qmax, qle] at hm))
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := Option.map_eq_some_iff.1 hg
      exact hG2.2 g' hg'
    · intro f hf
      obtain ⟨f', hf', rfl⟩ := Option.map_eq_some_iff.1 hf
      exact hF2.2 f' hf'
  -- step C: the first factor (bounded, no rays)
  have hCc : P (tcD d.G1 d.F1 d.G2 d.F2 d.x d.f) := by
    refine tc_factor (fun G F => P (tcD G F d.G2 d.F2 d.x d.f)) (q b.g1lo) (q b.f1lo)
      (some (q b.g1hi)) (some (q b.f1hi))
      (fun G F G' F' l h h' hl0 hl1 qq qq' => tc_conv1 _ _ _ _ (Or.inl ⟨h, h'⟩) hl0 hl1 qq qq')
      (fun G F G' F' l h h' hl0 hl1 qq qq' => tc_conv1 _ _ _ _ (Or.inr ⟨h, h'⟩) hl0 hl1 qq qq')
      (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
      (hB (b.g1lo, b.f1lo) S1.1) ?_ ?_ ?_ ?_ ?_ (fun g _ h => by cases h) (fun f h => by cases h) hG1.1 hF1.1 ?_ ?_
    · intro g hg; cases hg; exact hB (b.g1hi, b.f1lo) (S1.2.1 b.g1hi rfl)
    · intro f hf; cases hf; exact hB (b.g1lo, b.f1hi) (S1.2.2.1 b.f1hi rfl)
    · intro g f hg hf; cases hg; cases hf; exact hB (b.g1hi, b.f1hi) (S1.2.2.2.1 b.g1hi b.f1hi rfl rfl)
    · intro hg hf
      have := hB (max b.g1lo b.f1lo, max b.g1lo b.f1lo) (S1.2.2.2.2.1 (fun g h => by
        cases h; have := hg (q b.g1hi) rfl; rwa [← qmax, qle] at this)
        (fun f h => by cases h; have := hf (q b.f1hi) rfl; rwa [← qmax, qle] at this))
      simpa only [qmax] using this
    · intro g f hg hf hm
      cases hg; cases hf
      have := hB (min b.g1hi b.f1hi, min b.g1hi b.f1hi) (S1.2.2.2.2.2.1 b.g1hi b.f1hi rfl rfl (by rwa [← qmax, ← qmin, qle] at hm))
      simpa only [qmin] using this
    · intro g hg; cases hg; exact hG1.2
    · intro f hf; cases hf; exact hF1.2
  -- step D: monotone in `V1, V2`
  have := hCc.monoV (V1 := d.V1) (V2 := d.V2) hV1 hV2
  exact this.congr (by cases d; rfl)

end Census
end IIT
