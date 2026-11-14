/-
IIT 2.0 after Balduzzi & Tononi (2008), "Integrated Information in Discrete Dynamical
Systems: Motivation and Theoretical Framework", PLoS Comput Biol 4(6) e1000091.
Cited as [BT08]; page numbers are the printed page numbers.

Representation (see NOTES.md, "Representation"): every repertoire on the states of a
subset `A` is stored as a *density with respect to the a priori (maximum entropy)
repertoire*, as a function on full states `State N` that depends only on the
coordinates in `A`.  Averages `avg` are taken over the uniform distribution on
`State N`.  For functions depending only on `A`, `avg` agrees with the average over the
states of `A`, so `kl p q = ∑_{a₀} p(a₀) log₂ (p(a₀)/q(a₀))` with `p(a₀)`, `q(a₀)` the
probabilities (density × 2^{-|A|}).
-/
import IIT2.Interface

namespace IIT2

open Finset Real

variable {N : ℕ}

/-! ## Perturbations and averaging -/

/-- The state equal to `x` on `A` and to `e` off `A`: the perturbation `x` imposed on the
elements of `A`, the remaining inputs being `e`. -/
def mix (A : Finset (Fin N)) (x e : State N) : State N := fun j => if j ∈ A then x j else e j

/-- Average over the maximum entropy (uniform) distribution on `State N`.
`[BT08, p.3]`: "The a priori repertoire is the probability distribution on the set of
possible outputs of the elements considered independently, with each output equally likely";
`[BT08, p.4]`: external inputs are averaged "with the maximum entropy distribution". -/
noncomputable def avg (f : State N → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card (State N) : ℝ)

/-- `f` depends only on the coordinates in `A`. -/
def DepOn (A : Finset (Fin N)) (f : State N → ℝ) : Prop :=
  ∀ x y : State N, (∀ i ∈ A, x i = y i) → f x = f y

/-! ## Repertoires -/

/-- The probability that the elements of `A` output `x₁` (restricted to `A`) at `t = 1`
when the perturbation `x₀` (restricted to `A`) is imposed on `A` at `t = 0`.
Inputs from outside `A` are averaged with the maximum entropy distribution SEPARATELY for
each element of `A` (connections, not elements, are perturbed), and the mechanism of `A` is the
product of the averaged element mechanisms `[BT08 S1, §3, p.2]`: "Each connection afferent to S
is averaged over using the maximum entropy distribution. After averaging out extrinsic noise,
the mechanism of an element n_k in S is given by p_mech(n^k_1|do(s0)) = Σ_{e0}
p_mech(n^k_1|do(s0,e0)) p_max(e0) [...] The mechanism of the system, p_sys(s1|do(s0)) is then
the combined mechanism of the elements within S."  See also `[BT08, p.4]`. -/
noncomputable def cond (sys : UnitTPM N) (A : Finset (Fin N)) (x₁ x₀ : State N) : ℝ :=
  ∏ i ∈ A, avg (fun e => sys.prob i (mix A x₀ e) (x₁ i))

/-- The a posteriori repertoire `p(A₀ → a₁)` `[BT08, p.3]`, obtained by Bayes' rule from the
a priori repertoire `p^max(A₀)`, as a density with respect to `p^max(A₀)`:
`p(a₀ | a₁) / p^max(a₀) = p(a₁ | a₀) / ∑_{a₀'} p(a₁ | a₀') p^max(a₀')`.
If `a₁` has probability zero under every perturbation the value is `0` (Lean's `x/0 = 0`);
see NOTES.md, ambiguity A5. -/
noncomputable def post (sys : UnitTPM N) (A : Finset (Fin N)) (x₁ x₀ : State N) : ℝ :=
  cond sys A x₁ x₀ / avg (cond sys A x₁)

/-- The a priori repertoire `p^max(A₀)` `[BT08, p.3]` as a density with respect to itself. -/
def pmax : State N → ℝ := fun _ => 1

/-- Relative entropy `H[p ‖ q]` in bits `[BT08, p.3, Eq 1A]`, for densities `p`, `q` with
respect to the maximum entropy distribution. -/
noncomputable def kl (p q : State N → ℝ) : ℝ := avg (fun x => p x * logb 2 (p x / q x))

/-- Effective information `ei(A₀ → a₁) := H[p(A₀ → a₁) ‖ p^max(A₀)]` `[BT08, Eq 1A, p.3]`. -/
noncomputable def ei (sys : UnitTPM N) (S : Finset (Fin N)) (x₁ : State N) : ℝ :=
  kl (post sys S x₁) pmax

/-- The combined a posteriori repertoire of the parts, `∏_{M^k ∈ P} p(M^k₀ → m^k₁)`
`[BT08, Eq 2A, p.4; display p.5]`. -/
noncomputable def partsPost (sys : UnitTPM N) {S : Finset (Fin N)} (P : Finpartition S)
    (x₁ : State N) : State N → ℝ :=
  fun x => ∏ M ∈ P.parts, post sys M x₁ x

/-- `H[p(S₀ → s₁) ‖ ∏_{M^k ∈ P} p(M^k₀ → m^k₁)]`, the formula of `[BT08, p.5]`
(display after "To do so"). -/
noncomputable def eiRel (sys : UnitTPM N) {S : Finset (Fin N)} (P : Finpartition S)
    (x₁ : State N) : ℝ :=
  kl (post sys S x₁) (partsPost sys P x₁)

/-- Effective information across a partition, `ei(S₀ → s₁ / P)` `[BT08, p.5–6]`:
the formula of p.5, except for the total partition `P = {S}`, where it is *defined* to be
`ei(S₀ → s₁)` of Eq 1A `[BT08, p.6]`. -/
noncomputable def eiAcross (sys : UnitTPM N) {S : Finset (Fin N)} (P : Finpartition S)
    (x₁ : State N) : ℝ :=
  if P.parts.card = 1 then ei sys S x₁ else eiRel sys P x₁

/-- `min_k H^max(M^k₀)` in bits, i.e. the size of the smallest part. -/
def minPartSize {S : Finset (Fin N)} (P : Finpartition S) : ℕ :=
  if h : P.parts.Nonempty then P.parts.inf' h Finset.card else 0

/-- The normalization `N_P = (m − 1) · min_k H^max(M^k₀)`, with `N_P = H^max(S₀) = |S|` for
the total partition `[BT08, p.7, top]`. -/
noncomputable def normP {S : Finset (Fin N)} (P : Finpartition S) : ℝ :=
  if P.parts.card = 1 then (S.card : ℝ) else ((P.parts.card : ℝ) - 1) * (minPartSize P : ℝ)

/-- The key minimized by the minimum information partition `[BT08, p.7]`: first the
normalized effective information `ei/N_P`, then, among ties, the un-normalized `ei`
("we select those partitions that generate the lowest un-normalized quantity of effective
information"). Lexicographic order. -/
noncomputable def mipKey (sys : UnitTPM N) {S : Finset (Fin N)} (x₁ : State N)
    (P : Finpartition S) : Lex (ℝ × ℝ) :=
  toLex (eiAcross sys P x₁ / normP P, eiAcross sys P x₁)

/-- `P` is a minimum information partition `[BT08, p.7]`. -/
def IsMIP (sys : UnitTPM N) {S : Finset (Fin N)} (x₁ : State N) (P : Finpartition S) : Prop :=
  ∀ Q : Finpartition S, mipKey sys x₁ P ≤ mipKey sys x₁ Q

/-- Integrated information `φ(s₁) = ei(S₀ → s₁ / P^MIP)` `[BT08, Eq 2B, p.7]`, the minimum
over all partitions of `S` (`Finpartition S`, which includes the total partition) of
`mipKey`, second component. -/
noncomputable def phi (sys : UnitTPM N) (S : Finset (Fin N)) (x₁ : State N) : ℝ :=
  (ofLex ((Finset.univ : Finset (Finpartition S)).inf' Finset.univ_nonempty
    (mipKey sys x₁))).2

/-- `S` is a complex in state `x₁` `[BT08, Eq 3A, p.7]`:
`φ(s₁) > 0` and `φ(t₁) ≤ φ(s₁)` for all `T ⊇ S`. -/
def IsComplex (sys : UnitTPM N) (x₁ : State N) (S : Finset (Fin N)) : Prop :=
  0 < phi sys S x₁ ∧ ∀ T : Finset (Fin N), S ⊆ T → phi sys T x₁ ≤ phi sys S x₁

/-- `S` is a main complex in state `x₁` `[BT08, Eq 3B, p.7]`: a complex with
`φ(r₁) < φ(s₁)` for all `R ⊂ S`. -/
def IsMainComplex (sys : UnitTPM N) (x₁ : State N) (S : Finset (Fin N)) : Prop :=
  IsComplex sys x₁ S ∧ ∀ R : Finset (Fin N), R ⊂ S → phi sys R x₁ < phi sys S x₁

/-- The whole system `X` is the main complex in state `x₁` (`[BT08, Eq 3B]` with `S = X`). -/
def WholeIsMainComplex (sys : UnitTPM N) (x₁ : State N) : Prop :=
  IsMainComplex sys x₁ Finset.univ

/-- Remark (not the paper's definition of φ): the restriction to bipartitions used for the
numerical examples `[BT08, p.9, "Unless otherwise specified, for computational reasons we
measure integrated information by considering all bipartitions rather than all partitions"]`.
Partitions with at most two parts. -/
noncomputable def phiBipartitionsRemark (sys : UnitTPM N) (S : Finset (Fin N))
    (x₁ : State N) : ℝ :=
  if h : ((Finset.univ : Finset (Finpartition S)).filter (fun P => P.parts.card ≤ 2)).Nonempty
  then (ofLex ((Finset.univ.filter (fun P : Finpartition S => P.parts.card ≤ 2)).inf' h
    (mipKey sys x₁))).2
  else 0

end IIT2
