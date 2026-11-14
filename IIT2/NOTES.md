# IIT 2.0 in Lean — working notes

Source (only source used): C:\Users\Arnaud\sources\consciousness-2026-11\balduzzi2008.pdf
Balduzzi & Tononi (2008), PLoS Comput Biol 4(6) e1000091, doi 10.1371/journal.pcbi.1000091, 18 pp.
sha256 f3cb9a6bbf4ba56cd304ef2b1769d6c8aa54ce75d74de954c7605d7e7cfe71a7 (verified 2026-11-13).
Cited as [BT08]. Page numbers = printed page numbers of the PDF.

Text S1 (supplement): C:\Users\Arnaud\sources\consciousness-2026-11\balduzzi2008_S1.pdf, 11 pp,
sha256 49e9c125ceced1d62789a5bf945be7a8f47bd016a054127f5f39846705b03a0c (verified 2026-11-13). Cited [BT08 S1].
Read in full; used from the cond fix onward (see "FIX 1").

## Paper definitions (as read)
- a priori repertoire p^max(X0): uniform on outputs (p.3, "with each output equally likely").
- a posteriori repertoire p(X0 -> x1): Bayes' rule over perturbations (p.3; details deferred to Text S1 s.3).
- ei(X0 -> x1) := H[p(X0->x1) || p^max(X0)]  (Eq 1A, p.3); = H(p^max) - H(p)  (Eq 1B, p.4).
- external inputs averaged with the maximum entropy distribution (p.4, "Effective information in systems that are not isolated").
- parts' repertoires: each part as a system in its own right, averaging over inputs from other parts and extrinsic (p.4).
- ei(X0 -> x1 / P) := H[p(X0->x1) || prod_k p(M^k_0 -> m^k_1)]  (p.5, display after "To do so").
- total partition P={X}: ei across it := ei(X0 -> x1) of Eq 1A (p.6).
- N_P = (m-1) min_k H^max(M^k_0); total partition N_P = H^max(X0)  (p.7, top).
- P^MIP = argmin_P ei(X0->x1/P)/N_P, ties -> lowest un-normalized ei  (p.7).
- phi(x1) = ei(X0 -> x1 / P^MIP)  (Eq 2B, p.7).
- complex: phi(s1) > 0 and phi(t1) <= phi(s1) for all T ⊇ S  (Eq 3A, p.7).
- main complex: complex and phi(r1) < phi(s1) for all R ⊂ S  (Eq 3B, p.7).

## Progress
(see sections below; updated as work proceeds)

## Files
- IIT2/Basic.lean — all definitions (builds).
- IIT2/Theorems.lean — basic theorems (builds, no sorry).

## Definitions done (Lean name — paper)
- `mix`, `avg`, `DepOn` — auxiliary (perturbation imposed on A; maxent average, p.3–4).
- `cond` — p(a1 | a0) = prod_{i in A} avg_e p(x1_i | mix A x0 e): per-element maxent averaging of extrinsic inputs ([BT08 S1 s.3]; p.4).
- `post` — a posteriori repertoire p(A0 -> a1), Bayes' rule (p.3), as density w.r.t. p^max.
- `pmax` — a priori repertoire (p.3).
- `kl` — relative entropy H[p||q] in bits (Eq 1A, p.3).
- `ei` — Eq 1A, p.3.
- `partsPost`, `eiRel` — product of parts' repertoires and H[p||prod] (Eq 2A p.4; display p.5).
- `eiAcross` — ei(X0->x1/P), total partition defined as Eq 1A (p.6).
- `minPartSize`, `normP` — N_P (p.7).
- `mipKey`, `IsMIP` — MIP with tie-break (p.7).
- `phi` — Eq 2B, p.7.
- `IsComplex` (Eq 3A), `IsMainComplex` (Eq 3B), `WholeIsMainComplex` (p.7).
- `phiBipartitionsRemark` — remark only: bipartition restriction used for numerics (p.9).

## Theorems proved (Theorems.lean)
- `kl_nonneg` (Gibbs, p.3 "always non-negative"), `kl_self`.
- `avg_mul_of_disjoint`, `avg_prod_of_pairwiseDisjoint` (maxent independence of disjoint coordinates).
- `ei_nonneg`, `eiRel_nonneg`, `eiAcross_nonneg`, `phi_nonneg`.
- `exists_isMIP` (phi is attained by a MIP), `phi_eq_zero_of_eiAcross_eq_zero`.
- `phi_empty`.
- `phi_eq_zero_of_independent` (p.4, Fig 3, S1 s.4): if no element of A reads B and no element of B reads A, phi(A∪B)=0; shared external inputs allowed (e.g. a'=a xor e, b'=b xor e).
- `not_isComplex_of_phi_eq_zero`, `isComplex_univ_iff`, `exists_isMainComplex` (p.7).
- Bounds.lean: `post_le` (density <= 2^|S|), `ei_le_card` (p.4: "a system of n binary elements generates at most n bits"),
  `normP_le_card`, `normP_pos`, `phi_le_card` (p.7: "phi(x1) <= n bits").
- Zero sorry, no extra axioms (#print axioms: propext, Classical.choice, Quot.sound).
- Build: `LEAN_NUM_THREADS=2 lake build IIT2` passes.

## Not formalized (paper claims left aside)
- p.6: "For a system containing no elements with self-connections ei across the total partition and across the
  partition into individual elements coincide" (needs a notion of connection graph; not attempted).
- p.4: converse direction "phi is zero ONLY IF the system can be decomposed into independent parts" (not attempted;
  "independent" is not defined precisely in the paper).
- Eq 1B (ei = H(p^max) - H(p)) not proved as a separate identity; ei is defined by Eq 1A.
- Example values (figures) and Text S1 results (bipartition lower bound, homogeneous <= 1 bit, grids) not formalized.

## Representation
- Repertoires on states of A are densities w.r.t. p^max, stored on full states `State N` depending only on A
  (`DepOn`); `avg` = uniform average on `State N`. For A-measurable functions this equals the average over A-states,
  so `kl p q` = sum_{a0} p(a0) log2(p(a0)/q(a0)). Mathematically identical to the paper's formulas.

## Input mismatches (Interface.lean frozen, nothing changed)
- M1 Non-binary elements: paper allows "a finite repertoire of outputs" (p.3) and Fig 7A uses units with 2^n outputs
  (p.8). Interface is binary only. Not covered.
- M2 Elements with memory: Fig 10 (p.11, rule uses "the two time steps prior") and Fig 11C (p.11, memory of up to 8
  steps) are outside the memoryless framework the paper itself formalizes (p.3 "first order Markov"). Not covered.
- M3 Factorizing TPM: the paper's mechanisms are per-element rules (p.3), conditionally independent given inputs;
  this matches `UnitTPM`. No mismatch for the memoryless binary case.
- M4 World W ⊋ X: p.4 allows X embedded in a larger W. Here the whole of `Fin N` is the world; a subset S ⊆ Fin N
  plays X, and everything outside S is averaged with maxent. A world larger than the modelled N units is not
  representable except by including it in N.
- M5 Perturbation distribution: always maxent (p.3), no extra parameter needed. No time-step parameter needed
  (one step, p.3).

## Ambiguity choices
- A1 Log base: bits, `logb 2` ("3 bits", p.3; "n bits", p.4).
- A2 Partitions: `Finpartition S` = nonempty, pairwise disjoint parts covering S ("the parts are mutually disjoint
  and collectively pave the system", p.5). Includes the total partition. The MIP search is over ALL partitions
  (p.5 "searching over all partitions"); bipartitions-only is only the remark `phiBipartitionsRemark` (p.9).
- A3 Total partition: detected as `P.parts.card = 1`; its ei is Eq 1A and N_P = |S| (p.6, p.7).
- A4 Tie-breaking: lexicographic (ei/N_P, ei), "we select those partitions that generate the lowest
  un-normalized quantity of effective information" (p.7). phi is the ei value, so it is independent of which
  of several tied MIPs is chosen.
- A5 Probability-zero states: if s1 cannot occur under any perturbation, Bayes' rule is undefined (Fig 9 legend,
  p.10: "the value of phi for 7 elements firing is undefined, since no state ... is possible"). Lean: the
  repertoire is 0 (x/0 = 0), so ei = 0 and phi = 0; such a state never makes a complex. Positivity of
  the parts' repertoires wherever the whole's is positive is proved (`post_pos_of_subset`), so no log(p/0) issue.
- A6 Empty subset: phi(∅) = 0 (`phi_empty`), follows from the definitions; never a complex.
- A7 Eq 3A ranges over supersets T of S inside X (`S ⊆ T`, T = S harmless); Eq 3B over proper subsets R ⊂ S,
  including ∅ and singletons. The printed relation symbols are garbled in pdftotext; reading taken from the
  text "S is not contained in some larger set with strictly higher phi" and "A complex whose subsets have
  strictly lower phi is called a main complex" (p.7).
- A8 Subset in a state: phi of S in state x1 uses only x1 restricted to S (s1), with the rest of X as environment
  (p.4, parts and subsets treated as systems in their own right).
- A9 "the complex with the maximum value of phi necessarily forms a main complex" (p.7): with ties this is false
  as literally stated (a proper subset could share the maximum); formalized as existence
  (`exists_isMainComplex`: a maximizer of minimal size is a main complex).

## FIX 1 (2026-11-13): per-element averaging in `cond`
- Old (wrong): `cond` averaged the extrinsic inputs jointly, avg_e prod_{i in A} p(x1_i | mix A x0 e).
- New: `cond sys A x1 x0 = prod_{i in A} avg_e p(x1_i | mix A x0 e)`.
- Source [BT08 S1, s.3, p.2]: "Each connection afferent to S is averaged over using the maximum entropy
  distribution. After averaging out extrinsic noise, the mechanism of an element n_k in S is given by
  p_mech(n^k_1|do(s0)) = sum_{e0} p_mech(n^k_1|do(s0,e0)) p_max(e0) [...] The mechanism of the system,
  p_sys(s1|do(s0)) is then the combined mechanism of the elements within S. Imposing maximum ignorance on
  external inputs requires perturbing connections rather than elements".
- Granularity: per element, not per individual wire. These coincide here, since an element reads each
  external element through one connection.
- The old reading (joint averaging, from p.4 alone) is removed.
- Proofs changed: `cond_nonneg`, `cond_depOn`, `cond_pos_of_subset` (now factor by factor), and
  `phi_eq_zero_of_independent` (STRONGER: the hypothesis of disjoint external input sets E_A, E_B is dropped).
  Other proofs unchanged.

## Numerical check of printed values (scripts/check_figs.py, run `python -I scripts/check_figs.py`)
Python re-implementation of the same definitions (cond per element vs joint; phi_all = all partitions,
phi_bip = bipartitions + total partition). Rules read from the text; Fig 6/11 wiring is my reading
of the text (p.7: three copies of the AND triple; p.11: binary counter, n_k toggles iff n_1..n_{k-1} fire).
- Fig 1: ei = 3 bits (printed 3).
- Fig 6, A = triple, x1 = (001, copies 110): per-element phi = 3 (printed 3); joint = 1. Whole X: phi = 0 (printed 0).
- Fig 11 counter: per-element phi = 4 (x1 = 0000) or 0.193 (other states tried); printed "phi = 4 (across the
  total partition) or phi = .19 bits, depending on the current state"; joint gives 1 at 0000.
- Fig 14B majority (4 elements, fire iff >= 3 spikes, x1 = 1111): per-element part weights .09/.09/.82
  (printed .09/.09/.8), phi_bip = .793 (printed .79); joint phi_bip = .420.
- phi (the definition, all partitions, p.5) gives .566 for Fig 14B; the printed .79 uses bipartitions plus the
  total partition (p.9). `phi` keeps the definition; `phiBipartitionsRemark` is the p.9 variant.
