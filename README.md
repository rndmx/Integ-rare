# Integ-rare

Lean 4 formalization of a census of complexes in integrated information theory (IIT 4.0)
under the uniform measure on transition probability matrices (TPMs) of N binary units.
The current state is fixed; only the TPM is random, and every theorem holds for every state.

## Main theorems (`IIT/Census/`)

| Statement | Lean theorem |
|---|---|
| P(φ_s(whole substrate) > 0) → 0 | `IIT.Census.tendsto_volume_univPos` |
| exact ties between distinct candidates form a null set, for every N | `IIT.Census.volume_ties_null` |
| P(a proper subset is a complex) → 1 | `IIT.Census.tendsto_volume_B2` |
| a complex with φ_s > 0 and Φ = 0 (explicit 2-unit example) | `IIT.Census.complex_phiS_pos_Phi_zero` |

The development contains no `sorry` and no `axiom` declaration; `#print axioms` on the
main theorems gives `[propext, Classical.choice, Quot.sound]`. The Erlang tail bound, the
multivariate Lyapunov central limit theorem (portmanteau form) and Mityagin's theorem on
zero sets of real-analytic functions are proved in the development.

The IIT 4.0 definitions (`IIT/Phi.lean`, `IIT/System.lean`) are those of
[Integ](https://github.com/rndmx/Integ).

## Build

```
lake exe cache get
lake build
```
