# Complexes of random substrates in integrated information theory: limit theorems under the uniform measure

Lean 4 + Mathlib formalization of all the theorems of the paper of the same title (Arnaud Mayeux).

Draw the transition probability matrix (TPM) of N binary units uniformly: every entry z_{r,j} is independent and
uniform on [0,1]. The current state is fixed; only the TPM is random, and every theorem holds for every state.
The definitions of φ_s, complexes, distinctions, relations and Φ are those of the author's formalization of
IIT 4.0 (Integ v1.1), contained here in `IIT/Phi.lean`, `IIT/System.lean` and `IIT/Cond.lean`.

| Paper | Statement | Lean theorem | File |
|---|---|---|---|
| Theorem 4 | P(φ_s(whole) > 0) → 0 | `IIT.Census.tendsto_volume_univPos` | `IIT/Census/UnivZero.lean` |
| Theorem 8 | positive ties between distinct candidates have measure zero, for every N | `IIT.Census.volume_ties_null` | `IIT/Census/Ties.lean` |
| Theorem 11 | with probability → 1 a proper subset is a complex | `IIT.Census.tendsto_volume_B2` | `IIT/Census/B2Limit.lean` |
| Theorem 12 (i) | the maximizer of φ_s is a triple | `IIT.Census.tendsto_volume_argmax_ne3` | `IIT/Census/LawMain.lean` |
| Theorem 12 (ii) | Φ of the maximizer is at most e^{2^{K_N+1}} (2/3)^{N/2} | `IIT.Census.tendsto_volume_PhiArgmax_rate` | `IIT/Census/BigPhiMain.lean` |
| Theorem 12 | Φ of the main complex → 0 in probability | `IIT.Census.tendsto_volume_PhiArgmax` | `IIT/Census/BigPhiMain.lean` |
| Proposition 3 | a complex with φ_s > 0 and Φ = 0 | `IIT.Census.complex_phiS_pos_Phi_zero` | `IIT/Census/PhiZeroExample.lean` |
| Theorem 14 | given that the whole substrate is the complex, Φ ≥ 2^(2^⌊N/8⌋) with probability → 1 | `IIT.Census.b1PhiGoal_proved` | `IIT/Census/B1PhiGoalFinal.lean` |

## Checking

Every theorem depends only on Lean's three standard axioms. The repository contains no `sorry`, no `admit`,
no `native_decide` and no `axiom` declaration.

```
lake exe cache get        # prebuilt Mathlib (do not build Mathlib from source)
lake build                # builds the seven main-theorem files and all their imports
lake env lean CheckA.lean # axioms of Theorems 4, 8, 11 and Proposition 3
lake env lean CheckB.lean # axioms of Theorems 12 and 14
```

Each theorem reports `depends on axioms: [propext, Classical.choice, Quot.sound]`. The checks are split in two
files because the files of Theorem 11 (`PairCLT`) and of Theorems 12 and 14 (`BigPhiStats`) both define a
declaration `IIT.Census.Vp`, so they cannot be imported into one file; each main theorem compiles on its own.

Toolchain: `leanprover/lean4:v4.34.0-rc2` (see `lean-toolchain`). Mathlib is pinned in `lake-manifest.json`
(rev `2fbace17aa59`). The repository has 439 Lean files. Building them takes several hours on two cores; many
large-deviation certificates are checked by the kernel with `decide`, and those files are slow.

## Census for small N

The folder `census/` contains the script that computes Table 1 of the paper (N = 3,...,6), its exact-arithmetic
engine and the data of the reported runs; see `census/README.md`.

## Notes

- `IIT/Census/B1CountSkel.lean`, `B1ForcedB2.lean` and `B1LowerB.lean` contain definitions of earlier versions
  of the proof of Theorem 14; their superseded leaves were removed (one of them, `count_exp_famX`, is false as
  stated), and the proof uses the corrected route of `B1GoodX3.lean`.
- Every file in the import closure of the main theorems is present, even where only part of a file is used.

## License

MIT. Copyright (c) 2026 Arnaud Mayeux.
