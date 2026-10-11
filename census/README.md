# Census for small N (Section 3, Table 1)

- `trend_census.py`: classifies random TPMs (N = 3..6, entries uniform on [0,1), one random current state per
  TPM) into the cases A0, A, B1, B2, C of the paper. It uses a fast floating-point transcription of the system
  level of `IIT/System.lean`; every borderline decision (margin below 1e-9) is re-decided in exact rational
  arithmetic by `exact.py`, with logarithms kept symbolic.
- `exact.py`: the system level of `IIT/System.lean` in exact rational arithmetic.
- `data/summary_nN.json`, `data/trend_nN.csv`: the runs reported in Table 1 (seeds fixed in the script).

Reproduce, e.g. for N = 3 (4000 TPMs, 4 processes):

```
python trend_census.py run 3 4000 all 4
```

The counts in the new `summary_n3.json` equal those in `data/summary_n3.json`. The Table 1 runs used 4000, 4000,
1000 and 500 TPMs for N = 3, 4, 5, 6.
