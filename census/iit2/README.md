# IIT 2.0 census (Appendix A, Table A.1)

- `iit2_mirror.py`: IIT 2.0 (Balduzzi and Tononi 2008) as a transcription of `IIT2/Basic.lean`: repertoires in
  exact rational arithmetic, logarithms in double precision; strict inequalities between values of φ are required
  to hold with margin 1e-12.
- `census2_uniform.py N out.csv`: the IIT 2.0 verdict C2 (the whole substrate is the main complex) on every row of
  the IIT 4.0 census `data/census4_nN.csv`, N = 2, 3 (every state of each TPM). At N = 2 the TPMs are regenerated
  from the seeds; at N = 3 they are read from `data/tpms4_n3.json`. Output: `data/g2_nN.csv`.
- `census2_trend.py ../data/trend_nN.csv N start count`: the same verdict on the TPMs and states of the Table 1
  runs (`../data/trend_nN.csv`), N = 4, 5. Output columns: seed, state, case (IIT 4.0), B1, C2.
  Output: `data/c2_trend_nN.txt`.
- `table_a1.py`: prints Table A.1 from `data/`.
- `check_figs.py`: checks the IIT 2.0 definitions against the values printed in Balduzzi and Tononi (2008),
  Figs. 6, 11 and 14B.
