"""IIT 2.0 verdict C2 (whole substrate is the main complex) on the rows of the IIT 4.0 census
data/census4_n2.csv (N=2, TPMs regenerated from random.Random(seed), in idx order, N*2^N draws each)
and data/census4_n3.csv + data/tpms4_n3.json (N=3). tpm[state][unit] = P(unit ON); states little-endian.
usage: python census2_uniform.py N out.csv"""
import csv, sys, json, random, os
from fractions import Fraction as F
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here); import iit2_mirror as M
N, out = int(sys.argv[1]), sys.argv[2]
inp = os.path.join(here, 'data', 'census4_n%d.csv' % N)
rows = list(csv.DictReader(open(inp)))
if N == 2:
    TP = {}
    for seed in sorted({int(r['seed']) for r in rows}):
        m = max(int(r['idx']) for r in rows if int(r['seed']) == seed); rng = random.Random(seed)
        for i in range(m + 1): TP[(seed, i)] = [[rng.random() for _ in range(N)] for _ in range(2**N)]
    key = lambda r: (int(r['seed']), int(r['idx']))
else:
    TP = {int(k): v['tpm'] for k, v in json.load(open(os.path.join(here, 'data', 'tpms4_n3.json'))).items()}
    key = lambda r: int(r['tpm_idx'])
idx = lambda s: sum(b << k for k, b in enumerate(s))
with open(out, 'w', newline='') as g:
    w = csv.writer(g); w.writerow(['tpm', 'state', 'case4', 'B1_4', 'C2'])
    for row in rows:
        T = TP[key(row)]; u = int(row['state'])
        sysm = M.Sys(N, lambda i, s, b, T=T: F(T[idx(s)][i]) if b == 1 else 1 - F(T[idx(s)][i]))
        x1 = tuple((u >> k) & 1 for k in range(N))
        ph = {S: M.phi(sysm, S, x1) for S in M.subsets(N)}
        w.writerow([str(key(row)), u, row['case'], int(row['case'] == 'B1'), int(M.is_main(sysm, x1, frozenset(range(N)), ph))])
