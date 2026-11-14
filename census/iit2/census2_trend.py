"""IIT 2.0 verdict C2 on the rows of the IIT 4.0 trend census (paper Table census), same TPM (regenerated from seed
exactly as trend_census.random_tpm) and same state. usage: census2_trend.py <trend_nN.csv> N start count >> out"""
import csv, sys, random
from fractions import Fraction as F
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__))); import iit2_mirror as M
inp, N, a, c = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
idx = lambda s: sum(b << k for k, b in enumerate(s)); X = frozenset(range(N))
rows = list(csv.DictReader(open(inp)))[a:a + c]
for row in rows:
    rng = random.Random(int(row['seed'])); T = [[rng.random() for _ in range(N)] for _ in range(2**N)]
    sysm = M.Sys(N, lambda i, s, b, T=T: F(T[idx(s)][i]) if b else 1 - F(T[idx(s)][i]))
    u = int(row['state']); x1 = tuple((u >> k) & 1 for k in range(N))
    ph = {S: M.phi(sysm, S, x1) for S in M.subsets(N)}
    print(row['seed'], u, row['case'], int(row['case'] == 'B1'), int(M.is_main(sysm, x1, X, ph)), flush=True)
