"""Prints Table A.1 from data/: N=2,3 (g2_n*.csv, every state of each TPM), N=4,5 (c2_trend_n*.txt, the Table 1 runs)."""
import csv, os
here = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data')
def row(N, a, b):
    n = len(a); pa, pb = sum(a) / n, sum(b) / n; pab = sum(x * y for x, y in zip(a, b)) / n
    print('%d  P(C2)=%.1f  P(C4)=%.1f  P(C2&C4)=%.1f  P(C2|C4)=%.1f  P(C4|C2)=%.1f' % (N, 100*pa, 100*pb, 100*pab, 100*pab/pb, 100*pab/pa))
for N in (2, 3):
    R = list(csv.DictReader(open(os.path.join(here, 'g2_n%d.csv' % N))))
    row(N, [int(r['C2']) for r in R], [int(r['B1_4']) for r in R])
for N in (4, 5):
    L = [l.split() for l in open(os.path.join(here, 'c2_trend_n%d.txt' % N)) if l.strip()]
    row(N, [int(x[4]) for x in L], [int(x[3]) for x in L])
