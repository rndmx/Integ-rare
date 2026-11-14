"""Line-by-line mirror of iit2-lean/IIT2/Basic.lean in exact rational arithmetic.
Logs only at the end (floats). MODE='joint' = Lean `cond` (joint average over outside inputs).
MODE='marg' = variant: each element averages its outside inputs independently (product of
per-element marginals), used to test the paper's Fig 14B printed weights.
"""
from fractions import Fraction as F
from itertools import product
from functools import lru_cache
import math, sys

MODE = 'marg'  # = fixed Lean cond (per-element, BT08 S1 §3)

class Sys:
    def __init__(self, N, prob):  # prob(i, s, b) -> Fraction ; s tuple of 0/1
        self.N = N; self.prob = prob
        self.states = list(product((0, 1), repeat=N))
        self._cache = {}

def mix(A, x, e):  # Lean `mix`
    return tuple(x[j] if j in A else e[j] for j in range(len(x)))

def avg(sysm, f):  # Lean `avg`: uniform over State N
    return sum((f(x) for x in sysm.states), F(0)) / len(sysm.states)

def cond(sysm, A, x1, x0):
    key = (MODE, A, tuple(x1[i] for i in sorted(A)), tuple(x0[i] for i in sorted(A)))
    if key in sysm._cache: return sysm._cache[key]
    if MODE == 'joint':  # Lean: avg (fun e => prod_{i in A} prob i (mix A x0 e) (x1 i))
        def g(e):
            r = F(1)
            for i in A: r *= sysm.prob(i, mix(A, x0, e), x1[i])
            return r
        v = avg(sysm, g)
    else:
        v = F(1)
        for i in A: v *= avg(sysm, lambda e: sysm.prob(i, mix(A, x0, e), x1[i]))
    sysm._cache[key] = v
    return v

def post(sysm, A, x1):  # returns function x0 -> density; x/0 = 0
    d = avg(sysm, lambda x0: cond(sysm, A, x1, x0))
    return lambda x0: (cond(sysm, A, x1, x0) / d) if d != 0 else F(0)

def logb2(x):  # Lean logb 2 with log 0 = 0
    return 0.0 if x == 0 else math.log2(x)

def kl(sysm, p, q):
    tot = 0.0
    for x in sysm.states:
        px = p(x)
        if px == 0: continue
        qx = q(x)
        tot += float(px) * (logb2(F(px) / qx) if qx != 0 else 0.0)
    return tot / len(sysm.states)

def ei(sysm, S, x1):
    return kl(sysm, post(sysm, S, x1), lambda x: F(1))

def partsPost(sysm, P, x1):
    ps = [post(sysm, M, x1) for M in P]
    def f(x):
        r = F(1)
        for p in ps: r *= p(x)
        return r
    return f

def eiRel(sysm, P, S, x1):
    return kl(sysm, post(sysm, S, x1), partsPost(sysm, P, x1))

def eiAcross(sysm, P, S, x1):
    return ei(sysm, S, x1) if len(P) == 1 else eiRel(sysm, P, S, x1)

def normP(P, S):
    return len(S) if len(P) == 1 else (len(P) - 1) * min(len(M) for M in P)

def partitions(lst):
    if not lst: yield []; return
    first, rest = lst[0], lst[1:]
    for p in partitions(rest):
        for k in range(len(p)):
            yield p[:k] + [[first] + p[k]] + p[k+1:]
        yield [[first]] + p

def phi(sysm, S, x1, bip=False, ret=False):
    S = frozenset(S)
    if not S: return (0.0, None) if ret else 0.0
    best = None
    for P in partitions(sorted(S)):
        if bip and len(P) > 2: continue
        P = [frozenset(M) for M in P]
        e = eiAcross(sysm, P, S, x1)
        key = (round(e / normP(P, S), 12), round(e, 12))
        if best is None or key < best[0]: best = (key, e, P)
    return (best[1], best[2]) if ret else best[1]

def subsets(N):
    for m in range(1, 2**N):
        yield frozenset(i for i in range(N) if m >> i & 1)

def is_complex(sysm, x1, S, ph):
    return ph[S] > 1e-12 and all(ph[T] <= ph[S] + 1e-12 for T in ph if S <= T)

def is_main(sysm, x1, S, ph):
    return is_complex(sysm, x1, S, ph) and all(ph[R] < ph[S] - 1e-12 for R in ph if R < S)

def det(N, fn, noise=None):
    """deterministic unit rules fn(i, s) -> 0/1"""
    def prob(i, s, b):
        return F(1) if fn(i, s) == b else F(0)
    return Sys(N, prob)
