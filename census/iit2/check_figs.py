"""Independent numerical check of the [BT08] definitions as formalized in IIT2/Basic.lean.
cond (per element, [BT08 S1 s.3]) vs the old joint averaging. Base 2.
phi_all: all partitions (definition, p.5); phi_bip: bipartitions + total partition (p.9 numerics)."""
import itertools, math, sys

def states(n): return list(itertools.product([0,1], repeat=n))

def cond(prob, n, A, x1, x0, joint):
    out = [j for j in range(n) if j not in A]
    def mix(e):
        return tuple(x0[j] if j in A else e[j] for j in range(n))
    if joint:
        tot = 0.0
        for e in states(n):
            p = 1.0
            for i in A: p *= prob(i, mix(e), x1[i])
            tot += p
        return tot / 2**n
    p = 1.0
    for i in A:
        p *= sum(prob(i, mix(e), x1[i]) for e in states(n)) / 2**n
    return p

def post(prob, n, A, x1, joint):
    c = {x: cond(prob, n, A, x1, x, joint) for x in states(n)}
    z = sum(c.values()) / 2**n
    return {x: (c[x] / z if z > 0 else 0.0) for x in c}

def kl(p, q, n):
    return sum(p[x] * math.log2(p[x] / q[x]) for x in p if p[x] > 0) / 2**n

def partitions(s):
    s = list(s)
    if not s: yield []; return
    first, rest = s[0], s[1:]
    for p in partitions(rest):
        for k in range(len(p)):
            yield p[:k] + [[first] + p[k]] + p[k+1:]
        yield [[first]] + p

def phi(prob, n, S, x1, joint, bip):
    pS = post(prob, n, S, x1, joint)
    best = None
    for P in partitions(S):
        m = len(P)
        if bip and m > 2: continue
        if m == 1:
            e = kl(pS, {x: 1.0 for x in pS}, n); N = len(S)
        else:
            parts = [post(prob, n, M, x1, joint) for M in P]
            q = {x: math.prod(pp[x] for pp in parts) for x in pS}
            e = kl(pS, q, n); N = (m - 1) * min(len(M) for M in P)
        key = (round(e / N, 12), round(e, 12))
        if best is None or key < best: best = key
    return best[1]

def det(f):  # deterministic element rules f(i, state) -> 0/1
    return lambda i, s, b: 1.0 if f(i, s) == b else 0.0

def report(name, prob, n, S, x1):
    for joint in (False, True):
        lab = "joint     " if joint else "per-elem  "
        print(name, lab, "phi_all=%.3f" % phi(prob, n, S, x1, joint, False),
              "phi_bip=%.3f" % phi(prob, n, S, x1, joint, True))

# Fig 1: AND triple, n1=AND(n2,n3), n2=AND(n1,n3), n3=AND(n1,n2); x1=001 (p.3): ei = 3 bits.
andt = det(lambda i, s: int(all(s[j] for j in range(3) if j != i)))
print("Fig1 ei per-elem =", kl(post(andt, 3, [0,1,2], (0,0,1), False), {x:1.0 for x in states(3)}, 3))

# Fig 6 (my reading of the text, p.7): AND triple n1..n3 + copies n4,n5,n6 of n1,n2,n3.
def f6(i, s):
    if i < 3: return int(all(s[j] for j in range(3) if j != i))
    return s[i - 3]
p6 = det(f6)
x6 = (0, 0, 1, 1, 1, 0)  # triple 110 -> 001, copies hold the previous triple state 110
report("Fig6 A={1,2,3}", p6, 6, [0,1,2], x6)
report("Fig6 X        ", p6, 6, list(range(6)), x6)

# Fig 11 counter (p.11): n1 LSB toggles; n_k toggles iff n1..n_{k-1} all fire.
def f11(i, s): return s[i] ^ int(all(s[j] for j in range(i)))
p11 = det(f11)
for x1 in [(1,0,0,0), (0,1,1,0), (0,0,0,0)]:
    report("Fig11 x1=%s" % (x1,), p11, 4, [0,1,2,3], x1)

# Fig 14B (p.12-13): 4 elements, all-to-all with self, fire iff >=3 spikes; x1 = 1111
# (system repertoire = 5 equally weighted perturbations). Printed phi = .79 (bipartitions).
p14 = det(lambda i, s: int(sum(s) >= 3))
report("Fig14B", p14, 4, [0,1,2,3], (1,1,1,1))
pa = post(p14, 4, [0,1], (1,1,1,1), False)
print("Fig14B part {1,2} weights (per-elem):",
      sorted({round(pa[x] / 4, 3) for x in pa if pa[x] > 0}))
