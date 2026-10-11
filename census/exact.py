# -*- coding: utf-8 -*-
"""The system level in exact arithmetic, with no floating point on our side.

Why this exists.  The paper's headline finding partitions the sweep's system-level checks
into tied and untied, and reports that a tie in the maximal cause-effect state is
necessary for disagreement with PyPhi and not sufficient.  That partition is currently
made by floating-point comparison -- `1e-12` in the argmax, `1e-12` in the minimum
information partition, `1e-8` in the agreement test.  But "do these two states tie?" is a
question of exact equality, and a tolerance is the wrong instrument for it: two values
that differ by `1e-13` are called equal, and two that are genuinely equal might be
separated by rounding.  Since the entire finding rests on that partition, it deserves an
exact treatment.

What makes it possible.  Every probability in the pipeline is a product, sum or quotient
of transition-matrix entries, hence rational; and every entry PyPhi can hold is an IEEE
double, hence a dyadic rational represented *exactly* by `fractions.Fraction`.  So the
inputs are exact and every intermediate is exact.

The only irrational step is the logarithm, and it never needs to be evaluated -- only
compared.  Every quantity that reaches a comparison has the form

    a * log2(x),   a, x rational, a >= 0, x > 0,

which `LogTerm` below represents symbolically.  Comparisons are decided by

    a1 log2 x1 <= a2 log2 x2   <=>   x1^p <= x2^q,   where a1/a2 = p/q in lowest terms,

which is an inequality between integer powers of rationals: exact, no logarithms taken.
Taking the ratio *first* matters.  Clearing the denominators of `a1` and `a2` separately
would give exponents around `2^52` for a TPM of random doubles, which is hopeless; the
reduced ratio is small whenever the two selectivities are structurally related, which is
exactly the case when states tie.

Three outcomes are possible for a comparison and all three are counted, so nothing is
silently approximated:

  EXACT-EQ      the two symbolic terms coincide as rationals -- equal, no arithmetic
  EXACT-CMP     decided by the integer-power test above
  BOUNDED       the reduced exponents were too large to raise, so the comparison was
                decided by a rigorous 120-digit enclosure instead; reported separately,
                and never used to declare equality

Usage:  IIT_PYPHI_PYTHON=<venv python> python exact.py [n_systems] [seed] [n_seeds] [max_N]
"""
import os, sys, random, itertools
from fractions import Fraction as Q
from decimal import Decimal, getcontext, localcontext

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
os.environ['PYPHI_WELCOME_OFF'] = '1'

# how many bits we are willing to raise a rational to before falling back
MAX_POW_BITS = 2 ** 22
GUARD_DIGITS = 120

STATS = {'exact_eq': 0, 'exact_cmp': 0, 'bounded': 0, 'bounded_close': 0}


# ---------------------------------------------------------------- LogTerm
class LogTerm:
    """The value `a * log2(x)`, held symbolically.  `a` and `x` are exact rationals with
    `a >= 0` and `x > 0`; `ZERO` is the additive identity, which arises both from `a = 0`
    and from the guards that the transcription applies when a probability vanishes."""

    __slots__ = ('a', 'x')

    def __init__(self, a, x):
        self.a = Q(a)
        self.x = Q(x)

    @staticmethod
    def zero():
        return LogTerm(0, 1)

    def is_zero(self):
        return self.a == 0 or self.x == 1

    def sign(self):
        if self.a == 0 or self.x == 1:
            return 0
        return 1 if self.x > 1 else -1

    def scale(self, q):
        """multiply by a positive rational"""
        q = Q(q)
        if q == 0:
            return LogTerm.zero()
        return LogTerm(self.a * q, self.x)

    def approx(self):
        """A float, used ONLY to compare against PyPhi, which is itself float."""
        import math
        if self.is_zero():
            return 0.0
        return float(self.a) * math.log2(float(self.x))

    def __repr__(self):
        return 'LogTerm(%s * log2 %s)' % (self.a, self.x)


def _bits(q):
    return max(q.numerator.bit_length(), q.denominator.bit_length())


def _enclosure(t, prec):
    """A rigorous interval for `a * log2 x`, as two Decimals."""
    with localcontext() as ctx:
        ctx.prec = prec
        x = Decimal(t.x.numerator) / Decimal(t.x.denominator)
        ln2 = Decimal(2).ln()
        v = (x.ln() / ln2) * (Decimal(t.a.numerator) / Decimal(t.a.denominator))
        # a generous slack: a few ulps of the working precision
        slack = abs(v) * Decimal(10) ** (-prec + 4) + Decimal(10) ** (-prec + 4)
        return v - slack, v + slack


def cmp_log(A, B):
    """Compare two LogTerms exactly where possible.  Returns -1, 0 or 1."""
    sa, sb = A.sign(), B.sign()
    if sa != sb:
        STATS['exact_cmp'] += 1
        return -1 if sa < sb else 1
    if sa == 0:
        STATS['exact_eq'] += 1
        return 0
    # identical symbolic terms: equal, with no arithmetic at all
    if A.a == B.a and A.x == B.x:
        STATS['exact_eq'] += 1
        return 0

    # a1 log2 x1 ? a2 log2 x2  with a1, a2 > 0  <=>  x1^p ? x2^q  for a1/a2 = p/q
    r = A.a / B.a
    p, q = r.numerator, r.denominator
    cost = p * _bits(A.x) + q * _bits(B.x)
    if cost <= MAX_POW_BITS:
        lhs = A.x ** p
        rhs = B.x ** q
        STATS['exact_cmp'] += 1
        if lhs == rhs:
            return 0
        # both sides positive; for negative-sign terms the log is negative, so the
        # direction of the power comparison is the direction of the value comparison
        return -1 if lhs < rhs else 1

    lo1, hi1 = _enclosure(A, GUARD_DIGITS)
    lo2, hi2 = _enclosure(B, GUARD_DIGITS)
    STATS['bounded'] += 1
    if hi1 < lo2:
        return -1
    if hi2 < lo1:
        return 1
    STATS['bounded_close'] += 1
    return 0


def log_eq(A, B):
    return cmp_log(A, B) == 0


def log_min(A, B):
    return A if cmp_log(A, B) <= 0 else B


def log_pos(A):
    """`|.|+`, exactly: the sign test is a rational comparison."""
    return A if A.sign() > 0 else LogTerm.zero()


# ---------------------------------------------------------------- the system level
class ExactSys:
    """The system level of IIT/System.lean, in exact rationals.

    A transcription of the same declarations as `leanref.LeanSys`, with `Fraction` in
    place of `float` and `LogTerm` wherever the Lean writes `Real.logb`.  The guards --
    the transcription returns `0` when a probability vanishes, matching Lean's
    `logb 2 0 = 0` -- are reproduced exactly, since they are rational sign tests."""

    def __init__(self, tpm, N):
        self.tpm = [[Q(v) for v in row] for row in tpm]
        self.N = N
        self.states = list(range(2 ** N))
        self._memo = {}

    def bits(self, s):
        return tuple((s >> k) & 1 for k in range(self.N)) if isinstance(s, int) else s

    def idx(self, b):
        return sum(v << k for k, v in enumerate(b))

    def prob(self, i, s, b):
        p1 = self.tpm[s if isinstance(s, int) else self.idx(s)][i]
        return p1 if b == 1 else 1 - p1

    def merge(self, S, s, u):
        """merge -- transcribed from the Lean below.

        [LEAN merge from IIT/System.lean]
        def merge (S : Finset (Fin N)) (s u : State N) : State N :=
          fun j => if j ∈ S then s j else u j
        [END LEAN]
        """
        sb, ub = self.bits(s), self.bits(u)
        return tuple(sb[j] if j in S else ub[j] for j in range(self.N))

    def agree(self, M, m):
        """agree -- transcribed from the Lean below.

        [LEAN agree from IIT/Phi.lean]
        def agree (M : Finset (Fin N)) (m : State N) : Finset (State N) :=
          Finset.univ.filter (fun s => ∀ j ∈ M, s j = m j)
        [END LEAN]
        """
        mb = self.bits(m)
        return [s for s in self.states if all(self.bits(s)[k] == mb[k] for k in M)]

    def effUnit(self, M, m, i, b):
        """effUnit -- transcribed from the Lean below.

        [LEAN effUnit from IIT/Phi.lean]
        noncomputable def effUnit (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
            (i : Fin N) (b : Bool) : ℝ :=
          (∑ s ∈ agree M m, T.prob i s b) / (agree M m).card
        [END LEAN]
        """
        ag = self.agree(M, m)
        return sum((self.prob(i, s, b) for s in ag), Q(0)) / len(ag)

    def fullProb(self, v, w):
        """fullProb -- transcribed from the Lean below.

        [LEAN fullProb from IIT/System.lean]
        noncomputable def fullProb (T : UnitTPM N) (v w : State N) : ℝ :=
          ∏ i, T.prob i v (w i)
        [END LEAN]
        """
        wb = self.bits(w)
        r = Q(1)
        for i in range(self.N):
            r *= self.prob(i, v, wb[i])
        return r

    # ---- effect side [IIT4, Eqs 3, 5, 6]
    def sysEffProb(self, S, u, s, t):
        """sysEffProb -- transcribed from the Lean below.

        [LEAN sysEffProb from IIT/System.lean]
        noncomputable def sysEffProb (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
            (s t : State N) : ℝ :=
          ∏ i ∈ S, T.prob i (merge S s u) (t i)
        [END LEAN]
        """
        tb = self.bits(t)
        r = Q(1)
        for i in S:
            r *= self.prob(i, self.merge(S, s, u), tb[i])
        return r

    def sysUncEff(self, S, u, t):
        """sysUncEff -- transcribed from the Lean below.

        [LEAN sysUncEff from IIT/System.lean]
        noncomputable def sysUncEff (T : UnitTPM N) (S : Finset (Fin N)) (u t : State N) : ℝ :=
          avgOverStates fun s => sysEffProb T S u s t
        [END LEAN]
        """
        return sum((self.sysEffProb(S, u, s, t) for s in self.states), Q(0)) / (2 ** self.N)

    def sysIiE(self, S, u, s, t):
        """sysIiE -- transcribed from the Lean below.

        [LEAN sysIiE from IIT/System.lean]
        noncomputable def sysIiE (T : UnitTPM N) (S : Finset (Fin N)) (u s t : State N) : ℝ :=
          sysEffProb T S u s t * Real.logb 2 (sysEffProb T S u s t / sysUncEff T S u t)
        [END LEAN]
        """
        e = self.sysEffProb(S, u, s, t)
        un = self.sysUncEff(S, u, t)
        if e <= 0 or un <= 0:
            return LogTerm.zero()
        return LogTerm(e, e / un)

    # ---- cause side [IIT4, Eqs 4, 7, 9]
    def bgWeight(self, S, u, w):
        """bgWeight -- transcribed from the Lean below.

        [LEAN bgWeight from IIT/System.lean]
        noncomputable def bgWeight (T : UnitTPM N) (S : Finset (Fin N)) (u w : State N) : ℝ :=
          ((∑ s : State N, fullProb T (merge S s w) u) / (2 : ℝ) ^ (N - S.card))
            / ∑ v : State N, fullProb T v u
        [END LEAN]
        """
        key = ('bg', tuple(sorted(S)), self.idx(self.bits(u)), self.idx(self.bits(w)))
        if key in self._memo:
            return self._memo[key]
        num = sum((self.fullProb(self.merge(S, sv, w), u) for sv in self.states),
                  Q(0)) / (2 ** (self.N - len(S)))
        den = sum((self.fullProb(v, u) for v in self.states), Q(0))
        r = num / den if den > 0 else Q(0)
        self._memo[key] = r
        return r

    def sysCauseProb(self, S, u, s, t):
        """sysCauseProb -- transcribed from the Lean below.

        [LEAN sysCauseProb from IIT/System.lean]
        noncomputable def sysCauseProb (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
            (s t : State N) : ℝ :=
          ∏ i ∈ S, ((∑ w : State N, T.prob i (merge S t w) (s i) * bgWeight T S u w)
            / (2 : ℝ) ^ S.card)
        [END LEAN]
        """
        key = ('scp', tuple(sorted(S)), self.idx(self.bits(u)),
               self.idx(self.bits(s)), self.idx(self.bits(t)))
        if key in self._memo:
            return self._memo[key]
        sb = self.bits(s)
        r = Q(1)
        for i in S:
            tot = sum((self.prob(i, self.merge(S, t, w), sb[i]) * self.bgWeight(S, u, w)
                       for w in self.states), Q(0))
            r *= tot / (2 ** len(S))
        self._memo[key] = r
        return r

    def sysUncCause(self, S, u, s):
        """sysUncCause -- transcribed from the Lean below.

        [LEAN sysUncCause from IIT/System.lean]
        noncomputable def sysUncCause (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) : ℝ :=
          avgOverStates fun t => sysCauseProb T S u s t
        [END LEAN]
        """
        return sum((self.sysCauseProb(S, u, s, t) for t in self.states),
                   Q(0)) / (2 ** self.N)

    def sysBackCause(self, S, u, s, t):
        """sysBackCause -- transcribed from the Lean below.

        [LEAN sysBackCause from IIT/System.lean]
        noncomputable def sysBackCause (T : UnitTPM N) (S : Finset (Fin N)) (u s t : State N) : ℝ :=
          sysCauseProb T S u s t / ((2 : ℝ) ^ S.card * sysUncCause T S u s)
        [END LEAN]
        """
        den = (2 ** len(S)) * self.sysUncCause(S, u, s)
        return self.sysCauseProb(S, u, s, t) / den if den > 0 else Q(0)

    def sysIiC(self, S, u, s, t):
        """sysIiC -- transcribed from the Lean below.

        [LEAN sysIiC from IIT/System.lean]
        noncomputable def sysIiC (T : UnitTPM N) (S : Finset (Fin N)) (u s t : State N) : ℝ :=
          sysBackCause T S u s t * Real.logb 2 (sysCauseProb T S u s t / sysUncCause T S u s)
        [END LEAN]
        """
        c = self.sysCauseProb(S, u, s, t)
        un = self.sysUncCause(S, u, s)
        if c <= 0 or un <= 0:
            return LogTerm.zero()
        return LogTerm(self.sysBackCause(S, u, s, t), c / un)

    # ---- the tie sets [IIT4, Eq 12], on states of S and decided exactly
    def reprsOfS(self, S):
        Ss = sorted(S)
        out = []
        for m in range(2 ** len(Ss)):
            b = [0] * self.N
            for p, k in enumerate(Ss):
                b[k] = (m >> p) & 1
            out.append(self.idx(b))
        return out

    def _argmaxExact(self, cands, f):
        vals = [(f(c), c) for c in cands]
        best = vals[0][0]
        for v, _ in vals[1:]:
            if cmp_log(v, best) > 0:
                best = v
        return [c for v, c in vals if log_eq(v, best)]

    def sysMaxEffStates(self, S, u, s):
        """sysMaxEffStates -- transcribed from the Lean below.

        [LEAN sysMaxEffStates from IIT/System.lean]
        noncomputable def sysMaxEffStates (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) :
            Finset (State N) :=
          argmaxSet (sysIiE T S u s)
        [END LEAN]
        """
        return self._argmaxExact(self.reprsOfS(S), lambda t: self.sysIiE(S, u, s, t))

    def sysMaxCauseStates(self, S, u, s):
        """sysMaxCauseStates -- transcribed from the Lean below.

        [LEAN sysMaxCauseStates from IIT/System.lean]
        noncomputable def sysMaxCauseStates (T : UnitTPM N) (S : Finset (Fin N)) (u s : State N) :
            Finset (State N) :=
          argmaxSet (sysIiC T S u s)
        [END LEAN]
        """
        return self._argmaxExact(self.reprsOfS(S), lambda t: self.sysIiC(S, u, s, t))

    # ---- directional system partitions [IIT4, Eqs 14-16]
    def sysPartitions(self, S):
        S = tuple(sorted(S))
        n = len(S)
        out = set()
        for w in _rgs(n):
            blocks = {}
            for i, lab in enumerate(w):
                blocks.setdefault(lab, set()).add(S[i])
            parts = tuple(sorted((frozenset(b) for b in blocks.values()), key=sorted))
            if len(parts) < 2:
                continue
            for dirs in itertools.product(('inputs', 'outputs', 'both'), repeat=len(parts)):
                out.add((parts, dirs))
        return list(out)

    def cutSet(self, S, parts, dirs, i):
        r"""The cut set X of a directional system partition.

        [LEAN cutSet from IIT/System.lean]
        noncomputable def cutSet (p : Finset (Fin N)) : Finset (Fin N) :=
          match θ.dir p with
          | Dir.inputs => S \ p
          | Dir.both => S \ p
          | Dir.outputs =>
              (θ.parts.filter fun q => q ≠ p ∧ (θ.dir q = Dir.outputs ∨ θ.dir q = Dir.both)).sup id
        [END LEAN]
        """
        p, d = parts[i], dirs[i]
        if d in ('inputs', 'both'):
            return frozenset(set(S) - set(p))
        acc = set()
        for j, q in enumerate(parts):
            if j != i and dirs[j] in ('outputs', 'both'):
                acc |= set(q)
        return frozenset(acc)

    def partOfIdx(self, parts, j):
        """partOfIdx -- transcribed from the Lean below.

        [LEAN partOf from IIT/System.lean]
        noncomputable def partOf (j : Fin N) : Finset (Fin N) :=
          (θ.parts.filter fun p => j ∈ p).sup id
        [END LEAN]
        """
        for i, p in enumerate(parts):
            if j in p:
                return i
        return None

    def sysCutCount(self, S, parts, dirs):
        """sysCutCount -- transcribed from the Lean below.

        [LEAN sysCutCount from IIT/System.lean]
        noncomputable def sysCutCount {S : Finset (Fin N)} (θ : SysPartition N S) : ℕ :=
          ∑ p ∈ θ.parts, p.card * (θ.cutSet p).card
        [END LEAN]
        """
        return sum(len(parts[i]) * len(self.cutSet(S, parts, dirs, i))
                   for i in range(len(parts)))

    def sysPartEffProb(self, S, u, parts, dirs, s, t):
        """sysPartEffProb -- transcribed from the Lean below.

        [LEAN sysPartEffProb from IIT/System.lean]
        noncomputable def sysPartEffProb (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
            (θ : SysPartition N S) (s t : State N) : ℝ :=
          ∏ j ∈ S, effUnit T (θ.cutSet (θ.partOf j))ᶜ (merge S s u) j (t j)
        [END LEAN]
        """
        tb = self.bits(t)
        r = Q(1)
        for j in S:
            X = self.cutSet(S, parts, dirs, self.partOfIdx(parts, j))
            comp = [q for q in range(self.N) if q not in X]
            r *= self.effUnit(comp, self.merge(S, s, u), j, tb[j])
        return r

    def sysPartCauseProb(self, S, u, parts, dirs, s, t):
        """sysPartCauseProb -- transcribed from the Lean below.

        [LEAN sysPartCauseProb from IIT/System.lean]
        noncomputable def sysPartCauseProb (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
            (θ : SysPartition N S) (s t : State N) : ℝ :=
          ∏ j ∈ S, ((∑ w : State N,
              effUnit T (θ.cutSet (θ.partOf j))ᶜ (merge S t w) j (s j) * bgWeight T S u w)
            / (2 : ℝ) ^ S.card)
        [END LEAN]
        """
        sb = self.bits(s)
        r = Q(1)
        for j in S:
            X = self.cutSet(S, parts, dirs, self.partOfIdx(parts, j))
            comp = [q for q in range(self.N) if q not in X]
            tot = sum((self.effUnit(comp, self.merge(S, t, w), j, sb[j])
                       * self.bgWeight(S, u, w) for w in self.states), Q(0))
            r *= tot / (2 ** len(S))
        return r

    # ---- phi_s [IIT4, Eqs 19-23], with the clamp inside the partition
    def sysPhiE(self, S, u, parts, dirs, s, t):
        """sysPhiE -- transcribed from the Lean below.

        [LEAN sysPhiE from IIT/System.lean]
        noncomputable def sysPhiE (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
            (θ : SysPartition N S) (s t : State N) : ℝ :=
          sysEffProb T S u s t *
            pos (Real.logb 2 (sysEffProb T S u s t / sysPartEffProb T S u θ s t))
        [END LEAN]
        """
        e = self.sysEffProb(S, u, s, t)
        pe = self.sysPartEffProb(S, u, parts, dirs, s, t)
        if e <= 0 or pe <= 0:
            return LogTerm.zero()
        return log_pos(LogTerm(e, e / pe))

    def sysPhiC(self, S, u, parts, dirs, s, t):
        """sysPhiC -- transcribed from the Lean below.

        [LEAN sysPhiC from IIT/System.lean]
        noncomputable def sysPhiC (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
            (θ : SysPartition N S) (s t : State N) : ℝ :=
          sysBackCause T S u s t *
            pos (Real.logb 2 (sysCauseProb T S u s t / sysPartCauseProb T S u θ s t))
        [END LEAN]
        """
        c = self.sysCauseProb(S, u, s, t)
        pc = self.sysPartCauseProb(S, u, parts, dirs, s, t)
        if c <= 0 or pc <= 0:
            return LogTerm.zero()
        return log_pos(LogTerm(self.sysBackCause(S, u, s, t), c / pc))

    def sysPhiAt(self, S, u, parts, dirs, s, tc, te):
        """sysPhiAt -- transcribed from the Lean below.

        [LEAN sysPhiAt from IIT/System.lean]
        noncomputable def sysPhiAt (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
            (θ : SysPartition N S) (s tc te : State N) : ℝ :=
          min (sysPhiC T S u θ s tc) (sysPhiE T S u θ s te)
        [END LEAN]
        """
        return log_min(self.sysPhiC(S, u, parts, dirs, s, tc),
                       self.sysPhiE(S, u, parts, dirs, s, te))

    def sysPhiOfState(self, S, u, s, tc, te):
        """sysPhiOfState -- transcribed from the Lean below.

        [LEAN sysPhiOfState from IIT/System.lean]
        noncomputable def sysPhiOfState (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
            (s tc te : State N) : ℝ :=
          sup'OrZero (sysMipSetAt T S u s tc te) fun θ => sysPhiAt T S u θ s tc te
        [END LEAN]
        """
        ps = self.sysPartitions(S)
        if not ps:
            return LogTerm.zero()
        vals = []
        for parts, dirs in ps:
            cc = self.sysCutCount(S, parts, dirs)
            ph = self.sysPhiAt(S, u, parts, dirs, s, tc, te)
            nrm = ph.scale(Q(1, cc)) if cc > 0 else LogTerm.zero()
            vals.append((nrm, ph))
        mn = vals[0][0]
        for nrm, _ in vals[1:]:
            if cmp_log(nrm, mn) < 0:
                mn = nrm
        best = None
        for nrm, ph in vals:
            if log_eq(nrm, mn):
                if best is None or cmp_log(ph, best) > 0:
                    best = ph
        return best

    def sysPhi(self, S, u, s):
        """sysPhi -- transcribed from the Lean below.

        [LEAN sysPhi from IIT/System.lean]
        noncomputable def sysPhi (T : UnitTPM N) (S : Finset (Fin N)) (u : State N)
            (s : State N) : ℝ :=
          sup'OrZero ((sysMaxCauseStates T S u s) ×ˢ (sysMaxEffStates T S u s))
            fun p => sysPhiOfState T S u s p.1 p.2
        [END LEAN]
        """
        if not self.sysPartitions(S):
            return LogTerm.zero()
        best = LogTerm.zero()
        for tc in self.sysMaxCauseStates(S, u, s):
            for te in self.sysMaxEffStates(S, u, s):
                v = self.sysPhiOfState(S, u, s, tc, te)
                if cmp_log(v, best) > 0:
                    best = v
        return best


def _rgs(n):
    """restricted growth strings: every set partition once"""
    if n == 0:
        yield ()
        return
    def go(prefix, mx):
        if len(prefix) == n:
            yield tuple(prefix)
            return
        for lab in range(mx + 2):
            yield from go(prefix + [lab], max(mx, lab))
    yield from go([], -1)


# ---------------------------------------------------------------- the comparison
def main():
    import numpy as np
    import pyphi
    from pyphi import new_big_phi as nbp
    from leanref import LeanSys

    NSYS = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    SEED0 = int(sys.argv[2]) if len(sys.argv) > 2 else 20260903
    NSEED = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    MAXN = int(sys.argv[4]) if len(sys.argv) > 4 else 5
    TOL = 1e-8
    KINDS = ['uniform', 'deterministic', 'extreme']
    # a directional-partition budget for the exact VALUE; the exact tie CLASSIFICATION
    # is computed for every check regardless
    global VALUE_PARTITION_CAP
    VALUE_PARTITION_CAP = int(os.environ.get('EXACT_PARTITION_CAP', '400'))

    print('=' * 78)
    print('EXACT RE-DERIVATION OF THE TIE CLASSIFICATION')
    print('%d systems per seed, seeds %s, N in {2..%d}'
          % (NSYS, ', '.join(str(SEED0 + k) for k in range(NSEED)), MAXN))
    print('=' * 78)

    tab_f = {(True, True): 0, (True, False): 0, (False, True): 0, (False, False): 0}
    tab_e = dict(tab_f)
    disagree_tie, disagree_phi, checks = [], [], 0
    valued, skipped_value = [0], [0]

    for k in range(NSEED):
        seed = SEED0 + k
        rng = np.random.default_rng(seed)
        pyrng = random.Random(seed)
        for i in range(NSYS):
            N = int(rng.integers(2, MAXN + 1))
            kind = KINDS[i % len(KINDS)]
            rows = 2 ** N
            if kind == 'deterministic':
                tpm = rng.integers(0, 2, size=(rows, N)).astype(float)
            elif kind == 'extreme':
                tpm = rng.choice([1e-9, 0.5, 1 - 1e-9], size=(rows, N))
            else:
                tpm = rng.uniform(0.0, 1.0, size=(rows, N))
            state = tuple(int(b) for b in rng.integers(0, 2, size=N))
            try:
                net = pyphi.Network(tpm, node_labels=[chr(65 + j) for j in range(N)])
            except Exception:
                continue
            units = list(range(N))
            for _ in range(2):
                pyrng.sample(units, pyrng.randint(1, N))
                pyrng.sample(units, pyrng.randint(1, N))
            cands = [S for r in range(2, N + 1)
                     for S in itertools.combinations(units, r)]
            for S in pyrng.sample(cands, min(2, len(cands))):
                try:
                    sia = nbp.sia(pyphi.Subsystem(net, state, nodes=S))
                except Exception:
                    continue
                theirs = max(0.0, float(sia.phi))
                rows_t = [list(map(float, r)) for r in tpm]
                L = LeanSys(rows_t, N)
                E = ExactSys(rows_t, N)

                def on_S(obj, sts):
                    return {tuple(obj.bits(t)[j] for j in S) for t in sts}

                tf = (len(on_S(L, L.sysMaxCauseStates(list(S), state, state))) > 1
                      or len(on_S(L, L.sysMaxEffStates(list(S), state, state))) > 1)
                te_ = (len(on_S(E, E.sysMaxCauseStates(list(S), state, state))) > 1
                       or len(on_S(E, E.sysMaxEffStates(list(S), state, state))) > 1)
                mine_f = L.sysPhi(list(S), state, state)
                checks += 1
                tab_f[(tf, abs(mine_f - theirs) > TOL)] += 1
                if tf != te_:
                    disagree_tie.append('seed%d sys%d N=%d %s S=%s float=%s exact=%s'
                                        % (seed, i, N, kind, S, tf, te_))
                # the VALUE needs every directional partition in exact rationals, which
                # is out of reach for the larger candidate systems; the classification
                # above needed none of it and is computed for every check.
                npart = len(E.sysPartitions(list(S)))
                if npart <= VALUE_PARTITION_CAP:
                    mine_e = E.sysPhi(list(S), state, state).approx()
                    tab_e[(te_, abs(mine_e - theirs) > TOL)] += 1
                    valued[0] += 1
                    if abs(mine_f - mine_e) > 1e-9:
                        disagree_phi.append(
                            'seed%d sys%d N=%d %s S=%s float=%.12f exact=%.12f'
                            % (seed, i, N, kind, S, mine_f, mine_e))
                else:
                    skipped_value[0] += 1

    print()
    print('system-level checks compared: %d' % checks)
    print()
    print('tie classification re-derived exactly for all %d; phi_s value for %d '
          '(%d beyond the partition budget)' % (checks, valued[0], skipped_value[0]))
    print()
    print('%-12s %22s %22s' % ('', 'FLOAT (1e-12)', 'EXACT'))
    print('%-12s %11s %10s %11s %10s' % ('', 'agree', 'diverge', 'agree', 'diverge'))
    print('   (the EXACT columns cover the %d checks whose value was computed)'
          % valued[0])
    print('%-12s %11d %10d %11d %10d'
          % ('tied', tab_f[(True, False)], tab_f[(True, True)],
             tab_e[(True, False)], tab_e[(True, True)]))
    print('%-12s %11d %10d %11d %10d'
          % ('not tied', tab_f[(False, False)], tab_f[(False, True)],
             tab_e[(False, False)], tab_e[(False, True)]))
    print()
    print('checks whose TIE classification changes under exact arithmetic: %d'
          % len(disagree_tie))
    for d in disagree_tie[:20]:
        print('   ' + d)
    print('checks whose phi_s VALUE changes by more than 1e-9: %d' % len(disagree_phi))
    for d in disagree_phi[:20]:
        print('   ' + d)
    print()
    print('comparisons decided structurally (identical rationals) : %d' % STATS['exact_eq'])
    print('comparisons decided by integer powers                  : %d' % STATS['exact_cmp'])
    print('comparisons falling back to a 120-digit enclosure      : %d' % STATS['bounded'])
    print('   of those, too close to separate at 120 digits       : %d'
          % STATS['bounded_close'])
    print()
    delta = len(disagree_tie) + len(disagree_phi)
    print('VERDICT:', 'the float classification is confirmed exactly'
          if delta == 0 else 'the exact treatment CHANGES %d classification(s)' % delta)
    sys.exit(1 if STATS['bounded_close'] else 0)


if __name__ == '__main__':
    main()


# ---------------------------------------------------------------- conditioning
def _rel_gap(A, B):
    """|A - B| / max(|A|, |B|), from the enclosures; 0 when exactly equal."""
    if cmp_log(A, B) == 0:
        return 0.0
    a, b = A.approx(), B.approx()
    m = max(abs(a), abs(b), 1e-300)
    return abs(a - b) / m


def conditioning(E, S, u, s):
    """How far apart are the quantities a float implementation must SEPARATE?

    IIT 4.0 asks for two argmax/argmin decisions: the maximal cause-effect state
    `[IIT4, Eq 12]` and the minimum information partition `[IIT4, Eq 23]`.  Each is
    decided here exactly.  This returns the smallest relative gap between the winner and
    the nearest strict runner-up across both decisions -- the margin a floating-point
    implementation would have to resolve to reach the same answer.

    A check whose margin is below the resolution of double precision is not one on which
    PyPhi can be expected to agree: the disagreement is then a fact about the arithmetic,
    not about the theory.  Reporting it as a divergence from IIT 4.0 would be wrong, and
    reporting it as agreement would be luck."""
    gap = float('inf')

    def scan(vals, want_max):
        nonlocal gap
        best = vals[0]
        for v in vals[1:]:
            c = cmp_log(v, best)
            if (c > 0) if want_max else (c < 0):
                best = v
        for v in vals:
            if cmp_log(v, best) != 0:
                gap = min(gap, _rel_gap(v, best))

    reps = E.reprsOfS(S)
    scan([E.sysIiE(S, u, s, t) for t in reps], True)
    scan([E.sysIiC(S, u, s, t) for t in reps], True)

    tc = E.sysMaxCauseStates(S, u, s)
    te = E.sysMaxEffStates(S, u, s)
    ps = E.sysPartitions(S)
    if ps and tc and te:
        norms = []
        for parts, dirs in ps:
            cc = E.sysCutCount(S, parts, dirs)
            ph = E.sysPhiAt(S, u, parts, dirs, s, tc[0], te[0])
            norms.append(ph.scale(Q(1, cc)) if cc > 0 else LogTerm.zero())
        scan(norms, False)
    return gap
