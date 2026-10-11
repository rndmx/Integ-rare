# -*- coding: utf-8 -*-
"""T1 trend census (N = 3..6, uniform measure on the cube, u = s, ONE random state per TPM).

Question: does P(phi_s(univ) > 0) fall with N while small complexes persist?

Engine.  `FloatSys` below is a float transcription of `engine/exact.py::ExactSys` (the
system level of IIT/System.lean), with the same guards and the same selection rules
(argmax over tied cause/effect states, min over normalised partitions, max phi among the
minimisers) but memoised so that N = 5 (all candidates) and N = 6 (pairs + triples + univ)
are affordable.  It is used ONLY for speed; every decision that matters is checked:

  * ZERO / NONZERO of phi_s(S).  phi_s(S) = 0 iff some partition clamps a side
    (log2(p/q) <= 0) at every tied (tc, te) pair.  FloatSys records, per candidate, the
    margin of that decision (the smallest |log2 ratio| that decided it) and the relative
    gaps of the argmax / MIP selections.  A candidate whose margin or gap is below TOL is
    'borderline' and is re-decided with ExactSys (|S| <= 4), otherwise counted as unresolved.
  * Comparisons between two positive candidates closer than TOL (relative) are re-decided
    with ExactSys (|S| <= 4), otherwise counted as unresolved.
  * `calib` runs FloatSys against ExactSys on every candidate of several rows per N and
    reports sign agreement and the largest |float - exact| (exact via LogTerm.approx()).

IsComplex S := phi(S) > 0 and phi(S') < phi(S) for every OVERLAPPING S' != S (Lean, over
all candidates; |S| <= 1 has phi = 0, {} excluded).  Case split as in
results/first-pass/uniform_n3/census_n3.py: A0 unreachable; A max phi = 0; B1 univ is a
complex; B2 some complex, not univ; C max phi > 0 but no complex (only via ties);
flags B-multi (>= 2 complexes), B-notmax (a complex exists but an argmax is not one).
At N = 6 only pairs + triples + univ are computed, so the case is 'partial-*' (relative to
that family) and complexes are 'local' (undefeated within the family).

Usage:  python trend_census.py calib
        python trend_census.py run N NROWS MODE WORKERS     (MODE in all | ptu)
        python trend_census.py report
"""
import os, sys, time, json, csv, math, random, itertools

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from exact import ExactSys, cmp_log, LogTerm, _rgs   # noqa: E402

SEED_BASE = 20260926
TOL = 1e-9
EXACT_MAX_SIZE = 4          # exact re-decisions only for |S| <= this


# ------------------------------------------------------------------ combinatorics
_PART_CACHE = {}


def partitions_of(N, S):
    """[(cutcount, (comp_j for j in S)), ...] for every directional system partition of S,
    comp_j = complement (in Fin N) of the cut set of the part containing j, as a sorted
    tuple.  Pure combinatorics, mirrors ExactSys.sysPartitions / cutSet / partOfIdx."""
    S = tuple(sorted(S))
    key = (N, S)
    if key in _PART_CACHE:
        return _PART_CACHE[key]
    n = len(S)
    out = []
    seen = set()
    for w in _rgs(n):
        blocks = {}
        for i, lab in enumerate(w):
            blocks.setdefault(lab, set()).add(S[i])
        parts = tuple(sorted((frozenset(b) for b in blocks.values()), key=sorted))
        if len(parts) < 2:
            continue
        for dirs in itertools.product(('inputs', 'outputs', 'both'), repeat=len(parts)):
            if (parts, dirs) in seen:
                continue
            seen.add((parts, dirs))
            cuts = []
            for i, (p, d) in enumerate(zip(parts, dirs)):
                if d in ('inputs', 'both'):
                    X = frozenset(set(S) - set(p))
                else:
                    acc = set()
                    for j, q in enumerate(parts):
                        if j != i and dirs[j] in ('outputs', 'both'):
                            acc |= set(q)
                    X = frozenset(acc)
                cuts.append(X)
            cc = sum(len(p) * len(X) for p, X in zip(parts, cuts))
            comps = []
            for j in S:
                pi = next(i for i, p in enumerate(parts) if j in p)
                comps.append(tuple(q for q in range(N) if q not in cuts[pi]))
            out.append((cc, tuple(comps)))
    _PART_CACHE[key] = out
    return out


# ------------------------------------------------------------------ float engine
class FloatSys:
    """Float transcription of ExactSys for the census (u = s only used through the API).
    Every quantity depends on states only through their restriction to S or to a
    conditioning set, and that is what the memo keys use."""

    def __init__(self, tpm, N):
        self.N = N
        self.tpm = [[float(v) for v in row] for row in tpm]
        self.states = list(range(2 ** N))
        self.bitsT = [tuple((s >> k) & 1 for k in range(N)) for s in self.states]
        self._eu = {}
        self._agree = {}
        self._bg = {}
        self._full = {}

    def bits(self, s):
        return self.bitsT[s] if isinstance(s, int) else tuple(s)

    def idx(self, b):
        return sum(v << k for k, v in enumerate(b))

    def prob(self, i, s, b):
        p1 = self.tpm[s if isinstance(s, int) else self.idx(s)][i]
        return p1 if b == 1 else 1.0 - p1

    def merge(self, S, s, u):
        sb, ub = self.bits(s), self.bits(u)
        return tuple(sb[j] if j in S else ub[j] for j in range(self.N))

    def agree(self, M, m):
        mb = self.bits(m)
        key = (M, tuple(mb[k] for k in M))
        r = self._agree.get(key)
        if r is None:
            r = [s for s in self.states if all(self.bitsT[s][k] == mb[k] for k in M)]
            self._agree[key] = r
        return r

    def effUnit(self, M, m, i, b):
        """(sum over agree(M, m) of prob(i, s, b)) / |agree|, memoised on (M, m|M, i)."""
        mb = self.bits(m)
        key = (M, tuple(mb[k] for k in M), i)
        r = self._eu.get(key)
        if r is None:
            ag = self.agree(M, m)
            r = sum(self.tpm[s][i] for s in ag) / len(ag)
            self._eu[key] = r
        return r if b == 1 else 1.0 - r

    def fullProb(self, v, w):
        key = (v if isinstance(v, int) else self.idx(v), w if isinstance(w, int) else self.idx(w))
        r = self._full.get(key)
        if r is None:
            wb = self.bits(w)
            r = 1.0
            for i in range(self.N):
                r *= self.prob(i, key[0], wb[i])
            self._full[key] = r
        return r

    def reachable(self, u):
        return sum(self.fullProb(v, u) for v in self.states) > 0

    # ---- effect side
    def sysEffProb(self, S, u, s, t):
        m = self.merge(S, s, u)
        tb = self.bits(t)
        r = 1.0
        for i in S:
            r *= self.prob(i, m, tb[i])
        return r

    def reprs(self, S):
        Ss = sorted(S)
        out = []
        for m in range(2 ** len(Ss)):
            b = [0] * self.N
            for p, k in enumerate(Ss):
                b[k] = (m >> p) & 1
            out.append(self.idx(b))
        return out

    def sysUncEff(self, S, u, t):
        # avg over all 2^N s of sysEffProb(S, u, s, t); depends on s only via s|S
        reps = self.reprs(S)
        return sum(self.sysEffProb(S, u, s, t) for s in reps) / len(reps)

    # ---- cause side
    def bgWeight(self, S, u, w):
        """((sum_sv fullProb(merge(S, sv, w), u)) / 2^(N-|S|)) / sum_v fullProb(v, u);
        depends on w only via w|S^c."""
        wb = self.bits(w)
        comp = tuple(q for q in range(self.N) if q not in S)
        key = (S, tuple(wb[q] for q in comp), u)
        r = self._bg.get(key)
        if r is None:
            den = sum(self.fullProb(v, u) for v in self.states)
            if den > 0:
                num = sum(self.fullProb(x, u) for x in self.agree(comp, w))
                r = num / den
            else:
                r = 0.0
            self._bg[key] = r
        return r

    def bg_completions(self, S, u):
        """[(w_state, bgWeight)] over the 2^(N-|S|) backgrounds (w restricted to S^c,
        S-part zero)."""
        comp = tuple(q for q in range(self.N) if q not in S)
        out = []
        for m in range(2 ** len(comp)):
            b = [0] * self.N
            for p, k in enumerate(comp):
                b[k] = (m >> p) & 1
            w = self.idx(b)
            out.append((w, self.bgWeight(S, u, w)))
        return out

    def sysCauseProb(self, S, u, s, t, bgs):
        # prod_i (sum over all 2^N w of prob(i, merge(S,t,w), s_i) * bg(w)) / 2^|S|
        #   = prod_i sum over backgrounds wc of prob(i, (t|S, wc), s_i) * bg(wc)
        sb = self.bits(s)
        r = 1.0
        for i in S:
            tot = 0.0
            for w, bw in bgs:
                tot += self.prob(i, self.merge(S, t, w), sb[i]) * bw
            r *= tot
        return r

    def sysPartCauseProb(self, S, u, comps, s, t, bgs):
        sb = self.bits(s)
        r = 1.0
        for j, comp in zip(S, comps):
            tot = 0.0
            for w, bw in bgs:
                tot += self.effUnit(comp, self.merge(S, t, w), j, sb[j]) * bw
            r *= tot
        return r

    def sysPartEffProb(self, S, u, comps, s, t):
        m = self.merge(S, s, u)
        tb = self.bits(t)
        r = 1.0
        for j, comp in zip(S, comps):
            r *= self.effUnit(comp, m, j, tb[j])
        return r

    # ---- phi_s with diagnostics
    def sysPhi(self, S, u, s):
        """Returns (phi, diag) with diag = dict(margin, gap, clamp_side) where
        margin = smallest |log2 ratio| among the clamp decisions that determined
        zero/nonzero, gap = smallest relative gap among the argmax / MIP selections,
        clamp_side in {'', 'cause', 'effect', 'both'} = which side(s) some partition
        clamps at the selected (tc, te)."""
        S = tuple(sorted(S))
        diag = {'margin': float('inf'), 'gap': float('inf'), 'clamp_side': ''}
        if len(S) < 2:
            return 0.0, diag
        parts = partitions_of(self.N, S)
        reps = self.reprs(S)
        bgs = self.bg_completions(S, u)
        # effect side: maximal effect states
        iie = []
        unc_e = {}
        for t in reps:
            e = self.sysEffProb(S, u, s, t)
            un = self.sysUncEff(S, u, t)
            unc_e[t] = un
            iie.append((e * math.log2(e / un) if (e > 0 and un > 0) else 0.0, t))
        # cause side
        cps = {t: self.sysCauseProb(S, u, s, t, bgs) for t in reps}
        unc_c = sum(cps.values()) / len(reps)
        iic = []
        for t in reps:
            c = cps[t]
            if c > 0 and unc_c > 0:
                back = c / ((2 ** len(S)) * unc_c)
                iic.append((back * math.log2(c / unc_c), t))
            else:
                iic.append((0.0, t))
        tes, gap_e = _argmax(iie)
        tcs, gap_c = _argmax(iic)
        diag['gap'] = min(gap_e, gap_c)
        best = 0.0
        for tc in tcs:
            c = cps[tc]
            back = c / ((2 ** len(S)) * unc_c) if (c > 0 and unc_c > 0) else 0.0
            for te in tes:
                e = self.sysEffProb(S, u, s, te)
                vals = []
                min_lr_e = float('inf')
                min_lr_c = float('inf')
                for cc, comps in parts:
                    pe = self.sysPartEffProb(S, u, comps, s, te)
                    pc = self.sysPartCauseProb(S, u, comps, s, tc, bgs)
                    lr_e = math.log2(e / pe) if (e > 0 and pe > 0) else float('-inf')
                    lr_c = math.log2(c / pc) if (c > 0 and pc > 0) else float('-inf')
                    phE = e * lr_e if lr_e > 0 else 0.0
                    phC = back * lr_c if lr_c > 0 else 0.0
                    ph = min(phC, phE)
                    nrm = ph / cc if cc > 0 else 0.0
                    vals.append((nrm, ph))
                    if lr_e < min_lr_e:
                        min_lr_e = lr_e
                    if lr_c < min_lr_c:
                        min_lr_c = lr_c
                # min over normalised, then max ph among the minimisers (exact ties only)
                mn = min(v[0] for v in vals)
                nz = sorted({v[0] for v in vals})
                if len(nz) >= 2 and mn > 0:
                    diag['gap'] = min(diag['gap'], (nz[1] - nz[0]) / nz[1])
                v = max(ph for nrm, ph in vals if nrm == mn)
                # zero/nonzero margin: sign of min over partitions of min(lr_e, lr_c)
                m = min(min_lr_e, min_lr_c)
                diag['margin'] = min(diag['margin'], abs(m))
                side = ('cause' if min_lr_c <= 0 else '') + ('effect' if min_lr_e <= 0 else '')
                if side == 'causeeffect':
                    side = 'both'
                diag['clamp_side'] = side
                if v > best:
                    best = v
        return best, diag


def _argmax(vals):
    """vals = [(value, key)]. Returns (keys tied at the max in floats, relative gap to the
    runner-up)."""
    mx = max(v for v, _ in vals)
    keys = [k for v, k in vals if v == mx]
    others = [v for v, _ in vals if v != mx]
    if mx == 0:
        return keys, 0.0          # degenerate (all clamped): treat as borderline
    if not others:
        return keys, float('inf')
    return keys, (mx - max(others)) / abs(mx)


# ------------------------------------------------------------------ census
def candidates(N, mode):
    units = list(range(N))
    if mode == 'all':
        return [tuple(S) for r in range(2, N + 1) for S in itertools.combinations(units, r)]
    if mode == 'ptu':
        return ([tuple(S) for S in itertools.combinations(units, 2)]
                + [tuple(S) for S in itertools.combinations(units, 3)]
                + [tuple(units)])
    raise ValueError(mode)


def overlap(S, T):
    return bool(set(S) & set(T))


def random_tpm(seed, N):
    rng = random.Random(seed)
    return [[rng.random() for _ in range(N)] for _ in range(2 ** N)]


def random_state(seed, N):
    return random.Random(seed * 7919 + 1).randrange(2 ** N)


def wilson(k, n, z=1.959963984540054):
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    den = 1 + z * z / n
    c = (p + z * z / (2 * n)) / den
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / den
    return (max(0.0, c - h), min(1.0, c + h))


def classify(N, seed, idx, mode, exact_all=False):
    tpm = random_tpm(seed, N)
    u = random_state(seed, N)
    F = FloatSys(tpm, N)
    E = [None]
    cands = candidates(N, mode)
    univ = tuple(range(N))
    t0 = time.perf_counter()
    phis, diags, tim = {}, {}, {}
    for S in cands:
        t1 = time.perf_counter()
        phis[S], diags[S] = F.sysPhi(S, u, u)
        tim[S] = time.perf_counter() - t1
    t_float = time.perf_counter() - t0
    exact_cache = {}

    def exact_phi(S):
        if S not in exact_cache:
            if E[0] is None:
                E[0] = ExactSys(tpm, N)
            exact_cache[S] = E[0].sysPhi(list(S), u, u)
        return exact_cache[S]

    n_redecide_zero = n_redecide_cmp = n_unresolved = 0
    # ---- zero / nonzero
    pos = {}
    for S in cands:
        d = diags[S]
        borderline = d['margin'] < TOL or d['gap'] < TOL
        if not borderline:
            pos[S] = phis[S] > 0.0
        elif len(S) <= EXACT_MAX_SIZE:
            pos[S] = exact_phi(S).sign() > 0
            n_redecide_zero += 1
        else:
            pos[S] = phis[S] > 0.0
            n_unresolved += 1

    def less(T, S):
        """phi(T) < phi(S), exactly when both positive and within TOL (relative)."""
        nonlocal n_redecide_cmp, n_unresolved
        if not pos[T]:
            return pos[S]
        if not pos[S]:
            return False
        a, b = phis[T], phis[S]
        if abs(a - b) >= TOL * max(a, b):
            return a < b
        if max(len(T), len(S)) <= EXACT_MAX_SIZE:
            n_redecide_cmp += 1
            return cmp_log(exact_phi(T), exact_phi(S)) < 0
        n_unresolved += 1
        return a < b

    complexes = [S for S in cands if pos[S]
                 and all(less(T, S) for T in cands if T != S and overlap(S, T))]
    if any(pos.values()):
        best = max((S for S in cands if pos[S]), key=lambda S: phis[S])
        argmax = [best] + [S for S in cands if S != best and pos[S]
                           and not less(S, best) and not less(best, S)]
        maxpos = True
    else:
        best = max(cands, key=lambda S: phis[S])
        argmax = list(cands)
        maxpos = False
    reach = F.reachable(u)
    if not reach:
        case = 'A0'
    elif not maxpos:
        case = 'A'
    elif complexes:
        case = 'B1' if univ in complexes else 'B2'
    else:
        case = 'C'
    b_multi = len(complexes) >= 2
    b_notmax = bool(complexes) and any(S not in complexes for S in argmax)

    exact_checked = exact_sign_mismatch = 0
    exact_max_abs = 0.0
    if exact_all:
        for S in cands:
            ev = exact_phi(S)
            exact_checked += 1
            if (ev.sign() > 0) != pos[S]:
                exact_sign_mismatch += 1
            exact_max_abs = max(exact_max_abs, abs(ev.approx() - phis[S]))

    pairs = [S for S in cands if len(S) == 2]
    trips = [S for S in cands if len(S) == 3]
    pair_pos = sum(1 for S in pairs if pos[S])
    trip_pos = sum(1 for S in trips if pos[S])
    return {
        'N': N, 'seed': seed, 'idx': idx, 'state': u, 'mode': mode,
        'reachable': int(reach),
        'n_cands': len(cands),
        'phi_univ': repr(phis[univ]),
        'univ_pos': int(pos[univ]),
        'univ_clamp_side': diags[univ]['clamp_side'],
        'n_pairs': len(pairs), 'pairs_pos': pair_pos, 'any_pair_pos': int(pair_pos > 0),
        'n_trips': len(trips), 'trips_pos': trip_pos,
        'n_pos_cands': sum(1 for S in cands if pos[S]),
        'max_phi': repr(phis[best]),
        'case': case if mode == 'all' else 'partial-' + case,
        'n_complexes': len(complexes),
        'complex_sizes': json.dumps(sorted(len(S) for S in complexes)),
        'complexes': json.dumps([list(S) for S in complexes]),
        'b_multi': int(b_multi), 'b_notmax': int(b_notmax),
        'n_argmax': len(argmax),
        'argmax_size': len(argmax[0]) if maxpos else 0,
        'min_margin': repr(min(d['margin'] for d in diags.values())),
        'min_gap': repr(min(d['gap'] for d in diags.values())),
        'n_redecide_zero': n_redecide_zero, 'n_redecide_cmp': n_redecide_cmp,
        'n_unresolved': n_unresolved,
        'exact_checked': exact_checked, 'exact_sign_mismatch': exact_sign_mismatch,
        'exact_max_abs_diff': repr(exact_max_abs),
        't_float': round(t_float, 4), 't_row': round(time.perf_counter() - t0, 4),
        't_univ': round(tim[univ], 4),
        'phis': json.dumps({'-'.join(map(str, S)): phis[S] for S in cands}),
    }


COLS = ['N', 'seed', 'idx', 'state', 'mode', 'reachable', 'n_cands', 'phi_univ', 'univ_pos',
        'univ_clamp_side', 'n_pairs', 'pairs_pos', 'any_pair_pos', 'n_trips', 'trips_pos',
        'n_pos_cands', 'max_phi', 'case', 'n_complexes', 'complex_sizes', 'complexes',
        'b_multi', 'b_notmax', 'n_argmax', 'argmax_size', 'min_margin', 'min_gap',
        'n_redecide_zero', 'n_redecide_cmp', 'n_unresolved', 'exact_checked',
        'exact_sign_mismatch', 'exact_max_abs_diff', 't_float', 't_row', 't_univ', 'phis']


def work(args):
    return classify(*args)


def calib():
    """FloatSys vs ExactSys on every candidate: N = 3 (40 rows), N = 4 (8 rows), plus
    pairs + triples at N = 5 (3 rows) and N = 6 (2 rows) with exact checks of |S| <= 3."""
    out = []
    plan = [(3, 'all', 40), (4, 'all', 8), (5, 'ptu', 3), (6, 'ptu', 2)]
    for N, mode, n in plan:
        for i in range(n):
            seed = SEED_BASE + 7000000 + 1000000 * N + i   # disjoint from the run seeds
            t0 = time.perf_counter()
            if N <= 4:
                r = classify(N, seed, i, mode, exact_all=True)
            else:
                r = classify(N, seed, i, mode, exact_all=False)
                # exact check of pairs and triples only (univ too costly at N >= 5)
                tpm = random_tpm(seed, N)
                u = random_state(seed, N)
                E = ExactSys(tpm, N)
                ph = json.loads(r['phis'])
                for S in candidates(N, mode):
                    if len(S) > 3:
                        continue
                    ev = E.sysPhi(list(S), u, u)
                    r['exact_checked'] += 1
                    fv = ph['-'.join(map(str, S))]
                    if (ev.sign() > 0) != (fv > 0):
                        r['exact_sign_mismatch'] += 1
                    r['exact_max_abs_diff'] = repr(max(float(r['exact_max_abs_diff']),
                                                       abs(ev.approx() - fv)))
            r['wall'] = round(time.perf_counter() - t0, 3)
            r.pop('phis')
            out.append(r)
            print(json.dumps({k: r[k] for k in ('N', 'mode', 'idx', 'wall', 't_float', 't_univ',
                                                 'case', 'univ_pos', 'pairs_pos', 'exact_checked',
                                                 'exact_sign_mismatch', 'exact_max_abs_diff')}),
                  flush=True)
    agg = {}
    for N, mode, _ in plan:
        rs = [r for r in out if r['N'] == N]
        agg['N%d' % N] = {
            'mode': mode, 'rows': len(rs),
            'exact_checked': sum(r['exact_checked'] for r in rs),
            'exact_sign_mismatch': sum(r['exact_sign_mismatch'] for r in rs),
            'exact_max_abs_diff': max(float(r['exact_max_abs_diff']) for r in rs),
            'mean_t_float': sum(r['t_float'] for r in rs) / len(rs),
            'mean_wall': sum(r['wall'] for r in rs) / len(rs),
        }
    with open(os.path.join(HERE, 'calib.json'), 'w', encoding='utf-8') as f:
        json.dump({'aggregate': agg, 'rows': out}, f, indent=1)
    print(json.dumps(agg, indent=1))


def run(N, n_rows, mode, workers):
    jobs = [(N, SEED_BASE + 1000000 * N + i, i, mode) for i in range(n_rows)]
    t0 = time.perf_counter()
    if workers > 1:
        from multiprocessing import Pool
        with Pool(workers) as pool:
            rows = pool.map(work, jobs, chunksize=4)
    else:
        rows = [work(j) for j in jobs]
    wall = time.perf_counter() - t0
    path = os.path.join(HERE, 'trend_n%d.csv' % N)
    with open(path, 'w', newline='', encoding='utf-8') as f:
        w = csv.DictWriter(f, fieldnames=COLS)
        w.writeheader()
        for r in rows:
            w.writerow(r)
    summ = summarise(rows, N, mode, wall, workers)
    with open(os.path.join(HERE, 'summary_n%d.json' % N), 'w', encoding='utf-8') as f:
        json.dump(summ, f, indent=1)
    print(json.dumps({k: summ[k] for k in ('N', 'n_rows', 'wall_seconds', 'cases',
                                            'univ_pos', 'any_pair_pos', 'checks')}, indent=1))
    print('CSV:', path)


def pct(k, n):
    lo, hi = wilson(k, n)
    return {'count': k, 'pct': 100.0 * k / n if n else None,
            'wilson95_pct': [100.0 * lo, 100.0 * hi]}


def summarise(rows, N, mode, wall, workers):
    n = len(rows)
    strip = 'partial-' if mode != 'all' else ''
    cases = ['A0', 'A', 'B1', 'B2', 'C']
    cs = {c: pct(sum(1 for r in rows if r['case'] == strip + c), n) for c in cases}
    cs['B'] = pct(cs['B1']['count'] + cs['B2']['count'], n)
    cs['B-multi'] = pct(sum(int(r['b_multi']) for r in rows), n)
    cs['B-notmax'] = pct(sum(int(r['b_notmax']) for r in rows), n)
    sizes = {}
    for r in rows:
        for k in json.loads(r['complex_sizes']):
            sizes[str(k)] = sizes.get(str(k), 0) + 1
    ncx = {}
    for r in rows:
        ncx[str(r['n_complexes'])] = ncx.get(str(r['n_complexes']), 0) + 1
    asz = {}
    for r in rows:
        asz[str(r['argmax_size'])] = asz.get(str(r['argmax_size']), 0) + 1
    side = {}
    for r in rows:
        if int(r['univ_pos']) == 0:
            k = r['univ_clamp_side'] or 'none'
            side[k] = side.get(k, 0) + 1
    tp = sum(int(r['pairs_pos']) for r in rows)
    npairs = sum(int(r['n_pairs']) for r in rows)
    tt = sum(int(r['trips_pos']) for r in rows)
    ntr = sum(int(r['n_trips']) for r in rows)
    return {
        'N': N, 'mode': mode,
        'candidates': 'all |S| >= 2' if mode == 'all' else 'pairs + triples + univ',
        'measure': 'uniform doubles in [0,1) via random.Random; u = s = one random state per TPM',
        'seed_base': SEED_BASE + 1000000 * N, 'n_rows': n, 'workers': workers,
        'wall_seconds': wall,
        'seconds_per_row_cpu': {'mean': sum(float(r['t_row']) for r in rows) / n,
                                'max': max(float(r['t_row']) for r in rows)},
        'cases': cs,
        'univ_pos': pct(sum(int(r['univ_pos']) for r in rows), n),
        'univ_zero_clamp_side': side,
        'any_pair_pos': pct(sum(int(r['any_pair_pos']) for r in rows), n),
        'pair_pos_rate': pct(tp, npairs),
        'triple_pos_rate': pct(tt, ntr) if ntr else None,
        'mean_n_pos_cands': sum(int(r['n_pos_cands']) for r in rows) / n,
        'n_complexes_distribution': ncx,
        'complex_size_histogram': sizes,
        'argmax_size_distribution': asz,
        'n_argmax_distribution': {str(k): sum(1 for r in rows if int(r['n_argmax']) == k)
                                  for k in sorted({int(r['n_argmax']) for r in rows})},
        'checks': {
            'rows_borderline_redecided_zero': sum(1 for r in rows if int(r['n_redecide_zero']) > 0),
            'rows_borderline_redecided_cmp': sum(1 for r in rows if int(r['n_redecide_cmp']) > 0),
            'rows_unresolved': sum(1 for r in rows if int(r['n_unresolved']) > 0),
            'min_margin_over_rows': min(float(r['min_margin']) for r in rows),
            'min_gap_over_rows': min(float(r['min_gap']) for r in rows),
            'tol': TOL,
        },
    }


FINDINGS = """
## Findings (2026-09-26 run; N = 3, 4 all-state exact first pass agrees: 27.2% univ > 0 at N = 3)

1. **P(phi_s(univ) > 0) looks flat at N <= 7 but the limit is 0.** 27.7 (N=3), 24.9, 24.2, 25.6,
   28.0 (N=7, CI 22-35). CORRECTION (see results/theory/univ-zero.md): this is a crossover plateau.
   The single-unit CAUSE clamp rate rises with N (its complement decays like e^(-0.073 N), proved
   there and measured to N = 17) while the single-unit EFFECT clamp rate falls to 0; at N <= 7 the
   two cancel. NOTES sec. 2 was qualitatively right about the mechanism; its rate 0.947^N and the
   independence assumption were not needed.
2. **The clamp side does shift towards the cause side**, as sec. 2 predicted: among rows with
   phi_s(univ) = 0, cause-only rises 36 -> 51% and effect-only falls 29 -> 23% (N = 3 -> 7), but
   the two effects trade off instead of accumulating, leaving the zero rate stationary.
3. **A -> 0, some complex -> 1.** A = 18.1, 2.5, 0.1, 0.0, 0.0%. B = 82 -> 100%. C = 0 everywhere:
   no exact tie, no borderline decision (smallest clamp margin 1e-6 in log2 units, smallest
   relative selection gap 1e-5, both far above TOL = 1e-9; no exact re-decision was triggered).
   B-notmax = 0 always: without ties a positive argmax over all candidates is automatically a
   complex, so B-notmax is only reachable through C-type ties.
4. **B1 (univ is the complex) -> 0**: 10.1, 5.1, 2.5, 0.8, 2.0 (N=7 family-relative). Given
   phi_s(univ) > 0, univ wins 36, 20, 10, 3% (N = 3..6).
5. **B-multi grows fast**: 0, 7.9, 17.1, 24.0% (N = 3..6, all candidates), 46% at N = 7 relative
   to pairs + triples + univ. Mean number of complexes 0.82 -> 1.25 (N = 3 -> 6), 1.5 at N = 7.
6. **Complexes are small but the size distribution spreads with N.** Share of pairs among
   complexes: 88, 75, 66, 61% (N = 3..6); |S| >= 4 reaches 16% at N = 6 (35 five-unit and 4
   six-unit complexes in 500 rows). Sec. 3's "concentrates on |S| = 2 (maybe 3)" holds only
   loosely; the argmax candidate is a pair in 72, 72, 61, 54% of rows.
7. **Small candidates behave like small systems** (sec. 3 confirmed): per-pair positive rate
   41-42% and per-triple rate 26-28%, independent of N; P(some pair > 0) = 79, 95, 99, 100%.

Engine validation (`calib.json`): 378 candidate values at N = 3..6 (all candidates at N <= 4,
pairs + triples at N = 5, 6) against `engine/exact.py`: 0 sign mismatches, max |float - exact|
3e-16. Per-row float cost: 2 ms (N=3), 15 ms (4), 0.12 s (5), 1.0 s (6 all), 2.9 s (7 ptu).
Files: `trend_nN.csv` (one row per (TPM, state), all phi values in the `phis` column),
`summary_nN.json`, `summary_n6_ptu.json`/`trend_n6_ptu.csv` (earlier 300-row pairs+triples+univ
run at N = 6, same seeds), `calib.json`.
"""


def report():
    """trend.md from the summary files present."""
    lines = ['# T1 trend census (uniform measure, u = s, one random state per TPM)', '',
             'Engine: float transcription of `engine/exact.py` with exact re-decision of any',
             'borderline zero/nonzero or comparison (see `trend_census.py`, `calib.json`).',
             'Cases per CLOUD-TASKS.md. At N = 6 only pairs + triples + univ are computed, so',
             'its case split is relative to that family (a 4- or 5-set could beat a listed complex).',
             '']
    hdr = ['N', 'rows', 'cands', 'P(phi_univ>0)', 'A0', 'A', 'B1', 'B2', 'B-multi', 'B-notmax',
           'C', 'P(some pair>0)', 'pair>0 rate', 'complex sizes', 'cause/effect/both clamp of univ']
    lines.append('| ' + ' | '.join(hdr) + ' |')
    lines.append('|' + '---|' * len(hdr))
    for N in (3, 4, 5, 6, 7, 8):
        p = os.path.join(HERE, 'summary_n%d.json' % N)
        if not os.path.exists(p):
            continue
        s = json.load(open(p))

        def f(d):
            return '%.1f [%.1f, %.1f]' % (d['pct'], d['wilson95_pct'][0], d['wilson95_pct'][1])
        cs = s['cases']
        side = s['univ_zero_clamp_side']
        tot = sum(side.values()) or 1
        sd = '/'.join('%.0f' % (100 * side.get(k, 0) / tot) for k in ('cause', 'effect', 'both'))
        lines.append('| %d | %d | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |' % (
            N, s['n_rows'], s['candidates'], f(s['univ_pos']), f(cs['A0']), f(cs['A']), f(cs['B1']),
            f(cs['B2']), f(cs['B-multi']), f(cs['B-notmax']), f(cs['C']), f(s['any_pair_pos']),
            f(s['pair_pos_rate']), json.dumps(s['complex_size_histogram']), sd))
    lines += ['', '## Derived quantities', '',
              '| N | mean #complexes | complex size share % (2/3/4/5+) | P(univ is complex given phi_univ>0) | cause-side share of univ clamps | 0.947^N (NOTES sec. 2) | mean #positive cands | argmax is a pair % |',
              '|---|---|---|---|---|---|---|---|']
    for N in (3, 4, 5, 6, 7, 8):
        p = os.path.join(HERE, 'summary_n%d.json' % N)
        if not os.path.exists(p):
            continue
        s = json.load(open(p))
        n = s['n_rows']
        ncx = sum(int(k) * v for k, v in s['n_complexes_distribution'].items()) / n
        hist = s['complex_size_histogram']
        tot = sum(hist.values()) or 1
        share = '/'.join('%.0f' % (100 * sum(v for k, v in hist.items() if int(k) == sz) / tot)
                         for sz in (2, 3, 4)) + '/%.0f' % (
            100 * sum(v for k, v in hist.items() if int(k) >= 5) / tot)
        up = s['univ_pos']['count']
        b1 = s['cases']['B1']['count']
        side = s['univ_zero_clamp_side']
        z = sum(side.values()) or 1
        cause_any = (side.get('cause', 0) + side.get('both', 0)) / z
        asz = s['argmax_size_distribution']
        pair_arg = 100 * asz.get('2', 0) / n
        lines.append('| %d | %.2f | %s | %.0f%% (%d/%d) | %.0f%% (cause only %.0f%%) | %.2f | %.1f | %.0f |' % (
            N, ncx, share, 100 * b1 / up if up else 0, b1, up, 100 * cause_any,
            100 * side.get('cause', 0) / z, 0.947 ** N, s['mean_n_pos_cands'], pair_arg))
    lines += ['', 'Percentages with Wilson 95% intervals. "pair>0 rate" is per pair, pooled over',
              'rows. "complex sizes" counts complexes by |S| over all rows (a row can have several).',
              'The last column splits rows with phi_s(univ) = 0 by which side a partition clamps',
              'at the selected (tc, te): cause only / effect only / both.', '']
    lines += FINDINGS.split('\n')
    with open(os.path.join(HERE, 'trend.md'), 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(lines))
    print('\n'.join(lines))


if __name__ == '__main__':
    if sys.argv[1] == 'calib':
        calib()
    elif sys.argv[1] == 'report':
        report()
    else:
        run(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], int(sys.argv[5]))
