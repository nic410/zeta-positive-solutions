"""Certified ratio bounds R_1(X) >= sup_{x in [2, X] \\ PP} |Fhat_{J+1} - Fhat_J| / (|Delta p_1| Fhat_J)  for consecutive exact members.

Fhat_J = (Xi^2 P_J(t^2))^ for the exact Hermite member P_J; Delta p_1 = p_1^{(J+1)} - p_1^{(J)}.  Inputs: certified coefficient
enclosures of P_J and P_{J+1} (output of verify_exact_member.py).  D := Fhat_{J+1} - Fhat_J is the transform of
Xi^2 (P_{J+1} - P_J)(t^2), evaluated with the same exact Bessel-operator form (lib/bessel_form.py) from the ball difference
of the coefficients.  All prime powers <= X are nodes of both members, so D and Fhat_J both vanish to second order there
(exactly, by the Hermite conditions).

Certificate, for a list of targets (X_k, R_k) (increasing X_k, each X_k a prime power):
  * Nodes n <= max X_k.  Taylor coefficients d_k of D and c_k of Fhat_J at xi_n (with d_0 = d_1 = c_0 = c_1 = 0 exactly);
    for |u| <= h:  |D| <= u^2 (|d_2| + sum_{k>=3} |d_k| h^{k-2} + M_D h^{p-1}/(p+1)!),  Fhat_J >= u^2 c_2'  (as in verify_base.py),
    so the ratio is at most (that bound)/(|Delta p_1| c_2') on the punctured neighbourhood.
    Precondition check: d_0 = d_1 = c_0 = c_1 = 0 is used, not computed, so the inputs must be the certified enclosures
    of the exact members (outputs of verify_exact_member.py; their sha256 are printed).  As a consistency check, the
    computed balls must contain 0 and have radius <= 2^(-B/4) s h^2 (k = 0) resp. 2^(-B/4) s h (k = 1), with s = c_2 for
    Fhat_J and s = |Delta p_1| c_2 for D, at every node; otherwise NOT CERTIFIED.
  * Gaps.  Pieces with exact dyadic endpoints (overlapping the neighbourhoods), adaptive bisection: an upper bound for |D|
    (Taylor model: sum_k |d_k| r^k + remainder) over |Delta p_1| times a lower bound for Fhat_J (Taylor model, > 0).
  * A node neighbourhood or piece in [2, X_k] passes if its bound is <= R_k for the smallest X_k >= its right end.
Printed: for each X_k, the largest certified piece/node bound on [2, X_k] (rounded up) and the target R_k.

Usage (from anc/):  python exact/verify_r1.py BALL_J BALL_J+1 --target 31:1.021e9 [--target X:R ...] --prec B [--order 28]
"""
import argparse
import math
import multiprocessing as mp
import os
import sys
import time
from fractions import Fraction
from math import factorial

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from flint import arb, fmpq, fmpz, ctx  # noqa: E402
from lib.bessel_form import FhatOperators, Evaluator  # noqa: E402
from lib.common import relpath, sha256_file, prime_powers, first_prime_powers, round_up, require  # noqa: E402

DY = 200
S_DY = fmpz(2) ** DY
G = {}


def dyarb(k):
    return arb(fmpq(k, S_DY))


def dy(v, up):
    w = v * arb(2) ** DY
    return int((arb(w.upper()).ceil() if up else arb(w.lower()).floor()).unique_fmpz())


def target_for(xright):
    for X, R in G['targets']:
        if xright <= X:
            return R
    raise ValueError


def taylor(EV, xi, p, rel=False):
    der = EV.derivs_rel(xi, list(range(p + 1))) if rel else EV.derivs(xi, list(range(p + 1)))
    return [der[k] / factorial(k) for k in range(p + 1)]


def zero_balls(cs, scale, h):
    """Precondition check (see the docstring): c_0, c_1 contain 0, radius <= 2^(-B/4) |scale| h^2 resp. h."""
    tol = arb(2) ** (-(G['prec'] // 4)) * arb(abs(scale).lower())
    return bool(cs[0].contains(0) and cs[1].contains(0)
                and arb(cs[0].rad()) <= tol * h * h and arb(cs[1].rad()) <= tol * h)


def node_task(i):
    ctx.prec = G['prec']
    EVF, EVD, p, nodes, dp1 = G['EVF'], G['EVD'], G['p'], G['nodes'], G['dp1']
    PI = arb.pi()
    n = nodes[i]
    xin = arb(n).log() / (2 * PI)
    gaps = []
    if i + 1 < len(nodes):
        gaps.append((arb(nodes[i + 1]).log() - arb(n).log()) / (2 * PI))
    if i > 0:
        gaps.append((arb(n).log() - arb(nodes[i - 1]).log()) / (2 * PI))
    h = arb(min([0.004] + [float(g.mid()) / 3 for g in gaps]))
    cs = taylor(EVF, xin, p)
    ds = taylor(EVD, xin, p)
    if not (cs[2] > 0 and zero_balls(cs, cs[2], h) and zero_balls(ds, abs(dp1) * cs[2], h)):
        return dict(i=i, n=n, ok=False)
    left, right = n != nodes[0], n != nodes[-1]
    R = target_for(n)
    while True:
        lo = xin - h if left else xin
        hi = xin + h if right else xin
        MF = EVF.sup_abs(p + 1, lo, hi)
        MD = EVD.sup_abs(p + 1, lo, hi)
        c2p = cs[2] - sum((abs(cs[k]) * h ** (k - 2) for k in range(3, p + 1)), arb(0)) - MF * h ** (p - 1) / factorial(p + 1)
        dsup = abs(ds[2]) + sum((abs(ds[k]) * h ** (k - 2) for k in range(3, p + 1)), arb(0)) + MD * h ** (p - 1) / factorial(p + 1)
        if c2p > 0:
            ub = dsup / (abs(dp1) * c2p)
            if ub < R:
                lim = abs(ds[2]) / (abs(dp1) * cs[2])
                return dict(i=i, n=n, ok=True, lo=dy(xin - h, True), hi=dy(xin + h, False), h=float(h.mid()),
                            ub=round_up(ub, 6), lim=lim.str(5))
        h = h / 2
        if h < arb('1e-14'):
            return dict(i=i, n=n, ok=False)


def piece_bound(a, b):
    EVF, EVD, p, dp1 = G['EVF'], G['EVD'], G['p'], G['dp1']
    xi0 = (a + b) / 2
    r = (b - a) / 2
    cs = taylor(EVF, xi0, p, rel=True)
    ds = taylor(EVD, xi0, p, rel=True)
    MF = EVF.sup_abs(p + 1, a, b)
    MD = EVD.sup_abs(p + 1, a, b)
    lbF = cs[0] - sum((abs(cs[k]) * r ** k for k in range(1, p + 1)), arb(0)) - MF * r ** (p + 1) / factorial(p + 1)
    c2p = cs[2] - sum((abs(cs[k]) * r ** (k - 2) for k in range(3, p + 1)), arb(0)) - MF * r ** (p - 1) / factorial(p + 1)
    if c2p > 0:
        q1 = cs[0] - cs[1] ** 2 / (4 * c2p)
        if q1.lower() > lbF.lower():
            lbF = q1
    if not (lbF > 0):
        return None
    ubD = sum((abs(ds[k]) * r ** k for k in range(0, p + 1)), arb(0)) + MD * r ** (p + 1) / factorial(p + 1)
    return ubD / (abs(dp1) * lbF)


def gap_task(task):
    gi, a0, b0, nr = task
    ctx.prec = G['prec']
    R = target_for(nr)
    width = float(dyarb(b0 - a0).mid())
    k = max(1, int(width / 0.002) + 1)
    edges = [a0 + ((b0 - a0) * j) // k for j in range(k)] + [b0]
    stack = [(edges[j], edges[j + 1], 0) for j in range(k)][::-1]
    npieces, worst = 0, None
    while stack:
        a, b, dep = stack.pop()
        ub = piece_bound(dyarb(a), dyarb(b))
        npieces += 1
        if ub is not None and ub < R:
            u = arb(ub.upper())
            worst = u if worst is None or u > worst else worst
            continue
        if dep > 40 or b - a < 2:
            return dict(gi=gi, ok=False, pieces=npieces, fail='[%s, %s]' % (dyarb(a).str(12), dyarb(b).str(12)))
        m = (a + b) // 2
        stack += [(m, b, dep + 1), (a, m, dep + 1)]
    return dict(gi=gi, ok=True, pieces=npieces, worst=round_up(worst, 8))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('ballJ')
    ap.add_argument('ballJ1')
    ap.add_argument('--target', action='append', required=True)
    ap.add_argument('--prec', type=int, required=True)
    ap.add_argument('--order', type=int, default=28)
    ap.add_argument('--workers', type=int, default=1)
    a = ap.parse_args()
    t0 = time.time()
    ctx.prec = a.prec
    P = [arb(s) for s in open(a.ballJ).read().split('\n') if s.strip()]
    P1 = [arb(s) for s in open(a.ballJ1).read().split('\n') if s.strip()]
    J = (len(P) - 1) // 2
    require((len(P1) - 1) // 2 == J + 1, 'the second enclosure must be of degree 2J + 2')
    dP = [P1[k] - (P[k] if k < len(P) else arb(0)) for k in range(len(P1))]
    dp1 = P1[1] - P[1]
    targets = []
    for t in a.target:
        X, R = t.split(':')
        fr = Fraction(R)
        targets.append((int(X), arb(fmpq(fr.numerator, fr.denominator))))
    targets.sort(key=lambda u: u[0])
    Xmax = targets[-1][0]
    killed = [n for n, _ in first_prime_powers(J)]
    nodes = [n for n, _ in prime_powers(Xmax)]
    require(all(X in nodes for X, _ in targets) and all(n in killed for n in nodes),
            'every target X must be a prime power and every prime power <= max X a node of P_J')
    EVF = Evaluator(FhatOperators(P, a.order + 1, a.prec), a.prec, -int(a.prec * 0.30103) - 30)
    EVD = Evaluator(FhatOperators(dP, a.order + 1, a.prec), a.prec, -int(a.prec * 0.30103) - 30)
    ctx.prec = a.prec
    G.update(EVF=EVF, EVD=EVD, prec=a.prec, p=a.order, nodes=nodes, dp1=dp1, targets=targets)
    print('P_J  enclosure %s (sha256 %s), J = %d' % (relpath(a.ballJ), sha256_file(a.ballJ), J))
    print('P_J+1 enclosure %s (sha256 %s)' % (relpath(a.ballJ1), sha256_file(a.ballJ1)))
    print('Delta p_1 = p_1^(J+1) - p_1^(J) in %s;  region [xi_2, xi_%d] (%d nodes); %d bits, Taylor order %d'
          % (dp1.str(15), Xmax, len(nodes), a.prec, a.order), flush=True)
    pool = mp.get_context('fork').Pool(a.workers) if a.workers > 1 else None
    res = list(pool.imap(node_task, range(len(nodes))) if pool else map(node_task, range(len(nodes))))
    if not all(r['ok'] for r in res):
        print('  FAIL at nodes', [r['n'] for r in res if not r['ok']]); print('NOT CERTIFIED'); return 1
    tasks = [(k, res[k]['hi'], res[k + 1]['lo'], nodes[k + 1]) for k in range(len(nodes) - 1)]
    for t in tasks:
        require(t[1] < t[2], 'neighbourhoods overlap')
    gres = list(pool.imap_unordered(gap_task, tasks[::-1]) if pool else map(gap_task, tasks))
    if pool:
        pool.close()
    if not all(r['ok'] for r in gres):
        for r in gres:
            if not r['ok']:
                print('  FAIL in gap %d at %s' % (r['gi'], r['fail']))
        print('NOT CERTIFIED'); return 1
    gres.sort(key=lambda r: r['gi'])
    print('node items: ratio bound on the punctured neighbourhood (limit value |D\'\'|/(|Delta p_1| Fhat_J\'\') in brackets):')
    for r in res:
        print('  n = %3d: <= %s  [%s]' % (r['n'], r['ub'], r['lim']))
    print('all %d gaps certified with %d pieces' % (len(tasks), sum(r['pieces'] for r in gres)))
    ok = True
    for X, R in targets:
        vals = [r['ub'] for r in res if r['n'] <= X] + [g['worst'] for g in gres if nodes[g['gi'] + 1] <= X]
        mx = arb(max(vals, key=Fraction))                      # exact comparison of the decimal upper bounds
        good = all(arb(v) < R for v in vals)
        ok = ok and good
        print('  X = %3d: certified sup bound on [2, X] <= %s;  target R_1(X) = %s: %s' % (X, round_up(mx, 6), R.str(6), good))
    print('CERTIFIED: R_1 bounds (J = %d): %s   (%.0f s)' % (J, ok, time.time() - t0))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
