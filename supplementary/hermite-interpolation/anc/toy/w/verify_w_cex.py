#!/usr/bin/env python3
"""Proposition (certified counterexamples to W), items (a)-(f): Arb ball-arithmetic certificate.

Usage (from anc/):  python3 toy/w/verify_w_cex.py toy/w/params/w_cex.json [ITEM,ITEM,...]

Notation (paper, toy model).  tau_k(y) = (-1)^k (theta - y)^{2k} 1, theta = y d/dy.  For nodes y_1 < ... < y_J the
toy system P(0) = 1, Q_P(y_j) = Q_P'(y_j) = 0 is M p = b with M the 2J x 2J matrix of rows (tau_k(y_j))_k,
(tau_k'(y_j))_k (k = 1..2J) and b = (-1, 0, -1, 0, ...).  The p_1-rule functional
L = sum_j lambda_j delta_{y_j} + mu_j delta'_{y_j} is defined by L(tau_k) = [k = 1] (k = 1..2J), i.e. M^T w = e_1 with
w = (lambda_1, mu_1, lambda_2, mu_2, ...); then p_1 = -sum_j lambda_j.  Q''(y_j) = sum_k p_k tau_k''(y_j).
S_y = -p_2J L(tau_{2J+1}).  Property (W) at y: mu_j > 0 and Q''(y_j) > 0 for every j.  Nodes y_j = 2 pi n_j with
exact rational n_j (real pi).

Rigour.  python-flint arb/arb_mat at the working precision of each item; arb_mat.solve raises ZeroDivisionError
unless it proves that the matrix is invertible, so every successful solve certifies (N).  A sign is reported only
if the ball excludes 0 ('?' otherwise, which makes the item fail).  Enclosures are printed as Arb balls.
"""
import hashlib
import json
import os
import sys
import time
from fractions import Fraction

from flint import arb, arb_mat, arb_poly, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
ANC = os.path.dirname(os.path.dirname(HERE))


def rel(path):
    return os.path.relpath(os.path.abspath(path), ANC)


def sha256_file(path):
    with open(path, 'rb') as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def tau(k):
    """integer coefficient list (low -> high) of tau_k = (-1)^k (theta - y)^{2k} 1."""
    p = [1]
    for _ in range(2 * k):
        q = [0] * (len(p) + 1)          # (theta - y) p : coefficient m -> m p_m - p_{m-1}
        for m, c in enumerate(p):
            q[m] += m * c
            q[m + 1] -= c
        p = q
    return [-c for c in p] if k % 2 else p


def sgn(x):
    return '+' if x > 0 else ('-' if x < 0 else '?')


def solve(ns):
    """ns: exact rationals n_j; returns dict with p, lam, mu, Q2 and S (all Arb balls) for y_j = 2 pi n_j."""
    J = len(ns)
    tp = 2 * arb.pi()
    ys = [tp * arb(n.numerator) / n.denominator for n in ns]
    P = [arb_poly([arb(c) for c in tau(k)]) for k in range(2 * J + 2)]
    D1 = [p.derivative() for p in P]
    D2 = [p.derivative() for p in D1]
    M = arb_mat(2 * J, 2 * J)
    b = arb_mat(2 * J, 1)
    for i, y in enumerate(ys):
        for k in range(1, 2 * J + 1):
            M[2 * i, k - 1] = P[k](y)
            M[2 * i + 1, k - 1] = D1[k](y)
        b[2 * i, 0] = -P[0](y)
        b[2 * i + 1, 0] = -D1[0](y)
    x = M.solve(b)                                   # (N): raises unless non-singularity is proved
    e1 = arb_mat(2 * J, 1)
    e1[0, 0] = arb(1)
    w = M.transpose().solve(e1)
    p = [arb(1)] + [x[k, 0] for k in range(2 * J)]
    lam = [w[2 * j, 0] for j in range(J)]
    mu = [w[2 * j + 1, 0] for j in range(J)]
    Q2 = [sum((p[k] * D2[k](y) for k in range(2 * J + 1)), arb(0)) for y in ys]
    ell = sum((lam[j] * P[2 * J + 1](y) + mu[j] * D1[2 * J + 1](y) for j, y in enumerate(ys)), arb(0))
    return dict(p=p, lam=lam, mu=mu, Q2=Q2, S=-p[2 * J] * ell)


def in_class(ns, strict=False):
    if strict:
        return ns[0] > 1 and all(b - a > 1 for a, b in zip(ns, ns[1:]))
    return ns[0] >= 1 and all(b - a >= 1 for a, b in zip(ns, ns[1:]))


def rng(spec):
    a, b = (int(t) for t in spec.split('..'))
    return [Fraction(k) for k in range(a, b + 1)]


def main():
    pfile = sys.argv[1]
    par = json.load(open(pfile))
    want = sys.argv[2].split(',') if len(sys.argv) > 2 else [it['id'] for it in par['items']]
    print('Certified counterexamples to W (Arb ball arithmetic)')
    print('parameter file %s  sha256 %s' % (rel(pfile), sha256_file(pfile)), flush=True)
    allok = True
    for it in par['items']:
        if it['id'] not in want:
            continue
        t0 = time.time()
        ctx.prec = int(it['prec'])
        print('(%s) %s   [working precision %d bits]' % (it['id'], it['claim'], ctx.prec))
        ok = True
        if it['id'] in ('a', 'b', 'f'):
            ns = rng(it['n'])
            r = solve(ns)
            print('    n = %s: (N) certified; in the class: %s; mu signs %s; Q\'\' signs %s'
                  % (it['n'], in_class(ns), ''.join(sgn(m) for m in r['mu']), ''.join(sgn(q) for q in r['Q2'])))
            ok = ok and in_class(ns)
            if it['id'] == 'a':
                print('    mu_7 = %s' % r['mu'][6].str(6, radius=True))
                ok = ok and all(q > 0 for q in r['Q2']) and r['mu'][6] < 0
            if it['id'] == 'b':
                r9 = solve(ns[:9])
                d = r['p'][1] - r9['p'][1]
                print('    mu_9 = %s, mu_10 = %s' % (r['mu'][8].str(6, radius=True), r['mu'][9].str(6, radius=True)))
                print('    p_1(1..10) - p_1(1..9) = %s  (p_1(1..10) = %s)' % (d.str(6, radius=True), r['p'][1].str(15, radius=True)))
                ok = ok and r['mu'][8] < 0 and r['mu'][9] < 0 and d < 0
            if it['id'] == 'f':
                ok = ok and all(m > 0 for m in r['mu']) and all(q > 0 for q in r['Q2'])
        elif it['id'] == 'c':
            ns = rng(it['n'])
            r0 = solve(ns)
            print('    n = %s: (N) certified; S = %s' % (it['n'], r0['S'].str(6, radius=True)))
            ok = ok and r0['S'] < 0 and in_class(ns)
            for Yn in it['Y']:
                ns2 = ns + [Fraction(Yn)]
                r = solve(ns2)
                d = r['p'][1] - r0['p'][1]
                print('    n = %s + {%d}: (N) certified; in the class: %s; mu signs %s, Q\'\' signs %s; mu_Y = %s; '
                      'Delta = p_1(new) - p_1(old) = %s' % (it['n'], Yn, in_class(ns2), ''.join(sgn(m) for m in r['mu']),
                                                           ''.join(sgn(q) for q in r['Q2']), r['mu'][-1].str(5, radius=True),
                                                           d.str(5, radius=True)))
                ok = ok and in_class(ns2) and r['mu'][-1] < 0 and d < 0
        elif it['id'] == 'd':
            for e in it['eps'] + it['eps_weak']:
                eps = Fraction(e)
                ns = [(1 + eps) * j for j in range(1, 11)]
                r = solve(ns)
                inside = in_class(ns, strict=True)
                line = '    eps = %s: n_j = (1 + eps) j, j <= 10, strictly inside the class: %s; mu signs %s, Q\'\' signs %s; ' \
                       'mu_9 = %s, mu_10 = %s' % (e, inside, ''.join(sgn(m) for m in r['mu']), ''.join(sgn(q) for q in r['Q2']),
                                                   r['mu'][8].str(5, radius=True), r['mu'][9].str(5, radius=True))
                ok = ok and inside and r['mu'][9] < 0
                if e in it['eps']:
                    r5 = solve(ns[:5])
                    line += '; S(n_1..n_5) = %s' % r5['S'].str(5, radius=True)
                    ok = ok and r['mu'][8] < 0 and r5['S'] < 0
                print(line)
        elif it['id'] == 'e':
            st = Fraction(it['start'])
            ns = [st + j for j in range(int(it['count']))]
            r = solve(ns)
            print('    n_j = %s + j, j = 0..%d: (N) certified; in the class: %s; mu signs %s; Q\'\' signs %s'
                  % (it['start'], int(it['count']) - 1, in_class(ns), ''.join(sgn(m) for m in r['mu']),
                     ''.join(sgn(q) for q in r['Q2'])))
            for j in (47, 48, 49):
                print('    mu_%d = %s' % (j + 1, r['mu'][j].str(5, radius=True)))
            ok = ok and in_class(ns) and all(r['mu'][j] < 0 for j in (47, 48, 49))
        allok = allok and ok
        print('    item (%s): %s  [%.1f s]' % (it['id'], 'CERTIFIED' if ok else 'NOT CERTIFIED', time.time() - t0), flush=True)
    print('ALL CERTIFIED: items %s' % ','.join(want) if allok else 'NOT ALL CERTIFIED')
    sys.exit(0 if allok else 1)


if __name__ == '__main__':
    main()
