#!/usr/bin/env python3
"""Theorems W2 and W3, second route (insertion calculus): mu_Y and Q''(Y) of an inserted node, exact certificate.

Usage (from anc/):  python3 toy/w/verify_w_insertion.py toy/w/params/w_small.json J        (J = 2 or 3)

Every node is treated as the insertion Y of a node into the other J - 1 nodes x_1..x_{J-1} (insertion below or between
existing nodes is allowed).  With tau_k(y) = (-1)^k (theta - y)^{2k} 1, m = 2(J-1), base columns tau_1..tau_m, and
determinants over Q[x_1..x_{J-1}, Y] (rows: value and derivative rows at each x_i, and a value row at Y):
    detM   = det(base rows; columns 1..m)                      (the base system)
    B_K    = det(base rows + Y row; columns 1..m, K)           (K = 0, m+1, m+2;  B_K = detM Q_{V_K}(Y))
    L_K    = det(base rows; columns K, 2..m)                   (K = m+1, m+2;     L_K = detM l_K)
    omega  = prod_i (Y - x_i)^2
    A   = (L_{m+1} B_{m+2} - L_{m+2} B_{m+1}) / omega,         Wd  = Wr(B_{m+1}, B_{m+2}) / omega^2,
    W3d = Wr(B_0, B_{m+1}, B_{m+2}) / omega^3                  (exact divisions)
and, for the configuration x + {Y} with (N):   mu_Y = A / (Wd omega),   Q''(Y) = omega W3d / (detM Wd).
Both formulas are checked exactly against a direct rational solve at the check point of the parameter file.
Regions: y_1 = g + v_1, y_k = y_{k-1} + h + v_k (v >= 0).  For each insertion position p the four polynomials
A, Wd, W3d, detM, composed with the region parametrisation, must be one-signed coefficientwise, strictly (nonzero
constant term, or for h = 0 a nonzero monomial free of v_1, positive when all gaps are positive), with
sign(A) sign(Wd) = + and sign(W3d) sign(detM) sign(Wd) = +.  Then (N) holds for the full configuration
(detM != 0, Wd != 0), mu_Y > 0 and Q''(Y) > 0 at every node.  Exact arithmetic: python-flint fmpq_mpoly, fmpq_mat.
"""
import hashlib
import json
import os
import sys
import time
from fractions import Fraction
from functools import lru_cache

from flint import fmpq, fmpq_mat, fmpq_mpoly_ctx

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


def main():
    t00 = time.time()
    pfile, J = sys.argv[1], int(sys.argv[2])
    par = json.load(open(pfile))
    case = par['cases'][str(J)]
    print('Theorem W%d: exact certificate (insertion route)' % J)
    print('parameter file %s  sha256 %s' % (rel(pfile), sha256_file(pfile)), flush=True)
    names = tuple('x%d' % i for i in range(1, J)) + ('Y',)
    ctx = fmpq_mpoly_ctx.get(names, 'lex')
    gens = ctx.gens()
    X, Y = gens[:-1], gens[-1]
    zero = 0 * Y
    one = zero + 1

    def tpoly(k, v, der=0):
        c = tau(k)
        for _ in range(der):
            c = [i * c[i] for i in range(1, len(c))]
        acc = zero
        for a in reversed(c):
            acc = acc * v + a
        return acc

    def det(Mx):
        n = len(Mx)

        @lru_cache(None)
        def rec(r, cols):
            if r == n:
                return one
            tot = zero
            for idx, j in enumerate(cols):
                e = Mx[r][j]
                if e.is_zero():
                    continue
                term = e * rec(r + 1, cols[:idx] + cols[idx + 1:])
                tot = tot + term if idx % 2 == 0 else tot - term
            return tot
        return rec(0, tuple(range(n)))

    m = 2 * (J - 1)

    def rows(cols, withY):
        R = []
        for x in X:
            R.append([tpoly(k, x) for k in cols])
            R.append([tpoly(k, x, 1) for k in cols])
        if withY:
            R.append([tpoly(k, Y) for k in cols])
        return R
    base = list(range(1, m + 1))
    detM = det(rows(base, False)) if m else one
    K1, K2 = m + 1, m + 2
    B = {K: det(rows(base + [K], True)) for K in (0, K1, K2)}
    L = {K: det(rows([K] + base[1:], False)) for K in (K1, K2)}
    omega = one
    for x in X:
        omega = omega * (Y - x) ** 2
    dY = lambda p: p.derivative('Y')
    A = (L[K1] * B[K2] - L[K2] * B[K1]) / omega
    Wd = (B[K1] * dY(B[K2]) - dY(B[K1]) * B[K2]) / omega ** 2
    W3d = (B[0] * (dY(B[K1]) * dY(dY(B[K2])) - dY(dY(B[K1])) * dY(B[K2]))
           - dY(B[0]) * (B[K1] * dY(dY(B[K2])) - dY(dY(B[K1])) * B[K2])
           + dY(dY(B[0])) * (B[K1] * dY(B[K2]) - dY(B[K1]) * B[K2])) / omega ** 3
    print('[1] built: terms A %d, Wd %d, W3d %d, detM %d (%.1f s)' % (len(A), len(Wd), len(W3d), len(detM), time.time() - t00))
    # exact check of the two formulas against a direct solve at the check point
    pt = [fmpq(*[int(t) for t in s.split('/')]) for s in case['check_point']]

    def peval(c, x):
        s = fmpq(0)
        for a in reversed(c):
            s = s * x + a
        return s

    def dcoef(c):
        return [i * c[i] for i in range(1, len(c))]
    Mq = fmpq_mat([[peval(tau(k) if d == 0 else dcoef(tau(k)), y) for k in range(1, 2 * J + 1)] for y in pt for d in (0, 1)])
    bq = fmpq_mat([[-1 if d == 0 else 0] for y in pt for d in (0, 1)])
    pv = Mq.solve(bq)
    w = Mq.transpose().solve(fmpq_mat([[1 if i == 0 else 0] for i in range(2 * J)]))
    pcoef = [fmpq(1)] + [pv[i, 0] for i in range(2 * J)]
    conv = True
    for pos in range(J):
        vals = pt[:pos] + pt[pos + 1:] + [pt[pos]]
        ev = lambda P: P(*vals)
        mu_f = ev(A) / (ev(Wd) * ev(omega))
        q2_f = ev(omega) * ev(W3d) / (ev(detM) * ev(Wd))
        q2_d = sum((pcoef[k] * peval(dcoef(dcoef(tau(k))), pt[pos]) for k in range(2 * J + 1)), fmpq(0))
        conv = conv and mu_f == w[2 * pos + 1, 0] and q2_f == q2_d
    print('    mu_Y = A/(Wd omega) and Q\'\'(Y) = omega W3d/(detM Wd) equal the direct exact solve at y = (%s), every node: %s'
          % (', '.join(case['check_point']), conv), flush=True)
    ok = conv
    V = gens
    for lab, rg in case['regions'].items():
        g, h = Fraction(rg['g']), Fraction(rg['h'])
        z = [zero + fmpq(g.numerator, g.denominator) + V[0]]
        for i in range(1, J):
            z.append(z[-1] + fmpq(h.numerator, h.denominator) + V[i])
        good = True
        for pos in range(J):
            sub = z[:pos] + z[pos + 1:] + [z[pos]]
            sg, parts = {}, []
            for nm, P in (('A', A), ('Wd', Wd), ('W3d', W3d), ('detM', detM)):
                Q = P.compose(*sub)
                cf = Q.coeffs()
                s = 1 if all(c > 0 for c in cf) else (-1 if all(c < 0 for c in cf) else 0)
                const = dict(zip(Q.monoms(), cf)).get((0,) * J, 0)
                strict = const != 0 if h > 0 else (const != 0 or any(mono[0] == 0 for mono in Q.monoms()))
                sg[nm] = s if strict else 0
                parts.append('%s %s%d%s' % (nm, {1: '+', -1: '-', 0: '?'}[s], len(cf), '' if strict else ' (not strict)'))
            mu_s = sg['A'] * sg['Wd']
            q2_s = sg['W3d'] * sg['detM'] * sg['Wd']
            nodeok = all(sg.values()) and mu_s == 1 and q2_s == 1
            good = good and nodeok
            print('[2] region (%s) y_1 = %s + v_1, gaps = %s + v_k; inserted node = node %d: %s  =>  mu %s, Q\'\' %s'
                  % (lab, g, h, pos + 1, ' | '.join(parts), '+' if mu_s == 1 else '?', '+' if q2_s == 1 else '?'), flush=True)
        print('    region (%s): %s' % (lab, 'CERTIFIED: (N), mu_j > 0 and Q\'\'(y_j) > 0 at every node' if good else 'NOT CERTIFIED'))
        ok = ok and good
    print('total time %.1f s' % (time.time() - t00))
    print('ALL CERTIFIED: Theorem W%d on regions %s (insertion route)' % (J, ','.join(case['regions'])) if ok else 'NOT ALL CERTIFIED')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
