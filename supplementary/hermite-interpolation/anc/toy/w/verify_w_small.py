#!/usr/bin/env python3
"""Theorems W2 and W3: property (W) for J = 2 and J = 3 on two regions each (exact certificate, Cramer route).

Usage (from anc/):  python3 toy/w/verify_w_small.py toy/w/params/w_small.json J        (J = 2 or 3)

Setting (paper, toy model).  M is the 2J x 2J matrix of the toy system (rows (tau_k(y_j))_k and (tau_k'(y_j))_k for
j = 1..J, columns k = 1..2J), tau_k(y) = (-1)^k (theta - y)^{2k} 1.  The p_1-rule weights (lambda_j, mu_j) solve
M^T w = e_1, so by Cramer's rule
    mu_j = - N_j / det M,     N_j := det(M without the derivative row of y_j and without the column of tau_1).
Regions: y_1 = g + w_1, y_k = y_{k-1} + h + w_k (k >= 2), w >= 0 and y_1 < ... < y_J; the parameter file gives
(g, h) = (157/25, 157/25) for region (a) and (8, 0) (J = 2), (12, 0) (J = 3) for region (b).

Checks (exact integer/rational arithmetic, python-flint fmpz_mpoly / fmpq_mat):
 1. N_j and det M in Z[y_1..y_J] by cofactor expansion; det M is divisible by (y_1...y_J)^2 V^4, V = prod_{i<j}(y_i-y_j),
    with quotient Dc; the Cramer formula for mu_j is checked exactly against a direct rational solve at one point.
 2. On each region, after the substitution (homogenised; positive denominators cleared), Dc and every N_j are
    one-signed coefficientwise.  Strictness: for h > 0 a nonzero constant term (sign on the closed orthant w >= 0);
    for h = 0 a nonzero monomial free of w_1, which is positive whenever the gaps w_2, ..., w_J are positive.
    Then det M != 0 ((N)) and sign mu_j = -sign N_j sign Dc, which must be +.
 3. Each region lies in PT_delta (delta = 1/20): sum_{j<=K} y_j - (21/20) K(4K-1) has nonnegative coefficients and
    constant term in w, K <= J.  Hence Theorem PT_J (toy/pt/verify_pt.py) gives R_J > 0 coefficientwise, and
    Q''(y_j) = 2 R_J(y_j) prod_{i != j} (y_j - y_i)^2 > 0.
"""
import hashlib
import json
import os
import sys
import time
from fractions import Fraction
from functools import lru_cache

from flint import fmpq, fmpq_mat, fmpz_mpoly_ctx, fmpz_poly

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


def det(rows, zero, one):
    n = len(rows)

    @lru_cache(None)
    def rec(r, cols):
        if r == n:
            return one
        tot = zero
        for idx, c in enumerate(cols):
            e = rows[r][c]
            if e.is_zero():
                continue
            term = e * rec(r + 1, cols[:idx] + cols[idx + 1:])
            tot = tot + term if idx % 2 == 0 else tot - term
        return tot
    return rec(0, tuple(range(n)))


def main():
    t00 = time.time()
    pfile, J = sys.argv[1], int(sys.argv[2])
    par = json.load(open(pfile))
    case = par['cases'][str(J)]
    print('Theorem W%d: exact certificate (Cramer route)' % J)
    print('parameter file %s  sha256 %s' % (rel(pfile), sha256_file(pfile)), flush=True)
    names = tuple('y%d' % (j + 1) for j in range(J))
    ctx = fmpz_mpoly_ctx.get(names, 'lex')
    Y = ctx.gens()
    one = ctx.from_dict({(0,) * J: 1})
    zero = 0 * one
    T = [fmpz_poly(tau(k)) for k in range(2 * J + 1)]

    def in_var(p, j):
        d = {}
        for i, c in enumerate(p.coeffs()):
            if c != 0:
                e = [0] * J
                e[j] = i
                d[tuple(e)] = int(c)
        return ctx.from_dict(d) if d else zero

    rows = []
    for j in range(J):
        rows.append([in_var(T[k], j) for k in range(1, 2 * J + 1)])
        rows.append([in_var(T[k].derivative(), j) for k in range(1, 2 * J + 1)])
    D = det(rows, zero, one)
    N = []
    for j in range(J):
        sub = [r[1:] for i, r in enumerate(rows) if i != 2 * j + 1]
        N.append(det(sub, zero, one))
    prod_y2 = one
    for j in range(J):
        prod_y2 *= Y[j] * Y[j]
    V = one
    for i in range(J):
        for j in range(i + 1, J):
            V *= Y[i] - Y[j]
    Dc, rr = divmod(D, prod_y2 * V ** 4)
    print('[1] det M: %d terms; divisible by (y_1...y_J)^2 V^4: %s (quotient Dc: %d terms); N_j terms %s, total degrees %s'
          % (len(D), rr.is_zero(), len(Dc), [len(n) for n in N], [n.total_degree() for n in N]))
    ok = rr.is_zero()
    # exact check of mu_j = -N_j / det M at a rational point
    pt = [fmpq(*[int(t) for t in s.split('/')]) for s in case['check_point']]
    Mq = fmpq_mat([[fmpq_poly_eval(T[k], pt[j], d) for k in range(1, 2 * J + 1)] for j in range(J) for d in (0, 1)])
    e1 = fmpq_mat([[1 if i == 0 else 0] for i in range(2 * J)])
    w = Mq.transpose().solve(e1)

    def ev(p):
        s = fmpq(0)
        for mono, cf in zip(p.monoms(), p.coeffs()):
            t = fmpq(int(cf))
            for k in range(J):
                t *= pt[k] ** mono[k]
            s += t
        return s
    Dv = ev(D)
    conv = all(w[2 * j + 1, 0] == -ev(N[j]) / Dv for j in range(J))
    print('    Cramer formula mu_j = -N_j/det M equals the direct exact solve at y = (%s): %s'
          % (', '.join(case['check_point']), conv), flush=True)
    ok = ok and conv
    cpt = Fraction(par['pt_constant'])
    wn = tuple('w%d' % (j + 1) for j in range(J))
    wctx = fmpz_mpoly_ctx.get(wn, 'lex')
    W = wctx.gens()
    wone = wctx.from_dict({(0,) * J: 1})
    hctx = fmpz_mpoly_ctx.get(names + ('z',), 'lex')

    def subst(p, nums, den):
        d = p.total_degree()
        H = hctx.from_dict({tuple(m) + (d - sum(m),): int(c) for m, c in zip(p.monoms(), p.coeffs())})
        return H.compose(*nums, den, ctx=wctx)

    def sign_report(q, h):
        cf = [int(c) for c in q.coeffs()]
        s = 1 if all(c > 0 for c in cf) else (-1 if all(c < 0 for c in cf) else 0)
        mons = q.monoms()
        const = dict(zip(mons, cf)).get((0,) * J, 0)
        free = [m for m in mons if m[0] == 0]
        strict = const != 0 if h > 0 else (const != 0 or len(free) > 0)   # h > 0: the corner w = 0 is admissible
        how = 'constant term' if const != 0 else ('%d monomials free of w1' % len(free) if free else 'NONE')
        return s, strict, '%s%d terms, %s, strict via %s' % ({1: '+', -1: '-', 0: 'MIXED '}[s], len(cf),
                                                                'one-signed' if s else 'NOT one-signed', how)
    for lab, rg in case['regions'].items():
        g, h = Fraction(rg['g']), Fraction(rg['h'])
        den = g.denominator * h.denominator
        # y_1 = g + w_1, y_k = y_{k-1} + h + w_k  (numerators over the common denominator den)
        nums, acc = [], 0 * wone
        for k in range(J):
            acc = acc + (int(g * den) if k == 0 else int(h * den)) * wone + den * W[k]
            nums.append(acc)
        dn = den * wone
        # region inside PT_delta
        inside = True
        for K in range(1, J + 1):
            const = sum(g + j * h for j in range(K)) - cpt * K * (4 * K - 1)
            inside = inside and const >= 0              # coefficients of w are positive integers
        print('[2] region (%s): y_1 = %s + w_1, gaps = %s + w_k; inside PT_delta (delta = 1/20): %s' % (lab, g, h, inside))
        sD, stD, rD = sign_report(subst(Dc, nums, dn), h)
        print('    Dc: %s' % rD)
        good = inside and sD != 0 and stD
        for j in range(J):
            sN, stN, rN = sign_report(subst(N[j], nums, dn), h)
            musign = -sN * sD
            print('    N_%d: %s  =>  sign mu_%d = %s' % (j + 1, rN, j + 1, {1: '+', -1: '-', 0: '?'}[musign]))
            good = good and sN != 0 and stN and musign == 1
        print('    region (%s): %s' % (lab, 'CERTIFIED: (N), mu_j > 0 for all j (Q\'\'(y_j) > 0 by Theorem PT%d)' % J
                                       if good else 'NOT CERTIFIED'), flush=True)
        ok = ok and good
    print('total time %.1f s' % (time.time() - t00))
    print('ALL CERTIFIED: Theorem W%d on regions %s' % (J, ','.join(case['regions'])) if ok else 'NOT ALL CERTIFIED')
    sys.exit(0 if ok else 1)


def fmpq_poly_eval(p, x, der):
    q = p.derivative() if der else p
    s = fmpq(0)
    for c in reversed(q.coeffs()):
        s = s * x + int(c)
    return s


if __name__ == '__main__':
    main()
