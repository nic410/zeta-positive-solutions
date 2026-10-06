#!/usr/bin/env python3
"""(AP+) at delta = 1/20 for every J = 1..90, with (N) and p_2J > 0: exact rational certificate.

Usage (from anc/):  python3 toy/ap/verify_ap.py toy/ap/params/ap_delta005.json [Jmin Jmax]
                    (default: the full J range of the parameter file; the range may be split over processes)

The toy Hermite problem at the progression nodes y*_K = c (8K - 5), K = 1..J, c = 1 + delta (paper, toy model):
  find P(u) = 1 + p_1 u + ... + p_2J u^{2J} such that Q_P(y*_K) = Q_P'(y*_K) = 0 for K = 1..J, where
  Q_P = sum_k p_k tau_k and tau_k(y) = (-1)^k (theta - y)^{2k} 1, theta = y d/dy (tau_0 = 1, tau_k(0) = 0 for k >= 1,
  deg tau_k = 2k, leading coefficient (-1)^k).  R_J := Q_P / prod_K (y - y*_K)^2, a polynomial of degree 2J.
(AP+)_J : every coefficient of R_J is > 0.

For each J the script checks, in exact rational arithmetic (python-flint fmpq, fmpq_poly, fmpq_mat):
  (N)    the 2J x 2J system in p_1..p_2J is non-singular: the exact solve succeeds (fmpq_mat.solve raises
         ZeroDivisionError on a singular matrix) and the exact residual M p - b is zero;
  the division Q_P / prod_K (y - y*_K)^2 has zero remainder and the quotient R_J has degree 2J;
  (AP+)_J every coefficient r_0, ..., r_2J of R_J is > 0;  and p_2J > 0;
  two exact identities, as consistency checks of the solution:
         r_1/r_0 = 1 - P(-1) + 2 sum_K 1/y*_K,    r_{2J-1}/r_{2J} = 2 sum_K y*_K - 2J(4J-1)  (= 2 delta J(4J-1)).
Printed decimals of exact rationals are rounded down.
"""
import hashlib
import json
import math
import os
import sys
import time
from fractions import Fraction

from flint import fmpq, fmpq_mat, fmpq_poly


class CertificationError(RuntimeError):
    """A precondition or a check of the certificate failed."""


def require(cond, msg='check failed'):
    """Explicit check, used instead of assert (which python -O would remove): raise CertificationError unless cond."""
    if not cond:
        raise CertificationError(msg)

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


def floor_str(q, sig=12):
    """decimal string of the rational q (fmpq) with sig significant digits, rounded down."""
    q = Fraction(int(q.p), int(q.q))
    if q == 0:
        return '0'
    a = abs(q)
    E = int((a.numerator.bit_length() - a.denominator.bit_length()) * 0.3010299956639812)   # no big-int str()
    while Fraction(10) ** E > a:
        E -= 1
    while Fraction(10) ** (E + 1) <= a:
        E += 1
    n = math.floor(q / Fraction(10) ** (E - sig + 1))
    s = str(abs(n))
    return '%s%s%se%+d' % ('-' if n < 0 else '', s[0], ('.' + s[1:]) if len(s) > 1 else '', E - sig + len(s))


def main():
    pfile = sys.argv[1]
    par = json.load(open(pfile))
    print('(AP+) certificate, exact rational arithmetic')
    print('parameter file %s  sha256 %s' % (rel(pfile), sha256_file(pfile)))
    num, den = (int(t) for t in par['c'].split('/'))
    c = fmpq(num, den)
    J0, J1 = par['J_range']
    Jmin, Jmax = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (J0, J1)
    require(J0 <= Jmin <= Jmax <= J1, 'J range outside the parameter file')
    print('c = 1 + delta = %s, nodes y*_K = c(8K - 5), J = %d..%d' % (c, Jmin, Jmax), flush=True)
    T = [fmpq_poly(tau(k)) for k in range(2 * Jmax + 1)]
    dT = [t.derivative() for t in T]
    allok = True
    for J in range(Jmin, Jmax + 1):
        t0 = time.time()
        nodes = [c * (8 * K - 5) for K in range(1, J + 1)]
        rows, rhs = [], []
        for y in nodes:
            rows.append([T[k](y) for k in range(1, 2 * J + 1)])
            rhs.append([-T[0](y)])
            rows.append([dT[k](y) for k in range(1, 2 * J + 1)])
            rhs.append([-dT[0](y)])
        M = fmpq_mat(rows)
        b = fmpq_mat(rhs)
        try:
            x = M.solve(b)
            N = (M * x == b)
        except ZeroDivisionError:
            N = False
        if not N:
            print('J=%2d  (N) FAIL: singular system' % J, flush=True)
            allok = False
            continue
        p = [fmpq(1)] + [x[i, 0] for i in range(2 * J)]
        Q = fmpq_poly([0])
        for k in range(2 * J + 1):
            Q += p[k] * T[k]
        A = fmpq_poly([1])
        for y in nodes:
            A *= fmpq_poly([-y, 1]) ** 2
        R, rem = divmod(Q, A)
        exact = (rem == 0) and R.degree() == 2 * J
        r = [R[i] for i in range(R.degree() + 1)]
        Rpos = exact and all(a > 0 for a in r)
        p2J = p[2 * J] > 0
        Pm1 = sum((p[k] * (-1) ** k for k in range(2 * J + 1)), fmpq(0))
        id1 = exact and r[1] / r[0] == 1 - Pm1 + 2 * sum((1 / y for y in nodes), fmpq(0))
        id2 = exact and r[2 * J - 1] / r[2 * J] == 2 * sum(nodes, fmpq(0)) - 2 * J * (4 * J - 1)
        ok = exact and Rpos and p2J and id1 and id2
        allok = allok and ok
        print('J=%2d  (N) ok  exact division %s  R_J > 0 (all %d coefficients) %s  p_2J > 0 %s  identities %s  '
              'r_1/r_0 >= %s  [%.1f s]' % (J, 'ok' if exact else 'FAIL', len(r), 'ok' if Rpos else 'FAIL',
                                          'ok' if p2J else 'FAIL', 'ok' if (id1 and id2) else 'FAIL',
                                          floor_str(r[1] / r[0]) if exact else '-', time.time() - t0), flush=True)
    print('ALL CERTIFIED: (N), p_2J > 0 and (AP+)_J at delta = %s for J = %d..%d' % (c - 1, Jmin, Jmax)
          if allok else 'NOT ALL CERTIFIED')
    sys.exit(0 if allok else 1)


if __name__ == '__main__':
    main()
