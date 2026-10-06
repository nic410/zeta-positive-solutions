#!/usr/bin/env python3
"""Remark (zero-slack prefix traces are not sufficient): three exact J = 2 points with PT_1, PT_2 true and r_1 < 0.

Usage (from anc/):  python3 toy/pt/verify_pt0_false.py toy/pt/params/pt0_false.json

For nodes 0 < y_1 < y_2 (exact rationals from the parameter file) the toy system P(0) = 1, Q_P(y_j) = Q_P'(y_j) = 0
(j = 1, 2) in p_1..p_4 is solved exactly (Q_P = sum_k p_k tau_k, tau_k(y) = (-1)^k (theta - y)^{2k} 1, theta = y d/dy),
and R = Q_P / ((y - y_1)^2 (y - y_2)^2) = r_0 + r_1 y + ... + r_4 y^4 (exact division; r_0 = 1/(y_1 y_2)^2).
At each point the script checks, in exact rational arithmetic (python-flint fmpq, fmpq_mat, fmpq_poly):
    PT_1: y_1 > 3 and PT_2: y_1 + y_2 > 14 (strict, as in the definition; zero slack, delta = 0);
    (N) (the exact solve succeeds);
    r_1 < 0, so R is not in R_{>0}[y];
and prints the exact value of r_1, decimal enclosures of r_1 and r_1/r_0, and the signs of all r_i.  It also prints
whether PT_{0.05} holds (it must fail, by Theorem PT2): y_1 >= 63/20 and y_1 + y_2 >= 147/10.
"""
import hashlib
import json
import math
import os
import sys
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


def fmt_dir(q, sig, up):
    q = Fraction(int(q.p), int(q.q))
    if q == 0:
        return '0'
    a = abs(q)
    E = int((a.numerator.bit_length() - a.denominator.bit_length()) * 0.3010299956639812)
    while Fraction(10) ** E > a:
        E -= 1
    while Fraction(10) ** (E + 1) <= a:
        E += 1
    t = q / Fraction(10) ** (E - sig + 1)
    n = math.ceil(t) if up else math.floor(t)
    s = str(abs(n))
    return '%s%s%se%+d' % ('-' if n < 0 else '', s[0], ('.' + s[1:]) if len(s) > 1 else '', E - sig + len(s))


def dec(q):
    """exact decimal string of a rational with a terminating decimal expansion."""
    from decimal import Decimal, getcontext
    getcontext().prec = 50
    v = Decimal(int(q.p)) / Decimal(int(q.q))
    require(Fraction(v) == Fraction(int(q.p), int(q.q)), 'exact rational conversion')
    return format(v.normalize(), 'f')


def main():
    pfile = sys.argv[1]
    par = json.load(open(pfile))
    print('Zero-slack PT is not sufficient at J = 2: exact certificate')
    print('parameter file %s  sha256 %s' % (rel(pfile), sha256_file(pfile)), flush=True)
    T = [fmpq_poly(tau(k)) for k in range(5)]
    dT = [t.derivative() for t in T]
    allok = True
    for pt in par['points']:
        y1, y2 = (fmpq(*[int(t) for t in s.split('/')]) if '/' in s else fmpq(int(s)) for s in pt)
        pt0 = (y1 > 3) and (y1 + y2 > 14) and (0 < y1 < y2)
        pt5 = (y1 >= fmpq(63, 20)) and (y1 + y2 >= fmpq(147, 10))
        M = fmpq_mat([[T[k](y) for k in range(1, 5)] if d == 0 else [dT[k](y) for k in range(1, 5)] for y in (y1, y2) for d in (0, 1)])
        b = fmpq_mat([[-1], [0], [-1], [0]])
        try:
            x = M.solve(b)
            N = (M * x == b)
        except ZeroDivisionError:
            N = False
        if not N:
            print('(y_1, y_2) = (%s, %s): (N) FAILS' % (y1, y2))
            allok = False
            continue
        Q = T[0]
        for k in range(1, 5):
            Q += x[k - 1, 0] * T[k]
        A = fmpq_poly([-y1, 1]) ** 2 * fmpq_poly([-y2, 1]) ** 2
        R, rem = divmod(Q, A)
        r = [R[i] for i in range(R.degree() + 1)]
        exact = rem == 0 and R.degree() == 4 and r[0] == 1 / (y1 * y1 * y2 * y2)
        neg = r[1] < 0
        ok = pt0 and exact and neg
        allok = allok and ok
        print('(y_1, y_2) = (%s, %s) = (%s, %s) exactly:' % (y1, y2, dec(y1), dec(y2)))
        print('    PT_1 (y_1 > 3) and PT_2 (y_1 + y_2 > 14): %s;  PT_0.05 (y_1 >= 63/20, y_1 + y_2 >= 147/10): %s;  (N): True'
              % (pt0, pt5))
        print('    R = Q/A exact, r_0 = 1/(y_1 y_2)^2: %s;  signs of r_0..r_4: %s'
              % (exact, ''.join('+' if c > 0 else ('-' if c < 0 else '0') for c in r)))
        print('    r_1 = %s' % r[1])
        print('    r_1 in [%s, %s];  r_1/r_0 in [%s, %s]  => r_1 < 0: %s'
              % (fmt_dir(r[1], 6, False), fmt_dir(r[1], 6, True), fmt_dir(r[1] / r[0], 6, False), fmt_dir(r[1] / r[0], 6, True), neg),
              flush=True)
    print('ALL CERTIFIED: at every point PT_1 and PT_2 hold (zero slack), (N) holds and r_1 < 0' if allok else 'NOT ALL CERTIFIED')
    sys.exit(0 if allok else 1)


if __name__ == '__main__':
    main()
