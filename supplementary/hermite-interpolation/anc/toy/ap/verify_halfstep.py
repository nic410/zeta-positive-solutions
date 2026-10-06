#!/usr/bin/env python3
"""(B)_J at delta = 1/20 for every J = 1..90: the half-step cofactor at the progression nodes is positive (exact).

Usage (from anc/):  python3 toy/ap/verify_halfstep.py toy/ap/params/ap_delta005.json [Jmin Jmax]

Nodes y*_K = c (8K - 5), c = 1 + delta = 21/20.  The half-step chain at level J is the multiset
    Z = (y*_1, y*_1, ..., y*_{J-1}, y*_{J-1}, y*_J)          (|Z| = 2J - 1; the last node is simple).
Its cofactor T_J is the monic polynomial of degree 2J - 1 with prod_{z in Z}(y - z) * T_J in span(tau_0..tau_{2J-1}),
where tau_k(y) = (-1)^k (theta - y)^{2k} 1, theta = y d/dy (paper, toy model).  Here
    F = sum_{k <= 2J-1} a_k tau_k with a_{2J-1} = -1 (so that F is monic of degree 4J - 2),
    F(y*_K) = F'(y*_K) = 0 for K < J and F(y*_J) = 0          (2J - 1 linear conditions on a_0..a_{2J-2}),
    T_J = F / prod_{z in Z}(y - z)                               (exact division).
(B)_J : every coefficient of T_J is > 0; in particular T_J(y*_J) > 0.
Exact rational arithmetic (python-flint fmpq_mat, fmpq_poly); the solve raises ZeroDivisionError if the system is
singular, in which case the chain is reported as not regular.
"""
import hashlib
import json
import os
import sys
import time

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


def main():
    pfile = sys.argv[1]
    par = json.load(open(pfile))
    print('(B) half-step cofactor certificate, exact rational arithmetic')
    print('parameter file %s  sha256 %s' % (rel(pfile), sha256_file(pfile)))
    num, den = (int(t) for t in par['c'].split('/'))
    c = fmpq(num, den)
    J0, J1 = par['J_range']
    Jmin, Jmax = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (J0, J1)
    require(J0 <= Jmin <= Jmax <= J1, 'J range outside the parameter file')
    print('c = 1 + delta = %s, nodes y*_K = c(8K - 5), J = %d..%d' % (c, Jmin, Jmax), flush=True)
    T = [fmpq_poly(tau(k)) for k in range(2 * Jmax)]
    dT = [t.derivative() for t in T]
    allok = True
    for J in range(Jmin, Jmax + 1):
        t0 = time.time()
        nodes = [c * (8 * K - 5) for K in range(1, J + 1)]
        top = 2 * J - 1
        rows, rhs = [], []
        for K, y in enumerate(nodes):
            rows.append([T[k](y) for k in range(top)])
            rhs.append([T[top](y)])                      # a_top = -1 moved to the right-hand side
            if K < J - 1:
                rows.append([dT[k](y) for k in range(top)])
                rhs.append([dT[top](y)])
        M = fmpq_mat(rows)
        b = fmpq_mat(rhs)
        try:
            x = M.solve(b)
            reg = (M * x == b)
        except ZeroDivisionError:
            reg = False
        if not reg:
            print('J=%2d  half-step chain not regular (singular system): FAIL' % J, flush=True)
            allok = False
            continue
        F = -T[top]
        for k in range(top):
            F += x[k, 0] * T[k]
        om = fmpq_poly([1])
        for K, y in enumerate(nodes):
            om *= fmpq_poly([-y, 1]) ** (2 if K < J - 1 else 1)
        Tq, rem = divmod(F, om)
        exact = rem == 0 and Tq.degree() == top and Tq[top] == 1
        tc = [Tq[i] for i in range(Tq.degree() + 1)]
        pos = exact and all(a > 0 for a in tc)
        val = exact and Tq(nodes[-1]) > 0
        ok = exact and pos and val
        allok = allok and ok
        print('J=%2d  regular ok  exact division, monic %s  T_J > 0 (all %d coefficients) %s  T_J(y*_J) > 0 %s  [%.1f s]'
              % (J, 'ok' if exact else 'FAIL', len(tc), 'ok' if pos else 'FAIL', 'ok' if val else 'FAIL',
                 time.time() - t0), flush=True)
    print('ALL CERTIFIED: (B)_J (half-step cofactor T_J > 0, T_J(y*_J) > 0) at delta = %s for J = %d..%d'
          % (c - 1, Jmin, Jmax) if allok else 'NOT ALL CERTIFIED')
    sys.exit(0 if allok else 1)


if __name__ == '__main__':
    main()
