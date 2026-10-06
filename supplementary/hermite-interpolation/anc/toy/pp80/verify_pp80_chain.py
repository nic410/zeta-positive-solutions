#!/usr/bin/env python3
"""Theorem PP80, second route: hypotheses (I0), (I1'), (Y0) of Theorem A via the Stirling-1 cofactor system (Arb).

Usage (from anc/):  python3 toy/pp80/verify_pp80_chain.py toy/pp80/params/pp80_chain.json [Kmin Kmax]

This route shares no code with verify_pp80_tau.py: it never forms the tau basis.  It uses the characterisation of
the admissible space A_K = span(tau_0..tau_K) by odd Mellin coefficients (paper, toy model):
    Q (deg Q <= 2K) lies in A_K  <=>  sum_m q_m |s(m, 2i-1)| = 0 for i = 1..K,
where q_m are the coefficients of Q and |s(m, l)| are the unsigned Stirling numbers of the first kind.
For a multiset Z of K points the chain cofactor f_Z is the monic polynomial of degree K with
prod_{z in Z}(y - z) f_Z in A_K; it is found from the K x K linear system above in the unknowns f_0..f_{K-1}.
Nodes y_j = 2 pi n_j (n_j the j-th prime power, real pi), doubled chain z_{2j-1} = z_{2j} = y_j, Z_K = (z_1..z_K),
f = f_{Z_K}, g = f_{Z_K + 0} (one extra point at 0).
Checked at every level K in range:
  (I0)   every coefficient of f is > 0;
  (I1')  r_{k+1} - r_k > 0 for k = 0..K-1, where r_k = g_k / f_k;
  (Y0)   g(z_{K+1}) > 0.
All decisions are on Arb balls (a sign is accepted only if the ball excludes 0; arb_mat.solve raises unless it
proves that the matrix is invertible).  Printed bounds are rounded outward.
"""
import hashlib
import json
import math
import os
import sys
import time
from fractions import Fraction

from flint import arb, arb_mat, arb_poly, ctx


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


def is_prime_power(n):
    if n < 2:
        return False
    p = 2
    while p * p <= n:
        if n % p == 0:
            while n % p == 0:
                n //= p
            return n == 1
        p += 1
    return True


def stirling1_unsigned(n):
    s = [[0] * (n + 1) for _ in range(n + 1)]
    s[0][0] = 1
    for m in range(1, n + 1):
        for k in range(1, m + 1):
            s[m][k] = s[m - 1][k - 1] + (m - 1) * s[m - 1][k]
    return s


def exact_fraction(x):
    m, e = x.man_exp()
    m, e = int(m), int(e)
    return Fraction(m * 2 ** e) if e >= 0 else Fraction(m, 2 ** (-e))


def fmt_dir(q, sig, up):
    if q == 0:
        return '0'
    a = abs(q)
    E = int((a.numerator.bit_length() - a.denominator.bit_length()) * 0.3010299956639812)   # no big-int str()
    while Fraction(10) ** E > a:
        E -= 1
    while Fraction(10) ** (E + 1) <= a:
        E += 1
    t = q / Fraction(10) ** (E - sig + 1)
    n = math.ceil(t) if up else math.floor(t)
    s = str(abs(n))
    return '%s%s%se%+d' % ('-' if n < 0 else '', s[0], ('.' + s[1:]) if len(s) > 1 else '', E - sig + len(s))


def main():
    pfile = sys.argv[1]
    par = json.load(open(pfile))
    print('Theorem PP80, hypotheses of Theorem A via the Stirling-1 cofactor system (Arb ball arithmetic)')
    print('parameter file %s  sha256 %s' % (rel(pfile), sha256_file(pfile)))
    L0, L1 = par['levels']
    Kmin, Kmax = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (L0, L1)
    require(L0 <= Kmin <= Kmax <= L1, 'check failed: L0 <= Kmin <= Kmax <= L1')
    prec = int(par['precision_bits'])
    ctx.prec = prec
    pp = [int(n) for n in par['prime_powers']]
    require([n for n in range(2, pp[-1] + 1) if is_prime_power(n)] == pp, 'prime-power list is not an initial segment')
    npp = Kmax // 2 + 1
    require(npp <= len(pp), 'check failed: npp <= len(pp)')
    PI = arb.pi()
    chain = [2 * PI * n for n in pp[:npp] for _ in range(2)]
    print('levels K = %d..%d, working precision %d bits, chain z = 2 pi (2, 2, 3, 3, 4, 4, ..., %d, %d)'
          % (Kmin, Kmax, prec, pp[npp - 1], pp[npp - 1]), flush=True)
    st1 = stirling1_unsigned(2 * Kmax + 2)

    def cofactor(Z):
        K = len(Z)
        if K == 0:
            return [arb(1)]
        w = arb_poly([1])
        for z in Z:
            w *= arb_poly([-z, 1])
        cols = []
        for j in range(K + 1):                       # column of the monomial y^j of f:  Q_j = w y^j
            Qj = w * arb_poly([0] * j + [1])
            d = Qj.degree()
            cols.append([sum((Qj[m] * st1[m][2 * i - 1] for m in range(2 * i - 1, d + 1)), arb(0))
                         for i in range(1, K + 1)])
        A = arb_mat([[cols[j][i] for j in range(K)] for i in range(K)])
        b = arb_mat([[-cols[K][i]] for i in range(K)])
        x = A.solve(b)                               # raises unless invertibility is proved
        return [x[j, 0] for j in range(K)] + [arb(1)]

    def polyval(c, t):
        s = arb(0)
        for a in reversed(c):
            s = s * t + a
        return s

    allok = True
    min_inc = None
    worst_rad = None
    for K in range(Kmin, Kmax + 1):
        t0 = time.time()
        Z = chain[:K]
        f = cofactor(Z)
        g = cofactor(Z + [arb(0)])
        I0 = all(x > 0 for x in f)
        r = [g[k] / f[k] for k in range(K + 1)]
        I1p = all((r[k + 1] - r[k]) > 0 for k in range(K))
        Y0 = polyval(g, chain[K]) > 0
        ok = I0 and I1p and Y0
        allok = allok and ok
        line = 'K=%3d  (I0) %s  (I1\') %s  (Y0) %s' % (K, 'ok' if I0 else 'FAIL', 'ok' if I1p else 'FAIL',
                                                       'ok' if Y0 else 'FAIL')
        if K > 1 and I0:
            incs = [(r[k + 1] - r[k]) / abs(r[k]) for k in range(1, K)]     # interior increments, k = 1..K-1
            lo = min(exact_fraction(x.lower()) for x in incs)
            min_inc = lo if min_inc is None else min(min_inc, lo)
            line += '  min_{1<=k<K} rel. LR increment >= %s' % fmt_dir(lo, 7, up=False)
        rads = [abs(x.rad() / x.mid()) for x in f + g if not x.contains(0) and x.rad() > 0]
        if rads:
            wr = max(exact_fraction(x.upper()) for x in rads)
            worst_rad = wr if worst_rad is None else max(worst_rad, wr)
            line += '  rel. radius <= %s' % fmt_dir(wr, 3, up=True)
        print(line + '  [%.1f s]' % (time.time() - t0), flush=True)
    print('minimum over these levels of min_{1<=k<K} (r_{k+1}-r_k)/|r_k| >= %s'
          % (fmt_dir(min_inc, 7, up=False) if min_inc is not None else 'n/a'))
    print('worst relative radius of a cofactor coefficient <= %s' % (fmt_dir(worst_rad, 3, up=True) if worst_rad else 'n/a'))
    print('ALL CERTIFIED: (I0), (I1\'), (Y0) at every level K = %d..%d' % (Kmin, Kmax) if allok else 'NOT ALL CERTIFIED')
    sys.exit(0 if allok else 1)


if __name__ == '__main__':
    main()
