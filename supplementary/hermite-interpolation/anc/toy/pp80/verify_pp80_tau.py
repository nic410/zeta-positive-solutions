#!/usr/bin/env python3
"""Theorem PP80 (toy model, prime-power nodes): Arb ball-arithmetic certificate, tau-basis Hermite route.

Usage (from anc/):  python3 toy/pp80/verify_pp80_tau.py toy/pp80/params/pp80.json [Kmin Kmax]
                    (default: the full level range of the parameter file; the range may be split over processes)

Notation (paper, section on the toy model).
  theta = y d/dy;  tau_k(y) := (-1)^k (theta - y)^{2k} 1  (integer coefficients, degree 2k, leading coefficient
  (-1)^k; tau_0 = 1 and tau_k(0) = 0 for k >= 1; equivalently tau_k(y) = (-1)^k T_{2k}(-y), T_m Touchard).
  For P(u) = sum_k p_k u^k the toy transform is Q_P = sum_k p_k tau_k.
  Nodes y_j = 2 pi n_j, n_j the j-th prime power (2, 3, 4, 5, 7, 8, 9, 11, ...), with the real number pi.
  Doubled chain z_{2j-1} = z_{2j} = y_j and Z_K = (z_1, ..., z_K).
  Chain cofactor: F_Z is the element of span(tau_0, ..., tau_K) (K = |Z|) with tau_K-coefficient (-1)^K that
  vanishes on the multiset Z (with multiplicity); it is monic of degree 2K, and f_Z = F_Z / prod_{z in Z}(y - z)
  is monic of degree K.  g = f_{Z_K + 0} (one extra point at 0) is monic of degree K + 1.

Part 1 -- the hypotheses of Theorem A, at every level K in range:
  (I0)   every coefficient of f = f_{Z_K} is > 0;
  (I1')  g_{k+1} f_k - g_k f_{k+1} > 0 for k = 0..K-1 (so r_k = g_k/f_k is strictly increasing);
  (Y0)   g(z_{K+1}) > 0.
Part 2 -- the conclusions of Theorem PP80, checked directly (independently of Theorem A), at every even K = 2J >= 2:
  (N)    the toy system P(0) = 1, Q_P(y_j) = Q_P'(y_j) = 0 (j = 1..J), unknowns p_1..p_2J, is non-singular;
  p_2J > 0;  together with (I0) at level 2J this gives R_J = Q_P / prod_j (y - y_j)^2 = p_2J f_{Z_2J} > 0;
  TEL_J  Rhat_J - Rhat_{J-1} has strictly positive coefficients in degrees 1..2J (Rhat = R/R(0) = f/f(0));
  half-step positivity: every coefficient of f_{Z_{2J-1}} is > 0;
  consistency: the ball p_2J * prod_j y_j^2 * f_{Z_2J}(0) contains 1 (exact value 1, since Q_P(0) = 1).

Rigour.  All quantities are Arb balls (python-flint arb, working precision from the parameter file).  A sign is
accepted only if the ball excludes 0; arb_mat.solve raises ZeroDivisionError unless it proves that the matrix is
invertible.  Division by (y - z) is done bottom-up and is exact in exact arithmetic, so the balls enclose the true
coefficients.  Printed bounds are rounded outward (lower bounds down, upper bounds up).
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


def exact_fraction(x):
    m, e = x.man_exp()
    m, e = int(m), int(e)
    return Fraction(m * 2 ** e) if e >= 0 else Fraction(m, 2 ** (-e))


def fmt_dir(q, sig, up):
    """decimal string of the Fraction q with sig significant digits, rounded up (up=True) or down."""
    if q == 0:
        return '0'
    a = abs(q)
    E = len(str(a.numerator)) - len(str(a.denominator))
    while Fraction(10) ** E > a:
        E -= 1
    while Fraction(10) ** (E + 1) <= a:
        E += 1
    t = q / Fraction(10) ** (E - sig + 1)
    n = math.ceil(t) if up else math.floor(t)
    s = str(abs(n))
    return '%s%s%se%+d' % ('-' if n < 0 else '', s[0], ('.' + s[1:]) if len(s) > 1 else '', E - sig + len(s))


def lower_str(x, sig=7):
    return fmt_dir(exact_fraction(x.lower()), sig, up=False)


def upper_str(x, sig=3):
    return fmt_dir(exact_fraction(x.upper()), sig, up=True)


def main():
    pfile = sys.argv[1]
    par = json.load(open(pfile))
    print('Theorem PP80, tau-basis Hermite route (Arb ball arithmetic)')
    print('parameter file %s  sha256 %s' % (rel(pfile), sha256_file(pfile)))
    L0, L1 = par['levels']
    Kmin, Kmax = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (L0, L1)
    require(L0 <= Kmin <= Kmax <= L1, 'level range outside the parameter file')
    prec = int(par['precision_bits'])
    ctx.prec = prec
    pp = [int(n) for n in par['prime_powers']]
    # the list must be exactly the first len(pp) prime powers, in increasing order
    require(all(is_prime_power(n) for n in pp) and pp == sorted(set(pp)), 'node list must be increasing prime powers')
    require([n for n in range(2, pp[-1] + 1) if is_prime_power(n)] == pp, 'prime-power list is not an initial segment')
    npp = Kmax // 2 + 1                  # nodes y_1..y_{Kmax/2+1} are needed (z_{K+1} for (Y0) at K = Kmax)
    require(npp <= len(pp), 'check failed: npp <= len(pp)')
    PI = arb.pi()
    nodes = [2 * PI * n for n in pp[:npp]]
    print('levels K = %d..%d, working precision %d bits, nodes y_j = 2 pi n_j for n_j in %s ... %s (%d nodes)'
          % (Kmin, Kmax, prec, pp[:5], pp[npp - 1], npp))
    kmax = Kmax + 2
    t0 = time.time()
    TA = [[arb(c) for c in tau(k)] for k in range(kmax + 1)]
    VAL = [[None] * (kmax + 1) for _ in nodes]       # VAL[j][k] = (tau_k(y_j), tau_k'(y_j))
    for k in range(kmax + 1):
        P = arb_poly(TA[k])
        dP = P.derivative()
        for j, z in enumerate(nodes):
            VAL[j][k] = (P(z), dP(z))
    print('tau values cached (%.1f s)' % (time.time() - t0), flush=True)

    def rows_for(K):
        """Hermite conditions for Z_K: (node index, derivative order)."""
        R = []
        for j in range(K // 2):
            R += [(j, 0), (j, 1)]
        if K % 2:
            R.append((K // 2, 0))
        return R

    def solve_elem(K, kstart):
        """tau-coefficients of the element of span(tau_kstart..tau_{kstart+K}) vanishing on Z_K whose
        tau_{kstart+K}-coefficient is (-1)^{kstart+K}; kstart = 0 gives F_{Z_K}, kstart = 1 gives F_{Z_K+0}."""
        R = rows_for(K)
        top = kstart + K
        atop = arb((-1) ** top)
        if K == 0:
            return {top: atop}
        A = arb_mat([[VAL[j][k][d] for k in range(kstart, top)] for (j, d) in R])
        b = arb_mat([[-atop * VAL[j][top][d]] for (j, d) in R])
        x = A.solve(b)                                   # raises unless invertibility is proved
        a = {kstart + i: x[i, 0] for i in range(K)}
        a[top] = atop
        return a

    def poly_from(a, deg):
        c = [arb(0)] * (deg + 1)
        for k, ak in a.items():
            for m, t in enumerate(TA[k]):
                if m <= deg:
                    c[m] += ak * t
        return c

    def divide(c, K, shift0=False):
        """divide by prod_{z in Z_K}(y - z) (and by y if shift0), bottom-up synthetic division."""
        if shift0:
            c = c[1:]                                    # F_{Z+0}(0) = 0 exactly (no tau_0 component)
        for j in range(K // 2 + K % 2):
            mult = 2 if j < K // 2 else 1
            z = nodes[j]
            for _ in range(mult):
                q = [arb(0)] * (len(c) - 1)
                prev = arb(0)
                for i in range(len(c) - 1):
                    prev = (prev - c[i]) / z
                    q[i] = prev
                c = q
        return c

    def cof_f(K):
        return divide(poly_from(solve_elem(K, 0), 2 * K), K)

    def cof_g(K):
        return divide(poly_from(solve_elem(K, 1), 2 * K + 2), K, shift0=True)

    def polyval(c, t):
        s = arb(0)
        for x in reversed(c):
            s = s * t + x
        return s

    allok = True
    fcache = {}
    min_inc = None
    worst_rad = None
    nJ = 0
    for K in range(Kmin, Kmax + 1):
        t1 = time.time()
        f = cof_f(K)
        g = cof_g(K)
        fcache[K] = f
        require(len(f) == K + 1 and len(g) == K + 2 and f[K].overlaps(arb(1)) and g[K + 1].overlaps(arb(1)),
                'chain systems: unexpected size or normalisation')
        I0 = all(c > 0 for c in f)
        I1p = I0 and all((g[k + 1] * f[k] - g[k] * f[k + 1]) > 0 for k in range(K))
        Y0 = polyval(g, nodes[K // 2]) > 0              # nodes[K//2] = z_{K+1}
        line = 'K=%3d  (I0) %s  (I1\') %s  (Y0) %s' % (K, 'ok' if I0 else 'FAIL', 'ok' if I1p else 'FAIL',
                                                       'ok' if Y0 else 'FAIL')
        ok = I0 and I1p and Y0
        if I0 and K >= 1:
            r = [g[k] / f[k] for k in range(K + 1)]
            incs = [(r[k + 1] - r[k]) / abs(r[k]) for k in range(K) if not r[k].contains(0)]
            lo = min(exact_fraction(x.lower()) for x in incs)
            min_inc = lo if min_inc is None else min(min_inc, lo)
            line += '  min rel. LR increment >= %s' % fmt_dir(lo, 7, up=False)
        rads = [abs(c.rad() / c.mid()) for c in f + g if not c.contains(0) and c.rad() > 0]
        if rads:
            wr = max(exact_fraction(x.upper()) for x in rads)
            worst_rad = wr if worst_rad is None else max(worst_rad, wr)
            line += '  rel. radius <= %s' % fmt_dir(wr, 3, up=True)
        if K % 2 == 0 and K >= 2:
            J = K // 2
            fm2 = fcache.get(K - 2) or cof_f(K - 2)
            fm1 = fcache.get(K - 1) or cof_f(K - 1)
            R = rows_for(K)
            A = arb_mat([[VAL[j][k][d] for k in range(1, K + 1)] for (j, d) in R])
            b = arb_mat([[-VAL[j][0][d]] for (j, d) in R])
            p = A.solve(b)                               # (N): raises unless non-singularity is proved
            p2J = p[K - 1, 0]
            Rh = [c / f[0] for c in f]
            Rm = [c / fm2[0] for c in fm2] + [arb(0), arb(0)]
            TEL = all((Rh[i] - Rm[i]) > 0 for i in range(1, K + 1))
            half = all(c > 0 for c in fm1)
            w0 = arb(1)
            for y in nodes[:J]:
                w0 *= y * y
            cons = (p2J * w0 * f[0]).overlaps(arb(1))
            pos = bool(p2J > 0)
            line += '  | J=%2d (N) ok  p_2J>0 %s  TEL %s  half-step %s  consistency %s' % (
                J, 'ok' if pos else 'FAIL', 'ok' if TEL else 'FAIL', 'ok' if half else 'FAIL', 'ok' if cons else 'FAIL')
            ok = ok and pos and TEL and half and cons
            nJ += 1
            fcache.pop(K - 3, None)
            fcache.pop(K - 4, None)
        allok = allok and ok
        print(line + '  [%.1f s]' % (time.time() - t1), flush=True)
    Js = [K // 2 for K in range(Kmin, Kmax + 1) if K % 2 == 0 and K >= 2]
    print('minimum over these levels of the relative LR increment min_k (r_{k+1}-r_k)/|r_k| >= %s'
          % (fmt_dir(min_inc, 7, up=False) if min_inc is not None else 'n/a'))
    print('worst relative radius of a cofactor coefficient <= %s' % (fmt_dir(worst_rad, 3, up=True) if worst_rad else 'n/a'))
    if allok:
        print('ALL CERTIFIED: (I0), (I1\'), (Y0) at every level K = %d..%d' % (Kmin, Kmax)
              + ('; (N), p_2J > 0, TEL_J, half-step positivity, consistency for J = %d..%d' % (Js[0], Js[-1]) if Js else ''))
    else:
        print('NOT ALL CERTIFIED')
    sys.exit(0 if allok else 1)


if __name__ == '__main__':
    main()
