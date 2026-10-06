"""Lemma BF certificate: Fhat_{Xi^2 P_J(t^2)}(xi) > 0 for x = e^{2 pi xi} >= x_0, for the exact Hermite member P_J.

Bessel form: Fhat_P(xi) = 2 pi sqrt(x) sum_N d(N) g_P(2 pi N x), g_P = R_P(theta) K_0, R_P(theta) = P(-(theta+1/2)^2) theta^2 (theta+1)^2.
Since K_0(z) = int_1^oo e^{-zt} (t^2-1)^{-1/2} dt is a multiplicative (Mellin) convolution of e^{-y}, and theta = z d/dz
commutes with it,
    g_P(z) = int_1^oo Q_P(zt) e^{-zt} (t^2-1)^{-1/2} dt,   Q_P(y) e^{-y} := R_P(theta_y) e^{-y}   (Q_P a polynomial of degree 4J+4).
If Q_P has positive leading coefficient and no zero in [y_0, oo), then g_P(z) > 0 for z >= y_0 and, every divisor term
being evaluated at 2 pi N x >= 2 pi x, Fhat_P > 0 for 2 pi x >= y_0.
Certificate: theta acts on the polynomial part as q -> (y d/dy - y) q; Q_P is built in ball arithmetic from a certified
enclosure of the coefficients of P_J (produced by verify_exact_member.py), and all Taylor coefficients of Q_P(y_0 + v)
in v are certified > 0 (Horner Taylor shift), which excludes zeros in [y_0, oo).  A negative control at a smaller x_0
shows a negative constant coefficient (the edge is nearly sharp).

Usage (from anc/):  python exact/verify_bf.py BALLFILE --x0 199.4 [--x0 ...] [--control 199.35] [--prec 4600]
"""
import argparse
import math
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from flint import arb, fmpq, ctx  # noqa: E402
from lib.common import relpath, sha256_file  # noqa: E402


def op(q, c):
    """(theta + c) on q(y) e^{-y}, acting on the polynomial part: (y d/dy + c - y) q."""
    out = [arb(0)] * (len(q) + 1)
    for k, a in enumerate(q):
        out[k] += (k + c) * a
        out[k + 1] -= a
    return out


def taylor_shift(Q, y0):
    a = list(Q)
    n = len(a) - 1
    for i in range(n):
        for k in range(n - 1, i - 1, -1):
            a[k] = a[k] + y0 * a[k + 1]
    return a


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('ball')
    ap.add_argument('--x0', action='append', required=True)
    ap.add_argument('--control', action='append', default=[])
    ap.add_argument('--prec', type=int, default=4600)
    a = ap.parse_args()
    ctx.prec = a.prec
    P = [arb(s) for s in open(a.ball).read().split('\n') if s.strip()]
    J = (len(P) - 1) // 2
    rr = max(float((arb(p.rad()) / abs(p.mid())).log().mid()) / math.log(10) for p in P[1:])
    print('P-enclosure %s (sha256 %s): J = %d, %d coefficients, max log10 relative radius %.0f'
          % (relpath(a.ball), sha256_file(a.ball), J, len(P), rr))
    v = [arb(1)]
    for c in (0, 0, 1, 1):
        v = op(v, c)                                   # theta^2 (theta+1)^2 e^{-y}
    Q = [arb(0)] * (4 * J + 5)
    X = v
    for j in range(2 * J + 1):
        for k, c in enumerate(X):
            Q[k] += P[j] * c
        if j < 2 * J:
            X = [-c for c in op(op(X, arb(1) / 2), arb(1) / 2)]      # -(theta + 1/2)^2
    print('Q_P: degree %d, leading coefficient > 0: %s' % (len(Q) - 1, Q[-1] > 0))
    ok = Q[-1] > 0
    for x0, control in [(x, False) for x in a.x0] + [(x, True) for x in a.control]:
        fr = Fraction(x0)
        y0 = 2 * arb.pi() * arb(fmpq(fr.numerator, fr.denominator))
        t = taylor_shift(Q, y0)
        npos = sum(1 for c in t if c > 0)
        neg = [i for i, c in enumerate(t) if c < 0]
        und = [i for i, c in enumerate(t) if not (c > 0) and not (c < 0)]
        print('  x_0 = %s%s: Taylor coefficients of Q_P(2 pi x_0 + v) certified > 0: %d/%d; negative: %s; undetermined: %s'
              % (x0, ' (negative control)' if control else '', npos, len(t), neg[:5], und[:5]))
        if not control:
            ok = ok and npos == len(t)
    print('CERTIFIED: Fhat > 0 for x >= %s (J = %d): %s' % (min(a.x0, key=Fraction), J, bool(ok)))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
