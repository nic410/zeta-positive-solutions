"""Second evaluation path: an independent evaluator of Fhat_P^{(m)} for corroboration runs (drop-in replacement of
conelib.Fhat).  It uses an independent exact operator construction (lib/opcalc.py), not lib/bessel_form:
in the basis e0 = K_0(z), e1 = z K_1(z), with w = z^2 and theta = z d/dz,
    theta e0 = -e1,  theta e1 = -w e0,  theta w^i = 2i w^i,   W_0 = (w^2 + 9w) e0 - 6w e1,
    (A_j, B_j) := (2 theta + 1)^j W_0  (exact integer polynomials in w; lib/opcalc.build_ops),
    G_m = (theta + 1/2)^m P(-(theta + 1/2)^2) W_0 = sum_k p_k (-1)^k 4^{-k} 2^{-m} (A_{2k+m} e0 + B_{2k+m} e1)
        =: Acal_m(w) K_0(z) + Bcal_m(w) z K_1(z),
    Fhat_P^{(m)}(xi) = (2 pi)^m 2 pi sqrt(x) sum_N d(N) G_m(2 pi N x).
K_0 and z K_1: lib/besselk.K01 (series / asymptotic; Lemma A.3) by default here (the primary runs use the trapezoid rule),
or lib/k01_trapezoid.k01_trap.  N-tails: |Acal K0 + Bcal zK1| <= (|Acal|(w) + z|Bcal|(w)) K_{3/2}(z), d(N) <= 2 sqrt N, ratio of
consecutive bounds <= ((N+1)/N)^D e^{-2 pi x}, D = 1 + z-degree.  Sup bounds: |Acal|, |Bcal| increase and K_0, z K_1 decrease
in z > 0 ((z K_1)' = -z K_0).
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import conelib as L                                                      # noqa: E402  (paths, K backends)
from flint import arb, arb_poly, ctx                                     # noqa: E402
from lib.opcalc import build_ops, dcount                                 # noqa: E402
from lib.besselk import K32_upper                                        # noqa: E402


def _hw(cs, w):
    v = arb(0)
    for c in reversed(cs):
        v = v * w + c
    return v


class FhatAlt:
    def __init__(self, P, mmax, prec, kback='series'):
        self.prec = prec
        self.kback = kback
        old = ctx.prec
        ctx.prec = prec
        n2 = len(P) - 1
        ops = build_ops(2 * n2 + mmax + 1)
        self.A, self.B = [], []
        for m in range(mmax + 1):
            A = arb_poly([0]); B = arb_poly([0])
            f = arb(1) / arb(2) ** m
            for k, ck in enumerate(P):
                a, b = ops[2 * k + m]
                A += arb_poly([arb(x) for x in a.coeffs()]) * (ck * f)
                B += arb_poly([arb(x) for x in b.coeffs()]) * (ck * f)
                f = -f / 4
            self.A.append(A.coeffs()); self.B.append(B.coeffs())
        self.Aabs = [[abs(c) for c in A] for A in self.A]
        self.Babs = [[abs(c) for c in B] for B in self.B]
        self.Dm = [max(2 * (len(A) - 1), 2 * (len(B) - 1) + 1) + 1 for A, B in zip(self.A, self.B)]
        self.D = max(self.Dm)
        self._d = {}
        ctx.prec = old

    def K(self, z):
        """(K_0(z), z K_1(z)) on the ball z."""
        if self.kback == 'trap':
            K0, K1 = L.K01_trap(z, self.prec)
        else:
            K0, K1 = L.K01_series(z, self.prec)
        ctx.prec = self.prec + 64
        return +K0, z * K1

    def d(self, N):
        if N not in self._d:
            self._d[N] = dcount(N)
        return self._d[N]

    def tail_N(self, m, x_lo, x_hi, Nmax):
        PI = arb.pi()
        N1 = Nmax + 1
        zl = 2 * PI * N1 * arb(x_lo.lower())
        zh = 2 * PI * N1 * arb(x_hi.upper())
        t1 = 2 * arb(N1).sqrt() * (_hw(self.Aabs[m], zh * zh) + zh * _hw(self.Babs[m], zh * zh)) * K32_upper(zl)
        q = (arb(N1 + 1) / N1) ** self.Dm[m] * (-2 * PI * arb(x_lo.lower())).exp()
        if not (q < 1):
            return None
        return t1 / (1 - q)

    def derivs(self, xi, mlist, rel=None, mchk=None, Nmax_hard=100000):
        ctx.prec = self.prec
        if rel is None:
            rel = arb(2) ** -100
        if mchk is None:
            mchk = [mlist[0], mlist[-1]]
        PI = arb.pi()
        x = (2 * PI * xi).exp()
        acc = {m: arb(0) for m in mlist}
        N = 0
        while True:
            N += 1
            z = 2 * PI * N * x
            K0, zK1 = self.K(z)
            ctx.prec = self.prec
            w = z * z
            dN = self.d(N)
            for m in mlist:
                acc[m] += dN * (_hw(self.A[m], w) * K0 + _hw(self.B[m], w) * zK1)
            if N >= 2:
                ok = True
                for m in mchk:
                    t = self.tail_N(m, x, x, N)
                    if t is None or not (N >= Nmax_hard or t < rel * abs(acc[m])):
                        ok = False
                        break
                if ok:
                    tails = {m: self.tail_N(m, x, x, N) for m in mlist}
                    if all(t is not None for t in tails.values()):
                        break
        return {m: (2 * PI) ** m * 2 * PI * x.sqrt() * (acc[m] + arb(0, tails[m].upper())) for m in mlist}, N

    def sup_abs(self, m, xi_lo, xi_hi, rel='1e-3'):
        ctx.prec = self.prec
        PI = arb.pi()
        x_lo = arb(((2 * PI * arb(xi_lo.lower())).exp()).lower())
        x_hi = arb(((2 * PI * arb(xi_hi.upper())).exp()).upper())
        S = arb(0)
        N = 0
        relb = arb(rel)
        while True:
            N += 1
            zl = arb((2 * PI * N * x_lo).lower())
            zh = arb((2 * PI * N * x_hi).upper())
            K0l, zK1l = self.K(zl)
            ctx.prec = self.prec
            wh = zh * zh
            S += self.d(N) * (_hw(self.Aabs[m], wh) * arb(K0l.upper()) + _hw(self.Babs[m], wh) * arb(zK1l.upper()))
            if N >= 2:
                t = self.tail_N(m, x_lo, x_hi, N)
                if t is not None and t < S * relb:
                    S += t
                    break
        return arb(((2 * PI) ** m * 2 * PI * x_hi.sqrt() * S).upper())


def U_bound_alt(E, x):
    """|Fhat(xi)| <= 4 pi (|Acal_0|(z^2) + z |Bcal_0|(z^2)) e^{-z}(1 + 1/z)/(1 - q), z = 2 pi x, q = 2^D e^{-z} < 1/2."""
    from lib.common import require
    ctx.prec = E.prec
    PI = arb.pi()
    z = 2 * PI * x
    q = arb(2) ** E.D * (-z).exp()
    require(q < arb('0.5'), 'U_bound: needs 2^D e^{-2 pi x} < 1/2')
    return 2 * 2 * PI * (_hw(E.Aabs[0], z * z) + z * _hw(E.Babs[0], z * z)) * (-z).exp() * (1 + 1 / z) / (1 - q)
