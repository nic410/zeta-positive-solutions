"""Exact-operator (Bessel form) evaluation of the Fourier transform of F_H = Xi(t)^2 H(t), H(t) = P(t^2).

Normalisation: Fhat(xi) = int F(t) e^{-2 pi i xi t} dt;  x = e^{2 pi xi};  Xi(t) = xi(1/2 + it) (Riemann's xi).

Bessel/Voronoi form.  Lambda(s)^2 = (pi^{-s/2} Gamma(s/2) zeta(s))^2 is the Mellin transform of 4 sum_N d(N) K_0(2 pi N y),
and s(s-1) corresponds to theta(theta+1), theta = y d/dy.  Hence
    Psi(xi) := (Xi^2)^(xi) = 2 pi sqrt(x) sum_{N>=1} d(N) W_0(2 pi N x),   W_0 = theta^2 (theta+1)^2 K_0 = z^2[(z^2+9)K_0 - 6zK_1].
Multiplication by t^2 is -(2 pi)^-2 d^2/dxi^2 = -(theta + 1/2)^2 on functions of the form sqrt(x) g(x), so
    Fhat_H^{(m)}(xi) = (2 pi)^m 2 pi sqrt(x) sum_N d(N) G_m(2 pi N x),   G_m = (theta + 1/2)^m P(-(theta+1/2)^2) theta^2 (theta+1)^2 K_0.
On span{z^k K_0, z^k K_1} the operator theta = z d/dz acts exactly:
    theta(a K_0 + b K_1) = (theta a - z b) K_0 + (theta b - b - z a) K_1      (K_0' = -K_1, (z K_1)' = -z K_0),
so G_m = A_m(z) K_0(z) + B_m(z) K_1(z) with polynomials A_m, B_m obtained from the coefficients of P by exact recurrences.
Here P is enclosed coefficientwise in Arb balls computed from the exact rational factors (so A_m, B_m are balls that
contain the exact polynomials).

N-tails (always added as ball radii): d(N) <= 2 sqrt(N) and K_0 <= K_1 <= K_{3/2}(z) = sqrt(pi/2z) e^{-z}(1+1/z); the product
2 sqrt(N) sqrt(pi/(2 z N)) does not depend on N, so successive term bounds have ratio <= ((N+1)/N)^D e^{-2 pi x} (D >= deg).
"""
from flint import arb, arb_poly, ctx
from .besselk import K01, K32_upper
from .common import require


def build_P(rs, prec):
    """P(u) = prod_j (1 + r_j u + s_j u^2) as an arb_poly (balls containing the exact rational coefficients)."""
    old = ctx.prec
    ctx.prec = prec
    P = arb_poly([1])
    for r, s in rs:
        P = P * arb_poly([arb(1), arb(r), arb(s)])
    ctx.prec = old
    return P


def _theta(A, B):
    def th(q):
        cs = q.coeffs()
        return arb_poly([k * c for k, c in enumerate(cs)]) if cs else arb_poly([0])
    z = arb_poly([0, 1])
    return th(A) - z * B, th(B) - B - z * A


class FhatOperators:
    """Polynomials (A_m, B_m), m = 0..mmax, with G_m = A_m K_0 + B_m K_1 (see module docstring)."""

    def __init__(self, Pcoeffs, mmax, prec):
        old = ctx.prec
        ctx.prec = prec
        th = arb_poly([0, 1])
        w = arb_poly([arb(1) / 2, 1])
        mw2 = -(w * w)
        Q = arb_poly([0])
        for c in reversed(Pcoeffs):                 # Q(theta) = P(-(theta + 1/2)^2)
            Q = Q * mw2 + c
        R = Q * (th * th * (th + 1) * (th + 1))
        A, B = arb_poly([0]), arb_poly([0])
        for c in reversed(R.coeffs()):              # (A_0, B_0) = R(theta) K_0, Horner in theta
            A, B = _theta(A, B)
            A = A + c
        self.AB = [(A, B)]
        for m in range(mmax):
            tA, tB = _theta(A, B)
            A, B = tA + (arb(1) / 2) * A, tB + (arb(1) / 2) * B
            self.AB.append((A, B))
        self.mmax = mmax
        self.deg = max(max(a.degree(), b.degree()) for a, b in self.AB)
        self.coef = [(a.coeffs(), b.coeffs()) for a, b in self.AB]
        self.abscoef = [([abs(c) for c in a], [abs(c) for c in b]) for a, b in self.coef]
        ctx.prec = old


def horner(cs, z):
    v = arb(0)
    for c in reversed(cs):
        v = v * z + c
    return v


def divisor_count(N):
    c, d = 0, 1
    while d * d <= N:
        if N % d == 0:
            c += 1 if d * d == N else 2
        d += 1
    return c


class Evaluator:
    """Rigorous enclosures of Fhat_H^{(m)}(xi) and of sup |Fhat_H^{(m)}| on intervals, at working precision prec."""

    def __init__(self, FO, prec, tail_log10):
        self.FO = FO
        self.prec = prec
        self.tt = tail_log10          # target for the absolute N-tail at node centres: about 10^tail_log10
        self.Zc = None
        self._d = {}

    def d(self, N):
        if N not in self._d:
            self._d[N] = divisor_count(N)
        return self._d[N]

    def zcut(self):
        """Truncation heuristic only (the rigorous tail is always added): first z (step 8) where the crude
        bound of the largest-m terms falls below 10^(tt-5)."""
        if self.Zc is None:
            ctx.prec = self.prec
            Aab, Bab = self.FO.abscoef[-1]
            z = 16
            while True:
                za = arb(z)
                if (horner(Aab, za) + horner(Bab, za)) * K32_upper(za) * 40 < arb(10) ** (self.tt - 5):
                    break
                z += 8
            self.Zc = z
        return self.Zc

    def nmax_for(self, x_lo):
        return max(6, int(self.zcut() / (2 * 3.14159 * float(x_lo))) + 2)

    def tail_N(self, m, x_lo, x_hi, Nmax):
        """Upper bound of sum_{N > Nmax} d(N) |A_m K_0 + B_m K_1|(2 pi N x) for x in [x_lo, x_hi]."""
        PI = arb.pi()
        Aab, Bab = self.FO.abscoef[m]
        D = max(len(Aab), len(Bab))
        N1 = Nmax + 1
        zl = 2 * PI * N1 * arb(x_lo.lower())
        zh = 2 * PI * N1 * arb(x_hi.upper())
        t1 = 2 * arb(N1).sqrt() * (horner(Aab, zh) + horner(Bab, zh)) * K32_upper(zl)
        q = (arb(N1 + 1) / N1) ** D * (-2 * PI * arb(x_lo.lower())).exp()
        if not (q < 1):
            return arb('inf')
        return t1 / (1 - q)

    def _finish(self, acc, mlist, x, N):
        PI = arb.pi()
        out = {}
        for m in mlist:
            tail = self.tail_N(m, x, x, N)
            out[m] = (2 * PI) ** m * 2 * PI * x.sqrt() * (acc[m] + arb(0, tail.upper()))
        return out

    def derivs(self, xi, mlist):
        """Fhat_H^{(m)}(xi) for m in mlist (xi an arb), fixed truncation (full absolute accuracy)."""
        ctx.prec = self.prec
        PI = arb.pi()
        x = (2 * PI * xi).exp()
        Nmax = self.nmax_for(x.lower())
        acc = {m: arb(0) for m in mlist}
        for N in range(1, Nmax + 1):
            z = 2 * PI * N * x
            K0, K1 = K01(z, self.prec)
            dN = self.d(N)
            for m in mlist:
                Aa, Ba = self.FO.coef[m]
                acc[m] += dN * (horner(Aa, z) * K0 + horner(Ba, z) * K1)
        return self._finish(acc, mlist, x, Nmax)

    def derivs_rel(self, xi, mlist, rel=None):
        """As derivs, but truncation stops once the rigorous tail is < rel * |partial sum| for the first and last m."""
        if rel is None:
            rel = arb(10) ** -30
        ctx.prec = self.prec
        PI = arb.pi()
        x = (2 * PI * xi).exp()
        acc = {m: arb(0) for m in mlist}
        mchk = [mlist[0], mlist[-1]]
        Nhard = self.nmax_for(x.lower())
        N = 0
        while True:
            N += 1
            z = 2 * PI * N * x
            K0, K1 = K01(z, self.prec)
            dN = self.d(N)
            for m in mlist:
                Aa, Ba = self.FO.coef[m]
                acc[m] += dN * (horner(Aa, z) * K0 + horner(Ba, z) * K1)
            if N >= Nhard:
                break
            if N >= 2 and N % 2 == 0:
                if all(self.tail_N(m, x, x, N) < rel * abs(acc[m]) for m in mchk):
                    break
        return self._finish(acc, mlist, x, N)

    def sup_abs(self, m, xi_lo, xi_hi):
        """Upper bound of sup |Fhat_H^{(m)}| on [xi_lo, xi_hi]: |A_m|, |B_m| increasing and K_0, K_1 decreasing in z;
        truncation stops once the rigorous tail is < 1e-3 of the partial sum."""
        ctx.prec = self.prec
        PI = arb.pi()
        x_lo = arb(((2 * PI * xi_lo).exp()).lower())
        x_hi = arb(((2 * PI * xi_hi).exp()).upper())
        Aab, Bab = self.FO.abscoef[m]
        S = arb(0)
        N = 0
        Nhard = self.nmax_for(x_lo)
        while True:
            N += 1
            zl = arb((2 * PI * N * x_lo).lower())
            zh = arb((2 * PI * N * x_hi).upper())
            K0l, K1l = K01(zl, 64)
            S += self.d(N) * (horner(Aab, zh) * arb(K0l.upper()) + horner(Bab, zh) * arb(K1l.upper()))
            if N >= Nhard:
                break
            if N >= 2 and self.tail_N(m, x_lo, x_hi, N) < S * arb('1e-3'):
                break
        S += self.tail_N(m, x_lo, x_hi, N)
        return (2 * PI) ** m * 2 * PI * x_hi.sqrt() * S

    def U_bound(self, x):
        """Upper bound of |Fhat_H(xi)| at x = e^{2 pi xi} (x >= 1, 2^D e^{-2 pi x} < 1/2):
        |Fhat_H| <= 2 pi sum_N (|A_0|+|B_0|)(2 pi N x) e^{-2 pi N x}(1 + 1/(2 pi N x)) <= 4 pi (|A_0|+|B_0|)(z) e^{-z}(1+1/z)/(1-q),
        z = 2 pi x, q = 2^D e^{-z}, D = max degree (an extra factor 2 of slack is kept)."""
        ctx.prec = self.prec
        PI = arb.pi()
        Aab, Bab = self.FO.abscoef[0]
        D0 = self.FO.deg
        z = 2 * PI * x
        q = arb(2) ** D0 * (-z).exp()
        require(q < arb('0.5'), 'U_bound: needs 2^D e^{-2 pi x} < 1/2')
        return 2 * 2 * PI * (horner(Aab, z) + horner(Bab, z)) * (-z).exp() * (1 + 1 / z) / (1 - q)
