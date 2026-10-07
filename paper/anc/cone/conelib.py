"""Library of the cone/ certificates: rigorous (Arb ball) evaluation of Fhat_J^{(m)}(xi) for the EXACT Hermite member
F_J = Xi^2 P_J(t^2) of the paper (Prop 4.5), starting from a ball enclosure of the coefficient vector of P_J (Prop 5.6,
exact/out/P{J}_ball.txt).  The N-loops of derivs/sup_abs/sup_abs_all stop with an error after NCAP terms (liveness only;
never reached).

Normalisation:  Fhat(xi) = int F(t) e^{-2 pi i xi t} dt,  x = e^{2 pi xi},  z = 2 pi N x,
    Fhat_P^{(m)}(xi) = (2 pi)^m 2 pi sqrt(x) sum_{N>=1} d(N) G_m(2 pi N x),
    G_m = (theta + 1/2)^m P(-(theta+1/2)^2) theta^2 (theta+1)^2 K_0 = A_m(z) K_0(z) + B_m(z) K_1(z),   theta = z d/dz
(Prop 4.2 and Lemma 4.6; the polynomials A_m, B_m are built by lib/bessel_form.FhatOperators, by exact recurrences from
the coefficient balls of P, so they are balls containing the exact polynomials of the exact P_J).

K_0, K_1: validated, never Arb's bessel_k / hypgeom_u.  Backend 'trap' (default): lib/k01_trapezoid.k01_trap (trapezoid
rule on DLMF 10.32.8 with Trefethen-Weideman discretisation bound and explicit truncation bound; returns K_0 and z K_1).
Backend 'series': lib/besselk.K01 (DLMF series / asymptotic expansion with explicit remainder; Lemma A.3).
Both are rigorous for real z >= 1 (trap) resp. z > 0 (series); the self-test compares them.

N-tails (always added as ball radii): d(N) <= 2 sqrt N, K_0 <= K_1 <= K_{3/2}, ratio <= ((N+1)/N)^D e^{-2 pi x}
(Appendix A of the paper; lib/bessel_form.Evaluator.tail_N).

Also here: the Abel preimage Q_P(y) = e^y P(-(theta+1/2)^2) theta^2(theta+1)^2 e^{-y} (Lemma 4.6: G_0(z) =
int_z^oo Q(y) e^{-y} (y^2 - z^2)^{-1/2} dy), its Taylor shift (far-field criterion), and Bernstein lower bounds.
"""
import hashlib
import math
import os
import sys

TOP = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))      # top directory of the ancillary files (has lib/)
if TOP not in sys.path:
    sys.path.insert(0, TOP)
NCAP = 10 ** 6                                                           # liveness cap of the N-loops (never reached)

from flint import arb, arb_poly, fmpq, fmpz, ctx                         # noqa: E402
from lib.bessel_form import FhatOperators, horner, divisor_count          # noqa: E402
from lib.besselk import K01 as K01_series, K32_upper                     # noqa: E402
from lib.common import require                                           # noqa: E402
from lib.k01_trapezoid import k01_trap                                   # noqa: E402  (rigorous trapezoid rule)


def sha256_file(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


def load_pball(path, prec):
    """Coefficient balls p_0..p_{2J} of P_J (one Arb ball string per line).  p_0 must be exactly 1."""
    old = ctx.prec
    ctx.prec = prec
    P = [arb(s) for s in open(path).read().split('\n') if s.strip()]
    ctx.prec = old
    require(P[0] == 1 and P[0].rad() == 0, 'pball: p_0 must be exactly 1')
    require(len(P) % 2 == 1, 'pball: expected 2J+1 coefficients')
    return P


def K01_trap(z, prec):
    """(K_0(z), K_1(z)) for every z in the ball z (z >= 1), from the rigorous trapezoid rule k01_trap (returns K_0, z K_1)."""
    old = ctx.prec
    try:
        ctx.prec = prec
        K0, zK1 = k01_trap(z)
        ctx.prec = prec + 64
        return +K0, zK1 / z
    finally:
        ctx.prec = old


class Fhat:
    """Rigorous enclosures of Fhat^{(m)}(xi) and of sup |Fhat^{(m)}| on intervals, for Fhat = (Xi^2 P(t^2))^."""

    def __init__(self, P, mmax, prec, kback='trap'):
        self.prec = prec
        self.FO = FhatOperators(P, mmax, prec)
        self.kback = kback
        self._d = {}
        self.D = max(max(len(a), len(b)) for a, b in self.FO.abscoef)   # >= 1 + degree of every A_m, B_m

    def K(self, z):
        if self.kback == 'trap':
            return K01_trap(z, self.prec)
        return K01_series(z, self.prec)

    def d(self, N):
        if N not in self._d:
            self._d[N] = divisor_count(N)
        return self._d[N]

    def tail_N(self, m, x_lo, x_hi, Nmax):
        """Upper bound of sum_{N > Nmax} d(N) |A_m K_0 + B_m K_1|(2 pi N x) for x in [x_lo, x_hi] (Appendix A of the paper)."""
        PI = arb.pi()
        Aab, Bab = self.FO.abscoef[m]
        D = max(len(Aab), len(Bab))
        N1 = Nmax + 1
        zl = 2 * PI * N1 * arb(x_lo.lower())
        zh = 2 * PI * N1 * arb(x_hi.upper())
        t1 = 2 * arb(N1).sqrt() * (horner(Aab, zh) + horner(Bab, zh)) * K32_upper(zl)
        q = (arb(N1 + 1) / N1) ** D * (-2 * PI * arb(x_lo.lower())).exp()
        if not (q < 1):
            return None
        return t1 / (1 - q)

    def derivs(self, xi, mlist, rel=None, mchk=None, Nmax_hard=100000):
        """Balls containing Fhat^{(m)}(xi) for m in mlist (xi an arb ball; the balls contain the values at every point of xi).
        Truncation: stop once the rigorous N-tail is < rel * |partial sum| for every m in mchk (default: first and last m);
        the tail bound is always added as a radius, so the result is rigorous whatever the stopping point."""
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
            require(N <= NCAP, 'derivs: no rigorous N-tail bound up to N = %d' % NCAP)
            z = 2 * PI * N * x
            K0, K1 = self.K(z)
            ctx.prec = self.prec
            dN = self.d(N)
            for m in mlist:
                Aa, Ba = self.FO.coef[m]
                acc[m] += dN * (horner(Aa, z) * K0 + horner(Ba, z) * K1)
            if N >= 2:
                ok = True
                for m in mchk:                      # cheap test on the check orders first
                    t = self.tail_N(m, x, x, N)
                    if t is None or not (N >= Nmax_hard or t < rel * abs(acc[m])):
                        ok = False
                        break
                if ok:
                    tails = {m: self.tail_N(m, x, x, N) for m in mlist}
                    if all(t is not None for t in tails.values()):
                        break
        out = {}
        for m in mlist:
            out[m] = (2 * PI) ** m * 2 * PI * x.sqrt() * (acc[m] + arb(0, tails[m].upper()))
        return out, N

    def sup_abs(self, m, xi_lo, xi_hi, rel='1e-3'):
        """Upper bound of sup |Fhat^{(m)}| on [xi_lo, xi_hi] (arbs; their outer endpoints are used):
        |A_m|, |B_m| (absolute-coefficient polynomials) are increasing and K_0, K_1 decreasing in z > 0."""
        ctx.prec = self.prec
        PI = arb.pi()
        x_lo = arb(((2 * PI * arb(xi_lo.lower())).exp()).lower())
        x_hi = arb(((2 * PI * arb(xi_hi.upper())).exp()).upper())
        Aab, Bab = self.FO.abscoef[m]
        S = arb(0)
        N = 0
        relb = arb(rel)
        while True:
            N += 1
            require(N <= NCAP, 'sup_abs: no rigorous N-tail bound up to N = %d' % NCAP)
            zl = arb((2 * PI * N * x_lo).lower())
            zh = arb((2 * PI * N * x_hi).upper())
            K0l, K1l = self.K(zl)          # at the exact point zl: upper bounds for K on [zl, oo) (monotone)
            ctx.prec = self.prec
            S += self.d(N) * (horner(Aab, zh) * arb(K0l.upper()) + horner(Bab, zh) * arb(K1l.upper()))
            if N >= 2:
                t = self.tail_N(m, x_lo, x_hi, N)
                if t is not None and t < S * relb:
                    S += t
                    break
        return arb(((2 * PI) ** m * 2 * PI * x_hi.sqrt() * S).upper())


    def sup_abs_all(self, mlist, xi_lo, xi_hi, rel='1e-3'):
        """sup_abs for several m at once (shared K evaluations); returns {m: upper bound}."""
        ctx.prec = self.prec
        PI = arb.pi()
        x_lo = arb(((2 * PI * arb(xi_lo.lower())).exp()).lower())
        x_hi = arb(((2 * PI * arb(xi_hi.upper())).exp()).upper())
        S = {m: arb(0) for m in mlist}
        done = {}
        N = 0
        relb = arb(rel)
        while len(done) < len(mlist):
            N += 1
            require(N <= NCAP, 'sup_abs_all: no rigorous N-tail bound up to N = %d' % NCAP)
            zl = arb((2 * PI * N * x_lo).lower())
            zh = arb((2 * PI * N * x_hi).upper())
            K0l, K1l = self.K(zl)
            ctx.prec = self.prec
            k0, k1 = arb(K0l.upper()), arb(K1l.upper())
            dN = self.d(N)
            for m in mlist:
                if m in done:
                    continue
                Aab, Bab = self.FO.abscoef[m]
                S[m] += dN * (horner(Aab, zh) * k0 + horner(Bab, zh) * k1)
            if N >= 2:
                for m in mlist:
                    if m in done:
                        continue
                    t = self.tail_N(m, x_lo, x_hi, N)
                    if t is not None and t < S[m] * relb:
                        done[m] = S[m] + t
        f = 2 * PI * x_hi.sqrt()
        return {m: arb(((2 * PI) ** m * f * done[m]).upper()) for m in mlist}


# ------------------------------------------------------------------------------------------------ Abel preimage, far field

def theta_poly(P, prec):
    """Coefficients (in theta) of R(theta) = P(-(theta+1/2)^2) theta^2 (theta+1)^2, as in lib/bessel_form.FhatOperators."""
    old = ctx.prec
    ctx.prec = prec
    th = arb_poly([0, 1])
    w = arb_poly([arb(1) / 2, 1])
    mw2 = -(w * w)
    Q = arb_poly([0])
    for c in reversed(P):
        Q = Q * mw2 + c
    R = Q * (th * th * (th + 1) * (th + 1))
    ctx.prec = old
    return R.coeffs()


def abel_Q(P, prec):
    """Q(y) = e^y R(theta) e^{-y} = sum_i r_i (theta - y)^i 1, with (theta - y) f = y f' - y f on polynomials (Horner)."""
    old = ctx.prec
    ctx.prec = prec
    r = theta_poly(P, prec)
    f = [r[-1]]
    for c in reversed(r[:-1]):
        g = [arb(0)] * (len(f) + 1)
        for i, a in enumerate(f):
            g[i] += i * a          # theta f
            g[i + 1] -= a          # - y f
        g[0] += c
        f = g
    ctx.prec = old
    return f


def taylor_shift(c, y0):
    """Coefficients of q(y0 + v) in v (ball arithmetic, repeated synthetic division; contains the exact shift)."""
    c = list(c)
    out = []
    n = len(c)
    for k in range(n):
        acc = c[-1]
        new = [arb(0)] * (len(c) - 1)
        for i in range(len(c) - 2, -1, -1):
            new[i] = acc
            acc = acc * y0 + c[i]
        out.append(acc)
        c = new
        if not c:
            break
    return out


# ------------------------------------------------------------------------------------------------ Bernstein lower bound

_BC = {}


def _bern_matrix(n):
    """Exact rationals C(i,k)/C(n,k), 0 <= k <= i <= n."""
    if n not in _BC:
        rows = []
        for i in range(n + 1):
            rows.append([fmpq(math.comb(i, k), math.comb(n, k)) for k in range(i + 1)])
        _BC[n] = rows
    return _BC[n]


def bern_lower(a, h):
    """Lower bound (an exact arb point) for min_{0 <= s <= h} sum_k a_k s^k, a_k balls, h > 0 exact:
    the minimum of the Bernstein coefficients of t -> sum_k a_k h^k t^k on [0, 1]."""
    n = len(a) - 1
    b = []
    hk = arb(1)
    for k in range(n + 1):
        b.append(a[k] * hk)
        hk = hk * h
    M = _bern_matrix(n)
    best = None
    for i in range(n + 1):
        s = arb(0)
        row = M[i]
        for k in range(i + 1):
            s += b[k] * arb(row[k])
        lo = arb(s.lower())
        if best is None or lo < best:
            best = lo
    return best


def poly_lower_sym(a, r):
    """Lower bound on [-r, r] of sum_k a_k d^k: Bernstein on [0, r] and on [-r, 0] (via d -> -d)."""
    lp = bern_lower(a, r)
    am = [c if k % 2 == 0 else -c for k, c in enumerate(a)]
    lm = bern_lower(am, r)
    return lp if lp < lm else lm
