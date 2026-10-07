"""Validated K0(z), z*K1(z) (arb balls) for real z >= 1 by the trapezoid rule on DLMF 10.32.8 (s = v^2):
  K0(z) = e^{-z} (2z)^{-1/2} I0,  I0 = int_R e^{-v^2} (1+v^2/2z)^{-1/2} dv
  zK1(z) = (2z)^{1/2} e^{-z} I1,  I1 = int_R v^2 e^{-v^2} (1+v^2/2z)^{1/2} dv
Error bounds (all rigorous, evaluated in Arb):
 * discretisation (Trefethen-Weideman 2014, Thm 5.1): |I - h sum_Z f(kh)| <= 2 M_a/(e^{2 pi a/h} - 1), f analytic in
   |Im v| < sqrt(2z); on |Im v| = y <= a < sqrt(2z): |1+v^2/2z| >= 1 - a^2/2z, so
   M_a(f0) <= sqrt(pi) e^{a^2} (1-a^2/2z)^{-1/2},  M_a(f1) <= sqrt(pi) e^{a^2} [(1/2+a^2) + (3/4+a^2+a^4)/(4z)]
   (|v|^2 = x^2+y^2, |1+v^2/2z|^{1/2} <= 1+(x^2+y^2)/4z).
 * truncation |k| > n: f0(v) <= e^{-v^2};  f1(v) <= 3 e^{-v^2/2} for |v| >= 1, z >= 1 (v^2+v^4 <= 3e^{v^2/2}).
z may be a ball (bounds use its lower endpoint).  The precondition z >= 1 is checked with lib.common.require (no assert)."""
import math
from flint import arb, ctx
from lib.common import require


def k01_trap(z, B=None):
    P = ctx.prec
    B = B or P
    ctx.prec = P + 64
    za = z if isinstance(z, arb) else arb(z)
    zl = arb(za.lower())
    zf = float(zl)
    require(zf >= 1, 'k01_trap: needs z >= 1')
    L = (B + 30) * math.log(2)
    a = min(0.9 * math.sqrt(2 * zf), math.sqrt(L))
    h = 2 * math.pi * a / (L + a * a)
    n = int(math.sqrt(2 * (L + 10)) / h) + 2
    hh = arb(h)
    h2 = hh * hh
    inv2z = 1 / (2 * za)
    E = arb(1)
    q = (-h2).exp()
    q2 = q * q
    s0 = arb(1) / 2
    s1 = arb(0)
    for k in range(1, n + 1):
        E = E * q
        q = q * q2
        v2 = h2 * (k * k)
        y = 1 + v2 * inv2z
        r = y.rsqrt()
        s0 += E * r
        s1 += E * v2 * y * r
    T0 = 2 * hh * s0
    T1 = 2 * hh * s1
    aa = arb(a)
    sp = arb.pi().sqrt()
    ea = (aa * aa).exp()
    M0 = sp * ea / (1 - aa * aa / (2 * zl)).sqrt()
    M1 = sp * ea * ((arb(1) / 2 + aa * aa) + (arb(3) / 4 + aa * aa + aa ** 4) / (4 * zl))
    den = (2 * arb.pi() * aa / hh).exp() - 1
    d0 = 2 * M0 / den
    d1 = 2 * M1 / den
    n1 = arb(n + 1)
    t0 = 2 * hh * (-(n1 * n1) * h2).exp() / (1 - (-2 * n1 * h2).exp())
    t1 = 2 * hh * 3 * (-(n1 * n1) * h2 / 2).exp() / (1 - (-n1 * h2).exp())
    I0 = T0 + arb(0, (d0 + t0).upper())
    I1 = T1 + arb(0, (d1 + t1).upper())
    ez = (-za).exp()
    sq = (2 * za).sqrt()
    K0 = ez / sq * I0
    zK1 = sq * ez * I1
    ctx.prec = P
    return +K0, +zK1
