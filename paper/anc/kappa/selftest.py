"""Validation of the ingredients of verify_kappa.py and verify_exact_member.py (a sanity check, not a certificate).

 (a) The K_0, K_1 enclosures of lib/besselk.py contain mpmath's values (computed independently at 600 digits) at
     points z in [0.05, 3000], with small relative radius.
 (b) Bessel form versus direct integration: Fhat_H(0) = int Xi(t)^2 H(t) dt, the integral by Arb's acb.integral
     (Xi from Arb's zeta and gamma) on [-T, T]; here H = 1 and H(t) = 1 + r t^2 + s t^4.
 (c) Normalisation of the explicit formula used in verify_kappa.py (F = Xi^2 H vanishes at every nontrivial zero):
         archimedean side  A = 2F(i/2) + (1/2pi) int F(t)[Re psi(1/4 + it/2) - log pi] dt
         prime side        A = (1/pi) sum_{n >= 2} Lambda(n) n^{-1/2} Fhat_H(log n/2pi)   (Bessel form)
     must agree.  The tails |t| > T (Xi^2 decays like e^{-pi |t|/2}) are not included; T = 100 makes them negligible
     at the printed accuracy.
 (d) Derivatives of the operator form against central finite differences of the operator form itself.
Usage (from anc/): python kappa/selftest.py
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import mpmath  # noqa: E402
from flint import arb, acb, fmpq, ctx  # noqa: E402
from lib.besselk import K01  # noqa: E402
from lib.bessel_form import build_P, FhatOperators, Evaluator  # noqa: E402
from lib.common import prime_powers  # noqa: E402

t0 = time.time()
ok_all = True

# (a)
mpmath.mp.dps = 600
P = 1000
worst = -10 ** 9
for zs in ['0.05', '0.7', '3', '6.283185307179586', '20', '62.83', '150', '400', '700', '1100', '2400', '3000']:
    ctx.prec = P + 100
    K0, K1 = K01(arb(zs), P)
    k0 = mpmath.besselk(0, mpmath.mpf(zs))
    k1 = mpmath.besselk(1, mpmath.mpf(zs))
    in0 = K0.contains(arb(mpmath.nstr(k0, 590)))
    in1 = K1.contains(arb(mpmath.nstr(k1, 590)))
    rr = max(float((K0.rad() / abs(K0.mid())).mid().log()), float((K1.rad() / abs(K1.mid())).mid().log())) / 2.302585
    worst = max(worst, rr)
    ok_all = ok_all and in0 and in1
    print('(a) z = %-18s K_0, K_1 contain mpmath values: %s %s; log10 relative radius %.0f' % (zs, in0, in1, rr))
print('(a) worst log10 relative radius at P = %d bits: %.0f' % (P, worst), flush=True)

# (b), (c)
ctx.prec = 200
PI = arb.pi()
T = 100


def Xi(z):
    s = acb(arb(1) / 2) + acb(0, 1) * z
    return s * (s - 1) / 2 * acb(PI) ** (-s / 2) * (s / 2).gamma() * s.zeta()


for label, rs in (('H = 1', []), ('H = 1 + r t^2 + s t^4, r = 0.0169..., s = 0.000498...',
                                  [(fmpq(1692837645520772493388279, 10 ** 26), fmpq(4981149325826939398317563, 10 ** 28))])):
    ctx.prec = 200
    Pp = build_P(rs, 300)
    pc = [acb(c) for c in Pp.coeffs()]

    def F(z):
        u = z * z
        h = acb(0)
        for c in reversed(pc):
            h = h * u + c
        x = Xi(z)
        return x * x * h

    tol = dict(rel_tol=arb(2) ** -150, abs_tol=arb(10) ** -45, eval_limit=10 ** 7)
    I1 = acb.integral(lambda z, a: F(z), 0, T, **tol)
    I2 = acb.integral(lambda z, a: F(z) * ((acb(arb(1) / 4) + acb(0, 1) * z / 2).digamma()
                                         + (acb(arb(1) / 4) - acb(0, 1) * z / 2).digamma()) / 2, 0, T, **tol)
    Pm = arb(0)
    for c in reversed(Pp.coeffs()):
        Pm = Pm * arb(-0.25) + c                    # H(i/2) = P(-1/4); Xi(i/2) = xi(0) = 1/2
    intF = 2 * I1.real
    A_arch = 2 * Pm / 4 + (2 * I2.real - PI.log() * intF) / (2 * PI)
    FO = FhatOperators(Pp.coeffs(), 3, 200)
    EV = Evaluator(FO, 200, -60)
    ctx.prec = 200
    F0 = EV.derivs(arb(0), [0])[0]
    Ap = arb(0)
    for n, p in prime_powers(200):
        Ap += arb(p).log() / arb(n).sqrt() * EV.derivs(arb(n).log() / (2 * PI), [0])[0]
    Ap = Ap / PI
    db = abs(intF - F0)
    dc = abs(A_arch - Ap)
    okb = db < arb(10) ** -40
    okc = dc < arb(10) ** -40
    ok_all = ok_all and okb and okc
    print('(b) %s: int F (quadrature) = %s;  Fhat_H(0) (Bessel form) = %s;  |difference| <= %s  [%s]'
          % (label, intF.str(30), F0.str(30), arb(db.upper()).str(2, radius=False), 'agree' if okb else 'DISAGREE'))
    print('(c) %s: A archimedean = %s;  A prime side = %s;  |difference| <= %s  [%s]'
          % (label, A_arch.str(30), Ap.str(30), arb(dc.upper()).str(2, radius=False), 'agree' if okc else 'DISAGREE'))
    if rs:
        print('    kappa for this one-factor H: A/Fhat(0) = %s' % (Ap / F0).str(20), flush=True)
    # (d) derivatives vs finite differences (of the operator form itself) at xi = 0.3
    xi0 = arb('0.3')
    hh = arb(10) ** -20
    d = EV.derivs(xi0, [0, 1, 2])
    fp = EV.derivs(xi0 + hh, [0, 1])
    fm = EV.derivs(xi0 - hh, [0, 1])
    e1 = abs((fp[0] - fm[0]) / (2 * hh) - d[1]) / abs(d[1])
    e2 = abs((fp[1] - fm[1]) / (2 * hh) - d[2]) / abs(d[2])
    okd = e1 < arb(10) ** -30 and e2 < arb(10) ** -30
    ok_all = ok_all and okd
    print('(d) %s: relative finite-difference mismatch of Fhat\', Fhat\'\' at xi = 0.3: %s, %s  [%s]'
          % (label, arb(e1.upper()).str(2, radius=False), arb(e2.upper()).str(2, radius=False), 'agree' if okd else 'DISAGREE'),
          flush=True)
print('SELFTEST PASSED: %s   (%.0f s)' % (ok_all, time.time() - t0))
sys.exit(0 if ok_all else 1)
