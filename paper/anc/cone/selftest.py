"""Self-tests of the cone/ certificates (not certificates; mpmath is used only here).

 1. K backends: lib/k01_trapezoid (trapezoid rule) and lib/besselk (series/asymptotic) overlap at many z, and agree with
    mpmath besselk to the printed accuracy.
 2. Abel preimage: Q for P = 1 is y^4 - 8y^3 + 14y^2 - 4y (hand computation); abel_Q (Horner recursion g_i = i f_i - f_{i-1})
    agrees on the J = 10 ball with an independent construction through Stirling numbers of the second kind
    (e^y theta^i e^{-y} = sum_k S(i,k) (-y)^k); Taylor shift agrees with direct evaluation.
 3. Lemma 4.6 numerically: G_0(z) from the operator form equals int_z^oo Q(y) e^{-y} (y^2 - z^2)^{-1/2} dy (mpmath quad).
 4. Two routes to Fhat_J: the operator form for P_J agrees with sum_k p_k m_k(xi) built from the P = 1 moments.
 5. Bernstein lower bounds are below dense samples of random polynomials.
Usage: python cone/selftest.py
"""
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import conelib as L                                                  # noqa: E402
from flint import arb, ctx, arb_poly                                 # noqa: E402
from lib.bessel_form import FhatOperators, horner                   # noqa: E402
import mpmath as mpm                                                 # noqa: E402

D = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ok_all = True


def check(name, cond):
    global ok_all
    ok_all = ok_all and bool(cond)
    print('%-80s %s' % (name, 'OK' if cond else 'FAIL'), flush=True)


# 1. K backends
ctx.prec = 400
mpm.mp.prec = 400
good = True
for zs in ['1', '1.5', '6.283', '12.57', '40', '100.5', '400', '1250', '2934', '6000']:
    z = arb(zs)
    a0, a1 = L.K01_trap(z, 400)
    b0, b1 = L.K01_series(z, 400)
    m0 = mpm.besselk(0, mpm.mpf(zs)); m1 = mpm.besselk(1, mpm.mpf(zs))
    ok = a0.overlaps(b0) and a1.overlaps(b1)
    rel = max(float(abs((a0 - b0) / b0).upper()), float(abs((a1 - b1) / b1).upper()))
    relm = max(abs(float((a0.mid() - arb(str(m0))) / arb(str(m0)))), abs(float((a1.mid() - arb(str(m1))) / arb(str(m1)))))
    good = good and ok and rel < 1e-100 and relm < 1e-100
    print('   z = %-6s  trap vs series overlap %s, rel diff < %.1e, vs mpmath %.1e' % (zs, ok, rel, relm))
check('1. K_0, K_1: trapezoid rule and series/asymptotic overlap, agree to 1e-100', good)

# 2. Abel preimage
Q1 = L.abel_Q([arb(1)], 200)
check('2a. Q for P = 1 equals y^4 - 8y^3 + 14y^2 - 4y', [int(c.mid().unique_fmpz()) for c in Q1] == [0, -4, 14, -8, 1]
      and all(c.rad() == 0 for c in Q1))
P10 = L.load_pball(os.path.join(D, 'exact/out/P10_ball.txt'), 800)
Q = L.abel_Q(P10, 800)
ctx.prec = 800
R = L.theta_poly(P10, 800)                       # R(theta) = P(-(theta+1/2)^2) theta^2 (theta+1)^2
nR = len(R) - 1
S2 = [[1]]                                       # Stirling numbers of the second kind S(i, k), exact integers
for i in range(1, nR + 1):
    row = [0] * (i + 1)
    for k in range(1, i + 1):
        row[k] = k * (S2[i - 1][k] if k < i else 0) + S2[i - 1][k - 1]
    S2.append(row)
Q2 = [sum((R[i] * S2[i][k] for i in range(k, nR + 1)), arb(0)) * (-1) ** k for k in range(nR + 1)]
while Q2 and Q2[-1].is_zero():
    Q2.pop()
check('2b. abel_Q(P_10) overlaps the Stirling-number construction of Q coefficientwise',
      len(Q) == len(Q2) and all(u.overlaps(v) for u, v in zip(Q, Q2)))
ctx.prec = 800
y0 = arb('103.3')
T = L.taylor_shift(Q, y0)
v = arb('0.7')
lhs = sum((T[k] * v ** k for k in range(len(T))), arb(0))
rhs = sum((Q[k] * (y0 + v) ** k for k in range(len(Q))), arb(0))
check('2c. Taylor shift: sum T_k v^k = Q(y0 + v)', lhs.overlaps(rhs))

# 3. Lemma 4.6 numerically for J = 10
ctx.prec = 300
mpm.mp.dps = 60
FO = FhatOperators([arb(c.mid()) for c in P10], 0, 300)
Qm = [mpm.mpf(c.mid().str(60, radius=False)) for c in L.abel_Q([arb(c.mid()) for c in P10], 300)]
good = True
for zs in ['15', '60', '110']:
    z = arb(zs)
    K0, K1 = L.K01_series(z, 300)
    Aa, Ba = FO.coef[0]
    G0 = horner(Aa, z) * K0 + horner(Ba, z) * K1
    zz = mpm.mpf(zs)
    # y = z + s^2: dy/sqrt(y^2 - z^2) = 2 ds/sqrt(2z + s^2) (removes the endpoint singularity)
    g = lambda s: mpm.polyval(Qm[::-1], zz + s * s) * mpm.e ** (-(zz + s * s)) * 2 / mpm.sqrt(2 * zz + s * s)
    I = mpm.quad(g, [0, 1, 4, 10, 30])
    rel = abs((mpm.mpf(G0.mid().str(50, radius=False)) - I) / I)
    good = good and rel < 1e-30
    print('   z = %-4s  G_0 operator form %s ; quad %s ; rel %.1e' % (zs, G0.str(15), mpm.nstr(I, 15), float(rel)))
check('3. Lemma 4.6 (Abel form) agrees with the operator form to 1e-30 (J = 10, three z)', good)

# 4. two routes to Fhat_J
ctx.prec = 800
E = L.Fhat(P10, 2, 800)
FO1 = FhatOperators([arb(1)], 2 * 20 + 2, 800)
E1 = L.Fhat([arb(1)], 2 * 20 + 2, 800)
good = True
PI = arb.pi()
for xs in ['2.5', '7.5', '15.5', '30']:
    xi = arb(xs).log() / (2 * PI)
    d, _ = E.derivs(xi, [0, 1])
    m, _ = E1.derivs(xi, list(range(2 * 20 + 2)), mchk=[0])
    s0 = sum((P10[k] * (-1) ** k * (2 * PI) ** (-2 * k) * m[2 * k] for k in range(21)), arb(0))
    s1 = sum((P10[k] * (-1) ** k * (2 * PI) ** (-2 * k) * m[2 * k + 1] for k in range(21)), arb(0))
    ok = d[0].overlaps(s0) and d[1].overlaps(s1)
    good = good and ok
    print('   x = %-5s operator form %s ; moment form %s ; overlap %s' % (xs, d[0].str(12), s0.str(12), ok))
check('4. Fhat_J, Fhat_J\': operator form overlaps sum_k p_k m_k (J = 10)', good)

# 5. Bernstein lower bounds (samples evaluated in ball arithmetic at exact points)
random.seed(1)
ctx.prec = 200
good = True
for trial in range(200):
    n = random.randint(2, 30)
    a = [arb(random.uniform(-1, 1)) for _ in range(n + 1)]
    h = arb(random.uniform(0.1, 2))
    lb = L.bern_lower(a, h)
    lbs = L.poly_lower_sym(a, h)
    for j in range(201):
        s_ = h * j / 200
        vp = sum((a[k] * s_ ** k for k in range(n + 1)), arb(0))
        vm = sum((a[k] * (-s_) ** k for k in range(n + 1)), arb(0))
        if vp < lb or vp < lbs or vm < lbs:          # a certified violation (ball strictly below the bound)
            good = False
check('5. Bernstein lower bounds <= samples (200 random polynomials, 201 exact points each)', good)
print('ALL SELF-TESTS PASSED' if ok_all else 'SOME SELF-TEST FAILED')
sys.exit(0 if ok_all else 1)
