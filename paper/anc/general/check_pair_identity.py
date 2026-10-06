#!/usr/bin/env python3
"""Numerical consistency check (floating point, NOT part of any certificate) of the identity used by verify_pair.py:
    A_q(F) = int F mu dt + (1/pi) int F^ dnu
for the Herglotz pair of a parameter file and the Gaussian F(t) = exp(-pi t^2/sig^2), F^(xi) = sig exp(-pi sig^2 xi^2).

Usage (from anc/):   python3 general/check_pair_identity.py general/params/pair_gammaR2_X240.json SIGMA [DPS]

Dependencies: Python 3 standard library and mpmath.

The three quantities are computed independently:
  * A_q(F) = 2F(i/2) + (1/2pi) int F(t) [ sum_j (Re psi((1/2 + kappa_j)/2 + it/2) - log pi) + log q ] dt, directly;
  * (1/pi) int F^ dnu in the variable u = log x (where F^(u/2pi) = sig exp(-sig^2 u^2/(4 pi)) and dnu = e^{-u/2} dnu~):
    closed-form erf/erfc integrals for the Lebesgue part, the cells and the tails, and quadrature against the explicit
    Irwin-Hall density for the bumps (this side does NOT use the formula for mu);
  * int F mu dt with mu from the formula in verify_pair.py.
Atoms (bump half-width 0) contribute w_b e^{-u_b/2} F^(u_b/2pi) to the nu side; a centre "log2" is exactly log 2, and
the log-conductor may be a decimal string or "log(N)", as in verify_pair.py.
The printed residual A_q(F) - (int F mu + (1/pi) int F^ dnu) should be at the level of the working precision.
"""
import hashlib
import json
import os
import sys

import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
ANC = os.path.dirname(HERE)


def resolve(path):
    for cand in (path, os.path.join(ANC, path), os.path.join(HERE, path)):
        if os.path.isfile(cand):
            return os.path.abspath(cand)
    sys.exit('input file not found: %s' % path)


if len(sys.argv) not in (3, 4):
    sys.exit(__doc__)
pfile = resolve(sys.argv[1])
print('parameter file : %s' % os.path.relpath(pfile, ANC))
print('sha256         : %s' % hashlib.sha256(open(pfile, 'rb').read()).hexdigest())
mp.mp.dps = int(sys.argv[3]) if len(sys.argv) == 4 else 30
R = json.load(open(pfile))
LQ = mp.log(int(R['logq'][4:-1])) if str(R['logq']).startswith('log(') else mp.mpf(R['logq'])
sig = mp.mpf(sys.argv[2])
kaps = [mp.mpf(k) for k in R['gamma_shifts']]
EPS = mp.mpf(R['bump_halfwidth'])
KB = int(R['bump_order'])
w = [max(0.0, v) for v in R['w']]
f = [min(1.0, max(0.0, v)) for v in R['f']]
act = [j for j in range(len(w)) if w[j] > 0]
UB = [mp.log(2) if R['bump_centres'][j] == 'log2' else mp.mpf(R['bump_centres'][j]) for j in act]
MB = [mp.mpf(w[j]) * mp.exp(-UB[i] / 2) for i, j in enumerate(act)]
V = [mp.log(2)] + [mp.mpf(u) for u in R['edges'][1:]]
n = len(f)
Lx = V[-1]
Xa = mp.exp(Lx)
TA = [(mp.mpf(m), mp.mpf(max(0.0, a))) for m, a in zip(R['tail_powers'], R['tail_coeffs'])]
F = lambda t: mp.exp(-mp.pi * t * t / sig ** 2)
alpha = sig ** 2 / (4 * mp.pi)                       # F^(u/2pi) = sig exp(-alpha u^2)


def gint(a, b, beta):
    """int_a^b sig exp(-alpha u^2 + beta u) du (b may be +oo)."""
    sa = mp.sqrt(alpha)
    u0 = beta / (2 * alpha)
    pre = sig * mp.sqrt(mp.pi / alpha) / 2 * mp.exp(beta ** 2 / (4 * alpha))
    if b == mp.inf:
        return pre * mp.erfc(sa * (a - u0))          # erfc, not 1 - erf (avoids cancellation)
    return pre * (mp.erf(sa * (b - u0)) - mp.erf(sa * (a - u0)))


# nu side in u = log x: dx = e^u du and dnu = x^{-1/2} dnu~, so the Lebesgue part and the cells carry the weight
# e^{u/2} (beta = 1/2) and the tail term x^{-m} dx carries e^{(1/2 - m) u}
leb = gint(V[0], mp.inf, mp.mpf(1) / 2)
cells = sum(mp.mpf(f[i]) * gint(V[i], V[i + 1], mp.mpf(1) / 2) for i in range(n))
tails = sum(a * gint(Lx, mp.inf, mp.mpf(1) / 2 - m) for m, a in TA)


def irwin_hall(s, k):
    if s < 0 or s > k:
        return mp.mpf(0)
    return sum((-1) ** j * mp.binomial(k, j) * (s - j) ** (k - 1) for j in range(int(mp.floor(s)) + 1)) / mp.factorial(k - 1)


def bump_int(u0, m):
    """m * int F^((u0 + v)/2pi) phi(v) dv, phi = density of (eps/k)(2U - k), U ~ Irwin-Hall(k); for eps = 0 (an atom)
    this is m * F^(u0/2pi)."""
    if EPS == 0:
        return m * sig * mp.exp(-alpha * u0 ** 2)
    g = lambda v: sig * mp.exp(-alpha * (u0 + v) ** 2) * irwin_hall((v * KB / EPS + KB) / 2, KB) * KB / (2 * EPS)
    pts = [-EPS + 2 * EPS * j / KB for j in range(KB + 1)]
    return m * mp.quad(g, pts)


bumps = sum(bump_int(u, m) for u, m in zip(UB, MB))
nu_side = (leb - cells + bumps - tails) / mp.pi
C = [1 - mp.mpf(f[0])] + [mp.mpf(f[i - 1]) - mp.mpf(f[i]) for i in range(1, n)] + [mp.mpf(f[n - 1])]


def mu(t):
    rho = LQ + sum(mp.re(mp.digamma((mp.mpf(1) / 2 + k) / 2 + 1j * t / 2)) - mp.log(mp.pi) for k in kaps)
    val = rho / (2 * mp.pi)
    den = mp.mpf(1) / 4 + t * t
    val += sum(c * mp.exp(v / 2) * (mp.cos(t * v) / 2 + t * mp.sin(t * v)) for c, v in zip(C, V)) / den / mp.pi
    y = EPS * t / KB
    S = (mp.sin(y) / y) ** KB if y != 0 else mp.mpf(1)
    val -= S * sum(m * mp.cos(t * u) for u, m in zip(UB, MB)) / mp.pi
    for m, a in TA:
        h = m - mp.mpf(1) / 2
        val += a * Xa ** (mp.mpf(1) / 2 - m) / mp.pi * (h * mp.cos(t * Lx) - t * mp.sin(t * Lx)) / (h * h + t * t)
    return val


Tm = 12 * sig
mu_side = 2 * mp.quad(lambda t: F(t) * mu(t), [Tm * j / 120 for j in range(121)])
arch = 2 * mp.quad(lambda t: F(t) * (sum(mp.re(mp.digamma((mp.mpf(1) / 2 + k) / 2 + 1j * t / 2)) - mp.log(mp.pi)
                                         for k in kaps) + LQ), [Tm * j / 24 for j in range(25)]) / (2 * mp.pi)
Aq = 2 * mp.exp(mp.pi / (4 * sig ** 2)) * mp.mpf(R['pole_residue']) + arch     # 2F(i/2) = 2 exp(pi/(4 sig^2))
print('sigma = %s, %d digits, log q = %s' % (sig, mp.mp.dps, R['logq']))
print('A_q(F)            = %s' % mp.nstr(Aq, 22))
print('int F mu          = %s' % mp.nstr(mu_side, 22))
print('(1/pi) int F^ dnu = %s' % mp.nstr(nu_side, 22))
print('   parts: Lebesgue %s, cells %s, bumps %s, tails %s' % (mp.nstr(leb / mp.pi, 12), mp.nstr(-cells / mp.pi, 12),
                                                            mp.nstr(bumps / mp.pi, 12), mp.nstr(-tails / mp.pi, 12)))
print('residual A_q(F) - (int F mu + (1/pi) int F^ dnu) = %s' % mp.nstr(Aq - mu_side - nu_side, 5))
