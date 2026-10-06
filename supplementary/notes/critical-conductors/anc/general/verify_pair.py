#!/usr/bin/env python3
"""Verify that an explicit Herglotz-form pair (mu, nu) is admissible for Gamma-data prod_j Gamma_R(s + kappa_j),
one pole, conductor q (e.g. Gamma_R(s)^2 at log q = 1.6093347792651136, so q_min(Gamma_R^2) <= q).

Usage (from anc/):   python3 general/verify_pair.py general/params/pair_gammaR2_X240.json [--gap-x N]

Dependencies: Python 3 standard library, python-flint (Arb), nothing else.

The pair.  On x >= 1 let (all numbers from the parameter file, binary64 values used exactly; v_0 := log 2 exactly)
    nu~ = 1_[2,oo)(x) dx - sum_{i<n} f_i 1_[e^{v_i}, e^{v_{i+1}}](x) dx + sum_b (bump_b) - sum_m a_m x^{-m} 1_(X,oo)(x) dx,
with 0 <= f_i <= 1, edges v_0 < ... < v_n, X = e^{v_n}, and bump_b = w_b x^{1/2} e^{-u_b/2} phi(log x - u_b) d(log x),
w_b >= 0, where phi is the density of (eps/k)(2U - k), U ~ Irwin-Hall(k) (a sum of k uniform variables on [0, 1]);
phi is supported on [-eps, eps] and its Fourier transform is S(t) = sinc(eps t/k)^k.  Half-width eps = 0 means point
masses (atoms) w_b delta at x = e^{u_b}, with S = 1.  A bump centre given as the string "log2" is exactly log 2; the
log-conductor may be a decimal string or "log(N)" for an exact integer N.  The prime-side measure nu is
x^{-1/2} nu~ pushed to xi = log x/(2 pi); it is >= 0 and supported on [xi_2, oo), xi_2 = log 2/(2 pi), provided
    nu~ >= 0:  f_i in [0, 1], w_b >= 0, and 1 - sum_m a_m x^{-m} >= 0 on (X, oo) (it is increasing, so x = X suffices);
    support:   u_b - eps >= log 2 for every bump.
G(s) = int x^{-s} d nu~ has in 1/2 <= Re s <= 1 + delta only the simple pole of the Lebesgue part 2^{1-s}/(s - 1) at
s = 1, with residue 1 (= the pole order of the data): cells and bumps give entire functions, the tail m gives a pole at
s = 1 - m <= 0 only.  Moving the line of integration in F^(log x/2pi) = x^{-y} int F(t - iy) x^{-it} dt past s = 1 gives
(1/pi) int F^ dnu = 2F(i/2) + (1/pi) int F(t) Re G(1/2 + it) dt, hence for every F in the test class
    A_q(F) = int F mu dt + (1/pi) int F^ dnu,    mu(t) = rho_q(t) - (1/pi) Re G(1/2 + it),
    rho_q(t) = (1/2pi) [ log q + sum_j ( Re psi((1/2 + kappa_j)/2 + it/2) - log pi ) ],
    -(1/pi) Re G(1/2+it) = (1/pi) sum_{j=0}^{n} C_j e^{v_j/2} E(t, v_j) - (S(t)/pi) sum_b m_b cos(t u_b)
                           + sum_m (a_m/pi) X^{1/2-m} T_m(t),
    E(t, v) = Re[e^{itv}/(1/2 + it)] = (cos(tv)/2 + t sin(tv))/(1/4 + t^2),
    T_m(t)  = Re[e^{-itL}/(m - 1/2 + it)] = ((m - 1/2) cos(tL) - t sin(tL))/((m - 1/2)^2 + t^2),   L = log X,
    C_0 = 1 - f_0, C_j = f_{j-1} - f_j (0 < j < n), C_n = f_{n-1},  m_b = w_b e^{-u_b/2}.
The pair is admissible iff mu >= 0 (mu is even, so t >= 0 suffices).  This is checked rigorously:
  * on [0, T] by mean-value steps: mu(t) >= mu(t0) - (h + d) sup |mu'| on [t0 - d, t0 + h + d] (d = pad), where mu' is
    enclosed on the whole step by Arb ball arithmetic (psi' = Hurwitz zeta(2, .)); the step h is halved until this bound
    exceeds accept_fraction * mu(t0) (default 0, i.e. until it is positive), and doubled again afterwards up to hmax;
  * on [T, oo): rho_q is increasing (d/dt Re psi(w + it/2) > 0 for real w > 0; every shift kappa >= 0 is checked), while |E(t, v)| <= (1/4 + t^2)^{-1/2},
    |S(t)| <= min(1, (k/(eps t))^k) and |T_m(t)| <= ((m - 1/2)^2 + t^2)^{-1/2} are decreasing; so
    mu(t) >= rho_q(T) - [majorants at T] for t >= T.
Start of the support.  The density of the absolutely continuous part of nu~ is 1 - f_i on the i-th cell and
1 - sum_m a_m x^-m > 0 beyond X, and an active bump b is supported on [e^{u_b - eps}, e^{u_b + eps}].  So nu~ has no mass
below x0 = min(e^{v_i} for the first cell with f_i < 1 (X if there is none), e^{u_b - eps} over the active bumps).  The
script computes an exact rational lower bound for x0 (e^{log 2} = 2 exactly; Arb lower endpoints otherwise; the f_i are
compared with 1 exactly) and prints it rounded down.  With --gap-x N it also requires x0 >= N: then the prime measure
of the pair lives on [xi_N, oo), xi_N = log N/(2 pi), i.e. the pair is admissible for the data with the gap xi_N.
Read-off: an admissible pair exists at log q, so kappa*(data with log q) >= inf mu > 0, i.e. q_min = e^{-2 pi kappa*_0} <= q.
The certified lower bound for mu on R (minimum of the step bounds and of the tail bound) is printed and recorded.
A machine-readable summary (no timings) is written to general/results/<name>.json.
"""
import hashlib
import json
import os
import sys
import time
from fractions import Fraction

from flint import arb, acb, ctx


sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from lib.common import require, check_decimal  # noqa: E402  (explicit checks; exact check of every printed decimal)

HERE = os.path.dirname(os.path.abspath(__file__))
ANC = os.path.dirname(HERE)


def resolve(path):
    for cand in (path, os.path.join(ANC, path), os.path.join(HERE, path)):
        if os.path.isfile(cand):
            return os.path.abspath(cand)
    sys.exit('input file not found: %s' % path)


def sha256(p):
    with open(p, 'rb') as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def exact(a):
    m, e = a.man_exp()
    return Fraction(int(m)) * Fraction(2) ** int(e)


def dec(q, n, up):
    """Decimal string with n significant digits of the Fraction q, rounded toward +oo (up) or -oo (not up), with an
    exact a-posteriori check of the direction (lib/common.py)."""
    return check_decimal(_dec(q, n, up), q, up)


def _dec(q, n, up):
    """Decimal string with n significant digits of the Fraction q, rounded toward +oo (up) or -oo (not up)."""
    if q == 0:
        return '0'
    neg = q < 0
    a = -q if neg else q
    E = len(str(a.numerator)) - len(str(a.denominator))
    while Fraction(10) ** E > a:
        E -= 1
    while Fraction(10) ** (E + 1) <= a:
        E += 1
    k = a / Fraction(10) ** (E - n + 1)
    K = -((-k.numerator) // k.denominator) if (not neg) == up else k.numerator // k.denominator
    digits = str(K)
    if len(digits) > n:
        E += 1
        digits = digits[:n]
    sgn = '-' if neg else ''
    if -5 < E < 5:
        d = n - 1 - E
        if d <= 0:
            return sgn + digits + '0' * (-d)
        z = digits.rjust(d + 1, '0')
        return sgn + z[:-d] + '.' + z[-d:]
    return sgn + digits[0] + ('.' + digits[1:] if n > 1 else '') + 'e' + str(E)


ARGS = sys.argv[1:]
GAP_X = None
if '--gap-x' in ARGS:
    i = ARGS.index('--gap-x')
    if i + 1 >= len(ARGS):
        sys.exit(__doc__)
    GAP_X = ARGS[i + 1]                              # an exact decimal or integer N; the gap is xi_N = log N/(2 pi)
    del ARGS[i:i + 2]
if len(ARGS) != 1:
    sys.exit(__doc__)
pfile = resolve(ARGS[0])
R = json.load(open(pfile))
name = os.path.splitext(os.path.basename(pfile))[0]
print('parameter file : %s' % os.path.relpath(pfile, ANC))
print('sha256         : %s' % sha256(pfile))
require(R['object'] == 'herglotz_pair' and float(R['pole_residue']) == 1.0, 'not a Herglotz-pair file with pole residue 1')
num = R['numerics']
ctx.prec = int(num['prec_bits'])
if str(R['logq']).startswith('log('):                 # exact log N
    LQ = arb(int(R['logq'][4:-1])).log()
else:
    LQ = arb(R['logq'])                               # encloses the exact decimal log q
T = int(num['T'])
PI = arb.pi()
L2 = arb(2).log()
kaps = [arb(str(k)) for k in R['gamma_shifts']]
require(all(Fraction(str(k)) >= 0 for k in R['gamma_shifts']),
        'Gamma shifts must be >= 0: the digamma arguments w = (1/2 + kappa)/2 must be positive (monotone tail of rho_q)')
EPS = arb(str(R['bump_halfwidth']))
KB = int(R['bump_order'])
w = [max(0.0, v) for v in R['w']]
f = [min(1.0, max(0.0, v)) for v in R['f']]
require(w == R['w'] and f == R['f'], 'weights outside their admissible ranges')
act = [j for j in range(len(w)) if w[j] > 0]
UB = [L2 if R['bump_centres'][j] == 'log2' else arb(R['bump_centres'][j]) for j in act]
MB = [arb(w[j]) * (-UB[i] / 2).exp() for i, j in enumerate(act)]
V = [L2] + [arb(u) for u in R['edges'][1:]]           # v_0 = log 2 exactly
n = len(f)
require(len(V) == n + 1, 'check failed: len(V) == n + 1')
C = [1 - arb(f[0])] + [arb(f[i - 1]) - arb(f[i]) for i in range(1, n)] + [arb(f[n - 1])]
EV = [(v / 2).exp() for v in V]
Lx = V[-1]
Xa = Lx.exp()
require(len(R['tail_powers']) == len(R['tail_coeffs']), 'tail powers and coefficients differ in number')
require(all(Fraction(str(m)) > Fraction(1, 2) for m in R['tail_powers']),
        'tail exponents must satisfy m > 1/2 (finite integral of x^(-1/2) against the tail measure)')
TA = [(arb(m), arb(max(0.0, a))) for m, a in zip(R['tail_powers'], R['tail_coeffs'])]
require(all(a >= 0 for a in R['tail_coeffs']), 'tail coefficients must be >= 0')

# ---- nu~ >= 0 and support in [log 2, oo)
require(all(0 <= x <= 1 for x in f) and all(x >= 0 for x in w), 'need f in [0, 1] and w >= 0')
require(all(bool(V[i + 1] > V[i]) for i in range(n)), 'edges not increasing')
exact_l2 = [R['bump_centres'][j] == 'log2' for j in act]
require(all(EPS == 0 for e in exact_l2 if e), 'only atoms (half-width 0) may sit at exactly log 2')
require(all(bool(u - EPS >= L2) for u, e in zip(UB, exact_l2) if not e), 'bump support below log 2')
tail_density_at_X = sum((a / Xa ** m for m, a in TA), arb(0))
require(bool(tail_density_at_X < 1), 'tail density negative at X')
print('pair           : Gamma_R shifts %s, log q = %s; %d cells, %d bumps (half-width %s, order %d), tails %s, X = e^{v_n} = %s'
      % (R['gamma_shifts'], R['logq'], n, len(UB), R['bump_halfwidth'], KB,
         list(zip(R['tail_powers'], R['tail_coeffs'])), Xa.str(12)))
print('nu~ >= 0       : f in [0,1], w >= 0, bump supports in [log 2, oo), sum_m a_m X^-m = %s < 1: True'
      % tail_density_at_X.str(5))
# ---- start of supp nu~: exact rational lower bound x0 (see the docstring)
def exp_lower(v):
    return exact(v.exp().lower())


i_first = next((i for i in range(n) if Fraction(R['f'][i]) < 1), None)     # binary64 values compared with 1 exactly
starts = [exp_lower(Lx) if i_first is None else (Fraction(2) if i_first == 0 else exp_lower(V[i_first]))]
starts += [Fraction(2) if e else exp_lower(u - EPS) for u, e in zip(UB, exact_l2)]   # 'log2' centres are atoms at 2
x0 = min(starts)
print('nu~ support    : supp nu~ in [x0, oo) with x0 >= %s' % dec(x0, 7, False))
sys.stdout.flush()


def S(t):
    """S(t) = sinc(eps t/k)^k; near y = 0 use |sinc y - 1| <= y^2/6."""
    y = EPS * t / KB
    if y.contains(0):
        s = 1 + arb(0, (y * y / 6).upper())
        return s ** KB
    return (y.sin() / y) ** KB


def dS(t):
    """S'(t) = eps sinc^{k-1}(y) sinc'(y), y = eps t/k; near 0 use |sinc'(y)| <= |y|/3."""
    y = EPS * t / KB
    if y.contains(0) or abs(y).upper() < 1e-3:
        sc = 1 + arb(0, (y * y / 6).upper())
        dsc = arb(0, (abs(y) / 3).upper())
    else:
        sc = y.sin() / y
        dsc = (y * y.cos() - y.sin()) / (y * y)
    return EPS * sc ** (KB - 1) * dsc


def mu(t):
    rho = LQ
    for k in kaps:
        rho += acb((arb(1) / 2 + k) / 2, t / 2).digamma().real - PI.log()
    val = rho / (2 * PI)
    den = arb(1) / 4 + t * t
    acc = arb(0)
    for v, e, c in zip(V, EV, C):
        sn, cs = (t * v).sin_cos()
        acc += c * e * (cs / 2 + t * sn)
    val += acc / den / PI
    sb = arb(0)
    for u, m in zip(UB, MB):
        sb += m * (t * u).cos()
    val -= S(t) * sb / PI
    sn, cs = (t * Lx).sin_cos()
    for m, a in TA:
        h = m - arb(1) / 2
        val += a * Xa ** (arb(1) / 2 - m) / PI * (h * cs - t * sn) / (h * h + t * t)
    return val


def dmu(t):
    d = arb(0)
    for k in kaps:                                    # rho' = (1/2pi) sum_j -Im psi'(w_j + it/2)/2
        wq = acb((arb(1) / 2 + k) / 2, t / 2)
        d += -acb(2).zeta(wq).imag / 2               # psi'(w) = Hurwitz zeta(2, w)
    d = d / (2 * PI)
    den = arb(1) / 4 + t * t
    acc = arb(0)
    for v, e, c in zip(V, EV, C):
        sn, cs = (t * v).sin_cos()
        num_ = cs / 2 + t * sn
        dnum = -v * sn / 2 + sn + t * v * cs
        acc += c * e * (dnum * den - 2 * t * num_)
    d += acc / (den * den) / PI
    sb = arb(0)
    dsb = arb(0)
    for u, m in zip(UB, MB):
        sn, cs = (t * u).sin_cos()
        sb += m * cs
        dsb += -m * u * sn
    d -= (dS(t) * sb + S(t) * dsb) / PI
    sn, cs = (t * Lx).sin_cos()
    for m, a in TA:
        h = m - arb(1) / 2
        num_ = h * cs - t * sn
        dnum = -h * Lx * sn - sn - t * Lx * cs
        dd = h * h + t * t
        d += a * Xa ** (arb(1) / 2 - m) / PI * (dnum * dd - 2 * t * num_) / (dd * dd)
    return d


t0 = time.time()
t = arb(0)
steps = 0
minlb, minlb_lo = None, None                         # step bound with the smallest lower endpoint, and that endpoint
h = arb(num['h0'])
HMAX, HMIN, PAD = arb(num['hmax']), arb(num['hmin']), arb(num['pad'])
ACC = arb(num.get('accept_fraction', '0'))   # a step is accepted when its bound exceeds ACC * mu(t0) (0: any positive)
while t < T:
    t = arb(t.mid())
    m0 = mu(t)
    if not m0 > 0:
        print('FAIL: mu(t0) <= 0 at t0 =', t.str(10), m0.str(5))
        sys.exit(1)
    while True:
        ball = t + h / 2 + arb(0, (h / 2 + PAD).upper())     # contains [t - pad, t + h + pad]
        Dm = abs(dmu(ball)).upper()
        lb = m0 - (h + PAD) * arb(Dm)
        if lb > ACC * m0:
            break
        h = h / 2
        if h < HMIN:
            print('FAIL: step underflow at t =', t.str(10))
            sys.exit(1)
    steps += 1
    lb_lo = exact(lb.lower())                        # exact rational: compare lower endpoints exactly
    if minlb is None or lb_lo < minlb_lo:
        minlb, minlb_lo = lb, lb_lo
    t = arb(t.mid()) + h
    h = h * 2 if h < HMAX else h
    if steps % 5000 == 0:
        print('  t = %.3f, steps = %d, min lower bound so far %s (%.0f s)' % (float(t.mid()), steps, minlb.str(3),
                                                                           time.time() - t0))
        sys.stdout.flush()
# ---- tail t >= T
TT = arb(T)
rhoT = LQ
for k in kaps:
    rhoT += acb((arb(1) / 2 + k) / 2, TT / 2).digamma().real - PI.log()
rhoT = rhoT / (2 * PI)
WT = 1 / (arb(1) / 4 + TT * TT).sqrt()
cells = sum((abs(c) * e for c, e in zip(C, EV)), arb(0)) * WT / PI
Ssup = (arb(KB) / (EPS * TT)) ** KB if EPS > 0 else arb(1)        # atoms (eps = 0): |S| = 1
bumps = sum(MB, arb(0)) * (Ssup if Ssup < 1 else arb(1)) / PI
tails = sum((a * Xa ** (arb(1) / 2 - m) / ((m - arb(1) / 2) ** 2 + TT * TT).sqrt() / PI for m, a in TA), arb(0))
tail = rhoT - cells - bumps - tails
ok = bool(minlb > 0 and tail > 0)
q = LQ.exp()
print('steps on [0, %d]: %d mean-value steps; min lower bound for mu = %s (>= %s)'
      % (T, steps, minlb.str(5), dec(minlb_lo, 5, False)))
print('tail t >= %d   : mu(t) >= %s (>= %s)' % (T, tail.str(8), dec(exact(tail.lower()), 6, False)))
mu_floor = min(minlb_lo, exact(tail.lower()))  # mu(t) >= mu_floor for every real t (mu is even)
print('MU FLOOR       : mu(t) >= %s for all real t' % dec(mu_floor, 6, False))
print('ADMISSIBLE     : %s  (mu > 0 on R, nu >= 0 on [xi_2, oo))' % ok)
if GAP_X is not None:
    gap_ok = bool(ok and x0 >= Fraction(GAP_X))
    print('GAP            : admissible at gap xi_%s (prime measure on [%s, oo)): %s' % (GAP_X, GAP_X, gap_ok))
if ok:
    print('CONDUCTOR      : admissible at log q = %s, q = %s; hence q_min(data) <= %s'
          % (R['logq'], q.str(15), dec(exact(q.upper()), 8, True)))
else:
    print('CONDUCTOR      : no conclusion (admissibility not certified)')
checks = {}
for key, val, what in (('mu_steps_ge', exact(minlb.lower()), 'mu >= %s on [0, %d]'), ('mu_tail_ge', exact(tail.lower()), 'mu >= %s on [%d, oo)')):
    if key in R.get('claims', {}):
        v = ok and val >= Fraction(R['claims'][key])
        checks[key] = bool(v)
        print('CLAIM          : ' + what % (R['claims'][key], T) + ' ... ' + ('implied' if v else 'NOT IMPLIED'))
if 'conductor_upper_le' in R.get('claims', {}):
    c = Fraction(R['claims']['conductor_upper_le'])
    v = ok and exact(q.upper()) <= c
    checks['conductor_upper_le'] = bool(v)
    print('CLAIM          : q_min <= %s ... %s' % (R['claims']['conductor_upper_le'], 'implied' if v else 'NOT IMPLIED'))
if 'slack_q1_ge' in R.get('claims', {}):
    # The same nu~ for the data with conductor 1 (log q = 0): mu_1 = mu - log q/(2 pi) >= mu_floor - log q/(2 pi) on R,
    # so by weak duality kappa*(data with log q = 0) >= mu_floor - log q/(2 pi) (outward rounding below).
    k1 = arb(mu_floor.numerator) / arb(mu_floor.denominator) - LQ / (2 * PI)
    k1lo = exact(k1.lower())
    c = Fraction(R['claims']['slack_q1_ge'])
    v = ok and k1lo >= c
    checks['slack_q1_ge'] = bool(v)
    print('SLACK AT q = 1 : kappa*(data with log q = 0) >= mu_floor - log q/(2 pi) >= %s' % dec(k1lo, 6, False))
    print('CLAIM          : kappa*(data with log q = 0) >= %s ... %s' % (R['claims']['slack_q1_ge'], 'implied' if v else 'NOT IMPLIED'))
if GAP_X is not None:
    checks['gap_x_' + GAP_X] = gap_ok
res = dict(parameter_file=os.path.relpath(pfile, ANC), sha256=sha256(pfile), logq=R['logq'], T=T, steps=steps,
           min_lower_bound=minlb.str(5), tail_lower_bound=tail.str(8), mu_lower=dec(mu_floor, 6, False), admissible=ok,
           q_upper=dec(exact(q.upper()), 15, True), claims_checked=checks, certified=bool(ok and all(checks.values())),
           support_from_ge=dec(x0, 7, False))
if GAP_X is not None:
    res['admissible_at_gap_x'] = GAP_X
os.makedirs(os.path.join(HERE, 'results'), exist_ok=True)
with open(os.path.join(HERE, 'results', name + '.json'), 'w') as fh:
    json.dump(res, fh, indent=1)
    fh.write('\n')
print('summary written: %s' % os.path.relpath(os.path.join(HERE, 'results', name + '.json'), ANC))
print('RESULT         : %s (%.0f s)' % ('CERTIFIED' if res['certified'] else 'FAILED', time.time() - t0))
sys.exit(0 if res['certified'] else 1)
