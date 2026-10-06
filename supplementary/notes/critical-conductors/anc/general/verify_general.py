#!/usr/bin/env python3
"""Verify a Laguerre-basis (general-family) cone certificate for an explicit-formula functional.

Usage (from anc/):   python3 general/verify_general.py general/params/<name>.json

Dependencies: Python 3 standard library, python-flint (Arb/FLINT bindings), nothing else.

Test function.  With f_k(u) = L_k^{(-1/2)}(2 pi u^2) exp(-pi u^2) (L_k^{(-1/2)} the generalised Laguerre polynomial),
    F(t)     = sum_{k=0}^{K} a_k f_k(t/s),
    F_rep(t) = F(t) + eps * ( exp(-pi t^2/(16 s^2)) + exp(-16 pi t^2/s^2) ),
with the a_k the exact decimal strings of the parameter file (read as exact rationals), s and eps exact.
The f_k are Hermite functions of degree 2k, so f_k^ = (-1)^k f_k for  G^(xi) = int G(t) exp(-2 pi i xi t) dt.  Hence
    F(t)    = exp(-X/2) P(X),        X = 2 pi t^2 / s^2,      P = sum_k a_k L_k^{(-1/2)},
    F^(xi)  = s exp(-Y/2) Q(Y),      Y = 2 pi s^2 xi^2,       Q = sum_k (-1)^k a_k L_k^{(-1/2)},
and P, Q are polynomials with exact rational coefficients.  The two Gaussians of the repair term are positive with
positive Fourier transforms, so F_rep >= F and F_rep^ >= F^ pointwise.

Positivity (exact).  Sturm sequences over Q count the distinct real roots of P and Q:
  * P(0) > 0 and no root of P in (0, oo)                  ==>  F_rep > 0 on R;
  * Q(0) > 0 and no root of Q in (0, oo)                  ==>  F_rep^ > 0 on R           (Odlyzko-Poitou-Serre cone);
  * Q(Y_lo) > 0 and no root of Q in (Y_lo, oo), where Y_lo < Y_c is rational and Y_c = 2 pi s^2 xi_2^2 corresponds to
    the gap edge xi_2 = log 2/(2 pi)                      ==>  F_rep^ > 0 on [xi_2, oo)    (the cone of the paper).

Functional.  For Gamma-data prod_j Gamma_R(s + kappa_j) (Gamma_R(s) = pi^{-s/2} Gamma(s/2)), conductor N and pole
residue r, the archimedean side of Weil's explicit formula is
    A(F) = r * 2F(i/2) + (1/2pi) int_R F(t) [ sum_j ( Re psi((1/2 + kappa_j)/2 + it/2) - log pi ) + log N ] dt
(psi = Gamma'/Gamma; for zeta: one factor, kappa = 0, N = 1, r = 1).  A(F_rep) is computed from ONE rigorous Arb
integral (acb.integral) of F_rep(t) * sum_j Re psi(...) over [0, T], with F_rep evaluated by the three-term Laguerre
recurrence on complex balls, plus a rigorous bound for the tail t > T (it uses |Re psi(w_j + it/2)| <= t for t >= T >= 10,
proved for shifts 0 <= kappa_j with (1/2 + kappa_j)^2 <= 300; both conditions are checked).  Also computed: int F_rep = F_rep^(0) (exact
polynomial value plus the Gaussians) and D = 2F_rep(i/2).

Read-off.  For F in the cone with int F > 0 and every admissible pair (mu, nu) of the data,
A(F) = int F dmu + (1/pi) int F^ dnu >= 0.  Hence:
  * kappa*(data) <= A(F_rep)/int F_rep, and also kappa*_OPS(data) if F_rep^ >= 0 on all of R;
  * conductor q:  A_q = A + (log q/2pi) int F, so A_q(F_rep) < 0, i.e. no admissible pair, for
    log q < -2 pi A(F_rep)/int F_rep;  equivalently q_min = exp(-2 pi kappa*) >= exp(-2 pi A(F_rep)/int F_rep);
  * pole residue r:  A_r = A_1 + (r - 1) D is affine in r, so A_r(F_rep) < 0 (no admissible pair) for
    r < 1 - A_1/D if D > 0, and for r > 1 + A_1/|D| if D < 0.
Every printed decimal bound is rounded outward (upper bounds up, lower bounds down) from the Arb enclosure.
A machine-readable summary (no timings) is written to general/results/<name>.json.
"""
import hashlib
import json
import os
import sys
import time
from fractions import Fraction

from flint import arb, acb, fmpq, fmpq_poly, ctx


sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from lib.common import require, check_decimal  # noqa: E402  (explicit checks; exact check of every printed decimal)

HERE = os.path.dirname(os.path.abspath(__file__))
ANC = os.path.dirname(HERE)


# ----------------------------------------------------------------------------------------------- small utilities
def resolve(path):
    """Accept a path relative to the working directory, to anc/ or to anc/general/."""
    for cand in (path, os.path.join(ANC, path), os.path.join(HERE, path)):
        if os.path.isfile(cand):
            return os.path.abspath(cand)
    sys.exit('input file not found: %s' % path)


def rel(p):
    return os.path.relpath(p, ANC)


def sha256(p):
    with open(p, 'rb') as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def frac(x):
    """Exact rational from a decimal string (or int)."""
    return Fraction(str(x))


def to_fmpq(q):
    return fmpq(q.numerator, q.denominator)


def exact(a):
    """Exact value of an exact (zero-radius) arb as a Fraction."""
    m, e = a.man_exp()
    return Fraction(int(m)) * Fraction(2) ** int(e)


def lo(x):
    return exact(x.lower())


def hi(x):
    return exact(x.upper())


def dec(q, n, up):
    """Decimal string with n significant digits of the Fraction q, rounded toward +oo (up) or -oo (not up), with an
    exact a-posteriori check of the direction (lib/common.py)."""
    return check_decimal(_dec(q, n, up), q, up)


def _dec(q, n, up):
    """Decimal string with n significant digits of the Fraction q, rounded toward +oo (up=True) or -oo (up=False)."""
    if q == 0:
        return '0'
    neg = q < 0
    a = -q if neg else q
    E = len(str(a.numerator)) - len(str(a.denominator))
    while Fraction(10) ** E > a:
        E -= 1
    while Fraction(10) ** (E + 1) <= a:
        E += 1
    scale = Fraction(10) ** (E - n + 1)
    k = a / scale
    away = (not neg) == up                      # round the magnitude away from zero?
    K = -((-k.numerator) // k.denominator) if away else k.numerator // k.denominator
    digits = str(K)
    if len(digits) > n:                         # carried into a new decade (K = 10^n)
        E += 1
        digits = digits[:n]
    sgn = '-' if neg else ''
    if -5 < E < 5:                              # fixed-point notation: value = digits * 10^(-d)
        d = n - 1 - E
        if d <= 0:
            return sgn + digits + '0' * (-d)
        z = digits.rjust(d + 1, '0')
        return sgn + z[:-d] + '.' + z[-d:]
    return sgn + digits[0] + ('.' + digits[1:] if n > 1 else '') + 'e' + str(E)


def up(x, n=15):
    return dec(hi(x), n, True)


def down(x, n=15):
    return dec(lo(x), n, False)


# ------------------------------------------------------------------------------------------------------ inputs
if len(sys.argv) != 2:
    sys.exit(__doc__)
pfile = resolve(sys.argv[1])
prm = json.load(open(pfile))
name = os.path.splitext(os.path.basename(pfile))[0]
print('parameter file : %s' % rel(pfile))
print('sha256         : %s' % sha256(pfile))
require(prm['object'] == 'laguerre_test_function', 'not a Laguerre test-function file')
K = int(prm['K'])
s_q = frac(prm['s'])
eps_q = frac(prm['eps'])
a_q = [frac(x) for x in prm['a']]
require(len(a_q) == K + 1 and s_q > 0 and eps_q > 0, 'need K + 1 coefficients, s > 0, eps > 0')
gd = prm['gamma_data']
num = prm['numerics']
PREC, T = int(num['prec_bits']), int(num['T'])
RELB, ABST = int(num['rel_tol_bits']), int(num['abs_tol_exp10'])
ctx.prec = PREC
kappas = [arb(str(k)) for k in gd['shifts']]
# Domain of the tail estimate (see the comment at the tail bound below): every shift kappa_j satisfies 0 <= kappa_j and
# (1/2 + kappa_j)^2 <= 300, i.e. the digamma argument w_j = (1/2 + kappa_j)/2 lies in [1/4, 5 sqrt 3]; and T >= 10.
require(all(Fraction(str(k)) >= 0 and (Fraction(1, 2) + Fraction(str(k))) ** 2 <= 300 for k in gd['shifts']),
        'Gamma shifts must satisfy 0 <= kappa_j and (1/2 + kappa_j)^2 <= 300 (domain of the tail estimate)')
require(T >= 10, 'the tail estimate needs T >= 10')
logN = arb(str(gd['log_conductor']))
pole = arb(str(gd['pole_residue']))
nfac = len(kappas)
print('object         : K = %d, s = %s, eps = %s, Gamma_R shifts %s, log N = %s, pole residue %s'
      % (K, prm['s'], prm['eps'], gd['shifts'], gd['log_conductor'], gd['pole_residue']))
print('numerics       : %d-bit Arb, integral over [0, %d], rel_tol 2^-%d, abs_tol 1e-%d' % (PREC, T, RELB, ABST))
sys.stdout.flush()
t0 = time.time()

# ---------------------------------------------- exact P, Q by (k+1) L_{k+1} = (2k + 1/2 - x) L_k - (k - 1/2) L_{k-1}
x = fmpq_poly([0, 1])
L = [fmpq_poly([1]), fmpq_poly([fmpq(1, 2), -1])]
for k in range(1, K):
    L.append(((2 * k + fmpq(1, 2) - x) * L[k] - (k - fmpq(1, 2)) * L[k - 1]) / (k + 1))
a = [to_fmpq(v) for v in a_q]
P = fmpq_poly([0])
Q = fmpq_poly([0])
for k in range(K + 1):
    P += a[k] * L[k]
    Q += (a[k] if k % 2 == 0 else -a[k]) * L[k]
print('P, Q built     : degrees %d, %d (%.1f s)' % (P.degree(), Q.degree(), time.time() - t0))
sys.stdout.flush()


# ---------------------------------------------------------------------------------------------- Sturm sequences
def sturm(p):
    """Sturm sequence p, p', -rem(...), each remainder scaled by a positive rational (signs preserved)."""
    seq = [p, p.derivative()]
    while True:
        rem = -(seq[-2] % seq[-1])
        if rem.is_zero():
            break
        seq.append(rem / abs(rem.coeffs()[-1]))
    return seq


def variations(vals):
    sg = [v > 0 for v in vals if v != 0]
    return sum(1 for i in range(1, len(sg)) if sg[i] != sg[i - 1])


def roots_above(seq, a0):
    """Number of distinct real roots of seq[0] in (a0, oo); requires seq[0](a0) != 0 (Sturm's theorem)."""
    require(seq[0](a0) != 0, 'check failed: seq[0](a0) != 0')
    return variations([p(a0) for p in seq]) - variations([p.coeffs()[-1] for p in seq])


PI = arb.pi()
sA = arb(to_fmpq(s_q))
xi2 = arb(2).log() / (2 * PI)                       # gap edge xi_2 = log 2/(2 pi)
Yc = 2 * PI * sA * sA * xi2 * xi2                   # Y at xi = xi_2
Yc_lo = fmpq(int((Yc.lower() * 2 ** 220).floor().unique_fmpz()), 2 ** 220)
Yc_hi = fmpq(int((Yc.upper() * 2 ** 220).ceil().unique_fmpz()), 2 ** 220)
require(arb(Yc_lo) < Yc and arb(Yc_hi) > Yc, 'need Y_lo < Y_c < Y_hi')

zero = fmpq(0)
SP = sturm(P)
print('Sturm(P)       : length %d (%.1f s)' % (len(SP), time.time() - t0))
sys.stdout.flush()
nP = roots_above(SP, zero)
SQ = sturm(Q)
print('Sturm(Q)       : length %d (%.1f s)' % (len(SQ), time.time() - t0))
sys.stdout.flush()
nQ0 = roots_above(SQ, zero)
nQc = roots_above(SQ, Yc_lo)
nQch = roots_above(SQ, Yc_hi)
P0, Q0, QYc = P(zero), Q(zero), Q(Yc_lo)
F_pos = bool(P0 > 0 and nP == 0)
Fh_ops = bool(Q0 > 0 and nQ0 == 0)
Fh_cone = bool(QYc > 0 and nQc == 0)
print('P              : P(0) > 0: %s; leading coefficient > 0: %s; distinct real roots in (0, oo): %d'
      % (P0 > 0, P.coeffs()[-1] > 0, nP))
print('Q              : Q(0) > 0: %s; leading coefficient > 0: %s; distinct real roots in (0, oo): %d'
      % (Q0 > 0, Q.coeffs()[-1] > 0, nQ0))
print('Q at gap edge  : Y_lo < Y_c < Y_hi rational, |Y_hi - Y_lo| <= 2^-219; roots in (Y_lo, oo): %d, in (Y_hi, oo): %d;'
      ' Q(Y_lo) = %s (> 0: %s)' % (nQc, nQch, arb(QYc).str(8), QYc > 0))
print('POSITIVITY     : F_rep > 0 on R: %s | F_rep^ > 0 on [xi_2, oo) (cone): %s | F_rep^ > 0 on R (OPS cone): %s'
      % (F_pos, Fh_cone, Fh_ops))
sys.stdout.flush()
if not (F_pos and Fh_cone):
    print('FAIL: F_rep is not certified to lie in the cone')
    sys.exit(1)

# ------------------------------------------------------------------------------- A(F_rep) by direct integration
ac = [arb(v) for v in a]
epsA = arb(to_fmpq(eps_q))


def Feval(z):
    """F_rep(z) for complex z (acb), via the Laguerre three-term recurrence at X = 2 pi z^2/s^2."""
    X = 2 * PI * z * z / (sA * sA)
    l0 = acb(1)
    l1 = acb(arb(1) / 2) - X
    S = ac[0] * l0 + ac[1] * l1
    for k in range(1, K):
        l0, l1 = l1, ((2 * k + arb(1) / 2 - X) * l1 - (k - arb(1) / 2) * l0) / (k + 1)
        S += ac[k + 1] * l1
    return (-X / 2).exp() * S + epsA * ((-PI * z * z / (16 * sA * sA)).exp() + (-16 * PI * z * z / (sA * sA)).exp())


def integrand(z, analytic):
    """F_rep(z) * sum_j (psi(w_j + iz/2) + psi(w_j - iz/2))/2, w_j = (1/2 + kappa_j)/2: on R this is
    F_rep(t) * sum_j Re psi(w_j + it/2), and it is meromorphic in z (Arb returns an infinite ball near a pole,
    which makes the integrator subdivide), so no branch-cut handling is needed."""
    g = acb(0)
    for kap in kappas:
        w1 = acb((arb(1) / 2 + kap) / 2) + acb(0, 1) * z / 2
        w2 = acb((arb(1) / 2 + kap) / 2) - acb(0, 1) * z / 2
        g += (w1.digamma() + w2.digamma()) / 2
    return Feval(z) * g


I = acb.integral(integrand, 0, T, rel_tol=arb(2) ** (-RELB), abs_tol=arb(10) ** -ABST,
                 eval_limit=10 ** 8, depth_limit=10 ** 6)
print('integral       : int_0^T F_rep(t) sum_j Re psi = %s (imaginary part %s) (%.0f s)'
      % (I.real.str(30), I.imag.str(3), time.time() - t0))
sys.stdout.flush()
# Tail t > T.  |F(t)| <= exp(-X/2) sum_j |p_j| X^j with P = sum_j p_j X^j, and |Re psi(w_j + it/2)| <= t for t >= 10:
# for w > 0, tau > 0, the partial fractions Re psi(w + i tau) = lim_N (log N - sum_{n<N} f(n)), f(x) = (x+w)/((x+w)^2+tau^2),
# and |sum_{n<N} f(n) - int_0^N f| <= total variation of f on [0, oo) <= 1/tau give
#     |Re psi(w + i tau) - log sqrt(w^2 + tau^2)| <= 1/tau;
# with tau = t/2, t >= 10 and w_j^2 <= 75 <= 3t^2/4 (checked above): 0 < log(t/2) - 2/t <= Re psi(w_j + it/2) <= log t + 2/t <= t.
# With X = 2 pi t^2/s^2, t dt = s^2/(4 pi) dX and int_{X_T}^oo X^j e^{-X/2} dX = 2^{j+1} Gamma(j+1, X_T/2)
# (Arb: z.gamma_upper(s) = Gamma(s, z)).  The repair Gaussians: eps (e^{-pi t^2/16s^2} + e^{-16 pi t^2/s^2}) <=
# 2 eps e^{-pi t^2/16s^2} and int_T^oo t e^{-pi t^2/16s^2} dt = (16 s^2/2pi) e^{-pi T^2/16s^2}; an extra factor 4 is slack.
require(T >= 10, 'check failed: T >= 10')
XT = 2 * PI * arb(T) ** 2 / (sA * sA)
tb = arb(0)
for j, cf in enumerate(P.coeffs()):
    tb += abs(arb(cf)) * arb(2) ** (j + 1) * (XT / 2).gamma_upper(arb(j + 1))
tb = tb * sA * sA / (4 * PI) * nfac
tb += nfac * epsA * 2 * ((-PI * arb(T) ** 2 / (16 * sA * sA)).exp()) * (16 * sA * sA / (2 * PI)) * 4
Iint = I.real + arb(0, tb.upper())
Fh0 = sA * arb(Q0) + epsA * sA * (4 + arb(1) / 4)   # int F_rep = F_rep^(0) = s Q(0) + eps (4s + s/4)
Fi2 = Feval(acb(0, arb(1) / 2)).real
D = 2 * Fi2
A = pole * D + Iint / PI + (logN - nfac * PI.log()) / (2 * PI) * Fh0
ratio = A / Fh0
print('tail bound     : %s' % tb.str(3))
print('A(F_rep)       = %s' % A.str(25))
print('int F_rep      = %s' % Fh0.str(25))
print('D = 2F_rep(i/2)= %s' % D.str(20))
print('A/int F_rep    = %s' % ratio.str(25))
sys.stdout.flush()

# ------------------------------------------------------------------------------------------------------ read-off
res = dict(parameter_file=rel(pfile), sha256=sha256(pfile), K=K, s=prm['s'], eps=prm['eps'],
           gamma_data=gd, numerics=num,
           positivity={'P(0)>0': bool(P0 > 0), 'P_roots_(0,oo)': nP, 'Q(0)>0': bool(Q0 > 0), 'Q_roots_(0,oo)': nQ0,
                       'Q_roots_(Y_lo,oo)': nQc, 'Q_roots_(Y_hi,oo)': nQch, 'Q(Y_lo)>0': bool(QYc > 0),
                       'F_rep>0_on_R': F_pos, 'Fhat_rep>0_on_[xi2,oo)': Fh_cone, 'Fhat_rep>0_on_R': Fh_ops},
           A=A.str(25), int_F=Fh0.str(25), D=D.str(20), ratio=ratio.str(25), tail=tb.str(3))
ok = True
print('---- read-off (decimal bounds rounded outward)')
res['kappa_upper'] = up(ratio, 20)
cone = 'kappa*_OPS (and kappa*)' if Fh_ops else 'kappa*'
print('SLACK          : %s of the data <= %s' % (cone, up(ratio, 20)))
claims = prm.get('claims', {})
checks = {}
if 'kappa_upper_le' in claims:
    c = frac(claims['kappa_upper_le'])
    v = hi(ratio) <= c
    checks['kappa_upper_le'] = v
    print('CLAIM          : %s <= %s ... %s' % (cone, claims['kappa_upper_le'], 'implied' if v else 'NOT IMPLIED'))
Lq = -2 * PI * ratio                                 # A_q(F_rep) < 0, i.e. no admissible pair, for log q < Lq
qlo = Lq.exp()
res['log_conductor_threshold_lower'] = down(Lq, 20)
res['qmin_lower'] = down(qlo, 20)
if hi(ratio) < 0:
    print('CONDUCTOR      : no admissible pair for log q < %s, i.e. q < %s; q_min >= %s'
          % (down(Lq, 20), down(qlo, 20), down(qlo, 20)))
else:
    res['qmin_lower_as_1_minus'] = up(1 - qlo, 6)
    print('CONDUCTOR      : no admissible pair for log q < %s; q_min = exp(-2 pi kappa*) >= 1 - %s'
          % (down(Lq, 20), up(1 - qlo, 6)))
if 'qmin_ge_1_minus' in claims:
    c = frac(claims['qmin_ge_1_minus'])
    v = hi(1 - qlo) <= c
    checks['qmin_ge_1_minus'] = v
    print('CLAIM          : q_min >= 1 - %s ... %s' % (claims['qmin_ge_1_minus'], 'implied' if v else 'NOT IMPLIED'))
if 'conductor_lower_ge' in claims:
    c = frac(claims['conductor_lower_ge'])
    v = lo(qlo) >= c
    checks['conductor_lower_ge'] = v
    print('CLAIM          : q_min >= %s ... %s' % (claims['conductor_lower_ge'], 'implied' if v else 'NOT IMPLIED'))
if A > 0 and (D > 0 or D < 0):                     # pole-residue pin (meaningful when A(F_rep) > 0)
    w = A / abs(D)
    side = 'left' if D > 0 else 'right'
    res['pole_residue_' + side + '_width_upper'] = up(w, 12)
    if D > 0:
        print('POLE RESIDUE   : D > 0; A_r(F_rep) < 0, hence no admissible pair, for every r < 1 - A/D, A/D <= %s' % up(w, 12))
    else:
        print('POLE RESIDUE   : D < 0; A_r(F_rep) < 0, hence no admissible pair, for every r > 1 + A/|D|, A/|D| <= %s'
              % up(w, 12))
    for key, sgn in (('pole_left_width_gt', 1), ('pole_right_width_gt', -1)):
        if key in claims:
            wq = arb(to_fmpq(frac(claims[key])))
            # left: r <= 1 - w gives A_r <= A - w D (D > 0); right: r >= 1 + w gives A_r <= A + w D (D < 0)
            v = bool((sgn * D > 0) and (A - sgn * wq * D < 0))
            checks[key] = v
            stmt = 'r <= 1 - %s' % claims[key] if sgn > 0 else 'r >= 1 + %s' % claims[key]
            print('CLAIM          : no admissible pair for %s ... %s' % (stmt, 'implied' if v else 'NOT IMPLIED'))
res['claims_checked'] = checks
ok = ok and all(checks.values())
res['certified'] = bool(ok)
os.makedirs(os.path.join(HERE, 'results'), exist_ok=True)
with open(os.path.join(HERE, 'results', name + '.json'), 'w') as fh:
    json.dump(res, fh, indent=1)
    fh.write('\n')
print('summary written: %s' % rel(os.path.join(HERE, 'results', name + '.json')))
print('RESULT         : %s (%.0f s)' % ('CERTIFIED' if ok else 'FAILED', time.time() - t0))
sys.exit(0 if ok else 1)
