#!/usr/bin/env python3
"""Verify lower bounds  F >= m  on t-intervals and  F^ >= m  on frequency windows for a Laguerre-basis test function,
exactly, and derive the resulting bounds on every admissible pair (low-height rigidity).

Usage (from anc/), after running the certificate of the function (it writes general/results/<function>.json):
    python3 general/verify_windows.py general/params/F80_windows.json [WORKERS]

Dependencies: Python 3 standard library, python-flint.

Function.  F(t) = sum_k a_k f_k(t/s), f_k(u) = L_k^{(-1/2)}(2 pi u^2) exp(-pi u^2), read from the parameter file named in
the window file (without its repair term; the repaired function F_rep = F + eps R, R > 0 with R^ > 0, is larger, so every
lower bound for F and F^ holds for F_rep).  As in verify_general.py: F = e^{-X/2} P(X), X = 2 pi t^2/s^2, and
F^(xi) = s e^{-Y/2} Q(Y), Y = 2 pi s^2 xi^2, with P, Q in Q[x] exact.

Domain (checked for every entry before use).  Each entry is [kind, lo, hi, m, label] with kind "t" or "n", m > 0 and
lo < hi; for kind "t" also lo >= 0 (F is even and X = 2 pi t^2/s^2 is increasing on [0, oo), so [lo, hi] maps onto
[X(lo), X(hi)]; an interval containing negative t is rejected), for kind "n" also lo >= 1 (Y = s^2 (log n)^2/(2 pi) is
increasing on [1, oo)).
Lower bounds (exact).  F >= m on [lo, hi]  <=  P(X) - m U(X) > 0 on [X_lo, X_hi], where U >= e^{X/2} is a rational
polynomial: on a piece [a, a + h] (h <= piece_width), e^{X/2} = e^{a/2} e^y with y = (X - a)/2 in [0, h/2] and
e^y <= T_N(y) + e^{h/2}(h/2)^{N+1}(N+2)/N!  (Taylor polynomial of order N plus a generous Lagrange remainder), with
e^{a/2} replaced by a rational upper bound.  Likewise F^ >= m on [log(lo)/2pi, log(hi)/2pi]  <=  Q - (m/s) U > 0 on
[Y_lo, Y_hi], Y = s^2 (log n)^2/(2 pi).  The endpoints X_lo <= X(lo), X_hi >= X(hi) are rational (outward).  Positivity of
the exact rational polynomial D on [a, b] is proved by D(a) > 0, D(b) > 0 and Descartes' rule of signs after the Moebius
map (a, b) -> (0, oo) (zero sign variations), with bisection when the rule is inconclusive.

Derived bounds.  For an admissible pair (mu, nu) and F in the cone: int F dmu + (1/pi) int F^ dnu = A(F) with both terms
>= 0; mu is even and F is even, so for J in (0, oo):  2 min_J F mu(J) <= A(F);  and  min_I F^ nu(I) <= pi A(F).  Atoms:
nu({xi_n}) <= pi A(F)/F^(xi_n), xi_n = log n/(2 pi), with F^(xi_n) enclosed in Arb.  A = A(F_rep) is the certified upper
bound read from the summary of the function's certificate (its sha256 link to the parameter file is checked).
All derived bounds are rounded upward.

Exact inputs.  The window endpoints lo, hi and the minima m are read from the JSON file as exact decimals (the literal
digits, never through binary64), so the certified windows are exactly the decimal windows of the file.  Printed windows
are the exact decimals when they have at most 12 significant digits, and otherwise are rounded inward (lo up, hi down)
to 12 significant digits, so a printed window is always contained in the certified one; printed minima are rounded down.
"""
import hashlib
import json
import math
import os
import sys
from fractions import Fraction
from multiprocessing import Pool

from flint import arb, fmpq, fmpq_poly, ctx


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


def load(p, exact_decimals=False):
    print('input %-40s sha256 %s' % (os.path.relpath(p, ANC), sha256(p)))
    sys.stdout.flush()
    with open(p) as fh:                               # parse_float=Fraction: decimal literals are read exactly
        return (json.load(fh, parse_float=Fraction) if exact_decimals else json.load(fh)), sha256(p)


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


def inward(q, up):
    """Shortest exact decimal (<= 12 significant digits) of the Fraction q, else q rounded to 12 significant digits
    upward (up) or downward (not up)."""
    for n in range(1, 13):
        s = dec(q, n, up)
        if Fraction(s) == q:
            return s
    s = dec(q, 12, up)
    s = s.rstrip('0').rstrip('.') if '.' in s and 'e' not in s else s         # same value without trailing zeros
    return check_decimal(s, q, up)


def window(lo, hi):
    return '[%s, %s]' % (inward(lo, True), inward(hi, False))


def fq(x):
    f = Fraction(x)
    return fmpq(f.numerator, f.denominator)


def q_lo(x):
    f = exact(x.lower())
    return fmpq(f.numerator, f.denominator)


def q_hi(x):
    f = exact(x.upper())
    return fmpq(f.numerator, f.denominator)


# ------------------------------------------------------------------------------------------------------ inputs
if len(sys.argv) not in (2, 3):
    sys.exit(__doc__)
wfile = resolve(sys.argv[1])
W, _ = load(wfile, exact_decimals=True)
require(W['object'] == 'window_lower_bounds', 'not a window file')
NUM = W['numerics']
for _job in W['minima']:                              # validate every entry before any use
    require(isinstance(_job, list) and len(_job) == 5, 'malformed window entry %r' % (_job,))
    _kind, _lo, _hi, _m, _label = _job
    require(_kind in ('t', 'n'), 'window kind must be "t" or "n" (entry %s)' % _label)
    require(Fraction(_m) > 0, 'lower bound m must be > 0 (window %s)' % _label)
    require(Fraction(_lo) < Fraction(_hi), 'empty window %s' % _label)
    require(Fraction(_lo) >= (0 if _kind == 't' else 1),
            't-windows need 0 <= lo, n-windows need 1 <= lo (window %s)' % _label)
ctx.prec = int(NUM['prec_bits'])
ffile = os.path.join(HERE, W['function'])
FP, h_fp = load(ffile)
require(FP['object'] == 'laguerre_test_function', 'not a Laguerre test-function file')
K = int(FP['K'])
s_q = Fraction(FP['s'])
a_q = [Fraction(x) for x in FP['a']]
require(len(a_q) == K + 1, 'check failed: len(a_q) == K + 1')
x = fmpq_poly([0, 1])
L = [fmpq_poly([1]), fmpq_poly([fmpq(1, 2), -1])]
for k in range(1, K):
    L.append(((2 * k + fmpq(1, 2) - x) * L[k] - (k - fmpq(1, 2)) * L[k - 1]) / (k + 1))
P = fmpq_poly([0])
Q = fmpq_poly([0])
for k in range(K + 1):
    ak = fq(a_q[k])
    P += ak * L[k]
    Q += (ak if k % 2 == 0 else -ak) * L[k]
S_q = fq(s_q)
S = arb(S_q)
PI = arb.pi()
NTAY = int(NUM['taylor_order'])
PW = int(NUM['piece_width'])
MAXD = int(NUM['max_depth'])


def variations(p):
    c = [v for v in p.coeffs() if v != 0]
    return sum(1 for i in range(1, len(c)) if (c[i] > 0) != (c[i - 1] > 0))


def descartes_mobius(D, a, b):
    """Upper bound for the number of roots of D in (a, b): sign variations of (1 + y)^d D((a + b y)/(1 + y))."""
    D1 = D(fmpq_poly([a, b - a]))                      # roots in (0, 1)
    R = fmpq_poly(list(reversed(D1.coeffs())))         # x^d D1(1/x): roots in (1, oo)
    return variations(R(fmpq_poly([1, 1])))            # roots in (0, oo)


def positive_on(D, a, b, depth=0):
    """True only if D > 0 on [a, b] (exact)."""
    if D(a) <= 0 or D(b) <= 0:
        return False
    v = descartes_mobius(D, a, b)
    if v == 0:
        return True
    if v == 1 or depth >= MAXD:      # v = 1 is impossible when D(a), D(b) > 0; treat as failure
        return False
    mid = (a + b) / 2
    return positive_on(D, a, mid, depth + 1) and positive_on(D, mid, b, depth + 1)


def exp_half_upper(z0, h):
    """Rational polynomial U(z) with U(z) >= e^{z/2} on [z0, z0 + h]."""
    E0 = q_hi((arb(z0) / 2).exp())
    y = fmpq_poly([-z0 / 2, fmpq(1, 2)])               # y = (z - z0)/2 in [0, h/2]
    T = fmpq_poly([0])
    term = fmpq_poly([1])
    for j in range(NTAY + 1):
        T += term
        term = term * y / (j + 1)
    hh = arb(h) / 2
    Rb = q_hi(hh.exp() * hh ** (NTAY + 1) / arb(NTAY + 1).gamma() * (NTAY + 2))
    return E0 * (T + Rb)


def check(job):
    kind, lo, hi, m, label = job
    require(kind in ('t', 'n'), 'window kind must be "t" or "n" (entry %s)' % label)
    require(Fraction(m) > 0, 'lower bound m must be > 0 (window %s)' % label)    # m U >= m e^{X/2} needs m > 0
    require(Fraction(lo) < Fraction(hi), 'empty window %s' % label)
    require(Fraction(lo) >= (0 if kind == 't' else 1), 't-windows need 0 <= lo, n-windows need 1 <= lo (%s)' % label)
    mq = fq(m)
    if kind == 't':        # F >= m on [lo, hi]  <=  P(X) >= m e^{X/2},  X = 2 pi t^2/s^2
        z1 = q_lo(2 * PI * arb(fq(lo)) ** 2 / S ** 2)
        z2 = q_hi(2 * PI * arb(fq(hi)) ** 2 / S ** 2)
        poly, scale = P, mq
    else:                  # F^ >= m on [xi(lo), xi(hi)]  <=  Q(Y) >= (m/s) e^{Y/2},  Y = s^2 (log n)^2/(2 pi)
        require(lo >= 1, 'check failed: lo >= 1')
        z1 = q_lo(S ** 2 * arb(fq(lo)).log() ** 2 / (2 * PI))
        z2 = q_hi(S ** 2 * arb(fq(hi)).log() ** 2 / (2 * PI))
        poly, scale = Q, mq / S_q
    npc = max(1, int(math.ceil(float(z2 - z1) / PW)))
    ok = True
    for i in range(npc):
        a = z1 + (z2 - z1) * fmpq(i, npc)
        b = z1 + (z2 - z1) * fmpq(i + 1, npc)
        if not positive_on(poly - scale * exp_half_upper(a, b - a), a, b):
            ok = False
            break
    return label, kind, lo, hi, m, ok, npc


if __name__ == '__main__':
    jobs = W['minima']
    workers = int(sys.argv[2]) if len(sys.argv) == 3 else 1
    print('function       : K = %d, s = %s (%s); %d lower-bound claims; Taylor order %d, pieces of width <= %d in X or Y'
          % (K, FP['s'], W['function'], len(jobs), NTAY, PW))
    sys.stdout.flush()
    results = {}
    if workers > 1:
        with Pool(workers) as pool:
            out = list(pool.imap(check, jobs))
    else:
        out = [check(j) for j in jobs]
    nok = 0
    for label, kind, lo, hi, m, ok, npc in out:
        results[label] = (kind, lo, hi, m, ok)
        nok += ok
        what = 'F  >= m on t in' if kind == 't' else 'F^ >= m on n in'
        print('%-18s %s %s, m >= %s : %s (%d piece%s)' % (label, what, window(lo, hi), dec(Fraction(m), 7, False),
                                                         'PROVED' if ok else 'NOT PROVED', npc, '' if npc == 1 else 's'))
    print('LOWER BOUNDS   : %d/%d proved' % (nok, len(jobs)))
    sys.stdout.flush()
    # ---- A(F_rep) from the certificate summary
    ctx.prec = int(NUM['atom_prec_bits'])
    summ, _ = load(os.path.join(HERE, 'results', os.path.splitext(os.path.basename(ffile))[0] + '.json'))
    require(summ['sha256'] == h_fp, 'summary does not belong to the current function parameter file')
    require(summ['certified'] and summ['positivity']['F_rep>0_on_R'] and summ['positivity']['Fhat_rep>0_on_[xi2,oo)'],
            'certificate summary not certified')
    Aball = arb(summ['A'])
    A_hi = Aball.upper()                                # exact upper endpoint of the certified enclosure
    print('A(F_rep)       <= %s (from the certificate summary)' % dec(exact(Aball.upper()), 12, True))
    checks = {}
    cl = W.get('claims', {})
    print('---- derived bounds for every admissible pair (rounded up)')
    for label, (kind, lo, hi, m, ok) in results.items():
        if not ok:
            continue
        require(Fraction(m) > 0, 'lower bound m must be > 0 (window %s)' % label)
        mA = arb(fq(m))
        if kind == 'n':
            v = PI * A_hi / mA
            txt = 'nu([xi(%s), xi(%s)]) <= %s' % (inward(lo, True), inward(hi, False), dec(exact(v.upper()), 4, True))
            key = 'nu_window_le'
        else:
            if lo <= 0:
                continue                                 # J must lie in (0, oo)
            v = A_hi / (2 * mA)
            txt = 'mu(%s) <= %s' % (window(lo, hi), dec(exact(v.upper()), 4, True))
            key = 'mu_gap_le'
        line = '%-18s %s' % (label, txt)
        if label in cl.get(key, {}):
            c = Fraction(cl[key][label])
            okc = exact(v.upper()) <= c
            checks[label] = okc
            line += '   CLAIM <= %s ... %s' % (cl[key][label], 'implied' if okc else 'NOT IMPLIED')
        print(line)
    qc = [arb(c) for c in Q.coeffs()]
    for n in W.get('atoms', []):
        Y = S ** 2 * arb(n).log() ** 2 / (2 * PI)
        Fh = S * (-Y / 2).exp() * sum((qc[j] * Y ** j for j in range(len(qc))), arb(0))
        require(Fh > 0, 'check failed: Fh > 0')
        v = PI * A_hi / Fh
        line = 'atom n = %-8s F^(xi_n) = %s, nu({xi_n}) <= %s' % (n, Fh.str(8), dec(exact(v.upper()), 4, True))
        if n in cl.get('nu_atom_le', {}):
            okc = exact(v.upper()) <= Fraction(cl['nu_atom_le'][n])
            checks['atom_' + n] = okc
            line += '   CLAIM <= %s ... %s' % (cl['nu_atom_le'][n], 'implied' if okc else 'NOT IMPLIED')
        print(line)
    ok = nok == len(jobs) and all(checks.values())
    print('RESULT         : %s' % ('CERTIFIED' if ok else 'FAILED'))
    sys.exit(0 if ok else 1)
