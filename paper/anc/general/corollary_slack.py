#!/usr/bin/env python3
"""Read off a critical-point bracket and the slack of a number field's data from one dual and one primal certificate.

Usage (from anc/), after running the two certificates named in the corollary file, e.g.
    python3 general/verify_general.py general/params/gammaR2_K80_s7.json        (dual side)
    python3 general/verify_pair.py    general/params/pair_gammaR2_X240.json     (primal side)
    python3 general/corollary_slack.py general/params/corollary_qsqrt5.json [--gap-x N]

Dependencies: Python 3 standard library, python-flint (Arb).

Inputs: the corollary file, the two parameter files it names, and the summaries general/results/<name>.json written
by the two verifiers; each summary records the sha256 of its parameter file, which is checked against the file.

Data.  Gamma-data prod_j Gamma_R(s + kappa_j) with one pole and conductor q:
    A_q(F) = 2F(i/2) + (1/2pi) int F(t) [ sum_j (Re psi((1/2 + kappa_j)/2 + it/2) - log pi) + log q ] dt
           = A_0(F) + (log q/2pi) int F,
so kappa*(A_q) = kappa*_0 + log q/(2pi), and q_min := exp(-2 pi kappa*_0) is the least conductor admitting an
admissible pair.  A number field K with these Gamma-data has Lambda_K(s) = |d_K|^{s/2} (Gamma-factor) zeta_K(s), with
simple poles at s = 0, 1, i.e. the data with q = |d_K| (Q(sqrt 5): Gamma_R(s)^2, q = 5; Q(sqrt -3):
Gamma_C(s) = 2(2pi)^{-s} Gamma(s) = Gamma_R(s) Gamma_R(s+1), q = 3).

Dual side:   F_rep in the cone with A_0(F_rep)/int F_rep <= k0 (printed upper bound): kappa*_0 <= k0, q_min >= e^{-2 pi k0}.
Primal side: an admissible pair (mu, nu) at log q0 with mu >= m0 on R: A_{q0}(F) >= m0 int F on the cone, so
             kappa*_0 >= m0 - log q0/(2pi) and q_min <= q0.
Field:       kappa*(A_{|d_K|}) = kappa*_0 + log|d_K|/(2pi) lies in
             [ (log|d_K| - log q0)/(2pi) + m0 ,  k0 + log|d_K|/(2pi) ];
             (the primal pair read at q = |d_K| carries the uniform floor (log|d_K| - log q0)/(2pi) + m0 in mu).
Gaps.  If the dual function is in the OPS cone (F^_rep > 0 on R), it is in the cone for every gap; the primal pair is
admissible for the gap g whenever its prime measure lives on [g, oo), i.e. e^{2 pi g} <= x0, where supp nu~ is in
[x0, oo) (support_from_ge in the primal summary, a lower bound for x0).  Then the bracket and the slack interval hold
for every such gap.  With --gap-x N the script also checks this at the gap xi_N = log N/(2 pi) (the natural gap of the
field: its smallest prime-power norm N).
Every printed decimal bound is rounded outward from an Arb enclosure of exact rational inputs.
"""
import hashlib
import json
import os
import sys
from fractions import Fraction

from flint import arb, ctx, fmpq


sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from lib.common import require, check_decimal  # noqa: E402  (explicit checks; exact check of every printed decimal)

HERE = os.path.dirname(os.path.abspath(__file__))
ANC = os.path.dirname(HERE)
ctx.prec = 256


def resolve(path):
    for cand in (path, os.path.join(ANC, path), os.path.join(HERE, path)):
        if os.path.isfile(cand):
            return os.path.abspath(cand)
    sys.exit('input file not found: %s' % path)


def sha256(p):
    with open(p, 'rb') as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def load(p):
    print('input %-44s sha256 %s' % (os.path.relpath(p, ANC), sha256(p)))
    return json.load(open(p)), sha256(p)


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


def A(q):
    return arb(fmpq(q.numerator, q.denominator))


ARGS = sys.argv[1:]
GAP_X = None
if '--gap-x' in ARGS:
    i = ARGS.index('--gap-x')
    if i + 1 >= len(ARGS):
        sys.exit(__doc__)
    GAP_X = ARGS[i + 1]
    del ARGS[i:i + 2]
if len(ARGS) != 1:
    sys.exit(__doc__)
cfile = resolve(ARGS[0])
cor, _ = load(cfile)
require(cor['object'] == 'corollary', "check failed: cor['object'] == 'corollary'")
dpar = os.path.join(HERE, cor['dual'])
ppar = os.path.join(HERE, cor['primal'])
pd, h_pd = load(dpar)
pp, h_pp = load(ppar)
dual, _ = load(os.path.join(HERE, 'results', os.path.splitext(os.path.basename(dpar))[0] + '.json'))
prim, _ = load(os.path.join(HERE, 'results', os.path.splitext(os.path.basename(ppar))[0] + '.json'))
require(dual['sha256'] == h_pd, 'dual summary does not belong to the current parameter file')
require(prim['sha256'] == h_pp, 'primal summary does not belong to the current parameter file')
require(dual['certified'] and dual['positivity']['F_rep>0_on_R'] and dual['positivity']['Fhat_rep>0_on_[xi2,oo)'],
        'dual summary not certified')
require(prim['certified'] and prim['admissible'] and prim['logq'] == pp['logq'],
        'primal summary not certified or for another log q')
shifts = [Fraction(str(k)) for k in cor['gamma_shifts']]
require([Fraction(str(k)) for k in pd['gamma_data']['shifts']] == shifts, 'dual Gamma-data differ')
require([Fraction(str(k)) for k in pp['gamma_shifts']] == shifts, 'primal Gamma-data differ')
require(Fraction(pd['gamma_data']['log_conductor']) == 0 and Fraction(pd['gamma_data']['pole_residue']) == 1,
        'dual data must have log N = 0 and pole residue 1')
require(Fraction(str(pp['pole_residue'])) == 1, 'primal pair must have pole residue 1')

k0 = Fraction(dual['kappa_upper'])                   # kappa*_0 <= k0 (already rounded upward)
lq0 = Fraction(pp['logq'])                           # admissible pair at log q0 ...
m0 = Fraction(prim['mu_lower'])                      # ... with mu >= m0 on R (already rounded downward)
qF = Fraction(cor['field_conductor'])
PI = arb.pi()
LF = A(qF).log()
qlo = (-2 * PI * A(k0)).exp()
qhi = A(lq0).exp()
kF_hi = A(k0) + LF / (2 * PI)
kF_lo = (LF - A(lq0)) / (2 * PI) + A(m0)
print('data       : Gamma_R shifts %s, one pole; field %s with conductor %s' % (cor['gamma_shifts'], cor['field'], cor['field_conductor']))
print('dual       : kappa*_0 <= %s' % dual['kappa_upper'])
print('primal     : admissible pair at log q0 = %s with mu >= %s on R' % (pp['logq'], prim['mu_lower']))
print('BRACKET    : %s <= q_min <= %s' % (dec(exact(qlo.lower()), 16, False), dec(exact(qhi.upper()), 10, True)))
print('SLACK      : %s <= kappa*(%s) <= %s' % (dec(exact(kF_lo.lower()), 8, False), cor['field'], dec(exact(kF_hi.upper()), 8, True)))
OPS = bool(dual['positivity'].get('Fhat_rep>0_on_R'))
X0 = prim.get('support_from_ge')                     # supp nu~ in [x0, oo) with x0 >= X0 (rounded down)
if X0 is not None:
    print('GAPS       : dual function in the OPS cone: %s; supp nu~ of the pair in [x0, oo) with x0 >= %s; %s'
          % (OPS, X0, 'so the bracket and the slack interval hold for every gap g with e^{2 pi g} <= x0' if OPS
             else 'no statement for other gaps'))
cl = cor['claims']
claims = [('q_min >= %s' % cl['qmin_ge'], exact(qlo.lower()) >= Fraction(cl['qmin_ge'])),
          ('q_min <= %s' % cl['qmin_le'], exact(qhi.upper()) <= Fraction(cl['qmin_le'])),
          ('kappa*(%s) >= %s' % (cor['field'], cl['kappa_field_ge']), exact(kF_lo.lower()) >= Fraction(cl['kappa_field_ge'])),
          ('kappa*(%s) <= %s' % (cor['field'], cl['kappa_field_le']), exact(kF_hi.upper()) <= Fraction(cl['kappa_field_le'])),
          ('kappa*(%s) > 0, so these data are not critical' % cor['field'], exact(kF_lo.lower()) > 0)]
if GAP_X is not None:
    require(X0 is not None, 'the primal summary does not record support_from_ge')
    claims.append(('the bracket and the slack interval hold at the natural gap xi_%s of %s (%s <= x0)'
                   % (GAP_X, cor['field'], GAP_X), OPS and Fraction(X0) >= Fraction(GAP_X)))
for text, v in claims:
    print('CLAIM      : %s ... %s' % (text, 'implied' if v else 'NOT IMPLIED'))
ok = all(v for _, v in claims)
print('RESULT     : %s' % ('CERTIFIED' if ok else 'FAILED'))
sys.exit(0 if ok else 1)
