"""H >= 1 for the zero-killing functions of the slack ladder, and the resulting bound on int Xi^2 dmu (exact arithmetic).

For each parameter file (kappa/params/J*.json: H(t) = prod_j (1 + r_j t^2 + s_j t^4) with exact rationals r_j, s_j; the
canonical factor-list hash is checked) the polynomial P with H(t) = P(t^2) is expanded EXACTLY over Q (python-flint
fmpq_poly).  If P(0) = 1 and every coefficient of P is >= 0, then H(t) = P(t^2) >= P(0) = 1 for every real t, hence
F_rep = Xi^2 (H + eps e^{-pi t^2}) >= Xi^2 >= 0 on R.

Duality bound (with --duality-log LOG, the log of the certificate of one of the files, e.g. J = 100): the certificate
(kappa/verify_kappa.py) proves F_rep in the cone and A(F_rep) <= A_upper; for every admissible pair (mu, nu),
A(F_rep) = int F_rep dmu + (1/pi) int F_rep^ dnu with both terms >= 0 (weak duality), so
    int Xi^2 dmu <= int F_rep dmu <= A(F_rep) <= A_upper.
The script reads A_upper from the JSON line of LOG, checks that it belongs to the given parameter file (its sha256)
and that the run is certified, and prints A_upper rounded up to 3 significant digits (exact check of the direction).

Usage (from anc/):  python kappa/check_H_nonneg.py kappa/params/J20.json ... kappa/params/J100.json \\
                        --duality-log kappa/logs/J100.log
"""
import argparse
import json
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from flint import arb, fmpq, fmpq_poly, ctx  # noqa: E402
from lib.common import (load_factor_params, relpath, sha256_file, round_up, round_down, require,  # noqa: E402
                        check_decimal)


def dec_down(q):
    return '0' if q == 0 else round_down(arb(fmpq(q.numerator, q.denominator)), 6)


def dec_up(q):
    return '0' if q == 0 else round_up(arb(fmpq(q.numerator, q.denominator)), 6)


def frac(q):
    return Fraction(int(q.p), int(q.q))


def up3(x):
    """Smallest decimal with 3 significant digits that is >= the positive Fraction x (exact check of the direction)."""
    e = len(str(x.numerator)) - len(str(x.denominator))
    while Fraction(10) ** e > x:
        e -= 1
    while Fraction(10) ** (e + 1) <= x:
        e += 1
    k = x / Fraction(10) ** (e - 2)
    K = -((-k.numerator) // k.denominator)
    if K >= 1000:
        K, e = 100, e + 1
    s = '%d.%02de%d' % (K // 100, K % 100, e)
    return check_decimal(s, x, True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('params', nargs='+')
    ap.add_argument('--duality-log', default=None)
    a = ap.parse_args()
    ctx.prec = 200
    ok_all = True
    shas = {}
    print('H(t) = prod_j (1 + r_j t^2 + s_j t^4) = P(t^2), P expanded exactly over Q; certified: P(0) = 1, all coefficients >= 0')
    for path in a.params:
        meta, rs, fsha = load_factor_params(path)
        J = len(rs)
        shas[os.path.abspath(path)] = (fsha, J)
        P = fmpq_poly([1])
        for r, s in rs:
            P = P * fmpq_poly([1, r, s])
        c = [P[k] for k in range(P.degree() + 1)]
        p0 = c[0] == 1
        nonneg = all(x >= 0 for x in c)
        npos = sum(1 for x in c if x > 0)
        kmin = min(range(len(c)), key=lambda k: frac(c[k]))
        kmax = max(range(len(c)), key=lambda k: frac(c[k]))
        ok = bool(p0 and nonneg)
        ok_all = ok_all and ok
        print('%s (sha256 %s; factor list checked): J = %d, deg P = %d, %d coefficients, %d of them > 0; P(0) = 1: %s; '
              'min coefficient >= %s (k = %d); max coefficient <= %s (k = %d)'
              % (relpath(path), fsha, J, P.degree(), len(c), npos, p0, dec_down(frac(c[kmin])), kmin,
                 dec_up(frac(c[kmax])), kmax))
        print('CLAIM      : J = %d: all coefficients of P >= 0 and P(0) = 1, so H >= 1 on R and F_rep >= Xi^2 ... %s'
              % (J, 'implied' if ok else 'NOT IMPLIED'))
    if a.duality_log is not None:
        rec = None
        for line in open(a.duality_log):
            if line.startswith('{"J"'):
                rec = json.loads(line)
        require(rec is not None, 'no JSON summary line in %s' % a.duality_log)
        match = [p for p, (h, J) in shas.items() if h == rec['param_file_sha256'] and J == rec['J']]
        require(len(match) == 1, 'the duality log does not belong to one of the parameter files checked here')
        A_up = Fraction(rec['A_upper'])
        v = bool(rec['certified'] and A_up > 0)
        bound = up3(A_up)
        ok_all = ok_all and v
        print('duality    : %s: certified %s, J = %d, parameter file sha256 %s; A(F_rep) <= A_upper = %s'
              % (relpath(a.duality_log), rec['certified'], rec['J'], rec['param_file_sha256'], rec['A_upper']))
        print('CLAIM      : J = %d: every admissible pair (mu, nu) has int Xi^2 dmu <= int F_rep dmu <= A(F_rep) <= %s ... %s'
              % (rec['J'], bound, 'implied' if v else 'NOT IMPLIED'))
    print('RESULT     : %s' % ('CERTIFIED' if ok_all else 'FAILED'))
    return 0 if ok_all else 1


if __name__ == '__main__':
    sys.exit(main())
