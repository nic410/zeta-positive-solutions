"""Compare the primary certificates (cone/out/W_J{J}_x{X}.json: enclosures exact/out, operators lib/bessel_form, trapezoid-rule
K) with the second evaluation path (cone/out/Wref_J{J}_x{X}.json: the independently computed enclosures exact/ref, the
independent operator construction lib/opcalc, series/asymptotic K of lib/besselk).  Not a certificate: it checks that both
runs certify W_J (x_0 and piece counts are printed) and, for the x_min = 2 runs with the cost, that their certified intervals
for A(F_J) and kappa_J^exact overlap.
Usage: python cone/compare_runs.py 10,60,61,110,111 [--xmin 2|1]
"""
import json
import os
import sys
from fractions import Fraction

D = os.path.dirname(os.path.abspath(__file__))


def iv(lo, hi):
    return Fraction(lo), Fraction(hi)


def main():
    Js = [int(j) for j in sys.argv[1].split(',')]
    xm = sys.argv[sys.argv.index('--xmin') + 1] if '--xmin' in sys.argv else '2'
    ok_all = True
    for J in Js:
        pa = os.path.join(D, 'out/W_J%d_x%s.json' % (J, xm))
        pb = os.path.join(D, 'out/Wref_J%d_x%s.json' % (J, xm))
        if not (os.path.exists(pa) and os.path.exists(pb)):
            print('J = %d: run missing' % J)
            ok_all = False
            continue
        a, b = json.load(open(pa)), json.load(open(pb))
        ok = bool(a['W_certified'] and b['W_certified'])
        extra = ''
        if 'A_lower' in a and 'A_lower' in b:
            Aa, Ab = iv(a['A_lower'], a['A_upper']), iv(b['A_lower'], b['A_upper'])
            ka, kb = iv(a['kappa_exact_lower'], a['kappa_exact_upper']), iv(b['kappa_exact_lower'], b['kappa_exact_upper'])
            ovA = Aa[0] <= Ab[1] and Ab[0] <= Aa[1]
            ovk = ka[0] <= kb[1] and kb[0] <= ka[1]
            ok = ok and ovA and ovk
            extra = '; A intervals overlap: %s; kappa intervals overlap: %s' % (ovA, ovk)
        ok_all = ok_all and ok
        print('J = %3d, x_min = %s: W certified (primary, second path) = (%s, %s); x0 = (%s, %s); pieces = (%d, %d)%s; '
              'pball sha (%s.., %s..)' % (J, xm, a['W_certified'], b['W_certified'], a['x0_BF'], b['x0_BF'], a['pieces'],
                                          b['pieces'], extra, a['pball_sha256'][:10], b['pball_sha256'][:10]))
    print('ALL CONSISTENT' if ok_all else 'NOT ALL CONSISTENT')
    return 0 if ok_all else 1


if __name__ == '__main__':
    sys.exit(main())
