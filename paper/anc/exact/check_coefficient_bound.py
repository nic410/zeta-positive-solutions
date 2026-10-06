"""Explicit check of a coefficient bound for exact Hermite members, from their certified enclosures.

For each enclosure file (output of verify_exact_member.py: balls containing the exact coefficients p_0 = 1, p_1, ...,
p_2J of P_J), the script checks that every p_k (k >= 1) is certified > 0, computes a rigorous upper bound for
    a_J = max_{1 <= k <= 2J} ((2k)! p_k)^{1/(2k)}
from the upper endpoints of the balls (Arb), prints it rounded up, and checks a_J <= BOUND by an exact comparison
of the upper endpoint with the decimal BOUND.  Then 0 < p_k <= BOUND^{2k}/(2k)! for every k.

Usage (from anc/):  python exact/check_coefficient_bound.py --bound 0.71636 exact/out/P60_ball.txt [more files]
"""
import argparse
import math
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from flint import arb, ctx  # noqa: E402
from lib.common import relpath, sha256_file, fixed_up, exact_max, require  # noqa: E402


def exact(a):
    m, e = a.man_exp()
    return Fraction(int(m)) * Fraction(2) ** int(e)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--bound', required=True)
    ap.add_argument('balls', nargs='+')
    a = ap.parse_args()
    bound = Fraction(a.bound)
    ctx.prec = 4000
    ok_all = True
    Js = []
    for path in a.balls:
        P = [arb(s) for s in open(path).read().split('\n') if s.strip()]
        require(len(P) % 2 == 1 and len(P) >= 3, 'an enclosure must hold p_0 .. p_2J')
        J = (len(P) - 1) // 2
        pos = all(c > 0 for c in P[1:])
        aval = exact_max([(arb(math.factorial(2 * k)) * arb(c.upper())) ** (arb(1) / (2 * k))
                          for k, c in enumerate(P) if k > 0]) if pos else None
        ok = bool(pos and exact(aval.upper()) <= bound)
        ok_all = ok_all and ok
        Js.append(J)
        print('P-enclosure %s (sha256 %s): J = %d; all p_k > 0: %s; max_k ((2k)! p_k)^(1/2k) <= %s;  <= %s: %s'
              % (relpath(path), sha256_file(path), J, pos, fixed_up(aval, 6) if pos else 'n/a', a.bound, ok))
    print('CERTIFIED: 0 < p_k <= %s^(2k)/(2k)! for every k, at J = %s: %s'
          % (a.bound, ', '.join(str(J) for J in Js), ok_all))
    return 0 if ok_all else 1


if __name__ == '__main__':
    sys.exit(main())
