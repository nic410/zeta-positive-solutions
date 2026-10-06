"""Certified root geometry of the exact Hermite member P_J(u), u = t^2, from a certified coefficient enclosure.

The coefficient balls (output of verify_exact_member.py) define an acb_poly; Arb's root isolation (acb_poly.roots,
i.e. acb_poly_find_roots followed by acb_poly_validate_roots) returns 2J disjoint balls, each containing exactly one
root of every polynomial in the coefficient ball, or raises an error.  From the root balls:
  * min |Im t| over the roots t = +-sqrt(u)            (rigorous lower bound),
  * min |arg u| and min |u|                              (rigorous lower bounds),
  * B = sum 1/|u_j| and p_1 = -sum 1/u_j                  (balls),
  * the number of roots with Re u > 0 (each one certified to lie in Re u > 0 or Re u < 0), their |arg u| (midpoints to
    4 decimals, for orientation) and a rigorous interval containing all of them (min rounded down, max rounded up),
  * sup_{r>0} N(r)/r, N(r) = #{j : |u_j| <= r^2}: N is constant between consecutive moduli, so the sup is a max over
    the jump points r_i = sqrt|u_i| and is bounded above by max_i #{j : |u_j|_lower <= |u_i|_upper} / sqrt(|u_i|_lower).
All printed bounds are rounded outward with exact checks of the direction (lib/common.py); no binary64 arithmetic.
Usage (from anc/):  python exact/verify_roots.py BALLFILE [--prec BITS]
"""
import argparse
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from flint import arb, acb, acb_poly, ctx  # noqa: E402
from lib.common import relpath, sha256_file, round_down, round_up, fixed_up, require, exact_min, exact_max  # noqa: E402


def mid4(v):
    """Midpoint of the ball v rounded to 4 decimals (orientation only; exact rational arithmetic, no binary64)."""
    m, e = v.mid().man_exp()
    q = Fraction(int(m)) * Fraction(2) ** int(e)
    k = (q * 10 ** 4 * 2 + 1) // 2                                      # round half up
    return '%d.%04d' % divmod(int(k), 10 ** 4)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('ball')
    ap.add_argument('--prec', type=int, default=2000)
    a = ap.parse_args()
    ctx.prec = a.prec
    cs = [arb(w) for w in open(a.ball).read().split('\n') if w.strip()]
    d = len(cs) - 1
    print('P-enclosure %s (sha256 %s): degree %d in u = t^2' % (relpath(a.ball), sha256_file(a.ball), d))
    roots = acb_poly([acb(c) for c in cs]).roots(tol=arb(2) ** -150)              # isolate, then refine
    require(len(roots) == d, 'root isolation did not return deg P balls')
    print('all %d roots isolated (validated disjoint balls, one root each)' % d)
    lo = lambda v: arb(v.lower())                                        # noqa: E731
    imt = [lo(abs(u.sqrt().imag)) for u in roots]
    args = [lo(abs(u.arg())) for u in roots]
    mods = [abs(u) for u in roots]
    mn = exact_min                                                       # exact comparison of lower endpoints
    B = sum((1 / m for m in mods), arb(0))
    p1 = -sum((1 / u for u in roots), acb(0))
    rhp = [i for i, u in enumerate(roots) if u.real > 0]
    lhp = [i for i, u in enumerate(roots) if u.real < 0]
    und = d - len(rhp) - len(lhp)
    sup = None
    for i in range(d):
        cnt = sum(1 for j in range(d) if arb(mods[j].lower()) <= arb(mods[i].upper()))
        v = arb(cnt) / arb(mods[i].lower()).sqrt()
        sup = v if sup is None or arb(v.upper()) > arb(sup.upper()) else sup
    print('min |Im t| >= %s' % round_down(mn(imt), 8))
    print('min |arg u| >= %s;  min |u| >= %s' % (round_down(mn(args), 8), round_down(mn([lo(m) for m in mods]), 8)))
    print('B = sum 1/|u| in %s;  p_1 = -sum 1/u in %s' % (B.str(10), p1.real.str(12)))
    rargs = [abs(roots[i].arg()) for i in rhp]
    print('roots with Re u > 0: %d (certified), Re u < 0: %d, undetermined: %d;  |arg u| of the Re u > 0 roots: %s'
          % (len(rhp), len(lhp), und, '[%s]' % ', '.join(sorted(mid4(v) for v in rargs))))
    if rargs:
        print('|arg u| of the Re u > 0 roots: all in [%s, %s] (rounded outward)'
              % (round_down(exact_min(rargs), 8), round_up(exact_max(rargs), 8)))
    print('sup_r N(r)/r <= %s' % fixed_up(sup, 5))
    return 0


if __name__ == '__main__':
    sys.exit(main())
