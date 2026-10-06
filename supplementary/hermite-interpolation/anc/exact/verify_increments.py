"""Certified sign pattern of the coefficient increments p_k^{(J+1)} - p_k^{(J)} of consecutive exact members.

Inputs: certified enclosures of P_J and P_{J+1} (outputs of verify_exact_member.py; the balls contain the exact
coefficients).  For every k <= 2J the difference of the two balls is a ball containing the exact increment; its sign is
certified when the ball excludes 0.  Printed: the set of k with a certified negative increment, whether every other
k <= 2J has a certified positive increment, the signs of the two new top coefficients p_{2J+1}, p_{2J+2} of P_{J+1},
and the largest relative size |increment|/p_k^{(J)} among the negative increments (rounded up).

Usage (from anc/):  python exact/verify_increments.py BALL_J BALL_J+1 [--expect-negative 2,4,6,10,11]
"""
import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from flint import arb, ctx  # noqa: E402
from lib.common import relpath, sha256_file, round_up, require  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('ballJ')
    ap.add_argument('ballJ1')
    ap.add_argument('--expect-negative', default=None)
    a = ap.parse_args()
    ctx.prec = 4000
    P = [arb(s) for s in open(a.ballJ).read().split('\n') if s.strip()]
    P1 = [arb(s) for s in open(a.ballJ1).read().split('\n') if s.strip()]
    J = (len(P) - 1) // 2
    require((len(P1) - 1) // 2 == J + 1, 'the second enclosure must be of degree 2J + 2')
    print('P_J   enclosure %s (sha256 %s), J = %d' % (relpath(a.ballJ), sha256_file(a.ballJ), J))
    print('P_J+1 enclosure %s (sha256 %s)' % (relpath(a.ballJ1), sha256_file(a.ballJ1)))
    neg, pos, und = [], [], []
    worst = None
    for k in range(1, 2 * J + 1):
        d = P1[k] - P[k]
        if d < 0:
            neg.append(k)
            r = abs(d) / P[k]
            worst = r if worst is None or arb(r.upper()) > arb(worst.upper()) else worst
        elif d > 0:
            pos.append(k)
        else:
            und.append(k)
    top = [P1[2 * J + 1] > 0, P1[2 * J + 2] > 0]
    print('k = 1..%d: certified negative increments at k in %s; certified positive at the other %d values; undetermined: %s'
          % (2 * J, neg, len(pos), und))
    print('new top coefficients p_%d^(J+1) > 0: %s, p_%d^(J+1) > 0: %s' % (2 * J + 1, top[0], 2 * J + 2, top[1]))
    if worst is not None:
        print('largest relative negative increment |p_k^(J+1) - p_k^(J)| / p_k^(J) <= %s' % round_up(worst, 3))
    ok = not und and all(top)
    if a.expect_negative is not None:
        exp = [int(t) for t in a.expect_negative.split(',')]
        ok = ok and neg == exp
        print('negative set equals the expected %s: %s' % (exp, neg == exp))
    print('CERTIFIED: increment sign pattern (J = %d -> %d): %s' % (J, J + 1, ok))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
