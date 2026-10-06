"""(N) and (POS) for the exact Hermite member P_J (kernel Psi = (Xi^2)^): rigorous enclosure by an independent linear solve.

P_J(u) = 1 + sum_{k=1}^{2J} p_k u^k is defined by the 2J linear conditions
    Fhat_{Xi^2 P_J(t^2)}(xi_n) = 0,  Fhat'_{Xi^2 P_J(t^2)}(xi_n) = 0,   xi_n = log n/(2 pi),  n = the first J prime powers.
With Psi = (Xi^2)^ and t^{2k} <-> (-1)^k (2 pi)^{-2k} d^{2k}/dxi^{2k}, these read sum_k p_k m_k(xi_n) = 0 = sum_k p_k m_k'(xi_n),
    m_k = (-1)^k (2 pi)^{-2k} Psi^{(2k)},   m_k' = (-1)^k (2 pi)^{-2k} Psi^{(2k+1)}.
The moments Psi^{(j)}(xi_n), j <= 4J+1, are enclosed by the exact Bessel-operator form with P = 1 (lib/bessel_form.py),
rigorous K_0, K_1 (lib/besselk.py) and rigorous N-tails.  Rows and columns are scaled by exact powers of two and the
2J x 2J ball system is solved by Arb's arb_mat.solve (preconditioned).  The solve succeeds only if every matrix in the
ball is invertible, so success CERTIFIES (N) (the exact matrix is non-singular and P_J is unique); the output balls
contain the exact p_k.  (POS) is certified if every ball p_k has a positive lower bound.
With --ref, the run fails (exit code 1) unless every reference ball overlaps the new one (a corroboration check; the
certificate itself is the solve).  Also printed: a = max_k ((2k)! p_k)^{1/(2k)} and min_k p_k (bounds rounded outward, exact checks of the direction; the
maximal relative radius is printed as a rounded log10, an order of magnitude only), and, if a reference enclosure is
given, whether every reference ball overlaps the new ball (consistency with a second, independently computed enclosure).

Usage (from anc/):  python exact/verify_exact_member.py J --prec BITS [--workers W] [--ref FILE] [--out FILE]
"""
import argparse
import math
import multiprocessing as mp
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from flint import arb, arb_mat, ctx  # noqa: E402
from lib.bessel_form import FhatOperators, Evaluator  # noqa: E402
from lib.common import first_prime_powers, relpath, sha256_file, round_down, fixed_up, exact_max  # noqa: E402

G = {}


def node_moments(n):
    ctx.prec = G['prec']
    xi = arb(n).log() / (2 * arb.pi())
    d = G['EV'].derivs(xi, list(range(G['mm'] + 1)))
    digits = int(G['prec'] * 0.30103) + 20
    return n, [d[j].str(digits, radius=True, more=True) for j in range(G['mm'] + 1)]


def pow2(v):
    e = int(math.floor(-float(abs(v).mid().log()) / math.log(2)))
    return arb(2) ** e


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('J', type=int)
    ap.add_argument('--prec', type=int, required=True)
    ap.add_argument('--workers', type=int, default=1)
    ap.add_argument('--ref', default=None)
    ap.add_argument('--out', default=None)
    a = ap.parse_args()
    J, prec = a.J, a.prec
    t0 = time.time()
    ctx.prec = prec
    mm = 4 * J + 1
    FO = FhatOperators([arb(1)], mm, prec)
    EV = Evaluator(FO, prec, -int(prec * 0.30103) - 30)
    G.update(EV=EV, prec=prec, mm=mm)
    nodes = [n for n, _ in first_prime_powers(J)]
    print('J = %d: nodes = the first %d prime powers (2 ... %d); moments Psi^(j), j <= %d; %d bits; z_cut = %d'
          % (J, J, nodes[-1], mm, prec, EV.zcut()), flush=True)
    if a.workers > 1:
        with mp.get_context('fork').Pool(a.workers) as pool:
            res = dict(pool.map(node_moments, nodes))
    else:
        res = dict(map(node_moments, nodes))
    ctx.prec = prec
    PI = arb.pi()
    f = [(-1) ** k * (2 * PI) ** (-2 * k) for k in range(2 * J + 1)]
    M0, M1 = [], []
    for n in nodes:
        d = [arb(s) for s in res[n]]
        M0.append([f[k] * d[2 * k] for k in range(2 * J + 1)])
        M1.append([f[k] * d[2 * k + 1] for k in range(2 * J + 1)])
    acc = min(min(r[0].rel_accuracy_bits() for r in M0), min(r[0].rel_accuracy_bits() for r in M1))
    print('  moments done (%.0f s); min relative accuracy of m_0, m_0\' at the nodes: %d bits' % (time.time() - t0, acc),
          flush=True)
    m2 = 2 * J
    colsc = [pow2(arb(max(abs(M0[i][k].mid()) for i in range(J)))) for k in range(1, m2 + 1)]
    A = arb_mat(m2, m2)
    b = arb_mat(m2, 1)
    for i in range(J):
        r0 = pow2(arb(max(abs((M0[i][k] * colsc[k - 1]).mid()) for k in range(1, m2 + 1))))
        r1 = pow2(arb(max(abs((M1[i][k] * colsc[k - 1]).mid()) for k in range(1, m2 + 1))))
        for k in range(1, m2 + 1):
            A[2 * i, k - 1] = M0[i][k] * colsc[k - 1] * r0
            A[2 * i + 1, k - 1] = M1[i][k] * colsc[k - 1] * r1
        b[2 * i, 0] = -M0[i][0] * r0
        b[2 * i + 1, 0] = -M1[i][0] * r1
    try:
        y = A.solve(b, algorithm='precond')
        okN = True
    except ZeroDivisionError:
        okN = False
    print('(N)  rigorous solve of the %d x %d system succeeded (matrix certified non-singular): %s' % (m2, m2, okN),
          flush=True)
    if not okN:
        print('NOT CERTIFIED'); return 1
    pc = [arb(1)] + [y[k, 0] * colsc[k] for k in range(m2)]
    rr = max(float((c.rad() / abs(c.mid())).mid().log()) / math.log(10) for c in pc[1:])
    pos = all(c > 0 for c in pc)
    notpos = [k for k, c in enumerate(pc) if not (c > 0)]
    print('     enclosure of p_0..p_%d: max log10 relative radius %.0f' % (m2, rr))
    print('(POS) all %d coefficients p_k certified > 0: %s%s' % (m2 + 1, pos, '' if pos else ' (not: %s)' % notpos[:10]))
    if pos:
        kmin = 0
        for k in range(1, m2 + 1):                             # exact comparison of the lower endpoints
            if arb(pc[k].lower()) < arb(pc[kmin].lower()):
                kmin = k
        print('     min_k p_k >= %s (at k = %d);  p_1 in %s' % (round_down(pc[kmin], 4), kmin, pc[1].str(20)))
        aval = exact_max([(arb(math.factorial(2 * k)) * arb(c.upper())) ** (arb(1) / (2 * k)) for k, c in enumerate(pc) if k > 0])
        print('     a = max_k ((2k)! p_k)^(1/2k) <= %s' % fixed_up(aval, 6))
    if a.out:
        txt = '\n'.join(c.str(int(prec * 0.30103) + 10, radius=True) for c in pc) + '\n'
        open(a.out, 'w').write(txt)
        print('     enclosure written to %s (sha256 %s)' % (relpath(a.out), sha256_file(a.out)))
    if a.ref:
        ctx.prec = max(prec, 4000)
        ref = [arb(s) for s in open(a.ref).read().split('\n') if s.strip()]
        ov = len(ref) == len(pc) and all(u.overlaps(v) for u, v in zip(pc, ref))
        rr2 = max(float((c.rad() / abs(c.mid())).mid().log()) / math.log(10) for c in ref[1:])
        pos2 = all(c > 0 for c in ref)
        print('     reference enclosure %s (sha256 %s): max log10 rel radius %.0f; all p_k > 0: %s; '
              'every ball overlaps the new enclosure: %s' % (relpath(a.ref), sha256_file(a.ref), rr2, pos2, ov))
    print('CERTIFIED (N) and (POS) at J = %d: %s   (%.0f s)' % (J, bool(okN and pos), time.time() - t0))
    if a.ref and not ov:                                 # the corroboration was requested: its failure is a failure
        print('FAILED: corroboration: some ball of the reference enclosure does not overlap the new enclosure')
        return 1
    return 0 if (okN and pos) else 1


if __name__ == '__main__':
    sys.exit(main())
