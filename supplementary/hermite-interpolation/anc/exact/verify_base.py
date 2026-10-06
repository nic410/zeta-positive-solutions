"""Base data (B) for the exact Hermite member P_J, from a certified enclosure of its coefficients:

    (i)  Fhat_J''(xi_n) > 0 at every prime power n <= X;
    (ii) Fhat_J(xi) >= theta * Psi_1(xi) * min(1, d(x)^2)   for xi in [xi_2, xi_X],   x = e^{2 pi xi},  d(x) = dist(x, PP),

where Fhat_J = (Xi^2 P_J(t^2))^ and Psi_1(xi) = 2 pi sqrt(x) W_0(2 pi x), W_0(z) = z^2[(z^2+9) K_0(z) - 6 z K_1(z)] (the N = 1 term
of Psi).  All prime powers n <= X must be nodes of P_J (X <= n_J).

Method (Arb ball arithmetic; lib/bessel_form.py with the ball coefficients of P_J):
  * Nodes.  For the exact member, Fhat_J(xi_n) = Fhat_J'(xi_n) = 0 exactly (the defining Hermite conditions), so with the
    Taylor coefficients c_k at xi_n (balls valid for the exact P_J), for |u| <= h:
        Fhat_J(xi_n + u) >= u^2 c_2',   c_2' = c_2 - sum_{k>=3} |c_k| h^{k-2} - M h^{p-1}/(p+1)!,   M >= sup |Fhat^{(p+1)}|.
    For |u| <= h, d(x) = |x - n| (h <= one third of the neighbouring xi-gaps keeps n the nearest prime power, as all
    xi-gaps here are < 0.22) and |x - n| <= n |u| (e^{2 pi h} - 1)/h, so (ii) holds on the neighbourhood if
        c_2' >= theta * sup Psi_1 * n^2 ((e^{2 pi h} - 1)/h)^2.
    (i) is c_2 > 0.  At n = 2 only u >= 0 and at n = X only u <= 0 are needed.
    Precondition check: c_0 = c_1 = 0 is used, not computed, so the input must be the certified enclosure of the exact
    member (output of verify_exact_member.py; its sha256 is printed).  As a consistency check, the computed balls c_0, c_1
    must contain 0 and have radius <= 2^(-B/4) c_2 h^2 resp. 2^(-B/4) c_2 h at every node; otherwise NOT CERTIFIED.
  * Gaps (n_i, n_{i+1}).  Pieces with exact dyadic endpoints overlapping the neighbourhoods, adaptive bisection: lower
    bound of Fhat_J from a Taylor model of order p (as in kappa/verify_kappa.py, no cushion), against the upper bound
    theta * sup Psi_1 * min(1, dmax^2), dmax = min(x_hi - n_i, n_{i+1} - x_lo).
  * sup Psi_1 on [x_lo, x_hi] <= 2 pi sqrt(x_hi) z_hi^2 (z_hi^2 + 9) K_0(z_lo) - 2 pi sqrt(x_lo) 6 z_lo^3 K_1(z_hi), z = 2 pi x
    (K_0, K_1 decreasing).

Usage (from anc/):  python exact/verify_base.py BALLFILE --X 199 --theta 0.787979 --prec 1800 [--order 28] [--workers W]
"""
import argparse
import multiprocessing as mp
import os
import sys
import time
from fractions import Fraction
from math import factorial

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from flint import arb, fmpq, fmpz, ctx  # noqa: E402
from lib.bessel_form import FhatOperators, Evaluator  # noqa: E402
from lib.besselk import K01  # noqa: E402
from lib.common import relpath, sha256_file, prime_powers, first_prime_powers, round_down, require  # noqa: E402

DY = 200
S_DY = fmpz(2) ** DY
G = {}


def dyarb(k):
    return arb(fmpq(k, S_DY))


def dy(v, up):
    w = v * arb(2) ** DY
    return int((arb(w.upper()).ceil() if up else arb(w.lower()).floor()).unique_fmpz())


def psi1_upper(x_lo, x_hi):
    PI = arb.pi()
    zl = arb((2 * PI * x_lo).lower())
    zh = arb((2 * PI * x_hi).upper())
    K0l, _ = K01(zl, 64)
    _, K1h = K01(zh, 64)
    v = (2 * PI * arb(x_hi).sqrt() * zh * zh * (zh * zh + 9) * arb(K0l.upper())
         - 2 * PI * arb(x_lo).sqrt() * 6 * zl ** 3 * arb(K1h.lower()))
    return arb(v.upper())


def node_task(i):
    ctx.prec = G['prec']
    EV, p, theta, nodes = G['EV'], G['p'], G['theta'], G['nodes']
    PI = arb.pi()
    n = nodes[i]
    xin = arb(n).log() / (2 * PI)
    gaps = []
    if i + 1 < len(nodes):
        gaps.append((arb(nodes[i + 1]).log() - arb(n).log()) / (2 * PI))
    if i > 0:
        gaps.append((arb(n).log() - arb(nodes[i - 1]).log()) / (2 * PI))
    h = arb(min([0.004] + [float(g.mid()) / 3 for g in gaps]))
    der = EV.derivs(xin, list(range(p + 1)))
    cs = [der[k] / factorial(k) for k in range(p + 1)]
    second = 2 * cs[2]                                         # Fhat''(xi_n)
    if not (second > 0):
        return dict(i=i, n=n, ok=False, why='Fhat\'\'(xi_n) not certified > 0')
    if not zero_balls(cs, cs[2], h):
        return dict(i=i, n=n, ok=False, why='precondition Fhat_J(xi_n) = Fhat_J\'(xi_n) = 0 not met by the input enclosure: '
                    'computed %s, %s' % (cs[0].str(3), cs[1].str(3)))
    left = n != nodes[0]
    right = n != G['X']
    while True:
        lo = xin - h if left else xin
        hi = xin + h if right else xin
        M = EV.sup_abs(p + 1, lo, hi)
        c2p = cs[2] - sum((abs(cs[k]) * h ** (k - 2) for k in range(3, p + 1)), arb(0)) - M * h ** (p - 1) / factorial(p + 1)
        x_lo = arb(((2 * PI * lo).exp()).lower())
        x_hi = arb(((2 * PI * hi).exp()).upper())
        rhs = theta * psi1_upper(x_lo, x_hi) * n * n * (((2 * PI * h).exp() - 1) / h) ** 2
        if c2p > rhs:
            return dict(i=i, n=n, ok=True, lo=dy(xin - h, True), hi=dy(xin + h, False), h=float(h.mid()),
                        fpp=second.str(5), ratio=(c2p / rhs).str(4),
                        c0=cs[0].str(3), c1=cs[1].str(3))
        h = h / 2
        if h < arb('1e-14'):
            return dict(i=i, n=n, ok=False, why='neighbourhood not certified')


def zero_balls(cs, scale, h):
    """Precondition check at a node: the input must enclose the exact member, for which c_0 = c_1 = 0 exactly.  The
    computed balls c_0, c_1 must contain 0 and be negligible against the quadratic term: radius <= 2^(-B/4) |scale| h^2
    resp. 2^(-B/4) |scale| h.  (A perturbed or widened enclosure fails here.)"""
    tol = arb(2) ** (-(G['prec'] // 4)) * arb(abs(scale).lower())
    return bool(cs[0].contains(0) and cs[1].contains(0)
                and arb(cs[0].rad()) <= tol * h * h and arb(cs[1].rad()) <= tol * h)


def lb_piece(a, b):
    EV, p = G['EV'], G['p']
    xi0 = (a + b) / 2
    r = (b - a) / 2
    der = EV.derivs_rel(xi0, list(range(p + 1)))
    cs = [der[k] / factorial(k) for k in range(p + 1)]
    M = EV.sup_abs(p + 1, a, b)
    best = cs[0] - sum((abs(cs[k]) * r ** k for k in range(1, p + 1)), arb(0)) - M * r ** (p + 1) / factorial(p + 1)
    c2p = cs[2] - sum((abs(cs[k]) * r ** (k - 2) for k in range(3, p + 1)), arb(0)) - M * r ** (p - 1) / factorial(p + 1)
    if c2p > 0:
        q1 = cs[0] - cs[1] ** 2 / (4 * c2p)
        if q1.lower() > best.lower():
            best = q1
    return best


def gap_task(task):
    gi, a0, b0, nl, nr = task
    ctx.prec = G['prec']
    theta = G['theta']
    PI = arb.pi()
    width = float(dyarb(b0 - a0).mid())
    k = max(1, int(width / 0.002) + 1)
    edges = [a0 + ((b0 - a0) * j) // k for j in range(k)] + [b0]
    stack = [(edges[j], edges[j + 1], 0) for j in range(k)][::-1]
    npieces, worst = 0, None
    while stack:
        a, b, dep = stack.pop()
        A, B = dyarb(a), dyarb(b)
        x_lo = arb(((2 * PI * A).exp()).lower())
        x_hi = arb(((2 * PI * B).exp()).upper())
        d1, d2 = arb((x_hi - nl).upper()), arb((nr - x_lo).upper())      # d(x) <= min(d1, d2) on the piece
        dmax = d1 if d1 < d2 else d2
        m_up = arb(1) if dmax >= 1 else arb((dmax * dmax).upper())
        rhs = theta * psi1_upper(x_lo, x_hi) * m_up
        lb = lb_piece(A, B)
        npieces += 1
        if lb > rhs:
            q = lb / rhs
            worst = q if worst is None or arb(q.lower()) < arb(worst.lower()) else worst
            continue
        if dep > 40 or b - a < 2:
            return dict(gi=gi, ok=False, pieces=npieces, fail='[%s, %s]' % (dyarb(a).str(12), dyarb(b).str(12)))
        m = (a + b) // 2
        stack += [(m, b, dep + 1), (a, m, dep + 1)]
    return dict(gi=gi, ok=True, pieces=npieces, worst=arb(worst.lower()).str(40, radius=True, more=True))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('ball')
    ap.add_argument('--X', type=int, required=True)
    ap.add_argument('--theta', required=True)
    ap.add_argument('--prec', type=int, required=True)
    ap.add_argument('--order', type=int, default=28)
    ap.add_argument('--workers', type=int, default=1)
    a = ap.parse_args()
    t0 = time.time()
    ctx.prec = a.prec
    P = [arb(s) for s in open(a.ball).read().split('\n') if s.strip()]
    J = (len(P) - 1) // 2
    killed = [n for n, _ in first_prime_powers(J)]
    nodes = [n for n, _ in prime_powers(a.X)]
    require(nodes[-1] == a.X and all(n in killed for n in nodes), 'every prime power <= X must be a node of P_J')
    fr = Fraction(a.theta)
    theta = arb(fmpq(fr.numerator, fr.denominator))
    FO = FhatOperators(P, a.order + 1, a.prec)
    EV = Evaluator(FO, a.prec, -int(a.prec * 0.30103) - 30)
    ctx.prec = a.prec
    G.update(EV=EV, prec=a.prec, p=a.order, theta=theta, nodes=nodes, X=a.X)
    print('P-enclosure %s (sha256 %s): J = %d; region [xi_2, xi_X], X = %d (%d nodes); theta = %s; %d bits, Taylor order %d'
          % (relpath(a.ball), sha256_file(a.ball), J, a.X, len(nodes), a.theta, a.prec, a.order), flush=True)
    pool = mp.get_context('fork').Pool(a.workers) if a.workers > 1 else None
    res = list(pool.imap(node_task, range(len(nodes))) if pool else map(node_task, range(len(nodes))))
    okN = all(r['ok'] for r in res)
    for r in res:
        if not r['ok']:
            print('  FAIL at node %d: %s' % (r['n'], r['why']))
        elif r['i'] % 10 == 0 or r['n'] == a.X:
            print('  node %4d: Fhat\'\'(xi_n) = %s;  h = %.2e;  c_2\'/(theta sup Psi_1 n^2 ((e^{2 pi h}-1)/h)^2) = %s;  '
                  '[computed Fhat(xi_n) = %s, Fhat\'(xi_n) = %s: zero balls]' % (r['n'], r['fpp'], r['h'], r['ratio'], r['c0'], r['c1']))
    if not okN:
        print('NOT CERTIFIED'); return 1
    print('(i) Fhat\'\'(xi_n) > 0 at all %d nodes n <= %d; node neighbourhoods certified (%.0f s)'
          % (len(nodes), a.X, time.time() - t0), flush=True)
    tasks = [(k, res[k]['hi'], res[k + 1]['lo'], nodes[k], nodes[k + 1]) for k in range(len(nodes) - 1)]
    for t in tasks:
        require(t[1] < t[2], 'neighbourhoods overlap')
    gres = list(pool.imap_unordered(gap_task, tasks[::-1]) if pool else map(gap_task, tasks))
    if pool:
        pool.close()
    okG = all(r['ok'] for r in gres)
    for r in gres:
        if not r['ok']:
            print('  FAIL in gap %d at %s' % (r['gi'], r['fail']))
    if not okG:
        print('NOT CERTIFIED'); return 1
    worst_r = None
    for r in gres:                                             # exact comparison of the lower endpoints
        if worst_r is None or arb(arb(r['worst']).lower()) < arb(arb(worst_r['worst']).lower()):
            worst_r = r
    worst, worst_gap = arb(worst_r['worst']), worst_r['gi']
    print('(ii) all %d gaps certified: %d pieces; min over pieces of lower(Fhat)/upper(theta Psi_1 min(1,d^2)) = %s '
          '(gap %d-%d)' % (len(tasks), sum(r['pieces'] for r in gres), round_down(worst, 6), nodes[worst_gap], nodes[worst_gap + 1]))
    print('CERTIFIED: Fhat_J >= %s Psi_1 min(1, d^2) on [xi_2, xi_%d] and Fhat_J\'\' > 0 at the nodes (J = %d): True   (%.0f s)'
          % (a.theta, a.X, J, time.time() - t0))
    return 0


if __name__ == '__main__':
    sys.exit(main())
