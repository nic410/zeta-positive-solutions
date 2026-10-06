"""Certified upper bound for the slack kappa* from an explicit zero-killing function F_rep = Xi^2 (H + eps e^{-pi t^2}).

Object (fixed by the parameter file, exact rationals):
    F_rep(t) = Xi(t)^2 H(t) + eps Xi(t)^2 e^{-pi t^2},   H(t) = prod_{j<=J} (1 + r_j t^2 + s_j t^4).
Checked here:
  (1) H > 0 on R, exactly: s_j > 0 and r_j^2 < 4 s_j for every factor (exact rational arithmetic).  Hence F_rep >= 0 on R.
  (2) Fhat_rep >= 0 on [c, oo), c = log 2/(2 pi)  (Fhat_rep is even, so this gives |xi| >= c), where
      Fhat_rep = Fhat_H + eps (Psi * e^{-pi xi^2}) and the cushion is bounded below by eps e^{-pi(xi+delta)^2} I_delta
      (lib/cushion.py).  Fhat_H and its xi-derivatives are enclosed by the exact Bessel-operator form (lib/bessel_form.py)
      with rigorous K_0, K_1 (lib/besselk.py) and rigorous N-tails.
        * Node neighbourhoods: at every prime power n among the first J (where Fhat_H has a double zero up to the
          rationalisation of the parameters, including the edge n = 2, xi = c), a Taylor model of order p centred
          exactly at xi_n = log n/(2 pi) with the quadratic lower bound c_0 - c_1^2/(4 c_2'),
          c_2' = c_2 - sum_{k>=3} |c_k| h^{k-2} - M h^{p-1}/(p+1)!,  M >= sup |Fhat_H^{(p+1)}| on the neighbourhood.
        * Gaps between neighbourhoods (exact dyadic endpoints overlapping the neighbourhoods) and the last gap up to xi_far:
          Taylor models of order p at exact dyadic centres, lower bound c_0 - sum |c_k| r^k - M r^{p+1}/(p+1)! (or the
          quadratic bound), adaptive bisection.
        * Far region x >= x_far (x = e^{2 pi xi}): |Fhat_H| <= U(x) < cushion, and d/dz[log U - log cushion] <=
          (D + xi + delta)/z - 1 < 0 for z = 2 pi x >= 2 pi x_far > D + 4 with xi + delta < 3 at x_far (D = operator degree).
  (3) The explicit formula: F_rep vanishes at every nontrivial zero of zeta (on or off the line), so
          A(F_rep) = (1/pi) sum_{n>=2} Lambda(n) n^{-1/2} Fhat_H(log n/2pi) + eps A(Xi^2 e^{-pi t^2}).
      The prime-power sum is evaluated term by term up to x_far + 1 and the rest is bounded by a geometric tail
      (Lambda(n) <= log n, |Fhat_H| <= U); A(Xi^2 e^{-pi t^2}) is the rigorous archimedean value (lib/cushion.py).
  (4) kappa* <= A(F_rep)/Fhat_rep(0) <= A_upper / Fhat_H(0)_lower  (the cushion only increases Fhat_rep(0)),
      printed rounded UP to 8 significant digits (the rounding direction is checked exactly).

Usage (from anc/):
    python kappa/verify_kappa.py kappa/params/J40.json --prec 1000 --order 28 --workers 4
    [--order-far 64 --order-switch 121]   (Taylor order 64 for nodes/gaps with x >= 121; used at J = 100)
"""
import argparse
import json
import multiprocessing as mp
import os
import sys
import time
from math import factorial

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from flint import arb, fmpq, fmpz, ctx                                          # noqa: E402
from lib.common import (load_factor_params, eps_exponent, relpath, first_prime_powers,   # noqa: E402
                        prime_powers, round_up, round_down, require, exact_min)
from lib.bessel_form import build_P, FhatOperators, Evaluator                     # noqa: E402
from lib.cushion import cushion_A_upper, cushion_Id_lower                         # noqa: E402

DY = 200                       # dyadic endpoints k / 2^DY
S_DY = fmpz(2) ** DY
G = {}                         # state shared with forked workers


def dyarb(k):
    return arb(fmpq(k, S_DY))


def dy(v, up):
    """Exact dyadic k with k/2^DY >= v (up) or <= v (down)."""
    w = v * arb(2) ** DY
    return int((arb(w.upper()).ceil() if up else arb(w.lower()).floor()).unique_fmpz())


def cushion_lower(xi_hi):
    """Lower bound of eps (Psi * e^{-pi xi^2}) on [0, xi_hi] (the bound is decreasing in xi >= 0)."""
    return G['eps'] * (-arb.pi() * (arb(xi_hi) + G['delta']) ** 2).exp() * G['Id']


def order_at(x):
    return G['p_far'] if (G['switch'] is not None and x >= G['switch']) else G['p']


def zero_nbhd(i):
    """Certify Fhat_rep >= 0 on a neighbourhood of the i-th killed prime power; returns dyadic inner endpoints."""
    ctx.prec = G['prec']
    EV = G['EV']
    n = G['killed'][i]
    p = order_at(n)
    PI = arb.pi()
    xin = arb(n).log() / (2 * PI)
    gaps = []
    if i + 1 < len(G['killed']):
        gaps.append((arb(G['killed'][i + 1]).log() - arb(n).log()) / (2 * PI))
    if i > 0:
        gaps.append((arb(n).log() - arb(G['killed'][i - 1]).log()) / (2 * PI))
    h = arb(min([0.004] + [float(g.mid()) / 3 for g in gaps]))
    der = EV.derivs(xin, list(range(p + 1)))                   # full accuracy at the node centre
    cs = [der[k] / factorial(k) for k in range(p + 1)]
    while True:
        lo = xin if n == 2 else xin - h                         # at n = 2 only [c, c + h] is needed
        hi = xin + h
        M = EV.sup_abs(p + 1, lo, hi)
        c2p = cs[2] - sum((abs(cs[k]) * h ** (k - 2) for k in range(3, p + 1)), arb(0)) - M * h ** (p - 1) / factorial(p + 1)
        if c2p > 0:
            lb = cs[0] - cs[1] ** 2 / (4 * c2p) + cushion_lower(hi)
            if lb > 0:
                return dict(i=i, n=n, p=p, lo=dy(xin - h, True), hi=dy(xin + h, False), h=float(h.mid()),
                            lb=lb.str(5), c0=cs[0].str(3), c1=cs[1].str(3), c2=cs[2].str(3), ok=True)
        h = h / 2
        if h < arb('1e-12'):
            return dict(i=i, n=n, ok=False)


def lb_piece(a, b, p):
    """Lower bound of Fhat_rep on [a, b] (exact dyadic arbs)."""
    EV = G['EV']
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
    return best + cushion_lower(b)


def cover_gap(task):
    """Cover the gap [a0, b0] (dyadic numerators) by certified pieces with bisection."""
    gi, a0, b0, x_left = task
    ctx.prec = G['prec']
    p = order_at(x_left)
    width = float(dyarb(b0 - a0).mid())
    k = max(1, int(width / 0.004) + 1)
    edges = [a0 + ((b0 - a0) * j) // k for j in range(k)] + [b0]
    stack = [(edges[j], edges[j + 1], 0) for j in range(k)][::-1]
    npieces, minlb = 0, None
    while stack:
        a, b, dep = stack.pop()
        lb = lb_piece(dyarb(a), dyarb(b), p)
        npieces += 1
        if lb > 0:
            lo = arb(lb.lower())
            minlb = lo if minlb is None or lo < minlb else minlb
            continue
        if dep > 30 or b - a < 2:
            return dict(gi=gi, ok=False, pieces=npieces, fail='[%s, %s] lb %s' % (dyarb(a).str(15), dyarb(b).str(15), lb.str(4)))
        m = (a + b) // 2
        stack += [(m, b, dep + 1), (a, m, dep + 1)]
    return dict(gi=gi, ok=True, pieces=npieces, p=p, minlb=round_down(minlb, 8) if minlb is not None else None)


def prime_term(np_):
    """Lambda(n) n^{-1/2} Fhat_H(xi_n), as a decimal ball string (Arb prints an enclosing ball)."""
    n, prime = np_
    ctx.prec = G['prec']
    xi = arb(n).log() / (2 * arb.pi())
    v = arb(prime).log() / arb(n).sqrt() * G['EV'].derivs(xi, [0])[0]
    return n, v.str(G['prec'] // 3, radius=True, more=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('params')
    ap.add_argument('--prec', type=int, required=True)
    ap.add_argument('--order', type=int, default=28)
    ap.add_argument('--order-far', type=int, default=None)
    ap.add_argument('--order-switch', type=int, default=None)
    ap.add_argument('--workers', type=int, default=1)
    a = ap.parse_args()
    t0 = time.time()
    meta, rs, fsha = load_factor_params(a.params)
    J = len(rs)
    e2 = eps_exponent(meta['eps'])
    print('parameter file  : %s' % relpath(a.params))
    print('  file sha256   : %s' % fsha)
    print('  factors sha256: %s (canonical list, checked)' % meta['factors_sha256'])
    print('J = %d, eps = 1e-%d, working precision %d bits, Taylor order %d%s, workers %d'
          % (J, e2, a.prec, a.order, (', order %d for x >= %d' % (a.order_far, a.order_switch)) if a.order_far else '',
             a.workers), flush=True)
    # (1) H > 0 exactly
    okH = all(s > 0 and r * r < 4 * s for r, s in rs)
    print('(1) H > 0 on R (exact: s_j > 0, r_j^2 < 4 s_j for all j): %s' % okH, flush=True)
    # operators
    pmax = max(a.order, a.order_far or 0)
    P = build_P(rs, a.prec + 300)
    ctx.prec = a.prec
    FO = FhatOperators(P.coeffs(), pmax + 1, a.prec)
    EV = Evaluator(FO, a.prec, -(e2 + 40))
    ctx.prec = a.prec
    PI = arb.pi()
    Id, delta = cushion_Id_lower()
    Acush, Acush_im = cushion_A_upper()
    ctx.prec = a.prec
    G.update(EV=EV, prec=a.prec, p=a.order, p_far=a.order_far, switch=a.order_switch, eps=arb(fmpq(1, 10 ** e2)),
             Id=Id, delta=delta, killed=[n for n, _ in first_prime_powers(J)])
    print('    operator degree D = %d, N-truncation z_cut = %d (setup %.1f s)' % (FO.deg, EV.zcut(), time.time() - t0))
    print('    cushion: I_delta = int_{-1/20}^{1/20} Psi >= %s;  A(Xi^2 e^{-pi t^2}) in %s' % (Id.str(12), Acush.str(15)),
          flush=True)
    pool = mp.get_context('fork').Pool(a.workers) if a.workers > 1 else None
    imap = pool.imap if pool else map
    # (2a) node neighbourhoods
    nodes = list(imap(zero_nbhd, range(J)))
    okN = all(r['ok'] for r in nodes)
    print('(2a) node neighbourhoods (centred at the %d killed prime powers 2..%d):' % (J, G['killed'][-1]))
    for r in nodes:
        if not r['ok']:
            print('    FAIL at n = %d' % r['n'])
        elif r['i'] % 10 == 0 or r['i'] == J - 1:
            print('    n = %4d: h = %.2e, Fhat_H(xi_n) = %s, Fhat_H\'(xi_n) = %s, c_2 = %s, lower bound with cushion %s'
                  % (r['n'], r['h'], r['c0'], r['c1'], r['c2'], r['lb']))
    if not okN:
        print('NOT CERTIFIED'); return 1
    minlbN = exact_min([arb(arb(r['lb']).lower()) for r in nodes])
    maxc0 = max(abs(arb(r['c0'])).upper() for r in nodes)
    print('    all %d neighbourhoods certified; min lower bound %s; max |Fhat_H(xi_n)| <= %s (%.0f s)'
          % (J, round_down(minlbN, 4), round_up(arb(maxc0), 3), time.time() - t0), flush=True)
    # (2c) far region
    D0 = FO.deg
    xfar = None
    for xc in range(G['killed'][-1] + 2, 100000):
        if 2 * PI * xc < D0 + 4:
            continue
        if EV.U_bound(arb(xc)) < cushion_lower(arb(xc).log() / (2 * PI)):
            xfar = xc
            break
    require(xfar is not None and 2 * PI * xfar > D0 + 4 and arb(xfar).log() / (2 * PI) + delta < 3,
            'far field: needs 2 pi x_far > D + 4 and xi_far + delta < 3')
    print('(2c) far region: x_far = %d, U(x_far) = %s < cushion(x_far) = %s; monotone beyond (2 pi x_far > D + 4)'
          % (xfar, EV.U_bound(arb(xfar)).str(3), cushion_lower(arb(xfar).log() / (2 * PI)).str(3)), flush=True)
    # (2b) gaps
    nodes.sort(key=lambda r: r['i'])
    tasks = [(k, nodes[k]['hi'], nodes[k + 1]['lo'], nodes[k]['n']) for k in range(J - 1)]
    tasks.append((J - 1, nodes[-1]['hi'], dy(arb(xfar).log() / (2 * PI), True), nodes[-1]['n']))
    for _, lo, hi, _ in tasks:
        require(lo < hi, 'neighbourhoods overlap')
    order = sorted(range(len(tasks)), key=lambda k: -tasks[k][3])        # large x first (slowest)
    gres = list(pool.imap_unordered(cover_gap, [tasks[k] for k in order]) if pool else map(cover_gap, tasks))
    okG = all(r['ok'] for r in gres)
    npieces = sum(r['pieces'] for r in gres)
    for r in gres:
        if not r['ok']:
            print('    FAIL in gap %d: %s' % (r['gi'], r['fail']))
    if not okG:
        print('NOT CERTIFIED'); return 1
    minlbG = exact_min([arb(r['minlb']) for r in gres])
    print('(2b) gaps [c, xi_far] minus neighbourhoods: %d pieces, all certified; min lower bound %s (%.0f s)'
          % (npieces, round_down(minlbG, 4), time.time() - t0), flush=True)
    print('    => Fhat_rep >= 0 on [c, oo)', flush=True)
    # (3) A(F_rep)
    pps = prime_powers(xfar + 1)
    terms = list(imap(prime_term, pps))
    if pool:
        pool.close()
    ctx.prec = a.prec
    Ftot = arb(0)
    for n, s in terms:
        Ftot += arb(s)
    n1 = xfar + 2
    qq = (arb(n1 + 1) / n1) ** D0 * (-2 * PI).exp() * (arb(n1 + 1).log() / arb(n1).log())
    require(qq < arb('0.5'), 'prime-power tail: ratio bound must be < 1/2')
    tailH = arb(n1).log() * EV.U_bound(arb(n1)) / (1 - qq)
    S_H = Ftot / PI                                       # truncated prime-power sum over n <= x_far + 1
    A_H = S_H + arb(0, tailH.upper()) / PI                # A(Xi^2 H): the truncated sum plus the enclosure of the tail
    eps = G['eps']
    A_up = arb((A_H + eps * arb(Acush.upper())).upper())  # the same operations as before: the tail is added once
    F0 = EV.derivs_rel(arb(0), [0], arb(10) ** -40)[0]
    kap = A_up / arb(F0.lower())
    print('(3) prime-power sum over n <= %d (%d terms): S(Xi^2 H) = %s  (truncated)' % (xfar + 1, len(pps), S_H.str(15)))
    print('    tail n >= %d: <= %s;  eps A(cushion) <= %s' % (n1, round_up(tailH / PI, 3), round_up(eps * Acush, 5)))
    print('    A(Xi^2 H) = S(Xi^2 H) + tail in %s' % A_H.str(15))
    print('    A(F_rep) <= %s' % round_up(A_up, 12))
    print('    Fhat_H(0) = %s  (Fhat_rep(0) >= Fhat_H(0))' % F0.str(20))
    print('    cushion-free ratio A(Xi^2 H)/Fhat_H(0) = %s' % (A_H / F0).str(12))
    cert = bool(okH and okN and okG and F0 > 0 and kap > 0)
    res = dict(J=J, param_file=relpath(a.params), param_file_sha256=fsha, factors_sha256=meta['factors_sha256'],
               eps='1e-%d' % e2, prec=a.prec, order=a.order, order_far=a.order_far, order_switch=a.order_switch,
               H_positive=okH, nodes_ok=okN, pieces=npieces, x_far=xfar, S_trunc=S_H.str(15), A_H=A_H.str(15),
               A_upper=round_up(A_up, 12),
               Fhat0=F0.str(20), kappa_upper=round_up(kap, 8), kappa_upper_12=round_up(kap, 12), certified=cert,
               secs=round(time.time() - t0, 1))
    print('(4) kappa* <= A_upper / Fhat_H(0)_lower <= %s   (rounded up; 12 digits: %s)'
          % (res['kappa_upper'], res['kappa_upper_12']))
    print('CERTIFIED: %s   [J = %d, total %.0f s]' % (cert, J, time.time() - t0))
    print(json.dumps(res), flush=True)
    return 0 if cert else 1


if __name__ == '__main__':
    sys.exit(main())
