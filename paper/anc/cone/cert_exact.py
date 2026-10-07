"""Cushion-free certificate that the EXACT Hermite member F_J = Xi^2 P_J(t^2) (Prop 4.5 of the paper) lies in the cone C.

Numbering of the paper: Def 2.1 (test class T), Lemma 2.3 (explicit formula on T, unconditional), Def 2.4 (cone C),
Lemma 2.5 (weak duality), Lemma 4.1 (Psi > 0), Prop 4.2 (Bessel form), Cor 4.4 (explicit formula for zero-killing F),
Prop 4.5 (exact family), Lemma 4.6 (integral representation), Prop 5.6 (certified enclosures, POS), Lemma A.3 (K).

Input: a ball enclosure of the coefficient vector (p_0 = 1, p_1, ..., p_{2J}) of the exact P_J, one Arb ball per line
(Prop 5.6: exact/out/P{J}_ball.txt, produced by exact/verify_exact_member.py; the rigorous solve proves that the balls
contain the exact coefficients).  Its sha256 is printed and, with --sha, checked.

The clauses of F_J in C (Def 2.4: F in T, F >= 0 on R, Fhat >= 0 on [xi_2, oo)):
 (T)    F_J in T: F_J is even and real on R (Xi is, P_J has real coefficients), entire, and Xi^2 P(t^2) in T_delta for every
        polynomial P and delta in (0, 1/2) by Sec 4.1 of the paper (bound (4.1) for Xi).  A theorem, not a computation.
 (POS)  every p_k > 0 (Prop 5.6; re-checked here on the same balls)  =>  P_J >= 1 on [0, oo), F_J >= Xi^2 >= 0 on R.
 (W)    Fhat_J >= 0 on [xi_2, oo), certified as follows (every step in Arb ball arithmetic; a sign is accepted only if the
        ball excludes 0):
 (BF)   Far field (from Lemma 4.6): with Q(y) = e^y P_J(-(theta+1/2)^2) theta^2 (theta+1)^2 e^{-y},
        G_0(z) = int_z^oo Q(y) e^{-y} (y^2 - z^2)^{-1/2} dy and Fhat_J(xi) = 2 pi sqrt(x) sum_N d(N) G_0(2 pi N x).
        If every Taylor coefficient of Q at y_0 = 2 pi x_0 is > 0, then Q > 0 on [y_0, oo), so G_0 > 0 on [y_0, oo) and
        Fhat_J > 0 for x >= x_0 (every divisor term is evaluated at 2 pi N x >= y_0).
 (NODE) Jet subtraction at each of the J cancelled prime powers n (x = n, xi_n = log n / 2 pi): for the exact member
        Fhat_J(xi_n) = Fhat_J'(xi_n) = 0 EXACTLY (definition of P_J), so on |d| <= h
            Fhat_J(xi_n + d) = d^2 [ c_2 + c_3 d + ... + c_p d^{p-2} + R d^{p-1} ],   |R| <= sup|Fhat_J^{(p+1)}| / (p+1)!,
        c_k = Fhat_J^{(k)}(xi_n)/k! (balls containing the exact values).  If the Bernstein lower bound of the bracket's
        polynomial part on [0, h] and on [-h, 0] exceeds M h^{p-1}/(p+1)!, then Fhat_J > 0 on 0 < |d| <= h, and the zero at
        xi_n has order exactly 2.  No cushion: the enclosures of c_0, c_1 (balls around 0) are not used; they are printed and
        checked to contain 0, a flag that only detects gross input errors (e.g. a wrong coefficient file).  The validity of
        the certificate rests on Prop 5.6 (the certified preconditioned solve: the input balls contain the exact P_J) and on
        c_0 = c_1 = 0 for the exact member (Prop 4.5).  For n = 2 and --xmin 2 only d >= 0 is needed.
 (GAP)  Every remaining piece [a, b] (exact dyadic endpoints, adaptive bisection): Taylor model of order p at the exact
        centre, lower bound = Bernstein lower bound of the Taylor polynomial on [-r, r] - M r^{p+1}/(p+1)!  > 0.
 (COVER) The node neighbourhoods (inner dyadic endpoints), the gap pieces and [x_0, oo) cover [xi_min, oo) (checked exactly).
 => W_J: Fhat_J >= 0 on [xi_min, oo), = 0 exactly at the J nodes (double zeros), > 0 elsewhere.  With xi_min = xi_2 this is
    the last clause of F_J in C (exact, cushion-free); with --xmin 1 also on [1, 2).
 (A)    Optional (--cost NMAX).  F_J = Xi^2 H_J vanishes at every non-trivial zero of zeta (on or off the line), so by Lemma 2.3
        and Cor 4.4 (no hypothesis on the zeros), and Prop 4.5 (Fhat_J(xi_n) = 0 for n <= n_J),
            A(F_J) = (1/pi) sum_{n in PP, n > n_J} Lambda(n) n^{-1/2} Fhat_J(xi_n).
        Terms n_J < n <= NMAX are enclosed (Lambda(n) = log p exactly); every term is >= 0 by W_J, so the truncated sum is a
        lower bound; the rest is <= (1/pi) log(n1) U(n1)/(1 - q), n1 = NMAX + 1, with U the far bound of Appendix A of the paper
        (|Fhat_J(xi)| <= U(x) = 4 pi (|A_0|+|B_0|)(2 pi x) e^{-2 pi x}(1 + 1/(2 pi x))/(1 - 2^D e^{-2 pi x})) and q >= the ratio of
        consecutive bounds log(n) U(n) (checked < 1/2).  int F_J = Fhat_J(0) is enclosed.  Consequences printed:
        kappa* <= A(F_J)/int F_J (Def 2.4, F_J in C), and int Xi^2 dmu <= int F_J dmu <= A(F_J) for every admissible pair
        (Lemma 2.5 and F_J >= Xi^2), as in Cor 5.3.

Usage:  python cone/cert_exact.py J --pball FILE --prec BITS [--order 28] [--order-far 64 --order-switch 121] [--xmin 2]
        [--workers 4] [--kback trap|series] [--sha SHA256] [--cost NMAX] [--json OUT]
"""
import argparse
import json
import math
import multiprocessing as mp
import os
import platform
import sys
import time
from math import factorial

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import conelib as L                                                                  # noqa: E402
from flint import arb, fmpq, fmpz, ctx                                              # noqa: E402
from lib.common import first_prime_powers, prime_powers, round_up, round_down, require, exact_min   # noqa: E402

DY = 200
S_DY = fmpz(2) ** DY
G = {}


def dyarb(k):
    return arb(fmpq(k, S_DY))


def dy(v, up):
    w = v * arb(2) ** DY
    return int((arb(w.upper()).ceil() if up else arb(w.lower()).floor()).unique_fmpz())


def order_at(x):
    return G['p_far'] if (G['switch'] is not None and x >= G['switch']) else G['p']


def node_item(i):
    """Certify Fhat_J > 0 on a punctured neighbourhood of the i-th node (jet subtraction).  Returns inner dyadic endpoints."""
    ctx.prec = G['prec']
    E = G['E']
    n = G['nodes'][i]
    p = order_at(n)
    PI = arb.pi()
    xin = arb(n).log() / (2 * PI)
    one_sided = (n == 2 and G['xmin'] == 2)
    der, Nu = E.derivs(xin, list(range(0, p + 1)), rel=G['rel'], mchk=[2, p])
    c = [der[k] / factorial(k) for k in range(p + 1)]
    jets0 = bool(c[0].contains(0) and c[1].contains(0))
    gaps = []
    nodes = G['nodes']
    if i + 1 < len(nodes):
        gaps.append(float(((arb(nodes[i + 1]).log() - arb(n).log()) / (2 * PI)).mid()))
    if i > 0:
        gaps.append(float(((arb(n).log() - arb(nodes[i - 1]).log()) / (2 * PI)).mid()))
    else:
        gaps.append(float(xin.mid()))
    h = arb(min([G['hmax']] + [0.45 * g for g in gaps]))
    a = c[2:]                                       # bracket polynomial: c_2 + c_3 d + ... + c_p d^{p-2}
    tries = 0
    while True:
        tries += 1
        hd = arb(fmpq(dy(h, False), S_DY))           # exact dyadic h (rounded down)
        lo = xin if one_sided else xin - hd
        hi = xin + hd
        M = E.sup_abs(p + 1, lo, hi)
        rem = M * hd ** (p - 1) / factorial(p + 1)
        lbp = L.bern_lower(a, hd)
        lbm = None if one_sided else L.bern_lower([x if k % 2 == 0 else -x for k, x in enumerate(a)], hd)
        lb = lbp if (lbm is None or lbp < lbm) else lbm
        q = lb - rem
        if c[2] > 0 and q > 0:
            return dict(i=i, n=n, p=p, ok=True, jets0=jets0, h=float(hd.mid()), tries=tries, N=Nu,
                        lo=(None if one_sided else dy(xin - hd, True)), hi=dy(xin + hd, False),
                        c0=c[0].str(3), c1=c[1].str(3), c2=c[2].str(8), qlow=round_down(q, 6),
                        relq=float((q / c[2]).mid()))
        h = h / 2
        if h < arb('1e-15') or tries > 60:
            return dict(i=i, n=n, ok=False, jets0=jets0, c2=c[2].str(8), h=float(h.mid()))


def lb_piece(a, b, p):
    E = G['E']
    xi0 = (a + b) / 2
    r = (b - a) / 2
    der, _ = E.derivs(xi0, list(range(p + 1)), rel=G['rel'])
    cs = [der[k] / factorial(k) for k in range(p + 1)]
    M = E.sup_abs(p + 1, a, b)
    lbT = L.poly_lower_sym(cs, r)
    return lbT - M * r ** (p + 1) / factorial(p + 1), cs[0]


def cover_gap(task):
    gi, a0, b0, x_left = task
    ctx.prec = G['prec']
    p = order_at(x_left)
    PI = arb.pi()
    width = float(dyarb(b0 - a0).mid())
    w0 = min(G['wmax'], 0.5 * p / (4 * math.pi ** 2 * math.e * max(x_left, 1.0)))
    k = max(1, int(width / w0) + 1)
    edges = [a0 + ((b0 - a0) * j) // k for j in range(k)] + [b0]
    stack = [(edges[j], edges[j + 1], 0) for j in range(k)][::-1]
    npieces, minrel, nfail = 0, None, 0
    while stack:
        a, b, dep = stack.pop()
        lb, f0 = lb_piece(dyarb(a), dyarb(b), p)
        npieces += 1
        if lb > 0:
            rel = arb(lb.lower()) / arb(abs(f0).upper())
            minrel = rel if minrel is None or rel < minrel else minrel
            continue
        nfail += 1
        if dep > 40 or b - a < 2:
            return dict(gi=gi, ok=False, pieces=npieces, fail='[%s, %s] lb %s' % (dyarb(a).str(20), dyarb(b).str(20), lb.str(4)))
        m = (a + b) // 2
        stack += [(m, b, dep + 1), (a, m, dep + 1)]
    return dict(gi=gi, ok=True, pieces=npieces, bisections=nfail, p=p,
                min_rel_lb=(round_down(minrel, 3) if minrel is not None and minrel > 0 else None))


def prime_term(np_):
    n, prime = np_
    ctx.prec = G['prec']
    xi = arb(n).log() / (2 * arb.pi())
    der, _ = G['E'].derivs(xi, [0], rel=G['rel'])
    v = arb(prime).log() / arb(n).sqrt() * der[0]
    return n, v.str(60, radius=True, more=True)


def U_bound(E, x):
    """|Fhat(xi)| <= 4 pi (|A_0|+|B_0|)(z) e^{-z}(1+1/z)/(1-q), z = 2 pi x, q = 2^D e^{-z} < 1/2 (Appendix A of the paper)."""
    ctx.prec = E.prec
    PI = arb.pi()
    Aab, Bab = E.FO.abscoef[0]
    from lib.bessel_form import horner
    z = 2 * PI * x
    q = arb(2) ** E.D * (-z).exp()
    require(q < arb('0.5'), 'U_bound: needs 2^D e^{-2 pi x} < 1/2')
    return 2 * 2 * PI * (horner(Aab, z) + horner(Bab, z)) * (-z).exp() * (1 + 1 / z) / (1 - q)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('J', type=int)
    ap.add_argument('--pball', required=True)
    ap.add_argument('--sha', default=None)
    ap.add_argument('--prec', type=int, required=True)
    ap.add_argument('--order', type=int, default=28)
    ap.add_argument('--order-far', type=int, default=None)
    ap.add_argument('--order-switch', type=float, default=None)
    ap.add_argument('--xmin', type=int, default=2, choices=[1, 2])
    ap.add_argument('--workers', type=int, default=1)
    ap.add_argument('--kback', default='trap', choices=['trap', 'series'])
    ap.add_argument('--bf-step', default='1/20')
    ap.add_argument('--hmax', type=float, default=0.02)
    ap.add_argument('--wmax', type=float, default=0.02)
    ap.add_argument('--rel-bits', type=int, default=64)
    ap.add_argument('--cost', type=int, default=0)
    ap.add_argument('--json', default=None)
    a = ap.parse_args()
    t0 = time.time()
    J, prec = a.J, a.prec
    here = os.path.dirname(os.path.abspath(__file__))
    psha = L.sha256_file(a.pball)
    print('cert_exact: J = %d, working precision %d bits, Taylor order %d%s, K backend %s, x_min = %d, workers %d'
          % (J, prec, a.order, (', order %d for x >= %s' % (a.order_far, a.order_switch)) if a.order_far else '', a.kback,
             a.xmin, a.workers))
    print('  python %s | flint %s' % (platform.python_version(), __import__('flint').__version__))
    print('  pball %s  sha256 %s%s' % (a.pball, psha, '' if a.sha is None else ('  (expected %s: %s)' % (a.sha[:12], psha == a.sha))))
    for f in [os.path.join(here, 'cert_exact.py'), os.path.join(here, 'conelib.py'),
              os.path.join(L.TOP, 'lib/bessel_form.py'), os.path.join(L.TOP, 'lib/besselk.py'),
              os.path.join(L.TOP, 'lib/common.py'), os.path.join(L.TOP, 'lib/k01_trapezoid.py')]:
        print('  code %-24s sha256 %s' % (os.path.relpath(f, L.TOP), L.sha256_file(f)))
    if a.sha is not None:
        require(psha == a.sha, 'pball sha256 mismatch')
    P = L.load_pball(a.pball, prec)
    require(len(P) == 2 * J + 1, 'pball has %d coefficients, expected %d' % (len(P), 2 * J + 1))
    ctx.prec = prec
    # (POS)
    pos = all(c > 0 for c in P)
    kmin = min(range(len(P)), key=lambda k: P[k].lower())
    print('(POS) p_0 = 1 exactly; all %d coefficients p_k certified > 0: %s  (min_k p_k >= %s at k = %d)'
          % (len(P), pos, round_down(P[kmin], 4) if pos else '-', kmin))
    print('      => P_J(u) >= 1 for u >= 0, H_J(t) = P_J(t^2) >= 1 and F_J >= Xi^2 on R' if pos else '      POS NOT CERTIFIED')
    # operators
    pmax = max(a.order, a.order_far or 0)
    E = L.Fhat(P, pmax + 1, prec, kback=a.kback)
    nodes = [n for n, _ in first_prime_powers(J)]
    PI = arb.pi()
    G.update(E=E, prec=prec, p=a.order, p_far=a.order_far, switch=a.order_switch, nodes=nodes, xmin=a.xmin,
             rel=arb(2) ** (-a.rel_bits), hmax=a.hmax, wmax=a.wmax)
    print('  nodes: the first %d prime powers 2 .. %d; operator length D = %d (setup %.1f s)' % (J, nodes[-1], E.D, time.time() - t0),
          flush=True)
    # (BF)
    Q = L.abel_Q(P, prec)
    while len(Q) > 1 and Q[-1].contains(0) and Q[-1].rad() == 0:
        Q.pop()
    require(len(Q) - 1 == 4 * J + 4, 'deg Q = %d, expected 4J+4' % (len(Q) - 1))
    require(Q[-1] > 0, 'Q: leading coefficient not certified > 0')
    step = fmpq(*[int(s) for s in a.bf_step.split('/')]) if '/' in a.bf_step else fmpq(int(a.bf_step))
    x0 = None
    for k in range(1, 400):
        xc = fmpq(nodes[-1]) + step * k
        ctx.prec = prec
        T = L.taylor_shift(Q, 2 * PI * arb(xc))
        if all(t > 0 for t in T):
            x0 = xc
            break
    require(x0 is not None, 'BF: no x_0 found')
    print('(BF) Q = Abel preimage, degree %d = 4J+4, leading coefficient > 0; all %d Taylor coefficients of Q at y_0 = 2 pi x_0 '
          'certified > 0 for x_0 = %s (first point of the grid n_J + k*%s)' % (len(Q) - 1, len(T), x0, step))
    print('     => Fhat_J > 0 on [x_0, oo) = [%s, oo)  (Lemma 4.6, all divisor terms)' % x0, flush=True)
    pool = mp.get_context('fork').Pool(a.workers) if a.workers > 1 else None
    imap = pool.imap if pool else map
    # (NODE)
    nres = list(imap(node_item, range(J)))
    okN = all(r['ok'] for r in nres)
    okJ = all(r['jets0'] for r in nres)
    print('(NODE) jet-subtracted neighbourhoods of the %d nodes (%s):' % (J, 'n = 2 one-sided' if a.xmin == 2 else 'all two-sided'))
    for r in nres:
        if not r['ok']:
            print('    FAIL at n = %d (c_2 = %s, h = %.2e)' % (r['n'], r['c2'], r['h']))
        elif r['i'] < 3 or r['i'] % 10 == 0 or r['i'] >= J - 3:
            print('    n = %4d: p = %d, h = %.3e, c_0 = %s, c_1 = %s, c_2 = Fhat_J\'\'(xi_n)/2 = %s, bracket >= %s (%.2f c_2)'
                  % (r['n'], r['p'], r['h'], r['c0'], r['c1'], r['c2'], r['qlow'], r['relq']))
    print('    all certified: %s; every c_0, c_1 ball contains 0 (input consistency): %s  (%.0f s)' % (okN, okJ, time.time() - t0),
          flush=True)
    if not (okN and okJ):
        print('NOT CERTIFIED')
        return 1
    # (GAP)
    xi_min = arb(0) if a.xmin == 1 else None
    tasks = []
    if a.xmin == 1:
        tasks.append((0, 0, nres[0]['lo'], 1.0))
    for k in range(J - 1):
        tasks.append((k + 1, nres[k]['hi'], nres[k + 1]['lo'], float(nodes[k])))
    ctx.prec = prec
    xi0 = arb(x0).log() / (2 * PI)
    last_end = dy(xi0, True)
    if nres[J - 1]['hi'] < last_end:                 # otherwise the last node item already reaches beyond xi(x_0)
        tasks.append((J, nres[J - 1]['hi'], last_end, float(nodes[-1])))
    for t in tasks:
        require(t[1] < t[2], 'neighbourhoods overlap / empty gap %s' % (t,))
    order = sorted(range(len(tasks)), key=lambda k: -tasks[k][3])
    gres = list(pool.imap_unordered(cover_gap, [tasks[k] for k in order]) if pool else map(cover_gap, tasks))
    okG = all(r['ok'] for r in gres)
    npieces = sum(r['pieces'] for r in gres)
    for r in gres:
        if not r['ok']:
            print('    FAIL in gap %d: %s' % (r['gi'], r['fail']))
    minrel = exact_min([arb(r['min_rel_lb']) for r in gres if r['ok'] and r['min_rel_lb'] is not None]) if okG else None
    print('(GAP) %d gaps, %d Taylor pieces (%d bisections), all certified: %s; min (lower bound / |centre value|) = %s  (%.0f s)'
          % (len(tasks), npieces, sum(r.get('bisections', 0) for r in gres), okG, minrel.str(3) if minrel is not None else '-',
             time.time() - t0), flush=True)
    if not okG:
        print('NOT CERTIFIED')
        return 1
    # (COVER) exact check of the chain of dyadic endpoints
    chain = []
    if a.xmin == 1:
        chain.append(('gap', 0, nres[0]['lo']))
    for k in range(J):
        if nres[k]['lo'] is not None:
            chain.append(('node', nres[k]['lo'], nres[k]['hi']))
        if k < J - 1:
            chain.append(('gap', nres[k]['hi'], nres[k + 1]['lo']))
    if nres[J - 1]['hi'] < last_end:
        chain.append(('gap', nres[J - 1]['hi'], last_end))
    okC = all(chain[i][2] == chain[i + 1][1] for i in range(len(chain) - 1))
    first = 'xi = 0 (x = 1)' if a.xmin == 1 else 'xi_2 (x = 2; one-sided node item from the exact xi_2)'
    okC = okC and (arb(fmpq(chain[-1][2], S_DY)) >= xi0)
    print('(COVER) the items tile [%s, xi(x_0)] with exact dyadic endpoints, and the last endpoint >= xi(x_0): %s' % (first, okC))
    cert = bool(pos and okN and okJ and okG and okC)
    res = dict(J=J, pball=a.pball, pball_sha256=psha, prec=prec, order=a.order, order_far=a.order_far,
               order_switch=a.order_switch, kback=a.kback, xmin=a.xmin, POS=pos, x0_BF=str(x0), nodes_ok=okN,
               pieces=npieces, cover_ok=okC, W_certified=cert)
    print('W_J: Fhat_J >= 0 on [%s, oo), with exact double zeros at the %d nodes and Fhat_J > 0 elsewhere: %s'
          % ('x = 1' if a.xmin == 1 else 'x = 2', J, cert))
    if cert:
        print('     In particular W_J holds on every window [2, L(D+1)], D = 4J (any L > 0).')
    if cert:
        print('(C) clauses of Def 2.4 for F_J = Xi^2 P_J(t^2):  F_J in T (Sec 4.1, a theorem: even, real, Xi^2 P(t^2) in '
              'T_delta);  F_J >= Xi^2 >= 0 on R (POS);  Fhat_J >= 0 on [xi_2, oo) (W above)  =>  F_J in C, exactly (no cushion).')
    # (A) the exact cost
    if a.cost and cert:
        nmax = a.cost
        pps = [(n, pr) for n, pr in prime_powers(nmax) if n > nodes[-1]]
        terms = list(imap(prime_term, pps))
        ctx.prec = prec
        S = arb(0)
        for n, s in terms:
            S += arb(s)
        n1 = nmax + 1
        qq = (arb(n1 + 1) / n1) ** E.D * (-2 * PI).exp() * (arb(n1 + 1).log() / arb(n1).log())
        require(qq < arb('0.5'), 'cost tail: ratio bound must be < 1/2')
        tail = arb(n1).log() * U_bound(E, arb(n1)) / (1 - qq) / PI
        Atrunc = S / PI
        der0, _ = E.derivs(arb(0), [0], rel=arb(2) ** -120)
        F0 = der0[0]
        Alo = arb(Atrunc.lower())
        Ahi = arb((Atrunc + tail).upper())
        klo = Alo / arb(F0.upper())
        khi = Ahi / arb(F0.lower())
        print('(A) A(F_J) = (1/pi) sum_{n in PP, n > n_J} Lambda(n) n^{-1/2} Fhat_J(xi_n)  (Lemma 2.3 + Cor 4.4 + Prop 4.5; '
              'unconditional)')
        print('    truncation: terms n_J = %d < n <= %d (%d prime powers), each enclosed; their sum / pi = %s'
              % (nodes[-1], nmax, len(pps), Atrunc.str(15)))
        print('    first terms: %s' % '; '.join('n = %d: %s' % (n, (arb(t) / PI).str(8)) for n, t in terms[:3]))
        print('    tail n >= %d: every term >= 0 (W_J); sum <= log(n1) U(n1)/((1 - q) pi) = %s, q = %s < 1/2'
              % (n1, round_up(tail, 3), qq.str(3)))
        print('    A(F_J) in [%s, %s]   (certified ball: %s)' % (round_down(Alo, 12), round_up(Ahi, 12), ((Alo + Ahi) / 2 + arb(0, ((Ahi - Alo) / 2).upper())).str(12)))
        print('    int F_J = Fhat_J(0) = %s' % F0.str(25))
        print('    kappa_J^exact = A(F_J)/int F_J in [%s, %s]  =>  kappa* <= %s  (F_J in C, Def 2.4)'
              % (round_down(klo, 10), round_up(khi, 10), round_up(khi, 8)))
        print('    near-rigidity: every admissible pair (mu, nu) has int Xi^2 dmu <= int F_J dmu <= A(F_J) <= %s  '
              '(Lemma 2.5, F_J >= Xi^2, Fhat_J >= 0 on supp nu)' % round_up(Ahi, 8))
        res.update(A_lower=round_down(Alo, 12), A_upper=round_up(Ahi, 12), Fhat0=F0.str(25), nmax=nmax, tail_upper=round_up(tail, 3),
                   kappa_exact_lower=round_down(klo, 10), kappa_exact_upper=round_up(khi, 10))
    if pool:
        pool.close()
    res['secs'] = round(time.time() - t0, 1)
    print('CERTIFIED: %s   [J = %d, %.0f s]' % (cert, J, time.time() - t0))
    print(json.dumps(res), flush=True)
    if a.json:
        with open(a.json, 'w') as f:
            json.dump(dict({k: v for k, v in res.items() if k != 'secs'}, nodes=nres,      # no timing in the file
                           gaps=sorted(gres, key=lambda r: r['gi'])), f, indent=1)
    return 0 if cert else 1


if __name__ == '__main__':
    sys.exit(main())
