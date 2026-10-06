#!/usr/bin/env python3
"""Proposition (one-base laws certified at sampled levels): (UM+) at J in {2, 4, 8, 12, 20, 30, 40, 60}, Arb.

Usage (from anc/):  python3 toy/um/verify_um.py toy/um/params/um.json [J,J,...]

Setting (paper, toy model).  Nodes y_j = 2 pi n_j (n_j the j-th prime power, real pi), z = y_{J+1}.  Chain levels
B = PP_J (every y_j double, |B| = 2J) and B = PP_J + z (z simple, |B| = 2J + 1).  For r = 0, 1, 2 the window-r chain
element F_r = F_r^B is the element of span(tau_r, ..., tau_{r+|B|}) with tau_{r+|B|}-coefficient 1 that vanishes on B
(with multiplicity); tau_k(y) = (-1)^k (theta - y)^{2k} 1.  q_1 := F_2/F_1, a := F_0 F_2 / F_1^2.
(UM+) on [z, inf): F_1 != 0, a'(y) >= 4/y^2, q_1' < 0.

Certificates (Descartes at c = z: all Taylor coefficients at z of a polynomial one-signed => that sign on (z, inf)):
 (i)  P := y^2 (F_0 Wr(F_1,F_2) - F_2 Wr(F_0,F_1)) - 4 F_1^3 = F_1^3 (y^2 a' - 4) and F_1^3 are one-signed with the
      same sign  =>  F_1 != 0 and a' > 4/y^2 on (z, inf);
 (ii) Wr(F_1, F_2) = F_1^2 q_1' has all Taylor coefficients < 0  =>  q_1' < 0 on (z, inf);
 at B = PP_J + z, F_r = (y - z) G_r exactly, so the 3 lowest Taylor coefficients of P and F_1^3 and the 2 lowest of
 Wr(F_1, F_2) vanish exactly; they are checked to contain 0 and dropped (the remaining ones certify the statements
 for the G_r, i.e. for a and q_1, which are unchanged); at B = PP_J the constant terms are included, so the
 statements hold at z itself.
 (iii) a(z) > 0 at both levels: F_0(z) F_2(z) > 0 at B = PP_J and G_0(z) G_2(z) = F_0'(z) F_2'(z) > 0 at B = PP_J + z.
 As a consistency check the script also prints a(z) and tests a(z) <= 1 - 4/z (which follows from (i) and a(inf) = 1).
Rigour: Arb balls (python-flint); arb_mat.solve raises unless invertibility is proved; a sign counts only if the
ball excludes 0.
"""
import hashlib
import json
import os
import sys
import time

from flint import arb, arb_mat, arb_poly, ctx


class CertificationError(RuntimeError):
    """A precondition or a check of the certificate failed."""


def require(cond, msg='check failed'):
    """Explicit check, used instead of assert (which python -O would remove): raise CertificationError unless cond."""
    if not cond:
        raise CertificationError(msg)

HERE = os.path.dirname(os.path.abspath(__file__))
ANC = os.path.dirname(os.path.dirname(HERE))


def rel(path):
    return os.path.relpath(os.path.abspath(path), ANC)


def sha256_file(path):
    with open(path, 'rb') as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def is_prime_power(n):
    if n < 2:
        return False
    p = 2
    while p * p <= n:
        if n % p == 0:
            while n % p == 0:
                n //= p
            return n == 1
        p += 1
    return True


def tau(k):
    """integer coefficient list (low -> high) of tau_k = (-1)^k (theta - y)^{2k} 1."""
    p = [1]
    for _ in range(2 * k):
        q = [0] * (len(p) + 1)          # (theta - y) p : coefficient m -> m p_m - p_{m-1}
        for m, c in enumerate(p):
            q[m] += m * c
            q[m + 1] -= c
        p = q
    return [-c for c in p] if k % 2 else p


def Wr(f, g):
    return f * g.derivative() - f.derivative() * g


def coeffs(p):
    return [p[i] for i in range(p.degree() + 1)]


def onesign(cs):
    if all(c > 0 for c in cs):
        return 1
    if all(c < 0 for c in cs):
        return -1
    return 0


def main():
    pfile = sys.argv[1]
    par = json.load(open(pfile))
    Js = [int(s) for s in sys.argv[2].split(',')] if len(sys.argv) > 2 else [int(j) for j in par['J_list']]
    require(all(j in par['J_list'] for j in Js), "check failed: all(j in par['J_list'] for j in Js)")
    print('(UM+) at sampled levels along the prime-power nodes: Arb ball arithmetic')
    print('parameter file %s  sha256 %s' % (rel(pfile), sha256_file(pfile)))
    ctx.prec = int(par['precision_bits'])
    pp = [int(n) for n in par['prime_powers']]
    require([n for n in range(2, pp[-1] + 1) if is_prime_power(n)] == pp and len(pp) >= max(Js) + 1,
            'prime-power list must be an initial segment of length >= max J + 1')
    print('working precision %d bits, J = %s' % (ctx.prec, Js), flush=True)
    PI = arb.pi()
    nodes = [2 * PI * n for n in pp]
    TP = {}

    def tp(k):
        if k not in TP:
            TP[k] = arb_poly([arb(c) for c in tau(k)])
        return TP[k]

    def Fwin(pts, r):
        """window-r chain element for the multiset pts = [(z, multiplicity)], leading tau coefficient 1."""
        K = sum(m for _, m in pts)
        rows = [(z, d) for z, mu in pts for d in range(mu)]
        val = lambda k, z, d: tp(k)(z) if d == 0 else tp(k).derivative()(z)
        A = arb_mat([[val(k, z, d) for k in range(r, r + K)] for (z, d) in rows])
        b = arb_mat([[-val(r + K, z, d)] for (z, d) in rows])
        x = A.solve(b)                                   # raises unless invertibility is proved
        F = tp(r + K)
        for i in range(K):
            F += x[i, 0] * tp(r + i)
        return F
    Y2 = arb_poly([0, 0, 1])
    allok = True
    for J in Js:
        t0 = time.time()
        z = nodes[J]
        sh = arb_poly([z, 1])
        for label, pts, conf in (('PP_J', [(nodes[j], 2) for j in range(J)], False),
                                 ('PP_J + y_{J+1}', [(nodes[j], 2) for j in range(J)] + [(z, 1)], True)):
            F = [Fwin(pts, r) for r in range(3)]
            P = Y2 * (F[0] * Wr(F[1], F[2]) - F[2] * Wr(F[0], F[1])) - 4 * F[1] ** 3
            degok = P.degree() == 3 * F[1].degree() - 1            # the two top coefficients cancel exactly
            Pc, Cc, Wc = coeffs(P(sh)), coeffs((F[1] ** 3)(sh)), coeffs(Wr(F[1], F[2])(sh))
            dropok = True
            if conf:
                dropok = all(c.contains(0) for c in Pc[:3] + Cc[:3] + Wc[:2])
                Pc, Cc, Wc = Pc[3:], Cc[3:], Wc[2:]
            sP, sC, sW = onesign(Pc), onesign(Cc), onesign(Wc)
            if conf:
                a0 = F[0].derivative()(z) * F[2].derivative()(z) / F[1].derivative()(z) ** 2
            else:
                a0 = F[0](z) * F[2](z) / F[1](z) ** 2
            ok = degok and dropok and sP != 0 and sP == sC and sW == -1 and a0 > 0
            cons = a0 <= 1 - 4 / z
            allok = allok and ok
            print('J=%2d %-15s: P %s (%d coeffs), F_1^3 %s => a\' > 4/y^2: %s | Wr(F_1,F_2) < 0 (%d coeffs): %s | '
                  'a(z) = %s > 0: %s (<= 1 - 4/z: %s)  => %s'
                  % (J, label, {1: '+', -1: '-', 0: 'MIXED'}[sP], len(Pc), {1: '+', -1: '-', 0: 'MIXED'}[sC],
                     sP != 0 and sP == sC, len(Wc), sW == -1, a0.str(8, radius=True), a0 > 0, cons,
                     'CERTIFIED' if ok else 'NOT CERTIFIED'), flush=True)
        print('     [J=%d: %.1f s]' % (J, time.time() - t0), flush=True)
    print('ALL CERTIFIED: (UM+) and a(y_{J+1}) > 0 at both chain levels for J = %s' % ','.join(map(str, Js))
          if allok else 'NOT ALL CERTIFIED')
    sys.exit(0 if allok else 1)


if __name__ == '__main__':
    main()
