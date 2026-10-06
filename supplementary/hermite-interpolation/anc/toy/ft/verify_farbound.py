#!/usr/bin/env python3
"""Proposition (certified remainders on the prime powers): explicit far-node remainders for PP_6, PP_10, PP_20 (Arb).

Usage (from anc/):  python3 toy/ft/verify_farbound.py toy/ft/params/farbound.json

Setting (paper, toy model; same objects as toy/sm/verify_smset.py).  For the node set y = PP_J (y_j = 2 pi n_j,
n_j the j-th prime power, real pi): R_0 = Q_P/omega, R_m = Q_{E_m}/omega with E_m = u^{2J+m} - Pi_y u^{2J+m}
(m = 1, 2), l_m = [u^1] Pi_y u^{2J+m}, Phi = l_1 R_2 - l_2 R_1, W_2 = Wr(R_1, R_2), N = Wr(R_0, Phi),
S = S_y = -p_2J l_1.  For Y not a node, Delta_y(Y) = p_1(y + {Y}) - p_1(y) = N(Y)/W_2(Y), and
    E(Y) := Y^2 Delta_y(Y)/(2S) - 1 - 8J/Y = Eps(Y) / (Y W_2(Y)),   Eps := Y^3 N/(2S) - Y W_2 - 8J W_2.
Claim: 0 <= Y^2 E(Y) <= C_J for every Y >= y_{J+1}, i.e. Delta_y(Y) = (2S/Y^2)(1 + 8J/Y + theta C_J/Y^2), theta in [0,1].
Certificates at c = y_{J+1} (Descartes: all Taylor coefficients at c positive => positive on [c, infinity)):
  W_2 < 0:            all Taylor coefficients of -W_2 at c are > 0;
  Y^2 E >= 0:          -Y Eps >= 0;
  Y^2 E <= C_J:        Y Eps - C_J W_2 >= 0.
The coefficients of Y Eps in degrees 4J+6 and 4J+7 vanish identically (paper, far-node asymptotics: the leading term
and the 8J term cancel exactly), so the two top shifted coefficients are exactly zero; the script checks that their
balls contain 0 and drops them.  Rigour: Arb balls; arb_mat.solve raises unless invertibility is proved; the
precision is doubled from start_precision_bits until every sign is decided.
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


def objects(ns):
    tp = 2 * arb.pi()
    ys = [tp * n for n in ns]
    J = len(ys)
    T = [arb_poly([arb(c) for c in tau(k)]) for k in range(2 * J + 3)]
    dT = [f.derivative() for f in T]
    M = arb_mat(2 * J, 2 * J)
    for i, y in enumerate(ys):
        for k in range(1, 2 * J + 1):
            M[2 * i, k - 1] = T[k](y)
            M[2 * i + 1, k - 1] = dT[k](y)
    om = arb_poly([1])
    for y in ys:
        om *= arb_poly([y * y, -2 * y, 1])

    def proj(K):
        rhs = arb_mat(2 * J, 1)
        for i, y in enumerate(ys):
            rhs[2 * i, 0] = T[K](y)
            rhs[2 * i + 1, 0] = dT[K](y)
        x = M.solve(rhs)                             # raises unless invertibility is proved: (N)
        return T[K] - sum((T[k] * x[k - 1, 0] for k in range(1, 2 * J + 1)), arb_poly([0])), x
    QP, x0 = proj(0)                                 # x0 = -p (p_1..p_2J of the toy solution)
    QE1, x1 = proj(2 * J + 1)
    QE2, x2 = proj(2 * J + 2)
    l1, l2 = x1[0, 0], x2[0, 0]
    R0, R1, R2 = QP // om, QE1 // om, QE2 // om
    d = lambda f: f.derivative()
    Phi = R2 * l1 - R1 * l2
    W2 = R1 * d(R2) - d(R1) * R2
    N = R0 * d(Phi) - d(R0) * Phi
    S = x0[2 * J - 1, 0] * l1                        # = -p_2J l_1
    return W2, N, S


def main():
    pfile = sys.argv[1]
    par = json.load(open(pfile))
    print('Explicit far-node remainders along the prime-power nodes: Arb ball arithmetic')
    print('parameter file %s  sha256 %s' % (rel(pfile), sha256_file(pfile)), flush=True)
    pp = [int(n) for n in par['prime_powers']]
    require([n for n in range(2, pp[-1] + 1) if is_prime_power(n)] == pp, 'prime-power list must be an initial segment')
    allok = True
    for case in par['cases']:
        J, C = int(case['J']), int(case['C'])
        require(len(pp) >= J + 1, 'check failed: len(pp) >= J + 1')
        prec = int(par['start_precision_bits'])
        while True:
            t0 = time.time()
            ctx.prec = prec
            res = None
            try:
                W2, N, S = objects(pp[:J])
                c = 2 * arb.pi() * pp[J]
                Yp = arb_poly([0, 1])
                Eps = Yp * Yp * Yp * N * (1 / (2 * S)) - Yp * W2 - W2 * (8 * J)
                sh = arb_poly([c, 1])
                tests = []
                for lab, P, drop in (('-W_2 > 0', -W2, 0), ('Y^2 E >= 0  (-Y Eps >= 0)', -(Yp * Eps), 2),
                                     ('Y^2 E <= C  (Y Eps - C W_2 >= 0)', Yp * Eps - W2 * C, 2)):
                    g = P(sh)
                    cs = [g[i] for i in range(g.degree() + 1)]
                    top_ok = True
                    if drop:
                        top_ok = len(cs) == 4 * J + 8 and all(v.contains(0) for v in cs[-drop:])
                        cs = cs[:-drop]
                    tests.append((lab, top_ok, sum(1 for v in cs if v > 0), sum(1 for v in cs if v < 0), len(cs)))
                res = tests
            except ZeroDivisionError:
                res = None
            undecided = res is None or any(t[2] + t[3] < t[4] for t in res)
            if undecided and prec < int(par['max_precision_bits']):
                prec *= 2
                continue
            break
        ok = res is not None and all(t[1] and t[2] == t[4] for t in res)
        allok = allok and ok
        print('PP_%d (c = y_%d = 2 pi %d), C = %d, prec %d: S = %s' % (J, J + 1, pp[J], C, prec, S.str(10, radius=True)))
        for lab, top_ok, npos, nneg, n in res or []:
            print('    %-36s Taylor coefficients at c: %d of %d positive, %d negative%s'
                  % (lab, npos, n, nneg, '' if lab.startswith('-W') else ('; two top coefficients contain 0 and are dropped: %s' % top_ok)))
        print('    => %s  [%.1f s]' % ('CERTIFIED: Delta = (2S/Y^2)(1 + 8J/Y + theta C/Y^2), 0 <= theta <= 1, for all Y >= y_{J+1}'
                                       if ok else 'NOT CERTIFIED', time.time() - t0), flush=True)
    print('ALL CERTIFIED' if allok else 'NOT ALL CERTIFIED')
    sys.exit(0 if allok else 1)


if __name__ == '__main__':
    main()
