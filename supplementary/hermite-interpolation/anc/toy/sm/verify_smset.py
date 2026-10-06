#!/usr/bin/env python3
"""Proposition (certified set-function submodularity along PP): (SMset)_k for every k = 1..60 and every x > y_{k+1}.

Usage (from anc/):  python3 toy/sm/verify_smset.py toy/sm/params/smset.json [kmin kmax]

Setting (paper, toy model).  Nodes y_j = 2 pi n_j (n_j the j-th prime power, real pi); L = PP_k = (y_1..y_k),
L+ = PP_{k+1}.  For a node set L with (N): R_0 = Q_P / omega (omega = prod (y - y_j)^2) is the toy cofactor; for
m = 1, 2, E_m = u^{2k+m} - Pi_L u^{2k+m} (Pi_L: interpolation of the Hermite data at L by u, ..., u^{2k}),
R_m = Q_{E_m} / omega and l_m = [u^1] Pi_L u^{2k+m}.  Then
    Phi = l_1 R_2 - l_2 R_1,   W_2 = Wr(R_1, R_2),   N = Wr(R_0, Phi),
and for x not in L:  (N) for L + {x}  <=>  W_2(x) != 0, and  Delta_L(x) := p_1(L + {x}) - p_1(L) = N(x) / W_2(x).
Hence  Delta_{L+}(x) - Delta_L(x) = P(x) / (W_2(x) W_2^+(x))  with  P = N^+ W_2 - N W_2^+  (+ = objects of L+).
Certificate at each k (c = y_{k+1}): every Taylor coefficient at c of W_2 (of PP_k), W_2^+ (of PP_{k+1}) and P is
< 0 (Descartes: then all three are < 0 on (c, infinity)).  So for every x > y_{k+1}: (N) holds for PP_k + {x} and
PP_{k+1} + {x}, and Delta_{PP_{k+1}}(x) < Delta_{PP_k}(x), which is (SMset)_k (strictly).

Rigour.  Arb balls (python-flint arb, arb_mat, arb_poly); arb_mat.solve raises unless invertibility is proved
(this certifies (N) for PP_k and PP_{k+1}); the divisions by omega are exact in exact arithmetic, so the quotient
balls enclose the true polynomials; a coefficient counts only if its ball is < 0.  The working precision starts at
start_precision_bits and is doubled until every sign is decided (or max_precision_bits is exceeded: failure).
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
    """W_2 and N = Wr(R_0, Phi) for the nodes 2 pi n, n in ns (Arb polynomials)."""
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
        """tau_K minus its Hermite interpolant by tau_1..tau_2J at the nodes; and the tau_1 coefficient."""
        rhs = arb_mat(2 * J, 1)
        for i, y in enumerate(ys):
            rhs[2 * i, 0] = T[K](y)
            rhs[2 * i + 1, 0] = dT[K](y)
        x = M.solve(rhs)                             # raises unless invertibility is proved: (N)
        return T[K] - sum((T[k] * x[k - 1, 0] for k in range(1, 2 * J + 1)), arb_poly([0])), x[0, 0]
    QP, _ = proj(0)                                  # = Q_P with P(0) = 1
    QE1, l1 = proj(2 * J + 1)
    QE2, l2 = proj(2 * J + 2)
    R0, R1, R2 = QP // om, QE1 // om, QE2 // om
    d = lambda f: f.derivative()
    Phi = R2 * l1 - R1 * l2
    W2 = R1 * d(R2) - d(R1) * R2
    N = R0 * d(Phi) - d(R0) * Phi
    return W2, N


def status(f, c):
    """'neg' if every Taylor coefficient of f at c is < 0; 'FAIL' if one is > 0; else 'undecided'."""
    g = f(arb_poly([c, 1]))
    co = [g[i] for i in range(g.degree() + 1)]
    if all(v < 0 for v in co):
        return 'neg', len(co)
    if any(v > 0 for v in co):
        return 'FAIL', len(co)
    return 'undecided', len(co)


def main():
    pfile = sys.argv[1]
    par = json.load(open(pfile))
    print('(SMset) along the prime-power nodes: Arb ball arithmetic')
    print('parameter file %s  sha256 %s' % (rel(pfile), sha256_file(pfile)), flush=True)
    k0, k1 = par['k_range']
    kmin, kmax = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (k0, k1)
    require(k0 <= kmin <= kmax <= k1, 'check failed: k0 <= kmin <= kmax <= k1')
    pp = [int(n) for n in par['prime_powers']]
    require([n for n in range(2, pp[-1] + 1) if is_prime_power(n)] == pp and len(pp) >= kmax + 1,
            'prime-power list must be an initial segment of length >= kmax + 1')
    allok = True
    for k in range(kmin, kmax + 1):
        prec = int(par['start_precision_bits'])
        while True:
            t0 = time.time()
            ctx.prec = prec
            try:
                W2a, Na = objects(pp[:k])
                W2b, Nb = objects(pp[:k + 1])
                c = 2 * arb.pi() * pp[k]
                P = Nb * W2a - Na * W2b
                st = [status(W2a, c), status(W2b, c), status(P, c)]
            except ZeroDivisionError:
                st = [('undecided', 0)] * 3
            if any(s == 'undecided' for s, _ in st) and prec < int(par['max_precision_bits']):
                prec *= 2
                continue
            break
        ok = all(s == 'neg' for s, _ in st)
        allok = allok and ok
        print('k=%2d  c = y_{k+1} = 2 pi %3d  prec %5d:  W_2(PP_k) < 0 on (c,inf): %s (%d coeffs) | W_2(PP_{k+1}) < 0: %s (%d) | '
              'P < 0: %s (%d)  => (SMset)_%d %s  [%.1f s]' % (k, pp[k], prec, st[0][0], st[0][1], st[1][0], st[1][1], st[2][0],
                                                              st[2][1], k, 'CERTIFIED' if ok else 'NOT CERTIFIED', time.time() - t0), flush=True)
    print('ALL CERTIFIED: (SMset)_k with (N) for every x > y_{k+1}, k = %d..%d' % (kmin, kmax) if allok else 'NOT ALL CERTIFIED')
    sys.exit(0 if allok else 1)


if __name__ == '__main__':
    main()
