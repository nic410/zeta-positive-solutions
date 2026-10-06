#!/usr/bin/env python3
"""Theorems PT2, PT3, PT4: exact certificate that PT_delta (delta = 1/20) implies (N), p_2J > 0 and R_J > 0, J <= 4.

Usage (from anc/):  python3 toy/pt/verify_pt.py toy/pt/params/ptJ.json [PIECE,PIECE,...]
                    (default: every piece of the parameter file; the pieces may be split over processes)

Statement (paper, toy model).  Let J in {2, 3, 4}, 0 < y_1 < ... < y_J and, for every K <= J,
    y_1 + ... + y_K >= (1 + delta) K (4K - 1),   delta = 1/20                                   (PT_delta)
Then the toy Hermite system  P(0) = 1,  Q_P(y_j) = Q_P'(y_j) = 0 (j <= J)  in p_1..p_2J is uniquely solvable (N),
p_2J > 0, and R_J := Q_P / prod_j (y - y_j)^2 has only positive coefficients.  Here Q_P = sum_k p_k tau_k with
tau_k(y) = (-1)^k (theta - y)^{2k} 1, theta = y d/dy.

Method (exact integer arithmetic, python-flint fmpz_mpoly, in Z[y_1..y_J]):
 1. Derivation.  Qt(y) := det of the (2J+1) x (2J+1) matrix whose rows are (tau_k(y_j))_k, (tau_k'(y_j))_k for
    j = 1..J and (tau_k(y))_k as the last row, k = 0..2J.  Expanding along the last row, Qt = sum_k (-1)^k M_k tau_k,
    where M_k is the 2J x 2J minor of the node rows without column k; each M_k is computed by Laplace expansion
    along the row pairs of the nodes (2 x 2 minors tau_a tau_b' - tau_b tau_a' are univariate).  Qt is divided
    exactly by A(y) = prod_j (y - y_j)^2; with N_i = [y^i](Qt/A) and V = prod_{i<j}(y_i - y_j) one sets
    G_i := sigma N_i / V^4 (exact division), with sigma = +-1 fixed by G_0 > 0 at the point y_K = c(8K - 5).
 2. (a) Admissibility: A(y) * sum_i G_i y^i satisfies the 2J odd Stirling-1 conditions
        sum_{k >= 2l-1} |s(k, 2l-1)| q_k = 0, l = 1..2J  (q_k = coefficient of y^k),
    identically; these characterise span(tau_0..tau_2J) among polynomials of degree <= 4J.
    (b) Determinant: D := M_0 (the determinant of the system in p_1..p_2J) equals kappa (y_1...y_J)^2 V^4 G_0
        with kappa a nonzero integer constant.
    Hence, wherever G_0 != 0 and the y_j are distinct and nonzero, (N) holds and
        r_i = G_i / ((y_1...y_J)^2 G_0)   for every coefficient r_i of R_J.
 3. (c) Positivity on the region.  In slack coordinates y_1 = c(3 + X_1), y_k = y_{k-1} + c X_k (c = 1 + delta),
    PT_delta with increasing nodes is {X_1 >= 0; X_k > 0 (k >= 2); sum_{j<=K} (K-j+1) X_j >= 4K(K-1), K <= J}.
    The parameter file covers it by pieces X_j = N_j(v)/W(v), v >= 0 (the cover is proved in the paper).  For each
    piece the script checks (i) that the piece lies in the closed region (each constraint numerator has
    nonnegative coefficients in v) and (ii) for every G_i, that the numerator H_i(c_num M_1, ..., c_num M_J, c_den W)
    of the homogenised substitution (H_i the homogenisation of G_i, M_k = 3W + N_1 + ... + N_k) has only
    positive coefficients and a positive constant term.  Then every G_i > 0 on the piece (v >= 0), so
    G_0 > 0 gives (N), and r_i > 0 for all i; in particular p_2J = r_2J > 0.
"""
import ast
import hashlib
import itertools
import json
import os
import sys
import time

from flint import fmpq, fmpz_mpoly_ctx, fmpz_poly


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


def stirling1_unsigned(n):
    s = [[0] * (n + 1) for _ in range(n + 1)]
    s[0][0] = 1
    for m in range(1, n + 1):
        for k in range(1, m + 1):
            s[m][k] = s[m - 1][k - 1] + (m - 1) * s[m - 1][k]
    return s


def inversions(seq):
    return sum(1 for i in range(len(seq)) for j in range(i + 1, len(seq)) if seq[i] > seq[j])


def eval_expr(text, env):
    """evaluate an integer polynomial expression (+, -, *, ** with integer exponent, parentheses)."""
    def ev(node):
        if isinstance(node, ast.Expression):
            return ev(node.body)
        if isinstance(node, ast.BinOp):
            a, b = ev(node.left), ev(node.right)
            if isinstance(node.op, ast.Add):
                return a + b
            if isinstance(node.op, ast.Sub):
                return a - b
            if isinstance(node.op, ast.Mult):
                return a * b
            if isinstance(node.op, ast.Pow) and isinstance(b, int) and b >= 0:
                return a ** b
            raise ValueError('operator not allowed in ' + text)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
            return -ev(node.operand) if isinstance(node.op, ast.USub) else ev(node.operand)
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return node.value
        if isinstance(node, ast.Name) and node.id in env:
            return env[node.id]
        raise ValueError('token not allowed in ' + text)
    return ev(ast.parse(text, mode='eval'))


def main():
    t00 = time.time()
    pfile = sys.argv[1]
    par = json.load(open(pfile))
    J = int(par['J'])
    cn, cd = (int(t) for t in par['c'].split('/'))
    pieces = par['pieces']
    want = [p['name'] for p in pieces] if len(sys.argv) < 3 else sys.argv[2].split(',')
    require(all(any(p['name'] == w for p in pieces) for w in want), 'unknown piece')
    print('Theorem PT%d: exact certificate (python-flint fmpz_mpoly)' % J)
    print('parameter file %s  sha256 %s' % (rel(pfile), sha256_file(pfile)))
    print('J = %d, c = 1 + delta = %d/%d, pieces in this run: %s (of %s)'
          % (J, cn, cd, ','.join(want), ','.join(p['name'] for p in pieces)), flush=True)

    names = tuple('y%d' % (j + 1) for j in range(J))
    ctx = fmpz_mpoly_ctx.get(names, 'lex')
    Y = ctx.gens()
    one = ctx.from_dict({(0,) * J: 1})
    zero = 0 * one
    n = 2 * J
    T = [tau(k) for k in range(n + 1)]
    Tz = [fmpz_poly(t) for t in T]

    # ---------------- 1. derivation of G_0..G_2J
    def in_var(p, j):
        d = {}
        for i, c in enumerate(p.coeffs()):
            if c != 0:
                e = [0] * J
                e[j] = i
                d[tuple(e)] = int(c)
        return ctx.from_dict(d)

    w2 = {}

    def wr(a, b, j):                     # det [[tau_a, tau_b], [tau_a', tau_b']] at y_j  (a < b)
        key = (a, b, j)
        if key not in w2:
            w2[key] = in_var(Tz[a] * Tz[b].derivative() - Tz[b] * Tz[a].derivative(), j)
        return w2[key]

    memo = {}

    def det(S):
        """determinant of the rows of nodes J - |S|/2 .. J-1 (value and derivative rows) restricted to columns S."""
        if not S:
            return one
        if S in memo:
            return memo[S]
        node = J - len(S) // 2
        tot = zero
        for P in itertools.combinations(S, 2):
            rest = tuple(c for c in S if c not in P)
            term = wr(P[0], P[1], node) * det(rest)
            tot = tot - term if inversions(P + rest) % 2 else tot + term
        memo[S] = tot
        return tot

    t0 = time.time()
    Mk = [det(tuple(c for c in range(n + 1) if c != k)) for k in range(n + 1)]
    D = Mk[0]
    print('[1] minors M_0..M_%d by Laplace expansion: terms %s (%.1f s)'
          % (n, [len(m) for m in Mk], time.time() - t0), flush=True)
    Qt = [zero] * (2 * n + 1)
    for k in range(n + 1):
        sk = Mk[k] if k % 2 == 0 else -Mk[k]
        for m, cf in enumerate(T[k]):
            if cf:
                Qt[m] += cf * sk
    q = Qt
    for j in range(J):
        for _ in range(2):                                   # synthetic division by (y - y_j)
            d = len(q) - 1
            out = [zero] * d
            acc = zero
            for i in range(d, 0, -1):
                acc = acc * Y[j] + q[i]
                out[i - 1] = acc
            require((acc * Y[j] + q[0]).is_zero(), 'division by (y - y_j) not exact')
            q = out
    N = q
    V = one
    for i in range(J):
        for j in range(i + 1, J):
            V *= Y[i] - Y[j]
    V4 = V ** 4
    G = []
    for Ni in N:
        g, r = divmod(Ni, V4)
        require(r.is_zero(), 'N_i not divisible by V^4')
        G.append(g)
    ystar = [fmpq(cn * (8 * K - 5), cd) for K in range(1, J + 1)]

    def ev_at(g, pt):
        s = fmpq(0)
        for mono, cf in zip(g.monoms(), g.coeffs()):
            t = fmpq(int(cf))
            for k in range(J):
                t *= pt[k] ** mono[k]
            s += t
        return s
    sigma = 1 if ev_at(G[0], ystar) > 0 else -1
    G = [sigma * g for g in G]
    h = hashlib.sha256()
    for i, g in enumerate(G):
        for mono, cf in sorted(zip(g.monoms(), (int(c) for c in g.coeffs()))):
            h.update(('%d %s %d\n' % (i, ' '.join(map(str, mono)), cf)).encode())
    print('    Qt/A exact; N_i divisible by V^4; sigma = %+d' % sigma)
    print('    G_i terms: %s' % [len(g) for g in G])
    print('    G_i total degrees: %s' % [g.total_degree() for g in G])
    print('    fingerprint sha256(G) = %s  (%.1f s)' % (h.hexdigest(), time.time() - t0), flush=True)

    # ---------------- 2(a) admissibility identities
    t0 = time.time()
    A = [one]
    for j in range(J):
        fac = [Y[j] * Y[j], -2 * Y[j], one]
        out = [zero] * (len(A) + 2)
        for i, a in enumerate(A):
            for l, b in enumerate(fac):
                out[i + l] += a * b
        A = out
    Q2 = [zero] * (len(A) + len(G) - 1)
    for i, a in enumerate(A):
        for l, g in enumerate(G):
            Q2[i + l] += a * g
    s1 = stirling1_unsigned(2 * n)
    adm = all(sum((s1[k][2 * l - 1] * Q2[k] for k in range(2 * l - 1, len(Q2))), zero).is_zero()
              for l in range(1, n + 1))
    print('[2a] A(y) * sum_i G_i y^i satisfies the %d odd Stirling-1 conditions identically: %s (deg_y = %d, %.1f s)'
          % (n, adm, len(Q2) - 1, time.time() - t0), flush=True)

    # ---------------- 2(b) determinant identity
    t0 = time.time()
    prod_y2 = one
    for j in range(J):
        prod_y2 *= Y[j] * Y[j]
    kq, kr = divmod(D, prod_y2 * V4 * G[0])
    kappa_ok = kr.is_zero() and kq.is_constant() and not kq.is_zero()
    print('[2b] D = kappa (y_1...y_J)^2 V^4 G_0 with constant kappa: %s, kappa = %s (D has %d terms, %.1f s)'
          % (kappa_ok, kq, len(D), time.time() - t0), flush=True)

    # ---------------- 3(c) positivity on the pieces
    hnames = names + ('z',)
    hctx = fmpz_mpoly_ctx.get(hnames, 'lex')
    GH = []
    for g in G:
        dg = g.total_degree()
        GH.append(hctx.from_dict({tuple(m) + (dg - sum(m),): int(cf) for m, cf in zip(g.monoms(), g.coeffs())}))
    allpos = True
    for p in pieces:
        if p['name'] not in want:
            continue
        pctx = fmpz_mpoly_ctx.get(tuple(p['vars']), 'lex')
        env = dict(zip(p['vars'], pctx.gens()))
        pone = pctx.from_dict({(0,) * len(p['vars']): 1})
        W = eval_expr(p['W'], env) * pone
        X = [eval_expr(e, env) * pone for e in p['X']]
        require(len(X) == J, 'check failed: len(X) == J')

        def nonneg(f):
            return all(int(cf) >= 0 for cf in f.coeffs())
        inside = nonneg(W) and not W.is_zero() and all(nonneg(x) for x in X)
        for K in range(1, J + 1):
            inside = inside and nonneg(sum((X[j] * (K - j) for j in range(K)), 0 * pone) - 4 * K * (K - 1) * W)
        Ms, acc = [], 3 * W
        for x in X:
            acc = acc + x
            Ms.append(cn * acc)
        args = Ms + [cd * W]
        print('[3] piece %s: variables %s >= 0; W = %s; X = %s' % (p['name'], ','.join(p['vars']), p['W'], p['X']))
        print('    piece lies in the closed region (all constraint numerators have nonnegative coefficients): %s'
              % inside, flush=True)
        allpos = allpos and inside
        for i, H in enumerate(GH):
            t1 = time.time()
            Pc = H.compose(*args, ctx=pctx)
            cfs = [int(cf) for cf in Pc.coeffs()]
            const = dict(zip(Pc.monoms(), cfs)).get((0,) * len(p['vars']), 0)
            pos = all(cf > 0 for cf in cfs)
            allpos = allpos and pos and const > 0
            print('    %s G_%d: %d terms, all coefficients > 0: %s, constant term > 0: %s (%.1f s)'
                  % (p['name'], i, len(cfs), pos, const > 0, time.time() - t1), flush=True)
    allok = adm and kappa_ok and allpos
    print('total time %.1f s' % (time.time() - t00))
    if allok:
        print('ALL CERTIFIED: J = %d, identities (a), (b) and positivity of G_0..G_%d on pieces %s'
              % (J, n, ','.join(want)))
    else:
        print('NOT ALL CERTIFIED')
    sys.exit(0 if allok else 1)


if __name__ == '__main__':
    main()
