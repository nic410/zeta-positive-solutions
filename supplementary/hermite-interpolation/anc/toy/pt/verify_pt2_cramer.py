#!/usr/bin/env python3
"""Theorem PT2, second independent route: Cramer's rule and the ratios r_i/r_4 (exact rational arithmetic).

Usage (from anc/):  python3 toy/pt/verify_pt2_cramer.py

Statement (paper, toy model).  J = 2, 0 < y_1 < y_2, y_1 >= 63/20, y_1 + y_2 >= 147/10 (this is PT_delta for
delta = 1/20 and J = 2).  Then the toy Hermite system P(0) = 1, Q_P(y_j) = Q_P'(y_j) = 0 (j = 1, 2) in p_1..p_4 is
uniquely solvable and R_2 = Q_P / ((y - y_1)^2 (y - y_2)^2) = r_0 + r_1 y + ... + r_4 y^4 has only positive coefficients.

This route shares no code with verify_pt.py.  The basis is built from Stirling numbers of the second kind,
tau_k(y) = (-1)^k T_{2k}(-y) with T_m(x) = sum_i S(m, i) x^i (Touchard), and:
 1. the 4 x 4 matrix M (rows Q(y_1), Q'(y_1), Q(y_2), Q'(y_2); columns p_1..p_4) has entries in Z[y_1, y_2];
    det M and the Cramer numerators det M_k are computed by the Leibniz formula (fmpz_mpoly);
 2. det(M) Q_P = det M + sum_k det(M_k) tau_k(y) is divided exactly by (y - y_1)^2 (y - y_2)^2 in Z[y, y_1, y_2],
    giving c_0..c_4 with r_i = c_i / det M; then, exactly:
        c_3 = 2 (y_1 + y_2 - 14) c_4      (so r_3/r_4 = 2(y_1 + y_2 - 14) > 0 on the region),
        c_0 y_1^2 y_2^2 = det M           (so r_0 = 1/(y_1 y_2)^2 > 0),
        det M = y_1^2 y_2^2 (y_1 - y_2)^4 core(y_1, y_2);
 3. for i = 0, 1, 2 the ratio r_i/r_4 = c_i/c_4 is reduced by gcd to n_i/d_i; on the two subregions
        I : y_1 = 147/20 + s,                 y_2 = y_1 + t                          (s, t >= 0)
        II: y_1 = 63/20 + (21/5) s/(1+s),     y_2 = y_1 + 42/5 - (42/5) s/(1+s) + t  (s, t >= 0)
    (I covers y_1 >= 147/20, II covers 63/20 <= y_1 < 147/20 with y_1 + y_2 >= 147/10), the numerators of
    n_i, d_i and core after clearing the positive denominators (1+s)^deg have only positive coefficients and a
    positive constant term.  Hence core > 0 (so det M != 0 for y_1 != y_2: unique solvability), r_i/r_4 > 0 for
    i = 0..3, r_0 > 0, so r_4 > 0 and every r_i > 0.
"""
import itertools
import math
import sys
import time
from fractions import Fraction

from flint import fmpq, fmpq_mpoly_ctx, fmpz_mpoly_ctx


def floor_str(q, sig=6):
    """decimal string of the positive rational q (fmpq), sig significant digits, rounded down."""
    q = Fraction(int(q.p), int(q.q))
    E = int((q.numerator.bit_length() - q.denominator.bit_length()) * 0.3010299956639812)   # no big-int str()
    while Fraction(10) ** E > q:
        E -= 1
    while Fraction(10) ** (E + 1) <= q:
        E += 1
    n = math.floor(q / Fraction(10) ** (E - sig + 1))
    s = str(n)
    return '%s%se%+d' % (s[0], ('.' + s[1:]) if len(s) > 1 else '', E - sig + len(s))


def stirling2(n):
    S = [[0] * (n + 1) for _ in range(n + 1)]
    S[0][0] = 1
    for m in range(1, n + 1):
        for i in range(1, m + 1):
            S[m][i] = i * S[m - 1][i] + S[m - 1][i - 1]
    return S


def perm_sign(p):
    s, seen = 1, [False] * len(p)
    for i in range(len(p)):
        if not seen[i]:
            j, L = i, 0
            while not seen[j]:
                seen[j] = True
                j = p[j]
                L += 1
            if L % 2 == 0:
                s = -s
    return s


def leibniz(M, zero):
    n = len(M)
    tot = zero
    for p in itertools.permutations(range(n)):
        term = M[0][p[0]]
        for i in range(1, n):
            term = term * M[i][p[i]]
        tot = tot + perm_sign(p) * term
    return tot


def main():
    t0 = time.time()
    print('Theorem PT2, Cramer route (exact arithmetic, python-flint fmpz_mpoly / fmpq_mpoly)')
    S = stirling2(8)
    tau = [[(-1) ** k * S[2 * k][i] * (-1) ** i for i in range(2 * k + 1)] for k in range(5)]   # low -> high
    R3 = fmpz_mpoly_ctx.get(('y', 'y1', 'y2'), 'lex')
    y, y1, y2 = R3.gens()
    one = R3.from_dict({(0, 0, 0): 1})
    zero = 0 * one

    def ev(coeffs, v):
        acc = zero
        for c in reversed(coeffs):
            acc = acc * v + c
        return acc

    def dcoef(coeffs):
        return [i * coeffs[i] for i in range(1, len(coeffs))]
    M = [[ev(tau[k], y1) for k in range(1, 5)], [ev(dcoef(tau[k]), y1) for k in range(1, 5)],
         [ev(tau[k], y2) for k in range(1, 5)], [ev(dcoef(tau[k]), y2) for k in range(1, 5)]]
    b = [-one, zero, -one, zero]                 # Q = tau_0 + sum p_k tau_k, tau_0 = 1, tau_0' = 0
    D = leibniz(M, zero)
    Dk = []
    for k in range(4):
        Mk = [[b[i] if j == k else M[i][j] for j in range(4)] for i in range(4)]
        Dk.append(leibniz(Mk, zero))
    num = D * one + sum((Dk[k - 1] * ev(tau[k], y) for k in range(1, 5)), zero)
    A = (y - y1) ** 2 * (y - y2) ** 2
    q, r = divmod(num, A)
    print('[1] det M: %d terms; exact division by (y-y1)^2 (y-y2)^2: %s' % (len(D), r.is_zero()))
    # coefficients of y^i in q, as polynomials in (y1, y2)
    R2 = fmpz_mpoly_ctx.get(('y1', 'y2'), 'lex')
    Y1, Y2 = R2.gens()
    cd = [dict() for _ in range(5)]
    for mono, cf in zip(q.monoms(), q.coeffs()):
        cd[mono[0]][(mono[1], mono[2])] = int(cf)
    c = [R2.from_dict(d) for d in cd]
    D2 = R2.from_dict({(m[1], m[2]): int(cf) for m, cf in zip(D.monoms(), D.coeffs())})
    ok3 = (c[3] - 2 * (Y1 + Y2 - 14) * c[4]).is_zero()
    ok0 = (c[0] * Y1 ** 2 * Y2 ** 2 - D2).is_zero()
    core, rr = divmod(D2, Y1 ** 2 * Y2 ** 2 * (Y1 - Y2) ** 4)
    okc = rr.is_zero()
    print('[2] r_3/r_4 = 2(y1 + y2 - 14): %s;  r_0 = 1/(y1 y2)^2: %s;  det M = y1^2 y2^2 (y1-y2)^4 core: %s (core: %d terms)'
          % (ok3, ok0, okc, len(core)), flush=True)
    ratios = []
    for i in range(3):
        g = c[i].gcd(c[4])
        n_i, d_i = c[i] / g, c[4] / g
        ratios.append((n_i, d_i))
    # substitutions (homogenised; positive denominators (1+s)^deg cleared)
    Rs = fmpq_mpoly_ctx.get(('s', 't'), 'lex')
    s, t = Rs.gens()
    o = Rs.from_dict({(0, 0): 1})
    y1min, asplit = fmpq(63, 20), fmpq(21, 5)          # y_1 >= 63/20; subregion I is y_1 - 63/20 >= 21/5
    regions = {'I': (y1min + asplit + s, y1min + asplit + s + t, o),
               'II': (y1min * (1 + s) + asplit * s, y1min * (1 + s) + asplit * s + 2 * asplit + t * (1 + s), 1 + s)}

    def subst(P, u1, u2, w):
        d = P.total_degree()
        pw1, pw2, pww = [o], [o], [o]
        for _ in range(d):
            pw1.append(pw1[-1] * u1)
            pw2.append(pw2[-1] * u2)
            pww.append(pww[-1] * w)
        out = 0 * o
        for mono, cf in zip(P.monoms(), P.coeffs()):
            out += int(cf) * pw1[mono[0]] * pw2[mono[1]] * pww[d - mono[0] - mono[1]]
        return out

    def positive(P):
        cf = P.coeffs()
        const = dict(zip(P.monoms(), cf)).get((0, 0), fmpq(0))
        return all(x > 0 for x in cf) and const > 0, const

    allok = r.is_zero() and ok3 and ok0 and okc
    for name, (u1, u2, w) in regions.items():
        for i, (n_i, d_i) in enumerate(ratios):
            Pn, Pd = subst(n_i, u1, u2, w), subst(d_i, u1, u2, w)
            if positive(-Pn)[0] and positive(-Pd)[0]:
                Pn, Pd = -Pn, -Pd                    # same ratio; normalise the common sign
            pn, cn_ = positive(Pn)
            pd, cd_ = positive(Pd)
            allok = allok and pn and pd
            val = floor_str(cn_ / cd_) if cd_ != 0 else '-'
            print('[3] region %-2s r_%d/r_4: numerator %d terms all > 0 and constant > 0: %s; denominator %d terms: %s;'
                  ' value at the corner s = t = 0 >= %s' % (name, i, len(Pn), pn, len(Pd), pd, val))
        Pc = subst(core, u1, u2, w)
        pc, cc = positive(Pc)
        allok = allok and pc
        print('[3] region %-2s core = det M / (y1^2 y2^2 (y1-y2)^4): %d terms, all > 0 and constant > 0: %s'
              % (name, len(Pc), pc), flush=True)
    print('total time %.1f s' % (time.time() - t0))
    print('ALL CERTIFIED: Theorem PT2 (unique solvability and R_2 > 0 on y1 >= 63/20, y1 + y2 >= 147/10, y1 < y2)'
          if allok else 'NOT ALL CERTIFIED')
    sys.exit(0 if allok else 1)


if __name__ == '__main__':
    main()
