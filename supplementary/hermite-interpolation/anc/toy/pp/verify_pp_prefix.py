#!/usr/bin/env python3
"""Proposition (prime powers dominate the PT-tight progression), finite part: exact integer certificate.

Usage (from anc/):  python3 toy/pp/verify_pp_prefix.py toy/pp/params/pp_prefix.json

Statement certified (n_K = K-th prime power: 2, 3, 4, 5, 7, 8, 9, 11, ...; y*_K = (21/20)(8K - 5); c = 12366/10000):
    (D)  2 pi n_K > y*_K                                  for every K = 1, ..., K_max,
    (S)  2 pi (n_1 + ... + n_K) >= c K (4K - 1)           for every K = 1, ..., K_max,
with K_max = 217000 (n_{K_max} = 2997587).  The all-K statement in the paper combines (D) for K <= 89 and (S) for
K <= 158 with an elementary tail argument for larger K; both ranges are covered here.  (S) says that the prime-power
nodes satisfy PT_delta with the slack constant c / (1 + delta) for every prefix.

Method.  Prime powers by a sieve (exact integers).  pi is replaced by a rational lower bound pi_lo (and, for the
printed enclosure of the minimum, an upper bound pi_hi); pi_lo < pi < pi_hi is certified with Arb (python-flint
arb.pi()).  Since every quantity is increasing in pi, (D) and (S) with pi_lo imply them with pi.  All comparisons are
done in exact integer arithmetic; the printed minima are exact rationals rounded down (lower bounds) or up.
"""
import hashlib
import json
import math
import os
import sys
import time
from fractions import Fraction

from flint import arb


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


def fmt_dir(q, sig, up):
    if q == 0:
        return '0'
    a = abs(q)
    E = int((a.numerator.bit_length() - a.denominator.bit_length()) * 0.3010299956639812)
    while Fraction(10) ** E > a:
        E -= 1
    while Fraction(10) ** (E + 1) <= a:
        E += 1
    t = q / Fraction(10) ** (E - sig + 1)
    n = math.ceil(t) if up else math.floor(t)
    s = str(abs(n))
    return '%s%s%se%+d' % ('-' if n < 0 else '', s[0], ('.' + s[1:]) if len(s) > 1 else '', E - sig + len(s))


def main():
    t0 = time.time()
    pfile = sys.argv[1]
    par = json.load(open(pfile))
    print('Prime powers dominate the PT-tight progression: exact certificate')
    print('parameter file %s  sha256 %s' % (rel(pfile), sha256_file(pfile)), flush=True)
    KMAX, N = int(par['K_max']), int(par['sieve_limit'])
    plo, phi = Fraction(par['pi_lower']), Fraction(par['pi_upper'])
    cy, c = Fraction(par['y_star_factor']), Fraction(par['prefix_constant'])
    pi = arb.pi()
    bracket = (arb(plo.numerator) / plo.denominator < pi) and (pi < arb(phi.numerator) / phi.denominator)
    print('pi_lo = %s < pi < pi_hi = %s (certified with Arb): %s' % (par['pi_lower'], par['pi_upper'], bracket))
    # prime powers up to N
    sv = bytearray([1]) * (N + 1)
    sv[0] = sv[1] = 0
    for i in range(2, math.isqrt(N) + 1):
        if sv[i]:
            sv[i * i::i] = bytearray(len(sv[i * i::i]))
    isq = bytearray(N + 1)
    for p in range(2, N + 1):
        if sv[p]:
            q = p
            while q <= N:
                isq[q] = 1
                q *= p
    pp = [n for n in range(2, N + 1) if isq[n]]
    require(len(pp) >= KMAX, 'sieve limit too small')
    pp = pp[:KMAX]
    # exact integer comparisons:  (D) 2 pi_lo n > cy (8K-5);  (S) 2 pi_lo S >= c K(4K-1)
    a, b = plo.numerator, plo.denominator
    cyn, cyd = cy.numerator, cy.denominator
    cn, cd = c.numerator, c.denominator
    okD = okS = True
    firstD = firstS = None
    S = 0
    best_slack = best_ratio = None
    for K, n in enumerate(pp, 1):
        S += n
        if not (2 * a * n * cyd > cyn * (8 * K - 5) * b):
            okD = False
            firstD = firstD or K
        if not (2 * a * S * cd >= cn * K * (4 * K - 1) * b):
            okS = False
            firstS = firstS or K
        # exact minima over every K of the lower bounds  slack = 2 pi_lo n - y*_K  (common denominator b cyd)
        # and  ratio = 2 pi_lo S / (K(4K-1))  (compare S/(K(4K-1)) by cross-multiplication)
        num = 2 * a * n * cyd - cyn * (8 * K - 5) * b
        if best_slack is None or num < best_slack[0]:
            best_slack = (num, K, n)
        D = K * (4 * K - 1)
        if best_ratio is None or S * best_ratio[2] < best_ratio[1] * D:
            best_ratio = (K, S, D)
    print('prime powers: n_1 .. n_%d computed (n_%d = %d); sieve limit %d' % (KMAX, KMAX, pp[-1], N))
    sl, Ks, ns = Fraction(best_slack[0], b * cyd), best_slack[1], best_slack[2]
    print('(D) 2 pi n_K > (21/20)(8K-5) for K = 1..%d: %s%s' % (KMAX, okD, '' if okD else ' (first failure K = %d)' % firstD))
    print('    smallest slack 2 pi n_K - y*_K over all K <= K_max: >= %s at K = %d (n_K = %d)'
          % (fmt_dir(sl, 7, False), Ks, ns))
    Kr, Sr, _ = best_ratio
    ra = 2 * plo * Sr / (Kr * (4 * Kr - 1))
    hi = 2 * phi * Sr / (Kr * (4 * Kr - 1))
    print('(S) 2 pi (n_1 + ... + n_K) >= %s K(4K-1) for K = 1..%d: %s%s' % (par['prefix_constant'], KMAX, okS, '' if okS else ' (first failure K = %d)' % firstS))
    print('    smallest ratio 2 pi (n_1+...+n_K)/(K(4K-1)) over all K <= K_max: at K = %d (sum %d), '
          'in [%s, %s]' % (Kr, Sr, fmt_dir(ra, 9, False), fmt_dir(hi, 9, True)))
    need = par['ranges_needed_by_the_tail_argument']
    print('ranges needed by the tail argument: (D) for K <= %d, (S) for K <= %d: covered: %s'
          % (need['domination'], need['prefix_sums'], need['domination'] <= KMAX and need['prefix_sums'] <= KMAX))
    print('total time %.1f s' % (time.time() - t0))
    ok = bracket and okD and okS
    print('ALL CERTIFIED: (D) and (S) for K = 1..%d' % KMAX if ok else 'NOT ALL CERTIFIED')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
