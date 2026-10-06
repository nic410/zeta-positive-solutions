#!/usr/bin/env python3
"""Theorem PT4, region cover, case 4A + 3B + 2E < 48: exact geometry of the polytope Pi< (supporting check).

Usage (from anc/):  python3 toy/pt/check_pt4_region.py toy/pt/params/pt4.json

In the slack coordinates of verify_pt.py (y_1 = c(3 + A), y_2 = y_1 + cB, y_3 = y_2 + cE, y_4 = y_3 + cF), the part
of the PT_delta region (J = 4) with 4A + 3B + 2E < 48 projects onto
    Pi< = {A, B, E >= 0, 2A + B >= 8, 3A + 2B + E >= 24, 4A + 3B + 2E <= 48},
and the pieces II1..II6 of the parameter file cover it by the pulling triangulation from the apex (0, 8, 8)
(F = 48 - (4A + 3B + 2E) + f).  This script checks, in exact rational arithmetic (fractions.Fraction):
  1. the vertices of Pi< (all feasible intersections of three facet planes);
  2. the apex lies on the facets A = 0, 2A + B = 8, 3A + 2B + E = 24, and every base triangle of II1..II6 lies in
     one of the other three facets B = 0, E = 0, 4A + 3B + 2E = 48, and consists of vertices of Pi<;
  3. vol(Pi<) computed as the sum of the six tetrahedra equals vol(Pi<) computed independently as the integral over
     (A, B) of the length of the E-interval (a piecewise linear function, integrated exactly over two quadrilaterals).
The cover argument itself is given in the paper; this is a consistency check of its data.
"""
import hashlib
import itertools
import json
import os
import re
import sys
from fractions import Fraction as Fr


class CertificationError(RuntimeError):
    """A precondition or a check of the certificate failed."""


def require(cond, msg='check failed'):
    """Explicit check, used instead of assert (which python -O would remove): raise CertificationError unless cond."""
    if not cond:
        raise CertificationError(msg)

HERE = os.path.dirname(os.path.abspath(__file__))
ANC = os.path.dirname(os.path.dirname(HERE))

# facets: (normal, rhs, sense) for  n . x  >= rhs  or  <= rhs,  x = (A, B, E)
H = [((1, 0, 0), 0, '>='), ((0, 1, 0), 0, '>='), ((0, 0, 1), 0, '>='),
     ((2, 1, 0), 8, '>='), ((3, 2, 1), 24, '>='), ((4, 3, 2), 48, '<=')]


def dot(n, x):
    return sum(a * b for a, b in zip(n, x))


def feasible(x):
    return all((dot(n, x) >= b) if s == '>=' else (dot(n, x) <= b) for n, b, s in H)


def solve3(M, r):
    """exact Gauss-Jordan for a 3x3 system; None if singular."""
    A = [[Fr(v) for v in row] + [Fr(rr)] for row, rr in zip(M, r)]
    for c in range(3):
        piv = next((i for i in range(c, 3) if A[i][c] != 0), None)
        if piv is None:
            return None
        A[c], A[piv] = A[piv], A[c]
        for i in range(3):
            if i != c and A[i][c] != 0:
                f = A[i][c] / A[c][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[c])]
    return tuple(A[i][3] / A[i][i] for i in range(3))


def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def tri_integral(P, Q, R, f):
    """exact integral of the affine function f over the triangle PQR in the plane."""
    area = abs((Q[0] - P[0]) * (R[1] - P[1]) - (R[0] - P[0]) * (Q[1] - P[1])) / Fr(2)
    return area * (f(P) + f(Q) + f(R)) / 3


def main():
    pfile = sys.argv[1]
    with open(pfile, 'rb') as fh:
        print('parameter file %s  sha256 %s' % (os.path.relpath(os.path.abspath(pfile), ANC), hashlib.sha256(fh.read()).hexdigest()))
    par = json.load(open(pfile))
    ok = True
    V = set()
    for tri in itertools.combinations(H, 3):
        x = solve3([h[0] for h in tri], [h[1] for h in tri])
        if x is not None and feasible(x):
            V.add(x)
    Vs = sorted(tuple(int(v) if v.denominator == 1 else v for v in x) for x in V)
    print('1. vertices of Pi< (%d): %s' % (len(Vs), Vs))
    # tetrahedra of the pieces II1..II6 read from the parameter file: X_j = apex_j + T0_j s + T1_j t + T2_j u
    apex, tris = None, []
    for p in par['pieces']:
        if not p['name'].startswith('II'):
            continue
        rows = []
        for e in p['X'][:3]:
            m = re.fullmatch(r'\s*(-?\d+) \+ (-?\d+)\*s \+ (-?\d+)\*t \+ (-?\d+)\*u\s*', e)
            require(m, 'unexpected form of a simplex coordinate: ' + e)
            rows.append([int(g) for g in m.groups()])
        a = tuple(r[0] for r in rows)
        apex = a if apex is None else apex
        require(a == apex, 'check failed: a == apex')
        tris.append((p['name'], [tuple(rows[j][k] for j in range(3)) for k in (1, 2, 3)]))
    on_apex = [i for i, (n, b, s) in enumerate(H) if dot(n, apex) == b]
    print('2. apex %s lies on the facets %s' % (apex, [H[i][:2] for i in on_apex]))
    ok = ok and on_apex == [0, 3, 4]
    for name, T in tris:
        facets = [i for i, (n, b, s) in enumerate(H) if all(dot(n, v) == b for v in T)]
        isv = all(v in V for v in T)
        print('   %s: base triangle %s lies in facet(s) %s; vertices of Pi<: %s' % (name, T, [H[i][:2] for i in facets], isv))
        ok = ok and isv and len(facets) == 1 and facets[0] in (1, 2, 5)
    vol_tet = sum(abs(det3([[v[j] - apex[j] for j in range(3)] for v in T])) for _, T in tris) / Fr(6)
    # independent: integrate the E-length over (A, B)
    #   R1 = {A, B >= 0, 2A + B >= 8, 3A + 2B <= 24}:  E in [24 - 3A - 2B, (48 - 4A - 3B)/2], length A + B/2
    #   R2 = {A, B >= 0, 3A + 2B >= 24, 4A + 3B <= 48}: E in [0, (48 - 4A - 3B)/2]
    R1 = [(0, 8), (4, 0), (8, 0), (0, 12)]
    R2 = [(8, 0), (12, 0), (0, 16), (0, 12)]
    f1 = lambda P: Fr(P[0]) + Fr(P[1]) / 2
    f2 = lambda P: (48 - 4 * Fr(P[0]) - 3 * Fr(P[1])) / 2
    vol_int = sum(tri_integral(R1[0], R1[i], R1[i + 1], f1) for i in (1, 2)) + \
        sum(tri_integral(R2[0], R2[i], R2[i + 1], f2) for i in (1, 2))
    print('3. volume of Pi<: six pulling tetrahedra %s; integral of the E-length over (A, B) %s; equal: %s'
          % (vol_tet, vol_int, vol_tet == vol_int))
    ok = ok and vol_tet == vol_int and len(Vs) == 8
    print('ALL CHECKS PASSED' if ok else 'CHECK FAILED')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
