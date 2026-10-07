"""Independent exact operator construction for the second evaluation path of cone/ (cone/conelib_alt.py).

Exact operator calculus in the basis e0 = K0, e1 = z K1, polynomials in w = z^2:
  theta e0 = -e1, theta e1 = -w e0, theta w^i = 2i w^i;  2D := 2 theta + 1;  W0 = (w^2 + 9w) e0 - 6w e1.
  (A_j, B_j) := (2D)^j W0 (integer polys):  A_{j+1} = (4i+1)-scaled A_j - 2w B_j,  B_{j+1} = (4i+1)-scaled B_j - 2 A_j.
"""
from flint import fmpz_poly


def build_ops(jmax):
    A, B = fmpz_poly([0, 9, 1]), fmpz_poly([0, -6])
    out = [(A, B)]
    for _ in range(jmax):
        ca, cb = A.coeffs(), B.coeffs()
        sA = fmpz_poly([(4 * i + 1) * c for i, c in enumerate(ca)])
        sB = fmpz_poly([(4 * i + 1) * c for i, c in enumerate(cb)])
        wB = fmpz_poly([0] + list(cb))
        A, B = sA - 2 * wB, sB - 2 * A
        out.append((A, B))
    return out


def dcount(N):
    c, d = 0, 1
    while d * d <= N:
        if N % d == 0:
            c += 1 if d * d == N else 2
        d += 1
    return c
