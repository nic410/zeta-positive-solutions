"""The two cushion constants used by verify_kappa.py (both rigorous; see lib/cushion.py for the derivations):

  A(Xi^2 e^{-pi t^2}) = 2F(i/2) + (1/2pi) int F(t)[Re psi(1/4+it/2) - log pi] dt   (archimedean side; Arb acb.integral),
  I_delta = int_{-delta}^{delta} (Xi^2)^  >= ...,  delta = 1/20                       (Bessel form, N = 1 term, monotonicity).

Usage (from anc/):  python kappa/cushion_A.py
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from flint import arb  # noqa: E402
from lib.cushion import cushion_A_upper, cushion_Id_lower  # noqa: E402
from lib.common import round_up, round_down  # noqa: E402

A, im = cushion_A_upper(prec=128, T=8)
print('A(Xi^2 e^{-pi t^2}) = %s   (imaginary part of the integral: %s)' % (A.str(15), im.str(3)))
print('  rounded up: A <= %s' % round_up(A, 12))
Id, dl = cushion_Id_lower()
print('I_delta = int_{-delta}^{delta} Psi, delta = 1/20:  I_delta >= %s   (rounded down: %s)' % (Id.str(12), round_down(Id, 10)))
