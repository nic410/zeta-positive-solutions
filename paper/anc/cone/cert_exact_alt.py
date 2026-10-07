"""Second evaluation path (corroboration): runs cert_exact.main() unchanged, but with the evaluator replaced by
conelib_alt.FhatAlt (an independent exact operator construction in the (K_0, z K_1) basis with polynomials in w = z^2,
lib/opcalc.py) and the matching far bound.
The certificate logic (POS, the far field via the Abel preimage, jet-subtracted nodes, Bernstein gap pieces, exact coverage, the
prime-power sum) is that of cert_exact.py; only the evaluation of Fhat_J^{(m)}, its sup bounds and N-tails is replaced.
Usage: as cert_exact.py (the --kback option selects the K backend of FhatAlt; run_all.sh uses --kback series).
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cert_exact as C                                                   # noqa: E402
import conelib_alt as M                                                  # noqa: E402

if __name__ == '__main__':
    print('Second evaluation path cert_exact_alt.py: evaluator = conelib_alt.FhatAlt (independent operator construction); '
          'code sha256 %s (driver), %s (conelib_alt), %s (lib/opcalc.py)'
          % (C.L.sha256_file(os.path.abspath(__file__)), C.L.sha256_file(os.path.abspath(M.__file__)),
             C.L.sha256_file(os.path.join(C.L.TOP, 'lib/opcalc.py'))))
    C.L.Fhat = M.FhatAlt
    C.U_bound = M.U_bound_alt
    sys.exit(C.main())
