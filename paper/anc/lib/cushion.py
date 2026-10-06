"""The cushion term eps * Xi(t)^2 e^{-pi t^2} of the zero-killing functions F_rep.

(1) Its Fourier transform is eps (Psi * e^{-pi xi^2}) with Psi = (Xi^2)^ > 0 (Psi is the autoconvolution of the positive
    Fourier transform of Xi).  For xi >= 0 and 0 < delta:
        (Psi * e^{-pi xi^2})(xi) >= e^{-pi (xi + delta)^2} int_{-delta}^{delta} Psi.
    cushion_Id_lower() gives a rigorous lower bound for I_delta = int_{-delta}^{delta} Psi, delta = 1/20:
    Psi is even, Psi = 2 pi sqrt(x) sum_N d(N) W_0(2 pi N x) with W_0(z) = z^2[(z^2+9) K_0(z) - 6 z K_1(z)].
    For N >= 2 and xi >= 0 we have z >= 4 pi, where W_0 > 0: K_0/K_1 is increasing, 6z/(z^2+9) is decreasing for z > 3,
    and (z^2+9) K_0 - 6 z K_1 > 0 is checked at z = 4 pi.  So Psi >= (N = 1 term), which is bounded below on 50
    subintervals of [0, delta] by monotonicity of K_0, K_1 and of the polynomial factors.

(2) Its archimedean functional (the functional A of the explicit formula, archimedean side):
        A(Xi^2 e^{-pi t^2}) = 2 F(i/2) + (1/2pi) int_R F(t) [Re psi(1/4 + it/2) - log pi] dt,   F(i/2) = Xi(i/2)^2 e^{pi/4} = e^{pi/4}/4,
    computed by Arb's rigorous integrator acb.integral on [0, T] (even integrand; Re psi written as the analytic
    (psi(1/4+it/2) + psi(1/4-it/2))/2) plus a tail bound for |t| > T:
        |Xi(t)| <= Xi(0) < 1/2;  for t >= 2, -4.23 <= Re psi(1/4+it/2) <= 1.6 + log t
        (from Re psi(s+i tau) - psi(s) = sum_n tau^2/((n+s)((n+s)^2+tau^2)) and psi(1/4) = -gamma - pi/2 - 3 log 2),
    so |Re psi - log pi| <= 6 + t and (1/2pi) int_{|t|>T} |F| <= (1/2pi) (1/2) [6/(2 pi T) + 1/(2 pi)] e^{-pi T^2}.
"""
from flint import acb, arb, ctx
from .besselk import K01
from .common import require


def cushion_A_upper(prec=128, T=8):
    """Ball containing A(Xi^2 e^{-pi t^2})."""
    old = ctx.prec
    ctx.prec = prec
    PI = arb.pi()
    try:
        def Xi(t):
            s = acb(arb(1) / 2) + acb(0, 1) * t
            return s * (s - 1) / 2 * acb(PI) ** (-s / 2) * (s / 2).gamma() * s.zeta()

        def f(t, analytic):
            x = Xi(t)
            ps = ((acb(arb(1) / 4) + acb(0, 1) * t / 2).digamma() + (acb(arb(1) / 4) - acb(0, 1) * t / 2).digamma()) / 2
            return x * x * (-acb(PI) * t * t).exp() * (ps - acb(PI).log())

        I = acb.integral(f, 0, T)
        tail = (arb(1) / (2 * PI)) * (arb(1) / 2) * (6 / (2 * PI * T) + 1 / (2 * PI)) * (-PI * T * T).exp()
        A = (arb(1) / 2) * (PI / 4).exp() + 2 * I.real / (2 * PI) + arb(0, tail.upper())
        return A, I.imag
    finally:
        ctx.prec = old


def cushion_Id_lower(pieces=50, prec=200):
    """Rigorous lower bound (an exact arb) for int_{-delta}^{delta} Psi."""
    old = ctx.prec
    ctx.prec = prec
    try:
        PI = arb.pi()
        dl = arb(1) / 20
        z2 = 4 * PI
        k0, k1 = K01(z2, prec)
        require((z2 * z2 + 9) * k0 - 6 * z2 * k1 > 0, 'W_0(4 pi) > 0 not certified')   # W_0 > 0 for z >= 4 pi (docstring)
        Imin = None
        for i in range(pieces):
            a = dl * i / pieces
            b = dl * (i + 1) / pieces
            xl = arb(((2 * PI * a).exp()).lower())
            xh = arb(((2 * PI * b).exp()).upper())
            zl = arb((2 * PI * xl).lower())
            zh = arb((2 * PI * xh).upper())
            K0l, K1l = K01(zl, prec)
            K0h, K1h = K01(zh, prec)
            v = 2 * PI * xl.sqrt() * (zl * zl * (zl * zl + 9) * arb(K0h.lower()) - 6 * zh ** 3 * arb(K1l.upper()))
            lo = arb(v.lower())                                   # exact lower endpoint
            Imin = lo if Imin is None or lo < Imin else Imin
        require(Imin > 0, 'cushion: lower bound of Psi not positive')
        return 2 * dl * Imin, dl
    finally:
        ctx.prec = old
