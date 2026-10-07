# Ancillary files: certified computations of the paper

This directory contains every computer-assisted certificate used in the paper *Positive solutions of the explicit
formula for ζ(s): near-criticality and uniqueness*: the exact parameter files, standalone verification scripts, and logs
of fresh runs. Each statement of the paper that rests on a computation is listed in Section 6 with its script, its exact
input file (with SHA-256), the method and precision, the runtime and the expected output.

## 1. Requirements and conventions

- Python ≥ 3.10 with **python-flint 0.9.0** (FLINT/Arb ball arithmetic) and **mpmath 1.3.0**. Nothing else is
  needed: `pip install python-flint==0.9.0 mpmath==1.3.0`. No script uses numpy, scipy or sympy; mpmath is used only by
  the three checks that are not certificates (`kappa/selftest.py`, `cone/selftest.py`, `general/check_pair_identity.py`).
- Run every command from this directory (the top directory of the ancillary files). Scripts locate their inputs relative
  to their own location.
- `./runlog.sh LOGFILE "$PY" SCRIPT ARGS` (after `export PY=python3`, or any interpreter with the two packages) runs one
  verifier and writes a log with a header (command, UTC date, system, Python/python-flint/mpmath versions) and a footer
  (exit code, wall time). Every log shipped here was produced this way, in a fresh run of the shipped script on the
  shipped inputs.
- **Arithmetic.** "Exact" means integer/rational arithmetic (FLINT `fmpz`, `fmpq`, polynomials over ℚ). "Arb" means
  rigorous ball arithmetic (midpoint–radius intervals with outward rounding) at the stated working precision in bits;
  every quantity printed as a ball `[m +/- r]` contains the exact value.
- **Explicit checks.** Every precondition and every check of a certificate is an explicit test that raises an exception
  or prints `NOT CERTIFIED` and exits with a non-zero code; no certificate relies on `assert`, so running Python with
  `-O` does not disable any check.
- **Pole weight.** The parameter `pole_residue` is the pole weight r of the paper (the residue of −L′/L at s = 1).
  The JSON key and the log lines keep the name `pole_residue`/`pole residue`.
- **Exact inputs.** Every number that defines a certified object or a claim is read exactly: rationals are written as
  decimal or `p/q` strings and converted to exact rationals (or to Arb balls that contain them), and the window file of
  `general/verify_windows.py` is parsed with exact decimal literals. Nothing is read through binary64. The only binary64
  numbers are the parameters of the Herglotz pairs (`general/params/pair_*.json`): they *define* the pair, are used
  exactly (as the rationals they are), and are not claims (each file says so in its `definition` field).
- **Rounding.** Every bound printed by a certificate (a number after `<=` or `>=`, or labelled as a lower or upper
  bound) is rounded outward: upper bounds up, lower bounds down, with an exact check of the direction
  (`lib/common.py`: `round_up`, `round_down`, `fixed_up` in `kappa/`, `exact/` and `cone/`; `check_decimal` for the decimals
  that the `general/` scripts format themselves), and never through binary64 arithmetic. A printed interval is contained in the certified one. Values printed as balls `[m +/- r]` are
  enclosures. Numbers labelled as orders of magnitude (`max log10 relative radius`) or as midpoints are not bounds.
- Arb's `bessel_k` and `hypgeom_u` are never used for certified quantities: their enclosures of K₀, K₁ can lose
  about e^{2z} in relative accuracy at moderate z. `lib/besselk.py` and `lib/k01_trapezoid.py` implement validated K₀, K₁
  instead.
- Exit code 0 and the final success line listed in Section 6 mean that the certificate holds.
- `tools/logdiff.py` compares a re-run log with the shipped one after removing dates, the system line and timings
  (Section 8).

## 2. Layout

| Path | Contents |
|---|---|
| `lib/` | Shared library. `besselk.py`: rigorous K₀, K₁ (DLMF 10.31 series, DLMF 10.40 asymptotics with the 10.40(ii) error bound). `k01_trapezoid.py`: rigorous K₀, zK₁ for z ≥ 1 by the trapezoid rule on DLMF 10.32.8, with the discretisation bound of Trefethen and Weideman (SIAM Rev. 56 (2014), Theorem 5.1) and explicit truncation bounds. `bessel_form.py`: exact Bessel-operator form of F̂ for F = Ξ²P(t²) and its derivatives, with rigorous divisor-sum tails. `opcalc.py`: an independent exact operator construction in the basis K₀, zK₁ with polynomials in w = z² (second evaluation path of `cone/`). `cushion.py`: the cushion constants. `common.py`: parameter files, hashes, prime powers, explicit checks, outward decimal rounding. |
| `cone/` | The exact members F_J = Ξ²P_J(t²) lie in the cone, J = 10, 60, 61, 110, 111, without cushion: F̂_J ≥ 0 with exact double zeros at the J nodes, the cost 𝒜(F_J), κ* and the near-rigidity bound; a second evaluation path; self-test. `cone/out/` holds machine-readable summaries (outputs). |
| `kappa/` | Certified upper bounds for the slack κ* from explicit zero-killing functions Ξ²(H + εe^{−πt²}), J = 20 … 100 (the cushioned certificates of the paper's version 1.1, now a cross-check); cushion constants; self-test. |
| `exact/` | The exact Hermite members P_J: non-singularity (N), coefficient positivity (POS), the bound for max_k((2k)!p_k)^{1/2k}. `exact/out/` holds the certified coefficient enclosures (outputs), `exact/ref/` the independent reference enclosures. |
| `general/` | Certificates in the Gaussian–Laguerre family and explicit admissible pairs: Proposition 5.4 (Gaussian–Laguerre): κ*_OPS ≤ 9.9462·10⁻⁴¹, the low-height function F₈₀ and its windows, the two control examples ℚ(√5) and ℚ(√−3) (dual functions and pairs for Γ_ℝ² and Γ_ℂ), the pair for ζ's data at log q = 0.02 (the slack lower bound). `general/results/` holds machine-readable summaries (outputs). |
| `computed/` | Computed values that are **not** certificates (Section 9). |
| `tools/` | `logdiff.py`: compare logs up to dates and timings. |
| `runlog.sh` | Wrapper that writes a log with header and footer. |
| `SHA256SUMS` | SHA-256 of every shipped file except the logs, this README and the Lean project `lean/` (`sha256sum -c SHA256SUMS`). |

## 3. The slack κ*: zero-killing functions (`kappa/`)

These are the cushioned certificates of version 1.1 of the paper. Version 1.2 bounds κ* through the exact members of
`cone/` (Section 4), and the paper uses the certificates below only as a cross-check (Section 5.2 of the
paper): they evaluate a different function (rationalised parameters plus a cushion) with a different verifier, and at
J = 60 they agree with the exact member to eight digits.

**Object.** Each `kappa/params/J*.json` fixes, by exact rationals (decimal or `p/q` strings), the zero-killing function

  F_rep(t) = Ξ(t)² H(t) + ε Ξ(t)² e^{−πt²},  H(t) = ∏_{j≤J} (1 + r_j t² + s_j t⁴),  ε = 10^{−E},

where Ξ(t) = ξ(½ + it) is Riemann's ξ-function. The file also records the SHA-256 of the canonical factor list
(the string `r_1 s_1\n r_2 s_2 …`), which the verifier recomputes and checks.

**What `kappa/verify_kappa.py` proves** (all in Arb ball arithmetic):
1. H > 0 on ℝ, exactly: s_j > 0 and r_j² < 4s_j for every factor (rational arithmetic). Hence F_rep ≥ 0 on ℝ.
2. F̂_rep(ξ) ≥ 0 for |ξ| ≥ c = (log 2)/2π, where F̂(ξ) = ∫F(t)e^{−2πiξt}dt. Write x = e^{2πξ}.
   - F̂ of Ξ²H and its ξ-derivatives are computed from the Bessel form
     F̂^{(m)}(ξ) = (2π)^m · 2π√x · Σ_{N≥1} d(N) \[(θ+½)^m H(−(θ+½)²) θ²(θ+1)² K₀](2πNx), θ = z d/dz,
     where the operator acts exactly on span{z^k K₀, z^k K₁} (`lib/bessel_form.py`); the divisor sum is truncated
     with a rigorous tail bound (d(N) ≤ 2√N, K₀ ≤ K₁ ≤ K_{3/2}).
   - At each of the J prime powers n killed by H (where F̂ has a double zero up to the rationalisation of the
     parameters), including the edge n = 2 (ξ = c): a Taylor model of order p centred exactly at ξ_n = (log n)/2π, with
     the quadratic lower bound c₀ − c₁²/(4c₂′) on a neighbourhood; elsewhere on [c, ξ_far]: Taylor models on pieces
     with exact dyadic endpoints (overlapping the neighbourhoods) and adaptive bisection. The Taylor remainder uses a
     rigorous upper bound for sup|F̂^{(p+1)}| on the piece.
   - The cushion term contributes ε(Ψ ∗ e^{−πξ²})(ξ) ≥ ε e^{−π(ξ+1/20)²} I_δ with I_δ = ∫_{−1/20}^{1/20}Ψ and
     Ψ = (Ξ²)^ > 0 (`lib/cushion.py`); for x ≥ x_far an explicit majorant Υ(x) ≥ |F̂_{Ξ²H}| is below the cushion, and
     log Υ − log(cushion) is decreasing there (checked: 2πx_far > D + 4 and ξ_far + 1/20 < 3).
3. The explicit formula (F_rep vanishes at every nontrivial zero of ζ):
   𝒜(F_rep) = (1/π) Σ_{n≥2} Λ(n) n^{−½} F̂_{Ξ²H}((log n)/2π) + ε 𝒜(Ξ²e^{−πt²}). The prime-power sum is evaluated
   term by term up to x_far + 1 and the rest is bounded by a geometric tail. The log prints the truncated sum
   S(Ξ²H) over n ≤ x_far + 1, the tail bound, and the tail-inclusive enclosure 𝒜(Ξ²H) = S(Ξ²H) + [±tail]; the
   certified upper bound 𝒜_upper adds the tail exactly once.
4. κ* ≤ 𝒜(F_rep)/F̂_rep(0) ≤ 𝒜_upper / F̂_{Ξ²H}(0)_lower, printed rounded up to 8 significant digits.

`kappa/check_H_nonneg.py` expands H(t) = P(t²) exactly over ℚ for the nine parameter files and certifies P(0) = 1 and
that every coefficient of P is ≥ 0; hence H ≥ 1 on ℝ and F_rep ≥ Ξ². With the J = 100 certificate (𝒜(F_rep) ≤ 𝒜_upper,
read from `kappa/logs/J100.log` after checking its parameter hash) and weak duality, every admissible pair satisfies
∫Ξ²dμ ≤ ∫F_rep dμ ≤ 𝒜(F_rep) ≤ 3.21·10⁻⁹⁰⁶ (𝒜_upper rounded up, with an exact check of the direction). In version 1.2 the
paper's near-rigidity bound comes instead from the exact member F₁₁₁ (`cone/`, Section 4).

**The cushion constants.** `verify_kappa.py` recomputes both constants at start-up with the code of `lib/cushion.py`:
the archimedean value 𝒜(Ξ²e^{−πt²}) as an Arb ball (rigorous `acb.integral` on [0, 8] plus a tail bound), of which it
uses the *upper endpoint* (so ε𝒜(Ξ²e^{−πt²}) is bounded above by ε times that endpoint, which is below
0.930646274516), and the lower bound I_δ ≥ 0.09782880564 (N = 1 term of the Bessel form on 50 monotone pieces).
`kappa/cushion_A.py` prints the same two constants together with their decimal roundings (`A <= 9.30646274516e-1`,
`I_delta ... (rounded down: 9.782880564e-2)`).

`kappa/selftest.py` is a validation run (not a certificate): K₀, K₁ against mpmath at 12 points; the Bessel form
of F̂(0) against direct Arb integration of Ξ²H; the archimedean and prime sides of the explicit formula against each
other (this fixes the normalisation 1/π, n^{−½}, (log n)/2π used in step 3); derivatives against finite differences.
It exits with a non-zero code if any comparison fails.

## 4. The exact Hermite members P_J (`exact/`) and their membership in the cone (`cone/`)

P_J(u) = 1 + Σ_{k=1}^{2J} p_k u^k (u = t²) is the polynomial for which F̂_{Ξ²P_J(t²)} and its derivative vanish at the
first J prime powers (unique when the defining 2J × 2J linear system is non-singular, which is (N)); the entries of
the system are the moments (−1)^k(2π)^{−2k}Ψ^{(2k)}(ξ_n), (−1)^k(2π)^{−2k}Ψ^{(2k+1)}(ξ_n).
- `exact/verify_exact_member.py J --prec B` encloses all moments rigorously (Bessel form with H = 1), scales rows and
  columns by exact powers of two, and solves the ball system with Arb's preconditioned solver. A successful solve
  proves that every matrix in the ball, in particular the exact one, is non-singular: this is (N). The output balls
  contain the exact p_k; (POS) holds if every ball is positive. It prints min_k p_k (rounded down) and
  a = max_k((2k)!p_k)^{1/2k} (rounded up). The enclosure is written to `exact/out/P{J}_ball.txt` and compared with a
  second enclosure `exact/ref/P{J}_ref.txt` computed earlier by a different implementation (different K₀/K₁
  evaluation and basis); every pair of balls must overlap, otherwise the run fails (exit code 1). This overlap is a
  corroboration only: the certificate is the solve. The run is deterministic: with the same software versions it
  rewrites `exact/out/P{J}_ball.txt` byte for byte.
- `exact/check_coefficient_bound.py` checks the coefficient bound of the finite-J instances explicitly: from the
  enclosures it certifies p_k > 0 and computes an upper bound for max_k((2k)!p_k)^{1/2k}, which must be ≤ 0.71636 for
  J = 60, 61, 110, 111 (exact comparison); hence 0 < p_k ≤ 0.71636^{2k}/(2k)!.

**The exact members lie in the cone (`cone/`).** `cone/cert_exact.py J --pball exact/out/P{J}_ball.txt --sha SHA ...`
reads the certified enclosure of P_J written by `exact/verify_exact_member.py` (its SHA-256 is checked) and certifies,
for the exact member F_J = Ξ²P_J(t²) and without cushion (all in Arb ball arithmetic):
- (POS) every p_k > 0 on the balls, so P_J ≥ 1 on [0, ∞) and F_J ≥ Ξ² on ℝ.
- (BF) far field: with Q(y) = e^y P_J(−(θ+½)²)θ²(θ+1)²e^{−y} (θ = y d/dy, degree 4J + 4), the integral representation
  F̂_J(ξ) = 2π√x Σ_N d(N) ∫_z^∞ Q(y)e^{−y}(y² − z²)^{−½}dy, z = 2πNx, shows F̂_J > 0 for x ≥ x₀ once every Taylor
  coefficient of Q at y₀ = 2πx₀ is positive; x₀ is the first point n_J + k/20 (k ≥ 1) where this holds.
- (NODE) at each of the J nodes F̂_J(ξ_n) = F̂_J′(ξ_n) = 0 exactly (definition of P_J), so
  F̂_J(ξ_n + δ) = δ²[c₂ + c₃δ + … + c_pδ^{p−2} + Rδ^{p−1}] with |R| ≤ sup|F̂_J^{(p+1)}|/(p+1)!; a positive Bernstein lower
  bound of the bracket minus the remainder on [0, h] and on [−h, 0] gives F̂_J > 0 on 0 < |δ| ≤ h and a zero of order
  exactly 2. The balls of c₀, c₁ computed from the coefficient balls are not used: they are only checked to contain 0, a
  flag that detects gross input errors (for example a wrong coefficient file) and nothing more. The validity rests on the
  certified solve of `exact/verify_exact_member.py` (its balls contain the exact coefficients) and on c₀ = c₁ = 0 for the
  exact member.
- (GAP) between the node neighbourhoods: Taylor models of order p (24 or 28; 48 or 64 at large x) at exact dyadic centres,
  Bernstein lower bound minus the Lagrange remainder > 0, adaptive bisection; a failing piece stops the certificate.
- (COVER) the node items (dyadic ends rounded inward) and the gap pieces tile [ξ₂, ξ(x₀)] with exact dyadic endpoints
  k/2²⁰⁰ (`--xmin 2`; the item at n = 2 starts at the exact ξ₂), or [0, ξ(x₀)] (`--xmin 1`); checked exactly.
- (A) with `--cost NMAX`: 𝒜(F_J) = (1/π)Σ_{n ∈ PP, n > n_J} Λ(n)n^{−½}F̂_J(ξ_n), which uses no hypothesis on the zeros of ζ.
  The terms n ≤ NMAX (400 for J ≤ 61, 800 for J ≥ 110) are enclosed; every term is ≥ 0 by the certificate above; the
  rest is at most log(n₁)U(n₁)/((1 − q)π), n₁ = NMAX + 1, with the far bound
  U(x) = 4π(|A₀| + |B₀|)(2πx)e^{−2πx}(1 + 1/(2πx))/(1 − 2^D e^{−2πx}) and q < ½ a checked bound for the ratio of
  consecutive terms. ∫F_J = F̂_J(0) is enclosed, and the script prints κ* ≤ 𝒜(F_J)/∫F_J (F_J/∫F_J is in the cone) and
  the near-rigidity bound ∫Ξ²dμ ≤ ∫F_J dμ ≤ 𝒜(F_J) for every admissible pair (weak duality and F_J ≥ Ξ²).

F̂_J and its derivatives are evaluated with the operator polynomials of `lib/bessel_form.py` (exact recurrences on the
coefficient balls), the trapezoid-rule K₀, zK₁ of `lib/k01_trapezoid.py` and rigorous divisor-sum tails (d(N) ≤ 2√N,
K₀ ≤ K₁ ≤ K_{3/2}, geometric series in N, always added as a ball radius); sup bounds on an interval use that |A_m|, |B_m|
increase and K₀, K₁ decrease. With `--xmin 1` the certificate covers [0, ∞), hence (F̂_J is even) all of ℝ: F_J is then in
the classical cone 𝒞_OPS. The log line `In particular W_J holds on every window [2, L(D+1)], D = 4J (any L > 0).` is an
informational restatement of (W) on finite windows; its D is the degree bound 4J of H_J, not the operator length D printed in
the `nodes:` line of the same log. The **second evaluation path** `cone/cert_exact_alt.py` runs the same certificate logic with
independently computed coefficient enclosures (`exact/ref/`), an independent exact operator construction in the basis
K₀, zK₁ (`lib/opcalc.py`, `cone/conelib_alt.py`) and the series/asymptotic K₀, K₁ of `lib/besselk.py` (`--kback series`);
`cone/compare_runs.py` checks that both paths certify every J and that their intervals for 𝒜(F_J) and κ_J overlap. This is
a corroboration, not a certificate. `cone/selftest.py` (not a certificate) compares the two K backends with each other and
with mpmath, the Abel preimage Q with an independent construction through Stirling numbers, the integral representation
with numerical quadrature, the operator form with the moment form, and the Bernstein bounds with samples.

## 5. The Gaussian–Laguerre family (`general/`)

Test functions F(t) = Σ_{k≤K} c_k f_k(t/s), f_k(u) = L_k^{(−1/2)}(2πu²)e^{−πu²}, plus a positive two-Gaussian repair
term of size ε; the c_k are exact decimals. Then F = e^{−X/2}P(X) and F̂ = s·e^{−Y/2}Q(Y) with X = 2πt²/s²,
Y = 2πs²ξ² and P, Q polynomials over ℚ (`general/verify_general.py`).
- Positivity is **exact**: Sturm sequences over ℚ show that P has no root in (0, ∞) (so F > 0 on ℝ), and that Q has no
  root in (0, ∞) (F̂ > 0 on ℝ: the Odlyzko–Poitou–Serre cone) or no root in (Y_lo, ∞) with Y_lo a rational just below
  the gap edge (F̂ > 0 on [ξ₂, ∞)).
- The archimedean functional 𝒜 of the given Γ-data (r·2F(i/2) + (1/2π)∫F[Σ_j(Re ψ(·) − log π) + log N]dt) is one
  rigorous Arb integral (`acb.integral`) of F_rep against the digamma weight, F_rep evaluated by the three-term
  Laguerre recurrence on complex balls, plus a rigorous tail; F̂_rep(0) is exact. The printed bounds (κ*, q_min, pole
  weight) follow by exact arithmetic on these balls and are rounded outward.
- The tail t > T uses |Re ψ(w_j + it/2)| ≤ t for t ≥ T, with w_j = (½ + κ_j)/2. Proof: for w > 0 and τ > 0, the
  partial fractions give Re ψ(w + iτ) = lim_N (log N − Σ_{n<N} f(n)) with f(x) = (x + w)/((x + w)² + τ²), and the
  total variation of f on [0, ∞) is at most 1/τ; hence |Re ψ(w + iτ) − log√(w² + τ²)| ≤ 1/τ. With τ = t/2, t ≥ 10 and
  w_j² ≤ 75 ≤ 3t²/4 this gives 0 < Re ψ(w_j + it/2) ≤ log t + 2/t ≤ t. The script therefore requires T ≥ 10 and every
  Γ-shift in the domain 0 ≤ κ_j, (½ + κ_j)² ≤ 300 (exact check; the shipped shifts are 0 and 1). `verify_pair.py`
  requires every shift κ_j ≥ 0, so that the digamma arguments are positive reals and its tail majorant is monotone.
- `general/verify_pair.py` certifies an explicit admissible pair ("Herglotz pair") for given Γ-data and conductor q:
  ν̃ ≥ 0 (cells, bumps and tails; every tail exponent m > ½, so that ∫x^{−1/2}d|ν̃| < ∞), and μ > 0 on [0, T] by
  mean-value steps (μ′ enclosed on each whole step; the floor is the exact minimum of the lower endpoints) plus
  monotone majorants beyond T. It also prints a rigorous lower bound x0 for the start of supp ν̃ (the first cell with
  f_i < 1, the lowest active bump e^{u_b − ε}, or X; e^{log 2} = 2 exactly), and with `--gap-x N` it checks x0 ≥ N:
  then the prime measure lives on [ξ_N, ∞), and the pair is admissible for the data with the gap ξ_N. The shipped runs
  check the natural gaps: ξ₄ for the Γ_ℝ² pair (ℚ(√5): 2 is inert, so the smallest norm is 4), ξ₃ for the Γ_ℂ pair
  (ℚ(√−3): the smallest norm is 3) and ξ₂ for the ζ pair. With the claim `slack_q1_ge` it also prints the resulting lower bound for κ* of the same
  data at conductor 1, κ* ≥ inf μ − (log q)/2π (weak duality). `general/corollary_slack.py` combines a dual bound and
  a primal pair into the conductor bracket and the slack interval for a quadratic field (it checks the SHA-256 links of
  both summaries to their parameter files). Since both dual functions are in the OPS cone, the bracket and the interval
  hold for every gap g with e^{2πg} ≤ x0; with `--gap-x N` this is checked at the field's natural gap. `general/check_pair_identity.py` is a numerical check of the identity
  𝒜_q(F) = ∫Fμ + (1/π)∫F̂dν for a Gaussian F, run on all three pairs (mpmath, 30 digits; not a certificate).
- `general/verify_windows.py` proves exact lower bounds F ≥ m on t-intervals and F̂ ≥ m on frequency windows for a
  Laguerre-basis function (e^{X/2} bounded above by a rational Taylor polynomial with a Lagrange remainder; positivity
  of the resulting rational polynomials by Descartes' rule after a Möbius map, with bisection), and turns them, with
  the certified 𝒜(F_rep), into upper bounds for the mass that any admissible pair (μ, ν) can put on those windows
  (2·min_J F·μ(J) ≤ 𝒜(F) and min_I F̂·ν(I) ≤ π𝒜(F)), and for atoms of ν at the points ξ_n = (log n)/2π,
  n ∈ {2.5, 6, 10, 12, 14, 15, 18} (none of them a prime power). Every entry is checked before use: its kind is "t"
  (t-interval) or "n" (frequency window [ξ(lo), ξ(hi)]), m > 0, lo < hi, and 0 ≤ lo for t-intervals (F is even and
  X = 2πt²/s² is increasing on [0, ∞); an interval containing negative t is rejected), 1 ≤ lo for frequency windows.
  The window endpoints and minima are read as exact decimals; a printed window is the exact decimal when it has at most 12 significant digits,
  and is otherwise rounded inward to 12 significant digits, so every printed window lies inside the certified one.

## 6. Claims, scripts and expected output

Claims are named by what they state. "Runtime" is the wall time recorded in the footer of the shipped log (`W` = number of worker processes; otherwise one process). Every verifier prints the SHA-256 of each input
file it reads; the table abbreviates it, Section 7 lists it in full. "Expected output" quotes lines (or parts of
lines) of the shipped log verbatim.

### 6.1 The slack κ*: zero-killing functions (`kappa/`; the cushioned cross-check)

| Claim (label) | Command (from the top directory) | Input (SHA-256, abbreviated) | Method; precision | Runtime | Expected output (verbatim) |
|---|---|---|---|---|---|
| κ* ≤ 1.1508391·10⁻⁹⁰⁶ (cushioned cross-check, J = 100; version 1.1 headline) | `python kappa/verify_kappa.py kappa/params/J100.json --prec 3300 --order 28 --order-far 64 --order-switch 121 --workers 1` | `kappa/params/J100.json` (`1186be2c…90719662`) | Arb, 3300 bits; Taylor order 28 (x < 121), 64 (x ≥ 121); ε = 10⁻⁹¹¹; x_far = 452; 5848 pieces | 1648 s | `(4) kappa* <= A_upper / Fhat_H(0)_lower <= 1.1508391e-906`; `CERTIFIED: True` |
| κ* ≤ 1.0640143·10⁻⁴¹⁷ (cushioned cross-check) | `python kappa/verify_kappa.py kappa/params/J60.json --prec 1700 --order 28 --workers 1` | `kappa/params/J60.json` (`e22afd87…71e94a7e`) | Arb, 1700 bits; Taylor order 28; ε = 10⁻⁴²⁴; x_far = 231; 6741 pieces | 312 s | `(4) kappa* <= A_upper / Fhat_H(0)_lower <= 1.0640143e-417`; `CERTIFIED: True` |
| κ* ≤ 1.8493714·10⁻³¹¹ (cushioned cross-check) | `python kappa/verify_kappa.py kappa/params/J50.json --prec 1300 --order 28 --workers 1` | `kappa/params/J50.json` (`3e95b34b…bff3d100`) | Arb, 1300 bits; Taylor order 28; ε = 10⁻³¹⁸; x_far = 182; 2934 pieces | 128 s | `(4) kappa* <= A_upper / Fhat_H(0)_lower <= 1.8493714e-311`; `CERTIFIED: True` |
| κ* ≤ 9.3828982·10⁻²²⁰ (cushioned cross-check) | `python kappa/verify_kappa.py kappa/params/J40.json --prec 1000 --order 28 --workers 1` | `kappa/params/J40.json` (`b3b71157…897e8884`) | Arb, 1000 bits; Taylor order 28; ε = 10⁻²²⁶; x_far = 137; 1277 pieces | 42 s | `(4) kappa* <= A_upper / Fhat_H(0)_lower <= 9.3828982e-220`; `CERTIFIED: True` |
| κ* ≤ 9.9924044·10⁻¹⁷⁷ (cushioned cross-check) | `python kappa/verify_kappa.py kappa/params/J35.json --prec 850 --order 26 --workers 1` | `kappa/params/J35.json` (`35e8cc8e…33ae7dcb`) | Arb, 850 bits; Taylor order 26; ε = 10⁻¹⁸³; x_far = 116; 1007 pieces | 26 s | `(4) kappa* <= A_upper / Fhat_H(0)_lower <= 9.9924044e-177`; `CERTIFIED: True` |
| κ* ≤ 7.7522383·10⁻¹³² (cushioned cross-check) | `python kappa/verify_kappa.py kappa/params/J30.json --prec 700 --order 26 --workers 1` | `kappa/params/J30.json` (`472a5a88…ba0c201c`) | Arb, 700 bits; Taylor order 26; ε = 10⁻¹³⁸; x_far = 93; 662 pieces | 15 s | `(4) kappa* <= A_upper / Fhat_H(0)_lower <= 7.7522383e-132`; `CERTIFIED: True` |
| κ* ≤ 5.2941806·10⁻⁹¹ (cushioned cross-check) | `python kappa/verify_kappa.py kappa/params/J24.json --prec 500 --order 24 --workers 1` | `kappa/params/J24.json` (`55fde513…7d207e30`) | Arb, 500 bits; Taylor order 24; ε = 10⁻⁹³; x_far = 70; 456 pieces | 8 s | `(4) kappa* <= A_upper / Fhat_H(0)_lower <= 5.2941806e-91`; `CERTIFIED: True` |
| κ* ≤ 1.1963682·10⁻⁸⁰ (cushioned cross-check) | `python kappa/verify_kappa.py kappa/params/J23.json --prec 500 --order 24 --workers 1` | `kappa/params/J23.json` (`9ea699b1…dde66e80`) | Arb, 500 bits; Taylor order 24; ε = 10⁻⁸⁶; x_far = 66; 409 pieces | 7 s | `(4) kappa* <= A_upper / Fhat_H(0)_lower <= 1.1963682e-80`; `CERTIFIED: True` |
| κ* ≤ 2.0151627·10⁻⁶² (cushioned cross-check) | `python kappa/verify_kappa.py kappa/params/J20.json --prec 600 --order 28 --workers 1` | `kappa/params/J20.json` (`d686e47b…551c5ec8`) | Arb, 600 bits; Taylor order 28; ε = 10⁻⁶⁷; x_far = 55; 215 pieces | 7 s | `(4) kappa* <= A_upper / Fhat_H(0)_lower <= 2.0151627e-62`; `CERTIFIED: True` |
| H ≥ 1 on ℝ for the nine cushioned functions (every coefficient of P ≥ 0, P(0) = 1, where H(t) = P(t²)), hence F_rep ≥ Ξ²; and, by weak duality, ∫Ξ²dμ ≤ 3.21·10⁻⁹⁰⁶ for every admissible pair (J = 100; cross-check, superseded by `cone/`) | `python kappa/check_H_nonneg.py kappa/params/J20.json kappa/params/J23.json kappa/params/J24.json kappa/params/J30.json kappa/params/J35.json kappa/params/J40.json kappa/params/J50.json kappa/params/J60.json kappa/params/J100.json --duality-log kappa/logs/J100.log` | `kappa/params/J20.json` (`d686e47b…551c5ec8`)<br>`kappa/params/J23.json` (`9ea699b1…dde66e80`)<br>`kappa/params/J24.json` (`55fde513…7d207e30`)<br>`kappa/params/J30.json` (`472a5a88…ba0c201c`)<br>`kappa/params/J35.json` (`35e8cc8e…33ae7dcb`)<br>`kappa/params/J40.json` (`b3b71157…897e8884`)<br>`kappa/params/J50.json` (`3e95b34b…bff3d100`)<br>`kappa/params/J60.json` (`e22afd87…71e94a7e`)<br>`kappa/params/J100.json` (`1186be2c…90719662`) | exact (P expanded over ℚ); 𝒜_upper read from `kappa/logs/J100.log` (its parameter hash and certification are checked) | 56 s | `CLAIM      : J = 100: all coefficients of P >= 0 and P(0) = 1, so H >= 1 on R and F_rep >= Xi^2 ... implied`; `CLAIM      : J = 100: every admissible pair (mu, nu) has int Xi^2 dmu <= int F_rep dmu <= A(F_rep) <= 3.21e-906 ... implied`; `RESULT     : CERTIFIED` |
| The cushion constants 𝒜(Ξ²e^{−πt²}) and I_δ | `python kappa/cushion_A.py` | — | Arb: `acb.integral` at 128 bits on [0, 8] plus tail bound; I_δ from K₀, K₁ at 200 bits on 50 monotone pieces | < 1 s | `A(Xi^2 e^{-pi t^2}) = [0.930646274515431 +/- 2.27e-16]`; `rounded up: A <= 9.30646274516e-1`; `(rounded down: 9.782880564e-2)` |
| Validation of K₀, K₁, of the Bessel form and of the explicit-formula normalisation (**not a certificate**) | `python kappa/selftest.py` | — | Arb (1000 bits for K₀, K₁; 200 bits) against mpmath and direct integration | 247 s | `SELFTEST PASSED: True` |

### 6.2 The exact members P_J (`exact/`)

The enclosures `exact/out/P{J}_ball.txt` are the certified outputs of `verify_exact_member.py`.

| Claim (label) | Command (from the top directory) | Input (SHA-256, abbreviated) | Method; precision | Runtime | Expected output (verbatim) |
|---|---|---|---|---|---|
| Finite-J instance J = 60: (N), all p_k > 0, max_k((2k)!p_k)^{1/2k} ≤ 0.716207 | `python exact/verify_exact_member.py 60 --prec 1800 --workers 2 --ref exact/ref/P60_ref.txt --out exact/out/P60_ball.txt` | `exact/ref/P60_ref.txt` (`cf6cff39…52263576`) | Arb 1800 bits; moments Ψ^{(j)}, j ≤ 241; 120 × 120 preconditioned ball solve; writes `exact/out/P60_ball.txt` | 45 s (W = 2) | `(POS) all 121 coefficients p_k certified > 0: True`; `a = max_k ((2k)! p_k)^(1/2k) <= 0.716207`; `every ball overlaps the new enclosure: True`; `CERTIFIED (N) and (POS) at J = 60: True` |
| Finite-J instance J = 61: (N), all p_k > 0, max_k((2k)!p_k)^{1/2k} ≤ 0.716214 | `python exact/verify_exact_member.py 61 --prec 2000 --workers 2 --ref exact/ref/P61_ref.txt --out exact/out/P61_ball.txt` | `exact/ref/P61_ref.txt` (`532d0576…7b2f9637`) | Arb 2000 bits; 122 × 122 system; writes `exact/out/P61_ball.txt` | 54 s (W = 2) | `(POS) all 123 coefficients p_k certified > 0: True`; `a = max_k ((2k)! p_k)^(1/2k) <= 0.716214`; `CERTIFIED (N) and (POS) at J = 61: True` |
| Finite-J instance J = 110: (N), all p_k > 0, max_k((2k)!p_k)^{1/2k} ≤ 0.716351 | `python exact/verify_exact_member.py 110 --prec 3000 --workers 2 --ref exact/ref/P110_ref.txt --out exact/out/P110_ball.txt` | `exact/ref/P110_ref.txt` (`dcba593f…d53ef043`) | Arb 3000 bits; 220 × 220 system; writes `exact/out/P110_ball.txt` | 732 s (W = 2) | `(POS) all 221 coefficients p_k certified > 0: True`; `a = max_k ((2k)! p_k)^(1/2k) <= 0.716351`; `CERTIFIED (N) and (POS) at J = 110: True` |
| Finite-J instance J = 111: (N), all p_k > 0, max_k((2k)!p_k)^{1/2k} ≤ 0.716352 | `python exact/verify_exact_member.py 111 --prec 3000 --workers 2 --ref exact/ref/P111_ref.txt --out exact/out/P111_ball.txt` | `exact/ref/P111_ref.txt` (`0300ef95…0312c8cc`) | Arb 3000 bits; 222 × 222 system; writes `exact/out/P111_ball.txt` | 729 s (W = 2) | `(POS) all 223 coefficients p_k certified > 0: True`; `a = max_k ((2k)! p_k)^(1/2k) <= 0.716352`; `CERTIFIED (N) and (POS) at J = 111: True` |
| Finite-J instances J = 60, 61, 110, 111: 0 < p_k ≤ 0.71636^{2k}/(2k)! for every k | `python exact/check_coefficient_bound.py --bound 0.71636 exact/out/P60_ball.txt exact/out/P61_ball.txt exact/out/P110_ball.txt exact/out/P111_ball.txt` | `exact/out/P60_ball.txt` (`fdfbfe57…db6cda4b`)<br>`exact/out/P61_ball.txt` (`8cc7b2b9…91ca3dd4`)<br>`exact/out/P110_ball.txt` (`7c899956…f51c117a`)<br>`exact/out/P111_ball.txt` (`25669a32…f708b3f1`) | Arb (upper endpoints of the certified balls); exact comparison with 0.71636 | < 1 s | `CERTIFIED: 0 < p_k <= 0.71636^(2k)/(2k)! for every k, at J = 60, 61, 110, 111: True` |
| Finite-J instance J = 10: (N), all p_k > 0, max_k((2k)!p_k)^{1/2k} ≤ 0.697078 | `python exact/verify_exact_member.py 10 --prec 800 --workers 2 --ref exact/ref/P10_ref.txt --out exact/out/P10_ball.txt` | `exact/ref/P10_ref.txt` (`101eba60…db8a7971`) | Arb 800 bits; 20 × 20 system; writes `exact/out/P10_ball.txt` | < 1 s (W = 2) | `(POS) all 21 coefficients p_k certified > 0: True`; `a = max_k ((2k)! p_k)^(1/2k) <= 0.697078`; `CERTIFIED (N) and (POS) at J = 10: True` |

### 6.3 The Gaussian–Laguerre family (`general/`)

The corollaries and the window bounds read the summaries `general/results/*.json` written by the runs they name and
check that each summary belongs to the current parameter file (SHA-256) and is certified.

| Claim (label) | Command (from the top directory) | Input (SHA-256, abbreviated) | Method; precision | Runtime | Expected output (verbatim) |
|---|---|---|---|---|---|
| Proposition 5.4 (Gaussian–Laguerre): κ* ≤ κ*_OPS ≤ 9.9462·10⁻⁴¹; q_min ≥ 1 − 6.25·10⁻⁴⁰ | `python general/verify_general.py general/params/zeta_K128_s13.json` | `general/params/zeta_K128_s13.json` (`0976a671…879a4df2`) | exact Sturm sequences over ℚ (K = 128, s = 13, ε = 10⁻⁵⁶); Arb integral on [0, 220] at 512 bits | 557 s | `kappa*_OPS (and kappa*) of the data <= 9.9461827001452550725e-41`; `q_min = exp(-2 pi kappa*) >= 1 - 6.24938e-40`; `RESULT         : CERTIFIED` |
| The low-height windows: the function F₈₀, 𝒜(F₈₀)/∫F₈₀ ≤ 7.7253·10⁻²⁵ | `python general/verify_general.py general/params/zeta_K80_s12_F80.json` | `general/params/zeta_K80_s12_F80.json` (`c0f3afc2…a845eee6`) | exact Sturm (K = 80, s = 12, ε = 10⁻³⁰); Arb integral on [0, 200] at 512 bits | 296 s | `kappa*_OPS (and kappa*) of the data <= 7.7252542459488902828e-25`; `RESULT         : CERTIFIED` |
| The low-height windows: 59 lower bounds for F₈₀ and F̂₈₀, and the 13 window and atom bounds stated in the paper | `python general/verify_windows.py general/params/F80_windows.json 2` | `general/params/F80_windows.json` (`af90186b…e9579b24`)<br>`general/results/zeta_K80_s12_F80.json` (`0868ce12…a8c02533`) | exact (ℚ[x]; Descartes after a Möbius map; rational Taylor majorant of e^{X/2}); Arb 600 bits at the atoms | 2 s (W = 2) | `LOWER BOUNDS   : 59/59 proved`; `mu([14.2347251418, 20.9220396387]) <= 2.745e-17`; `nu([xi(2.05), xi(2.95)]) <= 6.801e-19`; `nu({xi_n}) <= 1.530e-21`; `RESULT         : CERTIFIED` |
| Γ_ℝ², one pole: κ*₀ ≤ −0.25566705789831547610, q_min ≥ 4.98485094226764 (control example ℚ(√5)) | `python general/verify_general.py general/params/gammaR2_K80_s7.json` | `general/params/gammaR2_K80_s7.json` (`79936770…026a71ee`) | exact Sturm (K = 80, s = 7); Arb integral on [0, 120] at 448 bits | 168 s | `kappa*_OPS (and kappa*) of the data <= -0.25566705789831547610`; `q_min >= 4.9848509422676437635`; `RESULT         : CERTIFIED` |
| Γ_ℝ², one pole: admissible pair at log q₀ = 1.6093347792651136, hence q_min ≤ 4.9994844; its prime measure lives on [ξ₄, ∞), the natural gap of ℚ(√5) (control example ℚ(√5)) | `python general/verify_pair.py general/params/pair_gammaR2_X240.json --gap-x 4` | `general/params/pair_gammaR2_X240.json` (`3b9f85c8…2b7dfb1d`) | Arb 128 bits; 17 214 mean-value steps on [0, 800] and monotone majorants beyond | 37 s | `nu~ support    : supp nu~ in [x0, oo) with x0 >= 4.049150`; `MU FLOOR       : mu(t) >= 6.59497e-9 for all real t`; `hence q_min(data) <= 4.9994844`; `GAP            : admissible at gap xi_4 (prime measure on [4, oo)): True`; `RESULT         : CERTIFIED` |
| Control example ℚ(√5): κ* ∈ [1.64·10⁻⁵, 4.83·10⁻⁴], so these data are not critical; the same at the natural gap ξ₄ | `python general/corollary_slack.py general/params/corollary_qsqrt5.json --gap-x 4` | `general/params/corollary_qsqrt5.json` (`540d1ad6…4b4afbab`)<br>`general/results/gammaR2_K80_s7.json` (`04a2de0c…fcca2e8b`)<br>`general/results/pair_gammaR2_X240.json` (`d76c8c61…5b7cd129`) | exact and Arb arithmetic on the two certified summaries (their parameter hashes are checked) | < 1 s | `SLACK      : 1.6420748e-5 <= kappa*(Q(sqrt 5)) <= 0.00048294147`; `CLAIM      : kappa*(Q(sqrt 5)) >= 1.64e-5 ... implied`; `CLAIM      : the bracket and the slack interval hold at the natural gap xi_4 of Q(sqrt 5) (4 <= x0) ... implied`; `RESULT     : CERTIFIED` |
| Γ_ℂ, one pole: dual certificate, q_min ≥ 2.981236704765 (control example ℚ(√−3)) | `python general/verify_general.py general/params/gammaC_K64_s9.json` | `general/params/gammaC_K64_s9.json` (`e330d8b7…c296021a`) | exact Sturm (K = 64, s = 9); Arb integral on [0, 160] at 448 bits | 187 s | `q_min >= 2.9812367047650810559`; `RESULT         : CERTIFIED` |
| Γ_ℂ, one pole: admissible pair at log q₀ = 1.0976698108720329, hence q_min ≤ 2.997174; its prime measure lives on [ξ₃, ∞), the natural gap of ℚ(√−3) (control example ℚ(√−3)) | `python general/verify_pair.py general/params/pair_gammaC_X40.json --gap-x 3` | `general/params/pair_gammaC_X40.json` (`f32152ae…2828eeae`) | Arb 128 bits; 9501 mean-value steps on [0, 800] and monotone majorants beyond | 19 s | `nu~ support    : supp nu~ in [x0, oo) with x0 >= 3.011664`; `MU FLOOR       : mu(t) >= 6.67226e-8 for all real t`; `GAP            : admissible at gap xi_3 (prime measure on [3, oo)): True`; `RESULT         : CERTIFIED` |
| Control example ℚ(√−3): κ* ∈ [1.5·10⁻⁴, 9.99·10⁻⁴], so these data are not critical; the same at the natural gap ξ₃ | `python general/corollary_slack.py general/params/corollary_qsqrtm3.json --gap-x 3` | `general/params/corollary_qsqrtm3.json` (`c0011615…6a7fd822`)<br>`general/results/gammaC_K64_s9.json` (`b51249bf…256def9f`)<br>`general/results/pair_gammaC_X40.json` (`83c8d09d…989672fb`) | exact and Arb arithmetic on the two certified summaries (hashes checked) | < 1 s | `SLACK      : 0.00015006672 <= kappa*(Q(sqrt -3)) <= 0.00099854968`; `CLAIM      : the bracket and the slack interval hold at the natural gap xi_3 of Q(sqrt -3) (3 <= x0) ... implied`; `RESULT     : CERTIFIED` |
| The slack lower bound: an admissible pair for ζ's data at log q = 0.02 with μ ≥ 4.71949·10⁻⁴ on all of ℝ; hence κ* ≥ 4.71949·10⁻⁴ − 0.02/(2π) ≥ −2.7112·10⁻³ | `python general/verify_pair.py general/params/pair_zeta_logq002_X10.json --gap-x 2` | `general/params/pair_zeta_logq002_X10.json` (`d28b347d…708888f6`) | Arb 128 bits; 8437 mean-value steps on [0, 2000] and monotone majorants beyond | 12 s | `MU FLOOR       : mu(t) >= 0.000471949 for all real t`; `CLAIM          : kappa*(data with log q = 0) >= -2.7112e-3 ... implied`; `GAP            : admissible at gap xi_2 (prime measure on [2, oo)): True`; `RESULT         : CERTIFIED` |
| Identity 𝒜_q(F) = ∫Fμ + (1/π)∫F̂dν for the Γ_ℝ² pair (X = 240) at σ = 1.5 and 0.7 (**not a certificate**) | `python general/check_pair_identity.py general/params/pair_gammaR2_X240.json 1.5`<br>`python general/check_pair_identity.py general/params/pair_gammaR2_X240.json 0.7` | `general/params/pair_gammaR2_X240.json` (`3b9f85c8…2b7dfb1d`) | mpmath, 30 digits (floating point) | 88 s; 84 s | `residual A_q(F) - (int F mu + (1/pi) int F^ dnu) = 1.9722e-31`; `residual A_q(F) - (int F mu + (1/pi) int F^ dnu) = 1.5777e-30` |
| Identity 𝒜_q(F) = ∫Fμ + (1/π)∫F̂dν for the Γ_ℂ pair (X = 40) at σ = 1.5 and 0.7 (**not a certificate**) | `python general/check_pair_identity.py general/params/pair_gammaC_X40.json 1.5`<br>`python general/check_pair_identity.py general/params/pair_gammaC_X40.json 0.7` | `general/params/pair_gammaC_X40.json` (`f32152ae…2828eeae`) | mpmath, 30 digits (floating point) | 83 s; 80 s | `residual A_q(F) - (int F mu + (1/pi) int F^ dnu) = -1.9722e-31`; `residual A_q(F) - (int F mu + (1/pi) int F^ dnu) = -3.1554e-30` |
| Identity 𝒜_q(F) = ∫Fμ + (1/π)∫F̂dν for the ζ pair (log q = 0.02) at σ = 1.5 and 0.7 (**not a certificate**) | `python general/check_pair_identity.py general/params/pair_zeta_logq002_X10.json 1.5`<br>`python general/check_pair_identity.py general/params/pair_zeta_logq002_X10.json 0.7` | `general/params/pair_zeta_logq002_X10.json` (`d28b347d…708888f6`) | mpmath, 30 digits (floating point) | 66 s; 63 s | `residual A_q(F) - (int F mu + (1/pi) int F^ dnu) = 1.9722e-31`; `residual A_q(F) - (int F mu + (1/pi) int F^ dnu) = -1.5777e-30` |

### 6.4 The exact members in the cone (`cone/`)

Every run reads a certified enclosure of P_J (Section 6.2; `exact/ref/` for the second path) and checks its SHA-256
(`--sha`); the full hashes are in Section 7. Each run writes the summary `cone/out/<log name>.json`. The x_min = 2 runs
prove the claims about 𝒞, 𝒜(F_J), κ_J and near-rigidity; the x_min = 1 runs extend the non-negativity of F̂_J to [0, ∞),
which gives 𝒞_OPS. The second evaluation path and the comparison corroborate these runs; no claim of the paper rests on
them.

| Claim (label) | Command (from the top directory) | Input (SHA-256, abbreviated) | Method; precision | Runtime | Expected output (verbatim) |
|---|---|---|---|---|---|
| J = 111: F_111 ∈ 𝒞 exactly (no cushion; F̂ ≥ 0 on [ξ₂, ∞) with exact double zeros at the 111 nodes, F ≥ Ξ²); 𝒜(F_111) ∈ [3.98510732131·10⁻¹⁰⁶⁰, 3.98510732132·10⁻¹⁰⁶⁰]; κ* ≤ 1.4291572·10⁻¹⁰⁶⁰ (Theorem 5.1, Table 1, Corollaries 5.2 and 5.3); every admissible pair has ∫Ξ²dμ ≤ 3.9851074·10⁻¹⁰⁶⁰ | `python cone/cert_exact.py 111 --pball exact/out/P111_ball.txt --sha 25669a321f71ddef789247cd0adc0fd129c5d70f293e488bc4dab8c3f708b3f1 --prec 3000 --order 28 --order-far 64 --order-switch 121 --workers 3 --xmin 2 --cost 800 --json cone/out/W_J111_x2.json` | `exact/out/P111_ball.txt` (`25669a32…f708b3f1`) | Arb 3000 bits; Taylor order 28 (x < 121), 64 (x ≥ 121); x₀ = 4793/10; 6448 pieces; terms n ≤ 800 enclosed, tail ≤ 2.52e-1759 | 542 s (W = 3) | `W_J: Fhat_J >= 0 on [x = 2, oo), with exact double zeros at the 111 nodes and Fhat_J > 0 elsewhere: True`; `A(F_J) in [3.98510732131e-1060, 3.98510732132e-1060]`; `kappa_J^exact = A(F_J)/int F_J in [1.429157161e-1060, 1.429157162e-1060]  =>  kappa* <= 1.4291572e-1060`; `near-rigidity: every admissible pair (mu, nu) has int Xi^2 dmu <= int F_J dmu <= A(F_J) <= 3.9851074e-1060`; `CERTIFIED: True` |
| J = 110: F_110 ∈ 𝒞 exactly (no cushion; F̂ ≥ 0 on [ξ₂, ∞) with exact double zeros at the 110 nodes, F ≥ Ξ²); 𝒜(F_110) ∈ [5.57968396330·10⁻¹⁰⁴², 5.57968396331·10⁻¹⁰⁴²]; κ* ≤ 2.0010115·10⁻¹⁰⁴² (Table 1); every admissible pair has ∫Ξ²dμ ≤ 5.5796840·10⁻¹⁰⁴² | `python cone/cert_exact.py 110 --pball exact/out/P110_ball.txt --sha 7c8999567bc77cd1c6fb5a9e816bb0b4f212b971f26dd0f3bda3237ff51c117a --prec 3000 --order 28 --order-far 64 --order-switch 121 --workers 3 --xmin 2 --cost 800 --json cone/out/W_J110_x2.json` | `exact/out/P110_ball.txt` (`7c899956…f51c117a`) | Arb 3000 bits; Taylor order 28 (x < 121), 64 (x ≥ 121); x₀ = 9347/20; 6298 pieces; terms n ≤ 800 enclosed, tail ≤ 1.30e-1760 | 543 s (W = 3) | `W_J: Fhat_J >= 0 on [x = 2, oo), with exact double zeros at the 110 nodes and Fhat_J > 0 elsewhere: True`; `A(F_J) in [5.57968396330e-1042, 5.57968396331e-1042]`; `kappa_J^exact = A(F_J)/int F_J in [2.001011429e-1042, 2.001011430e-1042]  =>  kappa* <= 2.0010115e-1042`; `near-rigidity: every admissible pair (mu, nu) has int Xi^2 dmu <= int F_J dmu <= A(F_J) <= 5.5796840e-1042`; `CERTIFIED: True` |
| J = 61: F_61 ∈ 𝒞 exactly (no cushion; F̂ ≥ 0 on [ξ₂, ∞) with exact double zeros at the 61 nodes, F ≥ Ξ²); 𝒜(F_61) ∈ [6.50716403226·10⁻⁴⁴², 6.50716403227·10⁻⁴⁴²]; κ* ≤ 2.3336286·10⁻⁴⁴² (Table 1); every admissible pair has ∫Ξ²dμ ≤ 6.5071641·10⁻⁴⁴² | `python cone/cert_exact.py 61 --pball exact/out/P61_ball.txt --sha 8cc7b2b9a66f643e8e40d84fd4ffd6970401342aeab87b716ec169bc91ca3dd4 --prec 2000 --order 28 --order-far 48 --order-switch 80 --workers 3 --xmin 2 --cost 400 --json cone/out/W_J61_x2.json` | `exact/out/P61_ball.txt` (`8cc7b2b9…91ca3dd4`) | Arb 2000 bits; Taylor order 28 (x < 80), 48 (x ≥ 80); x₀ = 2113/10; 1392 pieces; terms n ≤ 400 enclosed, tail ≤ 9.22e-834 | 40 s (W = 3) | `W_J: Fhat_J >= 0 on [x = 2, oo), with exact double zeros at the 61 nodes and Fhat_J > 0 elsewhere: True`; `A(F_J) in [6.50716403226e-442, 6.50716403227e-442]`; `kappa_J^exact = A(F_J)/int F_J in [2.333628513e-442, 2.333628514e-442]  =>  kappa* <= 2.3336286e-442`; `near-rigidity: every admissible pair (mu, nu) has int Xi^2 dmu <= int F_J dmu <= A(F_J) <= 6.5071641e-442`; `CERTIFIED: True` |
| J = 60: F_60 ∈ 𝒞 exactly (no cushion; F̂ ≥ 0 on [ξ₂, ∞) with exact double zeros at the 60 nodes, F ≥ Ξ²); 𝒜(F_60) ∈ [2.96693123411·10⁻⁴¹⁷, 2.96693123412·10⁻⁴¹⁷]; κ* ≤ 1.0640143·10⁻⁴¹⁷ (Table 1); every admissible pair has ∫Ξ²dμ ≤ 2.9669313·10⁻⁴¹⁷ | `python cone/cert_exact.py 60 --pball exact/out/P60_ball.txt --sha fdfbfe57bfe9945f640291b6f1e1b7e74e4d5afb04278961d5737f26db6cda4b --prec 1800 --order 28 --order-far 48 --order-switch 80 --workers 3 --xmin 2 --cost 400 --json cone/out/W_J60_x2.json` | `exact/out/P60_ball.txt` (`fdfbfe57…db6cda4b`) | Arb 1800 bits; Taylor order 28 (x < 80), 48 (x ≥ 80); x₀ = 997/5; 1342 pieces; terms n ≤ 400 enclosed, tail ≤ 2.88e-835 | 33 s (W = 3) | `W_J: Fhat_J >= 0 on [x = 2, oo), with exact double zeros at the 60 nodes and Fhat_J > 0 elsewhere: True`; `A(F_J) in [2.96693123411e-417, 2.96693123412e-417]`; `kappa_J^exact = A(F_J)/int F_J in [1.064014260e-417, 1.064014261e-417]  =>  kappa* <= 1.0640143e-417`; `near-rigidity: every admissible pair (mu, nu) has int Xi^2 dmu <= int F_J dmu <= A(F_J) <= 2.9669313e-417`; `CERTIFIED: True` |
| J = 10: F_10 ∈ 𝒞 exactly (no cushion; F̂ ≥ 0 on [ξ₂, ∞) with exact double zeros at the 10 nodes, F ≥ Ξ²); 𝒜(F_10) ∈ [4.21255630297·10⁻¹⁹, 4.21255630298·10⁻¹⁹]; κ* ≤ 1.5107258·10⁻¹⁹ (Table 1); every admissible pair has ∫Ξ²dμ ≤ 4.2125564·10⁻¹⁹ | `python cone/cert_exact.py 10 --pball exact/out/P10_ball.txt --sha 4e55d361d6d2c05f15565bd3c94d56b9f5e0715acecda9fd362410181bdc48d3 --prec 800 --order 24 --workers 3 --xmin 2 --cost 400 --json cone/out/W_J10_x2.json` | `exact/out/P10_ball.txt` (`4e55d361…1bdc48d3`) | Arb 800 bits; Taylor order 24; x₀ = 329/20; 67 pieces; terms n ≤ 400 enclosed, tail ≤ 6.17e-998 | 1.1 s (W = 3) | `W_J: Fhat_J >= 0 on [x = 2, oo), with exact double zeros at the 10 nodes and Fhat_J > 0 elsewhere: True`; `A(F_J) in [4.21255630297e-19, 4.21255630298e-19]`; `kappa_J^exact = A(F_J)/int F_J in [1.510725775e-19, 1.510725776e-19]  =>  kappa* <= 1.5107258e-19`; `near-rigidity: every admissible pair (mu, nu) has int Xi^2 dmu <= int F_J dmu <= A(F_J) <= 4.2125564e-19`; `CERTIFIED: True` |
| F̂_J ≥ 0 on [0, ∞) (x ≥ 1), hence on ℝ, with exact double zeros at the J nodes: F_J ∈ 𝒞_OPS for J = 10, 60, 61, 110, 111 (Proposition 5.7(b), Theorem 5.1, the classical-cone clause of Corollary 5.2) | `python cone/cert_exact.py 10 --pball exact/out/P10_ball.txt --sha 4e55d361d6d2c05f15565bd3c94d56b9f5e0715acecda9fd362410181bdc48d3 --prec 800 --order 24 --workers 3 --xmin 1 --json cone/out/W_J10_x1.json`<br>`python cone/cert_exact.py 60 --pball exact/out/P60_ball.txt --sha fdfbfe57bfe9945f640291b6f1e1b7e74e4d5afb04278961d5737f26db6cda4b --prec 1800 --order 28 --order-far 48 --order-switch 80 --workers 3 --xmin 1 --json cone/out/W_J60_x1.json`<br>`python cone/cert_exact.py 61 --pball exact/out/P61_ball.txt --sha 8cc7b2b9a66f643e8e40d84fd4ffd6970401342aeab87b716ec169bc91ca3dd4 --prec 2000 --order 28 --order-far 48 --order-switch 80 --workers 3 --xmin 1 --json cone/out/W_J61_x1.json`<br>`python cone/cert_exact.py 110 --pball exact/out/P110_ball.txt --sha 7c8999567bc77cd1c6fb5a9e816bb0b4f212b971f26dd0f3bda3237ff51c117a --prec 3000 --order 28 --order-far 64 --order-switch 121 --workers 3 --xmin 1 --json cone/out/W_J110_x1.json`<br>`python cone/cert_exact.py 111 --pball exact/out/P111_ball.txt --sha 25669a321f71ddef789247cd0adc0fd129c5d70f293e488bc4dab8c3f708b3f1 --prec 3000 --order 28 --order-far 64 --order-switch 121 --workers 3 --xmin 1 --json cone/out/W_J111_x1.json` | `exact/out/P{J}_ball.txt` (as above) | as above, all node items two-sided; the first gap piece starts at ξ = 0 | 2.0 s; 37 s; 44 s; 537 s; 584 s (W = 3) | `W_J: Fhat_J >= 0 on [x = 1, oo), with exact double zeros at the 10 nodes and Fhat_J > 0 elsewhere: True`<br>`W_J: Fhat_J >= 0 on [x = 1, oo), with exact double zeros at the 60 nodes and Fhat_J > 0 elsewhere: True`<br>`W_J: Fhat_J >= 0 on [x = 1, oo), with exact double zeros at the 61 nodes and Fhat_J > 0 elsewhere: True`<br>`W_J: Fhat_J >= 0 on [x = 1, oo), with exact double zeros at the 110 nodes and Fhat_J > 0 elsewhere: True`<br>`W_J: Fhat_J >= 0 on [x = 1, oo), with exact double zeros at the 111 nodes and Fhat_J > 0 elsewhere: True`; each run: `CERTIFIED: True` |
| Second evaluation path (**corroboration, not a certificate the paper relies on**): the same ten runs (both ranges, five J) through independently computed enclosures, an independent operator construction and the series/asymptotic K₀, K₁ | `python cone/cert_exact_alt.py 10 --pball exact/ref/P10_ref.txt --sha 101eba6041a44d9ecf7f8f2fb267899759d9b048fcf5fa420499b516db8a7971 --prec 800 --order 24 --workers 3 --xmin 2 --kback series --cost 400 --json cone/out/Wref_J10_x2.json`<br>`python cone/cert_exact_alt.py 60 --pball exact/ref/P60_ref.txt --sha cf6cff397c3fe1ba5084331132b52fc35f15a41a1fa84f11db6126f752263576 --prec 1800 --order 28 --order-far 48 --order-switch 80 --workers 3 --xmin 2 --kback series --cost 400 --json cone/out/Wref_J60_x2.json`<br>`python cone/cert_exact_alt.py 61 --pball exact/ref/P61_ref.txt --sha 532d0576df70320ebee3e286cca7b75fcae559a4eb5837f8bfaa17ff7b2f9637 --prec 2000 --order 28 --order-far 48 --order-switch 80 --workers 3 --xmin 2 --kback series --cost 400 --json cone/out/Wref_J61_x2.json`<br>`python cone/cert_exact_alt.py 110 --pball exact/ref/P110_ref.txt --sha dcba593fad1b1e11ce5320bb05c990dd9d3894879be4f2767ad9a483d53ef043 --prec 3000 --order 28 --order-far 64 --order-switch 121 --workers 3 --xmin 2 --kback series --cost 800 --json cone/out/Wref_J110_x2.json`<br>`python cone/cert_exact_alt.py 111 --pball exact/ref/P111_ref.txt --sha 0300ef95e96fc6f41cc341faa1b1b760f1db40a80da2f2c7cd80939d0312c8cc --prec 3000 --order 28 --order-far 64 --order-switch 121 --workers 3 --xmin 2 --kback series --cost 800 --json cone/out/Wref_J111_x2.json`<br>`python cone/cert_exact_alt.py 10 --pball exact/ref/P10_ref.txt --sha 101eba6041a44d9ecf7f8f2fb267899759d9b048fcf5fa420499b516db8a7971 --prec 800 --order 24 --workers 3 --xmin 1 --kback series --json cone/out/Wref_J10_x1.json`<br>`python cone/cert_exact_alt.py 60 --pball exact/ref/P60_ref.txt --sha cf6cff397c3fe1ba5084331132b52fc35f15a41a1fa84f11db6126f752263576 --prec 1800 --order 28 --order-far 48 --order-switch 80 --workers 3 --xmin 1 --kback series --json cone/out/Wref_J60_x1.json`<br>`python cone/cert_exact_alt.py 61 --pball exact/ref/P61_ref.txt --sha 532d0576df70320ebee3e286cca7b75fcae559a4eb5837f8bfaa17ff7b2f9637 --prec 2000 --order 28 --order-far 48 --order-switch 80 --workers 3 --xmin 1 --kback series --json cone/out/Wref_J61_x1.json`<br>`python cone/cert_exact_alt.py 110 --pball exact/ref/P110_ref.txt --sha dcba593fad1b1e11ce5320bb05c990dd9d3894879be4f2767ad9a483d53ef043 --prec 3000 --order 28 --order-far 64 --order-switch 121 --workers 3 --xmin 1 --kback series --json cone/out/Wref_J110_x1.json`<br>`python cone/cert_exact_alt.py 111 --pball exact/ref/P111_ref.txt --sha 0300ef95e96fc6f41cc341faa1b1b760f1db40a80da2f2c7cd80939d0312c8cc --prec 3000 --order 28 --order-far 64 --order-switch 121 --workers 3 --xmin 1 --kback series --json cone/out/Wref_J111_x1.json` | `exact/ref/P{J}_ref.txt` (Section 7) | as above, `--kback series` | x_min = 2: 1.4 s; 30 s; 37 s; 385 s; 396 s; x_min = 1: 2.4 s; 33 s; 40 s; 412 s; 409 s (W = 3) | every run: `CERTIFIED: True` |
| Consistency of the two paths (**not a certificate**): both certify every J, same x₀ and piece counts; for x_min = 2 the intervals for 𝒜(F_J) and κ_J overlap | `python cone/compare_runs.py 10,60,61,110,111 --xmin 2`<br>`python cone/compare_runs.py 10,60,61,110,111 --xmin 1` | `cone/out/*.json` | exact comparison of the JSON summaries | < 1 s | `ALL CONSISTENT` (both) |
| Validation of the two K₀, K₁ backends, of the Abel preimage, of the integral representation and of the Bernstein bounds (**not a certificate**) | `python cone/selftest.py` | `exact/out/P10_ball.txt` | Arb (200–800 bits) against mpmath, quadrature and an independent construction | 5.4 s | `ALL SELF-TESTS PASSED` |

## 7. Input and data files with SHA-256

| File | Content | SHA-256 |
|---|---|---|
| `kappa/params/J100.json` | zero-killing function F_rep (exact rational factors; canonical factor list hashed inside) | `1186be2c9c2e575810781c02fc8a22ee060ffa4c61be4e8eab21b63a90719662` |
| `kappa/params/J20.json` | zero-killing function F_rep (exact rational factors; canonical factor list hashed inside) | `d686e47b0412358c8ad519370655c6f8600c2d44d25ee8da8e39ab66551c5ec8` |
| `kappa/params/J23.json` | zero-killing function F_rep (exact rational factors; canonical factor list hashed inside) | `9ea699b1bb61092b89ce2fd2f0f57a560e9f1c4563daf81fca3e03e5dde66e80` |
| `kappa/params/J24.json` | zero-killing function F_rep (exact rational factors; canonical factor list hashed inside) | `55fde51339c382ccce6d0ad32c32db53e3a50bf825749b5eac0f6a097d207e30` |
| `kappa/params/J30.json` | zero-killing function F_rep (exact rational factors; canonical factor list hashed inside) | `472a5a881d5e96d55b8ce013e028416bd7bd7950ea936161a1dca60cba0c201c` |
| `kappa/params/J35.json` | zero-killing function F_rep (exact rational factors; canonical factor list hashed inside) | `35e8cc8eb2b4c5fc478b69807a9fbaa94ea60fee62548d71e641eef033ae7dcb` |
| `kappa/params/J40.json` | zero-killing function F_rep (exact rational factors; canonical factor list hashed inside) | `b3b711578a6e21ad75ad6c69ce3a1a384bfef1255f94ef365f1dab15897e8884` |
| `kappa/params/J50.json` | zero-killing function F_rep (exact rational factors; canonical factor list hashed inside) | `3e95b34b9579df88b72d66249e830d8af795816e702690bf209fb30fbff3d100` |
| `kappa/params/J60.json` | zero-killing function F_rep (exact rational factors; canonical factor list hashed inside) | `e22afd8721e40313f47f4ee5ab3415dcc4d5c24502c17c4994499a9971e94a7e` |
| `exact/out/P10_ball.txt` | certified enclosure of P_J (output of `exact/verify_exact_member.py`) | `4e55d361d6d2c05f15565bd3c94d56b9f5e0715acecda9fd362410181bdc48d3` |
| `exact/out/P110_ball.txt` | certified enclosure of P_J (output of `exact/verify_exact_member.py`) | `7c8999567bc77cd1c6fb5a9e816bb0b4f212b971f26dd0f3bda3237ff51c117a` |
| `exact/out/P111_ball.txt` | certified enclosure of P_J (output of `exact/verify_exact_member.py`) | `25669a321f71ddef789247cd0adc0fd129c5d70f293e488bc4dab8c3f708b3f1` |
| `exact/out/P60_ball.txt` | certified enclosure of P_J (output of `exact/verify_exact_member.py`) | `fdfbfe57bfe9945f640291b6f1e1b7e74e4d5afb04278961d5737f26db6cda4b` |
| `exact/out/P61_ball.txt` | certified enclosure of P_J (output of `exact/verify_exact_member.py`) | `8cc7b2b9a66f643e8e40d84fd4ffd6970401342aeab87b716ec169bc91ca3dd4` |
| `exact/ref/P10_ref.txt` | second, independently computed enclosure (overlap check only) | `101eba6041a44d9ecf7f8f2fb267899759d9b048fcf5fa420499b516db8a7971` |
| `exact/ref/P110_ref.txt` | second, independently computed enclosure (overlap check only) | `dcba593fad1b1e11ce5320bb05c990dd9d3894879be4f2767ad9a483d53ef043` |
| `exact/ref/P111_ref.txt` | second, independently computed enclosure (overlap check only) | `0300ef95e96fc6f41cc341faa1b1b760f1db40a80da2f2c7cd80939d0312c8cc` |
| `exact/ref/P60_ref.txt` | second, independently computed enclosure (overlap check only) | `cf6cff397c3fe1ba5084331132b52fc35f15a41a1fa84f11db6126f752263576` |
| `exact/ref/P61_ref.txt` | second, independently computed enclosure (overlap check only) | `532d0576df70320ebee3e286cca7b75fcae559a4eb5837f8bfaa17ff7b2f9637` |
| `cone/out/W_J{J}_x{X}.json`, `cone/out/Wref_J{J}_x{X}.json` | certificate summaries of `cone/` (outputs; input of `cone/compare_runs.py`; no timings, so a re-run reproduces them byte for byte) | `SHA256SUMS` |
| `general/params/F80_windows.json` | parameter file (Gaussian–Laguerre function, Herglotz pair, windows or corollary data) | `af90186bb2a9126187e3dd4b2358aec7ca4e69c40fbfef7a6daafdabe9579b24` |
| `general/params/corollary_qsqrt5.json` | parameter file (Gaussian–Laguerre function, Herglotz pair, windows or corollary data) | `540d1ad652df9feff6916301136f1a5c9656cb9eed46d745f1dda3674b4afbab` |
| `general/params/corollary_qsqrtm3.json` | parameter file (Gaussian–Laguerre function, Herglotz pair, windows or corollary data) | `c0011615f1a31599b4217b3c48b3718192c8b26a092faa34aea3058a6a7fd822` |
| `general/params/gammaC_K64_s9.json` | parameter file (Gaussian–Laguerre function, Herglotz pair, windows or corollary data) | `e330d8b743bd835920ecaad507a195773f4c858181d97bafb9d3eca1c296021a` |
| `general/params/gammaR2_K80_s7.json` | parameter file (Gaussian–Laguerre function, Herglotz pair, windows or corollary data) | `79936770a00991a3c4b24ac614f8405686fdf499d6eb0040dd9976ae026a71ee` |
| `general/params/pair_gammaC_X40.json` | parameter file (Gaussian–Laguerre function, Herglotz pair, windows or corollary data) | `f32152ae73a8e202fafd9bd56097dc0b98d68741392ee8149ee3d9262828eeae` |
| `general/params/pair_gammaR2_X240.json` | parameter file (Gaussian–Laguerre function, Herglotz pair, windows or corollary data) | `3b9f85c84efcf36f0e753e01edd442bfc3d6a1a2ead2377124b015ea2b7dfb1d` |
| `general/params/pair_zeta_logq002_X10.json` | parameter file (Gaussian–Laguerre function, Herglotz pair, windows or corollary data) | `d28b347d9807e6934a55bb326f20e09318c2aab4851595b914788f5c708888f6` |
| `general/params/zeta_K128_s13.json` | parameter file (Gaussian–Laguerre function, Herglotz pair, windows or corollary data) | `0976a6711193adc0f02a532931974b8ef4912337f79e39f59aa21445879a4df2` |
| `general/params/zeta_K80_s12_F80.json` | parameter file (Gaussian–Laguerre function, Herglotz pair, windows or corollary data) | `c0f3afc2d3367ebdadd0897a6e2f15fc5ae8a7caf8b7c6879b504119a845eee6` |
| `general/results/gammaC_K64_s9.json` | certificate summary (output of the run of the same name; input of the corollaries and windows) | `b51249bf71c6fdc858bd5511909830210018a8ec192dceef8362a1a8256def9f` |
| `general/results/gammaR2_K80_s7.json` | certificate summary (output of the run of the same name; input of the corollaries and windows) | `04a2de0c6141cc0a8ec66ce4a00b6595acb93e76a1d25e1e45ace87afcca2e8b` |
| `general/results/pair_gammaC_X40.json` | certificate summary (output of the run of the same name; input of the corollaries and windows) | `83c8d09df002c1c4f40aaf65f3b9b4f0088ec58f53619fb282bdc290989672fb` |
| `general/results/pair_gammaR2_X240.json` | certificate summary (output of the run of the same name; input of the corollaries and windows) | `d76c8c61ccedabaa795334a7bf9c0b321d51d1f3acec9259586083745b7cd129` |
| `general/results/pair_zeta_logq002_X10.json` | certificate summary (output of the run of the same name; input of the corollaries and windows) | `e6ede9ba1ca9f848038d1f8006a2924b8b4efbe92968a5c004b5e921367a8e16` |
| `general/results/zeta_K128_s13.json` | certificate summary (output of the run of the same name; input of the corollaries and windows) | `1d99cf539e9a3f00f0d40c0d686f1cb2cb3f61fd5fbf6a6bd549d533e5aec631` |
| `general/results/zeta_K80_s12_F80.json` | certificate summary (output of the run of the same name; input of the corollaries and windows) | `0868ce12d7fcfe6a3a2f3323b97dcb9f8f82018e7ddb0828b2a54290a8c02533` |
| `computed/family_J1_110.tsv` | computed table (**not** a certificate; Section 9) | `1242067a7e239ce779f12742e027bc32b3cd0cbd6282dc746df5da8b9b234750` |

## 8. Re-running and comparing with the shipped logs

From this directory, with `PY` set to a Python that has python-flint 0.9.0 and mpmath 1.3.0:

```sh
export PY=python3
kappa/run_all.sh        # cushion constants, self-test, κ* for J = 20 ... 100 (41.6 CPU-minutes)
exact/run_all.sh        # (N), (POS) and the coefficient bound at J = 10, 60, 61, 110, 111 (52.0 CPU-minutes)
cone/run_all.sh         # the exact members in the cone, both paths, x_min = 2 and 1, consistency (205.6 CPU-minutes)
general/run_all.sh      # classical cone, F₈₀ and windows, control examples, ζ pair, identity checks (29.1 CPU-minutes)
sha256sum -c SHA256SUMS # inputs and shipped outputs unchanged
```

The CPU-minutes are the sums of the wall times in the footers of the shipped logs, times the number of workers.

Each `run_all.sh` overwrites the logs in its `logs/` directory (and `exact/run_all.sh` rewrites `exact/out/`,
`cone/run_all.sh` rewrites `cone/out/`, `general/run_all.sh` rewrites `general/results/`), and stops at the first run that
does not certify (`set -e`). `cone/run_all.sh` reads `exact/out/`, so run it after `exact/run_all.sh`, or alone.
Run them on a copy of this directory and compare with the shipped logs:

```sh
cp -r anc anc-rerun && cd anc-rerun && export PY=python3 && kappa/run_all.sh && exact/run_all.sh && cone/run_all.sh && general/run_all.sh
python tools/logdiff.py ../anc .     # every log: IDENTICAL (dates, system line and timings are ignored)
sha256sum -c SHA256SUMS              # regenerated enclosures and summaries are byte-identical
```

The worker counts in the scripts are those of the shipped logs (`kappa/run_all.sh [W]`, default 1;
`exact/run_all.sh [W]`, default 2; `cone/run_all.sh [W] [WHAT]`, default 3). A single certificate is re-run with the command recorded in the first line of its
log, for example

```sh
./runlog.sh kappa/logs/J100.log "$PY" kappa/verify_kappa.py kappa/params/J100.json --prec 3300 --order 28 --order-far 64 --order-switch 121 --workers 1
```

The working precision, the Taylor orders and the number of workers affect only the running time, the width of the
enclosures and the header line of the log, not the validity of a successful run.

## 9. What is computed but not certified

The following numbers appear in the paper only as numerical observations. They come from high-precision
floating-point computations (not interval arithmetic). No theorem of the paper depends on them.

- **The family P_J for J ≤ 110** (`computed/family_J1_110.tsv`): for each J = 1, …, 110, the coefficient p₁, the top
  coefficient p_{2J}, the indices of non-positive coefficients, a_J = max_{1≤k≤2J}((2k)!|p_k|)^{1/(2k)}, the number of roots u
  with Re u > 0, min|Im t| and min|arg u|. The polynomials are floating-point solutions of the Hermite system at
  4600 bits (not interval-certified); the roots were isolated by Arb on these midpoint polynomials. The table shows:
  all coefficients positive for 10 ≤ J ≤ 110; for 3 ≤ J ≤ 9 the non-positive coefficients are p_{2J−1} and, for
  4 ≤ J ≤ 8, p_{2J−3}, while p_{2J} > 0 for every J; a_J increasing towards 0.71635; exactly three root pairs with
  Re u > 0 for J ≥ 10; min|Im t| increasing towards 9.6389. Only J = 10, 60, 61, 110, 111 are certified (Section 6.2).
- **The cushion-free ratios** 𝒜(Ξ²H)/F̂_{Ξ²H}(0) printed in the κ* logs are enclosures for the specific functions
  Ξ²H (the prime-power tail included), not bounds for κ*: without the cushion, F̂ need not be ≥ 0 on [ξ₂, ∞) after the
  parameters are rationalised.
- **Provenance not shipped.** The reference enclosures `exact/ref/P{J}_ref.txt` (used only for the overlap
  corroboration and as the input of the second evaluation path of `cone/`), the table `computed/family_J1_110.tsv` and the dense sign scans of F̂_J quoted in the paper (J = 20,
  30, 40, 50, 60, step 0.05) were produced by separate research scripts that depend on machine-specific paths and
  intermediate data; they are not shipped. A SHA-256 authenticates these files, not the computations that produced
  them. In particular, the dense sign scans and the location k ≈ 20–24 of the maximum in a_J, both quoted in the
  numerical observation on the exact family, cannot be reproduced from the shipped files (the table lists a_J only).
  No certificate depends on them.

## 10. Numerical traps

The following points were essential for these certificates; each of them, if ignored, produces wrong or unverifiable
numbers.

1. Exhaustion of working precision can look like a stall of an optimisation; precision must be monitored.
2. The positivity constraint must be imposed from ξ₂ = (log 2)/2π exactly; imposing it from a rounded value creates
   spurious corners and spurious zeros.
3. Solver tolerances must be far below the quantity certified (below κ*·10⁻³⁰ for the slack).
4. Rationalised parameters make F̂ slightly negative at the nodes and at ξ₂; hence the cushion term of `kappa/`. The exact
   members of `cone/` need no cushion, because the vanishing jets c₀ = c₁ = 0 at the nodes are subtracted exactly.
5. Arb's built-in Bessel and confluent hypergeometric functions lose about 2z/log 2 bits at moderate z and can be slow;
   no certificate uses them (`lib/besselk.py`).
6. Ball radii explode in cancelling recurrences; run them on midpoints and bound the error separately.
7. Constructing a ball from a decimal midpoint may round the midpoint to double precision; read decimals as exact
   rationals.
8. Suprema and infima read off a grid are not bounds; certified bounds on intervals need Taylor models or interval
   subdivision with remainder bounds.
9. Crude Taylor remainders blow up at large x, because P_J(−z²) is an alternating sum when all p_k > 0; the Taylor
    order must grow with x.
10. Certificates must record the exact parameters they certify (here by SHA-256), so that the certified object is
    unambiguous.

## 11. Software and hardware

- Python 3.10.12; python-flint 0.9.0 (built on FLINT 3.6.0, which contains Arb); mpmath 1.3.0. The header of every
  log records the versions actually used.
- The scripts are deterministic: a re-run with the same versions reproduces each log except for the date, the system
  line and the timings (checked with `tools/logdiff.py`).
- Runtimes are wall times on an Intel Xeon Platinum 8362 (2.8 GHz) shared with other jobs (one core per worker).
  Peak memory is below 200 MB per process.

## 12. Licence

Licence: Apache License 2.0 (see LICENSE at the repository root). Copyright 2026 Nic Johns.
