# Ancillary files: certified computations of *Hermite interpolation at the prime powers*

This directory contains every computer-assisted certificate used in the manuscript *Hermite interpolation at the prime
powers: a positivity calculus, a polynomial model, and a family of test functions vanishing at the zeros of ζ(s)*: the
exact parameter files, standalone verification scripts, and logs of fresh runs. Each statement that rests on a computation
is listed in Section 6 with its script, its exact input file (with SHA-256), the method and precision, the runtime and
the expected output. The directory is self-contained: it carries its own copy of the shared library and of the
certified enclosures it reads.

## 1. Requirements and conventions

- Python ≥ 3.10 with **python-flint 0.9.0** (FLINT/Arb ball arithmetic) and **mpmath 1.3.0** (only the log header
  queries its version). Nothing else is needed: `pip install python-flint==0.9.0 mpmath==1.3.0`. No script uses
  numpy, scipy or sympy.
- Run every command from this directory (the top directory of the ancillary files). Scripts locate their inputs relative
  to their own location.
- `./runlog.sh LOGFILE "$PY" SCRIPT ARGS` (after `export PY=python3`) runs one verifier and writes a log with a header
  (command, UTC date, system, software versions) and a footer (exit code, wall time). Every log shipped here was
  produced this way, in a fresh run of the shipped script on the shipped inputs.
- **Arithmetic.** "Exact" means integer/rational arithmetic (FLINT `fmpz`, `fmpq`, multivariate polynomials over ℤ or
  ℚ). "Arb" means rigorous ball arithmetic (midpoint–radius intervals with outward rounding) at the stated working
  precision in bits; every quantity printed as a ball `[m +/- r]` contains the exact value. Every sign decision is
  exact or a ball that excludes 0.
- **Explicit checks.** Every precondition and every check of a certificate is an explicit test that raises an exception
  or prints a failure and exits with a non-zero code; no certificate relies on `assert`, so running Python with `-O`
  does not disable any check (for example the check that the node list of a parameter file is the initial segment of
  the prime powers).
- **Exact inputs.** Every number that defines a certified object or a claim is read exactly (decimal or `p/q` strings
  converted to exact rationals, or Arb balls that contain them); nothing is read through binary64.
- **Rounding.** Every printed bound (a number after `<=` or `>=`) is rounded outward, with an exact check of the
  direction, never through binary64 arithmetic.
- Exit code 0 and the final success line listed in Section 6 mean that the certificate holds.
- `tools/logdiff.py` compares a re-run log with the shipped one after removing dates, the system line and timings
  (Section 8).

## 2. Layout

| Path | Contents |
|---|---|
| `lib/` | Shared library (a copy of the library of the ancillary files of Paper I). `besselk.py`: rigorous K₀, K₁. `bessel_form.py`: exact Bessel-operator form of F̂ for F = Ξ²P(t²), with rigorous divisor-sum tails. `cushion.py`: cushion constants (not used here). `common.py`: hashes, prime powers, explicit checks, outward decimal rounding. |
| `exact/` | Certificates for the exact members P_J of the true family: root geometry, Lemma BF instances, the base data (B), the ratio bounds R₁ and the coefficient increments. `exact/out/` holds their inputs, the certified coefficient enclosures of P_J (Section 3). |
| `toy/` | The polynomial model: Theorem PP₈₀ (`pp80/`), PT₂–PT₄ and PT₀ false (`pt/`), (AP+) and (B) (`ap/`), W false, W₂, W₃ (`w/`), (SMset) (`sm/`), (UM) (`um/`), far-node remainders (`ft/`), PP dominance, finite part (`pp/`). |
| `computed/` | Computed values that are **not** certificates (Section 9). |
| `tools/` | `logdiff.py`: compare logs up to dates and timings. |
| `runlog.sh` | Wrapper that writes a log with header and footer. |
| `SHA256SUMS` | SHA-256 of every shipped file except the logs and this README (`sha256sum -c SHA256SUMS`). |

## 3. Inputs from Paper I: the certified enclosures of P_J

P_J(u) = 1 + Σ_{k=1}^{2J} p_k u^k (u = t²) is the exact Hermite member: F̂_{Ξ²P_J(t²)} and its derivative vanish at the
first J prime powers. The files `exact/out/P{J}_ball.txt` (J = 10, 60, 61, 110, 111) contain Arb balls that contain the
exact coefficients p_0 = 1, p_1, …, p_{2J}. They are the certified outputs of `exact/verify_exact_member.py` in the
ancillary files of Paper I (certificate of (N) and (POS); same file names, byte-identical, SHA-256 in Section 7), and
are copied here as inputs. Every script below prints the SHA-256 of the enclosure it reads.

## 4. Certificates for the exact members (`exact/`)

- `exact/verify_roots.py` isolates the 2J roots of P_J (Arb `acb_poly.roots`, validated disjoint enclosures, one root
  each, valid for every polynomial in the coefficient balls) and prints rigorous bounds for min|Im t|, min|arg u|,
  min|u|, Σ1/|u|, the number of roots with Re u > 0, an interval containing |arg u| for all roots with Re u > 0
  (min rounded down, max rounded up; the list of their midpoints to 4 decimals is for orientation only), and
  sup_r N(r)/r, N(r) = #{j : |u_j| ≤ r²} (rounded up).
- `exact/verify_bf.py` certifies Lemma BF: F̂_{Ξ²P_J} > 0 for x ≥ x₀, by showing that the polynomial Q_P defined by
  \[P_J(−(θ+½)²)θ²(θ+1)²](e^{−y}) = Q_P(y)e^{−y} (θ = y d/dy) has positive leading coefficient and only positive Taylor
  coefficients at y₀ = 2πx₀ (hence no zero on [y₀, ∞)); since K₀ is a multiplicative convolution of e^{−y} that
  commutes with θ, this gives F̂ > 0 for 2πx ≥ y₀. x₀ is an exact decimal. A negative control at a slightly smaller x₀
  is printed.
- `exact/verify_base.py` certifies the base data (B): F̂_J ≥ θ·Ψ₁·min(1, d(x)²) on [ξ₂, ξ_X] and F̂_J″(ξ_n) > 0 at every
  prime power n ≤ X, where Ψ₁(ξ) = 2π√x W₀(2πx) is the N = 1 term of Ψ and d(x) = dist(x, PP). Since the exact
  member satisfies F̂_J(ξ_n) = F̂_J′(ξ_n) = 0 exactly, a node neighbourhood is certified by F̂_J(ξ_n+u) ≥ u²c₂′ against
  |x − n| ≤ n|u|(e^{2πh} − 1)/h; the gaps are covered by Taylor-model pieces against an upper bound for Ψ₁·min(1, d²).
  **Precondition check:** the vanishing c₀ = c₁ = 0 is used, not computed, so the input must be the enclosure of the
  exact member. As a consistency check the script requires, at every node, that the computed balls for F̂_J(ξ_n) and
  F̂_J′(ξ_n) contain 0 and are negligible against the quadratic term (radius ≤ 2^{−B/4} c₂h² resp. 2^{−B/4} c₂h at
  B bits); an enclosure of any other polynomial (for example with p₁ perturbed by 10⁻¹⁵) is rejected.
- `exact/verify_r1.py` certifies ratio bounds R₁(X) ≥ sup_{x∈[2,X]∖PP} |F̂_{J+1} − F̂_J| / (|Δp₁| F̂_J), with
  Δp₁ = p₁^{(J+1)} − p₁^{(J)}, from the enclosures of P_J and P_{J+1}. The difference D = F̂_{J+1} − F̂_J is the transform
  of Ξ²(P_{J+1} − P_J)(t²); D and F̂_J both vanish to second order at the common nodes, so node neighbourhoods are
  handled by the quadratic coefficients and the gaps by Taylor-model pieces (upper bound for |D|, lower bound for F̂_J).
  The same precondition check as in `verify_base.py` is applied to F̂_J and to D (scale |Δp₁|c₂ for D). Every node and
  piece bound is compared with its target, and the printed maximum is selected by exact comparison.
- `exact/verify_increments.py` certifies the sign of every coefficient increment p_k^{(J+1)} − p_k^{(J)} from the two
  certified enclosures (difference of balls), and prints the largest relative negative increment (rounded up).

## 5. The polynomial model (`toy/`)

In the model the kernel Ψ is replaced by e^{−y}; the nodes are y_j = 2πn_j (n_j the j-th prime power) or the symbolic
nodes y₁ < … < y_J, and the toy Hermite system, its solution P_J, the polynomial R_J and the chain cofactors are as
defined in the manuscript.
- `toy/pp80/verify_pp80_tau.py` (Theorem PP₈₀, direct route): Arb balls at 6000 bits in the τ basis
  τ_k = (−1)^k(θ − y)^{2k}1 (exact integer recursion); rigorous `arb_mat.solve` for the chain cofactors; checks (I0),
  (I1′) (in cross-multiplied form) and g(z_{K+1}) > 0 at every level K ≤ 160, and at every even K = 2J the toy
  system ((N)), p_{2J} > 0, strict TEL_J, positivity of the half-step cofactor and a consistency identity. The level
  range is split into two runs. The parameter file's node list is checked to be the initial segment of the prime powers.
- `toy/pp80/verify_pp80_chain.py` (Theorem PP₈₀, second route): the hypotheses of Theorem A by the Stirling-number
  (odd Mellin condition) chain systems at 4000 bits, at every level K ≤ 160.
- `toy/pt/verify_pt.py` (PT₂, PT₃, PT₄): exact arithmetic in ℤ[y₁, …, y_J] (FLINT `fmpz_mpoly`). The polynomials G_i
  are derived from the bordered Hermite determinant; the certificate checks (a) the defining odd Stirling conditions
  identically, (b) the determinant identity D = κ(y₁⋯y_J)²V⁴G₀ (V the Vandermonde product), and (c) on each piece of a
  cover of the region (slack coordinates, parameter file), that the piece lies in the region and that every G_i has only
  positive coefficients after the substitution. `toy/pt/verify_pt2_cramer.py` re-proves PT₂ by an independent Cramer
  computation. The large intermediate polynomials of PT₄ are regenerated (about 20 s), not shipped; each log prints a
  fingerprint. **Each PT₄ run needs about 1 GB of memory.**
- **The region cover is a hand proof.** The scripts check that every piece lies in the region ("piece ⊆ region", the
  `inside` lines of the logs), not that the pieces cover the region. That the pieces cover the region is proved by hand
  in the manuscript, in the subsection "The certificates for small J" (label `app:proofs-PT`), for PT₂, PT₃ and PT₄.
  `toy/pt/check_pt4_region.py` is a consistency check of the data of that argument for the part 4A + 3B + 2E < 48 of
  the PT₄ region (slack coordinates): the vertices of its projection Π<, the position of the apex and of the base
  triangles of the pieces II1–II6 of the pulling triangulation, and vol(Π<) = 1024/3 computed in two ways. It is not a
  proof of the cover; the part 4A + 3B + 2E ≥ 48 of PT₄ and the covers for PT₂ and PT₃ rest on the hand argument alone.
- `toy/ap/verify_ap.py` ((AP+) at δ = 1/20, J ≤ 90): exact rational arithmetic at y*_K = (21/20)(8K − 5):
  exact solve with residual check ((N)), p_{2J} > 0, exact division Q/A and positivity of every coefficient of R_J.
  `toy/ap/verify_halfstep.py` checks the half-step condition (B)_J at the same points, J ≤ 90.
- `toy/w/verify_w_cex.py` (W is false as stated): certified counterexamples in Arb (1500–7000 bits), items (a)–(f).
  `toy/w/verify_w_small.py` and `toy/w/verify_w_insertion.py` (W₂, W₃): exact certificates on both regions, by two
  routes (Cramer; insertion). The insertion route uses the insertion formulas of the manuscript (exact divisions that
  fail if inexact), so it is independent of PT_J but not of those formulas.
- `toy/sm/verify_smset.py` ((SMset)_k for every k ≤ 60 and every x > y_{k+1}), `toy/um/verify_um.py` ((UM) at
  J ∈ {2, 4, 8, 12, 20, 30, 40, 60}, both chain levels, together with a(y_{J+1}) > 0) and `toy/ft/verify_farbound.py`
  (explicit far-node remainders for the first 6, 10, 20 prime powers): Arb, coefficient-sign certificates of
  polynomials after substitution. `verify_farbound.py` drops the two top Taylor coefficients of YE after checking that
  their balls contain 0; their exact vanishing is a theorem of the manuscript.
- `toy/pp/verify_pp_prefix.py` (finite part of the proposition "PP dominates"): for every K ≤ 217000, exact integer
  comparisons (π bracketed by rationals checked in Arb) of (D) 2πn_K > (21/20)(8K − 5) and (S)
  2π(n₁ + … + n_K) ≥ 1.2366·K(4K − 1). `toy/pt/verify_pt0_false.py` (zero-slack PT is not sufficient): exact rational
  arithmetic at three points with PT₁, PT₂ strict and zero slack (δ = 0), printing the exact solution and the sign of
  each r_i.

## 6. Claims, scripts and expected output

Labels are the LaTeX labels of the statements in the manuscript. "Runtime" is the wall time recorded in the footer of
the shipped log (`W` = number of worker processes; otherwise one process). Every verifier prints the SHA-256 of each
input file it reads; the table abbreviates it, Section 7 lists it in full. "Expected output" quotes lines (or parts of
lines) of the shipped log verbatim.

### 6.1 The exact members (`exact/`)

| Claim (label) | Command (from the top directory) | Input (SHA-256, abbreviated) | Method; precision | Runtime | Expected output (verbatim) |
|---|---|---|---|---|---|
| Root geometry at J = 60 (`prop:roots`, certified root geometry) | `python exact/verify_roots.py exact/out/P60_ball.txt --prec 2000` | `exact/out/P60_ball.txt` (`fdfbfe57…db6cda4b`) | Arb root isolation (`acb_poly.roots`, validated), 2000 bits | < 1 s | `roots with Re u > 0: 6 (certified), Re u < 0: 114, undetermined: 0`; `\|arg u\| of the Re u > 0 roots: all in [1.0351074e0, 1.4522567e0] (rounded outward)`; `min \|Im t\| >= 9.6386206e0`; `sup_r N(r)/r <= 0.41658` |
| Root geometry at J = 110 (`prop:roots`, certified root geometry) | `python exact/verify_roots.py exact/out/P110_ball.txt --prec 2000` | `exact/out/P110_ball.txt` (`7c899956…f51c117a`) | Arb root isolation (`acb_poly.roots`, validated), 2000 bits | 4 s | `roots with Re u > 0: 6 (certified), Re u < 0: 214, undetermined: 0`; `\|arg u\| of the Re u > 0 roots: all in [1.0351421e0, 1.4522859e0] (rounded outward)`; `min \|Im t\| >= 9.6388900e0`; `sup_r N(r)/r <= 0.41623` |
| Root geometry at J = 111 (`prop:roots`, certified root geometry) | `python exact/verify_roots.py exact/out/P111_ball.txt --prec 2000` | `exact/out/P111_ball.txt` (`25669a32…f708b3f1`) | Arb root isolation (`acb_poly.roots`, validated), 2000 bits | 3 s | `roots with Re u > 0: 6 (certified), Re u < 0: 216, undetermined: 0`; `\|arg u\| of the Re u > 0 roots: all in [1.0351423e0, 1.4522861e0] (rounded outward)`; `min \|Im t\| >= 9.6388919e0`; `sup_r N(r)/r <= 0.41623` |
| Lemma BF instance: F̂₆₀ > 0 for x ≥ 199.39 (`prop:base`(a)) | `python exact/verify_bf.py exact/out/P60_ball.txt --x0 199.4 --x0 199.39 --control 199.35 --prec 4600` | `exact/out/P60_ball.txt` (`fdfbfe57…db6cda4b`) | Arb 4600 bits; Taylor shift of Q_P at 2πx₀ (x₀ = 199.4, 199.39; negative control 199.35) | < 1 s | `certified > 0: 245/245`; `CERTIFIED: Fhat > 0 for x >= 199.39 (J = 60): True` |
| Lemma BF instance: F̂₁₀ > 0 for x ≥ 16.45 (`prop:base`(a)) | `python exact/verify_bf.py exact/out/P10_ball.txt --x0 16.45 --control 16.44 --prec 1000` | `exact/out/P10_ball.txt` (`4e55d361…1bdc48d3`) | Arb 1000 bits (negative control 16.44) | < 1 s | `certified > 0: 45/45`; `CERTIFIED: Fhat > 0 for x >= 16.45 (J = 10): True` |
| (B) at J = 60 on [ξ₂, ξ₁₉₉], θ = 0.787979 (`prop:base`(b)) | `python exact/verify_base.py exact/out/P60_ball.txt --X 199 --theta 0.787979 --prec 1800 --workers 2` | `exact/out/P60_ball.txt` (`fdfbfe57…db6cda4b`) | Arb 1800 bits; Taylor order 28; node neighbourhoods and 59 gaps (adaptive bisection) | 170 s (W = 2) | `(ii) all 59 gaps certified: 6313 pieces`; `CERTIFIED: Fhat_J >= 0.787979 Psi_1 min(1, d^2) on [xi_2, xi_199] and Fhat_J'' > 0 at the nodes (J = 60): True` |
| (B) at J = 110 on [ξ₂, ξ₅₉], θ = 0.787979 (`prop:base`(b)) | `python exact/verify_base.py exact/out/P110_ball.txt --X 59 --theta 0.787979 --prec 3000 --workers 2` | `exact/out/P110_ball.txt` (`7c899956…f51c117a`) | Arb 3000 bits; Taylor order 28 | 151 s (W = 2) | `(ii) all 24 gaps certified: 484 pieces`; `CERTIFIED: Fhat_J >= 0.787979 Psi_1 min(1, d^2) on [xi_2, xi_59] and Fhat_J'' > 0 at the nodes (J = 110): True` |
| (B) at J = 10 on [ξ₂, ξ₁₆], θ = 0.786684 (`prop:base`(b)) | `python exact/verify_base.py exact/out/P10_ball.txt --X 16 --theta 0.786684 --prec 800 --workers 1` | `exact/out/P10_ball.txt` (`4e55d361…1bdc48d3`) | Arb 800 bits; Taylor order 28 | 8 s | `(ii) all 9 gaps certified: 142 pieces`; `CERTIFIED: Fhat_J >= 0.786684 Psi_1 min(1, d^2) on [xi_2, xi_16] and Fhat_J'' > 0 at the nodes (J = 10): True` |
| R₁(31) ≤ 1.021·10⁹ at J₁ = 60 (`prop:base`(c)); Δp₁ at J = 60 (`prop:increments`) | `python exact/verify_r1.py exact/out/P60_ball.txt exact/out/P61_ball.txt --target 31:1.021e9 --prec 1800 --workers 2` | `exact/out/P60_ball.txt` (`fdfbfe57…db6cda4b`)<br>`exact/out/P61_ball.txt` (`8cc7b2b9…91ca3dd4`) | Arb 1800 bits; Taylor order 28 | 74 s (W = 2) | `Delta p_1 = p_1^(J+1) - p_1^(J) in [2.08079540774023e-11 +/- 3.54e-26]`; `X =  31: certified sup bound on [2, X] <= 1.02023e9`; `CERTIFIED: R_1 bounds (J = 60): True` |
| R₁(31, 43, 47, 53, 59) ≤ 1.037, 2.701, 3.476, 4.844, 6.474 (·10⁹) at J₁ = 110 (`prop:base`(c)); Δp₁ at J = 110 (`prop:increments`) | `python exact/verify_r1.py exact/out/P110_ball.txt exact/out/P111_ball.txt --target 31:1.037e9 --target 43:2.701e9 --target 47:3.476e9 --target 53:4.844e9 --target 59:6.474e9 --prec 3000 --workers 2` | `exact/out/P110_ball.txt` (`7c899956…f51c117a`)<br>`exact/out/P111_ball.txt` (`25669a32…f708b3f1`) | Arb 3000 bits; Taylor order 28 | 444 s (W = 2) | `Delta p_1 = p_1^(J+1) - p_1^(J) in [2.91831836483267e-12 +/- 2.11e-27]`; `X =  59: certified sup bound on [2, X] <= 6.45773e9`; `CERTIFIED: R_1 bounds (J = 110): True` |
| Increment signs 60 → 61: negative exactly at k ∈ {2, 4, 6, 10, 11} (`prop:increments`) | `python exact/verify_increments.py exact/out/P60_ball.txt exact/out/P61_ball.txt --expect-negative 2,4,6,10,11` | `exact/out/P60_ball.txt` (`fdfbfe57…db6cda4b`)<br>`exact/out/P61_ball.txt` (`8cc7b2b9…91ca3dd4`) | Arb (differences of the certified balls) | < 1 s | `certified negative increments at k in [2, 4, 6, 10, 11]`; `<= 1.80e-6`; `CERTIFIED: increment sign pattern (J = 60 -> 61): True` |
| Increment signs 110 → 111: negative exactly at k ∈ {2, 4, 6, 10, 11} (`prop:increments`) | `python exact/verify_increments.py exact/out/P110_ball.txt exact/out/P111_ball.txt --expect-negative 2,4,6,10,11` | `exact/out/P110_ball.txt` (`7c899956…f51c117a`)<br>`exact/out/P111_ball.txt` (`25669a32…f708b3f1`) | Arb (differences of the certified balls) | < 1 s | `certified negative increments at k in [2, 4, 6, 10, 11]`; `<= 2.51e-7`; `CERTIFIED: increment sign pattern (J = 110 -> 111): True` |

### 6.2 The polynomial model (`toy/`)

| Claim (label) | Command (from the top directory) | Input (SHA-256, abbreviated) | Method; precision | Runtime | Expected output (verbatim) |
|---|---|---|---|---|---|
| Theorem PP₈₀, direct route, levels K ≤ 134 and 135 ≤ K ≤ 160 (`thm:PP80`) | `python toy/pp80/verify_pp80_tau.py toy/pp80/params/pp80.json 0 134`<br>`python toy/pp80/verify_pp80_tau.py toy/pp80/params/pp80.json 135 160` | `toy/pp80/params/pp80.json` (`9f840fb2…cc82f91c`) | Arb 6000 bits (τ basis, rigorous `arb_mat.solve`) | 266 s; 245 s | `ALL CERTIFIED: (I0), (I1'), (Y0) at every level K = 0..134; (N), p_2J > 0, TEL_J, half-step positivity, consistency for J = 1..67`; `ALL CERTIFIED: (I0), (I1'), (Y0) at every level K = 135..160; (N), p_2J > 0, TEL_J, half-step positivity, consistency for J = 68..80`; `min rel. LR increment >= 4.739370e-2` |
| Theorem PP₈₀, second route (hypotheses of Theorem A) (`thm:PP80`) | `python toy/pp80/verify_pp80_chain.py toy/pp80/params/pp80_chain.json` | `toy/pp80/params/pp80_chain.json` (`0fedf5dd…cc90f9ca`) | Arb 4000 bits (Stirling-number chain systems) | 462 s | `ALL CERTIFIED: (I0), (I1'), (Y0) at every level K = 0..160` |
| PT₂ (`thm:PT2`), two routes | `python toy/pt/verify_pt.py toy/pt/params/pt2.json`<br>`python toy/pt/verify_pt2_cramer.py` | `toy/pt/params/pt2.json` (`0db9256e…93e529f7`) | exact (ℤ[y₁, y₂]); Cramer route independent | < 1 s; < 1 s | `ALL CERTIFIED: J = 2, identities (a), (b) and positivity of G_0..G_4 on pieces I,II`; `ALL CERTIFIED: Theorem PT2` |
| PT₃ (`thm:PT3`) | `python toy/pt/verify_pt.py toy/pt/params/pt3.json` | `toy/pt/params/pt3.json` (`2f55a0f3…fbc63813`) | exact (ℤ[y₁, y₂, y₃]) | 3 s | `ALL CERTIFIED: J = 3, identities (a), (b) and positivity of G_0..G_6 on pieces PA,PAp,PB1,PB2` |
| PT₄ (`thm:PT4`): determinant identity, 8 admissibility identities, 11 pieces (two runs); geometry of the cover | `python toy/pt/verify_pt.py toy/pt/params/pt4.json Ia1,Iap,Ia3,Ib1,Ib2`<br>`python toy/pt/verify_pt.py toy/pt/params/pt4.json II1,II2,II3,II4,II5,II6`<br>`python toy/pt/check_pt4_region.py toy/pt/params/pt4.json` | `toy/pt/params/pt4.json` (`03bb73e2…f9cb2cb6`) | exact (ℤ[y₁, …, y₄]); about 1 GB of memory per run | 1152 s; 1194 s; < 1 s | `ALL CERTIFIED: J = 4, identities (a), (b) and positivity of G_0..G_8 on pieces Ia1,Iap,Ia3,Ib1,Ib2`; `ALL CERTIFIED: J = 4, identities (a), (b) and positivity of G_0..G_8 on pieces II1,II2,II3,II4,II5,II6`; `ALL CHECKS PASSED` |
| Zero-slack PT is not sufficient (`rem:PT0-false`) | `python toy/pt/verify_pt0_false.py toy/pt/params/pt0_false.json` | `toy/pt/params/pt0_false.json` (`13590e18…2065d5e4`) | exact (ℚ) | < 1 s | `ALL CERTIFIED: at every point PT_1 and PT_2 hold (zero slack), (N) holds and r_1 < 0` |
| (AP+) at δ = 1/20 with (N) and p_{2J} > 0, J ≤ 90 (`prop:AP-B-cert`) | `python toy/ap/verify_ap.py toy/ap/params/ap_delta005.json 1 80`<br>`python toy/ap/verify_ap.py toy/ap/params/ap_delta005.json 81 90` | `toy/ap/params/ap_delta005.json` (`8154e4dd…d4175235`) | exact (ℚ) | 346 s; 290 s | `ALL CERTIFIED: (N), p_2J > 0 and (AP+)_J at delta = 1/20 for J = 1..80`; `ALL CERTIFIED: (N), p_2J > 0 and (AP+)_J at delta = 1/20 for J = 81..90` |
| Half-step condition (B)_J at δ = 1/20, J ≤ 90 (`prop:AP-B-cert`) | `python toy/ap/verify_halfstep.py toy/ap/params/ap_delta005.json 1 90` | `toy/ap/params/ap_delta005.json` (`8154e4dd…d4175235`) | exact (ℚ) | 665 s | `ALL CERTIFIED: (B)_J (half-step cofactor T_J > 0, T_J(y*_J) > 0) at delta = 1/20 for J = 1..90` |
| W is false as stated: certified counterexamples (a)–(f) (`prop:W-false`) | `python toy/w/verify_w_cex.py toy/w/params/w_cex.json` | `toy/w/params/w_cex.json` (`fd2f0f47…6f0e4cef`) | Arb 1500–7000 bits | 6 s | `ALL CERTIFIED: items a,b,c,d,e,f` |
| W₂ (`thm:W-J2`), Cramer and insertion routes | `python toy/w/verify_w_small.py toy/w/params/w_small.json 2`<br>`python toy/w/verify_w_insertion.py toy/w/params/w_small.json 2` | `toy/w/params/w_small.json` (`3bd43f98…dd3b7a77`) | exact | < 1 s; < 1 s | `ALL CERTIFIED: Theorem W2 on regions a,b`; `ALL CERTIFIED: Theorem W2 on regions a,b (insertion route)` |
| W₃ (`thm:W-J3`), Cramer and insertion routes | `python toy/w/verify_w_small.py toy/w/params/w_small.json 3`<br>`python toy/w/verify_w_insertion.py toy/w/params/w_small.json 3` | `toy/w/params/w_small.json` (`3bd43f98…dd3b7a77`) | exact | < 1 s; 5 s | `ALL CERTIFIED: Theorem W3 on regions a,b`; `ALL CERTIFIED: Theorem W3 on regions a,b (insertion route)` |
| (SMset)_k for every k ≤ 60 and every x > y_{k+1} (`prop:SMset-cert`) | `python toy/sm/verify_smset.py toy/sm/params/smset.json` | `toy/sm/params/smset.json` (`fbe8d8f9…9763f15b`) | Arb 2000–4000 bits | 120 s | `ALL CERTIFIED: (SMset)_k with (N) for every x > y_{k+1}, k = 1..60` |
| (UM) at J ∈ {2, 4, 8, 12, 20, 30, 40, 60}, both chain levels (`prop:UM-cert`) | `python toy/um/verify_um.py toy/um/params/um.json` | `toy/um/params/um.json` (`cf1301db…cb934b3f`) | Arb 6000 bits | 38 s | `ALL CERTIFIED: (UM+) and a(y_{J+1}) > 0 at both chain levels for J = 2,4,8,12,20,30,40,60` |
| Far-node remainders for the first 6, 10, 20 prime powers (`prop:Fremainder`) | `python toy/ft/verify_farbound.py toy/ft/params/farbound.json` | `toy/ft/params/farbound.json` (`d69ae78e…0173b250`) | Arb | < 1 s | `ALL CERTIFIED` |
| (D) and (S) for every K ≤ 217000 (finite part of `prop:PP-dominates`) | `python toy/pp/verify_pp_prefix.py toy/pp/params/pp_prefix.json` | `toy/pp/params/pp_prefix.json` (`d528987a…ba9d7abd`) | exact (ℤ; π bracketed by rationals checked in Arb) | < 1 s | `ALL CERTIFIED: (D) and (S) for K = 1..217000` |

## 7. Input and data files with SHA-256

| File | Content | SHA-256 |
|---|---|---|
| `exact/out/P10_ball.txt` | certified enclosure of P_J (input; output of `exact/verify_exact_member.py` of Paper I, identical file) | `4e55d361d6d2c05f15565bd3c94d56b9f5e0715acecda9fd362410181bdc48d3` |
| `exact/out/P110_ball.txt` | certified enclosure of P_J (input; output of `exact/verify_exact_member.py` of Paper I, identical file) | `7c8999567bc77cd1c6fb5a9e816bb0b4f212b971f26dd0f3bda3237ff51c117a` |
| `exact/out/P111_ball.txt` | certified enclosure of P_J (input; output of `exact/verify_exact_member.py` of Paper I, identical file) | `25669a321f71ddef789247cd0adc0fd129c5d70f293e488bc4dab8c3f708b3f1` |
| `exact/out/P60_ball.txt` | certified enclosure of P_J (input; output of `exact/verify_exact_member.py` of Paper I, identical file) | `fdfbfe57bfe9945f640291b6f1e1b7e74e4d5afb04278961d5737f26db6cda4b` |
| `exact/out/P61_ball.txt` | certified enclosure of P_J (input; output of `exact/verify_exact_member.py` of Paper I, identical file) | `8cc7b2b9a66f643e8e40d84fd4ffd6970401342aeab87b716ec169bc91ca3dd4` |
| `toy/ap/params/ap_delta005.json` | toy-model parameter file | `8154e4dd3a63096e6626be846752083bde36b5c5c26267db59506145d4175235` |
| `toy/ft/params/farbound.json` | toy-model parameter file | `d69ae78eb3dbc3726400577e4bca33daadb45e99e7e97a92ae5479190173b250` |
| `toy/pp/params/pp_prefix.json` | toy-model parameter file | `d528987a839b8f6a12b7015db9ee00be9c422123ae835ca1fc1a87d4ba9d7abd` |
| `toy/pp80/params/pp80.json` | toy-model parameter file | `9f840fb2e65142ddf7bd47f33f2e95be51ac05dc42a03ef93fea5401cc82f91c` |
| `toy/pp80/params/pp80_chain.json` | toy-model parameter file | `0fedf5dd3f57bd2335abc6678b9451ace7cab7de6fb8e8943dc9dd3bcc90f9ca` |
| `toy/pt/params/pt0_false.json` | toy-model parameter file | `13590e181604c187d680d8179d4c51fe778516b508f2febd661b7c932065d5e4` |
| `toy/pt/params/pt2.json` | toy-model parameter file | `0db9256e86d5345238649f9544948bb06a39eed7c982391d9e0d146893e529f7` |
| `toy/pt/params/pt3.json` | toy-model parameter file | `2f55a0f3f7792042c1410fd58f36c2cbe5c303fb473ff366ec3b0d28fbc63813` |
| `toy/pt/params/pt4.json` | toy-model parameter file | `03bb73e2e7baab96bb2ccd5a9365a93c7cfdaa323bbb9588e2615a2df9cb2cb6` |
| `toy/sm/params/smset.json` | toy-model parameter file | `fbe8d8f92cc6f7de98425f34cf87ec62739de75b86c6069eeef0131d9763f15b` |
| `toy/um/params/um.json` | toy-model parameter file | `cf1301db32216348c06325299cbc31a7f0608e44af3104b1456166a9cb934b3f` |
| `toy/w/params/w_cex.json` | toy-model parameter file | `fd2f0f47437d346ee09f11b71d7e4e4030cc8b8f0e368305592900776f0e4cef` |
| `toy/w/params/w_small.json` | toy-model parameter file | `3bd43f9891a42840b64dee0ce993a5b30aed2e4c0e2a0fb90692204edd3b7a77` |
| `computed/family_J1_110.tsv` | computed table (**not** a certificate; Section 9) | `1242067a7e239ce779f12742e027bc32b3cd0cbd6282dc746df5da8b9b234750` |

## 8. Re-running and comparing with the shipped logs

From this directory, with `PY` set to a Python that has python-flint 0.9.0 and mpmath 1.3.0:

```sh
export PY=python3
exact/run_all.sh        # root geometry, Lemma BF, (B), R₁, increment signs (28.3 CPU-minutes)
toy/run_all.sh          # PP₈₀, PT₂–PT₄, (AP+), (B), W, (SMset), (UM), remainders, PP prefix, PT₀ (79.9 CPU-minutes)
sha256sum -c SHA256SUMS # inputs unchanged
```

Each `run_all.sh` overwrites the logs in its `logs/` directory and stops at the first run that does not certify
(`set -e`). Run them on a copy of this directory and compare with the shipped logs:

```sh
cp -r anc anc-rerun && cd anc-rerun && export PY=python3 && exact/run_all.sh && toy/run_all.sh
python tools/logdiff.py ../anc .     # every log: IDENTICAL (dates, system line and timings are ignored)
```

`exact/run_all.sh [W]` uses W = 2 worker processes by default, as in the shipped logs (one process for the J = 10 base
data). A single certificate is re-run with the command recorded in the first line of its log. The working precision
and the number of workers affect only the running time, the width of the enclosures and the header line of the log,
not the validity of a successful run.

## 9. What is computed but not certified

The following numbers appear in the manuscript only as numerical observations. No theorem depends on them.

- **The family P_J for J ≤ 110** (`computed/family_J1_110.tsv`, a copy of the table shipped with Paper I): for each
  J = 1, …, 110, the coefficient p₁, the top coefficient p_{2J}, the indices of non-positive coefficients,
  a_J = max_{1≤k≤2J}((2k)!|p_k|)^{1/(2k)}, the number of roots u with Re u > 0, min|Im t| and min|arg u|. The polynomials are
  floating-point solutions of the Hermite system at 4600 bits (not interval-certified); the roots were isolated by Arb
  on these midpoint polynomials. Only J = 10, 60, 61, 110, 111 are certified (Section 3). The research scripts that
  produced this table depend on machine-specific paths and intermediate data and are not shipped; its SHA-256
  authenticates the file, not the computation. No certificate depends on it.
- **The tail sum B₁₁₀ = 1.867·10⁻¹⁰** (and B₆₀ = 6.7196·10⁻¹⁰) of the tail reduction: the sum over the prime powers
  n ≥ 479 of the one-node increments of the fixed system at J₁ = 110. The terms with n ≤ 20000 (2218 points, about
  98.7% of the sum) were evaluated twice, by independent high-precision floating-point codes that agree to within
  5·10⁻¹⁵ per point; the remainder n > 20000 was estimated by assuming that a normalised ratio does not exceed its
  value at n = 20000, which is not proved. No script is shipped (the computation uses large tables of high-precision
  moments).

## 10. Numerical traps

1. Midpoints returned by polynomial root finders must be validated (disjoint isolating balls) before roots are counted.
2. Ball radii explode in cancelling recurrences; run them on midpoints and bound the error separately (or use an exact
   integer recursion, as for the τ basis of the model).
3. Constructing a ball from a decimal midpoint may round the midpoint to double precision; read decimals as exact
   rationals.
4. Suprema and infima read off a grid are not bounds; certified bounds on intervals need Taylor models, interval
   subdivision with remainder bounds, or coefficient-sign certificates after a substitution.
5. Crude Taylor remainders blow up at large x, because P_J(−z²) is an alternating sum when all p_k > 0; the Taylor
   order must grow with x.
6. Arb's built-in Bessel and confluent hypergeometric functions lose about 2z/log 2 bits at moderate z; no certificate
   uses them (`lib/besselk.py`).
7. A node list must be checked to be what the statement says (the initial segment of the prime powers); with the
   primes instead of the prime powers the model certificates fail at K = 13 ((I1′)) and K = 25 ((I0)).
8. Certificates must record the exact parameters they certify (here by SHA-256), so that the certified object is
   unambiguous.

## 11. Software and hardware

- Python 3.10.12; python-flint 0.9.0 (built on FLINT 3.6.0, which contains Arb); mpmath 1.3.0. The header of every
  log records the versions actually used.
- The scripts are deterministic: a re-run with the same versions reproduces each log except for the date, the system
  line and the timings (checked with `tools/logdiff.py`).
- Runtimes are wall times on an Intel Xeon Platinum 8362 (2.8 GHz) shared with other jobs (one core per worker).
  Peak memory is about 1 GB for each PT₄ run and at most a few hundred MB otherwise.

## 12. Licence

Licence: Apache License 2.0 (see LICENSE at the repository root). Copyright 2026 Nic Johns.
