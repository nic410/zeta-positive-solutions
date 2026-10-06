# Ancillary files: certified computations of the note on critical conductors

This directory contains every computer-assisted certificate used in the note on critical conductors (the slack of
other Γ-data, the critical conductors of Γ_ℝ² and Γ_ℂ, the pole-weight pins and the certified pair for the ℚ(i)
data): the exact parameter files, standalone verification scripts, and logs of fresh runs. Each statement that rests on
a computation is listed in Section 4 with its script, its exact input file (with SHA-256), the method and precision, the
runtime and the expected output. The directory is self-contained. Some certificates (the K = 128 bound and the Γ_ℝ²
and Γ_ℂ brackets with the two quadratic fields) are also shipped, as identical files, with the ancillary files of
Paper I.

## 1. Requirements and conventions

- Python ≥ 3.10 with **python-flint 0.9.0** (FLINT/Arb ball arithmetic) and **mpmath 1.3.0** (only the log header
  queries its version). Nothing else is needed: `pip install python-flint==0.9.0 mpmath==1.3.0`.
- Run every command from this directory (the top directory of the ancillary files).
- `./runlog.sh LOGFILE "$PY" SCRIPT ARGS` (after `export PY=python3`) runs one verifier and writes a log with a header
  (command, UTC date, system, software versions) and a footer (exit code, wall time). Every log shipped here was
  produced this way, in a fresh run of the shipped script on the shipped inputs.
- **Arithmetic.** "Exact" means rational arithmetic (FLINT `fmpq`, polynomials over ℚ); "Arb" means rigorous ball
  arithmetic at the stated working precision; every quantity printed as a ball `[m +/- r]` contains the exact value.
- **Explicit checks.** Every precondition and every check is an explicit test that raises an exception or prints
  `FAILED` and exits with a non-zero code; no certificate relies on `assert` (so `python -O` disables nothing).
- **Pole weight.** The parameter `pole_residue` is the pole weight r of the note (the residue of −L′/L at s = 1).
  The JSON key and the log lines keep the name `pole_residue`/`pole residue`.
- **Exact inputs.** The coefficients a_k, the scale s, the repair size ε, the Γ-shifts, the conductors and all claimed
  bounds are decimal strings read as exact rationals. The parameters of the Herglotz pairs (`general/params/pair_*.json`)
  are binary64 numbers that *define* the pair and are used exactly (each file says so in its `definition` field); the
  log-conductor of a pair is an exact decimal string or `log(N)`.
- **Rounding.** Every printed bound is rounded outward (upper bounds up, lower bounds down) with an exact a-posteriori
  check of the direction (`check_decimal` in `lib/common.py`), never
  through binary64.
- `tools/logdiff.py` compares a re-run log with the shipped one after removing dates, the system line and timings.

## 2. Layout

| Path | Contents |
|---|---|
| `general/verify_general.py` | Dual certificates: Gaussian–Laguerre functions in the cone, 𝒜 by one rigorous integral, read-off of κ*, q_min and pole-weight pins. |
| `general/verify_pair.py` | Primal certificates: explicit admissible pairs of Herglotz form. |
| `general/corollary_slack.py` | Combines a dual and a primal certificate into the conductor bracket and the slack interval of a quadratic field. |
| `general/params/`, `general/results/`, `general/logs/` | Parameter files; machine-readable summaries written by the runs (read by the corollaries); logs. |
| `lib/` | Shared library (a copy of the library of the ancillary files of Paper I); the scripts here use `lib/common.py` (explicit checks, exact check of every printed decimal). |
| `tools/` | `logdiff.py`: compare logs up to dates and timings. |
| `runlog.sh`, `SHA256SUMS` | Log wrapper; SHA-256 of every shipped file except the logs and this README. |

## 3. Method

Test functions F(t) = Σ_{k≤K} a_k f_k(t/s), f_k(u) = L_k^{(−1/2)}(2πu²)e^{−πu²}, plus a positive two-Gaussian repair
term of size ε. Then F = e^{−X/2}P(X) and F̂ = s·e^{−Y/2}Q(Y) with X = 2πt²/s², Y = 2πs²ξ² and P, Q polynomials over ℚ
(`general/verify_general.py`).
- Positivity is **exact**: Sturm sequences over ℚ show that P has no root in (0, ∞) (so F > 0 on ℝ), and that Q has no
  root in (0, ∞) (F̂ > 0 on ℝ: the Odlyzko–Poitou–Serre cone) or no root in (Y_lo, ∞) with Y_lo a rational just below
  the gap edge (F̂ > 0 on [ξ₂, ∞)).
- The archimedean functional 𝒜 of the given Γ-data (r·2F(i/2) + (1/2π)∫F[Σ_j(Re ψ(·) − log π) + log N]dt) is one
  rigorous Arb integral (`acb.integral`) of F_rep against the digamma weight plus a rigorous tail; F̂_rep(0) is exact.
  The printed bounds (κ*, q_min, pole weight) follow by exact arithmetic on these balls and are rounded outward. The
  pole-weight pin uses 𝒜_r = 𝒜 + (r − 1)D with D = 2F_rep(i/2).
- The tail t > T uses |Re ψ(w_j + it/2)| ≤ t for t ≥ T, with w_j = (½ + κ_j)/2. Proof: for w > 0 and τ > 0, the
  partial fractions give Re ψ(w + iτ) = lim_N (log N − Σ_{n<N} f(n)) with f(x) = (x + w)/((x + w)² + τ²), whose total
  variation on [0, ∞) is at most 1/τ; hence |Re ψ(w + iτ) − log√(w² + τ²)| ≤ 1/τ. With τ = t/2, t ≥ 10 and
  w_j² ≤ 75 ≤ 3t²/4 this gives 0 < Re ψ(w_j + it/2) ≤ log t + 2/t ≤ t. The script therefore requires T ≥ 10 and every
  Γ-shift in the domain 0 ≤ κ_j, (½ + κ_j)² ≤ 300 (exact check; the shipped shifts are 0 and 1). `verify_pair.py`
  requires every shift κ_j ≥ 0, so that the digamma arguments are positive reals and its tail majorant is monotone.
- `general/verify_pair.py` certifies an explicit admissible pair for given Γ-data and conductor q: ν̃ ≥ 0 (cells, bumps
  and tails, support in [2, ∞), every tail exponent m > ½), and μ > 0 on [0, T] by mean-value steps (μ′ enclosed on
  each whole step; the floor is the exact minimum of the lower endpoints) plus monotone majorants beyond T. An
  admissible pair at q gives q_min ≤ q. The script also prints a rigorous lower bound x0 for the start of supp ν̃, and
  with `--gap-x N` checks x0 ≥ N, so that the pair is admissible for the data with the gap ξ_N. The shipped runs check
  the natural gaps ξ₄ (Γ_ℝ² pair; ℚ(√5), whose smallest norm is 4) and ξ₃ (Γ_ℂ pair; ℚ(√−3), smallest norm 3); for the
  ℚ(i) pair (smallest norm 2) only x0 is reported.
- `general/corollary_slack.py` reads the summaries of one dual and one primal certificate (checking that each belongs
  to the current parameter file by SHA-256 and is certified) and prints, for a field of conductor q_F,
  (log q_F − log q₀)/2π + inf μ ≤ κ* ≤ κ*₀ + (log q_F)/2π. Both dual functions are in the OPS cone, so these bounds hold
  for every gap g with e^{2πg} ≤ x0; with `--gap-x N` this is checked at the field's natural gap ξ_N.

## 4. Claims, scripts and expected output

Labels are the LaTeX labels of the statements in the note. "Runtime" is the wall time recorded in the footer of the
shipped log (one process). The table abbreviates the SHA-256 of each input; Section 5 lists it in full.
"Expected output" quotes lines (or parts of lines) of the shipped log verbatim.

| Claim (label) | Command (from the top directory) | Input (SHA-256, abbreviated) | Method; precision | Runtime | Expected output (verbatim) |
|---|---|---|---|---|---|
| Left pole-weight pin: no admissible pair for r < 1 − A/D, A/D ≤ 5.5793·10⁻⁴⁰ (`thm:polepin`); κ*_OPS ≤ 9.9462·10⁻⁴¹ (`thm:notcritical`, a result of Paper I) | `python general/verify_general.py general/params/zeta_K128_s13.json` | `general/params/zeta_K128_s13.json` (`0976a671…879a4df2`) | exact Sturm sequences over ℚ (K = 128, s = 13, ε = 10⁻⁵⁶); Arb integral on [0, 220] at 512 bits | 448 s | `kappa*_OPS (and kappa*) of the data <= 9.9461827001452550725e-41`; `A/D <= 5.57930810147e-40`; `RESULT         : CERTIFIED` |
| κ*_OPS ≤ 7.24651·10⁻³² with K = 104 and the weaker left pin r < 1 − 4.0649249·10⁻³¹ (remark after `thm:polepin`) | `python general/verify_general.py general/params/zeta_K104_s13.json` | `general/params/zeta_K104_s13.json` (`737928c4…cdc1adde`) | exact Sturm (K = 104, s = 13); Arb integral on [0, 200] at 448 bits | 224 s | `kappa*_OPS (and kappa*) of the data <= 7.2465050671573871983e-32`; `A/D <= 4.06492480958e-31`; `RESULT         : CERTIFIED` |
| Right pole-weight pin: no admissible pair for r > 1 + 7.8550942·10⁻²¹ (`thm:polepin`) | `python general/verify_general.py general/params/zeta_K80_s12_edge.json` | `general/params/zeta_K80_s12_edge.json` (`9c70ac79…87e8b6ce`) | exact Sturm on (Y_lo, ∞) (K = 80, s = 12, gap edge ξ₂); Arb integral at 448 bits | 165 s | `A/\|D\| <= 7.85509419726e-21`; `RESULT         : CERTIFIED` |
| Γ_ℝ², one pole: q_min ≥ 4.98485094226764 (`thm:GR2`) | `python general/verify_general.py general/params/gammaR2_K80_s7.json` | `general/params/gammaR2_K80_s7.json` (`79936770…026a71ee`) | exact Sturm (K = 80, s = 7); Arb integral on [0, 120] at 448 bits | 167 s | `kappa*_OPS (and kappa*) of the data <= -0.25566705789831547610`; `q_min >= 4.9848509422676437635`; `RESULT         : CERTIFIED` |
| Γ_ℝ², one pole: q_min ≤ 4.9994844, by a pair whose prime measure lives on [ξ₄, ∞) (`thm:GR2`; the gap ξ₄ in `cor:natural-gaps`) | `python general/verify_pair.py general/params/pair_gammaR2_X240.json --gap-x 4` | `general/params/pair_gammaR2_X240.json` (`3b9f85c8…2b7dfb1d`) | Arb 128 bits; 17 214 mean-value steps on [0, 800] and monotone majorants beyond | 37 s | `nu~ support    : supp nu~ in [x0, oo) with x0 >= 4.049150`; `MU FLOOR       : mu(t) >= 6.59497e-9 for all real t`; `hence q_min(data) <= 4.9994844`; `GAP            : admissible at gap xi_4 (prime measure on [4, oo)): True`; `RESULT         : CERTIFIED` |
| κ*(ℚ(√5) data) ∈ [1.64·10⁻⁵, 4.83·10⁻⁴] (`thm:notcritical`, a result of Paper I); the bracket and this interval at the natural gap ξ₄ (`cor:natural-gaps`) | `python general/corollary_slack.py general/params/corollary_qsqrt5.json --gap-x 4` | `general/params/corollary_qsqrt5.json` (`540d1ad6…4b4afbab`)<br>`general/results/gammaR2_K80_s7.json` (`04a2de0c…fcca2e8b`)<br>`general/results/pair_gammaR2_X240.json` (`d76c8c61…5b7cd129`) | exact and Arb arithmetic on the two certified summaries (their parameter hashes are checked) | < 1 s | `SLACK      : 1.6420748e-5 <= kappa*(Q(sqrt 5)) <= 0.00048294147`; `CLAIM      : the bracket and the slack interval hold at the natural gap xi_4 of Q(sqrt 5) (4 <= x0) ... implied`; `RESULT     : CERTIFIED` |
| Γ_ℂ, one pole: q_min ≥ 2.981236704765 (`prop:GC`) | `python general/verify_general.py general/params/gammaC_K64_s9.json` | `general/params/gammaC_K64_s9.json` (`e330d8b7…c296021a`) | exact Sturm (K = 64, s = 9); Arb integral on [0, 160] at 448 bits | 187 s | `q_min >= 2.9812367047650810559`; `RESULT         : CERTIFIED` |
| Γ_ℂ, one pole: q_min ≤ 2.997174, by a pair whose prime measure lives on [ξ₃, ∞) (`prop:GC`; the gap ξ₃ in `cor:natural-gaps`) | `python general/verify_pair.py general/params/pair_gammaC_X40.json --gap-x 3` | `general/params/pair_gammaC_X40.json` (`f32152ae…2828eeae`) | Arb 128 bits; 9501 mean-value steps on [0, 800] and monotone majorants beyond | 19 s | `nu~ support    : supp nu~ in [x0, oo) with x0 >= 3.011664`; `MU FLOOR       : mu(t) >= 6.67226e-8 for all real t`; `hence q_min(data) <= 2.9971739`; `GAP            : admissible at gap xi_3 (prime measure on [3, oo)): True`; `RESULT         : CERTIFIED` |
| κ*(ℚ(√−3) data) ∈ [1.5·10⁻⁴, 9.99·10⁻⁴] (`thm:notcritical`, a result of Paper I); the bracket and this interval at the natural gap ξ₃ (`cor:natural-gaps`) | `python general/corollary_slack.py general/params/corollary_qsqrtm3.json --gap-x 3` | `general/params/corollary_qsqrtm3.json` (`c0011615…6a7fd822`)<br>`general/results/gammaC_K64_s9.json` (`b51249bf…256def9f`)<br>`general/results/pair_gammaC_X40.json` (`83c8d09d…989672fb`) | exact and Arb arithmetic on the two certified summaries (hashes checked) | < 1 s | `SLACK      : 0.00015006672 <= kappa*(Q(sqrt -3)) <= 0.00099854968`; `CLAIM      : the bracket and the slack interval hold at the natural gap xi_3 of Q(sqrt -3) (3 <= x0) ... implied`; `RESULT     : CERTIFIED` |
| Admissible pair for the ℚ(i) data at conductor 4 (`prop:Qi`) | `python general/verify_pair.py general/params/pair_Qi_X10.json` | `general/params/pair_Qi_X10.json` (`7ba4907b…a7932cb4`) | Arb 128 bits; 1277 mean-value steps on [0, 300] and monotone majorants beyond | 2 s | `nu~ support    : supp nu~ in [x0, oo) with x0 >= 3.088530`; `MU FLOOR       : mu(t) >= 0.0222324 for all real t`; `RESULT         : CERTIFIED` |

## 5. Input and data files with SHA-256

| File | Content | SHA-256 |
|---|---|---|
| `general/params/corollary_qsqrt5.json` | parameter file (Gaussian–Laguerre function, Herglotz pair or corollary data) | `540d1ad652df9feff6916301136f1a5c9656cb9eed46d745f1dda3674b4afbab` |
| `general/params/corollary_qsqrtm3.json` | parameter file (Gaussian–Laguerre function, Herglotz pair or corollary data) | `c0011615f1a31599b4217b3c48b3718192c8b26a092faa34aea3058a6a7fd822` |
| `general/params/gammaC_K64_s9.json` | parameter file (Gaussian–Laguerre function, Herglotz pair or corollary data) | `e330d8b743bd835920ecaad507a195773f4c858181d97bafb9d3eca1c296021a` |
| `general/params/gammaR2_K80_s7.json` | parameter file (Gaussian–Laguerre function, Herglotz pair or corollary data) | `79936770a00991a3c4b24ac614f8405686fdf499d6eb0040dd9976ae026a71ee` |
| `general/params/pair_Qi_X10.json` | parameter file (Gaussian–Laguerre function, Herglotz pair or corollary data) | `7ba4907baabea3199c95440a7f2e98d707fd4be6c4c934cf3045a2bca7932cb4` |
| `general/params/pair_gammaC_X40.json` | parameter file (Gaussian–Laguerre function, Herglotz pair or corollary data) | `f32152ae73a8e202fafd9bd56097dc0b98d68741392ee8149ee3d9262828eeae` |
| `general/params/pair_gammaR2_X240.json` | parameter file (Gaussian–Laguerre function, Herglotz pair or corollary data) | `3b9f85c84efcf36f0e753e01edd442bfc3d6a1a2ead2377124b015ea2b7dfb1d` |
| `general/params/zeta_K104_s13.json` | parameter file (Gaussian–Laguerre function, Herglotz pair or corollary data) | `737928c4912bc81b352fb163eef1b4171903e5c470f80a79a96bab08cdc1adde` |
| `general/params/zeta_K128_s13.json` | parameter file (Gaussian–Laguerre function, Herglotz pair or corollary data) | `0976a6711193adc0f02a532931974b8ef4912337f79e39f59aa21445879a4df2` |
| `general/params/zeta_K80_s12_edge.json` | parameter file (Gaussian–Laguerre function, Herglotz pair or corollary data) | `9c70ac7938e9d63c54437233bc22f2283fb44f9c2060c542c2005a4187e8b6ce` |
| `general/results/gammaC_K64_s9.json` | certificate summary (output of the run of the same name; input of the corollaries) | `b51249bf71c6fdc858bd5511909830210018a8ec192dceef8362a1a8256def9f` |
| `general/results/gammaR2_K80_s7.json` | certificate summary (output of the run of the same name; input of the corollaries) | `04a2de0c6141cc0a8ec66ce4a00b6595acb93e76a1d25e1e45ace87afcca2e8b` |
| `general/results/pair_Qi_X10.json` | certificate summary (output of the run of the same name; input of the corollaries) | `f20b8c78fa62cb9e163b6d0bcb7454d663245486271e33147b69e0d91e261672` |
| `general/results/pair_gammaC_X40.json` | certificate summary (output of the run of the same name; input of the corollaries) | `83c8d09df002c1c4f40aaf65f3b9b4f0088ec58f53619fb282bdc290989672fb` |
| `general/results/pair_gammaR2_X240.json` | certificate summary (output of the run of the same name; input of the corollaries) | `d76c8c61ccedabaa795334a7bf9c0b321d51d1f3acec9259586083745b7cd129` |
| `general/results/zeta_K104_s13.json` | certificate summary (output of the run of the same name; input of the corollaries) | `dd94bcf4b460f20d224689b07fdf3ff89cd0f92b55d5ab0e4371e93fd030a2e9` |
| `general/results/zeta_K128_s13.json` | certificate summary (output of the run of the same name; input of the corollaries) | `1d99cf539e9a3f00f0d40c0d686f1cb2cb3f61fd5fbf6a6bd549d533e5aec631` |
| `general/results/zeta_K80_s12_edge.json` | certificate summary (output of the run of the same name; input of the corollaries) | `f877dc3381038ef0283127a3bcfdb08bfc52236e7adf6b903a1b48e7646f9259` |

## 6. Re-running and comparing with the shipped logs

From this directory, with `PY` set to a Python that has python-flint 0.9.0 and mpmath 1.3.0:

```sh
export PY=python3
general/run_all.sh      # all certificates of this directory, one process at a time (20.8 CPU-minutes)
sha256sum -c SHA256SUMS # inputs and the regenerated summaries unchanged
```

`general/run_all.sh` overwrites the logs in `general/logs/` and the summaries in `general/results/`, and stops at the
first run that does not certify (`set -e`). Run it on a copy of this directory and compare with the shipped logs:

```sh
cp -r anc anc-rerun && cd anc-rerun && export PY=python3 && general/run_all.sh
python tools/logdiff.py ../anc .     # every log: IDENTICAL (dates, system line and timings are ignored)
sha256sum -c SHA256SUMS              # regenerated summaries are byte-identical
```

## 7. Software and hardware

- Python 3.10.12; python-flint 0.9.0 (built on FLINT 3.6.0, which contains Arb); mpmath 1.3.0. The header of every
  log records the versions actually used.
- The scripts are deterministic: a re-run with the same versions reproduces each log except for the date, the system
  line and the timings.
- Runtimes are wall times on an Intel Xeon Platinum 8362 (2.8 GHz) shared with other jobs.

## 8. Licence

Licence: Apache License 2.0 (see LICENSE at the repository root). Copyright 2026 Nic Johns.
