# Positive solutions of the explicit formula for ζ(s): near-criticality and uniqueness

**Status: preprint, October 2026; not yet peer-reviewed.** Author: Nic Johns. Licensing: the papers and documentation
are CC BY 4.0, the scripts are Apache-2.0 (see [Licence](#licence)).

This repository contains a mathematics research paper (42 pages) in analytic number theory, the scripts and logs
behind every computer-assisted statement in it, and a companion manuscript and three notes from the same project.

**How it was made.** The mathematics, the proofs, the numerical certificate scripts and the text were produced by AI
agents: instances of Anthropic's Claude working as coordinated agents, with separate Claude agents acting as hostile
referees. The independent checks included a review of the paper and its certificates by OpenAI's Astra, which re-ran
every certificate; its corrections are incorporated.
**No human mathematician has yet checked the proofs line by line.**

## What the result says, in plain language

The **Riemann zeta function** ζ(s) encodes the distribution of the prime numbers. Its nontrivial zeros are complex
numbers ρ = β + iγ with 0 < β < 1. The Riemann Hypothesis (RH), one of the best-known open problems in mathematics,
says that all of them lie on the **critical line** β = 1/2.

**Weil's explicit formula** is an exact identity that links the zeros to the prime powers. For every test function F
in a suitable class, a sum of F over the zeros plus a sum of its Fourier transform over the prime powers equals an
explicit quantity built from the Gamma factor of ζ and its pole at s = 1 (the "archimedean data"). If RH holds, the
zeros and the prime powers of ζ form one solution of this identity by two positive measures: one on the zero side
and one on the prime side.

**The question.** The paper keeps ζ's archimedean data fixed and asks for **all** solutions of the explicit formula
by two positive measures, the prime-side one supported beyond log 2/(2π) ("admissible pairs"). Nothing is assumed
about where the measures live, or about integrality. The paper conjectures (**Conjecture U**) that every admissible
pair, if one exists, is ζ's pair. Conjecture U does not by itself imply RH: it is consistent with "RH fails and no
admissible pair exists". Under Conjecture U, however, RH becomes equivalent to the existence of an admissible pair.

The results, in order of weight:

1. **Uniqueness near ζ's own solution (Theorem B).** Suppose an admissible pair has its zero measure carried by the
   zeros of ζ together with finitely many extra points, and its prime measure carried by the Bondarenko–Radchenko–Seip
   interpolation nodes. Then it is ζ's own pair, and RH holds. "Near" means exact containment in these sets, up to
   finitely many extra points on the zero side; it is not a statement about small displacements. The proof needs the
   prime measure to be positive on only one residue class of nodes, and the zero measure to be positive only at the
   origin. It uses theta-group cusp expansions and Landau's theorem on Dirichlet series with non-negative
   coefficients.
2. **Duality, and criticality as atomicity (Theorem A).** Linear-programming duality attaches one number to the
   problem, the **slack** κ\*. Admissible pairs exist if and only if κ\* ≥ 0, a positivity statement that involves
   neither zeros nor primes. The number q_min = e^{−2πκ\*} is the best degree-one conductor bound that the explicit
   formula gives from ζ's archimedean data, over test functions F ≥ 0 whose Fourier transform is non-negative beyond the
   gap. This sharpens the explicit-formula method of Stark and Odlyzko, recast by Serre and refined by Poitou, whose test
   functions have a non-negative Fourier transform everywhere. If admissible pairs exist, κ\* = 0 exactly when every admissible zero
   measure is purely atomic, carried by one discrete set.

   A **magic-function principle** (the Corollary after Theorem B) links this to uniqueness. Suppose some test
   function F ≥ 0, with Fourier transform non-negative beyond the gap, satisfies all of the following:
   - its explicit-formula value is 0;
   - it has only finitely many real zeros outside the zero set of ζ;
   - every zero of its Fourier transform beyond the gap lies in the Bondarenko–Radchenko–Seip nodes.

   Then Conjecture U holds.
3. **Certified bounds (Theorem C; computer-assisted).** Unconditionally, −2.7112·10⁻³ ≤ κ\* ≤ 1.1508391·10⁻⁹⁰⁶, so
   1 − 7.3·10⁻⁹⁰⁶ ≤ q_min < 1.017182. Only if an admissible pair exists, for instance under RH, is κ\* ≥ 0, that is,
   q_min ≤ 1. The theorem sharpens the bound that the explicit-formula method can give; the arithmetic conductor of ζ is
   1 in any case. In the classical cone (Fourier transform non-negative everywhere), κ\*_OPS ≤ 9.9462·10⁻⁴¹; Odlyzko's
   tables give 0.997 for this bound. The upper bound comes from an explicit test function that vanishes at every zero
   of ζ, and a ladder of such certificates, J = 20, …, 100, keeps improving with J. The certificates are evidence for
   Conjecture S (κ\* ≤ 0), and they form a reproducible tool: a shipped script checks each one in exact and interval
   arithmetic.
4. **What remains, specified (Theorem D).** Conjecture U and κ\* ≤ 0 would follow from asymptotic properties of an
   explicit family of test functions Ξ²P_J(t²), defined by Hermite interpolation at the first J prime powers. These
   properties are open. At J = 10, 60, 61, 110 and 111 the paper certifies that the interpolation problem is
   non-singular, together with the coefficient bound behind two of the hypotheses.
5. **Two examples for contrast.** The archimedean data of the quadratic fields ℚ(√5) and ℚ(√−3) have strictly
   positive slack, both with ζ's gap and at the fields' own natural gaps. This indicates that near-criticality is a
   property of ζ's data rather than of the method.

## What it does NOT show

- It is **not a proof of RH**. It does not prove that an admissible pair exists without assuming RH; unconditionally
  only κ\* ≥ −2.7112·10⁻³ is known, that is, q_min < 1.017182.
- It does **not** prove κ\* = 0, Conjecture U or Conjecture S (κ\* ≤ 0). The exponent 906 reflects a computational
  budget (J = 100), not a limit.
- Uniqueness is proved only **near ζ's own solution**: a zero measure carried by ζ's zeros plus finitely many points,
  and a prime measure on the Bondarenko–Radchenko–Seip nodes. Extra prime-side mass off these nodes, or infinitely many extra zeros, are not
  covered.
- The hypotheses of Theorem D concern infinitely many J, or a limit in J, and are **open**. Only finite-J instances
  are certified; convergence of the family is neither assumed nor proved.
- The comparison with ℚ(√5) and ℚ(√−3) concerns **two examples**; it is not a statement about L-functions in
  general.
- **Human expert review is still pending.**

## How it was verified

| Kind of evidence | What it covers | Where |
|---|---|---|
| **Certified numerics** (exact rational arithmetic, exact Sturm sequences, Arb ball arithmetic) | every computer-assisted statement: Theorem 5.1 and Corollary 5.2 (κ\* ≤ 1.1508391·10⁻⁹⁰⁶), and Propositions 5.3, 5.4, 5.5, 5.8 and 5.9. Each has a standalone verifier, a parameter file pinned by SHA-256, and the log of a fresh run | `paper/anc/`; Appendix C of the paper |
| **Written proofs only** | Theorems A, B and D, the corollary after Theorem B, and every other proved statement (Sections 2–4 and Appendix B); no formal verification | `paper/` |
| **Independent AI referee reviews** | several rounds of review by separate Claude agents acting as hostile referees: the mathematics, the computations, the literature, the focus of the paper, and a final cold-read regression check. Their requested repairs were incorporated | cleaned review records will be added in a later release |

Values that were computed but not certified appear only in Numerical observation 5.6 (and, by reference, in the
evidence for Conjecture 6.1); they are never used in a proof. The supplementary works have their own status, stated in
`supplementary/README.md`.

## Repository map

| Path | Contents |
|---|---|
| `README.md` | this overview |
| `LICENSE`, `LICENSE-CC-BY-4.0` | Apache-2.0 (code) and CC BY 4.0 (papers and documentation); see [Licence](#licence) |
| `paper/main.tex`, `paper/macros.tex`, `paper/refs.bib` | the paper's LaTeX sources |
| `paper/sections/` | the section files that `main.tex` inputs: Sections 1–6 and Appendices A–C |
| `paper/build/main.pdf` | the compiled paper (42 pages) |
| `paper/production/` | the bibliography style `amsplain-doi.bst`, and `make_arxiv_tarball.sh`, which builds the arXiv source tarball (sources, `main.bbl`, `anc/`) and test-compiles it from a clean unpack |
| `paper/anc/` | the ancillary files as they would be posted on arXiv: verifiers, parameter files, logs, `SHA256SUMS`, and `README.md` with commands, expected output and runtimes |
| `supplementary/` | a companion manuscript and three notes from the same project, each with its LaTeX sources, a compiled `build/main.pdf` and, where present, its own `anc/`; overview in `supplementary/README.md` |

## Where to start

- **5-minute skim.** This file, then the abstract and §1.4 "What is claimed and what is not" of
  `paper/build/main.pdf` (pp. 1 and 4).
- **A mathematician.** §1 of the paper (pp. 1–6) states Theorems A–D and points to their proofs: §2 duality and
  criticality, §3 uniqueness (the cusp expansions are in Appendix B.1.5), §4 the criterion, §5 the certified bounds,
  §6 the conjectures and open problems.
- **Reproducing the numerics.** `paper/anc/README.md`: Python ≥ 3.10 with `python-flint==0.9.0` and `mpmath==1.3.0`
  only; every certificate has its command and expected output. The three batches take 39.0, 44.4 and 27.5
  CPU-minutes.
- **Rebuilding the PDF.** From `paper/`, run pdflatex, then bibtex, then pdflatex again until LaTeX no longer asks for a
  rerun (four pdflatex passes in all for the paper):

  ```sh
  mkdir -p build
  pdflatex -output-directory=build main.tex
  bibtex build/main
  pdflatex -output-directory=build main.tex
  pdflatex -output-directory=build main.tex
  pdflatex -output-directory=build main.tex
  ```

  Alternatively, `latexmk -pdf -outdir=build main.tex` reruns as often as needed.

## Relation to other work

The problem is dual to the optimisation behind the explicit-formula method for lower bounds of discriminants and
conductors (Stark, Odlyzko, Serre, Poitou). The uniqueness theorem uses the Fourier interpolation basis of Bondarenko,
Radchenko and Seip (*Fourier interpolation with zeros of zeta and L-functions*, Constr. Approx. 57 (2023);
arXiv:2005.02996). The structure parallels linear-programming bounds for sphere packing, where near-sharpness is
familiar:
- Theorem C corresponds to Cohn and Kumar's certificate that the bound in dimension 24 is sharp up to a factor
  1 + 1.65·10⁻³⁰;
- the explicit admissible pairs correspond to Cohn and Triantafillou's dual certificates of non-sharpness;
- Theorem D corresponds to the sequences that Cohn and Miller conjectured to converge to magic functions.

Section 1.5 of the paper discusses related work, including Weil positivity (Connes–Consani, Zhu), the highest lowest
zero (Miller; Bober et al.) and the classification of Fourier summation formulas.

## How to cite

```bibtex
@misc{Johns2026ZetaPositiveSolutions,
  author       = {Johns, Nic},
  title        = {Positive solutions of the explicit formula for {$\zeta(s)$}: near-criticality and uniqueness},
  year         = {2026},
  month        = oct,
  howpublished = {Preprint},
  url          = {https://github.com/nic410/zeta-positive-solutions}
}
```

A Zenodo DOI will be added with the first release.

## Licence

Copyright 2026 Nic Johns.

- **Papers and documentation** (`paper/*.tex`, `paper/sections/`, `paper/refs.bib`, `paper/build/main.pdf`, the
  texts and PDFs under `supplementary/`, and the READMEs and other documentation outside `anc/` directories,
  including this one):
  [Creative Commons Attribution 4.0 International](LICENSE-CC-BY-4.0) (CC BY 4.0).
- **Code** (everything under `paper/anc/` and under the `anc/` directories in `supplementary/`, including their
  READMEs, and the build script `paper/production/make_arxiv_tarball.sh`): [Apache License 2.0](LICENSE).

The bibliography style `amsplain-doi.bst` (in `paper/production/` and in each supplementary work) is a modified copy
of the American Mathematical Society's `amsplain.bst` and remains under the LaTeX Project Public License 1.3c, as
stated in its header.
