# Positive solutions of the explicit formula for ζ(s): near-criticality and uniqueness

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23197915.svg)](https://doi.org/10.5281/zenodo.23197915) [![Lean](https://github.com/nic410/zeta-positive-solutions/actions/workflows/lean.yml/badge.svg)](https://github.com/nic410/zeta-positive-solutions/actions/workflows/lean.yml)

**Status: preprint, October 2026; not yet peer-reviewed.** Author: Nic Johns. Licensing: the papers and documentation
are CC BY 4.0, the scripts are Apache-2.0 (see [Licence](#licence)).

This repository contains a mathematics research paper (51 pages) in analytic number theory, the scripts and logs
behind every computer-assisted statement in it, and a companion manuscript and three notes from the same project.

**How it was made.** The mathematics, the proofs, the numerical certificate scripts and the text were produced by AI
agents: instances of Anthropic's Claude working as coordinated agents, with separate Claude agents acting as hostile
referees. The independent checks included a review of the paper and its certificates by OpenAI's Astra, which re-ran
every certificate; its corrections are incorporated. Two theorems and their proofs were contributed by OpenAI's Astra
during an independent review of an earlier version of the paper, and were then checked line by line by independent
Claude referees: the zero-side support theorem (Theorem 3.6), and the extension of Theorem B from finitely to countably
many extra zeros (Theorem 3.8, with its aggregate estimates and mean-value argument, Lemmas B.3–B.4). Astra also
contributed their consequences Corollary 3.9(a), Corollary 4.11 and the weakening of hypothesis (Mg) in Theorem 4.8.
The certificates of the exact members added in version 1.2 (Proposition 5.7) were produced and independently refereed by
Claude agents; their jet-subtraction approach was suggested by an analysis of the planar Cohn–Elkies certificate cited in
the paper. The theorem on integer weights added in version 1.3 (Theorem 3.11, with Corollary 3.12) and its proof were
produced and independently refereed by Claude agents.
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

1. **Uniqueness near ζ's own solution (Theorem B).**
   - (a) If an admissible pair has its zero measure carried by the zeros of ζ and the origin, then it is ζ's own pair,
     and RH holds. Nothing is assumed about the prime measure (Theorem 3.6, due to Astra).
   - (b) The same holds if the zero measure is carried by the zeros of ζ together with countably many extra points
     satisfying a summability condition (for instance finitely many), and the prime measure by the
     Bondarenko–Radchenko–Seip interpolation nodes (Theorem 3.8; the extension from finitely to countably many extra
     points is due to Astra).

   "Near" means exact containment in these sets, up to the stated extra points on the zero side; it is not a statement
   about small displacements. Part (b) needs the prime measure to be positive on only one residue class of nodes, and
   the zero measure to be positive only at the origin; its proof uses theta-group cusp expansions and a mean-value
   argument for an almost periodic function.
2. **Uniqueness for integer weights (Theorem 3.11).** If the zero measure of an admissible pair is purely atomic with
   integer weights, as for the zeros of an L-function, then the pair is ζ's own and RH holds, whatever the prime measure.
   With ζ's Gamma factor and pole but a conductor q in place of 1, such pairs exist only if q ≥ 1. Consequently
   Conjecture U holds if and only if every admissible zero measure is purely atomic with integer weights, while, by
   Theorem A(b), Conjecture S (κ\* ≤ 0) holds if and only if every admissible zero measure is purely atomic
   (Corollary 3.12). The proof turns the prime measure into a positive generalised Dirichlet series with Riemann's
   functional equation, and combines the one-dimensional Cohn–Elkies bound (Fejér's kernel) with Hamburger's theorem.
3. **Duality, and criticality as atomicity (Theorem A).** Linear-programming duality attaches one number to the
   problem, the **slack** κ\*. Admissible pairs exist if and only if κ\* ≥ 0, a positivity statement that involves
   neither zeros nor primes. The number q_min = e^{−2πκ\*} is the best degree-one conductor bound that the explicit
   formula gives from ζ's archimedean data, over test functions F ≥ 0 whose Fourier transform is non-negative beyond the
   gap. This sharpens the explicit-formula method of Stark and Odlyzko, recast by Serre and refined by Poitou, whose test
   functions have a non-negative Fourier transform everywhere. If admissible pairs exist, κ\* = 0 exactly when every admissible zero
   measure is purely atomic, carried by one discrete set.

   A **magic-function principle** (the Corollary after Theorem B) links this to uniqueness. Let F ≥ 0 be a test
   function whose Fourier transform is non-negative beyond the gap, and whose explicit-formula value is 0.
   - If every real zero of F lies in the zero set of ζ or at the origin, then Conjecture U holds; no condition on the
     zeros of its Fourier transform is needed.
   - The same holds if F has finitely many other real zeros (or countably many, under a summability condition) and
     every zero of its Fourier transform beyond the gap lies in the Bondarenko–Radchenko–Seip nodes.
4. **Certified bounds (Theorem C; computer-assisted).** Unconditionally, −2.7112·10⁻³ ≤ κ\* ≤ 1.4291572·10⁻¹⁰⁶⁰, so
   1 − 8.98·10⁻¹⁰⁶⁰ ≤ q_min < 1.017182. Only if an admissible pair exists, for instance under RH, is κ\* ≥ 0, that is,
   q_min ≤ 1. The theorem sharpens the bound that the explicit-formula method can give; the arithmetic conductor of ζ is
   1 in any case. The upper bound holds already in the classical cone (Fourier transform non-negative everywhere):
   κ\*_OPS ≤ 1.4291572·10⁻¹⁰⁶⁰, so the classical conductor bound is at least 1 − 8.98·10⁻¹⁰⁶⁰, where Odlyzko's tables
   give 0.997. It comes from an explicit test function Ξ²P₁₁₁(t²) that vanishes at every zero of ζ: the exact member
   J = 111 of the family of Theorem D, certified to lie in the cone without approximation (Proposition 5.7). The
   certified members J = 10, 60, 61, 110, 111 keep improving with J. The certificates are evidence for Conjecture S
   (κ\* ≤ 0), and they form a reproducible tool: a shipped script checks each one in interval arithmetic. They also
   give **near-rigidity** (Corollary 5.3): every admissible pair has ∫Ξ²dμ ≤ 3.99·10⁻¹⁰⁶⁰, so its zero measure puts
   mass at most 3.99·10⁻¹⁰⁶⁰/min_I Ξ² on any compact interval I that avoids the zeros of ζ. This is informative at low
   height.
5. **What remains, specified (Theorem D).** Conjecture U and κ\* ≤ 0 would follow from asymptotic properties of an
   explicit family of test functions Ξ²P_J(t²), defined by Hermite interpolation at the first J prime powers. These
   properties are open; the limiting Fourier transforms need only be non-negative beyond the gap. At J = 10, 60, 61,
   110 and 111 the paper certifies that the interpolation problem is non-singular, together with the coefficient bound
   behind two of the hypotheses, and that the exact members lie in the cone. Conjectures U and S would also follow from
   exact cone members F_J ≥ c_JΞ² with
   𝒜(F_J)/c_J → 0 (Corollary 4.11, due to Astra).
6. **Two examples for contrast.** The archimedean data of the quadratic fields ℚ(√5) and ℚ(√−3) have strictly
   positive slack, both with ζ's gap and at the fields' own natural gaps. This indicates that near-criticality is a
   property of ζ's data rather than of the method.

## What it does NOT show

- It is **not a proof of RH**. It does not prove that an admissible pair exists without assuming RH; unconditionally
  only κ\* ≥ −2.7112·10⁻³ is known, that is, q_min < 1.017182.
- It does **not** prove κ\* = 0, Conjecture U or Conjecture S (κ\* ≤ 0). The exponent 1060 reflects a computational
  budget (J = 111), not a limit.
- Uniqueness is proved only **near ζ's own solution, or for integer weights**: a zero measure carried by ζ's zeros and
  the origin (any prime measure); a zero measure carried by ζ's zeros plus countably many summable points, with the
  prime measure on the Bondarenko–Radchenko–Seip nodes; or a purely atomic zero measure with integer weights (any prime
  measure). Extra zeros, when some zero weight is not an integer, together with prime-side mass off these nodes or
  without the summability condition, and diffuse extra zero mass are not covered.
- The hypotheses of Theorem D concern infinitely many J, or a limit in J, and are **open**. Only finite-J instances
  are certified; convergence of the family is neither assumed nor proved.
- The comparison with ℚ(√5) and ℚ(√−3) concerns **two examples**; it is not a statement about L-functions in
  general.
- **Human expert review is still pending.**

## How it was verified

| Kind of evidence | What it covers | Where |
|---|---|---|
| **Certified numerics** (exact rational arithmetic, exact Sturm sequences, Arb ball arithmetic) | every computer-assisted statement: Theorem 5.1 and Corollaries 5.2 and 5.3 (κ\* ≤ 1.4291572·10⁻¹⁰⁶⁰; ∫Ξ²dμ ≤ 3.99·10⁻¹⁰⁶⁰), and Propositions 5.4, 5.5, 5.6, 5.7, 5.10 and 5.11. Each has a standalone verifier, an input file pinned by SHA-256, and the log of a fresh run | `paper/anc/`; Appendix C of the paper |
| **Lean 4, checked by the Lean kernel** | the logical spine: Theorems A–D and the Corollary are stated in Lean and derived from an explicit ledger of axioms (cited theorems, certificate outputs, and analytic steps of the paper not yet formalised) | `paper/anc/lean/` and its `README.md` |
| **Written proofs** | Theorems A, B and D, the Corollary, and every other proved statement (Sections 2–4 and Appendix B) | `paper/` |
| **Independent AI reviews** | several rounds of review by separate Claude agents acting as hostile referees (the mathematics, the computations, the literature, the focus of the paper, cold-read regression checks); an independent review by OpenAI's Astra, which contributed Theorems 3.6 and 3.8 (as extended); and line-by-line checks of those two proofs by independent Claude referees. Requested repairs were incorporated | cleaned review records will be added in a later release |

Values that were computed but not certified appear only in Numerical observation 5.8 (and, by reference, in the
evidence for Conjecture 6.1); they are never used in a proof. The supplementary works have their own status, stated in
`supplementary/README.md`.

## Repository map

| Path | Contents |
|---|---|
| `README.md` | this overview |
| `LICENSE`, `LICENSE-CC-BY-4.0` | Apache-2.0 (code) and CC BY 4.0 (papers and documentation); see [Licence](#licence) |
| `paper/main.tex`, `paper/macros.tex`, `paper/refs.bib` | the paper's LaTeX sources |
| `paper/sections/` | the section files that `main.tex` inputs: Sections 1–6 and Appendices A–C |
| `paper/build/main.pdf` | the compiled paper (51 pages) |
| `paper/production/` | the bibliography style `amsplain-doi.bst`, and `make_arxiv_tarball.sh`, which builds the arXiv source tarball (sources, `main.bbl`, `anc/`) and test-compiles it from a clean unpack |
| `paper/anc/` | the ancillary files as they would be posted on arXiv: verifiers, parameter files, logs, `SHA256SUMS`, and `README.md` with commands, expected output and runtimes |
| `paper/anc/lean/` | the Lean 4 formalisation of the paper's logical spine, with its axiom ledger, status table and audit scripts; see its `README.md` |
| `.github/workflows/lean.yml` | continuous integration for the Lean project in `paper/anc/lean/` (the "Lean" badge above) |
| `supplementary/` | a companion manuscript and three notes from the same project, each with its LaTeX sources, a compiled `build/main.pdf` and, where present, its own `anc/`; overview in `supplementary/README.md` |

## Where to start

- **5-minute skim.** This file, then the abstract and §1.4 "What is claimed and what is not" of
  `paper/build/main.pdf` (pp. 1 and 4).
- **A mathematician.** §1 of the paper (pp. 1–7) states Theorems A–D and the theorem on integer weights, and points to
  their proofs: §2 duality and criticality, §3 uniqueness (the zero-side support proof is in Appendix B.1.4, the cusp
  expansions and the mean-value step in Appendix B.1.6, the proof for integer weights in Appendix B.3), §4 the
  criterion, §5 the certified bounds, §6 the conjectures and open problems.
- **Reproducing the numerics.** `paper/anc/README.md`: Python ≥ 3.10 with `python-flint==0.9.0` and `mpmath==1.3.0`
  only; every certificate has its command and expected output. The four batches take 41.6, 52.0, 29.1 and 205.6
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
  doi          = {10.5281/zenodo.23197915},
  url          = {https://github.com/nic410/zeta-positive-solutions}
}
```

The DOI above is the concept DOI, which always resolves to the latest archived version; each release also has its
own version DOI on [Zenodo](https://doi.org/10.5281/zenodo.23197915) (v1.0.0: 10.5281/zenodo.23197916; v1.1: 10.5281/zenodo.23199443; v1.2: 10.5281/zenodo.23211712; v1.3: 10.5281/zenodo.23217537). GitHub's
"Cite this repository" button (generated from `CITATION.cff`) gives the same reference in other formats.

## Related repository

[nic410/dirichlet-critical-zeros](https://github.com/nic410/dirichlet-critical-zeros) (DOI [10.5281/zenodo.23070759](https://doi.org/10.5281/zenodo.23070759)) is an earlier paper by the same author, produced the same way: an unconditional proportion of simple zeros on the critical line for a weighted family of Dirichlet L-functions, with a Lean 4 formalisation. The two papers are independent; neither uses the other's results.

## Licence

Copyright 2026 Nic Johns.

- **Papers and documentation** (`paper/*.tex`, `paper/sections/`, `paper/refs.bib`, `paper/build/main.pdf`, the
  texts and PDFs under `supplementary/`, and the READMEs and other documentation outside `anc/` directories,
  including this one):
  [Creative Commons Attribution 4.0 International](LICENSE-CC-BY-4.0) (CC BY 4.0).
- **Code** (everything under `paper/anc/`, including the Lean project in `paper/anc/lean/`, and under the `anc/`
  directories in `supplementary/`, including their READMEs; the build script `paper/production/make_arxiv_tarball.sh`;
  and the CI workflow in `.github/`): [Apache License 2.0](LICENSE).

The bibliography style `amsplain-doi.bst` (in `paper/production/` and in each supplementary work) is a modified copy
of the American Mathematical Society's `amsplain.bst` and remains under the LaTeX Project Public License 1.3c, as
stated in its header.
