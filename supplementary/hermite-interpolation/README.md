# Hermite interpolation at the prime powers

*A positivity calculus, a polynomial model, and a family of test functions vanishing at the zeros of ζ(s)* (companion
manuscript)

**Author:** Nic Johns
**Date:** October 2026
**Licence:** texts and PDFs CC BY 4.0; code and data in the `anc/` directories Apache-2.0; copyright 2026 Nic Johns; see
`LICENSE` and `LICENSE-CC-BY-4.0` at the repository root.

**Status:** complete companion draft, not peer-reviewed. It accompanies the main paper in `../../paper/` (*Positive
solutions of the explicit formula for ζ(s): near-criticality and uniqueness*), which it cites as "companion
paper, in preparation". Its open problems, and the work that remains before a journal version, are listed in
`NEXT-STEPS.md`.

## What it is

The companion paper reduces two conjectures about positive solutions of Weil's explicit formula for ζ to four
hypotheses on an explicit family Ξ(t)²P_J(t²) of zero-killing test functions (they vanish at every non-trivial zero of ζ),
defined by double-node Hermite interpolation of the kernel
Ψ = (Ξ²)^ at the first J prime powers. This manuscript studies that interpolation problem for an arbitrary kernel and
for three kernels in particular: the true kernel Ψ, its archimedean part, and e^{−y}, which gives a polynomial model
(equivalently, radial Fourier interpolation on the circles |v| = √(2n) in ℝ²).

Thesis: positivity of the interpolant beyond the nodes reduces, level by level, to one likelihood-ratio law per level.

- Proved for all J: a kernel-free calculus (Christoffel, ladder, insertion and half-step identities, two tail bounds);
  the criterion "one likelihood-ratio law per level" in the model; far-node asymptotics (model: constant 8J; true
  kernel: 8(J+1)); an obstruction showing that open sign conditions on the five-function system cannot give the tail
  of the model; conditional reductions of the hypotheses of the companion paper's criterion (its Theorem D) to explicit step laws.
- Computer-assisted: the front of the model for every J ≤ 80 (two independent certificates); small cases J ≤ 4;
  counterexamples to a natural sign property (W) at and inside the critical density, and (W) for two and three
  nodes; tail laws of the model on finite ranges; base data and increments of the true family at J = 10, 60, 110; the
  root geometry of the exact members at J = 60, 110, 111.
- Open: every step law for all J (five conjectures, Section 11); nothing infinite in J is proved for the families.
- Numerical observations: all in Section 10, never used in proofs.

## Layout

```
main.tex            top-level file
macros.tex          macros
sections/           00-abstract, 01-intro, 02-setting (results of the companion paper, as Facts),
                    03-nested, 04-chain (kernel-free calculus), 05-08 (the model), 09-true (the true family),
                    10-observations, 11-conjectures, A-proofs, B-certificates, C-anc
refs.bib            bibliography (only the works cited)
amsplain-doi.bst    bibliography style
build/main.pdf      compiled PDF
anc/                ancillary files: verifiers, parameter files and logs (see anc/README.md)
NEXT-STEPS.md       open problems and the work remaining before a journal version
```

## Building

```sh
mkdir -p build
pdflatex -output-directory=build main.tex
bibtex build/main
pdflatex -output-directory=build main.tex
pdflatex -output-directory=build main.tex
```
