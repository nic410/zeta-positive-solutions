# Supplementary works

**Author:** Nic Johns
**Licence:** texts and PDFs CC BY 4.0; code and data in the `anc/` directories Apache-2.0; copyright 2026 Nic Johns; see
`LICENSE` and `LICENSE-CC-BY-4.0` at the repository root.

This directory holds the material that accompanies the main paper in `../paper/` (*Positive solutions of the explicit
formula for ζ(s): near-criticality and uniqueness*, called **Paper I** below) but is not part of it. All of
it was written together with Paper I and shares its notation and its standards of proof: every statement is either
proved, or a computer-assisted certificate that names its script and parameter file, or a numerical observation that
is labelled as such and never used in a proof.

**Status: companion drafts, not peer-reviewed.** None of these works has been submitted for publication. They are kept
here so that every result that left Paper I remains available, with its proof and its certificates, and so that the
companion manuscript can later be promoted to a standalone paper.

## What is here

Four works, each with its exact title:

| Directory | Work | Relation to Paper I |
|---|---|---|
| `hermite-interpolation/` | **Companion manuscript** (about 60 pp): *Hermite interpolation at the prime powers: a positivity calculus, a polynomial model, and a family of test functions vanishing at the zeros of ζ(s)* | Develops the interpolation problem behind the family Ξ(t)²P_J(t²) of Paper I, whose members vanish at every non-trivial zero of ζ (Paper I calls them zero-killing). Proves a kernel-free calculus, a criterion "one likelihood-ratio law per level" in a polynomial model, the front of the model for every J ≤ 80 (computer-assisted), far-node asymptotics, an obstruction, and counterexamples to a natural sign property; certifies the root geometry of the exact members at J = 60, 110, 111; reduces the open hypotheses of the criterion of Paper I (Theorem D there) to explicit step laws, which remain open. |
| `notes/extra-primes/` | **Note** (13 pp): *Extra prime atoms in positive solutions of the explicit formula: theta-group class sums and an obstruction* | Extends the uniqueness theorem of Paper I (Theorem 3.8 there, extra zeros) towards extra atoms of the prime measure, with full proofs of the structure lemma and the local theta lemma it uses, and a positive-spanning property of the Bondarenko–Radchenko–Seip functions U_m, m ≡ 2 (mod 3): at any finitely many positive points that are not zero ordinates of ζ, their value vectors positively span. Since the zero-side support theorem of Paper I (Theorem 3.6, contributed by Astra) excludes extra prime mass when there are no extra zeros, these results matter only together with extra zeros, where the question remains open when some zero weight is not an integer (Theorem 3.11 of Paper I). |
| `notes/critical-conductors/` | **Note** (9 pp): *Critical conductors of small archimedean data* | Certified brackets for the critical conductors of Γ_ℝ² and Γ_ℂ, valid for every gap up to slightly beyond the natural gaps of ℚ(√5) and ℚ(√−3), so that the data of these fields are certifiably not critical at their natural gaps; an admissible pair for the data of ℚ(i); the pinning of the pole weight of ζ's data (the residue of −ζ′/ζ at s = 1); computed critical conductors for seven Gamma types (at the gap ξ₂ = log 2/2π) compared with minimal discriminants, and the computed slack as a function of the gap; and the question whether critical data force uniqueness for other Gamma factors. |
| `notes/integer-beurling/` | **Note** (5 pp): *Integer-weight solutions of the explicit formula: a characterisation of ζ among uniformly discrete Beurling systems* | Positive solutions whose zero measure has integer weights: if the prime measure is carried by the logarithms of the integers (Hamburger's theorem), or generates a uniformly discrete multiplicative monoid (a theorem of Lev and Olevskii and an argument on linear recurrences), the solution is ζ's own and the Riemann hypothesis holds. Superseded by Theorem 3.11 of Paper I, which needs no condition on the prime measure; a remark in the note says so. |

Each work cites Paper I as "companion paper, in preparation" and recalls, in a section called *Setting*, the
definitions and the results of Paper I that it uses (as "Facts", without proof), so that it can be read on its own.
Paper I cites the four works, in the order of the table, as works in preparation; it does not depend on any of them.

The `anc/` directory inside each work, where present, holds the ancillary files of that work: parameter files,
standalone verifiers and logs, with their own `README.md`. Each is self-contained; inputs and certificates shared with
Paper I (the shared library, the certified enclosures of the exact members, and a few certificates on other Gamma
factors) are shipped as identical copies, and each text says which. The two notes on extra prime atoms and on integer
weights have no computer-assisted statements and no `anc/` directory.

## Status of each work

- **Companion manuscript.** Complete draft. Everything infinite in J that it proves is either kernel-free algebra or
  a conditional reduction whose hypotheses are named; nothing infinite in J is proved for the families themselves.
  Its five conjectures and four open problems are in its last section, with what each would imply and what a finite
  prefix of the computed family can and cannot decide. `hermite-interpolation/NEXT-STEPS.md` lists its open problems
  and the work that remains before a journal version.
- **Note on extra prime atoms.** Not yet a paper. Without extra zeros, extra prime mass is now excluded by Paper I (the
  zero-side support theorem, Theorem 3.6, contributed by Astra), and countably many extra zeros with summable weights are handled there
  too; what remains open is extra prime mass together with extra zeros, when some zero weight is not an integer.
- **Note on critical conductors.** A short computational note. Its certified brackets also hold at the natural gaps
  of ℚ(√5) and ℚ(√−3); its comparisons with minimal discriminants and its profile of the slack in the gap are
  numerical observations, and for the types other than Γ_ℝ² and Γ_ℂ the comparisons were computed at the gap ξ₂ only.
- **Note on integer weights.** Short and complete: its theorem is proved in full and uses no computation. The case of
  a general Beurling system (not uniformly discrete), stated there as open, is settled by Theorem 3.11 of Paper I,
  which also supersedes part (b) of the note's theorem.

## Building

Each work is a self-contained LaTeX document (`amsart`, the standard AMS packages, `booktabs`, `enumitem`, `xcolor`,
`hyperref`, `geometry`; bibliography style `amsplain-doi.bst`, included). From the directory of a work:

```sh
mkdir -p build
pdflatex -output-directory=build main.tex
bibtex build/main
pdflatex -output-directory=build main.tex
pdflatex -output-directory=build main.tex
```

The result is `build/main.pdf`; a compiled copy is included.
