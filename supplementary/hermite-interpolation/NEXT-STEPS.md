# Next steps: open problems and the work before a journal version

This file accompanies the companion manuscript *Hermite interpolation at the prime powers: a positivity calculus, a
polynomial model, and a family of test functions vanishing at the zeros of ζ(s)* (`main.tex` in this directory). It
lists the questions the manuscript leaves open and the editorial and computational work that remains before a journal
version. The main paper that the manuscript accompanies, cited there as the companion paper, is in `../../paper/`. The
precise open statements, five conjectures and four open problems, are in Section 11 of the manuscript. None of the
items below affects the correctness of a stated result.

## Scope and length

- The manuscript has about 60 pages. Decide between one paper and a split into (a) the kernel-free calculus and the
  polynomial model (Sections 3–8, about 30 pages, with genuine unconditional and computer-assisted theorems) and (b) the
  true family (Section 9), which is conditional throughout; (b) may be better as the last section of (a), or as a
  separate report, than as a journal paper on its own.
- Prune for a standalone paper: the number of numbered statements, the 15 numerical observations of Section 10, and the
  named conditions of Table 2 (about 40). Keep only the named laws that enter the headline results; move secondary
  observations to the README of the ancillary files.
- Restate the headline results of the introduction as numbered theorems once the final numbering is fixed.

## Notation

- Several symbols still carry more than one meaning and should be renamed before submission:
  - κ: the shifts κ_m in the expansion (7.1) of the model and the constants κ_r of Lemma 7.10, against the slack κ*
    of Section 2;
  - S: the screening factor S_y and S(B), the partial sums S_{≤m}(z), and the Stirling numbers S(m, i);
  - a: the coefficients a, b of the insertion formula, a_B, a_J and a*;
  - μ: the measures of Section 2 and the derivative weights μ_j, μ_Y of the p₁-rule;
  - Φ: the bordered determinant Φ_Z and the vectors Φ_l of the window criterion;
  - θ: the Euler operator and the angles θ₀ of the zero-side lemmas.

## Mathematics

- The window criterion of Remark 6.4 now has a derivation in the text; promote it to a lemma with a complete proof,
  including the non-degeneracy hypotheses.
- The far-node asymptotics for the true kernel (Theorem 9.27) have O-constants that depend on the node set. Explicit
  remainders, as for the model (Proposition 7.6), are needed to certify the tail constant B₁₁₀.
- State more precisely which arguments the obstruction (Proposition 7.11) excludes and which it does not.
- The criterion now needs only the non-strict condition (Mg), and the certificate route needs no limit: for infinitely
  many J, P_J > 0 on [0, ∞), the front statement (FR) at J, and Arch(F_J)/min H_J → 0. Decide which step laws of Section 9 are
  still needed in the strict form (Mg>) (which also describes the zero set of the limit transform), and whether the tail results of
  Section 9 can give the bound on Arch(F_J).
- The hypotheses (C01), (C02), (Z) of the sandwich step and the root-count hypothesis (CNT₁) are supported only by
  computations; consider whether any of them can be proved for the model.
- Quantify which property of the prime powers the front law of the model (Conjecture 11.4) uses: it fails on the integer
  nodes and on the progression y*, so the relevant property seems to be growth well above the PT-tight scale rather than
  sparsity as such; e.g. node sets satisfying PT_δ for some δ > 0 together with a regularity condition. A heuristic for
  the limit of the Newton-normalised margins of Table 5 (about 2.4 at K = 40, 1.7 at K = 160) would also help.

## Computations

- Several numerical observations are not reproduced by the ancillary files: Numerical observation 10.11 (further tail
  data of the model, items (a)–(d)), all items of Numerical observation 10.14 (computed data quoted in the
  text), the heuristic tail step in the computation of B₆₀ and B₁₁₀, and the observations on the true family that were
  computed with research code. For every observation that is kept, ship its script and data; otherwise drop it.
- Certify B₁₁₀ (Open problem (3) of Section 11) and close the base data (B⁺)₆₀ on [1, 2) and on (199, 199.39).
- After the final re-run of the ancillary files, re-check every number quoted in the text and in the tables, and the
  SHA-256 hashes of Table 8.
- Propositions 9.9, 9.19 and 9.20 (root geometry, base data, increments) read byte-identical copies of the enclosures
  `exact/out/P{J}_ball.txt` produced by the ancillary files of the main paper (hashes in `anc/README.md` and
  `anc/SHA256SUMS`). If the main paper regenerates them, re-copy them and re-run these three certificates.

## Literature

- The related-work paragraph of the introduction is short. Position the calculus relative to total positivity and
  Chebyshev systems, Christoffel-type formulas for multiple orthogonal polynomials and Hermite–Padé problems, and the
  recent literature on Fourier interpolation (radial interpolation in small dimensions, interpolation with derivatives).
  Verify every new reference at its primary source.
- Add exact pinpoints to the citations of the main paper once its numbering is final.

## Alignment with the main paper

- The non-strict form of Theorem D and the certificate route of the main paper (its Corollary 4.11) rest on its zero-side
  support theorem (Theorem 3.6), contributed by Astra (OpenAI); Section 2 cites them.
- Section 2 restates results of the main paper as Facts; the criterion through the zero-killing family is cited as
  its Theorem D. When that paper is final, align the restated statements and constants with it and cite the other
  Facts by number. The root geometry of the exact members (Proposition 9.9) is certified here, not there.

## Front matter

- Author, date, licence and AI-use statement are set (October 2026); update the date at submission.

## The three notes (`../notes/`)

- Extra prime atoms: not yet a paper (see its status paragraph). Its two numerical observations are not certified and
  their computations are not in ancillary files.
- Critical conductors: the window-mass computations and the computations in three one-parameter families of Gamma
  factors (Numerical observation 5.3) are not in the ancillary files, and the second is described only in outline. Ship
  them with a precise description, or drop them.
- Critical conductors: the comparisons of Numerical observation 5.1 for the five types other than Γ_ℝ² and Γ_ℂ were
  computed at the gap ξ₂ only; compute them at the natural gaps of the corresponding fields too, or say less. The
  profile of the slack in the gap (Numerical observation 3.4) is not in the ancillary files either.
- Integer weights: complete as a short note; its open problems (the general Beurling case, weaker discreteness) are
  stated in its last section.
