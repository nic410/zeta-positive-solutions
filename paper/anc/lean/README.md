# PositivityRigidity: the logical spine of Paper I in Lean 4

A Lean 4 / Mathlib formalisation (Phase 1) of the logical spine of

> *Positive solutions of the explicit formula for ζ(s): near-criticality and uniqueness* (Paper I),
> `paper/build/main.pdf` in this repository.

Phase 1 states the headline results — Theorems A, B, C, D and the Corollary (magic-function principle) —
faithfully in Lean, and proves them from Mathlib plus an explicit **axiom ledger**. Each axiom is either a
cited classical theorem, a computer-assisted certificate of §5 (with script, parameter-file SHA-256 and
log line), or an analytic step proved in the paper but not yet formalised.

**v1.3** (this version) follows v1.3 of the paper, which adds Theorem 3.11 (integer weights: if `(μ, ν)` is
admissible for `𝒜_q`, `q > 0`, and `μ` is purely atomic with integer weights, then `q ≥ 1`, and `q = 1` forces
RH and `(μ, ν) = p_ζ`; proof in Appendix B.3) and Corollary 3.12 (atomicity and integrality; part (a): (S) ⇔
every admissible `μ` is purely atomic, and (U) ⇔ every admissible `μ` is purely atomic with integer weights) in
a new §3.6, and states Theorem 3.11 again, unnumbered, in §1.3. Neither is formalised (`STATUS.md`, rows 24 and
25), and the unnumbered theorem is not one of the lettered headline results. No statement number changed and no
formalised statement changed, so the Lean sources, the 22 ledger axioms, `axioms.log` and the statement pin are
those of v1.2.

**v1.2** follows v1.2 of the paper: the exact members `F_J = Ξ² P_J(t²)` of Proposition 4.5 are
certified in the cone `𝒞`, and in the classical cone `𝒞_OPS`, without a cushion, for `J = 10, 60, 61, 110, 111`
(Proposition 5.7, new). Theorem C (a) becomes
`κ* ≤ κ*_OPS ≤ 1.4291572·10^{-1060}`, `q_min ≥ 1 − 8.98·10^{-1060}` and `e^{−2πκ*_OPS} ≥ 1 − 8.98·10^{-1060}`
(Theorem 5.1, Corollary 5.2), and Corollary 5.3 becomes `∫ Ξ² dμ ≤ 3.99·10^{-1060}` (`ExactMember.lean`,
`NearRigidity.lean`). One certificate axiom is added (`cert_exact_cone`) and two are removed (`cert_kappa_ladder`, the
cushioned representatives of v1.1's Table 1, and `cert_near_rigidity`); `F_J ∈ 𝒯`, `F_J ≥ Ξ²` and the evenness of
`F̂_J` are proved in Lean (from `xi_decay` and Proposition 5.6, `cert_finiteJ`). Statement numbers are those of v1.2
(Proposition 5.7 is new and the cushion lemma of Appendix A is gone, so the later statements of §5 and Appendix A are
renumbered).

**v1.1** follows v1.1 of the paper: Theorem 3.6 (zero-side support; Theorem B(a)), Theorem 3.8
for countably many extra zeros (Theorem B(b)), Corollary 3.9(a), Theorem 4.8 with the non-strict (Mg),
Corollary 4.11 (a certificate route) and Corollary 5.3 (near-rigidity), with three new ledger axioms. Statement
numbers in docstrings, `LEDGER.md` and `STATUS.md` are those of v1.2, which v1.3 keeps; Lean identifiers of v1.0
keep their v1.0 numbers (e.g. `thm_3_7` is Theorem 3.8 for finite `E`, `prop_5_3` is Proposition 5.4, `prop_5_8` is
Proposition 5.10), and the v1.0 headline theorems are kept unchanged (in v1.2, `theoremC` (a) carries the new
certified numbers).

## Status

* `lake build` succeeds with **no `sorry`**, no `native_decide`, and no `axiom` outside
  `PositivityRigidity/Ledger.lean` (`build.log`).
* **22 ledger axioms**: 3 classical, 10 analytic steps proved in the paper (two of which, `brs_lemma36_landau` and
  `brs_countable_meanvalue`, also carry the classical existence of the BRS basis), 9 certificates
  (`LEDGER.md`). v1.1 added `zero_support_rigidity`, `brs_countable_meanvalue` and `cert_near_rigidity`; v1.2
  added `cert_exact_cone` and removed `cert_kappa_ladder` and `cert_near_rigidity`.
* `#print axioms` of every headline theorem lists only ledger axioms and `propext`, `Classical.choice`,
  `Quot.sound` (`axioms.log`).
* Coverage of the 57 numbered statements of v1.3: 37 formalised (65 %), 29 proved (51 %); Theorem 3.11 and
  Corollary 3.12, new in v1.3, are not formalised; see `STATUS.md`.
* CI: `.github/workflows/lean.yml` (at the root of the public repository) builds the project and runs
  `scripts/audit.sh` on every push (section "Continuous integration and the audit" below).

| Paper | Lean (namespace `PosRig`) | File | Ledger axioms used |
|---|---|---|---|
| Theorem A (duality, criticality; Thm 2.7(a), Prop 2.10, Thm 2.12(b)) | `theoremA` | `Main.lean` | `duality_no_gap`, `floor_bound`, `weak_magic_functions` |
| Logic of §1.2 (Thm 2.9) | `logic_display`; `logic_a`–`logic_d` | `Main.lean`, `Logic.lean` | `explicit_formula`, `logic_b`, `duality_no_gap`, `floor_bound` |
| Theorem B(a) (Thm 3.6, zero-side support) — v1.1 | `theoremB_a` (`zero_support_theorem`) | `Main.lean`, `ZeroSupport.lean` | `zero_support_rigidity`, `logic_b` |
| Theorem B(b) (Thm 3.8 for `E ∪ −E`, `E` countable, weighted condition) — v1.1 | `theoremB_b` (`theoremB_b_countable`) | `Main.lean`, `CountableExtras.lean` | `brs_countable_meanvalue`, `explicit_formula`, `riemannZeta_neg_of_mem_Ioo` |
| Theorem B(b), finite `E` (the v1.0 Theorem B) | `theoremB'` (`theoremB`); also `theoremB_finite_of_countable` | `Main.lean`, `Uniqueness.lean`, `CountableExtras.lean` | `explicit_formula`, `riemannZeta_neg_of_mem_Ioo`, `brs_lemma36_landau` (resp. `brs_countable_meanvalue` instead) |
| Corollary, first sentence (Cor 3.9(a)) — v1.1 | `corollary_magic_a` (`magic_principle_zero`) | `Main.lean`, `ZeroSupport.lean` | `zero_support_rigidity`, `logic_b` |
| Corollary, second sentence, finitely many zeros (Cor 3.9(b), finite `E`) | `corollary_magic` | `Main.lean` | as `theoremB'` |
| Theorem C (Thm 5.1, Cor 5.2, Prop 5.10); v1.2: `κ* ≤ κ*_OPS ≤ 1.4291572·10^{-1060}`, `q_min ≥ 1 − 8.98·10^{-1060}`, the same bound for `e^{−2πκ*_OPS}` | `theoremC` (`thm_5_1`, `kappaOPS_le_kappa111`, `cor_5_2`, `prop_5_8_kappa`) | `Main.lean`, `ExactMember.lean`, `Certified.lean` | `cert_exact_cone`, `cert_finiteJ`, `xi_decay`, `cert_lowerbound`, `floor_bound` |
| Theorem 5.1, Corollary 5.2 and Proposition 5.7 (exact members in the cone) — v1.2 (`F_J ∈ 𝒞_OPS ⊆ 𝒞` for `J = 10, 60, 61, 110, 111`, without a cushion) | `thm_5_1`, `cor_5_2`, `cor_5_2_RH`, `prop_exact_cone` | `ExactMember.lean` | `cert_exact_cone`, `cert_finiteJ`, `xi_decay` (`floor_bound` for the conductor bounds; `explicit_formula` for the formula for `𝒜(F_J)` in `prop_exact_cone`, and under RH) |
| Theorem D (Thm 4.8, (Mg) non-strict) — v1.1 | `theoremD_nonstrict'` (`theoremD_nonstrict`) | `Main.lean`, `CriterionWeak.lean` | `robust_compactness`, `Zinf_lower_bound`, `xi_decay`, `explicit_formula`, `logic_b`, `zero_support_rigidity` |
| Theorem D with the strict (Mg) of v1.0 | `theoremD'` (`theoremD`) | `Main.lean`, `Criterion.lean` | as `theoremB'`, plus `robust_compactness`, `Zinf_lower_bound`, `xi_decay` |
| Corollary 4.11 (a certificate route) — v1.1 | `certificate_route` | `ZeroSupport.lean` | `zero_support_rigidity`, `logic_b`, `explicit_formula`, `riemannZeta_neg_of_mem_Ioo` |
| Corollary 5.3 (near-rigidity: `∫ Ξ² dμ ≤ 3.99·10^{-1060}`, through `F₁₁₁`; v1.1, with the numbers of v1.2) | `near_rigidity`, `near_rigidity_interval` (`exact111_near_rigidity`, `Ffam_ge_Xi_sq`) | `NearRigidity.lean`, `ExactMember.lean` | `cert_exact_cone`, `cert_finiteJ`, `xi_decay` |

## Building

Toolchain and pins (the same as those of the Lean formalisation of the families paper (github.com/nic410/dirichlet-critical-zeros)):

* `lean-toolchain`: `leanprover/lean4:v4.33.0-rc2`;
* Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`;
* Zeta23 (Lean formalisation of Alpöge–Furman, arXiv:2608.13637), `https://github.com/anthropics/zeta-23-lean`
  (now `anthropics/formal-math`, subdirectory `zeta23`), rev `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`;
* `lakefile.toml` with `autoImplicit = false`, `relaxedAutoImplicit = false`; `lake-manifest.json` is the
  manifest of the families formalisation with the package name changed.

Mathlib and the used Zeta23 modules must be **prebuilt**; this project compiles only its own ~7,830
lines (under two minutes on 8 cores). If a built checkout of a project with the same pins is at hand (for
instance the families formalisation), its packages can be reused by a hardlink copy (no extra disk space):

```sh
export PATH="$HOME/.elan/bin:$PATH"                                    # elan's lake/lean (if not on the PATH)
cp -al <built checkout with the same pins>/.lake/packages .lake/packages   # hardlinks, not a copy
nice -n 10 taskset -c 8-15 lake build                                  # builds PositivityRigidity only
nice -n 10 taskset -c 8-15 lake env lean scripts/print_axioms.lean     # regenerates axioms.log
python3 scripts/check_ledger_hashes.py                                 # re-checks every cited SHA-256
nice -n 10 env CORES=8-15 LEAN_NUM_THREADS=8 scripts/audit.sh          # the full audit (below)
```

Do **not** run `lake update` (it would move the pins). Elsewhere, `lake exe cache get` provides Mathlib's
oleans; the imported Zeta23 modules (below) then compile in a few minutes. `.lake/` is git-ignored.

## Module map (`PositivityRigidity/`)

| File | Content |
|---|---|
| `Basic.lean` | Definitions: `ξ_x`, `ξ₂`, strips; test class `𝒯_δ`, `𝒯` (`InTδ`, `TestClass`), Gaussian wave packets `𝒢` (`Gset`); `Ω_∞`, `𝒜` (`Arch`), `𝒜 + λ∫`, `𝒜_q`, `Ω_𝔤`, `𝒜_{𝔤,q}` (`ArchG`); pairs, admissibility at a gap for a functional (`Admissible`), `𝒦`, cones `𝒞_g`, `𝒞`, `𝒞_OPS`, slacks `κ*`, `κ*_OPS` (as `EReal` infima), `q_min`; non-trivial zeros, multiplicities, `t_ρ`, `Z_ζ`, `μ_ζ`, `ν_ζ`, `p_ζ`; (E), (U), (S); `Z(F)`, `Ẑ(F)`, discrete sets, atomic measures, exact and weak magic functions; BRS nodes `ℳ`, `ξ_PP`; `ξ`, `Ξ` |
| `BRSDefs.lean` | BRS basis (structure and defining properties), complex extension of `𝒜`, atom-weight pairings, the statements of Lemma 3.7 (3.4) for finite `E` and of the v1.0 Landau step |
| `FamilyDefs.lean` | `n_j`, `Ψ`, moments `m_k`, Hermite matrix `M_J`, `b_J`, `𝒥`, `p^{(J)}`, `P_J`, `H_J`, `F_J`; hypotheses (N), (G_a), (Z∞), the strict (Mg) of v1.0; hypotheses (i)–(v) of Lemma 4.7 |
| `CertDefs.lean` | Table 1 (v1.2: the certified exact members, `ExactRow`, `exactMembers`, `kappa111`), the windows of Table 2 |
| `ExtrasDefs.lean` | v1.1 definitions: the summability condition (3.5) (weighted and cumulative forms, as sums in `[0, ∞]`), `Lemma36Count` (Lemma 3.7, countable `E`), `MeanValueStep` (Lemmas B.3–B.4) |
| `Ledger.lean` | **All 22 axioms** (and nothing else) |
| `Sanity.lean` | Gaussian in `𝒯_δ`, `𝒞_OPS`, `𝒞_g`, `𝒢`; non-emptiness; elementary facts about `𝒯` (continuity, integrability, scaling, real transforms, vanishing of cone elements with `∫F = 0`); admissible pairs are Radon; linearity of `F̂` |
| `Faithful.lean` | Faithfulness checks: `Arch` = the paper's complex `𝒜` on `𝒯` (Schwarz reflection), `Ω_{Γ_ℝ} = Ω_∞`, `𝒢 ⊂ 𝒯_δ`, `RiemannHypothesis ↔` all zeros in `0 < Re s < 1` on the line |
| `Atoms.lean` | Measures carried by countable sets; bounds for `log 3`, `log 5` |
| `Zeta.lean` | `ξ = ½ s(s−1)Γ_ℝζ`, `Ξ` even, real on `ℝ`, zeros of `Ξ` = `Z_ζ`, `Ξ(t_ρ) = 0`, `Ξ(0) > 0`, `Z_ζ` countable, symmetric, multiplicities (with built Zeta23 modules) |
| `PZeta.lean` | `μ_ζ`, `ν_ζ`: support, atoms, evenness; **Theorem 2.9(a)** (RH ⇒ `p_ζ ∈ 𝒦`) from the explicit formula |
| `BRSValues.lean` | For every basis with the BRS properties: the values (3.3) of `𝒜`, **Proposition 3.5** (signed form) |
| `EFCheck.lean` | The explicit-formula axiom proved for a Paley–Wiener subclass of `𝒯` from Zeta23 (no ledger axiom) |
| `Duality.lean` | **Lemma 2.5** (weak duality), **Lemma 2.13** (complementary slackness), slacks of homogeneous functionals, **Theorem 2.7(a)**, **Proposition 2.8**, **Proposition 2.10** |
| `Logic.lean` | **Theorem 2.9** |
| `Criticality.lean` | **Theorem 2.12(b), (c)** |
| `Uniqueness.lean` | **Theorem 3.8** for finite `E` (atom-weight and admissible forms; the v1.0 route through the Landau step), **Proposition 3.5**, **Theorem B(b)** for finite `E`, **Corollary 3.9(b)** for finite `E` |
| `ZeroSupport.lean` | **Theorem 3.6** (zero-side support), Proposition 3.5 without the hypothesis on `ν`, **Corollary 3.9(a)**, **Corollary 4.11**; `∫ Ξ² dμ = 0` ⇒ `μ` carried by `Z_ζ`; `Ξ² ∈ 𝒯`; (U) ⇔ every admissible `μ` is carried by `Z_ζ` |
| `CountableExtras.lean` | **Theorem 3.8** for countable `E` (atom-weight and admissible forms), **Theorem B(b)**, the finite case without the Landau step; the weighted form of (3.5) implies the cumulative form |
| `Family.lean` | **Corollary 4.4**, last sentence of Lemma 4.7, interpolation property of **Proposition 4.5**, **Proposition 4.9(1)(2)**, **Proposition 5.6** consequences |
| `FamilyMore.lean` | **Proposition 4.5**: `F_J ∈ 𝒯`, double zeros (value and derivative rows), the tail formula for `𝒜(F_J)` |
| `Convexity.lean` | **Theorem 2.7(b)** convexity of `𝒦`; non-uniqueness of admissible pairs with a floor (**Proposition 5.11**, "not a singleton") |
| `Criterion.lean` | **Theorem 4.8 (D)** and **Remark 4.10(a)** with the strict (Mg) of v1.0, from a common core |
| `CriterionWeak.lean` | v1.1: **Theorem 4.8 (D)** with the non-strict (Mg), **Remark 4.10(a), (b)** (v1.1 forms), **Conjecture 6.1** with its non-strict part (c) and its implication |
| `Certified.lean` | **Propositions 5.4** (the Gaussian–Laguerre function), **5.5, 5.10, 5.11** (natural-gap step, exact arithmetic) |
| `ExactMember.lean` | v1.2: the exact members in the cones (`F_J ∈ 𝒞`, `𝒞_OPS` from the certified facts; `F_J ≥ Ξ²` from positive coefficients; `F̂` of an even function is even), **Proposition 5.7** (exact members in the cone), **Theorem 5.1** (`κ* ≤ κ*_OPS ≤ κ_J` for the rows of Table 1; `κ₁₁₁ = 1.4291572·10^{-1060}`), **Corollary 5.2** (`q_min ≥ 1 − 8.98·10^{-1060}`, the same for `e^{−2πκ*_OPS}`) |
| `NearRigidity.lean` | **Corollary 5.3** (v1.2: through `F₁₁₁ ≥ Ξ²`; `∫ Ξ² dμ ≤ 3.99·10^{-1060}`; `μ(I) ≤ 3.99·10^{-1060}/min_I Ξ²`) |
| `PosCert.lean` | **Lemma A.2** (positive-coefficient certificates) |
| `Conjectures.lean` | **Conjecture 6.1** in its v1.0 form (strict part (c)) stated, and its stated implication ((a)–(c) ⇒ (S), (U), RH ⇔ (E)) proved |
| `Main.lean` | **Theorems A, B, C, D, the Corollary**, the logic of §1.2, Conjecture S's equivalences, **Remark 4.10(b)** |

## Faithfulness: conventions and caveats

* `F : ℂ → ℂ`; only the values on the closed strip matter. `𝒯_δ` requires evenness on the strip, realness on
  `ℝ`, analyticity at every point of the closed strip (`AnalyticOnNhd`, i.e. on a neighbourhood), and
  `sup (1+|z|)²|F(z)| < ∞` there. `F̂` is Mathlib's `𝓕` of the restriction to `ℝ`, whose normalisation is the
  paper's.
* `Arch F` is real-valued: the real part of `F(i/2) + F(−i/2)` plus `∫ Re F · Ω_∞`. For `F ∈ 𝒯` it equals the
  paper's (complex) expression, proved in `Faithful.lean`. Likewise `intR F = ∫ Re F`.
* Positivity of complex values (`F(t) ≥ 0`, `F̂(ξ) ≥ 0`) uses Mathlib's order on `ℂ` (real and `≥ 0`).
* Measures are Mathlib `Measure ℝ` (positive); `ν` "on `[g, ∞)`" is a measure on `ℝ` carried by `[g, ∞)`.
  Local finiteness (Radon) is not written into `Admissible` because it follows from the integrability
  clause (`Admissible.isLocallyFinite`). Real measures carried by countable sets (Lemma 3.7, Theorem 3.8) are
  represented by their atom weights; for countable `E` the pairings with the BRS functions are required to
  converge absolutely (`Summable`), as in the paper.
* `DiscreteSet Z` (Theorem 2.12(b)(iii), Theorem A(b)) means *closed* discrete: no accumulation point in `ℝ`.
  This makes "(i) ⇒ (iii)" stronger and "(iii) ⇒ (ii)" weaker than plain "discrete"; both are proved.
* The BRS basis is not identified with a particular object: `brs_lemma36_landau` (resp.
  `brs_countable_meanvalue`) asserts the joint existence of a basis with the properties of Definition 3.4 and
  a coefficient function satisfying Lemma 3.7 for finite `E` and the v1.0 Landau step (resp. Lemma 3.7 for
  countable `E` and the mean-value step, Lemmas B.3–B.4), and Proposition 3.5 and Theorem 3.8 are proved for
  every such pair (no uniqueness is claimed; [BRS, Corollary 1.1] needs `H₁`, which `𝒯`-decay does not
  give).  Uniform decay of the basis on closed strips is the paper's reading of [BRS §4.3].
* The summability condition (3.5) is formalised as sums of non-negative terms in `[0, ∞]` (`WeightedCond`;
  `CumulativeCond`, "`A(T) ≤ εT^{1/2}` eventually, for every `ε > 0`"), so it has no junk value; `a_e = μ({e})`.
* (Mg) of v1.1 (`HypMg0`, "`F̂_J(ξ) ≥ −ε` eventually") is weaker than the strict (Mg) of v1.0 (`HypMg`), and
  Conjecture 6.1 of v1.1 (`ConjFamily0`) is weaker than that of v1.0 (`ConjFamily`); both implications are
  proved.
* `κ*`, `κ*_OPS`, `κ*_g` are `EReal` infima (never junk). `q_min = e^{−2πκ*}` is defined with
  `κ*.toReal`, meaningful because `κ*` is proved finite (`kappaStar_ne_bot/top`).
* `RiemannHypothesis` is Mathlib's; non-trivial zeros are the zeros in `0 < Re s < 1` (equivalence proved:
  `RH_iff_critical`).
* Proposition 2.8's "even real Radon measure `μ` with `μ − λdt ≥ 0`" is formalised, as in the first line of
  its proof, as a pair admissible for `𝒜 − λ∫` (`FloorFeasible`).
* Theorem C: the decimals are exact rationals (`1.4291572·10^{-1060} = 14291572/10^{1067}`,
  `8.98·10^{-1060} = 898/10^{1062}`, …).
* Theorem D's hypotheses (Mg), (iii), (iv) are written without `liminf` ("eventually `≥ c > 0`",
  "eventually `≥ −ε`"), which is equivalent for real sequences. Corollary 4.11's "`𝒜(F_J)/c_J → 0` for `J` in
  an infinite set" is a limit along `atTop ⊓ 𝓟 I`. The Hermite system is set up over `ℝ` with
  real parts of the (real-valued) moments; `M_J`'s derivative rows use `deriv` in `ξ`.
* The certificate axioms are existential (weaker than the certificates, which exhibit the functions), except
  `cert_exact_cone` (v1.2), which is about the exact members `Ffam J` themselves (`M_J` is certified non-singular
  for these `J`, `cert_finiteJ`, so `Ffam J` is the paper's `F_J`); the arithmetic combining them is done in Lean.

## Continuous integration and the audit

`.github/workflows/lean.yml`, at the root of the repository, is the workflow of the Lean formalisation of the families paper (github.com/nic410/dirichlet-critical-zeros), with working
directory `paper/anc/lean`. On every push and
pull request to `main` (and on demand) it frees disk space, adds 8 GB of swap, starts a resource monitor,
installs elan, restores the `.lake` cache (keyed on `lake-manifest.json` and `lean-toolchain`), downloads the
Mathlib build cache (`lake exe cache get`), runs `lake build` (a cold build compiles the imported Zeta23 modules
from source and takes hours on the 4-core runner; later runs reuse the cache), saves the cache, runs
`scripts/audit.sh`, and uploads the build, audit and monitor logs.

`scripts/audit.sh` prints one final line, `AUDIT PASSED` or `AUDIT FAILED` (exit code 0 or 1). It fails on:

| Check | What it verifies |
|---|---|
| (0) | `lake build --no-build PositivityRigidity` succeeds: the audited `.olean` files are those of the current sources |
| (a) | no `sorry`, `admit` or `native_decide` token in any Lean file of the project (`PositivityRigidity/`, `PositivityRigidity.lean`, `scripts/`; comments and strings stripped) |
| (b) | no `axiom` declaration outside `PositivityRigidity/Ledger.lean` (textually, and in the environment: `scripts/Audit.lean` scans every declaration of the library); the number of ledger axioms equals the total in `LEDGER.md`, which names each of them; no declaration depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound` and the ledger axioms (so no `sorryAx`, no `Lean.ofReduceBool`); the 14 headline theorems exist |
| (c) | the output of `scripts/print_axioms.lean` (`#print axioms` for every headline theorem and every other formalised numbered statement) equals `axioms.log` (its `# ` header lines excepted) exactly |
| (d) | statement pin: the output of `scripts/Statements.lean` — the types of the 14 headline theorems and of every ledger axiom, and the types and bodies of every project definition they unfold to, with structural hashes — equals `scripts/Statements.baseline.txt` exactly |
| (e) | every SHA-256 cited in `Ledger.lean` and `LEDGER.md` matches `paper/anc/SHA256SUMS` (`scripts/check_ledger_hashes.py`, Python standard library only) |
| (f) | non-vacuity: `scripts/NonVacuity.lean` compiles, and each of its 11 theorems (the test class and the cones contain the Gaussian, `κ*` is not a junk value, admissible pairs are Radon, `Arch` and `RiemannHypothesis` are the paper's, the explicit formula holds on a Paley–Wiener subclass, the hypotheses of the v1.1 results can be met) uses only `propext`, `Classical.choice`, `Quot.sound` |

Run it locally after `lake build` (it takes about half a minute on 8 cores once the project is built):

```sh
export PATH="$HOME/.elan/bin:$PATH"
nice -n 10 env CORES=8-15 LEAN_NUM_THREADS=8 scripts/audit.sh     # CORES= disables the CPU pinning
```

`CORES` (default `0-3`) is the CPU list for `taskset`, `LEAN_NUM_THREADS` defaults to 4, and `AUDIT_NO_GIT=1`
computes the printed provenance digest without git. After a deliberate change, regenerate the baselines:
`lake env lean scripts/print_axioms.lean` (with the header of `axioms.log`) and
`lake env lean scripts/Statements.lean > scripts/Statements.baseline.txt`, and update `LEDGER.md` if an axiom
is added or removed.

## Zeta23

Built Zeta23 modules imported: `Zeta23.Statement.Seam`, `Zeta23.ZetaReflect` (in `Zeta.lean`:
`riemannZeta_analyticOnNhd_compl_one`, `analyticOrderAt_riemannZeta_ne_top`, `ZetaSeam.finite_window_holds`,
`analyticOrderAt_zeta_conj`, `analyticOrderAt_zeta_one_sub`, `zeta_reflect_zero`) and `Zeta23.WeilEF.Main`
(only in `EFCheck.lean`). What Zeta23 offers for this paper:

* the Weil explicit formula for `ζ`, unconditionally (`Zeta23.WeilEF.EF_lit_zetaZeroConfig`), but only for
  test functions `F = paperFT k` with `k ∈ C_c²(ℝ)`, i.e. `F̂ ∈ C_c²` (Paley–Wiener type). This class does not
  contain `𝒯` (e.g. `1/(1+t²) ∈ 𝒯`), so Lemma 2.3 remains a ledger axiom; `EFCheck.lean` proves the axiom's
  exact conclusion on the even real part of that class, as a consistency check of the axiom;
* zero facts: multiplicities `≥ 1` and finite, finiteness of zeros in compact sets and windows, symmetry under
  `ρ ↦ ρ̄` and `ρ ↦ 1 − ρ` with multiplicities (used); local zero counts `N(t+1) − N(t) ≪ log t` and
  `Σ m_ρ/(1+γ²) < ∞` (available);
* digamma facts (`digamma_conj`, Stirling-type bounds for `Re ψ`) that would serve Lemma 2.2(c) and (2.2).

**Phase 2 candidate:** derive Lemma 2.3 on `𝒯` from Zeta23's Paley–Wiener formula by approximation
(`k_n = (k·χ(·/n)) ⋆ φ_n` with `k = (2π)^{-1}F̂(·/2π)`; dominated convergence on the zero side with
`zero_sum_inv_sq`, on the archimedean side with `abs_mu_le_of_gammaFacts`, on the prime side with
`Σ Λ(n) n^{-1-δ}`), which would remove `explicit_formula` from the ledger.
