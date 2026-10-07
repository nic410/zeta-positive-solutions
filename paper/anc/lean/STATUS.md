# Status: every numbered statement of Paper I

Numbering of v1.2 of the paper (`paper/build/main.pdf`, built 2026-10-07 10:49 UTC). This version has **55**
numbered statements: those of v1.1, plus **Proposition 5.7** (exact members in the cone), minus the cushion lemma
of Appendix A. (v1.1 had the 51 of v1.0, minus the Landau step (v1.0 Lemma B.3), plus **Theorem 3.6** (zero-side
support), **Corollary 4.11** (a certificate route), **Corollary 5.3** (near-rigidity), **Lemma B.3** (aggregate
expansion) and **Lemma B.4** (mean-value step).)
Where a statement was renumbered, its v1.0 number is given in brackets. The lettered statements of §1
(Conjectures U, S; Theorems A–D; the Corollary) are listed at the end.

**v1.2.** The exact members `F_J = Ξ² P_J(t²)` of Proposition 4.5 are certified in `𝒞_OPS ⊆ 𝒞` without a cushion
for `J = 10, 60, 61, 110, 111` (Proposition 5.7, row 41, ledger axiom `cert_exact_cone`); Table 1 lists these
members, and Theorem 5.1, Corollaries 5.2 and 5.3 and Theorem C now follow from it
(`κ* ≤ κ*_OPS ≤ 1.4291572·10^{-1060}`, `q_min ≥ 1 − 8.98·10^{-1060}`, `∫ Ξ² dμ ≤ 3.99·10^{-1060}`).

Status values:

* **proved (Mathlib only)** — no ledger axiom (Zeta23, a proved library, is noted where used);
* **proved from ledger axioms [list]**;
* **ledger axiom** — the statement (or the named part) is an axiom of `Ledger.lean`;
* **not formalised (reason)**.

Lean names are in namespace `PosRig`; files are in `PositivityRigidity/`. Lean identifiers of v1.0 keep their
v1.0 numbers (e.g. `thm_3_7` is Theorem 3.8 for finite `E`, `prop_5_3` is Proposition 5.4, `prop_5_8` is
Proposition 5.10); the docstrings use the v1.2 numbers.

## §2 Admissible pairs, duality and criticality

| # | Statement | Lean | Status |
|---|---|---|---|
| 1 | Definition 2.1 (test class; `𝒢 ⊂ 𝒯_δ`) | `InTδ`, `TestClass`, `gwp`, `gwpSpan`, `Gset` (Basic); `Gset_inTδ`, `Gset_subset_TestClass` (Faithful); `gauss_mem_TestClass`, `gauss_mem_Gset` (Sanity) | proved (Mathlib only): the definitions, and the claim `𝒢 ⊂ 𝒯_δ` for every `δ` |
| 2 | Lemma 2.2 (elementary facts: decay of `F̂`, `F(i/2)+F(−i/2) = 2∫F̂ cosh`, `|𝒜(F)| ≤ C_δ‖F‖_δ`) | — | not formalised (contour shift and Fourier inversion in the strip, digamma growth; used only inside the axiomatised steps `floor_bound`, `duality_*`) |
| 3 | Lemma 2.3 (explicit formula on `𝒯`) | `explicit_formula` (Ledger); `explicit_formula_of_paleyWiener`, `paperFT_mem_TestClass` (EFCheck) | **ledger axiom** (classical). Its exact conclusion is *proved (Mathlib + Zeta23)* for the Paley–Wiener subclass `F = paperFT k`, `k ∈ C_c²` even real |
| 4 | Definition 2.4 (admissible pairs, cones, slack, (E), (U), (S)) | `Admissible`, `Kset`, `K`, `ConeG`, `Cone`, `ConeOPS`, `slack`, `kappaStar`, `kappaOPS`, `CondE`, `CondU`, `CondS` (Basic); `Admissible.isLocallyFinite`, `Cone_nonempty` (Sanity); `kappaStar_le_kappaOPS` (Duality) | proved (Mathlib only): definitions; admissible pairs are Radon; `κ* ≤ κ*_OPS` |
| 5 | Lemma 2.5 (weak duality) | `weak_duality`, `weak_duality_nonneg`, `weak_duality_masses`, `not_dominatesLeb_of_cone` (Duality); `integral_le_Arch` (ZeroSupport) | proved (Mathlib only), for every functional and gap |
| 6 | Lemma 2.6 (a priori bounds) | — | not formalised (used only inside axiomatised steps: Theorem 2.7(ii)⇒(i), Theorem 3.6; and for the countable part of Corollary 3.9(b), which is therefore not formalised) |
| 7 | Theorem 2.7 (duality) | `duality`, `duality_i_ii`, `duality_ii_iii`, `duality_ii_iv`, `duality_shift` (Duality) | (a) proved from ledger axioms [`duality_no_gap` for (ii)⇒(i), `duality_gaussian` for (iii)⇒(ii)]; (i)⇒(ii), (ii)⇔(iv) proved (Mathlib only). (b): convexity of `𝒦` proved (Mathlib only: `Kset_convex`, `K_convex`, Convexity); `𝒢`-sufficiency and vague compactness not formalised (not used by the spine) |
| 8 | Proposition 2.8 (floors) | `prop_2_8`, `floorFeasible_iff`, `prop_2_8_dominates`, `kappaStar_ne_bot`, `kappaStar_ne_top` (Duality) | proved from ledger axioms [`duality_no_gap`, `floor_bound`] |
| 9 | Theorem 2.9 (logic) | `logic_a`, `logic_b'`, `logic_c`, `logic_d`, `pZeta_mem_K_iff_RH` (Logic); `pZeta_mem_K_of_RH` (PZeta) | (a) proved from ledger axioms [`explicit_formula`]; (b) **ledger axiom** `logic_b`; (c) proved from [`explicit_formula`, `logic_b`, `duality_no_gap`]; (d) proved from [`duality_no_gap`, `floor_bound`] |
| 10 | Proposition 2.10 (conductor form) | `slack_Arch_q`, `conductor_form`, `conductor_bound`, `condS_iff_qmin`, `qmin_le_one_of_RH` (Duality, Logic) | proved from ledger axioms [`duality_no_gap`, `floor_bound`; `explicit_formula` for RH ⇒ `q_min ≤ 1`] |
| 11 | Definition 2.11 (magic functions, `Z(F)`, `Ẑ(F)`) | `IsExactMagic`, `IsWeakMagic`, `ZF`, `ZhatF` (Basic) | proved (Mathlib only): definitions |
| 12 | Theorem 2.12 (criticality and atomicity) | `weak_magic_functions` (Ledger); `criticality`, `criticality_c`, `weakMagic_zeros_discrete`, `weakMagic_carries_mu/nu` (Criticality) | (a) **ledger axiom**; (b) proved from ledger axioms [`weak_magic_functions`, `duality_no_gap`, `floor_bound`]; (c) proved from [`weak_magic_functions`], except "zeros of `F*` have even order" (not formalised) |
| 13 | Lemma 2.13 (complementary slackness) | `comp_slackness`, `comp_slackness_gen` (Duality) | proved (Mathlib only), for every functional and gap |

## §3 Uniqueness

| # | Statement | Lean | Status |
|---|---|---|---|
| 14 | Lemma 3.1 (homogeneous directions) | — | not formalised (distributional Fourier analysis; not used by the headline results) |
| 15 | Proposition 3.2 (two-sided rigidity) | — | not formalised (positive-definite measures, Wiener's lemma; not used by the headline results) |
| 16 | Proposition 3.3 (Poisson examples) | — | not formalised (distributional Poisson summation; examples) |
| 17 | Definition 3.4 (the BRS basis) | `BRSBasis`, `IsBRSBasis` (BRSDefs); `brs_lemma36_landau`, `brs_countable_meanvalue` (Ledger) | **ledger axiom** (existence, BRS 2023 Thm 1.1, asserted jointly with Lemma 3.7 and the Landau step, resp. the mean-value step; no uniqueness claimed); formula (3.2) not formalised (only used inside Lemma 3.7) |
| 18 | Proposition 3.5 (uniqueness on `ζ`'s support) | `prop_3_5` (Uniqueness); signed form `support_uniqueness_thm`, values (3.3) `ArchC_brsU`, `ArchC_brsV0` (BRSValues); without the hypothesis on `ν` (remark after Theorem 3.6): `prop_3_5_strong` (ZeroSupport) | proved from ledger axioms [`explicit_formula`, `riemannZeta_neg_of_mem_Ioo`] for **every** basis with the properties of Definition 3.4 (`support_uniqueness_thm`); the admissible form `prop_3_5` via Theorem B [+ `brs_lemma36_landau`]; `prop_3_5_strong` from [`zero_support_rigidity`, `logic_b`] |
| 19 | **Theorem 3.6 (zero-side support)** — new | `zero_support_rigidity` (Ledger); `zero_support_theorem`, `zero_support_rigidity_sanity`, `isClosed_Zzeta` (ZeroSupport) | proved from ledger axioms [`zero_support_rigidity`, `logic_b`]: the first conclusion `ν = ν_ζ` (with the origin variant, `μ` carried by `Z_ζ ∪ {0}`) is the **ledger axiom** `zero_support_rigidity`; RH and `μ = μ_ζ` follow by Theorem 2.9(b), as in the paper |
| 20 | Lemma 3.7 (structure of pairs with extra atoms) [v1.0: 3.6] | `Lemma36` (BRSDefs), `Lemma36Count` (ExtrasDefs); `brs_lemma36_landau`, `brs_countable_meanvalue` (Ledger) | **ledger axiom** (formula (3.4) with absolutely convergent `c_N(E)`: for finite `E` part of `brs_lemma36_landau`, for countable `E` part of `brs_countable_meanvalue`; `B`, `α` existential); the "Moreover" clauses not formalised |
| 21 | Theorem 3.8 (countably many extra zeros) [v1.0: 3.7, finite `E`] | `extra_zeros_countable` (atom weights, real measures), `extra_zeros_countable_admissible`, `cumulativeCond_of_weightedCond`, `weightedCond_of_finite` (CountableExtras); finite `E` through the Landau step: `thm_3_7`, `thm_3_7_admissible` (Uniqueness) | proved from ledger axioms [`explicit_formula`, `riemannZeta_neg_of_mem_Ioo`] for every `(B, α)` satisfying Definition 3.4, Lemma 3.7 (countable) and Lemma B.4 (`extra_zeros_countable`), with (3.5) in its weighted or cumulative form; the admissible form obtains `(B, α)` from `brs_countable_meanvalue`. The weighted form of (3.5) implies the cumulative form (Mathlib only). For finite `E` also through `brs_lemma36_landau` (v1.0 route) |
| 22 | Corollary 3.9 (magic-function principle) [v1.0: 3.8 = (b) for finite `E`] | (a) `magic_principle_zero`, `condU_of_zero_support` (ZeroSupport); (b) finite `E`: `magic_function_principle` (Uniqueness) | (a) proved from ledger axioms [`zero_support_rigidity`, `logic_b`]; (b) for finite `E` proved from [`explicit_formula`, `riemannZeta_neg_of_mem_Ioo`, `brs_lemma36_landau`]; (b) for countable `E` under (3.6) not formalised (needs Lemma 2.6's bound `μ(E ∩ [n, n+1]) ≤ C log(3+n)` to pass from (3.6) to (3.5); Theorem 3.8 itself is formalised) |
| 23 | Remark 3.10 (extra prime atoms) [v1.0: 3.9] | — | not formalised (remark: heuristic about Gauss sums; its first sentence is Theorem 3.6) |

## §4 The zero-killing family and Theorem D

| # | Statement | Lean | Status |
|---|---|---|---|
| 24 | Lemma 4.1 (`Ψ > 0`) | — | not formalised (Riemann's representation of `Ξ`; used only inside the certificates) |
| 25 | Proposition 4.2 (Bessel form of `Ψ`) | — | not formalised (Mellin/Koshliakov analysis; used only inside the certificates) |
| 26 | Remark 4.3 (attribution) | — | not formalised (remark, no mathematical claim beyond Prop. 4.2) |
| 27 | Corollary 4.4 (explicit formula for zero-killing functions) | `zero_killing_EF` (Family) | proved from ledger axioms [`explicit_formula`] |
| 28 | Proposition 4.5 (the exact family) | `hermiteM`, `hermiteB`, `Jset`, `pvec`, `Pfam`, `Hfam`, `Ffam` (FamilyDefs); `FT_Ffam`, `FT_Ffam_pp` (Family); `deriv_FT_Ffam_pp`, `Ffam_mem_TestClass`, `Arch_Ffam_tail` (FamilyMore) | proved from ledger axioms [`xi_decay`; `explicit_formula` for the formula for `𝒜(F_J)`]: double zeros at `ξ_{n_1..n_J}`, `F_J ∈ 𝒯`, tail formula. Not formalised: the uniqueness clause ("exactly one") and the reformulation as a Hermite-interpolation error |
| 29 | Lemma 4.6 (integral representation) | — | not formalised (Bessel integral; used only inside the certificates) |
| 30 | Lemma 4.7 (robust compactness) | `RobustHyp` (FamilyDefs), `robust_compactness` (Ledger); `Arch_nonneg_of_zero_killing` (Family) | **ledger axiom**; its last sentence (`𝒜 ≥ 0` on zero-killing elements of `𝒞`) proved from [`explicit_formula`] |
| 31 | Theorem 4.8 (Theorem D), (Mg) non-strict | `theoremD_nonstrict`, `HypMg0`, `robustHyp_of_weak`, `criterion_core_weak`, `hypMg0_of_hypMg` (CriterionWeak); v1.0 form with the strict (Mg): `theoremD` (Criterion) | proved from ledger axioms [`robust_compactness`, `Zinf_lower_bound`, `xi_decay`, `explicit_formula`, `logic_b`, `zero_support_rigidity`]; the strict form, with the additional conclusion `F̂_∞⁻¹(0) ∩ [ξ₂, ∞) = ξ_PP` stated after the theorem, from [`robust_compactness`, `Zinf_lower_bound`, `xi_decay`, `explicit_formula`, `riemannZeta_neg_of_mem_Ioo`, `brs_lemma36_landau`] |
| 32 | Proposition 4.9 (coefficient bounds control the zero side) | `coeff_bound_consequences` (Family) | (1), (2) proved (Mathlib only); the "so (Z∞)/(G_a) hold" consequences are used in `remark_4_10a(_nonstrict)`; (3) normality, (4) Eneström–Kakeya not formalised |
| 33 | Remark 4.10 (variants) | (a) `remark_4_10a_nonstrict` (CriterionWeak), strict form `remark_4_10a` (Criterion); (b) `remark_4_10b` (Main), `remark_4_10b_zero` (CriterionWeak) | proved from ledger axioms: (a) [`robust_compactness`, `xi_decay`, `explicit_formula`, `logic_b`, `zero_support_rigidity`] — no `Zinf_lower_bound`; (b) first sentence [`weak_magic_functions`, `duality_no_gap`, Theorem B's axioms], last sentences (`Z(F*) ⊆ Z_ζ ∪ {0}`) [`weak_magic_functions`, `duality_no_gap`, `logic_b`, `zero_support_rigidity`] |
| 34 | **Corollary 4.11 (a certificate route)** — new | `certificate_route`, `carriedBy_Zzeta_of_lintegral`, `carriedBy_Zzeta_of_integral`, `exists_Xi_sq_lower`, `Xi_sq_mem_TestClass` (ZeroSupport) | proved from ledger axioms [`zero_support_rigidity`, `logic_b`, `explicit_formula`, `riemannZeta_neg_of_mem_Ioo`] (for an infinite index set; also `RH ⇔ (E)`, and `κ* = 0`, `𝒦 = {p_ζ}` under either). `Ξ² ∈ 𝒯` is not needed (lower integrals; `∫ F_J ≥ c_J ∫_{[−δ,δ]} Ξ²`); it is proved anyway [`xi_decay`]. "`∫ Ξ² dμ = 0` ⇒ `μ` carried by `Z_ζ`" is proved (Mathlib only) |

## §5 Certified bounds

| # | Statement | Lean | Status |
|---|---|---|---|
| 35 | Theorem 5.1 (certified upper bound for `κ*`, Table 1) | v1.2: `thm_5_1`, `thm_5_1_rows`, `kappaStar_le_kappa111`, `kappaOPS_le_kappa111`, `exact111` (ExactMember) | v1.2: proved from ledger axioms [`cert_exact_cone`, `cert_finiteJ`, `xi_decay`]: for every row of Table 1 (`J = 10, 60, 61, 110, 111`) `F_J ∈ 𝒞_OPS ⊆ 𝒞`, `∫ F_J > 0`, `𝒜(F_J) ≤ κ_J ∫ F_J`, so `κ* ≤ κ*_OPS ≤ κ_J`; in particular `κ* ≤ κ*_OPS ≤ 1.4291572·10^{-1060}`. |
| 36 | Corollary 5.2 (conductor form; infeasible deformations) | `cor_5_2`, `cor_5_2_RH`, `exists_cert111`, `two_pi_kappa111` (ExactMember) | v1.2 (`λ > 1.4291572·10^{-1060}`; `q ≤ 1 − 8.98·10^{-1060}`; `η > 8.9796596·10^{-1060}`; `q_min ≥ 1 − 8.98·10^{-1060}` and `e^{−2πκ*_OPS} ≥ 1 − 8.98·10^{-1060}`): proved from ledger axioms [`cert_exact_cone`, `cert_finiteJ`, `xi_decay`; `floor_bound` for the conductor bounds; `duality_no_gap`, `explicit_formula` under RH] |
| 37 | **Corollary 5.3 (near-criticality forces near-rigidity)** — new | `near_rigidity`, `near_rigidity_interval` (NearRigidity); `exact111_near_rigidity`, `Ffam_ge_Xi_sq` (ExactMember) | v1.2: proved from ledger axioms [`cert_exact_cone`, `cert_finiteJ`, `xi_decay`]: `∫ Ξ² dμ ≤ 3.99·10^{-1060}` for every admissible pair (with integrability), and `μ(I) ≤ 3.99·10^{-1060}/min_I Ξ²` for compact `I ⊂ ℝ \ Z_ζ`; `F_J ≥ Ξ²` from non-negative coefficients of `P_J` proved (Mathlib only). |
| 38 | Proposition 5.4 (the classical cone) [v1.0: 5.3] | `prop_5_3` (Certified) | proved from ledger axioms [`cert_kappaOPS`, `floor_bound`] (the Gaussian–Laguerre function; v1.2's sharper `κ*_OPS ≤ 1.4291572·10^{-1060}` is Theorem 5.1, `thm_5_1`) |
| 39 | Proposition 5.5 (low-height rigidity, Table 2) [v1.0: 5.4] | `prop_5_4`, `zero_window_bound`, `prime_window_bound` (Certified) | proved from ledger axioms [`cert_lowheight`] (all 13 entries of Table 2) |
| 40 | Proposition 5.6 (certified finite-`J` instances) [v1.0: 5.5] | `cert_finiteJ` (Ledger); `prop_5_5` (Family); `pcoef_nonneg_of_finiteJ` (ExactMember) | the certified facts are a **ledger axiom**; `H_J ≥ 1` on `ℝ`, `|H_J| ≤ cosh(0.71636|t|)` proved from it (Prop. 4.9); v1.2: also `F_J ≥ Ξ²` for the exact members |
| 41 | **Proposition 5.7 (exact members in the cone)** — new | `cert_exact_cone` (Ledger); `prop_exact_cone`, `exact_cone_facts`, `Ffam_mem_Cone_of`, `Ffam_mem_ConeOPS_of`, `FT_neg_of_even`, `Ffam_ge_Xi_sq` (ExactMember) | (b) `F̂_J ≥ 0` on `[0, ∞)` and (c) the bounds for `𝒜(F_J)`, `∫ F_J` are the **ledger axiom** `cert_exact_cone`; (a) `F_J ≥ Ξ²` (Mathlib only, from the coefficients of Proposition 5.6), `F_J ∈ 𝒞_OPS ⊆ 𝒞` [`cert_exact_cone`, `cert_finiteJ`, `xi_decay`] and the formula for `𝒜(F_J)` [`explicit_formula`, `xi_decay`, `cert_finiteJ`] proved; `F̂_J > 0` off the nodes, with zeros of order exactly two, not formalised (only `≥ 0`; order `≥ 2` is `deriv_FT_Ffam_pp`) |
| 42 | Numerical observation 5.8 [v1.0: 5.6] | — | not formalised (uncertified computation, by design never used) |
| 43 | Lemma 5.9 (Herglotz form) [v1.0: 5.7] | inside `cert_lowerbound`, `cert_Qsqrt5_pair`, `cert_Qsqrtm3_pair` | **ledger axiom** (folded into the three pair certificates, which assert admissibility directly) |
| 44 | Proposition 5.10 (lower bound for `κ*`) [v1.0: 5.8] | `prop_5_8`, `prop_5_8_kappa`, `prop_5_8_qmin` (Certified) | proved from ledger axioms [`cert_lowerbound`; `duality_no_gap`, `floor_bound` for `q_min ≤ e^{0.02}`] |
| 45 | Proposition 5.11 (`ℚ(√5)`, `ℚ(√−3)`, all gaps up to the natural ones) [v1.0: 5.9] | `prop_5_9_a`, `prop_5_9_b`, `prop_5_9_gaps`, `admissible_mono_gap` (Certified); `prop_5_9_not_singleton`, `not_unique_of_dominates` (Convexity) | proved from ledger axioms [`cert_Qsqrt5_dual/pair`, `cert_Qsqrtm3_dual/pair`]: the slack brackets at every gap `g ∈ (0, ξ_{x₀}]` (natural-gap step and `log 3`, `log 5`, `π` arithmetic in Lean); "some admissible pair has `μ ≥ 1.64·10^{-5} dt`" (resp. `1.50·10^{-4}`) and "the set of admissible pairs is not a singleton" (perturbation by an atom, proved in general) |
| 46 | Remark 5.12 (the gap and the margins) [v1.0: 5.10] | — | not formalised (remark; its brackets for the critical conductors follow the same pattern) |

## §6 Conjectures

| # | Statement | Lean | Status |
|---|---|---|---|
| 47 | Conjecture 6.1 (prime-power magic function), (c) non-strict | `ConjFamily0`, `conjFamily0_implies`, `conjFamily0_of_conjFamily` (CriterionWeak); v1.0 form (strict (c)): `ConjFamily`, `conjFamily_implies` (Conjectures) | stated (open); its stated implication ⇒ (S), (U), `RH ⇔ (E)` proved from ledger axioms [`robust_compactness`, `xi_decay`, `explicit_formula`, `logic_b`, `zero_support_rigidity`] (v1.0 form: [`robust_compactness`, `xi_decay`, `explicit_formula`, `riemannZeta_neg_of_mem_Ioo`, `brs_lemma36_landau`]); the v1.0 form implies the v1.1 form [`xi_decay`] |

## Appendix A

| # | Statement | Lean | Status |
|---|---|---|---|
| 48 | Remark A.1 (ball arithmetic) | — | not formalised (remark on arithmetic; no mathematical claim) |
| 49 | Lemma A.2 (positive-coefficient certificates) | `posc_a`, `posc_a'`, `posc_b`, `posc_b'` (PosCert) | proved (Mathlib only) |
| 50 | Lemma A.3 (validated `K_0`, `K_1`) | — | not formalised (DLMF series and asymptotics; used only inside the certificates) |
| 51 | Lemma A.4 (digamma on vertical lines) | — | not formalised (used only inside the certificates; Phase 2: from Mathlib's `digamma` series) |

## Appendix B

| # | Statement | Lean | Status |
|---|---|---|---|
| 52 | Lemma B.1 (expansion at the cusp 0) | — | not formalised (modular-integral analysis; used only inside the axiomatised Lemma B.4 and the Landau step) |
| 53 | Lemma B.2 (the class 2 mod 3) | — | not formalised (likewise) |
| 54 | **Lemma B.3 (aggregate expansion)** — new | — | not formalised (Mellin bound, cusp expansion in aggregate; used only inside Lemma B.4, axiomatised with it in `brs_countable_meanvalue`, whose part (ii) assumes the absolute convergence that B.3(a) proves) |
| 55 | **Lemma B.4 (mean-value step)** — new (replaces the v1.0 Landau step, Lemma B.3) | `MeanValueStep` (ExtrasDefs), `brs_countable_meanvalue` (Ledger) | **ledger axiom** (first assertion, with (B.7) in its cumulative form; part of `brs_countable_meanvalue`, `α` existential); the second assertion (`c_N = 0` on the class ⇒ `ϱ̃ = 0`) not formalised. The v1.0 Landau step is `LemmaB3`, part of `brs_lemma36_landau` |

## Lettered statements of §1

| Statement | Lean | Status |
|---|---|---|
| Conjecture U | `CondU`; `condU_iff_carriedBy`, `condU_iff_Xi_sq` (ZeroSupport) | stated (definition); (U) ⇔ every admissible `μ` is carried by `Z_ζ` ⇔ `∫ Ξ² dμ = 0` for every admissible pair, proved from [`zero_support_rigidity`, `logic_b`] |
| Conjecture S and its equivalences | `CondS`; `conjS_equivalences` (Main) | stated; the two equivalences proved from ledger axioms [`duality_no_gap`, `floor_bound`] |
| Logic of §1.2 | `logic_display` (Main) | proved from ledger axioms [`explicit_formula`, `logic_b`, `duality_no_gap`, `floor_bound`] |
| Theorem A | `theoremA` (Main) | proved from ledger axioms [`duality_no_gap`, `floor_bound`, `weak_magic_functions`]; "discrete set" is formalised as closed discrete (`DiscreteSet`) |
| Theorem B(a) — new | `theoremB_a` (Main) | proved from ledger axioms [`zero_support_rigidity`, `logic_b`] |
| Theorem B(b) — countable `E` new | `theoremB_b` (Main; `theoremB_b_countable`, CountableExtras) | proved from ledger axioms [`brs_countable_meanvalue`, `explicit_formula`, `riemannZeta_neg_of_mem_Ioo`]; finite `E` ("this holds whenever `E` is finite"): `theoremB'` (the v1.0 Theorem B, unchanged) from [`brs_lemma36_landau`, `explicit_formula`, `riemannZeta_neg_of_mem_Ioo`], and `theoremB_finite_of_countable` from [`brs_countable_meanvalue`, `explicit_formula`, `riemannZeta_neg_of_mem_Ioo`] |
| Corollary (magic-function principle) | first sentence: `corollary_magic_a` (Main); second sentence, finitely many zeros: `corollary_magic` (Main, unchanged) | proved from ledger axioms: [`zero_support_rigidity`, `logic_b`]; [as `theoremB'`]. The countable case under the condition of Corollary 3.9(b) is not formalised (see row 22) |
| Theorem C | `theoremC` (Main) | v1.2 statement (`κ* ≤ κ*_OPS ≤ 1.4291572·10^{-1060}`, `q_min ≥ 1 − 8.98·10^{-1060}`, `e^{−2πκ*_OPS} ≥ 1 − 8.98·10^{-1060}`; `κ* ≥ −2.7112·10^{-3}`): proved from ledger axioms [`cert_exact_cone`, `cert_finiteJ`, `xi_decay`, `cert_lowerbound`, `floor_bound`] |
| Theorem D | `theoremD_nonstrict'` (Main; (Mg) non-strict, v1.1); `theoremD'` (Main; strict (Mg), v1.0, unchanged) | proved from ledger axioms [as Theorem 4.8, row 31] |

## Coverage

Primary status of the 55 numbered statements of v1.2 (a statement with an axiomatised part and proved parts is
counted under its main claim, as in the tables):

| Status | Count | Statements |
|---|---|---|
| proved (Mathlib only) | 7 | 2.1, 2.4, 2.5, 2.11, 2.13, 4.9 (parts 1–2), A.2 |
| proved from ledger axioms | 22 | 2.7, 2.8, 2.9, 2.10, 2.12, 3.5, 3.6, 3.8, 3.9, 4.4, 4.5, 4.8, 4.10, 4.11, 5.1, 5.2, 5.3, 5.4, 5.5, 5.10, 5.11, 6.1 (implication) |
| ledger axiom (certified or cited input itself) | 8 | 2.3, 3.4, 3.7, 4.7, 5.6, 5.7, 5.9, B.4 |
| not formalised | 18 | 2.2, 2.6, 3.1, 3.2, 3.3, 3.10, 4.1, 4.2, 4.3, 4.6, 5.8, 5.12, A.1, A.3, A.4, B.1, B.2, B.3 |

* Formalised (any status but "not formalised"): **37 / 55 = 67 %**.
* Proved in Lean (Mathlib only, or from ledger axioms): **29 / 55 = 53 %**.
* Of these, proved from Mathlib alone: **7 / 55 = 13 %**.
* Excluding the five items without a mathematical claim of their own (Remarks 3.10, 4.3, 5.12, A.1 and the
  uncertified Observation 5.8), the formalised share is **37 / 50 = 74 %**.
* All lettered headline items of §1 are stated, and all theorems among them are proved from the ledger,
  except one case of the Corollary: countably many extra real zeros under the condition of Corollary 3.9(b)
  (not formalised; it needs Lemma 2.6).

Theorem 3.6 is counted as "proved from ledger axioms" although its analytic core, `ν = ν_ζ`, is the axiom
`zero_support_rigidity`: the rest of its statement (RH and `μ = μ_ζ`) is proved. The not-formalised statements
are (i) analytic lemmas used only inside axiomatised steps (2.2, 2.6), (ii) the soft-analysis section on
homogeneous directions (3.1–3.3), which no headline result uses, (iii) the special-function and Bessel
analysis used only inside the certificates (4.1, 4.2, 4.6, A.3, A.4), (iv) the modular analysis inside the
mean-value step and the Landau step (B.1–B.3), and (v) remarks and the uncertified observation.
