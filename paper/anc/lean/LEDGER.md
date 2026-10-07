# The axiom ledger

Every unproved input of the formalisation is an `axiom` in `PositivityRigidity/Ledger.lean`, and nowhere
else (`grep -rn '^axiom' PositivityRigidity/` lists exactly the 22 entries below; `scripts/audit.sh` checks
this, and the count in the table below). The docstring of each axiom in `Ledger.lean` repeats the
information of this table. Statement numbers are those of v1.2 of the paper (`paper/build/main.pdf`,
55 numbered statements); where a statement was renumbered since v1.0, the v1.0 number is also given. v1.2
(the exact members of the zero-killing family certified in the cone, without a cushion) adds Proposition 5.7;
its changes to the ledger are listed below.

**Grouping.**

| Category | Number | Axioms |
|---|---|---|
| Classical theorems (literature) | 3 | `explicit_formula`, `riemannZeta_neg_of_mem_Ioo`, `xi_decay` |
| Analytic steps proved in the paper, not yet formalised | 10 | `duality_no_gap`, `duality_gaussian`, `floor_bound`, `logic_b`, `weak_magic_functions`, `brs_lemma36_landau` (also carries the classical existence of the BRS basis), `brs_countable_meanvalue` (v1.1; likewise), `zero_support_rigidity` (v1.1), `robust_compactness`, `Zinf_lower_bound` |
| Computer-assisted certificates (§5) | 9 | `cert_exact_cone` (v1.2), `cert_kappaOPS`, `cert_lowheight`, `cert_lowerbound`, `cert_Qsqrt5_dual`, `cert_Qsqrt5_pair`, `cert_Qsqrtm3_dual`, `cert_Qsqrtm3_pair`, `cert_finiteJ` |
| **Total** | **22** | |

Changes in v1.2 (23 → 22 axioms: one added, two removed; no statement of another axiom changed):
* `cert_exact_cone` (Proposition 5.7, exact members in the cone, parts (b) and (c); `cone/cert_exact.py` with
  `cone/conelib.py`, Arb ball arithmetic, logs `cone/logs/W_J{J}_x1.log` and `cone/logs/W_J{J}_x2.log`): for each row of Table 1,
  `J = 10, 60, 61, 110, 111` (`exactMembers`, `CertDefs.lean`), the exact member `F_J = Ξ² P_J(t²)` of
  Proposition 4.5 (`Ffam J`) has `F̂_J ≥ 0` on `[0, ∞)`, `𝒜(F_J) ≤ A_J` and `∫ F_J ≥ I_J`. With the evenness of
  `F̂_J` (`FT_neg_of_even`), `F_J ∈ 𝒯` (`Ffam_mem_TestClass`, from `xi_decay`) and `F_J ≥ Ξ²` (`Ffam_ge_Xi_sq`,
  from the positive coefficients of Proposition 5.6, `cert_finiteJ`), all proved in Lean, `F_J ∈ 𝒞_OPS ⊆ 𝒞`
  without a cushion (`prop_exact_cone`), and Lean derives Theorem 5.1 (`κ* ≤ κ*_OPS ≤ 1.4291572·10^{-1060}`,
  `thm_5_1`), Corollary 5.2 (`q_min ≥ 1 − 8.98·10^{-1060}`, and `e^{−2πκ*_OPS} ≥ 1 − 8.98·10^{-1060}`, `cor_5_2`) and
  Corollary 5.3 (`∫ Ξ² dμ ≤ 3.99·10^{-1060}`, `near_rigidity`).
* `cert_kappa_ladder` (v1.1's Theorem 5.1 and Table 1: the cushioned representatives `Ξ²(H + ε e^{−πt²})`,
  `J = 20, …, 100`) is **removed**: in v1.2, Table 1 lists the exact members, and the cushioned certificates
  (ancillary directory `kappa/`) are only an unnumbered cross-check in the text. The definitions `Frep`,
  `LadderRow`, `kappaLadder`, `kappa100` and `Hpoly` and the lemmas about them are removed with it.
* `cert_near_rigidity` (v1.1, the `J = 100` certificate of Corollary 5.3) is **removed**: Corollary 5.3 now uses
  `F₁₁₁`.

Changes in v1.1 (20 → 23 axioms; none removed, no statement of an existing axiom changed; docstrings
renumbered):
* `zero_support_rigidity` (Theorem 3.6, zero-side support; due to Astra (OpenAI), contributed during an
  independent review of an earlier version of the paper, and independently verified):
  `∀ p ∈ 𝒦, μ carried by Z_ζ ∪ {0} → ν = ν_ζ`.  RH and `μ = μ_ζ` are then proved in Lean from Theorem 2.9(b)
  (`logic_b`).  It gives Theorem B(a), Proposition 3.5 without its hypothesis on `ν`, Corollary 3.9(a),
  Theorem 4.8 with the non-strict (Mg), Remark 4.10, Conjecture 6.1's implication and Corollary 4.11.
* `brs_countable_meanvalue` (Lemma 3.7 for countable `E` and Lemmas B.3–B.4, the mean-value step; due to
  Astra (OpenAI), independently verified): `∃ B α, IsBRSBasis B ∧ Lemma36Count B α ∧ MeanValueStep α`, mirroring
  `brs_lemma36_landau`.  It gives Theorem 3.8 for countable `E` under (3.5) and Theorem B(b), and, for finite
  `E`, the statement of `theoremB'` without the Landau step (`theoremB_finite_of_countable`).
  `brs_lemma36_landau` (the v1.0 route through the Landau step, which v1.1 replaces by Lemmas B.3–B.4) is
  kept so that the v1.0 headline theorems keep their axiom sets.
* `cert_near_rigidity` (Corollary 5.3; `kappa/check_H_nonneg.py`, exact arithmetic): the `J = 100`
  certificate has `P` with non-negative coefficients (so `F_rep ≥ Ξ²`, proved in Lean) and
  `𝒜(F_rep) ≤ 3.21·10^{-906}`. (Removed in v1.2, see above.)

Changes before v1.1 (21 → 20 axioms):
* `support_uniqueness` (Proposition 3.5, signed form) was retired: it is now the theorem
  `support_uniqueness_thm` (`BRSValues.lean`), proved — for every basis with the BRS properties — from
  `explicit_formula` and `riemannZeta_neg_of_mem_Ioo`.
* After an independent audit of the ledger, `brs_basis_exists` (existence of the
  BRS basis), the definition `brs := Classical.choose brs_basis_exists` and `structure_landau`
  (`∃ α, Lemma36 brs α ∧ LemmaB3 α`) were replaced by the single joint statement `brs_lemma36_landau :
  ∃ B α, IsBRSBasis B ∧ Lemma36 B α ∧ LemmaB3 α`.  The old pair was consistent, but its truth relied on
  `brs` being the BRS basis, and the claimed uniqueness ("[BRS, Corollary 1.1]") does not hold in the class
  used: Corollary 1.1 needs `H₁`, which the decay `(1 + |z|)^{-2}` of `𝒯` does not give (`1/(1 + z²) ∈ 𝒯`).
  Now nothing depends on identifying a witness: Proposition 3.5 and Theorem 3.8 (v1.0: 3.7) are proved for
  every `(B, α)` with the three properties, and Theorem B obtains one such pair from the axiom.

**Hygiene.**

* *No posited objects.* Every axiom is a proposition about objects defined from Mathlib in `Basic.lean`,
  `BRSDefs.lean`, `FamilyDefs.lean`, `CertDefs.lean` and `ExtrasDefs.lean`: `riemannZeta`,
  `completedRiemannZeta₀` (for `ξ`, `Ξ`), `Complex.digamma = Γ'/Γ`, Mathlib's Fourier transform `𝓕`,
  `ArithmeticFunction.vonMangoldt`, measures. The v1.2 certificate `cert_exact_cone` is about the exact members
  `Ffam J` themselves (defined from the moments of `Ξ²` and the inverse of the Hermite matrix `M_J`, which
  `cert_finiteJ` certifies non-singular for these `J`, so `Ffam J` is not a junk value), not about existentially
  quantified representatives.  The BRS basis and the coefficient function `α`
  of Lemma 3.7 and of the Landau step / mean-value step are not posited: they are only asserted to exist
  jointly (`brs_lemma36_landau`, `brs_countable_meanvalue`), every theorem using them holds for every
  witness, and no uniqueness is claimed.
* *No junk values.* The slacks are `EReal` infima, so they are never junk; the pairing hypotheses of the
  axioms only involve test functions in `𝒯` (where every integral converges) or finite sums; the vanishing
  `∫ F* dμ = 0` of Theorem 2.12(a) is stated with lower integrals of non-negative functions.  In the v1.1
  axioms, the countable sums are either `Summable` by hypothesis (the pairings with the BRS functions, the
  series `c_N`) or sums of non-negative terms in `[0, ∞]` (the summability condition (3.5)/(B.7):
  `partialMass`, `SqrtSmall`, `WeightedCond`, `CumulativeCond`).
* *Faithfulness checks of the definitions the axioms use* (all proved from Mathlib alone, `Sanity.lean`,
  `Faithful.lean`): `𝒯`, `𝒞`, `𝒞_OPS`, `𝒞 ∩ 𝒢` are non-empty (the Gaussian); `𝒢 ⊂ 𝒯_δ` for every `δ`
  (`Gset_inTδ`, as Definition 2.1 claims); Lean's real-valued `Arch F` equals the paper's complex expression
  `F(i/2) + F(−i/2) + ∫ F Ω_∞` for `F ∈ 𝒯` (`TestClass.Arch_eq_paper`, via Schwarz reflection); admissible
  pairs are automatically Radon (`Admissible.isLocallyFinite`); `xiR` is Riemann's `ξ` (`xiR_eq`); Mathlib's
  `RiemannHypothesis` is "all zeros in `0 < Re s < 1` are on the line" (`RH_iff_critical`).
* *Cross-check of the main classical axiom.* `EFCheck.lean` proves the conclusion of `explicit_formula`,
  verbatim, for every `F = paperFT k` with `k ∈ C_c²` even and real — a Paley–Wiener subclass of `𝒯`
  (`paperFT_mem_TestClass`) — from Zeta23's hypothesis-free theorem `Zeta23.WeilEF.EF_lit_zetaZeroConfig`,
  using **no** ledger axiom (the file does not import the ledger). This confirms the normalisation of the
  axiom (`t_ρ`, multiplicities, `ξ_n`, `1/π`, `Ω_∞`, the real part in `Arch`).  An independent audit of
  the ledger also checked the axiom numerically on `F = 1/(1+t²)`, which is not in that subclass: both sides
  agree to `1.5·10^{-16}`.
* *Consistency.* Each axiom is a theorem of the cited literature or of the paper, or a certified
  computation, or is weaker than one; so the axioms hold simultaneously in the intended model (the BRS
  basis and the coefficients of (3.1) witness `brs_lemma36_landau`). Each axiom's hypotheses were checked to be
  satisfiable/non-vacuous where an axiom of the form `(∀ F ∈ X, …) → …` could otherwise become too strong:
  `Cone`, `Cone ∩ Gset` are non-empty (`gauss`), and `Gset` is exactly the paper's `𝒢`.
* *v1.1 sanity checks.* `zero_support_rigidity_sanity`: under RH, `p_ζ` satisfies the hypothesis of
  `zero_support_rigidity` and its conclusion holds without the axiom.  `weightedCond_of_finite`,
  `cumulativeCond_of_weightedCond`: the summability condition (3.5) holds for finite `E` and its weighted
  form implies the cumulative form used in `MeanValueStep` (Mathlib only).  `hypMg0_of_hypMg`,
  `conjFamily0_of_conjFamily`: the v1.1 hypotheses are weaker than the v1.0 ones.
* *v1.2 sanity checks.* `Ffam_ge_Xi_sq`: non-negative coefficients of `P_J` give `F_J ≥ Ξ²` (Mathlib only; the
  non-vacuity check `near_rigidity_certificate_meaning`, which in v1.1 was the analogous statement for `F_rep`);
  `FT_neg_of_even`: the transform of an even function is even (Mathlib only); `Ffam_mem_Cone_of`,
  `Ffam_mem_ConeOPS_of`: the cone memberships from the certified facts (`xi_decay` only, for `F_J ∈ 𝒯`). The
  bounds `A_J/I_J ≤ κ_J` and `2π·κ₁₁₁ ≤ 8.9796596·10^{-1060}` are checked in Lean.
* `#print axioms` for the headline theorems is in `axioms.log`: only ledger axioms and
  `propext`, `Classical.choice`, `Quot.sound` occur. No `sorry`, no `native_decide` anywhere.  CI
  (`scripts/audit.sh`) re-checks all of this on every push.

Log lines are quoted with whitespace normalised (the v1.2 lines from `cone/logs/` verbatim, double spaces
included); `±` in a docstring stands for the logs' `+/-` (a Lean docstring cannot contain `/-`). All SHA-256 values are those of `paper/anc/SHA256SUMS`;
`python3 scripts/check_ledger_hashes.py` re-checks every cited hash against that file.

## Classical inputs

| Axiom | Paper statement | Source | Faithful / weaker | Notes |
|---|---|---|---|---|
| `explicit_formula` | Lemma 2.3 (explicit formula on `𝒯`): for `F ∈ 𝒯`, `𝒜(F) = Σ_ρ m(ρ) F(t_ρ) + (1/π) Σ_n Λ(n) n^{-1/2} F̂(ξ_n)`, both series absolutely convergent, no hypothesis on the zeros | A. Weil, *Sur les « formules explicites » de la théorie des nombres premiers* (1952); A. Bondarenko, D. Radchenko, K. Seip, *Fourier interpolation with zeros of zeta and L-functions*, Constr. Approx. (2023), formula (1.1) (class contains `𝒯`, proof of Lemma 2.3); Guinand (1948) | Faithful | Zeros = zeros in `0 < Re s < 1`, multiplicity = `analyticOrderNatAt`; `Summable` over the subtype of zeros (absolute convergence in `ℂ`). Verified on the Paley–Wiener subclass by `EFCheck.lean` (Zeta23). |
| `riemannZeta_neg_of_mem_Ioo` | `ζ(σ) < 0` for `0 < σ < 1` (used in §3.1, Theorem 3.8 via `Ξ(0) > 0`, and Definition 3.4 implicitly: no real zeros in the critical strip) | `(1 − 2^{1−σ}) ζ(σ) = Σ (−1)^{n−1} n^{−σ} > 0`, NIST DLMF (25.2.3), cited in §3.1 | Faithful | `riemannZeta_half_neg` is derived from it (`Zeta.lean`). Not in Mathlib or Zeta23. |
| `xi_decay` | Bound (4.1): `|Ξ(t)| ≤ C_b (1+|Re t|)^3 e^{−π|Re t|/4}` on `|Im t| ≤ b`, `b ∈ (0,1]` | Stirling + convexity bound, E. C. Titchmarsh, *The theory of the Riemann zeta-function*, 2nd ed. (1986), as cited at (4.1) | Faithful | `Xi` is Riemann's `Ξ` (`xiR_eq`). Used for integrability of `t^{2k}Ξ²` (Proposition 4.5, Theorem D, Conjecture 6.1) and for `Ξ² ∈ 𝒯`. |

## Analytic steps proved in the paper

| Axiom | Paper statement | Source (paper proof) | Faithful / weaker | Notes |
|---|---|---|---|---|
| `duality_no_gap` | Theorem 2.7(a), (ii) ⇒ (i), for `𝒜 + λ∫` (the remark after the proof extends it to every `λ`) | Appendix B.1.1 (Carathéodory in finite-dimensional subspaces, Lemma 2.6, Helly selection) | Faithful | Used at `λ = 0`, `λ = −κ*` (Proposition 2.8), `λ = log q/2π` (Proposition 2.10). Its hypothesis holds for every `λ ≥ 1.3231` (`duality_no_gap_hyp_of_ge`, from `floor_bound`), so it does produce pairs (`exists_admissible_shift`); for `λ` very negative the hypothesis fails at the Gaussian. |
| `duality_gaussian` | Theorem 2.7(a), (iii) ⇒ (ii) | Appendix B.1.1 (Riemann sums of Gaussian convolutions lie in `𝒢`) | Faithful | `𝒞 ∩ 𝒢 ∋ gauss`; `Gset` is the paper's `𝒢` and `𝒢 ⊂ 𝒯_δ` is proved. Used only for Theorem 2.7(a)(iii) itself. |
| `floor_bound` | Proposition 2.8, the inequality in its proof: `𝒜(F) ≥ −4ξ₂cosh(πξ₂) + Ω_∞(0) = −1.32304… ≥ −1.3231` for `F ∈ 𝒞`, `∫F = 1` | Proof of Proposition 2.8 (Lemma 2.2(b), (2.2)) | Faithful | Gives finiteness of `κ*` (hence of `q_min`). |
| `logic_b` | Theorem 2.9(b): `(μ, ν_ζ) ∈ 𝒦` ⇒ RH ∧ `μ = μ_ζ` | Appendix B.1.2 (Gaussians `F_u`, Bohr mean, uniqueness on `𝒢`) | Faithful | `RiemannHypothesis` is Mathlib's. |
| `weak_magic_functions` | Theorem 2.12(a) (existence when `κ* = 0`; evenness, `F̂* ∈ L¹`, `∫|F̂*|cosh(πξ) < ∞`, analytic extension to `|Im t| < 1/2`, `F̂* ≥ 0` on `|ξ| ≥ ξ₂`, `∫ F* log(2+|t|) < ∞`, `∫F* dμ = 0 = ∫F̂* dν`) | Proof of Theorem 2.12(a) ((2.4), Prokhorov, Vitali, Fatou) | Faithful | Vanishing stated with lower integrals of non-negative integrands. |
| `brs_lemma36_landau` | Definition 3.4 (the BRS basis, existence) **jointly with** Lemma 3.7 for finite `E` (formula (3.4); v1.0 Lemma 3.6) and the Landau step (v1.0 Lemma B.3): `∃ B α, IsBRSBasis B ∧ Lemma36 B α ∧ LemmaB3 α` | BRS (2023), Theorem 1.1 and §§4.2–4.3 (existence, (3.2), decay); Appendix B.1.5 (Lemma 3.7: testing on `U_m`, (3.2), Möbius inversion over squares); v1.0 Appendix B (Lemmas B.1, B.2, Landau's theorem [Montgomery–Vaughan 2007, Thm 1.7]); v1.1 replaces the Landau step by Lemmas B.3–B.4 (see `brs_countable_meanvalue`) | **Weaker** than the paper (which names `B` and `α`): joint existence only | Witness: BRS's basis with the Fourier coefficients of (3.1). BRS state rapid decay in vertical strips with constants depending on `y`; uniform decay on closed strips (so that Re/Im parts lie in `𝒯`) is the paper's reading of [BRS §4.3]. No uniqueness claimed (Corollary 1.1 needs `H₁`). Used by the v1.0 headlines `theoremB'`, `corollary_magic`, `theoremD'` (unchanged axiom sets); the same finite statement is derived from `brs_countable_meanvalue` without it. |
| `brs_countable_meanvalue` (v1.1) | Definition 3.4 **jointly with** Lemma 3.7 for countable symmetric `E ⊆ ℝ \ Z_ζ` (`Lemma36Count`: if the identity holds on the BRS functions with absolutely convergent integrals, the series `c_N(E)` converge absolutely and (3.4) holds) and Lemmas B.3–B.4 (`MeanValueStep`: countable `E₊ ⊂ [0,∞)`, real `a_e` with (B.7) in its cumulative form `Σ_{0<e≤T} |a_e||ζ(1/2+ie)| = o(T^{1/2})`, `a_0 ≥ 0`, `c_N ≥ 0` for `N ≡ 2 (3)` ⇒ `ϱ̃_e = 0`): `∃ B α, IsBRSBasis B ∧ Lemma36Count B α ∧ MeanValueStep α` | Appendix B.1.5 (Lemma 3.7), Appendix B.1.6 (Lemma B.3: Mellin identity [BRS (3.17)], polynomial Schwartz-seminorm bounds [Radchenko–Viazovska 2019, §6], the word `ST²ST²S`, aggregate bounds from the argument margin; Lemma B.4: Cesàro mean and mean square of the almost-periodic `Q`). The extension to countable `E` and the mean-value step are due to Astra (OpenAI), contributed during an independent review of an earlier version of the paper, and independently verified (Paper I, §3.3) | **Weaker** than the paper: joint existence of `B`, `α`; absolute convergence of the `c_N` (Lemma B.3(a)) assumed in (ii); the "Moreover" clauses of Lemma 3.7 and the second assertion of Lemma B.4 omitted | (B.7) is used in the paper's general (cumulative) form; the weighted form implies it (`cumulativeCond_of_weightedCond`, Mathlib only). No assertion without (B.7), for `ν` off `ℳ`, or for diffuse extra mass. Restricted to finite `E` it gives Theorem 3.8 without the Landau step. |
| `zero_support_rigidity` (v1.1) | Theorem 3.6 (zero-side support), first conclusion, with the origin variant: `∀ p ∈ 𝒦, μ carried by Z_ζ ∪ {0} → ν = ν_ζ` | Appendix B.1.4 (lattice functional `L(f) = ∫√x Σ_k f(kx) dν^♯`, continuous on Schwartz space by Lemma 2.6; the identities of the `U_m` [BRS §§3.4.1, 4.2–4.4] and square-divisor Möbius inversion; Radchenko–Viazovska interpolation in Schwartz space [RV 2019, Thm 1, §6]; regularisations of `g(t) = sin²(πt)/(π²(t²−1))`; divisor Möbius inversion; origin: `ζ(1/2) < 0`, `M_{g+h}(1/2) < 0`). Due to Astra (OpenAI), contributed during an independent review of an earlier version of the paper, and independently verified (Paper I, Theorem 3.6) | **Faithful** (the first conclusion; "supp μ ⊆ Z_ζ ∪ {0}" is `μ((Z_ζ ∪ {0})ᶜ) = 0`, the set being closed, `isClosed_Zzeta`) | No hypothesis on `ν` beyond admissibility. RH and `μ = μ_ζ` are not part of the axiom: `zero_support_theorem` derives them from `logic_b`, as the paper does. Sanity: `zero_support_rigidity_sanity`. |
| `robust_compactness` | Lemma 4.7, plus two facts from its proof (bound for `H_∞`; `F̂_J → F̂_∞` pointwise along the subsequence) | Appendix B.2.3 (Montel, (4.1), dominated convergence, Corollary 4.4) | Faithful (lemma + facts proved in its proof) | `F_∞ ∈ 𝒞` includes `F_∞ ∈ 𝒯` (closed strip of half-width `1/2 + δ'`, `δ' < δ`). |
| `Zinf_lower_bound` | Appendix B.2.3, "Equivalent forms of (Z∞)", (i) ⇒ (iii): under (N), (G_a), (Z∞), `liminf_J min_{|t|≤T} H_J(t) > 0` | Appendix B.2.3 (IVT with `H_J(0) = 1`, Montel, Hurwitz) | Faithful (one direction) | Only used by Theorem D (both forms); not needed for Remark 4.10(a) or Conjecture 6.1's implication. |

## Computer-assisted certificates

All scripts need Python ≥ 3.10 with `python-flint==0.9.0`, `mpmath==1.3.0` (see `paper/anc/README.md`).

| Axiom | Paper statement | Script, parameter file (SHA-256), decisive log line | Faithful / weaker |
|---|---|---|---|
| `cert_exact_cone` (v1.2) | Proposition 5.7 (exact members in the cone), parts (b) and (c): for each row of Table 1 (`exactMembers`: `J = 10, 60, 61, 110, 111`), the exact member `F_J = Ξ² P_J(t²)` of Proposition 4.5 has `F̂_J ≥ 0` on `[0, ∞)`, `𝒜(F_J) ≤ A_J` and `∫ F_J ≥ I_J`; e.g. `A₁₁₁ = 3.98510732132·10^{-1060}`, `I₁₁₁ = 2.788431830818955391538`. So `F_J ∈ 𝒞_OPS ⊆ 𝒞` without a cushion (with `F̂_J` even, `F_J ∈ 𝒯` and `F_J ≥ Ξ²` proved in Lean) | `cone/cert_exact.py` (sha256 58b4afeabe96a27070b1b24dde4171d598b09377adcf4c20a6eaced40803e46b) with `cone/conelib.py` (sha256 cc1534c4f34b72579f3eedd2df2adb8ce649d6ddbdacbd5a1090143031db12ee) and the validated `K₀`, `K₁` of `lib/k01_trapezoid.py` (sha256 864867203d52f421ade04725be5f78f8be4dcbf8569d355c98a3d43bf87408a1), Arb ball arithmetic, inputs `exact/out/P10_ball.txt` (sha256 4e55d361d6d2c05f15565bd3c94d56b9f5e0715acecda9fd362410181bdc48d3), `exact/out/P60_ball.txt` (sha256 fdfbfe57bfe9945f640291b6f1e1b7e74e4d5afb04278961d5737f26db6cda4b), `exact/out/P61_ball.txt` (sha256 8cc7b2b9a66f643e8e40d84fd4ffd6970401342aeab87b716ec169bc91ca3dd4), `exact/out/P110_ball.txt` (sha256 7c8999567bc77cd1c6fb5a9e816bb0b4f212b971f26dd0f3bda3237ff51c117a), `exact/out/P111_ball.txt` (sha256 25669a321f71ddef789247cd0adc0fd129c5d70f293e488bc4dab8c3f708b3f1). (b): logs `cone/logs/W_J{J}_x1.log`, `W_J: Fhat_J >= 0 on [x = 1, oo), with exact double zeros at the 111 nodes and Fhat_J > 0 elsewhere: True` (likewise with `10`, `60`, `61`, `110` nodes; all five lines are quoted in `Ledger.lean`). (c): logs `cone/logs/W_J{J}_x2.log`; at `J = 111`: `W_J: Fhat_J >= 0 on [x = 2, oo), with exact double zeros at the 111 nodes and Fhat_J > 0 elsewhere: True`, `A(F_J) in [3.98510732131e-1060, 3.98510732132e-1060]`, `int F_J = Fhat_J(0) = [2.788431830818955391538863 +/- 4.24e-25]`, `kappa_J^exact = A(F_J)/int F_J in [1.429157161e-1060, 1.429157162e-1060]  =>  kappa* <= 1.4291572e-1060  (F_J in C, Def 2.4)`, `near-rigidity: every admissible pair (mu, nu) has int Xi^2 dmu <= int F_J dmu <= A(F_J) <= 3.9851074e-1060  (Lemma 2.5, F_J >= Xi^2, Fhat_J >= 0 on supp nu)`; at `J = 110`: `kappa_J^exact = A(F_J)/int F_J in [2.001011429e-1042, 2.001011430e-1042]  =>  kappa* <= 2.0010115e-1042  (F_J in C, Def 2.4)` (the `A(F_J)` and `int F_J` lines of every `J` are quoted in `Ledger.lean`). Analytic inputs: Proposition 4.5 (exact double zeros at the nodes; `deriv_FT_Ffam_pp` in Lean), Lemma 2.3 and Corollary 4.4 (`𝒜(F_J)` as a prime-power tail sum; `Arch_Ffam_tail` in Lean), Proposition 4.2, Lemma 4.6, validated `K₀`, `K₁` | **Weaker** (only the one-sided bounds used; the order-two zeros and `F̂_J > 0` off the nodes are not stated). `F_J ∈ 𝒯`, `F_J ≥ Ξ²` and the evenness of `F̂_J` are proved in Lean; `A_J/I_J ≤ κ_J` is checked in Lean |
| `cert_kappaOPS` | Proposition 5.4 (v1.0: 5.3): some `F ∈ 𝒞_OPS` with `∫F > 0`, `𝒜(F) ≤ 9.9461827001452550725·10^{-41} ∫F` | `general/verify_general.py` with `general/params/zeta_K128_s13.json` (sha256 0976a6711193adc0f02a532931974b8ef4912337f79e39f59aa21445879a4df2): `SLACK : kappa*_OPS (and kappa*) of the data <= 9.9461827001452550725e-41`, `RESULT : CERTIFIED` | **Weaker** (existence). Analytic input of the tail: Lemma A.4 |
| `cert_lowheight` | Proposition 5.5 (v1.0: 5.4): `F_80 ∈ 𝒞_OPS`, `𝒜(F_80) ≤ 7.72525424595·10^{-25}`, `∫F_80 ≥ 0.9999999999999999444`, and the window lower bounds of Table 2 | `general/verify_general.py` with `general/params/zeta_K80_s12_F80.json` (sha256 c0f3afc2d3367ebdadd0897a6e2f15fc5ae8a7caf8b7c6879b504119a845eee6): `A(F_rep) = [7.725254245948889853868706e-25 +/- 4.30e-50]`; `general/verify_windows.py` with `general/params/F80_windows.json` (sha256 af90186bb2a9126187e3dd4b2358aec7ca4e69c40fbfef7a6daafdabe9579b24): `gap{1..5}_eta0.1 … PROVED`, `win… PROVED`, `atom n = 2.5 F^(xi_n) = [0.0015866025 +/- 3.99e-13]`, `atom n = 6 F^(xi_n) = [3.8125495e-7 +/- 3.84e-15]`, `RESULT : CERTIFIED` | **Weaker** (existence; Table 2's inward-rounded windows). Analytic inputs: Lemma A.2 (window bounds, after a Möbius map; proved in Lean, `PosCert.lean`) and Lemma A.4 (digamma tail) |
| `cert_lowerbound` | Proposition 5.10 (v1.0: 5.8), with Lemma 5.9 (v1.0: 5.7): an admissible pair for `𝒜_q`, `log q = 0.02`, with `μ ≥ 4.71949·10^{-4} dt` | `general/verify_pair.py` with `general/params/pair_zeta_logq002_X10.json` (sha256 d28b347d9807e6934a55bb326f20e09318c2aab4851595b914788f5c708888f6): `MU FLOOR : mu(t) >= 0.000471949 for all real t`, `GAP : admissible at gap xi_2 (prime measure on [2, oo)): True`, `RESULT : CERTIFIED`; admissibility of the Herglotz form is Lemma 5.9 [paper] | **Weaker** than certificate + Lemma 5.9 (pair only asserted to exist) |
| `cert_Qsqrt5_dual` | Proposition 5.11(a) (v1.0: 5.9(a)), dual side: `F ∈ 𝒞_OPS`, `𝒜_{Γ_ℝ²,1}(F) ≤ −0.25566705789831547610 ∫F` | `general/verify_general.py` with `general/params/gammaR2_K80_s7.json` (sha256 79936770a00991a3c4b24ac614f8405686fdf499d6eb0040dd9976ae026a71ee): `SLACK : … <= -0.25566705789831547610` | **Weaker** (existence). Lemma A.4 for the tail |
| `cert_Qsqrt5_pair` | Proposition 5.11(a), primal side (with Lemma 5.9): pair for `𝒜_{Γ_ℝ²,q₀}`, `log q₀ = 1.6093347792651136`, prime measure on `[ξ_{4.049150}, ∞)`, `μ ≥ 6.59497·10^{-9}` | `general/verify_pair.py` with `general/params/pair_gammaR2_X240.json` (sha256 3b9f85c84efcf36f0e753e01edd442bfc3d6a1a2ead2377124b015ea2b7dfb1d): `nu~ support : supp nu~ in [x0, oo) with x0 >= 4.049150`, `MU FLOOR : mu(t) >= 6.59497e-9 for all real t` | **Weaker** (existence) |
| `cert_Qsqrtm3_dual` | Proposition 5.11(b) (v1.0: 5.9(b)), dual side: `𝒜_{Γ_ℂ,1}(F) ≤ −0.17385102660887763683 ∫F` | `general/verify_general.py` with `general/params/gammaC_K64_s9.json` (sha256 e330d8b743bd835920ecaad507a195773f4c858181d97bafb9d3eca1c296021a): `SLACK : … <= -0.17385102660887763683` | **Weaker** (existence). Lemma A.4 for the tail |
| `cert_Qsqrtm3_pair` | Proposition 5.11(b), primal side (with Lemma 5.9): `log q₀ = 1.0976698108720329`, prime measure on `[ξ_{3.011664}, ∞)`, `μ ≥ 6.67226·10^{-8}` | `general/verify_pair.py` with `general/params/pair_gammaC_X40.json` (sha256 f32152ae73a8e202fafd9bd56097dc0b98d68741392ee8149ee3d9262828eeae): `nu~ support : … x0 >= 3.011664`, `MU FLOOR : mu(t) >= 6.67226e-8 for all real t` | **Weaker** (existence) |
| `cert_finiteJ` | Proposition 5.6 (v1.0: 5.5): for `J ∈ {10, 60, 61, 110, 111}`, `M_J` non-singular and `0 < p_k ≤ 0.71636^{2k}/(2k)!` | `exact/verify_exact_member.py` (logs `exact/logs/NPOS_J*.log`: `(N) rigorous solve … (matrix certified non-singular): True`, `(POS) all … coefficients p_k certified > 0: True`, `a = max_k ((2k)! p_k)^(1/2k) <= 0.697078` at `J = 10`); `exact/check_coefficient_bound.py` (sha256 c267e87652e86cff504f537b9a2de7913ebc6ea2fa4f6a616995a47e7c0d366c), log `exact/logs/coefficient_bound.log`: `CERTIFIED: 0 < p_k <= 0.71636^(2k)/(2k)! for every k, at J = 60, 61, 110, 111: True` | Faithful |

The arithmetic that combines certificates (`log 3`, `log 5`, `π` bounds, `A_J/I_J ≤ κ_J` for the rows of Table 1,
`2π·κ₁₁₁ ≤ 8.9796596·10^{-1060}`, `π𝒜(F_80)/m ≤` Table 2, …) is done in Lean (`Certified.lean`, `ExactMember.lean`,
`Atoms.lean`), not taken from the scripts.
