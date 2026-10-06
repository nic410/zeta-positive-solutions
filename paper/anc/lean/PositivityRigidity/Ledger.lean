/-
# The axiom ledger

Every input of the formalisation that is not proved in Lean is an `axiom` in this file, and nowhere
else.  Each docstring names the paper statement that the axiom transcribes, its category, its source,
and whether the Lean statement is a faithful transcription or a weaker one.  `LEDGER.md` tabulates them.

Categories:
* **[classical]** a published theorem, cited by author, year and theorem number;
* **[certificate]** a computer-assisted statement of §5, cited by script, parameter file, SHA-256
  (from `paper/anc/SHA256SUMS`) and the decisive line of the shipped log;
* **[paper]** an analytic step proved in the paper (main text or Appendix B) and not yet formalised.

Hygiene.  No axiom posits an object: the BRS basis and the coefficient function `α` of Lemma 3.7 and the
Landau step are only asserted to exist (jointly, `brs_lemma36_landau`, and for the countable forms of v1.1,
`brs_countable_meanvalue`), and every theorem that uses them holds for every witness.
Every axiom is a statement about objects defined concretely from Mathlib (`riemannZeta`, `𝓕`,
`Complex.digamma`, measures) in `Basic.lean`, `BRSDefs.lean`, `FamilyDefs.lean`, `CertDefs.lean`,
`ExtrasDefs.lean`.

v1.1 (three axioms added; none removed, none changed in substance): `brs_countable_meanvalue`
(Lemma 3.7 for countable `E` and Lemmas B.3–B.4, for Theorem 3.8 / Theorem B(b)), `zero_support_rigidity`
(Theorem 3.6: zero-side support forces `ν = ν_ζ`) and `cert_near_rigidity` (Corollary 5.3's certificate:
`F_rep ≥ Ξ²` at `J = 100`).  Statement numbers are those of v1.1 of the paper; v1.0 numbers are given
where a statement was renumbered.
-/
import PositivityRigidity.Basic
import PositivityRigidity.BRSDefs
import PositivityRigidity.FamilyDefs
import PositivityRigidity.CertDefs
import PositivityRigidity.ExtrasDefs

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder

namespace PosRig

/-! ## Classical inputs -/

/-- **[classical] Lemma 2.3 (the explicit formula on `𝒯`).**  For every `F ∈ 𝒯`,
`𝒜(F) = Σ_ρ F(t_ρ) + (1/π) Σ_{n ≥ 2} Λ(n) n^{-1/2} F̂(ξ_n)`, `t_ρ = −i(ρ − 1/2)`, `ρ` running over the
non-trivial zeros with multiplicity; both series converge absolutely.  No hypothesis on the zeros.

Source: A. Weil, *Sur les « formules explicites » de la théorie des nombres premiers* (1952);
A. Bondarenko, D. Radchenko, K. Seip, *Fourier interpolation with zeros of zeta and L-functions*
(Constr. Approx. 2023), formula (1.1), for `f` analytic in `|Im z| < 1/2 + ε` with
`|f(z)| ≪ (1+|z|)^{-1-η}`, a class containing `𝒯` (proof of Lemma 2.3).  Guinand (1948).

Faithful.  (Zeta23 proves this identity for the Paley–Wiener subclass `F̂ ∈ C_c²`,
`Zeta23.WeilEF.EF_lit_zetaZeroConfig`; see README.md.) -/
axiom explicit_formula : ∀ F ∈ TestClass,
    Summable (fun ρ : NontrivialZeros => (mult ρ : ℂ) * F (tOf ρ)) ∧
    Summable (fun n : ℕ =>
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * FT F (xiOf n)) ∧
    ((Arch F : ℝ) : ℂ) = (∑' ρ : NontrivialZeros, (mult ρ : ℂ) * F (tOf ρ)) +
      (1 / Real.pi : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * FT F (xiOf n)

/-- **[classical] `ζ(σ) < 0` for `0 < σ < 1`.**  Used for `ζ(1/2) < 0` (so `0 ∉ Z_ζ`, §3.1, and
`Ξ(0) = −(1/8)Γ_ℝ(1/2)ζ(1/2) > 0` in the proof of Theorem 3.8), and for the absence of real zeros in the
critical strip (the BRS basis is indexed by the zeros with `Im ρ > 0`, Definition 3.4).

Source: `(1 − 2^{1−σ}) ζ(σ) = Σ_{n ≥ 1} (−1)^{n−1} n^{−σ} > 0` for `0 < σ < 1` (alternating series with
decreasing terms), NIST DLMF (25.2.3), cited in §3.1.  Faithful. -/
axiom riemannZeta_neg_of_mem_Ioo : ∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta (σ : ℂ) < 0

/-- **[classical] The bound (4.1) for `Ξ`.**  For every `b ∈ (0, 1]` there is `C_b` with
`|Ξ(t)| ≤ C_b (1 + |Re t|)³ e^{−π|Re t|/4}` on `|Im t| ≤ b`.

Source: Stirling's formula and the convexity bound for `ζ` (E. C. Titchmarsh, *The theory of the
Riemann zeta-function*, 2nd ed. 1986, §§4.12, 5.1), as cited at (4.1).  Faithful. -/
axiom xi_decay : ∀ b : ℝ, 0 < b → b ≤ 1 → ∃ C : ℝ, ∀ z : ℂ, |z.im| ≤ b →
    ‖Xi z‖ ≤ C * (1 + |z.re|) ^ 3 * Real.exp (-(Real.pi / 4) * |z.re|)

/-! ## Analytic steps proved in the paper (not yet formalised) -/

/-- **[paper] Theorem 2.7(a), (ii) ⇒ (i) (no duality gap), for `𝒜 + λ∫`.**  If
`𝒜(F) + λ∫F ≥ 0` for every `F ∈ 𝒞`, then `𝒜 + λ∫` has an admissible pair.

Source: Appendix B.1.1 (Carathéodory's theorem in finite-dimensional subspaces, the a priori bounds of
Lemma 2.6 and Helly's selection theorem); the remark after the proof of Theorem 2.7 states that the
proof applies verbatim to `𝒜 + λ∫` for every `λ ∈ ℝ`.  Faithful. -/
axiom duality_no_gap (lam : ℝ) :
    (∀ F ∈ Cone, 0 ≤ ArchShift lam F) → ∃ p : Pair, Admissible (ArchShift lam) xi2 p

/-- **[paper] Theorem 2.7(a), (iii) ⇒ (ii).**  If `𝒜 ≥ 0` on `𝒞 ∩ 𝒢`, then `𝒜 ≥ 0` on `𝒞`.

Source: Appendix B.1.1 (approximation of `F ∈ 𝒞` by Riemann sums of Gaussian convolutions, which lie in
`𝒢`).  Faithful. -/
axiom duality_gaussian : (∀ F ∈ Cone ∩ Gset, 0 ≤ Arch F) → ∀ F ∈ Cone, 0 ≤ Arch F

/-- **[paper] Proposition 2.8, the lower bound in its proof.**  For `F ∈ 𝒞` with `∫ F = 1`,
`𝒜(F) ≥ −4ξ₂ cosh(πξ₂) + Ω_∞(0) = −1.3230483… ≥ −1.3231`.

Source: proof of Proposition 2.8 (Lemma 2.2(b), `|F̂| ≤ 1`, and (2.2): `Ω_∞ ≥ Ω_∞(0)`).
Faithful (it is the inequality proved there). -/
axiom floor_bound : ∀ F ∈ Cone, intR F = 1 → -(13231 / 10000 : ℝ) ≤ Arch F

/-- **[paper] Theorem 2.9(b).**  If `(μ, ν_ζ) ∈ 𝒦` for some `μ`, then RH holds and `μ = μ_ζ`.

Source: Appendix B.1.2, proof of Theorem 2.9(b) (Lemma 2.3 tested on Gaussians `F_u`; a Bohr-mean
argument; uniqueness of even measures agreeing on `𝒢`).  Faithful; `RiemannHypothesis` is Mathlib's. -/
axiom logic_b : ∀ μ : Measure ℝ, Admissible Arch xi2 ⟨μ, nuZeta⟩ → RiemannHypothesis ∧ μ = muZeta

/-- **[paper] Theorem 2.12(a) (weak magic functions).**  If `κ* = 0`, weak magic functions exist.
Every weak magic function `F*` is even, has `F̂* ∈ L¹` with `∫ |F̂*| cosh(πξ) < ∞` (so `F*` extends
analytically to `|Im t| < 1/2`), satisfies `F̂* ≥ 0` on `|ξ| ≥ ξ₂` and `∫ F* log(2+|t|) < ∞`, and has
`∫ F* dμ = 0 = ∫ F̂* dν` for every `(μ, ν) ∈ 𝒦` (written as lower integrals of the non-negative
integrands, which is how the proof obtains them, by Fatou's lemma).

Source: proof of Theorem 2.12(a) (moment bound (2.4), Prokhorov, Vitali, Fatou).  Faithful. -/
axiom weak_magic_functions :
    (kappaStar = 0 → ∃ Fs : ℝ → ℝ, IsWeakMagic Fs) ∧
    ∀ Fs : ℝ → ℝ, IsWeakMagic Fs →
      (∀ t, Fs (-t) = Fs t) ∧
      Integrable (𝓕 (fun t : ℝ => (Fs t : ℂ))) ∧
      Integrable (fun ξ : ℝ => ‖𝓕 (fun t : ℝ => (Fs t : ℂ)) ξ‖ * Real.cosh (Real.pi * ξ)) ∧
      (∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (openStrip (1 / 2)) ∧ ∀ t : ℝ, G t = Fs t) ∧
      (∀ ξ : ℝ, xi2 ≤ |ξ| → 0 ≤ 𝓕 (fun t : ℝ => (Fs t : ℂ)) ξ) ∧
      Integrable (fun t : ℝ => Fs t * Real.log (2 + |t|)) ∧
      ∀ p ∈ K, (∫⁻ t, ENNReal.ofReal (Fs t) ∂p.μ) = 0 ∧
        (∫⁻ ξ, ENNReal.ofReal (𝓕 (fun t : ℝ => (Fs t : ℂ)) ξ).re ∂p.ν) = 0

/-- **[classical + paper] Definition 3.4 (the BRS basis) together with Lemma 3.7 for finite `E`
(formula (3.4); Lemma 3.6 of v1.0) and the Landau step (Lemma B.3 of v1.0).**  There are a basis `B` with
the defining properties of Definition 3.4 (even entire `U_m`, `V_{ρ,j}` with the interpolation properties,
real and imaginary parts in `𝒯`) and a coefficient function `α` such that (3.4) holds for every pair with
finitely many extra atoms satisfying the identity on the functions of `B` (Lemma 3.7), and such that the
Landau step holds for `α`.

Witness: the Bondarenko–Radchenko–Seip basis and the Fourier coefficients `α_N(s)` of the modular
integral `𝖥(τ, s)` of (3.1).  Sources: A. Bondarenko, D. Radchenko, K. Seip, *Fourier interpolation with
zeros of zeta and L-functions*, Constr. Approx. (2023), Theorem 1.1 (existence; no RH, no simplicity)
and §§4.2–4.3 (formula (3.2), decay); Lemma 3.7 (Appendix B.1.5: testing on `U_m`, (3.2), Möbius inversion
over squares); the Landau step: Lemma B.3 of v1.0 of the paper (Lemmas B.1, B.2 and Landau's theorem on
Dirichlet series with non-negative coefficients, Montgomery–Vaughan 2007, Theorem 1.7).  In v1.1 the
paper replaces the Landau step by the mean-value step, Lemmas B.3–B.4 (§3.3 records the earlier
argument); that form is the ledger axiom `brs_countable_meanvalue`, from which the finite case is also
derived (`theoremB_finite_of_countable`).  This axiom is kept so that the v1.0 headline results keep
their axiom sets.  BRS state the decay of the basis functions as "rapid decay in vertical strips" with
constants depending on the height `y`; that the decay is uniform on every closed strip
`|Im z| ≤ 1/2 + δ` (so that the real and imaginary parts lie in `𝒯`) is the paper's reading of
[BRS, §4.3] in Definition 3.4.

Weaker than the paper: the paper names `B` and `α`; here they are only asserted to exist *jointly*.
No uniqueness of `B` is claimed or used: [BRS, Corollary 1.1] needs the class `H₁`, which the decay
`(1 + |z|)^{-2}` of `𝒯` does not give (e.g. `1/(1 + z²) ∈ 𝒯`).  Theorem 3.8 for finite `E` is proved for
every pair `(B, α)` with these properties (`thm_3_7`), and the admissible-pair form (Theorem B(b), finite
`E`) obtains one from this axiom. -/
axiom brs_lemma36_landau :
    ∃ (B : BRSBasis) (α : ℕ → ℂ → ℂ), IsBRSBasis B ∧ Lemma36 B α ∧ LemmaB3 α

/-- **[classical + paper, v1.1] Definition 3.4, Lemma 3.7 (countable `E`) and Lemmas B.3–B.4 (the
mean-value step).**  There are a basis `B` with the defining properties of Definition 3.4 and a
coefficient function `α` such that
(i) (`Lemma36Count`) Lemma 3.7, formula (3.4), holds for every countable symmetric `E ⊆ ℝ \ Z_ζ`: if an
even real `μ = Σ w(x)δ_x` carried by `Z_ζ ∪ E` and a real `ν` on `ℳ` satisfy the identity, with absolutely
convergent integrals, on the BRS functions of `B`, then every series `c_N(E) = Σ_{e ∈ E₊} ϱ̃_e α_N(s_e)`
converges absolutely and `C_N = c_N(E) + ½ (log N) 1_□(N)`; and
(ii) (`MeanValueStep`) Lemma B.4, with Lemma B.3, holds for `α`: if `E₊ ⊂ [0, ∞)` is countable, the real
`a_e` satisfy (B.7) (in its cumulative form `Σ_{e ∈ E₊, 0 < e ≤ T} |a_e| |ζ(1/2+ie)| = o(T^{1/2})`),
`a_0 ≥ 0` if `0 ∈ E₊`, and `c_N = Σ_{e ∈ E₊} ϱ̃_e α_N(s_e) ≥ 0` (absolutely convergent) for every
`N ≡ 2 (mod 3)`, then `ϱ̃_e = 0` for every `e ∈ E₊`.

Witness: as for `brs_lemma36_landau` (the BRS basis and the coefficients `α_N(s)` of (3.1)).  Sources:
(i) is Lemma 3.7 (proof in Appendix B.1.5: testing on `U_m`, (3.2), absolute convergence of the
`U_m`-pairings, Möbius inversion over squares); (ii) is Lemmas B.3 and B.4 (Appendix B.1.6: the Mellin
identity [BRS, (3.17)] with the polynomial Schwartz-seminorm bounds of D. Radchenko, M. Viazovska, *Fourier
interpolation on the real line*, Publ. Math. IHÉS 129 (2019), §6 (proof of Theorem 2); the word `ST²ST²S`
at `τ = 2/3 + iv` with aggregate bounds from the argument margin; the Cesàro mean and mean square of the
almost-periodic `Q(u) = B_0 + Σ_{e>0} (B_e e^{ieu/2} + c.c.)`, `B_e = ϱ̃_e(1 − 3·9^{−s_e})/3`).  The
extension to countable `E` and the mean-value step are due to Astra (OpenAI), contributed during an
independent review of an earlier version of the paper, and independently verified (Paper I, §3.3 and
Appendix B.1.6).

A transcription of Lemmas 3.7, B.3 and B.4, weaker than the paper in two ways: `B` and `α` are only
asserted to exist, jointly, as in `brs_lemma36_landau`; and in (ii) the absolute convergence of the
`c_N`, which Lemma B.3(a) proves, is assumed.  (B.7) is used in its general, cumulative form, as in the
paper; its weighted form implies it (proved in Lean, `cumulativeCond_of_weightedCond`).  The "Moreover"
clauses of Lemma 3.7 and the second assertion of Lemma B.4 are not included.  Nothing is asserted without
(B.7), for `ν` off `ℳ`, or for diffuse extra zero mass.  For finite `E` this gives Theorem 3.8 without the
Landau step (`theoremB_finite_of_countable`). -/
axiom brs_countable_meanvalue :
    ∃ (B : BRSBasis) (α : ℕ → ℂ → ℂ), IsBRSBasis B ∧ Lemma36Count B α ∧ MeanValueStep α

/-- **[paper, v1.1] Theorem 3.6 (zero-side support): the prime measure is `ν_ζ`.**  If `(μ, ν) ∈ 𝒦` and
`μ` is carried by `Z_ζ ∪ {0}`, then `ν = ν_ζ`.
There is no hypothesis on `ν` beyond admissibility (no BRS support, no atomicity).

Source: Paper I, Theorem 3.6 and its proof in Appendix B.1.4 (the theorem is due to Astra (OpenAI),
contributed during an independent review of an earlier version of the paper, and independently
verified): the push-forward `ρ` of `ν` under `x = e^{2πξ}` satisfies `ρ([R, 2R]) ≤ C R^{1/2}`
(Lemma 2.6), so `L_ρ(f) = ∫ √x Σ_{k ≥ 1} f(kx) dρ(x)` is continuous on Schwartz space; testing the
`U_m` (which vanish on `Z_ζ`) and square-divisor Möbius inversion give `L_ρ(b_N) = ½ log N 1_□(N)`
[A. Bondarenko, D. Radchenko, K. Seip, Constr. Approx. (2023), §§3.4.1, 4.2–4.4]; Radchenko–Viazovska
interpolation in Schwartz space [Publ. Math. IHÉS 129 (2019), Theorem 1 and §6] gives
`L_ρ(f) = c f(0) + Σ_n (log n) f(n)` for self-dual `f`; regularisations of the self-dual test
`g(t) = sin²(πt)/(π²(t²−1))` give `supp ρ ⊆ {2, 3, …}`, and divisor Möbius inversion gives
`√m ρ({m}) = Λ(m)`.  Origin: `μ({0}) = 0`, from `ζ(1/2) < 0` and `M_{g+h}(1/2) < 0`.

Faithful: the theorem's first conclusion, with the origin variant ("supp μ ⊆ Z_ζ ∪ {0}" is
`μ((Z_ζ ∪ {0})ᶜ) = 0`; the set is closed, `isClosed_Zzeta`).  The remaining conclusions, RH and
`μ = μ_ζ`, are not part of the axiom: they are proved in Lean from Theorem 2.9(b) (`logic_b`), as in the
paper (`zero_support_theorem`). -/
axiom zero_support_rigidity : ∀ p ∈ K, CarriedBy p.μ (Zzeta ∪ {0}) → p.ν = nuZeta

/-- **[paper] Lemma 4.7 (robust compactness), with two facts established in its proof.**  Under the
hypotheses (i)–(v), a subsequence `H_J` converges locally uniformly on `|Im t| < 1/2 + δ` to some
`H_∞`, and `F_∞ = Ξ² H_∞ ∈ 𝒞 ∩ 𝒯` with `𝒜(F_∞) = 0` and `F̂_∞(0) = ∫ F_∞ > 0`.  From the proof:
`|H_∞(t)| ≤ C e^{a|Re t|}` on the open strip, and `F̂_J → F̂_∞` (uniformly, in particular pointwise)
on `ℝ` along the subsequence.

Source: Lemma 4.7 and its proof in Appendix B.2.3 (Montel's theorem, the bound (4.1), dominated
convergence, Corollary 4.4).  Faithful (the lemma plus two facts proved in its proof). -/
axiom robust_compactness (I : Set ℕ) (H : ℕ → ℂ → ℂ) (δ a C : ℝ) (h : RobustHyp I H δ a C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, φ k ∈ I) ∧ ∃ Hinf : ℂ → ℂ,
      TendstoLocallyUniformlyOn (fun k => H (φ k)) Hinf atTop (openStrip (1 / 2 + δ)) ∧
      (∀ z ∈ openStrip (1 / 2 + δ), ‖Hinf z‖ ≤ C * Real.exp (a * |z.re|)) ∧
      (fun z => Xi z ^ 2 * Hinf z) ∈ Cone ∧
      Arch (fun z => Xi z ^ 2 * Hinf z) = 0 ∧
      0 < intR (fun z => Xi z ^ 2 * Hinf z) ∧
      ∀ ξ : ℝ, Tendsto (fun k => FT (fun z => Xi z ^ 2 * H (φ k) z) ξ) atTop
        (𝓝 (FT (fun z => Xi z ^ 2 * Hinf z) ξ))

/-- **[paper] Appendix B.2.3, "Equivalent forms of (Z_∞)", (i) ⇒ (iii).**  Assume (N) and (G_a).  If
(Z_∞) holds, then for every `T > 0`, `liminf_{J ∈ 𝒥} min_{|t| ≤ T} H_J(t) > 0`.

Source: Appendix B.2.3 (intermediate value theorem with `H_J(0) = 1`, Montel and Hurwitz).  Faithful
(one direction of the stated equivalence). -/
axiom Zinf_lower_bound : HypN → HypG → HypZinf →
    ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ J in atTop ⊓ 𝓟 Jset, ∀ t : ℝ, |t| ≤ T → c ≤ (Hfam J t).re

/-! ## Computer-assisted certificates (§5, Appendix C) -/

/-- **[certificate] Theorem 5.1 and Table 1.**  For each row `(J, κ_J, ε)` of Table 1 there are rationals
`r_j, s_j` (`j < J`) with `s_j > 0`, `r_j² < 4 s_j` (so `H > 0` on `ℝ`) such that
`F_rep = Ξ²(Π_j(1 + r_j t² + s_j t⁴) + ε e^{−πt²})` lies in `𝒞`, has `∫ F_rep > 0`, and
`𝒜(F_rep) ≤ κ_J ∫ F_rep`.

Source: `kappa/verify_kappa.py` (sha256 e02bce5a4457a23978ff3c12a42c178efa45213bff4bdc57fb7ac3c473771c4e),
ball arithmetic, Appendix C Table 4 first row, with
* `kappa/params/J20.json` (sha256 d686e47b0412358c8ad519370655c6f8600c2d44d25ee8da8e39ab66551c5ec8),
  log `(4) kappa* <= A_upper / Fhat_H(0)_lower <= 2.0151627e-62`;
* `kappa/params/J23.json` (sha256 9ea699b1bb61092b89ce2fd2f0f57a560e9f1c4563daf81fca3e03e5dde66e80), `<= 1.1963682e-80`;
* `kappa/params/J24.json` (sha256 55fde51339c382ccce6d0ad32c32db53e3a50bf825749b5eac0f6a097d207e30), `<= 5.2941806e-91`;
* `kappa/params/J30.json` (sha256 472a5a881d5e96d55b8ce013e028416bd7bd7950ea936161a1dca60cba0c201c), `<= 7.7522383e-132`;
* `kappa/params/J35.json` (sha256 35e8cc8eb2b4c5fc478b69807a9fbaa94ea60fee62548d71e641eef033ae7dcb), `<= 9.9924044e-177`;
* `kappa/params/J40.json` (sha256 b3b711578a6e21ad75ad6c69ce3a1a384bfef1255f94ef365f1dab15897e8884), `<= 9.3828982e-220`;
* `kappa/params/J50.json` (sha256 3e95b34b9579df88b72d66249e830d8af795816e702690bf209fb30fbff3d100), `<= 1.8493714e-311`;
* `kappa/params/J60.json` (sha256 e22afd8721e40313f47f4ee5ab3415dcc4d5c24502c17c4994499a9971e94a7e), `<= 1.0640143e-417`;
* `kappa/params/J100.json` (sha256 1186be2c9c2e575810781c02fc8a22ee060ffa4c61be4e8eab21b63a90719662),
  log `(4) kappa* <= A_upper / Fhat_H(0)_lower <= 1.1508391e-906`, `CERTIFIED: True   [J = 100, …]`
  (logs `kappa/logs/J*.log`; step (1) of each log certifies `s_j > 0, r_j^2 < 4 s_j`).
The certificates also rest on Proposition 4.2, Lemma 4.6, Corollary 4.4 and Lemmas A.3, A.4.
Weaker than the certificate: the rationals of the parameter files are only asserted to exist. -/
axiom cert_kappa_ladder : ∀ row ∈ kappaLadder, ∃ r s : Fin row.J → ℚ,
    (∀ j, 0 < s j ∧ r j ^ 2 < 4 * s j) ∧
    Frep r s row.eps ∈ Cone ∧ 0 < intR (Frep r s row.eps) ∧
    Arch (Frep r s row.eps) ≤ (row.kappa : ℝ) * intR (Frep r s row.eps)

/-- **[certificate, v1.1] Corollary 5.3 (near-rigidity): the `J = 100` certificate of Theorem 5.1
dominates `Ξ²`.**  For the certified `F_rep = Ξ²(H + ε e^{−πt²})` of Theorem 5.1 at `J = 100`
(`ε = 10^{-911}`): every coefficient of the polynomial `P` with `H(t) = P(t²)`,
`P(u) = Π_j (1 + r_j u + s_j u²)`, is non-negative (so `H ≥ P(0) = 1` on `ℝ` and `F_rep ≥ Ξ²`; this
step is proved in Lean, `Frep_ge_Xi_sq`), `F_rep ∈ 𝒞`, and `𝒜(F_rep) ≤ 3.21 · 10^{-906}`.

Source: `kappa/check_H_nonneg.py` (sha256 8e5c63371d867378cfa8675f180d310114950a503f81fb622e2712a731d1120d),
exact expansion of `P` over `ℚ` (python-flint `fmpq_poly`), with
`kappa/params/J100.json` (sha256 1186be2c9c2e575810781c02fc8a22ee060ffa4c61be4e8eab21b63a90719662),
log `kappa/logs/H_nonneg.log`: `J = 100, deg P = 200, 201 coefficients, 201 of them > 0; P(0) = 1: True`,
`CLAIM      : J = 100: all coefficients of P >= 0 and P(0) = 1, so H >= 1 on R and F_rep >= Xi^2 ... implied`,
`duality    : kappa/logs/J100.log: certified True, J = 100, …; A(F_rep) <= A_upper = 3.20903614143e-906`,
`RESULT     : CERTIFIED`; and, for `F_rep ∈ 𝒞` and the bound on `𝒜(F_rep)`, `kappa/verify_kappa.py`
(sha256 e02bce5a4457a23978ff3c12a42c178efa45213bff4bdc57fb7ac3c473771c4e) with `kappa/params/J100.json`, log
`kappa/logs/J100.log`: `A(F_rep) <= 3.20903614143e-906`, `CERTIFIED: True   [J = 100, …]` (the same run
as `cert_kappa_ladder`, with the same analytic inputs).  Weaker than the certificate: the rationals
of the parameter file are only asserted to exist, and only the rounded bound `3.21 · 10^{-906}` is
stated. -/
axiom cert_near_rigidity : ∃ r s : Fin 100 → ℚ,
    (∀ k, 0 ≤ (Hpoly r s).coeff k) ∧ Frep r s (1 / 10 ^ 911) ∈ Cone ∧
    Arch (Frep r s (1 / 10 ^ 911)) ≤ (321 : ℝ) / 10 ^ 908

/-- **[certificate] Proposition 5.4 (the classical cone).**  Some `F ∈ 𝒞_OPS` (the Gaussian–Laguerre
function with `s = 13`, `K = 128`, `ε = 10^{-56}`) has `∫ F > 0` and
`𝒜(F)/∫ F ≤ 9.9461827001452550725 · 10^{-41}`.

Source: `general/verify_general.py` (sha256 c47003144785517bd2f169f5e9637d7f61eb09d6cbc36994a2ea2d9179c8f823)
with `general/params/zeta_K128_s13.json` (sha256 0976a6711193adc0f02a532931974b8ef4912337f79e39f59aa21445879a4df2),
exact Sturm sequences and Arb; log `general/logs/zeta_K128_s13.log`:
`SLACK : kappa*_OPS (and kappa*) of the data <= 9.9461827001452550725e-41`,
`POSITIVITY : F_rep > 0 on R: True | … | F_rep^ > 0 on R (OPS cone): True`, `RESULT : CERTIFIED`.
The tail of the digamma integral uses Lemma A.5 (`Re ψ(w + it/2) ≤ log t + 2/t`), and the computation of
`F̂` uses `f̂_k = (−1)^k f_k`.  Weaker than the certificate: the function is only asserted to exist. -/
axiom cert_kappaOPS : ∃ F ∈ ConeOPS, 0 < intR F ∧
    Arch F ≤ ((99461827001452550725 : ℚ) / 10 ^ 60 : ℚ) * intR F

/-- **[certificate] Proposition 5.5 (low-height rigidity).**  Some `F_80 ∈ 𝒞_OPS` (the Gaussian–Laguerre
function with `K = 80`, `s = 12`, `ε = 10^{-30}`) has `𝒜(F_80) ≤ 7.72525424595 · 10^{-25}`,
`∫ F_80 ≥ 0.9999999999999999444`, and the certified lower bounds `F_80 ≥ m` on the zero-side windows,
`F̂_80 ≥ m` on the prime-side windows, and at the two atoms of Table 2.

Source: `general/verify_general.py` with `general/params/zeta_K80_s12_F80.json`
(sha256 c0f3afc2d3367ebdadd0897a6e2f15fc5ae8a7caf8b7c6879b504119a845eee6), log
`general/logs/zeta_K80_s12_F80.log`: `A(F_rep) = [7.725254245948889853868706e-25 ± 4.30e-50]`,
`int F_rep = [0.9999999999999999444888488 ± 3.13e-26]`, `F_rep^ > 0 on R (OPS cone): True`,
`RESULT : CERTIFIED`; and `general/verify_windows.py`
(sha256 94ecef7b62fff1916101130de9dc404f4a574ebf65dc42d4b2c70a150b85c044) with
`general/params/F80_windows.json` (sha256 af90186bb2a9126187e3dd4b2358aec7ca4e69c40fbfef7a6daafdabe9579b24),
log `general/logs/F80_windows.log`: lines `gap{1..5}_eta0.1 F >= m on t in [...] : PROVED`,
`win{2.05-2.95,…,14.0-15.0} F^ >= m on n in [...] : PROVED`, `atom n = 2.5 F^(xi_n) = [0.0015866025 ± 3.99e-13]`,
`atom n = 6 F^(xi_n) = [3.8125495e-7 ± 3.84e-15]`, `RESULT : CERTIFIED`.  The window bounds are certified
for `F_80` without the repair term, which only increases `F_80` and `F̂_80`.  Analytic inputs: Lemma A.2
(positive-coefficient certificates, applied after a Möbius map; proved in Lean as `posc_a`, `posc_b`)
for the window bounds, and Lemma A.5 for the tail of the digamma integral.
Weaker than the certificate: the function is only asserted to exist, and the windows are the
(inward-rounded) intervals of Table 2. -/
axiom cert_lowheight : ∃ F ∈ ConeOPS,
    Arch F ≤ (772525424595 : ℝ) / 10 ^ 36 ∧ (9999999999999999444 : ℝ) / 10 ^ 19 ≤ intR F ∧
    (∀ w ∈ zeroWindows, ∀ t : ℝ, (w.lo : ℝ) ≤ t → t ≤ (w.hi : ℝ) → (w.m : ℝ) ≤ (F t).re) ∧
    (∀ w ∈ primeWindows, ∀ ξ : ℝ, xiOf (w.lo : ℝ) ≤ ξ → ξ ≤ xiOf (w.hi : ℝ) →
      (w.m : ℝ) ≤ (FT F ξ).re) ∧
    (∀ w ∈ atomWindows, (w.m : ℝ) ≤ (FT F (xiOf (w.lo : ℝ))).re)

/-- **[certificate] Proposition 5.9, with Lemma 5.8.**  For `ζ`'s data with conductor `q = e^{0.02}`
there is an admissible pair (of the Herglotz form of Lemma 5.8) whose zero measure satisfies
`μ ≥ 4.71949 · 10^{-4} dt`.

Source: `general/verify_pair.py` (sha256 5ef20efe864698021f6493266465bcbed043e894d7bca9a4a0c9cf3f97a69cb4)
with `general/params/pair_zeta_logq002_X10.json`
(sha256 d28b347d9807e6934a55bb326f20e09318c2aab4851595b914788f5c708888f6), Arb; log
`general/logs/pair_zeta_logq002_X10.log`: `MU FLOOR : mu(t) >= 0.000471949 for all real t`,
`GAP : admissible at gap xi_2 (prime measure on [2, oo)): True`, `RESULT : CERTIFIED`;
admissibility of a pair of Herglotz form with `μ ≥ 0` is Lemma 5.8 [paper].
Weaker than certificate + Lemma 5.8: the pair is only asserted to exist. -/
axiom cert_lowerbound : ∃ p : Pair,
    Admissible (ArchShift ((1 / 50 : ℝ) / (2 * Real.pi))) xi2 p ∧
    DominatesLeb p.μ ((471949 : ℝ) / 10 ^ 9)

/-- **[certificate] Proposition 5.10(a), dual side.**  Some `F ∈ 𝒞_OPS` (a combination of
`f_0(t/7), …, f_80(t/7)` plus two Gaussians) has `∫ F > 0` and
`𝒜_{Γ_ℝ²,1}(F)/∫ F ≤ −0.25566705789831547610`.

Source: `general/verify_general.py` with `general/params/gammaR2_K80_s7.json`
(sha256 79936770a00991a3c4b24ac614f8405686fdf499d6eb0040dd9976ae026a71ee); log
`general/logs/gammaR2_K80_s7.log`: `SLACK : kappa*_OPS (and kappa*) of the data <= -0.25566705789831547610`,
`RESULT : CERTIFIED`; the tail of the digamma integral uses Lemma A.5.  Weaker than the certificate
(existence only). -/
axiom cert_Qsqrt5_dual : ∃ F ∈ ConeOPS, 0 < intR F ∧
    ArchG [0, 0] 1 F ≤ (-(25566705789831547610 : ℚ) / 10 ^ 20 : ℚ) * intR F

/-- **[certificate] Proposition 5.10(a), primal side, with Lemma 5.8.**  For the data `Γ_ℝ²` with
`log q₀ = 1.6093347792651136` there is an admissible pair of Herglotz form whose prime measure is carried
by `[ξ_{4.049150}, ∞)` and whose zero density satisfies `μ ≥ 6.59497 · 10^{-9}`.

Source: `general/verify_pair.py` with `general/params/pair_gammaR2_X240.json`
(sha256 3b9f85c84efcf36f0e753e01edd442bfc3d6a1a2ead2377124b015ea2b7dfb1d); log
`general/logs/pair_gammaR2_X240.log`: `nu~ support : supp nu~ in [x0, oo) with x0 >= 4.049150`,
`MU FLOOR : mu(t) >= 6.59497e-9 for all real t`, `RESULT : CERTIFIED`; Lemma 5.8 [paper].
Weaker than certificate + Lemma 5.8 (existence only). -/
axiom cert_Qsqrt5_pair : ∃ p : Pair,
    Admissible (ArchG [0, 0] (Real.exp ((16093347792651136 : ℝ) / 10 ^ 16)))
      (xiOf ((4049150 : ℝ) / 10 ^ 6)) p ∧
    DominatesLeb p.μ ((659497 : ℝ) / 10 ^ 14)

/-- **[certificate] Proposition 5.10(b), dual side.**  Some `F ∈ 𝒞_OPS` (a combination of
`f_0(t/9), …, f_64(t/9)` plus two Gaussians) has `∫ F > 0` and
`𝒜_{Γ_ℂ,1}(F)/∫ F ≤ −0.17385102660887763683`.

Source: `general/verify_general.py` with `general/params/gammaC_K64_s9.json`
(sha256 e330d8b743bd835920ecaad507a195773f4c858181d97bafb9d3eca1c296021a); log
`general/logs/gammaC_K64_s9.log`: `SLACK : kappa*_OPS (and kappa*) of the data <= -0.17385102660887763683`,
`RESULT : CERTIFIED`; the tail of the digamma integral uses Lemma A.5.  Weaker than the certificate
(existence only). -/
axiom cert_Qsqrtm3_dual : ∃ F ∈ ConeOPS, 0 < intR F ∧
    ArchG [0, 1] 1 F ≤ (-(17385102660887763683 : ℚ) / 10 ^ 20 : ℚ) * intR F

/-- **[certificate] Proposition 5.10(b), primal side, with Lemma 5.8.**  For the data `Γ_ℂ` with
`log q₀ = 1.0976698108720329` there is an admissible pair of Herglotz form whose prime measure is carried
by `[ξ_{3.011664}, ∞)` and whose zero density satisfies `μ ≥ 6.67226 · 10^{-8}`.

Source: `general/verify_pair.py` with `general/params/pair_gammaC_X40.json`
(sha256 f32152ae73a8e202fafd9bd56097dc0b98d68741392ee8149ee3d9262828eeae); log
`general/logs/pair_gammaC_X40.log`: `nu~ support : supp nu~ in [x0, oo) with x0 >= 3.011664`,
`MU FLOOR : mu(t) >= 6.67226e-8 for all real t`, `RESULT : CERTIFIED`; Lemma 5.8 [paper].
Weaker than certificate + Lemma 5.8 (existence only). -/
axiom cert_Qsqrtm3_pair : ∃ p : Pair,
    Admissible (ArchG [0, 1] (Real.exp ((10976698108720329 : ℝ) / 10 ^ 16)))
      (xiOf ((3011664 : ℝ) / 10 ^ 6)) p ∧
    DominatesLeb p.μ ((667226 : ℝ) / 10 ^ 13)

/-- **[certificate] Proposition 5.6 (certified finite-`J` instances).**  For `J ∈ {10, 60, 61, 110, 111}`
the Hermite matrix `M_J` is non-singular, and every coefficient of the exact `P_J` satisfies
`0 < p_k^{(J)} ≤ 0.71636^{2k}/(2k)!` (for `k = 0` this is `p_0 = 1`).

Source: `exact/verify_exact_member.py` (sha256 23b8ed44a3ea04eaa57923b91423cbc13bab3a5dfbdd600d5c86cd5160860c81),
Arb ball solve with moments evaluated through Proposition 4.2, logs `exact/logs/NPOS_J{10,60,61,110,111}.log`:
`(N)  rigorous solve of the 2J x 2J system succeeded (matrix certified non-singular): True`,
`(POS) all 2J+1 coefficients p_k certified > 0: True`, and for `J = 10`
`a = max_k ((2k)! p_k)^(1/2k) <= 0.697078`; output enclosures `exact/out/P10_ball.txt`
(sha256 4e55d361d6d2c05f15565bd3c94d56b9f5e0715acecda9fd362410181bdc48d3), `exact/out/P60_ball.txt`
(sha256 fdfbfe57bfe9945f640291b6f1e1b7e74e4d5afb04278961d5737f26db6cda4b), `exact/out/P61_ball.txt`
(sha256 8cc7b2b9a66f643e8e40d84fd4ffd6970401342aeab87b716ec169bc91ca3dd4), `exact/out/P110_ball.txt`
(sha256 7c8999567bc77cd1c6fb5a9e816bb0b4f212b971f26dd0f3bda3237ff51c117a), `exact/out/P111_ball.txt`
(sha256 25669a321f71ddef789247cd0adc0fd129c5d70f293e488bc4dab8c3f708b3f1); and
`exact/check_coefficient_bound.py` (sha256 c267e87652e86cff504f537b9a2de7913ebc6ea2fa4f6a616995a47e7c0d366c),
log `exact/logs/coefficient_bound.log`:
`CERTIFIED: 0 < p_k <= 0.71636^(2k)/(2k)! for every k, at J = 60, 61, 110, 111: True`.  Faithful. -/
axiom cert_finiteJ : ∀ J ∈ ({10, 60, 61, 110, 111} : Finset ℕ), J ∈ Jset ∧
    ∀ k ≤ 2 * J, 0 < pcoef J k ∧
      pcoef J k ≤ ((71636 : ℝ) / 100000) ^ (2 * k) / ((2 * k).factorial : ℝ)

end PosRig
