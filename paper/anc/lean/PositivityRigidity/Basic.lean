/-
Positivity–rigidity (Paper I): basic definitions.

Paper: "Positive solutions of the explicit formula for ζ(s): near-criticality and uniqueness".
Section, theorem and equation numbers below are those of the paper (`paper/build/main.pdf`).

This file contains *definitions only* (no axioms, no theorems).  Every definition transcribes a
definition of the paper; the docstrings say which one, and point out every place where the Lean
object is a harmless re-packaging of the paper's object (for example a real part of a quantity
that the paper shows to be real).
-/
import Mathlib

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

/-! ## Coordinates and strips (§1.6, §2.1) -/

/-- `ξ_x = log x / (2π)` for real `x > 0` (§1.6). -/
def xiOf (x : ℝ) : ℝ := Real.log x / (2 * Real.pi)

/-- The gap `ξ₂ = log 2 / (2π)` (§2.1). -/
def xi2 : ℝ := xiOf 2

/-- The closed horizontal strip `{z : |Im z| ≤ b}`. -/
def closedStrip (b : ℝ) : Set ℂ := {z : ℂ | |z.im| ≤ b}

/-- The open horizontal strip `{z : |Im z| < b}`. -/
def openStrip (b : ℝ) : Set ℂ := {z : ℂ | |z.im| < b}

/-- The restriction to the real line of a function on `ℂ`. -/
def onR (F : ℂ → ℂ) : ℝ → ℂ := fun t : ℝ => F (t : ℂ)

/-- The Fourier transform `F̂(ξ) = ∫_ℝ F(t) e^{-2πiξt} dt` of (the restriction to `ℝ` of) `F`
(§1.6, §2.1).  This is Mathlib's `𝓕`, whose normalisation is exactly the paper's
(`Real.fourier_real_eq_integral_exp_smul`). -/
def FT (F : ℂ → ℂ) : ℝ → ℂ := 𝓕 (onR F)

/-! ## The test class (Definition 2.1) -/

/-- `F ∈ 𝒯_δ` (Definition 2.1), for `0 < δ < 1/2`: `F` is even and real on `ℝ`, analytic in a
neighbourhood of the closed strip `|Im z| ≤ 1/2 + δ`, and
`‖F‖_δ = sup_{|Im z| ≤ 1/2+δ} (1+|z|)² |F(z)| < ∞`.

Lean conventions: `F : ℂ → ℂ` is a function on all of `ℂ`, but only its values on the closed strip
enter any definition below; evenness is required on the strip (where the paper's `F` lives).
`AnalyticOnNhd ℂ F S` means "analytic at every point of `S`", i.e. analytic on an open
neighbourhood of `S`. -/
structure InTδ (δ : ℝ) (F : ℂ → ℂ) : Prop where
  pos : 0 < δ
  lt_half : δ < 1 / 2
  even : ∀ z ∈ closedStrip (1 / 2 + δ), F (-z) = F z
  real : ∀ t : ℝ, (F t).im = 0
  analytic : AnalyticOnNhd ℂ F (closedStrip (1 / 2 + δ))
  bound : ∃ C : ℝ, ∀ z ∈ closedStrip (1 / 2 + δ), (1 + ‖z‖) ^ 2 * ‖F z‖ ≤ C

/-- The test class `𝒯 = ⋃_{δ>0} 𝒯_δ` (Definition 2.1). -/
def TestClass : Set (ℂ → ℂ) := {F | ∃ δ : ℝ, InTδ δ F}

/-- The Gaussian wave packet `t ↦ e^{-π(t-a)²/s² + 2πibt}`, as an entire function. -/
def gwp (a b s : ℝ) : ℂ → ℂ :=
  fun z => Complex.exp (-(Real.pi : ℂ) * (z - a) ^ 2 / (s : ℂ) ^ 2 + 2 * Real.pi * I * b * z)

/-- `span_ℂ {e^{-π(t-a)²/s² + 2πibt} : a, b ∈ ℝ, s > 0}` (Definition 2.1). -/
def gwpSpan : Submodule ℂ (ℂ → ℂ) :=
  Submodule.span ℂ {f | ∃ a b s : ℝ, 0 < s ∧ f = gwp a b s}

/-- `𝒢`: the even real-valued elements of the span of the Gaussian wave packets
(Definition 2.1). "Even" and "real-valued" refer to the functions of `t ∈ ℝ`. -/
def Gset : Set (ℂ → ℂ) :=
  {F | F ∈ gwpSpan ∧ (∀ t : ℝ, F (-(t : ℂ)) = F t) ∧ ∀ t : ℝ, (F t).im = 0}

/-! ## Archimedean data (§2.1) -/

/-- The archimedean density `Ω_∞(t) = (1/2π)(Re ψ(1/4 + it/2) − log π)`, `ψ = Γ'/Γ` (§2.1).
Mathlib's `Complex.digamma` is `logDeriv Complex.Gamma = Γ'/Γ`. -/
def Ωinf (t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ((Complex.digamma (1 / 4 + I * (t : ℂ) / 2)).re - Real.log Real.pi)

/-- `∫_ℝ F` for a test function (real-valued on `ℝ`): the integral of the real part. -/
def intR (F : ℂ → ℂ) : ℝ := ∫ t : ℝ, (F t).re

/-- The archimedean functional `𝒜(F) = F(i/2) + F(−i/2) + ∫_ℝ F(t) Ω_∞(t) dt` (§2.1).

For `F ∈ 𝒯` the paper's `𝒜(F)` is a real number (`F` is real on `ℝ`, and by Schwarz reflection and
evenness `F(−i/2) = F(i/2) ∈ ℝ`); the Lean value is its real part, hence equal to it. -/
def Arch (F : ℂ → ℂ) : ℝ :=
  (F (I / 2) + F (-I / 2)).re + ∫ t : ℝ, (F t).re * Ωinf t

/-- `𝒜 + λ∫(·)` (§2.2, after Theorem 2.7; Proposition 2.8). -/
def ArchShift (lam : ℝ) (F : ℂ → ℂ) : ℝ := Arch F + lam * intR F

/-- `𝒜_q = 𝒜 + (log q/2π) ∫(·)`, the archimedean functional with conductor `q` (§2.4). -/
def Arch_q (q : ℝ) (F : ℂ → ℂ) : ℝ := ArchShift (Real.log q / (2 * Real.pi)) F

/-- `Ω_𝔤(t) = (1/2π) Σ_{j ≤ d} (Re ψ((1/2 + k_j + it)/2) − log π)` for the Gamma factor with shifts
`ks = (k_j)` (§5.5): `Γ_ℝ ↔ [0]`, `Γ_ℝ² ↔ [0, 0]`, `Γ_ℂ ↔ [0, 1]`. -/
def OmegaG (ks : List ℕ) (t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (ks.map fun k : ℕ =>
      (Complex.digamma ((1 / 2 + (k : ℂ) + I * (t : ℂ)) / 2)).re - Real.log Real.pi).sum

/-- `𝒜_{𝔤,q}(F) = F(i/2) + F(−i/2) + ∫ F(t)(Ω_𝔤(t) + log q/2π) dt` (§5.5).  The conductor term is
written outside the integral; for `F ∈ 𝒯` both integrals converge absolutely, so this is the
paper's functional. -/
def ArchG (ks : List ℕ) (q : ℝ) (F : ℂ → ℂ) : ℝ :=
  (F (I / 2) + F (-I / 2)).re + (∫ t : ℝ, (F t).re * OmegaG ks t)
    + Real.log q / (2 * Real.pi) * intR F

/-! ## Pairs, admissibility, cones, slack (Definition 2.4) -/

/-- A pair `(μ, ν)` of positive Borel measures on `ℝ` (zero side, prime side). -/
@[ext]
structure Pair where
  μ : Measure ℝ
  ν : Measure ℝ

/-- `μ` is even: invariant under `t ↦ −t`. -/
def EvenMeasure (μ : Measure ℝ) : Prop := Measure.map (fun t : ℝ => -t) μ = μ

/-- `μ` is carried by `S`: `μ(ℝ \ S) = 0`. -/
def CarriedBy (μ : Measure ℝ) (S : Set ℝ) : Prop := μ Sᶜ = 0

/-- Admissible pairs (Definition 2.4), for an archimedean functional `A` and a gap `g`
(`g = ξ₂` in Definition 2.4; general gaps `g` in §5.5): `μ` even, `ν` carried by `[g, ∞)`, and for every
`F ∈ 𝒯` the integrals `∫ F dμ`, `∫ F̂ dν` converge absolutely and `A(F) = ∫ F dμ + (1/π) ∫ F̂ dν`.

The paper asks for positive *Radon* measures.  Local finiteness is not written into the definition
because it follows from the integrability clause applied to the Gaussian `e^{-πt²} ∈ 𝒯`
(proved in `Sanity.lean`: `Admissible.isLocallyFinite`). -/
def Admissible (A : (ℂ → ℂ) → ℝ) (g : ℝ) (p : Pair) : Prop :=
  EvenMeasure p.μ ∧ CarriedBy p.ν (Set.Ici g) ∧
    ∀ F ∈ TestClass, Integrable (onR F) p.μ ∧ Integrable (FT F) p.ν ∧
      ((A F : ℝ) : ℂ) = (∫ t, F t ∂p.μ) + (1 / Real.pi : ℂ) * ∫ ξ, FT F ξ ∂p.ν

/-- `𝒦(A)` at gap `g`. -/
def Kset (A : (ℂ → ℂ) → ℝ) (g : ℝ) : Set Pair := {p | Admissible A g p}

/-- `𝒦`, the set of admissible pairs (Definition 2.4). -/
def K : Set Pair := Kset Arch xi2

/-- The cone `𝒞_g = {F ∈ 𝒯 : F ≥ 0 on ℝ, F̂ ≥ 0 on [g, ∞)}` (§5.5; `𝒞 = 𝒞_{ξ₂}`).
`0 ≤ z` for `z : ℂ` is Mathlib's order on `ℂ` (`z` real and `≥ 0`). -/
def ConeG (g : ℝ) : Set (ℂ → ℂ) :=
  {F | F ∈ TestClass ∧ (∀ t : ℝ, 0 ≤ F t) ∧ ∀ ξ : ℝ, g ≤ ξ → 0 ≤ FT F ξ}

/-- The cone `𝒞` (Definition 2.4). -/
def Cone : Set (ℂ → ℂ) := ConeG xi2

/-- The classical cone `𝒞_OPS = {F ∈ 𝒯 : F ≥ 0 and F̂ ≥ 0 on ℝ}` (Definition 2.4). -/
def ConeOPS : Set (ℂ → ℂ) :=
  {F | F ∈ TestClass ∧ (∀ t : ℝ, 0 ≤ F t) ∧ ∀ ξ : ℝ, 0 ≤ FT F ξ}

/-- The slack `inf {A(F) : F ∈ C, ∫ F = 1}`, as an extended real (so that it has no junk value). -/
def slack (A : (ℂ → ℂ) → ℝ) (C : Set (ℂ → ℂ)) : EReal :=
  ⨅ F ∈ {F | F ∈ C ∧ intR F = 1}, ((A F : ℝ) : EReal)

/-- `κ* = inf {𝒜(F) : F ∈ 𝒞, ∫ F = 1}` (Definition 2.4). -/
def kappaStar : EReal := slack Arch Cone

/-- `κ*_OPS = inf {𝒜(F) : F ∈ 𝒞_OPS, ∫ F = 1}` (Definition 2.4). -/
def kappaOPS : EReal := slack Arch ConeOPS

/-- `q_min = e^{−2πκ*}` (Proposition 2.10).  Meaningful because `κ*` is finite
(`kappaStar_ne_bot`, `kappaStar_ne_top`). -/
def qmin : ℝ := Real.exp (-2 * Real.pi * kappaStar.toReal)

/-! ## The pair of ζ (§2.1) -/

/-- The non-trivial zeros of `ζ`: the zeros in the open critical strip `0 < Re s < 1`. -/
def NontrivialZeros : Set ℂ := {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}

/-- The multiplicity of a zero of `ζ` at `s` (order of vanishing; Mathlib's `analyticOrderNatAt`). -/
def mult (s : ℂ) : ℕ := analyticOrderNatAt riemannZeta s

/-- `t_ρ = −i(ρ − 1/2)` (Lemma 2.3). -/
def tOf (ρ : ℂ) : ℂ := -I * (ρ - 1 / 2)

/-- `Z_ζ = {γ ∈ ℝ : ζ(1/2 + iγ) = 0}`, the real zero ordinates (§1.6). -/
def Zzeta : Set ℝ := {γ : ℝ | riemannZeta (1 / 2 + I * (γ : ℂ)) = 0}

/-- `μ_ζ = Σ_{γ ∈ Z_ζ} m_γ δ_γ` (§2.1). -/
def muZeta : Measure ℝ :=
  Measure.sum fun γ : Zzeta => ((mult (1 / 2 + I * ((γ : ℝ) : ℂ)) : ℝ≥0∞)) • Measure.dirac (γ : ℝ)

/-- `ν_ζ = Σ_{n ≥ 2} Λ(n) n^{−1/2} δ_{ξ_n}` (§2.1). (The terms `n = 0, 1` vanish since `Λ = 0` there.) -/
def nuZeta : Measure ℝ :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (ArithmeticFunction.vonMangoldt n / Real.sqrt n) • Measure.dirac (xiOf n)

/-- `p_ζ = (μ_ζ, ν_ζ)` (§2.1). -/
def pZeta : Pair := ⟨muZeta, nuZeta⟩

/-! ## The statements (E), (U), (S) (Definition 2.4) -/

/-- (E): `𝒦 ≠ ∅`. -/
def CondE : Prop := K.Nonempty

/-- (U): `𝒦 ⊆ {p_ζ}` (Conjecture U). -/
def CondU : Prop := K ⊆ {pZeta}

/-- (S): `κ* ≤ 0` (Conjecture S). -/
def CondS : Prop := kappaStar ≤ 0

/-! ## Zero sets, discrete sets, atomic measures (§2.4) -/

/-- `Z(F) = F⁻¹(0) ∩ ℝ` (Definition 2.11). -/
def ZF (F : ℂ → ℂ) : Set ℝ := {t : ℝ | F t = 0}

/-- `Ẑ(F) = F̂⁻¹(0) ∩ [ξ₂, ∞)` (Definition 2.11). -/
def ZhatF (F : ℂ → ℂ) : Set ℝ := {ξ : ℝ | xi2 ≤ ξ ∧ FT F ξ = 0}

/-- `μ` is purely atomic: carried by a countable set. -/
def PurelyAtomic (μ : Measure ℝ) : Prop := ∃ S : Set ℝ, S.Countable ∧ CarriedBy μ S

/-- A discrete subset of `ℝ`, in the sense *closed and discrete*: no point of `ℝ` is an accumulation
point of `Z` (equivalently, `Z` meets every bounded interval in a finite set).  In Theorem 2.12(b)(iii)
and Theorem A(b) this makes "(i) ⇒ (iii)" stronger and "(iii) ⇒ (ii)" weaker than with plain
"discrete"; both directions are proved (the zero set of a weak magic function is closed and discrete). -/
def DiscreteSet (Z : Set ℝ) : Prop := ∀ x : ℝ, ∀ᶠ y in 𝓝[≠] x, y ∉ Z

/-- `μ ≥ λ dt`. -/
def DominatesLeb (μ : Measure ℝ) (lam : ℝ) : Prop := ENNReal.ofReal lam • (volume : Measure ℝ) ≤ μ

/-- Exact magic functions (Definition 2.11): `F ∈ 𝒞` with `∫ F > 0` and `𝒜(F) = 0`. -/
def IsExactMagic (F : ℂ → ℂ) : Prop := F ∈ Cone ∧ 0 < intR F ∧ Arch F = 0

/-- Weak magic functions (Definition 2.11): `F* : ℝ → [0, ∞)` with `∫ F* = 1`, for which there are
`F_K ∈ 𝒞` with `∫ F_K = 1` and `𝒜(F_K) → 0`, `F_K → F*` and `F̂_K → F̂*` pointwise on `ℝ`. -/
def IsWeakMagic (Fs : ℝ → ℝ) : Prop :=
  (∀ t, 0 ≤ Fs t) ∧ (∫ t, Fs t) = 1 ∧
    ∃ Fk : ℕ → ℂ → ℂ, (∀ k, Fk k ∈ Cone ∧ intR (Fk k) = 1) ∧
      Tendsto (fun k => Arch (Fk k)) atTop (𝓝 0) ∧
      (∀ t : ℝ, Tendsto (fun k => Fk k t) atTop (𝓝 (Fs t : ℂ))) ∧
      (∀ ξ : ℝ, Tendsto (fun k => FT (Fk k) ξ) atTop (𝓝 (𝓕 (fun t : ℝ => (Fs t : ℂ)) ξ)))

/-! ## The BRS nodes and prime powers (§1.3, §3, §4) -/

/-- The BRS node `log m/(4π)`. -/
def brsNode (m : ℕ) : ℝ := Real.log m / (4 * Real.pi)

/-- `ℳ = {log m/(4π) : m ≥ 1}` (§1.3). -/
def BRSNodes : Set ℝ := {x : ℝ | ∃ m : ℕ, 1 ≤ m ∧ x = brsNode m}

/-- `ξ_PP = {ξ_n : n a prime power}` (§1.6). -/
def xiPP : Set ℝ := {x : ℝ | ∃ n : ℕ, IsPrimePow n ∧ x = xiOf n}

/-! ## Riemann's Ξ (§4) -/

/-- Riemann's `ξ(s) = ½ s(s−1) Γ_ℝ(s) ζ(s)`, written with Mathlib's entire function
`completedRiemannZeta₀ = Λ₀`: since `Λ(s) = Λ₀(s) − 1/s − 1/(1−s)`, `s(s−1)Λ(s) = s(s−1)Λ₀(s) + 1`.
(`xiR_eq` in `Sanity.lean` checks `ξ(s) = ½ s(s−1) Γ_ℝ(s) ζ(s)` for `s ≠ 0, 1`.) -/
def xiR (s : ℂ) : ℂ := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- Riemann's `Ξ(t) = ξ(1/2 + it)` (§4). -/
def Xi (z : ℂ) : ℂ := xiR (1 / 2 + I * z)

end PosRig
