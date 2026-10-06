/-
Definitions for §3 (uniqueness): the Bondarenko–Radchenko–Seip (BRS) interpolation basis
(Definition 3.4), the pairing of complex BRS functions with purely atomic real measures, and the
statements of Lemma 3.7 (formula (3.4)) for finite `E` and of the Landau step (Lemma B.3 of v1.0) as
propositions about a coefficient function `α`.  (Their countable forms of v1.1, Lemma 3.7 and Lemmas
B.3–B.4, are `Lemma36Count` and `MeanValueStep` in `ExtrasDefs.lean`.)

Real measures carried by a countable set are purely atomic; Theorem 3.8 and Lemma 3.7 concern real
(signed) measures `μ` carried by `Z_ζ ∪ E` and `ν` carried by `ℳ`, so they are represented here by
their atom weights: `μ = Σ_x w(x) δ_x` and `ν = Σ_{m ≥ 1} ν_m δ_{log m/(4π)}`.
-/
import PositivityRigidity.Basic

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder

namespace PosRig

/-- The "real part" of a function, extended off `ℝ`: `z ↦ (F(z) + conj F(conj z))/2`.  On `ℝ` it is
`Re F`; if `F` is entire, so is `rePart F`. -/
def rePart (F : ℂ → ℂ) : ℂ → ℂ := fun z => (F z + (starRingEnd ℂ) (F ((starRingEnd ℂ) z))) / 2

/-- The "imaginary part" of a function, extended off `ℝ`: `z ↦ (F(z) − conj F(conj z))/(2i)`. -/
def imPart (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (F z - (starRingEnd ℂ) (F ((starRingEnd ℂ) z))) / (2 * I)

/-- `𝒜` extended by complex linearity to functions whose real and imaginary parts are in `𝒯`
(Definition 2.1, last sentence). -/
def ArchC (F : ℂ → ℂ) : ℂ := (Arch (rePart F) : ℂ) + I * (Arch (imPart F) : ℂ)

/-- Index set of the BRS functions `V_{ρ,j}`: non-trivial zeros `ρ` with `Im ρ > 0`, and
`0 ≤ j < m(ρ)` (Definition 3.4). -/
def VIndex : Type := {p : ℂ × ℕ // p.1 ∈ NontrivialZeros ∧ 0 < p.1.im ∧ p.2 < mult p.1}

/-- A candidate BRS basis: functions `U_m` (`m ≥ 1`; the slot `m = 0` is unused) and `V_{ρ,j}`. -/
structure BRSBasis where
  U : ℕ → ℂ → ℂ
  V : VIndex → ℂ → ℂ

/-- The defining properties of the BRS basis (Definition 3.4, transcribing
[BRS, Theorem 1.1 and §4.3]): even entire functions with
`U_m^{(j)}(t_ρ) = 0` (`j < m(ρ)`), `Û_m(log m'/4π) = δ_{mm'}`,
`V_{ρ,j}^{(j')}(t_{ρ'}) = δ_{(ρ,j),(ρ',j')}`, `V̂_{ρ,j}(log m/4π) = 0`, whose real and imaginary parts
lie in `𝒯`.  (`U 0 = 0` only fixes the unused slot.)  No uniqueness is claimed: [BRS, Corollary 1.1]
needs the class `H₁`, which the decay `(1 + |z|)^{-2}` of `𝒯` does not give; the formalisation proves
Proposition 3.5 and Theorem 3.8 for *every* basis with these properties. -/
def IsBRSBasis (B : BRSBasis) : Prop :=
  B.U 0 = 0 ∧
  (∀ m : ℕ, 1 ≤ m → Differentiable ℂ (B.U m) ∧ (∀ z, B.U m (-z) = B.U m z) ∧
      rePart (B.U m) ∈ TestClass ∧ imPart (B.U m) ∈ TestClass) ∧
  (∀ v : VIndex, Differentiable ℂ (B.V v) ∧ (∀ z, B.V v (-z) = B.V v z) ∧
      rePart (B.V v) ∈ TestClass ∧ imPart (B.V v) ∈ TestClass) ∧
  (∀ m : ℕ, 1 ≤ m → ∀ ρ ∈ NontrivialZeros, ∀ j < mult ρ, iteratedDeriv j (B.U m) (tOf ρ) = 0) ∧
  (∀ m m' : ℕ, 1 ≤ m → 1 ≤ m' → FT (B.U m) (brsNode m') = if m = m' then 1 else 0) ∧
  (∀ v : VIndex, ∀ ρ' ∈ NontrivialZeros, 0 < ρ'.im → ∀ j' < mult ρ',
      iteratedDeriv j' (B.V v) (tOf ρ') = if v.val = (ρ', j') then 1 else 0) ∧
  (∀ v : VIndex, ∀ m : ℕ, 1 ≤ m → FT (B.V v) (brsNode m) = 0)

/-- `∫ F dμ` for the purely atomic real measure `μ = Σ_x w(x) δ_x`. -/
def pairAtoms (w : ℝ → ℝ) (F : ℂ → ℂ) : ℂ := ∑' x : ℝ, (w x : ℂ) * F x

/-- `∫ G dν` for the real measure `ν = Σ_{m ≥ 1} ν_m δ_{log m/(4π)}` carried by `ℳ`. -/
def pairNodes (ν : ℕ → ℝ) (G : ℝ → ℂ) : ℂ :=
  ∑' m : ℕ, if 1 ≤ m then (ν m : ℂ) * G (brsNode m) else 0

/-- The identity `𝒜(F) = ∫ F dμ + (1/π) ∫ F̂ dν` for every BRS function `F` (hypothesis of
Lemma 3.7, Proposition 3.5 in its signed form, and Theorem 3.8).  For the data of those statements
every pairing here is a finite sum, by the interpolation properties. -/
def BRSIdentity (B : BRSBasis) (w : ℝ → ℝ) (ν : ℕ → ℝ) : Prop :=
  (∀ m : ℕ, 1 ≤ m →
      ArchC (B.U m) = pairAtoms w (B.U m) + (1 / Real.pi : ℂ) * pairNodes ν (FT (B.U m))) ∧
  (∀ v : VIndex,
      ArchC (B.V v) = pairAtoms w (B.V v) + (1 / Real.pi : ℂ) * pairNodes ν (FT (B.V v)))

/-- `s_e = 1/4 + ie/2` (§3.3). -/
def sOf (e : ℝ) : ℂ := 1 / 4 + I * (e : ℂ) / 2

/-- `ϱ̃_e = a_e Ξ(e)/(1/4 + e²)` for `e > 0` and `ϱ̃_0 = 2 a_0 Ξ(0)` (Lemma 3.7), with `a_e = w(e)`.
`Ξ` is real on `ℝ` (`Xi_real` in `Zeta.lean`), so taking the real part changes nothing. -/
def rhoTilde (w : ℝ → ℝ) (e : ℝ) : ℝ :=
  if e = 0 then 2 * w 0 * (Xi 0).re else w e * (Xi e).re / (1 / 4 + e ^ 2)

/-- `c_N(E) = Σ_{e ∈ E₊} ϱ̃_e α_N(s_e)`, `E₊ = E ∩ [0, ∞)` (Lemma 3.7). -/
def cN (α : ℕ → ℂ → ℂ) (E : Finset ℝ) (w : ℝ → ℝ) (N : ℕ) : ℂ :=
  ∑ e ∈ E.filter (fun e => 0 ≤ e), (rhoTilde w e : ℂ) * α N (sOf e)

/-- `ℓ_m = m^{1/4} ν({log m/(4π)})` (Lemma 3.7). -/
def ell (ν : ℕ → ℝ) (m : ℕ) : ℝ := (m : ℝ) ^ ((1 : ℝ) / 4) * ν m

/-- The divisors `k ≥ 1` with `k² ∣ N`. -/
def sqDivisors (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter (fun k => 1 ≤ k ∧ k ^ 2 ∣ N)

/-- `C_N = Σ_{k² ∣ N} ℓ_{N/k²}` (Lemma 3.7). -/
def CN (ν : ℕ → ℝ) (N : ℕ) : ℝ := ∑ k ∈ sqDivisors N, ell ν (N / k ^ 2)

open Classical in
/-- `1_□(N)`: `1` if `N` is a perfect square, `0` otherwise. -/
def sqInd (N : ℕ) : ℝ := if IsSquare N then 1 else 0

/-- Lemma 3.7 for finite `E` (Lemma 3.6 of v1.0), formula (3.4), as a property of a coefficient function
`α`: for every finite symmetric
`E ⊆ ℝ \ Z_ζ` and every even real measure `μ = Σ w(x)δ_x` carried by `Z_ζ ∪ E` and real measure
`ν = Σ ν_m δ_{log m/4π}` satisfying the identity on the BRS functions of `B`,
`C_N = c_N(E) + ½ (log N) 1_□(N)` for every `N ≥ 1`. -/
def Lemma36 (B : BRSBasis) (α : ℕ → ℂ → ℂ) : Prop :=
  ∀ E : Finset ℝ, (∀ e ∈ E, e ∉ Zzeta) → (∀ e ∈ E, -e ∈ E) →
    ∀ (w : ℝ → ℝ) (ν : ℕ → ℝ), (∀ x, w (-x) = w x) → (∀ x, w x ≠ 0 → x ∈ Zzeta ∨ x ∈ E) →
      BRSIdentity B w ν →
      ∀ N : ℕ, 1 ≤ N → ((CN ν N : ℝ) : ℂ) = cN α E w N + ((1 / 2 * Real.log N * sqInd N : ℝ) : ℂ)

/-- The Landau step (Lemma B.3 of v1.0; in v1.1 replaced by Lemmas B.3–B.4, `MeanValueStep`), as a
property of a coefficient function `α`: if `E₊ ⊂ [0, ∞)` is finite, `ϱ̃_e ∈ ℝ` with `ϱ̃_0 ≥ 0` if `0 ∈ E₊`, and `c_N = Σ_{e ∈ E₊} ϱ̃_e α_N(s_e) ≥ 0` for every
`N ≡ 2 (mod 3)`, then `ϱ̃_e = 0` for every `e ∈ E₊`. -/
def LemmaB3 (α : ℕ → ℂ → ℂ) : Prop :=
  ∀ Ep : Finset ℝ, (∀ e ∈ Ep, 0 ≤ e) → ∀ ϱ : ℝ → ℝ, ((0 : ℝ) ∈ Ep → 0 ≤ ϱ 0) →
    (∀ N : ℕ, N % 3 = 2 → 0 ≤ ∑ e ∈ Ep, (ϱ e : ℂ) * α N (sOf e)) →
    ∀ e ∈ Ep, ϱ e = 0

open Classical in
/-- The atom of `ν_ζ` at the BRS node `log m/(4π)`: `Λ(√m) m^{-1/4}`, with `Λ(√m) = 0` if `m` is not a
square (§3.2, (3.3)). -/
def nuZetaAtom (m : ℕ) : ℝ :=
  if IsSquare m then ArithmeticFunction.vonMangoldt (Nat.sqrt m) * (m : ℝ) ^ (-(1 : ℝ) / 4) else 0

end PosRig
