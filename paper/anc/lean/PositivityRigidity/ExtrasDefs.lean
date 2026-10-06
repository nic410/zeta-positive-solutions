/-
Definitions for the v1.1 additions (definitions only; no axioms, no theorems):

* the summability condition (3.5) of Theorem 3.8 (countably many extra zeros), in its weighted and its
  cumulative form, and the countable forms of Lemma 3.7 (formula (3.4)) and of the mean-value step
  (Lemmas B.3, B.4), as properties of a basis `B` and a coefficient function `α`, parallel to `Lemma36` and
  `LemmaB3` in `BRSDefs.lean` (v1.0 Lemma 3.6 and the v1.0 Landau step);
* the polynomial `P` with `H(t) = P(t²)` of the certified functions of Theorem 5.1 (Corollary 5.3).

Statement numbers are those of the v1.1 paper.
-/
import PositivityRigidity.Basic
import PositivityRigidity.BRSDefs
import PositivityRigidity.CertDefs

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

/-! ## Growth conditions -/

/-- `Σ_{e ∈ S, e ≤ T} β(e)`, as an element of `[0, ∞]` (each term is `max(β(e), 0)`; every `β` used
below is `≥ 0`).  For countable `S` this is an ordinary series of non-negative terms; there is no junk
value. -/
def partialMass (S : Set ℝ) (β : ℝ → ℝ) (T : ℝ) : ℝ≥0∞ :=
  ∑' e : ↥(S ∩ Set.Iic T), ENNReal.ofReal (β e)

/-- `Σ_{e ∈ S, e ≤ T} β(e) = o(√T)` as `T → ∞`: for every `ε > 0`, eventually
`Σ_{e ∈ S, e ≤ T} β(e) ≤ ε √T` (in particular the partial sums are finite). -/
def SqrtSmall (S : Set ℝ) (β : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ T in atTop, partialMass S β T ≤ ENNReal.ofReal (ε * Real.sqrt T)

/-- `b_e = |a_e| |ζ(1/2 + ie)|` for the zero-side atom weight `a_e = w(e)` (Appendix B.1.6). -/
def zetaWeight (w : ℝ → ℝ) (e : ℝ) : ℝ := |w e| * ‖riemannZeta (1 / 2 + I * (e : ℂ))‖

/-- The cumulative form of the summability condition (3.5) (and (B.7)):
`A(T) = Σ_{e ∈ E, 0 < e ≤ T} |a_e| |ζ(1/2 + ie)| = o(T^{1/2})`, with `a_e = w(e)`. -/
def CumulativeCond (E : Set ℝ) (w : ℝ → ℝ) : Prop := SqrtSmall (E ∩ Set.Ioi 0) (zetaWeight w)

/-- The weighted form of the summability condition (3.5) (and (B.7)):
`Σ_{e ∈ E, e > 0} |a_e| |ζ(1/2 + ie)| (1 + e)^{-1/2} < ∞`, with `a_e = w(e)` (a sum in `[0, ∞]`, so
there is no junk value). -/
def WeightedCond (E : Set ℝ) (w : ℝ → ℝ) : Prop :=
  ∑' e : ↥(E ∩ Set.Ioi 0), ENNReal.ofReal (zetaWeight w e / Real.sqrt (1 + e)) ≠ ⊤

/-! ## Countable forms of Lemma 3.7 and of the mean-value step -/

/-- `c_N = Σ_{e ∈ S} ϱ̃_e α_N(s_e)` over a countable set `S ⊂ [0, ∞)` (a `tsum`); Lemma 3.7 uses
`S = E₊ = E ∩ [0, ∞)`, Lemmas B.3 and B.4 a countable `E₊`.  (For finite `E` this is `cN`.) -/
def cNc (α : ℕ → ℂ → ℂ) (S : Set ℝ) (w : ℝ → ℝ) (N : ℕ) : ℂ :=
  ∑' e : ↥S, (rhoTilde w e : ℂ) * α N (sOf e)

/-- Lemma 3.7 (structure of pairs with extra atoms), formula (3.4), for countable `E`, as a property of a
coefficient function `α` (v1.1; in v1.0 this was Lemma 3.6, for finite `E`: `Lemma36`).  For every
countable symmetric `E ⊆ ℝ \ Z_ζ`, every even real measure `μ = Σ w(x)δ_x` carried by `Z_ζ ∪ E` and
every real `ν = Σ ν_m δ_{log m/4π}` such that `𝒜(F) = ∫ F dμ + (1/π)∫ F̂ dν`, with absolutely convergent
integrals, for every BRS function `F` of `B`: for every `N ≥ 1` the series `c_N(E)` converges absolutely
and `C_N = c_N(E) + ½ (log N) 1_□(N)`. -/
def Lemma36Count (B : BRSBasis) (α : ℕ → ℂ → ℂ) : Prop :=
  ∀ E : Set ℝ, E.Countable → (∀ e ∈ E, e ∉ Zzeta) → (∀ e ∈ E, -e ∈ E) →
    ∀ (w : ℝ → ℝ) (ν : ℕ → ℝ), (∀ x, w (-x) = w x) → (∀ x, w x ≠ 0 → x ∈ Zzeta ∨ x ∈ E) →
      (∀ m : ℕ, 1 ≤ m → Summable (fun x : ℝ => (w x : ℂ) * B.U m x)) →
      (∀ v : VIndex, Summable (fun x : ℝ => (w x : ℂ) * B.V v x)) →
      BRSIdentity B w ν →
      ∀ N : ℕ, 1 ≤ N →
        Summable (fun e : ↥(E ∩ Set.Ici 0) => (rhoTilde w e : ℂ) * α N (sOf e)) ∧
        ((CN ν N : ℝ) : ℂ) = cNc α (E ∩ Set.Ici 0) w N + ((1 / 2 * Real.log N * sqInd N : ℝ) : ℂ)

/-- Lemmas B.3 (aggregate expansion) and B.4 (mean-value step), as a property of a coefficient function
`α` (v1.1; they replace the Landau step, v1.0 Lemma B.3, `LemmaB3`): let `E₊ ⊂ [0, ∞)` be countable and
`a_e` (`e ∈ E₊`) real with the summability condition (B.7) (here in its cumulative form
`Σ_{e ∈ E₊, 0 < e ≤ T} |a_e| |ζ(1/2 + ie)| = o(T^{1/2})`, which the weighted form implies), `a_0 ≥ 0` if
`0 ∈ E₊`, and, with `ϱ̃_e` as in Lemma 3.7, `c_N = Σ_{e ∈ E₊} ϱ̃_e α_N(s_e)` (absolutely convergent)
`≥ 0` for every `N ≡ 2 (mod 3)`.  Then `ϱ̃_e = 0` for every `e ∈ E₊`. -/
def MeanValueStep (α : ℕ → ℂ → ℂ) : Prop :=
  ∀ Ep : Set ℝ, Ep.Countable → Ep ⊆ Set.Ici 0 → ∀ a : ℝ → ℝ, CumulativeCond Ep a →
    ((0 : ℝ) ∈ Ep → 0 ≤ a 0) →
    (∀ N : ℕ, N % 3 = 2 →
      Summable (fun e : ↥Ep => (rhoTilde a e : ℂ) * α N (sOf e)) ∧ 0 ≤ cNc α Ep a N) →
    ∀ e ∈ Ep, rhoTilde a e = 0

/-! ## The certified ladder functions -/

/-- The polynomial `P(u) = Π_{j < J} (1 + r_j u + s_j u²)` of the certified representative
`F_rep = Ξ²(P(t²) + ε e^{−πt²})` of Theorem 5.1 (`H(t) = P(t²)`), with rational coefficients. -/
def Hpoly {J : ℕ} (r s : Fin J → ℚ) : Polynomial ℚ :=
  ∏ j, (1 + Polynomial.C (r j) * Polynomial.X + Polynomial.C (s j) * Polynomial.X ^ 2)

end PosRig
