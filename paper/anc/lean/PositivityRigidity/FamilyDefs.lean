/-
Definitions for §4 (the zero-killing family and Theorem D): the moments `m_k`, the Hermite matrix
`M_J`, the exact family `P_J`, `H_J(t) = P_J(t²)`, `F_J = Ξ² H_J` (Proposition 4.5), and the
hypotheses (N), (G_a), (Z_∞) of Theorem 4.8 and the strict (Mg) of v1.0 (the non-strict (Mg) of v1.1 is
`HypMg0`, `CriterionWeak.lean`); the hypotheses (i)–(v) of Lemma 4.7.
-/
import PositivityRigidity.Basic

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder

namespace PosRig

/-- The `j`-th prime power `n_j` (`j ≥ 1`): `n_1 = 2, n_2 = 3, n_3 = 4, n_4 = 5, …` (§4.2). -/
def ppNth (j : ℕ) : ℕ := Nat.nth IsPrimePow (j - 1)

/-- `Ψ = (Ξ²)^`, the kernel (Lemma 4.1). -/
def Psi : ℝ → ℂ := FT (fun z => Xi z ^ 2)

/-- The moment `m_k = (t^{2k} Ξ²)^` (§4.2). -/
def mom (k : ℕ) : ℝ → ℂ := FT (fun z => z ^ (2 * k) * Xi z ^ 2)

/-- The moment as a real function, `ξ ↦ Re m_k(ξ)`.  `m_k` is the Fourier transform of the even
function `t^{2k} Ξ(t)²`, real on `ℝ`, hence real-valued (`FT_real_of_even_real` in `Sanity.lean`), so
taking the real part changes nothing; it makes the Hermite system a real linear system, as in the
paper. -/
def momR (k : ℕ) (ξ : ℝ) : ℝ := (mom k ξ).re

/-- Row `r` of the Hermite system corresponds to the node `n_j` with `j = r/2 + 1`, and to the value
(`r` even) or the `ξ`-derivative (`r` odd). -/
def rowNode (r : ℕ) : ℝ := xiOf (ppNth (r / 2 + 1))

/-- The data `[g(ξ_{n_j}); g'(ξ_{n_j})]` of a real function `g` in row `r` (derivatives in `ξ`). -/
def rowData (g : ℝ → ℝ) (r : ℕ) : ℝ := if r % 2 = 0 then g (rowNode r) else deriv g (rowNode r)

/-- The Hermite matrix `M_J = [m_k(ξ_{n_j}); m_k'(ξ_{n_j})]_{j ≤ J, 1 ≤ k ≤ 2J}` (Proposition 4.5);
column `c` is the moment `m_{c+1}`. -/
def hermiteM (J : ℕ) : Matrix (Fin (2 * J)) (Fin (2 * J)) ℝ :=
  fun r c => rowData (momR (c.val + 1)) r.val

/-- `b_J = [m_0(ξ_{n_j}); m_0'(ξ_{n_j})]` (Proposition 4.5). -/
def hermiteB (J : ℕ) : Fin (2 * J) → ℝ := fun r => rowData (momR 0) r.val

/-- `𝒥 = {J ≥ 1 : M_J non-singular}` (Proposition 4.5). -/
def Jset : Set ℕ := {J : ℕ | 1 ≤ J ∧ (hermiteM J).det ≠ 0}

/-- The coefficient vector `p^{(J)} = −M_J^{-1} b_J` (entries `p_1, …, p_{2J}`) (Proposition 4.5). -/
def pvec (J : ℕ) : Fin (2 * J) → ℝ := -(Matrix.mulVec (hermiteM J)⁻¹ (hermiteB J))

/-- The coefficient `p_k^{(J)}` of `P_J` (`p_0 = 1`, `p_k = 0` for `k > 2J`). -/
def pcoef (J k : ℕ) : ℝ :=
  if k = 0 then 1 else if h : k - 1 < 2 * J then pvec J ⟨k - 1, h⟩ else 0

/-- `P_J(u) = Σ_{k ≤ 2J} p_k u^k` with `P_J(0) = 1` (Proposition 4.5). -/
def Pfam (J : ℕ) (u : ℂ) : ℂ := ∑ k ∈ Finset.range (2 * J + 1), (pcoef J k : ℂ) * u ^ k

/-- `H_J(t) = P_J(t²)` (Proposition 4.5). -/
def Hfam (J : ℕ) (z : ℂ) : ℂ := Pfam J (z ^ 2)

/-- `F_J = Ξ² H_J` (Proposition 4.5). -/
def Ffam (J : ℕ) (z : ℂ) : ℂ := Xi z ^ 2 * Hfam J z

/-- (N): `𝒥` is infinite (§4.3). -/
def HypN : Prop := Jset.Infinite

/-- (G_a): there are `δ ∈ (0, 1/2)`, `a < π/2` and `C` with `|H_J(t)| ≤ C e^{a|Re t|}` on
`|Im t| ≤ 1/2 + δ` for all `J ∈ 𝒥` (§4.3). -/
def HypG : Prop :=
  ∃ δ a C : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ a < Real.pi / 2 ∧
    ∀ J ∈ Jset, ∀ z ∈ closedStrip (1 / 2 + δ), ‖Hfam J z‖ ≤ C * Real.exp (a * |z.re|)

/-- (Z_∞): no real point is a limit of zeros of `H_{J_k}` with `J_k ∈ 𝒥`, `J_k → ∞` (§4.3). -/
def HypZinf : Prop :=
  ∀ t₀ : ℝ, ¬ ∃ (Jk : ℕ → ℕ) (zk : ℕ → ℂ), (∀ k, Jk k ∈ Jset) ∧ Tendsto Jk atTop atTop ∧
    (∀ k, Hfam (Jk k) (zk k) = 0) ∧ Tendsto zk atTop (𝓝 (t₀ : ℂ))

/-- (Mg) of v1.0 (strict): for every `ξ ∈ [ξ₂, ∞) \ ξ_PP`, `liminf_{J ∈ 𝒥} F̂_J(ξ) > 0` (§4.3 of v1.0);
written without `liminf`: some `c > 0` is eventually (along `J ∈ 𝒥`) a lower bound.  `F̂_J` is
real-valued.  In v1.1 (Mg) is non-strict, `HypMg0`, and `hypMg0_of_hypMg` shows it is weaker. -/
def HypMg : Prop :=
  ∀ ξ : ℝ, xi2 ≤ ξ → ξ ∉ xiPP →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ J in atTop ⊓ 𝓟 Jset, c ≤ (FT (Ffam J) ξ).re

/-- The hypotheses (i)–(v) of Lemma 4.7 for a family `H_J`, `J` in an infinite index set `I`, with
constants `δ, a, C` (`F_J = Ξ² H_J`).  The `liminf` conditions (iii), (iv) are written as
"`∀ ε > 0`, eventually `≥ −ε`". -/
def RobustHyp (I : Set ℕ) (H : ℕ → ℂ → ℂ) (δ a C : ℝ) : Prop :=
  I.Infinite ∧ 0 < δ ∧ a < Real.pi / 2 ∧
  (∀ J ∈ I, (∀ z ∈ closedStrip (1 / 2 + δ), H J (-z) = H J z) ∧ (∀ t : ℝ, (H J t).im = 0) ∧
      AnalyticOnNhd ℂ (H J) (closedStrip (1 / 2 + δ))) ∧
  (∀ J ∈ I, ∀ z ∈ closedStrip (1 / 2 + δ), ‖H J z‖ ≤ C * Real.exp (a * |z.re|)) ∧
  (∀ J ∈ I, H J 0 = 1) ∧
  (∀ t : ℝ, ∀ ε > 0, ∀ᶠ J in atTop ⊓ 𝓟 I, -ε ≤ (H J t).re) ∧
  (∀ ξ : ℝ, xi2 ≤ ξ → ∀ ε > 0, ∀ᶠ J in atTop ⊓ 𝓟 I,
      -ε ≤ (FT (fun z => Xi z ^ 2 * H J z) ξ).re) ∧
  (∀ n : ℕ, IsPrimePow n →
      Tendsto (fun J => FT (fun z => Xi z ^ 2 * H J z) (xiOf n)) (atTop ⊓ 𝓟 I) (𝓝 0))

end PosRig
