/-
Corollary 5.3 (near-criticality forces near-rigidity): every admissible pair has
`∫ Ξ² dμ ≤ 3.99 · 10^{-1060}`, hence `μ(I) ≤ 3.99 · 10^{-1060}/min_I Ξ²` for every compact interval
`I ⊂ ℝ \ Z_ζ`: the exact member `F₁₁₁ ∈ 𝒞` of Theorem 5.1 satisfies `F₁₁₁ ≥ Ξ²` (`P₁₁₁(0) = 1` and every
coefficient of `P₁₁₁` is positive, Proposition 5.6, ledger axiom `cert_finiteJ`), and weak duality (Lemma 2.5)
gives `∫ Ξ² dμ ≤ ∫ F₁₁₁ dμ ≤ 𝒜(F₁₁₁) ≤ 3.98510732132 · 10^{-1060}` (Paper I, Corollary 5.3 and its proof; the
facts about `F₁₁₁` are `exact111_near_rigidity`, `ExactMember.lean`).
-/
import PositivityRigidity.ExactMember

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

/-- **Corollary 5.3 (near-criticality forces near-rigidity), first sentence (v1.2).**  Every admissible pair
has `∫ Ξ² dμ ≤ 3.99 · 10^{-1060}` (and `Ξ²` is `μ`-integrable): by weak duality,
`∫ Ξ² dμ ≤ ∫ F₁₁₁ dμ ≤ 𝒜(F₁₁₁)` for the exact member `F₁₁₁ ∈ 𝒞`, `F₁₁₁ ≥ Ξ²`, of Theorem 5.1.
(With `condU_iff_Xi_sq`: (U) holds iff the bound can be improved to `0` for every admissible pair.) -/
theorem near_rigidity : ∀ p ∈ K, Integrable (fun t : ℝ => (Xi t ^ 2).re) p.μ ∧
    ∫ t, (Xi t ^ 2).re ∂p.μ ≤ (399 : ℝ) / 10 ^ 1062 := by
  intro p hp
  obtain ⟨hcone, hge, hA⟩ := exact111_near_rigidity
  set F := Ffam 111 with hFdef
  have hintF : Integrable (fun t : ℝ => (F t).re) p.μ := (hp.integrable_re hcone.1).1
  have hintXi : Integrable (fun t : ℝ => (Xi t ^ 2).re) p.μ := by
    refine hintF.mono' continuous_Xi_sq_re.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Xi_sq_re_nonneg t)]
    exact hge t
  refine ⟨hintXi, ?_⟩
  calc ∫ t, (Xi t ^ 2).re ∂p.μ ≤ ∫ t, (F t).re ∂p.μ := integral_mono hintXi hintF hge
    _ ≤ Arch F := integral_le_Arch hp hcone
    _ ≤ (399 : ℝ) / 10 ^ 1062 := hA

/-- **Corollary 5.3, second sentence (v1.2).**  For every admissible pair and every compact interval
`I = [a, b] ⊂ ℝ \ Z_ζ`, `μ(I) ≤ 3.99 · 10^{-1060} / min_I Ξ²`; the minimum is attained at some `t₀ ∈ I` and is
positive. -/
theorem near_rigidity_interval {p : Pair} (hp : p ∈ K) {a b : ℝ} (hab : a ≤ b)
    (hI : Disjoint (Set.Icc a b) Zzeta) :
    ∃ t₀ ∈ Set.Icc a b, (∀ t ∈ Set.Icc a b, (Xi t₀ ^ 2).re ≤ (Xi t ^ 2).re) ∧
      0 < (Xi t₀ ^ 2).re ∧ p.μ.real (Set.Icc a b) ≤ ((399 : ℝ) / 10 ^ 1062) / (Xi t₀ ^ 2).re := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hab)
    continuous_Xi_sq_re.continuousOn
  have hpos : 0 < (Xi t₀ ^ 2).re := (Xi_sq_re_pos_iff t₀).mpr (Set.disjoint_left.mp hI ht₀)
  refine ⟨t₀, ht₀, fun t ht => hmin ht, hpos, ?_⟩
  obtain ⟨hlfμ, -⟩ := Admissible.isLocallyFinite hp
  obtain ⟨hcone, hge, hA⟩ := exact111_near_rigidity
  set F := Ffam 111 with hFdef
  have hw := weak_duality hp hcone measurableSet_Icc MeasurableSet.empty
    (a := (Xi t₀ ^ 2).re) (b := 0) hpos.le le_rfl
    (fun t ht => (hmin ht).trans (hge t)) (by simp)
  simp only [zero_div, ENNReal.ofReal_zero, zero_mul, add_zero] at hw
  have hfin : p.μ (Set.Icc a b) ≠ ⊤ := (isCompact_Icc.measure_lt_top).ne
  have hA0 : 0 ≤ Arch F := weak_duality_nonneg hp hcone
  rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hpos.le,
    ENNReal.ofReal_le_ofReal_iff hA0] at hw
  rw [le_div_iff₀ hpos, mul_comm]
  exact hw.trans hA

end PosRig
