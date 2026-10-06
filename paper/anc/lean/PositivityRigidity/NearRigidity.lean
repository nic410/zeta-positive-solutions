/-
v1.1: Corollary 5.3 (near-criticality forces near-rigidity).  Every admissible pair has
`∫ Ξ² dμ ≤ 3.21 · 10^{-906}`, hence `μ(I) ≤ 3.21 · 10^{-906}/min_I Ξ²` for every compact interval
`I ⊂ ℝ \ Z_ζ`: the certified `F_rep` of Theorem 5.1 at `J = 100` has `H ≥ 1` (all coefficients of `P` are
non-negative, ledger axiom `cert_near_rigidity`), hence `F_rep ≥ Ξ²`, and weak duality (Lemma 2.5) gives
`∫ Ξ² dμ ≤ ∫ F_rep dμ ≤ 𝒜(F_rep)` (Paper I, Corollary 5.3 and its proof).
-/
import PositivityRigidity.ZeroSupport

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

/-- `H(t) = P(t²)`: the product of `Frep` evaluated at a real point is `P(t²)`. -/
theorem Hpoly_eval₂ {J : ℕ} (r s : Fin J → ℚ) (t : ℝ) :
    (Hpoly r s).eval₂ (algebraMap ℚ ℝ) (t ^ 2) =
      ∏ j, (1 + (r j : ℝ) * t ^ 2 + (s j : ℝ) * t ^ 4) := by
  unfold Hpoly
  rw [Polynomial.eval₂_finsetProd]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.eval₂_pow]
  simp only [eq_ratCast]
  ring

/-- `P(0) = 1`. -/
theorem Hpoly_coeff_zero {J : ℕ} (r s : Fin J → ℚ) : (Hpoly r s).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold Hpoly
  rw [Polynomial.eval_prod]
  simp

/-- A polynomial with non-negative rational coefficients and `P(0) = 1` is `≥ 1` on `[0, ∞)`. -/
theorem one_le_eval₂_of_coeff_nonneg {P : Polynomial ℚ} (hcoef : ∀ k, 0 ≤ P.coeff k)
    (h0 : P.coeff 0 = 1) {u : ℝ} (hu : 0 ≤ u) : 1 ≤ P.eval₂ (algebraMap ℚ ℝ) u := by
  rw [Polynomial.eval₂_eq_sum_range]
  have hterm : ∀ i ∈ Finset.range (P.natDegree + 1), 0 ≤ (algebraMap ℚ ℝ) (P.coeff i) * u ^ i := by
    intro i _
    have : (0 : ℝ) ≤ (algebraMap ℚ ℝ) (P.coeff i) := by
      rw [eq_ratCast]
      exact_mod_cast hcoef i
    positivity
  have h := Finset.single_le_sum hterm (Finset.mem_range.mpr (Nat.succ_pos P.natDegree))
  simpa [h0] using h

/-- `H ≥ 1` on `ℝ` for a ladder function with non-negative coefficients of `P`. -/
theorem one_le_H {J : ℕ} {r s : Fin J → ℚ} (hcoef : ∀ k, 0 ≤ (Hpoly r s).coeff k) (t : ℝ) :
    1 ≤ ∏ j, (1 + (r j : ℝ) * t ^ 2 + (s j : ℝ) * t ^ 4) := by
  rw [← Hpoly_eval₂]
  exact one_le_eval₂_of_coeff_nonneg hcoef (Hpoly_coeff_zero r s) (by positivity)

/-- `F_rep` on the real line, as a real number. -/
theorem Frep_ofReal {J : ℕ} (r s : Fin J → ℚ) (ε : ℚ) (t : ℝ) :
    Frep r s ε t = (((Xi t).re ^ 2 * ((∏ j, (1 + (r j : ℝ) * t ^ 2 + (s j : ℝ) * t ^ 4)) +
      (ε : ℝ) * Real.exp (-Real.pi * t ^ 2)) : ℝ) : ℂ) := by
  set x := (Xi t).re with hx
  have hX : Xi t = (x : ℂ) := Complex.ext (by simp [hx]) (by simp [Xi_real t])
  unfold Frep
  rw [hX]
  push_cast
  rfl

/-- **`F_rep ≥ Ξ²` on `ℝ`** (`H ≥ 1`, `ε ≥ 0`). -/
theorem Frep_ge_Xi_sq {J : ℕ} {r s : Fin J → ℚ} (hcoef : ∀ k, 0 ≤ (Hpoly r s).coeff k) {ε : ℚ}
    (hε : 0 ≤ ε) (t : ℝ) : (Xi t ^ 2).re ≤ (Frep r s ε t).re := by
  rw [Frep_ofReal, Complex.ofReal_re, Xi_sq_re]
  have h1 := one_le_H hcoef t
  have h2 : (0 : ℝ) ≤ (ε : ℝ) * Real.exp (-Real.pi * t ^ 2) := by
    have : (0 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hε
    positivity
  have h3 : 0 ≤ (Xi t).re ^ 2 := sq_nonneg _
  nlinarith

/-- **Corollary 5.3 (near-criticality forces near-rigidity), first sentence.**  Every admissible pair has
`∫ Ξ² dμ ≤ 3.21 · 10^{-906}` (and `Ξ²` is `μ`-integrable): by weak duality,
`∫ Ξ² dμ ≤ ∫ F_rep dμ ≤ 𝒜(F_rep)` for the certified `F_rep ≥ Ξ²` of Theorem 5.1 at `J = 100`.
(With `condU_iff_Xi_sq`: (U) holds iff the bound can be improved to `0` for every admissible pair.) -/
theorem near_rigidity : ∀ p ∈ K, Integrable (fun t : ℝ => (Xi t ^ 2).re) p.μ ∧
    ∫ t, (Xi t ^ 2).re ∂p.μ ≤ (321 : ℝ) / 10 ^ 908 := by
  intro p hp
  obtain ⟨r, s, hcoef, hcone, hA⟩ := cert_near_rigidity
  set F := Frep r s (1 / 10 ^ 911) with hFdef
  have hge : ∀ t : ℝ, (Xi t ^ 2).re ≤ (F t).re := Frep_ge_Xi_sq hcoef (by positivity)
  have hintF : Integrable (fun t : ℝ => (F t).re) p.μ := (hp.integrable_re hcone.1).1
  have hintXi : Integrable (fun t : ℝ => (Xi t ^ 2).re) p.μ := by
    refine hintF.mono' continuous_Xi_sq_re.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Xi_sq_re_nonneg t)]
    exact hge t
  refine ⟨hintXi, ?_⟩
  calc ∫ t, (Xi t ^ 2).re ∂p.μ ≤ ∫ t, (F t).re ∂p.μ := integral_mono hintXi hintF hge
    _ ≤ Arch F := integral_le_Arch hp hcone
    _ ≤ (321 : ℝ) / 10 ^ 908 := hA

/-- **Corollary 5.3, second sentence.**  For every admissible pair and every compact interval
`I = [a, b] ⊂ ℝ \ Z_ζ`, `μ(I) ≤ 3.21 · 10^{-906} / min_I Ξ²`; the minimum is attained at some `t₀ ∈ I` and is
positive. -/
theorem near_rigidity_interval {p : Pair} (hp : p ∈ K) {a b : ℝ} (hab : a ≤ b)
    (hI : Disjoint (Set.Icc a b) Zzeta) :
    ∃ t₀ ∈ Set.Icc a b, (∀ t ∈ Set.Icc a b, (Xi t₀ ^ 2).re ≤ (Xi t ^ 2).re) ∧
      0 < (Xi t₀ ^ 2).re ∧ p.μ.real (Set.Icc a b) ≤ ((321 : ℝ) / 10 ^ 908) / (Xi t₀ ^ 2).re := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hab)
    continuous_Xi_sq_re.continuousOn
  have hpos : 0 < (Xi t₀ ^ 2).re := (Xi_sq_re_pos_iff t₀).mpr (Set.disjoint_left.mp hI ht₀)
  refine ⟨t₀, ht₀, fun t ht => hmin ht, hpos, ?_⟩
  obtain ⟨hlfμ, -⟩ := Admissible.isLocallyFinite hp
  obtain ⟨r, s, hcoef, hcone, hA⟩ := cert_near_rigidity
  set F := Frep r s (1 / 10 ^ 911) with hFdef
  have hw := weak_duality hp hcone measurableSet_Icc MeasurableSet.empty
    (a := (Xi t₀ ^ 2).re) (b := 0) hpos.le le_rfl
    (fun t ht => (hmin ht).trans (Frep_ge_Xi_sq hcoef (by positivity) t)) (by simp)
  simp only [zero_div, ENNReal.ofReal_zero, zero_mul, add_zero] at hw
  have hfin : p.μ (Set.Icc a b) ≠ ⊤ := (isCompact_Icc.measure_lt_top).ne
  have hA0 : 0 ≤ Arch F := weak_duality_nonneg hp hcone
  rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hpos.le,
    ENNReal.ofReal_le_ofReal_iff hA0] at hw
  rw [le_div_iff₀ hpos, mul_comm]
  exact hw.trans hA

end PosRig
