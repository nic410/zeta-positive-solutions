/-
Non-vacuity and sanity checks (`scripts/audit.sh`, check (f)).  Run (after `lake build`):
  lake env lean scripts/NonVacuity.lean

The headline theorems quantify over the test class `𝒯`, the cones `𝒞`, `𝒞_OPS`, `𝒢`, admissible pairs and
the normalised cone elements that define `κ*`; they would be vacuous (or the slacks junk) if these were
empty, and the ledger axioms of the form `(∀ F ∈ X, …) → …` would be too strong.  This file restates, from
the sanity lemmas of the library (`Sanity.lean`, `Faithful.lean`, `Duality.lean`, `EFCheck.lean`, and the v1.1
and v1.2 files), that none of this happens, and that the hypotheses of the v1.1 and v1.2 results can be met:

* `𝒯`, `𝒞`, `𝒞_OPS`, `𝒞 ∩ 𝒢` contain the Gaussian, which has `∫ = 1` (so `κ* < ∞`), and `𝒢 ⊆ 𝒯`;
* admissible pairs are Radon; `Arch` is the paper's complex `𝒜` on `𝒯`; Mathlib's `RiemannHypothesis` is the
  paper's RH; the conclusion of the `explicit_formula` axiom holds on a Paley–Wiener subclass of `𝒯`
  (Zeta23, no ledger axiom);
* v1.1: the summability condition (3.5) of Theorem 3.8 holds for every finite `E` (weighted and cumulative
  forms), and its weighted form implies the cumulative one; `∫ Ξ² dμ = 0` forces `μ` onto `Z_ζ`, and `μ_ζ` is
  carried by `Z_ζ ∪ {0}` (the hypothesis of `zero_support_rigidity` holds for `p_ζ`); `Z_ζ` is closed;
* v1.2: the certified coefficient property of Proposition 5.6 (`cert_finiteJ`: every coefficient of `P_J` is
  positive) gives `F_J ≥ Ξ²`, as Corollary 5.3 uses for `F₁₁₁`.

Every theorem here must depend only on `propext`, `Classical.choice` and `Quot.sound` (no ledger axiom); the
`#print axioms` lines at the end are checked by `scripts/audit.sh`.
-/
import PositivityRigidity

open MeasureTheory Filter
open scoped ENNReal

namespace PosRig.NonVacuity

/-- `𝒯`, `𝒞`, `𝒞_OPS` and `𝒞 ∩ 𝒢` are non-empty: they contain the Gaussian `e^{−πt²}`, and `𝒢 ⊆ 𝒯`. -/
theorem classes_nonempty :
    gauss ∈ TestClass ∧ gauss ∈ Cone ∧ gauss ∈ ConeOPS ∧ gauss ∈ Cone ∩ Gset ∧ Gset ⊆ TestClass :=
  ⟨gauss_mem_TestClass, gauss_mem_Cone, gauss_mem_ConeOPS, ⟨gauss_mem_Cone, gauss_mem_Gset⟩,
    Gset_subset_TestClass⟩

/-- The normalised cone elements that define `κ*` exist (`∫ gauss = 1`), so `κ* < ∞` is not a junk value. -/
theorem kappaStar_index_nonempty : (gauss ∈ Cone ∧ intR gauss = 1) ∧ kappaStar ≠ ⊤ :=
  ⟨⟨gauss_mem_Cone, intR_gauss⟩, kappaStar_ne_top⟩

/-- Admissible pairs (for any functional and gap) are Radon. -/
theorem admissible_radon {A : (ℂ → ℂ) → ℝ} {g : ℝ} {p : Pair} (hp : Admissible A g p) :
    IsLocallyFiniteMeasure p.μ ∧ IsLocallyFiniteMeasure p.ν :=
  Admissible.isLocallyFinite hp

/-- `Arch` is the paper's (complex) `𝒜` on `𝒯`. -/
theorem arch_faithful {F : ℂ → ℂ} (hF : F ∈ TestClass) :
    ((Arch F : ℝ) : ℂ) = F (Complex.I / 2) + F (-Complex.I / 2) + ∫ t : ℝ, F t * (Ωinf t : ℂ) :=
  TestClass.Arch_eq_paper hF

/-- Mathlib's `RiemannHypothesis` is "every zero in the open critical strip has real part `1/2`". -/
theorem rh_faithful : RiemannHypothesis ↔ ∀ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 :=
  RH_iff_critical

/-- The conclusion of the ledger axiom `explicit_formula`, proved without it on the Paley–Wiener subclass
`F = paperFT k`, `k ∈ C_c²` even and real (from Zeta23). -/
theorem explicit_formula_check (k : ℝ → ℂ) (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (heven : ∀ u, k (-u) = k u) (hreal : ∀ u, (k u).im = 0) :
    Summable (fun ρ : NontrivialZeros => (mult ρ : ℂ) * Zeta23.paperFT k (tOf ρ)) ∧
    Summable (fun n : ℕ =>
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * FT (Zeta23.paperFT k) (xiOf n)) ∧
    ((Arch (Zeta23.paperFT k) : ℝ) : ℂ) =
      (∑' ρ : NontrivialZeros, (mult ρ : ℂ) * Zeta23.paperFT k (tOf ρ)) +
        (1 / Real.pi : ℂ) * ∑' n : ℕ,
          ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * FT (Zeta23.paperFT k) (xiOf n) :=
  explicit_formula_of_paleyWiener k hk hkc heven hreal _ rfl

/-- v1.1, Theorem 3.8: the summability condition (3.5) holds, in both forms, for every finite `E`. -/
theorem summability_finite {E : Set ℝ} (hE : E.Finite) (w : ℝ → ℝ) :
    WeightedCond E w ∧ CumulativeCond E w :=
  ⟨weightedCond_of_finite hE w, cumulativeCond_of_weightedCond (weightedCond_of_finite hE w)⟩

/-- v1.1, (3.5): the weighted form implies the cumulative form. -/
theorem summability_weighted_cumulative {E : Set ℝ} {w : ℝ → ℝ} (h : WeightedCond E w) :
    CumulativeCond E w :=
  cumulativeCond_of_weightedCond h

/-- v1.2, Corollary 5.3: the certified coefficient property of Proposition 5.6 (non-negative coefficients of
`P_J`) gives `F_J ≥ Ξ²` on `ℝ`. -/
theorem near_rigidity_certificate_meaning {J : ℕ} (hpos : ∀ k ≤ 2 * J, 0 ≤ pcoef J k) (t : ℝ) :
    (Xi t ^ 2).re ≤ (Ffam J t).re :=
  Ffam_ge_Xi_sq hpos t

/-- v1.1, Corollary 4.11: `∫ Ξ² dμ = 0` forces `μ` onto `Z_ζ`; `Z_ζ` is closed. -/
theorem xi_sq_support {μ : Measure ℝ} (h : ∫⁻ t, ENNReal.ofReal (Xi t ^ 2).re ∂μ = 0) :
    CarriedBy μ Zzeta ∧ IsClosed Zzeta :=
  ⟨carriedBy_Zzeta_of_lintegral h, isClosed_Zzeta⟩

/-- v1.1, Theorem 3.6: `μ_ζ` satisfies the support hypothesis of `zero_support_rigidity`, and `ν_ζ` is
its conclusion (so the axiom is consistent with `p_ζ`; `p_ζ ∈ 𝒦` under RH is `pZeta_mem_K_of_RH`). -/
theorem zero_support_hypothesis_pZeta :
    CarriedBy pZeta.μ (Zzeta ∪ {0}) ∧ pZeta.ν = nuZeta :=
  ⟨measure_mono_null (Set.compl_subset_compl.mpr Set.subset_union_left) muZeta_carriedBy, rfl⟩

end PosRig.NonVacuity

#print axioms PosRig.NonVacuity.classes_nonempty
#print axioms PosRig.NonVacuity.kappaStar_index_nonempty
#print axioms PosRig.NonVacuity.admissible_radon
#print axioms PosRig.NonVacuity.arch_faithful
#print axioms PosRig.NonVacuity.rh_faithful
#print axioms PosRig.NonVacuity.explicit_formula_check
#print axioms PosRig.NonVacuity.summability_finite
#print axioms PosRig.NonVacuity.summability_weighted_cumulative
#print axioms PosRig.NonVacuity.near_rigidity_certificate_meaning
#print axioms PosRig.NonVacuity.xi_sq_support
#print axioms PosRig.NonVacuity.zero_support_hypothesis_pZeta
