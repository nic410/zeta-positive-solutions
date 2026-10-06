/-
§6: Conjecture 6.1 (the prime-power magic function) as stated in v1.0 (strict part (c)), and the
"Implication" paragraph of §6.1 (the v1.1 form, with the non-strict part (c), is `ConjFamily0` in
`CriterionWeak.lean`):
the conjecture implies (S) and (U), hence `RH ⇔ (E)`.  The proof goes through Remark 4.10(a)
(`remark_4_10a`): part (a) gives (N), part (b) gives the coefficient bound (4.3) with `C = 1`, and part
(c) gives (Mg), because `F̂_J → F̂_∞` pointwise by dominated convergence.
-/
import PositivityRigidity.Criterion

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

/-- **Conjecture 6.1 (prime-power magic function), v1.0 form** (v1.1: `ConjFamily0`, with `F̂_∞ ≥ 0` in
(c); `conjFamily0_of_conjFamily`).
(a) `M_J` is non-singular for every `J ≥ 1`.
(b) For every `J ≥ 10` all coefficients `p_k^{(J)}`, `0 ≤ k ≤ 2J`, are positive, and
`a* := sup_{J ≥ 10} max_{1 ≤ k ≤ 2J} ((2k)! p_k^{(J)})^{1/(2k)} < π/2`.
(c) `P_J → P_∞` coefficientwise, and `F_∞ := Ξ² P_∞(t²)` satisfies `F̂_∞(ξ) > 0` for every
`ξ ∈ [ξ₂, ∞) \ ξ_PP`.

Transcription notes.  In (b), "`a* < π/2`" is written as "some `a < π/2` bounds every
`((2k)! p_k^{(J)})^{1/(2k)}`, `J ≥ 10`, `1 ≤ k ≤ 2J`": if `a* < π/2` take `a = a*`; conversely such an
`a` gives `a* ≤ a < π/2` (the supremum of a bounded set of reals); the roots are real `k`-th roots of
positive numbers by the first half of (b).  In (c), `P_∞` is the power series with the limit
coefficients `pinf k` (`P_J` has `p_k = 0` for `k > 2J`), `P_∞(t²) = Σ' k, pinf k t^{2k}`, and `F̂_∞` is
the transform of the even function `Ξ² P_∞(t²)`, real on `ℝ`, hence real-valued
(`FT_real_of_even_real`), so writing `F̂_∞(ξ) > 0` as `0 < Re F̂_∞(ξ)` changes nothing. -/
def ConjFamily : Prop :=
  (∀ J : ℕ, 1 ≤ J → J ∈ Jset) ∧
  ((∀ J : ℕ, 10 ≤ J → ∀ k ≤ 2 * J, 0 < pcoef J k) ∧
    ∃ a : ℝ, a < Real.pi / 2 ∧ ∀ J : ℕ, 10 ≤ J → ∀ k : ℕ, 1 ≤ k → k ≤ 2 * J →
      (((2 * k).factorial : ℝ) * pcoef J k) ^ ((1 : ℝ) / (2 * k)) ≤ a) ∧
  ∃ pinf : ℕ → ℝ, (∀ k, Tendsto (fun J => pcoef J k) atTop (𝓝 (pinf k))) ∧
    ∀ ξ : ℝ, xi2 ≤ ξ → ξ ∉ xiPP →
      0 < (FT (fun z => Xi z ^ 2 * ∑' k, (pinf k : ℂ) * z ^ (2 * k)) ξ).re

/-! ## Coefficients -/

theorem pcoef_eq_zero_of_gt {J k : ℕ} (hk : 2 * J < k) : pcoef J k = 0 := by
  unfold pcoef
  rw [if_neg (by omega), dif_neg (by omega)]

/-- From `((2k)! p_k)^{1/(2k)} ≤ a` (with `p_k > 0`, `k ≥ 1`) to `p_k ≤ a^{2k}/(2k)!`. -/
theorem pcoef_le_of_root_le {J k : ℕ} {a : ℝ} (hk : 1 ≤ k) (hp : 0 < pcoef J k)
    (h : (((2 * k).factorial : ℝ) * pcoef J k) ^ ((1 : ℝ) / (2 * k)) ≤ a) :
    pcoef J k ≤ a ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  have hfac : (0 : ℝ) < ((2 * k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  set y : ℝ := ((2 * k).factorial : ℝ) * pcoef J k with hy
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hn : (2 * k : ℕ) ≠ 0 := by omega
  have hexp : (1 : ℝ) / (2 * k) = ((2 * k : ℕ) : ℝ)⁻¹ := by push_cast; ring
  rw [hexp] at h
  have hx0 : 0 ≤ y ^ ((2 * k : ℕ) : ℝ)⁻¹ := Real.rpow_nonneg hy0 _
  have hpow : y = (y ^ ((2 * k : ℕ) : ℝ)⁻¹) ^ (2 * k) := (Real.rpow_inv_natCast_pow hy0 hn).symm
  have hle : y ≤ a ^ (2 * k) := by
    rw [hpow]
    exact pow_le_pow_left₀ hx0 h _
  rw [le_div_iff₀ hfac, mul_comm]
  exact hle

/-- Part (b) of the conjecture gives the coefficient bound (4.3) with `J₀ = 10`, `C = 1` and
`a = max a* 0`. -/
theorem conjFamily_bound {a : ℝ}
    (hpos : ∀ J : ℕ, 10 ≤ J → ∀ k ≤ 2 * J, 0 < pcoef J k)
    (hbd : ∀ J : ℕ, 10 ≤ J → ∀ k : ℕ, 1 ≤ k → k ≤ 2 * J →
      (((2 * k).factorial : ℝ) * pcoef J k) ^ ((1 : ℝ) / (2 * k)) ≤ a) :
    ∀ J : ℕ, 10 ≤ J → ∀ k ≤ 2 * J,
      0 ≤ pcoef J k ∧ pcoef J k ≤ 1 * (max a 0) ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  intro J hJ k hk
  refine ⟨(hpos J hJ k hk).le, ?_⟩
  rw [one_mul]
  rcases Nat.eq_zero_or_pos k with h0 | h1
  · subst h0
    simp [pcoef]
  · exact pcoef_le_of_root_le h1 (hpos J hJ k hk) ((hbd J hJ k h1 hk).trans (le_max_left a 0))

/-! ## Pointwise convergence of `H_J` and of `F̂_J` -/

theorem Hfam_eq_tsum (J : ℕ) (z : ℂ) :
    Hfam J z = ∑' k, (pcoef J k : ℂ) * z ^ (2 * k) := by
  rw [tsum_eq_sum (s := Finset.range (2 * J + 1))]
  · simp only [Hfam, Pfam]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← pow_mul]
  · intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [pcoef_eq_zero_of_gt (by omega), Complex.ofReal_zero, zero_mul]

theorem summable_cosh_terms (r : ℝ) :
    Summable (fun k : ℕ => r ^ (2 * k) / ((2 * k).factorial : ℝ)) :=
  (Real.hasSum_cosh r).summable

/-- `H_J(t) → H_∞(t) = Σ' pinf k t^{2k}` for every real `t` (Tannery's theorem, dominated by the
cosh series). -/
theorem Hfam_tendsto {a : ℝ}
    (hP : ∀ J : ℕ, 10 ≤ J → ∀ k ≤ 2 * J,
      0 ≤ pcoef J k ∧ pcoef J k ≤ 1 * a ^ (2 * k) / ((2 * k).factorial : ℝ))
    {pinf : ℕ → ℝ} (hconv : ∀ k, Tendsto (fun J => pcoef J k) atTop (𝓝 (pinf k))) (t : ℝ) :
    Tendsto (fun J => Hfam J t) atTop (𝓝 (∑' k, (pinf k : ℂ) * (t : ℂ) ^ (2 * k))) := by
  simp_rw [Hfam_eq_tsum]
  refine tendsto_tsum_of_dominated_convergence (bound := fun k => (a * |t|) ^ (2 * k) /
    ((2 * k).factorial : ℝ)) (summable_cosh_terms _) (fun k => ?_) ?_
  · exact ((Complex.continuous_ofReal.tendsto _).comp (hconv k)).mul_const _
  · filter_upwards [eventually_ge_atTop 10] with J hJ k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, Complex.norm_real,
      Real.norm_eq_abs]
    by_cases hk : k ≤ 2 * J
    · obtain ⟨h0, h1⟩ := hP J hJ k hk
      rw [abs_of_nonneg h0, mul_pow, mul_div_right_comm]
      rw [one_mul] at h1
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    · rw [pcoef_eq_zero_of_gt (by omega), abs_zero, zero_mul]
      exact div_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _) (by positivity)

/-- `|Ξ(t)|² cosh(a|t|)` is integrable for `0 ≤ a < π/2` (from the ledger axiom `xi_decay`). -/
theorem integrable_Xi_sq_cosh {a : ℝ} (ha0 : 0 ≤ a) (ha : a < Real.pi / 2) :
    Integrable (fun t : ℝ => ‖Xi t‖ ^ 2 * Real.cosh (a * |t|)) := by
  obtain ⟨C, hC⟩ := xi_decay 1 one_pos le_rfl
  have hc : (0 : ℝ) < Real.pi / 2 - a := by linarith
  obtain ⟨K, hK0, hK⟩ := poly_exp_le_inv_sq hc 6
  have hcont : Continuous (fun t : ℝ => ‖Xi t‖ ^ 2 * Real.cosh (a * |t|)) :=
    ((differentiable_Xi.continuous.comp Complex.continuous_ofReal).norm.pow 2).mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_abs))
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (C ^ 2 * K))
    hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have h1 : ‖Xi t‖ ≤ C * (1 + |t|) ^ 3 * Real.exp (-(Real.pi / 4) * |t|) := by
    have := hC (t : ℂ) (by simp)
    simpa using this
  have hXnn : 0 ≤ ‖Xi t‖ := norm_nonneg _
  have hcosh : Real.cosh (a * |t|) ≤ Real.exp (a * |t|) := by
    rw [Real.cosh_eq]
    have : Real.exp (-(a * |t|)) ≤ Real.exp (a * |t|) := by
      apply Real.exp_le_exp.mpr
      have : 0 ≤ a * |t| := mul_nonneg ha0 (abs_nonneg t)
      linarith
    linarith
  have hcpos : 0 ≤ Real.cosh (a * |t|) := (Real.cosh_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖Xi t‖ ^ 2 * Real.cosh (a * |t|)
      ≤ (C * (1 + |t|) ^ 3 * Real.exp (-(Real.pi / 4) * |t|)) ^ 2 * Real.exp (a * |t|) := by
        gcongr
    _ = C ^ 2 * ((1 + |t|) ^ 6 * Real.exp (-(Real.pi / 2 - a) * |t|)) := by
        have he : Real.exp (-(Real.pi / 4) * |t|) ^ 2 * Real.exp (a * |t|) =
            Real.exp (-(Real.pi / 2 - a) * |t|) := by
          rw [sq, ← Real.exp_add, ← Real.exp_add]; ring_nf
        rw [mul_pow, mul_pow, ← pow_mul, mul_assoc, he]; ring
    _ ≤ C ^ 2 * (K * (1 + t ^ 2)⁻¹) := mul_le_mul_of_nonneg_left (hK t) (sq_nonneg C)
    _ = C ^ 2 * K * (1 + t ^ 2)⁻¹ := by ring

/-- `F̂_J(ξ) → F̂_∞(ξ)` for every `ξ`, by dominated convergence (the "Implication" paragraph of §6.1). -/
theorem FT_Ffam_tendsto {a : ℝ} (ha0 : 0 ≤ a) (ha : a < Real.pi / 2)
    (hP : ∀ J : ℕ, 10 ≤ J → ∀ k ≤ 2 * J,
      0 ≤ pcoef J k ∧ pcoef J k ≤ 1 * a ^ (2 * k) / ((2 * k).factorial : ℝ))
    {pinf : ℕ → ℝ} (hconv : ∀ k, Tendsto (fun J => pcoef J k) atTop (𝓝 (pinf k))) (ξ : ℝ) :
    Tendsto (fun J => FT (Ffam J) ξ) atTop
      (𝓝 (FT (fun z => Xi z ^ 2 * ∑' k, (pinf k : ℂ) * z ^ (2 * k)) ξ)) := by
  unfold FT onR
  simp_rw [Real.fourier_real_eq_integral_exp_smul]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => ‖Xi t‖ ^ 2 * Real.cosh (a * |t|)) ?_ ?_ (integrable_Xi_sq_cosh ha0 ha) ?_
  · -- measurability
    refine Eventually.of_forall fun J => Continuous.aestronglyMeasurable ?_
    refine Continuous.smul (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (by fun_prop)).mul continuous_const)) ?_
    exact ((differentiable_Xi.continuous.comp Complex.continuous_ofReal).pow 2).mul
      ((differentiable_Hfam J).continuous.comp Complex.continuous_ofReal)
  · -- domination
    filter_upwards [eventually_ge_atTop 10] with J hJ
    refine Eventually.of_forall fun t => ?_
    have hH := (coeff_bound_consequences (fun k hk => (hP J hJ k hk).1)
      (fun k hk => (hP J hJ k hk).2)).2 (t : ℂ)
    rw [one_mul, Complex.norm_real, Real.norm_eq_abs] at hH
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
    show ‖Xi t ^ 2 * Hfam J t‖ ≤ ‖Xi t‖ ^ 2 * Real.cosh (a * |t|)
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left hH (by positivity)
  · -- pointwise convergence
    refine Eventually.of_forall fun t => ?_
    exact ((Hfam_tendsto hP hconv t).const_mul (Xi t ^ 2)).const_smul _

/-! ## The implication -/

/-- **Conjecture 6.1 ⇒ (S), (U), v1.0 form** (the "Implication" paragraph of §6.1).  The conjecture implies (S)
and (U) unconditionally, hence `RH ⇔ (E)`; under either, `κ* = 0` and `𝒦 = {p_ζ}`. -/
theorem conjFamily_implies (h : ConjFamily) :
    CondS ∧ CondU ∧ (RiemannHypothesis ↔ CondE) ∧
      (RiemannHypothesis ∨ CondE → kappaStar = 0 ∧ K = {pZeta}) := by
  obtain ⟨ha, ⟨hpos, a, ha_lt, hbd⟩, pinf, hconv, hFpos⟩ := h
  -- (a) ⇒ (N)
  have hN : HypN := Set.infinite_of_forall_exists_gt fun n => ⟨n + 1, ha (n + 1) (by omega), by omega⟩
  -- (b) ⇒ (POS_a) with `J₀ = 10`, `C = 1`
  have hP := conjFamily_bound hpos hbd
  have ha0 : 0 ≤ max a 0 := le_max_right a 0
  have ha' : max a 0 < Real.pi / 2 := max_lt ha_lt (by have := Real.pi_pos; positivity)
  have hPOS : HypPOS := ⟨10, 1, max a 0, ha0, ha', fun J _ hJ k hk => hP J hJ k hk⟩
  -- (c) ⇒ (Mg)
  have hMg : HypMg := by
    intro ξ hξ hpp
    have hL := hFpos ξ hξ hpp
    set L := (FT (fun z => Xi z ^ 2 * ∑' k, (pinf k : ℂ) * z ^ (2 * k)) ξ).re with hLdef
    have hlim : Tendsto (fun J => (FT (Ffam J) ξ).re) atTop (𝓝 L) :=
      (Complex.continuous_re.tendsto _).comp (FT_Ffam_tendsto ha0 ha' hP hconv ξ)
    refine ⟨L / 2, by positivity, ?_⟩
    have hev : ∀ᶠ J in atTop, L / 2 ≤ (FT (Ffam J) ξ).re :=
      (hlim.eventually (lt_mem_nhds (by linarith : L / 2 < L))).mono fun J hJ => hJ.le
    exact hev.filter_mono inf_le_left
  exact remark_4_10a hN hPOS hMg

end PosRig
