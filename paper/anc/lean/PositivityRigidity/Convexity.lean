/-
Theorem 2.7(b) (convexity of `𝒦`) and the consequences of Proposition 5.11 (some admissible pair has a
zero measure `≥ c dt`; the set of admissible pairs is not a singleton), from the ledger axioms
`cert_Qsqrt5_pair`, `cert_Qsqrtm3_pair` (via the natural-gap step) and the perturbation in the proof of
Proposition 5.11(a).
-/
import PositivityRigidity.Certified
import PositivityRigidity.Faithful

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal NNReal

namespace PosRig

/-! ## Theorem 2.7(b): convexity -/

/-- **Theorem 2.7(b), convexity.**  A convex combination of two pairs admissible for `A` at the gap `g`
is admissible for `A` at `g`. -/
theorem Kset_convex (A : (ℂ → ℂ) → ℝ) (g : ℝ) {p₁ p₂ : Pair} (h₁ : Admissible A g p₁)
    (h₂ : Admissible A g p₂) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Admissible A g ⟨ENNReal.ofReal t • p₁.μ + ENNReal.ofReal (1 - t) • p₂.μ,
      ENNReal.ofReal t • p₁.ν + ENNReal.ofReal (1 - t) • p₂.ν⟩ := by
  obtain ⟨he₁, hc₁, hi₁⟩ := h₁
  obtain ⟨he₂, hc₂, hi₂⟩ := h₂
  have ht1' : 0 ≤ 1 - t := by linarith
  refine ⟨?_, ?_, ?_⟩
  · show Measure.map (fun x : ℝ => -x) (ENNReal.ofReal t • p₁.μ + ENNReal.ofReal (1 - t) • p₂.μ) =
      ENNReal.ofReal t • p₁.μ + ENNReal.ofReal (1 - t) • p₂.μ
    unfold EvenMeasure at he₁ he₂
    rw [Measure.map_add _ _ measurable_neg, Measure.map_smul, Measure.map_smul, he₁, he₂]
  · show (ENNReal.ofReal t • p₁.ν + ENNReal.ofReal (1 - t) • p₂.ν) (Set.Ici g)ᶜ = 0
    unfold CarriedBy at hc₁ hc₂
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hc₁, hc₂]
    simp
  · intro F hF
    obtain ⟨a1, b1, c1⟩ := hi₁ F hF
    obtain ⟨a2, b2, c2⟩ := hi₂ F hF
    have a1' := a1.smul_measure (ENNReal.ofReal_ne_top (r := t))
    have a2' := a2.smul_measure (ENNReal.ofReal_ne_top (r := 1 - t))
    have b1' := b1.smul_measure (ENNReal.ofReal_ne_top (r := t))
    have b2' := b2.smul_measure (ENNReal.ofReal_ne_top (r := 1 - t))
    refine ⟨a1'.add_measure a2', b1'.add_measure b2', ?_⟩
    show ((A F : ℝ) : ℂ) = (∫ x, onR F x ∂(ENNReal.ofReal t • p₁.μ + ENNReal.ofReal (1 - t) • p₂.μ)) +
      (1 / Real.pi : ℂ) * ∫ ξ, FT F ξ ∂(ENNReal.ofReal t • p₁.ν + ENNReal.ofReal (1 - t) • p₂.ν)
    rw [integral_add_measure a1' a2', integral_smul_measure, integral_smul_measure,
      integral_add_measure b1' b2', integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal ht0, ENNReal.toReal_ofReal ht1']
    have c1' : ((A F : ℝ) : ℂ) = (∫ x, onR F x ∂p₁.μ) + (1 / Real.pi : ℂ) * ∫ ξ, FT F ξ ∂p₁.ν := c1
    have c2' : ((A F : ℝ) : ℂ) = (∫ x, onR F x ∂p₂.μ) + (1 / Real.pi : ℂ) * ∫ ξ, FT F ξ ∂p₂.ν := c2
    simp only [Complex.real_smul]
    push_cast
    linear_combination (t : ℂ) * c1' + (1 - (t : ℂ)) * c2'

/-- **Theorem 2.7(b), convexity of `𝒦`.** -/
theorem K_convex {p₁ p₂ : Pair} (h₁ : p₁ ∈ K) (h₂ : p₂ ∈ K) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (⟨ENNReal.ofReal t • p₁.μ + ENNReal.ofReal (1 - t) • p₂.μ,
      ENNReal.ofReal t • p₁.ν + ENNReal.ofReal (1 - t) • p₂.ν⟩ : Pair) ∈ K :=
  Kset_convex Arch xi2 h₁ h₂ ht0 ht1

/-! ## Proposition 5.11: not a singleton -/

theorem sigmaFinite_ofReal_smul_volume (c : ℝ) :
    SigmaFinite (ENNReal.ofReal c • (volume : Measure ℝ)) := by
  rw [show ENNReal.ofReal c = ((Real.toNNReal c : ℝ≥0) : ℝ≥0∞) from rfl, ← ENNReal.smul_def]
  infer_instance

theorem evenMeasure_ofReal_smul_volume (c : ℝ) :
    EvenMeasure (ENNReal.ofReal c • (volume : Measure ℝ)) := by
  unfold EvenMeasure
  rw [Measure.map_smul]
  congr 1
  exact Measure.IsNegInvariant.neg_eq_self (μ := (volume : Measure ℝ))

/-- A measure dominating `c dt` (`c ≥ 0`) is `ρ + c dt` for some measure `ρ` (decomposition over the
unit intervals `[n, n+1)`, on which `c dt` is finite). -/
theorem exists_add_of_dominatesLeb {μ : Measure ℝ} {c : ℝ} (hdom : DominatesLeb μ c) :
    ∃ ρ : Measure ℝ, ρ + ENNReal.ofReal c • (volume : Measure ℝ) = μ := by
  set Y : Measure ℝ := ENNReal.ofReal c • (volume : Measure ℝ) with hY
  set P : ℤ → Set ℝ := fun n => Set.Ico (n : ℝ) (n + 1) with hP
  have hPm : ∀ n, MeasurableSet (P n) := fun n => measurableSet_Ico
  have hPd : Pairwise (Function.onFun Disjoint P) := Set.pairwise_disjoint_Ico_intCast ℝ
  have hPu : (⋃ n, P n) = Set.univ := iUnion_Ico_intCast ℝ
  have hfin : ∀ n, IsFiniteMeasure (Y.restrict (P n)) := by
    intro n
    rw [isFiniteMeasure_restrict, hY, Measure.smul_apply, Real.volume_Ico, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hle : ∀ n, Y.restrict (P n) ≤ μ.restrict (P n) := fun n => Measure.restrict_mono subset_rfl hdom
  have hsplit : ∀ m : Measure ℝ, m = Measure.sum fun n => m.restrict (P n) := by
    intro m
    rw [← Measure.restrict_iUnion hPd hPm, hPu, Measure.restrict_univ]
  refine ⟨Measure.sum fun n => μ.restrict (P n) - Y.restrict (P n), ?_⟩
  calc (Measure.sum fun n => μ.restrict (P n) - Y.restrict (P n)) + Y
      = (Measure.sum fun n => μ.restrict (P n) - Y.restrict (P n)) +
          Measure.sum (fun n => Y.restrict (P n)) := by rw [← hsplit Y]
    _ = Measure.sum (fun n => μ.restrict (P n)) := by
        rw [Measure.sum_add_sum]
        congr 1
        funext n
        have := hfin n
        exact Measure.sub_add_cancel_of_le (hle n)
    _ = μ := (hsplit μ).symm

/-- If `ρ + c dt` is even, so is `ρ` (cancellation of the σ-finite measure `c dt`). -/
theorem evenMeasure_of_add_leb {ρ μ : Measure ℝ} {c : ℝ}
    (h : ρ + ENNReal.ofReal c • (volume : Measure ℝ) = μ) (hμ : EvenMeasure μ) : EvenMeasure ρ := by
  have := sigmaFinite_ofReal_smul_volume c
  have hY := evenMeasure_ofReal_smul_volume c
  unfold EvenMeasure at hμ hY ⊢
  have key : Measure.map (fun t : ℝ => -t) ρ + ENNReal.ofReal c • (volume : Measure ℝ) =
      ρ + ENNReal.ofReal c • (volume : Measure ℝ) := by
    conv_lhs => rw [← hY]
    rw [← Measure.map_add _ _ measurable_neg, h, hμ]
  exact (Measure.add_left_inj _ _ _).mp key

/-- Lebesgue measure with an even density is even. -/
theorem evenMeasure_withDensity {d : ℝ → ℝ≥0∞} (heven : ∀ x, d (-x) = d x) :
    EvenMeasure ((volume : Measure ℝ).withDensity d) := by
  unfold EvenMeasure
  ext s hs
  rw [Measure.map_apply measurable_neg hs, withDensity_apply _ (measurable_neg hs),
    withDensity_apply _ hs, ← lintegral_indicator (measurable_neg hs), ← lintegral_indicator hs,
    ← lintegral_neg_eq_self (μ := (volume : Measure ℝ)) (s.indicator d)]
  congr 1
  funext x
  by_cases hx : -x ∈ s
  · rw [Set.indicator_of_mem (show x ∈ (fun t : ℝ => -t) ⁻¹' s from hx), Set.indicator_of_mem hx,
      heven]
  · rw [Set.indicator_of_notMem (show x ∉ (fun t : ℝ => -t) ⁻¹' s from hx),
      Set.indicator_of_notMem hx]

/-- For `F ∈ 𝒯` (even and real on `ℝ`), `F̂(ξ) = ∫ cos(2πξt) F(t) dt`. -/
theorem FT_eq_integral_cos {F : ℂ → ℂ} (hF : F ∈ TestClass) (ξ : ℝ) :
    FT F ξ = ∫ t : ℝ, ((Real.cos (2 * Real.pi * ξ * t) : ℝ) : ℂ) * F t := by
  have hreal : ∀ t : ℝ, F t = (((F t).re : ℝ) : ℂ) := fun t =>
    Complex.ext (by simp) (by simp [TestClass.real hF t])
  have hint : Integrable (onR F) := TestClass.integrable hF
  -- the right side is real
  have hR : (∫ t : ℝ, ((Real.cos (2 * Real.pi * ξ * t) : ℝ) : ℂ) * F t) =
      ((∫ t : ℝ, Real.cos (2 * Real.pi * ξ * t) * (F t).re : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext t
    rw [hreal t]
    push_cast
    simp
  -- the left side is real, and its real part is the cosine integral
  have hL : FT F ξ = (((FT F ξ).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [TestClass.FT_real hF ξ])
  rw [hR, hL]
  congr 1
  have hint' : Integrable (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) • onR F v) := by
    refine Integrable.mono' hint.norm ?_ ?_
    · exact Continuous.aestronglyMeasurable
        ((Complex.continuous_exp.comp (by fun_prop)).smul (TestClass.continuous hF))
    · exact Eventually.of_forall fun v => by
        rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hre := integral_re hint'
  simp only [RCLike.re_to_complex] at hre
  unfold FT
  rw [Real.fourier_real_eq_integral_exp_smul, ← hre]
  congr 1
  funext v
  simp only [onR, smul_eq_mul]
  rw [hreal v, Complex.re_mul_ofReal]
  rw [show (↑(-2 * Real.pi * v * ξ) * Complex.I) = (((-2 * Real.pi * v * ξ : ℝ)) : ℂ) * Complex.I from rfl,
    Complex.exp_ofReal_mul_I_re]
  rw [show -2 * Real.pi * v * ξ = -(2 * Real.pi * ξ * v) by ring, Real.cos_neg]
  simp [Complex.ofReal_re]

/-- **Perturbation (proof of Proposition 5.11(a)).**  A pair admissible for `𝒜_{𝔤,q}` at a gap `g` whose
zero measure dominates `c dt`, `c > 0`, is not the only admissible pair: adding an atom `w δ_g` to `ν`
(`w = πc/2`) and subtracting the density `(w/π) cos(2πg t)` from `μ` gives another one. -/
theorem not_unique_of_dominates {ks : List ℕ} {q g c : ℝ} (_hg : 0 < g) {p : Pair}
    (hp : Admissible (ArchG ks q) g p) (hc : 0 < c) (hdom : DominatesLeb p.μ c) :
    ∃ p' : Pair, Admissible (ArchG ks q) g p' ∧ p' ≠ p := by
  obtain ⟨ρ, hρ⟩ := exists_add_of_dominatesLeb hdom
  obtain ⟨hlfμ, hlfν⟩ := Admissible.isLocallyFinite hp
  have hpi : 0 < Real.pi := Real.pi_pos
  set k : ℝ := c / 2 with hk
  set w : ℝ := Real.pi * k with hw
  have hk0 : 0 < k := by rw [hk]; positivity
  have hw0 : 0 < w := by rw [hw]; positivity
  set dens : ℝ → ℝ≥0 := fun t => Real.toNNReal (c - k * Real.cos (2 * Real.pi * g * t)) with hdensdef
  have hdens : ∀ t, (dens t : ℝ) = c - k * Real.cos (2 * Real.pi * g * t) := by
    intro t
    rw [hdensdef, Real.coe_toNNReal]
    have := Real.cos_le_one (2 * Real.pi * g * t)
    nlinarith
  have hdens_le : ∀ t, (dens t : ℝ) ≤ c + k := by
    intro t
    rw [hdens t]
    have := Real.neg_one_le_cos (2 * Real.pi * g * t)
    nlinarith
  have hdens_meas : Measurable dens := by
    rw [hdensdef]
    exact (Continuous.measurable (by fun_prop)).real_toNNReal
  set W : Measure ℝ := (volume : Measure ℝ).withDensity (fun t => (dens t : ℝ≥0∞)) with hW
  set Y : Measure ℝ := ENNReal.ofReal c • (volume : Measure ℝ) with hY
  have hρle : ρ ≤ p.μ := by rw [← hρ]; exact Measure.le_add_right le_rfl
  refine ⟨⟨ρ + W, p.ν + ENNReal.ofReal w • Measure.dirac g⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- evenness
    have h1 := evenMeasure_of_add_leb hρ hp.1
    have h2 : EvenMeasure W := by
      rw [hW]
      apply evenMeasure_withDensity
      intro x
      simp only [hdensdef, mul_neg, Real.cos_neg]
    unfold EvenMeasure at h1 h2 ⊢
    rw [Measure.map_add _ _ measurable_neg, h1, h2]
  · -- the prime measure lives on `[g, ∞)`
    show (p.ν + ENNReal.ofReal w • Measure.dirac g) (Set.Ici g)ᶜ = 0
    have hc' := hp.2.1
    unfold CarriedBy at hc'
    rw [Measure.add_apply, Measure.smul_apply, hc',
      Measure.dirac_apply' _ measurableSet_Ici.compl]
    simp
  · -- the identity
    intro F hF
    obtain ⟨h1, h2, h3⟩ := hp.2.2 F hF
    have hint : Integrable (onR F) := TestClass.integrable hF
    have hiρ : Integrable (onR F) ρ := h1.mono_measure hρle
    have hiW : Integrable (onR F) W := by
      rw [hW, integrable_withDensity_iff_integrable_smul hdens_meas]
      refine Integrable.mono' (hint.norm.const_mul (c + k)) ?_ ?_
      · exact (hdens_meas.aestronglyMeasurable).smul hint.aestronglyMeasurable
      · exact Eventually.of_forall fun t => by
          rw [NNReal.smul_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (dens t).coe_nonneg]
          exact mul_le_mul_of_nonneg_right (hdens_le t) (norm_nonneg _)
    have hiD : Integrable (FT F) (ENNReal.ofReal w • Measure.dirac g) :=
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    refine ⟨hiρ.add_measure hiW, h2.add_measure hiD, ?_⟩
    show ((ArchG ks q F : ℝ) : ℂ) = (∫ x, onR F x ∂(ρ + W)) +
      (1 / Real.pi : ℂ) * ∫ ξ, FT F ξ ∂(p.ν + ENNReal.ofReal w • Measure.dirac g)
    have hY' : Integrable (onR F) Y := hint.smul_measure ENNReal.ofReal_ne_top
    -- the old identity, with `μ = ρ + c dt`
    have h3' : ((ArchG ks q F : ℝ) : ℂ) = ((∫ x, onR F x ∂ρ) + (c : ℂ) * ∫ x, onR F x) +
        (1 / Real.pi : ℂ) * ∫ ξ, FT F ξ ∂p.ν := by
      have e : (∫ x, onR F x ∂p.μ) = (∫ x, onR F x ∂ρ) + (c : ℂ) * ∫ x, onR F x := by
        rw [← hρ, integral_add_measure hiρ hY', hY, integral_smul_measure,
          ENNReal.toReal_ofReal hc.le, Complex.real_smul]
      rw [← e]
      exact h3
    -- the new zero side
    have hW' : (∫ x, onR F x ∂W) = (c : ℂ) * (∫ x, onR F x) - (k : ℂ) * FT F g := by
      rw [hW, integral_withDensity_eq_integral_smul hdens_meas, FT_eq_integral_cos hF g]
      have e1 : (fun x : ℝ => dens x • onR F x) =
          fun x => (c : ℂ) * onR F x - (k : ℂ) * (((Real.cos (2 * Real.pi * g * x) : ℝ) : ℂ) * F x) := by
        funext x
        rw [NNReal.smul_def, hdens x, Complex.real_smul]
        simp only [onR]
        push_cast
        ring
      have hcos : Integrable (fun x : ℝ => ((Real.cos (2 * Real.pi * g * x) : ℝ) : ℂ) * F x) := by
        refine Integrable.mono' hint.norm ?_ ?_
        · exact (Continuous.aestronglyMeasurable (by fun_prop)).mul hint.aestronglyMeasurable
        · exact Eventually.of_forall fun x => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have := Real.abs_cos_le_one (2 * Real.pi * g * x)
            calc |Real.cos (2 * Real.pi * g * x)| * ‖F x‖ ≤ 1 * ‖F x‖ :=
                  mul_le_mul_of_nonneg_right this (norm_nonneg _)
              _ = ‖onR F x‖ := by simp [onR]
      rw [e1, integral_sub (hint.const_mul _) (hcos.const_mul _), integral_const_mul,
        integral_const_mul]
    -- the new prime side
    have hD : (∫ ξ, FT F ξ ∂(p.ν + ENNReal.ofReal w • Measure.dirac g)) =
        (∫ ξ, FT F ξ ∂p.ν) + (w : ℂ) * FT F g := by
      rw [integral_add_measure h2 hiD, integral_smul_measure, integral_dirac,
        ENNReal.toReal_ofReal hw0.le, Complex.real_smul]
    rw [integral_add_measure hiρ hiW, hW', hD, h3', hw]
    have hpi' : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
    push_cast
    field_simp
    ring
  · -- the new pair differs from the old one: an extra atom at `g`
    intro heq
    have hν := congrArg Pair.ν heq
    simp only at hν
    have hfin : p.ν {g} ≠ ⊤ := (isCompact_singleton.measure_lt_top).ne
    have h := congrArg (fun m : Measure ℝ => m {g}) hν
    simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
      (Set.mem_singleton g), smul_eq_mul, mul_one] at h
    have h' : p.ν {g} + ENNReal.ofReal w = p.ν {g} + 0 := by rw [add_zero]; exact h
    have := (ENNReal.add_right_inj hfin).mp h'
    rw [ENNReal.ofReal_eq_zero] at this
    linarith

theorem dominatesLeb_mono {μ : Measure ℝ} {a b : ℝ} (hab : a ≤ b) (h : DominatesLeb μ b) :
    DominatesLeb μ a := by
  unfold DominatesLeb at h ⊢
  refine le_trans (Measure.le_iff'.mpr fun s => ?_) h
  simp only [Measure.smul_apply, smul_eq_mul]
  gcongr

/-- The natural-gap step and the change of conductor of Proposition 5.11 (as in `kappaG_ge_of_pair`):
a pair admissible for `𝒜_{𝔤,q₀}` at the gap `g'` with `μ ≥ c dt` gives, for every `g ≤ g'` and `q ≥ q₀`,
a pair admissible for `𝒜_{𝔤,q}` at the gap `g` with `μ ≥ (c + (log q − log q₀)/(2π)) dt`. -/
theorem exists_pair_shift (ks : List ℕ) {q₀ q g g' c : ℝ} (hq₀ : 0 < q₀) (hq : q₀ ≤ q) (hc : 0 ≤ c)
    {p : Pair} (hp : Admissible (ArchG ks q₀) g' p) (hdom : DominatesLeb p.μ c) (hg : g ≤ g') :
    ∃ p' : Pair, Admissible (ArchG ks q) g p' ∧
      DominatesLeb p'.μ (c + (Real.log q - Real.log q₀) / (2 * Real.pi)) := by
  have hq0 : 0 < q := lt_of_lt_of_le hq₀ hq
  set d : ℝ := (Real.log q - Real.log q₀) / (2 * Real.pi) with hd
  have hd0 : 0 ≤ d := by
    have : Real.log q₀ ≤ Real.log q := Real.log_le_log hq₀ hq
    have := Real.pi_pos
    rw [hd]; apply div_nonneg <;> linarith
  have hp' : Admissible (fun F => ArchG ks q F - d * intR F) g p := by
    have : (fun F => ArchG ks q F - d * intR F) = ArchG ks q₀ := by
      funext F; rw [ArchG_shift ks hq₀ hq0 F]; ring
    rw [this]; exact admissible_mono_gap hg hp
  refine ⟨_, admissible_add_leb hd0 hp', ?_⟩
  show DominatesLeb (p.μ + ENNReal.ofReal d • volume) (c + d)
  unfold DominatesLeb at hdom ⊢
  rw [ENNReal.ofReal_add hc hd0, add_smul]
  gcongr

/-- **Proposition 5.11(a), (b), the consequences.**  For the data of `ℚ(√5)` (resp. `ℚ(√−3)`) and every
gap `g ∈ (0, ξ_{4.04915}]` (resp. `(0, ξ_{3.011664}]`): some admissible pair has zero measure
`≥ 1.64 · 10^{-5} dt` (resp. `≥ 1.50 · 10^{-4} dt`), and the set of admissible pairs is not a singleton. -/
theorem prop_5_9_not_singleton :
    (∀ g : ℝ, 0 < g → g ≤ xiOf ((4049150 : ℝ) / 10 ^ 6) →
      (∃ p : Pair, Admissible (ArchG [0, 0] 5) g p ∧ DominatesLeb p.μ ((164 : ℝ) / 10 ^ 7)) ∧
      ¬ {p : Pair | Admissible (ArchG [0, 0] 5) g p}.Subsingleton) ∧
    (∀ g : ℝ, 0 < g → g ≤ xiOf ((3011664 : ℝ) / 10 ^ 6) →
      (∃ p : Pair, Admissible (ArchG [0, 1] 3) g p ∧ DominatesLeb p.μ ((150 : ℝ) / 10 ^ 6)) ∧
      ¬ {p : Pair | Admissible (ArchG [0, 1] 3) g p}.Subsingleton) := by
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  have hpi0 := Real.pi_pos
  constructor
  · intro g hg0 hg
    obtain ⟨hl5, hu5⟩ := log_five_bounds
    obtain ⟨p, hp, hdom⟩ := cert_Qsqrt5_pair
    have hq₀ : (0 : ℝ) < Real.exp ((16093347792651136 : ℝ) / 10 ^ 16) := Real.exp_pos _
    have hqle : Real.exp ((16093347792651136 : ℝ) / 10 ^ 16) ≤ 5 := by
      rw [← Real.log_le_log_iff (Real.exp_pos _) (by norm_num), Real.log_exp]
      linarith
    obtain ⟨p', hp', hdom'⟩ := exists_pair_shift [0, 0] hq₀ hqle (by norm_num) hp hdom hg
    rw [Real.log_exp] at hdom'
    have h1 : (16094379 / 10 ^ 7 - 16093347792651136 / 10 ^ 16 : ℝ) / (2 * 3.14159265358979323847)
        ≤ (Real.log 5 - 16093347792651136 / 10 ^ 16) / (2 * Real.pi) := by
      apply div_le_div₀ (by linarith) (by linarith) (by positivity) (by linarith)
    have h2 : (164 : ℝ) / 10 ^ 7 ≤ 659497 / 10 ^ 14 +
        (16094379 / 10 ^ 7 - 16093347792651136 / 10 ^ 16 : ℝ) / (2 * 3.14159265358979323847) := by
      norm_num
    have hc : (164 : ℝ) / 10 ^ 7 ≤
        659497 / 10 ^ 14 + (Real.log 5 - 16093347792651136 / 10 ^ 16) / (2 * Real.pi) := by
      linarith
    refine ⟨⟨p', hp', dominatesLeb_mono hc hdom'⟩, fun hs => ?_⟩
    obtain ⟨p'', hp'', hne⟩ := not_unique_of_dominates hg0 hp'
      (lt_of_lt_of_le (by norm_num) hc) hdom'
    exact hne (hs hp'' hp')
  · intro g hg0 hg
    obtain ⟨hl3, hu3⟩ := log_three_bounds
    obtain ⟨p, hp, hdom⟩ := cert_Qsqrtm3_pair
    have hq₀ : (0 : ℝ) < Real.exp ((10976698108720329 : ℝ) / 10 ^ 16) := Real.exp_pos _
    have hqle : Real.exp ((10976698108720329 : ℝ) / 10 ^ 16) ≤ 3 := by
      rw [← Real.log_le_log_iff (Real.exp_pos _) (by norm_num), Real.log_exp]
      linarith
    obtain ⟨p', hp', hdom'⟩ := exists_pair_shift [0, 1] hq₀ hqle (by norm_num) hp hdom hg
    rw [Real.log_exp] at hdom'
    have h1 : (10986122 / 10 ^ 7 - 10976698108720329 / 10 ^ 16 : ℝ) / (2 * 3.14159265358979323847)
        ≤ (Real.log 3 - 10976698108720329 / 10 ^ 16) / (2 * Real.pi) := by
      apply div_le_div₀ (by linarith) (by linarith) (by positivity) (by linarith)
    have h2 : (150 : ℝ) / 10 ^ 6 ≤ 667226 / 10 ^ 13 +
        (10986122 / 10 ^ 7 - 10976698108720329 / 10 ^ 16 : ℝ) / (2 * 3.14159265358979323847) := by
      norm_num
    have hc : (150 : ℝ) / 10 ^ 6 ≤
        667226 / 10 ^ 13 + (Real.log 3 - 10976698108720329 / 10 ^ 16) / (2 * Real.pi) := by
      linarith
    refine ⟨⟨p', hp', dominatesLeb_mono hc hdom'⟩, fun hs => ?_⟩
    obtain ⟨p'', hp'', hne⟩ := not_unique_of_dominates hg0 hp'
      (lt_of_lt_of_le (by norm_num) hc) hdom'
    exact hne (hs hp'' hp')

end PosRig
