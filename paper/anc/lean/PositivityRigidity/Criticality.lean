/-
§2.4: Theorem 2.12 (criticality and atomicity), parts (b) and (c), from part (a) (ledger axiom
`weak_magic_functions`), Proposition 2.8 and Theorem 2.7.
-/
import PositivityRigidity.Duality

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

/-! ## Discrete sets and atomic measures -/

/-- A discrete subset of `ℝ` is countable. -/
theorem DiscreteSet.countable {Z : Set ℝ} (h : DiscreteSet Z) : Z.Countable := by
  have hd : DiscreteTopology Z := by
    rw [discreteTopology_subtype_iff]
    intro x _
    rw [inf_principal_eq_bot]
    exact h x
  exact Set.countable_coe_iff.mp (TopologicalSpace.separableSpace_iff_countable.mp inferInstance)

/-- A purely atomic measure dominates no `λ dt` with `λ > 0`. -/
theorem not_dominatesLeb_of_purelyAtomic {μ : Measure ℝ} (h : PurelyAtomic μ) {lam : ℝ}
    (hl : 0 < lam) : ¬ DominatesLeb μ lam := by
  obtain ⟨S, hS, hμ⟩ := h
  intro hdom
  have h1 := Measure.le_iff'.mp hdom Sᶜ
  rw [Measure.smul_apply, hμ] at h1
  have hS0 : (volume : Measure ℝ) S = 0 := hS.measure_zero volume
  have hc : (volume : Measure ℝ) Sᶜ = ⊤ := by
    rw [measure_compl hS.measurableSet (by rw [hS0]; exact ENNReal.zero_ne_top), hS0,
      Real.volume_univ]
    simp
  rw [hc, smul_eq_mul, ENNReal.mul_top (by simpa using hl)] at h1
  exact absurd h1 (by simp)

/-! ## Weak magic functions: zero sets -/

theorem isPreconnected_openStrip (b : ℝ) : IsPreconnected (openStrip b) := by
  have : openStrip b = Complex.im ⁻¹' Set.Ioo (-b) b := by
    ext z; simp [openStrip, abs_lt]
  rw [this]
  exact ((convex_Ioo (-b) b).linear_preimage Complex.imLm).isPreconnected

theorem ofReal_mem_openStrip (t : ℝ) {b : ℝ} (hb : 0 < b) : (t : ℂ) ∈ openStrip b := by
  simp [openStrip, hb]

/-- The data of Theorem 2.12(a) for a weak magic function. -/
theorem weakMagic_props {Fs : ℝ → ℝ} (hFs : IsWeakMagic Fs) :
    (∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (openStrip (1 / 2)) ∧ ∀ t : ℝ, G t = Fs t) ∧
    (∀ ξ : ℝ, xi2 ≤ |ξ| → 0 ≤ 𝓕 (fun t : ℝ => (Fs t : ℂ)) ξ) ∧
    ∀ p ∈ K, (∫⁻ t, ENNReal.ofReal (Fs t) ∂p.μ) = 0 ∧
      (∫⁻ ξ, ENNReal.ofReal (𝓕 (fun t : ℝ => (Fs t : ℂ)) ξ).re ∂p.ν) = 0 := by
  obtain ⟨-, -, -, hG, hpos, -, hK⟩ := weak_magic_functions.2 Fs hFs
  exact ⟨hG, hpos, hK⟩

theorem weakMagic_continuous {Fs : ℝ → ℝ} (hFs : IsWeakMagic Fs) : Continuous Fs := by
  obtain ⟨⟨G, hG, hGF⟩, -, -⟩ := weakMagic_props hFs
  have hc : ∀ t : ℝ, ContinuousAt (fun s : ℝ => (G s).re) t := fun t =>
    Complex.continuous_re.continuousAt.comp
      ((hG t (ofReal_mem_openStrip t (by norm_num))).continuousAt.comp
        Complex.continuous_ofReal.continuousAt)
  have : Fs = fun s : ℝ => (G s).re := by
    funext s; rw [hGF s]; simp
  rw [this]
  exact continuous_iff_continuousAt.mpr hc

/-- **Theorem 2.12(c), first claim.** The real zero set `Z(F*)` of a weak magic function is discrete. -/
theorem weakMagic_zeros_discrete {Fs : ℝ → ℝ} (hFs : IsWeakMagic Fs) :
    DiscreteSet {t : ℝ | Fs t = 0} := by
  obtain ⟨⟨G, hG, hGF⟩, -, -⟩ := weakMagic_props hFs
  intro x
  rcases (hG x (ofReal_mem_openStrip x (by norm_num))).eventually_eq_zero_or_eventually_ne_zero
    with h | h
  · -- `G` vanishes near `x`, hence on the strip, hence `F* = 0` on `ℝ`: contradiction with `∫ F* = 1`
    exfalso
    have hz := hG.eqOn_zero_of_preconnected_of_eventuallyEq_zero (isPreconnected_openStrip _)
      (ofReal_mem_openStrip x (by norm_num)) h
    have h0 : ∀ t : ℝ, Fs t = 0 := by
      intro t
      have := hz (ofReal_mem_openStrip t (by norm_num))
      rw [hGF t] at this
      simpa using this
    have hint := hFs.2.1
    simp [h0] at hint
  · -- `G ≠ 0` on a punctured neighbourhood of `x` in `ℂ`; pull back to `ℝ`
    have ht : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] x) (𝓝[≠] (x : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (Complex.continuous_ofReal.tendsto x).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact fun h' => hs (Complex.ofReal_injective h')
    filter_upwards [ht.eventually h] with s hs
    intro hs0
    apply hs
    rw [hGF s]
    exact_mod_cast hs0

/-- **Theorem 2.12(c), second claim / (b)(i) ⇒ (iii).** Every admissible `μ` is carried by `Z(F*)`. -/
theorem weakMagic_carries_mu {Fs : ℝ → ℝ} (hFs : IsWeakMagic Fs) {p : Pair} (hp : p ∈ K) :
    CarriedBy p.μ {t : ℝ | Fs t = 0} := by
  obtain ⟨-, -, hK⟩ := weakMagic_props hFs
  have hl := (hK p hp).1
  have hmeas : Measurable fun t => ENNReal.ofReal (Fs t) :=
    ENNReal.measurable_ofReal.comp (weakMagic_continuous hFs).measurable
  rw [lintegral_eq_zero_iff hmeas] at hl
  have : ∀ᵐ t ∂p.μ, Fs t = 0 := by
    filter_upwards [hl] with t ht
    have h1 : Fs t ≤ 0 := ENNReal.ofReal_eq_zero.mp ht
    exact le_antisymm h1 (hFs.1 t)
  rw [ae_iff] at this
  unfold CarriedBy
  simpa [Set.compl_def] using this

/-- **Theorem 2.12(c), last claim.** Every admissible `ν` is carried by the closed set
`Ẑ(F*) = F̂*⁻¹(0) ∩ [ξ₂, ∞)`. -/
theorem weakMagic_carries_nu {Fs : ℝ → ℝ} (hFs : IsWeakMagic Fs) {p : Pair} (hp : p ∈ K) :
    CarriedBy p.ν {ξ : ℝ | xi2 ≤ ξ ∧ 𝓕 (fun t : ℝ => (Fs t : ℂ)) ξ = 0} ∧
      IsClosed {ξ : ℝ | xi2 ≤ ξ ∧ 𝓕 (fun t : ℝ => (Fs t : ℂ)) ξ = 0} := by
  obtain ⟨-, hpos, hK⟩ := weakMagic_props hFs
  have hint : Integrable (fun t : ℝ => (Fs t : ℂ)) := by
    have : Integrable Fs := by
      by_contra hni
      have := hFs.2.1
      rw [integral_undef hni] at this
      exact zero_ne_one this
    exact this.ofReal
  have hcont : Continuous (𝓕 (fun t : ℝ => (Fs t : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hint
  refine ⟨?_, ?_⟩
  · have hl := (hK p hp).2
    have hmeas : Measurable fun ξ => ENNReal.ofReal (𝓕 (fun t : ℝ => (Fs t : ℂ)) ξ).re :=
      ENNReal.measurable_ofReal.comp (Complex.continuous_re.comp hcont).measurable
    rw [lintegral_eq_zero_iff hmeas] at hl
    have hIci : ∀ᵐ ξ ∂p.ν, xi2 ≤ ξ := by
      have h := hp.2.1
      unfold CarriedBy at h
      rw [ae_iff]
      simpa [Set.compl_def] using h
    have : ∀ᵐ ξ ∂p.ν, xi2 ≤ ξ ∧ 𝓕 (fun t : ℝ => (Fs t : ℂ)) ξ = 0 := by
      filter_upwards [hl, hIci] with ξ hξ hg
      refine ⟨hg, ?_⟩
      have hxi2 : 0 ≤ xi2 := by
        unfold xi2 xiOf
        have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        positivity
      have h0 := hpos ξ (le_trans hg (le_abs_self ξ))
      have h1 : (𝓕 (fun t : ℝ => (Fs t : ℂ)) ξ).re ≤ 0 := ENNReal.ofReal_eq_zero.mp hξ
      obtain ⟨h2, h3⟩ := Complex.nonneg_iff.mp h0
      exact Complex.ext (le_antisymm h1 h2) (by simpa using h3.symm)
    rw [ae_iff] at this
    unfold CarriedBy
    simpa [Set.compl_def] using this
  · exact isClosed_le continuous_const continuous_id |>.inter (isClosed_eq hcont continuous_const)

/-! ## Theorem 2.12(b) -/

/-- **Theorem 2.12(b).**  Assume (E).  The following are equivalent: (i) `κ* = 0`; (ii) every admissible
`μ` is purely atomic; (iii) there is a discrete set `Z* ⊂ ℝ` carrying every admissible `μ`; (iv) no
admissible `μ` satisfies `μ ≥ λ dt` with `λ > 0`. -/
theorem criticality (hE : CondE) :
    (kappaStar = 0 ↔ ∀ p ∈ K, PurelyAtomic p.μ) ∧
    (kappaStar = 0 ↔ ∃ Z : Set ℝ, DiscreteSet Z ∧ ∀ p ∈ K, CarriedBy p.μ Z) ∧
    (kappaStar = 0 ↔ ∀ p ∈ K, ∀ lam : ℝ, 0 < lam → ¬ DominatesLeb p.μ lam) := by
  have i_iii : kappaStar = 0 → ∃ Z : Set ℝ, DiscreteSet Z ∧ ∀ p ∈ K, CarriedBy p.μ Z := by
    intro h0
    obtain ⟨Fs, hFs⟩ := weak_magic_functions.1 h0
    exact ⟨_, weakMagic_zeros_discrete hFs, fun p hp => weakMagic_carries_mu hFs hp⟩
  have iii_ii : (∃ Z : Set ℝ, DiscreteSet Z ∧ ∀ p ∈ K, CarriedBy p.μ Z) →
      ∀ p ∈ K, PurelyAtomic p.μ := by
    rintro ⟨Z, hZ, hcar⟩ p hp
    exact ⟨Z, hZ.countable, hcar p hp⟩
  have ii_iv : (∀ p ∈ K, PurelyAtomic p.μ) →
      ∀ p ∈ K, ∀ lam : ℝ, 0 < lam → ¬ DominatesLeb p.μ lam :=
    fun h p hp lam hl => not_dominatesLeb_of_purelyAtomic (h p hp) hl
  have iv_i : (∀ p ∈ K, ∀ lam : ℝ, 0 < lam → ¬ DominatesLeb p.μ lam) → kappaStar = 0 := by
    intro h
    have h0 : 0 ≤ kappaStar := condE_iff_kappaStar_nonneg.mp hE
    by_contra hne
    have hpos : 0 < kappaStar := lt_of_le_of_ne h0 (Ne.symm hne)
    obtain ⟨p, hp, hdom⟩ := prop_2_8_dominates.mp h0
    have hk : 0 < kappaStar.toReal := by
      have := kappaStar_coe
      rw [← this] at hpos
      exact_mod_cast hpos
    exact h p hp _ hk hdom
  refine ⟨⟨fun h => iii_ii (i_iii h), fun h => iv_i (ii_iv h)⟩,
    ⟨i_iii, fun h => iv_i (ii_iv (iii_ii h))⟩, ⟨fun h => ii_iv (iii_ii (i_iii h)), iv_i⟩⟩

/-- **Theorem 2.12(c).**  If `κ* = 0` and `F*` is a weak magic function, one may take `Z* = Z(F*)` in
(iii), and every admissible `ν` is carried by the closed set `Ẑ(F*)`.  (The claim that the real zeros
of `F*` have even order is not formalised.) -/
theorem criticality_c {Fs : ℝ → ℝ} (hFs : IsWeakMagic Fs) :
    DiscreteSet {t : ℝ | Fs t = 0} ∧ (∀ p ∈ K, CarriedBy p.μ {t : ℝ | Fs t = 0}) ∧
    (∀ p ∈ K, CarriedBy p.ν {ξ : ℝ | xi2 ≤ ξ ∧ 𝓕 (fun t : ℝ => (Fs t : ℂ)) ξ = 0}) ∧
    IsClosed {ξ : ℝ | xi2 ≤ ξ ∧ 𝓕 (fun t : ℝ => (Fs t : ℂ)) ξ = 0} := by
  refine ⟨weakMagic_zeros_discrete hFs, fun p hp => weakMagic_carries_mu hFs hp,
    fun p hp => (weakMagic_carries_nu hFs hp).1, ?_⟩
  have hint : Integrable (fun t : ℝ => (Fs t : ℂ)) := by
    have : Integrable Fs := by
      by_contra hni
      have := hFs.2.1
      rw [integral_undef hni] at this
      exact zero_ne_one this
    exact this.ofReal
  have hcont : Continuous (𝓕 (fun t : ℝ => (Fs t : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hint
  exact isClosed_le continuous_const continuous_id |>.inter (isClosed_eq hcont continuous_const)

end PosRig
