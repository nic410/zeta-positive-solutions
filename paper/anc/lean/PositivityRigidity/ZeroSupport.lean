/-
v1.1: Theorem 3.6 (zero-side support) and its consequences.

* `zero_support_theorem` (Theorem 3.6 = Theorem B(a)): if `(μ, ν) ∈ 𝒦` and `μ` is carried by
  `Z_ζ ∪ {0}`, then RH holds and `(μ, ν) = p_ζ` (the ledger axiom `zero_support_rigidity` gives
  `ν = ν_ζ`; Theorem 2.9(b), ledger axiom `logic_b`, gives the rest, as in the paper);
* `prop_3_5_strong`: for admissible pairs, Proposition 3.5 without its hypothesis on `ν` (after
  Theorem 3.6);
* `magic_principle_zero` (Corollary 3.9(a)): the magic-function principle without the Fourier condition;
* `certificate_route` (Corollary 4.11): `F_J ∈ 𝒞`, `F_J ≥ c_J Ξ²`, `c_J > 0`, `𝒜(F_J)/c_J → 0` give (U)
  and (S); `Ξ² ∈ 𝒯` is not needed for it (`Xi_sq_mem_TestClass` is proved nevertheless);
* `carriedBy_Zzeta_of_lintegral`, `carriedBy_Zzeta_of_integral`: `∫ Ξ² dμ = 0` forces `μ` onto `Z_ζ`;
* `condU_iff_carriedBy`, `condU_iff_Xi_sq`: (U) holds iff every admissible `μ` is carried by `Z_ζ`, iff
  `∫ Ξ² dμ = 0` for every admissible pair (a consequence of Theorem 3.6, not stated in the paper).

Sources: Paper I, Theorem 3.6 (Appendix B.1.4), Corollaries 3.9(a) and 4.11; these results are due to
Astra (OpenAI), contributed during an independent review of an earlier version of the paper, and
independently verified.
-/
import PositivityRigidity.Uniqueness
import PositivityRigidity.FamilyMore

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

/-! ## Facts about `Ξ²` on the real line -/

/-- `Z_ζ` is closed (so "carried by `Z_ζ`" and "`supp μ ⊆ Z_ζ`" agree for Radon measures). -/
theorem isClosed_Zzeta : IsClosed Zzeta := by
  have h : Zzeta = (fun t : ℝ => Xi t) ⁻¹' {0} := by
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Xi_eq_zero_iff]
  rw [h]
  exact isClosed_singleton.preimage (differentiable_Xi.continuous.comp Complex.continuous_ofReal)

theorem continuous_Xi_sq_re : Continuous (fun t : ℝ => (Xi t ^ 2).re) :=
  Complex.continuous_re.comp ((differentiable_Xi.continuous.comp Complex.continuous_ofReal).pow 2)

/-- `Ξ(t)² = (Re Ξ(t))²` on `ℝ`. -/
theorem Xi_sq_re (t : ℝ) : (Xi t ^ 2).re = (Xi t).re ^ 2 := by
  have h := Xi_real t
  rw [sq, sq, Complex.mul_re, h]
  ring

theorem Xi_sq_re_nonneg (t : ℝ) : 0 ≤ (Xi t ^ 2).re := by
  rw [Xi_sq_re]
  positivity

theorem Xi_sq_re_pos_iff (t : ℝ) : 0 < (Xi t ^ 2).re ↔ t ∉ Zzeta := by
  rw [Xi_sq_re, ← Xi_eq_zero_iff]
  constructor
  · intro h h0
    rw [h0, Complex.zero_re] at h
    simp at h
  · intro h
    have hre : (Xi t).re ≠ 0 := fun h0 =>
      h (Complex.ext (by simpa using h0) (by simpa using Xi_real t))
    positivity

/-- `Ξ² ∈ 𝒯` (§4.1: `Ξ² H ∈ 𝒯` with `H = 1`).  Not needed for the certificate route; it makes
`∫ Ξ² dμ` an admissible integral. -/
theorem Xi_sq_mem_TestClass : (fun z => Xi z ^ 2) ∈ TestClass := by
  have h := Xi_sq_mul_mem_TestClass (H := fun _ => 1) (A := 1) (m := 0) (differentiable_const 1)
    (fun _ => rfl) (fun t => by simp) (fun z _ => by simp)
  simpa using h

/-- **`∫ Ξ² dμ = 0` forces `μ` onto `Z_ζ`** (lower-integral form, for every measure `μ`; no
integrability needed). -/
theorem carriedBy_Zzeta_of_lintegral {μ : Measure ℝ}
    (h : ∫⁻ t, ENNReal.ofReal (Xi t ^ 2).re ∂μ = 0) : CarriedBy μ Zzeta := by
  have hmeas : Measurable (fun t : ℝ => ENNReal.ofReal (Xi t ^ 2).re) :=
    continuous_Xi_sq_re.measurable.ennreal_ofReal
  rw [lintegral_eq_zero_iff hmeas] at h
  have hae : ∀ᵐ t ∂μ, t ∈ Zzeta := by
    filter_upwards [h] with t ht
    have h0 : (Xi t ^ 2).re ≤ 0 := ENNReal.ofReal_eq_zero.mp ht
    by_contra hz
    exact absurd ((Xi_sq_re_pos_iff t).mpr hz) (not_lt.mpr h0)
  unfold CarriedBy
  rw [ae_iff] at hae
  simpa [Set.compl_def] using hae

/-- **`∫ Ξ² dμ = 0` forces `μ` onto `Z_ζ`** (Bochner-integral form). -/
theorem carriedBy_Zzeta_of_integral {μ : Measure ℝ}
    (hint : Integrable (fun t : ℝ => (Xi t ^ 2).re) μ) (h : ∫ t, (Xi t ^ 2).re ∂μ = 0) :
    CarriedBy μ Zzeta := by
  apply carriedBy_Zzeta_of_lintegral
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t => Xi_sq_re_nonneg t),
    h, ENNReal.ofReal_zero]

/-- Conversely, a measure carried by `Z_ζ` has `∫ Ξ² dμ = 0`. -/
theorem lintegral_Xi_sq_of_carriedBy {μ : Measure ℝ} (h : CarriedBy μ Zzeta) :
    ∫⁻ t, ENNReal.ofReal (Xi t ^ 2).re ∂μ = 0 := by
  have hmeas : Measurable (fun t : ℝ => ENNReal.ofReal (Xi t ^ 2).re) :=
    continuous_Xi_sq_re.measurable.ennreal_ofReal
  rw [lintegral_eq_zero_iff hmeas]
  have hae : ∀ᵐ t ∂μ, t ∈ Zzeta := by
    rw [ae_iff]
    simpa [CarriedBy, Set.compl_def] using h
  filter_upwards [hae] with t ht
  have : Xi t = 0 := (Xi_eq_zero_iff t).mpr ht
  simp [this]

/-- Weak duality, zero side: `∫ F dμ ≤ 𝒜(F)` for `F ∈ 𝒞` and `(μ, ν) ∈ 𝒦` (Lemma 2.5). -/
theorem integral_le_Arch {p : Pair} (hp : p ∈ K) {F : ℂ → ℂ} (hF : F ∈ Cone) :
    ∫ t, (F t).re ∂p.μ ≤ Arch F := by
  have hid := hp.real_identity hF.1
  have h2 := (hp.parts_nonneg hF).2
  have : 0 ≤ 1 / Real.pi * ∫ ξ, (FT F ξ).re ∂p.ν := by
    have := Real.pi_pos
    positivity
  linarith

/-! ## The theorem (zero-side support) -/

/-- **Theorem 3.6 (zero-side support; Theorem B(a)).**  If `(μ, ν) ∈ 𝒦` and `μ` is carried by
`Z_ζ ∪ {0}`, then `ν = ν_ζ`, RH holds and `(μ, ν) = p_ζ`.  No condition on `ν`.  (`ν = ν_ζ` is the
ledger axiom `zero_support_rigidity`; RH and `μ = μ_ζ` follow by Theorem 2.9(b).) -/
theorem zero_support_theorem {p : Pair} (hp : p ∈ K) (hμ : CarriedBy p.μ (Zzeta ∪ {0})) :
    RiemannHypothesis ∧ p = pZeta := by
  have hν : p.ν = nuZeta := zero_support_rigidity p hp hμ
  have hpeq : p = ⟨p.μ, nuZeta⟩ := by
    rw [← hν]
  have hp' : (⟨p.μ, nuZeta⟩ : Pair) ∈ K := hpeq ▸ hp
  obtain ⟨hRH, hμ'⟩ := logic_b p.μ hp'
  refine ⟨hRH, ?_⟩
  rw [hpeq, hμ']
  rfl

/-- Sanity check for the ledger axiom `zero_support_rigidity`: under RH, `p_ζ` satisfies its hypothesis
(`p_ζ ∈ 𝒦` and `μ_ζ` is carried by `Z_ζ ⊆ Z_ζ ∪ {0}`), and its conclusion `ν = ν_ζ` holds for `p_ζ` without
the axiom. -/
theorem zero_support_rigidity_sanity (hRH : RiemannHypothesis) :
    pZeta ∈ K ∧ CarriedBy pZeta.μ (Zzeta ∪ {0}) ∧ pZeta.ν = nuZeta :=
  ⟨pZeta_mem_K_of_RH hRH,
    measure_mono_null (Set.compl_subset_compl.mpr Set.subset_union_left) muZeta_carriedBy, rfl⟩

/-- **Proposition 3.5 without its hypothesis on `ν`, for admissible pairs** (the remark after
Theorem 3.6).  If `(μ, ν) ∈ 𝒦` and `μ` is carried by `Z_ζ`, then RH holds and `(μ, ν) = p_ζ`. -/
theorem prop_3_5_strong {p : Pair} (hp : p ∈ K) (hμ : CarriedBy p.μ Zzeta) :
    RiemannHypothesis ∧ p = pZeta :=
  zero_support_theorem hp (measure_mono_null (Set.compl_subset_compl.mpr Set.subset_union_left) hμ)

/-- The direct consequences of "every admissible `μ` is carried by `Z_ζ ∪ {0}`": (U), and
`(E) ⇒ RH ∧ 𝒦 = {p_ζ}`. -/
theorem condU_of_zero_support (hall : ∀ p ∈ K, CarriedBy p.μ (Zzeta ∪ {0})) :
    CondU ∧ (CondE → RiemannHypothesis ∧ K = {pZeta}) := by
  have h1 : ∀ p ∈ K, RiemannHypothesis ∧ p = pZeta := fun p hp =>
    zero_support_theorem hp (hall p hp)
  have hU : CondU := fun p hp => (h1 p hp).2
  refine ⟨hU, ?_⟩
  rintro ⟨p, hp⟩
  obtain ⟨hRH, hpz⟩ := h1 p hp
  subst hpz
  exact ⟨hRH, Set.Subset.antisymm hU (Set.singleton_subset_iff.mpr hp)⟩

/-- The consequences of "every admissible `μ` is carried by `Z_ζ ∪ {0}`": (U), `(E) ⇒ RH ∧ 𝒦 = {p_ζ}`,
`RH ⇔ (E)` (Theorem 2.9(a) for `⇒`), and, if also (S), `κ* = 0` and `𝒦 = {p_ζ}` under RH or (E). -/
theorem consequences_of_zero_support (hall : ∀ p ∈ K, CarriedBy p.μ (Zzeta ∪ {0})) :
    CondU ∧ (CondE → RiemannHypothesis ∧ K = {pZeta}) ∧ (RiemannHypothesis ↔ CondE) ∧
      (CondS → RiemannHypothesis ∨ CondE → kappaStar = 0 ∧ K = {pZeta}) := by
  obtain ⟨hU, hEU⟩ := condU_of_zero_support hall
  have hRE : RiemannHypothesis ↔ CondE := ⟨fun h => (logic_a h).2, fun h => (hEU h).1⟩
  refine ⟨hU, hEU, hRE, fun hS h => ?_⟩
  have hE : CondE := h.elim hRE.mp id
  exact ⟨le_antisymm hS (kappaStar_nonneg_of_condE hE), (hEU hE).2⟩

/-- **(U) ⇔ every admissible `μ` is carried by `Z_ζ`** (a consequence of Theorem 3.6). -/
theorem condU_iff_carriedBy : CondU ↔ ∀ p ∈ K, CarriedBy p.μ Zzeta := by
  constructor
  · intro hU p hp
    have hpz : p = pZeta := hU hp
    rw [hpz]
    exact muZeta_carriedBy
  · intro h
    exact (condU_of_zero_support fun p hp =>
      measure_mono_null (Set.compl_subset_compl.mpr Set.subset_union_left) (h p hp)).1

/-- **(U) ⇔ `∫ Ξ² dμ = 0` for every admissible pair** (a consequence of Theorem 3.6). -/
theorem condU_iff_Xi_sq : CondU ↔ ∀ p ∈ K, ∫⁻ t, ENNReal.ofReal (Xi t ^ 2).re ∂p.μ = 0 := by
  rw [condU_iff_carriedBy]
  exact ⟨fun h p hp => lintegral_Xi_sq_of_carriedBy (h p hp),
    fun h p hp => carriedBy_Zzeta_of_lintegral (h p hp)⟩

/-! ## Corollary 3.9(a): the magic-function principle without the Fourier condition -/

/-- **Corollary 3.9(a) (magic-function principle, no Fourier condition).**  If some `F ∈ 𝒞` with
`𝒜(F) = 0` has all its real zeros in `Z_ζ ∪ {0}` (that is, `E = Z(F) \ Z_ζ ⊆ {0}`; for instance
`Z(F) = Z_ζ`), then (U) holds; if moreover (E) holds, then RH holds and `𝒦 = {p_ζ}`.  No hypothesis on
`Ẑ(F)`. -/
theorem magic_principle_zero {F : ℂ → ℂ} (hF : F ∈ Cone) (hA : Arch F = 0)
    (hZ : ZF F ⊆ Zzeta ∪ {0}) : CondU ∧ (CondE → RiemannHypothesis ∧ K = {pZeta}) := by
  exact condU_of_zero_support fun p hp =>
    measure_mono_null (Set.compl_subset_compl.mpr hZ) (comp_slackness hF hA hp).1

/-! ## Corollary 4.11: the certificate route -/

/-- A positive lower bound for `Ξ²` near the origin (`Ξ(0) > 0`). -/
theorem exists_Xi_sq_lower :
    ∃ δ : ℝ, 0 < δ ∧ ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Set.Icc (-δ) δ, m ≤ (Xi t ^ 2).re := by
  have h0 : 0 < (Xi (0 : ℝ) ^ 2).re := by
    rw [Xi_sq_re]
    have := Xi_zero_pos
    simp only [Complex.ofReal_zero]
    positivity
  set m := (Xi (0 : ℝ) ^ 2).re / 2 with hm
  have hm0 : 0 < m := by rw [hm]; positivity
  have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), m < (Xi (t : ℂ) ^ 2).re :=
    continuousAt_const.eventually_lt continuous_Xi_sq_re.continuousAt (by rw [hm]; linarith)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε / 2, by positivity, m, hm0, fun t ht => (hball ?_).le⟩
  rw [Real.dist_eq, sub_zero, abs_lt]
  obtain ⟨h1, h2⟩ := ht
  constructor <;> linarith

/-- **Corollary 4.11 (a certificate route).**  Let `I ⊆ ℕ` be infinite, and let `F_J ∈ 𝒞` and `c_J > 0`
(`J ∈ I`) with `F_J ≥ c_J Ξ²` on `ℝ` and `𝒜(F_J)/c_J → 0` as `J → ∞` in `I`.  Then (U) and (S) hold; moreover
`RH ⇔ (E)`, and under either, `κ* = 0` and `𝒦 = {p_ζ}`.  (For every admissible pair,
`c_J ∫ Ξ² dμ ≤ ∫ F_J dμ ≤ 𝒜(F_J)`, so `∫ Ξ² dμ = 0` and Theorem 3.6 applies; and `∫ F_J ≥ c_J ∫ Ξ² > 0` gives
(S).  `Ξ² ∈ 𝒯` is not used.) -/
theorem certificate_route {I : Set ℕ} (hI : I.Infinite) {F : ℕ → ℂ → ℂ} {c : ℕ → ℝ}
    (hF : ∀ J ∈ I, F J ∈ Cone) (hc : ∀ J ∈ I, 0 < c J)
    (hdom : ∀ J ∈ I, ∀ t : ℝ, c J * (Xi t ^ 2).re ≤ (F J t).re)
    (hlim : Tendsto (fun J => Arch (F J) / c J) (atTop ⊓ 𝓟 I) (𝓝 0)) :
    CondU ∧ CondS ∧ (RiemannHypothesis ↔ CondE) ∧
      (RiemannHypothesis ∨ CondE → kappaStar = 0 ∧ K = {pZeta}) := by
  have : (atTop ⊓ 𝓟 I).NeBot :=
    frequently_mem_iff_neBot.mp (Nat.frequently_atTop_iff_infinite.mpr hI)
  have hevI : ∀ᶠ J in atTop ⊓ 𝓟 I, J ∈ I :=
    (eventually_principal.mpr fun J hJ => hJ).filter_mono inf_le_right
  -- the zero side: `∫ Ξ² dμ = 0` for every admissible pair
  have hzero : ∀ p ∈ K, ∫⁻ t, ENNReal.ofReal (Xi t ^ 2).re ∂p.μ = 0 := by
    intro p hp
    set X := ∫⁻ t, ENNReal.ofReal (Xi t ^ 2).re ∂p.μ with hX
    have hbound : ∀ J ∈ I, X ≤ ENNReal.ofReal (Arch (F J) / c J) := by
      intro J hJ
      have hint := (hp.integrable_re (hF J hJ).1).1
      have hnn : 0 ≤ᵐ[p.μ] fun t => (F J t).re :=
        Eventually.of_forall fun t => ConeG.re_nonneg (hF J hJ) t
      have h1 : X * ENNReal.ofReal (c J) ≤ ∫⁻ t, ENNReal.ofReal (F J t).re ∂p.μ := by
        rw [mul_comm, hX, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono fun t => ?_
        rw [← ENNReal.ofReal_mul (hc J hJ).le]
        exact ENNReal.ofReal_le_ofReal (hdom J hJ t)
      have h2 : ∫⁻ t, ENNReal.ofReal (F J t).re ∂p.μ = ENNReal.ofReal (∫ t, (F J t).re ∂p.μ) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
      have h3 : X * ENNReal.ofReal (c J) ≤ ENNReal.ofReal (Arch (F J)) :=
        h1.trans (h2 ▸ ENNReal.ofReal_le_ofReal (integral_le_Arch hp (hF J hJ)))
      rw [ENNReal.ofReal_div_of_pos (hc J hJ)]
      exact (ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hc J hJ))
        (Or.inl ENNReal.ofReal_ne_top)).mpr h3
    have hlim' : Tendsto (fun J => ENNReal.ofReal (Arch (F J) / c J)) (atTop ⊓ 𝓟 I) (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto 0).comp hlim
      rw [ENNReal.ofReal_zero] at this
      exact this
    exact nonpos_iff_eq_zero.mp (ge_of_tendsto hlim' (hevI.mono hbound))
  have hall : ∀ p ∈ K, CarriedBy p.μ (Zzeta ∪ {0}) := fun p hp =>
    measure_mono_null (Set.compl_subset_compl.mpr Set.subset_union_left)
      (carriedBy_Zzeta_of_lintegral (hzero p hp))
  obtain ⟨hU, -, hRE, hfin⟩ := consequences_of_zero_support hall
  -- (S): `∫ F_J ≥ c_J m` with `m > 0`, hence `κ* ≤ 𝒜(F_J)/∫ F_J ≤ max(𝒜(F_J)/c_J, 0)/m → 0`
  obtain ⟨δ, hδ, m₀, hm₀, hlow⟩ := exists_Xi_sq_lower
  set m : ℝ := m₀ * (2 * δ) with hmdef
  have hm : 0 < m := by rw [hmdef]; positivity
  have hintR : ∀ J ∈ I, c J * m ≤ intR (F J) := by
    intro J hJ
    have hint : Integrable (fun t : ℝ => (F J t).re) := (TestClass.integrable_re (hF J hJ).1)
    have hs : ∫ t in Set.Icc (-δ) δ, (F J t).re ≤ ∫ t : ℝ, (F J t).re :=
      setIntegral_le_integral hint (Eventually.of_forall fun t => ConeG.re_nonneg (hF J hJ) t)
    have hc' : (c J * m₀) * (volume.real (Set.Icc (-δ) δ)) ≤
        ∫ t in Set.Icc (-δ) δ, (F J (t : ℂ)).re :=
      setIntegral_ge_of_const_le_real measurableSet_Icc (by simp [Real.volume_Icc])
        (fun t ht => (mul_le_mul_of_nonneg_left (hlow t ht) (hc J hJ).le).trans (hdom J hJ t))
        hint.integrableOn
    have hvol : volume.real (Set.Icc (-δ) δ) = 2 * δ := by
      rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [hvol] at hc'
    have : intR (F J) = ∫ t : ℝ, (F J t).re := rfl
    rw [this, hmdef]
    linarith
  have hS : CondS := by
    have hκ : ∀ J ∈ I, kappaStar ≤ ((max (Arch (F J) / c J) 0 / m : ℝ) : EReal) := by
      intro J hJ
      have hpos : 0 < intR (F J) := lt_of_lt_of_le (mul_pos (hc J hJ) hm) (hintR J hJ)
      have h1 := slack_le homog_Arch (scalable_ConeG_Arch xi2) (hF J hJ) hpos
      refine h1.trans (EReal.coe_le_coe_iff.mpr ?_)
      rcases le_or_gt 0 (Arch (F J)) with hA | hA
      · calc Arch (F J) / intR (F J) ≤ Arch (F J) / (c J * m) :=
              div_le_div_of_nonneg_left hA (mul_pos (hc J hJ) hm) (hintR J hJ)
          _ = (Arch (F J) / c J) / m := by rw [div_div]
          _ ≤ max (Arch (F J) / c J) 0 / m := by gcongr; exact le_max_left _ _
      · have : Arch (F J) / intR (F J) < 0 := div_neg_of_neg_of_pos hA hpos
        have : 0 ≤ max (Arch (F J) / c J) 0 / m := by positivity
        linarith
    have hlim2 : Tendsto (fun J => max (Arch (F J) / c J) 0 / m) (atTop ⊓ 𝓟 I) (𝓝 0) := by
      have h := (hlim.max (tendsto_const_nhds (x := (0 : ℝ)))).div_const m
      rwa [max_self, zero_div] at h
    have hlim3 : Tendsto (fun J => ((max (Arch (F J) / c J) 0 / m : ℝ) : EReal)) (atTop ⊓ 𝓟 I)
        (𝓝 ((0 : ℝ) : EReal)) := (continuous_coe_real_ereal.tendsto 0).comp hlim2
    have h0 := ge_of_tendsto hlim3 (hevI.mono hκ)
    unfold CondS
    exact_mod_cast h0
  exact ⟨hU, hS, hRE, hfin hS⟩

end PosRig
