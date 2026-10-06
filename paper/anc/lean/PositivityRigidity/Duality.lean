/-
§2.2–2.4: weak duality (Lemma 2.5), complementary slackness (Lemma 2.13), duality (Theorem 2.7(a)),
floors (Proposition 2.8) and the conductor form (Proposition 2.10).
-/
import PositivityRigidity.Sanity
import PositivityRigidity.Ledger

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

/-! ## Real form of the identity -/

theorem integral_eq_ofReal_of_ae_real {μ : Measure ℝ} {f : ℝ → ℂ}
    (h : ∀ᵐ x ∂μ, (f x).im = 0) : ∫ x, f x ∂μ = ((∫ x, (f x).re ∂μ : ℝ) : ℂ) := by
  have h' : (fun x => f x) =ᵐ[μ] fun x => (((f x).re : ℝ) : ℂ) := by
    filter_upwards [h] with x hx
    exact Complex.ext (by simp) (by simp [hx])
  rw [integral_congr_ae h', integral_complex_ofReal]

/-- The identity of Definition 2.4 in real form. -/
theorem Admissible.real_identity {A : (ℂ → ℂ) → ℝ} {g : ℝ} {p : Pair} (hp : Admissible A g p)
    {F : ℂ → ℂ} (hF : F ∈ TestClass) :
    A F = (∫ t, (F t).re ∂p.μ) + (1 / Real.pi) * ∫ ξ, (FT F ξ).re ∂p.ν := by
  obtain ⟨-, -, h⟩ := hp
  obtain ⟨-, -, hid⟩ := h F hF
  have h1 : ∫ t, F t ∂p.μ = ((∫ t, (F t).re ∂p.μ : ℝ) : ℂ) :=
    integral_eq_ofReal_of_ae_real (Eventually.of_forall fun t => TestClass.real hF t)
  have h2 : ∫ ξ, FT F ξ ∂p.ν = ((∫ ξ, (FT F ξ).re ∂p.ν : ℝ) : ℂ) :=
    integral_eq_ofReal_of_ae_real (Eventually.of_forall fun ξ => TestClass.FT_real hF ξ)
  rw [h1, h2] at hid
  have h3 : ((1 / Real.pi : ℂ)) = ((1 / Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [h3] at hid
  exact_mod_cast hid

theorem Admissible.integrable_re {A : (ℂ → ℂ) → ℝ} {g : ℝ} {p : Pair} (hp : Admissible A g p)
    {F : ℂ → ℂ} (hF : F ∈ TestClass) :
    Integrable (fun t : ℝ => (F t).re) p.μ ∧ Integrable (fun ξ : ℝ => (FT F ξ).re) p.ν := by
  obtain ⟨-, -, h⟩ := hp
  obtain ⟨h1, h2, -⟩ := h F hF
  exact ⟨h1.re, h2.re⟩

theorem ConeG.re_nonneg {g : ℝ} {F : ℂ → ℂ} (hF : F ∈ ConeG g) (t : ℝ) : 0 ≤ (F t).re :=
  (Complex.nonneg_iff.mp (hF.2.1 t)).1

theorem ConeG.FT_re_nonneg {g : ℝ} {F : ℂ → ℂ} (hF : F ∈ ConeG g) {ξ : ℝ} (hξ : g ≤ ξ) :
    0 ≤ (FT F ξ).re :=
  (Complex.nonneg_iff.mp (hF.2.2 ξ hξ)).1

theorem Admissible.ae_Ici {A : (ℂ → ℂ) → ℝ} {g : ℝ} {p : Pair} (hp : Admissible A g p) :
    ∀ᵐ ξ ∂p.ν, g ≤ ξ := by
  have h := hp.2.1
  unfold CarriedBy at h
  rw [ae_iff]
  simpa [Set.compl_def] using h

/-- The two parts `∫ F dμ` and `∫ F̂ dν` of `ℛ_{μ,ν}(F)` are non-negative for `F` in the cone. -/
theorem Admissible.parts_nonneg {A : (ℂ → ℂ) → ℝ} {g : ℝ} {p : Pair} (hp : Admissible A g p)
    {F : ℂ → ℂ} (hF : F ∈ ConeG g) :
    0 ≤ ∫ t, (F t).re ∂p.μ ∧ 0 ≤ ∫ ξ, (FT F ξ).re ∂p.ν := by
  refine ⟨integral_nonneg fun t => ConeG.re_nonneg hF t, integral_nonneg_of_ae ?_⟩
  filter_upwards [hp.ae_Ici] with ξ hξ
  exact ConeG.FT_re_nonneg hF hξ

/-! ## Lemma 2.5 (weak duality) -/

/-- **Lemma 2.5, first consequence.** `A(F) ≥ 0` for every admissible pair and `F` in the cone. -/
theorem weak_duality_nonneg {A : (ℂ → ℂ) → ℝ} {g : ℝ} {p : Pair} (hp : Admissible A g p)
    {F : ℂ → ℂ} (hF : F ∈ ConeG g) : 0 ≤ A F := by
  rw [hp.real_identity hF.1]
  obtain ⟨h1, h2⟩ := hp.parts_nonneg hF
  have : 0 ≤ 1 / Real.pi := by positivity
  positivity

/-- **Lemma 2.5 (weak duality).**  Let `(μ, ν)` be admissible (for `A`, at the gap `g`) and `F` in the
cone `𝒞_g`.  For Borel sets `I, J ⊆ ℝ` and lower bounds `0 ≤ a ≤ F` on `I`, `0 ≤ b ≤ F̂` on `J`,
`a μ(I) + (1/π) b ν(J) ≤ A(F)` (in `[0, ∞]`; in particular the masses are finite when `a, b > 0`).
The paper takes `J ⊆ [ξ₂, ∞)`; the statement holds for all Borel `J` since `ν` lives on `[g, ∞)`. -/
theorem weak_duality {A : (ℂ → ℂ) → ℝ} {g : ℝ} {p : Pair} (hp : Admissible A g p)
    {F : ℂ → ℂ} (hF : F ∈ ConeG g) {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J)
    {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (haI : ∀ t ∈ I, a ≤ (F t).re)
    (hbJ : ∀ ξ ∈ J, b ≤ (FT F ξ).re) :
    ENNReal.ofReal a * p.μ I + ENNReal.ofReal (b / Real.pi) * p.ν J ≤ ENNReal.ofReal (A F) := by
  obtain ⟨hiμ, hiν⟩ := hp.integrable_re hF.1
  obtain ⟨h1, h2⟩ := hp.parts_nonneg hF
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [hp.real_identity hF.1, ENNReal.ofReal_add h1 (by positivity)]
  gcongr
  · -- zero side
    rw [ofReal_integral_eq_lintegral_ofReal hiμ (Eventually.of_forall fun t => ConeG.re_nonneg hF t)]
    calc ENNReal.ofReal a * p.μ I = ∫⁻ _ in I, ENNReal.ofReal a ∂p.μ := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ t in I, ENNReal.ofReal (F t).re ∂p.μ :=
          setLIntegral_mono' hI fun t ht => ENNReal.ofReal_le_ofReal (haI t ht)
      _ ≤ ∫⁻ t, ENNReal.ofReal (F t).re ∂p.μ := setLIntegral_le_lintegral _ _
  · -- prime side
    have hnn : 0 ≤ᵐ[p.ν] fun ξ => (FT F ξ).re := by
      filter_upwards [hp.ae_Ici] with ξ hξ
      exact ConeG.FT_re_nonneg hF hξ
    have key : ENNReal.ofReal b * p.ν J ≤ ENNReal.ofReal (∫ ξ, (FT F ξ).re ∂p.ν) := by
      rw [ofReal_integral_eq_lintegral_ofReal hiν hnn]
      calc ENNReal.ofReal b * p.ν J = ∫⁻ _ in J, ENNReal.ofReal b ∂p.ν := by
            rw [setLIntegral_const, mul_comm]
        _ ≤ ∫⁻ ξ in J, ENNReal.ofReal (FT F ξ).re ∂p.ν :=
            setLIntegral_mono' hJ fun ξ hξ => ENNReal.ofReal_le_ofReal (hbJ ξ hξ)
        _ ≤ ∫⁻ ξ, ENNReal.ofReal (FT F ξ).re ∂p.ν := setLIntegral_le_lintegral _ _
    have e1 : ENNReal.ofReal (b / Real.pi) = ENNReal.ofReal b * ENNReal.ofReal (1 / Real.pi) := by
      rw [← ENNReal.ofReal_mul hb]; ring_nf
    have e2 : ENNReal.ofReal (1 / Real.pi * ∫ ξ, (FT F ξ).re ∂p.ν)
        = ENNReal.ofReal (∫ ξ, (FT F ξ).re ∂p.ν) * ENNReal.ofReal (1 / Real.pi) := by
      rw [← ENNReal.ofReal_mul h2, mul_comm]
    rw [e1, e2, mul_right_comm]
    gcongr

/-- **Lemma 2.5, last consequence.** If `F ∈ 𝒞_g` and `∫ F = 1`, no admissible `μ` satisfies
`μ ≥ λ dt` with `λ > A(F)`. -/
theorem not_dominatesLeb_of_cone {A : (ℂ → ℂ) → ℝ} {g : ℝ} {p : Pair} (hp : Admissible A g p)
    {F : ℂ → ℂ} (hF : F ∈ ConeG g) (h1 : intR F = 1) {lam : ℝ} (hlam : A F < lam) :
    ¬ DominatesLeb p.μ lam := by
  intro hdom
  have hA := weak_duality_nonneg hp hF
  have hlam0 : 0 < lam := lt_of_le_of_lt hA hlam
  obtain ⟨hiμ, -⟩ := hp.integrable_re hF.1
  obtain ⟨-, h2⟩ := hp.parts_nonneg hF
  have hmono : ∫ t, (F t).re ∂(ENNReal.ofReal lam • (volume : Measure ℝ)) ≤ ∫ t, (F t).re ∂p.μ :=
    integral_mono_measure hdom (Eventually.of_forall fun t => ConeG.re_nonneg hF t) hiμ
  rw [integral_smul_measure, ENNReal.toReal_ofReal hlam0.le] at hmono
  have hint : ∫ t : ℝ, (F t).re = 1 := h1
  rw [hint] at hmono
  have hreal := hp.real_identity hF.1
  have : 0 ≤ 1 / Real.pi * ∫ ξ, (FT F ξ).re ∂p.ν := by positivity
  simp only [smul_eq_mul, mul_one] at hmono
  linarith

/-- **Lemma 2.5, middle consequences.** `μ(I) ≤ A(F)` if `F ≥ 1` on `I`, and `ν(J) ≤ π A(F)` if `F̂ ≥ 1`
on `J`. -/
theorem weak_duality_masses {A : (ℂ → ℂ) → ℝ} {g : ℝ} {p : Pair} (hp : Admissible A g p)
    {F : ℂ → ℂ} (hF : F ∈ ConeG g) {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J) :
    ((∀ t ∈ I, 1 ≤ (F t).re) → p.μ I ≤ ENNReal.ofReal (A F)) ∧
    ((∀ ξ ∈ J, 1 ≤ (FT F ξ).re) → p.ν J ≤ ENNReal.ofReal (Real.pi * A F)) := by
  constructor
  · intro h
    have := weak_duality hp hF hI (MeasurableSet.empty) (a := 1) (b := 0) zero_le_one le_rfl h
      (by simp)
    simpa using this
  · intro h
    have := weak_duality hp hF (MeasurableSet.empty) hJ (a := 0) (b := 1) le_rfl zero_le_one
      (by simp) h
    simp only [ENNReal.ofReal_zero, zero_mul, zero_add] at this
    have hpi : 0 < Real.pi := Real.pi_pos
    have e : ENNReal.ofReal (Real.pi * A F)
        = ENNReal.ofReal Real.pi * ENNReal.ofReal (A F) := ENNReal.ofReal_mul hpi.le
    have e2 : ENNReal.ofReal Real.pi * ENNReal.ofReal (1 / Real.pi) = 1 := by
      rw [← ENNReal.ofReal_mul hpi.le, mul_one_div_cancel hpi.ne', ENNReal.ofReal_one]
    calc p.ν J = ENNReal.ofReal Real.pi * (ENNReal.ofReal (1 / Real.pi) * p.ν J) := by
          rw [← mul_assoc, e2, one_mul]
      _ ≤ ENNReal.ofReal Real.pi * ENNReal.ofReal (A F) := by gcongr
      _ = ENNReal.ofReal (Real.pi * A F) := e.symm

/-! ## Lemma 2.13 (complementary slackness) -/

/-- **Lemma 2.13 (complementary slackness),** at a general gap `g` and for a general functional: if
`F ∈ 𝒞_g` and `A(F) = 0`, every admissible pair has `μ` carried by `Z(F)` and `ν` carried by
`{ξ ≥ g : F̂(ξ) = 0}`. -/
theorem comp_slackness_gen {A : (ℂ → ℂ) → ℝ} {g : ℝ} {p : Pair} (hp : Admissible A g p)
    {F : ℂ → ℂ} (hF : F ∈ ConeG g) (h0 : A F = 0) :
    CarriedBy p.μ (ZF F) ∧ CarriedBy p.ν {ξ | g ≤ ξ ∧ FT F ξ = 0} := by
  obtain ⟨hiμ, hiν⟩ := hp.integrable_re hF.1
  obtain ⟨h1, h2⟩ := hp.parts_nonneg hF
  have hid := hp.real_identity hF.1
  have hpi : 0 < 1 / Real.pi := by have := Real.pi_pos; positivity
  have hX : ∫ t : ℝ, (F t).re ∂p.μ = 0 := by nlinarith
  have hY : ∫ ξ, (FT F ξ).re ∂p.ν = 0 := by nlinarith
  constructor
  · have hae : (fun t : ℝ => (F t).re) =ᵐ[p.μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun t => ConeG.re_nonneg hF t) hiμ).mp hX
    unfold CarriedBy ZF
    have : ∀ᵐ t : ℝ ∂p.μ, F t = 0 := by
      filter_upwards [hae] with t ht
      exact Complex.ext (by simpa using ht) (by simpa using TestClass.real hF.1 t)
    rw [ae_iff] at this
    simpa [Set.compl_def] using this
  · have hnn : 0 ≤ᵐ[p.ν] fun ξ => (FT F ξ).re := by
      filter_upwards [hp.ae_Ici] with ξ hξ
      exact ConeG.FT_re_nonneg hF hξ
    have hae : (fun ξ => (FT F ξ).re) =ᵐ[p.ν] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnn hiν).mp hY
    unfold CarriedBy
    have : ∀ᵐ ξ ∂p.ν, g ≤ ξ ∧ FT F ξ = 0 := by
      filter_upwards [hae, hp.ae_Ici] with ξ hξ hg
      exact ⟨hg, Complex.ext (by simpa using hξ) (by simpa using TestClass.FT_real hF.1 ξ)⟩
    rw [ae_iff] at this
    simpa [Set.compl_def] using this

/-- **Lemma 2.13 (complementary slackness).**  If `F ∈ 𝒞` and `𝒜(F) = 0`, then every `(μ, ν) ∈ 𝒦` has
`μ` carried by `Z(F)` and `ν` carried by `Ẑ(F)`. -/
theorem comp_slackness {F : ℂ → ℂ} (hF : F ∈ Cone) (h0 : Arch F = 0) {p : Pair} (hp : p ∈ K) :
    CarriedBy p.μ (ZF F) ∧ CarriedBy p.ν (ZhatF F) :=
  comp_slackness_gen hp hF h0

/-! ## Slacks of homogeneous functionals -/

/-- A functional that is positively homogeneous of degree one under real scaling. -/
def Homog (A : (ℂ → ℂ) → ℝ) : Prop := ∀ (F : ℂ → ℂ) (c : ℝ), A (fun z => (c : ℂ) * F z) = c * A F

theorem homog_Arch : Homog Arch := fun F c => Arch_smul F c

theorem homog_ArchShift (lam : ℝ) : Homog (ArchShift lam) := by
  intro F c
  simp only [ArchShift, Arch_smul, intR_smul]
  ring

theorem homog_Arch_q (q : ℝ) : Homog (Arch_q q) := homog_ArchShift _

theorem homog_ArchG (ks : List ℕ) (q : ℝ) : Homog (ArchG ks q) := fun F c => ArchG_smul ks q F c

/-- A set of functions closed under scaling by `c ≥ 0`, with `∫ F ≥ 0`, on which `A` vanishes when
`∫ F = 0`: the setting of the normalisation `F ↦ F/∫F`. -/
structure ScalableFor (A : (ℂ → ℂ) → ℝ) (C : Set (ℂ → ℂ)) : Prop where
  smul : ∀ F ∈ C, ∀ c : ℝ, 0 ≤ c → (fun z => (c : ℂ) * F z) ∈ C
  intR_nonneg : ∀ F ∈ C, 0 ≤ intR F
  null : ∀ F ∈ C, intR F = 0 → A F = 0

theorem scalable_ConeG_Arch (g : ℝ) : ScalableFor Arch (ConeG g) :=
  ⟨fun _ hF _ hc => ConeG.smul hF hc, fun _ hF => ConeG.intR_nonneg hF,
    fun _ hF h => ConeG.Arch_eq_zero_of_intR_eq_zero hF h⟩

theorem scalable_ConeG_ArchShift (g lam : ℝ) : ScalableFor (ArchShift lam) (ConeG g) :=
  ⟨fun _ hF _ hc => ConeG.smul hF hc, fun _ hF => ConeG.intR_nonneg hF,
    fun F hF h => by simp [ArchShift, ConeG.Arch_eq_zero_of_intR_eq_zero hF h, h]⟩

theorem scalable_ConeG_ArchG (g : ℝ) (ks : List ℕ) (q : ℝ) : ScalableFor (ArchG ks q) (ConeG g) :=
  ⟨fun _ hF _ hc => ConeG.smul hF hc, fun _ hF => ConeG.intR_nonneg hF,
    fun _ hF h => ConeG.ArchG_eq_zero_of_intR_eq_zero hF h ks q⟩

theorem ConeOPS_subset_Cone : ConeOPS ⊆ Cone := ConeOPS_subset_ConeG xi2

theorem scalable_ConeOPS_Arch : ScalableFor Arch ConeOPS :=
  ⟨fun _ hF _ hc => ConeOPS.smul hF hc,
    fun _ hF => ConeG.intR_nonneg (ConeOPS_subset_Cone hF),
    fun _ hF h => ConeG.Arch_eq_zero_of_intR_eq_zero (ConeOPS_subset_Cone hF) h⟩

/-- Normalisation: for `F ∈ C` with `∫ F > 0`, `F/∫F ∈ C` has integral `1` and `A(F/∫F) = A(F)/∫F`. -/
theorem normalize {A : (ℂ → ℂ) → ℝ} {C : Set (ℂ → ℂ)} (hA : Homog A) (hC : ScalableFor A C)
    {F : ℂ → ℂ} (hF : F ∈ C) (hpos : 0 < intR F) :
    (fun z => ((1 / intR F : ℝ) : ℂ) * F z) ∈ C ∧
      intR (fun z => ((1 / intR F : ℝ) : ℂ) * F z) = 1 ∧
      A (fun z => ((1 / intR F : ℝ) : ℂ) * F z) = A F / intR F := by
  refine ⟨hC.smul F hF _ (by positivity), ?_, ?_⟩
  · rw [intR_smul]; field_simp
  · rw [hA]; field_simp

/-- `slack A C ≤ A(F)/∫F` for `F ∈ C` with `∫ F > 0`. -/
theorem slack_le {A : (ℂ → ℂ) → ℝ} {C : Set (ℂ → ℂ)} (hA : Homog A) (hC : ScalableFor A C)
    {F : ℂ → ℂ} (hF : F ∈ C) (hpos : 0 < intR F) : slack A C ≤ ((A F / intR F : ℝ) : EReal) := by
  obtain ⟨h1, h2, h3⟩ := normalize hA hC hF hpos
  unfold slack
  rw [← h3]
  exact iInf₂_le _ ⟨h1, h2⟩

/-- `c ≤ slack A C` iff `A(F) ≥ c ∫ F` for every `F ∈ C`. -/
theorem le_slack_iff {A : (ℂ → ℂ) → ℝ} {C : Set (ℂ → ℂ)} (hA : Homog A) (hC : ScalableFor A C)
    (c : ℝ) : (c : EReal) ≤ slack A C ↔ ∀ F ∈ C, c * intR F ≤ A F := by
  constructor
  · intro h F hF
    rcases (hC.intR_nonneg F hF).eq_or_lt with h0 | hpos
    · rw [← h0, hC.null F hF h0.symm, mul_zero]
    · have := h.trans (slack_le hA hC hF hpos)
      have h' : c ≤ A F / intR F := by exact_mod_cast this
      rwa [le_div_iff₀ hpos] at h'
  · intro h
    unfold slack
    refine le_iInf₂ fun F hF => ?_
    have := h F hF.1
    rw [hF.2, mul_one] at this
    exact_mod_cast this

theorem slack_nonneg_iff {A : (ℂ → ℂ) → ℝ} {C : Set (ℂ → ℂ)} (hA : Homog A)
    (hC : ScalableFor A C) : 0 ≤ slack A C ↔ ∀ F ∈ C, 0 ≤ A F := by
  have := le_slack_iff hA hC 0
  simp only [EReal.coe_zero, zero_mul] at this
  exact this

/-- Two extended reals with the same real lower bounds are equal. -/
theorem EReal.eq_of_forall_coe_le_iff {x y : EReal} (h : ∀ c : ℝ, (c : EReal) ≤ x ↔ (c : EReal) ≤ y) :
    x = y := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨c, hc1, hc2⟩ := EReal.exists_between_coe_real hlt
    exact absurd ((h c).mpr hc2.le) (not_le.mpr hc1)
  · obtain ⟨c, hc1, hc2⟩ := EReal.exists_between_coe_real hlt
    exact absurd ((h c).mp hc2.le) (not_le.mpr hc1)

/-- `κ*(A + λ∫) = κ*(A) + λ` (`∫ F = 1` normalisation). -/
theorem slack_shift (g lam : ℝ) :
    slack (ArchShift lam) (ConeG g) = slack Arch (ConeG g) + (lam : EReal) := by
  apply EReal.eq_of_forall_coe_le_iff
  intro c
  rw [le_slack_iff (homog_ArchShift lam) (scalable_ConeG_ArchShift g lam)]
  have hcoe : ((c : ℝ) : EReal) ≤ slack Arch (ConeG g) + (lam : EReal) ↔
      (((c - lam : ℝ)) : EReal) ≤ slack Arch (ConeG g) := by
    rw [EReal.coe_sub]
    exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot lam))
      (Or.inl (EReal.coe_ne_top lam))).symm
  rw [hcoe, le_slack_iff homog_Arch (scalable_ConeG_Arch g)]
  constructor
  · intro h F hF
    have := h F hF
    simp only [ArchShift] at this
    linarith
  · intro h F hF
    have := h F hF
    simp only [ArchShift]
    linarith

/-! ## Theorem 2.7(a) (duality) -/

/-- **Theorem 2.7(a), (i) ⇔ (ii), for `𝒜 + λ∫`.**  (i) ⇒ (ii) is weak duality (Lemma 2.5);
(ii) ⇒ (i) is the ledger axiom `duality_no_gap`. -/
theorem duality_shift (lam : ℝ) :
    (Kset (ArchShift lam) xi2).Nonempty ↔ ∀ F ∈ Cone, 0 ≤ ArchShift lam F := by
  constructor
  · rintro ⟨p, hp⟩ F hF
    exact weak_duality_nonneg hp hF
  · intro h
    obtain ⟨p, hp⟩ := duality_no_gap lam h
    exact ⟨p, hp⟩

theorem ArchShift_zero : ArchShift 0 = Arch := by
  funext F; simp [ArchShift]

/-- **Theorem 2.7(a), (i) ⇔ (ii).** `𝒦 ≠ ∅` iff `𝒜 ≥ 0` on `𝒞`. -/
theorem duality_i_ii : K.Nonempty ↔ ∀ F ∈ Cone, 0 ≤ Arch F := by
  have := duality_shift 0
  rw [ArchShift_zero] at this
  exact this

/-- **Theorem 2.7(a), (ii) ⇔ (iii).** `𝒜 ≥ 0` on `𝒞` iff `𝒜 ≥ 0` on `𝒞 ∩ 𝒢`. -/
theorem duality_ii_iii : (∀ F ∈ Cone, 0 ≤ Arch F) ↔ ∀ F ∈ Cone ∩ Gset, 0 ≤ Arch F :=
  ⟨fun h F hF => h F hF.1, duality_gaussian⟩

/-- **Theorem 2.7(a), (ii) ⇔ (iv).** `𝒜 ≥ 0` on `𝒞` iff `κ* ≥ 0` (homogeneity; no axiom). -/
theorem duality_ii_iv : (∀ F ∈ Cone, 0 ≤ Arch F) ↔ 0 ≤ kappaStar :=
  (slack_nonneg_iff homog_Arch (scalable_ConeG_Arch xi2)).symm

/-- **Theorem 2.7(a) (duality).**  (i) `𝒦 ≠ ∅` ⇔ (ii) `𝒜 ≥ 0` on `𝒞` ⇔ (iii) `𝒜 ≥ 0` on `𝒞 ∩ 𝒢`
⇔ (iv) `κ* ≥ 0`. -/
theorem duality :
    (K.Nonempty ↔ ∀ F ∈ Cone, 0 ≤ Arch F) ∧
    ((∀ F ∈ Cone, 0 ≤ Arch F) ↔ ∀ F ∈ Cone ∩ Gset, 0 ≤ Arch F) ∧
    ((∀ F ∈ Cone, 0 ≤ Arch F) ↔ 0 ≤ kappaStar) :=
  ⟨duality_i_ii, duality_ii_iii, duality_ii_iv⟩

/-- (E) ⇒ `κ* ≥ 0`: weak duality only (no ledger axiom). -/
theorem kappaStar_nonneg_of_condE (hE : CondE) : 0 ≤ kappaStar := by
  obtain ⟨p, hp⟩ := hE
  exact duality_ii_iv.mp fun F hF => weak_duality_nonneg hp hF

theorem condE_iff_kappaStar_nonneg : CondE ↔ 0 ≤ kappaStar :=
  duality_i_ii.trans duality_ii_iv

/-! ## κ* is finite (Proposition 2.8) -/

theorem kappaStar_le_gauss : kappaStar ≤ ((Arch gauss : ℝ) : EReal) := by
  unfold kappaStar slack
  exact iInf₂_le gauss ⟨gauss_mem_Cone, intR_gauss⟩

theorem kappaStar_ne_top : kappaStar ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) kappaStar_le_gauss

theorem kappaStar_ge_floor : ((-(13231 / 10000 : ℝ)) : EReal) ≤ kappaStar := by
  unfold kappaStar slack
  exact le_iInf₂ fun F hF => by exact_mod_cast floor_bound F hF.1 hF.2

theorem kappaStar_ne_bot : kappaStar ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) kappaStar_ge_floor

theorem kappaStar_coe : ((kappaStar.toReal : ℝ) : EReal) = kappaStar :=
  EReal.coe_toReal kappaStar_ne_top kappaStar_ne_bot

theorem kappaOPS_ne_top : kappaOPS ≠ ⊤ := by
  refine ne_top_of_le_ne_top (EReal.coe_ne_top (Arch gauss)) ?_
  unfold kappaOPS slack
  exact iInf₂_le gauss ⟨gauss_mem_ConeOPS, intR_gauss⟩

/-- `κ* ≤ κ*_OPS` (`𝒞_OPS ⊆ 𝒞`, Definition 2.4). -/
theorem kappaStar_le_kappaOPS : kappaStar ≤ kappaOPS := by
  unfold kappaStar kappaOPS slack
  exact le_iInf₂ fun F hF => iInf₂_le F ⟨ConeOPS_subset_Cone hF.1, hF.2⟩

/-! ## Proposition 2.8 (floors) -/

/-- Floor feasibility of `λ`: there are an even positive `μ'` and a positive `ν` on `[ξ₂, ∞)`
representing `𝒜 − λ∫` on `𝒯`.  This is the reformulation in the first line of the proof of
Proposition 2.8 of "an even real Radon measure `μ` with `μ − λ dt ≥ 0` and a positive `ν` with
`𝒜 = ℛ_{μ,ν}` on `𝒯`" (take `μ' = μ − λ dt`). -/
def FloorFeasible (lam : ℝ) : Prop := ∃ p : Pair, Admissible (ArchShift (-lam)) xi2 p

theorem floorFeasible_iff (lam : ℝ) : FloorFeasible lam ↔ (lam : EReal) ≤ kappaStar := by
  unfold FloorFeasible
  rw [show (∃ p : Pair, Admissible (ArchShift (-lam)) xi2 p) ↔
      (Kset (ArchShift (-lam)) xi2).Nonempty from Iff.rfl, duality_shift,
    show kappaStar = slack Arch (ConeG xi2) from rfl,
    le_slack_iff homog_Arch (scalable_ConeG_Arch xi2) lam]
  constructor
  · intro h F hF
    have := h F hF
    simp only [ArchShift] at this
    linarith
  · intro h F hF
    have := h F hF
    simp only [ArchShift]
    linarith

/-- **Proposition 2.8 (floors).**  `κ*` is finite, and it is the largest `λ` that is floor-feasible
(the maximum is attained). -/
theorem prop_2_8 :
    kappaStar ≠ ⊥ ∧ kappaStar ≠ ⊤ ∧ IsGreatest {lam : ℝ | FloorFeasible lam} kappaStar.toReal := by
  refine ⟨kappaStar_ne_bot, kappaStar_ne_top, ?_, ?_⟩
  · show FloorFeasible kappaStar.toReal
    rw [floorFeasible_iff, kappaStar_coe]
  · intro lam hlam
    have h := (floorFeasible_iff lam).mp hlam
    rw [← kappaStar_coe] at h
    exact_mod_cast h

/-- Adding `c dt` (`c ≥ 0`) to the zero measure turns a pair admissible for `A − c∫` into one admissible
for `A`. -/
theorem admissible_add_leb {A : (ℂ → ℂ) → ℝ} {g c : ℝ} (hc : 0 ≤ c) {p : Pair}
    (hp : Admissible (fun F => A F - c * intR F) g p) :
    Admissible A g ⟨p.μ + ENNReal.ofReal c • volume, p.ν⟩ := by
  obtain ⟨heven, hcar, hid⟩ := hp
  refine ⟨?_, hcar, ?_⟩
  · show Measure.map (fun t : ℝ => -t) (p.μ + ENNReal.ofReal c • volume) =
      p.μ + ENNReal.ofReal c • volume
    rw [Measure.map_add _ _ measurable_neg, Measure.map_smul]
    unfold EvenMeasure at heven
    rw [heven]
    congr 2
    exact Measure.IsNegInvariant.neg_eq_self (μ := (volume : Measure ℝ))
  · intro F hF
    obtain ⟨h1, h2, h3⟩ := hid F hF
    have hint : Integrable (onR F) (ENNReal.ofReal c • (volume : Measure ℝ)) :=
      (TestClass.integrable hF).smul_measure ENNReal.ofReal_ne_top
    refine ⟨h1.add_measure hint, h2, ?_⟩
    show ((A F : ℝ) : ℂ) = (∫ t, onR F t ∂(p.μ + ENNReal.ofReal c • volume)) +
      (1 / Real.pi : ℂ) * ∫ ξ, FT F ξ ∂p.ν
    rw [integral_add_measure h1 hint, integral_smul_measure, ENNReal.toReal_ofReal hc]
    have hI : ∫ t : ℝ, onR F t = ((intR F : ℝ) : ℂ) := TestClass.integral_eq hF
    rw [hI]
    have h3' : ((A F : ℝ) : ℂ) = ((A F - c * intR F : ℝ) : ℂ) + ((c * intR F : ℝ) : ℂ) := by
      push_cast; ring
    rw [h3']
    have h3'' : ((A F - c * intR F : ℝ) : ℂ) = (∫ t, onR F t ∂p.μ) +
        (1 / Real.pi : ℂ) * ∫ ξ, FT F ξ ∂p.ν := h3
    rw [h3'', Complex.real_smul]
    push_cast
    ring

/-- The hypothesis of the ledger axiom `duality_no_gap` holds for every `λ ≥ 1.3231` (from
`floor_bound`): the axiom is not vacuous. -/
theorem duality_no_gap_hyp_of_ge {lam : ℝ} (hlam : (13231 / 10000 : ℝ) ≤ lam) :
    ∀ F ∈ Cone, 0 ≤ ArchShift lam F := by
  intro F hF
  have hfl : ((-(13231 / 10000 : ℝ) : ℝ) : EReal) ≤ slack Arch (ConeG xi2) := kappaStar_ge_floor
  have h := (le_slack_iff homog_Arch (scalable_ConeG_Arch xi2) _).mp hfl F hF
  have h0 := ConeG.intR_nonneg hF
  unfold ArchShift
  nlinarith

/-- Consequently `duality_no_gap` produces admissible pairs for `𝒜 + λ∫`, `λ ≥ 1.3231`. -/
theorem exists_admissible_shift {lam : ℝ} (hlam : (13231 / 10000 : ℝ) ≤ lam) :
    (Kset (ArchShift lam) xi2).Nonempty :=
  (duality_shift lam).mpr (duality_no_gap_hyp_of_ge hlam)

/-- **Proposition 2.8, last sentence.**  `κ* ≥ 0` iff some admissible `μ` dominates `κ* dt`. -/
theorem prop_2_8_dominates : 0 ≤ kappaStar ↔ ∃ p ∈ K, DominatesLeb p.μ kappaStar.toReal := by
  constructor
  · intro h0
    have hfeas : FloorFeasible kappaStar.toReal := prop_2_8.2.2.1
    obtain ⟨p, hp⟩ := hfeas
    have hk : 0 ≤ kappaStar.toReal := EReal.toReal_nonneg h0
    have hp' : Admissible (fun F => Arch F - kappaStar.toReal * intR F) xi2 p := by
      have : (fun F => Arch F - kappaStar.toReal * intR F) = ArchShift (-kappaStar.toReal) := by
        funext F; simp [ArchShift]; ring
      rw [this]; exact hp
    refine ⟨_, admissible_add_leb hk hp', ?_⟩
    show ENNReal.ofReal kappaStar.toReal • (volume : Measure ℝ) ≤
      p.μ + ENNReal.ofReal kappaStar.toReal • volume
    exact Measure.le_add_left le_rfl
  · rintro ⟨p, hp, -⟩
    exact condE_iff_kappaStar_nonneg.mp ⟨p, hp⟩

/-! ## Proposition 2.10 (conductor form) -/

theorem Arch_q_eq_shift (q : ℝ) : Arch_q q = ArchShift (Real.log q / (2 * Real.pi)) := rfl

/-- **Proposition 2.10, first identity.** `κ*(𝒜_q) = κ* + log q/(2π)`. -/
theorem slack_Arch_q (q : ℝ) :
    slack (Arch_q q) Cone = kappaStar + ((Real.log q / (2 * Real.pi) : ℝ) : EReal) :=
  slack_shift xi2 _

/-- **Proposition 2.10.**  For `q > 0`, `𝒦(𝒜_q) ≠ ∅` iff `q ≥ q_min = e^{−2πκ*}`. -/
theorem conductor_form {q : ℝ} (hq : 0 < q) :
    (Kset (Arch_q q) xi2).Nonempty ↔ qmin ≤ q := by
  rw [Arch_q_eq_shift, duality_shift, ← Arch_q_eq_shift]
  have hsl := slack_nonneg_iff (C := Cone) (homog_Arch_q q) (scalable_ConeG_ArchShift xi2 _)
  rw [← hsl, slack_Arch_q]
  have hk := kappaStar_coe
  unfold qmin
  rw [← hk, ← EReal.coe_add, EReal.coe_nonneg, EReal.toReal_coe]
  rw [← Real.le_log_iff_exp_le hq]
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor
  · intro h
    have : -kappaStar.toReal ≤ Real.log q / (2 * Real.pi) := by linarith
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  · intro h
    have : -kappaStar.toReal ≤ Real.log q / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith

/-- **Proposition 2.10.** `(S) ⇔ q_min ≥ 1`. -/
theorem condS_iff_qmin : CondS ↔ 1 ≤ qmin := by
  unfold CondS qmin
  have hk := kappaStar_coe
  rw [← hk, EReal.coe_nonpos, EReal.toReal_coe, Real.one_le_exp_iff]
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Proposition 2.10, the bound.**  A test function `F ∈ 𝒞` with `∫ F = 1` certifies
`log q ≥ −2π 𝒜(F)` for every conductor `q > 0` admitting a positive solution. -/
theorem conductor_bound {F : ℂ → ℂ} (hF : F ∈ Cone) (h1 : intR F = 1) {q : ℝ} (_hq : 0 < q)
    (hK : (Kset (Arch_q q) xi2).Nonempty) : -2 * Real.pi * Arch F ≤ Real.log q := by
  obtain ⟨p, hp⟩ := hK
  have := weak_duality_nonneg hp hF
  simp only [Arch_q, ArchShift, h1, mul_one] at this
  have hpi : 0 < Real.pi := Real.pi_pos
  have : 0 ≤ 2 * Real.pi * Arch F + Real.log q := by
    have h2 : Real.log q / (2 * Real.pi) * (2 * Real.pi) = Real.log q := by field_simp
    nlinarith
  linarith

end PosRig
