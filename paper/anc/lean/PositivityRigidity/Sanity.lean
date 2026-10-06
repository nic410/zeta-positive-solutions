/-
Sanity lemmas (Mathlib only): the definitions of `Basic.lean` are not vacuous, and elementary facts
about the test class used throughout.

* The Gaussian `e^{−πz²}` lies in every `𝒯_δ`, in `𝒢`, and in `𝒞_OPS ⊆ 𝒞_g` (all `g`), with `∫ = 1`;
  so `𝒯`, `𝒞`, `𝒞_OPS`, `𝒢 ∩ 𝒞` are non-empty and `κ* < ∞`.
* Admissible pairs are automatically Radon (locally finite).
* Scaling, continuity, integrability, realness of transforms.
-/
import PositivityRigidity.Basic

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder

namespace PosRig

/-- The Gaussian `e^{−πz²}`. -/
def gauss : ℂ → ℂ := fun z => Complex.exp (-(Real.pi : ℂ) * z ^ 2)

/-! ## The Gaussian -/

theorem gauss_ofReal (t : ℝ) : gauss t = ((Real.exp (-Real.pi * t ^ 2) : ℝ) : ℂ) := by
  simp only [gauss]
  push_cast
  ring_nf

theorem norm_gauss (z : ℂ) :
    ‖gauss z‖ = Real.exp (-Real.pi * z.re ^ 2 + Real.pi * z.im ^ 2) := by
  simp only [gauss, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, sq]
  ring

theorem differentiable_gauss : Differentiable ℂ gauss := by
  unfold gauss
  fun_prop

private theorem gauss_bound_aux (x : ℝ) : (2 + |x|) ^ 2 * Real.exp (-Real.pi * x ^ 2) ≤ 6 := by
  have h1 : (2 + |x|) ^ 2 ≤ 6 * (1 + x ^ 2) := by
    have hx : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [sq_nonneg (|x| - 1), abs_nonneg x]
  have h2 : 1 + x ^ 2 ≤ Real.exp (Real.pi * x ^ 2) := by
    have := Real.add_one_le_exp (Real.pi * x ^ 2)
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    nlinarith [sq_nonneg x]
  have hexp : Real.exp (-Real.pi * x ^ 2) = (Real.exp (Real.pi * x ^ 2))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [hexp]
  have hpos : 0 < Real.exp (Real.pi * x ^ 2) := Real.exp_pos _
  rw [← div_eq_mul_inv, div_le_iff₀ hpos]
  nlinarith

theorem gauss_inTδ {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) : InTδ δ gauss where
  pos := h0
  lt_half := h1
  even := fun z _ => by simp [gauss]
  real := fun t => by rw [gauss_ofReal, Complex.ofReal_im]
  analytic := fun z _ => differentiable_gauss.analyticAt z
  bound := by
    refine ⟨6 * Real.exp Real.pi, fun z hz => ?_⟩
    have hy : |z.im| ≤ 1 := by
      have : |z.im| ≤ 1 / 2 + δ := hz
      linarith
    have hy2 : z.im ^ 2 ≤ 1 := by
      have := sq_abs z.im
      nlinarith [abs_nonneg z.im]
    have hnorm : ‖z‖ ≤ |z.re| + 1 := by
      have := Complex.norm_le_abs_re_add_abs_im z
      linarith
    have h1z : (1 + ‖z‖) ^ 2 ≤ (2 + |z.re|) ^ 2 := by
      have : 0 ≤ 1 + ‖z‖ := by positivity
      nlinarith
    rw [norm_gauss]
    have hsplit : Real.exp (-Real.pi * z.re ^ 2 + Real.pi * z.im ^ 2)
        = Real.exp (-Real.pi * z.re ^ 2) * Real.exp (Real.pi * z.im ^ 2) := by
      rw [Real.exp_add]
    rw [hsplit]
    have he : Real.exp (Real.pi * z.im ^ 2) ≤ Real.exp Real.pi := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    have hA := gauss_bound_aux z.re
    calc (1 + ‖z‖) ^ 2 * (Real.exp (-Real.pi * z.re ^ 2) * Real.exp (Real.pi * z.im ^ 2))
        ≤ (2 + |z.re|) ^ 2 * (Real.exp (-Real.pi * z.re ^ 2) * Real.exp Real.pi) := by
          apply mul_le_mul h1z (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)
            (by positivity) (by positivity)
      _ = ((2 + |z.re|) ^ 2 * Real.exp (-Real.pi * z.re ^ 2)) * Real.exp Real.pi := by ring
      _ ≤ 6 * Real.exp Real.pi := by
          apply mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le

theorem gauss_mem_TestClass : gauss ∈ TestClass :=
  ⟨1 / 4, gauss_inTδ (by norm_num) (by norm_num)⟩

theorem FT_gauss (ξ : ℝ) : FT gauss ξ = ((Real.exp (-Real.pi * ξ ^ 2) : ℝ) : ℂ) := by
  have h := fourier_gaussian_pi (b := (1 : ℂ)) (by simp)
  have h2 : onR gauss = fun x : ℝ => cexp (-↑Real.pi * 1 * ↑x ^ 2) := by
    funext x; simp [onR, gauss]
  unfold FT
  rw [h2, h]
  simp only [one_cpow, div_one, one_div, one_mul]
  push_cast
  ring_nf

theorem intR_gauss : intR gauss = 1 := by
  unfold intR
  have : ∀ t : ℝ, (gauss t).re = Real.exp (-Real.pi * t ^ 2) := by
    intro t; rw [gauss_ofReal, Complex.ofReal_re]
  simp_rw [this]
  rw [integral_gaussian]
  simp

theorem gauss_mem_ConeOPS : gauss ∈ ConeOPS := by
  refine ⟨gauss_mem_TestClass, fun t => ?_, fun ξ => ?_⟩
  · rw [gauss_ofReal]
    exact Complex.zero_le_real.mpr (Real.exp_pos _).le
  · rw [FT_gauss]
    exact Complex.zero_le_real.mpr (Real.exp_pos _).le

theorem ConeOPS_subset_ConeG (g : ℝ) : ConeOPS ⊆ ConeG g :=
  fun _ hF => ⟨hF.1, hF.2.1, fun ξ _ => hF.2.2 ξ⟩

theorem gauss_mem_ConeG (g : ℝ) : gauss ∈ ConeG g := ConeOPS_subset_ConeG g gauss_mem_ConeOPS

theorem gauss_mem_Cone : gauss ∈ Cone := gauss_mem_ConeG xi2

theorem gauss_eq_gwp : gauss = gwp 0 0 1 := by
  funext z
  simp [gauss, gwp]

theorem gauss_mem_Gset : gauss ∈ Gset := by
  refine ⟨?_, fun t => ?_, fun t => ?_⟩
  · rw [gauss_eq_gwp]
    exact Submodule.subset_span ⟨0, 0, 1, one_pos, rfl⟩
  · simp [gauss]
  · rw [gauss_ofReal, Complex.ofReal_im]

theorem TestClass_nonempty : TestClass.Nonempty := ⟨gauss, gauss_mem_TestClass⟩

theorem Cone_nonempty : Cone.Nonempty := ⟨gauss, gauss_mem_Cone⟩

theorem ConeOPS_nonempty : ConeOPS.Nonempty := ⟨gauss, gauss_mem_ConeOPS⟩

theorem Cone_inter_Gset_nonempty : (Cone ∩ Gset).Nonempty := ⟨gauss, gauss_mem_Cone, gauss_mem_Gset⟩

/-! ## Elementary facts about the test class -/

theorem TestClass.real {F : ℂ → ℂ} (hF : F ∈ TestClass) (t : ℝ) : (F t).im = 0 := by
  obtain ⟨δ, h⟩ := hF
  exact h.real t

theorem ofReal_mem_closedStrip {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ((t : ℝ) : ℂ) ∈ closedStrip (1 / 2 + δ) := by
  show |((t : ℝ) : ℂ).im| ≤ 1 / 2 + δ
  rw [Complex.ofReal_im, abs_zero]
  linarith

theorem TestClass.continuous {F : ℂ → ℂ} (hF : F ∈ TestClass) : Continuous (onR F) := by
  obtain ⟨δ, h⟩ := hF
  have hc : ∀ t : ℝ, ContinuousAt F (t : ℂ) := fun t =>
    (h.analytic (t : ℂ) (ofReal_mem_closedStrip h.pos t)).continuousAt
  exact continuous_iff_continuousAt.mpr fun t =>
    (hc t).comp Complex.continuous_ofReal.continuousAt

theorem TestClass.integrable {F : ℂ → ℂ} (hF : F ∈ TestClass) : Integrable (onR F) := by
  obtain ⟨δ, h⟩ := hF
  obtain ⟨C, hC⟩ := h.bound
  have hcont : Continuous (onR F) := TestClass.continuous ⟨δ, h⟩
  have hint : Integrable (fun t : ℝ => C * (1 + ‖t‖) ^ (-(2 : ℝ))) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
    exact this.const_mul C
  refine hint.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have h1 := hC (t : ℂ) (ofReal_mem_closedStrip h.pos t)
  rw [Complex.norm_real] at h1
  have hpos : 0 < (1 + ‖t‖) ^ 2 := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_two, ← div_eq_mul_inv, le_div_iff₀ hpos]
  simpa [onR, mul_comm] using h1

theorem TestClass.integrable_re {F : ℂ → ℂ} (hF : F ∈ TestClass) :
    Integrable (fun t : ℝ => (F t).re) := by
  have := (TestClass.integrable hF).re
  simpa [onR] using this

theorem TestClass.integral_eq {F : ℂ → ℂ} (hF : F ∈ TestClass) :
    ∫ t : ℝ, F t = ((intR F : ℝ) : ℂ) := by
  have h : ∀ t : ℝ, F t = (((F t).re : ℝ) : ℂ) := fun t =>
    Complex.ext (by simp) (by simp [TestClass.real hF t])
  calc ∫ t : ℝ, F t = ∫ t : ℝ, (((F t).re : ℝ) : ℂ) :=
        integral_congr_ae (Eventually.of_forall h)
    _ = ((∫ t : ℝ, (F t).re : ℝ) : ℂ) := integral_ofReal
    _ = ((intR F : ℝ) : ℂ) := rfl

theorem TestClass.smul {F : ℂ → ℂ} (hF : F ∈ TestClass) (c : ℝ) :
    (fun z => (c : ℂ) * F z) ∈ TestClass := by
  obtain ⟨δ, h⟩ := hF
  obtain ⟨C, hC⟩ := h.bound
  refine ⟨δ, h.pos, h.lt_half, fun z hz => by simp [h.even z hz],
    fun t => by simp [h.real t], analyticOnNhd_const.mul h.analytic, ⟨|c| * C, fun z hz => ?_⟩⟩
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc (1 + ‖z‖) ^ 2 * (|c| * ‖F z‖) = |c| * ((1 + ‖z‖) ^ 2 * ‖F z‖) := by ring
    _ ≤ |c| * C := mul_le_mul_of_nonneg_left (hC z hz) (abs_nonneg c)

theorem FT_smul (F : ℂ → ℂ) (c : ℂ) (ξ : ℝ) : FT (fun z => c * F z) ξ = c * FT F ξ := by
  unfold FT onR
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp_rw [smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext v
  ring

theorem Arch_smul (F : ℂ → ℂ) (c : ℝ) : Arch (fun z => (c : ℂ) * F z) = c * Arch F := by
  unfold Arch
  have h1 : ((c : ℂ) * F (I / 2) + (c : ℂ) * F (-I / 2)).re = c * (F (I / 2) + F (-I / 2)).re := by
    rw [← mul_add, Complex.re_ofReal_mul]
  have h2 : ∫ t : ℝ, ((c : ℂ) * F t).re * Ωinf t = c * ∫ t : ℝ, (F t).re * Ωinf t := by
    rw [← integral_const_mul]
    congr 1
    funext t
    rw [Complex.re_ofReal_mul]
    ring
  rw [h1, h2]
  ring

theorem intR_smul (F : ℂ → ℂ) (c : ℝ) : intR (fun z => (c : ℂ) * F z) = c * intR F := by
  unfold intR
  rw [← integral_const_mul]
  congr 1
  funext t
  rw [Complex.re_ofReal_mul]

theorem ArchG_smul (ks : List ℕ) (q : ℝ) (F : ℂ → ℂ) (c : ℝ) :
    ArchG ks q (fun z => (c : ℂ) * F z) = c * ArchG ks q F := by
  unfold ArchG
  have h1 : ((c : ℂ) * F (I / 2) + (c : ℂ) * F (-I / 2)).re = c * (F (I / 2) + F (-I / 2)).re := by
    rw [← mul_add, Complex.re_ofReal_mul]
  have h2 : ∫ t : ℝ, ((c : ℂ) * F t).re * OmegaG ks t = c * ∫ t : ℝ, (F t).re * OmegaG ks t := by
    rw [← integral_const_mul]
    congr 1
    funext t
    rw [Complex.re_ofReal_mul]
    ring
  rw [h1, h2, intR_smul]
  ring

theorem ConeG.smul {g : ℝ} {F : ℂ → ℂ} (hF : F ∈ ConeG g) {c : ℝ} (hc : 0 ≤ c) :
    (fun z => (c : ℂ) * F z) ∈ ConeG g := by
  refine ⟨TestClass.smul hF.1 c, fun t => ?_, fun ξ hξ => ?_⟩
  · exact mul_nonneg (Complex.zero_le_real.mpr hc) (hF.2.1 t)
  · rw [FT_smul]
    exact mul_nonneg (Complex.zero_le_real.mpr hc) (hF.2.2 ξ hξ)

theorem ConeOPS.smul {F : ℂ → ℂ} (hF : F ∈ ConeOPS) {c : ℝ} (hc : 0 ≤ c) :
    (fun z => (c : ℂ) * F z) ∈ ConeOPS := by
  refine ⟨TestClass.smul hF.1 c, fun t => ?_, fun ξ => ?_⟩
  · exact mul_nonneg (Complex.zero_le_real.mpr hc) (hF.2.1 t)
  · rw [FT_smul]
    exact mul_nonneg (Complex.zero_le_real.mpr hc) (hF.2.2 ξ)

theorem ConeG.intR_nonneg {g : ℝ} {F : ℂ → ℂ} (hF : F ∈ ConeG g) : 0 ≤ intR F := by
  unfold intR
  exact integral_nonneg fun t => (Complex.nonneg_iff.mp (hF.2.1 t)).1

theorem closedStrip_eq (b : ℝ) : closedStrip b = Complex.im ⁻¹' Set.Icc (-b) b := by
  ext z
  simp [closedStrip, abs_le]

theorem isPreconnected_closedStrip (b : ℝ) : IsPreconnected (closedStrip b) := by
  rw [closedStrip_eq]
  exact ((convex_Icc (-b) b).linear_preimage Complex.imLm).isPreconnected

/-- A function of the cone with `∫ F = 0` vanishes on `ℝ`, hence (identity theorem) on the strip, so
`𝒜(F) = 0` and `∫ F Ω_𝔤 = 0` (used for `𝒞 ∋ F ↦ F/∫F` in Theorem 2.7). -/
theorem ConeG.eq_zero_of_intR_eq_zero {g : ℝ} {F : ℂ → ℂ} (hF : F ∈ ConeG g) (h : intR F = 0) :
    (∀ t : ℝ, F t = 0) ∧ F (Complex.I / 2) = 0 ∧ F (-Complex.I / 2) = 0 := by
  obtain ⟨hT, hpos, -⟩ := hF
  obtain ⟨δ, hδ⟩ := hT
  have hre_nonneg : ∀ t : ℝ, 0 ≤ (F t).re := fun t => (Complex.nonneg_iff.mp (hpos t)).1
  have hint : Integrable (fun t : ℝ => (F t).re) := TestClass.integrable_re ⟨δ, hδ⟩
  have hae : (fun t : ℝ => (F t).re) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hre_nonneg hint).mp h
  have hcont : Continuous (fun t : ℝ => (F t).re) :=
    Complex.continuous_re.comp (TestClass.continuous ⟨δ, hδ⟩)
  have hzero_re : (fun t : ℝ => (F t).re) = 0 :=
    (Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hae
  have hR : ∀ t : ℝ, F t = 0 := fun t =>
    Complex.ext (by simpa using congrFun hzero_re t) (by simpa using hδ.real t)
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), F z = 0 := by
    have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have := Complex.continuous_ofReal.tendsto (0 : ℝ)
        simpa using this.mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun t ht => by
          simpa using ht
    exact ht.frequently (Eventually.frequently (Eventually.of_forall fun t => hR t))
  have h0mem : (0 : ℂ) ∈ closedStrip (1 / 2 + δ) := by
    simpa using ofReal_mem_closedStrip hδ.pos 0
  have hEq := hδ.analytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (isPreconnected_closedStrip _) h0mem hfreq
  have hmem1 : Complex.I / 2 ∈ closedStrip (1 / 2 + δ) := by
    show |(Complex.I / 2).im| ≤ 1 / 2 + δ
    have : (Complex.I / 2).im = 1 / 2 := by simp
    rw [this, abs_of_pos (by norm_num)]
    linarith [hδ.pos]
  have hmem2 : -Complex.I / 2 ∈ closedStrip (1 / 2 + δ) := by
    show |(-Complex.I / 2).im| ≤ 1 / 2 + δ
    have : (-Complex.I / 2).im = -(1 / 2) := by simp; norm_num
    rw [this, abs_neg, abs_of_pos (by norm_num)]
    linarith [hδ.pos]
  exact ⟨hR, hEq hmem1, hEq hmem2⟩

theorem ConeG.Arch_eq_zero_of_intR_eq_zero {g : ℝ} {F : ℂ → ℂ} (hF : F ∈ ConeG g)
    (h : intR F = 0) : Arch F = 0 := by
  obtain ⟨hR, hp, hm⟩ := ConeG.eq_zero_of_intR_eq_zero hF h
  unfold Arch
  rw [hp, hm]
  simp [hR]

theorem ConeG.ArchG_eq_zero_of_intR_eq_zero {g : ℝ} {F : ℂ → ℂ} (hF : F ∈ ConeG g)
    (h : intR F = 0) (ks : List ℕ) (q : ℝ) : ArchG ks q F = 0 := by
  obtain ⟨hR, hp, hm⟩ := ConeG.eq_zero_of_intR_eq_zero hF h
  unfold ArchG
  rw [hp, hm, h]
  simp [hR]

/-- The Fourier transform of an even function that is real on `ℝ` is real. -/
theorem FT_real_of_even_real (F : ℂ → ℂ) (heven : ∀ t : ℝ, F (-(t : ℂ)) = F t)
    (hreal : ∀ t : ℝ, (F t).im = 0) (ξ : ℝ) : (FT F ξ).im = 0 := by
  have hF : ∀ v : ℝ, (starRingEnd ℂ) (F v) = F v := fun v => Complex.conj_eq_iff_im.mpr (hreal v)
  have hconj : (starRingEnd ℂ) (FT F ξ) = FT F ξ := by
    unfold FT onR
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
    simp_rw [smul_eq_mul, map_mul, hF]
    rw [← integral_neg_eq_self]
    congr 1
    funext v
    rw [← Complex.exp_conj]
    have h1 : F ((-v : ℝ) : ℂ) = F v := by
      rw [Complex.ofReal_neg, heven v]
    rw [h1]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  exact Complex.conj_eq_iff_im.mp hconj

theorem TestClass.FT_real {F : ℂ → ℂ} (hF : F ∈ TestClass) (ξ : ℝ) : (FT F ξ).im = 0 := by
  obtain ⟨δ, h⟩ := hF
  exact FT_real_of_even_real F (fun t => h.even t (ofReal_mem_closedStrip h.pos t)) h.real ξ

theorem TestClass.continuous_FT {F : ℂ → ℂ} (hF : F ∈ TestClass) : Continuous (FT F) := by
  unfold FT
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (TestClass.integrable hF)

/-! ## Admissible pairs are Radon -/

private theorem exp_bound_on_Ioo {x t : ℝ} (ht : t ∈ Set.Ioo (x - 1) (x + 1)) :
    Real.exp (-Real.pi * (|x| + 1) ^ 2) ≤ Real.exp (-Real.pi * t ^ 2) := by
  apply Real.exp_le_exp.mpr
  have h1 : |t| ≤ |x| + 1 := by
    have : |t - x| < 1 := by
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
    calc |t| = |x + (t - x)| := by ring_nf
      _ ≤ |x| + |t - x| := abs_add_le _ _
      _ ≤ |x| + 1 := by linarith
  have h2 : t ^ 2 ≤ (|x| + 1) ^ 2 := by
    have := sq_abs t
    nlinarith [abs_nonneg t]
  nlinarith [Real.pi_pos]

/-- The integrability clause of Definition 2.4, applied to the Gaussian (`e^{−πt²} > 0`, with transform
`e^{−πξ²} > 0`), makes both measures locally finite: Lean's `Admissible` is exactly the paper's
definition with "positive Radon measures". -/
theorem Admissible.isLocallyFinite {A : (ℂ → ℂ) → ℝ} {g : ℝ} {p : Pair} (hp : Admissible A g p) :
    IsLocallyFiniteMeasure p.μ ∧ IsLocallyFiniteMeasure p.ν := by
  obtain ⟨hμint, hνint, -⟩ := hp.2.2 gauss gauss_mem_TestClass
  constructor
  · refine ⟨fun x => ⟨Set.Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩⟩
    have hm : 0 < Real.exp (-Real.pi * (|x| + 1) ^ 2) := Real.exp_pos _
    refine lt_of_le_of_lt (measure_mono ?_) (hμint.measure_norm_ge_lt_top hm)
    intro t ht
    simp only [Set.mem_ofPred_eq, onR, gauss_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact exp_bound_on_Ioo ht
  · refine ⟨fun x => ⟨Set.Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩⟩
    have hm : 0 < Real.exp (-Real.pi * (|x| + 1) ^ 2) := Real.exp_pos _
    refine lt_of_le_of_lt (measure_mono ?_) (hνint.measure_norm_ge_lt_top hm)
    intro t ht
    simp only [Set.mem_ofPred_eq, FT_gauss, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact exp_bound_on_Ioo ht

/-! ## Linearity of the transform -/

theorem FT_add_of_integrable {F G : ℂ → ℂ} (hF : Integrable (onR F)) (hG : Integrable (onR G))
    (ξ : ℝ) : FT (fun z => F z + G z) ξ = FT F ξ + FT G ξ := by
  have h := VectorFourier.fourierIntegral_add Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hF hG
  exact congrFun h ξ

theorem FT_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, Integrable (onR (f i))) (ξ : ℝ) :
    FT (fun z => ∑ i ∈ s, f i z) ξ = ∑ i ∈ s, FT (f i) ξ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold FT onR
    simp [Real.fourier_real_eq]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hs : ∀ i ∈ s, Integrable (onR (f i)) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum : Integrable (onR (fun z => ∑ i ∈ s, f i z)) := by
      have : onR (fun z => ∑ i ∈ s, f i z) = fun t => ∑ i ∈ s, onR (f i) t := rfl
      rw [this]
      exact integrable_finsetSum s hs
    have := FT_add_of_integrable (F := f a) (G := fun z => ∑ i ∈ s, f i z)
      (hf a (Finset.mem_insert_self a s)) hsum ξ
    simp only [Finset.sum_insert ha]
    rw [this, ih hs]

end PosRig
