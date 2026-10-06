/-
Faithfulness checks (Mathlib only, plus `Sanity.lean` and `Zeta.lean`): the Lean definitions of
`Basic.lean` say what the paper says.

* `TestClass.pole_real`, `TestClass.Arch_eq_paper`: for `F ∈ 𝒯` the Lean `𝒜(F)` (a real part) is the
  paper's complex expression `F(i/2) + F(−i/2) + ∫ F Ω_∞` (§2.1); the pole term is real by Schwarz
  reflection.
* `OmegaG_zeta`, `ArchG_zeta`: `Ω_{Γ_ℝ} = Ω_∞` and `𝒜_{Γ_ℝ,q} = 𝒜_q` (§5.5).
* `Gset_subset_TestClass`: `𝒢 ⊂ 𝒯_δ` for every `δ` (Definition 2.1).
* `RH_iff_critical`: Mathlib's `RiemannHypothesis` is "every non-trivial zero is on the critical line",
  with non-trivial zeros = zeros in `0 < Re s < 1` (`NontrivialZeros`).
-/
import PositivityRigidity.Sanity
import PositivityRigidity.Zeta

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder

namespace PosRig

/-! ## Schwarz reflection and the pole term -/

/-- If `F` is analytic at `conj z`, then `w ↦ conj (F (conj w))` is analytic at `z`. -/
theorem analyticAt_conj_comp_conj {F : ℂ → ℂ} {z : ℂ}
    (h : AnalyticAt ℂ F ((starRingEnd ℂ) z)) :
    AnalyticAt ℂ (fun w => (starRingEnd ℂ) (F ((starRingEnd ℂ) w))) z := by
  have hev : ∀ᶠ y in 𝓝 ((starRingEnd ℂ) z), DifferentiableAt ℂ F y :=
    h.eventually_analyticAt.mono fun y hy => hy.differentiableAt
  have hcont : Tendsto (starRingEnd ℂ) (𝓝 z) (𝓝 ((starRingEnd ℂ) z)) :=
    Complex.continuous_conj.tendsto z
  have hs : {w : ℂ | DifferentiableAt ℂ F ((starRingEnd ℂ) w)} ∈ 𝓝 z := hcont.eventually hev
  refine DifferentiableOn.analyticAt (s := {w : ℂ | DifferentiableAt ℂ F ((starRingEnd ℂ) w)})
    ?_ hs
  intro w hw
  have h1 := DifferentiableAt.conj_conj (hw : DifferentiableAt ℂ F ((starRingEnd ℂ) w))
  rw [Complex.conj_conj] at h1
  exact h1.differentiableWithinAt

theorem conj_mem_closedStrip {b : ℝ} {z : ℂ} (hz : z ∈ closedStrip b) :
    (starRingEnd ℂ) z ∈ closedStrip b := by
  simpa [closedStrip] using hz

/-- Schwarz reflection on the strip: for `F ∈ 𝒯_δ`, `F(z̄) = conj F(z)` on `|Im z| ≤ 1/2 + δ`. -/
theorem InTδ.conj_symm {δ : ℝ} {F : ℂ → ℂ} (h : InTδ δ F) {z : ℂ}
    (hz : z ∈ closedStrip (1 / 2 + δ)) :
    F z = (starRingEnd ℂ) (F ((starRingEnd ℂ) z)) := by
  have hG : AnalyticOnNhd ℂ (fun w => (starRingEnd ℂ) (F ((starRingEnd ℂ) w)))
      (closedStrip (1 / 2 + δ)) :=
    fun w hw => analyticAt_conj_comp_conj (h.analytic _ (conj_mem_closedStrip hw))
  have h0 : (0 : ℂ) ∈ closedStrip (1 / 2 + δ) := by
    simpa using ofReal_mem_closedStrip h.pos 0
  have hR : ∀ t : ℝ, F t = (starRingEnd ℂ) (F ((starRingEnd ℂ) (t : ℂ))) := by
    intro t
    rw [Complex.conj_ofReal]
    exact (Complex.conj_eq_iff_im.mpr (h.real t)).symm
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), F w = (starRingEnd ℂ) (F ((starRingEnd ℂ) w)) := by
    have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have := Complex.continuous_ofReal.tendsto (0 : ℝ)
        simpa using this.mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun t ht => by simpa using ht
    exact ht.frequently (Eventually.frequently (Eventually.of_forall fun t => hR t))
  exact h.analytic.eqOn_of_preconnected_of_frequently_eq hG (isPreconnected_closedStrip _) h0
    hfreq hz

/-- **Definition of `𝒜` (§2.1): the pole term is real.**  For `F ∈ 𝒯`, `F(i/2) + F(−i/2)` is real
(Schwarz reflection: `F(−i/2) = conj F(i/2)`), so taking its real part in `Arch` changes nothing. -/
theorem TestClass.pole_real {F : ℂ → ℂ} (hF : F ∈ TestClass) : (F (I / 2) + F (-I / 2)).im = 0 := by
  obtain ⟨δ, h⟩ := hF
  have hI : I / 2 ∈ closedStrip (1 / 2 + δ) := by
    show |(I / 2).im| ≤ 1 / 2 + δ
    have : (I / 2).im = 1 / 2 := by simp
    rw [this, abs_of_pos (by norm_num)]
    linarith [h.pos]
  have hs := h.conj_symm hI
  have hc : (starRingEnd ℂ) (I / 2) = -I / 2 := by
    rw [map_div₀, Complex.conj_I, map_ofNat]
  rw [hc] at hs
  have hm : F (-I / 2) = (starRingEnd ℂ) (F (I / 2)) := by
    rw [hs, Complex.conj_conj]
  rw [hm, Complex.add_conj, Complex.ofReal_im]

/-- **Definition of `𝒜` (§2.1).**  For `F ∈ 𝒯`, the Lean value `Arch F` is the paper's
`𝒜(F) = F(i/2) + F(−i/2) + ∫_ℝ F(t) Ω_∞(t) dt` (a real number). -/
theorem TestClass.Arch_eq_paper {F : ℂ → ℂ} (hF : F ∈ TestClass) :
    ((Arch F : ℝ) : ℂ) = F (I / 2) + F (-I / 2) + ∫ t : ℝ, F t * (Ωinf t : ℂ) := by
  unfold Arch
  have h1 : (((F (I / 2) + F (-I / 2)).re : ℝ) : ℂ) = F (I / 2) + F (-I / 2) :=
    Complex.ext (by simp) (by simp [TestClass.pole_real hF])
  have h2 : ∫ t : ℝ, F t * (Ωinf t : ℂ) = ((∫ t : ℝ, (F t).re * Ωinf t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext t
    have : F t = (((F t).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [TestClass.real hF t])
    rw [this]
    push_cast
    simp
  rw [Complex.ofReal_add, h1, h2]

/-! ## The Gamma factor `Γ_ℝ` (§5.5) -/

/-- **§5.5:** `Ω_{Γ_ℝ} = Ω_∞`. -/
theorem OmegaG_zeta (t : ℝ) : OmegaG [0] t = Ωinf t := by
  unfold OmegaG Ωinf
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Nat.cast_zero]
  rw [show (1 / 2 + I * (t : ℂ)) / 2 = 1 / 4 + I * (t : ℂ) / 2 by ring]

/-- **§5.5:** `𝒜_{Γ_ℝ,q} = 𝒜_q`. -/
theorem ArchG_zeta (q : ℝ) (F : ℂ → ℂ) : ArchG [0] q F = Arch_q q F := by
  have h : OmegaG [0] = Ωinf := funext OmegaG_zeta
  unfold ArchG Arch_q ArchShift Arch
  rw [h]

/-! ## The critical line -/

/-- **RH (§1.6).**  Mathlib's `RiemannHypothesis` (every zero of `ζ` other than the trivial zeros
`−2, −4, …` and the pole `s = 1` has real part `1/2`) is the paper's "every non-trivial zero (zero with
`0 < Re ρ < 1`) is on the critical line". -/
theorem RH_iff_critical : RiemannHypothesis ↔ ∀ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 := by
  constructor
  · intro hRH ρ hρ
    exact re_eq_half_of_RH hRH hρ
  · intro h s hs htriv hs1
    apply h s
    refine ⟨hs, ?_, ?_⟩
    · -- `0 < Re s`, by the functional equation
      by_contra hle
      push Not at hle
      have hs0 : s ≠ 0 := by
        rintro rfl
        rw [riemannZeta_zero] at hs
        norm_num at hs
      set s' : ℂ := 1 - s with hs'
      have hre' : 1 ≤ s'.re := by
        simp only [hs', Complex.sub_re, Complex.one_re]
        linarith
      have hn : ∀ n : ℕ, s' ≠ -n := by
        intro n hn
        have := congrArg Complex.re hn
        simp only [Complex.neg_re, Complex.natCast_re] at this
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      have hs'1 : s' ≠ 1 := by
        intro h'
        apply hs0
        have : s = 1 - s' := by rw [hs']; ring
        rw [this, h', sub_self]
      have hfe := riemannZeta_one_sub hn hs'1
      have hss : 1 - s' = s := by rw [hs']; ring
      rw [hss, hs] at hfe
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have h3 : (2 * (Real.pi : ℂ)) ^ (-s') ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero two_ne_zero hπ))
      have h4 : Complex.Gamma s' ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
      have h5 : riemannZeta s' ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre'
      have h6 : Complex.cos ((Real.pi : ℂ) * s' / 2) ≠ 0 := by
        intro hc
        obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hc
        have hsk : s' = 2 * k + 1 := by
          have h2 : (Real.pi : ℂ) * s' = (Real.pi : ℂ) * (2 * k + 1) := by
            linear_combination 2 * hk
          exact mul_left_cancel₀ hπ h2
        have hsk' : s = -(2 * (k : ℂ)) := by
          have : s = 1 - s' := by rw [hs']; ring
          rw [this, hsk]; ring
        have hkre : (s.re) = -(2 * (k : ℝ)) := by
          rw [hsk']; simp
        have hk0 : 0 ≤ k := by
          have : -(2 * (k : ℝ)) ≤ 0 := by rw [← hkre]; exact hle
          have : (0 : ℝ) ≤ k := by linarith
          exact_mod_cast this
        obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm
          apply hs0
          rw [hsk']
          simp
        · apply htriv
          refine ⟨m - 1, ?_⟩
          rw [hsk']
          have : ((m - 1 : ℕ) : ℂ) + 1 = (m : ℂ) := by
            rw [Nat.cast_sub (by omega)]; push_cast; ring
          rw [this]
          push_cast
          ring
      have hprod : (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-s') * Complex.Gamma s' *
          Complex.cos ((Real.pi : ℂ) * s' / 2) * riemannZeta s' ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h3) h4) h6) h5
      exact hprod hfe.symm
    · -- `Re s < 1`
      by_contra hge
      push Not at hge
      exact riemannZeta_ne_zero_of_one_le_re hge hs

/-! ## Gaussian wave packets lie in the test class (Definition 2.1) -/

/-- Entire, with `(1 + |z|)² |f(z)|` bounded on every horizontal strip. -/
def StripDecay (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∀ b : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.im| ≤ b → (1 + ‖z‖) ^ 2 * ‖f z‖ ≤ C

theorem StripDecay.zero : StripDecay 0 :=
  ⟨differentiable_const 0, fun _ => ⟨0, fun z _ => by simp⟩⟩

theorem StripDecay.add {f g : ℂ → ℂ} (hf : StripDecay f) (hg : StripDecay g) :
    StripDecay (f + g) := by
  refine ⟨hf.1.add hg.1, fun b => ?_⟩
  obtain ⟨C₁, h₁⟩ := hf.2 b
  obtain ⟨C₂, h₂⟩ := hg.2 b
  refine ⟨C₁ + C₂, fun z hz => ?_⟩
  have hn : ‖(f + g) z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le (f z) (g z)
  calc (1 + ‖z‖) ^ 2 * ‖(f + g) z‖ ≤ (1 + ‖z‖) ^ 2 * (‖f z‖ + ‖g z‖) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (1 + ‖z‖) ^ 2 * ‖f z‖ + (1 + ‖z‖) ^ 2 * ‖g z‖ := by ring
    _ ≤ C₁ + C₂ := add_le_add (h₁ z hz) (h₂ z hz)

theorem StripDecay.smul {f : ℂ → ℂ} (hf : StripDecay f) (c : ℂ) : StripDecay (c • f) := by
  refine ⟨hf.1.const_smul c, fun b => ?_⟩
  obtain ⟨C, h⟩ := hf.2 b
  refine ⟨‖c‖ * C, fun z hz => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  calc (1 + ‖z‖) ^ 2 * (‖c‖ * ‖f z‖) = ‖c‖ * ((1 + ‖z‖) ^ 2 * ‖f z‖) := by ring
    _ ≤ ‖c‖ * C := mul_le_mul_of_nonneg_left (h z hz) (norm_nonneg c)

theorem norm_gwp (a b s : ℝ) (z : ℂ) :
    ‖gwp a b s z‖ =
      Real.exp (-(Real.pi / s ^ 2) * ((z.re - a) ^ 2 - z.im ^ 2) - 2 * Real.pi * b * z.im) := by
  unfold gwp
  rw [Complex.norm_exp]
  congr 1
  have h : -(Real.pi : ℂ) * (z - a) ^ 2 / (s : ℂ) ^ 2 + 2 * Real.pi * I * b * z =
      ((-(Real.pi / s ^ 2) : ℝ) : ℂ) * ((z - a) * (z - a)) + ((2 * Real.pi * b : ℝ) : ℂ) * (I * z) := by
    push_cast; ring
  rw [h, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.I_mul_re,
    Complex.mul_re]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  ring

theorem sq_mul_exp_neg_le {c : ℝ} (hc : 0 < c) (u : ℝ) :
    u ^ 2 * Real.exp (-c * u ^ 2) ≤ 1 / c := by
  have h1 : c * u ^ 2 + 1 ≤ Real.exp (c * u ^ 2) := by
    linarith [Real.add_one_le_exp (c * u ^ 2)]
  have hexp : Real.exp (-c * u ^ 2) = (Real.exp (c * u ^ 2))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [hexp, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hc]
  nlinarith [sq_nonneg u]

theorem stripDecay_gwp (a b s : ℝ) (hs : 0 < s) : StripDecay (gwp a b s) := by
  refine ⟨?_, fun B => ?_⟩
  · unfold gwp; fun_prop
  · set c : ℝ := Real.pi / s ^ 2 with hc
    have hc0 : 0 < c := by rw [hc]; have := Real.pi_pos; positivity
    set B' : ℝ := max B 0 with hB'
    have hB'0 : 0 ≤ B' := le_max_right _ _
    set K : ℝ := 1 + |a| + B' with hK
    have hK0 : 0 ≤ K := by rw [hK]; positivity
    set E : ℝ := Real.exp (c * B' ^ 2 + 2 * Real.pi * |b| * B') with hE
    refine ⟨(2 * K ^ 2 + 2 * (1 / c)) * E, fun z hz => ?_⟩
    rw [norm_gwp]
    have hy : |z.im| ≤ B' := le_trans hz (le_max_left _ _)
    have hy2 : z.im ^ 2 ≤ B' ^ 2 := by
      have := sq_abs z.im
      nlinarith [abs_nonneg z.im]
    have hb : |2 * Real.pi * b * z.im| ≤ 2 * Real.pi * |b| * B' := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos Real.pi_pos]
      have := Real.pi_pos
      gcongr
    have hexp : -(Real.pi / s ^ 2) * ((z.re - a) ^ 2 - z.im ^ 2) - 2 * Real.pi * b * z.im
        ≤ -c * (z.re - a) ^ 2 + (c * B' ^ 2 + 2 * Real.pi * |b| * B') := by
      have h1 : -(2 * Real.pi * b * z.im) ≤ 2 * Real.pi * |b| * B' :=
        le_trans (neg_le_abs _) hb
      have h2 : c * z.im ^ 2 ≤ c * B' ^ 2 := mul_le_mul_of_nonneg_left hy2 hc0.le
      rw [← hc]
      nlinarith
    have hnorm : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    have hre : |z.re| ≤ |a| + |z.re - a| := by
      calc |z.re| = |a + (z.re - a)| := by ring_nf
        _ ≤ |a| + |z.re - a| := abs_add_le _ _
    have h1 : 1 + ‖z‖ ≤ K + |z.re - a| := by rw [hK]; linarith
    have h2 : (1 + ‖z‖) ^ 2 ≤ 2 * K ^ 2 + 2 * (z.re - a) ^ 2 := by
      have hsq := sq_abs (z.re - a)
      have h0 : 0 ≤ 1 + ‖z‖ := by positivity
      nlinarith [sq_nonneg (K - |z.re - a|), abs_nonneg (z.re - a)]
    have hE0 : 0 < E := Real.exp_pos _
    have hx1 : Real.exp (-c * (z.re - a) ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := sq_nonneg (z.re - a)
      nlinarith
    have hx2 := sq_mul_exp_neg_le hc0 (z.re - a)
    calc (1 + ‖z‖) ^ 2 *
          Real.exp (-(Real.pi / s ^ 2) * ((z.re - a) ^ 2 - z.im ^ 2) - 2 * Real.pi * b * z.im)
        ≤ (2 * K ^ 2 + 2 * (z.re - a) ^ 2) *
          Real.exp (-c * (z.re - a) ^ 2 + (c * B' ^ 2 + 2 * Real.pi * |b| * B')) := by
          apply mul_le_mul h2 (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
      _ = (2 * K ^ 2 * Real.exp (-c * (z.re - a) ^ 2) +
            2 * ((z.re - a) ^ 2 * Real.exp (-c * (z.re - a) ^ 2))) * E := by
          rw [hE, Real.exp_add]; ring
      _ ≤ (2 * K ^ 2 * 1 + 2 * (1 / c)) * E := by
          apply mul_le_mul_of_nonneg_right _ hE0.le
          have : 0 ≤ 2 * K ^ 2 := by positivity
          nlinarith
      _ = (2 * K ^ 2 + 2 * (1 / c)) * E := by ring

theorem stripDecay_of_mem_gwpSpan {F : ℂ → ℂ} (hF : F ∈ gwpSpan) : StripDecay F := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, s, hs, rfl⟩ := hx
    exact stripDecay_gwp a b s hs
  | zero => exact StripDecay.zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

/-- **Definition 2.1: `𝒢 ⊂ 𝒯_δ` for every `δ ∈ (0, 1/2)`.** -/
theorem Gset_inTδ {F : ℂ → ℂ} (hF : F ∈ Gset) {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) :
    InTδ δ F := by
  obtain ⟨hspan, heven, hreal⟩ := hF
  obtain ⟨hdiff, hbd⟩ := stripDecay_of_mem_gwpSpan hspan
  refine ⟨h0, h1, ?_, hreal, fun z _ => hdiff.analyticAt z, ?_⟩
  · have hG : AnalyticOnNhd ℂ (fun z => F (-z)) Set.univ := fun z _ =>
      (hdiff.comp differentiable_neg).analyticAt z
    have hF' : AnalyticOnNhd ℂ F Set.univ := fun z _ => hdiff.analyticAt z
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), F (-z) = F z := by
      have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have := Complex.continuous_ofReal.tendsto (0 : ℝ)
          simpa using this.mono_left nhdsWithin_le_nhds
        · exact eventually_nhdsWithin_of_forall fun t ht => by simpa using ht
      exact ht.frequently (Eventually.frequently (Eventually.of_forall fun t => heven t))
    have hEq := hG.eqOn_of_preconnected_of_frequently_eq hF' isPreconnected_univ
      (Set.mem_univ 0) hfreq
    exact fun z _ => hEq (Set.mem_univ z)
  · obtain ⟨C, hC⟩ := hbd (1 / 2 + δ)
    exact ⟨C, fun z hz => hC z hz⟩

/-- **Definition 2.1: `𝒢 ⊂ 𝒯`.** -/
theorem Gset_subset_TestClass : Gset ⊆ TestClass :=
  fun _ hF => ⟨1 / 4, Gset_inTδ hF (by norm_num) (by norm_num)⟩

end PosRig
