/-
§4.3: Theorem 4.8 (Theorem D) with the strict (Mg) of v1.0 (`HypMg`), from its analytic inputs: Lemma 4.7
(ledger axiom `robust_compactness`), the equivalent form of (Z_∞) (ledger axiom `Zinf_lower_bound`), the
interpolation property of the exact family (Proposition 4.5, proved in `Family.lean`), Corollary 3.9(b),
Theorem 2.9 and Theorem 2.7.  The v1.1 form, with the non-strict (Mg), is in `CriterionWeak.lean`.
-/
import PositivityRigidity.Family
import PositivityRigidity.Uniqueness

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

theorem Hfam_even (J : ℕ) (z : ℂ) : Hfam J (-z) = Hfam J z := by
  simp [Hfam]

theorem Hfam_real (J : ℕ) (t : ℝ) : (Hfam J t).im = 0 := by
  rw [Hfam_ofReal]; exact Complex.ofReal_im _

theorem Hfam_zero (J : ℕ) : Hfam J 0 = 1 := by
  simp only [Hfam, Pfam]
  rw [Finset.sum_eq_single 0]
  · simp [pcoef]
  · intro k _ hk
    simp [hk]
  · simp

theorem differentiable_Hfam (J : ℕ) : Differentiable ℂ (Hfam J) := by
  unfold Hfam Pfam
  fun_prop

theorem eventually_mono_sub {I : Set ℕ} (hI : I ⊆ Jset) {P : ℕ → Prop}
    (h : ∀ᶠ J in atTop ⊓ 𝓟 Jset, P J) : ∀ᶠ J in atTop ⊓ 𝓟 I, P J :=
  h.filter_mono (inf_le_inf_left _ (principal_mono.mpr hI))

/-- Hypotheses (i)–(v) of Lemma 4.7 for the exact family along an infinite `I ⊆ 𝒥`, from a uniform
bound (i), a positive lower bound for `H_J` on `ℝ` (giving (iii)), and (Mg) (giving (iv) off `ξ_PP`);
(iv) at `ξ_PP` and (v) are the interpolation property (Proposition 4.5). -/
theorem robustHyp_of {I : Set ℕ} (hIJ : I ⊆ Jset) (hI : I.Infinite) {δ a C : ℝ} (hδ : 0 < δ)
    (ha : a < Real.pi / 2)
    (hbound : ∀ J ∈ I, ∀ z ∈ closedStrip (1 / 2 + δ), ‖Hfam J z‖ ≤ C * Real.exp (a * |z.re|))
    (hlow : ∀ t : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ J in atTop ⊓ 𝓟 I, c ≤ (Hfam J t).re)
    (hMg : HypMg) : RobustHyp I Hfam δ a C := by
  refine ⟨hI, hδ, ha, fun J _ => ⟨fun z _ => Hfam_even J z, Hfam_real J,
    (differentiable_Hfam J).differentiableOn.analyticOnNhd isOpen_univ |>.mono (Set.subset_univ _)⟩,
    hbound, fun J _ => Hfam_zero J, ?_, ?_, ?_⟩
  · -- (iii)
    intro t ε hε
    obtain ⟨c, hc, hev⟩ := hlow t
    filter_upwards [hev] with J hJ
    linarith
  · -- (iv)
    intro ξ hξ ε hε
    by_cases hpp : ξ ∈ xiPP
    · obtain ⟨n, hn, rfl⟩ := hpp
      filter_upwards [eventually_mono_sub hIJ (FT_Ffam_pp_eventually hn)] with J hJ
      have : FT (fun z => Xi z ^ 2 * Hfam J z) (xiOf n) = 0 := hJ
      rw [this, Complex.zero_re]
      linarith
    · obtain ⟨c, hc, hev⟩ := hMg ξ hξ hpp
      filter_upwards [eventually_mono_sub hIJ hev] with J hJ
      have : (FT (fun z => Xi z ^ 2 * Hfam J z) ξ).re = (FT (Ffam J) ξ).re := rfl
      linarith
  · -- (v)
    intro n hn
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_mono_sub hIJ (FT_Ffam_pp_eventually hn)] with J hJ
    exact hJ.symm

/-- The common core of Theorem 4.8 and Remark 4.10(a) with the strict (Mg) of v1.0: from the hypotheses
of Lemma 4.7 along an infinite `I ⊆ 𝒥`, a positive lower bound for `H_J` on `ℝ` and (Mg), the limit `F_∞ = Ξ² H_∞` is an exact
magic function with `Z(F_∞) = Z_ζ` and `Ẑ(F_∞) = ξ_PP`; hence (S), (U), `RH ⇔ (E)`, and under either,
`κ* = 0` and `𝒦 = {p_ζ}`. -/
theorem criterion_core {I : Set ℕ} (hIJ : I ⊆ Jset) {δ a C : ℝ} (hδ : 0 < δ)
    (hR : RobustHyp I Hfam δ a C)
    (hlow : ∀ t : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ J in atTop ⊓ 𝓟 I, c ≤ (Hfam J t).re)
    (hMg : HypMg) :
    (∃ Hinf : ℂ → ℂ,
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, φ k ∈ Jset) ∧
        TendstoLocallyUniformlyOn (fun k => Hfam (φ k)) Hinf atTop (openStrip (1 / 2 + δ)) ∧
        ∀ z ∈ openStrip (1 / 2 + δ), ‖Hinf z‖ ≤ C * Real.exp (a * |z.re|)) ∧
      (∀ t : ℝ, 0 < (Hinf t).re ∧ (Hinf t).im = 0) ∧
      (fun z => Xi z ^ 2 * Hinf z) ∈ Cone ∧
      Arch (fun z => Xi z ^ 2 * Hinf z) = 0 ∧
      ZF (fun z => Xi z ^ 2 * Hinf z) = Zzeta ∧
      ZhatF (fun z => Xi z ^ 2 * Hinf z) = xiPP) ∧
    CondS ∧ CondU ∧ (RiemannHypothesis ↔ CondE) ∧
    (RiemannHypothesis ∨ CondE → kappaStar = 0 ∧ K = {pZeta}) := by
  obtain ⟨φ, hφ, hφI, Hinf, hconv, hHb, hcone, hA0, hint, hFT⟩ :=
    robust_compactness I Hfam δ a C hR
  -- `φ` tends to `∞` inside `I`
  have hφt : Tendsto φ atTop (atTop ⊓ 𝓟 I) :=
    tendsto_inf.mpr ⟨hφ.tendsto_atTop, tendsto_principal.mpr (Eventually.of_forall hφI)⟩
  set Finf : ℂ → ℂ := fun z => Xi z ^ 2 * Hinf z with hFinf
  -- `H_∞ > 0` on `ℝ`
  have hpos : ∀ t : ℝ, 0 < (Hinf t).re ∧ (Hinf t).im = 0 := by
    intro t
    have ht : (t : ℂ) ∈ openStrip (1 / 2 + δ) := by
      simp only [openStrip, Set.mem_ofPred_eq, Complex.ofReal_im, abs_zero]; positivity
    have hlim := hconv.tendsto_at ht
    obtain ⟨c, hc, hev⟩ := hlow t
    have hev' : ∀ᶠ k in atTop, c ≤ (Hfam (φ k) t).re := hφt.eventually hev
    refine ⟨lt_of_lt_of_le hc (ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hlim)
      hev'), ?_⟩
    have him : Tendsto (fun k => (Hfam (φ k) t).im) atTop (𝓝 (Hinf t).im) :=
      Complex.continuous_im.continuousAt.tendsto.comp hlim
    have h0 : (fun k => (Hfam (φ k) t).im) = fun _ => 0 := funext fun k => Hfam_real _ t
    rw [h0] at him
    exact tendsto_nhds_unique him tendsto_const_nhds
  -- the real zeros of `F_∞` are those of `Ξ`
  have hZF : ZF Finf = Zzeta := by
    ext t
    simp only [ZF, Set.mem_ofPred_eq, hFinf]
    rw [← Xi_eq_zero_iff]
    have hne : Hinf t ≠ 0 := fun h => by
      have := (hpos t).1; rw [h, Complex.zero_re] at this; exact lt_irrefl _ this
    constructor
    · intro h; exact pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp h).resolve_right hne)
    · intro h; rw [h]; ring
  -- the zeros of `F̂_∞` on `[ξ₂, ∞)` are the prime-power nodes
  have hZhat : ZhatF Finf = xiPP := by
    ext ξ
    simp only [ZhatF, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hξ, h0⟩
      by_contra hpp
      obtain ⟨c, hc, hev⟩ := hMg ξ hξ hpp
      have hlim := hFT ξ
      have hev' : ∀ᶠ k in atTop, c ≤ (FT (fun z => Xi z ^ 2 * Hfam (φ k) z) ξ).re :=
        hφt.eventually (eventually_mono_sub hIJ hev)
      have := ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hlim) hev'
      have h0' : (FT Finf ξ).re = 0 := by rw [h0, Complex.zero_re]
      linarith
    · rintro ⟨n, hn, rfl⟩
      refine ⟨xiPP_subset_Ici ⟨n, hn, rfl⟩, ?_⟩
      have hlim := hFT (xiOf n)
      have hev : ∀ᶠ k in atTop, FT (fun z => Xi z ^ 2 * Hfam (φ k) z) (xiOf n) = 0 :=
        hφt.eventually (eventually_mono_sub hIJ (FT_Ffam_pp_eventually hn))
      exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun k hk => hk.symm))
  -- (S)
  have hS : CondS := by
    unfold CondS kappaStar
    have := slack_le homog_Arch (scalable_ConeG_Arch xi2) hcone hint
    rw [hA0, zero_div] at this
    exact_mod_cast this
  -- (U), and (E) ⇒ RH ∧ 𝒦 = {p_ζ}, by the magic-function principle
  have hfin : (ZF Finf \ Zzeta).Finite := by rw [hZF, Set.sdiff_self]; exact Set.finite_empty
  obtain ⟨hU, hEU⟩ := magic_function_principle hcone hA0 hfin (by rw [hZhat]; exact xiPP_subset_BRSNodes)
  have hRE : RiemannHypothesis ↔ CondE := ⟨fun h => (logic_a h).2, fun h => (hEU h).1⟩
  refine ⟨⟨Hinf, ⟨φ, hφ, fun k => hIJ (hφI k), hconv, hHb⟩, hpos, hcone, hA0, hZF, hZhat⟩,
    hS, hU, hRE, fun h => ?_⟩
  have hE : CondE := h.elim (fun h => hRE.mp h) id
  exact ⟨le_antisymm hS (kappaStar_nonneg_of_condE hE), (hEU hE).2⟩

/-- **Theorem 4.8 (Theorem D) with the strict (Mg) of v1.0.**  Assume (N), (G_a), (Z_∞) and the strict
(Mg) (`HypMg`) for the exact family.  Then some
subsequential limit `F_∞ = Ξ² H_∞`, with `H_∞ ∈ ℋ` and `H_∞ > 0` on `ℝ`, satisfies `F_∞ ∈ 𝒞 ∩ 𝒯`,
`𝒜(F_∞) = 0`, `F_∞⁻¹(0) ∩ ℝ = Z_ζ` and `F̂_∞⁻¹(0) ∩ [ξ₂, ∞) = ξ_PP`.  Hence (S) and (U) hold, and
`RH ⇔ (E)`; under either, `κ* = 0` and `𝒦 = {p_ζ}`. -/
theorem theoremD (hN : HypN) (hG : HypG) (hZ : HypZinf) (hMg : HypMg) :
    (∃ Hinf : ℂ → ℂ,
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, φ k ∈ Jset) ∧ ∃ δ : ℝ, 0 < δ ∧
        TendstoLocallyUniformlyOn (fun k => Hfam (φ k)) Hinf atTop (openStrip (1 / 2 + δ)) ∧
        ∃ a C : ℝ, a < Real.pi / 2 ∧
          ∀ z ∈ openStrip (1 / 2 + δ), ‖Hinf z‖ ≤ C * Real.exp (a * |z.re|)) ∧
      (∀ t : ℝ, 0 < (Hinf t).re ∧ (Hinf t).im = 0) ∧
      (fun z => Xi z ^ 2 * Hinf z) ∈ Cone ∧
      Arch (fun z => Xi z ^ 2 * Hinf z) = 0 ∧
      ZF (fun z => Xi z ^ 2 * Hinf z) = Zzeta ∧
      ZhatF (fun z => Xi z ^ 2 * Hinf z) = xiPP) ∧
    CondS ∧ CondU ∧ (RiemannHypothesis ↔ CondE) ∧
    (RiemannHypothesis ∨ CondE → kappaStar = 0 ∧ K = {pZeta}) := by
  have hlow := Zinf_lower_bound hN hG hZ
  obtain ⟨δ, a, C, hδ, -, ha, hbound⟩ := hG
  have hlow' : ∀ t : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ J in atTop ⊓ 𝓟 Jset, c ≤ (Hfam J t).re := by
    intro t
    obtain ⟨c, hc, hev⟩ := hlow (|t| + 1) (by positivity)
    exact ⟨c, hc, hev.mono fun J hJ => hJ t (by linarith)⟩
  have hR := robustHyp_of subset_rfl hN hδ ha hbound hlow' hMg
  obtain ⟨⟨Hinf, ⟨φ, hφ, hφI, hconv, hHb⟩, hrest⟩, hconcl⟩ :=
    criterion_core subset_rfl hδ hR hlow' hMg
  exact ⟨⟨Hinf, ⟨φ, hφ, hφI, δ, hδ, hconv, a, C, ha, hHb⟩, hrest⟩, hconcl⟩

/-- (POS_a) for all large `J ∈ 𝒥`: `0 ≤ p_k^{(J)} ≤ C a^{2k}/(2k)!` with `0 ≤ a < π/2` and `C`
independent of `J` (formula (4.3)). -/
def HypPOS : Prop :=
  ∃ J₀ : ℕ, ∃ C a : ℝ, 0 ≤ a ∧ a < Real.pi / 2 ∧
    ∀ J ∈ Jset, J₀ ≤ J → ∀ k ≤ 2 * J,
      0 ≤ pcoef J k ∧ pcoef J k ≤ C * a ^ (2 * k) / ((2 * k).factorial : ℝ)

/-- **Remark 4.10(a) with the strict (Mg) of v1.0** (v1.1 form: `remark_4_10a_nonstrict`).  (N), (Mg) and
the coefficient bound (4.3) for all large `J` imply (S) and (U)
(and `RH ⇔ (E)`): by Proposition 4.9, `H_J ≥ 1` on `ℝ` replaces (Z_∞), and `|H_J(t)| ≤ C cosh(a|t|)`
gives (G_a) on every strip. -/
theorem remark_4_10a (hN : HypN) (hPOS : HypPOS) (hMg : HypMg) :
    CondS ∧ CondU ∧ (RiemannHypothesis ↔ CondE) ∧
    (RiemannHypothesis ∨ CondE → kappaStar = 0 ∧ K = {pZeta}) := by
  obtain ⟨J₀, C, a, ha0, ha, hP⟩ := hPOS
  set I : Set ℕ := {J | J ∈ Jset ∧ J₀ ≤ J} with hIdef
  have hIJ : I ⊆ Jset := fun J hJ => hJ.1
  have hI : I.Infinite := by
    have : I = Jset \ {J | J < J₀} := by
      ext J; simp [hIdef, not_lt]
    rw [this]
    exact hN.sdiff (Set.finite_lt_nat J₀)
  have hcons : ∀ J ∈ I, (∀ t : ℝ, 1 ≤ (Hfam J t).re ∧ (Hfam J t).im = 0) ∧
      ∀ z : ℂ, ‖Hfam J z‖ ≤ C * Real.cosh (a * ‖z‖) := fun J hJ =>
    coeff_bound_consequences (fun k hk => (hP J hJ.1 hJ.2 k hk).1)
      (fun k hk => (hP J hJ.1 hJ.2 k hk).2)
  have hC : 0 ≤ C := by
    obtain ⟨J, hJ⟩ := hI.nonempty
    have := hP J hJ.1 hJ.2 0 (by omega)
    simp [pcoef] at this
    linarith
  set δ : ℝ := 1 / 4
  have hbound : ∀ J ∈ I, ∀ z ∈ closedStrip (1 / 2 + δ),
      ‖Hfam J z‖ ≤ C * Real.exp (a * (3 / 4)) * Real.exp (a * |z.re|) := by
    intro J hJ z hz
    have h1 := (hcons J hJ).2 z
    have hz' : |z.im| ≤ 3 / 4 := by
      have : |z.im| ≤ 1 / 2 + δ := hz
      simp only [δ] at this; linarith
    have hnorm : ‖z‖ ≤ |z.re| + 3 / 4 := (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
    have hcosh : Real.cosh (a * ‖z‖) ≤ Real.exp (a * ‖z‖) := by
      rw [Real.cosh_eq]
      have := Real.exp_pos (a * ‖z‖)
      have : Real.exp (-(a * ‖z‖)) ≤ Real.exp (a * ‖z‖) := by
        apply Real.exp_le_exp.mpr
        have : 0 ≤ a * ‖z‖ := mul_nonneg ha0 (norm_nonneg _)
        linarith
      linarith
    have hexp : Real.exp (a * ‖z‖) ≤ Real.exp (a * (3 / 4)) * Real.exp (a * |z.re|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    calc ‖Hfam J z‖ ≤ C * Real.cosh (a * ‖z‖) := h1
      _ ≤ C * (Real.exp (a * (3 / 4)) * Real.exp (a * |z.re|)) := by
          gcongr; exact hcosh.trans hexp
      _ = C * Real.exp (a * (3 / 4)) * Real.exp (a * |z.re|) := by ring
  have hlow : ∀ t : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ J in atTop ⊓ 𝓟 I, c ≤ (Hfam J t).re := by
    intro t
    refine ⟨1, one_pos, ?_⟩
    filter_upwards [(eventually_principal.mpr fun J hJ => hJ).filter_mono inf_le_right] with J hJ
    exact ((hcons J hJ).1 t).1
  have hR := robustHyp_of hIJ hI (by norm_num : (0 : ℝ) < 1 / 4) ha hbound hlow hMg
  exact (criterion_core hIJ (by norm_num) hR hlow hMg).2

end PosRig
