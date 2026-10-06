/-
v1.1: Theorem 4.8 (Theorem D) with the non-strict hypothesis (Mg) of v1.1,
`liminf_{J ∈ 𝒥} F̂_J(ξ) ≥ 0` for every `ξ ≥ ξ₂` (`HypMg0`), keeping (N), (G_a), (Z_∞); Remark 4.10(a)
and (b) in their v1.1 form; Conjecture 6.1 with its non-strict part (c) (`ConjFamily0`), and its
implication.

The strict (Mg) of v1.0 (`HypMg`, used by `theoremD`, `theoremD'`, `remark_4_10a`, `ConjFamily`) was used
only to locate `Ẑ(F_∞)` in `ℳ` for Corollary 3.9(b); here (U) comes from the real zero set
`Z(F_∞) = Z_ζ` and Theorem 3.6, through Corollary 3.9(a) (`magic_principle_zero`).  Nothing is claimed
about `Ẑ(F_∞)`.  The weakening is due to Astra (OpenAI), contributed during an independent review of
an earlier version of the paper, and independently verified (Paper I, the paragraph after Theorem 4.8).
-/
import PositivityRigidity.Criterion
import PositivityRigidity.Criticality
import PositivityRigidity.Conjectures
import PositivityRigidity.ZeroSupport

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

/-- (Mg) of v1.1 (§4.3; non-strict): `liminf_{J ∈ 𝒥} F̂_J(ξ) ≥ 0` for every `ξ ≥ ξ₂`; written without
`liminf`: for every `ε > 0`, eventually (along `J ∈ 𝒥`) `F̂_J(ξ) ≥ −ε`.  `F̂_J` is real-valued.  (The
strict (Mg) of v1.0 is `HypMg`; it implies this one, `hypMg0_of_hypMg`.) -/
def HypMg0 : Prop :=
  ∀ ξ : ℝ, xi2 ≤ ξ → ∀ ε : ℝ, 0 < ε → ∀ᶠ J in atTop ⊓ 𝓟 Jset, -ε ≤ (FT (Ffam J) ξ).re

/-- The strict (Mg) of v1.0 implies the non-strict (Mg) of v1.1: at the prime-power nodes `F̂_J(ξ_n) = 0`
eventually (Proposition 4.5). -/
theorem hypMg0_of_hypMg (h : HypMg) : HypMg0 := by
  intro ξ hξ ε hε
  by_cases hpp : ξ ∈ xiPP
  · obtain ⟨n, hn, rfl⟩ := hpp
    filter_upwards [FT_Ffam_pp_eventually hn] with J hJ
    have : FT (Ffam J) (xiOf n) = 0 := hJ
    rw [this, Complex.zero_re]
    linarith
  · obtain ⟨c, hc, hev⟩ := h ξ hξ hpp
    filter_upwards [hev] with J hJ
    linarith

/-- Hypotheses (i)–(v) of Lemma 4.7 for the exact family along an infinite `I ⊆ 𝒥`, from a uniform
bound (i), a positive lower bound for `H_J` on `ℝ` (giving (iii)) and (Mg) (which is (iv)); (v) is the
interpolation property (Proposition 4.5). -/
theorem robustHyp_of_weak {I : Set ℕ} (hIJ : I ⊆ Jset) (hI : I.Infinite) {δ a C : ℝ} (hδ : 0 < δ)
    (ha : a < Real.pi / 2)
    (hbound : ∀ J ∈ I, ∀ z ∈ closedStrip (1 / 2 + δ), ‖Hfam J z‖ ≤ C * Real.exp (a * |z.re|))
    (hlow : ∀ t : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ J in atTop ⊓ 𝓟 I, c ≤ (Hfam J t).re)
    (hMg0 : HypMg0) : RobustHyp I Hfam δ a C := by
  refine ⟨hI, hδ, ha, fun J _ => ⟨fun z _ => Hfam_even J z, Hfam_real J,
    (differentiable_Hfam J).differentiableOn.analyticOnNhd isOpen_univ |>.mono (Set.subset_univ _)⟩,
    hbound, fun J _ => Hfam_zero J, ?_, ?_, ?_⟩
  · -- (iii)
    intro t ε hε
    obtain ⟨c, hc, hev⟩ := hlow t
    filter_upwards [hev] with J hJ
    linarith
  · -- (iv) is (Mg)
    intro ξ hξ ε hε
    filter_upwards [eventually_mono_sub hIJ (hMg0 ξ hξ ε hε)] with J hJ
    exact hJ
  · -- (v)
    intro n hn
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_mono_sub hIJ (FT_Ffam_pp_eventually hn)] with J hJ
    exact hJ.symm

/-- The common core of Theorem 4.8 and Remark 4.10(a) (v1.1): from the hypotheses of Lemma 4.7 along
an infinite `I ⊆ 𝒥` and a positive lower bound for `H_J` on `ℝ`, the limit `F_∞ = Ξ² H_∞` lies in `𝒞`, has
`𝒜(F_∞) = 0` and `Z(F_∞) = Z_ζ`; hence (S), (U), `RH ⇔ (E)`, and under either, `κ* = 0` and
`𝒦 = {p_ζ}`. -/
theorem criterion_core_weak {I : Set ℕ} (hIJ : I ⊆ Jset) {δ a C : ℝ} (hδ : 0 < δ)
    (hR : RobustHyp I Hfam δ a C)
    (hlow : ∀ t : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ J in atTop ⊓ 𝓟 I, c ≤ (Hfam J t).re) :
    (∃ Hinf : ℂ → ℂ,
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, φ k ∈ Jset) ∧
        TendstoLocallyUniformlyOn (fun k => Hfam (φ k)) Hinf atTop (openStrip (1 / 2 + δ)) ∧
        ∀ z ∈ openStrip (1 / 2 + δ), ‖Hinf z‖ ≤ C * Real.exp (a * |z.re|)) ∧
      (∀ t : ℝ, 0 < (Hinf t).re ∧ (Hinf t).im = 0) ∧
      (fun z => Xi z ^ 2 * Hinf z) ∈ Cone ∧
      Arch (fun z => Xi z ^ 2 * Hinf z) = 0 ∧
      ZF (fun z => Xi z ^ 2 * Hinf z) = Zzeta) ∧
    CondS ∧ CondU ∧ (RiemannHypothesis ↔ CondE) ∧
    (RiemannHypothesis ∨ CondE → kappaStar = 0 ∧ K = {pZeta}) := by
  obtain ⟨φ, hφ, hφI, Hinf, hconv, hHb, hcone, hA0, hint, -⟩ :=
    robust_compactness I Hfam δ a C hR
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
  -- (S)
  have hS : CondS := by
    unfold CondS kappaStar
    have := slack_le homog_Arch (scalable_ConeG_Arch xi2) hcone hint
    rw [hA0, zero_div] at this
    exact_mod_cast this
  -- (U) and the rest, from the zero-side support theorem
  have hall : ∀ p ∈ K, CarriedBy p.μ (Zzeta ∪ {0}) := fun p hp =>
    measure_mono_null (Set.compl_subset_compl.mpr (by rw [hZF]; exact Set.subset_union_left))
      (comp_slackness hcone hA0 hp).1
  obtain ⟨hU, -, hRE, hfin⟩ := consequences_of_zero_support hall
  exact ⟨⟨Hinf, ⟨φ, hφ, fun k => hIJ (hφI k), hconv, hHb⟩, hpos, hcone, hA0, hZF⟩,
    hS, hU, hRE, hfin hS⟩

/-- **Theorem 4.8 (Theorem D), v1.1.**  Assume (N), (G_a), (Z_∞) and (Mg):
`liminf_{J ∈ 𝒥} F̂_J(ξ) ≥ 0` for every `ξ ≥ ξ₂`.  Then some subsequential limit
`F_∞ = Ξ² H_∞`, with `H_∞ > 0` on `ℝ`, satisfies `F_∞ ∈ 𝒞 ∩ 𝒯`, `𝒜(F_∞) = 0` and
`F_∞⁻¹(0) ∩ ℝ = Z_ζ`.  Hence (S) and (U) hold, and `RH ⇔ (E)`; under either, `κ* = 0` and
`𝒦 = {p_ζ}`. -/
theorem theoremD_nonstrict (hN : HypN) (hG : HypG) (hZ : HypZinf) (hMg0 : HypMg0) :
    (∃ Hinf : ℂ → ℂ,
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, φ k ∈ Jset) ∧ ∃ δ : ℝ, 0 < δ ∧
        TendstoLocallyUniformlyOn (fun k => Hfam (φ k)) Hinf atTop (openStrip (1 / 2 + δ)) ∧
        ∃ a C : ℝ, a < Real.pi / 2 ∧
          ∀ z ∈ openStrip (1 / 2 + δ), ‖Hinf z‖ ≤ C * Real.exp (a * |z.re|)) ∧
      (∀ t : ℝ, 0 < (Hinf t).re ∧ (Hinf t).im = 0) ∧
      (fun z => Xi z ^ 2 * Hinf z) ∈ Cone ∧
      Arch (fun z => Xi z ^ 2 * Hinf z) = 0 ∧
      ZF (fun z => Xi z ^ 2 * Hinf z) = Zzeta) ∧
    CondS ∧ CondU ∧ (RiemannHypothesis ↔ CondE) ∧
    (RiemannHypothesis ∨ CondE → kappaStar = 0 ∧ K = {pZeta}) := by
  have hlow := Zinf_lower_bound hN hG hZ
  obtain ⟨δ, a, C, hδ, -, ha, hbound⟩ := hG
  have hlow' : ∀ t : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ J in atTop ⊓ 𝓟 Jset, c ≤ (Hfam J t).re := by
    intro t
    obtain ⟨c, hc, hev⟩ := hlow (|t| + 1) (by positivity)
    exact ⟨c, hc, hev.mono fun J hJ => hJ t (by linarith)⟩
  have hR := robustHyp_of_weak subset_rfl hN hδ ha hbound hlow' hMg0
  obtain ⟨⟨Hinf, ⟨φ, hφ, hφI, hconv, hHb⟩, hrest⟩, hconcl⟩ :=
    criterion_core_weak subset_rfl hδ hR hlow'
  exact ⟨⟨Hinf, ⟨φ, hφ, hφI, δ, hδ, hconv, a, C, ha, hHb⟩, hrest⟩, hconcl⟩

/-- **Remark 4.10(a), v1.1.**  (N), (Mg) (non-strict) and the coefficient bound (4.3) for all large `J`
imply (S) and (U) (and `RH ⇔ (E)`; under either, `κ* = 0` and `𝒦 = {p_ζ}`). -/
theorem remark_4_10a_nonstrict (hN : HypN) (hPOS : HypPOS) (hMg0 : HypMg0) :
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
  have hR := robustHyp_of_weak hIJ hI (by norm_num : (0 : ℝ) < 1 / 4) ha hbound hlow hMg0
  exact (criterion_core_weak hIJ (by norm_num) hR hlow).2

/-- **Remark 4.10(b), last sentences (v1.1).**  If `κ* = 0` and some weak magic function `F*` has
`Z(F*) ⊆ Z_ζ ∪ {0}`, then RH holds and `𝒦 = {p_ζ}`, with no condition on `Ẑ(F*)`: every admissible pair is
carried by `Z(F*)` on the zero side (Theorem 2.12(c)), and Theorem 3.6 applies. -/
theorem remark_4_10b_zero (h0 : kappaStar = 0) {Fs : ℝ → ℝ} (hFs : IsWeakMagic Fs)
    (hZ : {t : ℝ | Fs t = 0} ⊆ Zzeta ∪ {0}) : RiemannHypothesis ∧ K = {pZeta} := by
  have hE : CondE := condE_iff_kappaStar_nonneg.mpr h0.symm.le
  exact (condU_of_zero_support fun p hp =>
    measure_mono_null (Set.compl_subset_compl.mpr hZ) (weakMagic_carries_mu hFs hp)).2 hE

/-! ## Conjecture 6.1, v1.1 -/

/-- **Conjecture 6.1 (prime-power magic function), v1.1.**  Parts (a), (b) as in `ConjFamily`; part (c) is
non-strict: `P_J → P_∞` coefficientwise, and `F_∞ := Ξ² P_∞(t²)` satisfies `F̂_∞(ξ) ≥ 0` for every
`ξ ≥ ξ₂`.  (The transcription notes of `ConjFamily` apply; `ConjFamily ⇒ ConjFamily0`,
`conjFamily0_of_conjFamily`.) -/
def ConjFamily0 : Prop :=
  (∀ J : ℕ, 1 ≤ J → J ∈ Jset) ∧
  ((∀ J : ℕ, 10 ≤ J → ∀ k ≤ 2 * J, 0 < pcoef J k) ∧
    ∃ a : ℝ, a < Real.pi / 2 ∧ ∀ J : ℕ, 10 ≤ J → ∀ k : ℕ, 1 ≤ k → k ≤ 2 * J →
      (((2 * k).factorial : ℝ) * pcoef J k) ^ ((1 : ℝ) / (2 * k)) ≤ a) ∧
  ∃ pinf : ℕ → ℝ, (∀ k, Tendsto (fun J => pcoef J k) atTop (𝓝 (pinf k))) ∧
    ∀ ξ : ℝ, xi2 ≤ ξ →
      0 ≤ (FT (fun z => Xi z ^ 2 * ∑' k, (pinf k : ℂ) * z ^ (2 * k)) ξ).re

/-- The v1.0 form of Conjecture 6.1 implies the v1.1 form (at `ξ_n`, `F̂_∞(ξ_n) = lim F̂_J(ξ_n) = 0`). -/
theorem conjFamily0_of_conjFamily (h : ConjFamily) : ConjFamily0 := by
  obtain ⟨ha, ⟨hpos, a, ha_lt, hbd⟩, pinf, hconv, hFpos⟩ := h
  refine ⟨ha, ⟨hpos, a, ha_lt, hbd⟩, pinf, hconv, fun ξ hξ => ?_⟩
  by_cases hpp : ξ ∈ xiPP
  · have hP := conjFamily_bound hpos hbd
    have ha0 : 0 ≤ max a 0 := le_max_right a 0
    have ha' : max a 0 < Real.pi / 2 := max_lt ha_lt (by have := Real.pi_pos; positivity)
    obtain ⟨n, hn, rfl⟩ := hpp
    have hlim := FT_Ffam_tendsto ha0 ha' hP hconv (xiOf n)
    have hev : ∀ᶠ J in atTop, FT (Ffam J) (xiOf n) = 0 :=
      (FT_Ffam_pp_eventually hn).filter_mono (le_inf le_rfl (le_principal_iff.mpr ?_))
    · have h0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun J hJ => hJ.symm))
      rw [h0, Complex.zero_re]
    · -- `J ∈ 𝒥` for all `J ≥ 1`, by (a)
      exact Filter.mem_of_superset (eventually_ge_atTop 1) fun J hJ => ha J hJ
  · exact (hFpos ξ hξ hpp).le

/-- **Conjecture 6.1 ⇒ (S), (U), v1.1** (the "Implication" paragraph of §6.1): the conjecture with its
non-strict part (c) implies (S) and (U) unconditionally, hence `RH ⇔ (E)`; under either, `κ* = 0` and
`𝒦 = {p_ζ}`.  ((c) gives (Mg), and Remark 4.10(a) applies.) -/
theorem conjFamily0_implies (h : ConjFamily0) :
    CondS ∧ CondU ∧ (RiemannHypothesis ↔ CondE) ∧
      (RiemannHypothesis ∨ CondE → kappaStar = 0 ∧ K = {pZeta}) := by
  obtain ⟨ha, ⟨hpos, a, ha_lt, hbd⟩, pinf, hconv, hFnn⟩ := h
  have hN : HypN := Set.infinite_of_forall_exists_gt fun n => ⟨n + 1, ha (n + 1) (by omega), by omega⟩
  have hP := conjFamily_bound hpos hbd
  have ha0 : 0 ≤ max a 0 := le_max_right a 0
  have ha' : max a 0 < Real.pi / 2 := max_lt ha_lt (by have := Real.pi_pos; positivity)
  have hPOS : HypPOS := ⟨10, 1, max a 0, ha0, ha', fun J _ hJ k hk => hP J hJ k hk⟩
  -- (c) ⇒ (Mg)
  have hMg0 : HypMg0 := by
    intro ξ hξ ε hε
    have hL := hFnn ξ hξ
    set L := (FT (fun z => Xi z ^ 2 * ∑' k, (pinf k : ℂ) * z ^ (2 * k)) ξ).re with hLdef
    have hlim : Tendsto (fun J => (FT (Ffam J) ξ).re) atTop (𝓝 L) :=
      (Complex.continuous_re.tendsto _).comp (FT_Ffam_tendsto ha0 ha' hP hconv ξ)
    have hev : ∀ᶠ J in atTop, -ε ≤ (FT (Ffam J) ξ).re :=
      (hlim.eventually (lt_mem_nhds (by linarith : L - ε < L))).mono fun J hJ => by linarith
    exact hev.filter_mono inf_le_left
  exact remark_4_10a_nonstrict hN hPOS hMg0

end PosRig
