/-
The pair `p_ζ = (μ_ζ, ν_ζ)` (§2.1): support, atoms, evenness, and Theorem 2.9(a): under RH,
`p_ζ` is admissible (from the explicit formula, Lemma 2.3).
-/
import PositivityRigidity.Zeta
import PositivityRigidity.Sanity

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

private theorem Zzeta_measurableSet : MeasurableSet Zzeta := Zzeta_countable.measurableSet

theorem muZeta_carriedBy : CarriedBy muZeta Zzeta := by
  unfold CarriedBy muZeta
  rw [Measure.sum_apply _ Zzeta_measurableSet.compl]
  simp only [Measure.smul_apply, smul_eq_mul]
  refine ENNReal.tsum_eq_zero.mpr fun γ => ?_
  rw [Measure.dirac_apply' _ Zzeta_measurableSet.compl]
  simp

theorem muZeta_singleton {γ : ℝ} (hγ : γ ∈ Zzeta) :
    muZeta {γ} = ((mult (1 / 2 + I * (γ : ℂ)) : ℕ) : ℝ≥0∞) := by
  unfold muZeta
  rw [Measure.sum_apply _ (measurableSet_singleton γ)]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [tsum_eq_single ⟨γ, hγ⟩]
  · simp
  · intro γ' hne
    have hne' : (γ' : ℝ) ≠ γ := fun h => hne (Subtype.ext h)
    rw [Measure.dirac_apply' _ (measurableSet_singleton γ)]
    have : (γ' : ℝ) ∉ ({γ} : Set ℝ) := by simpa using hne'
    simp [Set.indicator_of_notMem this]

theorem muZeta_even : EvenMeasure muZeta := by
  unfold EvenMeasure
  ext A hA
  rw [Measure.map_apply measurable_neg hA]
  have hA' : MeasurableSet ((fun t : ℝ => -t) ⁻¹' A) := measurable_neg hA
  unfold muZeta
  rw [Measure.sum_apply _ hA', Measure.sum_apply _ hA]
  simp only [Measure.smul_apply, smul_eq_mul]
  -- reindex by the involution `γ ↦ −γ` of `Z_ζ`
  let e : Zzeta ≃ Zzeta :=
    { toFun := fun γ => ⟨-(γ : ℝ), neg_mem_Zzeta.mpr γ.2⟩
      invFun := fun γ => ⟨-(γ : ℝ), neg_mem_Zzeta.mpr γ.2⟩
      left_inv := fun γ => Subtype.ext (neg_neg _)
      right_inv := fun γ => Subtype.ext (neg_neg _) }
  set f : Zzeta → ℝ≥0∞ := fun γ =>
    ((mult (1 / 2 + I * ((γ : ℝ) : ℂ)) : ℕ) : ℝ≥0∞) * Measure.dirac (γ : ℝ) A with hf
  rw [← e.tsum_eq f]
  refine tsum_congr fun γ => ?_
  simp only [hf, e, Equiv.coe_fn_mk]
  rw [Measure.dirac_apply' _ hA', Measure.dirac_apply' _ hA]
  have hm := mult_neg (γ : ℝ)
  push_cast at hm ⊢
  rw [hm]
  -- `(neg ⁻¹' A).indicator 1 γ = A.indicator 1 (−γ)` holds by definition
  rfl

theorem xiPP_subset_Ici : xiPP ⊆ Set.Ici xi2 := by
  rintro x ⟨n, hn, rfl⟩
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
  simp only [Set.mem_Ici, xi2, xiOf]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Real.log_le_log (by norm_num) h2

theorem xiPP_subset_BRSNodes : xiPP ⊆ BRSNodes := by
  rintro x ⟨n, hn, rfl⟩
  refine ⟨n ^ 2, ?_, ?_⟩
  · have := hn.two_le
    nlinarith
  · simp only [xiOf, brsNode]
    push_cast
    rw [Real.log_pow]
    field_simp
    ring

private theorem xiPP_countable : xiPP.Countable := by
  apply (Set.countable_range (fun n : ℕ => xiOf n)).mono
  rintro x ⟨n, -, rfl⟩
  exact ⟨n, rfl⟩

theorem nuZeta_carriedBy_xiPP : CarriedBy nuZeta xiPP := by
  unfold CarriedBy nuZeta
  rw [Measure.sum_apply _ xiPP_countable.measurableSet.compl]
  simp only [Measure.smul_apply, smul_eq_mul]
  refine ENNReal.tsum_eq_zero.mpr fun n => ?_
  by_cases hn : IsPrimePow n
  · rw [Measure.dirac_apply' _ xiPP_countable.measurableSet.compl]
    have : xiOf n ∉ xiPPᶜ := fun h => h ⟨n, hn, rfl⟩
    simp [Set.indicator_of_notMem this]
  · have hΛ : ArithmeticFunction.vonMangoldt n = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
    simp [hΛ]

theorem nuZeta_carriedBy_Ici : CarriedBy nuZeta (Set.Ici xi2) :=
  measure_mono_null (Set.compl_subset_compl.mpr xiPP_subset_Ici) nuZeta_carriedBy_xiPP

theorem nuZeta_carriedBy_BRSNodes : CarriedBy nuZeta BRSNodes :=
  measure_mono_null (Set.compl_subset_compl.mpr xiPP_subset_BRSNodes) nuZeta_carriedBy_xiPP

/-- For `n, m ≥ 1`: `ξ_n = log m/(4π)` iff `m = n²`. -/
private theorem xiOf_eq_brsNode_iff {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    xiOf n = brsNode m ↔ n ^ 2 = m := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold xiOf brsNode
  constructor
  · intro h
    have h2 : Real.log ((n : ℝ) ^ 2) = Real.log m := by
      rw [Real.log_pow]
      field_simp at h
      push_cast
      linarith
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr hm0) h2
    exact_mod_cast this
  · intro h
    rw [← h]
    push_cast
    rw [Real.log_pow]
    field_simp
    ring

/-- `ν_ζ({log m/(4π)}) = Λ(√m) m^{-1/4}` (zero if `m` is not a square). -/
theorem nuZeta_singleton_brsNode {m : ℕ} (hm : 1 ≤ m) :
    nuZeta {brsNode m} = ENNReal.ofReal (nuZetaAtom m) := by
  unfold nuZeta
  rw [Measure.sum_apply _ (measurableSet_singleton _)]
  simp only [Measure.smul_apply, smul_eq_mul]
  -- the only possible contribution is `n = √m`
  have hterm : ∀ n : ℕ, (n ^ 2 ≠ m) →
      ENNReal.ofReal (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        Measure.dirac (xiOf n) {brsNode m} = 0 := by
    intro n hn
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · simp [hΛ]
    · have hn1 : 1 ≤ n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp at hΛ
        · exact h
      rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
      have : xiOf n ∉ ({brsNode m} : Set ℝ) := by
        simp only [Set.mem_singleton_iff]
        exact fun h => hn ((xiOf_eq_brsNode_iff hn1 hm).mp h)
      simp [Set.indicator_of_notMem this]
  unfold nuZetaAtom
  by_cases hsq : IsSquare m
  · obtain ⟨r, hr⟩ := hsq
    have hr2 : r ^ 2 = m := by rw [hr]; ring
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h; simp at hr; omega
      · exact h
    rw [tsum_eq_single r (fun n hn => hterm n (fun h => hn (by
        have : n ^ 2 = r ^ 2 := by rw [h, hr2]
        exact Nat.pow_left_injective (by norm_num) this)))]
    rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
    have hmem : xiOf r ∈ ({brsNode m} : Set ℝ) :=
      Set.mem_singleton_iff.mpr ((xiOf_eq_brsNode_iff hr1 hm).mpr hr2)
    rw [Set.indicator_of_mem hmem]
    have hsq' : IsSquare m := ⟨r, hr⟩
    rw [if_pos hsq']
    have hsqrt : Nat.sqrt m = r := by rw [hr]; exact Nat.sqrt_eq r
    rw [hsqrt]
    simp only [Pi.one_apply, mul_one]
    congr 1
    -- `Λ(r)/√r = Λ(r) · (r²)^{-1/4}`
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
    have hm' : (m : ℝ) = (r : ℝ) ^ 2 := by rw [← hr2]; push_cast; ring
    rw [hm', div_eq_mul_inv]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le, ← Real.rpow_neg hr0.le]
    norm_num
  · rw [if_neg hsq, ENNReal.ofReal_zero]
    refine ENNReal.tsum_eq_zero.mpr fun n => hterm n (fun h => hsq ⟨n, by rw [← h]; ring⟩)

/-- `μ_ζ` is purely atomic on the countable set `Z_ζ`, so it dominates no `λ dt` with `λ > 0`
(used in Theorem 2.9(d)). -/
theorem not_dominatesLeb_muZeta {lam : ℝ} (h : 0 < lam) : ¬ DominatesLeb muZeta lam := by
  intro hd
  have h1 := (Measure.le_iff'.mp hd) Zzetaᶜ
  have h0 : muZeta Zzetaᶜ = 0 := muZeta_carriedBy
  rw [h0] at h1
  simp only [Measure.smul_apply, smul_eq_mul] at h1
  have hvol0 : (volume : Measure ℝ) Zzeta = 0 := Zzeta_countable.measure_zero volume
  have hvol : (volume : Measure ℝ) Zzetaᶜ = ⊤ := by
    rw [measure_compl Zzeta_measurableSet (by rw [hvol0]; exact ENNReal.zero_ne_top), hvol0,
      Real.volume_univ]
    simp
  rw [hvol] at h1
  have hne : ENNReal.ofReal lam ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact h
  rw [ENNReal.mul_top hne] at h1
  exact absurd h1 (by simp)

/-- **Theorem 2.9(a).** RH implies `p_ζ ∈ 𝒦`. -/
theorem pZeta_mem_K_of_RH (hRH : RiemannHypothesis) : pZeta ∈ K := by
  -- under RH, `ρ = 1/2 + i Im ρ` for every non-trivial zero
  have hre : ∀ ρ : NontrivialZeros, (ρ : ℂ) = 1 / 2 + I * (((ρ : ℂ).im : ℝ) : ℂ) := by
    intro ρ
    have h := re_eq_half_of_RH hRH ρ.2
    apply Complex.ext <;> simp [h]
  have hmemZ : ∀ ρ : NontrivialZeros, ((ρ : ℂ).im : ℝ) ∈ Zzeta := by
    intro ρ
    show riemannZeta (1 / 2 + I * (((ρ : ℂ).im : ℝ) : ℂ)) = 0
    rw [← hre ρ]
    exact ρ.2.1
  -- the bijection `NontrivialZeros ≃ Z_ζ`, `ρ ↦ Im ρ`
  let e : NontrivialZeros ≃ Zzeta :=
    { toFun := fun ρ => ⟨(ρ : ℂ).im, hmemZ ρ⟩
      invFun := fun γ => ⟨1 / 2 + I * ((γ : ℝ) : ℂ), half_add_mem_NontrivialZeros γ.2⟩
      left_inv := fun ρ => Subtype.ext (hre ρ).symm
      right_inv := fun γ => Subtype.ext (by simp) }
  have : Countable Zzeta := Zzeta_countable.to_subtype
  refine ⟨muZeta_even, nuZeta_carriedBy_Ici, ?_⟩
  intro F hF
  obtain ⟨hsZ, hsP, hEF⟩ := explicit_formula F hF
  -- the zero side as a sum over `Z_ζ`
  set g : Zzeta → ℂ := fun γ => (mult (1 / 2 + I * ((γ : ℝ) : ℂ)) : ℂ) * F ((γ : ℝ) : ℂ) with hg
  have hcomp : (fun ρ : NontrivialZeros => (mult ρ : ℂ) * F (tOf ρ)) = g ∘ e := by
    funext ρ
    simp only [Function.comp_apply, hg, e, Equiv.coe_fn_mk]
    have h1 : tOf (ρ : ℂ) = (((ρ : ℂ).im : ℝ) : ℂ) := by
      conv_lhs => rw [hre ρ]
      exact tOf_half_add _
    rw [h1, ← hre ρ]
  have hgsum : Summable g := by
    rw [← e.summable_iff, ← hcomp]
    exact hsZ
  have hZtsum : ∑' ρ : NontrivialZeros, (mult ρ : ℂ) * F (tOf ρ) = ∑' γ : Zzeta, g γ := by
    rw [hcomp]
    exact e.tsum_eq g
  -- integrals against `μ_ζ`
  have hcμ : ∀ γ : Zzeta, ((mult (1 / 2 + I * ((γ : ℝ) : ℂ)) : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    fun γ => ENNReal.natCast_ne_top _
  have hsumμ : Summable fun γ : Zzeta =>
      (((mult (1 / 2 + I * ((γ : ℝ) : ℂ)) : ℕ) : ℝ≥0∞)).toReal * ‖onR F (γ : ℝ)‖ := by
    have := summable_norm_iff.mpr hgsum
    refine this.congr fun γ => ?_
    simp only [hg, onR, norm_mul, Complex.norm_natCast, ENNReal.toReal_natCast]
  have hintμ : Integrable (onR F) muZeta := by
    unfold muZeta
    exact (integrable_sum_dirac_iff hcμ).mpr hsumμ
  have hIμ : ∫ t, F t ∂muZeta = ∑' γ : Zzeta, g γ := by
    have := integral_sum_dirac_eq_tsum (f := onR F) hcμ hsumμ
    unfold muZeta
    refine this.trans (tsum_congr fun γ => ?_)
    simp only [hg, onR, ENNReal.toReal_natCast, Complex.real_smul]
    push_cast
    ring
  -- integrals against `ν_ζ`
  have hcν : ∀ n : ℕ, ENNReal.ofReal (ArithmeticFunction.vonMangoldt n / Real.sqrt n) ≠ ⊤ :=
    fun n => ENNReal.ofReal_ne_top
  have hnn : ∀ n : ℕ, 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
    fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hsumν : Summable fun n : ℕ =>
      (ENNReal.ofReal (ArithmeticFunction.vonMangoldt n / Real.sqrt n)).toReal *
        ‖FT F (xiOf n)‖ := by
    have := summable_norm_iff.mpr hsP
    refine this.congr fun n => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnn n),
      ENNReal.toReal_ofReal (hnn n)]
  have hintν : Integrable (FT F) nuZeta := by
    unfold nuZeta
    exact (integrable_sum_dirac_iff hcν).mpr hsumν
  have hIν : ∫ ξ, FT F ξ ∂nuZeta =
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * FT F (xiOf n) := by
    have := integral_sum_dirac_eq_tsum (f := FT F) hcν hsumν
    unfold nuZeta
    refine this.trans (tsum_congr fun n => ?_)
    rw [ENNReal.toReal_ofReal (hnn n), Complex.real_smul]
  refine ⟨hintμ, hintν, ?_⟩
  show ((Arch F : ℝ) : ℂ) = (∫ t, F t ∂muZeta) + (1 / Real.pi : ℂ) * ∫ ξ, FT F ξ ∂nuZeta
  rw [hIμ, hIν, ← hZtsum]
  exact hEF

end PosRig
