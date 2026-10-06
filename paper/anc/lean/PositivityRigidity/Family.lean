/-
§4: the zero-killing family.  Corollary 4.4 (the explicit formula for zero-killing functions) and the
non-negativity of `𝒜` on zero-killing functions of the cone (end of Lemma 4.7); the interpolation
property of the exact family (Proposition 4.5); Proposition 4.9 (1), (2); the consequences of the
certified finite-`J` instances (Proposition 5.6).
-/
import PositivityRigidity.Duality
import PositivityRigidity.Zeta
import PositivityRigidity.PZeta

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

/-! ## Corollary 4.4 -/

/-- **Corollary 4.4 (the explicit formula for zero-killing functions).**  If `F = Ξ² H ∈ 𝒯`, then
`𝒜(F) = (1/π) Σ_{n} Λ(n) n^{-1/2} F̂(ξ_n)`; no hypothesis on the zeros of `ζ` is used. -/
theorem zero_killing_EF {H : ℂ → ℂ} (hF : (fun z => Xi z ^ 2 * H z) ∈ TestClass) :
    Summable (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      FT (fun z => Xi z ^ 2 * H z) (xiOf n)) ∧
    ((Arch (fun z => Xi z ^ 2 * H z) : ℝ) : ℂ) = (1 / Real.pi : ℂ) *
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        FT (fun z => Xi z ^ 2 * H z) (xiOf n) := by
  obtain ⟨-, hsum, hEF⟩ := explicit_formula _ hF
  refine ⟨hsum, ?_⟩
  rw [hEF]
  have h0 : (∑' ρ : NontrivialZeros, (mult ρ : ℂ) * (Xi (tOf ρ) ^ 2 * H (tOf ρ))) = 0 := by
    have : ∀ ρ : NontrivialZeros, (mult ρ : ℂ) * (Xi (tOf ρ) ^ 2 * H (tOf ρ)) = 0 := by
      intro ρ
      rw [Xi_tOf ρ.2]
      ring
    simp [this]
  rw [h0, zero_add]

/-- **Lemma 4.7, last sentence.**  `𝒜(F) ≥ 0` for every `F ∈ 𝒞` of the form `Ξ² H` (by Corollary 4.4,
since `F̂ ≥ 0` at the prime powers). -/
theorem Arch_nonneg_of_zero_killing {H : ℂ → ℂ} (hF : (fun z => Xi z ^ 2 * H z) ∈ Cone) :
    0 ≤ Arch (fun z => Xi z ^ 2 * H z) := by
  obtain ⟨hsum, hEF⟩ := zero_killing_EF hF.1
  have hre := congrArg Complex.re hEF
  rw [Complex.ofReal_re] at hre
  rw [hre]
  have e : (1 / Real.pi : ℂ) = ((1 / Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul, Complex.re_tsum hsum]
  refine mul_nonneg (by have := Real.pi_pos; positivity) (tsum_nonneg fun n => ?_)
  rw [Complex.re_ofReal_mul]
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp [hΛ]
  · have hn : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
    have hξ : xi2 ≤ xiOf n := xiPP_subset_Ici ⟨n, hn, rfl⟩
    exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (ConeG.FT_re_nonneg hF hξ)

/-! ## Integrability of the moments -/

/-- `(1+|t|)^m e^{−c|t|} ≤ m'! e^c c^{−m'} (1+|t|)^{m−m'}` with `m' = m + 2`, hence a bound by
`K/(1+t²)`. -/
theorem poly_exp_le_inv_sq {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ,
      (1 + |t|) ^ m * Real.exp (-c * |t|) ≤ K * (1 + t ^ 2)⁻¹ := by
  set N := m + 2
  refine ⟨2 * (N.factorial * Real.exp c / c ^ N), by positivity, fun t => ?_⟩
  have h1 : 0 < 1 + |t| := by positivity
  have hexp : (c * (1 + |t|)) ^ N / N.factorial ≤ Real.exp (c * (1 + |t|)) :=
    Real.pow_div_factorial_le_exp _ (by positivity) N
  have hN : (1 + |t|) ^ N * Real.exp (-c * |t|) ≤ N.factorial * Real.exp c / c ^ N := by
    have he : Real.exp (c * (1 + |t|)) = Real.exp c * Real.exp (c * |t|) := by
      rw [← Real.exp_add]; ring_nf
    rw [he, div_le_iff₀ (by positivity : (0 : ℝ) < N.factorial)] at hexp
    rw [mul_pow] at hexp
    have hpos : 0 < Real.exp (c * |t|) := Real.exp_pos _
    have hneg : Real.exp (-c * |t|) = (Real.exp (c * |t|))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [hneg, le_div_iff₀ (by positivity)]
    calc (1 + |t|) ^ N * (Real.exp (c * |t|))⁻¹ * c ^ N
        = c ^ N * (1 + |t|) ^ N / Real.exp (c * |t|) := by field_simp
      _ ≤ Real.exp c * Real.exp (c * |t|) * N.factorial / Real.exp (c * |t|) := by
          gcongr
      _ = N.factorial * Real.exp c := by field_simp
  have hsq : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
    have := abs_nonneg t
    have : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    nlinarith
  have hsplit : (1 + |t|) ^ N = (1 + |t|) ^ m * (1 + |t|) ^ 2 := by rw [← pow_add]
  rw [hsplit] at hN
  have hpos2 : 0 < (1 + |t|) ^ 2 := by positivity
  have hle : (1 + |t|) ^ m * Real.exp (-c * |t|) ≤ (N.factorial * Real.exp c / c ^ N) / (1 + |t|) ^ 2 := by
    rw [le_div_iff₀ hpos2]; nlinarith [Real.exp_pos (-c * |t|)]
  calc (1 + |t|) ^ m * Real.exp (-c * |t|) ≤ (N.factorial * Real.exp c / c ^ N) / (1 + |t|) ^ 2 := hle
    _ ≤ (N.factorial * Real.exp c / c ^ N) / (1 + t ^ 2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
    _ ≤ 2 * (N.factorial * Real.exp c / c ^ N) * (1 + t ^ 2)⁻¹ := by
        rw [div_eq_mul_inv]
        have : 0 ≤ (N.factorial * Real.exp c / c ^ N) * (1 + t ^ 2)⁻¹ := by positivity
        nlinarith

/-- `t ↦ t^{j} Ξ(t)²` is integrable on `ℝ` (from the classical bound (4.1), ledger axiom `xi_decay`). -/
theorem integrable_pow_Xi_sq (j : ℕ) : Integrable (fun t : ℝ => (t : ℂ) ^ j * Xi t ^ 2) := by
  obtain ⟨C, hC⟩ := xi_decay 1 one_pos le_rfl
  have hc : (0 : ℝ) < Real.pi / 2 := by have := Real.pi_pos; positivity
  obtain ⟨K, hK0, hK⟩ := poly_exp_le_inv_sq hc (j + 6)
  have hcont : Continuous (fun t : ℝ => (t : ℂ) ^ j * Xi t ^ 2) :=
    (Complex.continuous_ofReal.pow j).mul
      ((differentiable_Xi.continuous.comp Complex.continuous_ofReal).pow 2)
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (C ^ 2 * K))
    hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have h1 : ‖Xi t‖ ≤ C * (1 + |t|) ^ 3 * Real.exp (-(Real.pi / 4) * |t|) := by
    have := hC (t : ℂ) (by simp)
    simpa using this
  have hXnn : 0 ≤ ‖Xi t‖ := norm_nonneg _
  have hC0 : 0 ≤ C * (1 + |t|) ^ 3 * Real.exp (-(Real.pi / 4) * |t|) := hXnn.trans h1
  have ht : |t| ≤ 1 + |t| := by linarith
  have htj : |t| ^ j ≤ (1 + |t|) ^ j := pow_le_pow_left₀ (abs_nonneg t) ht j
  rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  calc |t| ^ j * ‖Xi t‖ ^ 2
      ≤ (1 + |t|) ^ j * (C * (1 + |t|) ^ 3 * Real.exp (-(Real.pi / 4) * |t|)) ^ 2 := by
        gcongr
    _ = C ^ 2 * ((1 + |t|) ^ (j + 6) * Real.exp (-(Real.pi / 2) * |t|)) := by
        have he : Real.exp (-(Real.pi / 4) * |t|) ^ 2 = Real.exp (-(Real.pi / 2) * |t|) := by
          rw [sq, ← Real.exp_add]; ring_nf
        rw [mul_pow, mul_pow, he, pow_add]; ring
    _ ≤ C ^ 2 * (K * (1 + t ^ 2)⁻¹) := mul_le_mul_of_nonneg_left (hK t) (sq_nonneg C)
    _ = C ^ 2 * K * (1 + t ^ 2)⁻¹ := by ring

/-! ## Proposition 4.5: the exact family interpolates -/

/-- `m_k` is real-valued (transform of the even function `t^{2k} Ξ(t)²`, real on `ℝ`). -/
theorem mom_real (k : ℕ) (ξ : ℝ) : (mom k ξ).im = 0 := by
  unfold mom
  apply FT_real_of_even_real
  · intro t
    rw [Xi_even, show (-(t : ℂ)) ^ (2 * k) = (t : ℂ) ^ (2 * k) by rw [pow_mul, pow_mul, neg_sq]]
  · intro t
    have h1 : ((t : ℂ) ^ (2 * k)).im = 0 := by rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
    have h2 : (Xi t ^ 2).im = 0 := by
      have : Xi t = ((Xi t).re : ℂ) := Complex.ext (by simp) (by simp [Xi_real t])
      rw [this, ← Complex.ofReal_pow]; exact Complex.ofReal_im _
    simp [Complex.mul_im, h1, h2]

theorem mom_eq_ofReal (k : ℕ) (ξ : ℝ) : mom k ξ = (momR k ξ : ℂ) :=
  Complex.ext (by simp [momR]) (by simp [mom_real k ξ])

/-- `F̂_J = Σ_{k ≤ 2J} p_k m_k` (proof of Proposition 4.5). -/
theorem FT_Ffam (J : ℕ) (ξ : ℝ) :
    FT (Ffam J) ξ = ∑ k ∈ Finset.range (2 * J + 1), (pcoef J k : ℂ) * mom k ξ := by
  have hfun : Ffam J = fun z => ∑ k ∈ Finset.range (2 * J + 1),
      (fun k z => (pcoef J k : ℂ) * (z ^ (2 * k) * Xi z ^ 2)) k z := by
    funext z
    simp only [Ffam, Hfam, Pfam, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← pow_mul]; ring
  rw [hfun, FT_finset_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [FT_smul]
    rfl
  · intro k _
    exact (integrable_pow_Xi_sq (2 * k)).const_mul _

/-- The value rows of the Hermite system: `F̂_J` vanishes at the nodes (Proposition 4.5). -/
theorem FT_Ffam_rowNode {J : ℕ} (hJ : J ∈ Jset) {r : ℕ} (hr : r < 2 * J) (hreven : r % 2 = 0) :
    FT (Ffam J) (rowNode r) = 0 := by
  rw [FT_Ffam]
  simp_rw [mom_eq_ofReal]
  have hsum : ∑ k ∈ Finset.range (2 * J + 1), (pcoef J k : ℂ) * (momR k (rowNode r) : ℂ) =
      ((∑ k ∈ Finset.range (2 * J + 1), pcoef J k * momR k (rowNode r) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hsum, Complex.ofReal_eq_zero, Finset.sum_range_succ']
  -- `M_J p = −b_J`
  have hdet : IsUnit (hermiteM J).det := isUnit_iff_ne_zero.mpr hJ.2
  have hMp : Matrix.mulVec (hermiteM J) (pvec J) = -hermiteB J := by
    unfold pvec
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hrow := congrFun hMp ⟨r, hr⟩
  simp only [Matrix.mulVec, dotProduct, hermiteM, hermiteB, Pi.neg_apply, rowData,
    if_pos hreven] at hrow
  have hp0 : pcoef J 0 = 1 := by simp [pcoef]
  rw [hp0, one_mul]
  have : ∑ k ∈ Finset.range (2 * J), pcoef J (k + 1) * momR (k + 1) (rowNode r) =
      ∑ c : Fin (2 * J), momR (c.val + 1) (rowNode r) * pvec J c := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => pcoef J (k + 1) * momR (k + 1) (rowNode r))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm]
    congr 1
    simp [pcoef, c.isLt]
  rw [this, hrow]
  ring

theorem exists_ppNth {n : ℕ} (hn : IsPrimePow n) : ∃ j, 1 ≤ j ∧ ppNth j = n :=
  ⟨Nat.count IsPrimePow n + 1, by omega, by simp [ppNth, Nat.nth_count hn]⟩

/-- **Proposition 4.5.**  For `J ∈ 𝒥`, `F̂_J` vanishes at `ξ_{n_1}, …, ξ_{n_J}`. -/
theorem FT_Ffam_pp {J : ℕ} (hJ : J ∈ Jset) {j : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J) :
    FT (Ffam J) (xiOf (ppNth j)) = 0 := by
  have h := FT_Ffam_rowNode hJ (r := 2 * (j - 1)) (by omega) (by omega)
  have : rowNode (2 * (j - 1)) = xiOf (ppNth j) := by
    unfold rowNode; rw [show 2 * (j - 1) / 2 + 1 = j by omega]
  rwa [this] at h

/-- For every prime power `n`, `F̂_J(ξ_n) = 0` for all large `J ∈ 𝒥`. -/
theorem FT_Ffam_pp_eventually {n : ℕ} (hn : IsPrimePow n) :
    ∀ᶠ J in atTop ⊓ 𝓟 Jset, FT (Ffam J) (xiOf n) = 0 := by
  obtain ⟨j, hj1, hjn⟩ := exists_ppNth hn
  have h1 : ∀ᶠ J in atTop ⊓ 𝓟 Jset, j ≤ J := (eventually_ge_atTop j).filter_mono inf_le_left
  have h2 : ∀ᶠ J in atTop ⊓ 𝓟 Jset, J ∈ Jset :=
    (eventually_principal.mpr fun J hJ => hJ).filter_mono inf_le_right
  filter_upwards [h1, h2] with J hJ hJs
  rw [← hjn]
  exact FT_Ffam_pp hJs hj1 hJ

/-! ## Proposition 4.9 (1), (2) and Proposition 5.6 -/

theorem Hfam_ofReal (J : ℕ) (t : ℝ) :
    Hfam J t = ((∑ k ∈ Finset.range (2 * J + 1), pcoef J k * (t ^ 2) ^ k : ℝ) : ℂ) := by
  simp [Hfam, Pfam]

/-- **Proposition 4.9 (1), (2)** for one `J`: if `0 ≤ p_k ≤ C a^{2k}/(2k)!` for all `k`, then `H_J ≥ 1` on
`ℝ` and `|H_J(t)| ≤ C cosh(a|t|)` on `ℂ`. -/
theorem coeff_bound_consequences {J : ℕ} {C a : ℝ} (hpos : ∀ k ≤ 2 * J, 0 ≤ pcoef J k)
    (hbd : ∀ k ≤ 2 * J, pcoef J k ≤ C * a ^ (2 * k) / ((2 * k).factorial : ℝ)) :
    (∀ t : ℝ, 1 ≤ (Hfam J t).re ∧ (Hfam J t).im = 0) ∧
      ∀ z : ℂ, ‖Hfam J z‖ ≤ C * Real.cosh (a * ‖z‖) := by
  have hpos' : ∀ k ∈ Finset.range (2 * J + 1), 0 ≤ pcoef J k :=
    fun k hk => hpos k (by have := Finset.mem_range.mp hk; omega)
  refine ⟨fun t => ?_, fun z => ?_⟩
  · rw [Hfam_ofReal, Complex.ofReal_re, Complex.ofReal_im]
    refine ⟨?_, rfl⟩
    have h0 : (0 : ℕ) ∈ Finset.range (2 * J + 1) := by simp
    have := Finset.single_le_sum (f := fun k => pcoef J k * (t ^ 2) ^ k)
      (fun k hk => mul_nonneg (hpos' k hk) (by positivity)) h0
    simpa [pcoef] using this
  · have hC : 0 ≤ C := by
      have := hbd 0 (by omega)
      simpa [pcoef] using (zero_le_one.trans this)
    calc ‖Hfam J z‖ ≤ ∑ k ∈ Finset.range (2 * J + 1), ‖(pcoef J k : ℂ) * (z ^ 2) ^ k‖ := by
          simp only [Hfam, Pfam]; exact norm_sum_le _ _
      _ = ∑ k ∈ Finset.range (2 * J + 1), pcoef J k * ‖z‖ ^ (2 * k) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos' k hk), norm_pow,
            norm_pow, ← pow_mul]
      _ ≤ ∑ k ∈ Finset.range (2 * J + 1), C * ((a * ‖z‖) ^ (2 * k) / ((2 * k).factorial : ℝ)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hb := hbd k (by have := Finset.mem_range.mp hk; omega)
          rw [mul_pow, ← mul_div_assoc, mul_div_right_comm, ← mul_assoc]
          have : C * a ^ (2 * k) / ((2 * k).factorial : ℝ) * ‖z‖ ^ (2 * k) =
              C * (a ^ (2 * k) * ‖z‖ ^ (2 * k)) / ((2 * k).factorial : ℝ) := by ring
          calc pcoef J k * ‖z‖ ^ (2 * k) ≤ C * a ^ (2 * k) / ((2 * k).factorial : ℝ) * ‖z‖ ^ (2 * k) :=
                mul_le_mul_of_nonneg_right hb (by positivity)
            _ = C * a ^ (2 * k) / ((2 * k).factorial : ℝ) * ‖z‖ ^ (2 * k) := rfl
            _ = _ := by ring
      _ = C * ∑ k ∈ Finset.range (2 * J + 1), (a * ‖z‖) ^ (2 * k) / ((2 * k).factorial : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ C * Real.cosh (a * ‖z‖) := by
          gcongr
          exact sum_le_hasSum _ (fun k _ => div_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)
            (by positivity)) (Real.hasSum_cosh _)

/-- **Proposition 5.6, consequences.**  For `J ∈ {10, 60, 61, 110, 111}`: `M_J` is non-singular,
`H_J ≥ 1` on `ℝ`, and `|H_J(t)| ≤ cosh(0.71636 |t|)` on `ℂ` (from the certificate `cert_finiteJ` and
Proposition 4.9 with `C = 1`). -/
theorem prop_5_5 {J : ℕ} (hJ : J ∈ ({10, 60, 61, 110, 111} : Finset ℕ)) :
    J ∈ Jset ∧ (∀ t : ℝ, 1 ≤ (Hfam J t).re ∧ (Hfam J t).im = 0) ∧
      ∀ z : ℂ, ‖Hfam J z‖ ≤ Real.cosh ((71636 / 100000 : ℝ) * ‖z‖) := by
  obtain ⟨hJs, hk⟩ := cert_finiteJ J hJ
  have h := coeff_bound_consequences (J := J) (C := 1) (a := 71636 / 100000)
    (fun k hk' => (hk k hk').1.le) (fun k hk' => by rw [one_mul]; exact (hk k hk').2)
  refine ⟨hJs, h.1, fun z => ?_⟩
  simpa using h.2 z

end PosRig
