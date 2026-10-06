/-
§4.2, Proposition 4.5, remaining parts: each `F_J = Ξ² P_J(t²)` lies in `𝒯` (indeed `Ξ² P(t²) ∈ 𝒯` for
every polynomial `P` with real coefficients), and `𝒜(F_J) = (1/π) Σ_{n ∈ PP, n > n_J} Λ(n) n^{-1/2} F̂_J(ξ_n)`
for `J ∈ 𝒥`.
-/
import PositivityRigidity.Family
import PositivityRigidity.Criterion

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

/-! ## Zero-killing functions with polynomially bounded cofactor are test functions -/

/-- If `H` is entire, even, real on `ℝ`, and polynomially bounded on the strip `|Im z| ≤ 3/4`, then
`Ξ² H ∈ 𝒯_{1/4}` (the bound (4.1) absorbs the polynomial growth; §4.1). -/
theorem Xi_sq_mul_inTδ {H : ℂ → ℂ} (hd : Differentiable ℂ H) (heven : ∀ z, H (-z) = H z)
    (hreal : ∀ t : ℝ, (H t).im = 0) {A : ℝ} {m : ℕ}
    (hbd : ∀ z : ℂ, |z.im| ≤ 3 / 4 → ‖H z‖ ≤ A * (1 + |z.re|) ^ m) :
    InTδ (1 / 4) (fun z => Xi z ^ 2 * H z) := by
  obtain ⟨C, hC⟩ := xi_decay 1 one_pos le_rfl
  have hc : (0 : ℝ) < Real.pi / 2 := by have := Real.pi_pos; positivity
  obtain ⟨K, hK0, hK⟩ := poly_exp_le_inv_sq hc (m + 8)
  have hA : 0 ≤ A := by
    have h0 := hbd 0 (by norm_num)
    have : 0 ≤ ‖H 0‖ := norm_nonneg _
    simp at h0
    linarith
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro z _
    simp only [Xi_even, heven]
  · intro t
    have hX : Xi t = ((Xi t).re : ℂ) := Complex.ext (by simp) (by simp [Xi_real t])
    have hH : H t = ((H t).re : ℂ) := Complex.ext (by simp) (by simp [hreal t])
    rw [hX, hH]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im]
  · intro z _
    exact ((differentiable_Xi.pow 2).mul hd).analyticAt z
  · refine ⟨4 * C ^ 2 * A * K, fun z hz => ?_⟩
    have hz' : |z.im| ≤ 3 / 4 := by
      have : |z.im| ≤ 1 / 2 + 1 / 4 := hz
      linarith
    set x := z.re with hx
    set X : ℝ := 1 + |x| with hXdef
    have hX1 : 1 ≤ X := by have := abs_nonneg x; linarith
    have hnorm : 1 + ‖z‖ ≤ 2 * X := by
      have := Complex.norm_le_abs_re_add_abs_im z
      rw [hXdef]; linarith
    have hXi : ‖Xi z‖ ≤ C * X ^ 3 * Real.exp (-(Real.pi / 4) * |x|) :=
      hC z (le_trans hz' (by norm_num))
    have hH : ‖H z‖ ≤ A * X ^ m := hbd z hz'
    have hE : Real.exp (-(Real.pi / 4) * |x|) ^ 2 = Real.exp (-(Real.pi / 2) * |x|) := by
      rw [sq, ← Real.exp_add]; ring_nf
    have hKt := hK x
    have hinv : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
    rw [norm_mul, norm_pow]
    calc (1 + ‖z‖) ^ 2 * (‖Xi z‖ ^ 2 * ‖H z‖)
        ≤ (2 * X) ^ 2 * ((C * X ^ 3 * Real.exp (-(Real.pi / 4) * |x|)) ^ 2 * (A * X ^ m)) := by
          gcongr
      _ = 4 * C ^ 2 * A * (X ^ (m + 8) * Real.exp (-(Real.pi / 2) * |x|)) := by
          rw [← hE]; ring
      _ ≤ 4 * C ^ 2 * A * (K * (1 + x ^ 2)⁻¹) := by
          gcongr
      _ ≤ 4 * C ^ 2 * A * K := by
          have : K * (1 + x ^ 2)⁻¹ ≤ K := by
            calc K * (1 + x ^ 2)⁻¹ ≤ K * 1 := by gcongr
              _ = K := mul_one K
          gcongr

theorem Xi_sq_mul_mem_TestClass {H : ℂ → ℂ} (hd : Differentiable ℂ H) (heven : ∀ z, H (-z) = H z)
    (hreal : ∀ t : ℝ, (H t).im = 0) {A : ℝ} {m : ℕ}
    (hbd : ∀ z : ℂ, |z.im| ≤ 3 / 4 → ‖H z‖ ≤ A * (1 + |z.re|) ^ m) :
    (fun z => Xi z ^ 2 * H z) ∈ TestClass :=
  ⟨1 / 4, Xi_sq_mul_inTδ hd heven hreal hbd⟩

/-- `Ξ² P(t²) ∈ 𝒯` for every polynomial `P` with real coefficients (§4.1, after (4.1)). -/
theorem Xi_sq_mul_poly_mem_TestClass (P : Polynomial ℂ) (hPreal : ∀ k, (P.coeff k).im = 0) :
    (fun z => Xi z ^ 2 * P.eval (z ^ 2)) ∈ TestClass := by
  refine Xi_sq_mul_mem_TestClass (A := ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖)
    (m := 2 * P.natDegree) ?_ ?_ ?_ ?_
  · exact (Polynomial.differentiable P).comp (differentiable_id.pow 2)
  · intro z; simp
  · intro t
    rw [Polynomial.eval_eq_sum_range, Complex.im_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hc : P.coeff i = ((P.coeff i).re : ℂ) := Complex.ext (by simp) (by simp [hPreal i])
    rw [hc, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im]
  · intro z hz
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hX1 : 1 ≤ 1 + |z.re| := by have := abs_nonneg z.re; linarith
    have hnz : ‖z‖ ≤ 1 + |z.re| := by
      have := Complex.norm_le_abs_re_add_abs_im z
      linarith
    rw [norm_mul, norm_pow, norm_pow, ← pow_mul]
    gcongr
    calc ‖z‖ ^ (2 * i) ≤ (1 + |z.re|) ^ (2 * i) := pow_le_pow_left₀ (norm_nonneg _) hnz _
      _ ≤ (1 + |z.re|) ^ (2 * P.natDegree) := pow_le_pow_right₀ hX1 (by omega)

/-- **Proposition 4.5.** Each `F_J = Ξ² H_J`, `H_J(t) = P_J(t²)`, lies in `𝒯`. -/
theorem Ffam_mem_TestClass (J : ℕ) : Ffam J ∈ TestClass := by
  refine Xi_sq_mul_mem_TestClass (A := ∑ k ∈ Finset.range (2 * J + 1), |pcoef J k|) (m := 4 * J)
    (differentiable_Hfam J) (Hfam_even J) (Hfam_real J) ?_
  intro z hz
  simp only [Hfam, Pfam]
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hk' : k ≤ 2 * J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hX1 : 1 ≤ 1 + |z.re| := by have := abs_nonneg z.re; linarith
  have hnz : ‖z‖ ≤ 1 + |z.re| := by
    have := Complex.norm_le_abs_re_add_abs_im z
    linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, norm_pow, ← pow_mul]
  gcongr
  calc ‖z‖ ^ (2 * k) ≤ (1 + |z.re|) ^ (2 * k) := pow_le_pow_left₀ (norm_nonneg _) hnz _
    _ ≤ (1 + |z.re|) ^ (4 * J) := pow_le_pow_right₀ hX1 (by omega)

/-! ## The tail formula for `𝒜(F_J)` -/

theorem setOf_isPrimePow_infinite : (Set.ofPred (IsPrimePow : ℕ → Prop)).Infinite :=
  Nat.infinite_setOfPred_prime.mono fun _ hp => Nat.Prime.isPrimePow hp

theorem ppNth_strictMonoOn : StrictMonoOn ppNth {j : ℕ | 1 ≤ j} := by
  intro i hi j hj hij
  simp only [Set.mem_ofPred_eq] at hi hj
  unfold ppNth
  exact Nat.nth_strictMono setOf_isPrimePow_infinite (by omega)

/-- A prime power `n ≤ n_J` (`J ≥ 1`) is one of `n_1, …, n_J`. -/
theorem exists_ppNth_le {J n : ℕ} (hJ : 1 ≤ J) (hn : IsPrimePow n) (hle : n ≤ ppNth J) :
    ∃ j, 1 ≤ j ∧ j ≤ J ∧ ppNth j = n := by
  obtain ⟨j, hj1, hjn⟩ := exists_ppNth hn
  refine ⟨j, hj1, ?_, hjn⟩
  by_contra hjJ
  push Not at hjJ
  have := ppNth_strictMonoOn (show J ∈ {j : ℕ | 1 ≤ j} from hJ) (show j ∈ {j : ℕ | 1 ≤ j} from hj1) hjJ
  omega

/-- **Proposition 4.5, last claim.**  For `J ∈ 𝒥`,
`𝒜(F_J) = (1/π) Σ_{n ∈ PP, n > n_J} Λ(n) n^{-1/2} F̂_J(ξ_n)` (Corollary 4.4 with the interpolation
property: the prime powers `n ≤ n_J` are killed). -/
theorem Arch_Ffam_tail {J : ℕ} (hJ : J ∈ Jset) :
    ((Arch (Ffam J) : ℝ) : ℂ) = (1 / Real.pi : ℂ) * ∑' n : ℕ,
      (if ppNth J < n then
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * FT (Ffam J) (xiOf n)
      else 0) := by
  have h := (zero_killing_EF (H := Hfam J) (Ffam_mem_TestClass J)).2
  have h2 : ((Arch (Ffam J) : ℝ) : ℂ) = (1 / Real.pi : ℂ) *
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * FT (Ffam J) (xiOf n) :=
    h
  rw [h2]
  congr 1
  refine tsum_congr fun n => ?_
  split_ifs with hn
  · rfl
  · push Not at hn
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · simp [hΛ]
    · have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
      obtain ⟨j, hj1, hjJ, hjn⟩ := exists_ppNth_le hJ.1 hpp hn
      rw [← hjn, FT_Ffam_pp hJ hj1 hjJ, mul_zero]

/-! ## The derivative rows: double zeros at the nodes -/

/-- `m_k` is differentiable: `t ↦ t^{2k+1} Ξ(t)²` is integrable, so the transform can be differentiated
under the integral (`Real.hasDerivAt_fourier`). -/
theorem momR_hasDerivAt (k : ℕ) (w : ℝ) : ∃ d : ℝ, HasDerivAt (momR k) d w := by
  have hf : Integrable (onR (fun z => z ^ (2 * k) * Xi z ^ 2)) := integrable_pow_Xi_sq (2 * k)
  have hf' : Integrable (fun x : ℝ => x • onR (fun z => z ^ (2 * k) * Xi z ^ 2) x) := by
    refine (integrable_pow_Xi_sq (2 * k + 1)).congr (Eventually.of_forall fun x => ?_)
    simp only [onR, Complex.real_smul]
    ring
  have h : HasDerivAt (mom k) _ w := Real.hasDerivAt_fourier hf hf' w
  have hc := Complex.reCLM.hasFDerivAt.comp_hasDerivAt w h
  have he : (Complex.reCLM : ℂ → ℝ) ∘ mom k = momR k := by
    funext ξ; simp [momR]
  rw [he] at hc
  exact ⟨_, hc⟩

theorem momR_differentiableAt (k : ℕ) (w : ℝ) : DifferentiableAt ℝ (momR k) w := by
  obtain ⟨d, h⟩ := momR_hasDerivAt k w
  exact h.differentiableAt

/-- `Re F̂_J = Σ_{k ≤ 2J} p_k m_k` (the moments are real). -/
theorem FT_Ffam_re (J : ℕ) :
    (fun ξ => (FT (Ffam J) ξ).re) =
      fun ξ => ∑ k ∈ Finset.range (2 * J + 1), pcoef J k * momR k ξ := by
  funext ξ
  rw [FT_Ffam]
  simp_rw [mom_eq_ofReal]
  have : ∑ k ∈ Finset.range (2 * J + 1), (pcoef J k : ℂ) * (momR k ξ : ℂ) =
      ((∑ k ∈ Finset.range (2 * J + 1), pcoef J k * momR k ξ : ℝ) : ℂ) := by
    push_cast; rfl
  rw [this, Complex.ofReal_re]

/-- The derivative rows of the Hermite system: `F̂_J'` vanishes at the nodes (Proposition 4.5). -/
theorem deriv_FT_Ffam_rowNode {J : ℕ} (hJ : J ∈ Jset) {r : ℕ} (hr : r < 2 * J)
    (hrodd : r % 2 = 1) : deriv (fun ξ => (FT (Ffam J) ξ).re) (rowNode r) = 0 := by
  rw [FT_Ffam_re]
  have hd : deriv (fun ξ => ∑ k ∈ Finset.range (2 * J + 1), pcoef J k * momR k ξ) (rowNode r) =
      ∑ k ∈ Finset.range (2 * J + 1), pcoef J k * deriv (momR k) (rowNode r) := by
    have := HasDerivAt.fun_sum (u := Finset.range (2 * J + 1))
      (A := fun k ξ => pcoef J k * momR k ξ)
      (A' := fun k => pcoef J k * deriv (momR k) (rowNode r))
      (fun k _ => ((momR_differentiableAt k _).hasDerivAt).const_mul (pcoef J k))
    exact this.deriv
  rw [hd, Finset.sum_range_succ']
  have hdet : IsUnit (hermiteM J).det := isUnit_iff_ne_zero.mpr hJ.2
  have hMp : Matrix.mulVec (hermiteM J) (pvec J) = -hermiteB J := by
    unfold pvec
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hrow := congrFun hMp ⟨r, hr⟩
  have hne : ¬ (r % 2 = 0) := by omega
  simp only [Matrix.mulVec, dotProduct, hermiteM, hermiteB, Pi.neg_apply, rowData,
    if_neg hne] at hrow
  have hp0 : pcoef J 0 = 1 := by simp [pcoef]
  rw [hp0, one_mul]
  have : ∑ k ∈ Finset.range (2 * J), pcoef J (k + 1) * deriv (momR (k + 1)) (rowNode r) =
      ∑ c : Fin (2 * J), deriv (momR (c.val + 1)) (rowNode r) * pvec J c := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => pcoef J (k + 1) * deriv (momR (k + 1)) (rowNode r))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm]
    congr 1
    simp [pcoef, c.isLt]
  rw [this, hrow]
  ring

/-- **Proposition 4.5, zeros of order at least two.**  For `J ∈ 𝒥` and `1 ≤ j ≤ J`, both `F̂_J` and its
`ξ`-derivative vanish at `ξ_{n_j}`. -/
theorem deriv_FT_Ffam_pp {J : ℕ} (hJ : J ∈ Jset) {j : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J) :
    FT (Ffam J) (xiOf (ppNth j)) = 0 ∧
      deriv (fun ξ => (FT (Ffam J) ξ).re) (xiOf (ppNth j)) = 0 := by
  refine ⟨FT_Ffam_pp hJ hj1 hjJ, ?_⟩
  have h := deriv_FT_Ffam_rowNode hJ (r := 2 * (j - 1) + 1) (by omega) (by omega)
  have : rowNode (2 * (j - 1) + 1) = xiOf (ppNth j) := by
    unfold rowNode; rw [show (2 * (j - 1) + 1) / 2 + 1 = j by omega]
  rwa [this] at h

end PosRig
